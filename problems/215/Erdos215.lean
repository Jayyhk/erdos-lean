import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos215

/-
# Problem Description

Erdős Problem 215, an old question of Steinhaus. Does there exist `S ⊆ ℝ²` such that every
set congruent to `S` — that is, `S` after some translation and rotation — contains exactly
one point of `ℤ²`? `erdos_215` proves that such a set exists.

Erdős was "almost certain that such a set does not exist". It does: this is a theorem of
Jackson and Mauldin, whose construction depends on choice. Accordingly `Classical.choice`
appears among the dependencies listed at the end of this file, and that is intrinsic to the
result rather than an artefact of the formalization.

`Point` is `EuclideanSpace ℝ (Fin 2)`, and `IsSteinhaus S` is
`∀ (t : Point) (c s : ℝ), c ^ 2 + s ^ 2 = 1 → ∃! z : Point, z ∈ integerLattice ∧ z ∈ movedSet S t c s`
— the translation is `t`, the rotation is the unit vector `(c, s)`, and `∃!` is the
"exactly one point" of the question.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/Geometry.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-!
# The geometric interface for Erdős Problem 215

Exact coordinate translations and rotations, the embedded integer lattice, and elementary
equivalences turning the original congruent-copy statement into a transversal statement.
-/

open Set
open scoped BigOperators

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The Euclidean plane in standard orthonormal coordinates. -/
abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

/-- Integer coordinate pairs. -/
abbrev IntPoint : Type := Fin 2 → ℤ

/-- The standard coordinate embedding of `ℤ²` in the Euclidean plane. -/
def intPoint (z : IntPoint) : Point :=
  WithLp.toLp 2 (fun i ↦ (z i : ℝ))

@[simp]
lemma intPoint_apply (z : IntPoint) (i : Fin 2) : intPoint z i = (z i : ℝ) := rfl

lemma intPoint_injective : Function.Injective intPoint := by
  intro z w h
  funext i
  have hi := congrArg (fun p : Point ↦ p i) h
  change (z i : ℝ) = (w i : ℝ) at hi
  exact Int.cast_injective hi

/-- The standard integer lattice `ℤ² ⊆ ℝ²`. -/
def integerLattice : Set Point := Set.range intPoint

@[simp]
lemma intPoint_mem_integerLattice (z : IntPoint) : intPoint z ∈ integerLattice :=
  ⟨z, rfl⟩

/-- Rotation with cosine `c` and sine `s`. It is an isometry when `c² + s² = 1`. -/
def rotate (c s : ℝ) (p : Point) : Point :=
  WithLp.toLp 2 fun i : Fin 2 ↦
    if i = 0 then c * p 0 - s * p 1 else s * p 0 + c * p 1

@[simp]
lemma rotate_apply_zero (c s : ℝ) (p : Point) :
    rotate c s p 0 = c * p 0 - s * p 1 := by
  simp [rotate]

@[simp]
lemma rotate_apply_one (c s : ℝ) (p : Point) :
    rotate c s p 1 = s * p 0 + c * p 1 := by
  simp [rotate]

@[simp]
lemma rotate_zero (c s : ℝ) : rotate c s 0 = 0 := by
  ext i
  fin_cases i <;> simp [rotate]

lemma rotate_add (c s : ℝ) (p q : Point) :
    rotate c s (p + q) = rotate c s p + rotate c s q := by
  ext i
  fin_cases i <;> simp [rotate] <;> ring

lemma rotate_sub (c s : ℝ) (p q : Point) :
    rotate c s (p - q) = rotate c s p - rotate c s q := by
  ext i
  fin_cases i <;> simp [rotate] <;> ring

lemma rotate_neg (c s : ℝ) (p : Point) :
    rotate c s (-p) = -rotate c s p := by
  ext i
  fin_cases i <;> simp [rotate] <;> ring

lemma rotate_inverse_left (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (p : Point) :
    rotate c (-s) (rotate c s p) = p := by
  have hmul (x : ℝ) : (c ^ 2 + s ^ 2) * x = x := by rw [hcs, one_mul]
  ext i
  fin_cases i
  · simp [rotate]
    calc
      c * (c * p 0 - s * p 1) + s * (s * p 0 + c * p 1) =
          (c ^ 2 + s ^ 2) * p 0 := by ring
      _ = p 0 := hmul (p 0)
  · simp [rotate]
    calc
      -(s * (c * p 0 - s * p 1)) + c * (s * p 0 + c * p 1) =
          (c ^ 2 + s ^ 2) * p 1 := by ring
      _ = p 1 := hmul (p 1)

lemma rotate_inverse_right (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (p : Point) :
    rotate c s (rotate c (-s) p) = p := by
  have hmul (x : ℝ) : (c ^ 2 + s ^ 2) * x = x := by rw [hcs, one_mul]
  ext i
  fin_cases i
  · simp [rotate]
    calc
      c * (c * p 0 + s * p 1) - s * (-(s * p 0) + c * p 1) =
          (c ^ 2 + s ^ 2) * p 0 := by ring
      _ = p 0 := hmul (p 0)
  · simp [rotate]
    calc
      s * (c * p 0 + s * p 1) + c * (-(s * p 0) + c * p 1) =
          (c ^ 2 + s ^ 2) * p 1 := by ring
      _ = p 1 := hmul (p 1)

/-- The rigid motion which first rotates and then translates. -/
def motion (t : Point) (c s : ℝ) (p : Point) : Point :=
  t + rotate c s p

/-- The inverse formula for `motion t c s`, valid when `c² + s² = 1`. -/
def inverseMotion (t : Point) (c s : ℝ) (p : Point) : Point :=
  rotate c (-s) (p - t)

lemma inverseMotion_motion (t : Point) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (p : Point) : inverseMotion t c s (motion t c s p) = p := by
  simpa [inverseMotion, motion] using rotate_inverse_left c s hcs p

lemma motion_inverseMotion (t : Point) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (p : Point) : motion t c s (inverseMotion t c s p) = p := by
  simp [inverseMotion, motion, rotate_inverse_right c s hcs]

/-- A translate of a rotation of `S`. -/
def movedSet (S : Set Point) (t : Point) (c s : ℝ) : Set Point :=
  motion t c s '' S

lemma mem_movedSet_iff (S : Set Point) (t : Point) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) (p : Point) :
    p ∈ movedSet S t c s ↔ inverseMotion t c s p ∈ S := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [inverseMotion_motion t c s hcs q] using hq
  · intro hp
    refine ⟨inverseMotion t c s p, hp, ?_⟩
    exact motion_inverseMotion t c s hcs p

/-- Squared Euclidean distance in standard coordinates. -/
def distSq (p q : Point) : ℝ :=
  ∑ i : Fin 2, (p i - q i) ^ 2

@[simp]
lemma distSq_self (p : Point) : distSq p p = 0 := by
  simp [distSq]

lemma distSq_comm (p q : Point) : distSq p q = distSq q p := by
  simp only [distSq, Fin.sum_univ_two]
  ring

lemma distSq_eq_dist_sq (p q : Point) : distSq p q = dist p q ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp [distSq, Fin.sum_univ_two]
  rw [Real.sq_sqrt]
  positivity

lemma distSq_rotate (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (p q : Point) :
    distSq (rotate c s p) (rotate c s q) = distSq p q := by
  simp [distSq, Fin.sum_univ_two, rotate]
  nlinarith

lemma distSq_motion (t : Point) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (p q : Point) : distSq (motion t c s p) (motion t c s q) = distSq p q := by
  calc
    distSq (motion t c s p) (motion t c s q) =
        distSq (rotate c s p) (rotate c s q) := by
      simp [motion, distSq, Fin.sum_univ_two]
    _ = distSq p q := distSq_rotate c s hcs p q

lemma distSq_inverseMotion (t : Point) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (p q : Point) :
    distSq (inverseMotion t c s p) (inverseMotion t c s q) = distSq p q := by
  have hcs' : c ^ 2 + (-s) ^ 2 = 1 := by nlinarith
  calc
    distSq (inverseMotion t c s p) (inverseMotion t c s q) =
        distSq (p - t) (q - t) := by
      exact distSq_rotate c (-s) hcs' (p - t) (q - t)
    _ = distSq p q := by simp [distSq, Fin.sum_univ_two]

/-- Squared distance between two integer coordinate pairs, as an integer. -/
def intDistSq (z w : IntPoint) : ℤ :=
  ∑ i : Fin 2, (z i - w i) ^ 2

@[simp]
lemma distSq_intPoint (z w : IntPoint) :
    distSq (intPoint z) (intPoint w) = (intDistSq z w : ℝ) := by
  simp [distSq, intDistSq, Fin.sum_univ_two]

/-- No two distinct selected points have integral squared distance. -/
def IsPartialSteinhaus (S : Set Point) : Prop :=
  ∀ ⦃p : Point⦄, p ∈ S → ∀ ⦃q : Point⦄, q ∈ S → p ≠ q →
    ∀ n : ℤ, distSq p q ≠ (n : ℝ)

/-- Every inverse image of the integer lattice under a direct rigid motion is hit. -/
def HitsEveryLattice (S : Set Point) : Prop :=
  ∀ (t : Point) (c s : ℝ), c ^ 2 + s ^ 2 = 1 →
    ∃ z : IntPoint, inverseMotion t c s (intPoint z) ∈ S

/-- The literal statement of Erdős Problem 215. -/
def IsSteinhaus (S : Set Point) : Prop :=
  ∀ (t : Point) (c s : ℝ), c ^ 2 + s ^ 2 = 1 →
    ∃! z : Point, z ∈ integerLattice ∧ z ∈ movedSet S t c s

lemma integer_points_equal_of_partial
    {S : Set Point} (hS : IsPartialSteinhaus S)
    (t : Point) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (z w : IntPoint)
    (hz : inverseMotion t c s (intPoint z) ∈ S)
    (hw : inverseMotion t c s (intPoint w) ∈ S) : z = w := by
  by_contra hzw
  have hpq : inverseMotion t c s (intPoint z) ≠ inverseMotion t c s (intPoint w) := by
    intro h
    apply hzw
    apply intPoint_injective
    have := congrArg (motion t c s) h
    simpa only [motion_inverseMotion t c s hcs] using this
  have hnot := hS hz hw hpq (intDistSq z w)
  apply hnot
  rw [distSq_inverseMotion t c s hcs, distSq_intPoint]

/-- The partial-distance condition supplies uniqueness, so hitting every lattice is enough. -/
theorem isSteinhaus_of_partial_of_hits {S : Set Point}
    (hpartial : IsPartialSteinhaus S) (hhits : HitsEveryLattice S) : IsSteinhaus S := by
  intro t c s hcs
  obtain ⟨z, hz⟩ := hhits t c s hcs
  refine ⟨intPoint z, ⟨intPoint_mem_integerLattice z,
    (mem_movedSet_iff S t c s hcs (intPoint z)).2 hz⟩, ?_⟩
  intro p hp
  rcases hp.1 with ⟨w, rfl⟩
  have hw : inverseMotion t c s (intPoint w) ∈ S :=
    (mem_movedSet_iff S t c s hcs (intPoint w)).1 hp.2
  exact congrArg intPoint (integer_points_equal_of_partial hpartial t c s hcs w z hw hz)

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/RationalLattice.lean` -/

section
/-!
# Rational coordinates and rational rotations for Erdős Problem 215

This file isolates the elementary affine and finite-counting facts used in
the Jackson--Mauldin construction.  An `OrientedFrame` is an origin together
with a direct orthonormal frame, encoded by its cosine and sine.  Its rational
plane is the image of `ℚ²`; its integer lattice is the image of `ℤ²`.
-/

open Set
open scoped BigOperators

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Rational coordinate pairs. -/
abbrev RatPoint : Type := Fin 2 → ℚ

/-- The standard embedding of `ℚ²` in the real Euclidean plane. -/
def ratPoint (q : RatPoint) : Point :=
  WithLp.toLp 2 fun i ↦ (q i : ℝ)

@[simp]
lemma ratPoint_apply (q : RatPoint) (i : Fin 2) : ratPoint q i = (q i : ℝ) := rfl

/-- An oriented orthonormal affine frame, represented by an origin and the
cosine and sine of its direction angle. -/
structure OrientedFrame where
  origin : Point
  c : ℝ
  s : ℝ
  unit : c ^ 2 + s ^ 2 = 1

namespace OrientedFrame

/-- Convert frame coordinates to ambient coordinates. -/
def fromCoords (L : OrientedFrame) (p : Point) : Point :=
  L.origin + rotate L.c L.s p

/-- Convert ambient coordinates to frame coordinates. -/
def toCoords (L : OrientedFrame) (p : Point) : Point :=
  rotate L.c (-L.s) (p - L.origin)

lemma fromCoords_toCoords (L : OrientedFrame) (p : Point) :
    L.fromCoords (L.toCoords p) = p := by
  simp [fromCoords, toCoords, rotate_inverse_right L.c L.s L.unit]

lemma toCoords_fromCoords (L : OrientedFrame) (p : Point) :
    L.toCoords (L.fromCoords p) = p := by
  simp [fromCoords, toCoords, rotate_inverse_left L.c L.s L.unit]

lemma fromCoords_injective (L : OrientedFrame) : Function.Injective L.fromCoords := by
  intro p q h
  simpa only [L.toCoords_fromCoords] using congrArg L.toCoords h

lemma toCoords_injective (L : OrientedFrame) : Function.Injective L.toCoords := by
  intro p q h
  simpa only [L.fromCoords_toCoords] using congrArg L.fromCoords h

lemma distSq_fromCoords (L : OrientedFrame) (p q : Point) :
    distSq (L.fromCoords p) (L.fromCoords q) = distSq p q := by
  simpa [fromCoords, motion] using distSq_motion L.origin L.c L.s L.unit p q

/-- The rational-coordinate plane of a frame. -/
def IsRational (L : OrientedFrame) (p : Point) : Prop :=
  ∃ q : RatPoint, p = L.fromCoords (ratPoint q)

/-- The integer lattice of a frame. -/
def IsLatticePoint (L : OrientedFrame) (p : Point) : Prop :=
  ∃ z : IntPoint, p = L.fromCoords (intPoint z)

/-- A rational translate of the integer lattice belonging to `L`. -/
def rationalTranslate (L : OrientedFrame) (q : RatPoint) : Set Point :=
  {p | ∃ z : IntPoint, p = L.fromCoords (ratPoint q + intPoint z)}

lemma isRational_iff_toCoords (L : OrientedFrame) (p : Point) :
    L.IsRational p ↔ ∃ q : RatPoint, L.toCoords p = ratPoint q := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, L.toCoords_fromCoords _⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, (L.fromCoords_toCoords p).symm.trans (congrArg L.fromCoords hq)⟩

lemma origin_isRational (L : OrientedFrame) : L.IsRational L.origin := by
  refine ⟨0, ?_⟩
  have hzero : ratPoint (0 : RatPoint) = 0 := by
    ext i
    simp [ratPoint]
  simp [fromCoords, hzero]

/-- Rational equivalence, in its coordinate-plane form.  For orthonormal
frames this is equivalent to a finite chain of rational translations and
rational rotations. -/
def RationallyEquivalent (L K : OrientedFrame) : Prop :=
  ∀ p : Point, L.IsRational p ↔ K.IsRational p

@[refl]
lemma rationallyEquivalent_refl (L : OrientedFrame) : L.RationallyEquivalent L := by
  intro p
  rfl

@[symm]
lemma rationallyEquivalent_symm {L K : OrientedFrame}
    (h : L.RationallyEquivalent K) : K.RationallyEquivalent L := by
  intro p
  exact (h p).symm

@[trans]
lemma rationallyEquivalent_trans {L K M : OrientedFrame}
    (hLK : L.RationallyEquivalent K) (hKM : K.RationallyEquivalent M) :
    L.RationallyEquivalent M := by
  intro p
  exact (hLK p).trans (hKM p)

/-- Cosine of the rotation taking `K`-coordinates to `L`-coordinates. -/
def relativeC (L K : OrientedFrame) : ℝ := L.c * K.c + L.s * K.s

/-- Sine of the rotation taking `K`-coordinates to `L`-coordinates. -/
def relativeS (L K : OrientedFrame) : ℝ := L.c * K.s - L.s * K.c

lemma relative_unit (L K : OrientedFrame) :
    (L.relativeC K) ^ 2 + (L.relativeS K) ^ 2 = 1 := by
  dsimp [relativeC, relativeS]
  nlinarith [L.unit, K.unit]

lemma toCoords_fromCoords_other (L K : OrientedFrame) (p : Point) :
    L.toCoords (K.fromCoords p) =
      L.toCoords K.origin + rotate (L.relativeC K) (L.relativeS K) p := by
  ext i
  fin_cases i <;>
    simp [toCoords, fromCoords, rotate, relativeC, relativeS] <;> ring

/-- A rational relative rotation is one whose relative cosine and sine are
rational numbers. -/
def IsRationalRotation (L K : OrientedFrame) : Prop :=
  ∃ a b : ℚ, L.relativeC K = (a : ℝ) ∧ L.relativeS K = (b : ℝ)

lemma rational_image_of_relative
    {L K : OrientedFrame} (ho : L.IsRational K.origin)
    (hr : L.IsRationalRotation K) {p : Point} (hp : K.IsRational p) :
    L.IsRational p := by
  obtain ⟨o, ho⟩ := (L.isRational_iff_toCoords K.origin).mp ho
  obtain ⟨a, b, ha, hb⟩ := hr
  obtain ⟨q, rfl⟩ := hp
  apply (L.isRational_iff_toCoords _).mpr
  let v : RatPoint := fun i ↦ if i = 0 then o 0 + a * q 0 - b * q 1
    else o 1 + b * q 0 + a * q 1
  refine ⟨v, ?_⟩
  rw [L.toCoords_fromCoords_other K, ho, ha, hb]
  ext i
  fin_cases i <;> simp [v, rotate, ratPoint] <;> ring

lemma rationallyEquivalent_of_relative
    {L K : OrientedFrame} (ho : L.IsRational K.origin)
    (hr : L.IsRationalRotation K) : L.RationallyEquivalent K := by
  intro p
  constructor
  · intro hp
    have hKLr : K.IsRationalRotation L := by
      obtain ⟨a, b, ha, hb⟩ := hr
      refine ⟨a, -b, ?_, ?_⟩
      · dsimp [relativeC, relativeS] at ha hb ⊢
        nlinarith
      · dsimp [relativeC, relativeS] at ha hb ⊢
        push_cast
        nlinarith
    have hKLo : K.IsRational L.origin := by
      obtain ⟨q, hq⟩ := ho
      apply (K.isRational_iff_toCoords _).mpr
      obtain ⟨a, b, ha, hb⟩ := hKLr
      let v : RatPoint := fun i ↦ if i = 0 then -(a * q 0 - b * q 1)
        else -(b * q 0 + a * q 1)
      refine ⟨v, ?_⟩
      simp only [toCoords]
      rw [hq]
      ext i
      fin_cases i <;>
        simp [v, fromCoords, rotate, relativeC, relativeS] at ha hb ⊢ <;>
        rw [← ha, ← hb] <;> ring
    exact rational_image_of_relative hKLo hKLr hp
  · exact rational_image_of_relative ho hr

/-- Two distinct points which are rational in both frames force the relative
rotation to have rational cosine and sine. -/
lemma rationalRotation_of_two_common
    {L K : OrientedFrame} {x y : Point} (hxy : x ≠ y)
    (hxL : L.IsRational x) (hxK : K.IsRational x)
    (hyL : L.IsRational y) (hyK : K.IsRational y) :
    L.IsRationalRotation K := by
  obtain ⟨qx, hqx⟩ := hxL
  obtain ⟨rx, hrx⟩ := hxK
  obtain ⟨qy, hqy⟩ := hyL
  obtain ⟨ry, hry⟩ := hyK
  have hxcoord : ratPoint qx =
      L.toCoords K.origin + rotate (L.relativeC K) (L.relativeS K) (ratPoint rx) := by
    calc
      ratPoint qx = L.toCoords x := by rw [hqx, L.toCoords_fromCoords]
      _ = L.toCoords (K.fromCoords (ratPoint rx)) := by rw [← hrx]
      _ = _ := L.toCoords_fromCoords_other K _
  have hycoord : ratPoint qy =
      L.toCoords K.origin + rotate (L.relativeC K) (L.relativeS K) (ratPoint ry) := by
    calc
      ratPoint qy = L.toCoords y := by rw [hqy, L.toCoords_fromCoords]
      _ = L.toCoords (K.fromCoords (ratPoint ry)) := by rw [← hry]
      _ = _ := L.toCoords_fromCoords_other K _
  let u : ℚ := rx 0 - ry 0
  let v : ℚ := rx 1 - ry 1
  let m : ℚ := qx 0 - qy 0
  let n : ℚ := qx 1 - qy 1
  have huv : u ≠ 0 ∨ v ≠ 0 := by
    by_contra h
    push_neg at h
    have hr : rx = ry := by
      funext i
      fin_cases i
      · dsimp [u] at h
        exact sub_eq_zero.mp h.1
      · dsimp [v] at h
        exact sub_eq_zero.mp h.2
    apply hxy
    rw [hrx, hry, hr]
  have hD : u ^ 2 + v ^ 2 ≠ 0 := by
    rcases huv with hu | hv
    · positivity
    · positivity
  have h0 : (m : ℝ) = L.relativeC K * (u : ℝ) - L.relativeS K * (v : ℝ) := by
    have hx0 := congrArg (fun z : Point ↦ z 0) hxcoord
    have hy0 := congrArg (fun z : Point ↦ z 0) hycoord
    simp [ratPoint, rotate] at hx0 hy0
    dsimp [m, u, v]
    push_cast
    linarith
  have h1 : (n : ℝ) = L.relativeS K * (u : ℝ) + L.relativeC K * (v : ℝ) := by
    have hx1 := congrArg (fun z : Point ↦ z 1) hxcoord
    have hy1 := congrArg (fun z : Point ↦ z 1) hycoord
    simp [ratPoint, rotate] at hx1 hy1
    dsimp [n, u, v]
    push_cast
    linarith
  let a : ℚ := (m * u + n * v) / (u ^ 2 + v ^ 2)
  let b : ℚ := (-m * v + n * u) / (u ^ 2 + v ^ 2)
  refine ⟨a, b, ?_, ?_⟩
  · dsimp [a]
    rw [Rat.cast_div]
    apply (eq_div_iff (by exact_mod_cast hD)).2
    push_cast
    calc
      L.relativeC K * ((u : ℝ) ^ 2 + (v : ℝ) ^ 2) =
          (L.relativeC K * (u : ℝ) - L.relativeS K * (v : ℝ)) * (u : ℝ) +
            (L.relativeS K * (u : ℝ) + L.relativeC K * (v : ℝ)) * (v : ℝ) := by ring
      _ = (m : ℝ) * (u : ℝ) + (n : ℝ) * (v : ℝ) := by rw [← h0, ← h1]
  · dsimp [b]
    rw [Rat.cast_div]
    apply (eq_div_iff (by exact_mod_cast hD)).2
    push_cast
    calc
      L.relativeS K * ((u : ℝ) ^ 2 + (v : ℝ) ^ 2) =
          -(L.relativeC K * (u : ℝ) - L.relativeS K * (v : ℝ)) * (v : ℝ) +
            (L.relativeS K * (u : ℝ) + L.relativeC K * (v : ℝ)) * (u : ℝ) := by ring
      _ = -(m : ℝ) * (v : ℝ) + (n : ℝ) * (u : ℝ) := by rw [← h0, ← h1]

/-- Two distinct common rational points determine the rational-equivalence
class of an oriented lattice. -/
theorem rationallyEquivalent_of_two_common
    {L K : OrientedFrame} {x y : Point} (hxy : x ≠ y)
    (hxL : L.IsRational x) (hxK : K.IsRational x)
    (hyL : L.IsRational y) (hyK : K.IsRational y) :
    L.RationallyEquivalent K := by
  have hr := rationalRotation_of_two_common hxy hxL hxK hyL hyK
  have ho : L.IsRational K.origin := by
    obtain ⟨q, hq⟩ := hxL
    obtain ⟨r, hrx⟩ := hxK
    obtain ⟨a, b, ha, hb⟩ := hr
    apply (L.isRational_iff_toCoords _).mpr
    let o : RatPoint := fun i ↦ if i = 0 then q 0 - (a * r 0 - b * r 1)
      else q 1 - (b * r 0 + a * r 1)
    refine ⟨o, ?_⟩
    have hcoord : ratPoint q = L.toCoords K.origin +
        rotate (L.relativeC K) (L.relativeS K) (ratPoint r) := by
      calc
        ratPoint q = L.toCoords x := by rw [hq, L.toCoords_fromCoords]
        _ = L.toCoords (K.fromCoords (ratPoint r)) := by rw [← hrx]
        _ = _ := L.toCoords_fromCoords_other K _
    rw [ha, hb] at hcoord
    ext i
    fin_cases i
    · have h := congrArg (fun z : Point ↦ z 0) hcoord
      simp [o, ratPoint, rotate] at h ⊢
      linarith
    · have h := congrArg (fun z : Point ↦ z 1) hcoord
      simp [o, ratPoint, rotate] at h ⊢
      linarith
  exact rationallyEquivalent_of_relative ho hr

end OrientedFrame

/-- Standard rational points, used to state the affine-line lemma in
coordinates.  The framed version follows by applying `toCoords`. -/
def IsStandardRational (p : Point) : Prop := ∃ q : RatPoint, p = ratPoint q

/-- The determinant of two plane vectors. -/
def det₂ (u v : Point) : ℝ := u 0 * v 1 - u 1 * v 0

/-- An affine line through `p` with direction `v`. -/
def affineLine (p v : Point) : Set Point := {x | ∃ t : ℝ, x = p + t • v}

/-- The rational points at rational squared distance from `z`. -/
def rationalDistanceSet (z : Point) : Set Point :=
  {w | IsStandardRational w ∧ ∃ r : ℚ, distSq w z = (r : ℝ)}

lemma rational_sqDist_triple_collinear {z w₁ w₂ w₃ : Point}
    (hz : ¬IsStandardRational z)
    (hw₁ : w₁ ∈ rationalDistanceSet z)
    (hw₂ : w₂ ∈ rationalDistanceSet z)
    (hw₃ : w₃ ∈ rationalDistanceSet z) :
    det₂ (w₂ - w₁) (w₃ - w₁) = 0 := by
  obtain ⟨q₁, rfl⟩ := hw₁.1
  obtain ⟨q₂, rfl⟩ := hw₂.1
  obtain ⟨q₃, rfl⟩ := hw₃.1
  obtain ⟨r₁, hr₁⟩ := hw₁.2
  obtain ⟨r₂, hr₂⟩ := hw₂.2
  obtain ⟨r₃, hr₃⟩ := hw₃.2
  let A : ℚ := q₂ 0 - q₁ 0
  let B : ℚ := q₂ 1 - q₁ 1
  let C : ℚ := ((q₂ 0) ^ 2 + (q₂ 1) ^ 2 - r₂ -
    ((q₁ 0) ^ 2 + (q₁ 1) ^ 2 - r₁)) / 2
  let D : ℚ := q₃ 0 - q₁ 0
  let E : ℚ := q₃ 1 - q₁ 1
  let F : ℚ := ((q₃ 0) ^ 2 + (q₃ 1) ^ 2 - r₃ -
    ((q₁ 0) ^ 2 + (q₁ 1) ^ 2 - r₁)) / 2
  have hAC : (A : ℝ) * z 0 + (B : ℝ) * z 1 = (C : ℝ) := by
    simp [distSq, Fin.sum_univ_two, ratPoint] at hr₁ hr₂
    dsimp [A, B, C]
    push_cast
    nlinarith
  have hDF : (D : ℝ) * z 0 + (E : ℝ) * z 1 = (F : ℝ) := by
    simp [distSq, Fin.sum_univ_two, ratPoint] at hr₁ hr₃
    dsimp [D, E, F]
    push_cast
    nlinarith
  by_contra hdet
  have hden : A * E - B * D ≠ 0 := by
    intro h
    apply hdet
    simp [det₂, A, B, D, E, ratPoint]
    exact_mod_cast h
  let x : ℚ := (C * E - B * F) / (A * E - B * D)
  let y : ℚ := (A * F - C * D) / (A * E - B * D)
  have hx : z 0 = (x : ℝ) := by
    dsimp [x]
    rw [Rat.cast_div]
    apply (eq_div_iff (by exact_mod_cast hden)).2
    push_cast
    calc
      z 0 * ((A : ℝ) * (E : ℝ) - (B : ℝ) * (D : ℝ)) =
          ((A : ℝ) * z 0 + (B : ℝ) * z 1) * (E : ℝ) -
            (B : ℝ) * ((D : ℝ) * z 0 + (E : ℝ) * z 1) := by ring
      _ = (C : ℝ) * (E : ℝ) - (B : ℝ) * (F : ℝ) := by rw [hAC, hDF]
  have hy : z 1 = (y : ℝ) := by
    dsimp [y]
    rw [Rat.cast_div]
    apply (eq_div_iff (by exact_mod_cast hden)).2
    push_cast
    calc
      z 1 * ((A : ℝ) * (E : ℝ) - (B : ℝ) * (D : ℝ)) =
          (A : ℝ) * ((D : ℝ) * z 0 + (E : ℝ) * z 1) -
            ((A : ℝ) * z 0 + (B : ℝ) * z 1) * (D : ℝ) := by ring
      _ = (A : ℝ) * (F : ℝ) - (C : ℝ) * (D : ℝ) := by rw [hAC, hDF]
  apply hz
  let q : RatPoint := fun i ↦ if i = 0 then x else y
  refine ⟨q, ?_⟩
  ext i
  fin_cases i
  · simpa [q, ratPoint] using hx
  · simpa [q, ratPoint] using hy

/-- Rational points at rational squared distance from a fixed irrational
point lie on an affine line. -/
theorem rational_sqDist_subset_line {z : Point} (hz : ¬IsStandardRational z) :
    ∃ p v : Point, v ≠ 0 ∧ rationalDistanceSet z ⊆ affineLine p v := by
  let e₀ : Point := WithLp.toLp 2 fun i : Fin 2 ↦ if i = 0 then 1 else 0
  have he₀ : e₀ ≠ 0 := by
    intro h
    have h0 := congrArg (fun x : Point ↦ x 0) h
    simp [e₀] at h0
  by_cases hp : ∃ p, p ∈ rationalDistanceSet z
  · obtain ⟨p, hp⟩ := hp
    by_cases hq : ∃ q, q ∈ rationalDistanceSet z ∧ q ≠ p
    · obtain ⟨q, hq, hqp⟩ := hq
      refine ⟨p, q - p, sub_ne_zero.mpr hqp, ?_⟩
      intro w hw
      have hcol := rational_sqDist_triple_collinear hz hp hq hw
      by_cases h0 : (q - p) 0 = 0
      · have h1 : (q - p) 1 ≠ 0 := by
          intro hz1
          apply sub_ne_zero.mpr hqp
          ext i
          fin_cases i
          · simpa using h0
          · simpa using hz1
        refine ⟨(w 1 - p 1) / (q - p) 1, ?_⟩
        ext i
        fin_cases i
        · have hw0 : w 0 = p 0 := by
            simp [det₂, h0] at hcol
            rcases hcol with hbad | hgood
            · exact False.elim (h1 (by simpa using hbad))
            · exact sub_eq_zero.mp hgood
          simp [hw0, h0]
        · have h1' : q 1 - p 1 ≠ 0 := by simpa using h1
          simp
          field_simp [h1']
          <;> ring
      · refine ⟨(w 0 - p 0) / (q - p) 0, ?_⟩
        ext i
        fin_cases i
        · have h0' : q 0 - p 0 ≠ 0 := by simpa using h0
          simp
          field_simp [h0']
          <;> ring
        · simp [det₂] at hcol ⊢
          have h0' : q 0 - p 0 ≠ 0 := by simpa using h0
          field_simp [h0']
          nlinarith [hcol]
    · refine ⟨p, e₀, he₀, ?_⟩
      intro w hw
      have hwp : w = p := by
        by_contra hne
        exact hq ⟨w, hw, hne⟩
      exact ⟨0, by simp [hwp]⟩
  · refine ⟨0, e₀, he₀, ?_⟩
    intro w hw
    exact False.elim (hp ⟨w, hw⟩)

/-! ## The finite fundamental-domain count -/

/-- Integer coordinate pairs, written separately here to emphasize that the
following calculation takes place in the scaled integer plane. -/
abbrev ZPair : Type := Fin 2 → ℤ

/-- The integral matrix with columns `(a,b)` and `(-b,a)`. -/
def rotIntLinear (a b : ℤ) : ZPair →ₗ[ℤ] ZPair where
  toFun z := fun i ↦ if i = 0 then a * z 0 - b * z 1 else b * z 0 + a * z 1
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' n x := by
    funext i
    fin_cases i <;> simp <;> ring

@[simp]
lemma rotIntLinear_apply_zero (a b : ℤ) (z : ZPair) :
    rotIntLinear a b z 0 = a * z 0 - b * z 1 := by simp [rotIntLinear]

@[simp]
lemma rotIntLinear_apply_one (a b : ℤ) (z : ZPair) :
    rotIntLinear a b z 1 = b * z 0 + a * z 1 := by simp [rotIntLinear]

lemma rotIntLinear_injective {a b d : ℤ} (hd : d ≠ 0)
    (hab : a ^ 2 + b ^ 2 = d ^ 2) : Function.Injective (rotIntLinear a b) := by
  rw [← LinearMap.ker_eq_bot]
  ext z
  constructor
  · intro hz
    have h0 : a * z 0 - b * z 1 = 0 := by
      simpa using congrArg (fun x : ZPair ↦ x 0) hz
    have h1 : b * z 0 + a * z 1 = 0 := by
      simpa using congrArg (fun x : ZPair ↦ x 1) hz
    have hx : (a ^ 2 + b ^ 2) * z 0 = 0 := by
      linear_combination a * h0 + b * h1
    have hy : (a ^ 2 + b ^ 2) * z 1 = 0 := by
      linear_combination -(b * h0) + a * h1
    have hab0 : a ^ 2 + b ^ 2 ≠ 0 := by
      rw [hab]
      exact pow_ne_zero 2 hd
    have hz0 : z 0 = 0 := (mul_eq_zero.mp hx).resolve_left hab0
    have hz1 : z 1 = 0 := (mul_eq_zero.mp hy).resolve_left hab0
    ext i
    fin_cases i <;> simp [hz0, hz1]
  · rintro rfl
    simp [rotIntLinear]

/-- The full-rank sublattice generated by `(a,b)` and `(-b,a)`. -/
def rotatedIntLattice (a b : ℤ) : AddSubgroup ZPair :=
  (LinearMap.range (rotIntLinear a b)).toAddSubgroup

/-- The scalar sublattice `n ℤ²`. -/
def scalarIntLattice (n : ℤ) : AddSubgroup ZPair :=
  rotatedIntLattice n 0

lemma rotIntLinear_det (a b : ℤ) : LinearMap.det (rotIntLinear a b) = a ^ 2 + b ^ 2 := by
  let M : Matrix (Fin 2) (Fin 2) ℤ := fun i j ↦
    if i = 0 then (if j = 0 then a else -b) else (if j = 0 then b else a)
  have hmap : rotIntLinear a b = Matrix.toLin' M := by
    apply LinearMap.ext
    intro z
    funext i
    fin_cases i <;>
      rw [Matrix.toLin'_apply] <;>
      simp [rotIntLinear, M, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  rw [hmap, LinearMap.det_toLin']
  rw [Matrix.det_fin_two]
  simp [M]
  ring

/-- The determinant-index computation for the rotated integral lattice. -/
lemma rotatedIntLattice_index {a b d : ℤ} (hd : d ≠ 0)
    (hab : a ^ 2 + b ^ 2 = d ^ 2) :
    (rotatedIntLattice a b).index = d.natAbs ^ 2 := by
  let N : Submodule ℤ ZPair := LinearMap.range (rotIntLinear a b)
  let e : ZPair ≃ₗ[ℤ] N :=
    LinearEquiv.ofInjective (rotIntLinear a b) (rotIntLinear_injective hd hab)
  have hcard := Submodule.natAbs_det_equiv N e
  change Nat.card (ZPair ⧸ N) = _
  rw [← hcard]
  change (LinearMap.det (rotIntLinear a b)).natAbs = _
  rw [rotIntLinear_det, hab, Int.natAbs_pow]

/-- If `d ∣ e`, then `(de)ℤ²` lies in the lattice generated by the rational
rotation numerator vectors. -/
lemma scalarIntLattice_le_rotated {a b d e : ℤ} (hde : d ∣ e)
    (hab : a ^ 2 + b ^ 2 = d ^ 2) :
    scalarIntLattice (d * e) ≤ rotatedIntLattice a b := by
  obtain ⟨k, rfl⟩ := hde
  rintro _ ⟨z, rfl⟩
  let w : ZPair := fun i ↦ if i = 0 then a * k * z 0 + b * k * z 1
    else -(b * k) * z 0 + a * k * z 1
  refine ⟨w, ?_⟩
  ext i
  fin_cases i
  · simp [scalarIntLattice, rotatedIntLattice, w, rotIntLinear]
    linear_combination k * z 0 * hab
  · simp [scalarIntLattice, rotatedIntLattice, w, rotIntLinear]
    linear_combination k * z 1 * hab

/-- Exact finite fundamental-domain count.  The relative index is the number
of classes of the numerator lattice modulo `(de)ℤ²`, equivalently the number
of points of `e⁻¹R(ℤ²)` in a half-open unit square. -/
theorem scaled_rot_card_fundamental {a b d e : ℤ} (hd : 0 < d) (he : 0 < e)
    (hde : d ∣ e) (hab : a ^ 2 + b ^ 2 = d ^ 2) :
    (scalarIntLattice (d * e)).relIndex (rotatedIntLattice a b) = e.natAbs ^ 2 := by
  have hle := scalarIntLattice_le_rotated hde hab
  have hrot := rotatedIntLattice_index (ne_of_gt hd) hab
  have hscalar : (scalarIntLattice (d * e)).index = (d * e).natAbs ^ 2 := by
    apply rotatedIntLattice_index (mul_ne_zero (ne_of_gt hd) (ne_of_gt he))
    ring
  have hmul := AddSubgroup.relIndex_mul_index hle
  rw [hrot, hscalar, Int.natAbs_mul] at hmul
  have hdabs : 0 < d.natAbs ^ 2 := by positivity
  nlinarith

lemma rotatedIntLattice_multiple_le (a b d : ℤ) :
    rotatedIntLattice (d * a) (d * b) ≤ rotatedIntLattice a b := by
  rintro _ ⟨z, rfl⟩
  let w : ZPair := fun i ↦ d * z i
  refine ⟨w, ?_⟩
  ext i
  fin_cases i <;> simp [w, rotIntLinear] <;> ring

lemma rotatedIntLattice_multiple_relIndex {a b d : ℤ} (hd : 0 < d)
    (hab : a ^ 2 + b ^ 2 = d ^ 2) :
    (rotatedIntLattice (d * a) (d * b)).relIndex (rotatedIntLattice a b) =
      d.natAbs ^ 2 := by
  have hle := rotatedIntLattice_multiple_le a b d
  have hsmall : (rotatedIntLattice (d * a) (d * b)).index =
      (d * d).natAbs ^ 2 := by
    apply rotatedIntLattice_index (mul_ne_zero (ne_of_gt hd) (ne_of_gt hd))
    nlinarith
  have hlarge := rotatedIntLattice_index (ne_of_gt hd) hab
  have hmul := AddSubgroup.relIndex_mul_index hle
  rw [hsmall, hlarge, Int.natAbs_mul] at hmul
  have hpos : 0 < d.natAbs ^ 2 := by positivity
  nlinarith

/-! ## Finite transfer between commensurable lattices -/

/-- `A` meets every additive coset of `H`. -/
def HitsCosets {G : Type*} [AddCommGroup G] (A : Set G) (H : AddSubgroup G) : Prop :=
  ∀ x : G, ∃ a ∈ A, a - x ∈ H

/-- No two distinct points of `A` lie in the same coset of `H`. -/
def SeparatedMod {G : Type*} [AddCommGroup G] (A : Set G) (H : AddSubgroup G) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → a - b ∈ H → a = b

/-- The finite pigeonhole argument underlying rational-rotation transfer.
If two sublattices have the same finite index in a common superlattice, a
transversal for the first which is separated modulo the second is also a
transversal for the second. -/
theorem hitsCosets_of_equal_relIndex
    {G : Type*} [AddCommGroup G] (A : Set G) (H K M : AddSubgroup G)
    (hH : H ≤ M) (hK : K ≤ M)
    [Fintype (M ⧸ H.comap M.subtype)] [Fintype (M ⧸ K.comap M.subtype)]
    (hcard : Fintype.card (M ⧸ H.comap M.subtype) =
      Fintype.card (M ⧸ K.comap M.subtype))
    (hhit : HitsCosets A H) (hsep : SeparatedMod A K) : HitsCosets A K := by
  intro x
  let QH := M ⧸ H.comap M.subtype
  let QK := M ⧸ K.comap M.subtype
  let center (q : QH) : G := x + (Quotient.out q : M)
  let pick (q : QH) : G := Classical.choose (hhit (center q))
  have pick_mem (q : QH) : pick q ∈ A := (Classical.choose_spec (hhit (center q))).1
  have pick_res (q : QH) : pick q - center q ∈ H :=
    (Classical.choose_spec (hhit (center q))).2
  have pick_delta_mem (q : QH) : pick q - x ∈ M := by
    have hr : ((Quotient.out q : M) : G) ∈ M := (Quotient.out q : M).property
    have hs : pick q - center q ∈ M := hH (pick_res q)
    convert M.add_mem hs hr using 1 <;> simp [center] <;> abel
  let delta (q : QH) : M := ⟨pick q - x, pick_delta_mem q⟩
  let f (q : QH) : QK := QuotientAddGroup.mk (delta q)
  have hf_inj : Function.Injective f := by
    intro q r hqr
    have hkr : pick r - pick q ∈ K := by
      have hk0 : -delta q + delta r ∈ K.comap M.subtype :=
        QuotientAddGroup.eq.mp hqr
      change -(pick q - x) + (pick r - x) ∈ K at hk0
      convert hk0 using 1 <;> abel
    have hpick : pick q = pick r :=
      (hsep (pick_mem r) (pick_mem q) hkr).symm
    rw [← Quotient.out_eq' q, ← Quotient.out_eq' r]
    apply QuotientAddGroup.eq.mpr
    change -((Quotient.out q : M) : G) + ((Quotient.out r : M) : G) ∈ H
    have hs := H.sub_mem (pick_res q) (pick_res r)
    rw [hpick] at hs
    convert hs using 1 <;> simp [center] <;> abel
  have hf_surj : Function.Surjective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, hcard⟩ |>.2
  obtain ⟨q, hq⟩ := hf_surj (0 : QK)
  refine ⟨pick q, pick_mem q, ?_⟩
  have hk0 : -delta q + 0 ∈ K.comap M.subtype := QuotientAddGroup.eq.mp hq
  have hkneg' : (-delta q : M) ∈ K.comap M.subtype := by simpa using hk0
  have hkneg : -(pick q - x) ∈ K := hkneg'
  simpa using K.neg_mem hkneg

/-- The special case of `hitsCosets_of_equal_relIndex` in which the common
supergroup is the whole ambient group. -/
theorem hitsCosets_of_equal_index
    {G : Type*} [AddCommGroup G] (A : Set G) (H K : AddSubgroup G)
    [Fintype (G ⧸ H)] [Fintype (G ⧸ K)]
    (hcard : Fintype.card (G ⧸ H) = Fintype.card (G ⧸ K))
    (hhit : HitsCosets A H) (hsep : SeparatedMod A K) : HitsCosets A K := by
  intro x
  let pick (q : G ⧸ H) : G := Classical.choose (hhit (x + Quotient.out q))
  have pick_mem (q : G ⧸ H) : pick q ∈ A :=
    (Classical.choose_spec (hhit (x + Quotient.out q))).1
  have pick_res (q : G ⧸ H) : pick q - (x + Quotient.out q) ∈ H :=
    (Classical.choose_spec (hhit (x + Quotient.out q))).2
  let f (q : G ⧸ H) : G ⧸ K := QuotientAddGroup.mk (pick q - x)
  have hf_inj : Function.Injective f := by
    intro q r hqr
    have hkr : pick r - pick q ∈ K := by
      have hk0 : -(pick q - x) + (pick r - x) ∈ K := QuotientAddGroup.eq.mp hqr
      convert hk0 using 1 <;> abel
    have hpick : pick q = pick r :=
      (hsep (pick_mem r) (pick_mem q) hkr).symm
    rw [← Quotient.out_eq' q, ← Quotient.out_eq' r]
    apply QuotientAddGroup.eq.mpr
    have hs := H.sub_mem (pick_res q) (pick_res r)
    rw [hpick] at hs
    convert hs using 1 <;> abel
  have hf_surj : Function.Surjective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, hcard⟩ |>.2
  obtain ⟨q, hq⟩ := hf_surj (0 : G ⧸ K)
  refine ⟨pick q, pick_mem q, ?_⟩
  have hk0 : -(pick q - x) ∈ K := by simpa using QuotientAddGroup.eq.mp hq
  simpa using K.neg_mem hk0

/-! ## Rational-equivalence classes -/

namespace OrientedFrame

/-- The setoid of oriented frames having the same rational-coordinate plane. -/
def rationalSetoid : Setoid OrientedFrame where
  r := RationallyEquivalent
  iseqv := ⟨rationallyEquivalent_refl, rationallyEquivalent_symm,
    rationallyEquivalent_trans⟩

/-- A rational-equivalence class of oriented lattices. -/
abbrev RationalClass : Type := Quotient rationalSetoid

/-- The class of a concrete oriented frame. -/
def classOf (L : OrientedFrame) : RationalClass := Quotient.mk rationalSetoid L

/-- A classical representative of a rational-equivalence class. -/
noncomputable def representative (C : RationalClass) : OrientedFrame := Quotient.out C

@[simp]
lemma classOf_representative (C : RationalClass) : classOf (representative C) = C :=
  Quotient.out_eq C

lemma classOf_eq_iff (L K : OrientedFrame) :
    classOf L = classOf K ↔ L.RationallyEquivalent K :=
  Quotient.eq

/-- Two distinct common rational points recover equality of the quotient
classes, the interface used by the global Davies recursion. -/
theorem class_eq_of_two_common {L K : OrientedFrame} {x y : Point} (hxy : x ≠ y)
    (hxL : L.IsRational x) (hxK : K.IsRational x)
    (hyL : L.IsRational y) (hyK : K.IsRational y) : classOf L = classOf K :=
  (classOf_eq_iff L K).2
    (rationallyEquivalent_of_two_common hxy hxL hxK hyL hyK)

lemma rationalRotation_of_equivalent {L K : OrientedFrame}
    (hKL : K.RationallyEquivalent L) : L.IsRationalRotation K := by
  let e₀ : RatPoint := fun i ↦ if i = 0 then 1 else 0
  have he₀ : ratPoint e₀ ≠ 0 := by
    intro h
    have h0 := congrArg (fun p : Point ↦ p 0) h
    simp [e₀, ratPoint] at h0
  have hxy : K.origin ≠ K.fromCoords (ratPoint e₀) := by
    intro h
    apply he₀
    apply K.fromCoords_injective
    calc
      K.fromCoords (ratPoint e₀) = K.origin := h.symm
      _ = K.fromCoords 0 := by simp [fromCoords]
  have hxK : K.IsRational K.origin := K.origin_isRational
  have hyK : K.IsRational (K.fromCoords (ratPoint e₀)) := ⟨e₀, rfl⟩
  have hxL : L.IsRational K.origin := (hKL K.origin).mp hxK
  have hyL : L.IsRational (K.fromCoords (ratPoint e₀)) :=
    (hKL (K.fromCoords (ratPoint e₀))).mp hyK
  exact rationalRotation_of_two_common hxy hxL hxK hyL hyK

end OrientedFrame

/-- Clear the two rational denominators of a rational point on the unit
circle.  This supplies the integral Pythagorean triple used by the finite
fundamental-domain calculation. -/
lemma clear_rational_unit_denominators {A B : ℝ} {α β : ℚ}
    (hA : A = (α : ℝ)) (hB : B = (β : ℝ)) (hunit : A ^ 2 + B ^ 2 = 1) :
    ∃ a b d : ℤ, 0 < d ∧ A = (a : ℝ) / d ∧ B = (b : ℝ) / d ∧
      a ^ 2 + b ^ 2 = d ^ 2 := by
  let d : ℤ := (α.den * β.den : ℕ)
  let a : ℤ := α.num * β.den
  let b : ℤ := β.num * α.den
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Nat.mul_pos α.pos β.pos
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have ha : A = (a : ℝ) / d := by
    rw [hA]
    dsimp [a, d]
    push_cast
    rw [show (α : ℝ) = (α.num : ℝ) / α.den by exact_mod_cast α.num_div_den.symm]
    field_simp
  have hb : B = (b : ℝ) / d := by
    rw [hB]
    dsimp [b, d]
    push_cast
    rw [show (β : ℝ) = (β.num : ℝ) / β.den by exact_mod_cast β.num_div_den.symm]
    field_simp
  refine ⟨a, b, d, hd, ha, hb, ?_⟩
  have hint : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 = (d : ℝ) ^ 2 := by
    rw [ha, hb] at hunit
    field_simp [hd0] at hunit
    nlinarith
  exact_mod_cast hint

/-- An integer vector divided by a nonzero integer, regarded as a rational
coordinate vector. -/
def scaledRatPoint (n : ℤ) (z : ZPair) : RatPoint := fun i ↦ (z i : ℚ) / n

/-- Concrete rational-translate hitting predicate, kept in this foundational
module so the transfer theorem does not depend on the global recursion file. -/
def HitsFrameRationalTranslates (S : Set Point) (L : OrientedFrame) : Prop :=
  ∀ q : RatPoint, (S ∩ L.rationalTranslate q).Nonempty

/-- Concrete rational-class hitting predicate. -/
def HitsFrameRationalClass (S : Set Point) (L : OrientedFrame) : Prop :=
  ∀ K : OrientedFrame, K.RationallyEquivalent L →
    ∃ p : Point, p ∈ S ∧ K.IsLatticePoint p

/-- Rational-rotation transfer for actual oriented frames. -/
theorem RationalRotationTransferTheorem
    (S : Set Point) (L : OrientedFrame) (hpartial : IsPartialSteinhaus S)
    (hhit : HitsFrameRationalTranslates S L) : HitsFrameRationalClass S L := by
  intro K hKL
  have hrot := OrientedFrame.rationalRotation_of_equivalent hKL
  obtain ⟨α, β, hα, hβ⟩ := hrot
  obtain ⟨a, b, d, hd, hA, hB, hab⟩ :=
    clear_rational_unit_denominators hα hβ (L.relative_unit K)
  have hd0 : d ≠ 0 := ne_of_gt hd
  have horigin : L.IsRational K.origin := (hKL K.origin).mp K.origin_isRational
  obtain ⟨o, ho⟩ := (L.isRational_iff_toCoords K.origin).mp horigin
  let Λ : AddSubgroup ZPair := rotatedIntLattice a b
  let H₀ : AddSubgroup ZPair := scalarIntLattice (d * d)
  let K₀ : AddSubgroup ZPair := rotatedIntLattice (d * a) (d * b)
  have hHle : H₀ ≤ Λ := by
    exact scalarIntLattice_le_rotated (dvd_refl d) hab
  have hKle : K₀ ≤ Λ := rotatedIntLattice_multiple_le a b d
  let H : AddSubgroup Λ := H₀.comap Λ.subtype
  let J : AddSubgroup Λ := K₀.comap Λ.subtype
  have hHindex : H.index = d.natAbs ^ 2 := by
    exact scaled_rot_card_fundamental hd hd (dvd_refl d) hab
  have hJindex : J.index = d.natAbs ^ 2 := by
    exact rotatedIntLattice_multiple_relIndex hd hab
  letI : H.FiniteIndex := ⟨by rw [hHindex]; positivity⟩
  letI : J.FiniteIndex := ⟨by rw [hJindex]; positivity⟩
  letI : Fintype (Λ ⧸ H) := AddSubgroup.fintypeQuotientOfFiniteIndex
  letI : Fintype (Λ ⧸ J) := AddSubgroup.fintypeQuotientOfFiniteIndex
  have hcard : Fintype.card (Λ ⧸ H) = Fintype.card (Λ ⧸ J) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hHindex.trans hJindex.symm
  let A : Set Λ := {u | L.fromCoords (ratPoint (o + scaledRatPoint (d * d) u)) ∈ S}
  have hAHit : HitsCosets A H := by
    intro x
    obtain ⟨p, hpS, z, hpz⟩ := hhit (o + scaledRatPoint (d * d) x)
    let δ : ZPair := fun i ↦ x.1 i + (d * d) * z i
    have hδ : δ ∈ Λ := by
      apply Λ.add_mem x.2
      apply hHle
      refine ⟨z, ?_⟩
      ext i
      fin_cases i <;> simp [H₀, scalarIntLattice, rotIntLinear, δ]
    let y : Λ := ⟨δ, hδ⟩
    refine ⟨y, ?_, ?_⟩
    · change L.fromCoords (ratPoint (o + scaledRatPoint (d * d) y)) ∈ S
      rw [show L.fromCoords (ratPoint (o + scaledRatPoint (d * d) y)) = p by
        rw [hpz]
        apply congrArg L.fromCoords
        ext i
        fin_cases i <;> simp [y, δ, scaledRatPoint, ratPoint]
        · field_simp
          ring
        · field_simp
          ring]
      exact hpS
    · change y.1 - x.1 ∈ H₀
      refine ⟨z, ?_⟩
      ext i
      fin_cases i <;> simp [y, δ, H₀, scalarIntLattice, rotIntLinear]
  have hASep : SeparatedMod A J := by
    intro u hu v hv huv
    change u.1 - v.1 ∈ K₀ at huv
    obtain ⟨z, hz⟩ := huv
    let pu := L.fromCoords (ratPoint (o + scaledRatPoint (d * d) u))
    let pv := L.fromCoords (ratPoint (o + scaledRatPoint (d * d) v))
    have hdist : distSq pu pv = ((z 0) ^ 2 + (z 1) ^ 2 : ℤ) := by
      rw [L.distSq_fromCoords]
      simp [pu, pv, distSq, Fin.sum_univ_two, scaledRatPoint, ratPoint]
      have hz0 := congrArg (fun w : ZPair ↦ w 0) hz
      have hz1 := congrArg (fun w : ZPair ↦ w 1) hz
      simp [K₀, rotIntLinear] at hz0 hz1
      have hz0R : (d : ℝ) * (a : ℝ) * (z 0 : ℝ) -
          (d : ℝ) * (b : ℝ) * (z 1 : ℝ) = (u.1 0 : ℝ) - (v.1 0 : ℝ) := by
        exact_mod_cast hz0
      have hz1R : (d : ℝ) * (b : ℝ) * (z 0 : ℝ) +
          (d : ℝ) * (a : ℝ) * (z 1 : ℝ) = (u.1 1 : ℝ) - (v.1 1 : ℝ) := by
        exact_mod_cast hz1
      push_cast at ⊢
      field_simp [hd0]
      rw [← hz0R, ← hz1R]
      have habR : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 = (d : ℝ) ^ 2 := by exact_mod_cast hab
      calc
        ((d : ℝ) * (a : ℝ) * (z 0 : ℝ) - (d : ℝ) * (b : ℝ) * (z 1 : ℝ)) ^ 2 +
            ((d : ℝ) * (b : ℝ) * (z 0 : ℝ) + (d : ℝ) * (a : ℝ) * (z 1 : ℝ)) ^ 2 =
            (d : ℝ) ^ 2 * ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) *
              ((z 0 : ℝ) ^ 2 + (z 1 : ℝ) ^ 2) := by ring
        _ = (d : ℝ) ^ 4 * ((z 0 : ℝ) ^ 2 + (z 1 : ℝ) ^ 2) := by rw [habR]; ring
    have hpq : pu = pv := by
      by_contra hpq
      exact hpartial hu hv hpq ((z 0) ^ 2 + (z 1) ^ 2) hdist
    apply Subtype.ext
    apply funext
    intro i
    have hc := congrArg (fun p : Point ↦ (L.toCoords p) i) hpq
    simp [pu, pv, L.toCoords_fromCoords, scaledRatPoint, ratPoint] at hc
    have hdr : (d : ℝ) * (d : ℝ) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hd0) (by exact_mod_cast hd0)
    have hc' : ((u.1 i : ℤ) : ℝ) = ((v.1 i : ℤ) : ℝ) :=
      (div_left_inj' hdr).mp hc
    exact_mod_cast hc'
  have hAJ : HitsCosets A J := hitsCosets_of_equal_index A H J hcard hAHit hASep
  obtain ⟨u, huA, huJ⟩ := hAJ 0
  have huJ' : u ∈ J := by simpa using huJ
  change u.1 ∈ K₀ at huJ'
  obtain ⟨z, hz⟩ := huJ'
  let p := L.fromCoords (ratPoint (o + scaledRatPoint (d * d) u))
  refine ⟨p, huA, z, ?_⟩
  apply L.toCoords_injective
  rw [L.toCoords_fromCoords, L.toCoords_fromCoords_other K, ho]
  ext i
  fin_cases i
  · have hz0 := congrArg (fun w : ZPair ↦ w 0) hz
    simp [p, scaledRatPoint, K₀, rotIntLinear, hA, hB, ratPoint] at hz0 ⊢
    have hz0R : (d : ℝ) * (a : ℝ) * (z 0 : ℝ) -
        (d : ℝ) * (b : ℝ) * (z 1 : ℝ) = (u.1 0 : ℝ) := by exact_mod_cast hz0
    push_cast at ⊢
    field_simp [hd0]
    nlinarith [hz0R]
  · have hz1 := congrArg (fun w : ZPair ↦ w 1) hz
    simp [p, scaledRatPoint, K₀, rotIntLinear, hA, hB, ratPoint] at hz1 ⊢
    have hz1R : (d : ℝ) * (b : ℝ) * (z 0 : ℝ) +
        (d : ℝ) * (a : ℝ) * (z 1 : ℝ) = (u.1 1 : ℝ) := by exact_mod_cast hz1
    push_cast at ⊢
    field_simp [hd0]
    nlinarith [hz1R]

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/FinalBridge.lean` -/

section
/-!
# The final geometric bridge for Erdős Problem 215

The global construction is naturally phrased as hitting every rational
equivalence class of oriented lattices.  This file converts that conclusion
to the inverse-motion formulation used by the literal problem statement.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Hitting every rational class of oriented lattice frames entails hitting
the inverse image of the integer lattice under every direct rigid motion. -/
theorem hitsEveryLattice_of_hitsEveryRationalClass {S : Set Point}
    (h : ∀ L K : OrientedFrame, K.RationallyEquivalent L →
      ∃ p : Point, p ∈ S ∧ K.IsLatticePoint p) :
    HitsEveryLattice S := by
  intro t c s hcs
  let L : OrientedFrame :=
    { origin := inverseMotion t c s 0
      c := c
      s := -s
      unit := by nlinarith }
  obtain ⟨p, hpS, hpL⟩ := h L L (OrientedFrame.rationallyEquivalent_refl L)
  rcases hpL with ⟨z, rfl⟩
  refine ⟨z, ?_⟩
  simpa only [L, OrientedFrame.fromCoords, inverseMotion, rotate_zero,
    zero_sub, rotate_neg, rotate_sub, rotate_add, sub_eq_add_neg, add_comm,
    add_zero] using hpS

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/PoolGeometry.lean` -/

section
/-!
# Framed lines and finite-line avoidance

This file packages the elementary plane geometry used when constructing the
candidate pools in the Jackson--Mauldin argument.  Lines are recorded in the
coordinates of a fixed oriented frame.  This makes both the rational-distance
line lemma and the integer-slope avoidance argument independent of affine-map
bookkeeping.
-/

open Set

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Two points have rational squared distance. -/
def HasRationalSqDist (x y : Point) : Prop :=
  ∃ q : ℚ, distSq x y = (q : ℝ)

/-- An affine line, expressed in the coordinates of the frame `L`. -/
structure FramedLine (L : OrientedFrame) where
  point : Point
  direction : Point
  direction_ne : direction ≠ 0

namespace FramedLine

variable {L : OrientedFrame}

/-- The ambient carrier of a line recorded in `L`-coordinates. -/
def carrier (line : FramedLine L) : Set Point :=
  {x | L.toCoords x ∈ affineLine line.point line.direction}

end FramedLine

/-- Passing to frame coordinates preserves squared distance. -/
lemma OrientedFrame.distSq_toCoords (L : OrientedFrame) (p q : Point) :
    distSq (L.toCoords p) (L.toCoords q) = distSq p q := by
  simpa only [L.fromCoords_toCoords] using
    (L.distSq_fromCoords (L.toCoords p) (L.toCoords q)).symm

/-- In a fixed frame, rational points at rational squared distance from an
irrational point lie on one framed affine line. -/
theorem framed_rational_sqDist_line {L : OrientedFrame} {c : Point}
    (hc : ¬L.IsRational c) :
    ∃ line : FramedLine L, ∀ z : Point,
      L.IsRational z → HasRationalSqDist c z → z ∈ line.carrier := by
  have hc' : ¬IsStandardRational (L.toCoords c) := by
    intro h
    apply hc
    rcases h with ⟨q, hq⟩
    exact (L.isRational_iff_toCoords c).2 ⟨q, hq⟩
  obtain ⟨p, v, hv, hline⟩ := rational_sqDist_subset_line hc'
  refine ⟨⟨p, v, hv⟩, ?_⟩
  intro z hz ⟨r, hr⟩
  apply hline
  constructor
  · rcases (L.isRational_iff_toCoords z).1 hz with ⟨q, hq⟩
    exact ⟨q, hq⟩
  · refine ⟨r, ?_⟩
    rw [L.distSq_toCoords, distSq_comm, hr]

/-- Every point in a rational translate has rational coordinates in its
frame. -/
theorem isRational_of_mem_rationalTranslate {L : OrientedFrame}
    {q : RatPoint} {x : Point} (hx : x ∈ L.rationalTranslate q) :
    L.IsRational x := by
  rcases hx with ⟨z, rfl⟩
  let r : RatPoint := fun i ↦ q i + z i
  refine ⟨r, ?_⟩
  apply congrArg L.fromCoords
  ext i
  simp [r, ratPoint, intPoint]

/-- Two points rational in the same frame have rational squared distance. -/
theorem hasRationalSqDist_of_isRational {L : OrientedFrame} {x y : Point}
    (hx : L.IsRational x) (hy : L.IsRational y) :
    HasRationalSqDist x y := by
  rcases hx with ⟨q, rfl⟩
  rcases hy with ⟨r, rfl⟩
  refine ⟨(q 0 - r 0) ^ 2 + (q 1 - r 1) ^ 2, ?_⟩
  rw [L.distSq_fromCoords]
  simp [distSq, Fin.sum_univ_two, ratPoint]

/-- Two points in the same rational translate have integral squared
distance. -/
theorem exists_int_distSq_of_mem_rationalTranslate {L : OrientedFrame}
    {q : RatPoint} {x y : Point}
    (hx : x ∈ L.rationalTranslate q)
    (hy : y ∈ L.rationalTranslate q) :
    ∃ n : ℤ, distSq x y = (n : ℝ) := by
  rcases hx with ⟨z, rfl⟩
  rcases hy with ⟨w, rfl⟩
  refine ⟨intDistSq z w, ?_⟩
  rw [L.distSq_fromCoords]
  simp [distSq, intDistSq, Fin.sum_univ_two, ratPoint, intPoint]

/-- One rank-two residue sublattice in the coordinates of `L`. -/
def FramedResidueSet (L : OrientedFrame) (d : ℕ) (i j : Fin d)
    (a b : ℤ) : Set Point :=
  {x | ∃ k l : ℤ,
    x = L.fromCoords
      (ratPoint (fun r ↦ if r = 0 then (i : ℕ) / d + k else (j : ℕ) / d + l)) ∧
    a ≡ k [ZMOD d] ∧ b ≡ l [ZMOD d]}

/-- An arithmetic progression in a direction not parallel to a line meets
that line in at most one parameter. -/
lemma affineLine_integer_progression_subsingleton
    {base direction p v : Point} (hnonparallel : det₂ direction v ≠ 0) :
    {m : ℤ | base + (m : ℝ) • direction ∈ affineLine p v}.Subsingleton := by
  intro m hm n hn
  obtain ⟨s, hs⟩ := hm
  obtain ⟨t, ht⟩ := hn
  by_contra hmn
  have hmnR : (m : ℝ) - (n : ℝ) ≠ 0 := by
    exact sub_ne_zero.mpr (Int.cast_injective.ne hmn)
  have hs0 := congrArg (fun x : Point ↦ x 0) hs
  have hs1 := congrArg (fun x : Point ↦ x 1) hs
  have ht0 := congrArg (fun x : Point ↦ x 0) ht
  have ht1 := congrArg (fun x : Point ↦ x 1) ht
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hs0 hs1 ht0 ht1
  have h0 : ((m : ℝ) - (n : ℝ)) * direction 0 = (s - t) * v 0 := by
    linarith
  have h1 : ((m : ℝ) - (n : ℝ)) * direction 1 = (s - t) * v 1 := by
    linarith
  apply hnonparallel
  apply (mul_eq_zero.mp ?_).resolve_left hmnR
  calc
    ((m : ℝ) - (n : ℝ)) * det₂ direction v =
        (((m : ℝ) - (n : ℝ)) * direction 0) * v 1 -
          (((m : ℝ) - (n : ℝ)) * direction 1) * v 0 := by
            simp only [det₂]
            ring
    _ = ((s - t) * v 0) * v 1 - ((s - t) * v 1) * v 0 := by
      rw [h0, h1]
    _ = 0 := by ring

/-- There is an integer slope not parallel to any member of a finite family
of framed lines. -/
lemma exists_integerSlope_nonparallel {L : OrientedFrame}
    (G : Finset (FramedLine L)) :
    ∃ T : ℤ, ∀ line ∈ G,
      line.direction 1 - (T : ℝ) * line.direction 0 ≠ 0 := by
  let bad : Set ℤ := ⋃ line : {line // line ∈ G},
    {T : ℤ | (T : ℝ) * line.1.direction 0 = line.1.direction 1}
  have hsingle : ∀ line : {line // line ∈ G},
      {T : ℤ | (T : ℝ) * line.1.direction 0 =
        line.1.direction 1}.Subsingleton := by
    intro line m hm n hn
    have hv0 : line.1.direction 0 ≠ 0 := by
      intro hv0
      have hv1 : line.1.direction 1 = 0 := by
        simpa only [hv0, mul_zero] using hm.symm
      apply line.1.direction_ne
      ext r
      fin_cases r
      · simpa using hv0
      · simpa using hv1
    have hcast : (m : ℝ) = (n : ℝ) := by
      apply (mul_right_cancel₀ hv0)
      exact hm.trans hn.symm
    exact_mod_cast hcast
  have hbad : bad.Finite := by
    apply Set.finite_iUnion
    intro line
    exact (hsingle line).finite
  obtain ⟨T, -, hT⟩ := (Set.infinite_univ : (Set.univ : Set ℤ).Infinite).exists_notMem_finite hbad
  refine ⟨T, ?_⟩
  intro line hline hzero
  apply hT
  apply mem_iUnion.2
  refine ⟨⟨line, hline⟩, ?_⟩
  exact (sub_eq_zero.mp hzero).symm

/-- A rank-two residue sublattice still has infinitely many points after
removing a finite exceptional set and finitely many framed affine lines.

This is the exact robust form needed for pool richness: the exceptional set
can be the finitely many rational points outside a Davies layer. -/
theorem framedResidueSet_infinite_avoid {L : OrientedFrame}
    {d : ℕ} (hd : d ≠ 0) (i j : Fin d) (a b : ℤ)
    (G : Finset (FramedLine L)) {E : Set Point} (hE : E.Finite) :
    Set.Infinite {x : Point |
      x ∈ FramedResidueSet L d i j a b ∧ x ∉ E ∧
        ∀ line ∈ G, x ∉ line.carrier} := by
  obtain ⟨T, hT⟩ := exists_integerSlope_nonparallel G
  let q : ℤ → RatPoint := fun m r ↦
    if r = 0 then (i : ℕ) / d + (a + d * m : ℤ)
    else (j : ℕ) / d + (b + d * T * m : ℤ)
  let base : Point := ratPoint (fun r ↦
    if r = 0 then (i : ℕ) / d + a else (j : ℕ) / d + b)
  let direction : Point := WithLp.toLp 2 fun r ↦
    if r = 0 then (d : ℝ) else (d : ℝ) * (T : ℝ)
  let coord : ℤ → Point := fun m ↦ base + (m : ℝ) • direction
  let f : ℤ → Point := fun m ↦ L.fromCoords (coord m)
  have hcoord (m : ℤ) : coord m = ratPoint (q m) := by
    ext r
    fin_cases r
    · simp [coord, base, direction, q, ratPoint]
      ring
    · simp [coord, base, direction, q, ratPoint]
      ring
  have hf : Function.Injective f := by
    intro m n hmn
    have hc : coord m = coord n := L.fromCoords_injective hmn
    have hc0 := congrArg (fun x : Point ↦ x 0) hc
    simp [coord, direction] at hc0
    rcases hc0 with hmn | hd0
    · exact hmn
    · exact (hd hd0).elim
  have hnonparallel (line : FramedLine L) (hline : line ∈ G) :
      det₂ direction line.direction ≠ 0 := by
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    have hslope := hT line hline
    rw [show det₂ direction line.direction =
        (d : ℝ) * (line.direction 1 - (T : ℝ) * line.direction 0) by
      simp [det₂, direction]
      ring]
    exact mul_ne_zero hdR hslope
  let badLines : Set ℤ := ⋃ line : {line // line ∈ G},
    {m : ℤ | f m ∈ line.1.carrier}
  have hbadLines : badLines.Finite := by
    apply Set.finite_iUnion
    intro line
    apply (affineLine_integer_progression_subsingleton
      (hnonparallel line.1 line.2)).finite.subset
    intro m hm
    change L.toCoords (L.fromCoords (coord m)) ∈
      affineLine line.1.point line.1.direction at hm
    change coord m ∈ affineLine line.1.point line.1.direction
    simpa only [L.toCoords_fromCoords] using hm
  let bad : Set ℤ := f ⁻¹' E ∪ badLines
  have hbad : bad.Finite := by
    apply Set.Finite.union
    · exact hE.preimage hf.injOn
    · exact hbadLines
  have hgood : (Set.univ \ bad).Infinite :=
    Set.infinite_univ.sdiff hbad
  have himage : (f '' (Set.univ \ bad)).Infinite :=
    hgood.image hf.injOn
  apply himage.mono
  intro x hx
  rcases hx with ⟨m, hm, rfl⟩
  have hmE : f m ∉ E := by
    intro hfm
    exact hm.2 (Or.inl hfm)
  have hmLines : ∀ line ∈ G, f m ∉ line.carrier := by
    intro line hline hmline
    apply hm.2
    apply Or.inr
    apply mem_iUnion.2
    exact ⟨⟨line, hline⟩, hmline⟩
  refine ⟨?_, hmE, hmLines⟩
  refine ⟨a + d * m, b + d * T * m, ?_, ?_, ?_⟩
  · rw [← hcoord]
  · exact Int.modEq_iff_dvd.2 ⟨m, by ring⟩
  · exact Int.modEq_iff_dvd.2 ⟨T * m, by ring⟩

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/Selector.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
Finite arithmetic used in the Jackson--Mauldin rational-translate selector.

The main point of this file is to isolate the exact numerator appearing in
Equation (4.2) of the mathematical proof.  This makes the finite selector
condition a statement about divisibility in `ℤ`, with no ambiguity about
division in a residue ring.
-/

namespace Selector

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

abbrev RatPoint := ℚ × ℚ

/-- Squared Euclidean distance on rational coordinate pairs. -/
def sqDist (x y : RatPoint) : ℚ :=
  (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2

/-- The point selected above residue `(i,j)` modulo `d`, with integral lift `(k,l)`. -/
def liftedPoint (d : ℕ) (i j : Fin d) (k l : ℤ) : RatPoint :=
  (((i : ℕ) : ℚ) / d + k, ((j : ℕ) : ℚ) / d + l)

/-- The integral numerator in the squared-distance calculation (4.2). -/
def conflictNumerator (d : ℕ) (i₁ j₁ i₂ j₂ : Fin d) (k₁ l₁ k₂ l₂ : ℤ) : ℤ :=
  let A := ((i₁ : ℕ) : ℤ) - ((i₂ : ℕ) : ℤ)
  let B := ((j₁ : ℕ) : ℤ) - ((j₂ : ℕ) : ℤ)
  let K := k₁ - k₂
  let M := l₁ - l₂
  A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M)

/-- The literal numerator of the squared distance.  It differs from
`conflictNumerator` by a multiple of `d²`. -/
def distanceNumerator (d : ℕ) (i₁ j₁ i₂ j₂ : Fin d) (k₁ l₁ k₂ l₂ : ℤ) : ℤ :=
  let K := k₁ - k₂
  let M := l₁ - l₂
  conflictNumerator d i₁ j₁ i₂ j₂ k₁ l₁ k₂ l₂ + (d : ℤ) ^ 2 * (K ^ 2 + M ^ 2)

lemma sqDist_liftedPoint (d : ℕ) (hd : d ≠ 0)
    (i₁ j₁ i₂ j₂ : Fin d) (k₁ l₁ k₂ l₂ : ℤ) :
    sqDist (liftedPoint d i₁ j₁ k₁ l₁) (liftedPoint d i₂ j₂ k₂ l₂) =
      (distanceNumerator d i₁ j₁ i₂ j₂ k₁ l₁ k₂ l₂ : ℚ) / (d : ℚ) ^ 2 := by
  simp only [sqDist, liftedPoint, distanceNumerator, conflictNumerator]
  push_cast
  field_simp [hd]
  ring

lemma distanceNumerator_dvd_iff (d : ℕ) (i₁ j₁ i₂ j₂ : Fin d) (k₁ l₁ k₂ l₂ : ℤ) :
    (d : ℤ) ^ 2 ∣ distanceNumerator d i₁ j₁ i₂ j₂ k₁ l₁ k₂ l₂ ↔
      (d : ℤ) ^ 2 ∣ conflictNumerator d i₁ j₁ i₂ j₂ k₁ l₁ k₂ l₂ := by
  let Q : ℤ := (k₁ - k₂) ^ 2 + (l₁ - l₂) ^ 2
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z - Q, ?_⟩
    simp only [distanceNumerator, Q] at hz ⊢
    linear_combination hz
  · rintro ⟨z, hz⟩
    refine ⟨z + Q, ?_⟩
    simp only [distanceNumerator, Q] at hz ⊢
    linear_combination hz

/-- A rational number `N / d²` is integral exactly when `d² ∣ N`. -/
lemma div_sq_isInt_iff (d : ℕ) (hd : d ≠ 0) (N : ℤ) :
    (∃ z : ℤ, (N : ℚ) / (d : ℚ) ^ 2 = z) ↔ (d : ℤ) ^ 2 ∣ N := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    field_simp [hdq] at hz
    exact_mod_cast hz
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    push_cast
    field_simp [hdq]

/-- Exact integrality criterion (4.2). -/
theorem sqDist_liftedPoint_isInt_iff (d : ℕ) (hd : d ≠ 0)
    (i₁ j₁ i₂ j₂ : Fin d) (k₁ l₁ k₂ l₂ : ℤ) :
    (∃ z : ℤ,
        sqDist (liftedPoint d i₁ j₁ k₁ l₁) (liftedPoint d i₂ j₂ k₂ l₂) = z) ↔
      (d : ℤ) ^ 2 ∣ conflictNumerator d i₁ j₁ i₂ j₂ k₁ l₁ k₂ l₂ := by
  rw [sqDist_liftedPoint d hd]
  rw [div_sq_isInt_iff d hd]
  exact distanceNumerator_dvd_iff d i₁ j₁ i₂ j₂ k₁ l₁ k₂ l₂

/-- Integral lift data over all `d²` residue pairs. -/
structure LiftData (d : ℕ) where
  k : Fin d → Fin d → ℤ
  l : Fin d → Fin d → ℤ

namespace LiftData

def point {d : ℕ} (s : LiftData d) (i j : Fin d) : RatPoint :=
  liftedPoint d i j (s.k i j) (s.l i j)

/-- The finite selector condition `(*)_d`, written without division. -/
def Separated {d : ℕ} (s : LiftData d) : Prop :=
  ∀ i₁ j₁ i₂ j₂, (i₁, j₁) ≠ (i₂, j₂) →
    ¬(d : ℤ) ^ 2 ∣
      conflictNumerator d i₁ j₁ i₂ j₂
        (s.k i₁ j₁) (s.l i₁ j₁) (s.k i₂ j₂) (s.l i₂ j₂)

theorem separated_iff_sqDist_not_int {d : ℕ} (hd : d ≠ 0) (s : LiftData d) :
    s.Separated ↔
      ∀ i₁ j₁ i₂ j₂, (i₁, j₁) ≠ (i₂, j₂) →
        ¬∃ z : ℤ, sqDist (s.point i₁ j₁) (s.point i₂ j₂) = z := by
  simp only [Separated, point]
  constructor
  · intro h i₁ j₁ i₂ j₂ hne hz
    exact h i₁ j₁ i₂ j₂ hne
      ((sqDist_liftedPoint_isInt_iff d hd i₁ j₁ i₂ j₂
        (s.k i₁ j₁) (s.l i₁ j₁) (s.k i₂ j₂) (s.l i₂ j₂)).mp hz)
  · intro h i₁ j₁ i₂ j₂ hne hdiv
    exact h i₁ j₁ i₂ j₂ hne
      ((sqDist_liftedPoint_isInt_iff d hd i₁ j₁ i₂ j₂
        (s.k i₁ j₁) (s.l i₁ j₁) (s.k i₂ j₂) (s.l i₂ j₂)).mpr hdiv)

/-- The zero lift is already a separated selector at denominator two. -/
def initialTwo : LiftData 2 where
  k := fun _ _ ↦ 0
  l := fun _ _ ↦ 0

theorem initialTwo_separated : initialTwo.Separated := by
  intro i₁ j₁ i₂ j₂ hne hdiv
  have hval : (i₁ : ℕ) ≠ (i₂ : ℕ) ∨ (j₁ : ℕ) ≠ (j₂ : ℕ) := by
    by_contra h
    have hiEq : (i₁ : ℕ) = (i₂ : ℕ) := by
      by_contra hiNe
      exact h (Or.inl hiNe)
    have hjEq : (j₁ : ℕ) = (j₂ : ℕ) := by
      by_contra hjNe
      exact h (Or.inr hjNe)
    apply hne
    exact Prod.ext (Fin.ext hiEq) (Fin.ext hjEq)
  have hi : (i₁ : ℕ) = 0 ∨ (i₁ : ℕ) = 1 := by omega
  have hi' : (i₂ : ℕ) = 0 ∨ (i₂ : ℕ) = 1 := by omega
  have hj : (j₁ : ℕ) = 0 ∨ (j₁ : ℕ) = 1 := by omega
  have hj' : (j₂ : ℕ) = 0 ∨ (j₂ : ℕ) = 1 := by omega
  rcases hi with hi | hi <;> rcases hi' with hi' | hi' <;>
    rcases hj with hj | hj <;> rcases hj' with hj' | hj' <;>
    simp [initialTwo, conflictNumerator, hi, hi', hj, hj'] at hdiv <;> omega

/-- `t` changes every integral lift in `s` by a multiple of the denominator.
This is the freedom used to force a finite selector into a prescribed rich pool. -/
def Congruent {d : ℕ} (s t : LiftData d) : Prop :=
  ∀ i j, ∃ a b : ℤ,
    t.k i j = s.k i j + d * a ∧ t.l i j = s.l i j + d * b

lemma conflictNumerator_congruent {d : ℕ} {s t : LiftData d}
    (hst : s.Congruent t) (i₁ j₁ i₂ j₂ : Fin d) :
    (d : ℤ) ^ 2 ∣
      conflictNumerator d i₁ j₁ i₂ j₂
          (t.k i₁ j₁) (t.l i₁ j₁) (t.k i₂ j₂) (t.l i₂ j₂) -
        conflictNumerator d i₁ j₁ i₂ j₂
          (s.k i₁ j₁) (s.l i₁ j₁) (s.k i₂ j₂) (s.l i₂ j₂) := by
  rcases hst i₁ j₁ with ⟨a₁, b₁, hk₁, hl₁⟩
  rcases hst i₂ j₂ with ⟨a₂, b₂, hk₂, hl₂⟩
  let A : ℤ := ((i₁ : ℕ) : ℤ) - ((i₂ : ℕ) : ℤ)
  let B : ℤ := ((j₁ : ℕ) : ℤ) - ((j₂ : ℕ) : ℤ)
  refine ⟨2 * (A * (a₁ - a₂) + B * (b₁ - b₂)), ?_⟩
  simp only [conflictNumerator]
  rw [hk₁, hl₁, hk₂, hl₂]
  dsimp [A, B]
  ring

lemma dvd_conflict_iff_of_congruent {d : ℕ} {s t : LiftData d}
    (hst : s.Congruent t) (i₁ j₁ i₂ j₂ : Fin d) :
    ((d : ℤ) ^ 2 ∣
      conflictNumerator d i₁ j₁ i₂ j₂
        (t.k i₁ j₁) (t.l i₁ j₁) (t.k i₂ j₂) (t.l i₂ j₂)) ↔
    ((d : ℤ) ^ 2 ∣
      conflictNumerator d i₁ j₁ i₂ j₂
        (s.k i₁ j₁) (s.l i₁ j₁) (s.k i₂ j₂) (s.l i₂ j₂)) := by
  have hdiff := conflictNumerator_congruent hst i₁ j₁ i₂ j₂
  rcases hdiff with ⟨q, hq⟩
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z - q, ?_⟩
    linear_combination hz - hq
  · rintro ⟨z, hz⟩
    refine ⟨z + q, ?_⟩
    linear_combination hz + hq

theorem separated_of_congruent {d : ℕ} {s t : LiftData d}
    (hs : s.Separated) (hst : s.Congruent t) : t.Separated := by
  intro i₁ j₁ i₂ j₂ hne ht
  exact hs i₁ j₁ i₂ j₂ hne
    ((dvd_conflict_iff_of_congruent hst i₁ j₁ i₂ j₂).mp ht)

/-- A finite version of the rich-pool forcing step.  Once a separated residue
selector exists, one may independently replace every selected lift by any
congruent lift in `P`, without losing separation. -/
theorem choose_congruent_in_pool {d : ℕ} (s : LiftData d) (P : Set RatPoint)
    (hP : ∀ i j, ∃ k l a b : ℤ,
      k = s.k i j + d * a ∧ l = s.l i j + d * b ∧ liftedPoint d i j k l ∈ P) :
    ∃ t : LiftData d, s.Congruent t ∧
      (∀ i j, t.point i j ∈ P) ∧ (s.Separated → t.Separated) := by
  choose k l a b hk hl hp using hP
  let t : LiftData d := ⟨k, l⟩
  have hst : s.Congruent t := by
    intro i j
    exact ⟨a i j, b i j, hk i j, hl i j⟩
  refine ⟨t, hst, ?_, fun hs ↦ separated_of_congruent hs hst⟩
  intro i j
  exact hp i j

end LiftData

/-- The embedding of an old residue when the denominator is multiplied by `p`. -/
def oldIndex (p : ℕ) (hp : 0 < p) {d : ℕ} (i : Fin d) : Fin (p * d) :=
  ⟨p * (i : ℕ), (Nat.mul_lt_mul_left hp).2 i.isLt⟩

lemma oldIndex_injective (p : ℕ) (hp : 0 < p) {d : ℕ} :
    Function.Injective (oldIndex p hp : Fin d → Fin (p * d)) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  change p * (i : ℕ) = p * (j : ℕ) at hv
  exact Fin.ext (Nat.mul_left_cancel hp hv)

lemma liftedPoint_oldIndex (p d : ℕ) (hp : 0 < p) (hd : d ≠ 0)
    (i j : Fin d) (k l : ℤ) :
    liftedPoint (p * d) (oldIndex p hp i) (oldIndex p hp j) k l =
      liftedPoint d i j k l := by
  apply Prod.ext <;> simp only [liftedPoint, oldIndex]
  · congr 1
    push_cast
    field_simp [Nat.ne_of_gt hp, hd]
  · congr 1
    push_cast
    field_simp [Nat.ne_of_gt hp, hd]

/-- Literal extension of the integral lifts from denominator `d` to `p*d`. -/
def PrimeExtends (p : ℕ) (hp : 0 < p) {d : ℕ}
    (s : LiftData d) (t : LiftData (p * d)) : Prop :=
  ∀ i j,
    t.k (oldIndex p hp i) (oldIndex p hp j) = s.k i j ∧
    t.l (oldIndex p hp i) (oldIndex p hp j) = s.l i j

lemma point_oldIndex_of_primeExtends (p : ℕ) (hp : 0 < p) {d : ℕ} (hd : d ≠ 0)
    {s : LiftData d} {t : LiftData (p * d)} (hst : PrimeExtends p hp s t)
    (i j : Fin d) :
    t.point (oldIndex p hp i) (oldIndex p hp j) = s.point i j := by
  rcases hst i j with ⟨hk, hl⟩
  simp only [LiftData.point, hk, hl]
  exact liftedPoint_oldIndex p d hp hd i j (s.k i j) (s.l i j)

/-- Quotient and parity of a residue at doubled denominator. -/
def halfIndex {d : ℕ} (i : Fin (2 * d)) : Fin d :=
  ⟨(i : ℕ) / 2, by omega⟩

def parity {d : ℕ} (i : Fin (2 * d)) : ℕ :=
  (i : ℕ) % 2

lemma parity_lt_two {d : ℕ} (i : Fin (2 * d)) : parity i < 2 := by
  exact Nat.mod_lt _ (by omega)

lemma val_eq_two_mul_half_add_parity {d : ℕ} (i : Fin (2 * d)) :
    (i : ℕ) = 2 * (halfIndex i : ℕ) + parity i := by
  simp only [halfIndex, parity]
  omega

/-- The forward extension across the trivial prime `2`: copy the old lift on
each of the four parity cosets. -/
def doubleLift {d : ℕ} (s : LiftData d) : LiftData (2 * d) where
  k := fun i j ↦ s.k (halfIndex i) (halfIndex j)
  l := fun i j ↦ s.l (halfIndex i) (halfIndex j)

lemma halfIndex_oldIndex_two {d : ℕ} (i : Fin d) :
    halfIndex (oldIndex 2 (by omega) i) = i := by
  apply Fin.ext
  change (2 * (i : ℕ)) / 2 = (i : ℕ)
  omega

lemma doubleLift_primeExtends {d : ℕ} (s : LiftData d) :
    PrimeExtends 2 (by omega) s (doubleLift s) := by
  intro i j
  simp [doubleLift, halfIndex_oldIndex_two]

lemma sqDist_doubleLift_of_same_parity {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (i₁ j₁ i₂ j₂ : Fin (2 * d))
    (hi : parity i₁ = parity i₂) (hj : parity j₁ = parity j₂) :
    sqDist ((doubleLift s).point i₁ j₁) ((doubleLift s).point i₂ j₂) =
      sqDist (s.point (halfIndex i₁) (halfIndex j₁))
        (s.point (halfIndex i₂) (halfIndex j₂)) := by
  have hvi₁ := val_eq_two_mul_half_add_parity i₁
  have hvi₂ := val_eq_two_mul_half_add_parity i₂
  have hvj₁ := val_eq_two_mul_half_add_parity j₁
  have hvj₂ := val_eq_two_mul_half_add_parity j₂
  simp only [LiftData.point, doubleLift, liftedPoint, sqDist]
  push_cast
  field_simp [hd]
  rw [hvi₁, hvi₂, hvj₁, hvj₂, hi, hj]
  push_cast
  ring

lemma doubleLift_cross_not_integral {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (i₁ j₁ i₂ j₂ : Fin (2 * d))
    (hbit : parity i₁ ≠ parity i₂ ∨ parity j₁ ≠ parity j₂) :
    ¬∃ z : ℤ, sqDist ((doubleLift s).point i₁ j₁) ((doubleLift s).point i₂ j₂) = z := by
  intro hInt
  have hd2 : 2 * d ≠ 0 := Nat.mul_ne_zero (by omega) hd
  have hdiv := (sqDist_liftedPoint_isInt_iff (2 * d) hd2 i₁ j₁ i₂ j₂
    ((doubleLift s).k i₁ j₁) ((doubleLift s).l i₁ j₁)
    ((doubleLift s).k i₂ j₂) ((doubleLift s).l i₂ j₂)).mp hInt
  rcases hdiv with ⟨z, hz⟩
  have hvi₁ := val_eq_two_mul_half_add_parity i₁
  have hvi₂ := val_eq_two_mul_half_add_parity i₂
  have hvj₁ := val_eq_two_mul_half_add_parity j₁
  have hvj₂ := val_eq_two_mul_half_add_parity j₂
  have hpi₁ : parity i₁ = 0 ∨ parity i₁ = 1 := by
    have := parity_lt_two i₁
    omega
  have hpi₂ : parity i₂ = 0 ∨ parity i₂ = 1 := by
    have := parity_lt_two i₂
    omega
  have hpj₁ : parity j₁ = 0 ∨ parity j₁ = 1 := by
    have := parity_lt_two j₁
    omega
  have hpj₂ : parity j₂ = 0 ∨ parity j₂ = 1 := by
    have := parity_lt_two j₂
    omega
  have h4 : (4 : ZMod 4) = 0 := ZMod.natCast_self 4
  have h8 : (8 : ZMod 4) = 0 := by
    calc
      (8 : ZMod 4) = 4 + 4 := by ring
      _ = 0 := by rw [h4]; exact add_zero 0
  have h1 : (1 : ZMod 4) ≠ 0 := by decide
  have h2 : (2 : ZMod 4) ≠ 0 := by decide
  simp only [doubleLift, conflictNumerator] at hz
  rcases hpi₁ with hpi₁ | hpi₁ <;> rcases hpi₂ with hpi₂ | hpi₂ <;>
    rcases hpj₁ with hpj₁ | hpj₁ <;> rcases hpj₂ with hpj₂ | hpj₂ <;>
    rw [hvi₁, hvi₂, hvj₁, hvj₂, hpi₁, hpi₂, hpj₁, hpj₂] at hz <;>
    simp [hpi₁, hpi₂, hpj₁, hpj₂] at hbit
  all_goals
    have hz4 := congrArg (fun x : ℤ ↦ (x : ZMod 4)) hz
    norm_num at hz4
    ring_nf at hz4
    simp only [h4, h8, mul_zero, add_zero, sub_zero] at hz4
    first | exact h1 hz4 | exact h2 hz4

/-- A fully proved forward prime step for the trivial prime `2`. -/
theorem doubleLift_separated {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (hs : s.Separated) : (doubleLift s).Separated := by
  rw [LiftData.separated_iff_sqDist_not_int (Nat.mul_ne_zero (by omega) hd)]
  intro i₁ j₁ i₂ j₂ hne
  by_cases hi : parity i₁ = parity i₂
  · by_cases hj : parity j₁ = parity j₂
    · have hhalf :
          (halfIndex i₁, halfIndex j₁) ≠ (halfIndex i₂, halfIndex j₂) := by
        intro h
        apply hne
        apply Prod.ext <;> apply Fin.ext
        · have hq := congrArg (fun x : Fin d ↦ (x : ℕ)) (congrArg Prod.fst h)
          rw [val_eq_two_mul_half_add_parity i₁,
            val_eq_two_mul_half_add_parity i₂, hi, hq]
        · have hq := congrArg (fun x : Fin d ↦ (x : ℕ)) (congrArg Prod.snd h)
          rw [val_eq_two_mul_half_add_parity j₁,
            val_eq_two_mul_half_add_parity j₂, hj, hq]
      have hold := (LiftData.separated_iff_sqDist_not_int hd s).mp hs
        (halfIndex i₁) (halfIndex j₁) (halfIndex i₂) (halfIndex j₂) hhalf
      rwa [sqDist_doubleLift_of_same_parity hd s i₁ j₁ i₂ j₂ hi hj]
    · exact doubleLift_cross_not_integral hd s i₁ j₁ i₂ j₂ (Or.inr hj)
  · exact doubleLift_cross_not_integral hd s i₁ j₁ i₂ j₂ (Or.inl hi)

/-- Quotient and remainder of a residue at a denominator enlarged by `p`. -/
def quotientIndex (p : ℕ) {d : ℕ} (i : Fin (p * d)) : Fin d :=
  if hp : 0 < p then
    ⟨(i : ℕ) / p,
      (Nat.div_lt_iff_lt_mul hp).2 (lt_of_lt_of_eq i.isLt (Nat.mul_comm p d))⟩
  else by
    have hp0 : p = 0 := Nat.eq_zero_of_not_pos hp
    subst p
    exact Fin.elim0 (Fin.cast (by simp) i)

def remainderIndex (p : ℕ) {d : ℕ} (i : Fin (p * d)) : ℕ :=
  (i : ℕ) % p

lemma remainderIndex_lt (p : ℕ) (hp : 0 < p) {d : ℕ} (i : Fin (p * d)) :
    remainderIndex p i < p := Nat.mod_lt _ hp

lemma val_eq_mul_quotient_add_remainder (p : ℕ) (hp : 0 < p) {d : ℕ}
    (i : Fin (p * d)) :
    (i : ℕ) = p * (quotientIndex p i : ℕ) + remainderIndex p i := by
  simp only [quotientIndex, hp, ↓reduceDIte, remainderIndex]
  simpa [Nat.add_comm] using (Nat.mod_add_div (i : ℕ) p).symm

/-- Copy an old selector on every coset when multiplying its denominator by `p`. -/
def primeCopyLift (p : ℕ) {d : ℕ} (s : LiftData d) : LiftData (p * d) where
  k := fun i j ↦ s.k (quotientIndex p i) (quotientIndex p j)
  l := fun i j ↦ s.l (quotientIndex p i) (quotientIndex p j)

lemma quotientIndex_oldIndex (p : ℕ) (hp : 0 < p) {d : ℕ} (i : Fin d) :
    quotientIndex p (oldIndex p hp i) = i := by
  apply Fin.ext
  simp only [quotientIndex, hp, ↓reduceDIte, oldIndex]
  rw [Nat.mul_comm]
  exact Nat.mul_div_left (i : ℕ) hp

lemma primeCopy_primeExtends (p : ℕ) (hp : 0 < p) {d : ℕ} (s : LiftData d) :
    PrimeExtends p hp s (primeCopyLift p s) := by
  intro i j
  simp [primeCopyLift, quotientIndex_oldIndex p hp]

/-- An exact algebraic form of the source's condition that a prime be
"trivial": the binary norm form is anisotropic modulo `p`. -/
def NormAnisotropic (p : ℕ) : Prop :=
  ∀ x y : ZMod p, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0

/-- The finite-field fact used by the source for every prime `3 mod 4`. -/
theorem normAnisotropic_of_prime_mod_four_eq_three (p : ℕ) [Fact p.Prime]
    (hp3 : p % 4 = 3) : NormAnisotropic p := by
  intro x y hxy
  by_cases hy : y = 0
  · subst y
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at hxy
    exact ⟨sq_eq_zero_iff.mp hxy, rfl⟩
  · have hsq : x ^ 2 = -(y ^ 2) := by linear_combination hxy
    exact (ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hy hsq hp3).elim

/-- The localized quotient from (4.6a).  The parameter `Dinv` represents the
inverse modulo `q` of the complementary factor `D` in `d = qD`. -/
def localizedQuotient (q : ℕ) (Dinv : ZMod q) (x : ℤ) : ZMod q :=
  ((x / (q : ℤ) : ℤ) : ZMod q) * Dinv

lemma localizedQuotient_mul (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q) (a : ℤ) :
    localizedQuotient q Dinv ((q : ℤ) * a) = (a : ZMod q) * Dinv := by
  simp only [localizedQuotient]
  rw [Int.mul_ediv_cancel_left a (Int.ofNat_ne_zero.mpr hq)]

lemma localizedQuotient_add (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q) (x y : ℤ)
    (hx : (q : ℤ) ∣ x) (hy : (q : ℤ) ∣ y) :
    localizedQuotient q Dinv (x + y) =
      localizedQuotient q Dinv x + localizedQuotient q Dinv y := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  rw [← Int.mul_add, localizedQuotient_mul q hq,
    localizedQuotient_mul q hq, localizedQuotient_mul q hq]
  push_cast
  ring

lemma localizedQuotient_neg (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q) (x : ℤ)
    (hx : (q : ℤ) ∣ x) :
    localizedQuotient q Dinv (-x) = -localizedQuotient q Dinv x := by
  rcases hx with ⟨a, rfl⟩
  rw [← mul_neg, localizedQuotient_mul q hq, localizedQuotient_mul q hq]
  push_cast
  ring

lemma localizedQuotient_sub (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q) (x y : ℤ)
    (hx : (q : ℤ) ∣ x) (hy : (q : ℤ) ∣ y) :
    localizedQuotient q Dinv (x - y) =
      localizedQuotient q Dinv x - localizedQuotient q Dinv y := by
  rw [sub_eq_add_neg, localizedQuotient_add q hq Dinv x (-y) hx (dvd_neg.mpr hy),
    localizedQuotient_neg q hq Dinv y hy]
  rw [sub_eq_add_neg]

/-- The correction-term telescope at the end of the new--new consistency
case (4.15a)--(4.16). -/
lemma localizedQuotient_telescope (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q)
    (j₁ j₂ j₃ j₄ : ℤ)
    (h₃₄ : (q : ℤ) ∣ j₃ - j₄) (h₁₃ : (q : ℤ) ∣ j₁ - j₃)
    (h₂₄ : (q : ℤ) ∣ j₂ - j₄) :
    localizedQuotient q Dinv (j₃ - j₄) + localizedQuotient q Dinv (j₁ - j₃) -
        localizedQuotient q Dinv (j₂ - j₄) =
      localizedQuotient q Dinv (j₁ - j₂) := by
  have hsum : (q : ℤ) ∣ (j₃ - j₄) + (j₁ - j₃) := dvd_add h₃₄ h₁₃
  calc
    _ = localizedQuotient q Dinv ((j₃ - j₄) + (j₁ - j₃)) -
        localizedQuotient q Dinv (j₂ - j₄) := by
          rw [localizedQuotient_add q hq Dinv _ _ h₃₄ h₁₃]
    _ = localizedQuotient q Dinv
        (((j₃ - j₄) + (j₁ - j₃)) - (j₂ - j₄)) := by
          rw [localizedQuotient_sub q hq Dinv _ _ hsum h₂₄]
    _ = localizedQuotient q Dinv (j₁ - j₂) := by ring_nf

/-- Formula (4.16) before replacing the second shift by its equal cross
shift from (S7).  This is a pure ring identity, so it is reusable at every
prime-power component. -/
lemma auxiliaryOldLines_relation {R : Type*} [CommRing R]
    (i s₁ s₂ j₁ j₂ j₃ j₄ lam₁ lam₂ : R)
    (hline : i * (lam₁ - lam₂) = -(j₁ - j₂))
    (haux₁ : (i + s₁) * (lam₁ - lam₂) = -(j₁ - j₃))
    (haux₂ : (i + s₂) * (lam₂ - lam₁) = -(j₂ - j₄)) :
    (i + s₁ + s₂) * (lam₂ - lam₁) = -(j₃ - j₄) := by
  have hj₃₁ : j₃ - j₁ = (i + s₁) * (lam₁ - lam₂) := by
    simpa only [neg_sub] using haux₁.symm
  have hj₁₂ : j₁ - j₂ = -(i * (lam₁ - lam₂)) := by
    linear_combination hline
  have hj₂₄ : j₂ - j₄ = (i + s₂) * (lam₁ - lam₂) := by
    linear_combination haux₂
  calc
    _ = -((i + s₁) * (lam₁ - lam₂) + (-(i * (lam₁ - lam₂))) +
        (i + s₂) * (lam₁ - lam₂)) := by ring
    _ = -((j₃ - j₁) + (j₁ - j₂) + (j₂ - j₄)) := by
      rw [hj₃₁, hj₁₂, hj₂₄]
    _ = -(j₃ - j₄) := by ring

lemma sqDist_primeCopy_of_same_remainders (p : ℕ) (hp : 0 < p) {d : ℕ}
    (hd : d ≠ 0) (s : LiftData d) (i₁ j₁ i₂ j₂ : Fin (p * d))
    (hi : remainderIndex p i₁ = remainderIndex p i₂)
    (hj : remainderIndex p j₁ = remainderIndex p j₂) :
    sqDist ((primeCopyLift p s).point i₁ j₁) ((primeCopyLift p s).point i₂ j₂) =
      sqDist (s.point (quotientIndex p i₁) (quotientIndex p j₁))
        (s.point (quotientIndex p i₂) (quotientIndex p j₂)) := by
  have hvi₁ := val_eq_mul_quotient_add_remainder p hp i₁
  have hvi₂ := val_eq_mul_quotient_add_remainder p hp i₂
  have hvj₁ := val_eq_mul_quotient_add_remainder p hp j₁
  have hvj₂ := val_eq_mul_quotient_add_remainder p hp j₂
  simp only [LiftData.point, primeCopyLift, liftedPoint, sqDist]
  push_cast
  field_simp [Nat.ne_of_gt hp, hd]
  rw [hvi₁, hvi₂, hvj₁, hvj₂, hi, hj]
  push_cast
  ring

lemma primeCopy_cross_not_integral (p : ℕ) (hp : 0 < p) (han : NormAnisotropic p)
    {d : ℕ} (hd : d ≠ 0) (s : LiftData d) (i₁ j₁ i₂ j₂ : Fin (p * d))
    (hrem : remainderIndex p i₁ ≠ remainderIndex p i₂ ∨
      remainderIndex p j₁ ≠ remainderIndex p j₂) :
    ¬∃ z : ℤ,
      sqDist ((primeCopyLift p s).point i₁ j₁) ((primeCopyLift p s).point i₂ j₂) = z := by
  intro hInt
  have hpd : p * d ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hp) hd
  have hdiv := (sqDist_liftedPoint_isInt_iff (p * d) hpd i₁ j₁ i₂ j₂
    ((primeCopyLift p s).k i₁ j₁) ((primeCopyLift p s).l i₁ j₁)
    ((primeCopyLift p s).k i₂ j₂) ((primeCopyLift p s).l i₂ j₂)).mp hInt
  rcases hdiv with ⟨z, hz⟩
  have hvi₁ := val_eq_mul_quotient_add_remainder p hp i₁
  have hvi₂ := val_eq_mul_quotient_add_remainder p hp i₂
  have hvj₁ := val_eq_mul_quotient_add_remainder p hp j₁
  have hvj₂ := val_eq_mul_quotient_add_remainder p hp j₂
  have hzp := congrArg (fun x : ℤ ↦ (x : ZMod p)) hz
  simp only [primeCopyLift, conflictNumerator] at hzp
  rw [hvi₁, hvi₂, hvj₁, hvj₂] at hzp
  push_cast at hzp
  have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
  simp only [hp0, zero_mul, mul_zero, zero_add, add_zero] at hzp
  ring_nf at hzp
  let xi₁ : ZMod p := remainderIndex p i₁
  let xi₂ : ZMod p := remainderIndex p i₂
  let xj₁ : ZMod p := remainderIndex p j₁
  let xj₂ : ZMod p := remainderIndex p j₂
  have hzp' : -(xi₁ * xi₂ * 2) + xi₁ ^ 2 + xi₂ ^ 2 - xj₁ * xj₂ * 2 +
      xj₁ ^ 2 + xj₂ ^ 2 = 0 := by
    simpa [xi₁, xi₂, xj₁, xj₂] using hzp
  have hnorm : (xi₁ - xi₂) ^ 2 + (xj₁ - xj₂) ^ 2 = 0 := by
    calc
      _ = -(xi₁ * xi₂ * 2) + xi₁ ^ 2 + xi₂ ^ 2 - xj₁ * xj₂ * 2 +
          xj₁ ^ 2 + xj₂ ^ 2 := by ring
      _ = 0 := hzp'
  rcases han (xi₁ - xi₂) (xj₁ - xj₂) hnorm with ⟨hi, hj⟩
  dsimp [xi₁, xi₂] at hi
  dsimp [xj₁, xj₂] at hj
  have hi' : remainderIndex p i₁ = remainderIndex p i₂ := by
    have hc := congrArg ZMod.val (sub_eq_zero.mp hi)
    simpa [ZMod.val_natCast_of_lt (remainderIndex_lt p hp i₁),
      ZMod.val_natCast_of_lt (remainderIndex_lt p hp i₂)] using hc
  have hj' : remainderIndex p j₁ = remainderIndex p j₂ := by
    have hc := congrArg ZMod.val (sub_eq_zero.mp hj)
    simpa [ZMod.val_natCast_of_lt (remainderIndex_lt p hp j₁),
      ZMod.val_natCast_of_lt (remainderIndex_lt p hp j₂)] using hc
  exact hrem.elim (fun h ↦ h hi') (fun h ↦ h hj')

/-- The explicit forward source construction for every anisotropic modulus;
in particular it applies to primes congruent to `3 mod 4`. -/
theorem primeCopy_separated (p : ℕ) (hp : 0 < p) (han : NormAnisotropic p)
    {d : ℕ} (hd : d ≠ 0) (s : LiftData d) (hs : s.Separated) :
    (primeCopyLift p s).Separated := by
  rw [LiftData.separated_iff_sqDist_not_int (Nat.mul_ne_zero (Nat.ne_of_gt hp) hd)]
  intro i₁ j₁ i₂ j₂ hne
  by_cases hi : remainderIndex p i₁ = remainderIndex p i₂
  · by_cases hj : remainderIndex p j₁ = remainderIndex p j₂
    · have hquot :
          (quotientIndex p i₁, quotientIndex p j₁) ≠
            (quotientIndex p i₂, quotientIndex p j₂) := by
        intro h
        apply hne
        apply Prod.ext <;> apply Fin.ext
        · have hq := congrArg (fun x : Fin d ↦ (x : ℕ)) (congrArg Prod.fst h)
          rw [val_eq_mul_quotient_add_remainder p hp i₁,
            val_eq_mul_quotient_add_remainder p hp i₂, hi, hq]
        · have hq := congrArg (fun x : Fin d ↦ (x : ℕ)) (congrArg Prod.snd h)
          rw [val_eq_mul_quotient_add_remainder p hp j₁,
            val_eq_mul_quotient_add_remainder p hp j₂, hj, hq]
      have hold := (LiftData.separated_iff_sqDist_not_int hd s).mp hs
        (quotientIndex p i₁) (quotientIndex p j₁)
        (quotientIndex p i₂) (quotientIndex p j₂) hquot
      rwa [sqDist_primeCopy_of_same_remainders p hp hd s i₁ j₁ i₂ j₂ hi hj]
    · exact primeCopy_cross_not_integral p hp han hd s i₁ j₁ i₂ j₂ (Or.inr hj)
  · exact primeCopy_cross_not_integral p hp han hd s i₁ j₁ i₂ j₂ (Or.inl hi)

/-- The source's complete trivial odd-prime step, with literal preservation
of every old lift. -/
theorem primeCopy_step_of_prime_mod_four_eq_three (p : ℕ) [Fact p.Prime]
    (hp3 : p % 4 = 3) {d : ℕ} (hd : d ≠ 0) (s : LiftData d) (hs : s.Separated) :
    ∃ t : LiftData (p * d),
      PrimeExtends p (Nat.Prime.pos (Fact.out : p.Prime)) s t ∧ t.Separated := by
  have hprime : p.Prime := Fact.out
  exact ⟨primeCopyLift p s, primeCopy_primeExtends p hprime.pos s,
    primeCopy_separated p hprime.pos
      (normAnisotropic_of_prime_mod_four_eq_three p hp3) hd s hs⟩

/-- The prime-power modulus which survives after cancelling the common
prime-power content of an input difference. -/
def survivingModulus (d a : ℕ) : ℕ :=
  d / Nat.gcd d a

/-- Absolute difference between the canonical representatives of two residues. -/
def indexDiff {d : ℕ} (i j : Fin d) : ℕ :=
  Int.natAbs (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))

/-- Goodness condition (4.3), expressed using the equivalent quotient by the
capped gcd rather than prime valuations. -/
def GoodPerm (d : ℕ) (π : Equiv.Perm (Fin d)) : Prop :=
  ∀ i j, i ≠ j →
    ¬(survivingModulus d (indexDiff i j) : ℤ) ∣
      (((π i : Fin d) : ℕ) : ℤ) - (((π j : Fin d) : ℕ) : ℤ)

/-- The same condition for a raw endomap.  The source constructs the line
maps by formulas first and obtains permutations from goodness afterwards. -/
def GoodMap (d : ℕ) (f : Fin d → Fin d) : Prop :=
  ∀ i j, i ≠ j →
    ¬(survivingModulus d (indexDiff i j) : ℤ) ∣
      (((f i : Fin d) : ℕ) : ℤ) - (((f j : Fin d) : ℕ) : ℤ)

lemma GoodMap.injective {d : ℕ} {f : Fin d → Fin d} (hf : GoodMap d f) :
    Function.Injective f := by
  intro i j hij
  by_contra hne
  exact hf i j hne (by simp [hij])

noncomputable def GoodMap.toPerm {d : ℕ} (f : Fin d → Fin d) (hf : GoodMap d f) :
    Equiv.Perm (Fin d) :=
  Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf.injective, rfl⟩)

lemma GoodMap.toPerm_apply {d : ℕ} (f : Fin d → Fin d) (hf : GoodMap d f)
    (i : Fin d) : GoodMap.toPerm f hf i = f i := rfl

lemma GoodMap.goodPerm_toPerm {d : ℕ} (f : Fin d → Fin d) (hf : GoodMap d f) :
    GoodPerm d (GoodMap.toPerm f hf) := by
  simpa only [GoodPerm, GoodMap, GoodMap.toPerm_apply] using hf

lemma survivingModulus_dvd (d a : ℕ) : survivingModulus d a ∣ d := by
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left d a)

/-- Richness in all congruence classes of all rational translates, as in (4.1).
The infinitude is stronger than the nonemptiness used by the finite forcing
lemma, and is what permits repeated choices along a denominator chain. -/
def Rich (P : Set RatPoint) : Prop :=
  ∀ (d : ℕ), d ≠ 0 → ∀ (i j : Fin d) (a b : ℤ),
    Set.Infinite {x : RatPoint | ∃ k l : ℤ,
      x = liftedPoint d i j k l ∧
      a ≡ k [ZMOD d] ∧ b ≡ l [ZMOD d] ∧ x ∈ P}

/-- At one finite denominator, richness forces any separated selector into the
pool while preserving all its congruence data. -/
theorem finiteSelector_in_rich_pool {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (P : Set RatPoint) (hP : Rich P) (hs : s.Separated) :
    ∃ t : LiftData d, t.Separated ∧ ∀ i j, t.point i j ∈ P := by
  have havail : ∀ i j, ∃ k l a b : ℤ,
      k = s.k i j + d * a ∧ l = s.l i j + d * b ∧ liftedPoint d i j k l ∈ P := by
    intro i j
    rcases (hP d hd i j (s.k i j) (s.l i j)).nonempty with ⟨x, hx⟩
    rcases hx with ⟨k, l, rfl, hk, hl, hp⟩
    rcases Int.modEq_iff_add_fac.mp hk with ⟨a, ha⟩
    rcases Int.modEq_iff_add_fac.mp hl with ⟨b, hb⟩
    exact ⟨k, l, a, b, ha, hb, hp⟩
  rcases s.choose_congruent_in_pool P havail with ⟨t, -, hmem, hsep⟩
  exact ⟨t, hsep hs, hmem⟩

/-- A set of rational points has the partial Steinhaus property in coordinates. -/
def IsPartial (T : Set RatPoint) : Prop :=
  ∀ ⦃x⦄, x ∈ T → ∀ ⦃y⦄, y ∈ T → x ≠ y → ¬∃ z : ℤ, sqDist x y = z

/-- Rational translation classes modulo the integer lattice. -/
abbrev RatResidue := AddCircle (1 : ℚ) × AddCircle (1 : ℚ)

def residue (x : RatPoint) : RatResidue :=
  ((x.1 : AddCircle (1 : ℚ)), (x.2 : AddCircle (1 : ℚ)))

def HitsEveryIntegerTranslate (T : Set RatPoint) : Prop :=
  ∀ x : RatPoint, ∃ y ∈ T, residue y = residue x

end

end Selector

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/Circle.lean` -/

section
/-!
# The three-circle / four-bar finiteness lemma

The coordinates are normalized as in Section 5 of the mathematical write-up.
The proof uses adjugate numerators and never divides by their determinant.
-/

namespace Circle

open Polynomial

noncomputable section

def normSq (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2

/-- The normalized system (5.4), including the unit direction equation. -/
def NormalizedSolution
    (A B C R S d u v : ℝ) (z : ℝ × ℝ × ℝ × ℝ) : Prop :=
  let x := z.1
  let y := z.2.1
  let X := z.2.2.1
  let Y := z.2.2.2
  x ^ 2 + y ^ 2 = 1 ∧
    X ^ 2 + Y ^ 2 = 1 ∧
    (x + d * X - A) ^ 2 + (y + d * Y) ^ 2 = R ^ 2 ∧
    (x + u * X - v * Y - B) ^ 2 +
      (y + v * X + u * Y - C) ^ 2 = S ^ 2

private def fCert (A B C d u v : ℝ) : ℝ :=
  A * B * d * v - 2 * A * B * u * v - A * C * d * u + A * C * u ^ 2 -
    A * C * v ^ 2 - B ^ 2 * d * v + 2 * B ^ 2 * u * v + 2 * B * C * d * u -
    2 * B * C * u ^ 2 + 2 * B * C * v ^ 2 + C ^ 2 * d * v - 2 * C ^ 2 * u * v

private def gCert (A B C d u v : ℝ) : ℝ :=
  -A * B * d * u + A * B * u ^ 2 - A * B * v ^ 2 - A * C * d * v +
    2 * A * C * u * v + B ^ 2 * d * u - B ^ 2 * u ^ 2 + B ^ 2 * v ^ 2 +
    2 * B * C * d * v - 4 * B * C * u * v - C ^ 2 * d * u + C ^ 2 * u ^ 2 -
    C ^ 2 * v ^ 2

private def hOne (A B C d u v : ℝ) : ℝ :=
  -A * B * v - A * C * d + 2 * A * C * u + B ^ 2 * v + 2 * B * C * d -
    4 * B * C * u - C ^ 2 * v

private def hTwo (A B C d u v : ℝ) : ℝ :=
  -A * B * d + 2 * A * B * u + A * C * v + B ^ 2 * d - 2 * B ^ 2 * u -
    2 * B * C * v - C ^ 2 * d + 2 * C ^ 2 * u

private lemma bezout_certificate (A B C d u v : ℝ) :
    hOne A B C d u v * fCert A B C d u v +
        hTwo A B C d u v * gCert A B C d u v =
      u * (B ^ 2 + C ^ 2) * (u - d) * (2 * u - d) * ((A - B) ^ 2 + C ^ 2) := by
  simp only [hOne, hTwo, fCert, gCert]
  ring

private def eOneZero (A B C d v : ℝ) : ℝ :=
  -A * B * d + A * C * v + B ^ 2 * d - 2 * B * C * v - C ^ 2 * d

private def eTwoZero (A B C d v : ℝ) : ℝ :=
  A * B * v + A * C * d - B ^ 2 * v - 2 * B * C * d + C ^ 2 * v

private lemma zero_case_sum_certificate (A B C d v : ℝ) :
    eOneZero A B C d v ^ 2 + eTwoZero A B C d v ^ 2 =
      (B ^ 2 + C ^ 2) * (d ^ 2 + v ^ 2) * ((A - B) ^ 2 + C ^ 2) := by
  simp only [eOneZero, eTwoZero]
  ring

private def eOneD (A B C d v : ℝ) : ℝ :=
  A * B * d + A * C * v - B ^ 2 * d - 2 * B * C * v + C ^ 2 * d

private def eTwoD (A B C d v : ℝ) : ℝ :=
  A * B * v - A * C * d - B ^ 2 * v + 2 * B * C * d + C ^ 2 * v

private lemma d_case_sum_certificate (A B C d v : ℝ) :
    eOneD A B C d v ^ 2 + eTwoD A B C d v ^ 2 =
      (B ^ 2 + C ^ 2) * (d ^ 2 + v ^ 2) * ((A - B) ^ 2 + C ^ 2) := by
  simp only [eOneD, eTwoD]
  ring

private lemma f_zero_case (A B C d v : ℝ) :
    fCert A B C d 0 v = -v * eOneZero A B C d v := by
  simp only [fCert, eOneZero]
  ring

private lemma g_zero_case (A B C d v : ℝ) :
    gCert A B C d 0 v = -v * eTwoZero A B C d v := by
  simp only [gCert, eTwoZero]
  ring

private lemma f_d_case (A B C d v : ℝ) :
    fCert A B C d d v = -v * eOneD A B C d v := by
  simp only [fCert, eOneD]
  ring

private lemma g_d_case (A B C d v : ℝ) :
    gCert A B C d d v = -v * eTwoD A B C d v := by
  simp only [gCert, eTwoD]
  ring

private lemma half_case_f (A B C d u v : ℝ) (h : 2 * u = d) :
    4 * fCert A B C d u v = -C * (A - 2 * B) * (d ^ 2 + 4 * v ^ 2) := by
  rw [← h]
  simp only [fCert]
  ring

private lemma half_case_g (A B C d u v : ℝ) (h : 2 * u = d) :
    4 * gCert A B C d u v =
      -(A * B - B ^ 2 + C ^ 2) * (d ^ 2 + 4 * v ^ 2) := by
  rw [← h]
  simp only [gCert]
  ring

/-- The standard rational parametrization of the unit circle, omitting
`(-1,0)`. -/
def circleParam (t : ℝ) : ℝ × ℝ :=
  ((1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2))

def circleSlope (p : ℝ × ℝ) : ℝ := p.2 / (1 + p.1)

@[simp]
lemma circleParam_mem (t : ℝ) : normSq (circleParam t) = 1 := by
  have hden : 1 + t ^ 2 ≠ 0 := by positivity
  simp only [normSq, circleParam]
  field_simp [hden]
  ring

lemma circleParam_circleSlope {p : ℝ × ℝ} (hunit : normSq p = 1)
    (hne : p ≠ (-1, 0)) : circleParam (circleSlope p) = p := by
  rcases p with ⟨x, y⟩
  have hxy : x ^ 2 + y ^ 2 = 1 := hunit
  have hx : 1 + x ≠ 0 := by
    intro hx
    have hxeq : x = -1 := by linarith
    have hyeq : y = 0 := by nlinarith
    exact hne (by simp [hxeq, hyeq])
  have ht : 1 + (y / (1 + x)) ^ 2 ≠ 0 := by positivity
  ext <;> simp only [circleParam, circleSlope, Prod.fst, Prod.snd]
  · field_simp [hx, ht]
    nlinarith
  · field_simp [hx, ht]
    have hy := congrArg (fun z : ℝ ↦ 2 * y * z) hxy
    nlinarith [hy]

lemma circleSlope_injOn :
    Set.InjOn circleSlope {p : ℝ × ℝ | normSq p = 1 ∧ p ≠ (-1, 0)} := by
  intro p hp q hq hpq
  rw [← circleParam_circleSlope hp.1 hp.2, ← circleParam_circleSlope hq.1 hq.2, hpq]

/-! ## The determinant-free eliminant -/

private def alphaOne (A d X : ℝ) : ℝ := 2 * (d * X - A)
private def betaOne (d Y : ℝ) : ℝ := 2 * d * Y
private def gammaOne (A R d X : ℝ) : ℝ :=
  d ^ 2 + A ^ 2 + 1 - R ^ 2 - 2 * A * d * X

private def qx (u v X Y : ℝ) : ℝ := u * X - v * Y
private def qy (u v X Y : ℝ) : ℝ := v * X + u * Y
private def alphaTwo (B u v X Y : ℝ) : ℝ := 2 * (qx u v X Y - B)
private def betaTwo (C u v X Y : ℝ) : ℝ := 2 * (qy u v X Y - C)
private def gammaTwo (B C S u v X Y : ℝ) : ℝ :=
  u ^ 2 + v ^ 2 + B ^ 2 + C ^ 2 + 1 - S ^ 2 -
    2 * B * qx u v X Y - 2 * C * qy u v X Y

private def delta (A B C d u v X Y : ℝ) : ℝ :=
  alphaOne A d X * betaTwo C u v X Y - alphaTwo B u v X Y * betaOne d Y
private def numX (A B C R S d u v X Y : ℝ) : ℝ :=
  betaOne d Y * gammaTwo B C S u v X Y -
    betaTwo C u v X Y * gammaOne A R d X
private def numY (A B C R S d u v X Y : ℝ) : ℝ :=
  alphaTwo B u v X Y * gammaOne A R d X -
    alphaOne A d X * gammaTwo B C S u v X Y

/-- Equation (5.5a), with no division by `delta`. -/
def eliminant (A B C R S d u v X Y : ℝ) : ℝ :=
  (numX A B C R S d u v X Y ^ 2 + numY A B C R S d u v X Y ^ 2 -
    delta A B C d u v X Y ^ 2) / 4

/-- The denominator-cleared eliminant after substituting the rational
parametrization of the unit circle. -/
private def pDen : Polynomial ℝ := 1 + X ^ 2
private def pXN : Polynomial ℝ := 1 - X ^ 2
private def pYN : Polynomial ℝ := 2 * X
private def pA1 (A d : ℝ) : Polynomial ℝ :=
  2 * (Polynomial.C d * pXN - Polynomial.C A * pDen)
private def pB1 (d : ℝ) : Polynomial ℝ := 2 * Polynomial.C d * pYN
private def pG1 (A R d : ℝ) : Polynomial ℝ :=
  Polynomial.C (d ^ 2 + A ^ 2 + 1 - R ^ 2) * pDen -
    2 * Polynomial.C (A * d) * pXN
private def pQX (u v : ℝ) : Polynomial ℝ :=
  Polynomial.C u * pXN - Polynomial.C v * pYN
private def pQY (u v : ℝ) : Polynomial ℝ :=
  Polynomial.C v * pXN + Polynomial.C u * pYN
private def pA2 (B u v : ℝ) : Polynomial ℝ :=
  2 * (pQX u v - Polynomial.C B * pDen)
private def pB2 (C u v : ℝ) : Polynomial ℝ :=
  2 * (pQY u v - Polynomial.C C * pDen)
private def pG2 (B C S u v : ℝ) : Polynomial ℝ :=
  Polynomial.C (u ^ 2 + v ^ 2 + B ^ 2 + C ^ 2 + 1 - S ^ 2) * pDen -
    2 * Polynomial.C B * pQX u v - 2 * Polynomial.C C * pQY u v
private def pDelta (A B C d u v : ℝ) : Polynomial ℝ :=
  pA1 A d * pB2 C u v - pA2 B u v * pB1 d
private def pNumX (A B C R S d u v : ℝ) : Polynomial ℝ :=
  pB1 d * pG2 B C S u v - pB2 C u v * pG1 A R d
private def pNumY (A B C R S d u v : ℝ) : Polynomial ℝ :=
  pA2 B u v * pG1 A R d - pA1 A d * pG2 B C S u v

private def parameterElimPoly (A B C R S d u v : ℝ) : Polynomial ℝ :=
  pNumX A B C R S d u v ^ 2 + pNumY A B C R S d u v ^ 2 -
    pDelta A B C d u v ^ 2

private lemma pDen_eval (t : ℝ) : pDen.eval t = 1 + t ^ 2 := by simp [pDen]
private lemma pA1_eval (A d t : ℝ) :
    (pA1 A d).eval t = (1 + t ^ 2) * alphaOne A d (circleParam t).1 := by
  have h : 1 + t ^ 2 ≠ 0 := by positivity
  simp [pA1, pXN, pDen, circleParam, alphaOne]
  field_simp [h]
private lemma pB1_eval (d t : ℝ) :
    (pB1 d).eval t = (1 + t ^ 2) * betaOne d (circleParam t).2 := by
  have h : 1 + t ^ 2 ≠ 0 := by positivity
  simp [pB1, pYN, circleParam, betaOne]
  field_simp [h]
private lemma pQX_eval (u v t : ℝ) :
    (pQX u v).eval t = (1 + t ^ 2) * qx u v (circleParam t).1 (circleParam t).2 := by
  have h : 1 + t ^ 2 ≠ 0 := by positivity
  simp [pQX, pXN, pYN, circleParam, qx]
  field_simp [h]
private lemma pQY_eval (u v t : ℝ) :
    (pQY u v).eval t = (1 + t ^ 2) * qy u v (circleParam t).1 (circleParam t).2 := by
  have h : 1 + t ^ 2 ≠ 0 := by positivity
  simp [pQY, pXN, pYN, circleParam, qy]
  field_simp [h]
private lemma pG1_eval (A R d t : ℝ) :
    (pG1 A R d).eval t = (1 + t ^ 2) * gammaOne A R d (circleParam t).1 := by
  have h : 1 + t ^ 2 ≠ 0 := by positivity
  simp [pG1, pDen, pXN, circleParam, gammaOne]
  field_simp [h]
private lemma pA2_eval (B u v t : ℝ) :
    (pA2 B u v).eval t =
      (1 + t ^ 2) * alphaTwo B u v (circleParam t).1 (circleParam t).2 := by
  simp only [pA2, eval_mul, eval_sub, pQX_eval, eval_ofNat, eval_C, pDen_eval,
    alphaTwo]
  ring
private lemma pB2_eval (C u v t : ℝ) :
    (pB2 C u v).eval t =
      (1 + t ^ 2) * betaTwo C u v (circleParam t).1 (circleParam t).2 := by
  simp only [pB2, eval_mul, eval_sub, pQY_eval, eval_ofNat, eval_C, pDen_eval,
    betaTwo]
  ring
private lemma pG2_eval (B C S u v t : ℝ) :
    (pG2 B C S u v).eval t =
      (1 + t ^ 2) * gammaTwo B C S u v (circleParam t).1 (circleParam t).2 := by
  simp only [pG2, eval_sub, eval_mul, eval_C, eval_ofNat, pDen_eval, pQX_eval,
    pQY_eval, gammaTwo]
  ring
private lemma pDelta_eval (A B C d u v t : ℝ) :
    (pDelta A B C d u v).eval t =
      (1 + t ^ 2) ^ 2 * delta A B C d u v (circleParam t).1 (circleParam t).2 := by
  rw [pDelta, eval_sub, eval_mul, eval_mul, pA1_eval, pB2_eval, pA2_eval, pB1_eval]
  simp only [delta]
  ring
private lemma pNumX_eval (A B C R S d u v t : ℝ) :
    (pNumX A B C R S d u v).eval t =
      (1 + t ^ 2) ^ 2 * numX A B C R S d u v (circleParam t).1 (circleParam t).2 := by
  rw [pNumX, eval_sub, eval_mul, eval_mul, pB1_eval, pG2_eval, pB2_eval, pG1_eval]
  simp only [numX]
  ring
private lemma pNumY_eval (A B C R S d u v t : ℝ) :
    (pNumY A B C R S d u v).eval t =
      (1 + t ^ 2) ^ 2 * numY A B C R S d u v (circleParam t).1 (circleParam t).2 := by
  rw [pNumY, eval_sub, eval_mul, eval_mul, pA2_eval, pG1_eval, pA1_eval, pG2_eval]
  simp only [numY]
  ring

private lemma parameterElimPoly_eval (A B C R S d u v t : ℝ) :
    (parameterElimPoly A B C R S d u v).eval t =
      4 * (1 + t ^ 2) ^ 4 *
        eliminant A B C R S d u v (circleParam t).1 (circleParam t).2 := by
  have hden : 1 + t ^ 2 ≠ 0 := by positivity
  rw [parameterElimPoly, eval_sub, eval_add, eval_pow, eval_pow, eval_pow,
    pNumX_eval, pNumY_eval, pDelta_eval]
  simp only [eliminant]
  field_simp

private def oddCoeffFunctional (p : Polynomial ℝ) : ℝ :=
  3 * p.coeff 1 + p.coeff 5 - 2 * p.coeff 3

private def evenCoeffFunctional (p : Polynomial ℝ) : ℝ :=
  4 * p.coeff 0 - 3 * p.coeff 2 + 2 * p.coeff 4 - p.coeff 6

private lemma oddCoeffFunctional_add (p q : Polynomial ℝ) :
    oddCoeffFunctional (p + q) = oddCoeffFunctional p + oddCoeffFunctional q := by
  simp only [oddCoeffFunctional, coeff_add]
  ring

private lemma oddCoeffFunctional_sub (p q : Polynomial ℝ) :
    oddCoeffFunctional (p - q) = oddCoeffFunctional p - oddCoeffFunctional q := by
  simp only [oddCoeffFunctional, coeff_sub]
  ring

private lemma evenCoeffFunctional_add (p q : Polynomial ℝ) :
    evenCoeffFunctional (p + q) = evenCoeffFunctional p + evenCoeffFunctional q := by
  simp only [evenCoeffFunctional, coeff_add]
  ring

private lemma evenCoeffFunctional_sub (p q : Polynomial ℝ) :
    evenCoeffFunctional (p - q) = evenCoeffFunctional p - evenCoeffFunctional q := by
  simp only [evenCoeffFunctional, coeff_sub]
  ring

private lemma oddCoeffFunctional_sq (p : Polynomial ℝ) :
    oddCoeffFunctional (p ^ 2) =
      6 * p.coeff 0 * p.coeff 1 + 2 * p.coeff 0 * p.coeff 5 +
      2 * p.coeff 1 * p.coeff 4 + 2 * p.coeff 2 * p.coeff 3 -
      4 * p.coeff 0 * p.coeff 3 - 4 * p.coeff 1 * p.coeff 2 := by
  simp only [oddCoeffFunctional, pow_two, coeff_mul]
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  ring

private lemma evenCoeffFunctional_sq (p : Polynomial ℝ) :
    evenCoeffFunctional (p ^ 2) =
      4 * p.coeff 0 ^ 2 - 6 * p.coeff 0 * p.coeff 2 - 3 * p.coeff 1 ^ 2 +
      4 * p.coeff 0 * p.coeff 4 + 4 * p.coeff 1 * p.coeff 3 +
      2 * p.coeff 2 ^ 2 - 2 * p.coeff 0 * p.coeff 6 -
      2 * p.coeff 1 * p.coeff 5 - 2 * p.coeff 2 * p.coeff 4 - p.coeff 3 ^ 2 := by
  simp only [evenCoeffFunctional, pow_two, coeff_mul]
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  ring

private def quadPoly (a b c : ℝ) : Polynomial ℝ :=
  Polynomial.C a + Polynomial.C b * X + Polynomial.C c * X ^ 2

private def quarticPoly (a b c d e : ℝ) : Polynomial ℝ :=
  Polynomial.C a + Polynomial.C b * X + Polynomial.C c * X ^ 2 +
    Polynomial.C d * X ^ 3 + Polynomial.C e * X ^ 4

private lemma quadPoly_mul (a b c d e f : ℝ) :
    quadPoly a b c * quadPoly d e f =
      quarticPoly (a * d) (a * e + b * d) (a * f + b * e + c * d)
        (b * f + c * e) (c * f) := by
  simp only [quadPoly, quarticPoly]
  norm_num [map_add, map_mul, Polynomial.C_ofNat]
  ring

@[simp] private lemma quarticPoly_coeff_zero (a b c d e : ℝ) :
    (quarticPoly a b c d e).coeff 0 = a := by simp [quarticPoly]
@[simp] private lemma quarticPoly_coeff_one (a b c d e : ℝ) :
    (quarticPoly a b c d e).coeff 1 = b := by simp [quarticPoly]
@[simp] private lemma quarticPoly_coeff_two (a b c d e : ℝ) :
    (quarticPoly a b c d e).coeff 2 = c := by simp [quarticPoly]
@[simp] private lemma quarticPoly_coeff_three (a b c d e : ℝ) :
    (quarticPoly a b c d e).coeff 3 = d := by simp [quarticPoly]
@[simp] private lemma quarticPoly_coeff_four (a b c d e : ℝ) :
    (quarticPoly a b c d e).coeff 4 = e := by simp [quarticPoly]
@[simp] private lemma quarticPoly_coeff_five (a b c d e : ℝ) :
    (quarticPoly a b c d e).coeff 5 = 0 := by simp [quarticPoly]
@[simp] private lemma quarticPoly_coeff_six (a b c d e : ℝ) :
    (quarticPoly a b c d e).coeff 6 = 0 := by simp [quarticPoly]

private lemma pA1_quad (A d : ℝ) :
    pA1 A d = quadPoly (2 * (d - A)) 0 (-2 * (d + A)) := by
  simp only [pA1, pXN, pDen, quadPoly]
  norm_num [map_add, map_sub, map_mul, map_neg]
  simp only [Polynomial.C_ofNat]
  ring
private lemma pB1_quad (d : ℝ) : pB1 d = quadPoly 0 (4 * d) 0 := by
  simp only [pB1, pYN, quadPoly]
  norm_num [map_add, map_sub, map_mul, map_neg]
  simp only [Polynomial.C_ofNat]
  ring
private lemma pG1_quad (A R d : ℝ) :
    pG1 A R d =
      quadPoly (d ^ 2 + A ^ 2 + 1 - R ^ 2 - 2 * A * d) 0
        (d ^ 2 + A ^ 2 + 1 - R ^ 2 + 2 * A * d) := by
  simp only [pG1, pDen, pXN, quadPoly]
  norm_num [map_add, map_sub, map_mul, map_neg]
  simp only [Polynomial.C_ofNat]
  ring
private lemma pA2_quad (B u v : ℝ) :
    pA2 B u v = quadPoly (2 * (u - B)) (-4 * v) (-2 * (u + B)) := by
  simp only [pA2, pQX, pXN, pYN, pDen, quadPoly]
  norm_num [map_add, map_sub, map_mul, map_neg]
  simp only [Polynomial.C_ofNat]
  ring
private lemma pB2_quad (C u v : ℝ) :
    pB2 C u v = quadPoly (2 * (v - C)) (4 * u) (-2 * (v + C)) := by
  simp only [pB2, pQY, pXN, pYN, pDen, quadPoly]
  norm_num [map_add, map_sub, map_mul, map_neg]
  simp only [Polynomial.C_ofNat]
  ring
private lemma pG2_quad (B C S u v : ℝ) :
    pG2 B C S u v =
      quadPoly
        (u ^ 2 + v ^ 2 + B ^ 2 + C ^ 2 + 1 - S ^ 2 - 2 * B * u - 2 * C * v)
        (4 * B * v - 4 * C * u)
        (u ^ 2 + v ^ 2 + B ^ 2 + C ^ 2 + 1 - S ^ 2 + 2 * B * u + 2 * C * v) := by
  simp only [pG2, pQX, pQY, pDen, pXN, pYN, quadPoly]
  norm_num [map_add, map_sub, map_mul, map_neg]
  simp only [Polynomial.C_ofNat]
  ring

private lemma parameterElimPoly_odd_certificate (A B C R S d u v : ℝ) :
    oddCoeffFunctional (parameterElimPoly A B C R S d u v) =
      256 * A * d * fCert A B C d u v := by
  rw [parameterElimPoly, oddCoeffFunctional_sub, oddCoeffFunctional_add,
    oddCoeffFunctional_sq, oddCoeffFunctional_sq, oddCoeffFunctional_sq]
  simp only [pNumX, pNumY, pDelta]
  rw [pB1_quad, pG2_quad, pB2_quad, pG1_quad, pA2_quad, pA1_quad]
  repeat' rw [quadPoly_mul]
  simp only [coeff_add, coeff_sub, quarticPoly_coeff_zero, quarticPoly_coeff_one,
    quarticPoly_coeff_two, quarticPoly_coeff_three, quarticPoly_coeff_four,
    quarticPoly_coeff_five, fCert]
  ring

private lemma parameterElimPoly_even_certificate (A B C R S d u v : ℝ) :
    evenCoeffFunctional (parameterElimPoly A B C R S d u v) =
      256 * A * d * gCert A B C d u v := by
  rw [parameterElimPoly, evenCoeffFunctional_sub, evenCoeffFunctional_add,
    evenCoeffFunctional_sq, evenCoeffFunctional_sq, evenCoeffFunctional_sq]
  simp only [pNumX, pNumY, pDelta]
  rw [pB1_quad, pG2_quad, pB2_quad, pG1_quad, pA2_quad, pA1_quad]
  repeat' rw [quadPoly_mul]
  simp only [coeff_add, coeff_sub, quarticPoly_coeff_zero, quarticPoly_coeff_one,
    quarticPoly_coeff_two, quarticPoly_coeff_three, quarticPoly_coeff_four,
    quarticPoly_coeff_five, quarticPoly_coeff_six, gCert]
  ring

private lemma certs_not_both_zero
    {A B C d u v : ℝ} (hd : 0 < d)
    (hc13 : 0 < B ^ 2 + C ^ 2) (hc23 : 0 < (A - B) ^ 2 + C ^ 2)
    (ht13 : 0 < u ^ 2 + v ^ 2) (ht23 : 0 < (u - d) ^ 2 + v ^ 2) :
    fCert A B C d u v ≠ 0 ∨ gCert A B C d u v ≠ 0 := by
  by_contra h
  push_neg at h
  rcases h with ⟨hF, hG⟩
  have hb := bezout_certificate A B C d u v
  rw [hF, hG] at hb
  simp only [mul_zero, zero_mul, add_zero] at hb
  have hbc : B ^ 2 + C ^ 2 ≠ 0 := ne_of_gt hc13
  have hac : (A - B) ^ 2 + C ^ 2 ≠ 0 := ne_of_gt hc23
  have hprod : u * (u - d) * (2 * u - d) = 0 := by
    have hz : u * (B ^ 2 + C ^ 2) * (u - d) * (2 * u - d) = 0 :=
      (mul_eq_zero.mp hb.symm).resolve_right hac
    rcases mul_eq_zero.mp hz with hz | hz
    · rcases mul_eq_zero.mp hz with hz | hud
      · have hu : u = 0 := (mul_eq_zero.mp hz).resolve_right hbc
        simp [hu]
      · simp [hud]
    · simp [hz]
  rcases mul_eq_zero.mp hprod with huud | hhalf
  · rcases mul_eq_zero.mp huud with hu | hud
    · have hv : v ≠ 0 := by
        intro hv
        rw [hu, hv] at ht13
        norm_num at ht13
      have hF0 : fCert A B C d 0 v = 0 := by simpa [hu] using hF
      have hG0 : gCert A B C d 0 v = 0 := by simpa [hu] using hG
      have he1 : eOneZero A B C d v = 0 := by
        have hh := f_zero_case A B C d v
        rw [hF0] at hh
        exact (mul_eq_zero.mp hh.symm).resolve_left (neg_ne_zero.mpr hv)
      have he2 : eTwoZero A B C d v = 0 := by
        have hh := g_zero_case A B C d v
        rw [hG0] at hh
        exact (mul_eq_zero.mp hh.symm).resolve_left (neg_ne_zero.mpr hv)
      have hs := zero_case_sum_certificate A B C d v
      rw [he1, he2] at hs
      norm_num at hs
      have hdv : 0 < d ^ 2 + v ^ 2 := by positivity
      rcases hs with (h | h) | h
      · exact hbc h
      · exact (ne_of_gt hdv) h
      · exact hac h
    · have hu : u = d := sub_eq_zero.mp hud
      have hv : v ≠ 0 := by
        intro hv
        rw [hu, hv] at ht23
        norm_num at ht23
      have hFd : fCert A B C d d v = 0 := by simpa [hu] using hF
      have hGd : gCert A B C d d v = 0 := by simpa [hu] using hG
      have he1 : eOneD A B C d v = 0 := by
        have hh := f_d_case A B C d v
        rw [hFd] at hh
        exact (mul_eq_zero.mp hh.symm).resolve_left (neg_ne_zero.mpr hv)
      have he2 : eTwoD A B C d v = 0 := by
        have hh := g_d_case A B C d v
        rw [hGd] at hh
        exact (mul_eq_zero.mp hh.symm).resolve_left (neg_ne_zero.mpr hv)
      have hs := d_case_sum_certificate A B C d v
      rw [he1, he2] at hs
      norm_num at hs
      have hdv : 0 < d ^ 2 + v ^ 2 := by positivity
      rcases hs with (h | h) | h
      · exact hbc h
      · exact (ne_of_gt hdv) h
      · exact hac h
  · have hhalf' : 2 * u = d := sub_eq_zero.mp hhalf
    have hfac : d ^ 2 + 4 * v ^ 2 ≠ 0 := by positivity
    have hf := half_case_f A B C d u v hhalf'
    have hg := half_case_g A B C d u v hhalf'
    rw [hF] at hf
    rw [hG] at hg
    have hcf : C * (A - 2 * B) = 0 := by
      have hz : (-C * (A - 2 * B)) * (d ^ 2 + 4 * v ^ 2) = 0 := by
        simpa using hf.symm
      have := (mul_eq_zero.mp hz).resolve_right hfac
      simpa only [neg_mul, neg_eq_zero] using this
    have habc : A * B - B ^ 2 + C ^ 2 = 0 := by
      have hz : (-(A * B - B ^ 2 + C ^ 2)) * (d ^ 2 + 4 * v ^ 2) = 0 := by
        simpa using hg.symm
      exact neg_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hfac)
    rcases mul_eq_zero.mp hcf with hC | hAB
    · rw [hC] at hc13 hc23 habc
      norm_num at hc13 hc23 habc
      have hB : B ≠ 0 := by nlinarith
      have hAmB : A - B ≠ 0 := by nlinarith
      exact hAmB ((mul_eq_zero.mp (by nlinarith [habc] : B * (A - B) = 0)).resolve_left hB)
    · have hA2B : A = 2 * B := sub_eq_zero.mp hAB
      rw [hA2B] at habc
      nlinarith

private lemma normalizedSolution_eliminant
    {A B C R S d u v x y X Y : ℝ}
    (hz : NormalizedSolution A B C R S d u v (x, y, X, Y)) :
    eliminant A B C R S d u v X Y = 0 := by
  rcases hz with ⟨hxy, hXY, h2, h3⟩
  have hl1 : alphaOne A d X * x + betaOne d Y * y + gammaOne A R d X = 0 := by
    simp only [alphaOne, betaOne, gammaOne]
    nlinarith
  have hl2 : alphaTwo B u v X Y * x + betaTwo C u v X Y * y +
      gammaTwo B C S u v X Y = 0 := by
    simp only [alphaTwo, betaTwo, gammaTwo, qx, qy]
    nlinarith
  have hx : delta A B C d u v X Y * x = numX A B C R S d u v X Y := by
    simp only [delta, numX]
    linear_combination betaTwo C u v X Y * hl1 - betaOne d Y * hl2
  have hy : delta A B C d u v X Y * y = numY A B C R S d u v X Y := by
    simp only [delta, numY]
    linear_combination alphaOne A d X * hl2 - alphaTwo B u v X Y * hl1
  rw [eliminant, ← hx, ← hy]
  have :
      ((delta A B C d u v X Y * x) ^ 2 + (delta A B C d u v X Y * y) ^ 2 -
          delta A B C d u v X Y ^ 2) / 4 =
        delta A B C d u v X Y ^ 2 * (x ^ 2 + y ^ 2 - 1) / 4 := by ring
  rw [this, hxy]
  ring

private def solutionDirections (A B C R S d u v : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ x y, NormalizedSolution A B C R S d u v (x, y, p.1, p.2)}

private lemma solutionDirections_finite
    {A B C R S d u v : ℝ} (hA : 0 < A) (hd : 0 < d)
    (hc13 : 0 < B ^ 2 + C ^ 2) (hc23 : 0 < (A - B) ^ 2 + C ^ 2)
    (ht13 : 0 < u ^ 2 + v ^ 2) (ht23 : 0 < (u - d) ^ 2 + v ^ 2) :
    (solutionDirections A B C R S d u v).Finite := by
  by_contra hfin
  have hinf : (solutionDirections A B C R S d u v).Infinite := hfin
  let D' := solutionDirections A B C R S d u v \ {(-1, 0)}
  have hD'inf : D'.Infinite := hinf.sdiff (Set.finite_singleton (-1, 0))
  have hunit : ∀ p ∈ D', normSq p = 1 := by
    rintro p ⟨⟨x, y, hsol⟩, -⟩
    exact hsol.2.1
  have hinj : Set.InjOn circleSlope D' := by
    apply circleSlope_injOn.mono
    intro p hp
    exact ⟨hunit p hp, hp.2⟩
  have himage : (circleSlope '' D').Infinite := hD'inf.image hinj
  have hroots : Set.Infinite {t : ℝ |
      (parameterElimPoly A B C R S d u v).IsRoot t} := by
    apply himage.mono
    rintro t ⟨p, hp, rfl⟩
    rcases hp.1 with ⟨x, y, hsol⟩
    have helim := normalizedSolution_eliminant hsol
    have heval := parameterElimPoly_eval A B C R S d u v (circleSlope p)
    rw [circleParam_circleSlope hsol.2.1 hp.2, helim, mul_zero] at heval
    change (parameterElimPoly A B C R S d u v).IsRoot (circleSlope p)
    simpa only [Polynomial.IsRoot] using heval
  have hpzero : parameterElimPoly A B C R S d u v = 0 :=
    (parameterElimPoly A B C R S d u v).eq_zero_of_infinite_isRoot hroots
  have hodd := parameterElimPoly_odd_certificate A B C R S d u v
  have heven := parameterElimPoly_even_certificate A B C R S d u v
  rw [hpzero] at hodd heven
  simp only [oddCoeffFunctional, evenCoeffFunctional, coeff_zero, mul_zero, add_zero,
    sub_zero, zero_mul] at hodd heven
  have hscale : 256 * A * d ≠ 0 := by positivity
  have hF : fCert A B C d u v = 0 := by
    exact (mul_eq_zero.mp (by simpa [mul_assoc] using hodd.symm)).resolve_left hscale
  have hG : gCert A B C d u v = 0 := by
    exact (mul_eq_zero.mp (by simpa [mul_assoc] using heven.symm)).resolve_left hscale
  rcases certs_not_both_zero hd hc13 hc23 ht13 ht23 with hF' | hG'
  · exact hF' hF
  · exact hG' hG

private def linePolyY (a b k : ℝ) : Polynomial ℝ :=
  (Polynomial.C k - Polynomial.C b * X) ^ 2 +
    Polynomial.C (a ^ 2) * X ^ 2 - Polynomial.C (a ^ 2)

private def linePolyX (a b k : ℝ) : Polynomial ℝ :=
  (Polynomial.C k - Polynomial.C a * X) ^ 2 +
    Polynomial.C (b ^ 2) * X ^ 2 - Polynomial.C (b ^ 2)

private lemma linePolyY_ne_zero {a b k : ℝ} (ha : a ≠ 0) : linePolyY a b k ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial ℝ ↦ p.coeff 2) h
  norm_num [linePolyY, pow_two, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    coeff_X] at hc
  nlinarith [sq_pos_of_ne_zero ha]

private lemma linePolyX_ne_zero {a b k : ℝ} (hb : b ≠ 0) : linePolyX a b k ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial ℝ ↦ p.coeff 2) h
  norm_num [linePolyX, pow_two, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    coeff_X] at hc
  nlinarith [sq_pos_of_ne_zero hb]

private lemma finite_unitCircle_line {a b k : ℝ} (hab : a ≠ 0 ∨ b ≠ 0) :
    Set.Finite {p : ℝ × ℝ | normSq p = 1 ∧ a * p.1 + b * p.2 = k} := by
  rcases hab with ha | hb
  · have hroots : Set.Finite {y : ℝ | (linePolyY a b k).IsRoot y} :=
      Polynomial.finite_setOfPred_isRoot (linePolyY_ne_zero ha)
    apply (hroots.image (fun y ↦ ((k - b * y) / a, y))).subset
    rintro ⟨x, y⟩ ⟨hunit, hline⟩
    have hx : k - b * y = a * x := by linarith
    refine ⟨y, ?_, ?_⟩
    · change (linePolyY a b k).eval y = 0
      simp only [linePolyY, eval_sub, eval_add, eval_pow, eval_mul, eval_C, eval_X]
      rw [hx]
      simp only [normSq, Prod.fst, Prod.snd] at hunit
      nlinarith
    · ext <;> simp only [Prod.fst, Prod.snd]
      field_simp [ha]
      linarith
  · have hroots : Set.Finite {x : ℝ | (linePolyX a b k).IsRoot x} :=
      Polynomial.finite_setOfPred_isRoot (linePolyX_ne_zero hb)
    apply (hroots.image (fun x ↦ (x, (k - a * x) / b))).subset
    rintro ⟨x, y⟩ ⟨hunit, hline⟩
    have hy : k - a * x = b * y := by linarith
    refine ⟨x, ?_, ?_⟩
    · change (linePolyX a b k).eval x = 0
      simp only [linePolyX, eval_sub, eval_add, eval_pow, eval_mul, eval_C, eval_X]
      rw [hy]
      simp only [normSq, Prod.fst, Prod.snd] at hunit
      nlinarith
    · ext <;> simp only [Prod.fst, Prod.snd]
      field_simp [hb]
      linarith

private lemma finite_two_circles {a b r2 : ℝ}
    (hneq : a ≠ 0 ∨ b ≠ 0 ∨ r2 ≠ 1) :
    Set.Finite {p : ℝ × ℝ |
      normSq p = 1 ∧ (p.1 - a) ^ 2 + (p.2 - b) ^ 2 = r2} := by
  by_cases hab : a ≠ 0 ∨ b ≠ 0
  · apply (finite_unitCircle_line
      (a := a) (b := b) (k := (1 + a ^ 2 + b ^ 2 - r2) / 2) hab).subset
    rintro ⟨x, y⟩ ⟨hunit, hcircle⟩
    refine ⟨hunit, ?_⟩
    simp only [normSq, Prod.fst, Prod.snd] at hunit
    nlinarith
  · have ha : a = 0 := not_ne_iff.mp (not_or.mp hab).1
    have hb : b = 0 := not_ne_iff.mp (not_or.mp hab).2
    have hr : r2 ≠ 1 := by
      rcases hneq with ha' | hb' | hr
      · exact (ha' ha).elim
      · exact (hb' hb).elim
      · exact hr
    apply Set.finite_empty.subset
    rintro ⟨x, y⟩ ⟨hunit, hcircle⟩
    simp only [ha, hb, sub_zero, normSq, Prod.fst, Prod.snd] at hunit hcircle
    exact hr (by nlinarith)

private def solutionFiber (A B C R S d u v X Y : ℝ) : Set (ℝ × ℝ) :=
  {p | NormalizedSolution A B C R S d u v (p.1, p.2, X, Y)}

private lemma solutionFiber_finite
    {A B C R S d u v X Y : ℝ} (hA : 0 < A) (hd : 0 < d)
    (hunit : X ^ 2 + Y ^ 2 = 1)
    (hnot : ¬ (A = d ∧ B = u ∧ C = v ∧ R ^ 2 = 1 ∧ S ^ 2 = 1)) :
    (solutionFiber A B C R S d u v X Y).Finite := by
  by_cases hsecond : A - d * X ≠ 0 ∨ -d * Y ≠ 0 ∨ R ^ 2 ≠ 1
  · apply (finite_two_circles hsecond).subset
    rintro ⟨x, y⟩ hsol
    rcases hsol with ⟨hxy, hXY, h2, h3⟩
    refine ⟨hxy, ?_⟩
    nlinarith
  · push Not at hsecond
    rcases hsecond with ⟨ha, hy, hR⟩
    by_cases hthird : B - qx u v X Y ≠ 0 ∨ C - qy u v X Y ≠ 0 ∨ S ^ 2 ≠ 1
    · apply (finite_two_circles hthird).subset
      rintro ⟨x, y⟩ hsol
      rcases hsol with ⟨hxy, hXY, h2, h3⟩
      refine ⟨hxy, ?_⟩
      simp only [qx, qy] at hthird ⊢
      nlinarith
    · push Not at hthird
      rcases hthird with ⟨hB, hC, hS⟩
      have hY : Y = 0 := by
        have hd0 : d ≠ 0 := ne_of_gt hd
        have hdy : d * Y = 0 := by nlinarith
        exact (mul_eq_zero.mp hdy).resolve_left hd0
      have hXsq : X ^ 2 = 1 := by nlinarith
      have hXeq : X = A / d := by
        apply (eq_div_iff (ne_of_gt hd)).2
        nlinarith
      have hXpos : 0 < X := by rw [hXeq]; positivity
      have hX : X = 1 := by nlinarith
      have hAd : A = d := by nlinarith
      have hBu : B = u := by
        simp only [qx, hX, hY, mul_one, mul_zero, sub_zero, add_zero] at hB
        linarith
      have hCv : C = v := by
        simp only [qy, hX, hY, mul_one, mul_zero, add_zero] at hC
        linarith
      exact (hnot ⟨hAd, hBu, hCv, hR, hS⟩).elim

/-- Normalized three-circle rigidity, algebraic orientation.  The hypotheses
say that the three fixed centers and the three target vertices are pairwise
distinct.  The sole flexible case is the equal-radius congruent placement. -/
theorem circle_congruent_finite
    {A B C R S d u v : ℝ} (hA : 0 < A) (hd : 0 < d)
    (hc13 : 0 < B ^ 2 + C ^ 2) (hc23 : 0 < (A - B) ^ 2 + C ^ 2)
    (ht13 : 0 < u ^ 2 + v ^ 2) (ht23 : 0 < (u - d) ^ 2 + v ^ 2)
    (hnot : ¬ (A = d ∧ B = u ∧ C = v ∧ R ^ 2 = 1 ∧ S ^ 2 = 1)) :
    Set.Finite {z : ℝ × ℝ × ℝ × ℝ |
      NormalizedSolution A B C R S d u v z} := by
  let D := solutionDirections A B C R S d u v
  have hD : D.Finite := solutionDirections_finite hA hd hc13 hc23 ht13 ht23
  let liftFiber : (ℝ × ℝ) → (ℝ × ℝ) → (ℝ × ℝ × ℝ × ℝ) :=
    fun p q ↦ (q.1, q.2, p.1, p.2)
  let fibers : (ℝ × ℝ) → Set (ℝ × ℝ × ℝ × ℝ) :=
    fun p ↦ liftFiber p '' solutionFiber A B C R S d u v p.1 p.2
  have hFibers : ∀ p ∈ D, (fibers p).Finite := by
    intro p hp
    rcases hp with ⟨x, y, hsol⟩
    apply Set.Finite.image
    exact solutionFiber_finite hA hd hsol.2.1 hnot
  have hUnion : (⋃ p ∈ D, fibers p).Finite := hD.biUnion hFibers
  apply hUnion.subset
  intro z hz
  rcases z with ⟨x, y, X, Y⟩
  have hp : (X, Y) ∈ D := ⟨x, y, hz⟩
  simp only [Set.mem_iUnion]
  refine ⟨(X, Y), ⟨hp, ?_⟩⟩
  refine ⟨(x, y), hz, ?_⟩
  rfl

end

end Circle

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/CircleWrapper.lean` -/

section
/-!
# Coordinate wrapper for the three-circle finiteness theorem

`Circle.circle_congruent_finite` proves the normalized algebraic-orientation
case.  This file performs the similarity normalization and splits an arbitrary
labelled congruent triangle into its two possible orientations.
-/

open Set

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace CircleWrapper

abbrev Pair : Type := ℝ × ℝ

def pairDistSq (p q : Pair) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

def toPair (p : Point) : Pair := (p 0, p 1)

def ofPair (p : Pair) : Point :=
  WithLp.toLp 2 fun i ↦ if i = 0 then p.1 else p.2

@[simp] lemma ofPair_apply_zero (p : Pair) : ofPair p 0 = p.1 := by simp [ofPair]
@[simp] lemma ofPair_apply_one (p : Pair) : ofPair p 1 = p.2 := by simp [ofPair]

@[simp] lemma toPair_ofPair (p : Pair) : toPair (ofPair p) = p := by
  ext <;> simp [toPair]

@[simp] lemma ofPair_toPair (p : Point) : ofPair (toPair p) = p := by
  ext i
  fin_cases i <;> simp [toPair]

def baselineLength (p q : Point) : ℝ := Real.sqrt (distSq p q)

lemma baselineLength_pos {p q : Point} (hpq : p ≠ q) : 0 < baselineLength p q := by
  rw [baselineLength, Real.sqrt_pos]
  rw [distSq_eq_dist_sq]
  have hdist : 0 < dist p q := dist_pos.mpr hpq
  positivity

lemma baselineLength_sq (p q : Point) : baselineLength p q ^ 2 = distSq p q := by
  rw [baselineLength, Real.sq_sqrt]
  rw [distSq_eq_dist_sq]
  positivity

lemma baseline_components_sq (p q : Point) :
    (q 0 - p 0) ^ 2 + (q 1 - p 1) ^ 2 = baselineLength p q ^ 2 := by
  rw [baselineLength_sq]
  simp [distSq, Fin.sum_univ_two]
  ring

/-- Direct similarity taking `p` to the origin and `q` to the positive
horizontal axis, with an additional division by `ρ`. -/
def normalize (p q : Point) (ρ : ℝ) (x : Point) : Pair :=
  let D := baselineLength p q
  let dx := q 0 - p 0
  let dy := q 1 - p 1
  ((dx * (x 0 - p 0) + dy * (x 1 - p 1)) / (D * ρ),
    (-dy * (x 0 - p 0) + dx * (x 1 - p 1)) / (D * ρ))

/-- Inverse to `normalize` when the baseline and scale are nonzero. -/
def denormalize (p q : Point) (ρ : ℝ) (x : Pair) : Point :=
  let D := baselineLength p q
  let dx := q 0 - p 0
  let dy := q 1 - p 1
  WithLp.toLp 2 fun i ↦
    if i = 0 then p 0 + ρ / D * (dx * x.1 - dy * x.2)
    else p 1 + ρ / D * (dy * x.1 + dx * x.2)

lemma normalize_self (p q : Point) {ρ : ℝ} (_hρ : ρ ≠ 0) :
    normalize p q ρ p = (0, 0) := by
  simp [normalize]

lemma normalize_second {p q : Point} (hpq : p ≠ q) {ρ : ℝ} (hρ : ρ ≠ 0) :
    normalize p q ρ q = (baselineLength p q / ρ, 0) := by
  have hD := baselineLength_pos hpq
  have hDsq := baselineLength_sq p q
  have hcomp := baseline_components_sq p q
  ext <;> simp [normalize]
  · field_simp [ne_of_gt hD, hρ]
    nlinarith
  · exact Or.inl (by ring)

lemma pairDistSq_normalize {p q : Point} (hpq : p ≠ q) {ρ : ℝ} (hρ : ρ ≠ 0)
    (x y : Point) :
    pairDistSq (normalize p q ρ x) (normalize p q ρ y) = distSq x y / ρ ^ 2 := by
  have hD := baselineLength_pos hpq
  have hcomp := baseline_components_sq p q
  simp [pairDistSq, normalize, distSq, Fin.sum_univ_two]
  field_simp [ne_of_gt hD, hρ]
  linear_combination
    ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) * hcomp

lemma denormalize_normalize {p q : Point} (hpq : p ≠ q) {ρ : ℝ} (hρ : ρ ≠ 0)
    (x : Point) : denormalize p q ρ (normalize p q ρ x) = x := by
  have hD := baselineLength_pos hpq
  have hcomp := baseline_components_sq p q
  ext i
  fin_cases i <;> simp [denormalize, normalize]
  · field_simp [ne_of_gt hD, hρ]
    linear_combination (x 0 - p 0) * hcomp
  · field_simp [ne_of_gt hD, hρ]
    linear_combination (x 1 - p 1) * hcomp

/-- The two possible orientations of a triangle with prescribed three side
lengths, after its first edge has been represented as `d(X,Y)`. -/
lemma triangle_two_orientations {d u v : ℝ} (hd : 0 < d)
    (p₀ p₁ p₂ : Pair)
    (h01 : pairDistSq p₀ p₁ = d ^ 2)
    (h02 : pairDistSq p₀ p₂ = u ^ 2 + v ^ 2)
    (h12 : pairDistSq p₁ p₂ = (u - d) ^ 2 + v ^ 2) :
    ∃ X Y : ℝ,
      X ^ 2 + Y ^ 2 = 1 ∧
      p₁ = (p₀.1 + d * X, p₀.2 + d * Y) ∧
      (p₂ = (p₀.1 + u * X - v * Y, p₀.2 + v * X + u * Y) ∨
       p₂ = (p₀.1 + u * X + v * Y, p₀.2 - v * X + u * Y)) := by
  let X := (p₁.1 - p₀.1) / d
  let Y := (p₁.2 - p₀.2) / d
  let a := p₂.1 - p₀.1
  let b := p₂.2 - p₀.2
  let P := a * X + b * Y
  let Q := -a * Y + b * X
  have hd0 : d ≠ 0 := ne_of_gt hd
  have h01' : (p₁.1 - p₀.1) ^ 2 + (p₁.2 - p₀.2) ^ 2 = d ^ 2 := by
    calc
      _ = pairDistSq p₀ p₁ := by simp [pairDistSq]; ring
      _ = d ^ 2 := h01
  have h02' : a ^ 2 + b ^ 2 = u ^ 2 + v ^ 2 := by
    dsimp [a, b]
    calc
      _ = pairDistSq p₀ p₂ := by simp [pairDistSq]; ring
      _ = u ^ 2 + v ^ 2 := h02
  have h12' : (p₂.1 - p₁.1) ^ 2 + (p₂.2 - p₁.2) ^ 2 =
      (u - d) ^ 2 + v ^ 2 := by
    calc
      _ = pairDistSq p₁ p₂ := by simp [pairDistSq]; ring
      _ = (u - d) ^ 2 + v ^ 2 := h12
  have hunit : X ^ 2 + Y ^ 2 = 1 := by
    dsimp [X, Y]
    field_simp [hd0]
    nlinarith [h01']
  have hP : P = u := by
    dsimp [P, a, b, X, Y]
    field_simp [hd0]
    ring_nf at h01' h02' h12' ⊢
    nlinarith
  have hPQ : P ^ 2 + Q ^ 2 = u ^ 2 + v ^ 2 := by
    dsimp [P, Q]
    calc
      (a * X + b * Y) ^ 2 + (-a * Y + b * X) ^ 2 =
          (a ^ 2 + b ^ 2) * (X ^ 2 + Y ^ 2) := by ring
      _ = a ^ 2 + b ^ 2 := by rw [hunit, mul_one]
      _ = u ^ 2 + v ^ 2 := h02'
  have hQ : Q = v ∨ Q = -v := by
    have hsq : Q ^ 2 = v ^ 2 := by rw [hP] at hPQ; nlinarith
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  refine ⟨X, Y, hunit, ?_, ?_⟩
  · ext <;> simp [X, Y] <;> field_simp [hd0] <;> ring
  · have ha : a = P * X - Q * Y := by
      calc
        a = a * (X ^ 2 + Y ^ 2) := by rw [hunit, mul_one]
        _ = P * X - Q * Y := by dsimp [P, Q]; ring
    have hb : b = Q * X + P * Y := by
      calc
        b = b * (X ^ 2 + Y ^ 2) := by rw [hunit, mul_one]
        _ = Q * X + P * Y := by dsimp [P, Q]; ring
    rcases hQ with hQ | hQ
    · left
      rw [hP, hQ] at ha hb
      ext <;> simp [a, b] at ha hb ⊢ <;> linarith
    · right
      rw [hP, hQ] at ha hb
      ext <;> simp [a, b] at ha hb ⊢ <;> linarith

end CircleWrapper

open CircleWrapper

private lemma fin3_distances_of_three (f g : Fin 3 → Point)
    (h01 : distSq (f 0) (f 1) = distSq (g 0) (g 1))
    (h02 : distSq (f 0) (f 2) = distSq (g 0) (g 2))
    (h12 : distSq (f 1) (f 2) = distSq (g 1) (g 2)) :
    ∀ i j, distSq (f i) (f j) = distSq (g i) (g j) := by
  intro i j
  fin_cases i <;> fin_cases j
  · simp [distSq_self]
  · exact h01
  · exact h02
  · norm_num
    rw [distSq_comm (f 1) (f 0), distSq_comm (g 1) (g 0)]
    exact h01
  · simp [distSq_self]
  · exact h12
  · norm_num
    convert (show distSq (f 2) (f 0) = distSq (g 2) (g 0) by
      rw [distSq_comm (f 2) (f 0), distSq_comm (g 2) (g 0)]
      exact h02) using 1 <;> congr 2
  · norm_num
    convert (show distSq (f 2) (f 1) = distSq (g 2) (g 1) by
      rw [distSq_comm (f 2) (f 1), distSq_comm (g 2) (g 1)]
      exact h12) using 1 <;> congr 2
  · simp [distSq_self]

private lemma fin3_values_of_zero (r : Fin 3 → ℝ)
    (h1 : r 1 = r 0) (h2 : r 2 = r 0) : ∀ i j, r i = r j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all

/-- The coordinate-free three-circle finiteness statement used in the global
construction.  The two alternatives are exactly the two exceptional rigid
coincidences excluded by the normalized algebraic theorem. -/
theorem threeCircleFiniteness :
    ∀ (center target : Fin 3 → Point) (radiusSq : Fin 3 → ℝ),
      Function.Injective center →
      Function.Injective target →
      (∀ i, 0 < radiusSq i) →
      Set.Finite {z : Fin 3 → Point |
        (∀ i, distSq (center i) (z i) = radiusSq i) ∧
        ∀ i j, distSq (z i) (z j) = distSq (target i) (target j)} ∨
      ((∀ i j, radiusSq i = radiusSq j) ∧
        ∀ i j, distSq (center i) (center j) = distSq (target i) (target j)) := by
  intro center target radiusSq hcenter htarget hradius
  classical
  let Flexible : Prop :=
    (∀ i j, radiusSq i = radiusSq j) ∧
      ∀ i j, distSq (center i) (center j) = distSq (target i) (target j)
  by_cases hflex : Flexible
  · exact Or.inr hflex
  left
  have hc01 : center 0 ≠ center 1 := by
    intro h; have := hcenter h; omega
  have ht01 : target 0 ≠ target 1 := by
    intro h; have := htarget h; omega
  let ρ := Real.sqrt (radiusSq 0)
  have hρ : 0 < ρ := by dsimp [ρ]; exact Real.sqrt_pos.2 (hradius 0)
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  have hρsq : ρ ^ 2 = radiusSq 0 := by
    dsimp [ρ]
    exact Real.sq_sqrt (le_of_lt (hradius 0))
  let wc : Fin 3 → Pair := fun i ↦ normalize (center 0) (center 1) ρ (center i)
  let wt : Fin 3 → Pair := fun i ↦ normalize (target 0) (target 1) ρ (target i)
  let A := baselineLength (center 0) (center 1) / ρ
  let B := (wc 2).1
  let C := (wc 2).2
  let d := baselineLength (target 0) (target 1) / ρ
  let u := (wt 2).1
  let v := (wt 2).2
  let R := Real.sqrt (radiusSq 1) / ρ
  let S := Real.sqrt (radiusSq 2) / ρ
  have hA : 0 < A := div_pos (baselineLength_pos hc01) hρ
  have hd : 0 < d := div_pos (baselineLength_pos ht01) hρ
  have hwc0 : wc 0 = (0, 0) := by
    dsimp [wc]
    exact normalize_self _ _ hρ0
  have hwc1 : wc 1 = (A, 0) := by
    dsimp [wc, A]
    exact normalize_second hc01 hρ0
  have hwt0 : wt 0 = (0, 0) := by
    dsimp [wt]
    exact normalize_self _ _ hρ0
  have hwt1 : wt 1 = (d, 0) := by
    dsimp [wt, d]
    exact normalize_second ht01 hρ0
  have hc02 : center 0 ≠ center 2 := by
    intro h; have := hcenter h; omega
  have hc12 : center 1 ≠ center 2 := by
    intro h; have := hcenter h; omega
  have ht02 : target 0 ≠ target 2 := by
    intro h; have := htarget h; omega
  have ht12 : target 1 ≠ target 2 := by
    intro h; have := htarget h; omega
  have hc13 : 0 < B ^ 2 + C ^ 2 := by
    have hdist : 0 < distSq (center 0) (center 2) := by
      rw [distSq_eq_dist_sq]
      have : 0 < dist (center 0) (center 2) := dist_pos.mpr hc02
      positivity
    have hn := pairDistSq_normalize hc01 hρ0 (center 0) (center 2)
    change pairDistSq (wc 0) (wc 2) = _ at hn
    rw [hwc0] at hn
    have heq : B ^ 2 + C ^ 2 = distSq (center 0) (center 2) / ρ ^ 2 := by
      simpa [pairDistSq, B, C] using hn
    rw [heq]
    positivity
  have hc23 : 0 < (A - B) ^ 2 + C ^ 2 := by
    have hdist : 0 < distSq (center 1) (center 2) := by
      rw [distSq_eq_dist_sq]
      have : 0 < dist (center 1) (center 2) := dist_pos.mpr hc12
      positivity
    have hn := pairDistSq_normalize hc01 hρ0 (center 1) (center 2)
    change pairDistSq (wc 1) (wc 2) = _ at hn
    rw [hwc1] at hn
    have heq : (A - B) ^ 2 + C ^ 2 = distSq (center 1) (center 2) / ρ ^ 2 := by
      simpa [pairDistSq, B, C] using hn
    rw [heq]
    positivity
  have ht13 : 0 < u ^ 2 + v ^ 2 := by
    have hdist : 0 < distSq (target 0) (target 2) := by
      rw [distSq_eq_dist_sq]
      have : 0 < dist (target 0) (target 2) := dist_pos.mpr ht02
      positivity
    have hn := pairDistSq_normalize ht01 hρ0 (target 0) (target 2)
    change pairDistSq (wt 0) (wt 2) = _ at hn
    rw [hwt0] at hn
    have heq : u ^ 2 + v ^ 2 = distSq (target 0) (target 2) / ρ ^ 2 := by
      simpa [pairDistSq, u, v] using hn
    rw [heq]
    positivity
  have ht23 : 0 < (u - d) ^ 2 + v ^ 2 := by
    have hdist : 0 < distSq (target 1) (target 2) := by
      rw [distSq_eq_dist_sq]
      have : 0 < dist (target 1) (target 2) := dist_pos.mpr ht12
      positivity
    have hn := pairDistSq_normalize ht01 hρ0 (target 1) (target 2)
    change pairDistSq (wt 1) (wt 2) = _ at hn
    rw [hwt1] at hn
    have heq : (u - d) ^ 2 + v ^ 2 = distSq (target 1) (target 2) / ρ ^ 2 := by
      have heq' : (d - u) ^ 2 + v ^ 2 = distSq (target 1) (target 2) / ρ ^ 2 := by
        simpa [pairDistSq, u, v] using hn
      nlinarith
    rw [heq]
    positivity
  have hRsqrt : (Real.sqrt (radiusSq 1)) ^ 2 = radiusSq 1 :=
    Real.sq_sqrt (le_of_lt (hradius 1))
  have hSsqrt : (Real.sqrt (radiusSq 2)) ^ 2 = radiusSq 2 :=
    Real.sq_sqrt (le_of_lt (hradius 2))
  have exceptional_flexible
      (hAd : A = d) (hBu : B = u) (hCv : C ^ 2 = v ^ 2)
      (hR : R ^ 2 = 1) (hS : S ^ 2 = 1) : Flexible := by
    have hr1 : radiusSq 1 = radiusSq 0 := by
      dsimp [R] at hR
      field_simp [hρ0] at hR
      nlinarith [hRsqrt, hρsq]
    have hr2 : radiusSq 2 = radiusSq 0 := by
      dsimp [S] at hS
      field_simp [hρ0] at hS
      nlinarith [hSsqrt, hρsq]
    have hd01 : distSq (center 0) (center 1) = distSq (target 0) (target 1) := by
      have hc := baselineLength_sq (center 0) (center 1)
      have ht := baselineLength_sq (target 0) (target 1)
      dsimp [A, d] at hAd
      field_simp [hρ0] at hAd
      nlinarith [congrArg (fun x : ℝ ↦ x ^ 2) hAd]
    have hd02 : distSq (center 0) (center 2) = distSq (target 0) (target 2) := by
      have hc := pairDistSq_normalize hc01 hρ0 (center 0) (center 2)
      have ht := pairDistSq_normalize ht01 hρ0 (target 0) (target 2)
      change pairDistSq (wc 0) (wc 2) = _ at hc
      change pairDistSq (wt 0) (wt 2) = _ at ht
      rw [hwc0] at hc
      rw [hwt0] at ht
      have hc' : B ^ 2 + C ^ 2 = distSq (center 0) (center 2) / ρ ^ 2 := by
        simpa [pairDistSq, B, C] using hc
      have ht' : u ^ 2 + v ^ 2 = distSq (target 0) (target 2) / ρ ^ 2 := by
        simpa [pairDistSq, u, v] using ht
      field_simp [hρ0] at hc' ht'
      rw [hBu, hCv] at hc'
      rw [← hc', ← ht']
      ring
    have hd12 : distSq (center 1) (center 2) = distSq (target 1) (target 2) := by
      have hc := pairDistSq_normalize hc01 hρ0 (center 1) (center 2)
      have ht := pairDistSq_normalize ht01 hρ0 (target 1) (target 2)
      change pairDistSq (wc 1) (wc 2) = _ at hc
      change pairDistSq (wt 1) (wt 2) = _ at ht
      rw [hwc1] at hc
      rw [hwt1] at ht
      have hc' : (A - B) ^ 2 + C ^ 2 = distSq (center 1) (center 2) / ρ ^ 2 := by
        simpa [pairDistSq, B, C] using hc
      have ht' : (d - u) ^ 2 + v ^ 2 = distSq (target 1) (target 2) / ρ ^ 2 := by
        simpa [pairDistSq, u, v] using ht
      field_simp [hρ0] at hc' ht'
      rw [hAd, hBu, hCv] at hc'
      rw [← hc', ← ht']
      ring
    constructor
    · exact fin3_values_of_zero radiusSq hr1 hr2
    · exact fin3_distances_of_three center target hd01 hd02 hd12
  have hnotPlus :
      ¬ (A = d ∧ B = u ∧ C = v ∧ R ^ 2 = 1 ∧ S ^ 2 = 1) := by
    rintro ⟨hAd, hBu, hCv, hR, hS⟩
    apply hflex
    apply exceptional_flexible hAd hBu (by rw [hCv]) hR hS
  have hnotMinus :
      ¬ (A = d ∧ B = u ∧ C = -v ∧ R ^ 2 = 1 ∧ S ^ 2 = 1) := by
    rintro ⟨hAd, hBu, hCv, hR, hS⟩
    apply hflex
    apply exceptional_flexible hAd hBu (by rw [hCv]; ring) hR hS
  have hfinitePlus := Circle.circle_congruent_finite hA hd hc13 hc23 ht13 ht23 hnotPlus
  have hfiniteMinus := Circle.circle_congruent_finite hA hd hc13 hc23
    (by simpa using ht13) (by simpa using ht23) hnotMinus
  let Quad := ℝ × ℝ × ℝ × ℝ
  let placePlus : Quad → Fin 3 → Pair := fun q i ↦
    if i = 0 then (q.1, q.2.1)
    else if i = 1 then (q.1 + d * q.2.2.1, q.2.1 + d * q.2.2.2)
    else (q.1 + u * q.2.2.1 - v * q.2.2.2,
      q.2.1 + v * q.2.2.1 + u * q.2.2.2)
  let placeMinus : Quad → Fin 3 → Pair := fun q i ↦
    if i = 0 then (q.1, q.2.1)
    else if i = 1 then (q.1 + d * q.2.2.1, q.2.1 + d * q.2.2.2)
    else (q.1 + u * q.2.2.1 + v * q.2.2.2,
      q.2.1 - v * q.2.2.1 + u * q.2.2.2)
  let decodePlus : Quad → Fin 3 → Point := fun q i ↦
    denormalize (center 0) (center 1) ρ (placePlus q i)
  let decodeMinus : Quad → Fin 3 → Point := fun q i ↦
    denormalize (center 0) (center 1) ρ (placeMinus q i)
  apply Set.Finite.subset
    ((hfinitePlus.image decodePlus).union (hfiniteMinus.image decodeMinus))
  intro z hz
  let w : Fin 3 → Pair := fun i ↦ normalize (center 0) (center 1) ρ (z i)
  have hw01 : pairDistSq (w 0) (w 1) = d ^ 2 := by
    calc
      _ = distSq (z 0) (z 1) / ρ ^ 2 :=
        pairDistSq_normalize hc01 hρ0 (z 0) (z 1)
      _ = distSq (target 0) (target 1) / ρ ^ 2 := by rw [hz.2 0 1]
      _ = pairDistSq (wt 0) (wt 1) :=
        (pairDistSq_normalize ht01 hρ0 (target 0) (target 1)).symm
      _ = d ^ 2 := by rw [hwt0, hwt1]; simp [pairDistSq]
  have hw02 : pairDistSq (w 0) (w 2) = u ^ 2 + v ^ 2 := by
    calc
      _ = distSq (z 0) (z 2) / ρ ^ 2 :=
        pairDistSq_normalize hc01 hρ0 (z 0) (z 2)
      _ = distSq (target 0) (target 2) / ρ ^ 2 := by rw [hz.2 0 2]
      _ = pairDistSq (wt 0) (wt 2) :=
        (pairDistSq_normalize ht01 hρ0 (target 0) (target 2)).symm
      _ = u ^ 2 + v ^ 2 := by rw [hwt0]; simp [pairDistSq, u, v]
  have hw12 : pairDistSq (w 1) (w 2) = (u - d) ^ 2 + v ^ 2 := by
    calc
      _ = distSq (z 1) (z 2) / ρ ^ 2 :=
        pairDistSq_normalize hc01 hρ0 (z 1) (z 2)
      _ = distSq (target 1) (target 2) / ρ ^ 2 := by rw [hz.2 1 2]
      _ = pairDistSq (wt 1) (wt 2) :=
        (pairDistSq_normalize ht01 hρ0 (target 1) (target 2)).symm
      _ = (u - d) ^ 2 + v ^ 2 := by
        rw [hwt1]
        simp [pairDistSq, u, v]
        ring
  obtain ⟨X, Y, hXY, hw1, hw2 | hw2⟩ :=
    triangle_two_orientations hd (w 0) (w 1) (w 2) hw01 hw02 hw12
  · let q : Quad := ((w 0).1, (w 0).2, X, Y)
    have hrad0 : (w 0).1 ^ 2 + (w 0).2 ^ 2 = 1 := by
      have hn := pairDistSq_normalize hc01 hρ0 (center 0) (z 0)
      change pairDistSq (wc 0) (w 0) = _ at hn
      rw [hwc0, hz.1 0, hρsq] at hn
      simpa [pairDistSq, ne_of_gt (hradius 0)] using hn
    have hrad1 :
        ((w 0).1 + d * X - A) ^ 2 + ((w 0).2 + d * Y) ^ 2 = R ^ 2 := by
      have hn := pairDistSq_normalize hc01 hρ0 (center 1) (z 1)
      change pairDistSq (wc 1) (w 1) = _ at hn
      rw [hwc1, hw1, hz.1 1] at hn
      dsimp [R]
      rw [div_pow, hRsqrt]
      dsimp [pairDistSq] at hn
      convert hn using 1 <;> ring
    have hrad2 :
        ((w 0).1 + u * X - v * Y - B) ^ 2 +
          ((w 0).2 + v * X + u * Y - C) ^ 2 = S ^ 2 := by
      have hn := pairDistSq_normalize hc01 hρ0 (center 2) (z 2)
      change pairDistSq (wc 2) (w 2) = _ at hn
      rw [hw2, hz.1 2] at hn
      dsimp [S]
      rw [div_pow, hSsqrt]
      dsimp [pairDistSq, B, C] at hn
      convert hn using 1 <;> ring
    have hq : Circle.NormalizedSolution A B C R S d u v q := by
      exact ⟨hrad0, hXY, hrad1, hrad2⟩
    refine Set.mem_union_left _ ⟨q, hq, ?_⟩
    funext i
    fin_cases i
    · dsimp [decodePlus, placePlus, q, w]
      simpa only [Prod.eta] using denormalize_normalize hc01 hρ0 (z 0)
    · dsimp [decodePlus, placePlus, q]
      rw [← hw1]
      dsimp [w]
      exact denormalize_normalize hc01 hρ0 (z 1)
    · dsimp [decodePlus, placePlus, q]
      rw [← hw2]
      dsimp [w]
      exact denormalize_normalize hc01 hρ0 (z 2)
  · let q : Quad := ((w 0).1, (w 0).2, X, Y)
    have hrad0 : (w 0).1 ^ 2 + (w 0).2 ^ 2 = 1 := by
      have hn := pairDistSq_normalize hc01 hρ0 (center 0) (z 0)
      change pairDistSq (wc 0) (w 0) = _ at hn
      rw [hwc0, hz.1 0, hρsq] at hn
      simpa [pairDistSq, ne_of_gt (hradius 0)] using hn
    have hrad1 :
        ((w 0).1 + d * X - A) ^ 2 + ((w 0).2 + d * Y) ^ 2 = R ^ 2 := by
      have hn := pairDistSq_normalize hc01 hρ0 (center 1) (z 1)
      change pairDistSq (wc 1) (w 1) = _ at hn
      rw [hwc1, hw1, hz.1 1] at hn
      dsimp [R]
      rw [div_pow, hRsqrt]
      dsimp [pairDistSq] at hn
      convert hn using 1 <;> ring
    have hrad2 :
        ((w 0).1 + u * X + v * Y - B) ^ 2 +
          ((w 0).2 - v * X + u * Y - C) ^ 2 = S ^ 2 := by
      have hn := pairDistSq_normalize hc01 hρ0 (center 2) (z 2)
      change pairDistSq (wc 2) (w 2) = _ at hn
      rw [hw2, hz.1 2] at hn
      dsimp [S]
      rw [div_pow, hSsqrt]
      dsimp [pairDistSq, B, C] at hn
      convert hn using 1 <;> ring
    have hq : Circle.NormalizedSolution A B C R S d u (-v) q := by
      dsimp [Circle.NormalizedSolution, q]
      refine ⟨hrad0, hXY, hrad1, ?_⟩
      convert hrad2 using 1 <;> ring
    refine Set.mem_union_right _ ⟨q, hq, ?_⟩
    funext i
    fin_cases i
    · dsimp [decodeMinus, placeMinus, q, w]
      simpa only [Prod.eta] using denormalize_normalize hc01 hρ0 (z 0)
    · dsimp [decodeMinus, placeMinus, q]
      rw [← hw1]
      dsimp [w]
      exact denormalize_normalize hc01 hρ0 (z 1)
    · dsimp [decodeMinus, placeMinus, q]
      rw [← hw2]
      dsimp [w]
      exact denormalize_normalize hc01 hρ0 (z 2)

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/Davies.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-!
# Davies decompositions for countably many finitary operations

This file isolates the set-theoretic closure interface used in the proof of
Erdős Problem 215.  A `SkolemFamily` is a countable list of operations on
finite lists.  `SkolemFamily.Hull s` is the least set containing `s` and
closed under all those operations.

The eventual Davies decomposition is expressed using terminal, countable
layers and finitely many predecessor guards.  The guard formulation is the
part of the classical iterated-hull proof that later geometric arguments
actually use.
-/

open Set Cardinal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

/-- A countable family of Skolem operations of arbitrary finite arity. -/
abbrev SkolemFamily (U : Type u) := ℕ → List U → U

namespace SkolemFamily

variable {U : Type u} (sk : SkolemFamily U)

/-- One application of a Skolem operation to parameters from `s`. -/
def Step (s : Set U) : Set U :=
  s ∪ {y | ∃ (n : ℕ) (xs : List U), (∀ x ∈ xs, x ∈ s) ∧ sk n xs = y}

/-- The closure obtained after finitely many rounds of Skolem operations. -/
def Hull (s : Set U) : Set U :=
  ⋃ k : ℕ, (Step sk)^[k] s

@[simp]
theorem subset_step (s : Set U) : s ⊆ sk.Step s := by
  intro x hx
  exact Or.inl hx

theorem step_mono : Monotone sk.Step := by
  intro s t hst x hx
  rcases hx with hx | ⟨n, xs, hxs, rfl⟩
  · exact Or.inl (hst hx)
  · exact Or.inr ⟨n, xs, fun y hy ↦ hst (hxs y hy), rfl⟩

theorem iterate_subset_iterate_succ (s : Set U) (k : ℕ) :
    (sk.Step)^[k] s ⊆ (sk.Step)^[k + 1] s := by
  rw [Function.iterate_succ_apply']
  exact sk.subset_step _

theorem iterate_subset_of_le (s : Set U) {k l : ℕ} (hkl : k ≤ l) :
    (sk.Step)^[k] s ⊆ (sk.Step)^[l] s := by
  induction l, hkl using Nat.le_induction with
  | base => exact Subset.rfl
  | succ l hkl ih =>
      exact ih.trans (sk.iterate_subset_iterate_succ s l)

theorem subset_hull (s : Set U) : s ⊆ sk.Hull s := by
  intro x hx
  exact mem_iUnion.2 ⟨0, hx⟩

theorem hull_mono : Monotone sk.Hull := by
  intro s t hst x hx
  rcases mem_iUnion.1 hx with ⟨k, hk⟩
  refine mem_iUnion.2 ⟨k, ?_⟩
  exact (sk.step_mono.iterate k) hst hk

theorem step_subset_hull (s : Set U) : sk.Step (sk.Hull s) ⊆ sk.Hull s := by
  intro y hy
  rcases hy with hy | ⟨n, xs, hxs, rfl⟩
  · exact hy
  · have hex : ∃ k : ℕ, ∀ x ∈ xs, x ∈ (sk.Step)^[k] s := by
      induction xs with
      | nil => exact ⟨0, by simp⟩
      | cons a xs ih =>
          obtain ⟨ka, hka⟩ := mem_iUnion.1 (hxs a (by simp))
          obtain ⟨kl, hkl⟩ := ih (fun x hx ↦ hxs x (by simp [hx]))
          refine ⟨max ka kl, ?_⟩
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact sk.iterate_subset_of_le s (Nat.le_max_left _ _) hka
          · exact sk.iterate_subset_of_le s (Nat.le_max_right _ _) (hkl x hx)
    rcases hex with ⟨k, hk⟩
    refine mem_iUnion.2 ⟨k + 1, ?_⟩
    rw [Function.iterate_succ_apply']
    exact (Or.inr ⟨n, xs, hk, rfl⟩ : sk n xs ∈ sk.Step ((sk.Step)^[k] s))

/-- A set is closed under the selected Skolem operations. -/
def Closed (s : Set U) : Prop :=
  ∀ (n : ℕ) (xs : List U), (∀ x ∈ xs, x ∈ s) → sk n xs ∈ s

theorem closed_hull (s : Set U) : sk.Closed (sk.Hull s) := by
  intro n xs hxs
  exact sk.step_subset_hull s (Or.inr ⟨n, xs, hxs, rfl⟩)

/-- One Skolem round does not increase an infinite cardinal bound. -/
theorem mk_step_le_max (s : Set U) :
    #(sk.Step s) ≤ max ℵ₀ (Cardinal.mk s) := by
  classical
  let code : s ⊕ (ℕ × List s) → U
    | Sum.inl x => x.1
    | Sum.inr p => sk p.1 (p.2.map Subtype.val)
  have hsub : sk.Step s ⊆ Set.range code := by
    rintro y (hy | ⟨n, xs, hxs, rfl⟩)
    · exact ⟨Sum.inl ⟨y, hy⟩, rfl⟩
    · have liftList : ∃ ys : List s, ys.map Subtype.val = xs := by
        induction xs with
        | nil => exact ⟨[], rfl⟩
        | cons x xs ih =>
            obtain ⟨ys, hys⟩ := ih (fun y hy ↦ hxs y (by simp [hy]))
            exact ⟨⟨x, hxs x (by simp)⟩ :: ys, by simp [hys]⟩
      obtain ⟨ys, hys⟩ := liftList
      refine ⟨Sum.inr (n, ys), ?_⟩
      change sk n (ys.map Subtype.val) = sk n xs
      rw [hys]
  let K : Cardinal := max ℵ₀ (Cardinal.mk s)
  have hK : ℵ₀ ≤ K := le_max_left _ _
  calc
    #(sk.Step s) ≤ #(Set.range code) := Cardinal.mk_subtype_mono (fun _ hx ↦ hsub hx)
    _ ≤ #(s ⊕ (ℕ × List s)) := Cardinal.mk_range_le
    _ = #s + ℵ₀ * #(List s) := by simp
    _ ≤ K + K * K := by
      exact add_le_add (le_max_right _ _) <|
        mul_le_mul' (le_max_left _ _) (Cardinal.mk_list_le_max _)
    _ = K := by
      rw [Cardinal.mul_eq_self hK]
      exact Cardinal.add_eq_left hK le_rfl

theorem mk_iterate_le_max (s : Set U) (k : ℕ) :
    #((sk.Step)^[k] s) ≤ max ℵ₀ (Cardinal.mk s) := by
  let K : Cardinal := max ℵ₀ (Cardinal.mk s)
  have hK : ℵ₀ ≤ K := le_max_left _ _
  induction k with
  | zero => exact le_max_right _ _
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (sk.mk_step_le_max _).trans <| max_le hK ih

/-- Cardinal form of the downward Löwenheim--Skolem estimate for this coded
Skolem language.  It is valid without any regularity assumption on the
ambient cardinal. -/
theorem mk_hull_le_max (s : Set U) :
    #(sk.Hull s) ≤ max ℵ₀ (Cardinal.mk s) := by
  let K : Cardinal := max ℵ₀ (Cardinal.mk s)
  have hK : ℵ₀ ≤ K := le_max_left _ _
  calc
    #(sk.Hull s) ≤ (ℵ₀ : Cardinal.{u}) * ⨆ k : ℕ, #((sk.Step)^[k] s) := by
      simpa [Hull] using
        (Cardinal.mk_iUnion_le_lift (fun k : ℕ ↦ (sk.Step)^[k] s))
    _ ≤ K * K := by
      refine mul_le_mul' ?_ ?_
      · simpa using hK
      · exact ciSup_le' (sk.mk_iterate_le_max s)
    _ = K := Cardinal.mul_eq_self hK

end SkolemFamily

namespace DaviesSplit

variable {U : Type u} (sk : SkolemFamily U)

/-- The initial ordinal of the cardinality of a region. -/
abbrev Stage (N : Set U) := (Cardinal.mk N).ord.ToType

/-- A fixed enumeration of a region in initial-ordinal order. -/
noncomputable def enumerate (N : Set U) : Stage N ≃ N :=
  Classical.choice <| Cardinal.eq.mp (Cardinal.mk_ord_toType (Cardinal.mk N))

/-- Parameters enumerated no later than stage `i`. -/
def seed (N : Set U) (i : Stage N) : Set U :=
  Set.range fun j : Set.Iic i ↦ (enumerate N j.1).1

/-- The upper relative hull at `i`; it contains the `i`-th enumerated point. -/
def upper (N : Set U) (i : Stage N) : Set U :=
  N ∩ sk.Hull (seed N i)

/-- The continuous lower boundary at `i`, namely the union of all earlier
upper relative hulls.  Defining the zeroth boundary this way makes it empty,
as required in the Davies construction even when the Skolem language has
constants. -/
def lower (N : Set U) (i : Stage N) : Set U :=
  ⋃ j : Set.Iio i, upper sk N j.1

/-- The successor-difference region at `i`. -/
def difference (N : Set U) (i : Stage N) : Set U :=
  upper sk N i \ lower sk N i

theorem lower_subset_upper (N : Set U) (i : Stage N) :
    lower sk N i ⊆ upper sk N i := by
  rintro x hx
  rcases mem_iUnion.1 hx with ⟨j, hxj⟩
  refine inter_subset_inter_right N (sk.hull_mono ?_) hxj
  rintro y ⟨k, rfl⟩
  refine ⟨⟨k.1, ?_⟩, rfl⟩
  have hkj : k.1 ≤ j.1 := by simpa only [Set.mem_Iic] using k.2
  have hji : j.1 < i := by simpa only [Set.mem_Iio] using j.2
  simpa only [Set.mem_Iic] using hkj.trans hji.le

theorem enumerate_mem_upper (N : Set U) (i : Stage N) :
    (enumerate N i).1 ∈ upper sk N i := by
  refine ⟨(enumerate N i).2, sk.subset_hull _ ?_⟩
  refine ⟨⟨i, ?_⟩, rfl⟩
  simp

theorem seed_mono_le {N : Set U} {i j : Stage N} (hij : i ≤ j) :
    seed N i ⊆ seed N j := by
  rintro x ⟨k, rfl⟩
  refine ⟨⟨k.1, ?_⟩, rfl⟩
  have hki : k.1 ≤ i := by simpa only [Set.mem_Iic] using k.2
  simpa only [Set.mem_Iic] using hki.trans hij

theorem upper_mono {N : Set U} {i j : Stage N} (hij : i ≤ j) :
    upper sk N i ⊆ upper sk N j :=
  inter_subset_inter_right N <| sk.hull_mono (seed_mono_le hij)

theorem upper_subset_lower {N : Set U} {i j : Stage N} (hij : i < j) :
    upper sk N i ⊆ lower sk N j := by
  intro x hx
  exact mem_iUnion.2 ⟨⟨i, hij⟩, hx⟩

theorem iUnion_difference_eq (N : Set U) :
    ⋃ i, difference sk N i = N := by
  apply Set.Subset.antisymm
  · rintro x hx
    rcases mem_iUnion.1 hx with ⟨i, hxi⟩
    exact hxi.1.1
  · intro x hxN
    let A : Set (Stage N) := {i | x ∈ upper sk N i}
    have hA : A.Nonempty := by
      let i := (enumerate N).symm ⟨x, hxN⟩
      refine ⟨i, ?_⟩
      have he : (enumerate N i).1 = x := congrArg Subtype.val ((enumerate N).apply_symm_apply ⟨x, hxN⟩)
      simpa [A, he] using enumerate_mem_upper sk N i
    obtain ⟨i, hi, hmin⟩ := wellFounded_lt.has_min A hA
    refine mem_iUnion.2 ⟨i, hi, ?_⟩
    intro hlow
    rcases mem_iUnion.1 hlow with ⟨j, hxj⟩
    exact hmin j.1 hxj j.2

theorem difference_pairwise_disjoint (N : Set U) :
    Pairwise fun i j : Stage N ↦ Disjoint (difference sk N i) (difference sk N j) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · refine Set.disjoint_left.2 ?_
    intro x hxi hxj
    exact hxj.2 ((upper_subset_lower sk hij) hxi.1)
  · refine Set.disjoint_left.2 ?_
    intro x hxi hxj
    exact hxi.2 ((upper_subset_lower sk hji) hxj.1)

theorem mk_seed_lt (N : Set U) (i : Stage N) (hN : ℵ₀ < Cardinal.mk N) :
    Cardinal.mk (seed N i) < Cardinal.mk N := by
  refine (Cardinal.mk_range_le.trans_lt ?_)
  have hstage : ℵ₀ ≤ Cardinal.mk (Stage N) := by
    simpa [Stage] using hN.le
  simpa [Stage] using Cardinal.mk_Iic_lt i (by simp) hstage

/-- Every child difference has cardinality strictly below that of an
uncountable parent region.  This is the termination measure for the Davies
tree, and uses no regularity of the parent cardinal. -/
theorem mk_difference_lt (N : Set U) (i : Stage N) (hN : ℵ₀ < Cardinal.mk N) :
    Cardinal.mk (difference sk N i) < Cardinal.mk N := by
  have hseed : Cardinal.mk (seed N i) < Cardinal.mk N := mk_seed_lt N i hN
  calc
    Cardinal.mk (difference sk N i) ≤ Cardinal.mk (sk.Hull (seed N i)) :=
      Cardinal.mk_subtype_mono fun _ hx ↦ hx.1.2
    _ ≤ max ℵ₀ (Cardinal.mk (seed N i)) := sk.mk_hull_le_max _
    _ < Cardinal.mk N := max_lt hN hseed

end DaviesSplit

/-- Operations applied to parameters from `N` stay in the region `B ∪ N`. -/
def LocallyClosed {U : Type u} (sk : SkolemFamily U) (B N : Set U) : Prop :=
  ∀ n xs, (∀ x ∈ xs, x ∈ N) → sk n xs ∈ B ∪ N

/-- A finite family of predecessor guards, each of which forces Skolem values
into `B`, and whose union is exactly `B`. -/
def IsGuardBase {U : Type u} (sk : SkolemFamily U) (B : Set U)
    (G : Finset (Set U)) : Prop :=
  B = ⋃ g ∈ G, g ∧
    ∀ g ∈ G, ∀ n xs, (∀ x ∈ xs, x ∈ g) → sk n xs ∈ B

namespace DaviesSplit

variable {U : Type u} (sk : SkolemFamily U)

/-- A finite list of points in a nonempty lower boundary is contained in one
earlier upper hull. -/
theorem list_bounded_in_lower {N : Set U} {i : Stage N}
    (hne : (lower sk N i).Nonempty) (xs : List U)
    (hxs : ∀ x ∈ xs, x ∈ lower sk N i) :
    ∃ j : Stage N, j < i ∧ ∀ x ∈ xs, x ∈ upper sk N j := by
  obtain ⟨z, hz⟩ := hne
  rcases mem_iUnion.1 hz with ⟨j0, hz0⟩
  have hj0 : j0.1 < i := by simpa only [Set.mem_Iio] using j0.2
  induction xs with
  | nil => exact ⟨j0.1, hj0, by simp⟩
  | cons x xs ih =>
      rcases mem_iUnion.1 (hxs x (by simp)) with ⟨jx, hxj⟩
      have hjx : jx.1 < i := by simpa only [Set.mem_Iio] using jx.2
      obtain ⟨jt, hjt, htail⟩ := ih (fun y hy ↦ hxs y (by simp [hy]))
      refine ⟨max jx.1 jt, max_lt hjx hjt, ?_⟩
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact upper_mono sk (le_max_left _ _) hxj
      · exact upper_mono sk (le_max_right _ _) (htail y hy)

/-- `(D6)` for a nonempty lower relative piece. -/
theorem skolem_mem_base_union_lower {B N : Set U} {i : Stage N}
    (hlocal : LocallyClosed sk B N) (hne : (lower sk N i).Nonempty)
    (n : ℕ) (xs : List U) (hxs : ∀ x ∈ xs, x ∈ lower sk N i) :
    sk n xs ∈ B ∪ lower sk N i := by
  obtain ⟨j, hj, hupper⟩ := list_bounded_in_lower sk hne xs hxs
  have hparent : sk n xs ∈ B ∪ N :=
    hlocal n xs (fun x hx ↦ (lower_subset_upper sk N i (hxs x hx)).1)
  have hhull : sk n xs ∈ sk.Hull (seed N j) :=
    sk.closed_hull _ n xs (fun x hx ↦ (hupper x hx).2)
  rcases hparent with hB | hN
  · exact Or.inl hB
  · exact Or.inr <| mem_iUnion.2 ⟨⟨j, hj⟩, hN, hhull⟩

/-- The child successor difference is locally closed over the enlarged base
`B ∪ lower i`. -/
theorem difference_locallyClosed {B N : Set U} (hlocal : LocallyClosed sk B N)
    (i : Stage N) :
    LocallyClosed sk (B ∪ lower sk N i) (difference sk N i) := by
  intro n xs hxs
  have hparent : sk n xs ∈ B ∪ N :=
    hlocal n xs (fun x hx ↦ (hxs x hx).1.1)
  have hhull : sk n xs ∈ sk.Hull (seed N i) :=
    sk.closed_hull _ n xs (fun x hx ↦ (hxs x hx).1.2)
  rcases hparent with hB | hN
  · exact Or.inl (Or.inl hB)
  · have hu : sk n xs ∈ upper sk N i := ⟨hN, hhull⟩
    by_cases hl : sk n xs ∈ lower sk N i
    · exact Or.inl (Or.inr hl)
    · exact Or.inr ⟨hu, hl⟩

theorem prior_differences_eq_lower (N : Set U) (i : Stage N) :
    {x | ∃ j, j < i ∧ x ∈ difference sk N j} = lower sk N i := by
  apply Set.Subset.antisymm
  · rintro x ⟨j, hji, hxj⟩
    exact mem_iUnion.2 ⟨⟨j, hji⟩, hxj.1⟩
  · intro x hx
    rcases mem_iUnion.1 hx with ⟨j, hxj⟩
    have hji : j.1 < i := by simpa only [Set.mem_Iio] using j.2
    have hxN : x ∈ N := hxj.1
    have hall : x ∈ ⋃ k, difference sk N k := by
      rw [iUnion_difference_eq sk N]
      exact hxN
    rcases mem_iUnion.1 hall with ⟨k, hxk⟩
    refine ⟨k, ?_, hxk⟩
    by_contra hki
    have hik : i ≤ k := le_of_not_gt hki
    have hjk : j.1 < k := hji.trans_le hik
    exact hxk.2 ((upper_subset_lower sk hjk) hxj)
    
end DaviesSplit

/-- A Davies decomposition relative to an already constructed predecessor
region `B`.  The finite guard family at a terminal stage covers `B` together
with all earlier terminal layers. -/
structure RelativeDavies {U : Type u} (sk : SkolemFamily U)
    (B N : Set U) where
  Index : Type u
  lt : Index → Index → Prop
  isWellOrder : IsWellOrder Index lt
  layer : Index → Set U
  layer_countable : ∀ i, (layer i).Countable
  layer_disjoint : Pairwise fun i j ↦ Disjoint (layer i) (layer j)
  layer_cover : ⋃ i, layer i = N
  guards : Index → Finset (Set U)
  guards_cover : ∀ i,
    B ∪ {x | ∃ j, lt j i ∧ x ∈ layer j} = ⋃ g ∈ guards i, g
  guard_closed : ∀ i g, g ∈ guards i → ∀ n xs,
    (∀ x ∈ xs, x ∈ g) →
      sk n xs ∈ B ∪ {x | ∃ j, lt j i ∧ x ∈ layer j}
  layer_closed : ∀ i n xs, (∀ x ∈ xs, x ∈ layer i) →
    sk n xs ∈
      (B ∪ {x | ∃ j, lt j i ∧ x ∈ layer j}) ∪ layer i

namespace RelativeDavies

variable {U : Type u} {sk : SkolemFamily U} {B N : Set U}

theorem layer_subset_region (D : RelativeDavies sk B N) (i : D.Index) :
    D.layer i ⊆ N := by
  intro x hx
  have hx' : x ∈ ⋃ j, D.layer j := mem_iUnion.2 ⟨i, hx⟩
  rw [D.layer_cover] at hx'
  exact hx'

noncomputable def childGuards (sk : SkolemFamily U) (G : Finset (Set U))
    (i : DaviesSplit.Stage N) :
    Finset (Set U) := by
  classical
  exact if (DaviesSplit.lower sk N i).Nonempty then
      insert (DaviesSplit.lower sk N i) G
    else G

theorem childGuards_valid (G : Finset (Set U)) (hG : IsGuardBase sk B G)
    (hlocal : LocallyClosed sk B N) (i : DaviesSplit.Stage N) :
    IsGuardBase sk (B ∪ DaviesSplit.lower sk N i) (childGuards sk G i) := by
  classical
  by_cases hne : (DaviesSplit.lower sk N i).Nonempty
  · rw [childGuards, if_pos hne]
    constructor
    · rw [hG.1]
      simp only [Finset.mem_insert, iUnion_iUnion_eq_left]
      ext x
      simp [or_comm, or_left_comm]
    · intro g hg n xs hxs
      rw [Finset.mem_insert] at hg
      rcases hg with rfl | hg
      · exact DaviesSplit.skolem_mem_base_union_lower sk hlocal hne n xs hxs
      · exact Or.inl (hG.2 g hg n xs hxs)
  · have hempty : DaviesSplit.lower sk N i = ∅ := not_nonempty_iff_eq_empty.mp hne
    rw [childGuards, if_neg hne, hempty, union_empty]
    exact hG

/-- The countable base case of the cardinal recursion. -/
def ofCountable (G : Finset (Set U)) (hG : IsGuardBase sk B G)
    (hN : N.Countable) (hlocal : LocallyClosed sk B N) :
    RelativeDavies sk B N where
  Index := ULift.{u} (Fin 1)
  lt := (fun i j ↦ i < j)
  isWellOrder := inferInstance
  layer := fun _ ↦ N
  layer_countable := fun _ ↦ hN
  layer_disjoint := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  layer_cover := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases mem_iUnion.1 hx with ⟨i, hxi⟩
      exact hxi
    · intro x hx
      exact mem_iUnion.2 ⟨ULift.up (0 : Fin 1), hx⟩
  guards := fun _ ↦ G
  guards_cover := by
    intro i
    have hempty : {x | ∃ j, j < i ∧ x ∈ N} = (∅ : Set U) := by
      ext x
      constructor
      · rintro ⟨j, hji, hx⟩
        have hji' : i < i := by simpa [Subsingleton.elim j i] using hji
        exact (lt_irrefl i hji').elim
      · simp
    rw [hempty, union_empty]
    exact hG.1
  guard_closed := by
    intro i g hg n xs hxs
    exact Or.inl (hG.2 g hg n xs hxs)
  layer_closed := by
    intro i n xs hxs
    rcases hlocal n xs hxs with hB | hN
    · exact Or.inl (Or.inl hB)
    · exact Or.inr hN

theorem lex_before_eq (hlocal : LocallyClosed sk B N)
    (child : ∀ i : DaviesSplit.Stage N,
      RelativeDavies sk (B ∪ DaviesSplit.lower sk N i) (DaviesSplit.difference sk N i))
    (i : DaviesSplit.Stage N) (a : (child i).Index) :
    {x | ∃ q : Σ j, (child j).Index,
      Sigma.Lex (fun x y : DaviesSplit.Stage N ↦ x < y) (fun j ↦ (child j).lt) q ⟨i, a⟩ ∧
        x ∈ (child q.1).layer q.2} =
      DaviesSplit.lower sk N i ∪
        {x | ∃ b, (child i).lt b a ∧ x ∈ (child i).layer b} := by
  apply Set.Subset.antisymm
  · rintro x ⟨q, hq, hxq⟩
    rcases q with ⟨j, b⟩
    cases hq with
    | left _ _ hji =>
        apply Or.inl
        rw [← DaviesSplit.prior_differences_eq_lower sk N i]
        exact ⟨j, hji, (child j).layer_subset_region b hxq⟩
    | right _ _ hba =>
        exact Or.inr ⟨b, hba, hxq⟩
  · rintro x (hx | hx)
    · rw [← DaviesSplit.prior_differences_eq_lower sk N i] at hx
      rcases hx with ⟨j, hji, hxj⟩
      have hxcover : x ∈ ⋃ b, (child j).layer b := by
        rw [(child j).layer_cover]
        exact hxj
      rcases mem_iUnion.1 hxcover with ⟨b, hxb⟩
      exact ⟨⟨j, b⟩, Sigma.Lex.left _ _ hji, hxb⟩
    · rcases hx with ⟨b, hba, hxb⟩
      exact ⟨⟨i, b⟩, Sigma.Lex.right _ _ hba, hxb⟩

/-- Assemble the recursively decomposed successor differences in
lexicographic order. -/
def combine (hlocal : LocallyClosed sk B N)
    (child : ∀ i : DaviesSplit.Stage N,
      RelativeDavies sk (B ∪ DaviesSplit.lower sk N i) (DaviesSplit.difference sk N i)) :
    RelativeDavies sk B N where
  Index := Σ i : DaviesSplit.Stage N, (child i).Index
  lt := Sigma.Lex (fun i j : DaviesSplit.Stage N ↦ i < j) (fun i ↦ (child i).lt)
  isWellOrder := {
    wf := by
      let e := (Equiv.psigmaEquivSigma (fun i : DaviesSplit.Stage N ↦ (child i).Index)).symm
      have hp : WellFounded
          (PSigma.Lex (fun i j : DaviesSplit.Stage N ↦ i < j) (fun i ↦ (child i).lt)) :=
        wellFounded_lt.psigma_lex fun i ↦ (child i).isWellOrder.wf
      have he : WellFounded (Function.onFun
          (PSigma.Lex (fun i j : DaviesSplit.Stage N ↦ i < j) (fun i ↦ (child i).lt)) e) :=
        hp.onFun
      apply he.mono
      intro x y hxy
      cases hxy with
      | left a b hij => exact PSigma.Lex.left _ _ hij
      | right a b hab => exact PSigma.Lex.right _ hab
    trichotomous := by
      rintro ⟨i, a⟩ ⟨j, b⟩ hnij hnji
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact (hnij (Sigma.Lex.left _ _ hij)).elim
      · have hab : a = b := (child i).isWellOrder.trichotomous a b
            (fun h ↦ hnij (Sigma.Lex.right _ _ h))
            (fun h ↦ hnji (Sigma.Lex.right _ _ h))
        cases hab
        rfl
      · exact (hnji (Sigma.Lex.left _ _ hji)).elim
    }
  layer := fun q ↦ (child q.1).layer q.2
  layer_countable := fun q ↦ (child q.1).layer_countable q.2
  layer_disjoint := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hne
    by_cases hij : i = j
    · subst j
      apply (child i).layer_disjoint
      intro hab
      apply hne
      cases hab
      rfl
    · exact (DaviesSplit.difference_pairwise_disjoint sk N hij).mono
        ((child i).layer_subset_region a) ((child j).layer_subset_region b)
  layer_cover := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases mem_iUnion.1 hx with ⟨q, hxq⟩
      have hd : x ∈ DaviesSplit.difference sk N q.1 :=
        (child q.1).layer_subset_region q.2 hxq
      have hall : x ∈ ⋃ i, DaviesSplit.difference sk N i := mem_iUnion.2 ⟨q.1, hd⟩
      rw [DaviesSplit.iUnion_difference_eq sk N] at hall
      exact hall
    · intro x hx
      have hall : x ∈ ⋃ i, DaviesSplit.difference sk N i := by
        rw [DaviesSplit.iUnion_difference_eq sk N]
        exact hx
      rcases mem_iUnion.1 hall with ⟨i, hxi⟩
      have hc : x ∈ ⋃ a, (child i).layer a := by
        rw [(child i).layer_cover]
        exact hxi
      rcases mem_iUnion.1 hc with ⟨a, hxa⟩
      exact mem_iUnion.2 ⟨⟨i, a⟩, hxa⟩
  guards := fun q ↦ (child q.1).guards q.2
  guards_cover := by
    rintro ⟨i, a⟩
    rw [lex_before_eq hlocal child i a, ← union_assoc]
    exact (child i).guards_cover a
  guard_closed := by
    rintro ⟨i, a⟩ g hg n xs hxs
    have h := (child i).guard_closed a g hg n xs hxs
    rw [lex_before_eq hlocal child i a, ← union_assoc]
    exact h
  layer_closed := by
    rintro ⟨i, a⟩ n xs hxs
    have h := (child i).layer_closed a n xs hxs
    rw [lex_before_eq hlocal child i a, ← union_assoc]
    exact h

/-- The relative Davies decomposition, proved by well-founded recursion on
the cardinality of the current successor-difference region. -/
theorem exists_relative (G : Finset (Set U)) (hG : IsGuardBase sk B G)
    (hlocal : LocallyClosed sk B N) :
    Nonempty (RelativeDavies sk B N) := by
  let P : Cardinal.{u} → Prop := fun κ ↦
    ∀ (B' N' : Set U) (G' : Finset (Set U)),
      IsGuardBase sk B' G' → LocallyClosed sk B' N' → Cardinal.mk N' = κ →
        Nonempty (RelativeDavies sk B' N')
  have build : ∀ κ, P κ := by
    intro κ
    exact Cardinal.lt_wf.induction κ (fun κ ih ↦ by
      dsimp only [P]
      intro B' N' G' hG' hlocal' hcard
      by_cases hc : N'.Countable
      · exact ⟨ofCountable G' hG' hc hlocal'⟩
      · have hunc : ℵ₀ < Cardinal.mk N' := by
          apply lt_of_not_ge
          intro hle
          exact hc (Cardinal.mk_le_aleph0_iff.mp hle)
        have child_exists : ∀ i : DaviesSplit.Stage N',
            Nonempty (RelativeDavies sk
              (B' ∪ DaviesSplit.lower sk N' i) (DaviesSplit.difference sk N' i)) := by
          intro i
          have hlt : Cardinal.mk (DaviesSplit.difference sk N' i) < κ :=
            (DaviesSplit.mk_difference_lt sk N' i hunc).trans_eq hcard
          exact ih _ hlt
            (B' ∪ DaviesSplit.lower sk N' i) (DaviesSplit.difference sk N' i)
            (childGuards sk G' i) (childGuards_valid G' hG' hlocal' i)
            (DaviesSplit.difference_locallyClosed sk hlocal' i) rfl
        let child : ∀ i : DaviesSplit.Stage N',
            RelativeDavies sk
              (B' ∪ DaviesSplit.lower sk N' i) (DaviesSplit.difference sk N' i) :=
          fun i ↦ Classical.choice (child_exists i)
        exact ⟨combine hlocal' child⟩)
  exact build (Cardinal.mk N) B N G hG hlocal rfl

end RelativeDavies

/-- The part of a Davies tree used by the geometric recursion.

`layer i` is the countable terminal difference at stage `i`.  Earlier layers
are covered by the finitely many sets in `guards i`.  A Skolem value whose
parameters lie in one guard is forced back into the predecessor cut, while a
Skolem value whose parameters all lie in the current layer cannot jump past
that layer. -/
structure DaviesDecomposition {U : Type u} (sk : SkolemFamily U) where
  Index : Type u
  lt : Index → Index → Prop
  isWellOrder : IsWellOrder Index lt
  layer : Index → Set U
  layer_countable : ∀ i, (layer i).Countable
  layer_disjoint : Pairwise fun i j ↦ Disjoint (layer i) (layer j)
  layer_cover : ⋃ i, layer i = Set.univ
  guards : Index → Finset (Set U)
  guards_cover : ∀ i,
    {x | ∃ j, lt j i ∧ x ∈ layer j} = ⋃ g ∈ guards i, g
  guard_closed : ∀ i g, g ∈ guards i → ∀ n xs,
    (∀ x ∈ xs, x ∈ g) → sk n xs ∈ {x | ∃ j, lt j i ∧ x ∈ layer j}
  layer_closed : ∀ i n xs, (∀ x ∈ xs, x ∈ layer i) →
    sk n xs ∈ {x | ∃ j, lt j i ∧ x ∈ layer j} ∪ layer i

/-- Davies' finite-predecessor decomposition for a countable family of
finitary operations.  No continuum-hypothesis or regularity assumption is
used. -/
theorem exists_daviesDecomposition {U : Type u} (sk : SkolemFamily U) :
    Nonempty (DaviesDecomposition sk) := by
  have hguard : IsGuardBase sk (∅ : Set U) ∅ := by
    constructor
    · simp
    · simp
  have hlocal : LocallyClosed sk (∅ : Set U) Set.univ := by
    intro n xs hxs
    exact Or.inr (Set.mem_univ _)
  obtain ⟨R⟩ := RelativeDavies.exists_relative (∅ : Finset (Set U)) hguard hlocal
  exact ⟨{
    Index := R.Index
    lt := R.lt
    isWellOrder := R.isWellOrder
    layer := R.layer
    layer_countable := R.layer_countable
    layer_disjoint := R.layer_disjoint
    layer_cover := R.layer_cover
    guards := R.guards
    guards_cover := by
      intro i
      simpa using R.guards_cover i
    guard_closed := by
      intro i g hg n xs hxs
      simpa using R.guard_closed i g hg n xs hxs
    layer_closed := by
      intro i n xs hxs
      simpa using R.layer_closed i n xs hxs
    }⟩

/-- A chosen Davies decomposition. -/
noncomputable def daviesDecomposition {U : Type u} (sk : SkolemFamily U) :
    DaviesDecomposition sk :=
  Classical.choice (exists_daviesDecomposition sk)

namespace DaviesDecomposition

variable {U : Type u} {sk : SkolemFamily U} (D : DaviesDecomposition sk)

/-- The union of all layers before `i`. -/
def before (i : D.Index) : Set U :=
  {x | ∃ j, D.lt j i ∧ x ∈ D.layer j}

theorem before_eq_guards (i : D.Index) :
    D.before i = ⋃ g ∈ D.guards i, g :=
  D.guards_cover i

/-- Abstract `(D6)`: a named uniquely-defining operation applied inside one
predecessor guard has its value in the predecessor cut. -/
theorem skolem_mem_before {i : D.Index} {g : Set U} (hg : g ∈ D.guards i)
    (n : ℕ) (xs : List U) (hxs : ∀ x ∈ xs, x ∈ g) :
    sk n xs ∈ D.before i :=
  D.guard_closed i g hg n xs hxs

theorem skolem_mem_before_or_layer (i : D.Index) (n : ℕ) (xs : List U)
    (hxs : ∀ x ∈ xs, x ∈ D.layer i) :
    sk n xs ∈ D.before i ∪ D.layer i :=
  D.layer_closed i n xs hxs

theorem exists_guard_of_mem_before {i : D.Index} {x : U} (hx : x ∈ D.before i) :
    ∃ g ∈ D.guards i, x ∈ g := by
  rw [D.before_eq_guards i] at hx
  rcases mem_iUnion.1 hx with ⟨g, hx⟩
  rcases mem_iUnion.1 hx with ⟨hg, hxg⟩
  exact ⟨g, hg, hxg⟩

end DaviesDecomposition

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/Global.lean` -/

section
/-!
# The terminal and global recursions for Erdős Problem 215

This file contains the order-theoretic part of the Jackson--Mauldin
construction.  In particular, `globalOfStageExtension` is the genuine
well-founded union argument: it does not assume that initial segments of the
continuum are countable.

The geometric work at one countable terminal layer is isolated by the exact
predicates below.  They deliberately mention the selected sets, the rational
translate hitting property, and every old--new distance condition.  Thus the
outer recursion cannot manufacture either hitting or separation from a
weaker or vacuous hypothesis.
-/

open Set

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Global

/-- A set meets every rational translate of the integer lattice in the frame
`L`. -/
def HitsRationalTranslates (S : Set Point) (L : OrientedFrame) : Prop :=
  ∀ q : RatPoint, (S ∩ L.rationalTranslate q).Nonempty

/-- A set meets the lattice of every frame rationally equivalent to `L`.
This is the form consumed by the outer Davies recursion. -/
def HitsRationalClass (S : Set Point) (L : OrientedFrame) : Prop :=
  ∀ K : OrientedFrame, K.RationallyEquivalent L →
    ∃ p : Point, p ∈ S ∧ K.IsLatticePoint p

/-- A rich pool in the coordinates of `L`.  The formulation is the literal
rank-two residue condition (4.1): every residue sublattice in every rational
translate contributes infinitely many ambient points. -/
def FrameRich (L : OrientedFrame) (P : Set Point) : Prop :=
  ∀ (d : ℕ), d ≠ 0 → ∀ (i j : Fin d) (a b : ℤ),
    Set.Infinite {x : Point | ∃ k l : ℤ,
      x = L.fromCoords
        (ratPoint (fun r ↦ if r = 0 then (i : ℕ) / d + k else (j : ℕ) / d + l)) ∧
      a ≡ k [ZMOD d] ∧ b ≡ l [ZMOD d] ∧ x ∈ P}

/-- The exact rich-selector theorem required from the arithmetic component.
The optional distinguished point is the `w` of Section 4.  When it is
present it must be selected; partiality then separates it from all other
selected points. -/
def RichSelectorTheorem : Prop :=
  ∀ (L : OrientedFrame) (P : Set Point), FrameRich L P →
    (∀ x ∈ P, L.IsRational x) →
    ∀ w : Option Point, (∀ x, w = some x → x ∈ P) →
      ∃ T : Set Point,
        T ⊆ P ∧
        IsPartialSteinhaus T ∧
        HitsRationalTranslates T L ∧
        ∀ x, w = some x → x ∈ T

/-- The exact three-circle finiteness alternative.  This is intentionally
the component theorem itself, rather than the later finite-forbidden-lines
conclusion.  `target` is a labelled triangle and `center` the labelled circle
centres. -/
def ThreeCircleFinitenessTheorem : Prop :=
  ∀ (center target : Fin 3 → Point) (radiusSq : Fin 3 → ℝ),
    Function.Injective center →
    Function.Injective target →
    (∀ i, 0 < radiusSq i) →
    (Set.Finite {z : Fin 3 → Point |
      (∀ i, distSq (center i) (z i) = radiusSq i) ∧
      ∀ i j, distSq (z i) (z j) = distSq (target i) (target j)}) ∨
      (∀ i j, radiusSq i = radiusSq j) ∧
        ∀ i j, distSq (center i) (center j) = distSq (target i) (target j)

theorem threeCircleFiniteness : ThreeCircleFinitenessTheorem := by
  simpa only [ThreeCircleFinitenessTheorem] using Erdos215.threeCircleFiniteness

/-! ## The coded Skolem universe used by the Davies decomposition -/

/-- The finite data that are baked into one three-circle Skolem operation.
The operation's only run-time parameters are the three centres. -/
structure CircleDatum where
  radiusSq : Fin 3 → ℚ
  targetSq : Fin 3 → Fin 3 → ℤ
  deriving Nonempty, Countable

/-- The labelled configurations associated to a datum and three centres. -/
def circleConfigurations (d : CircleDatum) (center : Fin 3 → Point) :
    Set (Fin 3 → Point) :=
  {z | (∀ i, distSq (center i) (z i) = (d.radiusSq i : ℝ)) ∧
    ∀ i j, distSq (z i) (z j) = (d.targetSq i j : ℝ)}

/-- A one-sorted universe containing exactly the sorts on which the global
argument invokes Skolem closure. -/
inductive Code where
  | point : Point → Code
  | frame : OrientedFrame → Code
  | latticeClass : OrientedFrame.RationalClass → Code
  | configurations : Finset (Fin 3 → Point) → Code
  | default : Code

namespace Code

def standardFrame : OrientedFrame where
  origin := 0
  c := 1
  s := 0
  unit := by norm_num

/-- The class uniquely recovered from two common rational points, totalized
by the standard class when no witness exists. -/
noncomputable def recoveredClass (x y : Point) : OrientedFrame.RationalClass :=
  by
    classical
    exact if h : ∃ L : OrientedFrame,
      x ≠ y ∧ L.IsRational x ∧ L.IsRational y then
      OrientedFrame.classOf (Classical.choose h)
    else OrientedFrame.classOf standardFrame

theorem recoveredClass_eq {L : OrientedFrame} {x y : Point} (hxy : x ≠ y)
    (hx : L.IsRational x) (hy : L.IsRational y) :
    recoveredClass x y = OrientedFrame.classOf L := by
  have h : ∃ K : OrientedFrame,
      x ≠ y ∧ K.IsRational x ∧ K.IsRational y := ⟨L, hxy, hx, hy⟩
  rw [recoveredClass, dif_pos h]
  let K := Classical.choose h
  have hK := Classical.choose_spec h
  exact OrientedFrame.class_eq_of_two_common hxy hK.2.1 hx hK.2.2 hy

/-- Turn a finite set into a `Finset`, with a total default in the infinite
case. -/
noncomputable def finiteCode {X : Type} [DecidableEq X] (s : Set X) : Finset X :=
  by
    classical
    exact if h : s.Finite then h.toFinset else ∅

theorem mem_finiteCode_iff {X : Type} [DecidableEq X] {s : Set X}
    (hs : s.Finite) (x : X) : x ∈ finiteCode s ↔ x ∈ s := by
  simp [finiteCode, hs]

/-- A canonical (choice-dependent) enumeration of a nonempty position in a
finset.  The natural index is exactly the parameter-free integer baked into
the second D6 application in Claim 2.7. -/
noncomputable def nthConfiguration (F : Finset (Fin 3 → Point)) (k : ℕ) :
    Fin 3 → Point :=
  if hk : k < F.card then
    ((Fintype.equivFin {z // z ∈ F}).symm
      ⟨k, by simpa only [Fintype.card_coe] using hk⟩).1
  else fun _ ↦ 0

theorem exists_nthConfiguration_eq (F : Finset (Fin 3 → Point))
    {z : Fin 3 → Point} (hz : z ∈ F) :
    ∃ k < F.card, nthConfiguration F k = z := by
  let e := Fintype.equivFin {w // w ∈ F}
  let j := e ⟨z, hz⟩
  have hj : (j : ℕ) < F.card := by
    simpa only [Fintype.card_coe] using j.2
  refine ⟨j, hj, ?_⟩
  rw [nthConfiguration, dif_pos hj]
  exact congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)

/-- A parameter-free enumeration of rational coordinate pairs. -/
noncomputable def ratEnumeration : ℕ → RatPoint :=
  Classical.choose (exists_surjective_nat RatPoint)

theorem ratEnumeration_surjective : Function.Surjective ratEnumeration :=
  Classical.choose_spec (exists_surjective_nat RatPoint)

/-- All baked three-circle numeric data form a countable type. -/
noncomputable def circleDataEnumeration : ℕ → CircleDatum :=
  Classical.choose (exists_surjective_nat CircleDatum)

theorem circleDataEnumeration_surjective :
    Function.Surjective circleDataEnumeration :=
  Classical.choose_spec (exists_surjective_nat CircleDatum)

/-- The countable family of named Skolem operations used by the global
argument.  Odd indices `2*n+3` form finite three-circle solution codes;
even indices `2*k+4` recover a lattice class from the first two entries of
the `k`-th coded configuration. -/
noncomputable def skolem : SkolemFamily Code :=
  fun n xs ↦
    match n, xs with
    | 0, [latticeClass C] => frame (OrientedFrame.representative C)
    | 1, [frame L] => latticeClass (OrientedFrame.classOf L)
    | 2, [point x, point y] => latticeClass (recoveredClass x y)
    | n + 3, [latticeClass C] =>
        point ((OrientedFrame.representative C).fromCoords
          (ratPoint (ratEnumeration n)))
    | n + 3, [point c₀, point c₁, point c₂] =>
        if Odd (n + 3) then
          let d := circleDataEnumeration (n / 2)
          configurations (finiteCode (circleConfigurations d ![c₀, c₁, c₂]))
        else default
    | n + 4, [configurations F] =>
        if Even (n + 4) then
          let z := nthConfiguration F (n / 2)
          latticeClass (recoveredClass (z 0) (z 1))
        else default
    | _, _ => default

@[simp]
theorem skolem_representative (C : OrientedFrame.RationalClass) :
    skolem 0 [latticeClass C] = frame (OrientedFrame.representative C) := rfl

@[simp]
theorem skolem_classOf (L : OrientedFrame) :
    skolem 1 [frame L] = latticeClass (OrientedFrame.classOf L) := rfl

@[simp]
theorem skolem_recover (x y : Point) :
    skolem 2 [point x, point y] = latticeClass (recoveredClass x y) := rfl

@[simp]
theorem skolem_rationalPoint (n : ℕ)
    (C : OrientedFrame.RationalClass) :
    skolem (n + 3) [latticeClass C] =
      point ((OrientedFrame.representative C).fromCoords
        (ratPoint (ratEnumeration n))) := rfl

@[simp]
theorem skolem_circleCode (r : ℕ) (c₀ c₁ c₂ : Point) :
    skolem (2 * r + 3) [point c₀, point c₁, point c₂] =
      configurations (finiteCode (circleConfigurations
        (circleDataEnumeration r) ![c₀, c₁, c₂])) := by
  have hodd : Odd (2 * r + 3) := ⟨r + 1, by omega⟩
  simp [skolem, hodd]

@[simp]
theorem skolem_classFromConfiguration (k : ℕ)
    (F : Finset (Fin 3 → Point)) :
    skolem (2 * k + 4) [configurations F] =
      latticeClass (recoveredClass
        ((nthConfiguration F k) 0) ((nthConfiguration F k) 1)) := by
  have heven : Even (2 * k + 4) := ⟨k + 2, by omega⟩
  simp [skolem, heven]

end Code

/-- The exact circle alternative implies finiteness for a baked rational /
integer datum whenever the exceptional congruence would violate partiality of
the three old centres. -/
theorem circleConfigurations_finite
    (circle : ThreeCircleFinitenessTheorem)
    (d : CircleDatum) (center target : Fin 3 → Point)
    (hcenter : Function.Injective center) (htarget : Function.Injective target)
    (hpositive : ∀ i, 0 < (d.radiusSq i : ℝ))
    (htargetSq : ∀ i j,
      distSq (target i) (target j) = (d.targetSq i j : ℝ))
    {S : Set Point} (hS : IsPartialSteinhaus S)
    (hcenterS : ∀ i, center i ∈ S) :
    (circleConfigurations d center).Finite := by
  rcases circle center target (fun i ↦ (d.radiusSq i : ℝ))
      hcenter htarget hpositive with hfinite | hexception
  · let Q : Set (Fin 3 → Point) :=
      {z | (∀ i, distSq (center i) (z i) = (d.radiusSq i : ℝ)) ∧
        ∀ i j, distSq (z i) (z j) = distSq (target i) (target j)}
    have hset : Q = circleConfigurations d center := by
      ext z
      constructor
      · rintro ⟨hc, ht⟩
        exact ⟨hc, fun i j ↦ (ht i j).trans (htargetSq i j)⟩
      · rintro ⟨hc, ht⟩
        exact ⟨hc, fun i j ↦ (ht i j).trans (htargetSq i j).symm⟩
    rw [← hset]
    exact hfinite
  · exfalso
    have hne : center 0 ≠ center 1 := by
      intro h
      have h01 : (0 : Fin 3) = 1 := hcenter h
      norm_num at h01
    exact hS (hcenterS 0) (hcenterS 1) hne (d.targetSq 0 1)
      ((hexception.2 0 1).trans (htargetSq 0 1))

namespace CodedDavies

variable (D : DaviesDecomposition Code.skolem)

/-- The chosen Davies decomposition of the concrete coded universe. -/
noncomputable def decomposition : DaviesDecomposition Code.skolem :=
  daviesDecomposition Code.skolem

/-- Rational-equivalence classes whose class tags occur in one terminal
layer. -/
def classes (i : D.Index) : Set OrientedFrame.RationalClass :=
  {C | Code.latticeClass C ∈ D.layer i}

theorem classes_countable (i : D.Index) : (classes D i).Countable := by
  apply (D.layer_countable i).preimage
  intro C K h
  injection h

theorem not_mem_before_of_mem_layer {i : D.Index} {a : Code}
    (ha : a ∈ D.layer i) : a ∉ D.before i := by
  intro hb
  rcases hb with ⟨j, hji, hj⟩
  letI : IsWellOrder D.Index D.lt := D.isWellOrder
  have hne : j ≠ i := by
    intro h
    subst j
    exact (irrefl_of D.lt i hji)
  exact Set.disjoint_left.1 (D.layer_disjoint hne) hj ha

/-- If two distinct points in one predecessor guard are rational in `L`, the
class code of `L` is already in the predecessor cut.  This is the first D6
application used both in pool localization and in the one-cross argument. -/
theorem class_mem_before_of_two_points_in_guard
    {i : D.Index} {g : Set Code} (hg : g ∈ D.guards i)
    {L : OrientedFrame} {x y : Point} (hxy : x ≠ y)
    (hxg : Code.point x ∈ g) (hyg : Code.point y ∈ g)
    (hxL : L.IsRational x) (hyL : L.IsRational y) :
    Code.latticeClass (OrientedFrame.classOf L) ∈ D.before i := by
  have hs := D.skolem_mem_before hg 2 [Code.point x, Code.point y] (by
    intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl
    · exact hxg
    · exact hyg)
  simpa only [Code.skolem_recover, Code.recoveredClass_eq hxy hxL hyL] using hs

/-- First D6 application in the finite-forbidden-lines contradiction: three
centres in one guard put their finite configuration code below the current
layer. -/
theorem circleCode_mem_before
    {i : D.Index} {g : Set Code} (hg : g ∈ D.guards i)
    (d : CircleDatum) (c₀ c₁ c₂ : Point)
    (hc₀ : Code.point c₀ ∈ g) (hc₁ : Code.point c₁ ∈ g)
    (hc₂ : Code.point c₂ ∈ g) :
    Code.configurations (Code.finiteCode
      (circleConfigurations d ![c₀, c₁, c₂])) ∈ D.before i := by
  obtain ⟨r, hr⟩ := Code.circleDataEnumeration_surjective d
  have hs := D.skolem_mem_before hg (2 * r + 3)
    [Code.point c₀, Code.point c₁, Code.point c₂] (by
      intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact hc₀
      · exact hc₁
      · exact hc₂)
  rw [Code.skolem_circleCode, hr] at hs
  exact hs

/-- Second D6 application, using the single finite-set code as its only
parameter.  Any coded triple whose first two points are common rational points
recovers the corresponding current lattice class below the layer. -/
theorem class_mem_before_of_configurationCode
    {i : D.Index} (F : Finset (Fin 3 → Point))
    (hF : Code.configurations F ∈ D.before i)
    {z : Fin 3 → Point} (hzF : z ∈ F)
    {L : OrientedFrame} (hz : z 0 ≠ z 1)
    (hz₀ : L.IsRational (z 0)) (hz₁ : L.IsRational (z 1)) :
    Code.latticeClass (OrientedFrame.classOf L) ∈ D.before i := by
  obtain ⟨g, hg, hFg⟩ := D.exists_guard_of_mem_before hF
  obtain ⟨k, hk, hkz⟩ := Code.exists_nthConfiguration_eq F hzF
  have hs := D.skolem_mem_before hg (2 * k + 4) [Code.configurations F] (by
    intro a ha
    have : a = Code.configurations F := by
      simpa only [List.mem_singleton] using ha
    simpa only [this] using hFg)
  rw [Code.skolem_classFromConfiguration] at hs
  rw [hkz, Code.recoveredClass_eq hz hz₀ hz₁] at hs
  exact hs

/-- A predecessor guard contains at most one point rational in the current
lattice class. -/
theorem rational_points_in_guard_subsingleton
    {i : D.Index} {g : Set Code} (hg : g ∈ D.guards i)
    {L : OrientedFrame}
    (hclass : Code.latticeClass (OrientedFrame.classOf L) ∈ D.layer i) :
    {x : Point | Code.point x ∈ g ∧ L.IsRational x}.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  exact (not_mem_before_of_mem_layer D hclass)
    (class_mem_before_of_two_points_in_guard D hg hxy hx.1 hy.1 hx.2 hy.2)

/-- Only finitely many `L`-rational points have point codes below the current
Davies layer.  There is at most one such point in each of finitely many
guards. -/
theorem finite_rational_points_before
    {i : D.Index} {L : OrientedFrame}
    (hclass : Code.latticeClass (OrientedFrame.classOf L) ∈ D.layer i) :
    Set.Finite {x : Point | Code.point x ∈ D.before i ∧ L.IsRational x} := by
  let R : {g // g ∈ D.guards i} → Set Point := fun g ↦
    {x | Code.point x ∈ g.1 ∧ L.IsRational x}
  have hR : ∀ g, (R g).Finite := by
    intro g
    exact (rational_points_in_guard_subsingleton D g.2 hclass).finite
  have hU : Set.Finite (⋃ g, R g) := Set.finite_iUnion hR
  apply hU.subset
  intro x hx
  obtain ⟨g, hg, hxg⟩ := D.exists_guard_of_mem_before hx.1
  exact mem_iUnion.2 ⟨⟨g, hg⟩, hxg, hx.2⟩

/-- Every rational point of a class in the current layer is itself coded
either before that layer or in it.  The rational coordinate is compiled into
the natural-number index of the Skolem operation. -/
theorem rational_point_mem_before_or_layer
    {i : D.Index} {L : OrientedFrame}
    (hclass : Code.latticeClass (OrientedFrame.classOf L) ∈ D.layer i)
    {x : Point} (hx : L.IsRational x) :
    Code.point x ∈ D.before i ∪ D.layer i := by
  let C := OrientedFrame.classOf L
  let K := OrientedFrame.representative C
  have hKL : K.RationallyEquivalent L := by
    apply (OrientedFrame.classOf_eq_iff K L).1
    exact (OrientedFrame.classOf_representative C).trans rfl
  obtain ⟨q, hq⟩ := (hKL x).2 hx
  obtain ⟨n, hn⟩ := Code.ratEnumeration_surjective q
  have hs := D.skolem_mem_before_or_layer i (n + 3)
    [Code.latticeClass C] (by
      intro a ha
      have ha' : a = Code.latticeClass C := by
        simpa only [List.mem_singleton] using ha
      simpa only [ha'] using hclass)
  rw [Code.skolem_rationalPoint] at hs
  simpa only [C, K, hn, ← hq] using hs

/-- Pool localization in its strongest useful form: among all rational
points of a current class, only finitely many fail to lie in the current
terminal layer.  Every residue sublattice used by richness is a subset of
this rational plane, so the paper's localization lemma follows immediately. -/
theorem finite_rational_points_outside_layer
    {i : D.Index} {L : OrientedFrame}
    (hclass : Code.latticeClass (OrientedFrame.classOf L) ∈ D.layer i) :
    Set.Finite {x : Point | L.IsRational x ∧ Code.point x ∉ D.layer i} := by
  apply (finite_rational_points_before D hclass).subset
  intro x hx
  refine ⟨?_, hx.1⟩
  rcases rational_point_mem_before_or_layer D hclass hx.1 with hb | hl
  · exact hb
  · exact (hx.2 hl).elim

theorem exists_layer_of_class (C : OrientedFrame.RationalClass) :
    ∃ i : D.Index, C ∈ classes D i := by
  have h : Code.latticeClass C ∈ ⋃ i, D.layer i := by
    rw [D.layer_cover]
    trivial
  rcases mem_iUnion.1 h with ⟨i, hi⟩
  exact ⟨i, hi⟩

end CodedDavies

/-- Nonintegral squared distance, packaged as a symmetric binary relation. -/
def Separated (x y : Point) : Prop :=
  x ≠ y → ∀ z : ℤ, distSq x y ≠ (z : ℝ)

lemma separated_comm {x y : Point} : Separated x y ↔ Separated y x := by
  simp only [Separated, ne_eq]
  constructor
  · intro h hyx z hz
    exact h (Ne.symm hyx) z (by simpa only [distSq_comm] using hz)
  · intro h hxy z hz
    exact h (Ne.symm hxy) z (by simpa only [distSq_comm] using hz)

lemma partial_union {A B : Set Point} (hA : IsPartialSteinhaus A)
    (hB : IsPartialSteinhaus B)
    (hcross : ∀ x ∈ A, ∀ y ∈ B, Separated x y) :
    IsPartialSteinhaus (A ∪ B) := by
  intro x hx y hy hxy z
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hA hx hy hxy z
  · exact hcross x hx y hy hxy z
  · exact (separated_comm.mp (hcross y hy x hx)) hxy z
  · exact hB hx hy hxy z

/-- Data produced by the forbidden-line and candidate-pool construction for
one member of a countable terminal layer.  `old` includes the set inherited
from earlier terminal layers and all blocks already chosen in this layer.
The only old point not covered by `old_safe` is `distinguished`; requiring it to be
selected makes the block's own partiality handle that pair.

The proof that such data exist is the geometric Claim 2.7 part of the
construction; it must be derived from `ThreeCircleFinitenessTheorem` and the
guard closure of a `DaviesDecomposition`, not postulated globally.
-/
structure CandidatePool (old : Set Point) (L : OrientedFrame) where
  pool : Set Point
  distinguished : Option Point
  rich : FrameRich L pool
  rational : ∀ x ∈ pool, L.IsRational x
  distinguished_mem : ∀ x, distinguished = some x → x ∈ old ∩ pool
  old_safe : ∀ x ∈ old, ∀ y ∈ pool,
    distinguished ≠ some x → Separated x y

/-- One exact selector application extends a partial old set by a block
meeting all rational translates of `L`. -/
theorem extendByCandidatePool
    (selector : RichSelectorTheorem) {old : Set Point} (hOld : IsPartialSteinhaus old)
    (L : OrientedFrame) (C : CandidatePool old L) :
    ∃ T : Set Point,
      T ⊆ C.pool ∧
      IsPartialSteinhaus (old ∪ T) ∧
      HitsRationalTranslates T L := by
  obtain ⟨T, hTP, hTpartial, hThits, hdistinguished⟩ :=
    selector L C.pool C.rich C.rational C.distinguished
      (fun x hx ↦ (C.distinguished_mem x hx).2)
  refine ⟨T, hTP, ?_, hThits⟩
  apply partial_union hOld hTpartial
  intro x hx y hy
  by_cases hdx : C.distinguished = some x
  · have hxT : x ∈ T := hdistinguished x hdx
    intro hxy z hz
    exact hTpartial hxT hy hxy z hz
  · exact C.old_safe x hx y (hTP hy) hdx

/-- Frames in a countable terminal layer.  The set `active` is used instead
of an arbitrary countable type so the inner recursion is the ordinary
natural-number recursion used in the paper. -/
structure TerminalLayer where
  active : Set ℕ
  frame : ℕ → OrientedFrame

namespace TerminalLayer

variable (A : TerminalLayer)

/-- A set has hit every rational-equivalence class listed in the terminal
layer. -/
def Hits (S : Set Point) : Prop :=
  ∀ n ∈ A.active, HitsRationalClass S (A.frame n)

end TerminalLayer

/-! ## A countable schedule of all residue requirements -/

/-- One rank-two congruence class occurring in the definition of richness. -/
structure ResidueRequirement where
  d : ℕ
  hd : d ≠ 0
  i : Fin d
  j : Fin d
  a : ℤ
  b : ℤ
  deriving Countable

namespace ResidueRequirement

/-- The rational translate containing the whole residue requirement. -/
def translate (R : ResidueRequirement) : RatPoint := fun r ↦
  if r = 0 then (R.i : ℕ) / R.d else (R.j : ℕ) / R.d

theorem mem_rationalTranslate {L : OrientedFrame} {R : ResidueRequirement}
    {x : Point} (hx : x ∈ FramedResidueSet L R.d R.i R.j R.a R.b) :
    x ∈ L.rationalTranslate R.translate := by
  rcases hx with ⟨k, l, rfl, -, -⟩
  let z : IntPoint := fun r ↦ if r = 0 then k else l
  refine ⟨z, ?_⟩
  apply congrArg L.fromCoords
  ext r
  fin_cases r <;> simp [translate, z, ratPoint, intPoint]

end ResidueRequirement

/-- A residue requirement attached to an active frame of a terminal layer. -/
structure ScheduledRequirement (A : TerminalLayer) where
  index : ℕ
  active : index ∈ A.active
  residue : ResidueRequirement
  deriving Countable

namespace ScheduledRequirement

variable {A : TerminalLayer}

noncomputable def encodable : Encodable (ScheduledRequirement A) :=
  Encodable.ofCountable _

/-- Cantor pairing makes every requirement occur infinitely often: the
second paired coordinate is deliberately ignored. -/
noncomputable def scheduled (default : ScheduledRequirement A) (r : ℕ) :
    ScheduledRequirement A :=
  ( @Encodable.decode (ScheduledRequirement A) encodable (Nat.unpair r).1
    ).getD default

theorem scheduled_pair (default req : ScheduledRequirement A) (k : ℕ) :
    scheduled default
      (Nat.pair (@Encodable.encode (ScheduledRequirement A) encodable req) k) = req := by
  simp [scheduled, Nat.unpair_pair,
    @Encodable.encodek (ScheduledRequirement A) encodable]

end ScheduledRequirement

/-- A harmless totalization used when a previous point is already rational
in the frame currently being scheduled. -/
def defaultFramedLine (L : OrientedFrame) : FramedLine L where
  point := 0
  direction := WithLp.toLp 2 fun r ↦ if r = 0 then 1 else 0
  direction_ne := by
    intro h
    have h0 := congrArg (fun p : Point ↦ p 0) h
    norm_num at h0

/-- The line containing every rational point at rational squared distance
from `x`, totalized in the rational case. -/
noncomputable def rationalDistanceLine (L : OrientedFrame) (x : Point) :
    FramedLine L := by
  classical
  exact if hx : L.IsRational x then defaultFramedLine L
    else Classical.choose (framed_rational_sqDist_line hx)

theorem mem_rationalDistanceLine {L : OrientedFrame} {x y : Point}
    (hx : ¬L.IsRational x) (hy : L.IsRational y)
    (hxy : HasRationalSqDist x y) :
    y ∈ (rationalDistanceLine L x).carrier := by
  rw [rationalDistanceLine, dif_neg hx]
  exact Classical.choose_spec (framed_rational_sqDist_line hx) y hy hxy

/-- Well-founded recursive choice from a set depending on all earlier
values.  Keeping this small utility explicit makes the later candidate
sequence a genuine natural-number recursion. -/
noncomputable def recursiveChoice {X : Type}
    (available : (n : ℕ) → (Fin n → X) → Set X)
    (havailable : ∀ n previous, (available n previous).Nonempty)
    (n : ℕ) : X :=
  Classical.choose (havailable n fun k ↦
    recursiveChoice available havailable k.1)
termination_by n

theorem recursiveChoice_spec {X : Type}
    (available : (n : ℕ) → (Fin n → X) → Set X)
    (havailable : ∀ n previous, (available n previous).Nonempty)
    (n : ℕ) :
    recursiveChoice available havailable n ∈
      available n (fun k ↦ recursiveChoice available havailable k.1) := by
  rw [recursiveChoice]
  exact Classical.choose_spec (havailable n fun k ↦
    recursiveChoice available havailable k.1)

namespace CodedDavies

variable (D : DaviesDecomposition Code.skolem)

noncomputable def classEncodable (i : D.Index) :
    Encodable {C // C ∈ classes D i} :=
  (classes_countable D i).toEncodable

noncomputable def encodedClass (i : D.Index) (n : ℕ) :
    Option OrientedFrame.RationalClass :=
  Option.map Subtype.val
    (@Encodable.decode {C // C ∈ classes D i} (classEncodable D i) n)

/-- The no-repetition natural-number enumeration of the class tags in one
countable Davies layer. -/
noncomputable def terminalLayer (i : D.Index) : TerminalLayer where
  active := Set.range
    (@Encodable.encode {C // C ∈ classes D i} (classEncodable D i))
  frame := fun n ↦
    match encodedClass D i n with
    | some C => OrientedFrame.representative C
    | none => Code.standardFrame

theorem active_frame_class_mem_layer {i : D.Index} {n : ℕ}
    (hn : n ∈ (terminalLayer D i).active) :
    Code.latticeClass
      (OrientedFrame.classOf ((terminalLayer D i).frame n)) ∈ D.layer i := by
  rcases hn with ⟨C, rfl⟩
  have hdecode : @Encodable.decode {C // C ∈ classes D i} (classEncodable D i)
      (@Encodable.encode {C // C ∈ classes D i} (classEncodable D i) C) = some C :=
    @Encodable.encodek {C // C ∈ classes D i} (classEncodable D i) C
  simp only [terminalLayer, encodedClass, hdecode, Option.map_some]
  rw [OrientedFrame.classOf_representative]
  change Code.latticeClass (C : OrientedFrame.RationalClass) ∈ D.layer i
  have hC := C.property
  change Code.latticeClass (C : OrientedFrame.RationalClass) ∈ D.layer i at hC
  exact hC

theorem class_appears_in_terminalLayer {i : D.Index}
    {C : OrientedFrame.RationalClass} (hC : C ∈ classes D i) :
    ∃ n ∈ (terminalLayer D i).active,
      OrientedFrame.classOf ((terminalLayer D i).frame n) = C := by
  let c : {K // K ∈ classes D i} := ⟨C, hC⟩
  let n := @Encodable.encode {K // K ∈ classes D i} (classEncodable D i) c
  refine ⟨n, ⟨c, rfl⟩, ?_⟩
  have hdecode : @Encodable.decode {K // K ∈ classes D i} (classEncodable D i) n = some c :=
    @Encodable.encodek {K // K ∈ classes D i} (classEncodable D i) c
  simp only [terminalLayer, encodedClass, hdecode, Option.map_some]
  exact OrientedFrame.classOf_representative C

theorem terminalLayer_class_injOn (i : D.Index) :
    Set.InjOn (fun n ↦ OrientedFrame.classOf ((terminalLayer D i).frame n))
      (terminalLayer D i).active := by
  intro n hn m hm hnm
  rcases hn with ⟨C, rfl⟩
  rcases hm with ⟨K, rfl⟩
  have hdecodeC :
      @Encodable.decode {J // J ∈ classes D i} (classEncodable D i)
        (@Encodable.encode {J // J ∈ classes D i} (classEncodable D i) C) = some C :=
    @Encodable.encodek {J // J ∈ classes D i} (classEncodable D i) C
  have hdecodeK :
      @Encodable.decode {J // J ∈ classes D i} (classEncodable D i)
        (@Encodable.encode {J // J ∈ classes D i} (classEncodable D i) K) = some K :=
    @Encodable.encodek {J // J ∈ classes D i} (classEncodable D i) K
  simp only [terminalLayer, encodedClass, hdecodeC, hdecodeK, Option.map_some,
    OrientedFrame.classOf_representative] at hnm
  apply congrArg
    (@Encodable.encode {J // J ∈ classes D i} (classEncodable D i))
  exact Subtype.ext hnm

theorem every_class_appears (C : OrientedFrame.RationalClass) :
    ∃ (i : D.Index) (n : ℕ), n ∈ (terminalLayer D i).active ∧
      OrientedFrame.classOf ((terminalLayer D i).frame n) = C := by
  obtain ⟨i, hi⟩ := exists_layer_of_class D C
  obtain ⟨n, hn, hclass⟩ := class_appears_in_terminalLayer D hi
  exact ⟨i, n, hn, hclass⟩

/-- The robust localized pool remains rich after deleting finitely many
framed affine lines. -/
theorem layerAvoidPool_rich {i : D.Index} {L : OrientedFrame}
    (hclass : Code.latticeClass (OrientedFrame.classOf L) ∈ D.layer i)
    (G : Finset (FramedLine L)) :
    FrameRich L {x | Code.point x ∈ D.layer i ∧
      ∀ line ∈ G, x ∉ line.carrier} := by
  intro d hd ri rj a b
  let bad : Set Point :=
    {x | L.IsRational x ∧ Code.point x ∉ D.layer i}
  have hbad : bad.Finite := finite_rational_points_outside_layer D hclass
  have hinf := framedResidueSet_infinite_avoid hd ri rj a b G hbad
  apply hinf.mono
  intro x hx
  rcases hx with ⟨⟨k, l, heq, hka, hlb⟩, hxbad, hxlines⟩
  have hrat : L.IsRational x := by
    refine ⟨fun r ↦ if r = 0 then (ri : ℕ) / d + k else (rj : ℕ) / d + l, ?_⟩
    exact heq
  have hlayer : Code.point x ∈ D.layer i := by
    by_contra hout
    exact hxbad ⟨hrat, hout⟩
  exact ⟨k, l, heq, hka, hlb, hlayer, hxlines⟩

/-- For a fixed predecessor guard and a fixed rational translate, all
`L`-rational candidates having rational squared distance from an
`L`-irrational old point lie on finitely many framed lines.  This is the
three-centre/D6 core of Claim 2.7. -/
theorem finite_forbiddenLines_in_guard
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index} {L : OrientedFrame} {old : Set Point}
    {g : Set Code} (hg : g ∈ D.guards i)
    (hOld : IsPartialSteinhaus old)
    (hclass : Code.latticeClass (OrientedFrame.classOf L) ∈ D.layer i)
    (q : RatPoint) :
    ∃ G : Finset (FramedLine L),
      ∀ x ∈ old, Code.point x ∈ g → ¬L.IsRational x →
        ∀ y ∈ L.rationalTranslate q, HasRationalSqDist x y →
          ∃ line ∈ G, y ∈ line.carrier := by
  classical
  by_contra hcover
  have hstep (G : Finset (FramedLine L)) :
      ∃ x ∈ old, Code.point x ∈ g ∧ ¬L.IsRational x ∧
        ∃ y ∈ L.rationalTranslate q, HasRationalSqDist x y ∧
          ∀ line ∈ G, y ∉ line.carrier := by
    have hn := not_exists.mp hcover G
    push Not at hn
    exact hn
  obtain ⟨c₀, hc₀old, hc₀g, hc₀irr, t₀, ht₀q, hd₀, -⟩ :=
    hstep ∅
  obtain ⟨line₀, hline₀⟩ := framed_rational_sqDist_line hc₀irr
  have ht₀rat : L.IsRational t₀ := isRational_of_mem_rationalTranslate ht₀q
  have ht₀line : t₀ ∈ line₀.carrier := hline₀ t₀ ht₀rat hd₀
  obtain ⟨c₁, hc₁old, hc₁g, hc₁irr, t₁, ht₁q, hd₁, ht₁avoid⟩ :=
    hstep {line₀}
  obtain ⟨line₁, hline₁⟩ := framed_rational_sqDist_line hc₁irr
  have ht₁rat : L.IsRational t₁ := isRational_of_mem_rationalTranslate ht₁q
  have ht₁line : t₁ ∈ line₁.carrier := hline₁ t₁ ht₁rat hd₁
  have ht₁not₀ : t₁ ∉ line₀.carrier := ht₁avoid line₀ (by simp)
  obtain ⟨c₂, hc₂old, hc₂g, hc₂irr, t₂, ht₂q, hd₂, ht₂avoid⟩ :=
    hstep {line₀, line₁}
  have ht₂rat : L.IsRational t₂ := isRational_of_mem_rationalTranslate ht₂q
  have ht₂not₀ : t₂ ∉ line₀.carrier := ht₂avoid line₀ (by simp)
  have ht₂not₁ : t₂ ∉ line₁.carrier := ht₂avoid line₁ (by simp)
  have hc₀₁ : c₀ ≠ c₁ := by
    intro h
    apply ht₁not₀
    exact hline₀ t₁ ht₁rat (by simpa only [h] using hd₁)
  have hc₀₂ : c₀ ≠ c₂ := by
    intro h
    apply ht₂not₀
    exact hline₀ t₂ ht₂rat (by simpa only [h] using hd₂)
  have hc₁₂ : c₁ ≠ c₂ := by
    intro h
    apply ht₂not₁
    exact hline₁ t₂ ht₂rat (by simpa only [h] using hd₂)
  have ht₀₁ : t₀ ≠ t₁ := by
    intro h
    exact ht₁not₀ (h ▸ ht₀line)
  have ht₀₂ : t₀ ≠ t₂ := by
    intro h
    exact ht₂not₀ (h ▸ ht₀line)
  have ht₁₂ : t₁ ≠ t₂ := by
    intro h
    exact ht₂not₁ (h ▸ ht₁line)
  let center : Fin 3 → Point := ![c₀, c₁, c₂]
  let target : Fin 3 → Point := ![t₀, t₁, t₂]
  have hcenter : Function.Injective center := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact (hc₀₁ (by simpa [center] using hab)).elim
    · exact (hc₀₂ (by simpa [center] using hab)).elim
    · exact (hc₀₁ (by simpa [center] using hab.symm)).elim
    · rfl
    · exact (hc₁₂ (by simpa [center] using hab)).elim
    · exact (hc₀₂ (by simpa [center] using hab.symm)).elim
    · exact (hc₁₂ (by simpa [center] using hab.symm)).elim
    · rfl
  have htarget : Function.Injective target := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact (ht₀₁ (by simpa [target] using hab)).elim
    · exact (ht₀₂ (by simpa [target] using hab)).elim
    · exact (ht₀₁ (by simpa [target] using hab.symm)).elim
    · rfl
    · exact (ht₁₂ (by simpa [target] using hab)).elim
    · exact (ht₀₂ (by simpa [target] using hab.symm)).elim
    · exact (ht₁₂ (by simpa [target] using hab.symm)).elim
    · rfl
  rcases hd₀ with ⟨r₀, hr₀⟩
  rcases hd₁ with ⟨r₁, hr₁⟩
  rcases hd₂ with ⟨r₂, hr₂⟩
  let radius : Fin 3 → ℚ := ![r₀, r₁, r₂]
  have hc₀t₀ : c₀ ≠ t₀ := by
    intro h
    exact hc₀irr (h ▸ ht₀rat)
  have hc₁t₁ : c₁ ≠ t₁ := by
    intro h
    exact hc₁irr (h ▸ ht₁rat)
  have hc₂t₂ : c₂ ≠ t₂ := by
    intro h
    exact hc₂irr (h ▸ ht₂rat)
  have hr₀pos : 0 < (r₀ : ℝ) := by
    rw [← hr₀, distSq_eq_dist_sq]
    exact sq_pos_of_pos (dist_pos.mpr hc₀t₀)
  have hr₁pos : 0 < (r₁ : ℝ) := by
    rw [← hr₁, distSq_eq_dist_sq]
    exact sq_pos_of_pos (dist_pos.mpr hc₁t₁)
  have hr₂pos : 0 < (r₂ : ℝ) := by
    rw [← hr₂, distSq_eq_dist_sq]
    exact sq_pos_of_pos (dist_pos.mpr hc₂t₂)
  have htargetInt : ∀ a b, ∃ z : ℤ,
      distSq (target a) (target b) = (z : ℝ) := by
    intro a b
    apply exists_int_distSq_of_mem_rationalTranslate
    · fin_cases a
      · simpa [target] using ht₀q
      · simpa [target] using ht₁q
      · simpa [target] using ht₂q
    · fin_cases b
      · simpa [target] using ht₀q
      · simpa [target] using ht₁q
      · simpa [target] using ht₂q
  let targetSq : Fin 3 → Fin 3 → ℤ :=
    fun a b ↦ Classical.choose (htargetInt a b)
  have htargetSq : ∀ a b,
      distSq (target a) (target b) = (targetSq a b : ℝ) :=
    fun a b ↦ Classical.choose_spec (htargetInt a b)
  let d : CircleDatum := ⟨radius, targetSq⟩
  have hpositive : ∀ a, 0 < (d.radiusSq a : ℝ) := by
    intro a
    fin_cases a <;> assumption
  have hcenterOld : ∀ a, center a ∈ old := by
    intro a
    fin_cases a <;> assumption
  have hfinite : (circleConfigurations d center).Finite :=
    circleConfigurations_finite circle d center target hcenter htarget
      hpositive htargetSq hOld hcenterOld
  have htargetConfig : target ∈ circleConfigurations d center := by
    constructor
    · intro a
      fin_cases a
      · simpa [d, radius, center, target] using hr₀
      · simpa [d, radius, center, target] using hr₁
      · simpa [d, radius, center, target] using hr₂
    · exact htargetSq
  have htargetCode : target ∈
      Code.finiteCode (circleConfigurations d center) :=
    (Code.mem_finiteCode_iff hfinite target).2 htargetConfig
  have hcodeBefore : Code.configurations
      (Code.finiteCode (circleConfigurations d center)) ∈ D.before i := by
    simpa only [center] using
      circleCode_mem_before D hg d c₀ c₁ c₂ hc₀g hc₁g hc₂g
  have hclassBefore := class_mem_before_of_configurationCode D
    (Code.finiteCode (circleConfigurations d center)) hcodeBefore htargetCode
    (by simpa [target] using ht₀₁)
    (by simpa [target] using ht₀rat)
    (by simpa [target] using ht₁rat)
  exact (not_mem_before_of_mem_layer D hclass) hclassBefore

/-- The finite family of predecessor guards upgrades the preceding
guardwise conclusion to all old points coded below the current Davies
layer. -/
theorem finite_forbiddenLines
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index} {L : OrientedFrame} {old : Set Point}
    (hOld : IsPartialSteinhaus old)
    (hbefore : ∀ x ∈ old, Code.point x ∈ D.before i)
    (hclass : Code.latticeClass (OrientedFrame.classOf L) ∈ D.layer i)
    (q : RatPoint) :
    ∃ G : Finset (FramedLine L),
      ∀ x ∈ old, ¬L.IsRational x →
        ∀ y ∈ L.rationalTranslate q, HasRationalSqDist x y →
          ∃ line ∈ G, y ∈ line.carrier := by
  classical
  let cover : (g : {g // g ∈ D.guards i}) → Finset (FramedLine L) :=
    fun g ↦ Classical.choose
      (finite_forbiddenLines_in_guard D circle g.2 hOld hclass q)
  have cover_spec (g : {g // g ∈ D.guards i}) :
      ∀ x ∈ old, Code.point x ∈ g.1 → ¬L.IsRational x →
        ∀ y ∈ L.rationalTranslate q, HasRationalSqDist x y →
          ∃ line ∈ cover g, y ∈ line.carrier :=
    Classical.choose_spec
      (finite_forbiddenLines_in_guard D circle g.2 hOld hclass q)
  let G : Finset (FramedLine L) := (D.guards i).attach.biUnion cover
  refine ⟨G, ?_⟩
  intro x hxold hxirr y hyq hxy
  obtain ⟨g, hg, hxg⟩ := D.exists_guard_of_mem_before (hbefore x hxold)
  obtain ⟨line, hline, hyline⟩ :=
    cover_spec ⟨g, hg⟩ x hxold hxg hxirr y hyq hxy
  refine ⟨line, ?_, hyline⟩
  apply Finset.mem_biUnion.2
  exact ⟨⟨g, hg⟩, by simp, hline⟩

/-! ### The globally scheduled candidate sequence inside one terminal layer -/

/-- The finite outer-old obstruction attached to one scheduled residue
requirement. -/
noncomputable def outerForbiddenLines
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index} {A : TerminalLayer} {old : Set Point}
    (hOld : IsPartialSteinhaus old)
    (hbefore : ∀ x ∈ old, Code.point x ∈ D.before i)
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (req : ScheduledRequirement A) :
    Finset (FramedLine (A.frame req.index)) :=
  Classical.choose (finite_forbiddenLines D circle hOld hbefore
    (hclass req.index req.active) req.residue.translate)

theorem outerForbiddenLines_spec
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index} {A : TerminalLayer} {old : Set Point}
    (hOld : IsPartialSteinhaus old)
    (hbefore : ∀ x ∈ old, Code.point x ∈ D.before i)
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (req : ScheduledRequirement A) :
    ∀ x ∈ old, ¬(A.frame req.index).IsRational x →
      ∀ y ∈ (A.frame req.index).rationalTranslate req.residue.translate,
        HasRationalSqDist x y →
        ∃ line ∈ outerForbiddenLines D circle hOld hbefore hclass req,
          y ∈ line.carrier :=
  Classical.choose_spec (finite_forbiddenLines D circle hOld hbefore
    (hclass req.index req.active) req.residue.translate)

/-- At rank `r`, delete both the outer-old obstruction and the one rational
distance line contributed by each earlier candidate. -/
noncomputable def candidateLines {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    (r : ℕ) (previous : Fin r → Point) :
    Finset (FramedLine (A.frame (ScheduledRequirement.scheduled default r).index)) := by
  classical
  let req := ScheduledRequirement.scheduled default r
  exact outer req ∪ Finset.univ.image
    (fun k ↦ rationalDistanceLine (A.frame req.index) (previous k))

/-- The finitely many possible common rational points with earlier active
frame classes.  Removing them resolves the reverse-rank case in the
diagonal candidate construction. -/
def earlierCross (A : TerminalLayer) (req : ScheduledRequirement A) : Set Point :=
  {x | ∃ m < req.index, m ∈ A.active ∧
    (A.frame req.index).IsRational x ∧ (A.frame m).IsRational x}

theorem rational_intersection_subsingleton {A : TerminalLayer}
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    {m n : ℕ} (hm : m ∈ A.active) (hn : n ∈ A.active) (hmn : m ≠ n) :
    {x | (A.frame n).IsRational x ∧
      (A.frame m).IsRational x}.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have heq := OrientedFrame.class_eq_of_two_common hxy
    hx.1 hx.2 hy.1 hy.2
  exact hmn (hclassInj hm hn heq.symm)

theorem earlierCross_finite {A : TerminalLayer}
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (req : ScheduledRequirement A) : (earlierCross A req).Finite := by
  classical
  let cross : Fin req.index → Set Point := fun m ↦
    if hm : (m : ℕ) ∈ A.active then
      {x | (A.frame req.index).IsRational x ∧
        (A.frame m).IsRational x}
    else ∅
  have hcross : ∀ m, (cross m).Finite := by
    intro m
    by_cases hm : (m : ℕ) ∈ A.active
    · rw [show cross m = {x | (A.frame req.index).IsRational x ∧
          (A.frame m).IsRational x} by simp [cross, hm]]
      exact (rational_intersection_subsingleton hclassInj hm req.active
        (Nat.ne_of_lt m.2)).finite
    · simp [cross, hm]
  apply (Set.finite_iUnion hcross).subset
  intro x hx
  rcases hx with ⟨m, hmn, hm, hxn, hxm⟩
  apply mem_iUnion.2
  exact ⟨⟨m, hmn⟩, by simp [cross, hm, hxn, hxm]⟩

/-- The infinite set from which rank `r` is chosen. -/
def candidateAvailable {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    (i : D.Index) (r : ℕ) (previous : Fin r → Point) : Set Point :=
  let req := ScheduledRequirement.scheduled default r
  {x | x ∈ FramedResidueSet (A.frame req.index)
      req.residue.d req.residue.i req.residue.j
      req.residue.a req.residue.b ∧
    Code.point x ∈ D.layer i ∧
    (∀ line ∈ candidateLines default outer r previous,
      x ∉ line.carrier) ∧
    x ∉ earlierCross A req ∧
    ∀ k, x ≠ previous k}

theorem candidateAvailable_nonempty {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (r : ℕ) (previous : Fin r → Point) :
    (candidateAvailable D default outer i r previous).Nonempty := by
  classical
  let req := ScheduledRequirement.scheduled default r
  let G := candidateLines default outer r previous
  have hinfinite := layerAvoidPool_rich D
    (hclass req.index req.active) G
      req.residue.d req.residue.hd req.residue.i req.residue.j
      req.residue.a req.residue.b
  let previousSet : Set Point := ↑(Finset.univ.image previous)
  have hpreviousSet : previousSet.Finite := Finset.finite_toSet _
  have hremove : (earlierCross A req ∪ previousSet).Finite :=
    (earlierCross_finite hclassInj req).union hpreviousSet
  obtain ⟨x, hx, hxremove⟩ := hinfinite.exists_notMem_finite hremove
  refine ⟨x, ?_⟩
  change x ∈ FramedResidueSet (A.frame req.index)
      req.residue.d req.residue.i req.residue.j
      req.residue.a req.residue.b ∧
    Code.point x ∈ D.layer i ∧
    (∀ line ∈ G, x ∉ line.carrier) ∧
    x ∉ earlierCross A req ∧ ∀ k, x ≠ previous k
  rcases hx with ⟨k, l, heq, hka, hlb, hlayer, hlines⟩
  refine ⟨⟨k, l, heq, hka, hlb⟩, hlayer, hlines, ?_, ?_⟩
  · exact fun hx ↦ hxremove (Or.inl hx)
  intro k hk
  apply hxremove
  apply Or.inr
  apply Finset.mem_image.2
  exact ⟨k, by simp, hk.symm⟩

/-- The precomputed candidate sequence.  Each rank avoids every earlier
point and, when that point is irrational in the current frame, its entire
rational-distance line. -/
noncomputable def candidatePoint {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (r : ℕ) : Point :=
  recursiveChoice (candidateAvailable D default outer i)
    (candidateAvailable_nonempty D default outer hclass hclassInj) r

theorem candidatePoint_spec {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (r : ℕ) :
    candidatePoint D default outer hclass hclassInj r ∈
      candidateAvailable D default outer i r
        (fun k ↦ candidatePoint D default outer hclass hclassInj k.1) := by
  exact recursiveChoice_spec (candidateAvailable D default outer i)
    (candidateAvailable_nonempty D default outer hclass hclassInj) r

theorem candidatePoint_properties {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (r : ℕ) :
    let req := ScheduledRequirement.scheduled default r
    let p := candidatePoint D default outer hclass hclassInj r
    p ∈ FramedResidueSet (A.frame req.index)
        req.residue.d req.residue.i req.residue.j
        req.residue.a req.residue.b ∧
      Code.point p ∈ D.layer i ∧
      (∀ line ∈ candidateLines default outer r
        (fun k ↦ candidatePoint D default outer hclass hclassInj k.1),
        p ∉ line.carrier) ∧
      p ∉ earlierCross A req ∧
      ∀ k : Fin r, p ≠ candidatePoint D default outer hclass hclassInj k.1 := by
  simpa only [candidateAvailable, Set.mem_setOf_eq] using
    candidatePoint_spec D default outer hclass hclassInj r

theorem candidatePoint_ne_of_lt {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    {r s : ℕ} (hrs : r < s) :
    candidatePoint D default outer hclass hclassInj s ≠
      candidatePoint D default outer hclass hclassInj r :=
  (candidatePoint_properties D default outer hclass hclassInj s).2.2.2.2
    ⟨r, hrs⟩

theorem candidatePoint_injective {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active) :
    Function.Injective (candidatePoint D default outer hclass hclassInj) := by
  intro r s hrs
  rcases lt_trichotomy r s with hlt | heq | hgt
  · exact (candidatePoint_ne_of_lt D default outer hclass hclassInj hlt
      hrs.symm).elim
  · exact heq
  · exact (candidatePoint_ne_of_lt D default outer hclass hclassInj hgt
      hrs).elim

/-- Candidates born for the active frame `n`. -/
def candidateSource {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (n : ℕ) : Set Point :=
  {x | ∃ r, (ScheduledRequirement.scheduled default r).index = n ∧
    candidatePoint D default outer hclass hclassInj r = x}

theorem candidateSource_located {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    {n : ℕ} {x : Point}
    (hx : x ∈ candidateSource D default outer hclass hclassInj n) :
    Code.point x ∈ D.layer i := by
  rcases hx with ⟨r, -, rfl⟩
  exact (candidatePoint_properties D default outer hclass hclassInj r).2.1

theorem candidateSource_rational {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    {n : ℕ} {x : Point}
    (hx : x ∈ candidateSource D default outer hclass hclassInj n) :
    (A.frame n).IsRational x := by
  rcases hx with ⟨r, hrn, rfl⟩
  let req := ScheduledRequirement.scheduled default r
  have hres := (candidatePoint_properties D default outer hclass hclassInj r).1
  have hq := ResidueRequirement.mem_rationalTranslate hres
  have hrat := isRational_of_mem_rationalTranslate hq
  simpa only [req, hrn] using hrat

theorem candidateSource_rich {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    {n : ℕ} (hn : n ∈ A.active) :
    FrameRich (A.frame n)
      (candidateSource D default outer hclass hclassInj n) := by
  intro d hd ri rj a b
  let residue : ResidueRequirement := ⟨d, hd, ri, rj, a, b⟩
  let req : ScheduledRequirement A := ⟨n, hn, residue⟩
  let code := @Encodable.encode (ScheduledRequirement A)
    ScheduledRequirement.encodable req
  let rank : ℕ → ℕ := fun k ↦ Nat.pair code k
  let f : ℕ → Point := fun k ↦
    candidatePoint D default outer hclass hclassInj (rank k)
  have hrank : Function.Injective rank := by
    intro k l hkl
    have h := congrArg (fun z ↦ (Nat.unpair z).2) hkl
    simpa only [rank, Nat.unpair_pair] using h
  have hf : Function.Injective f :=
    (candidatePoint_injective D default outer hclass hclassInj).comp hrank
  apply (Set.infinite_range_of_injective hf).mono
  intro x hx
  rcases hx with ⟨k, rfl⟩
  have hschedule : ScheduledRequirement.scheduled default (rank k) = req := by
    exact ScheduledRequirement.scheduled_pair default req k
  have hp := (candidatePoint_properties D default outer hclass hclassInj (rank k)).1
  rw [hschedule] at hp
  rcases hp with ⟨u, v, heq, hua, hvb⟩
  refine ⟨u, v, ?_, hua, hvb, ?_⟩
  · simpa only [req, residue] using heq
  · refine ⟨rank k, ?_, rfl⟩
    simpa only [hschedule, req]

theorem candidatePoint_rational {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (r : ℕ) :
    let req := ScheduledRequirement.scheduled default r
    (A.frame req.index).IsRational
      (candidatePoint D default outer hclass hclassInj r) := by
  let req := ScheduledRequirement.scheduled default r
  have hres := (candidatePoint_properties D default outer hclass hclassInj r).1
  exact isRational_of_mem_rationalTranslate
    (ResidueRequirement.mem_rationalTranslate hres)

/-- Forward-rank half of the diagonal construction: rational squared
distance from an earlier candidate forces that earlier point to be rational
in the later candidate's scheduled frame. -/
theorem earlierCandidate_rational_of_rationalSqDist {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    {r s : ℕ} (hrs : r < s)
    (hdist : HasRationalSqDist
      (candidatePoint D default outer hclass hclassInj r)
      (candidatePoint D default outer hclass hclassInj s)) :
    let req := ScheduledRequirement.scheduled default s
    (A.frame req.index).IsRational
      (candidatePoint D default outer hclass hclassInj r) := by
  classical
  let req := ScheduledRequirement.scheduled default s
  let pr := candidatePoint D default outer hclass hclassInj r
  let ps := candidatePoint D default outer hclass hclassInj s
  by_contra hpr
  have hps : (A.frame req.index).IsRational ps :=
    candidatePoint_rational D default outer hclass hclassInj s
  have hline : ps ∈ (rationalDistanceLine (A.frame req.index) pr).carrier :=
    mem_rationalDistanceLine hpr hps hdist
  have havoid :=
    (candidatePoint_properties D default outer hclass hclassInj s).2.2.1
  apply havoid (rationalDistanceLine (A.frame req.index) pr)
  · apply Finset.mem_union_right
    apply Finset.mem_image.2
    exact ⟨⟨r, hrs⟩, by simp [req, pr]⟩
  · exact hline

/-- If `m < n`, rational squared distance between the two scheduled source
sets forces the older-source point to be rational in frame `n`.  In the
reverse rank order, the later-source point was explicitly removed by
`earlierCross`. -/
theorem sourcePoint_rational_of_rationalSqDist {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    {m n : ℕ} (hmn : m < n) {x y : Point}
    (hx : x ∈ candidateSource D default outer hclass hclassInj m)
    (hy : y ∈ candidateSource D default outer hclass hclassInj n)
    (hdist : HasRationalSqDist x y) :
    (A.frame n).IsRational x := by
  rcases hx with ⟨r, hrm, rfl⟩
  rcases hy with ⟨s, hsn, rfl⟩
  rcases lt_trichotomy r s with hrs | hrs | hsr
  · have h := earlierCandidate_rational_of_rationalSqDist D default outer
      hclass hclassInj hrs hdist
    simpa only [hsn] using h
  · subst s
    exact (Nat.ne_of_lt hmn (hrm.symm.trans hsn)).elim
  · exfalso
    have hyratM := earlierCandidate_rational_of_rationalSqDist D default outer
      hclass hclassInj hsr (by
        simpa only [HasRationalSqDist, distSq_comm] using hdist)
    have hyratN := candidatePoint_rational D default outer hclass hclassInj s
    have hnot :=
      (candidatePoint_properties D default outer hclass hclassInj s).2.2.2.1
    apply hnot
    refine ⟨(ScheduledRequirement.scheduled default r).index, ?_,
      (ScheduledRequirement.scheduled default r).active, hyratN, hyratM⟩
    simpa only [hrm, hsn] using hmn

/-- The outer forbidden-line theorem supplies the other half of (I5): a
candidate at source `n` can have rational squared distance from an outer-old
point only when that old point is itself rational in frame `n`. -/
theorem oldPoint_rational_of_rationalSqDist
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index} {A : TerminalLayer} {old : Set Point}
    (hOld : IsPartialSteinhaus old)
    (hbefore : ∀ x ∈ old, Code.point x ∈ D.before i)
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (default : ScheduledRequirement A)
    {n : ℕ} {x y : Point} (hx : x ∈ old)
    (hy : y ∈ candidateSource D default
      (outerForbiddenLines D circle hOld hbefore hclass)
      hclass hclassInj n)
    (hdist : HasRationalSqDist x y) :
    (A.frame n).IsRational x := by
  classical
  rcases hy with ⟨r, hrn, rfl⟩
  let req := ScheduledRequirement.scheduled default r
  by_contra hxirr
  have hxirr' : ¬(A.frame req.index).IsRational x := by
    simpa only [req, hrn] using hxirr
  have hp := candidatePoint_properties D default
    (outerForbiddenLines D circle hOld hbefore hclass)
    hclass hclassInj r
  have hyq := ResidueRequirement.mem_rationalTranslate hp.1
  obtain ⟨line, hlineOuter, hyline⟩ :=
    outerForbiddenLines_spec D circle hOld hbefore hclass req
      x hx hxirr'
      (candidatePoint D default
        (outerForbiddenLines D circle hOld hbefore hclass)
        hclass hclassInj r) hyq hdist
  have hlineAll : line ∈ candidateLines default
      (outerForbiddenLines D circle hOld hbefore hclass) r
      (fun k ↦ candidatePoint D default
        (outerForbiddenLines D circle hOld hbefore hclass)
        hclass hclassInj k.1) := by
    apply Finset.mem_union_left
    exact hlineOuter
  exact hp.2.2.1 line hlineAll hyline

end CodedDavies

/-- Rational-rotation transfer, exactly in the form needed after applying a
rich selector in one representative frame. -/
def RationalRotationTransferTheorem : Prop :=
  ∀ (S : Set Point) (L : OrientedFrame),
    IsPartialSteinhaus S → HitsRationalTranslates S L → HitsRationalClass S L

theorem rationalRotationTransfer : RationalRotationTransferTheorem := by
  intro S L hpartial hhits
  exact Erdos215.RationalRotationTransferTheorem S L hpartial hhits

lemma hitsRationalClass_mono {S T : Set Point} (hST : S ⊆ T)
    {L : OrientedFrame} (hS : HitsRationalClass S L) : HitsRationalClass T L := by
  intro K hKL
  obtain ⟨p, hpS, hpK⟩ := hS K hKL
  exact ⟨p, hST hpS, hpK⟩

/-- A rational squared distance.  This is the antecedent of invariant (I5),
not the stronger integral-distance conflict used by partiality. -/
def RationalSqDist (x y : Point) : Prop :=
  ∃ q : ℚ, distSq x y = (q : ℝ)

/-- The explanation demanded by (I5): both endpoints have rational
coordinates in a class processed at the current terminal layer. -/
def TerminalLayer.Explains (A : TerminalLayer) (x y : Point) : Prop :=
  ∃ n ∈ A.active, (A.frame n).IsRational x ∧ (A.frame n).IsRational y

/-- The finite inner state after processing the indices `< n` of one
terminal layer.  Unlike an arbitrary partial set, this state remembers (I3)
and (I5), so the known finite nonextendible examples cannot instantiate it. -/
structure TerminalState (A : TerminalLayer) (old : Set Point)
    (Located : Point → Prop) (Source : ℕ → Set Point) (n : ℕ) where
  selected : Set Point
  old_subset : old ⊆ selected
  isPartial : IsPartialSteinhaus selected
  hits_before : ∀ k < n, k ∈ A.active → HitsRationalClass selected (A.frame k)
  located_new : ∀ x ∈ selected, x ∉ old → Located x
  new_source : ∀ x ∈ selected, x ∉ old →
    ∃ k < n, k ∈ A.active ∧ x ∈ Source k
  explains_old_new : ∀ x ∈ old, ∀ y ∈ selected, y ∉ old →
    RationalSqDist x y → A.Explains x y

/-- A candidate pool with exactly the two additional conclusions obtained
from the Davies localization and forbidden-line arguments. -/
structure LocalizedCandidatePool (A : TerminalLayer) (old current : Set Point)
    (Located : Point → Prop) (Source : ℕ → Set Point) (n : ℕ)
    extends CandidatePool current (A.frame n) where
  located_fresh : ∀ y ∈ pool, y ∉ current → Located y
  fresh_source : ∀ y ∈ pool, y ∉ current → y ∈ Source n
  explains_fresh : ∀ x ∈ old, ∀ y ∈ pool, y ∉ current →
    RationalSqDist x y → A.Explains x y

namespace TerminalState

variable {A : TerminalLayer} {old : Set Point} {Located : Point → Prop}
    {Source : ℕ → Set Point}

def initial (hOld : IsPartialSteinhaus old) : TerminalState A old Located Source 0 where
  selected := old
  old_subset := Subset.rfl
  isPartial := hOld
  hits_before := by simp
  located_new := by
    intro x hx hnx
    exact (hnx hx).elim
  new_source := by
    intro x hx hnx
    exact (hnx hx).elim
  explains_old_new := by
    intro x hx y hy hny
    exact (hny hy).elim

/-- One active step of the terminal recursion.  The only imported arithmetic
fact is the rich-selector theorem; all old--new safety is visible in `C`. -/
noncomputable def activeStep (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem) (n : ℕ)
    (s : TerminalState A old Located Source n)
    (hn : n ∈ A.active)
    (C : LocalizedCandidatePool A old s.selected Located Source n) :
    TerminalState A old Located Source (n + 1) := by
  let witness := extendByCandidatePool selector s.isPartial (A.frame n) C.toCandidatePool
  let T : Set Point := Classical.choose witness
  have hT := Classical.choose_spec witness
  refine
    { selected := s.selected ∪ T
      old_subset := s.old_subset.trans subset_union_left
      isPartial := hT.2.1
      hits_before := ?_
      located_new := ?_
      new_source := ?_
      explains_old_new := ?_ }
  · intro k hk hkactive
    rcases Nat.lt_succ_iff_lt_or_eq.mp (by simpa using hk) with hkn | hkn
    · exact hitsRationalClass_mono subset_union_left
        (s.hits_before k hkn hkactive)
    · subst k
      exact hitsRationalClass_mono subset_union_right
        (transfer T (A.frame n)
          (fun x hx y hy hxy z ↦ hT.2.1 (Or.inr hx) (Or.inr hy) hxy z)
          hT.2.2)
  · intro x hx hxold
    rcases hx with hx | hx
    · exact s.located_new x hx hxold
    · by_cases hcurrent : x ∈ s.selected
      · exact s.located_new x hcurrent hxold
      · exact C.located_fresh x (hT.1 hx) hcurrent
  · intro x hx hxold
    rcases hx with hx | hx
    · obtain ⟨k, hk, hka, hsrc⟩ := s.new_source x hx hxold
      exact ⟨k, hk.trans (Nat.lt_succ_self n), hka, hsrc⟩
    · by_cases hcurrent : x ∈ s.selected
      · obtain ⟨k, hk, hka, hsrc⟩ := s.new_source x hcurrent hxold
        exact ⟨k, hk.trans (Nat.lt_succ_self n), hka, hsrc⟩
      · exact ⟨n, Nat.lt_succ_self n, hn, C.fresh_source x (hT.1 hx) hcurrent⟩
  · intro x hxold y hy hyold hr
    rcases hy with hy | hy
    · exact s.explains_old_new x hxold y hy hyold hr
    · by_cases hcurrent : y ∈ s.selected
      · exact s.explains_old_new x hxold y hcurrent hyold hr
      · exact C.explains_fresh x hxold y (hT.1 hy) hcurrent hr

def inactiveStep (n : ℕ) (s : TerminalState A old Located Source n)
    (hn : n ∉ A.active) :
    TerminalState A old Located Source (n + 1) where
  selected := s.selected
  old_subset := s.old_subset
  isPartial := s.isPartial
  hits_before := by
    intro k hk hkactive
    have hkn : k < n := by
      have hle : k ≤ n := Nat.le_of_lt_succ (by simpa using hk)
      exact hle.lt_of_ne (fun h ↦ by subst k; exact hn hkactive)
    exact s.hits_before k hkn hkactive
  located_new := s.located_new
  new_source := fun x hx hxold ↦ by
    obtain ⟨k, hk, hka, hsrc⟩ := s.new_source x hx hxold
    exact ⟨k, hk.trans (Nat.lt_succ_self n), hka, hsrc⟩
  explains_old_new := s.explains_old_new

/-- The exact pool-building obligation at an inner stage.  Its domain is a
state carrying the construction invariants, rather than an arbitrary partial
set.  The finite-forbidden-line proof supplies this obligation from the
three-circle theorem and Davies guards. -/
def PoolStepAvailable (A : TerminalLayer) (old : Set Point)
    (Located : Point → Prop) (Source : ℕ → Set Point) : Prop :=
  ∀ (n : ℕ) (s : TerminalState A old Located Source n), n ∈ A.active →
    Nonempty (LocalizedCandidatePool A old s.selected Located Source n)

/-- The actual natural-number recursion through a countable terminal layer. -/
noncomputable def run (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) :
    (n : ℕ) → TerminalState A old Located Source n := by
  classical
  intro n
  induction n with
  | zero => exact initial hOld
  | succ n s =>
      by_cases hn : n ∈ A.active
      · exact activeStep selector transfer n s hn
          (Classical.choice (pools n s hn))
      · exact inactiveStep n s hn

theorem run_selected_mono_succ (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) (n : ℕ) :
    (run selector transfer hOld pools n).selected ⊆
      (run selector transfer hOld pools (n + 1)).selected := by
  by_cases hn : n ∈ A.active
  · intro x hx
    simp only [run, dif_pos hn, activeStep]
    exact Or.inl hx
  · intro x hx
    simpa only [run, dif_neg hn, inactiveStep] using hx

theorem run_selected_mono (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) {n m : ℕ} (hnm : n ≤ m) :
    (run selector transfer hOld pools n).selected ⊆
      (run selector transfer hOld pools m).selected := by
  induction m, hnm using Nat.le_induction with
  | base => exact Subset.rfl
  | succ m hnm ih =>
      exact ih.trans (run_selected_mono_succ selector transfer hOld pools m)

/-- The union of all finite inner states. -/
def runResult (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) : Set Point :=
  ⋃ n, (run selector transfer hOld pools n).selected

theorem runResult_partial (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) :
    IsPartialSteinhaus (runResult selector transfer hOld pools) := by
  intro x hx y hy hxy z
  rcases mem_iUnion.1 hx with ⟨n, hxn⟩
  rcases mem_iUnion.1 hy with ⟨m, hym⟩
  let k := max n m
  exact (run selector transfer hOld pools k).isPartial
    (run_selected_mono selector transfer hOld pools (Nat.le_max_left n m) hxn)
    (run_selected_mono selector transfer hOld pools (Nat.le_max_right n m) hym)
    hxy z

theorem runResult_old_subset (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) :
    old ⊆ runResult selector transfer hOld pools := by
  intro x hx
  exact mem_iUnion.2 ⟨0, (run selector transfer hOld pools 0).old_subset hx⟩

theorem runResult_hits (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) :
    A.Hits (runResult selector transfer hOld pools) := by
  intro n hn K hK
  have hh := (run selector transfer hOld pools (n + 1)).hits_before
    n (Nat.lt_succ_self n) hn K hK
  obtain ⟨p, hp, hpK⟩ := hh
  exact ⟨p, mem_iUnion.2 ⟨n + 1, hp⟩, hpK⟩

theorem runResult_located_new (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) :
    ∀ x ∈ runResult selector transfer hOld pools, x ∉ old → Located x := by
  intro x hx hxold
  rcases mem_iUnion.1 hx with ⟨n, hxn⟩
  exact (run selector transfer hOld pools n).located_new x hxn hxold

theorem runResult_new_source (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) :
    ∀ x ∈ runResult selector transfer hOld pools, x ∉ old →
      ∃ k, k ∈ A.active ∧ x ∈ Source k := by
  intro x hx hxold
  rcases mem_iUnion.1 hx with ⟨n, hxn⟩
  obtain ⟨k, -, hka, hsrc⟩ :=
    (run selector transfer hOld pools n).new_source x hxn hxold
  exact ⟨k, hka, hsrc⟩

theorem runResult_explains_old_new (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) :
    ∀ x ∈ old, ∀ y ∈ runResult selector transfer hOld pools, y ∉ old →
      RationalSqDist x y → A.Explains x y := by
  intro x hx y hy hyold hr
  rcases mem_iUnion.1 hy with ⟨n, hyn⟩
  exact (run selector transfer hOld pools n).explains_old_new x hx y hyn hyold hr

end TerminalState

/-! ### Concrete terminal pool availability -/

/-- The precise one-cross invariant consumed by the terminal pool
constructor.  `GlobalOneCross.lean` derives it from the outer birth-block
invariants and Davies closure. -/
def TerminalLayer.OneCross (A : TerminalLayer) (old : Set Point)
    (Source : ℕ → Set Point) : Prop :=
  ∀ n ∈ A.active,
    {x | (x ∈ old ∨ ∃ m < n, m ∈ A.active ∧ x ∈ Source m) ∧
      (A.frame n).IsRational x}.Subsingleton

/-- Output of one complete countable terminal-layer recursion. -/
structure TerminalStageCertificate (A : TerminalLayer) (old : Set Point)
    (Located : Point → Prop) (Source : ℕ → Set Point) where
  selected : Set Point
  old_subset : old ⊆ selected
  isPartial : IsPartialSteinhaus selected
  hits : A.Hits selected
  located_new : ∀ x ∈ selected, x ∉ old → Located x
  new_source : ∀ x ∈ selected, x ∉ old →
    ∃ n ∈ A.active, x ∈ Source n
  explains_old_new : ∀ x ∈ old, ∀ y ∈ selected, y ∉ old →
    RationalSqDist x y → A.Explains x y

/-- Choose the unique point of a subsingleton set when it is inhabited. -/
noncomputable def optionalPoint (R : Set Point) : Option Point :=
  by
    classical
    exact if hR : R.Nonempty then some (Classical.choose hR) else none

theorem optionalPoint_mem {R : Set Point} {x : Point}
    (hx : optionalPoint R = some x) : x ∈ R := by
  classical
  rw [optionalPoint] at hx
  split at hx
  next hR =>
    injection hx with h
    simpa only [← h] using Classical.choose_spec hR
  next => simp at hx

theorem optionalPoint_eq_some {R : Set Point} (hR : R.Subsingleton)
    {x : Point} (hx : x ∈ R) : optionalPoint R = some x := by
  classical
  rw [optionalPoint, dif_pos ⟨x, hx⟩]
  congr
  exact hR (Classical.choose_spec ⟨x, hx⟩) hx

namespace CodedDavies

variable (D : DaviesDecomposition Code.skolem)

/-- The concrete forbidden-line/candidate-sequence construction discharges
the entire inner `PoolStepAvailable` obligation once the exact outer
one-cross invariant is supplied. -/
theorem poolStepAvailable
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index} {A : TerminalLayer} {old : Set Point}
    (hOld : IsPartialSteinhaus old)
    (hbefore : ∀ x ∈ old, Code.point x ∈ D.before i)
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (default : ScheduledRequirement A)
    (hone : A.OneCross old
      (candidateSource D default
        (outerForbiddenLines D circle hOld hbefore hclass)
        hclass hclassInj)) :
    TerminalState.PoolStepAvailable A old
      (fun x ↦ Code.point x ∈ D.layer i)
      (candidateSource D default
        (outerForbiddenLines D circle hOld hbefore hclass)
        hclass hclassInj) := by
  classical
  let outer := outerForbiddenLines D circle hOld hbefore hclass
  let Source := candidateSource D default outer hclass hclassInj
  intro n s hn
  let R : Set Point :=
    {x | x ∈ s.selected ∧ (A.frame n).IsRational x}
  have hR : R.Subsingleton := by
    intro x hx y hy
    apply hone n hn
    · refine ⟨?_, hx.2⟩
      by_cases hxold : x ∈ old
      · exact Or.inl hxold
      · obtain ⟨m, hmn, hm, hxm⟩ := s.new_source x hx.1 hxold
        exact Or.inr ⟨m, hmn, hm, hxm⟩
    · refine ⟨?_, hy.2⟩
      by_cases hyold : y ∈ old
      · exact Or.inl hyold
      · obtain ⟨m, hmn, hm, hym⟩ := s.new_source y hy.1 hyold
        exact Or.inr ⟨m, hmn, hm, hym⟩
  let w := optionalPoint R
  let P : Set Point := Source n ∪ {x | w = some x}
  refine ⟨{
    pool := P
    distinguished := w
    rich := ?_
    rational := ?_
    distinguished_mem := ?_
    old_safe := ?_
    located_fresh := ?_
    fresh_source := ?_
    explains_fresh := ?_ }⟩
  · intro d hd ri rj a b
    apply (candidateSource_rich D default outer hclass hclassInj hn
      d hd ri rj a b).mono
    intro x hx
    rcases hx with ⟨k, l, heq, hka, hlb, hsource⟩
    exact ⟨k, l, heq, hka, hlb, Or.inl hsource⟩
  · intro x hx
    rcases hx with hx | hx
    · exact candidateSource_rational D default outer hclass hclassInj hx
    · exact (optionalPoint_mem hx).2
  · intro x hx
    have hxR := optionalPoint_mem hx
    exact ⟨hxR.1, Or.inr hx⟩
  · intro x hx y hy hnot hxy z hdist
    have hratdist : HasRationalSqDist x y := by
      refine ⟨(z : ℚ), ?_⟩
      exact_mod_cast hdist
    rcases hy with hysource | hyv
    · have hxrat : (A.frame n).IsRational x := by
        by_cases hxold : x ∈ old
        · exact oldPoint_rational_of_rationalSqDist D circle hOld hbefore
            hclass hclassInj default hxold hysource hratdist
        · obtain ⟨m, hmn, hm, hxm⟩ := s.new_source x hx hxold
          exact sourcePoint_rational_of_rationalSqDist D default outer
            hclass hclassInj hmn hxm hysource hratdist
      exact hnot (optionalPoint_eq_some hR ⟨hx, hxrat⟩)
    · have hyR := optionalPoint_mem hyv
      exact s.isPartial hx hyR.1 hxy z hdist
  · intro y hy hycurrent
    rcases hy with hysource | hyv
    · exact candidateSource_located D default outer hclass hclassInj hysource
    · exact (hycurrent (optionalPoint_mem hyv).1).elim
  · intro y hy hycurrent
    rcases hy with hysource | hyv
    · exact hysource
    · exact (hycurrent (optionalPoint_mem hyv).1).elim
  · intro x hxold y hy hycurrent hdist
    rcases hy with hysource | hyv
    · refine ⟨n, hn, ?_, ?_⟩
      · apply oldPoint_rational_of_rationalSqDist D circle hOld hbefore
          hclass hclassInj default hxold hysource
        simpa only [RationalSqDist, HasRationalSqDist] using hdist
      · exact candidateSource_rational D default outer hclass hclassInj hysource
    · exact (hycurrent (optionalPoint_mem hyv).1).elim

/-- Running the verified inner recursion produces all terminal-stage
invariants needed by the outer birth-block recursion. -/
noncomputable def terminalStage
    (selector : RichSelectorTheorem)
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index} {A : TerminalLayer} {old : Set Point}
    (hOld : IsPartialSteinhaus old)
    (hbefore : ∀ x ∈ old, Code.point x ∈ D.before i)
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (default : ScheduledRequirement A)
    (hone : A.OneCross old
      (candidateSource D default
        (outerForbiddenLines D circle hOld hbefore hclass)
        hclass hclassInj)) :
    TerminalStageCertificate A old
      (fun x ↦ Code.point x ∈ D.layer i)
      (candidateSource D default
        (outerForbiddenLines D circle hOld hbefore hclass)
        hclass hclassInj) := by
  let Source := candidateSource D default
    (outerForbiddenLines D circle hOld hbefore hclass) hclass hclassInj
  let pools := poolStepAvailable D circle hOld hbefore hclass hclassInj default hone
  let S := TerminalState.runResult selector rationalRotationTransfer hOld pools
  exact {
    selected := S
    old_subset := TerminalState.runResult_old_subset
      selector rationalRotationTransfer hOld pools
    isPartial := TerminalState.runResult_partial
      selector rationalRotationTransfer hOld pools
    hits := TerminalState.runResult_hits
      selector rationalRotationTransfer hOld pools
    located_new := TerminalState.runResult_located_new
      selector rationalRotationTransfer hOld pools
    new_source := TerminalState.runResult_new_source
      selector rationalRotationTransfer hOld pools
    explains_old_new := TerminalState.runResult_explains_old_new
      selector rationalRotationTransfer hOld pools }

end CodedDavies

/-- A verified family of newly-added blocks indexed by terminal stages.
These are precisely the global invariants (I2)--(I5), expressed using birth
blocks rather than nested cumulative sets. -/
structure BlockFamily (I : Type) (lt : I → I → Prop)
    (layer : I → TerminalLayer) where
  block : I → Set Point
  block_partial : ∀ i, IsPartialSteinhaus (block i)
  earlier_separated : ∀ i j, lt i j →
    ∀ x ∈ block i, ∀ y ∈ block j, Separated x y
  hits_up_to : ∀ i, (layer i).Hits
    ({x | ∃ j, lt j i ∧ x ∈ block j} ∪ block i)
  located : I → Point → Prop
  first_added_located : ∀ i x, x ∈ block i → located i x
  old_new_explained : ∀ i j, lt i j →
    ∀ x ∈ block i, ∀ y ∈ block j,
      RationalSqDist x y → (layer j).Explains x y

namespace BlockFamily

variable {I : Type} {r : I → I → Prop} {layer : I → TerminalLayer}
    (B : BlockFamily I r layer)

def result : Set Point := ⋃ i, B.block i

/-- The global partial-Steinhaus conclusion.  Only total comparability of the
terminal well-order is used here; no countability assumption on its initial
segments occurs. -/
theorem result_partial (hTotal : ∀ i j, i = j ∨ r i j ∨ r j i) :
    IsPartialSteinhaus B.result := by
  intro x hx y hy hxy z
  rcases mem_iUnion.1 hx with ⟨i, hxi⟩
  rcases mem_iUnion.1 hy with ⟨j, hyj⟩
  rcases hTotal i j with rfl | hij | hji
  · exact B.block_partial i hxi hyj hxy z
  · exact B.earlier_separated i j hij x hxi y hyj hxy z
  · exact (separated_comm.mp
      (B.earlier_separated j i hji y hyj x hxi)) hxy z

theorem result_hits (i : I) : (layer i).Hits B.result := by
  intro n hn K hK
  obtain ⟨p, hp, hpK⟩ := B.hits_up_to i n hn K hK
  rcases hp with ⟨j, -, hpj⟩ | hpi
  · exact ⟨p, mem_iUnion.2 ⟨j, hpj⟩, hpK⟩
  · exact ⟨p, mem_iUnion.2 ⟨i, hpi⟩, hpK⟩

end BlockFamily

/-- Every oriented integer lattice is met. -/
def HitsAllFrames (S : Set Point) : Prop :=
  ∀ L : OrientedFrame, ∃ p : Point, p ∈ S ∧ L.IsLatticePoint p

namespace CodedDavies

variable (D : DaviesDecomposition Code.skolem)

theorem blockFamily_hitsAllFrames
    (B : BlockFamily D.Index D.lt (terminalLayer D)) :
    HitsAllFrames B.result := by
  intro K
  obtain ⟨i, n, hn, hclass⟩ := every_class_appears D (OrientedFrame.classOf K)
  have hKL : K.RationallyEquivalent ((terminalLayer D i).frame n) := by
    apply (OrientedFrame.classOf_eq_iff K ((terminalLayer D i).frame n)).1
    exact hclass.symm
  exact (B.result_hits i) n hn K hKL

end CodedDavies

end Global

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/GlobalRecursion.lean` -/

section
/-!
# The outer well-founded recursion for Erdős Problem 215

This file packages the purely order-theoretic assembly of the birth blocks
used in `Global.BlockFamily`.  A stage constructor is allowed to inspect all
strictly earlier blocks together with proofs of all invariants already
established there.  The construction uses well-founded recursion and makes
no countability assumption about initial segments of the stage order.
-/

open Set

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Global
namespace OuterRecursion

variable {I : Type} (r : I → I → Prop) [IsWellOrder I r]
    (layer : I → TerminalLayer) (Located : I → Point → Prop)

/-- The union of the blocks in a proof-indexed strict prefix. -/
def priorUnion (i : I) (prev : (j : I) → r j i → Set Point) : Set Point :=
  {x | ∃ (j : I) (hji : r j i), x ∈ prev j hji}

/-- All global invariants restricted to the strict prefix below `i`.

The proof arguments in `prev` are harmless: proof irrelevance makes the
chosen set independent of the particular proof of `r j i`.  Keeping them in
the type is what lets a `WellFounded.fix` body access exactly, and only, its
recursive predecessors. -/
structure PrefixGood (i : I) (prev : (j : I) → r j i → Set Point) : Prop where
  block_partial : ∀ j (hji : r j i), IsPartialSteinhaus (prev j hji)
  earlier_separated : ∀ j (hji : r j i) k (hki : r k i), r j k →
    ∀ x ∈ prev j hji, ∀ y ∈ prev k hki, Separated x y
  hits_up_to : ∀ j (hji : r j i), (layer j).Hits
    ({x | ∃ (k : I) (hkj : r k j),
      x ∈ prev k (IsTrans.trans k j i hkj hji)} ∪
      prev j hji)
  first_added_located : ∀ j (hji : r j i) x, x ∈ prev j hji → Located j x
  old_new_explained : ∀ j (hji : r j i) k (hki : r k i), r j k →
    ∀ x ∈ prev j hji, ∀ y ∈ prev k hki,
      RationalSqDist x y → (layer k).Explains x y

/-- The exact certificate returned by one outer stage. -/
structure StageFacts (i : I) (prev : (j : I) → r j i → Set Point)
    (newBlock : Set Point) : Prop where
  block_partial : IsPartialSteinhaus newBlock
  earlier_separated : ∀ j (hji : r j i),
    ∀ x ∈ prev j hji, ∀ y ∈ newBlock, Separated x y
  hits_up_to : (layer i).Hits (priorUnion r i prev ∪ newBlock)
  first_added_located : ∀ x, x ∈ newBlock → Located i x
  old_new_explained : ∀ j (hji : r j i),
    ∀ x ∈ prev j hji, ∀ y ∈ newBlock,
      RationalSqDist x y → (layer i).Explains x y

/-- The obligation discharged by the concrete terminal-layer construction.
It is only requested on prefixes which already carry all global invariants. -/
abbrev StageExtension : Prop :=
  ∀ (i : I) (prev : (j : I) → r j i → Set Point),
    PrefixGood r layer Located i prev →
      ∃ newBlock : Set Point, StageFacts r layer Located i prev newBlock

variable (extend : StageExtension r layer Located)

private noncomputable def nextBlock (i : I)
    (prev : (j : I) → r j i → Set Point) : Set Point := by
  classical
  exact if h : PrefixGood r layer Located i prev then
    Classical.choose (extend i prev h)
  else ∅

private theorem nextBlock_stageFacts (i : I)
    (prev : (j : I) → r j i → Set Point)
    (hgood : PrefixGood r layer Located i prev) :
    StageFacts r layer Located i prev
      (nextBlock r layer Located extend i prev) := by
  rw [nextBlock, dif_pos hgood]
  exact Classical.choose_spec (extend i prev hgood)

/-- Birth blocks selected by well-founded recursion.  The empty fallback is
never used: `blocks_prefixGood` proves inductively that the recursive prefix
always satisfies the stage constructor's premise. -/
noncomputable def blocks : I → Set Point :=
  WellFounded.fix (IsWellFounded.wf : WellFounded r) fun i rec ↦
    nextBlock r layer Located extend i rec

private theorem blocks_stageFacts_of_prefixGood (i : I)
    (hgood : PrefixGood r layer Located i
      (fun j (_ : r j i) ↦
        blocks (r := r) (layer := layer) (Located := Located) extend j)) :
    StageFacts r layer Located i
      (fun j (_ : r j i) ↦
        blocks (r := r) (layer := layer) (Located := Located) extend j)
      (blocks (r := r) (layer := layer) (Located := Located) extend i) := by
  have hunfold :
      blocks (r := r) (layer := layer) (Located := Located) extend i =
        nextBlock r layer Located extend i
          (fun j (_ : r j i) ↦
            blocks (r := r) (layer := layer) (Located := Located) extend j) := by
    unfold blocks
    rw [WellFounded.fix_eq]
  rw [hunfold]
  exact nextBlock_stageFacts r layer Located extend i _ hgood

/-- Every recursive prefix is good.  This is the induction which guarantees
that the fallback branch in `blocks` is unreachable. -/
theorem blocks_prefixGood (i : I) :
    PrefixGood r layer Located i
      (fun j (_ : r j i) ↦
        blocks (r := r) (layer := layer) (Located := Located) extend j) := by
  refine @IsWellFounded.induction I r _
    (fun i ↦ PrefixGood r layer Located i
      (fun j (_ : r j i) ↦
        blocks (r := r) (layer := layer) (Located := Located) extend j)) i ?_
  intro i ih
  let facts : ∀ j (hji : r j i),
      StageFacts r layer Located j
        (fun k (_ : r k j) ↦
          blocks (r := r) (layer := layer) (Located := Located) extend k)
        (blocks (r := r) (layer := layer) (Located := Located) extend j) :=
    fun j hji ↦
      blocks_stageFacts_of_prefixGood r layer Located extend j (ih j hji)
  refine
    { block_partial := ?_
      earlier_separated := ?_
      hits_up_to := ?_
      first_added_located := ?_
      old_new_explained := ?_ }
  · intro j hji
    exact (facts j hji).block_partial
  · intro j hji k hki hjk x hx y hy
    exact (facts k hki).earlier_separated j hjk x hx y hy
  · intro j hji
    exact (facts j hji).hits_up_to
  · intro j hji x hx
    exact (facts j hji).first_added_located x hx
  · intro j hji k hki hjk x hx y hy hr
    exact (facts k hki).old_new_explained j hjk x hx y hy hr

/-- The selected block at every stage satisfies its exact stage certificate. -/
theorem blocks_stageFacts (i : I) :
    StageFacts r layer Located i
      (fun j (_ : r j i) ↦
        blocks (r := r) (layer := layer) (Located := Located) extend j)
      (blocks (r := r) (layer := layer) (Located := Located) extend i) :=
  blocks_stageFacts_of_prefixGood r layer Located extend i
    (blocks_prefixGood (r := r) (layer := layer) (Located := Located) extend i)

include Located extend

/-- Generic outer-recursion theorem.  It assembles an exact
`Global.BlockFamily` from the one-stage extension hypothesis, without any
countability requirement on `I` or its initial segments. -/
theorem exists_blockFamily :
    Nonempty (BlockFamily I r layer) := by
  let B : I → Set Point :=
    blocks (r := r) (layer := layer) (Located := Located) extend
  refine ⟨
    { block := B
      block_partial := fun i ↦
        (blocks_stageFacts (r := r) (layer := layer) (Located := Located) extend i).block_partial
      earlier_separated := ?_
      hits_up_to := ?_
      located := Located
      first_added_located := ?_
      old_new_explained := ?_ }⟩
  · intro i j hij x hx y hy
    exact (blocks_stageFacts (r := r) (layer := layer) (Located := Located) extend j).earlier_separated i hij x hx y hy
  · intro i n hn K hK
    obtain ⟨p, hp, hpK⟩ :=
      (blocks_stageFacts (r := r) (layer := layer)
        (Located := Located) extend i).hits_up_to n hn K hK
    refine ⟨p, ?_, hpK⟩
    rcases hp with hp | hp
    · rcases hp with ⟨j, hji, hpj⟩
      exact Or.inl ⟨j, hji, hpj⟩
    · exact Or.inr hp
  · intro i x hx
    exact (blocks_stageFacts (r := r) (layer := layer) (Located := Located) extend i).first_added_located x hx
  · intro i j hij x hx y hy hr
    exact (blocks_stageFacts (r := r) (layer := layer) (Located := Located) extend j).old_new_explained i hij x hx y hy hr

end OuterRecursion
end Global

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/GlobalOneCross.lean` -/

section
/-!
# The one-cross invariant at a terminal layer

This file derives the one-cross property used by the inner terminal
recursion from the outer birth-block invariants and the concrete candidate
sequence.  In particular, the property is not an additional hypothesis of
the global construction.
-/

open Set

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Global
namespace CodedDavies

variable (D : DaviesDecomposition Code.skolem)

local instance : IsWellOrder D.Index D.lt := D.isWellOrder

/-- The outer-old set at stage `i`. -/
def stageOld {i : D.Index}
    (prev : (j : D.Index) → D.lt j i → Set Point) : Set Point :=
  OuterRecursion.priorUnion D.lt i prev

/-- The outer prefix invariants make the union of all prior birth blocks
partial Steinhaus. -/
theorem stageOld_partial {i : D.Index}
    {prev : (j : D.Index) → D.lt j i → Set Point}
    (hprefix : OuterRecursion.PrefixGood D.lt (terminalLayer D)
      (fun j x ↦ Code.point x ∈ D.layer j) i prev) :
    IsPartialSteinhaus (stageOld D prev) := by
  intro x hx y hy hxy z
  rcases hx with ⟨j, hji, hxj⟩
  rcases hy with ⟨k, hki, hyk⟩
  rcases trichotomous_of D.lt j k with hjk | hjk | hjk
  · exact hprefix.earlier_separated j hji k hki hjk x hxj y hyk hxy z
  · subst k
    exact hprefix.block_partial j hji hxj hyk hxy z
  · exact (separated_comm.mp
      (hprefix.earlier_separated k hki j hji hjk y hyk x hxj)) hxy z

/-- Every outer-old point code lies in the Davies predecessor cut. -/
theorem stageOld_before {i : D.Index}
    {prev : (j : D.Index) → D.lt j i → Set Point}
    (hprefix : OuterRecursion.PrefixGood D.lt (terminalLayer D)
      (fun j x ↦ Code.point x ∈ D.layer j) i prev) :
    ∀ x ∈ stageOld D prev, Code.point x ∈ D.before i := by
  intro x hx
  rcases hx with ⟨j, hji, hxj⟩
  exact ⟨j, hji, hprefix.first_added_located j hji x hxj⟩

/-- Two distinct rational points in one earlier birth block would recover
the current rational class by the layer-closure instance of D6. -/
private theorem samePriorBlock_eq {i j : D.Index} (hji : D.lt j i)
    {prev : (k : D.Index) → D.lt k i → Set Point}
    (hprefix : OuterRecursion.PrefixGood D.lt (terminalLayer D)
      (fun k x ↦ Code.point x ∈ D.layer k) i prev)
    {n : ℕ} (hn : n ∈ (terminalLayer D i).active)
    {x y : Point} (hx : x ∈ prev j hji) (hy : y ∈ prev j hji)
    (hxn : ((terminalLayer D i).frame n).IsRational x)
    (hyn : ((terminalLayer D i).frame n).IsRational y) : x = y := by
  by_contra hxy
  have hclosed := D.skolem_mem_before_or_layer j 2
    [Code.point x, Code.point y] (by
      intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl
      · exact hprefix.first_added_located j hji x hx
      · exact hprefix.first_added_located j hji y hy)
  rw [Code.skolem_recover,
    Code.recoveredClass_eq hxy hxn hyn] at hclosed
  have hbefore : Code.latticeClass
      (OrientedFrame.classOf ((terminalLayer D i).frame n)) ∈ D.before i := by
    rcases hclosed with hbeforeJ | hlayerJ
    · rcases hbeforeJ with ⟨k, hkj, hk⟩
      exact ⟨k, IsTrans.trans k j i hkj hji, hk⟩
    · exact ⟨j, hji, hlayerJ⟩
  exact (not_mem_before_of_mem_layer D
    (active_frame_class_mem_layer D hn)) hbefore

/-- The old-old part of one-cross.  Different birth blocks use invariant
(I5); the same birth block uses the preceding D6 argument. -/
theorem stageOld_rational_subsingleton {i : D.Index}
    {prev : (j : D.Index) → D.lt j i → Set Point}
    (hprefix : OuterRecursion.PrefixGood D.lt (terminalLayer D)
      (fun j x ↦ Code.point x ∈ D.layer j) i prev)
    {n : ℕ} (hn : n ∈ (terminalLayer D i).active) :
    {x | x ∈ stageOld D prev ∧
      ((terminalLayer D i).frame n).IsRational x}.Subsingleton := by
  intro x hx y hy
  rcases hx.1 with ⟨j, hji, hxj⟩
  rcases hy.1 with ⟨k, hki, hyk⟩
  rcases trichotomous_of D.lt j k with hjk | hjk | hjk
  · by_contra hxy
    have hdist : RationalSqDist x y := by
      simpa only [RationalSqDist, HasRationalSqDist] using
        hasRationalSqDist_of_isRational hx.2 hy.2
    obtain ⟨m, hm, hxm, hym⟩ :=
      hprefix.old_new_explained j hji k hki hjk x hxj y hyk hdist
    have hclassEq := OrientedFrame.class_eq_of_two_common hxy
      hx.2 hxm hy.2 hym
    have hclassK := active_frame_class_mem_layer D hm
    rw [← hclassEq] at hclassK
    exact (not_mem_before_of_mem_layer D
      (active_frame_class_mem_layer D hn)) ⟨k, hki, hclassK⟩
  · subst k
    exact samePriorBlock_eq D hji hprefix hn hxj hyk hx.2 hy.2
  · by_contra hxy
    have hdist : RationalSqDist y x := by
      simpa only [RationalSqDist, HasRationalSqDist] using
        hasRationalSqDist_of_isRational hy.2 hx.2
    obtain ⟨m, hm, hym, hxm⟩ :=
      hprefix.old_new_explained k hki j hji hjk y hyk x hxj hdist
    have hclassEq := OrientedFrame.class_eq_of_two_common (Ne.symm hxy)
      hy.2 hym hx.2 hxm
    have hclassJ := active_frame_class_mem_layer D hm
    rw [← hclassEq] at hclassJ
    exact (not_mem_before_of_mem_layer D
      (active_frame_class_mem_layer D hn)) ⟨j, hji, hclassJ⟩

/-- The concrete source family used at outer stage `i`. -/
noncomputable def stageSource
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index}
    {prev : (j : D.Index) → D.lt j i → Set Point}
    (hprefix : OuterRecursion.PrefixGood D.lt (terminalLayer D)
      (fun j x ↦ Code.point x ∈ D.layer j) i prev)
    (default : ScheduledRequirement (terminalLayer D i)) : ℕ → Set Point :=
  let hOld := stageOld_partial D hprefix
  let hbefore := stageOld_before D hprefix
  let hclass := fun n hn ↦ active_frame_class_mem_layer D hn
  let hclassInj := terminalLayer_class_injOn D i
  candidateSource D default
    (outerForbiddenLines D circle hOld hbefore hclass)
    hclass hclassInj

/-- The full one-cross invariant.  Before processing active frame `n`, at
most one point among the outer-old set and all earlier source families is
rational in frame `n`. -/
theorem oneCross_subsingleton
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index}
    {prev : (j : D.Index) → D.lt j i → Set Point}
    (hprefix : OuterRecursion.PrefixGood D.lt (terminalLayer D)
      (fun j x ↦ Code.point x ∈ D.layer j) i prev)
    (default : ScheduledRequirement (terminalLayer D i))
    (n : ℕ) (hn : n ∈ (terminalLayer D i).active) :
    {x | (x ∈ stageOld D prev ∨
        ∃ m < n, m ∈ (terminalLayer D i).active ∧
          x ∈ stageSource D circle hprefix default m) ∧
      ((terminalLayer D i).frame n).IsRational x}.Subsingleton := by
  let A := terminalLayer D i
  let old := stageOld D prev
  let hOld := stageOld_partial D hprefix
  let hbefore := stageOld_before D hprefix
  let hclass : ∀ m ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame m)) ∈ D.layer i :=
    fun m hm ↦ active_frame_class_mem_layer D hm
  let hclassInj : Set.InjOn
      (fun m ↦ OrientedFrame.classOf (A.frame m)) A.active :=
    terminalLayer_class_injOn D i
  let outer := outerForbiddenLines D circle hOld hbefore hclass
  let Source : ℕ → Set Point :=
    candidateSource D default outer hclass hclassInj
  have hSource : Source = stageSource D circle hprefix default := by
    rfl
  intro x hx y hy
  have hdist : HasRationalSqDist x y :=
    hasRationalSqDist_of_isRational hx.2 hy.2
  rcases hx.1 with hxold | hxsource
  · rcases hy.1 with hyold | hysource
    · exact stageOld_rational_subsingleton D hprefix hn ⟨hxold, hx.2⟩ ⟨hyold, hy.2⟩
    · rcases hysource with ⟨m, hmn, hm, hym⟩
      have hym' : y ∈ Source m := by simpa only [hSource] using hym
      have hxm := oldPoint_rational_of_rationalSqDist D circle hOld hbefore
        hclass hclassInj default hxold hym' hdist
      exact rational_intersection_subsingleton hclassInj hm hn
        (Nat.ne_of_lt hmn) ⟨hx.2, hxm⟩ ⟨hy.2,
          candidateSource_rational D default outer hclass hclassInj hym'⟩
  · rcases hxsource with ⟨m, hmn, hm, hxm⟩
    have hxm' : x ∈ Source m := by simpa only [hSource] using hxm
    rcases hy.1 with hyold | hysource
    · have hym := oldPoint_rational_of_rationalSqDist D circle hOld hbefore
        hclass hclassInj default hyold hxm' (by
          simpa only [HasRationalSqDist, distSq_comm] using hdist)
      exact rational_intersection_subsingleton hclassInj hm hn
        (Nat.ne_of_lt hmn) ⟨hx.2, candidateSource_rational D default outer
          hclass hclassInj hxm'⟩ ⟨hy.2, hym⟩
    · rcases hysource with ⟨k, hkn, hk, hyk⟩
      have hyk' : y ∈ Source k := by simpa only [hSource] using hyk
      rcases lt_trichotomy m k with hmk | hmk | hkm
      · have hxk := sourcePoint_rational_of_rationalSqDist D default outer
          hclass hclassInj hmk hxm' hyk' hdist
        exact rational_intersection_subsingleton hclassInj hk hn
          (Nat.ne_of_lt hkn) ⟨hx.2, hxk⟩
            ⟨hy.2, candidateSource_rational D default outer
              hclass hclassInj hyk'⟩
      · subst k
        exact rational_intersection_subsingleton hclassInj hm hn
          (Nat.ne_of_lt hmn)
          ⟨hx.2, candidateSource_rational D default outer
            hclass hclassInj hxm'⟩
          ⟨hy.2, candidateSource_rational D default outer
            hclass hclassInj hyk'⟩
      · have hyM := sourcePoint_rational_of_rationalSqDist D default outer
          hclass hclassInj hkm hyk' hxm' (by
            simpa only [HasRationalSqDist, distSq_comm] using hdist)
        exact rational_intersection_subsingleton hclassInj hm hn
          (Nat.ne_of_lt hmn)
          ⟨hx.2, candidateSource_rational D default outer
            hclass hclassInj hxm'⟩ ⟨hy.2, hyM⟩

/-- The concrete one-cross theorem in exactly the form consumed by
`poolStepAvailable`. -/
theorem stageOneCross
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index}
    {prev : (j : D.Index) → D.lt j i → Set Point}
    (hprefix : OuterRecursion.PrefixGood D.lt (terminalLayer D)
      (fun j x ↦ Code.point x ∈ D.layer j) i prev)
    (default : ScheduledRequirement (terminalLayer D i)) :
    (terminalLayer D i).OneCross (stageOld D prev)
      (stageSource D circle hprefix default) := by
  intro n hn
  exact oneCross_subsingleton D circle hprefix default n hn

end CodedDavies
end Global

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/GlobalAssembly.lean` -/

section
/-!
# Concrete global assembly for Erdős Problem 215

This module connects the terminal candidate construction and one-cross
theorem to the generic well-founded outer recursion.  The only remaining
component parameter is the rich selector theorem.
-/

open Set

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Global
namespace CodedDavies

variable (D : DaviesDecomposition Code.skolem)

local instance : IsWellOrder D.Index D.lt := D.isWellOrder

/-- A fixed residue requirement used only to seed the Cantor schedule once
an active frame has been exhibited. -/
def defaultRequirement {A : TerminalLayer} (n : ℕ) (hn : n ∈ A.active) :
    ScheduledRequirement A where
  index := n
  active := hn
  residue := {
    d := 1
    hd := by norm_num
    i := 0
    j := 0
    a := 0
    b := 0 }

/-- The exact concrete stage extension consumed by the well-founded outer
recursion. -/
theorem stageExtension (selector : RichSelectorTheorem) :
    OuterRecursion.StageExtension D.lt (terminalLayer D)
      (fun i x ↦ Code.point x ∈ D.layer i) := by
  intro i prev hprefix
  let A := terminalLayer D i
  let old := stageOld D prev
  by_cases hactive : A.active.Nonempty
  · obtain ⟨n, hn⟩ := hactive
    let default : ScheduledRequirement A := defaultRequirement n hn
    let hOld : IsPartialSteinhaus old := stageOld_partial D hprefix
    let hbefore : ∀ x ∈ old, Code.point x ∈ D.before i :=
      stageOld_before D hprefix
    let hclass : ∀ m ∈ A.active,
        Code.latticeClass (OrientedFrame.classOf (A.frame m)) ∈ D.layer i :=
      fun m hm ↦ active_frame_class_mem_layer D hm
    let hclassInj : Set.InjOn
        (fun m ↦ OrientedFrame.classOf (A.frame m)) A.active :=
      terminalLayer_class_injOn D i
    have hone : A.OneCross old
        (candidateSource D default
          (outerForbiddenLines D threeCircleFiniteness hOld hbefore hclass)
          hclass hclassInj) := by
      simpa only [A, old, stageSource] using
        stageOneCross D threeCircleFiniteness hprefix default
    let cert := terminalStage D selector threeCircleFiniteness hOld hbefore
      hclass hclassInj default hone
    let block : Set Point := cert.selected \ old
    refine ⟨block, ?_⟩
    refine {
      block_partial := ?_
      earlier_separated := ?_
      hits_up_to := ?_
      first_added_located := ?_
      old_new_explained := ?_ }
    · intro x hx y hy hxy z
      exact cert.isPartial hx.1 hy.1 hxy z
    · intro j hji x hx y hy hxy z hdist
      exact cert.isPartial (cert.old_subset ⟨j, hji, hx⟩) hy.1 hxy z hdist
    · intro m hm K hK
      obtain ⟨p, hp, hpK⟩ := cert.hits m hm K hK
      refine ⟨p, ?_, hpK⟩
      by_cases hpold : p ∈ old
      · exact Or.inl hpold
      · exact Or.inr ⟨hp, hpold⟩
    · intro x hx
      exact cert.located_new x hx.1 hx.2
    · intro j hji x hx y hy hdist
      exact cert.explains_old_new x ⟨j, hji, hx⟩ y hy.1 hy.2 hdist
  · refine ⟨∅, ?_⟩
    refine {
      block_partial := by simp [IsPartialSteinhaus]
      earlier_separated := by simp
      hits_up_to := ?_
      first_added_located := by simp
      old_new_explained := by simp }
    intro n hn
    exact (hactive ⟨n, hn⟩).elim

/-- The concrete outer recursion produces a verified global family of birth
blocks. -/
theorem exists_globalBlockFamily (selector : RichSelectorTheorem) :
    Nonempty (BlockFamily D.Index D.lt (terminalLayer D)) :=
  OuterRecursion.exists_blockFamily D.lt (terminalLayer D)
    (fun i x ↦ Code.point x ∈ D.layer i)
    (stageExtension D selector)

/-- Global partial-Steinhaus set meeting every rational-equivalence class of
oriented integer lattices. -/
theorem global_rational_classes (selector : RichSelectorTheorem) :
    ∃ S : Set Point, IsPartialSteinhaus S ∧
      ∀ L : OrientedFrame, HitsRationalClass S L := by
  let D := decomposition
  obtain ⟨B⟩ := exists_globalBlockFamily D selector
  letI : IsWellOrder D.Index D.lt := D.isWellOrder
  refine ⟨B.result, ?_, ?_⟩
  · apply B.result_partial
    intro i j
    rcases trichotomous_of D.lt i j with hij | hij | hij
    · exact Or.inr (Or.inl hij)
    · exact Or.inl hij
    · exact Or.inr (Or.inr hij)
  · intro L K hKL
    exact blockFamily_hitsAllFrames D B K

end CodedDavies
end Global

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorLimit.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
The denominator-chain/direct-limit part of the Jackson--Mauldin selector.

This file deliberately assumes the still-separate finite theorem saying that
every separated selector has a literal separated extension across each prime.
From that hypothesis it derives extension across every positive multiplier,
forces the new points into a rich pool without changing old points, and takes
the direct limit.
-/

namespace Selector

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The exact finite input needed by the direct-limit construction. -/
def LiteralPrimeExtensionHypothesis : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), ∀ {d : ℕ}, d ≠ 0 → ∀ (s : LiftData d),
    s.Separated → ∃ t : LiftData (p * d), PrimeExtends p hp.pos s t ∧ t.Separated

/-- Literal extension, with no primality restriction on the multiplier. -/
def MultExtends (m : ℕ) (hm : 0 < m) {d : ℕ}
    (s : LiftData d) (t : LiftData (m * d)) : Prop :=
  PrimeExtends m hm s t

def LiftData.cast {d e : ℕ} (h : d = e) (s : LiftData d) : LiftData e :=
  h ▸ s

@[simp] lemma LiftData.cast_rfl {d : ℕ} (s : LiftData d) : s.cast rfl = s := rfl

@[simp] lemma LiftData.cast_k {d e : ℕ} (h : d = e) (s : LiftData d) (i j : Fin e) :
    (s.cast h).k i j = s.k (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst e
  rfl

@[simp] lemma LiftData.cast_l {d e : ℕ} (h : d = e) (s : LiftData d) (i j : Fin e) :
    (s.cast h).l i j = s.l (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst e
  rfl

lemma LiftData.separated_cast {d e : ℕ} (h : d = e) (s : LiftData d)
    (hs : s.Separated) : (s.cast h).Separated := by
  subst e
  exact hs

lemma multExtends_one {d : ℕ} (s : LiftData d) :
    MultExtends 1 (by omega) s (s.cast (by simp)) := by
  intro i j
  simpa [MultExtends, oldIndex]

/-- Prime extensions compose to give an extension across any positive natural
multiplier. -/
theorem exists_multExtension (hprime : LiteralPrimeExtensionHypothesis)
    (m : ℕ) (hm : 0 < m) {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (hs : s.Separated) :
    ∃ t : LiftData (m * d), MultExtends m hm s t ∧ t.Separated := by
  induction m using Nat.strong_induction_on generalizing d with
  | h m ih =>
      by_cases hm1 : m = 1
      · subst m
        exact ⟨s.cast (by simp), multExtends_one s,
          s.separated_cast (by simp) hs⟩
      · obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
        let q := m / p
        have hp0 : 0 < p := hp.pos
        have hq0 : 0 < q := Nat.div_pos (Nat.le_of_dvd hm hpm) hp0
        have hmq : p * q = m := Nat.mul_div_cancel' hpm
        have hqm : q < m := Nat.div_lt_self hm hp.one_lt
        obtain ⟨t, hst, ht⟩ := ih q hqm hq0 hd s hs
        obtain ⟨u, htu, hu⟩ := hprime p hp (Nat.mul_ne_zero (Nat.ne_of_gt hq0) hd) t ht
        have hden : p * (q * d) = m * d := by rw [← hmq]; simp [Nat.mul_assoc]
        let u' : LiftData (m * d) := u.cast hden
        refine ⟨u', ?_, u.separated_cast hden hu⟩
        intro i j
        have hst' := hst i j
        have htu' := htu (oldIndex q hq0 i) (oldIndex q hq0 j)
        have hi : Fin.cast hden.symm (oldIndex m hm i) =
            oldIndex p hp0 (oldIndex q hq0 i) := by
          apply Fin.ext
          change m * (i : ℕ) = p * (q * (i : ℕ))
          rw [← hmq]
          simp [Nat.mul_assoc]
        have hj : Fin.cast hden.symm (oldIndex m hm j) =
            oldIndex p hp0 (oldIndex q hq0 j) := by
          apply Fin.ext
          change m * (j : ℕ) = p * (q * (j : ℕ))
          rw [← hmq]
          simp [Nat.mul_assoc]
        dsimp only [u']
        rw [LiftData.cast_k, LiftData.cast_l, hi, hj]
        exact ⟨htu'.1.trans hst'.1, htu'.2.trans hst'.2⟩

/-- Force only the genuinely new residues of a literal extension into a rich
pool.  The old lifts are left definitionally equal to the previous lifts. -/
theorem multExtension_in_rich_pool (P : Set RatPoint) (hP : Rich P)
    (m : ℕ) (hm : 0 < m) {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (hsP : ∀ i j, s.point i j ∈ P) {t : LiftData (m * d)}
    (hst : MultExtends m hm s t) (ht : t.Separated) :
    ∃ u : LiftData (m * d), MultExtends m hm s u ∧ u.Separated ∧
      ∀ i j, u.point i j ∈ P := by
  have hmd : m * d ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hm) hd
  have havail : ∀ i j, ∃ k l a b : ℤ,
      k = t.k i j + (m * d) * a ∧ l = t.l i j + (m * d) * b ∧
      liftedPoint (m * d) i j k l ∈ P ∧
      ∀ i₀ j₀, i = oldIndex m hm i₀ → j = oldIndex m hm j₀ →
        k = s.k i₀ j₀ ∧ l = s.l i₀ j₀ := by
    intro i j
    by_cases hold : ∃ i₀ j₀, i = oldIndex m hm i₀ ∧ j = oldIndex m hm j₀
    · rcases hold with ⟨i₀, j₀, rfl, rfl⟩
      have heq := hst i₀ j₀
      refine ⟨t.k (oldIndex m hm i₀) (oldIndex m hm j₀),
        t.l (oldIndex m hm i₀) (oldIndex m hm j₀), 0, 0, by simp, by simp, ?_, ?_⟩
      · change t.point (oldIndex m hm i₀) (oldIndex m hm j₀) ∈ P
        rw [point_oldIndex_of_primeExtends m hm hd hst i₀ j₀]
        exact hsP i₀ j₀
      · intro i₁ j₁ hi hj
        have hii : i₁ = i₀ := oldIndex_injective m hm (hi.symm)
        have hjj : j₁ = j₀ := oldIndex_injective m hm (hj.symm)
        subst i₁
        subst j₁
        exact heq
    · rcases (hP (m * d) hmd i j (t.k i j) (t.l i j)).nonempty with ⟨x, hx⟩
      rcases hx with ⟨k, l, rfl, hk, hl, hp⟩
      rcases Int.modEq_iff_add_fac.mp hk with ⟨a, ha⟩
      rcases Int.modEq_iff_add_fac.mp hl with ⟨b, hb⟩
      refine ⟨k, l, a, b, ha, hb, hp, ?_⟩
      intro i₀ j₀ hi hj
      exact (hold ⟨i₀, j₀, hi, hj⟩).elim
  choose k l a b hk hl hp hold using havail
  let u : LiftData (m * d) := ⟨k, l⟩
  have htu : t.Congruent u := by
    intro i j
    exact ⟨a i j, b i j, hk i j, hl i j⟩
  refine ⟨u, ?_, LiftData.separated_of_congruent ht htu, ?_⟩
  · intro i j
    exact hold (oldIndex m hm i) (oldIndex m hm j) i j rfl rfl
  · intro i j
    exact hp i j

/-- The rich-pool version of extension across any positive multiplier. -/
theorem exists_multExtension_in_rich_pool (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) (m : ℕ) (hm : 0 < m)
    {d : ℕ} (hd : d ≠ 0) (s : LiftData d) (hs : s.Separated)
    (hsP : ∀ i j, s.point i j ∈ P) :
    ∃ t : LiftData (m * d), MultExtends m hm s t ∧ t.Separated ∧
      ∀ i j, t.point i j ∈ P := by
  obtain ⟨t, hst, ht⟩ := exists_multExtension hprime m hm hd s hs
  exact multExtension_in_rich_pool P hP m hm hd s hsP hst ht

/-- A cofinal denominator chain.  Its closed form is `(n+1)! * d₀`. -/
def chainDenom (d₀ : ℕ) : ℕ → ℕ
  | 0 => d₀
  | n + 1 => (n + 2) * chainDenom d₀ n

lemma chainDenom_ne_zero {d₀ : ℕ} (hd₀ : d₀ ≠ 0) (n : ℕ) :
    chainDenom d₀ n ≠ 0 := by
  induction n with
  | zero => exact hd₀
  | succ n ih => exact Nat.mul_ne_zero (by omega) ih

lemma chainDenom_eq_factorial (d₀ n : ℕ) :
    chainDenom d₀ n = (n + 1).factorial * d₀ := by
  induction n with
  | zero => simp [chainDenom]
  | succ n ih =>
      rw [chainDenom, ih]
      change (n + 2) * ((n + 1).factorial * d₀) = (n + 2).factorial * d₀
      have hf : (n + 2).factorial = (n + 2) * (n + 1).factorial := by
        convert Nat.factorial_succ (n + 1) using 1 <;> omega
      rw [hf]
      ring

lemma dvd_chainDenom (d₀ e : ℕ) (he : 0 < e) : e ∣ chainDenom d₀ e := by
  rw [chainDenom_eq_factorial]
  exact dvd_mul_of_dvd_left (Nat.dvd_factorial he (by omega)) d₀

/-- A separated finite selector all of whose points lie in `P`. -/
structure PoolStage (P : Set RatPoint) (d : ℕ) where
  selector : LiftData d
  separated : selector.Separated
  mem_pool : ∀ i j, selector.point i j ∈ P

noncomputable def nextPoolStage (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d : ℕ} (hd : d ≠ 0) (n : ℕ)
    (s : PoolStage P d) : PoolStage P ((n + 2) * d) := by
  let h := exists_multExtension_in_rich_pool hprime P hP (n + 2) (by omega) hd
    s.selector s.separated s.mem_pool
  exact ⟨Classical.choose h, (Classical.choose_spec h).2.1,
    (Classical.choose_spec h).2.2⟩

lemma nextPoolStage_extends (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d : ℕ} (hd : d ≠ 0) (n : ℕ)
    (s : PoolStage P d) :
    MultExtends (n + 2) (by omega) s.selector
      (nextPoolStage hprime P hP hd n s).selector := by
  exact (Classical.choose_spec (exists_multExtension_in_rich_pool hprime P hP
    (n + 2) (by omega) hd s.selector s.separated s.mem_pool)).1

noncomputable def poolChain (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d₀ : ℕ} (hd₀ : d₀ ≠ 0)
    (s₀ : PoolStage P d₀) : (n : ℕ) → PoolStage P (chainDenom d₀ n)
  | 0 => s₀
  | n + 1 => nextPoolStage hprime P hP (chainDenom_ne_zero hd₀ n) n
      (poolChain hprime P hP hd₀ s₀ n)

lemma poolChain_extends (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d₀ : ℕ} (hd₀ : d₀ ≠ 0)
    (s₀ : PoolStage P d₀) (n : ℕ) :
    MultExtends (n + 2) (by omega)
      (poolChain hprime P hP hd₀ s₀ n).selector
      (poolChain hprime P hP hd₀ s₀ (n + 1)).selector := by
  change MultExtends (n + 2) (by omega)
    (poolChain hprime P hP hd₀ s₀ n).selector
    (nextPoolStage hprime P hP (chainDenom_ne_zero hd₀ n) n
      (poolChain hprime P hP hd₀ s₀ n)).selector
  exact nextPoolStage_extends hprime P hP (chainDenom_ne_zero hd₀ n) n _

def stageRange {d : ℕ} (s : LiftData d) : Set RatPoint :=
  Set.range (fun ij : Fin d × Fin d ↦ s.point ij.1 ij.2)

lemma stageRange_subset_of_multExtends (m : ℕ) (hm : 0 < m) {d : ℕ}
    (hd : d ≠ 0) {s : LiftData d} {t : LiftData (m * d)}
    (hst : MultExtends m hm s t) : stageRange s ⊆ stageRange t := by
  rintro x ⟨⟨i, j⟩, rfl⟩
  refine ⟨⟨oldIndex m hm i, oldIndex m hm j⟩, ?_⟩
  exact point_oldIndex_of_primeExtends m hm hd hst i j

lemma poolChain_stageRange_monotone (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d₀ : ℕ} (hd₀ : d₀ ≠ 0)
    (s₀ : PoolStage P d₀) :
    Monotone (fun n ↦ stageRange (poolChain hprime P hP hd₀ s₀ n).selector) := by
  apply monotone_nat_of_le_succ
  intro n
  exact stageRange_subset_of_multExtends (n + 2) (by omega)
    (chainDenom_ne_zero hd₀ n) (poolChain_extends hprime P hP hd₀ s₀ n)

def limitSelector (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d₀ : ℕ} (hd₀ : d₀ ≠ 0)
    (s₀ : PoolStage P d₀) : Set RatPoint :=
  ⋃ n, stageRange (poolChain hprime P hP hd₀ s₀ n).selector

lemma limitSelector_subset (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d₀ : ℕ} (hd₀ : d₀ ≠ 0)
    (s₀ : PoolStage P d₀) :
    limitSelector hprime P hP hd₀ s₀ ⊆ P := by
  rintro x hx
  rcases Set.mem_iUnion.mp hx with ⟨n, ⟨⟨i, j⟩, rfl⟩⟩
  exact (poolChain hprime P hP hd₀ s₀ n).mem_pool i j

lemma limitSelector_isPartial (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d₀ : ℕ} (hd₀ : d₀ ≠ 0)
    (s₀ : PoolStage P d₀) :
    IsPartial (limitSelector hprime P hP hd₀ s₀) := by
  intro x hx y hy hxy
  rcases Set.mem_iUnion.mp hx with ⟨a, hxa⟩
  rcases Set.mem_iUnion.mp hy with ⟨b, hyb⟩
  let N := max a b
  have hmono := poolChain_stageRange_monotone hprime P hP hd₀ s₀
  have hxN := hmono (le_max_left a b) hxa
  have hyN := hmono (le_max_right a b) hyb
  rcases hxN with ⟨⟨i₁, j₁⟩, rfl⟩
  rcases hyN with ⟨⟨i₂, j₂⟩, rfl⟩
  have hne : (i₁, j₁) ≠ (i₂, j₂) := by
    intro h
    exact hxy (congrArg
      (fun ij : Fin (chainDenom d₀ N) × Fin (chainDenom d₀ N) ↦
        (poolChain hprime P hP hd₀ s₀ N).selector.point ij.1 ij.2) h)
  exact (LiftData.separated_iff_sqDist_not_int (chainDenom_ne_zero hd₀ N)
    (poolChain hprime P hP hd₀ s₀ N).selector).mp
      (poolChain hprime P hP hd₀ s₀ N).separated i₁ j₁ i₂ j₂ hne

lemma residue_liftedPoint_eq (d : ℕ) (hd : d ≠ 0) (i j : Fin d)
    (k₁ l₁ k₂ l₂ : ℤ) :
    residue (liftedPoint d i j k₁ l₁) = residue (liftedPoint d i j k₂ l₂) := by
  apply Prod.ext
  · apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simp only [liftedPoint, residue, Prod.fst_sub, AddSubgroup.mem_zmultiples_iff]
    refine ⟨k₁ - k₂, ?_⟩
    push_cast
    field_simp [hd]
    ring
  · apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simp only [liftedPoint, residue, Prod.snd_sub, AddSubgroup.mem_zmultiples_iff]
    refine ⟨l₁ - l₂, ?_⟩
    push_cast
    field_simp [hd]
    ring

lemma rat_eq_residue_lift (q : ℚ) (D : ℕ) (hD : 0 < D) (hden : q.den ∣ D) :
    ∃ i : Fin D, ∃ k : ℤ, q = (i : ℚ) / D + k := by
  rcases hden with ⟨c, hc⟩
  have hcpos : 0 < c := by
    apply Nat.pos_of_ne_zero
    intro hc0
    subst c
    simp at hc
    omega
  let N : ℤ := q.num * c
  let r : ℤ := N % (D : ℤ)
  have hr0 : 0 ≤ r := Int.emod_nonneg N (by exact_mod_cast hD.ne')
  have hrD : r < (D : ℤ) := Int.emod_lt_of_pos N (by exact_mod_cast hD)
  let i : Fin D := ⟨r.toNat, (Int.toNat_lt hr0).2 hrD⟩
  let k : ℤ := N / (D : ℤ)
  refine ⟨i, k, ?_⟩
  have hir : ((i : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
  have hsplit : r + (D : ℤ) * k = N := Int.emod_add_mul_ediv N D
  rw [← q.num_div_den]
  push_cast
  field_simp [q.den_ne_zero, hD.ne']
  have hirQ : ((i : ℕ) : ℚ) = (r : ℚ) := by
    calc
      ((i : ℕ) : ℚ) = ((((i : ℕ) : ℤ)) : ℚ) := by norm_num
      _ = (r : ℚ) := congrArg (fun z : ℤ ↦ (z : ℚ)) hir
  have hsplitQ : (r : ℚ) + D * k = N := by exact_mod_cast hsplit
  rw [hirQ, hsplitQ]
  dsimp only [N]
  rw [hc]
  push_cast
  ring

lemma ratPoint_eq_liftedPoint (x : RatPoint) (D : ℕ) (hD : 0 < D)
    (hden₁ : x.1.den ∣ D) (hden₂ : x.2.den ∣ D) :
    ∃ i j : Fin D, ∃ k l : ℤ, x = liftedPoint D i j k l := by
  obtain ⟨i, k, hi⟩ := rat_eq_residue_lift x.1 D hD hden₁
  obtain ⟨j, l, hj⟩ := rat_eq_residue_lift x.2 D hD hden₂
  exact ⟨i, j, k, l, Prod.ext hi hj⟩

lemma limitSelector_hits (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d₀ : ℕ} (hd₀ : d₀ ≠ 0)
    (s₀ : PoolStage P d₀) :
    HitsEveryIntegerTranslate (limitSelector hprime P hP hd₀ s₀) := by
  intro x
  let e := x.1.den * x.2.den
  have he : 0 < e := Nat.mul_pos x.1.den_pos x.2.den_pos
  have heD : e ∣ chainDenom d₀ e := dvd_chainDenom d₀ e he
  have hden₁ : x.1.den ∣ chainDenom d₀ e :=
    (dvd_mul_right x.1.den x.2.den).trans heD
  have hden₂ : x.2.den ∣ chainDenom d₀ e :=
    (dvd_mul_left x.2.den x.1.den).trans heD
  obtain ⟨i, j, k, l, hx⟩ := ratPoint_eq_liftedPoint x (chainDenom d₀ e)
    (Nat.pos_of_ne_zero (chainDenom_ne_zero hd₀ e)) hden₁ hden₂
  let y := (poolChain hprime P hP hd₀ s₀ e).selector.point i j
  refine ⟨y, ?_, ?_⟩
  · apply Set.mem_iUnion.mpr
    exact ⟨e, ⟨(i, j), rfl⟩⟩
  · rw [hx]
    exact residue_liftedPoint_eq (chainDenom d₀ e) (chainDenom_ne_zero hd₀ e)
      i j _ _ k l

/-- Direct-limit assembly from one finite separated selector already lying in
the rich pool.  The last clause records that every base-stage point survives
literally in the limit. -/
theorem exists_rich_selector_from_base (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d₀ : ℕ} (hd₀ : d₀ ≠ 0)
    (s₀ : PoolStage P d₀) :
    ∃ T : Set RatPoint, T ⊆ P ∧ IsPartial T ∧ HitsEveryIntegerTranslate T ∧
      stageRange s₀.selector ⊆ T := by
  refine ⟨limitSelector hprime P hP hd₀ s₀,
    limitSelector_subset hprime P hP hd₀ s₀,
    limitSelector_isPartial hprime P hP hd₀ s₀,
    limitSelector_hits hprime P hP hd₀ s₀, ?_⟩
  intro x hx
  exact Set.mem_iUnion.mpr ⟨0, hx⟩

/-- Translate all integral lifts by the same integer vector. -/
def translateLift {d : ℕ} (s : LiftData d) (a b : ℤ) : LiftData d where
  k i j := s.k i j + a
  l i j := s.l i j + b

lemma translateLift_separated {d : ℕ} (s : LiftData d) (a b : ℤ)
    (hs : s.Separated) : (translateLift s a b).Separated := by
  intro i₁ j₁ i₂ j₂ hne hdiv
  apply hs i₁ j₁ i₂ j₂ hne
  have heq :
      conflictNumerator d i₁ j₁ i₂ j₂
          ((translateLift s a b).k i₁ j₁) ((translateLift s a b).l i₁ j₁)
          ((translateLift s a b).k i₂ j₂) ((translateLift s a b).l i₂ j₂) =
        conflictNumerator d i₁ j₁ i₂ j₂
          (s.k i₁ j₁) (s.l i₁ j₁) (s.k i₂ j₂) (s.l i₂ j₂) := by
    simp only [translateLift, conflictNumerator]
    ring
  rwa [heq] at hdiv

lemma translateLift_point_eq {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (i j : Fin d) (k l : ℤ) :
    (translateLift s (k - s.k i j) (l - s.l i j)).point i j =
      liftedPoint d i j k l := by
  simp only [LiftData.point, translateLift, liftedPoint]
  congr <;> ring

/-- Force a finite selector into a rich pool while reserving one prescribed
selected point literally. -/
theorem finiteSelector_in_rich_pool_through {d : ℕ} (hd : d ≠ 0)
    (s : LiftData d) (P : Set RatPoint) (hP : Rich P) (hs : s.Separated)
    (i₀ j₀ : Fin d) (hbase : s.point i₀ j₀ ∈ P) :
    ∃ t : LiftData d, t.Separated ∧ (∀ i j, t.point i j ∈ P) ∧
      t.point i₀ j₀ = s.point i₀ j₀ := by
  have havail : ∀ i j, ∃ k l a b : ℤ,
      k = s.k i j + d * a ∧ l = s.l i j + d * b ∧
      liftedPoint d i j k l ∈ P ∧
      ((i, j) = (i₀, j₀) → k = s.k i₀ j₀ ∧ l = s.l i₀ j₀) := by
    intro i j
    by_cases hij : (i, j) = (i₀, j₀)
    · have hi : i = i₀ := congrArg Prod.fst hij
      have hj : j = j₀ := congrArg Prod.snd hij
      refine ⟨s.k i j, s.l i j, 0, 0, by simp, by simp, ?_, ?_⟩
      · change s.point i j ∈ P
        simpa [hi, hj] using hbase
      · intro hij'
        have hi' : i = i₀ := congrArg Prod.fst hij'
        have hj' : j = j₀ := congrArg Prod.snd hij'
        simp [hi', hj']
    · rcases (hP d hd i j (s.k i j) (s.l i j)).nonempty with ⟨x, hx⟩
      rcases hx with ⟨k, l, rfl, hk, hl, hp⟩
      rcases Int.modEq_iff_add_fac.mp hk with ⟨a, ha⟩
      rcases Int.modEq_iff_add_fac.mp hl with ⟨b, hb⟩
      exact ⟨k, l, a, b, ha, hb, hp, fun h ↦ (hij h).elim⟩
  choose k l a b hk hl hp hkeep using havail
  let t : LiftData d := ⟨k, l⟩
  have hst : s.Congruent t := by
    intro i j
    exact ⟨a i j, b i j, hk i j, hl i j⟩
  refine ⟨t, LiftData.separated_of_congruent hs hst, hp, ?_⟩
  rcases hkeep i₀ j₀ rfl with ⟨hk₀, hl₀⟩
  simp only [LiftData.point, t, hk₀, hl₀]

/-- Coordinate-level rich selector, including an optional prescribed point.
The only finite arithmetic input is `LiteralPrimeExtensionHypothesis`: every
separated finite selector extends literally and separatedly across every
prime. -/
theorem rich_selector_of_literal_prime_extensions
    (hprime : LiteralPrimeExtensionHypothesis) (P : Set RatPoint) (hP : Rich P)
    (w : Option RatPoint) (hw : ∀ x, x ∈ w → x ∈ P) :
    ∃ T : Set RatPoint, T ⊆ P ∧ IsPartial T ∧ HitsEveryIntegerTranslate T ∧
      ∀ x, x ∈ w → x ∈ T := by
  cases w with
  | none =>
      obtain ⟨s, hs, hsP⟩ := finiteSelector_in_rich_pool (by omega)
        LiftData.initialTwo P hP LiftData.initialTwo_separated
      let s₀ : PoolStage P 2 := ⟨s, hs, hsP⟩
      obtain ⟨T, hTP, hpartial, hhits, -⟩ :=
        exists_rich_selector_from_base hprime P hP (by omega) s₀
      exact ⟨T, hTP, hpartial, hhits, by simp⟩
  | some w =>
      let m := w.1.den * w.2.den
      have hm : 0 < m := Nat.mul_pos w.1.den_pos w.2.den_pos
      obtain ⟨s, -, hs⟩ := exists_multExtension hprime m hm (by omega)
        LiftData.initialTwo LiftData.initialTwo_separated
      have hD : 0 < m * 2 := Nat.mul_pos hm (by omega)
      have hden₁ : w.1.den ∣ m * 2 :=
        (dvd_mul_right w.1.den w.2.den).trans (dvd_mul_right m 2)
      have hden₂ : w.2.den ∣ m * 2 :=
        (dvd_mul_left w.2.den w.1.den).trans (dvd_mul_right m 2)
      obtain ⟨i, j, k, l, hwrep⟩ :=
        ratPoint_eq_liftedPoint w (m * 2) hD hden₁ hden₂
      let s' := translateLift s (k - s.k i j) (l - s.l i j)
      have hs' : s'.Separated := translateLift_separated s _ _ hs
      have hpoint : s'.point i j = w := by
        exact (translateLift_point_eq hD.ne' s i j k l).trans hwrep.symm
      have hwp : w ∈ P := hw w (by simp)
      obtain ⟨t, ht, htP, htpoint⟩ := finiteSelector_in_rich_pool_through hD.ne'
        s' P hP hs' i j (hpoint.symm ▸ hwp)
      let s₀ : PoolStage P (m * 2) := ⟨t, ht, htP⟩
      obtain ⟨T, hTP, hpartial, hhits, hbase⟩ :=
        exists_rich_selector_from_base hprime P hP hD.ne' s₀
      have hwT : w ∈ T := hbase ⟨(i, j), htpoint.trans hpoint⟩
      refine ⟨T, hTP, hpartial, hhits, ?_⟩
      intro x hx
      have hwx : w = x := by simpa using hx
      have hxw : x = w := hwx.symm
      simpa [hxw] using hwT

end

end Selector

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorFrame.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-! Transport the coordinate selector theorem to an arbitrary oriented frame. -/

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace SelectorFrame

def pairToRatPoint (q : Selector.RatPoint) : RatPoint :=
  fun i ↦ if i = 0 then q.1 else q.2

def ratPointToPair (q : RatPoint) : Selector.RatPoint :=
  (q 0, q 1)

@[simp] lemma pairToRatPoint_apply_zero (q : Selector.RatPoint) :
    pairToRatPoint q 0 = q.1 := by simp [pairToRatPoint]

@[simp] lemma pairToRatPoint_apply_one (q : Selector.RatPoint) :
    pairToRatPoint q 1 = q.2 := by simp [pairToRatPoint]

@[simp] lemma pairToRatPoint_ratPointToPair (q : RatPoint) :
    pairToRatPoint (ratPointToPair q) = q := by
  funext i
  fin_cases i <;> simp [pairToRatPoint, ratPointToPair]

def framePoint (L : OrientedFrame) (q : Selector.RatPoint) : Point :=
  L.fromCoords (ratPoint (pairToRatPoint q))

lemma pairToRatPoint_liftedPoint (d : ℕ) (i j : Fin d) (k l : ℤ) :
    pairToRatPoint (Selector.liftedPoint d i j k l) =
      (fun r : Fin 2 ↦ if r = 0 then ((i : ℕ) : ℚ) / d + k
        else ((j : ℕ) : ℚ) / d + l) := by
  funext r
  fin_cases r <;> simp [pairToRatPoint, Selector.liftedPoint]

def coordinatePool (L : OrientedFrame) (P : Set Point) : Set Selector.RatPoint :=
  {q | framePoint L q ∈ P}

lemma coordinatePool_rich (L : OrientedFrame) (P : Set Point)
    (hP : Global.FrameRich L P) : Selector.Rich (coordinatePool L P) := by
  intro d hd i j a b
  let A : Set Selector.RatPoint := {q | ∃ k l : ℤ,
    q = Selector.liftedPoint d i j k l ∧
    a ≡ k [ZMOD d] ∧ b ≡ l [ZMOD d] ∧ q ∈ coordinatePool L P}
  let B : Set Point := {x | ∃ k l : ℤ,
    x = L.fromCoords
      (ratPoint (fun r ↦ if r = 0 then (i : ℕ) / d + k else (j : ℕ) / d + l)) ∧
    a ≡ k [ZMOD d] ∧ b ≡ l [ZMOD d] ∧ x ∈ P}
  have hB : B.Infinite := hP d hd i j a b
  have hsub : B ⊆ framePoint L '' A := by
    rintro x ⟨k, l, rfl, hk, hl, hp⟩
    let q := Selector.liftedPoint d i j k l
    refine ⟨q, ⟨k, l, rfl, hk, hl, ?_⟩, ?_⟩
    · change framePoint L q ∈ P
      simpa [framePoint, q, pairToRatPoint_liftedPoint] using hp
    · simp [framePoint, q, pairToRatPoint_liftedPoint]
  have himage : (framePoint L '' A).Infinite := hB.mono hsub
  have hA : A.Infinite := by
    by_contra hn
    exact (Set.not_infinite.mp hn).image (framePoint L) |>.not_infinite himage
  exact hA

lemma distSq_framePoint (L : OrientedFrame) (q r : Selector.RatPoint) :
    distSq (framePoint L q) (framePoint L r) = (Selector.sqDist q r : ℝ) := by
  rw [framePoint, framePoint, L.distSq_fromCoords]
  simp [distSq, Selector.sqDist, Fin.sum_univ_two, pairToRatPoint, ratPoint]

def frameSet (L : OrientedFrame) (T : Set Selector.RatPoint) : Set Point :=
  framePoint L '' T

lemma frameSet_subset (L : OrientedFrame) (P : Set Point)
    {T : Set Selector.RatPoint} (hT : T ⊆ coordinatePool L P) :
    frameSet L T ⊆ P := by
  rintro x ⟨q, hq, rfl⟩
  exact hT hq

lemma frameSet_partial (L : OrientedFrame) {T : Set Selector.RatPoint}
    (hT : Selector.IsPartial T) : IsPartialSteinhaus (frameSet L T) := by
  rintro p ⟨q, hq, rfl⟩ r ⟨s, hs, rfl⟩ hpq n hn
  have hqs : q ≠ s := fun h ↦ hpq (congrArg (framePoint L) h)
  have hnot := hT hq hs hqs
  apply hnot
  refine ⟨n, ?_⟩
  have hreal : (Selector.sqDist q s : ℝ) = (n : ℝ) := by
    rw [← distSq_framePoint L q s]
    exact hn
  exact_mod_cast hreal

lemma residue_eq_gives_int_translate {q r : Selector.RatPoint}
    (h : Selector.residue q = Selector.residue r) :
    ∃ z : IntPoint, pairToRatPoint q = pairToRatPoint r + fun i ↦ (z i : ℚ) := by
  have h₀ := congrArg Prod.fst h
  have h₁ := congrArg Prod.snd h
  have hm₀ := QuotientAddGroup.eq_iff_sub_mem.mp h₀
  have hm₁ := QuotientAddGroup.eq_iff_sub_mem.mp h₁
  rw [AddSubgroup.mem_zmultiples_iff] at hm₀ hm₁
  rcases hm₀ with ⟨z₀, hz₀⟩
  rcases hm₁ with ⟨z₁, hz₁⟩
  simp only [zsmul_eq_mul, mul_one] at hz₀ hz₁
  let z : IntPoint := fun i ↦ if i = 0 then z₀ else z₁
  refine ⟨z, ?_⟩
  funext i
  fin_cases i
  · simp [pairToRatPoint, z] at hz₀ ⊢
    rw [hz₀]
    ring
  · simp [pairToRatPoint, z] at hz₁ ⊢
    rw [hz₁]
    ring

lemma frameSet_hits (L : OrientedFrame) {T : Set Selector.RatPoint}
    (hT : Selector.HitsEveryIntegerTranslate T) :
    Global.HitsRationalTranslates (frameSet L T) L := by
  intro q
  obtain ⟨r, hrT, hr⟩ := hT (ratPointToPair q)
  obtain ⟨z, hz⟩ := residue_eq_gives_int_translate hr
  refine ⟨framePoint L r, ⟨⟨r, hrT, rfl⟩, ?_⟩⟩
  refine ⟨z, ?_⟩
  apply congrArg L.fromCoords
  ext i
  have hzi := congrFun hz i
  rw [pairToRatPoint_ratPointToPair] at hzi
  change (pairToRatPoint r i : ℝ) = (q i : ℝ) + (z i : ℝ)
  exact_mod_cast hzi

/-- The coordinate direct-limit theorem, transported to arbitrary oriented
frames. -/
theorem richSelectorTheorem_of_literalPrimeExtension :
    Selector.LiteralPrimeExtensionHypothesis → Global.RichSelectorTheorem := by
  intro hprime L P hP hrat w hw
  have hcoordRich : Selector.Rich (coordinatePool L P) := coordinatePool_rich L P hP
  cases w with
  | none =>
      obtain ⟨Tq, hTqP, hTqpartial, hTqhits, -⟩ :=
        Selector.rich_selector_of_literal_prime_extensions hprime
          (coordinatePool L P) hcoordRich none (by simp)
      refine ⟨frameSet L Tq, frameSet_subset L P hTqP,
        frameSet_partial L hTqpartial, frameSet_hits L hTqhits, ?_⟩
      intro x hx
      simp at hx
  | some w =>
      have hwP : w ∈ P := hw w rfl
      obtain ⟨q, hq⟩ := hrat w hwP
      let r : Selector.RatPoint := ratPointToPair q
      have hframe : framePoint L r = w := by
        dsimp only [r, framePoint]
        rw [pairToRatPoint_ratPointToPair]
        exact hq.symm
      have hrP : r ∈ coordinatePool L P := by
        change framePoint L r ∈ P
        rwa [hframe]
      have hopt : ∀ x, x ∈ (some r : Option Selector.RatPoint) →
          x ∈ coordinatePool L P := by
        intro x hx
        have hrx : r = x := by simpa using hx
        simpa [← hrx] using hrP
      obtain ⟨Tq, hTqP, hTqpartial, hTqhits, hTqr⟩ :=
        Selector.rich_selector_of_literal_prime_extensions hprime
          (coordinatePool L P) hcoordRich (some r) hopt
      have hrTq : r ∈ Tq := hTqr r (by simp)
      have hwT : w ∈ frameSet L Tq := by
        exact ⟨r, hrTq, hframe⟩
      refine ⟨frameSet L Tq, frameSet_subset L P hTqP,
        frameSet_partial L hTqpartial, frameSet_hits L hTqhits, ?_⟩
      intro x hx
      have hwx : w = x := Option.some.inj hx
      rwa [← hwx]

end SelectorFrame

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/FinalAssembly.lean` -/

section
/-!
# Final conditional assembly for Erdős Problem 215

This module isolates the last composition step.  Once the literal finite
prime-extension theorem is supplied, the arithmetic selector, Davies global
construction, rational-rotation transfer, and inverse-motion bridge produce
the strong Jackson--Mauldin conclusion used by the public theorem.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The literal finite prime-extension theorem implies the strong
Jackson--Mauldin conclusion. -/
theorem exists_partial_hitsEveryLattice_of_literalPrimeExtension
    (hprime : Selector.LiteralPrimeExtensionHypothesis) :
    ∃ S : Set Point, IsPartialSteinhaus S ∧ HitsEveryLattice S := by
  let selector : Global.RichSelectorTheorem :=
    SelectorFrame.richSelectorTheorem_of_literalPrimeExtension hprime
  obtain ⟨S, hpartial, hclasses⟩ :=
    Global.CodedDavies.global_rational_classes selector
  refine ⟨S, hpartial, hitsEveryLattice_of_hitsEveryRationalClass ?_⟩
  intro L K hKL
  exact hclasses L K hKL

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorModular.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
Modular arithmetic infrastructure for the nontrivial-prime selector step.

The source proof repeatedly localizes from a modulus `d` to one full
prime-power factor `p ^ a`, and then reconstructs residues by the Chinese
remainder theorem.  `PrimaryComponent` records exactly the factorization
data those operations need.  Keeping the coprimality witness in the
structure avoids introducing a separate valuation API into the selector
proof.
-/

namespace Selector.Modular

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- A root of `-1` modulo an arbitrary modulus.  This is an abbreviation of
a subtype so its coercion to `ZMod d` remains transparent to elaboration. -/
abbrev Root (d : ℕ) := {x : ZMod d // x ^ 2 = -1}

/-- A full primary component `p ^ a` of `d`, with its coprime complementary
factor.  The exponent is positive, while the complementary factor may be
one. -/
structure PrimaryComponent (d : ℕ) where
  p : ℕ
  a : ℕ
  D : ℕ
  prime : p.Prime
  exp_pos : 0 < a
  factor : d = p ^ a * D
  coprime : (p ^ a).Coprime D

namespace PrimaryComponent

/-- The prime-power modulus represented by a component. -/
def q {d : ℕ} (c : PrimaryComponent d) : ℕ := c.p ^ c.a

lemma q_pos {d : ℕ} (c : PrimaryComponent d) : 0 < c.q := by
  exact pow_pos c.prime.pos _

lemma q_ne_zero {d : ℕ} (c : PrimaryComponent d) : c.q ≠ 0 :=
  Nat.ne_of_gt c.q_pos

lemma factor_q {d : ℕ} (c : PrimaryComponent d) : d = c.q * c.D := by
  exact c.factor

lemma q_dvd {d : ℕ} (c : PrimaryComponent d) : c.q ∣ d := by
  exact ⟨c.D, c.factor⟩

lemma D_dvd {d : ℕ} (c : PrimaryComponent d) : c.D ∣ d := by
  refine ⟨c.q, ?_⟩
  calc
    d = c.q * c.D := c.factor_q
    _ = c.D * c.q := Nat.mul_comm _ _

/-- Reduction from the global modulus to this prime-power component. -/
def reduce {d : ℕ} (c : PrimaryComponent d) : ZMod d →+* ZMod c.q :=
  ZMod.castHom c.q_dvd (ZMod c.q)

@[simp] lemma reduce_natCast {d : ℕ} (c : PrimaryComponent d) (n : ℕ) :
    c.reduce (n : ZMod d) = (n : ZMod c.q) := by
  simp [reduce]

@[simp] lemma reduce_intCast {d : ℕ} (c : PrimaryComponent d) (z : ℤ) :
    c.reduce (z : ZMod d) = (z : ZMod c.q) := by
  simp [reduce]

@[simp] lemma reduce_neg {d : ℕ} (c : PrimaryComponent d) (x : ZMod d) :
    c.reduce (-x) = -c.reduce x := by
  exact map_neg c.reduce x

@[simp] lemma reduce_sub {d : ℕ} (c : PrimaryComponent d) (x y : ZMod d) :
    c.reduce (x - y) = c.reduce x - c.reduce y := by
  exact map_sub c.reduce x y

@[simp] lemma reduce_pow {d : ℕ} (c : PrimaryComponent d) (x : ZMod d) (n : ℕ) :
    c.reduce (x ^ n) = c.reduce x ^ n := by
  exact map_pow c.reduce x n

/-- Reducing a global root gives a root on every primary component. -/
def reduceRoot {d : ℕ} (c : PrimaryComponent d) (lam : Root d) : Root c.q :=
  ⟨c.reduce lam.1, by
    rw [← map_pow, lam.property]
    simp⟩

@[simp] lemma coe_reduceRoot {d : ℕ} (c : PrimaryComponent d) (lam : Root d) :
    (c.reduceRoot lam : ZMod c.q) = c.reduce lam.1 := rfl

lemma isUnit_D {d : ℕ} (c : PrimaryComponent d) : IsUnit (c.D : ZMod c.q) := by
  rw [ZMod.isUnit_iff_coprime]
  exact c.coprime.symm

/-- The source's localized quotient `[z/d]_(p^a)`, specialized to a primary
component `d = p^a D`. -/
def localQuotient {d : ℕ} (c : PrimaryComponent d) (z : ℤ) : ZMod c.q :=
  localizedQuotient c.q (c.D : ZMod c.q)⁻¹ z

/-- Clearing the complementary denominator recovers the ordinary quotient.
This lemma is the cancellation step behind equations (4.6) and (4.13). -/
lemma localQuotient_mul_D {d : ℕ} (c : PrimaryComponent d) (z : ℤ) :
    c.localQuotient z * (c.D : ZMod c.q) = (z / (c.q : ℤ) : ℤ) := by
  simp only [localQuotient, localizedQuotient, mul_assoc]
  rw [ZMod.inv_mul_of_unit _ c.isUnit_D]
  simp

/-- CRT splitting for the factorization stored by a primary component. -/
def split {d : ℕ} (c : PrimaryComponent d) :
    ZMod d ≃+* ZMod c.q × ZMod c.D :=
  (ZMod.ringEquivCongr c.factor_q).trans (ZMod.chineseRemainder c.coprime)

/-- CRT reconstruction for the factorization stored by a primary component. -/
def combine {d : ℕ} (c : PrimaryComponent d) (x : ZMod c.q) (y : ZMod c.D) :
    ZMod d :=
  c.split.symm (x, y)

@[simp] lemma split_combine {d : ℕ} (c : PrimaryComponent d)
    (x : ZMod c.q) (y : ZMod c.D) : c.split (c.combine x y) = (x, y) := by
  exact c.split.apply_symm_apply (x, y)

@[simp] lemma combine_split {d : ℕ} (c : PrimaryComponent d) (x : ZMod d) :
    c.combine (c.split x).1 (c.split x).2 = x := by
  exact c.split.symm_apply_apply x

@[simp] lemma split_combine_fst {d : ℕ} (c : PrimaryComponent d)
    (x : ZMod c.q) (y : ZMod c.D) : (c.split (c.combine x y)).1 = x := by
  simp

@[simp] lemma split_combine_snd {d : ℕ} (c : PrimaryComponent d)
    (x : ZMod c.q) (y : ZMod c.D) : (c.split (c.combine x y)).2 = y := by
  simp

/-- Reconstruct a global root from roots on one primary component and its
coprime complement. -/
def combineRoot {d : ℕ} (c : PrimaryComponent d)
    (x : Root c.q) (y : Root c.D) : Root d :=
  ⟨c.combine x.1 y.1, by
    apply c.split.injective
    simp only [map_pow, split_combine, map_neg, map_one]
    change (x.1 ^ 2, y.1 ^ 2) = ((-1 : ZMod c.q), (-1 : ZMod c.D))
    exact Prod.ext x.property y.property⟩

@[simp] lemma split_combineRoot {d : ℕ} (c : PrimaryComponent d)
    (x : Root c.q) (y : Root c.D) :
    c.split (c.combineRoot x y) = ((x : ZMod c.q), (y : ZMod c.D)) := by
  exact c.split_combine x.1 y.1

end PrimaryComponent

/-- Pairwise CRT in the construction direction. -/
def crt {m n : ℕ} (h : m.Coprime n) (x : ZMod m) (y : ZMod n) :
    ZMod (m * n) :=
  (ZMod.chineseRemainder h).symm (x, y)

@[simp] lemma chineseRemainder_crt {m n : ℕ} (h : m.Coprime n)
    (x : ZMod m) (y : ZMod n) :
    (ZMod.chineseRemainder h) (crt h x y) = (x, y) := by
  exact (ZMod.chineseRemainder h).apply_symm_apply (x, y)

/-- Pairwise CRT preserves the equation `x² = -1`. -/
def crtRoot {m n : ℕ} (h : m.Coprime n) (x : Root m) (y : Root n) :
    Root (m * n) :=
  ⟨crt h x.1 y.1, by
    apply (ZMod.chineseRemainder h).injective
    simp only [map_pow, chineseRemainder_crt, map_neg, map_one]
    change (x.1 ^ 2, y.1 ^ 2) = ((-1 : ZMod m), (-1 : ZMod n))
    exact Prod.ext x.property y.property⟩

@[simp] lemma chineseRemainder_crtRoot {m n : ℕ} (h : m.Coprime n)
    (x : Root m) (y : Root n) :
    (ZMod.chineseRemainder h) (crtRoot h x y) =
      ((x : ZMod m), (y : ZMod n)) := by
  exact chineseRemainder_crt h x.1 y.1

/-- The canonical numerator `(1 + λ.val²) / d` attached to a root. -/
def rootQuotient {d : ℕ} (lam : Root d) : ℕ :=
  (1 + ZMod.val lam.1 ^ 2) / d

lemma root_dvd_one_add_val_sq {d : ℕ} (hd : d ≠ 0) (lam : Root d) :
    d ∣ 1 + ZMod.val lam.1 ^ 2 := by
  let _ : NeZero d := ⟨hd⟩
  apply (ZMod.natCast_eq_zero_iff (1 + ZMod.val lam.1 ^ 2) d).mp
  push_cast
  rw [ZMod.natCast_zmod_val]
  rw [lam.property]
  simp

lemma mul_rootQuotient {d : ℕ} (hd : d ≠ 0) (lam : Root d) :
    d * rootQuotient lam = 1 + ZMod.val lam.1 ^ 2 := by
  exact Nat.mul_div_cancel' (root_dvd_one_add_val_sq hd lam)

/-- The modular half of `(1 + λ.val²) / d` occurring in (4.4). -/
def rootPhase {d : ℕ} (lam : Root d) : ZMod d :=
  (2 : ZMod d)⁻¹ * (rootQuotient lam : ZMod d)

lemma two_mul_rootPhase {d : ℕ} (h2 : Nat.Coprime 2 d) (lam : Root d) :
    (2 : ZMod d) * rootPhase lam = (rootQuotient lam : ZMod d) := by
  have hinv : (2 : ZMod d) * (2 : ZMod d)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one 2 h2
  simp only [rootPhase, ← mul_assoc, hinv, one_mul]

/-- Every root of `-1` is a unit, over an arbitrary commutative residue
ring (no primality assumption is required). -/
lemma root_isUnit {d : ℕ} (lam : Root d) : IsUnit (lam : ZMod d) := by
  refine ⟨⟨lam.1, -lam.1, ?_, ?_⟩, rfl⟩
  · change lam.1 * -lam.1 = 1
    rw [mul_neg, ← pow_two, lam.property]
    simp
  · change -lam.1 * lam.1 = 1
    rw [neg_mul, ← pow_two, lam.property]
    simp

end

end Selector.Modular

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorFinal.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
The line-family interface for the nontrivial-prime part of the
Jackson--Mauldin selector construction.

This file keeps formulas (4.4) and (4.6) literal.  Line maps are constructed
as raw functions; goodness packages them into permutations only afterwards.
-/

namespace Selector.Final

open Erdos215.Selector
open Erdos215.Selector.Modular

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

def rootVal {d : ℕ} (_hd : d ≠ 0) (lam : Root d) : ℕ := by
  letI : NeZero d := ⟨_hd⟩
  exact (lam : ZMod d).val

@[simp] lemma rootVal_cast {d : ℕ} (hd : d ≠ 0) (lam : Root d) :
    (rootVal hd lam : ZMod d) = lam := by
  let _ : NeZero d := ⟨hd⟩
  exact ZMod.natCast_zmod_val _

/-- The canonical residue `j` on the line with root `lam` and label `jtilde`. -/
def lineResidue {d : ℕ} (hd : d ≠ 0) (lam : Root d) (jtilde i : Fin d) : Fin d :=
  ⟨((jtilde : ℕ) + rootVal hd lam * (i : ℕ)) % d,
    Nat.mod_lt _ (Nat.pos_of_ne_zero hd)⟩

/-- The canonical integer `m` in
`j = jtilde + lam * i - m*d`. -/
def lineCarry {d : ℕ} (hd : d ≠ 0) (lam : Root d) (jtilde i : Fin d) : ℕ :=
  ((jtilde : ℕ) + rootVal hd lam * (i : ℕ)) / d

@[simp] lemma lineResidue_cast {d : ℕ} (hd : d ≠ 0) (lam : Root d)
    (jtilde i : Fin d) :
    ((lineResidue hd lam jtilde i : ℕ) : ZMod d) =
      ((jtilde : ℕ) : ZMod d) + (lam : ZMod d) * ((i : ℕ) : ZMod d) := by
  let _ : NeZero d := ⟨hd⟩
  change (((((jtilde : ℕ) + rootVal hd lam * (i : ℕ)) % d) : ℕ) : ZMod d) = _
  rw [ZMod.natCast_mod]
  push_cast
  rw [rootVal_cast]

/-- Equation (4.5) makes the two canonical line residues literally equal. -/
lemma lineResidue_eq_of_relation {d : ℕ} (hd : d ≠ 0) (lam₁ lam₂ : Root d)
    (j₁ j₂ i : Fin d)
    (hline : ((i : ℕ) : ZMod d) * ((lam₁ : ZMod d) - lam₂) =
      -(((j₁ : ℕ) : ZMod d) - ((j₂ : ℕ) : ZMod d))) :
    lineResidue hd lam₁ j₁ i = lineResidue hd lam₂ j₂ i := by
  let _ : NeZero d := ⟨hd⟩
  apply Fin.ext
  have hsum :
      ((j₁ : ℕ) : ZMod d) + (lam₁ : ZMod d) * ((i : ℕ) : ZMod d) =
        ((j₂ : ℕ) : ZMod d) + (lam₂ : ZMod d) * ((i : ℕ) : ZMod d) := by
    linear_combination hline
  have hcast :
      (((lineResidue hd lam₁ j₁ i : Fin d) : ℕ) : ZMod d) =
        (((lineResidue hd lam₂ j₂ i : Fin d) : ℕ) : ZMod d) := by
    rw [lineResidue_cast, lineResidue_cast, hsum]
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt (lineResidue hd lam₁ j₁ i).isLt,
    ZMod.val_natCast_of_lt (lineResidue hd lam₂ j₂ i).isLt] at hv
  exact hv

lemma lineResidue_add_mul_lineCarry {d : ℕ} (hd : d ≠ 0) (lam : Root d)
    (jtilde i : Fin d) :
    (lineResidue hd lam jtilde i : ℕ) + d * lineCarry hd lam jtilde i =
      (jtilde : ℕ) + rootVal hd lam * (i : ℕ) := by
  change (((jtilde : ℕ) + rootVal hd lam * (i : ℕ)) % d) +
      d * (((jtilde : ℕ) + rootVal hd lam * (i : ℕ)) / d) = _
  exact Nat.mod_add_div _ _

lemma lineResidue_int_equation {d : ℕ} (hd : d ≠ 0) (lam : Root d)
    (jtilde i : Fin d) :
    ((lineResidue hd lam jtilde i : ℕ) : ℤ) =
      (jtilde : ℕ) + (rootVal hd lam : ℤ) * (i : ℕ) -
        lineCarry hd lam jtilde i * d := by
  have h := lineResidue_add_mul_lineCarry hd lam jtilde i
  rw [mul_comm (lineCarry hd lam jtilde i : ℤ) (d : ℤ)]
  omega

/-- Subtracting the two canonical line equations gives the carry identity
used in the full substitution proof of (4.6). -/
lemma lineCarry_sub_relation {d : ℕ} (hd : d ≠ 0) (lam₁ lam₂ : Root d)
    (j₁ j₂ i : Fin d)
    (hj : lineResidue hd lam₁ j₁ i = lineResidue hd lam₂ j₂ i) :
    (d : ℤ) * ((lineCarry hd lam₁ j₁ i : ℤ) - lineCarry hd lam₂ j₂ i) =
      (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) +
        ((rootVal hd lam₁ : ℤ) - rootVal hd lam₂) * (i : ℕ) := by
  have h₁ := lineResidue_int_equation hd lam₁ j₁ i
  have h₂ := lineResidue_int_equation hd lam₂ j₂ i
  rw [hj] at h₁
  linear_combination h₁ - h₂

/-- A localized quotient of an actual multiple of the global modulus is the
corresponding integer, modulo the selected primary component. -/
lemma PrimaryComponent.localQuotient_mul_modulus {d : ℕ} (c : PrimaryComponent d)
    (a : ℤ) : c.localQuotient ((d : ℤ) * a) = (a : ZMod c.q) := by
  simp only [PrimaryComponent.localQuotient, localizedQuotient]
  have hcast : (d : ℤ) = (c.q : ℤ) * c.D := by
    exact_mod_cast c.factor_q
  rw [hcast, mul_assoc, Int.mul_ediv_cancel_left _ (Int.ofNat_ne_zero.mpr c.q_ne_zero)]
  push_cast
  calc
    ((c.D : ZMod c.q) * (a : ZMod c.q)) * (c.D : ZMod c.q)⁻¹ =
        (a : ZMod c.q) * ((c.D : ZMod c.q)⁻¹ * c.D) := by ring
    _ = (a : ZMod c.q) := by rw [ZMod.inv_mul_of_unit _ c.isUnit_D, mul_one]

lemma PrimaryComponent.localQuotient_add {d : ℕ} (c : PrimaryComponent d) (x y : ℤ)
    (hx : (c.q : ℤ) ∣ x) (hy : (c.q : ℤ) ∣ y) :
    c.localQuotient (x + y) = c.localQuotient x + c.localQuotient y := by
  exact localizedQuotient_add c.q c.q_ne_zero _ x y hx hy

lemma PrimaryComponent.localQuotient_mul_right {d : ℕ} (c : PrimaryComponent d)
    (x a : ℤ) (hx : (c.q : ℤ) ∣ x) :
    c.localQuotient (x * a) = c.localQuotient x * (a : ZMod c.q) := by
  rcases hx with ⟨b, rfl⟩
  simp only [PrimaryComponent.localQuotient]
  rw [mul_assoc, localizedQuotient_mul c.q c.q_ne_zero,
    localizedQuotient_mul c.q c.q_ne_zero]
  push_cast
  ring

/-- Difference of the two exact root quotients before modular division by
two. -/
lemma rootQuotient_sub_relation {d : ℕ} (hd : d ≠ 0) (lam₁ lam₂ : Root d) :
    (d : ℤ) * (((rootQuotient lam₁ : ℕ) : ℤ) - rootQuotient lam₂) =
      ((rootVal hd lam₁ : ℤ) - rootVal hd lam₂) *
        ((rootVal hd lam₁ : ℤ) + rootVal hd lam₂) := by
  have h₁ : (d : ℤ) * (rootQuotient lam₁ : ℕ) =
      1 + (rootVal hd lam₁ : ℤ) ^ 2 := by
    exact_mod_cast mul_rootQuotient hd lam₁
  have h₂ : (d : ℤ) * (rootQuotient lam₂ : ℕ) =
      1 + (rootVal hd lam₂ : ℤ) ^ 2 := by
    exact_mod_cast mul_rootQuotient hd lam₂
  linear_combination h₁ - h₂

/-- Primary-component form of the `h_d` subtraction in the consistency
calculation. -/
lemma two_mul_reduce_rootPhase_sub {d : ℕ} (hd : d ≠ 0) (hodd : Nat.Coprime 2 d)
    (c : PrimaryComponent d) (lam₁ lam₂ : Root d) :
    (2 : ZMod c.q) * c.reduce (rootPhase lam₁ - rootPhase lam₂) =
      c.localQuotient
        (((rootVal hd lam₁ : ℤ) - rootVal hd lam₂) *
          ((rootVal hd lam₁ : ℤ) + rootVal hd lam₂)) := by
  have h₁ := congrArg c.reduce (two_mul_rootPhase hodd lam₁)
  have h₂ := congrArg c.reduce (two_mul_rootPhase hodd lam₂)
  simp only [map_mul, map_ofNat, PrimaryComponent.reduce_natCast] at h₁ h₂
  rw [PrimaryComponent.reduce_sub]
  have hphase :
      (2 : ZMod c.q) * (c.reduce (rootPhase lam₁) - c.reduce (rootPhase lam₂)) =
        (((rootQuotient lam₁ : ℕ) : ℤ) - rootQuotient lam₂ : ℤ) := by
    push_cast
    linear_combination h₁ - h₂
  rw [hphase]
  have hroot := rootQuotient_sub_relation hd lam₁ lam₂
  rw [← hroot, Erdos215.Selector.Final.PrimaryComponent.localQuotient_mul_modulus]

lemma PrimaryComponent.reduce_root_eq_rootVal {d : ℕ} (hd : d ≠ 0)
    (c : PrimaryComponent d) (lam : Root d) :
    c.reduce lam = (rootVal hd lam : ZMod c.q) := by
  rw [← rootVal_cast hd lam]
  exact c.reduce_natCast _

/-- The two divisibilities implicit in the localized quotient in (4.6). -/
lemma PrimaryComponent.relation_divisibility {d : ℕ} (hd : d ≠ 0)
    (c : PrimaryComponent d) (lam₁ lam₂ : Root d) (j₁ j₂ i : Fin d)
    (hr : c.reduce lam₁ = c.reduce lam₂)
    (hline : ((i : ℕ) : ZMod d) * ((lam₁ : ZMod d) - lam₂) =
      -(((j₁ : ℕ) : ZMod d) - ((j₂ : ℕ) : ZMod d))) :
    (c.q : ℤ) ∣ (rootVal hd lam₁ : ℤ) - rootVal hd lam₂ ∧
      (c.q : ℤ) ∣ (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) := by
  have hrv₁ := Erdos215.Selector.Final.PrimaryComponent.reduce_root_eq_rootVal hd c lam₁
  have hrv₂ := Erdos215.Selector.Final.PrimaryComponent.reduce_root_eq_rootVal hd c lam₂
  have hdelta0 :
      (((rootVal hd lam₁ : ℤ) - rootVal hd lam₂ : ℤ) : ZMod c.q) = 0 := by
    push_cast
    rw [← hrv₁, ← hrv₂, hr, sub_self]
  have hdelta : (c.q : ℤ) ∣ (rootVal hd lam₁ : ℤ) - rootVal hd lam₂ :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hdelta0
  constructor
  · exact hdelta
  have hred := congrArg c.reduce hline
  simp only [map_mul, map_sub, map_neg, PrimaryComponent.reduce_natCast] at hred
  rw [hr, sub_self, mul_zero] at hred
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  linear_combination hred

/-- The right side of the source's line formula (4.4). -/
def lineValue {d : ℕ} (hd : d ≠ 0) (s : LiftData d) (lam : Root d)
    (jtilde i : Fin d) : ZMod d :=
  let j := lineResidue hd lam jtilde i
  (s.k i j : ZMod d) + (lam : ZMod d) * (s.l i j : ZMod d) -
      (lam : ZMod d) * (lineCarry hd lam jtilde i : ZMod d) +
    rootPhase lam * (i : ℕ)

/-- The raw induced line map. -/
def inducedLineMap {d : ℕ} (hd : d ≠ 0) (s : LiftData d) (lam : Root d)
    (jtilde : Fin d) : Fin d → Fin d := by
  let _ : NeZero d := ⟨hd⟩
  exact fun i ↦ ⟨(lineValue hd s lam jtilde i).val,
    ZMod.val_lt (lineValue hd s lam jtilde i)⟩

@[simp] lemma inducedLineMap_cast {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (lam : Root d) (jtilde i : Fin d) :
    ((inducedLineMap hd s lam jtilde i : ℕ) : ZMod d) = lineValue hd s lam jtilde i := by
  let _ : NeZero d := ⟨hd⟩
  exact ZMod.natCast_zmod_val _

/-- A raw family indexed by every root and every line label. -/
abbrev RawLineFamily (d : ℕ) := Root d → Fin d → Fin d → Fin d

def FamilyGood {d : ℕ} (F : RawLineFamily d) : Prop :=
  ∀ lam jtilde, GoodMap d (F lam jtilde)

/-- Componentwise form of the source's consistency equation (4.6). -/
def FamilyConsistent {d : ℕ} (F : RawLineFamily d) : Prop :=
  ∀ (c : PrimaryComponent d) (lam₁ lam₂ : Root d) (j₁ j₂ i : Fin d),
    c.reduce lam₁ = c.reduce lam₂ →
    ((i : ℕ) : ZMod d) * ((lam₁ : ZMod d) - lam₂) =
        -(((j₁ : ℕ) : ZMod d) - ((j₂ : ℕ) : ZMod d)) →
    c.reduce (((F lam₁ j₁ i : Fin d) : ℕ) : ZMod d) -
        c.reduce (((F lam₂ j₂ i : Fin d) : ℕ) : ZMod d) =
      -(c.reduce lam₁) * c.localQuotient (((j₁ : ℕ) : ℤ) - (j₂ : ℕ))

/-- Package a good raw family into actual permutations. -/
noncomputable def FamilyGood.toPermFamily {d : ℕ} (F : RawLineFamily d)
    (hF : FamilyGood F) : Root d → Fin d → Equiv.Perm (Fin d) :=
  fun lam jtilde ↦ GoodMap.toPerm (F lam jtilde) (hF lam jtilde)

@[simp] lemma FamilyGood.toPermFamily_apply {d : ℕ} (F : RawLineFamily d)
    (hF : FamilyGood F) (lam : Root d) (jtilde i : Fin d) :
    hF.toPermFamily F lam jtilde i = F lam jtilde i := rfl

/-- The line family canonically induced by a finite selector. -/
def inducedFamily {d : ℕ} (hd : d ≠ 0) (s : LiftData d) : RawLineFamily d :=
  fun lam jtilde ↦ inducedLineMap hd s lam jtilde

/-- Formula (4.4) holds definitionally for the induced raw family. -/
theorem inducedFamily_formula {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (lam : Root d) (jtilde i : Fin d) :
    (((inducedFamily hd s lam jtilde i : Fin d) : ℕ) : ZMod d) =
      lineValue hd s lam jtilde i := by
  exact inducedLineMap_cast hd s lam jtilde i

/-- The family induced by a finite selector satisfies the exact localized
consistency identity (4.6) on every primary component. -/
theorem inducedFamily_consistent {d : ℕ} (hd : d ≠ 0) (hodd : Nat.Coprime 2 d)
    (s : LiftData d) : FamilyConsistent (inducedFamily hd s) := by
  intro c lam₁ lam₂ j₁ j₂ i hr hline
  have hj := lineResidue_eq_of_relation hd lam₁ lam₂ j₁ j₂ i hline
  have hdiv := Erdos215.Selector.Final.PrimaryComponent.relation_divisibility
    hd c lam₁ lam₂ j₁ j₂ i hr hline
  let delta : ℤ := (rootVal hd lam₁ : ℤ) - rootVal hd lam₂
  let J : ℤ := ((j₁ : ℕ) : ℤ) - (j₂ : ℕ)
  let mdelta : ℤ :=
    (lineCarry hd lam₁ j₁ i : ℤ) - lineCarry hd lam₂ j₂ i
  have hdelta : (c.q : ℤ) ∣ delta := by
    simpa [delta] using hdiv.1
  have hJ : (c.q : ℤ) ∣ J := by
    simpa [J] using hdiv.2
  have hdeltai : (c.q : ℤ) ∣ delta * (i : ℕ) :=
    dvd_mul_of_dvd_left hdelta _
  have hcarry := lineCarry_sub_relation hd lam₁ lam₂ j₁ j₂ i hj
  have hcarryLocal :
      (mdelta : ZMod c.q) =
        c.localQuotient J + c.localQuotient delta * ((i : ℕ) : ZMod c.q) := by
    rw [← Erdos215.Selector.Final.PrimaryComponent.localQuotient_mul_modulus c mdelta]
    rw [show (d : ℤ) * mdelta = J + delta * (i : ℕ) by
      simpa [mdelta, J, delta] using hcarry]
    rw [Erdos215.Selector.Final.PrimaryComponent.localQuotient_add c J
      (delta * (i : ℕ)) hJ hdeltai]
    rw [Erdos215.Selector.Final.PrimaryComponent.localQuotient_mul_right c delta
      ((i : ℕ) : ℤ) hdelta]
    push_cast
    ring_nf
  have hphase := two_mul_reduce_rootPhase_sub hd hodd c lam₁ lam₂
  have hphase' :
      (2 : ZMod c.q) * c.reduce (rootPhase lam₁ - rootPhase lam₂) =
        c.localQuotient delta *
          (((rootVal hd lam₁ : ℤ) + rootVal hd lam₂ : ℤ) : ZMod c.q) := by
    rw [hphase]
    exact Erdos215.Selector.Final.PrimaryComponent.localQuotient_mul_right c delta
      ((rootVal hd lam₁ : ℤ) + rootVal hd lam₂) hdelta
  have hsum :
      (((rootVal hd lam₁ : ℤ) + rootVal hd lam₂ : ℤ) : ZMod c.q) =
        (2 : ZMod c.q) * c.reduce lam₁ := by
    push_cast
    rw [← Erdos215.Selector.Final.PrimaryComponent.reduce_root_eq_rootVal hd c lam₁,
      ← Erdos215.Selector.Final.PrimaryComponent.reduce_root_eq_rootVal hd c lam₂, hr]
    ring
  rw [hsum] at hphase'
  have hleft :
      c.reduce (((inducedFamily hd s lam₁ j₁ i : Fin d) : ℕ) : ZMod d) -
          c.reduce (((inducedFamily hd s lam₂ j₂ i : Fin d) : ℕ) : ZMod d) =
        -(c.reduce lam₁) * (mdelta : ZMod c.q) +
          c.reduce (rootPhase lam₁ - rootPhase lam₂) * ((i : ℕ) : ZMod c.q) := by
    rw [inducedFamily_formula, inducedFamily_formula]
    simp only [lineValue, map_add, map_sub, map_mul,
      PrimaryComponent.reduce_natCast]
    rw [hj, hr]
    simp only [mdelta, Int.cast_sub, Int.cast_natCast]
    ring
  rw [hleft]
  have h2coprime : Nat.Coprime 2 c.q := hodd.of_dvd_right c.q_dvd
  have h2unit : IsUnit (2 : ZMod c.q) := by
    change IsUnit (((2 : ℕ) : ZMod c.q))
    rw [ZMod.isUnit_iff_coprime]
    exact h2coprime
  apply h2unit.mul_left_cancel
  linear_combination
    -(2 : ZMod c.q) * (c.reduce lam₁) * hcarryLocal +
      (((i : ℕ) : ZMod c.q)) * hphase'

end

end Selector.Final

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorPartialGood.lean` -/

section
namespace Selector.PartialGood

open Erdos215.Selector

set_option autoImplicit false

/-!
# The partial-good-permutation extension (Jackson--Mauldin, Lemma 4.8)

The shift in the paper is a residue modulo `d'` which is divisible by `u`.
For formal purposes we retain its chosen quotient `q`; thus the actual shift
is `u * q i` and the correction in (4.8) is definitionally `d * q i`.
-/

/-- Add the (chosen nonnegative representative of the) shift `u * q i`
modulo `N`. -/
def partialGoodShift (N u : ℕ) (q : Fin N → ℕ) (i : Fin N) : Fin N :=
  ⟨(i.1 + u * q i) % N, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.2)⟩

/-- The raw extension map in formula (4.8). -/
def partialGoodExtension (N u d : ℕ) (q : Fin N → ℕ)
    (pi : Fin N → Fin N) (i : Fin N) : Fin N :=
  ⟨((pi (partialGoodShift N u q i)).1 + d * q i) % N,
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.2)⟩

/-- Goodness of the partial map on the distinguished residue class. -/
def PartialGoodOnClass (N p i₀ : ℕ) (pi : Fin N → Fin N) : Prop :=
  ∀ i j : Fin N, i.1 % p = i₀ → j.1 % p = i₀ → i ≠ j →
    ¬(survivingModulus N (indexDiff i j) : ℤ) ∣
      (((pi i).1 : ℕ) : ℤ) - (((pi j).1 : ℕ) : ℤ)

private lemma natMod_modEq (N a : ℕ) :
    ((a % N : ℕ) : ℤ) ≡ (a : ℤ) [ZMOD (N : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  have h : (a : ℤ) = (a % N : ℕ) + (N : ℤ) * (a / N : ℕ) := by
    exact_mod_cast (Nat.mod_add_div a N).symm
  use (a / N : ℕ)
  omega

private lemma indexDiff_dvd_iff {N k : ℕ} (i j : Fin N) :
    k ∣ indexDiff i j ↔
      (k : ℤ) ∣ (((i.1 : ℕ) : ℤ) - ((j.1 : ℕ) : ℤ)) := by
  change (Int.natAbs (k : ℤ)) ∣
      Int.natAbs (((i.1 : ℕ) : ℤ) - ((j.1 : ℕ) : ℤ)) ↔ _
  rw [Int.natAbs_dvd_natAbs]

private lemma gcd_indexDiff_eq_of_modEq {N : ℕ} (i j i' j' : Fin N)
    (h : (((i.1 : ℕ) : ℤ) - ((j.1 : ℕ) : ℤ)) ≡
      (((i'.1 : ℕ) : ℤ) - ((j'.1 : ℕ) : ℤ)) [ZMOD (N : ℤ)]) :
    Nat.gcd N (indexDiff i j) = Nat.gcd N (indexDiff i' j') := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    rw [indexDiff_dvd_iff]
    have hgN : ((Nat.gcd N (indexDiff i j) : ℕ) : ℤ) ∣ (N : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left N (indexDiff i j)
    have hgij : ((Nat.gcd N (indexDiff i j) : ℕ) : ℤ) ∣
        (((i.1 : ℕ) : ℤ) - ((j.1 : ℕ) : ℤ)) := by
      rw [← indexDiff_dvd_iff]
      exact Nat.gcd_dvd_right _ _
    rw [Int.modEq_iff_dvd] at h
    rcases hgN with ⟨a, ha⟩
    rcases hgij with ⟨b, hb⟩
    rcases h with ⟨c, hc⟩
    rw [ha] at hc
    use b + a * c
    linear_combination hb + hc
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    rw [indexDiff_dvd_iff]
    have hgN : ((Nat.gcd N (indexDiff i' j') : ℕ) : ℤ) ∣ (N : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left N (indexDiff i' j')
    have hgij : ((Nat.gcd N (indexDiff i' j') : ℕ) : ℤ) ∣
        (((i'.1 : ℕ) : ℤ) - ((j'.1 : ℕ) : ℤ)) := by
      rw [← indexDiff_dvd_iff]
      exact Nat.gcd_dvd_right _ _
    rw [Int.modEq_iff_dvd] at h
    rcases hgN with ⟨a, ha⟩
    rcases hgij with ⟨b, hb⟩
    rcases h with ⟨c, hc⟩
    rw [ha] at hc
    use b - a * c
    linear_combination hb - hc

private lemma gcd_indexDiff_partialGoodShift_eq {N u : ℕ} (q : Fin N → ℕ)
    (i j : Fin N) (hq : q i = q j) :
    Nat.gcd N (indexDiff (partialGoodShift N u q i) (partialGoodShift N u q j)) =
      Nat.gcd N (indexDiff i j) := by
  symm
  apply gcd_indexDiff_eq_of_modEq
  have hi := natMod_modEq N (i.1 + u * q i)
  have hj := natMod_modEq N (j.1 + u * q j)
  have h := hi.sub hj
  rw [hq] at h
  simp only [partialGoodShift]
  rw [hq]
  convert h.symm using 1
  push_cast
  ring

private lemma partialGoodShift_ne_of_q_eq {N u : ℕ} (q : Fin N → ℕ)
    {i j : Fin N} (hij : i ≠ j) (hq : q i = q j) :
    partialGoodShift N u q i ≠ partialGoodShift N u q j := by
  intro hs
  let _ : NeZero N := ⟨Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) i.2)⟩
  have hi : (((partialGoodShift N u q i).1 : ℕ) : ZMod N) =
      (i.1 : ZMod N) + (u : ZMod N) * (q i : ℕ) := by
    simp [partialGoodShift]
  have hj : (((partialGoodShift N u q j).1 : ℕ) : ZMod N) =
      (j.1 : ZMod N) + (u : ZMod N) * (q j : ℕ) := by
    simp [partialGoodShift]
  have hc : (i.1 : ZMod N) = (j.1 : ZMod N) := by
    rw [hs] at hi
    rw [hq] at hi
    exact add_right_cancel (hi.symm.trans hj)
  apply hij
  apply Fin.ext
  have hv := congrArg ZMod.val hc
  simpa [ZMod.val_natCast_of_lt i.2, ZMod.val_natCast_of_lt j.2] using hv

private lemma gcd_indexDiff_dvd_u_of_cross
    {N p u n : ℕ} (hp : p.Prime) (hN : N = u * p ^ n)
    (i j : Fin N) (hcross : i.1 % p ≠ j.1 % p) :
    Nat.gcd N (indexDiff i j) ∣ u := by
  have hpnot : ¬p ∣ Nat.gcd N (indexDiff i j) := by
    intro hpg
    have hpidx : p ∣ indexDiff i j := hpg.trans (Nat.gcd_dvd_right _ _)
    have hpz : (p : ℤ) ∣
        (((i.1 : ℕ) : ℤ) - ((j.1 : ℕ) : ℤ)) :=
      (indexDiff_dvd_iff i j).mp hpidx
    have hpz' : (p : ℤ) ∣
        (((j.1 : ℕ) : ℤ) - ((i.1 : ℕ) : ℤ)) := by
      simpa only [neg_sub] using dvd_neg.mpr hpz
    have hm : i.1 ≡ j.1 [MOD p] := by
      rw [Nat.modEq_iff_dvd]
      exact hpz'
    exact hcross hm
  have hgp : Nat.Coprime (Nat.gcd N (indexDiff i j)) p :=
    ((hp.coprime_iff_not_dvd).2 hpnot).symm
  have hgpown : Nat.Coprime (Nat.gcd N (indexDiff i j)) (p ^ n) :=
    hgp.pow_right n
  apply hgpown.dvd_of_dvd_mul_right
  rw [← hN]
  exact Nat.gcd_dvd_left _ _

private lemma natModEq_iff_dvd_indexDiff {N : ℕ} (m : ℕ) (i j : Fin N) :
    i.1 ≡ j.1 [MOD m] ↔ m ∣ indexDiff i j := by
  rw [Nat.modEq_iff_dvd, Int.natCast_dvd]
  simp only [indexDiff]
  rw [show ((j.1 : ℤ) - i.1) = -((i.1 : ℤ) - j.1) by ring, Int.natAbs_neg]

private lemma int_dvd_sub_iff_natModEq (m a b : ℕ) :
    (m : ℤ) ∣ (a : ℤ) - (b : ℤ) ↔ a ≡ b [MOD m] := by
  rw [Nat.modEq_iff_dvd]
  constructor <;> intro h <;> simpa only [neg_sub] using dvd_neg.mpr h

private lemma partialGoodShift_natModEq (N u : ℕ) (q : Fin N → ℕ) (i : Fin N) :
    (partialGoodShift N u q i).1 ≡ i.1 + u * q i [MOD N] := by
  simp [partialGoodShift, Nat.ModEq]

private lemma partialGoodExtension_natModEq (N u d : ℕ) (q : Fin N → ℕ)
    (pi : Fin N → Fin N) (i : Fin N) :
    (partialGoodExtension N u d q pi i).1 ≡
      (pi (partialGoodShift N u q i)).1 + d * q i [MOD N] := by
  simp [partialGoodExtension, Nat.ModEq]

private lemma pow_dvd_survivingModulus_of_gcd_dvd_u {N u p n a : ℕ}
    (hN : N = u * p ^ n) (hg : Nat.gcd N a ∣ u) :
    p ^ n ∣ survivingModulus N a := by
  rw [survivingModulus, Nat.dvd_div_iff_mul_dvd (Nat.gcd_dvd_left N a)]
  have hmul : Nat.gcd N a * p ^ n ∣ u * p ^ n :=
    Nat.mul_dvd_mul_right hg (p ^ n)
  have huN : u * p ^ n ∣ N := by rw [hN]
  exact hmul.trans huN

private lemma correction_not_modEq_pow {N u d p n qi qj : ℕ} (hp : p.Prime)
    (hn : 0 < n) (hcop : Nat.Coprime p u)
    (hpd : N = p * d) (hN : N = u * p ^ n)
    (hne : ¬qi ≡ qj [MOD p]) :
    ¬d * qi ≡ d * qj [MOD p ^ n] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hd : d = u * p ^ k := by
    apply Nat.mul_left_cancel hp.pos
    calc
      p * d = N := hpd.symm
      _ = u * p ^ (k + 1) := hN
      _ = p * (u * p ^ k) := by rw [pow_succ]; ac_rfl
  intro hbad
  have hbad' : p ^ k * (u * qi) ≡ p ^ k * (u * qj) [MOD p ^ k * p] := by
    simpa [hd, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hbad
  have hu : u * qi ≡ u * qj [MOD p] :=
    hbad'.mul_left_cancel' (pow_ne_zero _ hp.ne_zero)
  exact hne (hu.cancel_left_of_coprime hcop.gcd_eq_one)

private lemma q_not_modEq_of_shift_eq_of_cross {N u p : ℕ} (q : Fin N → ℕ)
    (hpN : p ∣ N) {i j : Fin N} (hij : i.1 % p ≠ j.1 % p)
    (hshift : partialGoodShift N u q i = partialGoodShift N u q j) :
    ¬q i ≡ q j [MOD p] := by
  intro hq
  have hsi := (partialGoodShift_natModEq N u q i).of_dvd hpN
  have hsj := (partialGoodShift_natModEq N u q j).of_dvd hpN
  have hsij : (partialGoodShift N u q i).1 ≡
      (partialGoodShift N u q j).1 [MOD p] := by rw [hshift]
  have huq : u * q i ≡ u * q j [MOD p] := hq.mul_left u
  have hm : i.1 ≡ j.1 [MOD p] := by
    exact huq.add_right_cancel (hsi.symm.trans (hsij.trans hsj))
  exact hij hm

private lemma gcd_mul_p_dvd_shift_gcd {N u p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hN : N = u * p ^ n) (q : Fin N → ℕ) {i j : Fin N}
    (hij : i.1 % p ≠ j.1 % p)
    (hxi : (partialGoodShift N u q i).1 % p =
      (partialGoodShift N u q j).1 % p) :
    Nat.gcd N (indexDiff i j) * p ∣
      Nat.gcd N (indexDiff (partialGoodShift N u q i)
        (partialGoodShift N u q j)) := by
  let g := Nat.gcd N (indexDiff i j)
  have hgu : g ∣ u := gcd_indexDiff_dvd_u_of_cross hp hN i j hij
  have hgN : g ∣ N := Nat.gcd_dvd_left _ _
  have hpN : p ∣ N := by
    rw [hN]
    exact dvd_mul_of_dvd_right (dvd_pow_self p (Nat.ne_of_gt hn)) u
  have hgi : i.1 ≡ j.1 [MOD g] :=
    (natModEq_iff_dvd_indexDiff g i j).2 (Nat.gcd_dvd_right _ _)
  have hsi := (partialGoodShift_natModEq N u q i).of_dvd hgN
  have hsj := (partialGoodShift_natModEq N u q j).of_dvd hgN
  have huci : u * q i ≡ 0 [MOD g] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hgu _)
  have hucj : u * q j ≡ 0 [MOD g] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hgu _)
  have hgxy : (partialGoodShift N u q i).1 ≡
      (partialGoodShift N u q j).1 [MOD g] := by
    exact hsi.trans (((Nat.ModEq.rfl.add huci).trans (hgi.add Nat.ModEq.rfl)).trans
      ((Nat.ModEq.rfl.add hucj.symm).trans hsj.symm))
  have hgdiff : g ∣ indexDiff (partialGoodShift N u q i)
      (partialGoodShift N u q j) :=
    (natModEq_iff_dvd_indexDiff g _ _).1 hgxy
  have hpdiff : p ∣ indexDiff (partialGoodShift N u q i)
      (partialGoodShift N u q j) :=
    (natModEq_iff_dvd_indexDiff p _ _).1 hxi
  have hpg : Nat.Coprime g p :=
    (hp.coprime_iff_not_dvd.mpr (by
      intro hpg
      exact hij ((natModEq_iff_dvd_indexDiff p i j).2
        (hpg.trans (Nat.gcd_dvd_right _ _))))).symm
  apply Nat.dvd_gcd
  · exact hpg.mul_dvd_of_dvd_of_dvd hgN hpN
  · exact hpg.mul_dvd_of_dvd_of_dvd hgdiff hpdiff

private lemma gcd_indexDiff_dvd_d_of_cross {N u d p n : ℕ} (hp : p.Prime)
    (hn : 0 < n) (hpd : N = p * d) (hN : N = u * p ^ n)
    {i j : Fin N} (hij : i.1 % p ≠ j.1 % p) :
    Nat.gcd N (indexDiff i j) ∣ d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hd : d = u * p ^ k := by
    apply Nat.mul_left_cancel hp.pos
    calc
      p * d = N := hpd.symm
      _ = u * p ^ (k + 1) := hN
      _ = p * (u * p ^ k) := by rw [pow_succ]; ac_rfl
  rw [hd]
  exact dvd_mul_of_dvd_left (gcd_indexDiff_dvd_u_of_cross hp hN _ _ hij) _

private lemma div_gcd_dvd_div_gcd_of_mul_dvd {N p d g gx : ℕ}
    (hp : 0 < p) (hpd : N = p * d) (hg : g ∣ d)
    (hxN : gx ∣ N) (hgpx : g * p ∣ gx) :
    N / gx ∣ d / g := by
  rw [Nat.dvd_div_iff_mul_dvd hg]
  have hmul : (g * p) * (N / gx) ∣ gx * (N / gx) :=
    Nat.mul_dvd_mul_right hgpx (N / gx)
  have hmulN : (g * p) * (N / gx) ∣ N := by
    convert hmul using 1
    rw [Nat.mul_comm gx, Nat.div_mul_cancel hxN]
  have hcancel : p * (g * (N / gx)) ∣ p * d := by
    simpa [hpd, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmulN
  rcases hcancel with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  apply Nat.mul_left_cancel hp
  simpa [Nat.mul_assoc] using hc

/-- Jackson--Mauldin's partial-good-permutation extension lemma (Lemma 4.8),
in raw-map form.  The actual shift is `u * q i`, so `q` is the retained
integer quotient `s(i) / u`. -/
theorem partialGoodExtension_good
    {N u d p n i₀ : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hcop : Nat.Coprime p u) (hpd : N = p * d) (hN : N = u * p ^ n)
    (q : Fin N → ℕ) (pi : Fin N → Fin N)
    (hqclass : ∀ i j : Fin N, i.1 % p = j.1 % p → q i = q j)
    (hshiftClass : ∀ i : Fin N, (partialGoodShift N u q i).1 % p = i₀)
    (hpartial : PartialGoodOnClass N p i₀ pi) :
    GoodMap N (partialGoodExtension N u d q pi) := by
  intro i j hij
  rw [int_dvd_sub_iff_natModEq]
  intro hbad
  let x := partialGoodShift N u q i
  let y := partialGoodShift N u q j
  let g := Nat.gcd N (indexDiff i j)
  let gx := Nat.gcd N (indexDiff x y)
  let M := survivingModulus N (indexDiff i j)
  let Mx := survivingModulus N (indexDiff x y)
  have hMN : M ∣ N := survivingModulus_dvd _ _
  have hxClass : x.1 % p = i₀ := hshiftClass i
  have hyClass : y.1 % p = i₀ := hshiftClass j
  by_cases hs : i.1 % p = j.1 % p
  · have hq : q i = q j := hqclass i j hs
    have hxy : x ≠ y := partialGoodShift_ne_of_q_eq q hij hq
    have hg' : Nat.gcd N (indexDiff x y) = Nat.gcd N (indexDiff i j) := by
      exact gcd_indexDiff_partialGoodShift_eq q i j hq
    have hMMx : Mx = M := by simp [M, Mx, survivingModulus, hg']
    have hnot : ¬(pi x).1 ≡ (pi y).1 [MOD Mx] := by
      rw [← int_dvd_sub_iff_natModEq]
      exact hpartial x y hxClass hyClass hxy
    have hei := (partialGoodExtension_natModEq N u d q pi i).of_dvd hMN
    have hej := (partialGoodExtension_natModEq N u d q pi j).of_dvd hMN
    have hsum : (pi x).1 + d * q i ≡ (pi y).1 + d * q j [MOD M] :=
      hei.symm.trans (hbad.trans hej)
    have hpimod : (pi x).1 ≡ (pi y).1 [MOD M] := by
      rw [hq] at hsum
      exact Nat.ModEq.add_right_cancel' (d * q j) hsum
    exact hnot (hMMx ▸ hpimod)
  · have hgu : g ∣ u := gcd_indexDiff_dvd_u_of_cross hp hN i j hs
    have hgD : g ∣ d := gcd_indexDiff_dvd_d_of_cross hp hn hpd hN hs
    have hpN : p ∣ N := by rw [hpd]; exact dvd_mul_right p d
    have hpPowN : p ^ n ∣ N := by
      rw [hN]
      exact dvd_mul_left (p ^ n) u
    have hpPowM : p ^ n ∣ M :=
      pow_dvd_survivingModulus_of_gcd_dvd_u hN hgu
    by_cases hxyEq : x = y
    · have hqne : ¬q i ≡ q j [MOD p] :=
        q_not_modEq_of_shift_eq_of_cross q hpN hs hxyEq
      have hbadPow := hbad.of_dvd hpPowM
      have hei := (partialGoodExtension_natModEq N u d q pi i).of_dvd hpPowN
      have hej := (partialGoodExtension_natModEq N u d q pi j).of_dvd hpPowN
      have hsum : (pi x).1 + d * q i ≡ (pi y).1 + d * q j [MOD p ^ n] :=
        hei.symm.trans (hbadPow.trans hej)
      rw [hxyEq] at hsum
      have hcorr : d * q i ≡ d * q j [MOD p ^ n] :=
        Nat.ModEq.add_left_cancel' (pi y).1 hsum
      exact correction_not_modEq_pow hp hn hcop hpd hN hqne hcorr
    · have hgpx : g * p ∣ gx := by
        apply gcd_mul_p_dvd_shift_gcd hp hn hN q hs
        rw [hxClass, hyClass]
      have hxN : gx ∣ N := Nat.gcd_dvd_left _ _
      have hMxDg : Mx ∣ d / g :=
        div_gcd_dvd_div_gcd_of_mul_dvd hp.pos hpd hgD hxN hgpx
      have hdN : d ∣ N := by rw [hpd]; exact dvd_mul_left d p
      have hDgM : d / g ∣ M := Nat.div_dvd_div hgD hdN
      have hbadDg := hbad.of_dvd hDgM
      have hDgN : d / g ∣ N := hDgM.trans hMN
      have hei := (partialGoodExtension_natModEq N u d q pi i).of_dvd hDgN
      have hej := (partialGoodExtension_natModEq N u d q pi j).of_dvd hDgN
      have hsum : (pi x).1 + d * q i ≡ (pi y).1 + d * q j [MOD d / g] :=
        hei.symm.trans (hbadDg.trans hej)
      have hdgi : d * q i ≡ 0 [MOD d / g] :=
        Nat.modEq_zero_iff_dvd.mpr
          (dvd_mul_of_dvd_left (Nat.div_dvd_of_dvd hgD) _)
      have hdgj : d * q j ≡ 0 [MOD d / g] :=
        Nat.modEq_zero_iff_dvd.mpr
          (dvd_mul_of_dvd_left (Nat.div_dvd_of_dvd hgD) _)
      have hpimodDg : (pi x).1 ≡ (pi y).1 [MOD d / g] :=
        hdgi.add_right_cancel (hsum.trans (Nat.ModEq.rfl.add hdgj))
      have hpimodMx : (pi x).1 ≡ (pi y).1 [MOD Mx] := hpimodDg.of_dvd hMxDg
      have hnot : ¬(pi x).1 ≡ (pi y).1 [MOD Mx] := by
        rw [← int_dvd_sub_iff_natModEq]
        exact hpartial x y hxClass hyClass hxyEq
      exact hnot hpimodMx

lemma partialGoodExtension_eq_on_distinguished
    {N u d p i₀ : ℕ} (q : Fin N → ℕ) (pi : Fin N → Fin N)
    (hqzero : ∀ i : Fin N, i.1 % p = i₀ → q i = 0)
    (i : Fin N) (hi : i.1 % p = i₀) :
    partialGoodExtension N u d q pi i = pi i := by
  have hq : q i = 0 := hqzero i hi
  apply Fin.ext
  simp [partialGoodExtension, partialGoodShift, hq, Nat.mod_eq_of_lt i.2,
    Nat.mod_eq_of_lt (pi i).2]

/-- Permutation packaging of `partialGoodExtension_good`.  It is literally
value-identical to the given partial map on the distinguished class. -/
theorem exists_goodPerm_extending_partial
    {N u d p n i₀ : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hcop : Nat.Coprime p u) (hpd : N = p * d) (hN : N = u * p ^ n)
    (q : Fin N → ℕ) (pi : Fin N → Fin N)
    (hqclass : ∀ i j : Fin N, i.1 % p = j.1 % p → q i = q j)
    (hqzero : ∀ i : Fin N, i.1 % p = i₀ → q i = 0)
    (hshiftClass : ∀ i : Fin N, (partialGoodShift N u q i).1 % p = i₀)
    (hpartial : PartialGoodOnClass N p i₀ pi) :
    ∃ sigma : Equiv.Perm (Fin N), GoodPerm N sigma ∧
      ∀ i : Fin N, i.1 % p = i₀ → sigma i = pi i := by
  have hg : GoodMap N (partialGoodExtension N u d q pi) :=
    partialGoodExtension_good hp hn hcop hpd hN q pi hqclass hshiftClass hpartial
  refine ⟨GoodMap.toPerm (partialGoodExtension N u d q pi) hg,
    GoodMap.goodPerm_toPerm _ hg, ?_⟩
  intro i hi
  rw [GoodMap.toPerm_apply,
    partialGoodExtension_eq_on_distinguished q pi hqzero i hi]

end Selector.PartialGood

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorPrimeExtension.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
The explicit residue shifts used in the nontrivial prime-extension step of
Jackson--Mauldin.  Keeping the chosen digit in `0, ..., p-1` records the
literal representatives required by (4.11), (S6), and (S7).
-/

namespace Selector.PrimeExtension

open Erdos215.Selector
open Erdos215.Selector.PartialGood

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Reduction of a finite index to its source class modulo `p`. -/
def sourceClass (p : ℕ) {N : ℕ} (i : Fin N) : ZMod p := i.1

/-- The chosen digit `a` for the shift `u*a` carrying `source` to `target`
modulo `p`. -/
def shiftDigit (p u : ℕ) (target source : ZMod p) : ℕ :=
  ((target - source) * (u : ZMod p)⁻¹).val

lemma shiftDigit_lt {p u : ℕ} (hp : p.Prime) (target source : ZMod p) :
    shiftDigit p u target source < p := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  exact ZMod.val_lt _

@[simp] lemma shiftDigit_cast {p u : ℕ} (hp : p.Prime)
    (target source : ZMod p) :
    (shiftDigit p u target source : ZMod p) =
      (target - source) * (u : ZMod p)⁻¹ := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  exact ZMod.natCast_zmod_val _

lemma source_add_shiftDigit {p u : ℕ} (hp : p.Prime)
    (hu : Nat.Coprime u p) (target source : ZMod p) :
    source + (u : ZMod p) * (shiftDigit p u target source : ℕ) = target := by
  have hu' : IsUnit (u : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    exact hu
  rw [shiftDigit_cast hp]
  calc
    source + (u : ZMod p) * ((target - source) * (u : ZMod p)⁻¹) =
        source + (target - source) * ((u : ZMod p) * (u : ZMod p)⁻¹) := by ring
    _ = target := by rw [ZMod.mul_inv_of_unit _ hu']; ring

lemma shiftDigit_eq_zero_of_eq {p u : ℕ} (target source : ZMod p)
    (h : source = target) : shiftDigit p u target source = 0 := by
  simp [shiftDigit, h]

/-- The Nat-valued guide function supplied to Lemma 4.8. -/
def shiftGuide {N : ℕ} (p u : ℕ) (target : ZMod p) (i : Fin N) : ℕ :=
  shiftDigit p u target (sourceClass p i)

lemma shiftGuide_constant {N p u : ℕ} (target : ZMod p) (i j : Fin N)
    (h : sourceClass p i = sourceClass p j) :
    shiftGuide p u target i = shiftGuide p u target j := by
  simp [shiftGuide, h]

lemma shiftGuide_zero {N p u : ℕ} (target : ZMod p) (i : Fin N)
    (h : sourceClass p i = target) : shiftGuide p u target i = 0 := by
  exact shiftDigit_eq_zero_of_eq target _ h

lemma shiftGuide_carries {N p u : ℕ} (hp : p.Prime) (hu : Nat.Coprime u p)
    (target : ZMod p) (i : Fin N) :
    sourceClass p i + (u : ZMod p) * (shiftGuide p u target i : ℕ) = target := by
  exact source_add_shiftDigit hp hu target (sourceClass p i)

lemma shiftGuide_constant_mod {N p u : ℕ}
    (target : ZMod p) (i j : Fin N) (h : i.1 % p = j.1 % p) :
    shiftGuide p u target i = shiftGuide p u target j := by
  apply shiftGuide_constant target i j
  unfold sourceClass
  have hcast : ((i.1 : ℕ) : ZMod p) = ((j.1 : ℕ) : ZMod p) := by
    rw [← ZMod.natCast_mod i.1 p, ← ZMod.natCast_mod j.1 p, h]
  exact hcast

lemma shiftGuide_zero_mod {N p u : ℕ} (target : Fin p)
    (i : Fin N) (h : i.1 % p = target.1) :
    shiftGuide p u (target : ZMod p) i = 0 := by
  apply shiftGuide_zero (target : ZMod p) i
  unfold sourceClass
  have hcast : ((i.1 : ℕ) : ZMod p) = ((target.1 : ℕ) : ZMod p) := by
    rw [← ZMod.natCast_mod i.1 p, h]
  exact hcast

lemma partialGoodShift_shiftGuide_mod {N p u n : ℕ} (hp : p.Prime)
    (hn : 0 < n) (hu : Nat.Coprime u p) (hN : N = u * p ^ n)
    (target : Fin p) (i : Fin N) :
    (partialGoodShift N u (shiftGuide p u (target : ZMod p)) i).1 % p = target.1 := by
  have hpN : p ∣ N := by
    rw [hN]
    exact dvd_mul_of_dvd_right (dvd_pow_self p (Nat.ne_of_gt hn)) u
  have hcarry := shiftGuide_carries hp hu (target : ZMod p) i
  have hcast :
      (((partialGoodShift N u (shiftGuide p u (target : ZMod p)) i).1 : ℕ) :
          ZMod p) = (target : ZMod p) := by
    change (((i.1 + u * shiftGuide p u (target : ZMod p) i) % N : ℕ) : ZMod p) = _
    calc
      (((i.1 + u * shiftGuide p u (target : ZMod p) i) % N : ℕ) : ZMod p) =
          ((((i.1 + u * shiftGuide p u (target : ZMod p) i) % N) % p : ℕ) :
            ZMod p) := by
              symm
              exact ZMod.natCast_mod _ _
      _ = (((i.1 + u * shiftGuide p u (target : ZMod p) i) % p : ℕ) :
          ZMod p) := by rw [Nat.mod_mod_of_dvd _ hpN]
      _ = ((i.1 + u * shiftGuide p u (target : ZMod p) i : ℕ) : ZMod p) :=
        ZMod.natCast_mod _ _
      _ = (target : ZMod p) := by
        push_cast
        exact hcarry
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast,
    ZMod.val_natCast_of_lt target.2] at hv
  exact hv

/-- Lemma 4.8 specialized to the canonical least nonnegative shift guide
from (4.11). -/
theorem exists_goodPerm_to_target
    {N u d p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hcop : Nat.Coprime p u) (hpd : N = p * d) (hN : N = u * p ^ n)
    (target : Fin p) (pi : Fin N → Fin N)
    (hpartial : PartialGoodOnClass N p target.1 pi) :
    ∃ sigma : Equiv.Perm (Fin N), GoodPerm N sigma ∧
      ∀ i : Fin N, i.1 % p = target.1 → sigma i = pi i := by
  let q : Fin N → ℕ := shiftGuide p u (target : ZMod p)
  apply exists_goodPerm_extending_partial hp hn hcop hpd hN q pi
  · intro i j hij
    exact shiftGuide_constant_mod (target : ZMod p) i j hij
  · intro i hi
    exact shiftGuide_zero_mod target i hi
  · intro i
    exact partialGoodShift_shiftGuide_mod hp hn hcop.symm hN target i
  · exact hpartial

/-- Scaling both old arguments by the new prime scales their capped
difference by exactly that prime. -/
lemma indexDiff_oldIndex (p : ℕ) (hp : 0 < p) {d : ℕ} (i j : Fin d) :
    indexDiff (oldIndex p hp i) (oldIndex p hp j) = p * indexDiff i j := by
  simp only [indexDiff, oldIndex]
  push_cast
  rw [← mul_sub, Int.natAbs_mul]
  simp

/-- Hence the surviving modulus on the old residue class is literally the
old surviving modulus. -/
lemma survivingModulus_oldIndex (p : ℕ) (hp : 0 < p) {d : ℕ} (i j : Fin d) :
    survivingModulus (p * d)
        (indexDiff (oldIndex p hp i) (oldIndex p hp j)) =
      survivingModulus d (indexDiff i j) := by
  rw [indexDiff_oldIndex]
  simp only [survivingModulus, Nat.gcd_mul_left]
  exact Nat.mul_div_mul_left d (Nat.gcd d (indexDiff i j)) hp

lemma exists_oldIndex_of_mod_eq_zero (p : ℕ) (hp : 0 < p) {d : ℕ}
    (x : Fin (p * d)) (hx : x.1 % p = 0) :
    ∃ i : Fin d, x = oldIndex p hp i := by
  have hpx : p ∣ x.1 := Nat.dvd_iff_mod_eq_zero.mpr hx
  have hlt : x.1 / p < d := by
    apply (Nat.div_lt_iff_lt_mul hp).2
    simpa only [Nat.mul_comm d p] using x.2
  let i : Fin d := ⟨x.1 / p, hlt⟩
  refine ⟨i, ?_⟩
  apply Fin.ext
  change x.1 = p * (x.1 / p)
  exact (Nat.mul_div_cancel' hpx).symm

private lemma int_dvd_sub_iff_natModEq (m a b : ℕ) :
    (m : ℤ) ∣ (a : ℤ) - (b : ℤ) ↔ a ≡ b [MOD m] := by
  rw [Nat.modEq_iff_dvd]
  constructor <;> intro h <;> simpa only [neg_sub] using dvd_neg.mpr h

/-- Any formula on the old class which reduces to a good old map is
partially good at the enlarged denominator.  This is the exact scaling
argument used immediately after (4.9). -/
lemma partialGoodOnOldClass_of_reduces_good
    (p : ℕ) (hp : 0 < p) {d : ℕ} (F : Fin d → Fin d)
    (hF : GoodMap d F) (f : Fin (p * d) → Fin (p * d))
    (hreduce : ∀ i : Fin d, (f (oldIndex p hp i)).1 ≡ (F i).1 [MOD d]) :
    PartialGoodOnClass (p * d) p 0 f := by
  intro x y hx hy hxy
  obtain ⟨i, rfl⟩ := exists_oldIndex_of_mod_eq_zero p hp x hx
  obtain ⟨j, rfl⟩ := exists_oldIndex_of_mod_eq_zero p hp y hy
  have hij : i ≠ j := by
    intro h
    apply hxy
    exact congrArg (oldIndex p hp) h
  rw [survivingModulus_oldIndex]
  let M := survivingModulus d (indexDiff i j)
  have hMd : M ∣ d := survivingModulus_dvd _ _
  intro hbad
  have hbadmod : (f (oldIndex p hp i)).1 ≡
      (f (oldIndex p hp j)).1 [MOD M] :=
    (int_dvd_sub_iff_natModEq _ _ _).mp hbad
  have hiF := (hreduce i).of_dvd hMd
  have hjF := (hreduce j).of_dvd hMd
  have hFF : (F i).1 ≡ (F j).1 [MOD M] :=
    hiF.symm.trans (hbadmod.trans hjF)
  exact hF i j hij ((int_dvd_sub_iff_natModEq _ _ _).mpr hFF)

/-- The distinguished source class in (4.10).  The coefficient is
`lambda - (-lambda)` rather than an abbreviated division by `2*lambda`. -/
def distinguishedResidue {p : ℕ} (lam j : ZMod p) : ZMod p :=
  -j * (lam - -lam)⁻¹

lemma distinguishedResidue_relation {p : ℕ} (lam j : ZMod p)
    (hunit : IsUnit (lam - -lam)) :
    distinguishedResidue lam j * (lam - -lam) = -j := by
  simp only [distinguishedResidue]
  rw [mul_assoc, ZMod.inv_mul_of_unit _ hunit, mul_one]

lemma distinguishedResidue_unique {p : ℕ} (lam j x : ZMod p)
    (hunit : IsUnit (lam - -lam))
    (hx : x * (lam - -lam) = -j) :
    x = distinguishedResidue lam j := by
  apply hunit.mul_right_cancel
  rw [hx, distinguishedResidue_relation lam j hunit]

/-- Algebraic core of (S6)--(S7): the two distinguished source classes add
to the original source class. -/
lemma distinguishedResidue_add_of_opposite
    {p : ℕ} (lam₁ lam₂ j₁ j₂ i : ZMod p)
    (hunit : IsUnit (lam₁ - -lam₁))
    (hopposite : lam₂ = -lam₁)
    (hline : i * (lam₁ - lam₂) = -(j₁ - j₂)) :
    distinguishedResidue lam₁ j₁ + distinguishedResidue lam₂ j₂ = i := by
  have h₁ := distinguishedResidue_relation lam₁ j₁ hunit
  have hunit₂ : IsUnit (lam₂ - -lam₂) := by
    rw [hopposite]
    simp only [neg_neg]
    have heq : -lam₁ - lam₁ = -(lam₁ - -lam₁) := by ring
    rw [heq]
    exact hunit.neg
  have h₂ := distinguishedResidue_relation lam₂ j₂ hunit₂
  apply hunit.mul_right_cancel
  rw [add_mul]
  rw [h₁]
  have hcoeff₂ : lam₂ - -lam₂ = -(lam₁ - -lam₁) := by
    rw [hopposite]
    ring
  have ht₂ : distinguishedResidue lam₂ j₂ * (lam₁ - -lam₁) = j₂ := by
    rw [hcoeff₂] at h₂
    calc
      distinguishedResidue lam₂ j₂ * (lam₁ - -lam₁) =
          -(distinguishedResidue lam₂ j₂ * -(lam₁ - -lam₁)) := by ring
      _ = -(-j₂) := congrArg Neg.neg h₂
      _ = j₂ := neg_neg _
  rw [ht₂]
  rw [hopposite] at hline
  simp only [sub_neg_eq_add] at hline
  linear_combination -hline

/-- Exact equality of the two pairs of chosen digits in (S7). -/
lemma shiftDigit_cross_eq
    {p u : ℕ} (hp : p.Prime)
    (lam₁ lam₂ j₁ j₂ i : ZMod p)
    (hunit : IsUnit (lam₁ - -lam₁))
    (hopposite : lam₂ = -lam₁)
    (hline : i * (lam₁ - lam₂) = -(j₁ - j₂)) :
    let t₁ := distinguishedResidue lam₁ j₁
    let t₂ := distinguishedResidue lam₂ j₂
    shiftDigit p u t₁ i = shiftDigit p u 0 t₂ ∧
      shiftDigit p u t₂ i = shiftDigit p u 0 t₁ := by
  dsimp only
  have hsum := distinguishedResidue_add_of_opposite
    lam₁ lam₂ j₁ j₂ i hunit hopposite hline
  constructor
  · have hcast :
        (shiftDigit p u (distinguishedResidue lam₁ j₁) i : ZMod p) =
          (shiftDigit p u 0 (distinguishedResidue lam₂ j₂) : ZMod p) := by
      rw [shiftDigit_cast hp, shiftDigit_cast hp]
      congr 1
      linear_combination hsum
    have hv := congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt (shiftDigit_lt hp _ _),
      ZMod.val_natCast_of_lt (shiftDigit_lt hp _ _)] at hv
    exact hv
  · have hcast :
        (shiftDigit p u (distinguishedResidue lam₂ j₂) i : ZMod p) =
          (shiftDigit p u 0 (distinguishedResidue lam₁ j₁) : ZMod p) := by
      rw [shiftDigit_cast hp, shiftDigit_cast hp]
      congr 1
      linear_combination hsum
    have hv := congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt (shiftDigit_lt hp _ _),
      ZMod.val_natCast_of_lt (shiftDigit_lt hp _ _)] at hv
    exact hv

/-- The two total chosen shifts in (S6) have the same literal sum. -/
lemma shiftDigit_cross_sum
    {p u : ℕ} (hp : p.Prime)
    (lam₁ lam₂ j₁ j₂ i : ZMod p)
    (hunit : IsUnit (lam₁ - -lam₁))
    (hopposite : lam₂ = -lam₁)
    (hline : i * (lam₁ - lam₂) = -(j₁ - j₂)) :
    let t₁ := distinguishedResidue lam₁ j₁
    let t₂ := distinguishedResidue lam₂ j₂
    shiftDigit p u t₁ i + shiftDigit p u 0 t₁ =
      shiftDigit p u t₂ i + shiftDigit p u 0 t₂ := by
  dsimp only
  obtain ⟨h₁, h₂⟩ := shiftDigit_cross_eq (u := u) hp lam₁ lam₂ j₁ j₂ i
    hunit hopposite hline
  rw [h₁, h₂]
  omega

end

end Selector.PrimeExtension

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorComponents.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
Primary-component lemmas used to reconstruct the odd-modulus selector.
-/

namespace Selector.Modular

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace PrimaryComponent

/-- An element of `ZMod (p ^ a)` is a unit as soon as its reduction modulo
`p` is nonzero.  This is the small local-ring fact used in the root
dichotomy, stated without installing a local-ring instance. -/
private lemma isUnit_of_castHom_ne_zero {p a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (z : ZMod (p ^ a))
    (hz : ZMod.castHom (dvd_pow_self p ha.ne') (ZMod p) z ≠ 0) : IsUnit z := by
  letI : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val z]
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp ha]
  intro hpz
  apply hz
  rw [← ZMod.natCast_zmod_val z]
  simpa only [map_natCast] using (ZMod.natCast_eq_zero_iff z.val p).2 hpz

/-- Over an odd prime power, the two roots of `X² + 1` differ only by
sign.  The oddness assumption is supplied in the form used by the selector:
`2` is coprime to the prime-power modulus. -/
theorem root_eq_or_eq_neg {d : ℕ} (c : PrimaryComponent d)
    (hodd : Nat.Coprime 2 c.q) (x y : Root c.q) :
    x.1 = y.1 ∨ x.1 = -y.1 := by
  have hpq : c.p ∣ c.q := dvd_pow_self c.p c.exp_pos.ne'
  let red : ZMod c.q →+* ZMod c.p := ZMod.castHom hpq (ZMod c.p)
  letI : Fact c.p.Prime := ⟨c.prime⟩
  have hxroot : red x.1 ^ 2 = -1 := by
    rw [← map_pow, x.property]
    simp
  have hyroot : red y.1 ^ 2 = -1 := by
    rw [← map_pow, y.property]
    simp
  have hxy : red x.1 = red y.1 ∨ red x.1 = -red y.1 :=
    eq_or_eq_neg_of_sq_eq_sq _ _ (hxroot.trans hyroot.symm)
  have h2p : ¬ c.p ∣ 2 := by
    apply c.prime.coprime_iff_not_dvd.mp
    exact (hodd.of_dvd_right hpq).symm
  have htwo : (2 : ZMod c.p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 2 c.p).not.mpr h2p
  have hx0 : red x.1 ≠ 0 := by
    intro hx
    rw [hx] at hxroot
    simpa using hxroot
  have hy0 : red y.1 ≠ 0 := by
    intro hy
    rw [hy] at hyroot
    simpa using hyroot
  have hprod : (x.1 - y.1) * (x.1 + y.1) = 0 := by
    calc
      (x.1 - y.1) * (x.1 + y.1) = x.1 ^ 2 - y.1 ^ 2 := by ring
      _ = 0 := by rw [x.property, y.property, sub_self]
  rcases hxy with hsame | hopp
  · have hsum_red : red (x.1 + y.1) ≠ 0 := by
      rw [map_add, hsame]
      intro hzero
      have : (2 : ZMod c.p) * red y.1 = 0 := by
        simpa [two_mul] using hzero
      exact (mul_ne_zero htwo hy0) this
    have hsum_unit : IsUnit (x.1 + y.1) := by
      exact isUnit_of_castHom_ne_zero c.prime c.exp_pos (x.1 + y.1) hsum_red
    left
    apply sub_eq_zero.mp
    calc
      x.1 - y.1 = (x.1 - y.1) * 1 := by simp
      _ = (x.1 - y.1) * ((x.1 + y.1) * (x.1 + y.1)⁻¹) := by
        rw [ZMod.mul_inv_of_unit _ hsum_unit]
      _ = ((x.1 - y.1) * (x.1 + y.1)) * (x.1 + y.1)⁻¹ := by
        rw [mul_assoc]
      _ = 0 := by rw [hprod, zero_mul]
  · have hdiff_red : red (x.1 - y.1) ≠ 0 := by
      rw [map_sub, hopp]
      intro hzero
      have : (2 : ZMod c.p) * (-red y.1) = 0 := by
        simpa [two_mul, sub_eq_add_neg] using hzero
      exact (mul_ne_zero htwo (neg_ne_zero.mpr hy0)) this
    have hdiff_unit : IsUnit (x.1 - y.1) := by
      exact isUnit_of_castHom_ne_zero c.prime c.exp_pos (x.1 - y.1) hdiff_red
    right
    rw [eq_neg_iff_add_eq_zero]
    calc
      x.1 + y.1 = 1 * (x.1 + y.1) := by simp
      _ = ((x.1 - y.1)⁻¹ * (x.1 - y.1)) * (x.1 + y.1) := by
        rw [ZMod.inv_mul_of_unit _ hdiff_unit]
      _ = (x.1 - y.1)⁻¹ * ((x.1 - y.1) * (x.1 + y.1)) := by
        rw [mul_assoc]
      _ = 0 := by rw [hprod, mul_zero]

end PrimaryComponent

/-- A finite list of full primary components whose pairwise-coprime moduli
multiply to the original modulus.  Repetitions are ruled out by
`pairwise`; the equality `product_eq` is the explicit completeness
hypothesis. -/
structure CompleteComponents (d : ℕ) where
  components : List (PrimaryComponent d)
  pairwise : components.Pairwise fun c₁ c₂ : PrimaryComponent d ↦
    Nat.Coprime c₁.q c₂.q
  product_eq : (components.map fun c ↦ c.q).prod = d

namespace CompleteComponents

/-- Complete primary reductions separate points of `ZMod d`.  This is the
finite CRT coverage statement used when independently chosen local signs
are reconstructed globally. -/
theorem eq_of_reduce_eq {d : ℕ} (C : CompleteComponents d) (hd : d ≠ 0)
    (x y : ZMod d)
    (h : ∀ c ∈ C.components, c.reduce x = c.reduce y) : x = y := by
  letI : NeZero d := ⟨hd⟩
  have hlocal : ∀ c ∈ C.components, x.val ≡ y.val [MOD c.q] := by
    intro c hc
    apply (ZMod.natCast_eq_natCast_iff x.val y.val c.q).mp
    have hcast : (ZMod.cast x : ZMod c.q) = ZMod.cast y := by
      simpa only [PrimaryComponent.reduce, ZMod.castHom_apply] using h c hc
    calc
      (x.val : ZMod c.q) = ZMod.cast x := ZMod.natCast_val x
      _ = ZMod.cast y := hcast
      _ = (y.val : ZMod c.q) := (ZMod.natCast_val y).symm
  have hmod : x.val ≡ y.val [MOD d] := by
    have hp := (Nat.modEq_list_map_prod_iff C.pairwise).2 hlocal
    simpa only [C.product_eq] using hp
  calc
    x = (x.val : ZMod d) := (ZMod.natCast_zmod_val x).symm
    _ = (y.val : ZMod d) :=
      (ZMod.natCast_eq_natCast_iff x.val y.val d).2 hmod
    _ = y := ZMod.natCast_zmod_val y

end CompleteComponents

end

end Selector.Modular

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorSeparation.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
The separation half of the Jackson--Mauldin finite selector reconstruction.

The only denominator-specific input is `ConflictRootLineProperty d`.  It is the exact
Hensel/CRT consequence supplied by the complete family of nontrivial primary
components.  Its antecedent is the *full* conflict divisibility, including
the cross term: the weaker condition `d ∣ A^2+B^2` does not suffice when a
coordinate difference is only partially divisible by a primary factor.
Keeping this hypothesis explicit prevents the argument below from silently
claiming the result for arbitrary moduli.
-/

namespace Selector.Separation

open Erdos215.Selector
open Erdos215.Selector.Modular
open Erdos215.Selector.Final

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The exact local-primary/Hensel/CRT input needed by the separation proof.
The integers `K,M` are the differences of the two integral lifts. -/
def ConflictRootLineProperty (d : ℕ) : Prop :=
  ∀ A B K M : ℤ,
    (d : ℤ) ^ 2 ∣ A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) →
    ∃ lam : Root d, (B : ZMod d) = (lam : ZMod d) * (A : ZMod d)

/-- Cancelling an integer from a divisibility by `d` leaves precisely the
source's capped-gcd quotient `d / gcd(d, |A|)`. -/
lemma survivingModulus_dvd_of_dvd_mul (d : ℕ) (hd : d ≠ 0) (A X : ℤ)
    (h : (d : ℤ) ∣ A * X) :
    (survivingModulus d A.natAbs : ℤ) ∣ X := by
  let g := Nat.gcd d A.natAbs
  let u := d / g
  let v := A.natAbs / g
  have hgpos : 0 < g := by
    exact Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hd)
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hgpos)
  have hgd : g ∣ d := Nat.gcd_dvd_left d A.natAbs
  have hgA : g ∣ A.natAbs := Nat.gcd_dvd_right d A.natAbs
  have hdu : g * u = d := by
    exact Nat.mul_div_cancel' hgd
  have hAv : g * v = A.natAbs := by
    exact Nat.mul_div_cancel' hgA
  have huv : u.Coprime v := by
    exact Nat.coprime_div_gcd_div_gcd hgpos
  have hAbs : (d : ℤ) ∣ (A.natAbs : ℤ) * X := by
    rcases Int.natAbs_eq A with hA | hA
    · have heq : A * X = (A.natAbs : ℤ) * X := congrArg (· * X) hA
      rw [← heq]
      exact h
    · have heq : A * X = -((A.natAbs : ℤ) * X) :=
        (congrArg (· * X) hA).trans (by ring)
      have hneg : (d : ℤ) ∣ -((A.natAbs : ℤ) * X) := by
        rw [← heq]
        exact h
      exact dvd_neg.mp hneg
  rcases hAbs with ⟨q, hq⟩
  have hcancel : (v : ℤ) * X = (u : ℤ) * q := by
    apply mul_left_cancel₀ hg0
    calc
      (g : ℤ) * ((v : ℤ) * X) = ((g * v : ℕ) : ℤ) * X := by
        push_cast
        ring
      _ = (A.natAbs : ℤ) * X := by rw [hAv]
      _ = (d : ℤ) * q := hq
      _ = (g : ℤ) * ((u : ℤ) * q) := by
        have hduZ : (g : ℤ) * (u : ℤ) = (d : ℤ) := by exact_mod_cast hdu
        rw [← hduZ]
        ring
  have hu_dvd : (u : ℤ) ∣ (v : ℤ) * X := ⟨q, hcancel⟩
  have hcop : IsCoprime (u : ℤ) (v : ℤ) := huv.isCoprime
  change (u : ℤ) ∣ X
  exact hcop.dvd_of_dvd_mul_left hu_dvd

/-- The label of the root line through a specified residue cell. -/
def lineLabel {d : ℕ} (hd : d ≠ 0) (lam : Root d) (i j : Fin d) : Fin d := by
  letI : NeZero d := ⟨hd⟩
  exact ⟨(((j : ℕ) : ZMod d) - (lam : ZMod d) * ((i : ℕ) : ZMod d)).val,
    ZMod.val_lt _⟩

@[simp] lemma lineLabel_cast {d : ℕ} (hd : d ≠ 0) (lam : Root d)
    (i j : Fin d) :
    (((lineLabel hd lam i j : Fin d) : ℕ) : ZMod d) =
      ((j : ℕ) : ZMod d) - (lam : ZMod d) * ((i : ℕ) : ZMod d) := by
  letI : NeZero d := ⟨hd⟩
  exact ZMod.natCast_zmod_val _

lemma fin_eq_of_zmod_cast_eq {d : ℕ} (hd : d ≠ 0) (x y : Fin d)
    (h : (((x : Fin d) : ℕ) : ZMod d) = (((y : Fin d) : ℕ) : ZMod d)) :
    x = y := by
  letI : NeZero d := ⟨hd⟩
  apply Fin.ext
  have hv := congrArg ZMod.val h
  simpa [ZMod.val_natCast_of_lt x.isLt, ZMod.val_natCast_of_lt y.isLt] using hv

/-- The canonical line label really gives the chosen cell at its input. -/
lemma lineResidue_lineLabel {d : ℕ} (hd : d ≠ 0) (lam : Root d)
    (i j : Fin d) :
    lineResidue hd lam (lineLabel hd lam i j) i = j := by
  apply fin_eq_of_zmod_cast_eq hd
  rw [lineResidue_cast, lineLabel_cast]
  ring

/-- If two cells satisfy `B = lam*A` modulo `d`, the line label obtained from
the first cell also passes through the second. -/
lemma lineResidue_lineLabel_second {d : ℕ} (hd : d ≠ 0) (lam : Root d)
    (i₁ j₁ i₂ j₂ : Fin d)
    (hline :
      ((((j₁ : ℕ) : ℤ) - (j₂ : ℕ) : ℤ) : ZMod d) =
        (lam : ZMod d) *
          (((((i₁ : ℕ) : ℤ) - (i₂ : ℕ) : ℤ)) : ZMod d)) :
    lineResidue hd lam (lineLabel hd lam i₁ j₁) i₂ = j₂ := by
  apply fin_eq_of_zmod_cast_eq hd
  rw [lineResidue_cast, lineLabel_cast]
  push_cast at hline ⊢
  linear_combination hline

/-- Once a conflict pair has been placed on a root line, the full conflict
divisibility forces the two line-map values to agree modulo the precise
surviving modulus.  This is the cancellation calculation following (4.7). -/
lemma survivingModulus_dvd_inducedFamily_sub_of_conflict
    {d : ℕ} (hd : d ≠ 0) (hodd : Nat.Coprime 2 d) (s : LiftData d)
    (i₁ j₁ i₂ j₂ : Fin d) (lam : Root d)
    (hline :
      ((((j₁ : ℕ) : ℤ) - (j₂ : ℕ) : ℤ) : ZMod d) =
        (lam : ZMod d) *
          (((((i₁ : ℕ) : ℤ) - (i₂ : ℕ) : ℤ)) : ZMod d))
    (hdiv : (d : ℤ) ^ 2 ∣
      conflictNumerator d i₁ j₁ i₂ j₂
        (s.k i₁ j₁) (s.l i₁ j₁) (s.k i₂ j₂) (s.l i₂ j₂)) :
    (survivingModulus d (indexDiff i₁ i₂) : ℤ) ∣
      ((((inducedFamily hd s lam (lineLabel hd lam i₁ j₁) i₁ : Fin d) : ℕ) : ℤ) -
        (((inducedFamily hd s lam (lineLabel hd lam i₁ j₁) i₂ : Fin d) : ℕ) : ℤ)) := by
  let jt := lineLabel hd lam i₁ j₁
  let A : ℤ := ((i₁ : ℕ) : ℤ) - (i₂ : ℕ)
  let B : ℤ := ((j₁ : ℕ) : ℤ) - (j₂ : ℕ)
  let K : ℤ := s.k i₁ j₁ - s.k i₂ j₂
  let M : ℤ := s.l i₁ j₁ - s.l i₂ j₂
  let c : ℤ := (lineCarry hd lam jt i₁ : ℕ) - lineCarry hd lam jt i₂
  let L : ℤ := rootVal hd lam
  let R : ℤ := rootQuotient lam
  let H : ℤ := ZMod.val (rootPhase lam)
  let T : ℤ := K + L * M - L * c
  let E : ℤ := A * H + T
  let o₁ : Fin d := inducedFamily hd s lam jt i₁
  let o₂ : Fin d := inducedFamily hd s lam jt i₂
  let O : ℤ := ((o₁ : ℕ) : ℤ) - (o₂ : ℕ)
  have hcell₁ : lineResidue hd lam jt i₁ = j₁ := lineResidue_lineLabel hd lam i₁ j₁
  have hcell₂ : lineResidue hd lam jt i₂ = j₂ :=
    lineResidue_lineLabel_second hd lam i₁ j₁ i₂ j₂ hline
  have hj₁ := lineResidue_int_equation hd lam jt i₁
  have hj₂ := lineResidue_int_equation hd lam jt i₂
  rw [hcell₁] at hj₁
  rw [hcell₂] at hj₂
  have hB : B = L * A - c * d := by
    dsimp only [A, B, L, c, jt]
    linear_combination hj₁ - hj₂
  have hrootN := mul_rootQuotient hd lam
  have hroot : (d : ℤ) * R = 1 + L ^ 2 := by
    dsimp only [R, L]
    exact_mod_cast hrootN
  have hphaseCast : (H : ZMod d) = rootPhase lam := by
    letI : NeZero d := ⟨hd⟩
    dsimp only [H]
    simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val (rootPhase lam)
  have hphaseEq : ((2 * H : ℤ) : ZMod d) = (R : ZMod d) := by
    calc
      ((2 * H : ℤ) : ZMod d) = (2 : ZMod d) * rootPhase lam := by
        push_cast
        rw [hphaseCast]
      _ = (rootQuotient lam : ZMod d) := two_mul_rootPhase hodd lam
      _ = (R : ZMod d) := by simp only [R, Int.cast_natCast]
  have hphaseD : (d : ℤ) ∣ R - 2 * H := by
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub (2 * H) R d).mp hphaseEq
  rcases hdiv with ⟨q, hq⟩
  change A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) = (d : ℤ) ^ 2 * q at hq
  have hd0Z : (d : ℤ) ≠ 0 := by exact_mod_cast hd
  have hinside : A * (A * R + 2 * T) + d * (c ^ 2 - 2 * c * M) = d * q := by
    apply mul_left_cancel₀ hd0Z
    calc
      (d : ℤ) * (A * (A * R + 2 * T) + d * (c ^ 2 - 2 * c * M)) =
          A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) := by
            rw [hB]
            dsimp only [T]
            linear_combination A ^ 2 * hroot
      _ = (d : ℤ) ^ 2 * q := hq
      _ = (d : ℤ) * (d * q) := by ring
  have hAR : (d : ℤ) ∣ A * (A * R + 2 * T) := by
    refine ⟨q - (c ^ 2 - 2 * c * M), ?_⟩
    linear_combination hinside
  rcases hAR with ⟨q₁, hq₁⟩
  rcases hphaseD with ⟨q₂, hq₂⟩
  have htwo : (d : ℤ) ∣ 2 * (A * E) := by
    refine ⟨q₁ - A ^ 2 * q₂, ?_⟩
    dsimp only [E]
    linear_combination hq₁ - A ^ 2 * hq₂
  have hAE : (d : ℤ) ∣ A * E := by
    have htwo' : (d : ℤ) ∣ (2 : ℤ) * (A * E) := by simpa [mul_assoc] using htwo
    have hcop : IsCoprime (d : ℤ) (2 : ℤ) := hodd.symm.isCoprime
    exact hcop.dvd_of_dvd_mul_left htwo'
  have hSE : (survivingModulus d A.natAbs : ℤ) ∣ E :=
    survivingModulus_dvd_of_dvd_mul d hd A E hAE
  have hf₁ := inducedFamily_formula hd s lam jt i₁
  have hf₂ := inducedFamily_formula hd s lam jt i₂
  simp only [lineValue] at hf₁ hf₂
  rw [hcell₁] at hf₁
  rw [hcell₂] at hf₂
  have hrootValCast : (L : ZMod d) = lam := by
    simpa only [L, Int.cast_natCast] using rootVal_cast hd lam
  have hout : (O : ZMod d) = (E : ZMod d) := by
    dsimp only [O, o₁, o₂]
    push_cast
    rw [hf₁, hf₂]
    rw [← hrootValCast, ← hphaseCast]
    dsimp only [E, T, K, M, A, c, jt]
    push_cast
    ring
  have hdEO : (d : ℤ) ∣ E - O :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub O E d).mp hout
  have hSdNat : survivingModulus d A.natAbs ∣ d := survivingModulus_dvd d A.natAbs
  have hSd : (survivingModulus d A.natAbs : ℤ) ∣ (d : ℤ) := by
    exact_mod_cast hSdNat
  have hSEO : (survivingModulus d A.natAbs : ℤ) ∣ E - O := hSd.trans hdEO
  rcases hSE with ⟨a, ha⟩
  rcases hSEO with ⟨b, hb⟩
  change (survivingModulus d (indexDiff i₁ i₂) : ℤ) ∣ O
  have hindex : indexDiff i₁ i₂ = A.natAbs := rfl
  rw [hindex]
  refine ⟨a - b, ?_⟩
  linear_combination ha - hb

/-- Goodness of the induced family rules out every conflict, hence gives the
finite selector condition `(*)_d`. -/
theorem separated_of_inducedFamily_good {d : ℕ} (hd : d ≠ 0)
    (hodd : Nat.Coprime 2 d) (hroot : ConflictRootLineProperty d)
    (s : LiftData d) (hgood : FamilyGood (inducedFamily hd s)) :
    s.Separated := by
  intro i₁ j₁ i₂ j₂ hne hdiv
  let A : ℤ := ((i₁ : ℕ) : ℤ) - (i₂ : ℕ)
  let B : ℤ := ((j₁ : ℕ) : ℤ) - (j₂ : ℕ)
  let K : ℤ := s.k i₁ j₁ - s.k i₂ j₂
  let M : ℤ := s.l i₁ j₁ - s.l i₂ j₂
  have hfull : (d : ℤ) ^ 2 ∣ A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) := by
    simpa only [conflictNumerator, A, B, K, M] using hdiv
  obtain ⟨lam, hline⟩ := hroot A B K M hfull
  let jt := lineLabel hd lam i₁ j₁
  have hcell₁ : lineResidue hd lam jt i₁ = j₁ := lineResidue_lineLabel hd lam i₁ j₁
  have hcell₂ : lineResidue hd lam jt i₂ = j₂ := by
    apply lineResidue_lineLabel_second hd lam i₁ j₁ i₂ j₂
    exact hline
  have hi : i₁ ≠ i₂ := by
    intro hii
    subst i₂
    have hjj : j₁ = j₂ := hcell₁.symm.trans hcell₂
    exact hne (Prod.ext rfl hjj)
  apply hgood lam jt i₁ i₂ hi
  exact survivingModulus_dvd_inducedFamily_sub_of_conflict
    hd hodd s i₁ j₁ i₂ j₂ lam hline hdiv

/-- Rewrite-friendly form used after the reconstruction module has shown
that a chosen lift realizes a prescribed good family. -/
theorem separated_of_inducedFamily_eq_good {d : ℕ} (hd : d ≠ 0)
    (hodd : Nat.Coprime 2 d) (hroot : ConflictRootLineProperty d)
    (s : LiftData d) {F : RawLineFamily d} (hrealize : inducedFamily hd s = F)
    (hgood : FamilyGood F) : s.Separated := by
  apply separated_of_inducedFamily_good hd hodd hroot s
  rw [hrealize]
  exact hgood

end

end Selector.Separation

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorReconstruct.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
Reconstruction of lift data from the line maps in the finite
Jackson--Mauldin selector construction.

The definitions in this file deliberately separate the two ingredients of
the argument.  `ResidueSolution` is the simultaneous system of line
equations (4.4), written in `ZMod d`.  Once such a solution is available,
`liftDataOfResidueSolution` chooses canonical integral representatives and
`inducedFamily_liftDataOfResidueSolution` proves that the resulting lift data
induces the prescribed family literally.
-/

namespace Selector.Reconstruct

open Erdos215.Selector
open Erdos215.Selector.Modular
open Erdos215.Selector.Final

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The root opposite to `lam`. -/
def negRoot {d : ℕ} (lam : Root d) : Root d :=
  ⟨-lam.1, by simpa only [neg_sq] using lam.property⟩

@[simp] lemma coe_negRoot {d : ℕ} (lam : Root d) :
    (negRoot lam : ZMod d) = -(lam : ZMod d) := rfl

/-- The cell of a line at the input coordinate `i`. -/
def lineCell {d : ℕ} (hd : d ≠ 0) (lam : Root d) (jtilde i : Fin d) :
    Fin d :=
  lineResidue hd lam jtilde i

/-- The unique canonical label of the `lam`-line through the cell `(i,j)`. -/
def cellLineLabel {d : ℕ} (hd : d ≠ 0) (lam : Root d) (i j : Fin d) :
    Fin d := by
  let _ : NeZero d := ⟨hd⟩
  exact ⟨(((j : ℕ) : ZMod d) - (lam : ZMod d) * ((i : ℕ) : ZMod d)).val,
    ZMod.val_lt _⟩

@[simp] lemma cellLineLabel_cast {d : ℕ} (hd : d ≠ 0) (lam : Root d)
    (i j : Fin d) :
    (((cellLineLabel hd lam i j : Fin d) : ℕ) : ZMod d) =
      ((j : ℕ) : ZMod d) - (lam : ZMod d) * ((i : ℕ) : ZMod d) := by
  let _ : NeZero d := ⟨hd⟩
  exact ZMod.natCast_zmod_val _

@[simp] lemma lineCell_cellLineLabel {d : ℕ} (hd : d ≠ 0) (lam : Root d)
    (i j : Fin d) :
    lineCell hd lam (cellLineLabel hd lam i j) i = j := by
  let _ : NeZero d := ⟨hd⟩
  apply Fin.ext
  have hcast :
      ((((lineCell hd lam (cellLineLabel hd lam i j) i : Fin d) : ℕ) : ZMod d)) =
        (((j : Fin d) : ℕ) : ZMod d) := by
    simp only [lineCell, lineResidue_cast, cellLineLabel_cast]
    ring
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt
      (lineCell hd lam (cellLineLabel hd lam i j) i).isLt,
    ZMod.val_natCast_of_lt j.isLt] at hv
  exact hv

lemma lineRelation_of_same_cell {d : ℕ} (hd : d ≠ 0)
    (lam₁ lam₂ : Root d) (j₁ j₂ i : Fin d)
    (hcell : lineCell hd lam₁ j₁ i = lineCell hd lam₂ j₂ i) :
    ((i : ℕ) : ZMod d) * ((lam₁ : ZMod d) - lam₂) =
      -(((j₁ : ℕ) : ZMod d) - ((j₂ : ℕ) : ZMod d)) := by
  have hcast := congrArg (fun j : Fin d ↦ (((j : ℕ) : ZMod d))) hcell
  simp only [lineCell, lineResidue_cast] at hcast
  linear_combination hcast

/-- The rearranged right hand side of (4.4).  Thus the equation imposed at
the cell `(i,lineCell ...)` is `k + lam*l = lineTarget ...`. -/
def lineTarget {d : ℕ} (hd : d ≠ 0) (F : RawLineFamily d)
    (lam : Root d) (jtilde i : Fin d) : ZMod d :=
  (((F lam jtilde i : Fin d) : ℕ) : ZMod d) - rootPhase lam * (i : ℕ) +
    (lam : ZMod d) * (lineCarry hd lam jtilde i : ZMod d)

lemma PrimaryComponent.localQuotient_mul_right {d : ℕ}
    (c : PrimaryComponent d) (z n : ℤ) (hz : (c.q : ℤ) ∣ z) :
    c.localQuotient (z * n) = c.localQuotient z * (n : ZMod c.q) := by
  rcases hz with ⟨a, rfl⟩
  simp only [PrimaryComponent.localQuotient]
  rw [mul_assoc, localizedQuotient_mul c.q c.q_ne_zero,
    localizedQuotient_mul c.q c.q_ne_zero]
  push_cast
  ring

lemma PrimaryComponent.localQuotient_add' {d : ℕ}
    (c : PrimaryComponent d) (x y : ℤ)
    (hx : (c.q : ℤ) ∣ x) (hy : (c.q : ℤ) ∣ y) :
    c.localQuotient (x + y) = c.localQuotient x + c.localQuotient y := by
  exact localizedQuotient_add c.q c.q_ne_zero _ x y hx hy

/-- The rearranged line targets must be independent of the chosen global
root whenever the two roots induce the same root on a primary component. -/
def FamilyTargetCoherent {d : ℕ} (hd : d ≠ 0) (F : RawLineFamily d) : Prop :=
  ∀ (c : PrimaryComponent d) (lam₁ lam₂ : Root d) (j₁ j₂ i : Fin d),
    c.reduce lam₁ = c.reduce lam₂ →
    ((i : ℕ) : ZMod d) * ((lam₁ : ZMod d) - lam₂) =
        -(((j₁ : ℕ) : ZMod d) - ((j₂ : ℕ) : ZMod d)) →
    c.reduce (lineTarget hd F lam₁ j₁ i) =
      c.reduce (lineTarget hd F lam₂ j₂ i)

/-- Formula (4.6), including its carry and `h_d` correction terms, says
exactly that the rearranged line target is componentwise well-defined. -/
theorem targetCoherent_of_consistent {d : ℕ} (hd : d ≠ 0)
    (hodd : Nat.Coprime 2 d) (F : RawLineFamily d)
    (hF : FamilyConsistent F) : FamilyTargetCoherent hd F := by
  intro c lam₁ lam₂ j₁ j₂ i hroot hline
  have hcell := lineResidue_eq_of_relation hd lam₁ lam₂ j₁ j₂ i hline
  have hcarry := lineCarry_sub_relation hd lam₁ lam₂ j₁ j₂ i hcell
  let delta : ℤ := (rootVal hd lam₁ : ℤ) - rootVal hd lam₂
  let jdiff : ℤ := ((j₁ : ℕ) : ℤ) - (j₂ : ℕ)
  let mdiff : ℤ := (lineCarry hd lam₁ j₁ i : ℤ) -
    lineCarry hd lam₂ j₂ i
  have hrootVal :
      ((rootVal hd lam₁ : ℤ) : ZMod c.q) =
        ((rootVal hd lam₂ : ℤ) : ZMod c.q) := by
    simp only [Int.cast_natCast, ← c.reduce_natCast, rootVal_cast]
    exact hroot
  have hdelta : (c.q : ℤ) ∣ delta := by
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub
      (rootVal hd lam₁) (rootVal hd lam₂) c.q).mp hrootVal
    simpa only [delta, neg_sub] using (dvd_neg.mpr h)
  have hlinec := congrArg c.reduce hline
  simp only [map_mul, map_sub, map_neg, c.reduce_natCast, hroot, sub_self,
    mul_zero, neg_eq_zero] at hlinec
  have hjdiffZero : (jdiff : ZMod c.q) = 0 := by
    dsimp only [jdiff]
    push_cast
    exact neg_eq_zero.mp hlinec.symm
  have hjdiff : (c.q : ℤ) ∣ jdiff :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd jdiff c.q).mp hjdiffZero
  have hdeltai : (c.q : ℤ) ∣ delta * (i : ℕ) :=
    dvd_mul_of_dvd_left hdelta _
  have hcarry' : (d : ℤ) * mdiff = jdiff + delta * (i : ℕ) := by
    simpa only [delta, jdiff, mdiff] using hcarry
  have hcarryLoc := congrArg c.localQuotient hcarry'
  rw [Erdos215.Selector.Final.PrimaryComponent.localQuotient_mul_modulus,
    Erdos215.Selector.Reconstruct.PrimaryComponent.localQuotient_add'
      c jdiff (delta * (i : ℕ)) hjdiff hdeltai,
    Erdos215.Selector.Reconstruct.PrimaryComponent.localQuotient_mul_right
      c delta (i : ℕ) hdelta] at hcarryLoc
  have hphase := two_mul_reduce_rootPhase_sub hd hodd c lam₁ lam₂
  have hphase' :
      (2 : ZMod c.q) * c.reduce (rootPhase lam₁ - rootPhase lam₂) =
        c.localQuotient delta *
          (((rootVal hd lam₁ : ℤ) + rootVal hd lam₂ : ℤ) : ZMod c.q) := by
    rw [hphase]
    exact Erdos215.Selector.Reconstruct.PrimaryComponent.localQuotient_mul_right c delta
      ((rootVal hd lam₁ : ℤ) + rootVal hd lam₂) hdelta
  have hsum :
      (((rootVal hd lam₁ : ℤ) + rootVal hd lam₂ : ℤ) : ZMod c.q) =
        (2 : ZMod c.q) * c.reduce lam₁ := by
    push_cast
    simp only [Int.cast_natCast, ← c.reduce_natCast, rootVal_cast, hroot]
    ring
  rw [hsum] at hphase'
  have htwoCoprime : Nat.Coprime 2 c.q := hodd.of_dvd_right c.q_dvd
  have htwoUnit : IsUnit (2 : ZMod c.q) := by
    exact IsUnit.of_mul_eq_one _ (ZMod.coe_mul_inv_eq_one 2 htwoCoprime)
  have hphaseCancel :
      c.reduce (rootPhase lam₁ - rootPhase lam₂) =
        c.reduce lam₁ * c.localQuotient delta := by
    apply htwoUnit.mul_left_cancel
    calc
      (2 : ZMod c.q) * c.reduce (rootPhase lam₁ - rootPhase lam₂) =
          c.localQuotient delta * ((2 : ZMod c.q) * c.reduce lam₁) := hphase'
      _ = (2 : ZMod c.q) *
          (c.reduce lam₁ * c.localQuotient delta) := by ring
  have hcons := hF c lam₁ lam₂ j₁ j₂ i hroot hline
  simp only [lineTarget, map_add, map_sub, map_mul, c.reduce_natCast,
    c.reduce_intCast]
  simp only [lineTarget, map_add, map_sub, map_mul, c.reduce_natCast,
    c.reduce_intCast] at hcons ⊢
  have hcarryLoc' := hcarryLoc
  dsimp only [mdiff, jdiff] at hcarryLoc' hcons ⊢
  push_cast at hcarryLoc'
  dsimp only [delta] at hphaseCancel
  simp only [map_sub] at hphaseCancel
  rw [← hroot]
  rw [← sub_eq_zero]
  linear_combination hcons +
    c.reduce lam₁ * hcarryLoc' - hphaseCancel * (((i : ℕ) : ZMod c.q))

/-- A solution, modulo `d`, of all the line equations attached to a raw
family. -/
structure ResidueSolution {d : ℕ} (hd : d ≠ 0) (F : RawLineFamily d) where
  k : Fin d → Fin d → ZMod d
  l : Fin d → Fin d → ZMod d
  line_eq : ∀ (lam : Root d) (jtilde i : Fin d),
    k i (lineCell hd lam jtilde i) +
        (lam : ZMod d) * l i (lineCell hd lam jtilde i) =
      lineTarget hd F lam jtilde i

/-- Equality in `ZMod d` is detected by all of its full primary
components.  This is the exact CRT separation property used below. -/
def PrimaryReductionsDetect (d : ℕ) : Prop :=
  ∀ x y : ZMod d,
    (∀ c : PrimaryComponent d, c.reduce x = c.reduce y) → x = y

/-- Every global root restricts, on each primary component, to one of the
two signs of a fixed global root. -/
def RootSignsCovered {d : ℕ} (lam₀ : Root d) : Prop :=
  ∀ (c : PrimaryComponent d) (lam : Root d),
    c.reduce lam = c.reduce lam₀ ∨ c.reduce lam = c.reduce (negRoot lam₀)

lemma primaryReductionsDetect_of_complete {d : ℕ}
    (C : CompleteComponents d) (hd : d ≠ 0) : PrimaryReductionsDetect d := by
  intro x y hxy
  exact C.eq_of_reduce_eq hd x y (fun c _hc ↦ hxy c)

lemma rootSignsCovered_of_odd {d : ℕ} (hodd : Nat.Coprime 2 d)
    (lam₀ : Root d) : RootSignsCovered lam₀ := by
  intro c lam
  have hcodd : Nat.Coprime 2 c.q := hodd.of_dvd_right c.q_dvd
  rcases c.root_eq_or_eq_neg hcodd (c.reduceRoot lam) (c.reduceRoot lam₀) with h | h
  · left
    exact h
  · right
    rw [show (negRoot lam₀ : ZMod d) = -(lam₀ : ZMod d) from rfl, map_neg]
    exact h

/-- The target attached to the unique `lam`-line through `(i,j)`. -/
def cellTarget {d : ℕ} (hd : d ≠ 0) (F : RawLineFamily d)
    (lam : Root d) (i j : Fin d) : ZMod d :=
  lineTarget hd F lam (cellLineLabel hd lam i j) i

/-- The solution of the two line equations belonging to `lam₀` and
`-lam₀`. -/
def reconstructedL {d : ℕ} (hd : d ≠ 0) (F : RawLineFamily d)
    (lam₀ : Root d) (i j : Fin d) : ZMod d :=
  ((lam₀ : ZMod d) - (negRoot lam₀ : ZMod d))⁻¹ *
    (cellTarget hd F lam₀ i j - cellTarget hd F (negRoot lam₀) i j)

def reconstructedK {d : ℕ} (hd : d ≠ 0) (F : RawLineFamily d)
    (lam₀ : Root d) (i j : Fin d) : ZMod d :=
  cellTarget hd F lam₀ i j - (lam₀ : ZMod d) * reconstructedL hd F lam₀ i j

lemma root_sub_negRoot_isUnit {d : ℕ} (hodd : Nat.Coprime 2 d)
    (lam : Root d) :
    IsUnit ((lam : ZMod d) - (negRoot lam : ZMod d)) := by
  have htwo : IsUnit (2 : ZMod d) :=
    IsUnit.of_mul_eq_one _ (ZMod.coe_mul_inv_eq_one 2 hodd)
  have hprod : IsUnit ((2 : ZMod d) * (lam : ZMod d)) :=
    htwo.mul (root_isUnit lam)
  convert hprod using 1 <;> simp only [coe_negRoot] <;> ring

lemma reconstructed_plus {d : ℕ} (hd : d ≠ 0) (hodd : Nat.Coprime 2 d)
    (F : RawLineFamily d) (lam₀ : Root d) (i j : Fin d) :
    reconstructedK hd F lam₀ i j +
        (lam₀ : ZMod d) * reconstructedL hd F lam₀ i j =
      cellTarget hd F lam₀ i j := by
  simp only [reconstructedK]
  ring

lemma reconstructed_minus {d : ℕ} (hd : d ≠ 0) (hodd : Nat.Coprime 2 d)
    (F : RawLineFamily d) (lam₀ : Root d) (i j : Fin d) :
    reconstructedK hd F lam₀ i j +
        (negRoot lam₀ : ZMod d) * reconstructedL hd F lam₀ i j =
      cellTarget hd F (negRoot lam₀) i j := by
  have hunit := root_sub_negRoot_isUnit hodd lam₀
  have hinv := ZMod.inv_mul_of_unit
    ((lam₀ : ZMod d) - (negRoot lam₀ : ZMod d)) hunit
  simp only [reconstructedK, reconstructedL]
  linear_combination
    cellTarget hd F lam₀ i j - cellTarget hd F (negRoot lam₀) i j -
      (cellTarget hd F lam₀ i j - cellTarget hd F (negRoot lam₀) i j) * hinv

/-- Reconstruction of every line equation from consistency.  The two
explicit hypotheses are precisely the standard primary-component CRT facts:
primary reductions detect equality, and a root of `X²+1` on an odd prime
power has one of two signs. -/
noncomputable def residueSolution_of_consistent {d : ℕ} (hd : d ≠ 0)
    (hodd : Nat.Coprime 2 d) (F : RawLineFamily d)
    (hF : FamilyConsistent F) (lam₀ : Root d)
    (hdetect : PrimaryReductionsDetect d) (hsigns : RootSignsCovered lam₀) :
    ResidueSolution hd F where
  k := reconstructedK hd F lam₀
  l := reconstructedL hd F lam₀
  line_eq := by
    intro lam jtilde i
    let j := lineCell hd lam jtilde i
    apply hdetect
    intro c
    have hcoherent := targetCoherent_of_consistent hd hodd F hF
    rcases hsigns c lam with hplus | hminus
    · have hsame :
          lineCell hd lam jtilde i =
            lineCell hd lam₀ (cellLineLabel hd lam₀ i j) i := by
        simp only [lineCell_cellLineLabel, j]
      have hrel := lineRelation_of_same_cell hd lam lam₀ jtilde
        (cellLineLabel hd lam₀ i j) i hsame
      have htarget := hcoherent c lam lam₀ jtilde
        (cellLineLabel hd lam₀ i j) i hplus hrel
      have hbase := congrArg c.reduce (reconstructed_plus hd hodd F lam₀ i j)
      calc
        c.reduce (reconstructedK hd F lam₀ i j +
            (lam : ZMod d) * reconstructedL hd F lam₀ i j) =
            c.reduce (reconstructedK hd F lam₀ i j) +
              c.reduce lam * c.reduce (reconstructedL hd F lam₀ i j) := by simp
        _ = c.reduce (reconstructedK hd F lam₀ i j) +
              c.reduce lam₀ * c.reduce (reconstructedL hd F lam₀ i j) := by
            rw [hplus]
        _ = c.reduce (reconstructedK hd F lam₀ i j +
              (lam₀ : ZMod d) * reconstructedL hd F lam₀ i j) := by simp
        _ = c.reduce (cellTarget hd F lam₀ i j) := hbase
        _ = c.reduce (lineTarget hd F lam₀ (cellLineLabel hd lam₀ i j) i) := rfl
        _ = c.reduce (lineTarget hd F lam jtilde i) := htarget.symm
    · have hsame :
          lineCell hd lam jtilde i =
            lineCell hd (negRoot lam₀) (cellLineLabel hd (negRoot lam₀) i j) i := by
        simp only [lineCell_cellLineLabel, j]
      have hrel := lineRelation_of_same_cell hd lam (negRoot lam₀) jtilde
        (cellLineLabel hd (negRoot lam₀) i j) i hsame
      have htarget := hcoherent c lam (negRoot lam₀) jtilde
        (cellLineLabel hd (negRoot lam₀) i j) i hminus hrel
      have hbase := congrArg c.reduce (reconstructed_minus hd hodd F lam₀ i j)
      calc
        c.reduce (reconstructedK hd F lam₀ i j +
            (lam : ZMod d) * reconstructedL hd F lam₀ i j) =
            c.reduce (reconstructedK hd F lam₀ i j) +
              c.reduce lam * c.reduce (reconstructedL hd F lam₀ i j) := by simp
        _ = c.reduce (reconstructedK hd F lam₀ i j) +
              c.reduce (negRoot lam₀) *
                c.reduce (reconstructedL hd F lam₀ i j) := by rw [hminus]
        _ = c.reduce (reconstructedK hd F lam₀ i j +
              (negRoot lam₀ : ZMod d) * reconstructedL hd F lam₀ i j) := by simp
        _ = c.reduce (cellTarget hd F (negRoot lam₀) i j) := hbase
        _ = c.reduce (lineTarget hd F (negRoot lam₀)
              (cellLineLabel hd (negRoot lam₀) i j) i) := rfl
        _ = c.reduce (lineTarget hd F lam jtilde i) := htarget.symm

/-- Choose the canonical integer representative of a residue. -/
def intRepresentative {d : ℕ} (x : ZMod d) : ℤ := x.val

@[simp] lemma intRepresentative_cast {d : ℕ} (hd : d ≠ 0) (x : ZMod d) :
    (intRepresentative x : ZMod d) = x := by
  letI : NeZero d := ⟨hd⟩
  simpa only [intRepresentative, Int.cast_natCast] using ZMod.natCast_zmod_val x

/-- Integral lift data obtained from a modular solution. -/
def liftDataOfResidueSolution {d : ℕ} {hd : d ≠ 0} {F : RawLineFamily d}
    (r : ResidueSolution hd F) : LiftData d where
  k i j := intRepresentative (r.k i j)
  l i j := intRepresentative (r.l i j)

/-- Choose representatives while keeping prescribed integral lifts exactly
on a specified set of cells.  The hypotheses merely say that those old
integers represent the reconstructed residues. -/
def liftDataOfResidueSolutionPreserving {d : ℕ} {hd : d ≠ 0}
    {F : RawLineFamily d} (r : ResidueSolution hd F) (old : LiftData d)
    (Q : Fin d → Fin d → Prop) : LiftData d := by
  classical
  exact
    { k := fun i j ↦ if Q i j then old.k i j else intRepresentative (r.k i j)
      l := fun i j ↦ if Q i j then old.l i j else intRepresentative (r.l i j) }

lemma liftDataOfResidueSolutionPreserving_cast_k {d : ℕ} {hd : d ≠ 0}
    {F : RawLineFamily d} (r : ResidueSolution hd F) (old : LiftData d)
    (Q : Fin d → Fin d → Prop)
    (hk : ∀ i j, Q i j → (old.k i j : ZMod d) = r.k i j) (i j : Fin d) :
    ((liftDataOfResidueSolutionPreserving r old Q).k i j : ZMod d) = r.k i j := by
  by_cases hQ : Q i j
  · simp only [liftDataOfResidueSolutionPreserving, if_pos hQ, hk i j hQ]
  · simp only [liftDataOfResidueSolutionPreserving, if_neg hQ,
      intRepresentative_cast hd]

lemma liftDataOfResidueSolutionPreserving_cast_l {d : ℕ} {hd : d ≠ 0}
    {F : RawLineFamily d} (r : ResidueSolution hd F) (old : LiftData d)
    (Q : Fin d → Fin d → Prop)
    (hl : ∀ i j, Q i j → (old.l i j : ZMod d) = r.l i j) (i j : Fin d) :
    ((liftDataOfResidueSolutionPreserving r old Q).l i j : ZMod d) = r.l i j := by
  by_cases hQ : Q i j
  · simp only [liftDataOfResidueSolutionPreserving, if_pos hQ, hl i j hQ]
  · simp only [liftDataOfResidueSolutionPreserving, if_neg hQ,
      intRepresentative_cast hd]

theorem liftDataOfResidueSolutionPreserving_eq_old {d : ℕ} {hd : d ≠ 0}
    {F : RawLineFamily d} (r : ResidueSolution hd F) (old : LiftData d)
    (Q : Fin d → Fin d → Prop) (i j : Fin d) (hQ : Q i j) :
    (liftDataOfResidueSolutionPreserving r old Q).k i j = old.k i j ∧
      (liftDataOfResidueSolutionPreserving r old Q).l i j = old.l i j := by
  simp only [liftDataOfResidueSolutionPreserving, if_pos hQ, and_self]

lemma lineValue_liftDataOfResidueSolution {d : ℕ} {hd : d ≠ 0}
    {F : RawLineFamily d} (r : ResidueSolution hd F) (lam : Root d)
    (jtilde i : Fin d) :
    lineValue hd (liftDataOfResidueSolution r) lam jtilde i =
      (((F lam jtilde i : Fin d) : ℕ) : ZMod d) := by
  have hline := r.line_eq lam jtilde i
  simp only [lineCell, lineTarget, lineValue, liftDataOfResidueSolution,
    intRepresentative_cast hd] at hline ⊢
  linear_combination hline

/-- A modular solution realizes the requested raw family literally. -/
theorem inducedFamily_liftDataOfResidueSolution {d : ℕ} {hd : d ≠ 0}
    {F : RawLineFamily d} (r : ResidueSolution hd F) :
    inducedFamily hd (liftDataOfResidueSolution r) = F := by
  funext lam jtilde i
  apply Fin.ext
  have hcast := inducedFamily_formula hd (liftDataOfResidueSolution r) lam jtilde i
  rw [lineValue_liftDataOfResidueSolution r lam jtilde i] at hcast
  letI : NeZero d := ⟨hd⟩
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt
      (inducedFamily hd (liftDataOfResidueSolution r) lam jtilde i).isLt,
    ZMod.val_natCast_of_lt (F lam jtilde i).isLt] at hv
  exact hv

/-- The preserving representative choice still realizes the same family. -/
theorem inducedFamily_liftDataOfResidueSolutionPreserving
    {d : ℕ} {hd : d ≠ 0} {F : RawLineFamily d}
    (r : ResidueSolution hd F) (old : LiftData d)
    (Q : Fin d → Fin d → Prop)
    (hk : ∀ i j, Q i j → (old.k i j : ZMod d) = r.k i j)
    (hl : ∀ i j, Q i j → (old.l i j : ZMod d) = r.l i j) :
    inducedFamily hd (liftDataOfResidueSolutionPreserving r old Q) = F := by
  funext lam jtilde i
  apply Fin.ext
  have hline := r.line_eq lam jtilde i
  have hvalue :
      lineValue hd (liftDataOfResidueSolutionPreserving r old Q) lam jtilde i =
        (((F lam jtilde i : Fin d) : ℕ) : ZMod d) := by
    simp only [lineCell, lineTarget, lineValue] at hline ⊢
    rw [liftDataOfResidueSolutionPreserving_cast_k r old Q hk,
      liftDataOfResidueSolutionPreserving_cast_l r old Q hl]
    linear_combination hline
  have hcast := inducedFamily_formula hd
    (liftDataOfResidueSolutionPreserving r old Q) lam jtilde i
  rw [hvalue] at hcast
  letI : NeZero d := ⟨hd⟩
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt
      (inducedFamily hd (liftDataOfResidueSolutionPreserving r old Q) lam jtilde i).isLt,
    ZMod.val_natCast_of_lt (F lam jtilde i).isLt] at hv
  exact hv

end

end Selector.Reconstruct

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorFlipRoot.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
Flipping one primary coordinate of a global root of `-1`.

For a primary factorization `d = c.q * c.D`, the Chinese remainder
equivalence writes a root modulo `d` as a root modulo `c.q` together with a
root modulo `c.D`.  Negating just the first coordinate again gives a root.
The lemmas below record both the changed primary reduction and the unchanged
complementary reduction, including the useful consequence for every other
primary component whose modulus divides `c.D`.
-/

namespace Selector.Modular

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace PrimaryComponent

/-- Reduction to the complementary CRT factor. -/
def reduceComplement {d : ℕ} (c : PrimaryComponent d) : ZMod d →+* ZMod c.D :=
  ZMod.castHom c.D_dvd (ZMod c.D)

/-- The first CRT coordinate is the primary-component reduction. -/
lemma split_fst_eq_reduce {d : ℕ} (c : PrimaryComponent d) (x : ZMod d) :
    (c.split x).1 = c.reduce x := by
  have hhom :
      (RingHom.fst (ZMod c.q) (ZMod c.D)).comp c.split.toRingHom = c.reduce :=
    RingHom.ext_zmod _ _
  exact DFunLike.congr_fun hhom x

/-- The second CRT coordinate is reduction to the complementary factor. -/
lemma split_snd_eq_reduceComplement {d : ℕ} (c : PrimaryComponent d) (x : ZMod d) :
    (c.split x).2 = c.reduceComplement x := by
  have hhom :
      (RingHom.snd (ZMod c.q) (ZMod c.D)).comp c.split.toRingHom =
        c.reduceComplement :=
    RingHom.ext_zmod _ _
  exact DFunLike.congr_fun hhom x

/-- Negate the `c.q` CRT coordinate of a root while preserving its `c.D`
coordinate. -/
def flipRoot {d : ℕ} (c : PrimaryComponent d) (lam : Root d) : Root d :=
  ⟨c.combine (-c.reduce lam.1) (c.split lam.1).2, by
    apply c.split.injective
    simp only [map_pow, split_combine, map_neg, map_one]
    apply Prod.ext
    · change (-c.reduce lam.1) ^ 2 = (-1 : ZMod c.q)
      rw [neg_sq, ← map_pow, lam.property]
      simp
    · change (c.split lam.1).2 ^ 2 = (-1 : ZMod c.D)
      have hroot : c.split (lam.1 ^ 2) = c.split (-1) :=
        congrArg c.split lam.property
      rw [map_pow, map_neg, map_one] at hroot
      have hcoord := congrArg Prod.snd hroot
      change (c.split lam.1).2 ^ 2 = (-1 : ZMod c.D) at hcoord
      exact hcoord⟩

@[simp] theorem reduce_flipRoot {d : ℕ} (c : PrimaryComponent d) (lam : Root d) :
    c.reduce (c.flipRoot lam).1 = -c.reduce lam.1 := by
  rw [← c.split_fst_eq_reduce]
  exact c.split_combine_fst _ _

@[simp] theorem reduceComplement_flipRoot {d : ℕ}
    (c : PrimaryComponent d) (lam : Root d) :
    c.reduceComplement (c.flipRoot lam).1 = c.reduceComplement lam.1 := by
  rw [← c.split_snd_eq_reduceComplement, ← c.split_snd_eq_reduceComplement]
  exact c.split_combine_snd _ _

/-- Flipping `c` is invisible to any primary component whose whole modulus
lies in the complementary factor `c.D`. -/
theorem reduce_flipRoot_eq_of_q_dvd_D {d : ℕ}
    (c c' : PrimaryComponent d) (hdiv : c'.q ∣ c.D) (lam : Root d) :
    c'.reduce (c.flipRoot lam).1 = c'.reduce lam.1 := by
  let fromComplement : ZMod c.D →+* ZMod c'.q :=
    ZMod.castHom hdiv (ZMod c'.q)
  have hfactor : fromComplement.comp c.reduceComplement = c'.reduce :=
    RingHom.ext_zmod _ _
  calc
    c'.reduce (c.flipRoot lam).1 =
        fromComplement (c.reduceComplement (c.flipRoot lam).1) := by
      exact (DFunLike.congr_fun hfactor (c.flipRoot lam).1).symm
    _ = fromComplement (c.reduceComplement lam.1) := by
      rw [c.reduceComplement_flipRoot]
    _ = c'.reduce lam.1 := by
      exact DFunLike.congr_fun hfactor lam.1

end PrimaryComponent

end

end Selector.Modular

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorPureExtension.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The pure nontrivial-prime extension

This file carries out the finite prime-extension step when every prime in the
denominator is congruent to one modulo four.  We keep the source's splitting

`d = u * p^a`, `p*d = p^(a+1) * u`, `(p,u)=1`

explicit.  The first lemmas identify the distinguished `p`-primary component
among *all* `PrimaryComponent`s of the enlarged denominator.  This avoids any
dependence on an ordering of a factorization list in the consistency proof.
-/

namespace Selector.PurePrimeExtension

open Erdos215.Selector
open Erdos215.Selector.Modular
open Erdos215.Selector.Final
open Erdos215.Selector.Reconstruct
open Erdos215.Selector.Separation
open Erdos215.Selector.PrimeExtension
open Erdos215.Selector.PartialGood

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The old pure denominator in the `p`-primary splitting. -/
def oldDenom (p u a : ℕ) : ℕ := u * p ^ a

/-- The enlarged denominator, in the literal order required by
`PrimeExtends`. -/
def newDenom (p u a : ℕ) : ℕ := p * oldDenom p u a

lemma newDenom_eq (p u a : ℕ) :
    newDenom p u a = p ^ (a + 1) * u := by
  simp only [newDenom, oldDenom, pow_succ]
  ac_rfl

lemma oldDenom_ne_zero {p u a : ℕ} (hp : p ≠ 0) (hu : u ≠ 0) :
    oldDenom p u a ≠ 0 := by
  exact Nat.mul_ne_zero hu (pow_ne_zero _ hp)

lemma newDenom_ne_zero {p u a : ℕ} (hp : p ≠ 0) (hu : u ≠ 0) :
    newDenom p u a ≠ 0 := by
  exact Nat.mul_ne_zero hp (oldDenom_ne_zero hp hu)

/-- The full `p^(a+1)` component of the enlarged denominator. -/
def newPrimeComponent (p u a : ℕ) (hp : p.Prime)
    (hcop : Nat.Coprime p u) : PrimaryComponent (newDenom p u a) where
  p := p
  a := a + 1
  D := u
  prime := hp
  exp_pos := Nat.succ_pos a
  factor := newDenom_eq p u a
  coprime := hcop.pow_left (a + 1)

@[simp] lemma newPrimeComponent_q (p u a : ℕ) (hp : p.Prime)
    (hcop : Nat.Coprime p u) :
    (newPrimeComponent p u a hp hcop).q = p ^ (a + 1) := rfl

@[simp] lemma newPrimeComponent_D (p u a : ℕ) (hp : p.Prime)
    (hcop : Nat.Coprime p u) :
    (newPrimeComponent p u a hp hcop).D = u := rfl

/-- Any primary component of `u*p^(a+1)` based at `p` is the whole
`p^(a+1)` component.  The proof uses only coprime cancellation, rather than
factorization exponents. -/
theorem component_q_eq_newPrimePower
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a)) (hcp : c.p = p) :
    c.q = p ^ (a + 1) := by
  let q := p ^ (a + 1)
  have hcbase : c.q = p ^ c.a := by simp only [PrimaryComponent.q, hcp]
  have hcu : Nat.Coprime c.q u := by
    rw [hcbase]
    exact hcop.pow_left c.a
  have hcq : c.q ∣ q := by
    apply hcu.dvd_of_dvd_mul_right
    have hdiv : c.q ∣ newDenom p u a := c.q_dvd
    simpa only [newDenom_eq, q] using hdiv
  have hpD : Nat.Coprime p c.D := by
    have hpq : p ∣ c.q := by
      rw [hcbase]
      exact dvd_pow_self p c.exp_pos.ne'
    exact c.coprime.of_dvd_left hpq
  have hqD : Nat.Coprime q c.D := hpD.pow_left (a + 1)
  have hqc : q ∣ c.q := by
    apply hqD.dvd_of_dvd_mul_right
    have hdiv : q ∣ newDenom p u a := by
      rw [newDenom_eq]
      exact dvd_mul_right q u
    rw [c.factor_q] at hdiv
    exact hdiv
  exact Nat.dvd_antisymm hcq hqc

/-- Every other full primary component divides the complementary factor
`u`. -/
theorem component_q_dvd_complement
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a)) (hcp : c.p ≠ p) :
    c.q ∣ u := by
  have hprimeCop : Nat.Coprime c.p p := by
    exact c.prime.coprime_iff_not_dvd.mpr (fun h ↦
      hcp ((Nat.prime_dvd_prime_iff_eq c.prime hp).mp h))
  have hpowCop : Nat.Coprime c.q (p ^ (a + 1)) := by
    simpa only [PrimaryComponent.q] using hprimeCop.pow c.a (a + 1)
  apply hpowCop.dvd_of_dvd_mul_left
  have hdiv : c.q ∣ newDenom p u a := c.q_dvd
  simpa only [newDenom_eq] using hdiv

/-- Exhaustive primary-component classification for the enlarged pure
denominator. -/
theorem component_classification
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a)) :
    (c.p = p ∧ c.q = p ^ (a + 1)) ∨ (c.p ≠ p ∧ c.q ∣ u) := by
  by_cases hcp : c.p = p
  · exact Or.inl ⟨hcp, component_q_eq_newPrimePower hp hcop c hcp⟩
  · exact Or.inr ⟨hcp, component_q_dvd_complement hp hcop c hcp⟩

lemma complement_ne_zero {p u : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u) :
    u ≠ 0 := by
  intro hu
  subst u
  simp only [Nat.coprime_zero_right] at hcop
  exact hp.ne_one hcop

/-- Canonical finite representative of a residue. -/
def residueFin {n : ℕ} (hn : n ≠ 0) (x : ZMod n) : Fin n :=
  ⟨x.val, by
    let _ : NeZero n := ⟨hn⟩
    exact ZMod.val_lt x⟩

@[simp] lemma residueFin_cast {n : ℕ} (hn : n ≠ 0) (x : ZMod n) :
    (((residueFin hn x : Fin n) : ℕ) : ZMod n) = x := by
  let _ : NeZero n := ⟨hn⟩
  exact ZMod.natCast_zmod_val x

/-- Reduction of a root along a divisor of its modulus. -/
def reduceRootOfDvd {m n : ℕ} (h : m ∣ n) (lam : Root n) : Root m :=
  ⟨ZMod.castHom h (ZMod m) lam.1, by
    rw [← map_pow, lam.property]
    rw [map_neg, map_one]⟩

@[simp] lemma reduceRootOfDvd_coe {m n : ℕ} (h : m ∣ n) (lam : Root n) :
    (reduceRootOfDvd h lam : ZMod m) = ZMod.castHom h (ZMod m) lam.1 := rfl

/-- The canonical old lift copied to all `p²` residue cosets. -/
def copiedLift (p u a : ℕ) (s : LiftData (oldDenom p u a)) :
    LiftData (newDenom p u a) :=
  primeCopyLift p s

theorem copiedLift_primeExtends {p u a : ℕ} (hp : 0 < p)
    (s : LiftData (oldDenom p u a)) :
    PrimeExtends p hp s (copiedLift p u a s) := by
  exact primeCopy_primeExtends p hp s

/-- The explicit quotient guide which moves an input into class zero modulo
`p`; this is the source's function `r` in (4.11). -/
def oldShiftGuide (p u : ℕ) {N : ℕ} (i : Fin N) : ℕ :=
  shiftGuide p u 0 i

lemma oldShiftGuide_zero {p u N : ℕ} (hp : 0 < p)
    (i : Fin N) (hi : i.1 % p = 0) :
    oldShiftGuide p u i = 0 := by
  letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have hz : (((⟨0, hp⟩ : Fin p) : ℕ) : ZMod p) = 0 := by
    change ((0 : ℕ) : ZMod p) = 0
    simp
  have h := shiftGuide_zero_mod (u := u) (target := ⟨0, hp⟩) i hi
  rw [hz] at h
  exact h

/-- Raw formula (4.12), before goodness is proved: extend the copied old
line map from the old input class to all inputs. -/
def oldLineExtension (p u a : ℕ) (hp : p ≠ 0) (hu : u ≠ 0)
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a)) :
    Fin (newDenom p u a) → Fin (newDenom p u a) :=
  partialGoodExtension (newDenom p u a) u (oldDenom p u a)
    (oldShiftGuide p u) (inducedFamily (newDenom_ne_zero hp hu)
      (copiedLift p u a s) lam jtilde)

lemma oldLineExtension_eq_on_old_input
    {p u a : ℕ} (hp : 0 < p) (hu : u ≠ 0)
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a))
    (hi : i.1 % p = 0) :
    oldLineExtension p u a hp.ne' hu s lam jtilde i =
      inducedFamily (newDenom_ne_zero hp.ne' hu)
        (copiedLift p u a s) lam jtilde i := by
  apply partialGoodExtension_eq_on_distinguished
    (oldShiftGuide p u)
    (inducedFamily (newDenom_ne_zero hp.ne' hu) (copiedLift p u a s) lam jtilde)
    (fun x hx ↦ oldShiftGuide_zero hp x hx) i hi

lemma prime_dvd_newDenom (p u a : ℕ) : p ∣ newDenom p u a := by
  exact dvd_mul_right p (oldDenom p u a)

/-- Reduction of an enlarged root modulo the new prime. -/
def primeRoot (p u a : ℕ) (lam : Root (newDenom p u a)) : Root p :=
  reduceRootOfDvd (prime_dvd_newDenom p u a) lam

/-- The line label reduced modulo the new prime. -/
def primeLabel (p : ℕ) {N : ℕ} (jtilde : Fin N) : ZMod p := jtilde.1

lemma primeRoot_isUnit {p u a : ℕ} (lam : Root (newDenom p u a)) :
    IsUnit (primeRoot p u a lam : ZMod p) :=
  root_isUnit (primeRoot p u a lam)

/-- For an odd prime, the two opposite reductions of a root have invertible
difference. -/
lemma primeRoot_sub_neg_isUnit {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (lam : Root (newDenom p u a)) :
    IsUnit ((primeRoot p u a lam : ZMod p) -
      -(primeRoot p u a lam : ZMod p)) := by
  have hcop2 : Nat.Coprime 2 p := by
    exact Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr (fun h ↦
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)))
  have htwo : IsUnit (2 : ZMod p) :=
    (ZMod.isUnit_iff_coprime 2 p).2 hcop2
  have hprod := htwo.mul (primeRoot_isUnit (p := p) (u := u) (a := a) lam)
  convert hprod using 1 <;> ring

/-- The distinguished source residue (4.10), now as a `Fin p`.  The same
formula gives zero for an old line label, so no case split is needed. -/
def distinguishedClass (p u a : ℕ) (hp : p.Prime)
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a)) : Fin p :=
  residueFin hp.ne_zero
    (distinguishedResidue (primeRoot p u a lam) (primeLabel p jtilde))

@[simp] lemma distinguishedClass_cast (p u a : ℕ) (hp : p.Prime)
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a)) :
    ((distinguishedClass p u a hp lam jtilde : ℕ) : ZMod p) =
      distinguishedResidue (primeRoot p u a lam) (primeLabel p jtilde) := by
  exact residueFin_cast hp.ne_zero _

/-- The canonical quotient guide carrying an arbitrary argument to the
line's distinguished source class. -/
def lineShiftGuide (p u a : ℕ) (hp : p.Prime)
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a))
    (i : Fin (newDenom p u a)) : ℕ :=
  shiftGuide p u (distinguishedClass p u a hp lam jtilde : ZMod p) i

/-- Remove the least base-`p` digit and retain the next `a` digits.  On one
fixed residue class modulo `p`, this is exactly the input of the permutation
`ρ` in (4.14). -/
def primaryDigit (p a : ℕ) (hp : p.Prime) {N : ℕ} (i : Fin N) :
    Fin (p ^ a) :=
  ⟨(i.1 / p) % p ^ a, Nat.mod_lt _ (pow_pos hp.pos a)⟩

@[simp] lemma primaryDigit_val (p a : ℕ) (hp : p.Prime) {N : ℕ}
    (i : Fin N) :
    (primaryDigit p a hp i : ℕ) = (i.1 / p) % p ^ a := rfl

/-- The canonical representative of a line label modulo the enlarged
`p`-power. -/
def primaryLabelRepresentative (p a : ℕ) {N : ℕ} (jtilde : Fin N) : ℕ :=
  jtilde.1 % p ^ (a + 1)

lemma primaryPower_dvd_label_sub (p a : ℕ) {N : ℕ} (jtilde : Fin N) :
    (p ^ (a + 1) : ℤ) ∣
      (jtilde.1 : ℤ) - primaryLabelRepresentative p a jtilde := by
  simp only [primaryLabelRepresentative]
  have hnat : p ^ (a + 1) ∣ jtilde.1 - jtilde.1 % p ^ (a + 1) :=
    Nat.dvd_sub_mod jtilde.1
  obtain ⟨k, hk⟩ := hnat
  refine ⟨(k : ℤ), ?_⟩
  rw [← Int.ofNat_sub (Nat.mod_le _ _), hk]
  push_cast
  rfl

/-- The `p^(a+1)`-coordinate in (4.14), including its indispensable line
constant. -/
def primaryDistinguishedValue
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    ZMod (p ^ (a + 1)) :=
  let cP := newPrimeComponent p u a hp hcop
  (((rho (primaryDigit p a hp i) : Fin (p ^ a)) : ℕ) : ZMod cP.q) -
    cP.reduce lam * cP.localQuotient
      ((jtilde.1 : ℤ) - primaryLabelRepresentative p a jtilde)

/-- The localized quotient for the complementary factor `u` in
`newDenom = u*p^(a+1)`. -/
def complementLocalQuotient (p u a : ℕ) (z : ℤ) : ZMod u :=
  localizedQuotient u ((p ^ (a + 1) : ZMod u))⁻¹ z

lemma complementPower_isUnit {p u a : ℕ} (hcop : Nat.Coprime p u) :
    IsUnit (p ^ (a + 1) : ZMod u) := by
  simpa using ((ZMod.isUnit_iff_coprime (p ^ (a + 1)) u).2
    (hcop.pow_left (a + 1)))

lemma complementLocalQuotient_mul_power
    {p u a : ℕ} (hu : u ≠ 0) (hcop : Nat.Coprime p u) (z : ℤ) :
    complementLocalQuotient p u a z * (p ^ (a + 1) : ZMod u) =
      (z / (u : ℤ) : ℤ) := by
  simp only [complementLocalQuotient, localizedQuotient, mul_assoc]
  rw [ZMod.inv_mul_of_unit _ (complementPower_isUnit hcop)]
  simp

/-- Flip only the enlarged `p^(a+1)` coordinate of a global root. -/
def flippedRoot (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) : Root (newDenom p u a) :=
  (newPrimeComponent p u a hp hcop).flipRoot lam

@[simp] lemma newPrimeComponent_reduce_flippedRoot
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) :
    (newPrimeComponent p u a hp hcop).reduce
        (flippedRoot p u a hp hcop lam) =
      -(newPrimeComponent p u a hp hcop).reduce lam := by
  exact PrimaryComponent.reduce_flipRoot _ _

@[simp] lemma primeRoot_flippedRoot
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) :
    (primeRoot p u a (flippedRoot p u a hp hcop lam) : ZMod p) =
      -(primeRoot p u a lam : ZMod p) := by
  let cP := newPrimeComponent p u a hp hcop
  let down : ZMod cP.q →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero a)) (ZMod p)
  have hcomp : down.comp cP.reduce =
      ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) :=
    RingHom.ext_zmod _ _
  change ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p)
      (flippedRoot p u a hp hcop lam).1 =
    -ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam.1
  rw [← DFunLike.congr_fun hcomp, ← DFunLike.congr_fun hcomp]
  change down (cP.reduce (flippedRoot p u a hp hcop lam)) =
    -down (cP.reduce lam)
  rw [newPrimeComponent_reduce_flippedRoot]
  exact map_neg down _

lemma reduce_flippedRoot_eq_of_other_component
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a)) (hcp : c.p ≠ p)
    (lam : Root (newDenom p u a)) :
    c.reduce (flippedRoot p u a hp hcop lam) = c.reduce lam := by
  exact PrimaryComponent.reduce_flipRoot_eq_of_q_dvd_D
    (newPrimeComponent p u a hp hcop) c
    (component_q_dvd_complement hp hcop c hcp) lam

/-- The old auxiliary line label through the point of the original line at
the specified argument.  In residues this is
`J + i*(lambda-flip(lambda))`. -/
def auxiliaryLabel
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    Fin (newDenom p u a) :=
  residueFin (newDenom_ne_zero hp.ne_zero
    (complement_ne_zero hp hcop))
    ((((jtilde : ℕ) : ZMod (newDenom p u a)) +
      (((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam : ZMod (newDenom p u a)) -
          (flippedRoot p u a hp hcop lam : ZMod (newDenom p u a))))))

@[simp] lemma auxiliaryLabel_cast
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    (((auxiliaryLabel p u a hp hcop lam jtilde i : ℕ) :
        ZMod (newDenom p u a))) =
      ((jtilde : ℕ) : ZMod (newDenom p u a)) +
        ((i : ℕ) : ZMod (newDenom p u a)) *
          ((lam : ZMod (newDenom p u a)) -
            (flippedRoot p u a hp hcop lam : ZMod (newDenom p u a))) := by
  exact residueFin_cast _ _

lemma auxiliaryLabel_relation
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam : ZMod (newDenom p u a)) -
          (flippedRoot p u a hp hcop lam : ZMod (newDenom p u a))) =
      -((((jtilde : ℕ) : ZMod (newDenom p u a)) -
        ((auxiliaryLabel p u a hp hcop lam jtilde i : ℕ) :
          ZMod (newDenom p u a)))) := by
  rw [auxiliaryLabel_cast]
  ring

lemma complement_dvd_label_sub_auxiliary
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    (u : ℤ) ∣ (jtilde.1 : ℤ) -
      (auxiliaryLabel p u a hp hcop lam jtilde i).1 := by
  let cP := newPrimeComponent p u a hp hcop
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ u).mp
  have hrel := congrArg cP.reduceComplement
    (auxiliaryLabel_relation p u a hp hcop lam jtilde i)
  simp only [map_mul, map_sub, map_neg, map_natCast] at hrel
  simp only [flippedRoot] at hrel
  rw [PrimaryComponent.reduceComplement_flipRoot, sub_self, mul_zero] at hrel
  push_cast at hrel ⊢
  exact neg_eq_zero.mp hrel.symm

/-- At the distinguished argument the auxiliary line label is old, i.e. is
divisible by `p`.  This is equation (4.10) with the flipped root. -/
lemma auxiliaryLabel_isOld
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a))
    (hi : i.1 % p = (distinguishedClass p u a hp lam jtilde : ℕ)) :
    (auxiliaryLabel p u a hp hcop lam jtilde i : ℕ) % p = 0 := by
  have hiCast : ((i.1 : ℕ) : ZMod p) =
      distinguishedResidue (primeRoot p u a lam) (primeLabel p jtilde) := by
    calc
      ((i.1 : ℕ) : ZMod p) = ((i.1 % p : ℕ) : ZMod p) := by
        exact (ZMod.natCast_mod i.1 p).symm
      _ = (((distinguishedClass p u a hp lam jtilde : ℕ) : ℕ) : ZMod p) := by
        rw [hi]
      _ = distinguishedResidue (primeRoot p u a lam) (primeLabel p jtilde) :=
        distinguishedClass_cast p u a hp lam jtilde
  have hunit := primeRoot_sub_neg_isUnit hp hp2 lam
  have hrel := distinguishedResidue_relation
    (primeRoot p u a lam) (primeLabel p jtilde) hunit
  have hcast :
      (((auxiliaryLabel p u a hp hcop lam jtilde i : ℕ) : ℕ) : ZMod p) = 0 := by
    have haux := congrArg
      (ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p))
      (auxiliaryLabel_cast p u a hp hcop lam jtilde i)
    simp only [map_add, map_mul, map_sub, map_natCast] at haux
    have hflip :
        ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p)
            (flippedRoot p u a hp hcop lam).1 =
          -ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam.1 := by
      exact primeRoot_flippedRoot p u a hp hcop lam
    change (((auxiliaryLabel p u a hp hcop lam jtilde i : ℕ) : ℕ) : ZMod p) = 0
    rw [haux, hiCast, hflip]
    change primeLabel p jtilde +
      distinguishedResidue (primeRoot p u a lam) (primeLabel p jtilde) *
        ((primeRoot p u a lam : ZMod p) - -(primeRoot p u a lam : ZMod p)) = 0
    rw [hrel]
    exact add_neg_cancel _
  exact Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff
    (auxiliaryLabel p u a hp hcop lam jtilde i : ℕ) p).mp hcast)

/-- If the entire enlarged `p`-power divides an input difference, the two
canonical auxiliary old labels coincide.  The `p`-coordinate vanishes by
the input hypothesis and the complementary coordinate vanishes because the
flipped root is unchanged there. -/
lemma auxiliaryLabel_eq_of_primaryPower_dvd_indexDiff
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (jtilde i₁ i₂ : Fin (newDenom p u a))
    (hpow : p ^ (a + 1) ∣ indexDiff i₁ i₂) :
    auxiliaryLabel p u a hp hcop lam jtilde i₁ =
      auxiliaryLabel p u a hp hcop lam jtilde i₂ := by
  let cP := newPrimeComponent p u a hp hcop
  have hmod : i₁.1 ≡ i₂.1 [MOD p ^ (a + 1)] := by
    rw [Nat.modEq_iff_dvd]
    have hz : (p ^ (a + 1) : ℤ) ∣
        (i₂.1 : ℤ) - (i₁.1 : ℤ) := by
      rw [← Int.natAbs_dvd_natAbs]
      have habs : Int.natAbs ((i₂.1 : ℤ) - i₁.1) =
          Int.natAbs ((i₁.1 : ℤ) - i₂.1) := by
        rw [show ((i₂.1 : ℤ) - i₁.1) = -((i₁.1 : ℤ) - i₂.1) by ring,
          Int.natAbs_neg]
      rw [Int.natAbs_pow, Int.natAbs_natCast, habs]
      exact hpow
    exact_mod_cast hz
  have hiq : (i₁.1 : ZMod cP.q) = (i₂.1 : ZMod cP.q) := by
    exact (ZMod.natCast_eq_natCast_iff _ _ cP.q).2 hmod
  apply fin_eq_of_zmod_cast_eq
    (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
  rw [auxiliaryLabel_cast, auxiliaryLabel_cast]
  congr 1
  apply cP.split.injective
  apply Prod.ext
  · rw [cP.split_fst_eq_reduce, cP.split_fst_eq_reduce]
    simp only [map_mul, map_sub, map_natCast]
    rw [hiq]
  · rw [cP.split_snd_eq_reduceComplement, cP.split_snd_eq_reduceComplement]
    simp only [map_mul, map_sub, map_natCast]
    change _ * (cP.reduceComplement lam - cP.reduceComplement (cP.flipRoot lam)) =
      _ * (cP.reduceComplement lam - cP.reduceComplement (cP.flipRoot lam))
    rw [cP.reduceComplement_flipRoot, sub_self, mul_zero, mul_zero]

/-- The complementary CRT coordinate of (4.13), using the canonical root
which is flipped only at the new prime power. -/
def complementDistinguishedValue
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    ZMod u :=
  let cP := newPrimeComponent p u a hp hcop
  let mu := flippedRoot p u a hp hcop lam
  let jt := auxiliaryLabel p u a hp hcop lam jtilde i
  (show ZMod u from cP.reduceComplement
      (((oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop)
        s mu jt i : Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))) -
    (show ZMod u from cP.reduceComplement lam) * complementLocalQuotient p u a
      ((jtilde.1 : ℤ) - (jt.1 : ℤ))

/-- CRT combination of (4.13) and (4.14) on the distinguished input class. -/
def distinguishedValue
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    Fin (newDenom p u a) :=
  let cP := newPrimeComponent p u a hp hcop
  residueFin (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
    (cP.combine
      (primaryDistinguishedValue p u a hp hcop rho lam jtilde i)
      (complementDistinguishedValue p u a hp hcop s lam jtilde i))

@[simp] lemma distinguishedValue_split
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    (newPrimeComponent p u a hp hcop).split
        ((((distinguishedValue p u a hp hcop rho s lam jtilde i :
          Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))) =
      (primaryDistinguishedValue p u a hp hcop rho lam jtilde i,
        complementDistinguishedValue p u a hp hcop s lam jtilde i) := by
  rw [distinguishedValue, residueFin_cast]
  exact PrimaryComponent.split_combine _ _ _

/-- Formula (4.15): extend the distinguished-class values to a full line
map by the same explicit partial-good extension used in Lemma 4.8. -/
def newLineExtension
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a)) :
    Fin (newDenom p u a) → Fin (newDenom p u a) :=
  partialGoodExtension (newDenom p u a) u (oldDenom p u a)
    (lineShiftGuide p u a hp lam jtilde)
    (distinguishedValue p u a hp hcop rho s lam jtilde)

lemma lineShiftGuide_zero_on_distinguished
    {p u a : ℕ} (hp : p.Prime)
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a))
    (hi : i.1 % p = (distinguishedClass p u a hp lam jtilde : ℕ)) :
    lineShiftGuide p u a hp lam jtilde i = 0 := by
  exact shiftGuide_zero_mod (u := u)
    (distinguishedClass p u a hp lam jtilde) i hi

lemma newLineExtension_eq_on_distinguished
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a))
    (hi : i.1 % p = (distinguishedClass p u a hp lam jtilde : ℕ)) :
    newLineExtension p u a hp hcop rho s lam jtilde i =
      distinguishedValue p u a hp hcop rho s lam jtilde i := by
  apply partialGoodExtension_eq_on_distinguished
    (lineShiftGuide p u a hp lam jtilde)
    (distinguishedValue p u a hp hcop rho s lam jtilde)
    (fun x hx ↦ lineShiftGuide_zero_on_distinguished hp lam jtilde x hx)
    i hi

/-- The complete raw line family at the enlarged denominator. -/
def extendedFamily
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a)) : RawLineFamily (newDenom p u a) :=
  fun lam jtilde ↦
    if jtilde.1 % p = 0 then
      oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop) s lam jtilde
    else
      newLineExtension p u a hp hcop rho s lam jtilde

lemma extendedFamily_old
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a))
    (hj : jtilde.1 % p = 0) :
    extendedFamily p u a hp hcop rho s lam jtilde =
      oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop) s lam jtilde := by
  simp only [extendedFamily, if_pos hj]

lemma extendedFamily_new
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a))
    (hj : jtilde.1 % p ≠ 0) :
    extendedFamily p u a hp hcop rho s lam jtilde =
      newLineExtension p u a hp hcop rho s lam jtilde := by
  simp only [extendedFamily, if_neg hj]

/-- The target line label of the line through an old cell. -/
def oldCellLineLabel
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (i j : Fin (oldDenom p u a)) :
    Fin (newDenom p u a) :=
  cellLineLabel (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop)) lam
    (oldIndex p hp.pos i) (oldIndex p hp.pos j)

lemma oldIndex_mod_prime
    {p d : ℕ} (hp : 0 < p) (i : Fin d) :
    (oldIndex p hp i : ℕ) % p = 0 := by
  simp only [oldIndex, Nat.mul_mod_right]

lemma oldCellLineLabel_isOld
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (i j : Fin (oldDenom p u a)) :
    (oldCellLineLabel p u a hp hcop lam i j : ℕ) % p = 0 := by
  let N := newDenom p u a
  let jt := oldCellLineLabel p u a hp hcop lam i j
  have hcast : ((jt.1 : ℕ) : ZMod p) = 0 := by
    have hlabel := congrArg (ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p))
      (cellLineLabel_cast
        (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop)) lam
        (oldIndex p hp.pos i) (oldIndex p hp.pos j))
    change ((jt.1 : ℕ) : ZMod p) = 0
    simp only [map_sub, map_mul, map_natCast] at hlabel
    have hi0 : (((oldIndex p hp.pos i : ℕ) : ℕ) : ZMod p) = 0 := by
      apply (ZMod.natCast_eq_zero_iff _ p).2
      exact Nat.dvd_mul_right p i.1
    have hj0 : (((oldIndex p hp.pos j : ℕ) : ℕ) : ZMod p) = 0 := by
      apply (ZMod.natCast_eq_zero_iff _ p).2
      exact Nat.dvd_mul_right p j.1
    rw [hi0, hj0, mul_zero, sub_zero] at hlabel
    exact hlabel
  exact Nat.dvd_iff_mod_eq_zero.mp
    ((ZMod.natCast_eq_zero_iff jt.1 p).mp hcast)

/-- On every root line through an old cell, the enlarged family retains the
copied old induced-family value. -/
lemma extendedFamily_eq_copied_on_old_cell
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (i j : Fin (oldDenom p u a)) :
    extendedFamily p u a hp hcop rho s lam
        (oldCellLineLabel p u a hp hcop lam i j) (oldIndex p hp.pos i) =
      inducedFamily (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
        (copiedLift p u a s) lam
        (oldCellLineLabel p u a hp hcop lam i j) (oldIndex p hp.pos i) := by
  rw [extendedFamily_old hp hcop rho s lam
    (oldCellLineLabel p u a hp hcop lam i j)
    (oldCellLineLabel_isOld hp hcop lam i j)]
  exact oldLineExtension_eq_on_old_input hp.pos (complement_ne_zero hp hcop)
    s lam (oldCellLineLabel p u a hp hcop lam i j) (oldIndex p hp.pos i)
    (oldIndex_mod_prime hp.pos i)

/-- At an old cell, the target attached to every target root is exactly the
line equation satisfied by the copied old integral lifts. -/
lemma cellTarget_extendedFamily_oldCell
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (i j : Fin (oldDenom p u a)) :
    cellTarget (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
        (extendedFamily p u a hp hcop rho s) lam
        (oldIndex p hp.pos i) (oldIndex p hp.pos j) =
      ((s.k i j : ℤ) : ZMod (newDenom p u a)) +
        (lam : ZMod (newDenom p u a)) *
          ((s.l i j : ℤ) : ZMod (newDenom p u a)) := by
  let hn : newDenom p u a ≠ 0 :=
    newDenom_ne_zero (a := a) hp.ne_zero (complement_ne_zero hp hcop)
  let I := oldIndex p hp.pos i
  let J := oldIndex p hp.pos j
  let jt := oldCellLineLabel p u a hp hcop lam i j
  have hfamily := congrArg (fun z : Fin (newDenom p u a) ↦
      (((z : Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)))
    (extendedFamily_eq_copied_on_old_cell hp hcop rho s lam i j)
  have hinduced := inducedFamily_formula hn (copiedLift p u a s) lam jt I
  have hcell : lineCell hn lam jt I = J := lineCell_cellLineLabel hn lam I J
  change lineResidue hn lam jt I = J at hcell
  have hk : (copiedLift p u a s).k I J = s.k i j := by
    exact (primeCopy_primeExtends p hp.pos s i j).1
  have hl : (copiedLift p u a s).l I J = s.l i j := by
    exact (primeCopy_primeExtends p hp.pos s i j).2
  change lineTarget hn (extendedFamily p u a hp hcop rho s) lam jt I = _
  simp only [lineTarget]
  rw [hfamily, hinduced]
  simp only [lineValue, hcell, hk, hl]
  ring

/-- Two opposite-root cell equations determine the reconstructed residues
uniquely. -/
lemma reconstructed_eq_of_opposite_cellTargets
    {d : ℕ} (hd : d ≠ 0) (hodd : Nat.Coprime 2 d)
    (F : RawLineFamily d) (lam₀ : Root d) (i j : Fin d) (k l : ZMod d)
    (hplus : cellTarget hd F lam₀ i j = k + (lam₀ : ZMod d) * l)
    (hminus : cellTarget hd F (negRoot lam₀) i j =
      k + (negRoot lam₀ : ZMod d) * l) :
    reconstructedK hd F lam₀ i j = k ∧ reconstructedL hd F lam₀ i j = l := by
  have hunit := root_sub_negRoot_isUnit hodd lam₀
  have hinv := ZMod.inv_mul_of_unit
    ((lam₀ : ZMod d) - (negRoot lam₀ : ZMod d)) hunit
  have hl : reconstructedL hd F lam₀ i j = l := by
    simp only [reconstructedL, hplus, hminus]
    calc
      ((lam₀ : ZMod d) - (negRoot lam₀ : ZMod d))⁻¹ *
          ((k + (lam₀ : ZMod d) * l) -
            (k + (negRoot lam₀ : ZMod d) * l)) =
          (((lam₀ : ZMod d) - (negRoot lam₀ : ZMod d))⁻¹ *
            ((lam₀ : ZMod d) - (negRoot lam₀ : ZMod d))) * l := by ring
      _ = l := by rw [hinv, one_mul]
  refine ⟨?_, hl⟩
  simp only [reconstructedK, hplus, hl]
  ring

/-- A cell of the enlarged residue square belongs to the literally embedded
old square precisely when both coordinates are divisible by `p`. -/
def IsOldCell (p : ℕ) {N : ℕ} (i j : Fin N) : Prop :=
  i.1 % p = 0 ∧ j.1 % p = 0

private lemma exists_oldIndex_of_zero_mod (p : ℕ) (hp : 0 < p) {d : ℕ}
    (x : Fin (p * d)) (hx : x.1 % p = 0) :
    ∃ i : Fin d, x = oldIndex p hp i := by
  have hpx : p ∣ x.1 := Nat.dvd_iff_mod_eq_zero.mpr hx
  have hlt : x.1 / p < d := by
    apply (Nat.div_lt_iff_lt_mul hp).2
    have hxlt : x.1 < p * d := x.2
    simpa only [Nat.mul_comm] using hxlt
  refine ⟨⟨x.1 / p, hlt⟩, ?_⟩
  apply Fin.ext
  change x.1 = p * (x.1 / p)
  exact (Nat.mul_div_cancel' hpx).symm

/-- Reconstruction from a good consistent family can retain all copied old
integral lifts literally, provided the family has the copied line targets on
old cells. -/
theorem reconstruct_preserving_oldCells
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (hodd : Nat.Coprime 2 (newDenom p u a))
    (C : CompleteComponents (newDenom p u a))
    (hroot : ConflictRootLineProperty (newDenom p u a))
    (F : RawLineFamily (newDenom p u a))
    (hgood : FamilyGood F) (hcons : FamilyConsistent F)
    (lam₀ : Root (newDenom p u a))
    (s : LiftData (oldDenom p u a))
    (htarget : ∀ (lam : Root (newDenom p u a))
      (i j : Fin (oldDenom p u a)),
      cellTarget (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
          F lam (oldIndex p hp.pos i) (oldIndex p hp.pos j) =
        ((s.k i j : ℤ) : ZMod (newDenom p u a)) +
          (lam : ZMod (newDenom p u a)) *
            ((s.l i j : ℤ) : ZMod (newDenom p u a))) :
    ∃ t : LiftData (newDenom p u a),
      PrimeExtends p hp.pos s t ∧ t.Separated := by
  let hn : newDenom p u a ≠ 0 :=
    newDenom_ne_zero (a := a) hp.ne_zero (complement_ne_zero hp hcop)
  let old := copiedLift p u a s
  let r := residueSolution_of_consistent hn hodd F hcons lam₀
    (primaryReductionsDetect_of_complete C hn)
    (rootSignsCovered_of_odd hodd lam₀)
  have hk : ∀ I J, IsOldCell p I J → ((old.k I J : ℤ) :
      ZMod (newDenom p u a)) = r.k I J := by
    intro I J hIJ
    obtain ⟨i, hi⟩ := exists_oldIndex_of_zero_mod p hp.pos I hIJ.1
    obtain ⟨j, hj⟩ := exists_oldIndex_of_zero_mod p hp.pos J hIJ.2
    subst I
    subst J
    have holdk : old.k (oldIndex p hp.pos i) (oldIndex p hp.pos j) = s.k i j :=
      (copiedLift_primeExtends hp.pos s i j).1
    have holdl : old.l (oldIndex p hp.pos i) (oldIndex p hp.pos j) = s.l i j :=
      (copiedLift_primeExtends hp.pos s i j).2
    have hrec := reconstructed_eq_of_opposite_cellTargets hn hodd F lam₀
      (oldIndex p hp.pos i) (oldIndex p hp.pos j)
      (((old.k (oldIndex p hp.pos i) (oldIndex p hp.pos j) : ℤ) :
        ZMod (newDenom p u a)))
      (((old.l (oldIndex p hp.pos i) (oldIndex p hp.pos j) : ℤ) :
        ZMod (newDenom p u a)))
      (by simpa only [holdk, holdl] using htarget lam₀ i j)
      (by simpa only [holdk, holdl] using htarget (negRoot lam₀) i j)
    change ((old.k (oldIndex p hp.pos i) (oldIndex p hp.pos j) : ℤ) :
      ZMod (newDenom p u a)) = reconstructedK hn F lam₀
        (oldIndex p hp.pos i) (oldIndex p hp.pos j)
    exact hrec.1.symm
  have hl : ∀ I J, IsOldCell p I J → ((old.l I J : ℤ) :
      ZMod (newDenom p u a)) = r.l I J := by
    intro I J hIJ
    obtain ⟨i, hi⟩ := exists_oldIndex_of_zero_mod p hp.pos I hIJ.1
    obtain ⟨j, hj⟩ := exists_oldIndex_of_zero_mod p hp.pos J hIJ.2
    subst I
    subst J
    have holdk : old.k (oldIndex p hp.pos i) (oldIndex p hp.pos j) = s.k i j :=
      (copiedLift_primeExtends hp.pos s i j).1
    have holdl : old.l (oldIndex p hp.pos i) (oldIndex p hp.pos j) = s.l i j :=
      (copiedLift_primeExtends hp.pos s i j).2
    have hrec := reconstructed_eq_of_opposite_cellTargets hn hodd F lam₀
      (oldIndex p hp.pos i) (oldIndex p hp.pos j)
      (((old.k (oldIndex p hp.pos i) (oldIndex p hp.pos j) : ℤ) :
        ZMod (newDenom p u a)))
      (((old.l (oldIndex p hp.pos i) (oldIndex p hp.pos j) : ℤ) :
        ZMod (newDenom p u a)))
      (by simpa only [holdk, holdl] using htarget lam₀ i j)
      (by simpa only [holdk, holdl] using htarget (negRoot lam₀) i j)
    change ((old.l (oldIndex p hp.pos i) (oldIndex p hp.pos j) : ℤ) :
      ZMod (newDenom p u a)) = reconstructedL hn F lam₀
        (oldIndex p hp.pos i) (oldIndex p hp.pos j)
    exact hrec.2.symm
  let t := liftDataOfResidueSolutionPreserving r old (IsOldCell p)
  have hrealize : inducedFamily hn t = F :=
    inducedFamily_liftDataOfResidueSolutionPreserving r old (IsOldCell p) hk hl
  refine ⟨t, ?_, separated_of_inducedFamily_eq_good hn hodd hroot t hrealize hgood⟩
  intro i j
  have hpres := liftDataOfResidueSolutionPreserving_eq_old r old (IsOldCell p)
    (oldIndex p hp.pos i) (oldIndex p hp.pos j)
    ⟨oldIndex_mod_prime hp.pos i, oldIndex_mod_prime hp.pos j⟩
  have hcopy := copiedLift_primeExtends hp.pos s i j
  exact ⟨hpres.1.trans hcopy.1, hpres.2.trans hcopy.2⟩

/-- Once goodness and consistency of the explicit family are established,
the resulting selector is a literal separated prime extension. -/
theorem purePrimeExtension_of_family
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (hodd : Nat.Coprime 2 (newDenom p u a))
    (C : CompleteComponents (newDenom p u a))
    (hroot : ConflictRootLineProperty (newDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (hgood : FamilyGood (extendedFamily p u a hp hcop rho s))
    (hcons : FamilyConsistent (extendedFamily p u a hp hcop rho s))
    (lam₀ : Root (newDenom p u a)) :
    ∃ t : LiftData (newDenom p u a),
      PrimeExtends p hp.pos s t ∧ t.Separated := by
  apply reconstruct_preserving_oldCells hp hcop hodd C hroot
    (extendedFamily p u a hp hcop rho s) hgood hcons lam₀ s
  exact cellTarget_extendedFamily_oldCell hp hcop rho s

end

end Selector.PurePrimeExtension

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorPrimeClassGood.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

namespace Selector.PrimeClassGood

open Erdos215.Selector

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- After restricting an index to one class modulo `p`, divide away the
mandatory factor `p` and retain its next `a` base-`p` digits. -/
def classDigit (p a : ℕ) (hp : 0 < p) {N : ℕ} (i : Fin N) : Fin (p ^ a) :=
  ⟨(i.1 / p) % p ^ a, Nat.mod_lt _ (pow_pos hp a)⟩

/-- Absolute difference of the integer quotients after dividing by `p`. -/
def quotientDiff (p : ℕ) {N : ℕ} (i j : Fin N) : ℕ :=
  Int.natAbs (((i.1 / p : ℕ) : ℤ) - ((j.1 / p : ℕ) : ℤ))

private lemma natMod_intModEq (m x : ℕ) :
    ((x % m : ℕ) : ℤ) ≡ (x : ℤ) [ZMOD (m : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  have h : (x : ℤ) = (x % m : ℕ) + (m : ℤ) * (x / m : ℕ) := by
    exact_mod_cast (Nat.mod_add_div x m).symm
  use (x / m : ℕ)
  omega

private lemma gcd_natAbs_sub_eq_of_intModEq
    {m x y x' y' : ℕ}
    (h : ((x : ℤ) - (y : ℤ)) ≡ ((x' : ℤ) - (y' : ℤ)) [ZMOD (m : ℤ)]) :
    Nat.gcd m (Int.natAbs ((x : ℤ) - (y : ℤ))) =
      Nat.gcd m (Int.natAbs ((x' : ℤ) - (y' : ℤ))) := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    rw [← Int.natCast_dvd_natCast]
    apply Int.dvd_natAbs.mpr
    have hgM : ((Nat.gcd m (Int.natAbs ((x : ℤ) - (y : ℤ))) : ℕ) : ℤ) ∣
        (m : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left m (Int.natAbs ((x : ℤ) - (y : ℤ)))
    have hgxy : ((Nat.gcd m (Int.natAbs ((x : ℤ) - (y : ℤ))) : ℕ) : ℤ) ∣
        (x : ℤ) - (y : ℤ) := by
      rw [← Int.dvd_natAbs]
      exact_mod_cast Nat.gcd_dvd_right m (Int.natAbs ((x : ℤ) - (y : ℤ)))
    rw [Int.modEq_iff_dvd] at h
    have hz := hgxy.add (hgM.trans h)
    have heq : (x : ℤ) - (y : ℤ) +
        ((x' : ℤ) - (y' : ℤ) - ((x : ℤ) - (y : ℤ))) =
          (x' : ℤ) - (y' : ℤ) := by ring
    rw [heq] at hz
    exact hz
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    rw [← Int.natCast_dvd_natCast]
    apply Int.dvd_natAbs.mpr
    have hgM : ((Nat.gcd m (Int.natAbs ((x' : ℤ) - (y' : ℤ))) : ℕ) : ℤ) ∣
        (m : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left m (Int.natAbs ((x' : ℤ) - (y' : ℤ)))
    have hgxy : ((Nat.gcd m (Int.natAbs ((x' : ℤ) - (y' : ℤ))) : ℕ) : ℤ) ∣
        (x' : ℤ) - (y' : ℤ) := by
      rw [← Int.dvd_natAbs]
      exact_mod_cast Nat.gcd_dvd_right m (Int.natAbs ((x' : ℤ) - (y' : ℤ)))
    rw [Int.modEq_iff_dvd] at h
    simpa only [sub_sub_cancel] using hgxy.sub (hgM.trans h)

lemma indexDiff_eq_mul_quotientDiff_of_same_class
    {N p : ℕ} (_hp : 0 < p) (i j : Fin N) (hsame : i.1 % p = j.1 % p) :
    indexDiff i j = p * quotientDiff p i j := by
  simp only [indexDiff, quotientDiff]
  have hi : (i.1 : ℤ) = (i.1 % p : ℕ) + (p : ℤ) * (i.1 / p : ℕ) := by
    exact_mod_cast (Nat.mod_add_div i.1 p).symm
  have hj : (j.1 : ℤ) = (j.1 % p : ℕ) + (p : ℤ) * (j.1 / p : ℕ) := by
    exact_mod_cast (Nat.mod_add_div j.1 p).symm
  rw [hi, hj, hsame]
  ring_nf
  rw [← mul_sub, Int.natAbs_mul, Int.natAbs_natCast]

lemma gcd_indexDiff_classDigit
    {N p a : ℕ} (hp : 0 < p) (i j : Fin N) :
    Nat.gcd (p ^ a)
        (indexDiff (classDigit p a hp i) (classDigit p a hp j)) =
      Nat.gcd (p ^ a) (quotientDiff p i j) := by
  apply gcd_natAbs_sub_eq_of_intModEq
  exact (natMod_intModEq (p ^ a) (i.1 / p)).sub
    (natMod_intModEq (p ^ a) (j.1 / p))

lemma survivingModulus_classDigit
    {N p a : ℕ} (hp : 0 < p) (i j : Fin N) :
    survivingModulus (p ^ a)
        (indexDiff (classDigit p a hp i) (classDigit p a hp j)) =
      p ^ a / Nat.gcd (p ^ a) (quotientDiff p i j) := by
  simp only [survivingModulus, gcd_indexDiff_classDigit hp i j]

private lemma gcd_mul_complement_dvd
    {m u q : ℕ} (hcop : Nat.Coprime m u) :
    Nat.gcd (m * u) q ∣ u * Nat.gcd m q := by
  let x := Nat.gcd (m * u) q
  have hfactor : Nat.gcd x m * Nat.gcd x u = x := by
    apply (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).2
    exact Nat.gcd_dvd_left _ _
  have hxm : Nat.gcd x m ∣ Nat.gcd m q := by
    apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_right _ _
    · exact (Nat.gcd_dvd_left x m).trans (Nat.gcd_dvd_right (m * u) q)
  have hxu : Nat.gcd x u ∣ u := Nat.gcd_dvd_right _ _
  change x ∣ u * Nat.gcd m q
  rw [← hfactor]
  simpa [Nat.mul_comm] using Nat.mul_dvd_mul hxm hxu

/-- In the branch where the full new `p`-power does not divide the input
difference, the surviving modulus of the quotient digit divides the full
surviving modulus.  This is the exact divisibility needed to apply goodness
of the auxiliary permutation on `Fin (p^a)`. -/
lemma survivingModulus_classDigit_dvd
    {N p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (hN : N = p ^ (a + 1) * u) (i j : Fin N)
    (hsame : i.1 % p = j.1 % p) :
    survivingModulus (p ^ a)
        (indexDiff (classDigit p a hp.pos i) (classDigit p a hp.pos j)) ∣
      survivingModulus N (indexDiff i j) := by
  let m := p ^ a
  let q := quotientDiff p i j
  let g₀ := Nat.gcd m q
  let gx := Nat.gcd (m * u) q
  have hcopMU : Nat.Coprime m u := hcop.pow_left a
  have hx : gx ∣ u * g₀ := by
    exact gcd_mul_complement_dvd hcopMU
  have hg₀m : g₀ ∣ m := Nat.gcd_dvd_left _ _
  have hxmu : gx ∣ m * u := by
    exact Nat.gcd_dvd_left _ _
  have hdiv : m / g₀ ∣ (m * u) / gx := by
    rw [Nat.dvd_div_iff_mul_dvd hxmu]
    have hmul := Nat.mul_dvd_mul_left (m / g₀) hx
    have hprod : (m / g₀) * (u * g₀) = m * u := by
      calc
        (m / g₀) * (u * g₀) = u * (g₀ * (m / g₀)) := by ac_rfl
        _ = u * m := by rw [Nat.mul_div_cancel' hg₀m]
        _ = m * u := Nat.mul_comm _ _
    rw [hprod] at hmul
    simpa [Nat.mul_comm] using hmul
  rw [survivingModulus_classDigit hp.pos i j]
  have hidx := indexDiff_eq_mul_quotientDiff_of_same_class hp.pos i j hsame
  simp only [survivingModulus, hN, hidx, pow_succ]
  simpa [m, q, g₀, gx, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
    Nat.gcd_mul_left, Nat.mul_div_mul_left _ _ hp.pos] using hdiv

/-- If the full new `p`-power has already been cancelled by the input
difference, only the complementary factor `u` can remain in the required
surviving modulus. -/
lemma survivingModulus_dvd_complement_of_primePower_dvd
    {N p u a delta : ℕ} (hp : p.Prime)
    (hN : N = p ^ (a + 1) * u) (hpow : p ^ (a + 1) ∣ delta) :
    survivingModulus N delta ∣ u := by
  have hpN : p ^ (a + 1) ∣ N := by rw [hN]; exact dvd_mul_right _ _
  have hpg : p ^ (a + 1) ∣ Nat.gcd N delta := Nat.dvd_gcd hpN hpow
  have hgN : Nat.gcd N delta ∣ N := Nat.gcd_dvd_left _ _
  have hdiv : N / Nat.gcd N delta ∣ N / p ^ (a + 1) :=
    Nat.div_dvd_div_left hgN hpg
  have hquot : N / p ^ (a + 1) = u := by
    rw [hN]
    simpa [Nat.mul_comm] using Nat.mul_div_left u (pow_pos hp.pos (a + 1))
  rw [hquot] at hdiv
  exact hdiv

private lemma int_dvd_sub_iff_natModEq (m x y : ℕ) :
    (m : ℤ) ∣ (x : ℤ) - (y : ℤ) ↔ x ≡ y [MOD m] := by
  rw [Nat.modEq_iff_dvd]
  constructor <;> intro h <;> simpa only [neg_sub] using dvd_neg.mpr h

lemma classDigit_ne_of_not_primePower_dvd
    {N p a : ℕ} (hp : p.Prime) (i j : Fin N)
    (hsame : i.1 % p = j.1 % p)
    (hnot : ¬p ^ (a + 1) ∣ indexDiff i j) :
    classDigit p a hp.pos i ≠ classDigit p a hp.pos j := by
  intro hdigit
  have hg : Nat.gcd (p ^ a) (quotientDiff p i j) = p ^ a := by
    rw [← gcd_indexDiff_classDigit hp.pos i j, hdigit]
    simp [indexDiff]
  have hq : p ^ a ∣ quotientDiff p i j := by
    rw [← hg]
    exact Nat.gcd_dvd_right _ _
  apply hnot
  rw [indexDiff_eq_mul_quotientDiff_of_same_class hp.pos i j hsame, pow_succ]
  simpa [Nat.mul_comm] using Nat.mul_dvd_mul_left p hq

/-- The `p`-primary branch of partial goodness for a map on one class
modulo `p`.  Its output modulo `p^(a+1)` is a fixed translate of a good
permutation applied to `classDigit`.  Unless the input difference has already
cancelled the whole `p^(a+1)`, that coordinate alone rules out a bad output
congruence modulo the full surviving modulus. -/
lemma not_dvd_output_sub_of_primePower_formula
    {N p u a target correction : ℕ}
    (hp : p.Prime) (hcop : Nat.Coprime p u)
    (hN : N = p ^ (a + 1) * u)
    (rho : Equiv.Perm (Fin (p ^ a))) (hrho : GoodPerm (p ^ a) rho)
    (f : Fin N → Fin N)
    (hout : ∀ i : Fin N, i.1 % p = target →
      (f i).1 ≡ (rho (classDigit p a hp.pos i)).1 + correction
        [MOD p ^ (a + 1)])
    (i j : Fin N) (hi : i.1 % p = target) (hj : j.1 % p = target)
    (hnot : ¬p ^ (a + 1) ∣ indexDiff i j) :
    ¬(survivingModulus N (indexDiff i j) : ℤ) ∣
      (((f i).1 : ℕ) : ℤ) - (((f j).1 : ℕ) : ℤ) := by
  have hsame : i.1 % p = j.1 % p := hi.trans hj.symm
  let di := classDigit p a hp.pos i
  let dj := classDigit p a hp.pos j
  have hdigit : di ≠ dj :=
    classDigit_ne_of_not_primePower_dvd hp i j hsame hnot
  let M₀ := survivingModulus (p ^ a) (indexDiff di dj)
  let M := survivingModulus N (indexDiff i j)
  have hM₀M : M₀ ∣ M := by
    exact survivingModulus_classDigit_dvd hp hcop hN i j hsame
  have hM₀pow : M₀ ∣ p ^ (a + 1) := by
    exact (survivingModulus_dvd _ _).trans (by
      rw [pow_succ]
      exact dvd_mul_right (p ^ a) p)
  intro hbad
  have hbadM₀ : (M₀ : ℤ) ∣
      (((f i).1 : ℕ) : ℤ) - (((f j).1 : ℕ) : ℤ) := by
    exact (Int.natCast_dvd_natCast.mpr hM₀M).trans hbad
  have hfi := (hout i hi).of_dvd hM₀pow
  have hfj := (hout j hj).of_dvd hM₀pow
  have hfij : (f i).1 ≡ (f j).1 [MOD M₀] :=
    (int_dvd_sub_iff_natModEq M₀ _ _).mp hbadM₀
  have hrmod : (rho di).1 ≡ (rho dj).1 [MOD M₀] := by
    exact Nat.ModEq.add_right_cancel'
      correction (hfi.symm.trans (hfij.trans hfj))
  exact hrho di dj hdigit ((int_dvd_sub_iff_natModEq M₀ _ _).mpr hrmod)

lemma survivingModulus_indexDiff_dvd_complement
    {N p u a : ℕ} (hp : p.Prime)
    (hN : N = p ^ (a + 1) * u) (i j : Fin N)
    (hpow : p ^ (a + 1) ∣ indexDiff i j) :
    survivingModulus N (indexDiff i j) ∣ u :=
  survivingModulus_dvd_complement_of_primePower_dvd hp hN hpow

end

end Selector.PrimeClassGood

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorGood.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

namespace Selector.Final

open Erdos215.Selector
open Erdos215.Selector.Modular

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

private lemma integer_line_factorization
    (d A B K M L R m : ℤ)
    (hline : B = L * A - m * d)
    (hroot : d * R = 1 + L ^ 2) :
    A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) =
      d * (A * (R * A + 2 * (K + L * M - L * m)) +
        d * (m ^ 2 - 2 * m * M)) := by
  rw [hline]
  linear_combination -A ^ 2 * hroot

private lemma surviving_times_difference_dvd
    (d : ℕ) (A : ℤ) :
    (d : ℤ) ∣ A * (survivingModulus d A.natAbs : ℤ) := by
  let g := Nat.gcd d A.natAbs
  let q := d / g
  have hg : g ∣ d := Nat.gcd_dvd_left _ _
  have hga : g ∣ A.natAbs := Nat.gcd_dvd_right _ _
  have hqg : q * g = d := Nat.div_mul_cancel hg
  rcases hga with ⟨a, ha⟩
  have hqa : q * A.natAbs = d * a := by
    calc
      q * A.natAbs = q * (g * a) := by rw [ha]
      _ = (q * g) * a := by ring
      _ = d * a := by rw [hqg]
  change (d : ℤ) ∣ A * (q : ℤ)
  refine ⟨Int.sign A * (a : ℤ), ?_⟩
  have hqa' : (q : ℤ) * (A.natAbs : ℤ) = (d : ℤ) * a := by
    exact_mod_cast hqa
  have hsign : Int.sign A * (A.natAbs : ℤ) = A := Int.sign_mul_natAbs A
  calc
    A * (q : ℤ) = (Int.sign A * (A.natAbs : ℤ)) * q := by rw [hsign]
    _ = Int.sign A * ((q : ℤ) * A.natAbs) := by ring
    _ = Int.sign A * ((d : ℤ) * a) := by rw [hqa']
    _ = (d : ℤ) * (Int.sign A * a) := by ring

private lemma square_dvd_of_line_divisibility
    (d q A B K M L R P C m : ℤ)
    (hqd : q ∣ d)
    (hAq : d ∣ A * q)
    (hC : q ∣ C)
    (hout : d ∣ C - (K + L * M - L * m + P * A))
    (hphase : d ∣ 2 * P - R)
    (hline : B = L * A - m * d)
    (hroot : d * R = 1 + L ^ 2) :
    d ^ 2 ∣ A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) := by
  let X := K + L * M - L * m
  let Y := R * A + 2 * X
  have hX : q ∣ X + P * A := by
    have hsub : q ∣ C - (X + P * A) := dvd_trans hqd hout
    have hx' := dvd_sub hC hsub
    simpa only [sub_sub_cancel] using hx'
  have hPA : q ∣ A * (2 * P - R) := dvd_mul_of_dvd_right (dvd_trans hqd hphase) A
  have hY : q ∣ Y := by
    have htwo : q ∣ 2 * (X + P * A) := dvd_mul_of_dvd_right hX 2
    have : Y = 2 * (X + P * A) - A * (2 * P - R) := by
      dsimp [Y, X]
      ring
    rw [this]
    exact dvd_sub htwo hPA
  have hAY : d ∣ A * Y := by
    rcases hAq with ⟨z, hz⟩
    rcases hY with ⟨y, hy⟩
    refine ⟨z * y, ?_⟩
    rw [hy, ← mul_assoc, hz]
    ring
  rw [integer_line_factorization d A B K M L R m hline hroot]
  rcases hAY with ⟨z, hz⟩
  refine ⟨z + (m ^ 2 - 2 * m * M), ?_⟩
  dsimp [Y, X] at hz
  rw [hz]
  ring

/-- Formula (4.4a): a separated selector induces good line maps at every
root of `-1` when two is invertible modulo the denominator. -/
theorem inducedFamily_good {d : ℕ} (hd : d ≠ 0) (hodd : Nat.Coprime 2 d)
    (s : LiftData d) (hs : s.Separated) :
    FamilyGood (inducedFamily hd s) := by
  let _ : NeZero d := ⟨hd⟩
  intro lam jtilde i₁ i₂ hi hbad
  let j₁ := lineResidue hd lam jtilde i₁
  let j₂ := lineResidue hd lam jtilde i₂
  let A : ℤ := (i₁ : ℕ) - (i₂ : ℕ)
  let B : ℤ := (j₁ : ℕ) - (j₂ : ℕ)
  let K : ℤ := s.k i₁ j₁ - s.k i₂ j₂
  let M : ℤ := s.l i₁ j₁ - s.l i₂ j₂
  let L : ℤ := rootVal hd lam
  let R : ℤ := rootQuotient lam
  let P : ℤ := (rootPhase lam).val
  let C : ℤ :=
    ((inducedFamily hd s lam jtilde i₁ : Fin d) : ℕ) -
      ((inducedFamily hd s lam jtilde i₂ : Fin d) : ℕ)
  let m : ℤ := lineCarry hd lam jtilde i₁ - lineCarry hd lam jtilde i₂
  let q : ℕ := survivingModulus d (indexDiff i₁ i₂)
  have hqdNat : q ∣ d := survivingModulus_dvd _ _
  have hqd : (q : ℤ) ∣ d := by exact_mod_cast hqdNat
  have hAabs : A.natAbs = indexDiff i₁ i₂ := by rfl
  have hAq : (d : ℤ) ∣ A * (q : ℤ) := by
    simpa [q, hAabs] using surviving_times_difference_dvd d A
  have hC : (q : ℤ) ∣ C := by
    exact hbad
  have hline : B = L * A - m * d := by
    have h₁ := lineResidue_int_equation hd lam jtilde i₁
    have h₂ := lineResidue_int_equation hd lam jtilde i₂
    dsimp [A, B, L, m, j₁, j₂]
    linear_combination h₁ - h₂
  have hroot : (d : ℤ) * R = 1 + L ^ 2 := by
    dsimp [R, L]
    exact_mod_cast mul_rootQuotient hd lam
  have hPcast : ((P : ℤ) : ZMod d) = rootPhase lam := by
    simpa [P] using (ZMod.natCast_zmod_val (rootPhase lam))
  have hphase : (d : ℤ) ∣ 2 * P - R := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub R (2 * P) d).mp
    push_cast
    rw [hPcast]
    simpa [R] using (two_mul_rootPhase hodd lam).symm
  have hvalue : ((C : ℤ) : ZMod d) =
      ((K + L * M - L * m + P * A : ℤ) : ZMod d) := by
    dsimp [C, K, L, M, m, A]
    push_cast
    rw [inducedFamily_formula hd s lam jtilde i₁,
      inducedFamily_formula hd s lam jtilde i₂]
    simp only [lineValue]
    rw [hPcast, rootVal_cast hd lam]
    ring
  have hout : (d : ℤ) ∣ C - (K + L * M - L * m + P * A) := by
    have hout' := (ZMod.intCast_eq_intCast_iff_dvd_sub C
      (K + L * M - L * m + P * A) d).mp hvalue
    simpa only [neg_sub] using dvd_neg.mpr hout'
  have hconf : (d : ℤ) ^ 2 ∣
      conflictNumerator d i₁ j₁ i₂ j₂
        (s.k i₁ j₁) (s.l i₁ j₁) (s.k i₂ j₂) (s.l i₂ j₂) := by
    apply square_dvd_of_line_divisibility (d : ℤ) q A B K M L R P C m
      hqd hAq hC hout hphase hline hroot
  apply hs i₁ j₁ i₂ j₂
  · intro hp
    exact hi (congrArg Prod.fst hp)
  · simpa [conflictNumerator, A, B, K, M] using hconf

end
end Selector.Final

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorOldLine.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The old residue class in the nontrivial prime-extension step

This file isolates formula (4.9) of Jackson--Mauldin.  If the denominator is
enlarged from `D` to `p * D`, both the argument and the line label lie in the
old residue class `0 mod p`, and the lift data are copied from denominator
`D`, then the enlarged line map reduces modulo `D` to the old line map.
Consequently the enlarged map is partially good on that residue class.
-/

namespace Selector.PrimeExtension.OldLine

open Erdos215.Selector
open Erdos215.Selector.Modular
open Erdos215.Selector.Final
open Erdos215.Selector.PartialGood
open Erdos215.Selector.PrimeExtension

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Reduction of a root at denominator `p * D` to denominator `D`. -/
def reducedRoot (p D : ℕ) (lam : Root (p * D)) : Root D :=
  ⟨ZMod.castHom (dvd_mul_left D p) (ZMod D) lam.1, by
    simpa using congrArg (ZMod.castHom (dvd_mul_left D p) (ZMod D)) lam.property⟩

@[simp] lemma reducedRoot_coe (p D : ℕ) (lam : Root (p * D)) :
    (reducedRoot p D lam : ZMod D) =
      ZMod.castHom (dvd_mul_left D p) (ZMod D) lam.1 := rfl

/-- The quotient of a line label in the old residue class. -/
def reducedLabel (p : ℕ) {D : ℕ} (J : Fin (p * D)) : Fin D :=
  quotientIndex p J

lemma val_eq_p_mul_reducedLabel {p D : ℕ} (hp : 0 < p)
    (J : Fin (p * D)) (hJ : J.1 % p = 0) :
    J.1 = p * (reducedLabel p J).1 := by
  have h := val_eq_mul_quotient_add_remainder p hp J
  simpa only [reducedLabel, remainderIndex, hJ, add_zero] using h

lemma rootVal_reducedRoot {p D : ℕ} (hp : 0 < p) (hD : D ≠ 0)
    (lam : Root (p * D)) :
    rootVal hD (reducedRoot p D lam) = ZMod.val lam.1 % D := by
  let _ : NeZero (p * D) := ⟨Nat.mul_ne_zero hp.ne' hD⟩
  let _ : NeZero D := ⟨hD⟩
  have hcast :
      ((rootVal hD (reducedRoot p D lam) : ℕ) : ZMod D) =
        ((ZMod.val lam.1 : ℕ) : ZMod D) := by
    rw [rootVal_cast, reducedRoot_coe]
    rw [← ZMod.natCast_zmod_val lam.1]
    simp
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast, ZMod.val_natCast] at hv
  have hlt : rootVal hD (reducedRoot p D lam) < D := by
    change (reducedRoot p D lam : ZMod D).val < D
    exact ZMod.val_lt (reducedRoot p D lam : ZMod D)
  calc
    rootVal hD (reducedRoot p D lam) =
        rootVal hD (reducedRoot p D lam) % D := (Nat.mod_eq_of_lt hlt).symm
    _ = ZMod.val lam.1 % D := hv

lemma val_eq_rootVal_add_D_mul_div {p D : ℕ} (hp : 0 < p) (hD : D ≠ 0)
    (lam : Root (p * D)) :
    ZMod.val lam.1 = rootVal hD (reducedRoot p D lam) +
      D * (ZMod.val lam.1 / D) := by
  rw [rootVal_reducedRoot hp hD]
  exact (Nat.mod_add_div (ZMod.val lam.1) D).symm

/-- The exact quotient identity behind the phase correction in (4.9). -/
lemma rootQuotient_reduction {p D : ℕ} (hp : 0 < p) (hD : D ≠ 0)
    (lam : Root (p * D)) :
    p * rootQuotient lam =
      rootQuotient (reducedRoot p D lam) +
        2 * rootVal hD (reducedRoot p D lam) * (ZMod.val lam.1 / D) +
        D * (ZMod.val lam.1 / D) ^ 2 := by
  have hN : p * D ≠ 0 := Nat.mul_ne_zero hp.ne' hD
  have hn := mul_rootQuotient hN lam
  have ho := mul_rootQuotient hD (reducedRoot p D lam)
  change D * rootQuotient (reducedRoot p D lam) =
    1 + rootVal hD (reducedRoot p D lam) ^ 2 at ho
  have hval := val_eq_rootVal_add_D_mul_div hp hD lam
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hD)
  calc
    D * (p * rootQuotient lam) = (p * D) * rootQuotient lam := by ring
    _ = 1 + ZMod.val lam.1 ^ 2 := hn
    _ = 1 + (rootVal hD (reducedRoot p D lam) +
        D * (ZMod.val lam.1 / D)) ^ 2 := by
      conv_lhs => rw [hval]
    _ = D * (rootQuotient (reducedRoot p D lam) +
        2 * rootVal hD (reducedRoot p D lam) * (ZMod.val lam.1 / D) +
        D * (ZMod.val lam.1 / D) ^ 2) := by
      calc
        1 + (rootVal hD (reducedRoot p D lam) +
            D * (ZMod.val lam.1 / D)) ^ 2 =
            (1 + rootVal hD (reducedRoot p D lam) ^ 2) +
              D * (2 * rootVal hD (reducedRoot p D lam) *
                (ZMod.val lam.1 / D) + D * (ZMod.val lam.1 / D) ^ 2) := by ring
        _ = D * rootQuotient (reducedRoot p D lam) +
              D * (2 * rootVal hD (reducedRoot p D lam) *
                (ZMod.val lam.1 / D) + D * (ZMod.val lam.1 / D) ^ 2) := by
              rw [← ho]
        _ = _ := by ring

lemma two_coprime_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.Coprime 2 p := by
  apply Nat.Coprime.symm
  rw [hp.coprime_iff_not_dvd]
  intro hpd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpd)

/-- After reduction to the old denominator, the enlarged phase differs from
the old phase by the root carry.  This is the phase part of formula (4.9). -/
lemma rootPhase_reduction {p D : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : D ≠ 0) (h2D : Nat.Coprime 2 D) (lam : Root (p * D)) :
    (p : ZMod D) *
        ZMod.castHom (dvd_mul_left D p) (ZMod D) (rootPhase lam) =
      rootPhase (reducedRoot p D lam) +
        (rootVal hD (reducedRoot p D lam) : ZMod D) *
          (ZMod.val lam.1 / D : ℕ) := by
  have h2p : Nat.Coprime 2 p := two_coprime_prime hp hp2
  have h2N : Nat.Coprime 2 (p * D) := h2p.mul_right h2D
  let r : ZMod (p * D) →+* ZMod D :=
    ZMod.castHom (dvd_mul_left D p) (ZMod D)
  have hn := congrArg r (two_mul_rootPhase h2N lam)
  have hn' :
      (2 : ZMod D) * r (rootPhase lam) = (rootQuotient lam : ZMod D) := by
    simpa only [map_mul, map_ofNat, map_natCast] using hn
  have ho := two_mul_rootPhase h2D (reducedRoot p D lam)
  have hq := rootQuotient_reduction hp.pos hD lam
  have hq' :
      (p : ZMod D) * (rootQuotient lam : ZMod D) =
        (rootQuotient (reducedRoot p D lam) : ZMod D) +
          (2 : ZMod D) * rootVal hD (reducedRoot p D lam) *
            (ZMod.val lam.1 / D : ℕ) := by
    have hqCast := congrArg (fun n : ℕ => (n : ZMod D)) hq
    push_cast at hqCast
    simpa using hqCast
  have htwo : IsUnit (2 : ZMod D) := by
    change IsUnit (((2 : ℕ) : ZMod D))
    rw [ZMod.isUnit_iff_coprime]
    exact h2D
  apply htwo.mul_left_cancel
  change (2 : ZMod D) * ((p : ZMod D) * r (rootPhase lam)) = _
  calc
    (2 : ZMod D) * ((p : ZMod D) * r (rootPhase lam)) =
        (p : ZMod D) * ((2 : ZMod D) * r (rootPhase lam)) := by ring
    _ = (p : ZMod D) * (rootQuotient lam : ZMod D) := by rw [hn']
    _ = (rootQuotient (reducedRoot p D lam) : ZMod D) +
          (2 : ZMod D) * rootVal hD (reducedRoot p D lam) *
            (ZMod.val lam.1 / D : ℕ) := hq'
    _ = (2 : ZMod D) *
        (rootPhase (reducedRoot p D lam) +
          (rootVal hD (reducedRoot p D lam) : ZMod D) *
            (ZMod.val lam.1 / D : ℕ)) := by rw [← ho]; ring

/-- On an old line, the canonical line residue is itself an old index. -/
lemma lineResidue_oldIndex {p D : ℕ} (hp : 0 < p) (hD : D ≠ 0)
    (lam : Root (p * D)) (J : Fin (p * D)) (hJ : J.1 % p = 0)
    (i : Fin D) :
    lineResidue (Nat.mul_ne_zero hp.ne' hD) lam J (oldIndex p hp i) =
      oldIndex p hp
        (lineResidue hD (reducedRoot p D lam) (reducedLabel p J) i) := by
  apply Fin.ext
  simp only [lineResidue, oldIndex]
  rw [val_eq_p_mul_reducedLabel hp J hJ]
  have hfactor :
      p * (reducedLabel p J).1 + rootVal (Nat.mul_ne_zero hp.ne' hD) lam *
          (p * i.1) =
        p * ((reducedLabel p J).1 +
          rootVal (Nat.mul_ne_zero hp.ne' hD) lam * i.1) := by ring
  rw [hfactor, Nat.mul_mod_mul_left]
  congr 1
  rw [show rootVal (Nat.mul_ne_zero hp.ne' hD) lam = ZMod.val lam.1 by rfl,
    rootVal_reducedRoot hp hD]
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

/-- The enlarged carry is the old carry plus the root quotient digit times
the old argument. -/
lemma lineCarry_oldIndex {p D : ℕ} (hp : 0 < p) (hD : D ≠ 0)
    (lam : Root (p * D)) (J : Fin (p * D)) (hJ : J.1 % p = 0)
    (i : Fin D) :
    lineCarry (Nat.mul_ne_zero hp.ne' hD) lam J (oldIndex p hp i) =
      lineCarry hD (reducedRoot p D lam) (reducedLabel p J) i +
        (ZMod.val lam.1 / D) * i.1 := by
  simp only [lineCarry, oldIndex]
  rw [val_eq_p_mul_reducedLabel hp J hJ]
  have hfactor :
      p * (reducedLabel p J).1 + rootVal (Nat.mul_ne_zero hp.ne' hD) lam *
          (p * i.1) =
        p * ((reducedLabel p J).1 +
          rootVal (Nat.mul_ne_zero hp.ne' hD) lam * i.1) := by ring
  rw [hfactor, Nat.mul_div_mul_left _ _ hp]
  rw [show rootVal (Nat.mul_ne_zero hp.ne' hD) lam = ZMod.val lam.1 by rfl]
  conv_lhs => rw [val_eq_rootVal_add_D_mul_div hp hD lam]
  rw [show (reducedLabel p J).1 +
      (rootVal hD (reducedRoot p D lam) + D * (ZMod.val lam.1 / D)) * i.1 =
        ((reducedLabel p J).1 +
          rootVal hD (reducedRoot p D lam) * i.1) +
            D * ((ZMod.val lam.1 / D) * i.1) by ring]
  rw [Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero hD)]

/-- Formula (4.9): the copied enlarged line value reduces literally to the
old line value on the old argument and old line-label classes. -/
lemma lineValue_oldIndex {p D : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : D ≠ 0) (h2D : Nat.Coprime 2 D) (s : LiftData D)
    (lam : Root (p * D)) (J : Fin (p * D)) (hJ : J.1 % p = 0)
    (i : Fin D) :
    ZMod.castHom (dvd_mul_left D p) (ZMod D)
        (lineValue (Nat.mul_ne_zero hp.ne_zero hD) (primeCopyLift p s) lam J
          (oldIndex p hp.pos i)) =
      lineValue hD s (reducedRoot p D lam) (reducedLabel p J) i := by
  let r : ZMod (p * D) →+* ZMod D :=
    ZMod.castHom (dvd_mul_left D p) (ZMod D)
  have hj := lineResidue_oldIndex hp.pos hD lam J hJ i
  have hm := lineCarry_oldIndex hp.pos hD lam J hJ i
  have hphase := rootPhase_reduction hp hp2 hD h2D lam
  simp only [lineValue, map_add, map_sub, map_mul, map_intCast, map_natCast]
  rw [hj, hm]
  simp only [primeCopyLift, quotientIndex_oldIndex]
  change
    (s.k i (lineResidue hD (reducedRoot p D lam) (reducedLabel p J) i) : ZMod D) +
        (reducedRoot p D lam : ZMod D) *
          (s.l i (lineResidue hD (reducedRoot p D lam) (reducedLabel p J) i) : ZMod D) -
        (reducedRoot p D lam : ZMod D) *
          (((lineCarry hD (reducedRoot p D lam) (reducedLabel p J) i : ℕ) +
            (ZMod.val lam.1 / D) * i.1 : ℕ) : ZMod D) +
        ZMod.castHom (dvd_mul_left D p) (ZMod D) (rootPhase lam) *
          ((p * i.1 : ℕ) : ZMod D) = _
  rw [show ((p * i.1 : ℕ) : ZMod D) = (p : ZMod D) * (i.1 : ZMod D) by
    push_cast; rfl]
  rw [show (((lineCarry hD (reducedRoot p D lam) (reducedLabel p J) i : ℕ) +
      (ZMod.val lam.1 / D) * i.1 : ℕ) : ZMod D) =
      (lineCarry hD (reducedRoot p D lam) (reducedLabel p J) i : ZMod D) +
        (ZMod.val lam.1 / D : ℕ) * (i.1 : ZMod D) by push_cast; rfl]
  rw [← mul_assoc, mul_comm
    (ZMod.castHom (dvd_mul_left D p) (ZMod D) (rootPhase lam)) (p : ZMod D),
    hphase]
  rw [rootVal_cast hD (reducedRoot p D lam)]
  ring

/-- Nat-valued form of (4.9), precisely matching the reduction hypothesis
of `partialGoodOnOldClass_of_reduces_good`. -/
lemma inducedFamily_oldIndex_modEq {p D : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : D ≠ 0) (h2D : Nat.Coprime 2 D) (s : LiftData D)
    (lam : Root (p * D)) (J : Fin (p * D)) (hJ : J.1 % p = 0)
    (i : Fin D) :
    ((inducedFamily (Nat.mul_ne_zero hp.ne_zero hD) (primeCopyLift p s) lam J
        (oldIndex p hp.pos i) : Fin (p * D)) : ℕ) ≡
      ((inducedFamily hD s (reducedRoot p D lam) (reducedLabel p J) i : Fin D) : ℕ)
        [MOD D] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ D).mp
  let r : ZMod (p * D) →+* ZMod D :=
    ZMod.castHom (dvd_mul_left D p) (ZMod D)
  have hn := congrArg r
    (inducedFamily_formula (Nat.mul_ne_zero hp.ne_zero hD) (primeCopyLift p s)
      lam J (oldIndex p hp.pos i))
  have ho := inducedFamily_formula hD s (reducedRoot p D lam) (reducedLabel p J) i
  calc
    (((inducedFamily (Nat.mul_ne_zero hp.ne_zero hD) (primeCopyLift p s) lam J
        (oldIndex p hp.pos i) : Fin (p * D)) : ℕ) : ZMod D) =
      r (lineValue (Nat.mul_ne_zero hp.ne_zero hD) (primeCopyLift p s) lam J
        (oldIndex p hp.pos i)) := by
          simpa only [map_natCast] using hn
    _ = lineValue hD s (reducedRoot p D lam) (reducedLabel p J) i :=
      lineValue_oldIndex hp hp2 hD h2D s lam J hJ i
    _ = (((inducedFamily hD s (reducedRoot p D lam) (reducedLabel p J) i :
        Fin D) : ℕ) : ZMod D) := ho.symm

/-- The copied enlarged line map is partially good on the old residue class.
This is the old-line case required before applying Lemma 4.8. -/
theorem inducedFamily_primeCopy_partialGood_oldLine
    {p D : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : D ≠ 0) (h2D : Nat.Coprime 2 D) (s : LiftData D)
    (hs : s.Separated) (lam : Root (p * D)) (J : Fin (p * D))
    (hJ : J.1 % p = 0) :
    PartialGoodOnClass (p * D) p 0
      (inducedFamily (Nat.mul_ne_zero hp.ne_zero hD) (primeCopyLift p s) lam J) := by
  let F : Fin D → Fin D :=
    inducedFamily hD s (reducedRoot p D lam) (reducedLabel p J)
  have hF : GoodMap D F :=
    inducedFamily_good hD h2D s hs (reducedRoot p D lam) (reducedLabel p J)
  apply partialGoodOnOldClass_of_reduces_good p hp.pos F hF
  intro i
  exact inducedFamily_oldIndex_modEq hp hp2 hD h2D s lam J hJ i

end

end Selector.PrimeExtension.OldLine

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorPrimePowerGood.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Good permutations at prime-power moduli

This file packages the iteration of Jackson--Mauldin Lemma 4.8 which is
needed when the nontrivial part of a denominator is a prime power.  At the
successor step the already constructed good permutation on `Fin (p ^ a)` is
embedded as the partial map on the source class `0 mod p`; Lemma 4.8 then
extends it to a good permutation on all of `Fin (p ^ (a + 1))`.
-/

namespace Selector.PrimePowerGood

open Erdos215.Selector
open Erdos215.Selector.PartialGood
open Erdos215.Selector.PrimeExtension

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Regard the value of a permutation of `Fin d` as an element of
`Fin (p * d)`.  Only its values on indices `oldIndex p hp i` matter in the
partial-goodness argument, but defining it on every index makes it directly
usable as the partial map in Lemma 4.8. -/
private def embeddedOldPerm (p : ℕ) (hp : 0 < p) {d : ℕ}
    (sigma : Equiv.Perm (Fin d)) : Fin (p * d) → Fin (p * d) :=
  fun x => Fin.castLE (Nat.le_mul_of_pos_left d hp) (sigma (quotientIndex p x))

private lemma embeddedOldPerm_oldIndex_modEq (p : ℕ) (hp : 0 < p) {d : ℕ}
    (sigma : Equiv.Perm (Fin d)) (i : Fin d) :
    (embeddedOldPerm p hp sigma (oldIndex p hp i)).1 ≡ (sigma i).1 [MOD d] := by
  simp only [embeddedOldPerm, quotientIndex_oldIndex, Fin.coe_castLE]
  exact Nat.ModEq.refl _

/-- Every prime-power modulus admits a permutation satisfying the exact
Jackson--Mauldin goodness condition (4.3). -/
theorem exists_goodPerm_primePower (p a : ℕ) (hp : p.Prime) :
    ∃ sigma : Equiv.Perm (Fin (p ^ a)), GoodPerm (p ^ a) sigma := by
  induction a with
  | zero =>
      refine ⟨Equiv.refl (Fin 1), ?_⟩
      intro i j hij
      exfalso
      apply hij
      apply Fin.ext
      have hi : i.1 < 1 := by simpa only [pow_zero] using i.2
      have hj : j.1 < 1 := by simpa only [pow_zero] using j.2
      omega
  | succ a ih =>
      rw [pow_succ, Nat.mul_comm (p ^ a) p]
      rcases ih with ⟨sigma, hsigma⟩
      let d := p ^ a
      let N := p * d
      let pi : Fin N → Fin N := embeddedOldPerm p hp.pos sigma
      have hsigmaMap : GoodMap d (fun i => sigma i) := by
        simpa only [GoodMap, GoodPerm] using hsigma
      have hpartial : PartialGoodOnClass N p 0 pi := by
        refine partialGoodOnOldClass_of_reduces_good p hp.pos
          (fun i => sigma i) hsigmaMap pi ?_
        intro i
        exact embeddedOldPerm_oldIndex_modEq p hp.pos sigma i
      let target : Fin p := ⟨0, hp.pos⟩
      have hcop : Nat.Coprime p 1 := Nat.coprime_one_right p
      have hpd : N = p * d := rfl
      have hn : 0 < a + 1 := Nat.succ_pos a
      have hN : N = 1 * p ^ (a + 1) := by
        simp only [N, d, one_mul, pow_succ]
        ac_rfl
      obtain ⟨tau, htau, _⟩ :=
        exists_goodPerm_to_target hp hn hcop hpd hN target pi hpartial
      change ∃ tau : Equiv.Perm (Fin N), GoodPerm N tau
      exact ⟨tau, htau⟩

end

end Selector.PrimePowerGood

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorPureGoodness.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Goodness of the pure nontrivial-prime extension

This file verifies condition (4.3) for every line map in
`PurePrimeExtension.extendedFamily`.  Old line labels use (4.9) and the
partial-good extension lemma.  For a new line label, the distinguished
values are treated in the two cases determined by whether the full new
`p`-power divides the input difference: the new primary coordinate handles
the first case, and the complementary coordinate reduces the second case to
one old-line extension.
-/

namespace Selector.PurePrimeExtension

open Erdos215.Selector
open Erdos215.Selector.Modular
open Erdos215.Selector.Final
open Erdos215.Selector.PartialGood
open Erdos215.Selector.PrimeExtension
open Erdos215.Selector.PrimeExtension.OldLine
open Erdos215.Selector.PrimeClassGood

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Formula (4.12) is good whenever its label lies in the old residue
class. -/
lemma oldLineExtension_good
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hodd : Nat.Coprime 2 (oldDenom p u a))
    (s : LiftData (oldDenom p u a)) (hs : s.Separated)
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a))
    (hj : jtilde.1 % p = 0) :
    GoodMap (newDenom p u a)
      (oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop)
        s lam jtilde) := by
  let D := oldDenom p u a
  let N := newDenom p u a
  let q : Fin N → ℕ := oldShiftGuide p u
  let pi : Fin N → Fin N :=
    inducedFamily (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
      (copiedLift p u a s) lam jtilde
  have hpartial : PartialGoodOnClass N p 0 pi := by
    simpa only [N, D, pi, copiedLift, newDenom] using
      inducedFamily_primeCopy_partialGood_oldLine hp hp2
        (oldDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
        hodd s hs lam jtilde hj
  apply partialGoodExtension_good hp (Nat.succ_pos a) hcop
    (show N = p * D by rfl)
    (show N = u * p ^ (a + 1) by
      dsimp only [N]
      rw [newDenom_eq]
      exact Nat.mul_comm _ _)
    q pi
  · intro i j hij
    exact shiftGuide_constant_mod (0 : ZMod p) i j hij
  · intro i
    change (partialGoodShift N u (shiftGuide p u (0 : ZMod p)) i).1 % p = 0
    simpa using
      partialGoodShift_shiftGuide_mod hp (Nat.succ_pos a) hcop.symm
        (show N = u * p ^ (a + 1) by
          dsimp only [N]
          rw [newDenom_eq]
          exact Nat.mul_comm _ _)
        ⟨0, hp.pos⟩ i
  · exact hpartial

private def primaryCorrection
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a)) : ℕ :=
  ZMod.val (-((newPrimeComponent p u a hp hcop).reduce lam *
    (newPrimeComponent p u a hp hcop).localQuotient
      ((jtilde.1 : ℤ) - primaryLabelRepresentative p a jtilde)))

/-- The first CRT coordinate of (4.14) has exactly the fixed-translate
shape required by the prime-power goodness lemma. -/
lemma distinguishedValue_primary_formula
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    (distinguishedValue p u a hp hcop rho s lam jtilde i).1 ≡
      (rho (PrimeClassGood.classDigit p a hp.pos i)).1 +
        primaryCorrection p u a hp hcop lam jtilde
      [MOD p ^ (a + 1)] := by
  let cP := newPrimeComponent p u a hp hcop
  apply (ZMod.natCast_eq_natCast_iff _ _ (p ^ (a + 1))).mp
  have hsplit := congrArg Prod.fst
    (distinguishedValue_split p u a hp hcop rho s lam jtilde i)
  simp only [PrimaryComponent.split_fst_eq_reduce] at hsplit
  rw [PrimaryComponent.reduce_natCast] at hsplit
  change (((distinguishedValue p u a hp hcop rho s lam jtilde i).1 : ℕ) :
      ZMod cP.q) = _ at hsplit
  have hsplit' :
      (((distinguishedValue p u a hp hcop rho s lam jtilde i).1 : ℕ) :
          ZMod (p ^ (a + 1))) =
        primaryDistinguishedValue p u a hp hcop rho lam jtilde i := by
    exact hsplit
  let z : ZMod (p ^ (a + 1)) :=
    -((newPrimeComponent p u a hp hcop).reduce lam *
      (newPrimeComponent p u a hp hcop).localQuotient
        ((jtilde.1 : ℤ) - primaryLabelRepresentative p a jtilde))
  have hcorr : primaryCorrection p u a hp hcop lam jtilde = ZMod.val z := by
    rfl
  have hprimary :
      primaryDistinguishedValue p u a hp hcop rho lam jtilde i =
        (((rho (PrimeClassGood.classDigit p a hp.pos i)).1 : ℕ) :
          ZMod (p ^ (a + 1))) + z := by
    simp only [primaryDistinguishedValue, primaryDigit,
      PrimeClassGood.classDigit, z]
    rw [sub_eq_add_neg]
    rfl
  change (((distinguishedValue p u a hp hcop rho s lam jtilde i).1 : ℕ) :
      ZMod (p ^ (a + 1))) = _
  rw [hsplit', hprimary, hcorr]
  let _ : NeZero (p ^ (a + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  push_cast
  rw [ZMod.natCast_zmod_val]

private lemma int_dvd_sub_iff_natModEq (m x y : ℕ) :
    (m : ℤ) ∣ (x : ℤ) - (y : ℤ) ↔ x ≡ y [MOD m] := by
  rw [Nat.modEq_iff_dvd]
  constructor <;> intro h <;> simpa only [neg_sub] using dvd_neg.mpr h

/-- The CRT values prescribed in (4.13)--(4.14) are partially good on the
distinguished source class. -/
lemma distinguishedValue_partialGood
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hodd : Nat.Coprime 2 (oldDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a))) (hrho : GoodPerm (p ^ a) rho)
    (s : LiftData (oldDenom p u a)) (hs : s.Separated)
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a)) :
    PartialGoodOnClass (newDenom p u a) p
      (distinguishedClass p u a hp lam jtilde : ℕ)
      (distinguishedValue p u a hp hcop rho s lam jtilde) := by
  let N := newDenom p u a
  let cP := newPrimeComponent p u a hp hcop
  let f : Fin N → Fin N :=
    distinguishedValue p u a hp hcop rho s lam jtilde
  intro i j hi hj hij
  by_cases hpow : p ^ (a + 1) ∣ indexDiff i j
  · let M := survivingModulus N (indexDiff i j)
    have hMu : M ∣ u := by
      exact survivingModulus_indexDiff_dvd_complement hp
        (show N = p ^ (a + 1) * u by exact newDenom_eq p u a) i j hpow
    have huN : u ∣ N := by
      rw [show N = p ^ (a + 1) * u by exact newDenom_eq p u a]
      exact dvd_mul_left u _
    have hMN : M ∣ N := hMu.trans huN
    let down : ZMod u →+* ZMod M := ZMod.castHom hMu (ZMod M)
    let direct : ZMod N →+* ZMod M := ZMod.castHom hMN (ZMod M)
    have hcomp : down.comp cP.reduceComplement = direct := RingHom.ext_zmod _ _
    let mu := flippedRoot p u a hp hcop lam
    let jt := auxiliaryLabel p u a hp hcop lam jtilde i
    have hjt : auxiliaryLabel p u a hp hcop lam jtilde j = jt := by
      exact (auxiliaryLabel_eq_of_primaryPower_dvd_indexDiff hp hcop lam
        jtilde i j hpow).symm
    have hjtOld : jt.1 % p = 0 := by
      exact auxiliaryLabel_isOld hp hp2 hcop lam jtilde i hi
    let oldF : Fin N → Fin N :=
      oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop)
        s mu jt
    have holdGood : GoodMap N oldF := by
      exact oldLineExtension_good hp hp2 hcop hodd s hs mu jt hjtOld
    intro hbad
    have houtMod : (f i).1 ≡ (f j).1 [MOD M] :=
      (int_dvd_sub_iff_natModEq M (f i).1 (f j).1).mp hbad
    have houtDirect :
        direct (((f i).1 : ℕ) : ZMod N) =
          direct (((f j).1 : ℕ) : ZMod N) := by
      have hcast : (((f i).1 : ℕ) : ZMod M) = (((f j).1 : ℕ) : ZMod M) :=
        (ZMod.natCast_eq_natCast_iff _ _ M).2 houtMod
      simpa [direct] using hcast
    have houtComplement :
        down (cP.reduceComplement (((f i).1 : ℕ) : ZMod N)) =
          down (cP.reduceComplement (((f j).1 : ℕ) : ZMod N)) := by
      calc
        down (cP.reduceComplement (((f i).1 : ℕ) : ZMod N)) =
            direct (((f i).1 : ℕ) : ZMod N) :=
          DFunLike.congr_fun hcomp _
        _ = direct (((f j).1 : ℕ) : ZMod N) := houtDirect
        _ = down (cP.reduceComplement (((f j).1 : ℕ) : ZMod N)) :=
          (DFunLike.congr_fun hcomp _).symm
    have hiSplit := congrArg Prod.snd
      (distinguishedValue_split p u a hp hcop rho s lam jtilde i)
    have hjSplit := congrArg Prod.snd
      (distinguishedValue_split p u a hp hcop rho s lam jtilde j)
    simp only [PrimaryComponent.split_snd_eq_reduceComplement] at hiSplit hjSplit
    let corr : ZMod cP.D := complementLocalQuotient p u a
      ((jtilde.1 : ℤ) - (jt.1 : ℤ))
    have hiComplement :
        cP.reduceComplement (((f i).1 : ℕ) : ZMod N) =
          cP.reduceComplement (((oldF i).1 : ℕ) : ZMod N) -
            cP.reduceComplement lam * corr := by
      rw [hiSplit]
      dsimp only [corr]
      rfl
    have hjComplement :
        cP.reduceComplement (((f j).1 : ℕ) : ZMod N) =
          cP.reduceComplement (((oldF j).1 : ℕ) : ZMod N) -
            cP.reduceComplement lam * corr := by
      rw [hjSplit]
      simp only [complementDistinguishedValue, hjt]
      dsimp only [corr]
      rfl
    rw [hiComplement, hjComplement] at houtComplement
    change down ((show ZMod u from
        cP.reduceComplement (((oldF i).1 : ℕ) : ZMod N)) -
          (show ZMod u from cP.reduceComplement lam) * (show ZMod u from corr)) =
      down ((show ZMod u from
        cP.reduceComplement (((oldF j).1 : ℕ) : ZMod N)) -
          (show ZMod u from cP.reduceComplement lam) * (show ZMod u from corr))
      at houtComplement
    have houtComplementMap :
        down (show ZMod u from
            cP.reduceComplement (((oldF i).1 : ℕ) : ZMod N)) -
            down ((show ZMod u from cP.reduceComplement lam) *
              (show ZMod u from corr)) =
          down (show ZMod u from
            cP.reduceComplement (((oldF j).1 : ℕ) : ZMod N)) -
            down ((show ZMod u from cP.reduceComplement lam) *
              (show ZMod u from corr)) := by
      calc
        down (show ZMod u from
            cP.reduceComplement (((oldF i).1 : ℕ) : ZMod N)) -
            down ((show ZMod u from cP.reduceComplement lam) *
              (show ZMod u from corr)) =
            down ((show ZMod u from
              cP.reduceComplement (((oldF i).1 : ℕ) : ZMod N)) -
                (show ZMod u from cP.reduceComplement lam) *
                  (show ZMod u from corr)) :=
          (down.map_sub _ _).symm
        _ = down ((show ZMod u from
              cP.reduceComplement (((oldF j).1 : ℕ) : ZMod N)) -
                (show ZMod u from cP.reduceComplement lam) *
                  (show ZMod u from corr)) := houtComplement
        _ = down (show ZMod u from
            cP.reduceComplement (((oldF j).1 : ℕ) : ZMod N)) -
            down ((show ZMod u from cP.reduceComplement lam) *
              (show ZMod u from corr)) := down.map_sub _ _
    have holdComplement :
        down (cP.reduceComplement (((oldF i).1 : ℕ) : ZMod N)) =
          down (cP.reduceComplement (((oldF j).1 : ℕ) : ZMod N)) := by
      exact sub_left_inj.mp houtComplementMap
    have holdCast : (((oldF i).1 : ℕ) : ZMod M) =
        (((oldF j).1 : ℕ) : ZMod M) := by
      calc
        (((oldF i).1 : ℕ) : ZMod M) =
            direct (((oldF i).1 : ℕ) : ZMod N) := by simp [direct]
        _ = down (cP.reduceComplement (((oldF i).1 : ℕ) : ZMod N)) :=
          (DFunLike.congr_fun hcomp _).symm
        _ = down (cP.reduceComplement (((oldF j).1 : ℕ) : ZMod N)) :=
          holdComplement
        _ = direct (((oldF j).1 : ℕ) : ZMod N) :=
          DFunLike.congr_fun hcomp _
        _ = (((oldF j).1 : ℕ) : ZMod M) := by simp [direct]
    have holdMod : (oldF i).1 ≡ (oldF j).1 [MOD M] :=
      (ZMod.natCast_eq_natCast_iff _ _ M).1 holdCast
    exact holdGood i j hij
      ((int_dvd_sub_iff_natModEq M (oldF i).1 (oldF j).1).2 holdMod)
  · exact not_dvd_output_sub_of_primePower_formula hp hcop
      (show N = p ^ (a + 1) * u by exact newDenom_eq p u a)
      rho hrho f
      (fun x _ ↦ distinguishedValue_primary_formula hp hcop rho s lam jtilde x)
      i j hi hj hpow

/-- Every new-label line map obtained from (4.15) is good. -/
lemma newLineExtension_good
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hodd : Nat.Coprime 2 (oldDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a))) (hrho : GoodPerm (p ^ a) rho)
    (s : LiftData (oldDenom p u a)) (hs : s.Separated)
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a)) :
    GoodMap (newDenom p u a)
      (newLineExtension p u a hp hcop rho s lam jtilde) := by
  let N := newDenom p u a
  let target := distinguishedClass p u a hp lam jtilde
  let q : Fin N → ℕ := lineShiftGuide p u a hp lam jtilde
  let pi : Fin N → Fin N := distinguishedValue p u a hp hcop rho s lam jtilde
  apply partialGoodExtension_good hp (Nat.succ_pos a) hcop
    (show N = p * oldDenom p u a by rfl)
    (show N = u * p ^ (a + 1) by
      dsimp only [N]
      rw [newDenom_eq]
      exact Nat.mul_comm _ _)
    q pi
  · intro i j hij
    exact shiftGuide_constant_mod (target : ZMod p) i j hij
  · intro i
    change (partialGoodShift N u (shiftGuide p u (target : ZMod p)) i).1 % p =
      target.1
    exact partialGoodShift_shiftGuide_mod hp (Nat.succ_pos a) hcop.symm
      (show N = u * p ^ (a + 1) by
        dsimp only [N]
        rw [newDenom_eq]
        exact Nat.mul_comm _ _)
      target i
  · exact distinguishedValue_partialGood hp hp2 hcop hodd rho hrho s hs lam jtilde

/-- Condition (4.3) for the complete pure nontrivial-prime line family. -/
theorem extendedFamily_good
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hodd : Nat.Coprime 2 (oldDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a))) (hrho : GoodPerm (p ^ a) rho)
    (s : LiftData (oldDenom p u a)) (hs : s.Separated) :
    FamilyGood (extendedFamily p u a hp hcop rho s) := by
  intro lam jtilde
  by_cases hj : jtilde.1 % p = 0
  · rw [extendedFamily_old hp hcop rho s lam jtilde hj]
    exact oldLineExtension_good hp hp2 hcop hodd s hs lam jtilde hj
  · rw [extendedFamily_new hp hcop rho s lam jtilde hj]
    exact newLineExtension_good hp hp2 hcop hodd rho hrho s hs lam jtilde

end

end Selector.PurePrimeExtension

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorPureConsistency.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Consistency of the pure nontrivial-prime extension

This file verifies the componentwise identity (4.6) for the line family
constructed in `SelectorPureExtension`.  The proof keeps the four source
cases visible: old--old, mixed, new--new at the new primary component, and
new--new at a complementary component (with its same-sign and opposite-sign
subcases).
-/

namespace Selector.PurePrimeExtension

open Erdos215.Selector
open Erdos215.Selector.Modular
open Erdos215.Selector.Final
open Erdos215.Selector.PrimeExtension
open Erdos215.Selector.PartialGood

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

private lemma partialGoodShift_cast
    {N u : ℕ} (hN : N ≠ 0) (q : Fin N → ℕ) (i : Fin N) :
    ((((partialGoodShift N u q i : Fin N) : ℕ) : ZMod N)) =
      ((i : ℕ) : ZMod N) + (u : ZMod N) * (q i : ℕ) := by
  let _ : NeZero N := ⟨hN⟩
  simp [partialGoodShift]

private lemma partialGoodExtension_cast
    {N u d : ℕ} (hN : N ≠ 0) (q : Fin N → ℕ)
    (pi : Fin N → Fin N) (i : Fin N) :
    ((((partialGoodExtension N u d q pi i : Fin N) : ℕ) : ZMod N)) =
      (((pi (partialGoodShift N u q i) : Fin N) : ℕ) : ZMod N) +
        (d : ZMod N) * (q i : ℕ) := by
  let _ : NeZero N := ⟨hN⟩
  simp [partialGoodExtension]

private lemma oldLineExtension_cast
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (j i : Fin (newDenom p u a)) :
    ((((oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop)
      s lam j i : Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))) =
      (((inducedFamily
          (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
          (copiedLift p u a s) lam j
          (partialGoodShift (newDenom p u a) u (oldShiftGuide p u) i) :
            Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) +
        (oldDenom p u a : ZMod (newDenom p u a)) *
          (oldShiftGuide p u i : ℕ) := by
  exact partialGoodExtension_cast
    (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
    (oldShiftGuide p u)
    (inducedFamily (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
      (copiedLift p u a s) lam j) i

private def complementToComponent
    {p u a : ℕ} (c : PrimaryComponent (newDenom p u a)) (hc : c.q ∣ u) :
    ZMod u →+* ZMod c.q :=
  ZMod.castHom hc (ZMod c.q)

private lemma reduce_eq_complementToComponent
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a)) (hc : c.q ∣ u)
    (x : ZMod (newDenom p u a)) :
    c.reduce x = complementToComponent c hc
      ((newPrimeComponent p u a hp hcop).reduceComplement x) := by
  let cP := newPrimeComponent p u a hp hcop
  let down := complementToComponent c hc
  have hhom : down.comp cP.reduceComplement = c.reduce := RingHom.ext_zmod _ _
  exact (DFunLike.congr_fun hhom x).symm

private lemma other_component_D_eq
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a)) (hdiv : c.q ∣ u) :
    c.D = p ^ (a + 1) * (u / c.q) := by
  apply Nat.eq_of_mul_eq_mul_left c.q_pos
  calc
    c.q * c.D = newDenom p u a := c.factor_q.symm
    _ = p ^ (a + 1) * u := newDenom_eq p u a
    _ = c.q * (p ^ (a + 1) * (u / c.q)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm c.q (p ^ (a + 1)), Nat.mul_assoc,
        Nat.mul_div_cancel' hdiv]

private lemma cast_complementLocalQuotient_eq_localQuotient
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a)) (hdiv : c.q ∣ u)
    (z : ℤ) (hz : (u : ℤ) ∣ z) :
    complementToComponent c hdiv (complementLocalQuotient p u a z) =
      c.localQuotient z := by
  let f : ZMod u →+* ZMod c.q := complementToComponent c hdiv
  apply c.isUnit_D.mul_right_cancel
  rw [c.localQuotient_mul_D]
  have hcomp := congrArg f
    (complementLocalQuotient_mul_power (a := a)
      (complement_ne_zero hp hcop) hcop z)
  simp only [map_mul, map_natCast, map_intCast] at hcomp
  rw [other_component_D_eq hp hcop c hdiv]
  push_cast
  have hpow : f ((p : ℕ) : ZMod u) ^ (a + 1) =
      ((p : ℕ) : ZMod c.q) ^ (a + 1) := by
    rw [map_natCast]
  simp only [map_pow] at hcomp
  rw [← hpow, ← mul_assoc, hcomp]
  rcases hz with ⟨k, rfl⟩
  have hu : (u : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr (complement_ne_zero hp hcop)
  have hcq : (c.q : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr c.q_ne_zero
  have hu_factor : (u : ℤ) = (c.q : ℤ) * (u / c.q : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdiv).symm
  rw [Int.mul_ediv_cancel_left k hu]
  rw [hu_factor]
  rw [show (c.q : ℤ) * (u / c.q : ℕ) * k =
      (c.q : ℤ) * ((u / c.q : ℕ) * k) by ring,
    Int.mul_ediv_cancel_left ((u / c.q : ℕ) * k) hcq]
  push_cast
  rw [← Int.natCast_div]
  simp only [Int.cast_natCast]
  ring

private lemma complementToComponent_complementDistinguishedValue
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (s : LiftData (oldDenom p u a))
    (c : PrimaryComponent (newDenom p u a)) (hc : c.q ∣ u)
    (lam : Root (newDenom p u a)) (j i : Fin (newDenom p u a)) :
    let mu := flippedRoot p u a hp hcop lam
    let jt := auxiliaryLabel p u a hp hcop lam j i
    complementToComponent c hc
        (complementDistinguishedValue p u a hp hcop s lam j i) =
      c.reduce ((((oldLineExtension p u a hp.ne_zero
        (complement_ne_zero hp hcop) s mu jt i) : Fin (newDenom p u a)) : ℕ) :
          ZMod (newDenom p u a)) -
      c.reduce lam * c.localQuotient ((j.1 : ℤ) - (jt.1 : ℤ)) := by
  dsimp only
  let cP := newPrimeComponent p u a hp hcop
  let oldValue : ZMod (newDenom p u a) :=
    (((oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop) s
      (flippedRoot p u a hp hcop lam)
      (auxiliaryLabel p u a hp hcop lam j i) i :
        Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))
  change complementToComponent c hc
      ((show ZMod u from cP.reduceComplement oldValue) -
        (show ZMod u from cP.reduceComplement lam) *
          complementLocalQuotient p u a
            ((j.1 : ℤ) - (auxiliaryLabel p u a hp hcop lam j i).1)) =
    c.reduce oldValue - c.reduce lam *
      c.localQuotient
        ((j.1 : ℤ) - (auxiliaryLabel p u a hp hcop lam j i).1)
  rw [map_sub, map_mul]
  rw [← reduce_eq_complementToComponent hp hcop c hc oldValue]
  rw [← reduce_eq_complementToComponent hp hcop c hc lam]
  rw [cast_complementLocalQuotient_eq_localQuotient hp hcop c hc]
  exact complement_dvd_label_sub_auxiliary p u a hp hcop lam j i

private lemma newPrime_reductions_eq_or_neg
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcop : Nat.Coprime p u)
    (lam₁ lam₂ : Root (newDenom p u a)) :
    let cP := newPrimeComponent p u a hp hcop
    cP.reduce lam₁ = cP.reduce lam₂ ∨ cP.reduce lam₁ = -cP.reduce lam₂ := by
  let cP := newPrimeComponent p u a hp hcop
  have hpTwo : Nat.Coprime p 2 :=
    hp.coprime_iff_not_dvd.mpr (fun h ↦
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
  have hodd : Nat.Coprime 2 cP.q := by
    exact hpTwo.symm.pow_right (a + 1)
  exact cP.root_eq_or_eq_neg hodd (cP.reduceRoot lam₁) (cP.reduceRoot lam₂)

private lemma primeRoot_eq_of_newPrime_reduce_eq
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam₁ lam₂ : Root (newDenom p u a))
    (h : (newPrimeComponent p u a hp hcop).reduce lam₁ =
      (newPrimeComponent p u a hp hcop).reduce lam₂) :
    (primeRoot p u a lam₁ : ZMod p) = primeRoot p u a lam₂ := by
  let cP := newPrimeComponent p u a hp hcop
  let down : ZMod cP.q →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero a)) (ZMod p)
  have hcomp : down.comp cP.reduce =
      ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) :=
    RingHom.ext_zmod _ _
  change ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam₁.1 =
    ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam₂.1
  rw [← DFunLike.congr_fun hcomp, ← DFunLike.congr_fun hcomp]
  exact congrArg down (by simpa only [cP] using h)

private lemma primeRoot_eq_neg_of_newPrime_reduce_eq_neg
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam₁ lam₂ : Root (newDenom p u a))
    (h : (newPrimeComponent p u a hp hcop).reduce lam₁ =
      -(newPrimeComponent p u a hp hcop).reduce lam₂) :
    (primeRoot p u a lam₁ : ZMod p) = -(primeRoot p u a lam₂) := by
  let cP := newPrimeComponent p u a hp hcop
  let down : ZMod cP.q →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero a)) (ZMod p)
  have hcomp : down.comp cP.reduce =
      ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) :=
    RingHom.ext_zmod _ _
  change ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam₁.1 =
    -ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam₂.1
  rw [← DFunLike.congr_fun hcomp, ← DFunLike.congr_fun hcomp]
  calc
    down (cP.reduce lam₁) = down (-cP.reduce lam₂) :=
      congrArg down (by simpa only [cP] using h)
    _ = -down (cP.reduce lam₂) := map_neg down _

private lemma lineShift_reaches_distinguished
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (j i : Fin (newDenom p u a)) :
    let x := partialGoodShift (newDenom p u a) u
      (lineShiftGuide p u a hp lam j) i
    x.1 % p = (distinguishedClass p u a hp lam j : ℕ) := by
  apply partialGoodShift_shiftGuide_mod hp (Nat.succ_pos a) hcop.symm
  rw [newDenom_eq, Nat.mul_comm]

private lemma newLineExtension_cast
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (j i : Fin (newDenom p u a)) :
    ((((newLineExtension p u a hp hcop rho s lam j i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))) =
      (((distinguishedValue p u a hp hcop rho s lam j
        (partialGoodShift (newDenom p u a) u
          (lineShiftGuide p u a hp lam j) i) : Fin (newDenom p u a)) : ℕ) :
          ZMod (newDenom p u a)) +
        (oldDenom p u a : ZMod (newDenom p u a)) *
          (lineShiftGuide p u a hp lam j i : ℕ) := by
  exact partialGoodExtension_cast
    (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
    (lineShiftGuide p u a hp lam j)
    (distinguishedValue p u a hp hcop rho s lam j) i

private lemma oldShiftGuide_after_lineShift
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (j i : Fin (newDenom p u a)) :
    oldShiftGuide p u
        (partialGoodShift (newDenom p u a) u
          (lineShiftGuide p u a hp lam j) i) =
      shiftDigit p u 0
        (distinguishedResidue (primeRoot p u a lam) (primeLabel p j)) := by
  unfold oldShiftGuide shiftGuide
  congr 1
  unfold sourceClass
  rw [← ZMod.natCast_mod]
  rw [lineShift_reaches_distinguished hp hcop lam j i]
  exact distinguishedClass_cast p u a hp lam j

/-- The old label obtained from an arbitrary opposite-primary auxiliary
root, rather than the canonical `flippedRoot`. -/
private def auxiliaryLabelFor
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam mu : Root (newDenom p u a))
    (j i : Fin (newDenom p u a)) : Fin (newDenom p u a) :=
  residueFin (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
    (((j.1 : ℕ) : ZMod (newDenom p u a)) +
      ((i.1 : ℕ) : ZMod (newDenom p u a)) *
        ((lam : ZMod (newDenom p u a)) - mu))

@[simp] private lemma auxiliaryLabelFor_cast
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam mu : Root (newDenom p u a))
    (j i : Fin (newDenom p u a)) :
    (((auxiliaryLabelFor hp hcop lam mu j i : ℕ) :
      ZMod (newDenom p u a))) =
      ((j.1 : ℕ) : ZMod (newDenom p u a)) +
        ((i.1 : ℕ) : ZMod (newDenom p u a)) *
          ((lam : ZMod (newDenom p u a)) - mu) := by
  exact residueFin_cast _ _

private lemma auxiliaryLabelFor_relation
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam mu : Root (newDenom p u a))
    (j i : Fin (newDenom p u a)) :
    ((i.1 : ℕ) : ZMod (newDenom p u a)) *
        ((lam : ZMod (newDenom p u a)) - mu) =
      -(((j.1 : ℕ) : ZMod (newDenom p u a)) -
        ((auxiliaryLabelFor hp hcop lam mu j i : ℕ) :
          ZMod (newDenom p u a))) := by
  rw [auxiliaryLabelFor_cast]
  ring

private lemma auxiliaryLabelFor_isOld
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcop : Nat.Coprime p u)
    (lam mu : Root (newDenom p u a))
    (j i : Fin (newDenom p u a))
    (hi : i.1 % p = (distinguishedClass p u a hp lam j : ℕ))
    (hmu : (primeRoot p u a mu : ZMod p) = -(primeRoot p u a lam : ZMod p)) :
    (auxiliaryLabelFor hp hcop lam mu j i : ℕ) % p = 0 := by
  have hiCast : ((i.1 : ℕ) : ZMod p) =
      distinguishedResidue (primeRoot p u a lam) (primeLabel p j) := by
    calc
      ((i.1 : ℕ) : ZMod p) = ((i.1 % p : ℕ) : ZMod p) :=
        (ZMod.natCast_mod i.1 p).symm
      _ = ((distinguishedClass p u a hp lam j : ℕ) : ZMod p) := by rw [hi]
      _ = _ := distinguishedClass_cast p u a hp lam j
  have hrel := distinguishedResidue_relation
    (primeRoot p u a lam) (primeLabel p j)
    (primeRoot_sub_neg_isUnit hp hp2 lam)
  have hcast := congrArg
    (ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p))
    (auxiliaryLabelFor_cast hp hcop lam mu j i)
  simp only [map_add, map_mul, map_sub, map_natCast] at hcast
  change ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) mu.1 =
    -ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam.1 at hmu
  have hz : (((auxiliaryLabelFor hp hcop lam mu j i : ℕ) : ℕ) : ZMod p) = 0 := by
    rw [hcast, hiCast, hmu]
    change primeLabel p j +
      distinguishedResidue (primeRoot p u a lam) (primeLabel p j) *
        ((primeRoot p u a lam : ZMod p) - -(primeRoot p u a lam : ZMod p)) = 0
    rw [hrel]
    exact add_neg_cancel _
  exact Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff
    (auxiliaryLabelFor hp hcop lam mu j i : ℕ) p).mp hz)

private theorem oldLineExtension_consistent
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u)
    (hoddN : Nat.Coprime 2 (newDenom p u a))
    (s : LiftData (oldDenom p u a))
    (c : PrimaryComponent (newDenom p u a))
    (lam₁ lam₂ : Root (newDenom p u a))
    (j₁ j₂ i : Fin (newDenom p u a))
    (hj₁ : j₁.1 % p = 0) (hj₂ : j₂.1 % p = 0)
    (hr : c.reduce lam₁ = c.reduce lam₂)
    (hline : ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam₁ : ZMod (newDenom p u a)) - lam₂) =
      -(((j₁ : ℕ) : ZMod (newDenom p u a)) -
        ((j₂ : ℕ) : ZMod (newDenom p u a)))) :
    c.reduce (((oldLineExtension p u a hp.ne_zero
        (complement_ne_zero hp hcop) s lam₁ j₁ i :
          Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) -
      c.reduce (((oldLineExtension p u a hp.ne_zero
        (complement_ne_zero hp hcop) s lam₂ j₂ i :
          Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) =
        -(c.reduce lam₁) * c.localQuotient
          (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) := by
  let N := newDenom p u a
  let hN : N ≠ 0 := newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop)
  let cP := newPrimeComponent p u a hp hcop
  let x : Fin N := partialGoodShift N u (oldShiftGuide p u) i
  have hoddP : Nat.Coprime 2 cP.q := hoddN.of_dvd_right cP.q_dvd
  have hxline : ((x : ℕ) : ZMod N) *
        ((lam₁ : ZMod N) - lam₂) =
      -(((j₁ : ℕ) : ZMod N) - ((j₂ : ℕ) : ZMod N)) := by
    rcases cP.root_eq_or_eq_neg hoddP (cP.reduceRoot lam₁)
        (cP.reduceRoot lam₂) with hsame | hopp
    · change cP.reduce lam₁ = cP.reduce lam₂ at hsame
      have huDiff : (u : ZMod N) *
          ((lam₁ : ZMod N) - lam₂) = 0 := by
        apply cP.split.injective
        apply Prod.ext
        · rw [cP.split_fst_eq_reduce, cP.split_fst_eq_reduce]
          simp only [map_mul, map_sub, map_natCast, hsame, sub_self, mul_zero,
            map_zero]
        · rw [cP.split_snd_eq_reduceComplement, cP.split_snd_eq_reduceComplement]
          simp only [map_mul, map_sub, map_natCast, map_zero]
          have hu0 : (u : ZMod cP.D) = 0 := by
            change (u : ZMod u) = 0
            exact ZMod.natCast_self u
          rw [hu0, zero_mul]
      rw [partialGoodShift_cast hN]
      calc
        (((i : ℕ) : ZMod N) + (u : ZMod N) *
              (oldShiftGuide p u i : ℕ)) *
            ((lam₁ : ZMod N) - lam₂) =
            ((i : ℕ) : ZMod N) * ((lam₁ : ZMod N) - lam₂) +
              (oldShiftGuide p u i : ZMod N) *
                ((u : ZMod N) * ((lam₁ : ZMod N) - lam₂)) := by ring
        _ = ((i : ℕ) : ZMod N) * ((lam₁ : ZMod N) - lam₂) := by
          rw [huDiff, mul_zero, add_zero]
        _ = -(((j₁ : ℕ) : ZMod N) - ((j₂ : ℕ) : ZMod N)) := hline
    · change cP.reduce lam₁ = -cP.reduce lam₂ at hopp
      have hoppP := primeRoot_eq_neg_of_newPrime_reduce_eq_neg hp hcop lam₁ lam₂ hopp
      have hj₁p : ((j₁.1 : ℕ) : ZMod p) = 0 := by
        rw [← ZMod.natCast_mod j₁.1 p, hj₁]
        simp
      have hj₂p : ((j₂.1 : ℕ) : ZMod p) = 0 := by
        rw [← ZMod.natCast_mod j₂.1 p, hj₂]
        simp
      have hlineP := congrArg
        (ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p)) hline
      simp only [map_mul, map_sub, map_neg, map_natCast] at hlineP
      change ((i.1 : ℕ) : ZMod p) *
          ((primeRoot p u a lam₁ : ZMod p) -
            (primeRoot p u a lam₂ : ZMod p)) =
        -(((j₁.1 : ℕ) : ZMod p) - ((j₂.1 : ℕ) : ZMod p)) at hlineP
      have hlineP' : ((i.1 : ℕ) : ZMod p) *
          ((primeRoot p u a lam₁ : ZMod p) -
            (primeRoot p u a lam₂ : ZMod p)) = 0 := by
        simpa only [hj₁p, hj₂p, sub_self, neg_zero] using hlineP
      have hdiffUnit : IsUnit
          ((primeRoot p u a lam₁ : ZMod p) -
            (primeRoot p u a lam₂ : ZMod p)) := by
        rw [hoppP]
        have hu := (primeRoot_sub_neg_isUnit hp hp2 lam₂).neg
        convert hu using 1 <;> ring
      have hiP : ((i.1 : ℕ) : ZMod p) = 0 := by
        apply hdiffUnit.mul_right_cancel
        simpa using hlineP'
      have hiMod : i.1 % p = 0 := by
        have hv := congrArg ZMod.val hiP
        simpa using hv
      have hq : oldShiftGuide p u i = 0 := oldShiftGuide_zero hp.pos i hiMod
      have hxi : x = i := by
        apply Fin.ext
        dsimp only [x, partialGoodShift]
        change (i.1 + u * oldShiftGuide p u i) % N = i.1
        rw [hq, mul_zero, add_zero, Nat.mod_eq_of_lt i.2]
      simpa only [hxi] using hline
  have hbase := inducedFamily_consistent hN hoddN (copiedLift p u a s)
    c lam₁ lam₂ j₁ j₂ x hr hxline
  rw [oldLineExtension_cast hp hcop, oldLineExtension_cast hp hcop]
  simp only [map_add, map_mul]
  dsimp only [N, hN, x] at hbase
  linear_combination hbase

private lemma reduce_distinguishedValue_other_component
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (c : PrimaryComponent (newDenom p u a)) (hc : c.q ∣ u)
    (lam : Root (newDenom p u a)) (j i : Fin (newDenom p u a)) :
    let mu := flippedRoot p u a hp hcop lam
    let jt := auxiliaryLabel p u a hp hcop lam j i
    c.reduce ((((distinguishedValue p u a hp hcop rho s lam j i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))) =
      c.reduce (((oldLineExtension p u a hp.ne_zero
        (complement_ne_zero hp hcop) s mu jt i : Fin (newDenom p u a)) : ℕ) :
          ZMod (newDenom p u a)) -
        c.reduce lam * c.localQuotient ((j.1 : ℤ) - (jt.1 : ℤ)) := by
  dsimp only
  let cP := newPrimeComponent p u a hp hcop
  let z : ZMod (newDenom p u a) :=
    (((distinguishedValue p u a hp hcop rho s lam j i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))
  have hs := distinguishedValue_split p u a hp hcop rho s lam j i
  have hsnd := congrArg Prod.snd hs
  rw [cP.split_snd_eq_reduceComplement] at hsnd
  change c.reduce z = _
  rw [reduce_eq_complementToComponent hp hcop c hc z, hsnd]
  exact complementToComponent_complementDistinguishedValue hp hcop s c hc lam j i

private lemma reduce_distinguishedValue_newPrimeComponent
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (j i : Fin (newDenom p u a)) :
    let cP := newPrimeComponent p u a hp hcop
    cP.reduce ((((distinguishedValue p u a hp hcop rho s lam j i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))) =
      primaryDistinguishedValue p u a hp hcop rho lam j i := by
  dsimp only
  let cP := newPrimeComponent p u a hp hcop
  have hs := distinguishedValue_split p u a hp hcop rho s lam j i
  have hfst := congrArg Prod.fst hs
  change cP.reduce ((((distinguishedValue p u a hp hcop rho s lam j i :
    Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))) = _
  rw [← cP.split_fst_eq_reduce]
  exact hfst

/-- Formula (4.13) is independent of the allowed old auxiliary line. -/
private lemma reduce_distinguishedValue_eq_auxiliary
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hoddN : Nat.Coprime 2 (newDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (c : PrimaryComponent (newDenom p u a)) (hcp : c.p ≠ p)
    (lam mu : Root (newDenom p u a))
    (j jOld i : Fin (newDenom p u a))
    (hjOld : jOld.1 % p = 0)
    (hi : i.1 % p = (distinguishedClass p u a hp lam j : ℕ))
    (hmuP : (newPrimeComponent p u a hp hcop).reduce mu =
      -(newPrimeComponent p u a hp hcop).reduce lam)
    (hmuC : c.reduce mu = c.reduce lam)
    (haux : ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam : ZMod (newDenom p u a)) - mu) =
      -(((j : ℕ) : ZMod (newDenom p u a)) -
        ((jOld : ℕ) : ZMod (newDenom p u a)))) :
    c.reduce ((((distinguishedValue p u a hp hcop rho s lam j i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))) =
      c.reduce (((oldLineExtension p u a hp.ne_zero
        (complement_ne_zero hp hcop) s mu jOld i : Fin (newDenom p u a)) : ℕ) :
          ZMod (newDenom p u a)) -
        c.reduce lam * c.localQuotient ((j.1 : ℤ) - (jOld.1 : ℤ)) := by
  let jt := auxiliaryLabel p u a hp hcop lam j i
  let flip := flippedRoot p u a hp hcop lam
  have hcq : c.q ∣ u := component_q_dvd_complement hp hcop c hcp
  have hjt : jt.1 % p = 0 :=
    auxiliaryLabel_isOld hp hp2 hcop lam j i hi
  have hflipC : c.reduce flip = c.reduce lam :=
    reduce_flippedRoot_eq_of_other_component hp hcop c hcp lam
  have hroot : c.reduce flip = c.reduce mu := hflipC.trans hmuC.symm
  have hcanonical := auxiliaryLabel_relation p u a hp hcop lam j i
  have holdLine : ((i : ℕ) : ZMod (newDenom p u a)) *
      ((flip : ZMod (newDenom p u a)) - mu) =
      -(((jt : ℕ) : ZMod (newDenom p u a)) -
        ((jOld : ℕ) : ZMod (newDenom p u a))) := by
    linear_combination haux - hcanonical
  have hold := oldLineExtension_consistent hp hp2 hcop hoddN s c
    flip mu jt jOld i hjt hjOld hroot holdLine
  have hq_jt_old : (c.q : ℤ) ∣ (jt.1 : ℤ) - (jOld.1 : ℤ) :=
    (Erdos215.Selector.Final.PrimaryComponent.relation_divisibility
      (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
      c flip mu jt jOld i hroot holdLine).2
  have hq_j_jt : (c.q : ℤ) ∣ (j.1 : ℤ) - (jt.1 : ℤ) := by
    have hcu : (c.q : ℤ) ∣ (u : ℤ) := by exact_mod_cast hcq
    exact hcu.trans (complement_dvd_label_sub_auxiliary p u a hp hcop lam j i)
  have hq_j_old : (c.q : ℤ) ∣ (j.1 : ℤ) - (jOld.1 : ℤ) :=
    (Erdos215.Selector.Final.PrimaryComponent.relation_divisibility
      (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
      c lam mu j jOld i hmuC.symm haux).2
  have htelescope := localizedQuotient_telescope c.q c.q_ne_zero
    ((c.D : ZMod c.q)⁻¹)
    (j.1 : ℤ) (jOld.1 : ℤ) (jt.1 : ℤ) (jOld.1 : ℤ)
    hq_jt_old hq_j_jt (by simpa using (dvd_zero (c.q : ℤ)))
  change c.localQuotient ((jt.1 : ℤ) - jOld.1) +
      c.localQuotient ((j.1 : ℤ) - jt.1) -
        c.localQuotient ((jOld.1 : ℤ) - jOld.1) =
      c.localQuotient ((j.1 : ℤ) - jOld.1) at htelescope
  have hzero : c.localQuotient 0 = 0 := by
    simp [PrimaryComponent.localQuotient, localizedQuotient]
  rw [sub_self, hzero, sub_zero] at htelescope
  rw [reduce_distinguishedValue_other_component hp hcop rho s c hcq]
  rw [hflipC] at hold
  dsimp only [flip, jt] at hold ⊢
  linear_combination hold - c.reduce lam * htelescope

private lemma new_old_opposite_and_distinguished
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcop : Nat.Coprime p u)
    (lam₁ lam₂ : Root (newDenom p u a))
    (j₁ j₂ i : Fin (newDenom p u a))
    (hj₁ : j₁.1 % p ≠ 0) (hj₂ : j₂.1 % p = 0)
    (hline : ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam₁ : ZMod (newDenom p u a)) - lam₂) =
      -(((j₁ : ℕ) : ZMod (newDenom p u a)) -
        ((j₂ : ℕ) : ZMod (newDenom p u a)))) :
    let cP := newPrimeComponent p u a hp hcop
    cP.reduce lam₁ = -cP.reduce lam₂ ∧
      i.1 % p = (distinguishedClass p u a hp lam₁ j₁ : ℕ) := by
  let cP := newPrimeComponent p u a hp hcop
  have hj₂p : ((j₂.1 : ℕ) : ZMod p) = 0 := by
    rw [← ZMod.natCast_mod j₂.1 p, hj₂]
    simp
  have hlineP := congrArg
    (ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p)) hline
  simp only [map_mul, map_sub, map_neg, map_natCast] at hlineP
  change ((i.1 : ℕ) : ZMod p) *
      ((primeRoot p u a lam₁ : ZMod p) -
        (primeRoot p u a lam₂ : ZMod p)) =
    -(((j₁.1 : ℕ) : ZMod p) - ((j₂.1 : ℕ) : ZMod p)) at hlineP
  have hlineP' : ((i.1 : ℕ) : ZMod p) *
      ((primeRoot p u a lam₁ : ZMod p) - (primeRoot p u a lam₂ : ZMod p)) =
      -((j₁.1 : ℕ) : ZMod p) := by
    simpa only [hj₂p, sub_zero] using hlineP
  rcases newPrime_reductions_eq_or_neg hp hp2 hcop lam₁ lam₂ with hsame | hopp
  · have hsameP := primeRoot_eq_of_newPrime_reduce_eq hp hcop lam₁ lam₂ hsame
    have hj₁p : ((j₁.1 : ℕ) : ZMod p) = 0 := by
      rw [hsameP, sub_self, mul_zero] at hlineP'
      simpa using hlineP'.symm
    have hv := congrArg ZMod.val hj₁p
    exact (hj₁ (by simpa using hv)).elim
  · refine ⟨hopp, ?_⟩
    have hoppP := primeRoot_eq_neg_of_newPrime_reduce_eq_neg hp hcop lam₁ lam₂ hopp
    have hlam₂ : (primeRoot p u a lam₂ : ZMod p) =
        -(primeRoot p u a lam₁ : ZMod p) := by
      linear_combination hoppP
    rw [hlam₂] at hlineP'
    have hiCast := distinguishedResidue_unique
      (primeRoot p u a lam₁) (primeLabel p j₁) ((i.1 : ℕ) : ZMod p)
      (primeRoot_sub_neg_isUnit hp hp2 lam₁) (by
        simpa only [primeLabel] using hlineP')
    have hclass := distinguishedClass_cast p u a hp lam₁ j₁
    have hiClass : ((i.1 : ℕ) : ZMod p) =
        ((distinguishedClass p u a hp lam₁ j₁ : ℕ) : ZMod p) :=
      hiCast.trans hclass.symm
    have hv := congrArg ZMod.val hiClass
    simpa only [ZMod.val_natCast,
      Nat.mod_eq_of_lt (distinguishedClass p u a hp lam₁ j₁).isLt] using hv

private lemma tested_component_ne_newPrime
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a))
    (lam₁ lam₂ : Root (newDenom p u a))
    (hr : c.reduce lam₁ = c.reduce lam₂)
    (hopp : (newPrimeComponent p u a hp hcop).reduce lam₁ =
      -(newPrimeComponent p u a hp hcop).reduce lam₂) :
    c.p ≠ p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  intro hcp
  have hpq : p ∣ c.q := by
    rw [PrimaryComponent.q, hcp]
    exact dvd_pow_self p c.exp_pos.ne'
  let down : ZMod c.q →+* ZMod p := ZMod.castHom hpq (ZMod p)
  have hcomp : down.comp c.reduce =
      ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) :=
    RingHom.ext_zmod _ _
  have hsameP : (primeRoot p u a lam₁ : ZMod p) = primeRoot p u a lam₂ := by
    change ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam₁.1 =
      ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam₂.1
    rw [← DFunLike.congr_fun hcomp, ← DFunLike.congr_fun hcomp]
    exact congrArg down hr
  have hoppP := primeRoot_eq_neg_of_newPrime_reduce_eq_neg hp hcop lam₁ lam₂ hopp
  have hzero : (primeRoot p u a lam₂ : ZMod p) -
      -(primeRoot p u a lam₂ : ZMod p) = 0 := by
    linear_combination hoppP - hsameP
  exact (primeRoot_sub_neg_isUnit hp hp2 lam₂).ne_zero hzero

private lemma component_eq_newPrimeComponent
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a)) (hcp : c.p = p) :
    c = newPrimeComponent p u a hp hcop := by
  have hq := component_q_eq_newPrimePower hp hcop c hcp
  have ha : c.a = a + 1 := by
    apply Nat.pow_right_injective hp.two_le
    simpa only [PrimaryComponent.q, hcp] using hq
  have hD : c.D = u := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos (a + 1))
    calc
      p ^ (a + 1) * c.D = c.q * c.D := by rw [hq]
      _ = newDenom p u a := c.factor_q.symm
      _ = p ^ (a + 1) * u := newDenom_eq p u a
  cases c with
  | mk cp ca cD cprime cexp cfactor ccop =>
      dsimp only [PrimaryComponent.q] at hcp ha hD
      subst cp
      subst ca
      subst cD
      rfl

private theorem new_old_consistent
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hoddN : Nat.Coprime 2 (newDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (c : PrimaryComponent (newDenom p u a))
    (lam₁ lam₂ : Root (newDenom p u a))
    (j₁ j₂ i : Fin (newDenom p u a))
    (hj₁ : j₁.1 % p ≠ 0) (hj₂ : j₂.1 % p = 0)
    (hr : c.reduce lam₁ = c.reduce lam₂)
    (hline : ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam₁ : ZMod (newDenom p u a)) - lam₂) =
      -(((j₁ : ℕ) : ZMod (newDenom p u a)) -
        ((j₂ : ℕ) : ZMod (newDenom p u a)))) :
    c.reduce (((newLineExtension p u a hp hcop rho s lam₁ j₁ i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) -
      c.reduce (((oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop)
        s lam₂ j₂ i : Fin (newDenom p u a)) : ℕ) :
          ZMod (newDenom p u a)) =
      -(c.reduce lam₁) * c.localQuotient
        (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) := by
  obtain ⟨hopp, hi⟩ :=
    new_old_opposite_and_distinguished hp hp2 hcop lam₁ lam₂ j₁ j₂ i
      hj₁ hj₂ hline
  have hcp : c.p ≠ p := tested_component_ne_newPrime hp hp2 hcop c lam₁ lam₂ hr hopp
  rw [newLineExtension_eq_on_distinguished hp hcop rho s lam₁ j₁ i hi]
  have hopp' : (newPrimeComponent p u a hp hcop).reduce lam₂ =
      -(newPrimeComponent p u a hp hcop).reduce lam₁ := by
    linear_combination hopp
  have hvalue := reduce_distinguishedValue_eq_auxiliary hp hp2 hcop hoddN rho s
    c hcp lam₁ lam₂ j₁ j₂ i hj₂ hi hopp' hr.symm hline
  linear_combination hvalue

private theorem old_new_consistent
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hoddN : Nat.Coprime 2 (newDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (c : PrimaryComponent (newDenom p u a))
    (lam₁ lam₂ : Root (newDenom p u a))
    (j₁ j₂ i : Fin (newDenom p u a))
    (hj₁ : j₁.1 % p = 0) (hj₂ : j₂.1 % p ≠ 0)
    (hr : c.reduce lam₁ = c.reduce lam₂)
    (hline : ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam₁ : ZMod (newDenom p u a)) - lam₂) =
      -(((j₁ : ℕ) : ZMod (newDenom p u a)) -
        ((j₂ : ℕ) : ZMod (newDenom p u a)))) :
    c.reduce (((oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop)
      s lam₁ j₁ i : Fin (newDenom p u a)) : ℕ) :
        ZMod (newDenom p u a)) -
      c.reduce (((newLineExtension p u a hp hcop rho s lam₂ j₂ i :
        Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) =
      -(c.reduce lam₁) * c.localQuotient
        (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) := by
  have hline' : ((i : ℕ) : ZMod (newDenom p u a)) *
      ((lam₂ : ZMod (newDenom p u a)) - lam₁) =
      -(((j₂ : ℕ) : ZMod (newDenom p u a)) -
        ((j₁ : ℕ) : ZMod (newDenom p u a))) := by
    linear_combination -hline
  have hswap := new_old_consistent hp hp2 hcop hoddN rho s c
    lam₂ lam₁ j₂ j₁ i hj₂ hj₁ hr.symm hline'
  have hdiv : (c.q : ℤ) ∣ ((j₁ : ℕ) : ℤ) - (j₂ : ℕ) :=
    (Erdos215.Selector.Final.PrimaryComponent.relation_divisibility
      (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
      c lam₁ lam₂ j₁ j₂ i hr hline).2
  have hneg : c.localQuotient (((j₂ : ℕ) : ℤ) - (j₁ : ℕ)) =
      -c.localQuotient (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) := by
    simp only [PrimaryComponent.localQuotient]
    convert localizedQuotient_neg c.q c.q_ne_zero ((c.D : ZMod c.q)⁻¹)
      (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) hdiv using 1 <;> ring
  rw [hneg, ← hr] at hswap
  linear_combination -hswap

private theorem new_new_primary_consistent
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (lam₁ lam₂ : Root (newDenom p u a))
    (j₁ j₂ i : Fin (newDenom p u a))
    (hr : (newPrimeComponent p u a hp hcop).reduce lam₁ =
      (newPrimeComponent p u a hp hcop).reduce lam₂)
    (hline : ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam₁ : ZMod (newDenom p u a)) - lam₂) =
      -(((j₁ : ℕ) : ZMod (newDenom p u a)) -
        ((j₂ : ℕ) : ZMod (newDenom p u a)))) :
    let cP := newPrimeComponent p u a hp hcop
    cP.reduce (((newLineExtension p u a hp hcop rho s lam₁ j₁ i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) -
      cP.reduce (((newLineExtension p u a hp hcop rho s lam₂ j₂ i :
        Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) =
      -(cP.reduce lam₁) * cP.localQuotient
        (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) := by
  dsimp only
  let cP := newPrimeComponent p u a hp hcop
  have hrootP := primeRoot_eq_of_newPrime_reduce_eq hp hcop lam₁ lam₂ hr
  have hlineP := congrArg
    (ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p)) hline
  simp only [map_mul, map_sub, map_neg, map_natCast] at hlineP
  change ((i.1 : ℕ) : ZMod p) *
      ((primeRoot p u a lam₁ : ZMod p) -
        (primeRoot p u a lam₂ : ZMod p)) =
    -(((j₁.1 : ℕ) : ZMod p) - ((j₂.1 : ℕ) : ZMod p)) at hlineP
  have hjPrime : primeLabel p j₁ = primeLabel p j₂ := by
    have hcast : ((j₁.1 : ℕ) : ZMod p) = ((j₂.1 : ℕ) : ZMod p) := by
      rw [hrootP, sub_self, mul_zero] at hlineP
      linear_combination hlineP
    exact hcast
  have hclass : distinguishedClass p u a hp lam₁ j₁ =
      distinguishedClass p u a hp lam₂ j₂ := by
    apply Erdos215.Selector.Separation.fin_eq_of_zmod_cast_eq hp.ne_zero
    rw [distinguishedClass_cast, distinguishedClass_cast, hrootP, hjPrime]
  have hguide : lineShiftGuide p u a hp lam₁ j₁ =
      lineShiftGuide p u a hp lam₂ j₂ := by
    funext z
    simp only [lineShiftGuide, hclass]
  let x : Fin (newDenom p u a) :=
    partialGoodShift (newDenom p u a) u
      (lineShiftGuide p u a hp lam₁ j₁) i
  have hx₂ : partialGoodShift (newDenom p u a) u
      (lineShiftGuide p u a hp lam₂ j₂) i = x := by
    rw [← hguide]
  have hjCast : ((j₁.1 : ℕ) : ZMod cP.q) = ((j₂.1 : ℕ) : ZMod cP.q) := by
    have hred := congrArg cP.reduce hline
    simp only [map_mul, map_sub, map_neg, map_natCast] at hred
    change ((i.1 : ℕ) : ZMod cP.q) *
      (cP.reduce lam₁ - cP.reduce lam₂) =
        -(((j₁.1 : ℕ) : ZMod cP.q) - ((j₂.1 : ℕ) : ZMod cP.q)) at hred
    rw [hr, sub_self, mul_zero] at hred
    linear_combination hred
  have hrep : primaryLabelRepresentative p a j₁ =
      primaryLabelRepresentative p a j₂ := by
    have hv := congrArg ZMod.val hjCast
    change ((j₁.1 : ZMod (p ^ (a + 1))).val) =
      ((j₂.1 : ZMod (p ^ (a + 1))).val) at hv
    simpa only [primaryLabelRepresentative, ZMod.val_natCast] using hv
  have hz₁ := primaryPower_dvd_label_sub p a j₁
  have hz₂ := primaryPower_dvd_label_sub p a j₂
  have hquot : cP.localQuotient
        ((j₁.1 : ℤ) - primaryLabelRepresentative p a j₁) -
      cP.localQuotient
        ((j₂.1 : ℤ) - primaryLabelRepresentative p a j₂) =
      cP.localQuotient ((j₁.1 : ℤ) - j₂.1) := by
    simp only [PrimaryComponent.localQuotient]
    rw [← localizedQuotient_sub cP.q cP.q_ne_zero
      ((cP.D : ZMod cP.q)⁻¹) _ _ (by simpa [cP] using hz₁)
        (by simpa [cP] using hz₂)]
    congr 1
    rw [hrep]
    ring
  rw [newLineExtension_cast hp hcop rho s lam₁ j₁ i,
    newLineExtension_cast hp hcop rho s lam₂ j₂ i]
  rw [hx₂]
  simp only [map_add, map_mul]
  rw [reduce_distinguishedValue_newPrimeComponent hp hcop rho s,
    reduce_distinguishedValue_newPrimeComponent hp hcop rho s]
  simp only [PrimaryComponent.reduce_natCast]
  simp only [primaryDistinguishedValue]
  rw [hr, hrep]
  dsimp only [cP] at hquot ⊢
  rw [hrep] at hquot
  dsimp only [x]
  rw [congrFun hguide i]
  linear_combination
    -(newPrimeComponent p u a hp hcop).reduce lam₂ * hquot

private theorem new_new_complement_same_sign
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hoddN : Nat.Coprime 2 (newDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (c : PrimaryComponent (newDenom p u a)) (hcp : c.p ≠ p)
    (lam₁ lam₂ : Root (newDenom p u a))
    (j₁ j₂ i : Fin (newDenom p u a))
    (hj₁ : j₁.1 % p ≠ 0) (hj₂ : j₂.1 % p ≠ 0)
    (hr : c.reduce lam₁ = c.reduce lam₂)
    (hsame : (newPrimeComponent p u a hp hcop).reduce lam₁ =
      (newPrimeComponent p u a hp hcop).reduce lam₂)
    (hline : ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam₁ : ZMod (newDenom p u a)) - lam₂) =
      -(((j₁ : ℕ) : ZMod (newDenom p u a)) -
        ((j₂ : ℕ) : ZMod (newDenom p u a)))) :
    c.reduce (((newLineExtension p u a hp hcop rho s lam₁ j₁ i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) -
      c.reduce (((newLineExtension p u a hp hcop rho s lam₂ j₂ i :
        Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) =
      -(c.reduce lam₁) * c.localQuotient
        (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) := by
  let cP := newPrimeComponent p u a hp hcop
  have hcq : c.q ∣ u := component_q_dvd_complement hp hcop c hcp
  have hrootP := primeRoot_eq_of_newPrime_reduce_eq hp hcop lam₁ lam₂ hsame
  have hlineP := congrArg
    (ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p)) hline
  simp only [map_mul, map_sub, map_neg, map_natCast] at hlineP
  change ((i.1 : ℕ) : ZMod p) *
      ((primeRoot p u a lam₁ : ZMod p) -
        (primeRoot p u a lam₂ : ZMod p)) =
    -(((j₁.1 : ℕ) : ZMod p) - ((j₂.1 : ℕ) : ZMod p)) at hlineP
  have hjPrime : primeLabel p j₁ = primeLabel p j₂ := by
    rw [hrootP, sub_self, mul_zero] at hlineP
    change ((j₁.1 : ℕ) : ZMod p) = ((j₂.1 : ℕ) : ZMod p)
    linear_combination hlineP
  have hclass : distinguishedClass p u a hp lam₁ j₁ =
      distinguishedClass p u a hp lam₂ j₂ := by
    apply Erdos215.Selector.Separation.fin_eq_of_zmod_cast_eq hp.ne_zero
    rw [distinguishedClass_cast, distinguishedClass_cast, hrootP, hjPrime]
  have hguide : lineShiftGuide p u a hp lam₁ j₁ =
      lineShiftGuide p u a hp lam₂ j₂ := by
    funext z
    simp only [lineShiftGuide, hclass]
  let x : Fin (newDenom p u a) :=
    partialGoodShift (newDenom p u a) u
      (lineShiftGuide p u a hp lam₁ j₁) i
  have hx₂ : partialGoodShift (newDenom p u a) u
      (lineShiftGuide p u a hp lam₂ j₂) i = x := by rw [← hguide]
  have hxclass₁ : x.1 % p = (distinguishedClass p u a hp lam₁ j₁ : ℕ) :=
    lineShift_reaches_distinguished hp hcop lam₁ j₁ i
  have hxclass₂ : x.1 % p = (distinguishedClass p u a hp lam₂ j₂ : ℕ) := by
    rw [← hclass]
    exact hxclass₁
  let mu := flippedRoot p u a hp hcop lam₁
  let jt := auxiliaryLabel p u a hp hcop lam₁ j₁ x
  have hjt : jt.1 % p = 0 :=
    auxiliaryLabel_isOld hp hp2 hcop lam₁ j₁ x hxclass₁
  have hmuP : cP.reduce mu = -cP.reduce lam₂ := by
    dsimp only [mu, cP]
    rw [newPrimeComponent_reduce_flippedRoot, hsame]
  have hmuC : c.reduce mu = c.reduce lam₂ := by
    dsimp only [mu]
    rw [reduce_flippedRoot_eq_of_other_component hp hcop c hcp, hr]
  have huDiff : (u : ZMod (newDenom p u a)) *
      ((lam₁ : ZMod (newDenom p u a)) - lam₂) = 0 := by
    apply cP.split.injective
    apply Prod.ext
    · rw [cP.split_fst_eq_reduce, cP.split_fst_eq_reduce]
      simp only [map_mul, map_sub, map_natCast, map_zero]
      rw [hsame, sub_self, mul_zero]
    · rw [cP.split_snd_eq_reduceComplement, cP.split_snd_eq_reduceComplement]
      simp only [map_mul, map_sub, map_natCast, map_zero]
      have hu0 : (u : ZMod cP.D) = 0 := by
        change (u : ZMod u) = 0
        exact ZMod.natCast_self u
      rw [hu0, zero_mul]
  have hxline : ((x : ℕ) : ZMod (newDenom p u a)) *
      ((lam₁ : ZMod (newDenom p u a)) - lam₂) =
      -(((j₁ : ℕ) : ZMod (newDenom p u a)) -
        ((j₂ : ℕ) : ZMod (newDenom p u a))) := by
    rw [partialGoodShift_cast
      (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))]
    calc
      _ = ((i : ℕ) : ZMod (newDenom p u a)) *
          ((lam₁ : ZMod (newDenom p u a)) - lam₂) +
        (lineShiftGuide p u a hp lam₁ j₁ i : ZMod (newDenom p u a)) *
          ((u : ZMod (newDenom p u a)) *
            ((lam₁ : ZMod (newDenom p u a)) - lam₂)) := by ring
      _ = ((i : ℕ) : ZMod (newDenom p u a)) *
          ((lam₁ : ZMod (newDenom p u a)) - lam₂) := by rw [huDiff]; ring
      _ = _ := hline
  have haux₁ := auxiliaryLabel_relation p u a hp hcop lam₁ j₁ x
  have haux₂ : ((x : ℕ) : ZMod (newDenom p u a)) *
      ((lam₂ : ZMod (newDenom p u a)) - mu) =
      -(((j₂ : ℕ) : ZMod (newDenom p u a)) -
        ((jt : ℕ) : ZMod (newDenom p u a))) := by
    linear_combination haux₁ - hxline
  have hv₁ := reduce_distinguishedValue_other_component hp hcop rho s c hcq
    lam₁ j₁ x
  have hv₂ := reduce_distinguishedValue_eq_auxiliary hp hp2 hcop hoddN rho s
    c hcp lam₂ mu j₂ jt x hjt hxclass₂ hmuP hmuC haux₂
  have hz₁ : (c.q : ℤ) ∣ (j₁.1 : ℤ) - (jt.1 : ℤ) := by
    have hcu : (c.q : ℤ) ∣ (u : ℤ) := by exact_mod_cast hcq
    exact hcu.trans (complement_dvd_label_sub_auxiliary p u a hp hcop lam₁ j₁ x)
  have hz₂ : (c.q : ℤ) ∣ (j₂.1 : ℤ) - (jt.1 : ℤ) :=
    (Erdos215.Selector.Final.PrimaryComponent.relation_divisibility
      (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
      c lam₂ mu j₂ jt x hmuC.symm haux₂).2
  have hquot : c.localQuotient ((j₁.1 : ℤ) - jt.1) -
      c.localQuotient ((j₂.1 : ℤ) - jt.1) =
      c.localQuotient ((j₁.1 : ℤ) - j₂.1) := by
    simp only [PrimaryComponent.localQuotient]
    rw [← localizedQuotient_sub c.q c.q_ne_zero ((c.D : ZMod c.q)⁻¹)
      _ _ hz₁ hz₂]
    congr 1
    ring
  rw [newLineExtension_cast hp hcop rho s lam₁ j₁ i,
    newLineExtension_cast hp hcop rho s lam₂ j₂ i, hx₂]
  simp only [map_add, map_mul]
  rw [hv₁, hv₂, hr]
  simp only [PrimaryComponent.reduce_natCast]
  dsimp only [mu, jt] at hquot ⊢
  have hguideC :
      ((lineShiftGuide p u a hp lam₁ j₁ i : ℕ) : ZMod c.q) =
        ((lineShiftGuide p u a hp lam₂ j₂ i : ℕ) : ZMod c.q) :=
    congrArg (fun n : ℕ ↦ (n : ZMod c.q)) (congrFun hguide i)
  linear_combination -(c.reduce lam₂) * hquot +
    (oldDenom p u a : ZMod c.q) * hguideC

private theorem new_new_complement_opposite_sign
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hoddN : Nat.Coprime 2 (newDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (c : PrimaryComponent (newDenom p u a)) (hcp : c.p ≠ p)
    (lam₁ lam₂ : Root (newDenom p u a))
    (j₁ j₂ i : Fin (newDenom p u a))
    (hj₁ : j₁.1 % p ≠ 0) (hj₂ : j₂.1 % p ≠ 0)
    (hr : c.reduce lam₁ = c.reduce lam₂)
    (hopp : (newPrimeComponent p u a hp hcop).reduce lam₁ =
      -(newPrimeComponent p u a hp hcop).reduce lam₂)
    (hline : ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam₁ : ZMod (newDenom p u a)) - lam₂) =
      -(((j₁ : ℕ) : ZMod (newDenom p u a)) -
        ((j₂ : ℕ) : ZMod (newDenom p u a)))) :
    c.reduce (((newLineExtension p u a hp hcop rho s lam₁ j₁ i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) -
      c.reduce (((newLineExtension p u a hp hcop rho s lam₂ j₂ i :
        Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) =
      -(c.reduce lam₁) * c.localQuotient
        (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) := by
  let N := newDenom p u a
  let hN : N ≠ 0 := newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop)
  let cP := newPrimeComponent p u a hp hcop
  let q₁ := lineShiftGuide p u a hp lam₁ j₁ i
  let q₂ := lineShiftGuide p u a hp lam₂ j₂ i
  let x₁ : Fin N := partialGoodShift N u (lineShiftGuide p u a hp lam₁ j₁) i
  let x₂ : Fin N := partialGoodShift N u (lineShiftGuide p u a hp lam₂ j₂) i
  let r₂ := oldShiftGuide p u x₁
  let r₁ := oldShiftGuide p u x₂
  let k₃ := auxiliaryLabelFor hp hcop lam₁ lam₂ j₁ x₁
  let k₄ := auxiliaryLabelFor hp hcop lam₂ lam₁ j₂ x₂
  let y₁ : Fin N := partialGoodShift N u (oldShiftGuide p u) x₁
  let y₂ : Fin N := partialGoodShift N u (oldShiftGuide p u) x₂
  have hoppP := primeRoot_eq_neg_of_newPrime_reduce_eq_neg hp hcop lam₁ lam₂ hopp
  have hoppP' : (primeRoot p u a lam₂ : ZMod p) =
      -(primeRoot p u a lam₁ : ZMod p) := by linear_combination hoppP
  have hlineP := congrArg
    (ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p)) hline
  simp only [map_mul, map_sub, map_neg, map_natCast] at hlineP
  change ((i.1 : ℕ) : ZMod p) *
      ((primeRoot p u a lam₁ : ZMod p) -
        (primeRoot p u a lam₂ : ZMod p)) =
    -(((j₁.1 : ℕ) : ZMod p) - ((j₂.1 : ℕ) : ZMod p)) at hlineP
  have hlineP' : ((i.1 : ℕ) : ZMod p) *
      ((primeRoot p u a lam₁ : ZMod p) - (primeRoot p u a lam₂ : ZMod p)) =
      -(primeLabel p j₁ - primeLabel p j₂) := by
    simpa only [primeLabel] using hlineP
  have hcross := shiftDigit_cross_eq (u := u) hp
    (primeRoot p u a lam₁) (primeRoot p u a lam₂)
    (primeLabel p j₁) (primeLabel p j₂) ((i.1 : ℕ) : ZMod p)
    (primeRoot_sub_neg_isUnit hp hp2 lam₁) hoppP' hlineP'
  have hsum0 := shiftDigit_cross_sum (u := u) hp
    (primeRoot p u a lam₁) (primeRoot p u a lam₂)
    (primeLabel p j₁) (primeLabel p j₂) ((i.1 : ℕ) : ZMod p)
    (primeRoot_sub_neg_isUnit hp hp2 lam₁) hoppP' hlineP'
  have hs₇₁ : q₁ = r₁ := by
    dsimp only [q₁, r₁]
    rw [oldShiftGuide_after_lineShift hp hcop lam₂ j₂ i]
    simpa only [lineShiftGuide, shiftGuide, sourceClass, distinguishedClass_cast] using hcross.1
  have hs₇₂ : q₂ = r₂ := by
    dsimp only [q₂, r₂]
    rw [oldShiftGuide_after_lineShift hp hcop lam₁ j₁ i]
    simpa only [lineShiftGuide, shiftGuide, sourceClass, distinguishedClass_cast] using hcross.2
  have hsum : q₁ + r₂ = q₂ + r₁ := by
    dsimp only [q₁, q₂, r₁, r₂]
    rw [oldShiftGuide_after_lineShift hp hcop lam₁ j₁ i,
      oldShiftGuide_after_lineShift hp hcop lam₂ j₂ i]
    simpa only [lineShiftGuide, shiftGuide, sourceClass, distinguishedClass_cast] using hsum0
  have hx₁class : x₁.1 % p =
      (distinguishedClass p u a hp lam₁ j₁ : ℕ) :=
    lineShift_reaches_distinguished hp hcop lam₁ j₁ i
  have hx₂class : x₂.1 % p =
      (distinguishedClass p u a hp lam₂ j₂ : ℕ) :=
    lineShift_reaches_distinguished hp hcop lam₂ j₂ i
  have hk₃old : k₃.1 % p = 0 :=
    auxiliaryLabelFor_isOld hp hp2 hcop lam₁ lam₂ j₁ x₁ hx₁class hoppP'
  have hk₄old : k₄.1 % p = 0 :=
    auxiliaryLabelFor_isOld hp hp2 hcop lam₂ lam₁ j₂ x₂ hx₂class hoppP
  have haux₁ := auxiliaryLabelFor_relation hp hcop lam₁ lam₂ j₁ x₁
  have haux₂ := auxiliaryLabelFor_relation hp hcop lam₂ lam₁ j₂ x₂
  have hy : y₂ = y₁ := by
    apply Erdos215.Selector.Separation.fin_eq_of_zmod_cast_eq hN
    rw [partialGoodShift_cast hN, partialGoodShift_cast hN,
      partialGoodShift_cast hN, partialGoodShift_cast hN]
    change ((i : ℕ) : ZMod N) + (u : ZMod N) * (q₂ : ℕ) +
        (u : ZMod N) * (r₁ : ℕ) =
      ((i : ℕ) : ZMod N) + (u : ZMod N) * (q₁ : ℕ) +
        (u : ZMod N) * (r₂ : ℕ)
    have hsumN := congrArg (fun n : ℕ ↦ (n : ZMod N)) hsum
    push_cast at hsumN
    linear_combination -(u : ZMod N) * hsumN
  have hyline : ((y₁ : ℕ) : ZMod N) *
      ((lam₂ : ZMod N) - lam₁) =
      -(((k₃ : ℕ) : ZMod N) - ((k₄ : ℕ) : ZMod N)) := by
    have haux₁' : (((i : ℕ) : ZMod N) + (u : ZMod N) * (q₁ : ℕ)) *
        ((lam₁ : ZMod N) - lam₂) =
        -(((j₁ : ℕ) : ZMod N) - ((k₃ : ℕ) : ZMod N)) := by
      rw [← partialGoodShift_cast hN]
      exact haux₁
    have haux₂' : (((i : ℕ) : ZMod N) + (u : ZMod N) * (q₂ : ℕ)) *
        ((lam₂ : ZMod N) - lam₁) =
        -(((j₂ : ℕ) : ZMod N) - ((k₄ : ℕ) : ZMod N)) := by
      rw [← partialGoodShift_cast hN]
      exact haux₂
    have hrel := auxiliaryOldLines_relation
      ((i : ℕ) : ZMod N) ((u : ZMod N) * (q₁ : ℕ))
      ((u : ZMod N) * (q₂ : ℕ))
      ((j₁ : ℕ) : ZMod N) ((j₂ : ℕ) : ZMod N)
      ((k₃ : ℕ) : ZMod N) ((k₄ : ℕ) : ZMod N)
      (lam₁ : ZMod N) (lam₂ : ZMod N) hline haux₁' haux₂'
    rw [partialGoodShift_cast hN, partialGoodShift_cast hN]
    dsimp only [q₁, q₂, r₂] at hs₇₂ ⊢
    push_cast at hs₇₂ ⊢
    rw [← hs₇₂]
    simpa only [add_assoc] using hrel
  have hbase := inducedFamily_consistent hN hoddN (copiedLift p u a s)
    c lam₂ lam₁ k₃ k₄ y₁ hr.symm hyline
  have hmu₁P : cP.reduce lam₂ = -cP.reduce lam₁ := by linear_combination hopp
  have hv₁ := reduce_distinguishedValue_eq_auxiliary hp hp2 hcop hoddN rho s
    c hcp lam₁ lam₂ j₁ k₃ x₁ hk₃old hx₁class hmu₁P hr.symm haux₁
  have hv₂ := reduce_distinguishedValue_eq_auxiliary hp hp2 hcop hoddN rho s
    c hcp lam₂ lam₁ j₂ k₄ x₂ hk₄old hx₂class hopp hr haux₂
  have hz₃₄ := (Erdos215.Selector.Final.PrimaryComponent.relation_divisibility
    hN c lam₂ lam₁ k₃ k₄ y₁ hr.symm hyline).2
  have hz₁₃ := (Erdos215.Selector.Final.PrimaryComponent.relation_divisibility
    hN c lam₁ lam₂ j₁ k₃ x₁ hr haux₁).2
  have hz₂₄ := (Erdos215.Selector.Final.PrimaryComponent.relation_divisibility
    hN c lam₂ lam₁ j₂ k₄ x₂ hr.symm haux₂).2
  have htelescope := localizedQuotient_telescope c.q c.q_ne_zero
    ((c.D : ZMod c.q)⁻¹) (j₁.1 : ℤ) (j₂.1 : ℤ)
      (k₃.1 : ℤ) (k₄.1 : ℤ) hz₃₄ hz₁₃ hz₂₄
  change c.localQuotient ((k₃.1 : ℤ) - k₄.1) +
      c.localQuotient ((j₁.1 : ℤ) - k₃.1) -
        c.localQuotient ((j₂.1 : ℤ) - k₄.1) =
      c.localQuotient ((j₁.1 : ℤ) - j₂.1) at htelescope
  have hsumC : ((q₁ : ℕ) : ZMod c.q) + (r₂ : ℕ) =
      ((q₂ : ℕ) : ZMod c.q) + (r₁ : ℕ) := by
    have hsumC' := congrArg (fun n : ℕ ↦ (n : ZMod c.q)) hsum
    push_cast at hsumC'
    exact hsumC'
  have hsumCRed :
      c.reduce ((q₁ : ℕ) : ZMod (newDenom p u a)) +
          c.reduce ((r₂ : ℕ) : ZMod (newDenom p u a)) =
        c.reduce ((q₂ : ℕ) : ZMod (newDenom p u a)) +
          c.reduce ((r₁ : ℕ) : ZMod (newDenom p u a)) := by
    have hsumCRed' := congrArg
      (fun n : ℕ ↦ c.reduce ((n : ℕ) : ZMod (newDenom p u a))) hsum
    simpa only [Nat.cast_add, map_add] using hsumCRed'
  rw [newLineExtension_cast hp hcop rho s lam₁ j₁ i,
    newLineExtension_cast hp hcop rho s lam₂ j₂ i]
  simp only [map_add, map_mul]
  rw [hv₁, hv₂]
  rw [oldLineExtension_cast hp hcop, oldLineExtension_cast hp hcop]
  simp only [map_add, map_mul]
  have hy' : partialGoodShift (newDenom p u a) u (oldShiftGuide p u) x₂ =
      partialGoodShift (newDenom p u a) u (oldShiftGuide p u) x₁ := by
    simpa only [N, y₁, y₂] using hy
  rw [hy', hr]
  dsimp only [q₁, q₂, r₁, r₂, k₃, k₄, y₁] at hbase htelescope hsumC hsumCRed ⊢
  linear_combination hbase - c.reduce lam₂ * htelescope +
    c.reduce (oldDenom p u a : ZMod (newDenom p u a)) * hsumCRed

/-- The family produced by the pure nontrivial-prime construction satisfies
 the exact componentwise consistency identity (4.6). -/
theorem extendedFamily_consistent
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u)
    (hoddN : Nat.Coprime 2 (newDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a)) :
    FamilyConsistent (extendedFamily p u a hp hcop rho s) := by
  intro c lam₁ lam₂ j₁ j₂ i hr hline
  by_cases hj₁ : j₁.1 % p = 0
  · by_cases hj₂ : j₂.1 % p = 0
    · rw [extendedFamily_old hp hcop rho s lam₁ j₁ hj₁,
        extendedFamily_old hp hcop rho s lam₂ j₂ hj₂]
      exact oldLineExtension_consistent hp hp2 hcop hoddN s c
        lam₁ lam₂ j₁ j₂ i hj₁ hj₂ hr hline
    · rw [extendedFamily_old hp hcop rho s lam₁ j₁ hj₁,
        extendedFamily_new hp hcop rho s lam₂ j₂ hj₂]
      exact old_new_consistent hp hp2 hcop hoddN rho s c
        lam₁ lam₂ j₁ j₂ i hj₁ hj₂ hr hline
  · by_cases hj₂ : j₂.1 % p = 0
    · rw [extendedFamily_new hp hcop rho s lam₁ j₁ hj₁,
        extendedFamily_old hp hcop rho s lam₂ j₂ hj₂]
      exact new_old_consistent hp hp2 hcop hoddN rho s c
        lam₁ lam₂ j₁ j₂ i hj₁ hj₂ hr hline
    · rw [extendedFamily_new hp hcop rho s lam₁ j₁ hj₁,
        extendedFamily_new hp hcop rho s lam₂ j₂ hj₂]
      rcases component_classification hp hcop c with hprimary | hother
      · obtain ⟨hcp, _hq⟩ := hprimary
        have hcEq := component_eq_newPrimeComponent hp hcop c hcp
        subst c
        exact new_new_primary_consistent hp hcop rho s lam₁ lam₂
          j₁ j₂ i hr hline
      · obtain ⟨hcp, _hcq⟩ := hother
        rcases newPrime_reductions_eq_or_neg hp hp2 hcop lam₁ lam₂ with
          hsame | hopp
        · exact new_new_complement_same_sign hp hp2 hcop hoddN rho s c hcp
            lam₁ lam₂ j₁ j₂ i hj₁ hj₂ hr hsame hline
        · exact new_new_complement_opposite_sign hp hp2 hcop hoddN rho s c hcp
            lam₁ lam₂ j₁ j₂ i hj₁ hj₂ hr hopp hline

end

end Selector.PurePrimeExtension

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorPrimeSplit.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
Split a nonzero denominator into its full `p`-primary factor and the
complementary factor.  The equality is deliberately oriented as
`d = u * p ^ a`, so that a caller can eliminate `d` with `subst` before
constructing or transporting dependent data such as `LiftData d`.
-/

namespace Selector.PrimeSplit

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The exponent of `p` in `d`. -/
def exponent (p d : ℕ) : ℕ := d.factorization p

/-- The factor of `d` complementary to its full `p`-primary part. -/
def complement (p d : ℕ) : ℕ := ordCompl[p] d

/-- The canonical prime split, packaged for dependent downstream uses. -/
structure Data (p d : ℕ) where
  a : ℕ
  u : ℕ
  eq_complement_mul_pow : d = u * p ^ a
  complement_ne_zero : u ≠ 0
  coprime : Nat.Coprime p u

/-- The canonical complement really gives the requested factorization,
in the literal orientation useful for rewriting a `LiftData d`. -/
theorem eq_complement_mul_pow (p d : ℕ) :
    d = complement p d * p ^ exponent p d := by
  simpa only [complement, exponent, mul_comm] using
    (Nat.ordProj_mul_ordCompl_eq_self d p).symm

/-- A nonzero denominator has nonzero prime complement. -/
theorem complement_ne_zero (p d : ℕ) (hd : d ≠ 0) :
    complement p d ≠ 0 := by
  exact (Nat.ordCompl_pos p hd).ne'

/-- The prime is coprime to its complementary factor. -/
theorem coprime_complement {p d : ℕ} (hp : p.Prime) (hd : d ≠ 0) :
    Nat.Coprime p (complement p d) := by
  exact Nat.coprime_ordCompl hp hd

/-- The canonical packaged prime split. -/
def canonical (p d : ℕ) (hp : p.Prime) (hd : d ≠ 0) : Data p d where
  a := exponent p d
  u := complement p d
  eq_complement_mul_pow := eq_complement_mul_pow p d
  complement_ne_zero := complement_ne_zero p d hd
  coprime := coprime_complement hp hd

/-- Existential form intended for `obtain ⟨u, a, rfl, hu, hpu⟩ := ...`.
The prime exponent chosen here is exactly `d.factorization p`, and `u` is
exactly `ordCompl[p] d`. -/
theorem exists_eq_complement_mul_pow {p d : ℕ} (hp : p.Prime) (hd : d ≠ 0) :
    ∃ u a, d = u * p ^ a ∧ u ≠ 0 ∧ Nat.Coprime p u := by
  exact ⟨complement p d, exponent p d, eq_complement_mul_pow p d,
    complement_ne_zero p d hd, coprime_complement hp hd⟩

end

end Selector.PrimeSplit

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorHensel.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
Elementary Hensel lifting for square roots of `-1` modulo odd prime powers.
-/

namespace Selector.Modular

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- One elementary Hensel step for `X² + 1`.  Besides producing a root
modulo the next power, the statement records that it reduces to the given
root.  The proof uses the correction
`x' = x + t p^a`, where `m = (1 + x²) / p^a` and
`t = -(2x)⁻¹m (mod p)`. -/
theorem exists_root_lift_succ (p a : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 0 < a) (lam : Root (p ^ a)) :
    ∃ mu : Root (p ^ (a + 1)),
      ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a)) mu.1 = lam.1 := by
  letI : Fact p.Prime := ⟨hp⟩
  let q := p ^ a
  have hqpos : 0 < q := pow_pos hp.pos _
  letI : NeZero q := ⟨hqpos.ne'⟩
  let x := ZMod.val lam.1
  have hxdiv : q ∣ 1 + x ^ 2 := by
    simpa only [q] using root_dvd_one_add_val_sq hqpos.ne' lam
  let m := (1 + x ^ 2) / q
  have hqm : q * m = 1 + x ^ 2 := by
    exact Nat.mul_div_cancel' hxdiv
  have hpq : p ∣ q := by
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    simp [q, pow_succ]
  have hxroot : ((x : ℕ) : ZMod p) ^ 2 = -1 := by
    have hz : ((1 + x ^ 2 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (1 + x ^ 2) p).2 (hpq.trans hxdiv)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at hz
    linear_combination hz
  have hcop : Nat.Coprime 2 p := by
    apply Nat.Coprime.symm
    rw [hp.coprime_iff_not_dvd]
    intro hpd
    have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hpd
    exact hp2 (Nat.le_antisymm hle hp.two_le)
  have htwo : IsUnit (2 : ZMod p) :=
    (ZMod.isUnit_iff_coprime 2 p).2 hcop
  have hxunit : IsUnit (x : ZMod p) :=
    root_isUnit (⟨(x : ZMod p), hxroot⟩ : Root p)
  have htwox : IsUnit ((2 : ZMod p) * (x : ZMod p)) := htwo.mul hxunit
  let t : ZMod p := (((2 : ZMod p) * (x : ZMod p))⁻¹) * (-(m : ZMod p))
  have ht : (m : ZMod p) + ((2 : ZMod p) * (x : ZMod p)) * t = 0 := by
    have hmul : ((2 : ZMod p) * (x : ZMod p)) * t = -(m : ZMod p) := by
      dsimp only [t]
      rw [← mul_assoc, ZMod.mul_inv_of_unit _ htwox, one_mul]
    rw [hmul, add_neg_cancel]
  have hcorr : p ∣ m + 2 * x * t.val := by
    apply (ZMod.natCast_eq_zero_iff (m + 2 * x * t.val) p).1
    push_cast
    rw [ZMod.natCast_zmod_val]
    simpa only [mul_assoc] using ht
  have hpbracket : p ∣ m + 2 * x * t.val + t.val ^ 2 * q := by
    exact Nat.dvd_add hcorr (dvd_mul_of_dvd_right hpq (t.val ^ 2))
  let y := x + t.val * q
  have hexpand : 1 + y ^ 2 = q * (m + 2 * x * t.val + t.val ^ 2 * q) := by
    dsimp only [y]
    calc
      1 + (x + t.val * q) ^ 2 = (1 + x ^ 2) + 2 * x * t.val * q + t.val ^ 2 * q ^ 2 := by
        ring
      _ = q * m + 2 * x * t.val * q + t.val ^ 2 * q ^ 2 := by rw [hqm]
      _ = q * (m + 2 * x * t.val + t.val ^ 2 * q) := by ring
  have hydiv : p ^ (a + 1) ∣ 1 + y ^ 2 := by
    rw [hexpand]
    simpa only [q, pow_succ] using Nat.mul_dvd_mul_left q hpbracket
  let mu : Root (p ^ (a + 1)) :=
    ⟨(y : ZMod (p ^ (a + 1))), by
      have hz : ((1 + y ^ 2 : ℕ) : ZMod (p ^ (a + 1))) = 0 :=
        (ZMod.natCast_eq_zero_iff (1 + y ^ 2) (p ^ (a + 1))).2 hydiv
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at hz
      linear_combination hz⟩
  refine ⟨mu, ?_⟩
  change ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a))
      (y : ZMod (p ^ (a + 1))) = lam.1
  rw [map_natCast]
  change (y : ZMod q) = lam.1
  simp [y, x, q]

/-- The chosen elementary Hensel lift. -/
def rootLiftSucc (p a : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 0 < a) (lam : Root (p ^ a)) : Root (p ^ (a + 1)) :=
  Classical.choose (exists_root_lift_succ p a hp hp2 ha lam)

/-- The chosen lift is compatible with reduction to the preceding power. -/
@[simp] theorem cast_rootLiftSucc (p a : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 0 < a) (lam : Root (p ^ a)) :
    ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a))
        (rootLiftSucc p a hp hp2 ha lam).1 = lam.1 :=
  Classical.choose_spec (exists_root_lift_succ p a hp hp2 ha lam)

/-- A recursively compatible tower of roots, starting from a root modulo
`p`.  Entry `n` is a root modulo `p^(n+1)`. -/
def rootTower (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (base : Root p) :
    (n : ℕ) → Root (p ^ (n + 1))
  | 0 => by simpa using base
  | n + 1 => rootLiftSucc p (n + 1) hp hp2 (Nat.succ_pos n) (rootTower p hp hp2 base n)

/-- Consecutive entries of `rootTower` reduce to one another. -/
@[simp] theorem cast_rootTower_succ (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (base : Root p) (n : ℕ) :
    ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ (n + 1))) (ZMod (p ^ (n + 1)))
        (rootTower p hp hp2 base (n + 1)).1 = (rootTower p hp hp2 base n).1 := by
  exact cast_rootLiftSucc p (n + 1) hp hp2 (Nat.succ_pos n) (rootTower p hp hp2 base n)

/-- A prime congruent to one modulo four has a square root of `-1` modulo
each positive prime power. -/
theorem root_primePower_nonempty_of_mod_four_eq_one (p a : ℕ) (hp : p.Prime)
    (hp1 : p % 4 = 1) (ha : 0 < a) : Nonempty (Root (p ^ a)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hn3 : p % 4 ≠ 3 := by omega
  rcases ZMod.exists_sq_eq_neg_one_iff.mpr hn3 with ⟨x, hx⟩
  let base : Root p := ⟨x, by simpa [pow_two] using hx.symm⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  exact ⟨rootTower p hp hp2 base n⟩

end

end Selector.Modular

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorConflictRoot.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
Prime-power arithmetic for the full-conflict root-line implication.
-/

namespace Selector.ConflictRoot

open Erdos215.Selector.Modular
open Erdos215.Selector.Separation

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Explicit data at a nontrivial primary component.  The root is the
prime-power lift of a root modulo the prime; the congruence field records
the nontrivial (`1 mod 4`) case in which that lift exists. -/
structure ConflictPrimePowerData {d : ℕ} (c : PrimaryComponent d) where
  mod_four : c.p % 4 = 1
  root : Root c.q

/-- The `p`-adic order capped at the component exponent, with zero assigned
the cap.  This convention is exactly what the conflict argument needs. -/
private def cappedOrder (p a : ℕ) (z : ℤ) : ℕ :=
  if z = 0 then a else min a (padicValInt p z)

private lemma cappedOrder_le (p a : ℕ) (z : ℤ) : cappedOrder p a z ≤ a := by
  simp only [cappedOrder]
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

private lemma pow_cappedOrder_dvd {p a : ℕ} (hp : p.Prime) (z : ℤ) :
    (p : ℤ) ^ cappedOrder p a z ∣ z := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [cappedOrder]
  split_ifs with hz
  · subst z
    exact dvd_zero _
  · exact (pow_dvd_pow (p : ℤ) (min_le_right a (padicValInt p z))).trans
      (padicValInt_dvd z)

private lemma cappedOrder_eq_padicValInt_of_lt {p a : ℕ} {z : ℤ}
    (h : cappedOrder p a z < a) :
    z ≠ 0 ∧ cappedOrder p a z = padicValInt p z := by
  have hz : z ≠ 0 := by
    intro hz
    subst z
    simp [cappedOrder] at h
  refine ⟨hz, ?_⟩
  simp only [cappedOrder, if_neg hz]
  simp only [cappedOrder, if_neg hz] at h
  omega

private lemma pow_succ_cappedOrder_not_dvd {p a : ℕ} (hp : p.Prime) {z : ℤ}
    (h : cappedOrder p a z < a) :
    ¬ (p : ℤ) ^ (cappedOrder p a z + 1) ∣ z := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hz, hv⟩ := cappedOrder_eq_padicValInt_of_lt h
  rw [padicValInt_dvd_iff]
  simp [hz, hv]

private lemma pow_add_dvd_mul {p r s : ℕ} {x y : ℤ}
    (hx : (p : ℤ) ^ r ∣ x) (hy : (p : ℤ) ^ s ∣ y) :
    (p : ℤ) ^ (r + s) ∣ x * y := by
  simpa only [pow_add] using mul_dvd_mul hx hy

private lemma pow_dvd_pow_of_le (p : ℕ) {r s : ℕ} (h : r ≤ s) :
    (p : ℤ) ^ r ∣ (p : ℤ) ^ s := by
  exact pow_dvd_pow (p : ℤ) h

private lemma pow_dvd_of_le_of_pow_dvd (p : ℕ) {r s : ℕ} {z : ℤ}
    (h : r ≤ s) (hz : (p : ℤ) ^ s ∣ z) :
    (p : ℤ) ^ r ∣ z :=
  (pow_dvd_pow_of_le p h).trans hz

private lemma pow_twice_cappedOrder_succ_not_dvd_sq {p a : ℕ} (hp : p.Prime)
    {z : ℤ} (h : cappedOrder p a z < a) :
    ¬ (p : ℤ) ^ (2 * cappedOrder p a z + 1) ∣ z ^ 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hz, hv⟩ := cappedOrder_eq_padicValInt_of_lt h
  intro hdvd
  have hval : 2 * cappedOrder p a z + 1 ≤ padicValInt p (z ^ 2) :=
    (padicValInt_dvd_iff (2 * cappedOrder p a z + 1) (z ^ 2)).mp hdvd |>.resolve_left
      (pow_ne_zero 2 hz)
  have hmul : padicValInt p (z ^ 2) = 2 * padicValInt p z := by
    rw [pow_two, padicValInt.mul hz hz]
    omega
  rw [hmul, ← hv] at hval
  omega

/-- In a full conflict, the two coordinates have the same capped `p`-adic
order at every primary component.  This is the point at which the cross
term in the hypothesis is essential. -/
private lemma cappedOrders_eq_of_full_conflict {d : ℕ} (c : PrimaryComponent d)
    (A B K M : ℤ)
    (hdiv : (d : ℤ) ^ 2 ∣ A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M)) :
    cappedOrder c.p c.a A = cappedOrder c.p c.a B := by
  let r := cappedOrder c.p c.a A
  let s := cappedOrder c.p c.a B
  have hrle : r ≤ c.a := cappedOrder_le _ _ _
  have hsle : s ≤ c.a := cappedOrder_le _ _ _
  have hpD : (c.p : ℤ) ^ c.a ∣ (d : ℤ) := by
    exact_mod_cast c.q_dvd
  have hA : (c.p : ℤ) ^ r ∣ A := pow_cappedOrder_dvd c.prime A
  have hB : (c.p : ℤ) ^ s ∣ B := pow_cappedOrder_dvd c.prime B
  by_contra hne
  rcases lt_or_gt_of_ne hne with hrs | hsr
  ·
    have hra : r < c.a := lt_of_lt_of_le hrs hsle
    have hrs' : r + 1 ≤ s := hrs
    have hB' : (c.p : ℤ) ^ (r + 1) ∣ B :=
      pow_dvd_of_le_of_pow_dvd c.p hrs' hB
    have hBr : (c.p : ℤ) ^ r ∣ B :=
      pow_dvd_of_le_of_pow_dvd c.p hrs.le hB
    have hBsq : (c.p : ℤ) ^ (2 * r + 1) ∣ B ^ 2 := by
      rw [pow_two]
      rw [← show (r + 1) + r = 2 * r + 1 by omega]
      exact pow_add_dvd_mul hB' hBr
    have hcrossA : (c.p : ℤ) ^ (2 * r + 1) ∣ 2 * (d : ℤ) * (A * K) := by
      have hbig : (c.p : ℤ) ^ (c.a + r) ∣ (d : ℤ) * A :=
        pow_add_dvd_mul hpD hA
      have hsmall : (c.p : ℤ) ^ (2 * r + 1) ∣ (d : ℤ) * A :=
        pow_dvd_of_le_of_pow_dvd c.p (by omega) hbig
      simpa only [mul_assoc] using
        (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hsmall K) 2)
    have hcrossB : (c.p : ℤ) ^ (2 * r + 1) ∣ 2 * (d : ℤ) * (B * M) := by
      have hbig : (c.p : ℤ) ^ (c.a + s) ∣ (d : ℤ) * B :=
        pow_add_dvd_mul hpD hB
      have hsmall : (c.p : ℤ) ^ (2 * r + 1) ∣ (d : ℤ) * B :=
        pow_dvd_of_le_of_pow_dvd c.p (by omega) hbig
      simpa only [mul_assoc] using
        (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hsmall M) 2)
    have hcross : (c.p : ℤ) ^ (2 * r + 1) ∣
        2 * (d : ℤ) * (A * K + B * M) := by
      simpa only [mul_add] using dvd_add hcrossA hcrossB
    have hdSq : (c.p : ℤ) ^ (2 * r + 1) ∣ (d : ℤ) ^ 2 := by
      have hbig : (c.p : ℤ) ^ (c.a + c.a) ∣ (d : ℤ) ^ 2 := by
        simpa only [pow_two] using pow_add_dvd_mul hpD hpD
      exact pow_dvd_of_le_of_pow_dvd c.p (by omega) hbig
    have hE : (c.p : ℤ) ^ (2 * r + 1) ∣
        A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) := hdSq.trans hdiv
    have hAsq : (c.p : ℤ) ^ (2 * r + 1) ∣ A ^ 2 := by
      rcases hE with ⟨u, hu⟩
      rcases hcross with ⟨v, hv⟩
      rcases hBsq with ⟨w, hw⟩
      refine ⟨u - v - w, ?_⟩
      linear_combination hu - hv - hw
    exact pow_twice_cappedOrder_succ_not_dvd_sq c.prime hra hAsq
  ·
    have hsa : s < c.a := lt_of_lt_of_le hsr hrle
    have hsr' : s + 1 ≤ r := hsr
    have hA' : (c.p : ℤ) ^ (s + 1) ∣ A :=
      pow_dvd_of_le_of_pow_dvd c.p hsr' hA
    have hAs : (c.p : ℤ) ^ s ∣ A :=
      pow_dvd_of_le_of_pow_dvd c.p hsr.le hA
    have hAsq : (c.p : ℤ) ^ (2 * s + 1) ∣ A ^ 2 := by
      rw [pow_two]
      rw [← show (s + 1) + s = 2 * s + 1 by omega]
      exact pow_add_dvd_mul hA' hAs
    have hcrossA : (c.p : ℤ) ^ (2 * s + 1) ∣ 2 * (d : ℤ) * (A * K) := by
      have hbig : (c.p : ℤ) ^ (c.a + r) ∣ (d : ℤ) * A :=
        pow_add_dvd_mul hpD hA
      have hsmall : (c.p : ℤ) ^ (2 * s + 1) ∣ (d : ℤ) * A :=
        pow_dvd_of_le_of_pow_dvd c.p (by omega) hbig
      simpa only [mul_assoc] using
        (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hsmall K) 2)
    have hcrossB : (c.p : ℤ) ^ (2 * s + 1) ∣ 2 * (d : ℤ) * (B * M) := by
      have hbig : (c.p : ℤ) ^ (c.a + s) ∣ (d : ℤ) * B :=
        pow_add_dvd_mul hpD hB
      have hsmall : (c.p : ℤ) ^ (2 * s + 1) ∣ (d : ℤ) * B :=
        pow_dvd_of_le_of_pow_dvd c.p (by omega) hbig
      simpa only [mul_assoc] using
        (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hsmall M) 2)
    have hcross : (c.p : ℤ) ^ (2 * s + 1) ∣
        2 * (d : ℤ) * (A * K + B * M) := by
      simpa only [mul_add] using dvd_add hcrossA hcrossB
    have hdSq : (c.p : ℤ) ^ (2 * s + 1) ∣ (d : ℤ) ^ 2 := by
      have hbig : (c.p : ℤ) ^ (c.a + c.a) ∣ (d : ℤ) ^ 2 := by
        simpa only [pow_two] using pow_add_dvd_mul hpD hpD
      exact pow_dvd_of_le_of_pow_dvd c.p (by omega) hbig
    have hE : (c.p : ℤ) ^ (2 * s + 1) ∣
        A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) := hdSq.trans hdiv
    have hBsq : (c.p : ℤ) ^ (2 * s + 1) ∣ B ^ 2 := by
      rcases hE with ⟨u, hu⟩
      rcases hcross with ⟨v, hv⟩
      rcases hAsq with ⟨w, hw⟩
      refine ⟨u - v - w, ?_⟩
      linear_combination hu - hv - hw
    exact pow_twice_cappedOrder_succ_not_dvd_sq c.prime hsa hBsq

private lemma component_coprime_two {d : ℕ} (c : PrimaryComponent d)
    (w : ConflictPrimePowerData c) : Nat.Coprime c.p 2 := by
  apply c.prime.coprime_iff_not_dvd.mpr
  intro hp2
  have hle : c.p ≤ 2 := Nat.le_of_dvd (by omega) hp2
  have heq : c.p = 2 := Nat.le_antisymm hle c.prime.two_le
  have := w.mod_four
  rw [heq] at this
  norm_num at this

/-- The local full-conflict implication at a single primary component. -/
theorem exists_component_root_line {d : ℕ} (c : PrimaryComponent d)
    (w : ConflictPrimePowerData c) (A B K M : ℤ)
    (hdiv : (d : ℤ) ^ 2 ∣ A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M)) :
    ∃ lam : Root c.q,
      (B : ZMod c.q) = (lam : ZMod c.q) * (A : ZMod c.q) := by
  let r := cappedOrder c.p c.a A
  have hrle : r ≤ c.a := cappedOrder_le _ _ _
  have horders := cappedOrders_eq_of_full_conflict c A B K M hdiv
  have hA : (c.p : ℤ) ^ r ∣ A := pow_cappedOrder_dvd c.prime A
  have hB : (c.p : ℤ) ^ r ∣ B := by
    change (c.p : ℤ) ^ cappedOrder c.p c.a A ∣ B
    rw [horders]
    exact pow_cappedOrder_dvd c.prime B
  have hqcast : (c.q : ℤ) = (c.p : ℤ) ^ c.a := by
    simp only [PrimaryComponent.q, Int.natCast_pow]
  letI : NeZero c.q := ⟨c.q_ne_zero⟩
  by_cases hra : r = c.a
  · have hAq : (c.q : ℤ) ∣ A := by
      rw [hqcast, ← hra]
      exact hA
    have hBq : (c.q : ℤ) ∣ B := by
      rw [hqcast, ← hra]
      exact hB
    refine ⟨w.root, ?_⟩
    have hAz : (A : ZMod c.q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd A c.q).mpr hAq
    have hBz : (B : ZMod c.q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd B c.q).mpr hBq
    rw [hAz, hBz, mul_zero]
  · have hra' : r < c.a := lt_of_le_of_ne hrle hra
    have hBord : cappedOrder c.p c.a B = r := horders.symm
    have hBsucc : ¬ (c.p : ℤ) ^ (r + 1) ∣ B := by
      simpa only [hBord] using
        (pow_succ_cappedOrder_not_dvd c.prime
          (show cappedOrder c.p c.a B < c.a by simpa only [hBord] using hra'))
    let L : ℤ := ZMod.val w.root.1
    let R : ℤ := rootQuotient w.root
    let X : ℤ := B - L * A
    let Y : ℤ := B + L * A
    have hLcast : (L : ZMod c.q) = w.root.1 := by
      dsimp only [L]
      simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val w.root.1
    have hroot : (c.p : ℤ) ^ c.a * R = 1 + L ^ 2 := by
      dsimp only [R, L, PrimaryComponent.q] at ⊢
      exact_mod_cast mul_rootQuotient c.q_ne_zero w.root
    have hfactor : (d : ℤ) = (c.p : ℤ) ^ c.a * c.D := by
      exact_mod_cast c.factor_q
    have hZ : (c.p : ℤ) ^ r ∣
        R * A ^ 2 + 2 * c.D * (A * K + B * M) := by
      have hRA : (c.p : ℤ) ^ r ∣ R * A ^ 2 := by
        simpa only [pow_two] using dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hA A) R
      have hlin : (c.p : ℤ) ^ r ∣ A * K + B * M :=
        dvd_add (dvd_mul_of_dvd_left hA K) (dvd_mul_of_dvd_left hB M)
      exact dvd_add hRA (dvd_mul_of_dvd_right hlin (2 * c.D))
    have hcorr : (c.p : ℤ) ^ (c.a + r) ∣
        (c.p : ℤ) ^ c.a *
          (R * A ^ 2 + 2 * c.D * (A * K + B * M)) :=
      pow_add_dvd_mul (dvd_refl _) hZ
    have hE : (c.p : ℤ) ^ (c.a + r) ∣
        A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) := by
      have hpD : (c.p : ℤ) ^ c.a ∣ (d : ℤ) := by exact_mod_cast c.q_dvd
      have hdsq : (c.p : ℤ) ^ (c.a + c.a) ∣ (d : ℤ) ^ 2 := by
        simpa only [pow_two] using pow_add_dvd_mul hpD hpD
      exact (pow_dvd_of_le_of_pow_dvd c.p (by omega) hdsq).trans hdiv
    have hXY : (c.p : ℤ) ^ (c.a + r) ∣ X * Y := by
      rcases hE with ⟨u, hu⟩
      rcases hcorr with ⟨v, hv⟩
      refine ⟨u - v, ?_⟩
      dsimp only [X, Y]
      rw [hfactor] at hu
      linear_combination hu - hv + A ^ 2 * hroot
    have hXr : (c.p : ℤ) ^ r ∣ X :=
      dvd_sub hB (dvd_mul_of_dvd_right hA L)
    have hYr : (c.p : ℤ) ^ r ∣ Y :=
      dvd_add hB (dvd_mul_of_dvd_right hA L)
    by_cases hX0 : X = 0
    · refine ⟨w.root, ?_⟩
      dsimp only [X] at hX0
      rw [sub_eq_zero] at hX0
      have hc := congrArg (fun z : ℤ ↦ (z : ZMod c.q)) hX0
      push_cast at hc
      simpa only [hLcast] using hc
    by_cases hY0 : Y = 0
    · refine ⟨⟨-w.root.1, by rw [neg_sq, w.root.property]⟩, ?_⟩
      dsimp only [Y] at hY0
      have hneg : B = -L * A := by linear_combination hY0
      have hc := congrArg (fun z : ℤ ↦ (z : ZMod c.q)) hneg
      push_cast at hc
      simpa only [hLcast] using hc
    letI : Fact c.p.Prime := ⟨c.prime⟩
    have hvalXY : c.a + r ≤ padicValInt c.p X + padicValInt c.p Y := by
      have hv := (padicValInt_dvd_iff (c.a + r) (X * Y)).mp hXY
      rw [padicValInt.mul hX0 hY0] at hv
      exact hv.resolve_left (mul_ne_zero hX0 hY0)
    have hvalX : r ≤ padicValInt c.p X :=
      ((padicValInt_dvd_iff r X).mp hXr).resolve_left hX0
    have hvalY : r ≤ padicValInt c.p Y :=
      ((padicValInt_dvd_iff r Y).mp hYr).resolve_left hY0
    have hnotBoth : ¬ (r + 1 ≤ padicValInt c.p X ∧
        r + 1 ≤ padicValInt c.p Y) := by
      rintro ⟨hx, hy⟩
      have hxdiv : (c.p : ℤ) ^ (r + 1) ∣ X :=
        (padicValInt_dvd_iff (r + 1) X).mpr (Or.inr hx)
      have hydiv : (c.p : ℤ) ^ (r + 1) ∣ Y :=
        (padicValInt_dvd_iff (r + 1) Y).mpr (Or.inr hy)
      have h2B : (c.p : ℤ) ^ (r + 1) ∣ 2 * B := by
        rcases hxdiv with ⟨u, hu⟩
        rcases hydiv with ⟨v, hv⟩
        refine ⟨u + v, ?_⟩
        dsimp only [X, Y] at hu hv
        linear_combination hu + hv
      have hcopNat : Nat.Coprime (c.p ^ (r + 1)) 2 :=
        (component_coprime_two c w).pow_left _
      have hcop : IsCoprime ((c.p : ℤ) ^ (r + 1)) (2 : ℤ) := by
        exact_mod_cast hcopNat
      exact hBsucc (hcop.dvd_of_dvd_mul_left h2B)
    rcases lt_or_ge (padicValInt c.p X) (r + 1) with hxlt | hxhigh
    · have hxle : padicValInt c.p X ≤ r := by omega
      have hx : padicValInt c.p X = r := le_antisymm hxle hvalX
      have hy : c.a ≤ padicValInt c.p Y := by omega
      have hydiv : (c.q : ℤ) ∣ Y := by
        rw [hqcast]
        exact (padicValInt_dvd_iff c.a Y).mpr (Or.inr hy)
      refine ⟨⟨-w.root.1, by rw [neg_sq, w.root.property]⟩, ?_⟩
      have heq := ((ZMod.intCast_eq_intCast_iff_dvd_sub
        ((-(ZMod.val w.root.1 : ℤ)) * A) B c.q).mpr (by
          dsimp only [Y, L] at hydiv
          simpa only [sub_neg_eq_add, neg_mul] using hydiv)).symm
      calc
        (B : ZMod c.q) = (((-(ZMod.val w.root.1 : ℤ)) * A : ℤ) : ZMod c.q) := heq
        _ = (-w.root.1) * (A : ZMod c.q) := by
          push_cast
          rw [ZMod.natCast_zmod_val w.root.1]

    · have hyNot : ¬ r + 1 ≤ padicValInt c.p Y := by
        intro hy
        exact hnotBoth ⟨hxhigh, hy⟩
      have hyle : padicValInt c.p Y ≤ r := by omega
      have hy : padicValInt c.p Y = r := le_antisymm hyle hvalY
      have hx : c.a ≤ padicValInt c.p X := by omega
      have hxdiv : (c.q : ℤ) ∣ X := by
        rw [hqcast]
        exact (padicValInt_dvd_iff c.a X).mpr (Or.inr hx)
      refine ⟨w.root, ?_⟩
      have heq := ((ZMod.intCast_eq_intCast_iff_dvd_sub
        ((ZMod.val w.root.1 : ℤ) * A) B c.q).mpr (by
          dsimp only [X, L] at hxdiv
          exact hxdiv)).symm
      calc
        (B : ZMod c.q) = ((((ZMod.val w.root.1 : ℤ)) * A : ℤ) : ZMod c.q) := heq
        _ = w.root.1 * (A : ZMod c.q) := by
          push_cast
          rw [ZMod.natCast_zmod_val w.root.1]

/-- Assemble independently selected local roots by the list CRT. -/
private theorem exists_global_root_of_component_roots {d : ℕ}
    (C : CompleteComponents d) (hd : d ≠ 0)
    (roots : ∀ c ∈ C.components, Root c.q) :
    ∃ lam : Root d, ∀ c, ∀ hc : c ∈ C.components,
      c.reduce lam.1 = (roots c hc : ZMod c.q) := by
  classical
  let residue : PrimaryComponent d → ℕ := fun c ↦
    if hc : c ∈ C.components then ZMod.val (roots c hc).1 else 0
  let z := Nat.chineseRemainderOfList residue
    (fun c : PrimaryComponent d ↦ c.q) C.components C.pairwise
  have hz (c : PrimaryComponent d) (hc : c ∈ C.components) :
      c.reduce ((z : ℕ) : ZMod d) = (roots c hc : ZMod c.q) := by
    letI : NeZero c.q := ⟨c.q_ne_zero⟩
    have hmod : (z : ℕ) ≡ residue c [MOD c.q] := z.property c hc
    have hcast : ((z : ℕ) : ZMod c.q) = (residue c : ZMod c.q) :=
      (ZMod.natCast_eq_natCast_iff (z : ℕ) (residue c) c.q).mpr hmod
    rw [PrimaryComponent.reduce_natCast]
    rw [hcast]
    dsimp only [residue]
    simp only [dif_pos hc]
    exact ZMod.natCast_zmod_val (roots c hc).1
  let x : ZMod d := (z : ℕ)
  have hxroot : x ^ 2 = -1 := by
    apply C.eq_of_reduce_eq hd
    intro c hc
    rw [map_pow, map_neg, map_one]
    change (c.reduce x) ^ 2 = (-1 : ZMod c.q)
    rw [show c.reduce x = (roots c hc : ZMod c.q) by exact hz c hc]
    exact (roots c hc).property
  refine ⟨⟨x, hxroot⟩, ?_⟩
  intro c hc
  exact hz c hc

/-- Complete primary components turn their local full-conflict root lines
into one root line modulo the original denominator. -/
theorem conflictRootLineProperty_of_complete_data {d : ℕ} (hd : d ≠ 0)
    (C : CompleteComponents d)
    (data : ∀ c ∈ C.components, ConflictPrimePowerData c) :
    ConflictRootLineProperty d := by
  intro A B K M hdiv
  have hlocal : ∀ c ∈ C.components, ∃ lam : Root c.q,
      (B : ZMod c.q) = (lam : ZMod c.q) * (A : ZMod c.q) := by
    intro c hc
    exact exists_component_root_line c (data c hc) A B K M hdiv
  let roots : ∀ c ∈ C.components, Root c.q := fun c hc ↦
    Classical.choose (hlocal c hc)
  have hlocal_spec (c : PrimaryComponent d) (hc : c ∈ C.components) :
      (B : ZMod c.q) = (roots c hc : ZMod c.q) * (A : ZMod c.q) :=
    Classical.choose_spec (hlocal c hc)
  obtain ⟨lam, hlam⟩ := exists_global_root_of_component_roots C hd roots
  refine ⟨lam, ?_⟩
  apply C.eq_of_reduce_eq hd
  intro c hc
  rw [PrimaryComponent.reduce_intCast, map_mul, PrimaryComponent.reduce_intCast]
  rw [hlam c hc]
  exact hlocal_spec c hc

/-- Construct the explicit component data from the congruence `p = 1 mod
4`, using the elementary prime-power Hensel tower. -/
def primePowerDataOfModFour {d : ℕ} (c : PrimaryComponent d)
    (hp1 : c.p % 4 = 1) : ConflictPrimePowerData c where
  mod_four := hp1
  root := Classical.choice
    (root_primePower_nonempty_of_mod_four_eq_one c.p c.a c.prime hp1 c.exp_pos)

/-- Public form: for a complete factorization all of whose component
primes are `1 mod 4`, the corrected full-conflict root-line property holds. -/
theorem conflictRootLineProperty_of_complete {d : ℕ} (hd : d ≠ 0)
    (C : CompleteComponents d)
    (hp1 : ∀ c ∈ C.components, c.p % 4 = 1) :
    ConflictRootLineProperty d :=
  conflictRootLineProperty_of_complete_data hd C
    (fun c hc ↦ primePowerDataOfModFour c (hp1 c hc))

end

end Selector.ConflictRoot

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorComplete.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
The canonical complete list of primary components of a nonzero denominator.

For every prime in `d.primeFactors` we retain its full power in `d`; its
complement is `ordCompl[p] d`.  Mathlib's factorization product and pairwise
coprimality theorems then give precisely the `CompleteComponents` package
used by the selector reconstruction.
-/

namespace Selector.Complete

open Erdos215.Selector.Modular
open Erdos215.Selector.Final
open Erdos215.Selector.Separation

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The full primary component of `d` indexed by a prime factor of `d`. -/
def canonicalPrimaryComponent (d : ℕ) (hd : d ≠ 0)
    (p : d.primeFactors) : PrimaryComponent d where
  p := p
  a := d.factorization p
  D := ordCompl[(p : ℕ)] d
  prime := Nat.prime_of_mem_primeFactors p.2
  exp_pos := (Nat.prime_of_mem_primeFactors p.2).factorization_pos_of_dvd hd
    (Nat.dvd_of_mem_primeFactors p.2)
  factor := (Nat.ordProj_mul_ordCompl_eq_self d p).symm
  coprime := (Nat.coprime_ordCompl (Nat.prime_of_mem_primeFactors p.2) hd).pow_left _

@[simp] theorem canonicalPrimaryComponent_q (d : ℕ) (hd : d ≠ 0)
    (p : d.primeFactors) :
    (canonicalPrimaryComponent d hd p).q =
      (p : ℕ) ^ d.factorization p := rfl

/-- The primary components, in the canonical order inherited from the finite
set of prime factors. -/
def canonicalComponentList (d : ℕ) (hd : d ≠ 0) :
    List (PrimaryComponent d) :=
  (Finset.univ : Finset d.primeFactors).toList.map
    (canonicalPrimaryComponent d hd)

/-- Every nonzero natural has a canonical complete primary decomposition. -/
def canonicalCompleteComponents (d : ℕ) (hd : d ≠ 0) :
    CompleteComponents d where
  components := canonicalComponentList d hd
  pairwise := by
    rw [canonicalComponentList, List.pairwise_map]
    apply List.Nodup.pairwise_of_forall_ne (Finset.nodup_toList _)
    intro p hp q hq hpq
    simpa only [canonicalPrimaryComponent_q] using
      d.pairwise_coprime_pow_primeFactors_factorization hpq
  product_eq := by
    simp only [canonicalComponentList, List.map_map, Finset.prod_map_toList,
      Function.comp_apply, canonicalPrimaryComponent_q]
    exact (Nat.prod_primeFactors_coe_pow_factorization hd).symm

/-- Membership in the canonical list remembers the prime-factor index from
which the component was built. -/
theorem mem_canonicalComponentList_iff {d : ℕ} {hd : d ≠ 0}
    (c : PrimaryComponent d) :
    c ∈ canonicalComponentList d hd ↔
      ∃ p : d.primeFactors, canonicalPrimaryComponent d hd p = c := by
  simp [canonicalComponentList]

/-- A hypothesis on all prime divisors of `d` transfers to every prime in
the canonical primary decomposition. -/
theorem canonical_component_mod_four_eq_one {d : ℕ} (hd : d ≠ 0)
    (hp1 : ∀ p : ℕ, p.Prime → p ∣ d → p % 4 = 1)
    (c : PrimaryComponent d)
    (hc : c ∈ (canonicalCompleteComponents d hd).components) :
    c.p % 4 = 1 := by
  change c ∈ canonicalComponentList d hd at hc
  obtain ⟨p, rfl⟩ := (mem_canonicalComponentList_iff
    (hd := hd) c).mp hc
  exact hp1 p (Nat.prime_of_mem_primeFactors p.2)
    (Nat.dvd_of_mem_primeFactors p.2)

/-- Complete `1 mod 4` primary data in particular supplies a global root of
`-1`.  This public wrapper avoids exposing the private CRT implementation in
`SelectorConflictRoot`: apply its full-conflict conclusion to the zero
quadruple. -/
theorem root_nonempty_of_complete {d : ℕ} (hd : d ≠ 0)
    (C : CompleteComponents d)
    (hp1 : ∀ c ∈ C.components, c.p % 4 = 1) : Nonempty (Root d) := by
  have hrootLine :=
    ConflictRoot.conflictRootLineProperty_of_complete hd C hp1
  obtain ⟨lam, _⟩ := hrootLine 0 0 0 0 (by simp)
  exact ⟨lam⟩

/-- The canonical decomposition supplies the full-conflict root-line
property when every prime divisor is `1 mod 4`. -/
theorem canonical_conflictRootLineProperty {d : ℕ} (hd : d ≠ 0)
    (hp1 : ∀ p : ℕ, p.Prime → p ∣ d → p % 4 = 1) :
    ConflictRootLineProperty d :=
  ConflictRoot.conflictRootLineProperty_of_complete hd
    (canonicalCompleteComponents d hd)
    (canonical_component_mod_four_eq_one hd hp1)

/-- Canonical global root existence for a pure nontrivial denominator. -/
theorem canonical_root_nonempty {d : ℕ} (hd : d ≠ 0)
    (hp1 : ∀ p : ℕ, p.Prime → p ∣ d → p % 4 = 1) :
    Nonempty (Root d) :=
  root_nonempty_of_complete hd (canonicalCompleteComponents d hd)
    (canonical_component_mod_four_eq_one hd hp1)

end

end Selector.Complete

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorFactorization.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
Canonical factorization of a denominator into the prime-power factors that are
`1 mod 4` and the complementary (anisotropic) factors.
-/

namespace Selector

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The full factorization of `d`, restricted to primes that are `1 mod 4`. -/
def nontrivialFactorization (d : ℕ) : ℕ →₀ ℕ :=
  Finsupp.filter (fun p ↦ p % 4 = 1) d.factorization

/-- The complementary full factorization of `d`. -/
def trivialFactorization (d : ℕ) : ℕ →₀ ℕ :=
  Finsupp.filter (fun p ↦ p % 4 ≠ 1) d.factorization

/-- Product of the full prime-power factors of `d` whose primes are `1 mod 4`. -/
def nontrivialPart (d : ℕ) : ℕ :=
  (nontrivialFactorization d).prod fun p e ↦ p ^ e

/-- Product of the complementary full prime-power factors of `d`. -/
def trivialPart (d : ℕ) : ℕ :=
  (trivialFactorization d).prod fun p e ↦ p ^ e

lemma nontrivialFactorization_le (d : ℕ) :
    nontrivialFactorization d ≤ d.factorization := by
  intro p
  simp only [nontrivialFactorization, Finsupp.filter_apply]
  split <;> simp_all

lemma trivialFactorization_le (d : ℕ) :
    trivialFactorization d ≤ d.factorization := by
  intro p
  simp only [trivialFactorization, Finsupp.filter_apply]
  split <;> simp_all

@[simp] theorem factorization_nontrivialPart (d : ℕ) :
    (nontrivialPart d).factorization = nontrivialFactorization d := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (nontrivialFactorization_le d)

@[simp] theorem factorization_trivialPart (d : ℕ) :
    (trivialPart d).factorization = trivialFactorization d := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (trivialFactorization_le d)

/-- The two products partition all prime-power factors of a nonzero denominator. -/
theorem nontrivialPart_mul_trivialPart (d : ℕ) (hd : d ≠ 0) :
    nontrivialPart d * trivialPart d = d := by
  rw [nontrivialPart, trivialPart,
    ← Finsupp.prod_add_index' (fun _ ↦ by simp) (fun p a b ↦ Nat.pow_add p a b)]
  rw [nontrivialFactorization, trivialFactorization,
    Finsupp.filter_add_filter_not]
  exact Nat.prod_factorization_pow_eq_self hd

lemma nontrivialPart_ne_zero (d : ℕ) (hd : d ≠ 0) : nontrivialPart d ≠ 0 := by
  intro h
  have hprod := nontrivialPart_mul_trivialPart d hd
  rw [h, zero_mul] at hprod
  exact hd hprod.symm

lemma trivialPart_ne_zero (d : ℕ) (hd : d ≠ 0) : trivialPart d ≠ 0 := by
  intro h
  have hprod := nontrivialPart_mul_trivialPart d hd
  rw [h, mul_zero] at hprod
  exact hd hprod.symm

@[simp] theorem factorization_nontrivialPart_apply (d q : ℕ) :
    (nontrivialPart d).factorization q =
      if q % 4 = 1 then d.factorization q else 0 := by
  rw [factorization_nontrivialPart, nontrivialFactorization, Finsupp.filter_apply]

@[simp] theorem factorization_trivialPart_apply (d q : ℕ) :
    (trivialPart d).factorization q =
      if q % 4 ≠ 1 then d.factorization q else 0 := by
  rw [factorization_trivialPart, trivialFactorization, Finsupp.filter_apply]

lemma prime_mod_four_ne_one_iff (q : ℕ) (hq : q.Prime) :
    q % 4 ≠ 1 ↔ q = 2 ∨ q % 4 = 3 := by
  constructor
  · intro hn1
    rcases hq.eq_two_or_odd with rfl | hodd
    · exact Or.inl rfl
    · right
      have hpar : q % 4 % 2 = 1 := by
        rw [Nat.mod_mod_of_dvd q (by norm_num : 2 ∣ 4)]
        exact hodd
      have hlt : q % 4 < 4 := Nat.mod_lt _ (by omega)
      omega
  · rintro (rfl | h3)
    · norm_num
    · omega

theorem prime_dvd_nontrivialPart_iff (d q : ℕ) (hd : d ≠ 0) (hq : q.Prime) :
    q ∣ nontrivialPart d ↔ q ∣ d ∧ q % 4 = 1 := by
  rw [hq.dvd_iff_one_le_factorization (nontrivialPart_ne_zero d hd)]
  simp only [factorization_nontrivialPart_apply]
  by_cases hq1 : q % 4 = 1
  · simp [hq1, hq.dvd_iff_one_le_factorization hd]
  · simp [hq1]

theorem prime_dvd_trivialPart_iff (d q : ℕ) (hd : d ≠ 0) (hq : q.Prime) :
    q ∣ trivialPart d ↔ q ∣ d ∧ (q = 2 ∨ q % 4 = 3) := by
  rw [hq.dvd_iff_one_le_factorization (trivialPart_ne_zero d hd)]
  simp only [factorization_trivialPart_apply]
  rw [← prime_mod_four_ne_one_iff q hq]
  by_cases hq1 : q % 4 ≠ 1
  · simp [hq1, hq.dvd_iff_one_le_factorization hd]
  · simp [hq1]

@[simp] theorem nontrivialPart_one : nontrivialPart 1 = 1 := by
  simp only [nontrivialPart, nontrivialFactorization, Nat.factorization_one,
    Finsupp.filter_zero, Finsupp.prod_zero_index]

@[simp] theorem trivialPart_one : trivialPart 1 = 1 := by
  simp only [trivialPart, trivialFactorization, Nat.factorization_one,
    Finsupp.filter_zero, Finsupp.prod_zero_index]

/-! ### Rigidity of the norm at the trivial denominator -/

def SquareNormRigid (Q : ℕ) : Prop :=
  ∀ A B : ℤ, (Q : ℤ) ^ 2 ∣ A ^ 2 + B ^ 2 → (Q : ℤ) ∣ A ∧ (Q : ℤ) ∣ B

@[simp] theorem squareNormRigid_one : SquareNormRigid 1 := by
  intro A B _
  simp

theorem SquareNormRigid.mul {m n : ℕ} (hmn : m.Coprime n)
    (hm : SquareNormRigid m) (hn : SquareNormRigid n) :
    SquareNormRigid (m * n) := by
  intro A B hnorm
  have hmSq : (m : ℤ) ^ 2 ∣ ((m * n : ℕ) : ℤ) ^ 2 := by
    refine ⟨(n : ℤ) ^ 2, ?_⟩
    push_cast
    ring
  have hnSq : (n : ℤ) ^ 2 ∣ ((m * n : ℕ) : ℤ) ^ 2 := by
    refine ⟨(m : ℤ) ^ 2, ?_⟩
    push_cast
    ring
  rcases hm A B (hmSq.trans hnorm) with ⟨hmA, hmB⟩
  rcases hn A B (hnSq.trans hnorm) with ⟨hnA, hnB⟩
  constructor
  · simpa only [Int.natCast_mul] using hmn.isCoprime.mul_dvd hmA hnA
  · simpa only [Int.natCast_mul] using hmn.isCoprime.mul_dvd hmB hnB

theorem squareNormRigid_two : SquareNormRigid 2 := by
  intro A B hnorm
  rcases Int.even_or_odd A with hAe | hAo
  · have hA : (2 : ℤ) ∣ A := even_iff_two_dvd.mp hAe
    rcases Int.even_or_odd B with hBe | hBo
    · exact ⟨hA, even_iff_two_dvd.mp hBe⟩
    · exfalso
      rcases hAe with ⟨a, rfl⟩
      rcases hBo with ⟨b, rfl⟩
      rcases hnorm with ⟨z, hz⟩
      norm_num at hz
      ring_nf at hz
      omega
  · rcases Int.even_or_odd B with hBe | hBo
    · exfalso
      rcases hAo with ⟨a, rfl⟩
      rcases hBe with ⟨b, rfl⟩
      rcases hnorm with ⟨z, hz⟩
      norm_num at hz
      ring_nf at hz
      omega
    · exfalso
      rcases hAo with ⟨a, rfl⟩
      rcases hBo with ⟨b, rfl⟩
      rcases hnorm with ⟨z, hz⟩
      norm_num at hz
      ring_nf at hz
      omega

theorem squareNormRigid_prime_mod_four_eq_three (q : ℕ) (hq : q.Prime)
    (hq3 : q % 4 = 3) : SquareNormRigid q := by
  letI : Fact q.Prime := ⟨hq⟩
  intro A B hnorm
  have hqSq : (q : ℤ) ∣ (q : ℤ) ^ 2 := dvd_pow_self (q : ℤ) (by omega)
  have hqnorm : (q : ℤ) ∣ A ^ 2 + B ^ 2 := hqSq.trans hnorm
  have hzero : ((A ^ 2 + B ^ 2 : ℤ) : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 hqnorm
  push_cast at hzero
  rcases normAnisotropic_of_prime_mod_four_eq_three q hq3 (A : ZMod q) (B : ZMod q)
      hzero with ⟨hA, hB⟩
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd A q).mp hA,
    (ZMod.intCast_zmod_eq_zero_iff_dvd B q).mp hB⟩

theorem squareNormRigid_trivial_prime (q : ℕ) (hq : q.Prime)
    (htriv : q = 2 ∨ q % 4 = 3) : SquareNormRigid q := by
  rcases htriv with rfl | hq3
  · exact squareNormRigid_two
  · exact squareNormRigid_prime_mod_four_eq_three q hq hq3

theorem squareNormRigid_trivial_prime_pow (q e : ℕ) (hq : q.Prime)
    (htriv : q = 2 ∨ q % 4 = 3) : SquareNormRigid (q ^ e) := by
  induction e with
  | zero => simpa using squareNormRigid_one
  | succ e ih =>
      intro A B hnorm
      have hqSqDvd : (q : ℤ) ^ 2 ∣ ((q ^ (e + 1) : ℕ) : ℤ) ^ 2 := by
        refine ⟨((q ^ e : ℕ) : ℤ) ^ 2, ?_⟩
        push_cast
        rw [pow_succ]
        ring
      rcases squareNormRigid_trivial_prime q hq htriv A B (hqSqDvd.trans hnorm) with
        ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      have hcancel : ((q ^ e : ℕ) : ℤ) ^ 2 ∣ a ^ 2 + b ^ 2 := by
        have hnorm' : (q : ℤ) ^ 2 * ((q ^ e : ℕ) : ℤ) ^ 2 ∣
            (q : ℤ) ^ 2 * (a ^ 2 + b ^ 2) := by
          rw [ha, hb] at hnorm
          convert hnorm using 1 <;> push_cast <;> rw [pow_succ] <;> ring
        exact (Int.mul_dvd_mul_iff_left
          (pow_ne_zero 2 (by exact_mod_cast hq.ne_zero : (q : ℤ) ≠ 0))).mp hnorm'
      rcases ih a b hcancel with ⟨hae, hbe⟩
      rw [ha, hb]
      constructor
      · simpa only [Int.natCast_pow, pow_succ, Int.natCast_mul, mul_comm] using
          mul_dvd_mul_left (q : ℤ) hae
      · simpa only [Int.natCast_pow, pow_succ, Int.natCast_mul, mul_comm] using
          mul_dvd_mul_left (q : ℤ) hbe

theorem squareNormRigid_finset_prod {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → ℕ)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i).Coprime (f j))
    (hrigid : ∀ i ∈ s, SquareNormRigid (f i)) :
    SquareNormRigid (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using squareNormRigid_one
  | @insert i s his ih =>
      have hiCop : (f i).Coprime (∏ j ∈ s, f j) := by
        rw [Nat.coprime_prod_right_iff]
        intro j hj
        exact hcop i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
          (fun hij ↦ his (hij ▸ hj))
      have hsRigid : SquareNormRigid (∏ j ∈ s, f j) := by
        apply ih
        · intro a ha b hb hab
          exact hcop a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
        · intro a ha
          exact hrigid a (Finset.mem_insert_of_mem ha)
      simpa [his] using SquareNormRigid.mul hiCop
        (hrigid i (Finset.mem_insert_self i s)) hsRigid

theorem squareNormRigid_trivialPart (d : ℕ) (hd : d ≠ 0) :
    SquareNormRigid (trivialPart d) := by
  let Q := trivialPart d
  have hQ : Q ≠ 0 := trivialPart_ne_zero d hd
  have hprod : Q = ∏ q ∈ Q.primeFactors, q ^ Q.factorization q :=
    Nat.prod_primeFactors_pow_factorization hQ
  change SquareNormRigid Q
  rw [hprod]
  apply squareNormRigid_finset_prod
  · intro p hp q hq hpq
    exact Nat.coprime_pow_primes _ _
      (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq) hpq
  · intro q hq
    have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqDvd : q ∣ trivialPart d := Nat.dvd_of_mem_primeFactors hq
    exact squareNormRigid_trivial_prime_pow q (Q.factorization q) hqPrime
      ((prime_dvd_trivialPart_iff d q hd hqPrime).mp hqDvd).2

/-! ### Reduced rational differences -/

end

end Selector

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorCompleteFactorization.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
The canonical complete list of primary components of a nonzero denominator.

This is the low-level factorization package used by the final selector
extension.  For every `p ∈ d.primeFactors` it records the full factor
`p ^ d.factorization p`, with complementary factor `ordCompl[p] d`.
-/

namespace Selector

open Modular

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The full primary component of `d` belonging to the prime factor `p`. -/
def completePrimaryComponent (d : ℕ) (hd : d ≠ 0)
    (p : d.primeFactors) : PrimaryComponent d where
  p := p
  a := d.factorization p
  D := ordCompl[(p : ℕ)] d
  prime := Nat.prime_of_mem_primeFactors p.2
  exp_pos := (Nat.prime_of_mem_primeFactors p.2).factorization_pos_of_dvd hd
    (Nat.dvd_of_mem_primeFactors p.2)
  factor := (Nat.ordProj_mul_ordCompl_eq_self d p).symm
  coprime := (Nat.coprime_ordCompl
    (Nat.prime_of_mem_primeFactors p.2) hd).pow_left _

@[simp] theorem completePrimaryComponent_p (d : ℕ) (hd : d ≠ 0)
    (p : d.primeFactors) :
    (completePrimaryComponent d hd p).p = p := rfl

@[simp] theorem completePrimaryComponent_a (d : ℕ) (hd : d ≠ 0)
    (p : d.primeFactors) :
    (completePrimaryComponent d hd p).a = d.factorization p := rfl

@[simp] theorem completePrimaryComponent_D (d : ℕ) (hd : d ≠ 0)
    (p : d.primeFactors) :
    (completePrimaryComponent d hd p).D =
      d / ((p : ℕ) ^ d.factorization p) := rfl

@[simp] theorem completePrimaryComponent_q (d : ℕ) (hd : d ≠ 0)
    (p : d.primeFactors) :
    (completePrimaryComponent d hd p).q =
      (p : ℕ) ^ d.factorization p := rfl

/-- The nontrivial denominator part is odd, also when it is equal to one. -/
theorem coprime_two_nontrivialPart (d : ℕ) (hd : d ≠ 0) :
    Nat.Coprime 2 (nontrivialPart d) := by
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  intro htwo
  have hmod : 2 % 4 = 1 :=
    ((prime_dvd_nontrivialPart_iff d 2 hd Nat.prime_two).mp htwo).2
  norm_num at hmod

end

end Selector

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorCoset.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The `P`/`Q` coset reduction

This file isolates the part of the Jackson--Mauldin selector argument which
does not depend on the construction of the good permutations.  The
denominator is written `P * Q`, where `P` is the product of the nontrivial
prime powers and `Q` is the complementary product.  A selector constructed at
denominator `p * P` is used separately on each of the `Q^2` cosets.

The only arithmetic input needed to rule out conflicts between distinct
cosets is `SquareNormRigid Q`.  It is deliberately stated over `ℤ`: this is
the right condition also at the prime `2`, where anisotropy over `ZMod 2` is
false.  `SelectorFactorization` is responsible for proving this condition for
the canonical trivial part.
-/

namespace Selector

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The remainder, as an element of the finite coset-indexing type. -/
def remainderFin (Q : ℕ) (hQ : 0 < Q) {D : ℕ} (i : Fin (Q * D)) : Fin Q :=
  ⟨remainderIndex Q i, remainderIndex_lt Q hQ i⟩

@[simp] lemma remainderFin_val (Q : ℕ) (hQ : 0 < Q) {D : ℕ}
    (i : Fin (Q * D)) :
    (remainderFin Q hQ i : ℕ) = remainderIndex Q i := rfl

/-- Reassemble a `Q`-coset and a coordinate in its denominator-`D` copy. -/
def joinIndex (Q : ℕ) (hQ : 0 < Q) {D : ℕ} (a : Fin Q) (x : Fin D) :
    Fin (Q * D) :=
  ⟨Q * (x : ℕ) + (a : ℕ), by
    calc
      Q * (x : ℕ) + (a : ℕ) < Q * (x : ℕ) + Q :=
        Nat.add_lt_add_left a.isLt _
      _ = Q * ((x : ℕ) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ ≤ Q * D := Nat.mul_le_mul_left Q (Nat.succ_le_iff.mpr x.isLt)⟩

@[simp] lemma joinIndex_val (Q : ℕ) (hQ : 0 < Q) {D : ℕ}
    (a : Fin Q) (x : Fin D) :
    (joinIndex Q hQ a x : ℕ) = Q * (x : ℕ) + (a : ℕ) := rfl

@[simp] lemma remainderIndex_joinIndex (Q : ℕ) (hQ : 0 < Q) {D : ℕ}
    (a : Fin Q) (x : Fin D) :
    remainderIndex Q (joinIndex Q hQ a x) = a := by
  simp only [remainderIndex, joinIndex_val, Nat.add_mod, Nat.mul_mod_right,
    zero_add, Nat.mod_eq_of_lt a.isLt]

@[simp] lemma quotientIndex_joinIndex (Q : ℕ) (hQ : 0 < Q) {D : ℕ}
    (a : Fin Q) (x : Fin D) :
    quotientIndex Q (joinIndex Q hQ a x) = x := by
  apply Fin.ext
  simp only [quotientIndex, hQ, ↓reduceDIte, joinIndex_val]
  simp [Nat.add_div, Nat.mod_eq_of_lt a.isLt,
    Nat.div_eq_of_lt a.isLt, Nat.not_le_of_gt a.isLt, hQ]

/-- Restrict a full selector to one `Q²`-coset and translate that coset back
to the pure denominator `D`. -/
def restrictCoset (Q : ℕ) (hQ : 0 < Q) {D : ℕ} (s : LiftData (Q * D))
    (a b : Fin Q) : LiftData D where
  k := fun x y ↦ s.k (joinIndex Q hQ a x) (joinIndex Q hQ b y)
  l := fun x y ↦ s.l (joinIndex Q hQ a x) (joinIndex Q hQ b y)

lemma sqDist_restrictCoset (Q : ℕ) (hQ : 0 < Q) {D : ℕ} (hD : D ≠ 0)
    (s : LiftData (Q * D)) (a b : Fin Q) (x₁ y₁ x₂ y₂ : Fin D) :
    sqDist ((restrictCoset Q hQ s a b).point x₁ y₁)
        ((restrictCoset Q hQ s a b).point x₂ y₂) =
      sqDist (s.point (joinIndex Q hQ a x₁) (joinIndex Q hQ b y₁))
        (s.point (joinIndex Q hQ a x₂) (joinIndex Q hQ b y₂)) := by
  simp only [LiftData.point, restrictCoset, liftedPoint, sqDist, joinIndex_val]
  push_cast
  field_simp [Nat.ne_of_gt hQ, hD]
  ring

theorem restrictCoset_separated (Q : ℕ) (hQ : 0 < Q) {D : ℕ} (hD : D ≠ 0)
    (s : LiftData (Q * D)) (hs : s.Separated) (a b : Fin Q) :
    (restrictCoset Q hQ s a b).Separated := by
  rw [LiftData.separated_iff_sqDist_not_int hD]
  intro x₁ y₁ x₂ y₂ hne hInt
  have hjoin :
      (joinIndex Q hQ a x₁, joinIndex Q hQ b y₁) ≠
        (joinIndex Q hQ a x₂, joinIndex Q hQ b y₂) := by
    intro h
    apply hne
    apply Prod.ext <;> apply Fin.ext
    · have hv := congrArg (fun z : Fin (Q * D) ↦ (z : ℕ)) (congrArg Prod.fst h)
      simp only [joinIndex_val] at hv
      exact Nat.mul_left_cancel hQ (Nat.add_right_cancel hv)
    · have hv := congrArg (fun z : Fin (Q * D) ↦ (z : ℕ)) (congrArg Prod.snd h)
      simp only [joinIndex_val] at hv
      exact Nat.mul_left_cancel hQ (Nat.add_right_cancel hv)
  have hfull := (LiftData.separated_iff_sqDist_not_int
      (Nat.mul_ne_zero (Nat.ne_of_gt hQ) hD) s).mp hs
    (joinIndex Q hQ a x₁) (joinIndex Q hQ b y₁)
    (joinIndex Q hQ a x₂) (joinIndex Q hQ b y₂) hjoin
  apply hfull
  rw [← sqDist_restrictCoset Q hQ hD s a b x₁ y₁ x₂ y₂]
  exact hInt

/-- Assemble independently chosen denominator-`D` selectors on all `Q²`
cosets. -/
def assembleCosets (Q : ℕ) (hQ : 0 < Q) {D : ℕ}
    (pieces : Fin Q → Fin Q → LiftData D) : LiftData (Q * D) where
  k := fun i j ↦
    (pieces (remainderFin Q hQ i) (remainderFin Q hQ j)).k
      (quotientIndex Q i) (quotientIndex Q j)
  l := fun i j ↦
    (pieces (remainderFin Q hQ i) (remainderFin Q hQ j)).l
      (quotientIndex Q i) (quotientIndex Q j)

/-- Translate the residue coordinates of a selector cyclically by `c,d`.
The quotient terms are the integral corrections at the wraparound. -/
def shiftLift {n : ℕ} (c d : Fin n) (s : LiftData n) : LiftData n where
  k := fun i j ↦
    s.k (i - c) (j - d) + (((i - c : Fin n) : ℕ) + (c : ℕ)) / n
  l := fun i j ↦
    s.l (i - c) (j - d) + (((j - d : Fin n) : ℕ) + (d : ℕ)) / n

lemma shiftLift_point {n : ℕ} (hn : n ≠ 0) (c d : Fin n) (s : LiftData n)
    (i j : Fin n) :
    (shiftLift c d s).point i j =
      ((s.point (i - c) (j - d)).1 + (c : ℕ) / (n : ℚ),
        (s.point (i - c) (j - d)).2 + (d : ℕ) / (n : ℚ)) := by
  letI : NeZero n := ⟨hn⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hxi : (((i - c : Fin n) : ℕ) + (c : ℕ)) % n = (i : ℕ) := by
    have h := congrArg (fun z : Fin n ↦ (z : ℕ)) (sub_add_cancel i c)
    simpa only [Fin.val_add, Nat.mod_eq_of_lt i.isLt] using h
  have hxdiv := Nat.mod_add_div (((i - c : Fin n) : ℕ) + (c : ℕ)) n
  have hxeq : (i : ℕ) + n * ((((i - c : Fin n) : ℕ) + (c : ℕ)) / n) =
      ((i - c : Fin n) : ℕ) + (c : ℕ) := by
    rw [← hxi]
    omega
  have hyi : (((j - d : Fin n) : ℕ) + (d : ℕ)) % n = (j : ℕ) := by
    have h := congrArg (fun z : Fin n ↦ (z : ℕ)) (sub_add_cancel j d)
    simpa only [Fin.val_add, Nat.mod_eq_of_lt j.isLt] using h
  have hydiv := Nat.mod_add_div (((j - d : Fin n) : ℕ) + (d : ℕ)) n
  have hyeq : (j : ℕ) + n * ((((j - d : Fin n) : ℕ) + (d : ℕ)) / n) =
      ((j - d : Fin n) : ℕ) + (d : ℕ) := by
    rw [← hyi]
    omega
  apply Prod.ext
  · simp only [LiftData.point, shiftLift, liftedPoint]
    push_cast
    field_simp [hn]
    norm_cast
    have hxeqZ : (i : ℤ) + (n : ℤ) *
        (((((i - c : Fin n) : ℕ) + (c : ℕ)) / n : ℕ) : ℤ) =
          ((i - c : Fin n) : ℕ) + (c : ℕ) := by
      exact_mod_cast hxeq
    rw [mul_add]
    linear_combination hxeqZ
  · simp only [LiftData.point, shiftLift, liftedPoint]
    push_cast
    field_simp [hn]
    norm_cast
    have hyeqZ : (j : ℤ) + (n : ℤ) *
        (((((j - d : Fin n) : ℕ) + (d : ℕ)) / n : ℕ) : ℤ) =
          ((j - d : Fin n) : ℕ) + (d : ℕ) := by
      exact_mod_cast hyeq
    rw [mul_add]
    linear_combination hyeqZ

lemma sqDist_shiftLift {n : ℕ} (hn : n ≠ 0) (c d : Fin n) (s : LiftData n)
    (i₁ j₁ i₂ j₂ : Fin n) :
    sqDist ((shiftLift c d s).point i₁ j₁) ((shiftLift c d s).point i₂ j₂) =
      sqDist (s.point (i₁ - c) (j₁ - d)) (s.point (i₂ - c) (j₂ - d)) := by
  rw [shiftLift_point hn, shiftLift_point hn]
  simp only [sqDist]
  ring

theorem shiftLift_separated {n : ℕ} (hn : n ≠ 0) (c d : Fin n)
    (s : LiftData n) (hs : s.Separated) : (shiftLift c d s).Separated := by
  letI : NeZero n := ⟨hn⟩
  rw [LiftData.separated_iff_sqDist_not_int hn]
  intro i₁ j₁ i₂ j₂ hne
  have hne' : (i₁ - c, j₁ - d) ≠ (i₂ - c, j₂ - d) := by
    intro h
    apply hne
    apply Prod.ext
    · exact sub_left_injective (congrArg Prod.fst h)
    · exact sub_left_injective (congrArg Prod.snd h)
  have hsep := (LiftData.separated_iff_sqDist_not_int hn s).mp hs
    (i₁ - c) (j₁ - d) (i₂ - c) (j₂ - d) hne'
  rw [sqDist_shiftLift hn]
  exact hsep

/-- Multiplication by `p` on the finite set of `Q` cosets. -/
def mulCosetMap (p Q : ℕ) (hQ : 0 < Q) (a : Fin Q) : Fin Q :=
  ⟨(p * (a : ℕ)) % Q, Nat.mod_lt _ hQ⟩

lemma mulCosetMap_injective (p Q : ℕ) (hQ : 0 < Q) (hcop : p.Coprime Q) :
    Function.Injective (mulCosetMap p Q hQ) := by
  intro a b hab
  have hv := congrArg (fun z : Fin Q ↦ (z : ℕ)) hab
  have hm : p * (a : ℕ) ≡ p * (b : ℕ) [MOD Q] := by
    exact hv
  have habm : (a : ℕ) ≡ (b : ℕ) [MOD Q] :=
    Nat.ModEq.cancel_left_of_coprime hcop.symm hm
  apply Fin.ext
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using habm

/-- The permutation of the `Q` cosets induced by multiplication by `p`. -/
noncomputable def mulCosetEquiv (p Q : ℕ) (hQ : 0 < Q) (hcop : p.Coprime Q) :
    Equiv.Perm (Fin Q) :=
  Equiv.ofBijective (mulCosetMap p Q hQ)
    ⟨mulCosetMap_injective p Q hQ hcop,
      (Finite.injective_iff_surjective).mp (mulCosetMap_injective p Q hQ hcop)⟩

@[simp] lemma mulCosetEquiv_apply (p Q : ℕ) (hQ : 0 < Q) (hcop : p.Coprime Q)
    (a : Fin Q) :
    mulCosetEquiv p Q hQ hcop a = mulCosetMap p Q hQ a := rfl

/-- The quotient carry in `p*a = Q*carry + (p*a mod Q)`. -/
def cosetCarry (p Q : ℕ) (a : Fin Q) : ℕ := p * (a : ℕ) / Q

lemma cosetCarry_lt (p Q : ℕ) (hp : 0 < p) (hQ : 0 < Q) (a : Fin Q) :
    cosetCarry p Q a < p := by
  rw [cosetCarry, Nat.div_lt_iff_lt_mul hQ]
  exact (Nat.mul_lt_mul_left hp).2 a.isLt

lemma mul_val_eq_coset (p Q : ℕ) (hQ : 0 < Q) (a : Fin Q) :
    p * (a : ℕ) = Q * cosetCarry p Q a + (mulCosetMap p Q hQ a : ℕ) := by
  simp only [cosetCarry, mulCosetMap]
  simpa [Nat.add_comm, Nat.mul_comm] using (Nat.mod_add_div (p * (a : ℕ)) Q).symm

/-- The quotient carry, regarded as a residue at the enlarged pure
denominator.  The inequality `carry < p ≤ p*P` is the reason for the
positivity hypothesis on `P`. -/
def cosetCarryIndex (p P Q : ℕ) (hp : 0 < p) (hP : 0 < P) (hQ : 0 < Q)
    (a : Fin Q) : Fin (p * P) :=
  ⟨cosetCarry p Q a, by
    have hc := cosetCarry_lt p Q hp hQ a
    have hpP : p ≤ p * P := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left p (Nat.succ_le_iff.mpr hP)
    exact lt_of_lt_of_le hc hpP⟩

@[simp] lemma cosetCarryIndex_val (p P Q : ℕ) (hp : 0 < p) (hP : 0 < P)
    (hQ : 0 < Q) (a : Fin Q) :
    (cosetCarryIndex p P Q hp hP hQ a : ℕ) = cosetCarry p Q a := rfl

/-- In the target copy belonging to the coset `p*a mod Q`, the old pure
residue `x` occurs at `p*x + carry(p,a)`. -/
def localOldIndex (p P Q : ℕ) (hp : 0 < p) (hP : 0 < P) (hQ : 0 < Q)
    (a : Fin Q) (x : Fin P) : Fin (p * P) :=
  ⟨p * (x : ℕ) + cosetCarry p Q a, by
    have hc := cosetCarry_lt p Q hp hQ a
    calc
      p * (x : ℕ) + cosetCarry p Q a < p * (x : ℕ) + p :=
        Nat.add_lt_add_left hc _
      _ = p * ((x : ℕ) + 1) := by ring
      _ ≤ p * P := Nat.mul_le_mul_left p (Nat.succ_le_iff.mpr x.isLt)⟩

@[simp] lemma localOldIndex_val (p P Q : ℕ) (hp : 0 < p) (hP : 0 < P)
    (hQ : 0 < Q) (a : Fin Q) (x : Fin P) :
    (localOldIndex p P Q hp hP hQ a x : ℕ) =
      p * (x : ℕ) + cosetCarry p Q a := rfl

lemma localOldIndex_sub_carry (p P Q : ℕ) (hp : 0 < p) (hP : 0 < P)
    (hQ : 0 < Q) (a : Fin Q) (x : Fin P) :
    localOldIndex p P Q hp hP hQ a x -
        cosetCarryIndex p P Q hp hP hQ a = oldIndex p hp x := by
  apply Fin.ext
  simp only [Fin.val_sub, localOldIndex_val, cosetCarryIndex_val, oldIndex]
  have hc : cosetCarry p Q a ≤ p * P :=
    le_of_lt (cosetCarryIndex p P Q hp hP hQ a).isLt
  have hx : p * (x : ℕ) < p * P := (oldIndex p hp x).isLt
  rw [show p * P - cosetCarry p Q a +
      (p * (x : ℕ) + cosetCarry p Q a) = p * P + p * (x : ℕ) by omega]
  simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_eq_of_lt hx]

lemma shiftLift_at_localOldIndex (p P Q : ℕ) (hp : 0 < p) (hP : 0 < P)
    (hQ : 0 < Q) (a b : Fin Q) (u : LiftData (p * P)) (x y : Fin P) :
    (shiftLift (cosetCarryIndex p P Q hp hP hQ a)
        (cosetCarryIndex p P Q hp hP hQ b) u).k
          (localOldIndex p P Q hp hP hQ a x)
          (localOldIndex p P Q hp hP hQ b y) =
        u.k (oldIndex p hp x) (oldIndex p hp y) ∧
    (shiftLift (cosetCarryIndex p P Q hp hP hQ a)
        (cosetCarryIndex p P Q hp hP hQ b) u).l
          (localOldIndex p P Q hp hP hQ a x)
          (localOldIndex p P Q hp hP hQ b y) =
        u.l (oldIndex p hp x) (oldIndex p hp y) := by
  have hi := localOldIndex_sub_carry p P Q hp hP hQ a x
  have hj := localOldIndex_sub_carry p P Q hp hP hQ b y
  have hxi : p * (x : ℕ) + cosetCarry p Q a < p * P :=
    (localOldIndex p P Q hp hP hQ a x).isLt
  have hyi : p * (y : ℕ) + cosetCarry p Q b < p * P :=
    (localOldIndex p P Q hp hP hQ b y).isLt
  constructor
  · simp only [shiftLift, hi, hj, oldIndex, cosetCarryIndex_val]
    have hzero : ((((p * (x : ℕ) : ℕ) : ℤ) +
        ((cosetCarry p Q a : ℕ) : ℤ)) /
          (((p * P : ℕ) : ℤ))) = 0 := by
      apply Int.ediv_eq_zero_of_lt
      · positivity
      · exact_mod_cast hxi
    rw [hzero, add_zero]
  · simp only [shiftLift, hi, hj, oldIndex, cosetCarryIndex_val]
    have hzero : ((((p * (y : ℕ) : ℕ) : ℤ) +
        ((cosetCarry p Q b : ℕ) : ℤ)) /
          (((p * P : ℕ) : ℤ))) = 0 := by
      apply Int.ediv_eq_zero_of_lt
      · positivity
      · exact_mod_cast hyi
    rw [hzero, add_zero]

/-- Transport lift data across an equality of denominators.  This definition
is kept local to the coset module, so the coset reduction does not depend on
the later infinite-chain construction. -/
def LiftData.transport {d e : ℕ} (h : d = e) (s : LiftData d) : LiftData e :=
  h ▸ s

@[simp] lemma LiftData.transport_rfl {d : ℕ} (s : LiftData d) :
    s.transport rfl = s := rfl

lemma LiftData.separated_transport {d e : ℕ} (h : d = e) (s : LiftData d)
    (hs : s.Separated) : (s.transport h).Separated := by
  subst e
  exact hs

@[simp] lemma LiftData.transport_k {d e : ℕ} (h : d = e) (s : LiftData d)
    (i j : Fin e) :
    (s.transport h).k i j = s.k (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst e
  rfl

@[simp] lemma LiftData.transport_l {d e : ℕ} (h : d = e) (s : LiftData d)
    (i j : Fin e) :
    (s.transport h).l i j = s.l (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst e
  rfl

/-- The elementary reassociation which changes the coset-friendly target
denominator into the standard prime-extension denominator. -/
lemma pqTargetDenom_eq (p P Q : ℕ) :
    Q * (p * P) = p * (P * Q) := by
  ac_rfl

lemma joinIndex_remainderFin_quotientIndex (Q : ℕ) (hQ : 0 < Q)
    {D : ℕ} (i : Fin (Q * D)) :
    joinIndex Q hQ (remainderFin Q hQ i) (quotientIndex Q i) = i := by
  apply Fin.ext
  exact (val_eq_mul_quotient_add_remainder Q hQ i).symm

/-- The old selector, written in `Q`-coset coordinates. -/
def oldCosetPiece (P Q : ℕ) (hQ : 0 < Q) (s : LiftData (P * Q))
    (a b : Fin Q) : LiftData P :=
  restrictCoset Q hQ (s.transport (Nat.mul_comm P Q)) a b

theorem oldCosetPiece_separated (P Q : ℕ) (hP : 0 < P) (hQ : 0 < Q)
    (s : LiftData (P * Q)) (hs : s.Separated) (a b : Fin Q) :
    (oldCosetPiece P Q hQ s a b).Separated := by
  apply restrictCoset_separated Q hQ (Nat.ne_of_gt hP)
      (s.transport (Nat.mul_comm P Q))
  exact LiftData.separated_transport (Nat.mul_comm P Q) s hs

lemma oldCosetPiece_at_quotient (P Q : ℕ) (hQ : 0 < Q)
    (s : LiftData (P * Q)) (i j : Fin (P * Q)) :
    let i' : Fin (Q * P) := Fin.cast (Nat.mul_comm P Q) i
    let j' : Fin (Q * P) := Fin.cast (Nat.mul_comm P Q) j
    (oldCosetPiece P Q hQ s (remainderFin Q hQ i') (remainderFin Q hQ j')).k
        (quotientIndex Q i') (quotientIndex Q j') = s.k i j ∧
    (oldCosetPiece P Q hQ s (remainderFin Q hQ i') (remainderFin Q hQ j')).l
        (quotientIndex Q i') (quotientIndex Q j') = s.l i j := by
  dsimp only
  simp only [oldCosetPiece, restrictCoset]
  rw [joinIndex_remainderFin_quotientIndex Q hQ,
    joinIndex_remainderFin_quotientIndex Q hQ]
  simp

lemma remainderFin_target_oldIndex (p : ℕ) (hp : 0 < p) (P Q : ℕ)
    (hQ : 0 < Q) (hcop : p.Coprime Q) (i : Fin (P * Q)) :
    let i' : Fin (Q * P) := Fin.cast (Nat.mul_comm P Q) i
    let I : Fin (Q * (p * P)) :=
      Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp i)
    remainderFin Q hQ I =
      mulCosetEquiv p Q hQ hcop (remainderFin Q hQ i') := by
  dsimp only
  apply Fin.ext
  simp only [remainderFin_val, remainderIndex, Fin.val_cast, oldIndex,
    mulCosetEquiv_apply, mulCosetMap]
  simp [Nat.mul_mod]

lemma quotientIndex_target_oldIndex (p : ℕ) (hp : 0 < p)
    (P Q : ℕ) (hP : 0 < P) (hQ : 0 < Q) (i : Fin (P * Q)) :
    let i' : Fin (Q * P) := Fin.cast (Nat.mul_comm P Q) i
    let I : Fin (Q * (p * P)) :=
      Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp i)
    quotientIndex Q I =
      localOldIndex p P Q hp hP hQ (remainderFin Q hQ i')
        (quotientIndex Q i') := by
  dsimp only
  let i' : Fin (Q * P) := Fin.cast (Nat.mul_comm P Q) i
  let I : Fin (Q * (p * P)) :=
    Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp i)
  let a : Fin Q := remainderFin Q hQ i'
  let x : Fin P := quotientIndex Q i'
  have hi := val_eq_mul_quotient_add_remainder Q hQ i'
  have hI := val_eq_mul_quotient_add_remainder Q hQ I
  have hspec : (I : ℕ) =
      Q * (localOldIndex p P Q hp hP hQ a x : ℕ) +
        (mulCosetMap p Q hQ a : ℕ) := by
    calc
      (I : ℕ) = p * (i : ℕ) := rfl
      _ = p * (i' : ℕ) := rfl
      _ = p * (Q * (x : ℕ) + (a : ℕ)) := by
        exact congrArg (fun z : ℕ ↦ p * z)
          (by simpa only [x, a, remainderFin_val] using hi)
      _ = Q * (p * (x : ℕ)) + p * (a : ℕ) := by ring
      _ = Q * (p * (x : ℕ)) +
          (Q * cosetCarry p Q a + (mulCosetMap p Q hQ a : ℕ)) := by
            rw [mul_val_eq_coset p Q hQ a]
      _ = Q * (localOldIndex p P Q hp hP hQ a x : ℕ) +
          (mulCosetMap p Q hQ a : ℕ) := by
            rw [localOldIndex_val]
            ring
  have hrem : remainderIndex Q I = (mulCosetMap p Q hQ a : ℕ) := by
    rw [remainderIndex, hspec]
    simp only [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (mulCosetMap p Q hQ a).isLt
  apply Fin.ext
  have heq : Q * (quotientIndex Q I : ℕ) + remainderIndex Q I =
      Q * (localOldIndex p P Q hp hP hQ a x : ℕ) + remainderIndex Q I := by
    calc
      _ = (I : ℕ) := hI.symm
      _ = Q * (localOldIndex p P Q hp hP hQ a x : ℕ) +
          (mulCosetMap p Q hQ a : ℕ) := hspec
      _ = _ := by rw [hrem]
  exact Nat.mul_left_cancel hQ (Nat.add_right_cancel heq)

lemma sourceCoset_target_oldIndex (p : ℕ) (hp : 0 < p) (P Q : ℕ)
    (hQ : 0 < Q) (hcop : p.Coprime Q) (i : Fin (P * Q)) :
    let i' : Fin (Q * P) := Fin.cast (Nat.mul_comm P Q) i
    let I : Fin (Q * (p * P)) :=
      Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp i)
    (mulCosetEquiv p Q hQ hcop).symm (remainderFin Q hQ I) =
      remainderFin Q hQ i' := by
  dsimp only
  rw [remainderFin_target_oldIndex p hp P Q hQ hcop]
  exact (mulCosetEquiv p Q hQ hcop).symm_apply_apply _

/-- If an integral squared distance occurs at denominator `Q*D`, then the two
coordinate numerators are divisible by `Q`.  Consequently the two residues
belong to the same `Q`-coset.  Notice that the lifts themselves are arbitrary. -/
theorem same_remainders_of_integral_sqDist
    (Q : ℕ) (hQ : 0 < Q) (hRigid : SquareNormRigid Q)
    {D : ℕ} (hD : D ≠ 0) (t : LiftData (Q * D))
    (i₁ j₁ i₂ j₂ : Fin (Q * D))
    (hInt : ∃ z : ℤ, sqDist (t.point i₁ j₁) (t.point i₂ j₂) = z) :
    remainderIndex Q i₁ = remainderIndex Q i₂ ∧
      remainderIndex Q j₁ = remainderIndex Q j₂ := by
  let N : ℕ := Q * D
  have hN : N ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hQ) hD
  have hconf : (N : ℤ) ^ 2 ∣
      conflictNumerator N i₁ j₁ i₂ j₂
        (t.k i₁ j₁) (t.l i₁ j₁) (t.k i₂ j₂) (t.l i₂ j₂) :=
    (sqDist_liftedPoint_isInt_iff N hN i₁ j₁ i₂ j₂
      (t.k i₁ j₁) (t.l i₁ j₁) (t.k i₂ j₂) (t.l i₂ j₂)).mp hInt
  have hdist : (N : ℤ) ^ 2 ∣
      distanceNumerator N i₁ j₁ i₂ j₂
        (t.k i₁ j₁) (t.l i₁ j₁) (t.k i₂ j₂) (t.l i₂ j₂) :=
    (distanceNumerator_dvd_iff N i₁ j₁ i₂ j₂
      (t.k i₁ j₁) (t.l i₁ j₁) (t.k i₂ j₂) (t.l i₂ j₂)).2 hconf
  have hQN : (Q : ℤ) ^ 2 ∣ (N : ℤ) ^ 2 := by
    refine ⟨(D : ℤ) ^ 2, ?_⟩
    simp only [N]
    push_cast
    ring
  have hQdist := dvd_trans hQN hdist
  let A : ℤ := (i₁ : ℕ) - (i₂ : ℕ) + (N : ℤ) * (t.k i₁ j₁ - t.k i₂ j₂)
  let B : ℤ := (j₁ : ℕ) - (j₂ : ℕ) + (N : ℤ) * (t.l i₁ j₁ - t.l i₂ j₂)
  have hAB : (Q : ℤ) ^ 2 ∣ A ^ 2 + B ^ 2 := by
    rcases hQdist with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    calc
      A ^ 2 + B ^ 2 = distanceNumerator N i₁ j₁ i₂ j₂
          (t.k i₁ j₁) (t.l i₁ j₁) (t.k i₂ j₂) (t.l i₂ j₂) := by
            dsimp [A, B, distanceNumerator, conflictNumerator]
            ring
      _ = (Q : ℤ) ^ 2 * c := hc
  obtain ⟨hA, hB⟩ := hRigid A B hAB
  have hQNk (k : ℤ) : (Q : ℤ) ∣ (N : ℤ) * k := by
    refine ⟨(D : ℤ) * k, ?_⟩
    simp only [N]
    push_cast
    ring
  have hiDiff : (Q : ℤ) ∣ ((i₁ : ℕ) : ℤ) - ((i₂ : ℕ) : ℤ) := by
    rw [show ((i₁ : ℕ) : ℤ) - ((i₂ : ℕ) : ℤ) =
        A - (N : ℤ) * (t.k i₁ j₁ - t.k i₂ j₂) by
      dsimp [A]
      ring]
    exact dvd_sub hA (hQNk (t.k i₁ j₁ - t.k i₂ j₂))
  have hjDiff : (Q : ℤ) ∣ ((j₁ : ℕ) : ℤ) - ((j₂ : ℕ) : ℤ) := by
    rw [show ((j₁ : ℕ) : ℤ) - ((j₂ : ℕ) : ℤ) =
        B - (N : ℤ) * (t.l i₁ j₁ - t.l i₂ j₂) by
      dsimp [B]
      ring]
    exact dvd_sub hB (hQNk (t.l i₁ j₁ - t.l i₂ j₂))
  let _ : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  have residue_eq_of_dvd {a b : ℕ}
      (h : (Q : ℤ) ∣ (a : ℤ) - (b : ℤ)) : a % Q = b % Q := by
    rcases h with ⟨c, hc⟩
    have hz : (a : ZMod Q) - (b : ZMod Q) = 0 := by
      have hc' := congrArg (fun x : ℤ ↦ (x : ZMod Q)) hc
      push_cast at hc'
      simpa using hc'
    have heq : (a : ZMod Q) = (b : ZMod Q) := sub_eq_zero.mp hz
    have hv := congrArg ZMod.val heq
    simpa using hv
  exact ⟨residue_eq_of_dvd hiDiff, residue_eq_of_dvd hjDiff⟩

/-- Distinct `Q`-cosets can never contain a pair at integral squared
distance.  This is the cross-coset half of the `P`/`Q` reduction. -/
theorem cross_coset_sqDist_not_integral
    (Q : ℕ) (hQ : 0 < Q) (hRigid : SquareNormRigid Q)
    {D : ℕ} (hD : D ≠ 0) (t : LiftData (Q * D))
    (i₁ j₁ i₂ j₂ : Fin (Q * D))
    (hcross : remainderIndex Q i₁ ≠ remainderIndex Q i₂ ∨
      remainderIndex Q j₁ ≠ remainderIndex Q j₂) :
    ¬∃ z : ℤ, sqDist (t.point i₁ j₁) (t.point i₂ j₂) = z := by
  intro hInt
  obtain ⟨hi, hj⟩ := same_remainders_of_integral_sqDist Q hQ hRigid hD t
    i₁ j₁ i₂ j₂ hInt
  exact hcross.elim (fun h ↦ h hi) (fun h ↦ h hj)

/-- Exact within-coset reduction.  For each of the `Q²` cosets, distances
are identified with distances in a local selector at denominator `D`. -/
def ModeledWithinCosets (Q : ℕ) (hQ : 0 < Q) {D : ℕ}
    (t : LiftData (Q * D)) (pieces : Fin Q → Fin Q → LiftData D) : Prop :=
  ∀ i₁ j₁ i₂ j₂,
    remainderIndex Q i₁ = remainderIndex Q i₂ →
    remainderIndex Q j₁ = remainderIndex Q j₂ →
    sqDist (t.point i₁ j₁) (t.point i₂ j₂) =
      sqDist
        ((pieces (remainderFin Q hQ i₁) (remainderFin Q hQ j₁)).point
          (quotientIndex Q i₁) (quotientIndex Q j₁))
        ((pieces (remainderFin Q hQ i₁) (remainderFin Q hQ j₁)).point
          (quotientIndex Q i₂) (quotientIndex Q j₂))

theorem assembleCosets_modeled (Q : ℕ) (hQ : 0 < Q) {D : ℕ} (hD : D ≠ 0)
    (pieces : Fin Q → Fin Q → LiftData D) :
    ModeledWithinCosets Q hQ (assembleCosets Q hQ pieces) pieces := by
  intro i₁ j₁ i₂ j₂ hi hj
  simp only [LiftData.point, assembleCosets, liftedPoint, sqDist]
  have hvi₁ := val_eq_mul_quotient_add_remainder Q hQ i₁
  have hvi₂ := val_eq_mul_quotient_add_remainder Q hQ i₂
  have hvj₁ := val_eq_mul_quotient_add_remainder Q hQ j₁
  have hvj₂ := val_eq_mul_quotient_add_remainder Q hQ j₂
  have hai : remainderFin Q hQ i₂ = remainderFin Q hQ i₁ := by
    apply Fin.ext
    exact hi.symm
  have haj : remainderFin Q hQ j₂ = remainderFin Q hQ j₁ := by
    apply Fin.ext
    exact hj.symm
  rw [hai, haj]
  push_cast
  field_simp [Nat.ne_of_gt hQ, hD]
  rw [hvi₁, hvi₂, hvj₁, hvj₂, hi, hj]
  push_cast
  ring

/-- Glue separated local selectors on the `Q²` cosets.  Same-coset pairs
reduce to a local selector; different-coset pairs are handled solely by the
integer norm condition. -/
theorem separated_of_coset_model
    (Q : ℕ) (hQ : 0 < Q) (hRigid : SquareNormRigid Q)
    {D : ℕ} (hD : D ≠ 0) (t : LiftData (Q * D))
    (pieces : Fin Q → Fin Q → LiftData D)
    (hpieces : ∀ a b, (pieces a b).Separated)
    (hmodel : ModeledWithinCosets Q hQ t pieces) : t.Separated := by
  rw [LiftData.separated_iff_sqDist_not_int (Nat.mul_ne_zero (Nat.ne_of_gt hQ) hD)]
  intro i₁ j₁ i₂ j₂ hne
  by_cases hi : remainderIndex Q i₁ = remainderIndex Q i₂
  · by_cases hj : remainderIndex Q j₁ = remainderIndex Q j₂
    · have hquot :
          (quotientIndex Q i₁, quotientIndex Q j₁) ≠
            (quotientIndex Q i₂, quotientIndex Q j₂) := by
        intro h
        apply hne
        apply Prod.ext <;> apply Fin.ext
        · have hq := congrArg (fun x : Fin D ↦ (x : ℕ)) (congrArg Prod.fst h)
          rw [val_eq_mul_quotient_add_remainder Q hQ i₁,
            val_eq_mul_quotient_add_remainder Q hQ i₂, hi, hq]
        · have hq := congrArg (fun x : Fin D ↦ (x : ℕ)) (congrArg Prod.snd h)
          rw [val_eq_mul_quotient_add_remainder Q hQ j₁,
            val_eq_mul_quotient_add_remainder Q hQ j₂, hj, hq]
      have hsep := (LiftData.separated_iff_sqDist_not_int hD
        (pieces (remainderFin Q hQ i₁) (remainderFin Q hQ j₁))).mp
          (hpieces _ _) (quotientIndex Q i₁) (quotientIndex Q j₁)
            (quotientIndex Q i₂) (quotientIndex Q j₂) hquot
      rw [hmodel i₁ j₁ i₂ j₂ hi hj]
      exact hsep
    · exact cross_coset_sqDist_not_integral Q hQ hRigid hD t i₁ j₁ i₂ j₂ (Or.inr hj)
  · exact cross_coset_sqDist_not_integral Q hQ hRigid hD t i₁ j₁ i₂ j₂ (Or.inl hi)

/-- Literal extension into the coset-friendly target denominator.  The cast
in the arguments is just the equality `Q*(p*P)=p*(P*Q)` read backwards. -/
def PQRawPrimeExtends (p : ℕ) (hp : 0 < p) (P Q : ℕ)
    (s : LiftData (P * Q)) (t : LiftData (Q * (p * P))) : Prop :=
  ∀ i j,
    t.k (Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp i))
        (Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp j)) = s.k i j ∧
    t.l (Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp i))
        (Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp j)) = s.l i j

/-- A family of literal pure extensions, one for each `Q²`-coset, together
with the exact gluing and literal-preservation facts.  The good-permutation
construction supplies `localExtends` and `localSeparated`; the coordinate
calculation supplies `modeled` and `literal`. -/
structure PQCosetExtension (p : ℕ) (hp : 0 < p) (P Q : ℕ) (hQ : 0 < Q)
    (s : LiftData (P * Q)) where
  oldLocal : Fin Q → Fin Q → LiftData P
  pureLocal : Fin Q → Fin Q → LiftData (p * P)
  localExtends : ∀ a b, PrimeExtends p hp (oldLocal a b) (pureLocal a b)
  pureSeparated : ∀ a b, (pureLocal a b).Separated
  /-- The pure pieces after permuting the `Q`-cosets and applying the exact
  quotient-carry shifts. -/
  newLocal : Fin Q → Fin Q → LiftData (p * P)
  localSeparated : ∀ a b, (newLocal a b).Separated
  target : LiftData (Q * (p * P))
  modeled : ModeledWithinCosets Q hQ target newLocal
  literal : PQRawPrimeExtends p hp P Q s target

/-- Construct the full coset-gluing certificate from a separated old
selector and the pure `P → pP` extension theorem.

The inverse of `mulCosetEquiv` identifies which old `Q`-coset feeds a target
coset.  `shiftLift` by `cosetCarry` then places every old pure residue at the
actual quotient of the full old index.  Thus the final `literal` field is an
equality of integer lifts, rather than merely an equality of selected
rational points. -/
theorem exists_PQCosetExtension
    (p : ℕ) (hp : 0 < p) (P Q : ℕ) (hP : 0 < P) (hQ : 0 < Q)
    (hcop : p.Coprime Q) (s : LiftData (P * Q)) (hs : s.Separated)
    (pureExtension : ∀ u : LiftData P, u.Separated →
      ∃ v : LiftData (p * P), PrimeExtends p hp u v ∧ v.Separated) :
    Nonempty (PQCosetExtension p hp P Q hQ s) := by
  let oldLocal : Fin Q → Fin Q → LiftData P :=
    fun a b ↦ oldCosetPiece P Q hQ s a b
  have oldSeparated : ∀ a b, (oldLocal a b).Separated := by
    intro a b
    exact oldCosetPiece_separated P Q hP hQ s hs a b
  choose pureLocal localExtends pureSeparated using
    fun a b ↦ pureExtension (oldLocal a b) (oldSeparated a b)
  let source : Fin Q → Fin Q := fun a ↦ (mulCosetEquiv p Q hQ hcop).symm a
  let newLocal : Fin Q → Fin Q → LiftData (p * P) := fun A B ↦
    shiftLift (cosetCarryIndex p P Q hp hP hQ (source A))
      (cosetCarryIndex p P Q hp hP hQ (source B))
      (pureLocal (source A) (source B))
  have newSeparated : ∀ A B, (newLocal A B).Separated := by
    intro A B
    exact shiftLift_separated (Nat.mul_ne_zero (Nat.ne_of_gt hp) (Nat.ne_of_gt hP))
      (cosetCarryIndex p P Q hp hP hQ (source A))
      (cosetCarryIndex p P Q hp hP hQ (source B))
      (pureLocal (source A) (source B)) (pureSeparated (source A) (source B))
  let target : LiftData (Q * (p * P)) := assembleCosets Q hQ newLocal
  have modeled : ModeledWithinCosets Q hQ target newLocal :=
    assembleCosets_modeled Q hQ (Nat.mul_ne_zero (Nat.ne_of_gt hp) (Nat.ne_of_gt hP))
      newLocal
  have literal : PQRawPrimeExtends p hp P Q s target := by
    intro i j
    let i' : Fin (Q * P) := Fin.cast (Nat.mul_comm P Q) i
    let j' : Fin (Q * P) := Fin.cast (Nat.mul_comm P Q) j
    let I : Fin (Q * (p * P)) :=
      Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp i)
    let J : Fin (Q * (p * P)) :=
      Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp j)
    let a : Fin Q := remainderFin Q hQ i'
    let b : Fin Q := remainderFin Q hQ j'
    let A : Fin Q := remainderFin Q hQ I
    let B : Fin Q := remainderFin Q hQ J
    let x : Fin P := quotientIndex Q i'
    let y : Fin P := quotientIndex Q j'
    have hsourceA : source A = a := by
      simpa only [source, A, a, I, i'] using
        sourceCoset_target_oldIndex p hp P Q hQ hcop i
    have hsourceB : source B = b := by
      simpa only [source, B, b, J, j'] using
        sourceCoset_target_oldIndex p hp P Q hQ hcop j
    have hquotI : quotientIndex Q I =
        localOldIndex p P Q hp hP hQ a x := by
      simpa only [I, i', a, x] using
        quotientIndex_target_oldIndex p hp P Q hP hQ i
    have hquotJ : quotientIndex Q J =
        localOldIndex p P Q hp hP hQ b y := by
      simpa only [J, j', b, y] using
        quotientIndex_target_oldIndex p hp P Q hP hQ j
    have hshift :
        (newLocal A B).k (quotientIndex Q I) (quotientIndex Q J) =
            (pureLocal a b).k (oldIndex p hp x) (oldIndex p hp y) ∧
        (newLocal A B).l (quotientIndex Q I) (quotientIndex Q J) =
            (pureLocal a b).l (oldIndex p hp x) (oldIndex p hp y) := by
      simp only [newLocal, hsourceA, hsourceB, hquotI, hquotJ]
      exact shiftLift_at_localOldIndex p P Q hp hP hQ a b (pureLocal a b) x y
    have hext := localExtends a b x y
    have hold :
        (oldLocal a b).k x y = s.k i j ∧
        (oldLocal a b).l x y = s.l i j := by
      simpa only [oldLocal, a, b, x, y, i', j'] using
        oldCosetPiece_at_quotient P Q hQ s i j
    change target.k I J = s.k i j ∧ target.l I J = s.l i j
    change (newLocal A B).k (quotientIndex Q I) (quotientIndex Q J) = s.k i j ∧
      (newLocal A B).l (quotientIndex Q I) (quotientIndex Q J) = s.l i j
    exact ⟨hshift.1.trans (hext.1.trans hold.1),
      hshift.2.trans (hext.2.trans hold.2)⟩
  exact ⟨{
    oldLocal := oldLocal
    pureLocal := pureLocal
    localExtends := localExtends
    pureSeparated := pureSeparated
    newLocal := newLocal
    localSeparated := newSeparated
    target := target
    modeled := modeled
    literal := literal }⟩

lemma transported_raw_primeExtends
    (p : ℕ) (hp : 0 < p) (P Q : ℕ)
    (s : LiftData (P * Q)) (t : LiftData (Q * (p * P)))
    (h : PQRawPrimeExtends p hp P Q s t) :
    PrimeExtends p hp s (t.transport (pqTargetDenom_eq p P Q)) := by
  intro i j
  rw [LiftData.transport_k, LiftData.transport_l]
  exact h i j

/-- The complete abstract `P`/`Q` reduction.  Literal separated pure
extensions on all `Q²` cosets glue to a literal separated extension at the
full denominator. -/
theorem PQCosetExtension.toPrimeExtension
    (p : ℕ) (hp : 0 < p) (P Q : ℕ) (hP : P ≠ 0)
    (hQ : 0 < Q) (hRigid : SquareNormRigid Q)
    (s : LiftData (P * Q)) (E : PQCosetExtension p hp P Q hQ s) :
    ∃ t : LiftData (p * (P * Q)), PrimeExtends p hp s t ∧ t.Separated := by
  let rawSeparated : E.target.Separated :=
    separated_of_coset_model Q hQ hRigid (Nat.mul_ne_zero (Nat.ne_of_gt hp) hP)
      E.target E.newLocal E.localSeparated E.modeled
  refine ⟨E.target.transport (pqTargetDenom_eq p P Q),
    transported_raw_primeExtends p hp P Q s E.target E.literal, ?_⟩
  exact LiftData.separated_transport (pqTargetDenom_eq p P Q) E.target rawSeparated

/-- The usable `P`/`Q` reduction: a pure extension theorem at `P` yields a
literal separated extension at `P*Q`. -/
theorem primeExtension_of_pure_cosets
    (p : ℕ) (hp : 0 < p) (P Q : ℕ) (hP : 0 < P) (hQ : 0 < Q)
    (hcop : p.Coprime Q) (hRigid : SquareNormRigid Q)
    (s : LiftData (P * Q)) (hs : s.Separated)
    (pureExtension : ∀ u : LiftData P, u.Separated →
      ∃ v : LiftData (p * P), PrimeExtends p hp u v ∧ v.Separated) :
    ∃ t : LiftData (p * (P * Q)), PrimeExtends p hp s t ∧ t.Separated := by
  obtain ⟨E⟩ := exists_PQCosetExtension p hp P Q hP hQ hcop s hs pureExtension
  exact PQCosetExtension.toPrimeExtension p hp P Q (Nat.ne_of_gt hP) hQ hRigid s E

end

end Selector

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215/SelectorPrimeExtensionFinal.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The literal prime-extension theorem

This file closes the finite part of the Jackson--Mauldin construction.  For
an odd prime congruent to one modulo four, it splits a pure denominator as
`u * p^a`, applies the explicit good and consistent line family, and
reconstructs a separated literal extension.  The nontrivial/trivial
factorization and the coset gluing theorem then reduce a general denominator
to that pure case.  The prime `2` and primes congruent to three modulo four
use the elementary copied extensions already proved in `Selector.lean`.
-/

namespace Selector.PrimeExtension

open Erdos215.Selector
open Erdos215.Selector.Modular
open Erdos215.Selector.Final
open Erdos215.Selector.Separation
open Erdos215.Selector.PurePrimeExtension

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Transport a literal prime extension across an equality of its old
denominators. -/
private theorem transportPrimeExtensionResult
    {p d e : ℕ} (hp : 0 < p) (h : d = e) (s : LiftData e)
    (H : ∃ t : LiftData (p * d),
      PrimeExtends p hp (s.transport h.symm) t ∧ t.Separated) :
    ∃ t : LiftData (p * e), PrimeExtends p hp s t ∧ t.Separated := by
  subst e
  simpa only [LiftData.transport_rfl] using H

/-- Literal extension across a `1 mod 4` prime when every prime divisor of
the old denominator is also `1 mod 4`. -/
theorem pureLiteralPrimeExtension
    {p d : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (hp2 : p ≠ 2) (hd : d ≠ 0)
    (hodd : Nat.Coprime 2 d)
    (hpure : ∀ q : ℕ, q.Prime → q ∣ d → q % 4 = 1)
    (s : LiftData d) (hs : s.Separated) :
    ∃ t : LiftData (p * d), PrimeExtends p hp.pos s t ∧ t.Separated := by
  obtain ⟨u, a, hsplit, hu, hcop⟩ :=
    PrimeSplit.exists_eq_complement_mul_pow hp hd
  subst d
  have h2p : Nat.Coprime 2 p := by
    exact Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr (fun h ↦
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)))
  have hoddN : Nat.Coprime 2 (newDenom p u a) := by
    simpa only [newDenom, oldDenom] using Nat.Coprime.mul_right h2p hodd
  have hN : newDenom p u a ≠ 0 :=
    newDenom_ne_zero hp.ne_zero hu
  have hpureN : ∀ q : ℕ, q.Prime → q ∣ newDenom p u a → q % 4 = 1 := by
    intro q hq hqN
    have hqMul : q ∣ p * oldDenom p u a := by
      simpa only [newDenom] using hqN
    rcases hq.dvd_mul.mp hqMul with hqp | hqOld
    · have hqpEq : q = p :=
        (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
      simpa only [hqpEq] using hp1
    · exact hpure q hq hqOld
  obtain ⟨rho, hrho⟩ := PrimePowerGood.exists_goodPerm_primePower p a hp
  let C : CompleteComponents (newDenom p u a) :=
    Complete.canonicalCompleteComponents (newDenom p u a) hN
  have hroot : ConflictRootLineProperty (newDenom p u a) :=
    Complete.canonical_conflictRootLineProperty hN hpureN
  obtain ⟨lam₀⟩ := Complete.canonical_root_nonempty hN hpureN
  have hgood : FamilyGood (extendedFamily p u a hp hcop rho s) :=
    extendedFamily_good hp hp2 hcop hodd rho hrho s hs
  have hcons : FamilyConsistent (extendedFamily p u a hp hcop rho s) :=
    extendedFamily_consistent hp hp2 hcop hoddN rho s
  exact purePrimeExtension_of_family hp hcop hoddN C hroot rho s
    hgood hcons lam₀

/-- The pure extension theorem in the form needed by the `P`/`Q` coset
reduction: the old denominator is the nontrivial part of an arbitrary
nonzero denominator. -/
theorem pureLiteralPrimeExtension_nontrivialPart
    (p : ℕ) (hp : p.Prime) (hp1 : p % 4 = 1)
    (d : ℕ) (hd : d ≠ 0)
    (s : LiftData (nontrivialPart d)) (hs : s.Separated) :
    ∃ t : LiftData (p * nontrivialPart d),
      PrimeExtends p hp.pos s t ∧ t.Separated := by
  have hp2 : p ≠ 2 := by
    intro hpEq
    subst p
    norm_num at hp1
  exact pureLiteralPrimeExtension hp hp1 hp2
    (nontrivialPart_ne_zero d hd)
    (coprime_two_nontrivialPart d hd)
    (fun q hq hqP ↦ ((prime_dvd_nontrivialPart_iff d q hd hq).mp hqP).2)
    s hs

/-- Every separated finite selector has a literal separated extension across
every prime.  This is the exact finite hypothesis consumed by the direct
limit construction. -/
theorem literalPrimeExtension : Erdos215.Selector.LiteralPrimeExtensionHypothesis := by
  intro p hp d hd s hs
  rcases hp.eq_two_or_odd with hpEq | hpOdd
  · subst p
    exact ⟨doubleLift s, doubleLift_primeExtends s,
      doubleLift_separated hd s hs⟩
  · have hpMod : p % 4 = 1 ∨ p % 4 = 3 :=
      (Nat.odd_mod_four_iff).mp hpOdd
    rcases hpMod with hp1 | hp3
    · let P := nontrivialPart d
      let Q := trivialPart d
      have hP : 0 < P := Nat.pos_of_ne_zero (nontrivialPart_ne_zero d hd)
      have hQ : 0 < Q := Nat.pos_of_ne_zero (trivialPart_ne_zero d hd)
      have hPQ : P * Q = d := by
        simpa only [P, Q] using nontrivialPart_mul_trivialPart d hd
      have hp2 : p ≠ 2 := by
        intro hpEq
        subst p
        norm_num at hp1
      have hcopQ : Nat.Coprime p Q := by
        apply hp.coprime_iff_not_dvd.mpr
        intro hpQ
        have hpQ' : p ∣ trivialPart d := by
          simpa only [Q] using hpQ
        rcases ((prime_dvd_trivialPart_iff d p hd hp).mp hpQ').2 with htwo | hthree
        · exact hp2 htwo
        · omega
      have hRigid : SquareNormRigid Q := by
        simpa only [Q] using squareNormRigid_trivialPart d hd
      let sPQ : LiftData (P * Q) := s.transport hPQ.symm
      have hsPQ : sPQ.Separated :=
        LiftData.separated_transport hPQ.symm s hs
      have hresult := primeExtension_of_pure_cosets p hp.pos P Q hP hQ hcopQ
        hRigid sPQ hsPQ (fun u hu ↦ by
          simpa only [P] using
            pureLiteralPrimeExtension_nontrivialPart p hp hp1 d hd u hu)
      apply transportPrimeExtensionResult hp.pos hPQ s
      simpa only [sPQ] using hresult
    · letI : Fact p.Prime := ⟨hp⟩
      exact primeCopy_step_of_prime_mod_four_eq_three p hp3 hd s hs

end

end Selector.PrimeExtension

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos215.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 215.
https://www.erdosproblems.com/forum/thread/215

Informal authors:
- Steve Jackson
- R. Daniel Mauldin

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos215.md
-/

/-!
# Erdős Problem 215

Jackson and Mauldin proved in ZFC that there is a subset of the Euclidean
plane meeting every translated and rotated copy of `ℤ²` in exactly one point.
The internal construction establishes their stronger partial-Steinhaus
statement; `erdos215_of_jmStrong` performs the exact final conversion.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The stronger Jackson--Mauldin conclusion used by the construction. -/
def JMStrong : Prop :=
  ∃ S : Set Point, IsPartialSteinhaus S ∧ HitsEveryLattice S

/-- The strong Jackson--Mauldin statement implies the literal formulation of
Erdős Problem 215. -/
theorem erdos215_of_jmStrong (h : JMStrong) : ∃ S : Set Point, IsSteinhaus S := by
  rcases h with ⟨S, hpartial, hhits⟩
  exact ⟨S, isSteinhaus_of_partial_of_hits hpartial hhits⟩

/-- The Jackson--Mauldin partial-Steinhaus set meeting every oriented
integer lattice. -/
theorem jmStrong : JMStrong :=
  exists_partial_hitsEveryLattice_of_literalPrimeExtension
    Selector.PrimeExtension.literalPrimeExtension

/-- Positive resolution of Erdős Problem 215 (Steinhaus's lattice-copy
problem): a planar set meets every translated and rotated copy of `ℤ²` in
exactly one point. -/
theorem erdos_215 : ∃ S : Set Point, IsSteinhaus S :=
  erdos215_of_jmStrong jmStrong

end

end

#print axioms erdos_215
-- 'Erdos215.erdos_215' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos215
