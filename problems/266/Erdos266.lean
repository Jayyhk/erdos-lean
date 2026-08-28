import Mathlib

namespace Erdos266

/-
# Problem Description

Erdős Problem 266. Let `aₙ` be an infinite sequence of positive integers with `∑ 1/aₙ`
convergent. Must there be an integer `t ≥ 1` for which `∑ 1/(aₙ + t)` is irrational?
`erdos_266` disproves this.

The conjecture is due to Stolarsky and is recorded in [ErGr80, p.64] and [Er88c, p.104]. It
was refuted by Kovač and Tao [KoTa24], who proved more: there is a strictly increasing
sequence of positive integers `aₙ` for which `∑ 1/(aₙ + t)` converges to a rational number for
every `t ∈ ℚ` with `t ≠ -aₙ` for all `n`. The construction formalised below produces such a
sequence and shows every positive integer shift gives a rational sum.

The scope of the shift is worth recording, since two versions appear in print. Erdős and
Graham state Stolarsky's conjecture on p.64 of [ErGr80] as: "The following pretty conjecture
is due to Stolarsky: `∑_{n=1}^∞ 1/(aₙ + t)` cannot be rational for every positive integer
`t`." That is the form proved below, and it is the reference erdosproblems.com lists first.
Erdős restates it on p.104 of [Er88c] (and in [Er87]) allowing `t` to be any integer other
than `-aₙ`, writing it equivalently as `∑ 1/(aₙ - t)` with `t ≠ aₙ`. Kovač and Tao [KoTa24]
record both readings and note the second differs "with the exception that `t` was also allowed
to be an integer different from any of the numbers `-aₙ`"; their Theorem 2.11 disproves even
the rational-shift version, giving a strictly increasing `(aₙ)` for which `∑ 1/(aₙ + t)` is
rational for every `t ∈ ℚ \ {-aₙ}`. The theorem below is the positive-integer version, i.e.
Stolarsky's conjecture as Erdős and Graham recorded it; the stronger rational-shift form is
`erdos_266.variants.all_rationals` in Formal Conjectures and is not formalised here.

The formalisation is by plby (github.com/plby/lean-proofs),
`src/latest/ErdosProblems/Erdos266.lean` together with the six modules of
`src/latest/ErdosProblems/Erdos266/`. The seven files are concatenated here in dependency
order, with their project-internal imports removed so that `Mathlib` is the only import, each
module's contents kept in a `section` carrying its own `open` lines, the whole wrapped once in
`namespace Erdos266`, the upstream trust-base print line and trailing `alias` removed, and the
final theorem renamed from `not_erdos_266` to `erdos_266`. No mathematical content is changed.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos266/Erdos266Coordinates.lean` -/

section
/-!
# Coordinate identities for Erdős problem 266

For a positive integer `i`, `reciprocalCoordinate i x` is

`1 / ((x + 1) * ... * (x + i))`.

The central identity is the finite-difference relation

`f_i (x + 1) = f_i x - i * f_(i+1) x`.

It permits every positive integral translate of `1 / (x + 1)` to be expressed
as a finite integral linear combination of the coordinates at `x`.
-/



open scoped BigOperators

noncomputable section

/-- The denominator `(x + 1) * ... * (x + i)`. -/
def reciprocalCoordinateDenominator (i : ℕ) (x : ℝ) : ℝ :=
  ∏ r ∈ Finset.range i, (x + (r + 1 : ℕ))

/-- The positive-shift reciprocal coordinate
`f_i(x) = 1 / ((x + 1) * ... * (x + i))`.

The value at `i = 0` is the empty product, hence `1`; all mathematical uses
of coordinates below assume `1 ≤ i`.
-/
def reciprocalCoordinate (i : ℕ) (x : ℝ) : ℝ :=
  (reciprocalCoordinateDenominator i x)⁻¹

@[simp] lemma reciprocalCoordinateDenominator_zero (x : ℝ) :
    reciprocalCoordinateDenominator 0 x = 1 := by
  simp [reciprocalCoordinateDenominator]

lemma reciprocalCoordinateDenominator_succ (i : ℕ) (x : ℝ) :
    reciprocalCoordinateDenominator (i + 1) x =
      reciprocalCoordinateDenominator i x * (x + (i + 1 : ℕ)) := by
  simp [reciprocalCoordinateDenominator, Finset.prod_range_succ]

@[simp] lemma reciprocalCoordinate_zero (x : ℝ) : reciprocalCoordinate 0 x = 1 := by
  simp [reciprocalCoordinate]

@[simp] lemma reciprocalCoordinate_one (x : ℝ) :
    reciprocalCoordinate 1 x = (x + 1)⁻¹ := by
  simp [reciprocalCoordinate, reciprocalCoordinateDenominator]

lemma reciprocalCoordinateDenominator_pos (i : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 < reciprocalCoordinateDenominator i x := by
  apply Finset.prod_pos
  intro r hr
  simp only [Finset.mem_range] at hr
  positivity

lemma reciprocalCoordinate_pos (i : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 < reciprocalCoordinate i x := by
  exact inv_pos.mpr (reciprocalCoordinateDenominator_pos i hx)

lemma reciprocalCoordinate_nonneg (i : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ reciprocalCoordinate i x :=
  (reciprocalCoordinate_pos i hx).le

lemma reciprocalCoordinate_succ (i : ℕ) (x : ℝ) :
    reciprocalCoordinate (i + 1) x =
      reciprocalCoordinate i x * (x + (i + 1 : ℕ))⁻¹ := by
  rw [reciprocalCoordinate, reciprocalCoordinateDenominator_succ]
  exact mul_inv _ _

/-- Removing the initial factor from the denominator translates the argument. -/
lemma reciprocalCoordinateDenominator_shift (i : ℕ) (x : ℝ) :
    (x + 1) * reciprocalCoordinateDenominator i (x + 1) =
      reciprocalCoordinateDenominator (i + 1) x := by
  induction i with
  | zero => simp [reciprocalCoordinateDenominator]
  | succ i ih =>
      rw [reciprocalCoordinateDenominator_succ,
        reciprocalCoordinateDenominator_succ]
      rw [← ih]
      push_cast
      ring

/-- The elementary finite-difference identity for the reciprocal coordinates. -/
theorem reciprocalCoordinate_shift (i : ℕ) (hi : 1 ≤ i) {x : ℝ} (hx : 0 ≤ x) :
    reciprocalCoordinate i (x + 1) =
      reciprocalCoordinate i x - (i : ℝ) * reciprocalCoordinate (i + 1) x := by
  have hP : reciprocalCoordinateDenominator i x ≠ 0 :=
    ne_of_gt (reciprocalCoordinateDenominator_pos i hx)
  have hQ : reciprocalCoordinateDenominator i (x + 1) ≠ 0 :=
    ne_of_gt (reciprocalCoordinateDenominator_pos i (by positivity))
  have hx1 : x + 1 ≠ 0 := by positivity
  rw [reciprocalCoordinate, reciprocalCoordinate,
    reciprocalCoordinate, reciprocalCoordinateDenominator_succ]
  have hshift := reciprocalCoordinateDenominator_shift i x
  rw [reciprocalCoordinateDenominator_succ] at hshift
  field_simp
  push_cast at hshift ⊢
  nlinarith [hshift]

/-- A coordinate decreases when another positive factor is appended. -/
lemma reciprocalCoordinate_succ_le (i : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    reciprocalCoordinate (i + 1) x ≤ reciprocalCoordinate i x := by
  rw [reciprocalCoordinate_succ]
  apply mul_le_of_le_one_right (reciprocalCoordinate_nonneg i hx)
  apply (inv_le_one₀ (by positivity)).2
  have hi : (1 : ℝ) ≤ (i + 1 : ℕ) := by norm_cast; omega
  linarith

/-- Every nonempty coordinate is bounded by `1 / x` on the positive axis. -/
lemma reciprocalCoordinate_le_inv (i : ℕ) (hi : 1 ≤ i) {x : ℝ} (hx : 0 < x) :
    reciprocalCoordinate i x ≤ x⁻¹ := by
  induction i with
  | zero => omega
  | succ i ih =>
    cases i with
    | zero =>
      simpa using (inv_anti₀ hx (by linarith : x ≤ x + 1))
    | succ i =>
      exact (reciprocalCoordinate_succ_le (i + 1) hx.le).trans (ih (by omega))

/-! ## The finite partial-fraction identity -/

/-- Integral coefficients in the finite expansion of `f_i (x + k)` in the
coordinates `f_j x`.  The recursion is the finite-difference identity. -/
def reciprocalCoordinateCoefficients (i : ℕ) : ℕ → ℕ →₀ ℤ
  | 0 => Finsupp.single i 1
  | k + 1 => reciprocalCoordinateCoefficients i k -
      (i : ℤ) • reciprocalCoordinateCoefficients (i + 1) k

/-- Evaluate a finitely-supported integral linear combination of coordinates. -/
def reciprocalCoordinateCombination (c : ℕ →₀ ℤ) (x : ℝ) : ℝ :=
  c.sum fun j z => (z : ℝ) * reciprocalCoordinate j x

lemma reciprocalCoordinateCombination_sub (c d : ℕ →₀ ℤ) (x : ℝ) :
    reciprocalCoordinateCombination (c - d) x =
      reciprocalCoordinateCombination c x - reciprocalCoordinateCombination d x := by
  unfold reciprocalCoordinateCombination
  apply Finsupp.sum_sub_index
  intro j z w
  push_cast
  ring

lemma reciprocalCoordinateCombination_zsmul (m : ℤ) (c : ℕ →₀ ℤ) (x : ℝ) :
    reciprocalCoordinateCombination (m • c) x =
      (m : ℝ) * reciprocalCoordinateCombination c x := by
  unfold reciprocalCoordinateCombination
  rw [Finsupp.sum_smul_index (by intro j; simp)]
  simp only [Finsupp.sum, Int.cast_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Finite partial-fraction/finite-difference expansion.  In particular, with
`i = 1`, this expresses `1 / (x + k + 1)` as a finite integral linear
combination of `f_j x`. -/
theorem reciprocalCoordinate_add_nat (i k : ℕ) (hi : 1 ≤ i) {x : ℝ} (hx : 0 ≤ x) :
    reciprocalCoordinate i (x + k) =
      reciprocalCoordinateCombination (reciprocalCoordinateCoefficients i k) x := by
  induction k generalizing i x with
  | zero =>
      simp [reciprocalCoordinateCoefficients, reciprocalCoordinateCombination]
  | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc]
      rw [reciprocalCoordinate_shift i hi (by positivity)]
      rw [ih i hi hx, ih (i + 1) (by omega) hx]
      simp only [reciprocalCoordinateCoefficients, reciprocalCoordinateCombination_sub,
        reciprocalCoordinateCombination_zsmul]
      norm_cast

/-- The preceding expansion specialized to a single shifted reciprocal. -/
theorem shiftedReciprocal_eq_coordinateCombination (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x + (k + 1 : ℕ))⁻¹ =
      reciprocalCoordinateCombination (reciprocalCoordinateCoefficients 1 k) x := by
  have h := reciprocalCoordinate_add_nat 1 k (by omega) hx
  rw [reciprocalCoordinate_one] at h
  convert h using 1
  push_cast
  ring

/-! ## Summability and rationality transfer -/

/-- Reciprocal summability transfers to every positive coordinate and every
nonnegative integral translate of its argument. -/
theorem summable_reciprocalCoordinate
    (a : ℕ → ℕ) (ha : ∀ n, 1 ≤ a n)
    (hsum : Summable (fun n => (1 : ℝ) / a n))
    (i k : ℕ) (hi : 1 ≤ i) :
    Summable (fun n => reciprocalCoordinate i ((a n : ℝ) + k)) := by
  apply Summable.of_nonneg_of_le
      (fun n => reciprocalCoordinate_nonneg i (by positivity))
      (fun n => ?_) hsum
  have ha_pos : (0 : ℝ) < a n := by exact_mod_cast (ha n)
  calc
    reciprocalCoordinate i ((a n : ℝ) + k) ≤ ((a n : ℝ) + k)⁻¹ :=
      reciprocalCoordinate_le_inv i hi (by positivity)
    _ ≤ (a n : ℝ)⁻¹ := inv_anti₀ ha_pos
      (le_add_of_nonneg_right (Nat.cast_nonneg k))
    _ = (1 : ℝ) / a n := by simp [one_div]

/-- Positive integral translation preserves summability of a positive
reciprocal series. -/
theorem summable_shiftedReciprocal
    (a : ℕ → ℕ) (ha : ∀ n, 1 ≤ a n)
    (hsum : Summable (fun n => (1 : ℝ) / a n)) (t : ℕ) :
    Summable (fun n => (1 : ℝ) / ((a n : ℝ) + t)) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsum
  have ha_pos : (0 : ℝ) < a n := by exact_mod_cast (ha n)
  exact one_div_le_one_div_of_le ha_pos (le_add_of_nonneg_right (Nat.cast_nonneg t))

/-- If every positive reciprocal coordinate has rational sum, then every
positive natural translate of the reciprocal series has rational sum. -/
theorem rational_tsum_shift_of_rational_coordinate_tsums
    (a : ℕ → ℕ) (ha : ∀ n, 1 ≤ a n)
    (hsum : Summable (fun n => (1 : ℝ) / a n))
    (hcoord : ∀ i, 1 ≤ i →
      ∃ q : ℚ, (∑' n, reciprocalCoordinate i (a n : ℝ)) = (q : ℝ)) :
    ∀ t : ℕ, 1 ≤ t →
      ∃ q : ℚ, (∑' n, (1 : ℝ) / ((a n : ℝ) + t)) = (q : ℝ) := by
  have htranslated : ∀ k i : ℕ, 1 ≤ i →
      ∃ q : ℚ, (∑' n, reciprocalCoordinate i ((a n : ℝ) + k)) = (q : ℝ) := by
    intro k
    induction k with
    | zero =>
        intro i hi
        simpa using hcoord i hi
    | succ k ih =>
        intro i hi
        obtain ⟨q, hq⟩ := ih i hi
        obtain ⟨r, hr⟩ := ih (i + 1) (by omega)
        refine ⟨q - (i : ℚ) * r, ?_⟩
        have hfi := summable_reciprocalCoordinate a ha hsum i k hi
        have hgi := (summable_reciprocalCoordinate a ha hsum (i + 1) k (by omega)).mul_left
          (i : ℝ)
        rw [Nat.cast_succ]
        calc
          (∑' n, reciprocalCoordinate i ((a n : ℝ) + ((k : ℝ) + 1))) =
              ∑' n, (reciprocalCoordinate i ((a n : ℝ) + k) -
                (i : ℝ) * reciprocalCoordinate (i + 1) ((a n : ℝ) + k)) := by
                apply tsum_congr
                intro n
                simpa only [add_assoc] using reciprocalCoordinate_shift i hi
                  (show 0 ≤ (a n : ℝ) + k by positivity)
          _ = (∑' n, reciprocalCoordinate i ((a n : ℝ) + k)) -
              ∑' n, (i : ℝ) * reciprocalCoordinate (i + 1) ((a n : ℝ) + k) :=
                hfi.tsum_sub hgi
          _ = (q : ℝ) - (i : ℝ) * (r : ℝ) := by
                rw [hq, tsum_mul_left, hr]
          _ = ((q - (i : ℚ) * r : ℚ) : ℝ) := by push_cast; rfl
  intro t ht
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  obtain ⟨q, hq⟩ := htranslated k 1 (by omega)
  refine ⟨q, ?_⟩
  rw [← hq]
  apply tsum_congr
  intro n
  simp [reciprocalCoordinate, reciprocalCoordinateDenominator]
  ring

/-- `HasSum` form of `rational_tsum_shift_of_rational_coordinate_tsums`, useful
when the coordinate construction records both convergence and its rational
value in one hypothesis. -/
theorem rational_hasSum_shift_of_rational_coordinate_hasSums
    (a : ℕ → ℕ) (ha : ∀ n, 1 ≤ a n)
    (hsum : Summable (fun n => (1 : ℝ) / a n))
    (hcoord : ∀ i, 1 ≤ i →
      ∃ q : ℚ, HasSum (fun n => reciprocalCoordinate i (a n : ℝ)) (q : ℝ)) :
    ∀ t : ℕ, 1 ≤ t →
      ∃ q : ℚ, HasSum (fun n => (1 : ℝ) / ((a n : ℝ) + t)) (q : ℝ) := by
  have hcoord' : ∀ i, 1 ≤ i →
      ∃ q : ℚ, (∑' n, reciprocalCoordinate i (a n : ℝ)) = (q : ℝ) := by
    intro i hi
    obtain ⟨q, hq⟩ := hcoord i hi
    exact ⟨q, hq.tsum_eq⟩
  intro t ht
  obtain ⟨q, hq⟩ := rational_tsum_shift_of_rational_coordinate_tsums
    a ha hsum hcoord' t ht
  refine ⟨q, ?_⟩
  have hs := (summable_shiftedReciprocal a ha hsum t).hasSum
  simpa only [hq] using hs

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos266/Erdos266Block.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The finite block calculation for Erdős problem 266

This file contains the finite-dimensional part of the Kovač--Tao construction.
The coordinates are

`coord p x = 1 / ((x + 1) ⋯ (x + p))`.

The leading linear map obtained by perturbing the points
`N, 2N, ..., dN` is a diagonally rescaled Vandermonde matrix.  The main
rounding lemma below solves that real linear system, rounds the inverse image
coordinatewise, and records both the rounding error and a bound on the
integer offsets.  The final theorem combines this with any coordinatewise
quadratic estimate of the precise form used in the analytic part of the
construction.
-/

open scoped BigOperators

namespace Erdos266Block

noncomputable section

/-- The `p`-th triangular coordinate, with shifts `1, ..., p`. -/
def coord (p : ℕ) (x : ℝ) : ℝ :=
  ∏ r ∈ Finset.range p, (x + (r + 1 : ℕ))⁻¹

@[simp] lemma coord_zero (x : ℝ) : coord 0 x = 1 := by
  simp [coord]

lemma coord_succ (p : ℕ) (x : ℝ) :
    coord (p + 1) x = coord p x * (x + (p + 1 : ℕ))⁻¹ := by
  simp [coord, Finset.prod_range_succ, mul_comm]

/-- The logarithmic-derivative sum associated to `coord`. -/
def logSum (p : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.range p, (x + (r + 1 : ℕ))⁻¹

/-- The sum of squares occurring in the second derivative. -/
def squareSum (p : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.range p, (x + (r + 1 : ℕ))⁻¹ ^ 2

lemma hasDerivAt_shiftInv (r : ℕ) (x : ℝ) (hx : x + (r + 1 : ℕ) ≠ 0) :
    HasDerivAt (fun y : ℝ => (y + (r + 1 : ℕ))⁻¹)
      (-((x + (r + 1 : ℕ))⁻¹ ^ 2)) x := by
  simpa only [Function.comp_def, id_eq, one_mul, mul_one, inv_pow] using
    (hasDerivAt_inv hx).comp x
      ((hasDerivAt_id x).add_const ((r + 1 : ℕ) : ℝ))

lemma hasDerivAt_logSum (p : ℕ) (x : ℝ)
    (hx : ∀ r < p, x + (r + 1 : ℕ) ≠ 0) :
    HasDerivAt (logSum p) (-squareSum p x) x := by
  unfold logSum squareSum
  have h := HasDerivAt.fun_sum (u := Finset.range p)
    (A := fun (r : ℕ) (y : ℝ) => (y + (r + 1 : ℕ))⁻¹)
    (A' := fun r : ℕ => -((x + (r + 1 : ℕ))⁻¹ ^ 2))
    (fun r hr => hasDerivAt_shiftInv r x (hx r (Finset.mem_range.mp hr)))
  exact h.congr_deriv (by simp)

lemma hasDerivAt_coord (p : ℕ) (x : ℝ)
    (hx : ∀ r < p, x + (r + 1 : ℕ) ≠ 0) :
    HasDerivAt (coord p) (-coord p x * logSum p x) x := by
  unfold coord logSum
  have hprod := HasDerivAt.fun_finsetProd (u := Finset.range p)
    (f := fun r (y : ℝ) => (y + (r + 1 : ℕ))⁻¹)
    (f' := fun r : ℕ => -((x + (r + 1 : ℕ))⁻¹ ^ 2))
    (fun r hr => hasDerivAt_shiftInv r x (hx r (Finset.mem_range.mp hr)))
  refine hprod.congr_deriv ?_
  simp only [smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrp := Finset.mem_range.mp hr
  have hden := hx r hrp
  rw [← Finset.prod_erase_mul (Finset.range p)
    (fun j : ℕ => (x + (j + 1 : ℕ))⁻¹) (Finset.mem_range.mpr hrp)]
  field_simp

lemma hasDerivAt_coordDeriv (p : ℕ) (x : ℝ)
    (hx : ∀ r < p, x + (r + 1 : ℕ) ≠ 0) :
    HasDerivAt (fun y => -coord p y * logSum p y)
      (coord p x * (logSum p x ^ 2 + squareSum p x)) x := by
  have h := (hasDerivAt_coord p x hx).neg.mul (hasDerivAt_logSum p x hx)
  change HasDerivAt ((-coord p) * logSum p)
    (coord p x * (logSum p x ^ 2 + squareSum p x)) x
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply]
  ring

lemma coord_eq_reciprocalCoordinate (p : ℕ) (x : ℝ) :
    coord p x = Erdos266.reciprocalCoordinate p x := by
  simp [coord, Erdos266.reciprocalCoordinate,
    Erdos266.reciprocalCoordinateDenominator, Finset.prod_inv_distrib]

/-- A convenient twice-mean-value form of the quadratic Taylor estimate. -/
lemma quadratic_taylor_bound {f f' f'' : ℝ → ℝ} {a b K : ℝ}
    (hK : 0 ≤ K)
    (hf : ∀ y ∈ Set.uIcc a b, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.uIcc a b, HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.uIcc a b, |f'' y| ≤ K) :
    |f b - f a - f' a * (b - a)| ≤ K * |b - a| ^ 2 := by
  have hdist : ∀ y ∈ Set.uIcc a b, |f' y - f' a| ≤ K * |b - a| := by
    intro y hy
    have hmvt := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f') (f' := f'')
      (fun z hz => (hf' z hz).hasDerivWithinAt)
      (fun z hz => by simpa [Real.norm_eq_abs] using hbound z hz)
      Set.left_mem_uIcc hy
    have hya : |y - a| ≤ |b - a| := by
      rcases Set.mem_uIcc.mp hy with hy | hy
      · rw [abs_of_nonneg (sub_nonneg.mpr hy.1),
          abs_of_nonneg (sub_nonneg.mpr (hy.1.trans hy.2))]
        linarith
      · rw [abs_of_nonpos (sub_nonpos.mpr hy.2),
          abs_of_nonpos (sub_nonpos.mpr (hy.1.trans hy.2))]
        linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    exact hmvt.trans (mul_le_mul_of_nonneg_left hya hK)
  let g : ℝ → ℝ := f - fun y => f' a * y
  have hg : ∀ y ∈ Set.uIcc a b, HasDerivAt g (f' y - f' a) y := by
    intro y hy
    have hlin := (hasDerivAt_id y).const_mul (f' a)
    have hlin' : HasDerivAt (fun y : ℝ => f' a * y) (f' a) y := by
      simpa only [id_eq, mul_one] using hlin
    change HasDerivAt (f - fun y : ℝ => f' a * y) (f' y - f' a) y
    exact (hf y hy).sub hlin'
  have hmvt := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := fun y => f' y - f' a)
    (fun y hy => (hg y hy).hasDerivWithinAt)
    (fun y hy => by simpa [Real.norm_eq_abs] using hdist y hy)
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  change |(f b - f' a * b) - (f a - f' a * a)| ≤ _ at hmvt
  calc
    |f b - f a - f' a * (b - a)| =
        |(f b - f' a * b) - (f a - f' a * a)| := by ring_nf
    _ ≤ (K * |b - a|) * |b - a| := hmvt
    _ = K * |b - a| ^ 2 := by ring

lemma abs_sub_left_le_abs_sub_right_of_mem_uIcc {a b y : ℝ}
    (hy : y ∈ Set.uIcc a b) : |y - a| ≤ |b - a| := by
  rcases Set.mem_uIcc.mp hy with hy | hy
  · rw [abs_of_nonneg (sub_nonneg.mpr hy.1),
      abs_of_nonneg (sub_nonneg.mpr (hy.1.trans hy.2))]
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr hy.2),
      abs_of_nonpos (sub_nonpos.mpr (hy.1.trans hy.2))]
    linarith

lemma coord_second_deriv_bound (p : ℕ) {X y : ℝ} (hX : 0 < X)
    (hy : X / 2 ≤ y) :
    |coord p y * (logSum p y ^ 2 + squareSum p y)| ≤
      2 ^ (p + 2) * ((p : ℝ) ^ 2 + p) / X ^ (p + 2) := by
  let b : ℝ := 2 / X
  have hb : 0 ≤ b := by positivity
  have hfactor : ∀ r < p, 0 ≤ (y + (r + 1 : ℕ))⁻¹ ∧
      (y + (r + 1 : ℕ))⁻¹ ≤ b := by
    intro r hr
    have hden : X / 2 ≤ y + (r + 1 : ℕ) := by
      have : (0 : ℝ) ≤ (r + 1 : ℕ) := by positivity
      linarith
    have hdenpos : 0 < y + (r + 1 : ℕ) := by linarith
    constructor
    · positivity
    · calc
        (y + (r + 1 : ℕ))⁻¹ ≤ (X / 2)⁻¹ := by
          simpa [one_div] using one_div_le_one_div_of_le (half_pos hX) hden
        _ = b := by
          dsimp [b]
          field_simp
  have hc0 : 0 ≤ coord p y := by
    unfold coord
    exact Finset.prod_nonneg fun r hr => (hfactor r (Finset.mem_range.mp hr)).1
  have hcb : coord p y ≤ b ^ p := by
    unfold coord
    calc
      ∏ r ∈ Finset.range p, (y + (r + 1 : ℕ))⁻¹ ≤
          ∏ _r ∈ Finset.range p, b := by
        exact Finset.prod_le_prod
          (fun r hr => (hfactor r (Finset.mem_range.mp hr)).1) fun r hr =>
            (hfactor r (Finset.mem_range.mp hr)).2
      _ = b ^ p := by simp
  have hl0 : 0 ≤ logSum p y := by
    unfold logSum
    exact Finset.sum_nonneg fun r hr => (hfactor r (Finset.mem_range.mp hr)).1
  have hlb : logSum p y ≤ p * b := by
    unfold logSum
    calc
      ∑ r ∈ Finset.range p, (y + (r + 1 : ℕ))⁻¹ ≤
          ∑ _r ∈ Finset.range p, b :=
        Finset.sum_le_sum fun r hr => (hfactor r (Finset.mem_range.mp hr)).2
      _ = p * b := by simp
  have hs0 : 0 ≤ squareSum p y := by
    unfold squareSum
    positivity
  have hsb : squareSum p y ≤ p * b ^ 2 := by
    unfold squareSum
    calc
      ∑ r ∈ Finset.range p, (y + (r + 1 : ℕ))⁻¹ ^ 2 ≤
          ∑ _r ∈ Finset.range p, b ^ 2 := by
        apply Finset.sum_le_sum
        intro r hr
        exact pow_le_pow_left₀ (hfactor r (Finset.mem_range.mp hr)).1
          (hfactor r (Finset.mem_range.mp hr)).2 2
      _ = p * b ^ 2 := by simp
  rw [abs_of_nonneg (mul_nonneg hc0 (add_nonneg (sq_nonneg _) hs0))]
  calc
    coord p y * (logSum p y ^ 2 + squareSum p y) ≤
        b ^ p * ((p * b) ^ 2 + p * b ^ 2) := by
      gcongr
    _ = 2 ^ (p + 2) * ((p : ℝ) ^ 2 + p) / X ^ (p + 2) := by
      dsimp [b]
      have hX0 : X ≠ 0 := ne_of_gt hX
      rw [div_pow]
      field_simp [hX0, pow_add]
      simp only [pow_add]
      ring

/-! The derivative mismatch is most conveniently estimated after scaling
`X` to `1`. -/

def normalizedCoord (p : ℕ) (u : ℝ) : ℝ :=
  ∏ r ∈ Finset.range p, (1 + (r + 1 : ℕ) * u)⁻¹

def normalizedPlainSum (p : ℕ) (u : ℝ) : ℝ :=
  ∑ r ∈ Finset.range p, (1 + (r + 1 : ℕ) * u)⁻¹

def normalizedWeightedSum (p : ℕ) (u : ℝ) : ℝ :=
  ∑ r ∈ Finset.range p,
    ((r + 1 : ℕ) : ℝ) * (1 + (r + 1 : ℕ) * u)⁻¹

def normalizedWeightedSquareSum (p : ℕ) (u : ℝ) : ℝ :=
  ∑ r ∈ Finset.range p,
    ((r + 1 : ℕ) : ℝ) * (1 + (r + 1 : ℕ) * u)⁻¹ ^ 2

def normalizedH (p : ℕ) (u : ℝ) : ℝ :=
  normalizedCoord p u * normalizedPlainSum p u

def weightTotal (p : ℕ) : ℝ :=
  ∑ r ∈ Finset.range p, ((r + 1 : ℕ) : ℝ)

lemma hasDerivAt_normalizedInv (r : ℕ) (u : ℝ)
    (hu : 1 + (r + 1 : ℕ) * u ≠ 0) :
    HasDerivAt (fun v : ℝ => (1 + (r + 1 : ℕ) * v)⁻¹)
      (-((r + 1 : ℕ) : ℝ) * (1 + (r + 1 : ℕ) * u)⁻¹ ^ 2) u := by
  have ha : HasDerivAt (fun v : ℝ => 1 + ((r + 1 : ℕ) : ℝ) * v)
      ((r + 1 : ℕ) : ℝ) u := by
    have hc := (hasDerivAt_id u).const_mul (((r + 1 : ℕ) : ℝ))
    simpa only [id_eq, mul_one] using
      hc.const_add 1
  have h := (hasDerivAt_inv hu).comp u ha
  change HasDerivAt ((fun y : ℝ => y⁻¹) ∘
    fun v : ℝ => 1 + ((r + 1 : ℕ) : ℝ) * v)
      (-((r + 1 : ℕ) : ℝ) * (1 + (r + 1 : ℕ) * u)⁻¹ ^ 2) u
  refine h.congr_deriv ?_
  rw [inv_pow]
  ring

lemma hasDerivAt_normalizedPlainSum (p : ℕ) (u : ℝ)
    (hu : ∀ r < p, 1 + (r + 1 : ℕ) * u ≠ 0) :
    HasDerivAt (normalizedPlainSum p) (-normalizedWeightedSquareSum p u) u := by
  unfold normalizedPlainSum normalizedWeightedSquareSum
  have h := HasDerivAt.fun_sum (u := Finset.range p)
    (A := fun (r : ℕ) (v : ℝ) => (1 + (r + 1 : ℕ) * v)⁻¹)
    (A' := fun r : ℕ =>
      -((r + 1 : ℕ) : ℝ) * (1 + (r + 1 : ℕ) * u)⁻¹ ^ 2)
    (fun r hr => hasDerivAt_normalizedInv r u (hu r (Finset.mem_range.mp hr)))
  refine h.congr_deriv ?_
  calc
    (∑ i ∈ Finset.range p,
        -((i + 1 : ℕ) : ℝ) * (1 + (i + 1 : ℕ) * u)⁻¹ ^ 2) =
      ∑ i ∈ Finset.range p,
        -(((i + 1 : ℕ) : ℝ) * (1 + (i + 1 : ℕ) * u)⁻¹ ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = -(∑ i ∈ Finset.range p,
        ((i + 1 : ℕ) : ℝ) * (1 + (i + 1 : ℕ) * u)⁻¹ ^ 2) := by
          rw [Finset.sum_neg_distrib]

lemma hasDerivAt_normalizedCoord (p : ℕ) (u : ℝ)
    (hu : ∀ r < p, 1 + (r + 1 : ℕ) * u ≠ 0) :
    HasDerivAt (normalizedCoord p)
      (-normalizedCoord p u * normalizedWeightedSum p u) u := by
  unfold normalizedCoord normalizedWeightedSum
  have hprod := HasDerivAt.fun_finsetProd (u := Finset.range p)
    (f := fun (r : ℕ) (v : ℝ) => (1 + (r + 1 : ℕ) * v)⁻¹)
    (f' := fun r : ℕ =>
      -((r + 1 : ℕ) : ℝ) * (1 + (r + 1 : ℕ) * u)⁻¹ ^ 2)
    (fun r hr => hasDerivAt_normalizedInv r u (hu r (Finset.mem_range.mp hr)))
  refine hprod.congr_deriv ?_
  simp only [smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrp := Finset.mem_range.mp hr
  have hden := hu r hrp
  rw [← Finset.prod_erase_mul (Finset.range p)
    (fun j : ℕ => (1 + (j + 1 : ℕ) * u)⁻¹) (Finset.mem_range.mpr hrp)]
  field_simp
  ac_rfl

lemma hasDerivAt_normalizedH (p : ℕ) (u : ℝ)
    (hu : ∀ r < p, 1 + (r + 1 : ℕ) * u ≠ 0) :
    HasDerivAt (normalizedH p)
      (-normalizedCoord p u *
        (normalizedWeightedSum p u * normalizedPlainSum p u +
          normalizedWeightedSquareSum p u)) u := by
  unfold normalizedH
  have h := (hasDerivAt_normalizedCoord p u hu).mul
    (hasDerivAt_normalizedPlainSum p u hu)
  refine h.congr_deriv ?_
  ring

lemma normalizedH_deriv_bound (p : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |-normalizedCoord p u *
        (normalizedWeightedSum p u * normalizedPlainSum p u +
          normalizedWeightedSquareSum p u)| ≤
      weightTotal p * (p : ℝ) + weightTotal p := by
  have hfactor : ∀ r < p, 0 ≤ (1 + (r + 1 : ℕ) * u)⁻¹ ∧
      (1 + (r + 1 : ℕ) * u)⁻¹ ≤ 1 := by
    intro r hr
    have hd : (1 : ℝ) ≤ 1 + (r + 1 : ℕ) * u := by
      have : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) * u :=
        mul_nonneg (by positivity) hu
      linarith
    constructor
    · positivity
    · exact inv_le_one_of_one_le₀ hd
  have hc0 : 0 ≤ normalizedCoord p u := by
    unfold normalizedCoord
    exact Finset.prod_nonneg fun r hr => (hfactor r (Finset.mem_range.mp hr)).1
  have hc1 : normalizedCoord p u ≤ 1 := by
    unfold normalizedCoord
    exact Finset.prod_le_one (fun r hr => (hfactor r (Finset.mem_range.mp hr)).1)
      (fun r hr => (hfactor r (Finset.mem_range.mp hr)).2)
  have hp0 : 0 ≤ normalizedPlainSum p u := by
    unfold normalizedPlainSum
    exact Finset.sum_nonneg fun r hr => (hfactor r (Finset.mem_range.mp hr)).1
  have hp1 : normalizedPlainSum p u ≤ p := by
    unfold normalizedPlainSum
    calc
      ∑ r ∈ Finset.range p, (1 + (r + 1 : ℕ) * u)⁻¹ ≤
          ∑ _r ∈ Finset.range p, (1 : ℝ) :=
        Finset.sum_le_sum fun r hr => (hfactor r (Finset.mem_range.mp hr)).2
      _ = p := by simp
  have hw0 : 0 ≤ normalizedWeightedSum p u := by
    unfold normalizedWeightedSum
    positivity
  have hw1 : normalizedWeightedSum p u ≤ weightTotal p := by
    unfold normalizedWeightedSum weightTotal
    exact Finset.sum_le_sum fun r hr => by
      calc
        ((r + 1 : ℕ) : ℝ) * (1 + (r + 1 : ℕ) * u)⁻¹ ≤
            ((r + 1 : ℕ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (hfactor r (Finset.mem_range.mp hr)).2 (by positivity)
        _ = ((r + 1 : ℕ) : ℝ) := by ring
  have hs0 : 0 ≤ normalizedWeightedSquareSum p u := by
    unfold normalizedWeightedSquareSum
    positivity
  have hs1 : normalizedWeightedSquareSum p u ≤ weightTotal p := by
    unfold normalizedWeightedSquareSum weightTotal
    apply Finset.sum_le_sum
    intro r hr
    have hf := hfactor r (Finset.mem_range.mp hr)
    calc
      ((r + 1 : ℕ) : ℝ) * (1 + (r + 1 : ℕ) * u)⁻¹ ^ 2 ≤
          ((r + 1 : ℕ) : ℝ) * 1 ^ 2 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hf.1 hf.2 2) (by positivity)
      _ = ((r + 1 : ℕ) : ℝ) := by ring
  have hwt0 : 0 ≤ weightTotal p := by
    unfold weightTotal
    positivity
  have habs : |-normalizedCoord p u *
      (normalizedWeightedSum p u * normalizedPlainSum p u +
        normalizedWeightedSquareSum p u)| =
      normalizedCoord p u *
        (normalizedWeightedSum p u * normalizedPlainSum p u +
          normalizedWeightedSquareSum p u) := by
    rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc0)
      (add_nonneg (mul_nonneg hw0 hp0) hs0))]
    ring
  rw [habs]
  calc
    normalizedCoord p u *
        (normalizedWeightedSum p u * normalizedPlainSum p u +
          normalizedWeightedSquareSum p u) ≤
      1 * (weightTotal p * (p : ℝ) + weightTotal p) := by gcongr
    _ = weightTotal p * (p : ℝ) + weightTotal p := by ring

@[simp] lemma normalizedH_zero (p : ℕ) : normalizedH p 0 = p := by
  simp [normalizedH, normalizedCoord, normalizedPlainSum]

lemma normalizedH_sub_bound (p : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |normalizedH p u - p| ≤
      (weightTotal p * (p : ℝ) + weightTotal p) * u := by
  let K : ℝ := weightTotal p * (p : ℝ) + weightTotal p
  have hderiv : ∀ y ∈ Set.Icc (0 : ℝ) u,
      HasDerivAt (normalizedH p)
        (-normalizedCoord p y *
          (normalizedWeightedSum p y * normalizedPlainSum p y +
            normalizedWeightedSquareSum p y)) y := by
    intro y hy
    apply hasDerivAt_normalizedH
    intro r hr
    have : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) * y :=
      mul_nonneg (by positivity) hy.1
    linarith
  have hK : ∀ y ∈ Set.Icc (0 : ℝ) u,
      ‖-normalizedCoord p y *
        (normalizedWeightedSum p y * normalizedPlainSum p y +
          normalizedWeightedSquareSum p y)‖ ≤ K := by
    intro y hy
    simpa [K, Real.norm_eq_abs] using normalizedH_deriv_bound p hy.1
  have hmvt := (convex_Icc (0 : ℝ) u).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := normalizedH p)
    (f' := fun y => -normalizedCoord p y *
      (normalizedWeightedSum p y * normalizedPlainSum p y +
        normalizedWeightedSquareSum p y))
    (fun y hy => (hderiv y hy).hasDerivWithinAt) hK
    (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu)
  simpa [K, Real.norm_eq_abs, abs_of_nonneg hu] using hmvt

lemma coord_scale (p : ℕ) {X : ℝ} (hX : X ≠ 0) :
    coord p X = X⁻¹ ^ p * normalizedCoord p X⁻¹ := by
  unfold coord normalizedCoord
  calc
    ∏ r ∈ Finset.range p, (X + (r + 1 : ℕ))⁻¹ =
        ∏ r ∈ Finset.range p,
          (X⁻¹ * (1 + (r + 1 : ℕ) * X⁻¹)⁻¹) := by
      apply Finset.prod_congr rfl
      intro r hr
      field_simp
    _ = (∏ _r ∈ Finset.range p, X⁻¹) *
        ∏ r ∈ Finset.range p, (1 + (r + 1 : ℕ) * X⁻¹)⁻¹ := by
      rw [Finset.prod_mul_distrib]
    _ = X⁻¹ ^ p * ∏ r ∈ Finset.range p,
        (1 + (r + 1 : ℕ) * X⁻¹)⁻¹ := by simp

lemma logSum_scale (p : ℕ) {X : ℝ} (hX : X ≠ 0) :
    logSum p X = X⁻¹ * normalizedPlainSum p X⁻¹ := by
  unfold logSum normalizedPlainSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  field_simp

lemma coord_mul_logSum_scale (p : ℕ) {X : ℝ} (hX : X ≠ 0) :
    coord p X * logSum p X = normalizedH p X⁻¹ / X ^ (p + 1) := by
  rw [coord_scale p hX, logSum_scale p hX]
  rw [eq_div_iff (pow_ne_zero (p + 1) hX)]
  unfold normalizedH
  rw [pow_add, pow_one]
  have hp : X⁻¹ ^ p * X ^ p = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hX, one_pow]
  calc
    (X⁻¹ ^ p * normalizedCoord p X⁻¹) *
        (X⁻¹ * normalizedPlainSum p X⁻¹) * (X ^ p * X) =
      (X⁻¹ ^ p * X ^ p) * (X⁻¹ * X) *
        (normalizedCoord p X⁻¹ * normalizedPlainSum p X⁻¹) := by ring
    _ = normalizedCoord p X⁻¹ * normalizedPlainSum p X⁻¹ := by
      rw [hp, inv_mul_cancel₀ hX]
      ring

lemma coord_deriv_mismatch_bound (p : ℕ) {X : ℝ} (hX : 0 < X) :
    |coord p X * logSum p X - (p : ℝ) / X ^ (p + 1)| ≤
      (weightTotal p * (p : ℝ) + weightTotal p) / X ^ (p + 2) := by
  have hX0 : X ≠ 0 := ne_of_gt hX
  have hu : 0 ≤ X⁻¹ := by positivity
  have hnorm := normalizedH_sub_bound p hu
  rw [coord_mul_logSum_scale p hX0]
  have hpow : 0 < X ^ (p + 1) := by positivity
  calc
    |normalizedH p X⁻¹ / X ^ (p + 1) - (p : ℝ) / X ^ (p + 1)| =
        |normalizedH p X⁻¹ - p| / X ^ (p + 1) := by
          rw [← sub_div, abs_div, abs_of_pos hpow]
    _ ≤ ((weightTotal p * (p : ℝ) + weightTotal p) * X⁻¹) /
        X ^ (p + 1) := div_le_div_of_nonneg_right hnorm hpow.le
    _ = (weightTotal p * (p : ℝ) + weightTotal p) / X ^ (p + 2) := by
      field_simp [hX0, pow_add]
      ring

/-- A deliberately coarse constant for the one-variable local estimate. -/
def localConstant (p : ℕ) : ℝ :=
  2 ^ (p + 2) * ((p : ℝ) ^ 2 + p) +
    (weightTotal p * (p : ℝ) + weightTotal p)

lemma localConstant_nonneg (p : ℕ) : 0 ≤ localConstant p := by
  unfold localConstant weightTotal
  positivity

/-- The local quadratic estimate for the actual shifted-product coordinate. -/
theorem coord_local_quadratic (p : ℕ) (hp : 1 ≤ p) (X : ℕ) (n : ℤ)
    (hX : 0 < X) (hn : |(n : ℝ)| ≤ (X : ℝ) / (4 * p)) :
    |coord p X - coord p ((X : ℝ) + n) -
        (p : ℝ) * n / (X : ℝ) ^ (p + 1)| ≤
      localConstant p * (n : ℝ) ^ 2 / (X : ℝ) ^ (p + 2) := by
  by_cases hn0 : n = 0
  · subst n
    simp
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hnHalf : |(n : ℝ)| ≤ (X : ℝ) / 2 := by
    calc
      |(n : ℝ)| ≤ (X : ℝ) / (4 * p) := hn
      _ ≤ (X : ℝ) / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have hinter : ∀ y ∈ Set.uIcc (X : ℝ) ((X : ℝ) + n),
      (X : ℝ) / 2 ≤ y := by
    intro y hy
    have hdist := abs_sub_left_le_abs_sub_right_of_mem_uIcc hy
    have hdist' : |y - (X : ℝ)| ≤ (X : ℝ) / 2 := by
      refine hdist.trans ?_
      simpa using hnHalf
    exact (abs_le.mp hdist').1 |> fun h => by linarith
  have hnonzero : ∀ y ∈ Set.uIcc (X : ℝ) ((X : ℝ) + n),
      ∀ r < p, y + (r + 1 : ℕ) ≠ 0 := by
    intro y hy r hr
    have hypos : 0 < y := (half_pos hXR).trans_le (hinter y hy)
    positivity
  let KT : ℝ := 2 ^ (p + 2) * ((p : ℝ) ^ 2 + p)
  let KM : ℝ := weightTotal p * (p : ℝ) + weightTotal p
  have hKT : 0 ≤ KT := by
    dsimp [KT]
    positivity
  have hTaylor := quadratic_taylor_bound
    (f := coord p)
    (f' := fun y => -coord p y * logSum p y)
    (f'' := fun y => coord p y * (logSum p y ^ 2 + squareSum p y))
    (a := (X : ℝ)) (b := (X : ℝ) + n)
    (K := KT / (X : ℝ) ^ (p + 2))
    (div_nonneg hKT (by positivity))
    (fun y hy => hasDerivAt_coord p y (hnonzero y hy))
    (fun y hy => hasDerivAt_coordDeriv p y (hnonzero y hy))
    (fun y hy => by
      simpa [KT] using coord_second_deriv_bound p hXR (hinter y hy))
  have hTaylor' :
      |coord p ((X : ℝ) + n) - coord p X +
          (coord p X * logSum p X) * n| ≤
        (KT / (X : ℝ) ^ (p + 2)) * |(n : ℝ)| ^ 2 := by
    convert hTaylor using 1 <;> ring
  have hMismatch :
      |coord p X * logSum p X - (p : ℝ) / (X : ℝ) ^ (p + 1)| ≤
        KM / (X : ℝ) ^ (p + 2) := by
    simpa [KM] using coord_deriv_mismatch_bound p hXR
  have hnOne : (1 : ℝ) ≤ |(n : ℝ)| := by
    have hi : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    exact_mod_cast hi
  have hKM : 0 ≤ KM := by
    dsimp [KM, weightTotal]
    positivity
  have hXp : 0 < (X : ℝ) ^ (p + 2) := by positivity
  have hdecomp :
      coord p X - coord p ((X : ℝ) + n) -
          (p : ℝ) * n / (X : ℝ) ^ (p + 1) =
        -(coord p ((X : ℝ) + n) - coord p X +
          (coord p X * logSum p X) * n) +
        n * (coord p X * logSum p X - (p : ℝ) / (X : ℝ) ^ (p + 1)) := by
    ring
  rw [hdecomp]
  let T : ℝ := coord p ((X : ℝ) + n) - coord p X +
    (coord p X * logSum p X) * n
  let E : ℝ := coord p X * logSum p X - (p : ℝ) / (X : ℝ) ^ (p + 1)
  calc
    |-(coord p ((X : ℝ) + n) - coord p X +
          (coord p X * logSum p X) * n) +
        n * (coord p X * logSum p X - (p : ℝ) / (X : ℝ) ^ (p + 1))| =
      |-T + (n : ℝ) * E| := by rfl
    _ ≤ |-T| + |(n : ℝ) * E| := abs_add_le _ _
    _ =
      |coord p ((X : ℝ) + n) - coord p X +
          (coord p X * logSum p X) * n| +
        |(n : ℝ)| * |coord p X * logSum p X -
          (p : ℝ) / (X : ℝ) ^ (p + 1)| := by
      simp only [abs_neg, abs_mul]
      rfl
    _ ≤ (KT / (X : ℝ) ^ (p + 2)) * |(n : ℝ)| ^ 2 +
        |(n : ℝ)| * (KM / (X : ℝ) ^ (p + 2)) :=
      add_le_add hTaylor'
        (mul_le_mul_of_nonneg_left hMismatch (abs_nonneg (n : ℝ)))
    _ ≤ (KT / (X : ℝ) ^ (p + 2)) * |(n : ℝ)| ^ 2 +
        |(n : ℝ)| ^ 2 * (KM / (X : ℝ) ^ (p + 2)) := by
      gcongr
      calc
        |(n : ℝ)| = |(n : ℝ)| * 1 := by ring
        _ ≤ |(n : ℝ)| * |(n : ℝ)| :=
          mul_le_mul_of_nonneg_left hnOne (abs_nonneg _)
        _ = |(n : ℝ)| ^ 2 := by ring
    _ = localConstant p * (n : ℝ) ^ 2 / (X : ℝ) ^ (p + 2) := by
      rw [sq_abs]
      dsimp [KT, KM, localConstant]
      ring

/-- The reciprocal points used in the Vandermonde linearization. -/
def nodes (d : ℕ) (j : Fin d) : ℝ := ((j.1 + 1 : ℕ) : ℝ)⁻¹

/--
The matrix with entries `(j+1)^(-(i+2))`.  It is presented as a transpose
Vandermonde matrix times a nonsingular diagonal matrix; this makes its
nonsingularity transparent to Mathlib.
-/
def blockMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.vandermonde (nodes d)).transpose * Matrix.diagonal (fun j => (nodes d j) ^ 2)

lemma nodes_ne_zero (d : ℕ) (j : Fin d) : nodes d j ≠ 0 := by
  exact inv_ne_zero (by positivity)

lemma nodes_injective (d : ℕ) : Function.Injective (nodes d) := by
  intro i j hij
  have hcast : ((i.1 + 1 : ℕ) : ℝ) = ((j.1 + 1 : ℕ) : ℝ) := by
    exact inv_inj.mp (by simpa [nodes] using hij)
  have hnat : i.1 + 1 = j.1 + 1 := by exact_mod_cast hcast
  exact Fin.ext (Nat.add_right_cancel hnat)

lemma det_blockMatrix_ne_zero (d : ℕ) : (blockMatrix d).det ≠ 0 := by
  rw [blockMatrix, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  exact mul_ne_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr (nodes_injective d))
    (Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero 2 (nodes_ne_zero d j))

lemma blockMatrix_apply (d : ℕ) (i j : Fin d) :
    blockMatrix d i j = (((j.1 + 1 : ℕ) : ℝ) ^ (i.1 + 2))⁻¹ := by
  classical
  rw [blockMatrix, Matrix.mul_diagonal]
  simp [nodes, Matrix.vandermonde_apply, pow_add, inv_pow, mul_comm]

/-- The sum of the absolute values of all entries of a finite matrix. -/
def entryMass {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ i, ∑ j, |A i j|

lemma entry_abs_le_entryMass {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d) : |A i j| ≤ entryMass A := by
  unfold entryMass
  have hrow : |A i j| ≤ ∑ k, |A i k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (A i k)) (Finset.mem_univ j)
  have hall : (∑ k, |A i k|) ≤ ∑ k, ∑ l, |A k l| :=
    Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg (A k l)) (Finset.mem_univ i)
  exact hrow.trans hall

lemma rowMass_le_entryMass {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) : (∑ j, |A i j|) ≤ entryMass A := by
  unfold entryMass
  exact Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg (A k l)) (Finset.mem_univ i)

/--
Coordinatewise inverse-matrix rounding.  Besides the usual error estimate,
this version records a uniform bound for the rounded integer vector.  The
smallness threshold is deliberately coarse; only its positivity matters in
the diagonal construction.
-/
theorem inverse_matrix_rounding {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.det ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ (M : ℕ) (hM : 1 ≤ M) (x : Fin d → ℝ),
        (∀ i, |x i| ≤ ε * M) →
        ∃ z : Fin d → ℤ,
          (∀ j, |z j| ≤ (M : ℝ)) ∧
          ∀ i, |A.mulVec (fun j => (z j : ℝ)) i - x i| ≤ entryMass A / 2 := by
  let B : Matrix (Fin d) (Fin d) ℝ := A⁻¹
  let C : ℝ := entryMass B
  let ε : ℝ := 1 / (2 * (C + 1))
  have hC : 0 ≤ C := by
    unfold C entryMass
    positivity
  have hden : 0 < 2 * (C + 1) := by positivity
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    rw [div_le_one hden]
    linarith
  refine ⟨ε, hε, hε1, ?_⟩
  intro M hM x hx
  let y : Fin d → ℝ := B.mulVec x
  let z : Fin d → ℤ := fun j => round (y j)
  refine ⟨z, ?_, ?_⟩
  · intro j
    have hy : |y j| ≤ C * (ε * M) := by
      calc
        |y j| = |∑ k, B j k * x k| := by rfl
        _ ≤ ∑ k, |B j k * x k| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k, |B j k| * |x k| := by simp only [abs_mul]
        _ ≤ ∑ k, |B j k| * (ε * M) := by
          exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hx k) (abs_nonneg _)
        _ = (∑ k, |B j k|) * (ε * M) := by rw [Finset.sum_mul]
        _ ≤ C * (ε * M) := by
          exact mul_le_mul_of_nonneg_right (rowMass_le_entryMass B j) (mul_nonneg hε.le (by positivity))
    have hyhalf : |y j| ≤ (M : ℝ) / 2 := by
      have hCε : C * ε ≤ (1 : ℝ) / 2 := by
        dsimp [ε]
        calc
          C * (1 / (2 * (C + 1))) = C / (2 * (C + 1)) := by ring
          _ ≤ (1 : ℝ) / 2 := (div_le_iff₀ hden).2 (by nlinarith)
      calc
        |y j| ≤ C * (ε * M) := hy
        _ = (C * ε) * M := by ring
        _ ≤ ((1 : ℝ) / 2) * M :=
          mul_le_mul_of_nonneg_right hCε (by positivity)
        _ = (M : ℝ) / 2 := by ring
    have hround := abs_sub_round (y j)
    have htri : |(z j : ℝ)| ≤ |y j| + |y j - (z j : ℝ)| := by
      calc
        |(z j : ℝ)| = |y j - (y j - (z j : ℝ))| := by ring_nf
        _ ≤ |y j| + |y j - (z j : ℝ)| := abs_sub _ _
    have hzreal : |(z j : ℝ)| ≤ (M : ℝ) := by
      calc
        |(z j : ℝ)| ≤ |y j| + |y j - (z j : ℝ)| := htri
        _ ≤ (M : ℝ) / 2 + 1 / 2 := add_le_add hyhalf (by simpa [z] using hround)
        _ ≤ (M : ℝ) := by
          have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
          linarith
    simpa using hzreal
  · intro i
    have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
    have hcancel : A.mulVec y = x := by
      rw [show y = B.mulVec x by rfl, Matrix.mulVec_mulVec]
      rw [show A * B = 1 by exact Matrix.mul_nonsing_inv A hunit]
      simp
    calc
      |A.mulVec (fun j => (z j : ℝ)) i - x i|
          = |∑ j, A i j * ((z j : ℝ) - y j)| := by
              rw [← hcancel]
              simp only [Matrix.mulVec, dotProduct]
              rw [← Finset.sum_sub_distrib]
              apply congrArg abs
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ ≤ ∑ j, |A i j * ((z j : ℝ) - y j)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |A i j| * |y j - (z j : ℝ)| := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_mul, abs_sub_comm]
      _ ≤ ∑ j, |A i j| * (1 / 2 : ℝ) := by
            exact Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (by simpa [z] using abs_sub_round (y j)) (abs_nonneg _)
      _ = (∑ j, |A i j|) / 2 := by rw [← Finset.sum_mul]; ring
      _ ≤ entryMass A / 2 := by
            exact div_le_div_of_nonneg_right (rowMass_le_entryMass A i) (by norm_num)

/-- A dimension-dependent radius, fixed before any block scale is selected. -/
def blockEpsilon (d : ℕ) : ℝ :=
  Classical.choose (inverse_matrix_rounding (blockMatrix d) (det_blockMatrix_ne_zero d))

theorem blockEpsilon_spec (d : ℕ) :
    0 < blockEpsilon d ∧ blockEpsilon d ≤ 1 ∧
      ∀ (M : ℕ) (hM : 1 ≤ M) (x : Fin d → ℝ),
        (∀ i, |x i| ≤ blockEpsilon d * M) →
        ∃ z : Fin d → ℤ,
          (∀ j, |z j| ≤ (M : ℝ)) ∧
          ∀ i, |(blockMatrix d).mulVec (fun j => (z j : ℝ)) i - x i| ≤
            entryMass (blockMatrix d) / 2 :=
  Classical.choose_spec
    (inverse_matrix_rounding (blockMatrix d) (det_blockMatrix_ne_zero d))

lemma blockEpsilon_pos (d : ℕ) : 0 < blockEpsilon d := (blockEpsilon_spec d).1

lemma blockEpsilon_le_one (d : ℕ) : blockEpsilon d ≤ 1 := (blockEpsilon_spec d).2.1

/-! ## The local estimate and the nonlinear block -/

/--
The local quadratic estimate needed at coordinate `i`.  The coordinate has
`i+1` factors, and its leading derivative at scale `X` is
`-(i+1) / X^(i+2)`.
-/
def LocalQuadraticEstimate {d : ℕ} (C : Fin d → ℝ) : Prop :=
  (∀ i, 0 ≤ C i) ∧
  ∀ (i : Fin d) (X : ℕ) (n : ℤ), 0 < X →
    |(n : ℝ)| ≤ (X : ℝ) / (4 * (i.1 + 1 : ℕ)) →
    |coord (i.1 + 1) X - coord (i.1 + 1) ((X : ℝ) + n) -
        ((i.1 + 1 : ℕ) : ℝ) * n / (X : ℝ) ^ (i.1 + 2)| ≤
      C i * (n : ℝ) ^ 2 / (X : ℝ) ^ (i.1 + 3)

/-- The canonical local-error constants in dimension `d`. -/
def localConstants (d : ℕ) : Fin d → ℝ :=
  fun i => localConstant (i.1 + 1)

/-- The shifted-product coordinates satisfy the required local estimate. -/
theorem localQuadraticEstimate (d : ℕ) :
    LocalQuadraticEstimate (localConstants d) := by
  constructor
  · intro i
    exact localConstant_nonneg _
  · intro i X n hX hn
    simpa [localConstants, Nat.add_assoc] using
      coord_local_quadratic (i.1 + 1) (by omega) X n hX hn

/-- A uniform error constant for all coordinates in dimension `d`. -/
def blockD (d : ℕ) : ℝ :=
  1 + (d : ℝ) * entryMass (blockMatrix d) +
    (d : ℝ) * ∑ i : Fin d, localConstants d i

lemma blockD_nonneg (d : ℕ) : 0 ≤ blockD d := by
  have hm : 0 ≤ entryMass (blockMatrix d) := by
    unfold entryMass
    positivity
  have hs : 0 ≤ ∑ i : Fin d, localConstants d i :=
    Finset.sum_nonneg fun i _ => (localQuadraticEstimate d).1 i
  have hd : (0 : ℝ) ≤ d := by positivity
  unfold blockD
  nlinarith [mul_nonneg hd hm, mul_nonneg hd hs]

lemma blockD_one_le (d : ℕ) : 1 ≤ blockD d := by
  have hm : 0 ≤ entryMass (blockMatrix d) := by
    unfold entryMass
    positivity
  have hs : 0 ≤ ∑ i : Fin d, localConstants d i :=
    Finset.sum_nonneg fun i _ => (localQuadraticEstimate d).1 i
  have hd : (0 : ℝ) ≤ d := by positivity
  unfold blockD
  nlinarith [mul_nonneg hd hm, mul_nonneg hd hs]

lemma rounding_coefficient_le_blockD (d : ℕ) (i : Fin d) :
    ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) ≤ blockD d := by
  have hi : ((i.1 + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast i.isLt
  have hm : 0 ≤ entryMass (blockMatrix d) := by
    unfold entryMass
    positivity
  have hs : 0 ≤ ∑ j : Fin d, localConstants d j := by
    exact Finset.sum_nonneg fun j _ => (localQuadraticEstimate d).1 j
  have hd : (0 : ℝ) ≤ d := by positivity
  unfold blockD
  calc
    ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) ≤
        (d : ℝ) * entryMass (blockMatrix d) := by
      nlinarith [mul_le_mul_of_nonneg_right hi hm]
    _ ≤ 1 + (d : ℝ) * entryMass (blockMatrix d) +
        (d : ℝ) * ∑ j : Fin d, localConstants d j := by
      nlinarith [mul_nonneg hd hs]

lemma quadratic_coefficient_le_blockD (d : ℕ) (i : Fin d) :
    (d : ℝ) * localConstants d i ≤ blockD d := by
  have hci : localConstants d i ≤ ∑ j : Fin d, localConstants d j :=
    Finset.single_le_sum (fun j _ => (localQuadraticEstimate d).1 j) (Finset.mem_univ i)
  have hd : (0 : ℝ) ≤ d := by positivity
  have hm : 0 ≤ entryMass (blockMatrix d) := by
    unfold entryMass
    positivity
  unfold blockD
  calc
    (d : ℝ) * localConstants d i ≤
        (d : ℝ) * ∑ j : Fin d, localConstants d j :=
      mul_le_mul_of_nonneg_left hci hd
    _ ≤ 1 + (d : ℝ) * entryMass (blockMatrix d) +
        (d : ℝ) * ∑ j : Fin d, localConstants d j := by
      nlinarith [mul_nonneg hd hm]

/-- The unperturbed block at `N, 2N, ..., dN`. -/
def referenceBlock (d N : ℕ) (i : Fin d) : ℝ :=
  ∑ j : Fin d, coord (i.1 + 1) (((j.1 + 1) * N : ℕ) : ℝ)

/-- The same block after integral perturbations. -/
def perturbedBlock (d N : ℕ) (z : Fin d → ℤ) (i : Fin d) : ℝ :=
  ∑ j : Fin d,
    coord (i.1 + 1) ((((j.1 + 1) * N : ℕ) : ℝ) + z j)

/-- The leading Vandermonde linearization of a block perturbation. -/
def linearBlock (d N : ℕ) (z : Fin d → ℤ) (i : Fin d) : ℝ :=
  ((i.1 + 1 : ℕ) : ℝ) / (N : ℝ) ^ (i.1 + 2) *
    (blockMatrix d).mulVec (fun j => (z j : ℝ)) i

lemma local_scale_condition {d N M : ℕ} (hN : 0 < N)
    (hscale : 4 * d * M ≤ N) (i j : Fin d) (z : Fin d → ℤ)
    (hz : ∀ j, |z j| ≤ (M : ℝ)) :
    |(z j : ℝ)| ≤ (((j.1 + 1) * N : ℕ) : ℝ) /
      (4 * (i.1 + 1 : ℕ)) := by
  have hi : i.1 + 1 ≤ d := i.isLt
  have hj : 1 ≤ j.1 + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hsR : (4 : ℝ) * d * M ≤ N := by exact_mod_cast hscale
  have hiR : (i.1 : ℝ) + 1 ≤ d := by exact_mod_cast hi
  have hjR : (1 : ℝ) ≤ (j.1 : ℝ) + 1 := by exact_mod_cast hj
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hz' : |(z j : ℝ)| ≤ (M : ℝ) := by simpa using hz j
  rw [le_div_iff₀ (by positivity)]
  push_cast
  calc
    |(z j : ℝ)| * (4 * ((i.1 : ℝ) + 1))
        ≤ (M : ℝ) * (4 * ((i.1 : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hz' (by positivity)
    _ = 4 * ((i.1 : ℝ) + 1) * M := by ring
    _ ≤ 4 * d * M := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hiR (by norm_num)) (by positivity)
    _ ≤ (N : ℝ) := hsR
    _ = 1 * (N : ℝ) := by ring
    _ ≤ ((j.1 : ℝ) + 1) * N :=
      mul_le_mul_of_nonneg_right hjR hNR.le

lemma linearBlock_eq_sum (d N : ℕ) (hN : 0 < N) (z : Fin d → ℤ)
    (i : Fin d) :
    linearBlock d N z i =
      ∑ j : Fin d, ((i.1 + 1 : ℕ) : ℝ) * z j /
        ((((j.1 + 1) * N : ℕ) : ℝ) ^ (i.1 + 2)) := by
  unfold linearBlock Matrix.mulVec dotProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change ((i.1 + 1 : ℕ) : ℝ) / (N : ℝ) ^ (i.1 + 2) *
      (blockMatrix d i j * (z j : ℝ)) =
    ((i.1 + 1 : ℕ) : ℝ) * z j /
      ((((j.1 + 1) * N : ℕ) : ℝ) ^ (i.1 + 2))
  rw [blockMatrix_apply]
  have hNR : (N : ℝ) ≠ 0 := by positivity
  have hjR : (((j.1 + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  push_cast
  rw [mul_pow]
  field_simp

/--
Summing the one-variable quadratic estimates gives the nonlinear error of a
whole block.  This is the estimate used after the Vandermonde rounding step.
-/
theorem block_remainder_bound {d N M : ℕ} {C : Fin d → ℝ}
    (hlocal : LocalQuadraticEstimate C) (hN : 0 < N)
    (hscale : 4 * d * M ≤ N) (z : Fin d → ℤ)
    (hz : ∀ j, |z j| ≤ (M : ℝ)) (i : Fin d) :
    |(referenceBlock d N i - perturbedBlock d N z i) - linearBlock d N z i| ≤
      (d : ℝ) * C i * (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3) := by
  rw [linearBlock_eq_sum d N hN z i]
  unfold referenceBlock perturbedBlock
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  calc
    |∑ j : Fin d,
        (coord (i.1 + 1) (((j.1 + 1) * N : ℕ) : ℝ) -
          coord (i.1 + 1) ((((j.1 + 1) * N : ℕ) : ℝ) + z j) -
          ((i.1 + 1 : ℕ) : ℝ) * z j /
            ((((j.1 + 1) * N : ℕ) : ℝ) ^ (i.1 + 2)))|
        ≤ ∑ j : Fin d,
          |coord (i.1 + 1) (((j.1 + 1) * N : ℕ) : ℝ) -
            coord (i.1 + 1) ((((j.1 + 1) * N : ℕ) : ℝ) + z j) -
            ((i.1 + 1 : ℕ) : ℝ) * z j /
              ((((j.1 + 1) * N : ℕ) : ℝ) ^ (i.1 + 2))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, C i * (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3) := by
      apply Finset.sum_le_sum
      intro j _
      have hX : 0 < (j.1 + 1) * N := Nat.mul_pos (Nat.succ_pos _) hN
      refine (hlocal.2 i ((j.1 + 1) * N) (z j) hX
        (local_scale_condition hN hscale i j z hz)).trans ?_
      have hz2 : (z j : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := by
        rw [sq_le_sq]
        simpa using hz j
      have hbase : (N : ℝ) ≤ (((j.1 + 1) * N : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_mul_of_pos_left N (Nat.succ_pos j.1)
      have hden : (N : ℝ) ^ (i.1 + 3) ≤
          (((j.1 + 1) * N : ℕ) : ℝ) ^ (i.1 + 3) :=
        pow_le_pow_left₀ (by positivity) hbase _
      have hCN : 0 ≤ C i := hlocal.1 i
      have hNp : 0 < (N : ℝ) ^ (i.1 + 3) := by positivity
      have hXp : 0 < ((((j.1 + 1) * N : ℕ) : ℝ) ^ (i.1 + 3)) := by positivity
      exact div_le_div₀ (mul_nonneg hCN (sq_nonneg _))
        (mul_le_mul_of_nonneg_left hz2 hCN) hNp hden
    _ = (d : ℝ) * C i * (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3) := by
      simp
      ring

/-- The block argument with an abstract rounding radius. -/
theorem discrete_block_approximation_of_rounding {d N M : ℕ} {C : Fin d → ℝ}
    {eps : ℝ} (hlocal : LocalQuadraticEstimate C) (hN : 0 < N) (hM : 1 ≤ M)
    (hscale : 4 * d * M ≤ N) (heps : 0 < eps)
    (hround : ∀ (M : ℕ) (hM : 1 ≤ M) (x : Fin d → ℝ),
      (∀ i, |x i| ≤ eps * M) →
      ∃ z : Fin d → ℤ, (∀ j, |z j| ≤ (M : ℝ)) ∧
        ∀ i, |(blockMatrix d).mulVec (fun j => (z j : ℝ)) i - x i| ≤
          entryMass (blockMatrix d) / 2) :
    ∀ q : Fin d → ℝ,
      (∀ i, |q i| ≤ eps * (M : ℝ) / (N : ℝ) ^ (i.1 + 2)) →
      ∃ z : Fin d → ℤ,
        (∀ j, |z j| ≤ (M : ℝ)) ∧
        ∀ i,
          |(referenceBlock d N i - perturbedBlock d N z i) - q i| ≤
            ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
                (N : ℝ) ^ (i.1 + 2) +
              (d : ℝ) * C i * (M : ℝ) ^ 2 /
                (N : ℝ) ^ (i.1 + 3) := by
  intro q hq
  let x : Fin d → ℝ := fun i =>
    (N : ℝ) ^ (i.1 + 2) / ((i.1 + 1 : ℕ) : ℝ) * q i
  have hx : ∀ i, |x i| ≤ eps * M := by
    intro i
    have hp : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by positivity
    have hNp : (0 : ℝ) < (N : ℝ) ^ (i.1 + 2) := by positivity
    calc
      |x i| = ((N : ℝ) ^ (i.1 + 2) / ((i.1 + 1 : ℕ) : ℝ)) * |q i| := by
        rw [show x i = (N : ℝ) ^ (i.1 + 2) / ((i.1 + 1 : ℕ) : ℝ) * q i by rfl,
          abs_mul, abs_of_pos (div_pos hNp hp)]
      _ ≤ ((N : ℝ) ^ (i.1 + 2) / ((i.1 + 1 : ℕ) : ℝ)) *
          (eps * (M : ℝ) / (N : ℝ) ^ (i.1 + 2)) :=
        mul_le_mul_of_nonneg_left (hq i) (by positivity)
      _ = eps * (M : ℝ) / ((i.1 + 1 : ℕ) : ℝ) := by field_simp
      _ ≤ eps * M := by
        rw [div_le_iff₀ hp]
        have hp1 : (1 : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.1)
        nlinarith [mul_nonneg heps.le (show (0 : ℝ) ≤ M by positivity)]
  rcases hround M hM x hx with ⟨z, hz, hzerr⟩
  refine ⟨z, hz, ?_⟩
  intro i
  have hp : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by positivity
  have hNp : (0 : ℝ) < (N : ℝ) ^ (i.1 + 2) := by positivity
  have hlinId : linearBlock d N z i - q i =
      (((i.1 + 1 : ℕ) : ℝ) / (N : ℝ) ^ (i.1 + 2)) *
        ((blockMatrix d).mulVec (fun j => (z j : ℝ)) i - x i) := by
    unfold linearBlock
    dsimp [x]
    field_simp
  have hlin : |linearBlock d N z i - q i| ≤
      ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
        (N : ℝ) ^ (i.1 + 2) := by
    rw [hlinId, abs_mul, abs_of_pos (div_pos hp hNp)]
    calc
      (((i.1 + 1 : ℕ) : ℝ) / (N : ℝ) ^ (i.1 + 2)) *
          |(blockMatrix d).mulVec (fun j => (z j : ℝ)) i - x i| ≤
        (((i.1 + 1 : ℕ) : ℝ) / (N : ℝ) ^ (i.1 + 2)) *
          (entryMass (blockMatrix d) / 2) :=
        mul_le_mul_of_nonneg_left (hzerr i) (by positivity)
      _ = ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
          (N : ℝ) ^ (i.1 + 2) := by ring
  have hrem := block_remainder_bound hlocal hN hscale z hz i
  calc
    |(referenceBlock d N i - perturbedBlock d N z i) - q i| =
        |((referenceBlock d N i - perturbedBlock d N z i) - linearBlock d N z i) +
          (linearBlock d N z i - q i)| := by ring_nf
    _ ≤ |(referenceBlock d N i - perturbedBlock d N z i) - linearBlock d N z i| +
        |linearBlock d N z i - q i| := abs_add_le _ _
    _ ≤ (d : ℝ) * C i * (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3) +
        (((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
          (N : ℝ) ^ (i.1 + 2)) := add_le_add hrem hlin
    _ = ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
          (N : ℝ) ^ (i.1 + 2) +
        (d : ℝ) * C i * (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3) := by ring

/--
The finite-dimensional discrete block approximation in the form used by the
diagonal construction.

Every target in the small coordinate box around the reference block can be
realized, up to the displayed sum of a lattice-rounding error and a quadratic
error, by a single tuple of bounded integral perturbations.  The same tuple
works in all `d` coordinates.
-/
theorem discrete_block_approximation {d N M : ℕ} {C : Fin d → ℝ}
    (hlocal : LocalQuadraticEstimate C) (hN : 0 < N) (hM : 1 ≤ M)
    (hscale : 4 * d * M ≤ N) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ q : Fin d → ℝ,
        (∀ i, |q i| ≤ ε * (M : ℝ) / (N : ℝ) ^ (i.1 + 2)) →
        ∃ z : Fin d → ℤ,
          (∀ j, |z j| ≤ (M : ℝ)) ∧
          ∀ i,
            |(referenceBlock d N i - perturbedBlock d N z i) - q i| ≤
              ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
                  (N : ℝ) ^ (i.1 + 2) +
                (d : ℝ) * C i * (M : ℝ) ^ 2 /
                  (N : ℝ) ^ (i.1 + 3) := by
  rcases inverse_matrix_rounding (blockMatrix d) (det_blockMatrix_ne_zero d) with
    ⟨ε, hε, hε1, hround⟩
  refine ⟨ε, hε, hε1, ?_⟩
  intro q hq
  let x : Fin d → ℝ := fun i =>
    (N : ℝ) ^ (i.1 + 2) / ((i.1 + 1 : ℕ) : ℝ) * q i
  have hx : ∀ i, |x i| ≤ ε * M := by
    intro i
    have hp : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by positivity
    have hNp : (0 : ℝ) < (N : ℝ) ^ (i.1 + 2) := by positivity
    calc
      |x i| = ((N : ℝ) ^ (i.1 + 2) / ((i.1 + 1 : ℕ) : ℝ)) * |q i| := by
        rw [show x i = (N : ℝ) ^ (i.1 + 2) / ((i.1 + 1 : ℕ) : ℝ) * q i by rfl,
          abs_mul, abs_of_pos (div_pos hNp hp)]
      _ ≤ ((N : ℝ) ^ (i.1 + 2) / ((i.1 + 1 : ℕ) : ℝ)) *
          (ε * (M : ℝ) / (N : ℝ) ^ (i.1 + 2)) :=
        mul_le_mul_of_nonneg_left (hq i) (by positivity)
      _ = ε * (M : ℝ) / ((i.1 + 1 : ℕ) : ℝ) := by field_simp
      _ ≤ ε * M := by
        rw [div_le_iff₀ hp]
        have hp1 : (1 : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.1)
        nlinarith [mul_nonneg hε.le (show (0 : ℝ) ≤ M by positivity)]
  rcases hround M hM x hx with ⟨z, hz, hzerr⟩
  refine ⟨z, hz, ?_⟩
  intro i
  have hp : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by positivity
  have hNp : (0 : ℝ) < (N : ℝ) ^ (i.1 + 2) := by positivity
  have hlinId : linearBlock d N z i - q i =
      (((i.1 + 1 : ℕ) : ℝ) / (N : ℝ) ^ (i.1 + 2)) *
        ((blockMatrix d).mulVec (fun j => (z j : ℝ)) i - x i) := by
    unfold linearBlock
    dsimp [x]
    field_simp
  have hlin : |linearBlock d N z i - q i| ≤
      ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
        (N : ℝ) ^ (i.1 + 2) := by
    rw [hlinId, abs_mul, abs_of_pos (div_pos hp hNp)]
    calc
      (((i.1 + 1 : ℕ) : ℝ) / (N : ℝ) ^ (i.1 + 2)) *
          |(blockMatrix d).mulVec (fun j => (z j : ℝ)) i - x i|
        ≤ (((i.1 + 1 : ℕ) : ℝ) / (N : ℝ) ^ (i.1 + 2)) *
          (entryMass (blockMatrix d) / 2) :=
        mul_le_mul_of_nonneg_left (hzerr i) (by positivity)
      _ = ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
          (N : ℝ) ^ (i.1 + 2) := by ring
  have hrem := block_remainder_bound hlocal hN hscale z hz i
  calc
    |(referenceBlock d N i - perturbedBlock d N z i) - q i| =
        |((referenceBlock d N i - perturbedBlock d N z i) - linearBlock d N z i) +
          (linearBlock d N z i - q i)| := by ring_nf
    _ ≤ |(referenceBlock d N i - perturbedBlock d N z i) - linearBlock d N z i| +
        |linearBlock d N z i - q i| := abs_add_le _ _
    _ ≤ (d : ℝ) * C i * (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3) +
        (((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
          (N : ℝ) ^ (i.1 + 2)) := add_le_add hrem hlin
    _ = ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
          (N : ℝ) ^ (i.1 + 2) +
        (d : ℝ) * C i * (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3) := by ring

/-- The block approximation with constants fixed solely by the dimension. -/
theorem discrete_block_approximation_fixed (d N M : ℕ) (hN : 0 < N) (hM : 1 ≤ M)
    (hscale : 4 * d * M ≤ N) :
    ∀ q : Fin d → ℝ,
      (∀ i, |q i| ≤ blockEpsilon d * (M : ℝ) / (N : ℝ) ^ (i.1 + 2)) →
      ∃ z : Fin d → ℤ,
        (∀ j, |z j| ≤ (M : ℝ)) ∧
        ∀ i,
          |(referenceBlock d N i - perturbedBlock d N z i) - q i| ≤
            ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
                (N : ℝ) ^ (i.1 + 2) +
              (d : ℝ) * localConstants d i * (M : ℝ) ^ 2 /
                (N : ℝ) ^ (i.1 + 3) :=
  discrete_block_approximation_of_rounding (localQuadraticEstimate d) hN hM hscale
    (blockEpsilon_pos d) (blockEpsilon_spec d).2.2

/--
Uniform cover/refinement form.  Both the box radius and the error constant are
chosen before `N` and `M`; this is the interface used to select the diagonal
scale schedule.
-/
theorem discrete_block_approximation_uniform (d N M : ℕ) (hN : 0 < N) (hM : 1 ≤ M)
    (hscale : 4 * d * M ≤ N) (q : Fin d → ℝ)
    (hq : ∀ i, |q i| ≤
      blockEpsilon d * (M : ℝ) / (N : ℝ) ^ (i.1 + 2)) :
    ∃ z : Fin d → ℤ,
      (∀ j, |z j| ≤ (M : ℝ)) ∧
      ∀ i,
        |(referenceBlock d N i - perturbedBlock d N z i) - q i| ≤
          blockD d *
            (1 / (N : ℝ) ^ (i.1 + 2) +
              (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3)) := by
  rcases discrete_block_approximation_fixed d N M hN hM hscale q hq with
    ⟨z, hz, herr⟩
  refine ⟨z, hz, ?_⟩
  intro i
  refine (herr i).trans ?_
  have hN1 : 0 ≤ (N : ℝ) ^ (i.1 + 2) := by positivity
  have hN2 : 0 ≤ (N : ℝ) ^ (i.1 + 3) := by positivity
  have hM2 : 0 ≤ (M : ℝ) ^ 2 := sq_nonneg _
  calc
    ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
          (N : ℝ) ^ (i.1 + 2) +
        (d : ℝ) * localConstants d i * (M : ℝ) ^ 2 /
          (N : ℝ) ^ (i.1 + 3) ≤
      blockD d / (N : ℝ) ^ (i.1 + 2) +
        blockD d * (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right (rounding_coefficient_le_blockD d i) hN1
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (quadratic_coefficient_le_blockD d i) hM2) hN2
    _ = blockD d *
        (1 / (N : ℝ) ^ (i.1 + 2) +
          (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3)) := by ring

end

end Erdos266Block

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos266/Erdos266Diagonal.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-!
# Diagonal nested-box recursion for Erdős Problem 266

This file isolates the choice, diagonalization, convergence, and finite-block
reindexing steps of the Kovač--Tao construction.  The finite-dimensional block
lemma and scale estimates are supplied through `Scheme.refine`.
-/

namespace Erdos266Diagonal

noncomputable section

open Filter Finset Topology

/-- Abstract input to the diagonal nested-box construction.  The active
dimension may stay fixed for many stages, but grows by at most one per stage
and eventually activates every coordinate. -/
structure Scheme (β : Type*) where
  dim : ℕ → ℕ
  dim_zero : dim 0 = 0
  dim_mono : Monotone dim
  dim_step : ∀ k, dim (k + 1) ≤ dim k + 1
  dim_unbounded : ∀ i, ∃ k, i < dim k
  refBlock : ℕ → ℕ → ℝ
  actualBlock : ℕ → β → ℕ → ℝ
  admissible : ℕ → β → Prop
  radius : ℕ → ℕ → ℝ
  tail : ℕ → ℕ → ℝ
  radius_pos : ∀ i k, 0 < radius i k
  tail_succ : ∀ i k, tail i k = refBlock i k + tail i (k + 1)
  refine : ∀ k (error : Fin (dim k) → ℝ),
    (∀ i, |error i| ≤ radius i k) →
      ∃ b : β, admissible k b ∧ ∀ i,
        |error i + refBlock i k - actualBlock k b i| ≤ radius i (k + 1)

namespace Scheme

variable {β : Type*} (S : Scheme β)

/-- The first-`k` actual blocks plus the reference tail beginning at `k`. -/
def approximation (choice : ℕ → β) (i k : ℕ) : ℝ :=
  (∑ l ∈ range k, S.actualBlock l (choice l) i) + S.tail i k

/-- A finite-stage state.  Total functions are used for the data, while the
proof fields record only the already active/used parts. -/
structure State (k : ℕ) where
  target : ℕ → ℚ
  choice : ℕ → β
  invariant : ∀ i, i < S.dim k →
    |(target i : ℝ) - S.approximation choice i k| ≤ S.radius i k
  choice_admissible : ∀ l, l < k → S.admissible l (choice l)

/-- A successor preserves all targets already active and all block choices
already used. -/
def Extends {k : ℕ} (s : S.State k) (s' : S.State (k + 1)) : Prop :=
  (∀ i, i < S.dim k → s'.target i = s.target i) ∧
  (∀ l, l < k → s'.choice l = s.choice l)

private lemma exists_rat_abs_sub_lt (x ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℚ, |(q : ℝ) - x| < ε := by
  have hinterval : x - ε < x + ε := by linarith
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hinterval
  refine ⟨q, (abs_lt).2 ⟨?_, ?_⟩⟩ <;> linarith

/-- One successor step: refine every currently active coordinate with one
admissible block, then rationally initialize the at-most-one coordinate newly
visible in the output state. -/
theorem exists_next {k : ℕ} (s : S.State k) :
    ∃ s' : S.State (k + 1), S.Extends s s' := by
  let center : ℕ → ℝ := fun i ↦ S.approximation s.choice i k
  let error : Fin (S.dim k) → ℝ := fun i ↦ (s.target i : ℝ) - center i
  have herror : ∀ i, |error i| ≤ S.radius i k := by
    intro i
    simpa [error, center] using s.invariant i i.isLt
  obtain ⟨b, hbadm, hb⟩ := S.refine k error herror
  let choice' : ℕ → β := Function.update s.choice k b
  have hchoice_lt : ∀ l ∈ range k, choice' l = s.choice l := by
    intro l hl
    exact Function.update_of_ne (Nat.ne_of_lt (mem_range.1 hl)) b s.choice
  have hsum (i : ℕ) :
      (∑ l ∈ range k, S.actualBlock l (choice' l) i) =
        ∑ l ∈ range k, S.actualBlock l (s.choice l) i := by
    apply sum_congr rfl
    intro l hl
    rw [hchoice_lt l hl]
  have hchoice_k : choice' k = b := Function.update_self k b s.choice
  have hold : ∀ i, i < S.dim k →
      |(s.target i : ℝ) - S.approximation choice' i (k + 1)| ≤ S.radius i (k + 1) := by
    intro i hi
    have hblock := hb ⟨i, hi⟩
    rw [approximation, sum_range_succ, hsum, hchoice_k]
    change |((s.target i : ℝ) - center i) + S.refBlock i k - S.actualBlock k b i| ≤
      S.radius i (k + 1) at hblock
    dsimp [center] at hblock
    rw [approximation, S.tail_succ i k] at hblock
    convert hblock using 1
    abel_nf
  let newCenter : ℝ := S.approximation choice' (S.dim k) (k + 1)
  obtain ⟨q : ℚ, hq⟩ :=
    exists_rat_abs_sub_lt newCenter (S.radius (S.dim k) (k + 1))
      (S.radius_pos (S.dim k) (k + 1))
  let target' : ℕ → ℚ := Function.update s.target (S.dim k) q
  have hinvariant : ∀ i, i < S.dim (k + 1) →
      |(target' i : ℝ) - S.approximation choice' i (k + 1)| ≤ S.radius i (k + 1) := by
    intro i hi
    by_cases hiold : i < S.dim k
    · have hne : i ≠ S.dim k := Nat.ne_of_lt hiold
      simpa [target', Function.update_of_ne hne] using hold i hiold
    · have hieq : i = S.dim k := by
        have hstep := S.dim_step k
        omega
      subst i
      simpa [target', newCenter] using hq.le
  have hadmissible : ∀ l, l < k + 1 → S.admissible l (choice' l) := by
    intro l hl
    by_cases h : l = k
    · subst l
      simpa [choice'] using hbadm
    · have hlk : l < k := by omega
      simpa [choice', Function.update_of_ne h] using s.choice_admissible l hlk
  let s' : S.State (k + 1) := ⟨target', choice', hinvariant, hadmissible⟩
  refine ⟨s', ?_, ?_⟩
  · intro i hi
    exact Function.update_of_ne (Nat.ne_of_lt hi) q s.target
  · intro l hl
    exact Function.update_of_ne (Nat.ne_of_lt hl) b s.choice

/-- A default block choice, obtained from the stage-zero refinement theorem.
It is used only to fill as-yet unused entries of the total choice function. -/
def arbitraryChoice : β :=
  Classical.choose
    (S.refine 0
      (fun i ↦ Fin.elim0 (Fin.cast S.dim_zero i))
      (fun i ↦ Fin.elim0 (Fin.cast S.dim_zero i)))

/-- The stage-zero invariant and admissibility conditions are vacuous. -/
def initialState : S.State 0 where
  target := 0
  choice := fun _ ↦ S.arbitraryChoice
  invariant := by simp [S.dim_zero]
  choice_admissible := by simp

/-- A classically chosen successor state. -/
def nextState {k : ℕ} (s : S.State k) : S.State (k + 1) :=
  Classical.choose (S.exists_next s)

lemma nextState_extends {k : ℕ} (s : S.State k) : S.Extends s (S.nextState s) :=
  Classical.choose_spec (S.exists_next s)

/-- The recursively chosen finite-stage states. -/
def states : (k : ℕ) → S.State k
  | 0 => S.initialState
  | k + 1 => nextState S (states k)

lemma states_succ_extends (k : ℕ) :
    S.Extends (S.states k) (S.states (k + 1)) := by
  change S.Extends (S.states k) (S.nextState (S.states k))
  exact S.nextState_extends (S.states k)

/-- The first stage at which coordinate `i` is active. -/
def activationStage (i : ℕ) : ℕ := Nat.find (S.dim_unbounded i)

lemma lt_dim_activationStage (i : ℕ) : i < S.dim (S.activationStage i) :=
  Nat.find_spec (S.dim_unbounded i)

lemma activationStage_le_of_lt_dim {i k : ℕ} (hik : i < S.dim k) :
    S.activationStage i ≤ k :=
  Nat.find_min' (S.dim_unbounded i) hik

/-- The rational target permanently assigned to coordinate `i`. -/
def target (i : ℕ) : ℚ := (S.states (S.activationStage i)).target i

/-- The permanent actual-block choice at stage `k`. -/
def choice (k : ℕ) : β := (S.states (k + 1)).choice k

lemma states_target_eq_target {i k : ℕ} (hik : i < S.dim k) :
    (S.states k).target i = S.target i := by
  induction k with
  | zero => simp [S.dim_zero] at hik
  | succ k ih =>
      have ha : S.activationStage i ≤ k + 1 := S.activationStage_le_of_lt_dim hik
      by_cases heq : S.activationStage i = k + 1
      · unfold target
        rw [heq]
      · have ha' : S.activationStage i ≤ k := by omega
        have hia := S.lt_dim_activationStage i
        have hiprev : i < S.dim k := lt_of_lt_of_le hia (S.dim_mono ha')
        calc
          (S.states (k + 1)).target i = (S.states k).target i :=
            (S.states_succ_extends k).1 i hiprev
          _ = S.target i := ih hiprev

lemma states_choice_eq_choice {l k : ℕ} (hlk : l < k) :
    (S.states k).choice l = S.choice l := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases h : l = k
      · subst l
        rfl
      · have hlk' : l < k := by omega
        calc
          (S.states (k + 1)).choice l = (S.states k).choice l :=
            (S.states_succ_extends k).2 l hlk'
          _ = S.choice l := ih hlk'

/-- Every globally selected block satisfies the stage-specific admissibility
condition returned by the refinement theorem. -/
theorem choice_admissible (k : ℕ) : S.admissible k (S.choice k) := by
  exact (S.states (k + 1)).choice_admissible k (by omega)

/-- The global nested-box invariant. -/
theorem invariant (i k : ℕ) (hik : i < S.dim k) :
    |(S.target i : ℝ) - S.approximation S.choice i k| ≤ S.radius i k := by
  have h := (S.states k).invariant i hik
  rw [S.states_target_eq_target hik] at h
  have hsum :
      (∑ l ∈ range k, S.actualBlock l ((S.states k).choice l) i) =
        ∑ l ∈ range k, S.actualBlock l (S.choice l) i := by
    apply sum_congr rfl
    intro l hl
    rw [S.states_choice_eq_choice (mem_range.1 hl)]
  simpa only [approximation, hsum] using h

/-- Once actual block series are summable and tails and radii tend to zero,
each coordinate sum equals its rational target. -/
theorem target_eq_tsum
    (hsummable : ∀ i, Summable (fun k ↦ S.actualBlock k (S.choice k) i))
    (htail : ∀ i, Tendsto (S.tail i) atTop (𝓝 0))
    (hradius : ∀ i, Tendsto (S.radius i) atTop (𝓝 0))
    (i : ℕ) :
    (S.target i : ℝ) = ∑' k, S.actualBlock k (S.choice k) i := by
  let blocks : ℕ → ℝ := fun k ↦ S.actualBlock k (S.choice k) i
  let approx : ℕ → ℝ := fun k ↦ (∑ l ∈ range k, blocks l) + S.tail i k
  have hpartial : Tendsto (fun k ↦ ∑ l ∈ range k, blocks l) atTop
      (𝓝 (∑' k, blocks k)) := by
    exact (hsummable i).hasSum.tendsto_sum_nat
  have happ_tsum : Tendsto approx atTop (𝓝 (∑' k, blocks k)) := by
    simpa [approx] using hpartial.add (htail i)
  have hactive : ∀ᶠ k in atTop, i < S.dim k := by
    filter_upwards [eventually_ge_atTop (S.activationStage i)] with k hk
    exact lt_of_lt_of_le (S.lt_dim_activationStage i) (S.dim_mono hk)
  have hbound : ∀ᶠ k in atTop, |(S.target i : ℝ) - approx k| ≤ S.radius i k := by
    filter_upwards [hactive] with k hk
    simpa [approx, blocks, approximation] using S.invariant i k hk
  have habs : Tendsto (fun k ↦ |(S.target i : ℝ) - approx k|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) hbound (hradius i)
  have happ_target : Tendsto approx atTop (𝓝 (S.target i : ℝ)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq, abs_sub_comm] using habs
  exact tendsto_nhds_unique happ_target happ_tsum

/-- Packaged diagonal output for the main construction. -/
theorem exists_rational_coordinate_sums
    (hsummable : ∀ i, Summable (fun k ↦ S.actualBlock k (S.choice k) i))
    (htail : ∀ i, Tendsto (S.tail i) atTop (𝓝 0))
    (hradius : ∀ i, Tendsto (S.radius i) atTop (𝓝 0)) :
    ∃ q : ℕ → ℚ, ∃ b : ℕ → β,
      (∀ k, S.admissible k (b k)) ∧
      (∀ i k, i < S.dim k →
        |(q i : ℝ) - S.approximation b i k| ≤ S.radius i k) ∧
      ∀ i, (q i : ℝ) = ∑' k, S.actualBlock k (b k) i := by
  exact ⟨S.target, S.choice, S.choice_admissible, S.invariant,
    S.target_eq_tsum hsummable htail hradius⟩

/-! ### Reindexing finite blocks -/

/-- The sigma type of positions in finite blocks of prescribed sizes. -/
def BlockIndex (size : ℕ → ℕ) := Σ k, Fin (size k)

instance (size : ℕ → ℕ) : Countable (BlockIndex size) := by
  let encode : BlockIndex size → ℕ × ℕ := fun p ↦ (p.1, p.2.val)
  have hencode : Function.Injective encode := by
    intro a b hab
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    simp only [encode, Prod.mk.injEq] at hab
    obtain ⟨rfl, hval⟩ := hab
    congr
    exact Fin.ext hval
  exact hencode.countable

/-- Pulling a series back along an enumeration of all block positions preserves
summability.  The explicit equivalence is an input so the caller may choose any
convenient enumeration. -/
theorem summable_reindex_iff (size : ℕ → ℕ) (f : BlockIndex size → ℝ)
    (e : ℕ ≃ BlockIndex size) :
    Summable (fun n ↦ f (e n)) ↔ Summable f := by
  change Summable (f ∘ e) ↔ Summable f
  exact e.summable_iff

/-- Pulling a series back along an enumeration of all block positions preserves
its sum. -/
theorem tsum_reindex_eq (size : ℕ → ℕ) (f : BlockIndex size → ℝ)
    (e : ℕ ≃ BlockIndex size) :
    (∑' n, f (e n)) = ∑' p, f p := by
  simpa only [Function.comp_apply] using e.tsum_eq f

/-- A summable series over finite block positions is the iterated sum of its
finite blocks. -/
theorem tsum_blockIndex_eq_tsum_sum (size : ℕ → ℕ) (f : BlockIndex size → ℝ)
    (hf : Summable f) :
    (∑' p, f p) = ∑' k, ∑ j : Fin (size k), f ⟨k, j⟩ := by
  calc
    (∑' p, f p) = ∑' k, ∑' j : Fin (size k), f ⟨k, j⟩ := hf.tsum_sigma
    _ = ∑' k, ∑ j : Fin (size k), f ⟨k, j⟩ := by
      apply tsum_congr
      intro k
      exact tsum_fintype _

/-- Reindexing and splitting into finite blocks in one equality. -/
theorem tsum_reindex_eq_tsum_sum (size : ℕ → ℕ) (f : BlockIndex size → ℝ)
    (e : ℕ ≃ BlockIndex size) (hf : Summable f) :
    (∑' n, f (e n)) = ∑' k, ∑ j : Fin (size k), f ⟨k, j⟩ :=
  (tsum_reindex_eq size f e).trans (tsum_blockIndex_eq_tsum_sum size f hf)

end Scheme

end

end Erdos266Diagonal

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos266/Erdos266Construction.lean` -/

section
/-!
# Block sequences for Erdős problem 266

This file contains the bookkeeping which turns bounded integral perturbations
of positive block centres into a positive summable family of natural numbers.
It is independent of the analytic construction which chooses the
perturbations.
-/

open scoped BigOperators



/-- The integer represented by the `j`-th point in block `k`. -/
def blockInt (L : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (k : ℕ) (j : ℕ) : ℤ :=
  (((j + 1) * L k : ℕ) : ℤ) + z k j

/-- The corresponding natural denominator.  Positivity is proved below from
the perturbation bound. -/
def blockNat (L : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (k : ℕ) (j : ℕ) : ℕ :=
  (blockInt L z k j).toNat

/-- Every perturbation in block `k` has absolute value at most `R k`. -/
def OffsetsBounded (R : ℕ → ℕ) (z : ℕ → ℕ → ℤ) : Prop :=
  ∀ k j, |(z k j : ℝ)| ≤ R k

lemma blockInt_cast (L : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (k j : ℕ) :
    ((blockInt L z k j : ℤ) : ℝ) =
      ((j + 1 : ℕ) : ℝ) * L k + z k j := by
  simp [blockInt, Nat.cast_mul]

lemma blockInt_pos {L R : ℕ → ℕ} {z : ℕ → ℕ → ℤ}
    (hL : ∀ k, 0 < L k) (hRL : ∀ k, 2 * R k ≤ L k)
    (hz : OffsetsBounded R z) (k j : ℕ) :
    0 < blockInt L z k j := by
  have hzlower : -((R k : ℕ) : ℝ) ≤ (z k j : ℝ) :=
    neg_le_of_abs_le (hz k j)
  have hbase : ((L k : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * L k := by
    have hj : (1 : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    calc
      ((L k : ℕ) : ℝ) = 1 * (L k : ℝ) := by ring
      _ ≤ ((j + 1 : ℕ) : ℝ) * L k :=
        mul_le_mul_of_nonneg_right hj (Nat.cast_nonneg _)
  have hR : (2 : ℝ) * R k ≤ L k := by exact_mod_cast hRL k
  have hLreal : (0 : ℝ) < L k := by exact_mod_cast hL k
  have hreal : (0 : ℝ) < ((blockInt L z k j : ℤ) : ℝ) := by
    rw [blockInt_cast]
    nlinarith
  exact_mod_cast hreal

lemma blockNat_pos {L R : ℕ → ℕ} {z : ℕ → ℕ → ℤ}
    (hL : ∀ k, 0 < L k) (hRL : ∀ k, 2 * R k ≤ L k)
    (hz : OffsetsBounded R z) (k j : ℕ) :
    0 < blockNat L z k j := by
  have h := blockInt_pos hL hRL hz k j
  simp only [blockNat]
  omega

lemma blockNat_cast {L R : ℕ → ℕ} {z : ℕ → ℕ → ℤ}
    (hL : ∀ k, 0 < L k) (hRL : ∀ k, 2 * R k ≤ L k)
    (hz : OffsetsBounded R z) (k j : ℕ) :
    ((blockNat L z k j : ℕ) : ℝ) =
      ((j + 1 : ℕ) : ℝ) * L k + z k j := by
  have hnonneg : 0 ≤ blockInt L z k j := (blockInt_pos hL hRL hz k j).le
  have htoNat : (((blockInt L z k j).toNat : ℕ) : ℤ) = blockInt L z k j :=
    Int.toNat_of_nonneg hnonneg
  have hcast := congrArg (fun x : ℤ => (x : ℝ)) htoNat
  simpa only [blockNat, Int.cast_natCast, blockInt_cast] using hcast

lemma half_L_le_blockNat {L R : ℕ → ℕ} {z : ℕ → ℕ → ℤ}
    (hL : ∀ k, 0 < L k) (hRL : ∀ k, 2 * R k ≤ L k)
    (hz : OffsetsBounded R z) (k j : ℕ) :
    ((L k : ℕ) : ℝ) / 2 ≤ blockNat L z k j := by
  rw [blockNat_cast hL hRL hz]
  have hzlower : -((R k : ℕ) : ℝ) ≤ (z k j : ℝ) :=
    neg_le_of_abs_le (hz k j)
  have hbase : ((L k : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * L k := by
    have hj : (1 : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    have hLreal : (0 : ℝ) < L k := by exact_mod_cast hL k
    nlinarith
  have hR : (2 : ℝ) * R k ≤ L k := by exact_mod_cast hRL k
  nlinarith

lemma reciprocal_blockNat_le {L R : ℕ → ℕ} {z : ℕ → ℕ → ℤ}
    (hL : ∀ k, 0 < L k) (hRL : ∀ k, 2 * R k ≤ L k)
    (hz : OffsetsBounded R z) (k j : ℕ) :
    (1 : ℝ) / blockNat L z k j ≤ 2 / L k := by
  have hLreal : (0 : ℝ) < L k := by exact_mod_cast hL k
  have hhalfpos : (0 : ℝ) < (L k : ℝ) / 2 := div_pos hLreal (by norm_num)
  have hrecip := one_div_le_one_div_of_le hhalfpos (half_L_le_blockNat hL hRL hz k j)
  calc
    (1 : ℝ) / blockNat L z k j ≤ 1 / ((L k : ℝ) / 2) := hrecip
    _ = 2 / L k := by field_simp

/-- Reciprocal summability of the sigma-indexed family of all block points. -/
theorem summable_reciprocal_blocks
    (d L R : ℕ → ℕ) (z : ℕ → ℕ → ℤ)
    (hL : ∀ k, 0 < L k) (hRL : ∀ k, 2 * R k ≤ L k)
    (hz : OffsetsBounded R z) (hd : ∀ k, d k ≤ k + 1)
    (hseries : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / L k)) :
    Summable (fun p : Σ k, Fin (d k) =>
      (1 : ℝ) / blockNat L z p.1 p.2.1) := by
  rw [summable_sigma_of_nonneg (fun _ => by positivity)]
  constructor
  · intro k
    exact Summable.of_finite
  · have houter : Summable (fun k : ℕ => 2 * (((k + 1 : ℕ) : ℝ) / L k)) :=
      hseries.mul_left 2
    refine Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => by positivity) ?_ houter
    intro k
    rw [tsum_fintype]
    calc
      (∑ j : Fin (d k), (1 : ℝ) / blockNat L z k j.1)
          ≤ ∑ _j : Fin (d k), (2 : ℝ) / L k := by
              exact Finset.sum_le_sum fun j _ => reciprocal_blockNat_le hL hRL hz k j.1
      _ = (d k : ℝ) * (2 / L k) := by simp
      _ ≤ (k + 1 : ℝ) * (2 / L k) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hd k) (by positivity)
      _ = 2 * (((k + 1 : ℕ) : ℝ) / L k) := by push_cast; ring

/-- Every positive triangular coordinate is summable on the block family. -/
theorem summable_coordinate_blocks
    (d L R : ℕ → ℕ) (z : ℕ → ℕ → ℤ)
    (hL : ∀ k, 0 < L k) (hRL : ∀ k, 2 * R k ≤ L k)
    (hz : OffsetsBounded R z) (hd : ∀ k, d k ≤ k + 1)
    (hseries : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / L k))
    (i : ℕ) (hi : 1 ≤ i) :
    Summable (fun p : Σ k, Fin (d k) =>
      reciprocalCoordinate i (blockNat L z p.1 p.2.1 : ℝ)) := by
  apply Summable.of_nonneg_of_le
    (fun p => reciprocalCoordinate_nonneg i (Nat.cast_nonneg _))
    (fun p => ?_)
    (summable_reciprocal_blocks d L R z hL hRL hz hd hseries)
  have hp : (0 : ℝ) < blockNat L z p.1 p.2.1 := by
    exact_mod_cast blockNat_pos hL hRL hz p.1 p.2.1
  calc
    reciprocalCoordinate i (blockNat L z p.1 p.2.1 : ℝ)
        ≤ ((blockNat L z p.1 p.2.1 : ℝ))⁻¹ :=
          reciprocalCoordinate_le_inv i hi hp
    _ = (1 : ℝ) / blockNat L z p.1 p.2.1 := by simp [one_div]

/-- Regroup a coordinate `tsum` by blocks. -/
theorem tsum_coordinate_blocks
    (d L R : ℕ → ℕ) (z : ℕ → ℕ → ℤ)
    (hL : ∀ k, 0 < L k) (hRL : ∀ k, 2 * R k ≤ L k)
    (hz : OffsetsBounded R z) (hd : ∀ k, d k ≤ k + 1)
    (hseries : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / L k))
    (i : ℕ) (hi : 1 ≤ i) :
    (∑' p : Σ k, Fin (d k),
      reciprocalCoordinate i (blockNat L z p.1 p.2.1 : ℝ)) =
      ∑' k, ∑ j : Fin (d k),
        reciprocalCoordinate i (blockNat L z k j.1 : ℝ) := by
  have hs := summable_coordinate_blocks d L R z hL hRL hz hd hseries i hi
  rw [hs.tsum_sigma]
  congr 1
  funext k
  rw [tsum_fintype]

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos266/Erdos266Scales.lean` -/

section
/-!
# Geometric scales for the Erdős 266 construction

This file collects the elementary asymptotic and scheduling facts used by the
diagonal construction.  Keeping them separate makes the analytic/block part of
the proof independent of routine power arithmetic.
-/

open Filter
open scoped Topology



noncomputable section

/-- The large scale of block `k`. -/
def N (k : ℕ) : ℕ := 16 ^ (k + 1)

/-- The radius of the integer perturbations in block `k`. -/
def M (k : ℕ) : ℕ := 4 ^ (k + 1)

lemma N_pos (k : ℕ) : 0 < N k := by
  simp [N]

lemma M_pos (k : ℕ) : 0 < M k := by
  simp [M]

lemma N_ne_zero (k : ℕ) : N k ≠ 0 := (N_pos k).ne'

lemma M_ne_zero (k : ℕ) : M k ≠ 0 := (M_pos k).ne'

lemma one_le_N (k : ℕ) : 1 ≤ N k := Nat.one_le_iff_ne_zero.2 (N_ne_zero k)

lemma one_le_M (k : ℕ) : 1 ≤ M k := Nat.one_le_iff_ne_zero.2 (M_ne_zero k)

lemma M_sq (k : ℕ) : M k ^ 2 = N k := by
  simp only [M, N]
  rw [show 16 = 4 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
  congr 1
  omega

lemma N_succ (k : ℕ) : N (k + 1) = 16 * N k := by
  simp [N, pow_succ, mul_comm]

lemma M_succ (k : ℕ) : M (k + 1) = 4 * M k := by
  simp [M, pow_succ, mul_comm]

lemma N_strictMono : StrictMono N := by
  intro a b hab
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

lemma M_strictMono : StrictMono M := by
  intro a b hab
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

lemma M_le_N (k : ℕ) : M k ≤ N k := by
  rw [← M_sq]
  nlinarith [one_le_M k]

/-- For dimensions at most `k + 1`, the perturbation radius fits the local
linearization window. -/
lemma four_mul_dim_mul_M_le_N {d k : ℕ} (hd : d ≤ k + 1) :
    4 * d * M k ≤ N k := by
  rw [← M_sq]
  have hkpow : k + 1 ≤ 4 ^ k := by
    clear d hd
    induction k with
    | zero => norm_num
    | succ k ih =>
        calc
          k + 2 ≤ 4 * (k + 1) := by omega
          _ ≤ 4 * 4 ^ k := Nat.mul_le_mul_left 4 ih
          _ = 4 ^ (k + 1) := by rw [pow_succ]; ring
  have hdk : d ≤ M k / 4 := by
    have : M k / 4 = 4 ^ k := by simp [M, pow_succ]
    rw [this]
    exact hd.trans hkpow
  have h4 : 4 * d ≤ M k := by
    have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mp hdk
    simpa [mul_comm] using this
  nlinarith [M_pos k]

lemma M_le_N_div_four_mul {d k : ℕ} (hd : d ≤ k + 1) (hdpos : 0 < d) :
    M k ≤ N k / (4 * d) := by
  exact (Nat.le_div_iff_mul_le (by positivity : 0 < 4 * d)).2 (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using four_mul_dim_mul_M_le_N hd)

/-- The quotient which occurs after dividing the old block error by the next
block's permitted error.  Since `N = M²`, this is
`N (k+1) ^ (e+1/2) / N k ^ (e+1)` without real square roots. -/
def absorptionRatio (e k : ℕ) : ℝ :=
  (M (k + 1) : ℝ) * (N (k + 1) : ℝ) ^ e / (N k : ℝ) ^ (e + 1)

lemma absorptionRatio_succ (e k : ℕ) :
    absorptionRatio e (k + 1) = absorptionRatio e k * ((1 : ℝ) / 4) := by
  simp only [absorptionRatio, N_succ, M_succ, Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_pow, mul_pow, pow_succ]
  have hNk : (N k : ℝ) ≠ 0 := by exact_mod_cast N_ne_zero k
  have hNks : (N (k + 1) : ℝ) ≠ 0 := by exact_mod_cast N_ne_zero (k + 1)
  field_simp [hNk, hNks]
  ring

lemma absorptionRatio_eq (e k : ℕ) :
    absorptionRatio e k = absorptionRatio e 0 * ((1 : ℝ) / 4) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [absorptionRatio_succ, ih, pow_succ]
      ring

lemma absorptionRatio_zero (e : ℕ) : absorptionRatio e 0 = (16 : ℝ) ^ e := by
  norm_num [absorptionRatio, N, M]
  rw [show (256 : ℝ) = 16 ^ 2 by norm_num, ← pow_mul, pow_succ]
  field_simp
  ring

lemma absorptionRatio_closedForm (e k : ℕ) :
    absorptionRatio e k = (16 : ℝ) ^ (e + 1) / (4 : ℝ) ^ (k + 2) := by
  rw [absorptionRatio_eq, absorptionRatio_zero, one_div_pow, pow_add, pow_succ]
  norm_num
  field_simp
  ring

lemma absorptionRatio_nonneg (e k : ℕ) : 0 ≤ absorptionRatio e k := by
  unfold absorptionRatio
  positivity

lemma absorptionRatio_pos (e k : ℕ) : 0 < absorptionRatio e k := by
  unfold absorptionRatio N M
  positivity

lemma tendsto_absorptionRatio (e : ℕ) :
    Tendsto (absorptionRatio e) atTop (nhds 0) := by
  have hp : Tendsto (fun k : ℕ => ((1 : ℝ) / 4) ^ k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h : Tendsto
      (fun k : ℕ => absorptionRatio e 0 * ((1 : ℝ) / 4) ^ k)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hp
  exact h.congr' (Filter.Eventually.of_forall fun k => (absorptionRatio_eq e k).symm)

lemma tendsto_const_mul_absorptionRatio (C : ℝ) (e : ℕ) :
    Tendsto (fun k => C * absorptionRatio e k) atTop (nhds 0) :=
  by simpa using tendsto_const_nhds.mul (tendsto_absorptionRatio e)

lemma eventually_const_mul_absorptionRatio_lt
    (C : ℝ) (e : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, C * absorptionRatio e k < ε := by
  exact (tendsto_const_mul_absorptionRatio C e).eventually (gt_mem_nhds hε)

lemma eventually_const_mul_absorptionRatio_le
    (C : ℝ) (e : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, C * absorptionRatio e k ≤ ε :=
  (eventually_const_mul_absorptionRatio_lt C e hε).mono fun _ => le_of_lt

/-- A coordinatewise form of the absorption inequality used between adjacent
blocks. -/
lemma eventually_localAbsorption (i : ℕ) {D ε : ℝ}
    (_hD : 0 ≤ D) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      D * (1 / (N k : ℝ) ^ (i + 2) +
          (M k : ℝ) ^ 2 / (N k : ℝ) ^ (i + 3)) ≤
        ε * (M (k + 1) : ℝ) / (N (k + 1) : ℝ) ^ (i + 2) := by
  have hev := eventually_const_mul_absorptionRatio_le
    (2 * D / ε) (i + 1) zero_lt_one
  filter_upwards [hev] with k hk
  have hNk : (N k : ℝ) ≠ 0 := by exact_mod_cast N_ne_zero k
  have hNks : (N (k + 1) : ℝ) ≠ 0 := by exact_mod_cast N_ne_zero (k + 1)
  have hMks : (M (k + 1) : ℝ) ≠ 0 := by exact_mod_cast M_ne_zero (k + 1)
  have hε0 : ε ≠ 0 := hε.ne'
  have hsquare : (M k : ℝ) ^ 2 = (N k : ℝ) := by
    exact_mod_cast M_sq k
  have hsquares : (M (k + 1) : ℝ) ^ 2 = (N (k + 1) : ℝ) := by
    exact_mod_cast M_sq (k + 1)
  calc
    D * (1 / (N k : ℝ) ^ (i + 2) +
          (M k : ℝ) ^ 2 / (N k : ℝ) ^ (i + 3)) =
        (ε * (M (k + 1) : ℝ) / (N (k + 1) : ℝ) ^ (i + 2)) *
          ((2 * D / ε) * absorptionRatio (i + 1) k) := by
            unfold absorptionRatio
            rw [hsquare, ← hsquares]
            field_simp [absorptionRatio, hNk, hNks, hMks, hε0]
            ring
    _ ≤ (ε * (M (k + 1) : ℝ) / (N (k + 1) : ℝ) ^ (i + 2)) * 1 := by
      exact mul_le_mul_of_nonneg_left hk (by positivity)
    _ = ε * (M (k + 1) : ℝ) / (N (k + 1) : ℝ) ^ (i + 2) := by ring

/-- `Absorbs ε D d e k` says that every one of the first `d` coordinates has
enough room at block `k+1` to absorb the error made at block `k`. -/
def Absorbs (ε D : ℕ → ℝ) (d e k : ℕ) : Prop :=
  ∀ i < d,
    D d * (1 / (N k : ℝ) ^ (i + 2) +
        (M k : ℝ) ^ 2 / (N k : ℝ) ^ (i + 3)) ≤
      ε e * (M (k + 1) : ℝ) / (N (k + 1) : ℝ) ^ (i + 2)

lemma eventually_absorbs (ε D : ℕ → ℝ)
    (hε : ∀ e, 0 < ε e) (hD : ∀ d, 0 ≤ D d) (d e : ℕ) :
    ∀ᶠ k : ℕ in atTop, Absorbs ε D d e k := by
  have hi : ∀ i ∈ Finset.range d, ∀ᶠ k : ℕ in atTop,
      D d * (1 / (N k : ℝ) ^ (i + 2) +
          (M k : ℝ) ^ 2 / (N k : ℝ) ^ (i + 3)) ≤
        ε e * (M (k + 1) : ℝ) / (N (k + 1) : ℝ) ^ (i + 2) := by
    intro i hi
    exact eventually_localAbsorption i (hD d) (hε e)
  filter_upwards [(Finset.eventually_all (Finset.range d)).2 hi] with k hk
  intro i hid
  exact hk i (Finset.mem_range.2 hid)

/-- Extract a concrete threshold from an eventual predicate. -/
def eventualThreshold {P : ℕ → Prop} (hP : ∀ᶠ k : ℕ in atTop, P k) : ℕ :=
  Classical.choose (eventually_atTop.1 hP)

lemma eventualThreshold_spec {P : ℕ → Prop} (hP : ∀ᶠ k : ℕ in atTop, P k)
    {k : ℕ} (hk : eventualThreshold hP ≤ k) : P k :=
  Classical.choose_spec (eventually_atTop.1 hP) k hk

/-- A threshold at which both the stationary-dimension and dimension-transition
absorption estimates hold. -/
def absorptionThreshold (ε D : ℕ → ℝ)
    (hε : ∀ e, 0 < ε e) (hD : ∀ d, 0 ≤ D d) (d : ℕ) : ℕ :=
  max d (eventualThreshold
    ((eventually_absorbs ε D hε hD d d).and
      (eventually_absorbs ε D hε hD d (d + 1))))

lemma absorptionThreshold_ge (ε D : ℕ → ℝ)
    (hε : ∀ e, 0 < ε e) (hD : ∀ d, 0 ≤ D d) (d : ℕ) :
    d ≤ absorptionThreshold ε D hε hD d :=
  le_max_left _ _

lemma absorptionThreshold_spec (ε D : ℕ → ℝ)
    (hε : ∀ e, 0 < ε e) (hD : ∀ d, 0 ≤ D d) (d : ℕ) {k : ℕ}
    (hk : absorptionThreshold ε D hε hD d ≤ k) :
    Absorbs ε D d d k ∧ Absorbs ε D d (d + 1) k := by
  let hboth := (eventually_absorbs ε D hε hD d d).and
    (eventually_absorbs ε D hε hD d (d + 1))
  apply @eventualThreshold_spec
    (fun k => Absorbs ε D d d k ∧ Absorbs ε D d (d + 1) k) hboth k
  dsimp [absorptionThreshold] at hk
  exact (le_max_right d _).trans hk

/-- Turn arbitrary lower bounds into a strictly increasing schedule which also
lies above the diagonal. -/
def schedule (threshold : ℕ → ℕ) : ℕ → ℕ
  | 0 => threshold 0
  | d + 1 => max (schedule threshold d + 1) (max (threshold (d + 1)) (d + 1))

lemma threshold_le_schedule (threshold : ℕ → ℕ) (d : ℕ) :
    threshold d ≤ schedule threshold d := by
  cases d with
  | zero => rfl
  | succ d =>
      exact (le_max_left _ _).trans (le_max_right _ _)

lemma index_le_schedule (threshold : ℕ → ℕ) (d : ℕ) :
    d ≤ schedule threshold d := by
  cases d with
  | zero => exact Nat.zero_le _
  | succ d =>
      exact (le_max_right _ _).trans (le_max_right _ _)

lemma schedule_succ (threshold : ℕ → ℕ) (d : ℕ) :
    schedule threshold d + 1 ≤ schedule threshold (d + 1) :=
  le_max_left _ _

lemma schedule_strictMono (threshold : ℕ → ℕ) :
    StrictMono (schedule threshold) := by
  exact strictMono_nat_of_lt_succ fun d => lt_of_lt_of_le (Nat.lt_succ_self _)
    (schedule_succ threshold d)

/-- Largest scheduled dimension which has started by stage `k`. -/
def activeDim (threshold : ℕ → ℕ) (k : ℕ) : ℕ :=
  Nat.findGreatest (fun d => schedule threshold d ≤ k) k

lemma activeDim_le (threshold : ℕ → ℕ) (k : ℕ) :
    activeDim threshold k ≤ k :=
  Nat.findGreatest_le k

lemma le_activeDim (threshold : ℕ → ℕ) {d k : ℕ}
    (hdk : d ≤ k) (hstart : schedule threshold d ≤ k) :
    d ≤ activeDim threshold k :=
  Nat.le_findGreatest hdk hstart

lemma scheduled_le_activeDim (threshold : ℕ → ℕ) {d k : ℕ}
    (hstart : schedule threshold d ≤ k) : d ≤ activeDim threshold k := by
  exact le_activeDim threshold ((index_le_schedule threshold d).trans hstart) hstart

lemma schedule_activeDim_le (threshold : ℕ → ℕ) {k : ℕ}
    (hk : schedule threshold 0 ≤ k) :
    schedule threshold (activeDim threshold k) ≤ k := by
  unfold activeDim
  exact Nat.findGreatest_spec (P := fun d => schedule threshold d ≤ k)
    (Nat.zero_le k) hk

lemma activeDim_mono (threshold : ℕ → ℕ) :
    Monotone (activeDim threshold) := by
  intro k l hkl
  by_cases hk : schedule threshold 0 ≤ k
  · apply le_activeDim threshold
    · exact (activeDim_le threshold k).trans hkl
    · exact (schedule_activeDim_le threshold hk).trans hkl
  · have hzero : activeDim threshold k = 0 := by
      rw [activeDim, Nat.findGreatest_eq_iff]
      refine ⟨Nat.zero_le _, ?_, ?_⟩
      · simp
      · intro n hn hnk hnstart
        apply hk
        exact ((schedule_strictMono threshold).monotone (Nat.zero_le n)).trans hnstart
    simp [hzero]

lemma activeDim_succ_le (threshold : ℕ → ℕ) (k : ℕ) :
    activeDim threshold (k + 1) ≤ activeDim threshold k + 1 := by
  by_cases hzero : activeDim threshold (k + 1) = 0
  · simp [hzero]
  · have hpos : 0 < activeDim threshold (k + 1) := Nat.pos_of_ne_zero hzero
    let d := activeDim threshold (k + 1) - 1
    have hd : d + 1 = activeDim threshold (k + 1) := by
      dsimp [d]
      omega
    have hstarted : schedule threshold (d + 1) ≤ k + 1 := by
      rw [hd]
      have hfg : Nat.findGreatest (fun d => schedule threshold d ≤ k + 1) (k + 1) =
          activeDim threshold (k + 1) := rfl
      exact (Nat.findGreatest_eq_iff.mp hfg).2.1 hzero
    have hdstart : schedule threshold d ≤ k := by
      have := schedule_succ threshold d
      omega
    have hdk : d ≤ k := (index_le_schedule threshold d).trans hdstart
    have hdactive : d ≤ activeDim threshold k := le_activeDim threshold hdk hdstart
    omega

lemma activeDim_succ_eq_or_eq_succ (threshold : ℕ → ℕ) (k : ℕ) :
    activeDim threshold (k + 1) = activeDim threshold k ∨
      activeDim threshold (k + 1) = activeDim threshold k + 1 := by
  have hmono : activeDim threshold k ≤ activeDim threshold (k + 1) := by
    simpa only [Nat.succ_eq_add_one] using activeDim_mono threshold (Nat.le_succ k)
  have hle := activeDim_succ_le threshold k
  omega

lemma tendsto_activeDim (threshold : ℕ → ℕ) :
    Tendsto (activeDim threshold) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro d
  refine ⟨max (schedule threshold d) d, ?_⟩
  intro k hk
  apply le_activeDim threshold
  · exact (le_max_right _ _).trans hk
  · exact (le_max_left _ _).trans hk

/-- If the threshold function was built from `absorptionThreshold`, the active
dimension has both estimates needed to stay fixed or increase by one. -/
lemma activeDim_absorbs (ε D : ℕ → ℝ)
    (hε : ∀ e, 0 < ε e) (hD : ∀ d, 0 ≤ D d) {k : ℕ}
    (hk : schedule (absorptionThreshold ε D hε hD) 0 ≤ k) :
    let d := activeDim (absorptionThreshold ε D hε hD) k
    Absorbs ε D d d k ∧ Absorbs ε D d (d + 1) k := by
  dsimp only
  apply absorptionThreshold_spec ε D hε hD
  exact (threshold_le_schedule (absorptionThreshold ε D hε hD) _).trans
    (schedule_activeDim_le _ hk)

/-- Every polynomial weight is summable against the reciprocal geometric
scale. -/
lemma summable_polynomial_div_N (p : ℕ) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ p / (N k : ℝ)) := by
  have hbase : Summable (fun k : ℕ => (k : ℝ) ^ p * ((1 : ℝ) / 16) ^ k) := by
    simpa [Real.norm_of_nonneg] using
      (summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) p
        (r := ((1 : ℝ) / 16)) (by norm_num))
  have hshift := (summable_nat_add_iff 1).2 hbase
  apply hshift.congr
  intro k
  simp only [N, Nat.cast_pow, Nat.cast_ofNat]
  change ((k + 1 : ℕ) : ℝ) ^ p * ((1 : ℝ) / 16) ^ (k + 1) =
    ((k + 1 : ℕ) : ℝ) ^ p / (16 : ℝ) ^ (k + 1)
  rw [one_div_pow]
  ring

/-- The same summability remains true with any positive fixed power of `N` in
the denominator. -/
lemma summable_polynomial_div_N_pow (p q : ℕ) (hq : 0 < q) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ p / (N k : ℝ) ^ q) := by
  apply (summable_polynomial_div_N p).of_nonneg_of_le
  · intro k
    positivity
  · intro k
    have hpowNat : N k ^ 1 ≤ N k ^ q :=
      Nat.pow_le_pow_right (one_le_N k) (by omega)
    have hpow : (N k : ℝ) ≤ (N k : ℝ) ^ q := by
      exact_mod_cast (by simpa using hpowNat)
    exact div_le_div_of_nonneg_left (by positivity)
      (Nat.cast_pos.2 (N_pos k)) hpow

lemma summable_succ_div_N :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / (N k : ℝ)) := by
  simpa using summable_polynomial_div_N 1

lemma summable_const_mul_polynomial_div_N (C : ℝ) (p : ℕ) :
    Summable (fun k : ℕ => C * (((k + 1 : ℕ) : ℝ) ^ p / (N k : ℝ))) :=
  (summable_polynomial_div_N p).mul_left C

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos266/Erdos266Series.lean` -/

section
/-!
# Coordinate block series for Erdős problem 266

These definitions and lemmas connect the geometric scales with the abstract
diagonal construction.  They contain no finite-dimensional approximation:
only positivity, comparison, regrouping, and tail identities.
-/

open Filter
open scoped BigOperators Topology



noncomputable section

/-- The unperturbed contribution of geometric block `k` in coordinate `i+1`. -/
def referenceCoordinateBlock (dim : ℕ → ℕ) (i k : ℕ) : ℝ :=
  ∑ j : Fin (dim k), reciprocalCoordinate (i + 1)
    ((((j.1 + 1) * N k : ℕ) : ℝ))

/-- The contribution after applying a total family of integral offsets. -/
def actualCoordinateBlock (dim : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (i k : ℕ) : ℝ :=
  ∑ j : Fin (dim k), reciprocalCoordinate (i + 1)
    (blockNat N z k j.1 : ℝ)

lemma referenceCoordinateBlock_nonneg (dim : ℕ → ℕ) (i k : ℕ) :
    0 ≤ referenceCoordinateBlock dim i k := by
  exact Finset.sum_nonneg fun _ _ => reciprocalCoordinate_nonneg _ (by positivity)

lemma referenceCoordinateBlock_le (dim : ℕ → ℕ)
    (hdim : ∀ k, dim k ≤ k + 1) (i k : ℕ) :
    referenceCoordinateBlock dim i k ≤ ((k + 1 : ℕ) : ℝ) / N k := by
  calc
    referenceCoordinateBlock dim i k
        ≤ ∑ _j : Fin (dim k), (1 : ℝ) / N k := by
          unfold referenceCoordinateBlock
          apply Finset.sum_le_sum
          intro j _
          have hpoint : (0 : ℝ) < (((j.1 + 1) * N k : ℕ) : ℝ) := by
            exact_mod_cast Nat.mul_pos (Nat.succ_pos j.1) (N_pos k)
          calc
            reciprocalCoordinate (i + 1) ((((j.1 + 1) * N k : ℕ) : ℝ))
                ≤ ((((j.1 + 1) * N k : ℕ) : ℝ))⁻¹ :=
                  reciprocalCoordinate_le_inv (i + 1) (by omega) hpoint
            _ ≤ (N k : ℝ)⁻¹ := by
                  apply inv_anti₀ (by exact_mod_cast N_pos k)
                  exact_mod_cast Nat.le_mul_of_pos_left (N k) (Nat.succ_pos j.1)
            _ = (1 : ℝ) / N k := by simp [one_div]
    _ = (dim k : ℝ) * (1 / N k) := by simp
    _ ≤ (k + 1 : ℝ) * (1 / N k) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdim k) (by positivity)
    _ = ((k + 1 : ℕ) : ℝ) / N k := by push_cast; ring

theorem summable_referenceCoordinateBlock (dim : ℕ → ℕ)
    (hdim : ∀ k, dim k ≤ k + 1) (i : ℕ) :
    Summable (referenceCoordinateBlock dim i) := by
  exact Summable.of_nonneg_of_le
    (referenceCoordinateBlock_nonneg dim i)
    (referenceCoordinateBlock_le dim hdim i)
    summable_succ_div_N

/-- The unperturbed tail beginning at stage `k`. -/
def referenceCoordinateTail (dim : ℕ → ℕ) (i k : ℕ) : ℝ :=
  ∑' n, referenceCoordinateBlock dim i (n + k)

lemma referenceCoordinateTail_succ (dim : ℕ → ℕ)
    (hdim : ∀ k, dim k ≤ k + 1) (i k : ℕ) :
    referenceCoordinateTail dim i k =
      referenceCoordinateBlock dim i k + referenceCoordinateTail dim i (k + 1) := by
  unfold referenceCoordinateTail
  rw [(summable_nat_add_iff k).2 (summable_referenceCoordinateBlock dim hdim i) |>.tsum_eq_zero_add]
  simp only [Nat.zero_add]
  congr 1
  apply tsum_congr
  intro n
  apply congrArg (referenceCoordinateBlock dim i)
  omega

theorem tendsto_referenceCoordinateTail (dim : ℕ → ℕ) (i : ℕ) :
    Tendsto (referenceCoordinateTail dim i) atTop (𝓝 0) := by
  unfold referenceCoordinateTail
  convert (tendsto_sum_nat_add (referenceCoordinateBlock dim i)) using 1

lemma actualCoordinateBlock_nonneg (dim : ℕ → ℕ) (z : ℕ → ℕ → ℤ)
    (_hpos : ∀ k j, 0 < blockNat N z k j) (i k : ℕ) :
    0 ≤ actualCoordinateBlock dim z i k := by
  exact Finset.sum_nonneg fun j _ =>
    reciprocalCoordinate_nonneg _ (Nat.cast_nonneg _)

/-- Bounded offsets make every actual coordinate block series summable. -/
theorem summable_actualCoordinateBlock
    (dim : ℕ → ℕ) (z : ℕ → ℕ → ℤ)
    (hz : OffsetsBounded M z) (hdim : ∀ k, dim k ≤ k + 1) (i : ℕ) :
    Summable (actualCoordinateBlock dim z i) := by
  have htwoM : ∀ k, 2 * M k ≤ N k := by
    intro k
    rw [← M_sq]
    have hM4 : 4 ≤ M k := by
      rw [M]
      exact Nat.le_pow (a := 4) (by omega)
    nlinarith
  have hsigma := summable_coordinate_blocks dim N M z N_pos htwoM hz hdim
    summable_succ_div_N (i + 1) (by omega)
  have hsplit := (summable_sigma_of_nonneg (fun _ =>
    reciprocalCoordinate_nonneg _ (Nat.cast_nonneg _))).mp hsigma
  convert hsplit.2 using 1
  funext k
  rw [tsum_fintype]
  rfl

/-- Regroup the sigma-indexed coordinate series as the series of actual blocks. -/
theorem tsum_actualCoordinateBlock
    (dim : ℕ → ℕ) (z : ℕ → ℕ → ℤ)
    (hz : OffsetsBounded M z) (hdim : ∀ k, dim k ≤ k + 1) (i : ℕ) :
    (∑' p : Σ k, Fin (dim k),
      reciprocalCoordinate (i + 1) (blockNat N z p.1 p.2.1 : ℝ)) =
      ∑' k, actualCoordinateBlock dim z i k := by
  have htwoM : ∀ k, 2 * M k ≤ N k := by
    intro k
    rw [← M_sq]
    have hM4 : 4 ≤ M k := by
      rw [M]
      exact Nat.le_pow (a := 4) (by omega)
    nlinarith
  simpa only [actualCoordinateBlock] using
    (tsum_coordinate_blocks dim N M z N_pos htwoM hz hdim
      summable_succ_div_N (i + 1) (by omega))

/-- The nested-box radius used for coordinate `i` at stage `k`. -/
def coordinateRadius (ε : ℕ → ℝ) (dim : ℕ → ℕ) (i k : ℕ) : ℝ :=
  ε (dim k) * (M k : ℝ) / (N k : ℝ) ^ (i + 2)

lemma coordinateRadius_pos (ε : ℕ → ℝ) (dim : ℕ → ℕ)
    (hε : ∀ d, 0 < ε d) (i k : ℕ) :
    0 < coordinateRadius ε dim i k := by
  unfold coordinateRadius
  exact div_pos (mul_pos (hε (dim k)) (by exact_mod_cast M_pos k))
    (pow_pos (by exact_mod_cast N_pos k) _)

lemma coordinateRadius_le_inv_N (ε : ℕ → ℝ) (dim : ℕ → ℕ)
    (hε0 : ∀ d, 0 ≤ ε d) (hε1 : ∀ d, ε d ≤ 1) (i k : ℕ) :
    coordinateRadius ε dim i k ≤ (1 : ℝ) / N k := by
  have hN : (0 : ℝ) < N k := by exact_mod_cast N_pos k
  have hden : (0 : ℝ) < (N k : ℝ) ^ (i + 2) := pow_pos hN _
  have hM : (0 : ℝ) ≤ M k := by positivity
  have hMN : (M k : ℝ) ≤ N k := by exact_mod_cast M_le_N k
  have hpowNat : N k ^ 2 ≤ N k ^ (i + 2) :=
    Nat.pow_le_pow_right (one_le_N k) (by omega)
  have hpow : (N k : ℝ) ^ 2 ≤ (N k : ℝ) ^ (i + 2) := by
    exact_mod_cast hpowNat
  calc
    coordinateRadius ε dim i k
        ≤ 1 * (M k : ℝ) / (N k : ℝ) ^ (i + 2) := by
          unfold coordinateRadius
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hε1 (dim k)) hM) hden.le
    _ ≤ 1 * (N k : ℝ) / (N k : ℝ) ^ (i + 2) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hMN (by norm_num)) hden.le
    _ ≤ 1 * (N k : ℝ) / (N k : ℝ) ^ 2 := by
          exact div_le_div_of_nonneg_left (by positivity) (pow_pos hN 2) hpow
    _ = (1 : ℝ) / N k := by field_simp

theorem tendsto_coordinateRadius (ε : ℕ → ℝ) (dim : ℕ → ℕ)
    (hε0 : ∀ d, 0 ≤ ε d) (hε1 : ∀ d, ε d ≤ 1) (i : ℕ) :
    Tendsto (coordinateRadius ε dim i) atTop (𝓝 0) := by
  have hinv : Tendsto (fun k : ℕ => (1 : ℝ) / N k) atTop (𝓝 0) := by
    have hs : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ 0 / (N k : ℝ)) :=
      summable_polynomial_div_N 0
    simpa using hs.tendsto_atTop_zero
  exact squeeze_zero'
    (Eventually.of_forall fun k => by
      unfold coordinateRadius
      exact div_nonneg (mul_nonneg (hε0 (dim k)) (by positivity)) (by positivity))
    (Eventually.of_forall (coordinateRadius_le_inv_N ε dim hε0 hε1 i)) hinv

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos266.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 266.
https://www.erdosproblems.com/forum/thread/266

Informal authors:
- Vjekoslav Kovač
- Terence Tao

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos266.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/266.lean
-/

/-!
# Erdős Problem 266

Kovač and Tao disproved the proposed assertion.  The construction below is a
specialization of their simultaneous block-approximation argument to the
positive integral shifts needed here.  The absence of a monotonicity condition
in the formal statement lets us use geometric block scales.
-/

open Filter
open scoped BigOperators Topology



noncomputable section

private lemma two_mul_M_le_N (k : ℕ) : 2 * M k ≤ N k := by
  rw [← M_sq]
  have hM4 : 4 ≤ M k := by
    rw [M]
    exact Nat.le_pow (a := 4) (by omega)
  nlinarith

private def constructionThreshold : ℕ → ℕ :=
  absorptionThreshold Erdos266Block.blockEpsilon Erdos266Block.blockD
    Erdos266Block.blockEpsilon_pos Erdos266Block.blockD_nonneg

private def constructionDim (k : ℕ) : ℕ :=
  activeDim constructionThreshold k

private lemma constructionDim_zero : constructionDim 0 = 0 := by
  exact Nat.eq_zero_of_le_zero (activeDim_le constructionThreshold 0)

private lemma constructionDim_mono : Monotone constructionDim :=
  activeDim_mono constructionThreshold

private lemma constructionDim_step (k : ℕ) :
    constructionDim (k + 1) ≤ constructionDim k + 1 :=
  activeDim_succ_le constructionThreshold k

private lemma constructionDim_le (k : ℕ) : constructionDim k ≤ k + 1 :=
  (activeDim_le constructionThreshold k).trans (Nat.le_succ k)

private lemma constructionDim_unbounded (i : ℕ) :
    ∃ k, i < constructionDim k := by
  let k := schedule constructionThreshold (i + 1)
  refine ⟨k, ?_⟩
  have hle : i + 1 ≤ activeDim constructionThreshold k :=
    scheduled_le_activeDim constructionThreshold (by rfl)
  simpa [constructionDim] using hle

private lemma schedule_zero_le_of_constructionDim_pos {k : ℕ}
    (hkpos : 0 < constructionDim k) : schedule constructionThreshold 0 ≤ k := by
  by_contra hk
  have hzero : activeDim constructionThreshold k = 0 := by
    rw [activeDim, Nat.findGreatest_eq_iff]
    refine ⟨Nat.zero_le _, ?_, ?_⟩
    · simp
    · intro n _hn _hnk hnstart
      apply hk
      exact ((schedule_strictMono constructionThreshold).monotone (Nat.zero_le n)).trans hnstart
  exact (Nat.ne_of_gt hkpos) (by simpa [constructionDim] using hzero)

/-- A block chosen at stage `k` is a total integer tuple.  Only its first
`constructionDim k` entries are used, but the total representation makes the
recursive choice type independent of `k`. -/
private def admissibleBlock (k : ℕ) (b : ℕ → ℤ) : Prop :=
  ∀ j, |(b j : ℝ)| ≤ M k

private def stageActualBlock (k : ℕ) (b : ℕ → ℤ) (i : ℕ) : ℝ :=
  ∑ j : Fin (constructionDim k), reciprocalCoordinate (i + 1)
    (((((j.1 + 1) * N k : ℕ) : ℝ)) + b j.1)

private lemma stageActualBlock_eq_actualCoordinateBlock
    (z : ℕ → ℕ → ℤ) (hz : OffsetsBounded M z) (i k : ℕ) :
    stageActualBlock k (z k) i = actualCoordinateBlock constructionDim z i k := by
  unfold stageActualBlock actualCoordinateBlock
  apply Finset.sum_congr rfl
  intro j _hj
  rw [blockNat_cast N_pos two_mul_M_le_N hz]
  push_cast
  rfl

private theorem refineBlock (k : ℕ)
    (error : Fin (constructionDim k) → ℝ)
    (herror : ∀ i, |error i| ≤
      coordinateRadius Erdos266Block.blockEpsilon constructionDim i k) :
    ∃ b : ℕ → ℤ, admissibleBlock k b ∧ ∀ i,
      |error i + referenceCoordinateBlock constructionDim i k -
          stageActualBlock k b i| ≤
        coordinateRadius Erdos266Block.blockEpsilon constructionDim i (k + 1) := by
  let d := constructionDim k
  let q : Fin d → ℝ := fun i => -error i
  have hq : ∀ i, |q i| ≤
      Erdos266Block.blockEpsilon d * (M k : ℝ) / (N k : ℝ) ^ (i.1 + 2) := by
    intro i
    simpa [q, d, coordinateRadius] using herror i
  obtain ⟨z, hz, hzerr⟩ :=
    Erdos266Block.discrete_block_approximation_uniform d (N k) (M k)
      (N_pos k) (one_le_M k)
      (four_mul_dim_mul_M_le_N (by simpa [d] using constructionDim_le k))
      q hq
  let b : ℕ → ℤ := fun j => if h : j < d then z ⟨j, h⟩ else 0
  have hb : admissibleBlock k b := by
    intro j
    by_cases h : j < d
    · simpa [b, h] using hz ⟨j, h⟩
    · simp [b, h]
  refine ⟨b, hb, ?_⟩
  intro i
  have href : referenceCoordinateBlock constructionDim i.1 k =
      Erdos266Block.referenceBlock d (N k) i := by
    unfold referenceCoordinateBlock Erdos266Block.referenceBlock
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Erdos266Block.coord_eq_reciprocalCoordinate]
  have hactual : stageActualBlock k b i.1 =
      Erdos266Block.perturbedBlock d (N k) z i := by
    unfold stageActualBlock Erdos266Block.perturbedBlock
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Erdos266Block.coord_eq_reciprocalCoordinate]
    have hjlt : j.1 < d := j.isLt
    simp [b, hjlt]
  have hdpos : 0 < constructionDim k :=
    (Nat.zero_le i.1).trans_lt i.isLt
  have hk0 := schedule_zero_le_of_constructionDim_pos hdpos
  have habsPair := activeDim_absorbs Erdos266Block.blockEpsilon Erdos266Block.blockD
    Erdos266Block.blockEpsilon_pos Erdos266Block.blockD_nonneg
    (k := k) (by simpa [constructionThreshold] using hk0)
  have habs :
      Erdos266Block.blockD d *
          (1 / (N k : ℝ) ^ (i.1 + 2) +
            (M k : ℝ) ^ 2 / (N k : ℝ) ^ (i.1 + 3)) ≤
        Erdos266Block.blockEpsilon (constructionDim (k + 1)) *
          (M (k + 1) : ℝ) / (N (k + 1) : ℝ) ^ (i.1 + 2) := by
    rcases activeDim_succ_eq_or_eq_succ constructionThreshold k with hsame | hsucc
    · rw [show constructionDim (k + 1) = d by simpa [constructionDim, d] using hsame]
      exact habsPair.1 i.1 i.isLt
    · rw [show constructionDim (k + 1) = d + 1 by simpa [constructionDim, d] using hsucc]
      exact habsPair.2 i.1 i.isLt
  have herr := hzerr i
  rw [← href, ← hactual] at herr
  have hfinal := herr.trans habs
  dsimp [q] at hfinal
  simpa [coordinateRadius, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hfinal

private def constructionScheme : Erdos266Diagonal.Scheme (ℕ → ℤ) where
  dim := constructionDim
  dim_zero := constructionDim_zero
  dim_mono := constructionDim_mono
  dim_step := constructionDim_step
  dim_unbounded := constructionDim_unbounded
  refBlock := referenceCoordinateBlock constructionDim
  actualBlock := stageActualBlock
  admissible := admissibleBlock
  radius := coordinateRadius Erdos266Block.blockEpsilon constructionDim
  tail := referenceCoordinateTail constructionDim
  radius_pos := coordinateRadius_pos _ _ Erdos266Block.blockEpsilon_pos
  tail_succ := referenceCoordinateTail_succ constructionDim constructionDim_le
  refine := refineBlock

private def chosenOffsets (k j : ℕ) : ℤ :=
  constructionScheme.choice k j

private lemma chosenOffsets_bounded : OffsetsBounded M chosenOffsets := by
  intro k j
  have h := constructionScheme.choice_admissible k
  exact h j

private lemma stageActualBlock_chosen_eq (i k : ℕ) :
    stageActualBlock k (constructionScheme.choice k) i =
      actualCoordinateBlock constructionDim chosenOffsets i k := by
  exact stageActualBlock_eq_actualCoordinateBlock chosenOffsets chosenOffsets_bounded i k

private theorem summable_chosen_actual_blocks (i : ℕ) :
    Summable (fun k => constructionScheme.actualBlock k
      (constructionScheme.choice k) i) := by
  have h := summable_actualCoordinateBlock constructionDim chosenOffsets
    chosenOffsets_bounded constructionDim_le i
  convert h using 1
  funext k
  exact stageActualBlock_chosen_eq i k

private theorem construction_target_eq_tsum (i : ℕ) :
    (constructionScheme.target i : ℝ) =
      ∑' k, stageActualBlock k (constructionScheme.choice k) i := by
  apply constructionScheme.target_eq_tsum
  · exact summable_chosen_actual_blocks
  · exact tendsto_referenceCoordinateTail constructionDim
  · exact tendsto_coordinateRadius Erdos266Block.blockEpsilon constructionDim
      (fun d => (Erdos266Block.blockEpsilon_pos d).le)
      Erdos266Block.blockEpsilon_le_one

private theorem rational_block_coordinate (i : ℕ) :
    ∃ q : ℚ,
      (∑' p : Erdos266Diagonal.Scheme.BlockIndex constructionDim,
        reciprocalCoordinate (i + 1)
          (blockNat N chosenOffsets p.1 p.2.1 : ℝ)) = (q : ℝ) := by
  refine ⟨constructionScheme.target i, ?_⟩
  calc
    (∑' p : Erdos266Diagonal.Scheme.BlockIndex constructionDim,
        reciprocalCoordinate (i + 1)
          (blockNat N chosenOffsets p.1 p.2.1 : ℝ)) =
        ∑' k, actualCoordinateBlock constructionDim chosenOffsets i k :=
      tsum_actualCoordinateBlock constructionDim chosenOffsets chosenOffsets_bounded
        constructionDim_le i
    _ = ∑' k, stageActualBlock k (constructionScheme.choice k) i := by
      apply tsum_congr
      intro k
      exact (stageActualBlock_chosen_eq i k).symm
    _ = (constructionScheme.target i : ℝ) := (construction_target_eq_tsum i).symm

private def blockEmbedding (n : ℕ) :
    Erdos266Diagonal.Scheme.BlockIndex constructionDim :=
  ⟨schedule constructionThreshold (n + 1),
    ⟨0, by
      have hle : n + 1 ≤ constructionDim (schedule constructionThreshold (n + 1)) := by
        simpa [constructionDim] using
          (scheduled_le_activeDim constructionThreshold
            (show schedule constructionThreshold (n + 1) ≤
              schedule constructionThreshold (n + 1) from le_rfl))
      omega⟩⟩

private lemma blockEmbedding_injective : Function.Injective blockEmbedding := by
  intro n m hnm
  have hs : schedule constructionThreshold (n + 1) =
      schedule constructionThreshold (m + 1) := congrArg Sigma.fst hnm
  have hsucc : n + 1 = m + 1 :=
    (schedule_strictMono constructionThreshold).injective hs
  omega

private noncomputable def blockEnumeration :
    ℕ ≃ Erdos266Diagonal.Scheme.BlockIndex constructionDim := by
  letI : Infinite (Erdos266Diagonal.Scheme.BlockIndex constructionDim) :=
    Infinite.of_injective blockEmbedding blockEmbedding_injective
  exact nonempty_equiv_of_countable.some

/-- The positive-integer sequence witnessing the negative solution of
Problem 266. -/
private def counterexampleSequence (n : ℕ) : ℕ :=
  let p := blockEnumeration n
  blockNat N chosenOffsets p.1 p.2.1

private lemma counterexampleSequence_pos (n : ℕ) :
    1 ≤ counterexampleSequence n := by
  dsimp [counterexampleSequence]
  exact blockNat_pos N_pos two_mul_M_le_N chosenOffsets_bounded _ _

private theorem summable_counterexample_reciprocals :
    Summable (fun n => (1 : ℝ) / counterexampleSequence n) := by
  have hsigma := summable_reciprocal_blocks constructionDim N M chosenOffsets
    N_pos two_mul_M_le_N chosenOffsets_bounded constructionDim_le summable_succ_div_N
  have hreindex :=
    (Erdos266Diagonal.Scheme.summable_reindex_iff constructionDim
      (fun p : Erdos266Diagonal.Scheme.BlockIndex constructionDim =>
        (1 : ℝ) / blockNat N chosenOffsets p.1 p.2.1) blockEnumeration).2 hsigma
  simpa [counterexampleSequence] using hreindex

private theorem rational_counterexample_coordinates :
    ∀ i : ℕ, 1 ≤ i →
      ∃ q : ℚ,
        (∑' n, reciprocalCoordinate i (counterexampleSequence n : ℝ)) = (q : ℝ) := by
  intro i hi
  obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
  obtain ⟨q, hq⟩ := rational_block_coordinate r
  refine ⟨q, ?_⟩
  calc
    (∑' n, reciprocalCoordinate (r + 1) (counterexampleSequence n : ℝ)) =
        ∑' p : Erdos266Diagonal.Scheme.BlockIndex constructionDim,
          reciprocalCoordinate (r + 1)
            (blockNat N chosenOffsets p.1 p.2.1 : ℝ) := by
      simpa [counterexampleSequence] using
        (Erdos266Diagonal.Scheme.tsum_reindex_eq constructionDim
          (fun p : Erdos266Diagonal.Scheme.BlockIndex constructionDim =>
            reciprocalCoordinate (r + 1)
              (blockNat N chosenOffsets p.1 p.2.1 : ℝ)) blockEnumeration)
    _ = (q : ℝ) := hq

/-- Erdős Problem 266 has a negative answer: there is a positive reciprocal-
summable sequence for which every positive integral shifted sum is rational. -/
theorem erdos_266 :
    ¬ ∀ (a : ℕ → ℕ), ((∀ n : ℕ, a n ≥ 1) ∧ Summable ((1 : ℝ) / a ·)) →
      ∃ t ≥ (1 : ℕ), Irrational (∑' n, (1 : ℝ) / ((a n) + t)) := by
  intro hclaim
  obtain ⟨t, ht, hirr⟩ := hclaim counterexampleSequence
    ⟨counterexampleSequence_pos, summable_counterexample_reciprocals⟩
  obtain ⟨q, hq⟩ := rational_tsum_shift_of_rational_coordinate_tsums
    counterexampleSequence counterexampleSequence_pos
    summable_counterexample_reciprocals rational_counterexample_coordinates t ht
  have hirr' : Irrational
      (∑' n, (1 : ℝ) / ((counterexampleSequence n : ℝ) + t)) := by
    simpa only [Nat.cast_add] using hirr
  rw [hq] at hirr'
  exact q.not_irrational hirr'

end

end

#print axioms erdos_266
-- 'Erdos266.erdos_266' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos266
