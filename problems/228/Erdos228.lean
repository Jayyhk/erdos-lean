import Mathlib

namespace Erdos228

/-
# Problem Description

Erdős Problem 228. Does there exist, for all large `n`, a polynomial `P` of degree `n` with
coefficients `±1` such that `√n ≪ |P(z)| ≪ √n` for all `|z| = 1`, with the implied constants
independent of `z` and `n`? `erdos_228` proves that there does.

The two `≪` are rendered as constants `c₁` and `c₂` bound before the quantifiers over `n` and
`z`, which is exactly the requirement that they be independent of both.

The formalisation is by plby (github.com/plby/lean-proofs),
`src/latest/ErdosProblems/Erdos228.lean` together with the modules of
`src/latest/ErdosProblems/Erdos228/`. Those files are concatenated here in dependency order,
with their project-internal imports removed so that `Mathlib` is the only import, each
module's contents kept in a `section` carrying its own `open` lines, and the whole wrapped
once in `namespace Erdos228` with the upstream trust-base print line removed. No mathematical
content is changed.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/Bernstein.lean` -/

section
/-!
# Bernstein bounds for complex polynomials and finite Fourier sums

This file proves the sharp Bernstein inequality on the complex unit circle,
its iterated Euler-derivative form used by the Balister--Bollobás--Morris--
Sahasrabudhe--Tiba construction, and elementary coefficient bounds for finite
Fourier sums.  The sharp proof uses polynomial reflection, the maximum-modulus
principle, and Gauss--Lucas.
-/

namespace Bernstein

open scoped BigOperators

/-- The purely imaginary frequency corresponding to the character
`x ↦ exp (k x i)`. -/
def frequency (k : ℕ) : ℂ := (k : ℂ) * Complex.I

/-- The `r`-th formal derivative of a finite Fourier sum.  At `r = 0` this is
the original sum; increasing `r` multiplies the `k`-th coefficient by `k i`.
-/
noncomputable def fourierDerivative (r : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ s, a k * frequency k ^ r *
    Complex.exp (((k : ℂ) * (x : ℂ)) * Complex.I)

@[simp]
theorem fourierDerivative_zero (s : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) :
    fourierDerivative 0 s a x =
      ∑ k ∈ s, a k * Complex.exp (((k : ℂ) * (x : ℂ)) * Complex.I) := by
  simp [fourierDerivative]

/-! ### Maximum-modulus preparation for the sharp Bernstein inequality -/

/-- Evaluation identity for the reflection of a polynomial in degree `n`. -/
theorem eval_reflect_mul_pow {p : Polynomial ℂ} {n : ℕ} (hdeg : p.natDegree ≤ n)
    {w : ℂ} (hw : w ≠ 0) :
    (p.reflect n).eval w⁻¹ * w ^ n = p.eval w := by
  let iw : Invertible w := invertibleOfNonzero hw
  simpa [invOf_eq_inv] using
    (@Polynomial.eval₂_reflect_mul_pow ℂ _ ℂ _ (RingHom.id ℂ) w iw n p hdeg)

/-- The degree-`n` reflection is bounded throughout the unit disk whenever
the original polynomial is bounded on the unit circle. -/
theorem norm_reflect_eval_le_of_circle_bound {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M)
    {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖(p.reflect n).eval u‖ ≤ M := by
  let q := p.reflect n
  have hboundary : ∀ z : ℂ, ‖z‖ = 1 → ‖q.eval z‖ ≤ M := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro hzzero
      simp [hzzero] at hz
    have hzinv : ‖z⁻¹‖ = 1 := by simp [hz]
    have hrel := eval_reflect_mul_pow hdeg (w := z⁻¹) (inv_ne_zero hz0)
    have hnorm : ‖q.eval z‖ = ‖p.eval z⁻¹‖ := by
      have hpownorm : ‖(z⁻¹) ^ n‖ = 1 := by
        rw [norm_pow, hzinv, one_pow]
      calc
        ‖q.eval z‖ = ‖q.eval z‖ * 1 := by simp
        _ = ‖q.eval z‖ * ‖(z⁻¹) ^ n‖ := by rw [hpownorm]
        _ = ‖q.eval z * (z⁻¹) ^ n‖ := by rw [norm_mul]
        _ = ‖p.eval z⁻¹‖ := by
          rw [show q.eval z * (z⁻¹) ^ n = p.eval z⁻¹ by simpa [q] using hrel]
    rw [hnorm]
    exact hM z⁻¹ hzinv
  by_cases hueq : ‖u‖ = 1
  · exact hboundary u hueq
  have hult : ‖u‖ < 1 := lt_of_le_of_ne hu hueq
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball
      ((p.reflect n).differentiableOn.diffContOnCl_ball Set.Subset.rfl)
      (C := M)
  · intro z hz
    apply hboundary z
    have hzsphere : z ∈ Metric.sphere (0 : ℂ) 1 :=
      Metric.frontier_ball_subset_sphere hz
    simpa [Metric.mem_sphere, dist_zero_right] using hzsphere
  · exact subset_closure (by simpa [Metric.mem_ball, dist_zero_right] using hult)

/-- Bernstein--Walsh outside the disk, in the elementary polynomial form
needed for the proof of the sharp circle derivative bound. -/
theorem norm_eval_le_circle_bound_mul_pow {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M)
    {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ‖p.eval w‖ ≤ M * ‖w‖ ^ n := by
  have hw0 : w ≠ 0 := by
    apply norm_ne_zero_iff.mp
    linarith
  have hu : ‖w⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hw)).2 hw
  have hq := norm_reflect_eval_le_of_circle_bound hdeg hM hu
  have hrel := eval_reflect_mul_pow hdeg hw0
  calc
    ‖p.eval w‖ = ‖(p.reflect n).eval w⁻¹‖ * ‖w‖ ^ n := by
      rw [← hrel, norm_mul, norm_pow]
    _ ≤ M * ‖w‖ ^ n :=
      mul_le_mul_of_nonneg_right hq (by positivity)

/-- Every coefficient up to a prescribed degree is bounded by the uniform
bound on the unit circle.  We only need the top coefficient below. -/
theorem norm_coeff_le_of_circle_bound {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M) :
    ‖p.coeff n‖ ≤ M := by
  have hq := norm_reflect_eval_le_of_circle_bound hdeg hM (u := (0 : ℂ)) (by norm_num)
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect,
    Polynomial.revAt_zero] at hq
  exact hq

/-! ### Sharp Bernstein inequality on the unit circle -/

/-- **Bernstein's inequality on the unit circle.**  If a complex polynomial
has degree at most `n` and norm at most `M` on the unit circle, then its
derivative has norm at most `n M` there.

The proof is the classical short argument using polynomial reflection,
the maximum-modulus principle, and Gauss--Lucas.  If the asserted derivative
bound failed at `z`, subtract the monomial whose derivative cancels there.
The new polynomial has every zero strictly inside the unit disk, whereas
Gauss--Lucas would put the unit-circle point `z` in their convex hull.
-/
theorem norm_derivative_eval_le_degree_mul_circleSup {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ w : ℂ, ‖w‖ = 1 → ‖p.eval w‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖p.derivative.eval z‖ ≤ (n : ℝ) * M := by
  by_cases hn : n = 0
  · subst n
    have hpdeg : p.natDegree = 0 := Nat.eq_zero_of_le_zero hdeg
    rw [Polynomial.derivative_eq_zero.mpr hpdeg]
    simp
  have hnNat : 0 < n := Nat.pos_of_ne_zero hn
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  by_contra hbound
  rw [not_le] at hbound
  have hz0 : z ≠ 0 := by
    intro hzero
    simp [hzero] at hz
  let β : ℂ := p.derivative.eval z / ((n : ℂ) * z ^ (n - 1))
  have hdenom : (n : ℂ) * z ^ (n - 1) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast hn) (pow_ne_zero _ hz0)
  have hβcancel : β * (n : ℂ) * z ^ (n - 1) = p.derivative.eval z := by
    dsimp [β]
    field_simp
  have hβnorm : ‖β‖ = ‖p.derivative.eval z‖ / (n : ℝ) := by
    dsimp [β]
    rw [norm_div, norm_mul, norm_pow, hz, one_pow, mul_one]
    simp
  have hβM : M < ‖β‖ := by
    rw [hβnorm, lt_div_iff₀ hnReal]
    simpa [mul_comm] using hbound
  let P : Polynomial ℂ := p - Polynomial.C β * Polynomial.X ^ n
  have hpcoeff : ‖p.coeff n‖ ≤ M := norm_coeff_le_of_circle_bound hdeg hM
  have hcoeffne : p.coeff n ≠ β := by
    intro heq
    rw [heq] at hpcoeff
    exact (not_le_of_gt hβM) hpcoeff
  have hPcoeff : P.coeff n ≠ 0 := by
    simpa [P, Polynomial.coeff_C_mul_X_pow] using sub_ne_zero.mpr hcoeffne
  have hPnatDegreePos : 0 < P.natDegree :=
    hnNat.trans_le (Polynomial.le_natDegree_of_ne_zero hPcoeff)
  have hPdegreePos : 0 < P.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hPnatDegreePos
  have hPderiv : P.derivative.eval z = 0 := by
    rw [show P.derivative.eval z = p.derivative.eval z -
        β * (n : ℂ) * z ^ (n - 1) by
      simp only [P, Polynomial.derivative_sub, Polynomial.derivative_C_mul_X_pow,
        Polynomial.eval_sub, Polynomial.eval_C_mul, Polynomial.eval_X_pow]]
    exact sub_eq_zero.mpr hβcancel.symm
  have hPderiv_ne : P.derivative ≠ 0 := by
    rw [Polynomial.derivative_ne_zero]
    exact hPnatDegreePos.ne'
  have hzDerivRoot : z ∈ P.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    exact ⟨hPderiv_ne, hPderiv⟩
  have hroots : P.rootSet ℂ ⊆ Metric.ball 0 1 := by
    intro w hwroot
    rw [Polynomial.mem_rootSet] at hwroot
    have hPeval0 : P.eval w = 0 := by
      simpa [Polynomial.coe_aeval_eq_eval] using hwroot.2
    have hPeval : p.eval w = β * w ^ n := by
      apply sub_eq_zero.mp
      simpa [P] using hPeval0
    have hwlt : ‖w‖ < 1 := by
      by_contra hwlt
      have hwge : 1 ≤ ‖w‖ := le_of_not_gt hwlt
      have hout := norm_eval_le_circle_bound_mul_pow hdeg hM hwge
      have hmul : ‖β‖ * ‖w‖ ^ n ≤ M * ‖w‖ ^ n := by
        rw [hPeval, norm_mul, norm_pow] at hout
        exact hout
      have hpow : 0 < ‖w‖ ^ n := pow_pos (lt_of_lt_of_le zero_lt_one hwge) n
      have : ‖β‖ ≤ M := le_of_mul_le_mul_right hmul hpow
      exact (not_le_of_gt hβM) this
    simpa [Metric.mem_ball, dist_zero_right] using hwlt
  have hconvex : convexHull ℝ (P.rootSet ℂ) ⊆ Metric.ball 0 1 :=
    convexHull_min hroots (convex_ball 0 1)
  have hzHull : z ∈ convexHull ℝ (P.rootSet ℂ) :=
    Polynomial.rootSet_derivative_subset_convexHull_rootSet hPdegreePos hzDerivRoot
  have hzlt : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hconvex hzHull
  linarith

/-! ### Iteration for derivatives of `p (exp (i x))` -/

/-- The Euler derivative `z p'(z)`.  Under the substitution `z = exp (i x)`,
ordinary differentiation in `x` is multiplication of this operator by `i`.
-/
noncomputable def eulerDerivative (p : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.X * p.derivative

@[simp]
theorem eval_eulerDerivative (p : Polynomial ℂ) (z : ℂ) :
    (eulerDerivative p).eval z = z * p.derivative.eval z := by
  simp [eulerDerivative]

/-- The Euler derivative does not increase polynomial degree. -/
theorem natDegree_eulerDerivative_le (p : Polynomial ℂ) :
    (eulerDerivative p).natDegree ≤ p.natDegree := by
  by_cases hp : p.natDegree = 0
  · simp [eulerDerivative, Polynomial.derivative_of_natDegree_zero hp, hp]
  have hd := Polynomial.natDegree_derivative_le p
  calc
    (eulerDerivative p).natDegree ≤
        Polynomial.X.natDegree + p.derivative.natDegree := by
      exact Polynomial.natDegree_mul_le
    _ ≤ 1 + (p.natDegree - 1) := by
      simp only [Polynomial.natDegree_X]
      exact Nat.add_le_add_left hd 1
    _ = p.natDegree := by omega

/-- Every iterate of the Euler derivative has degree at most that of the
starting polynomial. -/
theorem natDegree_iterate_eulerDerivative_le (r : ℕ) (p : Polynomial ℂ) :
    (eulerDerivative^[r] p).natDegree ≤ p.natDegree := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      exact (natDegree_eulerDerivative_le _).trans ih

/-- Iterated sharp Bernstein inequality for the Euler derivative.  This is
the precise uniform estimate used after composing a polynomial with the unit
circle parametrization. -/
theorem norm_iterate_eulerDerivative_eval_le_pow_mul_circleSup
    {p : Polynomial ℂ} {n : ℕ} (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ w : ℂ, ‖w‖ = 1 → ‖p.eval w‖ ≤ M)
    (r : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(eulerDerivative^[r] p).eval z‖ ≤ (n : ℝ) ^ r * M := by
  induction r generalizing z with
  | zero => simpa using hM z hz
  | succ r ih =>
      let q := eulerDerivative^[r] p
      have hqdeg : q.natDegree ≤ n :=
        (natDegree_iterate_eulerDerivative_le r p).trans hdeg
      have hqM : ∀ w : ℂ, ‖w‖ = 1 → ‖q.eval w‖ ≤ (n : ℝ) ^ r * M := by
        intro w hw
        exact ih hw
      have hderiv :=
        norm_derivative_eval_le_degree_mul_circleSup hqdeg hqM hz
      rw [Function.iterate_succ_apply']
      calc
        ‖(eulerDerivative q).eval z‖ = ‖q.derivative.eval z‖ := by
          rw [eval_eulerDerivative, norm_mul, hz, one_mul]
        _ ≤ (n : ℝ) * ((n : ℝ) ^ r * M) := hderiv
        _ = (n : ℝ) ^ (r + 1) * M := by rw [pow_succ]; ring

end Bernstein

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/CosineAlgebra.lean` -/

section
/-!
# The four-derivative algebra in the Rudin--Shapiro cosine construction

For fixed complex numbers `A` and `B`, the rapidly oscillating part of the
`k`-th derivative of

`H(x) = exp (I*x) * alpha(x) + exp (2*I*x) * beta(x)`

is `I^k A + (2*I)^k B`.  This file proves the finite-dimensional fact used in
the construction: if `‖A‖^2 + ‖B‖^2 = 1` and the true first four derivatives
are within `1/8` of these leading terms, then one of their real parts has
absolute value at least `1/4`.
-/

namespace CosineAlgebra

/-- The leading two-frequency term in the `k`-th derivative. -/
def leadingDerivative (k : ℕ) (A B : ℂ) : ℂ :=
  Complex.I ^ k * A + ((2 : ℂ) * Complex.I) ^ k * B

/-- The real part of the leading two-frequency derivative. -/
def leadingReal (k : ℕ) (A B : ℂ) : ℝ :=
  (leadingDerivative k A B).re

/-! ## The explicit four rows and their inverse -/

@[simp] theorem leadingReal_zero (A B : ℂ) :
    leadingReal 0 A B = A.re + B.re := by
  simp [leadingReal, leadingDerivative]

@[simp] theorem leadingReal_one (A B : ℂ) :
    leadingReal 1 A B = -A.im - 2 * B.im := by
  simp [leadingReal, leadingDerivative]
  ring

@[simp] theorem leadingReal_two (A B : ℂ) :
    leadingReal 2 A B = -A.re - 4 * B.re := by
  norm_num [leadingReal, leadingDerivative, pow_succ]
  ring

@[simp] theorem leadingReal_three (A B : ℂ) :
    leadingReal 3 A B = A.im + 8 * B.im := by
  norm_num [leadingReal, leadingDerivative, pow_succ]

/-! ## Quantitative inversion -/

/-- If all four rows of the system are bounded by `epsilon`, then the two
complex coordinates have energy at most `(55/9) * epsilon^2`. -/
theorem energy_le_of_leadingReal_le {A B : ℂ} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (h0 : |leadingReal 0 A B| ≤ epsilon)
    (h1 : |leadingReal 1 A B| ≤ epsilon)
    (h2 : |leadingReal 2 A B| ≤ epsilon)
    (h3 : |leadingReal 3 A B| ≤ epsilon) :
    ‖A‖ ^ 2 + ‖B‖ ^ 2 ≤ (55 / 9 : ℝ) * epsilon ^ 2 := by
  have h0' := abs_le.mp h0
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  have h3' := abs_le.mp h3
  have hAre : |A.re| ≤ (5 / 3 : ℝ) * epsilon := by
    rw [abs_le]
    simp only [leadingReal_zero, leadingReal_two] at h0' h2'
    constructor <;> nlinarith
  have hAim : |A.im| ≤ (5 / 3 : ℝ) * epsilon := by
    rw [abs_le]
    simp only [leadingReal_one, leadingReal_three] at h1' h3'
    constructor <;> nlinarith
  have hBre : |B.re| ≤ (2 / 3 : ℝ) * epsilon := by
    rw [abs_le]
    simp only [leadingReal_zero, leadingReal_two] at h0' h2'
    constructor <;> nlinarith
  have hBim : |B.im| ≤ (1 / 3 : ℝ) * epsilon := by
    rw [abs_le]
    simp only [leadingReal_one, leadingReal_three] at h1' h3'
    constructor <;> nlinarith
  have hAreSq : A.re ^ 2 ≤ ((5 / 3 : ℝ) * epsilon) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg A.re) (mul_nonneg (by norm_num) hepsilon)).2 hAre
  have hAimSq : A.im ^ 2 ≤ ((5 / 3 : ℝ) * epsilon) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg A.im) (mul_nonneg (by norm_num) hepsilon)).2 hAim
  have hBreSq : B.re ^ 2 ≤ ((2 / 3 : ℝ) * epsilon) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg B.re) (mul_nonneg (by norm_num) hepsilon)).2 hBre
  have hBimSq : B.im ^ 2 ≤ ((1 / 3 : ℝ) * epsilon) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg B.im) (mul_nonneg (by norm_num) hepsilon)).2 hBim
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  nlinarith

/-- The numerical instance used in the paper: four leading rows bounded by
`3/8` force energy at most `55/64`. -/
theorem energy_le_fiftyFive_div_sixtyFour {A B : ℂ}
    (h : ∀ k : Fin 4, |leadingReal k A B| ≤ 3 / 8) :
    ‖A‖ ^ 2 + ‖B‖ ^ 2 ≤ (55 / 64 : ℝ) := by
  have hbound := energy_le_of_leadingReal_le (A := A) (B := B)
    (epsilon := (3 / 8 : ℝ)) (by norm_num)
    (by simpa using h ⟨0, by omega⟩)
    (by simpa using h ⟨1, by omega⟩)
    (by simpa using h ⟨2, by omega⟩)
    (by simpa using h ⟨3, by omega⟩)
  norm_num at hbound ⊢
  exact hbound

/-! ## Perturbing the leading rows by the slow derivative terms -/

/-- Real version of the no-simultaneous-small-derivatives assertion. -/
theorem exists_large_of_real_error {A B : ℂ} (D : Fin 4 → ℝ)
    (henergy : ‖A‖ ^ 2 + ‖B‖ ^ 2 = 1)
    (herror : ∀ k : Fin 4, |D k - leadingReal k A B| ≤ 1 / 8) :
    ∃ k : Fin 4, 1 / 4 ≤ |D k| := by
  by_contra hlarge
  push_neg at hlarge
  have hleading : ∀ k : Fin 4, |leadingReal k A B| ≤ 3 / 8 := by
    intro k
    calc
      |leadingReal k A B| = |D k - (D k - leadingReal k A B)| := by ring_nf
      _ ≤ |D k| + |D k - leadingReal k A B| := abs_sub _ _
      _ ≤ 3 / 8 := by
        have hk := herror k
        have hk' := hlarge k
        linarith
  have hsmall := energy_le_fiftyFive_div_sixtyFour hleading
  rw [henergy] at hsmall
  norm_num at hsmall

/-- Complex derivative-error version.  Bounding the complex error bounds its
real coordinate, so the same `1/4` conclusion follows. -/
theorem exists_large_re_of_complex_error {A B : ℂ} (D : Fin 4 → ℂ)
    (henergy : ‖A‖ ^ 2 + ‖B‖ ^ 2 = 1)
    (herror : ∀ k : Fin 4, ‖D k - leadingDerivative k A B‖ ≤ 1 / 8) :
    ∃ k : Fin 4, 1 / 4 ≤ |(D k).re| := by
  apply exists_large_of_real_error (fun k ↦ (D k).re) henergy
  intro k
  have hre :
      |(D k - leadingDerivative k A B).re| ≤
        ‖D k - leadingDerivative k A B‖ :=
    Complex.abs_re_le_norm _
  have hid :
      (D k - leadingDerivative k A B).re =
        (D k).re - leadingReal k A B := by
    rfl
  rw [hid] at hre
  exact hre.trans (herror k)

/-- Multiplication by unit phases preserves the normalized Rudin--Shapiro
energy of `alpha` and `beta`. -/
theorem phase_energy {u v alpha beta : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (henergy : ‖alpha‖ ^ 2 + ‖beta‖ ^ 2 = 1) :
    ‖u * alpha‖ ^ 2 + ‖v * beta‖ ^ 2 = 1 := by
  rw [norm_mul, norm_mul, hu, hv, one_mul, one_mul]
  exact henergy

/-- The normalized statement in the form obtained by setting
`A = exp(I*x) * alpha` and `B = exp(2*I*x) * beta`. -/
theorem exists_large_re_of_normalized_modes {u v alpha beta : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (henergy : ‖alpha‖ ^ 2 + ‖beta‖ ^ 2 = 1)
    (D : Fin 4 → ℂ)
    (herror : ∀ k : Fin 4,
      ‖D k - leadingDerivative k (u * alpha) (v * beta)‖ ≤ 1 / 8) :
    ∃ k : Fin 4, 1 / 4 ≤ |(D k).re| :=
  exists_large_re_of_complex_error D (phase_energy hu hv henergy) herror

/-! ## Scaling back to the unnormalized cosine sum -/

end CosineAlgebra

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/Assembly.lean` -/

section
/-!
# Pairing identities and final estimates for Erdős Problem 228

The flat-polynomial construction is first made as a Laurent polynomial with
paired coefficients.  Equal coefficients at `k` and `-k` give a cosine term;
opposite coefficients give a purely imaginary sine term.  This file records
that conversion and the elementary norm estimates used at the end of the
proof.  The lemmas are independent of the particular way in which the signs
are constructed.
-/

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ## Points on the circle and paired Laurent monomials -/

/-- The standard parametrization of the complex unit circle. -/
def unitPoint (theta : ℝ) : ℂ :=
  Complex.exp ((theta : ℂ) * Complex.I)

@[simp]
theorem norm_unitPoint (theta : ℝ) : ‖unitPoint theta‖ = 1 := by
  simp [unitPoint, Complex.norm_exp]

@[simp]
theorem unitPoint_ne_zero (theta : ℝ) : unitPoint theta ≠ 0 := by
  simp [unitPoint]

@[simp]
theorem unitPoint_neg (theta : ℝ) : unitPoint (-theta) = (unitPoint theta)⁻¹ := by
  simp [unitPoint, Complex.exp_neg]

/-- Euler's identity for a natural power of a point on the circle. -/
theorem unitPoint_pow (theta : ℝ) (k : ℕ) :
    unitPoint theta ^ k =
      (Real.cos (k * theta) : ℂ) + (Real.sin (k * theta) : ℂ) * Complex.I := by
  rw [unitPoint, ← Complex.exp_nat_mul]
  have harg : (k : ℂ) * ((theta : ℂ) * Complex.I) =
      (((k : ℝ) * theta : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, ← Complex.cos_add_sin_I]
  simp

/-- The inverse power has the opposite sine component. -/
theorem unitPoint_inv_pow (theta : ℝ) (k : ℕ) :
    (unitPoint theta)⁻¹ ^ k =
      (Real.cos (k * theta) : ℂ) - (Real.sin (k * theta) : ℂ) * Complex.I := by
  rw [← unitPoint_neg, unitPoint_pow]
  simp [Real.cos_neg, Real.sin_neg]
  ring_nf

/-- A symmetric pair of Laurent monomials is twice a cosine. -/
theorem unitPoint_pow_add_inv_pow (theta : ℝ) (k : ℕ) :
    unitPoint theta ^ k + (unitPoint theta)⁻¹ ^ k =
      (2 * Real.cos (k * theta) : ℝ) := by
  rw [unitPoint_pow, unitPoint_inv_pow]
  push_cast
  ring

/-- An antisymmetric pair of Laurent monomials is twice `I` times a sine. -/
theorem unitPoint_pow_sub_inv_pow (theta : ℝ) (k : ℕ) :
    unitPoint theta ^ k - (unitPoint theta)⁻¹ ^ k =
      (2 * Real.sin (k * theta) : ℝ) * Complex.I := by
  rw [unitPoint_pow, unitPoint_inv_pow]
  push_cast
  ring

/-! ## Finite paired sums -/

/-- The real cosine sum belonging to a finite set of symmetric pairs. -/
def cosineSum (s : Finset ℕ) (eps : ℕ → ℝ) (theta : ℝ) : ℝ :=
  ∑ k ∈ s, eps k * Real.cos (k * theta)

/-- The real sine sum belonging to a finite set of antisymmetric pairs. -/
def sineSum (s : Finset ℕ) (eps : ℕ → ℝ) (theta : ℝ) : ℝ :=
  ∑ k ∈ s, eps k * Real.sin (k * theta)

/-- A centered Laurent value, split into one symmetric and two antisymmetric
parts.  The two sine parts correspond to the even and odd pieces in the
Balister--Bollobás--Morris--Sahasrabudhe--Tiba construction. -/
def pairedLaurentValue (C Se So : Finset ℕ)
    (epsC epsE epsO : ℕ → ℝ) (theta : ℝ) : ℂ :=
  1 +
    ∑ k ∈ C, (epsC k : ℂ) *
      (unitPoint theta ^ k + (unitPoint theta)⁻¹ ^ k) +
    ∑ k ∈ Se, (epsE k : ℂ) *
      (unitPoint theta ^ k - (unitPoint theta)⁻¹ ^ k) +
    ∑ k ∈ So, (epsO k : ℂ) *
      (unitPoint theta ^ k - (unitPoint theta)⁻¹ ^ k)

/-- The real/imaginary normal form used in the final estimates. -/
def assembledValue (c se so : ℝ) : ℂ :=
  ((1 + 2 * c : ℝ) : ℂ) + ((2 * (se + so) : ℝ) : ℂ) * Complex.I

@[simp]
theorem assembledValue_re (c se so : ℝ) :
    (assembledValue c se so).re = 1 + 2 * c := by
  simp [assembledValue]

@[simp]
theorem assembledValue_im (c se so : ℝ) :
    (assembledValue c se so).im = 2 * (se + so) := by
  simp [assembledValue]

/-- Pairing the Laurent coefficients gives exactly one real cosine component
and the sum of the two real sine components in the imaginary coordinate. -/
theorem pairedLaurentValue_eq_assembledValue (C Se So : Finset ℕ)
    (epsC epsE epsO : ℕ → ℝ) (theta : ℝ) :
    pairedLaurentValue C Se So epsC epsE epsO theta =
      assembledValue (cosineSum C epsC theta)
        (sineSum Se epsE theta) (sineSum So epsO theta) := by
  classical
  have hC :
      (∑ k ∈ C, (epsC k : ℂ) *
        (unitPoint theta ^ k + (unitPoint theta)⁻¹ ^ k)) =
        ((2 * cosineSum C epsC theta : ℝ) : ℂ) := by
    rw [cosineSum]
    push_cast
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [unitPoint_pow_add_inv_pow]
    push_cast
    ring
  have hE :
      (∑ k ∈ Se, (epsE k : ℂ) *
        (unitPoint theta ^ k - (unitPoint theta)⁻¹ ^ k)) =
        ((2 * sineSum Se epsE theta : ℝ) : ℂ) * Complex.I := by
    rw [sineSum]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [unitPoint_pow_sub_inv_pow]
    push_cast
    ring
  have hO :
      (∑ k ∈ So, (epsO k : ℂ) *
        (unitPoint theta ^ k - (unitPoint theta)⁻¹ ^ k)) =
        ((2 * sineSum So epsO theta : ℝ) : ℂ) * Complex.I := by
    rw [sineSum]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [unitPoint_pow_sub_inv_pow]
    push_cast
    ring
  rw [pairedLaurentValue, hC, hE, hO]
  simp only [assembledValue]
  push_cast
  ring

/-! ## Final lower and upper estimates -/

/-- The cosine coordinate alone gives the lower bound `2 |c| - 1`. -/
theorem two_mul_abs_sub_one_le_norm_assembledValue (c se so : ℝ) :
    2 * |c| - 1 ≤ ‖assembledValue c se so‖ := by
  have htriangle : |2 * c| ≤ |1 + 2 * c| + 1 := by
    calc
      |2 * c| = |(1 + 2 * c) - 1| := by ring_nf
      _ ≤ |1 + 2 * c| + |(1 : ℝ)| := abs_sub _ _
      _ = |1 + 2 * c| + 1 := by norm_num
  have hre : |1 + 2 * c| ≤ ‖assembledValue c se so‖ := by
    simpa using Complex.abs_re_le_norm (assembledValue c se so)
  rw [abs_mul] at htriangle
  norm_num at htriangle
  linarith

/-- The imaginary coordinate gives a lower bound after subtracting the size
of the already chosen even-sine part from the odd-sine part. -/
theorem two_mul_abs_sub_abs_le_norm_assembledValue (c se so : ℝ) :
    2 * (|so| - |se|) ≤ ‖assembledValue c se so‖ := by
  have htriangle : |so| ≤ |se + so| + |se| := by
    calc
      |so| = |(se + so) - se| := by ring_nf
      _ ≤ |se + so| + |se| := abs_sub _ _
  have him : |2 * (se + so)| ≤ ‖assembledValue c se so‖ := by
    simpa using Complex.abs_im_le_norm (assembledValue c se so)
  rw [abs_mul] at him
  norm_num at him
  linarith

/-- A convenient hypothesis form of the sine-coordinate lower bound. -/
theorem le_norm_assembledValue_of_sine_gap {a c se so : ℝ}
    (hgap : a / 2 + |se| ≤ |so|) :
    a ≤ ‖assembledValue c se so‖ := by
  have h := two_mul_abs_sub_abs_le_norm_assembledValue c se so
  linarith

/-- A linear upper bound obtained from the two coordinates.  This is looser
than the exact Pythagorean estimate but has especially convenient hypotheses. -/
theorem norm_assembledValue_le (c se so A B D : ℝ)
    (hA : |c| ≤ A) (hB : |se| ≤ B) (hD : |so| ≤ D) :
    ‖assembledValue c se so‖ ≤ 1 + 2 * (A + B + D) := by
  calc
    ‖assembledValue c se so‖ ≤ |1 + 2 * c| + |2 * (se + so)| := by
      simpa [assembledValue] using
        Complex.norm_le_abs_re_add_abs_im (assembledValue c se so)
    _ ≤ (1 + 2 * |c|) + 2 * (|se| + |so|) := by
      calc
        |1 + 2 * c| + |2 * (se + so)| ≤
            (|1| + |2 * c|) + |2| * (|se| + |so|) := by
              gcongr
              · exact abs_add_le _ _
              · rw [abs_mul]
                gcongr
                exact abs_add_le _ _
        _ = (1 + 2 * |c|) + 2 * (|se| + |so|) := by norm_num
    _ ≤ 1 + 2 * (A + B + D) := by linarith

/-- The numerical upper-bound calculation used in the published construction:
`|c| ≤ sqrt n`, `|se| ≤ 6 sqrt n`, and `|so| ≤ 2^10 sqrt n` are more
than enough for the advertised `2^12 sqrt n` bound. -/
theorem norm_assembledValue_le_two_pow_twelve_sqrt {n : ℕ} {c se so : ℝ}
    (hn : 1 ≤ n)
    (hc : |c| ≤ Real.sqrt n)
    (hse : |se| ≤ 6 * Real.sqrt n)
    (hso : |so| ≤ 2 ^ 10 * Real.sqrt n) :
    ‖assembledValue c se so‖ ≤ 2 ^ 12 * Real.sqrt n := by
  have hsqrt : 1 ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  have h := norm_assembledValue_le c se so
    (Real.sqrt n) (6 * Real.sqrt n) (2 ^ 10 * Real.sqrt n) hc hse hso
  norm_num at h ⊢
  nlinarith

/-- On a dangerous interval, an odd-sine value larger than `10 sqrt n`
dominates an even-sine error bounded by `6 sqrt n`. -/
theorem eight_sqrt_le_norm_assembledValue_of_odd_sine {n : ℕ} {c se so : ℝ}
    (hse : |se| ≤ 6 * Real.sqrt n)
    (hso : 10 * Real.sqrt n ≤ |so|) :
    8 * Real.sqrt n ≤ ‖assembledValue c se so‖ := by
  apply le_norm_assembledValue_of_sine_gap
  linarith

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/RudinShapiro.lean` -/

section
/-!
# Rudin--Shapiro polynomials

This file develops the finite Rudin--Shapiro recursion used in the proof of
Erdős Problem 228.  The normalization is

`P 0 = Q 0 = 1`,
`P (t+1) = P t + X^(2^t) Q t`, and
`Q (t+1) = P t - X^(2^t) Q t`.
-/

open scoped ComplexConjugate

noncomputable section

mutual
  /-- The first Rudin--Shapiro polynomial. -/
  def rudinShapiroP : ℕ → Polynomial ℂ
    | 0 => 1
    | t + 1 => rudinShapiroP t + Polynomial.X ^ (2 ^ t) * rudinShapiroQ t

  /-- The companion Rudin--Shapiro polynomial. -/
  def rudinShapiroQ : ℕ → Polynomial ℂ
    | 0 => 1
    | t + 1 => rudinShapiroP t - Polynomial.X ^ (2 ^ t) * rudinShapiroQ t
end

@[simp] theorem rudinShapiroP_zero : rudinShapiroP 0 = 1 := rfl
@[simp] theorem rudinShapiroQ_zero : rudinShapiroQ 0 = 1 := rfl

@[simp] theorem rudinShapiroP_succ (t : ℕ) :
    rudinShapiroP (t + 1) =
      rudinShapiroP t + Polynomial.X ^ (2 ^ t) * rudinShapiroQ t := rfl

@[simp] theorem rudinShapiroQ_succ (t : ℕ) :
    rudinShapiroQ (t + 1) =
      rudinShapiroP t - Polynomial.X ^ (2 ^ t) * rudinShapiroQ t := rfl

@[simp] theorem eval_rudinShapiroP_succ (t : ℕ) (z : ℂ) :
    (rudinShapiroP (t + 1)).eval z =
      (rudinShapiroP t).eval z + z ^ (2 ^ t) * (rudinShapiroQ t).eval z := by
  simp [rudinShapiroP_succ]

@[simp] theorem eval_rudinShapiroQ_succ (t : ℕ) (z : ℂ) :
    (rudinShapiroQ (t + 1)).eval z =
      (rudinShapiroP t).eval z - z ^ (2 ^ t) * (rudinShapiroQ t).eval z := by
  simp [rudinShapiroQ_succ]

/-- The parallelogram identity in the form needed by the recursion. -/
lemma normSq_add_mul_add_normSq_sub_mul (a b u : ℂ) :
    Complex.normSq (a + u * b) + Complex.normSq (a - u * b) =
      2 * (Complex.normSq a + Complex.normSq u * Complex.normSq b) := by
  rw [Complex.normSq_add, Complex.normSq_sub, Complex.normSq_mul]
  ring

/-- Rudin--Shapiro's exact energy identity on the unit circle. -/
theorem rudinShapiro_energy (t : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(rudinShapiroP t).eval z‖ ^ 2 + ‖(rudinShapiroQ t).eval z‖ ^ 2 =
      (2 ^ (t + 1) : ℝ) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      rw [eval_rudinShapiroP_succ, eval_rudinShapiroQ_succ,
        ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        normSq_add_mul_add_normSq_sub_mul]
      have hzu : Complex.normSq (z ^ (2 ^ t)) = 1 := by
        simp [Complex.normSq_eq_norm_sq, norm_pow, hz]
      rw [hzu, one_mul, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, ih]
      rw [show (2 ^ (t + 1 + 1) : ℝ) = 2 ^ (t + 1) * 2 by
        rw [pow_succ]]
      ring

/-- Each of the two Rudin--Shapiro evaluations is at most `sqrt (2^(t+1))`. -/
theorem norm_eval_rudinShapiroP_le (t : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(rudinShapiroP t).eval z‖ ≤ Real.sqrt (2 ^ (t + 1) : ℝ) := by
  have h := rudinShapiro_energy t hz
  have hsq : ‖(rudinShapiroP t).eval z‖ ^ 2 ≤ (2 ^ (t + 1) : ℝ) := by
    nlinarith [sq_nonneg ‖(rudinShapiroQ t).eval z‖]
  nlinarith [Real.sq_sqrt (show 0 ≤ (2 ^ (t + 1) : ℝ) by positivity),
    Real.sqrt_nonneg (2 ^ (t + 1) : ℝ)]

/-- The same pointwise bound for the companion polynomial. -/
theorem norm_eval_rudinShapiroQ_le (t : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(rudinShapiroQ t).eval z‖ ≤ Real.sqrt (2 ^ (t + 1) : ℝ) := by
  have h := rudinShapiro_energy t hz
  have hsq : ‖(rudinShapiroQ t).eval z‖ ^ 2 ≤ (2 ^ (t + 1) : ℝ) := by
    nlinarith [sq_nonneg ‖(rudinShapiroP t).eval z‖]
  nlinarith [Real.sq_sqrt (show 0 ≤ (2 ^ (t + 1) : ℝ) by positivity),
    Real.sqrt_nonneg (2 ^ (t + 1) : ℝ)]

/-- The coefficient and support assertions maintained by the recursion. -/
structure RudinShapiroCoeffFacts (t : ℕ) : Prop where
  p_sign : ∀ k < 2 ^ t, (rudinShapiroP t).coeff k = 1 ∨
    (rudinShapiroP t).coeff k = -1
  q_sign : ∀ k < 2 ^ t, (rudinShapiroQ t).coeff k = 1 ∨
    (rudinShapiroQ t).coeff k = -1
  p_zero : ∀ k, 2 ^ t ≤ k → (rudinShapiroP t).coeff k = 0
  q_zero : ∀ k, 2 ^ t ≤ k → (rudinShapiroQ t).coeff k = 0

/-- Both polynomials have sign coefficients precisely on the first `2^t`
positions and vanish after that block. -/
theorem rudinShapiro_coeffFacts (t : ℕ) : RudinShapiroCoeffFacts t := by
  induction t with
  | zero =>
      constructor
      · intro k hk
        have : k = 0 := by omega
        subst k
        simp
      · intro k hk
        have : k = 0 := by omega
        subst k
        simp
      · intro k hk
        have : k ≠ 0 := by omega
        simp [Polynomial.coeff_one, this]
      · intro k hk
        have : k ≠ 0 := by omega
        simp [Polynomial.coeff_one, this]
  | succ t ih =>
      have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by
        simp [pow_succ, mul_two]
      constructor
      · intro k hk
        rw [rudinShapiroP_succ, Polynomial.coeff_add,
          Polynomial.coeff_X_pow_mul']
        by_cases hlow : k < 2 ^ t
        · rw [if_neg (Nat.not_le.mpr hlow), add_zero]
          exact ih.p_sign k hlow
        · have hle : 2 ^ t ≤ k := Nat.le_of_not_gt hlow
          rw [if_pos hle, ih.p_zero k hle, zero_add]
          have hrest : k - 2 ^ t < 2 ^ t := by omega
          exact ih.q_sign (k - 2 ^ t) hrest
      · intro k hk
        rw [rudinShapiroQ_succ, Polynomial.coeff_sub,
          Polynomial.coeff_X_pow_mul']
        by_cases hlow : k < 2 ^ t
        · rw [if_neg (Nat.not_le.mpr hlow), sub_zero]
          exact ih.p_sign k hlow
        · have hle : 2 ^ t ≤ k := Nat.le_of_not_gt hlow
          rw [if_pos hle, ih.p_zero k hle, zero_sub]
          have hrest : k - 2 ^ t < 2 ^ t := by omega
          rcases ih.q_sign (k - 2 ^ t) hrest with h | h
          · right
            rw [h]
          · left
            rw [h]
            simp
      · intro k hk
        rw [rudinShapiroP_succ, Polynomial.coeff_add,
          Polynomial.coeff_X_pow_mul']
        have hle : 2 ^ t ≤ k := by omega
        rw [if_pos hle, ih.p_zero k hle, zero_add]
        apply ih.q_zero
        omega
      · intro k hk
        rw [rudinShapiroQ_succ, Polynomial.coeff_sub,
          Polynomial.coeff_X_pow_mul']
        have hle : 2 ^ t ≤ k := by omega
        rw [if_pos hle, ih.p_zero k hle, zero_sub]
        rw [ih.q_zero]
        · simp
        · omega

theorem coeff_rudinShapiroP_eq_one_or_neg_one {t k : ℕ} (hk : k < 2 ^ t) :
    (rudinShapiroP t).coeff k = 1 ∨ (rudinShapiroP t).coeff k = -1 :=
  (rudinShapiro_coeffFacts t).p_sign k hk

theorem coeff_rudinShapiroQ_eq_one_or_neg_one {t k : ℕ} (hk : k < 2 ^ t) :
    (rudinShapiroQ t).coeff k = 1 ∨ (rudinShapiroQ t).coeff k = -1 :=
  (rudinShapiro_coeffFacts t).q_sign k hk

theorem coeff_rudinShapiroP_eq_zero {t k : ℕ} (hk : 2 ^ t ≤ k) :
    (rudinShapiroP t).coeff k = 0 :=
  (rudinShapiro_coeffFacts t).p_zero k hk

theorem coeff_rudinShapiroQ_eq_zero {t k : ℕ} (hk : 2 ^ t ≤ k) :
    (rudinShapiroQ t).coeff k = 0 :=
  (rudinShapiro_coeffFacts t).q_zero k hk

theorem natDegree_rudinShapiroP (t : ℕ) :
    (rudinShapiroP t).natDegree = 2 ^ t - 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    apply coeff_rudinShapiroP_eq_zero
    have hpos : 0 < 2 ^ t := by positivity
    omega
  · have hpos : 0 < 2 ^ t := by positivity
    have hlt : 2 ^ t - 1 < 2 ^ t := by omega
    rcases coeff_rudinShapiroP_eq_one_or_neg_one hlt with h | h <;> simp [h]

theorem natDegree_rudinShapiroQ (t : ℕ) :
    (rudinShapiroQ t).natDegree = 2 ^ t - 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    apply coeff_rudinShapiroQ_eq_zero
    have hpos : 0 < 2 ^ t := by positivity
    omega
  · have hpos : 0 < 2 ^ t := by positivity
    have hlt : 2 ^ t - 1 < 2 ^ t := by omega
    rcases coeff_rudinShapiroQ_eq_one_or_neg_one hlt with h | h <;> simp [h]

/-- Keep only the coefficients in positions strictly below `m`. -/
def polynomialPrefix (p : Polynomial ℂ) (m : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range m, Polynomial.C (p.coeff k) * Polynomial.X ^ k

@[simp] theorem polynomialPrefix_zero (p : Polynomial ℂ) : polynomialPrefix p 0 = 0 := by
  simp [polynomialPrefix]

theorem coeff_polynomialPrefix (p : Polynomial ℂ) (m k : ℕ) :
    (polynomialPrefix p m).coeff k = if k < m then p.coeff k else 0 := by
  simp [polynomialPrefix, Polynomial.coeff_C_mul]

theorem coeff_rudinShapiroP_succ_of_lt {t k : ℕ} (hk : k < 2 ^ t) :
    (rudinShapiroP (t + 1)).coeff k = (rudinShapiroP t).coeff k := by
  rw [rudinShapiroP_succ, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    if_neg (Nat.not_le.mpr hk), add_zero]

theorem coeff_rudinShapiroQ_succ_of_lt {t k : ℕ} (hk : k < 2 ^ t) :
    (rudinShapiroQ (t + 1)).coeff k = (rudinShapiroP t).coeff k := by
  rw [rudinShapiroQ_succ, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul',
    if_neg (Nat.not_le.mpr hk), sub_zero]

@[simp] theorem coeff_rudinShapiroP_succ_add (t k : ℕ) :
    (rudinShapiroP (t + 1)).coeff (2 ^ t + k) = (rudinShapiroQ t).coeff k := by
  rw [rudinShapiroP_succ, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    if_pos (Nat.le_add_right _ _), coeff_rudinShapiroP_eq_zero]
  · simp
  · exact Nat.le_add_right _ _

@[simp] theorem coeff_rudinShapiroQ_succ_add (t k : ℕ) :
    (rudinShapiroQ (t + 1)).coeff (2 ^ t + k) = -(rudinShapiroQ t).coeff k := by
  rw [rudinShapiroQ_succ, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul',
    if_pos (Nat.le_add_right _ _), coeff_rudinShapiroP_eq_zero]
  · simp
  · exact Nat.le_add_right _ _

theorem polynomialPrefix_rudinShapiroP_succ_of_le {t m : ℕ} (hm : m ≤ 2 ^ t) :
    polynomialPrefix (rudinShapiroP (t + 1)) m =
      polynomialPrefix (rudinShapiroP t) m := by
  ext k
  rw [coeff_polynomialPrefix, coeff_polynomialPrefix]
  split_ifs with hk
  · exact coeff_rudinShapiroP_succ_of_lt (lt_of_lt_of_le hk hm)
  · rfl

theorem polynomialPrefix_rudinShapiroQ_succ_of_le {t m : ℕ} (hm : m ≤ 2 ^ t) :
    polynomialPrefix (rudinShapiroQ (t + 1)) m =
      polynomialPrefix (rudinShapiroP t) m := by
  ext k
  rw [coeff_polynomialPrefix, coeff_polynomialPrefix]
  split_ifs with hk
  · exact coeff_rudinShapiroQ_succ_of_lt (lt_of_lt_of_le hk hm)
  · rfl

theorem polynomialPrefix_rudinShapiroP_succ_add (t r : ℕ) :
    polynomialPrefix (rudinShapiroP (t + 1)) (2 ^ t + r) =
      rudinShapiroP t + Polynomial.X ^ (2 ^ t) * polynomialPrefix (rudinShapiroQ t) r := by
  ext k
  rw [coeff_polynomialPrefix, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    coeff_polynomialPrefix]
  by_cases hlow : k < 2 ^ t
  · have htotal : k < 2 ^ t + r := lt_of_lt_of_le hlow (Nat.le_add_right _ _)
    rw [if_pos htotal, if_neg (Nat.not_le.mpr hlow), add_zero]
    exact coeff_rudinShapiroP_succ_of_lt hlow
  · have hle : 2 ^ t ≤ k := Nat.le_of_not_gt hlow
    rw [if_pos hle, coeff_rudinShapiroP_eq_zero hle, zero_add]
    by_cases htotal : k < 2 ^ t + r
    · have hrest : k - 2 ^ t < r := by omega
      rw [if_pos htotal, if_pos hrest]
      rw [← Nat.add_sub_of_le hle, coeff_rudinShapiroP_succ_add]
      simp
    · have hrest : ¬ k - 2 ^ t < r := by omega
      rw [if_neg htotal, if_neg hrest]

theorem polynomialPrefix_rudinShapiroQ_succ_add (t r : ℕ) :
    polynomialPrefix (rudinShapiroQ (t + 1)) (2 ^ t + r) =
      rudinShapiroP t - Polynomial.X ^ (2 ^ t) * polynomialPrefix (rudinShapiroQ t) r := by
  ext k
  rw [coeff_polynomialPrefix, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul',
    coeff_polynomialPrefix]
  by_cases hlow : k < 2 ^ t
  · have htotal : k < 2 ^ t + r := lt_of_lt_of_le hlow (Nat.le_add_right _ _)
    rw [if_pos htotal, if_neg (Nat.not_le.mpr hlow), sub_zero]
    exact coeff_rudinShapiroQ_succ_of_lt hlow
  · have hle : 2 ^ t ≤ k := Nat.le_of_not_gt hlow
    rw [if_pos hle, coeff_rudinShapiroP_eq_zero hle, zero_sub]
    by_cases htotal : k < 2 ^ t + r
    · have hrest : k - 2 ^ t < r := by omega
      rw [if_pos htotal, if_pos hrest]
      rw [← Nat.add_sub_of_le hle, coeff_rudinShapiroQ_succ_add]
      simp
    · have hrest : ¬ k - 2 ^ t < r := by omega
      rw [if_neg htotal, if_neg hrest, neg_zero]

private lemma sqrt_two_mul_add_five_sqrt_le_five_sqrt_add
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ x) :
    Real.sqrt (2 * x) + 5 * Real.sqrt y ≤ 5 * Real.sqrt (x + y) := by
  have h2x : 0 ≤ 2 * x := by positivity
  have hxy : 0 ≤ x + y := by positivity
  have hs2x := Real.sq_sqrt h2x
  have hsy := Real.sq_sqrt hy
  have hsxy := Real.sq_sqrt hxy
  have hn2x := Real.sqrt_nonneg (2 * x)
  have hny := Real.sqrt_nonneg y
  have hnxy := Real.sqrt_nonneg (x + y)
  nlinarith [sq_nonneg (Real.sqrt (2 * x) - Real.sqrt y),
    sq_nonneg (Real.sqrt (2 * x) + 5 * Real.sqrt y - 5 * Real.sqrt (x + y))]

/-- Uniform prefix estimate.  This is the finite form of the standard
Rudin--Shapiro prefix bound used by BBMST; the constant `5` is deliberately
loose and is stable under the dyadic recursion. -/
theorem norm_eval_polynomialPrefix_rudinShapiro (t m : ℕ) {z : ℂ}
    (hm : m ≤ 2 ^ t) (hz : ‖z‖ = 1) :
    ‖(polynomialPrefix (rudinShapiroP t) m).eval z‖ ≤ 5 * Real.sqrt m ∧
      ‖(polynomialPrefix (rudinShapiroQ t) m).eval z‖ ≤ 5 * Real.sqrt m := by
  induction t generalizing m with
  | zero =>
      have hm' : m ≤ 1 := by simpa using hm
      interval_cases m <;> norm_num [polynomialPrefix, rudinShapiroP, rudinShapiroQ]
  | succ t ih =>
      have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by simp [pow_succ, mul_two]
      by_cases hlow : m ≤ 2 ^ t
      · rw [polynomialPrefix_rudinShapiroP_succ_of_le hlow,
          polynomialPrefix_rudinShapiroQ_succ_of_le hlow]
        exact ⟨(ih m hlow).1, (ih m hlow).1⟩
      · have hAm : 2 ^ t ≤ m := by omega
        let r := m - 2 ^ t
        have hm_eq : 2 ^ t + r = m := by
          dsimp [r]
          omega
        have hr : r ≤ 2 ^ t := by omega
        have hir := ih r hr
        have hfull := norm_eval_rudinShapiroP_le t hz
        have hcastpow : (2 ^ (t + 1) : ℝ) = 2 * (2 ^ t : ℝ) := by
          rw [pow_succ]
          ring
        have hsqrt : Real.sqrt (2 ^ (t + 1) : ℝ) =
            Real.sqrt (2 * (2 ^ t : ℝ)) := congrArg Real.sqrt hcastpow
        have hsqrt_bound : Real.sqrt (2 * (2 ^ t : ℝ)) + 5 * Real.sqrt (r : ℝ) ≤
            5 * Real.sqrt ((2 ^ t : ℝ) + r) := by
          apply sqrt_two_mul_add_five_sqrt_le_five_sqrt_add
          · positivity
          · positivity
          · exact_mod_cast hr
        constructor
        · rw [← hm_eq, polynomialPrefix_rudinShapiroP_succ_add,
            Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
          calc
            ‖(rudinShapiroP t).eval z + z ^ 2 ^ t *
                (polynomialPrefix (rudinShapiroQ t) r).eval z‖
                ≤ ‖(rudinShapiroP t).eval z‖ +
                    ‖z ^ 2 ^ t * (polynomialPrefix (rudinShapiroQ t) r).eval z‖ :=
              norm_add_le _ _
            _ = ‖(rudinShapiroP t).eval z‖ +
                ‖(polynomialPrefix (rudinShapiroQ t) r).eval z‖ := by
              rw [norm_mul, norm_pow, hz, one_pow, one_mul]
            _ ≤ Real.sqrt (2 * (2 ^ t : ℝ)) + 5 * Real.sqrt (r : ℝ) := by
              rw [← hsqrt]
              exact add_le_add hfull hir.2
            _ ≤ 5 * Real.sqrt ((2 ^ t : ℝ) + r) := hsqrt_bound
            _ = 5 * Real.sqrt ((2 ^ t + r : ℕ) : ℝ) := by norm_num
        · rw [← hm_eq, polynomialPrefix_rudinShapiroQ_succ_add,
            Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
          calc
            ‖(rudinShapiroP t).eval z - z ^ 2 ^ t *
                (polynomialPrefix (rudinShapiroQ t) r).eval z‖
                ≤ ‖(rudinShapiroP t).eval z‖ +
                    ‖z ^ 2 ^ t * (polynomialPrefix (rudinShapiroQ t) r).eval z‖ :=
              norm_sub_le _ _
            _ = ‖(rudinShapiroP t).eval z‖ +
                ‖(polynomialPrefix (rudinShapiroQ t) r).eval z‖ := by
              rw [norm_mul, norm_pow, hz, one_pow, one_mul]
            _ ≤ Real.sqrt (2 * (2 ^ t : ℝ)) + 5 * Real.sqrt (r : ℝ) := by
              rw [← hsqrt]
              exact add_le_add hfull hir.2
            _ ≤ 5 * Real.sqrt ((2 ^ t : ℝ) + r) := hsqrt_bound
            _ = 5 * Real.sqrt ((2 ^ t + r : ℕ) : ℝ) := by norm_num

theorem norm_eval_polynomialPrefix_rudinShapiroP_le (t m : ℕ) {z : ℂ}
    (hm : m ≤ 2 ^ t) (hz : ‖z‖ = 1) :
    ‖(polynomialPrefix (rudinShapiroP t) m).eval z‖ ≤ 5 * Real.sqrt m :=
  (norm_eval_polynomialPrefix_rudinShapiro t m hm hz).1

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/EvenConstruction.lean` -/

section
/-!
# The even-frequency part of the BBMST construction

This file formalizes equations (3), (6), and (7), and Lemma 3.3, of
Balister--Bollobás--Morris--Sahasrabudhe--Tiba.  Frequencies are first described
in the auxiliary variable `w = exp (2 i theta)`.  Doubling their supports gives
the even frequencies of the final centered Laurent polynomial.
-/

open scoped BigOperators ComplexConjugate

noncomputable section

/-- The large frequency shift `T = 2^(t+10)` used by BBMST. -/
def evenT (t : ℕ) : ℕ := 2 ^ (t + 10)

/-- The integer on the right side of BBMST equation (3). -/
def evenGammaNumerator (t : ℕ) : ℕ :=
  2 ^ (t + 11) + 2 ^ t - 1

/-- The arithmetic data chosen in Section 2.2 of BBMST.  Oddness is used by
the later dangerous-interval argument, while this file only needs the upper
bound on `gamma` and the exact parameter equation. -/
structure EvenParameters (n t : ℕ) (gamma : ℝ) : Prop where
  t_odd : Odd t
  gamma_pos : 0 < gamma
  gamma_le : gamma ≤ 1 / 2 ^ 40
  equation : gamma * n = evenGammaNumerator t

/-- The two blocks of frequencies before the substitution `w = exp(2 i theta)`. -/
def evenCPrime (t : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ t)).image (fun j => evenT t + j) ∪
    (Finset.range (2 ^ t)).image (fun j => 2 * evenT t + j)

/-- The cosine frequencies in the original angular variable. -/
def evenC (t : ℕ) : Finset ℕ :=
  (evenCPrime t).image (fun j => 2 * j)

/-- The even frequencies not reserved for the cosine polynomial. -/
def evenSPrime (n t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n) \ evenCPrime t

/-- The remaining even frequencies in the original angular variable. -/
def evenS (n t : ℕ) : Finset ℕ :=
  (evenSPrime n t).image (fun j => 2 * j)

/-- The polynomial whose real part supplies the cosine coordinate. -/
def cosineBlockPolynomial (t : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ evenT t * rudinShapiroP t +
    Polynomial.X ^ (2 * evenT t) * rudinShapiroQ t

/-- The two blocks deleted from the stable Rudin--Shapiro prefix when defining
the remaining even sine coordinate.  Both blocks use `P_t`; this is the
asymmetry between equations (6) and (7) in BBMST. -/
def deletedEvenBlockPolynomial (t : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ evenT t * rudinShapiroP t +
    Polynomial.X ^ (2 * evenT t) * rudinShapiroP t

/-- The stable prefix after deleting the two blocks assigned to `c`. -/
def evenRemainderPolynomial (n t u : ℕ) : Polynomial ℂ :=
  polynomialPrefix (rudinShapiroP u) (n + 1) - deletedEvenBlockPolynomial t

/-- BBMST's cosine polynomial `c(theta)`. -/
def evenCosine (t : ℕ) (theta : ℝ) : ℝ :=
  (cosineBlockPolynomial t).eval (unitPoint (2 * theta)) |>.re

/-- BBMST's remaining even sine polynomial `s_e(theta)`.  The level `u` is
any Rudin--Shapiro recursion level whose first `n+1` coefficients have
stabilized and which contains the two deleted blocks. -/
def evenSine (n t u : ℕ) (theta : ℝ) : ℝ :=
  (evenRemainderPolynomial n t u).eval (unitPoint (2 * theta)) |>.im

lemma evenT_eq_pow_mul (t : ℕ) : evenT t = 2 ^ t * 2 ^ 10 := by
  simp [evenT, pow_add]

lemma two_mul_evenT (t : ℕ) : 2 * evenT t = 2 ^ (t + 11) := by
  simp [evenT, pow_succ']

lemma evenT_add_pow_le_two_mul_evenT (t : ℕ) :
    evenT t + 2 ^ t ≤ 2 * evenT t := by
  rw [evenT_eq_pow_mul]
  have hpos : 0 < 2 ^ t := by positivity
  nlinarith [show (2 ^ 10 : ℕ) = 1024 by norm_num]

lemma pow_le_evenT (t : ℕ) : 2 ^ t ≤ evenT t := by
  rw [evenT_eq_pow_mul]
  have hpos : 0 < 2 ^ t := by positivity
  nlinarith [show (2 ^ 10 : ℕ) = 1024 by norm_num]

lemma evenGammaNumerator_add_one (t : ℕ) :
    evenGammaNumerator t + 1 = 2 * evenT t + 2 ^ t := by
  have hp : 0 < 2 ^ (t + 11) := by positivity
  have hone : 1 ≤ 2 ^ (t + 11) := hp
  have hsum : 1 ≤ 2 ^ (t + 11) + 2 ^ t :=
    hone.trans (Nat.le_add_right _ _)
  rw [evenGammaNumerator, Nat.sub_add_cancel hsum, two_mul_evenT]

lemma EvenParameters.gamma_le_one {n t : ℕ} {gamma : ℝ}
    (h : EvenParameters n t gamma) : gamma ≤ 1 := by
  calc
    gamma ≤ 1 / (2 : ℝ) ^ 40 := h.gamma_le
    _ ≤ 1 := by norm_num

lemma EvenParameters.numerator_le_n {n t : ℕ} {gamma : ℝ}
    (h : EvenParameters n t gamma) : evenGammaNumerator t ≤ n := by
  have hnonneg : 0 ≤ (n : ℝ) := by positivity
  have hreal : (evenGammaNumerator t : ℝ) ≤ n := by
    rw [← h.equation]
    nlinarith [h.gamma_le_one]
  exact_mod_cast hreal

lemma EvenParameters.pow_t_add_eleven_le_n {n t : ℕ} {gamma : ℝ}
    (h : EvenParameters n t gamma) : 2 ^ (t + 11) ≤ n := by
  apply le_trans _ h.numerator_le_n
  rw [evenGammaNumerator]
  have hpos : 0 < 2 ^ t := by positivity
  omega

lemma EvenParameters.five_le_n {n t : ℕ} {gamma : ℝ}
    (h : EvenParameters n t gamma) : 5 ≤ n := by
  have hp := h.pow_t_add_eleven_le_n
  have hbase : 2 ^ 11 ≤ 2 ^ (t + 11) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at hbase
  omega

lemma EvenParameters.pow_t_add_five_le_n {n t : ℕ} {gamma : ℝ}
    (h : EvenParameters n t gamma) : 2 ^ (t + 5) ≤ n := by
  exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans h.pow_t_add_eleven_le_n

lemma EvenParameters.blocks_fit {n t : ℕ} {gamma : ℝ}
    (h : EvenParameters n t gamma) :
    2 * evenT t + 2 ^ t ≤ n + 1 := by
  rw [← evenGammaNumerator_add_one]
  exact Nat.add_le_add_right h.numerator_le_n 1

@[simp] lemma mem_evenCPrime (t k : ℕ) :
    k ∈ evenCPrime t ↔
      (∃ j < 2 ^ t, k = evenT t + j) ∨
      ∃ j < 2 ^ t, k = 2 * evenT t + j := by
  simp [evenCPrime, eq_comm]

@[simp] lemma mem_evenC (t k : ℕ) :
    k ∈ evenC t ↔ ∃ j ∈ evenCPrime t, k = 2 * j := by
  simp [evenC, eq_comm]

@[simp] lemma mem_evenSPrime (n t k : ℕ) :
    k ∈ evenSPrime n t ↔ 1 ≤ k ∧ k ≤ n ∧ k ∉ evenCPrime t := by
  simp [evenSPrime, and_assoc]

@[simp] lemma mem_evenS (n t k : ℕ) :
    k ∈ evenS n t ↔ ∃ j ∈ evenSPrime n t, k = 2 * j := by
  simp [evenS, eq_comm]

lemma evenCPrime_subset_range {n t : ℕ}
    (hblock : 2 * evenT t + 2 ^ t ≤ n + 1) :
    evenCPrime t ⊆ Finset.range (n + 1) := by
  intro k hk
  rw [mem_evenCPrime] at hk
  simp only [Finset.mem_range]
  rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · have hsep := evenT_add_pow_le_two_mul_evenT t
    omega
  · omega

lemma evenC_disjoint_evenS (n t : ℕ) : Disjoint (evenC t) (evenS n t) := by
  rw [Finset.disjoint_left]
  intro k hkC hkS
  rw [mem_evenC] at hkC
  rw [mem_evenS] at hkS
  obtain ⟨a, ha, rfl⟩ := hkC
  obtain ⟨b, hb, hab⟩ := hkS
  have : a = b := by omega
  subst b
  exact (mem_evenSPrime n t a).mp hb |>.2.2 ha

/-! ## Exact block supports -/

lemma coeff_cosineBlockPolynomial_first (t j : ℕ) (hj : j < 2 ^ t) :
    (cosineBlockPolynomial t).coeff (evenT t + j) =
      (rudinShapiroP t).coeff j := by
  rw [cosineBlockPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  have hnot : ¬2 * evenT t ≤ evenT t + j := by
    have hsep := evenT_add_pow_le_two_mul_evenT t
    omega
  rw [if_pos (Nat.le_add_right _ _), if_neg hnot]
  simp

lemma coeff_cosineBlockPolynomial_second (t j : ℕ) (hj : j < 2 ^ t) :
    (cosineBlockPolynomial t).coeff (2 * evenT t + j) =
      (rudinShapiroQ t).coeff j := by
  rw [cosineBlockPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  have hfirst : evenT t ≤ 2 * evenT t + j := by omega
  rw [if_pos hfirst, if_pos (Nat.le_add_right _ _)]
  have hsub : 2 * evenT t + j - evenT t = evenT t + j := by omega
  rw [hsub, coeff_rudinShapiroP_eq_zero]
  · simp
  · exact (pow_le_evenT t).trans (Nat.le_add_right _ _)

lemma coeff_cosineBlockPolynomial_eq_zero_of_outside (t k : ℕ)
    (hk : k ∉ evenCPrime t) :
    (cosineBlockPolynomial t).coeff k = 0 := by
  rw [cosineBlockPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  by_cases hT : evenT t ≤ k
  · rw [if_pos hT]
    by_cases h2T : 2 * evenT t ≤ k
    · rw [if_pos h2T]
      have hq : 2 ^ t ≤ k - 2 * evenT t := by
        by_contra hq
        have hq' : k - 2 * evenT t < 2 ^ t := Nat.lt_of_not_ge hq
        apply hk
        rw [mem_evenCPrime]
        right
        exact ⟨k - 2 * evenT t, hq', (Nat.add_sub_of_le h2T).symm⟩
      have hp : 2 ^ t ≤ k - evenT t := by omega
      rw [coeff_rudinShapiroP_eq_zero hp, coeff_rudinShapiroQ_eq_zero hq,
        zero_add]
    · rw [if_neg h2T, add_zero]
      apply coeff_rudinShapiroP_eq_zero
      by_contra hp
      have hp' : k - evenT t < 2 ^ t := Nat.lt_of_not_ge hp
      apply hk
      rw [mem_evenCPrime]
      left
      exact ⟨k - evenT t, hp', (Nat.add_sub_of_le hT).symm⟩
  · rw [if_neg hT]
    have h2T : ¬2 * evenT t ≤ k := by omega
    rw [if_neg h2T, zero_add]

theorem support_cosineBlockPolynomial (t : ℕ) :
    (cosineBlockPolynomial t).support = evenCPrime t := by
  ext k
  simp only [Polynomial.mem_support_iff, ne_eq, mem_evenCPrime]
  constructor
  · intro hk
    by_contra hout
    apply hk
    apply coeff_cosineBlockPolynomial_eq_zero_of_outside t k
    rwa [mem_evenCPrime]
  · intro hk
    rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [coeff_cosineBlockPolynomial_first t j hj]
      rcases coeff_rudinShapiroP_eq_one_or_neg_one hj with h | h <;>
        rw [h] <;> norm_num
    · rw [coeff_cosineBlockPolynomial_second t j hj]
      rcases coeff_rudinShapiroQ_eq_one_or_neg_one hj with h | h <;>
        rw [h] <;> norm_num

lemma coeff_deletedEvenBlockPolynomial_first (t j : ℕ) (hj : j < 2 ^ t) :
    (deletedEvenBlockPolynomial t).coeff (evenT t + j) =
      (rudinShapiroP t).coeff j := by
  rw [deletedEvenBlockPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  have hnot : ¬2 * evenT t ≤ evenT t + j := by
    have hsep := evenT_add_pow_le_two_mul_evenT t
    omega
  rw [if_pos (Nat.le_add_right _ _), if_neg hnot]
  simp

lemma coeff_deletedEvenBlockPolynomial_second (t j : ℕ) (hj : j < 2 ^ t) :
    (deletedEvenBlockPolynomial t).coeff (2 * evenT t + j) =
      (rudinShapiroP t).coeff j := by
  rw [deletedEvenBlockPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  have hfirst : evenT t ≤ 2 * evenT t + j := by omega
  rw [if_pos hfirst, if_pos (Nat.le_add_right _ _)]
  have hsub : 2 * evenT t + j - evenT t = evenT t + j := by omega
  rw [hsub, coeff_rudinShapiroP_eq_zero]
  · simp
  · exact (pow_le_evenT t).trans (Nat.le_add_right _ _)

lemma coeff_deletedEvenBlockPolynomial_eq_zero_of_outside (t k : ℕ)
    (hk : k ∉ evenCPrime t) :
    (deletedEvenBlockPolynomial t).coeff k = 0 := by
  rw [deletedEvenBlockPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  by_cases hT : evenT t ≤ k
  · rw [if_pos hT]
    by_cases h2T : 2 * evenT t ≤ k
    · rw [if_pos h2T]
      have hsecond : 2 ^ t ≤ k - 2 * evenT t := by
        by_contra hsecond
        apply hk
        rw [mem_evenCPrime]
        right
        exact ⟨k - 2 * evenT t, Nat.lt_of_not_ge hsecond,
          (Nat.add_sub_of_le h2T).symm⟩
      have hfirst : 2 ^ t ≤ k - evenT t := by omega
      rw [coeff_rudinShapiroP_eq_zero hfirst,
        coeff_rudinShapiroP_eq_zero hsecond, zero_add]
    · rw [if_neg h2T, add_zero]
      apply coeff_rudinShapiroP_eq_zero
      by_contra hfirst
      apply hk
      rw [mem_evenCPrime]
      left
      exact ⟨k - evenT t, Nat.lt_of_not_ge hfirst,
        (Nat.add_sub_of_le hT).symm⟩
  · rw [if_neg hT]
    have h2T : ¬2 * evenT t ≤ k := by omega
    rw [if_neg h2T, zero_add]

/-! ## Stability of the two deleted blocks -/

/-- Once a coefficient of `P` has appeared, later Rudin--Shapiro recursion
levels leave it unchanged. -/
lemma coeff_rudinShapiroP_stable {a b k : ℕ} (hab : a ≤ b) (hk : k < 2 ^ a) :
    (rudinShapiroP b).coeff k = (rudinShapiroP a).coeff k := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      have hpow : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab
      rw [coeff_rudinShapiroP_succ_of_lt (hk.trans_le hpow), ih]

lemma coeff_rudinShapiroQ_add_ten (t j : ℕ) (hj : j < 2 ^ t) :
    (rudinShapiroQ (t + 10)).coeff j = (rudinShapiroP t).coeff j := by
  have hpow : 2 ^ t ≤ 2 ^ (t + 9) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [show t + 10 = (t + 9) + 1 by omega,
    coeff_rudinShapiroQ_succ_of_lt (hj.trans_le hpow)]
  exact coeff_rudinShapiroP_stable (by omega) hj

lemma coeff_rudinShapiroQ_add_eleven (t j : ℕ) (hj : j < 2 ^ t) :
    (rudinShapiroQ (t + 11)).coeff j = (rudinShapiroP t).coeff j := by
  have hpow : 2 ^ t ≤ 2 ^ (t + 10) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [show t + 11 = (t + 10) + 1 by omega,
    coeff_rudinShapiroQ_succ_of_lt (hj.trans_le hpow)]
  exact coeff_rudinShapiroP_stable (by omega) hj

/-- At every sufficiently late recursion level, the first distinguished block
of the stable prefix is a copy of `P_t`. -/
lemma coeff_rudinShapiroP_late_first_block {t u j : ℕ}
    (hu : t + 12 ≤ u) (hj : j < 2 ^ t) :
    (rudinShapiroP u).coeff (evenT t + j) =
      (rudinShapiroP t).coeff j := by
  have hindex : evenT t + j < 2 ^ (t + 11) := by
    rw [← two_mul_evenT]
    have hsep := evenT_add_pow_le_two_mul_evenT t
    omega
  calc
    (rudinShapiroP u).coeff (evenT t + j) =
        (rudinShapiroP (t + 11)).coeff (evenT t + j) :=
      coeff_rudinShapiroP_stable (by omega) hindex
    _ = (rudinShapiroQ (t + 10)).coeff j := by
      simpa [evenT] using coeff_rudinShapiroP_succ_add (t + 10) j
    _ = (rudinShapiroP t).coeff j := coeff_rudinShapiroQ_add_ten t j hj

/-- The second distinguished block of the stable prefix is another copy of
`P_t`. -/
lemma coeff_rudinShapiroP_late_second_block {t u j : ℕ}
    (hu : t + 12 ≤ u) (hj : j < 2 ^ t) :
    (rudinShapiroP u).coeff (2 * evenT t + j) =
      (rudinShapiroP t).coeff j := by
  have hindex : 2 * evenT t + j < 2 ^ (t + 12) := by
    have hsmall := pow_le_evenT t
    rw [show 2 ^ (t + 12) = 2 * evenT t + 2 * evenT t by
      simp [evenT, pow_add]
      ring]
    omega
  calc
    (rudinShapiroP u).coeff (2 * evenT t + j) =
        (rudinShapiroP (t + 12)).coeff (2 * evenT t + j) :=
      coeff_rudinShapiroP_stable hu hindex
    _ = (rudinShapiroQ (t + 11)).coeff j := by
      simpa [two_mul_evenT] using coeff_rudinShapiroP_succ_add (t + 11) j
    _ = (rudinShapiroP t).coeff j := coeff_rudinShapiroQ_add_eleven t j hj

lemma coeff_rudinShapiroP_late_eq_deleted {t u k : ℕ}
    (hu : t + 12 ≤ u) (hk : k ∈ evenCPrime t) :
    (rudinShapiroP u).coeff k = (deletedEvenBlockPolynomial t).coeff k := by
  rw [mem_evenCPrime] at hk
  rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [coeff_rudinShapiroP_late_first_block hu hj,
      coeff_deletedEvenBlockPolynomial_first t j hj]
  · rw [coeff_rudinShapiroP_late_second_block hu hj,
      coeff_deletedEvenBlockPolynomial_second t j hj]

lemma coeff_evenRemainderPolynomial_of_mem_CPrime {n t u k : ℕ}
    (hu : t + 12 ≤ u) (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hk : k ∈ evenCPrime t) :
    (evenRemainderPolynomial n t u).coeff k = 0 := by
  have hkrange := evenCPrime_subset_range hblock hk
  simp only [Finset.mem_range] at hkrange
  rw [evenRemainderPolynomial, Polynomial.coeff_sub,
    coeff_polynomialPrefix, if_pos hkrange,
    coeff_rudinShapiroP_late_eq_deleted hu hk, sub_self]

lemma coeff_evenRemainderPolynomial_sign_of_outside {n t u k : ℕ}
    (hprefix : n + 1 ≤ 2 ^ u) (hk : k < n + 1)
    (hkC : k ∉ evenCPrime t) :
    (evenRemainderPolynomial n t u).coeff k = 1 ∨
      (evenRemainderPolynomial n t u).coeff k = -1 := by
  rw [evenRemainderPolynomial, Polynomial.coeff_sub,
    coeff_polynomialPrefix, if_pos hk,
    coeff_deletedEvenBlockPolynomial_eq_zero_of_outside t k hkC, sub_zero]
  exact coeff_rudinShapiroP_eq_one_or_neg_one (hk.trans_le hprefix)

/-- Every positive frequency of the remaining even sine coordinate is a sign
exactly when it belongs to `S'_e`. -/
theorem coeff_evenRemainderPolynomial_sign_of_mem_evenSPrime {n t u k : ℕ}
    (hprefix : n + 1 ≤ 2 ^ u) (hk : k ∈ evenSPrime n t) :
    (evenRemainderPolynomial n t u).coeff k = 1 ∨
      (evenRemainderPolynomial n t u).coeff k = -1 := by
  rw [mem_evenSPrime] at hk
  exact coeff_evenRemainderPolynomial_sign_of_outside hprefix (by omega) hk.2.2

/-- On the two reserved blocks the remaining sine coefficient vanishes. -/
theorem coeff_evenRemainderPolynomial_eq_zero_on_CPrime {n t u k : ℕ}
    (hu : t + 12 ≤ u) (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hk : k ∈ evenCPrime t) :
    (evenRemainderPolynomial n t u).coeff k = 0 :=
  coeff_evenRemainderPolynomial_of_mem_CPrime hu hblock hk

/-! ## Evaluation formulae -/

theorem evenCosine_eq (t : ℕ) (theta : ℝ) :
    evenCosine t theta =
      ((unitPoint (2 * theta)) ^ evenT t *
          (rudinShapiroP t).eval (unitPoint (2 * theta)) +
        (unitPoint (2 * theta)) ^ (2 * evenT t) *
          (rudinShapiroQ t).eval (unitPoint (2 * theta))).re := by
  simp [evenCosine, cosineBlockPolynomial]

theorem evenSine_eq (n t u : ℕ) (theta : ℝ) :
    evenSine n t u theta =
      ((polynomialPrefix (rudinShapiroP u) (n + 1)).eval
          (unitPoint (2 * theta)) -
        (unitPoint (2 * theta)) ^ evenT t *
          (rudinShapiroP t).eval (unitPoint (2 * theta)) -
        (unitPoint (2 * theta)) ^ (2 * evenT t) *
          (rudinShapiroP t).eval (unitPoint (2 * theta))).im := by
  simp [evenSine, evenRemainderPolynomial, deletedEvenBlockPolynomial]
  ring

/-! ## The global estimates (BBMST Lemma 3.3) -/

private lemma two_mul_sqrt_pow_le_sqrt_nat {n t : ℕ}
    (hscale : 2 ^ (t + 3) ≤ n) :
    2 * Real.sqrt (2 ^ (t + 1) : ℝ) ≤ Real.sqrt n := by
  have hcast : (2 ^ (t + 3) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hscale
  have hpow : (2 ^ (t + 3) : ℝ) = 4 * (2 ^ (t + 1) : ℝ) := by
    rw [show t + 3 = (t + 1) + 2 by omega, pow_add]
    ring
  have hA : 0 ≤ (2 ^ (t + 1) : ℝ) := by positivity
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hsA := Real.sq_sqrt hA
  have hsn := Real.sq_sqrt hn
  have hsAn := Real.sqrt_nonneg (2 ^ (t + 1) : ℝ)
  have hsnn := Real.sqrt_nonneg (n : ℝ)
  rw [hpow] at hcast
  nlinarith

/-- The cosine coordinate has the paper's `sqrt n` global bound. -/
theorem abs_evenCosine_le_sqrt (n t : ℕ)
    (hscale : 2 ^ (t + 3) ≤ n) (theta : ℝ) :
    |evenCosine t theta| ≤ Real.sqrt n := by
  let z := unitPoint (2 * theta)
  have hz : ‖z‖ = 1 := norm_unitPoint _
  have hP := norm_eval_rudinShapiroP_le t hz
  have hQ := norm_eval_rudinShapiroQ_le t hz
  rw [evenCosine_eq]
  change |(z ^ evenT t * (rudinShapiroP t).eval z +
      z ^ (2 * evenT t) * (rudinShapiroQ t).eval z).re| ≤ _
  calc
    |(z ^ evenT t * (rudinShapiroP t).eval z +
        z ^ (2 * evenT t) * (rudinShapiroQ t).eval z).re| ≤
        ‖z ^ evenT t * (rudinShapiroP t).eval z +
          z ^ (2 * evenT t) * (rudinShapiroQ t).eval z‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖z ^ evenT t * (rudinShapiroP t).eval z‖ +
        ‖z ^ (2 * evenT t) * (rudinShapiroQ t).eval z‖ := norm_add_le _ _
    _ = ‖(rudinShapiroP t).eval z‖ + ‖(rudinShapiroQ t).eval z‖ := by
      simp [norm_mul, norm_pow, hz]
    _ ≤ 2 * Real.sqrt (2 ^ (t + 1) : ℝ) := by linarith
    _ ≤ Real.sqrt n := two_mul_sqrt_pow_le_sqrt_nat hscale

private lemma sqrt_succ_le_eleven_tenths_sqrt {n : ℕ} (hn : 5 ≤ n) :
    Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ (11 / 10 : ℝ) * Real.sqrt n := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hn1 : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hs0 := Real.sq_sqrt hn0
  have hs1 := Real.sq_sqrt hn1
  have hs0n := Real.sqrt_nonneg (n : ℝ)
  have hs1n := Real.sqrt_nonneg ((n + 1 : ℕ) : ℝ)
  have hncast : (5 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num only [Nat.cast_add, Nat.cast_one] at hs1
  by_contra hnot
  have hlt : ((11 / 10 : ℝ) * Real.sqrt n) ^ 2 <
      Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 :=
    (sq_lt_sq₀ (by positivity) hs1n).2 (lt_of_not_ge hnot)
  norm_num only [Nat.cast_add, Nat.cast_one] at hlt
  have hlt' : (121 / 100 : ℝ) * n < n + 1 := by
    nlinarith [hlt, hs0, hs1]
  nlinarith

private lemma two_mul_sqrt_pow_le_half_sqrt_nat {n t : ℕ}
    (hscale : 2 ^ (t + 5) ≤ n) :
    2 * Real.sqrt (2 ^ (t + 1) : ℝ) ≤ (1 / 2 : ℝ) * Real.sqrt n := by
  have hcast : (2 ^ (t + 5) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hscale
  have hpow : (2 ^ (t + 5) : ℝ) = 16 * (2 ^ (t + 1) : ℝ) := by
    rw [show t + 5 = (t + 1) + 4 by omega, pow_add]
    ring
  have hA : 0 ≤ (2 ^ (t + 1) : ℝ) := by positivity
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hsA := Real.sq_sqrt hA
  have hsn := Real.sq_sqrt hn
  have hsAn := Real.sqrt_nonneg (2 ^ (t + 1) : ℝ)
  have hsnn := Real.sqrt_nonneg (n : ℝ)
  rw [hpow] at hcast
  nlinarith

/-- The remaining even sine coordinate has the paper's `6 sqrt n` global
bound.  The hypotheses are the two elementary numerical consequences of
BBMST's parameter equation and `gamma ≤ 2^-40`. -/
theorem abs_evenSine_le_six_sqrt (n t u : ℕ)
    (hprefix : n + 1 ≤ 2 ^ u) (hn : 5 ≤ n)
    (hscale : 2 ^ (t + 5) ≤ n) (theta : ℝ) :
    |evenSine n t u theta| ≤ 6 * Real.sqrt n := by
  let z := unitPoint (2 * theta)
  have hz : ‖z‖ = 1 := norm_unitPoint _
  have hpref := norm_eval_polynomialPrefix_rudinShapiroP_le u (n + 1) hprefix hz
  have hP := norm_eval_rudinShapiroP_le t hz
  rw [evenSine_eq]
  change |((polynomialPrefix (rudinShapiroP u) (n + 1)).eval z -
      z ^ evenT t * (rudinShapiroP t).eval z -
      z ^ (2 * evenT t) * (rudinShapiroP t).eval z).im| ≤ _
  calc
    |((polynomialPrefix (rudinShapiroP u) (n + 1)).eval z -
        z ^ evenT t * (rudinShapiroP t).eval z -
        z ^ (2 * evenT t) * (rudinShapiroP t).eval z).im| ≤
        ‖(polynomialPrefix (rudinShapiroP u) (n + 1)).eval z -
          z ^ evenT t * (rudinShapiroP t).eval z -
          z ^ (2 * evenT t) * (rudinShapiroP t).eval z‖ :=
      Complex.abs_im_le_norm _
    _ ≤ ‖(polynomialPrefix (rudinShapiroP u) (n + 1)).eval z‖ +
          ‖z ^ evenT t * (rudinShapiroP t).eval z‖ +
          ‖z ^ (2 * evenT t) * (rudinShapiroP t).eval z‖ := by
      calc
        _ ≤ ‖(polynomialPrefix (rudinShapiroP u) (n + 1)).eval z -
              z ^ evenT t * (rudinShapiroP t).eval z‖ +
              ‖z ^ (2 * evenT t) * (rudinShapiroP t).eval z‖ := norm_sub_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_sub_le _ _
    _ = ‖(polynomialPrefix (rudinShapiroP u) (n + 1)).eval z‖ +
          2 * ‖(rudinShapiroP t).eval z‖ := by
      simp [norm_mul, norm_pow, hz]
      ring
    _ ≤ 5 * Real.sqrt ((n + 1 : ℕ) : ℝ) +
          2 * Real.sqrt (2 ^ (t + 1) : ℝ) := by
      exact add_le_add hpref (mul_le_mul_of_nonneg_left hP (by norm_num))
    _ ≤ 5 * ((11 / 10 : ℝ) * Real.sqrt n) +
          (1 / 2 : ℝ) * Real.sqrt n := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (sqrt_succ_le_eleven_tenths_sqrt hn) (by norm_num))
        (two_mul_sqrt_pow_le_half_sqrt_nat hscale)
    _ = 6 * Real.sqrt n := by ring

/-- The cosine bound with all numerical input discharged by BBMST's parameter
package. -/
theorem abs_evenCosine_le_sqrt_of_parameters {n t : ℕ} {gamma : ℝ}
    (h : EvenParameters n t gamma) (theta : ℝ) :
    |evenCosine t theta| ≤ Real.sqrt n := by
  apply abs_evenCosine_le_sqrt n t
  exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans
    h.pow_t_add_five_le_n

/-- The even-sine bound with all BBMST numerical hypotheses discharged. -/
theorem abs_evenSine_le_six_sqrt_of_parameters {n t u : ℕ} {gamma : ℝ}
    (h : EvenParameters n t gamma) (hprefix : n + 1 ≤ 2 ^ u)
    (theta : ℝ) :
    |evenSine n t u theta| ≤ 6 * Real.sqrt n :=
  abs_evenSine_le_six_sqrt n t u hprefix h.five_le_n
    h.pow_t_add_five_le_n theta

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/Interpolation.lean` -/

section
/-!
# Quantitative interpolation bounds for Erdős Problem 228

This file contains the finite-dimensional estimate used in the Howell
interpolation step of the flat Littlewood-polynomial construction.  The
analytic interpolation theorem writes a derivative as a weighted sum of
function values, up to a remainder.  The lemmas below bound the Lagrange
weights from separation of the nodes and then propagate uniform bounds on the
values and the remainder to the derivative.
-/

namespace Interpolation

open scoped BigOperators

/-! ### Repeated Rolle theorem -/

/-- If a `C^k` real function vanishes at `k+1` strictly increasing points,
then its `k`th derivative vanishes somewhere between the first and last
point.  This is the analytic core of the interpolation remainder argument. -/
theorem exists_iteratedDeriv_eq_zero_of_strictMono :
    ∀ (k : ℕ) (g : ℝ → ℝ) (x : Fin (k + 1) → ℝ),
      ContDiff ℝ k g → StrictMono x → (∀ i, g (x i) = 0) →
      ∃ z ∈ Set.Icc (x 0) (x (Fin.last k)), iteratedDeriv k g z = 0 := by
  intro k
  induction k with
  | zero =>
      intro g x _hg _hx hzero
      refine ⟨x 0, ⟨le_rfl, ?_⟩, ?_⟩
      · simp
      · simpa using hzero 0
  | succ k ih =>
      intro g x hg hx hzero
      have hrolle (i : Fin (k + 1)) :
          ∃ c ∈ Set.Ioo (x i.castSucc) (x i.succ), deriv g c = 0 := by
        apply exists_deriv_eq_zero
        · exact hx Fin.castSucc_lt_succ
        · exact hg.continuous.continuousOn
        · rw [hzero i.castSucc, hzero i.succ]
      let c : Fin (k + 1) → ℝ := fun i ↦ Classical.choose (hrolle i)
      have hc_mem (i : Fin (k + 1)) :
          c i ∈ Set.Ioo (x i.castSucc) (x i.succ) :=
        (Classical.choose_spec (hrolle i)).1
      have hc_zero (i : Fin (k + 1)) : deriv g (c i) = 0 :=
        (Classical.choose_spec (hrolle i)).2
      have hc_mono : StrictMono c := by
        intro i j hij
        have hij' : i.succ ≤ j.castSucc := by
          apply Fin.mk_le_mk.mpr
          omega
        exact (hc_mem i).2.trans ((hx.monotone hij').trans_lt (hc_mem j).1)
      have hderiv : ContDiff ℝ k (deriv g) := hg.deriv'
      obtain ⟨z, hz, hz0⟩ := ih (deriv g) c hderiv hc_mono hc_zero
      refine ⟨z, ⟨?_, ?_⟩, ?_⟩
      · exact (hc_mem 0).1.le.trans hz.1
      · exact hz.2.trans (hc_mem (Fin.last k)).2.le
      · simpa only [iteratedDeriv_succ'] using hz0

/-- The coefficient of the top-degree term of the `j`th Lagrange basis
polynomial, multiplied by `k!`.  Thus these are the weights occurring when
the `k`th derivative of the interpolating polynomial is evaluated. -/
noncomputable def lagrangeDerivativeWeight (k : ℕ) (y : Fin (k + 1) → ℝ)
    (j : Fin (k + 1)) : ℝ :=
  (k.factorial : ℝ) /
    ∏ i ∈ (Finset.univ.erase j), (y j - y i)

/-- The `k`th derivative of the degree-`k` Lagrange interpolant is the
weighted sum defined by `lagrangeDerivativeWeight`. -/
theorem eval_iterate_derivative_interpolate_top (k : ℕ)
    (y : Fin (k + 1) → ℝ) (v : Fin (k + 1) → ℝ) (hy : Function.Injective y)
    (x : ℝ) :
    ((Polynomial.derivative^[k])
      (Lagrange.interpolate Finset.univ y v)).eval x =
      ∑ i, lagrangeDerivativeWeight k y i * v i := by
  rw [Lagrange.iterate_derivative_interpolate v hy.injOn (by simp)]
  simp [lagrangeDerivativeWeight, Finset.mul_sum, div_eq_mul_inv, mul_comm]
  simp [Polynomial.eval_finsetSum, mul_left_comm]

/-- Iterated analytic differentiation of a polynomial evaluation agrees with
iteration of its formal polynomial derivative. -/
theorem iteratedDeriv_polynomial_eval (k : ℕ) (P : Polynomial ℝ) (x : ℝ) :
    iteratedDeriv k (fun t ↦ P.eval t) x =
      ((Polynomial.derivative^[k]) P).eval x := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ']
      have hfun : deriv (fun t ↦ P.eval t) = fun t ↦ P.derivative.eval t := by
        funext t
        exact P.deriv
      rw [hfun, ih]
      rw [Function.iterate_succ_apply']
      exact congrArg (Polynomial.eval x)
        ((Function.Commute.self_iterate
          (Polynomial.derivative : Polynomial ℝ → Polynomial ℝ) k) P).symm

/-- Howell's derivative interpolation estimate on the real line.

The nodes are strictly increasing, lie at distance at most `Delta` from the
basepoint `x`, and the `(k+1)`st derivative is bounded by `M`.  The `k`th
derivative at `x` is therefore within `Delta * M` of the `k`th derivative of
the Lagrange interpolant through the sampled values. -/
theorem howell_derivative_approximation (k : ℕ) (f : ℝ → ℝ)
    (y : Fin (k + 1) → ℝ) (x Delta M : ℝ)
    (hf : ContDiff ℝ (k + 1) f) (hy : StrictMono y)
    (_hDelta : 0 ≤ Delta) (hM : 0 ≤ M)
    (hyx : ∀ i, |y i - x| ≤ Delta)
    (hderiv : ∀ t, |iteratedDeriv (k + 1) f t| ≤ M) :
    |iteratedDeriv k f x -
      ∑ i, lagrangeDerivativeWeight k y i * f (y i)| ≤ Delta * M := by
  let P : Polynomial ℝ := Lagrange.interpolate Finset.univ y (fun i ↦ f (y i))
  let g : ℝ → ℝ := fun t ↦ f t - P.eval t
  have hP : ContDiff ℝ (k + 1) (fun t ↦ P.eval t) := by
    induction P using Polynomial.induction_on' with
    | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
    | monomial n a =>
        simp only [Polynomial.eval_monomial]
        fun_prop
  have hg : ContDiff ℝ k g := by
    apply ContDiff.sub (hf.of_le (by norm_num)) (hP.of_le (by norm_num))
  have hzero : ∀ i, g (y i) = 0 := by
    intro i
    have hPi : P.eval (y i) = f (y i) := by
      dsimp only [P]
      exact Lagrange.eval_interpolate_at_node _ hy.injective.injOn (Finset.mem_univ i)
    dsimp only [g]
    rw [hPi, sub_self]
  obtain ⟨z, hz, hz0⟩ :=
    exists_iteratedDeriv_eq_zero_of_strictMono k g y hg hy hzero
  have hPAt : ContDiffAt ℝ k (fun t ↦ P.eval t) z := (hP.of_le (by norm_num)).contDiffAt
  have hfAt : ContDiffAt ℝ k f z := (hf.of_le (by norm_num)).contDiffAt
  have hzEq : iteratedDeriv k f z =
      ∑ i, lagrangeDerivativeWeight k y i * f (y i) := by
    change iteratedDeriv k (f - fun t ↦ P.eval t) z = 0 at hz0
    rw [iteratedDeriv_sub hfAt hPAt, iteratedDeriv_polynomial_eval,
      eval_iterate_derivative_interpolate_top k y (fun i ↦ f (y i)) hy.injective z] at hz0
    linarith
  have hzDist : |z - x| ≤ Delta := by
    have hleft := (abs_le.mp (hyx (0 : Fin (k + 1)))).1
    have hright := (abs_le.mp (hyx (Fin.last k))).2
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hdiff : Differentiable ℝ (iteratedDeriv k f) :=
    hf.differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)
  have hmean :
      |iteratedDeriv k f x - iteratedDeriv k f z| ≤ M * |x - z| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (f := iteratedDeriv k f) (x := z) (y := x)
      (fun t _ ↦ hdiff.differentiableAt)
      (fun t _ ↦ by
        rw [← iteratedDeriv_succ]
        simpa only [Real.norm_eq_abs] using hderiv t)
      convex_univ (Set.mem_univ z) (Set.mem_univ x)
    simpa only [Real.norm_eq_abs] using h
  rw [← hzEq]
  calc
    |iteratedDeriv k f x - iteratedDeriv k f z| ≤ M * |x - z| := hmean
    _ = M * |z - x| := by rw [abs_sub_comm]
    _ ≤ M * Delta := mul_le_mul_of_nonneg_left hzDist hM
    _ = Delta * M := mul_comm _ _

/-- A product of `k` factors, each of absolute value at least `eta`, has
absolute value at least `eta ^ k`. -/
theorem pow_le_abs_prod_of_separated (k : ℕ) (y : Fin (k + 1) → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (j : Fin (k + 1)) :
    eta ^ k ≤ |∏ i ∈ (Finset.univ.erase j), (y j - y i)| := by
  classical
  rw [Finset.abs_prod]
  have hcard : (Finset.univ.erase j).card = k := by simp
  calc
    eta ^ k = eta ^ (Finset.univ.erase j).card := congrArg (eta ^ ·) hcard.symm
    _ = ∏ _i ∈ (Finset.univ.erase j), eta := by simp
    _ ≤ ∏ i ∈ (Finset.univ.erase j), |y j - y i| := by
      apply Finset.prod_le_prod (fun _i _hi ↦ heta)
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simpa only [abs_sub_comm] using hsep i j hij

/-- Separation of the interpolation nodes bounds every top-derivative
Lagrange weight by `k! / eta^k`. -/
theorem abs_lagrangeDerivativeWeight_le (k : ℕ) (y : Fin (k + 1) → ℝ) (eta : ℝ)
    (heta : 0 < eta)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (j : Fin (k + 1)) :
    |lagrangeDerivativeWeight k y j| ≤ (k.factorial : ℝ) / eta ^ k := by
  rw [lagrangeDerivativeWeight, abs_div, abs_of_nonneg (Nat.cast_nonneg _)]
  have hprod := pow_le_abs_prod_of_separated k y eta heta.le hsep j
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hprod

/-- Uniformly bounded summands have a uniformly bounded finite sum. -/
theorem abs_sum_le_card_mul {n : ℕ} (u : Fin n → ℝ) (A : ℝ)
    (hA : ∀ i, |u i| ≤ A) :
    |∑ i, u i| ≤ n * A := by
  calc
    |∑ i, u i| ≤ ∑ i, |u i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, A := Finset.sum_le_sum fun i _ ↦ hA i
    _ = n * A := by simp [nsmul_eq_mul]

/-- The interpolation sum is small when the nodes are separated and all
sampled function values are small. -/
theorem abs_lagrange_sum_le (k : ℕ) (y : Fin (k + 1) → ℝ) (eta epsilon : ℝ)
    (heta : 0 < eta) (_hepsilon : 0 ≤ epsilon)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (v : Fin (k + 1) → ℝ) (hv : ∀ i, |v i| ≤ epsilon) :
    |∑ i, lagrangeDerivativeWeight k y i * v i| ≤
      (k + 1) * ((k.factorial : ℝ) / eta ^ k * epsilon) := by
  have h := abs_sum_le_card_mul
    (fun i ↦ lagrangeDerivativeWeight k y i * v i)
    ((k.factorial : ℝ) / eta ^ k * epsilon) (fun i ↦ by
      rw [abs_mul]
      exact mul_le_mul
        (abs_lagrangeDerivativeWeight_le k y eta heta hsep i) (hv i)
        (abs_nonneg _) (by positivity))
  simpa [Nat.cast_add, Nat.cast_one] using h

/-- Quantitative Howell estimate, in the form needed by the construction.

The analytic part of derivative interpolation supplies `happrox`: the
derivative `d` differs from the derivative of the Lagrange interpolant by at
most `remainder`.  This lemma performs the complete quantitative estimate
from node separation and small sampled values. -/
theorem howell_bound_of_approximation (k : ℕ) (y : Fin (k + 1) → ℝ)
    (eta epsilon remainder d : ℝ)
    (heta : 0 < eta) (hepsilon : 0 ≤ epsilon) (_hremainder : 0 ≤ remainder)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (v : Fin (k + 1) → ℝ) (hv : ∀ i, |v i| ≤ epsilon)
    (happrox : |d - ∑ i, lagrangeDerivativeWeight k y i * v i| ≤ remainder) :
    |d| ≤ remainder + (k + 1) * ((k.factorial : ℝ) / eta ^ k * epsilon) := by
  have hsum := abs_lagrange_sum_le k y eta epsilon heta hepsilon hsep v hv
  calc
    |d| = |(d - ∑ i, lagrangeDerivativeWeight k y i * v i) +
        ∑ i, lagrangeDerivativeWeight k y i * v i| := by ring_nf
    _ ≤ |d - ∑ i, lagrangeDerivativeWeight k y i * v i| +
        |∑ i, lagrangeDerivativeWeight k y i * v i| := abs_add_le _ _
    _ ≤ remainder + (k + 1) * ((k.factorial : ℝ) / eta ^ k * epsilon) :=
      add_le_add happrox hsum

/-- The numerical specialization used in the seven-cell small-value
argument.  For derivative orders `1`, `2`, and `3`, values of size at most
`eta^3 / 128`, node separation `eta`, and interpolation remainder at most
`126 * eta` force the derivative to have absolute value strictly below
`1 / 4` whenever `eta < 2⁻¹¹`.

The constant `126` is `7 * 18`: every node is within `7 * eta` of the
basepoint and the fourth-derivative bound in the application is
`2^4 + 2 = 18`. -/
theorem howell_lt_quarter (k : ℕ) (hk₁ : 1 ≤ k) (hk₃ : k ≤ 3)
    (y : Fin (k + 1) → ℝ) (eta d : ℝ)
    (heta : 0 < eta) (hetaSmall : eta < (1 : ℝ) / 2048)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (v : Fin (k + 1) → ℝ) (hv : ∀ i, |v i| ≤ eta ^ 3 / 128)
    (happrox : |d - ∑ i, lagrangeDerivativeWeight k y i * v i| ≤ 126 * eta) :
    |d| < 1 / 4 := by
  have hetaPow : 0 ≤ eta ^ 3 / 128 := by positivity
  have hbound := howell_bound_of_approximation k y eta (eta ^ 3 / 128)
    (126 * eta) d heta hetaPow (by positivity) hsep v hv happrox
  have hetaOne : eta < 1 := by
    calc
      eta < (1 : ℝ) / 2048 := hetaSmall
      _ < 1 := by norm_num
  have hetaLeOne : eta ≤ 1 := hetaOne.le
  have hetaSqLeOne : eta ^ 2 ≤ 1 := by nlinarith [sq_nonneg eta]
  have hinterp :
      (k + 1 : ℝ) * ((k.factorial : ℝ) / eta ^ k * (eta ^ 3 / 128)) ≤ 3 / 16 := by
    interval_cases k <;> norm_num at hk₁ hk₃ ⊢
    · field_simp [ne_of_gt heta]
      nlinarith [sq_nonneg eta]
    · field_simp [ne_of_gt heta]
      nlinarith
    · field_simp [ne_of_gt heta]
      norm_num
  have hrem : 126 * eta < 1 / 16 := by
    norm_num at hetaSmall ⊢
    nlinarith
  nlinarith

/-- Fully analytic form of the Howell estimate used for derivative orders
`1`, `2`, and `3` in the seven-cell argument.  This combines repeated Rolle,
Lagrange interpolation, the derivative remainder estimate, the separated-node
weight bound, and the final numerical calculation. -/
theorem howell_lt_quarter_of_nodes (k : ℕ) (hk₁ : 1 ≤ k) (hk₃ : k ≤ 3)
    (f : ℝ → ℝ) (y : Fin (k + 1) → ℝ) (x eta : ℝ)
    (hf : ContDiff ℝ (k + 1) f) (hy : StrictMono y)
    (heta : 0 < eta) (hetaSmall : eta < (1 : ℝ) / 2048)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (hyx : ∀ i, |y i - x| ≤ 7 * eta)
    (hvalue : ∀ i, |f (y i)| ≤ eta ^ 3 / 128)
    (hderiv : ∀ t, |iteratedDeriv (k + 1) f t| ≤ 18) :
    |iteratedDeriv k f x| < 1 / 4 := by
  have happrox' := howell_derivative_approximation k f y x (7 * eta) 18 hf hy
    (by positivity) (by norm_num) hyx hderiv
  have happrox :
      |iteratedDeriv k f x -
        ∑ i, lagrangeDerivativeWeight k y i * f (y i)| ≤ 126 * eta := by
    convert happrox' using 1
    ring
  exact howell_lt_quarter k hk₁ hk₃ y eta (iteratedDeriv k f x) heta hetaSmall
    hsep (fun i ↦ f (y i)) hvalue happrox

end Interpolation

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/Intervals.lean` -/

section
/-!
# Finite grid intervals for Erdős Problem 228

This file isolates the finite, one-dimensional bookkeeping used when the
Rudin--Shapiro cosine sum is small.  There are three independent pieces:

* equally spaced grids and blocks of consecutive indices;
* maximal runs of indices satisfying a decidable predicate, together with the
  elementary bound "runs ≤ changes + 1";
* reflection operations on intervals and a generic way to bound the number of
  runs by the number of level-crossing witnesses.

The analytic construction can instantiate `bad i` with a strict sublevel-set
condition at the `i`-th grid point.  Continuity then supplies a level point in
each cell at which the truth value changes.
-/

namespace Intervals

open Set

/-! ## Equally spaced grids -/

/-- The `k`-th point of the grid of mesh `π / n`. -/
noncomputable def gridPoint (n k : ℕ) : ℝ := (k : ℝ) * Real.pi / n

/-- The closed cell between two consecutive grid points. -/
noncomputable def gridCell (n k : ℕ) : Set ℝ :=
  Icc (gridPoint n k) (gridPoint n (k + 1))

/-- A block of `length` consecutive integer grid indices. -/
def indexBlock (start length : ℕ) : Finset ℕ :=
  (Finset.range length).image (start + ·)

@[simp] theorem mem_indexBlock {start length i : ℕ} :
    i ∈ indexBlock start length ↔ start ≤ i ∧ i < start + length := by
  constructor
  · simp only [indexBlock, Finset.mem_image, Finset.mem_range]
    rintro ⟨j, hj, rfl⟩
    omega
  · rintro ⟨hsi, hi⟩
    simp only [indexBlock, Finset.mem_image, Finset.mem_range]
    exact ⟨i - start, by omega, by omega⟩

@[simp] theorem card_indexBlock (start length : ℕ) :
    (indexBlock start length).card = length := by
  rw [indexBlock, Finset.card_image_of_injective]
  · simp
  · exact fun _ _ h ↦ Nat.add_left_cancel h

theorem gridPoint_zero (n : ℕ) : gridPoint n 0 = 0 := by
  simp [gridPoint]

theorem gridPoint_add (n k l : ℕ) :
    gridPoint n (k + l) = gridPoint n k + gridPoint n l := by
  simp only [gridPoint, Nat.cast_add]
  ring

theorem gridPoint_succ (n k : ℕ) :
    gridPoint n (k + 1) = gridPoint n k + Real.pi / n := by
  rw [gridPoint_add]
  simp [gridPoint]

theorem gridPoint_strictMono {n : ℕ} (hn : 0 < n) :
    StrictMono (gridPoint n) := by
  intro i j hij
  simp only [gridPoint]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hn'
  simpa [mul_div_assoc] using (mul_lt_mul_of_pos_right (by exact_mod_cast hij) hpi)

theorem gridPoint_mono {n : ℕ} (hn : 0 < n) :
    Monotone (gridPoint n) := (gridPoint_strictMono hn).monotone

/-! ## Reflection bookkeeping -/

/-- Reflect an oriented interval through the origin. -/
def negInterval (I : ℝ × ℝ) : ℝ × ℝ := (-I.2, -I.1)

/-- Reflect an oriented interval through `π / 2`, i.e. by `θ ↦ π - θ`. -/
noncomputable def piMinusInterval (I : ℝ × ℝ) : ℝ × ℝ :=
  (Real.pi - I.2, Real.pi - I.1)

/-- Translate an oriented interval by `π`, i.e. by `θ ↦ π + θ`. -/
noncomputable def piPlusInterval (I : ℝ × ℝ) : ℝ × ℝ :=
  (Real.pi + I.1, Real.pi + I.2)

@[simp] theorem mem_Icc_negInterval {a b x : ℝ} :
    x ∈ Icc a b ↔ -x ∈ Icc (negInterval (a, b)).1 (negInterval (a, b)).2 := by
  change (a ≤ x ∧ x ≤ b) ↔ (-b ≤ -x ∧ -x ≤ -a)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

@[simp] theorem mem_Icc_piMinusInterval {a b x : ℝ} :
    x ∈ Icc a b ↔
      Real.pi - x ∈ Icc (piMinusInterval (a, b)).1 (piMinusInterval (a, b)).2 := by
  change (a ≤ x ∧ x ≤ b) ↔
    (Real.pi - b ≤ Real.pi - x ∧ Real.pi - x ≤ Real.pi - a)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

@[simp] theorem mem_Icc_piPlusInterval {a b x : ℝ} :
    x ∈ Icc a b ↔
      Real.pi + x ∈ Icc (piPlusInterval (a, b)).1 (piPlusInterval (a, b)).2 := by
  simp [piPlusInterval]

/-! ## Changes and maximal bad runs -/

/-- Indices at which a predicate changes between `i` and `i+1`.  The first
condition keeps both endpoints in `{0, ..., N-1}`. -/
def changeIndices (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad] : Finset ℕ :=
  (Finset.range N).filter fun i ↦ i + 1 < N ∧ ¬ (bad i ↔ bad (i + 1))

/-- Left endpoints of the maximal consecutive runs on which `bad` holds. -/
def runStarts (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad] : Finset ℕ :=
  (Finset.range N).filter fun i ↦ bad i ∧ (i = 0 ∨ ¬ bad (i - 1))

@[simp] theorem mem_changeIndices {N i : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] :
    i ∈ changeIndices N bad ↔ i + 1 < N ∧ ¬ (bad i ↔ bad (i + 1)) := by
  simp [changeIndices]
  omega

@[simp] theorem mem_runStarts {N i : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] :
    i ∈ runStarts N bad ↔
      i < N ∧ bad i ∧ (i = 0 ∨ ¬ bad (i - 1)) := by
  simp [runStarts]

/-- The interval `[a,b]` is one maximal run of `bad` in `{0, ..., N-1}`. -/
def IsMaximalBadRun (N : ℕ) (bad : ℕ → Prop) (a b : ℕ) : Prop :=
  a ≤ b ∧ b < N ∧
    (∀ i ∈ Finset.range N, a ≤ i → i ≤ b → bad i) ∧
    (a = 0 ∨ ¬ bad (a - 1)) ∧
    (b + 1 = N ∨ ¬ bad (b + 1))

instance instDecidableIsMaximalBadRun (N : ℕ) (bad : ℕ → Prop)
    [DecidablePred bad] (a b : ℕ) : Decidable (IsMaximalBadRun N bad a b) := by
  unfold IsMaximalBadRun
  infer_instance

/-- The finite set of all maximal bad runs, encoded by their endpoints. -/
def maximalBadRuns (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad] :
    Finset (ℕ × ℕ) :=
  ((Finset.range N).product (Finset.range N)).filter fun I ↦
    IsMaximalBadRun N bad I.1 I.2

/-- Two maximal bad runs with the same left endpoint are equal. -/
theorem IsMaximalBadRun.eq_of_start_eq {N a b c d : ℕ} {bad : ℕ → Prop}
    (h₁ : IsMaximalBadRun N bad a b) (h₂ : IsMaximalBadRun N bad c d)
    (hac : a = c) : (a, b) = (c, d) := by
  subst c
  congr 1
  apply le_antisymm
  · by_contra hnot
    have hdb : d < b := Nat.lt_of_not_ge hnot
    have hbad : bad (d + 1) :=
      h₁.2.2.1 (d + 1) (Finset.mem_range.2 (lt_of_le_of_lt hdb h₁.2.1))
        (Nat.le_succ_of_le h₂.1) hdb
    rcases h₂.2.2.2.2 with heq | hnbad
    · have hNb : N ≤ b := by omega
      exact (Nat.not_le_of_gt h₁.2.1) hNb
    · exact hnbad hbad
  · by_contra hnot
    have hbd : b < d := Nat.lt_of_not_ge hnot
    have hbad : bad (b + 1) :=
      h₂.2.2.1 (b + 1) (Finset.mem_range.2 (lt_of_le_of_lt hbd h₂.2.1))
        (Nat.le_succ_of_le h₁.1) hbd
    rcases h₁.2.2.2.2 with heq | hnbad
    · have hNd : N ≤ d := by omega
      exact (Nat.not_le_of_gt h₂.2.1) hNd
    · exact hnbad hbad

@[simp] theorem mem_maximalBadRuns {N a b : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] :
    (a, b) ∈ maximalBadRuns N bad ↔ IsMaximalBadRun N bad a b := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (h.1.trans_lt h.2.1), Finset.mem_range.mpr h.2.1⟩, h⟩

/-- Moving left from a bad index eventually reaches the beginning of its bad
run.  The last conjunct records that no good index was crossed. -/
theorem exists_runStart_le {N i : ℕ} {bad : ℕ → Prop} [DecidablePred bad]
    (hiN : i < N) (hi : bad i) :
    ∃ a, a ≤ i ∧ a ∈ runStarts N bad ∧
      ∀ j, a ≤ j → j ≤ i → bad j := by
  induction i with
  | zero =>
      refine ⟨0, le_rfl, ?_, ?_⟩
      · rw [mem_runStarts]
        exact ⟨hiN, hi, Or.inl rfl⟩
      · intro j hj₀ hj₁
        have : j = 0 := by omega
        simpa [this] using hi
  | succ i ih =>
      by_cases hprev : bad i
      · obtain ⟨a, hai, hastart, harun⟩ := ih (by omega) hprev
        refine ⟨a, by omega, hastart, ?_⟩
        intro j haj hji
        by_cases hj : j = i + 1
        · simpa [hj] using hi
        · exact harun j haj (by omega)
      · refine ⟨i + 1, le_rfl, ?_, ?_⟩
        · rw [mem_runStarts]
          refine ⟨hiN, hi, Or.inr ?_⟩
          change ¬ bad i
          exact hprev
        · intro j hj₀ hj₁
          have : j = i + 1 := by omega
          simpa [this] using hi

/-- Every bad grid point belongs to one of the maximal bad runs. -/
theorem exists_maximalBadRun_containing {N i : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] (hiN : i < N) (hi : bad i) :
    ∃ a b, IsMaximalBadRun N bad a b ∧ a ≤ i ∧ i ≤ b := by
  obtain ⟨a, hai, hastart, harun⟩ := exists_runStart_le hiN hi
  let P : ℕ → Prop := fun b ↦
    b < N ∧ ∀ j ∈ Finset.range N, a ≤ j → j ≤ b → bad j
  let _ : DecidablePred P := fun _ ↦ inferInstance
  have hi_bound : i ≤ N - 1 := by omega
  have hPi : P i := by
    refine ⟨hiN, ?_⟩
    intro j hjN haj hji
    exact harun j haj hji
  let b := Nat.findGreatest P (N - 1)
  have hib : i ≤ b := by
    exact Nat.le_findGreatest hi_bound hPi
  have hPb : P b := by
    exact Nat.findGreatest_spec hi_bound hPi
  have hright : b + 1 = N ∨ ¬ bad (b + 1) := by
    by_cases heq : b + 1 = N
    · exact Or.inl heq
    · right
      intro hbad
      have hsuccN : b + 1 < N := by omega
      have hsuccBound : b + 1 ≤ N - 1 := by omega
      have hPsucc : P (b + 1) := by
        refine ⟨hsuccN, ?_⟩
        intro j hjN haj hjb
        by_cases hj : j = b + 1
        · simpa [hj] using hbad
        · exact hPb.2 j hjN haj (by omega)
      exact (Nat.findGreatest_is_greatest (P := P) (n := N - 1)
        (k := b + 1) (Nat.lt_succ_self b) hsuccBound) hPsucc
  refine ⟨a, b, ?_, hai, hib⟩
  refine ⟨hai.trans hib, hPb.1, hPb.2, ?_, hright⟩
  exact (mem_runStarts.mp hastart).2.2

theorem exists_mem_maximalBadRuns_containing {N i : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] (hiN : i < N) (hi : bad i) :
    ∃ I ∈ maximalBadRuns N bad, I.1 ≤ i ∧ i ≤ I.2 := by
  obtain ⟨a, b, hab, hai, hib⟩ := exists_maximalBadRun_containing hiN hi
  exact ⟨(a, b), mem_maximalBadRuns.mpr hab, hai, hib⟩

/-! ## Turning changes into level roots -/

/-- A continuous function which lies strictly on one side of a level at one
endpoint and weakly on the other side at the other endpoint attains the level
inside the interval.  Applying this to `fun x ↦ |f x|` is the analytic input
needed for grid-change counting. -/
theorem exists_level_between {f : ℝ → ℝ} (hf : Continuous f)
    {x y level : ℝ} (hxy : x ≤ y)
    (hcross : (f x < level ∧ level ≤ f y) ∨
      (f y < level ∧ level ≤ f x)) :
    ∃ u ∈ Icc x y, f u = level := by
  rcases hcross with h | h
  · rcases intermediate_value_Icc hxy hf.continuousOn ⟨h.1.le, h.2⟩ with ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rcases intermediate_value_Icc' hxy hf.continuousOn ⟨h.1.le, h.2⟩ with ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

theorem exists_abs_level_between {f : ℝ → ℝ} (hf : Continuous f)
    {x y level : ℝ} (hxy : x ≤ y)
    (hcross : (|f x| < level ∧ level ≤ |f y|) ∨
      (|f y| < level ∧ level ≤ |f x|)) :
    ∃ u ∈ Icc x y, |f u| = level :=
  exists_level_between hf.abs hxy hcross

end Intervals

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/GaussianWalk.lean` -/

section
/-!
# Gaussian and finite-walk concentration tools for Erdős Problem 228

The Lovett--Meka part of the flat-polynomial construction repeatedly uses
Gaussian increments, independent signs, and a martingale tail estimate.  This
file records the corresponding interfaces in the form already supported by
Mathlib's sub-Gaussian moment-generating-function API.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace GaussianWalk

/-! ## A reusable two-sided Chernoff bound -/

/-! ## Centered Gaussian variables -/

/-! ## Symmetric signs and their finite product -/

/-- The symmetric probability measure supported on `{-1, 1}`. -/
noncomputable def rademacherMeasure : Measure ℝ :=
  bernoulliMeasure 1 (-1) ⟨1 / 2, by norm_num⟩

noncomputable instance instIsProbabilityMeasureRademacher :
    IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

theorem integral_id_rademacherMeasure :
    ∫ x, x ∂rademacherMeasure = 0 := by
  rw [rademacherMeasure, integral_bernoulliMeasure]
  norm_num

theorem ae_mem_Icc_rademacherMeasure :
    ∀ᵐ x ∂rademacherMeasure, x ∈ Icc (-1 : ℝ) 1 := by
  rw [rademacherMeasure, bernoulliMeasure_def]
  simp only [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff measurableSet_Icc).2 (by norm_num)
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff measurableSet_Icc).2 (by norm_num)

/-- A symmetric sign is sub-Gaussian with variance proxy one. -/
theorem hasSubgaussianMGF_id_rademacherMeasure :
    HasSubgaussianMGF id 1 rademacherMeasure := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := rademacherMeasure) (X := id) measurable_id.aemeasurable
    ae_mem_Icc_rademacherMeasure integral_id_rademacherMeasure
  have hc : ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2) = (1 : ℝ≥0) := by
    norm_num
  rw [hc] at h
  exact h

/-- A Rademacher variable has absolute value one almost surely. -/
theorem ae_abs_eq_one_rademacherMeasure :
    ∀ᵐ x ∂rademacherMeasure, |x| = 1 := by
  have hmeas : MeasurableSet {x : ℝ | |x| = 1} :=
    measurable_abs (measurableSet_singleton 1)
  rw [rademacherMeasure, bernoulliMeasure_def]
  simp only [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff hmeas).2 (by norm_num)
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff hmeas).2 (by norm_num)

/-- Product law for a finite family of independent symmetric signs. -/
noncomputable def rademacherProduct (iota : Type*) [Fintype iota] :
    Measure (iota → ℝ) :=
  Measure.pi fun _ : iota ↦ rademacherMeasure

noncomputable instance instIsProbabilityMeasureRademacherProduct
    (iota : Type*) [Fintype iota] :
    IsProbabilityMeasure (rademacherProduct iota) := by
  unfold rademacherProduct
  infer_instance

/-- Coordinate maps on the finite sign product are independent. -/
theorem iIndepFun_rademacherProduct
    (iota : Type*) [Fintype iota] :
    iIndepFun (fun i : iota ↦ fun omega : iota → ℝ ↦ omega i)
      (rademacherProduct iota) := by
  unfold rademacherProduct
  exact iIndepFun_pi fun _ ↦ measurable_id.aemeasurable

/-- Almost every point of the product space is an actual sign vector. -/
theorem ae_forall_abs_eq_one_rademacherProduct
    (iota : Type*) [Fintype iota] :
    ∀ᵐ omega ∂rademacherProduct iota, ∀ i, |omega i| = 1 := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (μ := fun _ : iota ↦ rademacherMeasure) i)
    |>.quasiMeasurePreserving.tendsto_ae ae_abs_eq_one_rademacherMeasure

/-- Each coordinate of the finite product is a sub-Gaussian sign. -/
theorem hasSubgaussianMGF_rademacherCoord
    (iota : Type*) [Fintype iota] (i : iota) :
    HasSubgaussianMGF (fun omega : iota → ℝ ↦ omega i) 1
      (rademacherProduct iota) := by
  refine HasSubgaussianMGF.of_map (μ := rademacherProduct iota) (X := id)
    (Y := fun omega : iota → ℝ ↦ omega i)
    (measurable_pi_apply i).aemeasurable ?_
  have hmap : (rademacherProduct iota).map (fun omega : iota → ℝ ↦ omega i) =
      rademacherMeasure := by
    unfold rademacherProduct
    exact (measurePreserving_eval (μ := fun _ : iota ↦ rademacherMeasure) i).map_eq
  rw [hmap]
  exact hasSubgaussianMGF_id_rademacherMeasure

/-- Weighted coordinates remain independent. -/
theorem iIndepFun_weightedRademacher
    (iota : Type*) [Fintype iota] (a : iota → ℝ) :
    iIndepFun (fun i : iota ↦ fun omega : iota → ℝ ↦ a i * omega i)
      (rademacherProduct iota) := by
  have h := (iIndepFun_rademacherProduct iota).comp
    (fun i x ↦ a i * x) (fun i ↦ measurable_const.mul measurable_id)
  simpa [Function.comp_def] using h

/-- A finite weighted Rademacher sum has variance proxy `sum a_i^2`. -/
theorem hasSubgaussianMGF_weightedRademacherSum
    (iota : Type*) [Fintype iota] (a : iota → ℝ) :
    HasSubgaussianMGF
      (fun omega : iota → ℝ ↦ ∑ i, a i * omega i)
      (∑ i, ⟨a i ^ 2, sq_nonneg (a i)⟩)
      (rademacherProduct iota) := by
  apply HasSubgaussianMGF.sum_of_iIndepFun
    (iIndepFun_weightedRademacher iota a) (s := Finset.univ)
  intro i hi
  have h := (hasSubgaussianMGF_rademacherCoord iota i).const_mul (a i)
  have hc : (⟨a i ^ 2, sq_nonneg (a i)⟩ : ℝ≥0) * 1 =
      ⟨a i ^ 2, sq_nonneg (a i)⟩ := mul_one _
  exact hc ▸ h

/-! ## Finite martingale sums -/

/-- Partial sums, with the convention that the zeroth sum is zero. -/
def partialSum {Omega : Type*} (Y : ℕ → Omega → ℝ) (n : ℕ) (omega : Omega) : ℝ :=
  ∑ i ∈ Finset.range n, Y i omega

@[simp]
theorem partialSum_zero {Omega : Type*} (Y : ℕ → Omega → ℝ) :
    partialSum Y 0 = 0 := by
  funext omega
  simp [partialSum]

end GaussianWalk

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/Martingale.lean` -/

section
/-!
# Conditional-Gaussian finite walks for Erdős Problem 228

The edge-walk argument used in the Lovett--Meka partial-colouring theorem is a
finite stopped Gaussian walk.  After conditioning on the past, the projection
of its next increment onto any fixed constraint vector is a centred Gaussian;
its variance is bounded by a deterministic variance budget.  This file turns
exactly that input into the one- and two-sided tail estimates used by the
partial-colouring argument.

Mathlib already proves the hard analytic step: a sum of adapted conditionally
sub-Gaussian increments is sub-Gaussian.  The definitions below provide the
missing adapter from the conditional Gaussian MGF identity (with a possibly
random conditional variance) to Mathlib's conditional sub-Gaussian API.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace Martingale

/-! ## Exact conditional Gaussian MGF data -/

/-- `X` has, conditionally on `m`, the MGF of a centred Gaussian whose
conditional variance is `variance`.  Allowing the variance to depend on the
past is essential for a stopped Gaussian walk: after a coordinate or
constraint freezes, its conditional variance can drop to zero.

This is the precise fragment of conditional Gaussianity needed for
concentration.  It is stated using the same conditional-expectation kernel as
`HasCondSubgaussianMGF`, so no regular-conditional-distribution conversion is
needed downstream. -/
structure HasConditionalGaussianMGF
    {Omega : Type*} (m : MeasurableSpace Omega)
    {mOmega : MeasurableSpace Omega} (hm : m ≤ mOmega)
    [StandardBorelSpace Omega]
    (X : Omega → ℝ) (variance : Omega → ℝ≥0)
    (mu : Measure Omega := by volume_tac) [IsFiniteMeasure mu] : Prop where
  integrable_exp_mul :
    ∀ t : ℝ, Integrable (fun omega ↦ exp (t * X omega)) mu
  mgf_eq :
    ∀ᵐ omega ∂(mu.trim hm), ∀ t : ℝ,
      mgf X (condExpKernel mu m omega) t =
        exp (variance omega * t ^ 2 / 2)

/-! ## Finite sums -/

/-- The sum of the first `n` increments of a real-valued finite walk. -/
def partialSum {Omega : Type*} (increment : ℕ → Omega → ℝ)
    (n : ℕ) (omega : Omega) : ℝ :=
  ∑ i ∈ Finset.range n, increment i omega

@[simp]
theorem partialSum_zero {Omega : Type*} (increment : ℕ → Omega → ℝ) :
    partialSum increment 0 = 0 := by
  funext omega
  simp [partialSum]

/-! ## Tail bounds -/

/-! ## Simultaneous control of finitely many constraints -/

end Martingale

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/ProjectionWalk.lean` -/

section
/-!
# Orthogonal projections for the Lovett--Meka edge walk

At a step of the Lovett--Meka walk, two finite collections of linear
conditions have to remain fixed: coordinates which are already close to a
face of the cube, and discrepancy constraints which are already close to
their permitted boundary.  An increment is therefore chosen in the
orthogonal complement of the span of the corresponding normal vectors.

This file packages that finite-dimensional linear algebra.  The definitions
are independent of the probabilistic law used to sample an increment.  In
particular, the dimension estimates show that fewer than half as many active
constraints as ambient coordinates leave a subspace of dimension greater
than half the ambient dimension.
-/

namespace ProjectionWalk

open scoped BigOperators

noncomputable section

/-! ## A generic finite family of active normal vectors -/

variable {I K : Type*} [Fintype I]

/-- The Euclidean space in which the finite edge walk takes place. -/
abbrev WalkSpace (I : Type*) [Fintype I] := EuclideanSpace ℝ I

/-- The span of the normals of all currently active linear constraints. -/
def constraintSpan (w : K → WalkSpace I) : Submodule ℝ (WalkSpace I) :=
  Submodule.span ℝ (Set.range w)

/-- The subspace of permitted increments: every vector in it is orthogonal
to every currently active normal. -/
def incrementSubspace (w : K → WalkSpace I) : Submodule ℝ (WalkSpace I) :=
  (constraintSpan w)ᗮ

theorem normal_mem_constraintSpan (w : K → WalkSpace I) (k : K) :
    w k ∈ constraintSpan w := by
  exact Submodule.subset_span (Set.mem_range_self k)

/-- Orthogonality to the span is equivalent to orthogonality to the finite
family of generators. -/
theorem mem_incrementSubspace_iff (w : K → WalkSpace I) (x : WalkSpace I) :
    x ∈ incrementSubspace w ↔ ∀ k, inner ℝ (w k) x = 0 := by
  constructor
  · intro hx k
    exact (Submodule.mem_orthogonal (constraintSpan w) x).1 hx
      (w k) (normal_mem_constraintSpan w k)
  · intro hx
    rw [incrementSubspace, Submodule.mem_orthogonal]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        exact hx k
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
    | smul a y _ hy => rw [inner_smul_left, hy, mul_zero]

/-! ## Dimension and codimension -/

variable [Fintype K]

/-- The span of `m` active normals has dimension at most `m`, without any
linear-independence assumption. -/
theorem finrank_constraintSpan_le_card (w : K → WalkSpace I) :
    Module.finrank ℝ (constraintSpan w) ≤ Fintype.card K := by
  exact finrank_range_le_card w

omit [Fintype K] in
/-- Rank-nullity for the active span and its orthogonal complement. -/
theorem finrank_constraintSpan_add_incrementSubspace (w : K → WalkSpace I) :
    Module.finrank ℝ (constraintSpan w) +
      Module.finrank ℝ (incrementSubspace w) = Fintype.card I := by
  calc
    Module.finrank ℝ (constraintSpan w) +
        Module.finrank ℝ (incrementSubspace w) =
        Module.finrank ℝ (WalkSpace I) := by
      exact Submodule.finrank_add_finrank_orthogonal (constraintSpan w)
    _ = Fintype.card I := finrank_euclideanSpace

/-- Equivalently, at least `d-m` dimensions remain when there are `m`
active normals in ambient dimension `d`. -/
theorem card_sub_card_le_finrank_incrementSubspace (w : K → WalkSpace I) :
    Fintype.card I - Fintype.card K ≤
      Module.finrank ℝ (incrementSubspace w) := by
  have hrank := finrank_constraintSpan_le_card w
  have hsum := finrank_constraintSpan_add_incrementSubspace w
  omega

/-! ## Coordinate and discrepancy constraints used by the edge walk -/

variable {J : Type*} [DecidableEq I]

/-- The standard coordinate normal. -/
def coordinateNormal (i : I) : WalkSpace I :=
  EuclideanSpace.single i 1

@[simp]
theorem inner_coordinateNormal (i : I) (x : WalkSpace I) :
    inner ℝ (coordinateNormal i) x = x i := by
  rw [coordinateNormal, EuclideanSpace.inner_single_left]
  norm_num

/-- A single indexed family containing both frozen coordinate normals and
active discrepancy normals. -/
def tightNormalFamily (v : J → WalkSpace I) (coordinates : Finset I)
    (discrepancies : Finset J) :
    Sum coordinates discrepancies → WalkSpace I
  | Sum.inl i => coordinateNormal i.1
  | Sum.inr j => v j.1

/-- The subspace of increments preserving both kinds of tight constraint. -/
def tightIncrementSubspace (v : J → WalkSpace I) (coordinates : Finset I)
    (discrepancies : Finset J) : Submodule ℝ (WalkSpace I) :=
  incrementSubspace (tightNormalFamily v coordinates discrepancies)

theorem mem_tightIncrementSubspace_iff
    (v : J → WalkSpace I) (coordinates : Finset I)
    (discrepancies : Finset J) (x : WalkSpace I) :
    x ∈ tightIncrementSubspace v coordinates discrepancies ↔
      (∀ i ∈ coordinates, x i = 0) ∧
      (∀ j ∈ discrepancies, inner ℝ (v j) x = 0) := by
  rw [tightIncrementSubspace, mem_incrementSubspace_iff]
  constructor
  · intro h
    constructor
    · intro i hi
      simpa [tightNormalFamily, inner_coordinateNormal] using
        h (Sum.inl ⟨i, hi⟩)
    · intro j hj
      simpa [tightNormalFamily] using h (Sum.inr ⟨j, hj⟩)
  · rintro ⟨hcoord, hdisc⟩ k
    cases k with
    | inl i =>
        simpa [tightNormalFamily, inner_coordinateNormal] using hcoord i.1 i.2
    | inr j =>
        simpa [tightNormalFamily] using hdisc j.1 j.2

/-- At least `d-m` dimensions remain after imposing the two kinds of active
constraint. -/
theorem card_sub_tight_card_le_finrank
    (v : J → WalkSpace I) (coordinates : Finset I)
    (discrepancies : Finset J) :
    Fintype.card I - (coordinates.card + discrepancies.card) ≤
      Module.finrank ℝ (tightIncrementSubspace v coordinates discrepancies) := by
  have h := card_sub_card_le_finrank_incrementSubspace
    (tightNormalFamily v coordinates discrepancies)
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe] at h
  exact h

end

end ProjectionWalk

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/Discrepancy.lean` -/

section
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/

/-!
# The finite discrepancy input for Erdős Problem 228

This file isolates the finite-dimensional colouring result used in Section 4
of Balister--Bollobás--Morris--Sahasrabudhe--Tiba.  Vectors are represented by
functions on a finite coordinate type.  The norm on such a function is the
supremum norm, while `l2Norm` is defined explicitly.

The elementary lemmas below are independent of the probabilistic partial
colouring argument.  In particular, `nearestSign` gives the terminal estimate
used for dimensions at most `900`, and `l2Norm_le_sqrt_card_mul_norm` is the
norm comparison used at each partial-colouring step.
-/

open scoped BigOperators

noncomputable section

namespace Discrepancy

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The coordinate dot product on a finite function space. -/
def dot (x v : I → ℝ) : ℝ := ∑ i, x i * v i

theorem dot_sub_left (x y v : I → ℝ) :
    dot (x - y) v = dot x v - dot y v := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- Membership in the closed coordinate cube `[-1,1]^I`. -/
def InCube (x : I → ℝ) : Prop := ∀ i, |x i| ≤ 1

/-- A vertex of the coordinate cube. -/
def IsSign (x : I → ℝ) : Prop := ∀ i, x i = 1 ∨ x i = -1

/-- The Euclidean norm, kept separate from the supremum norm on functions. -/
def l2Norm (v : I → ℝ) : ℝ := Real.sqrt (∑ i, (v i) ^ 2)

/-- Regard an ordinary coordinate function as the corresponding Euclidean
vector used by the projected Gaussian walk. -/
def toWalkSpace (x : I → ℝ) : ProjectionWalk.WalkSpace I :=
  WithLp.toLp 2 x

@[simp] theorem toWalkSpace_apply (x : I → ℝ) (i : I) :
    toWalkSpace x i = x i := rfl

/-- The explicit Euclidean norm agrees with the norm of the bundled walk
space. -/
theorem norm_toWalkSpace (v : I → ℝ) : ‖toWalkSpace v‖ = l2Norm v := by
  rw [EuclideanSpace.norm_eq]
  simp only [toWalkSpace_apply, Real.norm_eq_abs, sq_abs, l2Norm]

/-- The explicit Euclidean norm vanishes exactly on the zero row.  This is
the degenerate case needed when normalized discrepancy rows are converted
back to the unnormalized formulation. -/
theorem l2Norm_eq_zero_iff (v : I → ℝ) : l2Norm v = 0 ↔ v = 0 := by
  rw [← norm_toWalkSpace, norm_eq_zero]
  constructor
  · intro h
    funext i
    have hi := congrArg (fun x : ProjectionWalk.WalkSpace I ↦ x i) h
    simpa [toWalkSpace] using hi
  · rintro rfl
    rfl

/-- A zero-length discrepancy row contributes the zero linear form. -/
theorem dot_eq_zero_of_l2Norm_eq_zero (x v : I → ℝ)
    (hv : l2Norm v = 0) : dot x v = 0 := by
  rw [(l2Norm_eq_zero_iff v).mp hv]
  simp [dot]

/-- Coordinates which have reached a face of the cube. -/
def fixedCoordinates [DecidableEq I] (x : I → ℝ) : Finset I :=
  Finset.univ.filter fun i ↦ |x i| = 1

/-- Dot product restricted to a finite set of coordinates. -/
def dotOn (F : Finset I) (x v : I → ℝ) : ℝ :=
  ∑ i ∈ F, x i * v i

/-- Restrict a vector to the coordinates in `F`. -/
def restrict (F : Finset I) (x : I → ℝ) : F → ℝ := fun i ↦ x i

/-- Restrict a vector to the coordinates outside `F`. -/
def restrictOutside [DecidableEq I] (F : Finset I) (x : I → ℝ) :
    ↥(Fᶜ : Finset I) → ℝ := fun i ↦ x i

/-- Glue vectors on a finite coordinate set and its complement. -/
def glue [DecidableEq I] (F : Finset I) (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) : I → ℝ :=
  fun i ↦ if hi : i ∈ F then xF ⟨i, hi⟩ else xOutside ⟨i, by simp [hi]⟩

section Glue

variable [DecidableEq I] (F : Finset I)

@[simp] theorem glue_apply_mem (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) {i : I} (hi : i ∈ F) :
    glue F xF xOutside i = xF ⟨i, hi⟩ := by
  simp [glue, hi]

@[simp] theorem glue_apply_not_mem (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) {i : I} (hi : i ∉ F) :
    glue F xF xOutside i = xOutside ⟨i, by simp [hi]⟩ := by
  simp [glue, hi]

@[simp] theorem restrict_glue (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) :
    restrict F (glue F xF xOutside) = xF := by
  funext i
  simp [restrict]

@[simp] theorem restrictOutside_glue (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) :
    restrictOutside F (glue F xF xOutside) = xOutside := by
  funext i
  have hi : (i : I) ∉ F := Finset.mem_compl.mp i.property
  change glue F xF xOutside i = xOutside i
  rw [glue_apply_not_mem F xF xOutside hi]

@[simp] theorem glue_restrict (x : I → ℝ) :
    glue F (restrict F x) (restrictOutside F x) = x := by
  funext i
  by_cases hi : i ∈ F <;> simp [glue, restrict, restrictOutside, hi]

theorem isSign_glue {xF : F → ℝ} {xOutside : ↥(Fᶜ : Finset I) → ℝ}
    (hF : IsSign xF) (hOutside : IsSign xOutside) :
    IsSign (glue F xF xOutside) := by
  intro i
  by_cases hi : i ∈ F
  · simpa [glue, hi] using hF ⟨i, hi⟩
  · simpa [glue, hi] using hOutside ⟨i, Finset.mem_compl.mpr hi⟩

end Glue

section RestrictedDot

variable [DecidableEq I]

theorem dot_eq_dotOn_add_dotOn_compl (F : Finset I) (x v : I → ℝ) :
    dot x v = dotOn F x v + dotOn Fᶜ x v := by
  simpa only [dot, dotOn] using
    (F.sum_add_sum_compl (fun i ↦ x i * v i)).symm

theorem dot_glue (F : Finset I) (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) (v : I → ℝ) :
    dot (glue F xF xOutside) v =
      dot xF (restrict F v) + dot xOutside (restrictOutside F v) := by
  rw [dot_eq_dotOn_add_dotOn_compl F]
  congr 1
  · rw [dotOn, dot, ← Finset.sum_attach]
    simp [glue, restrict]
  · rw [dotOn, dot, ← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro i _
    have hi : (i : I) ∉ F := Finset.mem_compl.mp i.property
    simp [glue, restrictOutside, hi]

theorem dot_restrict_add_outside (F : Finset I) (x v : I → ℝ) :
    dot x v = dot (restrict F x) (restrict F v) +
      dot (restrictOutside F x) (restrictOutside F v) := by
  simpa using dot_glue F (restrict F x) (restrictOutside F x) v

end RestrictedDot

/-- The exact conclusion of the Lovett--Meka partial-colouring theorem. -/
def HasPartialColoring [DecidableEq I]
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ) : Prop :=
  ∃ x : I → ℝ,
    InCube x ∧
      Fintype.card I ≤ 2 * (fixedCoordinates x).card ∧
      ∀ j, |dot (x - x₀) (v j)| ≤ c j * l2Norm (v j)

/-- A formulation of the Lovett--Meka theorem uniform in finite index types.
The proposition is a named interface, rather than a global assumption, so
downstream deterministic arguments can state precisely which input remains
to be established. -/
def PartialColoringPrinciple (I J : Type*)
    [Fintype I] [Fintype J] [DecidableEq I] : Prop :=
  ∀ (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ),
    InCube x₀ →
      (∀ j, 0 ≤ c j) →
      (∑ j, Real.exp (-(c j) ^ 2 / 16)) ≤ (Fintype.card I : ℝ) / 16 →
      HasPartialColoring v x₀ c

/-- The exact conclusion of the BBMST full-colouring corollary. -/
def HasFullColoring
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ) : Prop :=
  ∃ x : I → ℝ, IsSign x ∧
    ∀ j,
      |dot (x - x₀) (v j)| ≤
        (c j + 30) * Real.sqrt (Fintype.card I) * ‖v j‖

/-- Parameters fed to one Lovett--Meka step in BBMST's iteration. -/
def partialParameter (c : J → ℝ) : J → ℝ := fun j ↦ 2 * c j / 7

theorem partialParameter_nonneg {c : J → ℝ} (hc : ∀ j, 0 ≤ c j) :
    ∀ j, 0 ≤ partialParameter c j := by
  intro j
  simp only [partialParameter]
  exact div_nonneg (mul_nonneg (by norm_num) (hc j)) (by norm_num)

theorem partialParameter_exponent (c : J → ℝ) (j : J) :
    -((partialParameter c j) ^ 2) / 16 = -(c j) ^ 2 / 196 := by
  simp only [partialParameter]
  ring

theorem partialParameter_budget {c : J → ℝ}
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
      (Fintype.card I : ℝ) / 16) :
    (∑ j, Real.exp (-((partialParameter c j) ^ 2) / 16)) ≤
      (Fintype.card I : ℝ) / 16 := by
  simpa only [partialParameter_exponent] using hbudget

/-- One invocation of the partial-colouring principle with BBMST's scaled
parameters. -/
theorem partialColoring_step [DecidableEq I]
    (hLM : PartialColoringPrinciple I J)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : InCube x₀) (hc : ∀ j, 0 ≤ c j)
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
      (Fintype.card I : ℝ) / 16) :
    HasPartialColoring v x₀ (partialParameter c) := by
  exact hLM v x₀ (partialParameter c) hx₀
    (partialParameter_nonneg hc) (partialParameter_budget hbudget)

/-- The numerical inequality closing the inductive step in BBMST Corollary
4.2.  The recursive coordinate set has cardinality `⌊d/2⌋`; its new
constraint parameter is the square root appearing on the left. -/
theorem induction_constant_inequality (d : ℕ) (c : ℝ)
    (hd : 900 < d) (hc : 0 ≤ c) :
    2 * c / 7 * Real.sqrt d +
        (Real.sqrt (c ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ))) + 30) *
          Real.sqrt (d / 2 : ℕ) ≤
      (c + 30) * Real.sqrt d := by
  have he_pos_nat : 0 < d / 2 := by omega
  have he_ge_nat : 450 ≤ d / 2 := by omega
  have hd_le_nat : d ≤ 2 * (d / 2) + 1 := by omega
  have he_pos : 0 < ((d / 2 : ℕ) : ℝ) := by exact_mod_cast he_pos_nat
  have he_ge : (450 : ℝ) ≤ (d / 2 : ℕ) := by exact_mod_cast he_ge_nat
  have hd_le : (d : ℝ) ≤ 2 * (d / 2 : ℕ) + 1 := by exact_mod_cast hd_le_nat
  have hd_pos_nat : 0 < d := by omega
  have hd_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have hratio_pos : 0 < (d : ℝ) / (d / 2 : ℕ) := div_pos hd_pos he_pos
  have hratio_le : (d : ℝ) / (d / 2 : ℕ) ≤ (901 : ℝ) / 450 := by
    rw [div_le_iff₀ he_pos]
    nlinarith
  have hlog_aux : Real.log ((901 : ℝ) / 450) ≤ Real.log 2 + 1 / 900 := by
    rw [show (901 : ℝ) / 450 = 2 * (901 / 900) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    gcongr
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 901 / 900 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog : Real.log ((d : ℝ) / (d / 2 : ℕ)) ≤ (36 : ℝ) / 49 := by
    calc
      Real.log ((d : ℝ) / (d / 2 : ℕ))
          ≤ Real.log ((901 : ℝ) / 450) := Real.log_le_log hratio_pos hratio_le
      _ ≤ Real.log 2 + 1 / 900 := hlog_aux
      _ ≤ (36 : ℝ) / 49 := by
        have h := Real.log_two_lt_d9.le
        norm_num at h ⊢
        linarith
  have ha :
      Real.sqrt (c ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ))) ≤ c + 12 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have he_le_nat : 2 * (d / 2) ≤ d := by omega
  have he_le : 2 * ((d / 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast he_le_nat
  have hsqrt : Real.sqrt (d / 2 : ℕ) ≤ (71 : ℝ) / 100 * Real.sqrt d := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hsqd := Real.sq_sqrt hd_pos.le
      nlinarith
  calc
    2 * c / 7 * Real.sqrt d +
          (Real.sqrt (c ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ))) + 30) *
            Real.sqrt (d / 2 : ℕ)
        ≤ 2 * c / 7 * Real.sqrt d + (c + 42) * Real.sqrt (d / 2 : ℕ) := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_right (by linarith [ha]) (Real.sqrt_nonneg _)) _
    _ ≤ 2 * c / 7 * Real.sqrt d +
          (c + 42) * ((71 : ℝ) / 100 * Real.sqrt d) := by
          exact add_le_add_right (mul_le_mul_of_nonneg_left hsqrt (by linarith)) _
    _ = (2 * c / 7 + (c + 42) * ((71 : ℝ) / 100)) * Real.sqrt d := by ring
    _ ≤ (c + 30) * Real.sqrt d := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          nlinarith

@[simp] theorem dot_zero_left (v : I → ℝ) : dot 0 v = 0 := by
  simp [dot]

@[simp] theorem dot_zero_right (x : I → ℝ) : dot x 0 = 0 := by
  simp [dot]

theorem abs_dot_le_sum_abs_mul (x v : I → ℝ) :
    |dot x v| ≤ ∑ i, |x i| * |v i| := by
  rw [dot]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact Finset.sum_le_sum fun i _ ↦ by rw [abs_mul]

theorem abs_dot_le_card_mul_norm_of_abs_le
    {x v : I → ℝ} {a : ℝ} (ha : 0 ≤ a) (hx : ∀ i, |x i| ≤ a) :
    |dot x v| ≤ Fintype.card I * a * ‖v‖ := by
  calc
    |dot x v| ≤ ∑ i, |x i| * |v i| := abs_dot_le_sum_abs_mul x v
    _ ≤ ∑ _i : I, a * ‖v‖ := by
      refine Finset.sum_le_sum fun i _ ↦ mul_le_mul (hx i) (norm_le_pi_norm v i)
        (abs_nonneg _) ha
    _ = Fintype.card I * a * ‖v‖ := by simp [mul_assoc]

theorem sum_sq_le_card_mul_norm_sq (v : I → ℝ) :
    (∑ i, (v i) ^ 2) ≤ Fintype.card I * ‖v‖ ^ 2 := by
  calc
    (∑ i, (v i) ^ 2) ≤ ∑ _i : I, ‖v‖ ^ 2 := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hvi : |v i| ≤ ‖v‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
      rw [← sq_abs]
      nlinarith [abs_nonneg (v i), norm_nonneg v,
        mul_nonneg (sub_nonneg.mpr hvi) (add_nonneg (norm_nonneg v) (abs_nonneg (v i)))]
    _ = Fintype.card I * ‖v‖ ^ 2 := by simp

theorem l2Norm_le_sqrt_card_mul_norm (v : I → ℝ) :
    l2Norm v ≤ Real.sqrt (Fintype.card I) * ‖v‖ := by
  have hsum_nonneg : 0 ≤ ∑ i, (v i) ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hcard_nonneg : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
  have hnorm_nonneg : 0 ≤ ‖v‖ := norm_nonneg _
  rw [l2Norm, ← Real.sqrt_sq hnorm_nonneg, ← Real.sqrt_mul hcard_nonneg]
  exact Real.sqrt_le_sqrt (sum_sq_le_card_mul_norm_sq v)

/-- Round a cube point coordinatewise to its nearest sign (choosing `1` at
zero). -/
def nearestSign (x : I → ℝ) : I → ℝ :=
  fun i ↦ if 0 ≤ x i then 1 else -1

theorem nearestSign_isSign (x : I → ℝ) : IsSign (nearestSign x) := by
  intro i
  simp only [nearestSign]
  split_ifs <;> simp

theorem abs_nearestSign_sub_le_one {x : I → ℝ} (hx : InCube x) (i : I) :
    |nearestSign x i - x i| ≤ 1 := by
  have hxi := hx i
  simp only [abs_le] at hxi
  simp only [nearestSign]
  split_ifs with h
  · rw [abs_of_nonneg]
    · linarith
    · linarith
  · rw [abs_of_nonpos]
    · linarith
    · linarith

theorem nearestSign_dot_sub_le_card_mul_norm
    {x : I → ℝ} (hx : InCube x) (v : I → ℝ) :
    |dot (nearestSign x - x) v| ≤ Fintype.card I * ‖v‖ := by
  change |dot (fun i ↦ nearestSign x i - x i) v| ≤ Fintype.card I * ‖v‖
  simpa using abs_dot_le_card_mul_norm_of_abs_le (v := v) (a := 1)
    (by norm_num) (abs_nearestSign_sub_le_one hx)

theorem card_le_900_le_thirty_mul_sqrt_card
    (hcard : Fintype.card I ≤ 900) :
    (Fintype.card I : ℝ) ≤ 30 * Real.sqrt (Fintype.card I) := by
  have h0 : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
  have hsqrt : Real.sqrt (Fintype.card I) ≤ 30 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · norm_num
      exact_mod_cast hcard
  nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (Fintype.card I)]

/-- The terminal (`d ≤ 900`) case of BBMST's full-colouring induction. -/
theorem hasFullColoring_of_card_le_900
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : InCube x₀) (hc : ∀ j, 0 ≤ c j)
    (hcard : Fintype.card I ≤ 900) :
    HasFullColoring v x₀ c := by
  refine ⟨nearestSign x₀, nearestSign_isSign x₀, ?_⟩
  intro j
  have hround := nearestSign_dot_sub_le_card_mul_norm hx₀ (v j)
  have hdim := card_le_900_le_thirty_mul_sqrt_card (I := I) hcard
  calc
    |dot (nearestSign x₀ - x₀) (v j)|
        ≤ Fintype.card I * ‖v j‖ := hround
    _ ≤ 30 * Real.sqrt (Fintype.card I) * ‖v j‖ := by
      exact mul_le_mul_of_nonneg_right hdim (norm_nonneg _)
    _ ≤ (c j + 30) * Real.sqrt (Fintype.card I) * ‖v j‖ := by
      gcongr
      linarith [hc j]

end Discrepancy

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/FullColoring.lean` -/

section
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/

/-!
# From partial colourings to full colourings

This file formalizes the deterministic iteration in Corollary 4.2 of
Balister--Bollobás--Morris--Sahasrabudhe--Tiba.  The probabilistic
partial-colouring theorem is an explicit argument of the final theorem.
-/

open scoped BigOperators

noncomputable section

namespace Discrepancy

universe uI uJ

variable {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]

/-- The parameter used for the recursively coloured half of the coordinates. -/
def nextParameter (d : ℕ) (c : J → ℝ) : J → ℝ :=
  fun j ↦ Real.sqrt (c j ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ)))

omit [Fintype J] in
theorem nextParameter_nonneg (d : ℕ) (c : J → ℝ) :
    ∀ j, 0 ≤ nextParameter d c j := fun _ ↦ Real.sqrt_nonneg _

theorem half_pos {d : ℕ} (hd : 900 < d) : 0 < d / 2 := by omega

theorem half_lt {d : ℕ} (hd : 900 < d) : d / 2 < d := by omega

theorem half_ratio_one_le {d : ℕ} (hd : 900 < d) :
    (1 : ℝ) ≤ (d : ℝ) / (d / 2 : ℕ) := by
  have hq : 0 < ((d / 2 : ℕ) : ℝ) := by exact_mod_cast half_pos hd
  rw [le_div_iff₀ hq]
  norm_num
  exact_mod_cast (show d / 2 ≤ d by omega)

omit [Fintype J] in
theorem nextParameter_sq {d : ℕ} (hd : 900 < d) (c : J → ℝ) (j : J) :
    nextParameter d c j ^ 2 =
      c j ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ)) := by
  rw [nextParameter, Real.sq_sqrt]
  have hlog : 0 ≤ Real.log ((d : ℝ) / (d / 2 : ℕ)) :=
    Real.log_nonneg (half_ratio_one_le hd)
  positivity

omit [Fintype J] in
theorem nextParameter_exp_identity {d : ℕ} (hd : 900 < d)
    (c : J → ℝ) (j : J) :
    Real.exp (-(nextParameter d c j) ^ 2 / 196) =
      Real.exp (-(c j) ^ 2 / 196) * ((d / 2 : ℕ) : ℝ) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hqR : (0 : ℝ) < (d / 2 : ℕ) := by exact_mod_cast half_pos hd
  rw [nextParameter_sq hd]
  rw [show -(c j ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ))) / 196 =
      -(c j) ^ 2 / 196 - Real.log ((d : ℝ) / (d / 2 : ℕ)) by ring]
  rw [Real.exp_sub, Real.exp_log (div_pos hdR hqR)]
  field_simp

theorem nextParameter_budget {d : ℕ} (hd : 900 < d) (c : J → ℝ)
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤ (d : ℝ) / 16) :
    (∑ j, Real.exp (-(nextParameter d c j) ^ 2 / 196)) ≤
      ((d / 2 : ℕ) : ℝ) / 16 := by
  simp_rw [nextParameter_exp_identity hd]
  simp_rw [mul_div_assoc]
  rw [← Finset.sum_mul]
  have hfactor : 0 ≤ (((d / 2 : ℕ) : ℝ) / d) := by positivity
  calc
    (∑ j, Real.exp (-(c j) ^ 2 / 196)) * (((d / 2 : ℕ) : ℝ) / d)
        ≤ ((d : ℝ) / 16) * (((d / 2 : ℕ) : ℝ) / d) := by
          exact mul_le_mul_of_nonneg_right hbudget hfactor
    _ = ((d / 2 : ℕ) : ℝ) / 16 := by
      have hd0 : (d : ℝ) ≠ 0 := by positivity
      field_simp

/-- Extend a vector on the as-yet-unfixed coordinates by zero dummy
coordinates, up to exactly `q` coordinates. -/
def padVector [DecidableEq I] (F : Finset I) (q : ℕ) (v : I → ℝ) :
    Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card)) → ℝ
  | Sum.inl i => v i
  | Sum.inr _ => 0

/-- Extend a cube point on the as-yet-unfixed coordinates by zero dummy
coordinates. -/
def padPoint [DecidableEq I] (F : Finset I) (q : ℕ) (x : I → ℝ) :
    Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card)) → ℝ
  | Sum.inl i => x i
  | Sum.inr _ => 0

theorem inCube_padPoint [DecidableEq I] (F : Finset I) (q : ℕ)
    {x : I → ℝ} (hx : InCube x) : InCube (padPoint F q x) := by
  intro i
  cases i with
  | inl i => simpa [padPoint] using hx i
  | inr i => simp [padPoint]

theorem norm_padVector_le [DecidableEq I] (F : Finset I) (q : ℕ)
    (v : I → ℝ) : ‖padVector F q v‖ ≤ ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  cases i with
  | inl i => simpa [padVector] using norm_le_pi_norm v i
  | inr i => simp [padVector]

theorem card_pad [DecidableEq I] (F : Finset I) (q : ℕ)
    (hcard : Fᶜ.card ≤ q) :
    Fintype.card (Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card))) = q := by
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin,
    Nat.add_sub_of_le hcard]

theorem dot_pad_sub [DecidableEq I] (F : Finset I) (q : ℕ)
    (y : Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card)) → ℝ)
    (x v : I → ℝ) :
    dot (y - padPoint F q x) (padVector F q v) =
      dot (fun i : ↥(Fᶜ : Finset I) ↦ y (Sum.inl i) - x i)
        (restrictOutside F v) := by
  simp [dot, padPoint, padVector, restrictOutside]

theorem fixed_restrict_isSign [DecidableEq I] (x : I → ℝ) :
    IsSign (restrict (fixedCoordinates x) x) := by
  intro i
  have hi : |x i| = 1 := by
    simpa [fixedCoordinates] using i.property
  simpa [restrict] using (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hi

theorem card_compl_fixed_le_half [DecidableEq I] {x : I → ℝ}
    (hfixed : Fintype.card I ≤ 2 * (fixedCoordinates x).card) :
    (fixedCoordinates x)ᶜ.card ≤ Fintype.card I / 2 := by
  rw [Finset.card_compl]
  omega

/-- BBMST Corollary 4.2.  This is the complete deterministic iteration; its
only non-elementary input is the supplied Lovett--Meka partial-colouring
principle, explicitly quantified over every finite coordinate type used by
the recursion. -/
theorem hasFullColoring_of_partialColoringPrinciple
    (hLM : ∀ (K : Type uI) [Fintype K] [DecidableEq K],
      PartialColoringPrinciple K J)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : InCube x₀) (hc : ∀ j, 0 ≤ c j)
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
      (Fintype.card I : ℝ) / 16) :
    HasFullColoring v x₀ c := by
  classical
  generalize hdcard : Fintype.card I = d at hbudget ⊢
  induction d using Nat.strong_induction_on generalizing I c with
  | h d ih =>
      by_cases hdsmall : d ≤ 900
      · exact hasFullColoring_of_card_le_900 v x₀ c hx₀ hc
          (hdcard.trans_le hdsmall)
      · have hdlarge : 900 < d := by omega
        have hbudgetI :
            (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
              (Fintype.card I : ℝ) / 16 := by simpa [hdcard] using hbudget
        obtain ⟨x, hxCube, hxFixed, hxError⟩ :=
          partialColoring_step (hLM I) v x₀ c hx₀ hc hbudgetI
        let F : Finset I := fixedCoordinates x
        let q : ℕ := d / 2
        have hFcard : Fᶜ.card ≤ q := by
          dsimp only [F, q]
          have hhalf := card_compl_fixed_le_half hxFixed
          simpa [hdcard] using hhalf
        let K := Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card))
        let vK : J → K → ℝ := fun j ↦ padVector F q (v j)
        let xK : K → ℝ := padPoint F q x
        have hcardK : Fintype.card K = q := by
          exact card_pad F q hFcard
        have hq_lt : q < d := by
          dsimp only [q]
          exact half_lt hdlarge
        have hxK : InCube xK := inCube_padPoint F q hxCube
        have hbudgetK :
            (∑ j, Real.exp (-(nextParameter d c j) ^ 2 / 196)) ≤
              (Fintype.card K : ℝ) / 16 := by
          rw [hcardK]
          exact nextParameter_budget hdlarge c hbudget
        have hrecursive : HasFullColoring vK xK (nextParameter d c) := by
          apply ih q hq_lt (I := K) vK xK (nextParameter d c) hxK
            (nextParameter_nonneg d c) hcardK
          simpa [hcardK] using hbudgetK
        obtain ⟨yK, hyKSign, hyKError⟩ := hrecursive
        let yOutside : ↥(Fᶜ : Finset I) → ℝ := fun i ↦ yK (Sum.inl i)
        let y : I → ℝ := glue F (restrict F x) yOutside
        have hyOutsideSign : IsSign yOutside := fun i ↦ hyKSign (Sum.inl i)
        have hySign : IsSign y := by
          exact isSign_glue F (fixed_restrict_isSign x) hyOutsideSign
        refine ⟨y, hySign, ?_⟩
        intro j
        have hpartial :
            |dot (x - x₀) (v j)| ≤
              (2 * c j / 7 * Real.sqrt d) * ‖v j‖ := by
          calc
            |dot (x - x₀) (v j)|
                ≤ partialParameter c j * l2Norm (v j) := hxError j
            _ ≤ partialParameter c j *
                (Real.sqrt (Fintype.card I) * ‖v j‖) := by
                  exact mul_le_mul_of_nonneg_left
                    (l2Norm_le_sqrt_card_mul_norm (v j))
                    (partialParameter_nonneg hc j)
            _ = (2 * c j / 7 * Real.sqrt d) * ‖v j‖ := by
                  simp [partialParameter, hdcard]
                  ring
        have hvKnorm : ‖vK j‖ ≤ ‖v j‖ := norm_padVector_le F q (v j)
        have hrecursiveError :
            |dot (yK - xK) (vK j)| ≤
              ((nextParameter d c j + 30) * Real.sqrt q) * ‖v j‖ := by
          calc
            |dot (yK - xK) (vK j)|
                ≤ (nextParameter d c j + 30) *
                    Real.sqrt (Fintype.card K) * ‖vK j‖ := hyKError j
            _ = ((nextParameter d c j + 30) * Real.sqrt q) * ‖vK j‖ := by
                  rw [hcardK]
            _ ≤ ((nextParameter d c j + 30) * Real.sqrt q) * ‖v j‖ := by
                  exact mul_le_mul_of_nonneg_left hvKnorm
                    (mul_nonneg (by linarith [nextParameter_nonneg d c j])
                      (Real.sqrt_nonneg _))
        have hyxDot :
            dot (y - x) (v j) = dot (yK - xK) (vK j) := by
          calc
            dot (y - x) (v j) =
                dot (yOutside - restrictOutside F x) (restrictOutside F (v j)) := by
              change dot (glue F (restrict F x) yOutside - x) (v j) = _
              rw [dot_sub_left, dot_glue, dot_restrict_add_outside F x,
                dot_sub_left]
              ring
            _ = dot (yK - xK) (vK j) := by
              symm
              exact dot_pad_sub F q yK x (v j)
        have hyx :
            |dot (y - x) (v j)| ≤
              ((nextParameter d c j + 30) * Real.sqrt q) * ‖v j‖ := by
          rw [hyxDot]
          exact hrecursiveError
        have hsplit :
            dot (y - x₀) (v j) = dot (x - x₀) (v j) + dot (y - x) (v j) := by
          rw [dot_sub_left, dot_sub_left, dot_sub_left]
          ring
        rw [hsplit]
        calc
          |dot (x - x₀) (v j) + dot (y - x) (v j)|
              ≤ |dot (x - x₀) (v j)| + |dot (y - x) (v j)| := abs_add_le _ _
          _ ≤ (2 * c j / 7 * Real.sqrt d) * ‖v j‖ +
                ((nextParameter d c j + 30) * Real.sqrt q) * ‖v j‖ :=
              add_le_add hpartial hyx
          _ = (2 * c j / 7 * Real.sqrt d +
                (nextParameter d c j + 30) * Real.sqrt q) * ‖v j‖ := by ring
          _ ≤ ((c j + 30) * Real.sqrt d) * ‖v j‖ := by
              exact mul_le_mul_of_nonneg_right
                (by simpa [nextParameter, q] using
                  induction_constant_inequality d (c j) hdlarge (hc j))
                (norm_nonneg _)
          _ = (c j + 30) * Real.sqrt (Fintype.card I) * ‖v j‖ := by
              rw [hdcard]

end Discrepancy

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/KernelClaims.lean` -/

section
/-!
# Oscillatory and telescoping estimates for Erdős Problem 228

This file supplies the calculus estimates used in Claims 1--3 of the
odd-sine kernel argument.  The first result is the smooth form of BBMST
Lemma 5.9.  It is stated with equality of the endpoint cosines; intervals
whose lengths are integer multiples of `π / n` satisfy precisely that
hypothesis.  The remaining results isolate the finite telescoping step, so
that the geometric part of the construction only has to establish ordering
and endpoint bounds for its interval family.
-/

namespace KernelClaims

open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral

private lemma hasDerivAt_neg_cos_div (omega : ℝ) (homega : omega ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ -Real.cos (omega * y) / omega)
      (Real.sin (omega * x)) x := by
  simpa [homega] using ((hasDerivAt_const_mul omega).cos.neg.div_const omega)

/-- Smooth monotone version of BBMST Lemma 5.9.  The endpoint-cosine
hypothesis follows whenever `b - a` is an integer multiple of `π / n`.

The differentiability assumptions are exactly what is needed for the three
kernel amplitudes (`1 / sin`, `1 / sin - 1 / id`, and `1 / id`) on each
component away from their poles. -/
theorem abs_integral_mul_sin_le_of_deriv_nonneg
    {h h' : ℝ → ℝ} {a b : ℝ} {n : ℕ}
    (hn : 0 < n) (hab : a ≤ b)
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt h (h' x) x)
    (hcont : ContinuousOn h' (Icc a b))
    (hnonneg : ∀ x ∈ Icc a b, 0 ≤ h' x)
    (hcos : Real.cos ((2 * (n : ℝ)) * b) = Real.cos ((2 * (n : ℝ)) * a)) :
    |∫ x in a..b, h x * Real.sin ((2 * (n : ℝ)) * x)| ≤
      |h b - h a| / n := by
  let omega : ℝ := 2 * (n : ℝ)
  have homega : omega ≠ 0 := by
    dsimp [omega]
    positivity
  let v : ℝ → ℝ := fun x ↦ -Real.cos (omega * x) / omega
  have hvderiv : ∀ x ∈ Icc a b, HasDerivAt v (Real.sin (omega * x)) x := by
    intro x hx
    exact hasDerivAt_neg_cos_div omega homega x
  have hh'int : IntervalIntegrable h' volume a b :=
    hcont.intervalIntegrable_of_Icc hab
  have hv'int : IntervalIntegrable (fun x ↦ Real.sin (omega * x)) volume a b :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hderivU : ∀ x ∈ uIcc a b, HasDerivAt h (h' x) x := by
    simpa [uIcc_of_le hab] using hderiv
  have hvderivU : ∀ x ∈ uIcc a b, HasDerivAt v (Real.sin (omega * x)) x := by
    simpa [uIcc_of_le hab] using hvderiv
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) hderivU hvderivU hh'int hv'int
  have hhprime : (∫ x in a..b, h' x) = h b - h a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderivU hh'int
  have hdiff_nonneg : 0 ≤ h b - h a := by
    rw [← hhprime]
    exact intervalIntegral.integral_nonneg hab hnonneg
  have hv_bound (x : ℝ) : |v x| ≤ 1 / omega := by
    dsimp [v]
    rw [abs_div, abs_neg, abs_of_pos (show 0 < omega by positivity)]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)
  have hj_bound : |∫ x in a..b, h' x * v x| ≤ (h b - h a) / omega := by
    calc
      |∫ x in a..b, h' x * v x| ≤ ∫ x in a..b, |h' x * v x| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ x in a..b, h' x * (1 / omega) := by
        refine intervalIntegral.integral_mono_on hab ?_ ?_ ?_
        · exact (hh'int.mul_continuousOn
            (show ContinuousOn v (uIcc a b) from by
              simpa [uIcc_of_le hab] using
                ((Real.continuous_cos.comp
                  (continuous_const.mul continuous_id)).neg.div_const _).continuousOn)).abs
        · exact hh'int.mul_const _
        · intro x hx
          rw [abs_mul, abs_of_nonneg (hnonneg x hx)]
          exact mul_le_mul_of_nonneg_left (hv_bound x) (hnonneg x hx)
      _ = (h b - h a) / omega := by
        rw [intervalIntegral.integral_mul_const, hhprime]
        ring
  have hboundary :
      h b * v b - h a * v a =
        (Real.cos (omega * a) * (h a - h b)) / omega := by
    dsimp [v, omega] at hcos ⊢
    rw [hcos]
    ring
  change |∫ x in a..b, h x * Real.sin (omega * x)| ≤ |h b - h a| / n
  rw [hparts, hboundary]
  have hboundary_abs :
      |Real.cos (omega * a) * (h a - h b) / omega| ≤
        (h b - h a) / omega := by
    rw [abs_div, abs_mul, abs_sub_comm, abs_of_nonneg hdiff_nonneg,
      abs_of_pos (show 0 < omega by positivity)]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_left hdiff_nonneg (Real.abs_cos_le_one _)) (by positivity)
  calc
    |Real.cos (omega * a) * (h a - h b) / omega -
        ∫ x in a..b, h' x * v x| ≤
        |Real.cos (omega * a) * (h a - h b) / omega| +
          |∫ x in a..b, h' x * v x| := abs_sub _ _
    _ ≤ (h b - h a) / omega + (h b - h a) / omega :=
      add_le_add hboundary_abs hj_bound
    _ = |h b - h a| / n := by
      rw [abs_of_nonneg hdiff_nonneg]
      dsimp [omega]
      field_simp
      ring

/-- The decreasing version of the smooth oscillatory estimate. -/
theorem abs_integral_mul_sin_le_of_deriv_nonpos
    {h h' : ℝ → ℝ} {a b : ℝ} {n : ℕ}
    (hn : 0 < n) (hab : a ≤ b)
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt h (h' x) x)
    (hcont : ContinuousOn h' (Icc a b))
    (hnonpos : ∀ x ∈ Icc a b, h' x ≤ 0)
    (hcos : Real.cos ((2 * (n : ℝ)) * b) = Real.cos ((2 * (n : ℝ)) * a)) :
    |∫ x in a..b, h x * Real.sin ((2 * (n : ℝ)) * x)| ≤
      |h b - h a| / n := by
  have h := abs_integral_mul_sin_le_of_deriv_nonneg
    (h := fun x ↦ -h x) (h' := fun x ↦ -h' x) hn hab
    (fun x hx ↦ (hderiv x hx).neg) hcont.neg
    (fun x hx ↦ neg_nonneg.mpr (hnonpos x hx)) hcos
  simpa only [neg_mul, intervalIntegral.integral_neg, abs_neg, neg_sub_neg,
    abs_sub_comm] using h

/-! ## Finite telescoping bounds -/

/-- Abstract form of the telescoping estimate used for a disjoint ordered
family of intervals on one increasing branch. -/
theorem sum_interval_error_le_of_monotone_endpoints
    {m : ℕ} {A B E : ℕ → ℝ} {n : ℕ} (hn : 0 < n)
    (hlocal : ∀ k < m, E k ≤ (B k - A k) / n)
    (hchain : ∀ k < m, B k ≤ A (k + 1)) :
    ∑ k ∈ Finset.range m, E k ≤ (A m - A 0) / n := by
  calc
    ∑ k ∈ Finset.range m, E k ≤
        ∑ k ∈ Finset.range m, (B k - A k) / n := by
      exact Finset.sum_le_sum fun k hk ↦ hlocal k (Finset.mem_range.mp hk)
    _ ≤ ∑ k ∈ Finset.range m, (A (k + 1) - A k) / n := by
      refine Finset.sum_le_sum fun k hk ↦ div_le_div_of_nonneg_right ?_ (by positivity)
      exact sub_le_sub_right (hchain k (Finset.mem_range.mp hk)) _
    _ = (A m - A 0) / n := by
      rw [← Finset.sum_div]
      congr 1
      simpa using Finset.sum_range_sub A m

/-! ## Assembly of the three kernel claims -/

/-- Once Claims 1--3 bound the total kernel error by `2 / 3`, the self
interval contribution from BBMST Lemma 5.8 gives the normalized lower bound
`2 / 3` and the convenient global upper bound `5`.  This formulation keeps
the bookkeeping of the signed interval family separate from the analytic
estimates above. -/
theorem normalized_kernel_bounds {value main error : ℝ}
    (hvalue : value = main + error)
    (hmain_lower : 4 / 3 ≤ |main|)
    (hmain_upper : |main| ≤ 4)
    (herror : |error| ≤ 2 / 3) :
    2 / 3 ≤ |value| ∧ |value| ≤ 5 := by
  subst value
  constructor
  · have hreverse : |main| ≤ |main + error| + |error| := by
      calc
        |main| = |(main + error) - error| := by ring_nf
        _ ≤ |main + error| + |error| := abs_sub _ _
    linarith
  · have hforward : |main + error| ≤ |main| + |error| :=
      abs_add_le main error
    linarith

end KernelClaims

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/Rounding.lean` -/

section
/-!
# The Taylor step in the odd-sine rounding argument

This file packages the analytic part of Section 5 of the
Balister--Bollobas--Morris--Sahasrabudhe--Tiba construction.  A discrepancy
vector gives simultaneous estimates for all formal derivatives of a finite
odd sine sum at a mesh of midpoints.  Expanding at the nearest midpoint turns
those estimates into the uniform error `72 * sqrt n`.

The formal derivatives are defined through complex exponentials.  This keeps
the Taylor identity exact and makes the phase shift which alternates sine and
cosine automatic.
-/

namespace Rounding

open scoped BigOperators

noncomputable section

/-- The `j`-th positive odd frequency. -/
def oddFrequency (j : ℕ) : ℕ := 2 * j + 1

/-- The finite odd sine sum with real coefficient vector `a`. -/
def oddSineSum (n : ℕ) (a : ℕ → ℝ) (theta : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, a j * Real.sin ((oddFrequency j : ℝ) * theta)

/-- The complex formal derivative of the odd exponential sum. -/
def oddExponentialDerivative (l n : ℕ) (a : ℕ → ℝ) (theta : ℝ) : ℂ :=
  ∑ j ∈ Finset.range n, (a j : ℂ) *
    (((oddFrequency j : ℝ) : ℂ) * Complex.I) ^ l *
      Complex.exp ((((oddFrequency j : ℝ) * theta : ℝ) : ℂ) * Complex.I)

/-- The corresponding real formal derivative of the odd sine sum. -/
def oddSineDerivative (l n : ℕ) (a : ℕ → ℝ) (theta : ℝ) : ℝ :=
  (oddExponentialDerivative l n a theta).im

@[simp]
theorem oddSineDerivative_zero (n : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    oddSineDerivative 0 n a theta = oddSineSum n a theta := by
  classical
  simp only [oddSineDerivative, oddExponentialDerivative, oddSineSum, pow_zero,
    mul_one]
  change Complex.imLm
    (∑ j ∈ Finset.range n, (a j : ℂ) *
      Complex.exp ((((oddFrequency j : ℝ) * theta : ℝ) : ℂ) * Complex.I)) = _
  rw [map_sum Complex.imLm]
  apply Finset.sum_congr rfl
  intro j hj
  change ((a j : ℂ) *
    Complex.exp ((((oddFrequency j : ℝ) * theta : ℝ) : ℂ) * Complex.I)).im = _
  rw [Complex.mul_im]
  simp [Complex.exp_im]

/-- Coefficientwise `l1` estimate for every formal derivative. -/
theorem abs_oddSineDerivative_le (l n : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    |oddSineDerivative l n a theta| ≤
      ∑ j ∈ Finset.range n, |a j| * (oddFrequency j : ℝ) ^ l := by
  classical
  calc
    |oddSineDerivative l n a theta| ≤ ‖oddExponentialDerivative l n a theta‖ :=
      Complex.abs_im_le_norm _
    _ ≤ ∑ j ∈ Finset.range n,
        ‖(a j : ℂ) *
          ((((oddFrequency j : ℝ) : ℂ) * Complex.I) ^ l) *
          Complex.exp ((((oddFrequency j : ℝ) * theta : ℝ) : ℂ) * Complex.I)‖ := by
      exact norm_sum_le _ _
    _ = ∑ j ∈ Finset.range n, |a j| * (oddFrequency j : ℝ) ^ l := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul, norm_mul, norm_pow]
      have hexp :
          ‖Complex.exp ((((oddFrequency j : ℝ) * theta : ℝ) : ℂ) * Complex.I)‖ = 1 :=
        Complex.norm_exp_ofReal_mul_I _
      have hfreq : 0 ≤ (oddFrequency j : ℝ) := by positivity
      have hnormFreq : ‖((oddFrequency j : ℝ) : ℂ)‖ = (oddFrequency j : ℝ) :=
        Complex.norm_of_nonneg hfreq
      rw [hexp, mul_one, Complex.norm_mul, hnormFreq, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs]

/-- On the first `n` odd frequencies, every frequency is at most `2n`. -/
theorem oddFrequency_le_two_mul {n j : ℕ} (hj : j ∈ Finset.range n) :
    oddFrequency j ≤ 2 * n := by
  simp only [Finset.mem_range] at hj
  simp only [oddFrequency]
  omega

/-- A convenient derivative bound when all coefficients are bounded by `A`. -/
theorem abs_oddSineDerivative_le_card_mul (l n : ℕ) (a : ℕ → ℝ) (A : ℝ)
    (hA : ∀ j < n, |a j| ≤ A) (hA0 : 0 ≤ A) (theta : ℝ) :
    |oddSineDerivative l n a theta| ≤
      n * A * (2 * n : ℝ) ^ l := by
  refine (abs_oddSineDerivative_le l n a theta).trans ?_
  calc
    (∑ j ∈ Finset.range n, |a j| * (oddFrequency j : ℝ) ^ l) ≤
        ∑ _j ∈ Finset.range n, A * (2 * n : ℝ) ^ l := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j < n := Finset.mem_range.mp hj
      have hfreq : (oddFrequency j : ℝ) ≤ (2 * n : ℝ) := by
        exact_mod_cast oddFrequency_le_two_mul hj
      exact mul_le_mul (hA j hj')
        (pow_le_pow_left₀ (by positivity) hfreq l) (by positivity) hA0
    _ = n * A * (2 * n : ℝ) ^ l := by
      simp [mul_assoc]

/-! ## The midpoint mesh -/

/-! ## Exact Taylor expansion -/

/-- Taylor expansion of the finite odd exponential sum about an arbitrary
base point. -/
theorem hasSum_oddExponentialDerivative_taylor (n : ℕ) (a : ℕ → ℝ)
    (x h : ℝ) :
    HasSum (fun l : ℕ => oddExponentialDerivative l n a x * (h : ℂ) ^ l / l.factorial)
      (oddExponentialDerivative 0 n a (x + h)) := by
  classical
  have hj (j : ℕ) :
      HasSum
        (fun l : ℕ =>
          ((a j : ℂ) *
            Complex.exp ((((oddFrequency j : ℝ) * x : ℝ) : ℂ) * Complex.I)) *
            (((((oddFrequency j : ℝ) : ℂ) * Complex.I) * (h : ℂ)) ^ l /
              l.factorial))
        ((a j : ℂ) *
          Complex.exp ((((oddFrequency j : ℝ) * x : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((oddFrequency j : ℝ) : ℂ) * Complex.I * (h : ℂ))) := by
    let z : ℂ := (((oddFrequency j : ℝ) : ℂ) * Complex.I) * (h : ℂ)
    let c : ℂ := (a j : ℂ) *
      Complex.exp ((((oddFrequency j : ℝ) * x : ℝ) : ℂ) * Complex.I)
    have hz : HasSum (fun l : ℕ => z ^ l / l.factorial) (Complex.exp z) :=
      Complex.exp_eq_exp_ℂ ▸ NormedSpace.expSeries_div_hasSum_exp z
    simpa only [z, c] using hz.mul_left c
  have hsum := hasSum_sum (s := Finset.range n) (fun j _ => hj j)
  convert hsum using 1
  · funext l
    simp only [oddExponentialDerivative, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hjmem
    rw [mul_pow]
    ring
  · simp only [oddExponentialDerivative, pow_zero, mul_one]
    apply Finset.sum_congr rfl
    intro j hjmem
    rw [show ((((oddFrequency j : ℝ) * (x + h) : ℝ) : ℂ) * Complex.I) =
        ((((oddFrequency j : ℝ) * x : ℝ) : ℂ) * Complex.I) +
          (((oddFrequency j : ℝ) : ℂ) * Complex.I * (h : ℂ)) by
            push_cast; ring]
    rw [Complex.exp_add]
    ring

/-- Taylor expansion after taking imaginary parts. -/
theorem hasSum_oddSineDerivative_taylor (n : ℕ) (a : ℕ → ℝ) (x h : ℝ) :
    HasSum (fun l : ℕ => oddSineDerivative l n a x * h ^ l / l.factorial)
      (oddSineDerivative 0 n a (x + h)) := by
  have him := Complex.hasSum_im (hasSum_oddExponentialDerivative_taylor n a x h)
  convert him using 1
  · funext l
    change (oddExponentialDerivative l n a x).im * h ^ l / l.factorial =
      (oddExponentialDerivative l n a x * (h : ℂ) ^ l / l.factorial).im
    have hcomponents : ((h : ℂ) ^ l).re = h ^ l ∧ ((h : ℂ) ^ l).im = 0 := by
      induction l with
      | zero => simp
      | succ l ih =>
          rw [pow_succ, pow_succ, Complex.mul_re, Complex.mul_im]
          simp [ih.1, ih.2]
    have hpow : (h : ℂ) ^ l = ((h ^ l : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hcomponents.1, hcomponents.2]
    rw [hpow]
    rw [Complex.div_im, Complex.normSq_natCast]
    have hfac : (l.factorial : ℝ) ≠ 0 := by positivity
    field_simp [hfac, Nat.factorial_ne_zero]
    rw [Complex.mul_im, Complex.mul_re]
    norm_num
    apply Or.inl
    rw [hcomponents.2, hcomponents.1]
    ring
  · rfl

/-! ## Numerical summation -/

/-- From the quadratic term onward the sharper constant `35` is available. -/
theorem affine_le_thirty_five_mul_factorial {l : ℕ} (hl : 2 ≤ l) :
    65 + 2 * l ≤ 35 * l.factorial := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
      by_cases hl2 : l = 2
      · subst l
        norm_num
      · have hl3 : 3 ≤ l := by omega
        have hlprev : 2 ≤ l - 1 := by omega
        have hih := ih (l - 1) (by omega) hlprev
        have hfac : 1 ≤ (l - 1).factorial := Nat.factorial_pos _
        have hthree : 3 * (l - 1).factorial ≤ l * (l - 1).factorial :=
          Nat.mul_le_mul_right _ hl3
        rw [show l = (l - 1) + 1 by omega, Nat.factorial_succ]
        calc
          65 + 2 * ((l - 1) + 1) = (65 + 2 * (l - 1)) + 2 := by omega
          _ ≤ 35 * (l - 1).factorial + 2 := Nat.add_le_add_right hih 2
          _ ≤ 35 * (3 * (l - 1).factorial) := by omega
          _ ≤ 35 * (l * (l - 1).factorial) := Nat.mul_le_mul_left 35 hthree
          _ = 35 * ((l - 1 + 1) * (l - 1).factorial) := by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ l)]

/-- A coarse factorial estimate, sufficient to dominate the whole affine
exponential series by a geometric series. -/
theorem affine_le_sixty_seven_mul_factorial (l : ℕ) :
    65 + 2 * l ≤ 67 * l.factorial := by
  by_cases hl : l < 2
  · interval_cases l <;> norm_num
  · exact (affine_le_thirty_five_mul_factorial (l := l) (by omega)).trans
      (Nat.mul_le_mul_right l.factorial (by norm_num))

/-- Absolute convergence of the affine factorial series on the interval used
by the mesh argument. -/
theorem summable_affine_factorial {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) :
    Summable (fun l : ℕ => (65 + 2 * l : ℝ) * q ^ l / l.factorial) := by
  have habs : |q| < 1 := by simpa [abs_of_nonneg hq0]
  have hgeo0 : Summable (fun l : ℕ => q ^ l) :=
    summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs] using habs)
  have hgeom : Summable (fun l : ℕ => (67 : ℝ) * q ^ l) := hgeo0.mul_left 67
  apply Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_) hgeom
  have hcoef : (65 + 2 * l : ℝ) ≤ 67 * l.factorial := by
    exact_mod_cast affine_le_sixty_seven_mul_factorial l
  have hfact : (0 : ℝ) < l.factorial := by positivity
  calc
    (65 + 2 * l : ℝ) * q ^ l / l.factorial ≤
        (67 * l.factorial) * q ^ l / l.factorial := by gcongr
    _ = 67 * q ^ l := by field_simp

/-- The explicit numerical series estimate used for the rounding constant. -/
theorem tsum_affine_factorial_le_seventy_two {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 11 / 112) :
    (∑' l : ℕ, (65 + 2 * l : ℝ) * q ^ l / l.factorial) ≤ 72 := by
  have hq1 : q < 1 := by linarith
  have hs := summable_affine_factorial hq0 hq1
  rw [← hs.sum_add_tsum_nat_add 2]
  have habs : |q| < 1 := by simpa [abs_of_nonneg hq0]
  have hgeo0 : Summable (fun l : ℕ => q ^ l) :=
    summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs] using habs)
  have htailGeom : Summable (fun k : ℕ => (35 : ℝ) * q ^ (k + 2)) :=
    (hgeo0.mul_left (35 * q ^ 2)).congr
      (fun k => by rw [pow_add]; ring)
  have htail : (∑' k : ℕ,
      (65 + 2 * ((k + 2 : ℕ) : ℝ)) * q ^ (k + 2) / (k + 2).factorial) ≤
      ∑' k : ℕ, (35 : ℝ) * q ^ (k + 2) := by
    have hsTail : Summable (fun k : ℕ =>
        (65 + 2 * ((k + 2 : ℕ) : ℝ)) * q ^ (k + 2) / (k + 2).factorial) := by
      simpa only using (summable_nat_add_iff 2).2 hs
    apply Summable.tsum_le_tsum
    · intro k
      have hcoef : (65 + 2 * ((k + 2 : ℕ) : ℝ)) ≤ 35 * (k + 2).factorial := by
        exact_mod_cast affine_le_thirty_five_mul_factorial (l := k + 2) (by omega)
      have hfact : (0 : ℝ) < (k + 2).factorial := by positivity
      calc
        (65 + 2 * ((k + 2 : ℕ) : ℝ)) * q ^ (k + 2) / (k + 2).factorial ≤
            (35 * (k + 2).factorial) * q ^ (k + 2) / (k + 2).factorial := by
          gcongr
        _ = 35 * q ^ (k + 2) := by field_simp
    · exact hsTail
    · exact htailGeom
  calc
    (∑ l ∈ Finset.range 2, (65 + 2 * l : ℝ) * q ^ l / l.factorial) +
        ∑' k : ℕ, (65 + 2 * ((k + 2 : ℕ) : ℝ)) * q ^ (k + 2) /
          (k + 2).factorial ≤
        65 + 67 * q + ∑' k : ℕ, (35 : ℝ) * q ^ (k + 2) := by
      convert add_le_add_left htail (65 + 67 * q) using 1 <;>
        norm_num [Finset.sum_range_succ] <;> ring
    _ = 65 + 67 * q + 35 * q ^ 2 / (1 - q) := by
      rw [show (∑' k : ℕ, (35 : ℝ) * q ^ (k + 2)) =
          35 * q ^ 2 * ∑' k : ℕ, q ^ k by
            rw [← tsum_mul_left]
            apply tsum_congr
            intro k
            rw [pow_add]
            ring,
        tsum_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs] using habs)]
      field_simp
    _ ≤ 72 := by
      have hmono : 0 ≤ ((11 / 112 : ℝ) - q) *
          (74 - 32 * ((11 / 112 : ℝ) + q)) := by
        apply mul_nonneg
        · linarith
        · nlinarith
      have hdiv : 35 * q ^ 2 / (1 - q) ≤ 72 - (65 + 67 * q) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith

/-- Summing all derivative discrepancy estimates costs at most
`72 * sqrt n` when the scaled displacement is at most `pi/32`. -/
theorem abs_oddSineSum_le_seventy_two_sqrt
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℝ) (x theta : ℝ)
    (hnear : |theta - x| ≤ Real.pi / (64 * n))
    (hdisc : ∀ l : ℕ,
      |oddSineDerivative l n a x| ≤
        (65 + 2 * l) * Real.sqrt n * (2 * n : ℝ) ^ l) :
    |oddSineSum n a theta| ≤ 72 * Real.sqrt n := by
  let h : ℝ := theta - x
  have htheta : x + h = theta := by dsimp [h]; ring
  have hq0 : 0 ≤ |h| * (2 * n : ℝ) := mul_nonneg (abs_nonneg _) (by positivity)
  have hpi : Real.pi < 22 / 7 := by
    exact lt_of_lt_of_le Real.pi_lt_d20 (by norm_num)
  have hq : |h| * (2 * n : ℝ) ≤ 11 / 112 := by
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hnear' : |h| ≤ Real.pi / (64 * n) := hnear
    calc
      |h| * (2 * n : ℝ) ≤ (Real.pi / (64 * n)) * (2 * n) := by
        gcongr
      _ = Real.pi / 32 := by field_simp; ring
      _ ≤ 11 / 112 := by linarith
  have htaylor := hasSum_oddSineDerivative_taylor n a x h
  let q : ℝ := |h| * (2 * n : ℝ)
  have hqdef : q = |h| * (2 * n : ℝ) := rfl
  have haff : Summable
      (fun l : ℕ => (65 + 2 * l : ℝ) * q ^ l / l.factorial) :=
    summable_affine_factorial (q := q) (hqdef ▸ hq0)
      (lt_of_le_of_lt (hqdef ▸ hq) (by norm_num : (11 / 112 : ℝ) < 1))
  have hbSummable : Summable (fun l : ℕ =>
      ((65 + 2 * l) * Real.sqrt n * (2 * n : ℝ) ^ l) *
        |h| ^ l / l.factorial) := by
    refine (haff.mul_left (Real.sqrt n)).congr (fun l => ?_)
    rw [hqdef, mul_pow]
    ring
  have hTaylorBound := htaylor.norm_le_of_bounded hbSummable.hasSum (fun l => by
    have hfacabs : |(l.factorial : ℝ)| = (l.factorial : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, hfacabs]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hdisc l) (by positivity)) (by positivity))
  rw [Real.norm_eq_abs, oddSineDerivative_zero, htheta] at hTaylorBound
  calc
    |oddSineSum n a theta| ≤ ∑' l : ℕ,
        ((65 + 2 * l) * Real.sqrt n * (2 * n : ℝ) ^ l) *
          |h| ^ l / l.factorial := hTaylorBound
    _ = Real.sqrt n *
        (∑' l : ℕ, (65 + 2 * l : ℝ) * q ^ l / l.factorial) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro l
      rw [hqdef]
      rw [mul_pow]
      ring
    _ ≤ Real.sqrt n * 72 := by
      exact mul_le_mul_of_nonneg_left
        (tsum_affine_factorial_le_seventy_two (q := q) (hqdef ▸ hq0) (hqdef ▸ hq))
        (Real.sqrt_nonneg n)
    _ = 72 * Real.sqrt n := by ring

end

end Rounding

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/OddSine.lean` -/

section
/-!
# The odd-sine part of the BBMST construction

This file isolates Section 5 of Balister--Bollobas--Morris--Sahasrabudhe--
Tiba.  A suitable family of short, separated grid intervals first gets a
symmetric sign colouring.  Its odd Fourier coefficients form a point of the
cube.  A second full-colouring argument rounds that point to signs while
controlling every derivative on a finite mesh.  Taylor expansion then gives
the uniform rounding error, which is combined with the odd Dirichlet-kernel
estimate.

The geometric facts about the interval family and the aggregate output of
the three kernel claims are explicit structures.  Thus downstream files can
construct them from the dangerous intervals without hiding any analytic
hypothesis in the final polynomial theorem.
-/

namespace OddSine

open scoped BigOperators Interval
open Set

noncomputable section

/-! ## Suitable interval families and their Fourier data -/

/-- The numerical multiplier in BBMST Section 5. -/
def K : ℝ := 2 ^ 7

@[simp] theorem K_eq : K = 128 := by norm_num [K]

/-- A closed real interval represented by its ordered endpoints. -/
abbrev RealInterval := ℝ × ℝ

/-- Membership in the closed interval represented by `I`. -/
def InInterval (I : RealInterval) (theta : ℝ) : Prop :=
  theta ∈ Icc I.1 I.2

/-- The part of a suitable fourfold-symmetric family in `[0, pi / 2]`.
The remaining intervals are obtained by the reflections used in BBMST.
All geometric properties consumed by the two colouring arguments are stated
here, rather than being implicit in an enumeration. -/
structure SuitableIntervalFamily (n : ℕ) where
  base : Finset RealInterval
  ordered : ∀ I ∈ base, I.1 ≤ I.2
  /-- Suitable intervals contain at least one full `pi / n` grid cell.
  In particular their two grid endpoints are distinct.  This is the
  `a < b` hypothesis in BBMST Lemma 5.8. -/
  nondegenerate : ∀ I ∈ base, I.1 < I.2
  in_first_quadrant : ∀ I ∈ base, 0 ≤ I.1 ∧ I.2 ≤ Real.pi / 2
  grid_endpoints : ∀ I ∈ base, ∃ a b : ℤ,
    I.1 = (a : ℝ) * Real.pi / n ∧ I.2 = (b : ℝ) * Real.pi / n
  short : ∀ I ∈ base, I.2 - I.1 ≤ 6 * Real.pi / n
  separated : Set.Pairwise ((↑base : Set RealInterval))
    (fun I J ↦ ∀ x ∈ Icc I.1 I.2, ∀ y ∈ Icc J.1 J.2,
      Real.pi / n ≤ |x - y|)
  away_from_axes : ∀ I ∈ base,
    100 * Real.pi / n ≤ I.1 ∧ I.2 ≤ Real.pi / 2 - 100 * Real.pi / n

/-- The dangerous set generated by the base intervals and the three
reflections `theta ↦ -theta`, `theta ↦ pi-theta`, and
`theta ↦ pi+theta`. -/
def IsDangerous {n : ℕ} (F : SuitableIntervalFamily n) (theta : ℝ) : Prop :=
  ∃ I ∈ F.base,
    InInterval I theta ∨ InInterval I (-theta) ∨
      InInterval I (Real.pi - theta) ∨ InInterval I (theta - Real.pi)

/-- One coordinate vector in the first discrepancy problem. -/
def firstVector {n : ℕ} (F : SuitableIntervalFamily n) (j : Fin n) :
    (↑F.base : Type) → ℝ :=
  fun I ↦ 4 * K * Real.sqrt n *
    ∫ theta in I.1.1..I.1.2,
      Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * theta)

/-- The shortness of every interval gives the sup-norm estimate used in the
first colouring.  This is the unsimplified form
`24*pi*K*sqrt(n)/n`, avoiding division by `sqrt n` downstream. -/
theorem norm_firstVector_le {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) (j : Fin n) :
    ‖firstVector F j‖ ≤
      24 * K * Real.pi * Real.sqrt n / n := by
  rw [pi_norm_le_iff_of_nonneg]
  · intro I
    rw [Real.norm_eq_abs]
    simp only [firstVector, abs_mul]
    have hintegral :
        ‖∫ theta in I.1.1..I.1.2,
            Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * theta)‖ ≤
          I.1.2 - I.1.1 := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := I.1.1) (b := I.1.2) (C := (1 : ℝ))
        (f := fun theta : ℝ ↦
          Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * theta))
        (fun theta htheta ↦ by
          simpa [Real.norm_eq_abs] using
            Real.abs_sin_le_one
              ((Erdos228.Rounding.oddFrequency j : ℝ) * theta))
      simpa [abs_of_nonneg (sub_nonneg.2 (F.ordered I I.2))] using h
    have hwidth := F.short I I.2
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hK : (0 : ℝ) ≤ K := by norm_num [K]
    have hcoefficient : 0 ≤ 4 * K * Real.sqrt n := by positivity
    calc
      |4| * |K| * |Real.sqrt ↑n| *
          |∫ theta in I.1.1..I.1.2,
            Real.sin ((Erdos228.Rounding.oddFrequency ↑j : ℝ) * theta)| ≤
          (4 * K * Real.sqrt n) * (I.1.2 - I.1.1) := by
            rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
              abs_of_nonneg (by norm_num [K] : (0 : ℝ) ≤ K),
              abs_of_nonneg (Real.sqrt_nonneg _)]
            exact mul_le_mul_of_nonneg_left hintegral hcoefficient
      _ ≤ (4 * K * Real.sqrt n) * (6 * Real.pi / n) := by
            exact mul_le_mul_of_nonneg_left hwidth hcoefficient
      _ = 24 * K * Real.pi * Real.sqrt n / n := by ring
  · have hK : (0 : ℝ) ≤ K := by norm_num [K]
    positivity

/-- The target coefficient obtained from a colouring of the base intervals.
Fourfold symmetry is responsible for the factor `4`. -/
def fourierTarget {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (j : ℕ) : ℝ :=
  if _hj : j < n then
    ∑ I : (↑F.base : Type),
      alpha I * (4 * K * Real.sqrt n *
        ∫ theta in I.1.1..I.1.2,
          Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * theta))
  else 0

theorem fourierTarget_eq_dot {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (j : Fin n) :
    fourierTarget F alpha j = Erdos228.Discrepancy.dot alpha (firstVector F j) := by
  simp [fourierTarget, firstVector, Erdos228.Discrepancy.dot, j.isLt]

/-- The trigonometric polynomial with the target Fourier coefficients. -/
def targetSine {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) : ℝ :=
  Erdos228.Rounding.oddSineSum n (fourierTarget F alpha) theta

/-! ## First colouring -/

/-- The finite numerical conditions needed for the first invocation of the
full-colouring corollary.  For the BBMST family they follow from
`F.base.card ≤ gamma*n`, `gamma ≤ 2^-40`, and `F.short`. -/
structure FirstColoringAdmissible {n : ℕ}
    (F : SuitableIntervalFamily n) (c : Fin n → ℝ) : Prop where
  parameter_nonneg : ∀ j, 0 ≤ c j
  budget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
    (Fintype.card (↑F.base : Type) : ℝ) / 16
  unit_error : ∀ j,
    (c j + 30) * Real.sqrt (Fintype.card (↑F.base : Type)) *
      ‖firstVector F j‖ ≤ 1

/-- Reduce admissibility to the scalar BBMST estimate after applying the
interval-length bound. -/
theorem firstColoringAdmissible_of_numeric {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) (c : Fin n → ℝ)
    (hc : ∀ j, 0 ≤ c j)
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
      (Fintype.card (↑F.base : Type) : ℝ) / 16)
    (hscalar : ∀ j,
      (c j + 30) * Real.sqrt (Fintype.card (↑F.base : Type)) *
        (24 * K * Real.pi * Real.sqrt n / n) ≤ 1) :
    FirstColoringAdmissible F c := by
  refine ⟨hc, hbudget, ?_⟩
  intro j
  have hleft : 0 ≤
      (c j + 30) * Real.sqrt (Fintype.card (↑F.base : Type)) :=
    mul_nonneg (by linarith [hc j]) (Real.sqrt_nonneg _)
  exact (mul_le_mul_of_nonneg_left (norm_firstVector_le hn F j) hleft).trans
    (hscalar j)

/-- The first full colouring chooses the interval signs and puts every odd
Fourier target coefficient in `[-1,1]`. -/
theorem exists_intervalColoring {n : ℕ} (F : SuitableIntervalFamily n)
    (c : Fin n → ℝ) (hc : FirstColoringAdmissible F c)
    (hLM : ∀ (I : Type) [Fintype I] [DecidableEq I],
      Erdos228.Discrepancy.PartialColoringPrinciple I (Fin n)) :
    ∃ alpha : (↑F.base : Type) → ℝ,
      Erdos228.Discrepancy.IsSign alpha ∧ ∀ j < n, |fourierTarget F alpha j| ≤ 1 := by
  classical
  have hzero : Erdos228.Discrepancy.InCube (0 : (↑F.base : Type) → ℝ) := by
    intro I
    simp
  obtain ⟨alpha, halpha, herror⟩ :=
    Erdos228.Discrepancy.hasFullColoring_of_partialColoringPrinciple hLM
      (firstVector F) (0 : (↑F.base : Type) → ℝ) c hzero
      hc.parameter_nonneg hc.budget
  refine ⟨alpha, halpha, ?_⟩
  intro j hj
  let jf : Fin n := ⟨j, hj⟩
  rw [fourierTarget_eq_dot F alpha jf]
  simpa [jf] using (herror jf).trans (hc.unit_error jf)

/-! ## Aggregate odd-kernel certificate -/

/-- A decomposition of the normalized odd Dirichlet-kernel integral into
its main interval and the aggregate of Claims 1--3.  The local calculus and
telescoping estimates producing these fields live in `KernelClaims`. -/
structure KernelCertificate {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) where
  main : ℝ → ℝ
  error : ℝ → ℝ
  decomposition : ∀ theta,
    targetSine F alpha theta =
      (K * Real.sqrt n) * (main theta + error theta)
  main_lower : ∀ theta, IsDangerous F theta → 4 / 3 ≤ |main theta|
  main_upper : ∀ theta, |main theta| ≤ 4
  error_bound : ∀ theta, |error theta| ≤ 2 / 3

/-- The aggregate kernel certificate gives precisely BBMST Lemma 5.6. -/
theorem targetSine_kernel_bounds {n : ℕ} (_hn : 0 < n)
    (F : SuitableIntervalFamily n) (alpha : (↑F.base : Type) → ℝ)
    (hkernel : KernelCertificate F alpha) :
    (∀ theta, IsDangerous F theta →
      (2 * K / 3) * Real.sqrt n ≤ |targetSine F alpha theta|) ∧
    (∀ theta, |targetSine F alpha theta| ≤ 5 * K * Real.sqrt n) := by
  constructor
  · intro theta htheta
    have hnormalized := Erdos228.KernelClaims.normalized_kernel_bounds
      (value := hkernel.main theta + hkernel.error theta)
      (main := hkernel.main theta) (error := hkernel.error theta)
      (hvalue := (rfl : hkernel.main theta + hkernel.error theta =
        hkernel.main theta + hkernel.error theta))
      (hmain_lower := hkernel.main_lower theta htheta)
      (hmain_upper := hkernel.main_upper theta)
      (herror := hkernel.error_bound theta)
    rw [hkernel.decomposition theta, abs_mul]
    have hK : 0 ≤ K := by norm_num [K]
    have hfactor : 0 ≤ K * Real.sqrt n := mul_nonneg hK
      (Real.sqrt_nonneg _)
    rw [abs_of_nonneg hfactor]
    calc
      (2 * K / 3) * Real.sqrt n = (K * Real.sqrt n) * (2 / 3) := by ring
      _ ≤ (K * Real.sqrt n) * |hkernel.main theta + hkernel.error theta| :=
        mul_le_mul_of_nonneg_left hnormalized.1 hfactor
  · intro theta
    have hnormalized : |hkernel.main theta + hkernel.error theta| ≤ 5 := by
      calc
        |hkernel.main theta + hkernel.error theta| ≤
            |hkernel.main theta| + |hkernel.error theta| := abs_add_le _ _
        _ ≤ 4 + 2 / 3 :=
          add_le_add (hkernel.main_upper theta) (hkernel.error_bound theta)
        _ ≤ 5 := by norm_num
    rw [hkernel.decomposition theta, abs_mul]
    have hK : 0 ≤ K := by norm_num [K]
    have hfactor : 0 ≤ K * Real.sqrt n := mul_nonneg hK
      (Real.sqrt_nonneg _)
    rw [abs_of_nonneg hfactor]
    calc
      (K * Real.sqrt n) * |hkernel.main theta + hkernel.error theta|
          ≤ (K * Real.sqrt n) * 5 :=
        mul_le_mul_of_nonneg_left hnormalized hfactor
      _ = 5 * K * Real.sqrt n := by ring

/-! ## Second colouring and Taylor rounding -/

/-- The contribution of coefficient `j` to the `l`-th formal derivative at
`theta`. -/
def derivativeVector (n l : ℕ) (theta : ℝ) : Fin n → ℝ :=
  fun j ↦
    ((((((Erdos228.Rounding.oddFrequency j : ℝ) : ℂ) * Complex.I) ^ l) *
      Complex.exp ((((Erdos228.Rounding.oddFrequency j : ℝ) * theta : ℝ) : ℂ) *
        Complex.I))).im

/-- A finite mesh whose derivative constraints suffice for the global Taylor
estimate.  The `cover` field incorporates the elementary odd-frequency
reflections and translations which reduce an arbitrary angle to the mesh. -/
structure RoundingSetup (n : ℕ) (G : Type) [Fintype G] where
  point : G → ℝ
  parameter : G × Fin n → ℝ
  parameter_nonneg : ∀ q, 0 ≤ parameter q
  budget : (∑ q, Real.exp (-(parameter q) ^ 2 / 196)) ≤ (n : ℝ) / 16
  parameter_bound : ∀ g l, parameter (g, l) + 30 ≤ 65 + 2 * (l : ℕ)
  cover : ∀ (a : ℕ → ℝ) (theta : ℝ), ∃ g theta',
    |theta' - point g| ≤ Real.pi / (64 * n) ∧
      |Erdos228.Rounding.oddSineSum n a theta| =
        |Erdos228.Rounding.oddSineSum n a theta'|

theorem oddSineDerivative_eq_dot (n l : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    Erdos228.Rounding.oddSineDerivative l n a theta =
      Erdos228.Discrepancy.dot (fun j : Fin n ↦ a j)
        (derivativeVector n l theta) := by
  classical
  simp only [Erdos228.Rounding.oddSineDerivative,
    Erdos228.Rounding.oddExponentialDerivative,
    derivativeVector, Erdos228.Discrepancy.dot]
  change Complex.imLm
      (∑ j ∈ Finset.range n, (a j : ℂ) *
        (((Erdos228.Rounding.oddFrequency j : ℝ) : ℂ) * Complex.I) ^ l *
          Complex.exp ((((Erdos228.Rounding.oddFrequency j : ℝ) * theta : ℝ) : ℂ) *
            Complex.I)) = _
  rw [map_sum Complex.imLm]
  change (∑ j ∈ Finset.range n,
    ((a j : ℂ) *
      (((Erdos228.Rounding.oddFrequency j : ℝ) : ℂ) * Complex.I) ^ l *
        Complex.exp ((((Erdos228.Rounding.oddFrequency j : ℝ) * theta : ℝ) : ℂ) *
          Complex.I)).im) = _
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
    ((a j : ℂ) *
      (((Erdos228.Rounding.oddFrequency j : ℝ) : ℂ) * Complex.I) ^ l *
        Complex.exp ((((Erdos228.Rounding.oddFrequency j : ℝ) * theta : ℝ) : ℂ) *
          Complex.I)).im) n]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc, Complex.mul_im]
  simp

theorem norm_derivativeVector_le {n l : ℕ} (theta : ℝ) :
    ‖derivativeVector n l theta‖ ≤ (2 * n : ℝ) ^ l := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro j
  rw [Real.norm_eq_abs]
  have him := Complex.abs_im_le_norm
    ((((((Erdos228.Rounding.oddFrequency j : ℝ) : ℂ) * Complex.I) ^ l) *
      Complex.exp ((((Erdos228.Rounding.oddFrequency j : ℝ) * theta : ℝ) : ℂ) *
        Complex.I)))
  change |((((((Erdos228.Rounding.oddFrequency j : ℝ) : ℂ) * Complex.I) ^ l) *
      Complex.exp ((((Erdos228.Rounding.oddFrequency j : ℝ) * theta : ℝ) : ℂ) *
        Complex.I))).im| ≤ _
  refine him.trans ?_
  simp only [norm_mul, norm_pow, Complex.norm_I, mul_one,
      Complex.norm_exp_ofReal_mul_I]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hfreq : (Erdos228.Rounding.oddFrequency j : ℝ) ≤ 2 * n := by
    exact_mod_cast Erdos228.Rounding.oddFrequency_le_two_mul
      (Finset.mem_range.2 j.isLt)
  exact pow_le_pow_left₀ (by positivity) hfreq l

theorem oddSineSum_sub (n : ℕ) (a b : ℕ → ℝ) (theta : ℝ) :
    Erdos228.Rounding.oddSineSum n (a - b) theta =
      Erdos228.Rounding.oddSineSum n a theta -
        Erdos228.Rounding.oddSineSum n b theta := by
  classical
  simp only [Erdos228.Rounding.oddSineSum, Pi.sub_apply, sub_mul,
    Finset.sum_sub_distrib]

/-- Every odd sine sum is odd. -/
theorem oddSineSum_neg (n : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    Erdos228.Rounding.oddSineSum n a (-theta) =
      -Erdos228.Rounding.oddSineSum n a theta := by
  classical
  simp [Erdos228.Rounding.oddSineSum, mul_neg]

/-- Reflection in `pi / 2` fixes every odd sine sum. -/
theorem oddSineSum_pi_sub (n : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    Erdos228.Rounding.oddSineSum n a (Real.pi - theta) =
      Erdos228.Rounding.oddSineSum n a theta := by
  classical
  simp only [Erdos228.Rounding.oddSineSum]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  rw [mul_sub]
  have hrewrite :
      (Erdos228.Rounding.oddFrequency j : ℝ) * Real.pi -
          (Erdos228.Rounding.oddFrequency j : ℝ) * theta =
        (Erdos228.Rounding.oddFrequency j : ℕ) * Real.pi -
          (Erdos228.Rounding.oddFrequency j : ℝ) * theta := by
    norm_num
  rw [hrewrite, Real.sin_nat_mul_pi_sub]
  simp [Erdos228.Rounding.oddFrequency, pow_add]

/-- Translation by `pi` negates every odd sine sum. -/
theorem oddSineSum_add_pi (n : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    Erdos228.Rounding.oddSineSum n a (theta + Real.pi) =
      -Erdos228.Rounding.oddSineSum n a theta := by
  classical
  simp only [Erdos228.Rounding.oddSineSum, mul_add]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (Erdos228.Rounding.oddFrequency j : ℝ) * theta +
      (Erdos228.Rounding.oddFrequency j : ℝ) * Real.pi =
      (Erdos228.Rounding.oddFrequency j : ℝ) * theta +
        (Erdos228.Rounding.oddFrequency j : ℕ) * Real.pi by norm_num,
    Real.sin_add_nat_mul_pi]
  simp [Erdos228.Rounding.oddFrequency, pow_add]

/-- Absolute values of odd sine sums reduce to the first quadrant. -/
theorem exists_firstQuadrant_abs_oddSineSum_eq
    (n : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    ∃ theta' ∈ Icc (0 : ℝ) (Real.pi / 2),
      |Erdos228.Rounding.oddSineSum n a theta| =
        |Erdos228.Rounding.oddSineSum n a theta'| := by
  let x := toIcoMod Real.pi_pos 0 theta
  have hxmem : x ∈ Ico (0 : ℝ) Real.pi := by
    simpa [x] using toIcoMod_mem_Ico Real.pi_pos 0 theta
  have hperiodic : Function.Periodic
      (fun y : ℝ ↦ |Erdos228.Rounding.oddSineSum n a y|) Real.pi := by
    intro y
    change |Erdos228.Rounding.oddSineSum n a (y + Real.pi)| =
      |Erdos228.Rounding.oddSineSum n a y|
    rw [oddSineSum_add_pi n a y, abs_neg]
  have hreduce : |Erdos228.Rounding.oddSineSum n a theta| =
      |Erdos228.Rounding.oddSineSum n a x| := by
    have heq := toIcoMod_add_toIcoDiv_zsmul Real.pi_pos 0 theta
    rw [← heq]
    exact hperiodic.zsmul (toIcoDiv Real.pi_pos 0 theta) x
  by_cases hx : x ≤ Real.pi / 2
  · exact ⟨x, ⟨show (0 : ℝ) ≤ x from hxmem.1, hx⟩, hreduce⟩
  · refine ⟨Real.pi - x, ?_, ?_⟩
    · constructor
      · linarith [hxmem.2]
      · linarith
    · rw [hreduce, oddSineSum_pi_sub]

/-- The second full colouring rounds all target coefficients to signs and
costs at most `72*sqrt n` uniformly. -/
theorem exists_rounding {n : ℕ} (hn : 0 < n) {G : Type} [Fintype G]
    [DecidableEq G] (setup : RoundingSetup n G) (hat : ℕ → ℝ)
    (hhat : ∀ j < n, |hat j| ≤ 1)
    (hLM : ∀ (I : Type) [Fintype I] [DecidableEq I],
      Erdos228.Discrepancy.PartialColoringPrinciple I (G × Fin n)) :
    ∃ eps : ℕ → ℝ, (∀ j, eps j = 1 ∨ eps j = -1) ∧
      ∀ theta,
        |Erdos228.Rounding.oddSineSum n eps theta -
          Erdos228.Rounding.oddSineSum n hat theta| ≤
          72 * Real.sqrt n := by
  classical
  let x₀ : Fin n → ℝ := fun j ↦ hat j
  let v : G × Fin n → Fin n → ℝ :=
    fun q ↦ derivativeVector n q.2 (setup.point q.1)
  have hx₀ : Erdos228.Discrepancy.InCube x₀ := by
    intro j
    exact hhat j j.isLt
  have hbudget : (∑ q, Real.exp (-(setup.parameter q) ^ 2 / 196)) ≤
      (Fintype.card (Fin n) : ℝ) / 16 := by
    simpa using setup.budget
  obtain ⟨epsFin, hepsSign, hepsDisc⟩ :=
    Erdos228.Discrepancy.hasFullColoring_of_partialColoringPrinciple
      hLM v x₀ setup.parameter
      hx₀ setup.parameter_nonneg hbudget
  let eps : ℕ → ℝ := fun j ↦ if hj : j < n then epsFin ⟨j, hj⟩ else 1
  refine ⟨eps, ?_, ?_⟩
  · intro j
    by_cases hj : j < n
    · simpa [eps, hj] using hepsSign ⟨j, hj⟩
    · simp [eps, hj]
  · intro theta
    let a : ℕ → ℝ := eps - hat
    obtain ⟨g, theta', hnear, habs⟩ := setup.cover a theta
    have hdisc : ∀ l : ℕ,
        |Erdos228.Rounding.oddSineDerivative l n a (setup.point g)| ≤
          (65 + 2 * l) * Real.sqrt n * (2 * n : ℝ) ^ l := by
      intro l
      by_cases hl : l < n
      · let lf : Fin n := ⟨l, hl⟩
        have hfull := hepsDisc (g, lf)
        have hdot : Erdos228.Discrepancy.dot (epsFin - x₀) (v (g, lf)) =
            Erdos228.Rounding.oddSineDerivative l n a (setup.point g) := by
          rw [oddSineDerivative_eq_dot]
          apply congrArg (fun z : Fin n → ℝ ↦
            Erdos228.Discrepancy.dot z (derivativeVector n l (setup.point g)))
          funext j
          simp [a, eps, x₀, j.isLt]
        rw [← hdot]
        calc
          |Erdos228.Discrepancy.dot (epsFin - x₀) (v (g, lf))| ≤
              (setup.parameter (g, lf) + 30) * Real.sqrt n *
                ‖v (g, lf)‖ := by simpa [v] using hfull
          _ ≤ (65 + 2 * l) * Real.sqrt n * (2 * n : ℝ) ^ l := by
            apply mul_le_mul
            · apply mul_le_mul_of_nonneg_right (setup.parameter_bound g lf)
                (Real.sqrt_nonneg _)
            · simpa [v, lf] using
                (norm_derivativeVector_le (n := n) (l := l) (setup.point g))
            · exact norm_nonneg _
            · exact mul_nonneg (by linarith [setup.parameter_nonneg (g, lf)])
                (Real.sqrt_nonneg _)
      · have hcoeff : ∀ j < n, |a j| ≤ 2 := by
          intro j hj
          have heps : |eps j| = 1 := by
            rcases (show eps j = 1 ∨ eps j = -1 by
              simp only [eps, dif_pos hj]
              exact hepsSign ⟨j, hj⟩) with h | h <;> simp [h]
          calc
            |a j| = |eps j - hat j| := rfl
            _ ≤ |eps j| + |hat j| := abs_sub _ _
            _ ≤ 2 := by linarith [hhat j hj]
        have htrivial :=
          Erdos228.Rounding.abs_oddSineDerivative_le_card_mul l n a 2 hcoeff
          (by norm_num) (setup.point g)
        have hsqrt : 1 ≤ Real.sqrt n := by
          rw [Real.one_le_sqrt]
          exact_mod_cast hn
        have hln : n ≤ l := Nat.le_of_not_gt hl
        calc
          |Erdos228.Rounding.oddSineDerivative l n a (setup.point g)| ≤
              n * 2 * (2 * n : ℝ) ^ l := htrivial
          _ ≤ (65 + 2 * l) * Real.sqrt n * (2 * n : ℝ) ^ l := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have : (n : ℝ) ≤ l := by exact_mod_cast hln
            nlinarith
    have hround := Erdos228.Rounding.abs_oddSineSum_le_seventy_two_sqrt hn a
      (setup.point g) theta' hnear hdisc
    rw [← oddSineSum_sub] at ⊢
    rw [habs]
    exact hround

/-! ## Final odd-sine theorem -/

end

end OddSine

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/RootCount.lean` -/

section
/-!
# Root counting for finite Laurent polynomials

The frequency range `[-m,m]` is indexed by `Fin (2 * m + 1)`: index `j`
represents exponent `j - m`.  Multiplication by `z^m` turns the Laurent
polynomial into an ordinary polynomial of degree at most `2 * m`.  This file
records the resulting root bound in a form that can be applied to level sets
of real trigonometric polynomials.
-/

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/CosineConstruction.lean` -/

section
/-!
# The exceptional intervals for the Rudin--Shapiro cosine block

This file packages the finite-grid part of the cosine construction in
Balister--Bollobas--Morris--Sahasrabudhe--Tiba.  In particular, a *bad cell*
is a cell of the `pi / n` grid on which the Rudin--Shapiro cosine falls below
the required threshold, and the dangerous intervals are its maximal runs.

The definitions use closed cells.  This is convenient analytically and is
the reason that a chosen boundary contact can belong to two adjacent cells.
-/

namespace CosineConstruction

open Set
open scoped BigOperators

noncomputable section

/-- The numerator in BBMST's parameter equation
`gamma * n = 2^(t+11) + 2^t - 1`. -/
def parameterNumerator (t : ℕ) : ℕ := 2 ^ (t + 11) + 2 ^ t - 1

/-- The lower-bound constant `2^-8 gamma^(7/2)`, written without a real
power: for nonnegative `gamma`, `gamma^3 * sqrt gamma = gamma^(7/2)`. -/
def cosineDelta (gamma : ℝ) : ℝ :=
  (1 / 2 ^ 8 : ℝ) * gamma ^ 3 * Real.sqrt gamma

/-- The target lower threshold for the cosine coordinate. -/
def cosineThreshold (n : ℕ) (gamma : ℝ) : ℝ :=
  cosineDelta gamma * Real.sqrt n

/-- The arithmetic hypotheses on the parameters used in the cosine
construction.  They are kept together so downstream statements cannot
silently omit either the exact equation or the quantitative window. -/
structure Parameters (n t : ℕ) (gamma : ℝ) : Prop where
  n_pos : 0 < n
  t_odd : Odd t
  equation : gamma * n = parameterNumerator t
  gamma_lower : (1 / 2 ^ 43 : ℝ) < gamma
  gamma_upper : gamma ≤ (1 / 2 ^ 40 : ℝ)

theorem Parameters.gamma_pos {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) : 0 < gamma := by
  exact lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / 2 ^ 43) h.gamma_lower.le

theorem cosineDelta_pos {gamma : ℝ} (hgamma : 0 < gamma) :
    0 < cosineDelta gamma := by
  simp only [cosineDelta]
  positivity

theorem cosineThreshold_pos {n : ℕ} {gamma : ℝ}
    (hn : 0 < n) (hgamma : 0 < gamma) : 0 < cosineThreshold n gamma := by
  simp only [cosineThreshold]
  exact mul_pos (cosineDelta_pos hgamma) (Real.sqrt_pos.2 (by exact_mod_cast hn))

theorem Parameters.toEvenParameters {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) : EvenParameters n t gamma where
  t_odd := h.t_odd
  gamma_pos := h.gamma_pos
  gamma_le := h.gamma_upper
  equation := by simpa [parameterNumerator, evenGammaNumerator] using h.equation

theorem Parameters.scale {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) : 2 ^ (t + 3) ≤ n := by
  exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans
    h.toEvenParameters.pow_t_add_eleven_le_n

theorem Parameters.eta_pos {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) :
    0 < 2 * (evenT t : ℝ) * Real.pi / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have hTR : (0 : ℝ) < evenT t := by
    exact_mod_cast (show 0 < evenT t by simp [evenT])
  exact div_pos (mul_pos (mul_pos (by norm_num) hTR) Real.pi_pos) hnR

theorem Parameters.eta_lt {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) :
    2 * (evenT t : ℝ) * Real.pi / n < 1 / 2048 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have hTle : (2 * evenT t : ℝ) ≤ gamma * n := by
    rw [h.equation]
    exact_mod_cast (show 2 * evenT t ≤ parameterNumerator t by
      rw [parameterNumerator, two_mul_evenT]
      have hp : 0 < 2 ^ t := by positivity
      omega)
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hgam : gamma ≤ 1 / 2 ^ 40 := h.gamma_upper
  have hgamma : 0 < gamma := h.gamma_pos
  calc
    2 * (evenT t : ℝ) * Real.pi / n ≤
        (gamma * n) * Real.pi / n := by
      gcongr
    _ = gamma * Real.pi := by field_simp
    _ < gamma * 4 := by gcongr
    _ ≤ (1 / 2 ^ 40 : ℝ) * 4 := by gcongr
    _ < 1 / 2048 := by norm_num

theorem Parameters.ratio_lower {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) :
    (15 / 16 : ℝ) * (gamma * n) < 2 * evenT t := by
  rw [h.equation]
  have hnat : 15 * parameterNumerator t < 16 * (2 * evenT t) := by
    rw [parameterNumerator, evenT]
    have hp : 0 < 2 ^ t := by positivity
    rw [show 2 ^ (t + 11) = 2 ^ t * 2 ^ 11 by rw [pow_add],
      show 2 ^ (t + 10) = 2 ^ t * 2 ^ 10 by rw [pow_add]]
    norm_num
    omega
  have hreal : (15 : ℝ) * parameterNumerator t < 16 * (2 * evenT t) := by
    exact_mod_cast hnat
  norm_num at hreal ⊢
  nlinarith

private theorem sqrt_two_mul_evenT (t : ℕ) :
    Real.sqrt (2 * (evenT t : ℝ)) =
      32 * Real.sqrt (2 ^ (t + 1) : ℝ) := by
  have hpow : (2 * (evenT t : ℝ)) = (2 ^ (t + 1) : ℝ) * 32 ^ 2 := by
    norm_num [evenT, pow_add]
    ring
  rw [hpow, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ (t + 1)),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 32)]
  ring

/-- The normalized seven-cell lower bound rescales to the exact threshold
required by the final construction. -/
theorem Parameters.threshold_le_normalized_good {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) :
    cosineThreshold n gamma ≤
      Real.sqrt (2 ^ (t + 1) : ℝ) *
        (2 * (evenT t : ℝ) * Real.pi / n) ^ 3 / 128 := by
  let A : ℝ := gamma * n
  let B : ℝ := 2 * evenT t
  have hnR : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have hgamma : 0 < gamma := h.gamma_pos
  have hA : 0 < A := mul_pos hgamma hnR
  have hB : 0 < B := by
    dsimp [B]
    have hT : (0 : ℝ) < evenT t := by
      exact_mod_cast (show 0 < evenT t by simp [evenT])
    positivity
  have hratio : (15 / 16 : ℝ) * A < B := by
    simpa [A, B] using h.ratio_lower
  have hratioSq : (15 / 16 : ℝ) ^ 2 * A < B := by
    have : (15 / 16 : ℝ) ^ 2 < 15 / 16 := by norm_num
    nlinarith
  have hsqrtRatio : (15 / 16 : ℝ) * Real.sqrt A < Real.sqrt B := by
    have hsA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
    have hsB : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
    have hsA2 : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA.le
    have hsB2 : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB.le
    nlinarith
  have hcubes : (15 / 16 : ℝ) ^ 3 * A ^ 3 < B ^ 3 := by
    have hp := pow_lt_pow_left₀ hratio
      (mul_nonneg (by norm_num) hA.le) (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [mul_pow] using hp
  have hprod : (15 / 16 : ℝ) ^ 4 * (A ^ 3 * Real.sqrt A) <
      B ^ 3 * Real.sqrt B := by
    have hsApos : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
    have hrpos : (0 : ℝ) < 15 / 16 := by norm_num
    have hm := mul_lt_mul hcubes hsqrtRatio.le
      (mul_pos hrpos hsApos) (pow_nonneg hB.le 3)
    calc
      (15 / 16 : ℝ) ^ 4 * (A ^ 3 * Real.sqrt A) =
          ((15 / 16 : ℝ) ^ 3 * A ^ 3) *
            ((15 / 16 : ℝ) * Real.sqrt A) := by ring
      _ < B ^ 3 * Real.sqrt B := hm
  have hnumeric : (16 : ℝ) < 3 ^ 3 * (15 / 16 : ℝ) ^ 4 := by norm_num
  have hpiCube : (3 : ℝ) ^ 3 < Real.pi ^ 3 := by
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
  have hmain : 16 * (A ^ 3 * Real.sqrt A) <
      Real.pi ^ 3 * (B ^ 3 * Real.sqrt B) := by
    have hAprodpos : 0 < A ^ 3 * Real.sqrt A :=
      mul_pos (pow_pos hA 3) (Real.sqrt_pos.2 hA)
    have hrprodpos : 0 < (15 / 16 : ℝ) ^ 4 * (A ^ 3 * Real.sqrt A) := by
      positivity
    have hpiCubePos : 0 < Real.pi ^ 3 := pow_pos Real.pi_pos 3
    calc
      16 * (A ^ 3 * Real.sqrt A) <
          (3 ^ 3 * (15 / 16 : ℝ) ^ 4) * (A ^ 3 * Real.sqrt A) := by
        exact mul_lt_mul_of_pos_right hnumeric hAprodpos
      _ = 3 ^ 3 * ((15 / 16 : ℝ) ^ 4 * (A ^ 3 * Real.sqrt A)) := by ring
      _ < Real.pi ^ 3 * ((15 / 16 : ℝ) ^ 4 * (A ^ 3 * Real.sqrt A)) :=
        mul_lt_mul_of_pos_right hpiCube hrprodpos
      _ < Real.pi ^ 3 * (B ^ 3 * Real.sqrt B) :=
        mul_lt_mul_of_pos_left hprod hpiCubePos
  have hsqrtA : Real.sqrt A = Real.sqrt gamma * Real.sqrt n := by
    dsimp [A]
    rw [Real.sqrt_mul (le_of_lt hgamma)]
  have hsqrtB : Real.sqrt B = 32 * Real.sqrt (2 ^ (t + 1) : ℝ) := by
    simpa [B] using sqrt_two_mul_evenT t
  have hscaled :
      (1 / 256 : ℝ) * gamma ^ 3 * Real.sqrt gamma * Real.sqrt n <
        Real.sqrt (2 ^ (t + 1) : ℝ) *
          (B * Real.pi / n) ^ 3 / 128 := by
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hlhs :
        (1 / 256 : ℝ) * gamma ^ 3 * Real.sqrt gamma * Real.sqrt n =
          (16 * (A ^ 3 * Real.sqrt A)) / (4096 * n ^ 3) := by
      calc
        (1 / 256 : ℝ) * gamma ^ 3 * Real.sqrt gamma * Real.sqrt n =
            (1 / 256 : ℝ) * gamma ^ 3 *
              (Real.sqrt gamma * Real.sqrt n) := by ring
        _ = (1 / 256 : ℝ) * gamma ^ 3 * Real.sqrt A := by rw [← hsqrtA]
        _ = (16 * (A ^ 3 * Real.sqrt A)) / (4096 * n ^ 3) := by
          dsimp [A]
          field_simp [hn0]
          ring
    have hs : Real.sqrt (2 ^ (t + 1) : ℝ) = Real.sqrt B / 32 := by
      rw [hsqrtB]
      ring
    have hrhs :
        Real.sqrt (2 ^ (t + 1) : ℝ) * (B * Real.pi / n) ^ 3 / 128 =
          (Real.pi ^ 3 * (B ^ 3 * Real.sqrt B)) / (4096 * n ^ 3) := by
      rw [hs]
      field_simp [hn0]
      ring
    rw [hlhs, hrhs]
    exact div_lt_div_of_pos_right hmain (by positivity)
  norm_num [cosineThreshold, cosineDelta, B] at hscaled ⊢
  exact hscaled.le

/-! ## The normalized Rudin--Shapiro modes -/

/-- Normalizing factor for the Rudin--Shapiro energy identity. -/
def rsNormalization (t : ℕ) : ℝ := (Real.sqrt (2 ^ (t + 1) : ℝ))⁻¹

/-- The normalized `r`th formal derivative of `P_t(exp(i x/T))`.
The factor `(i/T)^r` includes the chain rule. -/
def normalizedPDerivative (r t : ℕ) (x : ℝ) : ℂ :=
  (rsNormalization t : ℂ) *
    (Complex.I / (evenT t : ℝ)) ^ r *
      ((Erdos228.Bernstein.eulerDerivative^[r]) (rudinShapiroP t)).eval
        (unitPoint (x / evenT t))

/-- The companion normalized formal derivative. -/
def normalizedQDerivative (r t : ℕ) (x : ℝ) : ℂ :=
  (rsNormalization t : ℂ) *
    (Complex.I / (evenT t : ℝ)) ^ r *
      ((Erdos228.Bernstein.eulerDerivative^[r]) (rudinShapiroQ t)).eval
        (unitPoint (x / evenT t))

/-- BBMST's normalized two-mode function. -/
def normalizedH (t : ℕ) (x : ℝ) : ℂ :=
  unitPoint x * normalizedPDerivative 0 t x +
    unitPoint (2 * x) * normalizedQDerivative 0 t x

theorem rsNormalization_pos (t : ℕ) : 0 < rsNormalization t := by
  simp only [rsNormalization]
  positivity

/-- Exact normalized energy of the two slowly varying modes. -/
theorem normalized_energy (t : ℕ) (x : ℝ) :
    ‖normalizedPDerivative 0 t x‖ ^ 2 +
      ‖normalizedQDerivative 0 t x‖ ^ 2 = 1 := by
  have henergy := rudinShapiro_energy t (norm_unitPoint (x / evenT t))
  have hEpos : (0 : ℝ) < (2 ^ (t + 1) : ℝ) := by positivity
  have hspos : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := Real.sqrt_pos.2 hEpos
  have hsquare := Real.sq_sqrt hEpos.le
  simp only [normalizedPDerivative, normalizedQDerivative, pow_zero, one_mul,
    Function.iterate_zero_apply, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (rsNormalization_pos t)]
  rw [show
    (rsNormalization t * 1 * ‖(rudinShapiroP t).eval (unitPoint (x / evenT t))‖) ^ 2 +
      (rsNormalization t * 1 * ‖(rudinShapiroQ t).eval (unitPoint (x / evenT t))‖) ^ 2 =
      rsNormalization t ^ 2 *
        (‖(rudinShapiroP t).eval (unitPoint (x / evenT t))‖ ^ 2 +
          ‖(rudinShapiroQ t).eval (unitPoint (x / evenT t))‖ ^ 2) by ring,
    henergy]
  simp only [rsNormalization]
  field_simp
  exact hsquare.symm

private theorem normalizedDerivative_bound
    (p : Polynomial ℂ) (t r : ℕ) (x : ℝ)
    (hdeg : p.natDegree ≤ 2 ^ t)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 →
      ‖p.eval z‖ ≤ Real.sqrt (2 ^ (t + 1) : ℝ)) :
    ‖(rsNormalization t : ℂ) *
        (Complex.I / (evenT t : ℝ)) ^ r *
        ((Erdos228.Bernstein.eulerDerivative^[r]) p).eval
          (unitPoint (x / evenT t))‖ ≤ (1 / 2 ^ 10 : ℝ) ^ r := by
  have heuler :=
    Erdos228.Bernstein.norm_iterate_eulerDerivative_eval_le_pow_mul_circleSup
      hdeg hcircle r (norm_unitPoint (x / evenT t))
  have hTnat : 0 < evenT t := by simp [evenT]
  have hTpos : (0 : ℝ) < evenT t := by exact_mod_cast hTnat
  have hspos : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hpowcast : ((2 ^ t : ℕ) : ℝ) / evenT t = 1 / 2 ^ 10 := by
    rw [evenT_eq_pow_mul]
    push_cast
    field_simp
    norm_num
  have hnonneg : 0 ≤ (1 / (evenT t : ℝ)) ^ r := by positivity
  calc
    ‖(rsNormalization t : ℂ) *
        (Complex.I / (evenT t : ℝ)) ^ r *
        ((Erdos228.Bernstein.eulerDerivative^[r]) p).eval
          (unitPoint (x / evenT t))‖ =
      rsNormalization t * (1 / (evenT t : ℝ)) ^ r *
        ‖((Erdos228.Bernstein.eulerDerivative^[r]) p).eval
          (unitPoint (x / evenT t))‖ := by
      rw [norm_mul, norm_mul, norm_pow, norm_div, Complex.norm_I]
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (rsNormalization_pos t), abs_of_pos hTpos, one_div]
    _ ≤ rsNormalization t * (1 / (evenT t : ℝ)) ^ r *
        (((2 ^ t : ℕ) : ℝ) ^ r * Real.sqrt (2 ^ (t + 1) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left heuler
        (mul_nonneg (rsNormalization_pos t).le hnonneg)
    _ = (((2 ^ t : ℕ) : ℝ) / evenT t) ^ r := by
      rw [rsNormalization]
      field_simp
      ring
    _ = (1 / 2 ^ 10 : ℝ) ^ r := by rw [hpowcast]

theorem norm_normalizedPDerivative_le (r t : ℕ) (x : ℝ) :
    ‖normalizedPDerivative r t x‖ ≤ (1 / 2 ^ 10 : ℝ) ^ r := by
  apply normalizedDerivative_bound (rudinShapiroP t) t r x
  · rw [natDegree_rudinShapiroP]
    exact Nat.sub_le _ _
  · intro z hz
    exact norm_eval_rudinShapiroP_le t hz

theorem norm_normalizedQDerivative_le (r t : ℕ) (x : ℝ) :
    ‖normalizedQDerivative r t x‖ ≤ (1 / 2 ^ 10 : ℝ) ^ r := by
  apply normalizedDerivative_bound (rudinShapiroQ t) t r x
  · rw [natDegree_rudinShapiroQ]
    exact Nat.sub_le _ _
  · intro z hz
    exact norm_eval_rudinShapiroQ_le t hz

/-- The normalized function rescales exactly to `evenCosine`. -/
theorem evenCosine_eq_normalizedH (t : ℕ) (theta : ℝ) :
    evenCosine t theta =
      Real.sqrt (2 ^ (t + 1) : ℝ) * (normalizedH t (2 * evenT t * theta)).re := by
  have hTnat : 0 < evenT t := by simp [evenT]
  have hT : (evenT t : ℝ) ≠ 0 := by exact_mod_cast hTnat.ne'
  have hs : Real.sqrt (2 ^ (t + 1) : ℝ) ≠ 0 := by positivity
  have hdiv : (2 * (evenT t : ℝ) * theta) / evenT t = 2 * theta := by
    field_simp [hT]
  have hphase₁ : unitPoint (2 * (evenT t : ℝ) * theta) =
      unitPoint (2 * theta) ^ evenT t := by
    simp only [unitPoint, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hphase₂ : unitPoint (2 * (2 * (evenT t : ℝ) * theta)) =
      unitPoint (2 * theta) ^ (2 * evenT t) := by
    simp only [unitPoint, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [evenCosine_eq]
  simp only [normalizedH, normalizedPDerivative, normalizedQDerivative, pow_zero,
    one_mul, mul_one, Function.iterate_zero_apply, hdiv, hphase₁, hphase₂, rsNormalization]
  rw [show
    unitPoint (2 * theta) ^ evenT t *
          ((((Real.sqrt (2 ^ (t + 1) : ℝ))⁻¹ : ℝ) : ℂ) *
            (rudinShapiroP t).eval (unitPoint (2 * theta))) +
      unitPoint (2 * theta) ^ (2 * evenT t) *
          ((((Real.sqrt (2 ^ (t + 1) : ℝ))⁻¹ : ℝ) : ℂ) *
            (rudinShapiroQ t).eval (unitPoint (2 * theta))) =
      (((Real.sqrt (2 ^ (t + 1) : ℝ))⁻¹ : ℝ) : ℂ) *
        (unitPoint (2 * theta) ^ evenT t *
            (rudinShapiroP t).eval (unitPoint (2 * theta)) +
          unitPoint (2 * theta) ^ (2 * evenT t) *
            (rudinShapiroQ t).eval (unitPoint (2 * theta))) by ring]
  simp only [Complex.mul_re, Complex.inv_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.normSq_ofReal, zero_mul, sub_zero]
  field_simp

/-! ## Symmetries of the cosine block -/

private theorem cosineBlock_coeff_im_eq_zero {t k : ℕ}
    (hk : k ∈ (cosineBlockPolynomial t).support) :
    ((cosineBlockPolynomial t).coeff k).im = 0 := by
  rw [support_cosineBlockPolynomial] at hk
  rw [mem_evenCPrime] at hk
  rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [coeff_cosineBlockPolynomial_first t j hj]
    rcases coeff_rudinShapiroP_eq_one_or_neg_one hj with h | h <;> simp [h]
  · rw [coeff_cosineBlockPolynomial_second t j hj]
    rcases coeff_rudinShapiroQ_eq_one_or_neg_one hj with h | h <;> simp [h]

/-- The cosine block is a real cosine sum over the support of its defining
polynomial. -/
theorem evenCosine_eq_sum_cos (t : ℕ) (theta : ℝ) :
    evenCosine t theta =
      ∑ k ∈ (cosineBlockPolynomial t).support,
        ((cosineBlockPolynomial t).coeff k).re * Real.cos (k * (2 * theta)) := by
  classical
  rw [evenCosine, Polynomial.eval_eq_sum, Polynomial.sum_def]
  change Complex.reLm
      (∑ k ∈ (cosineBlockPolynomial t).support,
        (cosineBlockPolynomial t).coeff k * unitPoint (2 * theta) ^ k) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hre : (unitPoint (2 * theta) ^ k).re = Real.cos (k * (2 * theta)) := by
    have h := congrArg Complex.re (Erdos228.unitPoint_pow (2 * theta) k)
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, mul_one, add_zero] using h
  change ((cosineBlockPolynomial t).coeff k * unitPoint (2 * theta) ^ k).re = _
  rw [Complex.mul_re, cosineBlock_coeff_im_eq_zero hk, zero_mul, sub_zero, hre]

@[simp] theorem evenCosine_neg (t : ℕ) (theta : ℝ) :
    evenCosine t (-theta) = evenCosine t theta := by
  classical
  rw [evenCosine_eq_sum_cos, evenCosine_eq_sum_cos]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [show (k : ℝ) * (2 * -theta) = -((k : ℝ) * (2 * theta)) by ring,
    Real.cos_neg]

@[simp] theorem evenCosine_pi_sub (t : ℕ) (theta : ℝ) :
    evenCosine t (Real.pi - theta) = evenCosine t theta := by
  classical
  rw [evenCosine_eq_sum_cos, evenCosine_eq_sum_cos]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [show (k : ℝ) * (2 * (Real.pi - theta)) =
      (k : ℝ) * (2 * Real.pi) - (k : ℝ) * (2 * theta) by ring,
    Real.cos_nat_mul_two_pi_sub]

@[simp] theorem evenCosine_sub_pi (t : ℕ) (theta : ℝ) :
    evenCosine t (theta - Real.pi) = evenCosine t theta := by
  rw [show theta - Real.pi = -(Real.pi - theta) by ring, evenCosine_neg,
    evenCosine_pi_sub]

/-! ## The seven-cell analytic lemma -/

/-- The conclusion of the Howell argument before rescaling back to the
`pi/n` grid. -/
def HasGoodCellInEverySeven (f : ℝ → ℝ) (eta : ℝ) : Prop :=
  ∀ a : ℝ, ∃ j : ℕ, j < 7 ∧
    ∀ x ∈ Icc (a + (j : ℝ) * eta) (a + ((j : ℝ) + 1) * eta),
    eta ^ 3 / 128 ≤ |f x|

/-- The complete seven-cell argument.  The four-derivative algebra supplies
`hlarge`; Bernstein supplies `hderiv`; Howell interpolation then prevents all
seven consecutive cells from containing a small value. -/
theorem hasGoodCellInEverySeven_of_derivative_bounds
    (f : ℝ → ℝ) (eta : ℝ)
    (heta : 0 < eta) (hetaSmall : eta < (1 : ℝ) / 2048)
    (hf : ContDiff ℝ 4 f)
    (hlarge : ∀ x, ∃ k : Fin 4, 1 / 4 ≤ |iteratedDeriv k f x|)
    (hderiv : ∀ r ≤ 4, ∀ x, |iteratedDeriv r f x| ≤ 18) :
    HasGoodCellInEverySeven f eta := by
  intro a
  by_contra hnone
  push_neg at hnone
  have hsample (j : Fin 7) :
      ∃ x ∈ Icc (a + (j : ℕ) * eta) (a + ((j : ℕ) + 1) * eta),
        |f x| < eta ^ 3 / 128 := by
    exact hnone (j : ℕ) j.isLt
  let sample : Fin 7 → ℝ := fun j ↦ Classical.choose (hsample j)
  have sample_mem (j : Fin 7) :
      sample j ∈ Icc (a + (j : ℕ) * eta) (a + ((j : ℕ) + 1) * eta) :=
    (Classical.choose_spec (hsample j)).1
  have sample_small (j : Fin 7) : |f (sample j)| < eta ^ 3 / 128 :=
    (Classical.choose_spec (hsample j)).2
  obtain ⟨k, hklarge⟩ := hlarge (sample 0)
  by_cases hk0 : (k : ℕ) = 0
  · have hsmall := sample_small (0 : Fin 7)
    simp only [hk0, iteratedDeriv_zero] at hklarge
    have hetaOne : eta < 1 := lt_trans hetaSmall (by norm_num)
    have hetaCube : eta ^ 3 < 1 := pow_lt_one₀ heta.le hetaOne (by norm_num)
    norm_num at hsmall hklarge
    nlinarith
  · have hk₁ : 1 ≤ (k : ℕ) := Nat.one_le_iff_ne_zero.mpr hk0
    have hk₃ : (k : ℕ) ≤ 3 := by omega
    let node : Fin ((k : ℕ) + 1) → ℝ := fun i ↦
      sample ⟨2 * (i : ℕ), by omega⟩
    have hnode_mem (i : Fin ((k : ℕ) + 1)) :
        node i ∈ Icc (a + (2 * (i : ℕ)) * eta)
          (a + (2 * (i : ℕ) + 1) * eta) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (sample_mem ⟨2 * (i : ℕ), by omega⟩)
    have hnode_mono : StrictMono node := by
      intro i j hij
      have hi := hnode_mem i
      have hj := hnode_mem j
      have hijNat : (i : ℕ) < (j : ℕ) := by exact_mod_cast hij
      dsimp only [node]
      have hgap : a + (2 * (i : ℕ) + 1) * eta <
          a + (2 * (j : ℕ)) * eta := by
        have : (2 * (i : ℕ) + 1 : ℝ) < 2 * (j : ℕ) := by exact_mod_cast (by omega)
        nlinarith
      exact hi.2.trans_lt (hgap.trans_le hj.1)
    have hnode_sep : ∀ i j, i ≠ j → eta ≤ |node i - node j| := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with hijlt | hjilt
      · have hi := hnode_mem i
        have hj := hnode_mem j
        have hijNat : (i : ℕ) < (j : ℕ) := by exact_mod_cast hijlt
        rw [abs_of_nonpos (sub_nonpos.mpr (hnode_mono hijlt).le)]
        dsimp only [node] at hi hj ⊢
        have hgap : a + (2 * (i : ℕ) + 1) * eta + eta ≤
            a + (2 * (j : ℕ)) * eta := by
          have : (2 * (i : ℕ) + 2 : ℝ) ≤ 2 * (j : ℕ) := by exact_mod_cast (by omega)
          nlinarith
        linarith [hi.2, hj.1]
      · have hi := hnode_mem i
        have hj := hnode_mem j
        have hjiNat : (j : ℕ) < (i : ℕ) := by exact_mod_cast hjilt
        rw [abs_of_nonneg (sub_nonneg.mpr (hnode_mono hjilt).le)]
        dsimp only [node] at hi hj ⊢
        have hgap : a + (2 * (j : ℕ) + 1) * eta + eta ≤
            a + (2 * (i : ℕ)) * eta := by
          have : (2 * (j : ℕ) + 2 : ℝ) ≤ 2 * (i : ℕ) := by exact_mod_cast (by omega)
          nlinarith
        linarith [hj.2, hi.1]
    have hnode_dist (i : Fin ((k : ℕ) + 1)) :
        |node i - sample 0| ≤ 7 * eta := by
      have hi := hnode_mem i
      have h0 := sample_mem (0 : Fin 7)
      have hleft : sample 0 ≤ node i := by
        by_cases hi0 : (i : ℕ) = 0
        · apply le_of_eq
          have hieq : i = 0 := Fin.ext hi0
          subst i
          apply congrArg sample
          exact Fin.ext rfl
        · have hiPos : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.mpr hi0
          have hgap : a + eta ≤ a + (2 * (i : ℕ)) * eta := by
            have : (1 : ℝ) ≤ 2 * (i : ℕ) := by exact_mod_cast (by omega)
            nlinarith
          norm_num at h0
          exact h0.2.trans (hgap.trans hi.1)
      rw [abs_of_nonneg (sub_nonneg.mpr hleft)]
      have hik : (i : ℕ) ≤ (k : ℕ) := Nat.le_of_lt_succ i.isLt
      have hupper : node i ≤ a + 7 * eta := by
        calc
          node i ≤ a + (2 * (i : ℕ) + 1) * eta := hi.2
          _ ≤ a + 7 * eta := by
            have : (2 * (i : ℕ) + 1 : ℝ) ≤ 7 := by exact_mod_cast (by omega)
            nlinarith
      norm_num at h0
      linarith [h0.1]
    have hnode_value (i : Fin ((k : ℕ) + 1)) :
        |f (node i)| ≤ eta ^ 3 / 128 := by
      have hiLe : (i : ℕ) ≤ (k : ℕ) := Nat.le_of_lt_succ i.isLt
      have hkLt : (k : ℕ) < 4 := k.isLt
      have hidx : 2 * (i : ℕ) < 7 := by omega
      exact (sample_small ⟨2 * (i : ℕ), hidx⟩).le
    have hk4 : (k : ℕ) + 1 ≤ 4 := by omega
    have hquarter := Erdos228.Interpolation.howell_lt_quarter_of_nodes
      (k : ℕ) hk₁ hk₃ f node (sample 0) eta
      (hf.of_le (by exact_mod_cast hk4)) hnode_mono heta hetaSmall hnode_sep hnode_dist
      hnode_value
      (fun x ↦ hderiv ((k : ℕ) + 1) hk4 x)
    linarith

/-- A grid cell is bad if it contains a point at which the cosine coordinate
is strictly below the desired lower threshold. -/
def BadCell (n t : ℕ) (gamma : ℝ) (i : ℕ) : Prop :=
  ∃ theta ∈ Erdos228.Intervals.gridCell n i,
    |evenCosine t theta| < cosineThreshold n gamma

noncomputable instance instDecidablePredBadCell (n t : ℕ) (gamma : ℝ) :
    DecidablePred (BadCell n t gamma) := Classical.decPred _

/-- The maximal linear runs of bad cells in the period `[0,2*pi]`.
Endpoints are cell indices, so `(a,b)` denotes the real interval from
`a*pi/n` to `(b+1)*pi/n`. -/
noncomputable def dangerousRuns (n t : ℕ) (gamma : ℝ) : Finset (ℕ × ℕ) :=
  @Erdos228.Intervals.maximalBadRuns (2 * n) (BadCell n t gamma)
    (Classical.decPred _)

@[simp] theorem mem_dangerousRuns {n t : ℕ} {gamma : ℝ} {a b : ℕ} :
    (a, b) ∈ dangerousRuns n t gamma ↔
      Erdos228.Intervals.IsMaximalBadRun (2 * n) (BadCell n t gamma) a b := by
  classical
  exact Erdos228.Intervals.mem_maximalBadRuns

/-- The real interval represented by a run of cells. -/
def runInterval (n : ℕ) (I : ℕ × ℕ) : Set ℝ :=
  Icc (Erdos228.Intervals.gridPoint n I.1)
    (Erdos228.Intervals.gridPoint n (I.2 + 1))

/-- Endpoint pair corresponding to `runInterval`. -/
def runEndpoints (n : ℕ) (I : ℕ × ℕ) : Erdos228.OddSine.RealInterval :=
  (Erdos228.Intervals.gridPoint n I.1,
    Erdos228.Intervals.gridPoint n (I.2 + 1))

/-- The dangerous runs wholly contained in the first quadrant. -/
noncomputable def firstQuadrantRuns (n t : ℕ) (gamma : ℝ) : Finset (ℕ × ℕ) :=
  (dangerousRuns n t gamma).filter fun I ↦ 2 * (I.2 + 1) ≤ n

/-- First-quadrant intervals in the representation consumed by `OddSine`. -/
noncomputable def firstQuadrantIntervals (n t : ℕ) (gamma : ℝ) :
    Finset Erdos228.OddSine.RealInterval :=
  (firstQuadrantRuns n t gamma).image (runEndpoints n)

@[simp] theorem mem_firstQuadrantRuns {n t : ℕ} {gamma : ℝ} {I : ℕ × ℕ} :
    I ∈ firstQuadrantRuns n t gamma ↔
      I ∈ dangerousRuns n t gamma ∧ 2 * (I.2 + 1) ≤ n := by
  classical
  simp [firstQuadrantRuns]

theorem runEndpoints_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (runEndpoints n) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [runEndpoints, Prod.mk.injEq] at h
  have hstrict := Erdos228.Intervals.gridPoint_strictMono hn
  have hac : a = c := hstrict.injective h.1
  have hbd : b + 1 = d + 1 := hstrict.injective h.2
  simp only [Prod.mk.injEq]
  exact ⟨hac, Nat.succ.inj hbd⟩

theorem card_firstQuadrantIntervals {n t : ℕ} {gamma : ℝ} (hn : 0 < n) :
    (firstQuadrantIntervals n t gamma).card =
      (firstQuadrantRuns n t gamma).card := by
  classical
  exact Finset.card_image_of_injective _ (runEndpoints_injective hn)

/-- The seven-cell conclusion, isolated as the exact combinatorial statement
needed to make every dangerous interval short. -/
def SevenCellProperty (n t : ℕ) (gamma : ℝ) : Prop :=
  ∀ a, a + 7 ≤ 2 * n →
    ∃ j < 7, ¬BadCell n t gamma (a + j)

/-- Rescaling the normalized good-cell conclusion produces the combinatorial
seven-cell property for the original angular grid. -/
theorem sevenCellProperty_of_normalized_good
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    (hgood : HasGoodCellInEverySeven (fun x ↦ (normalizedH t x).re)
      (2 * (evenT t : ℝ) * Real.pi / n)) :
    SevenCellProperty n t gamma := by
  intro a ha
  let eta : ℝ := 2 * (evenT t : ℝ) * Real.pi / n
  obtain ⟨j, hj, hcell⟩ := hgood (a * eta)
  refine ⟨j, hj, ?_⟩
  rintro ⟨theta, htheta, hsmall⟩
  let x : ℝ := 2 * evenT t * theta
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  have hT : (0 : ℝ) < evenT t := by
    exact_mod_cast (show 0 < evenT t by simp [evenT])
  have hx : x ∈ Icc (a * eta + (j : ℝ) * eta)
      (a * eta + ((j : ℝ) + 1) * eta) := by
    rcases htheta with ⟨hthetaL, hthetaR⟩
    simp only [Erdos228.Intervals.gridCell, Erdos228.Intervals.gridPoint] at hthetaL hthetaR
    dsimp [x, eta]
    constructor <;> push_cast at * <;>
      (field_simp [ne_of_gt hnR] at hthetaL hthetaR ⊢ <;> nlinarith [Real.pi_pos])
  have hnorm : eta ^ 3 / 128 ≤ |(normalizedH t x).re| := by
    simpa [eta] using hcell x hx
  have hsqrt : 0 ≤ Real.sqrt (2 ^ (t + 1) : ℝ) := Real.sqrt_nonneg _
  have hlower : cosineThreshold n gamma ≤
      Real.sqrt (2 ^ (t + 1) : ℝ) * |(normalizedH t x).re| := by
    calc
      cosineThreshold n gamma ≤
          Real.sqrt (2 ^ (t + 1) : ℝ) * eta ^ 3 / 128 := by
        simpa [eta] using hparam.threshold_le_normalized_good
      _ ≤ Real.sqrt (2 ^ (t + 1) : ℝ) * |(normalizedH t x).re| := by
        have := mul_le_mul_of_nonneg_left hnorm hsqrt
        nlinarith
  have heq : |evenCosine t theta| =
      Real.sqrt (2 ^ (t + 1) : ℝ) * |(normalizedH t x).re| := by
    rw [evenCosine_eq_normalizedH]
    dsimp [x]
    rw [abs_mul, abs_of_nonneg hsqrt]
  rw [← heq] at hlower
  exact (not_lt_of_ge hlower) hsmall

/-- A maximal run has at most six cells as soon as every block of seven
cells contains a good cell. -/
theorem dangerousRun_length_le_six {n t : ℕ} {gamma : ℝ}
    (hseven : SevenCellProperty n t gamma) {a b : ℕ}
    (hab : (a, b) ∈ dangerousRuns n t gamma) :
    b + 1 - a ≤ 6 := by
  classical
  rw [mem_dangerousRuns] at hab
  by_contra hlong
  have hab7 : a + 7 ≤ b + 1 := by omega
  have hbN : b < 2 * n := hab.2.1
  have ha7N : a + 7 ≤ 2 * n := by omega
  obtain ⟨j, hj, hgood⟩ := hseven a ha7N
  apply hgood
  exact hab.2.2.1 (a + j) (Finset.mem_range.mpr (by omega)) (by omega) (by omega)

/-- Consequently each represented real interval has length at most
`6*pi/n`. -/
theorem dangerousRun_width_le {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n) (hseven : SevenCellProperty n t gamma) {I : ℕ × ℕ}
    (hI : I ∈ dangerousRuns n t gamma) :
    Erdos228.Intervals.gridPoint n (I.2 + 1) -
        Erdos228.Intervals.gridPoint n I.1 ≤ 6 * Real.pi / n := by
  rcases I with ⟨a, b⟩
  have hlen := dangerousRun_length_le_six hseven hI
  simp only [Erdos228.Intervals.gridPoint]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hba : a ≤ b + 1 := by
    rw [mem_dangerousRuns] at hI
    exact hI.1.trans (Nat.le_succ b)
  have hcast : ((b + 1 - a : ℕ) : ℝ) ≤ 6 := by exact_mod_cast hlen
  rw [Nat.cast_sub hba] at hcast
  rw [← sub_div]
  apply (div_le_div_iff_of_pos_right hnR).2
  nlinarith [Real.pi_pos]

/-- Distinct maximal runs have at least one grid step between their interiors.
The statement is oriented; swapping the two runs gives the other case. -/
theorem dangerousRuns_separated {n t : ℕ} {gamma : ℝ} {a b c d : ℕ}
    (h₁ : (a, b) ∈ dangerousRuns n t gamma)
    (h₂ : (c, d) ∈ dangerousRuns n t gamma)
    (hbc : b < c) : b + 2 ≤ c := by
  classical
  rw [mem_dangerousRuns] at h₁ h₂
  by_contra h
  have hc : c = b + 1 := by omega
  have hcN : c < 2 * n := h₂.1.trans_lt h₂.2.1
  have hbadc := h₂.2.2.1 c (Finset.mem_range.mpr hcN) le_rfl h₂.1
  rcases h₁.2.2.2.2 with hright | hgood
  · rw [hc, hright] at hcN
    omega
  · exact hgood (by simpa [hc] using hbadc)

/-! ## Conversion to the odd-sine interval interface -/

/-- The remaining two geometric estimates in the exact form required by
`OddSine.SuitableIntervalFamily`.  They are separated from the elementary
grid facts because the strict metric separation and exclusion of the axes
come from the analytic large-value neighborhoods. -/
structure GeometricCertificate (n t : ℕ) (gamma : ℝ) : Prop where
  separated : Set.Pairwise
    (↑(firstQuadrantIntervals n t gamma) :
      Set Erdos228.OddSine.RealInterval)
    (fun I J ↦ ∀ x ∈ Icc I.1 I.2, ∀ y ∈ Icc J.1 J.2,
      Real.pi / n ≤ |x - y|)
  away_from_axes : ∀ I ∈ firstQuadrantIntervals n t gamma,
    100 * Real.pi / n ≤ I.1 ∧
      I.2 ≤ Real.pi / 2 - 100 * Real.pi / n

/-- The maximal first-quadrant bad runs, equipped with the analytic
separation certificate, form exactly an `OddSine.SuitableIntervalFamily`. -/
def suitableIntervalFamilyOfDangerousRuns
    {n t : ℕ} {gamma : ℝ} (hn : 0 < n)
    (hseven : SevenCellProperty n t gamma)
    (hgeom : GeometricCertificate n t gamma) :
    Erdos228.OddSine.SuitableIntervalFamily n where
  base := firstQuadrantIntervals n t gamma
  ordered := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [mem_firstQuadrantRuns] at hJ
    rcases J with ⟨a, b⟩
    simp only [runEndpoints]
    apply Erdos228.Intervals.gridPoint_mono hn
    rw [mem_dangerousRuns] at hJ
    exact Nat.le_succ_of_le hJ.1.1
  nondegenerate := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [mem_firstQuadrantRuns] at hJ
    rcases J with ⟨a, b⟩
    simp only [runEndpoints]
    apply Erdos228.Intervals.gridPoint_strictMono hn
    rw [mem_dangerousRuns] at hJ
    exact Nat.lt_succ_of_le hJ.1.1
  in_first_quadrant := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [mem_firstQuadrantRuns] at hJ
    rcases J with ⟨a, b⟩
    simp only [runEndpoints]
    constructor
    · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le)
        (Nat.cast_nonneg _)
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hidx : (2 * (b + 1) : ℝ) ≤ n := by exact_mod_cast hJ.2
      simp only [Erdos228.Intervals.gridPoint]
      norm_num [Nat.cast_add]
      apply (div_le_iff₀ hnR).2
      have hmul := mul_le_mul_of_nonneg_right hidx Real.pi_pos.le
      norm_num [Nat.cast_add] at hmul
      nlinarith
  grid_endpoints := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rcases J with ⟨a, b⟩
    exact ⟨a, b + 1, by simp [runEndpoints, Erdos228.Intervals.gridPoint],
      by simp [runEndpoints, Erdos228.Intervals.gridPoint]⟩
  short := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [mem_firstQuadrantRuns] at hJ
    simpa only [runEndpoints] using dangerousRun_width_le hn hseven hJ.1
  separated := hgeom.separated
  away_from_axes := hgeom.away_from_axes

/-- Membership in one of the first-quadrant base intervals. -/
def InBaseFamily {n : ℕ} (F : Erdos228.OddSine.SuitableIntervalFamily n)
    (theta : ℝ) : Prop :=
  ∃ I ∈ F.base, Erdos228.OddSine.InInterval I theta

/-- The four defining symmetries of `IsDangerous` extend a lower bound from
the first quadrant to the bounded fundamental interval used by the final
assembly. -/
theorem lower_on_fundamental_of_lower_off_base
    {n t : ℕ} {gamma : ℝ} (F : Erdos228.OddSine.SuitableIntervalFamily n)
    (hfirst : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      ¬InBaseFamily F theta →
        cosineThreshold n gamma ≤ |evenCosine t theta|) :
    ∀ theta ∈ Icc (-Real.pi / 2) (3 * Real.pi / 2),
      ¬Erdos228.OddSine.IsDangerous F theta →
        cosineThreshold n gamma ≤ |evenCosine t theta| := by
  intro theta htheta hout
  rcases htheta with ⟨hthetaLower, hthetaUpper⟩
  by_cases h0 : theta ≤ 0
  · have hphi : -theta ∈ Icc (0 : ℝ) (Real.pi / 2) := by
      constructor <;> linarith
    have hbase : ¬InBaseFamily F (-theta) := by
      rintro ⟨I, hI, hmem⟩
      exact hout ⟨I, hI, Or.inr (Or.inl hmem)⟩
    simpa using hfirst (-theta) hphi hbase
  · have htheta0 : 0 ≤ theta := le_of_not_ge h0
    by_cases hhalf : theta ≤ Real.pi / 2
    · exact hfirst theta ⟨htheta0, hhalf⟩ fun hbase ↦ by
        rcases hbase with ⟨I, hI, hmem⟩
        exact hout ⟨I, hI, Or.inl hmem⟩
    · have hhalf' : Real.pi / 2 ≤ theta := le_of_not_ge hhalf
      by_cases hpi : theta ≤ Real.pi
      · have hphi : Real.pi - theta ∈ Icc (0 : ℝ) (Real.pi / 2) := by
          constructor <;> linarith
        have hbase : ¬InBaseFamily F (Real.pi - theta) := by
          rintro ⟨I, hI, hmem⟩
          exact hout ⟨I, hI, Or.inr (Or.inr (Or.inl hmem))⟩
        simpa using hfirst (Real.pi - theta) hphi hbase
      · have hpi' : Real.pi ≤ theta := le_of_not_ge hpi
        have hphi : theta - Real.pi ∈ Icc (0 : ℝ) (Real.pi / 2) := by
          constructor <;> linarith
        have hbase : ¬InBaseFamily F (theta - Real.pi) := by
          rintro ⟨I, hI, hmem⟩
          exact hout ⟨I, hI, Or.inr (Or.inr (Or.inr hmem))⟩
        simpa using hfirst (theta - Real.pi) hphi hbase

/-- Cardinality of the base family in the real form used by the first
discrepancy colouring. -/
theorem suitableFamily_base_card
    {n t : ℕ} {gamma : ℝ} (hn : 0 < n)
    (hseven : SevenCellProperty n t gamma)
    (hgeom : GeometricCertificate n t gamma) :
    (suitableIntervalFamilyOfDangerousRuns hn hseven hgeom).base.card =
      (firstQuadrantRuns n t gamma).card :=
  card_firstQuadrantIntervals hn

end

end CosineConstruction

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/CosineDerivatives.lean` -/

section
/-!
# Derivative bounds for the normalized Rudin--Shapiro cosine block

This file supplies the analytic differentiation facts for `normalizedH`.
-/

namespace CosineConstruction

open scoped BigOperators

noncomputable section

private theorem hasDerivAt_unitPoint (c x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ unitPoint (c * y))
      ((c : ℂ) * Complex.I * unitPoint (c * x)) x := by
  have hinner : HasDerivAt (fun y : ℝ ↦ ((c : ℂ) * Complex.I) * (y : ℂ))
      ((c : ℂ) * Complex.I) x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul
      ((c : ℂ) * Complex.I)
  simpa only [unitPoint, Complex.ofReal_mul, mul_assoc, mul_comm, mul_left_comm] using
    hinner.cexp

private theorem hasDerivAt_normalizedPDerivative (r t : ℕ) (x : ℝ) :
    HasDerivAt (normalizedPDerivative r t)
      (normalizedPDerivative (r + 1) t x) x := by
  have hTnat : 0 < evenT t := by simp [evenT]
  have hT : (evenT t : ℝ) ≠ 0 := by exact_mod_cast hTnat.ne'
  let p : Polynomial ℂ :=
    (Erdos228.Bernstein.eulerDerivative^[r]) (rudinShapiroP t)
  have hunit : HasDerivAt (fun y : ℝ ↦ unitPoint (y / evenT t))
      ((Complex.I / (evenT t : ℝ)) * unitPoint (x / evenT t)) x := by
    convert hasDerivAt_unitPoint (1 / evenT t) x using 1
    · funext y
      congr 1
      field_simp
    · push_cast
      field_simp
  have hpoly := (p.hasDerivAt (unitPoint (x / evenT t))).comp x hunit
  let C : ℂ := (rsNormalization t : ℂ) * (Complex.I / (evenT t : ℝ)) ^ r
  have hfun : normalizedPDerivative r t =
      fun y ↦ C * p.eval (unitPoint (y / evenT t)) := by
    funext y
    rfl
  rw [hfun]
  have hnext : normalizedPDerivative (r + 1) t x =
      C * (p.derivative.eval (unitPoint (x / evenT t)) *
        ((Complex.I / (evenT t : ℝ)) * unitPoint (x / evenT t))) := by
    unfold normalizedPDerivative
    rw [Function.iterate_succ_apply', Erdos228.Bernstein.eval_eulerDerivative,
      pow_succ]
    dsimp only [C, p]
    ring
  rw [hnext]
  exact hpoly.const_mul C

private theorem hasDerivAt_normalizedQDerivative (r t : ℕ) (x : ℝ) :
    HasDerivAt (normalizedQDerivative r t)
      (normalizedQDerivative (r + 1) t x) x := by
  have hTnat : 0 < evenT t := by simp [evenT]
  have hT : (evenT t : ℝ) ≠ 0 := by exact_mod_cast hTnat.ne'
  let p : Polynomial ℂ :=
    (Erdos228.Bernstein.eulerDerivative^[r]) (rudinShapiroQ t)
  have hunit : HasDerivAt (fun y : ℝ ↦ unitPoint (y / evenT t))
      ((Complex.I / (evenT t : ℝ)) * unitPoint (x / evenT t)) x := by
    convert hasDerivAt_unitPoint (1 / evenT t) x using 1
    · funext y
      congr 1
      field_simp
    · push_cast
      field_simp
  have hpoly := (p.hasDerivAt (unitPoint (x / evenT t))).comp x hunit
  let C : ℂ := (rsNormalization t : ℂ) * (Complex.I / (evenT t : ℝ)) ^ r
  have hfun : normalizedQDerivative r t =
      fun y ↦ C * p.eval (unitPoint (y / evenT t)) := by
    funext y
    rfl
  rw [hfun]
  have hnext : normalizedQDerivative (r + 1) t x =
      C * (p.derivative.eval (unitPoint (x / evenT t)) *
        ((Complex.I / (evenT t : ℝ)) * unitPoint (x / evenT t))) := by
    unfold normalizedQDerivative
    rw [Function.iterate_succ_apply', Erdos228.Bernstein.eval_eulerDerivative,
      pow_succ]
    dsimp only [C, p]
    ring
  rw [hnext]
  exact hpoly.const_mul C

private theorem contDiff_unitPoint_mul (c : ℝ) :
    ContDiff ℝ ⊤ (fun x : ℝ ↦ unitPoint (c * x)) := by
  have hr : ContDiff ℝ ⊤ (fun x : ℝ ↦ c * x) := contDiff_const.mul contDiff_id
  have hc : ContDiff ℝ ⊤ (fun x : ℝ ↦ ((c * x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hr
  unfold unitPoint
  exact (hc.mul contDiff_const).cexp

theorem contDiff_normalizedPDerivative (r t : ℕ) :
    ContDiff ℝ ⊤ (normalizedPDerivative r t) := by
  let p := (Erdos228.Bernstein.eulerDerivative^[r]) (rudinShapiroP t)
  have hp : ContDiff ℝ ⊤ (fun z : ℂ ↦ p.eval z) :=
    p.differentiable.contDiff.restrict_scalars ℝ
  have hu : ContDiff ℝ ⊤ (fun x : ℝ ↦ unitPoint (x / evenT t)) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      contDiff_unitPoint_mul ((evenT t : ℝ)⁻¹)
  unfold normalizedPDerivative
  exact contDiff_const.mul (hp.comp hu)

theorem contDiff_normalizedQDerivative (r t : ℕ) :
    ContDiff ℝ ⊤ (normalizedQDerivative r t) := by
  let p := (Erdos228.Bernstein.eulerDerivative^[r]) (rudinShapiroQ t)
  have hp : ContDiff ℝ ⊤ (fun z : ℂ ↦ p.eval z) :=
    p.differentiable.contDiff.restrict_scalars ℝ
  have hu : ContDiff ℝ ⊤ (fun x : ℝ ↦ unitPoint (x / evenT t)) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      contDiff_unitPoint_mul ((evenT t : ℝ)⁻¹)
  unfold normalizedQDerivative
  exact contDiff_const.mul (hp.comp hu)

theorem iteratedDeriv_normalizedPDerivative (q r t : ℕ) :
    iteratedDeriv q (normalizedPDerivative r t) =
      normalizedPDerivative (r + q) t := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      simpa [Nat.add_assoc] using (hasDerivAt_normalizedPDerivative (r + q) t x).deriv

theorem iteratedDeriv_normalizedQDerivative (q r t : ℕ) :
    iteratedDeriv q (normalizedQDerivative r t) =
      normalizedQDerivative (r + q) t := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      simpa [Nat.add_assoc] using (hasDerivAt_normalizedQDerivative (r + q) t x).deriv

private theorem iteratedDeriv_unitPoint_mul (q : ℕ) (c : ℝ) :
    iteratedDeriv q (fun x : ℝ ↦ unitPoint (c * x)) =
      fun x ↦ ((c : ℂ) * Complex.I) ^ q * unitPoint (c * x) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      simpa only [pow_succ, mul_assoc] using
        (hasDerivAt_unitPoint c x).const_mul (((c : ℂ) * Complex.I) ^ q) |>.deriv

/-- The exact complex `r`-th derivative of `normalizedH`. -/
def normalizedHDerivative (r t : ℕ) (x : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (r + 1),
      (r.choose i : ℂ) *
        (Complex.I ^ i * unitPoint x) * normalizedPDerivative (r - i) t x +
    ∑ i ∈ Finset.range (r + 1),
      (r.choose i : ℂ) *
        (((2 : ℂ) * Complex.I) ^ i * unitPoint (2 * x)) *
          normalizedQDerivative (r - i) t x

theorem contDiff_normalizedH (t : ℕ) :
    ContDiff ℝ ⊤ (normalizedH t) := by
  unfold normalizedH
  simpa only [one_mul] using
    (((contDiff_unitPoint_mul 1).mul (contDiff_normalizedPDerivative 0 t)).add
      ((contDiff_unitPoint_mul 2).mul (contDiff_normalizedQDerivative 0 t)))

theorem iteratedDeriv_normalizedH (r t : ℕ) (x : ℝ) :
    iteratedDeriv r (normalizedH t) x = normalizedHDerivative r t x := by
  have hu1 : ContDiff ℝ ⊤ (fun y : ℝ ↦ unitPoint y) := by
    simpa only [one_mul] using contDiff_unitPoint_mul 1
  have hu2 : ContDiff ℝ ⊤ (fun y : ℝ ↦ unitPoint (2 * y)) :=
    contDiff_unitPoint_mul 2
  have hp := contDiff_normalizedPDerivative 0 t
  have hq := contDiff_normalizedQDerivative 0 t
  have hdu1 (i : ℕ) : iteratedDeriv i (fun y : ℝ ↦ unitPoint y) x =
      Complex.I ^ i * unitPoint x := by
    have h := congrFun (iteratedDeriv_unitPoint_mul i 1) x
    norm_num at h
    exact h
  unfold normalizedH normalizedHDerivative
  change iteratedDeriv r
      ((fun y ↦ unitPoint y * normalizedPDerivative 0 t y) +
        fun y ↦ unitPoint (2 * y) * normalizedQDerivative 0 t y) x = _
  rw [iteratedDeriv_add
    ((hu1.mul hp).contDiffAt.of_le (by simp))
    ((hu2.mul hq).contDiffAt.of_le (by simp))]
  congr 1
  · change iteratedDeriv r
        ((fun y ↦ unitPoint y) * normalizedPDerivative 0 t) x = _
    rw [iteratedDeriv_mul
      (hu1.contDiffAt.of_le (by simp))
      (hp.contDiffAt.of_le (by simp))]
    simp_rw [hdu1,
      congrFun (iteratedDeriv_normalizedPDerivative _ _ _) x]
    simp only [Nat.zero_add]
  · change iteratedDeriv r
        ((fun y ↦ unitPoint (2 * y)) * normalizedQDerivative 0 t) x = _
    rw [iteratedDeriv_mul
      (hu2.contDiffAt.of_le (by simp))
      (hq.contDiffAt.of_le (by simp))]
    simp_rw [congrFun (iteratedDeriv_unitPoint_mul _ 2) x,
      congrFun (iteratedDeriv_normalizedQDerivative _ _ _) x]
    norm_num

theorem contDiff_normalizedH_re (t : ℕ) :
    ContDiff ℝ ⊤ (fun x ↦ (normalizedH t x).re) := by
  exact Complex.reCLM.contDiff.comp (contDiff_normalizedH t)

private theorem hasDerivAt_re_of_hasDerivAt {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y ↦ (f y).re) f'.re x := by
  have hc : HasDerivAt (fun _ : ℝ ↦ Complex.reCLM) 0 x := hasDerivAt_const x _
  simpa using hc.clm_apply hf

theorem iteratedDeriv_normalizedH_re (r t : ℕ) :
    iteratedDeriv r (fun x ↦ (normalizedH t x).re) =
      fun x ↦ (iteratedDeriv r (normalizedH t) x).re := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
      funext x
      have hd : DifferentiableAt ℝ (iteratedDeriv r (normalizedH t)) x :=
        ((contDiff_normalizedH t).differentiable_iteratedDeriv r (by simp)) x
      exact (hasDerivAt_re_of_hasDerivAt hd.hasDerivAt).deriv

theorem iteratedDeriv_normalizedH_re_eq (r t : ℕ) (x : ℝ) :
    iteratedDeriv r (fun y ↦ (normalizedH t y).re) x =
      (normalizedHDerivative r t x).re := by
  rw [congrFun (iteratedDeriv_normalizedH_re r t) x,
    iteratedDeriv_normalizedH]

private theorem norm_normalizedHDerivative_le_sum (r t : ℕ) (x : ℝ) :
    ‖normalizedHDerivative r t x‖ ≤
      ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * (1 / 2 ^ 10 : ℝ) ^ (r - i) +
        ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * 2 ^ i * (1 / 2 ^ 10 : ℝ) ^ (r - i) := by
  unfold normalizedHDerivative
  calc
    ‖∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℂ) * (Complex.I ^ i * unitPoint x) *
              normalizedPDerivative (r - i) t x +
        ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * unitPoint (2 * x)) *
              normalizedQDerivative (r - i) t x‖ ≤
        ‖∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℂ) * (Complex.I ^ i * unitPoint x) *
              normalizedPDerivative (r - i) t x‖ +
        ‖∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * unitPoint (2 * x)) *
              normalizedQDerivative (r - i) t x‖ := norm_add_le _ _
    _ ≤
        ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * (1 / 2 ^ 10 : ℝ) ^ (r - i) +
        ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * 2 ^ i * (1 / 2 ^ 10 : ℝ) ^ (r - i) := by
      apply add_le_add
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        simp only [norm_mul, norm_pow, Complex.norm_I, one_pow,
          norm_unitPoint, mul_one, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left
          (norm_normalizedPDerivative_le (r - i) t x) (by positivity)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        simp only [norm_mul, norm_pow, Complex.norm_I, norm_unitPoint, mul_one,
          Complex.norm_natCast]
        rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
        exact mul_le_mul_of_nonneg_left
          (norm_normalizedQDerivative_le (r - i) t x)
          (mul_nonneg (by positivity) (by positivity))

theorem norm_normalizedHDerivative_le_eighteen {r : ℕ} (hr : r ≤ 4)
    (t : ℕ) (x : ℝ) :
    ‖normalizedHDerivative r t x‖ ≤ 18 := by
  refine (norm_normalizedHDerivative_le_sum r t x).trans ?_
  interval_cases r <;> norm_num [Finset.sum_range_succ, Nat.choose]

theorem abs_iteratedDeriv_normalizedH_re_le_eighteen (r : ℕ) (hr : r ≤ 4)
    (t : ℕ) (x : ℝ) :
    |iteratedDeriv r (fun y ↦ (normalizedH t y).re) x| ≤ 18 := by
  rw [iteratedDeriv_normalizedH_re_eq]
  exact (Complex.abs_re_le_norm _).trans
    (norm_normalizedHDerivative_le_eighteen hr t x)

private def normalizedHDerivativeError (r t : ℕ) (x : ℝ) : ℂ :=
  ∑ i ∈ Finset.range r,
      (r.choose i : ℂ) *
        (Complex.I ^ i * unitPoint x) * normalizedPDerivative (r - i) t x +
    ∑ i ∈ Finset.range r,
      (r.choose i : ℂ) *
        (((2 : ℂ) * Complex.I) ^ i * unitPoint (2 * x)) *
          normalizedQDerivative (r - i) t x

private theorem normalizedHDerivative_sub_leading (r t : ℕ) (x : ℝ) :
    normalizedHDerivative r t x -
        Erdos228.CosineAlgebra.leadingDerivative r
          (unitPoint x * normalizedPDerivative 0 t x)
          (unitPoint (2 * x) * normalizedQDerivative 0 t x) =
      normalizedHDerivativeError r t x := by
  unfold normalizedHDerivative normalizedHDerivativeError
    Erdos228.CosineAlgebra.leadingDerivative
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self]
  ring

private theorem norm_normalizedHDerivativeError_le_sum (r t : ℕ) (x : ℝ) :
    ‖normalizedHDerivativeError r t x‖ ≤
      ∑ i ∈ Finset.range r,
          (r.choose i : ℝ) * (1 / 2 ^ 10 : ℝ) ^ (r - i) +
        ∑ i ∈ Finset.range r,
          (r.choose i : ℝ) * 2 ^ i * (1 / 2 ^ 10 : ℝ) ^ (r - i) := by
  unfold normalizedHDerivativeError
  calc
    ‖∑ i ∈ Finset.range r,
          (r.choose i : ℂ) * (Complex.I ^ i * unitPoint x) *
              normalizedPDerivative (r - i) t x +
        ∑ i ∈ Finset.range r,
          (r.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * unitPoint (2 * x)) *
              normalizedQDerivative (r - i) t x‖ ≤
        ‖∑ i ∈ Finset.range r,
          (r.choose i : ℂ) * (Complex.I ^ i * unitPoint x) *
              normalizedPDerivative (r - i) t x‖ +
        ‖∑ i ∈ Finset.range r,
          (r.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * unitPoint (2 * x)) *
              normalizedQDerivative (r - i) t x‖ := norm_add_le _ _
    _ ≤
        ∑ i ∈ Finset.range r,
          (r.choose i : ℝ) * (1 / 2 ^ 10 : ℝ) ^ (r - i) +
        ∑ i ∈ Finset.range r,
          (r.choose i : ℝ) * 2 ^ i * (1 / 2 ^ 10 : ℝ) ^ (r - i) := by
      apply add_le_add
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        simp only [norm_mul, norm_pow, Complex.norm_I, one_pow,
          norm_unitPoint, mul_one, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left
          (norm_normalizedPDerivative_le (r - i) t x) (by positivity)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        simp only [norm_mul, norm_pow, Complex.norm_I, norm_unitPoint, mul_one,
          Complex.norm_natCast]
        rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
        exact mul_le_mul_of_nonneg_left
          (norm_normalizedQDerivative_le (r - i) t x)
          (mul_nonneg (by positivity) (by positivity))

private theorem norm_normalizedHDerivative_sub_leading_le_eighth {r : ℕ}
    (hr : r < 4) (t : ℕ) (x : ℝ) :
    ‖normalizedHDerivative r t x -
        Erdos228.CosineAlgebra.leadingDerivative r
          (unitPoint x * normalizedPDerivative 0 t x)
          (unitPoint (2 * x) * normalizedQDerivative 0 t x)‖ ≤ 1 / 8 := by
  rw [normalizedHDerivative_sub_leading]
  refine (norm_normalizedHDerivativeError_le_sum r t x).trans ?_
  interval_cases r <;> norm_num [Finset.sum_range_succ, Nat.choose]

theorem exists_large_iteratedDeriv_normalizedH_re (t : ℕ) (x : ℝ) :
    ∃ k : Fin 4,
      1 / 4 ≤ |iteratedDeriv k (fun y ↦ (normalizedH t y).re) x| := by
  have hlarge := Erdos228.CosineAlgebra.exists_large_re_of_normalized_modes
    (u := unitPoint x) (v := unitPoint (2 * x))
    (alpha := normalizedPDerivative 0 t x) (beta := normalizedQDerivative 0 t x)
    (norm_unitPoint x) (norm_unitPoint (2 * x)) (normalized_energy t x)
    (fun k : Fin 4 ↦ normalizedHDerivative k t x)
    (fun k ↦ norm_normalizedHDerivative_sub_leading_le_eighth k.isLt t x)
  simpa only [iteratedDeriv_normalizedH_re_eq] using hlarge

/-- The normalized Rudin--Shapiro cosine has a good cell in every seven
consecutive cells at every mesh size below `1 / 2048`. -/
theorem normalizedH_re_hasGoodCellInEverySeven (t : ℕ) {eta : ℝ}
    (heta : 0 < eta) (hetaSmall : eta < (1 : ℝ) / 2048) :
    HasGoodCellInEverySeven (fun x ↦ (normalizedH t x).re) eta := by
  exact hasGoodCellInEverySeven_of_derivative_bounds
    (fun x ↦ (normalizedH t x).re) eta heta hetaSmall
    ((contDiff_normalizedH_re t).of_le (by simp))
    (exists_large_iteratedDeriv_normalizedH_re t)
    (fun r hr x ↦ abs_iteratedDeriv_normalizedH_re_le_eighteen r hr t x)

end

end CosineConstruction

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/CosineGeometry.lean` -/

section
namespace CosineConstruction

open Set

noncomputable section

/-- Distinct maximal bad runs are linearly ordered and disjoint. -/
private theorem maximalBadRuns_oriented {N a b c d : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad]
    (h₁ : Erdos228.Intervals.IsMaximalBadRun N bad a b)
    (h₂ : Erdos228.Intervals.IsMaximalBadRun N bad c d)
    (hne : (a, b) ≠ (c, d)) :
    b < c ∨ d < a := by
  rcases lt_trichotomy a c with hac | hac | hca
  · left
    by_contra hbc
    have hcb : c ≤ b := Nat.le_of_not_gt hbc
    have hcpos : 0 < c := by omega
    have hcPredN : c - 1 < N :=
      lt_of_le_of_lt (Nat.sub_le c 1) (hcb.trans_lt h₁.2.1)
    have hbadPred : bad (c - 1) :=
      h₁.2.2.1 (c - 1) (Finset.mem_range.mpr hcPredN) (by omega) (by omega)
    rcases h₂.2.2.2.1 with hc0 | hgoodPred
    · omega
    · exact hgoodPred hbadPred
  · exact False.elim (hne (h₁.eq_of_start_eq h₂ hac))
  · right
    by_contra hda
    have had : a ≤ d := Nat.le_of_not_gt hda
    have hapos : 0 < a := by omega
    have haPredN : a - 1 < N :=
      lt_of_le_of_lt (Nat.sub_le a 1) (had.trans_lt h₂.2.1)
    have hbadPred : bad (a - 1) :=
      h₂.2.2.1 (a - 1) (Finset.mem_range.mpr haPredN) (by omega) (by omega)
    rcases h₁.2.2.2.1 with ha0 | hgoodPred
    · omega
    · exact hgoodPred hbadPred

/-- The closed grid intervals attached to distinct first-quadrant dangerous
runs are separated by at least one grid spacing.  Equality can occur at the
two facing grid endpoints when exactly one good cell lies between the runs. -/
theorem firstQuadrantIntervals_pairwise_separated
    {n t : ℕ} {gamma : ℝ} (hn : 0 < n) :
    Set.Pairwise
      (↑(firstQuadrantIntervals n t gamma) :
        Set Erdos228.OddSine.RealInterval)
      (fun I J ↦ ∀ x ∈ Icc I.1 I.2, ∀ y ∈ Icc J.1 J.2,
        Real.pi / n ≤ |x - y|) := by
  classical
  intro I hI J hJ hne x hx y hy
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨⟨c, d⟩, hcd, rfl⟩ := Finset.mem_image.mp hJ
  have hrunsNe : (a, b) ≠ (c, d) := by
    intro heq
    apply hne
    exact congrArg (runEndpoints n) heq
  rw [mem_firstQuadrantRuns] at hab hcd
  have horient := maximalBadRuns_oriented
    (show Erdos228.Intervals.IsMaximalBadRun (2 * n) (BadCell n t gamma) a b by
      simpa only [mem_dangerousRuns] using hab.1)
    (show Erdos228.Intervals.IsMaximalBadRun (2 * n) (BadCell n t gamma) c d by
      simpa only [mem_dangerousRuns] using hcd.1)
    hrunsNe
  simp only [runEndpoints, mem_Icc] at hx hy ⊢
  have hmono := Erdos228.Intervals.gridPoint_mono hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmesh : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  rcases horient with hbc | hda
  · have hgap : b + 2 ≤ c := dangerousRuns_separated hab.1 hcd.1 hbc
    have hgrid :
        Erdos228.Intervals.gridPoint n (b + 1) + Real.pi / n ≤
          Erdos228.Intervals.gridPoint n c := by
      rw [← Erdos228.Intervals.gridPoint_succ]
      exact hmono hgap
    rw [abs_of_nonpos (by linarith [hx.2, hy.1])]
    linarith [hx.2, hy.1]
  · have hgap : d + 2 ≤ a := dangerousRuns_separated hcd.1 hab.1 hda
    have hgrid :
        Erdos228.Intervals.gridPoint n (d + 1) + Real.pi / n ≤
          Erdos228.Intervals.gridPoint n a := by
      rw [← Erdos228.Intervals.gridPoint_succ]
      exact hmono hgap
    rw [abs_of_nonneg (by linarith [hx.1, hy.2])]
    linarith [hx.1, hy.2]

private theorem rudinShapiro_odd_axis_values (k : ℕ) :
    (rudinShapiroP (2 * k + 1)).eval 1 = (2 ^ (k + 1) : ℕ) ∧
    (rudinShapiroQ (2 * k + 1)).eval 1 = 0 ∧
    (rudinShapiroP (2 * k + 1)).eval (-1) = 0 ∧
    (rudinShapiroQ (2 * k + 1)).eval (-1) = (2 ^ (k + 1) : ℕ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rcases ih with ⟨hP1, hQ1, hPm1, hQm1⟩
      have hs : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      rw [hs, show (2 * k + 1) + 2 = ((2 * k + 1) + 1) + 1 by omega]
      rw [eval_rudinShapiroP_succ ((2 * k + 1) + 1) 1,
        eval_rudinShapiroQ_succ ((2 * k + 1) + 1) 1,
        eval_rudinShapiroP_succ ((2 * k + 1) + 1) (-1),
        eval_rudinShapiroQ_succ ((2 * k + 1) + 1) (-1)]
      rw [eval_rudinShapiroP_succ (2 * k + 1) 1,
        eval_rudinShapiroQ_succ (2 * k + 1) 1,
        eval_rudinShapiroP_succ (2 * k + 1) (-1),
        eval_rudinShapiroQ_succ (2 * k + 1) (-1)]
      rw [hP1, hQ1, hPm1, hQm1]
      norm_num [pow_succ]
      ring

private theorem sqrt_two_pow_odd_succ (k : ℕ) :
    Real.sqrt (2 ^ ((2 * k + 1) + 1) : ℝ) = (2 ^ (k + 1) : ℕ) := by
  rw [show (2 * k + 1) + 1 = (k + 1) * 2 by omega, pow_mul]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
  · norm_num
  · positivity

theorem normalizedH_re_zero_of_odd {t : ℕ} (ht : Odd t) :
    (normalizedH t 0).re = 1 := by
  obtain ⟨k, rfl⟩ := ht
  rcases rudinShapiro_odd_axis_values k with ⟨hP1, hQ1, _hPm1, _hQm1⟩
  have hunit0 : unitPoint 0 = 1 := by simp [unitPoint]
  simp only [normalizedH, normalizedPDerivative, normalizedQDerivative, pow_zero,
    one_mul, Function.iterate_zero_apply, hunit0, zero_div, rsNormalization]
  rw [hP1, hQ1, sqrt_two_pow_odd_succ]
  norm_num

private theorem unitPoint_evenT_mul_pi (t : ℕ) :
    unitPoint ((evenT t : ℝ) * Real.pi) = 1 := by
  rw [show unitPoint ((evenT t : ℝ) * Real.pi) = unitPoint Real.pi ^ evenT t by
    simp only [unitPoint, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring]
  have hpi : unitPoint Real.pi = -1 := by simp [unitPoint]
  rw [hpi]
  rw [show evenT t = 2 * 2 ^ (t + 9) by simp [evenT, pow_succ']]
  rw [pow_mul]
  norm_num

theorem normalizedH_re_evenT_mul_pi_of_odd {t : ℕ} (ht : Odd t) :
    (normalizedH t ((evenT t : ℝ) * Real.pi)).re = 1 := by
  obtain ⟨k, rfl⟩ := ht
  rcases rudinShapiro_odd_axis_values k with ⟨_hP1, _hQ1, hPm1, hQm1⟩
  have hTpos : (0 : ℝ) < evenT (2 * k + 1) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) ((2 * k + 1) + 10))
  have hdiv :
      ((evenT (2 * k + 1) : ℝ) * Real.pi) / evenT (2 * k + 1) =
        Real.pi := by
    field_simp
  have hphase₁ := unitPoint_evenT_mul_pi (2 * k + 1)
  have hphase₂ :
      unitPoint (2 * ((evenT (2 * k + 1) : ℝ) * Real.pi)) = 1 := by
    rw [show 2 * ((evenT (2 * k + 1) : ℝ) * Real.pi) =
      (evenT (2 * k + 1) : ℝ) * Real.pi +
        (evenT (2 * k + 1) : ℝ) * Real.pi by ring]
    rw [show unitPoint
        ((evenT (2 * k + 1) : ℝ) * Real.pi +
          (evenT (2 * k + 1) : ℝ) * Real.pi) =
        unitPoint ((evenT (2 * k + 1) : ℝ) * Real.pi) *
          unitPoint ((evenT (2 * k + 1) : ℝ) * Real.pi) by
      simp [unitPoint, Complex.exp_add, add_mul]]
    rw [hphase₁]
    norm_num
  simp only [normalizedH, normalizedPDerivative, normalizedQDerivative, pow_zero,
    one_mul, Function.iterate_zero_apply, hphase₁, hphase₂, hdiv,
    show unitPoint Real.pi = -1 by simp [unitPoint], rsNormalization]
  rw [hPm1, hQm1, sqrt_two_pow_odd_succ]
  norm_num

theorem cosineThreshold_lt_half_normalization
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    cosineThreshold n gamma < Real.sqrt (2 ^ (t + 1) : ℝ) / 2 := by
  have hgamma0 : 0 ≤ gamma := (hparam.gamma_pos).le
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hthreshold0 : 0 ≤ cosineThreshold n gamma := by
    exact (cosineThreshold_pos hparam.n_pos hparam.gamma_pos).le
  have hscale0 : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hscaleSq : (Real.sqrt (2 ^ (t + 1) : ℝ)) ^ 2 = 2 ^ (t + 1) :=
    Real.sq_sqrt (by positivity)
  have hthresholdSq :
      (cosineThreshold n gamma) ^ 2 =
        (1 / 2 ^ 16 : ℝ) * (gamma ^ 7 * n) := by
    simp only [cosineThreshold, cosineDelta, mul_pow]
    rw [Real.sq_sqrt hgamma0, Real.sq_sqrt hn0]
    ring
  have hgammaOne : gamma ≤ 1 :=
    hparam.gamma_upper.trans (by norm_num)
  have hgammaPow : gamma ^ 6 ≤ 1 := by
    exact pow_le_one₀ hgamma0 hgammaOne
  have hnum : parameterNumerator t < 2 ^ (t + 12) := by
    have hpowpos : 0 < 2 ^ t := by positivity
    simp only [parameterNumerator, pow_add]
    norm_num
    omega
  have hnumR : (parameterNumerator t : ℝ) < (2 : ℝ) ^ (t + 12) := by
    exact_mod_cast hnum
  have hgammaNum : gamma ^ 7 * (n : ℝ) < (2 : ℝ) ^ (t + 12) := by
    calc
      gamma ^ 7 * (n : ℝ) = gamma ^ 6 * (gamma * n) := by ring
      _ = gamma ^ 6 * parameterNumerator t := by rw [hparam.equation]
      _ ≤ 1 * parameterNumerator t := by
        exact mul_le_mul_of_nonneg_right hgammaPow (by positivity)
      _ < (2 : ℝ) ^ (t + 12) := by simpa using hnumR
  have hsqLt :
      (cosineThreshold n gamma) ^ 2 <
        (Real.sqrt (2 ^ (t + 1) : ℝ) / 2) ^ 2 := by
    rw [hthresholdSq, div_pow, hscaleSq]
    calc
      (1 / 2 ^ 16 : ℝ) * (gamma ^ 7 * n) <
          (1 / 2 ^ 16 : ℝ) * 2 ^ (t + 12) := by gcongr
      _ < (2 ^ (t + 1) : ℝ) / 2 ^ 2 := by
        norm_num [pow_add]
        have hpow : (0 : ℝ) < 2 ^ t := by positivity
        nlinarith
  nlinarith

private theorem normalizedH_re_gt_half_of_close
    {t : ℕ} {axis x : ℝ}
    (haxis : (normalizedH t axis).re = 1)
    (hdiff : Differentiable ℝ (fun y ↦ (normalizedH t y).re))
    (hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normalizedH t z).re) y| ≤ 18)
    (hclose : 18 * |x - axis| < 1 / 2) :
    1 / 2 < (normalizedH t x).re := by
  have hmean :
      |(normalizedH t x).re - (normalizedH t axis).re| ≤
        18 * |x - axis| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (f := fun y ↦ (normalizedH t y).re)
      (x := axis) (y := x)
      (fun y _ ↦ hdiff.differentiableAt)
      (fun y _ ↦ by
        simpa only [Real.norm_eq_abs, iteratedDeriv_succ', iteratedDeriv_zero]
          using hderiv y)
      convex_univ (Set.mem_univ axis) (Set.mem_univ x)
    simpa only [Real.norm_eq_abs, abs_sub_comm] using h
  rw [haxis] at hmean
  have := (abs_le.mp hmean).1
  linarith

private theorem two_mul_evenT_div_n_lt_gamma
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    (2 * evenT t : ℝ) / n < gamma := by
  obtain ⟨k, ht⟩ := hparam.t_odd
  have htpos : 0 < t := by omega
  have hpow : 1 < 2 ^ t := by
    exact one_lt_pow₀ (by norm_num) htpos.ne'
  have hnat : 2 * evenT t < parameterNumerator t := by
    rw [parameterNumerator, two_mul_evenT]
    omega
  have hreal : (2 * evenT t : ℝ) < gamma * n := by
    rw [hparam.equation]
    exact_mod_cast hnat
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  exact (div_lt_iff₀ hnR).2 hreal

private theorem axis_close_numeric
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ 101) :
    18 * C * Real.pi * ((2 * evenT t : ℝ) / n) < 1 / 2 := by
  have hratio := two_mul_evenT_div_n_lt_gamma hparam
  have hgamma0 := hparam.gamma_pos.le
  calc
    18 * C * Real.pi * ((2 * evenT t : ℝ) / n) ≤
        18 * C * Real.pi * gamma := by
      apply mul_le_mul_of_nonneg_left hratio.le
      positivity
    _ ≤ 18 * 101 * 4 * (1 / 2 ^ 40 : ℝ) := by
      gcongr
      · exact Real.pi_le_four
      · exact hparam.gamma_upper
    _ < 1 / 2 := by norm_num

theorem not_badCell_of_left_axis
    {n t i : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    (hdiff : Differentiable ℝ (fun y ↦ (normalizedH t y).re))
    (hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normalizedH t z).re) y| ≤ 18)
    (hi : i < 100) :
    ¬BadCell n t gamma i := by
  rintro ⟨theta, htheta, hsmall⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  have hmono := Erdos228.Intervals.gridPoint_mono hparam.n_pos
  have htheta0 : 0 ≤ theta := by
    have hgp : 0 ≤ Erdos228.Intervals.gridPoint n i := by
      rw [← Erdos228.Intervals.gridPoint_zero n]
      exact hmono (Nat.zero_le i)
    exact hgp.trans htheta.1
  have htheta100 : theta ≤ 100 * Real.pi / n := by
    calc
      theta ≤ Erdos228.Intervals.gridPoint n (i + 1) := htheta.2
      _ ≤ Erdos228.Intervals.gridPoint n 100 := hmono (by omega)
      _ = 100 * Real.pi / n := by simp [Erdos228.Intervals.gridPoint]
  let x : ℝ := 2 * evenT t * theta
  have hxclose : 18 * |x - 0| < 1 / 2 := by
    have hT0 : (0 : ℝ) ≤ 2 * evenT t := by positivity
    rw [sub_zero, abs_of_nonneg (mul_nonneg hT0 htheta0)]
    calc
      18 * (2 * (evenT t : ℝ) * theta) ≤
          18 * (2 * (evenT t : ℝ) * (100 * Real.pi / n)) := by gcongr
      _ = 18 * 100 * Real.pi * ((2 * evenT t : ℝ) / n) := by ring
      _ < 1 / 2 := axis_close_numeric hparam (by norm_num) (by norm_num)
  have hxhalf : 1 / 2 < (normalizedH t x).re :=
    normalizedH_re_gt_half_of_close
      (normalizedH_re_zero_of_odd hparam.t_odd) hdiff hderiv hxclose
  have hscale : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hthreshold := cosineThreshold_lt_half_normalization hparam
  have hcos : cosineThreshold n gamma < evenCosine t theta := by
    rw [evenCosine_eq_normalizedH]
    change cosineThreshold n gamma <
      Real.sqrt (2 ^ (t + 1) : ℝ) * (normalizedH t x).re
    nlinarith
  have habs : evenCosine t theta ≤ |evenCosine t theta| := le_abs_self _
  linarith

theorem not_badCell_of_right_axis
    {n t i : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    (hdiff : Differentiable ℝ (fun y ↦ (normalizedH t y).re))
    (hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normalizedH t z).re) y| ≤ 18)
    (hiFirst : 2 * (i + 1) ≤ n)
    (hiNear : ¬2 * (i + 1 + 100) ≤ n) :
    ¬BadCell n t gamma i := by
  rintro ⟨theta, htheta, hsmall⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  have hiFirstR : (2 : ℝ) * (i + 1) ≤ n := by exact_mod_cast hiFirst
  have hiNearNat : n < 2 * (i + 101) := by omega
  have hiNearR : (n : ℝ) < 2 * (i + 101) := by exact_mod_cast hiNearNat
  have hrightEndpoint :
      Erdos228.Intervals.gridPoint n (i + 1) ≤ Real.pi / 2 := by
    simp only [Erdos228.Intervals.gridPoint, Nat.cast_add, Nat.cast_one]
    apply (div_le_iff₀ hnR).2
    field_simp [hnR.ne']
    nlinarith [Real.pi_pos]
  have hthetaAxis : theta ≤ Real.pi / 2 :=
    htheta.2.trans hrightEndpoint
  have hgridDist :
      Real.pi / 2 - Erdos228.Intervals.gridPoint n i <
        101 * Real.pi / n := by
    simp only [Erdos228.Intervals.gridPoint]
    apply (sub_lt_iff_lt_add).2
    rw [← add_div]
    apply (lt_div_iff₀ hnR).2
    nlinarith [Real.pi_pos]
  have hthetaDist : Real.pi / 2 - theta < 101 * Real.pi / n := by
    linarith [htheta.1, hgridDist]
  have hthetaDist0 : 0 ≤ Real.pi / 2 - theta := sub_nonneg.mpr hthetaAxis
  let x : ℝ := 2 * evenT t * theta
  let axis : ℝ := evenT t * Real.pi
  have hxclose : 18 * |x - axis| < 1 / 2 := by
    have hT0 : (0 : ℝ) ≤ 2 * evenT t := by positivity
    rw [show x - axis =
        -(2 * (evenT t : ℝ)) * (Real.pi / 2 - theta) by
      dsimp only [x, axis]
      ring]
    rw [abs_mul, abs_neg, abs_of_nonneg hT0, abs_of_nonneg hthetaDist0]
    calc
      18 * (2 * (evenT t : ℝ) * (Real.pi / 2 - theta)) ≤
          18 * (2 * (evenT t : ℝ) * (101 * Real.pi / n)) := by
            gcongr
      _ = 18 * 101 * Real.pi * ((2 * evenT t : ℝ) / n) := by ring
      _ < 1 / 2 := axis_close_numeric hparam (by norm_num) (by norm_num)
  have hxhalf : 1 / 2 < (normalizedH t x).re :=
    normalizedH_re_gt_half_of_close
      (show (normalizedH t axis).re = 1 by
        dsimp only [axis]
        exact normalizedH_re_evenT_mul_pi_of_odd hparam.t_odd)
      hdiff hderiv hxclose
  have hscale : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hthreshold := cosineThreshold_lt_half_normalization hparam
  have hcos : cosineThreshold n gamma < evenCosine t theta := by
    rw [evenCosine_eq_normalizedH]
    change cosineThreshold n gamma <
      Real.sqrt (2 ^ (t + 1) : ℝ) * (normalizedH t x).re
    nlinarith
  have habs : evenCosine t theta ≤ |evenCosine t theta| := le_abs_self _
  linarith

/-- The grid cell whose left endpoint is indexed by `n / 2` meets the
middle axis `pi / 2`, and is therefore good.  This includes the cell which
straddles the axis when `n` is odd. -/
theorem not_badCell_middle_axis
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    (hdiff : Differentiable ℝ (fun y ↦ (normalizedH t y).re))
    (hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normalizedH t z).re) y| ≤ 18) :
    ¬BadCell n t gamma (n / 2) := by
  rintro ⟨theta, htheta, hsmall⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  have hqLower : 2 * (n / 2) ≤ n := by omega
  have hqUpper : n < 2 * (n / 2 + 1) := by omega
  have hqLowerR : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast hqLower
  have hqUpperR : (n : ℝ) < 2 * (((n / 2 : ℕ) : ℝ) + 1) := by
    exact_mod_cast hqUpper
  have hgridLower :
      Real.pi / 2 - Real.pi / n ≤
        Erdos228.Intervals.gridPoint n (n / 2) := by
    simp only [Erdos228.Intervals.gridPoint]
    field_simp [hnR.ne']
    nlinarith [Real.pi_pos]
  have hgridUpper :
      Erdos228.Intervals.gridPoint n (n / 2 + 1) ≤
        Real.pi / 2 + Real.pi / n := by
    simp only [Erdos228.Intervals.gridPoint, Nat.cast_add, Nat.cast_one]
    field_simp [hnR.ne']
    nlinarith [Real.pi_pos]
  have hthetaDist : |theta - Real.pi / 2| ≤ Real.pi / n := by
    rw [abs_le]
    constructor <;> linarith [htheta.1, htheta.2, hgridLower, hgridUpper]
  let x : ℝ := 2 * evenT t * theta
  let axis : ℝ := evenT t * Real.pi
  have hxclose : 18 * |x - axis| < 1 / 2 := by
    have hT0 : (0 : ℝ) ≤ 2 * evenT t := by positivity
    rw [show x - axis =
        (2 * (evenT t : ℝ)) * (theta - Real.pi / 2) by
      dsimp only [x, axis]
      ring]
    rw [abs_mul, abs_of_nonneg hT0]
    calc
      18 * (2 * (evenT t : ℝ) * |theta - Real.pi / 2|) ≤
          18 * (2 * (evenT t : ℝ) * (Real.pi / n)) := by gcongr
      _ = 18 * 1 * Real.pi * ((2 * evenT t : ℝ) / n) := by ring
      _ < 1 / 2 := axis_close_numeric hparam (by norm_num) (by norm_num)
  have hxhalf : 1 / 2 < (normalizedH t x).re :=
    normalizedH_re_gt_half_of_close
      (show (normalizedH t axis).re = 1 by
        dsimp only [axis]
        exact normalizedH_re_evenT_mul_pi_of_odd hparam.t_odd)
      hdiff hderiv hxclose
  have hscale : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hthreshold := cosineThreshold_lt_half_normalization hparam
  have hcos : cosineThreshold n gamma < evenCosine t theta := by
    rw [evenCosine_eq_normalizedH]
    change cosineThreshold n gamma <
      Real.sqrt (2 ^ (t + 1) : ℝ) * (normalizedH t x).re
    nlinarith
  have habs : evenCosine t theta ≤ |evenCosine t theta| := le_abs_self _
  linarith

/-- Once the local large-value argument excludes bad cells next to the two
first-quadrant axes, the endpoint margin is pure grid arithmetic. -/
theorem firstQuadrantIntervals_away_from_axes_of_badCell_exclusion
    {n t : ℕ} {gamma : ℝ} (hn : 0 < n)
    (hleft : ∀ i, i < 100 → ¬BadCell n t gamma i)
    (hright : ∀ i, 2 * (i + 1) ≤ n → ¬2 * (i + 1 + 100) ≤ n →
      ¬BadCell n t gamma i) :
    ∀ I ∈ firstQuadrantIntervals n t gamma,
      100 * Real.pi / n ≤ I.1 ∧
        I.2 ≤ Real.pi / 2 - 100 * Real.pi / n := by
  classical
  intro I hI
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hI
  rw [mem_firstQuadrantRuns] at hab
  have hrun :
      Erdos228.Intervals.IsMaximalBadRun (2 * n) (BadCell n t gamma) a b := by
    simpa only [mem_dangerousRuns] using hab.1
  have hbada : BadCell n t gamma a :=
    hrun.2.2.1 a (Finset.mem_range.mpr (hrun.1.trans_lt hrun.2.1)) le_rfl hrun.1
  have hbadb : BadCell n t gamma b :=
    hrun.2.2.1 b (Finset.mem_range.mpr hrun.2.1) hrun.1 le_rfl
  have ha100 : 100 ≤ a := by
    by_contra ha
    exact hleft a (by omega) hbada
  have hb100 : 2 * (b + 1 + 100) ≤ n := by
    by_contra hb
    exact hright b hab.2 hb hbadb
  simp only [runEndpoints]
  constructor
  · rw [show 100 * Real.pi / (n : ℝ) =
        Erdos228.Intervals.gridPoint n 100 by
      simp [Erdos228.Intervals.gridPoint]]
    exact Erdos228.Intervals.gridPoint_mono hn ha100
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hb100R : (2 : ℝ) * (b + 1 + 100) ≤ n := by exact_mod_cast hb100
    simp only [Erdos228.Intervals.gridPoint, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat]
    apply (div_le_iff₀ hnR).2
    field_simp [hnR.ne']
    nlinarith [Real.pi_pos]

/-- The finite-grid separation and axis-exclusion conclusions assemble the
geometric certificate without any further analytic input. -/
theorem geometricCertificateOfBadCellExclusion
    {n t : ℕ} {gamma : ℝ} (hn : 0 < n)
    (hleft : ∀ i, i < 100 → ¬BadCell n t gamma i)
    (hright : ∀ i, 2 * (i + 1) ≤ n → ¬2 * (i + 1 + 100) ≤ n →
      ¬BadCell n t gamma i) :
    GeometricCertificate n t gamma where
  separated := firstQuadrantIntervals_pairwise_separated hn
  away_from_axes :=
    firstQuadrantIntervals_away_from_axes_of_badCell_exclusion hn hleft hright

theorem geometricCertificate_of_parameters
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    GeometricCertificate n t gamma := by
  have hdiff : Differentiable ℝ (fun y ↦ (normalizedH t y).re) :=
    (contDiff_normalizedH_re t).differentiable (by norm_num)
  have hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normalizedH t z).re) y| ≤ 18 := by
    intro y
    exact abs_iteratedDeriv_normalizedH_re_le_eighteen 1 (by omega) t y
  apply geometricCertificateOfBadCellExclusion hparam.n_pos
  · intro i hi
    exact not_badCell_of_left_axis hparam hdiff hderiv hi
  · intro i hiFirst hiNear
    exact not_badCell_of_right_axis hparam hdiff hderiv hiFirst hiNear

/-- Every first-quadrant point where the cosine is below its target level is
covered by one of the maximal bad intervals retained in the first quadrant.
The middle-axis large-value cell ensures that the containing maximal run
cannot cross `pi / 2`. -/
theorem low_point_covered_by_firstQuadrantIntervals
    {n t : ℕ} {gamma theta : ℝ} (hparam : Parameters n t gamma)
    (htheta : theta ∈ Icc 0 (Real.pi / 2))
    (hsmall : |evenCosine t theta| < cosineThreshold n gamma) :
    ∃ I ∈ firstQuadrantIntervals n t gamma,
      Erdos228.OddSine.InInterval I theta := by
  classical
  have hdiff : Differentiable ℝ (fun y ↦ (normalizedH t y).re) :=
    (contDiff_normalizedH_re t).differentiable (by norm_num)
  have hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normalizedH t z).re) y| ≤ 18 := by
    intro y
    exact abs_iteratedDeriv_normalizedH_re_le_eighteen 1 (by omega) t y
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  let P : ℕ → Prop := fun k ↦
    theta ≤ Erdos228.Intervals.gridPoint n (k + 1)
  have hqUpper : n < 2 * (n / 2 + 1) := by omega
  have hqUpperR : (n : ℝ) < 2 * (((n / 2 : ℕ) : ℝ) + 1) := by
    exact_mod_cast hqUpper
  have haxisGrid :
      Real.pi / 2 ≤ Erdos228.Intervals.gridPoint n (n / 2 + 1) := by
    simp only [Erdos228.Intervals.gridPoint, Nat.cast_add, Nat.cast_one]
    field_simp [hnR.ne']
    nlinarith [Real.pi_pos]
  have hPex : ∃ k, P k :=
    ⟨n / 2, htheta.2.trans haxisGrid⟩
  let i : ℕ := Nat.find hPex
  have hiright : theta ≤ Erdos228.Intervals.gridPoint n (i + 1) := by
    simpa only [i, P] using Nat.find_spec hPex
  have hileft : Erdos228.Intervals.gridPoint n i ≤ theta := by
    by_cases hi0 : i = 0
    · rw [hi0, Erdos228.Intervals.gridPoint_zero]
      exact htheta.1
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      have hnot := Nat.find_min hPex (show i - 1 < Nat.find hPex by
        simpa only [i] using Nat.sub_lt hipos Nat.one_pos)
      have hpred : i - 1 + 1 = i := by omega
      change ¬theta ≤ Erdos228.Intervals.gridPoint n (i - 1 + 1) at hnot
      rw [hpred] at hnot
      exact (lt_of_not_ge hnot).le
  have hiq : i ≤ n / 2 := by
    exact Nat.find_min' hPex (htheta.2.trans haxisGrid)
  have hiN : i < 2 * n := by
    have hnpos : 0 < n := hparam.n_pos
    have hn2 : n < 2 * n := by omega
    exact hiq.trans_lt ((Nat.div_le_self n 2).trans_lt hn2)
  have hbad : BadCell n t gamma i :=
    ⟨theta, ⟨hileft, hiright⟩, hsmall⟩
  obtain ⟨⟨a, b⟩, hab, hai, hib⟩ :=
    Erdos228.Intervals.exists_mem_maximalBadRuns_containing hiN hbad
  have hrun : (a, b) ∈ dangerousRuns n t gamma := by
    simpa only [dangerousRuns] using hab
  have hfirst : 2 * (b + 1) ≤ n := by
    by_contra hcross
    have hqLower : 2 * (n / 2) ≤ n := by omega
    have haq : a ≤ n / 2 := hai.trans hiq
    have hqb : n / 2 ≤ b := by omega
    have hmax :
        Erdos228.Intervals.IsMaximalBadRun
          (2 * n) (BadCell n t gamma) a b :=
      mem_dangerousRuns.mp hrun
    have hbadMiddle : BadCell n t gamma (n / 2) :=
      hmax.2.2.1 (n / 2)
        (Finset.mem_range.mpr (by omega)) haq hqb
    exact not_badCell_middle_axis hparam hdiff hderiv hbadMiddle
  have hfirstRun : (a, b) ∈ firstQuadrantRuns n t gamma :=
    mem_firstQuadrantRuns.mpr ⟨hrun, hfirst⟩
  refine ⟨runEndpoints n (a, b), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨(a, b), hfirstRun, rfl⟩
  · simp only [Erdos228.OddSine.InInterval, runEndpoints, mem_Icc]
    have hmono := Erdos228.Intervals.gridPoint_mono hparam.n_pos
    exact ⟨(hmono hai).trans hileft,
      hiright.trans (hmono (by omega))⟩

end

end CosineConstruction

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/CosineParameters.lean` -/

section
/-!
# Existence of parameters for the cosine construction

This file supplies the elementary dyadic parameter choice required by
`CosineConstruction.Parameters`.
-/

namespace CosineConstruction

open Filter

noncomputable section

private lemma parameterNumerator_two_mul_add_one_add_one (k : ℕ) :
    parameterNumerator (2 * k + 1) + 1 = 4098 * 4 ^ k := by
  have hpow : 0 < 2 ^ ((2 * k + 1) + 11) := by positivity
  have hone : 1 ≤ 2 ^ ((2 * k + 1) + 11) + 2 ^ (2 * k + 1) :=
    hpow.trans_le (Nat.le_add_right _ _)
  rw [parameterNumerator, Nat.sub_add_cancel hone]
  simp [pow_add, pow_mul]
  ring

/-- For every sufficiently large `n`, the odd dyadic scale needed by the
cosine construction can be chosen in the prescribed quantitative window. -/
theorem eventually_exists_parameters :
    ∀ᶠ n : ℕ in atTop, ∃ t gamma, Parameters n t gamma := by
  filter_upwards [eventually_ge_atTop (2 ^ 40 * 4098)] with n hn
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hx : (1 : ℝ) ≤ (n : ℝ) / (2 ^ 40 * 4098) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 40 * 4098)]
    exact_mod_cast hn
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 4)
  let t := 2 * k + 1
  let gamma := (parameterNumerator t : ℝ) / n
  refine ⟨t, gamma, ?_⟩
  constructor
  · exact hnpos
  · exact ⟨k, by simp [t]⟩
  · dsimp only [gamma]
    field_simp
  · dsimp only [gamma, t]
    have hnum : ((parameterNumerator (2 * k + 1) : ℕ) : ℝ) + 1 =
        4098 * 4 ^ k := by
      exact_mod_cast parameterNumerator_two_mul_add_one_add_one k
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ))]
    have hkpow : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    have hnupper : (n : ℝ) < (2 ^ 40 * 4098) * 4 ^ (k + 1) := by
      simpa [mul_comm] using (div_lt_iff₀
        (by positivity : (0 : ℝ) < 2 ^ 40 * 4098)).mp hkhi
    rw [show (4 : ℝ) ^ (k + 1) = 4 ^ k * 4 by rw [pow_succ]] at hnupper
    norm_num at hnupper ⊢
    nlinarith
  · dsimp only [gamma, t]
    have hnum : ((parameterNumerator (2 * k + 1) : ℕ) : ℝ) + 1 =
        4098 * 4 ^ k := by
      exact_mod_cast parameterNumerator_two_mul_add_one_add_one k
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ))]
    have hnlower : (2 ^ 40 * 4098 : ℝ) * 4 ^ k ≤ n := by
      simpa [mul_comm] using (le_div_iff₀
        (by positivity : (0 : ℝ) < 2 ^ 40 * 4098)).mp hklo
    norm_num at hnlower ⊢
    nlinarith

end

end CosineConstruction

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/CosineRootContactCount.lean` -/

section
namespace CosineConstruction

open Set

noncomputable section

/-- Replace each real cosine frequency of a complex polynomial by the
corresponding Chebyshev polynomial. -/
def realPartChebyshevPolynomial (p : Polynomial ℂ) : Polynomial ℝ :=
  ∑ k ∈ p.support,
    Polynomial.C (p.coeff k).re * Polynomial.Chebyshev.T ℝ (k : ℤ)

theorem eval_realPartChebyshevPolynomial_cos
    (p : Polynomial ℂ)
    (hreal : ∀ k ∈ p.support, (p.coeff k).im = 0)
    (x : ℝ) :
    (realPartChebyshevPolynomial p).eval (Real.cos x) =
      (p.eval (Erdos228.unitPoint x)).re := by
  classical
  rw [realPartChebyshevPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_eq_sum, Polynomial.sum_def]
  change (∑ k ∈ p.support,
      (Polynomial.C (p.coeff k).re * Polynomial.Chebyshev.T ℝ (k : ℤ)).eval
        (Real.cos x)) =
    Complex.reLm (∑ k ∈ p.support, p.coeff k * Erdos228.unitPoint x ^ k)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.Chebyshev.T_real_cos]
  have hpow := congrArg Complex.re (Erdos228.unitPoint_pow x k)
  have hre : (Erdos228.unitPoint x ^ k).re = Real.cos (k * x) := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, mul_one, add_zero] using hpow
  change (p.coeff k).re * Real.cos ((k : ℤ) * x) =
    (p.coeff k * Erdos228.unitPoint x ^ k).re
  rw [Complex.mul_re, hreal k hk, zero_mul, sub_zero, hre]
  norm_cast

theorem cosineBlockPolynomial_coeff_im (t k : ℕ) :
    ((cosineBlockPolynomial t).coeff k).im = 0 := by
  classical
  by_cases hk : k ∈ (cosineBlockPolynomial t).support
  · rw [support_cosineBlockPolynomial, mem_evenCPrime] at hk
    rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [coeff_cosineBlockPolynomial_first t j hj]
      rcases coeff_rudinShapiroP_eq_one_or_neg_one hj with h | h <;> simp [h]
    · rw [coeff_cosineBlockPolynomial_second t j hj]
      rcases coeff_rudinShapiroQ_eq_one_or_neg_one hj with h | h <;> simp [h]
  · have hcoeff : (cosineBlockPolynomial t).coeff k = 0 := by
      simpa [Polynomial.mem_support_iff] using hk
    simp [hcoeff]

/-- The ordinary real polynomial in `cos(2θ)` representing the cosine
block. -/
def evenCosineChebyshevPolynomial (t : ℕ) : Polynomial ℝ :=
  realPartChebyshevPolynomial (cosineBlockPolynomial t)

theorem eval_evenCosineChebyshevPolynomial (t : ℕ) (x : ℝ) :
    (evenCosineChebyshevPolynomial t).eval (Real.cos (2 * x)) =
      evenCosine t x := by
  simpa only [evenCosineChebyshevPolynomial, evenCosine] using
    eval_realPartChebyshevPolynomial_cos (cosineBlockPolynomial t)
      (fun k _ ↦ cosineBlockPolynomial_coeff_im t k) (2 * x)

theorem natDegree_evenCosineChebyshevPolynomial_le (t : ℕ) :
    (evenCosineChebyshevPolynomial t).natDegree ≤ parameterNumerator t := by
  classical
  rw [evenCosineChebyshevPolynomial, realPartChebyshevPolynomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hk' : k ∈ (cosineBlockPolynomial t).support := by simpa using hk
  have hkBound : k ≤ parameterNumerator t := by
    rw [support_cosineBlockPolynomial, mem_evenCPrime] at hk'
    rcases hk' with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [parameterNumerator, ← two_mul_evenT,
        Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr (by positivity))]
      have hjle : j ≤ 2 ^ t - 1 := Nat.le_sub_one_of_lt hj
      omega
    · rw [parameterNumerator, ← two_mul_evenT,
        Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr (by positivity))]
      exact Nat.add_le_add_left (Nat.le_sub_one_of_lt hj) _
  calc
    (Polynomial.C ((cosineBlockPolynomial t).coeff k).re *
        Polynomial.Chebyshev.T ℝ (k : ℤ)).natDegree ≤
        (Polynomial.C ((cosineBlockPolynomial t).coeff k).re).natDegree +
          (Polynomial.Chebyshev.T ℝ (k : ℤ)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + k := by simp
    _ = k := by omega
    _ ≤ parameterNumerator t := hkBound

private theorem parameterNumerator_eq_topIndex (t : ℕ) :
    parameterNumerator t = 2 * evenT t + (2 ^ t - 1) := by
  rw [parameterNumerator, ← two_mul_evenT,
    Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr (by positivity))]

private theorem topIndex_mem_cosineBlock_support (t : ℕ) :
    parameterNumerator t ∈ (cosineBlockPolynomial t).support := by
  rw [parameterNumerator_eq_topIndex, support_cosineBlockPolynomial,
    mem_evenCPrime]
  right
  exact ⟨2 ^ t - 1, Nat.sub_lt (by positivity) (by norm_num), rfl⟩

theorem natDegree_evenCosineChebyshevPolynomial (t : ℕ) :
    (evenCosineChebyshevPolynomial t).natDegree = parameterNumerator t := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_evenCosineChebyshevPolynomial_le t)
  let m := parameterNumerator t
  have hm : m ∈ (cosineBlockPolynomial t).support :=
    topIndex_mem_cosineBlock_support t
  have hj : 2 ^ t - 1 < 2 ^ t := by
    have : 0 < 2 ^ t := by positivity
    omega
  have htop : ((cosineBlockPolynomial t).coeff m).re ≠ 0 := by
    rw [show m = 2 * evenT t + (2 ^ t - 1) from parameterNumerator_eq_topIndex t]
    rw [coeff_cosineBlockPolynomial_second t (2 ^ t - 1) hj]
    rcases coeff_rudinShapiroQ_eq_one_or_neg_one hj with h | h <;> simp [h]
  have hTtop : (Polynomial.Chebyshev.T ℝ (m : ℤ)).coeff m ≠ 0 := by
    have hdeg : (Polynomial.Chebyshev.T ℝ (m : ℤ)).natDegree = m := by simp
    have hc := Polynomial.coeff_natDegree
      (p := Polynomial.Chebyshev.T ℝ (m : ℤ))
    rw [hdeg] at hc
    rw [hc, Polynomial.Chebyshev.leadingCoeff_T]
    positivity
  change (evenCosineChebyshevPolynomial t).coeff m ≠ 0
  rw [evenCosineChebyshevPolynomial, realPartChebyshevPolynomial,
    Polynomial.finsetSum_coeff, Finset.sum_eq_single m]
  · rw [Polynomial.coeff_C_mul]
    exact mul_ne_zero htop hTtop
  · intro k hk hkm
    have hkBound : k ≤ m := by
      rw [support_cosineBlockPolynomial, mem_evenCPrime] at hk
      rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · rw [show m = 2 * evenT t + (2 ^ t - 1) from parameterNumerator_eq_topIndex t]
        have hjle := Nat.le_sub_one_of_lt hj
        omega
      · rw [show m = 2 * evenT t + (2 ^ t - 1) from parameterNumerator_eq_topIndex t]
        exact Nat.add_le_add_left (Nat.le_sub_one_of_lt hj) _
    have hklt : k < m := lt_of_le_of_ne hkBound hkm
    have hTzero : (Polynomial.Chebyshev.T ℝ (k : ℤ)).coeff m = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hklt)
    rw [Polynomial.coeff_C_mul, hTzero, mul_zero]
  · intro hnot
    exact (hnot hm).elim

theorem evenCosineChebyshevPolynomial_sub_C_ne_zero (t : ℕ) (c : ℝ) :
    evenCosineChebyshevPolynomial t - Polynomial.C c ≠ 0 := by
  intro hzero
  have hconst : evenCosineChebyshevPolynomial t = Polynomial.C c :=
    sub_eq_zero.mp hzero
  have hdeg := natDegree_evenCosineChebyshevPolynomial t
  rw [hconst] at hdeg
  have hmpos : 0 < parameterNumerator t := by
    rw [parameterNumerator_eq_topIndex]
    have hT : 0 < evenT t := by simp [evenT]
    omega
  simp at hdeg
  omega

/-!
This scratch file isolates the topological/combinatorial half of the root
count for the first-quadrant bad runs.  A bad run has a strict sublevel
witness.  Its two ends are weakly above the level (using maximality, or the
two quadrant endpoints), so continuity gives two distinct level contacts.
The contact pairs belonging to distinct maximal runs are disjoint and
ordered.  Consequently any finite set containing all first-quadrant contacts
has at least twice as many elements as there are runs.
-/

theorem continuous_evenCosine (t : ℕ) : Continuous (evenCosine t) := by
  unfold evenCosine Erdos228.unitPoint
  fun_prop

private abbrev FirstQuadrantRun (n t : ℕ) (gamma : ℝ) :=
  ↑(firstQuadrantRuns n t gamma)

private noncomputable def runBadWitness {n t : ℕ} {gamma : ℝ}
    (I : FirstQuadrantRun n t gamma) : ℝ :=
  Classical.choose (show BadCell n t gamma I.1.1 by
    have hI := (mem_firstQuadrantRuns.mp I.2).1
    rw [mem_dangerousRuns] at hI
    exact hI.2.2.1 I.1.1 (Finset.mem_range.mpr (hI.1.trans_lt hI.2.1))
      le_rfl hI.1)

private theorem runBadWitness_mem {n t : ℕ} {gamma : ℝ}
    (I : FirstQuadrantRun n t gamma) :
    runBadWitness I ∈ Erdos228.Intervals.gridCell n I.1.1 := by
  exact (Classical.choose_spec (show BadCell n t gamma I.1.1 by
    have hI := (mem_firstQuadrantRuns.mp I.2).1
    rw [mem_dangerousRuns] at hI
    exact hI.2.2.1 I.1.1 (Finset.mem_range.mpr (hI.1.trans_lt hI.2.1))
      le_rfl hI.1)).1

private theorem runBadWitness_lt {n t : ℕ} {gamma : ℝ}
    (I : FirstQuadrantRun n t gamma) :
    |evenCosine t (runBadWitness I)| < cosineThreshold n gamma := by
  exact (Classical.choose_spec (show BadCell n t gamma I.1.1 by
    have hI := (mem_firstQuadrantRuns.mp I.2).1
    rw [mem_dangerousRuns] at hI
    exact hI.2.2.1 I.1.1 (Finset.mem_range.mpr (hI.1.trans_lt hI.2.1))
      le_rfl hI.1)).2

private theorem left_endpoint_ge {n t : ℕ} {gamma : ℝ}
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (I : FirstQuadrantRun n t gamma) :
    cosineThreshold n gamma ≤
      |evenCosine t (Erdos228.Intervals.gridPoint n I.1.1)| := by
  have hI := (mem_firstQuadrantRuns.mp I.2).1
  rw [mem_dangerousRuns] at hI
  have hn : 0 < n := by
    have hb : I.1.2 < 2 * n := hI.2.1
    exact Nat.pos_of_ne_zero (fun hn0 ↦ by simpa [hn0] using hb)
  by_cases ha : I.1.1 = 0
  · simpa [ha, Erdos228.Intervals.gridPoint_zero] using hzero
  · have hgood : ¬BadCell n t gamma (I.1.1 - 1) :=
      hI.2.2.2.1.resolve_left ha
    by_contra hlt
    rw [not_le] at hlt
    apply hgood
    refine ⟨Erdos228.Intervals.gridPoint n I.1.1, ?_, hlt⟩
    simp only [Erdos228.Intervals.gridCell, mem_Icc]
    constructor
    · exact (Erdos228.Intervals.gridPoint_mono (by omega)) (Nat.sub_le _ _)
    · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr ha)]

private theorem right_endpoint_ge {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (I : FirstQuadrantRun n t gamma) :
    cosineThreshold n gamma ≤
      |evenCosine t (Erdos228.Intervals.gridPoint n (I.1.2 + 1))| := by
  have hmem := mem_firstQuadrantRuns.mp I.2
  have hI := hmem.1
  rw [mem_dangerousRuns] at hI
  by_cases heq : 2 * (I.1.2 + 1) = n
  · have hnEven : (n : ℝ) = 2 * (I.1.2 + 1 : ℕ) := by exact_mod_cast heq.symm
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have harg : Erdos228.Intervals.gridPoint n (I.1.2 + 1) = Real.pi / 2 := by
      rw [Erdos228.Intervals.gridPoint, div_eq_iff hnR]
      rw [hnEven]
      ring
    rwa [harg]
  · have hstrict : 2 * (I.1.2 + 1) < n := lt_of_le_of_ne hmem.2 heq
    have hnotlast : I.1.2 + 1 ≠ 2 * n := by omega
    have hgood : ¬BadCell n t gamma (I.1.2 + 1) :=
      hI.2.2.2.2.resolve_left hnotlast
    by_contra hlt
    rw [not_le] at hlt
    apply hgood
    refine ⟨Erdos228.Intervals.gridPoint n (I.1.2 + 1), ?_, hlt⟩
    simp only [Erdos228.Intervals.gridCell, mem_Icc]
    exact ⟨le_rfl, (Erdos228.Intervals.gridPoint_mono hn) (by omega)⟩

private theorem exists_left_contact {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (I : FirstQuadrantRun n t gamma) :
    ∃ x ∈ Icc (Erdos228.Intervals.gridPoint n I.1.1) (runBadWitness I),
      |evenCosine t x| = cosineThreshold n gamma := by
  apply Erdos228.Intervals.exists_abs_level_between (continuous_evenCosine t)
  · exact (runBadWitness_mem I).1
  · exact Or.inr ⟨runBadWitness_lt I, left_endpoint_ge hzero I⟩

private theorem exists_right_contact {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (I : FirstQuadrantRun n t gamma) :
    ∃ x ∈ Icc (runBadWitness I)
        (Erdos228.Intervals.gridPoint n (I.1.2 + 1)),
      |evenCosine t x| = cosineThreshold n gamma := by
  apply Erdos228.Intervals.exists_abs_level_between (continuous_evenCosine t)
  · have hw := (runBadWitness_mem I).2
    have hI := (mem_firstQuadrantRuns.mp I.2).1
    rw [mem_dangerousRuns] at hI
    exact hw.trans ((Erdos228.Intervals.gridPoint_mono hn)
      (Nat.add_le_add_right hI.1 1))
  · exact Or.inl ⟨runBadWitness_lt I, right_endpoint_ge hn hhalf I⟩

private noncomputable def leftContact {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (I : FirstQuadrantRun n t gamma) : ℝ :=
  Classical.choose (exists_left_contact hn hzero I)

private noncomputable def rightContact {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (I : FirstQuadrantRun n t gamma) : ℝ :=
  Classical.choose (exists_right_contact hn hhalf I)

private theorem leftContact_spec {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (I : FirstQuadrantRun n t gamma) :
    leftContact hn hzero I ∈
        Icc (Erdos228.Intervals.gridPoint n I.1.1) (runBadWitness I) ∧
      |evenCosine t (leftContact hn hzero I)| = cosineThreshold n gamma :=
  Classical.choose_spec (exists_left_contact hn hzero I)

private theorem rightContact_spec {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (I : FirstQuadrantRun n t gamma) :
    rightContact hn hhalf I ∈
        Icc (runBadWitness I) (Erdos228.Intervals.gridPoint n (I.1.2 + 1)) ∧
      |evenCosine t (rightContact hn hhalf I)| = cosineThreshold n gamma :=
  Classical.choose_spec (exists_right_contact hn hhalf I)

private theorem leftContact_lt_witness {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (I : FirstQuadrantRun n t gamma) :
    leftContact hn hzero I < runBadWitness I := by
  have hs := leftContact_spec hn hzero I
  refine hs.1.2.lt_of_ne ?_
  intro heq
  have hv := hs.2
  rw [heq] at hv
  exact (runBadWitness_lt I).ne hv

private theorem witness_lt_rightContact {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (I : FirstQuadrantRun n t gamma) :
    runBadWitness I < rightContact hn hhalf I := by
  have hs := rightContact_spec hn hhalf I
  refine hs.1.1.lt_of_ne ?_
  intro heq
  have hv := hs.2
  rw [← heq] at hv
  exact (runBadWitness_lt I).ne hv

private noncomputable def pairedContact {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|) :
    FirstQuadrantRun n t gamma × Fin 2 → ℝ
  | (I, k) => if (k : ℕ) = 0 then leftContact hn hzero I else rightContact hn hhalf I

private theorem pairedContact_bounds {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (K : FirstQuadrantRun n t gamma) (k : Fin 2) :
    Erdos228.Intervals.gridPoint n K.1.1 ≤ pairedContact hn hzero hhalf (K, k) ∧
    pairedContact hn hzero hhalf (K, k) ≤
      Erdos228.Intervals.gridPoint n (K.1.2 + 1) := by
  by_cases hk : (k : ℕ) = 0
  · simp only [pairedContact, if_pos hk]
    refine ⟨(leftContact_spec hn hzero K).1.1, ?_⟩
    have hrun := mem_dangerousRuns.mp (mem_firstQuadrantRuns.mp K.2).1
    exact (leftContact_spec hn hzero K).1.2.trans <|
      (runBadWitness_mem K).2.trans <|
        (Erdos228.Intervals.gridPoint_mono hn) (Nat.add_le_add_right hrun.1 1)
  · simp only [pairedContact, if_neg hk]
    have hleft := (runBadWitness_mem K).1
    exact ⟨hleft.trans (rightContact_spec hn hhalf K).1.1,
      (rightContact_spec hn hhalf K).1.2⟩

private theorem pairedContact_level {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (K : FirstQuadrantRun n t gamma) (k : Fin 2) :
    |evenCosine t (pairedContact hn hzero hhalf (K, k))| =
      cosineThreshold n gamma := by
  by_cases hk : (k : ℕ) = 0
  · simpa only [pairedContact, if_pos hk] using (leftContact_spec hn hzero K).2
  · simpa only [pairedContact, if_neg hk] using (rightContact_spec hn hhalf K).2

private theorem pairedContact_injective {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|) :
    Function.Injective (pairedContact hn hzero hhalf) := by
  rintro ⟨I, i⟩ ⟨J, j⟩ hij
  have contact_bounds (K : FirstQuadrantRun n t gamma) (k : Fin 2) :
      Erdos228.Intervals.gridPoint n K.1.1 ≤ pairedContact hn hzero hhalf (K, k) ∧
      pairedContact hn hzero hhalf (K, k) ≤
        Erdos228.Intervals.gridPoint n (K.1.2 + 1) := by
    by_cases hk : (k : ℕ) = 0
    · simp only [pairedContact, if_pos hk]
      have hspec := leftContact_spec hn hzero K
      refine ⟨hspec.1.1, ?_⟩
      have hrun := mem_dangerousRuns.mp (mem_firstQuadrantRuns.mp K.2).1
      exact (leftContact_spec hn hzero K).1.2.trans <|
        (runBadWitness_mem K).2.trans <|
          (Erdos228.Intervals.gridPoint_mono hn) (Nat.add_le_add_right hrun.1 1)
    · simp only [pairedContact, if_neg hk]
      exact ⟨(runBadWitness_mem K).1.trans (rightContact_spec hn hhalf K).1.1,
        (rightContact_spec hn hhalf K).1.2⟩
  have hIJ : I = J := by
    apply Subtype.ext
    rcases lt_trichotomy I.1.1 J.1.1 with hlt | heq | hgt
    · have hI := (mem_firstQuadrantRuns.mp I.2).1
      have hJ := (mem_firstQuadrantRuns.mp J.2).1
      have hbc : I.1.2 < J.1.1 := by
        by_contra hnot
        have hmaxI := (mem_dangerousRuns.mp hI)
        have hmaxJ := (mem_dangerousRuns.mp hJ)
        have hJpos : 0 < J.1.1 := by omega
        have hpred : J.1.1 - 1 ≥ I.1.1 := by omega
        have hpred_le : J.1.1 - 1 ≤ I.1.2 := by omega
        have hbad := hmaxI.2.2.1 (J.1.1 - 1)
          (Finset.mem_range.mpr (hpred_le.trans_lt hmaxI.2.1)) hpred hpred_le
        exact hmaxJ.2.2.2.1.resolve_left (Nat.ne_of_gt hJpos) hbad
      have hsep := dangerousRuns_separated hI hJ hbc
      have hidx : I.1.2 + 1 < J.1.1 := by
        calc
          I.1.2 + 1 < (I.1.2 + 1) + 1 := Nat.lt_succ_self _
          _ ≤ J.1.1 := by simpa [Nat.add_assoc] using hsep
      have hgrid : Erdos228.Intervals.gridPoint n (I.1.2 + 1) <
          Erdos228.Intervals.gridPoint n J.1.1 :=
        Erdos228.Intervals.gridPoint_strictMono hn hidx
      have hi := pairedContact_bounds hn hzero hhalf I i
      have hj := pairedContact_bounds hn hzero hhalf J j
      rw [hij] at hi
      linarith
    · have hmaxI := mem_dangerousRuns.mp (mem_firstQuadrantRuns.mp I.2).1
      have hmaxJ := mem_dangerousRuns.mp (mem_firstQuadrantRuns.mp J.2).1
      exact Erdos228.Intervals.IsMaximalBadRun.eq_of_start_eq hmaxI hmaxJ heq
    · have hI := (mem_firstQuadrantRuns.mp I.2).1
      have hJ := (mem_firstQuadrantRuns.mp J.2).1
      have hdc : J.1.2 < I.1.1 := by
        by_contra hnot
        have hmaxI := (mem_dangerousRuns.mp hI)
        have hmaxJ := (mem_dangerousRuns.mp hJ)
        have hIpos : 0 < I.1.1 := by omega
        have hpred : I.1.1 - 1 ≥ J.1.1 := by omega
        have hpred_le : I.1.1 - 1 ≤ J.1.2 := by omega
        have hbad := hmaxJ.2.2.1 (I.1.1 - 1)
          (Finset.mem_range.mpr (hpred_le.trans_lt hmaxJ.2.1)) hpred hpred_le
        exact hmaxI.2.2.2.1.resolve_left (Nat.ne_of_gt hIpos) hbad
      have hsep := dangerousRuns_separated hJ hI hdc
      have hidx : J.1.2 + 1 < I.1.1 := by
        calc
          J.1.2 + 1 < (J.1.2 + 1) + 1 := Nat.lt_succ_self _
          _ ≤ I.1.1 := by simpa [Nat.add_assoc] using hsep
      have hgrid : Erdos228.Intervals.gridPoint n (J.1.2 + 1) <
          Erdos228.Intervals.gridPoint n I.1.1 :=
        Erdos228.Intervals.gridPoint_strictMono hn hidx
      have hi := pairedContact_bounds hn hzero hhalf I i
      have hj := pairedContact_bounds hn hzero hhalf J j
      rw [hij] at hi
      linarith
  subst J
  congr 1
  by_contra hne
  have hfin : ((i : ℕ) = 0 ∧ (j : ℕ) ≠ 0) ∨
      ((i : ℕ) ≠ 0 ∧ (j : ℕ) = 0) := by
    omega
  rcases hfin with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · simp only [pairedContact, if_pos hi, if_neg hj] at hij
    exact (leftContact_lt_witness hn hzero I).trans
      (witness_lt_rightContact hn hhalf I) |>.ne hij
  · simp only [pairedContact, if_neg hi, if_pos hj] at hij
    exact (leftContact_lt_witness hn hzero I).trans
      (witness_lt_rightContact hn hhalf I) |>.ne hij.symm

private noncomputable def polynomialAbsoluteLevelRoots
    (q : Polynomial ℝ) (level : ℝ) : Finset ℝ :=
  (q - Polynomial.C level).roots.toFinset ∪
    (q - Polynomial.C (-level)).roots.toFinset

private theorem card_polynomialAbsoluteLevelRoots_le
    (q : Polynomial ℝ) (level : ℝ) :
    (polynomialAbsoluteLevelRoots q level).card ≤ 2 * q.natDegree := by
  have hplus : (q - Polynomial.C level).roots.toFinset.card ≤ q.natDegree :=
    (Multiset.toFinset_card_le _).trans <|
      (Polynomial.card_roots' _).trans <|
        (Polynomial.natDegree_sub_le _ _).trans <| by
          simp only [max_le_iff]
          exact ⟨le_rfl, by simp⟩
  have hminus : (q - Polynomial.C (-level)).roots.toFinset.card ≤ q.natDegree :=
    (Multiset.toFinset_card_le _).trans <|
      (Polynomial.card_roots' _).trans <|
        (Polynomial.natDegree_sub_le _ _).trans <| by
          simp only [max_le_iff]
          exact ⟨le_rfl, by simp⟩
  calc
    (polynomialAbsoluteLevelRoots q level).card ≤
        (q - Polynomial.C level).roots.toFinset.card +
          (q - Polynomial.C (-level)).roots.toFinset.card :=
      Finset.card_union_le _ _
    _ ≤ q.natDegree + q.natDegree := Nat.add_le_add hplus hminus
    _ = 2 * q.natDegree := by omega

private theorem eval_mem_polynomialAbsoluteLevelRoots
    {q : Polynomial ℝ} {level x : ℝ}
    (hlevel : 0 ≤ level)
    (hplus : q - Polynomial.C level ≠ 0)
    (hminus : q - Polynomial.C (-level) ≠ 0)
    (hx : |q.eval x| = level) :
    x ∈ polynomialAbsoluteLevelRoots q level := by
  rw [abs_eq hlevel] at hx
  rw [polynomialAbsoluteLevelRoots, Finset.mem_union]
  rcases hx with hx | hx
  · left
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hplus, Polynomial.IsRoot.def]
    simp [hx]
  · right
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hminus, Polynomial.IsRoot.def]
    simp [hx]

/-- Polynomial form of the root count.  If `evenCosine t` is represented as
`q(cos(2θ))`, then injectivity of cosine on `[0,π]` sends the two contacts
of every first-quadrant run to distinct roots of `q ± threshold`. -/
theorem card_firstQuadrantRuns_le_polynomial_degree
    {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hlevel : 0 ≤ cosineThreshold n gamma)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (q : Polynomial ℝ)
    (hq : ∀ x, q.eval (Real.cos (2 * x)) = evenCosine t x)
    (hplus : q - Polynomial.C (cosineThreshold n gamma) ≠ 0)
    (hminus : q - Polynomial.C (-cosineThreshold n gamma) ≠ 0) :
    (firstQuadrantRuns n t gamma).card ≤ q.natDegree := by
  let roots := polynomialAbsoluteLevelRoots q (cosineThreshold n gamma)
  let f : FirstQuadrantRun n t gamma × Fin 2 → ↑roots := fun p ↦
    ⟨Real.cos (2 * pairedContact hn hzero hhalf p), by
      apply eval_mem_polynomialAbsoluteLevelRoots hlevel hplus hminus
      rw [hq]
      exact pairedContact_level hn hzero hhalf p.1 p.2⟩
  have hcos_inj : Set.InjOn (fun x : ℝ ↦ Real.cos (2 * x))
      (Icc 0 (Real.pi / 2)) := by
    intro x hx y hy hxy
    have h2x : 2 * x ∈ Icc (0 : ℝ) Real.pi := by
      constructor
      · exact mul_nonneg (by norm_num) hx.1
      · calc
          2 * x ≤ 2 * (Real.pi / 2) := mul_le_mul_of_nonneg_left hx.2 (by norm_num)
          _ = Real.pi := by ring
    have h2y : 2 * y ∈ Icc (0 : ℝ) Real.pi := by
      constructor
      · exact mul_nonneg (by norm_num) hy.1
      · calc
          2 * y ≤ 2 * (Real.pi / 2) := mul_le_mul_of_nonneg_left hy.2 (by norm_num)
          _ = Real.pi := by ring
    have := Real.injOn_cos h2x h2y hxy
    linarith
  have hf : Function.Injective f := by
    intro p r hpr
    apply pairedContact_injective hn hzero hhalf
    apply hcos_inj
    · constructor
      · exact (show 0 ≤ Erdos228.Intervals.gridPoint n p.1.1.1 by
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le)
            (Nat.cast_nonneg _)).trans
          (pairedContact_bounds hn hzero hhalf p.1 p.2).1
      · have hp := (mem_firstQuadrantRuns.mp p.1.2).2
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have hcast : (2 : ℝ) * ((p.1.1.2 + 1 : ℕ) : ℝ) ≤ n := by
          exact_mod_cast hp
        apply (pairedContact_bounds hn hzero hhalf p.1 p.2).2.trans
        simp only [Erdos228.Intervals.gridPoint]
        apply (div_le_iff₀ hnR).2
        nlinarith [Real.pi_pos]
    · constructor
      · exact (show 0 ≤ Erdos228.Intervals.gridPoint n r.1.1.1 by
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le)
            (Nat.cast_nonneg _)).trans
          (pairedContact_bounds hn hzero hhalf r.1 r.2).1
      · have hr := (mem_firstQuadrantRuns.mp r.1.2).2
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have hcast : (2 : ℝ) * ((r.1.1.2 + 1 : ℕ) : ℝ) ≤ n := by
          exact_mod_cast hr
        apply (pairedContact_bounds hn hzero hhalf r.1 r.2).2.trans
        simp only [Erdos228.Intervals.gridPoint]
        apply (div_le_iff₀ hnR).2
        nlinarith [Real.pi_pos]
    · exact Subtype.ext_iff.mp hpr
  have hcard := Fintype.card_le_of_injective f hf
  have hrootcard : roots.card ≤ 2 * q.natDegree :=
    card_polynomialAbsoluteLevelRoots_le q (cosineThreshold n gamma)
  have htwice : 2 * (firstQuadrantRuns n t gamma).card ≤ 2 * q.natDegree := by
    calc
      2 * (firstQuadrantRuns n t gamma).card = Fintype.card (FirstQuadrantRun n t gamma × Fin 2) := by
        simp [Fintype.card_prod, mul_comm]
      _ ≤ Fintype.card ↑roots := hcard
      _ = roots.card := Fintype.card_coe _
      _ ≤ 2 * q.natDegree := hrootcard
  omega

/-- The exact numerical consequence needed by the cosine construction once
its Chebyshev polynomial is supplied. -/
theorem card_firstQuadrantRuns_le_parameterNumerator_of_polynomial
    {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hlevel : 0 ≤ cosineThreshold n gamma)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (q : Polynomial ℝ)
    (hq : ∀ x, q.eval (Real.cos (2 * x)) = evenCosine t x)
    (hplus : q - Polynomial.C (cosineThreshold n gamma) ≠ 0)
    (hminus : q - Polynomial.C (-cosineThreshold n gamma) ≠ 0)
    (hdegree : q.natDegree ≤ parameterNumerator t) :
    (firstQuadrantRuns n t gamma).card ≤ parameterNumerator t :=
  (card_firstQuadrantRuns_le_polynomial_degree hn hlevel hzero hhalf q hq hplus hminus).trans
    hdegree

/-- The finite-contact/root-count conclusion specialized to the actual
Rudin--Shapiro cosine block. -/
theorem card_firstQuadrantRuns_le_parameterNumerator
    {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hlevel : 0 ≤ cosineThreshold n gamma)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|) :
    (firstQuadrantRuns n t gamma).card ≤ parameterNumerator t := by
  apply card_firstQuadrantRuns_le_parameterNumerator_of_polynomial
    hn hlevel hzero hhalf (evenCosineChebyshevPolynomial t)
  · exact eval_evenCosineChebyshevPolynomial t
  · exact evenCosineChebyshevPolynomial_sub_C_ne_zero t _
  · exact evenCosineChebyshevPolynomial_sub_C_ne_zero t _
  · exact natDegree_evenCosineChebyshevPolynomial_le t

end

end CosineConstruction

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/Basic.lean` -/

section
/-
Foundational definitions and elementary polynomial lemmas for Erdős Problem 228.

This file contains no analytic input from the flat-polynomial construction.  It
packages finite coefficient vectors as polynomials, records the elementary
monomial-shift identities, and converts positive non-strict flatness constants
to the strict inequalities used by the formal statement.
-/

open Filter

/-! ### Littlewood polynomials -/

/-- A complex number is a sign when it is either `1` or `-1`. -/
def IsSign (a : ℂ) : Prop := a = 1 ∨ a = -1

theorem IsSign.norm_eq_one {a : ℂ} (ha : IsSign a) : ‖a‖ = 1 := by
  rcases ha with rfl | rfl <;> simp

/-- The coefficient and degree conditions in the statement of Erdős 228. -/
def IsLittlewood (n : ℕ) (p : Polynomial ℂ) : Prop :=
  p.degree = n ∧ ∀ i ≤ n, IsSign (p.coeff i)

/-- Build a polynomial from a coefficient vector indexed by `0, ..., n`. -/
noncomputable def ofCoeffs (n : ℕ) (a : Fin (n + 1) → ℂ) : Polynomial ℂ :=
  ∑ i : Fin (n + 1), Polynomial.monomial (i : ℕ) (a i)

theorem coeff_ofCoeffs_of_le (n i : ℕ) (a : Fin (n + 1) → ℂ) (hi : i ≤ n) :
    (ofCoeffs n a).coeff i = a ⟨i, Nat.lt_succ_iff.mpr hi⟩ := by
  classical
  change Polynomial.lcoeff ℂ i
      (∑ j : Fin (n + 1), Polynomial.monomial (j : ℕ) (a j)) = _
  rw [map_sum]
  rw [Finset.sum_eq_single ⟨i, Nat.lt_succ_iff.mpr hi⟩]
  · simp
  · intro j _ hj
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
    rw [if_neg]
    intro hji
    apply hj
    exact Fin.ext hji
  · simp

theorem coeff_ofCoeffs_of_lt (n i : ℕ) (a : Fin (n + 1) → ℂ) (hi : n < i) :
    (ofCoeffs n a).coeff i = 0 := by
  classical
  change Polynomial.lcoeff ℂ i
      (∑ j : Fin (n + 1), Polynomial.monomial (j : ℕ) (a j)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j _
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  rw [if_neg]
  exact ne_of_lt ((Nat.le_of_lt_succ j.isLt).trans_lt hi)

theorem eval_ofCoeffs (n : ℕ) (a : Fin (n + 1) → ℂ) (z : ℂ) :
    (ofCoeffs n a).eval z = ∑ i, a i * z ^ (i : ℕ) := by
  classical
  simpa [ofCoeffs] using Polynomial.eval_finsetSum (Finset.univ : Finset (Fin (n + 1)))
    (fun i : Fin (n + 1) ↦ Polynomial.monomial (i : ℕ) (a i)) z

theorem degree_ofCoeffs (n : ℕ) (a : Fin (n + 1) → ℂ) (ha : a ⟨n, Nat.lt_succ_self n⟩ ≠ 0) :
    (ofCoeffs n a).degree = n := by
  apply Polynomial.degree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.degree_le_iff_coeff_zero]
    intro m hm
    exact coeff_ofCoeffs_of_lt n m a (by exact_mod_cast hm)
  · simpa [coeff_ofCoeffs_of_le n n a le_rfl] using ha

/-- A coefficient vector whose entries are all signs produces a Littlewood
polynomial of the indicated degree. -/
theorem isLittlewood_ofCoeffs (n : ℕ) (a : Fin (n + 1) → ℂ)
    (ha : ∀ i, IsSign (a i)) : IsLittlewood n (ofCoeffs n a) := by
  constructor
  · apply degree_ofCoeffs
    rcases ha ⟨n, Nat.lt_succ_self n⟩ with h | h <;> simp [h]
  · intro i hi
    rw [coeff_ofCoeffs_of_le n i a hi]
    exact ha ⟨i, Nat.lt_succ_iff.mpr hi⟩

/-! ### Multiplication by a monomial -/

/-- Shift every exponent upward by `k`. -/
noncomputable def shift (k : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.X ^ k * p

theorem eval_shift (k : ℕ) (p : Polynomial ℂ) (z : ℂ) :
    (shift k p).eval z = z ^ k * p.eval z := by
  simp [shift]

theorem norm_eval_shift_of_norm_eq_one (k : ℕ) (p : Polynomial ℂ) {z : ℂ}
    (hz : ‖z‖ = 1) : ‖(shift k p).eval z‖ = ‖p.eval z‖ := by
  rw [eval_shift, norm_mul, norm_pow, hz, one_pow, one_mul]

/-! ### Strictifying uniform square-root bounds -/

/-- The non-strict conclusion furnished by the published theorem. -/
def HasFlatBounds (delta Delta : ℝ) (n : ℕ) (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 →
    delta * Real.sqrt n ≤ ‖p.eval z‖ ∧ ‖p.eval z‖ ≤ Delta * Real.sqrt n

/-- The strict inequalities in the formal statement. -/
def HasStrictTargetBounds (c₁ c₂ : ℝ) (n : ℕ) (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 →
    Real.sqrt n < c₁ * ‖p.eval z‖ ∧
      ‖p.eval z‖ < c₂ * Real.sqrt n

theorem HasFlatBounds.shift {delta Delta : ℝ} {n k : ℕ} {p : Polynomial ℂ}
    (hp : HasFlatBounds delta Delta n p) : HasFlatBounds delta Delta n (shift k p) := by
  intro z hz
  simpa [norm_eval_shift_of_norm_eq_one k p hz] using hp z hz

theorem HasStrictTargetBounds.shift {c₁ c₂ : ℝ} {n k : ℕ} {p : Polynomial ℂ}
    (hp : HasStrictTargetBounds c₁ c₂ n p) :
    HasStrictTargetBounds c₁ c₂ n (shift k p) := by
  intro z hz
  simpa [norm_eval_shift_of_norm_eq_one k p hz] using hp z hz

theorem hasStrictTargetBounds_of_hasFlatBounds {delta Delta : ℝ} {n : ℕ}
    {p : Polynomial ℂ} (hdelta : 0 < delta) (hDelta : 0 < Delta) (hn : 0 < n)
    (hp : HasFlatBounds delta Delta n p) :
    HasStrictTargetBounds (2 / delta) (2 * Delta) n p := by
  intro z hz
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  obtain ⟨hlower, hupper⟩ := hp z hz
  constructor
  · have hmul : 2 * Real.sqrt n ≤ (2 / delta) * ‖p.eval z‖ := by
      calc
        2 * Real.sqrt n = (2 / delta) * (delta * Real.sqrt n) := by field_simp
        _ ≤ (2 / delta) * ‖p.eval z‖ :=
          mul_le_mul_of_nonneg_left hlower (by positivity)
    linarith
  · have hstrict : Delta * Real.sqrt n < (2 * Delta) * Real.sqrt n := by
      have := mul_pos hDelta hsqrt
      nlinarith
    exact hupper.trans_lt hstrict

/-- An eventual family with positive non-strict constants supplies the exact
eventual strict statement used by Erdős 228. -/
theorem eventually_strict_of_eventually_flat {delta Delta : ℝ}
    (hdelta : 0 < delta) (hDelta : 0 < Delta)
    (hflat : ∀ᶠ n : ℕ in atTop, ∃ p : Polynomial ℂ,
      IsLittlewood n p ∧ HasFlatBounds delta Delta n p) :
    ∀ᶠ n : ℕ in atTop, ∃ p : Polynomial ℂ,
      p.degree = n ∧
      (∀ i ≤ n, p.coeff i = 1 ∨ p.coeff i = -1) ∧
      HasStrictTargetBounds (2 / delta) (2 * Delta) n p := by
  filter_upwards [hflat, eventually_gt_atTop (0 : ℕ)] with n hnflat hn
  obtain ⟨p, hpLittlewood, hpFlat⟩ := hnflat
  exact ⟨p, hpLittlewood.1, hpLittlewood.2,
    hasStrictTargetBounds_of_hasFlatBounds hdelta hDelta hn hpFlat⟩

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/Target.lean` -/

section
/-!
# Erdős Problem 228: polynomial and target interface

This file contains the finite-vector representation of a Littlewood polynomial
and the final conversion from the usual non-strict flatness theorem to the
strict, eventual statement used by the formal-conjectures specification.
-/

open Filter

noncomputable section

/-! ## Littlewood polynomials from finite sign vectors -/

/-- The polynomial whose coefficient of `X ^ j` is `eps j`, for
`j : Fin (n + 1)`. -/
def signPoly (n : ℕ) (eps : Fin (n + 1) → ℂ) : Polynomial ℂ :=
  ∑ j : Fin (n + 1), Polynomial.monomial j.1 (eps j)

@[simp]
theorem coeff_signPoly_of_le (n i : ℕ) (eps : Fin (n + 1) → ℂ)
    (hi : i ≤ n) :
    (signPoly n eps).coeff i = eps ⟨i, Nat.lt_succ_iff.2 hi⟩ := by
  classical
  change (Polynomial.lcoeff ℂ i)
      (∑ j : Fin (n + 1), Polynomial.monomial j.1 (eps j)) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  rw [Fintype.sum_eq_single ⟨i, Nat.lt_succ_iff.2 hi⟩]
  · rw [if_pos rfl]
  · intro b hb
    simp only [ite_eq_right_iff]
    intro hbi
    exact (hb (Fin.ext hbi)).elim

@[simp]
theorem coeff_signPoly_of_lt (n i : ℕ) (eps : Fin (n + 1) → ℂ)
    (hi : n < i) :
    (signPoly n eps).coeff i = 0 := by
  classical
  change (Polynomial.lcoeff ℂ i)
      (∑ j : Fin (n + 1), Polynomial.monomial j.1 (eps j)) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [ite_eq_right_iff]
  intro hji
  omega

@[simp]
theorem eval_signPoly (n : ℕ) (eps : Fin (n + 1) → ℂ) (z : ℂ) :
    (signPoly n eps).eval z = ∑ j : Fin (n + 1), eps j * z ^ j.1 := by
  simp [signPoly, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-! ## Conversion of the standard flatness theorem to the target -/

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/FinalAssembly.lean` -/

section
/-!
# Final assembly for Erdős Problem 228

This file contains the purely algebraic last step of the BBMST construction.
It has two deliberately narrow interfaces:

* `CenteredPairedInput` records the signed coefficients of a centered Laurent
  polynomial together with its already assembled cosine/even-sine/odd-sine
  value;
* `EventuallyCenteredPaired` says that these inputs have been constructed for
  every sufficiently large scale.

The first interface is discharged by the cosine and odd-sine construction
modules.  Everything after it--shifting the Laurent polynomial, filling the
last zero, one, two, or three degrees, and changing square-root scales--is
proved here.
-/

open Filter
open scoped BigOperators

noncomputable section

/-- A length-`2 * pi` interval containing exactly the four real
representatives of the symmetric dangerous arcs used in the construction.
The analytic construction works on the circle quotient; keeping this
fundamental interval explicit prevents accidentally asking a bounded union of
real intervals to be periodic as a predicate on all of `ℝ`. -/
def InFundamentalAngle (theta : ℝ) : Prop :=
  theta ∈ Set.Icc (-Real.pi / 2) (3 * Real.pi / 2)

/-! ## Appending at most three sign coefficients -/

/-- A block of `r` consecutive monomials with coefficient `1`, immediately
after degree `base`. -/
def oneTail (base r : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range r, Polynomial.monomial (base + 1 + j) 1

theorem coeff_oneTail (base r i : ℕ) :
    (oneTail base r).coeff i =
      if base < i ∧ i ≤ base + r then 1 else 0 := by
  classical
  change Polynomial.lcoeff ℂ i
      (∑ j ∈ Finset.range r, Polynomial.monomial (base + 1 + j) 1) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  by_cases hi : base < i ∧ i ≤ base + r
  · rw [if_pos hi]
    have hj : i - (base + 1) < r := by omega
    rw [Finset.sum_eq_single (i - (base + 1))]
    · have heq : base + 1 + (i - (base + 1)) = i := by omega
      simp [heq]
    · intro b hb hne
      rw [if_neg]
      intro heq
      apply hne
      omega
    · simp [hj]
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    intro heq
    apply hi
    simp only [Finset.mem_range] at hj
    omega

/-- Append a consecutive block of `1` coefficients after the old degree. -/
def appendOnes (base r : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  p + oneTail base r

theorem coeff_appendOnes_of_le {base r i : ℕ} {p : Polynomial ℂ}
    (hi : i ≤ base) :
    (appendOnes base r p).coeff i = p.coeff i := by
  rw [appendOnes, Polynomial.coeff_add, coeff_oneTail]
  simp [show ¬base < i by omega]

theorem coeff_appendOnes_of_lt_le {base r i : ℕ} {p : Polynomial ℂ}
    (hp : p.degree = base) (hlo : base < i) (hhi : i ≤ base + r) :
    (appendOnes base r p).coeff i = 1 := by
  rw [appendOnes, Polynomial.coeff_add, coeff_oneTail, if_pos ⟨hlo, hhi⟩]
  have hpzero : p.coeff i = 0 := by
    apply Polynomial.coeff_eq_zero_of_degree_lt
    rw [hp]
    exact_mod_cast hlo
  rw [hpzero, zero_add]

theorem degree_appendOnes {base r : ℕ} {p : Polynomial ℂ}
    (hp : p.degree = base) :
    (appendOnes base r p).degree = base + r := by
  apply Polynomial.degree_eq_of_le_of_coeff_ne_zero (n := base + r)
  · rw [Polynomial.degree_le_iff_coeff_zero]
    intro i hi
    have hisum : base + r < i := by exact_mod_cast hi
    rw [appendOnes, Polynomial.coeff_add, coeff_oneTail]
    have hibase : base < i := by omega
    have htail : ¬(base < i ∧ i ≤ base + r) := by omega
    rw [if_neg htail]
    simp only [add_zero]
    apply Polynomial.coeff_eq_zero_of_degree_lt
    rw [hp]
    exact_mod_cast hibase
  · by_cases hr : r = 0
    · subst r
      simpa only [Nat.add_zero, appendOnes, oneTail, Finset.range_zero,
        Finset.sum_empty, add_zero] using
        (show p.coeff base ≠ 0 by
          apply Polynomial.coeff_ne_zero_of_eq_degree hp)
    · rw [coeff_appendOnes_of_lt_le hp (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hr)) le_rfl]
      norm_num

theorem isLittlewood_appendOnes {base r : ℕ} {p : Polynomial ℂ}
    (hp : IsLittlewood base p) :
    IsLittlewood (base + r) (appendOnes base r p) := by
  constructor
  · exact degree_appendOnes hp.1
  · intro i hi
    by_cases hibase : i ≤ base
    · rw [coeff_appendOnes_of_le hibase]
      exact hp.2 i hibase
    · rw [coeff_appendOnes_of_lt_le hp.1 (Nat.lt_of_not_ge hibase) hi]
      exact Or.inl rfl

theorem eval_oneTail (base r : ℕ) (z : ℂ) :
    (oneTail base r).eval z = ∑ j ∈ Finset.range r, z ^ (base + 1 + j) := by
  simp [oneTail, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem norm_eval_oneTail_le {base r : ℕ} {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(oneTail base r).eval z‖ ≤ r := by
  rw [eval_oneTail]
  calc
    ‖∑ j ∈ Finset.range r, z ^ (base + 1 + j)‖ ≤
        ∑ j ∈ Finset.range r, ‖z ^ (base + 1 + j)‖ := norm_sum_le _ _
    _ = ∑ _j ∈ Finset.range r, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [norm_pow, hz]
    _ = r := by simp

theorem norm_eval_appendOnes_upper {base r : ℕ} {p : Polynomial ℂ}
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(appendOnes base r p).eval z‖ ≤ ‖p.eval z‖ + r := by
  rw [appendOnes, Polynomial.eval_add]
  calc
    ‖p.eval z + (oneTail base r).eval z‖ ≤
        ‖p.eval z‖ + ‖(oneTail base r).eval z‖ := norm_add_le _ _
    _ ≤ ‖p.eval z‖ + r := by
      gcongr
      exact norm_eval_oneTail_le hz

theorem norm_eval_appendOnes_lower {base r : ℕ} {p : Polynomial ℂ}
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖p.eval z‖ - r ≤ ‖(appendOnes base r p).eval z‖ := by
  have htri : ‖p.eval z‖ ≤
      ‖(appendOnes base r p).eval z‖ + ‖(oneTail base r).eval z‖ := by
    calc
      ‖p.eval z‖ =
          ‖(appendOnes base r p).eval z - (oneTail base r).eval z‖ := by
            congr 1
            simp [appendOnes]
      _ ≤ _ := norm_sub_le _ _
  linarith [norm_eval_oneTail_le (base := base) (r := r) hz]

/-! ## Centered paired input -/

/-- The exact output needed from the cosine/even-sine/odd-sine construction.
The coefficient vector is already shifted from exponents `[-2n,2n]` to
`[0,4n]`.  The evaluation identity says that removing the harmless phase
`z^(2n)` gives the paired value proved in `Assembly.lean`.

Keeping the coefficient vector in this interface makes the final theorem
depend on actual signs, rather than on a bare analytic existence statement. -/
structure CenteredPairedInput (n : ℕ) where
  coeff : Fin (4 * n + 1) → ℂ
  coeff_isSign : ∀ j, IsSign (coeff j)
  cosine : ℝ → ℝ
  evenSine : ℝ → ℝ
  oddSine : ℝ → ℝ
  dangerous : ℝ → Prop
  eval_eq : ∀ theta,
    (ofCoeffs (4 * n) coeff).eval (unitPoint theta) =
      unitPoint theta ^ (2 * n) *
        assembledValue (cosine theta) (evenSine theta) (oddSine theta)
  cosine_upper : ∀ theta, |cosine theta| ≤ Real.sqrt n
  evenSine_upper : ∀ theta, |evenSine theta| ≤ 6 * Real.sqrt n
  oddSine_upper : ∀ theta, |oddSine theta| ≤ 2 ^ 10 * Real.sqrt n
  cosine_lower_off_dangerous : ∀ theta, InFundamentalAngle theta →
    ¬ dangerous theta →
    (1 / 2 ^ 160 : ℝ) * Real.sqrt n + 1 ≤ 2 * |cosine theta|
  oddSine_lower_on_dangerous : ∀ theta, InFundamentalAngle theta →
    dangerous theta →
    10 * Real.sqrt n ≤ |oddSine theta|

/-- The ordinary polynomial obtained by multiplying the centered Laurent
polynomial by `z^(2n)`.  The shift is already reflected in the indexing of
`CenteredPairedInput.coeff`. -/
def CenteredPairedInput.polynomial {n : ℕ} (A : CenteredPairedInput n) :
    Polynomial ℂ :=
  ofCoeffs (4 * n) A.coeff

theorem CenteredPairedInput.isLittlewood {n : ℕ}
    (A : CenteredPairedInput n) : IsLittlewood (4 * n) A.polynomial := by
  exact isLittlewood_ofCoeffs (4 * n) A.coeff A.coeff_isSign

theorem CenteredPairedInput.norm_eval_eq {n : ℕ}
    (A : CenteredPairedInput n) (theta : ℝ) :
    ‖A.polynomial.eval (unitPoint theta)‖ =
      ‖assembledValue (A.cosine theta) (A.evenSine theta) (A.oddSine theta)‖ := by
  rw [CenteredPairedInput.polynomial, A.eval_eq, norm_mul, norm_pow,
    norm_unitPoint, one_pow, one_mul]

theorem CenteredPairedInput.flat_on_parametrized_circle {n : ℕ}
    (hn : 1 ≤ n) (A : CenteredPairedInput n) (theta : ℝ)
    (htheta : InFundamentalAngle theta) :
    (1 / 2 ^ 160 : ℝ) * Real.sqrt n ≤
        ‖A.polynomial.eval (unitPoint theta)‖ ∧
      ‖A.polynomial.eval (unitPoint theta)‖ ≤
        2 ^ 12 * Real.sqrt n := by
  rw [A.norm_eval_eq]
  constructor
  · by_cases hdanger : A.dangerous theta
    · have hbig := eight_sqrt_le_norm_assembledValue_of_odd_sine
          (c := A.cosine theta)
          (A.evenSine_upper theta)
          (A.oddSine_lower_on_dangerous theta htheta hdanger)
      have hsqrt : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
      norm_num at hbig ⊢
      nlinarith
    · have hcos := two_mul_abs_sub_one_le_norm_assembledValue
          (A.cosine theta) (A.evenSine theta) (A.oddSine theta)
      have hlower := A.cosine_lower_off_dangerous theta htheta hdanger
      norm_num at hlower ⊢
      linarith
  · exact norm_assembledValue_le_two_pow_twelve_sqrt hn
      (A.cosine_upper theta) (A.evenSine_upper theta) (A.oddSine_upper theta)

/-! ## Removing the unit-circle parametrization -/

@[simp] theorem unitPoint_add_two_pi (theta : ℝ) :
    unitPoint (theta + 2 * Real.pi) = unitPoint theta := by
  unfold unitPoint
  rw [show (((theta + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
      (theta : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I by
        push_cast
        ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Every point of the unit circle has a representative in the fundamental
interval used by the cosine and odd-sine estimates. -/
theorem exists_fundamental_unitPoint_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ theta : ℝ, InFundamentalAngle theta ∧ unitPoint theta = z := by
  let a := z.arg
  have haLower : -Real.pi < a := Complex.neg_pi_lt_arg z
  have haUpper : a ≤ Real.pi := Complex.arg_le_pi z
  have haPoint : unitPoint a = z := by
    calc
      unitPoint a = Complex.exp ((a : ℂ) * Complex.I) := rfl
      _ = ‖z‖ * Complex.exp ((a : ℂ) * Complex.I) := by rw [hz]; simp
      _ = z := Complex.norm_mul_exp_arg_mul_I z
  by_cases ha : -Real.pi / 2 ≤ a
  · refine ⟨a, ⟨ha, ?_⟩, haPoint⟩
    nlinarith [Real.pi_pos]
  · refine ⟨a + 2 * Real.pi, ⟨?_, ?_⟩, ?_⟩
    · nlinarith [Real.pi_pos]
    · nlinarith [lt_of_not_ge ha]
    · rw [unitPoint_add_two_pi]
      exact haPoint

theorem CenteredPairedInput.flat_on_circle {n : ℕ}
    (hn : 1 ≤ n) (A : CenteredPairedInput n) :
    ∀ z : ℂ, ‖z‖ = 1 →
      (1 / 2 ^ 160 : ℝ) * Real.sqrt n ≤ ‖A.polynomial.eval z‖ ∧
      ‖A.polynomial.eval z‖ ≤ 2 ^ 12 * Real.sqrt n := by
  intro z hz
  obtain ⟨theta, htheta, rfl⟩ :=
    exists_fundamental_unitPoint_of_norm_eq_one hz
  exact A.flat_on_parametrized_circle hn theta htheta

/-! ## From degrees divisible by four to every large degree -/

private theorem sqrt_sixteen_mul (n : ℕ) :
    Real.sqrt (16 * (n : ℝ)) = 4 * Real.sqrt n := by
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 16)]
  norm_num

private theorem sqrt_mono_nat {a b : ℕ} (h : a ≤ b) :
    Real.sqrt a ≤ Real.sqrt b := by
  exact Real.sqrt_le_sqrt (by exact_mod_cast h)

/-- Starting with the degree `4*(d/4)` centered construction and appending
`d%4` leading `1` coefficients gives a degree-`d` Littlewood polynomial.  The
explicit absorption hypothesis is eventual because its left side tends to
infinity with `d`. -/
theorem extend_centered_to_degree (d : ℕ)
    (hn : 1 ≤ d / 4) (A : CenteredPairedInput (d / 4))
    (habsorb : 3 ≤ (1 / 2 ^ 163 : ℝ) * Real.sqrt d) :
    ∃ p : Polynomial ℂ, IsLittlewood d p ∧
      HasFlatBounds (1 / 2 ^ 163) (2 ^ 13) d p := by
  let n := d / 4
  let r := d % 4
  let q := A.polynomial
  let p := appendOnes (4 * n) r q
  have hr : r ≤ 3 := by
    dsimp [r]
    omega
  have hdecomp : 4 * n + r = d := by
    dsimp [n, r]
    omega
  have hqLittlewood : IsLittlewood (4 * n) q := by
    exact A.isLittlewood
  have hpLittlewood : IsLittlewood d p := by
    rw [← hdecomp]
    exact isLittlewood_appendOnes hqLittlewood
  refine ⟨p, hpLittlewood, ?_⟩
  intro z hz
  have hqflat := A.flat_on_circle hn z hz
  have hnle : n ≤ d := by
    dsimp [n]
    omega
  have hdle : d ≤ 16 * n := by
    rw [← hdecomp]
    omega
  have hsqrt_nd : Real.sqrt n ≤ Real.sqrt d := sqrt_mono_nat hnle
  have hsqrt_dn : Real.sqrt d ≤ 4 * Real.sqrt n := by
    calc
      Real.sqrt d ≤ Real.sqrt (16 * (n : ℝ)) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using sqrt_mono_nat hdle
      _ = 4 * Real.sqrt n := sqrt_sixteen_mul n
  have hsqrt_nonneg : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hsqrt_three : 3 ≤ Real.sqrt d := by
    have hfactor : (1 / 2 ^ 163 : ℝ) ≤ 1 := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hfactor hsqrt_nonneg]
  constructor
  · have htail := norm_eval_appendOnes_lower
        (base := 4 * n) (r := r) (p := q) hz
    change ‖q.eval z‖ - (r : ℝ) ≤ ‖p.eval z‖ at htail
    have hrR : (r : ℝ) ≤ 3 := by exact_mod_cast hr
    have hscale : (1 / 2 ^ 162 : ℝ) * Real.sqrt d ≤
        (1 / 2 ^ 160 : ℝ) * Real.sqrt n := by
      norm_num at ⊢
      nlinarith
    norm_num at hqflat habsorb ⊢
    nlinarith
  · have htail := norm_eval_appendOnes_upper
        (base := 4 * n) (r := r) (p := q) hz
    change ‖p.eval z‖ ≤ ‖q.eval z‖ + (r : ℝ) at htail
    have hrR : (r : ℝ) ≤ 3 := by exact_mod_cast hr
    norm_num at hqflat ⊢
    nlinarith

/-! ## Eventual construction and the exact target -/

/-- The sole eventual construction input expected from the analytic modules:
for every sufficiently large scale they produce actual centered sign
coefficients and the cosine/sine bounds recorded in `CenteredPairedInput`. -/
def EventuallyCenteredPaired : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, Nonempty (CenteredPairedInput n)

private theorem eventually_absorb_three :
    ∀ᶠ d : ℕ in Filter.atTop,
      3 ≤ (1 / 2 ^ 163 : ℝ) * Real.sqrt d := by
  have hsqrt : Filter.Tendsto (fun d : ℕ ↦ Real.sqrt (d : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscaled : Filter.Tendsto
      (fun d : ℕ ↦ (1 / 2 ^ 163 : ℝ) * Real.sqrt d)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hsqrt
  exact hscaled (eventually_ge_atTop 3)

/-- The centered construction supplies a uniform eventual family at every
degree.  The remainder `d % 4` is the only reason for the harmless loss from
`2^-160,2^12` to `2^-163,2^13`. -/
theorem eventually_flat_of_eventually_centered
    (hcentered : EventuallyCenteredPaired) :
    ∀ᶠ d : ℕ in Filter.atTop, ∃ p : Polynomial ℂ,
      IsLittlewood d p ∧
      HasFlatBounds (1 / 2 ^ 163) (2 ^ 13) d p := by
  rw [EventuallyCenteredPaired, eventually_atTop] at hcentered
  obtain ⟨N, hN⟩ := hcentered
  filter_upwards [eventually_ge_atTop (4 * max N 1), eventually_absorb_three]
    with d hd habsorb
  have hnN : N ≤ d / 4 := by omega
  have hn1 : 1 ≤ d / 4 := by omega
  obtain ⟨A⟩ := hN (d / 4) hnN
  exact extend_centered_to_degree d hn1 A habsorb

/-- Exact formal-conjectures conclusion, directly from the concrete centered
construction input. -/
theorem target_of_eventually_centered (hcentered : EventuallyCenteredPaired) :
    ∃ (c₁ : ℝ) (c₂ : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    ∃ p : Polynomial ℂ, p.degree = n ∧
    (∀ i ≤ n, p.coeff i = 1 ∨ p.coeff i = -1) ∧
    ∀ z : ℂ, ‖z‖ = 1 →
    (Real.sqrt n < c₁ * ‖p.eval z‖ ∧
      ‖p.eval z‖ < c₂ * Real.sqrt n) := by
  refine Iff.mp ?_ trivial
  constructor
  · intro _
    have hflat := eventually_flat_of_eventually_centered hcentered
    have hstrict := eventually_strict_of_eventually_flat
      (delta := (1 / 2 ^ 163 : ℝ)) (Delta := (2 ^ 13 : ℝ))
      (by positivity) (by positivity) hflat
    exact ⟨2 / (1 / 2 ^ 163 : ℝ), 2 * (2 ^ 13 : ℝ), hstrict⟩
  · intro _
    trivial

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/CosineCompletion.lean` -/

section
/-!
# Unconditional cosine package for Erdős Problem 228

This module combines the normalized derivative argument, maximal bad-cell
runs, the endpoint geometry, and the Chebyshev root count into the concrete
cosine package consumed by the final analytic assembly.
-/

namespace CosineConstruction

open Filter Set

noncomputable section

/-- All data furnished by the cosine construction at a fixed scale. -/
structure CosinePackage (n : ℕ) where
  t : ℕ
  gamma : ℝ
  parameters : Parameters n t gamma
  family : Erdos228.OddSine.SuitableIntervalFamily n
  base_card : (family.base.card : ℝ) ≤ gamma * n
  upper : ∀ theta, |evenCosine t theta| ≤ Real.sqrt n
  lower : ∀ theta, Erdos228.InFundamentalAngle theta →
    ¬Erdos228.OddSine.IsDangerous family theta →
      cosineDelta gamma * Real.sqrt n ≤ |evenCosine t theta|

theorem sevenCellProperty_of_parameters
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    SevenCellProperty n t gamma := by
  apply sevenCellProperty_of_normalized_good hparam
  exact normalizedH_re_hasGoodCellInEverySeven t hparam.eta_pos hparam.eta_lt

theorem endpoint_threshold_bounds
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    cosineThreshold n gamma ≤ |evenCosine t 0| ∧
      cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)| := by
  have hthreshold := cosineThreshold_lt_half_normalization hparam
  have hscale : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  constructor
  · rw [evenCosine_eq_normalizedH]
    simp only [mul_zero]
    rw [normalizedH_re_zero_of_odd hparam.t_odd]
    simp only [abs_mul, abs_one, mul_one, abs_of_pos hscale]
    linarith
  · rw [evenCosine_eq_normalizedH]
    have harg : 2 * (evenT t : ℝ) * (Real.pi / 2) =
        (evenT t : ℝ) * Real.pi := by ring
    rw [harg, normalizedH_re_evenT_mul_pi_of_odd hparam.t_odd]
    simp only [abs_mul, abs_one, mul_one, abs_of_pos hscale]
    linarith

theorem suitableFamily_base_card_le
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    (hseven : SevenCellProperty n t gamma)
    (hgeom : GeometricCertificate n t gamma) :
    ((suitableIntervalFamilyOfDangerousRuns hparam.n_pos hseven hgeom).base.card : ℝ) ≤
      gamma * n := by
  have hend := endpoint_threshold_bounds hparam
  have hcard := card_firstQuadrantRuns_le_parameterNumerator hparam.n_pos
    (cosineThreshold_pos hparam.n_pos hparam.gamma_pos).le hend.1 hend.2
  rw [suitableFamily_base_card hparam.n_pos hseven hgeom]
  have hcardR : ((firstQuadrantRuns n t gamma).card : ℝ) ≤
      parameterNumerator t := by exact_mod_cast hcard
  rwa [hparam.equation]

/-- The complete cosine package associated to any admissible parameter
triple. -/
def cosinePackageOfParameters
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    CosinePackage n := by
  let hseven : SevenCellProperty n t gamma :=
    sevenCellProperty_of_parameters hparam
  let hgeom : GeometricCertificate n t gamma :=
    geometricCertificate_of_parameters hparam
  let F : Erdos228.OddSine.SuitableIntervalFamily n :=
    suitableIntervalFamilyOfDangerousRuns hparam.n_pos hseven hgeom
  refine
    { t := t
      gamma := gamma
      parameters := hparam
      family := F
      base_card := ?_
      upper := ?_
      lower := ?_ }
  · simpa only [F] using suitableFamily_base_card_le hparam hseven hgeom
  · intro theta
    exact abs_evenCosine_le_sqrt_of_parameters hparam.toEvenParameters theta
  · intro theta htheta hout
    have hfirst : ∀ x ∈ Icc (0 : ℝ) (Real.pi / 2),
        ¬InBaseFamily F x → cosineThreshold n gamma ≤ |evenCosine t x| := by
      intro x hx hbase
      apply le_of_not_gt
      intro hsmall
      apply hbase
      obtain ⟨I, hI, hxI⟩ :=
        low_point_covered_by_firstQuadrantIntervals hparam hx hsmall
      refine ⟨I, ?_, hxI⟩
      change I ∈ firstQuadrantIntervals n t gamma
      exact hI
    have hlower := lower_on_fundamental_of_lower_off_base F hfirst theta
      (by simpa only [Erdos228.InFundamentalAngle] using htheta) hout
    simpa only [cosineThreshold] using hlower

/-- For every sufficiently large scale, the concrete cosine parameters and
dangerous interval family exist with all bounds needed by the final
assembly. -/
theorem eventually_exists_cosinePackage :
    ∀ᶠ n : ℕ in atTop, Nonempty (CosinePackage n) := by
  filter_upwards [eventually_exists_parameters] with n hparam
  obtain ⟨t, gamma, hparam⟩ := hparam
  exact ⟨cosinePackageOfParameters hparam⟩

end

end CosineConstruction

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/OddFirstAdmissible.lean` -/

section
/-!
# The first odd-sine colouring parameters

This file verifies the numerical hypotheses for the first full-colouring
argument in the odd-sine construction.  If the interval family has `N`
members, the common discrepancy parameter is

`14 * sqrt (log (16 * n / N))`.

The smallness assumption `N ≤ 2⁻⁴⁰ n` is just strong enough for the unit-error
estimate.  The proof retains the rational margin in the published constants.
-/

namespace OddSine

open scoped BigOperators

noncomputable section

/-- The common parameter in the first discrepancy colouring. -/
def firstColoringParameter (n N : ℕ) : ℝ :=
  14 * Real.sqrt (Real.log ((16 * n : ℕ) / (N : ℝ)))

private lemma firstColoring_ratio_ge
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    (2 : ℝ) ^ 44 ≤ (16 * n : ℕ) / (N : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsmall : (N : ℝ) ≤ (n : ℝ) / 2 ^ 40 := by
    calc
      (N : ℝ) ≤ gamma * n := hcard
      _ ≤ (1 / (2 : ℝ) ^ 40) * n :=
        mul_le_mul_of_nonneg_right hgamma hnR.le
      _ = (n : ℝ) / 2 ^ 40 := by ring
  apply (le_div_iff₀ hNR).2
  push_cast
  norm_num at hsmall ⊢
  nlinarith

private lemma firstColoring_log_ratio_nonneg
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    0 ≤ Real.log ((16 * n : ℕ) / (N : ℝ)) := by
  apply Real.log_nonneg
  exact (by norm_num : (1 : ℝ) ≤ 2 ^ 44).trans
    (firstColoring_ratio_ge hn hN hgamma hcard)

private lemma log_ratio_div_ratio_le
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    Real.log ((16 * n : ℕ) / (N : ℝ)) /
        ((16 * n : ℕ) / (N : ℝ)) ≤
      (28 / 5 : ℝ) ^ 2 / 2 ^ 44 := by
  let q : ℝ := (16 * n : ℕ) / (N : ℝ)
  have hq : (2 : ℝ) ^ 44 ≤ q := firstColoring_ratio_ge hn hN hgamma hcard
  have hexp : Real.exp 1 ≤ (2 : ℝ) ^ 44 := by
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have hmono : Real.log q / q ≤ Real.log ((2 : ℝ) ^ 44) / (2 : ℝ) ^ 44 :=
    Real.log_div_self_antitoneOn hexp (hexp.trans hq) hq
  have hlog2 : Real.log 2 ≤ (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  have hlogpow : Real.log ((2 : ℝ) ^ 44) ≤ 44 * (7 / 10 : ℝ) := by
    rw [Real.log_pow]
    nlinarith
  dsimp only [q] at hmono
  calc
    Real.log ((16 * n : ℕ) / (N : ℝ)) /
          ((16 * n : ℕ) / (N : ℝ)) ≤
        Real.log ((2 : ℝ) ^ 44) / (2 : ℝ) ^ 44 := hmono
    _ ≤ (28 / 5 : ℝ) ^ 2 / 2 ^ 44 := by
      apply div_le_div_of_nonneg_right (hlogpow.trans (by norm_num)) (by positivity)

private lemma sqrt_card_scale_le
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    Real.sqrt N * Real.sqrt n / n ≤ (1 : ℝ) / 2 ^ 20 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) ≤ N := by positivity
  have hsmall : (N : ℝ) ≤ (n : ℝ) / 2 ^ 40 := by
    calc
      (N : ℝ) ≤ gamma * n := hcard
      _ ≤ (1 / (2 : ℝ) ^ 40) * n :=
        mul_le_mul_of_nonneg_right hgamma hnR.le
      _ = (n : ℝ) / 2 ^ 40 := by ring
  have hsqrtn_sq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hsqrtN_sq : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt hNR
  have hscale_nonneg : 0 ≤ Real.sqrt N * Real.sqrt n / (n : ℝ) := by positivity
  have hsquare :
      (Real.sqrt N * Real.sqrt n / (n : ℝ)) ^ 2 = (N : ℝ) / n := by
    rw [div_pow, mul_pow, hsqrtN_sq, hsqrtn_sq]
    field_simp
  have htarget_nonneg : (0 : ℝ) ≤ 1 / 2 ^ 20 := by positivity
  have hratio : (N : ℝ) / n ≤ (1 : ℝ) / 2 ^ 40 := by
    apply (div_le_iff₀ hnR).2
    calc
      (N : ℝ) ≤ (n : ℝ) / 2 ^ 40 := hsmall
      _ = ((1 : ℝ) / 2 ^ 40) * n := by ring
  nlinarith [sq_nonneg
    (Real.sqrt N * Real.sqrt n / (n : ℝ) + (1 : ℝ) / 2 ^ 20)]

private lemma sqrt_log_mul_sqrt_card_scale_le
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    Real.sqrt (Real.log ((16 * n : ℕ) / (N : ℝ))) *
        (Real.sqrt N * Real.sqrt n / n) ≤
      (28 / 5 : ℝ) / 2 ^ 20 := by
  let q : ℝ := (16 * n : ℕ) / (N : ℝ)
  let a : ℝ := Real.sqrt N * Real.sqrt n / n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hlog : 0 ≤ Real.log q := by
    dsimp only [q]
    exact firstColoring_log_ratio_nonneg hn hN hgamma hcard
  have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
  have hsqrta : a ^ 2 = 16 / q := by
    have hsqrtn_sq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
    have hsqrtN_sq : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt hNR.le
    dsimp [a, q]
    rw [div_pow, mul_pow, hsqrtN_sq, hsqrtn_sq]
    push_cast
    field_simp
  have hquot := log_ratio_div_ratio_le hn hN hgamma hcard
  change Real.log q / q ≤ (28 / 5 : ℝ) ^ 2 / 2 ^ 44 at hquot
  have hsqrtlog_sq : (Real.sqrt (Real.log q)) ^ 2 = Real.log q :=
    Real.sq_sqrt hlog
  have hleft_nonneg : 0 ≤ Real.sqrt (Real.log q) * a := by positivity
  have hright_nonneg : (0 : ℝ) ≤ (28 / 5 : ℝ) / 2 ^ 20 := by positivity
  have hsquare :
      (Real.sqrt (Real.log q) * a) ^ 2 = 16 * (Real.log q / q) := by
    rw [mul_pow, hsqrtlog_sq, hsqrta]
    field_simp
  nlinarith

/-- The common parameter has exactly the exponential weight needed by the
first full-colouring budget. -/
theorem exp_neg_firstColoringParameter_sq
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    Real.exp (-(firstColoringParameter n N) ^ 2 / 196) =
      (N : ℝ) / (16 * n) := by
  have hlog := firstColoring_log_ratio_nonneg hn hN hgamma hcard
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [firstColoringParameter, mul_pow, Real.sq_sqrt hlog]
  have hqpos : (0 : ℝ) < (16 * n : ℕ) / (N : ℝ) := by positivity
  rw [show -((14 : ℝ) ^ 2 * Real.log ((16 * n : ℕ) / (N : ℝ))) / 196 =
      -Real.log ((16 * n : ℕ) / (N : ℝ)) by ring]
  rw [Real.exp_neg, Real.exp_log hqpos]
  push_cast
  field_simp

/-- Under the BBMST density bound, the common first-colouring parameter is
admissible.  Positivity of `F.base.card` is necessary here: when `n > 0`, the
budget condition itself rules out an empty base family. -/
theorem firstColoringAdmissible_of_card_le
    {n : ℕ} (hn : 0 < n) (F : SuitableIntervalFamily n) {gamma : ℝ}
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hbase : 0 < F.base.card)
    (hcard : (F.base.card : ℝ) ≤ gamma * n) :
    FirstColoringAdmissible F
      (fun _ ↦ firstColoringParameter n F.base.card) := by
  classical
  apply firstColoringAdmissible_of_numeric hn
  · intro j
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · simp_rw [exp_neg_firstColoringParameter_sq hn hbase hgamma hcard]
    simp
    field_simp
    norm_num
  · intro j
    have hscale := sqrt_card_scale_le hn hbase hgamma hcard
    have hlogscale :=
      sqrt_log_mul_sqrt_card_scale_le hn hbase hgamma hcard
    have hpi : Real.pi ≤ (22 / 7 : ℝ) :=
      Real.pi_lt_d4.le.trans (by norm_num)
    rw [firstColoringParameter]
    simp only [K_eq]
    have hnonneg :
        0 ≤ (14 * Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
          (Real.sqrt F.base.card * Real.sqrt n / n) := by
      have hlog := firstColoring_log_ratio_nonneg hn hbase hgamma hcard
      positivity
    calc
      (14 * Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
          Real.sqrt (Fintype.card (↑F.base : Type)) *
          (24 * 128 * Real.pi * Real.sqrt n / n) =
        (24 * 128 * Real.pi) *
          ((14 * Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
            (Real.sqrt F.base.card * Real.sqrt n / n)) := by
          simp only [Fintype.card_coe]
          ring
      _ ≤ (24 * 128 * (22 / 7 : ℝ)) *
          ((14 * Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
            (Real.sqrt F.base.card * Real.sqrt n / n)) := by
          gcongr
      _ ≤ (24 * 128 * (22 / 7 : ℝ)) *
          (14 * ((28 / 5 : ℝ) / 2 ^ 20) + 30 * ((1 : ℝ) / 2 ^ 20)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            (14 * Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
                (Real.sqrt F.base.card * Real.sqrt n / n) =
              14 * (Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) *
                (Real.sqrt F.base.card * Real.sqrt n / n)) +
              30 * (Real.sqrt F.base.card * Real.sqrt n / n) := by ring
            _ ≤ 14 * ((28 / 5 : ℝ) / 2 ^ 20) +
                30 * ((1 : ℝ) / 2 ^ 20) := by gcongr
      _ ≤ 1 := by norm_num

/-- If the interval family is empty, the first colouring step is unnecessary:
the unique empty collection of interval signs has all Fourier targets equal to
zero.  This is the correct replacement for admissibility in the zero-cardinal
branch (the admissibility budget itself is impossible when `n > 0`). -/
theorem exists_intervalColoring_of_base_card_eq_zero
    {n : ℕ} (F : SuitableIntervalFamily n) (hbase : F.base.card = 0) :
    ∃ alpha : (↑F.base : Type) → ℝ,
      Erdos228.Discrepancy.IsSign alpha ∧
        ∀ j < n, |fourierTarget F alpha j| ≤ 1 := by
  classical
  have hempty : F.base = ∅ := Finset.card_eq_zero.mp hbase
  have hisEmpty : IsEmpty (↑F.base : Type) := Finset.isEmpty_coe_sort.mpr hempty
  let alpha : (↑F.base : Type) → ℝ := fun _ ↦ 1
  refine ⟨alpha, fun I ↦ Or.inl rfl, ?_⟩
  intro j hj
  simp [fourierTarget, hj]

end

end OddSine

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/Kernel.lean` -/

section
/-!
# Trigonometric-kernel lemmas for Erdős Problem 228

This file collects the elementary finite-sum and cancellation identities used in
the odd-sine correction part of the Balister--Bollobás--Morris--Sahasrabudhe--Tiba
construction.
-/

namespace Kernel

open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral

/-! ## Odd Dirichlet kernels -/

/-- The odd-cosine sum in a denominator-free form.  This is just the
telescoping identity
`2 sin(t) cos((2j+1)t) = sin(2(j+1)t) - sin(2jt)` summed over `j`. -/
lemma two_mul_sin_mul_oddCosSum (n : ℕ) (t : ℝ) :
    2 * Real.sin t * (∑ j ∈ Finset.range n,
      Real.cos (((2 * j + 1 : ℕ) : ℝ) * t)) =
      Real.sin ((2 * n : ℕ) * t) := by
  have hterm (j : ℕ) :
      2 * Real.sin t * Real.cos (((2 * j + 1 : ℕ) : ℝ) * t) =
        Real.sin (((2 * (j + 1) : ℕ) : ℝ) * t) -
          Real.sin (((2 * j : ℕ) : ℝ) * t) := by
    rw [Real.two_mul_sin_mul_cos]
    have hsub : t - ((2 * j + 1 : ℕ) : ℝ) * t =
        -(((2 * j : ℕ) : ℝ) * t) := by
      push_cast
      ring
    have hadd : t + ((2 * j + 1 : ℕ) : ℝ) * t =
        ((2 * (j + 1) : ℕ) : ℝ) * t := by
      push_cast
      ring
    rw [hsub, hadd, Real.sin_neg]
    ring
  calc
    2 * Real.sin t * (∑ j ∈ Finset.range n,
        Real.cos (((2 * j + 1 : ℕ) : ℝ) * t)) =
        ∑ j ∈ Finset.range n,
          (2 * Real.sin t * Real.cos (((2 * j + 1 : ℕ) : ℝ) * t)) := by
            rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range n,
        (Real.sin (((2 * (j + 1) : ℕ) : ℝ) * t) -
          Real.sin (((2 * j : ℕ) : ℝ) * t)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hterm j
    _ = Real.sin (((2 * n : ℕ) : ℝ) * t) - Real.sin 0 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, mul_zero, zero_mul,
        Real.sin_zero] using
        (Finset.sum_range_sub
          (fun j : ℕ => Real.sin (((2 * j : ℕ) : ℝ) * t)) n)
    _ = Real.sin ((2 * n : ℕ) * t) := by simp

/-- Quotient form of the finite odd-cosine identity. -/
lemma two_mul_oddCosSum_eq (n : ℕ) {t : ℝ} (ht : Real.sin t ≠ 0) :
    2 * (∑ j ∈ Finset.range n,
      Real.cos (((2 * j + 1 : ℕ) : ℝ) * t)) =
      Real.sin ((2 * n : ℕ) * t) / Real.sin t := by
  have h := two_mul_sin_mul_oddCosSum n t
  apply (eq_div_iff ht).2
  rw [← h]
  ring

/-- Product-to-sum in the normalization convenient for the odd kernel. -/
lemma two_mul_sin_mul_sin (u v : ℝ) :
    2 * Real.sin u * Real.sin v = Real.cos (u - v) - Real.cos (u + v) := by
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- The odd Dirichlet kernel identity used in the construction. -/
theorem odd_dirichlet_kernel (n : ℕ) {θ θ₀ : ℝ}
    (hsub : Real.sin (θ - θ₀) ≠ 0) (hadd : Real.sin (θ + θ₀) ≠ 0) :
    4 * (∑ j ∈ Finset.range n,
      Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ₀) *
        Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ)) =
      Real.sin ((2 * n : ℕ) * (θ - θ₀)) / Real.sin (θ - θ₀) -
        Real.sin ((2 * n : ℕ) * (θ + θ₀)) / Real.sin (θ + θ₀) := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_assoc, Finset.mul_sum]
  have hprod (j : ℕ) :
      2 * (Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ₀) *
        Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ)) =
        Real.cos (((2 * j + 1 : ℕ) : ℝ) * (θ - θ₀)) -
          Real.cos (((2 * j + 1 : ℕ) : ℝ) * (θ + θ₀)) := by
    calc
      2 * (Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ₀) *
          Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ)) =
          2 * Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ₀) *
            Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ) := by ring
      _ = Real.cos ((((2 * j + 1 : ℕ) : ℝ) * θ₀) -
            (((2 * j + 1 : ℕ) : ℝ) * θ)) -
          Real.cos ((((2 * j + 1 : ℕ) : ℝ) * θ₀) +
            (((2 * j + 1 : ℕ) : ℝ) * θ)) :=
        two_mul_sin_mul_sin _ _
      _ = Real.cos (((2 * j + 1 : ℕ) : ℝ) * (θ - θ₀)) -
          Real.cos (((2 * j + 1 : ℕ) : ℝ) * (θ + θ₀)) := by
            have hneg : (((2 * j + 1 : ℕ) : ℝ) * θ₀) -
                (((2 * j + 1 : ℕ) : ℝ) * θ) =
                -(((2 * j + 1 : ℕ) : ℝ) * (θ - θ₀)) := by ring
            have hplus : (((2 * j + 1 : ℕ) : ℝ) * θ₀) +
                (((2 * j + 1 : ℕ) : ℝ) * θ) =
                ((2 * j + 1 : ℕ) : ℝ) * (θ + θ₀) := by ring
            rw [hneg, Real.cos_neg, hplus]
  rw [Finset.sum_congr rfl (fun j _ => hprod j), Finset.sum_sub_distrib,
    mul_sub, two_mul_oddCosSum_eq n hsub, two_mul_oddCosSum_eq n hadd]

/-! ## Exact cancellation over a period -/

/-! ## Elementary Taylor and sine-integral bounds -/

/-- The fourth-order Taylor polynomial is an upper bound for cosine on the
nonnegative half-line.  The proof differentiates once and uses Mathlib's
global cubic lower bound for sine. -/
lemma cos_le_taylor_four {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f (t : ℝ) := 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hderiv (t : ℝ) :
      deriv f t = -t + t ^ 3 / 6 + Real.sin t := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hderiv]
    have ht0 : 0 ≤ t := by
      rw [interior_Ici, mem_Ioi] at ht
      exact ht.le
    linarith [Real.sin_ge_sub_cube ht0]
  have h := hmono (show (0 : ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 by exact hx) hx
  dsimp [f] at h
  norm_num at h
  exact h

/-- The fifth-order Taylor polynomial is an upper bound for sine on the
nonnegative half-line. -/
lemma sin_le_taylor_five {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f (t : ℝ) := t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t
  have hderiv (t : ℝ) :
      deriv f t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hderiv]
    have ht0 : 0 ≤ t := by
      rw [interior_Ici, mem_Ioi] at ht
      exact ht.le
    linarith [cos_le_taylor_four ht0]
  have h := hmono (show (0 : ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 by exact hx) hx
  dsimp [f] at h
  norm_num at h
  exact h

/-- The corresponding quartic upper bound for sinc. -/
lemma sinc_le_taylor_four {x : ℝ} (hx : 0 ≤ x) :
    Real.sinc x ≤ 1 - x ^ 2 / 6 + x ^ 4 / 120 := by
  obtain rfl | hxpos := hx.eq_or_lt
  · norm_num
  rw [Real.sinc_of_ne_zero hxpos.ne']
  apply (div_le_iff₀ hxpos).2
  nlinarith [sin_le_taylor_five hxpos.le]

/-- The unnormalized sine integral `Si(b)`, expressed using the continuous
extension of `sin x / x` at the origin. -/
noncomputable def sineIntegral (b : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..b, Real.sinc x

/-- Integrating the quartic upper Taylor bound for sinc. -/
lemma sineIntegral_upper {b : ℝ} (hb : 0 ≤ b) :
    sineIntegral b ≤ b - b ^ 3 / 18 + b ^ 5 / 600 := by
  have hs : IntervalIntegrable Real.sinc volume 0 b :=
    Real.continuous_sinc.intervalIntegrable 0 b
  have hp1 : IntervalIntegrable (fun x : ℝ => 1 - x ^ 2 / 6) volume 0 b :=
    (by fun_prop : Continuous (fun x : ℝ => 1 - x ^ 2 / 6)).intervalIntegrable 0 b
  have hp2 : IntervalIntegrable (fun x : ℝ => x ^ 4 / 120) volume 0 b :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 4 / 120)).intervalIntegrable 0 b
  have hp : IntervalIntegrable
      (fun x : ℝ => 1 - x ^ 2 / 6 + x ^ 4 / 120) volume 0 b := hp1.add hp2
  have hmono := intervalIntegral.integral_mono_on hb hs hp
    (fun x hx => sinc_le_taylor_four hx.1)
  calc
    sineIntegral b = ∫ x in (0 : ℝ)..b, Real.sinc x := rfl
    _ ≤ ∫ x in (0 : ℝ)..b, (1 - x ^ 2 / 6 + x ^ 4 / 120) := hmono
    _ = b - b ^ 3 / 18 + b ^ 5 / 600 := by
      rw [intervalIntegral.integral_add hp1 hp2]
      simp [intervalIntegral.integral_sub, intervalIntegral.integral_div, integral_pow]
      ring

/-- A concrete upper bound at `π`, obtained by integrating the fifth-order
Taylor bound for sine. -/
theorem sineIntegral_pi_lt_two : sineIntegral Real.pi < 2 := by
  have hSi := sineIntegral_upper Real.pi_pos.le
  have hpi : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hcube : (3.14 : ℝ) ^ 3 < Real.pi ^ 3 :=
    pow_lt_pow_left₀ Real.pi_gt_d2 (by norm_num) (by norm_num)
  have hfifth : Real.pi ^ 5 < (3.15 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le (by norm_num)
  norm_num at hpi hcube hfifth ⊢
  nlinarith

end Kernel

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/OddKernelIdentity.lean` -/

section
/-!
# The exact finite odd-kernel identity

This file records the algebraic identity behind the odd-sine target in
`OddSine`.  In particular, it does not assume any of the analytic kernel
estimates packaged by `OddSine.KernelCertificate`.
-/

namespace OddKernelIdentity

open scoped BigOperators Interval
open Set MeasureTheory

noncomputable section

/-- The finite odd sine kernel, with the normalization used in BBMST
Section 5. -/
def oddKernel (n : ℕ) (x theta : ℝ) : ℝ :=
  4 * ∑ j ∈ Finset.range n,
    Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * x) *
      Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * theta)

/-- The odd kernel integrated over an oriented real interval. -/
def integratedOddKernel (n : ℕ) (I : Erdos228.OddSine.RealInterval)
    (theta : ℝ) : ℝ :=
  ∫ x in I.1..I.2, oddKernel n x theta

/-- Integrating the finite odd kernel is the same as integrating its
individual sine modes. -/
theorem integratedOddKernel_eq_sum (n : ℕ)
    (I : Erdos228.OddSine.RealInterval) (theta : ℝ) :
    integratedOddKernel n I theta =
      4 * ∑ j ∈ Finset.range n,
        (∫ x in I.1..I.2,
          Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * x)) *
            Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * theta) := by
  classical
  simp only [integratedOddKernel, oddKernel,
    intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_mul_const]
  · intro j hj
    exact (by fun_prop : Continuous (fun x : ℝ ↦
      Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * x) *
        Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * theta))).intervalIntegrable _ _

/-- Exact reconstruction of `OddSine.targetSine` from the integrated finite
odd kernel on the coloured base intervals.  This identity is valid even for
`n = 0`; positivity is needed only when dividing by the normalization. -/
theorem targetSine_eq_sum_integratedOddKernel {n : ℕ}
    (F : Erdos228.OddSine.SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) :
    Erdos228.OddSine.targetSine F alpha theta =
      (Erdos228.OddSine.K * Real.sqrt n) *
        ∑ I : (↑F.base : Type), alpha I * integratedOddKernel n I.1 theta := by
  classical
  rw [show Erdos228.OddSine.targetSine F alpha theta =
      ∑ j ∈ Finset.range n,
        (∑ I : (↑F.base : Type),
          alpha I * (4 * Erdos228.OddSine.K * Real.sqrt n *
            ∫ x in I.1.1..I.1.2,
              Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * x))) *
          Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * theta) by
    simp only [Erdos228.OddSine.targetSine,
      Erdos228.Rounding.oddSineSum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Erdos228.OddSine.fourierTarget,
      dif_pos (Finset.mem_range.mp hj)]
  ]
  simp_rw [integratedOddKernel_eq_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The normalized target is exactly the signed sum of integrated finite odd
kernels. -/
theorem targetSine_div_eq_sum_integratedOddKernel {n : ℕ} (hn : 0 < n)
    (F : Erdos228.OddSine.SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) :
    Erdos228.OddSine.targetSine F alpha theta /
        (Erdos228.OddSine.K * Real.sqrt n) =
      ∑ I : (↑F.base : Type), alpha I * integratedOddKernel n I.1 theta := by
  rw [targetSine_eq_sum_integratedOddKernel]
  exact mul_div_cancel_left₀ _ (mul_ne_zero (by norm_num [Erdos228.OddSine.K])
    (Real.sqrt_ne_zero'.2 (by exact_mod_cast hn)))

/-- Away from its removable singularities, the finite odd kernel has the
usual quotient form. -/
theorem oddKernel_eq_quotient (n : ℕ) {x theta : ℝ}
    (hsub : Real.sin (x - theta) ≠ 0)
    (hadd : Real.sin (x + theta) ≠ 0) :
    oddKernel n x theta =
      Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
        Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta) := by
  simpa [oddKernel, Erdos228.Rounding.oddFrequency, mul_comm] using
    (Erdos228.Kernel.odd_dirichlet_kernel n
      (θ := x) (θ₀ := theta) hsub hadd)

/-- If `x` is in the open first quadrant and `theta` is in the closed first
quadrant, the only possible singularity of the quotient form is the diagonal
`x = theta`. -/
theorem oddKernel_eq_quotient_of_theta_mem_Icc (n : ℕ) {x theta : ℝ}
    (hx₀ : 0 < x) (hx₁ : x < Real.pi / 2)
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hxt : x ≠ theta) :
    oddKernel n x theta =
      Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
        Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta) := by
  rcases htheta with ⟨ht₀, ht₁⟩
  apply oddKernel_eq_quotient
  · intro hzero
    have hdiff : x - theta = 0 :=
      (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])).mp hzero
    exact hxt (sub_eq_zero.mp hdiff)
  · intro hzero
    have hsum : x + theta = 0 :=
      (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])).mp hzero
    linarith

/-- The quotient form may be integrated over an interval lying strictly in
the first quadrant while the evaluation angle ranges over the closed first
quadrant.  The diagonal singularity is discarded as a null singleton. -/
theorem integral_oddKernel_eq_quotient_of_theta_mem_Icc (n : ℕ)
    {a b theta : ℝ} (hab : a ≤ b) (ha : 0 < a) (hb : b < Real.pi / 2)
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (∫ x in a..b, oddKernel n x theta) =
      ∫ x in a..b,
        (Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
          Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta)) := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume theta] with x hxt hx
  rw [uIoc_of_le hab] at hx
  exact oddKernel_eq_quotient_of_theta_mem_Icc n
    (ha.trans hx.1) (hx.2.trans_lt hb) htheta hxt

/-- Every base interval of a suitable family admits the integrated quotient
form for evaluation angles in the closed first quadrant. -/
theorem integratedOddKernel_eq_quotient_of_mem_base_theta_mem_Icc {n : ℕ}
    (hn : 0 < n) (F : Erdos228.OddSine.SuitableIntervalFamily n)
    (I : Erdos228.OddSine.RealInterval) (hI : I ∈ F.base)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    integratedOddKernel n I theta =
      ∫ x in I.1..I.2,
        (Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
          Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta)) := by
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  have hmesh : 0 < 100 * Real.pi / (n : ℝ) := by positivity
  apply integral_oddKernel_eq_quotient_of_theta_mem_Icc n
  · exact F.ordered I hI
  · linarith [F.away_from_axes I hI |>.1]
  · linarith [F.away_from_axes I hI |>.2]
  · exact htheta

/-- Closed-first-quadrant quotient-integral form of the normalized target.
This is the direct form consumed by kernel estimates on the base intervals. -/
theorem targetSine_div_eq_sum_quotientIntegral_of_theta_mem_Icc {n : ℕ}
    (hn : 0 < n) (F : Erdos228.OddSine.SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    Erdos228.OddSine.targetSine F alpha theta /
        (Erdos228.OddSine.K * Real.sqrt n) =
      ∑ I : (↑F.base : Type), alpha I *
        ∫ x in I.1.1..I.1.2,
          (Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
            Real.sin ((2 * n : ℕ) * (x + theta)) /
              Real.sin (x + theta)) := by
  rw [targetSine_div_eq_sum_integratedOddKernel hn]
  apply Finset.sum_congr rfl
  intro I hI
  rw [integratedOddKernel_eq_quotient_of_mem_base_theta_mem_Icc
    hn F I.1 I.2 htheta]

end

end OddKernelIdentity

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/KernelNearGeometry.lean` -/

section
/-!
# Finite near-interval geometry for the odd kernel

This file packages the elementary one-dimensional geometry used when the
BBMST odd kernel is split into its interval contributions.  For a point
`theta`, the base intervals within one grid spacing `pi / n` form a finite
set.  If `theta` is in a base interval, separation makes that interval the
only near interval.  If `theta` is outside their union, at most one near
interval can lie on either side, hence there are at most two in total.
-/

namespace KernelNearGeometry

open scoped BigOperators
open Set

noncomputable section

open Erdos228.OddSine

/-- The (nonnegative) gap from `theta` to the closed interval represented by
`I`.  It is written explicitly rather than through `Metric.infDist`, so the
left/right endpoint selected by the kernel estimates is visible to Lean. -/
def intervalGap (theta : ℝ) (I : RealInterval) : ℝ :=
  max (I.1 - theta) (max (theta - I.2) 0)

theorem intervalGap_eq_zero_of_mem {theta : ℝ} {I : RealInterval}
    (htheta : InInterval I theta) :
    intervalGap theta I = 0 := by
  rw [InInterval, mem_Icc] at htheta
  simp only [intervalGap]
  rw [max_eq_right (sub_nonpos.mpr htheta.2)]
  rw [max_eq_right (sub_nonpos.mpr htheta.1)]

theorem intervalGap_eq_left {theta : ℝ} {I : RealInterval}
    (hI : I.1 ≤ I.2) (htheta : theta ≤ I.1) :
    intervalGap theta I = I.1 - theta := by
  have htheta' : theta ≤ I.2 := htheta.trans hI
  simp only [intervalGap]
  rw [max_eq_right (sub_nonpos.mpr htheta')]
  rw [max_eq_left (sub_nonneg.mpr htheta)]

theorem intervalGap_eq_right {theta : ℝ} {I : RealInterval}
    (hI : I.1 ≤ I.2) (htheta : I.2 ≤ theta) :
    intervalGap theta I = theta - I.2 := by
  have htheta' : I.1 ≤ theta := hI.trans htheta
  simp only [intervalGap]
  rw [max_eq_left (sub_nonneg.mpr htheta)]
  rw [max_eq_right]
  exact (sub_nonpos.mpr htheta').trans (sub_nonneg.mpr htheta)

/-- An interval is near `theta` when its closed-interval gap is strictly less
than one grid spacing. -/
def Near (n : ℕ) (theta : ℝ) (I : RealInterval) : Prop :=
  intervalGap theta I < Real.pi / n

/-- The finite collection of base intervals near `theta`. -/
noncomputable def nearIntervals {n : ℕ} (F : SuitableIntervalFamily n) (theta : ℝ) :
    Finset RealInterval :=
  @Finset.filter _ (Near n theta) (Classical.decPred _) F.base

/-- The union-membership predicate for the base interval family. -/
def InBaseUnion {n : ℕ} (F : SuitableIntervalFamily n) (theta : ℝ) : Prop :=
  ∃ I ∈ F.base, InInterval I theta

/-- Near intervals strictly to the left of `theta`. -/
noncomputable def nearLeftIntervals {n : ℕ} (F : SuitableIntervalFamily n) (theta : ℝ) :
    Finset RealInterval :=
  @Finset.filter _ (fun I ↦ Near n theta I ∧ I.2 < theta)
    (Classical.decPred _) F.base

/-- Near intervals strictly to the right of `theta`. -/
noncomputable def nearRightIntervals {n : ℕ} (F : SuitableIntervalFamily n) (theta : ℝ) :
    Finset RealInterval :=
  @Finset.filter _ (fun I ↦ Near n theta I ∧ theta < I.1)
    (Classical.decPred _) F.base

/-- The same near collection indexed by the subtype used by the odd-kernel
coefficients. -/
noncomputable def nearBaseIntervals {n : ℕ} (F : SuitableIntervalFamily n)
    (theta : ℝ) : Finset (↑F.base : Type) :=
  @Finset.filter (↑F.base : Type) (fun I ↦ Near n theta I.1)
    (Classical.decPred _) Finset.univ

/-- Forgetting subtype membership identifies the subtype-indexed and
endpoint-indexed near collections. -/
theorem nearIntervals_eq_image_nearBaseIntervals {n : ℕ}
    (F : SuitableIntervalFamily n) (theta : ℝ) :
    nearIntervals F theta =
      (nearBaseIntervals F theta).image (fun I ↦ I.1) := by
  classical
  ext I
  simp [nearIntervals, nearBaseIntervals, and_comm]

/-- Two base intervals containing the same point are equal. -/
theorem eq_of_mem_intervals {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I J : RealInterval}
    (hI : I ∈ F.base) (hJ : J ∈ F.base)
    (hthetaI : InInterval I theta) (hthetaJ : InInterval J theta) :
    I = J := by
  by_contra hne
  have hsep := F.separated hI hJ hne theta hthetaI theta hthetaJ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  exact (not_le_of_gt hpi) (by simpa using hsep)

/-- If `theta` belongs to `I`, every other base interval has gap at least one
grid spacing. -/
theorem intervalGap_ge_of_mem_of_ne {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I J : RealInterval}
    (hI : I ∈ F.base) (hJ : J ∈ F.base) (hne : I ≠ J)
    (htheta : InInterval I theta) :
    Real.pi / n ≤ intervalGap theta J := by
  have hnotJ : ¬InInterval J theta := by
    intro hthetaJ
    exact hne (eq_of_mem_intervals hn F hI hJ htheta hthetaJ)
  rw [InInterval, mem_Icc] at hnotJ
  rcases not_and_or.mp hnotJ with hleft | hright
  · have hleft' : theta < J.1 := lt_of_not_ge hleft
    rw [intervalGap_eq_left (F.ordered J hJ) hleft'.le]
    have hsep := F.separated hI hJ hne theta htheta J.1
      ⟨le_rfl, F.ordered J hJ⟩
    rw [abs_of_neg (sub_neg.mpr hleft')] at hsep
    linarith
  · have hright' : J.2 < theta := lt_of_not_ge hright
    rw [intervalGap_eq_right (F.ordered J hJ) hright'.le]
    have hsep := F.separated hI hJ hne theta htheta J.2
      ⟨F.ordered J hJ, le_rfl⟩
    rw [abs_of_pos (sub_pos.mpr hright')] at hsep
    exact hsep

/-- A point of a base interval has exactly that interval in its near set. -/
theorem nearIntervals_eq_singleton_of_mem {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ F.base) (htheta : InInterval I theta) :
    nearIntervals F theta = {I} := by
  classical
  ext J
  simp only [nearIntervals, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hJ, hnear⟩
    by_contra hJI
    have hgap := intervalGap_ge_of_mem_of_ne hn F hI hJ
      (fun h ↦ hJI h.symm) htheta
    exact (not_lt_of_ge hgap) hnear
  · intro hJI
    subst J
    refine ⟨hI, ?_⟩
    rw [Near, intervalGap_eq_zero_of_mem htheta]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos Real.pi_pos hnR

/-- Subtype-indexed version of `nearIntervals_eq_singleton_of_mem`. -/
theorem nearBaseIntervals_eq_singleton_of_mem {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ F.base) (htheta : InInterval I theta) :
    nearBaseIntervals F theta = {⟨I, hI⟩} := by
  classical
  ext J
  simp only [nearBaseIntervals, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hnear
    apply Subtype.ext
    by_contra hne
    have hgap := intervalGap_ge_of_mem_of_ne hn F hI J.property
      (fun h ↦ hne h.symm) htheta
    exact (not_lt_of_ge hgap) hnear
  · intro hJI
    subst J
    rw [Near, intervalGap_eq_zero_of_mem htheta]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos Real.pi_pos hnR

/-- The endpoint and subtype versions have the same cardinality. -/
theorem card_nearBaseIntervals_eq_card_nearIntervals {n : ℕ}
    (F : SuitableIntervalFamily n) (theta : ℝ) :
    (nearBaseIntervals F theta).card = (nearIntervals F theta).card := by
  rw [nearIntervals_eq_image_nearBaseIntervals]
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm

/-- Outside the union, every near interval is either strictly left or
strictly right of the point. -/
theorem nearIntervals_eq_left_union_right_of_not_inBaseUnion {n : ℕ}
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (hout : ¬InBaseUnion F theta) :
    nearIntervals F theta =
      nearLeftIntervals F theta ∪ nearRightIntervals F theta := by
  classical
  ext I
  simp only [nearIntervals, nearLeftIntervals, nearRightIntervals,
    Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hI, hnear⟩
    have hnot : ¬InInterval I theta := fun h ↦ hout ⟨I, hI, h⟩
    rw [InInterval, mem_Icc] at hnot
    rcases not_and_or.mp hnot with hright | hleft
    · exact Or.inr ⟨hI, hnear, lt_of_not_ge hright⟩
    · exact Or.inl ⟨hI, hnear, lt_of_not_ge hleft⟩
  · rintro (hleft | hright)
    · exact ⟨hleft.1, hleft.2.1⟩
    · exact ⟨hright.1, hright.2.1⟩

/-- At most one near interval lies strictly to the left of a point. -/
theorem card_nearLeftIntervals_le_one {n : ℕ} (_hn : 0 < n)
    (F : SuitableIntervalFamily n) (theta : ℝ) :
    (nearLeftIntervals F theta).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro I hI J hJ
  simp only [nearLeftIntervals, Finset.mem_filter] at hI hJ
  by_contra hne
  have hsep := F.separated hI.1 hJ.1 hne I.2
    ⟨F.ordered I hI.1, le_rfl⟩ J.2 ⟨F.ordered J hJ.1, le_rfl⟩
  have hgapI : theta - I.2 < Real.pi / n := by
    rw [← intervalGap_eq_right (F.ordered I hI.1) hI.2.2.le]
    exact hI.2.1
  have hgapJ : theta - J.2 < Real.pi / n := by
    rw [← intervalGap_eq_right (F.ordered J hJ.1) hJ.2.2.le]
    exact hJ.2.1
  have habs : |I.2 - J.2| < Real.pi / n := by
    rw [abs_lt]
    constructor <;> linarith [hI.2.2, hJ.2.2]
  exact (not_lt_of_ge hsep) habs

/-- At most one near interval lies strictly to the right of a point. -/
theorem card_nearRightIntervals_le_one {n : ℕ} (_hn : 0 < n)
    (F : SuitableIntervalFamily n) (theta : ℝ) :
    (nearRightIntervals F theta).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro I hI J hJ
  simp only [nearRightIntervals, Finset.mem_filter] at hI hJ
  by_contra hne
  have hsep := F.separated hI.1 hJ.1 hne I.1
    ⟨le_rfl, F.ordered I hI.1⟩ J.1 ⟨le_rfl, F.ordered J hJ.1⟩
  have hgapI : I.1 - theta < Real.pi / n := by
    rw [← intervalGap_eq_left (F.ordered I hI.1) hI.2.2.le]
    exact hI.2.1
  have hgapJ : J.1 - theta < Real.pi / n := by
    rw [← intervalGap_eq_left (F.ordered J hJ.1) hJ.2.2.le]
    exact hJ.2.1
  have habs : |I.1 - J.1| < Real.pi / n := by
    rw [abs_lt]
    constructor <;> linarith [hI.2.2, hJ.2.2]
  exact (not_lt_of_ge hsep) habs

/-- Outside the base union, fewer than one grid spacing from `theta` can
hold for at most two base intervals. -/
theorem card_nearIntervals_le_two_of_not_inBaseUnion {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (hout : ¬InBaseUnion F theta) :
    (nearIntervals F theta).card ≤ 2 := by
  rw [nearIntervals_eq_left_union_right_of_not_inBaseUnion F hout]
  calc
    (nearLeftIntervals F theta ∪ nearRightIntervals F theta).card ≤
        (nearLeftIntervals F theta).card +
          (nearRightIntervals F theta).card :=
      Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add
      (card_nearLeftIntervals_le_one hn F theta)
      (card_nearRightIntervals_le_one hn F theta)
    _ = 2 := rfl

/-- Subtype-indexed cardinality bound used directly in odd-kernel sums. -/
theorem card_nearBaseIntervals_le_two_of_not_inBaseUnion {n : ℕ}
    (hn : 0 < n) (F : SuitableIntervalFamily n) {theta : ℝ}
    (hout : ¬InBaseUnion F theta) :
    (nearBaseIntervals F theta).card ≤ 2 := by
  rw [card_nearBaseIntervals_eq_card_nearIntervals]
  exact card_nearIntervals_le_two_of_not_inBaseUnion hn F hout

/-- In the first quadrant, the fourfold definition of `IsDangerous` reduces
to membership in one base interval.  Separation makes that interval unique. -/
theorem existsUnique_baseInterval_of_dangerous_firstQuadrant {n : ℕ}
    (hn : 0 < n) (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hdangerous : IsDangerous F theta) :
    ∃! I : RealInterval, I ∈ F.base ∧ InInterval I theta := by
  rcases hdangerous with ⟨I, hI, hmain | hneg | hreflect | htranslate⟩
  · refine ⟨I, ⟨hI, hmain⟩, ?_⟩
    rintro J ⟨hJ, hthetaJ⟩
    exact eq_of_mem_intervals hn F hJ hI hthetaJ hmain
  · have hquadI := F.in_first_quadrant I hI
    rw [InInterval, mem_Icc] at hneg
    have htheta0 : theta = 0 := by linarith [htheta.1, hquadI.1, hneg.1]
    have hmain : InInterval I theta := by
      rw [InInterval, mem_Icc]
      simpa [htheta0] using hneg
    refine ⟨I, ⟨hI, hmain⟩, ?_⟩
    rintro J ⟨hJ, hthetaJ⟩
    exact eq_of_mem_intervals hn F hJ hI hthetaJ hmain
  · have hquadI := F.in_first_quadrant I hI
    rw [InInterval, mem_Icc] at hreflect
    have hthetaMid : theta = Real.pi / 2 := by
      linarith [htheta.2, hquadI.2, hreflect.2]
    have harg : Real.pi - theta = theta := by
      rw [hthetaMid]
      ring
    have hmain : InInterval I theta := by
      rw [InInterval, mem_Icc, ← harg]
      exact hreflect
    refine ⟨I, ⟨hI, hmain⟩, ?_⟩
    rintro J ⟨hJ, hthetaJ⟩
    exact eq_of_mem_intervals hn F hJ hI hthetaJ hmain
  · have hquadI := F.in_first_quadrant I hI
    rw [InInterval, mem_Icc] at htranslate
    exfalso
    nlinarith [htheta.2, hquadI.1, htranslate.1, Real.pi_pos]

/-- Subtype-indexed unique interval for a dangerous first-quadrant point. -/
theorem existsUnique_baseSubtype_of_dangerous_firstQuadrant {n : ℕ}
    (hn : 0 < n) (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hdangerous : IsDangerous F theta) :
    ∃! I : (↑F.base : Type), InInterval I.1 theta := by
  obtain ⟨I, hI, hunique⟩ :=
    existsUnique_baseInterval_of_dangerous_firstQuadrant hn F htheta hdangerous
  refine ⟨⟨I, hI.1⟩, hI.2, ?_⟩
  intro J hthetaJ
  apply Subtype.ext
  exact hunique J.1 ⟨J.property, hthetaJ⟩

/-- Subtype-indexed exact near-sum formula at a point of a base interval. -/
theorem sum_nearBaseIntervals_eq_of_mem {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ F.base) (htheta : InInterval I theta)
    (f : (↑F.base : Type) → ℝ) :
    ∑ J ∈ nearBaseIntervals F theta, f J = f ⟨I, hI⟩ := by
  rw [nearBaseIntervals_eq_singleton_of_mem hn F hI htheta]
  simp

/-- Subtype-indexed two-term sum bound used by the kernel assembly. -/
theorem abs_sum_nearBaseIntervals_le_two_mul_of_not_inBaseUnion {n : ℕ}
    (hn : 0 < n) (F : SuitableIntervalFamily n) {theta C : ℝ}
    (hout : ¬InBaseUnion F theta) (hC : 0 ≤ C)
    (f : (↑F.base : Type) → ℝ)
    (hf : ∀ I ∈ nearBaseIntervals F theta, |f I| ≤ C) :
    |∑ I ∈ nearBaseIntervals F theta, f I| ≤ 2 * C := by
  classical
  have hcard := card_nearBaseIntervals_le_two_of_not_inBaseUnion hn F hout
  calc
    |∑ I ∈ nearBaseIntervals F theta, f I| ≤
        ∑ I ∈ nearBaseIntervals F theta, |f I| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _I ∈ nearBaseIntervals F theta, C := by
      exact Finset.sum_le_sum fun I hI ↦ hf I hI
    _ = ((nearBaseIntervals F theta).card : ℝ) * C := by simp
    _ ≤ 2 * C := by
      gcongr
      exact_mod_cast hcard

end

end KernelNearGeometry

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/SineIntegralGrid.lean` -/

section
namespace SineIntegralGrid

open scoped Interval
open Real Set MeasureTheory intervalIntegral

noncomputable section

private def lowerSincPolynomial (x : ℝ) : ℝ :=
  1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040

private def geometricLower (x : ℝ) : ℝ :=
  1 - x / Real.pi + (x / Real.pi) ^ 2 - (x / Real.pi) ^ 3

/-- The next alternating Taylor truncation after the estimates in `Kernel`. -/
private lemma sin_taylor_seven_le {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := by
  let q (t : ℝ) := Real.cos t -
    (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720)
  have hqderiv (t : ℝ) :
      deriv q t = -Real.sin t + t - t ^ 3 / 6 + t ^ 5 / 120 := by
    simp (disch := fun_prop) [q]
    ring
  have hqmono : MonotoneOn q (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hqderiv]
    have ht0 : 0 ≤ t := by
      rw [interior_Ici, mem_Ioi] at ht
      exact ht.le
    linarith [Erdos228.Kernel.sin_le_taylor_five ht0]
  have hq {t : ℝ} (ht : 0 ≤ t) :
      1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 ≤ Real.cos t := by
    have h := hqmono (show (0 : ℝ) ∈ Ici 0 by simp)
      (show t ∈ Ici 0 by exact ht) ht
    dsimp [q] at h
    norm_num at h
    linarith
  let f (t : ℝ) := Real.sin t -
    (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040)
  have hfderiv (t : ℝ) :
      deriv f t = Real.cos t -
        (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) := by
    simp (disch := fun_prop) [f]
    ring
  have hfmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hfderiv]
    have ht0 : 0 ≤ t := by
      rw [interior_Ici, mem_Ioi] at ht
      exact ht.le
    linarith [hq ht0]
  have h := hfmono (show (0 : ℝ) ∈ Ici 0 by simp)
    (show x ∈ Ici 0 by exact hx) hx
  dsimp [f] at h
  norm_num at h
  linarith

private lemma lowerSincPolynomial_le_sinc {x : ℝ} (hx : 0 ≤ x) :
    lowerSincPolynomial x ≤ Real.sinc x := by
  obtain rfl | hxpos := hx.eq_or_lt
  · norm_num [lowerSincPolynomial]
  rw [Real.sinc_of_ne_zero hxpos.ne']
  apply (le_div_iff₀ hxpos).2
  have h := sin_taylor_seven_le hxpos.le
  dsimp [lowerSincPolynomial]
  nlinarith

private lemma sinc_nonneg_on_zero_pi {x : ℝ} (hx0 : 0 ≤ x)
    (hxpi : x ≤ Real.pi) : 0 ≤ Real.sinc x := by
  obtain rfl | hxpos := hx0.eq_or_lt
  · simp
  rw [Real.sinc_of_ne_zero hxpos.ne']
  exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxpi) hx0

private lemma geometricLower_nonneg {x : ℝ} (hx0 : 0 ≤ x)
    (hxpi : x ≤ Real.pi) : 0 ≤ geometricLower x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hu0 : 0 ≤ x / Real.pi := div_nonneg hx0 hpi.le
  have hu1 : x / Real.pi ≤ 1 := (div_le_one hpi).2 hxpi
  dsimp [geometricLower]
  nlinarith [sq_nonneg (x / Real.pi)]

private lemma geometricLower_le_weight {x : ℝ} (hx0 : 0 ≤ x)
    (hxpi : x ≤ Real.pi) :
    geometricLower x ≤ Real.pi / (x + Real.pi) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hxpi_pos : 0 < x + Real.pi := add_pos_of_nonneg_of_pos hx0 hpi
  apply (le_div_iff₀ hxpi_pos).2
  dsimp [geometricLower]
  field_simp
  ring_nf
  nlinarith [sq_nonneg (x ^ 2)]

private lemma sinc_add_pi_eq_weight (x : ℝ) (hx0 : 0 ≤ x)
    (hxpi : x ≤ Real.pi) :
    Real.sinc x + Real.sinc (x + Real.pi) =
      Real.sinc x * (Real.pi / (x + Real.pi)) := by
  by_cases hx : x = 0
  · subst x
    simp [Real.sinc_of_ne_zero Real.pi_ne_zero]
  have hxpi0 : x + Real.pi ≠ 0 := by positivity
  rw [Real.sinc_of_ne_zero hx, Real.sinc_of_ne_zero hxpi0, Real.sin_add_pi]
  field_simp
  ring

private lemma polynomial_pair_le (x : ℝ) (hx : x ∈ Icc (0 : ℝ) Real.pi) :
    lowerSincPolynomial x * geometricLower x ≤
      Real.sinc x + Real.sinc (x + Real.pi) := by
  have hsinc0 := sinc_nonneg_on_zero_pi hx.1 hx.2
  have hpoly := lowerSincPolynomial_le_sinc hx.1
  have hgeom0 := geometricLower_nonneg hx.1 hx.2
  have hweight := geometricLower_le_weight hx.1 hx.2
  rw [sinc_add_pi_eq_weight x hx.1 hx.2]
  exact (mul_le_mul_of_nonneg_right hpoly hgeom0).trans
    (mul_le_mul_of_nonneg_left hweight hsinc0)

private lemma integral_polynomial_pair :
    (∫ x in (0 : ℝ)..Real.pi,
      lowerSincPolynomial x * geometricLower x) =
      -(73 * Real.pi ^ 7) / 12700800 +
        43 * Real.pi ^ 5 / 100800 - 7 * Real.pi ^ 3 / 360 +
          7 * Real.pi / 12 := by
  let F (x : ℝ) :=
    -x ^ 7 / 35280 + x ^ 5 / 600 - x ^ 3 / 18 + x +
    x ^ 8 / (40320 * Real.pi) - x ^ 6 / (720 * Real.pi) +
    x ^ 4 / (24 * Real.pi) - x ^ 2 / (2 * Real.pi) -
    x ^ 9 / (45360 * Real.pi ^ 2) + x ^ 7 / (840 * Real.pi ^ 2) -
    x ^ 5 / (30 * Real.pi ^ 2) + x ^ 3 / (3 * Real.pi ^ 2) +
    x ^ 10 / (50400 * Real.pi ^ 3) - x ^ 8 / (960 * Real.pi ^ 3) +
    x ^ 6 / (36 * Real.pi ^ 3) - x ^ 4 / (4 * Real.pi ^ 3)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := F) (f' := fun x => lowerSincPolynomial x * geometricLower x)]
  · dsimp [F]
    field_simp [Real.pi_ne_zero]
    ring
  · intro x hx
    have hdiff : DifferentiableAt ℝ F x := by
      dsimp [F]
      fun_prop
    have hderiv : deriv F x =
        lowerSincPolynomial x * geometricLower x := by
      simp (disch := fun_prop) [F, lowerSincPolynomial, geometricLower]
      field_simp [Real.pi_ne_zero]
      ring
    rw [← hderiv]
    exact hdiff.hasDerivAt
  · exact (by fun_prop : Continuous
      (fun x : ℝ => (1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040) *
        (1 - x / Real.pi + (x / Real.pi) ^ 2 - (x / Real.pi) ^ 3))).intervalIntegrable _ _

private lemma four_thirds_lt_integral_polynomial_pair :
    (4 : ℝ) / 3 < ∫ x in (0 : ℝ)..Real.pi,
      lowerSincPolynomial x * geometricLower x := by
  rw [integral_polynomial_pair]
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi' : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have h3 : Real.pi ^ 3 < (3.15 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hpi' Real.pi_pos.le (by norm_num)
  have h5 : (3.14 : ℝ) ^ 5 < Real.pi ^ 5 :=
    pow_lt_pow_left₀ hpi (by norm_num) (by norm_num)
  have h7 : Real.pi ^ 7 < (3.15 : ℝ) ^ 7 :=
    pow_lt_pow_left₀ hpi' Real.pi_pos.le (by norm_num)
  norm_num at hpi hpi' h3 h5 h7 ⊢
  linarith

/-- The first complete `2π` block of sinc already exceeds `4/3`. -/
theorem four_thirds_lt_sineIntegral_two_pi :
    (4 : ℝ) / 3 < Erdos228.Kernel.sineIntegral (2 * Real.pi) := by
  have hsinc : IntervalIntegrable Real.sinc volume (0 : ℝ) Real.pi :=
    Real.continuous_sinc.intervalIntegrable _ _
  have hsinc' : IntervalIntegrable (fun x : ℝ => Real.sinc (x + Real.pi))
      volume (0 : ℝ) Real.pi :=
    (Real.continuous_sinc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hpoly : IntervalIntegrable
      (fun x : ℝ => lowerSincPolynomial x * geometricLower x)
      volume (0 : ℝ) Real.pi :=
    (by fun_prop : Continuous
      (fun x : ℝ => (1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040) *
        (1 - x / Real.pi + (x / Real.pi) ^ 2 - (x / Real.pi) ^ 3))).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on Real.pi_pos.le hpoly
    (hsinc.add hsinc') polynomial_pair_le
  calc
    (4 : ℝ) / 3 < ∫ x in (0 : ℝ)..Real.pi,
        lowerSincPolynomial x * geometricLower x :=
      four_thirds_lt_integral_polynomial_pair
    _ ≤ ∫ x in (0 : ℝ)..Real.pi,
        (Real.sinc x + Real.sinc (x + Real.pi)) := hmono
    _ = Erdos228.Kernel.sineIntegral (2 * Real.pi) := by
      rw [intervalIntegral.integral_add hsinc hsinc']
      rw [intervalIntegral.integral_comp_add_right Real.sinc Real.pi]
      have hadd := intervalIntegral.integral_add_adjacent_intervals hsinc
        (Real.continuous_sinc.intervalIntegrable Real.pi (2 * Real.pi))
      unfold Erdos228.Kernel.sineIntegral
      convert hadd using 1 <;> ring

private def evenPoint (k : ℕ) : ℝ := (k : ℝ) * (2 * Real.pi)

private lemma evenPoint_nonneg (k : ℕ) : 0 ≤ evenPoint k := by
  exact mul_nonneg (Nat.cast_nonneg k) (by positivity)

private lemma evenPoint_pos {k : ℕ} (hk : 0 < k) : 0 < evenPoint k := by
  dsimp [evenPoint]
  exact mul_pos (by exact_mod_cast hk) (by positivity)

private lemma sin_evenPoint_add (k : ℕ) (x : ℝ) :
    Real.sin (evenPoint k + x) = Real.sin x := by
  rw [add_comm]
  exact Real.sin_add_nat_mul_two_pi x k

private lemma sinc_even_pair_nonneg {k : ℕ} (hk : 0 < k)
    {x : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi) :
    0 ≤ Real.sinc (evenPoint k + x) +
      Real.sinc (evenPoint k + Real.pi + x) := by
  have hc : 0 < evenPoint k := evenPoint_pos hk
  have hcx : 0 < evenPoint k + x := add_pos_of_pos_of_nonneg hc hx0
  have hcxpi : 0 < evenPoint k + Real.pi + x := by positivity
  have hsin : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxpi
  rw [Real.sinc_of_ne_zero hcx.ne', Real.sinc_of_ne_zero hcxpi.ne']
  rw [sin_evenPoint_add]
  have hphase : evenPoint k + Real.pi + x = evenPoint k + (x + Real.pi) := by ring
  rw [hphase, sin_evenPoint_add, Real.sin_add_pi]
  have hden : evenPoint k + x ≤ evenPoint k + (x + Real.pi) := by
    linarith [Real.pi_pos]
  have hrecip := one_div_le_one_div_of_le hcx hden
  calc
    0 ≤ Real.sin x *
        (1 / (evenPoint k + x) - 1 / (evenPoint k + (x + Real.pi))) :=
      mul_nonneg hsin (sub_nonneg.2 hrecip)
    _ = Real.sin x / (evenPoint k + x) +
        -Real.sin x / (evenPoint k + (x + Real.pi)) := by ring

private lemma sinc_odd_pair_nonpos (k : ℕ)
    {x : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi) :
    Real.sinc (evenPoint k + Real.pi + x) +
      Real.sinc (evenPoint (k + 1) + x) ≤ 0 := by
  have hfirst : 0 < evenPoint k + Real.pi + x := by
    have := evenPoint_nonneg k
    positivity
  have hsecond : 0 < evenPoint (k + 1) + x := by
    apply add_pos_of_pos_of_nonneg
    · exact evenPoint_pos (Nat.succ_pos k)
    · exact hx0
  have hsin : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxpi
  rw [Real.sinc_of_ne_zero hfirst.ne', Real.sinc_of_ne_zero hsecond.ne']
  have hphase1 : evenPoint k + Real.pi + x = evenPoint k + (x + Real.pi) := by ring
  rw [hphase1, sin_evenPoint_add, Real.sin_add_pi, sin_evenPoint_add]
  have heven : evenPoint (k + 1) = evenPoint k + 2 * Real.pi := by
    simp [evenPoint]
    ring
  have hden : evenPoint k + (x + Real.pi) ≤ evenPoint (k + 1) + x := by
    rw [heven]
    linarith [Real.pi_pos]
  have hfirst' : 0 < evenPoint k + (x + Real.pi) := by
    linarith
  have hrecip := one_div_le_one_div_of_le hfirst' hden
  calc
    -Real.sin x / (evenPoint k + (x + Real.pi)) +
        Real.sin x / (evenPoint (k + 1) + x) =
        Real.sin x *
          (1 / (evenPoint (k + 1) + x) -
            1 / (evenPoint k + (x + Real.pi))) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hsin (sub_nonpos.2 hrecip)

private lemma integral_nonpos_of_nonpos {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ} (hf : ∀ x ∈ Icc a b, f x ≤ 0) :
    (∫ x in a..b, f x) ≤ 0 := by
  have h := intervalIntegral.integral_nonneg (μ := volume) hab
    (fun x hx => neg_nonneg.2 (hf x hx))
  rw [intervalIntegral.integral_neg] at h
  linarith

private lemma even_full_block_nonneg {k : ℕ} (hk : 0 < k) :
    0 ≤ ∫ x in evenPoint k..evenPoint (k + 1), Real.sinc x := by
  have hs : IntervalIntegrable Real.sinc volume
      (evenPoint k) (evenPoint k + Real.pi) :=
    Real.continuous_sinc.intervalIntegrable _ _
  have hs' : IntervalIntegrable Real.sinc volume
      (evenPoint k + Real.pi) (evenPoint (k + 1)) :=
    Real.continuous_sinc.intervalIntegrable _ _
  have hshift1 := intervalIntegral.integral_comp_add_right Real.sinc (evenPoint k)
    (a := (0 : ℝ)) (b := Real.pi)
  have hshift2 := intervalIntegral.integral_comp_add_right Real.sinc
    (evenPoint k + Real.pi) (a := (0 : ℝ)) (b := Real.pi)
  have hp : 0 ≤ ∫ x in (0 : ℝ)..Real.pi,
      (Real.sinc (evenPoint k + x) +
        Real.sinc (evenPoint k + Real.pi + x)) := by
    apply intervalIntegral.integral_nonneg Real.pi_pos.le
    intro x hx
    exact sinc_even_pair_nonneg hk hx.1 hx.2
  have hadd := intervalIntegral.integral_add_adjacent_intervals hs hs'
  have hi1 : (∫ x in evenPoint k..evenPoint k + Real.pi, Real.sinc x) =
      ∫ x in (0 : ℝ)..Real.pi, Real.sinc (evenPoint k + x) := by
    rw [add_comm (evenPoint k)]
    convert hshift1.symm using 1 <;> ring
  have hi2 : (∫ x in evenPoint k + Real.pi..evenPoint (k + 1), Real.sinc x) =
      ∫ x in (0 : ℝ)..Real.pi, Real.sinc (evenPoint k + Real.pi + x) := by
    convert hshift2.symm using 1 <;> simp [evenPoint] <;> ring
  rw [← hadd]
  rw [hi1, hi2]
  have ha : IntervalIntegrable (fun x : ℝ => Real.sinc (evenPoint k + x))
      volume (0 : ℝ) Real.pi := by
    exact (Real.continuous_sinc.comp
      (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hb : IntervalIntegrable
      (fun x : ℝ => Real.sinc (evenPoint k + Real.pi + x))
      volume (0 : ℝ) Real.pi := by
    exact (Real.continuous_sinc.comp
      ((continuous_const.add continuous_const).add continuous_id)).intervalIntegrable _ _
  have hsum := intervalIntegral.integral_add ha hb
  rw [← hsum]
  exact hp

private lemma odd_full_block_nonpos (k : ℕ) :
    (∫ x in evenPoint k + Real.pi..evenPoint (k + 1) + Real.pi,
      Real.sinc x) ≤ 0 := by
  have hs : IntervalIntegrable Real.sinc volume
      (evenPoint k + Real.pi) (evenPoint (k + 1)) :=
    Real.continuous_sinc.intervalIntegrable _ _
  have hs' : IntervalIntegrable Real.sinc volume
      (evenPoint (k + 1)) (evenPoint (k + 1) + Real.pi) :=
    Real.continuous_sinc.intervalIntegrable _ _
  have hshift1 := intervalIntegral.integral_comp_add_right Real.sinc
    (evenPoint k + Real.pi) (a := (0 : ℝ)) (b := Real.pi)
  have hshift2 := intervalIntegral.integral_comp_add_right Real.sinc
    (evenPoint (k + 1)) (a := (0 : ℝ)) (b := Real.pi)
  have hp : (∫ x in (0 : ℝ)..Real.pi,
      (Real.sinc (evenPoint k + Real.pi + x) +
        Real.sinc (evenPoint (k + 1) + x))) ≤ 0 := by
    apply integral_nonpos_of_nonpos Real.pi_pos.le
    intro x hx
    exact sinc_odd_pair_nonpos k hx.1 hx.2
  have hadd := intervalIntegral.integral_add_adjacent_intervals hs hs'
  have hi1 : (∫ x in evenPoint k + Real.pi..evenPoint (k + 1), Real.sinc x) =
      ∫ x in (0 : ℝ)..Real.pi, Real.sinc (evenPoint k + Real.pi + x) := by
    convert hshift1.symm using 1 <;> simp [evenPoint] <;> ring
  have hi2 : (∫ x in evenPoint (k + 1)..evenPoint (k + 1) + Real.pi,
      Real.sinc x) =
      ∫ x in (0 : ℝ)..Real.pi, Real.sinc (evenPoint (k + 1) + x) := by
    rw [add_comm (evenPoint (k + 1))]
    convert hshift2.symm using 1 <;> ring
  rw [← hadd]
  rw [hi1, hi2]
  have ha : IntervalIntegrable
      (fun x : ℝ => Real.sinc (evenPoint k + Real.pi + x))
      volume (0 : ℝ) Real.pi := by
    exact (Real.continuous_sinc.comp
      ((continuous_const.add continuous_const).add continuous_id)).intervalIntegrable _ _
  have hb : IntervalIntegrable
      (fun x : ℝ => Real.sinc (evenPoint (k + 1) + x))
      volume (0 : ℝ) Real.pi := by
    exact (Real.continuous_sinc.comp
      (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hsum := intervalIntegral.integral_add ha hb
  rw [← hsum]
  exact hp

private lemma sinc_nonneg_even_half (k : ℕ) {x : ℝ}
    (hlo : evenPoint k ≤ x) (hhi : x ≤ evenPoint k + Real.pi) :
    0 ≤ Real.sinc x := by
  by_cases hx : x = 0
  · subst x
    simp
  have hx0 : 0 ≤ x := (evenPoint_nonneg k).trans hlo
  have ht0 : 0 ≤ x - evenPoint k := sub_nonneg.2 hlo
  have htpi : x - evenPoint k ≤ Real.pi := by linarith
  have hsin_t : 0 ≤ Real.sin (x - evenPoint k) :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 htpi
  have hphase : evenPoint k + (x - evenPoint k) = x := by ring
  have hsin : Real.sin x = Real.sin (x - evenPoint k) := by
    calc
      Real.sin x = Real.sin (evenPoint k + (x - evenPoint k)) :=
        congrArg Real.sin hphase.symm
      _ = Real.sin (x - evenPoint k) := sin_evenPoint_add _ _
  rw [Real.sinc_of_ne_zero hx, hsin]
  exact div_nonneg hsin_t hx0

private lemma sinc_nonpos_odd_half (k : ℕ) {x : ℝ}
    (hlo : evenPoint k + Real.pi ≤ x) (hhi : x ≤ evenPoint (k + 1)) :
    Real.sinc x ≤ 0 := by
  have hc0 := evenPoint_nonneg k
  have hxpos : 0 < x := lt_of_lt_of_le (by linarith [Real.pi_pos] :
    0 < evenPoint k + Real.pi) hlo
  let t := x - (evenPoint k + Real.pi)
  have ht0 : 0 ≤ t := sub_nonneg.2 hlo
  have heven : evenPoint (k + 1) = evenPoint k + 2 * Real.pi := by
    simp [evenPoint]
    ring
  have htpi : t ≤ Real.pi := by
    dsimp [t]
    rw [heven] at hhi
    linarith
  have hsint : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 htpi
  have hphase : x = evenPoint k + (t + Real.pi) := by
    dsimp [t]
    ring
  have hden : 0 ≤ evenPoint k + (t + Real.pi) := by
    rw [← hphase]
    exact hxpos.le
  rw [Real.sinc_of_ne_zero hxpos.ne', hphase, sin_evenPoint_add,
    Real.sin_add_pi]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hsint) hden

private lemma even_partial_block_nonneg {k : ℕ} (hk : 0 < k) {x : ℝ}
    (hlo : evenPoint k ≤ x) (hhi : x ≤ evenPoint (k + 1)) :
    0 ≤ ∫ t in evenPoint k..x, Real.sinc t := by
  by_cases hmid : x ≤ evenPoint k + Real.pi
  · apply intervalIntegral.integral_nonneg (μ := volume) hlo
    intro t ht
    exact sinc_nonneg_even_half k ht.1 (ht.2.trans hmid)
  · have hxmid : evenPoint k + Real.pi ≤ x := le_of_not_ge hmid
    have htail : (∫ t in x..evenPoint (k + 1), Real.sinc t) ≤ 0 := by
      apply integral_nonpos_of_nonpos hhi
      intro t ht
      exact sinc_nonpos_odd_half k (hxmid.trans ht.1) ht.2
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.continuous_sinc.intervalIntegrable (evenPoint k) x)
      (Real.continuous_sinc.intervalIntegrable x (evenPoint (k + 1)))
    linarith [even_full_block_nonneg hk]

private lemma odd_partial_block_nonpos (k : ℕ) {x : ℝ}
    (hlo : evenPoint k + Real.pi ≤ x)
    (hhi : x ≤ evenPoint (k + 1) + Real.pi) :
    (∫ t in evenPoint k + Real.pi..x, Real.sinc t) ≤ 0 := by
  by_cases hmid : x ≤ evenPoint (k + 1)
  · apply integral_nonpos_of_nonpos hlo
    intro t ht
    exact sinc_nonpos_odd_half k ht.1 (ht.2.trans hmid)
  · have hxmid : evenPoint (k + 1) ≤ x := le_of_not_ge hmid
    have htail : 0 ≤ ∫ t in x..evenPoint (k + 1) + Real.pi,
        Real.sinc t := by
      apply intervalIntegral.integral_nonneg (μ := volume) hhi
      intro t ht
      exact sinc_nonneg_even_half (k + 1) (hxmid.trans ht.1) ht.2
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.continuous_sinc.intervalIntegrable (evenPoint k + Real.pi) x)
      (Real.continuous_sinc.intervalIntegrable x (evenPoint (k + 1) + Real.pi))
    linarith [odd_full_block_nonpos k]

private lemma even_grid_tail_nonneg (k : ℕ) :
    0 ≤ ∫ x in evenPoint 1..evenPoint (k + 1), Real.sinc x := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable (evenPoint 1) (evenPoint (k + 1)))
        (Real.continuous_sinc.intervalIntegrable (evenPoint (k + 1))
          (evenPoint (k + 2)))
      have hblock := even_full_block_nonneg (k := k + 1) (Nat.succ_pos k)
      rw [← hadd]
      exact add_nonneg ih hblock

private lemma odd_grid_tail_nonpos (k : ℕ) :
    (∫ x in Real.pi..evenPoint k + Real.pi, Real.sinc x) ≤ 0 := by
  induction k with
  | zero => simp [evenPoint]
  | succ k ih =>
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable Real.pi (evenPoint k + Real.pi))
        (Real.continuous_sinc.intervalIntegrable (evenPoint k + Real.pi)
          (evenPoint (k + 1) + Real.pi))
      have hblock := odd_full_block_nonpos k
      rw [← hadd]
      exact add_nonpos ih hblock

private lemma even_tail_nonneg_of_le_fourteen_pi {x : ℝ}
    (hlo : evenPoint 1 ≤ x) (hhi : x ≤ evenPoint 7) :
    0 ≤ ∫ t in evenPoint 1..x, Real.sinc t := by
  have join (k : ℕ) (hk : 0 < k) (hklow : evenPoint k ≤ x)
      (hkhi : x ≤ evenPoint (k + 1)) :
      0 ≤ ∫ t in evenPoint 1..x, Real.sinc t := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.continuous_sinc.intervalIntegrable (evenPoint 1) (evenPoint k))
      (Real.continuous_sinc.intervalIntegrable (evenPoint k) x)
    rw [← hadd]
    exact add_nonneg (by simpa [Nat.sub_add_cancel hk] using even_grid_tail_nonneg (k - 1))
      (even_partial_block_nonneg hk hklow hkhi)
  by_cases h2 : x ≤ evenPoint 2
  · exact join 1 (by norm_num) hlo h2
  by_cases h3 : x ≤ evenPoint 3
  · exact join 2 (by norm_num) (le_of_not_ge h2) h3
  by_cases h4 : x ≤ evenPoint 4
  · exact join 3 (by norm_num) (le_of_not_ge h3) h4
  by_cases h5 : x ≤ evenPoint 5
  · exact join 4 (by norm_num) (le_of_not_ge h4) h5
  by_cases h6 : x ≤ evenPoint 6
  · exact join 5 (by norm_num) (le_of_not_ge h5) h6
  exact join 6 (by norm_num) (le_of_not_ge h6) hhi

private lemma odd_tail_nonpos_of_le_fourteen_pi {x : ℝ}
    (hlo : Real.pi ≤ x) (hhi : x ≤ evenPoint 7) :
    (∫ t in Real.pi..x, Real.sinc t) ≤ 0 := by
  have join (k : ℕ) (hklow : evenPoint k + Real.pi ≤ x)
      (hkhi : x ≤ evenPoint (k + 1) + Real.pi) :
      (∫ t in Real.pi..x, Real.sinc t) ≤ 0 := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.continuous_sinc.intervalIntegrable Real.pi (evenPoint k + Real.pi))
      (Real.continuous_sinc.intervalIntegrable (evenPoint k + Real.pi) x)
    rw [← hadd]
    exact add_nonpos (odd_grid_tail_nonpos k)
      (odd_partial_block_nonpos k hklow hkhi)
  by_cases h1 : x ≤ evenPoint 1 + Real.pi
  · exact join 0 (by simpa [evenPoint] using hlo) h1
  by_cases h2 : x ≤ evenPoint 2 + Real.pi
  · exact join 1 (le_of_not_ge h1) h2
  by_cases h3 : x ≤ evenPoint 3 + Real.pi
  · exact join 2 (le_of_not_ge h2) h3
  by_cases h4 : x ≤ evenPoint 4 + Real.pi
  · exact join 3 (le_of_not_ge h3) h4
  by_cases h5 : x ≤ evenPoint 5 + Real.pi
  · exact join 4 (le_of_not_ge h4) h5
  by_cases h6 : x ≤ evenPoint 6 + Real.pi
  · exact join 5 (le_of_not_ge h5) h6
  have hlast : x ≤ evenPoint 7 + Real.pi := hhi.trans (le_add_of_nonneg_right Real.pi_pos.le)
  exact join 6 (le_of_not_ge h6) hlast

/-- On the range needed for six grid cells, the sine integral stays in `[0,2]`. -/
theorem sineIntegral_mem_zero_two {x : ℝ} (hx0 : 0 ≤ x)
    (hx14 : x ≤ 14 * Real.pi) :
    Erdos228.Kernel.sineIntegral x ∈ Icc (0 : ℝ) 2 := by
  have hxEven : x ≤ evenPoint 7 := by
    dsimp [evenPoint]
    convert hx14 using 1 <;> ring
  constructor
  · by_cases hxpi : x ≤ Real.pi
    · apply intervalIntegral.integral_nonneg hx0
      intro t ht
      exact sinc_nonneg_on_zero_pi ht.1 (ht.2.trans hxpi)
    by_cases hx2 : x ≤ evenPoint 1
    · have htail : (∫ t in x..evenPoint 1, Real.sinc t) ≤ 0 := by
        apply integral_nonpos_of_nonpos hx2
        intro t ht
        have htpi : Real.pi ≤ t := (le_of_not_ge hxpi).trans ht.1
        exact sinc_nonpos_odd_half 0 (by simpa [evenPoint] using htpi) ht.2
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable (0 : ℝ) x)
        (Real.continuous_sinc.intervalIntegrable x (evenPoint 1))
      have hfirst := four_thirds_lt_sineIntegral_two_pi
      unfold Erdos228.Kernel.sineIntegral at hfirst ⊢
      have heq : evenPoint 1 = 2 * Real.pi := by simp [evenPoint]
      rw [heq] at hadd htail
      linarith
    · have htail := even_tail_nonneg_of_le_fourteen_pi (le_of_not_ge hx2) hxEven
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable (0 : ℝ) (evenPoint 1))
        (Real.continuous_sinc.intervalIntegrable (evenPoint 1) x)
      have hfirst := four_thirds_lt_sineIntegral_two_pi
      unfold Erdos228.Kernel.sineIntegral at hfirst ⊢
      have heq : evenPoint 1 = 2 * Real.pi := by simp [evenPoint]
      rw [heq] at hadd htail
      linarith
  · by_cases hxpi : x ≤ Real.pi
    · have htail : 0 ≤ ∫ t in x..Real.pi, Real.sinc t := by
        apply intervalIntegral.integral_nonneg hxpi
        intro t ht
        exact sinc_nonneg_on_zero_pi (hx0.trans ht.1) ht.2
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable (0 : ℝ) x)
        (Real.continuous_sinc.intervalIntegrable x Real.pi)
      have hpi := Erdos228.Kernel.sineIntegral_pi_lt_two
      unfold Erdos228.Kernel.sineIntegral at hpi ⊢
      linarith
    · have htail := odd_tail_nonpos_of_le_fourteen_pi (le_of_not_ge hxpi) hxEven
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable (0 : ℝ) Real.pi)
        (Real.continuous_sinc.intervalIntegrable Real.pi x)
      have hpi := Erdos228.Kernel.sineIntegral_pi_lt_two
      unfold Erdos228.Kernel.sineIntegral at hpi ⊢
      linarith

/-- After the first complete block, the sine integral remains above `4/3`. -/
theorem four_thirds_le_sineIntegral_of_two_pi_le {x : ℝ}
    (hx2 : 2 * Real.pi ≤ x) (hx14 : x ≤ 14 * Real.pi) :
    (4 : ℝ) / 3 ≤ Erdos228.Kernel.sineIntegral x := by
  have hlo : evenPoint 1 ≤ x := by simpa [evenPoint] using hx2
  have hhi : x ≤ evenPoint 7 := by
    dsimp [evenPoint]
    convert hx14 using 1 <;> ring
  have htail := even_tail_nonneg_of_le_fourteen_pi hlo hhi
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (Real.continuous_sinc.intervalIntegrable (0 : ℝ) (evenPoint 1))
    (Real.continuous_sinc.intervalIntegrable (evenPoint 1) x)
  have hfirst := four_thirds_lt_sineIntegral_two_pi
  unfold Erdos228.Kernel.sineIntegral at hfirst ⊢
  have heq : evenPoint 1 = 2 * Real.pi := by simp [evenPoint]
  rw [heq] at hadd htail
  linarith

theorem sineIntegral_neg (x : ℝ) :
    Erdos228.Kernel.sineIntegral (-x) = -Erdos228.Kernel.sineIntegral x := by
  unfold Erdos228.Kernel.sineIntegral
  have h := intervalIntegral.integral_comp_neg (f := Real.sinc)
    (a := (0 : ℝ)) (b := x)
  simp only [Real.sinc_neg] at h
  calc
    (∫ y in (0 : ℝ)..-x, Real.sinc y) =
        -(∫ y in -x..(0 : ℝ), Real.sinc y) :=
      intervalIntegral.integral_symm (-x) 0
    _ = -(∫ y in (0 : ℝ)..x, Real.sinc y) := by
      simpa using (congrArg Neg.neg h).symm

/-- Exact affine change of variables for the continuous odd kernel. -/
theorem integral_scaled_sinc_eq_sineIntegral_sub (n : ℕ) (hn : 0 < n)
    (u v theta : ℝ) :
    (∫ x in u..v,
      2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))) =
      Erdos228.Kernel.sineIntegral (2 * (n : ℝ) * (v - theta)) -
        Erdos228.Kernel.sineIntegral (2 * (n : ℝ) * (u - theta)) := by
  let c : ℝ := 2 * (n : ℝ)
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  have hcomp := intervalIntegral.integral_comp_mul_add Real.sinc hc (-c * theta)
    (a := u) (b := v)
  have hscale : (∫ x in u..v, c * Real.sinc (c * x + -c * theta)) =
      ∫ y in c * u + -c * theta..c * v + -c * theta, Real.sinc y := by
    rw [intervalIntegral.integral_const_mul]
    rw [hcomp]
    simp [hc]
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (Real.continuous_sinc.intervalIntegrable (0 : ℝ) (c * u + -c * theta))
    (Real.continuous_sinc.intervalIntegrable (c * u + -c * theta)
      (c * v + -c * theta))
  unfold Erdos228.Kernel.sineIntegral
  rw [show (∫ x in u..v,
      2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))) =
      ∫ x in u..v, c * Real.sinc (c * x + -c * theta) by
        congr 1
        funext x
        dsimp [c]
        ring]
  rw [hscale]
  have hu : c * u + -c * theta = c * (u - theta) := by ring
  have hv : c * v + -c * theta = c * (v - theta) := by ring
  rw [hu, hv] at hadd ⊢
  linarith

private lemma four_thirds_le_sineIntegral_add_of_add_eq_two_pi
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : u + v = 2 * Real.pi) :
    (4 : ℝ) / 3 ≤ Erdos228.Kernel.sineIntegral u +
      Erdos228.Kernel.sineIntegral v := by
  have hbound (z w : ℝ) (hzpi : Real.pi ≤ z) (hz2 : z ≤ 2 * Real.pi)
      (hw0 : 0 ≤ w) (hw14 : w ≤ 14 * Real.pi) :
      (4 : ℝ) / 3 ≤ Erdos228.Kernel.sineIntegral w +
        Erdos228.Kernel.sineIntegral z := by
    have htail : (∫ t in z..2 * Real.pi, Real.sinc t) ≤ 0 := by
      apply integral_nonpos_of_nonpos hz2
      intro t ht
      exact sinc_nonpos_odd_half 0 (by simpa [evenPoint] using hzpi.trans ht.1)
        (by simpa [evenPoint] using ht.2)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.continuous_sinc.intervalIntegrable (0 : ℝ) z)
      (Real.continuous_sinc.intervalIntegrable z (2 * Real.pi))
    have hw := sineIntegral_mem_zero_two hw0 hw14
    rcases hw with ⟨hw_nonneg, hw_le⟩
    have hfirst := four_thirds_lt_sineIntegral_two_pi
    unfold Erdos228.Kernel.sineIntegral at hfirst hw_nonneg hw_le ⊢
    linarith
  by_cases hupi : u ≤ Real.pi
  · have hvpi : Real.pi ≤ v := by linarith
    have hv2 : v ≤ 2 * Real.pi := by linarith
    have hu14 : u ≤ 14 * Real.pi := by nlinarith [Real.pi_pos]
    exact hbound v u hvpi hv2 hu hu14
  · have hvpi : v ≤ Real.pi := by linarith
    have hupi' : Real.pi ≤ u := le_of_not_ge hupi
    have hu2 : u ≤ 2 * Real.pi := by linarith
    have hv14 : v ≤ 14 * Real.pi := by nlinarith [Real.pi_pos]
    simpa [add_comm] using hbound u v hupi' hu2 hv hv14

/-- BBMST Lemma 5.8(a) for a nondegenerate grid interval of at most six cells. -/
theorem principal_grid_interval_inside (n : ℕ) (hn : 0 < n)
    (a b : ℤ) (hab : a < b)
    (hshort : (b : ℝ) * Real.pi / n - (a : ℝ) * Real.pi / n ≤
      6 * Real.pi / n)
    {theta : ℝ}
    (htheta : theta ∈ Icc ((a : ℝ) * Real.pi / n)
      ((b : ℝ) * Real.pi / n)) :
    (∫ x in (a : ℝ) * Real.pi / n..(b : ℝ) * Real.pi / n,
      2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))) ∈
      Icc ((4 : ℝ) / 3) 4 := by
  let L : ℝ := (a : ℝ) * Real.pi / n
  let U : ℝ := (b : ℝ) * Real.pi / n
  let c : ℝ := 2 * (n : ℝ)
  let u : ℝ := c * (theta - L)
  let v : ℝ := c * (U - theta)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < c := by dsimp [c]; positivity
  have hu : 0 ≤ u := mul_nonneg hc.le (sub_nonneg.2 htheta.1)
  have hv : 0 ≤ v := mul_nonneg hc.le (sub_nonneg.2 htheta.2)
  have huv : u + v = c * (U - L) := by
    dsimp [u, v]
    ring
  have htotal : u + v = 2 * ((b - a : ℤ) : ℝ) * Real.pi := by
    rw [huv]
    dsimp [c, U, L]
    push_cast
    field_simp
  have hsum12 : u + v ≤ 12 * Real.pi := by
    have hm := mul_le_mul_of_nonneg_left hshort hc.le
    calc
      u + v = c * (U - L) := huv
      _ ≤ c * (6 * Real.pi / n) := by simpa [U, L] using hm
      _ = 12 * Real.pi := by
        dsimp [c]
        field_simp
        norm_num
  have hu14 : u ≤ 14 * Real.pi := by
    nlinarith [Real.pi_pos]
  have hv14 : v ≤ 14 * Real.pi := by
    nlinarith [Real.pi_pos]
  have huMem := sineIntegral_mem_zero_two hu hu14
  have hvMem := sineIntegral_mem_zero_two hv hv14
  rcases huMem with ⟨huSi0, huSi2⟩
  rcases hvMem with ⟨hvSi0, hvSi2⟩
  have hlower : (4 : ℝ) / 3 ≤ Erdos228.Kernel.sineIntegral u +
      Erdos228.Kernel.sineIntegral v := by
    by_cases hgap : b - a = 1
    · apply four_thirds_le_sineIntegral_add_of_add_eq_two_pi hu hv
      rw [htotal, hgap]
      norm_num
    · have hgap2 : (2 : ℤ) ≤ b - a := by omega
      have htotal4 : 4 * Real.pi ≤ u + v := by
        rw [htotal]
        have hcast : (2 : ℝ) ≤ ((b - a : ℤ) : ℝ) := by exact_mod_cast hgap2
        nlinarith [Real.pi_pos]
      by_cases hu2 : 2 * Real.pi ≤ u
      · have hmain := four_thirds_le_sineIntegral_of_two_pi_le hu2 hu14
        linarith
      · have hv2 : 2 * Real.pi ≤ v := by linarith
        have hmain := four_thirds_le_sineIntegral_of_two_pi_le hv2 hv14
        linarith
  have hupper : Erdos228.Kernel.sineIntegral u +
      Erdos228.Kernel.sineIntegral v ≤ 4 := by linarith
  have hid := integral_scaled_sinc_eq_sineIntegral_sub n hn L U theta
  have hL : 2 * (n : ℝ) * (L - theta) = -u := by
    dsimp [c, u]
    ring
  have hU : 2 * (n : ℝ) * (U - theta) = v := by rfl
  dsimp [L, U] at hid ⊢
  rw [hid, hL, hU, sineIntegral_neg]
  constructor <;> linarith

/-- BBMST Lemma 5.8(b), in the near-exterior form used by the interval family.
The closest endpoint is at most one grid cell away. -/
theorem principal_grid_interval_outside_near (n : ℕ) (hn : 0 < n)
    (a b : ℤ) (hab : a < b)
    (hshort : (b : ℝ) * Real.pi / n - (a : ℝ) * Real.pi / n ≤
      6 * Real.pi / n)
    {theta : ℝ}
    (hnear :
      (theta ≤ (a : ℝ) * Real.pi / n ∧
        (a : ℝ) * Real.pi / n - theta ≤ Real.pi / n) ∨
      ((b : ℝ) * Real.pi / n ≤ theta ∧
        theta - (b : ℝ) * Real.pi / n ≤ Real.pi / n)) :
    |∫ x in (a : ℝ) * Real.pi / n..(b : ℝ) * Real.pi / n,
      2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))| ≤ 2 := by
  let L : ℝ := (a : ℝ) * Real.pi / n
  let U : ℝ := (b : ℝ) * Real.pi / n
  let c : ℝ := 2 * (n : ℝ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < c := by dsimp [c]; positivity
  have hwidth : c * (U - L) ≤ 12 * Real.pi := by
    have hm := mul_le_mul_of_nonneg_left hshort hc.le
    dsimp [c, U, L] at hm ⊢
    field_simp at hm ⊢
    nlinarith
  have hUL0 : 0 ≤ U - L := by
    have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    dsimp [U, L]
    have hmul : (a : ℝ) * Real.pi ≤ (b : ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_right habR.le Real.pi_pos.le
    exact sub_nonneg.2 (div_le_div_of_nonneg_right hmul hnR.le)
  have hid := integral_scaled_sinc_eq_sineIntegral_sub n hn L U theta
  rcases hnear with hleft | hright
  · let z : ℝ := c * (L - theta)
    let w : ℝ := c * (U - theta)
    have hz0 : 0 ≤ z := mul_nonneg hc.le (sub_nonneg.2 hleft.1)
    have hzw : w = z + c * (U - L) := by dsimp [z, w]; ring
    have hw0 : 0 ≤ w := by
      rw [hzw]
      exact add_nonneg hz0 (mul_nonneg hc.le hUL0)
    have hz2 : z ≤ 2 * Real.pi := by
      have hm := mul_le_mul_of_nonneg_left hleft.2 hc.le
      dsimp [c, z, L] at hm ⊢
      field_simp at hm ⊢
      nlinarith
    have hw14 : w ≤ 14 * Real.pi := by rw [hzw]; linarith
    have hzMem := sineIntegral_mem_zero_two hz0 (hz2.trans (by nlinarith [Real.pi_pos]))
    have hwMem := sineIntegral_mem_zero_two hw0 hw14
    rcases hzMem with ⟨hzSi0, hzSi2⟩
    rcases hwMem with ⟨hwSi0, hwSi2⟩
    have hL : 2 * (n : ℝ) * (L - theta) = z := by rfl
    have hU : 2 * (n : ℝ) * (U - theta) = w := by rfl
    dsimp [L, U] at hid ⊢
    rw [hid, hL, hU]
    rw [abs_le]
    constructor <;> linarith
  · let z : ℝ := c * (theta - U)
    let w : ℝ := c * (theta - L)
    have hz0 : 0 ≤ z := mul_nonneg hc.le (sub_nonneg.2 hright.1)
    have hzw : w = z + c * (U - L) := by dsimp [z, w]; ring
    have hw0 : 0 ≤ w := by
      rw [hzw]
      exact add_nonneg hz0 (mul_nonneg hc.le hUL0)
    have hz2 : z ≤ 2 * Real.pi := by
      have hm := mul_le_mul_of_nonneg_left hright.2 hc.le
      dsimp [c, z, U] at hm ⊢
      field_simp at hm ⊢
      nlinarith
    have hw14 : w ≤ 14 * Real.pi := by rw [hzw]; linarith
    have hzMem := sineIntegral_mem_zero_two hz0 (hz2.trans (by nlinarith [Real.pi_pos]))
    have hwMem := sineIntegral_mem_zero_two hw0 hw14
    rcases hzMem with ⟨hzSi0, hzSi2⟩
    rcases hwMem with ⟨hwSi0, hwSi2⟩
    have hL : 2 * (n : ℝ) * (L - theta) = -w := by dsimp [c, w]; ring
    have hU : 2 * (n : ℝ) * (U - theta) = -z := by dsimp [c, z]; ring
    dsimp [L, U] at hid ⊢
    rw [hid, hL, hU, sineIntegral_neg z, sineIntegral_neg w]
    rw [abs_le]
    constructor <;> linarith

end

end SineIntegralGrid

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/KernelDistantClaim.lean` -/

section
/-!
# The distant principal-kernel estimate in BBMST Claim 3

This file proves the concrete Claim 3 estimate for a
`OddSine.SuitableIntervalFamily`.  The near collection is the one fixed in
`KernelNearGeometry`; in particular, its complement uses the non-strict
separation `pi / n <= intervalGap theta I`.
-/

namespace KernelDistantClaim

open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral

noncomputable section

open Erdos228.OddSine

/-- The principal (translated sinc) part of the odd kernel on one interval. -/
def principalIntegral (n : ℕ) (I : RealInterval) (theta : ℝ) : ℝ :=
  ∫ x in I.1..I.2,
    2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))

/-- Base intervals outside the strict near set.  Thus membership means the
non-strict inequality `pi / n <= intervalGap theta I`. -/
def distantBaseIntervals {n : ℕ} (F : SuitableIntervalFamily n)
    (theta : ℝ) : Finset (↑F.base : Type) :=
  @Finset.filter (↑F.base : Type)
    (fun I ↦ ¬Erdos228.KernelNearGeometry.Near n theta I.1)
    (Classical.decPred _) Finset.univ

/-- The distant collection is literally the complement of
`KernelNearGeometry.nearBaseIntervals`. -/
theorem distantBaseIntervals_eq_sdiff {n : ℕ}
    (F : SuitableIntervalFamily n) (theta : ℝ) :
    distantBaseIntervals F theta =
      Finset.univ \
        Erdos228.KernelNearGeometry.nearBaseIntervals F theta := by
  classical
  ext I
  simp [distantBaseIntervals,
    Erdos228.KernelNearGeometry.nearBaseIntervals]

/-- Endpoint-indexed version of `distantBaseIntervals`. -/
private def distantIntervals {n : ℕ} (F : SuitableIntervalFamily n)
    (theta : ℝ) : Finset RealInterval :=
  @Finset.filter RealInterval
    (fun I ↦ ¬Erdos228.KernelNearGeometry.Near n theta I)
    (Classical.decPred _) F.base

private lemma sum_distantBaseIntervals_eq_sum_distantIntervals {n : ℕ}
    (F : SuitableIntervalFamily n) (theta : ℝ) (f : RealInterval → ℝ) :
    ∑ I ∈ distantBaseIntervals F theta, f I.1 =
      ∑ I ∈ distantIntervals F theta, f I := by
  classical
  apply Finset.sum_bij (fun I _ ↦ I.1)
  · intro I hI
    simp only [distantBaseIntervals, Finset.mem_filter, Finset.mem_univ,
      true_and] at hI
    simp [distantIntervals, I.property, hI]
  · intro I hI J hJ hIJ
    exact Subtype.ext hIJ
  · intro I hI
    simp only [distantIntervals, Finset.mem_filter] at hI
    refine ⟨⟨I, hI.1⟩, ?_, rfl⟩
    simp [distantBaseIntervals, hI.2]
  · intro I hI
    rfl

private lemma shifted_endpoint_cos_eq {n : ℕ} (hn : 0 < n)
    {I : RealInterval}
    (hgrid : ∃ a b : ℤ,
      I.1 = (a : ℝ) * Real.pi / n ∧ I.2 = (b : ℝ) * Real.pi / n)
    (theta : ℝ) :
    Real.cos ((2 * (n : ℝ)) * (I.2 - theta)) =
      Real.cos ((2 * (n : ℝ)) * (I.1 - theta)) := by
  obtain ⟨a, b, ha, hb⟩ := hgrid
  rw [ha, hb]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    Real.cos ((2 * (n : ℝ)) * ((b : ℝ) * Real.pi / n - theta)) =
        Real.cos ((b : ℝ) * (2 * Real.pi) - (2 * (n : ℝ)) * theta) := by
          congr 1
          field_simp [hn0]
    _ = Real.cos ((2 * (n : ℝ)) * theta) :=
      Real.cos_int_mul_two_pi_sub _ b
    _ = Real.cos ((a : ℝ) * (2 * Real.pi) - (2 * (n : ℝ)) * theta) :=
      (Real.cos_int_mul_two_pi_sub _ a).symm
    _ = Real.cos ((2 * (n : ℝ)) * ((a : ℝ) * Real.pi / n - theta)) := by
          congr 1
          field_simp [hn0]

/-- Away from the translated singular point, the sinc presentation is
exactly `sin (2*n*u) / u` after shifting the interval by `theta`. -/
theorem principalIntegral_eq_reciprocal_sine_of_zero_not_mem
    {n : ℕ} (hn : 0 < n)
    {I : RealInterval} {theta : ℝ}
    (hzero : ∀ u ∈ uIcc (I.1 - theta) (I.2 - theta), u ≠ 0) :
    principalIntegral n I theta =
      ∫ u in (I.1 - theta)..(I.2 - theta),
        u⁻¹ * Real.sin ((2 * (n : ℝ)) * u) := by
  rw [principalIntegral]
  rw [intervalIntegral.integral_comp_sub_right
    (fun u : ℝ ↦ 2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * u)) theta]
  apply intervalIntegral.integral_congr
  intro u hu
  have hn0 : (2 * (n : ℝ)) ≠ 0 := by positivity
  have hu0 := hzero u hu
  change 2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * u) =
    u⁻¹ * Real.sin (2 * (n : ℝ) * u)
  rw [Real.sinc_of_ne_zero (mul_ne_zero hn0 hu0)]
  field_simp [hn0, hu0]

/-- One distant grid interval is controlled by its reciprocal endpoint
variation.  This is the concrete one-interval use of BBMST Lemma 5.9. -/
theorem abs_principalIntegral_le_endpointVariation {n : ℕ} (hn : 0 < n)
    {I : RealInterval} {theta : ℝ} (hord : I.1 ≤ I.2)
    (hgrid : ∃ a b : ℤ,
      I.1 = (a : ℝ) * Real.pi / n ∧ I.2 = (b : ℝ) * Real.pi / n)
    (hside : I.2 ≤ theta - Real.pi / n ∨
      theta + Real.pi / n ≤ I.1) :
    |principalIntegral n I theta| ≤
      ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpiN : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  have hleftOrRight : I.2 < theta ∨ theta < I.1 := by
    rcases hside with hleft | hright
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hzero : ∀ u ∈ uIcc (I.1 - theta) (I.2 - theta), u ≠ 0 := by
    intro u hu
    rw [uIcc_of_le (sub_le_sub_right hord theta)] at hu
    rcases hleftOrRight with hleft | hright
    · have : u < 0 := lt_of_le_of_lt hu.2 (sub_neg.mpr hleft)
      exact this.ne
    · have : 0 < u := lt_of_lt_of_le (sub_pos.mpr hright) hu.1
      exact this.ne'
  rw [principalIntegral_eq_reciprocal_sine_of_zero_not_mem hn hzero]
  have hlocal :=
    Erdos228.KernelClaims.abs_integral_mul_sin_le_of_deriv_nonpos
      (h := fun u : ℝ ↦ u⁻¹) (h' := fun u : ℝ ↦ -(u ^ 2)⁻¹)
      hn (sub_le_sub_right hord theta)
      (fun u hu ↦ hasDerivAt_inv (hzero u (by
        simpa [uIcc_of_le (sub_le_sub_right hord theta)] using hu)))
      (by
        apply ContinuousOn.neg
        apply ContinuousOn.inv₀ (by fun_prop)
        intro u hu
        exact pow_ne_zero 2 (hzero u (by
          simpa [uIcc_of_le (sub_le_sub_right hord theta)] using hu)))
      (fun u hu ↦ neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg u)))
      (shifted_endpoint_cos_eq hn hgrid theta)
  have hanti : (I.2 - theta)⁻¹ ≤ (I.1 - theta)⁻¹ := by
    rcases hleftOrRight with hleft | hright
    · exact inv_antitoneOn_Iio
        (show I.1 - theta ∈ Iio 0 by exact sub_neg.mpr (hord.trans_lt hleft))
        (show I.2 - theta ∈ Iio 0 by exact sub_neg.mpr hleft)
        (sub_le_sub_right hord theta)
    · exact inv_antitoneOn_Ioi
        (show I.1 - theta ∈ Ioi 0 by exact sub_pos.mpr hright)
        (show I.2 - theta ∈ Ioi 0 by exact sub_pos.mpr (hright.trans_le hord))
        (sub_le_sub_right hord theta)
  rw [abs_of_nonpos (sub_nonpos.mpr hanti)] at hlocal
  convert hlocal using 1
  ring

/-! ## The finite endpoint telescope -/

private lemma endpoint_variation_le_of_monotone
    (s : Finset RealInterval) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hmono : MonotoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.2 - f I.1) ≤ f U - f L := by
  classical
  let t : Finset (Lex RealInterval) := s.image toLex
  let m := t.card
  let e : Fin m ≃o ↑t := Finset.orderIsoOfFin t rfl
  have emem (k : Fin m) : ofLex ((e k : ↑t) : Lex RealInterval) ∈ s := by
    have hk := (e k).property
    change ((e k : ↑t) : Lex RealInterval) ∈ s.image toLex at hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨I, hI, hEq⟩
    simpa [← hEq] using hI
  let A : ℕ → ℝ := fun k ↦
    if hk : k < m then
      f (ofLex ((e ⟨k, hk⟩ : ↑t) : Lex RealInterval)).1 else f U
  let B : ℕ → ℝ := fun k ↦
    if hk : k < m then
      f (ofLex ((e ⟨k, hk⟩ : ↑t) : Lex RealInterval)).2 else f U
  let E : ℕ → ℝ := fun k ↦ B k - A k
  have hchain : ∀ k < m, B k ≤ A (k + 1) := by
    intro k hk
    simp only [B, A, dif_pos hk]
    by_cases hks : k + 1 < m
    · rw [dif_pos hks]
      apply hmono
      · exact ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans
            (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
      · exact ⟨(hinside _ (emem ⟨k + 1, hks⟩)).1,
          (hord _ (emem ⟨k + 1, hks⟩)).le.trans
            (hinside _ (emem ⟨k + 1, hks⟩)).2⟩
      have horder : e ⟨k, hk⟩ ≤ e ⟨k + 1, hks⟩ :=
        e.le_iff_le.mpr (by simp)
      have hleft : (ofLex ((e ⟨k, hk⟩ : ↑t) : Lex RealInterval)).1 ≤
          (ofLex ((e ⟨k + 1, hks⟩ : ↑t) : Lex RealInterval)).1 := by
        exact (Prod.Lex.le_iff.mp horder).elim (fun h ↦ h.le) (fun h ↦ h.1.le)
      have hne : ofLex ((e ⟨k, hk⟩ : ↑t) : Lex RealInterval) ≠
          ofLex ((e ⟨k + 1, hks⟩ : ↑t) : Lex RealInterval) := by
        intro heq
        have heq' : e ⟨k, hk⟩ = e ⟨k + 1, hks⟩ := by
          apply Subtype.ext
          exact ofLex.injective heq
        have : (⟨k, hk⟩ : Fin m) = ⟨k + 1, hks⟩ := e.injective heq'
        simp at this
      rcases hsep (emem ⟨k, hk⟩) (emem ⟨k + 1, hks⟩) hne with hgood | hbad
      · exact hgood
      · have hstrict := hord _ (emem ⟨k + 1, hks⟩)
        linarith
    · rw [dif_neg hks]
      exact hmono
        ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
        ⟨hLU, le_rfl⟩ (hinside _ (emem ⟨k, hk⟩)).2
  have htelescope :=
    Erdos228.KernelClaims.sum_interval_error_le_of_monotone_endpoints
      (n := 1) (m := m) (A := A) (B := B) (E := E) (by norm_num)
      (fun k hk ↦ by simp [E]) hchain
  have hsum : (∑ I ∈ s, (f I.2 - f I.1)) =
      ∑ k ∈ Finset.range m, E k := by
    calc
      (∑ I ∈ s, (f I.2 - f I.1)) =
          ∑ J ∈ t, (f (ofLex J).2 - f (ofLex J).1) := by
            symm
            simpa [t] using (Finset.sum_image (s := s)
              (f := fun J : Lex RealInterval ↦
                f (ofLex J).2 - f (ofLex J).1) toLex.injective.injOn)
      _ = ∑ J : ↑t, (f (ofLex (J.1 : Lex RealInterval)).2 -
          f (ofLex (J.1 : Lex RealInterval)).1) := by
            symm
            exact (Finset.sum_subtype (M := ℝ) (s := t) (p := fun J ↦ J ∈ t)
              (by simp) (fun J : Lex RealInterval ↦
                f (ofLex J).2 - f (ofLex J).1)).symm
      _ = ∑ i : Fin m, (f (ofLex ((e i : ↑t) : Lex RealInterval)).2 -
          f (ofLex ((e i : ↑t) : Lex RealInterval)).1) := by
            exact (e.toEquiv.sum_comp (fun J : ↑t ↦
              f (ofLex (J.1 : Lex RealInterval)).2 -
                f (ofLex (J.1 : Lex RealInterval)).1)).symm
      _ = ∑ i : Fin m, E i := by
            apply Finset.sum_congr rfl
            intro i _
            simp [E, A, B, i.isLt]
      _ = ∑ k ∈ Finset.range m, E k := Fin.sum_univ_eq_sum_range E m
  rw [hsum]
  by_cases hm : m = 0
  · simpa [hm] using sub_nonneg.mpr
      (hmono ⟨le_rfl, hLU⟩ ⟨hLU, le_rfl⟩ hLU)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hA0 : A 0 =
        f (ofLex ((e ⟨0, hmpos⟩ : ↑t) : Lex RealInterval)).1 := by
      simp [A, hmpos]
    have hAm : A m = f U := by simp [A]
    rw [hA0, hAm] at htelescope
    simp only [Nat.cast_one, div_one] at htelescope
    exact htelescope.trans (sub_le_sub_left
      (hmono ⟨le_rfl, hLU⟩
        ⟨(hinside _ (emem ⟨0, hmpos⟩)).1,
          (hord _ (emem ⟨0, hmpos⟩)).le.trans
            (hinside _ (emem ⟨0, hmpos⟩)).2⟩
        (hinside _ (emem ⟨0, hmpos⟩)).1) _)

private lemma endpoint_variation_le_of_antitone
    (s : Finset RealInterval) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hanti : AntitoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.1 - f I.2) ≤ f L - f U := by
  have h := endpoint_variation_le_of_monotone s (-f) L U hord hLU hinside hsep
    (fun _ hx _ hy hxy ↦ neg_le_neg (hanti hx hy hxy))
  simpa only [Pi.neg_apply, neg_sub_neg] using h

private lemma pairwise_disjoint_base {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) :
    Set.Pairwise (↑F.base : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1) := by
  intro I hI J hJ hne
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpiN : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  rcases le_total I.1 J.1 with hle | hle
  · left
    by_contra hnot
    have hJlt : J.1 < I.2 := lt_of_not_ge hnot
    have hsep := F.separated hI hJ hne J.1
      ⟨hle, hJlt.le⟩ J.1 ⟨le_rfl, F.ordered J hJ⟩
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hpiN) this
  · right
    by_contra hnot
    have hIlt : I.1 < J.2 := lt_of_not_ge hnot
    have hsep := F.separated hI hJ hne I.1
      ⟨le_rfl, F.ordered I hI⟩ I.1 ⟨hle, hIlt.le⟩
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hpiN) this

private def leftDistantIntervals {n : ℕ} (F : SuitableIntervalFamily n)
    (theta : ℝ) : Finset RealInterval :=
  @Finset.filter RealInterval (fun I ↦ I.2 ≤ theta)
    (Classical.decPred _) (distantIntervals F theta)

private def rightDistantIntervals {n : ℕ} (F : SuitableIntervalFamily n)
    (theta : ℝ) : Finset RealInterval :=
  @Finset.filter RealInterval (fun I ↦ ¬I.2 ≤ theta)
    (Classical.decPred _) (distantIntervals F theta)

private lemma leftDistant_upper {n : ℕ} (_hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ leftDistantIntervals F theta) :
    I.2 ≤ theta - Real.pi / n := by
  simp only [leftDistantIntervals, distantIntervals, Finset.mem_filter] at hI
  have hgap : Real.pi / (n : ℝ) ≤
      Erdos228.KernelNearGeometry.intervalGap theta I := by
    exact le_of_not_gt hI.1.2
  rw [Erdos228.KernelNearGeometry.intervalGap_eq_right
    (F.ordered I hI.1.1) hI.2] at hgap
  linarith

private lemma rightDistant_lower {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ rightDistantIntervals F theta) :
    theta + Real.pi / n ≤ I.1 := by
  simp only [rightDistantIntervals, distantIntervals, Finset.mem_filter] at hI
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpiN : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  have hright : theta ≤ I.1 := by
    by_contra hnot
    have hleft : I.1 < theta := lt_of_not_ge hnot
    have hright : theta < I.2 := lt_of_not_ge hI.2
    apply hI.1.2
    rw [Erdos228.KernelNearGeometry.Near,
      Erdos228.KernelNearGeometry.intervalGap_eq_zero_of_mem]
    · exact hpiN
    · exact ⟨hleft.le, hright.le⟩
  have hgap : Real.pi / (n : ℝ) ≤
      Erdos228.KernelNearGeometry.intervalGap theta I := by
    exact le_of_not_gt hI.1.2
  rw [Erdos228.KernelNearGeometry.intervalGap_eq_left
    (F.ordered I hI.1.1) hright] at hgap
  linarith

private lemma side_pairwise_disjoint {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) (s : Finset RealInterval)
    (hs : s ⊆ F.base) :
    Set.Pairwise (↑s : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1) := by
  intro I hI J hJ hne
  exact pairwise_disjoint_base hn F (hs hI) (hs hJ) hne

private lemma sum_left_endpointVariation_le {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ leftDistantIntervals F theta,
        ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) ≤
      (n : ℝ) / Real.pi := by
  classical
  let s := leftDistantIntervals F theta
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hpiN : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  by_cases hs : s.Nonempty
  · obtain ⟨I, hI⟩ := hs
    have hbase : ∀ J ∈ s, J ∈ F.base := by
      intro J hJ
      have hJ' : (J ∈ F.base ∧
          ¬Erdos228.KernelNearGeometry.Near n theta J) ∧ J.2 ≤ theta := by
        simpa only [s, leftDistantIntervals, distantIntervals,
          Finset.mem_filter] using hJ
      exact hJ'.1.1
    have hinside : ∀ J ∈ s,
        (0 : ℝ) ≤ J.1 ∧ J.2 ≤ theta - Real.pi / n := by
      intro J hJ
      exact ⟨(F.in_first_quadrant J (hbase J hJ)).1,
        leftDistant_upper hn F (by simpa [s] using hJ)⟩
    have hLU : (0 : ℝ) ≤ theta - Real.pi / n :=
      (hinside I hI).1.trans
        ((F.ordered I (hbase I hI)).trans (hinside I hI).2)
    have htel := endpoint_variation_le_of_antitone s
      (fun x : ℝ ↦ (x - theta)⁻¹) 0 (theta - Real.pi / n)
      (fun J hJ ↦ F.nondegenerate J (hbase J hJ)) hLU hinside
      (side_pairwise_disjoint hn F s hbase)
      (sub_inv_antitoneOn_Icc_left (by linarith))
    have hzeroEndpoint : (0 - theta)⁻¹ ≤ 0 :=
      inv_nonpos.mpr (sub_nonpos.mpr htheta.1)
    have hfarEndpoint :
        (theta - Real.pi / (n : ℝ) - theta)⁻¹ =
          -(n : ℝ) / Real.pi := by
      field_simp [hn0, Real.pi_ne_zero]
      ring
    rw [hfarEndpoint] at htel
    dsimp [s] at htel
    calc
      ∑ I ∈ leftDistantIntervals F theta,
          ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) ≤
          (0 - theta)⁻¹ - (-(n : ℝ) / Real.pi) := htel
      _ ≤ 0 - (-(n : ℝ) / Real.pi) :=
        sub_le_sub_right hzeroEndpoint _
      _ = (n : ℝ) / Real.pi := by ring
  · have hs0 : leftDistantIntervals F theta = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      simpa [s] using hs
    rw [hs0]
    simp
    positivity

private lemma sum_right_endpointVariation_le {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ rightDistantIntervals F theta,
        ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) ≤
      (n : ℝ) / Real.pi := by
  classical
  let s := rightDistantIntervals F theta
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hpiN : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  by_cases hs : s.Nonempty
  · obtain ⟨I, hI⟩ := hs
    have hbase : ∀ J ∈ s, J ∈ F.base := by
      intro J hJ
      have hJ' : (J ∈ F.base ∧
          ¬Erdos228.KernelNearGeometry.Near n theta J) ∧ ¬J.2 ≤ theta := by
        simpa only [s, rightDistantIntervals, distantIntervals,
          Finset.mem_filter] using hJ
      exact hJ'.1.1
    have hinside : ∀ J ∈ s,
        theta + Real.pi / n ≤ J.1 ∧ J.2 ≤ Real.pi / 2 := by
      intro J hJ
      exact ⟨rightDistant_lower hn F (by simpa [s] using hJ),
        (F.in_first_quadrant J (hbase J hJ)).2⟩
    have hLU : theta + Real.pi / n ≤ Real.pi / 2 :=
      (hinside I hI).1.trans
        ((F.ordered I (hbase I hI)).trans (hinside I hI).2)
    have htel := endpoint_variation_le_of_antitone s
      (fun x : ℝ ↦ (x - theta)⁻¹)
      (theta + Real.pi / n) (Real.pi / 2)
      (fun J hJ ↦ F.nondegenerate J (hbase J hJ)) hLU hinside
      (side_pairwise_disjoint hn F s hbase)
      (sub_inv_antitoneOn_Icc_right (by linarith))
    have hlastEndpoint : 0 ≤ (Real.pi / 2 - theta)⁻¹ :=
      inv_nonneg.mpr (sub_nonneg.mpr htheta.2)
    have hnearEndpoint :
        (theta + Real.pi / (n : ℝ) - theta)⁻¹ =
          (n : ℝ) / Real.pi := by
      field_simp [hn0, Real.pi_ne_zero]
      ring
    rw [hnearEndpoint] at htel
    dsimp [s] at htel
    calc
      ∑ I ∈ rightDistantIntervals F theta,
          ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) ≤
          (n : ℝ) / Real.pi - (Real.pi / 2 - theta)⁻¹ := htel
      _ ≤ (n : ℝ) / Real.pi - 0 :=
        sub_le_sub_left hlastEndpoint _
      _ = (n : ℝ) / Real.pi := by ring
  · have hs0 : rightDistantIntervals F theta = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      simpa [s] using hs
    rw [hs0]
    simp
    positivity

private lemma sum_left_abs_principalIntegral_le {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ leftDistantIntervals F theta, |principalIntegral n I theta| ≤
      1 / Real.pi := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  calc
    ∑ I ∈ leftDistantIntervals F theta, |principalIntegral n I theta| ≤
        ∑ I ∈ leftDistantIntervals F theta,
          (((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) / n) := by
      apply Finset.sum_le_sum
      intro I hI
      have hI' : (I ∈ F.base ∧
          ¬Erdos228.KernelNearGeometry.Near n theta I) ∧ I.2 ≤ theta := by
        simpa only [leftDistantIntervals, distantIntervals,
          Finset.mem_filter] using hI
      exact abs_principalIntegral_le_endpointVariation hn
        (F.ordered I hI'.1.1) (F.grid_endpoints I hI'.1.1)
        (Or.inl (leftDistant_upper hn F hI))
    _ = (∑ I ∈ leftDistantIntervals F theta,
          ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹)) / n := by
      rw [Finset.sum_div]
    _ ≤ ((n : ℝ) / Real.pi) / n :=
      div_le_div_of_nonneg_right
        (sum_left_endpointVariation_le hn F htheta) hnR.le
    _ = 1 / Real.pi := by
      field_simp [hn0, Real.pi_ne_zero]

private lemma sum_right_abs_principalIntegral_le {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ rightDistantIntervals F theta, |principalIntegral n I theta| ≤
      1 / Real.pi := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  calc
    ∑ I ∈ rightDistantIntervals F theta, |principalIntegral n I theta| ≤
        ∑ I ∈ rightDistantIntervals F theta,
          (((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) / n) := by
      apply Finset.sum_le_sum
      intro I hI
      have hI' : (I ∈ F.base ∧
          ¬Erdos228.KernelNearGeometry.Near n theta I) ∧ ¬I.2 ≤ theta := by
        simpa only [rightDistantIntervals, distantIntervals,
          Finset.mem_filter] using hI
      exact abs_principalIntegral_le_endpointVariation hn
        (F.ordered I hI'.1.1) (F.grid_endpoints I hI'.1.1)
        (Or.inr (rightDistant_lower hn F hI))
    _ = (∑ I ∈ rightDistantIntervals F theta,
          ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹)) / n := by
      rw [Finset.sum_div]
    _ ≤ ((n : ℝ) / Real.pi) / n :=
      div_le_div_of_nonneg_right
        (sum_right_endpointVariation_le hn F htheta) hnR.le
    _ = 1 / Real.pi := by
      field_simp [hn0, Real.pi_ne_zero]

/-- Concrete BBMST Claim 3.  For an evaluation angle in the closed first
quadrant, the total absolute principal-kernel contribution of every base
interval outside the strict near set is at most `2 / pi`. -/
theorem sum_abs_principalIntegral_distant_le_two_div_pi {n : ℕ}
    (hn : 0 < n) (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ distantBaseIntervals F theta,
        |principalIntegral n I.1 theta| ≤ 2 / Real.pi := by
  classical
  rw [sum_distantBaseIntervals_eq_sum_distantIntervals F theta
    (fun I ↦ |principalIntegral n I theta|)]
  have hsplit :
      (∑ I ∈ distantIntervals F theta, |principalIntegral n I theta|) =
        (∑ I ∈ leftDistantIntervals F theta,
          |principalIntegral n I theta|) +
        ∑ I ∈ rightDistantIntervals F theta,
          |principalIntegral n I theta| := by
    rw [leftDistantIntervals, rightDistantIntervals,
      Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  calc
    (∑ I ∈ leftDistantIntervals F theta, |principalIntegral n I theta|) +
        ∑ I ∈ rightDistantIntervals F theta,
          |principalIntegral n I theta| ≤
        1 / Real.pi + 1 / Real.pi :=
      add_le_add (sum_left_abs_principalIntegral_le hn F htheta)
        (sum_right_abs_principalIntegral_le hn F htheta)
    _ = 2 / Real.pi := by ring

end

end KernelDistantClaim

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/KernelReplacementMonotone.lean` -/

section
/-!
# The removable denominator-replacement amplitude

This file supplies the analytic ingredient in Claim 2 of the odd-kernel
argument.  The function `1 / sin u - 1 / u` is extended continuously at the
origin by writing it as the divided slope of the inverse sinc function.  On
`[-pi / 2, pi / 2]` the resulting function has nonnegative derivative, and
its total endpoint variation is exactly `2 - 4 / pi`.
-/

namespace KernelReplacementMonotone

open Real Set

noncomputable section

/-- The analytic extension at zero of `1 / sin u - 1 / u`. -/
def replacementAmplitude : ℝ → ℝ :=
  dslope (fun u : ℝ ↦ (Real.sinc u)⁻¹) 0

@[simp] theorem replacementAmplitude_zero : replacementAmplitude 0 = 0 := by
  rw [replacementAmplitude, dslope_same]
  have hsinc : AnalyticAt ℝ Real.sinc 0 := by
    rw [Real.sinc_eq_dslope]
    exact Real.analyticAt_sin.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt
  have hinv : DifferentiableAt ℝ (fun u : ℝ ↦ (Real.sinc u)⁻¹) 0 :=
    (hsinc.inv (by simp)).differentiableAt
  let d := deriv (fun u : ℝ ↦ (Real.sinc u)⁻¹) 0
  have hd : HasDerivAt (fun u : ℝ ↦ (Real.sinc u)⁻¹) d 0 := hinv.hasDerivAt
  have hdneg : HasDerivAt (fun u : ℝ ↦ (Real.sinc (-u))⁻¹) (-d) 0 := by
    have hcomp := HasDerivAt.comp_of_eq (x := (0 : ℝ)) hd
      (hasDerivAt_neg 0) (by simp)
    simpa [d, Function.comp_def] using hcomp
  have hdneg' : HasDerivAt (fun u : ℝ ↦ (Real.sinc u)⁻¹) (-d) 0 := by
    simpa only [Real.sinc_neg] using hdneg
  have := hd.unique hdneg'
  dsimp [d] at this ⊢
  linarith

/-- Away from the removable singularity, the extension is the original
denominator-replacement amplitude. -/
theorem replacementAmplitude_eq {u : ℝ} (hu : u ≠ 0)
    (hsu : Real.sin u ≠ 0) :
    replacementAmplitude u = 1 / Real.sin u - 1 / u := by
  have hmul : u * replacementAmplitude u = (Real.sinc u)⁻¹ - 1 := by
    simpa [replacementAmplitude] using
      (sub_smul_dslope (fun x : ℝ ↦ (Real.sinc x)⁻¹) 0 u)
  apply (mul_left_cancel₀ hu)
  rw [hmul, Real.sinc_of_ne_zero hu]
  field_simp [hu, hsu]

private lemma analyticAt_sinc_zero : AnalyticAt ℝ Real.sinc 0 := by
  rw [Real.sinc_eq_dslope]
  exact Real.analyticAt_sin.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt

theorem analyticAt_replacementAmplitude_zero :
    AnalyticAt ℝ replacementAmplitude 0 := by
  have hinv : AnalyticAt ℝ (fun u : ℝ ↦ (Real.sinc u)⁻¹) 0 :=
    analyticAt_sinc_zero.inv (by simp)
  exact hinv.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt

theorem sin_ne_zero_of_mem_half {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hu0 : u ≠ 0) : Real.sin u ≠ 0 := by
  intro hsu
  apply hu0
  exact (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [hu.1, Real.pi_pos])
    (by linarith [hu.2, Real.pi_pos])).mp hsu

theorem analyticAt_replacementAmplitude {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    AnalyticAt ℝ replacementAmplitude u := by
  by_cases hu0 : u = 0
  · simpa [hu0] using analyticAt_replacementAmplitude_zero
  have hsu := sin_ne_zero_of_mem_half hu hu0
  have hrhs : AnalyticAt ℝ (fun x : ℝ ↦ 1 / Real.sin x - 1 / x) u := by
    fun_prop
  apply hrhs.congr
  filter_upwards [eventually_ne_nhds hu0,
      (Real.continuous_sin.tendsto u) (isOpen_ne.mem_nhds hsu)] with x hx0 hsx
  exact (replacementAmplitude_eq hx0 hsx).symm

theorem differentiableAt_replacementAmplitude {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    DifferentiableAt ℝ replacementAmplitude u :=
  (analyticAt_replacementAmplitude hu).differentiableAt

theorem hasDerivAt_replacementAmplitude {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt replacementAmplitude (deriv replacementAmplitude u) u :=
  (differentiableAt_replacementAmplitude hu).hasDerivAt

theorem replacementAmplitude_mul_self_nonneg {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    0 ≤ replacementAmplitude u * u := by
  rcases lt_trichotomy u 0 with hu0 | rfl | hu0
  · have hsu : Real.sin u < 0 := by
      rw [← neg_pos, ← Real.sin_neg]
      exact Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hu0)
        (by linarith [hu.1, Real.pi_pos])
    rw [replacementAmplitude_eq hu0.ne (ne_of_lt hsu)]
    have hsle : u ≤ Real.sin u := by
      have := Real.sin_le (show 0 ≤ -u by linarith)
      rw [Real.sin_neg] at this
      linarith
    rw [show (1 / Real.sin u - 1 / u) * u =
        (u - Real.sin u) / Real.sin u by
      field_simp [hu0.ne, ne_of_lt hsu]
      ]
    exact div_nonneg_of_nonpos (sub_nonpos.mpr hsle) hsu.le
  · simp
  · have hsu : 0 < Real.sin u :=
      Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [hu.2, Real.pi_pos])
    rw [replacementAmplitude_eq hu0.ne' (ne_of_gt hsu)]
    have hsle := Real.sin_le hu0.le
    rw [show (1 / Real.sin u - 1 / u) * u =
        (u - Real.sin u) / Real.sin u by
      field_simp [hu0.ne', ne_of_gt hsu]
      ]
    exact div_nonneg (sub_nonneg.mpr hsle) hsu.le

/-- The derivative is nonnegative throughout the closed half-period.  At
zero this follows from the divided-slope limit; away from zero it reduces to
`u² cos u ≤ sin² u`. -/
theorem deriv_replacementAmplitude_nonneg {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    0 ≤ deriv replacementAmplitude u := by
  by_cases hu0 : u = 0
  · subst u
    have hd := analyticAt_replacementAmplitude_zero.differentiableAt.hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope] at hd
    apply ge_of_tendsto hd
    have hIcc : Icc (-(Real.pi / 2)) (Real.pi / 2) ∈ nhds (0 : ℝ) :=
      Icc_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have hIcc' : Icc (-(Real.pi / 2)) (Real.pi / 2) ∈
        nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ :=
      mem_nhdsWithin_of_mem_nhds hIcc
    filter_upwards [self_mem_nhdsWithin, hIcc'] with x hx hxmem
    have hx0 : x ≠ 0 := by simpa using hx
    simp only [slope, replacementAmplitude_zero, sub_zero, vsub_eq_sub,
      smul_eq_mul]
    rw [show x⁻¹ * replacementAmplitude x =
        (replacementAmplitude x * x) / x ^ 2 by
      field_simp [hx0]
      ]
    exact div_nonneg (replacementAmplitude_mul_self_nonneg hxmem) (sq_nonneg x)
  · have hsu := sin_ne_zero_of_mem_half hu hu0
    have heq : replacementAmplitude =ᶠ[nhds u]
        (fun x : ℝ ↦ 1 / Real.sin x - 1 / x) := by
      filter_upwards [eventually_ne_nhds hu0,
        (Real.continuous_sin.tendsto u) (isOpen_ne.mem_nhds hsu)] with x hx0 hsx
      exact replacementAmplitude_eq hx0 hsx
    have hbase := ((Real.hasDerivAt_sin u).inv hsu).sub
      ((hasDerivAt_id u).inv hu0)
    have hbase' : HasDerivAt (fun x : ℝ ↦ 1 / Real.sin x - 1 / x)
        (1 / u ^ 2 - Real.cos u / Real.sin u ^ 2) u := by
      have hfun : (fun x : ℝ ↦ 1 / Real.sin x - 1 / x) =
          Real.sin⁻¹ - id⁻¹ := by
        funext x
        simp only [one_div, Pi.sub_apply, Pi.inv_apply, id_eq]
      have hcoef : 1 / u ^ 2 - Real.cos u / Real.sin u ^ 2 =
          -Real.cos u / Real.sin u ^ 2 - -1 / id u ^ 2 := by
        simp only [id_eq]
        ring
      rw [hfun, hcoef]
      exact hbase
    have hderiv : HasDerivAt replacementAmplitude
        (1 / u ^ 2 - Real.cos u / Real.sin u ^ 2) u := by
      exact heq.hasDerivAt_iff.mpr hbase'
    rw [hderiv.deriv]
    have habs : |u| ≤ Real.pi / 2 := (abs_le).2 hu
    have hcos0 : 0 ≤ Real.cos u := Real.cos_nonneg_of_mem_Icc hu
    have hsin_sq : u ^ 2 * Real.cos u ≤ Real.sin u ^ 2 := by
      have ht0 : 0 ≤ |u| := abs_nonneg u
      have ht2 : |u| < 2 := by
        exact lt_of_le_of_lt habs (by linarith [Real.pi_lt_four])
      have htsq : |u| ^ 2 < (2 : ℝ) ^ 2 :=
        (sq_lt_sq₀ ht0 (by norm_num)).2 ht2
      have hsmall : |u| ^ 2 ≤ 12 := by norm_num at htsq ⊢; linarith
      have hslo := Real.sin_ge_sub_cube (abs_nonneg u)
      have hcosup := Erdos228.Kernel.cos_le_taylor_four (abs_nonneg u)
      rw [Real.cos_abs] at hcosup
      have hbase : 0 ≤ |u| - |u| ^ 3 / 6 := by
        rw [show |u| - |u| ^ 3 / 6 = |u| * (1 - |u| ^ 2 / 6) by ring]
        exact mul_nonneg ht0 (by nlinarith [htsq])
      have habspi : |u| ≤ Real.pi := by linarith [habs, Real.pi_pos]
      have hsine0 : 0 ≤ Real.sin |u| :=
        Real.sin_nonneg_of_nonneg_of_le_pi ht0 habspi
      have hsloSq : (|u| - |u| ^ 3 / 6) ^ 2 ≤ Real.sin |u| ^ 2 :=
        (sq_le_sq₀ hbase hsine0).2 hslo
      have habssin := Real.abs_sin_eq_sin_abs_of_abs_le_pi habspi
      have hsinSqEq : Real.sin |u| ^ 2 = Real.sin u ^ 2 := by
        rw [← habssin, sq_abs]
      have hcosmult : |u| ^ 2 * Real.cos u ≤
          |u| ^ 2 * (1 - |u| ^ 2 / 2 + |u| ^ 4 / 24) :=
        mul_le_mul_of_nonneg_left hcosup (sq_nonneg |u|)
      have hprod : 0 ≤ |u| ^ 4 * (12 - |u| ^ 2) :=
        mul_nonneg (pow_nonneg ht0 4) (sub_nonneg.mpr hsmall)
      have hpoly : |u| ^ 2 * (1 - |u| ^ 2 / 2 + |u| ^ 4 / 24) ≤
          (|u| - |u| ^ 3 / 6) ^ 2 := by
        nlinarith
      rw [← sq_abs u, ← hsinSqEq]
      exact hcosmult.trans (hpoly.trans hsloSq)
    have hden : 0 < u ^ 2 * Real.sin u ^ 2 :=
      mul_pos (sq_pos_of_ne_zero hu0) (sq_pos_of_ne_zero hsu)
    rw [show 1 / u ^ 2 - Real.cos u / Real.sin u ^ 2 =
        (Real.sin u ^ 2 - u ^ 2 * Real.cos u) /
          (u ^ 2 * Real.sin u ^ 2) by
      field_simp [hu0, hsu]
      ]
    exact div_nonneg (sub_nonneg.mpr hsin_sq) hden.le

/-- The derivative data in precisely the form used by the smooth grid
oscillation estimate. -/
theorem replacementAmplitude_derivative_data :
    (∀ u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivAt replacementAmplitude (deriv replacementAmplitude u) u) ∧
    ContinuousOn (deriv replacementAmplitude)
      (Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧
    (∀ u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2),
      0 ≤ deriv replacementAmplitude u) := by
  refine ⟨fun u hu ↦ hasDerivAt_replacementAmplitude hu, ?_,
    fun u hu ↦ deriv_replacementAmplitude_nonneg hu⟩
  intro u hu
  exact (analyticAt_replacementAmplitude hu).deriv.continuousAt.continuousWithinAt

theorem monotoneOn_replacementAmplitude :
    MonotoneOn replacementAmplitude
      (Icc (-(Real.pi / 2)) (Real.pi / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun u hu ↦
      (analyticAt_replacementAmplitude hu).continuousAt.continuousWithinAt
  · exact fun u hu ↦
      (differentiableAt_replacementAmplitude (interior_subset hu)).differentiableWithinAt
  · intro u hu
    exact deriv_replacementAmplitude_nonneg (interior_subset hu)

@[simp] theorem replacementAmplitude_pi_div_two :
    replacementAmplitude (Real.pi / 2) = 1 - 2 / Real.pi := by
  rw [replacementAmplitude_eq (by positivity) (by simp), Real.sin_pi_div_two]
  field_simp [Real.pi_ne_zero]

@[simp] theorem replacementAmplitude_neg_pi_div_two :
    replacementAmplitude (-(Real.pi / 2)) = -(1 - 2 / Real.pi) := by
  rw [replacementAmplitude_eq
      (neg_ne_zero.mpr (div_ne_zero Real.pi_ne_zero (by norm_num))) (by simp), Real.sin_neg,
    Real.sin_pi_div_two]
  field_simp [Real.pi_ne_zero]
  ring

/-- The total variation used after telescoping all Claim-2 intervals. -/
theorem replacementAmplitude_endpoint_variation :
    replacementAmplitude (Real.pi / 2) -
      replacementAmplitude (-(Real.pi / 2)) = 2 - 4 / Real.pi := by
  rw [replacementAmplitude_pi_div_two, replacementAmplitude_neg_pi_div_two]
  ring

end

end KernelReplacementMonotone

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/KernelReflectedClaim.lean` -/

section
/-!
# The reflected-denominator estimate in BBMST Claim 1

The endpoints of every suitable interval lie on the `pi / n` grid.  After
translation by `theta`, the endpoint cosines in integration by parts are
therefore still equal.  The amplitude `1 / sin` is antitone to the left of
`pi / 2` and monotone to its right.  Non-strict separation is enough to
order and telescope the intervals on each side.  At most one interval
crosses the turning point, and shortness bounds that contribution directly.
-/

namespace KernelReflectedClaim

open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral

noncomputable section

open Erdos228.OddSine

/-- The reflected odd-kernel contribution of one base interval. -/
def reflectedIntegral (n : ℕ) (I : RealInterval) (theta : ℝ) : ℝ :=
  ∫ x in I.1..I.2,
    Real.sin (((2 * n : ℕ) : ℝ) * (x + theta)) / Real.sin (x + theta)

private def eta (n : ℕ) : ℝ := 100 * Real.pi / n

private def amplitude (theta x : ℝ) : ℝ := (Real.sin (x + theta))⁻¹

private def turningPoint (theta : ℝ) : ℝ := Real.pi / 2 - theta

private noncomputable def leftIntervals {n : ℕ}
    (F : SuitableIntervalFamily n) (theta : ℝ) : Finset RealInterval :=
  F.base.filter fun I ↦ I.2 ≤ turningPoint theta

private noncomputable def rightIntervals {n : ℕ}
    (F : SuitableIntervalFamily n) (theta : ℝ) : Finset RealInterval :=
  F.base.filter fun I ↦ turningPoint theta ≤ I.1

private noncomputable def crossingIntervals {n : ℕ}
    (F : SuitableIntervalFamily n) (theta : ℝ) : Finset RealInterval :=
  F.base.filter fun I ↦ I.1 < turningPoint theta ∧ turningPoint theta < I.2

private lemma eta_pos {n : ℕ} (hn : 0 < n) : 0 < eta n := by
  exact div_pos (mul_pos (by norm_num) Real.pi_pos) (by exact_mod_cast hn)

private lemma eta_le_pi_div_two {n : ℕ} (hn : 4096 ≤ n) :
    eta n ≤ Real.pi / 2 := by
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  dsimp [eta]
  apply (div_le_iff₀ hnpos).2
  nlinarith [Real.pi_pos]

private lemma shifted_mem_band {n : ℕ} (F : SuitableIntervalFamily n)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ F.base) {x : ℝ}
    (hx : x ∈ Icc I.1 I.2) :
    eta n ≤ x + theta ∧ x + theta ≤ Real.pi - eta n := by
  have haway := F.away_from_axes I hI
  constructor
  · exact (show eta n ≤ I.1 from haway.1) |>.trans hx.1 |>.trans
      (le_add_of_nonneg_right htheta.1)
  · exact (add_le_add hx.2 htheta.2).trans
      (show I.2 + Real.pi / 2 ≤ Real.pi - eta n by
        dsimp [eta]
        linarith [haway.2])

private lemma sin_shifted_pos {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ F.base) {x : ℝ}
    (hx : x ∈ Icc I.1 I.2) : 0 < Real.sin (x + theta) := by
  have hband := shifted_mem_band F htheta hI hx
  have heta := eta_pos hn
  exact Real.sin_pos_of_pos_of_lt_pi (heta.trans_le hband.1)
    (by linarith [hband.2, heta])

private lemma sin_pos_of_mem_shifted_interval {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ F.base) {u : ℝ}
    (hu : u ∈ Icc (I.1 + theta) (I.2 + theta)) :
    0 < Real.sin u := by
  have hx : u - theta ∈ Icc I.1 I.2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  simpa only [sub_add_cancel] using
    sin_shifted_pos hn F htheta hI hx

private lemma endpointSeparated {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) :
    Set.Pairwise (↑F.base : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1) := by
  intro I hI J hJ hne
  have hgrid : 0 < Real.pi / (n : ℝ) := by
    exact div_pos Real.pi_pos (by exact_mod_cast hn)
  by_cases hfirst : I.1 ≤ J.1
  · left
    by_contra hnot
    have hJinI : J.1 ∈ Icc I.1 I.2 := ⟨hfirst, (lt_of_not_ge hnot).le⟩
    have hsep := F.separated hI hJ hne J.1 hJinI J.1
      ⟨le_rfl, F.ordered J hJ⟩
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hgrid) this
  · right
    have hsecond : J.1 ≤ I.1 := (lt_of_not_ge hfirst).le
    by_contra hnot
    have hIinJ : I.1 ∈ Icc J.1 J.2 := ⟨hsecond, (lt_of_not_ge hnot).le⟩
    have hsep := F.separated hI hJ hne I.1
      ⟨le_rfl, F.ordered I hI⟩ I.1 hIinJ
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hgrid) this

private abbrev Interval := ℝ × ℝ

/-- Endpoint variations of a finite separated family telescope on a
monotone branch. -/
private lemma endpoint_variation_le_of_monotone
    (s : Finset Interval) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set Interval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hmono : MonotoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.2 - f I.1) ≤ f U - f L := by
  classical
  let t : Finset (Lex Interval) := s.image toLex
  let m := t.card
  let e : Fin m ≃o ↥t := Finset.orderIsoOfFin t rfl
  have emem (k : Fin m) : ofLex ((e k : ↥t) : Lex Interval) ∈ s := by
    have hk := (e k).property
    change ((e k : ↥t) : Lex Interval) ∈ s.image toLex at hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨I, hI, hEq⟩
    simpa [← hEq] using hI
  let A : ℕ → ℝ := fun k ↦
    if hk : k < m then f (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval)).1 else f U
  let B : ℕ → ℝ := fun k ↦
    if hk : k < m then f (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval)).2 else f U
  let E : ℕ → ℝ := fun k ↦ B k - A k
  have hchain : ∀ k < m, B k ≤ A (k + 1) := by
    intro k hk
    simp only [B, A, dif_pos hk]
    by_cases hks : k + 1 < m
    · rw [dif_pos hks]
      apply hmono
      · exact ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans
            (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
      · exact ⟨(hinside _ (emem ⟨k + 1, hks⟩)).1,
          (hord _ (emem ⟨k + 1, hks⟩)).le.trans
            (hinside _ (emem ⟨k + 1, hks⟩)).2⟩
      have horder : e ⟨k, hk⟩ ≤ e ⟨k + 1, hks⟩ :=
        e.le_iff_le.mpr (by simp)
      have hleft : (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval)).1 ≤
          (ofLex ((e ⟨k + 1, hks⟩ : ↥t) : Lex Interval)).1 := by
        exact (Prod.Lex.le_iff.mp horder).elim (fun h ↦ h.le) (fun h ↦ h.1.le)
      have hne : ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval) ≠
          ofLex ((e ⟨k + 1, hks⟩ : ↥t) : Lex Interval) := by
        intro heq
        have heq' : e ⟨k, hk⟩ = e ⟨k + 1, hks⟩ := by
          apply Subtype.ext
          exact ofLex.injective heq
        have : (⟨k, hk⟩ : Fin m) = ⟨k + 1, hks⟩ := e.injective heq'
        simp at this
      rcases hsep (emem ⟨k, hk⟩) (emem ⟨k + 1, hks⟩) hne with hgood | hbad
      · exact hgood
      · have hstrict := hord _ (emem ⟨k + 1, hks⟩)
        linarith
    · rw [dif_neg hks]
      exact hmono
        ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
        ⟨hLU, le_rfl⟩ (hinside _ (emem ⟨k, hk⟩)).2
  have htelescope :=
    Erdos228.KernelClaims.sum_interval_error_le_of_monotone_endpoints
      (n := 1) (m := m) (A := A) (B := B) (E := E) (by norm_num)
      (fun k hk ↦ by simp [E]) hchain
  have hsum : (∑ I ∈ s, (f I.2 - f I.1)) =
      ∑ k ∈ Finset.range m, E k := by
    calc
      (∑ I ∈ s, (f I.2 - f I.1)) =
          ∑ J ∈ t, (f (ofLex J).2 - f (ofLex J).1) := by
            symm
            simpa [t] using (Finset.sum_image (s := s)
              (f := fun J : Lex Interval ↦ f (ofLex J).2 - f (ofLex J).1)
              toLex.injective.injOn)
      _ = ∑ J : ↥t, (f (ofLex (J.1 : Lex Interval)).2 -
          f (ofLex (J.1 : Lex Interval)).1) := by
            symm
            exact (Finset.sum_subtype (M := ℝ) (s := t) (p := fun J ↦ J ∈ t)
              (by simp) (fun J : Lex Interval ↦
                f (ofLex J).2 - f (ofLex J).1)).symm
      _ = ∑ i : Fin m, (f (ofLex ((e i : ↥t) : Lex Interval)).2 -
          f (ofLex ((e i : ↥t) : Lex Interval)).1) := by
            exact (e.toEquiv.sum_comp (fun J : ↥t ↦
              f (ofLex (J.1 : Lex Interval)).2 -
                f (ofLex (J.1 : Lex Interval)).1)).symm
      _ = ∑ i : Fin m, E i := by
            apply Finset.sum_congr rfl
            intro i _
            simp [E, A, B, i.isLt]
      _ = ∑ k ∈ Finset.range m, E k := Fin.sum_univ_eq_sum_range E m
  rw [hsum]
  by_cases hm : m = 0
  · simpa [hm] using sub_nonneg.mpr (hmono ⟨le_rfl, hLU⟩ ⟨hLU, le_rfl⟩ hLU)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hA0 : A 0 = f (ofLex ((e ⟨0, hmpos⟩ : ↥t) : Lex Interval)).1 := by
      simp [A, hmpos]
    have hAm : A m = f U := by simp [A]
    rw [hA0, hAm] at htelescope
    simp only [Nat.cast_one, div_one] at htelescope
    exact htelescope.trans (sub_le_sub_left
      (hmono ⟨le_rfl, hLU⟩
        ⟨(hinside _ (emem ⟨0, hmpos⟩)).1,
          (hord _ (emem ⟨0, hmpos⟩)).le.trans
            (hinside _ (emem ⟨0, hmpos⟩)).2⟩
        (hinside _ (emem ⟨0, hmpos⟩)).1) _)

private lemma endpoint_variation_le_of_antitone
    (s : Finset Interval) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set Interval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hanti : AntitoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.1 - f I.2) ≤ f L - f U := by
  have h := endpoint_variation_le_of_monotone s (-f) L U hord hLU hinside hsep
    (fun _ hx _ hy hxy ↦ neg_le_neg (hanti hx hy hxy))
  simpa only [Pi.neg_apply, neg_sub_neg] using h

private lemma endpoint_cos_eq {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ F.base) :
    Real.cos ((2 * (n : ℝ)) * (I.2 + theta)) =
      Real.cos ((2 * (n : ℝ)) * (I.1 + theta)) := by
  obtain ⟨a, b, ha, hb⟩ := F.grid_endpoints I hI
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [ha, hb]
  have hphase (k : ℤ) :
      (2 * (n : ℝ)) * ((k : ℝ) * Real.pi / n + theta) =
        (2 * (n : ℝ)) * theta + (k : ℝ) * (2 * Real.pi) := by
    field_simp [hnR]
    ring
  rw [hphase a, hphase b, Real.cos_add_int_mul_two_pi,
    Real.cos_add_int_mul_two_pi]

private lemma shifted_integral_eq {n : ℕ} (I : RealInterval) (theta : ℝ) :
    reflectedIntegral n I theta =
      ∫ u in I.1 + theta..I.2 + theta,
        (Real.sin u)⁻¹ * Real.sin ((2 * (n : ℝ)) * u) := by
  have hshift := intervalIntegral.integral_comp_add_right
    (fun u : ℝ ↦ (Real.sin u)⁻¹ * Real.sin ((2 * (n : ℝ)) * u))
    theta (a := I.1) (b := I.2)
  rw [← hshift]
  unfold reflectedIntegral
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [div_eq_mul_inv]
  ring

private lemma local_left_bound {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ leftIntervals F theta) :
    |reflectedIntegral n I theta| ≤
      (amplitude theta I.1 - amplitude theta I.2) / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hbase : I ∈ F.base := (Finset.mem_filter.mp hI).1
  have hside : I.2 ≤ turningPoint theta := (Finset.mem_filter.mp hI).2
  have hab : I.1 + theta ≤ I.2 + theta := by
    linarith [F.ordered I hbase]
  have hderiv : ∀ u ∈ Icc (I.1 + theta) (I.2 + theta),
      HasDerivAt Real.sin⁻¹ (-Real.cos u / Real.sin u ^ 2) u := by
    intro u hu
    exact (Real.hasDerivAt_sin u).inv
      (ne_of_gt (sin_pos_of_mem_shifted_interval hn0 F htheta hbase hu))
  have hcont : ContinuousOn (fun u : ℝ ↦ -Real.cos u / Real.sin u ^ 2)
      (Icc (I.1 + theta) (I.2 + theta)) := by
    intro u hu
    have hsin : Real.sin u ≠ 0 := ne_of_gt
      (sin_pos_of_mem_shifted_interval hn0 F htheta hbase hu)
    exact ((Real.continuous_cos.continuousAt.neg).div
      (Real.continuous_sin.continuousAt.pow 2) (pow_ne_zero 2 hsin)).continuousWithinAt
  have hnonpos : ∀ u ∈ Icc (I.1 + theta) (I.2 + theta),
      -Real.cos u / Real.sin u ^ 2 ≤ 0 := by
    intro u hu
    have huHalf : u ≤ Real.pi / 2 := by
      dsimp [turningPoint] at hside
      linarith [hu.2]
    have huNonneg : -(Real.pi / 2) ≤ u := by
      have hx : u - theta ∈ Icc I.1 I.2 :=
        ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hband := shifted_mem_band F htheta hbase hx
      linarith [hband.1, eta_pos hn0, Real.pi_pos]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Real.cos_nonneg_of_mem_Icc ⟨huNonneg, huHalf⟩))
      (sq_nonneg _)
  have hosc := Erdos228.KernelClaims.abs_integral_mul_sin_le_of_deriv_nonpos
    (h := Real.sin⁻¹) (h' := fun u : ℝ ↦ -Real.cos u / Real.sin u ^ 2)
    hn0 hab hderiv hcont hnonpos (endpoint_cos_eq hn0 F hbase)
  rw [shifted_integral_eq]
  have hamp : amplitude theta I.2 ≤ amplitude theta I.1 := by
    have hsinA : 0 < Real.sin (I.1 + theta) :=
      sin_shifted_pos hn0 F htheta hbase ⟨le_rfl, F.ordered I hbase⟩
    have hbandA := shifted_mem_band F htheta hbase
      ⟨le_rfl, F.ordered I hbase⟩
    have hsinmono : Real.sin (I.1 + theta) ≤ Real.sin (I.2 + theta) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [hbandA.1, eta_pos hn0, Real.pi_pos])
        (by dsimp [turningPoint] at hside; linarith)
        (by linarith [F.ordered I hbase])
    simpa only [amplitude, one_div] using
      one_div_le_one_div_of_le hsinA hsinmono
  change |∫ u in I.1 + theta..I.2 + theta,
      (Real.sin u)⁻¹ * Real.sin ((2 * (n : ℝ)) * u)| ≤
    |(Real.sin (I.2 + theta))⁻¹ - (Real.sin (I.1 + theta))⁻¹| / n at hosc
  have hamp' : (Real.sin (I.2 + theta))⁻¹ ≤
      (Real.sin (I.1 + theta))⁻¹ := by simpa only [amplitude] using hamp
  rw [abs_of_nonpos (sub_nonpos.mpr hamp')] at hosc
  simpa only [amplitude, neg_sub] using hosc

private lemma local_right_bound {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ rightIntervals F theta) :
    |reflectedIntegral n I theta| ≤
      (amplitude theta I.2 - amplitude theta I.1) / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hbase : I ∈ F.base := (Finset.mem_filter.mp hI).1
  have hside : turningPoint theta ≤ I.1 := (Finset.mem_filter.mp hI).2
  have hab : I.1 + theta ≤ I.2 + theta := by
    linarith [F.ordered I hbase]
  have hderiv : ∀ u ∈ Icc (I.1 + theta) (I.2 + theta),
      HasDerivAt Real.sin⁻¹ (-Real.cos u / Real.sin u ^ 2) u := by
    intro u hu
    exact (Real.hasDerivAt_sin u).inv
      (ne_of_gt (sin_pos_of_mem_shifted_interval hn0 F htheta hbase hu))
  have hcont : ContinuousOn (fun u : ℝ ↦ -Real.cos u / Real.sin u ^ 2)
      (Icc (I.1 + theta) (I.2 + theta)) := by
    intro u hu
    have hsin : Real.sin u ≠ 0 := ne_of_gt
      (sin_pos_of_mem_shifted_interval hn0 F htheta hbase hu)
    exact ((Real.continuous_cos.continuousAt.neg).div
      (Real.continuous_sin.continuousAt.pow 2) (pow_ne_zero 2 hsin)).continuousWithinAt
  have hnonneg : ∀ u ∈ Icc (I.1 + theta) (I.2 + theta),
      0 ≤ -Real.cos u / Real.sin u ^ 2 := by
    intro u hu
    have huHalf : Real.pi / 2 ≤ u := by
      dsimp [turningPoint] at hside
      linarith [hu.1]
    have huTop : u ≤ Real.pi + Real.pi / 2 := by
      have hx : u - theta ∈ Icc I.1 I.2 :=
        ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hband := shifted_mem_band F htheta hbase hx
      linarith [hband.2, eta_pos hn0, Real.pi_pos]
    exact div_nonneg (neg_nonneg.mpr
      (Real.cos_nonpos_of_pi_div_two_le_of_le huHalf huTop)) (sq_nonneg _)
  have hosc := Erdos228.KernelClaims.abs_integral_mul_sin_le_of_deriv_nonneg
    (h := Real.sin⁻¹) (h' := fun u : ℝ ↦ -Real.cos u / Real.sin u ^ 2)
    hn0 hab hderiv hcont hnonneg (endpoint_cos_eq hn0 F hbase)
  rw [shifted_integral_eq]
  have hamp : amplitude theta I.1 ≤ amplitude theta I.2 := by
    have hsinB : 0 < Real.sin (I.2 + theta) :=
      sin_shifted_pos hn0 F htheta hbase ⟨F.ordered I hbase, le_rfl⟩
    have hcompOrder : Real.pi - (I.2 + theta) ≤
        Real.pi - (I.1 + theta) := by linarith [F.ordered I hbase]
    have hcompTop : Real.pi - (I.1 + theta) ≤ Real.pi / 2 := by
      dsimp [turningPoint] at hside
      linarith
    have hcompLow : -(Real.pi / 2) ≤ Real.pi - (I.2 + theta) := by
      have hband := shifted_mem_band F htheta hbase
        ⟨F.ordered I hbase, le_rfl⟩
      linarith [hband.2, eta_pos hn0, Real.pi_pos]
    have hsinmono := Real.sin_le_sin_of_le_of_le_pi_div_two
      hcompLow hcompTop hcompOrder
    rw [Real.sin_pi_sub, Real.sin_pi_sub] at hsinmono
    simpa only [amplitude, one_div] using
      one_div_le_one_div_of_le hsinB hsinmono
  change |∫ u in I.1 + theta..I.2 + theta,
      (Real.sin u)⁻¹ * Real.sin ((2 * (n : ℝ)) * u)| ≤
    |(Real.sin (I.2 + theta))⁻¹ - (Real.sin (I.1 + theta))⁻¹| / n at hosc
  have hamp' : (Real.sin (I.1 + theta))⁻¹ ≤
      (Real.sin (I.2 + theta))⁻¹ := by simpa only [amplitude] using hamp
  rw [abs_of_nonneg (sub_nonneg.mpr hamp')] at hosc
  simpa only [amplitude] using hosc

private lemma amplitude_antitone_left {n : ℕ} (hn : 4096 ≤ n)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hbranch : eta n ≤ turningPoint theta) :
    AntitoneOn (amplitude theta) (Icc (eta n) (turningPoint theta)) := by
  intro x hx y hy hxy
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hsinX : 0 < Real.sin (x + theta) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [hx.1, eta_pos hn0, htheta.1]
    · dsimp [turningPoint] at hy
      linarith [hy.2, Real.pi_pos]
  have hsinmono : Real.sin (x + theta) ≤ Real.sin (y + theta) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hx.1, eta_pos hn0, htheta.1, Real.pi_pos])
      (by dsimp [turningPoint] at hy; linarith [hy.2])
      (by linarith)
  simpa only [amplitude, one_div] using
    one_div_le_one_div_of_le hsinX hsinmono

private lemma amplitude_monotone_right {n : ℕ} (hn : 4096 ≤ n)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hbranch : turningPoint theta ≤ Real.pi / 2 - eta n) :
    MonotoneOn (amplitude theta)
      (Icc (turningPoint theta) (Real.pi / 2 - eta n)) := by
  intro x hx y hy hxy
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hsinY : 0 < Real.sin (y + theta) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · dsimp [turningPoint] at hx
      linarith [hx.1, Real.pi_pos]
    · linarith [hy.2, eta_pos hn0, htheta.2]
  have hcompOrder : Real.pi - (y + theta) ≤ Real.pi - (x + theta) := by
    linarith
  have hcompTop : Real.pi - (x + theta) ≤ Real.pi / 2 := by
    dsimp [turningPoint] at hx
    linarith [hx.1]
  have hcompLow : -(Real.pi / 2) ≤ Real.pi - (y + theta) := by
    linarith [hy.2, eta_pos hn0, htheta.2, Real.pi_pos]
  have hsinmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    hcompLow hcompTop hcompOrder
  rw [Real.sin_pi_sub, Real.sin_pi_sub] at hsinmono
  simpa only [amplitude, one_div] using
    one_div_le_one_div_of_le hsinY hsinmono

private lemma sum_left_le {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ leftIntervals F theta, |reflectedIntegral n I theta| ≤
      1 / ((n : ℝ) * Real.sin (eta n)) := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  by_cases hbranch : eta n ≤ turningPoint theta
  · have hvar := endpoint_variation_le_of_antitone
      (leftIntervals F theta) (amplitude theta) (eta n) (turningPoint theta)
      (fun I hI ↦ F.nondegenerate I (Finset.mem_filter.mp hI).1)
      hbranch
      (fun I hI ↦ ⟨(F.away_from_axes I (Finset.mem_filter.mp hI).1).1,
        (Finset.mem_filter.mp hI).2⟩)
      (fun I hI J hJ hne ↦ endpointSeparated hn0 F
        (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hJ).1 hne)
      (amplitude_antitone_left hn htheta hbranch)
    have hturn : amplitude theta (turningPoint theta) = 1 := by
      simp [amplitude, turningPoint]
    have hampEta : amplitude theta (eta n) ≤ 1 / Real.sin (eta n) := by
      have hsineta : 0 < Real.sin (eta n) :=
        Real.sin_pos_of_pos_of_lt_pi (eta_pos hn0)
          ((eta_le_pi_div_two hn).trans_lt (by linarith [Real.pi_pos]))
      have hsinmono : Real.sin (eta n) ≤ Real.sin (eta n + theta) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [eta_pos hn0, Real.pi_pos])
          (by dsimp [turningPoint] at hbranch; linarith)
          (by linarith [htheta.1])
      simpa only [amplitude, one_div] using
        one_div_le_one_div_of_le hsineta hsinmono
    calc
      ∑ I ∈ leftIntervals F theta, |reflectedIntegral n I theta| ≤
          ∑ I ∈ leftIntervals F theta,
            (amplitude theta I.1 - amplitude theta I.2) / n :=
        Finset.sum_le_sum fun I hI ↦ local_left_bound hn F htheta hI
      _ = (∑ I ∈ leftIntervals F theta,
            (amplitude theta I.1 - amplitude theta I.2)) / n := by
        rw [Finset.sum_div]
      _ ≤ (1 / Real.sin (eta n)) / n := by
        apply (div_le_div_iff_of_pos_right (by exact_mod_cast hn0)).2
        rw [hturn] at hvar
        linarith
      _ = 1 / ((n : ℝ) * Real.sin (eta n)) := by
        field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn0]
  · have hempty : leftIntervals F theta = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hmem
      have hI := (Finset.mem_filter.mp hmem).1
      have hside := (Finset.mem_filter.mp hmem).2
      have haway := (F.away_from_axes I hI).1
      have hstrict := F.nondegenerate I hI
      dsimp [eta, turningPoint] at hbranch hside
      linarith
    rw [hempty]
    simp
    have hsineta : 0 < Real.sin (eta n) :=
      Real.sin_pos_of_pos_of_lt_pi (eta_pos hn0)
        ((eta_le_pi_div_two hn).trans_lt (by linarith [Real.pi_pos]))
    exact mul_nonneg (inv_nonneg.mpr hsineta.le)
      (inv_nonneg.mpr (show (0 : ℝ) ≤ n by positivity))

private lemma sum_right_le {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ rightIntervals F theta, |reflectedIntegral n I theta| ≤
      1 / ((n : ℝ) * Real.sin (eta n)) := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  by_cases hbranch : turningPoint theta ≤ Real.pi / 2 - eta n
  · have hvar := endpoint_variation_le_of_monotone
      (rightIntervals F theta) (amplitude theta) (turningPoint theta)
        (Real.pi / 2 - eta n)
      (fun I hI ↦ F.nondegenerate I (Finset.mem_filter.mp hI).1)
      hbranch
      (fun I hI ↦ ⟨(Finset.mem_filter.mp hI).2,
        (F.away_from_axes I (Finset.mem_filter.mp hI).1).2⟩)
      (fun I hI J hJ hne ↦ endpointSeparated hn0 F
        (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hJ).1 hne)
      (amplitude_monotone_right hn htheta hbranch)
    have hturn : amplitude theta (turningPoint theta) = 1 := by
      simp [amplitude, turningPoint]
    have hampU : amplitude theta (Real.pi / 2 - eta n) ≤
        1 / Real.sin (eta n) := by
      have hsineta : 0 < Real.sin (eta n) :=
        Real.sin_pos_of_pos_of_lt_pi (eta_pos hn0)
          ((eta_le_pi_div_two hn).trans_lt (by linarith [Real.pi_pos]))
      have hcompOrder : eta n ≤
          Real.pi - ((Real.pi / 2 - eta n) + theta) := by
        linarith [htheta.2]
      have hcompTop : Real.pi - ((Real.pi / 2 - eta n) + theta) ≤
          Real.pi / 2 := by
        dsimp [turningPoint] at hbranch
        linarith
      have hsinmono := Real.sin_le_sin_of_le_of_le_pi_div_two
        (x := eta n)
        (y := Real.pi - ((Real.pi / 2 - eta n) + theta))
        (by linarith [eta_pos hn0, Real.pi_pos]) hcompTop hcompOrder
      rw [Real.sin_pi_sub] at hsinmono
      simpa only [amplitude, one_div] using
        one_div_le_one_div_of_le hsineta hsinmono
    calc
      ∑ I ∈ rightIntervals F theta, |reflectedIntegral n I theta| ≤
          ∑ I ∈ rightIntervals F theta,
            (amplitude theta I.2 - amplitude theta I.1) / n :=
        Finset.sum_le_sum fun I hI ↦ local_right_bound hn F htheta hI
      _ = (∑ I ∈ rightIntervals F theta,
            (amplitude theta I.2 - amplitude theta I.1)) / n := by
        rw [Finset.sum_div]
      _ ≤ (1 / Real.sin (eta n)) / n := by
        apply (div_le_div_iff_of_pos_right (by exact_mod_cast hn0)).2
        rw [hturn] at hvar
        linarith
      _ = 1 / ((n : ℝ) * Real.sin (eta n)) := by
        field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn0]
  · have hempty : rightIntervals F theta = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hmem
      have hI := (Finset.mem_filter.mp hmem).1
      have hside := (Finset.mem_filter.mp hmem).2
      have haway := (F.away_from_axes I hI).2
      have hstrict := F.nondegenerate I hI
      dsimp [eta, turningPoint] at hbranch hside
      linarith
    rw [hempty]
    simp
    have hsineta : 0 < Real.sin (eta n) :=
      Real.sin_pos_of_pos_of_lt_pi (eta_pos hn0)
        ((eta_le_pi_div_two hn).trans_lt (by linarith [Real.pi_pos]))
    exact mul_nonneg (inv_nonneg.mpr hsineta.le)
      (inv_nonneg.mpr (show (0 : ℝ) ≤ n by positivity))

private lemma crossing_pointwise_bound {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ crossingIntervals F theta) :
    |reflectedIntegral n I theta| ≤ 12 * Real.pi / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hbase : I ∈ F.base := (Finset.mem_filter.mp hI).1
  have hcross := (Finset.mem_filter.mp hI).2
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := I.1) (b := I.2) (C := (2 : ℝ))
    (f := fun x : ℝ ↦
      Real.sin (((2 * n : ℕ) : ℝ) * (x + theta)) / Real.sin (x + theta))
    (fun x hx ↦ by
      rw [Set.uIoc_of_le (F.ordered I hbase)] at hx
      have hxI : x ∈ Icc I.1 I.2 := ⟨hx.1.le, hx.2⟩
      have hdist : |(x + theta) - Real.pi / 2| ≤ 6 * Real.pi / n := by
        have hwidth := F.short I hbase
        dsimp [turningPoint] at hcross
        rw [abs_le]
        constructor <;> linarith [hxI.1, hxI.2]
      have hsmall : |(x + theta) - Real.pi / 2| ≤ 1 := by
        have hpi4 : Real.pi < 4 := Real.pi_lt_four
        have hfrac : 6 * Real.pi / (n : ℝ) < 1 := by
          apply (div_lt_iff₀ hnRpos).2
          nlinarith
        exact hdist.trans hfrac.le
      have hcos : (1 : ℝ) / 2 ≤ Real.cos ((x + theta) - Real.pi / 2) := by
        have hlow := Real.one_sub_sq_div_two_le_cos
          (x := (x + theta) - Real.pi / 2)
        have hsq : ((x + theta) - Real.pi / 2) ^ 2 ≤ 1 := by
          have habs0 : 0 ≤ |(x + theta) - Real.pi / 2| := abs_nonneg _
          nlinarith [sq_abs ((x + theta) - Real.pi / 2)]
        linarith
      have hsin : (1 : ℝ) / 2 ≤ Real.sin (x + theta) := by
        rw [← Real.cos_sub_pi_div_two]
        exact hcos
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by linarith : 0 ≤ Real.sin (x + theta))]
      apply (div_le_iff₀ (by linarith : 0 < Real.sin (x + theta))).2
      nlinarith [Real.abs_sin_le_one
        (((2 * n : ℕ) : ℝ) * (x + theta))])
  unfold reflectedIntegral
  rw [Real.norm_eq_abs] at hnorm
  calc
    |∫ x in I.1..I.2,
        Real.sin (((2 * n : ℕ) : ℝ) * (x + theta)) /
          Real.sin (x + theta)| ≤ 2 * |I.2 - I.1| := hnorm
    _ = 2 * (I.2 - I.1) := by
      rw [abs_of_nonneg (sub_nonneg.mpr (F.ordered I hbase))]
    _ ≤ 2 * (6 * Real.pi / n) := by
      gcongr
      exact F.short I hbase
    _ = 12 * Real.pi / n := by ring

private lemma card_crossing_le_one {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) (theta : ℝ) :
    (crossingIntervals F theta).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro I hI J hJ
  have hbaseI := (Finset.mem_filter.mp hI).1
  have hbaseJ := (Finset.mem_filter.mp hJ).1
  by_contra hne
  have hcrossI := (Finset.mem_filter.mp hI).2
  have hcrossJ := (Finset.mem_filter.mp hJ).2
  have hsep := F.separated hbaseI hbaseJ hne (turningPoint theta)
    ⟨hcrossI.1.le, hcrossI.2.le⟩ (turningPoint theta)
    ⟨hcrossJ.1.le, hcrossJ.2.le⟩
  have hpi : 0 < Real.pi / (n : ℝ) :=
    div_pos Real.pi_pos (by exact_mod_cast hn)
  have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
  exact (not_le_of_gt hpi) this

private lemma sum_crossing_le {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ crossingIntervals F theta, |reflectedIntegral n I theta| ≤
      12 * Real.pi / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  calc
    ∑ I ∈ crossingIntervals F theta, |reflectedIntegral n I theta| ≤
        ∑ _I ∈ crossingIntervals F theta, 12 * Real.pi / n :=
      Finset.sum_le_sum fun I hI ↦ crossing_pointwise_bound hn F htheta hI
    _ = ((crossingIntervals F theta).card : ℝ) * (12 * Real.pi / n) := by simp
    _ ≤ 1 * (12 * Real.pi / n) := by
      gcongr
      exact_mod_cast card_crossing_le_one hn0 F theta
    _ = 12 * Real.pi / n := one_mul _

private lemma base_partition {n : ℕ} (F : SuitableIntervalFamily n) (theta : ℝ) :
    F.base = (leftIntervals F theta ∪ rightIntervals F theta) ∪
      crossingIntervals F theta := by
  classical
  ext I
  simp only [leftIntervals, rightIntervals, crossingIntervals, Finset.mem_filter,
    Finset.mem_union]
  constructor
  · intro hI
    by_cases hleft : I.2 ≤ turningPoint theta
    · exact Or.inl (Or.inl ⟨hI, hleft⟩)
    · by_cases hright : turningPoint theta ≤ I.1
      · exact Or.inl (Or.inr ⟨hI, hright⟩)
      · exact Or.inr ⟨hI, lt_of_not_ge hright, lt_of_not_ge hleft⟩
  · rintro ((⟨hI, _⟩ | ⟨hI, _⟩) | ⟨hI, _⟩) <;> exact hI

private lemma disjoint_left_right {n : ℕ} (F : SuitableIntervalFamily n)
    (theta : ℝ) : Disjoint (leftIntervals F theta) (rightIntervals F theta) := by
  classical
  rw [Finset.disjoint_left]
  intro I hleft hright
  have hbase := (Finset.mem_filter.mp hleft).1
  have hstrict := F.nondegenerate I hbase
  linarith [(Finset.mem_filter.mp hleft).2, (Finset.mem_filter.mp hright).2]

private lemma disjoint_sides_crossing {n : ℕ} (F : SuitableIntervalFamily n)
    (theta : ℝ) :
    Disjoint (leftIntervals F theta ∪ rightIntervals F theta)
      (crossingIntervals F theta) := by
  classical
  rw [Finset.disjoint_left]
  intro I hsides hcross
  simp only [Finset.mem_union] at hsides
  have hc := (Finset.mem_filter.mp hcross).2
  rcases hsides with hleft | hright
  · linarith [(Finset.mem_filter.mp hleft).2, hc.2]
  · linarith [(Finset.mem_filter.mp hright).2, hc.1]

/-- Concrete BBMST Claim 1 for a suitable interval family.  The two
monotone tails telescope to one reciprocal-sine endpoint each, and the
unique interval crossing `pi / 2 - theta` costs at most `12*pi/n`. -/
theorem sum_abs_reflectedIntegral_le {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I : (↑F.base : Type), |reflectedIntegral n I.1 theta| ≤
      2 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) + 12 * Real.pi / n := by
  classical
  rw [← Finset.sum_subtype F.base (by simp)
    (fun I ↦ |reflectedIntegral n I theta|)]
  rw [base_partition F theta,
    Finset.sum_union (disjoint_sides_crossing F theta),
    Finset.sum_union (disjoint_left_right F theta)]
  have hleft := sum_left_le hn F htheta
  have hright := sum_right_le hn F htheta
  have hcross := sum_crossing_le hn F htheta
  dsimp [eta] at hleft hright
  calc
    (∑ I ∈ leftIntervals F theta, |reflectedIntegral n I theta|) +
          (∑ I ∈ rightIntervals F theta, |reflectedIntegral n I theta|) +
        ∑ I ∈ crossingIntervals F theta, |reflectedIntegral n I theta| ≤
      1 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
        1 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
          12 * Real.pi / n := by linarith
    _ = 2 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
          12 * Real.pi / n := by ring

end

end KernelReflectedClaim

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/ConcreteKernelClaims.lean` -/

section
/-!
# Concrete aggregate kernel estimates for Erdős Problem 228

This file turns the one-interval calculus estimates in `KernelClaims` into
estimates for an actual `OddSine.SuitableIntervalFamily`.  The only
bookkeeping needed for this passage is that a finite separated family of
real intervals can be put in increasing order and its endpoint variations
then telescope.
-/

namespace ConcreteKernelClaims

open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral

noncomputable section

open Erdos228.OddSine

private abbrev Interval := ℝ × ℝ

/-! ## A finite-family telescope -/

theorem endpoint_variation_le_of_monotone
    (s : Finset Interval) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set Interval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hmono : MonotoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.2 - f I.1) ≤ f U - f L := by
  classical
  let t : Finset (Lex Interval) := s.image toLex
  let m := t.card
  let e : Fin m ≃o ↥t := Finset.orderIsoOfFin t rfl
  have emem (k : Fin m) : ofLex ((e k : ↥t) : Lex Interval) ∈ s := by
    have hk := (e k).property
    change ((e k : ↥t) : Lex Interval) ∈ s.image toLex at hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨I, hI, hEq⟩
    simpa [← hEq] using hI
  let A : ℕ → ℝ := fun k ↦
    if hk : k < m then f (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval)).1 else f U
  let B : ℕ → ℝ := fun k ↦
    if hk : k < m then f (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval)).2 else f U
  let E : ℕ → ℝ := fun k ↦ B k - A k
  have hchain : ∀ k < m, B k ≤ A (k + 1) := by
    intro k hk
    simp only [B, A, dif_pos hk]
    by_cases hks : k + 1 < m
    · rw [dif_pos hks]
      apply hmono
      · exact ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans
            (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
      · exact ⟨(hinside _ (emem ⟨k + 1, hks⟩)).1,
          (hord _ (emem ⟨k + 1, hks⟩)).le.trans
            (hinside _ (emem ⟨k + 1, hks⟩)).2⟩
      have horder : e ⟨k, hk⟩ ≤ e ⟨k + 1, hks⟩ :=
        e.le_iff_le.mpr (by simp)
      have hleft : (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval)).1 ≤
          (ofLex ((e ⟨k + 1, hks⟩ : ↥t) : Lex Interval)).1 := by
        exact (Prod.Lex.le_iff.mp horder).elim (fun h ↦ h.le) (fun h ↦ h.1.le)
      have hne : ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval) ≠
          ofLex ((e ⟨k + 1, hks⟩ : ↥t) : Lex Interval) := by
        intro heq
        have heq' : e ⟨k, hk⟩ = e ⟨k + 1, hks⟩ := by
          apply Subtype.ext
          exact ofLex.injective heq
        have : (⟨k, hk⟩ : Fin m) = ⟨k + 1, hks⟩ := e.injective heq'
        simp at this
      rcases hsep (emem ⟨k, hk⟩) (emem ⟨k + 1, hks⟩) hne with hgood | hbad
      · exact hgood
      · have hstrict := hord _ (emem ⟨k + 1, hks⟩)
        linarith
    · rw [dif_neg hks]
      exact hmono
        ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
        ⟨hLU, le_rfl⟩ (hinside _ (emem ⟨k, hk⟩)).2
  have htelescope :=
    Erdos228.KernelClaims.sum_interval_error_le_of_monotone_endpoints
      (n := 1) (m := m) (A := A) (B := B) (E := E) (by norm_num)
      (fun k hk ↦ by simp [E]) hchain
  have hsum : (∑ I ∈ s, (f I.2 - f I.1)) = ∑ k ∈ Finset.range m, E k := by
    calc
      (∑ I ∈ s, (f I.2 - f I.1)) =
          ∑ J ∈ t, (f (ofLex J).2 - f (ofLex J).1) := by
            symm
            simpa [t] using (Finset.sum_image (s := s)
              (f := fun J : Lex Interval ↦ f (ofLex J).2 - f (ofLex J).1)
              toLex.injective.injOn)
      _ = ∑ J : ↥t, (f (ofLex (J.1 : Lex Interval)).2 -
          f (ofLex (J.1 : Lex Interval)).1) := by
            symm
            exact (Finset.sum_subtype (M := ℝ) (s := t) (p := fun J ↦ J ∈ t)
              (by simp) (fun J : Lex Interval ↦
                f (ofLex J).2 - f (ofLex J).1)).symm
      _ = ∑ i : Fin m, (f (ofLex ((e i : ↥t) : Lex Interval)).2 -
          f (ofLex ((e i : ↥t) : Lex Interval)).1) := by
            exact (e.toEquiv.sum_comp (fun J : ↥t ↦
              f (ofLex (J.1 : Lex Interval)).2 -
                f (ofLex (J.1 : Lex Interval)).1)).symm
      _ = ∑ i : Fin m, E i := by
            apply Finset.sum_congr rfl
            intro i _
            simp [E, A, B, i.isLt]
      _ = ∑ k ∈ Finset.range m, E k := Fin.sum_univ_eq_sum_range E m
  rw [hsum]
  by_cases hm : m = 0
  · simpa [hm] using sub_nonneg.mpr (hmono ⟨le_rfl, hLU⟩ ⟨hLU, le_rfl⟩ hLU)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hA0 : A 0 = f (ofLex ((e ⟨0, hmpos⟩ : ↥t) : Lex Interval)).1 := by
      simp [A, hmpos]
    have hAm : A m = f U := by simp [A]
    rw [hA0, hAm] at htelescope
    simp only [Nat.cast_one, div_one] at htelescope
    exact htelescope.trans (sub_le_sub_left
      (hmono ⟨le_rfl, hLU⟩
        ⟨(hinside _ (emem ⟨0, hmpos⟩)).1,
          (hord _ (emem ⟨0, hmpos⟩)).le.trans
            (hinside _ (emem ⟨0, hmpos⟩)).2⟩
        (hinside _ (emem ⟨0, hmpos⟩)).1) _)

theorem endpoint_variation_le_of_antitone
    (s : Finset Interval) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set Interval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hanti : AntitoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.1 - f I.2) ≤ f L - f U := by
  have h := endpoint_variation_le_of_monotone s (-f) L U hord hLU hinside hsep
    (fun _ hx _ hy hxy ↦ neg_le_neg (hanti hx hy hxy))
  simpa only [Pi.neg_apply, neg_sub_neg] using h

/-! ## Claim 2: replacement of `sin u` by `u` -/

/-- The removable denominator-replacement contribution on one base interval. -/
def replacementIntegral (n : ℕ) (I : RealInterval) (theta : ℝ) : ℝ :=
  ∫ x in I.1..I.2,
    Erdos228.KernelReplacementMonotone.replacementAmplitude (x - theta) *
      Real.sin ((2 * (n : ℝ)) * (x - theta))

private lemma endpointSeparated {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) :
    Set.Pairwise (↑F.base : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1) := by
  intro I hI J hJ hne
  have hgrid : 0 < Real.pi / (n : ℝ) :=
    div_pos Real.pi_pos (by exact_mod_cast hn)
  by_cases hfirst : I.1 ≤ J.1
  · left
    by_contra hnot
    have hJinI : J.1 ∈ Icc I.1 I.2 :=
      ⟨hfirst, (lt_of_not_ge hnot).le⟩
    have hsep := F.separated hI hJ hne J.1 hJinI J.1
      ⟨le_rfl, F.ordered J hJ⟩
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hgrid) this
  · right
    have hsecond : J.1 ≤ I.1 := (lt_of_not_ge hfirst).le
    by_contra hnot
    have hIinJ : I.1 ∈ Icc J.1 J.2 :=
      ⟨hsecond, (lt_of_not_ge hnot).le⟩
    have hsep := F.separated hI hJ hne I.1
      ⟨le_rfl, F.ordered I hI⟩ I.1 hIinJ
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hgrid) this

private lemma shifted_mem_half {n : ℕ} (F : SuitableIntervalFamily n)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ F.base) {u : ℝ}
    (hu : u ∈ Icc (I.1 - theta) (I.2 - theta)) :
    u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hquadrant := F.in_first_quadrant I hI
  constructor
  · linarith [hu.1, hquadrant.1, htheta.2]
  · linarith [hu.2, hquadrant.2, htheta.1]

private lemma shifted_endpoint_cos_eq {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ F.base) :
    Real.cos ((2 * (n : ℝ)) * (I.2 - theta)) =
      Real.cos ((2 * (n : ℝ)) * (I.1 - theta)) := by
  obtain ⟨a, b, ha, hb⟩ := F.grid_endpoints I hI
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [ha, hb]
  calc
    Real.cos ((2 * (n : ℝ)) * ((b : ℝ) * Real.pi / n - theta)) =
        Real.cos ((b : ℝ) * (2 * Real.pi) - (2 * (n : ℝ)) * theta) := by
          congr 1
          field_simp [hn0]
    _ = Real.cos ((2 * (n : ℝ)) * theta) :=
      Real.cos_int_mul_two_pi_sub _ b
    _ = Real.cos ((a : ℝ) * (2 * Real.pi) - (2 * (n : ℝ)) * theta) :=
      (Real.cos_int_mul_two_pi_sub _ a).symm
    _ = Real.cos ((2 * (n : ℝ)) * ((a : ℝ) * Real.pi / n - theta)) := by
          congr 1
          field_simp [hn0]

private lemma replacementIntegral_shifted (n : ℕ) (I : RealInterval)
    (theta : ℝ) :
    replacementIntegral n I theta =
      ∫ u in I.1 - theta..I.2 - theta,
        Erdos228.KernelReplacementMonotone.replacementAmplitude u *
          Real.sin ((2 * (n : ℝ)) * u) := by
  exact intervalIntegral.integral_comp_sub_right
    (fun u : ℝ ↦
      Erdos228.KernelReplacementMonotone.replacementAmplitude u *
        Real.sin ((2 * (n : ℝ)) * u)) theta

private lemma abs_replacementIntegral_le {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ F.base) :
    |replacementIntegral n I theta| ≤
      (Erdos228.KernelReplacementMonotone.replacementAmplitude (I.2 - theta) -
        Erdos228.KernelReplacementMonotone.replacementAmplitude (I.1 - theta)) / n := by
  rw [replacementIntegral_shifted]
  have hdata :=
    Erdos228.KernelReplacementMonotone.replacementAmplitude_derivative_data
  have hosc := Erdos228.KernelClaims.abs_integral_mul_sin_le_of_deriv_nonneg
    (h := Erdos228.KernelReplacementMonotone.replacementAmplitude)
    (h' := deriv Erdos228.KernelReplacementMonotone.replacementAmplitude)
    hn (sub_le_sub_right (F.ordered I hI) theta)
    (fun u hu ↦ hdata.1 u (shifted_mem_half F htheta hI hu))
    (hdata.2.1.mono (fun u hu ↦ shifted_mem_half F htheta hI hu))
    (fun u hu ↦ hdata.2.2 u (shifted_mem_half F htheta hI hu))
    (shifted_endpoint_cos_eq hn F hI)
  have hmono := Erdos228.KernelReplacementMonotone.monotoneOn_replacementAmplitude
    (shifted_mem_half F htheta hI
      ⟨le_rfl, sub_le_sub_right (F.ordered I hI) theta⟩)
    (shifted_mem_half F htheta hI
      ⟨sub_le_sub_right (F.ordered I hI) theta, le_rfl⟩)
    (sub_le_sub_right (F.ordered I hI) theta)
  rw [abs_of_nonneg (sub_nonneg.mpr hmono)] at hosc
  exact hosc

/-- Claim 2, aggregated over the concrete suitable interval family. -/
theorem sum_abs_replacementIntegral_le {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ F.base, |replacementIntegral n I theta| ≤
      (2 - 4 / Real.pi) / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  let f : ℝ → ℝ := fun x ↦
    Erdos228.KernelReplacementMonotone.replacementAmplitude (x - theta)
  have hfmono : MonotoneOn f (Icc (0 : ℝ) (Real.pi / 2)) := by
    intro x hx y hy hxy
    exact Erdos228.KernelReplacementMonotone.monotoneOn_replacementAmplitude
      ⟨by linarith [hx.1, htheta.2], by linarith [hx.2, htheta.1]⟩
      ⟨by linarith [hy.1, htheta.2], by linarith [hy.2, htheta.1]⟩
      (sub_le_sub_right hxy theta)
  have htel := endpoint_variation_le_of_monotone F.base f 0 (Real.pi / 2)
    F.nondegenerate (by positivity) F.in_first_quadrant
    (endpointSeparated hn0 F) hfmono
  have hglobal : f (Real.pi / 2) - f 0 ≤
      Erdos228.KernelReplacementMonotone.replacementAmplitude (Real.pi / 2) -
        Erdos228.KernelReplacementMonotone.replacementAmplitude (-(Real.pi / 2)) := by
    apply sub_le_sub
    · exact Erdos228.KernelReplacementMonotone.monotoneOn_replacementAmplitude
        ⟨by linarith [htheta.2, Real.pi_pos], by linarith [htheta.1]⟩
        ⟨by linarith [Real.pi_pos], le_rfl⟩ (by linarith [htheta.1])
    · exact Erdos228.KernelReplacementMonotone.monotoneOn_replacementAmplitude
        ⟨le_rfl, by linarith [Real.pi_pos]⟩
        ⟨by linarith [htheta.2], by linarith [htheta.1, Real.pi_pos]⟩
        (by linarith [htheta.2])
  calc
    ∑ I ∈ F.base, |replacementIntegral n I theta| ≤
        ∑ I ∈ F.base, (f I.2 - f I.1) / n := by
          apply Finset.sum_le_sum
          intro I hI
          exact abs_replacementIntegral_le hn0 F htheta hI
    _ = (∑ I ∈ F.base, (f I.2 - f I.1)) / n := by
          rw [Finset.sum_div]
    _ ≤ (f (Real.pi / 2) - f 0) / n := by
          exact div_le_div_of_nonneg_right htel (Nat.cast_nonneg n)
    _ ≤ (Erdos228.KernelReplacementMonotone.replacementAmplitude (Real.pi / 2) -
        Erdos228.KernelReplacementMonotone.replacementAmplitude (-(Real.pi / 2))) / n := by
          exact div_le_div_of_nonneg_right hglobal (Nat.cast_nonneg n)
    _ = (2 - 4 / Real.pi) / n := by
          rw [Erdos228.KernelReplacementMonotone.replacementAmplitude_endpoint_variation]

/-- Subtype-indexed form of the aggregate Claim 2 estimate. -/
theorem sum_abs_replacementIntegral_subtype_le {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I : (↑F.base : Type), |replacementIntegral n I.1 theta| ≤
      (2 - 4 / Real.pi) / n := by
  rw [Finset.univ_eq_attach]
  calc
    ∑ I ∈ F.base.attach, |replacementIntegral n I.1 theta| =
        ∑ I ∈ F.base, |replacementIntegral n I theta| :=
      Finset.sum_attach F.base (fun I ↦ |replacementIntegral n I theta|)
    _ ≤ (2 - 4 / Real.pi) / n :=
      sum_abs_replacementIntegral_le hn F htheta

/-! ## Exact per-interval decomposition -/

/-- The quotient form of the odd kernel integrated over one interval. -/
def quotientIntegral (n : ℕ) (I : RealInterval) (theta : ℝ) : ℝ :=
  ∫ x in I.1..I.2,
    (Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
      Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta))

private lemma quotientFirst_eq_principal_add_replacement {n : ℕ} (hn : 0 < n)
    {u : ℝ} (huHalf : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hu : u ≠ 0) :
    Real.sin ((2 * n : ℕ) * u) / Real.sin u =
      2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * u) +
        Erdos228.KernelReplacementMonotone.replacementAmplitude u *
          Real.sin (2 * (n : ℝ) * u) := by
  have hsin := Erdos228.KernelReplacementMonotone.sin_ne_zero_of_mem_half
    huHalf hu
  have hscale : (2 * (n : ℝ)) ≠ 0 := by positivity
  have harg : 2 * (n : ℝ) * u ≠ 0 := mul_ne_zero hscale hu
  rw [Real.sinc_of_ne_zero harg,
    Erdos228.KernelReplacementMonotone.replacementAmplitude_eq hu hsin]
  norm_cast
  field_simp [hu, hsin, hscale]
  ring

/-- Exact decomposition of one integrated quotient kernel into its
principal, denominator-replacement, and reflected pieces. -/
theorem quotientIntegral_eq_principal_add_replacement_sub_reflected
    {n : ℕ} (hn : 0 < n) (F : SuitableIntervalFamily n)
    {I : RealInterval} (hI : I ∈ F.base) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    quotientIntegral n I theta =
      Erdos228.KernelDistantClaim.principalIntegral n I theta +
        replacementIntegral n I theta -
          Erdos228.KernelReflectedClaim.reflectedIntegral n I theta := by
  let p : ℝ → ℝ := fun x ↦
    2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))
  let r : ℝ → ℝ := fun x ↦
    Erdos228.KernelReplacementMonotone.replacementAmplitude (x - theta) *
      Real.sin (2 * (n : ℝ) * (x - theta))
  let q : ℝ → ℝ := fun x ↦
    Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta)
  let s : ℝ → ℝ := fun x ↦
    Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta)
  have hord := F.ordered I hI
  have hpint : IntervalIntegrable p volume I.1 I.2 := by
    apply Continuous.intervalIntegrable
    dsimp [p]
    fun_prop
  have hrcont : ContinuousOn r (uIcc I.1 I.2) := by
    intro x hx
    have hxI : x ∈ Icc I.1 I.2 := by
      simpa [uIcc_of_le hord] using hx
    have hxHalf : x - theta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      shifted_mem_half F htheta hI
        ⟨sub_le_sub_right hxI.1 theta, sub_le_sub_right hxI.2 theta⟩
    have hamp : ContinuousAt
        (fun y : ℝ ↦
          Erdos228.KernelReplacementMonotone.replacementAmplitude (y - theta)) x := by
      have hsub : ContinuousAt (fun y : ℝ ↦ y - theta) x :=
        continuousAt_id.sub continuousAt_const
      simpa only [Function.comp_def] using
        (Erdos228.KernelReplacementMonotone.analyticAt_replacementAmplitude
          hxHalf).continuousAt.comp_of_eq hsub rfl
    exact (hamp.mul (by fun_prop)).continuousWithinAt
  have hrint : IntervalIntegrable r volume I.1 I.2 := hrcont.intervalIntegrable
  have hscont : ContinuousOn s (uIcc I.1 I.2) := by
    intro x hx
    have hxI : x ∈ Icc I.1 I.2 := by
      simpa [uIcc_of_le hord] using hx
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hmesh : 0 < 100 * Real.pi / (n : ℝ) := by positivity
    have haxes := F.away_from_axes I hI
    have hsumPos : 0 < x + theta := by
      linarith [hxI.1, haxes.1, htheta.1]
    have hsumLt : x + theta < Real.pi := by
      linarith [hxI.2, haxes.2, htheta.2]
    have hsin : Real.sin (x + theta) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hsumPos hsumLt)
    have hnum : ContinuousAt
        (fun y : ℝ ↦ Real.sin ((2 * n : ℕ) * (y + theta))) x := by
      fun_prop
    have hden : ContinuousAt (fun y : ℝ ↦ Real.sin (y + theta)) x := by
      fun_prop
    exact (hnum.div hden hsin).continuousWithinAt
  have hsint : IntervalIntegrable s volume I.1 I.2 := hscont.intervalIntegrable
  have hqr : ∀ᵐ x ∂volume, x ∈ uIoc I.1 I.2 → q x = p x + r x := by
    filter_upwards [Measure.ae_ne volume theta] with x hxt hx
    have hxIoc : x ∈ Ioc I.1 I.2 := by
      simpa [uIoc_of_le hord] using hx
    have hxI : x ∈ Icc I.1 I.2 := ⟨hxIoc.1.le, hxIoc.2⟩
    have hu : x - theta ≠ 0 := sub_ne_zero.mpr hxt
    have huHalf : x - theta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      shifted_mem_half F htheta hI
        ⟨sub_le_sub_right hxI.1 theta, sub_le_sub_right hxI.2 theta⟩
    exact quotientFirst_eq_principal_add_replacement hn huHalf hu
  have hqrRestrict : p + r =ᵐ[volume.restrict (uIoc I.1 I.2)] q := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume theta)] with x hx hxt
    have hxIoc : x ∈ Ioc I.1 I.2 := by
      simpa [uIoc_of_le hord] using hx
    have hxI : x ∈ Icc I.1 I.2 := ⟨hxIoc.1.le, hxIoc.2⟩
    have hu : x - theta ≠ 0 := sub_ne_zero.mpr hxt
    have huHalf : x - theta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      shifted_mem_half F htheta hI
        ⟨sub_le_sub_right hxI.1 theta, sub_le_sub_right hxI.2 theta⟩
    exact (quotientFirst_eq_principal_add_replacement hn huHalf hu).symm
  have hqint : IntervalIntegrable q volume I.1 I.2 :=
    (hpint.add hrint).congr_ae hqrRestrict
  have hfirst : (∫ x in I.1..I.2, q x) =
      (∫ x in I.1..I.2, p x) + ∫ x in I.1..I.2, r x := by
    rw [intervalIntegral.integral_congr_ae hqr,
      intervalIntegral.integral_add hpint hrint]
  rw [quotientIntegral, show (fun x : ℝ ↦
      Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
        Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta)) =
      fun x ↦ q x - s x by rfl,
    intervalIntegral.integral_sub hqint hsint, hfirst]
  rfl

/-! ## Explicit numerical absorption -/

/-- At the concrete threshold used by the odd construction, the sum of the
three sharp error bounds is at most `2 / 3`. -/
theorem total_kernel_error_le_two_thirds {n : ℕ} (hn : 4096 ≤ n) :
    2 / Real.pi + 2 / (n * Real.sin (100 * Real.pi / n)) +
        12 * Real.pi / n + (2 - 4 / Real.pi) / n ≤ 2 / 3 := by
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  let x : ℝ := 100 * Real.pi / n
  have hxpos : 0 < x := by positivity
  have hxle : x ≤ 1 / 10 := by
    rw [show x = 100 * Real.pi / n by rfl, div_le_iff₀ hnpos]
    nlinarith [Real.pi_lt_four]
  have hxsq : x ^ 2 ≤ 1 / 100 := by nlinarith [sq_nonneg x]
  have hsin0 := Real.sin_ge_sub_cube hxpos.le
  have hsin : (99 / 100) * x ≤ Real.sin x := by
    nlinarith [mul_nonneg hxpos.le (sub_nonneg.mpr hxsq)]
  have hden : 300 ≤ (n : ℝ) * Real.sin x := by
    calc
      (300 : ℝ) ≤ 99 * Real.pi := by
        nlinarith [Real.pi_gt_d2]
      _ = (n : ℝ) * ((99 / 100) * x) := by
        dsimp [x]
        field_simp [hn0]
      _ ≤ (n : ℝ) * Real.sin x := mul_le_mul_of_nonneg_left hsin hnpos.le
  have hdenpos : 0 < (n : ℝ) * Real.sin x := lt_of_lt_of_le (by norm_num) hden
  have hreflectedPole : 2 / ((n : ℝ) * Real.sin x) ≤ 1 / 150 := by
    apply (div_le_iff₀ hdenpos).2
    nlinarith
  have hprincipal : 2 / Real.pi ≤ 100 / 157 := by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_gt_d2]
  have hcrossing : 12 * Real.pi / (n : ℝ) ≤ 189 / 20480 := by
    apply (div_le_iff₀ hnpos).2
    nlinarith [Real.pi_lt_d2]
  have hreplacement : (2 - 4 / Real.pi) / (n : ℝ) ≤ 1 / 2048 := by
    apply (div_le_iff₀ hnpos).2
    have : 0 ≤ 4 / Real.pi := div_nonneg (by norm_num) Real.pi_pos.le
    nlinarith
  change 2 / Real.pi + 2 / ((n : ℝ) * Real.sin x) +
      12 * Real.pi / n + (2 - 4 / Real.pi) / n ≤ 2 / 3
  calc
    2 / Real.pi + 2 / ((n : ℝ) * Real.sin x) +
          12 * Real.pi / n + (2 - 4 / Real.pi) / n ≤
        100 / 157 + 1 / 150 + 189 / 20480 + 1 / 2048 := by linarith
    _ ≤ 2 / 3 := by norm_num

/-! ## The combined signed residual -/

/-- Claims 1--3 combined in the exact form used by the normalized odd-kernel
assembly: after retaining the principal kernel only on the strict near set,
the entire signed residual has absolute value at most `2 / 3`. -/
theorem signed_kernel_residual_le_two_thirds {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n) (alpha : (↑F.base : Type) → ℝ)
    (halpha : Erdos228.Discrepancy.IsSign alpha) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    |(∑ I : (↑F.base : Type), alpha I * quotientIntegral n I.1 theta) -
        (∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
          alpha I * Erdos228.KernelDistantClaim.principalIntegral n I.1 theta)| ≤
      2 / 3 := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  let principal : (↑F.base : Type) → ℝ := fun I ↦
    Erdos228.KernelDistantClaim.principalIntegral n I.1 theta
  let replacement : (↑F.base : Type) → ℝ := fun I ↦
    replacementIntegral n I.1 theta
  let reflected : (↑F.base : Type) → ℝ := fun I ↦
    Erdos228.KernelReflectedClaim.reflectedIntegral n I.1 theta
  have halphaAbs (I : (↑F.base : Type)) : |alpha I| = 1 := by
    rcases halpha I with hI | hI <;> simp [hI]
  have hquotient :
      (∑ I : (↑F.base : Type), alpha I * quotientIntegral n I.1 theta) =
        (∑ I : (↑F.base : Type), alpha I * principal I) +
          (∑ I : (↑F.base : Type), alpha I * replacement I) -
            ∑ I : (↑F.base : Type), alpha I * reflected I := by
    simp_rw [quotientIntegral_eq_principal_add_replacement_sub_reflected
      hn0 F (hI := Subtype.property _) htheta]
    simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rfl
  have hpartition :
      (∑ I : (↑F.base : Type), alpha I * principal I) =
        (∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
          alpha I * principal I) +
        ∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
          alpha I * principal I := by
    rw [Erdos228.KernelDistantClaim.distantBaseIntervals_eq_sdiff]
    calc
      (∑ I : (↑F.base : Type), alpha I * principal I) =
          (∑ I ∈ Finset.univ \
              Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
            alpha I * principal I) +
          ∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
            alpha I * principal I :=
        (Finset.sum_sdiff
          (Finset.subset_univ
            (Erdos228.KernelNearGeometry.nearBaseIntervals F theta))).symm
      _ = (∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
            alpha I * principal I) +
          ∑ I ∈ Finset.univ \
              Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
            alpha I * principal I := add_comm _ _
  have hresidual :
      (∑ I : (↑F.base : Type), alpha I * quotientIntegral n I.1 theta) -
          (∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
            alpha I * Erdos228.KernelDistantClaim.principalIntegral n I.1 theta) =
        (∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
          alpha I * principal I) +
        (∑ I : (↑F.base : Type), alpha I * replacement I) -
          ∑ I : (↑F.base : Type), alpha I * reflected I := by
    rw [hquotient, hpartition]
    dsimp only [principal]
    ring
  have hprincipal :
      |∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
          alpha I * principal I| ≤ 2 / Real.pi := by
    calc
      |∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
          alpha I * principal I| ≤
          ∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
            |alpha I * principal I| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
            |principal I| := by
          apply Finset.sum_congr rfl
          intro I hI
          rw [abs_mul, halphaAbs, one_mul]
      _ ≤ 2 / Real.pi :=
        Erdos228.KernelDistantClaim.sum_abs_principalIntegral_distant_le_two_div_pi
          hn0 F htheta
  have hreplacement :
      |∑ I : (↑F.base : Type), alpha I * replacement I| ≤
        (2 - 4 / Real.pi) / n := by
    calc
      |∑ I : (↑F.base : Type), alpha I * replacement I| ≤
          ∑ I : (↑F.base : Type), |alpha I * replacement I| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ I : (↑F.base : Type), |replacement I| := by
          apply Finset.sum_congr rfl
          intro I hI
          rw [abs_mul, halphaAbs, one_mul]
      _ ≤ (2 - 4 / Real.pi) / n :=
        sum_abs_replacementIntegral_subtype_le hn F htheta
  have hreflected :
      |∑ I : (↑F.base : Type), alpha I * reflected I| ≤
        2 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
          12 * Real.pi / n := by
    calc
      |∑ I : (↑F.base : Type), alpha I * reflected I| ≤
          ∑ I : (↑F.base : Type), |alpha I * reflected I| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ I : (↑F.base : Type), |reflected I| := by
          apply Finset.sum_congr rfl
          intro I hI
          rw [abs_mul, halphaAbs, one_mul]
      _ ≤ 2 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
          12 * Real.pi / n :=
        Erdos228.KernelReflectedClaim.sum_abs_reflectedIntegral_le hn F htheta
  rw [hresidual]
  calc
    |(∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
          alpha I * principal I) +
        (∑ I : (↑F.base : Type), alpha I * replacement I) -
          ∑ I : (↑F.base : Type), alpha I * reflected I| ≤
        |∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
          alpha I * principal I| +
        |∑ I : (↑F.base : Type), alpha I * replacement I| +
        |∑ I : (↑F.base : Type), alpha I * reflected I| := by
          linarith [abs_add_le
            (∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
              alpha I * principal I)
            (∑ I : (↑F.base : Type), alpha I * replacement I),
            abs_sub
              ((∑ I ∈ Erdos228.KernelDistantClaim.distantBaseIntervals F theta,
                alpha I * principal I) +
                ∑ I : (↑F.base : Type), alpha I * replacement I)
              (∑ I : (↑F.base : Type), alpha I * reflected I)]
    _ ≤ 2 / Real.pi + (2 - 4 / Real.pi) / n +
        (2 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
          12 * Real.pi / n) := by linarith
    _ ≤ 2 / 3 := by
      linarith [total_kernel_error_le_two_thirds hn]

end

end ConcreteKernelClaims

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/OddKernelCertificate.lean` -/

section
/-!
# The concrete odd-kernel certificate

This module closes the analytic interface left by `OddSine.KernelCertificate`.
The first part is a small numerical adapter: once the normalized odd kernel
has its sharp `2 / 3` lower bound on the dangerous set and its `14 / 3`
global upper bound, it packages those inequalities into the exact
`main + error` format consumed by `OddSine`.

The remaining sections prove those normalized bounds from the exact odd
Dirichlet identity, the grid geometry of a suitable interval family, and the
three concrete kernel estimates.
-/

namespace OddKernelCertificate

open scoped BigOperators Interval
open Set

noncomputable section

open Erdos228.OddSine

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## A numerical adapter for the certificate structure -/

/-- The target sine sum after removing its positive `K * sqrt n` scale. -/
def normalizedTarget {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) : ℝ :=
  targetSine F alpha theta / (K * Real.sqrt n)

private def clippedMagnitude (dangerous : Prop) [Decidable dangerous]
    (a : ℝ) : ℝ :=
  min 4 (max (if dangerous then 4 / 3 else 0) a)

private lemma clippedMagnitude_nonneg (dangerous : Prop) [Decidable dangerous]
    {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ clippedMagnitude dangerous a := by
  unfold clippedMagnitude
  apply le_min (by norm_num)
  exact le_max_of_le_right ha

private lemma clippedMagnitude_le_four (dangerous : Prop) [Decidable dangerous]
    (a : ℝ) :
    clippedMagnitude dangerous a ≤ 4 := by
  exact min_le_left _ _

private lemma four_thirds_le_clippedMagnitude {dangerous : Prop}
    [Decidable dangerous] {a : ℝ} (hdangerous : dangerous) :
    4 / 3 ≤ clippedMagnitude dangerous a := by
  unfold clippedMagnitude
  rw [if_pos hdangerous]
  apply le_min (by norm_num)
  exact le_max_left _ _

private lemma abs_sub_clippedMagnitude_le {dangerous : Prop}
    [Decidable dangerous] {a : ℝ} (ha : 0 ≤ a)
    (haUpper : a ≤ 14 / 3)
    (haLower : dangerous → 2 / 3 ≤ a) :
    |a - clippedMagnitude dangerous a| ≤ 2 / 3 := by
  classical
  unfold clippedMagnitude
  by_cases hdangerous : dangerous
  · rw [if_pos hdangerous]
    have halower := haLower hdangerous
    by_cases ha4 : a ≤ 4
    · rw [min_eq_right]
      · by_cases ha43 : 4 / 3 ≤ a
        · rw [max_eq_right ha43]
          norm_num
        · rw [max_eq_left (le_of_not_ge ha43)]
          rw [abs_of_nonpos]
          · linarith
          · linarith
      · exact max_le (by norm_num) ha4
    · have h4a : 4 ≤ max (4 / 3) a := by
        exact le_max_of_le_right (le_of_not_ge ha4)
      rw [min_eq_left h4a, abs_of_nonneg (sub_nonneg.2 (le_of_not_ge ha4))]
      linarith
  · rw [if_neg hdangerous, max_eq_right ha]
    by_cases ha4 : a ≤ 4
    · rw [min_eq_right ha4]
      norm_num
    · rw [min_eq_left (le_of_not_ge ha4),
        abs_of_nonneg (sub_nonneg.2 (le_of_not_ge ha4))]
      linarith

private def clippedMain {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) : ℝ :=
  let m := clippedMagnitude (IsDangerous F theta)
    |normalizedTarget F alpha theta|
  if 0 ≤ normalizedTarget F alpha theta then m else -m

private def clippedError {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) : ℝ :=
  normalizedTarget F alpha theta - clippedMain F alpha theta

private lemma abs_clippedMain {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) :
    |clippedMain F alpha theta| =
      clippedMagnitude (IsDangerous F theta)
        |normalizedTarget F alpha theta| := by
  classical
  simp only [clippedMain]
  by_cases hv : 0 ≤ normalizedTarget F alpha theta
  · rw [if_pos hv,
      abs_of_nonneg (clippedMagnitude_nonneg _ (abs_nonneg _))]
  · rw [if_neg hv, abs_neg,
      abs_of_nonneg (clippedMagnitude_nonneg _ (abs_nonneg _))]

private lemma abs_clippedError {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) :
    |clippedError F alpha theta| =
      |(|normalizedTarget F alpha theta| -
        clippedMagnitude (IsDangerous F theta)
          |normalizedTarget F alpha theta|)| := by
  classical
  unfold clippedError clippedMain
  by_cases hv : 0 ≤ normalizedTarget F alpha theta
  · rw [if_pos hv, abs_of_nonneg hv]
  · rw [if_neg hv, abs_of_neg (lt_of_not_ge hv)]
    have heq : normalizedTarget F alpha theta +
        clippedMagnitude (IsDangerous F theta)
            (-normalizedTarget F alpha theta) =
          -(-normalizedTarget F alpha theta -
            clippedMagnitude (IsDangerous F theta)
              (-normalizedTarget F alpha theta)) := by ring
    rw [sub_neg_eq_add, heq, abs_neg]

/-- Package the two sharp normalized estimates into the precise
`OddSine.KernelCertificate` interface.  This lemma is only an internal
adapter: the public theorem below proves both estimates from the interval
geometry and has no analytic hypotheses. -/
noncomputable def kernelCertificate_of_normalized_bounds {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ)
    (hlower : ∀ theta, IsDangerous F theta →
      2 / 3 ≤ |normalizedTarget F alpha theta|)
    (hupper : ∀ theta, |normalizedTarget F alpha theta| ≤ 14 / 3) :
    KernelCertificate F alpha := by
  classical
  refine
    { main := clippedMain F alpha
      error := clippedError F alpha
      decomposition := ?_
      main_lower := ?_
      main_upper := ?_
      error_bound := ?_ }
  · intro theta
    have hscale : K * Real.sqrt n ≠ 0 := by
      apply mul_ne_zero
      · norm_num [K]
      · exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hn))
    rw [show clippedMain F alpha theta + clippedError F alpha theta =
        normalizedTarget F alpha theta by
      simp only [clippedError]
      ring]
    simp only [normalizedTarget]
    rw [mul_comm]
    exact (div_mul_cancel₀ _ hscale).symm
  · intro theta htheta
    rw [abs_clippedMain]
    exact four_thirds_le_clippedMagnitude htheta
  · intro theta
    rw [abs_clippedMain]
    exact clippedMagnitude_le_four _ _
  · intro theta
    rw [abs_clippedError]
    exact abs_sub_clippedMagnitude_le (abs_nonneg _)
      (hupper theta) (hlower theta)

/-! ## Reduction to the first quadrant -/

/-- It is enough to establish the normalized kernel estimates in the first
quadrant.  The upper bound uses the absolute-value reduction for every odd
sine sum.  For the lower bound, the four clauses in `IsDangerous` give the
corresponding odd/reflection/translation identity directly. -/
theorem normalized_bounds_of_firstQuadrant {n : ℕ}
    (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ)
    (hlower : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      IsDangerous F theta → 2 / 3 ≤ |normalizedTarget F alpha theta|)
    (hupper : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      |normalizedTarget F alpha theta| ≤ 14 / 3) :
    (∀ theta, IsDangerous F theta →
      2 / 3 ≤ |normalizedTarget F alpha theta|) ∧
    (∀ theta, |normalizedTarget F alpha theta| ≤ 14 / 3) := by
  constructor
  · intro theta htheta
    obtain ⟨I, hI, hmem | hmem | hmem | hmem⟩ := htheta
    · exact hlower theta
        ⟨(F.in_first_quadrant I hI).1.trans hmem.1,
          hmem.2.trans (F.in_first_quadrant I hI).2⟩
        ⟨I, hI, Or.inl hmem⟩
    · have hqmem : -theta ∈ Icc (0 : ℝ) (Real.pi / 2) :=
        ⟨(F.in_first_quadrant I hI).1.trans hmem.1,
          hmem.2.trans (F.in_first_quadrant I hI).2⟩
      have hqdanger : IsDangerous F (-theta) :=
        ⟨I, hI, Or.inl hmem⟩
      have hq := hlower (-theta) hqmem hqdanger
      simpa only [normalizedTarget, targetSine,
        oddSineSum_neg, abs_div, abs_neg] using hq
    · have hqmem : Real.pi - theta ∈ Icc (0 : ℝ) (Real.pi / 2) :=
        ⟨(F.in_first_quadrant I hI).1.trans hmem.1,
          hmem.2.trans (F.in_first_quadrant I hI).2⟩
      have hqdanger : IsDangerous F (Real.pi - theta) :=
        ⟨I, hI, Or.inl hmem⟩
      have hq := hlower (Real.pi - theta) hqmem hqdanger
      simpa only [normalizedTarget, targetSine,
        oddSineSum_pi_sub, abs_div] using hq
    · have hqmem : theta - Real.pi ∈ Icc (0 : ℝ) (Real.pi / 2) :=
        ⟨(F.in_first_quadrant I hI).1.trans hmem.1,
          hmem.2.trans (F.in_first_quadrant I hI).2⟩
      have hqdanger : IsDangerous F (theta - Real.pi) :=
        ⟨I, hI, Or.inl hmem⟩
      have hq := hlower (theta - Real.pi) hqmem hqdanger
      have heq : theta = (theta - Real.pi) + Real.pi := by ring
      rw [heq]
      simpa only [normalizedTarget, targetSine,
        oddSineSum_add_pi, abs_div, abs_neg] using hq
  · intro theta
    obtain ⟨theta', htheta', heq⟩ :=
      exists_firstQuadrant_abs_oddSineSum_eq n (fourierTarget F alpha) theta
    have hq := hupper theta' htheta'
    simp only [normalizedTarget, targetSine, abs_div] at hq ⊢
    rw [heq]
    exact hq

/-! ## Finite near/distant assembly -/

/-- A nondegenerate suitable interval has strictly ordered integer grid
indices.  This is the exact endpoint form consumed by the grid
sine-integral lemma. -/
theorem exists_gridIndices_lt {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) (I : (↑F.base : Type)) :
    ∃ a b : ℤ, a < b ∧
      I.1.1 = (a : ℝ) * Real.pi / n ∧
      I.1.2 = (b : ℝ) * Real.pi / n := by
  obtain ⟨a, b, ha, hb⟩ := F.grid_endpoints I.1 I.property
  refine ⟨a, b, ?_, ha, hb⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscalePos : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  have hscaled : (a : ℝ) * (Real.pi / (n : ℝ)) <
      (b : ℝ) * (Real.pi / (n : ℝ)) := by
    simpa only [mul_div_assoc, ha, hb] using
      F.nondegenerate I.1 I.property
  have habR : (a : ℝ) < b := by
    nlinarith [hscalePos]
  exact_mod_cast habR

/-- The principal integral on the interval containing the evaluation point
is the main lobe from BBMST Lemma 5.8(a). -/
theorem principalIntegral_self_mem {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (I : (↑F.base : Type)) (htheta : InInterval I.1 theta) :
    Erdos228.KernelDistantClaim.principalIntegral n I.1 theta ∈
      Icc ((4 : ℝ) / 3) 4 := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_gridIndices_lt hn F I
  have hshort : (b : ℝ) * Real.pi / n - (a : ℝ) * Real.pi / n ≤
      6 * Real.pi / n := by
    rw [← ha, ← hb]
    exact F.short I.1 I.property
  have htheta' : theta ∈ Icc ((a : ℝ) * Real.pi / n)
      ((b : ℝ) * Real.pi / n) := by
    change theta ∈ Icc I.1.1 I.1.2 at htheta
    simpa only [← ha, ← hb] using htheta
  have hmain := Erdos228.SineIntegralGrid.principal_grid_interval_inside
    n hn a b hab hshort htheta'
  simpa only [Erdos228.KernelDistantClaim.principalIntegral, ha, hb] using hmain

/-- Every near interval not containing the evaluation point is an exterior
interval in BBMST Lemma 5.8(b), hence contributes at most `2`. -/
theorem abs_principalIntegral_le_two_of_near_of_not_mem {n : ℕ}
    (hn : 0 < n) (F : SuitableIntervalFamily n) {theta : ℝ}
    (I : (↑F.base : Type))
    (hnear : I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta)
    (hout : ¬InInterval I.1 theta) :
    |Erdos228.KernelDistantClaim.principalIntegral n I.1 theta| ≤ 2 := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_gridIndices_lt hn F I
  have hshort : (b : ℝ) * Real.pi / n - (a : ℝ) * Real.pi / n ≤
      6 * Real.pi / n := by
    rw [← ha, ← hb]
    exact F.short I.1 I.property
  have hnearGap : Erdos228.KernelNearGeometry.Near n theta I.1 := by
    simpa only [Erdos228.KernelNearGeometry.nearBaseIntervals,
      Finset.mem_filter, Finset.mem_univ, true_and] using hnear
  rw [InInterval, mem_Icc] at hout
  have hside :
      (theta ≤ (a : ℝ) * Real.pi / n ∧
        (a : ℝ) * Real.pi / n - theta ≤ Real.pi / n) ∨
      ((b : ℝ) * Real.pi / n ≤ theta ∧
        theta - (b : ℝ) * Real.pi / n ≤ Real.pi / n) := by
    rcases not_and_or.mp hout with hleft | hright
    · left
      have htheta : theta ≤ I.1.1 := (lt_of_not_ge hleft).le
      have hgap := hnearGap
      rw [Erdos228.KernelNearGeometry.Near,
        Erdos228.KernelNearGeometry.intervalGap_eq_left
          (F.ordered I.1 I.property) htheta] at hgap
      rw [← ha]
      exact ⟨htheta, hgap.le⟩
    · right
      have htheta : I.1.2 ≤ theta := (lt_of_not_ge hright).le
      have hgap := hnearGap
      rw [Erdos228.KernelNearGeometry.Near,
        Erdos228.KernelNearGeometry.intervalGap_eq_right
          (F.ordered I.1 I.property) htheta] at hgap
      rw [← hb]
      exact ⟨htheta, hgap.le⟩
  have hoff := Erdos228.SineIntegralGrid.principal_grid_interval_outside_near
    n hn a b hab hshort hside
  simpa only [Erdos228.KernelDistantClaim.principalIntegral, ha, hb] using hoff

/-- Abstract assembly of the kernel bookkeeping after Claims 1--3 have been
summed.  The hypotheses are the concrete conclusions proved below:

* `principal` is the `sin(2n u) / u` integral on one grid interval;
* its near part contains one self interval (bounded between `4/3` and `4`)
  or at most two outside intervals (each bounded by `2`);
* `error` is the reflected kernel, denominator-replacement error, and all
  distant principal intervals, whose aggregate is at most `2/3`.

Keeping this finite step separate makes the use of separation and the sign
colouring completely explicit. -/
theorem firstQuadrant_normalized_bounds_of_decomposition {n : ℕ}
    (hn : 0 < n) (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ)
    (halpha : Erdos228.Discrepancy.IsSign alpha)
    (principal : (↑F.base : Type) → ℝ → ℝ) (error : ℝ → ℝ)
    (hdecomposition : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      normalizedTarget F alpha theta =
        (∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
          alpha I * principal I theta) + error theta)
    (herror : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      |error theta| ≤ 2 / 3)
    (hself_lower : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      ∀ I : (↑F.base : Type), InInterval I.1 theta →
        4 / 3 ≤ |principal I theta|)
    (hself_upper : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      ∀ I : (↑F.base : Type), InInterval I.1 theta →
        |principal I theta| ≤ 4)
    (hoff_upper : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      ∀ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
        ¬InInterval I.1 theta → |principal I theta| ≤ 2) :
    (∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2), IsDangerous F theta →
      2 / 3 ≤ |normalizedTarget F alpha theta|) ∧
    (∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      |normalizedTarget F alpha theta| ≤ 14 / 3) := by
  classical
  have halpha_abs (I : (↑F.base : Type)) : |alpha I| = 1 := by
    rcases halpha I with hI | hI <;> simp [hI]
  constructor
  · intro theta htheta hdangerous
    obtain ⟨I, hthetaI, _hunique⟩ :=
      Erdos228.KernelNearGeometry.existsUnique_baseSubtype_of_dangerous_firstQuadrant
        hn F htheta hdangerous
    have hnear := Erdos228.KernelNearGeometry.sum_nearBaseIntervals_eq_of_mem hn F
      I.property hthetaI (fun J ↦ alpha J * principal J theta)
    have hmainLower : 4 / 3 ≤ |alpha I * principal I theta| := by
      rw [abs_mul, halpha_abs, one_mul]
      exact hself_lower theta htheta I hthetaI
    have hreverse : |alpha I * principal I theta| ≤
        |normalizedTarget F alpha theta| + |error theta| := by
      rw [hdecomposition theta htheta, hnear]
      calc
        |alpha I * principal I theta| =
            |(alpha I * principal I theta + error theta) - error theta| := by
              ring_nf
        _ ≤ _ := abs_sub _ _
    linarith [herror theta htheta]
  · intro theta htheta
    have hmainUpper :
        |∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
          alpha I * principal I theta| ≤ 4 := by
      by_cases hin : Erdos228.KernelNearGeometry.InBaseUnion F theta
      · obtain ⟨I, hI, hthetaI⟩ := hin
        rw [Erdos228.KernelNearGeometry.sum_nearBaseIntervals_eq_of_mem hn F hI hthetaI]
        rw [abs_mul, halpha_abs, one_mul]
        exact hself_upper theta htheta ⟨I, hI⟩ hthetaI
      · have htwo :=
          Erdos228.KernelNearGeometry.abs_sum_nearBaseIntervals_le_two_mul_of_not_inBaseUnion
            hn F hin (show (0 : ℝ) ≤ 2 by norm_num)
            (fun I ↦ alpha I * principal I theta) (by
              intro I hI
              rw [abs_mul, halpha_abs, one_mul]
              exact hoff_upper theta htheta I hI
                (fun hmem ↦ hin ⟨I.1, I.property, hmem⟩))
        norm_num at htwo ⊢
        exact htwo
    rw [hdecomposition theta htheta]
    calc
      |(∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
            alpha I * principal I theta) + error theta| ≤
          |∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
            alpha I * principal I theta| + |error theta| := abs_add_le _ _
      _ ≤ 4 + 2 / 3 := add_le_add hmainUpper (herror theta htheta)
      _ = 14 / 3 := by norm_num

/-! ## Concrete Claims 1--3 and the certificate -/

/-- The aggregate of the three terms discarded when only the strict-near
principal kernels are retained. -/
def concreteError {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) : ℝ :=
  normalizedTarget F alpha theta -
    ∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
      alpha I * Erdos228.KernelDistantClaim.principalIntegral n I.1 theta

theorem concrete_decomposition {n : ℕ} (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) :
    normalizedTarget F alpha theta =
      (∑ I ∈ Erdos228.KernelNearGeometry.nearBaseIntervals F theta,
        alpha I * Erdos228.KernelDistantClaim.principalIntegral n I.1 theta) +
        concreteError F alpha theta := by
  simp only [concreteError]
  ring

/-- The signed aggregate of Claims 1--3 is at most `2 / 3`.  The equality
before the estimate is the exact odd Dirichlet-kernel identity, not an
asymptotic approximation. -/
theorem abs_concreteError_le_two_thirds {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ)
    (halpha : Erdos228.Discrepancy.IsSign alpha) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    |concreteError F alpha theta| ≤ 2 / 3 := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have htarget :=
    Erdos228.OddKernelIdentity.targetSine_div_eq_sum_quotientIntegral_of_theta_mem_Icc
      hnpos F alpha htheta
  rw [concreteError]
  change normalizedTarget F alpha theta =
      ∑ I : (↑F.base : Type), alpha I *
        Erdos228.ConcreteKernelClaims.quotientIntegral n I.1 theta at htarget
  rw [htarget]
  exact Erdos228.ConcreteKernelClaims.signed_kernel_residual_le_two_thirds
    hn F alpha halpha htheta

/-- The two normalized bounds in the first quadrant, with the exact
principal kernel as the near contribution. -/
theorem concrete_firstQuadrant_normalized_bounds {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ)
    (halpha : Erdos228.Discrepancy.IsSign alpha) :
    (∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2), IsDangerous F theta →
      2 / 3 ≤ |normalizedTarget F alpha theta|) ∧
    (∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      |normalizedTarget F alpha theta| ≤ 14 / 3) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  apply firstQuadrant_normalized_bounds_of_decomposition hnpos F alpha halpha
    (fun I theta ↦ Erdos228.KernelDistantClaim.principalIntegral n I.1 theta)
    (concreteError F alpha)
  · exact fun theta _ ↦ concrete_decomposition F alpha theta
  · exact fun _ htheta ↦ abs_concreteError_le_two_thirds hn F alpha halpha htheta
  · intro theta _ I htheta
    have hmain := principalIntegral_self_mem hnpos F I htheta
    rw [abs_of_nonneg (by linarith [hmain.1])]
    exact hmain.1
  · intro theta _ I htheta
    have hmain := principalIntegral_self_mem hnpos F I htheta
    rw [abs_of_nonneg (by linarith [hmain.1])]
    exact hmain.2
  · intro theta _ I hnear hout
    exact abs_principalIntegral_le_two_of_near_of_not_mem hnpos F I hnear hout

/-- The unconditional concrete odd-kernel certificate used by the final
Erdős 228 assembly. -/
noncomputable def kernelCertificate {n : ℕ} (hn : 4096 ≤ n)
    (F : SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ)
    (halpha : Erdos228.Discrepancy.IsSign alpha) :
    KernelCertificate F alpha := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hfirst := concrete_firstQuadrant_normalized_bounds hn F alpha halpha
  have hglobal := normalized_bounds_of_firstQuadrant F alpha hfirst.1 hfirst.2
  exact kernelCertificate_of_normalized_bounds hnpos F alpha hglobal.1 hglobal.2

end

end OddKernelCertificate

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/OddRoundingSetup.lean` -/

section
/-!
# The explicit second-colouring mesh for the odd sine construction

This file supplies the finite mesh and the numerical parameters used in the
second BBMST colouring.  The mesh consists of the midpoints of the `16 * n`
equal subintervals of the first quadrant.
-/

namespace OddSine

open scoped BigOperators Interval
open Set

noncomputable section

/-- The number of equal pieces into which the first quadrant is divided. -/
def roundingMeshSize (n : ℕ) : ℕ := 16 * n

/-- The midpoint of the `g`-th piece of the first-quadrant mesh. -/
def roundingMeshPoint (n : ℕ) (g : Fin (roundingMeshSize n)) : ℝ :=
  (2 * (g : ℕ) + 1 : ℕ) * Real.pi / (64 * n)

/-- The BBMST parameter attached to derivative order `l`. -/
def roundingParameter (l : ℕ) : ℝ :=
  14 * Real.sqrt ((9 + l : ℕ) * Real.log 2)

@[simp] theorem roundingMeshSize_eq (n : ℕ) : roundingMeshSize n = 16 * n := rfl

theorem roundingParameter_nonneg (l : ℕ) : 0 ≤ roundingParameter l := by
  exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

/-- Squaring the chosen parameter removes its square root exactly. -/
theorem roundingParameter_sq (l : ℕ) :
    (roundingParameter l) ^ 2 = 196 * ((9 + l : ℕ) * Real.log 2) := by
  rw [roundingParameter, mul_pow, Real.sq_sqrt]
  · norm_num
  · exact mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))

/-- Each exponential weight is the corresponding dyadic geometric term. -/
theorem exp_roundingParameter (l : ℕ) :
    Real.exp (-(roundingParameter l) ^ 2 / 196) =
      (1 / 2 : ℝ) ^ (9 + l) := by
  rw [roundingParameter_sq]
  have hcancel :
      -(196 * (((9 + l : ℕ) : ℝ) * Real.log 2)) / 196 =
        -(((9 + l : ℕ) : ℝ) * Real.log 2) := by ring
  rw [hcancel]
  calc
    Real.exp (-(((9 + l : ℕ) : ℝ) * Real.log 2)) =
        Real.exp (((9 + l : ℕ) : ℝ) * (-Real.log 2)) := by ring_nf
    _ = Real.exp (-Real.log 2) ^ (9 + l) := Real.exp_nat_mul _ _
    _ = (1 / 2 : ℝ) ^ (9 + l) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num

/-- The finite geometric sum needed by the exponential budget. -/
theorem sum_exp_roundingParameter_le (n : ℕ) :
    (∑ l : Fin n, Real.exp (-(roundingParameter l) ^ 2 / 196)) ≤
      (1 / 256 : ℝ) := by
  simp_rw [exp_roundingParameter]
  calc
    (∑ l : Fin n, (1 / 2 : ℝ) ^ (9 + (l : ℕ))) =
        (1 / 512 : ℝ) * ∑ l : Fin n, (1 / 2 : ℝ) ^ (l : ℕ) := by
          simp_rw [pow_add]
          norm_num
          rw [Finset.mul_sum]
    _ ≤ (1 / 512 : ℝ) * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Fin.sum_univ_eq_sum_range]
      exact sum_geometric_two_le n
    _ = 1 / 256 := by norm_num

/-- The numerical parameter bound used after the full-colouring theorem. -/
theorem roundingParameter_add_thirty_le (l : ℕ) :
    roundingParameter l + 30 ≤ 65 + 2 * l := by
  have htwo_exp : (2 : ℝ) < Real.exp (25 / 36) := by
    refine lt_of_lt_of_le ?_
      (Real.sum_le_exp_of_nonneg (x := (25 / 36 : ℝ)) (by norm_num) 5)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hlog : Real.log 2 < 25 / 36 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
    exact htwo_exp
  have hradicand :
      ((9 + l : ℕ) : ℝ) * Real.log 2 ≤
        ((35 + 2 * (l : ℝ)) / 14) ^ 2 := by
    push_cast
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt hlog)
      (show (0 : ℝ) ≤ ((9 + l : ℕ) : ℝ) by positivity)
    push_cast at hmul
    nlinarith [sq_nonneg (l : ℝ)]
  have hsqrt := Real.sqrt_le_sqrt hradicand
  have hright : 0 ≤ (35 + 2 * (l : ℝ)) / 14 := by positivity
  rw [Real.sqrt_sq hright] at hsqrt
  unfold roundingParameter
  nlinarith

/-- Every point in the first quadrant is within half a mesh spacing of a
mesh midpoint. -/
theorem exists_roundingMeshPoint {n : ℕ} (hn : 0 < n) (theta : ℝ)
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∃ g : Fin (roundingMeshSize n),
      |theta - roundingMeshPoint n g| ≤ Real.pi / (64 * n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmesh : 0 < roundingMeshSize n := by
    simp [roundingMeshSize, hn]
  by_cases hend : theta = Real.pi / 2
  · let g : Fin (roundingMeshSize n) :=
      ⟨roundingMeshSize n - 1, Nat.sub_lt hmesh (by omega)⟩
    refine ⟨g, ?_⟩
    have hsub : (roundingMeshSize n - 1 : ℕ) + 1 = roundingMeshSize n := by
      omega
    have hdifference :
        theta - roundingMeshPoint n g = Real.pi / (64 * n) := by
      rw [hend]
      simp only [roundingMeshPoint, g]
      rw [show 2 * (roundingMeshSize n - 1) + 1 =
          2 * roundingMeshSize n - 1 by omega]
      simp only [roundingMeshSize]
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * (16 * n))]
      field_simp
      ring
    rw [hdifference, abs_of_nonneg (by positivity)]
  · have htheta_lt : theta < Real.pi / 2 :=
      lt_of_le_of_ne htheta.2 hend
    let y : ℝ := theta * (32 * n) / Real.pi
    have hy_nonneg : 0 ≤ y := by
      exact div_nonneg (mul_nonneg htheta.1 (by positivity)) hpi.le
    have hy_lt : y < (roundingMeshSize n : ℕ) := by
      rw [roundingMeshSize]
      apply (div_lt_iff₀ hpi).2
      have hmul := mul_lt_mul_of_pos_right htheta_lt
        (show (0 : ℝ) < 32 * n by positivity)
      push_cast at hmul ⊢
      nlinarith
    let k : ℕ := ⌊y⌋₊
    have hk_le : (k : ℝ) ≤ y := Nat.floor_le hy_nonneg
    have hy_succ : y < (k : ℝ) + 1 := by
      simpa [k] using Nat.lt_floor_add_one y
    have hk_mesh : k < roundingMeshSize n := by
      exact_mod_cast lt_of_le_of_lt hk_le hy_lt
    let g : Fin (roundingMeshSize n) := ⟨k, hk_mesh⟩
    refine ⟨g, ?_⟩
    have habs : |y - ((k : ℝ) + 1 / 2)| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith
    have hdifference :
        theta - roundingMeshPoint n g =
          (y - ((k : ℝ) + 1 / 2)) * (Real.pi / (32 * n)) := by
      simp only [roundingMeshPoint, g]
      dsimp only [y]
      push_cast
      field_simp
      ring
    rw [hdifference, abs_mul, abs_of_nonneg (by positivity :
      0 ≤ Real.pi / (32 * (n : ℝ)))]
    calc
      |y - ((k : ℝ) + 1 / 2)| * (Real.pi / (32 * n)) ≤
          (1 / 2) * (Real.pi / (32 * n)) :=
        mul_le_mul_of_nonneg_right habs (by positivity)
      _ = Real.pi / (64 * n) := by ring

/-- The explicit BBMST second-colouring setup. -/
def explicitRoundingSetup {n : ℕ} (hn : 0 < n) :
    RoundingSetup n (Fin (roundingMeshSize n)) where
  point := roundingMeshPoint n
  parameter := fun q ↦ roundingParameter q.2
  parameter_nonneg := fun q ↦ roundingParameter_nonneg q.2
  budget := by
    rw [Fintype.sum_prod_type]
    simp only
    calc
      (∑ _g : Fin (roundingMeshSize n),
          ∑ l : Fin n, Real.exp (-(roundingParameter l) ^ 2 / 196)) =
          (roundingMeshSize n : ℝ) *
            ∑ l : Fin n, Real.exp (-(roundingParameter l) ^ 2 / 196) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      _ ≤ (roundingMeshSize n : ℝ) * (1 / 256 : ℝ) := by
        apply mul_le_mul_of_nonneg_left (sum_exp_roundingParameter_le n)
        positivity
      _ = (n : ℝ) / 16 := by
        simp [roundingMeshSize]
        ring
  parameter_bound := fun _g l ↦ roundingParameter_add_thirty_le l
  cover := by
    intro a theta
    obtain ⟨theta', htheta', habs⟩ :=
      exists_firstQuadrant_abs_oddSineSum_eq n a theta
    obtain ⟨g, hnear⟩ := exists_roundingMeshPoint hn theta' htheta'
    exact ⟨g, theta', hnear, habs⟩

/-- There is an explicit second-colouring setup for every positive `n`, with
no additional geometric or numerical hypotheses. -/
theorem exists_roundingSetup {n : ℕ} (hn : 0 < n) :
    Nonempty (RoundingSetup n (Fin (16 * n))) := by
  exact ⟨explicitRoundingSetup hn⟩

end

end OddSine

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/CompactEndpoint.lean` -/

section
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/

/-!
# The compactness endpoint in the partial-colouring argument

The finite Gaussian walk used in the Lovett--Meka argument naturally first
produces, for every positive tolerance, a cube point at which at least half of
the coordinates are within that tolerance of a face.  This file records the
compactness argument which removes the tolerance.  The linear discrepancy
inequalities are closed, so they pass to the limiting cube point as well.
-/

open Filter Set
open scoped BigOperators Topology

noncomputable section

namespace Discrepancy

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Coordinates which are within `epsilon` of one of the two faces of the
cube.  On the cube this is the same as being within `epsilon` of `1` or
`-1`. -/
def approximateFixedCoordinates [DecidableEq I]
    (epsilon : ℝ) (x : I → ℝ) : Finset I :=
  Finset.univ.filter fun i ↦ 1 - epsilon ≤ |x i|

@[simp]
theorem mem_approximateFixedCoordinates [DecidableEq I]
    {epsilon : ℝ} {x : I → ℝ} {i : I} :
    i ∈ approximateFixedCoordinates epsilon x ↔ 1 - epsilon ≤ |x i| := by
  simp [approximateFixedCoordinates]

omit [Fintype I] in
/-- The coordinate cube is compact in the product topology. -/
theorem isCompact_inCube : IsCompact {x : I → ℝ | InCube x} := by
  have hset : {x : I → ℝ | InCube x} =
      Set.pi Set.univ (fun _ : I ↦ Set.Icc (-1 : ℝ) 1) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const, mem_Icc]
    constructor
    · intro hx i
      simpa only [abs_le] using hx i
    · intro hx i
      simpa only [abs_le] using hx i
  rw [hset]
  exact isCompact_univ_pi fun _ ↦ isCompact_Icc

omit [Fintype J] in
/-- If arbitrarily accurate approximate partial colourings satisfy fixed
closed discrepancy bounds, then an exact partial colouring satisfies the same
bounds.  The cardinal inequality is the integer form of saying that at least
`ceil(card I / 2)` coordinates have reached a face. -/
theorem hasPartialColoring_of_approximate [DecidableEq I]
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (happrox : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ x : I → ℝ,
        InCube x ∧
          Fintype.card I ≤
            2 * (approximateFixedCoordinates epsilon x).card ∧
          ∀ j, |dot (x - x₀) (v j)| ≤ c j * l2Norm (v j)) :
    HasPartialColoring v x₀ c := by
  let epsilon : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hepsilon_pos (n : ℕ) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  have hwitness : ∀ n : ℕ, ∃ x : I → ℝ,
      InCube x ∧
        Fintype.card I ≤
          2 * (approximateFixedCoordinates (epsilon n) x).card ∧
        ∀ j, |dot (x - x₀) (v j)| ≤ c j * l2Norm (v j) := by
    intro n
    exact happrox (epsilon n) (hepsilon_pos n)
  choose x hxCube hxCard hxDiscrepancy using hwitness
  obtain ⟨xLimit, hxLimitCube, phi, hphi, hxLimit⟩ :=
    isCompact_inCube.tendsto_subseq hxCube
  refine ⟨xLimit, hxLimitCube, ?_, ?_⟩
  · have hepsilon_tendsto :
        Tendsto epsilon atTop (nhds (0 : ℝ)) := by
      simpa only [epsilon, Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0))
    have hepsilon_subseq :
        Tendsto (fun n ↦ epsilon (phi n)) atTop (nhds (0 : ℝ)) :=
      hepsilon_tendsto.comp hphi.tendsto_atTop
    have hxCoordinate (i : I) :
        Tendsto (fun n ↦ x (phi n) i) atTop (nhds (xLimit i)) :=
      tendsto_pi_nhds.mp hxLimit i
    have hnotApprox (i : I) (hi : i ∉ fixedCoordinates xLimit) :
        ∀ᶠ n in atTop,
          i ∉ approximateFixedCoordinates (epsilon (phi n)) (x (phi n)) := by
      have habs_le : |xLimit i| ≤ 1 := hxLimitCube i
      have habs_ne : |xLimit i| ≠ 1 := by
        simpa [fixedCoordinates] using hi
      have hgap : 0 < 1 - |xLimit i| := sub_pos.mpr (lt_of_le_of_ne habs_le habs_ne)
      have htendsto :
          Tendsto
            (fun n ↦ 1 - epsilon (phi n) - |x (phi n) i|)
            atTop (nhds (1 - |xLimit i|)) := by
        simpa using
          (tendsto_const_nhds.sub hepsilon_subseq).sub
            ((hxCoordinate i).abs)
      have hpositive :
          ∀ᶠ n in atTop, 0 < 1 - epsilon (phi n) - |x (phi n) i| :=
        htendsto.eventually (isOpen_Ioi.mem_nhds hgap)
      filter_upwards [hpositive] with n hn
      simp only [mem_approximateFixedCoordinates, not_le]
      linarith
    have hsubset_eventually :
        ∀ᶠ n in atTop,
          approximateFixedCoordinates (epsilon (phi n)) (x (phi n)) ⊆
            fixedCoordinates xLimit := by
      have hall :
          ∀ᶠ n in atTop, ∀ i : I,
            i ∈ approximateFixedCoordinates (epsilon (phi n)) (x (phi n)) →
              i ∈ fixedCoordinates xLimit := by
        apply Filter.eventually_all.mpr
        intro i
        by_cases hfixed : i ∈ fixedCoordinates xLimit
        · exact Eventually.of_forall fun _ _ ↦ hfixed
        · exact (hnotApprox i hfixed).mono fun _ hnot hmem ↦
            False.elim (hnot hmem)
      exact hall.mono fun _ hn _ hi ↦ hn _ hi
    obtain ⟨n, hsubset⟩ := hsubset_eventually.exists
    have hcardSubset := Finset.card_le_card hsubset
    exact (hxCard (phi n)).trans (Nat.mul_le_mul_left 2 hcardSubset)
  · intro j
    have hxCoordinate (i : I) :
        Tendsto (fun n ↦ x (phi n) i) atTop (nhds (xLimit i)) :=
      tendsto_pi_nhds.mp hxLimit i
    have hdot :
        Tendsto (fun n ↦ dot (x (phi n) - x₀) (v j)) atTop
          (nhds (dot (xLimit - x₀) (v j))) := by
      unfold dot
      apply tendsto_finsetSum
      intro i hi
      exact ((hxCoordinate i).sub tendsto_const_nhds).mul_const (v j i)
    exact le_of_tendsto' hdot.abs fun n ↦ hxDiscrepancy (phi n) j

end Discrepancy

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/EdgeWalk.lean` -/

section
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/

/-!
# The Lovett--Meka partial-colouring principle

This file proves the finite-dimensional partial-colouring principle used by
the BBMST construction.  We use a projected Rademacher edge walk and a
deterministic exponential potential.  This is the discrete analogue of the
Gaussian edge walk: averaging over the next sign vector proves that at least
one next step simultaneously makes enough Euclidean progress and preserves
all exponential discrepancy potentials.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace EdgeWalk

open Erdos228.Discrepancy Erdos228.GaussianWalk Erdos228.ProjectionWalk

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Regard a finite real family as a vector in Euclidean space. -/
abbrev toWalk (v : I → ℝ) : WalkSpace I := WithLp.toLp 2 v

theorem norm_walkSpace_sq (v : WalkSpace I) :
    ‖v‖ ^ 2 = ∑ i, v i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

theorem l2Norm_eq_norm (v : I → ℝ) : l2Norm v = ‖toWalk v‖ := by
  rw [l2Norm, EuclideanSpace.norm_eq]
  simp only [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]

theorem dot_eq_inner (x v : I → ℝ) :
    dot x v = inner ℝ (toWalk v) (toWalk x) := by
  simp [dot, toWalk, EuclideanSpace.inner_eq_star_dotProduct,
    RCLike.star_def, dotProduct, mul_comm]

/-! ## Normalized constraints and active faces -/

/-- The unit normal associated to a nonzero discrepancy vector. -/
def normalizedConstraint (v : I → ℝ) : WalkSpace I :=
  (l2Norm v)⁻¹ • toWalk v

theorem norm_normalizedConstraint_le_one (v : I → ℝ) :
    ‖normalizedConstraint v‖ ≤ 1 := by
  by_cases hv : l2Norm v = 0
  · simp [normalizedConstraint, hv]
  · rw [normalizedConstraint, norm_smul, Real.norm_eq_abs,
      abs_inv, l2Norm_eq_norm]
    have hnorm : ‖toWalk v‖ ≠ 0 := by
      rw [← l2Norm_eq_norm]
      exact hv
    rw [abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hnorm]

/-- The normalized discrepancy of `x` from the starting point. -/
def normalizedDiscrepancy (v : I → ℝ) (x₀ : I → ℝ)
    (x : WalkSpace I) : ℝ :=
  inner ℝ (normalizedConstraint v) (x - toWalk x₀)

theorem normalizedDiscrepancy_mul_l2Norm {v : I → ℝ}
    (hv : 0 < l2Norm v) (x₀ : I → ℝ) (x : WalkSpace I) :
    normalizedDiscrepancy v x₀ x * l2Norm v =
      dot (fun i ↦ x i - x₀ i) v := by
  calc
    normalizedDiscrepancy v x₀ x * l2Norm v =
        inner ℝ (toWalk v) (x - toWalk x₀) := by
      rw [normalizedDiscrepancy, normalizedConstraint, inner_smul_left]
      simp only [starRingEnd_apply, star_trivial]
      field_simp [hv.ne']
    _ = inner ℝ (toWalk v) (toWalk (fun i ↦ x i - x₀ i)) := by
      congr 1
    _ = dot (fun i ↦ x i - x₀ i) v :=
      (dot_eq_inner _ _).symm

/-- Coordinates within `delta` of a face of the cube. -/
def activeCoordinates [DecidableEq I] (delta : ℝ) (x : WalkSpace I) : Finset I :=
  Finset.univ.filter fun i ↦ 1 - delta ≤ |x i|

/-- Nonzero discrepancy rows within `delta` of their allowed boundary. -/
def activeDiscrepancies [DecidableEq J] (delta : ℝ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) : Finset J :=
  Finset.univ.filter fun j ↦
    0 < l2Norm (v j) ∧ c j - delta ≤ |normalizedDiscrepancy (v j) x₀ x|

@[simp] theorem mem_activeCoordinates [DecidableEq I]
    {delta : ℝ} {x : WalkSpace I} {i : I} :
    i ∈ activeCoordinates delta x ↔ 1 - delta ≤ |x i| := by
  simp [activeCoordinates]

@[simp] theorem mem_activeDiscrepancies [DecidableEq J]
    {delta : ℝ} {v : J → I → ℝ} {x₀ : I → ℝ} {c : J → ℝ}
    {x : WalkSpace I} {j : J} :
    j ∈ activeDiscrepancies delta v x₀ c x ↔
      0 < l2Norm (v j) ∧
        c j - delta ≤ |normalizedDiscrepancy (v j) x₀ x| := by
  simp [activeDiscrepancies]

/-! ## One projected Rademacher step -/

/-- A product sample regarded as a Euclidean vector. -/
def sampleVector (omega : I → ℝ) : WalkSpace I := toWalk omega

/-- Moving the orthogonal projection from the random vector to the test
vector turns the projected functional into an ordinary weighted sum. -/
def projectedCoefficients (K : Submodule ℝ (WalkSpace I))
    (v : WalkSpace I) : I → ℝ := fun i ↦ K.starProjection v i

theorem inner_starProjection_sample_eq_sum
    (K : Submodule ℝ (WalkSpace I)) (v : WalkSpace I) (omega : I → ℝ) :
    inner ℝ v (K.starProjection (sampleVector omega)) =
      ∑ i, projectedCoefficients K v i * omega i := by
  rw [real_inner_comm, K.inner_starProjection_left_eq_right, real_inner_comm]
  simp [PiLp.inner_apply, projectedCoefficients, sampleVector, toWalk, mul_comm]

theorem integrable_exp_inner_starProjection_sample
    (K : Submodule ℝ (WalkSpace I)) (v : WalkSpace I) (t : ℝ) :
    Integrable (fun omega : I → ℝ ↦
      exp (t * inner ℝ v (K.starProjection (sampleVector omega))))
      (rademacherProduct I) := by
  rw [show (fun omega : I → ℝ ↦
      exp (t * inner ℝ v (K.starProjection (sampleVector omega)))) =
      (fun omega ↦ exp (t * ∑ i, projectedCoefficients K v i * omega i)) by
    funext omega
    rw [inner_starProjection_sample_eq_sum]]
  exact (hasSubgaussianMGF_weightedRademacherSum I
    (projectedCoefficients K v)).integrable_exp_mul t

theorem sum_projectedCoefficients_sq
    (K : Submodule ℝ (WalkSpace I)) (v : WalkSpace I) :
    ∑ i, projectedCoefficients K v i ^ 2 = ‖K.starProjection v‖ ^ 2 := by
  simpa [projectedCoefficients, EuclideanSpace.norm_sq_eq]

theorem sum_projectedCoefficients_sq_le
    (K : Submodule ℝ (WalkSpace I)) (v : WalkSpace I) :
    ∑ i, projectedCoefficients K v i ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [sum_projectedCoefficients_sq]
  nlinarith [norm_nonneg (K.starProjection v), norm_nonneg v,
    K.norm_starProjection_apply_le v]

/-- The projected-Rademacher one-step MGF estimate. -/
theorem integral_exp_inner_starProjection_sample_le
    (K : Submodule ℝ (WalkSpace I)) (v : WalkSpace I) (t : ℝ) :
    ∫ omega : I → ℝ,
        exp (t * inner ℝ v (K.starProjection (sampleVector omega)))
      ∂(rademacherProduct I) ≤ exp (t ^ 2 * ‖v‖ ^ 2 / 2) := by
  rw [show (fun omega : I → ℝ ↦
      exp (t * inner ℝ v (K.starProjection (sampleVector omega)))) =
      (fun omega ↦ exp (t * ∑ i, projectedCoefficients K v i * omega i)) by
    funext omega
    rw [inner_starProjection_sample_eq_sum]]
  have hmgf := (hasSubgaussianMGF_weightedRademacherSum I
    (projectedCoefficients K v)).mgf_le t
  rw [mgf] at hmgf
  let q : I → ℝ≥0 := fun i ↦ ⟨projectedCoefficients K v i ^ 2,
    sq_nonneg (projectedCoefficients K v i)⟩
  let variance : ℝ≥0 := ∑ i, q i
  change (∫ omega : I → ℝ,
      exp (t * ∑ i, projectedCoefficients K v i * omega i)
    ∂(rademacherProduct I)) ≤ exp ((variance : ℝ) * t ^ 2 / 2) at hmgf
  have hcoe : (variance : ℝ) = ∑ i, projectedCoefficients K v i ^ 2 := by
    calc
      (variance : ℝ) = ↑(∑ i, q i) := rfl
      _ = ∑ i, (q i : ℝ) := by
        simpa using NNReal.coe_sum Finset.univ q
      _ = ∑ i, projectedCoefficients K v i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rfl
  calc
    ∫ omega : I → ℝ,
        exp (t * ∑ i, projectedCoefficients K v i * omega i)
      ∂(rademacherProduct I) ≤
        exp ((variance : ℝ) * t ^ 2 / 2) := hmgf
    _ ≤ exp (t ^ 2 * ‖v‖ ^ 2 / 2) := by
      apply exp_le_exp.mpr
      rw [hcoe]
      nlinarith [sum_projectedCoefficients_sq_le K v, sq_nonneg t]

theorem memLp_id_rademacherMeasure : MemLp id 2 rademacherMeasure := by
  exact memLp_of_bounded ae_mem_Icc_rademacherMeasure
    measurable_id.aestronglyMeasurable 2

theorem memLp_weighted_rademacher_coord (a : I → ℝ) (i : I) :
    MemLp (fun omega : I → ℝ ↦ a i * omega i) 2 (rademacherProduct I) := by
  exact (memLp_id_rademacherMeasure.comp_measurePreserving
    (measurePreserving_eval (μ := fun _ : I ↦ rademacherMeasure) i)).const_mul (a i)

theorem integral_weighted_rademacher_sum (a : I → ℝ) :
    ∫ omega, (∑ i, a i * omega i) ∂rademacherProduct I = 0 := by
  rw [integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro i hi
    rw [integral_const_mul]
    have hmap : (rademacherProduct I).map (fun omega : I → ℝ ↦ omega i) =
        rademacherMeasure := by
      unfold rademacherProduct
      exact (measurePreserving_eval (μ := fun _ : I ↦ rademacherMeasure) i).map_eq
    rw [← integral_map (μ := rademacherProduct I) (f := fun x : ℝ ↦ x)
      (measurable_pi_apply i).aemeasurable measurable_id.aestronglyMeasurable, hmap]
    rw [integral_id_rademacherMeasure]
    ring
  · intro i hi
    exact (memLp_weighted_rademacher_coord a i).integrable (by norm_num)

theorem integral_inner_starProjection_sample_eq_zero
    (K : Submodule ℝ (WalkSpace I)) (v : WalkSpace I) :
    ∫ omega, inner ℝ v (K.starProjection (sampleVector omega))
      ∂rademacherProduct I = 0 := by
  simp_rw [inner_starProjection_sample_eq_sum]
  exact integral_weighted_rademacher_sum (projectedCoefficients K v)

theorem memLp_weighted_rademacher_sum (a : I → ℝ) :
    MemLp (fun omega : I → ℝ ↦ ∑ i, a i * omega i) 2
      (rademacherProduct I) := by
  have h := memLp_finsetSum Finset.univ
    (fun i _ ↦ memLp_weighted_rademacher_coord a i)
  simpa only [Finset.sum_apply] using h

theorem integral_sq_weighted_rademacher_sum (a : I → ℝ) :
    ∫ omega, (∑ i, a i * omega i) ^ 2 ∂rademacherProduct I = ∑ i, a i ^ 2 := by
  have hvar : Var[fun omega : I → ℝ ↦ ∑ i, a i * omega i;
      rademacherProduct I] = ∑ i, a i ^ 2 := by
    have hfun : (fun omega : I → ℝ ↦ ∑ i, a i * omega i) =
        ∑ i, fun omega : I → ℝ ↦ a i * omega i := by
      funext omega
      simp
    rw [hfun]
    unfold rademacherProduct
    rw [variance_sum_pi]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [variance_const_mul]
      have hid : Var[id; rademacherMeasure] = 1 := by
        rw [variance_eq_sub memLp_id_rademacherMeasure]
        simp only [Pi.pow_apply, id_eq, integral_id_rademacherMeasure, sub_zero]
        have hsq : (fun x : ℝ ↦ x ^ 2) =ᵐ[rademacherMeasure] fun _ ↦ 1 := by
          filter_upwards [ae_abs_eq_one_rademacherMeasure] with x hx
          rw [← sq_abs, hx]
          norm_num
        rw [integral_congr_ae hsq]
        simp
      change a i ^ 2 * Var[id; rademacherMeasure] = a i ^ 2
      rw [hid, mul_one]
    · intro i
      exact memLp_id_rademacherMeasure.const_mul (a i)
  rw [← hvar]
  rw [variance_of_integral_eq_zero]
  · exact (Finset.measurable_fun_sum Finset.univ fun i _ ↦
      measurable_const.mul (measurable_pi_apply i)).aemeasurable
  · exact integral_weighted_rademacher_sum a

theorem norm_sq_starProjection_eq_sum_inner_sq
    (K : Submodule ℝ (WalkSpace I)) (omega : I → ℝ) :
    ‖K.starProjection (sampleVector omega)‖ ^ 2 =
      ∑ k : Fin (Module.finrank ℝ K),
        inner ℝ ((stdOrthonormalBasis ℝ K k : K) : WalkSpace I)
          (sampleVector omega) ^ 2 := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ K)) ℝ K :=
    stdOrthonormalBasis ℝ K
  let y : K := ⟨K.starProjection (sampleVector omega),
    K.starProjection_apply_mem (sampleVector omega)⟩
  change ‖y‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq y, ← b.sum_inner_mul_inner y y]
  apply Finset.sum_congr rfl
  intro k hk
  have hproj : inner ℝ (b k) y =
      inner ℝ ((b k : K) : WalkSpace I) (sampleVector omega) := by
    change inner ℝ (b k) (K.orthogonalProjectionOnto (sampleVector omega)) = _
    exact K.inner_orthogonalProjectionOnto_eq_of_mem_left (b k) (sampleVector omega)
  have hcomm : inner ℝ y (b k) = inner ℝ (b k) y :=
    (real_inner_comm y (b k)).symm
  rw [hcomm, hproj]
  ring

theorem integral_norm_sq_starProjection (K : Submodule ℝ (WalkSpace I)) :
    ∫ omega, ‖K.starProjection (sampleVector omega)‖ ^ 2
      ∂rademacherProduct I = (Module.finrank ℝ K : ℝ) := by
  simp_rw [norm_sq_starProjection_eq_sum_inner_sq K]
  rw [integral_finsetSum]
  · have hsquare (w : WalkSpace I) :
        ∫ omega, inner ℝ w (sampleVector omega) ^ 2 ∂rademacherProduct I = ‖w‖ ^ 2 := by
      simp_rw [show ∀ omega, inner ℝ w (sampleVector omega) =
          ∑ i, w i * omega i by
        intro omega
        simp [PiLp.inner_apply, sampleVector, toWalk, mul_comm]]
      rw [integral_sq_weighted_rademacher_sum]
      exact (EuclideanSpace.real_norm_sq_eq w).symm
    simp_rw [hsquare]
    calc
      (∑ k : Fin (Module.finrank ℝ K),
          ‖((stdOrthonormalBasis ℝ K k : K) : WalkSpace I)‖ ^ 2) =
          ∑ _k : Fin (Module.finrank ℝ K), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        change ‖stdOrthonormalBasis ℝ K k‖ ^ 2 = 1
        rw [OrthonormalBasis.norm_eq_one]
        norm_num
      _ = (Module.finrank ℝ K : ℝ) := by simp
  · intro k hk
    have hmem : MemLp
        (fun omega ↦ inner ℝ
          ((stdOrthonormalBasis ℝ K k : K) : WalkSpace I) (sampleVector omega))
        2 (rademacherProduct I) := by
      simp_rw [show ∀ omega, inner ℝ
          ((stdOrthonormalBasis ℝ K k : K) : WalkSpace I) (sampleVector omega) =
          ∑ i, (((stdOrthonormalBasis ℝ K k : K) : WalkSpace I) i) * omega i by
        intro omega
        simp [PiLp.inner_apply, sampleVector, toWalk, mul_comm]]
      exact memLp_weighted_rademacher_sum _
    exact hmem.integrable_sq

/-! ## The edge step and its exponential potential -/

variable [DecidableEq I] [DecidableEq J]

/-- The permitted-increment subspace at a state. -/
def edgeSubspace (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) : Submodule ℝ (WalkSpace I) :=
  tightIncrementSubspace (fun j ↦ normalizedConstraint (v j))
    (activeCoordinates delta x) (activeDiscrepancies delta v x₀ c x)

/-- One projected sign increment. -/
def edgeIncrement (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ) : WalkSpace I :=
  (edgeSubspace delta v x₀ c x).starProjection (sampleVector omega)

/-- One edge-walk update. -/
def edgeStep (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ) : WalkSpace I :=
  x + gamma • edgeIncrement delta v x₀ c x omega

theorem edgeIncrement_mem (delta : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ) :
    edgeIncrement delta v x₀ c x omega ∈ edgeSubspace delta v x₀ c x := by
  exact (edgeSubspace delta v x₀ c x).starProjection_apply_mem _

theorem edgeIncrement_apply_eq_zero_of_active
    (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ)
    {i : I} (hi : i ∈ activeCoordinates delta x) :
    edgeIncrement delta v x₀ c x omega i = 0 := by
  exact (mem_tightIncrementSubspace_iff
    (fun j ↦ normalizedConstraint (v j))
    (activeCoordinates delta x) (activeDiscrepancies delta v x₀ c x) _).1
      (edgeIncrement_mem delta v x₀ c x omega) |>.1 i hi

theorem inner_edgeIncrement_eq_zero_of_active
    (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ)
    {j : J} (hj : j ∈ activeDiscrepancies delta v x₀ c x) :
    inner ℝ (normalizedConstraint (v j))
      (edgeIncrement delta v x₀ c x omega) = 0 := by
  exact (mem_tightIncrementSubspace_iff
    (fun j ↦ normalizedConstraint (v j))
    (activeCoordinates delta x) (activeDiscrepancies delta v x₀ c x) _).1
      (edgeIncrement_mem delta v x₀ c x omega) |>.2 j hj

theorem norm_edgeIncrement_le (delta : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ) :
    ‖edgeIncrement delta v x₀ c x omega‖ ≤ ‖sampleVector omega‖ := by
  exact (edgeSubspace delta v x₀ c x).norm_starProjection_apply_le _

/-- Every point in the support of the Rademacher product has squared
Euclidean norm equal to the ambient dimension. -/
theorem norm_sampleVector_sq_of_signs {omega : I → ℝ}
    (homega : ∀ i, |omega i| = 1) :
    ‖sampleVector omega‖ ^ 2 = Fintype.card I := by
  rw [norm_walkSpace_sq]
  simp only [sampleVector, toWalk, PiLp.toLp_apply]
  calc
    ∑ i, omega i ^ 2 = ∑ _i : I, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      nlinarith [sq_abs (omega i), homega i]
    _ = Fintype.card I := by simp

theorem norm_sampleVector_le_sqrt_card {omega : I → ℝ}
    (homega : ∀ i, |omega i| = 1) :
    ‖sampleVector omega‖ ≤ sqrt (Fintype.card I) := by
  have hsq := norm_sampleVector_sq_of_signs homega
  rw [← Real.sqrt_sq (norm_nonneg _), hsq]

theorem normalizedDiscrepancy_edgeStep
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ) (j : J) :
    normalizedDiscrepancy (v j) x₀ (edgeStep delta gamma v x₀ c x omega) =
      normalizedDiscrepancy (v j) x₀ x +
        gamma * inner ℝ (normalizedConstraint (v j))
          (edgeIncrement delta v x₀ c x omega) := by
  rw [normalizedDiscrepancy, normalizedDiscrepancy, edgeStep]
  have hsub : x + gamma • edgeIncrement delta v x₀ c x omega - toWalk x₀ =
      (x - toWalk x₀) + gamma • edgeIncrement delta v x₀ c x omega := by
    abel
  rw [hsub, inner_add_right, inner_smul_right]

/-- The exponential weight from the Lovett--Meka entropy budget. -/
def entropyWeight (a : ℝ) : ℝ := exp (-a ^ 2 / 16)

/-- One side of the compensated exponential potential for a row. -/
def signedRowPotential (sigma gamma : ℝ) (t : ℕ) (a y : ℝ) : ℝ :=
  entropyWeight a *
    exp (sigma * (a / 5) * y - (a / 5) ^ 2 * gamma ^ 2 * t / 2)

/-- The two-sided row potential. -/
def rowPotential (gamma : ℝ) (t : ℕ) (a y : ℝ) : ℝ :=
  signedRowPotential 1 gamma t a y + signedRowPotential (-1) gamma t a y

/-- Sum of the row potentials. -/
def discrepancyPotential (gamma : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) : ℝ :=
  ∑ j, rowPotential gamma t (c j) (normalizedDiscrepancy (v j) x₀ x)

/-- Euclidean progress minus five times the exponential discrepancy
potential.  The factor five is the total variance budget of the walk. -/
def edgeScore (gamma : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) : ℝ :=
  ‖x‖ ^ 2 - 5 * discrepancyPotential gamma t v x₀ c x

theorem discrepancyPotential_zero (gamma : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) :
    discrepancyPotential gamma 0 v x₀ c (toWalk x₀) =
      2 * ∑ j, entropyWeight (c j) := by
  simp [discrepancyPotential, rowPotential, signedRowPotential,
    normalizedDiscrepancy, entropyWeight, Finset.mul_sum, two_mul]

theorem signedRowPotential_nonneg (sigma gamma : ℝ) (t : ℕ) (a y : ℝ) :
    0 ≤ signedRowPotential sigma gamma t a y := by
  exact mul_nonneg (le_of_lt (exp_pos _)) (le_of_lt (exp_pos _))

theorem rowPotential_nonneg (gamma : ℝ) (t : ℕ) (a y : ℝ) :
    0 ≤ rowPotential gamma t a y :=
  add_nonneg (signedRowPotential_nonneg _ _ _ _ _)
    (signedRowPotential_nonneg _ _ _ _ _)

theorem integral_signedRowPotential_step_le
    (sigma gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) (j : J) (hsigma : sigma ^ 2 = 1) :
    ∫ omega,
        signedRowPotential sigma gamma (t + 1) (c j)
          (normalizedDiscrepancy (v j) x₀
            (edgeStep delta gamma v x₀ c x omega))
      ∂rademacherProduct I ≤
        signedRowPotential sigma gamma t (c j)
          (normalizedDiscrepancy (v j) x₀ x) := by
  let S := edgeSubspace delta v x₀ c x
  let w := normalizedConstraint (v j)
  let a := c j / 5
  let y := normalizedDiscrepancy (v j) x₀ x
  let q := sigma * a * gamma
  let base := sigma * a * y - a ^ 2 * gamma ^ 2 * t / 2 -
    a ^ 2 * gamma ^ 2 / 2
  let B := entropyWeight (c j) * exp base
  have hrewrite (omega : I → ℝ) :
      signedRowPotential sigma gamma (t + 1) (c j)
          (normalizedDiscrepancy (v j) x₀
            (edgeStep delta gamma v x₀ c x omega)) =
        B * exp (q * inner ℝ w (S.starProjection (sampleVector omega))) := by
    rw [normalizedDiscrepancy_edgeStep]
    unfold signedRowPotential
    change entropyWeight (c j) * exp _ =
      (entropyWeight (c j) * exp base) * exp _
    calc
      entropyWeight (c j) * exp _ =
          entropyWeight (c j) *
            (exp base * exp (q * inner ℝ w
              (S.starProjection (sampleVector omega)))) := by
        congr 1
        rw [← exp_add]
        congr 1
        dsimp only [base, a, y, q, S, w, edgeIncrement]
        push_cast
        ring
      _ = (entropyWeight (c j) * exp base) *
          exp (q * inner ℝ w (S.starProjection (sampleVector omega))) := by
        ring
  simp_rw [hrewrite]
  rw [integral_const_mul]
  have hB : 0 ≤ B := mul_nonneg (le_of_lt (exp_pos _)) (le_of_lt (exp_pos _))
  calc
    B * ∫ omega, exp (q * inner ℝ w (S.starProjection (sampleVector omega)))
        ∂rademacherProduct I ≤ B * exp (q ^ 2 * ‖w‖ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left
        (integral_exp_inner_starProjection_sample_le S w q) hB
    _ ≤ B * exp (q ^ 2 / 2) := by
      gcongr
      have hwSq : ‖w‖ ^ 2 ≤ 1 := by
        nlinarith [mul_self_le_mul_self (norm_nonneg w)
          (norm_normalizedConstraint_le_one (v j))]
      nlinarith [hwSq, sq_nonneg q]
    _ = signedRowPotential sigma gamma t (c j) y := by
      dsimp only [B, base, q, a]
      unfold signedRowPotential
      rw [mul_assoc, ← exp_add]
      congr 2
      push_cast
      nlinarith

theorem integrable_signedRowPotential_step
    (sigma gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) (j : J) :
    Integrable (fun omega ↦
      signedRowPotential sigma gamma (t + 1) (c j)
        (normalizedDiscrepancy (v j) x₀
          (edgeStep delta gamma v x₀ c x omega)))
      (rademacherProduct I) := by
  let S := edgeSubspace delta v x₀ c x
  let w := normalizedConstraint (v j)
  let q := sigma * (c j / 5) * gamma
  let base := sigma * (c j / 5) * normalizedDiscrepancy (v j) x₀ x -
    (c j / 5) ^ 2 * gamma ^ 2 * t / 2 -
    (c j / 5) ^ 2 * gamma ^ 2 / 2
  let B := entropyWeight (c j) * exp base
  have heq : (fun omega ↦
      signedRowPotential sigma gamma (t + 1) (c j)
        (normalizedDiscrepancy (v j) x₀
          (edgeStep delta gamma v x₀ c x omega))) =
      (fun omega ↦ B * exp (q * inner ℝ w
        (S.starProjection (sampleVector omega)))) := by
    funext omega
    rw [normalizedDiscrepancy_edgeStep]
    unfold signedRowPotential
    change entropyWeight (c j) * exp _ =
      (entropyWeight (c j) * exp base) * exp _
    calc
      entropyWeight (c j) * exp _ =
          entropyWeight (c j) *
            (exp base * exp (q * inner ℝ w
              (S.starProjection (sampleVector omega)))) := by
        congr 1
        rw [← exp_add]
        congr 1
        dsimp only [base, q, S, w, edgeIncrement]
        push_cast
        ring
      _ = (entropyWeight (c j) * exp base) *
          exp (q * inner ℝ w (S.starProjection (sampleVector omega))) := by
        ring
  rw [heq]
  exact (integrable_exp_inner_starProjection_sample S w q).const_mul B

theorem integral_rowPotential_step_le
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) (j : J) :
    ∫ omega,
        rowPotential gamma (t + 1) (c j)
          (normalizedDiscrepancy (v j) x₀
            (edgeStep delta gamma v x₀ c x omega))
      ∂rademacherProduct I ≤
        rowPotential gamma t (c j)
          (normalizedDiscrepancy (v j) x₀ x) := by
  unfold rowPotential
  rw [integral_add]
  · exact add_le_add
      (integral_signedRowPotential_step_le 1 gamma delta t v x₀ c x j (by norm_num))
      (integral_signedRowPotential_step_le (-1) gamma delta t v x₀ c x j (by norm_num))
  · exact integrable_signedRowPotential_step 1 gamma delta t v x₀ c x j
  · exact integrable_signedRowPotential_step (-1) gamma delta t v x₀ c x j

theorem integrable_discrepancyPotential_step
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) :
    Integrable (fun omega ↦ discrepancyPotential gamma (t + 1) v x₀ c
      (edgeStep delta gamma v x₀ c x omega)) (rademacherProduct I) := by
  unfold discrepancyPotential
  exact integrable_finset_sum Finset.univ fun j hj ↦
    integrable_signedRowPotential_step 1 gamma delta t v x₀ c x j |>.add
      (integrable_signedRowPotential_step (-1) gamma delta t v x₀ c x j)

theorem integral_discrepancyPotential_step_le
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) :
    ∫ omega, discrepancyPotential gamma (t + 1) v x₀ c
        (edgeStep delta gamma v x₀ c x omega)
      ∂rademacherProduct I ≤ discrepancyPotential gamma t v x₀ c x := by
  unfold discrepancyPotential
  rw [integral_finsetSum]
  exact Finset.sum_le_sum fun j hj ↦
    integral_rowPotential_step_le gamma delta t v x₀ c x j
  intro j hj
  exact (integrable_signedRowPotential_step 1 gamma delta t v x₀ c x j).add
    (integrable_signedRowPotential_step (-1) gamma delta t v x₀ c x j)

theorem integrable_inner_starProjection_sample
    (K : Submodule ℝ (WalkSpace I)) (v : WalkSpace I) :
    Integrable (fun omega ↦ inner ℝ v (K.starProjection (sampleVector omega)))
      (rademacherProduct I) := by
  simp_rw [inner_starProjection_sample_eq_sum]
  exact (memLp_weighted_rademacher_sum (projectedCoefficients K v)).integrable
    (by norm_num)

theorem integrable_norm_sq_starProjection
    (K : Submodule ℝ (WalkSpace I)) :
    Integrable (fun omega ↦ ‖K.starProjection (sampleVector omega)‖ ^ 2)
      (rademacherProduct I) := by
  simp_rw [norm_sq_starProjection_eq_sum_inner_sq K]
  exact integrable_finset_sum Finset.univ fun k hk ↦
    ((memLp_weighted_rademacher_sum
      (fun i ↦ (((stdOrthonormalBasis ℝ K k : K) : WalkSpace I) i))).integrable_sq.congr
        (Filter.Eventually.of_forall fun omega ↦ by
          congr 1
          simp [PiLp.inner_apply, sampleVector, toWalk, mul_comm]))

theorem norm_edgeStep_sq
    (gamma delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ) :
    ‖edgeStep delta gamma v x₀ c x omega‖ ^ 2 = ‖x‖ ^ 2 +
      2 * gamma * inner ℝ x (edgeIncrement delta v x₀ c x omega) +
      gamma ^ 2 * ‖edgeIncrement delta v x₀ c x omega‖ ^ 2 := by
  rw [edgeStep, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, inner_smul_right,
    starRingEnd_apply, star_trivial]
  rw [mul_pow, sq_abs]
  ring

theorem integral_norm_edgeStep_sq
    (gamma delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) :
    ∫ omega, ‖edgeStep delta gamma v x₀ c x omega‖ ^ 2
      ∂rademacherProduct I = ‖x‖ ^ 2 +
        gamma ^ 2 * Module.finrank ℝ (edgeSubspace delta v x₀ c x) := by
  simp_rw [norm_edgeStep_sq]
  have hconst : Integrable (fun _omega : I → ℝ ↦ ‖x‖ ^ 2)
      (rademacherProduct I) := integrable_const _
  have hlinear : Integrable (fun omega : I → ℝ ↦
      2 * gamma * inner ℝ x (edgeIncrement delta v x₀ c x omega))
      (rademacherProduct I) :=
    (integrable_inner_starProjection_sample
      (edgeSubspace delta v x₀ c x) x).const_mul (2 * gamma)
  have hquadratic : Integrable (fun omega : I → ℝ ↦
      gamma ^ 2 * ‖edgeIncrement delta v x₀ c x omega‖ ^ 2)
      (rademacherProduct I) :=
    (integrable_norm_sq_starProjection
      (edgeSubspace delta v x₀ c x)).const_mul (gamma ^ 2)
  have hzero : ∫ omega,
      inner ℝ x (edgeIncrement delta v x₀ c x omega)
        ∂rademacherProduct I = 0 := by
    exact integral_inner_starProjection_sample_eq_zero
      (edgeSubspace delta v x₀ c x) x
  have hsquare : ∫ omega,
      ‖edgeIncrement delta v x₀ c x omega‖ ^ 2
        ∂rademacherProduct I =
        (Module.finrank ℝ (edgeSubspace delta v x₀ c x) : ℝ) := by
    exact integral_norm_sq_starProjection (edgeSubspace delta v x₀ c x)
  have hmeasure : (rademacherProduct I).real Set.univ = 1 := by
    rw [Measure.real, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
  rw [integral_add]
  · rw [integral_add]
    · rw [integral_const, integral_const_mul,
    hzero, mul_zero, integral_const_mul, hsquare]
      rw [hmeasure]
      simp only [mul_one, add_zero]
      ring
    · exact hconst
    · exact hlinear
  · exact hconst.add hlinear
  · exact hquadratic

theorem integrable_norm_edgeStep_sq
    (gamma delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) :
    Integrable (fun omega ↦ ‖edgeStep delta gamma v x₀ c x omega‖ ^ 2)
      (rademacherProduct I) := by
  simp_rw [norm_edgeStep_sq]
  exact (integrable_const _).add
    ((integrable_inner_starProjection_sample
      (edgeSubspace delta v x₀ c x) x).const_mul (2 * gamma)) |>.add
        ((integrable_norm_sq_starProjection
          (edgeSubspace delta v x₀ c x)).const_mul (gamma ^ 2))

theorem integrable_edgeScore_step
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) :
    Integrable (fun omega ↦ edgeScore gamma (t + 1) v x₀ c
      (edgeStep delta gamma v x₀ c x omega)) (rademacherProduct I) := by
  unfold edgeScore
  exact (integrable_norm_edgeStep_sq gamma delta v x₀ c x).sub
    ((integrable_discrepancyPotential_step gamma delta t v x₀ c x).const_mul 5)

theorem integral_edgeScore_step_ge
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) :
    edgeScore gamma t v x₀ c x +
        gamma ^ 2 * Module.finrank ℝ (edgeSubspace delta v x₀ c x) ≤
      ∫ omega, edgeScore gamma (t + 1) v x₀ c
        (edgeStep delta gamma v x₀ c x omega) ∂rademacherProduct I := by
  rw [edgeScore]
  simp_rw [edgeScore]
  rw [integral_sub, integral_const_mul, integral_norm_edgeStep_sq]
  · have hp := integral_discrepancyPotential_step_le gamma delta t v x₀ c x
    linarith
  · exact integrable_norm_edgeStep_sq gamma delta v x₀ c x
  · exact (integrable_discrepancyPotential_step gamma delta t v x₀ c x).const_mul 5

theorem measure_not_signs_eq_zero :
    rademacherProduct I {omega | ¬ ∀ i, |omega i| = 1} = 0 := by
  rw [← ae_iff]
  simpa only [Set.mem_setOf_eq, not_not] using
    (ae_forall_abs_eq_one_rademacherProduct I)

/-- At each state an actual sign vector realizes at least the average
increase in the score. -/
theorem exists_sign_edgeScore_step
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) :
    ∃ omega : I → ℝ, (∀ i, |omega i| = 1) ∧
      edgeScore gamma t v x₀ c x +
          gamma ^ 2 * Module.finrank ℝ (edgeSubspace delta v x₀ c x) ≤
        edgeScore gamma (t + 1) v x₀ c
          (edgeStep delta gamma v x₀ c x omega) := by
  let N : Set (I → ℝ) := {omega | ¬ ∀ i, |omega i| = 1}
  obtain ⟨omega, homegaN, homega⟩ :=
    exists_notMem_null_integral_le
      (μ := rademacherProduct I)
      (f := fun omega ↦ edgeScore gamma (t + 1) v x₀ c
        (edgeStep delta gamma v x₀ c x omega))
      (integrable_edgeScore_step gamma delta t v x₀ c x)
      (show rademacherProduct I N = 0 by exact measure_not_signs_eq_zero)
  refine ⟨omega, ?_, (integral_edgeScore_step_ge gamma delta t v x₀ c x).trans homega⟩
  simpa only [N, Set.mem_setOf_eq, not_not] using homegaN

end EdgeWalk

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/PartialColoring.lean` -/

section
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/

/-!
# Iterating the projected Rademacher edge walk

This file completes the deterministic iteration of the one-step score
inequality in `EdgeWalk`.  The walk uses step size `1 / q`, runs for
`5 * q ^ 2` steps, and freezes every coordinate or discrepancy row within
`delta` of its boundary.  Monotonicity of the frozen sets and the terminal
exponential potential force at least half of the coordinates to reach a
`delta`-neighbourhood of the cube boundary.  The compact endpoint then
removes `delta`.
-/

open Real Set
open scoped BigOperators

noncomputable section

namespace EdgeWalk

open Erdos228.Discrepancy Erdos228.ProjectionWalk

universe u v

variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]
variable [DecidableEq I] [DecidableEq J]

/-! ## A deterministic choice of the next sign vector -/

/-- A sign vector witnessing the one-step score inequality. -/
def edgeChoice (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) : I → ℝ :=
  Classical.choose (exists_sign_edgeScore_step gamma delta t v x₀ c x)

theorem edgeChoice_isSign (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) :
    ∀ i, |edgeChoice gamma delta t v x₀ c x i| = 1 :=
  (Classical.choose_spec
    (exists_sign_edgeScore_step gamma delta t v x₀ c x)).1

theorem edgeChoice_score (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) :
    edgeScore gamma t v x₀ c x +
        gamma ^ 2 * Module.finrank ℝ (edgeSubspace delta v x₀ c x) ≤
      edgeScore gamma (t + 1) v x₀ c
        (edgeStep delta gamma v x₀ c x
          (edgeChoice gamma delta t v x₀ c x)) :=
  (Classical.choose_spec
    (exists_sign_edgeScore_step gamma delta t v x₀ c x)).2

/-- The deterministic edge walk obtained by repeatedly taking `edgeChoice`. -/
def edgeWalk (delta gamma : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) : ℕ → WalkSpace I
  | 0 => toWalk x₀
  | t + 1 => edgeStep delta gamma v x₀ c (edgeWalk delta gamma v x₀ c t)
      (edgeChoice gamma delta t v x₀ c (edgeWalk delta gamma v x₀ c t))

@[simp] theorem edgeWalk_zero (delta gamma : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) :
    edgeWalk delta gamma v x₀ c 0 = toWalk x₀ := rfl

@[simp] theorem edgeWalk_succ (delta gamma : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) (t : ℕ) :
    edgeWalk delta gamma v x₀ c (t + 1) =
      edgeStep delta gamma v x₀ c (edgeWalk delta gamma v x₀ c t)
        (edgeChoice gamma delta t v x₀ c (edgeWalk delta gamma v x₀ c t)) := rfl

theorem edgeWalk_score_step (delta gamma : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) (t : ℕ) :
    edgeScore gamma t v x₀ c (edgeWalk delta gamma v x₀ c t) +
        gamma ^ 2 * Module.finrank ℝ
          (edgeSubspace delta v x₀ c (edgeWalk delta gamma v x₀ c t)) ≤
      edgeScore gamma (t + 1) v x₀ c
        (edgeWalk delta gamma v x₀ c (t + 1)) := by
  simpa only [edgeWalk_succ] using
    edgeChoice_score gamma delta t v x₀ c (edgeWalk delta gamma v x₀ c t)

/-! ## Cube and discrepancy invariants -/

theorem abs_apply_le_norm_walkSpace (x : WalkSpace I) (i : I) :
    |x i| ≤ ‖x‖ := by
  have hi : x i ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_walkSpace_sq]
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)
  nlinarith [sq_abs (x i), abs_nonneg (x i), norm_nonneg x]

theorem abs_edgeIncrement_le_sqrt_card
    (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ)
    (homega : ∀ i, |omega i| = 1) (i : I) :
    |edgeIncrement delta v x₀ c x omega i| ≤
      sqrt (Fintype.card I) := by
  exact (abs_apply_le_norm_walkSpace _ i).trans
    ((norm_edgeIncrement_le delta v x₀ c x omega).trans
      (norm_sampleVector_le_sqrt_card homega))

theorem abs_inner_edgeIncrement_le_sqrt_card
    (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ)
    (homega : ∀ i, |omega i| = 1) (j : J) :
    |inner ℝ (normalizedConstraint (v j))
        (edgeIncrement delta v x₀ c x omega)| ≤
      sqrt (Fintype.card I) := by
  calc
    |inner ℝ (normalizedConstraint (v j))
        (edgeIncrement delta v x₀ c x omega)| ≤
        ‖normalizedConstraint (v j)‖ *
          ‖edgeIncrement delta v x₀ c x omega‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ 1 * sqrt (Fintype.card I) := by
      gcongr
      · exact norm_normalizedConstraint_le_one (v j)
      · exact (norm_edgeIncrement_le delta v x₀ c x omega).trans
          (norm_sampleVector_le_sqrt_card homega)
    _ = sqrt (Fintype.card I) := one_mul _

theorem edgeStep_inCube
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ)
    (hx : InCube x) (homega : ∀ i, |omega i| = 1)
    (hgamma : 0 ≤ gamma)
    (hdelta : delta = gamma * sqrt (Fintype.card I)) :
    InCube (edgeStep delta gamma v x₀ c x omega) := by
  intro i
  by_cases hi : i ∈ activeCoordinates delta x
  · rw [edgeStep]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      edgeIncrement_apply_eq_zero_of_active delta v x₀ c x omega hi,
      mul_zero, add_zero]
    exact hx i
  · have hxi : |x i| < 1 - delta := by
      simpa only [mem_activeCoordinates, not_le] using hi
    have hinc := abs_edgeIncrement_le_sqrt_card
      delta v x₀ c x omega homega i
    rw [edgeStep]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    calc
      |x i + gamma * edgeIncrement delta v x₀ c x omega i| ≤
          |x i| + |gamma * edgeIncrement delta v x₀ c x omega i| :=
        abs_add_le _ _
      _ = |x i| + gamma * |edgeIncrement delta v x₀ c x omega i| := by
        rw [abs_mul, abs_of_nonneg hgamma]
      _ ≤ |x i| + gamma * sqrt (Fintype.card I) := by gcongr
      _ ≤ 1 := by rw [← hdelta]; linarith

theorem edgeStep_normalizedDiscrepancy_le
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ)
    (hx : ∀ j, |normalizedDiscrepancy (v j) x₀ x| ≤ c j)
    (homega : ∀ i, |omega i| = 1) (hgamma : 0 ≤ gamma)
    (hdelta : delta = gamma * sqrt (Fintype.card I)) :
    ∀ j, |normalizedDiscrepancy (v j) x₀
      (edgeStep delta gamma v x₀ c x omega)| ≤ c j := by
  intro j
  by_cases hv : l2Norm (v j) = 0
  · simpa [normalizedDiscrepancy, normalizedConstraint, hv] using hx j
  by_cases hj : j ∈ activeDiscrepancies delta v x₀ c x
  · rw [normalizedDiscrepancy_edgeStep,
      inner_edgeIncrement_eq_zero_of_active delta v x₀ c x omega hj,
      mul_zero, add_zero]
    exact hx j
  · have hvpos : 0 < l2Norm (v j) :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hv)
    have hy : |normalizedDiscrepancy (v j) x₀ x| < c j - delta := by
      simpa only [mem_activeDiscrepancies, hvpos, true_and, not_le] using hj
    have hinc := abs_inner_edgeIncrement_le_sqrt_card
      delta v x₀ c x omega homega j
    rw [normalizedDiscrepancy_edgeStep]
    calc
      |normalizedDiscrepancy (v j) x₀ x + gamma *
          inner ℝ (normalizedConstraint (v j))
            (edgeIncrement delta v x₀ c x omega)| ≤
          |normalizedDiscrepancy (v j) x₀ x| +
            |gamma * inner ℝ (normalizedConstraint (v j))
              (edgeIncrement delta v x₀ c x omega)| := abs_add_le _ _
      _ = |normalizedDiscrepancy (v j) x₀ x| + gamma *
            |inner ℝ (normalizedConstraint (v j))
              (edgeIncrement delta v x₀ c x omega)| := by
        rw [abs_mul, abs_of_nonneg hgamma]
      _ ≤ |normalizedDiscrepancy (v j) x₀ x| +
            gamma * sqrt (Fintype.card I) := by gcongr
      _ ≤ c j := by rw [← hdelta]; linarith

theorem edgeWalk_inCube
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (hx₀ : InCube x₀) (hgamma : 0 ≤ gamma)
    (hdelta : delta = gamma * sqrt (Fintype.card I)) :
    ∀ t, InCube (edgeWalk delta gamma v x₀ c t) := by
  intro t
  induction t with
  | zero => simpa [edgeWalk] using hx₀
  | succ t ht =>
      rw [edgeWalk_succ]
      exact edgeStep_inCube delta gamma v x₀ c _ _ ht
        (edgeChoice_isSign gamma delta t v x₀ c _) hgamma hdelta

theorem edgeWalk_normalizedDiscrepancy_le
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (hgamma : 0 ≤ gamma)
    (hdelta : delta = gamma * sqrt (Fintype.card I)) :
    ∀ t j, |normalizedDiscrepancy (v j) x₀
      (edgeWalk delta gamma v x₀ c t)| ≤ c j := by
  intro t
  induction t with
  | zero =>
      intro j
      simpa [edgeWalk, normalizedDiscrepancy] using hc j
  | succ t ht =>
      rw [edgeWalk_succ]
      exact edgeStep_normalizedDiscrepancy_le delta gamma v x₀ c _ _ ht
        (edgeChoice_isSign gamma delta t v x₀ c _) hgamma hdelta

/-! ## Monotonicity of the active sets -/

theorem activeCoordinates_mono_edgeStep
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ) :
    activeCoordinates delta x ⊆
      activeCoordinates delta (edgeStep delta gamma v x₀ c x omega) := by
  intro i hi
  rw [mem_activeCoordinates]
  rw [edgeStep]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    edgeIncrement_apply_eq_zero_of_active delta v x₀ c x omega hi,
    mul_zero, add_zero]
  exact mem_activeCoordinates.mp hi

theorem activeDiscrepancies_mono_edgeStep
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ) :
    activeDiscrepancies delta v x₀ c x ⊆
      activeDiscrepancies delta v x₀ c
        (edgeStep delta gamma v x₀ c x omega) := by
  intro j hj
  rw [mem_activeDiscrepancies]
  have hj' := (mem_activeDiscrepancies.mp hj)
  refine ⟨hj'.1, ?_⟩
  rw [normalizedDiscrepancy_edgeStep,
    inner_edgeIncrement_eq_zero_of_active delta v x₀ c x omega hj,
    mul_zero, add_zero]
  exact hj'.2

theorem activeCoordinates_mono_edgeWalk
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) {s t : ℕ} (hst : s ≤ t) :
    activeCoordinates delta (edgeWalk delta gamma v x₀ c s) ⊆
      activeCoordinates delta (edgeWalk delta gamma v x₀ c t) := by
  induction t, hst using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ t hst ih =>
      exact ih.trans (by
        rw [edgeWalk_succ]
        exact activeCoordinates_mono_edgeStep delta gamma v x₀ c _ _)

theorem activeDiscrepancies_mono_edgeWalk
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) {s t : ℕ} (hst : s ≤ t) :
    activeDiscrepancies delta v x₀ c (edgeWalk delta gamma v x₀ c s) ⊆
      activeDiscrepancies delta v x₀ c (edgeWalk delta gamma v x₀ c t) := by
  induction t, hst using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ t hst ih =>
      exact ih.trans (by
        rw [edgeWalk_succ]
        exact activeDiscrepancies_mono_edgeStep delta gamma v x₀ c _ _)

/-! ## The terminal potential -/

/-- A row within `delta` of its discrepancy boundary contributes at least
one unit to the compensated potential, throughout the first five units of
quadratic time.  The small-`a` case uses both signs of the potential; the
large-`a` case uses the sign agreeing with `y`. -/
theorem one_le_rowPotential_of_near_boundary
    (gamma delta : ℝ) (t : ℕ) (a y : ℝ)
    (ha : 0 ≤ a) (hdelta : 0 ≤ delta) (hdeltaSmall : delta ≤ 1 / 4)
    (htime : gamma ^ 2 * (t : ℝ) ≤ 5)
    (hnear : a - delta ≤ |y|) :
    1 ≤ rowPotential gamma t a y := by
  let Q : ℝ := (a / 5) ^ 2 * gamma ^ 2 * (t : ℝ) / 2
  have hQ : Q ≤ a ^ 2 / 10 := by
    have hmul := mul_le_mul_of_nonneg_left htime
      (div_nonneg (sq_nonneg (a / 5)) (by norm_num : (0 : ℝ) ≤ 2))
    dsimp only [Q]
    nlinarith
  by_cases hlarge : 16 * delta ≤ 3 * a
  · have hprod : 16 * a * delta ≤ 3 * a ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hlarge ha]
    by_cases hy : 0 ≤ y
    · have hay : a - delta ≤ y := by simpa [abs_of_nonneg hy] using hnear
      have haymul : a * (a - delta) ≤ a * y :=
        mul_le_mul_of_nonneg_left hay ha
      have hexponent :
          0 ≤ -a ^ 2 / 16 + a / 5 * y - Q := by
        nlinarith
      have hone : 1 ≤ signedRowPotential 1 gamma t a y := by
        rw [signedRowPotential, entropyWeight, ← exp_add]
        have heq : -a ^ 2 / 16 +
            (1 * (a / 5) * y - (a / 5) ^ 2 * gamma ^ 2 * (t : ℝ) / 2) =
            -a ^ 2 / 16 + a / 5 * y - Q := by
          dsimp only [Q]
          ring
        rw [heq]
        simpa only [exp_zero] using exp_le_exp.mpr hexponent
      exact hone.trans (le_add_of_nonneg_right
        (signedRowPotential_nonneg (-1) gamma t a y))
    · have hy' : y ≤ 0 := le_of_not_ge hy
      have hay : a - delta ≤ -y := by simpa [abs_of_nonpos hy'] using hnear
      have haymul : a * (a - delta) ≤ a * (-y) :=
        mul_le_mul_of_nonneg_left hay ha
      have hexponent :
          0 ≤ -a ^ 2 / 16 + (-1) * (a / 5) * y - Q := by
        nlinarith
      have hone : 1 ≤ signedRowPotential (-1) gamma t a y := by
        rw [signedRowPotential, entropyWeight, ← exp_add]
        have heq : -a ^ 2 / 16 +
            ((-1) * (a / 5) * y - (a / 5) ^ 2 * gamma ^ 2 * (t : ℝ) / 2) =
            -a ^ 2 / 16 + (-1) * (a / 5) * y - Q := by
          dsimp only [Q]
          ring
        rw [heq]
        simpa only [exp_zero] using exp_le_exp.mpr hexponent
      exact hone.trans (le_add_of_nonneg_left
        (signedRowPotential_nonneg 1 gamma t a y))
  · have haUpper : a < 4 / 3 := by
      have : 3 * a < 16 * delta := lt_of_not_ge hlarge
      nlinarith
    have haSq : 13 * a ^ 2 / 80 ≤ 1 / 2 := by
      nlinarith [sq_nonneg (a - 4 / 3)]
    have hbase : -1 / 2 ≤ -a ^ 2 / 16 - Q := by
      nlinarith
    let z : ℝ := a / 5 * y
    let base : ℝ := -a ^ 2 / 16 - Q
    have hsum : 1 ≤ (1 + (base + z)) + (1 + (base - z)) := by
      dsimp only [base]
      nlinarith
    calc
      1 ≤ (1 + (base + z)) + (1 + (base - z)) := hsum
      _ ≤ exp (base + z) + exp (base - z) :=
        add_le_add (by simpa [add_comm] using add_one_le_exp (base + z))
          (by simpa [add_comm] using add_one_le_exp (base - z))
      _ = rowPotential gamma t a y := by
        unfold rowPotential signedRowPotential entropyWeight
        rw [← exp_add, ← exp_add]
        dsimp only [base, z, Q]
        congr 1 <;> ring

/-! ## Accumulated score and the half-coordinate conclusion -/

theorem edgeWalk_score_sum
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (t : ℕ) :
    edgeScore gamma 0 v x₀ c (toWalk x₀) +
        gamma ^ 2 * ∑ s ∈ Finset.range t,
          (Module.finrank ℝ
            (edgeSubspace delta v x₀ c (edgeWalk delta gamma v x₀ c s)) : ℝ) ≤
      edgeScore gamma t v x₀ c (edgeWalk delta gamma v x₀ c t) := by
  induction t with
  | zero => simp
  | succ t ht =>
      rw [Finset.sum_range_succ]
      calc
        edgeScore gamma 0 v x₀ c (toWalk x₀) + gamma ^ 2 *
            ((∑ s ∈ Finset.range t,
              (Module.finrank ℝ (edgeSubspace delta v x₀ c
                (edgeWalk delta gamma v x₀ c s)) : ℝ)) +
              (Module.finrank ℝ (edgeSubspace delta v x₀ c
                (edgeWalk delta gamma v x₀ c t)) : ℝ)) =
            (edgeScore gamma 0 v x₀ c (toWalk x₀) + gamma ^ 2 *
              ∑ s ∈ Finset.range t,
                (Module.finrank ℝ (edgeSubspace delta v x₀ c
                  (edgeWalk delta gamma v x₀ c s)) : ℝ)) +
              gamma ^ 2 * (Module.finrank ℝ (edgeSubspace delta v x₀ c
                (edgeWalk delta gamma v x₀ c t)) : ℝ) := by ring
        _ ≤ edgeScore gamma t v x₀ c (edgeWalk delta gamma v x₀ c t) +
              gamma ^ 2 * (Module.finrank ℝ (edgeSubspace delta v x₀ c
                (edgeWalk delta gamma v x₀ c t)) : ℝ) :=
          add_le_add ht (le_refl _)
        _ ≤ edgeScore gamma (t + 1) v x₀ c
              (edgeWalk delta gamma v x₀ c (t + 1)) :=
          edgeWalk_score_step delta gamma v x₀ c t

theorem card_le_finrank_add_active
    (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) :
    Fintype.card I ≤
      Module.finrank ℝ (edgeSubspace delta v x₀ c x) +
        (activeCoordinates delta x).card +
        (activeDiscrepancies delta v x₀ c x).card := by
  have h := card_sub_tight_card_le_finrank
    (fun j ↦ normalizedConstraint (v j))
    (activeCoordinates delta x) (activeDiscrepancies delta v x₀ c x)
  change Fintype.card I -
      ((activeCoordinates delta x).card +
        (activeDiscrepancies delta v x₀ c x).card) ≤
    Module.finrank ℝ (edgeSubspace delta v x₀ c x) at h
  omega

theorem card_activeDiscrepancies_le_potential
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ) (x : WalkSpace I)
    (hc : ∀ j, 0 ≤ c j) (hdelta : 0 ≤ delta)
    (hdeltaSmall : delta ≤ 1 / 4)
    (htime : gamma ^ 2 * (t : ℝ) ≤ 5) :
    ((activeDiscrepancies delta v x₀ c x).card : ℝ) ≤
      discrepancyPotential gamma t v x₀ c x := by
  let A := activeDiscrepancies delta v x₀ c x
  calc
    (A.card : ℝ) = ∑ _j ∈ A, (1 : ℝ) := by simp [A]
    _ ≤ ∑ j ∈ A,
        rowPotential gamma t (c j) (normalizedDiscrepancy (v j) x₀ x) := by
      apply Finset.sum_le_sum
      intro j hj
      exact one_le_rowPotential_of_near_boundary gamma delta t (c j)
        (normalizedDiscrepancy (v j) x₀ x) (hc j) hdelta hdeltaSmall htime
        ((mem_activeDiscrepancies.mp hj).2)
    _ ≤ ∑ j,
        rowPotential gamma t (c j) (normalizedDiscrepancy (v j) x₀ x) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        (fun j hj₁ hj₂ ↦ rowPotential_nonneg gamma t (c j)
          (normalizedDiscrepancy (v j) x₀ x))
    _ = discrepancyPotential gamma t v x₀ c x := rfl

theorem norm_sq_le_card_of_inCube (x : WalkSpace I) (hx : InCube x) :
    ‖x‖ ^ 2 ≤ Fintype.card I := by
  rw [norm_walkSpace_sq]
  calc
    ∑ i, x i ^ 2 ≤ ∑ _i : I, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hsq := mul_self_le_mul_self (abs_nonneg (x i)) (hx i)
      nlinarith [sq_abs (x i)]
    _ = Fintype.card I := by simp

/-- If the walk runs for exactly five units of quadratic time, its terminal
active-coordinate set contains at least half of all coordinates. -/
theorem edgeWalk_terminal_half
    (delta gamma : ℝ) (T : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : InCube x₀) (hc : ∀ j, 0 ≤ c j)
    (hentropy : (∑ j, exp (-(c j) ^ 2 / 16)) ≤
      (Fintype.card I : ℝ) / 16)
    (hgamma : 0 ≤ gamma)
    (hdeltaEq : delta = gamma * sqrt (Fintype.card I))
    (hdelta : 0 ≤ delta) (hdeltaSmall : delta ≤ 1 / 4)
    (htime : gamma ^ 2 * (T : ℝ) = 5) :
    Fintype.card I ≤ 2 *
      (activeCoordinates delta (edgeWalk delta gamma v x₀ c T)).card := by
  let xT := edgeWalk delta gamma v x₀ c T
  let C := (activeCoordinates delta xT).card
  let D := (activeDiscrepancies delta v x₀ c xT).card
  let N : ℝ := Fintype.card I
  by_contra hhalf
  have hClt : 2 * C < Fintype.card I := by
    exact Nat.lt_of_not_ge hhalf
  have hNpos : 0 < N := by
    dsimp only [N]
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le (2 * C)) hClt)
  have hrank (s : ℕ) (hs : s ∈ Finset.range T) :
      N - C - D ≤
        (Module.finrank ℝ
          (edgeSubspace delta v x₀ c (edgeWalk delta gamma v x₀ c s)) : ℝ) := by
    have hsT : s ≤ T := Nat.le_of_lt (Finset.mem_range.mp hs)
    have hcoord := Finset.card_le_card
      (activeCoordinates_mono_edgeWalk delta gamma v x₀ c hsT)
    have hdisc := Finset.card_le_card
      (activeDiscrepancies_mono_edgeWalk delta gamma v x₀ c hsT)
    have hdim := card_le_finrank_add_active delta v x₀ c
      (edgeWalk delta gamma v x₀ c s)
    have hcoordR :
        ((activeCoordinates delta (edgeWalk delta gamma v x₀ c s)).card : ℝ) ≤ C := by
      exact_mod_cast hcoord
    have hdiscR :
        ((activeDiscrepancies delta v x₀ c
          (edgeWalk delta gamma v x₀ c s)).card : ℝ) ≤ D := by
      exact_mod_cast hdisc
    have hdimR : N ≤
        (Module.finrank ℝ
          (edgeSubspace delta v x₀ c (edgeWalk delta gamma v x₀ c s)) : ℝ) +
        (activeCoordinates delta (edgeWalk delta gamma v x₀ c s)).card +
        (activeDiscrepancies delta v x₀ c
          (edgeWalk delta gamma v x₀ c s)).card := by
      dsimp only [N]
      exact_mod_cast hdim
    linarith
  have hrankSum : (T : ℝ) * (N - C - D) ≤
      ∑ s ∈ Finset.range T,
        (Module.finrank ℝ
          (edgeSubspace delta v x₀ c (edgeWalk delta gamma v x₀ c s)) : ℝ) := by
    calc
      (T : ℝ) * (N - C - D) =
          ∑ _s ∈ Finset.range T, (N - C - D) := by
        simp
        ring
      _ ≤ _ := Finset.sum_le_sum fun s hs ↦ hrank s hs
  have hscore := edgeWalk_score_sum delta gamma v x₀ c T
  have hprogress :
      edgeScore gamma 0 v x₀ c (toWalk x₀) + 5 * (N - C - D) ≤
        edgeScore gamma T v x₀ c xT := by
    have hmul := mul_le_mul_of_nonneg_left hrankSum (sq_nonneg gamma)
    calc
      edgeScore gamma 0 v x₀ c (toWalk x₀) + 5 * (N - C - D) =
          edgeScore gamma 0 v x₀ c (toWalk x₀) +
            gamma ^ 2 * ((T : ℝ) * (N - C - D)) := by
        rw [← htime]
        ring
      _ ≤ edgeScore gamma 0 v x₀ c (toWalk x₀) + gamma ^ 2 *
          ∑ s ∈ Finset.range T,
            (Module.finrank ℝ (edgeSubspace delta v x₀ c
              (edgeWalk delta gamma v x₀ c s)) : ℝ) := by linarith
      _ ≤ edgeScore gamma T v x₀ c xT := hscore
  have hD : (D : ℝ) ≤ discrepancyPotential gamma T v x₀ c xT := by
    exact card_activeDiscrepancies_le_potential gamma delta T v x₀ c xT hc
      hdelta hdeltaSmall htime.le
  have hP0 : discrepancyPotential gamma 0 v x₀ c (toWalk x₀) ≤ N / 8 := by
    rw [discrepancyPotential_zero]
    change 2 * ∑ j, exp (-(c j) ^ 2 / 16) ≤ N / 8
    linarith
  have hxTCube : InCube xT :=
    edgeWalk_inCube delta gamma v x₀ c hx₀ hgamma hdeltaEq T
  have hxTNorm : ‖xT‖ ^ 2 ≤ N :=
    norm_sq_le_card_of_inCube xT hxTCube
  have hx₀Norm : 0 ≤ ‖toWalk x₀‖ ^ 2 := sq_nonneg _
  have hlower : -5 * (N / 8) + 5 * (N - C) ≤ ‖xT‖ ^ 2 := by
    dsimp only [xT] at hprogress hD hxTNorm ⊢
    simp only [edgeScore] at hprogress
    nlinarith
  have hCltR : 2 * (C : ℝ) < N := by
    dsimp only [N]
    exact_mod_cast hClt
  nlinarith

/-! ## Arbitrary accuracy and compactness -/

theorem exists_walk_parameters (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ q : ℕ, 0 < q ∧
      let gamma : ℝ := 1 / (q : ℝ)
      let delta : ℝ := gamma * sqrt (Fintype.card I)
      let T : ℕ := 5 * q ^ 2
      0 ≤ gamma ∧ 0 ≤ delta ∧ delta ≤ 1 / 4 ∧ delta ≤ epsilon ∧
        gamma ^ 2 * (T : ℝ) = 5 := by
  obtain ⟨q, hq⟩ := exists_nat_gt
    (max 1 (max (4 * sqrt (Fintype.card I))
      (sqrt (Fintype.card I) / epsilon)))
  have hqOne : (1 : ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq
  have hqposR : (0 : ℝ) < q := lt_trans (by norm_num) hqOne
  have hqpos : 0 < q := by exact_mod_cast hqposR
  have hqFour : 4 * sqrt (Fintype.card I) < (q : ℝ) := by
    exact lt_of_le_of_lt (le_trans (le_max_left _ _)
      (le_max_right 1 _)) hq
  have hqEpsilon : sqrt (Fintype.card I) / epsilon < (q : ℝ) := by
    exact lt_of_le_of_lt (le_trans (le_max_right _ _)
      (le_max_right _ _)) hq
  refine ⟨q, hqpos, ?_⟩
  dsimp only
  have hgamma : 0 ≤ (1 : ℝ) / q := by positivity
  have hdelta : 0 ≤ (1 / (q : ℝ)) * sqrt (Fintype.card I) := by positivity
  have hdeltaForm : (1 / (q : ℝ)) * sqrt (Fintype.card I) =
      sqrt (Fintype.card I) / q := by ring
  have hdeltaSmall : (1 / (q : ℝ)) * sqrt (Fintype.card I) ≤ 1 / 4 := by
    rw [hdeltaForm, div_le_iff₀ hqposR]
    nlinarith
  have hdeltaEpsilon :
      (1 / (q : ℝ)) * sqrt (Fintype.card I) ≤ epsilon := by
    rw [hdeltaForm, div_le_iff₀ hqposR]
    have hsqrt : sqrt (Fintype.card I) < (q : ℝ) * epsilon := by
      have := (div_lt_iff₀ hepsilon).mp hqEpsilon
      nlinarith
    linarith
  refine ⟨hgamma, hdelta, hdeltaSmall, hdeltaEpsilon, ?_⟩
  push_cast
  field_simp

/-- The finite edge walk produces an approximate partial colouring at every
positive accuracy. -/
theorem exists_approximate_partialColoring
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : InCube x₀) (hc : ∀ j, 0 ≤ c j)
    (hentropy : (∑ j, exp (-(c j) ^ 2 / 16)) ≤
      (Fintype.card I : ℝ) / 16)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ x : I → ℝ,
      InCube x ∧
        Fintype.card I ≤ 2 * (approximateFixedCoordinates epsilon x).card ∧
        ∀ j, |dot (x - x₀) (v j)| ≤ c j * l2Norm (v j) := by
  obtain ⟨q, hq, hgamma, hdelta, hdeltaSmall, hdeltaEpsilon, htime⟩ :=
    exists_walk_parameters (I := I) epsilon hepsilon
  let gamma : ℝ := 1 / (q : ℝ)
  let delta : ℝ := gamma * sqrt (Fintype.card I)
  let T : ℕ := 5 * q ^ 2
  let xT : WalkSpace I := edgeWalk delta gamma v x₀ c T
  have hgamma' : 0 ≤ gamma := hgamma
  have hdelta' : 0 ≤ delta := hdelta
  have hdeltaSmall' : delta ≤ 1 / 4 := hdeltaSmall
  have hdeltaEpsilon' : delta ≤ epsilon := hdeltaEpsilon
  have htime' : gamma ^ 2 * (T : ℝ) = 5 := htime
  have hhalf : Fintype.card I ≤
      2 * (activeCoordinates delta xT).card := by
    exact edgeWalk_terminal_half delta gamma T v x₀ c hx₀ hc hentropy
      hgamma' rfl hdelta' hdeltaSmall' htime'
  have hxTCube : InCube xT :=
    edgeWalk_inCube delta gamma v x₀ c hx₀ hgamma' rfl T
  have hnormalized : ∀ j,
      |normalizedDiscrepancy (v j) x₀ xT| ≤ c j :=
    edgeWalk_normalizedDiscrepancy_le delta gamma v x₀ c hc hgamma' rfl T
  let x : I → ℝ := fun i ↦ xT i
  refine ⟨x, hxTCube, ?_, ?_⟩
  · have hsubset : activeCoordinates delta xT ⊆
        approximateFixedCoordinates epsilon x := by
      intro i hi
      rw [mem_approximateFixedCoordinates]
      have hi' := mem_activeCoordinates.mp hi
      dsimp only [x]
      linarith
    exact hhalf.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hsubset))
  · intro j
    by_cases hv : l2Norm (v j) = 0
    · rw [dot_eq_zero_of_l2Norm_eq_zero (x - x₀) (v j) hv, hv]
      simp
    · have hvpos : 0 < l2Norm (v j) :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hv)
      have hscale := normalizedDiscrepancy_mul_l2Norm hvpos x₀ xT
      have hnormNonneg : 0 ≤ l2Norm (v j) := Real.sqrt_nonneg _
      change |dot (fun i ↦ xT i - x₀ i) (v j)| ≤ c j * l2Norm (v j)
      rw [← hscale, abs_mul, abs_of_nonneg hnormNonneg]
      exact mul_le_mul_of_nonneg_right (hnormalized j) hnormNonneg

omit [DecidableEq J] in
/-- The unconditional, universe-polymorphic Lovett--Meka partial-colouring
principle used by the Erdős 228 construction. -/
theorem partialColoringPrinciple (I : Type u) (J : Type v)
    [Fintype I] [Fintype J] [DecidableEq I] :
    Erdos228.Discrepancy.PartialColoringPrinciple I J := by
  letI : DecidableEq J := Classical.decEq J
  intro v x₀ c hx₀ hc hentropy
  apply hasPartialColoring_of_approximate v x₀ c
  intro epsilon hepsilon
  exact exists_approximate_partialColoring v x₀ c hx₀ hc hentropy epsilon hepsilon

end EdgeWalk

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228/AnalyticCore.lean` -/

section
/-!
# The concrete centered coefficient assembly for Erdős Problem 228

This file converts three disjoint families of positive frequencies into the
coefficient vector of the centered Littlewood polynomial.  Symmetric pairs
are used for the cosine family and antisymmetric pairs for the two sine
families.  The construction is deliberately independent of the analytic
proofs which produce the three sign sequences.
-/

open scoped BigOperators

noncomputable section

/-! ## A generic centered pairing of sign coefficients -/

/-- Three disjoint sign-coloured families which partition the positive
frequencies `1, ..., 2*n`. -/
structure PairedSignData (n : ℕ) where
  C : Finset ℕ
  Se : Finset ℕ
  So : Finset ℕ
  cover : C ∪ Se ∪ So = Finset.Icc 1 (2 * n)
  disjoint_C_Se : Disjoint C Se
  disjoint_C_So : Disjoint C So
  disjoint_Se_So : Disjoint Se So
  epsC : ℕ → ℝ
  epsE : ℕ → ℝ
  epsO : ℕ → ℝ
  epsC_isSign : ∀ k ∈ C, epsC k = 1 ∨ epsC k = -1
  epsE_isSign : ∀ k ∈ Se, epsE k = 1 ∨ epsE k = -1
  epsO_isSign : ∀ k ∈ So, epsO k = 1 ∨ epsO k = -1

/-- Coefficient at a positive centered frequency. -/
def PairedSignData.positiveCoefficient {n : ℕ} (D : PairedSignData n)
    (k : ℕ) : ℂ :=
  if k ∈ D.C then D.epsC k
  else if k ∈ D.Se then D.epsE k
  else D.epsO k

/-- Coefficient at a negative centered frequency.  The cosine signs are
unchanged and the two sine signs are negated. -/
def PairedSignData.negativeCoefficient {n : ℕ} (D : PairedSignData n)
    (k : ℕ) : ℂ :=
  if k ∈ D.C then D.epsC k
  else if k ∈ D.Se then -D.epsE k
  else -D.epsO k

/-- The coefficient vector obtained after shifting centered exponents
`[-2*n,2*n]` to ordinary exponents `[0,4*n]`. -/
def PairedSignData.coeff {n : ℕ} (D : PairedSignData n) :
    Fin (4 * n + 1) → ℂ := fun j ↦
  if (j : ℕ) < 2 * n then D.negativeCoefficient (2 * n - j)
  else if (j : ℕ) = 2 * n then 1
  else D.positiveCoefficient ((j : ℕ) - 2 * n)

private theorem PairedSignData.disjoint_CSe_So {n : ℕ}
    (D : PairedSignData n) : Disjoint (D.C ∪ D.Se) D.So := by
  rw [Finset.disjoint_left]
  intro k hk hko
  simp only [Finset.mem_union] at hk
  rcases hk with hkc | hke
  · exact (Finset.disjoint_left.mp D.disjoint_C_So) hkc hko
  · exact (Finset.disjoint_left.mp D.disjoint_Se_So) hke hko

private theorem PairedSignData.C_subset {n : ℕ} (D : PairedSignData n) :
    D.C ⊆ Finset.Icc 1 (2 * n) := by
  intro k hk
  rw [← D.cover]
  simp [hk]

private theorem PairedSignData.Se_subset {n : ℕ} (D : PairedSignData n) :
    D.Se ⊆ Finset.Icc 1 (2 * n) := by
  intro k hk
  rw [← D.cover]
  simp [hk]

private theorem PairedSignData.So_subset {n : ℕ} (D : PairedSignData n) :
    D.So ⊆ Finset.Icc 1 (2 * n) := by
  intro k hk
  rw [← D.cover]
  simp [hk]

theorem PairedSignData.coeff_isSign {n : ℕ} (D : PairedSignData n) :
    ∀ j, IsSign (D.coeff j) := by
  intro j
  by_cases hjlt : (j : ℕ) < 2 * n
  · have hk : 2 * n - (j : ℕ) ∈ Finset.Icc 1 (2 * n) := by
      simp only [Finset.mem_Icc]
      omega
    rw [← D.cover] at hk
    simp only [Finset.mem_union] at hk
    simp only [PairedSignData.coeff, if_pos hjlt,
      PairedSignData.negativeCoefficient]
    by_cases hC : 2 * n - (j : ℕ) ∈ D.C
    · rw [if_pos hC]
      rcases D.epsC_isSign _ hC with h | h <;> simp [h, IsSign]
    · rw [if_neg hC]
      by_cases hE : 2 * n - (j : ℕ) ∈ D.Se
      · rw [if_pos hE]
        rcases D.epsE_isSign _ hE with h | h <;> simp [h, IsSign]
      · rw [if_neg hE]
        have hO : 2 * n - (j : ℕ) ∈ D.So := by
          rcases hk with (hC' | hE') | hO
          · exact (hC hC').elim
          · exact (hE hE').elim
          · exact hO
        rcases D.epsO_isSign _ hO with h | h <;> simp [h, IsSign]
  · by_cases hjeq : (j : ℕ) = 2 * n
    · simp [PairedSignData.coeff, hjeq, IsSign]
    · have hjgt : 2 * n < (j : ℕ) := by omega
      have hk : (j : ℕ) - 2 * n ∈ Finset.Icc 1 (2 * n) := by
        simp only [Finset.mem_Icc]
        have hjtop : (j : ℕ) ≤ 4 * n := by omega
        omega
      rw [← D.cover] at hk
      simp only [Finset.mem_union] at hk
      simp only [PairedSignData.coeff, if_neg hjlt, if_neg hjeq,
        PairedSignData.positiveCoefficient]
      by_cases hC : (j : ℕ) - 2 * n ∈ D.C
      · rw [if_pos hC]
        rcases D.epsC_isSign _ hC with h | h <;> simp [h, IsSign]
      · rw [if_neg hC]
        by_cases hE : (j : ℕ) - 2 * n ∈ D.Se
        · rw [if_pos hE]
          rcases D.epsE_isSign _ hE with h | h <;> simp [h, IsSign]
        · rw [if_neg hE]
          have hO : (j : ℕ) - 2 * n ∈ D.So := by
            rcases hk with (hC' | hE') | hO
            · exact (hC hC').elim
            · exact (hE hE').elim
            · exact hO
          rcases D.epsO_isSign _ hO with h | h <;> simp [h, IsSign]

private theorem sum_range_center_sub {n : ℕ} (D : PairedSignData n)
    (z : ℂ) :
    (∑ j ∈ Finset.range (2 * n),
        D.negativeCoefficient (2 * n - j) * z ^ j) =
      ∑ k ∈ Finset.Icc 1 (2 * n),
        D.negativeCoefficient k * z ^ (2 * n - k) := by
  classical
  apply Finset.sum_bij (fun j _ ↦ 2 * n - j)
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_range] at ha hb
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨2 * n - k, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    congr 2
    omega

private theorem sum_range_center_add {n : ℕ} (D : PairedSignData n)
    (z : ℂ) :
    (∑ j ∈ Finset.range (2 * n),
        D.positiveCoefficient (j + 1) * z ^ (2 * n + (j + 1))) =
      ∑ k ∈ Finset.Icc 1 (2 * n),
        D.positiveCoefficient k * z ^ (2 * n + k) := by
  classical
  apply Finset.sum_bij (fun j _ ↦ j + 1)
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨k - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro j hj
    rfl

private theorem PairedSignData.sum_positive_partition {n : ℕ}
    (D : PairedSignData n) (f : ℕ → ℂ) :
    (∑ k ∈ Finset.Icc 1 (2 * n), D.positiveCoefficient k * f k) =
      (∑ k ∈ D.C, (D.epsC k : ℂ) * f k) +
      (∑ k ∈ D.Se, (D.epsE k : ℂ) * f k) +
      ∑ k ∈ D.So, (D.epsO k : ℂ) * f k := by
  classical
  rw [← D.cover, Finset.sum_union D.disjoint_CSe_So,
    Finset.sum_union D.disjoint_C_Se]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro k hk
      simp [PairedSignData.positiveCoefficient, hk]
    · apply Finset.sum_congr rfl
      intro k hk
      have hnotC : k ∉ D.C := fun hC ↦
        (Finset.disjoint_left.mp D.disjoint_C_Se) hC hk
      simp [PairedSignData.positiveCoefficient, hk, hnotC]
  · apply Finset.sum_congr rfl
    intro k hk
    have hnotC : k ∉ D.C := fun hC ↦
      (Finset.disjoint_left.mp D.disjoint_C_So) hC hk
    have hnotE : k ∉ D.Se := fun hE ↦
      (Finset.disjoint_left.mp D.disjoint_Se_So) hE hk
    simp [PairedSignData.positiveCoefficient, hnotC, hnotE]

private theorem PairedSignData.sum_negative_partition {n : ℕ}
    (D : PairedSignData n) (f : ℕ → ℂ) :
    (∑ k ∈ Finset.Icc 1 (2 * n), D.negativeCoefficient k * f k) =
      (∑ k ∈ D.C, (D.epsC k : ℂ) * f k) -
      (∑ k ∈ D.Se, (D.epsE k : ℂ) * f k) -
      ∑ k ∈ D.So, (D.epsO k : ℂ) * f k := by
  classical
  rw [← D.cover, Finset.sum_union D.disjoint_CSe_So,
    Finset.sum_union D.disjoint_C_Se]
  simp only [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro k hk
      simp [PairedSignData.negativeCoefficient, hk]
    · apply Finset.sum_congr rfl
      intro k hk
      have hnotC : k ∉ D.C := fun hC ↦
        (Finset.disjoint_left.mp D.disjoint_C_Se) hC hk
      simp [PairedSignData.negativeCoefficient, hk, hnotC]
  · apply Finset.sum_congr rfl
    intro k hk
    have hnotC : k ∉ D.C := fun hC ↦
      (Finset.disjoint_left.mp D.disjoint_C_So) hC hk
    have hnotE : k ∉ D.Se := fun hE ↦
      (Finset.disjoint_left.mp D.disjoint_Se_So) hE hk
    simp [PairedSignData.negativeCoefficient, hnotC, hnotE]

private theorem sum_center_sub_factor {n : ℕ} (s : Finset ℕ)
    (eps : ℕ → ℝ) (hs : s ⊆ Finset.Icc 1 (2 * n))
    (z : ℂ) (hz : z ≠ 0) :
    (∑ k ∈ s, (eps k : ℂ) * z ^ (2 * n - k)) =
      z ^ (2 * n) * ∑ k ∈ s, (eps k : ℂ) * z⁻¹ ^ k := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ 2 * n := (Finset.mem_Icc.mp (hs hk)).2
  rw [pow_sub₀ z hz hkn, inv_pow]
  ring

private theorem sum_center_add_factor {n : ℕ} (s : Finset ℕ)
    (eps : ℕ → ℝ) (z : ℂ) :
    (∑ k ∈ s, (eps k : ℂ) * z ^ (2 * n + k)) =
      z ^ (2 * n) * ∑ k ∈ s, (eps k : ℂ) * z ^ k := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_add]
  ring

/-- Exact evaluation identity for the shifted centered coefficient vector. -/
theorem PairedSignData.eval_eq {n : ℕ} (D : PairedSignData n)
    (theta : ℝ) :
    (ofCoeffs (4 * n) D.coeff).eval (unitPoint theta) =
      unitPoint theta ^ (2 * n) *
        pairedLaurentValue D.C D.Se D.So D.epsC D.epsE D.epsO theta := by
  classical
  let z := unitPoint theta
  have hz : z ≠ 0 := unitPoint_ne_zero theta
  rw [eval_ofCoeffs]
  change (∑ i : Fin (4 * n + 1), D.coeff i * z ^ (i : ℕ)) = _
  let term : ℕ → ℂ := fun j ↦
    if hj : j < 4 * n + 1 then D.coeff ⟨j, hj⟩ * z ^ j else 0
  have hfin :
      (∑ i : Fin (4 * n + 1), D.coeff i * z ^ (i : ℕ)) =
        ∑ j ∈ Finset.range (4 * n + 1), term j := by
    rw [← Fin.sum_univ_eq_sum_range term (4 * n + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show term (i : ℕ) = D.coeff i * z ^ (i : ℕ) by
      simp only [term, dif_pos i.isLt]]
  rw [hfin]
  rw [show 4 * n + 1 = 2 * n + (1 + 2 * n) by omega,
    Finset.sum_range_add]
  rw [Finset.sum_range_add (fun j ↦
    term (2 * n + j)) 1 (2 * n)]
  simp only [Finset.sum_range_one, Nat.add_zero]
  have hnegative :
      (∑ j ∈ Finset.range (2 * n),
          term j) =
        ∑ k ∈ Finset.Icc 1 (2 * n),
          D.negativeCoefficient k * z ^ (2 * n - k) := by
    rw [← sum_range_center_sub D z]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hjtop : j < 4 * n + 1 := by omega
    rw [show term j = D.coeff ⟨j, hjtop⟩ * z ^ j by
      simp only [term, dif_pos hjtop]]
    simp only [PairedSignData.coeff, if_pos hj]
  have hcenter : term (2 * n) = z ^ (2 * n) := by
    have hjtop : 2 * n < 4 * n + 1 := by omega
    rw [show term (2 * n) = D.coeff ⟨2 * n, hjtop⟩ * z ^ (2 * n) by
      simp only [term, dif_pos hjtop]]
    simp [PairedSignData.coeff]
  have hpositive :
      (∑ j ∈ Finset.range (2 * n),
          term (2 * n + (1 + j))) =
        ∑ k ∈ Finset.Icc 1 (2 * n),
          D.positiveCoefficient k * z ^ (2 * n + k) := by
    rw [← sum_range_center_add D z]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hjtop : 2 * n + (1 + j) < 4 * n + 1 := by omega
    have hne : 2 * n + (1 + j) ≠ 2 * n := by omega
    rw [show term (2 * n + (1 + j)) =
        D.coeff ⟨2 * n + (1 + j), hjtop⟩ * z ^ (2 * n + (1 + j)) by
      simp only [term, dif_pos hjtop]]
    simp only [PairedSignData.coeff, if_neg (by omega : ¬2 * n + (1 + j) < 2 * n),
      if_neg hne]
    congr 2 <;> omega
  rw [hnegative, hcenter, hpositive]
  rw [D.sum_negative_partition (fun k ↦ z ^ (2 * n - k)),
    D.sum_positive_partition (fun k ↦ z ^ (2 * n + k))]
  rw [sum_center_sub_factor D.C D.epsC D.C_subset z hz,
    sum_center_sub_factor D.Se D.epsE D.Se_subset z hz,
    sum_center_sub_factor D.So D.epsO D.So_subset z hz,
    sum_center_add_factor D.C D.epsC z,
    sum_center_add_factor D.Se D.epsE z,
    sum_center_add_factor D.So D.epsO z]
  simp only [pairedLaurentValue, z]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- The generic pairing data gives an actual `CenteredPairedInput` whenever
the three trigonometric components satisfy the final analytic estimates. -/
def PairedSignData.toCenteredPairedInput {n : ℕ} (D : PairedSignData n)
    (dangerous : ℝ → Prop)
    (hcosUpper : ∀ theta, |cosineSum D.C D.epsC theta| ≤ Real.sqrt n)
    (hevenUpper : ∀ theta, |sineSum D.Se D.epsE theta| ≤ 6 * Real.sqrt n)
    (hoddUpper : ∀ theta, |sineSum D.So D.epsO theta| ≤ 2 ^ 10 * Real.sqrt n)
    (hcosLower : ∀ theta, InFundamentalAngle theta → ¬dangerous theta →
      (1 / 2 ^ 160 : ℝ) * Real.sqrt n + 1 ≤
        2 * |cosineSum D.C D.epsC theta|)
    (hoddLower : ∀ theta, InFundamentalAngle theta → dangerous theta →
      10 * Real.sqrt n ≤ |sineSum D.So D.epsO theta|) :
    CenteredPairedInput n where
  coeff := D.coeff
  coeff_isSign := D.coeff_isSign
  cosine := cosineSum D.C D.epsC
  evenSine := sineSum D.Se D.epsE
  oddSine := sineSum D.So D.epsO
  dangerous := dangerous
  eval_eq := fun theta ↦ D.eval_eq theta |>.trans
    (congrArg (unitPoint theta ^ (2 * n) * ·)
      (pairedLaurentValue_eq_assembledValue
        D.C D.Se D.So D.epsC D.epsE D.epsO theta))
  cosine_upper := hcosUpper
  evenSine_upper := hevenUpper
  oddSine_upper := hoddUpper
  cosine_lower_off_dangerous := hcosLower
  oddSine_lower_on_dangerous := hoddLower

/-! ## The exact even/odd frequency partition used by BBMST -/

/-- All positive odd frequencies up to `2*n`. -/
def oddS (n : ℕ) : Finset ℕ :=
  (Finset.range n).image Erdos228.Rounding.oddFrequency

@[simp] theorem mem_oddS {n k : ℕ} :
    k ∈ oddS n ↔ ∃ j < n, k = 2 * j + 1 := by
  simp [oddS, Erdos228.Rounding.oddFrequency, eq_comm]

private theorem evenC_union_evenS {n t : ℕ}
    (hblock : 2 * evenT t + 2 ^ t ≤ n + 1) :
    evenC t ∪ evenS n t =
      (Finset.Icc 1 n).image (fun j ↦ 2 * j) := by
  classical
  ext k
  simp only [Finset.mem_union, mem_evenC, mem_evenS, Finset.mem_image,
    Finset.mem_Icc]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · refine ⟨j, ?_, rfl⟩
      have hjrange := evenCPrime_subset_range hblock hj
      simp only [Finset.mem_range] at hjrange
      have hjpos : 1 ≤ j := by
        rw [mem_evenCPrime] at hj
        rcases hj with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
        · have hT : 0 < evenT t := by simp [evenT]
          omega
        · have hT : 0 < evenT t := by simp [evenT]
          omega
      exact ⟨hjpos, by omega⟩
    · have hj' := (mem_evenSPrime n t j).mp hj
      exact ⟨j, ⟨hj'.1, hj'.2.1⟩, rfl⟩
  · rintro ⟨j, ⟨hjpos, hjn⟩, rfl⟩
    by_cases hjC : j ∈ evenCPrime t
    · exact Or.inl ⟨j, hjC, rfl⟩
    · exact Or.inr ⟨j, (mem_evenSPrime n t j).mpr ⟨hjpos, hjn, hjC⟩, rfl⟩

private theorem evenOdd_cover {n t : ℕ}
    (hblock : 2 * evenT t + 2 ^ t ≤ n + 1) :
    evenC t ∪ evenS n t ∪ oddS n = Finset.Icc 1 (2 * n) := by
  classical
  rw [evenC_union_evenS hblock]
  ext k
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc, mem_oddS]
  constructor
  · rintro (⟨j, ⟨hjpos, hjn⟩, rfl⟩ | ⟨j, hjn, rfl⟩)
    · omega
    · omega
  · intro hk
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' k
    · left
      refine ⟨j, ?_, hj.symm⟩
      omega
    · right
      exact ⟨j, by omega, hj⟩

private theorem evenC_disjoint_oddS (n t : ℕ) :
    Disjoint (evenC t) (oddS n) := by
  rw [Finset.disjoint_left]
  intro k hkC hkO
  rw [mem_evenC] at hkC
  rw [mem_oddS] at hkO
  obtain ⟨a, ha, rfl⟩ := hkC
  obtain ⟨b, hb, hab⟩ := hkO
  omega

private theorem evenS_disjoint_oddS (n t : ℕ) :
    Disjoint (evenS n t) (oddS n) := by
  rw [Finset.disjoint_left]
  intro k hkE hkO
  rw [mem_evenS] at hkE
  rw [mem_oddS] at hkO
  obtain ⟨a, ha, rfl⟩ := hkE
  obtain ⟨b, hb, hab⟩ := hkO
  omega

/-- Real sign attached to an even cosine frequency. -/
def evenCosineCoefficient (t k : ℕ) : ℝ :=
  ((cosineBlockPolynomial t).coeff (k / 2)).re

/-- Real sign attached to a remaining even sine frequency. -/
def evenSineCoefficient (n t u k : ℕ) : ℝ :=
  ((evenRemainderPolynomial n t u).coeff (k / 2)).re

/-- A sign sequence on odd-frequency indices, viewed as a function of the
actual odd frequency. -/
def oddSineCoefficient (eps : ℕ → ℝ) (k : ℕ) : ℝ :=
  eps (k / 2)

private theorem evenCosineCoefficient_isSign {t k : ℕ} (hk : k ∈ evenC t) :
    evenCosineCoefficient t k = 1 ∨ evenCosineCoefficient t k = -1 := by
  rw [mem_evenC] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hdiv : 2 * j / 2 = j := by omega
  simp only [evenCosineCoefficient, hdiv]
  rw [mem_evenCPrime] at hj
  rcases hj with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · rw [coeff_cosineBlockPolynomial_first t a ha]
    rcases coeff_rudinShapiroP_eq_one_or_neg_one ha with h | h <;>
      simp [h]
  · rw [coeff_cosineBlockPolynomial_second t a ha]
    rcases coeff_rudinShapiroQ_eq_one_or_neg_one ha with h | h <;>
      simp [h]

private theorem evenSineCoefficient_isSign {n t u k : ℕ}
    (hprefix : n + 1 ≤ 2 ^ u) (hk : k ∈ evenS n t) :
    evenSineCoefficient n t u k = 1 ∨ evenSineCoefficient n t u k = -1 := by
  rw [mem_evenS] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hdiv : 2 * j / 2 = j := by omega
  simp only [evenSineCoefficient, hdiv]
  rcases coeff_evenRemainderPolynomial_sign_of_mem_evenSPrime hprefix hj with h | h <;>
    simp [h]

private theorem oddSineCoefficient_isSign {n k : ℕ} {eps : ℕ → ℝ}
    (heps : ∀ j, eps j = 1 ∨ eps j = -1) (hk : k ∈ oddS n) :
    oddSineCoefficient eps k = 1 ∨ oddSineCoefficient eps k = -1 := by
  rw [mem_oddS] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hdiv : (2 * j + 1) / 2 = j := by omega
  simpa [oddSineCoefficient, hdiv] using heps j

/-- The exact three-family sign data obtained from the even
Rudin--Shapiro construction and an odd sign sequence. -/
def concretePairedSignData (n t u : ℕ) (eps : ℕ → ℝ)
    (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hprefix : n + 1 ≤ 2 ^ u)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1) : PairedSignData n where
  C := evenC t
  Se := evenS n t
  So := oddS n
  cover := evenOdd_cover hblock
  disjoint_C_Se := evenC_disjoint_evenS n t
  disjoint_C_So := evenC_disjoint_oddS n t
  disjoint_Se_So := evenS_disjoint_oddS n t
  epsC := evenCosineCoefficient t
  epsE := evenSineCoefficient n t u
  epsO := oddSineCoefficient eps
  epsC_isSign := fun _ hk ↦ evenCosineCoefficient_isSign hk
  epsE_isSign := fun _ hk ↦ evenSineCoefficient_isSign hprefix hk
  epsO_isSign := fun _ hk ↦ oddSineCoefficient_isSign heps hk

/-! ## Identification of the three paired sums -/

private theorem eval_unitPoint_re_eq_cosine_support (p : Polynomial ℂ)
    (hreal : ∀ k ∈ p.support, (p.coeff k).im = 0) (theta : ℝ) :
    (p.eval (unitPoint theta)).re =
      ∑ k ∈ p.support, (p.coeff k).re * Real.cos (k * theta) := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  change Complex.reLm (∑ k ∈ p.support, p.coeff k * unitPoint theta ^ k) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hre : (unitPoint theta ^ k).re = Real.cos (k * theta) := by
    have h := congrArg Complex.re (Erdos228.unitPoint_pow theta k)
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, mul_one, add_zero] using h
  change (p.coeff k * unitPoint theta ^ k).re = _
  rw [Complex.mul_re, hreal k hk, zero_mul, sub_zero, hre]

private theorem eval_unitPoint_im_eq_sine_support (p : Polynomial ℂ)
    (hreal : ∀ k ∈ p.support, (p.coeff k).im = 0) (theta : ℝ) :
    (p.eval (unitPoint theta)).im =
      ∑ k ∈ p.support, (p.coeff k).re * Real.sin (k * theta) := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  change Complex.imLm (∑ k ∈ p.support, p.coeff k * unitPoint theta ^ k) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have him : (unitPoint theta ^ k).im = Real.sin (k * theta) := by
    have h := congrArg Complex.im (Erdos228.unitPoint_pow theta k)
    simpa only [Complex.add_im, Complex.ofReal_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      mul_one, add_zero, zero_add] using h
  change (p.coeff k * unitPoint theta ^ k).im = _
  rw [Complex.mul_im, hreal k hk, zero_mul, add_zero, him]

private theorem cosineBlock_coeff_im_eq_zero {t k : ℕ}
    (hk : k ∈ (cosineBlockPolynomial t).support) :
    ((cosineBlockPolynomial t).coeff k).im = 0 := by
  rw [support_cosineBlockPolynomial] at hk
  rw [mem_evenCPrime] at hk
  rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [coeff_cosineBlockPolynomial_first t j hj]
    rcases coeff_rudinShapiroP_eq_one_or_neg_one hj with h | h <;> simp [h]
  · rw [coeff_cosineBlockPolynomial_second t j hj]
    rcases coeff_rudinShapiroQ_eq_one_or_neg_one hj with h | h <;> simp [h]

theorem cosineSum_evenC_eq_evenCosine (t : ℕ) (theta : ℝ) :
    cosineSum (evenC t) (evenCosineCoefficient t) theta =
      evenCosine t theta := by
  classical
  rw [cosineSum, evenC, Finset.sum_image]
  · rw [evenCosine]
    rw [eval_unitPoint_re_eq_cosine_support
      (cosineBlockPolynomial t) (fun k hk ↦ cosineBlock_coeff_im_eq_zero hk)]
    rw [support_cosineBlockPolynomial]
    apply Finset.sum_congr rfl
    intro j hj
    have hdiv : 2 * j / 2 = j := by omega
    simp only [evenCosineCoefficient, hdiv]
    congr 2
    push_cast
    ring
  · intro a ha b hb hab
    dsimp only at hab
    omega

private theorem coeff_evenRemainderPolynomial_zero {n t u : ℕ} :
    (evenRemainderPolynomial n t u).coeff 0 = 1 := by
  have hzero : 0 ∉ evenCPrime t := by
    rw [mem_evenCPrime]
    push Not
    constructor
    · intro j hj
      have hT : 0 < evenT t := by simp [evenT]
      omega
    · intro j hj
      have hT : 0 < evenT t := by simp [evenT]
      omega
  rw [evenRemainderPolynomial, Polynomial.coeff_sub,
    coeff_polynomialPrefix, if_pos (by omega),
    coeff_deletedEvenBlockPolynomial_eq_zero_of_outside t 0 hzero, sub_zero]
  have hstable := coeff_rudinShapiroP_stable
    (a := 0) (b := u) (k := 0) (Nat.zero_le u) (by norm_num)
  simpa [rudinShapiroP] using hstable

private theorem support_evenRemainderPolynomial {n t u : ℕ}
    (hu : t + 12 ≤ u) (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hprefix : n + 1 ≤ 2 ^ u) :
    (evenRemainderPolynomial n t u).support =
      insert 0 (evenSPrime n t) := by
  classical
  ext k
  simp only [Polynomial.mem_support_iff, Finset.mem_insert, ne_eq]
  constructor
  · intro hk
    by_cases hk0 : k = 0
    · exact Or.inl hk0
    · right
      rw [mem_evenSPrime]
      have hklt : k < n + 1 := by
        by_contra hnot
        have hlarge : n + 1 ≤ k := Nat.le_of_not_gt hnot
        have hkC : k ∉ evenCPrime t := by
          intro hkC
          have hkrange := evenCPrime_subset_range hblock hkC
          simp only [Finset.mem_range] at hkrange
          omega
        apply hk
        rw [evenRemainderPolynomial, Polynomial.coeff_sub,
          coeff_polynomialPrefix, if_neg (by omega),
          coeff_deletedEvenBlockPolynomial_eq_zero_of_outside t k hkC,
          sub_zero]
      refine ⟨by omega, by omega, ?_⟩
      intro hkC
      exact hk (coeff_evenRemainderPolynomial_eq_zero_on_CPrime hu hblock hkC)
  · rintro (rfl | hk)
    · rw [coeff_evenRemainderPolynomial_zero]
      norm_num
    · rcases coeff_evenRemainderPolynomial_sign_of_mem_evenSPrime hprefix hk with h | h <;>
        rw [h] <;> norm_num

private theorem evenRemainder_coeff_im_eq_zero {n t u k : ℕ}
    (hu : t + 12 ≤ u) (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hprefix : n + 1 ≤ 2 ^ u)
    (hk : k ∈ (evenRemainderPolynomial n t u).support) :
    ((evenRemainderPolynomial n t u).coeff k).im = 0 := by
  rw [support_evenRemainderPolynomial hu hblock hprefix] at hk
  simp only [Finset.mem_insert] at hk
  rcases hk with rfl | hk
  · simp [coeff_evenRemainderPolynomial_zero]
  · rcases coeff_evenRemainderPolynomial_sign_of_mem_evenSPrime hprefix hk with h | h <;>
      simp [h]

theorem sineSum_evenS_eq_evenSine (n t u : ℕ)
    (hu : t + 12 ≤ u) (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hprefix : n + 1 ≤ 2 ^ u) (theta : ℝ) :
    sineSum (evenS n t) (evenSineCoefficient n t u) theta =
      evenSine n t u theta := by
  classical
  rw [sineSum, evenS, Finset.sum_image]
  · rw [evenSine]
    rw [eval_unitPoint_im_eq_sine_support
      (evenRemainderPolynomial n t u)
      (fun k hk ↦ evenRemainder_coeff_im_eq_zero hu hblock hprefix hk)]
    rw [support_evenRemainderPolynomial hu hblock hprefix]
    rw [Finset.sum_insert]
    · simp only [Nat.cast_zero, zero_mul, Real.sin_zero, mul_zero, zero_add]
      apply Finset.sum_congr rfl
      intro j hj
      have hdiv : 2 * j / 2 = j := by omega
      simp only [evenSineCoefficient, hdiv]
      congr 2
      push_cast
      ring
    · simp [mem_evenSPrime]
  · intro a ha b hb hab
    dsimp only at hab
    omega

theorem sineSum_oddS_eq_oddSineSum (n : ℕ) (eps : ℕ → ℝ) (theta : ℝ) :
    sineSum (oddS n) (oddSineCoefficient eps) theta =
      Erdos228.Rounding.oddSineSum n eps theta := by
  classical
  rw [sineSum, oddS, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j hj
    have hdiv : (2 * j + 1) / 2 = j := by omega
    simp [oddSineCoefficient, hdiv, Erdos228.Rounding.oddFrequency]
  · intro a ha b hb hab
    simp only [Erdos228.Rounding.oddFrequency] at hab
    omega

/-! ## Concrete analytic components -/

private theorem exists_oddSine_of_intervalColoring {n : ℕ} (hn : 0 < n)
    (F : Erdos228.OddSine.SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ)
    (htarget : ∀ j < n, |Erdos228.OddSine.fourierTarget F alpha j| ≤ 1)
    (hkernel : Erdos228.OddSine.KernelCertificate F alpha)
    {G : Type} [Fintype G]
    (setup : Erdos228.OddSine.RoundingSetup n G) :
    ∃ eps : ℕ → ℝ, (∀ j, eps j = 1 ∨ eps j = -1) ∧
      (∀ theta, Erdos228.OddSine.IsDangerous F theta →
        10 * Real.sqrt n < |Erdos228.Rounding.oddSineSum n eps theta|) ∧
      (∀ theta, |Erdos228.Rounding.oddSineSum n eps theta| ≤
        2 ^ 10 * Real.sqrt n) := by
  classical
  obtain ⟨eps, heps, hround⟩ := Erdos228.OddSine.exists_rounding hn setup
    (Erdos228.OddSine.fourierTarget F alpha) htarget
    (fun I _ _ ↦ Erdos228.EdgeWalk.partialColoringPrinciple I (G × Fin n))
  obtain ⟨hkernelLower, hkernelUpper⟩ :=
    Erdos228.OddSine.targetSine_kernel_bounds hn F alpha hkernel
  refine ⟨eps, heps, ?_, ?_⟩
  · intro theta htheta
    have htri : |Erdos228.OddSine.targetSine F alpha theta| ≤
        |Erdos228.Rounding.oddSineSum n eps theta| +
          |Erdos228.Rounding.oddSineSum n eps theta -
            Erdos228.OddSine.targetSine F alpha theta| := by
      calc
        |Erdos228.OddSine.targetSine F alpha theta| =
            |Erdos228.Rounding.oddSineSum n eps theta -
              (Erdos228.Rounding.oddSineSum n eps theta -
                Erdos228.OddSine.targetSine F alpha theta)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    have hlower := hkernelLower theta htheta
    have herror := hround theta
    change |Erdos228.Rounding.oddSineSum n eps theta -
      Erdos228.OddSine.targetSine F alpha theta| ≤ 72 * Real.sqrt n at herror
    rw [Erdos228.OddSine.K_eq] at hlower
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith [Real.sqrt_pos.2 hnR]
  · intro theta
    have htri := abs_add_le (Erdos228.OddSine.targetSine F alpha theta)
      (Erdos228.Rounding.oddSineSum n eps theta -
        Erdos228.OddSine.targetSine F alpha theta)
    have heq : Erdos228.OddSine.targetSine F alpha theta +
        (Erdos228.Rounding.oddSineSum n eps theta -
          Erdos228.OddSine.targetSine F alpha theta) =
          Erdos228.Rounding.oddSineSum n eps theta := by ring
    rw [heq] at htri
    have hu := hkernelUpper theta
    have he := hround theta
    change |Erdos228.Rounding.oddSineSum n eps theta -
      Erdos228.OddSine.targetSine F alpha theta| ≤ 72 * Real.sqrt n at he
    rw [Erdos228.OddSine.K_eq] at hu
    norm_num at ⊢
    nlinarith [Real.sqrt_nonneg n]

/-- The two discrepancy invocations and the explicit rounding mesh reduce the
odd-sine construction to its concrete kernel certificate. -/
theorem exists_concrete_oddSine {n : ℕ} (hn : 0 < n)
    (F : Erdos228.OddSine.SuitableIntervalFamily n) {gamma : ℝ}
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (F.base.card : ℝ) ≤ gamma * n)
    (hkernel : ∀ alpha : (↑F.base : Type) → ℝ,
      Erdos228.Discrepancy.IsSign alpha →
        Erdos228.OddSine.KernelCertificate F alpha) :
    ∃ eps : ℕ → ℝ, (∀ j, eps j = 1 ∨ eps j = -1) ∧
      (∀ theta, Erdos228.OddSine.IsDangerous F theta →
        10 * Real.sqrt n < |Erdos228.Rounding.oddSineSum n eps theta|) ∧
      (∀ theta, |Erdos228.Rounding.oddSineSum n eps theta| ≤
        2 ^ 10 * Real.sqrt n) := by
  classical
  obtain ⟨alpha, halpha, htarget⟩ :
      ∃ alpha : (↑F.base : Type) → ℝ,
        Erdos228.Discrepancy.IsSign alpha ∧
          ∀ j < n, |Erdos228.OddSine.fourierTarget F alpha j| ≤ 1 := by
    by_cases hbase : F.base.card = 0
    · exact Erdos228.OddSine.exists_intervalColoring_of_base_card_eq_zero F hbase
    · have hbasePos : 0 < F.base.card := Nat.pos_of_ne_zero hbase
      have hadmissible := Erdos228.OddSine.firstColoringAdmissible_of_card_le
        hn F hgamma hbasePos hcard
      exact Erdos228.OddSine.exists_intervalColoring F
        (fun _ ↦ Erdos228.OddSine.firstColoringParameter n F.base.card)
        hadmissible
        (fun I _ _ ↦ Erdos228.EdgeWalk.partialColoringPrinciple I (Fin n))
  obtain ⟨setup⟩ := Erdos228.OddSine.exists_roundingSetup hn
  exact exists_oddSine_of_intervalColoring hn F alpha htarget
    (hkernel alpha halpha) setup

private theorem nat_succ_le_two_pow (m : ℕ) : m + 1 ≤ 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [pow_succ]
      omega

private theorem cosineDelta_gt_two_pow_neg_160 {gamma : ℝ}
    (hgammaLower : (1 / 2 ^ 43 : ℝ) < gamma) :
    (1 / 2 ^ 160 : ℝ) < Erdos228.CosineConstruction.cosineDelta gamma := by
  have hgamma : 0 < gamma := by
    exact lt_trans (by positivity : (0 : ℝ) < 1 / 2 ^ 43) hgammaLower
  have hcube : (1 / 2 ^ 43 : ℝ) ^ 3 < gamma ^ 3 := by
    gcongr
  have hsmallSq : (1 / 2 ^ 22 : ℝ) ^ 2 < gamma := by
    have : (1 / 2 ^ 22 : ℝ) ^ 2 < (1 / 2 ^ 43 : ℝ) := by norm_num
    exact this.trans hgammaLower
  have hsqrtSq := Real.sq_sqrt hgamma.le
  have hsqrt : (1 / 2 ^ 22 : ℝ) < Real.sqrt gamma := by
    nlinarith [Real.sqrt_nonneg gamma]
  rw [Erdos228.CosineConstruction.cosineDelta]
  calc
    (1 / 2 ^ 160 : ℝ) < (1 / 2 ^ 159 : ℝ) := by norm_num
    _ = (1 / 2 ^ 8 : ℝ) * (1 / 2 ^ 43 : ℝ) ^ 3 * (1 / 2 ^ 22 : ℝ) := by
      norm_num
    _ < (1 / 2 ^ 8 : ℝ) * gamma ^ 3 * Real.sqrt gamma := by
      gcongr

/-- Assemble one centered input from the concrete cosine package and the
concrete odd-kernel certificate.  `habsorb` is the eventual numerical
condition which absorbs the central coefficient in the lower bound. -/
theorem exists_centeredPairedInput_of_components
    {n t : ℕ} {gamma : ℝ}
    (hparam : Erdos228.CosineConstruction.Parameters n t gamma)
    (F : Erdos228.OddSine.SuitableIntervalFamily n)
    (hcard : (F.base.card : ℝ) ≤ gamma * n)
    (hcosUpper : ∀ theta, |evenCosine t theta| ≤ Real.sqrt n)
    (hcosLower : ∀ theta, InFundamentalAngle theta →
      ¬Erdos228.OddSine.IsDangerous F theta →
      Erdos228.CosineConstruction.cosineDelta gamma * Real.sqrt n ≤
        |evenCosine t theta|)
    (hkernel : ∀ alpha : (↑F.base : Type) → ℝ,
      Erdos228.Discrepancy.IsSign alpha →
        Erdos228.OddSine.KernelCertificate F alpha)
    (habsorb : 1 ≤ (1 / 2 ^ 160 : ℝ) * Real.sqrt n) :
    Nonempty (CenteredPairedInput n) := by
  have heven := hparam.toEvenParameters
  have hu : t + 12 ≤ n := by
    have ht : t + 12 ≤ 2 ^ (t + 11) := by
      simpa only [Nat.reduceAdd] using nat_succ_le_two_pow (t + 11)
    exact ht.trans heven.pow_t_add_eleven_le_n
  have hprefix : n + 1 ≤ 2 ^ n := nat_succ_le_two_pow n
  obtain ⟨eps, heps, hoddLower, hoddUpper⟩ :=
    exists_concrete_oddSine hparam.n_pos F hparam.gamma_upper hcard hkernel
  let D := concretePairedSignData n t n eps heven.blocks_fit hprefix heps
  refine ⟨D.toCenteredPairedInput (Erdos228.OddSine.IsDangerous F) ?_ ?_ ?_ ?_ ?_⟩
  · intro theta
    rw [show cosineSum D.C D.epsC theta = evenCosine t theta by
      exact cosineSum_evenC_eq_evenCosine t theta]
    exact hcosUpper theta
  · intro theta
    rw [show sineSum D.Se D.epsE theta = evenSine n t n theta by
      exact sineSum_evenS_eq_evenSine n t n hu heven.blocks_fit hprefix theta]
    exact abs_evenSine_le_six_sqrt_of_parameters heven hprefix theta
  · intro theta
    rw [show sineSum D.So D.epsO theta =
        Erdos228.Rounding.oddSineSum n eps theta by
      exact sineSum_oddS_eq_oddSineSum n eps theta]
    exact hoddUpper theta
  · intro theta htheta hsafe
    rw [show cosineSum D.C D.epsC theta = evenCosine t theta by
      exact cosineSum_evenC_eq_evenCosine t theta]
    have hlower := hcosLower theta htheta hsafe
    have hdelta := cosineDelta_gt_two_pow_neg_160 hparam.gamma_lower
    have hsqrt : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    nlinarith
  · intro theta _htheta hdanger
    rw [show sineSum D.So D.epsO theta =
        Erdos228.Rounding.oddSineSum n eps theta by
      exact sineSum_oddS_eq_oddSineSum n eps theta]
    exact (hoddLower theta hdanger).le

private theorem eventually_absorb_one :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 ≤ (1 / 2 ^ 160 : ℝ) * Real.sqrt n := by
  have hsqrt : Filter.Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscaled : Filter.Tendsto
      (fun n : ℕ ↦ (1 / 2 ^ 160 : ℝ) * Real.sqrt n)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hsqrt
  exact hscaled (Filter.eventually_ge_atTop 1)

/-- The cosine construction, the two concrete discrepancy colorings, and the
odd-kernel certificate produce centered Littlewood inputs at every
sufficiently large scale. -/
theorem eventuallyCenteredPaired : EventuallyCenteredPaired := by
  rw [EventuallyCenteredPaired]
  filter_upwards [Erdos228.CosineConstruction.eventually_exists_cosinePackage,
    Filter.eventually_ge_atTop 4096, eventually_absorb_one]
    with n hpackage hn habsorb
  obtain ⟨P⟩ := hpackage
  exact exists_centeredPairedInput_of_components P.parameters P.family
    P.base_card P.upper P.lower
    (Erdos228.OddKernelCertificate.kernelCertificate hn P.family) habsorb

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos228.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 228.
https://www.erdosproblems.com/forum/thread/228

Informal authors:
- Paul Balister
- Béla Bollobás
- Robert Morris
- Julian Sahasrabudhe
- Marius Tiba

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos228.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/228.lean
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Erdős Problem 228

Balister, Bollobás, Morris, Sahasrabudhe, and Tiba proved that Littlewood
polynomials exist whose modulus is bounded above and below by absolute
multiples of the square root of their degree, uniformly on the unit circle.

The detailed mathematical reconstruction and the correspondence between its
lemmas and this development are in `tex/228.tex`.
-/

/-- The affirmative resolution of Erdős Problem 228. -/
theorem erdos_228 :
    ∃ (c₁ : ℝ) (c₂ : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    ∃ p : Polynomial ℂ, p.degree = n ∧
    (∀ i ≤ n, p.coeff i = 1 ∨ p.coeff i = -1) ∧
    ∀ z : ℂ, ‖z‖ = 1 →
    (√n < c₁ * ‖p.eval z‖ ∧ ‖p.eval z‖ < c₂ * √n) := by
  exact target_of_eventually_centered eventuallyCenteredPaired

end

#print axioms erdos_228
-- 'Erdos228.erdos_228' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos228
