import Mathlib

set_option linter.style.longLine false
set_option linter.flexible false

/-
  Erdős Problem 1141 - self-contained single-file proof.

  Inlined from 139 upstream modules: plby/lean-proofs (Lean 4.33.0) and
  frenzymath/FormalPantheon `BoundedGaps` (written for Lean 4.32.0).  Modules are
  concatenated in dependency order, each wrapped in its own `section` with any
  end-of-file scopes closed explicitly.  The
  `backward.isDefEq.respectTransparency.types false` option set below is the same
  4.32-compatibility option Mathlib itself uses for these `ArithmeticFunction`
  proofs; it is what lets the BoundedGaps half build under 4.33.
-/

namespace Erdos1141

set_option backward.isDefEq.respectTransparency.types false

/-! ### Upstream module `ErdosProblems/Erdos1141/QuadraticCoefficients.lean` -/

section

/-!
# Nonnegative divisor coefficients of quadratic characters

For a quadratic character `χ`, the coefficients of `ζ(s) L(s, χ)` are
nonnegative.  This module records their local factors in a real-valued form
suited to finite Euler products and Rankin's inequality.
-/

namespace Pollack17

open scoped BigOperators ComplexOrder
open ArithmeticFunction

variable {m : ℕ}

/-- The divisor coefficient `∑ d ∣ n, χ(d)`, regarded as a real number. -/
noncomputable def divisorCoefficient (χ : DirichletCharacter ℂ m) (n : ℕ) : ℝ :=
  (χ.zetaMul n).re

theorem divisorCoefficient_nonneg (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) (n : ℕ) :
    0 ≤ divisorCoefficient χ n :=
  (Complex.nonneg_iff.mp (χ.zetaMul_nonneg hχ.sq_eq_one n)).1

theorem ofReal_divisorCoefficient (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) (n : ℕ) :
    (divisorCoefficient χ n : ℂ) = χ.zetaMul n := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp (χ.zetaMul_nonneg hχ.sq_eq_one n)).2


@[simp] theorem divisorCoefficient_one (χ : DirichletCharacter ℂ m) :
    divisorCoefficient χ 1 = 1 := by
  simp [divisorCoefficient, χ.isMultiplicative_zetaMul.map_one]

theorem divisorCoefficient_mul (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) {a b : ℕ} (hab : a.Coprime b) :
    divisorCoefficient χ (a * b) = divisorCoefficient χ a * divisorCoefficient χ b := by
  apply Complex.ofReal_injective
  push_cast
  rw [ofReal_divisorCoefficient χ hχ, ofReal_divisorCoefficient χ hχ,
    ofReal_divisorCoefficient χ hχ]
  exact χ.isMultiplicative_zetaMul.map_mul_of_coprime hab

theorem zetaMul_prime_pow_eq_sum (χ : DirichletCharacter ℂ m)
    {p : ℕ} (hp : p.Prime) (e : ℕ) :
    χ.zetaMul (p ^ e) = ∑ i ∈ Finset.range (e + 1), χ (p : ZMod m) ^ i := by
  calc
    χ.zetaMul (p ^ e) =
        ∑ d ∈ (p ^ e).divisors, toArithmeticFunction (χ ·) d :=
      coe_zeta_mul_apply (f := toArithmeticFunction (χ ·))
    _ = _ := by
      simp only [toArithmeticFunction, coe_mk, Nat.sum_divisors_prime_pow hp,
    pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
    Nat.cast_pow, map_pow]

theorem divisorCoefficient_prime_pow_of_eq_one (χ : DirichletCharacter ℂ m)
    {p : ℕ} (hp : p.Prime) (h : χ (p : ZMod m) = 1) (e : ℕ) :
    divisorCoefficient χ (p ^ e) = e + 1 := by
  simp [divisorCoefficient, zetaMul_prime_pow_eq_sum χ hp, h]

theorem divisorCoefficient_prime_pow_of_eq_zero (χ : DirichletCharacter ℂ m)
    {p : ℕ} (hp : p.Prime) (h : χ (p : ZMod m) = 0) (e : ℕ) :
    divisorCoefficient χ (p ^ e) = 1 := by
  simp [divisorCoefficient, zetaMul_prime_pow_eq_sum χ hp, h]

theorem divisorCoefficient_prime_pow_of_eq_neg_one (χ : DirichletCharacter ℂ m)
    {p : ℕ} (hp : p.Prime) (h : χ (p : ZMod m) = -1) (e : ℕ) :
    divisorCoefficient χ (p ^ e) = if Even e then 1 else 0 := by
  rw [divisorCoefficient, zetaMul_prime_pow_eq_sum χ hp, h, neg_one_geom_sum]
  by_cases he : Even e
  · simp [he, Nat.even_add_one]
  · simp [he, Nat.even_add_one]

theorem divisorCoefficient_prime_pow_le (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    divisorCoefficient χ (p ^ e) ≤ e + 1 := by
  rcases hχ (p : ZMod m) with h | h | h
  · rw [divisorCoefficient_prime_pow_of_eq_zero χ hp h]
    linarith [Nat.cast_nonneg (α := ℝ) e]
  · exact (divisorCoefficient_prime_pow_of_eq_one χ hp h e).le
  · rw [divisorCoefficient_prime_pow_of_eq_neg_one χ hp h]
    split_ifs <;> linarith [Nat.cast_nonneg (α := ℝ) e]

theorem hasSum_succ_mul_geometric {u : ℝ} (hu : ‖u‖ < 1) :
    HasSum (fun e : ℕ => (e + 1 : ℝ) * u ^ e) ((1 - u)⁻¹ ^ 2) := by
  simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one,
    one_div, inv_pow] using hasSum_choose_mul_geometric_of_norm_lt_one 1 hu

theorem summable_divisorCoefficient_prime_pow (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) {p : ℕ} (hp : p.Prime)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Summable (fun e : ℕ => divisorCoefficient χ (p ^ e) * u ^ e) := by
  have hu : ‖u‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hu0]
  exact Summable.of_nonneg_of_le
    (fun e => mul_nonneg (divisorCoefficient_nonneg χ hχ _) (pow_nonneg hu0 _))
    (fun e => mul_le_mul_of_nonneg_right
      (divisorCoefficient_prime_pow_le χ hχ hp e) (pow_nonneg hu0 _))
    (hasSum_succ_mul_geometric hu).summable

theorem local_divisorCoefficient_sum_le (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) {p : ℕ} (hp : p.Prime)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (∑' e : ℕ, divisorCoefficient χ (p ^ e) * u ^ e) ≤ (1 - u)⁻¹ ^ 2 := by
  have hu : ‖u‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hu0]
  exact (Summable.tsum_le_tsum
    (fun e => mul_le_mul_of_nonneg_right
      (divisorCoefficient_prime_pow_le χ hχ hp e) (pow_nonneg hu0 _))
    (summable_divisorCoefficient_prime_pow χ hχ hp hu0 hu1)
    (hasSum_succ_mul_geometric hu).summable).trans_eq
      (hasSum_succ_mul_geometric hu).tsum_eq

theorem hasSum_divisorCoefficient_of_neg_one (χ : DirichletCharacter ℂ m)
    {p : ℕ} (hp : p.Prime) (h : χ (p : ZMod m) = -1)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    HasSum (fun e : ℕ => divisorCoefficient χ (p ^ e) * u ^ e)
      (1 - u ^ 2)⁻¹ := by
  have hu : ‖u‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hu0]
  have hnu : ‖-u‖ < 1 := by simpa only [norm_neg] using hu
  have hs := ((hasSum_geometric_of_norm_lt_one hu).add
    (hasSum_geometric_of_norm_lt_one hnu)).div_const 2
  have hterm (e : ℕ) :
      divisorCoefficient χ (p ^ e) * u ^ e = (u ^ e + (-u) ^ e) / 2 := by
    rw [divisorCoefficient_prime_pow_of_eq_neg_one χ hp h, neg_pow,
      neg_one_pow_eq_ite]
    split_ifs <;> ring
  have hvalue : ((1 - u)⁻¹ + (1 - -u)⁻¹) / 2 = (1 - u ^ 2)⁻¹ := by
    have hminus : 1 - u ≠ 0 := ne_of_gt (sub_pos.mpr hu1)
    have hplus : 1 + u ≠ 0 := ne_of_gt (by linarith)
    have hsquare : 1 - u ^ 2 ≠ 0 := by
      have : 0 < (1 - u) * (1 + u) := mul_pos (sub_pos.mpr hu1) (by linarith)
      nlinarith
    rw [sub_neg_eq_add]
    field_simp [hminus, hplus, hsquare]
    ring
  simpa only [← hterm, hvalue] using hs

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessEnergyArithmetic.lean` -/

section

/-!
# Elementary collision estimates for Burgess averaging

The interval-collision and harmonic overcount arguments are extracted from
`Erdos587.NVDevelopment`. They are independent of its fixed fourth-moment
estimate and apply to every modulus with coprime denominators.
-/

namespace Pollack17.Burgess

open scoped BigOperators

lemma sum_Icc_inv_natCast_le_one_add_log (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, ((r : ℝ)⁻¹)) ≤ 1 + Real.log n := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast] using harmonic_le_one_add_log n

/-- Scaled harmonic estimate in the exact form of the nonzero-residue term in
the quadratic Weyl bound. -/
lemma sum_Icc_natCast_div_le (q n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, (q : ℝ) / r) ≤
      q * (1 + Real.log n) := by
  simp_rw [div_eq_mul_inv]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_Icc_inv_natCast_le_one_add_log n)
    (Nat.cast_nonneg q)

lemma card_le_div_add_one_of_pairwise_modEq {s : Finset ℕ} {X h : ℕ}
    (hsX : s ⊆ Finset.Icc 1 X) (_hh : 0 < h)
    (hmod : ∀ a ∈ s, ∀ b ∈ s, a ≡ b [MOD h]) :
    s.card ≤ X / h + 1 := by
  let f : ℕ → ℕ := fun a ↦ a / h
  have hinj : Set.InjOn f s := by
    intro a ha b hb hab
    have hrem : a % h = b % h := hmod a ha b hb
    have hda : h * (a / h) + a % h = a := Nat.div_add_mod a h
    have hdb : h * (b / h) + b % h = b := Nat.div_add_mod b h
    dsimp [f] at hab
    calc
      a = h * (a / h) + a % h := hda.symm
      _ = h * (b / h) + b % h := by rw [hab, hrem]
      _ = b := hdb
  have himage : s.image f ⊆ Finset.range (X / h + 1) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [Finset.mem_range]
    have haX : a ≤ X := (Finset.mem_Icc.mp (hsX ha)).2
    exact Nat.lt_succ_of_le (Nat.div_le_div_right haX)
  calc
    s.card = (s.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (X / h + 1)).card := Finset.card_le_card himage
    _ = X / h + 1 := Finset.card_range _

lemma card_le_div_add_one_of_fst_pairwise_modEq
    {s : Finset (ℕ × ℕ)} {H a : ℕ}
    (hsH : ∀ z ∈ s, z.1 < H) (ha : 0 < a)
    (hinj : Set.InjOn (fun z : ℕ × ℕ ↦ z.1) s)
    (hmod : ∀ z ∈ s, ∀ w ∈ s, z.1 ≡ w.1 [MOD a]) :
    s.card ≤ H / a + 1 := by
  let f : ℕ × ℕ → ℕ := fun z ↦ z.1 + 1
  have hfinj : Set.InjOn f s := by
    intro z hz w hw hzw
    apply hinj hz hw
    change z.1 + 1 = w.1 + 1 at hzw
    exact Nat.add_right_cancel hzw
  have hcard : s.card = (s.image f).card :=
    (Finset.card_image_of_injOn hfinj).symm
  rw [hcard]
  apply card_le_div_add_one_of_pairwise_modEq
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    simp only [Finset.mem_Icc]
    exact ⟨Nat.succ_pos _, Nat.succ_le_iff.mpr (hsH z hz)⟩
  · exact ha
  · intro x hx y hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact (hmod z hz w hw).add_right 1

/-- Pairs of interval positions which give the same quotient after the two
fixed Burgess denominators are cross-multiplied modulo `p`. -/
def burgessIntervalCollision (p M H u₁ u₂ : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range H) ×ˢ (Finset.range H)).filter fun ij ↦
    (M + ij.1) * u₂ ≡ (M + ij.2) * u₁ [MOD p]
def positiveMultiplesUpTo (d U : ℕ) : Finset ℕ :=
  (Finset.Icc 1 U).filter fun u ↦ d ∣ u

lemma positiveMultiplesUpTo_card (d U : ℕ) :
    (positiveMultiplesUpTo d U).card = U / d := by
  have hset : Finset.Icc 1 U = Finset.Ioc 0 U := by
    ext x
    simp
    omega
  rw [positiveMultiplesUpTo, hset]
  exact Nat.Ioc_filter_dvd_card_eq_div U d

/-- Division by `d` bijects its positive multiples up to `U` with the
positive integers up to `U / d`. -/
lemma sum_positiveMultiplesUpTo_quotient
    {R : Type*} [AddCommMonoid R] (d U : ℕ) (hd : 0 < d)
    (f : ℕ → R) :
    (∑ u ∈ positiveMultiplesUpTo d U, f (u / d)) =
      ∑ a ∈ Finset.Icc 1 (U / d), f a := by
  apply Finset.sum_bij (fun u _ ↦ u / d)
  · intro u hu
    change u ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u) at hu
    rw [Finset.mem_filter] at hu
    rw [Finset.mem_Icc]
    exact ⟨Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp hu.1).1 hu.2) hd,
      Nat.div_le_div_right (Finset.mem_Icc.mp hu.1).2⟩
  · intro u₁ hu₁ u₂ hu₂ h
    change u₁ ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u) at hu₁
    change u₂ ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u) at hu₂
    have hd₁ := (Finset.mem_filter.mp hu₁).2
    have hd₂ := (Finset.mem_filter.mp hu₂).2
    calc
      u₁ = d * (u₁ / d) := (Nat.mul_div_cancel' hd₁).symm
      _ = d * (u₂ / d) := by rw [h]
      _ = u₂ := Nat.mul_div_cancel' hd₂
  · intro a ha
    refine ⟨d * a, ?_, ?_⟩
    · change d * a ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u)
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_Icc] at ha ⊢
        exact ⟨Nat.mul_pos hd ha.1,
          by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).mp ha.2⟩
      · exact dvd_mul_right d a
    · rw [Nat.mul_div_cancel_left]
      exact hd
  · intro u hu
    rfl

lemma sum_Icc_natDiv_add_one_cast_le (H n : ℕ) :
    (((∑ a ∈ Finset.Icc 1 n, (H / a + 1)) : ℕ) : ℝ) ≤
      H * (1 + Real.log n) + n := by
  rw [Nat.cast_sum]
  calc
    (∑ a ∈ Finset.Icc 1 n, (((H / a + 1) : ℕ) : ℝ)) ≤
        ∑ a ∈ Finset.Icc 1 n, ((H : ℝ) / a + 1) := by
      apply Finset.sum_le_sum
      intro a ha
      norm_num only [Nat.cast_add, Nat.cast_one]
      exact add_le_add (Nat.cast_div_le (α := ℝ) (m := H) (n := a)) le_rfl
    _ = (∑ a ∈ Finset.Icc 1 n, (H : ℝ) / a) + n := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ H * (1 + Real.log n) + n := by
      gcongr
      exact sum_Icc_natCast_div_le H n

/-- The gcd itself is one of the common divisors, so the reduced-denominator
term is bounded by the sum over all common divisors. -/
lemma reduced_term_le_common_divisor_sum
    {H U u₁ u₂ : ℕ} (hu₁ : u₁ ∈ Finset.Icc 1 U) :
    H / (u₁ / u₁.gcd u₂) + 1 ≤
      ∑ d ∈ Finset.Icc 1 U,
        if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
  let d := u₁.gcd u₂
  have hu₁pos : 0 < u₁ := (Finset.mem_Icc.mp hu₁).1
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left u₂ hu₁pos
  have hdmem : d ∈ Finset.Icc 1 U := by
    rw [Finset.mem_Icc]
    exact ⟨hdpos, (Nat.gcd_le_left u₂ hu₁pos).trans
      (Finset.mem_Icc.mp hu₁).2⟩
  calc
    H / (u₁ / u₁.gcd u₂) + 1 =
        if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      simp [d, Nat.gcd_dvd_left, Nat.gcd_dvd_right]
    _ ≤ ∑ d ∈ Finset.Icc 1 U,
        if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      exact Finset.single_le_sum
        (s := Finset.Icc 1 U)
        (f := fun d ↦ if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0)
        (fun _ _ ↦ Nat.zero_le _) hdmem

def burgessDivisorOvercount (H U : ℕ) : ℕ :=
  ∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
    ∑ d ∈ Finset.Icc 1 U,
      if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0

lemma burgessDivisorSlice_eq (H U d : ℕ) (hd : 0 < d) :
    (∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
      if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0) =
      (U / d) * ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1) := by
  classical
  simp_rw [ite_and]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  change (∑ u₁ ∈ positiveMultiplesUpTo d U,
      ∑ u₂ ∈ Finset.Icc 1 U,
        if d ∣ u₂ then H / (u₁ / d) + 1 else 0) = _
  calc
    (∑ u₁ ∈ positiveMultiplesUpTo d U,
        ∑ u₂ ∈ Finset.Icc 1 U,
          if d ∣ u₂ then H / (u₁ / d) + 1 else 0) =
      ∑ u₁ ∈ positiveMultiplesUpTo d U,
        ∑ _u₂ ∈ positiveMultiplesUpTo d U,
          (H / (u₁ / d) + 1) := by
      apply Finset.sum_congr rfl
      intro u₁ hu₁
      rw [← Finset.sum_filter]
      rfl
    _ = (U / d) * ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1) := by
      simp_rw [Finset.sum_const]
      rw [positiveMultiplesUpTo_card]
      simp_rw [Nat.nsmul_eq_mul]
      rw [← Finset.mul_sum]
      congr 1
      exact sum_positiveMultiplesUpTo_quotient d U hd
        (fun a ↦ H / a + 1)

lemma burgessDivisorOvercount_eq (H U : ℕ) :
    burgessDivisorOvercount H U =
      ∑ d ∈ Finset.Icc 1 U, (U / d) *
        ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1) := by
  rw [burgessDivisorOvercount]
  calc
    (∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
        ∑ d ∈ Finset.Icc 1 U,
          if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0) =
      ∑ u₁ ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc 1 U,
        ∑ u₂ ∈ Finset.Icc 1 U,
          if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u₁ hu₁
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Icc 1 U, ∑ u₁ ∈ Finset.Icc 1 U,
        ∑ u₂ ∈ Finset.Icc 1 U,
          if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hdmem
      exact burgessDivisorSlice_eq H U d (Finset.mem_Icc.mp hdmem).1

lemma burgessDivisorOvercount_cast_le (H U : ℕ) (hU : 0 < U) :
    (burgessDivisorOvercount H U : ℝ) ≤
      ((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U)) := by
  rw [burgessDivisorOvercount_eq, Nat.cast_sum]
  have hlogU : 0 ≤ 1 + Real.log U := by
    have : (1 : ℝ) ≤ U := by exact_mod_cast hU
    linarith [Real.log_nonneg this]
  calc
    (∑ d ∈ Finset.Icc 1 U,
        ((((U / d) * ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1)) : ℕ) : ℝ)) ≤
      ∑ d ∈ Finset.Icc 1 U,
        ((U : ℝ) / d) * ((H : ℝ) * (1 + Real.log U) + U) := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hdpos : 0 < d := (Finset.mem_Icc.mp hdmem).1
      have hdU : d ≤ U := (Finset.mem_Icc.mp hdmem).2
      have hnpos : 0 < U / d := Nat.div_pos hdU hdpos
      have hnU : U / d ≤ U := Nat.div_le_self U d
      have hlog : Real.log (((U / d : ℕ) : ℝ)) ≤ Real.log U := by
        apply Real.log_le_log
        · exact_mod_cast hnpos
        · exact_mod_cast hnU
      rw [Nat.cast_mul]
      apply mul_le_mul
      · exact Nat.cast_div_le
      · calc
          (((∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1)) : ℕ) : ℝ) ≤
              (H : ℝ) * (1 + Real.log (((U / d : ℕ) : ℝ))) +
                (U / d : ℕ) :=
            sum_Icc_natDiv_add_one_cast_le H (U / d)
          _ ≤ (H : ℝ) * (1 + Real.log U) + U := by
            gcongr
      · positivity
      · positivity
    _ = ((H : ℝ) * (1 + Real.log U) + U) *
        ∑ d ∈ Finset.Icc 1 U, ((U : ℝ) / d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ ((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U)) := by
      exact mul_le_mul_of_nonneg_left (sum_Icc_natCast_div_le U U)
        (add_nonneg (mul_nonneg (Nat.cast_nonneg H) hlogU) (Nat.cast_nonneg U))

lemma reduced_denominator_sum_cast_le
    (H U : ℕ) :
    ((∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
      (H / (u₁ / u₁.gcd u₂) + 1) : ℕ) : ℝ) ≤
      (burgessDivisorOvercount H U : ℝ) := by
  exact_mod_cast Finset.sum_le_sum fun u₁ hu₁ ↦
    Finset.sum_le_sum fun u₂ hu₂ ↦
      reduced_term_le_common_divisor_sum hu₁
lemma burgessIntervalCollision_card_le_of_coprime
    {q M H U u₁ u₂ : ℕ}
    (hH : 0 < H) (hU : 0 < U)
    (hu₁ : u₁ ∈ Finset.Icc 1 U) (hu₂ : u₂ ∈ Finset.Icc 1 U)
    (hcop₁ : q.Coprime u₁)
    (hsmall : 2 * (U * H) < q) :
    (burgessIntervalCollision q M H u₁ u₂).card ≤
      H / (u₁ / u₁.gcd u₂) + 1 := by
  let d := u₁.gcd u₂
  let a := u₁ / d
  let b := u₂ / d
  have hu₁pos : 0 < u₁ := (Finset.mem_Icc.mp hu₁).1
  have hu₂pos : 0 < u₂ := (Finset.mem_Icc.mp hu₂).1
  have hu₁U : u₁ ≤ U := (Finset.mem_Icc.mp hu₁).2
  have hu₂U : u₂ ≤ U := (Finset.mem_Icc.mp hu₂).2
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left u₂ hu₁pos
  have hd₁ : d ∣ u₁ := Nat.gcd_dvd_left u₁ u₂
  have hd₂ : d ∣ u₂ := Nat.gcd_dvd_right u₁ u₂
  have hfac₁ : d * a = u₁ := Nat.mul_div_cancel' hd₁
  have hfac₂ : d * b = u₂ := Nat.mul_div_cancel' hd₂
  have hapos : 0 < a := Nat.div_pos (Nat.le_of_dvd hu₁pos hd₁) hdpos
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hdpos
  apply card_le_div_add_one_of_fst_pairwise_modEq
  · intro z hz
    exact Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).1
  · exact hapos
  · intro z hz w hw hzw
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    apply Prod.ext hzw
    change z.1 = w.1 at hzw
    rw [hzw] at hz'
    have hjmodM : M + z.2 ≡ M + w.2 [MOD q] := by
      apply Nat.ModEq.cancel_right_of_coprime hcop₁.gcd_eq_one
      exact hz'.symm.trans hw'
    have hjmod : z.2 ≡ w.2 [MOD q] :=
      Nat.ModEq.add_left_cancel' M hjmodM
    have hHq : H < q := by
      have hUHpos : 0 < U * H := Nat.mul_pos hU hH
      have hHle : H ≤ U * H := by
        simpa [mul_comm] using Nat.le_mul_of_pos_right H hU
      omega
    exact hjmod.eq_of_lt_of_lt
      (lt_trans (Finset.mem_range.mp
        (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).2) hHq)
      (lt_trans (Finset.mem_range.mp
        (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).2) hHq)
  · intro z hz w hw
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    have hsum := hz'.add hw'.symm
    have hred : u₂ * z.1 + u₁ * w.2 ≡
        u₂ * w.1 + u₁ * z.2 [MOD q] := by
      apply Nat.ModEq.add_left_cancel' (M * (u₁ + u₂))
      simpa [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc,
        add_comm, add_left_comm, add_assoc] using hsum
    have hzH := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).1
    have hzH₂ := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).2
    have hwH := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).1
    have hwH₂ := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).2
    have hterm₁ : u₂ * z.1 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₂U hzH hU
    have hterm₂ : u₁ * w.2 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₁U hwH₂ hU
    have hterm₃ : u₂ * w.1 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₂U hwH hU
    have hterm₄ : u₁ * z.2 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₁U hzH₂ hU
    have heq : u₂ * z.1 + u₁ * w.2 =
        u₂ * w.1 + u₁ * z.2 :=
      hred.eq_of_lt_of_lt (by omega) (by omega)
    have hdeq : d * (b * z.1 + a * w.2) =
        d * (b * w.1 + a * z.2) := by
      calc
        d * (b * z.1 + a * w.2) = u₂ * z.1 + u₁ * w.2 := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, hfac₂, hfac₁]
        _ = u₂ * w.1 + u₁ * z.2 := heq
        _ = d * (b * w.1 + a * z.2) := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, hfac₂, hfac₁]
    have hnorm : b * z.1 + a * w.2 = b * w.1 + a * z.2 :=
      Nat.eq_of_mul_eq_mul_left hdpos hdeq
    have haw : a * w.2 ≡ 0 [MOD a] :=
      (Nat.dvd_mul_right a w.2).modEq_zero_nat
    have haz : a * z.2 ≡ 0 [MOD a] :=
      (Nat.dvd_mul_right a z.2).modEq_zero_nat
    have hfull : b * z.1 + a * w.2 ≡ b * w.1 + a * z.2 [MOD a] := by
      rw [hnorm]
    have hba : b * z.1 ≡ b * w.1 [MOD a] :=
      ((Nat.ModEq.rfl.add haw.symm).trans hfull).trans
        (Nat.ModEq.rfl.add haz)
    exact Nat.ModEq.cancel_left_of_coprime hab.gcd_eq_one hba

end Pollack17.Burgess

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/PrimitiveConductorFibers.lean` -/

section

/-!
# Primitive-character conductor fibers

This file formalizes the finite conductor classification used after the
centered `psi'` estimate in Akbary--Hambrook2013v2, Section 7, p. 25. A
positive-level character is partitioned by its conductor, and each conductor
fiber is equivalent to the primitive characters at that conductor. The later
`1 / phi (k * d)` weighting, least-prime cutoff, and analytic mean value are
deliberately outside this finite module.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section















end

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/PositiveDivisorPairReindex.lean` -/

section

/-!
# Positive divisor-pair reindexing

This file isolates the finite index change on Akbary--Hambrook2013v2,
Section 7, p. 25. A positive modulus and one of its divisors are reindexed by
the ordered pair `(d,k)` with modulus `d*k`. The first coordinate is reserved
for the future primitive conductor. The centered character sum, its
conductor-one vanishing, the totient weight, and the least-prime-factor cutoff
are deliberately not built into this generic finite layer.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Positive ordered factor pairs whose product is at most `Q`.

The first coordinate is the future primitive conductor and the second is its
positive multiplier. -/
def positiveFactorPairs (Q : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc 0 Q ×ˢ Finset.Ioc 0 Q).filter
    (fun p ↦ p.1 * p.2 ≤ Q)

/-- Regroup a first-coordinate-filtered positive factor-pair sum by its first
coordinate and the exact positive multiplier range. -/
theorem sum_positiveFactorPairs_filter_fst_eq_sum_multipliers
    {Q : ℕ} {M : Type*} [AddCommMonoid M]
    (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℕ → M) :
    (∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦ P p.1),
      f p.1 p.2) =
      ∑ d ∈ Finset.Ioc 0 Q with P d,
        ∑ k ∈ Finset.Ioc 0 (Q / d), f d k := by
  let S : Finset (ℕ × ℕ) :=
    (positiveFactorPairs Q).filter (fun p ↦ P p.1)
  let T : Finset ((d : ℕ) × ℕ) :=
    Finset.sigma ((Finset.Ioc 0 Q).filter P)
      (fun d ↦ Finset.Ioc 0 (Q / d))
  have hbij :
      (∑ p ∈ S, f p.1 p.2) =
        ∑ z ∈ T, f z.1 z.2 := by
    apply Finset.sum_bij (fun p _hp ↦ ⟨p.1, p.2⟩)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpairs, hP⟩
      rcases Finset.mem_filter.mp hpairs with ⟨hprodmem, hprod⟩
      rcases Finset.mem_product.mp hprodmem with ⟨hdmem, hkmem⟩
      have hdpos : 0 < p.1 := (Finset.mem_Ioc.mp hdmem).1
      have hkdiv : p.2 ≤ Q / p.1 := by
        apply (Nat.le_div_iff_mul_le hdpos).2
        simpa [Nat.mul_comm] using hprod
      exact Finset.mem_sigma.mpr ⟨
        Finset.mem_filter.mpr ⟨hdmem, hP⟩,
        Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hkmem).1, hkdiv⟩⟩
    · intro p _hp p' _hp' heq
      apply Prod.ext
      · exact congrArg Sigma.fst heq
      · exact congrArg Sigma.snd heq
    · intro z hz
      rcases z with ⟨d, k⟩
      rcases Finset.mem_sigma.mp hz with ⟨hdmemP, hkmem⟩
      rcases Finset.mem_filter.mp hdmemP with ⟨hdmem, hP⟩
      have hdpos : 0 < d := (Finset.mem_Ioc.mp hdmem).1
      have hkBounds := Finset.mem_Ioc.mp hkmem
      have hprod : d * k ≤ Q := by
        have h := (Nat.le_div_iff_mul_le hdpos).1 hkBounds.2
        simpa [Nat.mul_comm] using h
      have hkQ : k ≤ Q :=
        hkBounds.2.trans (Nat.div_le_self Q d)
      have hpairs : (d, k) ∈ positiveFactorPairs Q := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr ⟨hdmem,
          Finset.mem_Ioc.mpr ⟨hkBounds.1, hkQ⟩⟩, hprod⟩
      exact ⟨(d, k), Finset.mem_filter.mpr ⟨hpairs, hP⟩, rfl⟩
    · intro p _hp
      rfl
  have hsum := Finset.sum_sigma'
    ((Finset.Ioc 0 Q).filter P)
    (fun d ↦ Finset.Ioc 0 (Q / d)) (fun d k ↦ f d k)
  simpa [S, T] using hbij.trans hsum.symm

/-- Reindex positive products and their divisor antidiagonals by ordered
positive factor pairs. -/
theorem sum_divisorsAntidiagonal_up_to_eq_sum_positiveFactorPairs
    {Q : ℕ} {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) :
    (∑ q ∈ Finset.Ioc 0 Q,
      ∑ p ∈ q.divisorsAntidiagonal, f p.1 p.2) =
      ∑ p ∈ positiveFactorPairs Q, f p.1 p.2 := by
  let T : Finset ℕ := Finset.Ioc 0 Q
  let g : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2
  have hmaps : ∀ p ∈ positiveFactorPairs Q, g p ∈ T := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hprod⟩
    rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
    rw [Finset.mem_Ioc] at hp₁ hp₂
    exact Finset.mem_Ioc.mpr ⟨Nat.mul_pos hp₁.1 hp₂.1, hprod⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := positiveFactorPairs Q) (t := T) hmaps
    (fun p ↦ f p.1 p.2)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le (N := Q)]
  · apply Finset.sum_congr
    · ext p
      simp only [positiveFactorPairs, g, Finset.mem_filter]
      constructor
      · rintro ⟨hp, hprod⟩
        exact ⟨⟨hp, hprod.le.trans (Finset.mem_Ioc.mp hq).2⟩, hprod⟩
      · rintro ⟨⟨hp, _⟩, hprod⟩
        exact ⟨hp, hprod⟩
    · intro p _
      rfl
  · exact (Finset.mem_Ioc.mp hq).1.ne'
  · exact (Finset.mem_Ioc.mp hq).2

/-- Reindex a positive modulus and one of its divisors by the divisor and its
positive complementary factor. -/
theorem sum_divisors_up_to_eq_sum_positiveFactorPairs
    {Q : ℕ} {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) :
    (∑ q ∈ Finset.Ioc 0 Q,
      ∑ d ∈ q.divisors, f q d) =
      ∑ p ∈ positiveFactorPairs Q,
        f (p.1 * p.2) p.1 := by
  calc
    (∑ q ∈ Finset.Ioc 0 Q, ∑ d ∈ q.divisors, f q d) =
        ∑ q ∈ Finset.Ioc 0 Q,
          ∑ p ∈ q.divisorsAntidiagonal,
            f (p.1 * p.2) p.1 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Nat.sum_divisorsAntidiagonal
        (f := fun d _k ↦ f q d)]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      rw [hp.1]
    _ = _ :=
      sum_divisorsAntidiagonal_up_to_eq_sum_positiveFactorPairs
        (fun d k ↦ f (d * k) d)



end

end BoundedGaps.Maynard

end

/-! ### Upstream module `ErdosProblems/Erdos1141/DivisorHyperbola.lean` -/

section

/-!
# A truncated hyperbola estimate for quadratic divisor coefficients
-/

namespace Pollack17

open scoped BigOperators
open BoundedGaps.Maynard

theorem divisor_sum_hyperbola (f : ℕ → ℝ) {X Y : ℕ} (hYX : Y ≤ X) :
    (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, f d) =
      (∑ d ∈ Finset.Icc 1 Y, ((X / d : ℕ) : ℝ) * f d) +
        ∑ a ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Ioc Y (X / a), f d := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (positiveFactorPairs X)
    (fun p : ℕ × ℕ => p.1 ≤ Y) (fun p => f p.1)
  have hsmall : (∑ p ∈ (positiveFactorPairs X).filter (fun p => p.1 ≤ Y), f p.1) =
      ∑ d ∈ Finset.Icc 1 Y, ((X / d : ℕ) : ℝ) * f d := by
    rw [sum_positiveFactorPairs_filter_fst_eq_sum_multipliers (fun d => d ≤ Y) (fun d _ => f d)]
    have hset : (Finset.Ioc 0 X).filter (fun d => d ≤ Y) = Finset.Icc 1 Y := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hset]
    simp
  have hlarge : (∑ p ∈ (positiveFactorPairs X).filter (fun p => ¬p.1 ≤ Y), f p.1) =
      ∑ a ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Ioc Y (X / a), f d := by
    rw [Finset.sum_sigma']
    apply Finset.sum_bij (fun p _ => ⟨p.2, p.1⟩)
    · intro p hp
      obtain ⟨hp, hY⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp, hprod⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      have ha := Finset.mem_Ioc.mp ha
      have hb := Finset.mem_Ioc.mp hb
      exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr hb,
        Finset.mem_Ioc.mpr ⟨by change Y < p.1; omega, (Nat.le_div_iff_mul_le hb.1).mpr hprod⟩⟩
    · intro p _ p' _ h
      exact Prod.ext (congrArg Sigma.snd h) (congrArg Sigma.fst h)
    · rintro ⟨a, d⟩ h
      obtain ⟨ha, hd⟩ := Finset.mem_sigma.mp h
      have ha := Finset.mem_Icc.mp ha
      have hd := Finset.mem_Ioc.mp hd
      dsimp only [Sigma.fst, Sigma.snd] at ha hd
      refine ⟨(d, a), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, by simpa using not_le.mpr hd.1⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega,
        hd.2.trans (Nat.div_le_self _ _)⟩, Finset.mem_Ioc.mpr ha⟩,
        (Nat.le_div_iff_mul_le ha.1).mp hd.2⟩
    · intro p _
      rfl
  calc
    _ = ∑ n ∈ Finset.Ioc 0 X, ∑ d ∈ n.divisors, f d := by
      rw [show Finset.Icc 1 X = Finset.Ioc 0 X by ext n; simp; omega]
    _ = ∑ p ∈ positiveFactorPairs X, f p.1 := sum_divisors_up_to_eq_sum_positiveFactorPairs _
    _ = _ := by rw [← hsplit, hsmall, hlarge]

theorem abs_truncated_floor_error_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (X Y : ℕ) :
    |(∑ d ∈ Finset.Icc 1 Y, ((X / d : ℕ) : ℝ) * f d) -
      (X : ℝ) * ∑ d ∈ Finset.Icc 1 Y, f d / (d : ℝ)| ≤ Y := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 Y,
        |((X / d : ℕ) : ℝ) * f d - (X : ℝ) * (f d / (d : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 Y, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have heq : ((X / d : ℕ) : ℝ) * f d - (X : ℝ) * (f d / (d : ℝ)) =
          (((X / d : ℕ) : ℝ) - (X : ℝ) / d) * f d := by ring
      rw [heq, abs_mul]
      have hfloor : |((X / d : ℕ) : ℝ) - (X : ℝ) / d| ≤ 1 := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr Nat.cast_div_le)]
        have h := Nat.lt_floor_add_one ((X : ℝ) / d)
        rw [Nat.floor_div_eq_div] at h
        linarith
      exact (mul_le_mul hfloor (hf d) (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
    _ = _ := by simp

theorem abs_hyperbola_tail_le (f : ℕ → ℝ) {X Y : ℕ} (hY : 0 < Y)
    {b : ℝ} (hb : 0 ≤ b)
    (hprefix : ∀ n : ℕ, Y ≤ n →
      |∑ d ∈ Finset.Icc 1 n, f d| ≤ (n : ℝ) * b) :
    |∑ a ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Ioc Y (X / a), f d| ≤
      2 * (X : ℝ) * b * (1 + Real.log (X : ℝ)) := by
  have hterm (a : ℕ) (ha : a ∈ Finset.Icc 1 X) :
      |∑ d ∈ Finset.Ioc Y (X / a), f d| ≤ 2 * (X : ℝ) * b * (a : ℝ)⁻¹ := by
    by_cases hN : Y ≤ X / a
    · have heq : (∑ d ∈ Finset.Ioc Y (X / a), f d) =
          (∑ d ∈ Finset.Icc 1 (X / a), f d) - ∑ d ∈ Finset.Icc 1 Y, f d := by
        rw [show Finset.Icc 1 (X / a) = Finset.Ioc 0 (X / a) by ext n; simp; omega,
          show Finset.Icc 1 Y = Finset.Ioc 0 Y by ext n; simp; omega,
          ← Finset.sum_Ioc_consecutive f (Nat.zero_le Y) hN]
        ring
      rw [heq]
      calc
        _ ≤ |∑ d ∈ Finset.Icc 1 (X / a), f d| + |∑ d ∈ Finset.Icc 1 Y, f d| := by
          simpa only [Real.norm_eq_abs] using norm_sub_le
            (∑ d ∈ Finset.Icc 1 (X / a), f d) (∑ d ∈ Finset.Icc 1 Y, f d)
        _ ≤ ((X / a : ℕ) : ℝ) * b + (Y : ℝ) * b :=
          add_le_add (hprefix _ hN) (hprefix _ le_rfl)
        _ ≤ 2 * (((X / a : ℕ) : ℝ) * b) := by
          have h := mul_le_mul_of_nonneg_right (show (Y : ℝ) ≤ (X / a : ℕ) by exact_mod_cast hN) hb
          linarith
        _ ≤ 2 * ((X : ℝ) / a * b) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right Nat.cast_div_le hb) (by norm_num)
        _ = _ := by ring
    · rw [Finset.Ioc_eq_empty_of_le (by omega), Finset.sum_empty, abs_zero]
      positivity
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 X, |∑ d ∈ Finset.Ioc Y (X / a), f d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 X, 2 * (X : ℝ) * b * (a : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = (2 * (X : ℝ) * b) * ∑ a ∈ Finset.Icc 1 X, (a : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (Burgess.sum_Icc_inv_natCast_le_one_add_log X) (by positivity)

theorem abs_divisor_sum_sub_truncated_main_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {X Y : ℕ} (hY : 0 < Y) (hYX : Y ≤ X) {b : ℝ} (hb : 0 ≤ b)
    (hprefix : ∀ n : ℕ, Y ≤ n → |∑ d ∈ Finset.Icc 1 n, f d| ≤ (n : ℝ) * b) :
    |(∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, f d) -
        (X : ℝ) * ∑ d ∈ Finset.Icc 1 Y, f d / (d : ℝ)| ≤
      (Y : ℝ) + 2 * (X : ℝ) * b * (1 + Real.log (X : ℝ)) := by
  rw [divisor_sum_hyperbola f hYX]
  have heq : (∑ d ∈ Finset.Icc 1 Y, ((X / d : ℕ) : ℝ) * f d) +
      (∑ a ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Ioc Y (X / a), f d) -
        (X : ℝ) * ∑ d ∈ Finset.Icc 1 Y, f d / (d : ℝ) =
      ((∑ d ∈ Finset.Icc 1 Y, ((X / d : ℕ) : ℝ) * f d) -
        (X : ℝ) * ∑ d ∈ Finset.Icc 1 Y, f d / (d : ℝ)) +
        (∑ a ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Ioc Y (X / a), f d) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add (abs_truncated_floor_error_le f hf X Y)
    (abs_hyperbola_tail_le f hY hb hprefix))

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/StepanovBox.lean` -/

section

/-!
# Nonvanishing for the quadratic Stepanov construction

A polynomial whose nonzero exponents have residues below `A` modulo the
characteristic has the same property after translation.  Lucas's theorem
therefore bounds every root multiplicity modulo the characteristic.
Two such polynomials cannot cancel after one is multiplied by a half-power
of a polynomial with a simple root.  This is the nonvanishing argument for
the auxiliary polynomial used to estimate quadratic character sums.
-/

namespace Pollack17.Stepanov

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] {p A : ℕ}

/-- All nonzero coefficients occur at exponents with small residue modulo `p`. -/
def LowResidueSupport (p A : ℕ) (P : K[X]) : Prop :=
  ∀ n : ℕ, P.coeff n ≠ 0 → n % p < A

theorem choose_cast_eq_zero_of_residue_lt [Fact p.Prime] [CharP K p]
    {n k : ℕ} (h : n % p < k % p) :
    (n.choose k : K) = 0 := by
  have hmod := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := n) (k := k)
  rw [Nat.choose_eq_zero_of_lt h, zero_mul] at hmod
  exact (CharP.cast_eq_zero_iff K p _).mpr (Nat.modEq_zero_iff_dvd.mp hmod)

theorem LowResidueSupport.taylor [Fact p.Prime] [CharP K p]
    {P : K[X]} (hP : LowResidueSupport p A P) (x : K) :
    LowResidueSupport p A (taylor x P) := by
  intro k hk
  by_contra hkle
  have hkA : A ≤ k % p := Nat.le_of_not_gt hkle
  apply hk
  rw [taylor_coeff, hasseDeriv_apply, Polynomial.sum_def, eval_finsetSum]
  apply Finset.sum_eq_zero
  intro n hn
  have hnA := hP n (Polynomial.mem_support_iff.mp hn)
  have hchoose : (n.choose k : K) = 0 := choose_cast_eq_zero_of_residue_lt (hnA.trans_le hkA)
  simp [hchoose]

theorem LowResidueSupport.rootMultiplicity_mod_lt [Fact p.Prime] [CharP K p] {P : K[X]}
    (hP : LowResidueSupport p A P) (hP0 : P ≠ 0) (x : K) :
    P.rootMultiplicity x % p < A := by
  have hT : Polynomial.taylor x P ≠ 0 := (Polynomial.taylor_eq_zero x P).not.mpr hP0
  have hcoeff : (Polynomial.taylor x P).coeff (Polynomial.taylor x P).natTrailingDegree ≠ 0 :=
    Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT
  have hres := hP.taylor x _ hcoeff
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  exact hres

theorem rootMultiplicity_neg_eq (P : K[X]) (x : K) :
    (-P).rootMultiplicity x = P.rootMultiplicity x := by
  simp only [Polynomial.rootMultiplicity_eq_natTrailingDegree, neg_comp,
    Polynomial.natTrailingDegree_neg]

theorem rootMultiplicity_pow_eq {f : K[X]} (hf : f ≠ 0) (x : K) (t : ℕ) :
    (f ^ t).rootMultiplicity x = t * f.rootMultiplicity x := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hf) hf), ih]
    ring

/-- The two halves of the quadratic auxiliary polynomial are independent.
The degree of `f` is unrestricted; only one simple root is needed. -/
theorem add_pow_mul_ne_zero [Fact p.Prime] [CharP K p] {P Q f : K[X]} {x : K} {t : ℕ}
    (hP : LowResidueSupport p A P) (hQ : LowResidueSupport p A Q)
    (hne : P ≠ 0 ∨ Q ≠ 0) (hf : f ≠ 0) (hx : f.rootMultiplicity x = 1)
    (hAt : A ≤ t) (htA : t + A ≤ p) :
    P + f ^ t * Q ≠ 0 := by
  intro hzero
  have hQ0 : Q ≠ 0 := by
    intro hQzero
    have hPzero : P = 0 := by simpa [hQzero] using hzero
    exact hne.elim (fun h => h hPzero) (fun h => h hQzero)
  have hP0 : P ≠ 0 := by
    intro hPzero
    have hprod : f ^ t * Q = 0 := by simpa [hPzero] using hzero
    exact mul_ne_zero (pow_ne_zero _ hf) hQ0 hprod
  have hPmod := hP.rootMultiplicity_mod_lt hP0 x
  have hQmod := hQ.rootMultiplicity_mod_lt hQ0 x
  have hmult : P.rootMultiplicity x = t + Q.rootMultiplicity x := by
    rw [eq_neg_of_add_eq_zero_left hzero, rootMultiplicity_neg_eq,
      Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hf) hQ0),
      rootMultiplicity_pow_eq hf x t, hx, mul_one]
  have htlt : t < p := by omega
  have hsumlt : t + Q.rootMultiplicity x % p < p := by omega
  have hmod : P.rootMultiplicity x % p = t + Q.rootMultiplicity x % p := by
    rw [hmult, Nat.add_mod, Nat.mod_eq_of_lt htlt, Nat.mod_eq_of_lt hsumlt]
  omega

/-- The exponent of one monomial in the Frobenius coefficient box. -/
def boxExponent (p : ℕ) {A B : ℕ} (i : Fin A × Fin B) : ℕ := i.1 + p * i.2

theorem boxExponent_mod {A B : ℕ} (hA : A ≤ p) (i : Fin A × Fin B) :
    boxExponent p i % p = i.1 := by
  simp [boxExponent, Nat.add_mod, Nat.mod_eq_of_lt (i.1.isLt.trans_le hA)]

theorem boxExponent_injective {A B : ℕ} (hA : A ≤ p) :
    Function.Injective (boxExponent p : Fin A × Fin B → ℕ) := by
  intro i j hij
  have ha : (i.1 : ℕ) = j.1 := by
    simpa only [boxExponent_mod hA] using congrArg (fun n => n % p) hij
  have hp0 : 0 < p := (Nat.zero_le _).trans_lt (i.1.isLt.trans_le hA)
  have hmul : p * (i.2 : ℕ) = p * (j.2 : ℕ) := by
    simpa only [boxExponent, ha, Nat.add_left_cancel_iff] using hij
  exact Prod.ext (Fin.ext ha) (Fin.ext (Nat.eq_of_mul_eq_mul_left hp0 hmul))

/-- A polynomial with coefficients in a rectangular Frobenius box. -/
noncomputable def boxPolynomial {A B : ℕ} (a : Fin A × Fin B → K) : K[X] :=
  ∑ i : Fin A × Fin B, monomial (boxExponent p i) (a i)

theorem boxPolynomial_coeff {A B : ℕ} (hA : A ≤ p)
    (a : Fin A × Fin B → K) (i : Fin A × Fin B) :
    (boxPolynomial (p := p) a).coeff (boxExponent p i) = a i := by
  classical
  rw [boxPolynomial, finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne := (boxExponent_injective hA).ne hji
    simp [coeff_monomial, hne]
  · simp

theorem boxPolynomial_injective {A B : ℕ} (hA : A ≤ p) :
    Function.Injective (boxPolynomial (K := K) (p := p) (A := A) (B := B)) := by
  intro a b hab
  funext i
  simpa only [boxPolynomial_coeff hA] using
    congrArg (fun P : K[X] => P.coeff (boxExponent p i)) hab

theorem boxPolynomial_lowResidueSupport {A B : ℕ} (hA : A ≤ p)
    (a : Fin A × Fin B → K) : LowResidueSupport p A (boxPolynomial (p := p) a) := by
  classical
  intro n hn
  by_contra hnot
  apply hn
  rw [boxPolynomial, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  have hne : boxExponent p i ≠ n := by
    intro h
    have : n % p = i.1 := h ▸ boxExponent_mod hA i
    exact hnot (this ▸ i.1.isLt)
  simp [coeff_monomial, hne]

theorem boxPolynomial_ne_zero {A B : ℕ} (hA : A ≤ p)
    {a : Fin A × Fin B → K} (ha : a ≠ 0) : boxPolynomial (p := p) a ≠ 0 := by
  intro h
  apply ha
  apply boxPolynomial_injective (K := K) hA
  simpa [boxPolynomial] using h

theorem box_auxiliary_ne_zero [Fact p.Prime] [CharP K p]
    {A B t : ℕ} {a b : Fin A × Fin B → K}
    (hab : a ≠ 0 ∨ b ≠ 0) {f : K[X]} {x : K}
    (hf : f ≠ 0) (hx : f.rootMultiplicity x = 1)
    (hAt : A ≤ t) (htA : t + A ≤ p) :
    boxPolynomial (p := p) a + f ^ t * boxPolynomial (p := p) b ≠ 0 := by
  have hAp : A ≤ p := by omega
  exact add_pow_mul_ne_zero (boxPolynomial_lowResidueSupport hAp a)
    (boxPolynomial_lowResidueSupport hAp b)
    (hab.imp (boxPolynomial_ne_zero hAp) (boxPolynomial_ne_zero hAp))
    hf hx hAt htA

end Pollack17.Stepanov

end

/-! ### Upstream module `ErdosProblems/Erdos1141/StepanovDerivative.lean` -/

section

/-!
# Reduced derivatives for the quadratic Stepanov polynomial

Multiplication by `f^k` clears the denominators from differentiating
`f^t g`.  The resulting polynomial has degree growing only linearly in
the derivative order, independently of the exponent `t`.
-/

namespace Pollack17.Stepanov

open Polynomial

variable {K : Type*} [Field K]

noncomputable def reducedDerivative (f : K[X]) (t : K) (g : K[X]) : ℕ → K[X]
  | 0 => g
  | k + 1 => f * (reducedDerivative f t g k).derivative +
      C (t - k) * f.derivative * reducedDerivative f t g k

theorem mul_derivative_pow (f : K[X]) (k : ℕ) :
    f * (f ^ k).derivative = C (k : K) * f ^ k * f.derivative := by
  cases k with
  | zero => simp
  | succ k =>
    rw [derivative_pow_succ, pow_succ]
    push_cast
    ring

theorem mul_derivative_pow_mul (f g : K[X]) (k : ℕ) :
    f * (f ^ k * g).derivative =
      C (k : K) * f ^ k * f.derivative * g + f ^ (k + 1) * g.derivative := by
  rw [derivative_mul, mul_add, ← mul_assoc, mul_derivative_pow]
  rw [pow_succ]
  ring

theorem pow_mul_iterate_derivative (f g : K[X]) (t k : ℕ) :
    f ^ k * derivative^[k] (f ^ t * g) =
      f ^ t * reducedDerivative f (t : K) g k := by
  induction k with
  | zero => simp [reducedDerivative]
  | succ k ih =>
    have hderiv := congrArg (fun P : K[X] => f * P.derivative) ih
    rw [mul_derivative_pow_mul, mul_derivative_pow_mul] at hderiv
    simp only [map_natCast] at hderiv
    rw [Function.iterate_succ_apply', reducedDerivative]
    simp only [map_sub, map_natCast]
    linear_combination hderiv - (k : K[X]) * f.derivative * ih

theorem reducedDerivative_natDegree_le (f g : K[X]) (t : K) (k : ℕ) :
    (reducedDerivative f t g k).natDegree ≤ g.natDegree + k * f.natDegree := by
  induction k with
  | zero => simp [reducedDerivative]
  | succ k ih =>
    rw [reducedDerivative]
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · have hderiv := (Polynomial.natDegree_derivative_le
        (reducedDerivative f t g k)).trans (Nat.sub_le _ _)
      have hmul := Polynomial.natDegree_mul_le
        (p := f) (q := (reducedDerivative f t g k).derivative)
      nlinarith
    · have hderiv := (Polynomial.natDegree_derivative_le f).trans (Nat.sub_le _ _)
      have hconst := Polynomial.natDegree_C_mul_le (t - (k : K)) f.derivative
      have hmul := Polynomial.natDegree_mul_le
        (p := C (t - (k : K)) * f.derivative) (q := reducedDerivative f t g k)
      nlinarith

theorem iterate_derivative_mul_of_derivative_zero (g H : K[X])
    (hH : H.derivative = 0) (k : ℕ) :
    derivative^[k] (g * H) = derivative^[k] g * H := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih, derivative_mul, hH]

theorem derivative_frobenius_monomial {p : ℕ} [CharP K p] (b : ℕ) :
    (X ^ (p * b) : K[X]).derivative = 0 := by
  rw [derivative_X_pow]
  simp [Nat.cast_mul]

theorem eval_pow_mul_iterate_derivative_frobenius {p : ℕ} [CharP K p]
    (f g : K[X]) (t k b : ℕ) (x : K) (hx : x ^ p = x) :
    f.eval x ^ k * (derivative^[k] ((f ^ t * g) * X ^ (p * b))).eval x =
      f.eval x ^ t * (reducedDerivative f (t : K) g k).eval x * x ^ b := by
  rw [iterate_derivative_mul_of_derivative_zero _ _ (derivative_frobenius_monomial b)]
  simp only [eval_mul, eval_pow, eval_X]
  rw [pow_mul, hx, ← mul_assoc]
  have h := congrArg (fun P : K[X] => P.eval x) (pow_mul_iterate_derivative f g t k)
  simpa only [eval_mul, eval_pow] using congrArg (fun z : K => z * x ^ b) h

end Pollack17.Stepanov

end

/-! ### Upstream module `ErdosProblems/Erdos1141/StepanovConditions.lean` -/

section

/-!
# The linear conditions in the quadratic Stepanov argument

The coefficient box has dimension `2*A*B`.  Vanishing of the reduced
derivatives imposes fewer linear conditions when the displayed parameter
inequality holds, so a nonzero coefficient family exists.
-/

namespace Pollack17.Stepanov

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] {p A B D : ℕ}

abbrev BoxPair (K : Type*) (A B : ℕ) :=
  (Fin A × Fin B → K) × (Fin A × Fin B → K)

noncomputable def conditionHalf (f : K[X]) (t : K) (k : ℕ)
    (a : Fin A × Fin B → K) : K[X] :=
  ∑ i : Fin A × Fin B,
    a i • (reducedDerivative f t (X ^ (i.1 : ℕ)) k * X ^ (i.2 : ℕ))

noncomputable def conditionPolynomial (f : K[X]) (t : K) (k : ℕ)
    (a : BoxPair K A B) : K[X] := conditionHalf f 0 k a.1 + conditionHalf f t k a.2

theorem conditionHalf_natDegree_le (f : K[X]) (t : K) (k : ℕ)
    (a : Fin A × Fin B → K) :
    (conditionHalf f t k a).natDegree ≤ A + B + k * f.natDegree := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply (Polynomial.natDegree_smul_le _ _).trans
  have hred := reducedDerivative_natDegree_le f (X ^ (i.1 : ℕ)) t k
  have hmul := Polynomial.natDegree_mul_le
    (p := reducedDerivative f t (X ^ (i.1 : ℕ)) k) (q := X ^ (i.2 : ℕ))
  simp only [natDegree_X_pow] at hred hmul
  have ha := i.1.isLt
  have hb := i.2.isLt
  omega

theorem conditionPolynomial_natDegree_le (f : K[X]) (t : K) (k : ℕ)
    (a : BoxPair K A B) :
    (conditionPolynomial f t k a).natDegree ≤ A + B + k * f.natDegree := by
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le (conditionHalf_natDegree_le f 0 k a.1) (conditionHalf_natDegree_le f t k a.2))

theorem conditionPolynomial_add (f : K[X]) (t : K) (k : ℕ)
    (a b : BoxPair K A B) :
    conditionPolynomial f t k (a + b) =
      conditionPolynomial f t k a + conditionPolynomial f t k b := by
  simp [conditionPolynomial, conditionHalf, add_smul, Finset.sum_add_distrib,
    add_add_add_comm]

theorem conditionPolynomial_smul (f : K[X]) (t : K) (k : ℕ)
    (c : K) (a : BoxPair K A B) :
    conditionPolynomial f t k (c • a) = c • conditionPolynomial f t k a := by
  simp [conditionPolynomial, conditionHalf, Finset.smul_sum, smul_add, smul_smul]

noncomputable def conditionLinear (f : K[X]) (t : K) (A B D H : ℕ) :
    BoxPair K A B →ₗ[K] (Fin D → Fin H → K) where
  toFun a k j := (conditionPolynomial f t k a).coeff j
  map_add' a b := by
    funext k j
    rw [conditionPolynomial_add, coeff_add]
    rfl
  map_smul' c a := by
    funext k j
    rw [conditionPolynomial_smul, coeff_smul]
    rfl

theorem exists_nonzero_condition_kernel (f : K[X]) (t : K) (A B D H : ℕ)
    (hdim : D * H < 2 * A * B) :
    ∃ a : BoxPair K A B, a ≠ 0 ∧ conditionLinear f t A B D H a = 0 := by
  let T := conditionLinear f t A B D H
  have hker : LinearMap.ker T ≠ ⊥ := by
    intro hbot
    have hle := T.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hbot)
    have hsource : Module.finrank K (BoxPair K A B) = 2 * A * B := by
      simp [BoxPair, Module.finrank_prod]
      ring
    have htarget : Module.finrank K (Fin D → Fin H → K) = D * H := by
      simp [Module.finrank_pi_fintype]
    rw [hsource, htarget] at hle
    exact (not_le_of_gt hdim) hle
  obtain ⟨a, ha, hane⟩ := (LinearMap.ker T).ne_bot_iff.mp hker
  exact ⟨a, hane, ha⟩

theorem exists_nonzero_vanishing_conditions (f : K[X]) (t : K) (A B D : ℕ)
    (hdim : D * (A + B + D * f.natDegree + 1) < 2 * A * B) :
    ∃ a : BoxPair K A B, a ≠ 0 ∧
      ∀ k : ℕ, k < D → conditionPolynomial f t k a = 0 := by
  let H := A + B + D * f.natDegree + 1
  obtain ⟨a, ha, hkernel⟩ := exists_nonzero_condition_kernel f t A B D H hdim
  refine ⟨a, ha, ?_⟩
  intro k hk
  have hdegree : (conditionPolynomial f t k a).natDegree < H := by
    have hdeg := conditionPolynomial_natDegree_le f t k a
    have hmul := Nat.mul_le_mul_right f.natDegree hk.le
    omega
  ext n
  rw [coeff_zero]
  by_cases hn : n < H
  · exact congrFun (congrFun hkernel ⟨k, hk⟩) ⟨n, hn⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdegree.trans_le (Nat.le_of_not_gt hn))

theorem pow_mul_boxPolynomial_eq_sum (f : K[X]) (t : ℕ)
    (a : Fin A × Fin B → K) :
    f ^ t * boxPolynomial (p := p) a =
      ∑ i : Fin A × Fin B, a i • ((f ^ t * X ^ (i.1 : ℕ)) * X ^ (p * i.2)) := by
  classical
  rw [boxPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← C_mul_X_pow_eq_monomial, boxExponent, pow_add, smul_eq_C_mul]
  ring

theorem eval_conditionHalf {p : ℕ} [CharP K p]
    (f : K[X]) (t k : ℕ) (a : Fin A × Fin B → K) (x : K) (hx : x ^ p = x) :
    f.eval x ^ k * (derivative^[k] (f ^ t * boxPolynomial (p := p) a)).eval x =
      f.eval x ^ t * (conditionHalf f (t : K) k a).eval x := by
  classical
  rw [pow_mul_boxPolynomial_eq_sum, Polynomial.iterate_derivative_sum]
  simp only [Polynomial.iterate_derivative_smul, eval_finsetSum, eval_smul,
    conditionHalf, eval_mul, eval_pow, eval_X]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := eval_pow_mul_iterate_derivative_frobenius f (X ^ (i.1 : ℕ)) t k i.2 x hx
  change f.eval x ^ k * (a i * _) = f.eval x ^ t * (a i * (_ * _))
  linear_combination a i * h

theorem eval_conditionPolynomial {p : ℕ} [CharP K p]
    (f : K[X]) (t k : ℕ) (a : BoxPair K A B) (x : K)
    (hx : x ^ p = x) (hft : f.eval x ^ t = 1) :
    f.eval x ^ k *
        (derivative^[k] (boxPolynomial (p := p) a.1 + f ^ t * boxPolynomial (p := p) a.2)).eval x =
      (conditionPolynomial f (t : K) k a).eval x := by
  have h0 := eval_conditionHalf f 0 k a.1 x hx
  have ht := eval_conditionHalf f t k a.2 x hx
  simp only [pow_zero, one_mul, Nat.cast_zero] at h0
  rw [hft, one_mul] at ht
  have hsum : derivative^[k]
      (boxPolynomial (p := p) a.1 + f ^ t * boxPolynomial (p := p) a.2) =
      derivative^[k] (boxPolynomial (p := p) a.1) +
        derivative^[k] (f ^ t * boxPolynomial (p := p) a.2) :=
    iterate_map_add Polynomial.derivative k _ _
  rw [hsum, eval_add, mul_add, h0, ht, conditionPolynomial, eval_add]

end Pollack17.Stepanov

end

/-! ### Upstream module `ErdosProblems/Erdos1141/StepanovRootCount.lean` -/

section

/-!
# Root counting for the quadratic Stepanov polynomial
-/

namespace Pollack17.Stepanov

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

theorem le_rootMultiplicity_of_derivatives {p D : ℕ} [Fact p.Prime] [CharP K p]
    {P : K[X]} {x : K} (hP : P ≠ 0) (hDp : D ≤ p)
    (hvanish : ∀ k : ℕ, k < D → (derivative^[k] P).eval x = 0) :
    D ≤ P.rootMultiplicity x := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  apply Polynomial.le_natTrailingDegree
  · exact (Polynomial.taylor_eq_zero x P).not.mpr hP
  · intro k hk
    change (Polynomial.taylor x P).coeff k = 0
    rw [Polynomial.taylor_coeff]
    have hfact : (k.factorial : K) ≠ 0 := by
      rw [ne_eq, CharP.cast_eq_zero_iff K p, (Fact.out : p.Prime).dvd_factorial, not_le]
      exact hk.trans_le hDp
    have hscaled := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) k) P
    have heval := congrArg (fun Q : K[X] => Q.eval x) hscaled
    simp only [nsmul_eq_mul, Module.End.mul_apply, Module.End.natCast_apply,
      nsmul_eq_mul, eval_mul, eval_natCast] at heval
    rw [hvanish k hk] at heval
    exact (mul_eq_zero.mp heval).resolve_left hfact

theorem mul_card_le_natDegree_of_derivatives {p D : ℕ} [Fact p.Prime] [CharP K p]
    {P : K[X]} (hP : P ≠ 0) (hDp : D ≤ p) (S : Finset K)
    (hvanish : ∀ x ∈ S, ∀ k : ℕ, k < D → (derivative^[k] P).eval x = 0) :
    D * S.card ≤ P.natDegree := by
  classical
  by_cases hD : D = 0
  · simp [hD]
  have hmult (x : K) (hx : x ∈ S) : D ≤ P.rootMultiplicity x :=
    le_rootMultiplicity_of_derivatives hP hDp (hvanish x hx)
  have hsubset : S ⊆ P.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, ← Multiset.count_pos, Polynomial.count_roots]
    exact (Nat.pos_of_ne_zero hD).trans_le (hmult x hx)
  calc
    D * S.card = ∑ _x ∈ S, D := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ S, P.rootMultiplicity x := Finset.sum_le_sum hmult
    _ = ∑ x ∈ S, P.roots.count x := by simp only [Polynomial.count_roots]
    _ ≤ ∑ x ∈ P.roots.toFinset, P.roots.count x := Finset.sum_le_sum_of_subset hsubset
    _ = P.roots.card := Multiset.toFinset_sum_count_eq P.roots
    _ ≤ P.natDegree := Polynomial.card_roots' P

theorem boxPolynomial_natDegree_le {p A B : ℕ} (a : Fin A × Fin B → K) :
    (boxPolynomial (p := p) a).natDegree ≤ A + p * B := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply (Polynomial.natDegree_monomial_le (a i)).trans
  dsimp [boxExponent]
  have hmul := Nat.mul_le_mul_left p i.2.isLt.le
  have ha := i.1.isLt.le
  omega

/-- The finite Stepanov fiber inequality before choosing numerical parameters. -/
theorem quadratic_fiber_card_bound {p A B D t : ℕ} [Fact p.Prime] [CharP K p]
    (f : K[X]) {x₀ : K} (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1)
    (hAt : A ≤ t) (htA : t + A ≤ p) (hDp : D ≤ p)
    (hdim : D * (A + B + D * f.natDegree + 1) < 2 * A * B)
    (S : Finset K)
    (hS : ∀ x ∈ S, x ^ p = x ∧ f.eval x ≠ 0 ∧ f.eval x ^ t = 1) :
    D * S.card ≤ A + p * B + t * f.natDegree := by
  classical
  obtain ⟨a, ha, hcond⟩ := exists_nonzero_vanishing_conditions f (t : K) A B D hdim
  have hpair : a.1 ≠ 0 ∨ a.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (Prod.ext h.1 h.2)
  let F := boxPolynomial (p := p) a.1 + f ^ t * boxPolynomial (p := p) a.2
  have hF : F ≠ 0 := box_auxiliary_ne_zero hpair hf hroot hAt htA
  have hdeg : F.natDegree ≤ A + p * B + t * f.natDegree := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact (boxPolynomial_natDegree_le a.1).trans (Nat.le_add_right _ _)
    · have hmul := Polynomial.natDegree_mul_le
        (p := f ^ t) (q := boxPolynomial (p := p) a.2)
      rw [Polynomial.natDegree_pow] at hmul
      have hb := boxPolynomial_natDegree_le (p := p) a.2
      omega
  apply (mul_card_le_natDegree_of_derivatives hF hDp S ?_).trans hdeg
  intro x hx k hk
  obtain ⟨hxp, hfx, hft⟩ := hS x hx
  have heval := eval_conditionPolynomial f t k a x hxp hft
  rw [hcond k hk, eval_zero] at heval
  exact (mul_eq_zero.mp heval).resolve_left (pow_ne_zero _ hfx)

end Pollack17.Stepanov

end

/-! ### Upstream module `ErdosProblems/Erdos1141/StepanovParameters.lean` -/

section

/-!
# Parameters for the quadratic Stepanov construction
-/

namespace Pollack17.Stepanov

open Polynomial

theorem constraints_lt_coefficients {A B D d : ℕ}
    (hB : 1 ≤ B) (hD : D + 1 = 2 * B) (hA : 4 * (d + 1) * B ^ 2 < A) :
    D * (A + B + D * d + 1) < 2 * A * B := by
  have hDle : D ≤ 2 * B := by omega
  have hDd : D * d ≤ 2 * B * d := Nat.mul_le_mul_right d hDle
  have hinner : B + D * d + 1 ≤ 2 * B * (d + 1) := by nlinarith
  have hcost : D * (B + D * d + 1) ≤ 4 * (d + 1) * B ^ 2 := by
    calc
      D * (B + D * d + 1) ≤ (2 * B) * (2 * B * (d + 1)) :=
        Nat.mul_le_mul hDle hinner
      _ = _ := by ring
  have hDA : D * A + A = 2 * A * B := by
    calc
      D * A + A = (D + 1) * A := by ring
      _ = 2 * A * B := by rw [hD]; ring
  calc
    D * (A + B + D * d + 1) = D * A + D * (B + D * d + 1) := by ring
    _ < D * A + A := Nat.add_lt_add_left (hcost.trans_lt hA) _
    _ = 2 * A * B := hDA

theorem half_characteristic_parameters {p B d : ℕ} (hp : 0 < p) (hB : 1 ≤ B)
    (hsmall : 16 * (d + 1) * B ^ 2 ≤ p) :
    let A := (p - 1) / 2
    let D := 2 * B - 1
    A + A ≤ p ∧ D ≤ p ∧ D * (A + B + D * d + 1) < 2 * A * B := by
  dsimp only
  let A := (p - 1) / 2
  let D := 2 * B - 1
  have hdiv := Nat.div_mul_le_self (p - 1) 2
  have hmod := Nat.mod_add_div (p - 1) 2
  have hmodlt := Nat.mod_lt (p - 1) (by norm_num : 0 < 2)
  have hAlower : p ≤ 2 * A + 2 := by dsimp [A]; omega
  have hAupper : A + A ≤ p := by dsimp [A]; omega
  have hD : D + 1 = 2 * B := by dsimp [D]; omega
  have hBsq : B ≤ B ^ 2 := by nlinarith
  have hterm : 1 ≤ (d + 1) * B ^ 2 := by
    change 0 < (d + 1) * B ^ 2
    positivity
  have hprod : B ^ 2 ≤ (d + 1) * B ^ 2 := by
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hlarge : 4 * (d + 1) * B ^ 2 < A := by nlinarith
  have hDp : D ≤ p := by nlinarith
  exact ⟨hAupper, hDp, constraints_lt_coefficients hB hD hlarge⟩

theorem quadratic_fiber_card_bound_small_square
    {K : Type*} [Field K] {p B : ℕ} [Fact p.Prime] [CharP K p]
    (f : K[X]) {x₀ : K} (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1)
    (hB : 1 ≤ B) (hsmall : 16 * (f.natDegree + 1) * B ^ 2 ≤ p)
    (S : Finset K)
    (hS : ∀ x ∈ S, x ^ p = x ∧ f.eval x ≠ 0 ∧ f.eval x ^ ((p - 1) / 2) = 1) :
    2 * (2 * B - 1) * S.card ≤ p * (2 * B - 1) + p * (f.natDegree + 2) := by
  obtain ⟨hA, hDp, hdim⟩ := half_characteristic_parameters
    (Fact.out : p.Prime).pos hB hsmall
  have hcount := quadratic_fiber_card_bound f hf hroot le_rfl hA hDp hdim S hS
  have hD : (2 * B - 1) + 1 = 2 * B := by omega
  have hAd := Nat.mul_le_mul_right f.natDegree hA
  nlinarith

end Pollack17.Stepanov

end

/-! ### Upstream module `ErdosProblems/Erdos1141/StepanovCharacterSum.lean` -/

section

/-!
# Quadratic character sums of polynomials with a simple root

The two-sided estimate follows by applying the residue-fiber estimate both
to `f` and to a nonsquare scalar multiple of `f`.
-/

namespace Pollack17.Stepanov

open Polynomial
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

noncomputable def residueFiber (f : (ZMod p)[X]) : Finset (ZMod p) :=
  Finset.univ.filter fun x => quadraticChar (ZMod p) (f.eval x) = 1

noncomputable def zeroFiber (f : (ZMod p)[X]) : Finset (ZMod p) :=
  Finset.univ.filter fun x => f.eval x = 0

noncomputable def polynomialCharacterSum (f : (ZMod p)[X]) : ℝ :=
  ∑ x : ZMod p, (quadraticChar (ZMod p) (f.eval x) : ℝ)

theorem polynomialCharacterSum_eq_fibers (f : (ZMod p)[X]) :
    polynomialCharacterSum f = 2 * (residueFiber f).card + (zeroFiber f).card - p := by
  classical
  have hpoint (x : ZMod p) : (quadraticChar (ZMod p) (f.eval x) : ℝ) =
      2 * (if quadraticChar (ZMod p) (f.eval x) = 1 then (1 : ℝ) else 0) +
        (if f.eval x = 0 then 1 else 0) - 1 := by
    by_cases hx : f.eval x = 0
    · simp [hx]
    · rcases quadraticChar_dichotomy hx with h | h <;> norm_num [h, hx]
  have hres : (∑ x : ZMod p,
      if quadraticChar (ZMod p) (f.eval x) = 1 then (1 : ℝ) else 0) = (residueFiber f).card := by
    simp [residueFiber]
  have hzero : (∑ x : ZMod p, if f.eval x = 0 then (1 : ℝ) else 0) = (zeroFiber f).card := by
    simp [zeroFiber]
  simp only [polynomialCharacterSum, hpoint, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, hres, hzero]
  simp

theorem zeroFiber_card_le {f : (ZMod p)[X]} (hf : f ≠ 0) :
    (zeroFiber f).card ≤ f.natDegree := by
  classical
  have hsubset : zeroFiber f ⊆ f.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
    exact (Finset.mem_filter.mp hx).2
  exact ((Finset.card_le_card hsubset).trans (Multiset.toFinset_card_le _)).trans
    (Polynomial.card_roots' f)

theorem residueFiber_spec (f : (ZMod p)[X]) (hp2 : p ≠ 2)
    {x : ZMod p} (hx : x ∈ residueFiber f) :
    x ^ p = x ∧ f.eval x ≠ 0 ∧ f.eval x ^ ((p - 1) / 2) = 1 := by
  have hchar := (Finset.mem_filter.mp hx).2
  have hfx : f.eval x ≠ 0 := by
    intro hzero
    simp [hzero] at hchar
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hpow := quadraticChar_eq_pow_of_char_ne_two' hF (f.eval x)
  have hodd := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hhalf : p / 2 = (p - 1) / 2 := by
    have := Nat.odd_iff.mp hodd
    omega
  refine ⟨?_, hfx, ?_⟩
  · simp
  · simpa only [hchar, Int.cast_one, ZMod.card, hhalf] using hpow.symm

theorem polynomialCharacterSum_le_of_small_square {B : ℕ}
    (f : (ZMod p)[X]) {x₀ : ZMod p} (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1)
    (hp2 : p ≠ 2) (hB : 1 ≤ B) (hsmall : 16 * (f.natDegree + 1) * B ^ 2 ≤ p) :
    polynomialCharacterSum f ≤
      (p : ℝ) * (f.natDegree + 2) / (2 * B - 1 : ℕ) + f.natDegree := by
  have hcount := quadratic_fiber_card_bound_small_square f hf hroot hB hsmall
    (residueFiber f) (fun _ hx => residueFiber_spec f hp2 hx)
  have hcountR : (2 : ℝ) * (2 * B - 1 : ℕ) * (residueFiber f).card ≤
      (p : ℝ) * (2 * B - 1 : ℕ) + (p : ℝ) * (f.natDegree + 2) := by
    exact_mod_cast hcount
  have hzeros : ((zeroFiber f).card : ℝ) ≤ f.natDegree := by exact_mod_cast zeroFiber_card_le hf
  have hDpos : (0 : ℝ) < (2 * B - 1 : ℕ) := by exact_mod_cast (show 0 < 2 * B - 1 by omega)
  have hquot : (2 : ℝ) * (residueFiber f).card - p ≤
      (p : ℝ) * (f.natDegree + 2) / (2 * B - 1 : ℕ) := by
    apply (le_div_iff₀ hDpos).mpr
    nlinarith
  rw [polynomialCharacterSum_eq_fibers]
  linarith

theorem abs_polynomialCharacterSum_le_of_small_square {B : ℕ}
    (f : (ZMod p)[X]) {x₀ : ZMod p} (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1)
    (hp2 : p ≠ 2) (hB : 1 ≤ B) (hsmall : 16 * (f.natDegree + 1) * B ^ 2 ≤ p) :
    |polynomialCharacterSum f| ≤
      (p : ℝ) * (f.natDegree + 2) / (2 * B - 1 : ℕ) + f.natDegree := by
  have hu := polynomialCharacterSum_le_of_small_square f hf hroot hp2 hB hsmall
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hF
  have ha0 : a ≠ 0 := by
    intro hzero
    simp [hzero] at ha
  let g := C a * f
  have hg : g ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr ha0) hf
  have hgroot : g.rootMultiplicity x₀ = 1 := by
    rw [Polynomial.rootMultiplicity_mul hg, Polynomial.rootMultiplicity_C, hroot, zero_add]
  have hgdegree : g.natDegree = f.natDegree := by
    rw [Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr ha0) hf, natDegree_C, zero_add]
  have hl := polynomialCharacterSum_le_of_small_square g hg hgroot hp2 hB
    (by simpa only [hgdegree] using hsmall)
  have hsum : polynomialCharacterSum g = -polynomialCharacterSum f := by
    simp [polynomialCharacterSum, g, map_mul, ha, Finset.sum_neg_distrib]
  rw [hgdegree, hsum] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

theorem abs_polynomialCharacterSum_le_card (f : (ZMod p)[X]) :
    |polynomialCharacterSum f| ≤ p := by
  have hpoint (x : ZMod p) : |(quadraticChar (ZMod p) (f.eval x) : ℝ)| ≤ 1 := by
    rcases quadraticChar_isQuadratic (ZMod p) (f.eval x) with h | h | h <;> norm_num [h]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun x _ => hpoint x)).trans_eq (by simp))

end Pollack17.Stepanov

end

/-! ### Upstream module `ErdosProblems/Erdos1141/StepanovSqrt.lean` -/

section

/-!
# A square-root bound with a degree-dependent constant
-/

namespace Pollack17.Stepanov

open Polynomial

def simpleRootConstant (d : ℕ) : ℕ :=
  32 * (d + 1) + 64 * (d + 1) * (d + 2) + d

theorem sqrt_div_square_small (p c : ℕ) (hc : 0 < c) :
    c * (Nat.sqrt p / c) ^ 2 ≤ p := by
  have hdiv : c * (Nat.sqrt p / c) ≤ Nat.sqrt p := by
    simpa only [mul_comm] using Nat.div_mul_le_self (Nat.sqrt p) c
  have hc2 : c ≤ c ^ 2 := by nlinarith
  calc
    c * (Nat.sqrt p / c) ^ 2 ≤ c ^ 2 * (Nat.sqrt p / c) ^ 2 :=
      Nat.mul_le_mul_right _ hc2
    _ = (c * (Nat.sqrt p / c)) ^ 2 := by ring
    _ ≤ (Nat.sqrt p) ^ 2 := Nat.pow_le_pow_left hdiv 2
    _ ≤ p := Nat.sqrt_le' p

theorem modulus_le_sqrt_mul_div {p c : ℕ} (hp : 0 < p) (hc : 0 < c)
    (hB : 1 ≤ Nat.sqrt p / c) :
    (p : ℝ) ≤ 4 * c * ((Nat.sqrt p / c : ℕ) : ℝ) * Real.sqrt p := by
  let B := Nat.sqrt p / c
  have hmod := Nat.mod_add_div (Nat.sqrt p) c
  have hmodlt := Nat.mod_lt (Nat.sqrt p) hc
  have hfloor : Nat.sqrt p + 1 ≤ c * (B + 1) := by dsimp [B]; nlinarith
  have hnext : Nat.sqrt p + 1 ≤ 2 * c * B := by
    calc
      Nat.sqrt p + 1 ≤ c * (B + 1) := hfloor
      _ ≤ c * (2 * B) := Nat.mul_le_mul_left c (by omega)
      _ = _ := by ring
  have hpn : p ≤ 2 * c * B * (Nat.sqrt p + 1) := by
    calc
      p ≤ (Nat.sqrt p + 1) ^ 2 := (Nat.lt_succ_sqrt' p).le
      _ ≤ (2 * c * B) * (Nat.sqrt p + 1) := by
        simpa only [pow_two] using Nat.mul_le_mul_right (Nat.sqrt p + 1) hnext
  have hpr : (p : ℝ) ≤ 2 * c * B * ((Nat.sqrt p : ℝ) + 1) := by exact_mod_cast hpn
  have hs0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg _)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hs1 : 1 ≤ Real.sqrt (p : ℝ) := by nlinarith
  have hl2 : (Nat.sqrt p : ℝ) ^ 2 ≤ p := by exact_mod_cast Nat.sqrt_le' p
  have hl : (Nat.sqrt p : ℝ) ≤ Real.sqrt p := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.sqrt p)]
  calc
    (p : ℝ) ≤ 2 * c * B * ((Nat.sqrt p : ℝ) + 1) := hpr
    _ ≤ 2 * c * B * (2 * Real.sqrt p) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

/-- A quadratic Weil estimate sufficient for Burgess moments.  The degree
is arbitrary and the only polynomial hypothesis is a simple root. -/
theorem abs_polynomialCharacterSum_le_sqrt
    {p : ℕ} [Fact p.Prime] (f : (ZMod p)[X]) {x₀ : ZMod p}
    (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1) :
    |polynomialCharacterSum f| ≤ (simpleRootConstant f.natDegree : ℝ) * Real.sqrt p := by
  let d := f.natDegree
  let c := 16 * (d + 1)
  let B := Nat.sqrt p / c
  have hc : 0 < c := by dsimp [c]; positivity
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hs0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs1 : 1 ≤ Real.sqrt (p : ℝ) := by nlinarith
  have hC : (simpleRootConstant d : ℝ) =
      2 * c + 4 * c * (d + 2) + d := by
    simp only [simpleRootConstant, c, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  by_cases hlarge : 2 * c ≤ Nat.sqrt p
  · have hB2 : 2 ≤ B := (Nat.le_div_iff_mul_le hc).mpr (by simpa only [mul_comm] using hlarge)
    have hB : 1 ≤ B := by omega
    have hp2 : p ≠ 2 := by
      have hsp := Nat.sqrt_le_self p
      have hc16 : 16 ≤ c := by dsimp [c]; omega
      omega
    have hsmall : 16 * (f.natDegree + 1) * B ^ 2 ≤ p := sqrt_div_square_small p c hc
    have hraw := abs_polynomialCharacterSum_le_of_small_square f hf hroot hp2 hB hsmall
    have hpb : (p : ℝ) ≤ 4 * c * B * Real.sqrt p := modulus_le_sqrt_mul_div hp hc hB
    have hDB : (B : ℝ) ≤ (2 * B - 1 : ℕ) := by exact_mod_cast (show B ≤ 2 * B - 1 by omega)
    have hD0 : (0 : ℝ) < (2 * B - 1 : ℕ) := by exact_mod_cast (show 0 < 2 * B - 1 by omega)
    have hpD : (p : ℝ) ≤ 4 * c * (2 * B - 1 : ℕ) * Real.sqrt p := by
      apply hpb.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hDB (by positivity)) hs0
    have hquot : (p : ℝ) * (d + 2) / (2 * B - 1 : ℕ) ≤
        4 * c * (d + 2) * Real.sqrt p := by
      apply (div_le_iff₀ hD0).mpr
      have h := mul_le_mul_of_nonneg_right hpD (show (0 : ℝ) ≤ d + 2 by positivity)
      nlinarith
    have hd : (d : ℝ) ≤ d * Real.sqrt p := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hs1 (Nat.cast_nonneg d)
    calc
      |polynomialCharacterSum f| ≤ (p : ℝ) * (d + 2) / (2 * B - 1 : ℕ) + d := hraw
      _ ≤ 4 * c * (d + 2) * Real.sqrt p + d * Real.sqrt p := add_le_add hquot hd
      _ ≤ (simpleRootConstant d : ℝ) * Real.sqrt p := by
        rw [hC]
        have : 0 ≤ 2 * (c : ℝ) * Real.sqrt p := by positivity
        nlinarith
  · have hnext : Nat.sqrt p + 1 ≤ 2 * c := by omega
    have hpbound : p ≤ (2 * c) ^ 2 :=
      (Nat.lt_succ_sqrt' p).le.trans (Nat.pow_le_pow_left hnext 2)
    have hpboundR : (p : ℝ) ≤ (2 * c) ^ 2 := by exact_mod_cast hpbound
    have hsr : Real.sqrt (p : ℝ) ≤ 2 * c := by
      nlinarith [Nat.cast_nonneg (α := ℝ) c]
    have hpc : (p : ℝ) ≤ 2 * c * Real.sqrt p := by nlinarith
    calc
      |polynomialCharacterSum f| ≤ p := abs_polynomialCharacterSum_le_card f
      _ ≤ 2 * c * Real.sqrt p := hpc
      _ ≤ (simpleRootConstant d : ℝ) * Real.sqrt p := by
        rw [hC]
        apply mul_le_mul_of_nonneg_right _ hs0
        have : 0 ≤ 4 * (c : ℝ) * (d + 2) + d := by positivity
        linarith

end Pollack17.Stepanov

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessMoments.lean` -/

section

/-!
# Arbitrary moments of shifted quadratic character sums
-/

namespace Pollack17.Burgess

open Polynomial
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

noncomputable def qchar (x : ZMod p) : ℝ := (quadraticChar (ZMod p) x : ℝ)


noncomputable def shiftPolynomial {n : ℕ} (v : Fin n → ZMod p) : (ZMod p)[X] :=
  ∏ i : Fin n, (X + C (v i))

theorem shiftPolynomial_ne_zero {n : ℕ} (v : Fin n → ZMod p) : shiftPolynomial v ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact Polynomial.X_add_C_ne_zero (v i)

theorem shiftPolynomial_natDegree {n : ℕ} (v : Fin n → ZMod p) :
    (shiftPolynomial v).natDegree = n := by
  rw [shiftPolynomial, Polynomial.natDegree_prod]
  · simp
  · intro i _
    exact Polynomial.X_add_C_ne_zero (v i)

theorem shiftPolynomial_simple_root {n : ℕ} (v : Fin n → ZMod p) (i : Fin n)
    (hsingle : ∀ j : Fin n, j ≠ i → v j ≠ v i) :
    (shiftPolynomial v).rootMultiplicity (-v i) = 1 := by
  classical
  let Q : (ZMod p)[X] := ∏ j ∈ Finset.univ.erase i, (X + C (v j))
  have hfactor : shiftPolynomial v = (X + C (v i)) * Q := by
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hQeval : Q.eval (-v i) ≠ 0 := by
    simp only [Q, eval_prod, eval_add, eval_X, eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hne := hsingle j (Finset.mem_erase.mp hj).1
    simpa only [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr hne
  have hQroot : Q.rootMultiplicity (-v i) = 0 := Polynomial.rootMultiplicity_eq_zero hQeval
  have hmul : (X + C (v i)) * Q ≠ 0 := hfactor ▸ shiftPolynomial_ne_zero v
  rw [hfactor, Polynomial.rootMultiplicity_mul hmul, hQroot, add_zero]
  simpa only [map_neg, sub_neg_eq_add] using
    (Polynomial.rootMultiplicity_X_sub_C_self (x := -v i))

theorem correlation_le_of_singleton {n : ℕ} (v : Fin n → ZMod p)
    (hsingle : ∃ i : Fin n, ∀ j : Fin n, j ≠ i → v j ≠ v i) :
    |∑ x : ZMod p, qchar (∏ i : Fin n, (x + v i))| ≤
      (Stepanov.simpleRootConstant n : ℝ) * Real.sqrt p := by
  obtain ⟨i, hi⟩ := hsingle
  have h := Stepanov.abs_polynomialCharacterSum_le_sqrt (shiftPolynomial v)
    (shiftPolynomial_ne_zero v) (shiftPolynomial_simple_root v i hi)
  rw [shiftPolynomial_natDegree] at h
  simpa only [Stepanov.polynomialCharacterSum, shiftPolynomial, eval_prod,
    eval_add, eval_X, eval_C, qchar] using h



end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/RepeatedTuples.lean` -/

section

/-!
# Counting tuples with no singleton entry

An exceptional tuple in a Burgess moment has at most half as many distinct
entries as positions.  Encoding its distinct entries and a map into their
labels gives a bound valid for every moment order.
-/

namespace Pollack17.Burgess

open scoped BigOperators

def RepeatedTuple {α : Type*} {n : ℕ} (v : Fin n → α) : Prop :=
  ∀ i : Fin n, ∃ j : Fin n, j ≠ i ∧ v j = v i

theorem repeatedTuple_image_card {α : Type*} [DecidableEq α] {n : ℕ}
    (v : Fin n → α) (hv : RepeatedTuple v) :
    2 * (Finset.univ.image v).card ≤ n := by
  have hfiber (a : α) (ha : a ∈ Finset.univ.image v) :
      2 ≤ (Finset.univ.filter fun i => v i = a).card := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hji, hval⟩ := hv i
    apply Finset.one_lt_card.mpr
    exact ⟨i, by simp, j, by simp [hval], hji.symm⟩
  calc
    2 * (Finset.univ.image v).card = ∑ _a ∈ Finset.univ.image v, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ a ∈ Finset.univ.image v, (Finset.univ.filter fun i => v i = a).card :=
      Finset.sum_le_sum hfiber
    _ = n := by simpa using (Finset.card_eq_sum_card_image v Finset.univ).symm

theorem exists_tuple_factorization {α : Type*} [DecidableEq α] {n r : ℕ}
    (hn : 0 < n) (v : Fin n → α) (hcard : (Finset.univ.image v).card ≤ r) :
    ∃ a : Fin r → α, ∃ b : Fin n → Fin r, v = a ∘ b := by
  classical
  let S := Finset.univ.image v
  let e : S ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
  let z : Fin n → S := fun i => ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let b : Fin n → Fin r := fun i => ⟨(e (z i)).val, (e (z i)).isLt.trans_le hcard⟩
  let a : Fin r → α := fun j =>
    if h : j.val < S.card then (e.symm ⟨j.val, h⟩).val else v ⟨0, hn⟩
  refine ⟨a, b, ?_⟩
  funext i
  dsimp only [Function.comp_apply, a, b]
  rw [dif_pos (e (z i)).isLt]
  exact (congrArg Subtype.val (e.symm_apply_apply (z i))).symm

noncomputable def repeatedTuples (α : Type*) [Fintype α] (n : ℕ) : Finset (Fin n → α) := by
  classical
  exact Finset.univ.filter RepeatedTuple

theorem repeatedTuples_card_le (α : Type*) [Fintype α] (r : ℕ) :
    (repeatedTuples α (2 * r)).card ≤ (Fintype.card α) ^ r * r ^ (2 * r) := by
  classical
  by_cases hr : r = 0
  · subst r
    simpa [repeatedTuples] using
      (Finset.card_filter_le (Finset.univ : Finset (Fin 0 → α)) RepeatedTuple)
  let T : Finset ((Fin r → α) × (Fin (2 * r) → Fin r)) := Finset.univ
  let compose : ((Fin r → α) × (Fin (2 * r) → Fin r)) → (Fin (2 * r) → α) :=
    fun ab => ab.1 ∘ ab.2
  have hsubset : repeatedTuples α (2 * r) ⊆ T.image compose := by
    intro v hv
    have hrep : RepeatedTuple v := (Finset.mem_filter.mp hv).2
    have htwice := repeatedTuple_image_card v hrep
    have hcard : (Finset.univ.image v).card ≤ r := by omega
    obtain ⟨a, b, hab⟩ := exists_tuple_factorization (by omega : 0 < 2 * r) v hcard
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, hab.symm⟩
  calc
    (repeatedTuples α (2 * r)).card ≤ (T.image compose).card := Finset.card_le_card hsubset
    _ ≤ T.card := Finset.card_image_le
    _ = (Fintype.card α) ^ r * r ^ (2 * r) := by simp [T]

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessPrimeMoment.lean` -/

section

/-!
# The complete prime-field Burgess moment estimate for every order
-/

namespace Pollack17.Burgess

open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]



end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/QuadraticCRT.lean` -/

section

/-!
# Products of local quadratic characters

The Chinese remainder interface is independent of the moment order.
-/

namespace Pollack17.Burgess

open scoped BigOperators

def primeModulus (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

theorem primeModulus_pos (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    0 < primeModulus s := Finset.prod_pos (fun p hp => (hs p hp).pos)

theorem primeSet_pairwise (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Pairwise (fun p r : s => Nat.Coprime (p : ℕ) (r : ℕ)) := by
  intro p r hpr
  exact (hs p p.property).coprime_iff_not_dvd.mpr fun hdvd =>
    hpr (Subtype.ext ((Nat.prime_dvd_prime_iff_eq (hs p p.property)
      (hs r r.property)).mp hdvd))

noncomputable def primeCRT (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ZMod (primeModulus s) ≃+* (∀ p : s, ZMod (p : ℕ)) := by
  have hprod : primeModulus s = ∏ p : s, (p : ℕ) :=
    (Finset.prod_attach s (fun p : ℕ => p)).symm
  exact (ZMod.ringEquivCongr hprod).trans
    (ZMod.prodEquivPi (fun p : s => (p : ℕ)) (primeSet_pairwise s hs))

theorem primeCRT_natCast (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (n : ℕ) (p : s) :
    primeCRT s hs (n : ZMod (primeModulus s)) p = (n : ZMod (p : ℕ)) := by
  simp [primeCRT]

noncomputable def localChar (p : ℕ) (hp : p.Prime) (x : ZMod p) : ℝ :=
  @qchar p ⟨hp⟩ x

noncomputable def productChar (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (x : ZMod (primeModulus s)) : ℝ :=
  ∏ p : s, localChar p (hs p p.property) (primeCRT s hs x p)

theorem productChar_mul (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (a b : ZMod (primeModulus s)) :
    productChar s hs (a * b) = productChar s hs a * productChar s hs b := by
  simp [productChar, localChar, qchar, map_mul, Finset.prod_mul_distrib]

theorem abs_localChar_le_one (p : ℕ) (hp : p.Prime) (x : ZMod p) :
    |localChar p hp x| ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rcases quadraticChar_isQuadratic (ZMod p) x with h | h | h <;>
    norm_num [localChar, qchar, h]

theorem abs_productChar_le_one (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (x : ZMod (primeModulus s)) : |productChar s hs x| ≤ 1 := by
  rw [productChar, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) fun p _ =>
    abs_localChar_le_one p (hs p p.property) _

theorem productChar_complete_correlation (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] [(p : s) → NeZero (p : ℕ)] {n : ℕ} (v : Fin n → ℕ) :
    (∑ x : ZMod (primeModulus s),
        productChar s hs (∏ i : Fin n, (x + v i))) =
      ∏ p : s, ∑ y : ZMod (p : ℕ),
        localChar p (hs p p.property) (∏ i : Fin n, (y + v i)) := by
  let e := primeCRT s hs
  calc
    _ = ∑ y : (∀ p : s, ZMod (p : ℕ)),
        ∏ p : s, localChar p (hs p p.property) (∏ i : Fin n, (y p + v i)) := by
      rw [← e.toEquiv.sum_comp]
      apply Finset.sum_congr rfl
      intro x _
      rw [productChar]
      apply Fintype.prod_congr
      intro p
      congr 1
      simp [e]
    _ = _ := by rw [Fintype.prod_sum]

theorem prod_prime_gcd (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (d : ℕ) :
    (∏ p ∈ s, p.gcd d) = (primeModulus s).gcd d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [primeModulus]
  | @insert p s hp ih =>
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (Finset.mem_insert_of_mem hr)
    have hpp : p.Prime := hs p (Finset.mem_insert_self p s)
    have hcop : p.Coprime (primeModulus s) := Nat.Coprime.prod_right fun r hr =>
      hpp.coprime_iff_not_dvd.mpr fun hdvd =>
        hp ((Nat.prime_dvd_prime_iff_eq hpp (hs' r hr)).mp hdvd ▸ hr)
    rw [Finset.prod_insert hp, ih hs']
    rw [show primeModulus (insert p s) = p * primeModulus s from Finset.prod_insert hp]
    rw [Nat.gcd_comm (p * primeModulus s), hcop.gcd_mul d,
      Nat.gcd_comm d p, Nat.gcd_comm d (primeModulus s)]

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessSubpower.lean` -/

section

/-!
# Subpower losses from the number of prime factors

The factorial argument is extracted from `Erdos587.NVDevelopment`.
-/

namespace Pollack17.Burgess

open Filter
open scoped BigOperators

lemma factorial_card_le_prod_of_one_le (s : Finset ℕ)
    (hs : ∀ x ∈ s, 1 ≤ x) :
    Nat.factorial s.card ≤ ∏ x ∈ s, x := by
  classical
  let f : Fin s.card ↪o ℕ := s.orderEmbOfFin rfl
  have hidx : ∀ i : ℕ, ∀ hi : i < s.card, i + 1 ≤ f ⟨i, hi⟩ := by
    intro i hi
    induction i with
    | zero =>
        have hmem : f ⟨0, hi⟩ ∈ s := by
          simp [f]
        simpa [f] using hs (f ⟨0, hi⟩) hmem
    | succ i ih =>
        have hi' : i < s.card := Nat.lt_of_succ_lt hi
        have hprev : i + 1 ≤ f ⟨i, hi'⟩ := ih hi'
        have hlt : f ⟨i, hi'⟩ < f ⟨i + 1, hi⟩ := by
          exact f.strictMono (Nat.lt_succ_self i)
        exact le_trans (Nat.succ_le_succ hprev) (Nat.succ_le_of_lt hlt)
  have hprod : (∏ i : Fin s.card, (i.1 + 1)) ≤ ∏ i : Fin s.card, f i := by
    refine Finset.prod_le_prod' ?_
    intro i _
    exact hidx i.1 i.2
  have hleft : (∏ i : Fin s.card, (i.1 + 1)) = Nat.factorial s.card := by
    calc
      (∏ i : Fin s.card, (i.1 + 1)) =
          ∏ i ∈ Finset.range s.card, (i + 1) := by
        simpa using (Fin.prod_univ_eq_prod_range (fun i : ℕ => i + 1) s.card)
      _ = Nat.factorial s.card := Finset.prod_range_add_one_eq_factorial s.card
  have hright : (∏ i : Fin s.card, f i) = ∏ x ∈ s, x := by
    calc
      (∏ i : Fin s.card, f i) =
          ∏ x ∈ Finset.map (s.orderEmbOfFin rfl).toEmbedding Finset.univ, x := by
        symm
        simpa [f] using
          (Finset.prod_map (s := Finset.univ)
            (e := (s.orderEmbOfFin rfl).toEmbedding) (f := fun x : ℕ => x))
      _ = ∏ x ∈ s, x := by
        rw [Finset.map_orderEmbOfFin_univ (s := s) (h := rfl)]
  calc
    Nat.factorial s.card = ∏ i : Fin s.card, (i.1 + 1) := hleft.symm
    _ ≤ ∏ i : Fin s.card, f i := hprod
    _ = ∏ x ∈ s, x := hright

/-- The factorial of the number of distinct prime factors of a nonzero
natural is bounded by the natural itself. -/
lemma factorial_card_primeFactors_le (n : ℕ) (hn : n ≠ 0) :
    Nat.factorial n.primeFactors.card ≤ n := by
  have hprod : Nat.factorial n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
    factorial_card_le_prod_of_one_le _ (by
      intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).one_le)
  exact hprod.trans
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n))

/-- For fixed `b` and positive `m`, the loss `b ^ ω(n)` is eventually at
most `n ^ (1 / m)`.  This is the exact subpower input needed to absorb the
`3 ^ ω(q)` CRT loss in the quadratic Burgess fourth moment. -/
theorem const_pow_primeFactors_card_le_rpow_eventually
    (b m : ℕ) (hb : 1 ≤ b) (hm : 0 < m) :
    ∃ Nω : ℕ, ∀ {n : ℕ}, Nω ≤ n →
      (b : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) ^ ((1 : ℝ) / m) := by
  have hfact : ∀ᶠ k : ℕ in atTop, (b ^ m) ^ k < Nat.factorial (k - 1) := by
    simpa using (Nat.eventually_pow_lt_factorial_sub (b ^ m) 1)
  rcases eventually_atTop.mp hfact with ⟨k₀, hk₀⟩
  refine ⟨max 3 ((b ^ k₀) ^ m), ?_⟩
  intro n hn
  let k := n.primeFactors.card
  have hn3 : 3 ≤ n := (Nat.le_max_left _ _).trans hn
  have hnpos : 0 < n := by omega
  by_cases hk_small : k < k₀
  · have hk_le : k ≤ k₀ := hk_small.le
    have hpow_nat : (b ^ k : ℕ) ≤ b ^ k₀ :=
      Nat.pow_le_pow_right (by omega : 0 < b) hk_le
    have hpow_real : (b : ℝ) ^ k ≤ (b : ℝ) ^ k₀ := by
      exact_mod_cast hpow_nat
    have hconst_nat : ((b ^ k₀ : ℕ) ^ m) ≤ n :=
      (Nat.le_max_right _ _).trans hn
    have hconst_real : (((b : ℝ) ^ k₀) ^ m) ≤ (n : ℝ) := by
      exact_mod_cast hconst_nat
    have hroot_le :
        (((b : ℝ) ^ k₀) ^ m) ^ ((1 : ℝ) / m) ≤
          (n : ℝ) ^ ((1 : ℝ) / m) := by
      exact Real.rpow_le_rpow (by positivity) hconst_real (by positivity)
    have hroot :
        (((b : ℝ) ^ k₀) ^ m) ^ ((1 : ℝ) / m) = (b : ℝ) ^ k₀ := by
      simpa [one_div] using
        Real.pow_rpow_inv_natCast (show 0 ≤ (b : ℝ) ^ k₀ by positivity)
          (Nat.ne_of_gt hm)
    rw [hroot] at hroot_le
    exact hpow_real.trans hroot_le
  · have hk_ge : k₀ ≤ k := Nat.le_of_not_gt hk_small
    have hmain_nat : (b ^ m) ^ k < Nat.factorial k := by
      exact (hk₀ k hk_ge).trans_le (Nat.factorial_le (Nat.sub_le _ _))
    have hk_fact_le_n : Nat.factorial k ≤ n := by
      simpa [k] using factorial_card_primeFactors_le n (Nat.ne_of_gt hnpos)
    have hpowm_nat' : (b ^ m) ^ k ≤ n :=
      (Nat.le_of_lt hmain_nat).trans hk_fact_le_n
    have hpowm_nat : (b ^ k : ℕ) ^ m ≤ n := by
      calc
        (b ^ k : ℕ) ^ m = b ^ (k * m) := by rw [pow_mul]
        _ = b ^ (m * k) := by rw [Nat.mul_comm]
        _ = (b ^ m) ^ k := by rw [pow_mul]
        _ ≤ n := hpowm_nat'
    have hpowm_real : (((b : ℝ) ^ k) ^ m) ≤ (n : ℝ) := by
      exact_mod_cast hpowm_nat
    have hroot_le :
        (((b : ℝ) ^ k) ^ m) ^ ((1 : ℝ) / m) ≤
          (n : ℝ) ^ ((1 : ℝ) / m) := by
      exact Real.rpow_le_rpow (by positivity) hpowm_real (by positivity)
    have hroot :
        (((b : ℝ) ^ k) ^ m) ^ ((1 : ℝ) / m) = (b : ℝ) ^ k := by
      simpa [one_div] using
        Real.pow_rpow_inv_natCast (show 0 ≤ (b : ℝ) ^ k by positivity)
          (Nat.ne_of_gt hm)
    rw [hroot] at hroot_le
    exact hroot_le

theorem primeModulus_primeFactors (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (primeModulus s).primeFactors = s := Nat.primeFactors_prod hs

theorem primeModulus_card_divisors (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (primeModulus s).divisors.card = 2 ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [primeModulus]
  | @insert p s hp ih =>
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (Finset.mem_insert_of_mem hr)
    have hpp : p.Prime := hs p (Finset.mem_insert_self p s)
    have hcop : p.Coprime (primeModulus s) := Nat.Coprime.prod_right fun r hr =>
      hpp.coprime_iff_not_dvd.mpr fun hdvd =>
        hp ((Nat.prime_dvd_prime_iff_eq hpp (hs' r hr)).mp hdvd ▸ hr)
    rw [show primeModulus (insert p s) = p * primeModulus s from Finset.prod_insert hp,
      hcop.card_divisors_mul, ih hs', Finset.card_insert_of_notMem hp, pow_succ', hpp.divisors]
    have hpne : p ≠ 1 := hpp.ne_one
    simp [Ne.symm hpne]

theorem eventually_const_pow_primeFactors_le (b : ℕ) (hb : 1 ≤ b)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, (b : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) ^ δ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
  have hmpos : 0 < m := by
    have hreal : 0 < (m : ℝ) := lt_trans (one_div_pos.mpr hδ) hm
    exact_mod_cast hreal
  have hexp : (1 : ℝ) / m ≤ δ := by
    have hprod : 1 < (m : ℝ) * δ := (div_lt_iff₀ hδ).mp hm
    exact (div_le_iff₀ (by exact_mod_cast hmpos : 0 < (m : ℝ))).mpr (by nlinarith)
  obtain ⟨Q, hQ⟩ := const_pow_primeFactors_card_le_rpow_eventually b m hb hmpos
  filter_upwards [eventually_ge_atTop Q, eventually_ge_atTop 1] with q hq hq1
  exact (hQ hq).trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq1) hexp)


theorem eventually_const_mul_pow_primeFactors_le (K : ℝ) (b : ℕ) (hb : 1 ≤ b)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, K * (b : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) ^ δ := by
  have hp := eventually_const_pow_primeFactors_le b hb (half_pos hδ)
  have hK : ∀ᶠ q : ℕ in atTop, K ≤ (q : ℝ) ^ (δ / 2) :=
    ((tendsto_rpow_atTop (half_pos hδ)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop K)
  filter_upwards [hp, hK, eventually_ge_atTop 1] with q hq hKq hq1
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq1
  calc
    K * (b : ℝ) ^ q.primeFactors.card ≤
        (q : ℝ) ^ (δ / 2) * (q : ℝ) ^ (δ / 2) :=
      mul_le_mul hKq hq (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hqpos.le _)
    _ = (q : ℝ) ^ δ := by rw [← Real.rpow_add hqpos]; congr 1; ring

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessPowerScales.lean` -/

section

/-!
# Elementary estimates for the power scales in Burgess averaging
-/

namespace Pollack17.Burgess

open Filter

theorem eventually_const_mul_rpow_le {C d a b : ℝ} (hd : 0 < d) (hab : a < b) :
    ∀ᶠ q : ℕ in atTop, C * (q : ℝ) ^ a ≤ d * (q : ℝ) ^ b := by
  have hlarge := ((tendsto_rpow_atTop (sub_pos.mpr hab)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (C / d))
  filter_upwards [hlarge, eventually_ge_atTop 1] with q hq hq1
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq1
  have hratio : C ≤ d * (q : ℝ) ^ (b - a) := by
    simpa only [mul_comm, Function.comp_apply] using (div_le_iff₀ hd).mp hq
  calc
    _ ≤ (d * (q : ℝ) ^ (b - a)) * (q : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hq0.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hq0]; congr 2; ring

theorem eventually_floor_rpow_bounds {a : ℝ} (ha : 0 < a) :
    ∀ᶠ q : ℕ in atTop,
      (q : ℝ) ^ a / 2 ≤ (⌊(q : ℝ) ^ a⌋₊ : ℝ) ∧
        (⌊(q : ℝ) ^ a⌋₊ : ℝ) ≤ (q : ℝ) ^ a := by
  have hlarge := ((tendsto_rpow_atTop ha).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop 2)
  filter_upwards [hlarge] with q hq
  change 2 ≤ (q : ℝ) ^ a at hq
  refine ⟨?_, Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg q) _)⟩
  have hfloor := Nat.lt_floor_add_one ((q : ℝ) ^ a)
  linarith

theorem ceil_rpow_bounds {a : ℝ} (ha : 0 ≤ a) {q : ℕ} (hq : 1 ≤ q) :
    (q : ℝ) ^ a ≤ (⌈(q : ℝ) ^ a⌉₊ : ℝ) ∧
      (⌈(q : ℝ) ^ a⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ a := by
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ a := Real.one_le_rpow (by exact_mod_cast hq) ha
  refine ⟨Nat.le_ceil _, ?_⟩
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg q) a)
  linarith

theorem eventually_one_add_log_le_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, 1 + Real.log (q : ℝ) ≤ (q : ℝ) ^ δ := by
  have hcomp := eventually_const_mul_rpow_le
    (C := 1 + (δ / 2)⁻¹) (d := 1) (a := δ / 2) (b := δ) (by norm_num) (by linarith)
  filter_upwards [hcomp, eventually_ge_atTop 1] with q hq hq1
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ (δ / 2) :=
    Real.one_le_rpow (by exact_mod_cast hq1) (by linarith)
  have hlog := Real.log_natCast_le_rpow_div q (half_pos hδ)
  change Real.log (q : ℝ) ≤ (q : ℝ) ^ (δ / 2) * (δ / 2)⁻¹ at hlog
  have hbound : 1 + Real.log (q : ℝ) ≤
      (1 + (δ / 2)⁻¹) * (q : ℝ) ^ (δ / 2) := by
    nlinarith
  exact hbound.trans (by simpa only [one_mul] using hq)

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessGcdAverage.lean` -/

section

/-!
# Averaging the gcd losses in composite-modulus correlations
-/

namespace Pollack17.Burgess

open scoped BigOperators

theorem gcd_le_divisor_sum {q : ℕ} (hq : q ≠ 0) (n : ℕ) :
    q.gcd n ≤ ∑ d ∈ q.divisors, if d ∣ n then d else 0 := by
  have hg : q.gcd n ∈ q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left q n, hq⟩
  calc
    q.gcd n = (if q.gcd n ∣ n then q.gcd n else 0) := by simp [Nat.gcd_dvd_right]
    _ ≤ _ := Finset.single_le_sum (s := q.divisors)
      (f := fun d => if d ∣ n then d else 0) (fun _ _ => Nat.zero_le _) hg

theorem sum_gcd_Icc_le {q : ℕ} (hq : q ≠ 0) (V : ℕ) :
    (∑ n ∈ Finset.Icc 1 V, q.gcd n) ≤ V * q.divisors.card := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 V, ∑ d ∈ q.divisors, if d ∣ n then d else 0 :=
      Finset.sum_le_sum fun n _ => gcd_le_divisor_sum hq n
    _ = ∑ d ∈ q.divisors, ∑ n ∈ Finset.Icc 1 V, if d ∣ n then d else 0 :=
      Finset.sum_comm
    _ = ∑ d ∈ q.divisors, d * (V / d) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [← Finset.sum_filter]
      change (∑ _n ∈ positiveMultiplesUpTo d V, d) = _
      simp [positiveMultiplesUpTo_card, Nat.mul_comm]
    _ ≤ ∑ _d ∈ q.divisors, V :=
      Finset.sum_le_sum fun d _ => Nat.mul_div_le V d
    _ = _ := by simp [Nat.mul_comm]

theorem sum_gcd_dist_one_side_le {q V a : ℕ} (hq : q ≠ 0) (ha : a ≤ V)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 V)
    (hne : ∀ b ∈ S, b ≠ a)
    (hside : (∀ b ∈ S, b ≤ a) ∨ (∀ b ∈ S, a ≤ b)) :
    (∑ b ∈ S, q.gcd (Nat.dist a b)) ≤ V * q.divisors.card := by
  have hinj : Set.InjOn (Nat.dist a) S := by
    intro b hb c hc hbc
    rcases hside with hl | hr
    · have hb' := hl b hb
      have hc' := hl c hc
      rw [Nat.dist_eq_sub_of_le_right hb', Nat.dist_eq_sub_of_le_right hc'] at hbc
      omega
    · have hb' := hr b hb
      have hc' := hr c hc
      rw [Nat.dist_eq_sub_of_le hb', Nat.dist_eq_sub_of_le hc'] at hbc
      omega
  have hsub : S.image (Nat.dist a) ⊆ Finset.Icc 1 V := by
    intro n hn
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hn
    have hbV := (Finset.mem_Icc.mp (hS hb)).2
    have hbne := hne b hb
    simp only [Finset.mem_Icc, Nat.dist]
    omega
  calc
    _ = ∑ n ∈ S.image (Nat.dist a), q.gcd n := (Finset.sum_image hinj).symm
    _ ≤ ∑ n ∈ Finset.Icc 1 V, q.gcd n := Finset.sum_le_sum_of_subset hsub
    _ ≤ _ := sum_gcd_Icc_le hq V

theorem sum_gcd_dist_erase_le {q V a : ℕ} (hq : q ≠ 0) (ha : a ≤ V) :
    (∑ b ∈ (Finset.Icc 1 V).erase a, q.gcd (Nat.dist a b)) ≤
      2 * V * q.divisors.card := by
  let L := (Finset.Icc 1 V).filter (fun b => b < a)
  let R := (Finset.Icc 1 V).filter (fun b => a < b)
  have heq : (Finset.Icc 1 V).erase a = L ∪ R := by
    ext b
    simp only [Finset.mem_erase, L, R, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hdisj : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro b hbL hbR
    have hL := (Finset.mem_filter.mp hbL).2
    have hR := (Finset.mem_filter.mp hbR).2
    omega
  rw [heq, Finset.sum_union hdisj]
  have hL := sum_gcd_dist_one_side_le hq ha L (Finset.filter_subset _ _)
    (fun b hb => ne_of_lt (Finset.mem_filter.mp hb).2)
    (Or.inl (fun b hb => le_of_lt (Finset.mem_filter.mp hb).2))
  have hR := sum_gcd_dist_one_side_le hq ha R (Finset.filter_subset _ _)
    (fun b hb => ne_of_gt (Finset.mem_filter.mp hb).2)
    (Or.inr (fun b hb => le_of_lt (Finset.mem_filter.mp hb).2))
  nlinarith

theorem modEq_iff_dvd_dist (p a b : ℕ) : a ≡ b [MOD p] ↔ p ∣ Nat.dist a b := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab, Nat.modEq_iff_dvd' hab]
  · rw [Nat.dist_eq_sub_of_le_right hba, Nat.ModEq.comm, Nat.modEq_iff_dvd' hba]

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessCompositeCorrelation.lean` -/

section

/-!
# Complete composite correlations with gcd losses

A distinguished shift gives a simple root at every prime which does not
divide one of its differences from the other shifts. The remaining local
factors are bounded trivially and charged to these gcds.
-/

namespace Pollack17.Burgess

open scoped BigOperators

theorem simpleRootConstant_one_le (n : ℕ) : 1 ≤ Stepanov.simpleRootConstant n := by
  unfold Stepanov.simpleRootConstant
  omega

theorem local_correlation_le_gcd {p : ℕ} (hp : p.Prime) [NeZero p]
    {n : ℕ} (v : Fin n → ℕ) (i : Fin n) :
    |∑ x : ZMod p, localChar p hp (∏ j : Fin n, (x + v j))| ≤
      (Stepanov.simpleRootConstant n : ℝ) * Real.sqrt p *
        ∏ j ∈ Finset.univ.erase i, (p.gcd (Nat.dist (v i) (v j)) : ℝ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let g : Fin n → ℕ := fun j => p.gcd (Nat.dist (v i) (v j))
  have hg : ∀ j : Fin n, 1 ≤ g j := fun j => Nat.gcd_pos_of_pos_left _ hp.pos
  have hprod : (1 : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, (g j : ℝ) := by
    exact_mod_cast Finset.one_le_prod' (s := Finset.univ.erase i) (fun j _ => hg j)
  have hbase : (1 : ℝ) ≤ (Stepanov.simpleRootConstant n : ℝ) * Real.sqrt p := by
    have hC : (1 : ℝ) ≤ Stepanov.simpleRootConstant n := by
      exact_mod_cast simpleRootConstant_one_le n
    have hS : (1 : ℝ) ≤ Real.sqrt p :=
      Real.one_le_sqrt.mpr (by exact_mod_cast hp.one_lt.le)
    nlinarith
  by_cases hsingle : ∀ j : Fin n, j ≠ i → (v j : ZMod p) ≠ v i
  · have hcorr := correlation_le_of_singleton (fun j => (v j : ZMod p)) ⟨i, hsingle⟩
    exact hcorr.trans (le_mul_of_one_le_right (le_trans zero_le_one hbase) hprod)
  · push Not at hsingle
    obtain ⟨j, hji, hval⟩ := hsingle
    have hdiv : p ∣ Nat.dist (v i) (v j) :=
      (modEq_iff_dvd_dist p (v i) (v j)).mp
        ((ZMod.natCast_eq_natCast_iff _ _ _).mp hval.symm)
    have hgj : g j = p := Nat.gcd_eq_left_iff_dvd.mpr hdiv
    have hpProd : (p : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, (g j : ℝ) := by
      have h := Finset.single_le_prod' (s := Finset.univ.erase i)
        (fun j _ => hg j) (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
      rw [hgj] at h
      exact_mod_cast h
    have htrivial : |∑ x : ZMod p, localChar p hp (∏ j : Fin n, (x + v j))| ≤ p := by
      calc
        _ ≤ ∑ x : ZMod p, |localChar p hp (∏ j : Fin n, (x + v j))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _x : ZMod p, (1 : ℝ) :=
          Finset.sum_le_sum fun x _ => abs_localChar_le_one p hp _
        _ = _ := by simp
    exact htrivial.trans (hpProd.trans
      (le_mul_of_one_le_left (le_trans zero_le_one hprod) hbase))

theorem product_correlation_le_gcd (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] {n : ℕ} (v : Fin n → ℕ) (i : Fin n) :
    |∑ x : ZMod (primeModulus s), productChar s hs (∏ j : Fin n, (x + v j))| ≤
      (Stepanov.simpleRootConstant n : ℝ) ^ s.card * Real.sqrt (primeModulus s) *
        ∏ j ∈ Finset.univ.erase i, ((primeModulus s).gcd (Nat.dist (v i) (v j)) : ℝ) := by
  classical
  have : (p : s) → NeZero (p : ℕ) := fun p => ⟨(hs p p.property).ne_zero⟩
  rw [productChar_complete_correlation s hs v, Finset.abs_prod]
  refine (Finset.prod_le_prod (s := (Finset.univ : Finset s)) (fun _ _ => abs_nonneg _)
    (fun (p : s) _ => local_correlation_le_gcd (hs p p.property) v i)).trans_eq ?_
  simp only [Finset.prod_mul_distrib]
  have hC : (∏ _p : s, (Stepanov.simpleRootConstant n : ℝ)) =
      (Stepanov.simpleRootConstant n : ℝ) ^ s.card := by simp
  have hsqrt : (∏ p : s, Real.sqrt (p : ℕ)) = Real.sqrt (primeModulus s) := by
    rw [← Real.sqrt_prod _ (fun p _ => Nat.cast_nonneg _), ← Nat.cast_prod]
    congr 2
    exact Finset.prod_attach s (fun p : ℕ => p)
  have hgcd : (∏ p : s, ∏ j ∈ Finset.univ.erase i,
        ((p : ℕ).gcd (Nat.dist (v i) (v j)) : ℝ)) =
      ∏ j ∈ Finset.univ.erase i, ((primeModulus s).gcd (Nat.dist (v i) (v j)) : ℝ) := by
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j _
    rw [← Nat.cast_prod]
    congr 1
    exact (Finset.prod_coe_sort s (fun p : ℕ => p.gcd (Nat.dist (v i) (v j)))).trans
      (prod_prime_gcd s hs _)
  rw [hC, hsqrt, hgcd]

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessStarWeights.lean` -/

section

/-!
# Summing independent difference weights around a distinguished tuple entry
-/

namespace Pollack17.Burgess

open scoped BigOperators

noncomputable def starWeight {α : Type*} {n : ℕ} (w : α → α → ℝ)
    (v : Fin n → α) (i : Fin n) : ℝ :=
  ∏ j : {j : Fin n // j ≠ i}, w (v i) (v j)

theorem starWeight_nonneg {α : Type*} {n : ℕ} (w : α → α → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (v : Fin n → α) (i : Fin n) :
    0 ≤ starWeight w v i := Finset.prod_nonneg fun _ _ => hw _ _

theorem starWeight_eq_prod_erase {α : Type*} {n : ℕ} (w : α → α → ℝ)
    (v : Fin n → α) (i : Fin n) :
    starWeight w v i = ∏ j ∈ Finset.univ.erase i, w (v i) (v j) := by
  exact (Finset.prod_subtype (p := fun j => j ≠ i)
    (Finset.univ.erase i) (by simp) (fun j => w (v i) (v j))).symm

theorem sum_starWeight {α : Type*} [Fintype α] {n : ℕ}
    (w : α → α → ℝ) (i : Fin n) :
    (∑ v : Fin n → α, starWeight w v i) =
      ∑ a : α, (∑ b : α, w a b) ^ (n - 1) := by
  classical
  let e := Equiv.funSplitAt i α
  let F : (α × ({j : Fin n // j ≠ i} → α)) → ℝ :=
    fun ab => ∏ j : {j : Fin n // j ≠ i}, w ab.1 (ab.2 j)
  have heq (v : Fin n → α) : starWeight w v i = F (e v) := rfl
  have hcard : Fintype.card {j : Fin n // j ≠ i} = n - 1 := by
    simp [Fintype.card_subtype_compl]
  calc
    _ = ∑ v : Fin n → α, F (e v) := Finset.sum_congr rfl fun v _ => heq v
    _ = ∑ ab, F ab := e.sum_comp F
    _ = ∑ a : α, ∑ b : ({j : Fin n // j ≠ i} → α),
        ∏ j : {j : Fin n // j ≠ i}, w a (b j) := Fintype.sum_prod_type _
    _ = ∑ a : α, ∏ _j : {j : Fin n // j ≠ i}, ∑ b : α, w a b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Fintype.prod_sum]
    _ = _ := by simp [hcard]

theorem sum_starWeight_le {α : Type*} [Fintype α] {n : ℕ}
    (w : α → α → ℝ) (hw : ∀ a b, 0 ≤ w a b) {B : ℝ}
    (hB : ∀ a : α, ∑ b : α, w a b ≤ B) (i : Fin n) :
    (∑ v : Fin n → α, starWeight w v i) ≤ (Fintype.card α : ℝ) * B ^ (n - 1) := by
  rw [sum_starWeight]
  calc
    _ ≤ ∑ _a : α, B ^ (n - 1) := Finset.sum_le_sum fun a _ =>
      pow_le_pow_left₀ (Finset.sum_nonneg fun b _ => hw a b) (hB a) _
    _ = _ := by simp

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessTupleBound.lean` -/

section

/-!
# An arbitrary-order moment bound from singleton correlation estimates
-/

namespace Pollack17.Burgess

open scoped BigOperators

theorem sum_tuple_correlations_le {α : Type*} [Fintype α] (r : ℕ)
    (corr : (Fin (2 * r) → α) → ℝ) (w : α → α → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) {B C T : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hrow : ∀ a, ∑ b : α, w a b ≤ T)
    (htrivial : ∀ v, corr v ≤ B)
    (hsingle : ∀ (v : Fin (2 * r) → α) (i : Fin (2 * r)),
      (∀ j, j ≠ i → v j ≠ v i) → corr v ≤ C * starWeight w v i) :
    (∑ v : Fin (2 * r) → α, corr v) ≤
      (Fintype.card α : ℝ) ^ r * (r : ℝ) ^ (2 * r) * B +
        C * (2 * r : ℕ) * (Fintype.card α : ℝ) * T ^ (2 * r - 1) := by
  classical
  have hpoint (v : Fin (2 * r) → α) :
      corr v ≤ (if RepeatedTuple v then B else 0) + C * ∑ i, starWeight w v i := by
    have hweight : 0 ≤ ∑ i, starWeight w v i :=
      Finset.sum_nonneg fun i _ => starWeight_nonneg w hw v i
    by_cases hv : RepeatedTuple v
    · rw [if_pos hv]
      exact (htrivial v).trans (le_add_of_nonneg_right (mul_nonneg hC hweight))
    · rw [if_neg hv, zero_add]
      have hsi : ∃ i : Fin (2 * r), ∀ j, j ≠ i → v j ≠ v i := by
        simpa only [RepeatedTuple, not_forall, not_exists, not_and] using hv
      obtain ⟨i, hi⟩ := hsi
      exact (hsingle v i hi).trans (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun j _ => starWeight_nonneg w hw v j) (Finset.mem_univ i)) hC)
  have hdiag : (∑ v : Fin (2 * r) → α, if RepeatedTuple v then B else 0) ≤
      (Fintype.card α : ℝ) ^ r * (r : ℝ) ^ (2 * r) * B := by
    rw [← Finset.sum_filter]
    change (∑ _v ∈ repeatedTuples α (2 * r), B) ≤ _
    simp only [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hB
    exact_mod_cast repeatedTuples_card_le α r
  have hweights : (∑ v : Fin (2 * r) → α, ∑ i, starWeight w v i) ≤
      (2 * r : ℕ) * (Fintype.card α : ℝ) * T ^ (2 * r - 1) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _i : Fin (2 * r), (Fintype.card α : ℝ) * T ^ (2 * r - 1) :=
        Finset.sum_le_sum fun i _ => sum_starWeight_le w hw hrow i
      _ = _ := by simp [mul_assoc]
  calc
    _ ≤ ∑ v : Fin (2 * r) → α,
        ((if RepeatedTuple v then B else 0) + C * ∑ i, starWeight w v i) :=
      Finset.sum_le_sum fun v _ => hpoint v
    _ = (∑ v : Fin (2 * r) → α, if RepeatedTuple v then B else 0) +
        C * ∑ v : Fin (2 * r) → α, ∑ i, starWeight w v i := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
      have h := add_le_add hdiag (mul_le_mul_of_nonneg_left hweights hC)
      simpa only [mul_assoc] using h

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessEnergy.lean` -/

section

/-!
# Ratio energy with arbitrary coprime natural denominators

The incidence box is kept in the natural numbers. In particular, the argument
does not require every small integer to be coprime to the modulus.
-/

namespace Pollack17.Burgess

open scoped BigOperators

def naturalRatioWeight (q M H : ℕ) (D : Finset ℕ) (x : ZMod q) : ℕ :=
  ((Finset.range H ×ˢ D).filter fun iu =>
    (iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ) = x).card

noncomputable def naturalRatioEnergy (q M H : ℕ) [NeZero q] (D : Finset ℕ) : ℝ :=
  ∑ x : ZMod q, (naturalRatioWeight q M H D x : ℝ) ^ 2

theorem sum_naturalRatioWeight (q M H : ℕ) [NeZero q] (D : Finset ℕ) :
    ∑ x : ZMod q, naturalRatioWeight q M H D x = H * D.card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.range H ×ˢ D) (t := Finset.univ)
    (f := fun iu : ℕ × ℕ => (iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ)) (by simp)
  simpa only [Finset.card_product, Finset.card_range, naturalRatioWeight] using h.symm

theorem sum_naturalRatioWeight_mul (q M H : ℕ) [NeZero q]
    (D : Finset ℕ) (f : ZMod q → ℝ) :
    (∑ x : ZMod q, (naturalRatioWeight q M H D x : ℝ) * f x) =
      ∑ i ∈ Finset.range H, ∑ u ∈ D, f ((u : ZMod q)⁻¹ * (M + i : ℕ)) := by
  calc
    _ = ∑ iu ∈ Finset.range H ×ˢ D,
        f ((iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ)) := by
      rw [← Finset.sum_fiberwise' (Finset.range H ×ˢ D)
        (fun iu : ℕ × ℕ => (iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ)) f]
      apply Finset.sum_congr rfl
      intro x _
      simp [naturalRatioWeight, nsmul_eq_mul]
    _ = _ := Finset.sum_product _ _ _

theorem sum_card_fiber_sq_eq_card_collision
    {α β : Type*} [Fintype β] [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    (∑ y : β, ((s.filter fun a => f a = y).card) ^ 2) =
      (((s ×ˢ s).filter fun ab => f ab.1 = f ab.2).card) := by
  let c := (s ×ˢ s).filter fun ab => f ab.1 = f ab.2
  have hmap : (c : Set (α × α)).MapsTo (fun ab => f ab.1)
      (Finset.univ : Finset β) := by
    intro ab _
    exact Finset.mem_univ _
  change (∑ y : β, ((s.filter fun a => f a = y).card) ^ 2) = c.card
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro y _
  rw [pow_two, ← Finset.card_product]
  congr 1
  ext ab
  simp only [c, Finset.mem_product, Finset.mem_filter]
  aesop

theorem natural_inv_ratio_eq_iff {q n₁ n₂ u₁ u₂ : ℕ}
    (h₁ : u₁.Coprime q) (h₂ : u₂.Coprime q) :
    (u₁ : ZMod q)⁻¹ * n₁ = (u₂ : ZMod q)⁻¹ * n₂ ↔
      n₁ * u₂ ≡ n₂ * u₁ [MOD q] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, Nat.cast_mul]
  have hmul₁ := ZMod.coe_mul_inv_eq_one u₁ h₁
  have hmul₂ := ZMod.coe_mul_inv_eq_one u₂ h₂
  constructor
  · intro h
    calc
      (n₁ : ZMod q) * u₂ = ((u₁ : ZMod q) * (u₁ : ZMod q)⁻¹) * (n₁ * u₂) := by
        rw [hmul₁, one_mul]
      _ = ((u₁ : ZMod q) * u₂) * ((u₁ : ZMod q)⁻¹ * n₁) := by ring
      _ = ((u₁ : ZMod q) * u₂) * ((u₂ : ZMod q)⁻¹ * n₂) := by rw [h]
      _ = ((u₂ : ZMod q) * (u₂ : ZMod q)⁻¹) * (n₂ * u₁) := by ring
      _ = _ := by rw [hmul₂, one_mul]
  · intro h
    calc
      (u₁ : ZMod q)⁻¹ * n₁ = ((u₂ : ZMod q) * (u₂ : ZMod q)⁻¹) *
          ((u₁ : ZMod q)⁻¹ * n₁) := by rw [hmul₂, one_mul]
      _ = ((u₁ : ZMod q)⁻¹ * (u₂ : ZMod q)⁻¹) * (n₁ * u₂) := by ring
      _ = ((u₁ : ZMod q)⁻¹ * (u₂ : ZMod q)⁻¹) * (n₂ * u₁) := by rw [h]
      _ = ((u₁ : ZMod q) * (u₁ : ZMod q)⁻¹) * ((u₂ : ZMod q)⁻¹ * n₂) := by ring
      _ = _ := by rw [hmul₁, one_mul]

theorem naturalRatioEnergy_eq_sum (q M H : ℕ) [NeZero q] (D : Finset ℕ)
    (hD : ∀ u ∈ D, u.Coprime q) :
    naturalRatioEnergy q M H D =
      ((∑ u ∈ D, ∑ v ∈ D, (burgessIntervalCollision q M H u v).card : ℕ) : ℝ) := by
  let box := Finset.range H ×ˢ D
  have h := sum_card_fiber_sq_eq_card_collision box
    (fun iu : ℕ × ℕ => (iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ))
  have heq : ((box ×ˢ box).filter fun ab =>
      (ab.1.2 : ZMod q)⁻¹ * (M + ab.1.1 : ℕ) =
        (ab.2.2 : ZMod q)⁻¹ * (M + ab.2.1 : ℕ)) =
      ((box ×ˢ box).filter fun ab =>
        (M + ab.1.1) * ab.2.2 ≡ (M + ab.2.1) * ab.1.2 [MOD q]) := by
    apply Finset.filter_congr
    intro ab hab
    have hmem := Finset.mem_product.mp hab
    exact natural_inv_ratio_eq_iff
      (hD ab.1.2 (Finset.mem_product.mp hmem.1).2)
      (hD ab.2.2 (Finset.mem_product.mp hmem.2).2)
  rw [heq] at h
  have hcard : (((box ×ˢ box).filter fun ab =>
      (M + ab.1.1) * ab.2.2 ≡ (M + ab.2.1) * ab.1.2 [MOD q]).card) =
      ∑ u ∈ D, ∑ v ∈ D, (burgessIntervalCollision q M H u v).card := by
    simp only [box, burgessIntervalCollision, Finset.card_eq_sum_ones,
      Finset.sum_filter, Finset.sum_product]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    calc
      _ = ∑ i ∈ Finset.range H, ∑ v ∈ D, ∑ j ∈ Finset.range H,
          if (M + i) * v ≡ (M + j) * u [MOD q] then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := Finset.sum_comm
  rw [hcard] at h
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) h
  simpa only [naturalRatioEnergy, naturalRatioWeight, box, Nat.cast_sum,
    Nat.cast_pow] using hcast

theorem naturalRatioEnergy_le {q M H U : ℕ} [NeZero q] (D : Finset ℕ)
    (hD : D ⊆ Finset.Icc 1 U) (hcop : ∀ u ∈ D, u.Coprime q)
    (hH : 0 < H) (hU : 0 < U) (hsmall : 2 * (U * H) < q) :
    naturalRatioEnergy q M H D ≤
      ((H : ℝ) * (1 + Real.log U) + U) * ((U : ℝ) * (1 + Real.log U)) := by
  rw [naturalRatioEnergy_eq_sum q M H D hcop]
  have hfirst : (∑ u ∈ D, ∑ v ∈ D, (burgessIntervalCollision q M H u v).card) ≤
      ∑ u ∈ D, ∑ v ∈ D, (H / (u / u.gcd v) + 1) := by
    apply Finset.sum_le_sum
    intro u hu
    apply Finset.sum_le_sum
    intro v hv
    exact burgessIntervalCollision_card_le_of_coprime hH hU
      (hD hu) (hD hv) (hcop u hu).symm hsmall
  have hsecond : (∑ u ∈ D, ∑ v ∈ D, (H / (u / u.gcd v) + 1)) ≤
      ∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 U, (H / (u / u.gcd v) + 1) := by
    exact (Finset.sum_le_sum fun u _ => Finset.sum_le_sum_of_subset hD).trans
      (Finset.sum_le_sum_of_subset hD)
  calc
    _ ≤ ((∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 U,
        (H / (u / u.gcd v) + 1) : ℕ) : ℝ) := by exact_mod_cast hfirst.trans hsecond
    _ ≤ (burgessDivisorOvercount H U : ℝ) := reduced_denominator_sum_cast_le H U
    _ ≤ _ := burgessDivisorOvercount_cast_le H U hU

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessHolder.lean` -/

section

/-!
# Weighted Hölder in the integer-power form for Burgess amplification
-/

namespace Pollack17.Burgess

open scoped BigOperators

theorem weighted_power_sum_le {ι : Type*} (S : Finset ι) (w z : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hz : ∀ i ∈ S, 0 ≤ z i) (k : ℕ) :
    (∑ i ∈ S, w i * z i) ^ (k + 1) ≤
      (∑ i ∈ S, w i) ^ k * ∑ i ∈ S, w i * z i ^ (k + 1) := by
  let W := ∑ i ∈ S, w i
  have hW0 : 0 ≤ W := Finset.sum_nonneg hw
  by_cases hW : W = 0
  · have hwi : ∀ i ∈ S, w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hW
    have hleft : (∑ i ∈ S, w i * z i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hwi i hi, zero_mul]
    have hright : (∑ i ∈ S, w i * z i ^ (k + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hwi i hi, zero_mul]
    simp [hleft, hright]
  have hWpos : 0 < W := lt_of_le_of_ne hW0 (Ne.symm hW)
  have hj := Real.pow_arith_mean_le_arith_mean_pow S (fun i => w i / W) z
    (fun i hi => div_nonneg (hw i hi) hW0)
    (by rw [← Finset.sum_div]; exact div_self hW) hz (k + 1)
  have hj' : ((∑ i ∈ S, w i * z i) / W) ^ (k + 1) ≤
      (∑ i ∈ S, w i * z i ^ (k + 1)) / W := by
    simpa only [div_mul_eq_mul_div, ← Finset.sum_div] using hj
  rw [div_pow] at hj'
  have hscaled := (div_le_iff₀ (pow_pos hWpos (k + 1))).mp hj'
  calc
    (∑ i ∈ S, w i * z i) ^ (k + 1) ≤
        ((∑ i ∈ S, w i * z i ^ (k + 1)) / W) * W ^ (k + 1) := hscaled
    _ = W ^ k * ∑ i ∈ S, w i * z i ^ (k + 1) := by
      rw [pow_succ]
      field_simp
    _ = _ := rfl

theorem weighted_even_power_sum_le {ι : Type*} (S : Finset ι) (w z : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hz : ∀ i ∈ S, 0 ≤ z i) (k : ℕ) :
    (∑ i ∈ S, w i * z i) ^ (2 * (k + 1)) ≤
      (∑ i ∈ S, w i) ^ (2 * k) * (∑ i ∈ S, w i ^ 2) *
        ∑ i ∈ S, z i ^ (2 * (k + 1)) := by
  have hsum0 : 0 ≤ ∑ i ∈ S, w i * z i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hz i hi)
  have hj := weighted_power_sum_le S w z hw hz k
  have hj2 := pow_le_pow_left₀ (pow_nonneg hsum0 _) hj 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S w (fun i => z i ^ (k + 1))
  have hpowers (i : ι) : (z i ^ (k + 1)) ^ 2 = z i ^ (2 * (k + 1)) := by
    rw [← pow_mul]
    congr 1
    omega
  simp_rw [hpowers] at hcs
  calc
    (∑ i ∈ S, w i * z i) ^ (2 * (k + 1)) =
        ((∑ i ∈ S, w i * z i) ^ (k + 1)) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ ((∑ i ∈ S, w i) ^ k * ∑ i ∈ S, w i * z i ^ (k + 1)) ^ 2 := hj2
    _ = (∑ i ∈ S, w i) ^ (2 * k) * (∑ i ∈ S, w i * z i ^ (k + 1)) ^ 2 := by
      rw [mul_pow, ← pow_mul]
      congr 2
      omega
    _ ≤ (∑ i ∈ S, w i) ^ (2 * k) *
        ((∑ i ∈ S, w i ^ 2) * ∑ i ∈ S, z i ^ (2 * (k + 1))) :=
      mul_le_mul_of_nonneg_left hcs (pow_nonneg (Finset.sum_nonneg hw) _)
    _ = _ := by ring

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessAmplifier.lean` -/

section

/-!
# Interval averaging for real multiplicative characters

The boundary estimates are extracted from `Erdos587.NVDevelopment`.
The amplification below allows any finite family of coprime denominators.
-/

namespace Pollack17.Burgess

open scoped BigOperators

lemma abs_sum_range_shift_sub_le (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) (M H h : ℕ) (hh : h ≤ H) :
    |(∑ i ∈ Finset.range H, f (M + i)) -
      ∑ i ∈ Finset.range H, f (M + h + i)| ≤ 2 * h := by
  have hH₁ : h + (H - h) = H := Nat.add_sub_of_le hh
  have hH₂ : (H - h) + h = H := Nat.sub_add_cancel hh
  have hdecomp :
      (∑ i ∈ Finset.range H, f (M + i)) -
          ∑ i ∈ Finset.range H, f (M + h + i) =
        (∑ i ∈ Finset.range h, f (M + i)) -
          ∑ i ∈ Finset.range h, f (M + H + i) := by
    have hleft := Finset.sum_range_add (fun i ↦ f (M + i)) h (H - h)
    have hright := Finset.sum_range_add
      (fun i ↦ f (M + h + i)) (H - h) h
    rw [hH₁] at hleft
    rw [hH₂] at hright
    rw [hleft, hright]
    have hmiddle :
        (∑ x ∈ Finset.range (H - h), f (M + (h + x))) =
          ∑ x ∈ Finset.range (H - h), f (M + h + x) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega
    have hsuffix :
        (∑ x ∈ Finset.range h, f (M + h + ((H - h) + x))) =
          ∑ x ∈ Finset.range h, f (M + H + x) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega
    rw [hmiddle, hsuffix]
    ring
  rw [hdecomp]
  calc
    |(∑ i ∈ Finset.range h, f (M + i)) -
        ∑ i ∈ Finset.range h, f (M + H + i)| ≤
        |∑ i ∈ Finset.range h, f (M + i)| +
          |∑ i ∈ Finset.range h, f (M + H + i)| := abs_sub _ _
    _ ≤ (∑ i ∈ Finset.range h, |f (M + i)|) +
        ∑ i ∈ Finset.range h, |f (M + H + i)| := by
      gcongr <;> exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ _i ∈ Finset.range h, (1 : ℝ)) +
        ∑ _i ∈ Finset.range h, (1 : ℝ) := by
      gcongr <;> exact hf _
    _ = 2 * h := by simp; ring

lemma abs_burgess_shift_average_sub_le
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (M H : ℕ) (U V : Finset ℕ) (g : ℕ → ℕ → ℕ)
    (hg : ∀ u ∈ U, ∀ v ∈ V, g u v ≤ H) :
    |((U.card * V.card : ℕ) : ℝ) *
        (∑ i ∈ Finset.range H, f (M + i)) -
      ∑ u ∈ U, ∑ v ∈ V,
        ∑ i ∈ Finset.range H, f (M + g u v + i)| ≤
      ∑ u ∈ U, ∑ v ∈ V, ((2 * g u v : ℕ) : ℝ) := by
  let S : ℕ → ℝ := fun h ↦ ∑ i ∈ Finset.range H, f (M + h + i)
  have hS0 : S 0 = ∑ i ∈ Finset.range H, f (M + i) := by
    simp [S]
  have heq :
      ((U.card * V.card : ℕ) : ℝ) * S 0 -
          ∑ u ∈ U, ∑ v ∈ V, S (g u v) =
        ∑ u ∈ U, ∑ v ∈ V, (S 0 - S (g u v)) := by
    simp only [Finset.sum_sub_distrib]
    simp
    ring
  rw [← hS0, heq]
  calc
    |∑ u ∈ U, ∑ v ∈ V, (S 0 - S (g u v))| ≤
        ∑ u ∈ U, |∑ v ∈ V, (S 0 - S (g u v))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ U, ∑ v ∈ V, |S 0 - S (g u v)| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ U, ∑ v ∈ V, ((2 * g u v : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      simpa [S] using
        abs_sum_range_shift_sub_le f hf M H (g u v) (hg u hu v hv)

lemma abs_burgess_shifted_triple_sum_le_finset
    (f : ℕ → ℝ) (M H : ℕ) (U V : Finset ℕ) (shift : ℕ → ℕ → ℕ) :
    |∑ u ∈ U, ∑ v ∈ V, ∑ i ∈ Finset.range H,
        f (M + shift u v + i)| ≤
      ∑ i ∈ Finset.range H, ∑ u ∈ U,
        |∑ v ∈ V, f (M + i + shift u v)| := by
  have hreorder :
      (∑ u ∈ U, ∑ v ∈ V, ∑ i ∈ Finset.range H,
          f (M + shift u v + i)) =
        ∑ i ∈ Finset.range H, ∑ u ∈ U,
          ∑ v ∈ V, f (M + i + shift u v) := by
    calc
      (∑ u ∈ U, ∑ v ∈ V, ∑ i ∈ Finset.range H,
          f (M + shift u v + i)) =
        ∑ u ∈ U, ∑ i ∈ Finset.range H,
          ∑ v ∈ V, f (M + shift u v + i) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.sum_comm]
      _ = ∑ i ∈ Finset.range H, ∑ u ∈ U,
          ∑ v ∈ V, f (M + shift u v + i) := by
          rw [Finset.sum_comm]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_congr rfl
          intro v hv
          congr 1
          omega
  rw [hreorder]
  calc
    |∑ i ∈ Finset.range H, ∑ u ∈ U,
        ∑ v ∈ V, f (M + i + shift u v)| ≤
      ∑ i ∈ Finset.range H,
        |∑ u ∈ U, ∑ v ∈ V, f (M + i + shift u v)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range H, ∑ u ∈ U,
        |∑ v ∈ V, f (M + i + shift u v)| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _

noncomputable def naturalShiftSum {q : ℕ} (f : ZMod q → ℝ) (V : ℕ) (x : ZMod q) : ℝ :=
  ∑ v ∈ Finset.Icc 1 V, f (x + v)

noncomputable def amplifierNumerator {q : ℕ} [NeZero q] (f : ZMod q → ℝ)
    (M H : ℕ) (D : Finset ℕ) (V : ℕ) : ℝ :=
  ∑ x : ZMod q, (naturalRatioWeight q M H D x : ℝ) * |naturalShiftSum f V x|


theorem abs_natural_dilated_sum {q : ℕ} (f : ZMod q → ℝ)
    (hmul : ∀ a b, f (a * b) = f a * f b) (M i u V : ℕ)
    (hu : u.Coprime q) (hfu : |f u| = 1) :
    |∑ v ∈ Finset.Icc 1 V, f (M + i + u * v : ℕ)| =
      |naturalShiftSum f V ((u : ZMod q)⁻¹ * (M + i : ℕ))| := by
  have halg (v : ℕ) : ((M + i + u * v : ℕ) : ZMod q) =
      u * ((u : ZMod q)⁻¹ * (M + i : ℕ) + v) := by
    rw [mul_add, ← mul_assoc, ZMod.coe_mul_inv_eq_one u hu, one_mul]
    push_cast
    ring
  simp_rw [halg, hmul]
  rw [← Finset.mul_sum, abs_mul, hfu, one_mul]
  rfl

theorem amplifierNumerator_eq_natural {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) (hmul : ∀ a b, f (a * b) = f a * f b)
    (M H : ℕ) (D : Finset ℕ) (V : ℕ)
    (hD : ∀ u ∈ D, u.Coprime q) (hfD : ∀ u ∈ D, |f u| = 1) :
    amplifierNumerator f M H D V =
      ∑ i ∈ Finset.range H, ∑ u ∈ D,
        |∑ v ∈ Finset.Icc 1 V, f (M + i + u * v : ℕ)| := by
  rw [amplifierNumerator, sum_naturalRatioWeight_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro u hu
  exact (abs_natural_dilated_sum f hmul M i u V (hD u hu) (hfD u hu)).symm

theorem amplified_abs_le {q M H U V : ℕ} [NeZero q]
    (f : ZMod q → ℝ) (hmul : ∀ a b, f (a * b) = f a * f b)
    (hf : ∀ x, |f x| ≤ 1) (D : Finset ℕ)
    (hD : D ⊆ Finset.Icc 1 U) (hcop : ∀ u ∈ D, u.Coprime q)
    (hfD : ∀ u ∈ D, |f u| = 1) (hUV : U * V ≤ H) :
    (D.card : ℝ) * V * |∑ i ∈ Finset.range H, f (M + i : ℕ)| ≤
      amplifierNumerator f M H D V + 2 * (D.card : ℝ) * V * (U * V) := by
  let S := ∑ i ∈ Finset.range H, f (M + i : ℕ)
  let T := ∑ u ∈ D, ∑ v ∈ Finset.Icc 1 V,
    ∑ i ∈ Finset.range H, f (M + u * v + i : ℕ)
  have havg := abs_burgess_shift_average_sub_le (fun n => f (n : ZMod q))
    (fun n => hf _) M H D (Finset.Icc 1 V) (fun u v => u * v) (by
      intro u hu v hv
      exact (Nat.mul_le_mul (Finset.mem_Icc.mp (hD hu)).2
        (Finset.mem_Icc.mp hv).2).trans hUV)
  have herror : |(D.card : ℝ) * V * S - T| ≤
      2 * (D.card : ℝ) * V * (U * V) := by
    have havg' : |(D.card : ℝ) * V * S - T| ≤
        ∑ u ∈ D, ∑ v ∈ Finset.Icc 1 V, ((2 * (u * v) : ℕ) : ℝ) := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_mul] using havg
    refine havg'.trans ?_
    calc
      _ ≤ ∑ _u ∈ D, ∑ _v ∈ Finset.Icc 1 V, ((2 * (U * V) : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro v hv
        exact_mod_cast Nat.mul_le_mul_left 2 (Nat.mul_le_mul
          (Finset.mem_Icc.mp (hD hu)).2 (Finset.mem_Icc.mp hv).2)
      _ = _ := by simp; ring
  have hT : |T| ≤ amplifierNumerator f M H D V := by
    rw [amplifierNumerator_eq_natural f hmul M H D V hcop hfD]
    exact abs_burgess_shifted_triple_sum_le_finset
      (fun n => f (n : ZMod q)) M H D (Finset.Icc 1 V) (fun u v => u * v)
  have htri : |(D.card : ℝ) * V * S| ≤ |(D.card : ℝ) * V * S - T| + |T| := by
    simpa only [sub_add_cancel] using abs_add_le ((D.card : ℝ) * V * S - T) T
  rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))] at htri
  exact htri.trans ((add_le_add herror hT).trans_eq (add_comm _ _))

theorem amplifierNumerator_even_power_le {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) (M H : ℕ) (D : Finset ℕ) (V k : ℕ) :
    amplifierNumerator f M H D V ^ (2 * (k + 1)) ≤
      ((H : ℝ) * D.card) ^ (2 * k) * naturalRatioEnergy q M H D *
        ∑ x : ZMod q, naturalShiftSum f V x ^ (2 * (k + 1)) := by
  have hh := weighted_even_power_sum_le (Finset.univ : Finset (ZMod q))
    (fun x => (naturalRatioWeight q M H D x : ℝ))
    (fun x => |naturalShiftSum f V x|)
    (fun x _ => Nat.cast_nonneg _) (fun x _ => abs_nonneg _) k
  have hsum : (∑ x : ZMod q, (naturalRatioWeight q M H D x : ℝ)) =
      (H : ℝ) * D.card := by exact_mod_cast sum_naturalRatioWeight q M H D
  have habs (x : ZMod q) : |naturalShiftSum f V x| ^ (2 * (k + 1)) =
      naturalShiftSum f V x ^ (2 * (k + 1)) := (even_two_mul _).pow_abs _
  simpa only [hsum, habs, amplifierNumerator, naturalRatioEnergy] using hh

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessCompositeMoment.lean` -/

section

/-!
# The complete Burgess moment for squarefree quadratic characters

This bound is valid at every moment order. Its only arithmetic loss beyond
the prime-field square-root estimate is a fixed power of the divisor count.
-/

namespace Pollack17.Burgess

open scoped BigOperators

theorem productChar_prod (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {ι : Type*} [Fintype ι] (f : ι → ZMod (primeModulus s)) :
    productChar s hs (∏ i, f i) = ∏ i, productChar s hs (f i) := by
  classical
  simp only [productChar, localChar, qchar, map_prod, Finset.prod_apply, Int.cast_prod]
  rw [Finset.prod_comm]

theorem productChar_moment_expansion (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] (V n : ℕ) :
    (∑ x : ZMod (primeModulus s), naturalShiftSum (productChar s hs) V x ^ n) =
      ∑ v : Fin n → (Finset.Icc 1 V), ∑ x : ZMod (primeModulus s),
        productChar s hs (∏ i : Fin n, (x + (v i : ℕ))) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [naturalShiftSum, ← Finset.sum_attach, Finset.attach_eq_univ, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro v _
  exact (productChar_prod s hs (fun i : Fin n => x + (v i : ℕ))).symm

noncomputable def gcdKernel (q a b : ℕ) : ℝ :=
  if b ≠ a then (q.gcd (Nat.dist a b) : ℝ) else 0

theorem gcdKernel_nonneg (q a b : ℕ) : 0 ≤ gcdKernel q a b := by
  unfold gcdKernel
  split_ifs <;> positivity

theorem sum_gcdKernel_le {q : ℕ} (hq : q ≠ 0) (V : ℕ) (a : Finset.Icc 1 V) :
    (∑ b : Finset.Icc 1 V, gcdKernel q a b) ≤ 2 * V * q.divisors.card := by
  rw [Finset.sum_coe_sort (Finset.Icc 1 V) (fun b : ℕ => gcdKernel q a b)]
  simp only [gcdKernel, ← Finset.sum_filter, Finset.filter_ne']
  exact_mod_cast sum_gcd_dist_erase_le hq (Finset.mem_Icc.mp a.property).2

theorem productChar_even_moment_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] (V r : ℕ) :
    (∑ x : ZMod (primeModulus s), naturalShiftSum (productChar s hs) V x ^ (2 * r)) ≤
      (V : ℝ) ^ r * (r : ℝ) ^ (2 * r) * primeModulus s +
        ((Stepanov.simpleRootConstant (2 * r) : ℝ) ^ s.card * Real.sqrt (primeModulus s)) *
          (2 * r : ℕ) * V * (2 * V * ((primeModulus s).divisors.card : ℝ)) ^ (2 * r - 1) := by
  classical
  let α := Finset.Icc 1 V
  let q := primeModulus s
  let corr : (Fin (2 * r) → α) → ℝ := fun v =>
    ∑ x : ZMod q, productChar s hs (∏ i : Fin (2 * r), (x + (v i : ℕ)))
  let w : α → α → ℝ := fun a b => gcdKernel q a b
  let C : ℝ := (Stepanov.simpleRootConstant (2 * r) : ℝ) ^ s.card * Real.sqrt q
  have hw : ∀ a b : α, 0 ≤ w a b := fun a b => gcdKernel_nonneg q a b
  have hrow : ∀ a : α, (∑ b : α, w a b) ≤ 2 * V * (q.divisors.card : ℝ) :=
    fun a => sum_gcdKernel_le (NeZero.ne q) V a
  have htrivial (v : Fin (2 * r) → α) : corr v ≤ q := by
    calc
      _ ≤ ∑ _x : ZMod q, (1 : ℝ) := Finset.sum_le_sum fun x _ =>
        (le_abs_self _).trans (abs_productChar_le_one s hs _)
      _ = _ := by simp
  have hsingle (v : Fin (2 * r) → α) (i : Fin (2 * r))
      (hi : ∀ j, j ≠ i → v j ≠ v i) : corr v ≤ C * starWeight w v i := by
    have hbound := product_correlation_le_gcd s hs (fun j => (v j : ℕ)) i
    have hwprod : starWeight w v i =
        ∏ j ∈ Finset.univ.erase i, (q.gcd (Nat.dist (v i) (v j)) : ℝ) := by
      rw [starWeight_eq_prod_erase]
      apply Finset.prod_congr rfl
      intro j hj
      have hne : (v j : ℕ) ≠ v i := fun h => hi j (Finset.mem_erase.mp hj).1 (Subtype.ext h)
      exact if_pos hne
    rw [hwprod]
    exact (le_abs_self (corr v)).trans hbound
  rw [productChar_moment_expansion]
  have h := sum_tuple_correlations_le r corr w hw (Nat.cast_nonneg q)
    (by dsimp [C]; positivity) hrow htrivial hsingle
  simpa only [α, corr, C, q, Fintype.card_coe, Nat.card_Icc, Nat.add_sub_cancel] using h

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessMomentAsymptotics.lean` -/

section

/-!
# Absorbing composite moment losses into an arbitrarily small power
-/

namespace Pollack17.Burgess

open Filter
open scoped BigOperators

theorem composite_moment_second_term (C w V n : ℕ) (hn : 0 < n) (q : ℝ) :
    (C : ℝ) ^ w * q * n * V * (2 * V * (2 : ℝ) ^ w) ^ (n - 1) =
      ((n : ℝ) * 2 ^ (n - 1)) * ((C * 2 ^ (n - 1) : ℕ) : ℝ) ^ w * q * (V : ℝ) ^ n := by
  have hV : (V : ℝ) * (V : ℝ) ^ (n - 1) = (V : ℝ) ^ n := by
    rw [← pow_succ']
    congr 1
    omega
  have htwo : ((2 : ℝ) ^ w) ^ (n - 1) = ((2 : ℝ) ^ (n - 1)) ^ w := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow, htwo]
  calc
    _ = ((n : ℝ) * 2 ^ (n - 1)) *
        ((C : ℝ) ^ w * (2 ^ (n - 1)) ^ w) * q * ((V : ℝ) * (V : ℝ) ^ (n - 1)) := by ring
    _ = _ := by rw [hV]

theorem eventually_productChar_moment_le (r : ℕ) (hr : 0 < r)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q : ℕ, ∀ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime), Q ≤ primeModulus s →
      ∀ V : ℕ, letI : NeZero (primeModulus s) := ⟨(primeModulus_pos s hs).ne'⟩
      (∑ x : ZMod (primeModulus s), naturalShiftSum (productChar s hs) V x ^ (2 * r)) ≤
        (primeModulus s : ℝ) ^ δ *
          ((primeModulus s : ℝ) * (V : ℝ) ^ r + Real.sqrt (primeModulus s) * (V : ℝ) ^ (2 * r)) := by
  let n := 2 * r
  let C := Stepanov.simpleRootConstant n
  let b := C * 2 ^ (n - 1)
  have hb : 1 ≤ b := Nat.mul_pos (simpleRootConstant_one_le n) (by positivity)
  have hfirst := eventually_const_mul_pow_primeFactors_le ((r : ℝ) ^ (2 * r)) 1 (by omega) hδ
  have hsecond := eventually_const_mul_pow_primeFactors_le ((n : ℝ) * 2 ^ (n - 1)) b hb hδ
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp (hfirst.and hsecond)
  refine ⟨Q, fun s hs hq V => ?_⟩
  have : NeZero (primeModulus s) := ⟨(primeModulus_pos s hs).ne'⟩
  have hc₁ : (r : ℝ) ^ (2 * r) ≤ (primeModulus s : ℝ) ^ δ := by
    simpa using (hQ (primeModulus s) hq).1
  have hc₂ : ((n : ℝ) * 2 ^ (n - 1)) * (b : ℝ) ^ s.card ≤
      (primeModulus s : ℝ) ^ δ := by
    simpa only [primeModulus_primeFactors s hs] using (hQ (primeModulus s) hq).2
  have hm := productChar_even_moment_le s hs V r
  rw [primeModulus_card_divisors s hs, Nat.cast_pow, Nat.cast_ofNat] at hm
  have heq := composite_moment_second_term C s.card V n (by dsimp [n]; omega)
    (Real.sqrt (primeModulus s))
  change _ = ((n : ℝ) * 2 ^ (n - 1)) * (b : ℝ) ^ s.card *
    Real.sqrt (primeModulus s) * (V : ℝ) ^ n at heq
  rw [heq] at hm
  have h₁ := mul_le_mul_of_nonneg_right hc₁
    (mul_nonneg (Nat.cast_nonneg (primeModulus s)) (pow_nonneg (Nat.cast_nonneg V) r))
  have h₂ := mul_le_mul_of_nonneg_right hc₂
    (mul_nonneg (Real.sqrt_nonneg (primeModulus s)) (pow_nonneg (Nat.cast_nonneg V) n))
  refine hm.trans ?_
  nlinarith only [h₁, h₂]

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessScaleEstimates.lean` -/

section

/-!
# Finite power-scale estimates for the Burgess amplifier
-/

namespace Pollack17.Burgess

open scoped BigOperators

theorem pow_le_scaled_rpow {x q C a : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q)
    (h : x ≤ C * q ^ a) (k : ℕ) : x ^ k ≤ C ^ k * q ^ (a * k) := by
  simpa only [mul_pow, ← Real.rpow_mul_natCast hq] using pow_le_pow_left₀ hx h k

theorem scaled_rpow_le_pow {x q C a : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q)
    (h : C * q ^ a ≤ x) (k : ℕ) : C ^ k * q ^ (a * k) ≤ x ^ k := by
  simpa only [mul_pow, ← Real.rpow_mul_natCast hq] using
    pow_le_pow_left₀ (mul_nonneg hC (Real.rpow_nonneg hq _)) h k

theorem harmonic_energy_scale_le {q : ℕ} (hq : 1 ≤ q) {H U : ℕ}
    (hU : 0 < U) {c u δ : ℝ} (hu1 : u ≤ 1) (huδ : u ≤ c + δ)
    (hH : (H : ℝ) ≤ (q : ℝ) ^ c) (hUp : (U : ℝ) ≤ (q : ℝ) ^ u)
    (hlog : 1 + Real.log (q : ℝ) ≤ (q : ℝ) ^ δ) :
    ((H : ℝ) * (1 + Real.log U) + U) * ((U : ℝ) * (1 + Real.log U)) ≤
      2 * (q : ℝ) ^ (c + u + 2 * δ) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : 0 < (q : ℝ) := zero_lt_one.trans_le hq1
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hUq : (U : ℝ) ≤ q := hUp.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hq1 hu1)
  have hL : 1 + Real.log (U : ℝ) ≤ (q : ℝ) ^ δ := by
    have hl := Real.log_le_log hU0 hUq
    linarith
  have hL0 : 0 ≤ 1 + Real.log (U : ℝ) := by
    have hl := Real.log_nonneg (by exact_mod_cast hU : (1 : ℝ) ≤ U)
    linarith
  have hA : (H : ℝ) * (1 + Real.log U) ≤ (q : ℝ) ^ (c + δ) := by
    simpa only [Real.rpow_add hq0] using mul_le_mul hH hL hL0 (Real.rpow_nonneg hq0.le c)
  have hU' : (U : ℝ) ≤ (q : ℝ) ^ (c + δ) :=
    hUp.trans (Real.rpow_le_rpow_of_exponent_le hq1 huδ)
  have hA' : (H : ℝ) * (1 + Real.log U) + U ≤ 2 * (q : ℝ) ^ (c + δ) := by
    linarith
  have hB : (U : ℝ) * (1 + Real.log U) ≤ (q : ℝ) ^ (u + δ) := by
    simpa only [Real.rpow_add hq0] using mul_le_mul hUp hL hL0 (Real.rpow_nonneg hq0.le u)
  calc
    _ ≤ (2 * (q : ℝ) ^ (c + δ)) * (q : ℝ) ^ (u + δ) :=
      mul_le_mul hA' hB (mul_nonneg hU0.le hL0) (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hq0]; congr 2; ring

theorem moment_scale_le {q : ℕ} (hq : 0 < q) {V r : ℕ} {v δ : ℝ}
    (hv : v * (r : ℝ) = 1 / 2) (hV : (V : ℝ) ≤ 2 * (q : ℝ) ^ v) :
    (q : ℝ) ^ δ * ((q : ℝ) * (V : ℝ) ^ r + Real.sqrt q * (V : ℝ) ^ (2 * r)) ≤
      ((2 : ℝ) ^ r + 2 ^ (2 * r)) * (q : ℝ) ^ (3 / 2 + δ) := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have h₁ := pow_le_scaled_rpow (Nat.cast_nonneg V) hq0.le hV r
  have h₂ := pow_le_scaled_rpow (Nat.cast_nonneg V) hq0.le hV (2 * r)
  have hvr : v * ((2 * r : ℕ) : ℝ) = 1 := by push_cast; nlinarith only [hv]
  rw [hv] at h₁
  rw [hvr, Real.rpow_one] at h₂
  have hqpow : (q : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) = (q : ℝ) ^ (3 / 2 : ℝ) := by
    calc
      _ = (q : ℝ) ^ (1 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
      _ = (q : ℝ) ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hq0 _ _).symm
      _ = _ := by norm_num
  have hsum : (q : ℝ) * (V : ℝ) ^ r + Real.sqrt q * (V : ℝ) ^ (2 * r) ≤
      ((2 : ℝ) ^ r + 2 ^ (2 * r)) * (q : ℝ) ^ (3 / 2 : ℝ) := by
    have ha := mul_le_mul_of_nonneg_left h₁ hq0.le
    have hb := mul_le_mul_of_nonneg_left h₂ (Real.sqrt_nonneg q)
    rw [Real.sqrt_eq_rpow] at hb ⊢
    calc
      _ ≤ (q : ℝ) * (2 ^ r * (q : ℝ) ^ (1 / 2 : ℝ)) +
          (q : ℝ) ^ (1 / 2 : ℝ) * (2 ^ (2 * r) * q) := add_le_add ha hb
      _ = (2 ^ r + 2 ^ (2 * r)) * ((q : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [hqpow]
  calc
    _ ≤ (q : ℝ) ^ δ * (((2 : ℝ) ^ r + 2 ^ (2 * r)) * (q : ℝ) ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hq0.le δ)
    _ = _ := by rw [mul_left_comm, ← Real.rpow_add hq0]; congr 2; ring

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessDenominators.lean` -/

section

/-!
# Counting the admissible Burgess denominators

These inclusion-exclusion estimates are extracted from the elementary sieve
in `Erdos587.NVDevelopment`, independently of its fourth-moment results.
-/

namespace Pollack17.Burgess

open scoped BigOperators

def coprimeDenominators (s : Finset ℕ) (U : ℕ) : Finset ℕ :=
  (Finset.Icc 1 U).filter fun u ↦ u.Coprime (primeModulus s)

/-- Multiples of `p` in the finite interval used to count admissible
Burgess denominators. -/
def primeSetMultiplesInIcc (U p : ℕ) : Finset ↥(Finset.Icc 1 U) :=
  Finset.univ.filter fun u ↦ p ∣ (u : ℕ)

lemma prod_dvd_iff_all_prime_dvd
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (n : ℕ) :
    (∏ p ∈ t, p) ∣ n ↔ ∀ p ∈ t, p ∣ n := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem id hp).trans h
  · intro h
    induction t using Finset.induction_on with
    | empty => simp
    | @insert p t hpt ih =>
        rw [Finset.prod_insert hpt]
        have hp : p.Prime := ht p (Finset.mem_insert_self p t)
        have hcop : p.Coprime (∏ r ∈ t, r) := by
          apply Nat.Coprime.prod_right
          intro r hr
          exact (Nat.coprime_primes hp
            (ht r (Finset.mem_insert_of_mem hr))).mpr
            (Ne.symm (ne_of_mem_of_not_mem hr hpt))
        exact hcop.mul_dvd_of_dvd_of_dvd
          (h p (Finset.mem_insert_self p t))
          (ih (fun r hr ↦ ht r (Finset.mem_insert_of_mem hr))
            (fun r hr ↦ h r (Finset.mem_insert_of_mem hr)))

lemma card_inf_primeSetMultiplesInIcc
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (U : ℕ) :
    (t.inf (primeSetMultiplesInIcc U)).card =
      U / (∏ p ∈ t, p) := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  refine Finset.card_bij
    (s := t.inf (primeSetMultiplesInIcc U))
    (t := (Finset.Ioc 0 U).filter fun n ↦ (∏ p ∈ t, p) ∣ n)
    (fun (u : ↥(Finset.Icc 1 U)) _hu ↦ (u : ℕ)) ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_Ioc.mpr (Finset.mem_Icc.mp u.property)
    · rw [prod_dvd_iff_all_prime_dvd t ht]
      intro p hp
      have hu' : ∀ p ∈ t, u ∈ primeSetMultiplesInIcc U p := by
        simpa only [Finset.mem_inf] using hu
      have hup : u ∈ primeSetMultiplesInIcc U p := hu' p hp
      simpa [primeSetMultiplesInIcc] using hup
  · intro u₁ h₁ u₂ h₂ huv
    exact Subtype.ext huv
  · intro n hn
    have hnIoc := (Finset.mem_filter.mp hn).1
    let u : ↥(Finset.Icc 1 U) :=
      ⟨n, Finset.mem_Icc.mpr (Finset.mem_Ioc.mp hnIoc)⟩
    refine ⟨u, ?_, rfl⟩
    simp only [Finset.mem_inf]
    intro p hp
    simp only [primeSetMultiplesInIcc, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (prod_dvd_iff_all_prime_dvd t ht n).mp
      (Finset.mem_filter.mp hn).2 p hp

lemma inf_compl_primeSetMultiples_eq_coprime
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ) :
    s.inf (fun p ↦ (primeSetMultiplesInIcc U p)ᶜ) =
      (Finset.univ : Finset ↥(Finset.Icc 1 U)).filter
        (fun (u : ↥(Finset.Icc 1 U)) ↦
          (u : ℕ).Coprime (primeModulus s)) := by
  ext u
  simp only [Finset.mem_inf, Finset.mem_compl,
    primeSetMultiplesInIcc, Finset.mem_filter, Finset.mem_univ,
    true_and, primeModulus, Nat.coprime_prod_right_iff]
  constructor
  · intro h p hp
    rw [Nat.coprime_comm, (hs p hp).coprime_iff_not_dvd]
    exact h p hp
  · intro h p hp hdiv
    have hpco := h p hp
    rw [Nat.coprime_comm, (hs p hp).coprime_iff_not_dvd] at hpco
    exact hpco hdiv

/-- Inclusion--exclusion formula for the positive denominators coprime to a
squarefree prime-set conductor. -/
lemma card_coprimeDenominators_eq_alternating
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ) :
    ((coprimeDenominators s U).card : ℤ) =
      ∑ t ∈ s.powerset,
        (-1 : ℤ) ^ t.card * (U / (∏ p ∈ t, p) : ℕ) := by
  have hIE := Finset.inclusion_exclusion_card_inf_compl s
    (primeSetMultiplesInIcc U)
  calc
    ((coprimeDenominators s U).card : ℤ) =
        (((Finset.univ : Finset ↥(Finset.Icc 1 U)).filter
          (fun (u : ↥(Finset.Icc 1 U)) ↦
            (u : ℕ).Coprime (primeModulus s))).card : ℤ) := by
      apply congrArg (fun n : ℕ ↦ (n : ℤ))
      refine Finset.card_bij
        (s := coprimeDenominators s U)
        (t := (Finset.univ : Finset ↥(Finset.Icc 1 U)).filter
          (fun (u : ↥(Finset.Icc 1 U)) ↦
            (u : ℕ).Coprime (primeModulus s)))
        (fun n hn ↦ ⟨n, ?_⟩) ?_ ?_ ?_
      · exact (Finset.mem_filter.mp hn).1
      · intro n hn
        simpa [coprimeDenominators] using
          (Finset.mem_filter.mp hn).2
      · intro a ha b hb hab
        exact congrArg Subtype.val hab
      · intro u hu
        refine ⟨u, ?_, Subtype.ext rfl⟩
        simpa [coprimeDenominators] using
          (Finset.mem_filter.mp hu).2
    _ = ((s.inf fun p ↦ (primeSetMultiplesInIcc U p)ᶜ).card : ℤ) := by
      rw [inf_compl_primeSetMultiples_eq_coprime s hs U]
    _ = ∑ t ∈ s.powerset,
          (-1 : ℤ) ^ t.card *
            ((t.inf (primeSetMultiplesInIcc U)).card : ℤ) := hIE
    _ = ∑ t ∈ s.powerset,
          (-1 : ℤ) ^ t.card * (U / (∏ p ∈ t, p) : ℕ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [card_inf_primeSetMultiplesInIcc t
        (fun p hp ↦ hs p (Finset.mem_powerset.mp ht hp)) U]

lemma alternating_prime_reciprocal_eq
    (s : Finset ℕ) (U : ℕ) :
    (∑ t ∈ s.powerset,
        (-1 : ℝ) ^ t.card *
          ((U : ℝ) / (∏ p ∈ t, p : ℕ))) =
      (U : ℝ) * ∏ p ∈ s, (1 - (p : ℝ)⁻¹) := by
  rw [Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_inv_distrib]
  simp only [Nat.cast_prod]
  ring

lemma half_le_one_sub_prime_inv {p : ℕ} (hp : p.Prime) :
    (1 / 2 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) hp2
  norm_num at hinv ⊢
  linarith

lemma prod_one_sub_prime_inv_lower
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (1 / 2 : ℝ) ^ s.card ≤ ∏ p ∈ s, (1 - (p : ℝ)⁻¹) := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod (fun p hp ↦ by positivity)
    (fun p hp ↦ half_le_one_sub_prime_inv (hs p hp))

lemma abs_natCast_div_sub_div_lt_one (U d : ℕ) :
    |((U / d : ℕ) : ℝ) - (U : ℝ) / (d : ℝ)| < 1 := by
  have hle : ((U / d : ℕ) : ℝ) ≤ (U : ℝ) / (d : ℝ) :=
    Nat.cast_div_le
  have hlt : (U : ℝ) / (d : ℝ) < ((U / d : ℕ) : ℝ) + 1 := by
    simpa only [Nat.floor_div_eq_div] using
      (Nat.lt_floor_add_one ((U : ℝ) / (d : ℝ)))
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith

lemma alternating_prime_floor_sum_error
    (s : Finset ℕ) (U : ℕ) :
    |(∑ t ∈ s.powerset,
        (-1 : ℝ) ^ t.card * ((U / (∏ p ∈ t, p) : ℕ) : ℝ)) -
      ∑ t ∈ s.powerset,
        (-1 : ℝ) ^ t.card *
          ((U : ℝ) / (∏ p ∈ t, p : ℕ))| ≤
        (2 : ℝ) ^ s.card := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ t ∈ s.powerset,
        ((-1 : ℝ) ^ t.card * ((U / (∏ p ∈ t, p) : ℕ) : ℝ) -
          (-1 : ℝ) ^ t.card *
            ((U : ℝ) / (∏ p ∈ t, p : ℕ)))| ≤
        ∑ t ∈ s.powerset,
          |((-1 : ℝ) ^ t.card * ((U / (∏ p ∈ t, p) : ℕ) : ℝ) -
            (-1 : ℝ) ^ t.card *
              ((U : ℝ) / (∏ p ∈ t, p : ℕ)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ s.powerset, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [← mul_sub, abs_mul, abs_neg_one_pow]
      simpa only [one_mul] using
        (abs_natCast_div_sub_div_lt_one U (∏ p ∈ t, p)).le
    _ = (2 : ℝ) ^ s.card := by simp

/-- Crude uniform lower bound for the number of Burgess denominators.  The
main term loses at most one half per conductor prime; the
inclusion--exclusion floor errors cost at most the number of subsets. -/
lemma card_coprimeDenominators_lower
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ) :
    (U : ℝ) * (1 / 2 : ℝ) ^ s.card - (2 : ℝ) ^ s.card ≤
      (coprimeDenominators s U).card := by
  let F : ℝ := ∑ t ∈ s.powerset,
    (-1 : ℝ) ^ t.card * ((U / (∏ p ∈ t, p) : ℕ) : ℝ)
  let R : ℝ := ∑ t ∈ s.powerset,
    (-1 : ℝ) ^ t.card * ((U : ℝ) / (∏ p ∈ t, p : ℕ))
  have hcount : ((coprimeDenominators s U).card : ℝ) = F := by
    have h := congrArg (fun z : ℤ ↦ (z : ℝ))
      (card_coprimeDenominators_eq_alternating s hs U)
    simpa only [Int.cast_natCast, Int.cast_sum, Int.cast_mul,
      Int.cast_pow, Int.cast_neg, Int.cast_one] using h
  have herror : |F - R| ≤ (2 : ℝ) ^ s.card :=
    alternating_prime_floor_sum_error s U
  have hR : (U : ℝ) * ∏ p ∈ s, (1 - (p : ℝ)⁻¹) = R :=
    (alternating_prime_reciprocal_eq s U).symm
  have hprod : (U : ℝ) * (1 / 2 : ℝ) ^ s.card ≤ R := by
    rw [← hR]
    exact mul_le_mul_of_nonneg_left
      (prod_one_sub_prime_inv_lower s hs) (by positivity)
  have hRF : R - F ≤ (2 : ℝ) ^ s.card := by
    calc
      R - F ≤ |R - F| := le_abs_self _
      _ = |F - R| := abs_sub_comm _ _
      _ ≤ (2 : ℝ) ^ s.card := herror
  rw [hcount]
  linarith

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessDenominatorAsymptotics.lean` -/

section

/-!
# A subpower lower bound for the admissible amplifier denominators
-/

namespace Pollack17.Burgess

open Filter

theorem coprimeDenominators_lower_half (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (U : ℕ) (hU : 2 * (4 : ℝ) ^ s.card ≤ U) :
    (U : ℝ) / (2 * (2 : ℝ) ^ s.card) ≤ (coprimeDenominators s U).card := by
  let a := (2 : ℝ) ^ s.card
  have ha : 0 < a := by dsimp [a]; positivity
  have h4 : (4 : ℝ) ^ s.card = a ^ 2 := by
    dsimp [a]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hUa : 2 * a ^ 2 ≤ (U : ℝ) := by simpa only [h4] using hU
  have hcalc : ((U : ℝ) / a - a) * (2 * a) = 2 * U - 2 * a ^ 2 := by
    field_simp
  have hhalf : (U : ℝ) / (2 * a) ≤ (U : ℝ) / a - a := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * a)).mpr
    rw [hcalc]
    linarith
  have hbound := card_coprimeDenominators_lower s hs U
  have hmain : (U : ℝ) * (1 / 2 : ℝ) ^ s.card = (U : ℝ) / a := by
    simp [a, div_eq_mul_inv, inv_pow]
  rw [hmain] at hbound
  exact hhalf.trans hbound

theorem eventually_coprimeDenominators_lower {u δ : ℝ} (hu : 0 < u) (hδ : 0 < δ) :
    ∃ Q : ℕ, ∀ (s : Finset ℕ) (_hs : ∀ p ∈ s, p.Prime), Q ≤ primeModulus s →
      ∀ U : ℕ, (primeModulus s : ℝ) ^ u ≤ U →
        (U : ℝ) * (primeModulus s : ℝ) ^ (-δ) ≤ (coprimeDenominators s U).card := by
  have h₁ := eventually_const_mul_pow_primeFactors_le 2 4 (by omega) hu
  have h₂ := eventually_const_mul_pow_primeFactors_le 2 2 (by omega) hδ
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp (h₁.and h₂)
  refine ⟨Q, fun s hs hq U hU => ?_⟩
  have h4 : 2 * (4 : ℝ) ^ s.card ≤ (primeModulus s : ℝ) ^ u := by
    simpa only [primeModulus_primeFactors s hs, Nat.cast_ofNat] using (hQ (primeModulus s) hq).1
  have h2 : 2 * (2 : ℝ) ^ s.card ≤ (primeModulus s : ℝ) ^ δ := by
    simpa only [primeModulus_primeFactors s hs, Nat.cast_ofNat] using (hQ (primeModulus s) hq).2
  have hi := inv_anti₀ (by positivity : (0 : ℝ) < 2 * 2 ^ s.card) h2
  have hi' : (primeModulus s : ℝ) ^ (-δ) ≤ (2 * (2 : ℝ) ^ s.card)⁻¹ := by
    simpa only [Real.rpow_neg (Nat.cast_nonneg _)] using hi
  calc
    _ ≤ (U : ℝ) / (2 * (2 : ℝ) ^ s.card) := by
      exact mul_le_mul_of_nonneg_left hi' (Nat.cast_nonneg U)
    _ ≤ _ := coprimeDenominators_lower_half s hs U (h4.trans hU)

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessCompositeAmplifier.lean` -/

section

/-!
# The Burgess amplifier on power scales
-/

namespace Pollack17.Burgess

open scoped BigOperators

theorem abs_productChar_natCast_of_coprime (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (u : ℕ) (hu : u.Coprime (primeModulus s)) : |productChar s hs u| = 1 := by
  classical
  rw [productChar, Finset.abs_prod]
  apply Finset.prod_eq_one
  intro p _
  have : Fact (Nat.Prime (p : ℕ)) := ⟨hs p p.property⟩
  have hcop : u.Coprime (p : ℕ) := hu.of_dvd_right (Finset.dvd_prod_of_mem id p.property)
  have hnz : (u : ZMod (p : ℕ)) ≠ 0 := by
    intro hz
    exact ((hs p p.property).coprime_iff_not_dvd.mp hcop.symm)
      ((ZMod.natCast_eq_zero_iff u (p : ℕ)).mp hz)
  rw [primeCRT_natCast]
  rcases quadraticChar_dichotomy hnz with h | h <;> simp [localChar, qchar, h]

theorem productChar_amplified_abs_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] {M H U V : ℕ} (hUV : U * V ≤ H) :
    ((coprimeDenominators s U).card : ℝ) * V *
        |∑ i ∈ Finset.range H, productChar s hs (M + i : ℕ)| ≤
      amplifierNumerator (productChar s hs) M H (coprimeDenominators s U) V +
        2 * ((coprimeDenominators s U).card : ℝ) * V * (U * V) := by
  exact amplified_abs_le (productChar s hs) (productChar_mul s hs)
    (abs_productChar_le_one s hs) (coprimeDenominators s U) (Finset.filter_subset _ _)
    (fun _ h => (Finset.mem_filter.mp h).2)
    (fun u h => abs_productChar_natCast_of_coprime s hs u (Finset.mem_filter.mp h).2) hUV

theorem amplifier_scale_le {q : ℕ} [NeZero q] (hq : 1 ≤ q)
    (f : ZMod q → ℝ) (M H U V k : ℕ) (D : Finset ℕ)
    (hD : D ⊆ Finset.Icc 1 U) (hcop : ∀ u ∈ D, u.Coprime q)
    (hH0 : 0 < H) (hU0 : 0 < U) (hsmall : 2 * (U * H) < q)
    {c u v δ : ℝ} (hu1 : u ≤ 1) (huδ : u ≤ c + δ)
    (hH : (H : ℝ) ≤ (q : ℝ) ^ c) (hU : (U : ℝ) ≤ (q : ℝ) ^ u)
    (hV : (V : ℝ) ≤ 2 * (q : ℝ) ^ v) (hv : v * (k + 1 : ℝ) = 1 / 2)
    (hlog : 1 + Real.log (q : ℝ) ≤ (q : ℝ) ^ δ)
    (hmoment : (∑ x : ZMod q, naturalShiftSum f V x ^ (2 * (k + 1))) ≤
      (q : ℝ) ^ δ * ((q : ℝ) * (V : ℝ) ^ (k + 1) +
        Real.sqrt q * (V : ℝ) ^ (2 * (k + 1)))) :
    amplifierNumerator f M H D V ^ (2 * (k + 1)) ≤
      (2 * ((2 : ℝ) ^ (k + 1) + 2 ^ (2 * (k + 1)))) *
        (q : ℝ) ^ ((c + u) * (2 * k + 1 : ℕ) + 3 / 2 + 3 * δ) := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have hcard : (D.card : ℝ) ≤ U := by
    exact_mod_cast (Finset.card_le_card hD).trans_eq (by simp)
  have hHD : (H : ℝ) * D.card ≤ (q : ℝ) ^ (c + u) := by
    rw [Real.rpow_add hq0]
    exact mul_le_mul hH (hcard.trans hU) (Nat.cast_nonneg _) (Real.rpow_nonneg hq0.le _)
  have hpHD : ((H : ℝ) * D.card) ^ (2 * k) ≤ (q : ℝ) ^ ((c + u) * (2 * k : ℕ)) := by
    simpa only [one_mul, one_pow] using pow_le_scaled_rpow
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hq0.le
      (show (H : ℝ) * D.card ≤ 1 * (q : ℝ) ^ (c + u) by simpa only [one_mul] using hHD) (2 * k)
  have he := (naturalRatioEnergy_le (M := M) D hD hcop hH0 hU0 hsmall).trans
    (harmonic_energy_scale_le hq hU0 hu1 huδ hH hU hlog)
  have hm := hmoment.trans (moment_scale_le (by omega : 0 < q)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hv) hV)
  have hh := amplifierNumerator_even_power_le f M H D V k
  have he0 : 0 ≤ naturalRatioEnergy q M H D :=
    Finset.sum_nonneg fun x _ => sq_nonneg _
  have hm0 : 0 ≤ ∑ x : ZMod q, naturalShiftSum f V x ^ (2 * (k + 1)) :=
    Finset.sum_nonneg fun x _ => (even_two_mul _).pow_nonneg _
  calc
    _ ≤ ((H : ℝ) * D.card) ^ (2 * k) * naturalRatioEnergy q M H D *
        ∑ x : ZMod q, naturalShiftSum f V x ^ (2 * (k + 1)) := hh
    _ ≤ (q : ℝ) ^ ((c + u) * (2 * k : ℕ)) *
        (2 * (q : ℝ) ^ (c + u + 2 * δ)) *
        (((2 : ℝ) ^ (k + 1) + 2 ^ (2 * (k + 1))) * (q : ℝ) ^ (3 / 2 + δ)) := by
      exact mul_le_mul (mul_le_mul hpHD he he0 (Real.rpow_nonneg hq0.le _)) hm hm0
        (by positivity)
    _ = (2 * ((2 : ℝ) ^ (k + 1) + 2 ^ (2 * (k + 1)))) *
        ((q : ℝ) ^ ((c + u) * (2 * k : ℕ)) *
          (q : ℝ) ^ (c + u + 2 * δ) * (q : ℝ) ^ (3 / 2 + δ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
      congr 2
      push_cast
      ring

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessBlocks.lean` -/

section

/-!
# Burgess cancellation on a fixed positive-power block length

The inequalities on the exponents below record the parameter budget. They
will be instantiated with arbitrarily small positive slack above one quarter.
-/

namespace Pollack17.Burgess

open Filter
open scoped BigOperators

theorem eventually_power_block_bound (k : ℕ) {c u v δ η : ℝ}
    (hc : 0 < c) (hu : 0 < u) (hv : 0 ≤ v) (hδ : 0 < δ) (hη : 0 < η)
    (hu1 : u ≤ 1) (huδ : u ≤ c + δ) (huv : u + v < c - η) (huc : u + c < 1)
    (hvk : v * (k + 1 : ℝ) = 1 / 2)
    (hgap : (c + u) * (2 * k + 1 : ℕ) + 3 / 2 + 3 * δ <
      (u + v + c - δ - η) * (2 * (k + 1) : ℕ)) :
    ∀ᶠ q : ℕ in atTop, ∀ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime),
      primeModulus s = q → ∀ M : ℕ,
        |∑ i ∈ Finset.range ⌊(q : ℝ) ^ c⌋₊, productChar s hs (M + i : ℕ)| ≤
          (q : ℝ) ^ (c - η) := by
  obtain ⟨Qm, hm⟩ := eventually_productChar_moment_le (k + 1) (by omega) hδ
  obtain ⟨Qd, hd⟩ := eventually_coprimeDenominators_lower (half_pos hu) hδ
  have hroot := eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
    (a := u / 2) (b := u) (by norm_num) (by linarith)
  have hshift := eventually_const_mul_rpow_le (C := 2) (d := 1 / 2)
    (a := u + v) (b := c) (by norm_num) (by linarith)
  have hsmall := eventually_const_mul_rpow_le (C := 2) (d := 1 / 2)
    (a := u + c) (b := 1) (by norm_num) huc
  have herror := eventually_const_mul_rpow_le (C := 4) (d := 1 / 2)
    (a := u + v) (b := c - η) (by norm_num) huv
  have hbudget := eventually_const_mul_rpow_le
    (C := 2 * ((2 : ℝ) ^ (k + 1) + 2 ^ (2 * (k + 1))))
    (d := (1 / 4 : ℝ) ^ (2 * (k + 1))) (by positivity) hgap
  filter_upwards [eventually_ge_atTop Qm, eventually_ge_atTop Qd,
    eventually_ge_atTop 1, eventually_floor_rpow_bounds hc, eventually_floor_rpow_bounds hu,
    eventually_one_add_log_le_rpow hδ, hroot, hshift, hsmall, herror, hbudget]
    with q hqm hqd hq1 hHbounds hUbounds hlog hrootq hshiftq hsmallq herrorq hbudgetq
  intro s hs hsq M
  subst q
  let q := primeModulus s
  let H := ⌊(q : ℝ) ^ c⌋₊
  let U := ⌊(q : ℝ) ^ u⌋₊
  let V := ⌈(q : ℝ) ^ v⌉₊
  let D := coprimeDenominators s U
  let A : ℝ := (D.card : ℝ) * V
  let B : ℝ := (q : ℝ) ^ (c - η) / 2
  have : NeZero (primeModulus s) := ⟨(primeModulus_pos s hs).ne'⟩
  let W := amplifierNumerator (productChar s hs) M H D V
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq1
  have hHlo : (q : ℝ) ^ c / 2 ≤ (H : ℝ) := hHbounds.1
  have hHhi : (H : ℝ) ≤ (q : ℝ) ^ c := hHbounds.2
  have hUlo : (q : ℝ) ^ u / 2 ≤ (U : ℝ) := hUbounds.1
  have hUhi : (U : ℝ) ≤ (q : ℝ) ^ u := hUbounds.2
  have hVbounds := ceil_rpow_bounds hv hq1
  have hVlo : (q : ℝ) ^ v ≤ (V : ℝ) := hVbounds.1
  have hVhi : (V : ℝ) ≤ 2 * (q : ℝ) ^ v := hVbounds.2
  have hHpos : 0 < H := by
    have h : (0 : ℝ) < H := lt_of_lt_of_le (by positivity) hHlo
    exact_mod_cast h
  have hUpos : 0 < U := by
    have h : (0 : ℝ) < U := lt_of_lt_of_le (by positivity) hUlo
    exact_mod_cast h
  have hVpos : 0 < (V : ℝ) := (Real.rpow_pos_of_pos hq0 v).trans_le hVlo
  have hUroot : (q : ℝ) ^ (u / 2) ≤ U := by
    have h : (q : ℝ) ^ (u / 2) ≤ (q : ℝ) ^ u / 2 := by
      simpa only [one_mul, one_div, div_eq_mul_inv, mul_comm] using hrootq
    exact h.trans hUlo
  have hDbase : (U : ℝ) * (q : ℝ) ^ (-δ) ≤ (D.card : ℝ) := hd s hs hqd U hUroot
  have hDlo : (1 / 2 : ℝ) * (q : ℝ) ^ (u - δ) ≤ (D.card : ℝ) := by
    calc
      _ = ((q : ℝ) ^ u / 2) * (q : ℝ) ^ (-δ) := by
        rw [sub_eq_add_neg, Real.rpow_add hq0]
        ring
      _ ≤ (U : ℝ) * (q : ℝ) ^ (-δ) :=
        mul_le_mul_of_nonneg_right hUlo (Real.rpow_nonneg hq0.le _)
      _ ≤ _ := hDbase
  have hDpos : (0 : ℝ) < D.card := lt_of_lt_of_le (by positivity) hDlo
  have hApos : 0 < A := mul_pos hDpos hVpos
  have hUV : (U : ℝ) * V ≤ 2 * (q : ℝ) ^ (u + v) := by
    calc
      _ ≤ (q : ℝ) ^ u * (2 * (q : ℝ) ^ v) :=
        mul_le_mul hUhi hVhi (Nat.cast_nonneg V) (Real.rpow_nonneg hq0.le _)
      _ = _ := by rw [mul_left_comm, ← Real.rpow_add hq0]
  have hUVH : U * V ≤ H := by
    have h : (U : ℝ) * V ≤ H := hUV.trans (hshiftq.trans (by
      simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hHlo))
    exact_mod_cast h
  have hUHsmall : 2 * (U * H) < q := by
    have hUH : (U : ℝ) * H ≤ (q : ℝ) ^ (u + c) := by
      simpa only [Real.rpow_add hq0] using
        mul_le_mul hUhi hHhi (Nat.cast_nonneg H) (Real.rpow_nonneg hq0.le _)
    have hsmall' : 2 * (q : ℝ) ^ (u + c) ≤ (q : ℝ) / 2 := by
      simpa only [Real.rpow_one, one_div, div_eq_mul_inv, mul_comm, one_mul] using hsmallq
    have hstrict : 2 * ((U : ℝ) * H) < q := by
      have hle := (mul_le_mul_of_nonneg_left hUH (by norm_num : (0 : ℝ) ≤ 2)).trans hsmall'
      exact hle.trans_lt (half_lt_self hq0)
    exact_mod_cast hstrict
  have hWpow := amplifier_scale_le hq1 (productChar s hs) M H U V k D
    (Finset.filter_subset _ _) (fun _ h => (Finset.mem_filter.mp h).2)
    hHpos hUpos hUHsmall hu1 huδ hHhi hUhi hVhi hvk hlog (hm s hs hqm V)
  have hAB : (1 / 4 : ℝ) * (q : ℝ) ^ (u + v + c - δ - η) ≤ A * B := by
    have hprod := mul_le_mul hDlo hVlo (Real.rpow_nonneg hq0.le v) (le_of_lt hDpos)
    have hscaled := mul_le_mul_of_nonneg_right hprod
      (by dsimp [B]; positivity : 0 ≤ B)
    refine le_trans ?_ hscaled
    apply le_of_eq
    dsimp [B]
    rw [div_eq_mul_inv]
    calc
      _ = (1 / 4 : ℝ) * ((q : ℝ) ^ (u - δ) * (q : ℝ) ^ v * (q : ℝ) ^ (c - η)) := by
        rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
        congr 2
        ring
      _ = _ := by ring
  have hABpow := scaled_rpow_le_pow (by norm_num : (0 : ℝ) ≤ 1 / 4) hq0.le hAB (2 * (k + 1))
  have hWle : W ≤ A * B := le_of_pow_le_pow_left₀ (n := 2 * (k + 1)) (by omega)
    (by dsimp [A, B]; positivity) (hWpow.trans (hbudgetq.trans hABpow))
  have hamp := productChar_amplified_abs_le s hs (M := M) hUVH
  have hS : |∑ i ∈ Finset.range H, productChar s hs (M + i : ℕ)| ≤ B + 2 * (U : ℝ) * V := by
    apply (mul_le_mul_iff_right₀ hApos).mp
    change (D.card : ℝ) * V * |∑ i ∈ Finset.range H, productChar s hs (M + i : ℕ)| ≤ _
    calc
      _ ≤ W + 2 * (D.card : ℝ) * V * (U * V) := hamp
      _ ≤ A * B + 2 * A * ((U : ℝ) * V) := by
        dsimp only [A]
        nlinarith only [hWle]
      _ = _ := by ring
  have hboundary : 2 * (U : ℝ) * V ≤ (q : ℝ) ^ (c - η) / 2 := by
    have hUV2 := mul_le_mul_of_nonneg_left hUV (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [hUV2, herrorq]
  change |∑ i ∈ Finset.range H, productChar s hs (M + i : ℕ)| ≤ _
  dsimp only [B] at hS
  linarith

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessQuarter.lean` -/

section

/-!
# Quadratic-character cancellation above the quarter-power scale
-/

namespace Pollack17.Burgess

open Filter
open scoped BigOperators

theorem eventually_quarter_block_cancellation {c : ℝ}
    (hc : 1 / 4 < c) (hc' : c < 1 / 2) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ q : ℕ in atTop,
      ∀ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime), primeModulus s = q → ∀ M : ℕ,
        |∑ i ∈ Finset.range ⌊(q : ℝ) ^ c⌋₊, productChar s hs (M + i : ℕ)| ≤
          (q : ℝ) ^ (c - η) := by
  let e := c - 1 / 4
  have he : 0 < e := sub_pos.mpr hc
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / e)
  let v : ℝ := 1 / (2 * (k + 1 : ℝ))
  let u : ℝ := c - v - e / 4
  let η : ℝ := e / (64 * (k + 2 : ℝ))
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hv0 : 0 < v := by dsimp [v]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hveq : v * (k + 1 : ℝ) = 1 / 2 := by dsimp [v]; field_simp
  have hηeq : η * (64 * (k + 2 : ℝ)) = e := by dsimp [η]; field_simp
  have hvsmall : v < e / 4 := by
    have hek : 2 < (k : ℝ) * e := (div_lt_iff₀ he).mp hk
    dsimp [v]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (k + 1 : ℝ))).mpr
    nlinarith only [hek, he]
  have hηsmall : η < e / 4 := by
    have hkη : 0 ≤ (k : ℝ) * η := mul_nonneg hk0 hη.le
    nlinarith only [hηeq, hkη, hη]
  have hu : 0 < u := by dsimp [u, e] at *; linarith
  have hu1 : u ≤ 1 := by dsimp [u]; dsimp [e] at he; linarith
  have huδ : u ≤ c + η := by dsimp [u]; linarith
  have huv : u + v < c - η := by dsimp [u]; linarith
  have huc : u + c < 1 := by dsimp [u]; linarith
  have hgap : (c + u) * (2 * k + 1 : ℕ) + 3 / 2 + 3 * η <
      (u + v + c - η - η) * (2 * (k + 1) : ℕ) := by
    have hid : (u + v + c - η - η) * (2 * (k + 1) : ℕ) -
        ((c + u) * (2 * k + 1 : ℕ) + 3 / 2 + 3 * η) =
        2 * e - v - e / 4 - (4 * (k + 1 : ℝ) + 3) * η := by
      push_cast
      dsimp [u, e]
      nlinarith only [hveq]
    have hηloss : (4 * (k + 1 : ℝ) + 3) * η < e / 16 := by
      nlinarith only [hηeq, hη]
    apply sub_pos.mp
    rw [hid]
    nlinarith only [he, hvsmall, hηloss]
  exact ⟨η, hη, eventually_power_block_bound k (by linarith) hu hv0.le hη hη
    hu1 huδ huv huc hveq hgap⟩

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessLongIntervals.lean` -/

section

/-!
# Extending fixed-block cancellation to every longer interval
-/

namespace Pollack17.Burgess

open Filter
open scoped BigOperators

theorem abs_sum_range_multiple_le (f : ℕ → ℝ) (H : ℕ) {B : ℝ}
    (hblock : ∀ M : ℕ, |∑ i ∈ Finset.range H, f (M + i)| ≤ B) (t M : ℕ) :
    |∑ i ∈ Finset.range (t * H), f (M + i)| ≤ (t : ℝ) * B := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.succ_mul, Finset.sum_range_add]
    have htail : (∑ i ∈ Finset.range H, f (M + (t * H + i))) =
        ∑ i ∈ Finset.range H, f (M + t * H + i) := by
      simp only [Nat.add_assoc]
    rw [htail]
    have htri := (abs_add_le _ _).trans (add_le_add ih (hblock (M + t * H)))
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using htri

theorem abs_sum_range_le_blocks (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {H : ℕ} (hH : 0 < H) {B : ℝ} (hB : 0 ≤ B)
    (hblock : ∀ M : ℕ, |∑ i ∈ Finset.range H, f (M + i)| ≤ B) (M L : ℕ) :
    |∑ i ∈ Finset.range L, f (M + i)| ≤ (L : ℝ) * (B / H) + H := by
  have hdecomp : L = (L / H) * H + L % H := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod L H).symm
  have heq : (∑ i ∈ Finset.range L, f (M + i)) =
      (∑ i ∈ Finset.range ((L / H) * H), f (M + i)) +
        ∑ i ∈ Finset.range (L % H), f (M + ((L / H) * H + i)) := by
    calc
      _ = ∑ i ∈ Finset.range ((L / H) * H + L % H), f (M + i) := by rw [← hdecomp]
      _ = _ := Finset.sum_range_add _ _ _
  have htail : |∑ i ∈ Finset.range (L % H), f (M + ((L / H) * H + i))| ≤ H := by
    calc
      _ ≤ ∑ i ∈ Finset.range (L % H), |f (M + ((L / H) * H + i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (L % H), (1 : ℝ) := Finset.sum_le_sum fun i _ => hf _
      _ = (L % H : ℕ) := by simp
      _ ≤ (H : ℝ) := by exact_mod_cast (Nat.mod_lt L hH).le
  rw [heq]
  calc
    _ ≤ |∑ i ∈ Finset.range ((L / H) * H), f (M + i)| +
        |∑ i ∈ Finset.range (L % H), f (M + ((L / H) * H + i))| := abs_add_le _ _
    _ ≤ ((L / H : ℕ) : ℝ) * B + H :=
      add_le_add (abs_sum_range_multiple_le f H hblock (L / H) M) htail
    _ ≤ ((L : ℝ) / H) * B + H :=
      add_le_add (mul_le_mul_of_nonneg_right Nat.cast_div_le hB) le_rfl
    _ = _ := by ring

theorem block_bound_implies_long_bound {q : ℕ} (hq : 0 < q) {c η : ℝ}
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (hfloor : (q : ℝ) ^ c / 2 ≤ (⌊(q : ℝ) ^ c⌋₊ : ℝ))
    (hblock : ∀ M : ℕ, |∑ i ∈ Finset.range ⌊(q : ℝ) ^ c⌋₊, f (M + i)| ≤
      (q : ℝ) ^ (c - η)) (M L : ℕ) :
    |∑ i ∈ Finset.range L, f (M + i)| ≤
      2 * (L : ℝ) * (q : ℝ) ^ (-η) + (q : ℝ) ^ c := by
  let H := ⌊(q : ℝ) ^ c⌋₊
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have hH0 : (0 : ℝ) < H := lt_of_lt_of_le (by positivity) hfloor
  have hHpos : 0 < H := by exact_mod_cast hH0
  have hratio : (q : ℝ) ^ (c - η) / H ≤ 2 * (q : ℝ) ^ (-η) := by
    apply (div_le_iff₀ hH0).mpr
    calc
      _ = (2 * (q : ℝ) ^ (-η)) * ((q : ℝ) ^ c / 2) := by
        rw [show c - η = -η + c by ring, Real.rpow_add hq0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfloor (by positivity)
  have h := abs_sum_range_le_blocks f hf hHpos (Real.rpow_nonneg hq0.le _) hblock M L
  calc
    _ ≤ (L : ℝ) * ((q : ℝ) ^ (c - η) / H) + H := h
    _ ≤ (L : ℝ) * (2 * (q : ℝ) ^ (-η)) + (q : ℝ) ^ c :=
      add_le_add (mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg L))
        (Nat.floor_le (Real.rpow_nonneg hq0.le c))
    _ = _ := by ring

theorem eventually_squarefree_burgess {d : ℝ} (hd : 1 / 4 < d) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ q : ℕ in atTop,
      ∀ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime), primeModulus s = q →
        ∀ M L : ℕ, (q : ℝ) ^ d ≤ L →
          |∑ i ∈ Finset.range L, productChar s hs (M + i : ℕ)| ≤
            (L : ℝ) * (q : ℝ) ^ (-σ) := by
  let c : ℝ := min ((d + 1 / 4) / 2) (3 / 8)
  have hc : 1 / 4 < c := lt_min (by linarith) (by norm_num)
  have hc' : c < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hcd : c < d := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨η, hη, hblock⟩ := eventually_quarter_block_cancellation hc hc'
  let σ : ℝ := min η (d - c) / 2
  have hσ : 0 < σ := half_pos (lt_min hη (sub_pos.mpr hcd))
  have hση : σ < η := by
    have h := min_le_left η (d - c)
    dsimp [σ]
    linarith
  have hσd : σ < d - c := by
    have h := min_le_right η (d - c)
    dsimp [σ]
    linarith
  have hmain := eventually_const_mul_rpow_le (C := 2) (d := 1 / 2)
    (a := -η) (b := -σ) (by norm_num) (by linarith)
  have hrem := eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
    (a := c) (b := d - σ) (by norm_num) (by linarith)
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hblock, hmain, hrem, eventually_floor_rpow_bounds (by linarith : 0 < c),
    eventually_ge_atTop 1] with q hblockq hmainq hremq hfloor hq1
  intro s hs hsq M L hL
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq1
  have hb := block_bound_implies_long_bound (by omega : 0 < q)
    (fun n => productChar s hs (n : ℕ))
    (fun n => abs_productChar_le_one s hs _) hfloor.1 (hblockq s hs hsq) M L
  have hfirst : 2 * (L : ℝ) * (q : ℝ) ^ (-η) ≤
      (1 / 2 : ℝ) * ((L : ℝ) * (q : ℝ) ^ (-σ)) := by
    have h := mul_le_mul_of_nonneg_left hmainq (Nat.cast_nonneg L)
    nlinarith only [h]
  have hsecond : (q : ℝ) ^ c ≤ (1 / 2 : ℝ) * ((L : ℝ) * (q : ℝ) ^ (-σ)) := by
    have hrem' : (q : ℝ) ^ c ≤ (1 / 2 : ℝ) * ((q : ℝ) ^ d * (q : ℝ) ^ (-σ)) := by
      simpa only [one_mul, sub_eq_add_neg, Real.rpow_add hq0] using hremq
    exact hrem'.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hq0.le _)) (by norm_num))
  nlinarith only [hb, hfirst, hsecond]

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/QuadraticFieldClassification.lean` -/

section

/-!
# Classifying quadratic characters on finite fields
-/

namespace Pollack17

theorem quadratic_apply_square_unit {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) {x : R} (hx : IsUnit x) (hsq : IsSquare x) :
    χ x = 1 := by
  obtain ⟨r, rfl⟩ := hsq
  have hr : IsUnit r := (IsUnit.mul_iff.mp hx).1
  have hrnz : χ r ≠ 0 := MulChar.apply_ne_zero_iff.mpr hr
  rw [map_mul]
  rcases hχ r with h | h | h
  · exact (hrnz h).elim
  · simp [h]
  · simp [h]

theorem quadratic_field_eq_quadraticChar {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (hχ : χ.IsQuadratic) (hne : χ ≠ 1) :
    ∀ x : F, χ x = (quadraticChar F x : ℂ) := by
  classical
  obtain ⟨a, ha⟩ := MulChar.ne_one_iff.mp hne
  have ha0 : χ (a : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr a.isUnit
  have haχ : χ (a : F) = -1 := by
    rcases hχ a with h | h | h
    · exact (ha0 h).elim
    · exact (ha h).elim
    · exact h
  have hansq : ¬IsSquare (a : F) := fun h =>
    ha (quadratic_apply_square_unit χ hχ a.isUnit h)
  have haq : quadraticChar F (a : F) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hansq
  intro x
  by_cases hx : x = 0
  · subst x
    simp only [quadraticChar_zero, Int.cast_zero]
    exact χ.map_nonunit not_isUnit_zero
  by_cases hxsq : IsSquare x
  · rw [quadratic_apply_square_unit χ hχ (isUnit_iff_ne_zero.mpr hx) hxsq,
      (quadraticChar_one_iff_isSquare hx).mpr hxsq]
    norm_num
  have hxq : quadraticChar F x = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hxsq
  have hxaq : quadraticChar F (x * a) = 1 := by rw [map_mul, hxq, haq]; norm_num
  have hxasq : IsSquare (x * (a : F)) :=
    (quadraticChar_one_iff_isSquare (mul_ne_zero hx a.ne_zero)).mp hxaq
  have hxachi := quadratic_apply_square_unit χ hχ
    ((isUnit_iff_ne_zero.mpr hx).mul a.isUnit) hxasq
  rw [map_mul, haχ] at hxachi
  rw [hxq]
  linear_combination -hxachi

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/QuadraticCharacterProducts.lean` -/

section

/-!
# Quadratic characters on a finite product of unit groups
-/

namespace Pollack17

open scoped BigOperators

noncomputable def pullbackUnitChar {R S : Type*} [CommMonoid R] [CommMonoid S]
    (χ : MulChar R ℂ) (f : Sˣ →* Rˣ) : MulChar S ℂ :=
  MulChar.ofUnitHom (χ.toUnitHom.comp f)

theorem pullbackUnitChar_apply_unit {R S : Type*} [CommMonoid R] [CommMonoid S]
    (χ : MulChar R ℂ) (f : Sˣ →* Rˣ) (x : Sˣ) :
    pullbackUnitChar χ f x = χ (f x : R) := by
  simp only [pullbackUnitChar, MulChar.ofUnitHom_coe, MonoidHom.comp_apply,
    MulChar.coe_toUnitHom]

theorem pullbackUnitChar_isQuadratic {R S : Type*} [CommMonoid R] [CommMonoid S]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) (f : Sˣ →* Rˣ) :
    (pullbackUnitChar χ f).IsQuadratic := by
  intro x
  by_cases hx : IsUnit x
  · have heq : pullbackUnitChar χ f x = χ (f hx.unit : R) :=
      pullbackUnitChar_apply_unit χ f hx.unit
    rw [heq]
    exact hχ _
  · exact Or.inl ((pullbackUnitChar χ f).map_nonunit hx)

noncomputable def productUnitEmbedding {ι : Type*} [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)] (i : ι) :
    (R i)ˣ →* (∀ j, R j)ˣ :=
  (MulEquiv.piUnits (M := R)).symm.toMonoidHom.comp
    (MonoidHom.mulSingle (fun j => (R j)ˣ) i)

theorem productUnitEmbedding_val {ι : Type*} [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)] (i : ι) (x : (R i)ˣ) :
    (productUnitEmbedding R i x : ∀ j, R j) = Pi.mulSingle i (x : R i) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [productUnitEmbedding, MulEquiv.piUnits]
  · simp [productUnitEmbedding, MulEquiv.piUnits, hji]

theorem prod_productUnitEmbedding {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)] (x : (∀ j, R j)ˣ) :
    (∏ i, productUnitEmbedding R i (MulEquiv.piUnits x i)) = x := by
  apply Units.ext
  ext j
  simp only [Units.coe_prod, Finset.prod_apply, productUnitEmbedding_val]
  exact Fintype.prod_pi_mulSingle j (fun i => (x : ∀ j, R j) i)

noncomputable def productComponentChar {ι : Type*} [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)] (χ : MulChar (∀ j, R j) ℂ) (i : ι) :
    MulChar (R i) ℂ := pullbackUnitChar χ (productUnitEmbedding R i)

theorem productComponentChar_isQuadratic {ι : Type*} [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)]
    (χ : MulChar (∀ j, R j) ℂ) (hχ : χ.IsQuadratic) (i : ι) :
    (productComponentChar R χ i).IsQuadratic :=
  pullbackUnitChar_isQuadratic χ hχ _

theorem character_eq_prod_components {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)]
    (χ : MulChar (∀ j, R j) ℂ) (x : (∀ j, R j)ˣ) :
    χ (x : ∀ j, R j) = ∏ i, productComponentChar R χ i ((x : ∀ j, R j) i) := by
  calc
    _ = χ ((∏ i, productUnitEmbedding R i (MulEquiv.piUnits x i) : (∀ j, R j)ˣ) : ∀ j, R j) := by
      rw [prod_productUnitEmbedding]
    _ = ∏ i, χ (productUnitEmbedding R i (MulEquiv.piUnits x i) : ∀ j, R j) := by
      rw [Units.coe_prod, map_prod]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact (pullbackUnitChar_apply_unit χ (productUnitEmbedding R i) (MulEquiv.piUnits x i)).symm

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/QuadraticPrimePowerComponents.lean` -/

section

/-!
# Prime-power components of an arbitrary quadratic Dirichlet character
-/

namespace Pollack17

open scoped BigOperators

noncomputable def primePowerCRT (m : ℕ) (hm : m ≠ 0) :
    ZMod m ≃+* (∀ p : m.primeFactors, ZMod ((p : ℕ) ^ m.factorization p)) := by
  have hprod := Nat.prod_primeFactors_coe_pow_factorization hm
  refine (ZMod.ringEquivCongr hprod).trans (ZMod.prodEquivPi _ ?_)
  intro p r hpr
  have hp := Nat.prime_of_mem_primeFactors p.property
  have hr := Nat.prime_of_mem_primeFactors r.property
  have hcop : (p : ℕ).Coprime (r : ℕ) := (Nat.coprime_primes hp hr).mpr (by
    intro h
    exact hpr (Subtype.ext h))
  exact hcop.pow _ _

theorem primePowerCRT_natCast (m : ℕ) (hm : m ≠ 0) (a : ℕ) (p : m.primeFactors) :
    primePowerCRT m hm (a : ZMod m) p = (a : ZMod ((p : ℕ) ^ m.factorization p)) := by
  simp [primePowerCRT]

theorem exists_quadratic_primePower_components {m : ℕ} (hm : m ≠ 0)
    (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) :
    ∃ ψ : ∀ p : m.primeFactors, DirichletCharacter ℂ ((p : ℕ) ^ m.factorization p),
      (∀ p, (ψ p).IsQuadratic) ∧
        ∀ a : ℕ, a.Coprime m → χ (a : ZMod m) =
          ∏ p : m.primeFactors, ψ p (a : ZMod ((p : ℕ) ^ m.factorization p)) := by
  classical
  let R : m.primeFactors → Type := fun p => ZMod ((p : ℕ) ^ m.factorization p)
  let e := primePowerCRT m hm
  let eU := Units.mapEquiv e.toMulEquiv
  let χ' := pullbackUnitChar χ eU.symm.toMonoidHom
  have hχ' : χ'.IsQuadratic := pullbackUnitChar_isQuadratic χ hχ _
  refine ⟨productComponentChar R χ', productComponentChar_isQuadratic R χ' hχ', ?_⟩
  intro a ha
  let x := ZMod.unitOfCoprime a ha
  have hχx : χ (a : ZMod m) = χ' (eU x : ∀ p, R p) := by
    have h := pullbackUnitChar_apply_unit χ eU.symm.toMonoidHom (eU x)
    simpa only [x, χ', MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, ZMod.coe_unitOfCoprime]
      using h.symm
  rw [hχx, character_eq_prod_components R χ' (eU x)]
  apply Finset.prod_congr rfl
  intro p _
  congr 1
  change e (a : ZMod m) p = (a : R p)
  exact primePowerCRT_natCast m hm a p

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/QuadraticPrimePowerSquares.lean` -/

section

/-!
# Squares in the principal congruence subgroups of prime-power units

Hensel's lemma handles both the odd-prime kernel modulo `p` and the
two-adic kernel modulo `8`.
-/

namespace Pollack17

open Polynomial

theorem isSquare_zmod_prime_pow_of_norm {p : ℕ} [Fact p.Prime]
    (a : ℤ) (n : ℕ) (ha : ‖((1 - a : ℤ) : ℤ_[p])‖ < ‖(2 : ℤ_[p])‖ ^ 2) :
    IsSquare (a : ZMod (p ^ n)) := by
  let F : Polynomial ℤ := X ^ 2 - C a
  have hder : F.derivative.aeval (1 : ℤ_[p]) = (2 : ℤ_[p]) := by
    norm_num [F, derivative_sub, derivative_pow, derivative_X]
    exact map_ofNat (aeval (1 : ℤ_[p])) 2
  have hnorm : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    rw [hder]
    simpa [F] using ha
  obtain ⟨z, hz, _⟩ := hensels_lemma hnorm
  have hsq : z ^ 2 = (a : ℤ_[p]) := by simpa [F, sub_eq_zero] using hz
  refine ⟨PadicInt.toZModPow n z, ?_⟩
  have hmap := congrArg (PadicInt.toZModPow n) hsq
  simpa only [map_pow, map_mul, map_intCast, pow_two] using hmap.symm

theorem isSquare_zmod_odd_prime_pow_of_one_mod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : ℤ) (n : ℕ) (ha : (p : ℤ) ∣ 1 - a) : IsSquare (a : ZMod (p ^ n)) := by
  have : Fact p.Prime := ⟨hp⟩
  apply isSquare_zmod_prime_pow_of_norm a n
  have hnorm : ‖(2 : ℤ_[p])‖ = 1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  rw [hnorm, one_pow]
  exact (PadicInt.norm_int_lt_one_iff_dvd (1 - a)).mpr ha

theorem isSquare_zmod_two_pow_of_one_mod_eight (a : ℤ) (n : ℕ)
    (ha : (8 : ℤ) ∣ 1 - a) : IsSquare (a : ZMod (2 ^ n)) := by
  apply isSquare_zmod_prime_pow_of_norm a n
  have hnorm : ‖((1 - a : ℤ) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(3 : ℕ) : ℤ) :=
    PadicInt.norm_int_le_pow_iff_dvd.mpr (by simpa using ha)
  have htwo : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p
  rw [htwo]
  refine hnorm.trans_lt ?_
  norm_num

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/QuadraticPrimePowerReduction.lean` -/

section

/-!
# Reducing quadratic characters at prime powers
-/

namespace Pollack17

theorem quadratic_factorsThrough_of_kernel_squares {m d : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) (hd : d ∣ m)
    (hsquare : ∀ a : ℤ, (d : ℤ) ∣ 1 - a → IsSquare (a : ZMod m)) :
    χ.FactorsThrough d := by
  apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  apply Units.ext
  change χ (x : ZMod m) = 1
  apply quadratic_apply_square_unit χ hχ x.isUnit
  have hval : (((x : ZMod m).val : ℕ) : ZMod d) = 1 := by
    have h := congrArg Units.val hx
    simpa only [ZMod.unitsMap_val, ZMod.cast_eq_val, Units.val_one] using h
  have hdiv : (d : ℤ) ∣ 1 - ((x : ZMod m).val : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_sub, Int.cast_one, Int.cast_natCast, hval, sub_self]
  have hsq := hsquare ((x : ZMod m).val : ℤ) hdiv
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hsq

theorem quadratic_odd_prime_power_factorsThrough {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    (χ : DirichletCharacter ℂ (p ^ n)) (hχ : χ.IsQuadratic) :
    χ.FactorsThrough p := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply quadratic_factorsThrough_of_kernel_squares χ hχ (dvd_pow_self p (by omega : n ≠ 0))
  exact fun a ha => isSquare_zmod_odd_prime_pow_of_one_mod hp hp2 a n ha

theorem quadratic_two_power_factorsThrough {n : ℕ} (hn : 3 ≤ n)
    (χ : DirichletCharacter ℂ (2 ^ n)) (hχ : χ.IsQuadratic) :
    χ.FactorsThrough 8 := by
  have : NeZero (2 ^ n) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hd : 8 ∣ 2 ^ n := by
    have h := Nat.pow_dvd_pow 2 hn
    norm_num at h
    exact h
  exact quadratic_factorsThrough_of_kernel_squares χ hχ hd
    (fun a ha => isSquare_zmod_two_pow_of_one_mod_eight a n ha)

theorem quadratic_of_changeLevel {m d : ℕ} [NeZero m] (hd : d ∣ m)
    (ψ : DirichletCharacter ℂ d) (hψ : (DirichletCharacter.changeLevel hd ψ).IsQuadratic) :
    ψ.IsQuadratic := by
  apply MulChar.isQuadratic_iff_sq_eq_one.mpr
  apply DirichletCharacter.changeLevel_injective hd
  rw [map_pow, map_one, hψ.sq_eq_one]

theorem changeLevel_natCast {R : Type*} [CommMonoidWithZero R] {m d : ℕ}
    (hd : d ∣ m) (ψ : DirichletCharacter R d)
    (a : ℕ) (ha : a.Coprime m) :
    DirichletCharacter.changeLevel hd ψ (a : ZMod m) = ψ (a : ZMod d) := by
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ hd (ZMod.unitOfCoprime a ha)
  simpa only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd] using h

theorem quadratic_odd_prime_power_values {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    (χ : DirichletCharacter ℂ (p ^ n)) (hχ : χ.IsQuadratic) :
    letI : Fact p.Prime := ⟨hp⟩
    ∃ b : Bool, ∀ a : ℕ, a.Coprime p → χ (a : ZMod (p ^ n)) =
      if b then (quadraticChar (ZMod p) (a : ZMod p) : ℂ) else 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let hfactor := quadratic_odd_prime_power_factorsThrough hp hp2 hn χ hχ
  let ψ := hfactor.χ₀
  have hψ : ψ.IsQuadratic := quadratic_of_changeLevel hfactor.dvd ψ (by
    rw [← hfactor.eq_changeLevel]
    exact hχ)
  have heval (a : ℕ) (ha : a.Coprime p) : χ (a : ZMod (p ^ n)) = ψ (a : ZMod p) := by
    rw [hfactor.eq_changeLevel]
    exact changeLevel_natCast hfactor.dvd ψ a (ha.pow_right n)
  by_cases hψ1 : ψ = 1
  · refine ⟨false, fun a ha => ?_⟩
    rw [heval a ha, hψ1]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime a p).mpr ha)
  · refine ⟨true, fun a ha => ?_⟩
    rw [heval a ha]
    exact quadratic_field_eq_quadraticChar ψ hψ hψ1 _

theorem quadratic_two_power_small_level (n : ℕ)
    (χ : DirichletCharacter ℂ (2 ^ n)) (hχ : χ.IsQuadratic) :
    ∃ e : ℕ, e ≤ 3 ∧ e ≤ n ∧ ∃ θ : DirichletCharacter ℂ (2 ^ e), θ.IsQuadratic ∧
      ∀ a : ℕ, a.Coprime (2 ^ n) → χ (a : ZMod (2 ^ n)) = θ (a : ZMod (2 ^ e)) := by
  by_cases hn : n ≤ 3
  · exact ⟨n, hn, le_rfl, χ, hχ, fun _ _ => rfl⟩
  have : NeZero (2 ^ n) := ⟨pow_ne_zero _ (by norm_num)⟩
  let hfactor := quadratic_two_power_factorsThrough (by omega : 3 ≤ n) χ hχ
  let θ := hfactor.χ₀
  have hθ : θ.IsQuadratic := quadratic_of_changeLevel hfactor.dvd θ (by
    rw [← hfactor.eq_changeLevel]
    exact hχ)
  refine ⟨3, le_rfl, by omega, θ, hθ, fun a ha => ?_⟩
  rw [hfactor.eq_changeLevel]
  exact changeLevel_natCast hfactor.dvd θ a ha

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/QuadraticDecomposition.lean` -/

section

/-!
# Decomposing every quadratic Dirichlet character on the units

The only two-adic factor has modulus at most eight. The odd factors are
selected Legendre characters; omitted prime factors contribute the principal
character. Values away from the units will be handled by inclusion-exclusion.
-/

namespace Pollack17

open scoped BigOperators

noncomputable def quadraticPrimeValue (p a : ℕ) : ℂ := by
  classical
  exact if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    (quadraticChar (ZMod p) (a : ZMod p) : ℂ)
  else 0

theorem exists_subset_product_choices (s : Finset ℕ) (f g : ℕ → ℕ → ℂ) (P : ℕ → Prop)
    (h : ∀ p ∈ s, ∃ b : Bool, ∀ a, P a → f p a = if b then g p a else 1) :
    ∃ t ⊆ s, ∀ a, P a → (∏ p ∈ s, f p a) = ∏ p ∈ t, g p a := by
  classical
  choose b hb using h
  let B : ℕ → Bool := fun p => if hp : p ∈ s then b p hp else false
  refine ⟨s.filter (fun p => B p), Finset.filter_subset _ _, fun a ha => ?_⟩
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  simpa only [B, dif_pos hp] using hb p hp a ha

theorem quadratic_character_decomposition {m : ℕ} (hm : m ≠ 0)
    (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) :
    ∃ s : Finset ℕ, s ⊆ m.primeFactors.erase 2 ∧
      ∃ e : ℕ, e ≤ 3 ∧ e ≤ m.factorization 2 ∧
        ∃ θ : DirichletCharacter ℂ (2 ^ e), θ.IsQuadratic ∧
          ∀ a : ℕ, a.Coprime m → χ (a : ZMod m) =
            θ (a : ZMod (2 ^ e)) * ∏ p ∈ s, quadraticPrimeValue p a := by
  classical
  obtain ⟨ψ, hψ, hprod⟩ := exists_quadratic_primePower_components hm χ hχ
  let f : ℕ → ℕ → ℂ := fun p a =>
    if hp : p ∈ m.primeFactors then ψ ⟨p, hp⟩ (a : ZMod (p ^ m.factorization p)) else 1
  have hlocal : ∀ p ∈ m.primeFactors.erase 2, ∃ b : Bool,
      ∀ a : ℕ, a.Coprime m → f p a = if b then quadraticPrimeValue p a else 1 := by
    intro p hp
    have hpne : p ≠ 2 := (Finset.mem_erase.mp hp).1
    have hpm : p ∈ m.primeFactors := (Finset.mem_erase.mp hp).2
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpm
    have : Fact p.Prime := ⟨hpp⟩
    have he : 0 < m.factorization p :=
      hpp.factorization_pos_of_dvd hm (Nat.dvd_of_mem_primeFactors hpm)
    obtain ⟨b, hb⟩ := quadratic_odd_prime_power_values hpp hpne he (ψ ⟨p, hpm⟩) (hψ ⟨p, hpm⟩)
    refine ⟨b, fun a ha => ?_⟩
    have hap : a.Coprime p := ha.of_dvd_right (Nat.dvd_of_mem_primeFactors hpm)
    simpa only [f, dif_pos hpm, quadraticPrimeValue, dif_pos hpp] using hb a hap
  obtain ⟨s, hs, hodd⟩ := exists_subset_product_choices (m.primeFactors.erase 2) f
    quadraticPrimeValue (fun a => a.Coprime m) hlocal
  have htwo : ∃ e : ℕ, e ≤ 3 ∧ e ≤ m.factorization 2 ∧
      ∃ θ : DirichletCharacter ℂ (2 ^ e), θ.IsQuadratic ∧
        ∀ a : ℕ, a.Coprime m → f 2 a = θ (a : ZMod (2 ^ e)) := by
    by_cases h2 : 2 ∈ m.primeFactors
    · obtain ⟨e, he3, hem, θ, hθ, heval⟩ :=
        quadratic_two_power_small_level (m.factorization 2) (ψ ⟨2, h2⟩) (hψ ⟨2, h2⟩)
      refine ⟨e, he3, hem, θ, hθ, fun a ha => ?_⟩
      have hd : 2 ^ m.factorization 2 ∣ m :=
        Nat.prime_two.pow_dvd_iff_le_factorization hm |>.mpr le_rfl
      simpa only [f, dif_pos h2] using heval a (ha.of_dvd_right hd)
    · refine ⟨0, by omega, Nat.zero_le _, 1, ?_, fun a ha => ?_⟩
      · exact MulChar.isQuadratic_iff_sq_eq_one.mpr (one_pow 2)
      · have hunit : IsUnit (a : ZMod (2 ^ 0)) :=
          (ZMod.isUnit_iff_coprime a _).mpr (by simp)
        simp only [f, dif_neg h2, MulChar.one_apply hunit]
  obtain ⟨e, he3, hem, θ, hθ, heval⟩ := htwo
  refine ⟨s, hs, e, he3, hem, θ, hθ, fun a ha => ?_⟩
  have hprod' : χ (a : ZMod m) = ∏ p ∈ m.primeFactors, f p a := by
    rw [hprod a ha]
    rw [← Finset.prod_coe_sort m.primeFactors (fun p => f p a)]
    apply Finset.prod_congr rfl
    intro p _
    simp only [f, dif_pos p.property]
  rw [hprod']
  have hsplit : (∏ p ∈ m.primeFactors, f p a) =
      f 2 a * ∏ p ∈ m.primeFactors.erase 2, f p a := by
    by_cases h2 : 2 ∈ m.primeFactors
    · exact (Finset.mul_prod_erase _ _ h2).symm
    · simp only [Finset.erase_eq_of_notMem h2, f, dif_neg h2, one_mul]
  rw [hsplit, heval a ha, hodd a ha]

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/QuadraticRealCharacter.lean` -/

section

/-!
# Real-valued quadratic characters and the product-character interface
-/

namespace Pollack17

open scoped BigOperators

theorem quadratic_apply_im_zero {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) (x : R) : (χ x).im = 0 := by
  rcases hχ x with h | h | h <;> simp [h]

noncomputable def quadraticRealChar {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) : MulChar R ℝ where
  toFun x := (χ x).re
  map_one' := by rw [map_one, Complex.one_re]
  map_mul' x y := by
    rw [map_mul, Complex.mul_re, quadratic_apply_im_zero χ hχ, zero_mul, sub_zero]
  map_nonunit' x hx := by rw [χ.map_nonunit hx, Complex.zero_re]

theorem quadraticRealChar_apply {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) (x : R) :
    quadraticRealChar χ hχ x = (χ x).re := rfl

theorem quadraticRealChar_isQuadratic {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) : (quadraticRealChar χ hχ).IsQuadratic := by
  intro x
  rcases hχ x with h | h | h
  · exact Or.inl (by simp [quadraticRealChar_apply, h])
  · exact Or.inr (Or.inl (by simp [quadraticRealChar_apply, h]))
  · exact Or.inr (Or.inr (by simp [quadraticRealChar_apply, h]))

theorem ofReal_quadraticRealChar {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) (x : R) :
    (quadraticRealChar χ hχ x : ℂ) = χ x := by
  apply Complex.ext
  · rfl
  · exact (quadratic_apply_im_zero χ hχ x).symm


theorem product_quadraticPrimeValue_eq (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (a : ℕ) :
    (∏ p ∈ s, quadraticPrimeValue p a) =
      (Burgess.productChar s hs (a : ZMod (Burgess.primeModulus s)) : ℂ) := by
  classical
  rw [Burgess.productChar, Complex.ofReal_prod]
  rw [← Finset.prod_coe_sort s (fun p => quadraticPrimeValue p a)]
  apply Finset.prod_congr rfl
  intro p _
  rw [Burgess.primeCRT_natCast]
  simp only [quadraticPrimeValue, dif_pos (hs p p.property), Burgess.localChar, Burgess.qchar,
    Complex.ofReal_intCast]

theorem quadratic_character_real_decomposition {m : ℕ} (hm : m ≠ 0)
    (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) :
    ∃ s : Finset ℕ, s ⊆ m.primeFactors.erase 2 ∧
      ∃ hs : ∀ p ∈ s, p.Prime, ∃ e : ℕ, e ≤ 3 ∧ e ≤ m.factorization 2 ∧
        ∃ θ : DirichletCharacter ℝ (2 ^ e), θ.IsQuadratic ∧
          ∀ a : ℕ, a.Coprime m → quadraticRealChar χ hχ (a : ZMod m) =
            θ (a : ZMod (2 ^ e)) * Burgess.productChar s hs
              (a : ZMod (Burgess.primeModulus s)) := by
  obtain ⟨s, hsm, e, he3, hem, θ, hθ, heval⟩ := quadratic_character_decomposition hm χ hχ
  have hs : ∀ p ∈ s, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp (hsm hp)).2
  refine ⟨s, hsm, hs, e, he3, hem, quadraticRealChar θ hθ,
    quadraticRealChar_isQuadratic θ hθ, fun a ha => ?_⟩
  have h := congrArg Complex.re (heval a ha)
  rw [product_quadraticPrimeValue_eq s hs a] at h
  simpa only [quadraticRealChar_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] using h

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/BurgessProgressions.lean` -/

section

/-!
# The short two-adic factor and arithmetic progressions
-/

namespace Pollack17.Burgess

open Filter
open scoped BigOperators

theorem sum_range_mul_eq_progressions (f : ℕ → ℝ) (h t M : ℕ) :
    (∑ i ∈ Finset.range (t * h), f (M + i)) =
      ∑ a ∈ Finset.range h, ∑ j ∈ Finset.range t, f (M + a + h * j) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    simp_rw [Finset.sum_range_succ]
    rw [Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    ac_rfl

theorem abs_sum_range_le_progressions (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {h : ℕ} (hh : 0 < h) (M H : ℕ) {B : ℝ}
    (hbound : ∀ a ∈ Finset.range h,
      |∑ j ∈ Finset.range (H / h), f (M + a + h * j)| ≤ B) :
    |∑ i ∈ Finset.range H, f (M + i)| ≤ (h : ℝ) * B + h := by
  have hdecomp : H = (H / h) * h + H % h := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod H h).symm
  have heq : (∑ i ∈ Finset.range H, f (M + i)) =
      (∑ a ∈ Finset.range h, ∑ j ∈ Finset.range (H / h), f (M + a + h * j)) +
        ∑ i ∈ Finset.range (H % h), f (M + ((H / h) * h + i)) := by
    calc
      _ = ∑ i ∈ Finset.range ((H / h) * h + H % h), f (M + i) := by rw [← hdecomp]
      _ = _ := by rw [Finset.sum_range_add, sum_range_mul_eq_progressions]
  have hmain : |∑ a ∈ Finset.range h,
      ∑ j ∈ Finset.range (H / h), f (M + a + h * j)| ≤ (h : ℝ) * B := by
    calc
      _ ≤ ∑ a ∈ Finset.range h, |∑ j ∈ Finset.range (H / h), f (M + a + h * j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ Finset.range h, B := Finset.sum_le_sum hbound
      _ = _ := by simp
  have htail : |∑ i ∈ Finset.range (H % h), f (M + ((H / h) * h + i))| ≤ h := by
    calc
      _ ≤ ∑ i ∈ Finset.range (H % h), |f (M + ((H / h) * h + i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (H % h), (1 : ℝ) := Finset.sum_le_sum fun i _ => hf _
      _ = (H % h : ℕ) := by simp
      _ ≤ (h : ℝ) := by exact_mod_cast (Nat.mod_lt H hh).le
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hmain htail)

theorem abs_twisted_progression_sum_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] {h : ℕ} (hcop : h.Coprime (primeModulus s))
    (θ : DirichletCharacter ℝ h) (hθ : θ.IsQuadratic) (a L : ℕ) {B : ℝ} (_hB : 0 ≤ B)
    (hbound : ∀ M : ℕ, |∑ j ∈ Finset.range L,
      productChar s hs (M + j : ℕ)| ≤ B) :
    |∑ j ∈ Finset.range L,
      θ (a + h * j : ℕ) * productChar s hs (a + h * j : ℕ)| ≤ B := by
  let q := primeModulus s
  let t : ℕ := ((h : ZMod q)⁻¹ * a).val
  have halg (j : ℕ) : ((a + h * j : ℕ) : ZMod q) =
      (h : ZMod q) * (t + j : ℕ) := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul]
    dsimp only [t]
    rw [ZMod.natCast_zmod_val, mul_add, ← mul_assoc, ZMod.coe_mul_inv_eq_one h hcop, one_mul]
  have hterm (j : ℕ) : θ (a + h * j : ℕ) * productChar s hs (a + h * j : ℕ) =
      (θ (a : ZMod h) * productChar s hs (h : ZMod q)) * productChar s hs (t + j : ℕ) := by
    have hθval : θ (a + h * j : ℕ) = θ (a : ZMod h) := by
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
    rw [hθval, halg, productChar_mul]
    ring
  have hθabs : |θ (a : ZMod h)| ≤ 1 := by
    rcases hθ (a : ZMod h) with hz | hz | hz <;> norm_num [hz]
  have hcoeff : |θ (a : ZMod h) * productChar s hs (h : ZMod q)| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hθabs (abs_productChar_le_one s hs _) (abs_nonneg _) (by norm_num)).trans_eq
      (one_mul 1)
  simp_rw [hterm]
  rw [← Finset.mul_sum, abs_mul]
  exact (mul_le_mul hcoeff (hbound t) (abs_nonneg _) (by norm_num)).trans_eq (one_mul B)

theorem div_small_modulus_ge_scale {H h : ℕ} (hh : 0 < h) (hh8 : h ≤ 8)
    {Q : ℝ} (hQ : 1 ≤ Q) (hH : 16 * Q ≤ H) : Q ≤ ((H / h : ℕ) : ℝ) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hh8' : (h : ℝ) ≤ 8 := by exact_mod_cast hh8
  have hdiv : (H : ℝ) / h < ((H / h : ℕ) : ℝ) + 1 := by
    simpa only [Nat.floor_div_eq_div] using Nat.lt_floor_add_one ((H : ℝ) / h)
  have hHlt := (div_lt_iff₀ hh0).mp hdiv
  have hmul := mul_le_mul_of_nonneg_left hh8'
    (by positivity : (0 : ℝ) ≤ ((H / h : ℕ) : ℝ) + 1)
  linarith only [hQ, hH, hHlt, hmul]

theorem eventually_twisted_squarefree_burgess {d : ℝ} (hd : 1 / 4 < d) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ q : ℕ in atTop,
      ∀ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime), primeModulus s = q →
        ∀ h : ℕ, 0 < h → h ≤ 8 → h.Coprime q →
          ∀ θ : DirichletCharacter ℝ h, θ.IsQuadratic →
            ∀ M H : ℕ, (q : ℝ) ^ d ≤ H →
              |∑ i ∈ Finset.range H, θ (M + i : ℕ) * productChar s hs (M + i : ℕ)| ≤
                (H : ℝ) * (q : ℝ) ^ (-σ) := by
  let c : ℝ := (d + 1 / 4) / 2
  have hc : 1 / 4 < c := by dsimp [c]; linarith
  have hcd : c < d := by dsimp [c]; linarith
  have hd0 : 0 < d := by linarith
  obtain ⟨η, hη, hburgess⟩ := eventually_squarefree_burgess hc
  let σ : ℝ := min η d / 2
  have hσ : 0 < σ := half_pos (lt_min hη hd0)
  have hση : σ < η := by have h := min_le_left η d; dsimp [σ]; linarith
  have hσd : σ < d := by have h := min_le_right η d; dsimp [σ]; linarith
  have hscale := eventually_const_mul_rpow_le (C := 16) (d := 1) (by norm_num) hcd
  have hmain := eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
    (a := -η) (b := -σ) (by norm_num) (by linarith)
  have htail := eventually_const_mul_rpow_le (C := 8) (d := 1 / 2)
    (a := 0) (b := d - σ) (by norm_num) (by linarith)
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hburgess, hscale, hmain, htail, eventually_ge_atTop 1]
    with q hburgessq hscaleq hmainq htailq hq1
  intro s hs hsq h hh hh8 hcop θ hθ M H hH
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq1
  have : NeZero (primeModulus s) := ⟨(primeModulus_pos s hs).ne'⟩
  have hcop' : h.Coprime (primeModulus s) := by simpa only [hsq] using hcop
  have hscale' : 16 * (q : ℝ) ^ c ≤ (q : ℝ) ^ d := by simpa only [one_mul] using hscaleq
  have hHscale : 16 * (q : ℝ) ^ c ≤ H := hscale'.trans hH
  have hN : (q : ℝ) ^ c ≤ ((H / h : ℕ) : ℝ) :=
    div_small_modulus_ge_scale hh hh8
      (Real.one_le_rpow (by exact_mod_cast hq1) (by linarith)) hHscale
  have hB : 0 ≤ ((H / h : ℕ) : ℝ) * (q : ℝ) ^ (-η) := by positivity
  have hθabs (n : ℕ) : |θ (n : ZMod h)| ≤ 1 := by
    rcases hθ (n : ZMod h) with hz | hz | hz <;> norm_num [hz]
  have hf (n : ℕ) : |θ (n : ZMod h) * productChar s hs (n : ℕ)| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (hθabs n) (abs_productChar_le_one s hs _) (abs_nonneg _) (by norm_num)).trans_eq
      (one_mul 1)
  have hprog (a : ℕ) : |∑ j ∈ Finset.range (H / h),
      θ (a + h * j : ℕ) * productChar s hs (a + h * j : ℕ)| ≤
      ((H / h : ℕ) : ℝ) * (q : ℝ) ^ (-η) :=
    abs_twisted_progression_sum_le s hs hcop' θ hθ a (H / h) hB
      (fun K => hburgessq s hs hsq K (H / h) hN)
  have hsum := abs_sum_range_le_progressions
    (fun n => θ (n : ZMod h) * productChar s hs (n : ℕ)) hf hh M H
    (fun a _ => by simpa only [Nat.add_assoc] using hprog (M + a))
  have hcount : (h : ℝ) * ((H / h : ℕ) : ℝ) ≤ H := by
    exact_mod_cast Nat.mul_div_le H h
  have hraw : |∑ i ∈ Finset.range H, θ (M + i : ℕ) * productChar s hs (M + i : ℕ)| ≤
      (H : ℝ) * (q : ℝ) ^ (-η) + 8 := by
    refine hsum.trans ?_
    have hm := mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hq0.le (-η))
    have hh8' : (h : ℝ) ≤ 8 := by exact_mod_cast hh8
    nlinarith only [hm, hh8']
  have hfirst : (H : ℝ) * (q : ℝ) ^ (-η) ≤
      (1 / 2 : ℝ) * ((H : ℝ) * (q : ℝ) ^ (-σ)) := by
    have hm := mul_le_mul_of_nonneg_left hmainq (Nat.cast_nonneg H)
    nlinarith only [hm]
  have hsecond : (8 : ℝ) ≤ (1 / 2 : ℝ) * ((H : ℝ) * (q : ℝ) ^ (-σ)) := by
    have ht : (8 : ℝ) ≤ (1 / 2 : ℝ) * ((q : ℝ) ^ d * (q : ℝ) ^ (-σ)) := by
      simpa only [Real.rpow_zero, mul_one, sub_eq_add_neg, Real.rpow_add hq0] using htailq
    exact ht.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg hq0.le _)) (by norm_num))
  nlinarith only [hraw, hfirst, hsecond]

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/QuadraticProductCharacters.lean` -/

section

/-!
# Dirichlet-character structures for the reduced product characters
-/

namespace Pollack17

open scoped BigOperators

noncomputable def transportMulChar {R S T : Type*} [CommMonoid R] [CommMonoid S]
    [CommMonoidWithZero T] (χ : MulChar S T) (e : R ≃* S) : MulChar R T where
  toFun x := χ (e x)
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  map_nonunit' x hx := by
    apply χ.map_nonunit
    intro hu
    have h := hu.map e.symm
    exact hx (by simpa only [MulEquiv.symm_apply_apply] using h)

noncomputable def productMulChar {R S T : Type*} [CommMonoid R] [CommMonoid S]
    [CommMonoidWithZero T] (χ : MulChar R T) (ψ : MulChar S T) : MulChar (R × S) T where
  toFun x := χ x.1 * ψ x.2
  map_one' := by simp only [Prod.fst_one, Prod.snd_one, map_one, mul_one]
  map_mul' x y := by simp only [Prod.fst_mul, Prod.snd_mul, map_mul]; ac_rfl
  map_nonunit' x hx := by
    by_cases h₁ : IsUnit x.1
    · have h₂ : ¬IsUnit x.2 := fun h₂ => hx (Prod.isUnit_iff.mpr ⟨h₁, h₂⟩)
      rw [ψ.map_nonunit h₂, mul_zero]
    · rw [χ.map_nonunit h₁, zero_mul]

noncomputable def Burgess.productDirichletChar (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    DirichletCharacter ℝ (Burgess.primeModulus s) where
  toFun := Burgess.productChar s hs
  map_one' := by
    classical
    unfold Burgess.productChar
    apply Finset.prod_eq_one
    intro p _
    have : Fact (Nat.Prime (p : ℕ)) := ⟨hs p p.property⟩
    simp only [Burgess.localChar, Burgess.qchar, map_one, Pi.one_apply, Int.cast_one]
  map_mul' := Burgess.productChar_mul s hs
  map_nonunit' x hx := by
    classical
    have hni : ¬IsUnit (Burgess.primeCRT s hs x) := by
      intro hu
      have h := hu.map (Burgess.primeCRT s hs).symm
      exact hx (by simpa only [RingEquiv.symm_apply_apply] using h)
    have hex : ∃ p : s, ¬IsUnit (Burgess.primeCRT s hs x p) := by
      simpa only [Pi.isUnit_iff, not_forall] using hni
    obtain ⟨p, hp⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    have : Fact (Nat.Prime (p : ℕ)) := ⟨hs p p.property⟩
    simp only [Burgess.localChar, Burgess.qchar, (quadraticChar (ZMod (p : ℕ))).map_nonunit hp,
      Int.cast_zero]

theorem Burgess.productDirichletChar_apply (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (x : ZMod (Burgess.primeModulus s)) :
    Burgess.productDirichletChar s hs x = Burgess.productChar s hs x := rfl

noncomputable def tensorDirichletChar {a b : ℕ} (hab : a.Coprime b)
    (χ : DirichletCharacter ℝ a) (ψ : DirichletCharacter ℝ b) :
    DirichletCharacter ℝ (a * b) :=
  transportMulChar (productMulChar χ ψ) (ZMod.chineseRemainder hab).toMulEquiv

theorem tensorDirichletChar_natCast {a b : ℕ} (hab : a.Coprime b)
    (χ : DirichletCharacter ℝ a) (ψ : DirichletCharacter ℝ b) (n : ℕ) :
    tensorDirichletChar hab χ ψ (n : ZMod (a * b)) = χ (n : ZMod a) * ψ (n : ZMod b) := by
  simp [tensorDirichletChar, transportMulChar, productMulChar]

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/QuadraticReducedCharacter.lean` -/

section

/-!
# A reduced conductor dividing the original modulus
-/

namespace Pollack17

open scoped BigOperators

theorem pow_two_coprime_primeModulus {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (hodd : 2 ∉ s) (e : ℕ) : (2 ^ e).Coprime (Burgess.primeModulus s) := by
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.prod_right
  intro p hp
  exact (Nat.coprime_primes Nat.prime_two (hs p hp)).mpr (by
    intro h
    exact hodd (h ▸ hp))

theorem primeModulus_dvd_of_subset {m : ℕ} {s : Finset ℕ} (hs : s ⊆ m.primeFactors) :
    Burgess.primeModulus s ∣ m :=
  (Finset.prod_dvd_prod_of_subset s m.primeFactors id hs).trans (Nat.prod_primeFactors_dvd m)

theorem exists_quadratic_reduced_character {m : ℕ} (hm : m ≠ 0)
    (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) :
    ∃ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime), s ⊆ m.primeFactors.erase 2 ∧
      ∃ e : ℕ, e ≤ 3 ∧ e ≤ m.factorization 2 ∧
        ∃ θ : DirichletCharacter ℝ (2 ^ e), θ.IsQuadratic ∧
          ∃ hcop : (2 ^ e).Coprime (Burgess.primeModulus s),
            ∃ hd : 2 ^ e * Burgess.primeModulus s ∣ m,
              quadraticRealChar χ hχ = DirichletCharacter.changeLevel hd
                (tensorDirichletChar hcop θ (Burgess.productDirichletChar s hs)) := by
  have : NeZero m := ⟨hm⟩
  obtain ⟨s, hsm, hs, e, he3, hem, θ, hθ, heval⟩ :=
    quadratic_character_real_decomposition hm χ hχ
  have hodd : 2 ∉ s := fun h => (Finset.mem_erase.mp (hsm h)).1 rfl
  have hcop := pow_two_coprime_primeModulus hs hodd e
  have hq : Burgess.primeModulus s ∣ m := primeModulus_dvd_of_subset
    (fun p hp => (Finset.mem_erase.mp (hsm hp)).2)
  have h2 : 2 ^ e ∣ m := Nat.prime_two.pow_dvd_iff_le_factorization hm |>.mpr hem
  have hd := hcop.mul_dvd_of_dvd_of_dvd h2 hq
  refine ⟨s, hs, hsm, e, he3, hem, θ, hθ, hcop, hd, ?_⟩
  apply MulChar.ext
  intro x
  have ha := ZMod.val_coe_unit_coprime x
  have h := changeLevel_natCast hd
    (tensorDirichletChar hcop θ (Burgess.productDirichletChar s hs)) (x : ZMod m).val ha
  rw [tensorDirichletChar_natCast, Burgess.productDirichletChar_apply,
    ← heval _ ha] at h
  simpa only [ZMod.natCast_zmod_val] using h.symm

theorem quadraticRealChar_eq_one_iff {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) : quadraticRealChar χ hχ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    apply MulChar.ext
    intro x
    have hx := ofReal_quadraticRealChar χ hχ (x : R)
    rw [h, MulChar.one_apply_coe, Complex.ofReal_one] at hx
    simpa only [MulChar.one_apply_coe] using hx.symm
  · intro h
    apply MulChar.ext
    intro x
    simp only [quadraticRealChar_apply, h, MulChar.one_apply_coe, Complex.one_re]

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/CharacterIntervalBounds.lean` -/

section

/-!
# Elementary interval bounds and reduced characters
-/

namespace Pollack17.Burgess

open Filter
open scoped BigOperators

theorem abs_quadratic_interval_le_length {q : ℕ}
    (χ : DirichletCharacter ℝ q) (hχ : χ.IsQuadratic) (M H : ℕ) :
    |∑ i ∈ Finset.range H, χ (M + i : ℕ)| ≤ H := by
  calc
    _ ≤ ∑ i ∈ Finset.range H, |χ (M + i : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range H, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rcases hχ (M + i : ℕ) with h | h | h <;> rw [h] <;> norm_num
    _ = _ := by simp

theorem sum_zmod_eq_sum_range {q : ℕ} [NeZero q] (f : ZMod q → ℝ) :
    (∑ a : ZMod q, f a) = ∑ i ∈ Finset.range q, f (i : ZMod q) := by
  classical
  apply Finset.sum_nbij (fun a : ZMod q => a.val)
  · intro a _
    exact Finset.mem_range.mpr a.val_lt
  · exact (ZMod.val_injective q).injOn
  · intro i hi
    exact ⟨(i : ZMod q), Finset.mem_univ _, ZMod.val_cast_of_lt (Finset.mem_range.mp hi)⟩
  · intro a _
    rw [ZMod.natCast_zmod_val]

theorem sum_quadratic_period_eq_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) (M : ℕ) :
    (∑ i ∈ Finset.range q, χ (M + i : ℕ)) = 0 := by
  calc
    _ = ∑ a : ZMod q, χ ((M : ZMod q) + a) := by
      rw [sum_zmod_eq_sum_range]
      simp only [Nat.cast_add]
    _ = ∑ a : ZMod q, χ a := Equiv.sum_comp (Equiv.addLeft (M : ZMod q)) χ
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

theorem abs_quadratic_interval_le_modulus {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ.IsQuadratic) (hχ1 : χ ≠ 1) (M H : ℕ) :
    |∑ i ∈ Finset.range H, χ (M + i : ℕ)| ≤ q := by
  have hf (n : ℕ) : |χ (n : ZMod q)| ≤ 1 := by
    rcases hχ (n : ZMod q) with h | h | h <;> norm_num [h]
  have hblock (K : ℕ) : |∑ i ∈ Finset.range q, χ (K + i : ℕ)| ≤ (0 : ℝ) := by
    rw [sum_quadratic_period_eq_zero χ hχ1 K, abs_zero]
  simpa only [zero_div, mul_zero, zero_add] using
    abs_sum_range_le_blocks (fun n => χ (n : ZMod q)) hf (NeZero.pos q)
      (le_refl (0 : ℝ)) hblock M H

theorem interval_bound_extend_to_short {q : ℕ}
    (χ : DirichletCharacter ℝ q) (hχ : χ.IsQuadratic) {T b : ℝ}
    (hT0 : 0 ≤ T) (hb : 0 ≤ b)
    (hbound : ∀ M H : ℕ, T ≤ H → |∑ i ∈ Finset.range H, χ (M + i : ℕ)| ≤ H * b)
    (M H : ℕ) : |∑ i ∈ Finset.range H, χ (M + i : ℕ)| ≤ H * b + T := by
  by_cases hT : T ≤ H
  · exact (hbound M H hT).trans (le_add_of_nonneg_right hT0)
  · have hlen := abs_quadratic_interval_le_length χ hχ M H
    have hprod : 0 ≤ (H : ℝ) * b := mul_nonneg (Nat.cast_nonneg _) hb
    linarith

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/DivisibleIntervals.lean` -/

section

/-!
# Divisibility classes in translated intervals

The enumeration argument is extracted from `Erdos587.NVDevelopment`.
-/

namespace Pollack17.Burgess

open scoped BigOperators

def residueClassLength (H d a : ℕ) : ℕ :=
  if a < H then (H + d - 1 - a) / d else 0

lemma lt_residueClassLength_iff
    {H d a j : ℕ} (hd : 0 < d) (ha : a < H) :
    j < residueClassLength H d a ↔ a + d * j < H := by
  rw [residueClassLength, if_pos ha, Nat.lt_div_iff_mul_lt hd]
  have heq : H + d - 1 - a - (d - 1) = H - a := by omega
  rw [heq, Nat.mul_comm j d]
  omega

lemma residueClassLength_eq_zero_of_le
    {H d a : ℕ} (ha : H ≤ a) : residueClassLength H d a = 0 := by
  simp [residueClassLength, Nat.not_lt.mpr ha]

/-- Explicit enumeration of the indices in a fixed divisibility class. -/
lemma filter_range_dvd_add_eq_image_residueClass
    {M H d a : ℕ} (hd : 0 < d) (ha : a < d) (hMa : d ∣ M + a) :
    (Finset.range H).filter (fun i ↦ d ∣ M + i) =
      (Finset.range (residueClassLength H d a)).image (fun j ↦ a + d * j) := by
  ext i
  constructor
  · intro hi
    have hiH := (Finset.mem_filter.mp hi).1
    have hMi := (Finset.mem_filter.mp hi).2
    have hmod : i ≡ a [MOD d] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      have hMiz : ((M + i : ℕ) : ZMod d) = 0 :=
        (ZMod.natCast_eq_zero_iff (M + i) d).mpr hMi
      have hMaz : ((M + a : ℕ) : ZMod d) = 0 :=
        (ZMod.natCast_eq_zero_iff (M + a) d).mpr hMa
      calc
        (i : ZMod d) = ((M + i : ℕ) : ZMod d) - (M : ZMod d) := by
          push_cast
          ring
        _ = -(M : ZMod d) := by rw [hMiz]; ring
        _ = ((M + a : ℕ) : ZMod d) - (M : ZMod d) := by rw [hMaz]; ring
        _ = (a : ZMod d) := by push_cast; ring
    have himod : i % d = a := Nat.mod_eq_of_modEq hmod ha
    let j := i / d
    have hij : i = a + d * j := by
      dsimp [j]
      calc
        i = d * (i / d) + i % d := (Nat.div_add_mod i d).symm
        _ = d * (i / d) + a := by rw [himod]
        _ = a + d * (i / d) := by omega
    have hai : a ≤ i := by rw [hij]; exact Nat.le_add_right _ _
    have haH : a < H := hai.trans_lt (Finset.mem_range.mp hiH)
    have hj : j < residueClassLength H d a :=
      (lt_residueClassLength_iff hd haH).mpr (by
        rw [← hij]
        exact Finset.mem_range.mp hiH)
    rw [Finset.mem_image]
    exact ⟨j, Finset.mem_range.mpr hj, hij.symm⟩
  · intro hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    have haH : a < H := by
      by_contra h
      have hz := residueClassLength_eq_zero_of_le
        (d := d) (Nat.le_of_not_gt h)
      rw [Finset.mem_range, hz] at hj
      omega
    have hlt : a + d * j < H :=
      (lt_residueClassLength_iff hd haH).mp (Finset.mem_range.mp hj)
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr hlt
    · obtain ⟨c, hc⟩ := hMa
      refine ⟨c + j, ?_⟩
      calc
        M + (a + d * j) = (M + a) + d * j := by omega
        _ = d * c + d * j := by rw [hc]
        _ = d * (c + j) := by ring

lemma sum_ite_dvd_eq_residueClass
    (f : ℕ → ℝ) {M H d a : ℕ}
    (hd : 0 < d) (ha : a < d) (hMa : d ∣ M + a) :
    (∑ i ∈ Finset.range H, if d ∣ M + i then f (M + i) else 0) =
      ∑ j ∈ Finset.range (residueClassLength H d a),
        f (M + (a + d * j)) := by
  rw [← Finset.sum_filter]
  rw [filter_range_dvd_add_eq_image_residueClass hd ha hMa]
  rw [Finset.sum_image]
  intro x hx y hy hxy
  exact mul_left_cancel₀ hd.ne' (Nat.add_left_cancel hxy)

lemma residueClassLength_le
    {M H d a : ℕ} (hd : 0 < d) (ha : a < d) (hMa : d ∣ M + a) :
    residueClassLength H d a ≤ H := by
  have heq := filter_range_dvd_add_eq_image_residueClass
    (M := M) (H := H) hd ha hMa
  have hinj : Function.Injective (fun j : ℕ ↦ a + d * j) := by
    intro x y hxy
    exact mul_left_cancel₀ hd.ne' (Nat.add_left_cancel hxy)
  have hcard :
      residueClassLength H d a =
        ((Finset.range H).filter (fun i ↦ d ∣ M + i)).card := by
    rw [heq, Finset.card_image_of_injective _ hinj]
    simp
  rw [hcard]
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

/-- A divisibility-restricted sum of a completely multiplicative real
function is, up to the constant factor at `d`, an ordinary consecutive sum
of length at most `H`. -/
lemma exists_divisible_sum_factorization
    (f : ℕ → ℝ) (hmul : ∀ a b, f (a * b) = f a * f b)
    (M H d : ℕ) (hd : 0 < d) :
    ∃ K L : ℕ, L ≤ H ∧
      (∑ i ∈ Finset.range H,
        if d ∣ M + i then f (M + i) else 0) =
        f d * ∑ j ∈ Finset.range L, f (K + j) := by
  have : NeZero d := ⟨hd.ne'⟩
  let a : ℕ := (-(M : ZMod d)).val
  let K : ℕ := (M + a) / d
  let L : ℕ := residueClassLength H d a
  have ha : a < d := ZMod.val_lt _
  have hMa : d ∣ M + a := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    change (M : ZMod d) + (a : ZMod d) = 0
    rw [show (a : ZMod d) = -(M : ZMod d) by
      exact ZMod.natCast_zmod_val _]
    ring
  have hK : d * K = M + a := Nat.mul_div_cancel' hMa
  refine ⟨K, L, residueClassLength_le hd ha hMa, ?_⟩
  rw [sum_ite_dvd_eq_residueClass f hd ha hMa]
  calc
    (∑ j ∈ Finset.range L, f (M + (a + d * j))) =
        ∑ j ∈ Finset.range L, f (d * (K + j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          congr 2
          calc
            M + (a + d * j) = (M + a) + d * j := by omega
            _ = d * K + d * j := by rw [hK]
            _ = d * (K + j) := by ring
    _ = ∑ j ∈ Finset.range L, f d * f (K + j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hmul d (K + j)
    _ = f d * ∑ j ∈ Finset.range L, f (K + j) := by
      rw [Finset.mul_sum]

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/CharacterUnitSieve.lean` -/

section

/-!
# Inclusion-exclusion for an induced character

The unit restriction is expanded before estimating the resulting shorter
intervals. This argument is uniform in both the conductor and the modulus.
-/

namespace Pollack17.Burgess

open scoped BigOperators

theorem prod_divisibility_indicator (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (n : ℕ) :
    (∏ p ∈ s, (if p ∣ n then (1 : ℝ) else 0)) =
      if (∏ p ∈ s, p) ∣ n then 1 else 0 := by
  classical
  by_cases h : (∏ p ∈ s, p) ∣ n
  · rw [if_pos h]
    exact Finset.prod_eq_one fun p hp => if_pos ((prod_dvd_iff_all_prime_dvd s hs n).mp h p hp)
  · rw [if_neg h]
    have hn : ¬ ∀ p ∈ s, p ∣ n := by rwa [← prod_dvd_iff_all_prime_dvd s hs n]
    push_neg at hn
    obtain ⟨p, hp, hpn⟩ := hn
    exact Finset.prod_eq_zero hp (if_neg hpn)

theorem coprime_indicator_eq_alternating {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    (if n.Coprime m then (1 : ℝ) else 0) =
      ∑ t ∈ m.primeFactors.powerset, (-1 : ℝ) ^ t.card *
        (if (∏ p ∈ t, p) ∣ n then 1 else 0) := by
  classical
  have hprod : (if n.Coprime m then (1 : ℝ) else 0) =
      ∏ p ∈ m.primeFactors, (1 - (if p ∣ n then (1 : ℝ) else 0)) := by
    by_cases hc : n.Coprime m
    · rw [if_pos hc]
      symm
      apply Finset.prod_eq_one
      intro p hp
      have hpc := hc.of_dvd_right (Nat.dvd_of_mem_primeFactors hp)
      have hpn := (Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mp hpc.symm
      simp [hpn]
    · rw [if_neg hc]
      obtain ⟨p, hp, hpn, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
      symm
      exact Finset.prod_eq_zero (Nat.mem_primeFactors.mpr ⟨hp, hpm, hm⟩) (by simp [hpn])
  rw [hprod, Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_const_one, mul_one, prod_divisibility_indicator t
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp))]

theorem changeLevel_natCast_eq_ite {d m : ℕ} (hd : d ∣ m)
    (φ : DirichletCharacter ℝ d) (n : ℕ) :
    DirichletCharacter.changeLevel hd φ (n : ZMod m) =
      if n.Coprime m then φ (n : ZMod d) else 0 := by
  by_cases hc : n.Coprime m
  · rw [if_pos hc]
    exact Pollack17.changeLevel_natCast hd φ n hc
  · rw [if_neg hc]
    exact MulChar.map_nonunit _ (by simpa only [ZMod.isUnit_iff_coprime] using hc)

theorem changeLevel_sum_eq_alternating {d m : ℕ} (hm : m ≠ 0) (hd : d ∣ m)
    (φ : DirichletCharacter ℝ d) (M H : ℕ) :
    (∑ i ∈ Finset.range H, DirichletCharacter.changeLevel hd φ (M + i : ℕ)) =
      ∑ t ∈ m.primeFactors.powerset, (-1 : ℝ) ^ t.card *
        ∑ i ∈ Finset.range H, if (∏ p ∈ t, p) ∣ M + i then φ (M + i : ℕ) else 0 := by
  classical
  have hpoint (n : ℕ) : DirichletCharacter.changeLevel hd φ (n : ℕ) =
      ∑ t ∈ m.primeFactors.powerset, (-1 : ℝ) ^ t.card *
        (if (∏ p ∈ t, p) ∣ n then φ (n : ℕ) else 0) := by
    rw [changeLevel_natCast_eq_ite]
    calc
      _ = φ (n : ℕ) * (if n.Coprime m then (1 : ℝ) else 0) := by split_ifs <;> simp
      _ = _ := by
        rw [coprime_indicator_eq_alternating hm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> ring
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem abs_changeLevel_sum_le {d m : ℕ} (hm : m ≠ 0) (hd : d ∣ m)
    (φ : DirichletCharacter ℝ d) (hφ : φ.IsQuadratic) (M H : ℕ) {B : ℝ}
    (hB : 0 ≤ B)
    (hbound : ∀ K L : ℕ, L ≤ H → |∑ j ∈ Finset.range L, φ (K + j : ℕ)| ≤ B) :
    |∑ i ∈ Finset.range H, DirichletCharacter.changeLevel hd φ (M + i : ℕ)| ≤
      (2 : ℝ) ^ m.primeFactors.card * B := by
  classical
  rw [changeLevel_sum_eq_alternating hm hd φ M H]
  calc
    _ ≤ ∑ t ∈ m.primeFactors.powerset,
        |(-1 : ℝ) ^ t.card * ∑ i ∈ Finset.range H,
          if (∏ p ∈ t, p) ∣ M + i then φ (M + i : ℕ) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ m.primeFactors.powerset, B := by
      apply Finset.sum_le_sum
      intro t ht
      rw [abs_mul, abs_neg_one_pow, one_mul]
      have htpos : 0 < ∏ p ∈ t, p := Finset.prod_pos fun p hp =>
        (Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp)).pos
      obtain ⟨K, L, hLH, heq⟩ := exists_divisible_sum_factorization
        (fun n => φ (n : ℕ)) (fun a b => by simp only [Nat.cast_mul, map_mul]) M H _ htpos
      rw [heq, abs_mul]
      have habs : |φ ((∏ p ∈ t, p) : ℕ)| ≤ 1 := by
        rcases hφ ((∏ p ∈ t, p) : ℕ) with h | h | h <;> rw [h] <;> norm_num
      exact (mul_le_mul habs (hbound K L hLH) (abs_nonneg _) (by norm_num)).trans_eq (one_mul B)
    _ = _ := by simp

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/GeneralBurgess.lean` -/

section

/-!
# Burgess cancellation for every quadratic character

The reduced odd conductor is either large enough for Burgess, or small
enough for the elementary complete-period estimate. Inclusion-exclusion
restores all prime factors of the original modulus with a subpower loss.
-/

namespace Pollack17.Burgess

open Filter
open scoped BigOperators

theorem real_quadratic_of_changeLevel {m d : ℕ} [NeZero m] (hd : d ∣ m)
    (φ : DirichletCharacter ℝ d) (hφ : (DirichletCharacter.changeLevel hd φ).IsQuadratic) :
    φ.IsQuadratic := by
  apply MulChar.isQuadratic_iff_sq_eq_one.mpr
  apply DirichletCharacter.changeLevel_injective hd
  rw [map_pow, map_one, hφ.sq_eq_one]

theorem eventually_quadratic_burgess {d : ℝ} (hd : 1 / 4 < d) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic), χ ≠ 1 →
        ∀ M H : ℕ, (m : ℝ) ^ d ≤ H →
          |∑ i ∈ Finset.range H, (χ (M + i : ℕ)).re| ≤
            (H : ℝ) * (m : ℝ) ^ (-σ) := by
  let c : ℝ := (d + 1 / 4) / 2
  have hc : 1 / 4 < c := by dsimp [c]; linarith
  have hcd : c < d := by dsimp [c]; linarith
  have hc0 : 0 < c := by linarith
  let κ : ℝ := (d - c) / 4
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hκd : κ < d := by dsimp [κ]; linarith
  obtain ⟨η, hη, hburgess⟩ := eventually_twisted_squarefree_burgess hc
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp hburgess
  let σ : ℝ := min (κ * η) (min (d - c) (d - κ)) / 8
  have hσ : 0 < σ := by
    dsimp [σ]
    exact div_pos (lt_min (mul_pos hκ hη) (lt_min (sub_pos.mpr hcd) (sub_pos.mpr hκd))) (by norm_num)
  have hση : 2 * σ < κ * η := by
    have h := min_le_left (κ * η) (min (d - c) (d - κ))
    dsimp only [σ] at hσ ⊢
    linarith
  have hσc : c < d - 2 * σ := by
    have h := (min_le_right (κ * η) (min (d - c) (d - κ))).trans (min_le_left _ _)
    dsimp only [σ] at hσ ⊢
    linarith
  have hσκ : κ < d - 2 * σ := by
    have h := (min_le_right (κ * η) (min (d - c) (d - κ))).trans (min_le_right _ _)
    dsimp only [σ] at hσ ⊢
    linarith
  have hlarge := ((tendsto_rpow_atTop hκ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (Q : ℝ))
  have hmain := eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
    (a := -(κ * η)) (b := -(2 * σ)) (by norm_num) (by linarith)
  have htail := eventually_const_mul_rpow_le (C := 1) (d := 1 / 2) (by norm_num) hσc
  have hsmall := eventually_const_mul_rpow_le (C := 8) (d := 1) (by norm_num) hσκ
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hlarge, hmain, htail, hsmall,
    eventually_const_pow_primeFactors_le 2 (by norm_num) hσ, eventually_ge_atTop 1]
    with m hlarge hmain htail hsmall hω hm1
  intro χ hχ hχ1 M H hH
  have hm0 : 0 < m := hm1
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  have : NeZero m := ⟨hm0.ne'⟩
  obtain ⟨s, hs, hsm, e, he3, _hem, θ, hθ, hcop, hD, heq⟩ :=
    exists_quadratic_reduced_character hm0.ne' χ hχ
  let q := primeModulus s
  let φ := tensorDirichletChar hcop θ (productDirichletChar s hs)
  change quadraticRealChar χ hχ = DirichletCharacter.changeLevel hD φ at heq
  have hq0 : 0 < q := primeModulus_pos s hs
  have : NeZero q := ⟨hq0.ne'⟩
  have : NeZero (2 ^ e * q) := ⟨(mul_pos (by positivity) hq0).ne'⟩
  have hφ : φ.IsQuadratic := real_quadratic_of_changeLevel hD φ (by
    rw [← heq]
    exact quadraticRealChar_isQuadratic χ hχ)
  have hφ1 : φ ≠ 1 := by
    intro h
    apply hχ1
    apply (quadraticRealChar_eq_one_iff χ hχ).mp
    rw [heq, h, map_one]
  have hqle : q ≤ m := Nat.le_of_dvd hm0 (primeModulus_dvd_of_subset
    (fun p hp => (Finset.mem_erase.mp (hsm hp)).2))
  have h2 : 2 ^ e ≤ 8 := by
    calc
      2 ^ e ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) he3
      _ = 8 := by norm_num
  have hφbound : ∀ K L : ℕ, L ≤ H →
      |∑ j ∈ Finset.range L, φ (K + j : ℕ)| ≤ (H : ℝ) * (m : ℝ) ^ (-(2 * σ)) := by
    intro K L hLH
    by_cases hqbig : (m : ℝ) ^ κ ≤ q
    · have hQq : Q ≤ q := by
        have hQr : (Q : ℝ) ≤ q := hlarge.trans hqbig
        exact_mod_cast hQr
      have hb (K L : ℕ) (hL : (q : ℝ) ^ c ≤ L) :
          |∑ j ∈ Finset.range L, φ (K + j : ℕ)| ≤ L * (q : ℝ) ^ (-η) := by
        have h := hQ q hQq s hs rfl (2 ^ e) (by positivity) h2 hcop θ hθ K L hL
        simpa only [φ, tensorDirichletChar_natCast, productDirichletChar_apply] using h
      have hraw := interval_bound_extend_to_short φ hφ
        (Real.rpow_nonneg (by positivity) c) (Real.rpow_nonneg (by positivity) (-η)) hb K L
      have hneg : (q : ℝ) ^ (-η) ≤ (m : ℝ) ^ (-(κ * η)) := by
        calc
          _ ≤ ((m : ℝ) ^ κ) ^ (-η) := Real.rpow_le_rpow_of_nonpos
            (Real.rpow_pos_of_pos hmR _) hqbig (by linarith)
          _ = _ := by rw [← Real.rpow_mul hmR.le]; congr 1; ring
      have hpos : (q : ℝ) ^ c ≤ (m : ℝ) ^ c :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hqle) hc0.le
      have hfirst : (L : ℝ) * (q : ℝ) ^ (-η) ≤
          (1 / 2 : ℝ) * ((H : ℝ) * (m : ℝ) ^ (-(2 * σ))) := by
        have hLM : (L : ℝ) ≤ H := by exact_mod_cast hLH
        have hneg' : (q : ℝ) ^ (-η) ≤ (1 / 2 : ℝ) * (m : ℝ) ^ (-(2 * σ)) :=
          hneg.trans (by simpa only [one_mul] using hmain)
        calc
          _ ≤ (H : ℝ) * ((1 / 2 : ℝ) * (m : ℝ) ^ (-(2 * σ))) :=
            mul_le_mul hLM hneg' (Real.rpow_nonneg (by positivity) _) (Nat.cast_nonneg _)
          _ = _ := by ring
      have hsecond : (q : ℝ) ^ c ≤
          (1 / 2 : ℝ) * ((H : ℝ) * (m : ℝ) ^ (-(2 * σ))) := by
        have ht : (m : ℝ) ^ c ≤
            (1 / 2 : ℝ) * ((m : ℝ) ^ d * (m : ℝ) ^ (-(2 * σ))) := by
          simpa only [one_mul, sub_eq_add_neg, Real.rpow_add hmR] using htail
        exact (hpos.trans ht).trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg hmR.le _)) (by norm_num))
      linarith only [hraw, hfirst, hsecond]
    · have hperiod := abs_quadratic_interval_le_modulus φ hφ hφ1 K L
      have hqsmall : (q : ℝ) ≤ (m : ℝ) ^ κ := (lt_of_not_ge hqbig).le
      have h2R : ((2 ^ e : ℕ) : ℝ) ≤ 8 := by exact_mod_cast h2
      have hperiod' : |∑ j ∈ Finset.range L, φ (K + j : ℕ)| ≤ 8 * (m : ℝ) ^ κ := by
        refine hperiod.trans ?_
        rw [Nat.cast_mul]
        exact mul_le_mul h2R hqsmall (Nat.cast_nonneg _) (by norm_num)
      have hsm' : 8 * (m : ℝ) ^ κ ≤ (m : ℝ) ^ d * (m : ℝ) ^ (-(2 * σ)) := by
        simpa only [one_mul, sub_eq_add_neg, Real.rpow_add hmR] using hsmall
      exact (hperiod'.trans hsm').trans
        (mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg hmR.le _))
  have hsieve := abs_changeLevel_sum_le hm0.ne' hD φ hφ M H (by positivity) hφbound
  have hlast : (2 : ℝ) ^ m.primeFactors.card * ((H : ℝ) * (m : ℝ) ^ (-(2 * σ))) ≤
      (H : ℝ) * (m : ℝ) ^ (-σ) := by
    calc
      _ ≤ (m : ℝ) ^ σ * ((H : ℝ) * (m : ℝ) ^ (-(2 * σ))) :=
        mul_le_mul_of_nonneg_right hω (by positivity)
      _ = _ := by
        rw [mul_left_comm, ← Real.rpow_add hmR]
        congr 2
        ring
  have hsum : (∑ i ∈ Finset.range H, (χ (M + i : ℕ)).re) =
      ∑ i ∈ Finset.range H, DirichletCharacter.changeLevel hD φ (M + i : ℕ) := by
    simp only [← heq, quadraticRealChar_apply]
  rw [hsum]
  exact hsieve.trans hlast

end Pollack17.Burgess

end

/-! ### Upstream module `ErdosProblems/Erdos1141/ReciprocalIntervals.lean` -/

section

/-!
# Discrete partial summation for reciprocal character sums
-/

namespace Pollack17

open scoped BigOperators

theorem abs_reciprocal_interval_le (f : ℕ → ℝ) {x y : ℕ} (hx : 0 < x) (hxy : x ≤ y)
    {b : ℝ} (hb : 0 ≤ b)
    (hprefix : ∀ n : ℕ, x ≤ n → n ≤ y →
      |∑ i ∈ Finset.range (n + 1), f i| ≤ (n : ℝ) * b) :
    |∑ i ∈ Finset.Ioc x y, f i / (i : ℝ)| ≤ b * (3 + Real.log (y : ℝ)) := by
  by_cases heq : x = y
  · subst y
    have hy1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
    simp only [Finset.Ioc_self, Finset.sum_empty, abs_zero]
    exact mul_nonneg hb (by linarith [Real.log_nonneg hy1])
  have hlt : x < y := lt_of_le_of_ne hxy heq
  have hxR : 0 < (x : ℝ) := by exact_mod_cast hx
  have hyR : 0 < (y : ℝ) := by exact_mod_cast (hx.trans_le hxy)
  let S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), f i
  have hid : (∑ i ∈ Finset.Ioc x y, f i / (i : ℝ)) =
      (y : ℝ)⁻¹ * S y - ((x + 1 : ℕ) : ℝ)⁻¹ * S x -
        ∑ i ∈ Finset.Ioc x (y - 1),
          (((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i := by
    simpa only [S, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      Finset.sum_Ioc_by_parts (fun i : ℕ => (i : ℝ)⁻¹) f hlt
  have hend : |(y : ℝ)⁻¹ * S y| ≤ b := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hyR)]
    calc
      _ ≤ (y : ℝ)⁻¹ * ((y : ℝ) * b) := mul_le_mul_of_nonneg_left
        (hprefix y hxy le_rfl) (inv_nonneg.mpr hyR.le)
      _ = _ := by field_simp
  have hstart : |((x + 1 : ℕ) : ℝ)⁻¹ * S x| ≤ b := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < ((x + 1 : ℕ) : ℝ)⁻¹)]
    calc
      _ ≤ ((x + 1 : ℕ) : ℝ)⁻¹ * ((x : ℝ) * b) :=
        mul_le_mul_of_nonneg_left (hprefix x le_rfl hxy) (by positivity)
      _ ≤ ((x + 1 : ℕ) : ℝ)⁻¹ * (((x + 1 : ℕ) : ℝ) * b) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by push_cast; linarith) hb) (by positivity)
      _ = b := by field_simp
  have hterm (i : ℕ) (hi : i ∈ Finset.Ioc x (y - 1)) :
      |(((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i| ≤ b * (i : ℝ)⁻¹ := by
    have hix := (Finset.mem_Ioc.mp hi).1
    have hiy := (Finset.mem_Ioc.mp hi).2
    have hiR : 0 < (i : ℝ) := by exact_mod_cast (hx.trans hix)
    have hi1R : 0 < ((i + 1 : ℕ) : ℝ) := by positivity
    have hinv : ((i + 1 : ℕ) : ℝ)⁻¹ ≤ (i : ℝ)⁻¹ :=
      inv_anti₀ hiR (by push_cast; linarith)
    have hdiff : 0 ≤ (i : ℝ)⁻¹ - ((i + 1 : ℕ) : ℝ)⁻¹ := sub_nonneg.mpr hinv
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hinv)]
    calc
      _ = ((i : ℝ)⁻¹ - ((i + 1 : ℕ) : ℝ)⁻¹) * |S i| := by ring
      _ ≤ ((i : ℝ)⁻¹ - ((i + 1 : ℕ) : ℝ)⁻¹) * ((i : ℝ) * b) :=
        mul_le_mul_of_nonneg_left (hprefix i hix.le (by omega)) hdiff
      _ = b * ((i + 1 : ℕ) : ℝ)⁻¹ := by
        push_cast
        field_simp
        ring
      _ ≤ b * (i : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hinv hb
  have hsum : |∑ i ∈ Finset.Ioc x (y - 1),
      (((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i| ≤ b * (1 + Real.log (y : ℝ)) := by
    calc
      _ ≤ ∑ i ∈ Finset.Ioc x (y - 1),
          |(((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Ioc x (y - 1), b * (i : ℝ)⁻¹ := Finset.sum_le_sum hterm
      _ = b * ∑ i ∈ Finset.Ioc x (y - 1), (i : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ b * ∑ i ∈ Finset.Icc 1 y, (i : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ hb
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          have hi := Finset.mem_Ioc.mp hi
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        · intro i _ _
          positivity
      _ ≤ _ := mul_le_mul_of_nonneg_left (Burgess.sum_Icc_inv_natCast_le_one_add_log y) hb
  rw [hid]
  calc
    _ ≤ |(y : ℝ)⁻¹ * S y| + |((x + 1 : ℕ) : ℝ)⁻¹ * S x| +
        |∑ i ∈ Finset.Ioc x (y - 1), (((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i| :=
      (by
        have h₁ := norm_sub_le ((y : ℝ)⁻¹ * S y - ((x + 1 : ℕ) : ℝ)⁻¹ * S x)
          (∑ i ∈ Finset.Ioc x (y - 1), (((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i)
        have h₂ := norm_sub_le ((y : ℝ)⁻¹ * S y) (((x + 1 : ℕ) : ℝ)⁻¹ * S x)
        simp only [Real.norm_eq_abs] at h₁ h₂
        linarith only [h₁, h₂])
    _ ≤ b + b + b * (1 + Real.log (y : ℝ)) := add_le_add (add_le_add hend hstart) hsum
    _ = _ := by ring

end Pollack17

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldCrossLevelCharacters.lean` -/

section

/-!
# Cross-level characters in Goldfeld's argument

Two primitive real characters in Theorem 12.9 can have different moduli.
Mathlib's cross-level product lifts them to the least common multiple of those
moduli.  This file records the exact distinctness, quadraticity,
nonprincipality, and conductor facts used before the four-factor Dirichlet
series is formed.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, Theorem 12.9, printed
pp. 125--126.  Semantic review: `SEM-549`.
-/

noncomputable section

namespace BoundedGaps.Maynard

/-- Two characters at possibly different levels are distinct when their
canonical lifts to the common least-common-multiple level are unequal. -/
def goldfeldCharactersDistinct {q1 q : ℕ}
    (chi1 : DirichletCharacter Complex q1)
    (chi : DirichletCharacter Complex q) : Prop :=
  chi1.changeLevel (Nat.dvd_lcm_left q1 q) ≠
    chi.changeLevel (Nat.dvd_lcm_right q1 q)

/-- At one level, Goldfeld distinctness is ordinary character inequality. -/
theorem goldfeldCharactersDistinct_same_level_iff
    {q : ℕ} [NeZero q]
    (chi1 chi : DirichletCharacter Complex q) :
    goldfeldCharactersDistinct chi1 chi ↔ chi1 ≠ chi := by
  letI : NeZero (Nat.lcm q q) :=
    ⟨Nat.lcm_ne_zero (NeZero.ne q) (NeZero.ne q)⟩
  unfold goldfeldCharactersDistinct
  rw [show Nat.dvd_lcm_right q q = Nat.dvd_lcm_left q q from
    Subsingleton.elim _ _]
  exact (DirichletCharacter.changeLevel_injective
    (R := Complex) (Nat.dvd_lcm_left q q)).ne_iff

/-- Primitive characters at unequal moduli remain unequal after lifting to
their common level. -/
theorem goldfeldCharactersDistinct_of_modulus_ne
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter Complex q1)
    (chi : DirichletCharacter Complex q)
    (hprimitive1 : DirichletCharacter.IsPrimitive chi1)
    (hprimitive : DirichletCharacter.IsPrimitive chi)
    (hmodulus : q1 ≠ q) :
    goldfeldCharactersDistinct chi1 chi := by
  letI : NeZero (Nat.lcm q1 q) :=
    ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩
  rw [goldfeldCharactersDistinct]
  intro heq
  apply hmodulus
  have hconductor := congrArg DirichletCharacter.conductor heq
  rw [chi1.conductor_changeLevel, chi.conductor_changeLevel] at hconductor
  exact hprimitive1.symm.trans (hconductor.trans hprimitive)

private lemma changeLevel_sq_eq_one
    {q m : ℕ} (hqm : q ∣ m)
    (chi : DirichletCharacter Complex q) (hsquare : chi ^ 2 = 1) :
    (chi.changeLevel hqm) ^ 2 = 1 := by
  rw [← map_pow, hsquare, map_one]


/-- A square-principal character cannot have principal cross-level product
with a distinct character. -/
theorem goldfeldCrossLevelMul_ne_one
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter Complex q1)
    (chi : DirichletCharacter Complex q)
    (hsquare1 : chi1 ^ 2 = 1)
    (hdistinct : goldfeldCharactersDistinct chi1 chi) :
    DirichletCharacter.mul chi1 chi ≠ 1 := by
  intro hprincipal
  apply hdistinct
  have hsquareLift := changeLevel_sq_eq_one
    (Nat.dvd_lcm_left q1 q) chi1 hsquare1
  have hproduct :
      chi1.changeLevel (Nat.dvd_lcm_left q1 q) *
          chi.changeLevel (Nat.dvd_lcm_right q1 q) = 1 := by
    simpa [DirichletCharacter.mul] using hprincipal
  have hinv :
      (chi1.changeLevel (Nat.dvd_lcm_left q1 q))⁻¹ =
        chi1.changeLevel (Nat.dvd_lcm_left q1 q) := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using hsquareLift
  exact ((eq_inv_of_mul_eq_one_right hproduct).trans hinv).symm


end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/InducingEulerProduct.lean` -/

section

/-!
# The inducing Dirichlet Euler product

The L-function of a character is the L-function of its inducing primitive
character times an exact finite product over the prime divisors of the
original modulus. Inactive conductor-prime factors are retained as factors
equal to one.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 110,
equation (11.2), and printed pp. 112--113. Semantic review: `SEM-506`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex

private local instance conductorNeZero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    NeZero chi.conductor :=
  ⟨chi.conductor_ne_zero⟩

/-- The exact finite Euler product relating a character to its inducing
primitive character. Inactive factors are retained as factors equal to one. -/
noncomputable def inducingEulerProduct
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors,
    (1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s))

private lemma primitiveCharacter_ne_one_of_ne_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) :
    chi.primitiveCharacter ≠ 1 := by
  intro hpsi
  apply hchi
  rw [← chi.changeLevel_primitiveCharacter]
  exact (DirichletCharacter.changeLevel_eq_one_iff
    chi.conductor_dvd_level).2 hpsi

/-- The guarded change-of-level identity for an arbitrary character. -/
theorem LFunction_eq_inducingPrimitive_mul_inducingEulerProduct
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hguard : chi ≠ 1 ∨ s ≠ 1) :
    DirichletCharacter.LFunction chi s =
      DirichletCharacter.LFunction chi.primitiveCharacter s *
        inducingEulerProduct chi s := by
  have hprimitiveGuard : chi.primitiveCharacter ≠ 1 ∨ s ≠ 1 :=
    hguard.imp (primitiveCharacter_ne_one_of_ne_one chi) id
  calc
    DirichletCharacter.LFunction chi s =
        DirichletCharacter.LFunction
          (DirichletCharacter.changeLevel chi.conductor_dvd_level
            chi.primitiveCharacter) s := by
      rw [chi.changeLevel_primitiveCharacter]
    _ = DirichletCharacter.LFunction chi.primitiveCharacter s *
        ∏ p ∈ q.primeFactors,
          (1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s)) :=
      DirichletCharacter.LFunction_changeLevel chi.conductor_dvd_level
        chi.primitiveCharacter hprimitiveGuard
    _ = _ := rfl

private lemma norm_character_mul_cpow_lt_one
    {d : ℕ} (psi : DirichletCharacter ℂ d)
    (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 0 < s.re) :
    ‖psi p * (p : ℂ) ^ (-s)‖ < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos, neg_re]
  calc
    ‖psi p‖ * (p : ℝ) ^ (-s.re) ≤
        1 * (p : ℝ) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right (psi.norm_le_one p)
        (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    _ < 1 := by
      simpa using
        Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_neg_of_pos hs)

private lemma inducingEulerFactor_ne_zero_of_re_pos
    {d : ℕ} (psi : DirichletCharacter ℂ d)
    (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 0 < s.re) :
    (1 : ℂ) - psi p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro hzero
  have hw : psi p * (p : ℂ) ^ (-s) = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hnorm := norm_character_mul_cpow_lt_one psi p hp s hs
  rw [hw, norm_one] at hnorm
  exact (lt_irrefl 1) hnorm

/-- The inducing product has no zero in the open right half-plane. -/
theorem inducingEulerProduct_ne_zero_of_re_pos
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) :
    inducingEulerProduct chi s ≠ 0 := by
  rw [inducingEulerProduct, Finset.prod_ne_zero_iff]
  intro p hp
  exact inducingEulerFactor_ne_zero_of_re_pos chi.primitiveCharacter p
    (Nat.prime_of_mem_primeFactors hp) s hs



end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/FixedStripGammaRatio.lean` -/

section

/-!
# Fixed-strip Dirichlet Gamma-factor ratio

This file proves the absolute polynomial bound for the Gamma-factor quotient
used in the primitive functional equation. The source comparison is
Koukoulopoulos, printed p. 24, Exercise 1.12(a), and printed p. 114,
Lemma 11.4; see semantic review SEM-476.

The proof uses an eleven-step reciprocal-Gamma recurrence and Euler's Beta
integral. This retains Mathlib's totalized values at the classical Gamma
poles instead of imposing a nonzero denominator hypothesis.
-/

namespace BoundedGaps.Maynard

open Complex Set MeasureTheory

private lemma one_div_Gamma_eq_prod_mul_one_div_Gamma_add_nat
    (z : ℂ) (n : ℕ) :
    (Complex.Gamma z)⁻¹ =
      (∏ j ∈ Finset.range n, (z + j)) * (Complex.Gamma (z + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ih, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one,
        Finset.prod_range_succ, Nat.cast_succ]
      ring_nf

private lemma Gamma_div_Gamma_eq_prod_mul_beta_div
    (w X : ℂ) (d : ℝ) (hX : 0 < X.re) (hd : 0 < d)
    (hsum : X + (d : ℂ) = w + 11) :
    Complex.Gamma X / Complex.Gamma w =
      (∏ j ∈ Finset.range 11, (w + j)) *
        (Complex.betaIntegral X d / Complex.Gamma d) := by
  have hXd : 0 < (X + (d : ℂ)).re := by simp; linarith
  have hGXd := Complex.Gamma_ne_zero_of_re_pos hXd
  have hGd := Complex.Gamma_ne_zero_of_re_pos
    (show 0 < ((d : ℂ)).re by simpa)
  rw [div_eq_mul_inv, one_div_Gamma_eq_prod_mul_one_div_Gamma_add_nat w 11]
  have hsum' : w + (11 : ℕ) = X + (d : ℂ) := by simpa using hsum.symm
  rw [hsum', Complex.betaIntegral_eq_Gamma_mul_div X d hX
    (show 0 < ((d : ℂ)).re by simpa)]
  field_simp [hGXd, hGd]

private lemma norm_betaIntegral_fixed_re_le
    {u : ℂ} {q : ℝ} (hu : (1 / 4 : ℝ) ≤ u.re)
    (hq : (1 / 2 : ℝ) ≤ q) :
    ‖Complex.betaIntegral u q‖ ≤ 12 := by
  rw [Complex.betaIntegral]
  let f : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ ((q : ℂ) - 1)
  let g : ℝ → ℝ := fun x =>
    2 * x ^ (-(3 / 4 : ℝ)) + 2 * (1 - x) ^ (-(1 / 2 : ℝ))
  have hxpow : IntervalIntegrable (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hhalfpow :
      IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hsubpow :
      IntervalIntegrable (fun x : ℝ => (1 - x) ^ (-(1 / 2 : ℝ))) volume 0 1 := by
    simpa only [sub_zero, sub_self] using (hhalfpow.comp_sub_left 1).symm
  have hg : IntervalIntegrable g volume 0 1 :=
    (hxpow.const_mul 2).add (hsubpow.const_mul 2)
  have hf : IntervalIntegrable f volume 0 1 :=
    Complex.betaIntegral_convergent
      (lt_of_lt_of_le (by norm_num) hu)
      (show 0 < ((q : ℂ)).re by simp; linarith)
  have hpoint : ∀ x : ℝ, x ∈ Icc 0 1 → ‖f x‖ ≤ g x := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · have hzero : ‖(0 : ℂ) ^ (u - 1)‖ ≤ 1 := by
        by_cases h : u - 1 = 0
        · rw [h, Complex.cpow_zero, norm_one]
        · rw [Complex.zero_cpow h, norm_zero]
          norm_num
      have htwo : ‖(0 : ℂ) ^ (u - 1)‖ ≤ 2 := hzero.trans (by norm_num)
      simpa [f, g] using htwo
    rcases eq_or_ne x 1 with rfl | hx1
    · have hzero : ‖(0 : ℂ) ^ ((q : ℂ) - 1)‖ ≤ 1 := by
        by_cases h : (q : ℂ) - 1 = 0
        · rw [h, Complex.cpow_zero, norm_one]
        · rw [Complex.zero_cpow h, norm_zero]
          norm_num
      have htwo : ‖(0 : ℂ) ^ ((q : ℂ) - 1)‖ ≤ 2 := hzero.trans (by norm_num)
      simpa [f, g] using htwo
    have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have hsubpos : 0 < 1 - x := sub_pos.mpr hxlt
    dsimp [f]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos hsubpos]
    simp only [sub_re, one_re, ofReal_re]
    have hxpow_le : x ^ (u.re - 1) ≤ x ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hxpos hx.2 (by linarith)
    have hsubpow_le :
        (1 - x) ^ (q - 1) ≤ (1 - x) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hsubpos (sub_le_self 1 hxpos.le) (by linarith)
    have hxnonneg := Real.rpow_nonneg hxpos.le (u.re - 1)
    have hsubnonneg := Real.rpow_nonneg hsubpos.le (q - 1)
    have hbase :
        x ^ (u.re - 1) * (1 - x) ^ (q - 1) ≤
          x ^ (-(3 / 4 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul hxpow_le hsubpow_le hsubnonneg
        (Real.rpow_nonneg hxpos.le (-(3 / 4 : ℝ)))
    have hmajor :
        x ^ (-(3 / 4 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)) ≤ g x := by
      by_cases hhalf : x ≤ 1 / 2
      · have hsubhalf : (1 / 2 : ℝ) ≤ 1 - x := by linarith
        have hone :
            (1 - x) ^ (-(1 / 2 : ℝ)) ≤ (1 - x) ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hsubpos (sub_le_self 1 hxpos.le) (by norm_num)
        have hinv : (1 - x) ^ (-(1 : ℝ)) ≤ 2 := by
          rw [Real.rpow_neg_one, ← one_div]
          exact (one_div_le hsubpos (by norm_num)).2 hsubhalf
        dsimp [g]
        have hxrp := Real.rpow_nonneg hxpos.le (-(3 / 4 : ℝ))
        have hsrp := Real.rpow_nonneg hsubpos.le (-(1 / 2 : ℝ))
        nlinarith
      · have hxhalf : (1 / 2 : ℝ) ≤ x := le_of_not_ge hhalf
        have hone :
            x ^ (-(3 / 4 : ℝ)) ≤ x ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hxpos hx.2 (by norm_num)
        have hinv : x ^ (-(1 : ℝ)) ≤ 2 := by
          rw [Real.rpow_neg_one, ← one_div]
          exact (one_div_le hxpos (by norm_num)).2 hxhalf
        dsimp [g]
        have hxrp := Real.rpow_nonneg hxpos.le (-(3 / 4 : ℝ))
        have hsrp := Real.rpow_nonneg hsubpos.le (-(1 / 2 : ℝ))
        nlinarith
    exact hbase.trans hmajor
  calc
    _ ≤ ∫ x in (0 : ℝ)..1, ‖f x‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ x in (0 : ℝ)..1, g x :=
      intervalIntegral.integral_mono_on (by norm_num) hf.norm hg hpoint
    _ = 12 := by
      dsimp [g]
      rw [intervalIntegral.integral_add (hxpow.const_mul 2) (hsubpow.const_mul 2),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      have hsub :
          (∫ x in (0 : ℝ)..1, (1 - x) ^ (-(1 / 2 : ℝ))) =
            ∫ x in (0 : ℝ)..1, x ^ (-(1 / 2 : ℝ)) := by
        simpa using intervalIntegral.integral_comp_sub_left
          (a := (0 : ℝ)) (b := 1) (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) 1
      rw [hsub, integral_rpow (Or.inl (by norm_num)),
        integral_rpow (Or.inl (by norm_num))]
      norm_num

private lemma exists_norm_one_div_Gamma_Icc_le :
    ∃ K : ℝ, 0 < K ∧ ∀ d : ℝ, (1 / 2 : ℝ) ≤ d → d ≤ 11 →
      ‖(Complex.Gamma (d : ℂ))⁻¹‖ ≤ K := by
  have hcont : Continuous (fun d : ℝ => ‖(Complex.Gamma (d : ℂ))⁻¹‖) :=
    (Complex.differentiable_one_div_Gamma.continuous.comp
      Complex.continuous_ofReal).norm
  obtain ⟨c, hc⟩ := bddAbove_def.mp
    (IsCompact.bddAbove_image isCompact_Icc hcont.continuousOn)
  let K : ℝ := max c 0 + 1
  refine ⟨K, by dsimp [K]; linarith [le_max_right c 0], ?_⟩
  intro d hd hd11
  have hdmem : d ∈ Icc (1 / 2 : ℝ) 11 := ⟨hd, hd11⟩
  exact (hc _ (mem_image_of_mem _ hdmem)).trans
    (by dsimp [K]; linarith [le_max_left c 0])

private lemma norm_prod_range_eleven_add_le
    (w : ℂ) (t : ℝ)
    (hwlower : -(5 : ℝ) ≤ w.re) (hwupper : w.re ≤ (3 / 4 : ℝ))
    (hwim : |w.im| = |t| / 2) :
    ‖∏ j ∈ Finset.range 11, (w + j)‖ ≤
      (6 : ℝ) ^ 11 * (|t| + 2) ^ 11 := by
  have hfactor : ∀ j ∈ Finset.range 11,
      ‖w + (j : ℂ)‖ ≤ 6 * (|t| + 2) := by
    intro j hj
    have hjlt : j < 11 := Finset.mem_range.mp hj
    have hjle : j ≤ 10 := Nat.le_pred_of_lt hjlt
    have hjreal : (j : ℝ) ≤ 10 := by exact_mod_cast hjle
    have hjnonneg : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hreabs : |(w + (j : ℂ)).re| ≤ 43 / 4 := by
      rw [add_re, natCast_re]
      apply abs_le.mpr
      constructor <;> linarith
    have himabs : |(w + (j : ℂ)).im| = |t| / 2 := by
      simp only [add_im, natCast_im, add_zero, hwim]
    calc
      ‖w + (j : ℂ)‖ ≤ |(w + (j : ℂ)).re| + |(w + (j : ℂ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 43 / 4 + |t| / 2 := by rw [himabs]; gcongr
      _ ≤ 6 * (|t| + 2) := by nlinarith [abs_nonneg t]
  calc
    ‖∏ j ∈ Finset.range 11, (w + j)‖ ≤
        ∏ j ∈ Finset.range 11, ‖w + (j : ℂ)‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ _j ∈ Finset.range 11, (6 * (|t| + 2)) := by
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) hfactor
    _ = (6 * (|t| + 2)) ^ 11 := by simp
    _ = (6 : ℝ) ^ 11 * (|t| + 2) ^ 11 := by ring

private lemma norm_Gamma_div_Gamma_fixedStrip_le
    (K : ℝ)
    (hK : ∀ d : ℝ, (1 / 2 : ℝ) ≤ d → d ≤ 11 →
      ‖(Complex.Gamma (d : ℂ))⁻¹‖ ≤ K)
    (a : ℝ) (s : ℂ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hslo : -(10 : ℝ) ≤ s.re) (hshi : s.re ≤ (1 / 2 : ℝ)) :
    ‖Complex.Gamma ((1 - s + (a : ℂ)) / 2) /
        Complex.Gamma ((s + (a : ℂ)) / 2)‖ ≤
      (12 * K * 6 ^ 11) * (|s.im| + 2) ^ 11 := by
  let w : ℂ := ((starRingEnd ℂ) s + (a : ℂ)) / 2
  let X : ℂ := (1 - s + (a : ℂ)) / 2
  let d : ℝ := 21 / 2 + s.re
  have hwlower : -(5 : ℝ) ≤ w.re := by
    rw [show w.re = (s.re + a) / 2 by norm_num [w]]
    linarith
  have hwupper : w.re ≤ (3 / 4 : ℝ) := by
    rw [show w.re = (s.re + a) / 2 by norm_num [w]]
    linarith
  have hwim : |w.im| = |s.im| / 2 := by
    rw [show w.im = -s.im / 2 by norm_num [w], abs_div, abs_neg]
    norm_num
  have hX : (1 / 4 : ℝ) ≤ X.re := by
    rw [show X.re = (1 - s.re + a) / 2 by norm_num [X]]
    linarith
  have hdlo : (1 / 2 : ℝ) ≤ d := by dsimp [d]; linarith
  have hdhi : d ≤ 11 := by dsimp [d]; linarith
  have hsum : X + (d : ℂ) = w + 11 := by
    dsimp [X, d, w]
    apply Complex.ext
    · norm_num
      ring
    · norm_num
  have hidentity := Gamma_div_Gamma_eq_prod_mul_beta_div w X d
    (lt_of_lt_of_le (by norm_num) hX) (lt_of_lt_of_le (by norm_num) hdlo) hsum
  have hwconj : w = (starRingEnd ℂ) ((s + (a : ℂ)) / 2) := by
    dsimp [w]
    rw [map_div₀, map_add, map_ofNat]
    norm_num
  have hdennorm :
      ‖Complex.Gamma ((s + (a : ℂ)) / 2)‖ = ‖Complex.Gamma w‖ := by
    have h := congrArg norm (Complex.Gamma_conj ((s + (a : ℂ)) / 2))
    rw [Complex.norm_conj] at h
    rw [hwconj, h]
  have hquotnorm :
      ‖Complex.Gamma X / Complex.Gamma ((s + (a : ℂ)) / 2)‖ =
        ‖Complex.Gamma X / Complex.Gamma w‖ := by
    simp only [norm_div, hdennorm]
  have hprod := norm_prod_range_eleven_add_le w s.im hwlower hwupper hwim
  have hresidual :
      ‖Complex.betaIntegral X d / Complex.Gamma d‖ ≤ 12 * K := by
    rw [div_eq_mul_inv, norm_mul]
    exact mul_le_mul (norm_betaIntegral_fixed_re_le hX hdlo)
      (hK d hdlo hdhi) (norm_nonneg _) (by norm_num)
  rw [show (1 - s + (a : ℂ)) / 2 = X by rfl, hquotnorm, hidentity, norm_mul]
  calc
    _ ≤ ((6 : ℝ) ^ 11 * (|s.im| + 2) ^ 11) * (12 * K) :=
      mul_le_mul hprod hresidual (norm_nonneg _)
        (mul_nonneg (by positivity) (by positivity))
    _ = (12 * K * 6 ^ 11) * (|s.im| + 2) ^ 11 := by ring

private lemma norm_GammaR_div_GammaR_le_Gamma_div_Gamma
    (a : ℝ) (s : ℂ) (hs : s.re ≤ (1 / 2 : ℝ)) :
    ‖Complex.Gammaℝ (1 - s + (a : ℂ)) /
        Complex.Gammaℝ (s + (a : ℂ))‖ ≤
      ‖Complex.Gamma ((1 - s + (a : ℂ)) / 2) /
        Complex.Gamma ((s + (a : ℂ)) / 2)‖ := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def]
  have hfactor :
      ((Real.pi : ℂ) ^ (-(1 - s + (a : ℂ)) / 2) *
          Complex.Gamma ((1 - s + (a : ℂ)) / 2)) /
        ((Real.pi : ℂ) ^ (-(s + (a : ℂ)) / 2) *
          Complex.Gamma ((s + (a : ℂ)) / 2)) =
      (((Real.pi : ℂ) ^ (-(1 - s + (a : ℂ)) / 2)) /
          ((Real.pi : ℂ) ^ (-(s + (a : ℂ)) / 2))) *
        (Complex.Gamma ((1 - s + (a : ℂ)) / 2) /
          Complex.Gamma ((s + (a : ℂ)) / 2)) := by
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [hfactor, norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, ← Real.rpow_sub Real.pi_pos]
  have hexp :
      (-(1 - s + (a : ℂ)) / 2).re - (-(s + (a : ℂ)) / 2).re =
        s.re - 1 / 2 := by
    norm_num
    ring
  rw [hexp]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (le_trans (by norm_num) Real.two_le_pi) (by linarith)

private lemma even_inv_for_gammaFactor
    {q : ℕ} {chi : DirichletCharacter ℂ q} (hchi : chi.Even) :
    (chi⁻¹).Even := by
  simp only [DirichletCharacter.Even] at hchi ⊢
  rw [MulChar.inv_apply_eq_inv', hchi, inv_one]

private lemma odd_inv_for_gammaFactor
    {q : ℕ} {chi : DirichletCharacter ℂ q} (hchi : chi.Odd) :
    (chi⁻¹).Odd := by
  simp only [DirichletCharacter.Odd] at hchi ⊢
  rw [MulChar.inv_apply_eq_inv', hchi]
  norm_num

/-- The Dirichlet Gamma-factor quotient has absolute polynomial growth on
the fixed left strip used by the local zero-expansion argument.

The constant is uniform in the modulus and character. No nonzero hypothesis
is imposed on the denominator Gamma factor; this includes the parity-
dependent trivial-zero points under Lean's totalized division. -/
theorem exists_norm_gammaFactor_ratio_fixedStrip_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q) (s : ℂ),
        -(10 : ℝ) ≤ s.re →
        s.re ≤ (1 / 2 : ℝ) →
        ‖DirichletCharacter.gammaFactor chi⁻¹ (1 - s) /
          DirichletCharacter.gammaFactor chi s‖ ≤
          C * (|s.im| + 2) ^ 11 := by
  obtain ⟨K, hKpos, hK⟩ := exists_norm_one_div_Gamma_Icc_le
  let C : ℝ := 12 * K * 6 ^ 11
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro q _ chi s hslo hshi
  have hbound (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
      ‖Complex.Gammaℝ (1 - s + (a : ℂ)) /
          Complex.Gammaℝ (s + (a : ℂ))‖ ≤
        C * (|s.im| + 2) ^ 11 := by
    exact (norm_GammaR_div_GammaR_le_Gamma_div_Gamma a s hshi).trans
      (norm_Gamma_div_Gamma_fixedStrip_le K hK a s ha0 ha1 hslo hshi)
  rcases chi.even_or_odd with heven | hodd
  · rw [(even_inv_for_gammaFactor heven).gammaFactor_def, heven.gammaFactor_def]
    simpa using hbound 0 (by norm_num) (by norm_num)
  · rw [(odd_inv_for_gammaFactor hodd).gammaFactor_def, hodd.gammaFactor_def]
    convert hbound 1 (by norm_num) (by norm_num) using 1
    all_goals norm_num

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/PrimitiveGaussSum.lean` -/

section

/-!
# Primitive Gauss sums on `ZMod`

This file proves the finite Fourier and Gauss-sum prerequisites for
DavenportMNTCh23PV1980, printed pp. 135--136. In particular, the Gauss norm
proof works for composite moduli and does not use Mathlib's field-only Gauss
sum product theorem.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

open AddChar Finset

private theorem sum_star_mul_dft {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ k : ZMod q, star (ZMod.dft f k) * ZMod.dft f k) =
      (q : ℂ) * ∑ j : ZMod q, star (f j) * f j := by
  classical
  have hstar (x : ZMod q) :
      star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
    simpa only [Complex.star_def] using
      (AddChar.map_neg_eq_conj ZMod.stdAddChar x).symm
  simp only [ZMod.dft_apply, smul_eq_mul, star_sum, star_mul]
  simp_rw [hstar]
  simp only [neg_neg]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  have hsummand (i k : ZMod q) :
      star (f j) * ZMod.stdAddChar (j * k) *
          (ZMod.stdAddChar (-(i * k)) * f i) =
        (star (f j) * f i) * ZMod.stdAddChar (k * (j - i)) := by
    calc
      _ = (star (f j) * f i) *
          (ZMod.stdAddChar (j * k) * ZMod.stdAddChar (-(i * k))) := by ring
      _ = (star (f j) * f i) *
          ZMod.stdAddChar (j * k + -(i * k)) := by rw [map_add_eq_mul]
      _ = _ := by
        rw [show j * k + -(i * k) = k * (j - i) by ring]
  simp_rw [hsummand, ← Finset.mul_sum]
  simp_rw [AddChar.sum_mulShift (ψ := ZMod.stdAddChar) _
    (ZMod.isPrimitive_stdAddChar q)]
  simp only [sub_eq_zero, ZMod.card, Nat.cast_ite, Nat.cast_zero,
    mul_ite, mul_zero]
  simp [eq_comm]
  ring

/-- Parseval's identity for Mathlib's unnormalized complex DFT on `ZMod q`. -/
theorem sum_norm_sq_dft {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ k : ZMod q, ‖ZMod.dft f k‖ ^ 2) =
      (q : ℝ) * ∑ j : ZMod q, ‖f j‖ ^ 2 := by
  have h := sum_star_mul_dft f
  rw [Complex.star_def] at h
  simp_rw [← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

/-- The squared mass of a Dirichlet character is the number of unit residue
classes. -/
theorem sum_norm_sq_dirichletCharacter {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∑ j : ZMod q, ‖χ j‖ ^ 2) = (Nat.totient q : ℝ) := by
  classical
  calc
    (∑ j : ZMod q, ‖χ j‖ ^ 2) =
        ∑ j : ZMod q, if IsUnit j then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : IsUnit j
      · have hnorm : ‖χ j‖ = 1 := by
          rw [← hj.unit_spec]
          exact χ.unit_norm_eq_one hj.unit
        simp [hj, hnorm]
      · simp [hj, χ.map_nonunit hj]
    _ = (((Finset.univ : Finset (ZMod q)).filter IsUnit).card : ℝ) := by
      simp
    _ = ((Fintype.card (ZMod q)ˣ : ℕ) : ℝ) := by
      congr 1
      calc
        ((Finset.univ : Finset (ZMod q)).filter IsUnit).card =
            (Finset.univ.map ⟨((↑) : (ZMod q)ˣ → ZMod q),
              Units.val_injective⟩).card := by
          congr 1
          ext j
          simp [IsUnit]
        _ = Fintype.card (ZMod q)ˣ := by simp
    _ = (Nat.totient q : ℝ) := by rw [ZMod.card_units_eq_totient]

/-- A primitive Dirichlet character modulo any positive, possibly composite,
modulus has standard Gauss-sum norm `sqrt q`. -/
theorem norm_gaussSum_stdAddChar_of_isPrimitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt q := by
  have hmassNeg :
      (∑ k : ZMod q, ‖χ⁻¹ (-k)‖ ^ 2) = (Nat.totient q : ℝ) := by
    calc
      _ = ∑ k : ZMod q, ‖χ⁻¹ k‖ ^ 2 :=
        Equiv.sum_comp (Equiv.neg (ZMod q)) (fun k ↦ ‖χ⁻¹ k‖ ^ 2)
      _ = (Nat.totient q : ℝ) := sum_norm_sq_dirichletCharacter χ⁻¹
  have hparseval := sum_norm_sq_dft (f := fun j ↦ χ j)
  simp_rw [hχ.fourierTransform_eq_inv_mul_gaussSum, norm_mul, mul_pow] at hparseval
  rw [← Finset.sum_mul, hmassNeg,
    sum_norm_sq_dirichletCharacter χ] at hparseval
  have htotient : (Nat.totient q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr
      (Nat.pos_of_ne_zero (NeZero.ne q))))
  have hsquare : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (q : ℝ) := by
    apply mul_left_cancel₀ htotient
    calc
      (Nat.totient q : ℝ) * ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 =
          (q : ℝ) * Nat.totient q := hparseval
      _ = (Nat.totient q : ℝ) * q := by ring
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg q),
    norm_nonneg (gaussSum χ ZMod.stdAddChar), Real.sqrt_nonneg (q : ℝ)]

/-- Davenport's primitive Fourier expansion in Mathlib's negative-kernel DFT
normalization. -/
theorem primitive_fourier_expansion {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (n : ZMod q) :
    (∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (a * n)) =
      χ n * gaussSum χ⁻¹ ZMod.stdAddChar := by
  have hχinv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hχ
  have hfourier := hχinv.fourierTransform_eq_inv_mul_gaussSum (-n)
  simpa only [ZMod.dft_apply, smul_eq_mul, mul_neg, neg_neg, inv_inv,
    mul_comm] using hfourier

/-- Davenport's primitive Fourier expansion after division by the proved
nonzero Gauss sum. -/
theorem primitive_fourier_expansion_div {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (n : ZMod q) :
    χ n = (∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (a * n)) /
      gaussSum χ⁻¹ ZMod.stdAddChar := by
  have hχinv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hχ
  have hnorm := norm_gaussSum_stdAddChar_of_isPrimitive χ⁻¹ hχinv
  have hgauss : gaussSum χ⁻¹ ZMod.stdAddChar ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hnorm
    have hqpos : (0 : ℝ) < q := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    nlinarith [Real.sqrt_pos.2 hqpos]
  rw [primitive_fourier_expansion χ hχ n,
    mul_div_cancel_right₀ _ hgauss]

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/PrimitiveFunctionalEquation.lean` -/

section

/-!
# Primitive Dirichlet functional equation

This file rewrites Mathlib's completed primitive functional equation as an
exact identity for the ordinary Dirichlet `LFunction` on `Re s <= 1/2`.
The source normalization is Koukoulopoulos, printed p. 111, equation (11.3)
and Theorem 11.1; see semantic review SEM-475.
-/

namespace BoundedGaps.Maynard

open Complex

private lemma gammaFactor_inv_one_sub_ne_zero
    {q : ℕ} (chi : DirichletCharacter ℂ q) {s : ℂ}
    (hs : s.re ≤ (1 / 2 : ℝ)) :
    DirichletCharacter.gammaFactor chi⁻¹ (1 - s) ≠ 0 := by
  rcases chi⁻¹.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  · rw [hodd.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

/-- A primitive Dirichlet root number has unit complex norm.

This is the norm-one observation immediately before Koukoulopoulos, printed
p. 111, Theorem 11.1, using the primitive Gauss-sum norm from printed p. 105,
Theorem 10.4. -/
theorem norm_rootNumber_of_isPrimitive
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive) :
    ‖DirichletCharacter.rootNumber chi‖ = 1 := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
  rw [DirichletCharacter.rootNumber, norm_div, norm_div,
    norm_gaussSum_stdAddChar_of_isPrimitive chi hchi, norm_pow,
    Complex.norm_I, one_pow, div_one,
    Complex.norm_natCast_cpow_of_pos hqpos]
  simp [Real.sqrt_eq_rpow, hq0]

/-- The primitive functional equation rewritten for the ordinary L-function
on the closed half-plane `Re(s) <= 1/2`.

The denominator Gamma factor is deliberately allowed to vanish at a trivial
zero. The real-part hypothesis is used only to show that the reflected Gamma
factor is nonzero. -/
theorem LFunction_eq_functionalEquation_of_isPrimitive
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (s : ℂ) (hs : s.re ≤ (1 / 2 : ℝ)) :
    DirichletCharacter.LFunction chi s =
      (q : ℂ) ^ ((1 / 2 : ℂ) - s) *
        DirichletCharacter.rootNumber chi *
        DirichletCharacter.LFunction chi⁻¹ (1 - s) *
        (DirichletCharacter.gammaFactor chi⁻¹ (1 - s) /
          DirichletCharacter.gammaFactor chi s) := by
  have hqne : q ≠ 1 := Nat.ne_of_gt hq
  have hcompleted :
      DirichletCharacter.completedLFunction chi s =
        (q : ℂ) ^ ((1 / 2 : ℂ) - s) *
          DirichletCharacter.rootNumber chi *
          DirichletCharacter.completedLFunction chi⁻¹ (1 - s) := by
    convert hchi.completedLFunction_one_sub (1 - s) using 1 <;> ring_nf
  have hgamma := gammaFactor_inv_one_sub_ne_zero chi hs
  have hreflected :
      DirichletCharacter.completedLFunction chi⁻¹ (1 - s) =
        DirichletCharacter.LFunction chi⁻¹ (1 - s) *
          DirichletCharacter.gammaFactor chi⁻¹ (1 - s) := by
    symm
    exact (eq_div_iff hgamma).mp
      (DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi⁻¹
        (1 - s) (.inr hqne))
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi s (.inr hqne),
    hcompleted, hreflected]
  ring

/-- The exact norm factorization obtained from the primitive functional
equation and the unit norm of its root number. -/
theorem norm_LFunction_eq_functionalEquation_of_isPrimitive
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (s : ℂ) (hs : s.re ≤ (1 / 2 : ℝ)) :
    ‖DirichletCharacter.LFunction chi s‖ =
      (q : ℝ) ^ ((1 : ℝ) / 2 - s.re) *
        ‖DirichletCharacter.LFunction chi⁻¹ (1 - s)‖ *
        ‖DirichletCharacter.gammaFactor chi⁻¹ (1 - s) /
          DirichletCharacter.gammaFactor chi s‖ := by
  rw [LFunction_eq_functionalEquation_of_isPrimitive hq chi hchi s hs,
    norm_mul, norm_mul, norm_mul, norm_rootNumber_of_isPrimitive chi hchi,
    Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hq)]
  norm_num

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/DirichletLFunctionAbelContinuation.lean` -/

section

/-!
# Abel continuation for nonprincipal Dirichlet L-functions

This Mathlib-only module continues the Abel integral of a Dirichlet character
from the half-plane of absolute convergence to `0 < re s`, assuming a uniform
bound on its natural partial sums. The project-facing specializations are
reviewed in `SEM-474` and `SEM-544`.
-/

open Asymptotics Complex Filter MeasureTheory Set
open scoped BigOperators Real Topology

namespace BoundedGaps.Maynard

private noncomputable def characterPrefixTail
    {q : ℕ} (chi : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator
    (fun u ↦ ∑ k ∈ Finset.Icc 1 ⌊u⌋₊, chi (k : ZMod q)) y

private lemma measurable_characterPrefixTail
    {q : ℕ} (chi : DirichletCharacter ℂ q) :
    Measurable (characterPrefixTail chi) := by
  apply Measurable.indicator _ measurableSet_Ioi
  exact
    (measurable_of_countable
      (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q))).comp
      Nat.measurable_floor

private lemma norm_characterPrefixTail_le
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    (y : ℝ) :
    ‖characterPrefixTail chi y‖ ≤ C := by
  by_cases hy : y ∈ Ioi (1 : ℝ)
  · rw [characterPrefixTail, indicator_of_mem hy]
    exact hprefix ⌊y⌋₊
  · rw [characterPrefixTail, indicator_of_notMem hy, norm_zero]
    exact hC

private lemma locallyIntegrable_characterPrefixTail
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C) :
    LocallyIntegrableOn (characterPrefixTail chi) (Ioi 0) := by
  have hnormScale : ‖((C : ℝ) : ℂ)‖ = C := by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
  refine ((locallyIntegrable_const ((C : ℝ) : ℂ)).locallyIntegrableOn
      (Ioi 0)).mono
      (measurable_characterPrefixTail chi).aestronglyMeasurable ?_
  filter_upwards with y
  rw [hnormScale]
  exact norm_characterPrefixTail_le chi C hC hprefix y

private lemma characterPrefixTail_isBigO_atTop
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C) :
    characterPrefixTail chi =O[atTop] (fun y : ℝ ↦ y ^ (-(0 : ℝ))) := by
  refine isBigO_iff.mpr ⟨C, Eventually.of_forall fun y ↦ ?_⟩
  simpa using norm_characterPrefixTail_le chi C hC hprefix y

private lemma characterPrefixTail_isBigO_nhdsGT_zero
    {q : ℕ} (chi : DirichletCharacter ℂ q) (b : ℝ) :
    characterPrefixTail chi =O[𝓝[>] 0] (fun y : ℝ ↦ y ^ (-b)) := by
  have hlt : ∀ᶠ y : ℝ in 𝓝[>] 0, y < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [hlt] with y hy
  simp [characterPrefixTail, not_lt.mpr hy.le]

private lemma differentiableAt_characterPrefixMellin_neg
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun w ↦ mellin (characterPrefixTail chi) (-w)) s := by
  have hm : DifferentiableAt ℂ (mellin (characterPrefixTail chi)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow
      (a := 0) (b := (-s).re - 1)
      (locallyIntegrable_characterPrefixTail chi C hC hprefix)
      (characterPrefixTail_isBigO_atTop chi C hC hprefix) ?_
      (characterPrefixTail_isBigO_nhdsGT_zero chi ((-s).re - 1)) ?_
    · simpa using (neg_lt_zero.mpr hs)
    · linarith
  exact hm.comp s differentiableAt_id.neg

private lemma characterPrefixMellin_neg_eq_integral
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (characterPrefixTail chi) (-s) =
      ∫ y in Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) := by
  rw [mellin]
  simp only [smul_eq_mul]
  calc
    (∫ y : ℝ in Ioi 0,
        (y : ℂ) ^ (-s - 1) * characterPrefixTail chi y) =
        ∫ y : ℝ in Ioi 0, (Ioi (1 : ℝ)).indicator
          (fun u ↦ (u : ℂ) ^ (-s - 1) *
            ∑ k ∈ Finset.Icc 1 ⌊u⌋₊, chi (k : ZMod q)) y := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
      by_cases hy : y ∈ Ioi (1 : ℝ)
      · simp [characterPrefixTail, hy]
      · simp [characterPrefixTail, hy]
    _ = ∫ y : ℝ in Ioi 0 ∩ Ioi 1,
        (y : ℂ) ^ (-s - 1) *
          (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) := by
      rw [setIntegral_indicator measurableSet_Ioi]
    _ = ∫ y : ℝ in Ioi 1,
        (y : ℂ) ^ (-s - 1) *
          (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) := by
      rw [Ioi_inter_Ioi, max_eq_right zero_le_one]
    _ = ∫ y : ℝ in Ioi 1,
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]

private lemma characterPartialSums_isBigO_atTop
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (0 : ℝ)) := by
  refine isBigO_iff.mpr ⟨C, Eventually.of_forall fun n ↦ ?_⟩
  simpa using hprefix n

private lemma LFunction_eq_characterPrefixMellin_of_one_lt_re
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * mellin (characterPrefixTail chi) (-s) := by
  calc
    DirichletCharacter.LFunction chi s = LSeries (chi ·) s :=
      DirichletCharacter.LFunction_eq_LSeries chi hs
    _ = s * ∫ y in Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) :=
      LSeries_eq_mul_integral (chi ·) (r := 0) le_rfl (zero_lt_one.trans hs)
        (DirichletCharacter.LSeriesSummable_of_one_lt_re chi hs)
        (characterPartialSums_isBigO_atTop chi C hprefix)
    _ = s * mellin (characterPrefixTail chi) (-s) := by
      rw [characterPrefixMellin_neg_eq_integral]

/-- A bounded natural character prefix gives the Abel integral representation
throughout the positive half-plane. The proof establishes the integral's
convergence before applying analytic uniqueness. -/
theorem LFunction_eq_abelIntegral_of_prefixBound
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    (s : ℂ) (hs : 0 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * ∫ y in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) := by
  have hC : 0 ≤ C := by
    simpa using hprefix 0
  let U : Set ℂ := {w | 0 < w.re}
  have hUOpen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUPre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hLeft :
      AnalyticOnNhd ℂ (DirichletCharacter.LFunction chi) U :=
    (DirichletCharacter.differentiable_LFunction hchi).differentiableOn.analyticOnNhd hUOpen
  have hRight : AnalyticOnNhd ℂ
      (fun w ↦ w * mellin (characterPrefixTail chi) (-w)) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw ↦ ?_) hUOpen
    exact (differentiableAt_id.mul
      (differentiableAt_characterPrefixMellin_neg chi C hC hprefix hw)).differentiableWithinAt
  have hEq : EqOn (DirichletCharacter.LFunction chi)
      (fun w ↦ w * mellin (characterPrefixTail chi) (-w)) U := by
    refine hLeft.eqOn_of_preconnected_of_eventuallyEq hRight hUPre
      (show (2 : ℂ) ∈ U by simp [U]) ?_
    refine eventually_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show 1 < (2 : ℂ).re by norm_num)) ?_
    intro w hw
    exact LFunction_eq_characterPrefixMellin_of_one_lt_re chi C hprefix hw
  rw [hEq hs]
  change s * mellin (characterPrefixTail chi) (-s) = _
  rw [characterPrefixMellin_neg_eq_integral]

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/StandardAddCharInterval.lean` -/

section

/-!
# Standard additive characters on translated integer intervals

This file proves the geometric-series and reciprocal-sine steps in
DavenportMNTCh23PV1980, printed p. 136. The sharp sum over all nonzero
frequencies remains a separate theorem.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

open AddChar Finset

private theorem sum_Ioc_int_eq_sum_range_add_succ
    {A : Type*} [AddCommMonoid A] (f : ℤ → A) (M : ℤ) (N : ℕ) :
    (∑ m ∈ Finset.Ioc M (M + (N : ℤ)), f m) =
      ∑ n ∈ Finset.range N, f (M + (n + 1 : ℕ)) := by
  rw [Int.Ioc_eq_finset_map, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]
  congr 1
  · simp
  · funext n
    congr 1
    push_cast
    ring

private theorem stdAddChar_mul_int_add_succ {q : ℕ} [NeZero q]
    (a : ZMod q) (M : ℤ) (n : ℕ) :
    ZMod.stdAddChar (a * ((M + ((n + 1 : ℕ) : ℤ) : ℤ) : ZMod q)) =
      ZMod.stdAddChar (a * ((M + 1 : ℤ) : ZMod q)) *
        ZMod.stdAddChar a ^ n := by
  rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_add_eq_mul]
  congr 1
  push_cast
  simp only [nsmul_eq_mul]
  ring

private theorem stdAddChar_ne_one_of_ne_zero
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : a ≠ 0) :
    ZMod.stdAddChar a ≠ 1 := by
  intro h
  apply ha
  apply ZMod.injective_stdAddChar
  simpa only [AddChar.map_zero_eq_one] using h

private theorem norm_stdAddChar_sub_one_eq_two_mul_abs_sin
    {q : ℕ} [NeZero q] (a : ZMod q) :
    ‖ZMod.stdAddChar a - 1‖ =
      2 * |Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ))| := by
  rw [← ZMod.natCast_zmod_val a]
  rw [show (a.val : ZMod q) = ((a.val : ℤ) : ZMod q) by simp,
    ZMod.stdAddChar_coe]
  simp only [Int.cast_natCast]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) / (q : ℂ) =
      Complex.I * ((2 * Real.pi * (a.val : ℝ) / (q : ℝ) : ℝ) : ℂ) by
        push_cast
        ring]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  simp only [show (2 * Real.pi * (a.val : ℝ) / (q : ℝ)) / 2 =
    Real.pi * (a.val : ℝ) / (q : ℝ) by ring]
  rw [Real.norm_eq_abs, abs_mul]
  norm_num

/-- The standard additive character on `M < n ≤ M + N` is a translated
finite geometric progression. -/
theorem sum_stdAddChar_Ioc_eq_geometric
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : a ≠ 0)
    (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
      ZMod.stdAddChar (a * (n : ZMod q))) =
      ZMod.stdAddChar (a * ((M + 1 : ℤ) : ZMod q)) *
        ((1 - ZMod.stdAddChar (a * (N : ZMod q))) /
          (1 - ZMod.stdAddChar a)) := by
  rw [sum_Ioc_int_eq_sum_range_add_succ]
  simp_rw [stdAddChar_mul_int_add_succ]
  rw [← Finset.mul_sum, geom_sum_eq (stdAddChar_ne_one_of_ne_zero ha)]
  have hpow : ZMod.stdAddChar (a * (N : ZMod q)) =
      ZMod.stdAddChar a ^ N := by
    rw [show a * (N : ZMod q) = N • a by ring,
      AddChar.map_nsmul_eq_pow]
  rw [hpow]
  congr 1
  rw [div_eq_mul_inv, div_eq_mul_inv,
    show ZMod.stdAddChar a - 1 = -(1 - ZMod.stdAddChar a) by ring,
    inv_neg]
  ring

/-- A nonzero standard additive frequency has the reciprocal-sine interval
bound used in the proof of Pólya--Vinogradov. -/
theorem norm_sum_stdAddChar_Ioc_le_inv_sin
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : a ≠ 0)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
      ZMod.stdAddChar (a * (n : ZMod q))‖ ≤
      (Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)))⁻¹ := by
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have havalpos : (0 : ℝ) < a.val := by
    exact_mod_cast Nat.pos_of_ne_zero ((ZMod.val_ne_zero a).mpr ha)
  have hanglepos : 0 < Real.pi * (a.val : ℝ) / (q : ℝ) :=
    div_pos (mul_pos Real.pi_pos havalpos) hqpos
  have hanglelt : Real.pi * (a.val : ℝ) / (q : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hqpos]
    have havallt : (a.val : ℝ) < q := by exact_mod_cast a.val_lt
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi hanglepos hanglelt
  have hnum : ‖1 - ZMod.stdAddChar (a * (N : ZMod q))‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖ZMod.stdAddChar (a * (N : ZMod q))‖ :=
        norm_sub_le _ _
      _ = 2 := by rw [AddChar.norm_apply]; norm_num
  have hdenom : ‖1 - ZMod.stdAddChar a‖ =
      2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)) := by
    rw [show (1 : ℂ) - ZMod.stdAddChar a =
      -(ZMod.stdAddChar a - 1) by ring, norm_neg,
      norm_stdAddChar_sub_one_eq_two_mul_abs_sin,
      abs_of_pos hsin]
  rw [sum_stdAddChar_Ioc_eq_geometric ha, norm_mul,
    AddChar.norm_apply, one_mul, norm_div, hdenom]
  calc
    ‖1 - ZMod.stdAddChar (a * (N : ZMod q))‖ /
        (2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ))) ≤
        2 / (2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ))) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)))⁻¹ := by
      field_simp

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/PrimitiveCharacterInterval.lean` -/

section

/-!
# Primitive character sums on translated integer intervals

This file composes the audited primitive Fourier expansion with the translated
standard-character interval estimate. The sharp reciprocal-sine aggregate is
left to a later owner.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

open AddChar Finset

private theorem sum_zmod_erase_zero_eq_sum_Ico_val
    {q : ℕ} [NeZero q]
    {A : Type*} [AddCommMonoid A] (f : ZMod q → A) :
    (∑ a ∈ Finset.univ.erase (0 : ZMod q), f a) =
      ∑ a ∈ Finset.Ico 1 q, f (a : ZMod q) := by
  classical
  apply Finset.sum_nbij (fun a : ZMod q => a.val)
  · intro a ha
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
    exact Finset.mem_Ico.mpr ⟨ZMod.val_pos.mpr ha0, a.val_lt⟩
  · exact (ZMod.val_injective q).injOn
  · intro b hb
    have hbmem := Finset.mem_Ico.mp hb
    refine ⟨(b : ZMod q), ?_, ?_⟩
    · apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      apply (ZMod.val_ne_zero _).mp
      rw [ZMod.val_cast_of_lt hbmem.2]
      exact Nat.ne_of_gt hbmem.1
    · exact ZMod.val_cast_of_lt hbmem.2
  · intro a ha
    rw [ZMod.natCast_zmod_val]

/-- Summing the primitive Fourier expansion over a translated integer interval
and commuting the two finite sums. -/
theorem sum_dirichletCharacter_Ioc_eq_fourier
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi.IsPrimitive) (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
      (∑ a : ZMod q, chi⁻¹ a *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar (a * (n : ZMod q))) /
        gaussSum chi⁻¹ ZMod.stdAddChar := by
  classical
  have hpoint (n : ℤ) :
      chi (n : ZMod q) =
        (∑ a : ZMod q,
          chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
    exact primitive_fourier_expansion_div chi hchi (n : ZMod q)
  calc
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ((∑ a : ZMod q,
            chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
            gaussSum chi⁻¹ ZMod.stdAddChar) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hpoint n
    _ = (∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ∑ a : ZMod q,
            chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      rw [Finset.sum_div]
    _ = (∑ a : ZMod q, ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      rw [Finset.sum_comm]
    _ = (∑ a : ZMod q, chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.mul_sum]

/-- At modulus greater than one, the zero Fourier frequency has zero character
coefficient and may be erased exactly. -/
theorem sum_dirichletCharacter_Ioc_eq_fourier_erase_zero
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
      (∑ a ∈ Finset.univ.erase (0 : ZMod q), chi⁻¹ a *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar (a * (n : ZMod q))) /
        gaussSum chi⁻¹ ZMod.stdAddChar := by
  classical
  have hzero : chi⁻¹ (0 : ZMod q) = 0 :=
    DirichletCharacter.map_zero' chi⁻¹ (Nat.ne_of_gt hq)
  calc
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
        (∑ a : ZMod q, chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar :=
      sum_dirichletCharacter_Ioc_eq_fourier chi hchi M N
    _ = (∑ a ∈ Finset.univ.erase (0 : ZMod q), chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod q))]
      simp [hzero]

/-- The erased nonzero Fourier frequencies, written as their canonical natural
representatives `1 ≤ a < q`. -/
theorem sum_dirichletCharacter_Ioc_eq_nat_fourier
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
      (∑ a ∈ Finset.Ico 1 q, chi⁻¹ (a : ZMod q) *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))) /
        gaussSum chi⁻¹ ZMod.stdAddChar := by
  classical
  calc
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
        (∑ a ∈ Finset.univ.erase (0 : ZMod q), chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar :=
      sum_dirichletCharacter_Ioc_eq_fourier_erase_zero hq chi hchi M N
    _ = (∑ a ∈ Finset.Ico 1 q, chi⁻¹ (a : ZMod q) *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      exact sum_zmod_erase_zero_eq_sum_Ico_val
        (f := fun a : ZMod q => chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q)))

/-- Davenport's primitive-character interval envelope before the sharp
reciprocal-sine aggregate. -/
theorem norm_sum_dirichletCharacter_Ioc_le_reciprocalSineSum
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)‖ ≤
      (∑ a ∈ Finset.Ico 1 q,
        (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹) /
        Real.sqrt q := by
  classical
  have hchiInv : chi⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hchi
  have hgaussNorm : ‖gaussSum chi⁻¹ ZMod.stdAddChar‖ = Real.sqrt q :=
    norm_gaussSum_stdAddChar_of_isPrimitive chi⁻¹ hchiInv
  have hnumerator :
      ‖∑ a ∈ Finset.Ico 1 q, chi⁻¹ (a : ZMod q) *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ ≤
        ∑ a ∈ Finset.Ico 1 q,
          (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := by
    calc
      _ ≤ ∑ a ∈ Finset.Ico 1 q,
          ‖chi⁻¹ (a : ZMod q) *
            ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
              ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ a ∈ Finset.Ico 1 q,
          (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := by
        apply Finset.sum_le_sum
        intro a ha
        have haIco := Finset.mem_Ico.mp ha
        have ha0 : (a : ZMod q) ≠ 0 := by
          apply (ZMod.val_ne_zero (a : ZMod q)).mp
          rw [ZMod.val_cast_of_lt haIco.2]
          exact Nat.ne_of_gt haIco.1
        have hinterval := norm_sum_stdAddChar_Ioc_le_inv_sin
          (q := q) (a := (a : ZMod q)) ha0 M N
        rw [ZMod.val_cast_of_lt haIco.2] at hinterval
        calc
          ‖chi⁻¹ (a : ZMod q) *
              ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
                ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ =
              ‖chi⁻¹ (a : ZMod q)‖ *
                ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
                  ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ :=
            norm_mul _ _
          _ ≤ 1 * (Real.sin
                (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ :=
            mul_le_mul (DirichletCharacter.norm_le_one chi⁻¹ (a : ZMod q))
              hinterval (norm_nonneg _) zero_le_one
          _ = (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := one_mul _
  rw [sum_dirichletCharacter_Ioc_eq_nat_fourier hq chi hchi M N,
    norm_div, hgaussNorm]
  exact div_le_div_of_nonneg_right hnumerator (Real.sqrt_nonneg q)

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/ReciprocalSineAggregate.lean` -/

section

/-!
# The sharp reciprocal-sine aggregate

This file proves the finite reciprocal-sine estimate used in DavenportMNTCh23PV1980,
printed p. 136. Sine symmetry and Jordan's inequality reduce the estimate to
sharp elementary bounds for harmonic numbers.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

open Finset

private theorem harmonic_cast_le_log_two_mul_add_one (n : ℕ) :
    (harmonic n : ℝ) ≤ Real.log (2 * (n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [harmonic_succ]
      simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_succ]
      have hden : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
      have hlog := Real.le_log_one_add_of_nonneg
        (show (0 : ℝ) ≤ 2 / (2 * (n : ℝ) + 1) by positivity)
      have hincrement :
          ((n : ℝ) + 1)⁻¹ ≤
            Real.log (2 * ((n : ℝ) + 1) + 1) -
              Real.log (2 * (n : ℝ) + 1) := by
        rw [← Real.log_div (by positivity) hden.ne']
        convert hlog using 1 <;> field_simp <;> ring_nf
      linarith

private theorem harmonic_cast_lt_log_two_mul_add_one {n : ℕ} (hn : 0 < n) :
    (harmonic n : ℝ) < Real.log (2 * (n : ℝ) + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [harmonic_succ]
  simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_succ]
  have hbase := harmonic_cast_le_log_two_mul_add_one n
  have hden : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hlog := Real.lt_log_one_add_of_pos
    (show (0 : ℝ) < 2 / (2 * (n : ℝ) + 1) by positivity)
  have hincrement :
      ((n : ℝ) + 1)⁻¹ <
        Real.log (2 * ((n : ℝ) + 1) + 1) -
          Real.log (2 * (n : ℝ) + 1) := by
    rw [← Real.log_div (by positivity) hden.ne']
    convert hlog using 1 <;> field_simp <;> ring_nf
  linarith

private theorem harmonic_cast_pred_add_inv_two_mul_lt_log_two_mul
    {m : ℕ} (hm : 0 < m) :
    (harmonic (m - 1) : ℝ) + (((2 * m : ℕ) : ℝ))⁻¹ <
      Real.log (((2 * m : ℕ) : ℝ)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp only [Nat.succ_sub_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ]
  have hbase := harmonic_cast_le_log_two_mul_add_one m
  have hden : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hx : (0 : ℝ) < (2 * (m : ℝ) + 1)⁻¹ := by positivity
  have hlog := Real.lt_log_one_add_of_pos hx
  have hincrement :
      (2 * ((m : ℝ) + 1))⁻¹ <
        Real.log (2 * ((m : ℝ) + 1)) -
          Real.log (2 * (m : ℝ) + 1) := by
    rw [← Real.log_div (by positivity) hden.ne']
    calc
      (2 * ((m : ℝ) + 1))⁻¹ <
          2 * (2 * (m : ℝ) + 1)⁻¹ /
            ((2 * (m : ℝ) + 1)⁻¹ + 2) := by
        field_simp
        linarith
      _ < Real.log (1 + (2 * (m : ℝ) + 1)⁻¹) := hlog
      _ = Real.log (2 * ((m : ℝ) + 1) / (2 * (m : ℝ) + 1)) := by
        congr 1
        field_simp
        ring
  linarith

private noncomputable def reciprocalSineTerm (q a : ℕ) : ℝ :=
  (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹

private theorem reciprocalSineTerm_le_div {q a : ℕ} (hq : 0 < q)
    (ha : 0 < a) (haq : 2 * a ≤ q) :
    reciprocalSineTerm q a ≤ (q : ℝ) / (2 * (a : ℝ)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hangle0 : 0 ≤ Real.pi * (a : ℝ) / (q : ℝ) := by positivity
  have hanglehalf : Real.pi * (a : ℝ) / (q : ℝ) ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ hqR zero_lt_two]
    have haqR : (2 : ℝ) * (a : ℝ) ≤ q := by exact_mod_cast haq
    nlinarith [Real.pi_pos]
  have hjordan := Real.mul_le_sin hangle0 hanglehalf
  have hbase : 0 < 2 / Real.pi *
      (Real.pi * (a : ℝ) / (q : ℝ)) := by positivity
  have hinv := inv_anti₀ hbase hjordan
  calc
    reciprocalSineTerm q a =
        (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := rfl
    _ ≤ (2 / Real.pi * (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := hinv
    _ = (q : ℝ) / (2 * (a : ℝ)) := by field_simp

private theorem reciprocalSineTerm_sub {q a : ℕ} (hq : 0 < q) (ha : a ≤ q) :
    reciprocalSineTerm q (q - a) = reciprocalSineTerm q a := by
  rw [reciprocalSineTerm, reciprocalSineTerm, Nat.cast_sub ha]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [show Real.pi * ((q : ℝ) - (a : ℝ)) / (q : ℝ) =
      Real.pi - Real.pi * (a : ℝ) / (q : ℝ) by field_simp,
    Real.sin_pi_sub]

private theorem reciprocalSineTerm_two_mul_self {m : ℕ} (hm : 0 < m) :
    reciprocalSineTerm (2 * m) m = 1 := by
  rw [reciprocalSineTerm]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [show Real.pi * (m : ℝ) / ((2 * m : ℕ) : ℝ) = Real.pi / 2 by
      push_cast
      field_simp,
    Real.sin_pi_div_two, inv_one]

private theorem sum_Ico_inv_eq_harmonic (n : ℕ) :
    (∑ a ∈ Finset.Ico 1 (n + 1), ((a : ℝ))⁻¹) = (harmonic n : ℝ) := by
  rw [Finset.Ico_add_one_right_eq_Icc]
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

private theorem sum_reciprocalSine_Ico_le_half_mul_harmonic
    {q m : ℕ} (hq : 0 < q) (hmq : 2 * m ≤ q) :
    (∑ a ∈ Finset.Ico 1 (m + 1), reciprocalSineTerm q a) ≤
      (q : ℝ) / 2 * (harmonic m : ℝ) := by
  calc
    (∑ a ∈ Finset.Ico 1 (m + 1), reciprocalSineTerm q a) ≤
        ∑ a ∈ Finset.Ico 1 (m + 1), (q : ℝ) / (2 * (a : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact reciprocalSineTerm_le_div hq (Finset.mem_Ico.mp ha).1
        ((Nat.mul_le_mul_left 2
          (Nat.le_of_lt_succ (Finset.mem_Ico.mp ha).2)).trans hmq)
    _ = (q : ℝ) / 2 *
        ∑ a ∈ Finset.Ico 1 (m + 1), ((a : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      field_simp
    _ = (q : ℝ) / 2 * (harmonic m : ℝ) := by
      rw [sum_Ico_inv_eq_harmonic]

private theorem sum_reciprocalSine_odd_eq_two_mul (m : ℕ) :
    (∑ a ∈ Finset.Ico 1 (2 * m + 1), reciprocalSineTerm (2 * m + 1) a) =
      2 * ∑ a ∈ Finset.Ico 1 (m + 1), reciprocalSineTerm (2 * m + 1) a := by
  have hq : 0 < 2 * m + 1 := by omega
  have hreflect := Finset.sum_Ico_reflect
    (reciprocalSineTerm (2 * m + 1)) 1
    (m := m + 1) (n := 2 * m + 1) (by omega)
  have hb1 : 2 * m + 1 + 1 - (m + 1) = m + 1 := by omega
  have hb2 : 2 * m + 1 + 1 - 1 = 2 * m + 1 := by omega
  rw [hb1, hb2] at hreflect
  have hupper :
      (∑ a ∈ Finset.Ico (m + 1) (2 * m + 1),
        reciprocalSineTerm (2 * m + 1) a) =
        ∑ a ∈ Finset.Ico 1 (m + 1), reciprocalSineTerm (2 * m + 1) a := by
    rw [← hreflect]
    apply Finset.sum_congr rfl
    intro a ha
    apply reciprocalSineTerm_sub hq
    exact (Nat.le_of_lt_succ (Finset.mem_Ico.mp ha).2).trans (by omega)
  calc
    (∑ a ∈ Finset.Ico 1 (2 * m + 1), reciprocalSineTerm (2 * m + 1) a) =
        (∑ a ∈ Finset.Ico 1 (m + 1), reciprocalSineTerm (2 * m + 1) a) +
          ∑ a ∈ Finset.Ico (m + 1) (2 * m + 1),
            reciprocalSineTerm (2 * m + 1) a := by
      rw [Finset.sum_Ico_consecutive (reciprocalSineTerm (2 * m + 1))
        (by omega) (by omega)]
    _ = 2 * ∑ a ∈ Finset.Ico 1 (m + 1),
        reciprocalSineTerm (2 * m + 1) a := by rw [hupper]; ring

private theorem sum_reciprocalSine_even_eq_two_mul_add_one
    {m : ℕ} (hm : 0 < m) :
    (∑ a ∈ Finset.Ico 1 (2 * m), reciprocalSineTerm (2 * m) a) =
      2 * (∑ a ∈ Finset.Ico 1 m, reciprocalSineTerm (2 * m) a) + 1 := by
  have hq : 0 < 2 * m := Nat.mul_pos two_pos hm
  have hreflect := Finset.sum_Ico_reflect
    (reciprocalSineTerm (2 * m)) 1
    (m := m) (n := 2 * m) (by omega)
  have hb1 : 2 * m + 1 - m = m + 1 := by omega
  have hb2 : 2 * m + 1 - 1 = 2 * m := by omega
  rw [hb1, hb2] at hreflect
  have hupper :
      (∑ a ∈ Finset.Ico (m + 1) (2 * m), reciprocalSineTerm (2 * m) a) =
        ∑ a ∈ Finset.Ico 1 m, reciprocalSineTerm (2 * m) a := by
    rw [← hreflect]
    apply Finset.sum_congr rfl
    intro a ha
    apply reciprocalSineTerm_sub hq
    exact (Nat.le_of_lt (Finset.mem_Ico.mp ha).2).trans (by omega)
  have hrest :
      (∑ a ∈ Finset.Ico m (2 * m), reciprocalSineTerm (2 * m) a) =
        reciprocalSineTerm (2 * m) m +
          ∑ a ∈ Finset.Ico (m + 1) (2 * m), reciprocalSineTerm (2 * m) a := by
    calc
      _ = (∑ a ∈ Finset.Ico m (m + 1), reciprocalSineTerm (2 * m) a) +
          ∑ a ∈ Finset.Ico (m + 1) (2 * m), reciprocalSineTerm (2 * m) a := by
        rw [Finset.sum_Ico_consecutive (reciprocalSineTerm (2 * m))
          (by omega) (by omega)]
      _ = _ := by simp
  calc
    (∑ a ∈ Finset.Ico 1 (2 * m), reciprocalSineTerm (2 * m) a) =
        (∑ a ∈ Finset.Ico 1 m, reciprocalSineTerm (2 * m) a) +
          ∑ a ∈ Finset.Ico m (2 * m), reciprocalSineTerm (2 * m) a := by
      rw [Finset.sum_Ico_consecutive (reciprocalSineTerm (2 * m))
        (by omega) (by omega)]
    _ = 2 * (∑ a ∈ Finset.Ico 1 m, reciprocalSineTerm (2 * m) a) + 1 := by
      rw [hrest, hupper, reciprocalSineTerm_two_mul_self hm]
      ring

/-- Davenport's sharp sum of reciprocal sines over the nonzero natural
representatives modulo `q`; see DavenportMNTCh23PV1980, printed p. 136. -/
theorem sum_reciprocalSine_Ico_lt_mul_log {q : ℕ} (hq : 1 < q) :
    (∑ a ∈ Finset.Ico 1 q,
      (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹) <
      (q : ℝ) * Real.log (q : ℝ) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' q
  · have hm : 0 < m := by omega
    change (∑ a ∈ Finset.Ico 1 (2 * m), reciprocalSineTerm (2 * m) a) < _
    rw [sum_reciprocalSine_even_eq_two_mul_add_one hm]
    have hhalf := sum_reciprocalSine_Ico_le_half_mul_harmonic
      (q := 2 * m) (m := m - 1) (by omega) (by omega)
    have htop : m - 1 + 1 = m := Nat.sub_add_cancel hm
    rw [htop] at hhalf
    have hlog := harmonic_cast_pred_add_inv_two_mul_lt_log_two_mul hm
    calc
      2 * (∑ a ∈ Finset.Ico 1 m, reciprocalSineTerm (2 * m) a) + 1 ≤
          2 * (((2 * m : ℕ) : ℝ) / 2 * (harmonic (m - 1) : ℝ)) + 1 :=
        by
          simpa only [add_comm] using add_le_add_right
            (mul_le_mul_of_nonneg_left hhalf (show (0 : ℝ) ≤ 2 by norm_num)) 1
      _ = ((2 * m : ℕ) : ℝ) *
          ((harmonic (m - 1) : ℝ) + (((2 * m : ℕ) : ℝ))⁻¹) := by
        have htwoM : (((2 * m : ℕ) : ℝ)) ≠ 0 := by positivity
        field_simp
      _ < ((2 * m : ℕ) : ℝ) * Real.log (((2 * m : ℕ) : ℝ)) :=
        mul_lt_mul_of_pos_left hlog (by positivity)
  · have hm : 0 < m := by omega
    change (∑ a ∈ Finset.Ico 1 (2 * m + 1),
      reciprocalSineTerm (2 * m + 1) a) < _
    rw [sum_reciprocalSine_odd_eq_two_mul]
    have hhalf := sum_reciprocalSine_Ico_le_half_mul_harmonic
      (q := 2 * m + 1) (m := m) (by omega) (by omega)
    have hlog := harmonic_cast_lt_log_two_mul_add_one hm
    calc
      2 * (∑ a ∈ Finset.Ico 1 (m + 1), reciprocalSineTerm (2 * m + 1) a) ≤
          2 * (((2 * m + 1 : ℕ) : ℝ) / 2 * (harmonic m : ℝ)) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
      _ = ((2 * m + 1 : ℕ) : ℝ) * (harmonic m : ℝ) := by ring
      _ < ((2 * m + 1 : ℕ) : ℝ) * Real.log (((2 * m + 1 : ℕ) : ℝ)) := by
        apply mul_lt_mul_of_pos_left _ (by positivity)
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hlog

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/PrimitivePolyaVinogradov.lean` -/

section

/-!
# Primitive Polya--Vinogradov interval bound

This is the direct composition of the audited pre-aggregate envelope and the
strict reciprocal-sine estimate in DavenportMNTCh23PV1980, printed p. 136.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

/-- Primitive Polya--Vinogradov on an arbitrary translated integer interval. -/
theorem norm_sum_dirichletCharacter_Ioc_lt_sqrt_mul_log
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)‖ <
      Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast Nat.zero_lt_of_lt hq
  have hsqrt : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqpos
  calc
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)‖ ≤
        (∑ a ∈ Finset.Ico 1 q,
          (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹) /
          Real.sqrt q :=
      norm_sum_dirichletCharacter_Ioc_le_reciprocalSineSum hq chi hchi M N
    _ < ((q : ℝ) * Real.log (q : ℝ)) / Real.sqrt q :=
      div_lt_div_of_pos_right (sum_reciprocalSine_Ico_lt_mul_log hq) hsqrt
    _ = Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      apply (div_eq_iff hsqrt.ne').2
      calc
        (q : ℝ) * Real.log (q : ℝ) =
            (Real.sqrt (q : ℝ)) ^ 2 * Real.log (q : ℝ) := by
          rw [Real.sq_sqrt hqpos.le]
        _ = (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
            Real.sqrt (q : ℝ) := by ring

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Statement.lean` -/

section

/-! # Bombieri--Vinogradov statement surface -/

namespace BoundedGaps.Maynard

open scoped BigOperators










end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/WeightedStatement.lean` -/

section

/-!
# Weighted Bombieri--Vinogradov statement layer

This file records the natural-endpoint von Mangoldt interface selected in
`Vaughan1980` and cross-checked against `DavenportMNTCh28BV1980`. It defines
only finite sums, discrepancies, and a proposition contract. It proves no
Siegel--Walfisz, large-sieve, or Bombieri--Vinogradov theorem.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators ArithmeticFunction.vonMangoldt










end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/CharacterOrthogonality.lean` -/

section

/-!
# Character orthogonality for weighted progression sums

This file implements the finite algebraic bridge reviewed in SEM-413. It
expresses a von Mangoldt progression sum as an average of complex character
twists. It contains no character-sum estimate or asymptotic theorem.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators ArithmeticFunction.vonMangoldt







end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/VaughanConvolutionIdentity.lean` -/

section

/-!
# Vaughan's convolution identity

This file formalizes the finite arithmetic-function core of the four-term
Vaughan decomposition in Akbary--Hambrook2013v2, Section 6, pp. 18--19. The
explicit pair and triple source-index expansions remain separate.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction ArithmeticFunction.Moebius
  ArithmeticFunction.zeta BigOperators

noncomputable section











end

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/VaughanSourceReindex.lean` -/

section

/-!
# Vaughan source reindexing

This file expands the third and fourth convolution terms from SEM-429 into
the exact finite sums displayed in Akbary--Hambrook2013v2, Section 6,
pp. 18--19. It contains no character or analytic estimate.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction ArithmeticFunction.Moebius
  ArithmeticFunction.zeta BigOperators

noncomputable section




end

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/VaughanTwistedDecomposition.lean` -/

section

/-!
# Vaughan's character-twisted decomposition

This file lifts the four source-shaped Vaughan coefficients from
Akbary--Hambrook2013v2, Section 6, pp. 18--19 through a complex Dirichlet
character and the finite natural endpoint sum. It contains no character-sum
estimate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators ArithmeticFunction.vonMangoldt

noncomputable section







end

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/VaughanSecondTermReindex.lean` -/

section

/-!
# Vaughan's second-term factor reindex

This file reindexes the second twisted Vaughan term from its endpoint and
factor-antidiagonal form to `AkbaryHambrook2013v2`, Section 6, p. 19.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section







end

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/VaughanSecondTermReduction.lean` -/

section

/-!
# Vaughan's second-term finite reduction

This file formalizes `AkbaryHambrook2013v2`, Section 6, pp. 19--20,
equation (6.8), at natural endpoints. It stops before Pólya--Vinogradov.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- A complex Dirichlet-character sum over an inclusive natural interval. -/
noncomputable def dirichletCharacterIntervalSum
    (a b q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ h ∈ Finset.Icc a b, χ h









end

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/VaughanSecondTermPolyaVinogradov.lean` -/

section

/-!
# Polya--Vinogradov bound for Vaughan's second term

This file transfers the primitive interval theorem to SEM-433's natural
interval convention and proves AkbaryHambrook2013v2, equation (6.9). The raw
modulus-one estimate and the aggregate equation (6.10) remain separate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

/-- Primitive Polya--Vinogradov on an inclusive natural interval. -/
theorem norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
    {q : ℕ} (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (a b : ℕ) :
    ‖dirichletCharacterIntervalSum a b q chi‖ <
      Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  letI : NeZero q := ⟨Nat.ne_zero_of_lt hq⟩
  have hboundPos :
      0 < Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
    exact mul_pos (Real.sqrt_pos.2 (by exact_mod_cast Nat.zero_lt_of_lt hq))
      (Real.log_pos (by exact_mod_cast hq))
  by_cases hab : a ≤ b
  · have hendpoint :
        (a : ℤ) - 1 + (((b - a) + 1 : ℕ) : ℤ) = (b : ℤ) := by
      rw [Nat.cast_add, Nat.cast_sub hab]
      push_cast
      ring
    have hfinset :
        (Finset.Icc a b).map (Nat.castEmbedding : ℕ ↪ ℤ) =
          Finset.Ioc ((a : ℤ) - 1) (b : ℤ) := by
      ext n
      simp only [Finset.mem_map, Nat.castEmbedding_apply, Finset.mem_Icc,
        Finset.mem_Ioc]
      constructor
      · rintro ⟨m, hm, rfl⟩
        constructor <;> omega
      · intro hn
        have hnnonneg : 0 ≤ n := by
          have : (a : ℤ) ≤ n := by omega
          exact (Int.natCast_nonneg a).trans this
        lift n to ℕ using hnnonneg with m
        refine ⟨m, ?_, rfl⟩
        constructor <;> omega
    rw [dirichletCharacterIntervalSum]
    calc
      ‖∑ n ∈ Finset.Icc a b, chi n‖ =
          ‖∑ n ∈ Finset.Ioc ((a : ℤ) - 1) (b : ℤ),
            chi (n : ZMod q)‖ := by
        rw [← hfinset, Finset.sum_map]
        simp
      _ = ‖∑ n ∈ Finset.Ioc ((a : ℤ) - 1)
            ((a : ℤ) - 1 + (((b - a) + 1 : ℕ) : ℤ)),
            chi (n : ZMod q)‖ := by rw [hendpoint]
      _ < Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
        norm_sum_dirichletCharacter_Ioc_lt_sqrt_mul_log hq chi hchi
          ((a : ℤ) - 1) ((b - a) + 1)
  · rw [dirichletCharacterIntervalSum, Finset.Icc_eq_empty (by omega),
      Finset.sum_empty, norm_zero]
    exact hboundPos


end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/PrimitiveLFunctionCentralStrip.lean` -/

section

/-!
# Primitive Dirichlet L-functions in the central strip

For a primitive character of level greater than one, this file continues the
Abel integral for its Dirichlet series to the positive half-plane and derives
a coarse explicit bound on `1 / 2 ≤ re s ≤ 2`.

Sources: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 110 for
conditional convergence, printed p. 113 for Lemma 11.2 and its proof, printed
p. 13 for partial summation (1.8)--(1.9), and printed pp. 106--107 for the
Polya--Vinogradov inequality, Theorem 10.6. Semantic review: `SEM-474`.
-/

open Asymptotics Complex Filter MeasureTheory Set
open scoped BigOperators Real Topology

namespace BoundedGaps.Maynard

private lemma polyaVinogradovScale_pos {q : ℕ} (hq : 1 < q) :
    0 < Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  exact mul_pos
    (Real.sqrt_pos.2 (by exact_mod_cast Nat.zero_lt_of_lt hq))
    (Real.log_pos (by exact_mod_cast hq))

/-- A primitive character of modulus greater than one is nonprincipal. -/
theorem character_ne_one_of_isPrimitive
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive) : chi ≠ 1 := by
  intro heq
  have hc : chi.conductor = 1 :=
    DirichletCharacter.eq_one_iff_conductor_eq_one.mp heq
  have hp : chi.conductor = q := hchi
  omega

/-- The conditionally convergent character series represented by its Abel
integral throughout the positive half-plane. The equality is first obtained
in the half-plane of absolute convergence and then continued analytically.
See printed p. 110, partial summation (1.8)--(1.9) on p. 13, and Theorem 10.6
on pp. 106--107, whose project implementation is reviewed in `SEM-438`. -/
theorem LFunction_eq_abelIntegral_of_isPrimitive
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (s : ℂ) (hs : 0 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * ∫ y in Set.Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1)) := by
  simpa [dirichletCharacterIntervalSum] using
    LFunction_eq_abelIntegral_of_prefixBound chi
      (character_ne_one_of_isPrimitive hq chi hchi)
      (Real.sqrt (q : ℝ) * Real.log (q : ℝ))
      (fun n ↦ by
        simpa [dirichletCharacterIntervalSum] using
          (norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
            hq chi hchi 1 n).le)
      s hs

private lemma norm_characterAbelIntegral_le
    {q : ℕ} (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {s : ℂ} (hs : 0 < s.re) :
    ‖∫ y in Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
      (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / s.re := by
  have hPower : IntegrableOn
      (fun y : ℝ ↦ y ^ (-(s.re + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hScale : 0 ≤ Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
    (polyaVinogradovScale_pos hq).le
  have hDom : IntegrableOn
      (fun y : ℝ ↦
        (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
          y ^ (-(s.re + 1))) (Ioi 1) :=
    hPower.const_mul _
  have hActualMeasurable : AEStronglyMeasurable
      (fun y : ℝ ↦
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))) (volume.restrict (Ioi 1)) := by
    have hPrefix : Measurable
        (fun y : ℝ ↦ dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi) :=
      (measurable_of_countable
        (fun n : ℕ ↦ dirichletCharacterIntervalSum 1 n q chi)).comp
        Nat.measurable_floor
    have hCpow : ContinuousOn
        (fun y : ℝ ↦ (y : ℂ) ^ (-(s + 1))) (Ioi 1) :=
      continuousOn_of_forall_continuousAt fun y hy ↦
        continuousAt_ofReal_cpow_const y (-(s + 1))
          (Or.inr (zero_lt_one.trans hy).ne')
    exact hPrefix.aestronglyMeasurable.mul
      (hCpow.aestronglyMeasurable measurableSet_Ioi)
  have hBound : ∀ᵐ (y : ℝ) ∂volume.restrict (Ioi 1),
      ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
        (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
          y ^ (-(s.re + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hy)]
    simp only [neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_right
      (norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
        hq chi hchi 1 ⌊y⌋₊).le
      (Real.rpow_nonneg (zero_lt_one.trans hy).le _)
  have hActual : IntegrableOn
      (fun y : ℝ ↦
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    hDom.mono' hActualMeasurable hBound
  calc
    ‖∫ y in Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
        ∫ y in Ioi (1 : ℝ),
          ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
            (y : ℂ) ^ (-(s + 1))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioi (1 : ℝ),
          (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
            y ^ (-(s.re + 1)) :=
      setIntegral_mono_ae_restrict hActual.norm hDom hBound
    _ = (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
        ∫ y in Ioi (1 : ℝ), y ^ (-(s.re + 1)) := by
      rw [integral_const_mul]
    _ = (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / s.re := by
      rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
      field_simp [hs.ne']
      ring

/-- A coarse explicit `j = 0` central-strip consequence of Lemma 11.2. The
source states a sharper bound with an implied constant; the literal factor
`2` here is derived from the global Polya--Vinogradov bound and strip limits. -/
theorem norm_LFunction_centralStrip_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {sigma t : ℝ} (hsigma_lower : (1 / 2 : ℝ) ≤ sigma)
    (hsigma_upper : sigma ≤ 2) :
    ‖DirichletCharacter.LFunction chi ((sigma : ℂ) + t * I)‖ ≤
      2 * (|t| + 2) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  let s : ℂ := (sigma : ℂ) + t * I
  have hsigma_pos : 0 < sigma := by linarith
  have hsre : s.re = sigma := by simp [s]
  have hspos : 0 < s.re := hsre.symm ▸ hsigma_pos
  have hscale : 0 ≤ Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
    (polyaVinogradovScale_pos hq).le
  have hnormS : ‖s‖ ≤ |t| + 2 := by
    calc
      ‖s‖ ≤ ‖(sigma : ℂ)‖ + ‖(t : ℂ) * I‖ := by
        simpa only [s] using norm_add_le (sigma : ℂ) ((t : ℂ) * I)
      _ = |sigma| + |t| := by simp [Real.norm_eq_abs]
      _ = sigma + |t| := by rw [abs_of_nonneg hsigma_pos.le]
      _ ≤ |t| + 2 := by linarith
  have hinv : 1 / sigma ≤ 2 := by
    apply (div_le_iff₀ hsigma_pos).2
    linarith
  have hquot :
      (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / sigma ≤
        2 * (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) := by
    calc
      (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / sigma =
          (1 / sigma) *
            (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) := by ring
      _ ≤ 2 * (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hinv hscale
  have hIntegral := norm_characterAbelIntegral_le hq chi hchi hspos
  rw [hsre] at hIntegral
  change ‖DirichletCharacter.LFunction chi s‖ ≤ _
  calc
    ‖DirichletCharacter.LFunction chi s‖ =
        ‖s‖ *
          ‖∫ y in Ioi (1 : ℝ),
            dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
              (y : ℂ) ^ (-(s + 1))‖ := by
      rw [LFunction_eq_abelIntegral_of_isPrimitive hq chi hchi s hspos,
        norm_mul]
    _ ≤ ‖s‖ *
        ((Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / sigma) :=
      mul_le_mul_of_nonneg_left hIntegral (norm_nonneg s)
    _ ≤ (|t| + 2) *
        ((Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / sigma) :=
      mul_le_mul_of_nonneg_right hnormS
        (div_nonneg hscale hsigma_pos.le)
    _ ≤ (|t| + 2) *
        (2 * (Real.sqrt (q : ℝ) * Real.log (q : ℝ))) :=
      mul_le_mul_of_nonneg_left hquot (by positivity)
    _ = 2 * (|t| + 2) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      ring

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/PrimitiveLFunctionFixedStrip.lean` -/

section

/-!
# Primitive Dirichlet L-functions on a fixed left strip

This file combines the primitive central-strip estimate, the exact ordinary-L
functional equation, and the fixed-strip Gamma-factor bound. It gives an
explicit polynomial-growth realization of Koukoulopoulos, printed p. 114,
Lemma 11.4. The natural exponent `12` is a conservative local consequence,
not an exponent printed in the source. See semantic review SEM-477.
-/

namespace BoundedGaps.Maynard

open Complex

/-- In the half-plane of absolute convergence, every positive-modulus
Dirichlet L-function is bounded by three. -/
theorem norm_LFunction_farRight_le_three
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (z : ℂ)
    (hz : (2 : ℝ) ≤ z.re) :
    ‖DirichletCharacter.LFunction chi z‖ ≤ 3 := by
  have hz1 : 1 < z.re := one_lt_two.trans_le hz
  have hsummable : LSeriesSummable (chi ·) z :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re chi hz1
  rw [DirichletCharacter.LFunction_eq_LSeries chi hz1, LSeries]
  calc
    ‖∑' n : ℕ, LSeries.term (chi ·) z n‖ ≤
        ∑' n : ℕ, ‖LSeries.term (chi ·) z n‖ :=
      norm_tsum_le_tsum_norm hsummable.norm
    _ ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by
      apply hsummable.norm.tsum_le_tsum
      · intro n
        rw [LSeries.norm_term_eq]
        split_ifs with hn
        · simp
        · have hn1 : (1 : ℝ) ≤ n := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
          have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ z.re := by
            rw [← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le hn1 hz
          calc
            ‖chi n‖ / (n : ℝ) ^ z.re ≤ 1 / (n : ℝ) ^ z.re :=
              div_le_div_of_nonneg_right (chi.norm_le_one n)
                (Real.rpow_nonneg (Nat.cast_nonneg n) z.re)
            _ ≤ 1 / (n : ℝ) ^ 2 :=
              one_div_le_one_div_of_le (by positivity) hpow
      · exact Real.summable_one_div_nat_pow.mpr (by norm_num)
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
    _ ≤ 3 := by nlinarith [Real.pi_nonneg, Real.pi_le_four]

/-- Primitive Dirichlet L-functions have absolute polynomial growth on the
fixed left strip used by the local zero-expansion argument.

This is an explicit fixed-degree realization of the polynomial-growth step
in Koukoulopoulos, printed p. 114, Lemma 11.4. -/
theorem exists_norm_LFunction_fixedStrip_le_const_mul_pow_twelve :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ s : ℂ, -(10 : ℝ) ≤ s.re → s.re ≤ (1 / 2 : ℝ) →
            ‖DirichletCharacter.LFunction chi s‖ ≤
              C * ((q : ℝ) * (|s.im| + 2)) ^ 12 := by
  obtain ⟨Cgamma, hCgamma, hgamma⟩ :=
    exists_norm_gammaFactor_ratio_fixedStrip_le
  refine ⟨3 * Cgamma, mul_pos (by norm_num) hCgamma, ?_⟩
  intro q _ hq chi hchi s hslo hshi
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := one_le_two.trans hq2
  have hq0 : (0 : ℝ) ≤ q := zero_le_one.trans hq1
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hq1
  have hT2 : (2 : ℝ) ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hT1 : (1 : ℝ) ≤ |s.im| + 2 := one_le_two.trans hT2
  have hT0 : (0 : ℝ) ≤ |s.im| + 2 := zero_le_one.trans hT1
  have hchiInv : chi⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hchi
  have hgamma' := hgamma q chi s hslo hshi
  rw [norm_LFunction_eq_functionalEquation_of_isPrimitive hq chi hchi s hshi]
  by_cases hmid : -(1 : ℝ) ≤ s.re
  · have hreflected := norm_LFunction_centralStrip_le hq chi⁻¹ hchiInv
      (sigma := 1 - s.re) (t := -s.im) (by linarith) (by linarith)
    have hreflectArg :
        (((1 - s.re : ℝ) : ℂ) + ((-s.im : ℝ) : ℂ) * I) = 1 - s := by
      apply Complex.ext <;> simp
    rw [hreflectArg] at hreflected
    simp only [abs_neg] at hreflected
    have hqpow :
        (q : ℝ) ^ ((1 : ℝ) / 2 - s.re) ≤ (q : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    have hsqrt : Real.sqrt (q : ℝ) ≤ q :=
      Real.sqrt_le_self_iff.mpr (Or.inr hq1)
    have hlog : Real.log (q : ℝ) ≤ q :=
      (Real.log_le_sub_one_of_pos hqpos).trans
        (sub_le_self _ zero_le_one)
    have hqpowFour : (q : ℝ) ^ 4 ≤ (q : ℝ) ^ 12 :=
      pow_le_pow_right₀ hq1 (by norm_num)
    calc
      (q : ℝ) ^ ((1 : ℝ) / 2 - s.re) *
            ‖DirichletCharacter.LFunction chi⁻¹ (1 - s)‖ *
          ‖DirichletCharacter.gammaFactor chi⁻¹ (1 - s) /
            DirichletCharacter.gammaFactor chi s‖ ≤
          (q : ℝ) ^ 2 *
              (2 * (|s.im| + 2) * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
            (Cgamma * (|s.im| + 2) ^ 11) := by
        gcongr
      _ ≤ (q : ℝ) ^ 2 *
              (2 * (|s.im| + 2) * (q : ℝ) * (q : ℝ)) *
            (Cgamma * (|s.im| + 2) ^ 11) := by
        gcongr
      _ = (2 * Cgamma) * (q : ℝ) ^ 4 * (|s.im| + 2) ^ 12 := by
        ring
      _ ≤ (3 * Cgamma) * (q : ℝ) ^ 12 * (|s.im| + 2) ^ 12 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (by nlinarith) hqpowFour (pow_nonneg hq0 4)
            (by positivity))
          (pow_nonneg hT0 12)
      _ = (3 * Cgamma) * ((q : ℝ) * (|s.im| + 2)) ^ 12 := by
        rw [mul_pow]
        ring
  · have hreflected := norm_LFunction_farRight_le_three chi⁻¹ (1 - s) (by
      simp only [sub_re, one_re]
      linarith)
    have hqpow :
        (q : ℝ) ^ ((1 : ℝ) / 2 - s.re) ≤ (q : ℝ) ^ (11 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    have hqpowstep : (q : ℝ) ^ 11 ≤ (q : ℝ) ^ 12 := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hq0 11) hq1
    have hTpowstep : (|s.im| + 2) ^ 11 ≤ (|s.im| + 2) ^ 12 := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hT0 11) hT1
    calc
      (q : ℝ) ^ ((1 : ℝ) / 2 - s.re) *
            ‖DirichletCharacter.LFunction chi⁻¹ (1 - s)‖ *
          ‖DirichletCharacter.gammaFactor chi⁻¹ (1 - s) /
            DirichletCharacter.gammaFactor chi s‖ ≤
          (q : ℝ) ^ 11 * 3 * (Cgamma * (|s.im| + 2) ^ 11) := by
        gcongr
      _ = (3 * Cgamma) * (q : ℝ) ^ 11 * (|s.im| + 2) ^ 11 := by
        ring
      _ ≤ (3 * Cgamma) * (q : ℝ) ^ 12 * (|s.im| + 2) ^ 12 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hqpowstep (by positivity)) hTpowstep
          (pow_nonneg hT0 11) (by positivity)
      _ = (3 * Cgamma) * ((q : ℝ) * (|s.im| + 2)) ^ 12 := by
        rw [mul_pow]
        ring

private lemma natCast_le_four_pow (n : ℕ) : (n : ℝ) ≤ 4 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.cast_succ, pow_succ]
      have hone : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
      nlinarith

/-- The absolute coefficient in the fixed-degree strip bound can be absorbed
into one uniform natural conductor-height exponent. -/
theorem exists_norm_LFunction_fixedStrip_le_pow :
    ∃ A : ℕ, 12 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ s : ℂ, -(10 : ℝ) ≤ s.re → s.re ≤ (1 / 2 : ℝ) →
            ‖DirichletCharacter.LFunction chi s‖ ≤
              ((q : ℝ) * (|s.im| + 2)) ^ A := by
  obtain ⟨C, _hCpos, hC⟩ :=
    exists_norm_LFunction_fixedStrip_le_const_mul_pow_twelve
  obtain ⟨n : ℕ, hn⟩ := exists_nat_ge C
  refine ⟨n + 12, by omega, ?_⟩
  intro q _ hq chi hchi s hslo hshi
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hT2 : (2 : ℝ) ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hbase4 : (4 : ℝ) ≤ (q : ℝ) * (|s.im| + 2) := by
    nlinarith
  have hbase0 : (0 : ℝ) ≤ (q : ℝ) * (|s.im| + 2) :=
    zero_le_four.trans hbase4
  have hCbase : C ≤ ((q : ℝ) * (|s.im| + 2)) ^ n := by
    calc
      C ≤ (n : ℝ) := hn
      _ ≤ 4 ^ n := natCast_le_four_pow n
      _ ≤ ((q : ℝ) * (|s.im| + 2)) ^ n :=
        pow_le_pow_left₀ (by norm_num) hbase4 n
  calc
    ‖DirichletCharacter.LFunction chi s‖ ≤
        C * ((q : ℝ) * (|s.im| + 2)) ^ 12 :=
      hC q hq chi hchi s hslo hshi
    _ ≤ ((q : ℝ) * (|s.im| + 2)) ^ n *
        ((q : ℝ) * (|s.im| + 2)) ^ 12 :=
      mul_le_mul_of_nonneg_right hCbase (pow_nonneg hbase0 12)
    _ = ((q : ℝ) * (|s.im| + 2)) ^ (n + 12) := by
      rw [pow_add]

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/DirichletLFunctionClosedStripGrowth.lean` -/

section

/-!
# Dirichlet L-functions on the Goldfeld strip

This file extends the primitive fixed-strip bound through the exact inducing
Euler product.  The resulting estimate covers the generally imprimitive
cross character in Koukoulopoulos, printed p. 126, Theorem 12.9.

Source: printed p. 110, equation (11.2), and printed p. 115, Exercise 11.1.
Semantic review: `SEM-556`.
-/

namespace BoundedGaps.Maynard

open Complex

/-- On `Re(s) >= -1`, the finite Euler product omitted by passage to the
primitive inducer costs at most the square of the original level. -/
theorem norm_inducingEulerProduct_le_sq_of_neg_one_le_re
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : -(1 : ℝ) ≤ s.re) :
    ‖inducingEulerProduct chi s‖ ≤ (q : ℝ) ^ 2 := by
  rw [inducingEulerProduct]
  calc
    ‖∏ p ∈ q.primeFactors,
        (1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s))‖ ≤
        ∏ p ∈ q.primeFactors,
          ‖1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s)‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ p ∈ q.primeFactors, (p : ℝ) ^ 2 := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        have hpPrime := Nat.prime_of_mem_primeFactors hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_le
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
        have hpow : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) := by
          calc
            (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
            _ = (p : ℝ) := Real.rpow_one _
        calc
          ‖1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s)‖ ≤
              1 + ‖chi.primitiveCharacter p * (p : ℂ) ^ (-s)‖ := by
            simpa using norm_sub_le (1 : ℂ)
              (chi.primitiveCharacter p * (p : ℂ) ^ (-s))
          _ = 1 + ‖chi.primitiveCharacter p‖ * (p : ℝ) ^ (-s.re) := by
            rw [norm_mul, Complex.norm_natCast_cpow_of_pos hpPrime.pos, neg_re]
          _ ≤ 1 + 1 * (p : ℝ) := by
            gcongr
            exact chi.primitiveCharacter.norm_le_one p
          _ ≤ (p : ℝ) ^ 2 := by nlinarith
    _ = (∏ p ∈ q.primeFactors, (p : ℝ)) ^ 2 :=
      Finset.prod_pow q.primeFactors 2 (fun p : ℕ => (p : ℝ))
    _ = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ 2 := by
      push_cast
      rfl
    _ ≤ (q : ℝ) ^ 2 := by
      gcongr
      exact_mod_cast Nat.le_of_dvd (NeZero.pos q)
        (Nat.prod_primeFactors_dvd q)

private theorem exists_norm_primitiveLFunction_closedStrip_le_pow :
    ∃ A : ℕ, 12 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ s : ℂ, -(1 : ℝ) ≤ s.re → s.re ≤ 3 →
            ‖DirichletCharacter.LFunction chi s‖ ≤
              ((q : ℝ) * (|s.im| + 2)) ^ A := by
  obtain ⟨A, hA, hleft⟩ := exists_norm_LFunction_fixedStrip_le_pow
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi s hslo hshi
  let T : ℝ := |s.im| + 2
  let B : ℝ := (q : ℝ) * T
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := one_le_two.trans hq2
  have hT2 : (2 : ℝ) ≤ T := by
    dsimp [T]
    linarith [abs_nonneg s.im]
  have hB4 : (4 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hB1 : (1 : ℝ) ≤ B := by linarith
  by_cases hleftCase : s.re ≤ (1 / 2 : ℝ)
  · exact hleft q hq chi hchi s (by linarith) hleftCase
  · have hhalf : (1 / 2 : ℝ) ≤ s.re := le_of_not_ge hleftCase
    by_cases hcentral : s.re ≤ 2
    · have hc := norm_LFunction_centralStrip_le hq chi hchi
          (sigma := s.re) (t := s.im) hhalf hcentral
      have hsarg : (((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * I) = s := by
        apply Complex.ext <;> simp
      rw [hsarg] at hc
      have hsqrt : Real.sqrt (q : ℝ) ≤ q :=
        Real.sqrt_le_self_iff.mpr (Or.inr hq1)
      have hlog : Real.log (q : ℝ) ≤ q :=
        (Real.log_le_sub_one_of_pos (by positivity)).trans
          (sub_le_self _ zero_le_one)
      have hcentralBound :
          2 * T * Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤ B ^ 2 := by
        calc
          2 * T * Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤
              2 * T * (q : ℝ) * (q : ℝ) := by gcongr
          _ ≤ ((q : ℝ) * T) ^ 2 := by nlinarith
          _ = B ^ 2 := rfl
      calc
        ‖DirichletCharacter.LFunction chi s‖ ≤
            2 * T * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
          simpa [T] using hc
        _ ≤ B ^ 2 := hcentralBound
        _ ≤ B ^ A := pow_le_pow_right₀ hB1 (by omega)
    · have hfar : (2 : ℝ) ≤ s.re := le_of_not_ge hcentral
      have hf := norm_LFunction_farRight_le_three chi s hfar
      calc
        ‖DirichletCharacter.LFunction chi s‖ ≤ 3 := hf
        _ ≤ B ^ 1 := by simp; linarith
        _ ≤ B ^ A := pow_le_pow_right₀ hB1 (by omega)

/-- One absolute exponent controls every nonprincipal, possibly imprimitive,
Dirichlet L-function on the closed strip used by Goldfeld's contour. -/
theorem exists_norm_LFunction_closedStrip_le_pow :
    ∃ A : ℕ, 14 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi ≠ 1 →
          ∀ s : ℂ, -(1 : ℝ) ≤ s.re → s.re ≤ 3 →
            ‖DirichletCharacter.LFunction chi s‖ ≤
              ((q : ℝ) * (|s.im| + 2)) ^ A := by
  obtain ⟨A, hA, hprimitive⟩ :=
    exists_norm_primitiveLFunction_closedStrip_le_pow
  refine ⟨A + 2, by omega, ?_⟩
  intro q _ hq chi hchi s hslo hshi
  let d := chi.conductor
  letI : NeZero d := ⟨chi.conductor_ne_zero⟩
  have hd1 : 1 < d := by
    have hdne : d ≠ 1 := by
      intro hd
      apply hchi
      exact DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hd
    have hd0 : d ≠ 0 := NeZero.ne d
    omega
  have hdq : d ≤ q :=
    Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level
  let T : ℝ := |s.im| + 2
  let B : ℝ := (q : ℝ) * T
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := one_le_two.trans hq2
  have hT2 : (2 : ℝ) ≤ T := by
    dsimp [T]
    linarith [abs_nonneg s.im]
  have hT0 : (0 : ℝ) ≤ T := zero_le_two.trans hT2
  have hB1 : (1 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hprimitiveBound := hprimitive d hd1 chi.primitiveCharacter
    chi.primitiveCharacter_isPrimitive s hslo hshi
  have hbase : (d : ℝ) * T ≤ B := by
    dsimp [B]
    gcongr
  have hprimitiveBound' :
      ‖DirichletCharacter.LFunction chi.primitiveCharacter s‖ ≤ B ^ A :=
    hprimitiveBound.trans (by
      simpa [T] using
        pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg d) hT0) hbase A)
  have hEuler := norm_inducingEulerProduct_le_sq_of_neg_one_le_re chi hslo
  have hqB : (q : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hqSq : (q : ℝ) ^ 2 ≤ B ^ 2 := by gcongr
  rw [LFunction_eq_inducingPrimitive_mul_inducingEulerProduct chi (.inl hchi),
    norm_mul]
  calc
    ‖DirichletCharacter.LFunction chi.primitiveCharacter s‖ *
        ‖inducingEulerProduct chi s‖ ≤ B ^ A * B ^ 2 :=
      mul_le_mul hprimitiveBound' (hEuler.trans hqSq)
        (norm_nonneg _) (pow_nonneg (zero_le_one.trans hB1) A)
    _ = B ^ (A + 2) := by rw [pow_add]

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldCoefficient.lean` -/

section

/-!
# Goldfeld's four-factor coefficient

This file reconstructs the coefficient and initial half-plane series identity
in the proof of Koukoulopoulos Theorem 12.9, printed p. 126.  The two
individual characters retain their original levels; only their product is
formed at the canonical least-common-multiple level.  The later Mellin cutoff
and contour argument are deliberately separate.

Semantic review: `SEM-551`.
-/

noncomputable section

open scoped ComplexOrder
open ArithmeticFunction

namespace BoundedGaps.Maynard

private instance goldfeldLcmNeZero {q1 q : ℕ} [NeZero q1] [NeZero q] :
    NeZero (Nat.lcm q1 q) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩

/-- The original-level fourfold Dirichlet convolution in Goldfeld's proof. -/
noncomputable def goldfeldCoefficient
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  ((ArithmeticFunction.zeta * toArithmeticFunction (chi1 ·)) *
      toArithmeticFunction (chi ·)) *
    toArithmeticFunction (DirichletCharacter.mul chi1 chi ·)

/-- Canonical cross-level multiplication agrees with the original pointwise product. -/
theorem goldfeldCrossLevelMul_apply
    {q1 q n : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q) :
    DirichletCharacter.mul chi1 chi n = chi1 n * chi n := by
  by_cases h1 : Nat.Coprime n q1
  · by_cases h2 : Nat.Coprime n q
    · have hlcm : Nat.Coprime n (Nat.lcm q1 q) :=
        Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul q1 q) (h1.mul_right h2)
      change
        (chi1.changeLevel (Nat.dvd_lcm_left q1 q) *
          chi.changeLevel (Nat.dvd_lcm_right q1 q)) n = _
      rw [MulChar.mul_apply]
      have hInt : IsCoprime (n : ℤ) (Nat.lcm q1 q : ℤ) :=
        Nat.Coprime.isCoprime hlcm
      simpa using congrArg₂ (· * ·)
        (DirichletCharacter.changeLevel_eq_cast_of_dvd' chi1
          (Nat.dvd_lcm_left q1 q) hInt)
        (DirichletCharacter.changeLevel_eq_cast_of_dvd' chi
          (Nat.dvd_lcm_right q1 q) hInt)
    · have hlcm : ¬Nat.Coprime n (Nat.lcm q1 q) := fun h =>
        h2 (Nat.Coprime.of_dvd_right (Nat.dvd_lcm_right q1 q) h)
      have hpzero : DirichletCharacter.mul chi1 chi n = 0 :=
        MulChar.map_nonunit _ (by
          simpa [ZMod.isUnit_iff_coprime] using hlcm)
      have hzero : chi n = 0 :=
        MulChar.map_nonunit _ (by
          simpa [ZMod.isUnit_iff_coprime] using h2)
      rw [hpzero, hzero, mul_zero]
  · have hlcm : ¬Nat.Coprime n (Nat.lcm q1 q) := fun h =>
      h1 (Nat.Coprime.of_dvd_right (Nat.dvd_lcm_left q1 q) h)
    have hpzero : DirichletCharacter.mul chi1 chi n = 0 :=
      MulChar.map_nonunit _ (by
        simpa [ZMod.isUnit_iff_coprime] using hlcm)
    have hzero : chi1 n = 0 :=
      MulChar.map_nonunit _ (by
        simpa [ZMod.isUnit_iff_coprime] using h1)
    rw [hpzero, hzero, zero_mul]

theorem goldfeldCoefficient_one
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q) :
    goldfeldCoefficient chi1 chi 1 = 1 := by
  simp [goldfeldCoefficient, toArithmeticFunction]

private theorem characterAF_prime_pow
    {q p k : ℕ} (chi : DirichletCharacter ℂ q) (hp : p.Prime) :
    toArithmeticFunction (chi ·) (p ^ k) = (chi p) ^ k := by
  rw [← chi.apply_eq_toArithmeticFunction_apply (pow_ne_zero k hp.ne_zero)]
  simpa only [Nat.cast_pow] using map_pow chi (p : ZMod q) k

private theorem productAF_prime_pow
    {q1 q p k : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q)
    (hp : p.Prime) :
    toArithmeticFunction (DirichletCharacter.mul chi1 chi ·) (p ^ k) =
      (chi1 p * chi p) ^ k := by
  rw [characterAF_prime_pow _ hp, goldfeldCrossLevelMul_apply]

private theorem zeta_prime_pow {p k : ℕ} (hp : p.Prime) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p ^ k) = 1 := by
  have hpow : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  simp only [ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne hpow, Nat.cast_one]

private theorem mul_apply_prime_pow
    (f g : ArithmeticFunction ℂ) {p k : ℕ} (hp : p.Prime) :
    (f * g) (p ^ k) =
      ∑ i ∈ Finset.range (k + 1), f (p ^ i) * g (p ^ (k - i)) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => f x * g y),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.pow_div (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hp.pos]

private theorem mul_apply_prime_pow_eq_left_of_right_unit
    (f g : ArithmeticFunction ℂ) {p k : ℕ} (hp : p.Prime)
    (hone : g 1 = 1) (hzero : ∀ j, 0 < j → g (p ^ j) = 0) :
    (f * g) (p ^ k) = f (p ^ k) := by
  rw [mul_apply_prime_pow f g hp]
  classical
  rw [Finset.sum_eq_single k]
  · simp [hone]
  · intro i hi hik
    have hik' : i < k :=
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).lt_of_ne hik
    rw [hzero (k - i) (Nat.sub_pos_of_lt hik'), mul_zero]
  · simp

private theorem mul_prime_pow_nonneg_of_local_eq
    (f g : ArithmeticFunction ℂ) {p k : ℕ} (hp : p.Prime)
    (hf : ∀ n, 0 ≤ f n) (hlocal : ∀ j, g (p ^ j) = f (p ^ j)) :
    0 ≤ (f * g) (p ^ k) := by
  rw [mul_apply_prime_pow f g hp]
  exact Finset.sum_nonneg fun i _ => by
    rw [hlocal]
    exact mul_nonneg (hf _) (hf _)

private theorem goldfeldCoefficient_prime_pow_nonneg
    {q1 q p : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare : chi ^ 2 = 1)
    (hp : p.Prime) (k : ℕ) :
    0 ≤ goldfeldCoefficient chi1 chi (p ^ k) := by
  let A := toArithmeticFunction (chi1 ·)
  let B := toArithmeticFunction (chi ·)
  let C := toArithmeticFunction (DirichletCharacter.mul chi1 chi ·)
  let Z : ArithmeticFunction ℂ := ArithmeticFunction.zeta
  have hA : ∀ j, A (p ^ j) = (chi1 p) ^ j := fun _ =>
    characterAF_prime_pow chi1 hp
  have hB : ∀ j, B (p ^ j) = (chi p) ^ j := fun _ =>
    characterAF_prime_pow chi hp
  have hC : ∀ j, C (p ^ j) = (chi1 p * chi p) ^ j := fun _ =>
    productAF_prime_pow chi1 chi hp
  have hZ : ∀ j, Z (p ^ j) = 1 := fun _ => zeta_prime_pow hp
  have hZA : ∀ n, 0 ≤ (Z * A) n := fun n => by
    simpa [Z, A, DirichletCharacter.zetaMul] using
      chi1.zetaMul_nonneg hsquare1 n
  have hZB : ∀ n, 0 ≤ (Z * B) n := fun n => by
    simpa [Z, B, DirichletCharacter.zetaMul] using
      chi.zetaMul_nonneg hsquare n
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsquare1 p with ha | ha | ha
  · have hCunit : C 1 = 1 := by simpa using hC 0
    have hCzero : ∀ j, 0 < j → C (p ^ j) = 0 := by
      intro j hj
      rw [hC]
      simp [ha, zero_pow hj.ne']
    have hAC (j : ℕ) : (A * C) (p ^ j) = A (p ^ j) :=
      mul_apply_prime_pow_eq_left_of_right_unit A C hp hCunit hCzero
    have hACunit : (A * C) 1 = 1 := by
      calc
        (A * C) 1 = (A * C) (p ^ 0) := by simp
        _ = A (p ^ 0) := hAC 0
        _ = (chi1 p) ^ 0 := hA 0
        _ = 1 := by simp
    have hACzero : ∀ j, 0 < j → (A * C) (p ^ j) = 0 := by
      intro j hj
      rw [hAC, hA]
      simp [ha, zero_pow hj.ne']
    rw [goldfeldCoefficient]
    rw [show ((Z * A) * B) * C = (Z * B) * (A * C) by ac_rfl]
    rw [mul_apply_prime_pow_eq_left_of_right_unit (Z * B) (A * C)
      hp hACunit hACzero]
    exact hZB _
  · rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsquare p with hb | hb | hb
    · have hBunit : B 1 = 1 := by simpa using hB 0
      have hBzero : ∀ j, 0 < j → B (p ^ j) = 0 := by
        intro j hj
        rw [hB]
        simp [hb, zero_pow hj.ne']
      have hCB (j : ℕ) : (C * B) (p ^ j) = C (p ^ j) :=
        mul_apply_prime_pow_eq_left_of_right_unit C B hp hBunit hBzero
      have hCBunit : (C * B) 1 = 1 := by
        calc
          (C * B) 1 = (C * B) (p ^ 0) := by simp
          _ = C (p ^ 0) := hCB 0
          _ = (chi1 p * chi p) ^ 0 := hC 0
          _ = 1 := by simp
      have hCBzero : ∀ j, 0 < j → (C * B) (p ^ j) = 0 := by
        intro j hj
        rw [hCB, hC]
        simp [hb, zero_pow hj.ne']
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * A) * (C * B) by ac_rfl]
      rw [mul_apply_prime_pow_eq_left_of_right_unit (Z * A) (C * B)
        hp hCBunit hCBzero]
      exact hZA _
    · have hpair (j : ℕ) : (B * C) (p ^ j) = (Z * A) (p ^ j) := by
        rw [mul_apply_prime_pow B C hp, mul_apply_prime_pow Z A hp]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hB, hC, hZ, hA]
        simp [ha, hb]
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * A) * (B * C) by ac_rfl]
      exact mul_prime_pow_nonneg_of_local_eq (Z * A) (B * C) hp hZA hpair
    · have hpair (j : ℕ) : (A * C) (p ^ j) = (Z * B) (p ^ j) := by
        rw [mul_apply_prime_pow A C hp, mul_apply_prime_pow Z B hp]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hA, hC, hZ, hB]
        simp [ha, hb]
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * B) * (A * C) by ac_rfl]
      exact mul_prime_pow_nonneg_of_local_eq (Z * B) (A * C) hp hZB hpair
  · rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsquare p with hb | hb | hb
    · have hBunit : B 1 = 1 := by simpa using hB 0
      have hBzero : ∀ j, 0 < j → B (p ^ j) = 0 := by
        intro j hj
        rw [hB]
        simp [hb, zero_pow hj.ne']
      have hCB (j : ℕ) : (C * B) (p ^ j) = C (p ^ j) :=
        mul_apply_prime_pow_eq_left_of_right_unit C B hp hBunit hBzero
      have hCBunit : (C * B) 1 = 1 := by
        calc
          (C * B) 1 = (C * B) (p ^ 0) := by simp
          _ = C (p ^ 0) := hCB 0
          _ = (chi1 p * chi p) ^ 0 := hC 0
          _ = 1 := by simp
      have hCBzero : ∀ j, 0 < j → (C * B) (p ^ j) = 0 := by
        intro j hj
        rw [hCB, hC]
        simp [hb, zero_pow hj.ne']
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * A) * (C * B) by ac_rfl]
      rw [mul_apply_prime_pow_eq_left_of_right_unit (Z * A) (C * B)
        hp hCBunit hCBzero]
      exact hZA _
    · have hpair (j : ℕ) : (B * C) (p ^ j) = (Z * A) (p ^ j) := by
        rw [mul_apply_prime_pow B C hp, mul_apply_prime_pow Z A hp]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hB, hC, hZ, hA]
        simp [ha, hb]
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * A) * (B * C) by ac_rfl]
      exact mul_prime_pow_nonneg_of_local_eq (Z * A) (B * C) hp hZA hpair
    · have hpair (j : ℕ) : (C * B) (p ^ j) = (Z * A) (p ^ j) := by
        rw [mul_apply_prime_pow C B hp, mul_apply_prime_pow Z A hp]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hC, hB, hZ, hA]
        simp [ha, hb]
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * A) * (C * B) by ac_rfl]
      exact mul_prime_pow_nonneg_of_local_eq (Z * A) (C * B) hp hZA hpair

private theorem goldfeldCoefficient_isMultiplicative
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q) :
    (goldfeldCoefficient chi1 chi).IsMultiplicative := by
  exact (((ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    chi1.isMultiplicative_toArithmeticFunction).mul
      chi.isMultiplicative_toArithmeticFunction).mul
        (DirichletCharacter.mul chi1 chi).isMultiplicative_toArithmeticFunction)

/-- Every coefficient is real and nonnegative for two square-principal characters. -/
theorem goldfeldCoefficient_nonneg
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare : chi ^ 2 = 1) (n : ℕ) :
    0 ≤ goldfeldCoefficient chi1 chi n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [(goldfeldCoefficient_isMultiplicative chi1 chi).multiplicative_factorization _ hn]
    exact Finset.prod_nonneg fun p hp =>
      goldfeldCoefficient_prime_pow_nonneg chi1 chi hsquare1 hsquare
        (Nat.prime_of_mem_primeFactors hp) _

private theorem characterAF_LSeriesHasSum
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (toArithmeticFunction (chi ·)) s
      (DirichletCharacter.LFunction chi s) := by
  have hsummable : LSeriesSummable (toArithmeticFunction (chi ·)) s :=
    (LSeriesSummable_congr s fun hn =>
      chi.apply_eq_toArithmeticFunction_apply hn).mp
        (ZMod.LSeriesSummable_of_one_lt_re chi hs)
  rw [chi.LFunction_eq_LSeries hs,
    LSeries_congr (fun hn => chi.apply_eq_toArithmeticFunction_apply hn) s]
  exact hsummable.LSeriesHasSum

/-- The coefficient series equals Goldfeld's four-factor product on `Re(s)>1`. -/
theorem goldfeldCoefficient_LSeriesHasSum
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (goldfeldCoefficient chi1 chi) s
      (riemannZeta s * DirichletCharacter.LFunction chi1 s *
        DirichletCharacter.LFunction chi s *
          DirichletCharacter.LFunction
            (DirichletCharacter.mul chi1 chi) s) := by
  exact ArithmeticFunction.LSeriesHasSum_mul
    (ArithmeticFunction.LSeriesHasSum_mul
      (ArithmeticFunction.LSeriesHasSum_mul
        (ArithmeticFunction.LSeriesHasSum_zeta hs)
        (characterAF_LSeriesHasSum chi1 hs))
      (characterAF_LSeriesHasSum chi hs))
    (characterAF_LSeriesHasSum (DirichletCharacter.mul chi1 chi) hs)

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldMellinInversion.lean` -/

section

/-!
# Smooth Mellin inversion for an absolutely convergent L-series

This file proves the generic form of Koukoulopoulos equation (7.8).  The
vertical integral is a Bochner integral over the real line, so the source
factor `1 / (2 * pi * I)` becomes `1 / (2 * pi)` after upward
parameterization.

Semantic review: `SEM-553`.
-/

noncomputable section

open Complex MeasureTheory

namespace BoundedGaps.Maynard

private lemma cpow_div_of_pos
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (s : ℂ) :
    ((x / y : ℝ) : ℂ) ^ s = (x : ℂ) ^ s / (y : ℂ) ^ s := by
  rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (div_ne_zero hx.ne' hy.ne')),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
    ← Complex.exp_sub]
  congr 1
  rw [← sub_mul]
  congr 1
  rw [← Complex.ofReal_log (div_nonneg hx.le hy.le),
    Real.log_div hx.ne' hy.ne', Complex.ofReal_sub,
    Complex.ofReal_log hx.le, Complex.ofReal_log hy.le]

private lemma cpow_neg_div_of_pos
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (s : ℂ) :
    ((x / y : ℝ) : ℂ) ^ (-s) =
      (x : ℂ) ^ (-s) * (y : ℂ) ^ s := by
  rw [cpow_div_of_pos hx hy, Complex.cpow_neg, Complex.cpow_neg,
    div_inv_eq_mul]

/-- Smooth Mellin inversion after interchanging an absolutely convergent
L-series with the full vertical integral. -/
theorem smoothMellinLSeriesInversion
    (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (phi : ℝ → ℂ) {alpha x : ℝ}
    (_halpha : 0 < alpha) (hx : 0 < x)
    (hsum : LSeriesSummable a (alpha : ℂ))
    (hphi : MellinConvergent phi (alpha : ℂ))
    (hphiVertical : VerticalIntegrable (mellin phi) alpha)
    (hphiContinuous : Continuous phi) :
    (∑' n : ℕ, a n * phi ((n : ℝ) / x)) =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ t : ℝ,
          LSeries a ((alpha : ℂ) + t * I) *
            mellin phi ((alpha : ℂ) + t * I) *
            (x : ℂ) ^ ((alpha : ℂ) + t * I) := by
  let s : ℝ → ℂ := fun t => (alpha : ℂ) + t * I
  let phiLine : ℝ → ℂ := fun t => mellin phi (s t)
  let F : ℕ → ℝ → ℂ := fun n t =>
    LSeries.term a (s t) n * phiLine t * (x : ℂ) ^ (s t)
  let G : ℝ → ℂ := fun t =>
    LSeries a (s t) * phiLine t * (x : ℂ) ^ (s t)
  have hsContinuous : Continuous s := by
    fun_prop
  have hxPowContinuous : Continuous fun t : ℝ => (x : ℂ) ^ (s t) := by
    exact continuous_const.cpow hsContinuous fun _ =>
      Complex.ofReal_mem_slitPlane.mpr hx
  have htermContinuous (n : ℕ) :
      Continuous fun t : ℝ => LSeries.term a (s t) n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simpa using (continuous_const : Continuous fun _ : ℝ => (0 : ℂ))
    · have hnReal : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hpow : Continuous fun t : ℝ => (n : ℂ) ^ (s t) := by
        exact continuous_const.cpow hsContinuous fun _ => by
          simpa only [← Complex.ofReal_natCast] using
            Complex.ofReal_mem_slitPlane.mpr hnReal
      have hpowNe (t : ℝ) : (n : ℂ) ^ (s t) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr <| Or.inl <| Nat.cast_ne_zero.mpr hn
      simp only [LSeries.term_of_ne_zero hn]
      exact continuous_const.div hpow hpowNe
  have hphiLineIntegrable : Integrable phiLine := by
    simpa [VerticalIntegrable, phiLine, s] using hphiVertical
  have hmultiplierContinuous (n : ℕ) : Continuous fun t : ℝ =>
      LSeries.term a (s t) n * (x : ℂ) ^ (s t) :=
    (htermContinuous n).mul hxPowContinuous
  have hmultiplierNorm (n : ℕ) (t : ℝ) :
      ‖LSeries.term a (s t) n * (x : ℂ) ^ (s t)‖ =
        ‖LSeries.term a (alpha : ℂ) n‖ * x ^ alpha := by
    rw [norm_mul, LSeries.norm_term_eq, LSeries.norm_term_eq,
      Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp [s]
  have hFIntegrable (n : ℕ) : Integrable (F n) := by
    have h := hphiLineIntegrable.mul_bdd
      (hmultiplierContinuous n).aestronglyMeasurable
      (ae_of_all _ fun t => (hmultiplierNorm n t).le)
    convert h using 1
    funext t
    simp only [F, phiLine]
    ring
  have hFNormIntegral (n : ℕ) :
      (∫ t : ℝ, ‖F n t‖) =
        ‖LSeries.term a (alpha : ℂ) n‖ * x ^ alpha *
          ∫ t : ℝ, ‖phiLine t‖ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [show F n t = phiLine t *
        (LSeries.term a (s t) n * (x : ℂ) ^ (s t)) by
      simp only [F]
      ring]
    rw [norm_mul, hmultiplierNorm]
    ring
  have hFNormSummable : Summable fun n : ℕ => ∫ t : ℝ, ‖F n t‖ := by
    refine (hsum.norm.mul_right
      (x ^ alpha * ∫ t : ℝ, ‖phiLine t‖)).congr ?_
    intro n
    rw [hFNormIntegral]
    ring
  have hFHasSum (t : ℝ) : HasSum (fun n : ℕ => F n t) (G t) := by
    have hline : LSeriesSummable a (s t) :=
      hsum.of_re_le_re (by simp [s])
    have h := (hline.LSeriesHasSum.mul_right (phiLine t)).mul_right
      ((x : ℂ) ^ (s t))
    simpa [F, G] using h
  have hinterchange : HasSum (fun n : ℕ => ∫ t : ℝ, F n t)
      (∫ t : ℝ, G t) := by
    have h := hasSum_integral_of_summable_integral_norm hFIntegrable hFNormSummable
    rw [← integral_congr_ae
      (ae_of_all _ fun t => (hFHasSum t).tsum_eq)]
    exact h
  have hterm (n : ℕ) :
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) * (∫ t : ℝ, F n t) =
        a n * phi ((n : ℝ) / x) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [ha0, F]
    · have hnReal : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hratio : 0 < (n : ℝ) / x := div_pos hnReal hx
      have hpoint (t : ℝ) : F n t =
          a n * (((n : ℝ) / x : ℝ) : ℂ) ^ (-(s t)) * phiLine t := by
        dsimp only [F]
        rw [LSeries.term_def₀ ha0, cpow_neg_div_of_pos hnReal hx]
        simp only [Complex.ofReal_natCast]
        ring
      have hintegral : (∫ t : ℝ, F n t) =
          a n * ∫ t : ℝ,
            (((n : ℝ) / x : ℝ) : ℂ) ^ (-(s t)) * phiLine t := by
        calc
          (∫ t : ℝ, F n t) = ∫ t : ℝ,
              a n * ((((n : ℝ) / x : ℝ) : ℂ) ^ (-(s t)) * phiLine t) := by
            apply integral_congr_ae
            exact ae_of_all _ fun t => by rw [hpoint]; ring
          _ = a n * ∫ t : ℝ,
              (((n : ℝ) / x : ℝ) : ℂ) ^ (-(s t)) * phiLine t :=
            MeasureTheory.integral_const_mul _ _
      have hinversion := mellinInv_mellin_eq alpha phi hratio hphi
        hphiVertical (hphiContinuous.continuousAt)
      have hinversion' :
          (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
              (∫ t : ℝ,
                (((n : ℝ) / x : ℝ) : ℂ) ^ (-(s t)) * phiLine t) =
            phi ((n : ℝ) / x) := by
        simpa [mellinInv, s, phiLine, smul_eq_mul, div_eq_mul_inv,
          mul_comm] using hinversion
      rw [hintegral, ← mul_assoc, mul_comm _ (a n), mul_assoc,
        hinversion']
  have hscaled := hinterchange.mul_left (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  have hsumSmoothed : HasSum (fun n : ℕ =>
      a n * phi ((n : ℝ) / x))
      ((((2 * Real.pi : ℝ) : ℂ)⁻¹) * ∫ t : ℝ, G t) :=
    hscaled.congr_fun fun n => (hterm n).symm
  simpa [G, phiLine, s] using hsumSmoothed.tsum_eq

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldPlateauMellin.lean` -/

section

/-!
# Goldfeld's smooth plateau and Mellin boundary

This file freezes the fixed smooth cutoff used in the proof of
Koukoulopoulos Theorem 12.9.  The cutoff is constructed independently with
Mathlib's smooth separation theorem.  Its restriction to the nonnegative
half-line is one on `[0, 1]`, takes values in `[0, 1]`, and vanishes from `2`
onwards.  The raw Mellin transform is only used on `Re(s) > 0`; continuation
and the vertical decay estimate are represented by the explicit contract below
and are kept separate from the later sum/integral interchange.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 73--74,
80, and 125--126.  Semantic review: `SEM-552`.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped ContDiff Topology

namespace BoundedGaps.Maynard

private noncomputable def goldfeldPlateauBump : ContDiffBump (1 / 2 : ℝ) :=
  ⟨1 / 2, 3 / 2, by norm_num, by norm_num⟩

/-- A fixed smooth extension of the plateau cutoff from Theorem 12.9. -/
noncomputable def goldfeldPlateau : ℝ → ℝ := goldfeldPlateauBump

theorem goldfeldPlateau_contDiff : ContDiff ℝ ∞ goldfeldPlateau := by
  simpa [goldfeldPlateau] using
    (goldfeldPlateauBump.contDiff : ContDiff ℝ ∞ (goldfeldPlateauBump : ℝ → ℝ))

theorem goldfeldPlateau_range : Set.range goldfeldPlateau ⊆ Icc 0 1 := by
  rintro _ ⟨y, rfl⟩
  exact ⟨goldfeldPlateauBump.nonneg, goldfeldPlateauBump.le_one⟩

theorem goldfeldPlateau_nonneg (y : ℝ) : 0 ≤ goldfeldPlateau y := by
  exact (goldfeldPlateau_range ⟨y, rfl⟩).1

theorem goldfeldPlateau_le_one (y : ℝ) : goldfeldPlateau y ≤ 1 := by
  exact (goldfeldPlateau_range ⟨y, rfl⟩).2

theorem goldfeldPlateau_eq_one {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    goldfeldPlateau y = 1 := by
  apply goldfeldPlateauBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  simp only [goldfeldPlateauBump]
  rw [abs_le]
  constructor <;> linarith

theorem goldfeldPlateau_eq_zero {y : ℝ} (hy : 2 ≤ y) :
    goldfeldPlateau y = 0 := by
  apply goldfeldPlateauBump.zero_of_le_dist
  rw [Real.dist_eq]
  simp only [goldfeldPlateauBump]
  rw [abs_of_nonneg (by linarith : 0 ≤ y - 1 / 2)]
  linarith

theorem goldfeldPlateau_hasCompactSupport :
    HasCompactSupport goldfeldPlateau := by
  simpa [goldfeldPlateau] using goldfeldPlateauBump.hasCompactSupport

private noncomputable def goldfeldPlateauComplex : ℝ → ℂ :=
  fun y => goldfeldPlateau y

/-- The raw Mellin transform, only used in its half-plane of convergence. -/
noncomputable def goldfeldRawMellin (s : ℂ) : ℂ :=
  mellin goldfeldPlateauComplex s

private lemma goldfeldPlateauComplex_locallyIntegrable :
    LocallyIntegrableOn goldfeldPlateauComplex (Ioi (0 : ℝ)) := by
  apply (Complex.continuous_ofReal.comp goldfeldPlateau_contDiff.continuous).continuousOn
    |>.locallyIntegrableOn measurableSet_Ioi

private lemma goldfeldPlateauComplex_isBigO_top :
    ∀ a : ℝ, goldfeldPlateauComplex =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  intro a
  refine Filter.Eventually.isBigO ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with y hy
  change ‖(goldfeldPlateau y : ℂ)‖ ≤ _
  rw [goldfeldPlateau_eq_zero hy.le]
  simp only [Complex.ofReal_zero, norm_zero]
  exact Real.rpow_nonneg (by linarith) _

private lemma goldfeldPlateauComplex_isBigO_zero :
    goldfeldPlateauComplex =O[nhdsWithin 0 (Ioi 0)] (fun _ : ℝ => (1 : ℝ)) := by
  refine Filter.Eventually.isBigO ?_
  filter_upwards [] with y
  change ‖(goldfeldPlateau y : ℂ)‖ ≤ 1
  calc
    ‖(goldfeldPlateau y : ℂ)‖ = |goldfeldPlateau y| := RCLike.norm_ofReal _
    _ = goldfeldPlateau y := abs_of_nonneg (goldfeldPlateau_nonneg y)
    _ ≤ 1 := goldfeldPlateau_le_one y

theorem goldfeldRawMellin_convergent {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent goldfeldPlateauComplex s := by
  refine mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := 0)
    goldfeldPlateauComplex_locallyIntegrable ?_ ?_ ?_ ?_
  · simpa using goldfeldPlateauComplex_isBigO_top (s.re + 1)
  · linarith
  · simpa using goldfeldPlateauComplex_isBigO_zero
  · linarith


/-- The complex derivative of the real plateau. -/
noncomputable def goldfeldPlateauDerivativeComplex : ℝ → ℂ :=
  fun y => ((deriv goldfeldPlateau) y : ℂ)

/-- The derivative weight used after one Mellin integration by parts. -/
noncomputable def goldfeldMellinDerivativeWeight (y : ℝ) : ℂ :=
  (y : ℂ) * goldfeldPlateauDerivativeComplex y

theorem goldfeldPlateau_deriv_contDiff :
    ContDiff ℝ ∞ (deriv goldfeldPlateau) :=
  (contDiff_infty_iff_deriv.mp goldfeldPlateau_contDiff).2

private theorem goldfeldPlateau_deriv_hasCompactSupport :
    HasCompactSupport (deriv goldfeldPlateau) :=
  goldfeldPlateau_hasCompactSupport.deriv

theorem goldfeldPlateau_deriv_eq_zero_of_pos_of_lt_one
    {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    deriv goldfeldPlateau y = 0 := by
  have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 y := hasDerivAt_const y 1
  have h := hconst.congr_of_eventuallyEq
    (show (fun z : ℝ => goldfeldPlateau z) =ᶠ[𝓝 y] (fun _ => (1 : ℝ)) by
      filter_upwards [Ioo_mem_nhds hy0 hy1] with z hz
      exact goldfeldPlateau_eq_one hz.1.le hz.2.le)
  exact h.deriv

theorem goldfeldPlateau_deriv_eq_zero_of_two_lt
    {y : ℝ} (hy : 2 < y) : deriv goldfeldPlateau y = 0 := by
  have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 y := hasDerivAt_const y 0
  have h := hconst.congr_of_eventuallyEq
    (show (fun z : ℝ => goldfeldPlateau z) =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      exact goldfeldPlateau_eq_zero hz.le)
  exact h.deriv

private lemma goldfeldPlateauDerivativeComplex_locallyIntegrable :
    LocallyIntegrableOn goldfeldPlateauDerivativeComplex (Ioi (0 : ℝ)) := by
  have hcont : Continuous (deriv goldfeldPlateau) :=
    goldfeldPlateau_contDiff.continuous_deriv (by norm_num)
  exact (Complex.continuous_ofReal.comp hcont).continuousOn.locallyIntegrableOn
    (μ := volume) measurableSet_Ioi

private lemma goldfeldPlateauDerivativeComplex_isBigO_top :
    ∀ a : ℝ, goldfeldPlateauDerivativeComplex =O[atTop]
      (fun x : ℝ => x ^ (-a)) := by
  intro a
  refine Filter.Eventually.isBigO ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with y hy
  change ‖((deriv goldfeldPlateau) y : ℂ)‖ ≤ _
  rw [goldfeldPlateau_deriv_eq_zero_of_two_lt hy]
  simp only [Complex.ofReal_zero, norm_zero]
  exact Real.rpow_nonneg (by linarith) _

private lemma goldfeldPlateauDerivativeComplex_isBigO_zero :
    ∀ b : ℝ, goldfeldPlateauDerivativeComplex =O[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => x ^ (-b)) := by
  intro b
  refine Filter.Eventually.isBigO ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with y hy
  change ‖((deriv goldfeldPlateau) y : ℂ)‖ ≤ _
  rw [goldfeldPlateau_deriv_eq_zero_of_pos_of_lt_one hy.1 hy.2]
  simp only [Complex.ofReal_zero, norm_zero]
  exact Real.rpow_nonneg hy.1.le _

private theorem goldfeldPlateauDerivativeComplex_mellin_differentiableAt
    (s : ℂ) :
    DifferentiableAt ℂ (mellin goldfeldPlateauDerivativeComplex) s := by
  refine mellin_differentiableAt_of_isBigO_rpow
    (a := s.re + 1) (b := s.re - 1)
    goldfeldPlateauDerivativeComplex_locallyIntegrable ?_ ?_ ?_ ?_
  · simpa using goldfeldPlateauDerivativeComplex_isBigO_top (s.re + 1)
  · linarith
  · simpa using goldfeldPlateauDerivativeComplex_isBigO_zero (s.re - 1)
  · linarith

/-- Mellin transform of the derivative weight, shifted to expose the pole. -/
noncomputable def goldfeldDerivativeMellin (s : ℂ) : ℂ :=
  mellin goldfeldPlateauDerivativeComplex (s + 1)

theorem goldfeldDerivativeMellin_eq_weight (s : ℂ) :
    goldfeldDerivativeMellin s = mellin goldfeldMellinDerivativeWeight s := by
  unfold goldfeldDerivativeMellin goldfeldMellinDerivativeWeight
  rw [← mellin_cpow_smul]
  simp only [Complex.cpow_one, smul_eq_mul]

private theorem goldfeldDerivativeMellin_differentiableAt (s : ℂ) :
    DifferentiableAt ℂ goldfeldDerivativeMellin s := by
  exact (goldfeldPlateauDerivativeComplex_mellin_differentiableAt (s + 1)).comp s
    ((hasDerivAt_id' s).add_const 1).differentiableAt

/-- The derivative Mellin transform is entire. -/
theorem differentiable_goldfeldDerivativeMellin :
    Differentiable ℂ goldfeldDerivativeMellin :=
  fun s => goldfeldDerivativeMellin_differentiableAt s

/-- The integration-by-parts candidate for the continued Mellin transform.
Lean totalizes division, so its value at `s = 0` is an irrelevant representative;
the punctured-limit theorem below records the meromorphic pole. -/
noncomputable def goldfeldMellinCandidate (s : ℂ) : ℂ :=
  -goldfeldDerivativeMellin s / s

/-- On its initial half-plane, the integration-by-parts candidate is the raw
Mellin integral. -/
theorem goldfeldMellinCandidate_eq_raw {s : ℂ} (hs : 0 < s.re) :
    goldfeldMellinCandidate s = goldfeldRawMellin s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    simp at hs
  let u : ℝ → ℂ := fun x => (x : ℂ) ^ s
  let v : ℝ → ℂ := goldfeldPlateauComplex
  let uD : ℝ → ℂ := fun x => s * (x : ℂ) ^ (s - 1)
  let vD : ℝ → ℂ := fun x => Complex.ofReal ((deriv goldfeldPlateau) x)
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (uD x) x := by
    intro x hx
    exact hasDerivAt_ofReal_cpow_const hx.ne' hs0
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (vD x) x := by
    intro x hx
    exact (goldfeldPlateau_contDiff.differentiable (by simp)).differentiableAt
      |>.hasDerivAt.ofReal_comp
  have hvD_cont : Continuous vD := by
    exact Complex.continuous_ofReal.comp goldfeldPlateau_deriv_contDiff.continuous
  have hvD_compact : HasCompactSupport vD := by
    change HasCompactSupport (Complex.ofReal ∘ deriv goldfeldPlateau)
    exact goldfeldPlateau_deriv_hasCompactSupport.comp_left Complex.ofReal_zero
  have huvD : IntegrableOn (u * vD) (Ioi 0) := by
    apply Integrable.integrableOn
    exact ((Complex.continuous_ofReal_cpow_const hs).mul hvD_cont)
      |>.integrable_of_hasCompactSupport hvD_compact.mul_left
  have huDv : IntegrableOn (uD * v) (Ioi 0) := by
    have hm := goldfeldRawMellin_convergent hs
    rw [MellinConvergent] at hm
    change Integrable
      (fun x : ℝ => (s * (x : ℂ) ^ (s - 1)) * goldfeldPlateauComplex x)
      (volume.restrict (Ioi 0))
    simpa only [smul_eq_mul, mul_assoc] using hm.const_mul s
  have hzero : Tendsto (u * v) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hp : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc := (Complex.continuousAt_ofReal_cpow_const 0 s (Or.inl hs)).tendsto
      change Tendsto u (𝓝 0 ⊓ 𝓟 (Ioi 0)) (𝓝 0)
      simpa [u, Complex.zero_cpow hs0] using hc.mono_left inf_le_left
    have hv0 : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hphi0 : goldfeldPlateauComplex 0 = 1 := by
        change (goldfeldPlateau 0 : ℂ) = 1
        rw [goldfeldPlateau_eq_one (by norm_num) (by norm_num)]
        norm_num
      have hc : Tendsto goldfeldPlateauComplex (𝓝 (0 : ℝ))
          (𝓝 (goldfeldPlateauComplex 0)) :=
        (Complex.continuous_ofReal.comp goldfeldPlateau_contDiff.continuous)
          |>.continuousAt.tendsto
      change Tendsto v (𝓝 0 ⊓ 𝓟 (Ioi 0)) (𝓝 1)
      simpa [v, hphi0] using hc.mono_left inf_le_left
    change Tendsto (fun x => u x * v x) (𝓝[>] (0 : ℝ)) (𝓝 0)
    simpa using hp.mul hv0
  have hinfty : Tendsto (u * v) atTop (𝓝 0) := by
    have heq : u * v =ᶠ[atTop] 0 := by
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      simp [Pi.mul_apply, v, goldfeldPlateauComplex, goldfeldPlateau_eq_zero hx]
    exact heq.tendsto
  have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := 0) hu hv huvD huDv hzero hinfty
  have hweight : mellin goldfeldMellinDerivativeWeight s =
      ∫ x : ℝ in Ioi 0, u x * vD x := by
    rw [mellin]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [goldfeldMellinDerivativeWeight, goldfeldPlateauDerivativeComplex,
      u, vD, smul_eq_mul]
    have hpow : (x : ℂ) ^ (s - 1) * (x : ℂ) = (x : ℂ) ^ s := by
      calc
        (x : ℂ) ^ (s - 1) * (x : ℂ) =
            (x : ℂ) ^ (s - 1) * (x : ℂ) ^ (1 : ℂ) := by
              rw [Complex.cpow_one]
        _ = (x : ℂ) ^ ((s - 1) + 1) :=
          (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')).symm
        _ = (x : ℂ) ^ s := by rw [sub_add_cancel]
    rw [← mul_assoc, hpow]
  have hraw : ∫ x : ℝ in Ioi 0, uD x * v x =
      s * ∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (s - 1) * goldfeldPlateauComplex x := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp [uD, v, mul_assoc]
  rw [hraw] at hibp
  rw [goldfeldMellinCandidate, goldfeldDerivativeMellin_eq_weight, hweight,
    goldfeldRawMellin, mellin]
  simp only [smul_eq_mul, zero_sub, sub_zero] at hibp ⊢
  rw [hibp]
  field_simp [hs0]

theorem goldfeldMellinCandidate_meromorphic :
    MeromorphicOn goldfeldMellinCandidate Set.univ := by
  have hJ : AnalyticOnNhd ℂ goldfeldDerivativeMellin Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (fun s => goldfeldDerivativeMellin_differentiableAt s)
  have hneg : AnalyticOnNhd ℂ (fun s : ℂ => -goldfeldDerivativeMellin s) Set.univ := by
    exact hJ.neg
  exact hneg.meromorphicOn.div analyticOnNhd_id.meromorphicOn

theorem goldfeldMellinCandidate_analyticAt {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ goldfeldMellinCandidate s := by
  have hJ : AnalyticOnNhd ℂ goldfeldDerivativeMellin Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (fun z => goldfeldDerivativeMellin_differentiableAt z)
  have hneg : AnalyticOnNhd ℂ (fun z : ℂ => -goldfeldDerivativeMellin z) {0}ᶜ :=
    hJ.neg.mono (by intro z hz; exact Set.mem_univ z)
  have hdiv : AnalyticOnNhd ℂ goldfeldMellinCandidate {0}ᶜ := by
    change AnalyticOnNhd ℂ (fun z : ℂ => -goldfeldDerivativeMellin z / z) {0}ᶜ
    exact hneg.div (analyticOnNhd_id.mono (by intro z hz; exact Set.mem_univ z))
      (fun z hz => hz)
  exact hdiv s (by simp [hs])

private theorem goldfeldDerivativeMellin_zero :
    goldfeldDerivativeMellin 0 = -1 := by
  unfold goldfeldDerivativeMellin
  rw [show (0 : ℂ) + 1 = 1 by norm_num]
  rw [mellin]
  simp only [sub_self, cpow_zero, one_smul]
  have h := goldfeldPlateau_hasCompactSupport.integral_Ioi_deriv_eq
    (goldfeldPlateau_contDiff.of_le (by norm_num)) (0 : ℝ)
  unfold goldfeldPlateauDerivativeComplex
  change (∫ t : ℝ in Ioi 0, ((deriv goldfeldPlateau t : ℝ) : ℂ)) = -1
  have hcast := (integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun t : ℝ => (deriv goldfeldPlateau) t))
  calc
    (∫ t : ℝ in Ioi 0, (((deriv goldfeldPlateau) t : ℝ) : ℂ)) =
        Complex.ofReal (∫ t : ℝ in Ioi 0, (deriv goldfeldPlateau) t) := by
          exact hcast
    _ = -Complex.ofReal (goldfeldPlateau 0) := by
      simpa using congrArg Complex.ofReal h
    _ = -1 := by
      rw [goldfeldPlateau_eq_one (by norm_num) (by norm_num)]
      norm_num

theorem goldfeldMellinCandidate_residue :
    Tendsto (fun s => s * goldfeldMellinCandidate s) (𝓝[≠] 0) (𝓝 1) := by
  have hcont : Tendsto goldfeldDerivativeMellin (𝓝 0) (𝓝 (-(1 : ℂ))) := by
    have hc := (goldfeldDerivativeMellin_differentiableAt 0).continuousAt
    change Tendsto goldfeldDerivativeMellin (𝓝 0)
      (𝓝 (goldfeldDerivativeMellin 0)) at hc
    simpa only [goldfeldDerivativeMellin_zero] using hc
  have hpunct : Tendsto (fun s : ℂ => s * goldfeldMellinCandidate s)
      (𝓝[≠] 0) (𝓝 (1 : ℂ)) := by
    have heq : (fun s : ℂ => s * goldfeldMellinCandidate s) =ᶠ[𝓝[≠] 0]
        (fun s => -goldfeldDerivativeMellin s) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [goldfeldMellinCandidate]
      calc
        s * (-goldfeldDerivativeMellin s / s) =
            (-goldfeldDerivativeMellin s) * s / s := by ring
        _ = -goldfeldDerivativeMellin s := mul_div_cancel_right₀ _ hs
    have hneg : Tendsto (fun s : ℂ => -goldfeldDerivativeMellin s)
        (𝓝[≠] 0) (𝓝 (1 : ℂ)) := by
      simpa using ((hcont.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)).neg)
    exact hneg.congr' heq.symm
  exact hpunct

/-! The source-facing continuation is packaged as explicit data.  The companion
Schwartz/Fourier module supplies the fixed-line decay field. -/

/-- A total-function presentation of the meromorphic continuation.  The value
of `Phi` at zero is only Lean's totalized representative; `meromorphic`,
`analytic_off_zero`, and `residue_one` carry the source pole semantics. -/
structure GoldfeldMellinContinuationData where
  Phi : ℂ → ℂ
  agrees_on_right : ∀ {s : ℂ}, 0 < s.re → Phi s = goldfeldRawMellin s
  equals_candidate : ∀ s, Phi s = goldfeldMellinCandidate s
  meromorphic : MeromorphicOn Phi Set.univ
  analytic_off_zero : ∀ {s : ℂ}, s ≠ 0 → AnalyticAt ℂ Phi s
  residue_one : Tendsto (fun s => s * Phi s) (𝓝[≠] 0) (𝓝 1)
  decay_on_neg_one : ∀ (A : ℕ), 1 ≤ A →
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖Phi ((-1 : ℂ) + t * I)‖ ≤ C / (1 + |t|) ^ A

noncomputable def goldfeldMellinContinuationData_of_decay
    (hdecay : ∀ (A : ℕ), 1 ≤ A → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖goldfeldMellinCandidate ((-1 : ℂ) + t * I)‖ ≤ C / (1 + |t|) ^ A) :
    GoldfeldMellinContinuationData := by
  exact
    { Phi := goldfeldMellinCandidate
      agrees_on_right := fun hs => goldfeldMellinCandidate_eq_raw hs
      equals_candidate := fun _ => rfl
      meromorphic := goldfeldMellinCandidate_meromorphic
      analytic_off_zero := fun hs => goldfeldMellinCandidate_analyticAt hs
      residue_one := goldfeldMellinCandidate_residue
      decay_on_neg_one := hdecay }

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldPlateauMellinDecay.lean` -/

section

/-!
# Vertical decay for the Goldfeld Mellin candidate

The logarithmic substitution in the Mellin transform turns the derivative
weight into the Fourier transform of a compactly supported smooth function.
This file is intentionally separate from the cutoff/continuation contract:
the Schwartz estimate is the only remaining analytic input in SEM-552.

Semantic review: `SEM-552`.
-/

noncomputable section

open Complex Set MeasureTheory Filter Real
open scoped ContDiff Topology SchwartzMap FourierTransform

namespace BoundedGaps.Maynard

private noncomputable def goldfeldLogKernel (u : ℝ) : ℂ :=
  (Real.exp u : ℂ) * goldfeldMellinDerivativeWeight (Real.exp (-u))

private theorem goldfeldMellinDerivativeWeight_contDiff :
    ContDiff ℝ ∞ goldfeldMellinDerivativeWeight := by
  have hd : ContDiff ℝ ∞ goldfeldPlateauDerivativeComplex :=
    Complex.ofRealCLM.contDiff.comp goldfeldPlateau_deriv_contDiff
  unfold goldfeldMellinDerivativeWeight
  exact (Complex.ofRealCLM.contDiff.comp contDiff_id).mul hd

private theorem goldfeldLogKernel_contDiff :
    ContDiff ℝ ∞ goldfeldLogKernel := by
  have he : ContDiff ℝ ∞ (fun u : ℝ => (Real.exp u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_id.exp
  have hne : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-u)) :=
    (contDiff_id.neg).exp
  unfold goldfeldLogKernel
  exact he.mul (goldfeldMellinDerivativeWeight_contDiff.comp hne)

private theorem goldfeldLogKernel_eq_zero_of_pos {u : ℝ} (hu : 0 < u) :
    goldfeldLogKernel u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlt : Real.exp (-u) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hd := goldfeldPlateau_deriv_eq_zero_of_pos_of_lt_one harg hlt
  simp [goldfeldLogKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem goldfeldLogKernel_eq_zero_of_lt_neg_log_two
    {u : ℝ} (hu : u < -Real.log 2) : goldfeldLogKernel u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlog : Real.log 2 < -u := by linarith
  have hgt : 2 < Real.exp (-u) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact (Real.exp_lt_exp).2 hlog
  have hd := goldfeldPlateau_deriv_eq_zero_of_two_lt hgt
  simp [goldfeldLogKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem goldfeldLogKernel_support_subset :
    Function.support goldfeldLogKernel ⊆ Icc (-Real.log 2) 0 := by
  intro u hu
  by_contra hnot
  have hleft : u < -Real.log 2 ∨ 0 < u := by
    by_cases h₁ : u < -Real.log 2
    · exact Or.inl h₁
    · have h₁' : -Real.log 2 ≤ u := le_of_not_gt h₁
      by_cases h₂ : 0 < u
      · exact Or.inr h₂
      · have h₂' : u ≤ 0 := le_of_not_gt h₂
        exact False.elim (hnot ⟨h₁', h₂'⟩)
  rcases hleft with hleft | hright
  · exact hu (goldfeldLogKernel_eq_zero_of_lt_neg_log_two hleft)
  · exact hu (goldfeldLogKernel_eq_zero_of_pos hright)

private theorem goldfeldLogKernel_hasCompactSupport :
    HasCompactSupport goldfeldLogKernel := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc (-Real.log 2) 0)
    isCompact_Icc
  exact goldfeldLogKernel_support_subset

private noncomputable def goldfeldLogKernelSchwartz : 𝓢(ℝ, ℂ) :=
  goldfeldLogKernel_hasCompactSupport.toSchwartzMap goldfeldLogKernel_contDiff

private theorem goldfeldDerivativeMellin_on_neg_one (t : ℝ) :
    goldfeldDerivativeMellin ((-1 : ℂ) + t * I) =
      𝓕 goldfeldLogKernelSchwartz (t / (2 * π)) := by
  calc
    goldfeldDerivativeMellin ((-1 : ℂ) + t * I) =
        mellin goldfeldMellinDerivativeWeight ((-1 : ℂ) + t * I) :=
      goldfeldDerivativeMellin_eq_weight _
    _ = 𝓕 (fun u : ℝ =>
        Real.exp (-((-1 : ℂ) + t * I).re * u) •
          goldfeldMellinDerivativeWeight (Real.exp (-u)))
        (((-1 : ℂ) + t * I).im / (2 * π)) :=
      mellin_eq_fourier goldfeldMellinDerivativeWeight
    _ = 𝓕 goldfeldLogKernelSchwartz (t / (2 * π)) := by
      norm_num
      rw [SchwartzMap.fourier_coe]
      apply congrArg (fun f : ℝ → ℂ => 𝓕 f (t / (2 * π)))
      funext u
      simp [goldfeldLogKernelSchwartz, goldfeldLogKernel]

private theorem schwartz_pointwise_bound (f : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ‖(f : ℝ → ℂ) x‖ ≤ C / (1 + |x|) ^ A := by
  obtain ⟨C, hC, hbound⟩ := f.decay A 0
  obtain ⟨C0, hC0, hbound0⟩ := f.decay 0 0
  refine ⟨max (C * 2 ^ A) (C0 * 2 ^ A), by positivity, ?_⟩
  intro x
  by_cases hx : 1 ≤ |x|
  · have hpow : (1 + |x|) ^ A ≤ (2 * |x|) ^ A := by
      apply pow_le_pow_left₀ (by positivity) _ _
      linarith
    have hprod := hbound x
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hprod
    have hxpos : 0 < |x| := lt_of_lt_of_le (by norm_num) hx
    have hnorm : ‖(f : ℝ → ℂ) x‖ ≤ C / |x| ^ A := by
      apply (le_div_iff₀ (pow_pos hxpos A)).2
      simpa [mul_comm] using hprod
    calc
      ‖(f : ℝ → ℂ) x‖ ≤ C / |x| ^ A := hnorm
      _ ≤ (C * 2 ^ A) / (1 + |x|) ^ A := by
        apply (div_le_div_iff₀ (pow_pos hxpos A) (by positivity)).2
        calc
          C * (1 + |x|) ^ A ≤ C * (2 * |x|) ^ A :=
            mul_le_mul_of_nonneg_left hpow hC.le
          _ = (C * 2 ^ A) * |x| ^ A := by rw [mul_pow]; ring
      _ ≤ max (C * 2 ^ A) (C0 * 2 ^ A) / (1 + |x|) ^ A := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hx' : |x| < 1 := lt_of_not_ge hx
    have h0 := hbound0 x
    have h0' : ‖(f : ℝ → ℂ) x‖ ≤ C0 := by
      simpa [norm_iteratedFDeriv_zero] using h0
    have hsmall : C0 ≤ C0 * 2 ^ A / (1 + |x|) ^ A := by
      have hden : (1 + |x|) ^ A ≤ 2 ^ A := by
        apply pow_le_pow_left₀ (by positivity) _ _
        linarith
      have hdenpos : 0 < (1 + |x|) ^ A := by positivity
      apply (le_div_iff₀ hdenpos).2
      exact mul_le_mul_of_nonneg_left hden hC0.le
    have hmax : C0 * 2 ^ A / (1 + |x|) ^ A ≤
        max (C * 2 ^ A) (C0 * 2 ^ A) / (1 + |x|) ^ A := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    calc
      ‖(f : ℝ → ℂ) x‖ ≤ C0 := h0'
      _ ≤ C0 * 2 ^ A / (1 + |x|) ^ A := hsmall
      _ ≤ max (C * 2 ^ A) (C0 * 2 ^ A) / (1 + |x|) ^ A := hmax

theorem goldfeldMellinCandidate_decay_on_neg_one (A : ℕ) (_hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖goldfeldMellinCandidate ((-1 : ℂ) + t * I)‖ ≤ C / (1 + |t|) ^ A := by
  obtain ⟨C, hC, hpoint⟩ :=
    schwartz_pointwise_bound (𝓕 goldfeldLogKernelSchwartz) A
  refine ⟨C * (2 * π) ^ A, by positivity, ?_⟩
  intro t
  have hs : ((-1 : ℂ) + t * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hnorms : 1 ≤ ‖(-1 : ℂ) + t * I‖ := by
    have h := Complex.abs_re_le_norm ((-1 : ℂ) + t * I)
    norm_num at h ⊢
    exact h
  rw [goldfeldMellinCandidate, norm_div, norm_neg]
  calc
    ‖goldfeldDerivativeMellin ((-1 : ℂ) + t * I)‖ /
        ‖(-1 : ℂ) + t * I‖ ≤
      ‖goldfeldDerivativeMellin ((-1 : ℂ) + t * I)‖ :=
        (div_le_self (norm_nonneg _) hnorms)
    _ = ‖𝓕 goldfeldLogKernelSchwartz (t / (2 * π))‖ := by
      rw [goldfeldDerivativeMellin_on_neg_one]
    _ ≤ C / (1 + |t / (2 * π)|) ^ A := hpoint _
    _ ≤ C * (2 * π) ^ A / (1 + |t|) ^ A := by
      have hpi : 0 < (2 * π : ℝ) := by positivity
      have hpi1 : (1 : ℝ) ≤ 2 * π := by
        nlinarith [two_le_pi]
      rw [abs_div, abs_of_pos hpi]
      have hscale : 1 + |t| ≤ (2 * π) * (1 + |t| / (2 * π)) := by
        rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hpi)]
        nlinarith
      have hpowscale : (1 + |t|) ^ A ≤
          ((2 * π) * (1 + |t| / (2 * π))) ^ A :=
        pow_le_pow_left₀ (by positivity) hscale A
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      calc
        C * (1 + |t|) ^ A ≤
            C * ((2 * π) ^ A * (1 + |t| / (2 * π)) ^ A) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          simpa [mul_pow] using hpowscale
        _ = (C * (2 * π) ^ A) * (1 + |t| / (2 * π)) ^ A := by ring

/-- The complete source-facing continuation package for Goldfeld's cutoff. -/
noncomputable def goldfeldMellinContinuationData :
    GoldfeldMellinContinuationData :=
  goldfeldMellinContinuationData_of_decay
    goldfeldMellinCandidate_decay_on_neg_one

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldMellinPositiveLine.lean` -/

section

/-!
# Positive-line integrability of the Goldfeld Mellin transform

The generic inversion theorem needs the raw Mellin transform to be integrable
on its full positive vertical line.  We prove this by writing the derivative
Mellin transform as the Fourier transform of a compactly supported smooth
logarithmic kernel.

Semantic review: `SEM-553`.
-/

noncomputable section

open Complex Set MeasureTheory Real
open scoped ContDiff Topology SchwartzMap FourierTransform

namespace BoundedGaps.Maynard

private noncomputable def goldfeldPositiveLineKernel
    (alpha u : ℝ) : ℂ :=
  (Real.exp (-alpha * u) : ℂ) *
    goldfeldMellinDerivativeWeight (Real.exp (-u))

private theorem goldfeldMellinDerivativeWeight_contDiff_positiveLine :
    ContDiff ℝ ∞ goldfeldMellinDerivativeWeight := by
  have hd : ContDiff ℝ ∞ goldfeldPlateauDerivativeComplex :=
    Complex.ofRealCLM.contDiff.comp goldfeldPlateau_deriv_contDiff
  unfold goldfeldMellinDerivativeWeight
  exact (Complex.ofRealCLM.contDiff.comp contDiff_id).mul hd

private theorem goldfeldPositiveLineKernel_contDiff (alpha : ℝ) :
    ContDiff ℝ ∞ (goldfeldPositiveLineKernel alpha) := by
  have hlinear : ContDiff ℝ ∞ (fun u : ℝ => -alpha * u) :=
    contDiff_const.mul contDiff_id
  have heReal : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-alpha * u)) :=
    hlinear.exp
  have he : ContDiff ℝ ∞ (fun u : ℝ => (Real.exp (-alpha * u) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp heReal
  have harg : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-u)) := by
    fun_prop
  unfold goldfeldPositiveLineKernel
  exact he.mul
    (goldfeldMellinDerivativeWeight_contDiff_positiveLine.comp harg)

private theorem goldfeldPositiveLineKernel_eq_zero_of_pos
    (alpha : ℝ) {u : ℝ} (hu : 0 < u) :
    goldfeldPositiveLineKernel alpha u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlt : Real.exp (-u) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hd := goldfeldPlateau_deriv_eq_zero_of_pos_of_lt_one harg hlt
  simp [goldfeldPositiveLineKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem goldfeldPositiveLineKernel_eq_zero_of_lt_neg_log_two
    (alpha : ℝ) {u : ℝ} (hu : u < -Real.log 2) :
    goldfeldPositiveLineKernel alpha u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlog : Real.log 2 < -u := by linarith
  have hgt : 2 < Real.exp (-u) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact (Real.exp_lt_exp).2 hlog
  have hd := goldfeldPlateau_deriv_eq_zero_of_two_lt hgt
  simp [goldfeldPositiveLineKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem goldfeldPositiveLineKernel_support_subset (alpha : ℝ) :
    Function.support (goldfeldPositiveLineKernel alpha) ⊆
      Icc (-Real.log 2) 0 := by
  intro u hu
  by_contra hnot
  have hcases : u < -Real.log 2 ∨ 0 < u := by
    by_cases hleft : u < -Real.log 2
    · exact Or.inl hleft
    · have hleft' : -Real.log 2 ≤ u := le_of_not_gt hleft
      by_cases hright : 0 < u
      · exact Or.inr hright
      · exact False.elim (hnot ⟨hleft', le_of_not_gt hright⟩)
  rcases hcases with hleft | hright
  · exact hu (goldfeldPositiveLineKernel_eq_zero_of_lt_neg_log_two alpha hleft)
  · exact hu (goldfeldPositiveLineKernel_eq_zero_of_pos alpha hright)

private theorem goldfeldPositiveLineKernel_hasCompactSupport (alpha : ℝ) :
    HasCompactSupport (goldfeldPositiveLineKernel alpha) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Icc (-Real.log 2) 0) isCompact_Icc
  exact goldfeldPositiveLineKernel_support_subset alpha

private noncomputable def goldfeldPositiveLineKernelSchwartz
    (alpha : ℝ) : 𝓢(ℝ, ℂ) :=
  (goldfeldPositiveLineKernel_hasCompactSupport alpha).toSchwartzMap
    (goldfeldPositiveLineKernel_contDiff alpha)

private theorem goldfeldDerivativeMellin_on_positiveLine
    (alpha t : ℝ) :
    goldfeldDerivativeMellin ((alpha : ℂ) + t * I) =
      𝓕 (goldfeldPositiveLineKernelSchwartz alpha) (t / (2 * π)) := by
  calc
    goldfeldDerivativeMellin ((alpha : ℂ) + t * I) =
        mellin goldfeldMellinDerivativeWeight ((alpha : ℂ) + t * I) :=
      goldfeldDerivativeMellin_eq_weight _
    _ = 𝓕 (fun u : ℝ =>
        Real.exp (-((alpha : ℂ) + t * I).re * u) •
          goldfeldMellinDerivativeWeight (Real.exp (-u)))
        (((alpha : ℂ) + t * I).im / (2 * π)) :=
      mellin_eq_fourier goldfeldMellinDerivativeWeight
    _ = 𝓕 (goldfeldPositiveLineKernelSchwartz alpha) (t / (2 * π)) := by
      norm_num
      rw [SchwartzMap.fourier_coe]
      apply congrArg (fun f : ℝ → ℂ => 𝓕 f (t / (2 * π)))
      funext u
      simp [goldfeldPositiveLineKernelSchwartz, goldfeldPositiveLineKernel]

/-- The raw Goldfeld Mellin transform is integrable on every positive
vertical line. -/
theorem goldfeldRawMellin_verticalIntegrable
    {alpha : ℝ} (halpha : 0 < alpha) :
    VerticalIntegrable goldfeldRawMellin alpha := by
  let fourierLine : ℝ → ℂ := fun t =>
    𝓕 (goldfeldPositiveLineKernelSchwartz alpha) (t / (2 * π))
  let z : ℝ → ℂ := fun t => (alpha : ℂ) + t * I
  let invFactor : ℝ → ℂ := fun t => -(z t)⁻¹
  have hfourier : Integrable fourierLine := by
    have h := (𝓕 (goldfeldPositiveLineKernelSchwartz alpha)).integrable
      |>.comp_mul_right'
        (show (2 * π : ℝ)⁻¹ ≠ 0 by positivity)
    simpa [fourierLine, div_eq_mul_inv] using h
  have hzContinuous : Continuous z := by
    fun_prop
  have hzNe (t : ℝ) : z t ≠ 0 := by
    intro ht
    have hre := congrArg Complex.re ht
    simp [z] at hre
    exact halpha.ne' hre
  have hinvContinuous : Continuous invFactor := by
    exact (hzContinuous.inv₀ hzNe).neg
  have hzNorm (t : ℝ) : alpha ≤ ‖z t‖ := by
    have h := Complex.abs_re_le_norm (z t)
    simpa [z, abs_of_pos halpha] using h
  have hinvBound : ∀ᵐ t : ℝ, ‖invFactor t‖ ≤ alpha⁻¹ :=
    ae_of_all _ fun t => by
      change ‖-(z t)⁻¹‖ ≤ alpha⁻¹
      rw [norm_neg, norm_inv]
      exact (inv_le_inv₀ (halpha.trans_le (hzNorm t)) halpha).2 (hzNorm t)
  have hproduct : Integrable fun t => fourierLine t * invFactor t :=
    hfourier.mul_bdd hinvContinuous.aestronglyMeasurable hinvBound
  rw [VerticalIntegrable]
  refine hproduct.congr (ae_of_all _ fun t => ?_)
  have hraw : goldfeldRawMellin (z t) = fourierLine t * invFactor t := by
    rw [← goldfeldMellinCandidate_eq_raw (by simp [z, halpha])]
    rw [goldfeldMellinCandidate,
      goldfeldDerivativeMellin_on_positiveLine alpha t]
    simp only [fourierLine, invFactor, div_eq_mul_inv]
    ring
  simpa [z] using hraw.symm

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldSmoothedSum.lean` -/

section

/-!
# Goldfeld's smoothed four-factor sum

This file specializes smooth Mellin inversion to the shifted four-factor
coefficient in the proof of Koukoulopoulos Theorem 12.9.  It
defines the source integral `I_alpha` with the continued Mellin transform and
proves the exact initial identity `S = I_2`.

Semantic review: `SEM-553`.
-/

noncomputable section

open Complex MeasureTheory

namespace BoundedGaps.Maynard

private instance goldfeldSmoothedLcmNeZero
    {q1 q : ℕ} [NeZero q1] [NeZero q] : NeZero (Nat.lcm q1 q) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩

/-- The four L-functions in Goldfeld's auxiliary Dirichlet series. -/
noncomputable def goldfeldFourFactorLFunction
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  riemannZeta s * DirichletCharacter.LFunction chi1 s *
    DirichletCharacter.LFunction chi s *
      DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) s

/-- The coefficient `f(n) / n^beta`, with the zero index explicitly
totalized as zero by `LSeries.term`. -/
noncomputable def goldfeldBetaCoefficient
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta : ℝ) (n : ℕ) : ℂ :=
  LSeries.term (goldfeldCoefficient chi1 chi) (beta : ℂ) n

private theorem goldfeldBetaCoefficient_term
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (goldfeldBetaCoefficient chi1 chi beta) s n =
      LSeries.term (goldfeldCoefficient chi1 chi)
        (s + (beta : ℂ)) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [goldfeldBetaCoefficient, LSeries.term_of_ne_zero hn]
    rw [Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
    field_simp

/-- The shifted coefficient series is the four-factor product wherever the
original series converges absolutely. -/
theorem goldfeldBetaCoefficient_LSeriesHasSum
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta : ℝ) {s : ℂ}
    (hs : 1 < (s + (beta : ℂ)).re) :
    LSeriesHasSum (goldfeldBetaCoefficient chi1 chi beta) s
      (goldfeldFourFactorLFunction chi1 chi (s + (beta : ℂ))) := by
  have h := goldfeldCoefficient_LSeriesHasSum chi1 chi hs
  change HasSum (LSeries.term (goldfeldBetaCoefficient chi1 chi beta) s) _
  simpa [goldfeldFourFactorLFunction] using
    h.congr_fun (goldfeldBetaCoefficient_term chi1 chi beta s)

/-- The source auxiliary sum `S`.  When `x > 0`, the `tsum` is finite in
effect because the plateau vanishes from `2` onward. -/
noncomputable def goldfeldSmoothedSum
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) : ℂ :=
  ∑' n : ℕ,
    goldfeldBetaCoefficient chi1 chi beta n *
      (goldfeldPlateau ((n : ℝ) / x) : ℂ)

/-- The continued integrand used before and after the Goldfeld contour
displacement. -/
noncomputable def goldfeldContourIntegrand
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) (s : ℂ) : ℂ :=
  goldfeldFourFactorLFunction chi1 chi (s + (beta : ℂ)) *
    goldfeldMellinContinuationData.Phi s * (x : ℂ) ^ s

/-- The source integral `I_alpha`, parameterized upward by the real line. -/
noncomputable def goldfeldVerticalIntegral
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x alpha : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ t : ℝ,
      goldfeldContourIntegrand chi1 chi beta x
        ((alpha : ℂ) + t * I)

/-- Exercise 7.2(d) specialized exactly as in Theorem 12.9: `S = I_2`. -/
theorem goldfeldSmoothedSum_eq_verticalIntegral_two
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : -1 < beta) (hx : 1 ≤ x) :
    goldfeldSmoothedSum chi1 chi beta x =
      goldfeldVerticalIntegral chi1 chi beta x 2 := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hsum : LSeriesSummable
      (goldfeldBetaCoefficient chi1 chi beta) (2 : ℂ) := by
    apply (goldfeldBetaCoefficient_LSeriesHasSum
      chi1 chi beta (s := (2 : ℂ)) ?_).LSeriesSummable
    norm_num
    linarith
  have hinversion := smoothMellinLSeriesInversion
    (goldfeldBetaCoefficient chi1 chi beta) (by simp [goldfeldBetaCoefficient])
    (fun y : ℝ => (goldfeldPlateau y : ℂ))
    (alpha := 2) (x := x) (by norm_num) hxpos hsum
    (goldfeldRawMellin_convergent (by norm_num))
    (goldfeldRawMellin_verticalIntegrable (by norm_num))
    (Complex.continuous_ofReal.comp goldfeldPlateau_contDiff.continuous)
  rw [goldfeldSmoothedSum, goldfeldVerticalIntegral]
  calc
    (∑' n : ℕ,
        goldfeldBetaCoefficient chi1 chi beta n *
          (goldfeldPlateau ((n : ℝ) / x) : ℂ)) =
        (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
          ∫ t : ℝ,
            LSeries (goldfeldBetaCoefficient chi1 chi beta)
                ((2 : ℂ) + t * I) *
              goldfeldRawMellin ((2 : ℂ) + t * I) *
              (x : ℂ) ^ ((2 : ℂ) + t * I) := hinversion
    _ = (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
          ∫ t : ℝ,
            goldfeldContourIntegrand chi1 chi beta x
              ((2 : ℂ) + t * I) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      have hs : 1 < (((2 : ℂ) + t * I) + (beta : ℂ)).re := by
        norm_num
        linarith
      have hseries := (goldfeldBetaCoefficient_LSeriesHasSum
        chi1 chi beta (s := (2 : ℂ) + t * I) hs).LSeries_eq
      have hphi := goldfeldMellinContinuationData.agrees_on_right
        (s := (2 : ℂ) + t * I) (by norm_num)
      rw [hseries, ← hphi]
      rfl

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/FarRightLFunctionCenter.lean` -/

section

/-! # Far-right Dirichlet L-function center bound

The proofs of `KoukoulopoulosDistributionPrimesPrelim2022`, Lemma 8.2
(printed p. 91) and Lemma 11.4 (printed p. 114), use a uniform reciprocal
bound at the far-right center `2+it`. Semantic review: `SEM-473`.
-/

open Complex LSeries
open scoped LSeries.notation ArithmeticFunction.Moebius

namespace BoundedGaps.Maynard

private lemma norm_character_mul_moebius_le_one
    {q : ℕ} (chi : DirichletCharacter ℂ q) (n : ℕ) :
    ‖chi n * (ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  rw [norm_mul]
  calc
    ‖chi n‖ * ‖(ArithmeticFunction.moebius n : ℂ)‖
        ≤ 1 * ‖(ArithmeticFunction.moebius n : ℂ)‖ :=
      mul_le_mul_of_nonneg_right (chi.norm_le_one n) (norm_nonneg _)
    _ ≤ 1 * 1 := by
      gcongr
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ = 1 := one_mul 1

private lemma norm_character_moebius_LSeries_le_eight_thirds
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ) :
    ‖L (fun n => chi n * (ArithmeticFunction.moebius n : ℂ))
        (2 + I * t)‖ ≤ (8 : ℝ) / 3 := by
  let s : ℂ := 2 + I * t
  let a : ℕ → ℂ := fun n => chi n * (ArithmeticFunction.moebius n : ℂ)
  have hs : s.re = 2 := by simp [s]
  have ha : LSeriesSummable a s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    · intro n _
      exact norm_character_mul_moebius_le_one chi n
    · simp [hs]
  calc
    ‖L a s‖ ≤ ∑' n, ‖term a s n‖ := norm_tsum_le_tsum_norm ha.norm
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
      apply Summable.tsum_le_tsum
      · intro n
        rw [norm_term_eq, hs]
        split_ifs with hn
        · simp [hn]
        · change ‖a n‖ / (n : ℝ) ^ (2 : ℝ) ≤ 1 / (n : ℝ) ^ 2
          rw [Real.rpow_two]
          exact div_le_div_of_nonneg_right
            (by simpa [a] using norm_character_mul_moebius_le_one chi n)
            (sq_nonneg (n : ℝ))
      · exact ha.norm
      · exact hasSum_zeta_two.summable
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
    _ ≤ (8 : ℝ) / 3 := by nlinarith [Real.pi_le_four, Real.pi_pos]

/-- The reciprocal of every positive-modulus Dirichlet L-function is uniformly
bounded on the vertical line with real part two. -/
theorem norm_inv_LFunction_two_add_mul_I_le_three
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (t : ℝ) :
    ‖(DirichletCharacter.LFunction chi ((2 : ℂ) + t * I))⁻¹‖ ≤ 3 := by
  let s : ℂ := 2 + t * I
  let a : ℕ → ℂ := fun n => chi n * (ArithmeticFunction.moebius n : ℂ)
  have hs : 1 < s.re := by simp [s]
  have hprod : L (chi ·) s * L a s = 1 := by
    have ha_fun : a = (fun n : ℕ => chi n) *
        (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) := by
      funext n
      rfl
    rw [ha_fun]
    exact DirichletCharacter.LSeries.mul_mu_eq_one chi hs
  rw [DirichletCharacter.LFunction_eq_LSeries chi hs,
    inv_eq_of_mul_eq_one_right hprod]
  have ha : ‖L a s‖ ≤ (8 : ℝ) / 3 := by
    simpa [a, s, mul_comm] using
      norm_character_moebius_LSeries_le_eight_thirds chi t
  exact ha.trans (by norm_num)

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/RiemannZetaAbel.lean` -/

section

/-!
# An Abel representation for regularized zeta

Euler--Maclaurin summation represents zeta on the positive half-plane by a
pole term and an absolutely convergent fractional-part integral. Multiplying
away the pole gives an analytic identity for Mathlib's entire
`riemannZeta₁`.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 14--15,
Theorem 1.10, and printed p. 55, equation (5.7). Semantic review: `SEM-482`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Asymptotics Complex Filter MeasureTheory Set
open scoped Topology

private noncomputable def zetaFractionalTail (u : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) u

private noncomputable def zetaFractionalMellin (s : ℂ) : ℂ :=
  mellin zetaFractionalTail (-s)

private lemma measurable_zetaFractionalTail :
    Measurable zetaFractionalTail := by
  exact (Complex.continuous_ofReal.measurable.comp measurable_fract).indicator
    measurableSet_Ioi

private lemma norm_zetaFractionalTail_le_one (u : ℝ) :
    ‖zetaFractionalTail u‖ ≤ 1 := by
  by_cases hu : 1 < u
  · simpa [zetaFractionalTail, hu, Complex.norm_real, Real.norm_eq_abs,
      Int.abs_fract] using
      (Int.fract_lt_one u).le
  · simp [zetaFractionalTail, hu]

private lemma locallyIntegrable_zetaFractionalTail :
    LocallyIntegrable zetaFractionalTail := by
  refine (locallyIntegrable_const (1 : ℂ)).mono
    measurable_zetaFractionalTail.aestronglyMeasurable ?_
  filter_upwards with u
  simpa using norm_zetaFractionalTail_le_one u

private lemma zetaFractionalTail_isBigO_atTop :
    zetaFractionalTail =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  refine isBigO_iff.mpr ⟨1, Eventually.of_forall fun u => ?_⟩
  simpa using norm_zetaFractionalTail_le_one u

private lemma zetaFractionalTail_isBigO_nhdsGT_zero (b : ℝ) :
    zetaFractionalTail =O[𝓝[>] 0] (fun u : ℝ => u ^ (-b)) := by
  have hsmall : ∀ᶠ u : ℝ in 𝓝[>] 0, u < 1 :=
    Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [hsmall] with u hu
  simp [zetaFractionalTail, not_lt.mpr hu.le]

private lemma mellinConvergent_zetaFractionalTail
    {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent zetaFractionalTail (-s) := by
  refine mellinConvergent_of_isBigO_rpow
    (a := 0) (b := (-s).re - 1)
    (locallyIntegrable_zetaFractionalTail.locallyIntegrableOn (Ioi 0))
    (by simpa using zetaFractionalTail_isBigO_atTop) ?_
    (zetaFractionalTail_isBigO_nhdsGT_zero ((-s).re - 1)) ?_
  · simpa using hs
  · linarith

private lemma differentiableAt_zetaFractionalMellin
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ zetaFractionalMellin s := by
  have hMellin : DifferentiableAt ℂ (mellin zetaFractionalTail) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow
      (a := 0) (b := (-s).re - 1)
      (locallyIntegrable_zetaFractionalTail.locallyIntegrableOn (Ioi 0))
      (by simpa using zetaFractionalTail_isBigO_atTop) ?_
      (zetaFractionalTail_isBigO_nhdsGT_zero ((-s).re - 1)) ?_
    · simpa using hs
    · linarith
  exact hMellin.comp s differentiableAt_id.neg

private lemma zetaFractionalMellin_eq_integral (s : ℂ) :
    zetaFractionalMellin s =
      ∫ u in Ioi (1 : ℝ),
        (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1))) := by
  rw [zetaFractionalMellin, mellin]
  simp only [smul_eq_mul]
  calc
    (∫ u : ℝ in Ioi 0,
        (u : ℂ) ^ (-s - 1) * zetaFractionalTail u) =
        ∫ u : ℝ in Ioi 0, (Ioi (1 : ℝ)).indicator
          (fun x : ℝ =>
            (x : ℂ) ^ (-s - 1) * ((Int.fract x : ℝ) : ℂ)) u := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      by_cases hu : 1 < u <;> simp [zetaFractionalTail, hu]
    _ = ∫ u : ℝ in Ioi (0 : ℝ) ∩ Ioi 1,
        (u : ℂ) ^ (-s - 1) * ((Int.fract u : ℝ) : ℂ) := by
      rw [setIntegral_indicator measurableSet_Ioi]
    _ = ∫ u : ℝ in Ioi 1,
        (u : ℂ) ^ (-s - 1) * ((Int.fract u : ℝ) : ℂ) := by
      rw [Ioi_inter_Ioi, max_eq_right zero_le_one]
    _ = ∫ u : ℝ in Ioi 1,
        ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]

private lemma norm_zetaFractionalMellin_le
    {s : ℂ} (hs : 0 < s.re) :
    ‖zetaFractionalMellin s‖ ≤ 1 / s.re := by
  rw [zetaFractionalMellin_eq_integral]
  have hmajorant : IntegrableOn
      (fun u : ℝ => u ^ (-(s.re + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hconvergent := mellinConvergent_zetaFractionalTail hs
  rw [MellinConvergent] at hconvergent
  have hrestricted :=
    hconvergent.mono_set (Ioi_subset_Ioi zero_le_one)
  have hintegrable : IntegrableOn
      (fun u : ℝ =>
        ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1)))
      (Ioi 1) := by
    refine hrestricted.congr_fun ?_ measurableSet_Ioi
    intro u hu
    simp only [smul_eq_mul]
    rw [zetaFractionalTail, indicator_of_mem hu, mul_comm]
    congr 1
    ring_nf
  have hbound : ∀ᵐ (u : ℝ) ∂volume.restrict (Ioi 1),
      ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1))‖ ≤
        u ^ (-(s.re + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hu)]
    simp only [neg_re, add_re, one_re, Complex.norm_real, Real.norm_eq_abs,
      Int.abs_fract]
    exact mul_le_of_le_one_left
      (Real.rpow_nonneg (zero_lt_one.trans hu).le _)
      (Int.fract_lt_one u).le
  calc
    ‖∫ u : ℝ in Ioi 1,
        ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1))‖ ≤
        ∫ u : ℝ in Ioi 1,
          ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in Ioi 1, u ^ (-(s.re + 1)) :=
      setIntegral_mono_ae_restrict hintegrable.norm hmajorant hbound
    _ = 1 / s.re := by
      rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
      field_simp [hs.ne']
      ring

private lemma unit_partialSums_isBigO :
    (fun n : ℕ => ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  simpa [Nat.card_Icc] using
    (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)

private lemma riemannZeta_eq_pole_sub_mellin
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * zetaFractionalMellin s := by
  have hseries :
      riemannZeta s =
        s * ∫ u : ℝ in Ioi 1,
          (∑ k ∈ Finset.Icc 1 ⌊u⌋₊, (1 : ℂ)) *
            (u : ℂ) ^ (-(s + 1)) := by
    have h := LSeries_eq_mul_integral_of_nonneg
      (fun _ : ℕ => (1 : ℝ)) (r := 1) zero_le_one hs
      unit_partialSums_isBigO (fun _ => zero_le_one)
    calc
      riemannZeta s = LSeries (1 : ℕ → ℂ) s :=
        (LSeries_one_eq_riemannZeta hs).symm
      _ = LSeries (fun _ : ℕ => ((1 : ℝ) : ℂ)) s := by
        apply LSeries_congr
        simp
      _ = s * ∫ u : ℝ in Ioi 1,
          (∑ k ∈ Finset.Icc 1 ⌊u⌋₊, (1 : ℂ)) *
            (u : ℂ) ^ (-(s + 1)) := by simpa using h
  have hfloor :
      (∫ u : ℝ in Ioi 1,
          (∑ k ∈ Finset.Icc 1 ⌊u⌋₊, (1 : ℂ)) *
            (u : ℂ) ^ (-(s + 1))) =
        ∫ u : ℝ in Ioi 1,
          ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) *
            (u : ℂ) ^ (-(s + 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 ≤ u := (zero_lt_one.trans hu).le
    have hfloorReal : (⌊u⌋₊ : ℝ) = u - Int.fract u := by
      rw [natCast_floor_eq_intCast_floor hu0]
      linarith [Int.floor_add_fract u]
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc,
      Nat.add_sub_cancel, mul_one]
    rw [← Complex.ofReal_natCast, hfloorReal, Complex.ofReal_sub]
  rw [hfloor] at hseries
  have hpure : IntegrableOn
      (fun u : ℝ => (u : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one
  have hfrac : IntegrableOn
      (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) *
        (u : ℂ) ^ (-(s + 1))) (Ioi 1) := by
    have hconv := mellinConvergent_zetaFractionalTail (zero_lt_one.trans hs)
    rw [MellinConvergent] at hconv
    have hrestrict := hconv.mono_set (Ioi_subset_Ioi zero_le_one)
    refine hrestrict.congr_fun ?_ measurableSet_Ioi
    intro u hu
    simp only [smul_eq_mul]
    rw [zetaFractionalTail, indicator_of_mem hu, mul_comm]
    congr 1
    ring_nf
  have hpoint : ∀ u ∈ Ioi (1 : ℝ),
      ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) *
          (u : ℂ) ^ (-(s + 1)) =
        (u : ℂ) ^ (-s) -
          ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1)) := by
    intro u hu
    rw [sub_mul]
    congr 2
    have hu0 : (u : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hu).ne'
    calc
      (u : ℂ) * (u : ℂ) ^ (-(s + 1)) =
          (u : ℂ) ^ 1 * (u : ℂ) ^ (-(s + 1)) := by rw [cpow_one]
      _ = (u : ℂ) ^ (1 + -(s + 1)) := (cpow_add _ _ hu0).symm
      _ = (u : ℂ) ^ (-s) := by congr 1; ring
  have hintegral :
      (∫ u : ℝ in Ioi 1,
          ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) *
            (u : ℂ) ^ (-(s + 1))) =
        (∫ u : ℝ in Ioi 1, (u : ℂ) ^ (-s)) -
          ∫ u : ℝ in Ioi 1,
            ((Int.fract u : ℝ) : ℂ) *
              (u : ℂ) ^ (-(s + 1)) := by
    rw [← integral_sub hpure hfrac]
    exact setIntegral_congr_fun measurableSet_Ioi hpoint
  rw [hintegral,
    integral_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one,
    Complex.ofReal_one, one_cpow, ← zetaFractionalMellin_eq_integral] at hseries
  have hpole : -1 / (-s + 1) = 1 / (s - 1) := by
    rw [show -s + 1 = -(s - 1) by ring, div_neg]
    ring
  calc
    riemannZeta s = s * (-1 / (-s + 1) - zetaFractionalMellin s) := hseries
    _ = s / (s - 1) - s * zetaFractionalMellin s := by
      rw [hpole]
      ring

/-- The regularized zeta function represented by the fractional-part Abel
integral throughout the positive half-plane. -/
theorem riemannZeta₁_eq_abelIntegral
    (s : ℂ) (hs : 0 < s.re) :
    riemannZeta₁ s =
      s - s * (s - 1) *
        ∫ u in Set.Ioi (1 : ℝ),
          (((Int.fract u : ℝ) : ℂ) *
            (u : ℂ) ^ (-(s + 1))) := by
  let U : Set ℂ := {z | 0 < z.re}
  let rhs : ℂ → ℂ := fun z =>
    z - z * (z - 1) * zetaFractionalMellin z
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hleft : AnalyticOnNhd ℂ riemannZeta₁ U :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hUopen
  have hright : AnalyticOnNhd ℂ rhs U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    exact (differentiableAt_id.sub
      ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
        (differentiableAt_zetaFractionalMellin hz))).differentiableWithinAt
  have heq : Set.EqOn riemannZeta₁ rhs U := by
    refine hleft.eqOn_of_preconnected_of_eventuallyEq hright
      (convex_halfSpace_re_gt 0).isPreconnected
      (show (2 : ℂ) ∈ U by simp [U]) ?_
    refine eventually_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show 1 < (2 : ℂ).re by norm_num)) ?_
    intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      norm_num at hz
    have hfactor : riemannZeta₁ z = (z - 1) * riemannZeta z := by
      rw [riemannZeta_eq_inv_sub_mul hz1]
      field_simp
    rw [hfactor, riemannZeta_eq_pole_sub_mellin hz]
    dsimp [rhs]
    field_simp
  rw [heq hs]
  dsimp [rhs]
  rw [zetaFractionalMellin_eq_integral]

/-- The direct norm consequence of the regularized Abel representation. -/
theorem norm_riemannZeta₁_le_abel
    (s : ℂ) (hs : 0 < s.re) :
    ‖riemannZeta₁ s‖ ≤
      ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re := by
  rw [riemannZeta₁_eq_abelIntegral s hs,
    ← zetaFractionalMellin_eq_integral]
  calc
    ‖s - s * (s - 1) * zetaFractionalMellin s‖ ≤
        ‖s‖ + ‖s * (s - 1) * zetaFractionalMellin s‖ := norm_sub_le _ _
    _ = ‖s‖ + ‖s‖ * ‖s - 1‖ * ‖zetaFractionalMellin s‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ * (1 / s.re) := by
      gcongr
      exact norm_zetaFractionalMellin_le hs
    _ = ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re := by ring

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/RiemannZetaRadiusFour.lean` -/

section

/-!
# Regularized zeta growth on radius-four spheres

The fixed-disk argument for the principal pole needs only the strip
`1 <= re(s) <= 2`. We therefore use inner radius one, selected radius two,
and outer radius four around `2+it`. The right half-plane is controlled by
the Abel representation, while the left half-plane uses the completed-zeta
functional equation and the audited Gamma-factor quotient.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 55,
equation (5.7), printed p. 61, equations (6.1)--(6.2), and printed
pp. 89--91, Lemmas 8.5--8.6. Semantic review: `SEM-482`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex Metric Set

private lemma even_one_mod_one :
    (1 : DirichletCharacter ℂ 1).Even := by
  rw [DirichletCharacter.Even]
  exact map_one _

/-- The exact regularized-zeta reflection identity on the left half-plane
away from zero. -/
theorem riemannZeta₁_eq_reflection_of_re_le
    (s : ℂ) (hs0 : s ≠ 0) (hs : s.re ≤ (1 / 2 : ℝ)) :
    riemannZeta₁ s =
      (1 - s) / s * riemannZeta₁ (1 - s) *
        (DirichletCharacter.gammaFactor
            (1 : DirichletCharacter ℂ 1) (1 - s) /
          DirichletCharacter.gammaFactor
            (1 : DirichletCharacter ℂ 1) s) := by
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hreflect0 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hGammaReflect : Gammaℝ (1 - s) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hGammaR :
      riemannZeta₁ s =
        (1 - s) / s * riemannZeta₁ (1 - s) *
          (Gammaℝ (1 - s) / Gammaℝ s) := by
    by_cases hGamma : Gammaℝ s = 0
    · obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hGamma
      have hn0 : n ≠ 0 := by
        intro hn0
        subst n
        simp at hn
        exact hs0 hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      have hzeta : riemannZeta (-(2 * ((k + 1 : ℕ) : ℂ))) = 0 := by
        simpa [Nat.cast_add, Nat.cast_one] using
          riemannZeta_neg_two_mul_nat_add_one k
      have harg1 : -(2 * ((k + 1 : ℕ) : ℂ)) ≠ 1 := by
        intro h
        have hreal := congrArg Complex.re h
        norm_num at hreal
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      have hsub : -(2 * ((k + 1 : ℕ) : ℂ)) - 1 ≠ 0 :=
        sub_ne_zero.mpr harg1
      have hfactor := riemannZeta_eq_inv_sub_mul harg1
      rw [hzeta] at hfactor
      have hinv : (-(2 * ((k + 1 : ℕ) : ℂ)) - 1)⁻¹ ≠ 0 :=
        inv_ne_zero hsub
      have hzeta1 : riemannZeta₁ (-(2 * ((k + 1 : ℕ) : ℂ))) = 0 :=
        (mul_eq_zero.mp hfactor.symm).resolve_left hinv
      have hden : Gammaℝ (-(2 * ((k + 1 : ℕ) : ℂ))) = 0 := by
        simpa [hn] using hGamma
      rw [hn, hzeta1, hden]
      simp
    · have hreflected :
          completedRiemannZeta (1 - s) =
            riemannZeta (1 - s) * Gammaℝ (1 - s) := by
        symm
        exact (eq_div_iff hGammaReflect).mp
          (riemannZeta_def_of_ne_zero hreflect0)
      have hzeta :
          riemannZeta s =
            riemannZeta (1 - s) * Gammaℝ (1 - s) / Gammaℝ s := by
        rw [riemannZeta_def_of_ne_zero hs0,
          ← completedRiemannZeta_one_sub s, hreflected]
      have hreg : riemannZeta₁ s = (s - 1) * riemannZeta s := by
        rw [riemannZeta_eq_inv_sub_mul hs1]
        field_simp
      have hreflect1 : 1 - s ≠ 1 := by
        intro h
        apply hs0
        linear_combination -h
      have hregReflect :
          riemannZeta₁ (1 - s) =
            ((1 - s) - 1) * riemannZeta (1 - s) := by
        rw [riemannZeta_eq_inv_sub_mul hreflect1]
        field_simp
      rw [hreg, hzeta, hregReflect]
      field_simp [hs0, hGamma]
      ring
  rw [even_one_mod_one.gammaFactor_def, even_one_mod_one.gammaFactor_def]
  exact hGammaR

private lemma radiusFourSphere_geometry
    (t : ℝ) (z : ℂ)
    (hz : z ∈ sphere ((2 : ℂ) + t * I) 4) :
    -(2 : ℝ) ≤ z.re ∧ z.re ≤ 6 ∧
      |z.im| + 2 ≤ 3 * (|t| + 2) ∧
        ‖z‖ ≤ 3 * (|t| + 2) := by
  have hdist : ‖z - ((2 : ℂ) + t * I)‖ = 4 := by
    simpa [mem_sphere, Complex.dist_eq] using hz
  have hre : |z.re - 2| ≤ 4 := by
    calc
      |z.re - 2| = |(z - ((2 : ℂ) + t * I)).re| := by simp
      _ ≤ ‖z - ((2 : ℂ) + t * I)‖ := Complex.abs_re_le_norm _
      _ = 4 := hdist
  have him : |z.im - t| ≤ 4 := by
    calc
      |z.im - t| = |(z - ((2 : ℂ) + t * I)).im| := by simp
      _ ≤ ‖z - ((2 : ℂ) + t * I)‖ := Complex.abs_im_le_norm _
      _ = 4 := hdist
  have hzIm : |z.im| ≤ |t| + 4 := by
    calc
      |z.im| = |(z.im - t) + t| := by rw [sub_add_cancel]
      _ ≤ |z.im - t| + |t| := abs_add_le _ _
      _ ≤ 4 + |t| := by linarith
      _ = |t| + 4 := by ring
  have hcenter : ‖(2 : ℂ) + t * I‖ ≤ 2 + |t| := by
    calc
      ‖(2 : ℂ) + t * I‖ ≤ ‖(2 : ℂ)‖ + ‖t * I‖ := norm_add_le _ _
      _ = 2 + |t| := by simp [Real.norm_eq_abs]
  have hnorm : ‖z‖ ≤ |t| + 6 := by
    calc
      ‖z‖ = ‖(z - ((2 : ℂ) + t * I)) + ((2 : ℂ) + t * I)‖ := by ring_nf
      _ ≤ ‖z - ((2 : ℂ) + t * I)‖ + ‖(2 : ℂ) + t * I‖ :=
        norm_add_le _ _
      _ ≤ 4 + (2 + |t|) := add_le_add (le_of_eq hdist) hcenter
      _ = |t| + 6 := by ring
  constructor
  · rw [abs_le] at hre
    linarith
  constructor
  · rw [abs_le] at hre
    linarith
  constructor
  · linarith [abs_nonneg t]
  · linarith [abs_nonneg t]

private lemma exists_pos_norm_riemannZeta₁_closedBall_one_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ closedBall (0 : ℂ) 1,
      ‖riemannZeta₁ z‖ ≤ C := by
  have hball : IsCompact (closedBall (0 : ℂ) 1) :=
    isCompact_closedBall (0 : ℂ) 1
  obtain ⟨C, hC⟩ := hball.exists_bound_of_continuousOn
    differentiable_riemannZeta₁.continuous.continuousOn
  refine ⟨max C 0 + 1, by linarith [le_max_right C 0], ?_⟩
  intro z hz
  exact (hC z hz).trans (by linarith [le_max_left C 0])

private lemma natCast_le_two_pow (n : ℕ) : (n : ℝ) ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.cast_succ, pow_succ]
      have hone : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith

/-- Regularized zeta has one absolute polynomial bound on the radius-four
spheres used by the principal fixed-disk argument. -/
theorem exists_nat_norm_riemannZeta₁_radiusFourSphere_le :
    ∃ E : ℕ, 1 ≤ E ∧
      ∀ (t : ℝ) (z : ℂ),
        z ∈ sphere ((2 : ℂ) + t * I) 4 →
          ‖riemannZeta₁ z‖ ≤ (|t| + 2) ^ E := by
  obtain ⟨Ccompact, hCcompact, hcompact⟩ :=
    exists_pos_norm_riemannZeta₁_closedBall_one_le
  obtain ⟨Cgamma, hCgamma, hgamma⟩ :=
    exists_norm_gammaFactor_ratio_fixedStrip_le
  let K : ℝ := max Ccompact (4 * Cgamma * 3 ^ 11)
  obtain ⟨n : ℕ, hn⟩ := exists_nat_ge K
  refine ⟨n + 19, by omega, ?_⟩
  intro t z hz
  obtain ⟨hzlo, hzhi, hzheight, hznorm⟩ :=
    radiusFourSphere_geometry t z hz
  let T : ℝ := |t| + 2
  have hT2 : (2 : ℝ) ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hT1 : (1 : ℝ) ≤ T := one_le_two.trans hT2
  have hT0 : (0 : ℝ) ≤ T := zero_le_one.trans hT1
  have hzsub : ‖z - 1‖ ≤ 4 * T := by
    calc
      ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 * T + 1 := add_le_add (by simpa [T] using hznorm) (by norm_num)
      _ ≤ 4 * T := by linarith
  have hKpow : K ≤ T ^ n := by
    calc
      K ≤ (n : ℝ) := hn
      _ ≤ 2 ^ n := natCast_le_two_pow n
      _ ≤ T ^ n := pow_le_pow_left₀ (by norm_num) hT2 n
  by_cases hright : (1 / 2 : ℝ) ≤ z.re
  · have habel := norm_riemannZeta₁_le_abel z (by linarith)
    have hrightBound : ‖riemannZeta₁ z‖ ≤ T ^ 7 := by
      calc
        ‖riemannZeta₁ z‖ ≤ ‖z‖ + ‖z‖ * ‖z - 1‖ / z.re := habel
        _ ≤ 3 * T + (3 * T) * (4 * T) / (1 / 2 : ℝ) := by
          gcongr
        _ = 3 * T + 24 * T ^ 2 := by ring
        _ ≤ T ^ 7 := by
          have hT5 : (32 : ℝ) ≤ T ^ 5 := by
            have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hT2 5
            norm_num at h
            exact h
          have hT7 : 32 * T ^ 2 ≤ T ^ 7 := by
            calc
              32 * T ^ 2 ≤ T ^ 5 * T ^ 2 :=
                mul_le_mul_of_nonneg_right hT5 (sq_nonneg T)
              _ = T ^ 7 := by ring
          nlinarith [sq_nonneg T]
    exact hrightBound.trans (pow_le_pow_right₀ hT1 (by omega))
  · have hzleft : z.re ≤ (1 / 2 : ℝ) := le_of_not_ge hright
    by_cases hzsmall : ‖z‖ ≤ 1
    · have hzball : z ∈ closedBall (0 : ℂ) 1 := by
        simpa [mem_closedBall, dist_zero_right] using hzsmall
      have hC : Ccompact ≤ K := le_max_left _ _
      calc
        ‖riemannZeta₁ z‖ ≤ Ccompact := hcompact z hzball
        _ ≤ K := hC
        _ ≤ T ^ n := hKpow
        _ ≤ T ^ (n + 19) := pow_le_pow_right₀ hT1 (by omega)
    · have hz0 : z ≠ 0 := by
        intro h
        subst z
        simp at hzsmall
      have hreflect := riemannZeta₁_eq_reflection_of_re_le z hz0 hzleft
      have hreflectRe : (1 / 2 : ℝ) ≤ (1 - z).re := by simp; linarith
      have hreflectNorm : ‖1 - z‖ ≤ 4 * T := by
        calc
          ‖1 - z‖ = ‖z - 1‖ := by
            rw [show 1 - z = -(z - 1) by ring, norm_neg]
          _ ≤ 4 * T := hzsub
      have hreflectSub : ‖(1 - z) - 1‖ ≤ 3 * T := by
        simpa only [sub_sub_cancel_left, norm_neg] using
          (show ‖z‖ ≤ 3 * T by simpa [T] using hznorm)
      have hreflectAbel := norm_riemannZeta₁_le_abel (1 - z) (by linarith)
      have hreflectBound : ‖riemannZeta₁ (1 - z)‖ ≤ T ^ 7 := by
        calc
          ‖riemannZeta₁ (1 - z)‖ ≤
              ‖1 - z‖ + ‖1 - z‖ * ‖(1 - z) - 1‖ / (1 - z).re :=
            hreflectAbel
          _ ≤ 4 * T + (4 * T) * (3 * T) / (1 / 2 : ℝ) := by
            gcongr
          _ = 4 * T + 24 * T ^ 2 := by ring
          _ ≤ T ^ 7 := by
            have hT5 : (32 : ℝ) ≤ T ^ 5 := by
              have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hT2 5
              norm_num at h
              exact h
            have hT7 : 32 * T ^ 2 ≤ T ^ 7 := by
              calc
                32 * T ^ 2 ≤ T ^ 5 * T ^ 2 :=
                  mul_le_mul_of_nonneg_right hT5 (sq_nonneg T)
                _ = T ^ 7 := by ring
            nlinarith [sq_nonneg T]
      have hratio : ‖(1 - z) / z‖ ≤ 4 * T := by
        rw [norm_div]
        have hzOne : (1 : ℝ) ≤ ‖z‖ := le_of_not_ge hzsmall
        exact (div_le_iff₀ (norm_pos_iff.mpr hz0)).2 (by
          calc
            ‖1 - z‖ ≤ 4 * T := hreflectNorm
            _ ≤ 4 * T * ‖z‖ := by
              exact le_mul_of_one_le_right (by positivity) hzOne)
      have hgamma' := hgamma 1 (1 : DirichletCharacter ℂ 1) z
        (by linarith) hzleft
      have hgammaBound :
          ‖DirichletCharacter.gammaFactor
                (1 : DirichletCharacter ℂ 1)⁻¹ (1 - z) /
              DirichletCharacter.gammaFactor
                (1 : DirichletCharacter ℂ 1) z‖ ≤
            Cgamma * (3 * T) ^ 11 := by
        exact hgamma'.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by simpa [T] using hzheight) 11)
          hCgamma.le)
      have hinvOne : (1 : DirichletCharacter ℂ 1)⁻¹ = 1 := inv_one
      rw [hinvOne] at hgammaBound
      rw [hreflect, norm_mul, norm_mul]
      calc
        ‖(1 - z) / z‖ * ‖riemannZeta₁ (1 - z)‖ *
              ‖DirichletCharacter.gammaFactor
                  (1 : DirichletCharacter ℂ 1) (1 - z) /
                DirichletCharacter.gammaFactor
                  (1 : DirichletCharacter ℂ 1) z‖ ≤
            (4 * T) * T ^ 7 * (Cgamma * (3 * T) ^ 11) := by
          gcongr
        _ = (4 * Cgamma * 3 ^ 11) * T ^ 19 := by ring
        _ ≤ K * T ^ 19 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hT0 19)
        _ ≤ T ^ n * T ^ 19 :=
          mul_le_mul_of_nonneg_right hKpow (pow_nonneg hT0 19)
        _ = T ^ (n + 19) := by rw [pow_add]


end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/RiemannZetaClosedStripGrowth.lean` -/

section

/-!
# Riemann zeta on the Goldfeld strip

The existing radius-four estimate for the entire function `riemannZeta₁` is
extended to its enclosed disk by the maximum-modulus principle.  High
ordinate then transfers the result to ordinary zeta.

Source: Koukoulopoulos, printed pp. 66--67, Theorem 6.3.
Semantic review: `SEM-556`.
-/

namespace BoundedGaps.Maynard

open Complex Metric Set

/-- Regularized zeta has absolute polynomial growth on the closed strip
`-1 <= Re(s) <= 3`. -/
theorem exists_norm_riemannZeta₁_closedStrip_le_pow :
    ∃ E : ℕ, 1 ≤ E ∧
      ∀ z : ℂ, -(1 : ℝ) ≤ z.re → z.re ≤ 3 →
        ‖riemannZeta₁ z‖ ≤ (|z.im| + 2) ^ E := by
  obtain ⟨E, hE, hsphere⟩ :=
    exists_nat_norm_riemannZeta₁_radiusFourSphere_le
  refine ⟨E, hE, ?_⟩
  intro z hzlo hzhi
  let c : ℂ := (2 : ℂ) + z.im * I
  have hzmem : z ∈ closedBall c 4 := by
    rw [mem_closedBall, Complex.dist_eq]
    have heq : z - c = ((z.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [c]
    rw [heq, norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := ball c 4) Metric.isBounded_ball
    differentiable_riemannZeta₁.diffContOnCl
    (C := (|z.im| + 2) ^ E)
  · intro w hw
    rw [frontier_ball c (by norm_num)] at hw
    exact hsphere z.im w (by simpa [c] using hw)
  · rw [closure_ball c (by norm_num)]
    exact hzmem

/-- Away from the real-axis pole, ordinary zeta inherits the same strip
exponent as its entire regularization. -/
theorem exists_norm_riemannZeta_closedStrip_le_pow :
    ∃ E : ℕ, 1 ≤ E ∧
      ∀ z : ℂ, -(1 : ℝ) ≤ z.re → z.re ≤ 3 → 1 ≤ |z.im| →
        ‖riemannZeta z‖ ≤ (|z.im| + 2) ^ E := by
  obtain ⟨E, hE, hzetaOne⟩ :=
    exists_norm_riemannZeta₁_closedStrip_le_pow
  refine ⟨E, hE, ?_⟩
  intro z hzlo hzhi hzim
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hzim
  have hsub : (1 : ℝ) ≤ ‖z - 1‖ := by
    have him := Complex.abs_im_le_norm (z - 1)
    simp only [sub_im, one_im, sub_zero] at him
    exact hzim.trans him
  have hinv : ‖(z - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hz1)) |>.2 hsub
  rw [riemannZeta_eq_inv_sub_mul hz1, norm_mul]
  calc
    ‖(z - 1)⁻¹‖ * ‖riemannZeta₁ z‖ ≤ 1 * ‖riemannZeta₁ z‖ :=
      mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
    _ ≤ (|z.im| + 2) ^ E := by simpa using hzetaOne z hzlo hzhi

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldFourFactorClosedStrip.lean` -/

section

/-!
# Goldfeld's four-factor function on the contour strip

This file combines the ordinary-zeta and arbitrary-character growth bounds at
the original character levels.  In particular, the cross character remains
at level `lcm(q1,q)` and may be imprimitive.

Source: Koukoulopoulos, printed p. 126, proof of Theorem 12.9.
Semantic review: `SEM-556`.
-/

namespace BoundedGaps.Maynard

open Complex


/-- One absolute natural exponent controls Goldfeld's complete four-factor
function uniformly across the high-ordinate closed contour strip. -/
theorem exists_norm_goldfeldFourFactorLFunction_closedStrip_le_pow :
    ∃ A : ℕ, 57 ≤ A ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta : ℝ) (s : ℂ),
            0 ≤ beta → beta ≤ 1 →
            -(1 : ℝ) ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
            ‖goldfeldFourFactorLFunction chi1 chi
                (s + (beta : ℂ))‖ ≤
              ((q : ℝ) * (|s.im| + 2)) ^ A := by
  obtain ⟨L, hLexp, hL⟩ := exists_norm_LFunction_closedStrip_le_pow
  obtain ⟨E, hEexp, hZeta⟩ := exists_norm_riemannZeta_closedStrip_le_pow
  refine ⟨E + 4 * L, by omega, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross beta s
    hbeta0 hbeta1 hslo hshi hheight
  have hq : 1 < q := hq1.trans_le hq1q
  let w : ℂ := s + (beta : ℂ)
  let T : ℝ := |s.im| + 2
  let B : ℝ := (q : ℝ) * T
  have hwre : w.re = s.re + beta := by simp [w]
  have hwim : w.im = s.im := by simp [w]
  have hwlo : -(1 : ℝ) ≤ w.re := by rw [hwre]; linarith
  have hwhi : w.re ≤ 3 := by rw [hwre]; linarith
  have hwheight : 1 ≤ |w.im| := by simpa [hwim] using hheight
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1r : (1 : ℝ) ≤ q := one_le_two.trans hq2
  have hq0 : (0 : ℝ) ≤ q := zero_le_one.trans hq1r
  have hT3 : (3 : ℝ) ≤ T := by
    dsimp [T]
    linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) ≤ T := zero_le_one.trans hT1
  have hB1 : (1 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hq1qReal : (q1 : ℝ) ≤ q := by exact_mod_cast hq1q
  have hZetaBound : ‖riemannZeta w‖ ≤ B ^ E := by
    have hz := hZeta w hwlo hwhi hwheight
    have hTB : T ≤ B := by
      dsimp [B]
      nlinarith
    exact hz.trans (by
      simpa [T, hwim] using pow_le_pow_left₀ hT0 hTB E)
  have hchi1Bound :
      ‖DirichletCharacter.LFunction chi1 w‖ ≤ B ^ L := by
    have h := hL q1 hq1 chi1 hchi1 w hwlo hwhi
    have hbase : (q1 : ℝ) * (|w.im| + 2) ≤ B := by
      dsimp [B, T]
      rw [hwim]
      gcongr
    exact h.trans (pow_le_pow_left₀ (by positivity) hbase L)
  have hchiBound :
      ‖DirichletCharacter.LFunction chi w‖ ≤ B ^ L := by
    simpa [B, T, hwim] using hL q hq chi hchi w hwlo hwhi
  let m := Nat.lcm q1 q
  have hmpos : 0 < m := Nat.lcm_pos (NeZero.pos q1) (NeZero.pos q)
  letI : NeZero m := ⟨hmpos.ne'⟩
  have hqm : q ≤ m := Nat.le_of_dvd hmpos (Nat.dvd_lcm_right q1 q)
  have hm1 : 1 < m := hq.trans_le hqm
  have hmqq : m ≤ q1 * q :=
    Nat.le_of_dvd (Nat.mul_pos (NeZero.pos q1) (NeZero.pos q))
      (Nat.lcm_dvd_mul q1 q)
  have hmqqReal : (m : ℝ) ≤ (q : ℝ) ^ 2 := by
    calc
      (m : ℝ) ≤ ((q1 * q : ℕ) : ℝ) := by exact_mod_cast hmqq
      _ = (q1 : ℝ) * (q : ℝ) := by norm_num
      _ ≤ (q : ℝ) * (q : ℝ) :=
        mul_le_mul_of_nonneg_right hq1qReal hq0
      _ = (q : ℝ) ^ 2 := by ring
  have hmBase : (m : ℝ) * (|w.im| + 2) ≤ B ^ 2 := by
    rw [hwim]
    dsimp [B, T]
    calc
      (m : ℝ) * (|s.im| + 2) ≤
          (q : ℝ) ^ 2 * (|s.im| + 2) :=
        mul_le_mul_of_nonneg_right hmqqReal (by positivity)
      _ ≤ (q : ℝ) ^ 2 * (|s.im| + 2) ^ 2 := by
        gcongr
        nlinarith
      _ = ((q : ℝ) * (|s.im| + 2)) ^ 2 := by ring
  have hcrossBound :
      ‖DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) w‖ ≤
        B ^ (2 * L) := by
    have h := hL m hm1 (DirichletCharacter.mul chi1 chi) hcross w hwlo hwhi
    calc
      ‖DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) w‖ ≤
          ((m : ℝ) * (|w.im| + 2)) ^ L := h
      _ ≤ (B ^ 2) ^ L := pow_le_pow_left₀ (by positivity) hmBase L
      _ = B ^ (2 * L) := by rw [pow_mul]
  rw [goldfeldFourFactorLFunction, norm_mul, norm_mul, norm_mul]
  calc
    ‖riemannZeta w‖ * ‖DirichletCharacter.LFunction chi1 w‖ *
          ‖DirichletCharacter.LFunction chi w‖ *
        ‖DirichletCharacter.LFunction
            (DirichletCharacter.mul chi1 chi) w‖ ≤
      B ^ E * B ^ L * B ^ L * B ^ (2 * L) := by gcongr
    _ = B ^ (E + 4 * L) := by ring

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldLeftLineBounds.lean` -/

section

/-!
# Goldfeld bounds on the left contour line

The shifted four-factor function is controlled at every height on
`Re(s) = -1`.  At low height ordinary zeta is recovered from its entire
regularization using the fixed distance from the pole.  Combining this with
the fixed-line Mellin decay retains the exact source factor `x⁻¹`.

Source: Koukoulopoulos, printed p. 126, proof of Theorem 12.9.
Semantic review: `SEM-558`.
-/

namespace BoundedGaps.Maynard

open Complex

noncomputable section


/-- One absolute exponent controls the complete Goldfeld four-factor
function at every height on the shifted left contour line. -/
theorem exists_norm_goldfeldFourFactorLFunction_leftLine_le_pow :
    ∃ A : ℕ, 57 ≤ A ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta t : ℝ),
            0 ≤ beta → beta ≤ 1 →
            ‖goldfeldFourFactorLFunction chi1 chi
                (((-1 : ℂ) + t * I) + (beta : ℂ))‖ ≤
              ((q : ℝ) * (|t| + 2)) ^ A := by
  obtain ⟨L, hLexp, hL⟩ := exists_norm_LFunction_closedStrip_le_pow
  obtain ⟨E, hEexp, hZetaOne⟩ :=
    exists_norm_riemannZeta₁_closedStrip_le_pow
  refine ⟨E + 4 * L, by omega, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta t hbeta0 hbeta1
  let w : ℂ := ((-1 : ℂ) + t * I) + (beta : ℂ)
  let T : ℝ := |t| + 2
  let B : ℝ := (q : ℝ) * T
  have hwre : w.re = -1 + beta := by simp [w]
  have hwim : w.im = t := by simp [w]
  have hwlo : -(1 : ℝ) ≤ w.re := by rw [hwre]; linarith
  have hwhi : w.re ≤ 3 := by rw [hwre]; linarith
  have hq : 1 < q := hq1.trans_le hq1q
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1r : (1 : ℝ) ≤ q := one_le_two.trans hq2
  have hq0 : (0 : ℝ) ≤ q := zero_le_one.trans hq1r
  have hT2 : (2 : ℝ) ≤ T := by
    dsimp [T]
    linarith [abs_nonneg t]
  have hT1 : (1 : ℝ) ≤ T := one_le_two.trans hT2
  have hT0 : (0 : ℝ) ≤ T := zero_le_one.trans hT1
  have hB1 : (1 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hwOne : w ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hwre] at hre
    norm_num at hre
    linarith
  have hwSubNorm : (1 : ℝ) ≤ ‖w - 1‖ := by
    have hre : (w - 1).re ≤ -1 := by
      simp only [sub_re, one_re]
      rw [hwre]
      linarith
    have habs : (1 : ℝ) ≤ |(w - 1).re| := by
      rw [abs_of_nonpos (hre.trans (by norm_num))]
      linarith
    exact habs.trans (Complex.abs_re_le_norm (w - 1))
  have hZetaInv : ‖(w - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hwOne))).2 hwSubNorm
  have hZetaBound : ‖riemannZeta w‖ ≤ B ^ E := by
    have hregular := hZetaOne w hwlo hwhi
    have hTB : T ≤ B := by
      dsimp [B]
      nlinarith
    rw [riemannZeta_eq_inv_sub_mul hwOne, norm_mul]
    calc
      ‖(w - 1)⁻¹‖ * ‖riemannZeta₁ w‖ ≤
          1 * ‖riemannZeta₁ w‖ :=
        mul_le_mul_of_nonneg_right hZetaInv (norm_nonneg _)
      _ ≤ T ^ E := by simpa [T, hwim] using hregular
      _ ≤ B ^ E := pow_le_pow_left₀ hT0 hTB E
  have hq1qReal : (q1 : ℝ) ≤ q := by exact_mod_cast hq1q
  have hchi1Bound :
      ‖DirichletCharacter.LFunction chi1 w‖ ≤ B ^ L := by
    have h := hL q1 hq1 chi1 hchi1 w hwlo hwhi
    have hbase : (q1 : ℝ) * (|w.im| + 2) ≤ B := by
      dsimp [B, T]
      rw [hwim]
      gcongr
    exact h.trans (pow_le_pow_left₀ (by positivity) hbase L)
  have hchiBound :
      ‖DirichletCharacter.LFunction chi w‖ ≤ B ^ L := by
    simpa [B, T, hwim] using hL q hq chi hchi w hwlo hwhi
  let m := Nat.lcm q1 q
  have hmpos : 0 < m := Nat.lcm_pos (NeZero.pos q1) (NeZero.pos q)
  letI : NeZero m := ⟨hmpos.ne'⟩
  have hqm : q ≤ m := Nat.le_of_dvd hmpos (Nat.dvd_lcm_right q1 q)
  have hm1 : 1 < m := hq.trans_le hqm
  have hmqq : m ≤ q1 * q :=
    Nat.le_of_dvd (Nat.mul_pos (NeZero.pos q1) (NeZero.pos q))
      (Nat.lcm_dvd_mul q1 q)
  have hmqqReal : (m : ℝ) ≤ (q : ℝ) ^ 2 := by
    calc
      (m : ℝ) ≤ ((q1 * q : ℕ) : ℝ) := by exact_mod_cast hmqq
      _ = (q1 : ℝ) * (q : ℝ) := by norm_num
      _ ≤ (q : ℝ) * (q : ℝ) :=
        mul_le_mul_of_nonneg_right hq1qReal hq0
      _ = (q : ℝ) ^ 2 := by ring
  have hmBase : (m : ℝ) * (|w.im| + 2) ≤ B ^ 2 := by
    rw [hwim]
    dsimp [B, T]
    calc
      (m : ℝ) * (|t| + 2) ≤
          (q : ℝ) ^ 2 * (|t| + 2) :=
        mul_le_mul_of_nonneg_right hmqqReal (by positivity)
      _ ≤ (q : ℝ) ^ 2 * (|t| + 2) ^ 2 := by
        gcongr
        nlinarith
      _ = ((q : ℝ) * (|t| + 2)) ^ 2 := by ring
  have hcrossBound :
      ‖DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) w‖ ≤
        B ^ (2 * L) := by
    have h := hL m hm1 (DirichletCharacter.mul chi1 chi) hcross
      w hwlo hwhi
    calc
      ‖DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) w‖ ≤
          ((m : ℝ) * (|w.im| + 2)) ^ L := h
      _ ≤ (B ^ 2) ^ L := pow_le_pow_left₀ (by positivity) hmBase L
      _ = B ^ (2 * L) := by rw [pow_mul]
  rw [goldfeldFourFactorLFunction, norm_mul, norm_mul, norm_mul]
  calc
    ‖riemannZeta w‖ * ‖DirichletCharacter.LFunction chi1 w‖ *
          ‖DirichletCharacter.LFunction chi w‖ *
        ‖DirichletCharacter.LFunction
            (DirichletCharacter.mul chi1 chi) w‖ ≤
      B ^ E * B ^ L * B ^ L * B ^ (2 * L) := by gcongr
    _ = B ^ (E + 4 * L) := by ring

private lemma goldfeld_leftLine_decay_product_le
    {q u x C : ℝ} {A : ℕ}
    (hq : 0 ≤ q) (hu : 0 ≤ u) (hx : 0 < x) (hC : 0 ≤ C) :
    (q * (u + 2)) ^ A * (C / (1 + u) ^ (A + 2)) * x⁻¹ ≤
      (C * (2 : ℝ) ^ A) * q ^ A /
        (x * (1 + u) ^ 2) := by
  have hbase : u + 2 ≤ 2 * (1 + u) := by linarith
  have hpow : (u + 2) ^ A ≤ (2 * (1 + u)) ^ A :=
    pow_le_pow_left₀ (by linarith) hbase A
  have hqpow : 0 ≤ q ^ A := pow_nonneg hq A
  have hprod :
      q ^ A * (u + 2) ^ A * (C / (1 + u) ^ (A + 2)) * x⁻¹ ≤
        q ^ A * (2 * (1 + u)) ^ A *
          (C / (1 + u) ^ (A + 2)) * x⁻¹ := by
    gcongr
  calc
    (q * (u + 2)) ^ A * (C / (1 + u) ^ (A + 2)) * x⁻¹ =
        q ^ A * (u + 2) ^ A *
          (C / (1 + u) ^ (A + 2)) * x⁻¹ := by rw [mul_pow]
    _ ≤ q ^ A * (2 * (1 + u)) ^ A *
          (C / (1 + u) ^ (A + 2)) * x⁻¹ := hprod
    _ = (C * (2 : ℝ) ^ A) * q ^ A /
          (x * (1 + u) ^ 2) := by
      rw [mul_pow]
      field_simp
      ring

/-- The raw contour integrand retains the exact `x⁻¹` scale and two
integrable powers of ordinate decay on the complete left line. -/
theorem exists_norm_goldfeldContourIntegrand_leftLine_le :
    ∃ A : ℕ, 57 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta x t : ℝ),
            0 ≤ beta → beta ≤ 1 → 1 ≤ x →
            ‖goldfeldContourIntegrand chi1 chi beta x
                ((-1 : ℂ) + t * I)‖ ≤
              C * (q : ℝ) ^ A / (x * (1 + |t|) ^ 2) := by
  obtain ⟨A, hA, hF⟩ :=
    exists_norm_goldfeldFourFactorLFunction_leftLine_le_pow
  obtain ⟨Cphi, hCphi, hPhi⟩ :=
    goldfeldMellinContinuationData.decay_on_neg_one (A + 2) (by omega)
  let C : ℝ := Cphi * (2 : ℝ) ^ A
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨A, hA, C, hC, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta x t hbeta0 hbeta1 hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hF' := hF q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
    beta t hbeta0 hbeta1
  have hPhi' := hPhi t
  have hxpow : ‖(x : ℂ) ^ ((-1 : ℂ) + t * I)‖ = x⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    simp [Real.rpow_neg_one]
  rw [goldfeldContourIntegrand, norm_mul, norm_mul, hxpow]
  calc
    ‖goldfeldFourFactorLFunction chi1 chi
          (((-1 : ℂ) + t * I) + (beta : ℂ))‖ *
        ‖goldfeldMellinContinuationData.Phi ((-1 : ℂ) + t * I)‖ * x⁻¹ ≤
      ((q : ℝ) * (|t| + 2)) ^ A *
        (Cphi / (1 + |t|) ^ (A + 2)) * x⁻¹ := by gcongr
    _ ≤ (Cphi * (2 : ℝ) ^ A) * (q : ℝ) ^ A /
          (x * (1 + |t|) ^ 2) :=
      goldfeld_leftLine_decay_product_le hq0 (abs_nonneg t)
        hxpos hCphi.le
    _ = C * (q : ℝ) ^ A / (x * (1 + |t|) ^ 2) := by rfl

end

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldLeftLineIntegral.lean` -/

section

/-!
# Goldfeld's complete left-line integral

The raw contour integrand is continuous and absolutely integrable on the
complete line `Re(s) = -1`.  Its normalized upward vertical integral has the
source-scale bound `C * q^A / x`.

Source: Koukoulopoulos, printed p. 126, proof of Theorem 12.9.
Semantic review: `SEM-558`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory

noncomputable section

private instance goldfeldLeftLineIntegralLcmNeZero
    {q1 q : ℕ} [NeZero q1] [NeZero q] : NeZero (Nat.lcm q1 q) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩

private theorem continuous_goldfeldContourIntegrand_leftLine
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1}
    {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ} (hbeta1 : beta ≤ 1) (hx : 0 < x) :
    Continuous (fun t : ℝ =>
      goldfeldContourIntegrand chi1 chi beta x
        ((-1 : ℂ) + t * I)) := by
  let s : ℝ → ℂ := fun t => (-1 : ℂ) + t * I
  have hs : Continuous s := by fun_prop
  have hs0 (t : ℝ) : s t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  have hshift : Continuous (fun t : ℝ => s t + (beta : ℂ)) :=
    hs.add continuous_const
  have hshiftOne (t : ℝ) : s t + (beta : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    linarith
  have hzeta : Continuous (fun t : ℝ =>
      riemannZeta (s t + (beta : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hcomp :=
      (differentiableAt_riemannZeta (hshiftOne t)).continuousAt.comp
        (f := fun u : ℝ => s u + (beta : ℂ)) hshift.continuousAt
    simpa [Function.comp_def] using hcomp
  have hLchi1 : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction chi1 (s t + (beta : ℂ))) :=
    (DirichletCharacter.differentiable_LFunction hchi1).continuous.comp
      hshift
  have hLchi : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction chi (s t + (beta : ℂ))) :=
    (DirichletCharacter.differentiable_LFunction hchi).continuous.comp
      hshift
  have hLcross : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
        (s t + (beta : ℂ))) :=
    (DirichletCharacter.differentiable_LFunction hcross).continuous.comp
      hshift
  have hPhi : Continuous (fun t : ℝ =>
      goldfeldMellinContinuationData.Phi (s t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    simpa [Function.comp_def] using
      (goldfeldMellinContinuationData.analytic_off_zero
        (hs0 t)).continuousAt.comp hs.continuousAt
  have hxpow : Continuous (fun t : ℝ => (x : ℂ) ^ s t) :=
    continuous_const.cpow hs fun _ => Complex.ofReal_mem_slitPlane.mpr hx
  have hproduct :=
    (((((hzeta.mul hLchi1).mul hLchi).mul hLcross).mul hPhi).mul hxpow)
  convert hproduct using 1
  ext t
  simp [s, goldfeldContourIntegrand, goldfeldFourFactorLFunction]

private lemma goldfeld_leftLine_source_envelope_le_cauchy
    {q A : ℕ} {C x t y : ℝ}
    (hC : 0 ≤ C) (hx : 0 < x)
    (hy : y ≤ C * (q : ℝ) ^ A / (x * (1 + |t|) ^ 2)) :
    y ≤ (C * (q : ℝ) ^ A / x) * (1 + t ^ 2)⁻¹ := by
  let K : ℝ := C * (q : ℝ) ^ A / x
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hden : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
    nlinarith [sq_abs t, abs_nonneg t]
  have hinv : ((1 + |t|) ^ 2)⁻¹ ≤ (1 + t ^ 2)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 hden
  calc
    y ≤ C * (q : ℝ) ^ A / (x * (1 + |t|) ^ 2) := hy
    _ = K * ((1 + |t|) ^ 2)⁻¹ := by
      dsimp [K]
      field_simp
    _ ≤ K * (1 + t ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hK

/-- The raw Goldfeld integrand is genuinely Bochner integrable on the full
upward line `Re(s) = -1`. -/
theorem goldfeldContourIntegrand_leftLine_verticalIntegrable
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ} (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (hx : 1 ≤ x) :
    VerticalIntegrable
      (goldfeldContourIntegrand chi1 chi beta x) (-1) := by
  obtain ⟨A, _hA, C, hC, hpoint⟩ :=
    exists_norm_goldfeldContourIntegrand_leftLine_le
  let K : ℝ := C * (q : ℝ) ^ A / x
  have hmajor : Integrable (fun t : ℝ => K * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  have hcontinuous := continuous_goldfeldContourIntegrand_leftLine
    hchi1 hchi hcross hbeta1 (zero_lt_one.trans_le hx)
  rw [VerticalIntegrable]
  refine hmajor.mono' ?_ ?_
  · simpa using hcontinuous.aestronglyMeasurable
  · filter_upwards [] with t
    have hp := hpoint q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
      beta x t hbeta0 hbeta1 hx
    have hcauchy := goldfeld_leftLine_source_envelope_le_cauchy
      hC.le (zero_lt_one.trans_le hx) hp
    simpa [K] using hcauchy

/-- The normalized complete left-line integral has Goldfeld's source scale
`O(q^A / x)`, with absolute witnesses chosen before all data. -/
theorem exists_norm_goldfeldVerticalIntegral_neg_one_le :
    ∃ A : ℕ, 57 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta x : ℝ),
            0 ≤ beta → beta ≤ 1 → 1 ≤ x →
            ‖goldfeldVerticalIntegral chi1 chi beta x (-1)‖ ≤
              C * (q : ℝ) ^ A / x := by
  obtain ⟨A, hA, C0, hC0, hpoint⟩ :=
    exists_norm_goldfeldContourIntegrand_leftLine_le
  let C : ℝ := C0 * Real.pi
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨A, hA, C, hC, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta x hbeta0 hbeta1 hx
  let f : ℝ → ℂ := fun t =>
    goldfeldContourIntegrand chi1 chi beta x
      (((-1 : ℝ) : ℂ) + t * I)
  let K : ℝ := C0 * (q : ℝ) ^ A / x
  have hvertical := goldfeldContourIntegrand_leftLine_verticalIntegrable
    hq1 hq1q chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hx
  have hraw : Integrable f := by
    simpa [VerticalIntegrable, f] using hvertical
  have hmajor : Integrable (fun t : ℝ => K * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  have hmajorPoint : ∀ t : ℝ, ‖f t‖ ≤ K * (1 + t ^ 2)⁻¹ := by
    intro t
    have hp := hpoint q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
      beta x t hbeta0 hbeta1 hx
    have hcauchy := goldfeld_leftLine_source_envelope_le_cauchy
      hC0.le (zero_lt_one.trans_le hx) hp
    simpa [f, K] using hcauchy
  have hnormIntegral : ‖∫ t : ℝ, f t‖ ≤ K * Real.pi := by
    calc
      ‖∫ t : ℝ, f t‖ ≤ ∫ t : ℝ, ‖f t‖ :=
        norm_integral_le_integral_norm f
      _ ≤ ∫ t : ℝ, K * (1 + t ^ 2)⁻¹ :=
        integral_mono_ae hraw.norm hmajor (ae_of_all _ hmajorPoint)
      _ = K * Real.pi := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq]
  have hcoefficient :
      ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    exact (inv_le_one₀ (by positivity : 0 < 2 * Real.pi)).2
      (by nlinarith [Real.two_le_pi])
  rw [goldfeldVerticalIntegral, norm_mul]
  calc
    ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ * ‖∫ t : ℝ, f t‖ ≤
        1 * (K * Real.pi) := by gcongr
    _ = C * (q : ℝ) ^ A / x := by
      dsimp [C, K]
      ring

end

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldLocalCancellation.lean` -/

section

/-!
# Goldfeld local cancellation and shifted-zeta residue

This file fills the canceled Mellin pole in Koukoulopoulos Theorem 12.9 with
Mathlib's divided slope. It then isolates the shifted zeta pole at
`s = 1 - beta` and proves its exact source residue. It does not move a contour
or assert that the residue is nonzero.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 55--56,
73--74, and 124--126. Semantic review: `SEM-555`.
-/

noncomputable section

open Complex Set Filter
open scoped Topology

namespace BoundedGaps.Maynard

/-- The shifted location where `zeta(s + beta)` has its source pole. -/
noncomputable def goldfeldShiftedZetaPole (beta : ℝ) : ℂ :=
  ((1 - beta : ℝ) : ℂ)

/-- The derivative-filled quotient of the shifted exceptional L-function by
`s`, centered at the canceled Mellin point. -/
noncomputable def goldfeldShiftedLFunctionDividedSlope
    {q1 : ℕ} [NeZero q1]
    (chi1 : DirichletCharacter ℂ q1) (beta : ℝ) (s : ℂ) : ℂ :=
  dslope
    (fun z : ℂ => DirichletCharacter.LFunction chi1 (z + (beta : ℂ))) 0 s

/-- The numerator left after filling the Mellin point and removing the shifted
zeta denominator. It is entire under the hypotheses proved below. -/
noncomputable def goldfeldContourNumerator
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) (s : ℂ) : ℂ :=
  riemannZeta₁ (s + (beta : ℂ)) *
    goldfeldShiftedLFunctionDividedSlope chi1 beta s *
    DirichletCharacter.LFunction chi (s + (beta : ℂ)) *
    DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
      (s + (beta : ℂ)) *
    (-goldfeldDerivativeMellin s) * (x : ℂ) ^ s

/-- The contour integrand filled at zero, with the shifted zeta pole retained
as the explicit denominator `s - (1 - beta)`. -/
noncomputable def goldfeldRegularizedContourIntegrand
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) (s : ℂ) : ℂ :=
  goldfeldContourNumerator chi1 chi beta x s /
    (s - goldfeldShiftedZetaPole beta)

/-- The exact positive-orientation residue coefficient displayed in the proof
of Koukoulopoulos Theorem 12.9. -/
noncomputable def goldfeldContourResidue
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) : ℂ :=
  (x : ℂ) ^ goldfeldShiftedZetaPole beta *
    DirichletCharacter.LFunction chi1 1 *
    DirichletCharacter.LFunction chi 1 *
    DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) 1 *
    goldfeldMellinContinuationData.Phi (goldfeldShiftedZetaPole beta)

private theorem goldfeldShiftedLFunctionDividedSlope_mul
    {q1 : ℕ} [NeZero q1]
    (chi1 : DirichletCharacter ℂ q1) (beta : ℝ)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    (s : ℂ) :
    s * goldfeldShiftedLFunctionDividedSlope chi1 beta s =
      DirichletCharacter.LFunction chi1 (s + (beta : ℂ)) := by
  simpa [goldfeldShiftedLFunctionDividedSlope, smul_eq_mul] using
    (sub_smul_dslope_of_zero (f := fun z : ℂ =>
      DirichletCharacter.LFunction chi1 (z + (beta : ℂ)))
      (a := (0 : ℂ)) (by simpa using hzero) s)

/-- A shifted nonprincipal L-function has an entire derivative-filled divided
slope. -/
theorem differentiable_goldfeldShiftedLFunctionDividedSlope
    {q1 : ℕ} [NeZero q1]
    {chi1 : DirichletCharacter ℂ q1} (hchi1 : chi1 ≠ 1)
    (beta : ℝ) :
    Differentiable ℂ (goldfeldShiftedLFunctionDividedSlope chi1 beta) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope Filter.univ_mem).2
    (((DirichletCharacter.differentiable_LFunction hchi1).comp
      (differentiable_id.add_const (beta : ℂ))).differentiableOn)


/-- Under the three nonprincipal hypotheses, every factor of the regularized
numerator is entire. -/
theorem differentiable_goldfeldContourNumerator
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1}
    {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    (beta : ℝ) {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (goldfeldContourNumerator chi1 chi beta x) := by
  have hshift : Differentiable ℂ (fun s : ℂ => s + (beta : ℂ)) :=
    differentiable_id.add_const _
  have hzeta : Differentiable ℂ (fun s : ℂ =>
      riemannZeta₁ (s + (beta : ℂ))) :=
    differentiable_riemannZeta₁.comp hshift
  have hLchi : Differentiable ℂ (fun s : ℂ =>
      DirichletCharacter.LFunction chi (s + (beta : ℂ))) :=
    (DirichletCharacter.differentiable_LFunction hchi).comp hshift
  have hLcross : Differentiable ℂ (fun s : ℂ =>
      DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
        (s + (beta : ℂ))) :=
    (DirichletCharacter.differentiable_LFunction hcross).comp hshift
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hxpow : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) :=
    differentiable_id.const_cpow (.inl hx0)
  unfold goldfeldContourNumerator
  exact (((((hzeta.mul
    (differentiable_goldfeldShiftedLFunctionDividedSlope hchi1 beta)).mul
      hLchi).mul hLcross).mul
        differentiable_goldfeldDerivativeMellin.neg).mul hxpow)

/-- Off the canceled point and shifted zeta point, the regularized function is
exactly the original contour integrand. -/
theorem goldfeldRegularizedContourIntegrand_eq_contourIntegrand
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ}
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    {s : ℂ} (hs0 : s ≠ 0)
    (hspole : s ≠ goldfeldShiftedZetaPole beta) :
    goldfeldRegularizedContourIntegrand chi1 chi beta x s =
      goldfeldContourIntegrand chi1 chi beta x s := by
  have hL := goldfeldShiftedLFunctionDividedSlope_mul chi1 beta hzero s
  have harg : s + (beta : ℂ) ≠ 1 := by
    intro h
    apply hspole
    rw [goldfeldShiftedZetaPole]
    norm_num at h ⊢
    linear_combination h
  have hshift : s + (beta : ℂ) - 1 =
      s - goldfeldShiftedZetaPole beta := by
    rw [goldfeldShiftedZetaPole]
    norm_num
    ring
  have hzeta := riemannZeta_eq_inv_sub_mul harg
  rw [hshift] at hzeta
  rw [goldfeldRegularizedContourIntegrand, goldfeldContourNumerator,
    goldfeldContourIntegrand, goldfeldFourFactorLFunction,
    hzeta, ← hL, goldfeldMellinContinuationData.equals_candidate,
    goldfeldMellinCandidate]
  field_simp [hs0, sub_ne_zero.mpr hspole]


/-- Evaluating the entire numerator at the shifted zeta point gives exactly
the source residue coefficient. -/
theorem goldfeldContourNumerator_apply_shiftedZetaPole
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : beta < 1)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    goldfeldContourNumerator chi1 chi beta x
        (goldfeldShiftedZetaPole beta) =
      goldfeldContourResidue chi1 chi beta x := by
  have hdelta0 : goldfeldShiftedZetaPole beta ≠ 0 := by
    rw [goldfeldShiftedZetaPole]
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hbeta.ne')
  have hshift : goldfeldShiftedZetaPole beta + (beta : ℂ) = 1 := by
    rw [goldfeldShiftedZetaPole]
    norm_num
  have hL := goldfeldShiftedLFunctionDividedSlope_mul chi1 beta hzero
    (goldfeldShiftedZetaPole beta)
  rw [hshift] at hL
  have hphi := goldfeldMellinContinuationData.equals_candidate
    (goldfeldShiftedZetaPole beta)
  rw [goldfeldMellinCandidate] at hphi
  have hphiMul : goldfeldShiftedZetaPole beta *
      goldfeldMellinContinuationData.Phi (goldfeldShiftedZetaPole beta) =
      -goldfeldDerivativeMellin (goldfeldShiftedZetaPole beta) := by
    rw [hphi]
    field_simp [hdelta0]
  rw [goldfeldContourNumerator, goldfeldContourResidue, hshift,
    riemannZeta₁_one, one_mul, ← hphiMul, ← hL]
  ring



end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldMellinStripDecay.lean` -/

section

/-!
# Uniform Mellin decay on Goldfeld's contour strip

The logarithmic Mellin kernel has one fixed compact support for every real
part in `[-1,2]`.  Leibniz bounds its derivatives uniformly in that parameter,
and the Fourier derivative identity gives arbitrary high-ordinate decay.

Source: Koukoulopoulos, printed pp. 73--74, equations (7.6)--(7.7), and
printed p. 80, Exercise 7.2(c). Semantic review: `SEM-556`.
-/

noncomputable section

open Complex Set MeasureTheory Filter Real
open scoped ContDiff Topology SchwartzMap FourierTransform RealInnerProductSpace

namespace BoundedGaps.Maynard

private theorem iteratedDeriv_real_smul
    (n : ℕ) (f : ℝ → ℝ) (g : ℝ → ℂ) (u : ℝ)
    (hf : ContDiffAt ℝ n f u) (hg : ContDiffAt ℝ n g u) :
    iteratedDeriv n (f • g) u = ∑ i ∈ Finset.range (n + 1),
      n.choose i • iteratedDeriv i f u • iteratedDeriv (n - i) g u := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_smul (Set.mem_univ u) uniqueDiffOn_univ
      hf.contDiffWithinAt hg.contDiffWithinAt

private noncomputable def baseKernel (u : ℝ) : ℂ :=
  goldfeldMellinDerivativeWeight (Real.exp (-u))

private noncomputable def stripKernel (sigma u : ℝ) : ℂ :=
  Real.exp (-sigma * u) • baseKernel u

private theorem weight_contDiff :
    ContDiff ℝ ∞ goldfeldMellinDerivativeWeight := by
  have hd : ContDiff ℝ ∞ goldfeldPlateauDerivativeComplex :=
    Complex.ofRealCLM.contDiff.comp goldfeldPlateau_deriv_contDiff
  unfold goldfeldMellinDerivativeWeight
  exact (Complex.ofRealCLM.contDiff.comp contDiff_id).mul hd

private theorem base_contDiff : ContDiff ℝ ∞ baseKernel := by
  unfold baseKernel
  exact weight_contDiff.comp (contDiff_id.neg.exp)

private theorem strip_contDiff (sigma : ℝ) :
    ContDiff ℝ ∞ (stripKernel sigma) := by
  unfold stripKernel
  exact (contDiff_const.mul contDiff_id).exp.smul base_contDiff

private theorem base_eq_zero_of_pos {u : ℝ} (hu : 0 < u) :
    baseKernel u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlt : Real.exp (-u) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hd := goldfeldPlateau_deriv_eq_zero_of_pos_of_lt_one harg hlt
  simp [baseKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem base_eq_zero_of_lt_neg_log_two
    {u : ℝ} (hu : u < -Real.log 2) : baseKernel u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlog : Real.log 2 < -u := by linarith
  have hgt : 2 < Real.exp (-u) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact (Real.exp_lt_exp).2 hlog
  have hd := goldfeldPlateau_deriv_eq_zero_of_two_lt hgt
  simp [baseKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem base_support_subset :
    Function.support baseKernel ⊆ Icc (-Real.log 2) 0 := by
  intro u hu
  by_contra hnot
  have hcases : u < -Real.log 2 ∨ 0 < u := by
    by_cases hleft : u < -Real.log 2
    · exact Or.inl hleft
    · have hleft' : -Real.log 2 ≤ u := le_of_not_gt hleft
      by_cases hright : 0 < u
      · exact Or.inr hright
      · exact False.elim (hnot ⟨hleft', le_of_not_gt hright⟩)
  rcases hcases with hleft | hright
  · exact hu (base_eq_zero_of_lt_neg_log_two hleft)
  · exact hu (base_eq_zero_of_pos hright)

private theorem base_hasCompactSupport : HasCompactSupport baseKernel := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Icc (-Real.log 2) 0) isCompact_Icc
  exact base_support_subset

private noncomputable def baseSchwartz : 𝓢(ℝ, ℂ) :=
  base_hasCompactSupport.toSchwartzMap base_contDiff

private theorem stripKernel_fourier (sigma t : ℝ) :
    goldfeldDerivativeMellin ((sigma : ℂ) + t * I) =
      𝓕 (stripKernel sigma) (t / (2 * π)) := by
  calc
    goldfeldDerivativeMellin ((sigma : ℂ) + t * I) =
        mellin goldfeldMellinDerivativeWeight ((sigma : ℂ) + t * I) :=
      goldfeldDerivativeMellin_eq_weight _
    _ = 𝓕 (fun u : ℝ =>
        Real.exp (-((sigma : ℂ) + t * I).re * u) •
          goldfeldMellinDerivativeWeight (Real.exp (-u)))
        (((sigma : ℂ) + t * I).im / (2 * π)) :=
      mellin_eq_fourier goldfeldMellinDerivativeWeight
    _ = 𝓕 (stripKernel sigma) (t / (2 * π)) := by
      norm_num
      apply congrArg (fun f : ℝ → ℂ => 𝓕 f (t / (2 * π)))
      funext u
      simp [stripKernel, baseKernel]

private theorem iteratedDeriv_base_eq_zero_of_not_mem
    (n : ℕ) {u : ℝ} (hu : u ∉ Icc (-Real.log 2) 0) :
    iteratedDeriv n baseKernel u = 0 := by
  have hcases : u < -Real.log 2 ∨ 0 < u := by
    by_cases hleft : u < -Real.log 2
    · exact Or.inl hleft
    · right
      have hleft' : -Real.log 2 ≤ u := le_of_not_gt hleft
      by_contra hnot
      exact hu ⟨hleft', le_of_not_gt hnot⟩
  rcases hcases with hleft | hright
  · have heq : Set.EqOn baseKernel 0 (Iio (-Real.log 2)) := by
      intro v hv
      exact base_eq_zero_of_lt_neg_log_two hv
    have h := heq.iteratedDeriv_of_isOpen isOpen_Iio n hleft
    simpa using h
  · have heq : Set.EqOn baseKernel 0 (Ioi 0) := by
      intro v hv
      exact base_eq_zero_of_pos hv
    have h := heq.iteratedDeriv_of_isOpen isOpen_Ioi n hright
    simpa using h

private theorem norm_iteratedDeriv_base_le_seminorm (n : ℕ) (u : ℝ) :
    ‖iteratedDeriv n baseKernel u‖ ≤
      SchwartzMap.seminorm ℝ 0 n baseSchwartz := by
  have h := SchwartzMap.le_seminorm' ℝ 0 n baseSchwartz u
  change ‖iteratedDeriv n (baseSchwartz : ℝ → ℂ) u‖ ≤
    SchwartzMap.seminorm ℝ 0 n baseSchwartz
  simpa using h

private theorem expFactor_iteratedDeriv (sigma : ℝ) (n : ℕ) :
    iteratedDeriv n (fun u : ℝ => Real.exp (-sigma * u)) =
      fun u => (-sigma) ^ n * Real.exp (-sigma * u) := by
  simpa only [neg_mul] using iteratedDeriv_exp_const_mul n (-sigma)

private theorem expFactor_le_four
    {sigma u : ℝ} (hsigma : sigma ∈ Icc (-(1 : ℝ)) 2)
    (hu : u ∈ Icc (-Real.log 2) 0) :
    Real.exp (-sigma * u) ≤ 4 := by
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsigmaAbs : |sigma| ≤ 2 :=
    (abs_le).2 ⟨by linarith [hsigma.1], hsigma.2⟩
  have huAbs : |u| ≤ Real.log 2 := by
    rw [abs_of_nonpos hu.2]
    linarith [hu.1]
  have hprod : |sigma * u| ≤ 2 * Real.log 2 := by
    rw [abs_mul]
    exact mul_le_mul hsigmaAbs huAbs (abs_nonneg u) (by norm_num)
  have harg : -sigma * u ≤ 2 * Real.log 2 := by
    calc
      -sigma * u = -(sigma * u) := by ring
      _ ≤ |sigma * u| := neg_le_abs _
      _ ≤ 2 * Real.log 2 := hprod
  calc
    Real.exp (-sigma * u) ≤ Real.exp (2 * Real.log 2) :=
      Real.exp_le_exp.mpr harg
    _ = 4 := by
      rw [show (2 : ℝ) * Real.log 2 = Real.log 2 + Real.log 2 by ring,
        Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num

private theorem norm_iteratedDeriv_stripKernel_le
    (n : ℕ) {sigma : ℝ} (hsigma : sigma ∈ Icc (-(1 : ℝ)) 2)
    (u : ℝ) :
    ‖iteratedDeriv n (stripKernel sigma) u‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * 2 ^ i * 4 *
          SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz := by
  by_cases hu : u ∈ Icc (-Real.log 2) 0
  · rw [show stripKernel sigma =
        (fun u : ℝ => Real.exp (-sigma * u)) • baseKernel by rfl]
    have hExp : ContDiffAt ℝ n (fun u : ℝ => Real.exp (-sigma * u)) u :=
      (contDiff_const.mul contDiff_id).exp.contDiffAt.of_le (by
        exact_mod_cast le_top)
    have hBase : ContDiffAt ℝ n baseKernel u :=
      base_contDiff.contDiffAt.of_le (by exact_mod_cast le_top)
    rw [iteratedDeriv_real_smul n _ _ u hExp hBase]
    calc
      ‖∑ i ∈ Finset.range (n + 1),
          n.choose i •
            iteratedDeriv i (fun u : ℝ => Real.exp (-sigma * u)) u •
              iteratedDeriv (n - i) baseKernel u‖ ≤
          ∑ i ∈ Finset.range (n + 1),
            ‖n.choose i •
              iteratedDeriv i (fun u : ℝ => Real.exp (-sigma * u)) u •
                iteratedDeriv (n - i) baseKernel u‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * 2 ^ i * 4 *
            SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz := by
        apply Finset.sum_le_sum
        intro i hi
        rw [expFactor_iteratedDeriv]
        rw [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul,
          norm_smul, Real.norm_eq_abs]
        have hsigmaPow : |(-sigma) ^ i| ≤ (2 : ℝ) ^ i := by
          rw [abs_pow, abs_neg]
          exact pow_le_pow_left₀ (abs_nonneg sigma) (by
            exact (abs_le).2 ⟨by linarith [hsigma.1], hsigma.2⟩) i
        have hexp := expFactor_le_four hsigma hu
        have hbase := norm_iteratedDeriv_base_le_seminorm (n - i) u
        have hchoose : 0 ≤ (n.choose i : ℝ) := by positivity
        have hpow : 0 ≤ (2 : ℝ) ^ i := by positivity
        have hseminorm : 0 ≤ SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz :=
          by positivity
        rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
        change (n.choose i : ℝ) *
            (|(-sigma) ^ i| * Real.exp (-sigma * u) *
              ‖iteratedDeriv (n - i) baseKernel u‖) ≤ _
        calc
          (n.choose i : ℝ) *
                (|(-sigma) ^ i| * Real.exp (-sigma * u) *
                  ‖iteratedDeriv (n - i) baseKernel u‖) ≤
              (n.choose i : ℝ) *
                ((2 : ℝ) ^ i * 4 *
                  SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz) := by
            gcongr
          _ = (n.choose i : ℝ) * 2 ^ i * 4 *
              SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz := by ring
  · have hzero : iteratedDeriv n (stripKernel sigma) u = 0 := by
      rw [show stripKernel sigma =
        (fun u : ℝ => Real.exp (-sigma * u)) • baseKernel by rfl]
      have hExp : ContDiffAt ℝ n (fun u : ℝ => Real.exp (-sigma * u)) u :=
        (contDiff_const.mul contDiff_id).exp.contDiffAt.of_le (by
          exact_mod_cast le_top)
      have hBase : ContDiffAt ℝ n baseKernel u :=
        base_contDiff.contDiffAt.of_le (by exact_mod_cast le_top)
      rw [iteratedDeriv_real_smul n _ _ u hExp hBase]
      apply Finset.sum_eq_zero
      intro i hi
      rw [iteratedDeriv_base_eq_zero_of_not_mem (n - i) hu]
      simp
    rw [hzero, norm_zero]
    positivity

private theorem strip_hasCompactSupport (sigma : ℝ) :
    HasCompactSupport (stripKernel sigma) := by
  change HasCompactSupport
    ((fun u : ℝ => Real.exp (-sigma * u)) • baseKernel)
  exact base_hasCompactSupport.smul_left

private theorem hasCompactSupport_iteratedDeriv
    {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∀ n : ℕ, HasCompactSupport (iteratedDeriv n f)
  | 0 => by simpa using hf
  | n + 1 => by
      rw [iteratedDeriv_succ]
      exact (hasCompactSupport_iteratedDeriv hf n).deriv

private theorem integrable_iteratedDeriv_stripKernel
    (sigma : ℝ) (n : ℕ) :
    Integrable (iteratedDeriv n (stripKernel sigma)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (strip_contDiff sigma).continuous_iteratedDeriv n (by
      exact_mod_cast le_top)
  · exact hasCompactSupport_iteratedDeriv (strip_hasCompactSupport sigma) n

private theorem iteratedDeriv_stripKernel_eq_zero_of_not_mem
    (n : ℕ) (sigma : ℝ) {u : ℝ}
    (hu : u ∉ Icc (-Real.log 2) 0) :
    iteratedDeriv n (stripKernel sigma) u = 0 := by
  rw [show stripKernel sigma =
    (fun u : ℝ => Real.exp (-sigma * u)) • baseKernel by rfl]
  have hExp : ContDiffAt ℝ n (fun u : ℝ => Real.exp (-sigma * u)) u :=
    (contDiff_const.mul contDiff_id).exp.contDiffAt.of_le (by
      exact_mod_cast le_top)
  have hBase : ContDiffAt ℝ n baseKernel u :=
    base_contDiff.contDiffAt.of_le (by exact_mod_cast le_top)
  rw [iteratedDeriv_real_smul n _ _ u hExp hBase]
  apply Finset.sum_eq_zero
  intro i hi
  rw [iteratedDeriv_base_eq_zero_of_not_mem (n - i) hu]
  simp

private theorem integral_norm_iteratedDeriv_stripKernel_le
    (n : ℕ) {sigma : ℝ} (hsigma : sigma ∈ Icc (-(1 : ℝ)) 2) :
    ∫ u : ℝ, ‖iteratedDeriv n (stripKernel sigma) u‖ ≤
      (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * 2 ^ i * 4 *
          SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz) * Real.log 2 := by
  let M : ℝ := ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * 2 ^ i * 4 *
      SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hsupport : (fun u : ℝ => ‖iteratedDeriv n (stripKernel sigma) u‖) =
      (Icc (-Real.log 2) 0).indicator
        (fun u : ℝ => ‖iteratedDeriv n (stripKernel sigma) u‖) := by
    funext u
    by_cases hu : u ∈ Icc (-Real.log 2) 0
    · simp [hu]
    · rw [iteratedDeriv_stripKernel_eq_zero_of_not_mem n sigma hu]
      simp [hu]
  rw [hsupport, integral_indicator measurableSet_Icc]
  calc
    (∫ u : ℝ in Icc (-Real.log 2) 0,
        ‖iteratedDeriv n (stripKernel sigma) u‖) ≤
        ∫ _u : ℝ in Icc (-Real.log 2) 0, M := by
      apply setIntegral_mono_on
      · exact (integrable_iteratedDeriv_stripKernel sigma n).norm.integrableOn
      · apply integrableOn_const
        · exact ne_of_lt isCompact_Icc.measure_lt_top
        · finiteness
      · exact measurableSet_Icc
      · intro u hu
        simpa [M] using norm_iteratedDeriv_stripKernel_le n hsigma u
    _ = M * Real.log 2 := by
      rw [setIntegral_const, Measure.real, Real.volume_Icc]
      rw [show 0 - -Real.log 2 = Real.log 2 by ring]
      rw [ENNReal.toReal_ofReal (Real.log_nonneg (by norm_num))]
      simp [smul_eq_mul, mul_comm]
    _ = (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * 2 ^ i * 4 *
          SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz) * Real.log 2 := rfl

private theorem abs_pow_mul_norm_fourier_stripKernel_le
    (n : ℕ) {sigma : ℝ} (hsigma : sigma ∈ Icc (-(1 : ℝ)) 2)
    (t : ℝ) :
    |t| ^ n * ‖𝓕 (stripKernel sigma) (t / (2 * π))‖ ≤
      (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * 2 ^ i * 4 *
          SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz) * Real.log 2 := by
  let xi : ℝ := t / (2 * π)
  have hFourier := congrFun
    (Real.fourier_iteratedDeriv (N := n)
      ((strip_contDiff sigma).of_le (by exact_mod_cast le_top))
      (fun m _hm => integrable_iteratedDeriv_stripKernel sigma m)
      (n := n) (by rfl)) xi
  have hfreq : ‖(2 * (π : ℂ) * I * (xi : ℂ))‖ = |t| := by
    have hcoeff : 2 * (π : ℂ) * I * (xi : ℂ) = (t : ℂ) * I := by
      dsimp [xi]
      push_cast
      field_simp [Real.pi_ne_zero]
    rw [hcoeff, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
  calc
    |t| ^ n * ‖𝓕 (stripKernel sigma) (t / (2 * π))‖ =
        ‖(2 * (π : ℂ) * I * (xi : ℂ)) ^ n •
          𝓕 (stripKernel sigma) xi‖ := by
      rw [norm_smul, norm_pow, hfreq]
    _ = ‖𝓕 (iteratedDeriv n (stripKernel sigma)) xi‖ := by
      rw [hFourier]
    _ ≤ ∫ u : ℝ, ‖iteratedDeriv n (stripKernel sigma) u‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm
        𝐞 volume (innerₗ ℝ) (iteratedDeriv n (stripKernel sigma)) xi
    _ ≤ (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * 2 ^ i * 4 *
          SchwartzMap.seminorm ℝ 0 (n - i) baseSchwartz) * Real.log 2 :=
      integral_norm_iteratedDeriv_stripKernel_le n hsigma

/-- The continued Mellin candidate decays to every prescribed natural order,
with one constant uniform over the complete closed contour strip. -/
theorem goldfeldMellinCandidate_decay_on_closedStrip
    (A : ℕ) (_hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ sigma t : ℝ, sigma ∈ Icc (-(1 : ℝ)) 2 →
        1 ≤ |t| →
          ‖goldfeldMellinCandidate ((sigma : ℂ) + t * I)‖ ≤
            C / (1 + |t|) ^ A := by
  let M : ℝ := (∑ i ∈ Finset.range (A + 1),
    (A.choose i : ℝ) * 2 ^ i * 4 *
      SchwartzMap.seminorm ℝ 0 (A - i) baseSchwartz) * Real.log 2
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  let C : ℝ := (M + 1) * 2 ^ A
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro sigma t hsigma ht
  let s : ℂ := (sigma : ℂ) + t * I
  have htpos : 0 < |t| := zero_lt_one.trans_le ht
  have hsNorm : (1 : ℝ) ≤ ‖s‖ := by
    have him := Complex.abs_im_le_norm s
    have him' : |t| ≤ ‖s‖ := by simpa [s] using him
    exact ht.trans him'
  have hcandidate :
      ‖goldfeldMellinCandidate s‖ ≤ ‖goldfeldDerivativeMellin s‖ := by
    rw [goldfeldMellinCandidate, norm_div, norm_neg]
    exact div_le_self (norm_nonneg _) hsNorm
  have hfourier :
      ‖goldfeldDerivativeMellin s‖ =
        ‖𝓕 (stripKernel sigma) (t / (2 * π))‖ := by
    rw [stripKernel_fourier]
  have hpow := abs_pow_mul_norm_fourier_stripKernel_le A hsigma t
  have hfourierDecay :
      ‖𝓕 (stripKernel sigma) (t / (2 * π))‖ ≤ M / |t| ^ A := by
    apply (le_div_iff₀ (pow_pos htpos A)).2
    simpa [M, mul_comm] using hpow
  have hscale : 1 + |t| ≤ 2 * |t| := by linarith
  have hpowscale : (1 + |t|) ^ A ≤ (2 * |t|) ^ A :=
    pow_le_pow_left₀ (by positivity) hscale A
  have hconvert : M / |t| ^ A ≤ C / (1 + |t|) ^ A := by
    apply (div_le_div_iff₀ (pow_pos htpos A) (by positivity)).2
    calc
      M * (1 + |t|) ^ A ≤ M * (2 * |t|) ^ A :=
        mul_le_mul_of_nonneg_left hpowscale hM
      _ ≤ (M + 1) * (2 * |t|) ^ A := by
        gcongr
        linarith
      _ = C * |t| ^ A := by
        dsimp [C]
        rw [mul_pow]
        ring
  calc
    ‖goldfeldMellinCandidate s‖ ≤ ‖goldfeldDerivativeMellin s‖ := hcandidate
    _ = ‖𝓕 (stripKernel sigma) (t / (2 * π))‖ := hfourier
    _ ≤ M / |t| ^ A := hfourierDecay
    _ ≤ C / (1 + |t|) ^ A := hconvert

/-- The source-facing continuation package inherits the uniform closed-strip
decay of its explicit candidate. -/
theorem goldfeldMellinContinuation_decay_on_closedStrip
    (A : ℕ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ sigma t : ℝ, sigma ∈ Icc (-(1 : ℝ)) 2 →
        1 ≤ |t| →
          ‖goldfeldMellinContinuationData.Phi
              ((sigma : ℂ) + t * I)‖ ≤
            C / (1 + |t|) ^ A := by
  obtain ⟨C, hC, hbound⟩ :=
    goldfeldMellinCandidate_decay_on_closedStrip A hA
  refine ⟨C, hC, ?_⟩
  intro sigma t hsigma ht
  rw [goldfeldMellinContinuationData.equals_candidate]
  exact hbound sigma t hsigma ht

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldHorizontalEdge.lean` -/

section

/-!
# Goldfeld horizontal-edge decay

The closed-strip growth and Mellin estimates are combined on the real-part
interval `[-1,2]`.  The filled numerator supplies interval integrability; on
the nonzero high horizontal lines it agrees with the raw contour integrand.
The left-to-right lower integral is kept separate from the positively
oriented contour side, whose later consumer inserts a minus sign.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 58, 74,
125--127, especially (5.13), (7.9), and the proof of Theorem 12.9.
Semantic review: `SEM-557`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory Set Filter
open scoped Interval Topology

noncomputable section

private lemma goldfeld_mul_decay_bound
    {q u x C : ℝ} {A : ℕ} (hq : 0 ≤ q) (hu : 0 ≤ u)
    (_hx : 0 ≤ x) (hC : 0 ≤ C) :
    (q * (u + 2)) ^ A * (C / (1 + u) ^ (A + 2)) * x ^ 2 ≤
      (C * (2 : ℝ) ^ A) * q ^ A * x ^ 2 / (1 + u) ^ 2 := by
  have hbase : u + 2 ≤ 2 * (1 + u) := by linarith
  have hpow : (u + 2) ^ A ≤ (2 * (1 + u)) ^ A :=
    pow_le_pow_left₀ (by linarith) hbase A
  have hqpow : 0 ≤ q ^ A := pow_nonneg hq A
  have hprod :
      q ^ A * (u + 2) ^ A * (C / (1 + u) ^ (A + 2)) * x ^ 2 ≤
        q ^ A * (2 * (1 + u)) ^ A *
          (C / (1 + u) ^ (A + 2)) * x ^ 2 := by
    gcongr
  calc
    (q * (u + 2)) ^ A * (C / (1 + u) ^ (A + 2)) * x ^ 2 =
        q ^ A * (u + 2) ^ A * (C / (1 + u) ^ (A + 2)) * x ^ 2 := by
      rw [mul_pow]
    _ ≤ q ^ A * (2 * (1 + u)) ^ A *
          (C / (1 + u) ^ (A + 2)) * x ^ 2 := hprod
    _ = (C * (2 : ℝ) ^ A) * q ^ A * x ^ 2 / (1 + u) ^ 2 := by
      rw [mul_pow]
      field_simp
      ring

private theorem norm_goldfeldContourIntegrand_horizontal_le_of_bounds
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1}
    {chi : DirichletCharacter ℂ q}
    {A : ℕ} {Cphi beta x sigma t : ℝ}
    (hx : 1 ≤ x)
    (hsigma : sigma ∈ Icc (-(1 : ℝ)) 2) (ht : 1 ≤ |t|)
    (hF : ‖goldfeldFourFactorLFunction chi1 chi
        (((sigma : ℂ) + t * I) + (beta : ℂ))‖ ≤
      ((q : ℝ) * (|t| + 2)) ^ A)
    (hPhi : ‖goldfeldMellinContinuationData.Phi
        ((sigma : ℂ) + t * I)‖ ≤ Cphi / (1 + |t|) ^ (A + 2))
    (hCphi : 0 ≤ Cphi) :
    ‖goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + t * I)‖ ≤
      (Cphi * (2 : ℝ) ^ A) * (q : ℝ) ^ A * x ^ 2 /
        (1 + |t|) ^ 2 := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hsigmaPow : x ^ sigma ≤ x ^ (2 : ℕ) := by
    calc
      x ^ sigma ≤ x ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx hsigma.2
      _ = x ^ (2 : ℕ) := Real.rpow_two x
  have hpowprod := goldfeld_mul_decay_bound (A := A) hq0 (abs_nonneg t)
    (by positivity : 0 ≤ x) hCphi
  have hcpow : ‖(x : ℂ) ^ ((sigma : ℂ) + t * I)‖ = x ^ sigma := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    simp
  rw [goldfeldContourIntegrand, norm_mul, norm_mul, hcpow]
  calc
    ‖goldfeldFourFactorLFunction chi1 chi
        (((sigma : ℂ) + t * I) + (beta : ℂ))‖ *
        ‖goldfeldMellinContinuationData.Phi ((sigma : ℂ) + t * I)‖ *
        x ^ sigma ≤
      ((q : ℝ) * (|t| + 2)) ^ A *
        (Cphi / (1 + |t|) ^ (A + 2)) * x ^ 2 := by
      calc
        _ ≤
            ‖goldfeldFourFactorLFunction chi1 chi
                (((sigma : ℂ) + t * I) + (beta : ℂ))‖ *
              ‖goldfeldMellinContinuationData.Phi ((sigma : ℂ) + t * I)‖ *
              x ^ (2 : ℕ) := by
          exact mul_le_mul_of_nonneg_left hsigmaPow
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ _ := by
          gcongr
    _ ≤ (Cphi * (2 : ℝ) ^ A) * (q : ℝ) ^ A * x ^ 2 /
          (1 + |t|) ^ 2 := hpowprod

/-- One absolute exponent and one absolute constant bound the raw integrand on
both signed high horizontal lines. -/
theorem exists_norm_goldfeldContourIntegrand_horizontal_le :
    ∃ A : ℕ, 57 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta x sigma t : ℝ),
            0 ≤ beta → beta ≤ 1 → 1 ≤ x →
            sigma ∈ Icc (-(1 : ℝ)) 2 → 1 ≤ |t| →
            ‖goldfeldContourIntegrand chi1 chi beta x
                ((sigma : ℂ) + t * I)‖ ≤
              C * (q : ℝ) ^ A * x ^ 2 / (1 + |t|) ^ 2 := by
  obtain ⟨A, hA, hF⟩ :=
    exists_norm_goldfeldFourFactorLFunction_closedStrip_le_pow
  obtain ⟨Cphi, hCphi, hPhi⟩ :=
    goldfeldMellinContinuation_decay_on_closedStrip (A + 2) (by omega)
  let C : ℝ := Cphi * (2 : ℝ) ^ A
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨A, hA, C, hC, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta x sigma t hbeta0 hbeta1 hx hsigma ht
  have him : (((sigma : ℂ) + t * I).im) = t := by simp
  have hF' : ‖goldfeldFourFactorLFunction chi1 chi
        (((sigma : ℂ) + t * I) + (beta : ℂ))‖ ≤
      ((q : ℝ) * (|t| + 2)) ^ A := by
    have h := hF q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
      beta ((sigma : ℂ) + t * I) hbeta0 hbeta1
        (by simpa using hsigma.1) (by simpa using hsigma.2)
        (by simpa [him] using ht)
    simpa [him] using h
  have hPhi' := hPhi sigma t hsigma ht
  have hpoint := norm_goldfeldContourIntegrand_horizontal_le_of_bounds
    (A := A) (q := q) (chi1 := chi1) (chi := chi)
    hx hsigma ht hF' hPhi' hCphi.le
  simpa [C, mul_assoc, mul_left_comm, mul_comm] using hpoint

private theorem continuous_goldfeldRegularizedContourIntegrand_horizontal_plus
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1} {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ} (hx : 0 < x) (hT : 1 ≤ T) :
    Continuous (fun sigma : ℝ => goldfeldRegularizedContourIntegrand
      chi1 chi beta x ((sigma : ℂ) + T * I)) := by
  have hpath : Continuous (fun sigma : ℝ => (sigma : ℂ) + T * I) :=
    Complex.continuous_ofReal.add continuous_const
  have hnum : Continuous (goldfeldContourNumerator chi1 chi beta x) :=
    (differentiable_goldfeldContourNumerator hchi1 hchi hcross beta hx).continuous
  have hden : Continuous (fun sigma : ℝ =>
      ((sigma : ℂ) + T * I) - goldfeldShiftedZetaPole beta) :=
    hpath.sub continuous_const
  have hden_ne : ∀ sigma : ℝ,
      ((sigma : ℂ) + T * I) - goldfeldShiftedZetaPole beta ≠ 0 := by
    intro sigma hs
    have hi := congrArg Complex.im hs
    simp [goldfeldShiftedZetaPole] at hi
    linarith
  unfold goldfeldRegularizedContourIntegrand
  exact (hnum.comp hpath).div hden hden_ne

private theorem continuous_goldfeldRegularizedContourIntegrand_horizontal_minus
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1} {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ} (hx : 0 < x) (hT : 1 ≤ T) :
    Continuous (fun sigma : ℝ => goldfeldRegularizedContourIntegrand
      chi1 chi beta x ((sigma : ℂ) - T * I)) := by
  have hpath : Continuous (fun sigma : ℝ => (sigma : ℂ) - T * I) :=
    Complex.continuous_ofReal.sub continuous_const
  have hnum : Continuous (goldfeldContourNumerator chi1 chi beta x) :=
    (differentiable_goldfeldContourNumerator hchi1 hchi hcross beta hx).continuous
  have hden : Continuous (fun sigma : ℝ =>
      ((sigma : ℂ) - T * I) - goldfeldShiftedZetaPole beta) :=
    hpath.sub continuous_const
  have hden_ne : ∀ sigma : ℝ,
      ((sigma : ℂ) - T * I) - goldfeldShiftedZetaPole beta ≠ 0 := by
    intro sigma hs
    have hi := congrArg Complex.im hs
    simp [goldfeldShiftedZetaPole] at hi
    linarith
  unfold goldfeldRegularizedContourIntegrand
  exact (hnum.comp hpath).div hden hden_ne

/-- The filled Goldfeld integrand is interval-integrable on both high
horizontal edges. -/
theorem intervalIntegrable_goldfeldRegularizedContourIntegrand_horizontal
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1} {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ} (hx : 0 < x) (hT : 1 ≤ T) :
    IntervalIntegrable
      (fun sigma : ℝ => goldfeldRegularizedContourIntegrand
        chi1 chi beta x ((sigma : ℂ) + T * I)) volume (-1) 2 ∧
    IntervalIntegrable
      (fun sigma : ℝ => goldfeldRegularizedContourIntegrand
        chi1 chi beta x ((sigma : ℂ) - T * I)) volume (-1) 2 := by
  exact ⟨(continuous_goldfeldRegularizedContourIntegrand_horizontal_plus
      hchi1 hchi hcross hx hT).intervalIntegrable _ _,
    (continuous_goldfeldRegularizedContourIntegrand_horizontal_minus
      hchi1 hchi hcross hx hT).intervalIntegrable _ _⟩

private theorem goldfeldRegularizedContourIntegrand_eq_horizontal_plus
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q)
    {beta x T : ℝ}
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    (hT : 1 ≤ T) (sigma : ℝ) :
    goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I) =
      goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hs0 : ((sigma : ℂ) + T * I) ≠ 0 := by
    intro hs
    have hi := congrArg Complex.im hs
    simp at hi
    linarith
  have hsp : ((sigma : ℂ) + T * I) ≠ goldfeldShiftedZetaPole beta := by
    intro hs
    have hi := congrArg Complex.im hs
    simp [goldfeldShiftedZetaPole] at hi
    linarith
  exact goldfeldRegularizedContourIntegrand_eq_contourIntegrand
    chi1 chi hzero hs0 hsp

private theorem goldfeldRegularizedContourIntegrand_eq_horizontal_minus
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q)
    {beta x T : ℝ}
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    (hT : 1 ≤ T) (sigma : ℝ) :
    goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I) =
      goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hs0 : ((sigma : ℂ) - T * I) ≠ 0 := by
    intro hs
    have hi := congrArg Complex.im hs
    simp at hi
    linarith
  have hsp : ((sigma : ℂ) - T * I) ≠ goldfeldShiftedZetaPole beta := by
    intro hs
    have hi := congrArg Complex.im hs
    simp [goldfeldShiftedZetaPole] at hi
    linarith
  exact goldfeldRegularizedContourIntegrand_eq_contourIntegrand
    chi1 chi hzero hs0 hsp

/-- On either high horizontal line the filled and raw integrals coincide. -/
theorem goldfeldRegularizedContourIntegrand_eq_intervalIntegral_goldfeldContourIntegrand_horizontal
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1} {chi : DirichletCharacter ℂ q}
    {beta x T : ℝ}
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    (hT : 1 ≤ T) :
    (∫ sigma in (-1)..2,
      goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I)) =
      ∫ sigma in (-1)..2,
        goldfeldContourIntegrand chi1 chi beta x
          ((sigma : ℂ) + T * I) ∧
    (∫ sigma in (-1)..2,
      goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I)) =
      ∫ sigma in (-1)..2,
        goldfeldContourIntegrand chi1 chi beta x
          ((sigma : ℂ) - T * I) := by
  have hplus : Set.EqOn
      (fun sigma : ℝ => goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I))
      (fun sigma : ℝ => goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I)) (uIcc (-1) 2) := by
    intro sigma _hsigma
    exact goldfeldRegularizedContourIntegrand_eq_horizontal_plus
      chi1 chi hzero hT sigma
  have hminus : Set.EqOn
      (fun sigma : ℝ => goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I))
      (fun sigma : ℝ => goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I)) (uIcc (-1) 2) := by
    intro sigma _hsigma
    exact goldfeldRegularizedContourIntegrand_eq_horizontal_minus
      chi1 chi hzero hT sigma
  exact ⟨intervalIntegral.integral_congr hplus,
    intervalIntegral.integral_congr hminus⟩

/-- Under the canceling zero hypothesis, the raw integrand is also
interval-integrable on both horizontal edges. -/
theorem intervalIntegrable_goldfeldContourIntegrand_horizontal
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1} {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ} (hx : 0 < x) (hT : 1 ≤ T)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    IntervalIntegrable
      (fun sigma : ℝ => goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I)) volume (-1) 2 ∧
    IntervalIntegrable
      (fun sigma : ℝ => goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I)) volume (-1) 2 := by
  have hreg := intervalIntegrable_goldfeldRegularizedContourIntegrand_horizontal
    (beta := beta) hchi1 hchi hcross hx hT
  constructor
  · exact hreg.1.congr fun sigma _hsigma =>
      goldfeldRegularizedContourIntegrand_eq_horizontal_plus
        chi1 chi hzero hT sigma
  · exact hreg.2.congr fun sigma _hsigma =>
      goldfeldRegularizedContourIntegrand_eq_horizontal_minus
        chi1 chi hzero hT sigma

end

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/RectangleReciprocalWedgeIntegral.lean` -/

section

/-!
# Reciprocal integrals on rectangle boundaries

This file evaluates the positively oriented `Complex.wedgeIntegral` boundary
of the simple principal part `c / (s - p)` when `p` is strictly inside an
ordered rectangle. The proof uses only real logarithm and arctangent
antiderivatives from pinned Mathlib.

The result is a generic component for a later finite principal-part
subtraction argument. It defines no residue and proves no finite-hole theorem.
Semantic review: `SEM-520`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory intervalIntegral

noncomputable section

/-- Translating an integrand and both rectangle corners by the same amount
does not change the corresponding wedge integral. -/
theorem wedgeIntegral_comp_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (z w p : ℂ) :
    Complex.wedgeIntegral z w (fun s => f (s - p)) =
      Complex.wedgeIntegral (z - p) (w - p) f := by
  simp_rw [Complex.wedgeIntegral, sub_re, sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  apply congrArg₂ (· + ·)
  · apply intervalIntegral.integral_congr
    intro t _
    apply congrArg f
    apply Complex.ext <;> simp
  · apply congrArg (Complex.I • ·)
    apply intervalIntegral.integral_congr
    intro t _
    apply congrArg f
    apply Complex.ext <;> simp

private lemma sq_add_sq_ne_zero_right (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    x ^ 2 + y ^ 2 ≠ 0 := by
  positivity

private lemma inv_add_mul_I (x y : ℝ) :
    ((x : ℂ) + (y : ℂ) * I)⁻¹ =
      ((x : ℂ) - I * (y : ℂ)) / (x ^ 2 + y ^ 2 : ℝ) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr 1
  · simp [map_add, map_mul]
    ring
  · simp [Complex.normSq]
    ring

private lemma integral_self_div_sq_add_sq {a b y : ℝ} (hy : y ≠ 0) :
    ∫ x in a..b, x / (x ^ 2 + y ^ 2) =
      Real.log (b ^ 2 + y ^ 2) / 2 -
        Real.log (a ^ 2 + y ^ 2) / 2 := by
  let F : ℝ → ℝ := fun x => Real.log (x ^ 2 + y ^ 2) / 2
  have hF : ∀ x : ℝ, HasDerivAt F (x / (x ^ 2 + y ^ 2)) x := by
    intro x
    have hbase :
        HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).add_const (y ^ 2)
    convert! (hbase.log (sq_add_sq_ne_zero_right x hy)).div_const 2 using 1
    field_simp
  have hderiv : deriv F = fun x => x / (x ^ 2 + y ^ 2) :=
    funext fun x => (hF x).deriv
  rw [← hderiv, intervalIntegral.integral_deriv_eq_sub
    (fun x _ => (hF x).differentiableAt)]
  rw [hderiv]
  exact
    (continuous_id.div (continuous_id.pow 2 |>.add continuous_const)
      (fun x => sq_add_sq_ne_zero_right x hy)).intervalIntegrable _ _

private lemma integral_const_div_sq_add_sq {a b y : ℝ} (hy : y ≠ 0) :
    ∫ x in a..b, y / (x ^ 2 + y ^ 2) =
      Real.arctan (b / y) - Real.arctan (a / y) := by
  let F : ℝ → ℝ := fun x => Real.arctan (x / y)
  have hF : ∀ x : ℝ, HasDerivAt F (y / (x ^ 2 + y ^ 2)) x := by
    intro x
    have hquot : HasDerivAt (fun t : ℝ => t / y) (1 / y) x := by
      simpa using hasDerivAt_id x |>.div_const y
    convert! (Real.hasDerivAt_arctan (x / y)).comp x hquot using 1
    field_simp [hy, sq_add_sq_ne_zero_right x hy]
    ring
  have hderiv : deriv F = fun x => y / (x ^ 2 + y ^ 2) :=
    funext fun x => (hF x).deriv
  rw [← hderiv, intervalIntegral.integral_deriv_eq_sub
    (fun x _ => (hF x).differentiableAt)]
  rw [hderiv]
  exact
    (continuous_const.div (continuous_id.pow 2 |>.add continuous_const)
      (fun x => sq_add_sq_ne_zero_right x hy)).intervalIntegrable _ _

private lemma integral_div_add_mul_I {a b y : ℝ} (hy : y ≠ 0) (c : ℂ) :
    ∫ x : ℝ in a..b, c / (x + y * I) =
      c * (Real.log (b ^ 2 + y ^ 2) / 2 -
        Real.log (a ^ 2 + y ^ 2) / 2) -
      c * I * (Real.arctan (b / y) - Real.arctan (a / y)) := by
  have hpoint (x : ℝ) :
      c / (x + y * I) =
        c * (x / (x ^ 2 + y ^ 2) : ℝ) -
          c * I * (y / (x ^ 2 + y ^ 2) : ℝ) := by
    rw [div_eq_mul_inv, inv_add_mul_I]
    push_cast
    ring
  have hdenom : Continuous fun x : ℝ => x ^ 2 + y ^ 2 :=
    continuous_id.pow 2 |>.add continuous_const
  have hxReal : Continuous fun x : ℝ => x / (x ^ 2 + y ^ 2) :=
    continuous_id.div hdenom (fun x => sq_add_sq_ne_zero_right x hy)
  have hyReal : Continuous fun x : ℝ => y / (x ^ 2 + y ^ 2) :=
    continuous_const.div hdenom (fun x => sq_add_sq_ne_zero_right x hy)
  have hx : IntervalIntegrable
      (fun x : ℝ => c * (x / (x ^ 2 + y ^ 2) : ℝ)) volume a b :=
    (continuous_const.mul (continuous_ofReal.comp hxReal)).intervalIntegrable _ _
  have hyi : IntervalIntegrable
      (fun x : ℝ => c * I * (y / (x ^ 2 + y ^ 2) : ℝ)) volume a b :=
    ((continuous_const.mul continuous_const).mul
      (continuous_ofReal.comp hyReal)).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (fun x _ => hpoint x),
    intervalIntegral.integral_sub hx hyi]
  simp_rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, integral_self_div_sq_add_sq hy,
    integral_const_div_sq_add_sq hy]
  push_cast
  rfl

private lemma I_mul_div_add_mul_I (x y : ℝ) (c : ℂ) :
    I * (c / (x + y * I)) = c / (y + (-x) * I) := by
  have hrotate : (y : ℂ) + -(x : ℂ) * I =
      -I * ((x : ℂ) + (y : ℂ) * I) := by
    apply Complex.ext <;> simp
  change I * (c / ((x : ℂ) + (y : ℂ) * I)) =
    c / ((y : ℂ) + -(x : ℂ) * I)
  rw [hrotate]
  simp [div_eq_mul_inv]
  ring

private lemma I_mul_integral_div_add_mul_I
    {a b x : ℝ} (hx : x ≠ 0) (c : ℂ) :
    I * (∫ y : ℝ in a..b, c / (x + y * I)) =
      c * (Real.log (b ^ 2 + (-x) ^ 2) / 2 -
        Real.log (a ^ 2 + (-x) ^ 2) / 2) -
      c * I * (Real.arctan (b / (-x)) - Real.arctan (a / (-x))) := by
  rw [← intervalIntegral.integral_const_mul]
  calc
    (∫ y : ℝ in a..b, I * (c / (x + y * I))) =
        ∫ y : ℝ in a..b, c / (y + (-x) * I) :=
      intervalIntegral.integral_congr fun y _ => I_mul_div_add_mul_I x y c
    _ = _ := by
      simpa using
        (integral_div_add_mul_I (a := a) (b := b)
          (neg_ne_zero.mpr hx) c)

private lemma arctan_div_neg_eq_add_of_div_neg {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x / y < 0) :
    Real.arctan (y / -x) = Real.pi / 2 + Real.arctan (x / y) := by
  have hratio : y / x = (x / y)⁻¹ := by
    field_simp [hx, hy]
  calc
    Real.arctan (y / -x) = -Real.arctan (y / x) := by
      rw [div_neg, Real.arctan_neg]
    _ = -Real.arctan ((x / y)⁻¹) := by rw [hratio]
    _ = Real.pi / 2 + Real.arctan (x / y) := by
      rw [Real.arctan_inv_of_neg hxy]
      ring

private lemma arctan_div_neg_eq_sub_of_div_pos {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : 0 < x / y) :
    Real.arctan (y / -x) = -Real.pi / 2 + Real.arctan (x / y) := by
  have hratio : y / x = (x / y)⁻¹ := by
    field_simp [hx, hy]
  calc
    Real.arctan (y / -x) = -Real.arctan (y / x) := by
      rw [div_neg, Real.arctan_neg]
    _ = -Real.arctan ((x / y)⁻¹) := by rw [hratio]
    _ = -Real.pi / 2 + Real.arctan (x / y) := by
      rw [Real.arctan_inv_of_pos hxy]
      ring

private theorem wedgeIntegral_add_wedgeIntegral_div_of_straddles_zero
    (z w c : ℂ)
    (hzRe : z.re < 0) (hwRe : 0 < w.re)
    (hzIm : z.im < 0) (hwIm : 0 < w.im) :
    Complex.wedgeIntegral z w (fun s => c / s) +
        Complex.wedgeIntegral w z (fun s => c / s) =
      2 * Real.pi * I * c := by
  rw [Complex.wedgeIntegral_add_wedgeIntegral_eq]
  simp only [smul_eq_mul]
  rw [integral_div_add_mul_I hzIm.ne c,
    integral_div_add_mul_I hwIm.ne' c,
    I_mul_integral_div_add_mul_I hwRe.ne' c,
    I_mul_integral_div_add_mul_I hzRe.ne c]
  have h₁ := arctan_div_neg_eq_add_of_div_neg
    hwRe.ne' hzIm.ne (div_neg_of_pos_of_neg hwRe hzIm)
  have h₂ := arctan_div_neg_eq_sub_of_div_pos
    hwRe.ne' hwIm.ne' (div_pos hwRe hwIm)
  have h₃ := arctan_div_neg_eq_sub_of_div_pos
    hzRe.ne hzIm.ne (div_pos_of_neg_of_neg hzRe hzIm)
  have h₄ := arctan_div_neg_eq_add_of_div_neg
    hzRe.ne hwIm.ne' (div_neg_of_neg_of_pos hzRe hwIm)
  rw [h₁, h₂, h₃, h₄]
  push_cast
  ring_nf

/-- The positively oriented boundary integral of `c / (s - p)` is
`2 * pi * I * c` when `p` is strictly inside an ordered rectangle. -/
theorem wedgeIntegral_add_wedgeIntegral_div_sub_eq_two_pi_I_mul
    (z w p c : ℂ)
    (hzRe : z.re < p.re) (hpRe : p.re < w.re)
    (hzIm : z.im < p.im) (hpIm : p.im < w.im) :
    Complex.wedgeIntegral z w (fun s => c / (s - p)) +
        Complex.wedgeIntegral w z (fun s => c / (s - p)) =
      2 * Real.pi * I * c := by
  rw [wedgeIntegral_comp_sub (fun s => c / s) z w p,
    wedgeIntegral_comp_sub (fun s => c / s) w z p]
  apply wedgeIntegral_add_wedgeIntegral_div_of_straddles_zero
  · simpa using sub_neg.mpr hzRe
  · simpa using sub_pos.mpr hpRe
  · simpa using sub_neg.mpr hzIm
  · simpa using sub_pos.mpr hpIm

end

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldContourRectangle.lean` -/

section

/-!
# Goldfeld's finite contour rectangle

The entire Goldfeld numerator is split at the shifted-zeta pole by Mathlib's
filled divided slope. Cauchy kills that analytic remainder, while the exact
reciprocal-rectangle theorem evaluates the retained principal part. The final
identity is stated on the raw source integrand with all four orientations
visible.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 58 and 126,
especially (5.13) and the proof of Theorem 12.9. Semantic review: `SEM-559`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

/-- The entire remainder after subtracting the shifted-zeta principal part. -/
noncomputable def goldfeldContourAnalyticRemainder
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) (s : ℂ) : ℂ :=
  dslope (goldfeldContourNumerator chi1 chi beta x)
    (goldfeldShiftedZetaPole beta) s

/-- The normalized upward vertical integral truncated at ordinates `-T,T`. -/
noncomputable def goldfeldTruncatedVerticalIntegral
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x alpha T : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ t in (-T)..T,
      goldfeldContourIntegrand chi1 chi beta x
        ((alpha : ℂ) + t * I)

/-- The source-oriented lower horizontal contribution. Its explicit minus
reverses the left-to-right scalar parameterization. -/
noncomputable def goldfeldTruncatedLowerIntegral
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x T : ℝ) : ℂ :=
  ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) *
    (-(∫ sigma in (-1)..2,
      goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I)))

/-- The source-oriented upper horizontal contribution. -/
noncomputable def goldfeldTruncatedUpperIntegral
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x T : ℝ) : ℂ :=
  ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) *
    ∫ sigma in (-1)..2,
      goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I)

/-- The numerator divided slope is entire whenever the numerator is. -/
theorem differentiable_goldfeldContourAnalyticRemainder
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1}
    {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    (beta : ℝ) {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ
      (goldfeldContourAnalyticRemainder chi1 chi beta x) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope Filter.univ_mem).2
    (differentiable_goldfeldContourNumerator
      hchi1 hchi hcross beta hx).differentiableOn

/-- Off the shifted pole, the filled integrand is its entire remainder plus
the exact reciprocal principal part. -/
theorem goldfeldRegularizedContourIntegrand_eq_remainder_add
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : beta < 1)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    {s : ℂ} (hs : s ≠ goldfeldShiftedZetaPole beta) :
    goldfeldRegularizedContourIntegrand chi1 chi beta x s =
      goldfeldContourAnalyticRemainder chi1 chi beta x s +
        goldfeldContourResidue chi1 chi beta x /
          (s - goldfeldShiftedZetaPole beta) := by
  have hnum := sub_smul_dslope
    (goldfeldContourNumerator chi1 chi beta x)
    (goldfeldShiftedZetaPole beta) s
  have hp := goldfeldContourNumerator_apply_shiftedZetaPole
    chi1 chi (x := x) hbeta hzero
  rw [hp] at hnum
  unfold goldfeldRegularizedContourIntegrand
    goldfeldContourAnalyticRemainder
  have hsub : s - goldfeldShiftedZetaPole beta ≠ 0 :=
    sub_ne_zero.mpr hs
  simp only [smul_eq_mul] at hnum
  apply (div_eq_iff hsub).2
  rw [add_mul, div_mul_cancel₀ _ hsub]
  calc
    goldfeldContourNumerator chi1 chi beta x s =
        (goldfeldContourNumerator chi1 chi beta x s -
          goldfeldContourResidue chi1 chi beta x) +
          goldfeldContourResidue chi1 chi beta x := by ring
    _ = (s - goldfeldShiftedZetaPole beta) *
          dslope (goldfeldContourNumerator chi1 chi beta x)
            (goldfeldShiftedZetaPole beta) s +
          goldfeldContourResidue chi1 chi beta x := by rw [hnum]
    _ = dslope (goldfeldContourNumerator chi1 chi beta x)
          (goldfeldShiftedZetaPole beta) s *
          (s - goldfeldShiftedZetaPole beta) +
          goldfeldContourResidue chi1 chi beta x := by ring

private lemma continuous_horizontal_principal_part
    (c p : ℂ) (y : ℝ) (hy : y ≠ p.im) :
    Continuous (fun t : ℝ => c / ((t : ℂ) + y * I - p)) := by
  apply Continuous.div continuous_const
    ((continuous_ofReal.add (continuous_const.mul continuous_const)).sub
      continuous_const)
  intro t
  apply sub_ne_zero.mpr
  intro h
  apply hy
  simpa using congrArg Complex.im h

private lemma continuous_vertical_principal_part
    (c p : ℂ) (x : ℝ) (hx : x ≠ p.re) :
    Continuous (fun t : ℝ => c / ((x : ℂ) + t * I - p)) := by
  apply Continuous.div continuous_const
    ((continuous_const.add (continuous_ofReal.mul continuous_const)).sub
      continuous_const)
  intro t
  apply sub_ne_zero.mpr
  intro h
  apply hx
  simpa using congrArg Complex.re h

private theorem rectangle_boundary_eq_two_pi_I_mul_of_decomposition
    (f F : ℂ → ℂ) (z w p c : ℂ)
    (hF : Differentiable ℂ F)
    (hdecomp : ∀ s, s ≠ p → f s = F s + c / (s - p))
    (hzRe : z.re < p.re) (hpRe : p.re < w.re)
    (hzIm : z.im < p.im) (hpIm : p.im < w.im) :
    Complex.wedgeIntegral z w f + Complex.wedgeIntegral w z f =
      (2 * Real.pi * I) * c := by
  let G : ℂ → ℂ := fun s => c / (s - p)
  have hFcontinuous : Continuous F := hF.continuous
  have hFbottom : IntervalIntegrable
      (fun t : ℝ => F ((t : ℂ) + z.im * I)) volume z.re w.re :=
    (hFcontinuous.comp (by fun_prop)).intervalIntegrable _ _
  have hFtop : IntervalIntegrable
      (fun t : ℝ => F ((t : ℂ) + w.im * I)) volume w.re z.re :=
    (hFcontinuous.comp (by fun_prop)).intervalIntegrable _ _
  have hFright : IntervalIntegrable
      (fun t : ℝ => F ((w.re : ℂ) + t * I)) volume z.im w.im :=
    (hFcontinuous.comp (by fun_prop)).intervalIntegrable _ _
  have hFleft : IntervalIntegrable
      (fun t : ℝ => F ((z.re : ℂ) + t * I)) volume w.im z.im :=
    (hFcontinuous.comp (by fun_prop)).intervalIntegrable _ _
  have hGbottom : IntervalIntegrable
      (fun t : ℝ => G ((t : ℂ) + z.im * I)) volume z.re w.re := by
    exact (continuous_horizontal_principal_part c p z.im
      (ne_of_lt hzIm)).intervalIntegrable _ _
  have hGtop : IntervalIntegrable
      (fun t : ℝ => G ((t : ℂ) + w.im * I)) volume w.re z.re := by
    exact (continuous_horizontal_principal_part c p w.im
      (ne_of_gt hpIm)).intervalIntegrable _ _
  have hGright : IntervalIntegrable
      (fun t : ℝ => G ((w.re : ℂ) + t * I)) volume z.im w.im := by
    exact (continuous_vertical_principal_part c p w.re
      (ne_of_gt hpRe)).intervalIntegrable _ _
  have hGleft : IntervalIntegrable
      (fun t : ℝ => G ((z.re : ℂ) + t * I)) volume w.im z.im := by
    exact (continuous_vertical_principal_part c p z.re
      (ne_of_lt hzRe)).intervalIntegrable _ _
  have hnotBottom (t : ℝ) : (t : ℂ) + z.im * I ≠ p := by
    intro h
    exact (ne_of_lt hzIm) (by simpa using congrArg Complex.im h)
  have hnotTop (t : ℝ) : (t : ℂ) + w.im * I ≠ p := by
    intro h
    exact (ne_of_gt hpIm) (by simpa using congrArg Complex.im h)
  have hnotRight (t : ℝ) : (w.re : ℂ) + t * I ≠ p := by
    intro h
    exact (ne_of_gt hpRe) (by simpa using congrArg Complex.re h)
  have hnotLeft (t : ℝ) : (z.re : ℂ) + t * I ≠ p := by
    intro h
    exact (ne_of_lt hzRe) (by simpa using congrArg Complex.re h)
  have hbottom :
      (∫ t : ℝ in z.re..w.re, f ((t : ℂ) + z.im * I)) =
        ∫ t : ℝ in z.re..w.re,
          F ((t : ℂ) + z.im * I) + G ((t : ℂ) + z.im * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hdecomp _ (hnotBottom t)
  have htop :
      (∫ t : ℝ in w.re..z.re, f ((t : ℂ) + w.im * I)) =
        ∫ t : ℝ in w.re..z.re,
          F ((t : ℂ) + w.im * I) + G ((t : ℂ) + w.im * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hdecomp _ (hnotTop t)
  have hright :
      (∫ t : ℝ in z.im..w.im, f ((w.re : ℂ) + t * I)) =
        ∫ t : ℝ in z.im..w.im,
          F ((w.re : ℂ) + t * I) + G ((w.re : ℂ) + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hdecomp _ (hnotRight t)
  have hleft :
      (∫ t : ℝ in w.im..z.im, f ((z.re : ℂ) + t * I)) =
        ∫ t : ℝ in w.im..z.im,
          F ((z.re : ℂ) + t * I) + G ((z.re : ℂ) + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hdecomp _ (hnotLeft t)
  have hzw : Complex.wedgeIntegral z w f =
      Complex.wedgeIntegral z w F + Complex.wedgeIntegral z w G := by
    simp only [Complex.wedgeIntegral]
    rw [hbottom, hright,
      intervalIntegral.integral_add hFbottom hGbottom,
      intervalIntegral.integral_add hFright hGright]
    simp only [smul_add]
    abel
  have hwz : Complex.wedgeIntegral w z f =
      Complex.wedgeIntegral w z F + Complex.wedgeIntegral w z G := by
    simp only [Complex.wedgeIntegral]
    rw [htop, hleft,
      intervalIntegral.integral_add hFtop hGtop,
      intervalIntegral.integral_add hFleft hGleft]
    simp only [smul_add]
    abel
  have hFzero : Complex.wedgeIntegral z w F +
      Complex.wedgeIntegral w z F = 0 := by
    have hconservative := hF.differentiableOn.isConservativeOn z w
      (fun _ _ => mem_univ _)
    rw [hconservative]
    simp
  have hGsum : Complex.wedgeIntegral z w G +
      Complex.wedgeIntegral w z G = (2 * Real.pi * I) * c := by
    exact wedgeIntegral_add_wedgeIntegral_div_sub_eq_two_pi_I_mul
      z w p c hzRe hpRe hzIm hpIm
  rw [hzw, hwz]
  calc
    (Complex.wedgeIntegral z w F + Complex.wedgeIntegral z w G) +
        (Complex.wedgeIntegral w z F + Complex.wedgeIntegral w z G) =
      (Complex.wedgeIntegral z w F + Complex.wedgeIntegral w z F) +
        (Complex.wedgeIntegral z w G + Complex.wedgeIntegral w z G) := by
          abel
    _ = (2 * Real.pi * I) * c := by rw [hFzero, hGsum, zero_add]

/-- The filled Goldfeld integrand has the exact positive rectangle boundary
integral. The scalar lower and upper paths are both parameterized
left-to-right; the displayed signs encode the positive boundary. -/
theorem goldfeldRegularizedContourIntegrand_rectangle_boundary_eq
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 0 < x) (hT : 1 ≤ T)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    (∫ sigma in (-1)..2,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((sigma : ℂ) - T * I)) -
      (∫ sigma in (-1)..2,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((sigma : ℂ) + T * I)) +
      I * (∫ t in (-T)..T,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((2 : ℂ) + t * I)) -
      I * (∫ t in (-T)..T,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((-1 : ℂ) + t * I)) =
      (2 * Real.pi * I) *
        goldfeldContourResidue chi1 chi beta x := by
  let z : ℂ := (-1 : ℂ) - T * I
  let w : ℂ := (2 : ℂ) + T * I
  let p : ℂ := goldfeldShiftedZetaPole beta
  let f : ℂ → ℂ := goldfeldRegularizedContourIntegrand chi1 chi beta x
  let F : ℂ → ℂ := goldfeldContourAnalyticRemainder chi1 chi beta x
  let c : ℂ := goldfeldContourResidue chi1 chi beta x
  have hzRe : z.re < p.re := by
    simp [z, p, goldfeldShiftedZetaPole]
    linarith
  have hpRe : p.re < w.re := by
    simp [w, p, goldfeldShiftedZetaPole]
    linarith
  have hzIm : z.im < p.im := by
    simp [z, p, goldfeldShiftedZetaPole]
    linarith
  have hpIm : p.im < w.im := by
    simp [w, p, goldfeldShiftedZetaPole]
    linarith
  have hboundary := rectangle_boundary_eq_two_pi_I_mul_of_decomposition
    f F z w p c
    (differentiable_goldfeldContourAnalyticRemainder
      hchi1 hchi hcross beta hx)
    (fun s hs => goldfeldRegularizedContourIntegrand_eq_remainder_add
      chi1 chi hbeta1 hzero hs)
    hzRe hpRe hzIm hpIm
  rw [Complex.wedgeIntegral_add_wedgeIntegral_eq] at hboundary
  simpa [f, F, c, z, w, p, smul_eq_mul, sub_eq_add_neg] using hboundary

/-- The exact finite source decomposition, with the lower side reversed and
all vertical parameterizations upward. -/
theorem goldfeldContourIntegrand_truncated_rectangle_decomposition
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 0 < x) (hT : 1 ≤ T)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    goldfeldTruncatedVerticalIntegral chi1 chi beta x 2 T =
      goldfeldTruncatedLowerIntegral chi1 chi beta x T +
        goldfeldTruncatedVerticalIntegral chi1 chi beta x (-1) T +
        goldfeldTruncatedUpperIntegral chi1 chi beta x T +
        goldfeldContourResidue chi1 chi beta x := by
  have hboundary :=
    goldfeldRegularizedContourIntegrand_rectangle_boundary_eq
      chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hx hT hzero
  have hhorizontal :=
    goldfeldRegularizedContourIntegrand_eq_intervalIntegral_goldfeldContourIntegrand_horizontal
      (chi1 := chi1) (chi := chi) (x := x) hzero hT
  have hright :
      (∫ t in (-T)..T,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((2 : ℂ) + t * I)) =
      ∫ t in (-T)..T,
        goldfeldContourIntegrand chi1 chi beta x
          ((2 : ℂ) + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact goldfeldRegularizedContourIntegrand_eq_contourIntegrand
      chi1 chi hzero (by
        intro hs
        have hre := congrArg Complex.re hs
        norm_num at hre)
      (by
        intro hs
        have hre := congrArg Complex.re hs
        simp [goldfeldShiftedZetaPole] at hre
        linarith)
  have hleft :
      (∫ t in (-T)..T,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((-1 : ℂ) + t * I)) =
      ∫ t in (-T)..T,
        goldfeldContourIntegrand chi1 chi beta x
          ((-1 : ℂ) + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact goldfeldRegularizedContourIntegrand_eq_contourIntegrand
      chi1 chi hzero (by
        intro hs
        have hre := congrArg Complex.re hs
        norm_num at hre)
      (by
        intro hs
        have hre := congrArg Complex.re hs
        simp [goldfeldShiftedZetaPole] at hre
        linarith)
  rw [hhorizontal.2, hhorizontal.1, hright, hleft] at hboundary
  let lower : ℂ := ∫ sigma in (-1)..2,
    goldfeldContourIntegrand chi1 chi beta x
      ((sigma : ℂ) - T * I)
  let upper : ℂ := ∫ sigma in (-1)..2,
    goldfeldContourIntegrand chi1 chi beta x
      ((sigma : ℂ) + T * I)
  let right : ℂ := ∫ t in (-T)..T,
    goldfeldContourIntegrand chi1 chi beta x
      ((2 : ℂ) + t * I)
  let left : ℂ := ∫ t in (-T)..T,
    goldfeldContourIntegrand chi1 chi beta x
      ((-1 : ℂ) + t * I)
  change lower - upper + I * right - I * left =
    (2 * Real.pi * I) * goldfeldContourResidue chi1 chi beta x at hboundary
  have hIright :
      I * right =
        (2 * Real.pi * I) * goldfeldContourResidue chi1 chi beta x -
          lower + upper + I * left := by
    linear_combination hboundary
  have hmainMul :
      -I * ((2 * Real.pi * I) *
        goldfeldContourResidue chi1 chi beta x) =
        (((2 * Real.pi : ℝ) : ℂ)) *
          goldfeldContourResidue chi1 chi beta x := by
    calc
      _ = (-I * I) * ((((2 * Real.pi : ℝ) : ℂ)) *
          goldfeldContourResidue chi1 chi beta x) := by
        push_cast
        ring
      _ = _ := by rw [neg_mul, I_mul_I]; simp
  have hleftMul : -I * (I * left) = left := by
    rw [← mul_assoc, neg_mul, I_mul_I]
    simp
  have hrightEq :
      right = (((2 * Real.pi : ℝ) : ℂ)) *
          goldfeldContourResidue chi1 chi beta x +
        I * lower - I * upper + left := by
    calc
      _ = -I * (I * right) := by
        rw [← mul_assoc, neg_mul, I_mul_I]
        simp
      _ = -I * ((2 * Real.pi * I) *
          goldfeldContourResidue chi1 chi beta x -
          lower + upper + I * left) := by rw [hIright]
      _ = _ := by
        rw [mul_add, mul_add, mul_sub, hmainMul, hleftMul]
        ring
  simp only [goldfeldTruncatedVerticalIntegral,
    goldfeldTruncatedLowerIntegral, goldfeldTruncatedUpperIntegral]
  norm_num only [ofReal_neg, ofReal_one]
  change (((2 * Real.pi : ℝ) : ℂ)⁻¹) * right =
    ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) * (-lower) +
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) * left +
      ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) * upper +
      goldfeldContourResidue chi1 chi beta x
  have hpi : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast Real.two_pi_pos.ne'
  rw [hrightEq]
  field_simp [hpi, I_ne_zero]
  simp [mul_add, mul_sub, ← mul_assoc, I_mul_I]
  ring

end

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldHorizontalEdgeLimit.lean` -/

section

/-!
# Goldfeld horizontal-edge integral limits

This file applies the pointwise envelope only after the raw horizontal paths
have been proved genuinely interval-integrable. It then retains the source
orientation while sending the upper and lower sides to zero.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 58, 74,
125--127, especially (5.13), (7.9), and the proof of Theorem 12.9.
Semantic review: `SEM-557`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory Set Filter
open scoped Interval Topology

noncomputable section

private theorem norm_intervalIntegral_le_const_of_intervalIntegrable
    {f : ℝ → ℂ} {a b M : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hpoint : ∀ x ∈ Icc a b, ‖f x‖ ≤ M) :
    ‖∫ x in a..b, f x‖ ≤ M * (b - a) := by
  calc
    ‖∫ x in a..b, f x‖ ≤ ∫ x in a..b, ‖f x‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ _x in a..b, M :=
      intervalIntegral.integral_mono_on hab hf.norm
        intervalIntegrable_const hpoint
    _ = M * (b - a) := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]
      ring

/-- The two left-to-right horizontal integrals inherit the pointwise decay;
the factor `3` is the length of the closed strip. -/
theorem exists_norm_intervalIntegral_goldfeldContourIntegrand_horizontal_le :
    ∃ A : ℕ, 57 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta x T : ℝ),
            0 ≤ beta → beta ≤ 1 → 1 ≤ x → 1 ≤ T →
            DirichletCharacter.LFunction chi1 (beta : ℂ) = 0 →
            (‖∫ sigma in (-1)..2,
              goldfeldContourIntegrand chi1 chi beta x
                ((sigma : ℂ) + T * I)‖ ≤
                3 * C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2) ∧
            (‖∫ sigma in (-1)..2,
              goldfeldContourIntegrand chi1 chi beta x
                ((sigma : ℂ) - T * I)‖ ≤
                3 * C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2) := by
  obtain ⟨A, hA, C, hC, hpoint⟩ :=
    exists_norm_goldfeldContourIntegrand_horizontal_le
  refine ⟨A, hA, C, hC, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta x T hbeta0 hbeta1 hx hT hzero
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTabs : 1 ≤ |T| := by simpa [abs_of_pos hTpos] using hT
  have hraw := intervalIntegrable_goldfeldContourIntegrand_horizontal
    (beta := beta) hchi1 hchi hcross (zero_lt_one.trans_le hx) hT hzero
  have hplusBound : ∀ sigma ∈ Icc (-(1 : ℝ)) 2,
      ‖goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I)‖ ≤
        C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2 := by
    intro sigma hsigma
    exact hpoint q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
      beta x sigma T hbeta0 hbeta1 hx hsigma hTabs
  have hminusBound : ∀ sigma ∈ Icc (-(1 : ℝ)) 2,
      ‖goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I)‖ ≤
        C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2 := by
    intro sigma hsigma
    have h := hpoint q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
      beta x sigma (-T) hbeta0 hbeta1 hx hsigma
      (by simpa [abs_of_pos hTpos, abs_neg] using hT)
    simpa [sub_eq_add_neg, abs_neg] using h
  have hplus := norm_intervalIntegral_le_const_of_intervalIntegrable
    (by norm_num : (-1 : ℝ) ≤ 2) hraw.1 hplusBound
  have hminus := norm_intervalIntegral_le_const_of_intervalIntegrable
    (by norm_num : (-1 : ℝ) ≤ 2) hraw.2 hminusBound
  constructor
  · calc
      ‖∫ sigma in (-1)..2,
          goldfeldContourIntegrand chi1 chi beta x
            ((sigma : ℂ) + T * I)‖ ≤
          (C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2) *
            ((2 : ℝ) - (-1)) := hplus
      _ = 3 * C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2 := by ring
  · calc
      ‖∫ sigma in (-1)..2,
          goldfeldContourIntegrand chi1 chi beta x
            ((sigma : ℂ) - T * I)‖ ≤
          (C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2) *
            ((2 : ℝ) - (-1)) := hminus
      _ = 3 * C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2 := by ring

/-- With the source orientation, the upper edge is left-to-right and the lower
edge is the negative of the left-to-right integral. Both vanish at infinity. -/
theorem exists_tendsto_goldfeldContourIntegrand_horizontal_integrals_zero :
    ∃ A : ℕ, 57 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta x : ℝ),
            0 ≤ beta → beta ≤ 1 → 1 ≤ x →
            DirichletCharacter.LFunction chi1 (beta : ℂ) = 0 →
            Tendsto
              (fun T : ℝ => ∫ sigma in (-1)..2,
                goldfeldContourIntegrand chi1 chi beta x
                  ((sigma : ℂ) + T * I)) atTop (𝓝 0) ∧
            Tendsto
              (fun T : ℝ => -(∫ sigma in (-1)..2,
                goldfeldContourIntegrand chi1 chi beta x
                  ((sigma : ℂ) - T * I))) atTop (𝓝 0) := by
  obtain ⟨A, hA, C, hC, hbound⟩ :=
    exists_norm_intervalIntegral_goldfeldContourIntegrand_horizontal_le
  refine ⟨A, hA, C, hC, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta x hbeta0 hbeta1 hx hzero
  let K : ℝ := 3 * C * (q : ℝ) ^ A * x ^ 2
  have hlinear : Tendsto (fun T : ℝ => 1 + T) atTop atTop := by
    simpa [add_comm] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop))
  have hsquare : Tendsto (fun T : ℝ => (1 + T) ^ 2) atTop atTop := by
    have h := tendsto_mul_self_atTop.comp hlinear
    simpa [Function.comp_def, pow_two] using h
  have hdecay : Tendsto (fun T : ℝ => K / (1 + T) ^ 2)
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsquare
  have hupperNorm : Tendsto
      (fun T : ℝ => ‖∫ sigma in (-1)..2,
        goldfeldContourIntegrand chi1 chi beta x
          ((sigma : ℂ) + T * I)‖) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun T : ℝ => K / (1 + T) ^ 2)
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have h := (hbound q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
        beta x T hbeta0 hbeta1 hx hT hzero).1
      simpa [K, abs_of_nonneg (zero_le_one.trans hT)] using h
    · exact hdecay
  have hlowerNorm : Tendsto
      (fun T : ℝ => ‖-(∫ sigma in (-1)..2,
        goldfeldContourIntegrand chi1 chi beta x
          ((sigma : ℂ) - T * I))‖) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun T : ℝ => K / (1 + T) ^ 2)
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have h := (hbound q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
        beta x T hbeta0 hbeta1 hx hT hzero).2
      simpa [K, norm_neg, abs_of_nonneg (zero_le_one.trans hT)] using h
    · exact hdecay
  exact ⟨tendsto_zero_iff_norm_tendsto_zero.mpr hupperNorm,
    tendsto_zero_iff_norm_tendsto_zero.mpr hlowerNorm⟩

end

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldContourLimit.lean` -/

section

/-!
# Goldfeld's complete contour displacement

The raw right line is proved genuinely Bochner integrable from absolute
Dirichlet-series convergence and the already established Mellin integrability.
Both finite vertical edges then converge to their complete lines, and SEM-557
sends the source-oriented horizontal edges to zero. This turns SEM-559's exact
finite rectangle into `I_2 = residue + I_(-1)`.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 73--74 and
125--126, especially (7.9) and Theorem 12.9. Semantic review: `SEM-559`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory Filter
open scoped Topology

noncomputable section

private theorem continuous_goldfeldRightLineMultiplier
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : -1 < beta) (hx : 0 < x) :
    Continuous (fun t : ℝ =>
      goldfeldFourFactorLFunction chi1 chi
          (((2 : ℂ) + t * I) + (beta : ℂ)) *
        (x : ℂ) ^ ((2 : ℂ) + t * I)) := by
  let s : ℝ → ℂ := fun t => (2 : ℂ) + t * I
  have hs : Continuous s := by fun_prop
  have hshift : Continuous (fun t : ℝ => s t + (beta : ℂ)) :=
    hs.add continuous_const
  have hnotOne (t : ℝ) : s t + (beta : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    linarith
  have hzeta : Continuous (fun t : ℝ =>
      riemannZeta (s t + (beta : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    simpa [Function.comp_def] using
      (differentiableAt_riemannZeta (hnotOne t)).continuousAt.comp
        (f := fun u : ℝ => s u + (beta : ℂ)) hshift.continuousAt
  have hchi1 : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction chi1 (s t + (beta : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    simpa [Function.comp_def] using
      (DirichletCharacter.differentiableAt_LFunction chi1
        (s t + (beta : ℂ)) (.inl (hnotOne t))).continuousAt.comp
          (f := fun u : ℝ => s u + (beta : ℂ)) hshift.continuousAt
  have hchi : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction chi (s t + (beta : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    simpa [Function.comp_def] using
      (DirichletCharacter.differentiableAt_LFunction chi
        (s t + (beta : ℂ)) (.inl (hnotOne t))).continuousAt.comp
          (f := fun u : ℝ => s u + (beta : ℂ)) hshift.continuousAt
  have hcross : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
        (s t + (beta : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    simpa [Function.comp_def] using
      (DirichletCharacter.differentiableAt_LFunction
        (DirichletCharacter.mul chi1 chi)
        (s t + (beta : ℂ)) (.inl (hnotOne t))).continuousAt.comp
          (f := fun u : ℝ => s u + (beta : ℂ)) hshift.continuousAt
  have hxpow : Continuous (fun t : ℝ => (x : ℂ) ^ (s t)) :=
    continuous_const.cpow hs fun _ => Complex.ofReal_mem_slitPlane.mpr hx
  have hfour := (((hzeta.mul hchi1).mul hchi).mul hcross)
  change Continuous (fun t : ℝ =>
    (((riemannZeta (s t + (beta : ℂ)) *
      DirichletCharacter.LFunction chi1 (s t + (beta : ℂ))) *
      DirichletCharacter.LFunction chi (s t + (beta : ℂ))) *
      DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
        (s t + (beta : ℂ))) * (x : ℂ) ^ (s t))
  exact hfour.mul hxpow

/-- The complete raw right line `Re(s)=2` is genuinely Bochner integrable.
No nonprincipal-character premise is needed in the half-plane of absolute
Dirichlet-series convergence. -/
theorem goldfeldContourIntegrand_two_verticalIntegrable
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : -1 < beta) (hx : 0 < x) :
    VerticalIntegrable
      (goldfeldContourIntegrand chi1 chi beta x) 2 := by
  let a : ℕ → ℂ := goldfeldBetaCoefficient chi1 chi beta
  let s : ℝ → ℂ := fun t => (2 : ℂ) + t * I
  let phiLine : ℝ → ℂ := fun t => goldfeldRawMellin (s t)
  let multiplier : ℝ → ℂ := fun t =>
    goldfeldFourFactorLFunction chi1 chi (s t + (beta : ℂ)) *
      (x : ℂ) ^ (s t)
  have hsum : LSeriesSummable a (2 : ℂ) := by
    apply (goldfeldBetaCoefficient_LSeriesHasSum
      chi1 chi beta (s := (2 : ℂ)) ?_).LSeriesSummable
    norm_num
    linarith
  let K : ℝ := ∑' n : ℕ, ‖LSeries.term a (2 : ℂ) n‖
  have hfactor (t : ℝ) :
      ‖goldfeldFourFactorLFunction chi1 chi
        (s t + (beta : ℂ))‖ ≤ K := by
    have hsReal : 1 < ((s t + (beta : ℂ))).re := by
      simp [s]
      linarith
    have hseries := goldfeldBetaCoefficient_LSeriesHasSum
      chi1 chi beta (s := s t) hsReal
    have hline : LSeriesSummable a (s t) := by
      simpa [a] using hseries.LSeriesSummable
    have hlineNorm : Summable fun n : ℕ => ‖LSeries.term a (s t) n‖ :=
      summable_norm_iff.mpr hline
    calc
      ‖goldfeldFourFactorLFunction chi1 chi
          (s t + (beta : ℂ))‖ = ‖LSeries a (s t)‖ := by
            rw [hseries.LSeries_eq]
      _ ≤ ∑' n : ℕ, ‖LSeries.term a (s t) n‖ :=
        norm_tsum_le_tsum_norm hlineNorm
      _ = K := by
        apply tsum_congr
        intro n
        simp only [LSeries.norm_term_eq]
        congr 2
        simp [s]
  have hmultiplierContinuous : Continuous multiplier := by
    simpa [multiplier, s] using
      continuous_goldfeldRightLineMultiplier chi1 chi hbeta hx
  have hmultiplierBound : ∀ᵐ t : ℝ, ‖multiplier t‖ ≤ K * x ^ 2 :=
    ae_of_all _ fun t => by
      simp only [multiplier, norm_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      have hxpow : x ^ (s t).re = x ^ 2 := by
        rw [show (s t).re = 2 by simp [s], Real.rpow_two]
      rw [hxpow]
      exact mul_le_mul_of_nonneg_right (hfactor t) (sq_nonneg x)
  have hphi : Integrable phiLine := by
    simpa [phiLine, s, VerticalIntegrable] using
      (goldfeldRawMellin_verticalIntegrable (alpha := 2) (by norm_num))
  have hproduct : Integrable fun t => phiLine t * multiplier t :=
    hphi.mul_bdd hmultiplierContinuous.aestronglyMeasurable
      hmultiplierBound
  rw [VerticalIntegrable]
  refine hproduct.congr (ae_of_all _ fun t => ?_)
  change phiLine t * multiplier t =
    goldfeldContourIntegrand chi1 chi beta x (s t)
  have hPhi := goldfeldMellinContinuationData.agrees_on_right
    (s := s t) (by simp [s])
  rw [goldfeldContourIntegrand, hPhi]
  simp only [phiLine, multiplier, s]
  ring

private theorem tendsto_goldfeldTruncatedVerticalIntegral_of_verticalIntegrable
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x alpha : ℝ)
    (hvertical : VerticalIntegrable
      (goldfeldContourIntegrand chi1 chi beta x) alpha) :
    Tendsto
      (goldfeldTruncatedVerticalIntegral chi1 chi beta x alpha)
      atTop
      (𝓝 (goldfeldVerticalIntegral chi1 chi beta x alpha)) := by
  let f : ℝ → ℂ := fun t =>
    goldfeldContourIntegrand chi1 chi beta x
      ((alpha : ℂ) + t * I)
  have hraw : Integrable f := by
    simpa [VerticalIntegrable, f] using hvertical
  have hlimit := MeasureTheory.intervalIntegral_tendsto_integral hraw
    tendsto_neg_atTop_atBot tendsto_id
  have hnormalized := hlimit.const_mul (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  change Tendsto
    (fun T : ℝ => (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
      ∫ t in (-T)..T, f t) atTop
    (𝓝 ((((2 * Real.pi : ℝ) : ℂ)⁻¹) * ∫ t : ℝ, f t))
  exact hnormalized

/-- The normalized truncated right edge converges to the complete `I_2`. -/
theorem tendsto_goldfeldContourIntegrand_truncated_vertical_two
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : -1 < beta) (hx : 0 < x) :
    Tendsto
      (goldfeldTruncatedVerticalIntegral chi1 chi beta x 2)
      atTop
      (𝓝 (goldfeldVerticalIntegral chi1 chi beta x 2)) :=
  tendsto_goldfeldTruncatedVerticalIntegral_of_verticalIntegrable
    chi1 chi beta x 2
      (goldfeldContourIntegrand_two_verticalIntegrable
        chi1 chi hbeta hx)

/-- The normalized truncated left edge converges to the complete `I_(-1)`. -/
theorem tendsto_goldfeldContourIntegrand_truncated_vertical_neg_one
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ} (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (hx : 1 ≤ x) :
    Tendsto
      (goldfeldTruncatedVerticalIntegral chi1 chi beta x (-1))
      atTop
      (𝓝 (goldfeldVerticalIntegral chi1 chi beta x (-1))) :=
  tendsto_goldfeldTruncatedVerticalIntegral_of_verticalIntegrable
    chi1 chi beta x (-1)
      (goldfeldContourIntegrand_leftLine_verticalIntegrable
        hq1 hq1q chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hx)

/-- Goldfeld's complete contour displacement: the right line is the exact
shifted-zeta residue plus the upward left line. -/
theorem goldfeldVerticalIntegral_two_eq_residue_add_neg_one
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 1 ≤ x)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    goldfeldVerticalIntegral chi1 chi beta x 2 =
      goldfeldContourResidue chi1 chi beta x +
        goldfeldVerticalIntegral chi1 chi beta x (-1) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hright := tendsto_goldfeldContourIntegrand_truncated_vertical_two
    chi1 chi (show -1 < beta by linarith) hxpos
  have hleft := tendsto_goldfeldContourIntegrand_truncated_vertical_neg_one
    hq1 hq1q chi1 chi hchi1 hchi hcross hbeta0 hbeta1.le hx
  obtain ⟨_A, _hA, _C, _hC, hhorizontal⟩ :=
    exists_tendsto_goldfeldContourIntegrand_horizontal_integrals_zero
  have hedges := hhorizontal q1 q hq1 hq1q chi1 chi
    hchi1 hchi hcross beta x hbeta0 hbeta1.le hx hzero
  have hlower : Tendsto
      (goldfeldTruncatedLowerIntegral chi1 chi beta x)
      atTop (𝓝 0) := by
    have h := hedges.2.const_mul
      ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹)
    change Tendsto (fun T : ℝ =>
      ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) *
        (-(∫ sigma in (-1)..2,
          goldfeldContourIntegrand chi1 chi beta x
            ((sigma : ℂ) - T * I)))) atTop (𝓝 0)
    simpa only [mul_zero] using h
  have hupper : Tendsto
      (goldfeldTruncatedUpperIntegral chi1 chi beta x)
      atTop (𝓝 0) := by
    have h := hedges.1.const_mul
      ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹)
    change Tendsto (fun T : ℝ =>
      ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) *
        ∫ sigma in (-1)..2,
          goldfeldContourIntegrand chi1 chi beta x
            ((sigma : ℂ) + T * I)) atTop (𝓝 0)
    simpa only [mul_zero] using h
  let rhs : ℝ → ℂ := fun T =>
    goldfeldTruncatedLowerIntegral chi1 chi beta x T +
      goldfeldTruncatedVerticalIntegral chi1 chi beta x (-1) T +
      goldfeldTruncatedUpperIntegral chi1 chi beta x T +
      goldfeldContourResidue chi1 chi beta x
  have hrhs : Tendsto rhs atTop
      (𝓝 (goldfeldVerticalIntegral chi1 chi beta x (-1) +
        goldfeldContourResidue chi1 chi beta x)) := by
    have hconstant : Tendsto
        (fun _ : ℝ => goldfeldContourResidue chi1 chi beta x) atTop
        (𝓝 (goldfeldContourResidue chi1 chi beta x)) :=
      tendsto_const_nhds
    have h := ((hlower.add hleft).add hupper).add hconstant
    simpa [rhs] using h
  have heq :
      (goldfeldTruncatedVerticalIntegral chi1 chi beta x 2) =ᶠ[atTop]
        rhs := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact goldfeldContourIntegrand_truncated_rectangle_decomposition
      chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hxpos hT hzero
  have hright' := hright.congr' heq
  have hresult := tendsto_nhds_unique hright' hrhs
  simpa [add_comm] using hresult

/-- Source-facing form of the contour displacement after the already verified
Mellin inversion identity `S=I_2`. -/
theorem goldfeldSmoothedSum_eq_residue_add_verticalIntegral_neg_one
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 1 ≤ x)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    goldfeldSmoothedSum chi1 chi beta x =
      goldfeldContourResidue chi1 chi beta x +
        goldfeldVerticalIntegral chi1 chi beta x (-1) := by
  rw [goldfeldSmoothedSum_eq_verticalIntegral_two
    chi1 chi (show -1 < beta by linarith) hx]
  exact goldfeldVerticalIntegral_two_eq_residue_add_neg_one
    hq1 hq1q chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hx hzero

end

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/ImprimitivePolyaVinogradovPrefix.lean` -/

section

/-!
# Polya--Vinogradov for imprimitive prefixes

This file proves the all-nonprincipal natural-prefix specialization of
KoukoulopoulosDistributionPrimesPrelim2022, Theorem 10.6, needed on printed
p. 125. The explicit factor `2` comes from pairing divisors of the quotient
of the modulus by the conductor; the source states only an absolute constant.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators

private theorem card_divisors_le_two_mul_sqrt
    {n : ℕ} (hn : 0 < n) :
    n.divisors.card ≤ 2 * Nat.sqrt n := by
  classical
  let small := n.divisors.filter fun d ↦ d ≤ Nat.sqrt n
  let large := n.divisors.filter fun d ↦ ¬d ≤ Nat.sqrt n
  have hsmall : small.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := by
    apply Finset.card_le_card
    intro d hd
    simp only [small, Finset.mem_filter] at hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd.1, hd.2⟩
  have hlarge : large.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := by
    refine Finset.card_le_card_of_injOn (fun d ↦ n / d) ?_ ?_
    · intro d hd
      simp only [large, Finset.mem_coe, Finset.mem_filter] at hd
      have hdDvd : d ∣ n := (Nat.mem_divisors.mp hd.1).1
      have hdPos : 0 < d := Nat.pos_of_mem_divisors hd.1
      have hquotPos : 0 < n / d :=
        Nat.div_pos (Nat.le_of_dvd hn hdDvd) hdPos
      have hfactor : n = d * (n / d) := (Nat.mul_div_cancel' hdDvd).symm
      exact Finset.mem_Icc.mpr
        ⟨hquotPos, (Nat.le_sqrt_of_eq_mul hfactor).resolve_left hd.2⟩
    · intro d₁ hd₁ d₂ hd₂ heq
      simp only [large, Finset.mem_coe, Finset.mem_filter] at hd₁ hd₂
      have hd₁Dvd : d₁ ∣ n := (Nat.mem_divisors.mp hd₁.1).1
      have hd₂Dvd : d₂ ∣ n := (Nat.mem_divisors.mp hd₂.1).1
      have hquotPos : 0 < n / d₁ :=
        Nat.div_pos (Nat.le_of_dvd hn hd₁Dvd)
          (Nat.pos_of_mem_divisors hd₁.1)
      change n / d₁ = n / d₂ at heq
      apply Nat.mul_right_cancel hquotPos
      calc
        d₁ * (n / d₁) = n := Nat.mul_div_cancel' hd₁Dvd
        _ = d₂ * (n / d₂) := (Nat.mul_div_cancel' hd₂Dvd).symm
        _ = d₂ * (n / d₁) := by rw [heq]
  have hsmall' : small.card ≤ Nat.sqrt n := by
    calc
      small.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := hsmall
      _ = Nat.sqrt n := by rw [Nat.card_Icc]; omega
  have hlarge' : large.card ≤ Nat.sqrt n := by
    calc
      large.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := hlarge
      _ = Nat.sqrt n := by rw [Nat.card_Icc]; omega
  have hpartition : small.card + large.card = n.divisors.card := by
    simpa [small, large] using
      (Finset.card_filter_add_card_filter_not (s := n.divisors)
        (fun d ↦ d ≤ Nat.sqrt n))
  omega

private theorem divisors_gcd_eq_filter
    {n r : ℕ} (hn : 0 < n) (hr : 0 < r) :
    (n.gcd r).divisors = r.divisors.filter (fun a ↦ a ∣ n) := by
  ext a
  have hgcd : 0 < n.gcd r := Nat.gcd_pos_of_pos_left r hn
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨ha, _⟩
    exact ⟨⟨ha.trans (Nat.gcd_dvd_right n r), hr.ne'⟩,
      ha.trans (Nat.gcd_dvd_left n r)⟩
  · rintro ⟨⟨har, _⟩, han⟩
    exact ⟨Nat.dvd_gcd han har, hgcd.ne'⟩

private theorem sum_moebius_divisors_eq_coprimeIndicator
    {n r : ℕ} (hn : 0 < n) (hr : 0 < r) :
    (∑ a ∈ r.divisors,
      if a ∣ n then
        ((ArithmeticFunction.moebius a : ℤ) : ℂ)
      else 0) =
      if n.Coprime r then 1 else 0 := by
  have hgcd : 0 < n.gcd r := Nat.gcd_pos_of_pos_left r hn
  calc
    (∑ a ∈ r.divisors,
        if a ∣ n then ((ArithmeticFunction.moebius a : ℤ) : ℂ) else 0) =
        ∑ a ∈ r.divisors.filter (fun a ↦ a ∣ n),
          ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
      rw [Finset.sum_filter]
    _ = ∑ a ∈ (n.gcd r).divisors,
          ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
      rw [divisors_gcd_eq_filter hn hr]
    _ = ∑ a ∈ (n.gcd r).divisors,
          (ArithmeticFunction.moebius : ArithmeticFunction ℂ) a := by
      simp
    _ = (((ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) (n.gcd r)) := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]
    _ = (1 : ArithmeticFunction ℂ) (n.gcd r) := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
    _ = if n.Coprime r then 1 else 0 := by
      by_cases hcop : n.Coprime r <;> simp [hcop]

private theorem character_eq_primitive_mul_coprimeIndicator
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (n : ℕ) :
    chi n = chi.primitiveCharacter n *
      (if n.Coprime (q / chi.conductor) then 1 else 0) := by
  have hdvd : chi.conductor ∣ q := chi.conductor_dvd_level
  have hfactor : chi.conductor * (q / chi.conductor) = q :=
    Nat.mul_div_cancel' hdvd
  by_cases hnr : n.Coprime (q / chi.conductor)
  · rw [if_pos hnr, mul_one]
    by_cases hnd : n.Coprime chi.conductor
    · have hnq : n.Coprime q := by
        rw [← hfactor, Nat.coprime_mul_iff_right]
        exact ⟨hnd, hnr⟩
      simpa only [Int.cast_natCast] using
        (chi.primitiveCharacter_apply_of_isCoprime
          (Nat.isCoprime_iff_coprime.mpr hnq)).symm
    · have hnq : ¬n.Coprime q := by
        rw [← hfactor, Nat.coprime_mul_iff_right]
        exact fun h ↦ hnd h.1
      have hchiZero : chi (n : ℤ) = 0 :=
        (DirichletCharacter.apply_eq_zero_iff chi (n : ℤ)).2
          (fun h ↦ hnq (Nat.isCoprime_iff_coprime.mp h))
      have hpsiZero : chi.primitiveCharacter (n : ℤ) = 0 :=
        (DirichletCharacter.apply_eq_zero_iff chi.primitiveCharacter (n : ℤ)).2
          (fun h ↦ hnd (Nat.isCoprime_iff_coprime.mp h))
      simpa only [Int.cast_natCast] using hchiZero.trans hpsiZero.symm
  · rw [if_neg hnr, mul_zero]
    have hnq : ¬n.Coprime q := by
      rw [← hfactor, Nat.coprime_mul_iff_right]
      exact fun h ↦ hnr h.2
    simpa only [Int.cast_natCast] using
      (DirichletCharacter.apply_eq_zero_iff chi (n : ℤ)).2
        (fun h ↦ hnq (Nat.isCoprime_iff_coprime.mp h))

private theorem sum_multiples_character
    {d a Y : ℕ} (ha : 0 < a) (psi : DirichletCharacter ℂ d) :
    (∑ n ∈ (Finset.Icc 1 Y).filter (fun n ↦ a ∣ n), psi n) =
      ∑ m ∈ Finset.Icc 1 (Y / a), psi (a * m) := by
  classical
  refine Finset.sum_bij'
    (fun n _ ↦ n / a) (fun m _ ↦ a * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    have hnPos : 0 < n := zero_lt_one.trans_le hn.1.1
    exact Finset.mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hnPos hn.2) ha,
        Nat.div_le_div_right hn.1.2⟩
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos ha hm.1,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha).mp hm.2⟩,
        Nat.dvd_mul_right a m⟩
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m hm
    exact Nat.mul_div_cancel_left m ha
  · intro n hn
    simp only [Finset.mem_filter] at hn
    congr 1
    simpa only [Nat.cast_mul] using
      congrArg (fun k : ℕ ↦ (k : ZMod d))
        (Nat.mul_div_cancel' hn.2).symm

private theorem imprimitivePrefix_eq_divisorSum
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (Y : ℕ) :
    dirichletCharacterIntervalSum 1 Y q chi =
      ∑ a ∈ (q / chi.conductor).divisors,
        (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            chi.primitiveCharacter a) *
          dirichletCharacterIntervalSum 1 (Y / a) chi.conductor
            chi.primitiveCharacter := by
  classical
  have hdPos : 0 < chi.conductor := Nat.pos_of_ne_zero chi.conductor_ne_zero
  have hrPos : 0 < q / chi.conductor :=
    Nat.div_pos
      (Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level) hdPos
  rw [dirichletCharacterIntervalSum]
  calc
    (∑ n ∈ Finset.Icc 1 Y, chi n) =
        ∑ n ∈ Finset.Icc 1 Y,
          chi.primitiveCharacter n *
            (if n.Coprime (q / chi.conductor) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact character_eq_primitive_mul_coprimeIndicator chi n
    _ = ∑ n ∈ Finset.Icc 1 Y,
          chi.primitiveCharacter n *
            (∑ a ∈ (q / chi.conductor).divisors,
              if a ∣ n then
                ((ArithmeticFunction.moebius a : ℤ) : ℂ)
              else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [sum_moebius_divisors_eq_coprimeIndicator
        (zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1) hrPos]
    _ = ∑ a ∈ (q / chi.conductor).divisors,
          ∑ n ∈ Finset.Icc 1 Y,
            chi.primitiveCharacter n *
              (if a ∣ n then
                ((ArithmeticFunction.moebius a : ℤ) : ℂ)
              else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ a ∈ (q / chi.conductor).divisors,
        (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            chi.primitiveCharacter a) *
          dirichletCharacterIntervalSum 1 (Y / a) chi.conductor
            chi.primitiveCharacter := by
      apply Finset.sum_congr rfl
      intro a ha
      have haPos : 0 < a := Nat.pos_of_mem_divisors ha
      calc
        (∑ n ∈ Finset.Icc 1 Y,
            chi.primitiveCharacter n *
              (if a ∣ n then
                ((ArithmeticFunction.moebius a : ℤ) : ℂ)
              else 0)) =
            ∑ n ∈ (Finset.Icc 1 Y).filter (fun n ↦ a ∣ n),
              chi.primitiveCharacter n *
                ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro n hn
          by_cases han : a ∣ n <;> simp [han]
        _ = ∑ m ∈ Finset.Icc 1 (Y / a),
              chi.primitiveCharacter (a * m) *
                ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
          rw [← Finset.sum_mul, sum_multiples_character haPos,
            Finset.sum_mul]
        _ = (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a) *
            (∑ m ∈ Finset.Icc 1 (Y / a),
              chi.primitiveCharacter m) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          rw [map_mul]
          ring
        _ = (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a) *
            dirichletCharacterIntervalSum 1 (Y / a) chi.conductor
              chi.primitiveCharacter := by
          rw [dirichletCharacterIntervalSum]

/-- The all-nonprincipal natural-prefix specialization of
Polya--Vinogradov. -/
theorem norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (Y : ℕ) :
    ‖dirichletCharacterIntervalSum 1 Y q chi‖ ≤
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  let d := chi.conductor
  let r := q / d
  have hdPos : 0 < d := Nat.pos_of_ne_zero chi.conductor_ne_zero
  have hdDvd : d ∣ q := chi.conductor_dvd_level
  have hfactor : d * r = q := Nat.mul_div_cancel' hdDvd
  have hrPos : 0 < r :=
    Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hdDvd) hdPos
  have hdNeOne : d ≠ 1 := by
    intro hd
    exact hchi (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hd)
  have hd : 1 < d := by omega
  have hdLeq : d ≤ q := Nat.le_of_dvd (NeZero.pos q) hdDvd
  letI : NeZero d := ⟨hdPos.ne'⟩
  have hscalePos :
      0 < Real.sqrt (d : ℝ) * Real.log (d : ℝ) :=
    mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hdPos))
      (Real.log_pos (by exact_mod_cast hd))
  have hcard : r.divisors.card ≤ 2 * Nat.sqrt r :=
    card_divisors_le_two_mul_sqrt hrPos
  have hcardReal :
      (r.divisors.card : ℝ) ≤ 2 * Real.sqrt (r : ℝ) := by
    calc
      (r.divisors.card : ℝ) ≤ ((2 * Nat.sqrt r : ℕ) : ℝ) := by
        exact_mod_cast hcard
      _ = 2 * (Nat.sqrt r : ℝ) := by norm_num
      _ ≤ 2 * Real.sqrt (r : ℝ) := by
        gcongr
        exact Real.nat_sqrt_le_real_sqrt
  have hsqrt :
      Real.sqrt (d : ℝ) * Real.sqrt (r : ℝ) = Real.sqrt (q : ℝ) := by
    calc
      Real.sqrt (d : ℝ) * Real.sqrt (r : ℝ) =
          Real.sqrt ((d : ℝ) * (r : ℝ)) :=
        (Real.sqrt_mul (by positivity) _).symm
      _ = Real.sqrt (q : ℝ) := by rw [← Nat.cast_mul, hfactor]
  have hlog : Real.log (d : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by exact_mod_cast hdPos) (by exact_mod_cast hdLeq)
  rw [imprimitivePrefix_eq_divisorSum chi Y]
  calc
    ‖∑ a ∈ r.divisors,
        (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            chi.primitiveCharacter a) *
          dirichletCharacterIntervalSum 1 (Y / a) d
            chi.primitiveCharacter‖ ≤
        ∑ a ∈ r.divisors,
          ‖(((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a) *
            dirichletCharacterIntervalSum 1 (Y / a) d
              chi.primitiveCharacter‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ r.divisors,
        Real.sqrt (d : ℝ) * Real.log (d : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      have hmu : ‖((ArithmeticFunction.moebius a : ℤ) : ℂ)‖ ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or a with hzero | hone | hneg
        · simp [hzero]
        · simp [hone]
        · simp [hneg]
      have hcoeff :
          ‖((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a‖ ≤ 1 := by
        rw [norm_mul]
        calc
          ‖((ArithmeticFunction.moebius a : ℤ) : ℂ)‖ *
              ‖chi.primitiveCharacter a‖ ≤ 1 * 1 :=
            mul_le_mul hmu (chi.primitiveCharacter.norm_le_one a)
              (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      rw [norm_mul]
      calc
        ‖((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a‖ *
            ‖dirichletCharacterIntervalSum 1 (Y / a) d
              chi.primitiveCharacter‖ ≤
            1 * ‖dirichletCharacterIntervalSum 1 (Y / a) d
              chi.primitiveCharacter‖ :=
          mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
        _ ≤ Real.sqrt (d : ℝ) * Real.log (d : ℝ) := by
          simpa using
            (norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
              hd chi.primitiveCharacter chi.primitiveCharacter_isPrimitive
              1 (Y / a)).le
    _ = (r.divisors.card : ℝ) *
        (Real.sqrt (d : ℝ) * Real.log (d : ℝ)) := by simp
    _ ≤ (2 * Real.sqrt (r : ℝ)) *
        (Real.sqrt (d : ℝ) * Real.log (d : ℝ)) :=
      mul_le_mul_of_nonneg_right hcardReal hscalePos.le
    _ = 2 * Real.sqrt (q : ℝ) * Real.log (d : ℝ) := by
      calc
        (2 * Real.sqrt (r : ℝ)) *
            (Real.sqrt (d : ℝ) * Real.log (d : ℝ)) =
            2 * (Real.sqrt (d : ℝ) * Real.sqrt (r : ℝ)) *
              Real.log (d : ℝ) := by ring
        _ = 2 * Real.sqrt (q : ℝ) * Real.log (d : ℝ) := by rw [hsqrt]
    _ ≤ 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      gcongr

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/CharacterPartialSummation.lean` -/

section

/-!
# Partial summation for nonprincipal character prefixes

This file derives the finite reciprocal Cauchy estimate and weighted-prefix
estimate used before the conditional `L(1, chi)` bridge on Koukoulopoulos,
printed p. 125. The finite statements and their endpoints are reviewed in
`SEM-543`.
-/

open MeasureTheory Set
open scoped BigOperators

namespace BoundedGaps.Maynard

private noncomputable def characterCumulative
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, chi (n : ZMod q)

private lemma characterCumulative_eq_interval
    {q : ℕ} (hq : 1 < q) (chi : DirichletCharacter ℂ q) (t : ℝ) :
    characterCumulative chi t =
      dirichletCharacterIntervalSum 1 ⌊t⌋₊ q chi := by
  rw [characterCumulative, dirichletCharacterIntervalSum,
    Finset.Icc_eq_cons_Ioc (Nat.zero_le ⌊t⌋₊), Finset.sum_cons]
  have hzero : chi ((0 : ℕ) : ZMod q) = 0 := by
    simpa only [Nat.cast_zero] using chi.map_zero' (Nat.ne_of_gt hq)
  rw [hzero, zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 ⌊t⌋₊]
  norm_num

private lemma norm_characterCumulative_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) :
    ‖characterCumulative chi t‖ ≤
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  rw [characterCumulative_eq_interval hq]
  exact norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
    hq chi hchi ⌊t⌋₊

private lemma characterScale_nonneg {q : ℕ} (hq : 1 < q) :
    0 ≤ 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  exact mul_nonneg
    (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
    (Real.log_pos (by exact_mod_cast hq)).le

private lemma hasDerivAt_complexOfReal_inv {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ ((u : ℂ)⁻¹))
      (-((t : ℂ) ^ 2)⁻¹) t := by
  have hcomplex : HasDerivAt (fun z : ℂ ↦ z⁻¹)
      (-((t : ℂ) ^ 2)⁻¹) (t : ℂ) :=
    hasDerivAt_inv (by exact_mod_cast ht)
  exact hcomplex.comp_ofReal

private lemma integrableOn_deriv_complexOfReal_inv
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹))) (Icc a b) := by
  let g : ℝ → ℂ := fun t ↦ -((t : ℂ) ^ 2)⁻¹
  have hgContinuous : ContinuousOn g (Icc a b) := by
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact Complex.continuous_ofReal.continuousOn.pow 2
    · intro t ht
      exact pow_ne_zero 2 (by exact_mod_cast (ha.trans_le ht.1).ne')
  apply hgContinuous.integrableOn_Icc.congr_fun _ measurableSet_Icc
  intro t ht
  exact (hasDerivAt_complexOfReal_inv (ha.trans_le ht.1).ne').deriv.symm

private lemma integral_Ioc_inv_sq
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t : ℝ in Ioc a b, (t ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hdiff : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ (fun u : ℝ ↦ u⁻¹) t := by
    intro t ht
    apply differentiableAt_inv
    have ht' : t ∈ Icc a b := by
      simpa [Set.uIcc_of_le hab] using ht
    exact (ha.trans_le ht'.1).ne'
  have hint : IntervalIntegrable
      (deriv (fun u : ℝ ↦ u⁻¹)) volume a b := by
    rw [show deriv (fun u : ℝ ↦ u⁻¹) = fun u ↦ -(u ^ 2)⁻¹ by
      funext u
      exact deriv_inv]
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact continuousOn_id.pow 2
    · intro t ht
      have ht' : t ∈ Icc a b := by
        simpa [Set.uIcc_of_le hab] using ht
      exact pow_ne_zero 2 (ha.trans_le ht'.1).ne'
  have hfund := intervalIntegral.integral_deriv_eq_sub hdiff hint
  rw [intervalIntegral.integral_of_le hab] at hfund
  rw [show deriv (fun u : ℝ ↦ u⁻¹) = fun u ↦ -(u ^ 2)⁻¹ by
    funext u
    exact deriv_inv] at hfund
  rw [integral_neg] at hfund
  linarith

private lemma integral_const_Ioc (C a b : ℝ) (hab : a ≤ b) :
    (∫ _t : ℝ in Ioc a b, C) = C * (b - a) := by
  rw [setIntegral_const, Measure.real_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  simp only [smul_eq_mul]
  ring

/-- A finite reciprocal Cauchy estimate obtained from the all-nonprincipal
Polya--Vinogradov prefix bound. This is not yet an identification of the
conditional infinite tail with `L(1, chi)`. -/
theorem norm_dirichletCharacterReciprocalIntervalSum_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (x y : ℕ) (hx : 0 < x) :
    ‖∑ n ∈ Finset.Ioc x y,
      chi (n : ZMod q) / (n : ℂ)‖ ≤
      4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / (x : ℝ) := by
  by_cases hxy : x ≤ y
  · have hxReal : 0 < (x : ℝ) := by exact_mod_cast hx
    have hxyReal : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
    have hyReal : 0 < (y : ℝ) := hxReal.trans_le hxyReal
    let C : ℝ := 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
    have hfDiff : ∀ t ∈ Icc (x : ℝ) y,
        DifferentiableAt ℝ (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t := by
      intro t ht
      exact (hasDerivAt_complexOfReal_inv
        (hxReal.trans_le ht.1).ne').differentiableAt
    have hfInt : IntegrableOn
        (deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹))) (Icc (x : ℝ) y) :=
      integrableOn_deriv_complexOfReal_inv hxReal
    have habel := sum_mul_eq_sub_sub_integral_mul'
      (f := fun t : ℝ ↦ ((t : ℂ)⁻¹))
      (c := fun n : ℕ ↦ chi (n : ZMod q)) hxy hfDiff hfInt
    have hrepresentation :
        (∑ n ∈ Finset.Ioc x y,
          chi (n : ZMod q) / (n : ℂ)) =
          ((y : ℂ)⁻¹ * characterCumulative chi (y : ℝ) -
            (x : ℂ)⁻¹ * characterCumulative chi (x : ℝ)) -
            ∫ t in Ioc (x : ℝ) y,
              deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
                characterCumulative chi t := by
      simpa [characterCumulative, div_eq_mul_inv, mul_comm] using habel
    have hActual : IntegrableOn
        (fun t : ℝ ↦ deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
          characterCumulative chi t) (Ioc (x : ℝ) y) := by
      apply (integrableOn_mul_sum_Icc
        (fun n : ℕ ↦ chi (n : ZMod q)) hxReal.le hfInt).mono_set
      exact Ioc_subset_Icc_self
    have hReciprocalContinuous : ContinuousOn
        (fun t : ℝ ↦ (t ^ 2)⁻¹) (Icc (x : ℝ) y) := by
      apply ContinuousOn.inv₀
      · exact continuousOn_id.pow 2
      · intro t ht
        exact pow_ne_zero 2 (hxReal.trans_le ht.1).ne'
    have hMajorant : IntegrableOn
        (fun t : ℝ ↦ C * (t ^ 2)⁻¹) (Ioc (x : ℝ) y) :=
      (continuousOn_const.mul hReciprocalContinuous).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    have hPoint : ∀ t ∈ Ioc (x : ℝ) y,
        ‖deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
            characterCumulative chi t‖ ≤ C * (t ^ 2)⁻¹ := by
      intro t ht
      have htPos : 0 < t := hxReal.trans ht.1
      rw [(hasDerivAt_complexOfReal_inv htPos.ne').deriv, norm_mul]
      have hderivNorm : ‖-((t : ℂ) ^ 2)⁻¹‖ = (t ^ 2)⁻¹ := by
        rw [norm_neg, norm_inv, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos htPos]
      rw [hderivNorm]
      calc
        (t ^ 2)⁻¹ * ‖characterCumulative chi t‖ =
            ‖characterCumulative chi t‖ * (t ^ 2)⁻¹ := mul_comm _ _
        _ ≤ C * (t ^ 2)⁻¹ := mul_le_mul_of_nonneg_right
          (by simpa [C] using
            norm_characterCumulative_le hq chi hchi t)
          (inv_nonneg.mpr (sq_nonneg t))
    have hIntegral :
        ‖∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
              characterCumulative chi t‖ ≤
          C * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) := by
      calc
        ‖∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
              characterCumulative chi t‖ ≤
            ∫ t in Ioc (x : ℝ) y,
              ‖deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
                characterCumulative chi t‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ t in Ioc (x : ℝ) y, C * (t ^ 2)⁻¹ := by
          apply setIntegral_mono_ae_restrict hActual.norm hMajorant
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact hPoint t ht
        _ = C * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) := by
          rw [integral_const_mul, integral_Ioc_inv_sq hxReal hxyReal]
    have hUpper :
        ‖(y : ℂ)⁻¹ * characterCumulative chi (y : ℝ)‖ ≤
          C * (y : ℝ)⁻¹ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      calc
        (y : ℝ)⁻¹ * ‖characterCumulative chi (y : ℝ)‖ ≤
            (y : ℝ)⁻¹ * C := mul_le_mul_of_nonneg_left
          (by simpa [C] using
            norm_characterCumulative_le hq chi hchi (y : ℝ))
          (inv_nonneg.mpr hyReal.le)
        _ = C * (y : ℝ)⁻¹ := mul_comm _ _
    have hLower :
        ‖(x : ℂ)⁻¹ * characterCumulative chi (x : ℝ)‖ ≤
          C * (x : ℝ)⁻¹ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      calc
        (x : ℝ)⁻¹ * ‖characterCumulative chi (x : ℝ)‖ ≤
            (x : ℝ)⁻¹ * C := mul_le_mul_of_nonneg_left
          (by simpa [C] using
            norm_characterCumulative_le hq chi hchi (x : ℝ))
          (inv_nonneg.mpr hxReal.le)
        _ = C * (x : ℝ)⁻¹ := mul_comm _ _
    rw [hrepresentation]
    calc
      ‖((y : ℂ)⁻¹ * characterCumulative chi (y : ℝ) -
          (x : ℂ)⁻¹ * characterCumulative chi (x : ℝ)) -
          ∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
              characterCumulative chi t‖ ≤
          (‖(y : ℂ)⁻¹ * characterCumulative chi (y : ℝ)‖ +
            ‖(x : ℂ)⁻¹ * characterCumulative chi (x : ℝ)‖) +
            ‖∫ t in Ioc (x : ℝ) y,
              deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
                characterCumulative chi t‖ := by
        exact (norm_sub_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (C * (y : ℝ)⁻¹ + C * (x : ℝ)⁻¹) +
          C * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) :=
        add_le_add (add_le_add hUpper hLower) hIntegral
      _ = 4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / (x : ℝ) := by
        dsimp [C]
        ring
  · have hyx : y ≤ x := Nat.le_of_not_ge hxy
    rw [Finset.Ioc_eq_empty_of_le hyx, Finset.sum_empty, norm_zero]
    have hNumerator :
        0 ≤ 4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      nlinarith [characterScale_nonneg hq]
    exact div_nonneg hNumerator (by positivity)

/-- A weighted-prefix estimate obtained from the all-nonprincipal
Polya--Vinogradov prefix bound. -/
theorem norm_dirichletCharacterWeightedPrefixSum_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (y : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 y,
      (n : ℂ) * chi (n : ZMod q)‖ ≤
      4 * (y : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  by_cases hy : y = 0
  · subst y
    simp
  · have hyPos : 0 < y := Nat.pos_of_ne_zero hy
    have hyOne : 1 ≤ y := hyPos
    have hyReal : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hyOne
    let C : ℝ := 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
    have hcastDeriv (t : ℝ) :
        HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 t := by
      simpa using (hasDerivAt_id (𝕜 := ℂ) (x := (t : ℂ))).comp_ofReal
    have hfDiff : ∀ t ∈ Icc (1 : ℝ) y,
        DifferentiableAt ℝ (fun u : ℝ ↦ (u : ℂ)) t := by
      intro t _
      exact (hcastDeriv t).differentiableAt
    have hfInt : IntegrableOn
        (deriv (fun u : ℝ ↦ (u : ℂ))) (Icc (1 : ℝ) y) := by
      apply (continuousOn_const : ContinuousOn
        (fun _t : ℝ ↦ (1 : ℂ)) (Icc (1 : ℝ) y)).integrableOn_Icc.congr_fun
        _ measurableSet_Icc
      intro t _
      exact (hcastDeriv t).deriv.symm
    have habel := sum_mul_eq_sub_integral_mul₀'
      (f := fun t : ℝ ↦ (t : ℂ))
      (c := fun n : ℕ ↦ chi (n : ZMod q))
      (by simpa only [Nat.cast_zero] using
        chi.map_zero' (Nat.ne_of_gt hq)) y hfDiff hfInt
    have hleft :
        (∑ n ∈ Finset.Icc 0 y,
          (n : ℂ) * chi (n : ZMod q)) =
          ∑ n ∈ Finset.Icc 1 y,
            (n : ℂ) * chi (n : ZMod q) := by
      rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le y), Finset.sum_cons]
      simp only [Nat.cast_zero, zero_mul, zero_add]
      rw [← Finset.Icc_add_one_left_eq_Ioc 0 y]
      norm_num
    have hrepresentation :
        (∑ n ∈ Finset.Icc 1 y,
          (n : ℂ) * chi (n : ZMod q)) =
          (y : ℂ) * characterCumulative chi (y : ℝ) -
            ∫ t in Ioc (1 : ℝ) y,
              deriv (fun u : ℝ ↦ (u : ℂ)) t *
                characterCumulative chi t := by
      rw [← hleft]
      simpa [characterCumulative] using habel
    have hActual : IntegrableOn
        (fun t : ℝ ↦ deriv (fun u : ℝ ↦ (u : ℂ)) t *
          characterCumulative chi t) (Ioc (1 : ℝ) y) := by
      apply (integrableOn_mul_sum_Icc
        (fun n : ℕ ↦ chi (n : ZMod q)) zero_le_one hfInt).mono_set
      exact Ioc_subset_Icc_self
    have hMajorant : IntegrableOn
        (fun _t : ℝ ↦ C) (Ioc (1 : ℝ) y) :=
      integrableOn_const measure_Ioc_lt_top.ne
    have hPoint : ∀ t ∈ Ioc (1 : ℝ) y,
        ‖deriv (fun u : ℝ ↦ (u : ℂ)) t *
            characterCumulative chi t‖ ≤ C := by
      intro t _
      rw [(hcastDeriv t).deriv, one_mul]
      simpa [C] using norm_characterCumulative_le hq chi hchi t
    have hIntegral :
        ‖∫ t in Ioc (1 : ℝ) y,
            deriv (fun u : ℝ ↦ (u : ℂ)) t *
              characterCumulative chi t‖ ≤
          C * ((y : ℝ) - 1) := by
      calc
        ‖∫ t in Ioc (1 : ℝ) y,
            deriv (fun u : ℝ ↦ (u : ℂ)) t *
              characterCumulative chi t‖ ≤
            ∫ t in Ioc (1 : ℝ) y,
              ‖deriv (fun u : ℝ ↦ (u : ℂ)) t *
                characterCumulative chi t‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ _t in Ioc (1 : ℝ) y, C := by
          apply setIntegral_mono_ae_restrict hActual.norm hMajorant
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact hPoint t ht
        _ = C * ((y : ℝ) - 1) := integral_const_Ioc C 1 y hyReal
    have hEndpoint :
        ‖(y : ℂ) * characterCumulative chi (y : ℝ)‖ ≤
          (y : ℝ) * C := by
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left
        (by simpa [C] using
          norm_characterCumulative_le hq chi hchi (y : ℝ))
        (by positivity)
    rw [hrepresentation]
    calc
      ‖(y : ℂ) * characterCumulative chi (y : ℝ) -
          ∫ t in Ioc (1 : ℝ) y,
            deriv (fun u : ℝ ↦ (u : ℂ)) t *
              characterCumulative chi t‖ ≤
          ‖(y : ℂ) * characterCumulative chi (y : ℝ)‖ +
            ‖∫ t in Ioc (1 : ℝ) y,
              deriv (fun u : ℝ ↦ (u : ℂ)) t *
                characterCumulative chi t‖ := norm_sub_le _ _
      _ ≤ (y : ℝ) * C + C * ((y : ℝ) - 1) :=
        add_le_add hEndpoint hIntegral
      _ ≤ 4 * (y : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
        dsimp [C]
        have hscale := characterScale_nonneg hq
        nlinarith

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/NonprincipalLFunctionAbel.lean` -/

section

/-!
# Abel continuation and the ordered value at one

This file specializes the bounded-prefix Abel continuation to every
nonprincipal character and identifies the natural reciprocal prefixes with
the analytic value `L(1, chi)`. The series is conditionally convergent, so the
statement deliberately uses finite prefixes and `Tendsto`, not an
unconditional infinite-sum interface. Semantic review: `SEM-544`.
-/

open Asymptotics Complex Filter MeasureTheory Set
open scoped BigOperators Real Topology

namespace BoundedGaps.Maynard

/-- The Abel integral for every nonprincipal character on the positive
half-plane, using the all-nonprincipal Polya--Vinogradov prefix bound. -/
theorem LFunction_eq_abelIntegral_of_ne_one
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) (hs : 0 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * ∫ y in Set.Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1)) := by
  simpa [dirichletCharacterIntervalSum] using
    LFunction_eq_abelIntegral_of_prefixBound chi hchi
      (2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ))
      (fun n ↦ by
        simpa [dirichletCharacterIntervalSum] using
          norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
            hq chi hchi n)
      s hs

private theorem tendsto_reciprocalPrefix_of_abelIntegral
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖dirichletCharacterIntervalSum 1 n q chi‖ ≤ C)
    (habel : DirichletCharacter.LFunction chi (1 : ℂ) =
      (1 : ℂ) * ∫ y in Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-((1 : ℂ) + 1))) :
    Tendsto (fun x : ℕ ↦ ∑ n ∈ Finset.Icc 1 x,
      chi (n : ZMod q) / (n : ℂ)) atTop
      (𝓝 (DirichletCharacter.LFunction chi (1 : ℂ))) := by
  let c : ℕ → ℂ := fun n ↦ chi (n : ZMod q)
  let f : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-(1 : ℂ))
  have hc0 : c 0 = 0 := by
    simpa [c] using chi.map_zero' (Nat.ne_of_gt hq)
  have hCumulative (n : ℕ) :
      ∑ k ∈ Finset.Icc 0 n, c k =
        dirichletCharacterIntervalSum 1 n q chi := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hc0,
      zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 n]
    norm_num [c, dirichletCharacterIntervalSum]
  have hfDiff : ∀ t ∈ Ici (1 : ℝ), DifferentiableAt ℝ f t := by
    intro t ht
    exact differentiableAt_id.ofReal_cpow_const
      (zero_lt_one.trans_le ht).ne' (by norm_num)
  have hfInt : LocallyIntegrableOn (deriv f) (Ici (1 : ℝ)) := by
    exact (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one
        (by norm_num))).locallyIntegrableOn
  have hEndpoint : Tendsto
      (fun n : ℕ ↦ f n * ∑ k ∈ Finset.Icc 0 n, c k) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun n : ℕ ↦ C / (n : ℝ))
    · exact Eventually.of_forall fun n ↦ norm_nonneg _
    · filter_upwards [eventually_gt_atTop 0] with n hn
      rw [hCumulative, norm_mul]
      have hfn : ‖f n‖ = (n : ℝ)⁻¹ := by
        change ‖(n : ℂ) ^ (-(1 : ℂ))‖ = (n : ℝ)⁻¹
        rw [Complex.cpow_neg_one, norm_inv, Complex.norm_natCast]
      rw [hfn]
      calc
        (n : ℝ)⁻¹ *
            ‖dirichletCharacterIntervalSum 1 n q chi‖ ≤
            (n : ℝ)⁻¹ * C :=
          mul_le_mul_of_nonneg_left (hprefix n)
            (inv_nonneg.mpr (by positivity))
        _ = C / (n : ℝ) := by ring
    · simpa [div_eq_mul_inv] using
        ((tendsto_const_nhds (x := C)).mul
          (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hDom :
      (fun t ↦ deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =O[atTop]
        (fun t : ℝ ↦ t ^ (-2 : ℝ)) := by
    refine isBigO_iff.mpr ⟨C, ?_⟩
    filter_upwards [eventually_gt_atTop 1] with t ht
    rw [norm_mul, hCumulative]
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hderiv : ‖deriv f t‖ = t ^ (-2 : ℝ) := by
      rw [show deriv f t =
          deriv (fun u : ℝ ↦ (u : ℂ) ^ (-(1 : ℂ))) t by rfl,
        deriv_ofReal_cpow_const ht0.ne' (by norm_num), norm_mul,
        norm_neg, norm_one, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      norm_num
    rw [hderiv]
    have hgNonneg : 0 ≤ t ^ (-2 : ℝ) := Real.rpow_nonneg ht0.le _
    calc
      t ^ (-2 : ℝ) *
          ‖dirichletCharacterIntervalSum 1 ⌊t⌋₊ q chi‖ ≤
          t ^ (-2 : ℝ) * C :=
        mul_le_mul_of_nonneg_left (hprefix _) hgNonneg
      _ = C * ‖t ^ (-2 : ℝ)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hgNonneg]
        ring
  have hconv := tendsto_sum_mul_atTop_nhds_one_sub_integral₀
    (f := f) (l := 0) c hc0 hfDiff hfInt hEndpoint hDom
      (integrableAtFilter_rpow_atTop_iff.mpr (by norm_num))
  have hleft (n : ℕ) :
      (∑ k ∈ Finset.Icc 0 n, f k * c k) =
        ∑ k ∈ Finset.Icc 1 n,
          chi (k : ZMod q) / (k : ℂ) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hc0,
      mul_zero, zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 n]
    norm_num [f, c, Complex.cpow_neg_one, div_eq_mul_inv, mul_comm]
  have hright :
      0 - ∫ t in Ioi (1 : ℝ),
          deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k =
        DirichletCharacter.LFunction chi (1 : ℂ) := by
    rw [habel, one_mul, zero_sub, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change -(deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) = _
    rw [show deriv f t =
        deriv (fun u : ℝ ↦ (u : ℂ) ^ (-(1 : ℂ))) t by rfl,
      deriv_ofReal_cpow_const (zero_lt_one.trans ht).ne' (by norm_num),
      hCumulative]
    ring_nf
  rw [← hright]
  exact hconv.congr' (Eventually.of_forall hleft)

/-- The natural reciprocal prefixes of a nonprincipal character converge to
the analytic value `L(1, chi)`. This is conditional, ordered convergence. -/
theorem tendsto_dirichletCharacterReciprocalPrefix_atTop
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    Tendsto
      (fun x : ℕ ↦ ∑ n ∈ Finset.Icc 1 x,
        chi (n : ZMod q) / (n : ℂ))
      atTop (𝓝 (DirichletCharacter.LFunction chi (1 : ℂ))) := by
  let C : ℝ := 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
  apply tendsto_reciprocalPrefix_of_abelIntegral hq chi C
  · intro n
    simpa [C] using
      norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
        hq chi hchi n
  · exact LFunction_eq_abelIntegral_of_ne_one
      hq chi hchi (1 : ℂ) (by norm_num)

/-- The factor-four quantitative remainder for the naturally ordered value
`L(1, chi)`. -/
theorem norm_LFunction_one_sub_dirichletCharacterReciprocalPrefix_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (x : ℕ) (hx : 0 < x) :
    ‖DirichletCharacter.LFunction chi (1 : ℂ) -
        ∑ n ∈ Finset.Icc 1 x,
          chi (n : ZMod q) / (n : ℂ)‖ ≤
      4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / (x : ℝ) := by
  let P : ℕ → ℂ := fun y ↦ ∑ n ∈ Finset.Icc 1 y,
    chi (n : ZMod q) / (n : ℂ)
  have htail {y : ℕ} (hxy : x ≤ y) :
      P y - P x = ∑ n ∈ Finset.Ioc x y,
        chi (n : ZMod q) / (n : ℂ) := by
    have hunion : Finset.Icc 1 x ∪ Finset.Ioc x y =
        Finset.Icc 1 y := by
      ext n
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      constructor
      · rintro (hn | hn) <;> omega
      · intro hn
        by_cases hnx : n ≤ x
        · exact Or.inl ⟨hn.1, hnx⟩
        · exact Or.inr ⟨lt_of_not_ge hnx, hn.2⟩
    have hdis : Disjoint (Finset.Icc 1 x) (Finset.Ioc x y) := by
      rw [Finset.disjoint_left]
      intro n hncc hnoc
      simp only [Finset.mem_Icc] at hncc
      simp only [Finset.mem_Ioc] at hnoc
      omega
    change (∑ n ∈ Finset.Icc 1 y,
        chi (n : ZMod q) / (n : ℂ)) -
      (∑ n ∈ Finset.Icc 1 x,
        chi (n : ZMod q) / (n : ℂ)) = _
    rw [← hunion, Finset.sum_union hdis]
    ring
  have hconv :=
    tendsto_dirichletCharacterReciprocalPrefix_atTop hq chi hchi
  have hlim : Tendsto (fun y ↦ ‖P y - P x‖) atTop
      (𝓝 ‖DirichletCharacter.LFunction chi (1 : ℂ) - P x‖) := by
    exact (hconv.sub_const (P x)).norm
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop x] with y hxy
  rw [htail hxy]
  exact norm_dirichletCharacterReciprocalIntervalSum_le
    hq chi hchi x y hx

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/NearOneLFunction.lean` -/

section

/-!
# Nonprincipal Dirichlet L-functions near one

The all-character Polya--Vinogradov prefix bound controls the Abel integral
after splitting it at the modulus.  A Cauchy circle then gives the explicit
real-axis derivative estimate needed for the weak real-zero gap.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 113,
Lemma 11.2, and printed p. 124, equation (12.11).  Semantic review:
`SEM-548`.
-/

noncomputable section

open Complex MeasureTheory Metric Set
open scoped BigOperators Real Topology

namespace BoundedGaps.Maynard

private lemma three_le_modulus_of_character_ne_one
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    3 ≤ q := by
  by_contra hq
  have hqPos : 0 < q := NeZero.pos q
  have hqNeOne : q ≠ 1 := fun h ↦ hchi (chi.level_one' h)
  have hqTwo : q = 2 := by omega
  subst q
  have hcard : Nat.card (DirichletCharacter ℂ 2) = 1 := by
    rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    norm_num
  exact hchi ((Nat.card_eq_one_iff_unique.mp hcard).1.elim chi 1)

private lemma one_lt_log_modulus
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    1 < Real.log (q : ℝ) := by
  have hqThree : (3 : ℝ) ≤ q := by
    exact_mod_cast three_le_modulus_of_character_ne_one chi hchi
  exact (by norm_num : (1 : ℝ) < 1.0986122885).trans
    (Real.log_three_gt_d9.trans_le
      (Real.log_le_log (by norm_num) hqThree))

private lemma norm_characterIntervalSum_floor_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {y : ℝ} (hy : 1 < y) :
    ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi‖ ≤ y := by
  have hfloorPos : 0 < ⌊y⌋₊ := Nat.floor_pos.mpr hy.le
  calc
    ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi‖ ≤
        ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ‖chi (n : ZMod q)‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊y⌋₊, (1 : ℝ) := by
      exact Finset.sum_le_sum fun n _ ↦ chi.norm_le_one (n : ZMod q)
    _ = (⌊y⌋₊ : ℝ) := by
      simp [Nat.card_Icc]
    _ ≤ y := Nat.floor_le (zero_lt_one.trans hy).le

private lemma measurable_characterAbelIntegrand
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ) :
    AEStronglyMeasurable
      (fun y : ℝ ↦
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1)))
      (volume.restrict (Ioi 1)) := by
  have hPrefix : Measurable
      (fun y : ℝ ↦ dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi) :=
    (measurable_of_countable
      (fun n : ℕ ↦ dirichletCharacterIntervalSum 1 n q chi)).comp
      Nat.measurable_floor
  have hCpow : ContinuousOn
      (fun y : ℝ ↦ (y : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    continuousOn_of_forall_continuousAt fun y hy ↦
      continuousAt_ofReal_cpow_const y (-(s + 1))
        (Or.inr (zero_lt_one.trans hy).ne')
  exact hPrefix.aestronglyMeasurable.mul
    (hCpow.aestronglyMeasurable measurableSet_Ioi)

private lemma integrableOn_characterAbelIntegrand
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun y : ℝ ↦
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1)))
      (Ioi 1) := by
  let C := 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
  have hPower : IntegrableOn
      (fun y : ℝ ↦ y ^ (-(s.re + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hMajorant : IntegrableOn
      (fun y : ℝ ↦ C * y ^ (-(s.re + 1))) (Ioi 1) :=
    hPower.const_mul C
  have hBound : ∀ᵐ (y : ℝ) ∂volume.restrict (Ioi 1),
      ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
        C * y ^ (-(s.re + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hyPos : 0 < y := zero_lt_one.trans hy
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hyPos]
    simp only [neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_right
      (by
        simpa [C] using
          norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
            hq chi hchi ⌊y⌋₊)
      (Real.rpow_nonneg hyPos.le _)
  exact hMajorant.mono' (measurable_characterAbelIntegrand chi s) hBound

private lemma initial_characterAbelIntegral_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {s : ℂ}
    (hsRe : 1 - 5 / (16 * Real.log (q : ℝ)) ≤ s.re) :
    ‖∫ y in Ioc (1 : ℝ) q,
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
      3 * Real.log (q : ℝ) := by
  let L := Real.log (q : ℝ)
  let f : ℝ → ℂ := fun y ↦
    dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
      (y : ℂ) ^ (-(s + 1))
  let g : ℝ → ℝ := fun y ↦ 3 * y ^ (-1 : ℝ)
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hqPos : (0 : ℝ) < q := zero_lt_one.trans_le hqOne
  have hLpos : 0 < L := by
    exact Real.log_pos (by exact_mod_cast hq)
  have hLone : 1 < L := one_lt_log_modulus chi hchi
  have hMajorant : IntegrableOn g (Ioc (1 : ℝ) q) := by
    apply (continuousOn_const.mul ?_).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    exact continuousOn_of_forall_continuousAt fun y hy ↦
      Real.continuousAt_rpow_const _ _
        (Or.inl (zero_lt_one.trans_le hy.1).ne')
  have hPoint : ∀ y ∈ Ioc (1 : ℝ) q, ‖f y‖ ≤ g y := by
    intro y hy
    have hyPos : 0 < y := zero_lt_one.trans hy.1
    have hyOne : 1 ≤ y := hy.1.le
    have hdelta : 1 - s.re ≤ 5 / (16 * L) := by
      dsimp [L]
      linarith
    have hpow : y ^ (1 - s.re) ≤ 3 := by
      by_cases hdeltaNonpos : 1 - s.re ≤ 0
      · exact (Real.rpow_le_one_of_one_le_of_nonpos hyOne hdeltaNonpos).trans
          (by norm_num)
      · have hdeltaNonneg : 0 ≤ 1 - s.re := le_of_not_ge hdeltaNonpos
        have hbase : y ^ (1 - s.re) ≤ (q : ℝ) ^ (1 - s.re) :=
          Real.rpow_le_rpow hyPos.le hy.2 hdeltaNonneg
        have hexponent :
            (q : ℝ) ^ (1 - s.re) ≤ (q : ℝ) ^ (5 / (16 * L)) :=
          Real.rpow_le_rpow_of_exponent_le hqOne hdelta
        have heval : (q : ℝ) ^ (5 / (16 * L)) = Real.exp (5 / 16) := by
          rw [Real.rpow_def_of_pos hqPos]
          congr 1
          dsimp [L]
          have hlogNe : Real.log (q : ℝ) ≠ 0 :=
            (Real.log_pos (by exact_mod_cast hq)).ne'
          field_simp [hlogNe]
        calc
          y ^ (1 - s.re) ≤ (q : ℝ) ^ (1 - s.re) := hbase
          _ ≤ (q : ℝ) ^ (5 / (16 * L)) := hexponent
          _ = Real.exp (5 / 16) := heval
          _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
          _ ≤ 3 := Real.exp_one_lt_three.le
    dsimp [f, g]
    rw [norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hyPos]
    simp only [neg_re, add_re, one_re]
    calc
      ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi‖ *
          y ^ (-(s.re + 1)) ≤
          y * y ^ (-(s.re + 1)) :=
        mul_le_mul_of_nonneg_right
          (norm_characterIntervalSum_floor_le chi hy.1)
          (Real.rpow_nonneg hyPos.le _)
      _ = y ^ (-s.re) := by
        rw [mul_comm, ← Real.rpow_add_one hyPos.ne']
        congr 1
        ring
      _ = y ^ (-1 : ℝ) * y ^ (1 - s.re) := by
        rw [← Real.rpow_add hyPos]
        congr 1
        ring
      _ ≤ y ^ (-1 : ℝ) * 3 :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hyPos.le _)
      _ = 3 * y ^ (-1 : ℝ) := by ring
  have hsPos : 0 < s.re := by
    have hfrac : 5 / (16 * L) ≤ 5 / 16 := by
      rw [div_le_iff₀ (by positivity : 0 < 16 * L)]
      nlinarith
    linarith
  have hActual : IntegrableOn f (Ioc (1 : ℝ) q) :=
    (integrableOn_characterAbelIntegrand hq chi hchi hsPos).mono_set
      Ioc_subset_Ioi_self
  calc
    ‖∫ y in Ioc (1 : ℝ) q, f y‖ ≤
        ∫ y in Ioc (1 : ℝ) q, ‖f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioc (1 : ℝ) q, g y :=
      setIntegral_mono_on hActual.norm hMajorant measurableSet_Ioc hPoint
    _ = 3 * Real.log (q : ℝ) := by
      rw [integral_const_mul]
      rw [← intervalIntegral.integral_of_le hqOne]
      simp_rw [Real.rpow_neg_one]
      rw [integral_inv_of_pos zero_lt_one hqPos]
      simp

private lemma tail_characterAbelIntegral_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {s : ℂ} (hsRe : 1 - 5 / (16 * Real.log (q : ℝ)) ≤ s.re) :
    ‖∫ y in Ioi (q : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
      4 * Real.log (q : ℝ) := by
  let L := Real.log (q : ℝ)
  let C := 2 * Real.sqrt (q : ℝ) * L
  let f : ℝ → ℂ := fun y ↦
    dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
      (y : ℂ) ^ (-(s + 1))
  let g : ℝ → ℝ := fun y ↦ C * y ^ (-(s.re + 1))
  have hqThree := three_le_modulus_of_character_ne_one chi hchi
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hqThree.trans' (by norm_num)
  have hqPos : (0 : ℝ) < q := zero_lt_one.trans_le hqOne
  have hLone : 1 < L := one_lt_log_modulus chi hchi
  have hLpos : 0 < L := zero_lt_one.trans hLone
  have hfrac : 5 / (16 * L) ≤ 5 / 16 := by
    rw [div_le_iff₀ (by positivity : 0 < 16 * L)]
    nlinarith
  have hsLower : (11 / 16 : ℝ) ≤ s.re := by
    dsimp [L] at hfrac
    linarith
  have hsPos : 0 < s.re := by linarith
  have hCnonneg : 0 ≤ C := by positivity
  have hPower : IntegrableOn (fun y : ℝ ↦ y ^ (-(s.re + 1))) (Ioi q) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hqPos
  have hMajorant : IntegrableOn g (Ioi (q : ℝ)) := hPower.const_mul C
  have hPoint : ∀ y ∈ Ioi (q : ℝ), ‖f y‖ ≤ g y := by
    intro y hy
    have hyPos : 0 < y := hqPos.trans hy
    dsimp [f, g, C]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hyPos]
    simp only [neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_right
      (norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
        hq chi hchi ⌊y⌋₊)
      (Real.rpow_nonneg hyPos.le _)
  have hActual : IntegrableOn f (Ioi (q : ℝ)) :=
    (integrableOn_characterAbelIntegrand hq chi hchi hsPos).mono_set
      (Ioi_subset_Ioi hqOne)
  have hnormIntegral :
      ‖∫ y in Ioi (q : ℝ), f y‖ ≤
        C * ((q : ℝ) ^ (-s.re) / s.re) := by
    calc
      ‖∫ y in Ioi (q : ℝ), f y‖ ≤
          ∫ y in Ioi (q : ℝ), ‖f y‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ y in Ioi (q : ℝ), g y :=
        setIntegral_mono_on hActual.norm hMajorant measurableSet_Ioi hPoint
      _ = C * ∫ y in Ioi (q : ℝ), y ^ (-(s.re + 1)) := by
        rw [integral_const_mul]
      _ = C * ((q : ℝ) ^ (-s.re) / s.re) := by
        rw [integral_Ioi_rpow_of_lt (by linarith) hqPos]
        congr 1
        field_simp [hsPos.ne']
        ring_nf
  have hsHalf : (1 / 2 : ℝ) ≤ s.re := by linarith
  have hpowProduct :
      Real.sqrt (q : ℝ) * (q : ℝ) ^ (-s.re) ≤ 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hqPos]
    exact Real.rpow_le_one_of_one_le_of_nonpos hqOne (by linarith)
  have hinv : 1 / s.re ≤ 2 := by
    exact (div_le_iff₀ hsPos).2 (by linarith)
  calc
    ‖∫ y in Ioi (q : ℝ), f y‖ ≤
        C * ((q : ℝ) ^ (-s.re) / s.re) := hnormIntegral
    _ = 2 * L *
        (Real.sqrt (q : ℝ) * (q : ℝ) ^ (-s.re)) * (1 / s.re) := by
      dsimp [C]
      ring
    _ ≤ 2 * L * 1 * 2 := by
      gcongr
    _ = 4 * Real.log (q : ℝ) := by
      dsimp [L]
      ring

/-- Explicit all-nonprincipal `j = 0` bound in the narrow complex region
used by the Cauchy circle. -/
theorem norm_LFunction_near_one_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {s : ℂ}
    (hsRe : 1 - 5 / (16 * Real.log (q : ℝ)) ≤ s.re)
    (hsNorm : ‖s‖ ≤ 2) :
    ‖DirichletCharacter.LFunction chi s‖ ≤
      32 * Real.log (q : ℝ) := by
  let f : ℝ → ℂ := fun y ↦
    dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
      (y : ℂ) ^ (-(s + 1))
  have hLone := one_lt_log_modulus chi hchi
  have hLpos : 0 < Real.log (q : ℝ) := zero_lt_one.trans hLone
  have hRePos : 0 < s.re := by
    have hfrac : 5 / (16 * Real.log (q : ℝ)) ≤ 5 / 16 := by
      rw [div_le_iff₀ (by positivity : 0 < 16 * Real.log (q : ℝ))]
      nlinarith
    linarith
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hInitial := initial_characterAbelIntegral_le hq chi hchi hsRe
  have hTail := tail_characterAbelIntegral_le hq chi hchi hsRe
  have hIntegrable := integrableOn_characterAbelIntegrand hq chi hchi hRePos
  have hSplit :
      (∫ y in Ioi (1 : ℝ), f y) =
        (∫ y in Ioc (1 : ℝ) q, f y) +
          (∫ y in Ioi (q : ℝ), f y) := by
    rw [← Ioc_union_Ioi_eq_Ioi hqOne,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hIntegrable.mono_set Ioc_subset_Ioi_self)
        (hIntegrable.mono_set (Ioi_subset_Ioi hqOne))]
  rw [LFunction_eq_abelIntegral_of_ne_one hq chi hchi s hRePos, norm_mul]
  change ‖s‖ * ‖∫ y in Ioi (1 : ℝ), f y‖ ≤ _
  rw [hSplit]
  calc
    ‖s‖ * ‖(∫ y in Ioc (1 : ℝ) q, f y) +
        (∫ y in Ioi (q : ℝ), f y)‖ ≤
      ‖s‖ * (‖∫ y in Ioc (1 : ℝ) q, f y‖ +
        ‖∫ y in Ioi (q : ℝ), f y‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg s)
    _ ≤ 2 * (3 * Real.log (q : ℝ) + 4 * Real.log (q : ℝ)) := by
      gcongr
    _ ≤ 32 * Real.log (q : ℝ) := by nlinarith

/-- Explicit `j = 1` real-axis consequence of Lemma 11.2 in the range
needed for the weak real-zero gap. -/
theorem norm_deriv_LFunction_ofReal_near_one_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {sigma : ℝ}
    (hsigmaNear :
      1 - 1 / (4 * Real.log (q : ℝ)) ≤ sigma)
    (hsigmaOne : sigma ≤ 1) :
    ‖deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
      512 * (Real.log (q : ℝ)) ^ 2 := by
  let L := Real.log (q : ℝ)
  let r := 1 / (16 * L)
  have hLone : 1 < L := one_lt_log_modulus chi hchi
  have hLpos : 0 < L := zero_lt_one.trans hLone
  have hrPos : 0 < r := by positivity
  have hrLe : r ≤ 1 / 16 := by
    dsimp [r]
    rw [div_le_iff₀ (by positivity : 0 < 16 * L)]
    nlinarith
  have hsigmaPos : 0 < sigma := by
    have hquarter : 1 / (4 * L) < 1 := by
      rw [div_lt_one (by positivity : 0 < 4 * L)]
      nlinarith
    change 1 - 1 / (4 * L) ≤ sigma at hsigmaNear
    linarith
  have hsphere : ∀ z ∈ sphere (sigma : ℂ) r,
      ‖DirichletCharacter.LFunction chi z‖ ≤ 32 * L := by
    intro z hz
    have hdist : ‖z - (sigma : ℂ)‖ = r := by
      simpa [dist_eq_norm] using mem_sphere.mp hz
    have hreDiff : |z.re - sigma| ≤ r := by
      calc
        |z.re - sigma| = |(z - (sigma : ℂ)).re| := by simp
        _ ≤ ‖z - (sigma : ℂ)‖ := Complex.abs_re_le_norm _
        _ = r := hdist
    have hzRe : 1 - 5 / (16 * L) ≤ z.re := by
      have hrad : r = 1 / (16 * L) := rfl
      rw [hrad] at hreDiff
      have hlower := (abs_le.mp hreDiff).1
      change 1 - 1 / (4 * L) ≤ sigma at hsigmaNear
      have hratio : 1 / (4 * L) = 4 * (1 / (16 * L)) := by
        field_simp [hLpos.ne']
        ring
      rw [hratio] at hsigmaNear
      have hfive : 5 / (16 * L) = 5 * (1 / (16 * L)) := by ring
      rw [hfive]
      linarith
    have hzNorm : ‖z‖ ≤ 2 := by
      calc
        ‖z‖ ≤ ‖(sigma : ℂ)‖ + ‖z - (sigma : ℂ)‖ := by
          simpa [add_comm] using norm_add_le (z - (sigma : ℂ)) (sigma : ℂ)
        _ = sigma + r := by simp [abs_of_pos hsigmaPos, hdist]
        _ ≤ 2 := by linarith
    simpa [L] using norm_LFunction_near_one_le hq chi hchi hzRe hzNorm
  have hCauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hrPos (DirichletCharacter.differentiable_LFunction hchi).diffContOnCl hsphere
  calc
    ‖deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
        (32 * L) / r := hCauchy
    _ = 512 * (Real.log (q : ℝ)) ^ 2 := by
      change (32 * L) / (1 / (16 * L)) = 512 * L ^ 2
      field_simp [hLpos.ne']
      ring

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/DirichletLZeroDivisor.lean` -/

section

/-!
# The zero divisor of a nontrivial Dirichlet L-function

For a nontrivial Dirichlet character, Mathlib's continued `LFunction` is
entire and is nonzero at `s = 2`. Its divisor therefore records every ordinary
zero with its exact finite analytic multiplicity, and has finite support on a
closed disk.

This is intentionally the divisor of the ordinary L-function: it includes
trivial zeros and zeros introduced by imprimitive Euler factors. Identifying a
filtered part of it with completed primitive nontrivial zeros is a later
bridge.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 112--114,
zero conventions and Lemma 11.4(a)--(b). Convention checks:
`ElkiesM229PNTAP2018`, p. 1, and `ElkiesM229NearlyZeroFree2018`, pp. 2--3.
Semantic review: `SEM-470`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex

private theorem analyticOnNhd_LFunction_of_nontrivial
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
  fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z

private theorem LFunction_ne_zero_function_of_nontrivial
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ ≠ 0 := by
  intro hzero
  have hz : DirichletCharacter.LFunction χ (2 : ℂ) = 0 := by
    rw [hzero]
    rfl
  exact (χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (by norm_num)) hz

private theorem analyticOrderAt_LFunction_ne_top
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (s : ℂ) :
    analyticOrderAt (DirichletCharacter.LFunction χ) s ≠ ⊤ := by
  rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s
    (fun z => analyticOnNhd_LFunction_of_nontrivial hχ z (Set.mem_univ z))]
  exact LFunction_ne_zero_function_of_nontrivial hχ

/-- The divisor coefficient is the exact natural analytic multiplicity. -/
theorem divisor_LFunction_apply_eq_analyticOrderNatAt
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {U : Set ℂ} {s : ℂ} (hsU : s ∈ U) :
    MeromorphicOn.divisor (DirichletCharacter.LFunction χ) U s =
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) s : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
    ((analyticOnNhd_LFunction_of_nontrivial hχ).mono (Set.subset_univ U)) hsU]
  have hfinite := analyticOrderAt_LFunction_ne_top hχ s
  rw [← Nat.cast_analyticOrderNatAt hfinite, ENat.map_coe,
    WithTop.untop₀_coe]




/-- Only finitely many ordinary zeros lie in a closed disk. -/
theorem divisor_LFunction_closedBall_support_finite
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (c : ℂ) (R : ℝ) :
    (MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
      (Metric.closedBall c R)).support.Finite :=
  ((analyticOnNhd_LFunction_of_nontrivial hχ).mono
    (Set.subset_univ (Metric.closedBall c R))).meromorphicOn
      |>.divisor_support_finite_of_subset (isCompact_closedBall c R)
        Set.Subset.rfl


end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/FixedDiskLogDerivative.lean` -/

section

/-! # Fixed-disk logarithmic derivative

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 90--91,
Lemma 8.6(a). Semantic review: `SEM-472`.
-/

open Filter Function Metric Set
open scoped Topology

namespace BoundedGaps.Maynard

noncomputable section

private noncomputable def selectedDivisor
    (f : ℂ -> ℂ) (c : ℂ) (R : ℝ) : Function.locallyFinsuppWithin
      (closedBall c (2 * R)) ℤ :=
  MeromorphicOn.divisor f (closedBall c (2 * R))

private noncomputable def selectedZeroProduct
    (f : ℂ -> ℂ) (c : ℂ) (R : ℝ) : ℂ -> ℂ :=
  ∏ᶠ rho : ℂ, (fun z => z - rho) ^ selectedDivisor f c R rho

private noncomputable def selectedRawFactor
    (f : ℂ -> ℂ) (c : ℂ) (R : ℝ) : ℂ -> ℂ :=
  (selectedZeroProduct f c R)⁻¹ * f

private noncomputable def selectedRegularFactor
    (f : ℂ -> ℂ) (c : ℂ) (R : ℝ) : ℂ -> ℂ :=
  toMeromorphicNFOn (selectedRawFactor f c R)
    (closedBall c (4 * R))

private theorem selectedDivisor_support_finite
    (f : ℂ -> ℂ) (c : ℂ) (R : ℝ) :
    (selectedDivisor f c R).support.Finite :=
  (selectedDivisor f c R).finiteSupport (isCompact_closedBall c (2 * R))

private theorem analyticOrderAt_ne_top_on_closedBall
    {f : ℂ -> ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    {z : ℂ} (hz : z ∈ closedBall c R) :
    analyticOrderAt f z ≠ ⊤ := by
  have hc_mem : c ∈ closedBall c R := mem_closedBall_self hR
  apply hf.analyticOrderAt_ne_top_of_isPreconnected
    (convex_closedBall c R).isPreconnected hc_mem hz
  rw [(hf c hc_mem).analyticOrderAt_eq_zero.mpr hc]
  exact WithTop.zero_ne_top

private theorem selectedDivisor_apply_eq_order
    {f : ℂ -> ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    {z : ℂ} (hz : z ∈ closedBall c (2 * R)) :
    selectedDivisor f c R z = (analyticOrderNatAt f z : ℤ) := by
  have hf_inner : AnalyticOnNhd ℂ f (closedBall c (2 * R)) :=
    hf.mono (closedBall_subset_closedBall (by linarith))
  have hfinite := analyticOrderAt_ne_top_on_closedBall (by positivity)
    hf_inner hc hz
  rw [selectedDivisor, MeromorphicOn.AnalyticOnNhd.divisor_apply hf_inner hz,
    ← Nat.cast_analyticOrderNatAt hfinite, ENat.map_coe, WithTop.untop₀_coe]

private theorem selectedDivisor_nonneg
    {f : ℂ -> ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) :
    0 ≤ selectedDivisor f c R := by
  exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg
    (hf.mono (closedBall_subset_closedBall (by linarith)))

private theorem meromorphic_selectedZeroProduct
    (f : ℂ -> ℂ) (c : ℂ) (R : ℝ) :
    Meromorphic (selectedZeroProduct f c R) := by
  simpa [selectedZeroProduct] using
    (Function.FactorizedRational.meromorphicNFOn_univ
      (selectedDivisor f c R)).meromorphicOn

private theorem meromorphicOn_selectedRawFactor
    {f : ℂ -> ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) :
    MeromorphicOn (selectedRawFactor f c R) (closedBall c (4 * R)) := by
  exact (meromorphic_selectedZeroProduct f c R).meromorphicOn.inv.mul
    hf.meromorphicOn

private theorem meromorphicOrderAt_selectedRawFactor
    {f : ℂ -> ℂ} {c z : ℂ} {R : ℝ}
    (hfz : AnalyticAt ℂ f z) :
    meromorphicOrderAt (selectedRawFactor f c R) z =
      -(selectedDivisor f c R z : WithTop ℤ) +
        (analyticOrderAt f z).map (↑) := by
  rw [selectedRawFactor,
    meromorphicOrderAt_mul
      ((meromorphic_selectedZeroProduct f c R z).inv) hfz.meromorphicAt,
    meromorphicOrderAt_inv,
    selectedZeroProduct,
    Function.FactorizedRational.meromorphicOrderAt_eq
      (selectedDivisor f c R) (selectedDivisor_support_finite f c R),
    hfz.meromorphicOrderAt_eq]

private theorem meromorphicOrderAt_selectedRawFactor_eq_zero
    {f : ℂ -> ℂ} {c z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hz : z ∈ closedBall c (2 * R)) :
    meromorphicOrderAt (selectedRawFactor f c R) z = 0 := by
  have hz_outer : z ∈ closedBall c (4 * R) :=
    closedBall_subset_closedBall (by linarith) hz
  have hfinite := analyticOrderAt_ne_top_on_closedBall (by positivity) hf hc hz_outer
  rw [meromorphicOrderAt_selectedRawFactor (hf z hz_outer),
    selectedDivisor_apply_eq_order hR hf hc hz,
    ← Nat.cast_analyticOrderNatAt hfinite, ENat.map_coe]
  simp

private theorem meromorphicOrderAt_selectedRawFactor_nonneg
    {f : ℂ -> ℂ} {c z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hz : z ∈ closedBall c (4 * R)) :
    0 ≤ meromorphicOrderAt (selectedRawFactor f c R) z := by
  by_cases hz_inner : z ∈ closedBall c (2 * R)
  · rw [meromorphicOrderAt_selectedRawFactor_eq_zero hR hf hc hz_inner]
  · have hfinite := analyticOrderAt_ne_top_on_closedBall (by positivity) hf hc hz
    rw [meromorphicOrderAt_selectedRawFactor (hf z hz),
      selectedDivisor, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz_inner,
      ← Nat.cast_analyticOrderNatAt hfinite, ENat.map_coe]
    simp only [WithTop.coe_zero, neg_zero, zero_add]
    exact_mod_cast Nat.zero_le (analyticOrderNatAt f z)

private theorem analyticOnNhd_selectedRegularFactor
    {f : ℂ -> ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0) :
    AnalyticOnNhd ℂ (selectedRegularFactor f c R) (closedBall c (4 * R)) := by
  intro z hz
  have hraw := meromorphicOn_selectedRawFactor hf
  have hnf := meromorphicNFOn_toMeromorphicNFOn
    (selectedRawFactor f c R) (closedBall c (4 * R)) hz
  unfold selectedRegularFactor
  rw [← hnf.meromorphicOrderAt_nonneg_iff_analyticAt,
    meromorphicOrderAt_toMeromorphicNFOn hraw hz]
  exact meromorphicOrderAt_selectedRawFactor_nonneg hR hf hc hz

private theorem selectedRegularFactor_ne_zero
    {f : ℂ -> ℂ} {c z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hz : z ∈ closedBall c (2 * R)) :
    selectedRegularFactor f c R z ≠ 0 := by
  have hz_outer : z ∈ closedBall c (4 * R) :=
    closedBall_subset_closedBall (by linarith) hz
  have hraw := meromorphicOn_selectedRawFactor hf
  have hnf := meromorphicNFOn_toMeromorphicNFOn
    (selectedRawFactor f c R) (closedBall c (4 * R)) hz_outer
  unfold selectedRegularFactor
  rw [← hnf.meromorphicOrderAt_eq_zero_iff,
    meromorphicOrderAt_toMeromorphicNFOn hraw hz_outer]
  exact meromorphicOrderAt_selectedRawFactor_eq_zero hR hf hc hz

private theorem selectedZeroProduct_ne_zero_of_divisor_eq_zero
    {f : ℂ -> ℂ} {c z : ℂ} {R : ℝ}
    (hz : selectedDivisor f c R z = 0) :
    selectedZeroProduct f c R z ≠ 0 := by
  simpa [selectedZeroProduct] using
    (Function.FactorizedRational.ne_zero (d := selectedDivisor f c R) hz)

private theorem selectedRegularFactor_eq_raw
    {f : ℂ -> ℂ} {c z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R)))
    (hz : z ∈ closedBall c (4 * R))
    (hPz : selectedZeroProduct f c R z ≠ 0) :
    selectedRegularFactor f c R z = selectedRawFactor f c R z := by
  have hraw := meromorphicOn_selectedRawFactor hf
  have hP_analytic : AnalyticAt ℂ (selectedZeroProduct f c R) z := by
    unfold selectedZeroProduct
    exact Function.FactorizedRational.analyticAt
      (selectedDivisor_nonneg hR hf z)
  have hraw_nf : MeromorphicNFAt (selectedRawFactor f c R) z := by
    apply AnalyticAt.meromorphicNFAt
    unfold selectedRawFactor
    exact (hP_analytic.inv hPz).mul (hf z hz)
  rw [selectedRegularFactor,
    toMeromorphicNFOn_eq_toMeromorphicNFAt hraw hz,
    toMeromorphicNFAt_eq_self.2 hraw_nf]

private theorem selectedDivisor_apply_center_eq_zero
    {f : ℂ -> ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0) :
    selectedDivisor f c R c = 0 := by
  rw [selectedDivisor_apply_eq_order hR hf hc (by simp [hR.le])]
  have horder := (hf c (by simp [hR.le])).analyticOrderAt_eq_zero.mpr hc
  simp [analyticOrderNatAt, horder]

private theorem selectedDivisor_apply_eq_zero_of_ne_zero
    {f : ℂ -> ℂ} {c z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hz : z ∈ closedBall c (2 * R)) (hfz : f z ≠ 0) :
    selectedDivisor f c R z = 0 := by
  rw [selectedDivisor_apply_eq_order hR hf hc hz]
  have hz_outer : z ∈ closedBall c (4 * R) :=
    closedBall_subset_closedBall (by linarith) hz
  have horder := (hf z hz_outer).analyticOrderAt_eq_zero.mpr hfz
  simp [analyticOrderNatAt, horder]

private theorem norm_selectedZeroProduct_center_le_sphere
    {f : ℂ -> ℂ} {c w : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hw : w ∈ sphere c (4 * R)) :
    ‖selectedZeroProduct f c R c‖ ≤ ‖selectedZeroProduct f c R w‖ := by
  let D := selectedDivisor f c R
  have hD : D.support.Finite := selectedDivisor_support_finite f c R
  have hmul (x : ℂ) : (fun rho => (x - rho) ^ D rho).mulSupport ⊆ hD.toFinset := by
    intro rho hrho
    apply hD.mem_toFinset.mpr
    intro hzero
    simp [hzero] at hrho
  rw [selectedZeroProduct, Function.FactorizedRational.finprod_eq_fun hD]
  change ‖∏ᶠ rho : ℂ, (c - rho) ^ D rho‖ ≤
    ‖∏ᶠ rho : ℂ, (w - rho) ^ D rho‖
  rw [finprod_eq_prod_of_mulSupport_subset _ (hmul c),
    finprod_eq_prod_of_mulSupport_subset _ (hmul w), norm_prod, norm_prod]
  apply Finset.prod_le_prod
  · intro rho hrho
    exact norm_nonneg _
  · intro rho hrho
    have hrho_support : rho ∈ D.support := hD.mem_toFinset.mp hrho
    have hrho_inner : rho ∈ closedBall c (2 * R) := D.supportWithinDomain hrho_support
    have hrho_dist : dist rho c ≤ 2 * R := mem_closedBall.mp hrho_inner
    have hbase : ‖c - rho‖ ≤ ‖w - rho‖ := by
      have htriangle := dist_triangle w rho c
      rw [mem_sphere] at hw
      rw [hw] at htriangle
      calc
        ‖c - rho‖ = dist rho c := by
          rw [dist_eq_norm]
          simpa only [neg_sub] using (norm_neg (c - rho)).symm
        _ ≤ 2 * R := hrho_dist
        _ ≤ dist w rho := by linarith [htriangle, hrho_dist]
        _ = ‖w - rho‖ := dist_eq_norm w rho
    rw [selectedDivisor_apply_eq_order hR hf hc hrho_inner]
    simp only [zpow_natCast, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hbase _

private theorem norm_selectedRegularFactor_le_on_outer_sphere
    {f : ℂ -> ℂ} {c w : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hbound : ∀ z ∈ sphere c (4 * R),
      ‖f z‖ ≤ Real.exp M * ‖f c‖)
    (hw : w ∈ sphere c (4 * R)) :
    ‖selectedRegularFactor f c R w‖ ≤
      Real.exp M * ‖selectedRegularFactor f c R c‖ := by
  have hc_outer : c ∈ closedBall c (4 * R) := by simp [hR.le]
  have hw_outer : w ∈ closedBall c (4 * R) := sphere_subset_closedBall hw
  have hw_not_inner : w ∉ closedBall c (2 * R) := by
    intro hw_inner
    have hw_dist := mem_sphere.mp hw
    have hw_inner_dist := mem_closedBall.mp hw_inner
    linarith
  have hDc := selectedDivisor_apply_center_eq_zero hR hf hc
  have hDw : selectedDivisor f c R w = 0 := by
    unfold selectedDivisor
    exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hw_not_inner
  have hPc := selectedZeroProduct_ne_zero_of_divisor_eq_zero hDc
  have hPw := selectedZeroProduct_ne_zero_of_divisor_eq_zero hDw
  rw [selectedRegularFactor_eq_raw hR hf hw_outer hPw,
    selectedRegularFactor_eq_raw hR hf hc_outer hPc]
  simp only [selectedRawFactor, Pi.mul_apply, Pi.inv_apply, norm_mul, norm_inv]
  have hPnorm := norm_selectedZeroProduct_center_le_sphere hR hf hc hw
  have hPinv : ‖selectedZeroProduct f c R w‖⁻¹ ≤
      ‖selectedZeroProduct f c R c‖⁻¹ := by
    exact (inv_le_inv₀ (norm_pos_iff.mpr hPw) (norm_pos_iff.mpr hPc)).2 hPnorm
  calc
    ‖selectedZeroProduct f c R w‖⁻¹ * ‖f w‖
        ≤ ‖selectedZeroProduct f c R w‖⁻¹ *
            (Real.exp M * ‖f c‖) :=
      mul_le_mul_of_nonneg_left (hbound w hw) (inv_nonneg.mpr (norm_nonneg _))
    _ ≤ ‖selectedZeroProduct f c R c‖⁻¹ *
          (Real.exp M * ‖f c‖) :=
      mul_le_mul_of_nonneg_right hPinv (mul_nonneg (Real.exp_pos M).le (norm_nonneg _))
    _ = Real.exp M *
          (‖selectedZeroProduct f c R c‖⁻¹ * ‖f c‖) := by ring

private theorem norm_selectedRegularFactor_le_on_outer_closedBall
    {f : ℂ -> ℂ} {c z : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hbound : ∀ w ∈ sphere c (4 * R),
      ‖f w‖ ≤ Real.exp M * ‖f c‖)
    (hz : z ∈ closedBall c (4 * R)) :
    ‖selectedRegularFactor f c R z‖ ≤
      Real.exp M * ‖selectedRegularFactor f c R c‖ := by
  have h4R : 4 * R ≠ 0 := by positivity
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    ((analyticOnNhd_selectedRegularFactor hR hf hc).differentiableOn.diffContOnCl_ball
      (by rfl))
  · intro w hw
    apply norm_selectedRegularFactor_le_on_outer_sphere hR hf hc hbound
    simpa [frontier_ball c h4R] using hw
  · simpa [closure_ball c h4R] using hz

private theorem norm_logDeriv_selectedRegularFactor_le
    {f : ℂ -> ℂ} {c s : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hbound : ∀ z ∈ sphere c (4 * R), ‖f z‖ ≤ Real.exp M * ‖f c‖)
    (hs : s ∈ closedBall c R) :
    ‖logDeriv (selectedRegularFactor f c R) s‖ ≤ 16 * M / R := by
  let G := selectedRegularFactor f c R
  have hG : AnalyticOnNhd ℂ G (closedBall c (4 * R)) :=
    analyticOnNhd_selectedRegularFactor hR hf hc
  have hGne {z : ℂ} (hz : z ∈ closedBall c (2 * R)) : G z ≠ 0 :=
    selectedRegularFactor_ne_zero hR hf hc hz
  have hlogDiff : DifferentiableOn ℂ (logDeriv G) (ball c (2 * R)) := by
    intro z hz
    have hz' : z ∈ closedBall c (2 * R) := mem_closedBall.mpr (mem_ball.mp hz).le
    have hz'' : z ∈ closedBall c (4 * R) :=
      closedBall_subset_closedBall (by linarith) hz'
    exact (by
      simpa [logDeriv] using ((hG z hz'').deriv.div (hG z hz'') (hGne hz'))
      : AnalyticAt ℂ (logDeriv G) z).differentiableAt.differentiableWithinAt
  obtain ⟨H, hHc, hH⟩ := hlogDiff.isExactOn_ball.with_val_at c 0
  have hHDiff : DifferentiableOn ℂ H (ball c (2 * R)) :=
    fun z hz => (hH z hz).differentiableAt.differentiableWithinAt
  have hc_ball : c ∈ ball c (2 * R) := mem_ball_self (by positivity)
  have hGDiff : DifferentiableOn ℂ G (ball c (2 * R)) := by
    intro z hz
    exact (hG z (closedBall_subset_closedBall (by linarith)
      (mem_closedBall.mpr (mem_ball.mp hz).le))).differentiableAt.differentiableWithinAt
  have hEDiff : DifferentiableOn ℂ (Complex.exp ∘ H) (ball c (2 * R)) := by
    intro z hz
    exact (Complex.differentiableAt_exp.comp z
      (hH z hz).differentiableAt).differentiableWithinAt
  have hlogEq : EqOn (logDeriv (Complex.exp ∘ H)) (logDeriv G) (ball c (2 * R)) := by
    intro z hz
    rw [logDeriv_comp Complex.differentiableAt_exp (hH z hz).differentiableAt]
    simp only [logDeriv_apply, (Complex.hasDerivAt_exp _).deriv,
      div_self (Complex.exp_ne_zero _), one_mul, (hH z hz).deriv]
  obtain ⟨a, ha, hEq⟩ := (logDeriv_eqOn_iff hEDiff hGDiff isOpen_ball
    (convex_ball c (2 * R)).isPreconnected (fun z hz => hGne
      (mem_closedBall.mpr (mem_ball.mp hz).le))
    (fun z _ => Complex.exp_ne_zero (H z))).mp hlogEq
  have hGc : G c ≠ 0 := hGne (by simp [hR.le])
  have ha_eq : a = (G c)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa [hHc, smul_eq_mul] using (hEq hc_ball).symm
  have hHre {z : ℂ} (hz : z ∈ ball c (2 * R)) : (H z).re ≤ M := by
    have hz_outer : z ∈ closedBall c (4 * R) :=
      closedBall_subset_closedBall (by linarith)
        (mem_closedBall.mpr (mem_ball.mp hz).le)
    have hmax := norm_selectedRegularFactor_le_on_outer_closedBall hR hf hc hbound hz_outer
    have hexp : ‖Complex.exp (H z)‖ ≤ Real.exp M := by
      change ‖(Complex.exp ∘ H) z‖ ≤ Real.exp M
      rw [hEq hz, ha_eq]
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv]
      calc
        ‖G c‖⁻¹ * ‖G z‖ ≤ ‖G c‖⁻¹ * (Real.exp M * ‖G c‖) :=
          mul_le_mul_of_nonneg_left hmax (inv_nonneg.mpr (norm_nonneg _))
        _ = Real.exp M := by field_simp
    rw [Complex.norm_exp] at hexp
    exact Real.exp_le_exp.mp hexp
  have hHbound {w : ℂ} (hw : w ∈ sphere s (R / 2)) : ‖H w‖ ≤ 6 * M := by
    have hws : dist w s = R / 2 := mem_sphere.mp hw
    have hsc : dist s c ≤ R := by simpa [dist_comm] using mem_closedBall.mp hs
    have hwc : ‖w - c‖ ≤ 3 * R / 2 := by
      rw [← dist_eq_norm]
      linarith [dist_triangle w s c]
    have huc : w - c ∈ ball (0 : ℂ) (2 * R) := by
      rw [mem_ball_zero_iff]
      linarith
    have hBC := Complex.borelCaratheodory_zero hM (f := fun u => H (c + u)) (R := 2 * R)
      (by
        intro u hu
        have hcu : c + u ∈ ball c (2 * R) := by
          simpa [mem_ball, dist_eq_norm] using hu
        exact ((hH (c + u) hcu).differentiableAt.comp u
          (by fun_prop)).differentiableWithinAt)
      (by
        intro u hu
        have hcu : c + u ∈ ball c (2 * R) := by
          simpa [mem_ball, dist_eq_norm] using hu
        exact hHre hcu)
      (by positivity) huc (by simpa using hHc)
    have hden : 0 < 2 * R - ‖w - c‖ := by linarith
    calc
      ‖H w‖ = ‖H (c + (w - c))‖ := by ring_nf
      _ ≤ 2 * M * ‖w - c‖ / (2 * R - ‖w - c‖) := hBC
      _ ≤ 6 * M := by
        rw [div_le_iff₀ hden]
        nlinarith [mul_nonneg hM.le (norm_nonneg (w - c))]
  have hclosure : closedBall s (R / 2) ⊆ ball c (2 * R) := by
    intro w hw
    have hws : dist w s ≤ R / 2 := mem_closedBall.mp hw
    have hsc : dist s c ≤ R := by simpa [dist_comm] using mem_closedBall.mp hs
    exact mem_ball.mpr (by linarith [dist_triangle w s c])
  have hCauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by positivity : 0 < R / 2)
    (hHDiff.diffContOnCl_ball hclosure)
    (fun w hw => hHbound hw)
  rw [(hH s (hclosure (mem_closedBall_self (by positivity)))).deriv] at hCauchy
  calc
    ‖logDeriv G s‖ ≤ 6 * M / (R / 2) := hCauchy
    _ ≤ 16 * M / R := by
      field_simp
      nlinarith

private theorem logDeriv_factorizedRational_eq_finsum
    {D : ℂ -> ℤ} (hD : D.support.Finite) {s : ℂ} (hs : D s = 0) :
    logDeriv (∏ᶠ rho : ℂ, (fun z => z - rho) ^ D rho) s =
      ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho) := by
  have hmul : (fun rho : ℂ => (fun z : ℂ => z - rho) ^ D rho).mulSupport ⊆
      hD.toFinset := by
    rw [Function.FactorizedRational.mulSupport]
    exact hD.coe_toFinset.ge
  rw [finprod_eq_prod_of_mulSupport_subset _ hmul]
  have hprod : (∏ rho ∈ hD.toFinset, (fun z : ℂ => z - rho) ^ D rho) =
      fun z => ∏ rho ∈ hD.toFinset, (z - rho) ^ D rho := by ext z; simp
  rw [hprod, logDeriv_prod]
  · rw [finsum_eq_sum_of_support_subset]
    · apply Finset.sum_congr rfl
      intro rho _
      rw [logDeriv_fun_zpow (by fun_prop)]
      simp [logDeriv_apply, div_eq_mul_inv]
    · intro rho hrho
      apply hD.mem_toFinset.mpr
      intro hzero
      simp [hzero] at hrho
  · intro rho hrho
    have hrho := Function.mem_support.mp (hD.mem_toFinset.mp hrho)
    exact zpow_ne_zero _ (sub_ne_zero.mpr (fun h => hrho (h ▸ hs)))
  · intro rho hrho
    have hrho := Function.mem_support.mp (hD.mem_toFinset.mp hrho)
    exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z - rho) s).zpow
      (.inl (sub_ne_zero.mpr (fun h => hrho (h ▸ hs))))

private theorem logDeriv_selectedRegularFactor_eq_sub_finsum
    {f : ℂ -> ℂ} {c s : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hs : s ∈ closedBall c R) (hfs : f s ≠ 0) :
    logDeriv (selectedRegularFactor f c R) s = logDeriv f s -
      ∑ᶠ rho : ℂ, ((selectedDivisor f c R rho : ℤ) : ℂ) / (s - rho) := by
  have hs_inner : s ∈ closedBall c (2 * R) :=
    closedBall_subset_closedBall (by linarith) hs
  have hs_outer : s ∈ closedBall c (4 * R) :=
    closedBall_subset_closedBall (by linarith) hs
  have hDs := selectedDivisor_apply_eq_zero_of_ne_zero hR hf hc hs_inner hfs
  have hPs := selectedZeroProduct_ne_zero_of_divisor_eq_zero hDs
  have hPa : AnalyticAt ℂ (selectedZeroProduct f c R) s := by
    unfold selectedZeroProduct
    exact Function.FactorizedRational.analyticAt (selectedDivisor_nonneg hR hf s)
  have hrawa : AnalyticAt ℂ (selectedRawFactor f c R) s := by
    unfold selectedRawFactor
    exact (hPa.inv hPs).mul (hf s hs_outer)
  have hraw := meromorphicOn_selectedRawFactor hf
  have heq : selectedRegularFactor f c R =ᶠ[nhds s] selectedRawFactor f c R := by
    simpa [selectedRegularFactor, toMeromorphicNFAt_eq_self.2 hrawa.meromorphicNFAt] using
      toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hraw hs_outer
  have hlogeq : logDeriv (selectedRegularFactor f c R) s =
      logDeriv (selectedRawFactor f c R) s := by
    simp only [logDeriv_apply]
    rw [heq.deriv_eq, heq.self_of_nhds]
  rw [hlogeq]
  have hrawfun : selectedRawFactor f c R =
      fun z => f z / selectedZeroProduct f c R z := by
    funext z
    simp [selectedRawFactor, div_eq_mul_inv, mul_comm]
  rw [hrawfun, logDeriv_div s hfs hPs (hf s hs_outer).differentiableAt
    hPa.differentiableAt]
  rw [selectedZeroProduct, logDeriv_factorizedRational_eq_finsum
    (selectedDivisor_support_finite f c R) hDs]

/-- A zero-free logarithmic derivative after removing the zeros in the `2R` disk.
The constants follow from Borel--Caratheodory and Cauchy's estimate. -/
theorem norm_logDeriv_sub_divisor_finsum_le
    {f : ℂ → ℂ} {c s : ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R)))
    (hc : f c ≠ 0)
    (hbound : ∀ z ∈ sphere c (4 * R),
      ‖f z‖ ≤ Real.exp M * ‖f c‖)
    (hs : s ∈ closedBall c R) (hfs : f s ≠ 0) :
    ‖logDeriv f s - ∑ᶠ rho : ℂ,
      ((MeromorphicOn.divisor f (closedBall c (2 * R))) rho : ℂ) /
        (s - rho)‖ ≤ 16 * M / R := by
  have hid := logDeriv_selectedRegularFactor_eq_sub_finsum hR hf hc hs hfs
  rw [selectedDivisor] at hid
  rw [← hid]
  rcases hM.eq_or_lt with rfl | hM
  · simp only [mul_zero, zero_div]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hεR : 0 < ε * R / 16 := by positivity
    have hb : ∀ z ∈ sphere c (4 * R),
        ‖f z‖ ≤ Real.exp (ε * R / 16) * ‖f c‖ := by
      intro z hz
      exact (hbound z hz).trans (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr hεR.le) (norm_nonneg _))
    have he := norm_logDeriv_selectedRegularFactor_le hR hεR hf hc hb hs
    exact he.trans_eq (by field_simp [hR.ne']; ring)
  · exact norm_logDeriv_selectedRegularFactor_le hR hM hf hc hbound hs

end

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/PrimitiveLFunctionRadiusTwelve.lean` -/

section

/-!
# Primitive Dirichlet L-functions on radius-twelve spheres

This file turns fixed-strip polynomial growth into the relative boundary
growth used by the fixed-disk logarithmic-derivative argument. The center is
`2+it`, the inner radius is `3`, and the growth sphere has radius `12`.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 89--91,
Lemmas 8.5--8.6, and printed p. 114, Lemma 11.4. The natural exponents are
conservative project consequences, not source-printed constants. Semantic
review: `SEM-478`.
-/

namespace BoundedGaps.Maynard

open Complex Metric

private lemma radiusTwelveSphere_geometry
    (t : ℝ) (z : ℂ)
    (hz : z ∈ sphere ((2 : ℂ) + t * I) 12) :
    -(10 : ℝ) ≤ z.re ∧ z.re ≤ 14 ∧
      |z.im| + 2 ≤ 7 * (|t| + 2) := by
  have hdist : ‖z - ((2 : ℂ) + t * I)‖ = 12 := by
    simpa [mem_sphere, Complex.dist_eq] using hz
  have hre : |z.re - 2| ≤ 12 := by
    calc
      |z.re - 2| = |(z - ((2 : ℂ) + t * I)).re| := by simp
      _ ≤ ‖z - ((2 : ℂ) + t * I)‖ := Complex.abs_re_le_norm _
      _ = 12 := hdist
  have him : |z.im - t| ≤ 12 := by
    calc
      |z.im - t| = |(z - ((2 : ℂ) + t * I)).im| := by simp
      _ ≤ ‖z - ((2 : ℂ) + t * I)‖ := Complex.abs_im_le_norm _
      _ = 12 := hdist
  have hz_im : |z.im| ≤ |t| + 12 := by
    have hadd := abs_add_le (z.im - t) t
    rw [sub_add_cancel] at hadd
    linarith
  constructor
  · rw [abs_le] at hre
    linarith
  constructor
  · rw [abs_le] at hre
    linarith
  · linarith [abs_nonneg t]

/-- Primitive Dirichlet L-functions have one absolute polynomial bound on
the radius-twelve spheres used by the fixed-disk argument. -/
theorem exists_nat_norm_LFunction_radiusTwelveSphere_le :
    ∃ E : ℕ, 36 ≤ E ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ (t : ℝ) (z : ℂ),
            z ∈ sphere ((2 : ℂ) + t * I) 12 →
              ‖DirichletCharacter.LFunction chi z‖ ≤
                ((q : ℝ) * (|t| + 2)) ^ E := by
  obtain ⟨A, hA, hstrip⟩ := exists_norm_LFunction_fixedStrip_le_pow
  refine ⟨3 * A, by omega, ?_⟩
  intro q _ hq chi hchi t z hz
  obtain ⟨hzlo, _hzhi, hzheight⟩ := radiusTwelveSphere_geometry t z hz
  let B : ℝ := (q : ℝ) * (|t| + 2)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := one_le_two.trans hq2
  have hq0 : (0 : ℝ) ≤ q := zero_le_one.trans hq1
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hq1
  have hT2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hT1 : (1 : ℝ) ≤ |t| + 2 := one_le_two.trans hT2
  have hB4 : (4 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hB0 : (0 : ℝ) ≤ B := zero_le_one.trans hB1
  have hqB : (q : ℝ) ≤ B := by
    calc
      (q : ℝ) = (q : ℝ) * 1 := by ring
      _ ≤ (q : ℝ) * (|t| + 2) :=
        mul_le_mul_of_nonneg_left hT1 hq0
      _ = B := rfl
  by_cases hleft : z.re ≤ (1 / 2 : ℝ)
  · have hzT0 : (0 : ℝ) ≤ |z.im| + 2 := by positivity
    have hlocal : (q : ℝ) * (|z.im| + 2) ≤ B ^ 3 := by
      calc
        (q : ℝ) * (|z.im| + 2) ≤
            (q : ℝ) * (7 * (|t| + 2)) :=
          mul_le_mul_of_nonneg_left hzheight hq0
        _ = 7 * B := by simp [B]; ring
        _ ≤ B ^ 2 * B := by
          apply mul_le_mul_of_nonneg_right _ hB0
          nlinarith [sq_nonneg B]
        _ = B ^ 3 := by ring
    calc
      ‖DirichletCharacter.LFunction chi z‖ ≤
          ((q : ℝ) * (|z.im| + 2)) ^ A :=
        hstrip q hq chi hchi z hzlo hleft
      _ ≤ (B ^ 3) ^ A :=
        pow_le_pow_left₀ (mul_nonneg hq0 hzT0) hlocal A
      _ = B ^ (3 * A) := by rw [pow_mul]
  · have hhalf : (1 / 2 : ℝ) ≤ z.re := le_of_not_ge hleft
    by_cases hcentral : z.re ≤ 2
    · have hcentralBound := norm_LFunction_centralStrip_le hq chi hchi
          (sigma := z.re) (t := z.im) hhalf hcentral
      have hzarg : (((z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I) = z := by
        apply Complex.ext <;> simp
      rw [hzarg] at hcentralBound
      have hsqrt : Real.sqrt (q : ℝ) ≤ q :=
        Real.sqrt_le_self_iff.mpr (Or.inr hq1)
      have hlog : Real.log (q : ℝ) ≤ q :=
        (Real.log_le_sub_one_of_pos hqpos).trans
          (sub_le_self _ zero_le_one)
      have h14 : (14 : ℝ) ≤ B ^ 2 := by
        nlinarith [sq_nonneg B]
      have hcentralPower :
          2 * (|z.im| + 2) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤
            B ^ 4 := by
        calc
          2 * (|z.im| + 2) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤
              2 * (7 * (|t| + 2)) * (q : ℝ) * (q : ℝ) := by
            gcongr
          _ = 14 * (q : ℝ) * B := by simp [B]; ring
          _ ≤ 14 * B * B := by gcongr
          _ = 14 * B ^ 2 := by ring
          _ ≤ B ^ 2 * B ^ 2 :=
            mul_le_mul_of_nonneg_right h14 (sq_nonneg B)
          _ = B ^ 4 := by ring
      calc
        ‖DirichletCharacter.LFunction chi z‖ ≤
            2 * (|z.im| + 2) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
          hcentralBound
        _ ≤ B ^ 4 := hcentralPower
        _ ≤ B ^ (3 * A) :=
          pow_le_pow_right₀ hB1 (by omega)
    · have hfar : (2 : ℝ) ≤ z.re := le_of_not_ge hcentral
      have hfarBound := norm_LFunction_farRight_le_three chi z hfar
      have hBpow : B ≤ B ^ (3 * A) := by
        calc
          B = B ^ 1 := by simp
          _ ≤ B ^ (3 * A) := pow_le_pow_right₀ hB1 (by omega)
      exact hfarBound.trans (le_trans (by linarith) hBpow)

/-- The radius-twelve absolute bound can be made relative to the nonzero
far-right center with one additional conductor-height power. -/
theorem exists_nat_norm_LFunction_radiusTwelveSphere_le_exp_mul_center :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ (t : ℝ) (z : ℂ),
            z ∈ sphere ((2 : ℂ) + t * I) 12 →
              ‖DirichletCharacter.LFunction chi z‖ ≤
                Real.exp
                    ((A : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) *
                  ‖DirichletCharacter.LFunction chi ((2 : ℂ) + t * I)‖ := by
  obtain ⟨E, hE, habsolute⟩ :=
    exists_nat_norm_LFunction_radiusTwelveSphere_le
  refine ⟨E + 1, by omega, ?_⟩
  intro q _ hq chi hchi t z hz
  let c : ℂ := (2 : ℂ) + t * I
  let B : ℝ := (q : ℝ) * (|t| + 2)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hT2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hB4 : (4 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hBpos : (0 : ℝ) < B := zero_lt_four.trans_le hB4
  have hc : DirichletCharacter.LFunction chi c ≠ 0 := by
    have hc_re : 1 < c.re := by simp [c]
    rw [DirichletCharacter.LFunction_eq_LSeries chi hc_re]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re chi hc_re
  have hinv : ‖(DirichletCharacter.LFunction chi c)⁻¹‖ ≤ 3 := by
    simpa [c] using norm_inv_LFunction_two_add_mul_I_le_three chi t
  have hone_center :
      (1 : ℝ) ≤ 3 * ‖DirichletCharacter.LFunction chi c‖ := by
    calc
      (1 : ℝ) = ‖(DirichletCharacter.LFunction chi c)⁻¹ *
          DirichletCharacter.LFunction chi c‖ := by
        rw [inv_mul_cancel₀ hc, norm_one]
      _ = ‖(DirichletCharacter.LFunction chi c)⁻¹‖ *
          ‖DirichletCharacter.LFunction chi c‖ := norm_mul _ _
      _ ≤ 3 * ‖DirichletCharacter.LFunction chi c‖ :=
        mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
  have hone_base_center :
      (1 : ℝ) ≤ B * ‖DirichletCharacter.LFunction chi c‖ := by
    exact hone_center.trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have habs : ‖DirichletCharacter.LFunction chi z‖ ≤ B ^ E := by
    simpa [B, c] using habsolute q hq chi hchi t z hz
  have hexp :
      Real.exp (((E + 1 : ℕ) : ℝ) * Real.log B) = B ^ (E + 1) := by
    rw [Real.exp_nat_mul, Real.exp_log hBpos]
  calc
    ‖DirichletCharacter.LFunction chi z‖ ≤ B ^ E := habs
    _ = B ^ E * 1 := by ring
    _ ≤ B ^ E * (B * ‖DirichletCharacter.LFunction chi c‖) :=
      mul_le_mul_of_nonneg_left hone_base_center (pow_nonneg hBpos.le E)
    _ = B ^ (E + 1) * ‖DirichletCharacter.LFunction chi c‖ := by
      rw [pow_succ]
      ring
    _ = Real.exp (((E + 1 : ℕ) : ℝ) * Real.log B) *
        ‖DirichletCharacter.LFunction chi c‖ := by rw [hexp]
    _ = Real.exp
          (((E + 1 : ℕ) : ℝ) *
            Real.log ((q : ℝ) * (|t| + 2))) *
        ‖DirichletCharacter.LFunction chi ((2 : ℂ) + t * I)‖ := by
      rfl

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/PrimitiveLFunctionFixedDisk.lean` -/

section

/-!
# Primitive Dirichlet L-functions on a fixed disk

This file specializes the fixed-disk logarithmic-derivative theorem to the
center `2+it` and radii `3`, `6`, and `12`. The selected radius-six divisor is
the ordinary L-function divisor, so it includes trivial zeros when they lie in
the disk.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 90--92,
Lemma 8.6(a) and the proof of Lemma 8.2(b), and printed pp. 112--114,
Lemma 11.4 and its zero conventions. Semantic review: `SEM-479`.
-/

namespace BoundedGaps.Maynard

open Complex Metric

noncomputable section

/-- The radius-six ordinary divisor coefficient is the analytic multiplicity
inside the closed disk and zero outside it. -/
theorem divisor_LFunction_radiusSix_apply
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t : ℝ) (rho : ℂ) :
    MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
        (closedBall ((2 : ℂ) + t * I) 6) rho =
      ((if dist rho ((2 : ℂ) + t * I) ≤ 6 then
          analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
        else 0 : ℕ) : ℤ) := by
  have hchi_ne := character_ne_one_of_isPrimitive hq chi hchi
  by_cases hrho : dist rho ((2 : ℂ) + t * I) ≤ 6
  · rw [if_pos hrho,
      divisor_LFunction_apply_eq_analyticOrderNatAt hchi_ne
        (mem_closedBall.mpr hrho)]
  · rw [if_neg hrho,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _
        (by simpa [mem_closedBall] using hrho)]
    norm_cast

/-- Reindex the radius-six ordinary divisor sum by conditional analytic
multiplicity. -/
theorem finsum_divisor_LFunction_radiusSix_eq
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t : ℝ) (s : ℂ) :
    (∑ᶠ rho : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
          (closedBall ((2 : ℂ) + t * I) 6)) rho : ℂ) / (s - rho)) =
      ∑ᶠ rho : ℂ,
        ((if dist rho ((2 : ℂ) + t * I) ≤ 6 then
            analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
          else 0 : ℕ) : ℂ) / (s - rho) := by
  apply finsum_congr
  intro rho
  rw [divisor_LFunction_radiusSix_apply hq chi hchi t rho]
  norm_cast

/-- The primitive Dirichlet specialization of the fixed-disk theorem,
retaining the exact ordinary divisor of the closed radius-six disk. -/
theorem exists_nat_norm_logDeriv_LFunction_sub_radiusSix_divisor_finsum_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ (t : ℝ) (s : ℂ),
            s ∈ closedBall ((2 : ℂ) + t * I) 3 →
              DirichletCharacter.LFunction chi s ≠ 0 →
                ‖logDeriv (DirichletCharacter.LFunction chi) s -
                    ∑ᶠ rho : ℂ,
                      ((MeromorphicOn.divisor
                        (DirichletCharacter.LFunction chi)
                        (closedBall ((2 : ℂ) + t * I) 6)) rho : ℂ) /
                          (s - rho)‖ ≤
                  16 * ((A : ℝ) *
                    Real.log ((q : ℝ) * (|t| + 2))) / 3 := by
  obtain ⟨A, hA, hgrowth⟩ :=
    exists_nat_norm_LFunction_radiusTwelveSphere_le_exp_mul_center
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi t s hs hLs
  let c : ℂ := (2 : ℂ) + t * I
  let B : ℝ := (q : ℝ) * (|t| + 2)
  let M : ℝ := (A : ℝ) * Real.log B
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hT2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hB4 : (4 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hM : 0 ≤ M := by
    exact mul_nonneg (Nat.cast_nonneg A) (Real.log_nonneg (by linarith))
  have hchi_ne : chi ≠ 1 := character_ne_one_of_isPrimitive hq chi hchi
  have hf : AnalyticOnNhd ℂ (DirichletCharacter.LFunction chi)
      (closedBall c (4 * (3 : ℝ))) :=
    fun z _ => (DirichletCharacter.differentiable_LFunction hchi_ne).analyticAt z
  have hc : DirichletCharacter.LFunction chi c ≠ 0 := by
    have hc_re : 1 < c.re := by simp [c]
    rw [DirichletCharacter.LFunction_eq_LSeries chi hc_re]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re chi hc_re
  have hbound : ∀ z ∈ sphere c (4 * (3 : ℝ)),
      ‖DirichletCharacter.LFunction chi z‖ ≤
        Real.exp M * ‖DirichletCharacter.LFunction chi c‖ := by
    intro z hz
    norm_num at hz
    simpa [c, M, B] using
      hgrowth q hq chi hchi t z (by simpa [c] using hz)
  have hfixed := norm_logDeriv_sub_divisor_finsum_le
    (f := DirichletCharacter.LFunction chi) (c := c) (s := s)
    (R := (3 : ℝ)) (M := M) (by norm_num) hM hf hc hbound
    (by simpa [c] using hs) hLs
  rw [show (2 : ℝ) * 3 = 6 by norm_num] at hfixed
  simpa [c, M, B] using hfixed

/-- The same fixed-disk estimate with each ordinary zero represented by its
conditional analytic multiplicity. -/
theorem exists_nat_norm_logDeriv_LFunction_sub_radiusSix_analyticOrder_finsum_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ (t : ℝ) (s : ℂ),
            s ∈ closedBall ((2 : ℂ) + t * I) 3 →
              DirichletCharacter.LFunction chi s ≠ 0 →
                ‖logDeriv (DirichletCharacter.LFunction chi) s -
                    ∑ᶠ rho : ℂ,
                      ((if dist rho ((2 : ℂ) + t * I) ≤ 6 then
                          analyticOrderNatAt
                            (DirichletCharacter.LFunction chi) rho
                        else 0 : ℕ) : ℂ) / (s - rho)‖ ≤
                  16 * ((A : ℝ) *
                    Real.log ((q : ℝ) * (|t| + 2))) / 3 := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_nat_norm_logDeriv_LFunction_sub_radiusSix_divisor_finsum_le
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi t s hs hLs
  rw [← finsum_divisor_LFunction_radiusSix_eq hq chi hchi t s]
  exact hbound q hq chi hchi t s hs hLs

end

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/PrimitiveLFunctionSelectedSubdivisor.lean` -/

section

/-!
# Selected subdivisors of primitive Dirichlet L-functions

This file turns the full ordinary radius-six zero sum into a one-sided bound
for every finite submultiset dominated by analytic multiplicity. It does not
identify the selected points as nontrivial zeros.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 90--91,
Lemma 8.6(a), pp. 112--114, Lemma 11.4 and its zero conventions, and
pp. 119--120, Lemma 12.2. Semantic review: `SEM-480`.
-/

namespace BoundedGaps.Maynard

open Complex Metric

noncomputable section

/-- An ordinary zero of a primitive Dirichlet L-function of modulus greater
than one lies strictly to the left of the line `Re(s)=1`. -/
theorem LFunction_zero_re_lt_one_of_isPrimitive
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {rho : ℂ} (hzero : DirichletCharacter.LFunction chi rho = 0) :
    rho.re < 1 := by
  by_contra hrho
  exact (chi.LFunction_ne_zero_of_one_le_re
    (.inl (character_ne_one_of_isPrimitive hq chi hchi))
    (le_of_not_gt hrho)) hzero

private theorem radiusSixAnalyticOrder_hasFiniteSupport
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t : ℝ) :
    Function.HasFiniteSupport fun rho : ℂ =>
      if dist rho ((2 : ℂ) + t * I) ≤ 6 then
        analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
      else 0 := by
  apply (divisor_LFunction_closedBall_support_finite
    (character_ne_one_of_isPrimitive hq chi hchi)
    ((2 : ℂ) + t * I) 6).subset
  intro rho hrho
  rw [Function.mem_support] at hrho ⊢
  rw [divisor_LFunction_radiusSix_apply hq chi hchi t rho]
  exact_mod_cast hrho

/-- A multiplicity-bounded submultiset contributes at most the full ordinary
radius-six zero sum on the half-plane `Re(s)>=1`. -/
theorem selected_radiusSix_subdivisor_sum_le_re_analyticOrder_finsum
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t : ℝ) (s : ℂ) (hs : 1 ≤ s.re) (Z : ℂ →₀ ℕ)
    (hZ : ∀ rho : ℂ,
      Z rho ≤
        if dist rho ((2 : ℂ) + t * I) ≤ 6 then
          analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
        else 0) :
    Z.sum (fun rho m =>
        (m : ℝ) * (((s - rho)⁻¹).re)) ≤
      (∑ᶠ rho : ℂ,
        ((if dist rho ((2 : ℂ) + t * I) ≤ 6 then
            analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
          else 0 : ℕ) : ℂ) / (s - rho)).re := by
  let m : ℂ → ℕ := fun rho =>
    if dist rho ((2 : ℂ) + t * I) ≤ 6 then
      analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
    else 0
  have hm : (Function.support m).Finite :=
    radiusSixAnalyticOrder_hasFiniteSupport hq chi hchi t
  have hZsupport : Z.support ⊆ hm.toFinset := by
    intro rho hrho
    apply hm.mem_toFinset.mpr
    rw [Function.mem_support]
    intro hmrho
    have hZrho : Z rho = 0 :=
      Nat.eq_zero_of_le_zero ((hZ rho).trans_eq hmrho)
    exact Finsupp.mem_support_iff.mp hrho hZrho
  have hfullSupport :
      Function.support (fun rho : ℂ => (m rho : ℂ) / (s - rho)) ⊆
        hm.toFinset := by
    intro rho hrho
    apply hm.mem_toFinset.mpr
    rw [Function.mem_support] at hrho ⊢
    exact fun hmrho => hrho (by simp [hmrho])
  have hfullSum :
      (∑ᶠ rho : ℂ, (m rho : ℂ) / (s - rho)) =
        ∑ rho ∈ hm.toFinset, (m rho : ℂ) / (s - rho) :=
    finsum_eq_sum_of_support_subset
      (fun rho : ℂ => (m rho : ℂ) / (s - rho)) hfullSupport
  rw [Finsupp.sum_of_support_subset Z hZsupport _ (by simp)]
  change (∑ rho ∈ hm.toFinset,
      (Z rho : ℝ) * ((s - rho)⁻¹).re) ≤
    (∑ᶠ rho : ℂ, (m rho : ℂ) / (s - rho)).re
  rw [hfullSum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro rho _
  by_cases hmrho : m rho = 0
  · have hZrho : Z rho = 0 :=
      Nat.eq_zero_of_le_zero ((hZ rho).trans_eq hmrho)
    simp [hZrho, hmrho]
  · have hzero : DirichletCharacter.LFunction chi rho = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero (by
        dsimp [m] at hmrho
        split at hmrho
        · exact hmrho
        · exact False.elim (hmrho rfl))
    have hrho : rho.re < 1 :=
      LFunction_zero_re_lt_one_of_isPrimitive hq chi hchi hzero
    have hinv : 0 ≤ ((s - rho)⁻¹).re := by
      rw [Complex.inv_re]
      exact div_nonneg (by simp only [Complex.sub_re]; linarith)
        (Complex.normSq_nonneg _)
    have hcoeff : (Z rho : ℝ) ≤ (m rho : ℝ) := by
      exact_mod_cast hZ rho
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right hcoeff hinv

/-- The primitive fixed-disk lower bound for every multiplicity-bounded
submultiset of the ordinary radius-six divisor. -/
theorem exists_nat_selected_radiusSix_subdivisor_sum_sub_le_re_logDeriv_LFunction :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ (t sigma : ℝ) (Z : ℂ →₀ ℕ),
            1 ≤ sigma → sigma ≤ 2 →
              DirichletCharacter.LFunction chi
                  ((sigma : ℂ) + t * I) ≠ 0 →
                (∀ rho : ℂ,
                  Z rho ≤
                    if dist rho ((2 : ℂ) + t * I) ≤ 6 then
                      analyticOrderNatAt
                        (DirichletCharacter.LFunction chi) rho
                    else 0) →
                  Z.sum (fun rho m =>
                      (m : ℝ) *
                        ((((sigma : ℂ) + t * I) - rho)⁻¹).re) -
                      16 * ((A : ℝ) *
                        Real.log ((q : ℝ) * (|t| + 2))) / 3 ≤
                    (logDeriv (DirichletCharacter.LFunction chi)
                      ((sigma : ℂ) + t * I)).re := by
  obtain ⟨A, hA, hfixed⟩ :=
    exists_nat_norm_logDeriv_LFunction_sub_radiusSix_analyticOrder_finsum_le
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi t sigma Z hsigma1 hsigma2 hLs hZ
  let s : ℂ := (sigma : ℂ) + t * I
  let E : ℝ :=
    16 * ((A : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) / 3
  let S : ℂ := ∑ᶠ rho : ℂ,
    ((if dist rho ((2 : ℂ) + t * I) ≤ 6 then
        analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
      else 0 : ℕ) : ℂ) / (s - rho)
  have hsball : s ∈ closedBall ((2 : ℂ) + t * I) 3 := by
    rw [mem_closedBall, Complex.dist_eq]
    have hdiff :
        s - ((2 : ℂ) + t * I) = ((sigma - 2 : ℝ) : ℂ) := by
      simp [s]
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hsre : 1 ≤ s.re := by
    simpa [s] using hsigma1
  have hnorm :
      ‖logDeriv (DirichletCharacter.LFunction chi) s - S‖ ≤ E := by
    simpa [S, E] using
      hfixed q hq chi hchi t s hsball (by simpa [s] using hLs)
  have hselected :
      Z.sum (fun rho m =>
        (m : ℝ) * (((s - rho)⁻¹).re)) ≤ S.re := by
    simpa [S] using
      selected_radiusSix_subdivisor_sum_le_re_analyticOrder_finsum
        hq chi hchi t s hsre Z hZ
  have hnormSwap :
      ‖S - logDeriv (DirichletCharacter.LFunction chi) s‖ ≤ E := by
    rw [norm_sub_rev]
    exact hnorm
  have hreal :
      (S - logDeriv (DirichletCharacter.LFunction chi) s).re ≤
        ‖S - logDeriv (DirichletCharacter.LFunction chi) s‖ :=
    Complex.re_le_norm _
  have hresult :
      Z.sum (fun rho m =>
          (m : ℝ) * (((s - rho)⁻¹).re)) - E ≤
        (logDeriv (DirichletCharacter.LFunction chi) s).re := by
    rw [Complex.sub_re] at hreal
    linarith
  simpa [s, E] using hresult

end

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/PrimitiveLFunctionNontrivialSelection.lean` -/

section

/-!
# Primitive Dirichlet L-function nontrivial-zero selections

This file identifies primitive completed zeros with ordinary L-function zeros
in the open critical strip, then embeds every multiplicity-bounded local-height
selection into the ordinary radius-six subdivisor interface from SEM-480.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 111--114,
equation (11.3), Theorem 11.1, and Lemma 11.4, and printed pp. 119--120,
Lemma 12.2. Semantic review: `SEM-481`.
-/

namespace BoundedGaps.Maynard

open Complex Metric

noncomputable section

/-- A source-level nontrivial zero for a primitive Dirichlet L-function of
modulus greater than one. Mathlib's completed function differs from the
source normalization by a nowhere-zero power of the modulus. -/
def IsPrimitiveNontrivialLFunctionZero
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (rho : ℂ) : Prop :=
  1 < q ∧ chi.IsPrimitive ∧
    DirichletCharacter.completedLFunction chi rho = 0


/-- A primitive completed zero of modulus greater than one is an ordinary
L-function zero. The division-form Mathlib identity remains valid at Gamma
poles. -/
theorem IsPrimitiveNontrivialLFunctionZero.LFunction_eq_zero
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q} {rho : ℂ}
    (hrho : IsPrimitiveNontrivialLFunctionZero chi rho) :
    DirichletCharacter.LFunction chi rho = 0 := by
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi rho
    (.inr (Nat.ne_of_gt hrho.1)), hrho.2.2, zero_div]

/-- A primitive nontrivial L-function zero lies strictly to the right of the
line `Re(s)=0`. -/
theorem IsPrimitiveNontrivialLFunctionZero.re_pos
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q} {rho : ℂ}
    (hrho : IsPrimitiveNontrivialLFunctionZero chi rho) :
    0 < rho.re := by
  by_contra hrhoRe
  have hchi_ne : chi ≠ 1 :=
    character_ne_one_of_isPrimitive hrho.1 chi hrho.2.1
  have hq0 : (q : ℂ) ≠ 0 := by
    exact_mod_cast NeZero.ne q
  have hroot : DirichletCharacter.rootNumber chi ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_rootNumber_of_isPrimitive chi hrho.2.1]
    exact one_ne_zero
  have hfun := hrho.2.1.completedLFunction_one_sub (1 - rho)
  have hinvzero :
      DirichletCharacter.completedLFunction chi⁻¹ (1 - rho) = 0 := by
    rw [show 1 - (1 - rho) = rho by ring] at hfun
    rw [show 1 - rho - 1 / 2 = 1 / 2 - rho by ring] at hfun
    have hpow : (q : ℂ) ^ ((1 / 2 : ℂ) - rho) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (.inl hq0)
    exact (mul_eq_zero.mp (hfun.symm.trans hrho.2.2)).resolve_left
      (mul_ne_zero hpow hroot)
  have hLzero : DirichletCharacter.LFunction chi⁻¹ (1 - rho) = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi⁻¹
      (1 - rho) (.inr (Nat.ne_of_gt hrho.1)), hinvzero, zero_div]
  exact ((chi⁻¹).LFunction_ne_zero_of_one_le_re
    (.inl (inv_ne_one.mpr hchi_ne)) (by simp; linarith)) hLzero

/-- A primitive nontrivial L-function zero lies strictly to the left of the
line `Re(s)=1`. -/
theorem IsPrimitiveNontrivialLFunctionZero.re_lt_one
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q} {rho : ℂ}
    (hrho : IsPrimitiveNontrivialLFunctionZero chi rho) :
    rho.re < 1 :=
  LFunction_zero_re_lt_one_of_isPrimitive hrho.1 chi hrho.2.1
    hrho.LFunction_eq_zero


/-- A local-height primitive nontrivial zero lies in the closed radius-six
disk used by the fixed-disk logarithmic-derivative estimate. -/
theorem IsPrimitiveNontrivialLFunctionZero.dist_two_add_mul_I_le_six
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q} {rho : ℂ}
    (hrho : IsPrimitiveNontrivialLFunctionZero chi rho)
    {t : ℝ} (hheight : |rho.im - t| ≤ 1) :
    dist rho ((2 : ℂ) + t * I) ≤ 6 := by
  have hre0 : 0 ≤ rho.re := hrho.re_pos.le
  have hre1 : rho.re < 1 := hrho.re_lt_one
  have hxabs : |rho.re - 2| ≤ (2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hx : (rho.re - 2) ^ 2 ≤ (2 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by simpa using hxabs)
  have hy : (rho.im - t) ^ 2 ≤ (1 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by simpa using hheight)
  rw [Complex.dist_eq, Complex.norm_def, Real.sqrt_le_iff]
  constructor
  · norm_num
  · rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, sub_zero, Complex.sub_im, Complex.add_im]
    norm_num
    nlinarith

/-- Every multiplicity-bounded local selection of primitive nontrivial zeros
is a subdivisor of the ordinary closed radius-six divisor. -/
theorem selectedPrimitiveNontrivialZeros_le_radiusSix_analyticOrder
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (t : ℝ) (Z : ℂ →₀ ℕ)
    (hZ : ∀ rho ∈ Z.support,
      IsPrimitiveNontrivialLFunctionZero chi rho ∧
        |rho.im - t| ≤ 1)
    (hmult : ∀ rho : ℂ,
      Z rho ≤ analyticOrderNatAt
        (DirichletCharacter.LFunction chi) rho) :
    ∀ rho : ℂ,
      Z rho ≤
        if dist rho ((2 : ℂ) + t * I) ≤ 6 then
          analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
        else 0 := by
  intro rho
  by_cases hzero : Z rho = 0
  · simp [hzero]
  · have hmem : rho ∈ Z.support := Finsupp.mem_support_iff.mpr hzero
    have hdisk : dist rho ((2 : ℂ) + t * I) ≤ 6 :=
      (hZ rho hmem).1.dist_two_add_mul_I_le_six (hZ rho hmem).2
    rw [if_pos hdisk]
    exact hmult rho

/-- The primitive selected-nontrivial-zero lower bound with the exact SEM-480
residual and explicit ordinary multiplicity premise. -/
theorem exists_nat_selectedPrimitiveNontrivialZeros_sum_sub_le_re_logDeriv_LFunction :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ (t sigma : ℝ) (Z : ℂ →₀ ℕ),
            1 ≤ sigma → sigma ≤ 2 →
              DirichletCharacter.LFunction chi
                  ((sigma : ℂ) + t * I) ≠ 0 →
                (∀ rho ∈ Z.support,
                  IsPrimitiveNontrivialLFunctionZero chi rho ∧
                    |rho.im - t| ≤ 1) →
                  (∀ rho : ℂ,
                    Z rho ≤ analyticOrderNatAt
                      (DirichletCharacter.LFunction chi) rho) →
                    Z.sum (fun rho m =>
                        (m : ℝ) *
                          ((((sigma : ℂ) + t * I) - rho)⁻¹).re) -
                        16 * ((A : ℝ) *
                          Real.log ((q : ℝ) * (|t| + 2))) / 3 ≤
                      (logDeriv (DirichletCharacter.LFunction chi)
                        ((sigma : ℂ) + t * I)).re := by
  obtain ⟨A, hA, hselected⟩ :=
    exists_nat_selected_radiusSix_subdivisor_sum_sub_le_re_logDeriv_LFunction
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi t sigma Z hsigma1 hsigma2 hLs hZ hmult
  exact hselected q hq chi hchi t sigma Z hsigma1 hsigma2 hLs
    (selectedPrimitiveNontrivialZeros_le_radiusSix_analyticOrder
      chi t Z hZ hmult)

end

end BoundedGaps.Maynard

end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/ImprimitiveLFunctionTransport.lean` -/

section

/-!
# Imprimitive Dirichlet L-function transport

The L-function of a nonprincipal character is its inducing primitive
L-function times a finite Euler product. The extra factors are nonzero on
`Re(s) > 0`, preserve open-strip zero multiplicities, and cost at most
`log q` in logarithmic derivative on `Re(s) >= 1`.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 110,
equation (11.2), pp. 112--114, and p. 119, equation (12.1) and Lemma 12.2.
Semantic review: `SEM-483`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex Filter
open scoped Topology















end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/DirichletLFunctionConjugation.lean` -/

section

/-!
# Conjugation symmetry of Dirichlet L-functions

Complex conjugation exchanges the L-functions of a nonprincipal character
and its inverse. For a character whose square is principal, this gives the
conjugate-pair symmetry used in the real-character branch of the classical
zero-free region.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 110 and
119--121, especially the conjugate-zero step on p. 121. Independent
comparison: `ElkiesM229NearlyZeroFree2018`, p. 3. Semantic review: `SEM-485`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex Filter
open scoped ComplexConjugate Topology

private lemma conj_LSeries_conj_eq_inv
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ) :
    conj (LSeries (chi ·) (conj s)) = LSeries (chi⁻¹ ·) s := by
  rw [LSeries, conj_tsum, LSeries]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      map_div₀]
    have hcoeff : (starRingEnd ℂ) (chi n) = chi⁻¹ n := by
      change star (chi n) = chi⁻¹ n
      exact MulChar.star_apply' chi n
    rw [hcoeff]
    congr 1
    rw [← Complex.conj_cpow (n : ℂ) s (by
      rw [Complex.natCast_arg]
      exact ne_of_eq_of_ne rfl Real.pi_ne_zero.symm),
      Complex.conj_natCast]

/-- Analytic continuation preserves the conjugation identity between a
character and its inverse. -/
theorem LFunction_inv_conj
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction chi⁻¹ (conj s) =
      conj (DirichletCharacter.LFunction chi s) := by
  have hinvAnalytic : AnalyticOnNhd ℂ
      (DirichletCharacter.LFunction chi⁻¹) Set.univ :=
    DifferentiableOn.analyticOnNhd
      (DirichletCharacter.differentiable_LFunction
        (inv_ne_one.mpr hchi)).differentiableOn isOpen_univ
  have hconjAnalytic : AnalyticOnNhd ℂ
      (fun z : ℂ =>
        conj (DirichletCharacter.LFunction chi (conj z))) Set.univ :=
    DifferentiableOn.analyticOnNhd (fun z _ =>
      (differentiableAt_conj_conj_iff.mpr
        (DirichletCharacter.differentiable_LFunction hchi (conj z))).differentiableWithinAt)
      isOpen_univ
  have heq (z : ℂ) (hz : 1 < z.re) :
      DirichletCharacter.LFunction chi⁻¹ z =
        conj (DirichletCharacter.LFunction chi (conj z)) := by
    rw [DirichletCharacter.LFunction_eq_LSeries chi⁻¹ hz,
      DirichletCharacter.LFunction_eq_LSeries chi (by simpa using hz)]
    exact (conj_LSeries_conj_eq_inv chi z).symm
  have hfun : DirichletCharacter.LFunction chi⁻¹ =
      fun z : ℂ => conj (DirichletCharacter.LFunction chi (conj z)) :=
    hinvAnalytic.eq_of_eventuallyEq hconjAnalytic <|
      eventuallyEq_of_mem
        ((isOpen_lt continuous_const continuous_re).mem_nhds
          (by norm_num : (1 : ℝ) < ((2 : ℂ).re))) heq
  simpa using congrFun hfun (conj s)

/-- A square-principal nonprincipal character has a real-coefficient
L-function on the whole continued plane. -/
theorem LFunction_conj_of_sq_eq_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) (hsquare : chi ^ 2 = 1) (s : ℂ) :
    DirichletCharacter.LFunction chi (conj s) =
      conj (DirichletCharacter.LFunction chi s) := by
  have hinv : chi⁻¹ = chi :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsquare)
  simpa [hinv] using LFunction_inv_conj chi hchi s


end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/QuadraticLValueCutoff.lean` -/

section

/-!
# Explicit cutoff arithmetic for the quadratic L-value bound

This file chooses a natural smoothing cutoff at the source scale
`q * (log q)^4` and proves the numerical inequalities used in Theorem 12.8.
All numerals are project-derived.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 124--125.
Semantic review: `SEM-547`.
-/

noncomputable section

namespace BoundedGaps.Maynard

private noncomputable def quadraticLValueScale (q : ℕ) : ℝ :=
  (2 ^ 22 : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ 4

/-- The explicit natural smoothing cutoff used for the effective L-value
bound. -/
noncomputable def quadraticLValueCutoff (q : ℕ) : ℕ :=
  ⌈quadraticLValueScale q⌉₊

private lemma one_half_lt_log_natCast {q : ℕ} (hq : 1 < q) :
    (1 / 2 : ℝ) < Real.log (q : ℝ) := by
  have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogTwo : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  exact hlogTwo.trans_le (Real.log_le_log (by norm_num) hqTwo)

private lemma quadraticLValueScale_pos {q : ℕ} (hq : 1 < q) :
    0 < quadraticLValueScale q := by
  have hqPos : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hlogPos : 0 < Real.log (q : ℝ) := by
    linarith [one_half_lt_log_natCast hq]
  unfold quadraticLValueScale
  exact mul_pos (mul_pos (by norm_num) hqPos) (pow_pos hlogPos 4)

private lemma one_eighth_le_natCast_mul_log_pow_four {q : ℕ} (hq : 1 < q) :
    (1 / 8 : ℝ) ≤ (q : ℝ) * (Real.log (q : ℝ)) ^ 4 := by
  have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogPow : (1 / 2 : ℝ) ^ 4 ≤ (Real.log (q : ℝ)) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) (one_half_lt_log_natCast hq).le 4
  have hmul := mul_le_mul hqTwo hlogPow (by norm_num : (0 : ℝ) ≤ (1 / 2) ^ 4)
    (by positivity : (0 : ℝ) ≤ q)
  norm_num at hmul ⊢
  exact hmul

private lemma quadraticLValueScale_le_cutoff {q : ℕ} :
    quadraticLValueScale q ≤ (quadraticLValueCutoff q : ℝ) := by
  exact Nat.le_ceil _

private lemma cutoff_le_two_mul_quadraticLValueScale
    {q : ℕ} (hq : 1 < q) :
    (quadraticLValueCutoff q : ℝ) ≤ 2 * quadraticLValueScale q := by
  unfold quadraticLValueCutoff
  apply Nat.ceil_le_two_mul
  have hmul := one_eighth_le_natCast_mul_log_pow_four hq
  unfold quadraticLValueScale
  nlinarith

/-- The explicit cutoff is in the domain of the square-sum lower bound. -/
theorem four_le_quadraticLValueCutoff {q : ℕ} (hq : 1 < q) :
    4 ≤ quadraticLValueCutoff q := by
  have hscale := quadraticLValueScale_le_cutoff (q := q)
  have hmul := one_eighth_le_natCast_mul_log_pow_four hq
  have hfour : (4 : ℝ) ≤ quadraticLValueScale q := by
    unfold quadraticLValueScale
    nlinarith
  exact_mod_cast hfour.trans hscale

/-- A coarse logarithmic upper bound for the explicit cutoff. -/
theorem log_quadraticLValueCutoff_le {q : ℕ} (hq : 1 < q) :
    Real.log (quadraticLValueCutoff q : ℝ) ≤
      51 * Real.log (q : ℝ) := by
  have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqOne : (1 : ℝ) ≤ q := hqTwo.trans' (by norm_num)
  have hqPos : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num) hqTwo
  have hlogNonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqOne
  have hlogLeQ : Real.log (q : ℝ) ≤ (q : ℝ) :=
    (Real.log_le_sub_one_of_pos hqPos).trans (by linarith)
  have htwoPow : (2 : ℝ) ^ 23 ≤ (q : ℝ) ^ 23 :=
    pow_le_pow_left₀ (by norm_num) hqTwo 23
  have hlogPow : (Real.log (q : ℝ)) ^ 4 ≤ (q : ℝ) ^ 4 :=
    pow_le_pow_left₀ hlogNonneg hlogLeQ 4
  have hcutPow : (quadraticLValueCutoff q : ℝ) ≤ (q : ℝ) ^ 51 := by
    calc
      (quadraticLValueCutoff q : ℝ) ≤ 2 * quadraticLValueScale q :=
        cutoff_le_two_mul_quadraticLValueScale hq
      _ = (2 : ℝ) ^ 23 * q * (Real.log (q : ℝ)) ^ 4 := by
        unfold quadraticLValueScale
        norm_num
        ring
      _ ≤ (q : ℝ) ^ 23 * q * (q : ℝ) ^ 4 := by
        gcongr
      _ = (q : ℝ) ^ 28 := by ring
      _ ≤ (q : ℝ) ^ 51 := pow_le_pow_right₀ hqOne (by norm_num)
  have hcutPos : (0 : ℝ) < quadraticLValueCutoff q := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 4)
      (four_le_quadraticLValueCutoff hq))
  have hlog := Real.log_le_log hcutPos hcutPow
  rw [Real.log_pow] at hlog
  norm_num at hlog ⊢
  exact hlog

private lemma cutoffLowerScale_le_sqrt {q : ℕ} (hq : 1 < q) :
    2048 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ≤
      Real.sqrt (quadraticLValueCutoff q : ℝ) := by
  have hleftNonneg :
      0 ≤ 2048 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    positivity
  have hleftSq :
      (2048 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2) ^ 2 =
        quadraticLValueScale q := by
    have hsqrtQSq : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) :=
      Real.sq_sqrt (by positivity)
    unfold quadraticLValueScale
    rw [show
      (2048 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2) ^ 2 =
        4194304 * (Real.sqrt (q : ℝ)) ^ 2 *
          (Real.log (q : ℝ)) ^ 4 by ring]
    rw [hsqrtQSq]
    norm_num
  have hsqrtSq :
      (Real.sqrt (quadraticLValueCutoff q : ℝ)) ^ 2 =
        (quadraticLValueCutoff q : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hscale := quadraticLValueScale_le_cutoff (q := q)
  have hsqrtNonneg := Real.sqrt_nonneg (quadraticLValueCutoff q : ℝ)
  nlinarith

/-- The comparison error at the explicit cutoff consumes at most one eighth
of the square-sum main scale. -/
theorem quadraticLValueComparisonError_le {q : ℕ} (hq : 1 < q) :
    (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
        Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤
      (1 / 8 : ℝ) * Real.sqrt (quadraticLValueCutoff q : ℝ) := by
  have hlogPos : 0 < Real.log (q : ℝ) := by
    linarith [one_half_lt_log_natCast hq]
  have hcoef :
      6 + 4 * Real.log (quadraticLValueCutoff q : ℝ) ≤
        216 * Real.log (q : ℝ) := by
    have hlogCut := log_quadraticLValueCutoff_le hq
    have hlogHalf := one_half_lt_log_natCast hq
    linarith
  have hfactorNonneg :
      0 ≤ Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) hlogPos.le
  have herror :
      (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
          Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤
        216 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    calc
      (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
          Real.sqrt (q : ℝ) * Real.log (q : ℝ) =
        (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
          (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) := by ring
      _ ≤ (216 * Real.log (q : ℝ)) *
          (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef hfactorNonneg
      _ = 216 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by ring
  have hlower := cutoffLowerScale_le_sqrt hq
  calc
    (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
        Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤
      216 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := herror
    _ ≤ 256 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
      gcongr
      norm_num
    _ = (1 / 8 : ℝ) *
        (2048 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2) := by ring
    _ ≤ (1 / 8 : ℝ) * Real.sqrt (quadraticLValueCutoff q : ℝ) := by
      gcongr

/-- The natural ceiling enlarges the source scale by less than the displayed
factor two, so its square root has this explicit upper bound. -/
theorem sqrt_quadraticLValueCutoff_le {q : ℕ} (hq : 1 < q) :
    Real.sqrt (quadraticLValueCutoff q : ℝ) ≤
      4096 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
  have hrightNonneg :
      0 ≤ 4096 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    positivity
  have hrightSq :
      (4096 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2) ^ 2 =
        4 * quadraticLValueScale q := by
    have hsqrtQSq : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) :=
      Real.sq_sqrt (by positivity)
    unfold quadraticLValueScale
    rw [show
      (4096 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2) ^ 2 =
        16777216 * (Real.sqrt (q : ℝ)) ^ 2 *
          (Real.log (q : ℝ)) ^ 4 by ring]
    rw [hsqrtQSq]
    norm_num
    ring
  have hsqrtSq :
      (Real.sqrt (quadraticLValueCutoff q : ℝ)) ^ 2 =
        (quadraticLValueCutoff q : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hcut := cutoff_le_two_mul_quadraticLValueScale hq
  have hscalePos := quadraticLValueScale_pos hq
  have hsqrtNonneg := Real.sqrt_nonneg (quadraticLValueCutoff q : ℝ)
  nlinarith

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/QuadraticZetaEulerMaclaurin.lean` -/

section

/-!
# The finite Euler--Maclaurin cutoff

This file proves the exact fractional-part identity used in the smoothed
quadratic-character calculation.  The source is Koukoulopoulos, preliminary
version, Theorem 1.10 (p. 15), specialized in the proof of Theorem 12.8
(pp. 124--125).  The real cutoff is kept explicit; no totalized division at
zero is used.

Semantic review: `SEM-545`.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BoundedGaps.Maynard

private lemma integrableOn_fract_Icc (a b : ℝ) :
    IntegrableOn (Int.fract : ℝ → ℝ) (Icc a b) := by
  apply Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
  · exact measurable_fract.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le


private lemma integral_fract_unit :
    (∫ t : ℝ in Set.Ioc 0 1, Int.fract t) = 1 / 2 := by
  calc
    (∫ t : ℝ in Set.Ioc 0 1, Int.fract t) =
        ∫ t : ℝ in Set.Ioc 0 1, t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (volume.ae_ne (1 : ℝ))] with t ht htne
      exact Int.fract_eq_self.mpr ⟨ht.1.le, lt_of_le_of_ne ht.2 htne⟩
    _ = 1 / 2 := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      norm_num

private lemma integral_fract_formula {u : ℝ} (hu : 0 < u) :
    (∫ t : ℝ in Set.Ioc 0 u, Int.fract t) =
      (⌊u⌋₊ : ℝ) / 2 + (u - (⌊u⌋₊ : ℝ)) ^ 2 / 2 := by
  let n : ℕ := ⌊u⌋₊
  have hbase : IntervalIntegrable (Int.fract : ℝ → ℝ) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
    exact integrableOn_fract_Icc 0 1
  have hall (a b : ℝ) :
      IntervalIntegrable (Int.fract : ℝ → ℝ) volume a b :=
    (Int.fract_periodic ℝ).intervalIntegrable₀ one_ne_zero hbase a b
  have hbaseValue : (∫ t : ℝ in 0..1, Int.fract t) = 1 / 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact integral_fract_unit
  have hnValue : (∫ t : ℝ in 0..(n : ℝ), Int.fract t) = (n : ℝ) / 2 := by
    have hperiod := (Int.fract_periodic ℝ).intervalIntegral_add_zsmul_eq
      (n : ℤ) 0 hall
    simpa [hbaseValue, nsmul_eq_mul, div_eq_mul_inv] using hperiod
  have hn_le : (n : ℝ) ≤ u := by
    dsimp [n]
    exact Nat.floor_le hu.le
  have hu_lt : u < (n : ℝ) + 1 := by
    dsimp [n]
    exact Nat.lt_floor_add_one u
  have hrem : (∫ t : ℝ in (n : ℝ)..u, Int.fract t) =
      (u - (n : ℝ)) ^ 2 / 2 := by
    calc
      (∫ t : ℝ in (n : ℝ)..u, Int.fract t) =
          ∫ t : ℝ in (n : ℝ)..u, (t - (n : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Set.uIcc (n : ℝ) u := ht
        rw [Set.uIcc_of_le hn_le] at ht'
        rw [← Int.fract_sub_natCast t n]
        exact Int.fract_eq_self.mpr ⟨sub_nonneg.mpr ht'.1,
          (sub_lt_iff_lt_add).mpr
            (ht'.2.trans_lt (by simpa [add_comm] using hu_lt))⟩
      _ = (u - (n : ℝ)) ^ 2 / 2 := by
        rw [intervalIntegral.integral_sub]
        · rw [integral_id, intervalIntegral.integral_const]
          simp only [smul_eq_mul]
          ring
        · exact continuous_id.intervalIntegrable (μ := volume) _ _
        · exact continuous_const.intervalIntegrable (μ := volume) _ _
  rw [← intervalIntegral.integral_of_le hu.le]
  change (∫ t : ℝ in 0..u, Int.fract t) =
    (n : ℝ) / 2 + (u - (n : ℝ)) ^ 2 / 2
  rw [← intervalIntegral.integral_add_adjacent_intervals (hall 0 n) (hall n u),
    hnValue, hrem]


/-- The exact linear Euler--Maclaurin formula for a positive real cutoff. -/
theorem sum_linear_cutoff_eq_half_sub_fractIntegral
    {u : ℝ} (hu : 0 < u) :
    (∑ b ∈ Finset.Icc 1 ⌊u⌋₊,
      (1 - (b : ℝ) / u)) =
      u / 2 - (1 / u) *
        (∫ t : ℝ in Set.Ioc 0 u, Int.fract t) := by
  rw [integral_fract_formula hu]
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  have hsum_id : ∀ n : ℕ,
      (∑ b ∈ Finset.Icc 1 n, (b : ℝ)) =
        (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih]
        push_cast
        ring
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, hsum_id]
  simp only [Nat.card_Icc]
  push_cast
  field_simp [hu.ne']
  ring

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/QuadraticZetaConvolutionSquare.lean` -/

section

/-!
# Quadratic zeta-convolution coefficients at squares

For a square-principal Dirichlet character, every even prime-power
coefficient of `1 * chi` is at least one. Multiplicativity then gives the same
lower bound at every positive square.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 124, proof of
Theorem 12.8. Semantic review: `SEM-539`.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedGaps.Maynard

open ArithmeticFunction

/-- Even prime-power coefficients of `1 * chi` are at least one for a
square-principal character. -/
theorem one_le_zetaMul_prime_pow_two_mul
    {q p k : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hsquare : chi ^ 2 = 1) (hp : p.Prime) :
    (1 : ℂ) ≤ chi.zetaMul (p ^ (2 * k)) := by
  simp only [DirichletCharacter.zetaMul, toArithmeticFunction,
    coe_zeta_mul_apply, coe_mk, Nat.sum_divisors_prime_pow hp,
    pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
    Nat.cast_pow, map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsquare p with h | h | h
  · simp [h]
  · simp [h]
    positivity
  · simp [h, neg_one_geom_sum]

/-- The coefficient of `1 * chi` at every positive square is at least one. -/
theorem one_le_zetaMul_sq
    {q n : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hsquare : chi ^ 2 = 1) (hn : n ≠ 0) :
    (1 : ℂ) ≤ chi.zetaMul (n ^ 2) := by
  rw [chi.isMultiplicative_zetaMul.multiplicative_factorization _
    (pow_ne_zero 2 hn)]
  refine Finset.one_le_prod fun p hp => ?_
  have hp' : p.Prime := by
    exact Nat.prime_of_mem_primeFactors (by simpa using hp)
  simpa [Nat.factorization_pow] using
    one_le_zetaMul_prime_pow_two_mul (chi := chi) hsquare hp'

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/QuadraticZetaSmoothedSquareLower.lean` -/

section

/-!
# A smoothed quadratic convolution lower bound

For a square-principal Dirichlet character, the linearly smoothed finite sum
of the coefficients of `1 * chi` is bounded below by its bare square weights.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 124--125,
proof of Theorem 12.8. Semantic review: `SEM-540`.
-/

noncomputable section

open scoped BigOperators ComplexOrder

namespace BoundedGaps.Maynard

/-- The linearly smoothed finite sum of the coefficients of `1 * chi`. -/
noncomputable def quadraticZetaLinearSmoothedSum
    {q : ℕ} (chi : DirichletCharacter ℂ q) (X : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X,
    chi.zetaMul n * ((1 - (n : ℝ) / (X : ℝ) : ℝ) : ℂ)

/-- Dropping nonsquares from the smoothed quadratic convolution gives a lower
bound by the bare square weights. -/
theorem sum_square_linearCutoff_le_quadraticZetaLinearSmoothedSum
    {q X : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hsquare : chi ^ 2 = 1) (hX : 0 < X) :
    (∑ m ∈ Finset.Icc 1 X.sqrt,
        ((1 - (m : ℝ) ^ 2 / (X : ℝ) : ℝ) : ℂ)) ≤
      quadraticZetaLinearSmoothedSum chi X := by
  classical
  let squares := Finset.Icc 1 X.sqrt
  let indices := Finset.Icc 1 X
  let square : ℕ → ℕ := fun m ↦ m ^ 2
  let weight : ℕ → ℂ := fun n ↦
    ((1 - (n : ℝ) / (X : ℝ) : ℝ) : ℂ)
  let summand : ℕ → ℂ := fun n ↦ chi.zetaMul n * weight n
  have hXreal : (0 : ℝ) < X := by
    exact_mod_cast hX
  have hweight : ∀ n ∈ indices, (0 : ℂ) ≤ weight n := by
    intro n hn
    have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
    dsimp only [weight]
    rw [Complex.nonneg_iff, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨sub_nonneg.mpr ((div_le_one hXreal).2 (by exact_mod_cast hnX)), rfl⟩
  have hsquare_subset : squares.image square ⊆ indices := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
    have hm_bounds := Finset.mem_Icc.mp hm
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.one_le_pow 2 m (by omega)
    · exact Nat.le_sqrt'.mp hm_bounds.2
  have hsquare_injective : Set.InjOn square squares :=
    (Nat.pow_left_injective (by decide : 2 ≠ 0)).injOn
  have hselected :
      (∑ m ∈ squares, weight (square m)) ≤
        ∑ m ∈ squares, summand (square m) := by
    apply Finset.sum_le_sum
    intro m hm
    have hm_ne : m ≠ 0 := by
      have hm_one : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      omega
    have hm_image : square m ∈ squares.image square :=
      Finset.mem_image.mpr ⟨m, hm, rfl⟩
    simpa only [summand, square, one_mul] using
      mul_le_mul_of_nonneg_right
        (one_le_zetaMul_sq (chi := chi) hsquare hm_ne)
        (hweight _ (hsquare_subset hm_image))
  have hmain :
      (∑ m ∈ squares, weight (square m)) ≤ ∑ n ∈ indices, summand n := by
    calc
      (∑ m ∈ squares, weight (square m)) ≤
          ∑ m ∈ squares, summand (square m) := hselected
      _ = ∑ n ∈ squares.image square, summand n :=
        (Finset.sum_image hsquare_injective).symm
      _ ≤ ∑ n ∈ indices, summand n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsquare_subset fun n hn _ ↦
          mul_nonneg (chi.zetaMul_nonneg hsquare n) (hweight n hn)
  simpa [squares, indices, square, weight, summand,
    quadraticZetaLinearSmoothedSum, Nat.cast_pow] using hmain

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/QuadraticZetaDirectEulerRemainder.lean` -/

section

/-!
# Direct Euler remainder for the quadratic zeta cutoff

The finite divisor reindex and the source-facing Euler--Maclaurin identity are
proved separately from the later swapped-integral estimate.  This keeps the
positive-factor endpoint and every complex/real coercion visible.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, Theorem 12.8,
pp. 124--125.  Semantic review: `SEM-545`.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BoundedGaps.Maynard

private theorem mem_positiveFactorPairs_quadratic
    {X : ℕ} (p : ℕ × ℕ) :
    p ∈ positiveFactorPairs X ↔
      p.1 ∈ Finset.Icc 1 X ∧ p.2 ∈ Finset.Icc 1 (X / p.1) := by
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hprod⟩
    rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
    rw [Finset.mem_Ioc] at hp₁ hp₂
    exact ⟨Finset.mem_Icc.mpr ⟨hp₁.1, hp₁.2⟩,
      Finset.mem_Icc.mpr ⟨hp₂.1,
        (Nat.le_div_iff_mul_le hp₁.1).mpr (by
          simpa only [Nat.mul_comm] using hprod)⟩⟩
  · rintro ⟨hm, hk⟩
    rw [Finset.mem_Icc] at hm hk
    have hprod : p.1 * p.2 ≤ X := by
      simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hm.1).mp hk.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Ioc.mpr hm,
          Finset.mem_Ioc.mpr
            ⟨hk.1, hk.2.trans (Nat.div_le_self X p.1)⟩⟩,
        hprod⟩

private theorem sum_divisors_cutoff_eq_nested_quadratic
    {X : ℕ} (f : ℕ → ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, f n d) =
      ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a), f (a * b) a := by
  calc
    (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, f n d) =
        ∑ n ∈ Finset.Ioc 0 X, ∑ d ∈ n.divisors, f n d := by
      rw [show Finset.Icc 1 X = Finset.Ioc 0 X by
        simpa using Finset.Icc_succ_left_eq_Ioc 0 X]
    _ = ∑ p ∈ positiveFactorPairs X, f (p.1 * p.2) p.1 :=
      sum_divisors_up_to_eq_sum_positiveFactorPairs f
    _ = ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a),
          f (a * b) a := by
      exact Finset.sum_finset_product' (f := fun a b ↦ f (a * b) a)
        (positiveFactorPairs X) (Finset.Icc 1 X)
        (fun a ↦ Finset.Icc 1 (X / a))
        mem_positiveFactorPairs_quadratic

private theorem zetaMul_cutoff_eq_nested_quadratic
    {q X : ℕ} (chi : DirichletCharacter ℂ q) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 X, chi.zetaMul n * w n) =
      ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a),
        chi (a : ZMod q) * w (a * b) := by
  have hz : (∑ n ∈ Finset.Icc 1 X, chi.zetaMul n * w n) =
      ∑ n ∈ Finset.Icc 1 X,
        (∑ d ∈ n.divisors, chi (d : ZMod q)) * w n := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    rw [DirichletCharacter.zetaMul,
      ArithmeticFunction.coe_zeta_mul_apply]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [toArithmeticFunction, ArithmeticFunction.coe_mk,
      if_neg (Nat.pos_of_mem_divisors hd).ne']
  rw [hz]
  simp_rw [Finset.sum_mul]
  rw [sum_divisors_cutoff_eq_nested_quadratic]

/-- The direct fractional-part remainder before the finite integral swap. -/
noncomputable def quadraticZetaDirectEulerRemainder
    {q : ℕ} (chi : DirichletCharacter ℂ q) (X : ℕ) : ℂ :=
  (1 / (X : ℂ)) *
    ∑ a ∈ Finset.Icc 1 X,
      (a : ℂ) * chi (a : ZMod q) *
        (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)),
          ((Int.fract t : ℝ) : ℂ))

/-- The smoothed quadratic convolution equals its direct Euler expansion. -/
theorem quadraticZetaLinearSmoothedSum_eq_directEulerRemainder
    {q X : ℕ} (chi : DirichletCharacter ℂ q) (hX : 0 < X) :
    quadraticZetaLinearSmoothedSum chi X =
      ((X : ℂ) / 2) *
        (∑ a ∈ Finset.Icc 1 X,
          chi (a : ZMod q) / (a : ℂ)) -
      quadraticZetaDirectEulerRemainder chi X := by
  let weight : ℕ → ℂ := fun n ↦
    ((1 - (n : ℝ) / (X : ℝ) : ℝ) : ℂ)
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hinner : ∀ a ∈ Finset.Icc 1 X,
      (∑ b ∈ Finset.Icc 1 (X / a), weight (a * b)) =
        (X : ℂ) / (2 * (a : ℂ)) -
          ((a : ℂ) / (X : ℂ)) *
            (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)),
              ((Int.fract t : ℝ) : ℂ)) := by
    intro a ha
    have haPos : 0 < a := (Finset.mem_Icc.mp ha).1
    have haReal : (0 : ℝ) < a := by exact_mod_cast haPos
    let u : ℝ := (X : ℝ) / (a : ℝ)
    have hu : 0 < u := div_pos hXreal haReal
    have heuler := sum_linear_cutoff_eq_half_sub_fractIntegral hu
    have hfloor : ⌊u⌋₊ = X / a := by
      simpa [u] using (Nat.floor_div_eq_div (K := ℝ) X a)
    rw [hfloor] at heuler
    have hweight : ∀ b : ℕ,
        (1 - (a : ℝ) * (b : ℝ) / (X : ℝ)) =
          1 - (b : ℝ) / u := by
      intro b
      dsimp [u]
      field_simp [hXreal.ne', haReal.ne']
    have hreal :
        (∑ b ∈ Finset.Icc 1 (X / a),
          (1 - (a : ℝ) * (b : ℝ) / (X : ℝ))) =
          u / 2 - (1 / u) *
            (∫ t : ℝ in Set.Ioc 0 u, Int.fract t) := by
      rw [show (∑ b ∈ Finset.Icc 1 (X / a),
          (1 - (a : ℝ) * (b : ℝ) / (X : ℝ))) =
          ∑ b ∈ Finset.Icc 1 (X / a),
            (1 - (b : ℝ) / u) by
        apply Finset.sum_congr rfl
        intro b hb
        exact hweight b]
      exact heuler
    calc
      (∑ b ∈ Finset.Icc 1 (X / a), weight (a * b)) =
          (((∑ b ∈ Finset.Icc 1 (X / a),
            (1 - (a : ℝ) * (b : ℝ) / (X : ℝ))) : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro b hb
        simp [weight, Nat.cast_mul]
      _ = _ := by
        rw [hreal, Complex.ofReal_sub, Complex.ofReal_mul]
        rw [show ((∫ t : ℝ in Set.Ioc 0 u, Int.fract t : ℝ) : ℂ) =
            ∫ t : ℝ in Set.Ioc 0 u, ((Int.fract t : ℝ) : ℂ) by
          exact integral_ofReal.symm]
        dsimp [u]
        push_cast
        field_simp [hXreal.ne', haReal.ne']
  rw [quadraticZetaLinearSmoothedSum]
  change (∑ n ∈ Finset.Icc 1 X, chi.zetaMul n * weight n) = _
  rw [zetaMul_cutoff_eq_nested_quadratic]
  calc
    (∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a),
        chi (a : ZMod q) * weight (a * b)) =
        ∑ a ∈ Finset.Icc 1 X,
          chi (a : ZMod q) *
            ((X : ℂ) / (2 * (a : ℂ)) -
              ((a : ℂ) / (X : ℂ)) *
                (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)),
                  ((Int.fract t : ℝ) : ℂ))) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.mul_sum, hinner a ha]
    _ = ∑ a ∈ Finset.Icc 1 X,
          (((X : ℂ) / 2) *
              (chi (a : ZMod q) / (a : ℂ)) -
            (1 / (X : ℂ)) *
              ((a : ℂ) * chi (a : ZMod q) *
                (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)),
                  ((Int.fract t : ℝ) : ℂ)))) := by
      apply Finset.sum_congr rfl
      intro a ha
      have haNe : (a : ℂ) ≠ 0 := by
        have haPos : 0 < a := lt_of_lt_of_le Nat.zero_lt_one
          (Finset.mem_Icc.mp ha).1
        exact_mod_cast haPos.ne'
      have hXne : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
      field_simp [haNe, hXne]
    _ = ((X : ℂ) / 2) *
          (∑ a ∈ Finset.Icc 1 X,
            chi (a : ZMod q) / (a : ℂ)) -
        quadraticZetaDirectEulerRemainder chi X := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      unfold quadraticZetaDirectEulerRemainder
      rw [Finset.mul_sum]

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/QuadraticZetaSwappedEulerRemainder.lean` -/

section

/-!
# Swapping the fractional-part Euler remainder

The direct finite sum of integrals from SEM-545 is rewritten as one integral
over `(0,X]`.  The source cutoff is `min X floor(X/t)` for positive `t`; the
representative at zero is arbitrary because the integration set is `Ioc 0 X`.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 124--125.
Semantic review: `SEM-546`.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BoundedGaps.Maynard

/-- The source cutoff, with an arbitrary representative at the omitted zero. -/
noncomputable def quadraticEulerCutoff (X : ℕ) (t : ℝ) : ℕ :=
  if t = 0 then X else min X ⌊(X : ℝ) / t⌋₊

/-- The single-integral form of the direct Euler remainder. -/
noncomputable def quadraticZetaSwappedEulerRemainder
    {q : ℕ} (chi : DirichletCharacter ℂ q) (X : ℕ) : ℂ :=
  (1 / (X : ℂ)) *
    ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
      ((Int.fract t : ℝ) : ℂ) *
        ∑ a ∈ Finset.Icc 1 (quadraticEulerCutoff X t),
          (a : ℂ) * chi (a : ZMod q)

private lemma mem_quadraticEulerCutoff_iff
    {X : ℕ} {t : ℝ} (ht : 0 < t) (a : ℕ) :
    a ∈ Finset.Icc 1 (quadraticEulerCutoff X t) ↔
      a ∈ Finset.Icc 1 X ∧ (a : ℝ) ≤ (X : ℝ) / t := by
  rw [quadraticEulerCutoff, if_neg ht.ne']
  rw [Finset.mem_Icc, Finset.mem_Icc, Nat.le_min]
  constructor
  · rintro ⟨ha1, haX, haf⟩
    refine ⟨⟨ha1, haX⟩, ?_⟩
    rw [Nat.le_floor_iff (div_nonneg (by positivity) ht.le)] at haf
    exact haf
  · rintro ⟨⟨ha1, haX⟩, har⟩
    refine ⟨ha1, haX, ?_⟩
    exact (Nat.le_floor_iff (div_nonneg (by positivity) ht.le)).mpr har

private lemma ratio_swap_iff
    {X a : ℕ} {t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    t ≤ (X : ℝ) / (a : ℝ) ↔ (a : ℝ) ≤ (X : ℝ) / t := by
  have haReal : (0 : ℝ) < a := by exact_mod_cast ha
  rw [le_div_iff₀ haReal, le_div_iff₀ ht]
  ring_nf

private lemma interval_inter_quadratic_cutoff
    {X a : ℕ} (hX : 0 < X) (ha : a ∈ Finset.Icc 1 X) :
    Set.Ioc 0 (X : ℝ) ∩ Set.Iic ((X : ℝ) / (a : ℝ)) =
      Set.Ioc 0 ((X : ℝ) / (a : ℝ)) := by
  have haPos : 0 < a := (Finset.mem_Icc.mp ha).1
  have haReal : (0 : ℝ) < a := by exact_mod_cast haPos
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hle : (X : ℝ) / (a : ℝ) ≤ (X : ℝ) := by
    rw [div_le_iff₀ haReal]
    nlinarith [show (1 : ℝ) ≤ a by exact_mod_cast (Finset.mem_Icc.mp ha).1]
  ext t
  constructor
  · rintro ⟨⟨ht0, htX⟩, hta⟩
    exact ⟨ht0, hta⟩
  · rintro ⟨ht0, hta⟩
    exact ⟨⟨ht0, hta.trans hle⟩, hta⟩

private lemma sum_integral_indicator
    {X : ℕ} (hX : 0 < X) (f : ℝ → ℂ)
    (hf : IntegrableOn f (Set.Ioc 0 (X : ℝ))) (g : ℕ → ℂ) :
    (∑ a ∈ Finset.Icc 1 X, g a *
      (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)), f t)) =
      ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
        ∑ a ∈ Finset.Icc 1 X,
          g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t := by
  have hmeas : ∀ a ∈ Finset.Icc 1 X,
      MeasurableSet (Set.Iic ((X : ℝ) / (a : ℝ))) := by
    intro a ha
    exact measurableSet_Iic
  have hIntIndicator : ∀ a ∈ Finset.Icc 1 X,
      IntegrableOn (Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f)
        (Set.Ioc 0 (X : ℝ)) := by
    intro a ha
    exact hf.indicator (hmeas a ha)
  calc
    (∑ a ∈ Finset.Icc 1 X, g a *
        (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)), f t)) =
        ∑ a ∈ Finset.Icc 1 X, g a *
          (∫ t : ℝ in Set.Ioc 0 (X : ℝ),
            Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [setIntegral_indicator (hmeas a ha)]
      rw [interval_inter_quadratic_cutoff hX ha]
    _ = ∑ a ∈ Finset.Icc 1 X,
          ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
            g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [integral_const_mul]
    _ = ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
          ∑ a ∈ Finset.Icc 1 X,
            g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t := by
      rw [integral_finsetSum]
      intro a ha
      exact (hIntIndicator a ha).const_mul _

private lemma indicator_sum_eq_cutoff
    {X : ℕ} {t : ℝ} (ht : 0 < t) (f : ℝ → ℂ) (g : ℕ → ℂ) :
    (∑ a ∈ Finset.Icc 1 X,
      g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t) =
      f t * ∑ a ∈ Finset.Icc 1 (quadraticEulerCutoff X t), g a := by
  calc
    (∑ a ∈ Finset.Icc 1 X,
        g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t) =
        f t * ∑ a ∈ (Finset.Icc 1 X).filter
          (fun a : ℕ ↦ t ≤ (X : ℝ) / (a : ℝ)), g a := by
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hmem : t ∈ Set.Iic ((X : ℝ) / (a : ℝ))
      · simp only [Set.mem_Iic] at hmem
        simp [Set.indicator, hmem, mul_comm]
      · simp only [Set.mem_Iic] at hmem
        simp [Set.indicator, hmem]
    _ = f t * ∑ a ∈ Finset.Icc 1 (quadraticEulerCutoff X t), g a := by
      apply congrArg (fun s : Finset ℕ => f t * ∑ a ∈ s, g a) ?_
      ext a
      rw [Finset.mem_filter, mem_quadraticEulerCutoff_iff ht]
      apply and_congr_right
      intro ha
      exact ratio_swap_iff (lt_of_lt_of_le Nat.zero_lt_one
        (Finset.mem_Icc.mp ha).1) ht

private lemma integrableOn_fractComplex {X : ℕ} :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ))
      (Set.Ioc 0 (X : ℝ)) := by
  apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
  · exact (Complex.continuous_ofReal.measurable.comp measurable_fract).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le

/-- The direct and swapped fractional-part remainders are equal. -/
theorem quadraticZetaDirectEulerRemainder_eq_swapped
    {q X : ℕ} (chi : DirichletCharacter ℂ q) (hX : 0 < X) :
    quadraticZetaDirectEulerRemainder chi X =
      quadraticZetaSwappedEulerRemainder chi X := by
  let f : ℝ → ℂ := fun t => ((Int.fract t : ℝ) : ℂ)
  let g : ℕ → ℂ := fun a => (a : ℂ) * chi (a : ZMod q)
  have hswap := sum_integral_indicator hX f
    (integrableOn_fractComplex (X := X)) g
  have hcut :
      ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
          ∑ a ∈ Finset.Icc 1 X,
            g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t =
        ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
          f t * ∑ a ∈ Finset.Icc 1 (quadraticEulerCutoff X t), g a := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [indicator_sum_eq_cutoff ht.1]
  unfold quadraticZetaDirectEulerRemainder quadraticZetaSwappedEulerRemainder
  dsimp [f, g] at hswap hcut ⊢
  rw [hcut] at hswap
  simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg
    (fun z : ℂ => (1 / (X : ℂ)) * z) hswap

private lemma quadraticEulerCutoff_le (X : ℕ) (t : ℝ) :
    quadraticEulerCutoff X t ≤ X := by
  by_cases ht : t = 0
  · simp [quadraticEulerCutoff, ht]
  · simp [quadraticEulerCutoff, ht]

private lemma cast_quadraticEulerCutoff_le_div
    {X : ℕ} {t : ℝ} (ht : 0 < t) :
    (quadraticEulerCutoff X t : ℝ) ≤ (X : ℝ) / t := by
  rw [quadraticEulerCutoff, if_neg ht.ne']
  have hfloor : (min X ⌊(X : ℝ) / t⌋₊ : ℕ) ≤ ⌊(X : ℝ) / t⌋₊ :=
    min_le_right _ _
  have hfloor_le :
      (⌊(X : ℝ) / t⌋₊ : ℝ) ≤ (X : ℝ) / t :=
    Nat.floor_le (div_nonneg (by positivity) ht.le)
  have hcast : ((min X ⌊(X : ℝ) / t⌋₊ : ℕ) : ℝ) ≤
      (⌊(X : ℝ) / t⌋₊ : ℝ) := by exact_mod_cast hfloor
  exact hcast.trans hfloor_le

private lemma measurable_quadraticEulerCutoff (X : ℕ) :
    Measurable (quadraticEulerCutoff X) := by
  unfold quadraticEulerCutoff
  have hzero : MeasurableSet ({(0 : ℝ)} : Set ℝ) := measurableSet_singleton (0 : ℝ)
  apply Measurable.ite (by simpa only [Set.setOf_eq_eq_singleton] using hzero)
    measurable_const
  have hdiv : Measurable (fun t : ℝ ↦ (X : ℝ) / t) :=
    measurable_const.div measurable_id
  exact (measurable_of_countable (fun y : ℕ ↦ min X y)).comp hdiv.nat_floor

private lemma integrableOn_quadraticSwappedIntegrand
    {q X : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    IntegrableOn
      (fun t : ℝ ↦ ((Int.fract t : ℝ) : ℂ) *
        ∑ a ∈ Finset.Icc 1 (quadraticEulerCutoff X t),
          (a : ℂ) * chi (a : ZMod q))
      (Set.Ioc 0 (X : ℝ)) := by
  let charPrefix : ℕ → ℂ := fun y ↦
    ∑ a ∈ Finset.Icc 1 y, (a : ℂ) * chi (a : ZMod q)
  let F : ℝ → ℂ := fun t ↦ ((Int.fract t : ℝ) : ℂ) *
    charPrefix (quadraticEulerCutoff X t)
  have hprefixMeas : Measurable (fun t ↦
      charPrefix (quadraticEulerCutoff X t)) :=
    (measurable_of_countable charPrefix).comp
      (measurable_quadraticEulerCutoff X)
  have hFMeas : Measurable F :=
    (Complex.continuous_ofReal.measurable.comp measurable_fract).mul hprefixMeas
  apply IntegrableOn.of_bound measure_Ioc_lt_top hFMeas.aestronglyMeasurable
    (4 * (X : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  change ‖((Int.fract t : ℝ) : ℂ) *
      charPrefix (quadraticEulerCutoff X t)‖ ≤ _
  rw [norm_mul]
  have hfract : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le
  have hprefix := norm_dirichletCharacterWeightedPrefixSum_le
    hq chi hchi (quadraticEulerCutoff X t)
  change ‖charPrefix (quadraticEulerCutoff X t)‖ ≤ _ at hprefix
  calc
    ‖((Int.fract t : ℝ) : ℂ)‖ *
        ‖charPrefix (quadraticEulerCutoff X t)‖ ≤
        1 * (4 * (quadraticEulerCutoff X t : ℝ) *
          Real.sqrt (q : ℝ) * Real.log (q : ℝ)) :=
      mul_le_mul hfract hprefix (norm_nonneg _) zero_le_one
    _ ≤ 4 * (X : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      have hlog : 0 ≤ Real.log (q : ℝ) :=
        (Real.log_pos (by exact_mod_cast hq)).le
      have hscale : 0 ≤ Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
        mul_nonneg (Real.sqrt_nonneg _) hlog
      have hcut : (quadraticEulerCutoff X t : ℝ) ≤ (X : ℝ) := by
        exact_mod_cast quadraticEulerCutoff_le X t
      have hfour : (0 : ℝ) ≤ 4 := by norm_num
      have h4cut : 4 * (quadraticEulerCutoff X t : ℝ) ≤
          4 * (X : ℝ) := mul_le_mul_of_nonneg_left hcut hfour
      calc
        1 * (4 * (quadraticEulerCutoff X t : ℝ) * Real.sqrt (q : ℝ) *
            Real.log (q : ℝ)) =
            (4 * (quadraticEulerCutoff X t : ℝ)) *
              (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) := by
              ring
        _ ≤ (4 * (X : ℝ)) * (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) :=
          mul_le_mul_of_nonneg_right h4cut hscale
        _ = 4 * (X : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
          ring

/-- The swapped Euler remainder has the explicit source-scale logarithmic
bound. -/
theorem norm_quadraticZetaSwappedEulerRemainder_le
    {q X : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (hX : 0 < X) :
    ‖quadraticZetaSwappedEulerRemainder chi X‖ ≤
      4 * (1 + Real.log (X : ℝ)) * Real.sqrt (q : ℝ) *
        Real.log (q : ℝ) := by
  let charPrefix : ℕ → ℂ := fun y ↦
    ∑ a ∈ Finset.Icc 1 y, (a : ℂ) * chi (a : ZMod q)
  let F : ℝ → ℂ := fun t ↦ ((Int.fract t : ℝ) : ℂ) *
    charPrefix (quadraticEulerCutoff X t)
  let S : ℝ := Real.sqrt (q : ℝ) * Real.log (q : ℝ)
  have hXone : 1 ≤ X := hX
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hOneX : (1 : ℝ) ≤ X := by exact_mod_cast hXone
  have hS : 0 ≤ S := mul_nonneg (Real.sqrt_nonneg _)
    (Real.log_pos (by exact_mod_cast hq)).le
  have hFint : IntegrableOn F (Set.Ioc 0 (X : ℝ)) := by
    simpa [F, charPrefix] using
      integrableOn_quadraticSwappedIntegrand hq chi hchi (X := X)
  have hpointFirst : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖F t‖ ≤ 4 * (X : ℝ) * S := by
    intro t ht
    change ‖((Int.fract t : ℝ) : ℂ) *
      charPrefix (quadraticEulerCutoff X t)‖ ≤ _
    rw [norm_mul]
    have hfract : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le
    have hprefix :=
      norm_dirichletCharacterWeightedPrefixSum_le
        hq chi hchi (quadraticEulerCutoff X t)
    change ‖charPrefix (quadraticEulerCutoff X t)‖ ≤ _ at hprefix
    calc
      ‖((Int.fract t : ℝ) : ℂ)‖ *
          ‖charPrefix (quadraticEulerCutoff X t)‖ ≤
          1 * (4 * (quadraticEulerCutoff X t : ℝ) * S) := by
        simpa [S, mul_assoc] using
          mul_le_mul hfract hprefix (norm_nonneg _) zero_le_one
      _ ≤ 4 * (X : ℝ) * S := by
        have hcut : (quadraticEulerCutoff X t : ℝ) ≤ (X : ℝ) := by
          exact_mod_cast quadraticEulerCutoff_le X t
        have hfour : (0 : ℝ) ≤ 4 := by norm_num
        have h4cut : 4 * (quadraticEulerCutoff X t : ℝ) ≤
            4 * (X : ℝ) := mul_le_mul_of_nonneg_left hcut hfour
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right h4cut hS
  have hpointSecond : ∀ t ∈ Set.Ioc (1 : ℝ) X,
      ‖F t‖ ≤ (4 * (X : ℝ) * S) * t⁻¹ := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans ht.1
    change ‖((Int.fract t : ℝ) : ℂ) *
      charPrefix (quadraticEulerCutoff X t)‖ ≤ _
    rw [norm_mul]
    have hfract : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le
    have hprefix := norm_dirichletCharacterWeightedPrefixSum_le
      hq chi hchi (quadraticEulerCutoff X t)
    change ‖charPrefix (quadraticEulerCutoff X t)‖ ≤ _ at hprefix
    calc
      ‖((Int.fract t : ℝ) : ℂ)‖ *
          ‖charPrefix (quadraticEulerCutoff X t)‖ ≤
          1 * (4 * (quadraticEulerCutoff X t : ℝ) * S) := by
        simpa [S, mul_assoc] using
          mul_le_mul hfract hprefix (norm_nonneg _) zero_le_one
      _ ≤ 4 * ((X : ℝ) / t) * S := by
        have hcut : (quadraticEulerCutoff X t : ℝ) ≤ (X : ℝ) / t :=
          cast_quadraticEulerCutoff_le_div ht0
        have hfour : (0 : ℝ) ≤ 4 := by norm_num
        have h4cut : 4 * (quadraticEulerCutoff X t : ℝ) ≤
            4 * ((X : ℝ) / t) :=
          mul_le_mul_of_nonneg_left hcut hfour
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right h4cut hS
      _ = (4 * (X : ℝ) * S) * t⁻¹ := by ring
  have hFirstInt : IntegrableOn (fun t ↦ ‖F t‖) (Set.Ioc (0 : ℝ) 1) :=
    (hFint.mono_set (Set.Ioc_subset_Ioc_right hOneX)).norm
  have hSecondInt : IntegrableOn (fun t ↦ ‖F t‖) (Set.Ioc (1 : ℝ) X) :=
    (hFint.mono_set (Set.Ioc_subset_Ioc_left zero_le_one)).norm
  have hFirstMajor : IntegrableOn (fun _t : ℝ ↦ 4 * (X : ℝ) * S)
      (Set.Ioc (0 : ℝ) 1) := integrableOn_const measure_Ioc_lt_top.ne
  have hSecondMajor : IntegrableOn (fun t : ℝ ↦
      (4 * (X : ℝ) * S) * t⁻¹) (Set.Ioc (1 : ℝ) X) := by
    have hinv : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc 1 X) := by
      apply ContinuousOn.inv₀ continuousOn_id
      intro t ht
      exact (zero_lt_one.trans_le ht.1).ne'
    exact (hinv.const_mul (4 * (X : ℝ) * S)).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hFirst : (∫ t : ℝ in Set.Ioc 0 1, ‖F t‖) ≤
      4 * (X : ℝ) * S := by
    calc
      (∫ t : ℝ in Set.Ioc 0 1, ‖F t‖) ≤
          ∫ _t : ℝ in Set.Ioc 0 1, 4 * (X : ℝ) * S := by
        apply setIntegral_mono_ae_restrict hFirstInt hFirstMajor
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hpointFirst t ht
      _ = 4 * (X : ℝ) * S := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Ioc]
        norm_num [smul_eq_mul]
  have hSecond : (∫ t : ℝ in Set.Ioc 1 (X : ℝ), ‖F t‖) ≤
      4 * (X : ℝ) * S * Real.log (X : ℝ) := by
    calc
      (∫ t : ℝ in Set.Ioc 1 (X : ℝ), ‖F t‖) ≤
          ∫ t : ℝ in Set.Ioc 1 (X : ℝ),
            (4 * (X : ℝ) * S) * t⁻¹ := by
        apply setIntegral_mono_ae_restrict hSecondInt hSecondMajor
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hpointSecond t ht
      _ = 4 * (X : ℝ) * S * Real.log (X : ℝ) := by
        rw [integral_const_mul]
        rw [← intervalIntegral.integral_of_le hOneX]
        rw [integral_inv_of_pos zero_lt_one hXreal]
        simp only [div_one]
  have hunion : Set.Ioc (0 : ℝ) (X : ℝ) =
      Set.Ioc (0 : ℝ) (1 : ℝ) ∪ Set.Ioc (1 : ℝ) (X : ℝ) := by
    ext t
    simp only [Set.mem_Ioc, Set.mem_union]
    constructor
    · intro ht
      by_cases ht1 : t ≤ 1
      · exact Or.inl ⟨ht.1, ht1⟩
      · exact Or.inr ⟨lt_of_not_ge ht1, ht.2⟩
    · rintro (ht | ht) <;> constructor
      · exact ht.1
      · exact ht.2.trans hOneX
      · exact zero_lt_one.trans ht.1
      · exact ht.2
  have hdis : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioc 1 X) := by
    rw [Set.disjoint_left]
    intro t ht1 ht2
    exact (not_lt_of_ge ht1.2) ht2.1
  have hnormIntegral : ‖∫ t : ℝ in Set.Ioc 0 (X : ℝ), F t‖ ≤
      4 * (X : ℝ) * (1 + Real.log (X : ℝ)) * S := by
    calc
      ‖∫ t : ℝ in Set.Ioc 0 (X : ℝ), F t‖ ≤
          ∫ t : ℝ in Set.Ioc 0 (X : ℝ), ‖F t‖ :=
        norm_integral_le_integral_norm _
      _ = (∫ t : ℝ in Set.Ioc 0 1, ‖F t‖) +
          ∫ t : ℝ in Set.Ioc 1 (X : ℝ), ‖F t‖ := by
        rw [hunion, setIntegral_union hdis measurableSet_Ioc
          hFirstInt hSecondInt]
      _ ≤ 4 * (X : ℝ) * S +
          4 * (X : ℝ) * S * Real.log (X : ℝ) := add_le_add hFirst hSecond
      _ = 4 * (X : ℝ) * (1 + Real.log (X : ℝ)) * S := by ring
  unfold quadraticZetaSwappedEulerRemainder
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  change (1 / (X : ℝ)) *
      ‖∫ t : ℝ in Set.Ioc 0 (X : ℝ), F t‖ ≤ _
  calc
    (1 / (X : ℝ)) * ‖∫ t : ℝ in Set.Ioc 0 (X : ℝ), F t‖ ≤
        (1 / (X : ℝ)) *
          (4 * (X : ℝ) * (1 + Real.log (X : ℝ)) * S) :=
      mul_le_mul_of_nonneg_left hnormIntegral (by positivity)
    _ = 4 * (1 + Real.log (X : ℝ)) * Real.sqrt (q : ℝ) *
        Real.log (q : ℝ) := by
      dsimp [S]
      field_simp [hXreal.ne']

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/QuadraticZetaLFunctionComparison.lean` -/

section

/-!
# Comparison with the ordered value at one

The direct Euler expansion and the ordered reciprocal-prefix estimate give a
quantitative comparison with `L(1, chi)`.  The theorem leaves the swapped
Euler remainder as an explicit hypothesis; this is the bridge consumed by the
later analytic lower-bound route.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 124--125.
Semantic review: `SEM-546`.
-/

noncomputable section

open scoped BigOperators

namespace BoundedGaps.Maynard

/-- The smoothed quadratic sum differs from its `L(1, chi)` main term by the
reciprocal-prefix error and the explicitly displayed Euler remainder. -/
theorem norm_quadraticZetaLinearSmoothedSum_sub_half_LFunction_le
    {q X : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (hX : 0 < X)
    (B : ℝ)
    (hB : ‖quadraticZetaSwappedEulerRemainder chi X‖ ≤ B) :
    ‖quadraticZetaLinearSmoothedSum chi X -
        ((X : ℂ) / 2) * DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) + B := by
  let P : ℂ := ∑ a ∈ Finset.Icc 1 X,
    chi (a : ZMod q) / (a : ℂ)
  let S : ℝ := Real.sqrt (q : ℝ) * Real.log (q : ℝ)
  have htail := norm_LFunction_one_sub_dirichletCharacterReciprocalPrefix_le
    hq chi hchi X hX
  have htail' : ‖P - DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
      4 * S / (X : ℝ) := by
    rw [norm_sub_rev]
    dsimp [P, S]
    convert htail using 1 ; ring
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hmain := quadraticZetaLinearSmoothedSum_eq_directEulerRemainder chi hX
  have hswap := quadraticZetaDirectEulerRemainder_eq_swapped chi hX
  have hscale : ‖((X : ℂ) / 2)‖ = (X : ℝ) / 2 := by
    rw [norm_div, Complex.norm_natCast]
    norm_num
  have hscaled : ‖((X : ℂ) / 2) *
        (P - DirichletCharacter.LFunction chi (1 : ℂ))‖ ≤ 2 * S := by
    rw [norm_mul, hscale]
    calc
      ((X : ℝ) / 2) * ‖P - DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
          ((X : ℝ) / 2) * (4 * S / (X : ℝ)) :=
        mul_le_mul_of_nonneg_left htail' (by positivity)
      _ = 2 * S := by
        field_simp [hXreal.ne']
        ring
  calc
    ‖quadraticZetaLinearSmoothedSum chi X -
        ((X : ℂ) / 2) * DirichletCharacter.LFunction chi (1 : ℂ)‖ =
        ‖((X : ℂ) / 2) *
            (P - DirichletCharacter.LFunction chi (1 : ℂ)) -
          quadraticZetaSwappedEulerRemainder chi X‖ := by
      rw [hmain, hswap]
      dsimp [P]
      ring_nf
    _ ≤ ‖((X : ℂ) / 2) *
          (P - DirichletCharacter.LFunction chi (1 : ℂ))‖ +
        ‖quadraticZetaSwappedEulerRemainder chi X‖ := norm_sub_le _ _
    _ ≤ 2 * S + B := add_le_add hscaled hB
    _ = 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) + B := by
      dsimp [S]
      ring

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/QuadraticZetaSquareScaleLower.lean` -/

section

/-!
# Square-root scale of the smoothed square sum

The bare square weights in the linearly smoothed quadratic convolution have
an explicit square-root lower bound. The constant is sharp on the stated
natural-endpoint range.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 125, proof
of Theorem 12.8. Semantic review: `SEM-541`.
-/

noncomputable section

open scoped BigOperators ComplexOrder

namespace BoundedGaps.Maynard

/-- The positive square weights below a natural cutoff have square-root
scale. -/
theorem three_eighths_mul_real_sqrt_le_sum_square_linearCutoff
    {X : ℕ} (hX : 4 ≤ X) :
    (3 / 8 : ℝ) * Real.sqrt (X : ℝ) ≤
      ∑ m ∈ Finset.Icc 1 X.sqrt,
        (1 - (m : ℝ) ^ 2 / (X : ℝ) : ℝ) := by
  have hXpos : 0 < X := by omega
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hsqrt_two : 2 ≤ X.sqrt := by
    rw [Nat.le_sqrt]
    omega
  have hsum_sq : ∀ r : ℕ,
      (∑ m ∈ Finset.Icc 1 r, (m : ℝ) ^ 2) =
        (r : ℝ) * ((r : ℝ) + 1) * (2 * (r : ℝ) + 1) / 6 := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih]
        push_cast
        ring
  have hsum_weights :
      (∑ m ∈ Finset.Icc 1 X.sqrt,
          (1 - (m : ℝ) ^ 2 / (X : ℝ) : ℝ)) =
        (X.sqrt : ℝ) -
          (X.sqrt : ℝ) * ((X.sqrt : ℝ) + 1) *
            (2 * (X.sqrt : ℝ) + 1) / (6 * (X : ℝ)) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsum_sq]
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    push_cast
    simp
    ring
  rw [hsum_weights]
  let r : ℝ := X.sqrt
  let R : ℝ := Real.sqrt (X : ℝ)
  let u : ℝ := R - r
  change (3 / 8 : ℝ) * R ≤
    r - r * (r + 1) * (2 * r + 1) / (6 * (X : ℝ))
  have hr : (2 : ℝ) ≤ r := by
    dsimp only [r]
    exact_mod_cast hsqrt_two
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hR_sq : R ^ 2 = (X : ℝ) := by
    dsimp only [R]
    exact Real.sq_sqrt hXreal.le
  have hrR : r ≤ R := by
    dsimp only [r, R]
    exact Real.nat_sqrt_le_real_sqrt
  have hRlt : R < r + 1 := by
    dsimp only [r, R]
    exact Real.real_sqrt_lt_nat_sqrt_succ
  have hu0 : (0 : ℝ) ≤ u := by
    dsimp only [u]
    linarith
  have hu1 : u < 1 := by
    dsimp only [u]
    linarith
  have hru : r * u ≤ r := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hu1.le)]
  have hu_sq : u ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1.le)]
  have hr_sq : (4 : ℝ) ≤ r ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (by linarith : 0 ≤ r + 2)]
  have hbracket :
      (0 : ℝ) ≤ 21 * r ^ 2 - 3 * r * u - 9 * u ^ 2 := by
    nlinarith
  have hfirst :
      (0 : ℝ) ≤ r * (r - 2) * (7 * r + 2) :=
    mul_nonneg (mul_nonneg hr0 (sub_nonneg.mpr hr)) (by nlinarith)
  have hsecond :
      (0 : ℝ) ≤ u * (21 * r ^ 2 - 3 * r * u - 9 * u ^ 2) :=
    mul_nonneg hu0 hbracket
  have hidentity :
      24 * (X : ℝ) *
          (r - r * (r + 1) * (2 * r + 1) / (6 * (X : ℝ)) -
            (3 / 8 : ℝ) * R) =
        r * (r - 2) * (7 * r + 2) +
          u * (21 * r ^ 2 - 3 * r * u - 9 * u ^ 2) := by
    rw [← hR_sq]
    dsimp only [u]
    field_simp [show R ≠ 0 by positivity]
    ring
  have hscaled :
      (0 : ℝ) ≤ 24 * (X : ℝ) *
        (r - r * (r + 1) * (2 * r + 1) / (6 * (X : ℝ)) -
          (3 / 8 : ℝ) * R) := by
    rw [hidentity]
    exact add_nonneg hfirst hsecond
  have hscale_pos : (0 : ℝ) < 24 * (X : ℝ) := by positivity
  have := (mul_nonneg_iff_of_pos_left hscale_pos).mp hscaled
  linarith

/-- The linearly smoothed quadratic zeta convolution has square-root scale. -/
theorem three_eighths_mul_real_sqrt_le_quadraticZetaLinearSmoothedSum
    {q X : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hsquare : chi ^ 2 = 1) (hX : 4 ≤ X) :
    (((3 / 8 : ℝ) * Real.sqrt (X : ℝ) : ℝ) : ℂ) ≤
      quadraticZetaLinearSmoothedSum chi X := by
  have hscalar :
      (((3 / 8 : ℝ) * Real.sqrt (X : ℝ) : ℝ) : ℂ) ≤
        ∑ m ∈ Finset.Icc 1 X.sqrt,
          ((1 - (m : ℝ) ^ 2 / (X : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum]
    exact_mod_cast
      three_eighths_mul_real_sqrt_le_sum_square_linearCutoff hX
  exact hscalar.trans
    (sum_square_linearCutoff_le_quadraticZetaLinearSmoothedSum
      hsquare (by omega))

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/QuadraticLValueLowerBound.lean` -/

section

/-!
# Effective lower bound for quadratic L-values at one

The positive smoothed quadratic convolution is compared with its
`L(1, chi)` main term at the explicit cutoff from `QuadraticLValueCutoff`.
This gives a weak but fully effective lower bound, uniformly for primitive
and imprimitive square-principal nonprincipal characters.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 124--125,
Theorem 12.8. Semantic review: `SEM-547`.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedGaps.Maynard

/-- At one, the L-function of a square-principal nonprincipal character is
real. -/
theorem LFunction_one_im_eq_zero_of_sq_eq_one
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1) :
    (DirichletCharacter.LFunction chi (1 : ℂ)).im = 0 := by
  have hconj := LFunction_conj_of_sq_eq_one chi hchi hsquare (1 : ℂ)
  apply Complex.conj_eq_iff_im.mp
  simpa using hconj.symm

private theorem norm_quadraticZetaLinearSmoothedSum_sub_half_LFunction_cutoff_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    ‖quadraticZetaLinearSmoothedSum chi (quadraticLValueCutoff q) -
        ((quadraticLValueCutoff q : ℂ) / 2) *
          DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
      (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
        Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  have hXpos : 0 < quadraticLValueCutoff q := by
    exact lt_of_lt_of_le (by norm_num) (four_le_quadraticLValueCutoff hq)
  have hrem := norm_quadraticZetaSwappedEulerRemainder_le hq chi hchi hXpos
  have hcomparison :=
    norm_quadraticZetaLinearSmoothedSum_sub_half_LFunction_le
      hq chi hchi hXpos
        (4 * (1 + Real.log (quadraticLValueCutoff q : ℝ)) *
          Real.sqrt (q : ℝ) * Real.log (q : ℝ)) hrem
  calc
    ‖quadraticZetaLinearSmoothedSum chi (quadraticLValueCutoff q) -
        ((quadraticLValueCutoff q : ℂ) / 2) *
          DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) +
        4 * (1 + Real.log (quadraticLValueCutoff q : ℝ)) *
          Real.sqrt (q : ℝ) * Real.log (q : ℝ) := hcomparison
    _ = (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
        Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by ring

/-- Effective Theorem 12.8 specialization with all constants displayed. -/
theorem effectiveQuadraticLValueLowerBound
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1) :
    (((1 / (8192 * Real.sqrt (q : ℝ) *
        (Real.log (q : ℝ)) ^ 2) : ℝ) : ℂ)) ≤
      DirichletCharacter.LFunction chi (1 : ℂ) := by
  let X := quadraticLValueCutoff q
  let T := quadraticZetaLinearSmoothedSum chi X
  let L := DirichletCharacter.LFunction chi (1 : ℂ)
  let R := Real.sqrt (X : ℝ)
  have hXfour : 4 ≤ X := by
    simpa [X] using four_le_quadraticLValueCutoff hq
  have hXpos : 0 < X := by omega
  have hXrealPos : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hRpos : 0 < R := by
    exact Real.sqrt_pos.2 hXrealPos
  have hLim : L.im = 0 := by
    simpa [L] using LFunction_one_im_eq_zero_of_sq_eq_one chi hchi hsquare
  have hTlower : (((3 / 8 : ℝ) * R : ℝ) : ℂ) ≤ T := by
    simpa [X, T, R] using
      three_eighths_mul_real_sqrt_le_quadraticZetaLinearSmoothedSum
        hsquare hXfour
  have hTre : (3 / 8 : ℝ) * R ≤ T.re := by
    simpa using (Complex.le_def.mp hTlower).1
  have hTim : T.im = 0 := by
    simpa using (Complex.le_def.mp hTlower).2.symm
  have hnorm :
      ‖T - ((X : ℂ) / 2) * L‖ ≤ (1 / 8 : ℝ) * R := by
    have hcomparison :=
      norm_quadraticZetaLinearSmoothedSum_sub_half_LFunction_cutoff_le
        hq chi hchi
    have herror := quadraticLValueComparisonError_le hq
    exact (by simpa [X, T, L, R] using hcomparison.trans herror)
  have hdiffRe :
      T.re - ((X : ℝ) / 2) * L.re ≤ (1 / 8 : ℝ) * R := by
    have habs := (Complex.abs_re_le_norm (T - ((X : ℂ) / 2) * L)).trans hnorm
    have hupper := (abs_le.mp habs).2
    simpa [Complex.mul_re, hLim] using hupper
  have hmainLower :
      (1 / 4 : ℝ) * R ≤ ((X : ℝ) / 2) * L.re := by
    linarith
  have hhalfXPos : 0 < (X : ℝ) / 2 := by positivity
  have hLlower : (1 / (2 * R) : ℝ) ≤ L.re := by
    apply (mul_le_mul_iff_of_pos_left hhalfXPos).mp
    calc
      ((X : ℝ) / 2) * (1 / (2 * R) : ℝ) = (1 / 4 : ℝ) * R := by
        have hRsq : R ^ 2 = (X : ℝ) := by
          dsimp [R]
          exact Real.sq_sqrt hXrealPos.le
        field_simp [hRpos.ne']
        nlinarith
      _ ≤ ((X : ℝ) / 2) * L.re := hmainLower
  have hsqrtUpper :
      R ≤ 4096 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    simpa [X, R] using sqrt_quadraticLValueCutoff_le hq
  have hdenom :
      2 * R ≤ 8192 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    nlinarith
  have hreciprocal :
      (1 / (8192 * Real.sqrt (q : ℝ) *
          (Real.log (q : ℝ)) ^ 2) : ℝ) ≤ 1 / (2 * R) :=
    one_div_le_one_div_of_le (by positivity) hdenom
  refine Complex.le_def.mpr ⟨?_, ?_⟩
  · change (1 / (8192 * Real.sqrt (q : ℝ) *
        (Real.log (q : ℝ)) ^ 2) : ℝ) ≤
      (DirichletCharacter.LFunction chi (1 : ℂ)).re
    simpa only [L] using hreciprocal.trans hLlower
  · change (0 : ℝ) = (DirichletCharacter.LFunction chi (1 : ℂ)).im
    simpa only [L] using hLim.symm

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/QuadraticRealZeroGap.lean` -/

section

/-!
# Effective real-zero gap for quadratic Dirichlet L-functions

The near-one derivative estimate is integrated along the real axis and
combined with the effective positive lower bound for `L(1, chi)`.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 124--125,
equations (12.11)--(12.12) and Theorem 12.8.  Semantic review: `SEM-548`.
-/

noncomputable section

open Set

namespace BoundedGaps.Maynard

private lemma one_lt_log_modulus_of_character_ne_one
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    1 < Real.log (q : ℝ) := by
  have hqThree : 3 ≤ q := by
    by_contra hq
    have hqPos : 0 < q := NeZero.pos q
    have hqNeOne : q ≠ 1 := fun h ↦ hchi (chi.level_one' h)
    have hqTwo : q = 2 := by omega
    subst q
    have hcard : Nat.card (DirichletCharacter ℂ 2) = 1 := by
      rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
      norm_num
    exact hchi ((Nat.card_eq_one_iff_unique.mp hcard).1.elim chi 1)
  have hqThreeReal : (3 : ℝ) ≤ q := by exact_mod_cast hqThree
  exact (by norm_num : (1 : ℝ) < 1.0986122885).trans
    (Real.log_three_gt_d9.trans_le
      (Real.log_le_log (by norm_num) hqThreeReal))

/-- Norm form of the fundamental-theorem step from a near-one real point to
one. -/
theorem norm_LFunction_one_sub_ofReal_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {beta : ℝ}
    (hbetaNear :
      1 - 1 / (4 * Real.log (q : ℝ)) ≤ beta)
    (hbetaOne : beta ≤ 1) :
    ‖DirichletCharacter.LFunction chi (1 : ℂ) -
        DirichletCharacter.LFunction chi (beta : ℂ)‖ ≤
      512 * (Real.log (q : ℝ)) ^ 2 * (1 - beta) := by
  let f : ℝ → ℂ := fun sigma ↦
    DirichletCharacter.LFunction chi (sigma : ℂ)
  let f' : ℝ → ℂ := fun sigma ↦
    deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)
  have hderiv : ∀ sigma ∈ Icc beta 1,
      HasDerivWithinAt f (f' sigma) (Icc beta 1) sigma := by
    intro sigma _
    exact ((DirichletCharacter.differentiable_LFunction hchi
      (sigma : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hbound : ∀ sigma ∈ Ico beta 1,
      ‖f' sigma‖ ≤ 512 * (Real.log (q : ℝ)) ^ 2 := by
    intro sigma hsigma
    dsimp [f']
    apply norm_deriv_LFunction_ofReal_near_one_le hq chi hchi
    · exact hbetaNear.trans hsigma.1
    · exact hsigma.2.le
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment'
    hderiv hbound (1 : ℝ) (right_mem_Icc.mpr hbetaOne)
  simpa [f] using hmean

/-- Explicit weak gap between one and every real zero at or below one of a
square-principal nonprincipal character. -/
theorem effectiveQuadraticRealZeroGap
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1)
    {beta : ℝ} (hbetaOne : beta ≤ 1)
    (hzero : DirichletCharacter.LFunction chi (beta : ℂ) = 0) :
    1 / ((2 ^ 22 : ℝ) * Real.sqrt (q : ℝ) *
        (Real.log (q : ℝ)) ^ 4) ≤
      1 - beta := by
  let L := Real.log (q : ℝ)
  let D := (2 ^ 22 : ℝ) * Real.sqrt (q : ℝ) * L ^ 4
  have hLpos : 0 < L := Real.log_pos (by exact_mod_cast hq)
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (q : ℝ) := by
    simpa using Real.sqrt_le_sqrt hqOne
  have hLone : 1 < L := by
    exact one_lt_log_modulus_of_character_ne_one chi hchi
  have hLpow : L ≤ L ^ 4 := by
    simpa using pow_le_pow_right₀ hLone.le (show 1 ≤ 4 by norm_num)
  have hdenom : 4 * L ≤ D := by
    have hprod : L ≤ Real.sqrt (q : ℝ) * L ^ 4 := by
      calc
        L ≤ L ^ 4 := hLpow
        _ = 1 * L ^ 4 := by ring
        _ ≤ Real.sqrt (q : ℝ) * L ^ 4 := by gcongr
    dsimp [D]
    nlinarith
  have hfarTarget : 1 / D ≤ 1 / (4 * L) :=
    one_div_le_one_div_of_le (by positivity) hdenom
  by_cases hbetaNear : 1 - 1 / (4 * L) ≤ beta
  · have hmean := norm_LFunction_one_sub_ofReal_le hq chi hchi
      (by simpa [L] using hbetaNear) hbetaOne
    have hmeanZero :
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
          512 * L ^ 2 * (1 - beta) := by
      simpa [hzero, L] using hmean
    have hLower := effectiveQuadraticLValueLowerBound hq chi hchi hsquare
    have hLowerRe :
        1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2) ≤
          (DirichletCharacter.LFunction chi (1 : ℂ)).re := by
      have hLowerReRaw := (Complex.le_def.mp hLower).1
      change
        1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2) ≤
          (DirichletCharacter.LFunction chi (1 : ℂ)).re at hLowerReRaw
      exact hLowerReRaw
    have hcombined :
        1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2) ≤
          512 * L ^ 2 * (1 - beta) :=
      hLowerRe.trans (Complex.re_le_norm _ |>.trans hmeanZero)
    have hscalePos : 0 < 512 * L ^ 2 := by positivity
    have hsqrtPos : 0 < Real.sqrt (q : ℝ) := by positivity
    calc
      1 / D =
          (1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2)) /
            (512 * L ^ 2) := by
        dsimp [D]
        field_simp [hLpos.ne', hsqrtPos.ne']
        norm_num
      _ ≤ (512 * L ^ 2 * (1 - beta)) / (512 * L ^ 2) :=
        (div_le_div_iff_of_pos_right hscalePos).2 hcombined
      _ = 1 - beta := by field_simp
  · exact hfarTarget.trans (by
      have : 1 / (4 * L) < 1 - beta := by linarith
      exact this.le)

/-- Real-axis nonvanishing in the explicit weak quadratic zero-free
interval. -/
theorem effectiveQuadraticLFunction_ofReal_ne_zero
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1)
    {sigma : ℝ}
    (hsigma :
      1 - 1 / ((2 ^ 22 : ℝ) * Real.sqrt (q : ℝ) *
        (Real.log (q : ℝ)) ^ 4) < sigma) :
    DirichletCharacter.LFunction chi (sigma : ℂ) ≠ 0 := by
  by_cases hsigmaOne : sigma ≤ 1
  · intro hzero
    have hgap := effectiveQuadraticRealZeroGap hq chi hchi hsquare
      hsigmaOne hzero
    linarith
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi
      (.inl hchi) (by simp; linarith)

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldLValueUpper.lean` -/

section

/-!
# The equation-(12.11) L-value upper bound

The near-one mean-value estimate and the all-nonprincipal value estimate are
combined into one source-shaped bound valid for every real zero at or below
one.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 124,
equation (12.11). Semantic review: `SEM-550`.
-/

noncomputable section

namespace BoundedGaps.Maynard

/-- Explicit norm strengthening of equation (12.11), with no primitivity or
quadraticity hypothesis. -/
theorem norm_LFunction_one_of_real_zero_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {beta : ℝ} (hbetaOne : beta ≤ 1)
    (hzero : DirichletCharacter.LFunction chi (beta : ℂ) = 0) :
    ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
      512 * (1 - beta) * (q : ℝ) ^ ((1 - beta) / 2) *
        (Real.log (q : ℝ)) ^ 2 := by
  let L := Real.log (q : ℝ)
  let Q := (q : ℝ) ^ ((1 - beta) / 2)
  have hLpos : 0 < L := by
    exact Real.log_pos (by exact_mod_cast hq)
  have hdelta : 0 ≤ 1 - beta := sub_nonneg.mpr hbetaOne
  have hqOne : (1 : ℝ) ≤ q := by
    exact_mod_cast hq.le
  have hQone : 1 ≤ Q := by
    exact Real.one_le_rpow hqOne (div_nonneg hdelta (by norm_num))
  by_cases hbetaNear : 1 - 1 / (4 * L) ≤ beta
  · have hmean := norm_LFunction_one_sub_ofReal_le hq chi hchi
      (by simpa [L] using hbetaNear) hbetaOne
    have hbase :
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
          512 * L ^ 2 * (1 - beta) := by
      simpa [hzero, L] using hmean
    calc
      ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
          512 * L ^ 2 * (1 - beta) := hbase
      _ = 512 * (1 - beta) * 1 * L ^ 2 := by ring
      _ ≤ 512 * (1 - beta) * Q * L ^ 2 := by gcongr
      _ = 512 * (1 - beta) * (q : ℝ) ^ ((1 - beta) / 2) *
          (Real.log (q : ℝ)) ^ 2 := rfl
  · have hfar : 1 / (4 * L) < 1 - beta := by
      linarith
    have hvalue :
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤ 32 * L := by
      simpa [L] using
        norm_LFunction_near_one_le hq chi hchi (s := (1 : ℂ))
          (by
            have hfrac : 0 ≤ 5 / (16 * L) := by positivity
            simpa [L] using sub_le_self (1 : ℝ) hfrac)
          (by norm_num)
    calc
      ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤ 32 * L := hvalue
      _ ≤ 128 * L := by nlinarith
      _ = 512 * (1 / (4 * L)) * 1 * L ^ 2 := by
        field_simp [hLpos.ne']
        ring
      _ ≤ 512 * (1 - beta) * Q * L ^ 2 := by gcongr
      _ = 512 * (1 - beta) * (q : ℝ) ^ ((1 - beta) / 2) *
          (Real.log (q : ℝ)) ^ 2 := rfl

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldMellinPositiveBound.lean` -/

section

/-!
# Goldfeld Mellin transform on the positive real axis

The fixed plateau is supported in `[0, 2]` and bounded by one.  Integrating
the resulting power majorant gives the quantitative estimate used in
Goldfeld's proof of Koukoulopoulos Theorem 12.9.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 126.
Semantic review: `SEM-560`.
-/

noncomputable section

open Complex Set MeasureTheory

namespace BoundedGaps.Maynard

/-- Universal norm version of the positive-real Mellin estimate used in the
proof of Theorem 12.9. -/
theorem norm_goldfeldMellinContinuationData_Phi_ofReal_le_two_div
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    ‖goldfeldMellinContinuationData.Phi (delta : ℂ)‖ ≤ 2 / delta := by
  rw [goldfeldMellinContinuationData.agrees_on_right (by simpa using hdelta0)]
  let f : ℝ → ℂ := fun y =>
    (y : ℂ) ^ (((delta : ℝ) : ℂ) - 1) * (goldfeldPlateau y : ℂ)
  have hfIoi : IntegrableOn f (Ioi (0 : ℝ)) := by
    have hconv := goldfeldRawMellin_convergent
      (s := ((delta : ℝ) : ℂ)) (by simpa using hdelta0)
    rw [MellinConvergent] at hconv
    change IntegrableOn f (Ioi (0 : ℝ)) at hconv
    exact hconv
  have htruncate :
      (∫ y in Ioi (0 : ℝ), f y) = ∫ y in Ioc (0 : ℝ) 2, f y := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun _ hy => hy.1)
    intro y hy
    have hyTwo : 2 ≤ y := by
      exact (lt_of_not_ge fun hyLe => hy.2 ⟨hy.1, hyLe⟩).le
    simp [f, goldfeldPlateau_eq_zero hyTwo]
  have hfIoc : IntegrableOn f (Ioc (0 : ℝ) 2) :=
    hfIoi.mono_set (fun _ hy => hy.1)
  have hpowInterval : IntervalIntegrable
      (fun y : ℝ => y ^ (delta - 1)) volume 0 2 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hpowIoc : IntegrableOn (fun y : ℝ => y ^ (delta - 1))
      (Ioc (0 : ℝ) 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1
      hpowInterval
  have hpoint : ∀ y ∈ Ioc (0 : ℝ) 2, ‖f y‖ ≤ y ^ (delta - 1) := by
    intro y hy
    dsimp only [f]
    rw [norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hy.1]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (goldfeldPlateau_nonneg y)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hy.1.le _)
      (goldfeldPlateau_le_one y)
  have heval :
      (∫ y in Ioc (0 : ℝ) 2, y ^ (delta - 1)) =
        (2 : ℝ) ^ delta / delta := by
    calc
      (∫ y in Ioc (0 : ℝ) 2, y ^ (delta - 1)) =
          ∫ y in (0 : ℝ)..2, y ^ (delta - 1) := by
        exact (intervalIntegral.integral_of_le (by norm_num)).symm
      _ = ((2 : ℝ) ^ ((delta - 1) + 1) -
            (0 : ℝ) ^ ((delta - 1) + 1)) / ((delta - 1) + 1) := by
        rw [integral_rpow (Or.inl (by linarith))]
      _ = (2 : ℝ) ^ delta / delta := by
        rw [show delta - 1 + 1 = delta by ring,
          Real.zero_rpow hdelta0.ne']
        ring
  have hpow : (2 : ℝ) ^ delta ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hdelta1
  rw [goldfeldRawMellin, mellin]
  change ‖∫ y in Ioi (0 : ℝ), f y‖ ≤ 2 / delta
  rw [htruncate]
  calc
    ‖∫ y in Ioc (0 : ℝ) 2, f y‖ ≤
        ∫ y in Ioc (0 : ℝ) 2, ‖f y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioc (0 : ℝ) 2, y ^ (delta - 1) :=
      setIntegral_mono_on hfIoc.norm hpowIoc measurableSet_Ioc hpoint
    _ = (2 : ℝ) ^ delta / delta := heval
    _ ≤ 2 / delta :=
      (div_le_div_iff_of_pos_right hdelta0).2 hpow

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldSmoothedSumLowerBound.lean` -/

section

/-!
# Goldfeld's smoothed-sum lower bound

This file proves the elementary positivity step in Koukoulopoulos Theorem
12.9, printed p. 126.  The cutoff makes the sum finite, every summand is
nonnegative, and the summand at one is exactly one.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, Theorem 12.9, printed
p. 126.

Semantic review: `SEM-554`.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedGaps.Maynard

private theorem goldfeldSmoothedSummand_nonneg
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare : chi ^ 2 = 1)
    (beta x : ℝ) (n : ℕ) :
    0 ≤ goldfeldBetaCoefficient chi1 chi beta n *
      (goldfeldPlateau ((n : ℝ) / x) : ℂ) := by
  apply mul_nonneg
  · simpa [goldfeldBetaCoefficient] using
      LSeries.term_nonneg
        (goldfeldCoefficient_nonneg chi1 chi hsquare1 hsquare n) beta
  · exact (RCLike.ofReal_nonneg (K := ℂ)).2
      (goldfeldPlateau_nonneg _)

private theorem goldfeldSmoothedSummand_summable
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta : ℝ) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ =>
      goldfeldBetaCoefficient chi1 chi beta n *
        (goldfeldPlateau ((n : ℝ) / x) : ℂ) := by
  apply summable_of_ne_finset_zero
    (s := Finset.range (Nat.ceil (2 * x)))
  intro n hn
  have hnceil : Nat.ceil (2 * x) ≤ n := by
    simpa only [Finset.mem_range, not_lt] using hn
  have hcutoff : 2 * x ≤ (n : ℝ) := by
    calc
      2 * x ≤ (Nat.ceil (2 * x) : ℕ) := Nat.le_ceil _
      _ ≤ n := by exact_mod_cast hnceil
  have hratio : 2 ≤ (n : ℝ) / x :=
    (le_div_iff₀ hx).2 hcutoff
  rw [goldfeldPlateau_eq_zero hratio]
  simp

/-- The source auxiliary sum is at least its `n = 1` summand. -/
theorem one_le_goldfeldSmoothedSum
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare : chi ^ 2 = 1)
    {beta x : ℝ} (hx : 1 ≤ x) :
    (1 : ℂ) ≤ goldfeldSmoothedSum chi1 chi beta x := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hsummable :=
    goldfeldSmoothedSummand_summable chi1 chi beta hxpos
  rw [goldfeldSmoothedSum]
  calc
    (1 : ℂ) = goldfeldBetaCoefficient chi1 chi beta 1 *
        (goldfeldPlateau ((1 : ℝ) / x) : ℂ) := by
      rw [goldfeldBetaCoefficient,
        LSeries.term_of_ne_zero one_ne_zero, goldfeldCoefficient_one]
      have hplateau : goldfeldPlateau ((1 : ℝ) / x) = 1 :=
        goldfeldPlateau_eq_one
          (div_nonneg zero_le_one hxpos.le)
          ((div_le_one hxpos).2 hx)
      rw [hplateau]
      norm_num
    _ ≤ ∑' n : ℕ,
        goldfeldBetaCoefficient chi1 chi beta n *
          (goldfeldPlateau ((n : ℝ) / x) : ℂ) := by
      simpa using hsummable.sum_le_tsum {1} fun n _ =>
        goldfeldSmoothedSummand_nonneg
          chi1 chi hsquare1 hsquare beta x n

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldQuantitativeResidue.lean` -/

section

/-!
# Quantitative bounds for Goldfeld's contour residue

The exact contour identity first gives a lower bound for the residue after the
left line is made small.  The residue's four explicit factors then give the
matching upper bound used in Koukoulopoulos Theorem 12.9.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 126.
Semantic review: `SEM-560`.
-/

noncomputable section

open Complex
open scoped ComplexOrder

namespace BoundedGaps.Maynard

/-- If the complete left line costs at most one half, positivity of the
smoothed sum forces the exact shifted-zeta residue to have norm at least one
half. -/
theorem half_le_norm_goldfeldContourResidue_of_leftLine
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare : chi ^ 2 = 1)
    {beta x : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 1 ≤ x)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    (hleft : ‖goldfeldVerticalIntegral chi1 chi beta x (-1)‖ ≤ 1 / 2) :
    1 / 2 ≤ ‖goldfeldContourResidue chi1 chi beta x‖ := by
  have hsumOrder := one_le_goldfeldSmoothedSum
    chi1 chi hsquare1 hsquare (beta := beta) hx
  have hsumRe : 1 ≤ (goldfeldSmoothedSum chi1 chi beta x).re := by
    have hre := Complex.re_le_re hsumOrder
    simpa using hre
  have hsumNorm : 1 ≤ ‖goldfeldSmoothedSum chi1 chi beta x‖ :=
    hsumRe.trans (Complex.re_le_norm _)
  rw [goldfeldSmoothedSum_eq_residue_add_verticalIntegral_neg_one
    hq1 hq1q chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hx hzero] at hsumNorm
  have htriangle :
      1 ≤ ‖goldfeldContourResidue chi1 chi beta x‖ +
        ‖goldfeldVerticalIntegral chi1 chi beta x (-1)‖ :=
    hsumNorm.trans (norm_add_le _ _)
  linarith

/-- Explicit upper bound for the residue after applying equation (12.11), the
cross-character value estimate, and the positive-real Mellin estimate. -/
theorem norm_goldfeldContourResidue_le
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 1 ≤ x)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    ‖goldfeldContourResidue chi1 chi beta x‖ ≤
      65536 * x ^ (1 - beta) *
        (q : ℝ) ^ ((1 - beta) / 2) *
        (Real.log (q : ℝ)) ^ 3 *
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
  let delta : ℝ := 1 - beta
  have hdelta0 : 0 < delta := by dsimp [delta]; linarith
  have hdelta1 : delta ≤ 1 := by dsimp [delta]; linarith
  have hdeltaNonneg : 0 ≤ delta := hdelta0.le
  have hq1Pos : 0 < (q1 : ℝ) := by positivity
  have hq1qReal : (q1 : ℝ) ≤ q := by exact_mod_cast hq1q
  have hlogq1Nonneg : 0 ≤ Real.log (q1 : ℝ) :=
    (Real.log_pos (by exact_mod_cast hq1)).le
  have hlogq1q : Real.log (q1 : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log hq1Pos hq1qReal
  have hqpow :
      (q1 : ℝ) ^ (delta / 2) ≤ (q : ℝ) ^ (delta / 2) :=
    Real.rpow_le_rpow hq1Pos.le hq1qReal (by positivity)
  have hlogpow :
      (Real.log (q1 : ℝ)) ^ 2 ≤ (Real.log (q : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hlogq1Nonneg hlogq1q 2
  have hLone := norm_LFunction_one_of_real_zero_le
    hq1 chi1 hchi1 hbeta1.le hzero
  have hLoneQ :
      ‖DirichletCharacter.LFunction chi1 (1 : ℂ)‖ ≤
        512 * delta * (q : ℝ) ^ (delta / 2) *
          (Real.log (q : ℝ)) ^ 2 := by
    calc
      ‖DirichletCharacter.LFunction chi1 (1 : ℂ)‖ ≤
          512 * delta * (q1 : ℝ) ^ (delta / 2) *
            (Real.log (q1 : ℝ)) ^ 2 := by simpa [delta] using hLone
      _ ≤ 512 * delta * (q : ℝ) ^ (delta / 2) *
          (Real.log (q : ℝ)) ^ 2 := by
        gcongr
  letI : NeZero (Nat.lcm q1 q) :=
    ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩
  have hlcmPos : 0 < Nat.lcm q1 q := NeZero.pos _
  have hq1lcm : q1 ≤ Nat.lcm q1 q :=
    Nat.le_of_dvd hlcmPos (Nat.dvd_lcm_left q1 q)
  have hlcmOne : 1 < Nat.lcm q1 q := hq1.trans_le hq1lcm
  have hlcmNat : Nat.lcm q1 q ≤ q ^ 2 := by
    calc
      Nat.lcm q1 q ≤ q1 * q :=
        Nat.le_of_dvd (Nat.mul_pos (NeZero.pos q1) (NeZero.pos q))
          (Nat.lcm_dvd_mul q1 q)
      _ ≤ q * q := Nat.mul_le_mul_right q hq1q
      _ = q ^ 2 := by ring
  have hlcmReal : (Nat.lcm q1 q : ℝ) ≤ (q : ℝ) ^ 2 := by
    exact_mod_cast hlcmNat
  have hlcmLog :
      Real.log (Nat.lcm q1 q : ℝ) ≤ 2 * Real.log (q : ℝ) := by
    calc
      Real.log (Nat.lcm q1 q : ℝ) ≤ Real.log ((q : ℝ) ^ 2) :=
        Real.log_le_log (by exact_mod_cast hlcmPos) hlcmReal
      _ = 2 * Real.log (q : ℝ) := by rw [Real.log_pow]; norm_num
  have hcrossValue := norm_LFunction_near_one_le hlcmOne
    (DirichletCharacter.mul chi1 chi) hcross (s := (1 : ℂ))
    (by
      exact sub_le_self 1 (div_nonneg (by norm_num) (by positivity)))
    (by norm_num)
  have hcrossQ :
      ‖DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
          (1 : ℂ)‖ ≤ 64 * Real.log (q : ℝ) := by
    nlinarith
  have hPhi :=
    norm_goldfeldMellinContinuationData_Phi_ofReal_le_two_div
      hdelta0 hdelta1
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hxpow :
      ‖(x : ℂ) ^ goldfeldShiftedZetaPole beta‖ = x ^ delta := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
    simp [goldfeldShiftedZetaPole, delta]
  rw [goldfeldContourResidue]
  simp only [norm_mul]
  rw [hxpow]
  calc
    x ^ delta * ‖DirichletCharacter.LFunction chi1 1‖ *
          ‖DirichletCharacter.LFunction chi 1‖ *
          ‖DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) 1‖ *
          ‖goldfeldMellinContinuationData.Phi
            (goldfeldShiftedZetaPole beta)‖ ≤
        x ^ delta *
          (512 * delta * (q : ℝ) ^ (delta / 2) *
            (Real.log (q : ℝ)) ^ 2) *
          ‖DirichletCharacter.LFunction chi 1‖ *
          (64 * Real.log (q : ℝ)) * (2 / delta) := by
      have hPhi' :
          ‖goldfeldMellinContinuationData.Phi
              (goldfeldShiftedZetaPole beta)‖ ≤ 2 / delta := by
        simpa [goldfeldShiftedZetaPole, delta] using hPhi
      gcongr
    _ = 65536 * x ^ (1 - beta) *
        (q : ℝ) ^ ((1 - beta) / 2) *
        (Real.log (q : ℝ)) ^ 3 *
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
      have hbetaNe : 1 - beta ≠ 0 := by linarith
      dsimp [delta]
      field_simp [hbetaNe]
      ring

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldDistinctLValueLower.lean` -/

section

/-!
# Goldfeld's distinct-character L-value lower bound

One global scale choice makes the complete left line smaller than one half.
Combining the resulting residue lower bound with its explicit upper bound
gives the pairwise quantitative L-value estimate used in the proof of
Koukoulopoulos Theorem 12.9.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 126.
Semantic review: `SEM-560`.
-/

noncomputable section

open Complex

namespace BoundedGaps.Maynard

/-- Uniform project-derived norm analogue of Goldfeld's pairwise L-value
lower bound.  The witnesses are chosen before all character data. -/
theorem exists_goldfeldDistinctLValueLowerBound :
    ∃ A : ℕ, 58 ≤ A ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          chi1 ^ 2 = 1 → chi ^ 2 = 1 →
          goldfeldCharactersDistinct chi1 chi →
          ∀ beta : ℝ, 0 ≤ beta → beta < 1 →
            DirichletCharacter.LFunction chi1 (beta : ℂ) = 0 →
            c * (q : ℝ) ^ (-((A : ℝ) * (1 - beta))) /
                (Real.log (q : ℝ)) ^ 3 ≤
              ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
  obtain ⟨E, hE, C, hC, hleft⟩ :=
    exists_norm_goldfeldVerticalIntegral_neg_one_le
  let D : ℝ := 2 * max 1 C
  let A : ℕ := E + 1
  let c : ℝ := (131072 * D)⁻¹
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hDone : 1 ≤ D := by
    dsimp [D]
    nlinarith [le_max_left (1 : ℝ) C]
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨A, ?_, c, hcpos, ?_⟩
  · dsimp [A]
    omega
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi
    hsquare1 hsquare hdistinct beta hbeta0 hbeta1 hzero
  have hqOne : 1 < q := hq1.trans_le hq1q
  have hqPos : 0 < (q : ℝ) := by positivity
  have hqRealOne : (1 : ℝ) ≤ q := by exact_mod_cast hqOne.le
  have hlogqPos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast hqOne)
  have hcross : DirichletCharacter.mul chi1 chi ≠ 1 :=
    goldfeldCrossLevelMul_ne_one chi1 chi hsquare1 hdistinct
  let x : ℝ := D * (q : ℝ) ^ E
  have hqPowPos : 0 < (q : ℝ) ^ E := pow_pos hqPos E
  have hqPowOne : (1 : ℝ) ≤ (q : ℝ) ^ E := one_le_pow₀ hqRealOne
  have hxOne : 1 ≤ x := by
    dsimp [x]
    exact one_le_mul_of_one_le_of_one_le hDone hqPowOne
  have hleftAtScale := hleft q1 q hq1 hq1q chi1 chi
    hchi1 hchi hcross beta x hbeta0 hbeta1.le hxOne
  have hscaleIdentity : C * (q : ℝ) ^ E / x = C / D := by
    dsimp [x]
    field_simp [hDpos.ne', hqPowPos.ne']
  have hCmax : C ≤ max 1 C := le_max_right 1 C
  have hCdiv : C / D ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ hDpos).2
    dsimp [D]
    nlinarith
  have hleftSmall :
      ‖goldfeldVerticalIntegral chi1 chi beta x (-1)‖ ≤ 1 / 2 :=
    hleftAtScale.trans (hscaleIdentity.trans_le hCdiv)
  have hresLower := half_le_norm_goldfeldContourResidue_of_leftLine
    hq1 hq1q chi1 chi hchi1 hchi hcross hsquare1 hsquare
    hbeta0 hbeta1 hxOne hzero hleftSmall
  have hresUpper := norm_goldfeldContourResidue_le
    hq1 hq1q chi1 chi hchi1 hcross hbeta0 hbeta1 hxOne hzero
  let delta : ℝ := 1 - beta
  have hdelta0 : 0 < delta := by dsimp [delta]; linarith
  have hdelta1 : delta ≤ 1 := by dsimp [delta]; linarith
  have hdeltaNonneg : 0 ≤ delta := hdelta0.le
  have hmaster :
      1 ≤ 131072 * x ^ delta * (q : ℝ) ^ (delta / 2) *
        (Real.log (q : ℝ)) ^ 3 *
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
    calc
      (1 : ℝ) = 2 * (1 / 2 : ℝ) := by norm_num
      _ ≤ 2 * ‖goldfeldContourResidue chi1 chi beta x‖ :=
        mul_le_mul_of_nonneg_left hresLower (by norm_num)
      _ ≤ 2 * (65536 * x ^ (1 - beta) *
          (q : ℝ) ^ ((1 - beta) / 2) *
          (Real.log (q : ℝ)) ^ 3 *
          ‖DirichletCharacter.LFunction chi (1 : ℂ)‖) :=
        mul_le_mul_of_nonneg_left hresUpper (by norm_num)
      _ = 131072 * x ^ delta * (q : ℝ) ^ (delta / 2) *
          (Real.log (q : ℝ)) ^ 3 *
          ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
        dsimp [delta]
        ring
  have hDpow : D ^ delta ≤ D := by
    simpa using Real.rpow_le_rpow_of_exponent_le hDone hdelta1
  have hexponent :
      (E : ℝ) * delta + delta / 2 ≤ (A : ℝ) * delta := by
    dsimp [A]
    push_cast
    nlinarith
  have hqExponent :
      (q : ℝ) ^ ((E : ℝ) * delta + delta / 2) ≤
        (q : ℝ) ^ ((A : ℝ) * delta) :=
    Real.rpow_le_rpow_of_exponent_le hqRealOne hexponent
  have hscalePower :
      x ^ delta * (q : ℝ) ^ (delta / 2) ≤
        D * (q : ℝ) ^ ((A : ℝ) * delta) := by
    calc
      x ^ delta * (q : ℝ) ^ (delta / 2) =
          (D ^ delta * (((q : ℝ) ^ E) ^ delta)) *
            (q : ℝ) ^ (delta / 2) := by
        dsimp [x]
        rw [Real.mul_rpow hDpos.le (pow_nonneg hqPos.le E)]
      _ = D ^ delta *
          (q : ℝ) ^ ((E : ℝ) * delta + delta / 2) := by
        rw [← Real.rpow_natCast_mul hqPos.le E delta,
          mul_assoc, ← Real.rpow_add hqPos]
      _ ≤ D * (q : ℝ) ^ ((E : ℝ) * delta + delta / 2) :=
        mul_le_mul_of_nonneg_right hDpow (Real.rpow_nonneg hqPos.le _)
      _ ≤ D * (q : ℝ) ^ ((A : ℝ) * delta) :=
        mul_le_mul_of_nonneg_left hqExponent hDpos.le
  have hmaster' :
      1 ≤ 131072 * D * (q : ℝ) ^ ((A : ℝ) * delta) *
        (Real.log (q : ℝ)) ^ 3 *
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
    calc
      (1 : ℝ) ≤ 131072 *
          (x ^ delta * (q : ℝ) ^ (delta / 2)) *
          (Real.log (q : ℝ)) ^ 3 *
          ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
        simpa [mul_assoc] using hmaster
      _ ≤ 131072 *
          (D * (q : ℝ) ^ ((A : ℝ) * delta)) *
          (Real.log (q : ℝ)) ^ 3 *
          ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
        gcongr
      _ = 131072 * D * (q : ℝ) ^ ((A : ℝ) * delta) *
          (Real.log (q : ℝ)) ^ 3 *
          ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by ring
  have hdenPos :
      0 < 131072 * D * (q : ℝ) ^ ((A : ℝ) * delta) *
        (Real.log (q : ℝ)) ^ 3 := by
    positivity
  have hdivided :
      1 / (131072 * D * (q : ℝ) ^ ((A : ℝ) * delta) *
          (Real.log (q : ℝ)) ^ 3) ≤
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
    apply (div_le_iff₀ hdenPos).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmaster'
  calc
    c * (q : ℝ) ^ (-((A : ℝ) * (1 - beta))) /
          (Real.log (q : ℝ)) ^ 3 =
        1 / (131072 * D * (q : ℝ) ^ ((A : ℝ) * delta) *
          (Real.log (q : ℝ)) ^ 3) := by
      dsimp [c, delta]
      rw [Real.rpow_neg hqPos.le]
      field_simp [hDpos.ne',
        (Real.rpow_pos_of_pos hqPos ((A : ℝ) * (1 - beta))).ne',
        hlogqPos.ne']
    _ ≤ ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := hdivided

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/GoldfeldExceptionalCharacter.lean` -/

section

/-!
# Goldfeld's global exceptional character

Primitive real nonprincipal characters at varying moduli are packaged in one
dependent type.  The quantitative pairwise bounds from SEM-550 and SEM-560
then show that, for each positive exponent, at most one such character has a
zero in the corresponding near-one region.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, Theorem 12.9, printed
pp. 125--127. Semantic review: `SEM-561`.
-/

noncomputable section

open Complex Set

namespace BoundedGaps.Maynard

/-- A primitive real nonprincipal Dirichlet character, with its modulus, as
one global label across all character levels. -/
structure GoldfeldPrimitiveRealCharacter where
  modulus : ℕ
  modulus_gt_one : 1 < modulus
  character : DirichletCharacter ℂ modulus
  isPrimitive : character.IsPrimitive
  ne_one : character ≠ 1
  sq_eq_one : character ^ 2 = 1

instance (psi : GoldfeldPrimitiveRealCharacter) : NeZero psi.modulus :=
  ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt psi.modulus_gt_one)⟩

/-- The character has a real zero strictly inside the requested near-one
region. -/
def goldfeldPrimitiveNearOneZero
    (epsilon c : ℝ) (psi : GoldfeldPrimitiveRealCharacter) : Prop :=
  ∃ beta : ℝ,
    1 - c * (psi.modulus : ℝ) ^ (-epsilon) < beta ∧
      beta < 1 ∧
        DirichletCharacter.LFunction psi.character (beta : ℂ) = 0

/-- The source's real-axis zero-free conclusion for one primitive character. -/
def goldfeldPrimitiveZeroFree
    (epsilon c : ℝ) (psi : GoldfeldPrimitiveRealCharacter) : Prop :=
  ∀ sigma : ℝ,
    1 - c * (psi.modulus : ℝ) ^ (-epsilon) < sigma →
      DirichletCharacter.LFunction psi.character (sigma : ℂ) ≠ 0

/-- Global-label inequality is exactly canonical LCM-level character
distinctness. -/
theorem goldfeldPrimitiveRealCharacter_distinct_iff_ne
    (psi1 psi2 : GoldfeldPrimitiveRealCharacter) :
    goldfeldCharactersDistinct psi1.character psi2.character ↔
      psi1 ≠ psi2 := by
  constructor
  · intro hdistinct heq
    subst psi2
    exact (goldfeldCharactersDistinct_same_level_iff _ _).mp hdistinct rfl
  · intro hne
    by_cases hmodulus : psi1.modulus = psi2.modulus
    · cases psi1 with
      | mk q hq chi hprimitive hchi hsquare =>
        cases psi2 with
        | mk q' hq' chi' hprimitive' hchi' hsquare' =>
          dsimp at hmodulus
          subst q'
          letI : NeZero q :=
            ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hq)⟩
          rw [goldfeldCharactersDistinct_same_level_iff]
          intro hcharacters
          apply hne
          cases hcharacters
          rfl
    · exact goldfeldCharactersDistinct_of_modulus_ne
        psi1.character psi2.character psi1.isPrimitive psi2.isPrimitive
        hmodulus

/-- Having a near-one zero is exactly failure of the real-axis zero-free
predicate. -/
theorem goldfeldPrimitiveNearOneZero_iff_not_zeroFree
    (epsilon c : ℝ) (psi : GoldfeldPrimitiveRealCharacter) :
    goldfeldPrimitiveNearOneZero epsilon c psi ↔
      ¬ goldfeldPrimitiveZeroFree epsilon c psi := by
  constructor
  · rintro ⟨beta, hbetaLower, _, hzero⟩ hzeroFree
    exact hzeroFree beta hbetaLower hzero
  · intro hnotZeroFree
    classical
    simp only [goldfeldPrimitiveZeroFree, not_forall,
      not_ne_iff] at hnotZeroFree
    obtain ⟨sigma, hsigmaLower, hzero⟩ := hnotZeroFree
    refine ⟨sigma, hsigmaLower, ?_, hzero⟩
    by_contra hsigmaOne
    have hone : 1 ≤ sigma := le_of_not_gt hsigmaOne
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re
      psi.character (.inl psi.ne_one) (by simpa using hone)) hzero

/-- For every positive exponent, the primitive real characters with a zero
in one common near-one region form a subsingleton across all moduli. -/
theorem exists_goldfeldPrimitiveNearOneZero_subsingleton :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ c : ℝ, 0 < c ∧
        Set.Subsingleton
          {psi : GoldfeldPrimitiveRealCharacter |
            goldfeldPrimitiveNearOneZero epsilon c psi} := by
  intro epsilon hepsilon
  obtain ⟨A, hA, c0, hc0, hLValueLower⟩ :=
    exists_goldfeldDistinctLValueLowerBound
  let r : ℝ := epsilon / 20
  let c : ℝ := min (1 / 2) (min
    (epsilon / (2 * (A : ℝ))) (c0 * r ^ 5 / 1024))
  have hAOne : (1 : ℝ) ≤ A := by exact_mod_cast (by omega : 1 ≤ A)
  have hAPos : (0 : ℝ) < A := zero_lt_one.trans_le hAOne
  have hrPos : 0 < r := by dsimp [r]; positivity
  have hcPos : 0 < c := by
    dsimp [c]
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hcHalf : c ≤ 1 / 2 := by
    dsimp [c]
    exact min_le_left _ _
  have hcExponent : c ≤ epsilon / (2 * (A : ℝ)) := by
    dsimp [c]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hcLog : c ≤ c0 * r ^ 5 / 1024 := by
    dsimp [c]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hordered :
      ∀ (psi1 psi : GoldfeldPrimitiveRealCharacter),
        psi1.modulus ≤ psi.modulus →
          goldfeldPrimitiveNearOneZero epsilon c psi1 →
            goldfeldPrimitiveNearOneZero epsilon c psi →
              goldfeldCharactersDistinct psi1.character psi.character →
                False := by
    intro psi1 psi hmoduli hnear1 hnear hdistinct
    obtain ⟨beta1, hbeta1Lower, hbeta1One, hzero1⟩ := hnear1
    obtain ⟨beta, hbetaLower, hbetaOne, hzero⟩ := hnear
    let Q : ℝ := psi.modulus
    let L : ℝ := Real.log Q
    let delta1 : ℝ := 1 - beta1
    let delta : ℝ := 1 - beta
    have hQOne : 1 ≤ Q := by
      dsimp [Q]
      exact_mod_cast psi.modulus_gt_one.le
    have hQPos : 0 < Q := zero_lt_one.trans_le hQOne
    have hLPos : 0 < L := by
      dsimp [L, Q]
      exact Real.log_pos (by exact_mod_cast psi.modulus_gt_one)
    have hq1PowLeOne :
        (psi1.modulus : ℝ) ^ (-epsilon) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast psi1.modulus_gt_one.le) (by linarith)
    have hqPowLeOne : Q ^ (-epsilon) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hQOne (by linarith)
    have hdelta1Near :
        delta1 < c * (psi1.modulus : ℝ) ^ (-epsilon) := by
      dsimp [delta1]
      linarith
    have hdeltaNear : delta < c * Q ^ (-epsilon) := by
      dsimp [delta, Q] at hbetaLower ⊢
      linarith
    have hdelta1LtC : delta1 < c :=
      hdelta1Near.trans_le (mul_le_of_le_one_right hcPos.le hq1PowLeOne)
    have hdeltaLtC : delta < c :=
      hdeltaNear.trans_le (mul_le_of_le_one_right hcPos.le hqPowLeOne)
    have hbeta1Half : 1 / 2 < beta1 := by
      have hbase : 1 - c ≤
          1 - c * (psi1.modulus : ℝ) ^ (-epsilon) := by
        linarith [mul_le_of_le_one_right hcPos.le hq1PowLeOne]
      linarith
    have hbetaHalf : 1 / 2 < beta := by
      have hbase : 1 - c ≤ 1 - c * Q ^ (-epsilon) := by
        linarith [mul_le_of_le_one_right hcPos.le hqPowLeOne]
      dsimp [Q] at hbase hbetaLower
      linarith
    have hLower := hLValueLower psi1.modulus psi.modulus
      psi1.modulus_gt_one hmoduli psi1.character psi.character
      psi1.ne_one psi.ne_one psi1.sq_eq_one psi.sq_eq_one hdistinct
      beta1 (by linarith) hbeta1One hzero1
    have hUpper := norm_LFunction_one_of_real_zero_le
      psi.modulus_gt_one psi.character psi.ne_one hbetaOne.le hzero
    have hLThreePos : 0 < L ^ 3 := pow_pos hLPos 3
    have hcomparison :
        c0 * Q ^ (-((A : ℝ) * delta1)) ≤
          512 * delta * Q ^ (delta / 2) * L ^ 5 := by
      calc
        c0 * Q ^ (-((A : ℝ) * delta1)) ≤
            ‖DirichletCharacter.LFunction psi.character (1 : ℂ)‖ *
              L ^ 3 := by
          apply (div_le_iff₀ hLThreePos).mp
          simpa [Q, L, delta1] using hLower
        _ ≤ (512 * delta * Q ^ (delta / 2) * L ^ 2) * L ^ 3 :=
          mul_le_mul_of_nonneg_right (by simpa [Q, L, delta] using hUpper)
            hLThreePos.le
        _ = 512 * delta * Q ^ (delta / 2) * L ^ 5 := by ring
    have hdelta1Exponent :
        (A : ℝ) * delta1 < epsilon / 2 := by
      have hdelta1Bound :
          delta1 < epsilon / (2 * (A : ℝ)) :=
        hdelta1LtC.trans_le hcExponent
      calc
        (A : ℝ) * delta1 <
            (A : ℝ) * (epsilon / (2 * (A : ℝ))) :=
          mul_lt_mul_of_pos_left hdelta1Bound hAPos
        _ = epsilon / 2 := by field_simp [hAPos.ne']
    have hleftFloor :
        c0 * Q ^ (-epsilon / 2) ≤
          c0 * Q ^ (-((A : ℝ) * delta1)) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hQOne (by linarith)) hc0.le
    have hcScaled : c * (2 * (A : ℝ)) ≤ epsilon :=
      (le_div_iff₀ (by positivity : 0 < 2 * (A : ℝ))).mp hcExponent
    have hcEpsilonHalf : c ≤ epsilon / 2 := by
      have htwoC : 2 * c ≤ c * (2 * (A : ℝ)) := by
        calc
          2 * c = c * (2 * 1) := by ring
          _ ≤ c * (2 * (A : ℝ)) := by gcongr
      linarith
    have hdeltaQuarter : delta / 2 ≤ epsilon / 4 := by
      linarith
    have hdeltaPower : Q ^ (delta / 2) ≤ Q ^ (epsilon / 4) :=
      Real.rpow_le_rpow_of_exponent_le hQOne hdeltaQuarter
    have hlogBase : L ≤ Q ^ r / r := by
      simpa [L, Q] using
        Real.log_natCast_le_rpow_div psi.modulus hrPos
    have hlogPow : L ^ 5 ≤ Q ^ (epsilon / 4) / r ^ 5 := by
      calc
        L ^ 5 ≤ (Q ^ r / r) ^ 5 :=
          pow_le_pow_left₀ hLPos.le hlogBase 5
        _ = Q ^ (epsilon / 4) / r ^ 5 := by
          rw [div_pow, ← Real.rpow_mul_natCast hQPos.le]
          congr 2
          dsimp [r]
          ring
    have hpowThreeQuarter :
        Q ^ (-epsilon) * Q ^ (epsilon / 4) =
          Q ^ (-3 * epsilon / 4) := by
      rw [← Real.rpow_add hQPos]
      congr 1
      ring
    have hpowHalf :
        Q ^ (-3 * epsilon / 4) * Q ^ (epsilon / 4) =
          Q ^ (-epsilon / 2) := by
      rw [← Real.rpow_add hQPos]
      congr 1
      ring
    have hupperStrict :
        512 * delta * Q ^ (delta / 2) * L ^ 5 <
          c0 * Q ^ (-epsilon / 2) := by
      calc
        512 * delta * Q ^ (delta / 2) * L ^ 5 <
            512 * (c * Q ^ (-epsilon)) * Q ^ (delta / 2) *
              L ^ 5 := by gcongr
        _ ≤ 512 * (c * Q ^ (-epsilon)) * Q ^ (epsilon / 4) *
              L ^ 5 := by gcongr
        _ = 512 * c * Q ^ (-3 * epsilon / 4) * L ^ 5 := by
          rw [show 512 * (c * Q ^ (-epsilon)) * Q ^ (epsilon / 4) *
              L ^ 5 = 512 * c *
                (Q ^ (-epsilon) * Q ^ (epsilon / 4)) * L ^ 5 by ring,
            hpowThreeQuarter]
        _ ≤ 512 * (c0 * r ^ 5 / 1024) *
              Q ^ (-3 * epsilon / 4) *
                (Q ^ (epsilon / 4) / r ^ 5) := by gcongr
        _ = (c0 / 2) * Q ^ (-epsilon / 2) := by
          calc
            512 * (c0 * r ^ 5 / 1024) * Q ^ (-3 * epsilon / 4) *
                (Q ^ (epsilon / 4) / r ^ 5) =
                (c0 / 2) *
                  (Q ^ (-3 * epsilon / 4) * Q ^ (epsilon / 4)) := by
              field_simp [hrPos.ne']; ring
            _ = (c0 / 2) * Q ^ (-epsilon / 2) := by rw [hpowHalf]
        _ < c0 * Q ^ (-epsilon / 2) := by
          have hproductPos : 0 < c0 * Q ^ (-epsilon / 2) :=
            mul_pos hc0 (Real.rpow_pos_of_pos hQPos _)
          nlinarith
    exact (not_lt_of_ge (hleftFloor.trans hcomparison)) hupperStrict
  refine ⟨c, hcPos, ?_⟩
  intro psi1 hnear1 psi2 hnear2
  by_contra hne
  rcases le_total psi1.modulus psi2.modulus with hle | hle
  · exact hordered psi1 psi2 hle hnear1 hnear2
      ((goldfeldPrimitiveRealCharacter_distinct_iff_ne _ _).2 hne)
  · exact hordered psi2 psi1 hle hnear2 hnear1
      ((goldfeldPrimitiveRealCharacter_distinct_iff_ne _ _).2 (Ne.symm hne))

/-- Source-facing Theorem 12.9: after fixing the exponent, every primitive
real nonprincipal character except one optional global label is zero-free. -/
theorem exists_goldfeldPrimitiveExceptionalCharacter :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ c : ℝ, 0 < c ∧
        ∃ exception : Option GoldfeldPrimitiveRealCharacter,
          ∀ psi : GoldfeldPrimitiveRealCharacter,
            some psi ≠ exception →
              goldfeldPrimitiveZeroFree epsilon c psi := by
  intro epsilon hepsilon
  obtain ⟨c, hc, hsubsingleton⟩ :=
    exists_goldfeldPrimitiveNearOneZero_subsingleton epsilon hepsilon
  refine ⟨c, hc, ?_⟩
  classical
  by_cases hnonempty :
      Set.Nonempty
        {psi : GoldfeldPrimitiveRealCharacter |
          goldfeldPrimitiveNearOneZero epsilon c psi}
  · obtain ⟨exception, hexception⟩ := hnonempty
    refine ⟨some exception, ?_⟩
    intro psi hpsi
    by_contra hnotZeroFree
    have hnear :=
      (goldfeldPrimitiveNearOneZero_iff_not_zeroFree _ _ _).2
        hnotZeroFree
    have heq : psi = exception := hsubsingleton hnear hexception
    exact hpsi (congrArg some heq)
  · refine ⟨none, ?_⟩
    intro psi _
    by_contra hnotZeroFree
    exact hnonempty ⟨psi,
      (goldfeldPrimitiveNearOneZero_iff_not_zeroFree _ _ _).2
        hnotZeroFree⟩

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `BoundedGaps/BombieriVinogradov/Analytic/SiegelZeroFreeRegion.lean` -/

section

/-!
# Siegel's real-character zero-free region

The optional primitive exception from Goldfeld's argument is a single fixed
character.  Its explicit weak zero gap therefore removes it after a
noncomputable shrinking of the common constant.  Equation (11.2) then
transports the result from primitive conductors to arbitrary character levels.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, Theorem 12.10, printed
p. 127, and equation (11.2), printed p. 110. Semantic review: `SEM-562`.
-/

noncomputable section

open Complex

namespace BoundedGaps.Maynard

/-- After fixing the exponent, one positive constant gives a real-axis
zero-free region for every primitive real nonprincipal character. -/
theorem exists_siegelPrimitiveRealCharacterZeroFree :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ c : ℝ, 0 < c ∧
        ∀ psi : GoldfeldPrimitiveRealCharacter,
          goldfeldPrimitiveZeroFree epsilon c psi := by
  intro epsilon hepsilon
  obtain ⟨c0, hc0, exception, hzeroFree⟩ :=
    exists_goldfeldPrimitiveExceptionalCharacter epsilon hepsilon
  cases exception with
  | none =>
      let c : ℝ := min c0 (1 / 2)
      have hcPos : 0 < c := by
        dsimp [c]
        exact lt_min hc0 (by norm_num)
      refine ⟨c, hcPos, ?_⟩
      intro psi sigma hsigma
      apply hzeroFree psi (by simp) sigma
      have hcLe : c ≤ c0 := by
        dsimp [c]
        exact min_le_left _ _
      have hweightNonneg :
          0 ≤ (psi.modulus : ℝ) ^ (-epsilon) :=
        Real.rpow_nonneg (Nat.cast_nonneg psi.modulus) _
      have hscaled :=
        mul_le_mul_of_nonneg_right hcLe hweightNonneg
      linarith
  | some exception =>
      let gap : ℝ :=
        1 / ((2 ^ 22 : ℝ) * Real.sqrt (exception.modulus : ℝ) *
          (Real.log (exception.modulus : ℝ)) ^ 4)
      let weight : ℝ :=
        (exception.modulus : ℝ) ^ (-epsilon)
      let c : ℝ := min (min c0 (1 / 2)) (gap / weight)
      have hmodulusPos : (0 : ℝ) < exception.modulus := by
        exact_mod_cast (Nat.zero_lt_of_lt exception.modulus_gt_one)
      have hlogPos : 0 < Real.log (exception.modulus : ℝ) :=
        Real.log_pos (by exact_mod_cast exception.modulus_gt_one)
      have hgapPos : 0 < gap := by
        dsimp [gap]
        positivity
      have hweightPos : 0 < weight := by
        dsimp [weight]
        exact Real.rpow_pos_of_pos hmodulusPos _
      have hcPos : 0 < c := by
        dsimp [c]
        exact lt_min (lt_min hc0 (by norm_num))
          (div_pos hgapPos hweightPos)
      have hcLe : c ≤ c0 := by
        dsimp [c]
        exact (min_le_left _ _).trans (min_le_left _ _)
      have hcGap : c * weight ≤ gap := by
        apply (le_div_iff₀ hweightPos).mp
        dsimp [c]
        exact min_le_right _ _
      refine ⟨c, hcPos, ?_⟩
      intro psi
      by_cases hpsi : psi = exception
      · subst psi
        intro sigma hsigma
        apply effectiveQuadraticLFunction_ofReal_ne_zero
          exception.modulus_gt_one exception.character exception.ne_one
            exception.sq_eq_one
        have hthreshold : 1 - gap ≤ 1 - c * weight := by
          linarith
        exact hthreshold.trans_lt (by simpa [weight] using hsigma)
      · intro sigma hsigma
        apply hzeroFree psi (by simpa using hpsi) sigma
        have hweightNonneg :
            0 ≤ (psi.modulus : ℝ) ^ (-epsilon) :=
          Real.rpow_nonneg (Nat.cast_nonneg psi.modulus) _
        have hscaled :=
          mul_le_mul_of_nonneg_right hcLe hweightNonneg
        linarith

/-- Siegel's theorem for every real nonprincipal character, including
imprimitive characters. The witness may depend noncomputably on the optional
global primitive exception selected after the exponent is fixed. -/
theorem exists_siegelRealCharacterZeroFree :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ c : ℝ, 0 < c ∧
        ∀ (q : ℕ) [NeZero q]
          (chi : DirichletCharacter ℂ q),
            chi ≠ 1 →
              chi ^ 2 = 1 →
                ∀ sigma : ℝ,
                  1 - c * (q : ℝ) ^ (-epsilon) < sigma →
                    DirichletCharacter.LFunction chi (sigma : ℂ) ≠ 0 := by
  intro epsilon hepsilon
  obtain ⟨c0, hc0, hprimitive⟩ :=
    exists_siegelPrimitiveRealCharacterZeroFree epsilon hepsilon
  let c : ℝ := min c0 (1 / 2)
  have hcPos : 0 < c := by
    dsimp [c]
    exact lt_min hc0 (by norm_num)
  have hcLe : c ≤ c0 := by
    dsimp [c]
    exact min_le_left _ _
  have hcHalf : c ≤ 1 / 2 := by
    dsimp [c]
    exact min_le_right _ _
  refine ⟨c, hcPos, ?_⟩
  intro q _ chi hchi hsquare sigma hsigma
  have hconductorOne : 1 < chi.conductor := by
    have hconductorZero : chi.conductor ≠ 0 := chi.conductor_ne_zero
    have hconductorNeOne : chi.conductor ≠ 1 := by
      intro hconductor
      exact hchi
        (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hconductor)
    omega
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hprimitiveNeOne : chi.primitiveCharacter ≠ 1 := by
    intro hprincipal
    apply hchi
    rw [← chi.changeLevel_primitiveCharacter]
    exact (DirichletCharacter.changeLevel_eq_one_iff
      chi.conductor_dvd_level).2 hprincipal
  have hprimitiveSquare : chi.primitiveCharacter ^ 2 = 1 := by
    apply DirichletCharacter.changeLevel_injective
      chi.conductor_dvd_level
    rw [map_pow, chi.changeLevel_primitiveCharacter, hsquare, map_one]
  let psi : GoldfeldPrimitiveRealCharacter :=
    { modulus := chi.conductor
      modulus_gt_one := hconductorOne
      character := chi.primitiveCharacter
      isPrimitive := chi.primitiveCharacter_isPrimitive
      ne_one := hprimitiveNeOne
      sq_eq_one := hprimitiveSquare }
  have hconductorLe : chi.conductor ≤ q :=
    Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level
  have hconductorPos : (0 : ℝ) < chi.conductor := by
    exact_mod_cast (Nat.zero_lt_of_lt hconductorOne)
  have hconductorLevel : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast hconductorLe
  have hnegativePower :
      (q : ℝ) ^ (-epsilon) ≤
        (chi.conductor : ℝ) ^ (-epsilon) :=
    Real.rpow_le_rpow_of_nonpos hconductorPos hconductorLevel
      (by linarith)
  have hconductorWeightNonneg :
      0 ≤ (chi.conductor : ℝ) ^ (-epsilon) :=
    Real.rpow_nonneg (Nat.cast_nonneg chi.conductor) _
  have hscaled :
      c * (q : ℝ) ^ (-epsilon) ≤
        c0 * (chi.conductor : ℝ) ^ (-epsilon) := by
    calc
      c * (q : ℝ) ^ (-epsilon) ≤
          c * (chi.conductor : ℝ) ^ (-epsilon) :=
        mul_le_mul_of_nonneg_left hnegativePower hcPos.le
      _ ≤ c0 * (chi.conductor : ℝ) ^ (-epsilon) :=
        mul_le_mul_of_nonneg_right hcLe hconductorWeightNonneg
  have hprimitiveThreshold :
      1 - c0 * (chi.conductor : ℝ) ^ (-epsilon) < sigma := by
    linarith
  have hprimitiveNonzero :
      DirichletCharacter.LFunction chi.primitiveCharacter
          (sigma : ℂ) ≠ 0 := by
    apply hprimitive psi sigma
    simpa [psi] using hprimitiveThreshold
  have hlevelOne : (1 : ℝ) ≤ q := by
    exact_mod_cast NeZero.pos q
  have hlevelWeightLeOne :
      (q : ℝ) ^ (-epsilon) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlevelOne (by linarith)
  have hscaledHalf : c * (q : ℝ) ^ (-epsilon) ≤ 1 / 2 :=
    (mul_le_of_le_one_right hcPos.le hlevelWeightLeOne).trans hcHalf
  have hsigmaPos : 0 < sigma := by
    linarith
  rw [LFunction_eq_inducingPrimitive_mul_inducingEulerProduct chi
    (.inl hchi)]
  exact mul_ne_zero hprimitiveNonzero
    (inducingEulerProduct_ne_zero_of_re_pos chi (by simpa using hsigmaPos))

end BoundedGaps.Maynard

end
end

/-! ### Upstream module `ErdosProblems/Erdos1141/SiegelNearOne.lean` -/

section

/-!
# A small quadratic L-value forces a nearby real zero

Extracted from the proved analytic foundations in `Erdos1140.Erdos1140Base`,
without importing its downstream dependency on the theorem proved here.
-/

namespace Pollack17

open Complex MeasureTheory Metric Set Filter
open ArithmeticFunction
open scoped BigOperators ComplexOrder Real Topology

open BoundedGaps.Maynard

private lemma three_le_modulus_of_character_ne_one__m120
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    3 ≤ q := by
  by_contra hq
  have hqPos : 0 < q := NeZero.pos q
  have hqNeOne : q ≠ 1 := fun h ↦ hchi (chi.level_one' h)
  have hqTwo : q = 2 := by omega
  subst q
  have hcard : Nat.card (DirichletCharacter ℂ 2) = 1 := by
    rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    norm_num
  exact hchi ((Nat.card_eq_one_iff_unique.mp hcard).1.elim chi 1)

private lemma one_lt_log_modulus__m120
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    1 < Real.log (q : ℝ) := by
  have hqThree : (3 : ℝ) ≤ q := by
    exact_mod_cast three_le_modulus_of_character_ne_one__m120 chi hchi
  exact (by norm_num : (1 : ℝ) < 1.0986122885).trans
    (Real.log_three_gt_d9.trans_le
      (Real.log_le_log (by norm_num) hqThree))

private lemma norm_first_order_remainder_right_le
    {f f' f'' : ℝ → ℂ} {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc a b,
      HasDerivWithinAt f (f' t) (Icc a b) t)
    (hf' : ∀ t ∈ Icc a b,
      HasDerivWithinAt f' (f'' t) (Icc a b) t)
    (hbound : ∀ t ∈ Ico a b, ‖f'' t‖ ≤ M) :
    ‖f b - f a - ((b - a : ℝ) : ℂ) * f' a‖ ≤
      M * (b - a) ^ 2 := by
  have hvar : ∀ t ∈ Icc a b, ‖f' t - f' a‖ ≤ M * (t - a) :=
    norm_image_sub_le_of_norm_deriv_le_segment' hf' hbound
  let g : ℝ → ℂ := fun t ↦ f t - ((t - a : ℝ) : ℂ) * f' a
  have hg : ∀ t ∈ Icc a b,
      HasDerivWithinAt g (f' t - f' a) (Icc a b) t := by
    intro t ht
    have hlinear : HasDerivAt
        (fun u : ℝ ↦ ((u - a : ℝ) : ℂ) * f' a) (f' a) t := by
      simpa only [id_eq, Complex.ofReal_sub, Complex.ofReal_one, one_mul] using
        ((((hasDerivAt_id t).sub_const a).ofReal_comp).mul_const (f' a))
    change HasDerivWithinAt
      (fun u : ℝ ↦ f u - ((u - a : ℝ) : ℂ) * f' a)
        (f' t - f' a) (Icc a b) t
    exact (hf t ht).sub hlinear.hasDerivWithinAt
  have hgbound : ∀ t ∈ Ico a b,
      ‖f' t - f' a‖ ≤ M * (b - a) := by
    intro t ht
    exact (hvar t ⟨ht.1, ht.2.le⟩).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le a) hM)
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment'
    hg hgbound b (right_mem_Icc.mpr hab)
  dsimp [g] at hmean
  simp only [sub_self, Complex.ofReal_zero, zero_mul, sub_zero] at hmean
  have heq :
      f b - ((b - a : ℝ) : ℂ) * f' a - f a =
        f b - f a - ((b - a : ℝ) : ℂ) * f' a := by ring
  rw [heq] at hmean
  simpa [g, pow_two, mul_assoc] using hmean

private lemma norm_first_order_remainder_left_le
    {f f' f'' : ℝ → ℂ} {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc a b,
      HasDerivWithinAt f (f' t) (Icc a b) t)
    (hf' : ∀ t ∈ Icc a b,
      HasDerivWithinAt f' (f'' t) (Icc a b) t)
    (hbound : ∀ t ∈ Ico a b, ‖f'' t‖ ≤ M) :
    ‖f a - f b - ((a - b : ℝ) : ℂ) * f' b‖ ≤
      M * (b - a) ^ 2 := by
  have hvar : ∀ t ∈ Icc a b, ‖f' t - f' b‖ ≤ M * (b - t) := by
    intro t ht
    have hsub : Icc t b ⊆ Icc a b := by
      intro u hu
      exact ⟨ht.1.trans hu.1, hu.2⟩
    have hderiv : ∀ u ∈ Icc t b,
        HasDerivWithinAt f' (f'' u) (Icc t b) u := by
      intro u hu
      exact (hf' u (hsub hu)).mono hsub
    have hbd : ∀ u ∈ Ico t b, ‖f'' u‖ ≤ M := by
      intro u hu
      exact hbound u ⟨ht.1.trans hu.1, hu.2⟩
    have hmean := norm_image_sub_le_of_norm_deriv_le_segment'
      hderiv hbd b (right_mem_Icc.mpr ht.2)
    simpa [norm_sub_rev] using hmean
  let g : ℝ → ℂ := fun t ↦ f t - ((t - b : ℝ) : ℂ) * f' b
  have hg : ∀ t ∈ Icc a b,
      HasDerivWithinAt g (f' t - f' b) (Icc a b) t := by
    intro t ht
    have hlinear : HasDerivAt
        (fun u : ℝ ↦ ((u - b : ℝ) : ℂ) * f' b) (f' b) t := by
      simpa only [id_eq, Complex.ofReal_sub, Complex.ofReal_one, one_mul] using
        ((((hasDerivAt_id t).sub_const b).ofReal_comp).mul_const (f' b))
    change HasDerivWithinAt
      (fun u : ℝ ↦ f u - ((u - b : ℝ) : ℂ) * f' b)
        (f' t - f' b) (Icc a b) t
    exact (hf t ht).sub hlinear.hasDerivWithinAt
  have hgbound : ∀ t ∈ Ico a b,
      ‖f' t - f' b‖ ≤ M * (b - a) := by
    intro t ht
    exact (hvar t ⟨ht.1, ht.2.le⟩).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_left ht.1 b) hM)
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment'
    hg hgbound b (right_mem_Icc.mpr hab)
  rw [norm_sub_rev] at hmean
  dsimp [g] at hmean
  simp only [sub_self, Complex.ofReal_zero, zero_mul, sub_zero] at hmean
  have heq :
      f a - ((a - b : ℝ) : ℂ) * f' b - f b =
        f a - f b - ((a - b : ℝ) : ℂ) * f' b := by ring
  rw [heq] at hmean
  simpa [g, pow_two, mul_assoc] using hmean

private lemma hasDerivAt_deriv_LFunction_ofReal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (sigma : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ deriv (DirichletCharacter.LFunction chi) (t : ℂ))
      (iteratedDeriv 2 (DirichletCharacter.LFunction chi) (sigma : ℂ))
      sigma := by
  have hdiff : Differentiable ℂ
      (deriv (DirichletCharacter.LFunction chi)) :=
    (DirichletCharacter.differentiable_LFunction hchi).deriv
  have h := (hdiff (sigma : ℂ)).hasDerivAt.comp_ofReal
  simpa [iteratedDeriv_succ'] using h

/-- A second-derivative version of the near-one Cauchy estimate. -/
theorem norm_iteratedDeriv_two_LFunction_ofReal_near_one_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {sigma : ℝ}
    (hsigmaNear :
      1 - 1 / (4 * Real.log (q : ℝ)) ≤ sigma)
    (hsigmaUpper : sigma ≤ 3 / 2) :
    ‖iteratedDeriv 2 (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
      16384 * (Real.log (q : ℝ)) ^ 3 := by
  let L := Real.log (q : ℝ)
  let r := 1 / (16 * L)
  have hLone : 1 < L := one_lt_log_modulus__m120 chi hchi
  have hLpos : 0 < L := zero_lt_one.trans hLone
  have hrPos : 0 < r := by positivity
  have hrLe : r ≤ 1 / 16 := by
    dsimp [r]
    rw [div_le_iff₀ (by positivity : 0 < 16 * L)]
    nlinarith
  have hsigmaPos : 0 < sigma := by
    have hquarter : 1 / (4 * L) < 1 := by
      rw [div_lt_one (by positivity : 0 < 4 * L)]
      nlinarith
    change 1 - 1 / (4 * L) ≤ sigma at hsigmaNear
    linarith
  have hsphere : ∀ z ∈ sphere (sigma : ℂ) r,
      ‖DirichletCharacter.LFunction chi z‖ ≤ 32 * L := by
    intro z hz
    have hdist : ‖z - (sigma : ℂ)‖ = r := by
      simpa [dist_eq_norm] using mem_sphere.mp hz
    have hreDiff : |z.re - sigma| ≤ r := by
      calc
        |z.re - sigma| = |(z - (sigma : ℂ)).re| := by simp
        _ ≤ ‖z - (sigma : ℂ)‖ := Complex.abs_re_le_norm _
        _ = r := hdist
    have hzRe : 1 - 5 / (16 * L) ≤ z.re := by
      have hrad : r = 1 / (16 * L) := rfl
      rw [hrad] at hreDiff
      have hlower := (abs_le.mp hreDiff).1
      change 1 - 1 / (4 * L) ≤ sigma at hsigmaNear
      have hratio : 1 / (4 * L) = 4 * (1 / (16 * L)) := by
        field_simp [hLpos.ne']
        ring
      rw [hratio] at hsigmaNear
      have hfive : 5 / (16 * L) = 5 * (1 / (16 * L)) := by ring
      rw [hfive]
      linarith
    have hzNorm : ‖z‖ ≤ 2 := by
      calc
        ‖z‖ ≤ ‖(sigma : ℂ)‖ + ‖z - (sigma : ℂ)‖ := by
          simpa [add_comm] using norm_add_le (z - (sigma : ℂ)) (sigma : ℂ)
        _ = sigma + r := by simp [abs_of_pos hsigmaPos, hdist]
        _ ≤ 2 := by linarith
    simpa [L] using norm_LFunction_near_one_le hq chi hchi hzRe hzNorm
  have hCauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    2 hrPos (DirichletCharacter.differentiable_LFunction hchi).diffContOnCl hsphere
  calc
    ‖iteratedDeriv 2 (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
        Nat.factorial 2 * (32 * L) / r ^ 2 := hCauchy
    _ = 16384 * (Real.log (q : ℝ)) ^ 3 := by
      change 2 * (32 * L) / (1 / (16 * L)) ^ 2 = 16384 * L ^ 3
      field_simp [hLpos.ne']
      ring

/-- Positivity of the zeta convolution gives the elementary Euler-product
lower bound needed just to the right of one. -/
theorem one_le_riemannZeta_mul_LFunction_ofReal
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1) {sigma : ℝ} (hsigma : 1 < sigma) :
    (1 : ℂ) ≤ riemannZeta (sigma : ℂ) *
      DirichletCharacter.LFunction chi (sigma : ℂ) := by
  have hsum : LSeriesSummable chi.zetaMul (sigma : ℂ) :=
    chi.LSeriesSummable_zetaMul (by simpa using hsigma)
  have hterm : (1 : ℂ) ≤ LSeries chi.zetaMul (sigma : ℂ) := by
    have hnonneg (n : ℕ) :
        0 ≤ LSeries.term (chi.zetaMul ·) (sigma : ℂ) n :=
      LSeries.term_nonneg (DirichletCharacter.zetaMul_nonneg hsquare n) sigma
    have hone :
        LSeries.term (chi.zetaMul ·) (sigma : ℂ) 1 = (1 : ℂ) := by
      rw [LSeries.term_of_ne_zero one_ne_zero]
      simp [chi.isMultiplicative_zetaMul.map_one]
    calc
      (1 : ℂ) = ∑ n ∈ ({1} : Finset ℕ),
          LSeries.term (chi.zetaMul ·) (sigma : ℂ) n := by
        simp only [Finset.sum_singleton]
        exact hone.symm
      _ ≤ ∑' n : ℕ, LSeries.term (chi.zetaMul ·) (sigma : ℂ) n :=
        hsum.sum_le_tsum ({1} : Finset ℕ) (fun n _ ↦ hnonneg n)
      _ = LSeries chi.zetaMul (sigma : ℂ) := rfl
  calc
    (1 : ℂ) ≤ LSeries chi.zetaMul (sigma : ℂ) := hterm
    _ = riemannZeta (sigma : ℂ) *
        DirichletCharacter.LFunction chi (sigma : ℂ) := by
      rw [DirichletCharacter.zetaMul, ← ArithmeticFunction.coe_mul,
        LSeries_convolution']
      · have hs : 1 < ((sigma : ℂ)).re := by simpa using hsigma
        congr 1
        · simpa only [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
        · rw [DirichletCharacter.LFunction_eq_LSeries chi hs]
          exact (LSeries_congr chi.apply_eq_toArithmeticFunction_apply (sigma : ℂ)).symm
      · exact LSeriesSummable_zeta_iff.mpr (by simpa using hsigma)
      · exact (LSeriesSummable_congr _ fun h ↦
          (chi.apply_eq_toArithmeticFunction_apply h).symm).mpr
            (ZMod.LSeriesSummable_of_one_lt_re chi (by simpa using hsigma))

/-- On the real half-line to the right of one, the continued zeta function
is the usual real Dirichlet series. -/
theorem riemannZeta_ofReal_eq_tsum_rpow
    {sigma : ℝ} (hsigma : 1 < sigma) :
    riemannZeta (sigma : ℂ) =
      ((∑' n : ℕ, (n + 1 : ℝ) ^ (-sigma) : ℝ) : ℂ) := by
  calc
    riemannZeta (sigma : ℂ) =
        ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (sigma : ℂ) :=
      zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hsigma)
    _ = ∑' n : ℕ, (((n + 1 : ℝ) ^ (-sigma) : ℝ) : ℂ) := by
      apply tsum_congr
      intro n
      have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      have hcpow :
          ((((n : ℝ) + 1) ^ sigma : ℝ) : ℂ) =
            (((n : ℝ) + 1 : ℝ) : ℂ) ^ (sigma : ℂ) :=
        @Complex.ofReal_cpow ((n : ℝ) + 1) hn sigma
      rw [@Real.rpow_neg ((n : ℝ) + 1) hn sigma]
      calc
        1 / ((n : ℂ) + 1) ^ (sigma : ℂ) =
            ((((n : ℝ) + 1) ^ sigma : ℝ) : ℂ)⁻¹ := by
          rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by norm_num,
            ← hcpow, one_div]
        _ = (((((n : ℝ) + 1) ^ sigma)⁻¹ : ℝ) : ℂ) :=
          (Complex.ofReal_inv _).symm
    _ = ((∑' n : ℕ, (n + 1 : ℝ) ^ (-sigma) : ℝ) : ℂ) :=
      (Complex.ofReal_tsum _).symm

/-- The elementary integral-test bound `zeta(sigma) ≤ 1 + 1/(sigma-1)`. -/
theorem riemannZeta_ofReal_le_one_add_inv_sub_one
    {sigma : ℝ} (hsigma : 1 < sigma) :
    riemannZeta (sigma : ℂ) ≤
      (((1 + 1 / (sigma - 1) : ℝ) : ℂ)) := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-sigma)
  have hanti : AntitoneOn f (Ici (1 : ℝ)) := by
    intro a ha b hb hab
    change 1 ≤ a at ha
    change 1 ≤ b at hb
    dsimp [f]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hab (by linarith)
  have hint : IntegrableOn f (Ioi (1 : ℝ)) := by
    dsimp [f]
    exact integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hnonneg : ∀ x ∈ Ioi (1 : ℝ), 0 ≤ f x := by
    intro x hx
    change 1 < x at hx
    dsimp [f]
    exact Real.rpow_nonneg (by linarith) _
  have hanti' : AntitoneOn f (Ici ((1 : ℕ) : ℝ)) := by
    simpa using hanti
  have hint' : IntegrableOn f (Ioi ((1 : ℕ) : ℝ)) := by
    simpa using hint
  have hnonneg' : ∀ x ∈ Ioi ((1 : ℕ) : ℝ), 0 ≤ f x := by
    simpa using hnonneg
  have htail := AntitoneOn.tsum_comp_add_le_integral
    (f := f) 1 hanti' hint' hnonneg'
  norm_num at htail
  have hintegral : ∫ x in Ioi (1 : ℝ), f x = 1 / (sigma - 1) := by
    dsimp [f]
    rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    rw [Real.one_rpow]
    have hleft : -sigma + 1 ≠ 0 := by linarith
    have hright : sigma - 1 ≠ 0 := by linarith
    field_simp [hleft, hright]
    ring
  rw [hintegral] at htail
  have hsummable : Summable (fun n : ℕ ↦
      (n + 1 : ℝ) ^ (-sigma)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((_root_.summable_nat_add_iff 1).mpr
        (Real.summable_nat_rpow.mpr (by linarith : -sigma < -1)))
  have hreal :
      (∑' n : ℕ, (n + 1 : ℝ) ^ (-sigma)) ≤
        1 + 1 / (sigma - 1) := by
    rw [hsummable.tsum_eq_zero_add]
    simpa [f, add_assoc, Nat.cast_add, Nat.cast_one,
      Real.rpow_neg, one_div] using add_le_add_left htail 1
  rw [riemannZeta_ofReal_eq_tsum_rpow hsigma]
  exact_mod_cast hreal

/-- The same Dirichlet series is at least its first term. -/
theorem one_le_riemannZeta_ofReal
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (1 : ℂ) ≤ riemannZeta (sigma : ℂ) := by
  have hsummable : Summable (fun n : ℕ ↦
      (n + 1 : ℝ) ^ (-sigma)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((_root_.summable_nat_add_iff 1).mpr
        (Real.summable_nat_rpow.mpr (by linarith : -sigma < -1)))
  have htail : 0 ≤ ∑' n : ℕ, (((n : ℝ) + 1) + 1) ^ (-sigma) :=
    tsum_nonneg fun _ ↦ Real.rpow_nonneg (by positivity) _
  rw [riemannZeta_ofReal_eq_tsum_rpow hsigma]
  apply Complex.le_def.mpr
  constructor
  · change (1 : ℝ) ≤ ∑' n : ℕ, (n + 1 : ℝ) ^ (-sigma)
    rw [hsummable.tsum_eq_zero_add]
    norm_num
    exact htail
  · simp

/-- Positivity of the quadratic zeta convolution and the elementary zeta
upper bound imply the useful lower bound `L(sigma, chi) ≥ (sigma-1)/sigma`. -/
theorem sub_one_div_self_le_LFunction_ofReal
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1) {sigma : ℝ} (hsigma : 1 < sigma) :
    ((((sigma - 1) / sigma : ℝ) : ℂ)) ≤
      DirichletCharacter.LFunction chi (sigma : ℂ) := by
  let Z := riemannZeta (sigma : ℂ)
  let V := DirichletCharacter.LFunction chi (sigma : ℂ)
  have hprod : (1 : ℂ) ≤ Z * V := by
    simpa [Z, V] using
      one_le_riemannZeta_mul_LFunction_ofReal chi hchi hsquare hsigma
  have hZupper : Z ≤ (((1 + 1 / (sigma - 1) : ℝ) : ℂ)) := by
    simpa [Z] using riemannZeta_ofReal_le_one_add_inv_sub_one hsigma
  have hZlower : (1 : ℂ) ≤ Z := by
    simpa [Z] using one_le_riemannZeta_ofReal hsigma
  have hZim : Z.im = 0 := by
    simpa using (Complex.le_def.mp hZlower).2.symm
  have hVim : V.im = 0 := by
    have hconj := LFunction_conj_of_sq_eq_one chi hchi hsquare (sigma : ℂ)
    apply Complex.conj_eq_iff_im.mp
    simpa [V] using hconj.symm
  have hprodRe : 1 ≤ Z.re * V.re := by
    have h := (Complex.le_def.mp hprod).1
    simpa [Complex.mul_re, hZim, hVim] using h
  have hZupperRe : Z.re ≤ 1 + 1 / (sigma - 1) := by
    have h := (Complex.le_def.mp hZupper).1
    change Z.re ≤ 1 + 1 / (sigma - 1) at h
    exact h
  have hZlowerRe : 1 ≤ Z.re := by
    simpa using (Complex.le_def.mp hZlower).1
  have hZpos : 0 < Z.re := zero_lt_one.trans_le hZlowerRe
  have hrecipZ : 1 / Z.re ≤ V.re := by
    apply (div_le_iff₀ hZpos).mpr
    simpa [one_div, mul_comm] using hprodRe
  have hrecipUpper :
      1 / (1 + 1 / (sigma - 1)) ≤ 1 / Z.re :=
    one_div_le_one_div_of_le hZpos hZupperRe
  have hsigmaPos : 0 < sigma := by linarith
  have hsubPos : 0 < sigma - 1 := by linarith
  have hid : 1 / (1 + 1 / (sigma - 1)) = (sigma - 1) / sigma := by
    field_simp [hsigmaPos.ne', hsubPos.ne']
    ring
  apply Complex.le_def.mpr
  constructor
  · change (sigma - 1) / sigma ≤ V.re
    rw [← hid]
    exact hrecipUpper.trans hrecipZ
  · simpa [V] using hVim.symm

/-- If a real quadratic `L`-value at one were smaller than a fixed negative
power of its logarithmic conductor, Taylor's theorem would force a real zero
in a very short interval immediately to the left of one. -/
theorem exists_real_zero_of_LFunction_one_re_lt
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1)
    (hsmall :
      (DirichletCharacter.LFunction chi (1 : ℂ)).re <
        1 / ((2 ^ 24 : ℝ) * (Real.log (q : ℝ)) ^ 3)) :
    ∃ beta : ℝ,
      1 - 8 * (DirichletCharacter.LFunction chi (1 : ℂ)).re ≤ beta ∧
      beta ≤ 1 ∧
      DirichletCharacter.LFunction chi (beta : ℂ) = 0 := by
  let L := Real.log (q : ℝ)
  let ell := (DirichletCharacter.LFunction chi (1 : ℂ)).re
  let delta := 8 * ell
  let M := 16384 * L ^ 3
  let F : ℝ → ℂ := fun sigma ↦
    DirichletCharacter.LFunction chi (sigma : ℂ)
  let F' : ℝ → ℂ := fun sigma ↦
    deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)
  let F'' : ℝ → ℂ := fun sigma ↦
    iteratedDeriv 2 (DirichletCharacter.LFunction chi) (sigma : ℂ)
  have hLone : 1 < L := one_lt_log_modulus__m120 chi hchi
  have hLpos : 0 < L := zero_lt_one.trans hLone
  have hellPos : 0 < ell := by
    have heff := effectiveQuadraticLValueLowerBound hq chi hchi hsquare
    have heffRe := (Complex.le_def.mp heff).1
    have hbasePos : 0 <
        1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2) := by
      positivity
    change 1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2) ≤ ell at heffRe
    exact hbasePos.trans_le heffRe
  have hdeltaPos : 0 < delta := by
    dsimp [delta]
    positivity
  have hdenomPos : 0 < (2 ^ 24 : ℝ) * L ^ 3 := by positivity
  have hscaled : (2 ^ 24 : ℝ) * L ^ 3 * ell < 1 := by
    have hs : ell * ((2 ^ 24 : ℝ) * L ^ 3) < 1 := by
      apply (lt_div_iff₀ hdenomPos).mp
      simpa [L, ell] using hsmall
    simpa [mul_comm] using hs
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hdeltaNear : delta ≤ 1 / (4 * L) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * L)).mpr
    have hbase : 0 ≤ L * ell := mul_nonneg hLpos.le hellPos.le
    have hcomparison :
        32 * L * ell ≤ (2 ^ 24 : ℝ) * L ^ 3 * ell := by
      calc
        32 * L * ell ≤ (2 ^ 24 : ℝ) * (L * ell) := by
          nlinarith
        _ ≤ (2 ^ 24 : ℝ) * (L ^ 2 * (L * ell)) := by
          gcongr <;> nlinarith
        _ = (2 ^ 24 : ℝ) * L ^ 3 * ell := by ring
    dsimp [delta]
    convert hcomparison.trans hscaled.le using 1 <;> ring
  have hdeltaHalf : delta ≤ 1 / 2 := by
    have hquarter : 1 / (4 * L) < 1 / 2 := by
      rw [div_lt_iff₀ (by positivity : 0 < 4 * L)]
      nlinarith
    exact hdeltaNear.trans hquarter.le
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have herror : 2 * M * delta ^ 2 < ell := by
    dsimp [M, delta]
    nlinarith
  have hrightRem :
      ‖F (1 + delta) - F 1 - (delta : ℂ) * F' 1‖ ≤
        M * delta ^ 2 := by
    have hraw := norm_first_order_remainder_right_le
        (a := (1 : ℝ)) (b := 1 + delta) (M := M)
        (f := F) (f' := F') (f'' := F'')
        (by linarith) hMnonneg
        (by
          intro sigma _
          dsimp [F, F']
          exact ((DirichletCharacter.differentiable_LFunction hchi
            (sigma : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt)
        (by
          intro sigma _
          dsimp [F', F'']
          exact (hasDerivAt_deriv_LFunction_ofReal chi hchi sigma).hasDerivWithinAt)
        (by
          intro sigma hsigma
          dsimp [F'']
          apply norm_iteratedDeriv_two_LFunction_ofReal_near_one_le
            hq chi hchi
          · have hfrac : 0 < 1 / (4 * L) := by positivity
            have : 1 - 1 / (4 * L) < 1 := by linarith
            change 1 - 1 / (4 * L) ≤ sigma
            exact this.le.trans hsigma.1
          · change sigma ≤ 3 / 2
            linarith [hsigma.2, hdeltaHalf])
    simpa using hraw
  have hleftRem :
      ‖F (1 - delta) - F 1 - ((-delta : ℝ) : ℂ) * F' 1‖ ≤
        M * delta ^ 2 := by
    have hraw := norm_first_order_remainder_left_le
      (a := 1 - delta) (b := (1 : ℝ)) (M := M)
      (f := F) (f' := F') (f'' := F'')
      (by linarith : 1 - delta ≤ (1 : ℝ)) hMnonneg
      (by
        intro sigma _
        dsimp [F, F']
        exact ((DirichletCharacter.differentiable_LFunction hchi
          (sigma : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt)
      (by
        intro sigma _
        dsimp [F', F'']
        exact (hasDerivAt_deriv_LFunction_ofReal chi hchi sigma).hasDerivWithinAt)
      (by
        intro sigma hsigma
        dsimp [F'']
        apply norm_iteratedDeriv_two_LFunction_ofReal_near_one_le
          hq chi hchi
        · change 1 - 1 / (4 * L) ≤ sigma
          linarith [hsigma.1, hdeltaNear]
        · change sigma ≤ 3 / 2
          linarith [hsigma.2])
    simpa using hraw
  have hrightLower : 4 * ell ≤ (F (1 + delta)).re := by
    have hcomplex := sub_one_div_self_le_LFunction_ofReal
      chi hchi hsquare (sigma := 1 + delta) (by linarith)
    have hre := (Complex.le_def.mp hcomplex).1
    have hratio : 4 * ell ≤ delta / (1 + delta) := by
      apply (le_div_iff₀ (by linarith : 0 < 1 + delta)).mpr
      dsimp [delta]
      nlinarith [hdeltaHalf]
    norm_num only [Complex.ofReal_re] at hre
    change ((1 + delta - 1) / (1 + delta) : ℝ) ≤
      (F (1 + delta)).re at hre
    have hre' : (delta / (1 + delta) : ℝ) ≤
        (F (1 + delta)).re := by
      convert hre using 1 <;> ring
    exact hratio.trans hre'
  have hrightError :
      (F (1 + delta)).re - ell - delta * (F' 1).re ≤
        M * delta ^ 2 := by
    have h := (Complex.abs_re_le_norm
      (F (1 + delta) - F 1 - (delta : ℂ) * F' 1)).trans hrightRem
    have hupper := (abs_le.mp h).2
    simpa [F, ell] using hupper
  have hleftError :
      (F (1 - delta)).re - ell + delta * (F' 1).re ≤
        M * delta ^ 2 := by
    have h := (Complex.abs_re_le_norm
      (F (1 - delta) - F 1 - ((-delta : ℝ) : ℂ) * F' 1)).trans hleftRem
    have hupper := (abs_le.mp h).2
    calc
      (F (1 - delta)).re - ell + delta * (F' 1).re =
          (F (1 - delta) - F 1 - ((-delta : ℝ) : ℂ) * F' 1).re := by
        simp [F, ell]
      _ ≤ M * delta ^ 2 := hupper
  have hleftNeg : (F (1 - delta)).re < 0 := by
    nlinarith
  let g : ℝ → ℝ := fun sigma ↦ (F sigma).re
  have hgContinuous : Continuous g := by
    dsimp [g, F]
    exact Complex.continuous_re.comp
      ((DirichletCharacter.differentiable_LFunction hchi).continuous.comp
        Complex.continuous_ofReal)
  have hzeroMem : (0 : ℝ) ∈ Icc (g (1 - delta)) (g 1) := by
    constructor
    · simpa [g] using hleftNeg.le
    · change 0 ≤ ell
      exact hellPos.le
  obtain ⟨beta, hbetaMem, hbetaZero⟩ :=
    intermediate_value_Icc (by linarith : 1 - delta ≤ (1 : ℝ))
      hgContinuous.continuousOn hzeroMem
  refine ⟨beta, ?_, hbetaMem.2, ?_⟩
  · simpa [delta, ell] using hbetaMem.1
  · have hreal : (F beta).re = 0 := by
      simpa [g] using hbetaZero
    have himag : (F beta).im = 0 := by
      have hconj := LFunction_conj_of_sq_eq_one chi hchi hsquare (beta : ℂ)
      apply Complex.conj_eq_iff_im.mp
      simpa [F] using hconj.symm
    apply Complex.ext
    · simpa [F] using hreal
    · simpa [F] using himag

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/SiegelLowerBound.lean` -/

section

/-!
# Siegel's lower bound with an arbitrary positive exponent
-/

namespace Pollack17

open Filter
open BoundedGaps.Maynard

theorem eventually_rpow_neg_le_log_threshold {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop,
      (q : ℝ) ^ (-δ) ≤ 1 / ((2 ^ 24 : ℝ) * (Real.log (q : ℝ)) ^ 3) := by
  have hlittle := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) hδ).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound := hlittle.bound (show (0 : ℝ) < 1 / (2 ^ 24 : ℝ) by positivity)
  filter_upwards [hbound, eventually_ge_atTop 3] with q hbound hq
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith)
  have hpow : 0 < (q : ℝ) ^ δ := Real.rpow_pos_of_pos hq0 _
  simp only [Function.comp_apply, Real.norm_eq_abs] at hbound
  rw [abs_of_pos (Real.rpow_pos_of_pos hlog _), abs_of_pos hpow] at hbound
  have hlogpow : Real.log (q : ℝ) ^ (3 : ℝ) = Real.log (q : ℝ) ^ (3 : ℕ) := by
    norm_num [Real.rpow_natCast]
  rw [hlogpow] at hbound
  have hdom : (2 ^ 24 : ℝ) * Real.log (q : ℝ) ^ 3 ≤ (q : ℝ) ^ δ := by
    nlinarith only [hbound]
  have hrecip := one_div_le_one_div_of_le
    (by positivity : 0 < (2 ^ 24 : ℝ) * Real.log (q : ℝ) ^ 3) hdom
  simpa only [Real.rpow_neg hq0.le, one_div] using hrecip

theorem eventually_quadratic_LFunction_one_re_ge_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop,
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ.IsQuadratic →
        (q : ℝ) ^ (-δ) ≤ (DirichletCharacter.LFunction χ (1 : ℂ)).re := by
  obtain ⟨c, hc, hzeroFree⟩ := exists_siegelRealCharacterZeroFree (δ / 2) (half_pos hδ)
  have hpowTendsto : Tendsto (fun q : ℕ => (q : ℝ) ^ (-(δ / 2))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (half_pos hδ)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := hpowTendsto.eventually (eventually_lt_nhds (show 0 < c / 8 by positivity))
  filter_upwards [eventually_rpow_neg_le_log_threshold hδ, hsmall, eventually_gt_atTop 1]
    with q hlog hsmall hq
  intro _ χ hχ1 hχ
  by_contra hnot
  have hv : (DirichletCharacter.LFunction χ (1 : ℂ)).re < (q : ℝ) ^ (-δ) := lt_of_not_ge hnot
  obtain ⟨β, hβlower, _hβupper, hβzero⟩ :=
    exists_real_zero_of_LFunction_one_re_lt hq χ hχ1 hχ.sq_eq_one (hv.trans_le hlog)
  have hq0 : (0 : ℝ) < q := by positivity
  have hsq : (q : ℝ) ^ (-δ) = ((q : ℝ) ^ (-(δ / 2))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    congr 1
    ring
  have ha : 0 < (q : ℝ) ^ (-(δ / 2)) := Real.rpow_pos_of_pos hq0 _
  have hgap : 8 * (DirichletCharacter.LFunction χ (1 : ℂ)).re < c * (q : ℝ) ^ (-(δ / 2)) := by
    rw [hsq] at hv
    nlinarith only [hv, hsmall, ha]
  have hβ : 1 - c * (q : ℝ) ^ (-(δ / 2)) < β := by linarith only [hgap, hβlower]
  exact (hzeroFree q χ hχ1 hχ.sq_eq_one β hβ) hβzero

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/CharacterLValueApproximation.lean` -/

section

/-!
# Approximating the real L-value by a reciprocal prefix
-/

namespace Pollack17

open Filter
open scoped BigOperators
open BoundedGaps.Maynard

theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, f i) = ∑ i ∈ Finset.range n, f (1 + i) := by
  have heq : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by ext i; simp
  rw [heq, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm]

theorem sum_range_succ_eq_zero_add_Icc (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), f i) = f 0 + ∑ i ∈ Finset.Icc 1 n, f i := by
  rw [sum_Icc_one_eq_sum_range, Finset.sum_range_succ']
  simp only [add_comm]

theorem eventually_quadratic_prefix_bound {d : ℝ} (hd : 1 / 4 < d) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ (χ : DirichletCharacter ℂ m), χ.IsQuadratic → χ ≠ 1 →
        ∀ n : ℕ, (m : ℝ) ^ d ≤ n →
          |∑ i ∈ Finset.Icc 1 n, (χ (i : ℕ)).re| ≤ (n : ℝ) * (m : ℝ) ^ (-σ) := by
  obtain ⟨σ, hσ, h⟩ := Burgess.eventually_quadratic_burgess hd
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [h] with m hm
  intro χ hχ hχ1 n hn
  rw [sum_Icc_one_eq_sum_range]
  exact hm χ hχ hχ1 1 n hn

theorem reciprocal_prefix_re {m : ℕ} (χ : DirichletCharacter ℂ m) (y : ℕ) :
    (∑ i ∈ Finset.Icc 1 y, χ (i : ℕ) / (i : ℂ)).re =
      ∑ i ∈ Finset.Icc 1 y, (χ (i : ℕ)).re / (i : ℝ) := by
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.div_natCast_re]

theorem abs_reciprocal_prefix_sub_LFunction_re_le {m : ℕ} [NeZero m]
    (hm : 1 < m) (χ : DirichletCharacter ℂ m) (hχ1 : χ ≠ 1)
    {x y : ℕ} (hx : 0 < x) (hxy : x ≤ y) {b : ℝ} (hb : 0 ≤ b)
    (hprefix : ∀ n : ℕ, x ≤ n → n ≤ y →
      |∑ i ∈ Finset.Icc 1 n, (χ (i : ℕ)).re| ≤ (n : ℝ) * b) :
    |(∑ i ∈ Finset.Icc 1 x, (χ (i : ℕ)).re / (i : ℝ)) -
        (DirichletCharacter.LFunction χ (1 : ℂ)).re| ≤
      b * (3 + Real.log (y : ℝ)) +
        4 * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / (y : ℝ) := by
  let P : ℕ → ℝ := fun n => ∑ i ∈ Finset.Icc 1 n, (χ (i : ℕ)).re / (i : ℝ)
  have hzero : (χ ((0 : ℕ) : ZMod m)).re = 0 := by
    rw [Nat.cast_zero, χ.map_zero' (by omega), Complex.zero_re]
  have hfinite := abs_reciprocal_interval_le (fun i => (χ (i : ℕ)).re) hx hxy hb
    (fun n hn hny => by rw [sum_range_succ_eq_zero_add_Icc, hzero, zero_add]; exact hprefix n hn hny)
  have hdiff : P y - P x = ∑ i ∈ Finset.Ioc x y, (χ (i : ℕ)).re / (i : ℝ) := by
    dsimp only [P]
    rw [show Finset.Icc 1 y = Finset.Ioc 0 y by ext i; simp; omega,
      show Finset.Icc 1 x = Finset.Ioc 0 x by ext i; simp; omega,
      ← Finset.sum_Ioc_consecutive (fun i => (χ (i : ℕ)).re / (i : ℝ)) (Nat.zero_le x) hxy]
    ring
  have htail := (Complex.abs_re_le_norm (DirichletCharacter.LFunction χ (1 : ℂ) -
      ∑ i ∈ Finset.Icc 1 y, χ (i : ℕ) / (i : ℂ))).trans
    (norm_LFunction_one_sub_dirichletCharacterReciprocalPrefix_le hm χ hχ1 y (hx.trans_le hxy))
  rw [Complex.sub_re, reciprocal_prefix_re] at htail
  change |P x - (DirichletCharacter.LFunction χ 1).re| ≤ _
  have htri := abs_sub_le (P x) (P y) (DirichletCharacter.LFunction χ 1).re
  rw [abs_sub_comm (P x) (P y), hdiff] at htri
  have htail' : |P y - (DirichletCharacter.LFunction χ 1).re| ≤
      4 * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / (y : ℝ) := by
    rw [abs_sub_comm]
    exact htail
  exact htri.trans (add_le_add hfinite htail')

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/DivisorLValueComparison.lean` -/

section

/-!
# Finite comparison of the divisor sum with its L-value main term
-/

namespace Pollack17

open scoped BigOperators

theorem divisorCoefficient_eq_sum {m : ℕ} (χ : DirichletCharacter ℂ m) (n : ℕ) :
    divisorCoefficient χ n = ∑ d ∈ n.divisors, (χ (d : ℕ)).re := by
  unfold divisorCoefficient
  have heq : χ.zetaMul n = ∑ d ∈ n.divisors, χ (d : ℕ) := by
    change (ArithmeticFunction.zeta * toArithmeticFunction (χ ·)) n = _
    rw [ArithmeticFunction.coe_zeta_mul_apply]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [toArithmeticFunction, ArithmeticFunction.coe_mk,
      if_neg (Nat.pos_of_mem_divisors hd).ne']
  rw [heq, Complex.re_sum]

theorem abs_divisor_sum_sub_LFunction_main_le {m X Y R : ℕ} [NeZero m]
    (hm : 1 < m) (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) (hχ1 : χ ≠ 1)
    (hY : 0 < Y) (hYX : Y ≤ X) (hYR : Y ≤ R) {b : ℝ} (hb : 0 ≤ b)
    (hprefix : ∀ n : ℕ, Y ≤ n →
      |∑ d ∈ Finset.Icc 1 n, (χ (d : ℕ)).re| ≤ (n : ℝ) * b) :
    |(∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n) -
        (X : ℝ) * (DirichletCharacter.LFunction χ 1).re| ≤
      (Y : ℝ) + (X : ℝ) * b * (5 + 2 * Real.log (X : ℝ) + Real.log (R : ℝ)) +
        4 * (X : ℝ) * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / (R : ℝ) := by
  have hf (n : ℕ) : |(χ (n : ℕ)).re| ≤ 1 := by
    rcases hχ (n : ℕ) with h | h | h <;> rw [h] <;> norm_num
  have hhyp := abs_divisor_sum_sub_truncated_main_le (fun n => (χ (n : ℕ)).re)
    hf hY hYX hb hprefix
  have htail := abs_reciprocal_prefix_sub_LFunction_re_le hm χ hχ1 hY hYR hb
    (fun n hn _ => hprefix n hn)
  simp_rw [← divisorCoefficient_eq_sum χ] at hhyp
  let P : ℝ := ∑ d ∈ Finset.Icc 1 Y, (χ (d : ℕ)).re / (d : ℝ)
  let L : ℝ := (DirichletCharacter.LFunction χ 1).re
  let S : ℝ := ∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n
  have htri := abs_sub_le S ((X : ℝ) * P) ((X : ℝ) * L)
  have hscaled : |(X : ℝ) * P - (X : ℝ) * L| ≤
      (X : ℝ) * (b * (3 + Real.log (R : ℝ)) +
        4 * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / (R : ℝ)) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg X)]
    exact mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg X)
  change |S - (X : ℝ) * L| ≤ _
  calc
    _ ≤ ((Y : ℝ) + 2 * (X : ℝ) * b * (1 + Real.log (X : ℝ))) +
        (X : ℝ) * (b * (3 + Real.log (R : ℝ)) +
          4 * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / (R : ℝ)) :=
      htri.trans (add_le_add hhyp hscaled)
    _ = _ := by ring

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/DivisorErrorScales.lean` -/

section

/-!
# Absorbing the three hyperbola error terms
-/

namespace Pollack17

open Filter

theorem eventually_three_power_errors_le {c a b d C D E : ℝ}
    (ha : a < c) (hb : b < c) (hd : d < c) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ m : ℕ in atTop,
      C * (m : ℝ) ^ a + D * (m : ℝ) ^ b + E * (m : ℝ) ^ d ≤ (m : ℝ) ^ (c - τ) := by
  let τ : ℝ := min (c - a) (min (c - b) (c - d)) / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτa : a < c - τ := by
    have h := min_le_left (c - a) (min (c - b) (c - d))
    dsimp [τ] at hτ ⊢
    linarith
  have hτb : b < c - τ := by
    have h := (min_le_right (c - a) (min (c - b) (c - d))).trans (min_le_left _ _)
    dsimp [τ] at hτ ⊢
    linarith
  have hτd : d < c - τ := by
    have h := (min_le_right (c - a) (min (c - b) (c - d))).trans (min_le_right _ _)
    dsimp [τ] at hτ ⊢
    linarith
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [Burgess.eventually_const_mul_rpow_le (C := C) (d := 1 / 3) (by norm_num) hτa,
    Burgess.eventually_const_mul_rpow_le (C := D) (d := 1 / 3) (by norm_num) hτb,
    Burgess.eventually_const_mul_rpow_le (C := E) (d := 1 / 3) (by norm_num) hτd]
    with m hm₁ hm₂ hm₃
  linarith only [hm₁, hm₂, hm₃]

theorem eventually_divisor_error_le {c a σ : ℝ} (hc : 0 < c) (ha : a < c) (hσ : 0 < σ) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ m : ℕ in atTop,
      2 * (m : ℝ) ^ a + (7 + 2 * c) * (m : ℝ) ^ (c - σ) * (1 + Real.log (m : ℝ)) +
        4 * (m : ℝ) ^ (c - 3 / 2) * (1 + Real.log (m : ℝ)) ≤ (m : ℝ) ^ (c - τ) := by
  let κ : ℝ := min σ 1 / 4
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκσ : κ < σ := by
    have h := min_le_left σ 1
    dsimp [κ] at hκ ⊢
    linarith
  have hκ1 : κ < 3 / 2 := by
    have h := min_le_right σ 1
    dsimp [κ]
    linarith
  obtain ⟨τ, hτ, h⟩ := eventually_three_power_errors_le
    (C := 2) (D := 7 + 2 * c) (E := 4) ha
    (show c - σ + κ < c by linarith) (show c - 3 / 2 + κ < c by linarith)
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [h, Burgess.eventually_one_add_log_le_rpow hκ, eventually_ge_atTop 1]
    with m hm hlog hm1
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm1
  have hfirst : (7 + 2 * c) * (m : ℝ) ^ (c - σ) * (1 + Real.log (m : ℝ)) ≤
      (7 + 2 * c) * (m : ℝ) ^ (c - σ + κ) := by
    rw [Real.rpow_add hm0, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  have hsecond : 4 * (m : ℝ) ^ (c - 3 / 2) * (1 + Real.log (m : ℝ)) ≤
      4 * (m : ℝ) ^ (c - 3 / 2 + κ) := by
    rw [Real.rpow_add hm0, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  exact (add_le_add (add_le_add le_rfl hfirst) hsecond).trans hm

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/DivisorComparisonAsymptotics.lean` -/

section

/-!
# The divisor-sum asymptotic above the quarter-power scale
-/

namespace Pollack17

open Filter
open scoped BigOperators

theorem divisor_comparison_error_le_scales {m X Y : ℕ} (hm : 1 ≤ m) (hX : 0 < X)
    {c a σ : ℝ} (hc : 0 < c) (hXu : (X : ℝ) ≤ (m : ℝ) ^ c)
    (hYu : (Y : ℝ) ≤ 2 * (m : ℝ) ^ a) :
    (Y : ℝ) + (X : ℝ) * (m : ℝ) ^ (-σ) *
        (5 + 2 * Real.log (X : ℝ) + Real.log ((m ^ 2 : ℕ) : ℝ)) +
      4 * (X : ℝ) * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / ((m ^ 2 : ℕ) : ℝ) ≤
    2 * (m : ℝ) ^ a + (7 + 2 * c) * (m : ℝ) ^ (c - σ) * (1 + Real.log (m : ℝ)) +
      4 * (m : ℝ) ^ (c - 3 / 2) * (1 + Real.log (m : ℝ)) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hXm : 0 < (X : ℝ) := by exact_mod_cast hX
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hlogXu : Real.log (X : ℝ) ≤ c * Real.log (m : ℝ) := by
    have h := Real.log_le_log hXm hXu
    simpa only [Real.log_rpow hmR] using h
  have hlogR : Real.log ((m ^ 2 : ℕ) : ℝ) = 2 * Real.log (m : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hfactor : 5 + 2 * Real.log (X : ℝ) + Real.log ((m ^ 2 : ℕ) : ℝ) ≤
      (7 + 2 * c) * (1 + Real.log (m : ℝ)) := by
    rw [hlogR]
    nlinarith only [hlogXu, hlogm, hc]
  have hfirst : (X : ℝ) * (m : ℝ) ^ (-σ) *
        (5 + 2 * Real.log (X : ℝ) + Real.log ((m ^ 2 : ℕ) : ℝ)) ≤
      (7 + 2 * c) * (m : ℝ) ^ (c - σ) * (1 + Real.log (m : ℝ)) := by
    have hxpow : (X : ℝ) * (m : ℝ) ^ (-σ) ≤ (m : ℝ) ^ (c - σ) := by
      rw [sub_eq_add_neg, Real.rpow_add hmR]
      exact mul_le_mul_of_nonneg_right hXu (Real.rpow_nonneg hmR.le _)
    have hfac0 : 0 ≤ 5 + 2 * Real.log (X : ℝ) + Real.log ((m ^ 2 : ℕ) : ℝ) := by
      rw [hlogR]
      positivity
    calc
      _ ≤ (m : ℝ) ^ (c - σ) * ((7 + 2 * c) * (1 + Real.log (m : ℝ))) :=
        mul_le_mul hxpow hfactor hfac0 (Real.rpow_nonneg hmR.le _)
      _ = _ := by ring
  have hratio : (m : ℝ) ^ c * Real.sqrt (m : ℝ) / ((m ^ 2 : ℕ) : ℝ) =
      (m : ℝ) ^ (c - 3 / 2) := by
    rw [Nat.cast_pow, Real.sqrt_eq_rpow, ← Real.rpow_add hmR,
      ← Real.rpow_natCast, ← Real.rpow_sub hmR]
    congr 1
    ring
  have hsecond : 4 * (X : ℝ) * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / ((m ^ 2 : ℕ) : ℝ) ≤
      4 * (m : ℝ) ^ (c - 3 / 2) * (1 + Real.log (m : ℝ)) := by
    calc
      _ ≤ 4 * (m : ℝ) ^ c * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / ((m ^ 2 : ℕ) : ℝ) := by
        gcongr
      _ = 4 * (m : ℝ) ^ (c - 3 / 2) * Real.log (m : ℝ) := by
        rw [← hratio]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  exact add_le_add (add_le_add hYu hfirst) hsecond

theorem eventually_divisor_sum_asymptotic {c : ℝ} (hc : 1 / 4 < c) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ [NeZero m] (χ : DirichletCharacter ℂ m), χ.IsQuadratic → χ ≠ 1 →
        |(∑ n ∈ Finset.Icc 1 ⌊(m : ℝ) ^ c⌋₊, divisorCoefficient χ n) -
          (⌊(m : ℝ) ^ c⌋₊ : ℝ) * (DirichletCharacter.LFunction χ 1).re| ≤ (m : ℝ) ^ (c - τ) := by
  let a : ℝ := min ((c + 1 / 4) / 2) (1 / 2)
  have ha : 1 / 4 < a := by dsimp [a]; exact lt_min (by linarith) (by norm_num)
  have hac : a < c := (min_le_left _ _).trans_lt (by linarith)
  have ha2 : a < 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hc0 : 0 < c := by linarith
  have ha0 : 0 < a := by linarith
  obtain ⟨σ, hσ, hprefix⟩ := eventually_quadratic_prefix_bound ha
  obtain ⟨τ, hτ, herror⟩ := eventually_divisor_error_le hc0 hac hσ
  have hYX := Burgess.eventually_const_mul_rpow_le (C := 2) (d := 1 / 2) (by norm_num) hac
  have hYR := Burgess.eventually_const_mul_rpow_le (C := 2) (d := 1) (by norm_num) ha2
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [hprefix, herror, hYX, hYR, Burgess.eventually_floor_rpow_bounds hc0,
    eventually_ge_atTop 2] with m hpref herr hYX hYR hfloor hm
  intro _ χ hχ hχ1
  have hm0 : 0 < m := by omega
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  let X := ⌊(m : ℝ) ^ c⌋₊
  let Y := ⌈(m : ℝ) ^ a⌉₊
  have hceil := Burgess.ceil_rpow_bounds ha0.le (show 1 ≤ m by omega)
  have hXpos : 0 < X := by
    have h : (0 : ℝ) < X := lt_of_lt_of_le (by positivity) hfloor.1
    exact_mod_cast h
  have hYpos : 0 < Y := by
    have h : (0 : ℝ) < Y := lt_of_lt_of_le (Real.rpow_pos_of_pos hmR a) hceil.1
    exact_mod_cast h
  have hYX' : Y ≤ X := by
    have hmid : 2 * (m : ℝ) ^ a ≤ (m : ℝ) ^ c / 2 := by
      nlinarith only [hYX]
    have h : (Y : ℝ) ≤ X := hceil.2.trans (hmid.trans hfloor.1)
    exact_mod_cast h
  have hYR' : Y ≤ m ^ 2 := by
    have h : (Y : ℝ) ≤ ((m ^ 2 : ℕ) : ℝ) := by
      have h := hceil.2.trans hYR
      simpa only [one_mul, Real.rpow_two, Nat.cast_pow] using h
    exact_mod_cast h
  have hb : 0 ≤ (m : ℝ) ^ (-σ) := Real.rpow_nonneg hmR.le _
  have hbound (n : ℕ) (hn : Y ≤ n) :
      |∑ d ∈ Finset.Icc 1 n, (χ (d : ℕ)).re| ≤ (n : ℝ) * (m : ℝ) ^ (-σ) :=
    hpref χ hχ hχ1 n (hceil.1.trans (by exact_mod_cast hn))
  have hcomp := abs_divisor_sum_sub_LFunction_main_le (by omega) χ hχ hχ1 hYpos hYX' hYR' hb hbound
  exact (hcomp.trans (divisor_comparison_error_le_scales (by omega) hXpos hc0 hfloor.2 hceil.2)).trans herr

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/DivisorSumLowerBound.lean` -/

section

/-!
# Uniform lower bounds for the quadratic divisor sum
-/

namespace Pollack17

open Filter
open scoped BigOperators

theorem one_le_principal_divisorCoefficient {m n : ℕ} (hn : 0 < n) :
    1 ≤ divisorCoefficient (1 : DirichletCharacter ℂ m) n := by
  rw [divisorCoefficient_eq_sum]
  have hnonneg (d : ℕ) : 0 ≤ ((1 : DirichletCharacter ℂ m) (d : ℕ)).re := by
    by_cases hd : IsUnit (d : ZMod m)
    · rw [MulChar.one_apply hd, Complex.one_re]
      norm_num
    · rw [MulChar.map_nonunit _ hd, Complex.zero_re]
  have h := Finset.single_le_sum (fun d _ => hnonneg d)
    (show 1 ∈ n.divisors from Nat.one_mem_divisors.mpr hn.ne')
  simpa only [Nat.cast_one, map_one, Complex.one_re] using h

theorem principal_divisor_sum_lower (m X : ℕ) :
    (X : ℝ) ≤ ∑ n ∈ Finset.Icc 1 X, divisorCoefficient (1 : DirichletCharacter ℂ m) n := by
  calc
    _ = ∑ _n ∈ Finset.Icc 1 X, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun n hn => one_le_principal_divisorCoefficient (Finset.mem_Icc.mp hn).1

theorem eventually_divisor_sum_lower_bound {c δ : ℝ} (hc : 1 / 4 < c) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ (χ : DirichletCharacter ℂ m), χ.IsQuadratic →
      (m : ℝ) ^ (c - δ) ≤ ∑ n ∈ Finset.Icc 1 ⌊(m : ℝ) ^ c⌋₊, divisorCoefficient χ n := by
  have hc0 : 0 < c := by linarith
  obtain ⟨τ, hτ, hcomp⟩ := eventually_divisor_sum_asymptotic hc
  let u : ℝ := min δ τ / 4
  have hu : 0 < u := by dsimp [u]; positivity
  have huδ : u < δ := by
    have h := min_le_left δ τ
    dsimp [u] at hu ⊢
    linarith
  have huτ : u < τ := by
    have h := min_le_right δ τ
    dsimp [u] at hu ⊢
    linarith
  have herr := Burgess.eventually_const_mul_rpow_le (C := 1) (d := 1 / 4)
    (a := c - τ) (b := c - u) (by norm_num) (by linarith)
  have htarget := Burgess.eventually_const_mul_rpow_le (C := 1) (d := 1 / 4)
    (a := c - δ) (b := c - u) (by norm_num) (by linarith)
  have hprincipal := Burgess.eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
    (a := c - δ) (b := c) (by norm_num) (by linarith)
  filter_upwards [hcomp, eventually_quadratic_LFunction_one_re_ge_rpow hu,
    herr, htarget, hprincipal, Burgess.eventually_floor_rpow_bounds hc0, eventually_ge_atTop 1]
    with m hcomp hL herr htarget hprincipal hfloor hm1
  intro χ hχ
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm1
  have : NeZero m := ⟨by omega⟩
  by_cases hχ1 : χ = 1
  · rw [hχ1]
    have htarget' : (m : ℝ) ^ (c - δ) ≤ (m : ℝ) ^ c / 2 := by
      nlinarith only [hprincipal]
    exact (htarget'.trans hfloor.1).trans (principal_divisor_sum_lower m _)
  · have hLv := hL χ hχ1 hχ
    have hmain : (1 / 2 : ℝ) * (m : ℝ) ^ (c - u) ≤
        (⌊(m : ℝ) ^ c⌋₊ : ℝ) * (DirichletCharacter.LFunction χ 1).re := by
      calc
        _ = ((m : ℝ) ^ c / 2) * (m : ℝ) ^ (-u) := by
          rw [sub_eq_add_neg, Real.rpow_add hm0]
          ring
        _ ≤ _ := mul_le_mul hfloor.1 hLv (Real.rpow_nonneg hm0.le _) (Nat.cast_nonneg _)
    have herror := (abs_le.mp (hcomp χ hχ hχ1)).1
    have herr' : (m : ℝ) ^ (c - τ) ≤ (1 / 4 : ℝ) * (m : ℝ) ^ (c - u) := by
      simpa only [one_mul] using herr
    have htarget' : (m : ℝ) ^ (c - δ) ≤ (1 / 4 : ℝ) * (m : ℝ) ^ (c - u) := by
      simpa only [one_mul] using htarget
    linarith only [hmain, herror, herr', htarget']

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/Definitions.lean` -/

section

namespace Pollack17

/-- The analytic cutoff `m^(1/4 + ε)` appearing in Theorem 1.3. -/
noncomputable def residuePrimeUpperBound (m : ℕ) (ε : ℝ) : ℝ :=
  Real.rpow (m : ℝ) ((1 / 4 : ℝ) + ε)

/--
The finite set of primes `ℓ` with `ℓ ≤ m^(1/4 + ε)` and `χ(ℓ) = 1`.

This definition does **not** assume `χ` is quadratic; the quadraticity hypothesis
belongs only to `theorem_1_3`, matching the statement of the paper.
-/
noncomputable def residuePrimesUpTo (m : ℕ) (χ : DirichletCharacter ℂ m) (ε : ℝ) : Finset ℕ := by
  classical
  exact
    ((Finset.range (Nat.ceil (residuePrimeUpperBound m ε) + 1)).filter fun ℓ =>
      Nat.Prime ℓ ∧
      (ℓ : ℝ) ≤ residuePrimeUpperBound m ε ∧
      χ (ℓ : ZMod m) = (1 : ℂ))

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/FiniteEulerProduct.lean` -/

section

/-!
# A finite Rankin inequality for quadratic divisor coefficients

Only primes below the summation endpoint enter the Euler product.  Thus
the inequality does not require convergence of `ζ(s)L(s,χ)` in the half
plane where Rankin's parameter will be chosen.
-/

namespace Pollack17

open scoped BigOperators

variable {m : ℕ}

noncomputable def weightedDivisorCoefficient (χ : DirichletCharacter ℂ m)
    (s : ℝ) (n : ℕ) : ℝ := divisorCoefficient χ n * (n : ℝ) ^ (-s)

theorem weightedDivisorCoefficient_nonneg (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) (s : ℝ) (n : ℕ) :
    0 ≤ weightedDivisorCoefficient χ s n :=
  mul_nonneg (divisorCoefficient_nonneg χ hχ n)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

@[simp] theorem weightedDivisorCoefficient_one (χ : DirichletCharacter ℂ m)
    (s : ℝ) : weightedDivisorCoefficient χ s 1 = 1 := by
  simp [weightedDivisorCoefficient]

theorem weightedDivisorCoefficient_mul (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) (s : ℝ) {a b : ℕ} (hab : a.Coprime b) :
    weightedDivisorCoefficient χ s (a * b) =
      weightedDivisorCoefficient χ s a * weightedDivisorCoefficient χ s b := by
  simp only [weightedDivisorCoefficient, divisorCoefficient_mul χ hχ hab,
    Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  ring

theorem weightedDivisorCoefficient_prime_pow (χ : DirichletCharacter ℂ m)
    (s : ℝ) (p e : ℕ) :
    weightedDivisorCoefficient χ s (p ^ e) =
      divisorCoefficient χ (p ^ e) * ((p : ℝ) ^ (-s)) ^ e := by
  unfold weightedDivisorCoefficient
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p),
    mul_comm (e : ℝ), Real.rpow_mul_natCast (Nat.cast_nonneg p)]

theorem summable_norm_weightedDivisorCoefficient_prime_pow
    (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    {s : ℝ} (hs : 0 < s) {p : ℕ} (hp : p.Prime) :
    Summable (fun e : ℕ => ‖weightedDivisorCoefficient χ s (p ^ e)‖) := by
  have hu0 : 0 ≤ (p : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hu1 : (p : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hs)
  apply (summable_divisorCoefficient_prime_pow χ hχ hp hu0 hu1).congr
  intro e
  rw [Real.norm_eq_abs,
    abs_of_nonneg (weightedDivisorCoefficient_nonneg χ hχ s _),
    weightedDivisorCoefficient_prime_pow]

/-- Rankin's inequality with all local factors left explicit. -/
theorem sum_divisorCoefficient_le_finiteEulerProduct
    (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    {s : ℝ} (hs : 0 < s) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n) ≤
      (X : ℝ) ^ s *
        ∏ p ∈ (X + 1).primesBelow,
          ∑' e : ℕ, divisorCoefficient χ (p ^ e) * ((p : ℝ) ^ (-s)) ^ e := by
  classical
  let f := weightedDivisorCoefficient χ s
  have hf0 (n : ℕ) : 0 ≤ f n := weightedDivisorCoefficient_nonneg χ hχ s n
  have hEuler := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (weightedDivisorCoefficient_one χ s)
    (fun {_ _} hab => weightedDivisorCoefficient_mul χ hχ s hab)
    (fun {_} hp => summable_norm_weightedDivisorCoefficient_prime_pow χ hχ hs hp)
    (X + 1)
  let terms : Finset (X + 1).smoothNumbers := (Finset.Icc 1 X).attach.map
    { toFun := fun n => ⟨n.1, Nat.mem_smoothNumbers_of_lt
        (Finset.mem_Icc.mp n.2).1 (Nat.lt_succ_of_le (Finset.mem_Icc.mp n.2).2)⟩
      inj' := by
        intro a b h
        exact Subtype.ext (congrArg (fun z : (X + 1).smoothNumbers => (z : ℕ)) h) }
  have hterms : (∑ z ∈ terms, f z) = ∑ n ∈ Finset.Icc 1 X, f n := by
    simp only [terms, Finset.sum_map]
    change (∑ z ∈ (Finset.Icc 1 X).attach, f z.1) = _
    exact Finset.sum_attach _ _
  have hsum : (∑ n ∈ Finset.Icc 1 X, f n) ≤
      ∏ p ∈ (X + 1).primesBelow, ∑' e : ℕ, f (p ^ e) := by
    rw [← hterms]
    exact (hEuler.2.summable.sum_le_tsum terms (fun n _ => hf0 n)).trans_eq
      hEuler.2.tsum_eq
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 X) :
      divisorCoefficient χ n ≤ (X : ℝ) ^ s * f n := by
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hpow : (n : ℝ) ^ s ≤ (X : ℝ) ^ s :=
      Real.rpow_le_rpow hn0.le (by exact_mod_cast (Finset.mem_Icc.mp hn).2) hs.le
    calc
      divisorCoefficient χ n = (n : ℝ) ^ s * f n := by
        dsimp [f, weightedDivisorCoefficient]
        rw [mul_left_comm, ← Real.rpow_add hn0]
        simp
      _ ≤ (X : ℝ) ^ s * f n := mul_le_mul_of_nonneg_right hpow (hf0 n)
  calc
    (∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n) ≤
        ∑ n ∈ Finset.Icc 1 X, (X : ℝ) ^ s * f n :=
      Finset.sum_le_sum hpoint
    _ = (X : ℝ) ^ s * ∑ n ∈ Finset.Icc 1 X, f n := by rw [Finset.mul_sum]
    _ ≤ (X : ℝ) ^ s *
        ∏ p ∈ (X + 1).primesBelow, ∑' e : ℕ, f (p ^ e) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by simp only [f, weightedDivisorCoefficient_prime_pow]

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/PrimeSetBounds.lean` -/

section

/-!
# A cardinality bound for the Rankin mass of a finite prime set

The elements of the set need not be small: splitting at its cardinality
controls the sum of their negative powers by a function of that cardinality.
-/

namespace Pollack17

open scoped BigOperators

theorem sum_Icc_rpow_sub_one_le (K : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ (δ - 1)) ≤
      (K : ℝ) ^ δ * (1 + Real.log (K : ℝ)) := by
  calc
    (∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ (δ - 1)) ≤
        ∑ n ∈ Finset.Icc 1 K, (K : ℝ) ^ δ * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [Real.rpow_sub_one hn0.ne', div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (Nat.cast_nonneg _)
          (by exact_mod_cast (Finset.mem_Icc.mp hn).2) hδ)
        (inv_nonneg.mpr hn0.le)
    _ = (K : ℝ) ^ δ * (harmonic K : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rw [Finset.mul_sum]
    _ ≤ (K : ℝ) ^ δ * (1 + Real.log (K : ℝ)) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log K)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem sum_rpow_sub_one_le_card (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑ n ∈ S, (n : ℝ) ^ (δ - 1)) ≤
      (S.card : ℝ) ^ δ * (2 + Real.log (S.card : ℝ)) := by
  classical
  by_cases hK : S.card = 0
  · have hEmpty : S = ∅ := Finset.card_eq_zero.mp hK
    simp [hEmpty, Real.zero_rpow hδ0.ne']
  have hKpos : 0 < (S.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hK
  let T := S.filter fun n => n ≤ S.card
  let U := S.filter fun n => ¬ n ≤ S.card
  have hsmall : (∑ n ∈ T, (n : ℝ) ^ (δ - 1)) ≤
      (S.card : ℝ) ^ δ * (1 + Real.log (S.card : ℝ)) := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (s := T)
      (t := Finset.Icc 1 S.card) ?_ ?_).trans (sum_Icc_rpow_sub_one_le _ hδ0.le)
    · intro n hn
      have hn' := Finset.mem_filter.mp hn
      exact Finset.mem_Icc.mpr ⟨hS n hn'.1, hn'.2⟩
    · intro n _ _
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlarge : (∑ n ∈ U, (n : ℝ) ^ (δ - 1)) ≤ (S.card : ℝ) ^ δ := by
    calc
      (∑ n ∈ U, (n : ℝ) ^ (δ - 1)) ≤
          ∑ _n ∈ U, (S.card : ℝ) ^ (δ - 1) := by
        apply Finset.sum_le_sum
        intro n hn
        have hKn : S.card ≤ n := by
          have := (Finset.mem_filter.mp hn).2
          omega
        exact Real.rpow_le_rpow_of_nonpos hKpos
          (by exact_mod_cast hKn) (sub_nonpos.mpr hδ1)
      _ = (U.card : ℝ) * (S.card : ℝ) ^ (δ - 1) := by simp
      _ ≤ (S.card : ℝ) * (S.card : ℝ) ^ (δ - 1) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hKpos.le _)
        exact_mod_cast Finset.card_filter_le S (fun n => ¬ n ≤ S.card)
      _ = (S.card : ℝ) ^ δ := by
        rw [Real.rpow_sub_one hKpos.ne']
        field_simp
  calc
    (∑ n ∈ S, (n : ℝ) ^ (δ - 1)) =
        (∑ n ∈ T, (n : ℝ) ^ (δ - 1)) +
          ∑ n ∈ U, (n : ℝ) ^ (δ - 1) := by
      exact (Finset.sum_filter_add_sum_filter_not S
        (fun n => n ≤ S.card) (fun n => (n : ℝ) ^ (δ - 1))).symm
    _ ≤ (S.card : ℝ) ^ δ * (1 + Real.log (S.card : ℝ)) +
        (S.card : ℝ) ^ δ := add_le_add hsmall hlarge
    _ = (S.card : ℝ) ^ δ * (2 + Real.log (S.card : ℝ)) := by ring

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/SparseEulerProduct.lean` -/

section

/-!
# Sparse exceptional primes in a quadratic Euler product

Primes with character value `-1` contribute only even powers, giving a
convergent square-power Euler product for every Rankin parameter above
`1/2`.  The remaining primes cost an exponential depending only on their
cardinality.
-/

namespace Pollack17

open scoped BigOperators

noncomputable def eulerLogConstant : ℝ := (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹

theorem eulerLogConstant_pos : 0 < eulerLogConstant := by
  apply inv_pos.mpr
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))

theorem inv_one_sub_le_exp_eulerLogConstant {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ))) :
    (1 - u)⁻¹ ≤ Real.exp (eulerLogConstant * u) := by
  let c : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))
  have hc : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hden : 0 < 1 - u := sub_pos.mpr (hu.trans_lt hc)
  have hcden : 0 < 1 - c := sub_pos.mpr hc
  have hlog : -Real.log (1 - u) ≤ (1 - u)⁻¹ - 1 := by
    linarith [Real.one_sub_inv_le_log_of_pos hden]
  have hid : (1 - u)⁻¹ - 1 = u * (1 - u)⁻¹ := by
    field_simp
    ring
  have hinv : (1 - u)⁻¹ ≤ (1 - c)⁻¹ :=
    (inv_le_inv₀ hden hcden).2 (sub_le_sub_left hu 1)
  have hexp : -Real.log (1 - u) ≤ eulerLogConstant * u := by
    calc
      -Real.log (1 - u) ≤ (1 - u)⁻¹ - 1 := hlog
      _ = u * (1 - u)⁻¹ := hid
      _ ≤ u * (1 - c)⁻¹ := mul_le_mul_of_nonneg_left hinv hu0
      _ = eulerLogConstant * u := by simp [eulerLogConstant, c, mul_comm]
  calc
    (1 - u)⁻¹ = Real.exp (-Real.log (1 - u)) := by rw [Real.exp_neg, Real.exp_log hden]
    _ ≤ Real.exp (eulerLogConstant * u) := Real.exp_le_exp.mpr hexp

theorem prime_neg_rpow_le_half_reference {p : ℕ} (hp : p.Prime)
    {s : ℝ} (hs : 1 / 2 ≤ s) :
    (p : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  calc
    (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) (neg_le_neg hs)
    _ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by norm_num)

theorem local_divisorCoefficient_sum_le_squareFactor
    {m : ℕ} (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    {p : ℕ} (hp : p.Prime) {s : ℝ} (hs : 1 / 2 ≤ s) :
    (∑' e : ℕ, divisorCoefficient χ (p ^ e) * ((p : ℝ) ^ (-s)) ^ e) ≤
      (1 - ((p : ℝ) ^ (-s)) ^ 2)⁻¹ *
        Real.exp (if χ (p : ZMod m) ≠ -1 then
          2 * eulerLogConstant * (p : ℝ) ^ (-s) else 0) := by
  let u : ℝ := (p : ℝ) ^ (-s)
  have hu0 : 0 ≤ u := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have huref : u ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := prime_neg_rpow_le_half_reference hp hs
  have hu1 : u < 1 := huref.trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hden : 0 < 1 - u ^ 2 := by nlinarith
  have hbase : 1 ≤ (1 - u ^ 2)⁻¹ := by
    rw [← one_div, le_div_iff₀ hden]
    nlinarith
  by_cases h : χ (p : ZMod m) = -1
  · simpa [h, u] using (hasSum_divisorCoefficient_of_neg_one χ hp h hu0 hu1).tsum_eq.le
  · rw [if_pos h]
    calc
      (∑' e : ℕ, divisorCoefficient χ (p ^ e) * u ^ e) ≤ (1 - u)⁻¹ ^ 2 :=
        local_divisorCoefficient_sum_le χ hχ hp hu0 hu1
      _ ≤ Real.exp (eulerLogConstant * u) ^ 2 :=
        pow_le_pow_left₀ (inv_nonneg.mpr (sub_nonneg.mpr hu1.le))
          (inv_one_sub_le_exp_eulerLogConstant hu0 huref) 2
      _ = Real.exp (2 * eulerLogConstant * u) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      _ ≤ (1 - u ^ 2)⁻¹ * Real.exp (2 * eulerLogConstant * u) :=
        le_mul_of_one_le_left (Real.exp_nonneg _) hbase

/-- The primes whose Euler factor is not the square-only factor. -/
noncomputable def exceptionalPrimes {m : ℕ} (χ : DirichletCharacter ℂ m) (X : ℕ) : Finset ℕ :=
  ((X + 1).primesBelow).filter fun p => χ (p : ZMod m) ≠ -1

noncomputable def natPowerHom (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ s
  map_one' := by simp
  map_mul' a b := by simp [Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

theorem squareEulerProduct_le_tsum (X : ℕ) {s : ℝ} (hs : 1 / 2 < s) :
    (∏ p ∈ (X + 1).primesBelow, (1 - ((p : ℝ) ^ (-s)) ^ 2)⁻¹) ≤
      ∑' n : ℕ, (n : ℝ) ^ (-(2 * s)) := by
  let f := natPowerHom (-(2 * s))
  have hf : Summable f := Real.summable_nat_rpow.mpr (by linarith)
  have hlocal (p : ℕ) : ((p : ℝ) ^ (-s)) ^ 2 = f p := by
    dsimp [f, natPowerHom]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
    congr 1
    push_cast
    ring
  simp_rw [hlocal]
  rw [EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers hf]
  exact tsum_comp_le_tsum_of_inj hf (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (Subtype.val_injective : Function.Injective (fun n : (X + 1).smoothNumbers => (n : ℕ)))

theorem finiteEulerProduct_le_sparse_bound
    {m : ℕ} (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    (X : ℕ) {s : ℝ} (hs0 : 1 / 2 < s) (hs1 : s < 1) :
    (∏ p ∈ (X + 1).primesBelow,
      ∑' e : ℕ, divisorCoefficient χ (p ^ e) * ((p : ℝ) ^ (-s)) ^ e) ≤
      (∑' n : ℕ, (n : ℝ) ^ (-(2 * s))) *
        Real.exp (2 * eulerLogConstant *
          (exceptionalPrimes χ X).card ^ (1 - s) *
            (2 + Real.log (exceptionalPrimes χ X).card)) := by
  classical
  let S := (X + 1).primesBelow
  let B : ℕ → ℝ := fun p => (1 - ((p : ℝ) ^ (-s)) ^ 2)⁻¹
  let E : ℕ → ℝ := fun p => if χ (p : ZMod m) ≠ -1 then
    2 * eulerLogConstant * (p : ℝ) ^ (-s) else 0
  have hprod :
      (∏ p ∈ S, ∑' e : ℕ, divisorCoefficient χ (p ^ e) * ((p : ℝ) ^ (-s)) ^ e) ≤
        (∏ p ∈ S, B p) * Real.exp (∑ p ∈ S, E p) := by
    calc
      _ ≤ ∏ p ∈ S, B p * Real.exp (E p) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact tsum_nonneg fun e =>
            mul_nonneg (divisorCoefficient_nonneg χ hχ _)
              (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _)
        · intro p hp
          exact local_divisorCoefficient_sum_le_squareFactor χ hχ
            (Nat.prime_of_mem_primesBelow hp) hs0.le
      _ = _ := by rw [Finset.prod_mul_distrib, Real.exp_sum]
  have hsum : (∑ p ∈ S, E p) ≤
      2 * eulerLogConstant * (exceptionalPrimes χ X).card ^ (1 - s) *
        (2 + Real.log (exceptionalPrimes χ X).card) := by
    have hmass := sum_rpow_sub_one_le_card (exceptionalPrimes χ X)
      (fun p hp => (Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1).pos)
      (sub_pos.mpr hs1) (by linarith : 1 - s ≤ 1)
    have hmass' : (∑ p ∈ exceptionalPrimes χ X, (p : ℝ) ^ (-s)) ≤
        (exceptionalPrimes χ X).card ^ (1 - s) *
          (2 + Real.log (exceptionalPrimes χ X).card) := by
      simpa only [sub_sub_cancel_left] using hmass
    calc
      (∑ p ∈ S, E p) =
          2 * eulerLogConstant * ∑ p ∈ exceptionalPrimes χ X, (p : ℝ) ^ (-s) := by
        simp only [exceptionalPrimes, Finset.sum_filter, E, S, Finset.mul_sum,
          mul_ite, mul_zero]
      _ ≤ _ := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hmass'
            (mul_nonneg (by norm_num) eulerLogConstant_pos.le)
  exact hprod.trans (mul_le_mul (squareEulerProduct_le_tsum X hs0)
    (Real.exp_le_exp.mpr hsum) (Real.exp_nonneg _)
    (tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))

theorem sum_divisorCoefficient_le_sparse_bound
    {m : ℕ} (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    (X : ℕ) {s : ℝ} (hs0 : 1 / 2 < s) (hs1 : s < 1) :
    (∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n) ≤
      (X : ℝ) ^ s * (∑' n : ℕ, (n : ℝ) ^ (-(2 * s))) *
        Real.exp (2 * eulerLogConstant *
          (exceptionalPrimes χ X).card ^ (1 - s) *
            (2 + Real.log (exceptionalPrimes χ X).card)) := by
  have h := mul_le_mul_of_nonneg_left
    (finiteEulerProduct_le_sparse_bound χ hχ X hs0 hs1)
    (Real.rpow_nonneg (Nat.cast_nonneg X) s)
  exact (sum_divisorCoefficient_le_finiteEulerProduct χ hχ
    (by linarith : 0 < s) X).trans (by simpa only [mul_assoc] using h)

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/ExceptionalPrimes.lean` -/

section

/-!
# Connecting the sparse Euler product to the exact residue-prime set

Every exceptional prime is either a divisor of the modulus or a prime at
which the character is `1`.  The latter are counted by the unchanged
`residuePrimesUpTo` definition.
-/

namespace Pollack17

open scoped BigOperators

theorem mem_residuePrimesUpTo_iff {m p : ℕ} {ε : ℝ}
    {χ : DirichletCharacter ℂ m} :
    p ∈ residuePrimesUpTo m χ ε ↔ p.Prime ∧
      (p : ℝ) ≤ residuePrimeUpperBound m ε ∧ χ (p : ZMod m) = 1 := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, h⟩
    apply Nat.lt_succ_of_le
    exact_mod_cast h.2.1.trans (Nat.le_ceil (residuePrimeUpperBound m ε))

theorem exceptionalPrimes_subset {m X : ℕ} {ε : ℝ}
    (hm : m ≠ 0) (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    (hX : (X : ℝ) ≤ residuePrimeUpperBound m ε) :
    exceptionalPrimes χ X ⊆ m.primeFactors ∪ residuePrimesUpTo m χ ε := by
  classical
  intro p hp
  obtain ⟨hpS, hpne⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpX, hprime⟩ := Nat.mem_primesBelow.mp hpS
  rcases hχ (p : ZMod m) with hzero | hone | hneg
  · apply Finset.mem_union_left
    have hnonunit := MulChar.apply_eq_zero_iff.mp hzero
    have hdiv : p ∣ m := by
      simpa only [ZMod.isUnit_iff_coprime, hprime.coprime_iff_not_dvd, not_not] using hnonunit
    exact Nat.mem_primeFactors.mpr ⟨hprime, hdiv, hm⟩
  · apply Finset.mem_union_right
    exact mem_residuePrimesUpTo_iff.mpr ⟨hprime,
      (show (p : ℝ) ≤ X by exact_mod_cast Nat.lt_succ_iff.mp hpX).trans hX, hone⟩
  · exact (hpne hneg).elim

theorem exceptionalPrimes_card_le {m X : ℕ} {ε : ℝ}
    (hm : m ≠ 0) (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    (hX : (X : ℝ) ≤ residuePrimeUpperBound m ε) :
    (exceptionalPrimes χ X).card ≤ m.primeFactors.card + (residuePrimesUpTo m χ ε).card :=
  (Finset.card_le_card (exceptionalPrimes_subset hm χ hχ hX)).trans
    (Finset.card_union_le _ _)

theorem primeFactors_card_le_log {m : ℕ} (hm : 0 < m) :
    (m.primeFactors.card : ℝ) ≤ Real.log (m : ℝ) / Real.log 2 := by
  have hpow : 2 ^ m.primeFactors.card ≤ m := by
    calc
      2 ^ m.primeFactors.card = ∏ _p ∈ m.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ m.primeFactors, p := by
        exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
          (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ m := Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
  have hcast : (2 : ℝ) ^ m.primeFactors.card ≤ (m : ℝ) := by exact_mod_cast hpow
  have hlog := Real.log_le_log (pow_pos (by norm_num) _) hcast
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/SparseAsymptotics.lean` -/

section

/-!
# Absorbing a sparse Euler product into a small power

When the number of exceptional primes is bounded by a fixed power of
`log m`, the exponential cost in the finite Euler product is smaller than
every positive power of `m`, after choosing the Rankin exponent small enough.
-/

namespace Pollack17

open Filter
open scoped BigOperators

theorem eventually_const_mul_rpow_le {C d a b : ℝ} (hd : 0 < d) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a ≤ d * x ^ b := by
  have hlarge := (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually
    (eventually_ge_atTop (C / d))
  filter_upwards [hlarge, eventually_ge_atTop 1] with x hx hx1
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hratio : C ≤ d * x ^ (b - a) := by
    simpa only [mul_comm] using (div_le_iff₀ hd).mp hx
  calc
    C * x ^ a ≤ (d * x ^ (b - a)) * x ^ a :=
      mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hx0.le _)
    _ = d * x ^ b := by
      rw [mul_assoc, ← Real.rpow_add hx0]
      congr 2
      ring

theorem sparse_cost_le_double_rpow (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (K : ℝ) ^ δ * (2 + Real.log (K : ℝ)) ≤
      (2 + δ⁻¹) * (K : ℝ) ^ (2 * δ) := by
  by_cases hK : K = 0
  · subst K
    simp [Real.zero_rpow hδ.ne', Real.zero_rpow (by positivity : 2 * δ ≠ 0)]
  have hK1 : 1 ≤ (K : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hK
  have hK0 : 0 < (K : ℝ) := zero_lt_one.trans_le hK1
  have hpow : 1 ≤ (K : ℝ) ^ δ := Real.one_le_rpow hK1 hδ.le
  have hlog : Real.log (K : ℝ) ≤ (K : ℝ) ^ δ * δ⁻¹ := by
    simpa only [div_eq_mul_inv] using Real.log_natCast_le_rpow_div K hδ
  calc
    (K : ℝ) ^ δ * (2 + Real.log (K : ℝ)) ≤
        (K : ℝ) ^ δ * ((2 + δ⁻¹) * (K : ℝ) ^ δ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hK0.le _)
      nlinarith
    _ = (2 + δ⁻¹) * (K : ℝ) ^ (2 * δ) := by
      rw [mul_left_comm, ← Real.rpow_add hK0]
      congr 2
      ring

theorem eventually_sparse_exponential_le_rpow {B δ η C : ℝ}
    (_hB : 0 < B) (hδ : 0 < δ) (hsmall : 2 * B * δ < 1)
    (hη : 0 < η) (hC : 0 ≤ C) :
    ∀ᶠ m : ℕ in atTop, ∀ K : ℕ,
      (K : ℝ) ≤ (Real.log (m : ℝ)) ^ B →
        Real.exp (C * (K : ℝ) ^ δ * (2 + Real.log (K : ℝ))) ≤ (m : ℝ) ^ η := by
  have hlogtop : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound := hlogtop.eventually
    (eventually_const_mul_rpow_le (C := C * (2 + δ⁻¹)) hη hsmall)
  filter_upwards [hbound, eventually_ge_atTop 2] with m hm hm2
  intro K hK
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hL0 : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm2)
  have hmass : (K : ℝ) ^ δ * (2 + Real.log (K : ℝ)) ≤
      (2 + δ⁻¹) * (Real.log (m : ℝ)) ^ (2 * B * δ) := by
    calc
      (K : ℝ) ^ δ * (2 + Real.log (K : ℝ)) ≤
          (2 + δ⁻¹) * (K : ℝ) ^ (2 * δ) := sparse_cost_le_double_rpow K hδ
      _ ≤ (2 + δ⁻¹) * ((Real.log (m : ℝ)) ^ B) ^ (2 * δ) := by
        apply mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg K) hK (by positivity))
        positivity
      _ = (2 + δ⁻¹) * (Real.log (m : ℝ)) ^ (2 * B * δ) := by
        rw [← Real.rpow_mul hL0.le]
        congr 2
        ring
  have hexponent : C * (K : ℝ) ^ δ * (2 + Real.log (K : ℝ)) ≤
      Real.log (m : ℝ) * η := by
    have hmassC := mul_le_mul_of_nonneg_left hmass hC
    simp only [Real.rpow_one] at hm
    nlinarith
  rw [Real.rpow_def_of_pos hm0]
  exact Real.exp_le_exp.mpr hexponent

/-- A polylogarithmic number of exceptional primes forces a fixed power
saving in the divisor-coefficient sum, uniformly over the character. -/
theorem eventually_sparse_divisor_sum {c B : ℝ} (hc : 0 < c) (hB : 0 < B) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ χ : DirichletCharacter ℂ m, MulChar.IsQuadratic χ → ∀ X : ℕ,
        (X : ℝ) ≤ (m : ℝ) ^ c →
        ((exceptionalPrimes χ X).card : ℝ) ≤ (Real.log (m : ℝ)) ^ B →
        (∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n) ≤ (m : ℝ) ^ (c - ρ) := by
  let δ : ℝ := 1 / (4 * (B + 1))
  let s : ℝ := 1 - δ
  let η : ℝ := c * δ / 4
  let ρ : ℝ := c * δ / 2
  let Z : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(2 * s))
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ < 1 / 4 := by
    exact one_div_lt_one_div_of_lt (by norm_num) (by nlinarith : 4 < 4 * (B + 1))
  have hδid : 4 * (B + 1) * δ = 1 := by
    exact mul_one_div_cancel (by positivity : (4 : ℝ) * (B + 1) ≠ 0)
  have hsmall : 2 * B * δ < 1 := by nlinarith
  have hs0 : 1 / 2 < s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  have hspos : 0 < s := by linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hexp := eventually_sparse_exponential_le_rpow (C := 2 * eulerLogConstant)
    hB hδ0 hsmall hη
    (mul_nonneg (by norm_num) eulerLogConstant_pos.le)
  have hZ : ∀ᶠ m : ℕ in atTop, Z ≤ (m : ℝ) ^ η := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_const_mul_rpow_le (C := Z) (d := 1) (a := 0) (by norm_num) hη)
    simpa only [Real.rpow_zero, mul_one, one_mul] using h
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [hexp, hZ, eventually_ge_atTop 1] with m hmExp hmZ hm1
  intro χ hχ X hX hK
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm1
  have hXpow : (X : ℝ) ^ s ≤ (m : ℝ) ^ (c * s) := by
    calc
      (X : ℝ) ^ s ≤ ((m : ℝ) ^ c) ^ s :=
        Real.rpow_le_rpow (Nat.cast_nonneg X) hX hspos.le
      _ = (m : ℝ) ^ (c * s) := (Real.rpow_mul hm0.le c s).symm
  have hExp := hmExp (exceptionalPrimes χ X).card hK
  have hExp' :
      Real.exp (2 * eulerLogConstant * (exceptionalPrimes χ X).card ^ (1 - s) *
        (2 + Real.log (exceptionalPrimes χ X).card)) ≤ (m : ℝ) ^ η := by
    simpa only [s, sub_sub_cancel] using hExp
  calc
    (∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n) ≤
        (X : ℝ) ^ s * Z *
          Real.exp (2 * eulerLogConstant * (exceptionalPrimes χ X).card ^ (1 - s) *
            (2 + Real.log (exceptionalPrimes χ X).card)) :=
      sum_divisorCoefficient_le_sparse_bound χ hχ X hs0 hs1
    _ ≤ (m : ℝ) ^ (c * s) * (m : ℝ) ^ η * (m : ℝ) ^ η :=
      mul_le_mul
        (mul_le_mul hXpow hmZ hZ0 (Real.rpow_nonneg hm0.le _)) hExp'
        (Real.exp_nonneg _)
        (mul_nonneg (Real.rpow_nonneg hm0.le _) (Real.rpow_nonneg hm0.le _))
    _ = (m : ℝ) ^ (c - ρ) := by
      rw [← Real.rpow_add hm0, ← Real.rpow_add hm0]
      congr 1
      dsimp [s, η, ρ]
      ring

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/SparseResiduePrimes.lean` -/

section

/-!
# The counting half of Pollack's residue-prime argument

Fewer than a prescribed power of `log m` residue primes forces a power
saving in the sum of the quadratic divisor coefficients through the exact
cutoff.  This theorem is uniform over all quadratic characters, including
imprimitive characters and the principal character.
-/

namespace Pollack17

open Filter
open scoped BigOperators

theorem eventually_few_residue_primes_divisor_sum
    (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ χ : DirichletCharacter ℂ m, MulChar.IsQuadratic χ →
        ((residuePrimesUpTo m χ ε).card : ℝ) ≤ (Real.log (m : ℝ)) ^ A →
        ∀ X : ℕ, (X : ℝ) ≤ residuePrimeUpperBound m ε →
          (∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n) ≤
            (m : ℝ) ^ ((1 / 4 : ℝ) + ε - ρ) := by
  have hc : 0 < (1 / 4 : ℝ) + ε := by linarith
  have hB : 0 < A + 2 := by linarith
  obtain ⟨ρ, hρ, hsum⟩ := eventually_sparse_divisor_sum hc hB
  have hlogtop : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hram := hlogtop.eventually
    (eventually_const_mul_rpow_le (C := (Real.log 2)⁻¹) (d := 1 / 2)
      (a := 1) (b := A + 2) (by norm_num) (by linarith))
  have hres := hlogtop.eventually
    (eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
      (a := A) (b := A + 2) (by norm_num) (by linarith))
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [hsum, hram, hres, eventually_ge_atTop 1] with m hmSum hmRam hmRes hm1
  intro χ hχ hcount X hX
  apply hmSum χ hχ X hX
  have hmpos : 0 < m := hm1
  have hcard : ((exceptionalPrimes χ X).card : ℝ) ≤
      (m.primeFactors.card : ℝ) + ((residuePrimesUpTo m χ ε).card : ℝ) := by
    exact_mod_cast exceptionalPrimes_card_le hmpos.ne' χ hχ hX
  have hram' : Real.log (m : ℝ) / Real.log 2 ≤
      (1 / 2 : ℝ) * (Real.log (m : ℝ)) ^ (A + 2) := by
    simpa only [Real.rpow_one, div_eq_mul_inv, mul_comm] using hmRam
  have hres' : (Real.log (m : ℝ)) ^ A ≤
      (1 / 2 : ℝ) * (Real.log (m : ℝ)) ^ (A + 2) := by
    simpa only [one_mul] using hmRes
  linarith [primeFactors_card_le_log hmpos]

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/ResiduePrimeTheorem.lean` -/

section

/-!
# Pollack's uniform lower bound for prime quadratic residues

Pollack, *Bounds for the First Several Prime Character Nonresidues* (2017),
Theorem 1.3. The two bounds on the same nonnegative divisor sum contradict
one another if there are fewer than the prescribed power of the logarithm
residue primes. Both bounds are uniform over all quadratic characters.
-/

namespace Pollack17

open Filter
open scoped BigOperators

theorem residue_prime_count (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ m0 : ℕ, ∀ m : ℕ, m > m0 →
      ∀ χ : DirichletCharacter ℂ m, MulChar.IsQuadratic χ →
        Real.rpow (Real.log (m : ℝ)) A ≤ ((residuePrimesUpTo m χ ε).card : ℝ) := by
  obtain ⟨ρ, hρ, hupper⟩ := eventually_few_residue_primes_divisor_sum ε A hε hA
  have hlower := eventually_divisor_sum_lower_bound
    (c := (1 / 4 : ℝ) + ε) (δ := ρ / 2) (by linarith) (half_pos hρ)
  have hresult : ∀ᶠ m : ℕ in atTop,
      ∀ χ : DirichletCharacter ℂ m, MulChar.IsQuadratic χ →
        Real.rpow (Real.log (m : ℝ)) A ≤ ((residuePrimesUpTo m χ ε).card : ℝ) := by
    filter_upwards [hupper, hlower, eventually_ge_atTop 2] with m hu hl hm
    intro χ hχ
    by_contra hnot
    have hcount : ((residuePrimesUpTo m χ ε).card : ℝ) ≤ (Real.log (m : ℝ)) ^ A :=
      (lt_of_not_ge hnot).le
    have hX : (⌊(m : ℝ) ^ ((1 / 4 : ℝ) + ε)⌋₊ : ℝ) ≤ residuePrimeUpperBound m ε :=
      Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hsum := (hl χ hχ).trans (hu χ hχ hcount _ hX)
    have hstrict : (m : ℝ) ^ ((1 / 4 : ℝ) + ε - ρ) <
        (m : ℝ) ^ ((1 / 4 : ℝ) + ε - ρ / 2) :=
      Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (show 1 < m by omega)) (by linarith)
    exact (not_le_of_gt hstrict) hsum
  obtain ⟨m0, hm0⟩ := eventually_atTop.mp hresult
  exact ⟨m0, fun m hm => hm0 m hm.le⟩

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/PollackTheorem.lean` -/

section

namespace Pollack17

/--
Pollack, *Bounds for the First Several Prime Character Nonresidues*, Theorem 1.3.
-/
theorem theorem_1_3
    (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ m0 : ℕ, ∀ m : ℕ,
      m > m0 →
      ∀ χ : DirichletCharacter ℂ m,
        MulChar.IsQuadratic χ →
          Real.rpow (Real.log (m : ℝ)) A ≤
            ((residuePrimesUpTo m χ ε).card : ℝ) :=
  residue_prime_count ε A hε hA

end Pollack17

end

/-! ### Upstream module `ErdosProblems/Erdos1141/AttachedCharacter.lean` -/

section

/-!
# Jacobi characters at arbitrary multiple moduli

The original public interface remains available to other formalizations.
All results in this module are elementary; no prime-existence theorem is assumed.
-/

/-- A lightweight paper-facing formalization of “`χ` is a quadratic character modulo `m`”.

This interface is retained for the Jacobi-symbol construction and its users in other problems. -/
structure QuadraticCharacterMod (m : ℕ) where
  toFun : ℕ → ℤ
  periodic : ∀ {a b : ℕ}, Nat.ModEq m a b → toFun a = toFun b
  map_non_coprime : ∀ {a : ℕ}, ¬ Nat.Coprime a m → toFun a = 0
  map_coprime : ∀ {a : ℕ}, Nat.Coprime a m → toFun a = 1 ∨ toFun a = -1
  map_mul : ∀ {a b : ℕ}, Nat.Coprime a m → Nat.Coprime b m →
    toFun (a * b) = toFun a * toFun b

instance {m : ℕ} : CoeFun (QuadraticCharacterMod m) (fun _ ↦ ℕ → ℤ) :=
  ⟨QuadraticCharacterMod.toFun⟩

/-- A quadratic character modulo `m` takes the value `1` at `1`. -/
lemma QuadraticCharacterMod.map_one {m : ℕ} (χ : QuadraticCharacterMod m) : χ 1 = 1 := by
  have hcop : Nat.Coprime 1 m := by
    simp
  rcases χ.map_coprime hcop with h1 | h1
  · exact h1
  · have : False := by
      have hmul : χ (1 * 1) = χ 1 * χ 1 := χ.map_mul (a := 1) (b := 1) hcop hcop
      have hbad : (-1 : ℤ) = 1 := by
        rw [h1] at hmul
        norm_num at hmul
      norm_num at hbad
    exact this.elim

/-- A unit of `ZMod m` has a representative coprime to `m`. -/
lemma natCoprime_val_of_isUnit_zmod {m : ℕ} [NeZero m] {a : ZMod m} (ha : IsUnit a) :
    Nat.Coprime a.val m := by
  rw [← ha.unit_spec]
  exact ZMod.val_coe_unit_coprime ha.unit

/-- A nonunit of `ZMod m` has no representative coprime to `m`. -/
lemma not_natCoprime_val_of_not_isUnit_zmod {m : ℕ} [NeZero m] {a : ZMod m}
    (ha : ¬ IsUnit a) : ¬ Nat.Coprime a.val m := by
  intro hcop
  apply ha
  simpa [ZMod.natCast_zmod_val a] using (ZMod.isUnit_iff_coprime a.val m).2 hcop

/-- Repackage a paper-facing quadratic character as a `DirichletCharacter` over `ℂ`. -/
def QuadraticCharacterMod.toDirichletCharacterComplex {m : ℕ} [NeZero m]
    (χ : QuadraticCharacterMod m) : DirichletCharacter ℂ m where
  toFun a := (χ a.val : ℂ)
  map_one' := by
    have hperiodic : χ ((1 : ZMod m).val) = χ 1 := by
      apply χ.periodic
      rw [← ZMod.natCast_eq_natCast_iff]
      simp
    rw [hperiodic]
    simpa using congrArg (fun z : ℤ => (z : ℂ)) χ.map_one
  map_mul' := by
    intro a b
    by_cases ha : IsUnit a
    · by_cases hb : IsUnit b
      · have hcopa : Nat.Coprime a.val m := natCoprime_val_of_isUnit_zmod ha
        have hcopb : Nat.Coprime b.val m := natCoprime_val_of_isUnit_zmod hb
        have hperiodic : χ ((a * b).val) = χ (a.val * b.val) := by
          apply χ.periodic
          rw [← ZMod.natCast_eq_natCast_iff]
          calc
            (((a * b).val : ℕ) : ZMod m) = a * b := by
              simp
            _ = ((a.val : ZMod m) * (b.val : ZMod m)) := by
              simp
            _ = ((a.val * b.val : ℕ) : ZMod m) := by simp
        have hperiodicC : (χ ((a * b).val) : ℂ) = (χ (a.val * b.val) : ℂ) :=
          congrArg (fun z : ℤ => (z : ℂ)) hperiodic
        rw [hperiodicC]
        simpa using congrArg (fun z : ℤ => (z : ℂ)) (χ.map_mul hcopa hcopb)
      · have hnon : ¬ IsUnit (a * b) := by
          intro hab
          exact hb (isUnit_of_mul_isUnit_right hab)
        have hzero_mul : χ ((a * b).val) = 0 :=
          χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod hnon)
        have hzero_b : χ b.val = 0 :=
          χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod hb)
        simp [hzero_mul, hzero_b]
    · have hnon : ¬ IsUnit (a * b) := by
        intro hab
        exact ha (isUnit_of_mul_isUnit_left hab)
      have hzero_mul : χ ((a * b).val) = 0 :=
        χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod hnon)
      have hzero_a : χ a.val = 0 :=
        χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod ha)
      simp [hzero_mul, hzero_a]
  map_nonunit' := by
    intro a ha
    have hzero : χ a.val = 0 :=
      χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod ha)
    simp [hzero]

@[simp] lemma QuadraticCharacterMod.toDirichletCharacterComplex_apply {m : ℕ} [NeZero m]
    (χ : QuadraticCharacterMod m) (a : ZMod m) :
    χ.toDirichletCharacterComplex a = (χ a.val : ℂ) := rfl

@[simp] lemma QuadraticCharacterMod.toDirichletCharacterComplex_apply_nat
    {m n : ℕ} [NeZero m] (χ : QuadraticCharacterMod m) :
    χ.toDirichletCharacterComplex (n : ZMod m) = (χ n : ℂ) := by
  change ((χ ((n : ZMod m).val) : ℂ) = (χ n : ℂ))
  simpa [ZMod.val_natCast] using
    congrArg (fun z : ℤ => (z : ℂ)) (χ.periodic (Nat.mod_modEq n m))

/-- The associated complex Dirichlet character is quadratic. -/
lemma QuadraticCharacterMod.toDirichletCharacterComplex_isQuadratic
    {m : ℕ} [NeZero m] (χ : QuadraticCharacterMod m) :
    MulChar.IsQuadratic (χ.toDirichletCharacterComplex) := by
  intro a
  by_cases ha : IsUnit a
  · have hcop : Nat.Coprime a.val m := natCoprime_val_of_isUnit_zmod ha
    rcases χ.map_coprime hcop with h1 | hneg
    · right
      left
      simp [h1]
    · right
      right
      simp [hneg]
  · left
    have hcop : ¬ Nat.Coprime a.val m := not_natCoprime_val_of_not_isUnit_zmod ha
    simp [χ.map_non_coprime hcop]

/-- If the associated complex Dirichlet character takes the value `1` at a natural number,
then the original integer-valued character also takes the value `1` there. -/
lemma QuadraticCharacterMod.eq_one_of_toDirichletCharacterComplex_apply_nat_eq_one
    {m n : ℕ} [NeZero m] (χ : QuadraticCharacterMod m)
    (hχ : χ.toDirichletCharacterComplex (n : ZMod m) = (1 : ℂ)) :
    χ n = 1 := by
  have happly : χ.toDirichletCharacterComplex (n : ZMod m) = (χ n : ℂ) :=
    χ.toDirichletCharacterComplex_apply_nat (n := n)
  have hχ' : (χ n : ℂ) = (1 : ℂ) := by
    rw [← happly]
    exact hχ
  by_cases hcop : Nat.Coprime n m
  · rcases χ.map_coprime hcop with h1 | hneg
    · exact h1
    · exfalso
      rw [hneg] at hχ'
      norm_num at hχ'
  · exfalso
    rw [χ.map_non_coprime hcop] at hχ'
    norm_num at hχ'

/-- If `4*d ∣ m`, then `d ∣ m`. -/
lemma d_dvd_of_four_d_dvd {d m : ℕ} (hdvd : 4 * d ∣ m) : d ∣ m := by
  exact dvd_trans (show d ∣ 4 * d by exact ⟨4, by ac_rfl⟩) hdvd

/-- If `4*d ∣ m`, then `2 ∣ m`. -/
lemma two_dvd_of_four_d_dvd {d m : ℕ} (hdvd : 4 * d ∣ m) : 2 ∣ m := by
  exact dvd_trans (show 2 ∣ 4 * d by exact ⟨2 * d, by ac_rfl⟩) hdvd

/-- The quadratic character attached to `d`, viewed modulo any multiple `m` of `4*d`.

On integers coprime to `m` it is the Jacobi symbol `jacobiSym d`; on non-coprime integers it
is `0`.  The congruence invariance modulo `m` comes from `jacobiSym.mod_right`.

This public construction is also used by the formalization of Erdős Problem 1140. -/
def attachedQuadraticCharacter (d m : ℕ) (hdvd : 4 * d ∣ m) :
    QuadraticCharacterMod m where
  toFun n := if Nat.Coprime n m then jacobiSym (d : ℤ) n else 0
  periodic := by
    intro a b hmod
    have hcop : Nat.Coprime a m ↔ Nat.Coprime b m := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one, hmod.gcd_eq]
    by_cases ha : Nat.Coprime a m
    · have hb : Nat.Coprime b m := hcop.mp ha
      have hmod' : Nat.ModEq (4 * d) a b := hmod.of_dvd hdvd
      have ha2 : Nat.Coprime a 2 := ha.coprime_dvd_right (two_dvd_of_four_d_dvd hdvd)
      have hb2 : Nat.Coprime b 2 := hb.coprime_dvd_right (two_dvd_of_four_d_dvd hdvd)
      have haOdd : Odd a := (Nat.coprime_two_right).1 ha2
      have hbOdd : Odd b := (Nat.coprime_two_right).1 hb2
      have hJ : jacobiSym (d : ℤ) a = jacobiSym (d : ℤ) b := by
        calc
          jacobiSym (d : ℤ) a = jacobiSym (d : ℤ) (a % (4 * d)) := by
            simpa using jacobiSym.mod_right (d : ℤ) haOdd
          _ = jacobiSym (d : ℤ) (b % (4 * d)) := by
            simpa using congrArg (fun t : ℕ ↦ jacobiSym (d : ℤ) t) hmod'
          _ = jacobiSym (d : ℤ) b := by
            simpa using (jacobiSym.mod_right (d : ℤ) hbOdd).symm
      rw [if_pos ha, if_pos hb]
      exact hJ
    · have hb : ¬ Nat.Coprime b m := mt hcop.mpr ha
      rw [if_neg ha, if_neg hb]
  map_non_coprime := by
    intro a ha
    rw [if_neg ha]
  map_coprime := by
    intro a ha
    have had : Nat.Coprime a d := ha.coprime_dvd_right (d_dvd_of_four_d_dvd hdvd)
    have hgcd : Int.gcd (d : ℤ) a = 1 := by
      simpa [Int.gcd_eq_natAbs, Nat.gcd_comm] using had.gcd_eq_one
    rw [if_pos ha]
    exact jacobiSym.eq_one_or_neg_one (a := (d : ℤ)) (b := a) hgcd
  map_mul := by
    intro a b ha hb
    have ha2 : Nat.Coprime a 2 := ha.coprime_dvd_right (two_dvd_of_four_d_dvd hdvd)
    have hb2 : Nat.Coprime b 2 := hb.coprime_dvd_right (two_dvd_of_four_d_dvd hdvd)
    have haOdd : Odd a := (Nat.coprime_two_right).1 ha2
    have hbOdd : Odd b := (Nat.coprime_two_right).1 hb2
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0] at haOdd
      norm_num at haOdd
    have hb0 : b ≠ 0 := by
      intro h0
      rw [h0] at hbOdd
      norm_num at hbOdd
    split_ifs at * with hab
    · exact jacobiSym.mul_right' (d : ℤ) ha0 hb0
    · exact (hab (Nat.coprime_mul_iff_left.2 ⟨ha, hb⟩)).elim

@[simp] lemma attachedQuadraticCharacter_apply_coprime {d m n : ℕ}
    (hdvd : 4 * d ∣ m) (hn : Nat.Coprime n m) :
    attachedQuadraticCharacter d m hdvd n = jacobiSym (d : ℤ) n := by
  simp [attachedQuadraticCharacter, hn]


end

/-! ### Upstream module `Util/MertensThird.lean` -/

section

/-
Below you can find a formalization of (a version of) Mertens third theorem,
which is used in the conditional Lean proofs of Erdős Problems #237
(https://www.erdosproblems.com/237) and #1141
(https://www.erdosproblems.com/1141) that you can find here:

https://gist.githubusercontent.com/pitmonticone/8ea0d1cdb963b6213ac639b11d33f811/raw/98a5824d16da14313f65d77eeab5563dd874613a/Erdos237.lean

https://github.com/yuta0x89/ErdosProblems/blob/9eebc7a51466e6ad1b57318302cdc821d30df4ff/Erdos1141.lean

The formalization of Mertens third theorem was obtained by Aristotle from Harmonic (aristotle-harmonic@harmonic.fun).

-/

open Finset ArithmeticFunction Real
open scoped BigOperators

set_option maxRecDepth 4000

/-- ψ(n) = Σ_{m=1}^{n} Λ(m), the first Chebyshev function. -/
noncomputable def chebyshevPsi (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), vonMangoldt m

/-- L_n = lcm(1, 2, ..., n). -/
def lcmRange (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm _root_.id

/-- S(n) = Σ_{m=2}^{n} Λ(m)/m. -/
noncomputable def sumS (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 n, vonMangoldt m / m

/-- T(n) = Σ_{m=2}^{n} Λ(m)/(m * log m). -/
noncomputable def sumT (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 n, vonMangoldt m / (m * Real.log m)

/-- P(n) = ∏_{p ≤ n, p prime} (1 - 1/p). -/
noncomputable def prodP (n : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

/-! # Lemma: Central Binomial Coefficient Bounds -/

lemma centralBinom_le_four_pow (r : ℕ) (hr : 1 ≤ r) :
    Nat.choose (2 * r) r ≤ 4 ^ r := by
  rw [show 4 ^ r = (2 : ℕ) ^ (2 * r) by norm_num [pow_mul]]
  rw [← Nat.sum_range_choose]
  exact Finset.single_le_sum (fun x _ => Nat.zero_le _)
    (Finset.mem_range.mpr (by linarith))

lemma choose_odd_le_four_pow (r : ℕ) (_hr : 1 ≤ r) :
    Nat.choose (2 * r + 1) r ≤ 4 ^ r := by
  exact Nat.choose_middle_le_pow r

/-! # LCM helpers -/

lemma lcmRange_pos (n : ℕ) (_hn : 1 ≤ n) : 0 < lcmRange n := by
  exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) )

lemma lcmRange_dvd_of_le {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    m ∣ lcmRange n := by
  exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hm, hmn ⟩ )

/-! # LCM Divisibility Lemmas -/

lemma lcmRange_dvd_even (r : ℕ) (hr : 1 ≤ r) :
    lcmRange (2 * r) ∣ lcmRange r * Nat.choose (2 * r) r := by
  -- By definition of lcmRange, we need to show that for every prime power $p^a$ dividing $m \in (1, 2r]$, $p^a$ divides $lcmRange(r) * \binom{2r}{r}$.
  have h_div : ∀ m ∈ Finset.Icc 1 (2 * r), ∀ p ∈ Nat.primeFactors m, p ^ Nat.factorization m p ∣ lcmRange r * Nat.choose (2 * r) r := by
    intro m hm p hp
    by_cases hpa : p ^ Nat.factorization m p ≤ r;
    · exact dvd_mul_of_dvd_left ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ ( Nat.pos_of_mem_primeFactors hp ), hpa ⟩ ) ) _;
    · -- Since $p^a > r$, we have $p^{a-1} \leq r$.
      have hpa_minus_one : p ^ (Nat.factorization m p - 1) ≤ r := by
        rcases k : Nat.factorization m p with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
        nlinarith [ hp.1.two_le, Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd m p ), Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd m p ), show m ≥ p ^ ( Nat.factorization m p ) from Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd m p ), show p ^ ( Nat.factorization m p ) = p * p ^ ‹_› from by rw [ ← pow_succ', k ] ];
      -- Since $p^{a-1} \leq r$, we have $p^{a-1} \mid lcmRange(r)$.
      have hpa_minus_one_div : p ^ (Nat.factorization m p - 1) ∣ lcmRange r := by
        exact lcmRange_dvd_of_le ( pow_pos ( Nat.pos_of_mem_primeFactors hp ) _ ) hpa_minus_one;
      -- Since $p^a > r$, we have $p \mid \binom{2r}{r}$.
      have hpa_div_choose : p ∣ Nat.choose (2 * r) r := by
        have hpa_div_choose : Nat.factorization (Nat.choose (2 * r) r) p ≥ 1 := by
          have hpa_div_choose : Nat.factorization (Nat.choose (2 * r) r) p = (∑ k ∈ Finset.Ico 1 (Nat.log p (2 * r) + 1), (Nat.floor ((2 * r) / p ^ k) - 2 * Nat.floor (r / p ^ k))) := by
            have := Fact.mk ( Nat.prime_of_mem_primeFactors hp ) ; rw [ Nat.factorization_def ];
            · rw [ padicValNat_choose ];
              any_goals exact Nat.lt_succ_self _;
              · norm_num [ two_mul, Nat.add_div ];
                rw [ Finset.card_filter ];
                refine Finset.sum_congr rfl fun x hx => ?_
                rw [ Nat.add_div ( pow_pos ( Nat.Prime.pos ( Nat.prime_of_mem_primeFactors hp ) ) _ ) ] ; aesop;
              · linarith;
            · exact Nat.prime_of_mem_primeFactors hp;
          rw [hpa_div_choose];
          refine le_trans ?_ ( Finset.single_le_sum ( fun x hx => Nat.zero_le _ ) ( Finset.mem_Ico.mpr ⟨ Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( show m.factorization p ≠ 0 from Finsupp.mem_support_iff.mp hp ) ), Nat.lt_succ_of_le ( Nat.le_log_of_pow_le ( Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hp ) ) ( show p ^ m.factorization p ≤ 2 * r from ?_ ) ) ⟩ ) )
          · norm_num [ Nat.div_eq_of_lt ( show r < p ^ m.factorization p from lt_of_not_ge hpa ) ];
            exact Nat.div_pos ( by linarith [ Finset.mem_Icc.mp hm, Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) ( Nat.ordProj_dvd m p ) ] ) ( pow_pos ( Nat.pos_of_mem_primeFactors hp ) _ );
          · exact le_trans ( Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) ( Nat.ordProj_dvd _ _ ) ) ( by linarith [ Finset.mem_Icc.mp hm ] );
        exact Nat.dvd_trans ( dvd_pow_self _ ( by linarith ) ) ( Nat.ordProj_dvd _ _ );
      convert Nat.mul_dvd_mul hpa_minus_one_div hpa_div_choose using 1 ; rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hp ) ) ) ];
  -- Since every prime power in the lcm divides the product, the lcm itself must divide the product.
  have h_lcm_div : ∀ m ∈ Finset.Icc 1 (2 * r), m ∣ lcmRange r * Nat.choose (2 * r) r := by
    intro m hm
    have h_prod_div : ∏ p ∈ Nat.primeFactors m, p ^ Nat.factorization m p ∣ lcmRange r * Nat.choose (2 * r) r := by
      -- The least common multiple of a set of numbers is equal to their product divided by their greatest common divisor.
      have h_lcm_prod : ∀ {S : Finset ℕ} {f : ℕ → ℕ}, (∀ p ∈ S, Nat.Prime p) → (∀ p q : ℕ, p ∈ S → q ∈ S → p ≠ q → Nat.gcd (p ^ f p) (q ^ f q) = 1) → Finset.lcm S (fun p => p ^ f p) = ∏ p ∈ S, p ^ f p := by
        intros S f hprime hgcd; induction S using Finset.induction <;> simp_all +decide ;
        exact Nat.Coprime.lcm_eq_mul <| Nat.Coprime.prod_right fun p hp => hgcd _ _ ( Or.inl rfl ) ( Or.inr hp ) <| by aesop;
      rw [ ← h_lcm_prod ( fun p hp => Nat.prime_of_mem_primeFactors hp ) ( fun p q hp hq hpq => by simpa [ hpq ] using Nat.coprime_pow_primes _ _ ( Nat.prime_of_mem_primeFactors hp ) ( Nat.prime_of_mem_primeFactors hq ) ) ];
      exact Finset.lcm_dvd fun p hp => h_div m hm p hp;
    rwa [ ← Nat.prod_factorization_pow_eq_self ( by linarith [ Finset.mem_Icc.mp hm ] : m ≠ 0 ) ];
  exact Finset.lcm_dvd h_lcm_div

lemma lcmRange_dvd_odd (r : ℕ) (hr : 1 ≤ r) :
    lcmRange (2 * r + 1) ∣ lcmRange (r + 1) * Nat.choose (2 * r + 1) r := by
  -- For any prime power $p^a \leq 2r+1$, we need to show that $p^a$ divides $lcmRange(r+1) * (2r+1 choose r)$.
  have h_prime_power : ∀ p a : ℕ, Nat.Prime p → p^a ≤ 2 * r + 1 → p^a ∣ lcmRange (r + 1) * Nat.choose (2 * r + 1) r := by
    intro p a hp ha
    by_cases hpa : p^a ≤ r + 1;
    · exact dvd_mul_of_dvd_left
        (Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ hp.pos, hpa ⟩))
        (Nat.choose (2 * r + 1) r)
    · -- Since $p^a > r + 1$, we have $p^{a-1} \leq r$.
      have hpa_minus_one : p^(a-1) ≤ r := by
        rcases a <;> simp_all +decide [ pow_succ' ];
        nlinarith [ hp.two_le ];
      -- Since $p^{a-1} \leq r$, we have $p^a \mid \binom{2r+1}{r}$.
      have hpa_div_choose : p^a ∣ Nat.choose (2 * r + 1) r * p^(a-1) := by
        have hpa_div_choose : padicValNat p (Nat.choose (2 * r + 1) r) ≥ 1 := by
          have := Fact.mk hp; rw [ padicValNat_choose ];
          any_goals exact Nat.lt_succ_self _;
          · refine Finset.card_pos.mpr ⟨ a, ?_ ⟩ ; norm_num;
            exact ⟨ ⟨ Nat.pos_of_ne_zero ( by rintro rfl; linarith ), Nat.le_log_of_pow_le hp.one_lt ha ⟩, by rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> omega ⟩;
          · linarith;
        have hpa_div_choose : p ∣ Nat.choose (2 * r + 1) r := by
          contrapose! hpa_div_choose; simp_all +decide ;
        rcases a with ( _ | a ) <;> simp_all +decide [ pow_succ', mul_dvd_mul ];
      -- Since $p^{a-1} \leq r$, we have $p^{a-1} \mid lcmRange(r+1)$.
      have hpa_minus_one_div_lcm : p^(a-1) ∣ lcmRange (r + 1) := by
        have hpa_minus_one_div_lcm : p^(a-1) ∈ Finset.Icc 1 (r + 1) := by
          exact Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ hp.pos, by linarith ⟩;
        exact Finset.dvd_lcm hpa_minus_one_div_lcm;
      exact dvd_trans hpa_div_choose ( by rw [ mul_comm ] ; exact mul_dvd_mul hpa_minus_one_div_lcm dvd_rfl );
  -- By definition of lcmRange, lcmRange (2 * r + 1) divides the product of all numbers in the range 1 to 2r+1.
  have h_lcm_div : ∀ m ∈ Finset.Icc 1 (2 * r + 1), m ∣ lcmRange (r + 1) * Nat.choose (2 * r + 1) r := by
    intro m hm; rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
    · intro p; by_cases hp : Nat.Prime p <;> by_cases hp' : p ∣ m <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ] ;
      have := h_prime_power p ( Nat.factorization m p ) hp ( Nat.le_trans ( Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd _ _ ) ) hm.2 ) ; rw [ ← Nat.factorization_le_iff_dvd ] at this <;> simp_all +decide ;
      exact ⟨ Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop, Nat.ne_of_gt <| Nat.choose_pos <| by linarith ⟩;
    · linarith [ Finset.mem_Icc.mp hm ];
    · exact ⟨ Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop, Nat.ne_of_gt <| Nat.choose_pos <| by linarith ⟩;
  exact Finset.lcm_dvd fun x hx => h_lcm_div x hx

/-! # LCM Bound: L_n ≤ 4^n -/

lemma lcmRange_le_four_pow (n : ℕ) (hn : 1 ≤ n) :
    lcmRange n ≤ 4 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
  by_cases h₂ : n ≤ 4;
  · interval_cases n <;> decide;
  · rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩;
    · -- By lcmRange_dvd_even, lcmRange(2k) | lcmRange(k) * choose(2k,k).
      have h_div : lcmRange (2 * k) ∣ lcmRange k * Nat.choose (2 * k) k := by
        exact lcmRange_dvd_even k ( by linarith );
      -- Since $\binom{2k}{k} \leq 4^k$, we have $lcmRange (2 * k) \leq lcmRange k * 4^k$.
      have h_bound : lcmRange (2 * k) ≤ lcmRange k * 4 ^ k := by
        refine le_trans ( Nat.le_of_dvd ( Nat.mul_pos ( lcmRange_pos k ( by linarith ) ) ( Nat.choose_pos ( by linarith ) ) ) h_div ) ?_
        exact Nat.mul_le_mul_left _ ( centralBinom_le_four_pow k ( by linarith ) );
      exact h_bound.trans ( by rw [ pow_mul' ] ; exact Nat.mul_le_mul_right _ ( ih k ( by linarith ) ( by linarith ) ) |> le_trans <| by ring_nf; norm_num );
    · -- By lcmRange_dvd_odd, lcmRange(2k+1) | lcmRange(k+1) * choose(2k+1,k).
      have h_div : lcmRange (2 * k + 1) ∣ lcmRange (k + 1) * Nat.choose (2 * k + 1) k := by
        convert lcmRange_dvd_odd k ( by linarith ) using 1;
      -- By choose_odd_le_four_pow, choose(2k+1,k) ≤ 4^k.
      have h_choose : Nat.choose (2 * k + 1) k ≤ 4 ^ k := by
        convert choose_odd_le_four_pow k ( by linarith ) using 1;
      refine le_trans ( Nat.le_of_dvd ?_ h_div ) ?_
      · exact mul_pos ( lcmRange_pos _ ( by linarith ) ) ( Nat.choose_pos ( by linarith ) );
      · exact le_trans ( Nat.mul_le_mul ( ih _ ( by linarith ) ( by linarith ) ) h_choose ) ( by ring_nf; norm_num )

/-! # Chebyshev ψ bound -/

lemma chebyshevPsi_eq_log_lcmRange (n : ℕ) (hn : 1 ≤ n) :
    chebyshevPsi n = Real.log (lcmRange n) := by
  -- By definition of ψ, we know that ψ(n) = Σ_{m=0}^n Λ(m)
  have h_psi_def : chebyshevPsi n = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), Nat.log p n * Real.log p := by
    have h_psi_def : chebyshevPsi n = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (∑ k ∈ Finset.Icc 1 (Nat.log p n), Real.log p) := by
      unfold chebyshevPsi;
      have h_sum_floor : ∑ m ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt m) = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (ArithmeticFunction.vonMangoldt (p ^ k)) := by
        have h_sum_floor : Finset.filter (fun m => ArithmeticFunction.vonMangoldt m ≠ 0) (Finset.range (n + 1)) = Finset.biUnion (Finset.filter Nat.Prime (Finset.range (n + 1))) (fun p => Finset.image (fun k => p ^ k) (Finset.Icc 1 (Nat.log p n))) := by
          ext m;
          simp [ArithmeticFunction.vonMangoldt];
          constructor;
          · intro hm;
            obtain ⟨ p, k, hp, hk, rfl ⟩ := hm.2.1;
            exact ⟨ p, ⟨ by linarith [ Nat.le_self_pow hk.ne' p ], hp.nat_prime ⟩, k, ⟨ hk, Nat.le_log_of_pow_le hp.nat_prime.one_lt hm.1 ⟩, rfl ⟩;
          · rintro ⟨ p, ⟨ hp₁, hp₂ ⟩, k, ⟨ hk₁, hk₂ ⟩, rfl ⟩;
            exact ⟨ Nat.pow_le_of_le_log ( by linarith ) hk₂, hp₂.isPrimePow.pow ( by linarith ), Nat.ne_of_gt ( Nat.minFac_pos _ ), ne_of_gt ( one_lt_pow₀ hp₂.one_lt ( by linarith ) ), by linarith ⟩;
        rw [ ← Finset.sum_filter_ne_zero, h_sum_floor, Finset.sum_biUnion ];
        · exact Finset.sum_congr rfl fun p hp => Finset.sum_image <| fun a ha b hb h => Nat.pow_right_injective ( Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) h;
        · intros p hp q hq hpq; simp_all +decide [ Finset.disjoint_left ];
          intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; subst_vars; have := Nat.Prime.dvd_of_dvd_pow hp.2 ( hy₃.symm ▸ dvd_pow_self _ ( by linarith ) ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
      convert h_sum_floor using 3;
      rw [ ArithmeticFunction.vonMangoldt_apply ];
      rw [ if_pos ];
      · rw [ Nat.Prime.pow_minFac ] <;> aesop;
      · exact Nat.Prime.isPrimePow ( Finset.mem_filter.mp ‹_› |>.2 ) |> fun h => h.pow ( by linarith [ Finset.mem_Icc.mp ‹_› ] );
    aesop;
  -- By definition of $lcmRange$, we know that $lcmRange n = \prod_{p \leq n} p^{e_p(n)}$ where $e_p(n) = \lfloor \log_p n \rfloor$.
  have h_lcm_def : lcmRange n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n) := by
    clear h_psi_def;
    -- By definition of lcmRange, we know that lcmRange n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n).
    have h_lcmRange_def : ∀ m ∈ Finset.Icc 1 n, m ∣ ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n) := by
      intro m hm; rw [ ← Nat.prod_factorization_pow_eq_self ( by linarith [ Finset.mem_Icc.mp hm ] : m ≠ 0 ) ] ;
      rw [ ← Finset.prod_sdiff <| show m.primeFactors ⊆ Finset.filter Nat.Prime ( Finset.range ( n + 1 ) ) from fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_trans ( Nat.le_of_mem_primeFactors hp ) <| Finset.mem_Icc.mp hm |>.2, Nat.prime_of_mem_primeFactors hp ⟩ ];
      exact dvd_mul_of_dvd_right ( Finset.prod_dvd_prod_of_dvd _ _ fun p hp => pow_dvd_pow p <| Nat.le_log_of_pow_le ( Nat.prime_of_mem_primeFactors hp |> Nat.Prime.one_lt ) <| Nat.le_trans ( Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) <| Nat.ordProj_dvd _ _ ) <| Finset.mem_Icc.mp hm |>.2 ) _;
    refine Nat.dvd_antisymm ?_ ?_
    · exact Finset.lcm_dvd fun x hx => h_lcmRange_def x hx;
    · -- By definition of lcmRange, we know that lcmRange n is divisible by each prime power p^k where p is prime and k is such that p^k ≤ n.
      have h_lcmRange_div : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n) ∣ lcmRange n := by
        intros p hp
        have h_div : p ^ (Nat.log p n) ≤ n := by
          exact Nat.pow_log_le_self p ( by linarith );
        exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ), h_div ⟩ );
      -- The least common multiple of a set of numbers is equal to the product of the highest powers of all primes dividing any of the numbers.
      have h_lcm_eq_prod : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Finset.lcm S (fun p => p ^ (Nat.log p n)) = ∏ p ∈ S, p ^ (Nat.log p n) := by
        intros S hS; induction S using Finset.induction <;> simp_all +decide ;
        exact Nat.Coprime.lcm_eq_mul <| Nat.Coprime.prod_right fun p hp => Nat.Coprime.pow _ _ <| hS.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 p hp ) ; aesop;
      rw [ ← h_lcm_eq_prod fun p hp => Finset.mem_filter.mp hp |>.2 ];
      exact Finset.lcm_dvd h_lcmRange_div;
  rw [ h_psi_def, h_lcm_def, Nat.cast_prod, Real.log_prod ] <;> aesop

lemma chebyshevPsi_le (n : ℕ) (hn : 1 ≤ n) :
    chebyshevPsi n ≤ 2 * n * Real.log 2 := by
  have h_log : Real.log (lcmRange n) ≤ Real.log (4 ^ n) := by
    gcongr;
    · exact_mod_cast lcmRange_pos n hn;
    · exact_mod_cast lcmRange_le_four_pow n hn;
  rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, pow_right_comm ] at h_log ; norm_num at *;
  rw [ chebyshevPsi_eq_log_lcmRange n hn ] ; linarith

/-! # S(n) Upper Bound -/

/-
S(n) ≤ (log(n!) + ψ(n)) / n
-/
lemma sumS_le_basic (n : ℕ) (hn : 2 ≤ n) :
    sumS n ≤ (Real.log (n.factorial) + chebyshevPsi n) / n := by
  -- By the properties of logarithms and the definition of S(n), we can rewrite the inequality.
  have h_rewrite : ∑ m ∈ Finset.Icc 2 n, (vonMangoldt m / m : ℝ) * n ≤ Real.log (Nat.factorial n) + ∑ m ∈ Finset.Icc 1 n, vonMangoldt m := by
    -- We'll use that $\sum_{m=1}^n \Lambda(m) \left\lfloor \frac{n}{m} \right\rfloor = \log(n!)$.
    have h_log_factorial : ∑ m ∈ Finset.Icc 1 n, (vonMangoldt m : ℝ) * Nat.floor (n / m) = Real.log (Nat.factorial n) := by
      -- By definition of von Mangoldt function, we know that $\sum_{d \mid m} \Lambda(d) = \log m$.
      have h_von_mangoldt : ∀ m : ℕ, 1 ≤ m → ∑ d ∈ Nat.divisors m, (ArithmeticFunction.vonMangoldt d : ℝ) = Real.log m := by
        exact fun m a => vonMangoldt_sum;
      -- Applying the definition of von Mangoldt function to the sum.
      have h_sum_von_mangoldt : ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors m, (ArithmeticFunction.vonMangoldt d : ℝ) = ∑ d ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt d : ℝ) * Nat.floor (n / d) := by
        have h_sum_von_mangoldt : ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors m, (ArithmeticFunction.vonMangoldt d : ℝ) = ∑ d ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt d : ℝ) * (if d ∣ m then 1 else 0) := by
          rw [ Finset.sum_comm, Finset.sum_congr rfl ];
          simp +zetaDelta at *;
          intro x hx₁ hx₂; rw [ ← Finset.sum_filter ] ; congr; ext; simp +decide [ Nat.mem_divisors ] ;
          exact ⟨ fun h => ⟨ ⟨ Nat.pos_of_dvd_of_pos h.1 hx₁, Nat.le_trans ( Nat.le_of_dvd hx₁ h.1 ) hx₂ ⟩, h.1 ⟩, fun h => ⟨ h.2, by linarith ⟩ ⟩;
        simp_all +decide [ Finset.sum_ite ];
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [ mul_comm, show Finset.filter ( fun y => x ∣ y ) ( Finset.Icc 1 n ) = Finset.image ( fun y => x * y ) ( Finset.Icc 1 ( n / x ) ) from ?_, Finset.card_image_of_injective _ fun y z h => mul_left_cancel₀ ( by linarith [ Finset.mem_Icc.mp hx ] ) h ];
        · norm_num;
        · ext y; simp [Finset.mem_image];
          exact ⟨ fun h => ⟨ y / x, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( Finset.mem_Icc.mp hx |>.1 ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Finset.mem_Icc.mp hx |>.1 ], by nlinarith [ Finset.mem_Icc.mp hx |>.2, Nat.div_mul_le_self n x ] ⟩, by simp +decide ⟩ ⟩;
      rw [ ← h_sum_von_mangoldt, Finset.sum_congr rfl fun m hm => h_von_mangoldt m <| Finset.mem_Icc.mp hm |>.1 ];
      erw [ ← Real.log_prod ] <;> norm_cast <;> norm_num;
      · erw [ ← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial ];
      · grind;
    -- Applying the inequality $\frac{n}{m} \leq \left\lfloor \frac{n}{m} \right\rfloor + 1$ to each term in the sum, we get:
    have h_ineq : ∀ m ∈ Finset.Icc 2 n, (vonMangoldt m : ℝ) * (n / m) ≤ (vonMangoldt m : ℝ) * Nat.floor (n / m) + (vonMangoldt m : ℝ) := by
      intros m hm
      have h_floor : (n / m : ℝ) ≤ Nat.floor (n / m) + 1 := by
        rw [ div_le_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_add_mod n m, Nat.mod_lt n ( by linarith [ Finset.mem_Icc.mp hm ] : 0 < m ), Nat.lt_floor_add_one ( n / m ) ];
      simpa only [ mul_add, mul_one ] using mul_le_mul_of_nonneg_left h_floor <| by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by rw [ ArithmeticFunction.vonMangoldt_apply ] ; positivity ) ) ) ) ) ) ) ) ;
    refine le_trans ( Finset.sum_le_sum fun m hm => by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h_ineq m hm ) ?_;
    rw [ ← h_log_factorial, Finset.sum_add_distrib ];
    have hsub : Finset.Icc 2 n ⊆ Finset.Icc 1 n :=
      Finset.Icc_subset_Icc (by norm_num) le_rfl
    exact add_le_add
      (by
        simpa [mul_comm] using
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ =>
            mul_nonneg (Nat.cast_nonneg (n / x)) (ArithmeticFunction.vonMangoldt_nonneg (n := x))))
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ =>
        ArithmeticFunction.vonMangoldt_nonneg (n := x));
  have h_left :
      (∑ m ∈ Finset.Icc 2 n, (vonMangoldt m / m : ℝ) * n) / n = sumS n := by
    rw [Finset.sum_div]
    unfold sumS
    exact Finset.sum_congr rfl fun _ _ => by
      rw [mul_div_cancel_right₀ _ (by positivity)]
  have h_psi : chebyshevPsi n = ∑ m ∈ Finset.Icc 1 n, vonMangoldt m := by
    unfold chebyshevPsi
    erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num
  simpa [h_left, h_psi] using div_le_div_of_nonneg_right h_rewrite (Nat.cast_nonneg n)

/-
log(n!) ≤ n*log(n) - n + 1 + log(n)
-/
lemma log_factorial_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial) ≤ n * Real.log n - n + 1 + Real.log n := by
  induction hn <;> simp_all +decide [ Nat.factorial_succ ];
  rw [ Real.log_mul ( by positivity ) ( by positivity ), add_comm ];
  have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( ↑‹ℕ› : ℝ ) / ( ↑‹ℕ› + 1 ) );
  rw [ Real.log_div ] at this <;> first | positivity | nlinarith [ mul_div_cancel₀ ( ( ↑‹ℕ› : ℝ ) : ℝ ) ( by positivity : ( ↑‹ℕ› + 1 : ℝ ) ≠ 0 ) ] ;

lemma sumS_le_logn_plus (n : ℕ) (hn : 200 ≤ n) :
    sumS n ≤ Real.log n + 0.418 := by
  -- By combining the results from the previous steps, we conclude the proof.
  have h_final : Real.log (n.factorial) + chebyshevPsi n ≤ n * Real.log n + 2 * n * Real.log 2 - n + 1 + Real.log n := by
    linarith [ log_factorial_le n ( by linarith ), chebyshevPsi_le n ( by linarith ) ];
  -- Divide both sides by $n$ and simplify the expression.
  have h_div : sumS n ≤ Real.log n + 2 * Real.log 2 - 1 + (Real.log n + 1) / n := by
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    calc
      sumS n ≤ (Real.log (n.factorial) + chebyshevPsi n) / n :=
        sumS_le_basic n (by linarith)
      _ ≤ (n * Real.log n + 2 * n * Real.log 2 - n + 1 + Real.log n) / n :=
        div_le_div_of_nonneg_right h_final (Nat.cast_nonneg _)
      _ = Real.log n + 2 * Real.log 2 - 1 + (Real.log n + 1) / n := by
        field_simp [hn0]
        ring
  -- We'll use that $Real.log n + 1 \leq Real.log 200 + 1$ for $n \geq 200$.
  have h_log_bound : (Real.log n + 1) / n ≤ (Real.log 200 + 1) / 200 := by
    rw [ div_le_div_iff₀ ] <;> try positivity;
    have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) / 200 );
    rw [ Real.log_div ] at this <;> norm_num at * <;> nlinarith [ ( by norm_cast : ( 200 :ℝ ) ≤ n ), Real.le_log_iff_exp_le ( by positivity : ( 0 :ℝ ) < 200 ) |>.2 <| show ( Real.exp 1 :ℝ ) ≤ 200 by exact le_of_lt <| Real.exp_one_lt_d9.trans_le <| by norm_num ];
  -- We'll use that $Real.log 200 < 5.3$.
  have h_log_200 : Real.log 200 < 5.3 := by
    norm_num [ Real.log_lt_iff_lt_exp ];
    -- We can raise both sides to the power of 10 to remove the fraction.
    suffices h_exp : (200 : ℝ) ^ 10 < Real.exp 53 by
      contrapose! h_exp;
      exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 10 );
    have := Real.exp_one_gt_d9.le ; norm_num at * ; rw [ show Real.exp 53 = ( Real.exp 1 ) ^ 53 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_lt_of_le ( by norm_num ) ( pow_le_pow_left₀ ( by positivity ) this _ );
  have := Real.log_two_lt_d9 ; norm_num at * ; linarith

/-! # Tail bound -/

/-
-log P(n) ≤ T(n) + 1/10 via log series truncation
-/
set_option maxHeartbeats 800000 in
-- The generated tail-bound proof uses large `norm_num` and summability terms.
lemma neg_log_prodP_le_sumT_plus (n : ℕ) (hn : 200 ≤ n) :
    -Real.log (prodP n) ≤ sumT n + 1/10 := by
  -- Let's rewrite the sum in terms of the prime number theorem and the bound we have.
  have h_sum_bound : ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (-Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k)) ≤ 1 / 10 := by
    -- For each prime $p$, the tail $\sum_{k > \lfloor \log_p n \rfloor} \frac{1}{k p^k}$ is bounded by $\frac{1}{(K+1)(p-1)p^K}$ where $K = \lfloor \log_p n \rfloor$.
    have h_tail_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), -Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k) ≤ 1 / ((Nat.log p n + 1) * (p - 1) * (p : ℝ) ^ (Nat.log p n)) := by
      intro p hp
      have h_tail_bound : -Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k) ≤ ∑' k : ℕ, 1 / ((Nat.log p n + k + 1) * (p : ℝ) ^ (Nat.log p n + k + 1)) := by
        have h_tail_bound : -Real.log (1 - 1 / (p : ℝ)) = ∑' k : ℕ, 1 / ((k + 1) * (p : ℝ) ^ (k + 1)) := by
          have := @Real.hasSum_pow_div_log_of_abs_lt_one ( 1 / ( p : ℝ ) ) ?_ <;> norm_num at *;
          · exact this.tsum_eq.symm ▸ rfl;
          · exact inv_lt_one_of_one_lt₀ <| mod_cast hp.2.one_lt;
        erw [ h_tail_bound, ← Summable.sum_add_tsum_nat_add ( Nat.log p n ) ];
        · erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ add_comm, add_left_comm, add_assoc ];
          norm_num [ Finset.sum_range_succ' ];
        · norm_num +zetaDelta at *;
          exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun k => mul_le_of_le_one_right ( by positivity ) <| inv_le_one_of_one_le₀ <| by linarith ) <| by simpa using summable_nat_add_iff 1 |>.2 <| summable_geometric_of_lt_one ( by positivity ) <| inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.2 hp.2.one_lt;
      -- We'll use the fact that $\sum_{k=K+1}^{\infty} \frac{1}{k p^k} \leq \frac{1}{(K+1)p^K} \sum_{k=0}^{\infty} \frac{1}{p^k}$.
      have h_sum_bound : ∑' k : ℕ, 1 / ((Nat.log p n + k + 1) * (p : ℝ) ^ (Nat.log p n + k + 1)) ≤ 1 / ((Nat.log p n + 1) * (p : ℝ) ^ (Nat.log p n + 1)) * ∑' k : ℕ, (1 / (p : ℝ)) ^ k := by
        rw [ ← tsum_mul_left ];
        refine Summable.tsum_le_tsum ?_ ?_ ?_
        · intro i; rw [ div_pow ] ; rw [ div_mul_div_comm ] ; rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring_nf <;> norm_num;
          · exact Or.inr ⟨ ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ), pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩, pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩;
          · exact Or.inr ⟨ ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ), pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩, pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩;
        · norm_num +zetaDelta at *;
          have hgeom :
              Summable (((fun q : ℕ => ((p : ℝ) ^ q)⁻¹) ∘
                fun k : ℕ => Nat.log p n + k + 1)) := by
            exact Summable.comp_injective
              (by
                simpa using
                  summable_geometric_of_lt_one (by positivity)
                    (inv_lt_one_of_one_lt₀ (by
                      norm_cast
                      exact hp.2.one_lt)))
              (by
                intro a b h
                exact Nat.add_left_cancel (Nat.add_right_cancel h))
          exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun k => mul_le_of_le_one_right ( by positivity ) <| inv_le_one_of_one_le₀ <| by linarith ) <| by
            simpa [Function.comp_def] using hgeom
        · exact Summable.mul_left _ <| summable_geometric_of_lt_one ( by positivity ) <| by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2;
      calc
        -Real.log (1 - 1 / (p : ℝ)) -
            ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k)
            ≤
              1 / ((Nat.log p n + 1) * (p : ℝ) ^ (Nat.log p n + 1)) *
                ∑' k : ℕ, (1 / (p : ℝ)) ^ k :=
          h_tail_bound.trans h_sum_bound
        _ = 1 / ((Nat.log p n + 1) * (p - 1) * (p : ℝ) ^ (Nat.log p n)) := by
          have hp_gt_one : (1 : ℝ) < p := by
            norm_cast
            exact Nat.Prime.one_lt (Finset.mem_filter.mp hp |>.2)
          rw [tsum_geometric_of_lt_one (r := 1 / (p : ℝ)) (by positivity)
            (by simpa [one_div] using inv_lt_one_of_one_lt₀ hp_gt_one)]
          ring_nf
          rw [ ← mul_inv ]
          congr
          nlinarith only [
            inv_mul_cancel_left₀
              ( show ( p : ℝ ) ≠ 0 by
                  norm_cast
                  exact Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) )
              ( p ^ Nat.log p n ),
            inv_mul_cancel₀
              ( show ( p : ℝ ) ≠ 0 by
                  norm_cast
                  exact Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ),
            show ( p : ℝ ) ≥ 2 by
              norm_cast
              exact Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ]
    -- Split the sum into two parts: one for primes $p \leq 13$ and one for primes $p > 13$.
    have h_split_sum : ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (-Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k)) ≤ (∑ p ∈ Finset.filter Nat.Prime (Finset.range 14), 1 / ((Nat.log p n + 1) * (p - 1) * (p : ℝ) ^ (Nat.log p n))) + (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 17 (n)), 1 / ((1 + 1) * (p - 1) * (p : ℝ) ^ 1)) := by
      refine le_trans ( Finset.sum_le_sum h_tail_bound ) ?_;
      have h_split_sum : Finset.filter Nat.Prime (Finset.range (n + 1)) ⊆ Finset.filter Nat.Prime (Finset.range 14) ∪ Finset.filter Nat.Prime (Finset.Icc 17 n) := by
        simp +decide [ Finset.subset_iff ];
        exact fun p hp₁ hp₂ => if h : p < 14 then Or.inl ⟨ h, hp₂ ⟩ else Or.inr ⟨ ⟨ not_lt.mp fun h' => by interval_cases p <;> trivial, hp₁ ⟩, hp₂ ⟩;
      refine le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_split_sum ?_ ) ?_;
      · exact fun _ _ _ => one_div_nonneg.mpr ( mul_nonneg ( mul_nonneg ( by positivity ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( by aesop ) ) ) ) ) ( by positivity ) );
      · rw [ Finset.sum_union ];
        · gcongr;
          all_goals norm_num at *;
          any_goals linarith [ Nat.Prime.one_lt ( by tauto ) ];
          · exact mul_pos ( mul_pos two_pos ( sub_pos.mpr ( Nat.one_lt_cast.mpr ( by linarith ) ) ) ) ( Nat.cast_pos.mpr ( by linarith ) );
          · exact mul_nonneg ( by positivity ) ( sub_nonneg_of_le ( mod_cast Nat.Prime.pos ( by tauto ) ) );
          · exact Nat.le_log_of_pow_le ( by linarith ) ( by linarith );
          · exact Nat.le_log_of_pow_le ( by linarith ) ( by linarith );
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
    -- For primes $p \leq 13$, we can bound the sum individually.
    have h_small_primes : ∑ p ∈ Finset.filter Nat.Prime (Finset.range 14), 1 / ((Nat.log p n + 1) * (p - 1) * (p : ℝ) ^ (Nat.log p n)) ≤ 1 / 50 := by
      norm_num [ Finset.sum_filter, Finset.sum_range_succ ];
      -- Since $n \geq 200$, we have $\log_2 n \geq 7$, $\log_3 n \geq 4$, $\log_5 n \geq 3$, $\log_7 n \geq 2$, $\log_{11} n \geq 2$, and $\log_{13} n \geq 2$.
      have h_log_bounds : Nat.log 2 n ≥ 7 ∧ Nat.log 3 n ≥ 4 ∧ Nat.log 5 n ≥ 3 ∧ Nat.log 7 n ≥ 2 ∧ Nat.log 11 n ≥ 2 ∧ Nat.log 13 n ≥ 2 := by
        exact ⟨ Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ) ⟩;
      refine le_trans ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 2 n : ℝ ) + 1 ≥ 8 by norm_cast; linarith ) ) ( by positivity ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 3 n : ℝ ) + 1 ≥ 5 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 5 n : ℝ ) + 1 ≥ 4 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 7 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 11 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 13 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ?_ ; norm_num;
      exact le_trans ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.1 ) ) ( by positivity ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.2.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.2.2.2 ) ) ( by positivity ) ) ) ( by norm_num );
    -- For primes $p > 13$, we can bound the sum using the fact that $\sum_{p \geq 17} \frac{1}{p(p-1)} \leq \frac{1}{32}$.
    have h_large_primes : ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 17 (n)), 1 / ((1 + 1) * (p - 1) * (p : ℝ)) ≤ 1 / 32 := by
      -- We'll use the fact that $\sum_{p \geq 17} \frac{1}{p(p-1)} \leq \frac{1}{32}$.
      have h_large_primes_bound : ∑ p ∈ Finset.Icc 17 n, (1 / ((p - 1) * (p : ℝ))) ≤ 1 / 16 := by
        -- We'll use the fact that $\sum_{p \geq 17} \frac{1}{p(p-1)}$ is a telescoping series.
        have h_telescoping : ∀ m : ℕ, 17 ≤ m → ∑ p ∈ Finset.Icc 17 m, (1 / ((p - 1) * (p : ℝ))) = 1 / 16 - 1 / (m : ℝ) := by
          intro m hm; induction hm <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
          rw [ Finset.sum_Ioc_succ_top ( by linarith ), ‹∑ x ∈ Ioc 16 _, _ = _› ] ; norm_num;
          -- Combine and simplify the terms on the left-hand side.
          field_simp
          ring;
        exact h_telescoping n ( by linarith ) ▸ sub_le_self _ ( by positivity );
      norm_num [ ← mul_assoc, ← Finset.sum_mul _ _ _ ] at *;
      exact le_trans ( mul_le_mul_of_nonneg_right ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => mul_nonneg ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) ( inv_nonneg.2 ( sub_nonneg.2 ( Nat.one_le_cast.2 ( by linarith [ Finset.mem_Icc.1 ‹_› ] ) ) ) ) ) ( by norm_num ) ) ( by linarith );
    norm_num at * ; linarith;
  convert add_le_add_left h_sum_bound ( ∑ p ∈ Finset.filter Nat.Prime ( Finset.range ( n + 1 ) ), ∑ k ∈ Finset.Icc 1 ( Nat.log p n ), 1 / ( k * ( p : ℝ ) ^ k ) ) using 1;
  · unfold prodP; rw [ Real.log_prod ] <;> norm_num;
    exact fun p hp hp' => sub_ne_zero_of_ne <| by aesop;
  · rw [ add_comm, sumT ];
    -- Let's rewrite the sum $\sum_{m=2}^n \frac{\Lambda(m)}{m \log m}$ using the definition of $\Lambda$.
    have h_sum_eq : ∑ m ∈ Finset.Icc 2 n, (ArithmeticFunction.vonMangoldt m : ℝ) / (m * Real.log m) = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (ArithmeticFunction.vonMangoldt (p^k) : ℝ) / (p^k * Real.log (p^k)) := by
      have h_sum_eq : Finset.filter (fun m => ArithmeticFunction.vonMangoldt m ≠ 0) (Finset.Icc 2 n) = Finset.biUnion (Finset.filter Nat.Prime (Finset.range (n + 1))) (fun p => Finset.image (fun k => p^k) (Finset.Icc 1 (Nat.log p n))) := by
        ext m; simp [ArithmeticFunction.vonMangoldt];
        constructor;
        · rintro ⟨ ⟨ hm₁, hm₂ ⟩, hm₃, hm₄, hm₅, hm₆ ⟩;
          obtain ⟨ p, k, hp, hk, rfl ⟩ := hm₃;
          exact ⟨ p, ⟨ by linarith [ Nat.le_self_pow hk.ne' p ], hp.nat_prime ⟩, k, ⟨ hk, Nat.le_log_of_pow_le hp.nat_prime.one_lt hm₂ ⟩, rfl ⟩;
        · rintro ⟨ p, ⟨ hp₁, hp₂ ⟩, k, ⟨ hk₁, hk₂ ⟩, rfl ⟩;
          exact ⟨ ⟨ one_lt_pow₀ hp₂.one_lt ( by linarith ), Nat.pow_le_of_le_log ( by linarith ) hk₂ ⟩, hp₂.isPrimePow.pow ( by linarith ), Nat.ne_of_gt ( Nat.minFac_pos _ ), ne_of_gt ( one_lt_pow₀ hp₂.one_lt ( by linarith ) ), by linarith ⟩;
      have h_sum_eq : ∑ m ∈ Finset.Icc 2 n, (ArithmeticFunction.vonMangoldt m : ℝ) / (m * Real.log m) = ∑ m ∈ Finset.filter (fun m => ArithmeticFunction.vonMangoldt m ≠ 0) (Finset.Icc 2 n), (ArithmeticFunction.vonMangoldt m : ℝ) / (m * Real.log m) := by
        rw [ Finset.sum_filter_of_ne ] ; aesop;
      rw [ h_sum_eq, ‹ { m ∈ Icc 2 n | Λ m ≠ 0 } = _ ›, Finset.sum_biUnion ];
      · exact Finset.sum_congr rfl fun p hp => by rw [ Finset.sum_image <| by intros a ha b hb hab; exact Nat.pow_right_injective ( Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) hab ] ; norm_cast;
      · intros p hp q hq hpq; simp_all +decide [ Finset.disjoint_left ];
        intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; subst_vars; have := Nat.Prime.dvd_of_dvd_pow hp.2 ( hy₃.symm ▸ dvd_pow_self _ ( by linarith ) ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
    rw [ h_sum_eq ];
    refine congr rfl ( Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun k hk => ?_ )
    rw [ ArithmeticFunction.vonMangoldt_apply ];
    rw [ if_pos ];
    · rw [ Nat.pow_minFac ] <;> norm_num [ Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ];
      · rw [ Nat.Prime.minFac_eq ( Finset.mem_filter.mp hp |>.2 ) ] ; ring_nf;
        rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( Finset.mem_filter.mp hp |>.2 ) ) ) ) ), one_mul ];
      · grind;
    · exact Nat.Prime.isPrimePow ( Finset.mem_filter.mp hp |>.2 ) |> fun h => h.pow ( by linarith [ Finset.mem_Icc.mp hk ] )

/-! ### Helper lemmas for sumT_sub_199_bound -/

private lemma log_factorial_ge' (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial) ≥ n * Real.log n - n + 1 := by
  induction hn <;> simp_all +decide [ Nat.factorial ]
  rw [ Real.log_mul ( by positivity ) ( by positivity ) ]
  have h_log : ∀ m : ℕ, 1 ≤ m → Real.log (m + 1) ≤ Real.log m + 1 / m := by
    intro m hm; rw [ Real.log_le_iff_le_exp ( by positivity ) ] ; rw [ Real.exp_add, Real.exp_log ( by positivity ) ]
    nlinarith [ Real.add_one_le_exp ( 1 / ( m : ℝ ) ), one_div_mul_cancel ( by positivity : ( m : ℝ ) ≠ 0 ) ]
  have := h_log _ ‹_›; norm_num at *; nlinarith [ inv_mul_cancel₀ ( by positivity : ( ( Nat.cast:ℕ →ℝ ) ‹_› ) ≠ 0 ) ]

private lemma sumS_ge_log_sub_one (n : ℕ) (hn : 2 ≤ n) :
    sumS n ≥ Real.log n - 1 := by
  have h_sum_floor : ∑ m ∈ Finset.Icc 1 n, vonMangoldt m * Nat.floor (n / m) = Real.log (Nat.factorial n) := by
    have h_sum_floor : ∑ k ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors k, vonMangoldt d = Real.log (Nat.factorial n) := by
      have h_sum_floor : ∀ k ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors k, vonMangoldt d = Real.log k := by
        exact fun _ _ => vonMangoldt_sum
      rw [ Finset.sum_congr rfl h_sum_floor ]
      exact Nat.recOn n ( by norm_num ) fun n ih => by simp_all +decide [ Nat.factorial_succ, Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; linarith
    have h_interchange : ∑ k ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors k, vonMangoldt d = ∑ d ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, vonMangoldt d * (if d ∣ k then 1 else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ]
      simp +contextual [ Finset.sum_ite ]
      intro x hx₁ hx₂; rw [ ← Finset.sum_subset ( show x.divisors ⊆ Finset.filter ( fun d => d ∣ x ) ( Finset.Icc 1 n ) from fun y hy => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Nat.pos_of_mem_divisors hy, Nat.le_trans ( Nat.le_of_dvd hx₁ <| Nat.dvd_of_mem_divisors hy ) hx₂ ⟩, Nat.dvd_of_mem_divisors hy ⟩ ) ] ; aesop
    have h_inner : ∀ d ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, (if d ∣ k then 1 else 0) = Nat.floor (n / d) := by
      intros d hd
      have h_divisors : Finset.filter (fun k => d ∣ k) (Finset.Icc 1 n) = Finset.image (fun k => d * k) (Finset.Icc 1 (n / d)) := by
        ext k; simp [Finset.mem_image]
        exact ⟨ fun h => ⟨ k / d, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( Finset.mem_Icc.mp hd |>.1 ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Finset.mem_Icc.mp hd |>.1 ], by nlinarith [ Finset.mem_Icc.mp hd |>.2, Nat.div_mul_le_self n d ] ⟩, by norm_num ⟩ ⟩
      simp_all +decide [ Finset.sum_ite ]
      rw [ Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ ( by linarith ) hxy ] ; aesop
    simp_all +decide [ Finset.sum_ite ]
    exact Eq.trans ( Finset.sum_congr rfl fun x hx => by rw [ h_inner x ( Finset.mem_Icc.mp hx |>.1 ) ( Finset.mem_Icc.mp hx |>.2 ) ] ; ring ) h_sum_floor
  have h_floor_le : ∑ m ∈ Finset.Icc 1 n, vonMangoldt m * Nat.floor (n / m) ≤ n * ∑ m ∈ Finset.Icc 1 n, vonMangoldt m / (m : ℝ) := by
    rw [ Finset.mul_sum _ _ _ ] ; refine Finset.sum_le_sum fun x hx => ?_ ; rcases eq_or_ne x 0 with rfl | hx' <;> simp_all +decide ; ring_nf
    rw [ mul_assoc ] ; exact mul_le_mul_of_nonneg_left ( by rw [ ← div_eq_mul_inv ] ; exact ( by rw [ le_div_iff₀ ( by positivity ) ] ; norm_cast; linarith [ Nat.div_mul_le_self n x ] ) ) ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by rw [ ArithmeticFunction.vonMangoldt_apply ] ; positivity ) ) ) ) ) ) ) ) ) ) ) ) ) ) )
  have h_sum_eq : ∑ m ∈ Finset.Icc 1 n, vonMangoldt m / (m : ℝ) = sumS n := by
    rw [ Finset.Icc_eq_cons_Ioc ( by linarith ), Finset.sum_cons ] ; aesop
  nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast, Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) ), log_factorial_ge' n ( by linarith ) ]


private lemma div_sub_le_log_sub' {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / b ≤ Real.log b - Real.log a := by
  have h_mul : b - a ≤ b * (Real.log b - Real.log a) := by
    have := Real.log_le_sub_one_of_pos ( div_pos ha ( show 0 < b by linarith ) )
    rw [ Real.log_div ] at this <;> nlinarith [ mul_div_cancel₀ a ( by linarith : b ≠ 0 ) ]
  rwa [ div_le_iff₀' ( by linarith ) ]

private lemma sum_log_ratio_le_log_log' (a n : ℕ) (ha : 3 ≤ a) (hn : a ≤ n) :
    ∑ m ∈ Finset.Ico a n,
      (Real.log (↑m + 1) - Real.log m) / Real.log (↑m + 1) ≤
    Real.log (Real.log n) - Real.log (Real.log a) := by
  have h_term : ∀ m ∈ Finset.Ico a n, (Real.log (m + 1) - Real.log m) / Real.log (m + 1) ≤ Real.log (Real.log (m + 1)) - Real.log (Real.log m) := by
    intro m hm
    rw [ ← Real.log_div ( ne_of_gt <| Real.log_pos <| by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ( ne_of_gt <| Real.log_pos <| by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ]
    convert Real.one_sub_inv_le_log_of_pos _ using 1
    · rw [ inv_div, sub_div, div_self <| ne_of_gt <| Real.log_pos <| by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ]
    · exact div_pos ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ) ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) )
  calc
    ∑ m ∈ Finset.Ico a n,
        (Real.log (↑m + 1) - Real.log m) / Real.log (↑m + 1)
        ≤ ∑ m ∈ Finset.Ico a n,
            (Real.log (Real.log (m + 1)) - Real.log (Real.log m)) :=
      Finset.sum_le_sum h_term
    _ = Real.log (Real.log n) - Real.log (Real.log a) := by
      let F : ℕ → ℝ := fun m => Real.log (Real.log m)
      have htel : ∑ m ∈ Finset.Ico a n, (F (m + 1) - F m) = F n - F a := by
        induction n, hn using Nat.le_induction with
        | base =>
            simp [F]
        | succ n hn ih =>
            rw [Finset.sum_Ico_succ_top hn,
              ih (fun m hm => h_term m (Finset.mem_Ico.mpr
                ⟨(Finset.mem_Ico.mp hm).1, Nat.lt_succ_of_lt (Finset.mem_Ico.mp hm).2⟩))]
            ring
      simpa [F, Nat.cast_add, Nat.cast_one] using htel

private lemma log_200_ge' : Real.log 200 ≥ 1418 / 270 := by
  have h_log_200 : Real.log 200 = 3 * Real.log 2 + 2 * Real.log 5 := by
    norm_num [ ← Real.log_rpow, ← Real.log_mul ]
  rw [ h_log_200, show ( 5 : ℝ ) = 2 ^ 2 * 1.25 by norm_num, Real.log_mul, Real.log_pow ] <;> ring_nf <;> norm_num
  have := Real.log_two_gt_d9 ; norm_num at * ; have := Real.log_inv ( 5 / 4 ) ; norm_num at * ; linarith [ Real.log_le_sub_one_of_pos ( show 0 < 4 / 5 by norm_num ) ]

private lemma abel_identity_sumT (n : ℕ) (hn : 200 ≤ n) :
    ∑ m ∈ Finset.Icc 200 n, (Λ m) / (m * Real.log m) = ((sumS n) - (sumS 199)) / Real.log n + ∑ m ∈ Finset.Ico 200 n, ((sumS m) - (sumS 199)) * (1 / Real.log m - 1 / Real.log (m + 1)) := by
  induction hn with
  | refl =>
    simp [sumS]
    rw [ show ( Finset.Icc 2 200 : Finset ℕ ) = Finset.Icc 2 199 ∪ { 200 } by decide, Finset.sum_union ] <;> norm_num ; ring
  | step hk ih =>
    rename_i k
    simp_all +decide [(Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc)]
    rw [ Finset.sum_Ioc_succ_top ( by linarith ), ‹∑ x ∈ Ioc 199 k, _ = _› ]
    rw [ Finset.sum_Ico_succ_top ( by linarith ), show sumS ( k + 1 ) = sumS k + Λ ( k + 1 ) / ( k + 1 : ℝ ) from ?_ ]
    · norm_num [ div_eq_mul_inv ] ; ring
    · exact_mod_cast Finset.sum_Ioc_succ_top ( by linarith ) _

/-
T(n) - T(199) ≤ log(log n) - log(log 199) + 27/100, using Abel summation and S(m) ≤ log m + 0.418
-/
lemma sumT_sub_199_bound (n : ℕ) (hn : 200 ≤ n) :
    sumT n ≤ sumT 199 + Real.log (Real.log ↑n) - Real.log (Real.log 199) + 27/100 := by
  -- Step 1: Split sumT
  have h_split : sumT n = sumT 199 + ∑ m ∈ Finset.Icc 200 n, vonMangoldt m / (m * Real.log m) := by
    unfold sumT; erw [ Finset.sum_Ico_consecutive ] <;> norm_cast ; linarith
  rw [h_split]
  -- Step 2: Abel summation identity
  have h_identity := abel_identity_sumT n hn
  -- Step 3: Bound the Abel sum terms
  have h_bound : (∑ m ∈ Finset.Ico 200 n, ((sumS m) - (sumS 199)) * (1 / Real.log m - 1 / Real.log (m + 1))) ≤ (∑ m ∈ Finset.Ico 200 n, ((Real.log m - Real.log 199 + 1.418) * (1 / Real.log m - 1 / Real.log (m + 1)))) := by
    refine Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_right ?_ ?_ <;> norm_num at *
    · have := sumS_le_logn_plus m ( by linarith ) ; ( have := sumS_ge_log_sub_one 199 ( by norm_num ) ; ( norm_num at * ; linarith ) )
    · exact inv_anti₀ ( Real.log_pos <| by norm_cast; linarith ) ( Real.log_le_log ( by norm_cast; linarith ) <| by linarith )
  -- Step 4: Expand and telescope the sum
  have h_expand : ∑ m ∈ Finset.Ico 200 n, ((Real.log m - Real.log 199 + 1.418) * (1 / Real.log m - 1 / Real.log (m + 1))) = ∑ m ∈ Finset.Ico 200 n, ((Real.log (m + 1) - Real.log m) / Real.log (m + 1)) + (1.418 - Real.log 199) * (1 / Real.log 200 - 1 / Real.log n) := by
    have h_expand : ∀ m ∈ Finset.Ico 200 n, ((Real.log m - Real.log 199 + 1.418) * (1 / Real.log m - 1 / Real.log (m + 1))) = ((Real.log (m + 1) - Real.log m) / Real.log (m + 1)) + (1.418 - Real.log 199) * (1 / Real.log m - 1 / Real.log (m + 1)) := by
      intro m hm; ring_nf
      rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ) ) ] ; ring
    rw [ Finset.sum_congr rfl h_expand, Finset.sum_add_distrib ]
    norm_num [ Finset.sum_Ico_eq_sum_range ]
    rw [ ← Finset.mul_sum _ _ _ ]
    exact congrArg _ ( by convert Finset.sum_range_sub' _ _ using 3 <;> push_cast [ Nat.cast_sub hn ] <;> ring_nf )
  -- Step 5: Apply log ratio telescoping bound
  have h_log_ratio : ∑ m ∈ Finset.Ico 200 n, ((Real.log (m + 1) - Real.log m) / Real.log (m + 1)) ≤ Real.log (Real.log n) - Real.log (Real.log 200) := by
    simpa using sum_log_ratio_le_log_log' 200 n ( by norm_num ) hn
  -- Step 6: Bound the boundary term
  have h_sumS_le : (sumS n - sumS 199) / Real.log n ≤ (Real.log n + 0.418 - (Real.log 199 - 1)) / Real.log n := by
    gcongr
    · exact sumS_le_logn_plus n hn
    · exact sumS_ge_log_sub_one 199 ( by norm_num )
  -- Step 7: Numerical bound
  have h_num : 1 + (1.418 - Real.log 199) / Real.log 200 + Real.log (Real.log 199) - Real.log (Real.log 200) ≤ 27 / 100 := by
    have h_log_diff : Real.log (Real.log 200) - Real.log (Real.log 199) ≥ (Real.log 200 - Real.log 199) / Real.log 200 := by
      exact div_sub_le_log_sub' ( show 0 < Real.log 199 by positivity ) ( show Real.log 199 ≤ Real.log 200 by gcongr ; norm_num )
    ring_nf at *
    nlinarith [ inv_mul_cancel₀ ( show Real.log 200 ≠ 0 by positivity ), Real.log_pos ( show 199 > 1 by norm_num ), Real.log_lt_log ( by norm_num ) ( show 200 > 199 by norm_num ), show Real.log 200 ≥ 1418 / 270 from log_200_ge' ]
  -- Step 8: Combine all bounds
  ring_nf at *
  nlinarith [ inv_pos.mpr ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ) ), inv_pos.mpr ( Real.log_pos ( show ( 200 : ℝ ) > 1 by norm_num ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ) ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( 200 : ℝ ) > 1 by norm_num ) ) ), Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ), Real.log_pos ( show ( 200 : ℝ ) > 1 by norm_num ) ]

/-
Computational upper bound on T(199)
-/
lemma sumT_199_lt : sumT 199 < 23/10 := by
  -- By definition of sumT, we can rewrite the sum as a sum over prime powers.
  have h_sum_prime_powers : ∀ n : ℕ, sumT n = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (1 / (p^k * k : ℝ)) := by
    intro n
    have h_sumT_prime_powers : ∀ m ∈ Finset.Icc 2 n, vonMangoldt m = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (if m = p^k then Real.log p else 0) := by
      intro m hm
      by_cases hm_prime_power : ∃ p k : ℕ, Nat.Prime p ∧ k ≥ 1 ∧ m = p^k ∧ p^k ≤ n;
      · obtain ⟨ p, k, hp, hk, rfl, hk' ⟩ := hm_prime_power; simp +decide [Finset.sum_ite] ;
        rw [ Finset.sum_eq_single p ];
        · rw [ Finset.card_eq_one.mpr ] <;> norm_num [ hp, hk ];
          · grind +suggestions;
          · exact ⟨ k, Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hk, Nat.le_log_of_pow_le hp.one_lt hk' ⟩, rfl ⟩, fun x hx => Nat.pow_right_injective hp.one_lt <| Finset.mem_filter.mp hx |>.2.symm ⟩ ⟩;
        · intro q hq hqp; simp_all +decide [ Finset.ext_iff ] ;
          exact Or.inl fun a ha₁ ha₂ ha₃ => hqp <| by have := congr_arg ( ·.factorization ( q : ℕ ) ) ha₃; norm_num at this; have := congr_arg ( ·.factorization ( p : ℕ ) ) ha₃; norm_num at this; aesop;
        · exact fun h => False.elim <| h <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.two_le, by linarith [ pow_le_pow_right₀ hp.one_lt.le hk ] ⟩, hp ⟩;
      · rw [ ArithmeticFunction.vonMangoldt_apply ];
        rw [ if_neg ];
        · exact Eq.symm ( Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun k hk => if_neg fun h => hm_prime_power ⟨ p, k, Finset.mem_filter.mp hp |>.2, Finset.mem_Icc.mp hk |>.1, h, by linarith [ Finset.mem_Icc.mp hm, Finset.mem_Icc.mp hk |>.2, Nat.pow_log_le_self p ( show m ≠ 0 by linarith [ Finset.mem_Icc.mp hm ] ) ] ⟩ );
        · contrapose! hm_prime_power;
          rw [ isPrimePow_nat_iff ] at hm_prime_power ; aesop;
    -- By interchanging the order of summation, we can rewrite the sum.
    have h_interchange : ∑ m ∈ Finset.Icc 2 n, (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (if m = p^k then Real.log p else 0)) / (m * Real.log m) = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (Real.log p) / (p^k * Real.log (p^k)) := by
      simp +decide only [Finset.sum_div _ _ _];
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      intro p hp; rw [ Finset.sum_comm ] ; simp +decide [ div_eq_mul_inv ] ;
      exact Finset.sum_congr rfl fun x hx => if_pos ⟨ le_trans ( Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ) ( Nat.le_self_pow ( by linarith [ Finset.mem_Icc.mp hx ] ) _ ), Nat.pow_le_of_le_log ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) ] ) ( by linarith [ Finset.mem_Icc.mp hx ] ) ⟩;
    convert h_interchange using 2;
    · exact Finset.sum_congr rfl fun x hx => h_sumT_prime_powers x hx ▸ rfl;
    · norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
      exact Finset.sum_congr rfl fun _ _ => by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( by aesop ) ) ) ) ) ] ; ring;
  rw [ h_sum_prime_powers ];
  norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
  rw [ show ( Finset.filter Nat.Prime ( Finset.Ioc 1 199 ) ) = { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199 } by decide ] ; simp +decide ;
  norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *

/-
Lower bound on log(log 199)
-/
lemma log_log_199_gt : Real.log (Real.log 199) > 163/100 := by
  -- We'll use that $Real.log 199 > 5.11$.
  have h_log_199 : Real.log 199 > 5.11 := by
    norm_num [ Real.lt_log_iff_exp_lt ];
    -- We can raise both sides to the power of 100 to remove the fraction.
    suffices h_exp : Real.exp 511 < 199 ^ 100 by
      contrapose! h_exp;
      exact le_trans ( pow_le_pow_left₀ ( by norm_num ) h_exp 100 ) ( by norm_num [ ← Real.exp_nat_mul ] );
    have := Real.exp_one_lt_d9.le;
    -- We can raise both sides to the power of 511 to remove the fraction.
    have : Real.exp 511 ≤ (2.7182818286 : ℝ) ^ 511 := by
      exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) this _ );
    grind;
  refine lt_of_lt_of_le ?_ ( Real.log_le_log ( by positivity ) h_log_199.le )
  rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
  have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 163 = ( Real.exp 1 ) ^ 163 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num )

lemma neg_log_prodP_bound (n : ℕ) (hn : 200 ≤ n) :
    -Real.log (prodP n) < Real.log (Real.log n) + 1.095 := by
  have h1 := neg_log_prodP_le_sumT_plus n hn
  have h2 := sumT_sub_199_bound n hn
  have h3 := sumT_199_lt
  have h4 := log_log_199_gt
  -- -log P(n) ≤ T(n) + 1/10
  --           ≤ T(199) + log(log n) - log(log 199) + 27/100 + 1/10
  --           < 23/10 + log(log n) - 163/100 + 27/100 + 1/10
  --           = log(log n) + (2300 + 270 + 100 - 1630)/1000
  --           = log(log n) + 1040/1000 = log(log n) + 1.04
  --           < log(log n) + 1.095
  linarith

/-! # Finite Check -/

lemma prodP_le_of_le {m n : ℕ} (h : m ≤ n) : prodP n ≤ prodP m := by
  unfold prodP;
  rw [ ← Finset.prod_sdiff ( Finset.filter_subset_filter _ <| Finset.range_mono <| Nat.succ_le_succ h ) ];
  exact mul_le_of_le_one_left ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) <| Finset.prod_le_one ( fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) fun _ _ => sub_le_self _ <| by positivity;

lemma mertens_finite_check (n : ℕ) (hn3 : 3 ≤ n) (hn199 : n ≤ 199) :
    1 / (3 * Real.log n) ≤ prodP n := by
  by_cases hn : n ≤ 10;
  · interval_cases n <;> norm_num [ Finset.prod_filter, Finset.prod_range_succ, prodP ];
    any_goals rw [ inv_mul_le_iff₀ ( by positivity ) ];
    any_goals rw [ inv_le_comm₀ ] <;> norm_num [ Real.le_log_iff_exp_le ];
    any_goals rw [ ← div_le_iff₀ ] <;> norm_num [ Real.le_log_iff_exp_le ];
    any_goals positivity;
    any_goals have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 5 : ℝ ) / 4 = 1 + 1 / 4 by norm_num, Real.exp_add ] ; nlinarith [ Real.exp_pos ( 1 / 4 ), Real.exp_neg ( 1 / 4 ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( 1 / 4 ) ) ), Real.add_one_le_exp ( 1 / 4 ), Real.add_one_le_exp ( - ( 1 / 4 ) ) ];
    any_goals have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 35 / 24 : ℝ ) = 1 + 11 / 24 by norm_num, Real.exp_add ] ; nlinarith [ Real.exp_pos ( 11 / 24 ), Real.exp_neg ( 11 / 24 ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( 11 / 24 ) ) ), Real.add_one_le_exp ( 11 / 24 ), Real.add_one_le_exp ( - ( 11 / 24 ) ) ];
    · exact Real.exp_one_lt_d9.le.trans <| by norm_num;
    · exact Real.exp_one_lt_d9.le.trans ( by norm_num );
  · by_cases hn : n ≤ 30;
    · -- For $11 \leq n \leq 30$, we use the fact that $prodP(n) \geq prodP(30)$ and $prodP(30) \geq 1/7$.
      have h_prod_bound : prodP n ≥ prodP 30 := by
        exact prodP_le_of_le hn
      have h_prod_30 : prodP 30 ≥ 1 / 7 := by
        unfold prodP; norm_num [ Finset.prod_filter, Finset.prod_range_succ ] ;
      have h_log_bound : 7 ≤ 3 * Real.log 11 := by
        norm_num [ ← Real.log_rpow, Real.le_log_iff_exp_le ] at *;
        have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 7 = ( Real.exp 1 ) ^ 7 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ;
      have h_final : 1 / (3 * Real.log n) ≤ 1 / 7 := by
        exact one_div_le_one_div_of_le ( by positivity ) ( by linarith [ Real.log_le_log ( by positivity ) ( show ( n : ℝ ) ≥ 11 by norm_cast; linarith ) ] )
      exact le_trans h_final (le_trans h_prod_30 h_prod_bound);
    · have h_prodP_199 : prodP 199 ≥ 1 / 10 := by
        unfold prodP; norm_num;
        norm_num [ Finset.prod_filter, Finset.prod_range_succ ];
      have h_log_bound : Real.log n ≥ 10 / 3 := by
        rw [ ge_iff_le, div_le_iff₀' ] <;> norm_num;
        rw [ ← Real.log_rpow, Real.le_log_iff_exp_le ] <;> norm_cast <;> try linarith;
        · exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 10 = ( Real.exp 1 ) ^ 10 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ) ( Nat.cast_le.mpr ( Nat.pow_le_pow_left ( show n ≥ 31 by linarith ) 3 ) );
        · positivity;
      exact le_trans ( by rw [ div_le_iff₀ ] <;> linarith ) ( h_prodP_199.trans ( prodP_le_of_le ( by linarith ) ) )

/-! # Main Theorem -/

theorem mertens_third_theorem (n : ℕ) (hn : 3 ≤ n) :
    1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  by_cases hn2 : n ≥ 200;
  · have := neg_log_prodP_bound n hn2;
    -- Exponentiating both sides, we get $prodP n > \frac{1}{3 \log n}$.
    have h_exp : prodP n > 1 / (3 * Real.log n) := by
      have h_exp : Real.log (prodP n) > -Real.log (3 * Real.log n) := by
        rw [ Real.log_mul ] <;> norm_num;
        · have h_log3 : Real.log 3 > 1.095 := by
            norm_num [ Real.log_lt_log ];
            rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
            have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 219 = ( Real.exp 1 ) ^ 219 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num );
          linarith;
        · grind;
      rw [ gt_iff_lt, Real.lt_log_iff_exp_lt ] at h_exp;
      · simpa [ Real.exp_neg, Real.exp_log ( show 0 < 3 * Real.log n by exact mul_pos zero_lt_three ( Real.log_pos ( by norm_cast; linarith ) ) ) ] using h_exp;
      · exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Finset.mem_filter.mp hp, Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ;
    exact h_exp.le;
  · -- Apply the finite check lemma to conclude the proof.
    apply mertens_finite_check n hn (by linarith)

end

/-! ### Upstream module `ErdosProblems/Erdos1141.lean` -/

section

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1141.
https://www.erdosproblems.com/forum/thread/1141

Formalization status:
- Unconditional

Informal authors:
- an internal model at OpenAI
- Boris Alexeev
- Moe Putterman
- Mehtaab Sawhney
- Mark Sellke
- Gregory Valiant

Formal authors:
- GPT-5.4 Pro
- Yuta Oriike

URLs:
- https://www.erdosproblems.com/forum/thread/1141#post-5335
- https://github.com/yuta0x89/ErdosProblems/blob/a1319f732cdee5140faf47d984e2c451c1184803/Erdos1141.lean
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1141.lean
-/

/-!
# Erdős Problem 1141

We formalize the `Pa`-variant of Erdős Problem 1141 from the paper
https://arxiv.org/abs/2604.06609 and then deduce the Formal
Conjectures statement.
Fix `a ≥ 1`. Let `Pa a n` denote the property that
`n - a*k^2` is prime for every positive integer `k` with `(k,n)=1` and `a*k^2 < n`.
Then only finitely many `n` satisfy `Pa a n`.

The main development intentionally mirrors the style of Pietro Monticone's
`Erdos237.lean`:

* source: <https://gist.githubusercontent.com/pitmonticone/
  8ea0d1cdb963b6213ac639b11d33f811/raw/
  98a5824d16da14313f65d77eeab5563dd874613a/Erdos237.lean>

* the analytic inputs are proved in supporting modules;
* the rest is organized into helper lemmas matching the paper;
* the medium-weight arithmetic / analytic steps are spelled out in helper lemmas.

## Analytic inputs

1. `Pollack17.theorem_1_3`: Pollack's Theorem 1.3, proved in the literal
   `DirichletCharacter`-based form from Pollack's paper
   <https://www.ams.org/journals/proc/2017-145-07/
   S0002-9939-2016-13432-1/S0002-9939-2016-13432-1.pdf>.
2. `mertens_third_theorem`: the same product bound used in Pietro Monticone's `Erdos237.lean`.

## Proof structure

Given `n`, write `a*n = u^2*d` with `d` squarefree.

* Case 1: `d > 1`.
  Pollack gives an odd prime `p ≲ (4*a*n)^(3/8)` for which `d` is a quadratic residue mod `p`.
  Hence `a*x^2 ≡ n [MOD p]` is solvable.

* Case 2: `d = 1`, so `a*n` is a square.
  We **do not** introduce a separate lemma producing a small odd prime `p ∤ a*n`.
  Instead, factor the fixed coefficient `a = v^2*dₐ` with `dₐ` squarefree.

  - If `dₐ > 1`, then from `a = v^2*dₐ` we get `4*dₐ ∣ 4*a*n`.  Pollack applied to the *fixed*
    squarefree part `dₐ` with modulus `4*a*n` again gives an odd prime `p ≲ (4*a*n)^(3/8)`
    with `p ∤ a*n`.
    Since `a*n` is a square, the congruence `a*x^2 ≡ n [MOD p]` is automatically solvable,
    so the same counting contradiction applies.

  - If `dₐ = 1`, then `a = v^2` is itself a square.  From `a*n = u^2` we deduce that `n`
    is also a square, say `n = m^2`.  Then `k = 1` already gives
    `n - a = m^2 - v^2 = (m-v)(m+v)`, which is composite for all sufficiently large `n`.
-/

open scoped BigOperators
open Finset Real

/-! ## Basic definitions -/

/-- `Pa a n` means that every positive `k` coprime to `n` with `a*k^2 < n`
produces a prime value `n - a*k^2`. -/
def Pa (a n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → Nat.Coprime k n → a * k ^ 2 < n → Nat.Prime (n - a * k ^ 2)

/-- `d` is a quadratic residue modulo `p`.  We use an elementary `Nat.ModEq` formulation,
which is enough for the formalization. -/
def QuadResidueMod (d p : ℕ) : Prop :=
  ∃ x : ℕ, Nat.ModEq p (x ^ 2) d

/-- The congruence `a*x^2 ≡ n [MOD p]` is solvable. -/
def SolvableAX2EqNMod (a n p : ℕ) : Prop :=
  ∃ x : ℕ, Nat.ModEq p (a * x ^ 2) n

/-- The size bound that naturally appears after specializing Pollack with `ε = 1/8`
and `m = 4*a*n`. -/
noncomputable def pollackSizeBound (a n : ℕ) : ℝ :=
  Real.rpow ((4 * a * n : ℕ) : ℝ) ((3 : ℝ) / 8)

/-- Candidate values of `k` used in both cases of the proof.  We range over `k < n`; this is
harmless because `a*k^2 < n` and `a ≥ 1` automatically force `k < n`. -/
def candidateKs (a n p : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun k ↦
    1 ≤ k ∧ a * k ^ 2 < n ∧ Nat.Coprime k n ∧ Nat.ModEq p (a * k ^ 2) n

/-! ## Elementary setup -/

/-- Squarefree-part factorization of a natural number. -/
lemma exists_squarefree_factorization (m : ℕ) :
    ∃ u d : ℕ, u ^ 2 * d = m ∧ Squarefree d := by
  obtain ⟨d, u, h, hd⟩ := Nat.sq_mul_squarefree m
  exact ⟨u, d, h, hd⟩

/-- `1` is always a quadratic residue. -/
private lemma one_is_quad_residue (p : ℕ) : QuadResidueMod 1 p := by
  refine ⟨1, ?_⟩
  simpa using (Nat.ModEq.refl (1 : ℕ))

/-- A squarefree natural different from `1` is `> 1`. -/
lemma one_lt_of_squarefree_ne_one {d : ℕ} (hd : Squarefree d) (h : d ≠ 1) : 1 < d := by
  cases d with
  | zero => exact (hd.ne_zero rfl).elim
  | succ d =>
      cases d with
      | zero => exact (h rfl).elim
      | succ d => exact Nat.succ_lt_succ (Nat.succ_pos _)

/-- The obvious size comparison `n ≤ 4*a*n` for `a ≥ 1`, used to feed Pollack with `m = 4*a*n`. -/
lemma le_pollack_modulus {a n : ℕ} (ha : 1 ≤ a) : n ≤ 4 * a * n := by
  have hmul : 1 ≤ 4 * a := by
    nlinarith
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_right n hmul

/-- If `u^2*d = a*n`, then the conductor-relevant multiple `4*d` divides `4*a*n`. -/
private lemma squarefree_factor_dvd_pollack_modulus {a n u d : ℕ}
    (hdecomp : u ^ 2 * d = a * n) : 4 * d ∣ 4 * a * n := by
  refine ⟨u ^ 2, ?_⟩
  calc
    4 * a * n = 4 * (a * n) := by ac_rfl
    _ = 4 * (u ^ 2 * d) := by rw [← hdecomp]
    _ = (4 * d) * (u ^ 2) := by ac_rfl

/-- If `v^2*d = a`, then the conductor-relevant multiple `4*d` divides `4*a*n`. -/
private lemma squarefree_coeff_dvd_pollack_modulus {a n v d : ℕ}
    (hadecomp : v ^ 2 * d = a) : 4 * d ∣ 4 * a * n := by
  refine ⟨v ^ 2 * n, ?_⟩
  calc
    4 * a * n = 4 * (v ^ 2 * d) * n := by rw [← hadecomp]
    _ = (4 * d) * (v ^ 2 * n) := by ac_rfl

/-- A prime not dividing `4*a*n` certainly does not divide `a*n`. -/
lemma not_dvd_an_of_not_dvd_pollack_modulus {a n p : ℕ}
    (h : ¬ p ∣ 4 * a * n) : ¬ p ∣ a * n := by
  intro hp
  apply h
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using dvd_mul_of_dvd_right hp 4

/-- If the squarefree part of `a` is `1`, then `a` is a square. -/
private lemma coeff_is_square_of_squarefree_part_eq_one {a v d : ℕ}
    (hadecomp : v ^ 2 * d = a)
    (hd1 : d = 1) :
    a = v ^ 2 := by
  simpa [hd1] using hadecomp.symm

/-- A square root in `ZMod p` yields a witness for `QuadResidueMod d p`. -/
private lemma quadResidueMod_of_isSquare_zmod {d p : ℕ} (h : IsSquare (d : ZMod p)) :
    QuadResidueMod d p := by
  rcases h with ⟨x, hx⟩
  cases p with
  | zero =>
      refine ⟨x.val, ?_⟩
      rw [Nat.ModEq, Nat.mod_zero, Nat.mod_zero]
      simpa [pow_two] using congrArg ZMod.val hx.symm
  | succ p =>
      refine ⟨x.val, ?_⟩
      rw [← ZMod.natCast_eq_natCast_iff]
      calc
        (((x.val ^ 2 : ℕ) : ZMod (p + 1))) = (((x.val : ℕ) : ZMod (p + 1)) ^ 2) := by
          simp
        _ = x ^ 2 := by
          simp
        _ = (d : ZMod (p + 1)) := by
          simpa [pow_two] using hx.symm

/-! ## Bridge from Pollack's literal theorem to the Jacobi-symbol specialization -/

/-- If the attached character takes the value `1` at a prime `p`, then `p` is an odd prime
not dividing `m`, and `d` is a quadratic residue modulo `p`.

This is the exact downstream interface needed in the two contradiction arguments. -/
private lemma attachedQuadraticCharacter_spec
    {d m p : ℕ} (hdvd : 4 * d ∣ m)
    (hp : p.Prime)
    (hχ : attachedQuadraticCharacter d m hdvd p = 1) :
    p ≠ 2 ∧ ¬ p ∣ m ∧ QuadResidueMod d p := by
  have hcop : Nat.Coprime p m := by
    by_contra hnot
    have hzero : attachedQuadraticCharacter d m hdvd p = 0 := by
      simp [attachedQuadraticCharacter, hnot]
    have h01 : (0 : ℤ) = 1 := by
      rw [hzero] at hχ
      exact hχ
    norm_num at h01
  have hpndvd : ¬ p ∣ m := (hp.coprime_iff_not_dvd).1 hcop
  have hp2 : p ≠ 2 := by
    intro hp2
    apply hpndvd
    simpa [hp2] using two_dvd_of_four_d_dvd hdvd
  have hJacobi : jacobiSym (d : ℤ) p = 1 := by
    rw [attachedQuadraticCharacter_apply_coprime hdvd hcop] at hχ
    exact hχ
  have : Fact p.Prime := ⟨hp⟩
  have hsqInt : IsSquare ((d : ℤ) : ZMod p) :=
    ZMod.isSquare_of_jacobiSym_eq_one (a := (d : ℤ)) (p := p) hJacobi
  have hsq : IsSquare (d : ZMod p) := by
    rcases hsqInt with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa using hx
  exact ⟨hp2, hpndvd, quadResidueMod_of_isSquare_zmod hsq⟩

/-! ## Pollack specialized to the exact bound used in the paper -/

/-- The `A = 1`, `ε = 1/8` specialization of Pollack, reduced to the only output needed later:
the existence of one Pollack-sized odd prime with `d` a quadratic residue modulo `p`.

This is the abstraction boundary for the rest of the file.  All later arguments use only this
lemma, and never the full cardinality statement of `Pollack17.theorem_1_3`. -/
lemma exists_small_prime_from_pollack :
    ∃ M0 : ℕ, ∀ {m d : ℕ}, M0 ≤ m → 4 * d ∣ m →
      ∃ p : ℕ,
        p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ m ∧
        (p : ℝ) ≤ Real.rpow (m : ℝ) ((3 : ℝ) / 8) ∧
        QuadResidueMod d p := by
  classical
  obtain ⟨m0, hm0⟩ :=
    Pollack17.theorem_1_3 ((1 : ℝ) / 8) 1 (by norm_num) (by norm_num)
  refine ⟨max (m0 + 1) 2, ?_⟩
  intro m d hm hdvd
  have hm2 : 2 ≤ m := le_trans (le_max_right _ _) hm
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm2
  have : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  set χ : QuadraticCharacterMod m := attachedQuadraticCharacter d m hdvd
  set P : Finset ℕ :=
    Pollack17.residuePrimesUpTo m χ.toDirichletCharacterComplex ((1 : ℝ) / 8)
  have hgt : m > m0 := by
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self m0) (le_trans (le_max_left _ _) hm)
  have hcard : Real.rpow (Real.log (m : ℝ)) 1 ≤ (P.card : ℝ) := by
    simpa [P] using
      hm0 m hgt χ.toDirichletCharacterComplex χ.toDirichletCharacterComplex_isQuadratic
  have hcard' : Real.log (m : ℝ) ≤ (P.card : ℝ) := by
    simpa using hcard
  have hm1_real : (1 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hm2)
  have hlog_pos : 0 < Real.log (m : ℝ) := Real.log_pos hm1_real
  have hcard_pos : 0 < P.card := by
    by_contra hcard_not
    have hcard0 : P.card = 0 := Nat.eq_zero_of_not_pos hcard_not
    have hcard_pos_real : (0 : ℝ) < (P.card : ℝ) := lt_of_lt_of_le hlog_pos hcard'
    have : (0 : ℝ) < 0 := by
      rw [hcard0] at hcard_pos_real
      norm_num at hcard_pos_real
    exact (lt_irrefl (0 : ℝ)) this
  obtain ⟨p, hpP⟩ := Finset.card_pos.mp hcard_pos
  have hpP' : p ∈ Pollack17.residuePrimesUpTo m χ.toDirichletCharacterComplex ((1 : ℝ) / 8) := by
    simpa [P] using hpP
  have hpP'' := Finset.mem_filter.mp (show p ∈
    (Finset.range
      (Nat.ceil
        (Pollack17.residuePrimeUpperBound m ((1 : ℝ) / 8)) + 1)).filter
      (fun ℓ => Nat.Prime ℓ ∧
        (ℓ : ℝ) ≤ Pollack17.residuePrimeUpperBound m ((1 : ℝ) / 8) ∧
        χ.toDirichletCharacterComplex (ℓ : ZMod m) = (1 : ℂ)) from hpP')
  rcases hpP''.2 with ⟨hpp, hpbound, hχpComplex⟩
  have hχp : χ p = 1 := by
    exact χ.eq_one_of_toDirichletCharacterComplex_apply_nat_eq_one
      (n := p) (by simpa using hχpComplex)
  have hspec : p ≠ 2 ∧ ¬ p ∣ m ∧ QuadResidueMod d p := by
    simpa [χ] using attachedQuadraticCharacter_spec (d := d) (m := m) (p := p) hdvd hpp hχp
  rcases hspec with ⟨hp2, hpndvd, hres⟩
  refine ⟨p, hpp, hp2, hpndvd, ?_, hres⟩
  rw [Pollack17.residuePrimeUpperBound] at hpbound
  convert hpbound using 1
  norm_num

/-! ## Turning quadratic residuosity into solvability of `a*x^2 ≡ n [MOD p]` -/

/-- In the non-square case, Pollack gives `d` as a quadratic residue.  Combined with
`u^2*d = a*n` and `p ∤ a*n`, this yields solvability of `a*x^2 ≡ n [MOD p]`. -/
lemma solvable_of_squarefree_part
    {a n u d p : ℕ}
    (hdecomp : u ^ 2 * d = a * n)
    (hp : p.Prime)
    (hpn : ¬ p ∣ a * n)
    (hres : QuadResidueMod d p) :
    SolvableAX2EqNMod a n p := by
  obtain ⟨y, hy⟩ := hres
  have hpa : ¬ p ∣ a := by
    intro hpa
    exact hpn (dvd_mul_of_dvd_left hpa n)
  have hcop : Nat.Coprime a p := (hp.coprime_iff_not_dvd.2 hpa).symm
  have hfermat : Nat.ModEq p (a ^ (p - 1)) 1 :=
    Nat.ModEq.pow_card_sub_one_eq_one hp hcop
  let b : ℕ := a * a ^ (p - 2)
  have hp2le : 2 ≤ p := hp.two_le
  have hp_sub : p - 1 = (p - 2) + 1 := by
    omega
  have hb : Nat.ModEq p b 1 := by
    dsimp [b]
    simpa [hp_sub, Nat.pow_add, pow_one, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      hfermat
  have hb2 : Nat.ModEq p (b ^ 2) 1 := by
    simpa using Nat.ModEq.pow 2 hb
  have hsq : Nat.ModEq p ((u * y) ^ 2) (a * n) := by
    have hmul : Nat.ModEq p (u ^ 2 * y ^ 2) (u ^ 2 * d) := hy.mul_left (u ^ 2)
    have hmul' : Nat.ModEq p ((u * y) ^ 2) (u ^ 2 * d) := by
      simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
    rw [← hdecomp]
    exact hmul'
  let x : ℕ := u * y * a ^ (p - 2)
  have hax : Nat.ModEq p (a * x ^ 2) (n * b ^ 2) := by
    have hmul :
        Nat.ModEq p (((u * y) ^ 2) * (a ^ (p - 2)) ^ 2)
          ((a * n) * (a ^ (p - 2)) ^ 2) :=
      hsq.mul_right ((a ^ (p - 2)) ^ 2)
    have hmul' :
        Nat.ModEq p (a * (((u * y) ^ 2) * (a ^ (p - 2)) ^ 2))
          (a * ((a * n) * (a ^ (p - 2)) ^ 2)) :=
      hmul.mul_left a
    simpa [x, b, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul'
  have hnb : Nat.ModEq p (n * b ^ 2) n := by
    simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hb2.mul_left n
  exact ⟨x, hax.trans hnb⟩

/-- In the square case `a*n = u^2`, every odd prime `p ∤ a*n` makes `a*x^2 ≡ n [MOD p]`
solvable. -/
private lemma solvable_of_square_case
    {a n u p : ℕ}
    (hsq : u ^ 2 = a * n)
    (hp : p.Prime)
    (hpn : ¬ p ∣ a * n) :
    SolvableAX2EqNMod a n p := by
  have hdecomp : u ^ 2 * 1 = a * n := by
    simpa using hsq
  exact solvable_of_squarefree_part hdecomp hp hpn (one_is_quad_residue p)

/-! ## Candidate set bounds -/

/-- If `Pa a n` holds, then for any prime `p` there is at most one candidate `k`.
Indeed, `p ∣ n - a*k^2` and primality force `n - a*k^2 = p`, and that equation has at most one
positive solution in `k`. -/
private lemma candidateKs_card_le_one
    {a n p : ℕ}
    (ha : 1 ≤ a)
    (hPa : Pa a n)
    (hp : p.Prime) :
    (candidateKs a n p).card ≤ 1 := by
  refine Finset.card_le_one.2 ?_
  intro k1 hk1 k2 hk2
  rw [candidateKs, Finset.mem_filter] at hk1 hk2
  rcases hk1 with ⟨_, hk1_pos, hk1_lt, hk1_coprime, hk1_mod⟩
  rcases hk2 with ⟨_, hk2_pos, hk2_lt, hk2_coprime, hk2_mod⟩
  have hprime1 : Nat.Prime (n - a * k1 ^ 2) := hPa k1 hk1_pos hk1_coprime hk1_lt
  have hprime2 : Nat.Prime (n - a * k2 ^ 2) := hPa k2 hk2_pos hk2_coprime hk2_lt
  have hdiv1 : p ∣ n - a * k1 ^ 2 :=
    (Nat.modEq_iff_dvd' (Nat.le_of_lt hk1_lt)).1 hk1_mod
  have hdiv2 : p ∣ n - a * k2 ^ 2 :=
    (Nat.modEq_iff_dvd' (Nat.le_of_lt hk2_lt)).1 hk2_mod
  have hEq1 : p = n - a * k1 ^ 2 := (Nat.prime_dvd_prime_iff_eq hp hprime1).1 hdiv1
  have hEq2 : p = n - a * k2 ^ 2 := (Nat.prime_dvd_prime_iff_eq hp hprime2).1 hdiv2
  let t1 : ℕ := a * k1 ^ 2
  let t2 : ℕ := a * k2 ^ 2
  have ht1lt : t1 < n := by
    simpa [t1] using hk1_lt
  have ht2lt : t2 < n := by
    simpa [t2] using hk2_lt
  have ht1eq : p = n - t1 := by
    simpa [t1] using hEq1
  have ht2eq : p = n - t2 := by
    simpa [t2] using hEq2
  have ht12 : t1 = t2 := by
    omega
  have hsq_eq : k1 ^ 2 = k2 ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.succ_le_iff.mp ha)
    simpa [t1, t2] using ht12
  exact Nat.pow_left_injective (show (2 : ℕ) ≠ 0 by decide) hsq_eq

/-! ### Counting helpers for `many_candidates_of_pollack_size` -/

private lemma factorial_card_le_prod_of_one_le (s : Finset ℕ)
    (hs : ∀ x ∈ s, 1 ≤ x) :
    Nat.factorial s.card ≤ ∏ x ∈ s, x := by
  classical
  let f : Fin s.card ↪o ℕ := s.orderEmbOfFin rfl
  have hidx : ∀ i : ℕ, ∀ hi : i < s.card, i + 1 ≤ f ⟨i, hi⟩ := by
    intro i hi
    induction i with
    | zero =>
        have hmem : f ⟨0, hi⟩ ∈ s := by
          simp [f]
        simpa [f] using hs (f ⟨0, hi⟩) hmem
    | succ i ih =>
        have hi' : i < s.card := Nat.lt_of_succ_lt hi
        have hprev : i + 1 ≤ f ⟨i, hi'⟩ := ih hi'
        have hlt : f ⟨i, hi'⟩ < f ⟨i + 1, hi⟩ := by
          exact f.strictMono (Nat.lt_succ_self i)
        exact le_trans (Nat.succ_le_succ hprev) (Nat.succ_le_of_lt hlt)
  have hprod : (∏ i : Fin s.card, (i.1 + 1)) ≤ ∏ i : Fin s.card, f i := by
    refine Finset.prod_le_prod' ?_
    intro i _
    exact hidx i.1 i.2
  have hleft : (∏ i : Fin s.card, (i.1 + 1)) = Nat.factorial s.card := by
    calc
      (∏ i : Fin s.card, (i.1 + 1)) = ∏ i ∈ Finset.range s.card, (i + 1) := by
        simpa using (Fin.prod_univ_eq_prod_range (fun i : ℕ => i + 1) s.card)
      _ = Nat.factorial s.card := Finset.prod_range_add_one_eq_factorial s.card
  have hright : (∏ i : Fin s.card, f i) = ∏ x ∈ s, x := by
    calc
      (∏ i : Fin s.card, f i) =
        ∏ x ∈ Finset.map (s.orderEmbOfFin rfl).toEmbedding Finset.univ, x := by
        symm
        simpa [f] using
          (Finset.prod_map (s := Finset.univ) (e := (s.orderEmbOfFin rfl).toEmbedding)
            (f := fun x : ℕ => x))
      _ = ∏ x ∈ s, x := by
        rw [Finset.map_orderEmbOfFin_univ (s := s) (h := rfl)]
  calc
    Nat.factorial s.card = ∏ i : Fin s.card, (i.1 + 1) := hleft.symm
    _ ≤ ∏ i : Fin s.card, f i := hprod
    _ = ∏ x ∈ s, x := hright

private lemma factorial_card_primeFactors_le (n : ℕ) (hn : n ≠ 0) :
    Nat.factorial n.primeFactors.card ≤ n := by
  have h1 : Nat.factorial n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
    factorial_card_le_prod_of_one_le _ (by
      intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).one_le)
  exact le_trans h1 (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n))

private lemma two_pow_primeFactors_card_le_rpow_sixteenth_eventually :
    ∃ Nω : ℕ, ∀ {n : ℕ}, Nω ≤ n →
      (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) ^ ((1 : ℝ) / 16) := by
  have hfact : ∀ᶠ k : ℕ in Filter.atTop, (2 ^ 16) ^ k < Nat.factorial (k - 1) := by
    simpa using (Nat.eventually_pow_lt_factorial_sub 65536 1)
  rcases Filter.eventually_atTop.mp hfact with ⟨k0, hk0⟩
  refine ⟨max 3 ((2 ^ k0) ^ 16), ?_⟩
  intro n hn
  let k := n.primeFactors.card
  have hn3 : 3 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnpos : 0 < n := by omega
  by_cases hk_small : k < k0
  · have hk_le : k ≤ k0 := hk_small.le
    have hpow_nat : (2 ^ k : ℕ) ≤ 2 ^ k0 :=
      Nat.pow_le_pow_right Nat.zero_lt_two hk_le
    have hpow_real : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k0 := by
      exact_mod_cast hpow_nat
    have hconst_nat : ((2 ^ k0 : ℕ) ^ 16) ≤ n :=
      le_trans (Nat.le_max_right _ _) hn
    have hconst16_real : (((2 : ℝ) ^ k0) ^ (16 : ℕ)) ≤ (n : ℝ) := by
      exact_mod_cast hconst_nat
    have hconst_le' :
        (((2 : ℝ) ^ k0) ^ (16 : ℕ)) ^ ((1 : ℝ) / 16) ≤
          (n : ℝ) ^ ((1 : ℝ) / 16) := by
      exact Real.rpow_le_rpow
        (show 0 ≤ (((2 : ℝ) ^ k0) ^ (16 : ℕ)) by positivity)
        hconst16_real
        (by norm_num : 0 ≤ ((1 : ℝ) / 16))
    have hnonneg_k0 : 0 ≤ (2 : ℝ) ^ k0 := by positivity
    have hroot : (((2 : ℝ) ^ k0) ^ (16 : ℕ)) ^ ((1 : ℝ) / 16) = (2 : ℝ) ^ k0 := by
      simpa [one_div] using Real.pow_rpow_inv_natCast hnonneg_k0 (by norm_num : (16 : ℕ) ≠ 0)
    rw [hroot] at hconst_le'
    exact hpow_real.trans hconst_le'
  · have hk_ge : k0 ≤ k := Nat.le_of_not_gt hk_small
    have hmain_nat : (2 ^ 16) ^ k < Nat.factorial k := by
      exact lt_of_lt_of_le (hk0 k hk_ge) (Nat.factorial_le (Nat.sub_le _ _))
    have hk_fact_le_n : Nat.factorial k ≤ n := by
      simpa [k] using factorial_card_primeFactors_le n (Nat.ne_of_gt hnpos)
    have hpow16_nat' : (2 ^ 16) ^ k ≤ n := le_trans (Nat.le_of_lt hmain_nat) hk_fact_le_n
    have hpow16_nat : (2 ^ k : ℕ) ^ 16 ≤ n := by
      calc
        (2 ^ k : ℕ) ^ 16 = 2 ^ (k * 16) := by rw [pow_mul]
        _ = 2 ^ (16 * k) := by rw [Nat.mul_comm]
        _ = (2 ^ 16) ^ k := by rw [pow_mul]
        _ ≤ n := hpow16_nat'
    have hpow16_real : (((2 : ℝ) ^ k) ^ (16 : ℕ)) ≤ (n : ℝ) := by
      exact_mod_cast hpow16_nat
    have hgoal' :
        (((2 : ℝ) ^ k) ^ (16 : ℕ)) ^ ((1 : ℝ) / 16) ≤
          (n : ℝ) ^ ((1 : ℝ) / 16) := by
      exact Real.rpow_le_rpow
        (show 0 ≤ (((2 : ℝ) ^ k) ^ (16 : ℕ)) by positivity)
        hpow16_real
        (by norm_num : 0 ≤ ((1 : ℝ) / 16))
    have hnonneg_k : 0 ≤ (2 : ℝ) ^ k := by positivity
    have hroot : (((2 : ℝ) ^ k) ^ (16 : ℕ)) ^ ((1 : ℝ) / 16) = (2 : ℝ) ^ k := by
      simpa [one_div] using Real.pow_rpow_inv_natCast hnonneg_k (by norm_num : (16 : ℕ) ≠ 0)
    rw [hroot] at hgoal'
    exact hgoal'

private lemma nat_rpow_sixteenth_div_log_eventually_large (N : ℝ) :
    ∃ N0 : ℕ, 3 ≤ N0 ∧ ∀ n : ℕ, N0 ≤ n →
      N ≤ (n : ℝ) ^ ((1 : ℝ) / 16) / (3 * Real.log n) := by
  have h_tend : Filter.Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 16) / (3 * Real.log n))
      Filter.atTop Filter.atTop := by
    have h_aux : Filter.Tendsto (fun u : ℝ ↦ Real.exp u / (48 * u)) Filter.atTop Filter.atTop := by
      have h1 : Filter.Tendsto (fun u : ℝ ↦ Real.exp u / u) Filter.atTop Filter.atTop := by
        simpa using Real.tendsto_exp_div_pow_atTop 1
      convert Filter.Tendsto.atTop_div_const (show 0 < (48 : ℝ) by norm_num) h1 using 1 with u
      ring_nf
    have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log n / 16) Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.atTop_div_const (show 0 < (16 : ℝ) by norm_num) <|
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact (h_aux.comp hlog).congr' (by
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hlog16 : Real.log n / 16 = Real.log n * ((1 : ℝ) / 16) := by ring
      have hden' : 48 * (Real.log n * ((1 : ℝ) / 16)) = 3 * Real.log n := by ring
      simp only [Function.comp_apply]
      rw [Real.rpow_def_of_pos hn', hlog16, hden'])
  rcases Filter.eventually_atTop.1 (h_tend.eventually_ge_atTop N) with ⟨N0, hN0⟩
  refine ⟨max N0 3, le_max_right _ _, ?_⟩
  intro n hn
  exact hN0 n (le_trans (le_max_left _ _) hn)

private lemma mem_finset_inf_iff {ι α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset ι} {f : ι → Finset α} {a : α} :
    a ∈ s.inf f ↔ ∀ i ∈ s, a ∈ f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert b s hb ih =>
      simp [Finset.inf_insert, ih]

private lemma count_root_class_with_divisors
    {n p r K : ℕ} (hp : p.Prime) (_hn0 : n ≠ 0) (hpn : ¬ p ∣ n)
    (t : Finset ℕ) (ht : t ⊆ n.primeFactors) :
    ∃ v : ℕ,
      #{k ∈ (Finset.range K) | Nat.ModEq p k r ∧ ∀ q ∈ t, q ∣ k}
        = K.count (· ≡ v [MOD p * ∏ q ∈ t, q]) := by
  classical
  let d : ℕ := ∏ q ∈ t, q
  have hp_coprime_d : Nat.Coprime p d := by
    refine Nat.coprime_prod_right_iff.mpr ?_
    intro q hq
    have hqmem : q ∈ n.primeFactors := ht hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hpq : p ≠ q := by
      intro hpq
      apply hpn
      simpa [hpq] using (Nat.dvd_of_mem_primeFactors hqmem)
    exact (Nat.coprime_primes hp hqprime).2 hpq
  have hpair : Set.Pairwise (↑t : Set ℕ) (fun q q' : ℕ ↦ Nat.Coprime q q') := by
    intro q hq q' hq' hqq'
    exact (Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors (ht hq))
      (Nat.prime_of_mem_primeFactors (ht hq'))).2 hqq'
  have hlcm : t.lcm (fun q : ℕ ↦ q) = d := by
    simpa [d] using (Finset.lcm_eq_prod (s := t) (f := fun q : ℕ ↦ q) hpair)
  have hdiv_iff : ∀ k : ℕ, (∀ q ∈ t, q ∣ k) ↔ d ∣ k := by
    intro k
    simpa [d, hlcm] using
      (Finset.lcm_dvd_iff (s := t) (f := fun q : ℕ ↦ q) (a := k)).symm
  let v : ℕ := Nat.chineseRemainder hp_coprime_d r 0
  have hvp : Nat.ModEq p v r := by
    simpa [v] using (Nat.chineseRemainder hp_coprime_d r 0).prop.1
  have hvd : Nat.ModEq d v 0 := by
    simpa [v] using (Nat.chineseRemainder hp_coprime_d r 0).prop.2
  refine ⟨v, ?_⟩
  rw [Nat.count_eq_card_filter_range]
  apply congrArg Finset.card
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hkK, hkpr, hkt⟩
    refine ⟨hkK, ?_⟩
    have hk0 : d ∣ k := (hdiv_iff k).1 hkt
    simpa [d, v] using
      (Nat.chineseRemainder_modEq_unique hp_coprime_d hkpr
        (Nat.modEq_zero_iff_dvd.2 hk0))
  · rintro ⟨hkK, hk⟩
    have hk' : Nat.ModEq p k v ∧ Nat.ModEq d k v := by
      have hk'' : Nat.ModEq (p * d) k v := by
        simpa [d] using hk
      exact (Nat.modEq_and_modEq_iff_modEq_mul hp_coprime_d).mpr hk''
    refine ⟨hkK, hk'.1.trans hvp, ?_⟩
    exact (hdiv_iff k).2 <| Nat.modEq_zero_iff_dvd.1 (hk'.2.trans hvd)

private lemma root_class_good_count_lower_bound
    {a n p r K : ℕ}
    (_ha : 1 ≤ a)
    (hn3 : 3 ≤ n)
    (hp : p.Prime)
    (hpndvd : ¬ p ∣ a * n)
    (_hroot : Nat.ModEq p (a * r ^ 2) n)
    (_hK : K = Nat.sqrt ((n - 1) / a) + 1) :
    let U : Finset ℕ := ((Finset.range K).filter fun k ↦ Nat.ModEq p k r)
    let α := {k : ℕ // k ∈ U}
    let emb : α ↪ ℕ :=
      ⟨Subtype.val, by
        intro x y h
        exact Subtype.ext h⟩
    let S : ℕ → Finset α := fun q ↦ (Finset.univ : Finset α).filter fun k ↦ q ∣ (k : ℕ)
    let good : Finset α := n.primeFactors.inf fun q ↦ (S q)ᶜ
    ((good.map emb).card : ℝ)
      ≥ (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ))
          - (2 : ℝ) ^ n.primeFactors.card := by
  classical
  let U : Finset ℕ := ((Finset.range K).filter fun k ↦ Nat.ModEq p k r)
  let α := {k : ℕ // k ∈ U}
  let emb : α ↪ ℕ :=
    ⟨Subtype.val, by
      intro x y h
      exact Subtype.ext h⟩
  let S : ℕ → Finset α := fun q ↦ (Finset.univ : Finset α).filter fun k ↦ q ∣ (k : ℕ)
  let good : Finset α := n.primeFactors.inf fun q ↦ (S q)ᶜ
  change ((good.map emb).card : ℝ)
      ≥ (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ))
          - (2 : ℝ) ^ n.primeFactors.card
  have hn0 : n ≠ 0 := by omega
  have hpn : ¬ p ∣ n := by
    intro hpn
    exact hpndvd (dvd_mul_of_dvd_right hpn a)
  have hIE : ((good.map emb).card : ℤ) =
      ∑ t ∈ n.primeFactors.powerset, (-1 : ℤ) ^ t.card * ((t.inf S).card : ℤ) := by
    rw [Finset.card_map]
    simpa [good] using
      (Finset.inclusion_exclusion_card_inf_compl (s := n.primeFactors) (S := S))
  have hIE_real : ((good.map emb).card : ℝ) =
      ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((t.inf S).card : ℝ) := by
    exact_mod_cast hIE
  have hterm :
      ∀ t ∈ n.primeFactors.powerset,
        (-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q)) - 1 ≤
          (-1 : ℝ) ^ t.card * ((t.inf S).card : ℝ) := by
    intro t ht
    have htsub : t ⊆ n.primeFactors := Finset.mem_powerset.mp ht
    obtain ⟨v, hv⟩ :=
      count_root_class_with_divisors (n := n) (p := p) (r := r) (K := K) hp hn0 hpn t htsub
    have hmap :
        (t.inf S).map emb =
          (Finset.range K).filter fun k ↦ Nat.ModEq p k r ∧ ∀ q ∈ t, q ∣ k := by
      ext k
      constructor
      · intro hk
        rcases Finset.mem_map.mp hk with ⟨x, hx, rfl⟩
        have hxU : (x : ℕ) ∈ U := x.property
        rcases Finset.mem_filter.mp hxU with ⟨hxK, hxr⟩
        have hxdiv : ∀ q ∈ t, q ∣ (x : ℕ) := by
          intro q hq
          have hxq : x ∈ S q :=
            (mem_finset_inf_iff (s := t) (f := S) (a := x)).1 hx q hq
          simpa [S] using hxq
        exact Finset.mem_filter.mpr ⟨hxK, ⟨hxr, hxdiv⟩⟩
      · intro hk
        rcases Finset.mem_filter.mp hk with ⟨hkK, hkcond⟩
        rcases hkcond with ⟨hkr, hkdiv⟩
        have hkU : k ∈ U := Finset.mem_filter.mpr ⟨hkK, hkr⟩
        let x : α := ⟨k, hkU⟩
        have hx : x ∈ t.inf S := by
          refine (mem_finset_inf_iff (s := t) (f := S) (a := x)).2 ?_
          intro q hq
          simpa [x, S] using hkdiv q hq
        exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    have hcard_map :
        ((t.inf S).map emb).card = K.count (· ≡ v [MOD p * ∏ q ∈ t, q]) := by
      simpa [hmap] using hv
    have hcard_eq_count :
        (t.inf S).card = K.count (· ≡ v [MOD p * ∏ q ∈ t, q]) := by
      simpa using hcard_map
    let m : ℕ := p * ∏ q ∈ t, q
    have hm_pos : 0 < m := by
      dsimp [m]
      refine Nat.mul_pos hp.pos ?_
      refine Finset.prod_pos ?_
      intro q hq
      exact (Nat.prime_of_mem_primeFactors (htsub hq)).pos
    have hcount_formula :
        (t.inf S).card = K / m + if v % m < K % m then 1 else 0 := by
      rw [hcard_eq_count, Nat.count_modEq_card (b := K) (r := m) (hr := hm_pos) v]
    have hcount_formula_real :
        ((t.inf S).card : ℝ) =
          ((K / m : ℕ) : ℝ) + ((if v % m < K % m then 1 else 0 : ℕ) : ℝ) := by
      exact_mod_cast hcount_formula
    have hdiv_le : ((K / m : ℕ) : ℝ) ≤ (K : ℝ) / m := Nat.cast_div_le
    have hm_posR : (0 : ℝ) < m := by exact_mod_cast hm_pos
    have hlt_nat : K < (K / m + 1) * m := by
      exact (Nat.div_lt_iff_lt_mul hm_pos).mp (Nat.lt_succ_self _)
    have hlt_real : (K : ℝ) < ((((K / m : ℕ) : ℝ) + 1) * m) := by
      exact_mod_cast hlt_nat
    have hdiv_lt : (K : ℝ) / m < ((K / m : ℕ) : ℝ) + 1 := by
      exact (div_lt_iff₀ hm_posR).2 hlt_real
    have hbit_nonneg :
        (0 : ℝ) ≤ ((if v % m < K % m then 1 else 0 : ℕ) : ℝ) := by
      by_cases h : v % m < K % m
      · simp [h]
      · simp [h]
    have hbit_le_one :
        ((if v % m < K % m then 1 else 0 : ℕ) : ℝ) ≤ 1 := by
      by_cases h : v % m < K % m
      · simp [h]
      · simp [h]
    have hlower : (K : ℝ) / m - 1 ≤ ((t.inf S).card : ℝ) := by
      rw [hcount_formula_real]
      have hq_ge : (K : ℝ) / m - 1 ≤ (K / m : ℝ) := by
        linarith
      linarith
    have hupper : ((t.inf S).card : ℝ) ≤ (K : ℝ) / m + 1 := by
      rw [hcount_formula_real]
      linarith
    rcases neg_one_pow_eq_or ℝ t.card with hsgn | hsgn
    · rw [hsgn]
      simpa [m] using hlower
    · rw [hsgn]
      have hupper' : ((t.inf S).card : ℝ) ≤ (K : ℝ) / (p * ∏ q ∈ t, q) + 1 := by
        simpa [m] using hupper
      linarith
  have hsum_lower :
      ∑ t ∈ n.primeFactors.powerset,
        ((-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q)) - 1)
        ≤ ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((t.inf S).card : ℝ) := by
    exact Finset.sum_le_sum (fun t ht ↦ hterm t ht)
  have hsum_lower' :
      ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q))
        - ∑ t ∈ n.primeFactors.powerset, (1 : ℝ)
        ≤ ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((t.inf S).card : ℝ) := by
    simpa [Finset.sum_sub_distrib] using hsum_lower
  have hmain_expand :
      ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q))
        = (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) := by
    calc
      ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q))
          = ∑ t ∈ n.primeFactors.powerset,
              (-1 : ℝ) ^ t.card * ((K : ℝ) / p * ∏ q ∈ t, (1 / (q : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              have htsub : t ⊆ n.primeFactors := Finset.mem_powerset.mp ht
              have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
              have hprod_pos : 0 < ∏ q ∈ t, (q : ℝ) := by
                refine Finset.prod_pos ?_
                intro q hq
                exact_mod_cast (Nat.prime_of_mem_primeFactors (htsub hq)).pos
              have hprod_ne0 : (∏ q ∈ t, (q : ℝ)) ≠ 0 := by
                exact ne_of_gt hprod_pos
              have hprod_inv :
                  ∏ q ∈ t, (1 / (q : ℝ)) = 1 / ∏ q ∈ t, (q : ℝ) := by
                calc
                  ∏ q ∈ t, (1 / (q : ℝ)) = ∏ q ∈ t, ((q : ℝ)⁻¹) := by
                    simp [one_div]
                  _ = (∏ q ∈ t, (q : ℝ))⁻¹ := by
                    rw [Finset.prod_inv_distrib]
                  _ = 1 / ∏ q ∈ t, (q : ℝ) := by
                    simp [one_div]
              rw [hprod_inv]
              have hcast_prod : ((∏ q ∈ t, q : ℕ) : ℝ) = ∏ q ∈ t, (q : ℝ) := by
                simp
              rw [hcast_prod]
              field_simp [hp0, hprod_ne0]
      _ = ∑ t ∈ n.primeFactors.powerset,
            (K : ℝ) / p * ((-1 : ℝ) ^ t.card * ∏ q ∈ t, (1 / (q : ℝ))) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          ring
      _ = (K : ℝ) / p * ∑ t ∈ n.primeFactors.powerset,
            (-1 : ℝ) ^ t.card * ∏ q ∈ t, (1 / (q : ℝ)) := by
          symm
          rw [Finset.mul_sum]
      _ = (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) := by
          congr 1
          symm
          simpa using
            (Finset.prod_sub (s := n.primeFactors) (f := fun _ : ℕ => (1 : ℝ))
              (g := fun q : ℕ => 1 / (q : ℝ)))
  have herror :
      ∑ t ∈ n.primeFactors.powerset, (1 : ℝ) = (2 : ℝ) ^ n.primeFactors.card := by
    calc
      ∑ t ∈ n.primeFactors.powerset, (1 : ℝ) = (n.primeFactors.powerset.card : ℝ) := by simp
      _ = (2 : ℝ) ^ n.primeFactors.card := by simp
  calc
    ((good.map emb).card : ℝ)
        = ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((t.inf S).card : ℝ) := hIE_real
    _ ≥ ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q))
          - ∑ t ∈ n.primeFactors.powerset, (1 : ℝ) := hsum_lower'
    _ = (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ))
          - (2 : ℝ) ^ n.primeFactors.card := by rw [hmain_expand, herror]

private lemma mertens_primeFactors_lower_bound {n : ℕ} (hn3 : 3 ≤ n) :
    1 / (3 * Real.log n)
      ≤ ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) := by
  let t : Finset ℕ := (Finset.range (n + 1)).filter Nat.Prime
  let f : ℕ → ℝ := fun q ↦ 1 - 1 / (q : ℝ)
  have hsubset : n.primeFactors ⊆ t := by
    intro q hq
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_mem_primeFactors hq)),
      Nat.prime_of_mem_primeFactors hq⟩
  have hfactor_nonneg : ∀ q ∈ t, 0 ≤ f q := by
    intro q hq
    have hqprime : Nat.Prime q := (Finset.mem_filter.mp hq).2
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
    have hq_ge1 : (1 : ℝ) ≤ q := by exact_mod_cast hqprime.one_le
    have hdiv_le : 1 / (q : ℝ) ≤ 1 :=
      by simpa using (one_div_le_one_div_of_le zero_lt_one hq_ge1)
    nlinarith
  have hfactor_le_one : ∀ q ∈ t, f q ≤ 1 := by
    intro q hq
    have hdiv_nonneg : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
    nlinarith
  have hs_nonneg : 0 ≤ ∏ q ∈ n.primeFactors, f q := by
    refine Finset.prod_nonneg ?_
    intro q hq
    exact hfactor_nonneg q (hsubset hq)
  have hextra_le_one : ∏ q ∈ t \ n.primeFactors, f q ≤ 1 := by
    refine Finset.prod_le_one ?_ ?_
    · intro q hq
      exact hfactor_nonneg q (Finset.mem_sdiff.mp hq).1
    · intro q hq
      exact hfactor_le_one q (Finset.mem_sdiff.mp hq).1
  have hprod_le : ∏ q ∈ t, f q ≤ ∏ q ∈ n.primeFactors, f q := by
    calc
      ∏ q ∈ t, f q = (∏ q ∈ t \ n.primeFactors, f q) * ∏ q ∈ n.primeFactors, f q := by
        symm
        exact Finset.prod_sdiff hsubset
      _ ≤ 1 * ∏ q ∈ n.primeFactors, f q := by
        exact mul_le_mul_of_nonneg_right hextra_le_one hs_nonneg
      _ = ∏ q ∈ n.primeFactors, f q := by simp
  have hmertens : 1 / (3 * Real.log n) ≤ ∏ q ∈ t, f q := by
    simpa [t, f] using mertens_third_theorem n hn3
  exact le_trans hmertens hprod_le

/-- Main counting lemma.

For fixed `a`, if `p` is an odd prime of Pollack-size, `p ∤ a*n`, and
`a*x^2 ≡ n [MOD p]` is solvable, then for all sufficiently large `n`
there are more than one candidates.

This is exactly where the Möbius-inversion count and `mertens_third_theorem` enter.
In this formalization, it is enough to count one chosen root class modulo `p`; the
factor `2` from the paper is not needed. -/
private lemma many_candidates_of_pollack_size
    (a : ℕ)
    (ha : 1 ≤ a) :
    ∃ N0 : ℕ, ∀ {n p : ℕ},
      N0 ≤ n →
      p.Prime →
      p ≠ 2 →
      ¬ p ∣ a * n →
      SolvableAX2EqNMod a n p →
      (p : ℝ) ≤ pollackSizeBound a n →
      1 < (candidateKs a n p).card := by
  classical
  obtain ⟨Nω, hω⟩ := two_pow_primeFactors_card_le_rpow_sixteenth_eventually
  obtain ⟨Nmain, hNmain_ge3, hmain⟩ := nat_rpow_sixteenth_div_log_eventually_large (48 * a)
  refine ⟨max Nω Nmain, ?_⟩
  intro n p hn hp hp2 hpndvd hsol hpbound
  have hnω : Nω ≤ n := le_trans (le_max_left _ _) hn
  have hnmain : Nmain ≤ n := le_trans (le_max_right _ _) hn
  have hn3 : 3 ≤ n := le_trans hNmain_ge3 hnmain
  have hn0 : n ≠ 0 := by omega
  let x : ℕ := Classical.choose hsol
  have hx : Nat.ModEq p (a * x ^ 2) n := Classical.choose_spec hsol
  let r : ℕ := x % p
  have hr_root : Nat.ModEq p (a * r ^ 2) n := by
    have hxr : Nat.ModEq p r x := Nat.mod_modEq x p
    exact ((Nat.ModEq.pow 2 hxr).mul_left a).trans hx
  have hr_lt_p : r < p := by
    dsimp [r]
    exact Nat.mod_lt _ hp.pos
  have hr_ne_zero : r ≠ 0 := by
    intro hr0
    have hmod : Nat.ModEq p n 0 := by
      simpa [r, hr0] using hr_root.symm
    have hpdvdn : p ∣ n := (Nat.modEq_zero_iff_dvd.mp hmod)
    exact hpndvd (dvd_mul_of_dvd_right hpdvdn a)
  let K : ℕ := Nat.sqrt ((n - 1) / a) + 1
  let U : Finset ℕ := ((Finset.range K).filter fun k ↦ Nat.ModEq p k r)
  let α := {k : ℕ // k ∈ U}
  let emb : α ↪ ℕ :=
    ⟨Subtype.val, by
      intro x y h
      exact Subtype.ext h⟩
  let S : ℕ → Finset α := fun q ↦ (Finset.univ : Finset α).filter fun k ↦ q ∣ (k : ℕ)
  let good : Finset α := n.primeFactors.inf fun q ↦ (S q)ᶜ
  have hgood_sub : good.map emb ⊆ candidateKs a n p := by
    intro k hk
    rcases Finset.mem_map.mp hk with ⟨y, hy, rfl⟩
    have hyU : (y : ℕ) ∈ U := y.property
    have hy_ltK : (y : ℕ) < K := by
      simpa [U] using (Finset.mem_filter.mp hyU).1
    have hy_mod : Nat.ModEq p (y : ℕ) r := by
      simpa [U] using (Finset.mem_filter.mp hyU).2
    have hy_notdvd : ∀ q ∈ n.primeFactors, ¬ q ∣ (y : ℕ) := by
      intro q hq
      have hyq : y ∈ (S q)ᶜ :=
        (mem_finset_inf_iff (s := n.primeFactors) (f := fun q ↦ (S q)ᶜ) (a := y)).1 hy q hq
      simpa [S] using hyq
    have hy_ne_zero : (y : ℕ) ≠ 0 := by
      intro hy0
      have hzr : Nat.ModEq p 0 r := by simpa [hy0] using hy_mod
      have hpdvdr : p ∣ r := Nat.modEq_zero_iff_dvd.mp hzr.symm
      exact (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hr_ne_zero) hr_lt_p) hpdvdr
    have hy_pos : 1 ≤ (y : ℕ) := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hy_ne_zero)
    have hy_disj : Disjoint (y : ℕ).primeFactors n.primeFactors := by
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      exact hy_notdvd q hq2 (Nat.dvd_of_mem_primeFactors hq1)
    have hy_coprime : Nat.Coprime (y : ℕ) n := by
      exact (Nat.disjoint_primeFactors hy_ne_zero hn0).mp hy_disj
    have hy_le_sqrt : (y : ℕ) ≤ Nat.sqrt ((n - 1) / a) := by
      simpa [K] using Nat.lt_succ_iff.mp hy_ltK
    have hy_sq_le : (y : ℕ) ^ 2 ≤ (n - 1) / a := (Nat.le_sqrt'.mp hy_le_sqrt)
    have hy_quad_le : a * (y : ℕ) ^ 2 ≤ n - 1 := by
      exact le_trans (Nat.mul_le_mul_left a hy_sq_le) (Nat.mul_div_le (n - 1) a)
    have hy_pred_lt : n - 1 < n := by
      have hnpos : 0 < n := by omega
      rw [← Nat.sub_add_cancel (Nat.succ_le_of_lt hnpos)]
      exact Nat.lt_succ_self _
    have hy_quad : a * (y : ℕ) ^ 2 < n := lt_of_le_of_lt hy_quad_le hy_pred_lt
    have hy_sq_lt_n : (y : ℕ) ^ 2 < n := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ ha) hy_quad
    have hy_lt_n : (y : ℕ) < n := by
      have hy_le_sq : (y : ℕ) ≤ (y : ℕ) ^ 2 := by
        simpa [pow_two] using Nat.le_mul_of_pos_right (y : ℕ) (Nat.pos_of_ne_zero hy_ne_zero)
      exact lt_of_le_of_lt hy_le_sq hy_sq_lt_n
    have hy_root : Nat.ModEq p (a * (y : ℕ) ^ 2) n := by
      exact (((Nat.ModEq.pow 2 hy_mod).mul_left a).trans hr_root)
    rw [candidateKs, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr hy_lt_n, hy_pos, hy_quad, hy_coprime, hy_root⟩
  have hlower : ((good.map emb).card : ℝ)
      ≥ (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ))
          - (2 : ℝ) ^ n.primeFactors.card := by
    simpa [U, α, emb, S, good, K] using
      (root_class_good_count_lower_bound (a := a) (n := n) (p := p) (r := r) (K := K)
        ha hn3 hp hpndvd hr_root rfl)
  have hmertens : 1 / (3 * Real.log n)
      ≤ ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) :=
    mertens_primeFactors_lower_bound hn3
  have hmain' : (48 * a : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 16) / (3 * Real.log n) := hmain n hnmain
  have hω' : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) ^ ((1 : ℝ) / 16) := hω hnω
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp_le : p ≤ (4 * a * n : ℝ) ^ ((3 : ℝ) / 8) := by
    simpa [pollackSizeBound] using hpbound
  have hK_over_p : (2 : ℝ) + (2 : ℝ) ^ n.primeFactors.card
      ≤ (K : ℝ) / p * (1 / (3 * Real.log n)) := by
    have ha_pos_nat : 0 < a := by omega
    have hn_pos_nat : 0 < n := by omega
    have ha_pos : (0 : ℝ) < a := by exact_mod_cast ha_pos_nat
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
    have hnpow16_pos : 0 < (n : ℝ) ^ ((1 : ℝ) / 16) := by positivity
    have h4a_ne : (4 * a : ℝ) ≠ 0 := by positivity
    have hpow16_ne : (n : ℝ) ^ ((1 : ℝ) / 16) ≠ 0 := hnpow16_pos.ne'
    have hKp_lower : (n : ℝ) ^ ((1 : ℝ) / 8) / (4 * a) ≤ (K : ℝ) / p := by
      have hKsq_nat : ((n - 1) / a + 1) ≤ K ^ 2 := by
        dsimp [K]
        simpa [pow_two] using Nat.succ_le_succ_sqrt' ((n - 1) / a)
      have hn_le_div_nat : n ≤ a * (((n - 1) / a) + 1) := by
        have hlt : n - 1 < a * (((n - 1) / a) + 1) := by
          calc
            n - 1 = a * ((n - 1) / a) + ((n - 1) % a) := by
              simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
                (Nat.div_add_mod' (n - 1) a).symm
            _ < a * ((n - 1) / a) + a := by
              exact Nat.add_lt_add_left (Nat.mod_lt _ ha_pos_nat) _
            _ = a * (((n - 1) / a) + 1) := by ring
        rw [← Nat.succ_pred_eq_of_pos hn_pos_nat]
        exact Nat.succ_le_of_lt hlt
      have hn_le_aKsq_nat : n ≤ a * K ^ 2 := by
        calc
          n ≤ a * (((n - 1) / a) + 1) := hn_le_div_nat
          _ ≤ a * K ^ 2 := Nat.mul_le_mul_left _ hKsq_nat
      have hn_le_aKsq : (n : ℝ) ≤ a * (K : ℝ) ^ 2 := by
        exact_mod_cast hn_le_aKsq_nat
      have hna_div : (n : ℝ) / a ≤ (K : ℝ) ^ 2 := by
        exact (div_le_iff₀ ha_pos).2 <| by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hn_le_aKsq
      have hsqrt_leK : ((n : ℝ) / a) ^ ((1 : ℝ) / 2) ≤ K := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
        exact ⟨by positivity, hna_div⟩
      have hmid :
          ((n : ℝ) / a) ^ ((1 : ℝ) / 2) / (4 * a * n : ℝ) ^ ((3 : ℝ) / 8)
            ≤ (K : ℝ) / p := by
        have h1 :
            ((n : ℝ) / a) ^ ((1 : ℝ) / 2) / (4 * a * n : ℝ) ^ ((3 : ℝ) / 8)
              ≤ ((n : ℝ) / a) ^ ((1 : ℝ) / 2) / p := by
          exact div_le_div_of_nonneg_left (by positivity) hp_pos hp_le
        have h2 :
            ((n : ℝ) / a) ^ ((1 : ℝ) / 2) / p ≤ (K : ℝ) / p := by
          exact div_le_div_of_nonneg_right hsqrt_leK hp_pos.le
        exact le_trans h1 h2
      have hbase :
          (n : ℝ) ^ ((1 : ℝ) / 8) / (4 * a)
            ≤ ((n : ℝ) / a) ^ ((1 : ℝ) / 2) / (4 * a * n : ℝ) ^ ((3 : ℝ) / 8) := by
        have h4a_pos : 0 < (4 * a : ℝ) := by positivity
        have h4an_pos : 0 < (4 * a * n : ℝ) ^ ((3 : ℝ) / 8) := by positivity
        rw [div_le_div_iff₀ h4a_pos h4an_pos]
        have hrewrite :
            (4 * a * n : ℝ) ^ ((3 : ℝ) / 8)
              = ((4 : ℝ) * a) ^ ((3 : ℝ) / 8) * (n : ℝ) ^ ((3 : ℝ) / 8) := by
          have hmul : (4 * a * n : ℝ) = ((4 : ℝ) * a) * n := by ring
          rw [hmul, Real.mul_rpow (by positivity) (by positivity)]
        have hdivrpow :
            ((n : ℝ) / a) ^ ((1 : ℝ) / 2)
              = (n : ℝ) ^ ((1 : ℝ) / 2) / (a : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [Real.div_rpow (by positivity) (by positivity)]
        have hncombine :
            (n : ℝ) ^ ((1 : ℝ) / 8) * (n : ℝ) ^ ((3 : ℝ) / 8)
              = (n : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_add hn_pos]
          norm_num
        have hahalf :
            (a : ℝ) / (a : ℝ) ^ ((1 : ℝ) / 2) = (a : ℝ) ^ ((1 : ℝ) / 2) := by
          have hsub :
              (a : ℝ) ^ ((1 : ℝ) - (1 : ℝ) / 2)
                = (a : ℝ) / (a : ℝ) ^ ((1 : ℝ) / 2) := by
            rw [Real.rpow_sub ha_pos, Real.rpow_one]
          calc
            (a : ℝ) / (a : ℝ) ^ ((1 : ℝ) / 2)
                = (a : ℝ) ^ ((1 : ℝ) - (1 : ℝ) / 2) := by simpa using hsub.symm
            _ = (a : ℝ) ^ ((1 : ℝ) / 2) := by norm_num
        have hconst :
            ((4 : ℝ) * a) ^ ((3 : ℝ) / 8) ≤ (4 : ℝ) * (a : ℝ) ^ ((1 : ℝ) / 2) := by
          calc
            ((4 : ℝ) * a) ^ ((3 : ℝ) / 8)
                = (4 : ℝ) ^ ((3 : ℝ) / 8) * (a : ℝ) ^ ((3 : ℝ) / 8) := by
                    rw [Real.mul_rpow (by positivity) (by positivity)]
            _ ≤ (4 : ℝ) * (a : ℝ) ^ ((1 : ℝ) / 2) := by
              have h4 : (4 : ℝ) ^ ((3 : ℝ) / 8) ≤ 4 := by
                have htmp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
                  (by norm_num : (3 : ℝ) / 8 ≤ 1)
                simpa [Real.rpow_one] using htmp
              have haexp : (a : ℝ) ^ ((3 : ℝ) / 8) ≤ (a : ℝ) ^ ((1 : ℝ) / 2) := by
                have ha_one : (1 : ℝ) ≤ a := by exact_mod_cast ha
                exact Real.rpow_le_rpow_of_exponent_le ha_one
                  (by norm_num : (3 : ℝ) / 8 ≤ (1 : ℝ) / 2)
              exact mul_le_mul h4 haexp (by positivity) (by positivity)
        rw [hrewrite, hdivrpow]
        calc
          (n : ℝ) ^ ((1 : ℝ) / 8) *
              (((4 : ℝ) * a) ^ ((3 : ℝ) / 8) * (n : ℝ) ^ ((3 : ℝ) / 8))
              = ((4 : ℝ) * a) ^ ((3 : ℝ) / 8) *
                  ((n : ℝ) ^ ((1 : ℝ) / 8) * (n : ℝ) ^ ((3 : ℝ) / 8)) := by ring
          _ = ((4 : ℝ) * a) ^ ((3 : ℝ) / 8) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
            rw [hncombine]
          _ = (n : ℝ) ^ ((1 : ℝ) / 2) * (((4 : ℝ) * a) ^ ((3 : ℝ) / 8)) := by ring
          _ ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * ((4 : ℝ) * (a : ℝ) ^ ((1 : ℝ) / 2)) := by
            exact mul_le_mul_of_nonneg_left hconst (by positivity)
          _ = ((n : ℝ) ^ ((1 : ℝ) / 2) / (a : ℝ) ^ ((1 : ℝ) / 2)) * ((4 : ℝ) * a) := by
            calc
              (n : ℝ) ^ ((1 : ℝ) / 2) * ((4 : ℝ) * (a : ℝ) ^ ((1 : ℝ) / 2))
                  = (4 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) * (a : ℝ) ^ ((1 : ℝ) / 2) := by ring
              _ = (4 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) *
                    ((a : ℝ) / (a : ℝ) ^ ((1 : ℝ) / 2)) := by rw [hahalf]
              _ = ((n : ℝ) ^ ((1 : ℝ) / 2) / (a : ℝ) ^ ((1 : ℝ) / 2)) * ((4 : ℝ) * a) := by
                ring
      exact le_trans hbase hmid
    have hlog_lower : (48 * a : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 16) ≤ 1 / (3 * Real.log n) := by
      have hmain'' : (48 * a : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 16) * (1 / (3 * Real.log n)) := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmain'
      have hmain''' : (48 * a : ℝ) ≤ (1 / (3 * Real.log n)) * (n : ℝ) ^ ((1 : ℝ) / 16) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmain''
      exact (div_le_iff₀ hnpow16_pos).2 hmain'''
    have hpow8_eq :
        (n : ℝ) ^ ((1 : ℝ) / 8)
          = (n : ℝ) ^ ((1 : ℝ) / 16) * (n : ℝ) ^ ((1 : ℝ) / 16) := by
      rw [show ((1 : ℝ) / 8) = (1 : ℝ) / 16 + (1 : ℝ) / 16 by norm_num]
      rw [Real.rpow_add hn_pos]
    have hprod_eq :
        ((n : ℝ) ^ ((1 : ℝ) / 8) / (4 * a)) *
            ((48 * a : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 16))
          = 12 * (n : ℝ) ^ ((1 : ℝ) / 16) := by
      rw [hpow8_eq]
      field_simp [h4a_ne, hpow16_ne]
      ring
    have h12 :
        12 * (n : ℝ) ^ ((1 : ℝ) / 16)
          ≤ (K : ℝ) / p * (1 / (3 * Real.log n)) := by
      have hmul := mul_le_mul hKp_lower hlog_lower (by positivity) (by positivity)
      rw [hprod_eq] at hmul
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    have hn16_ge_one : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 16) := by
      have hn_one : (1 : ℝ) ≤ n := by
        exact_mod_cast (show 1 ≤ n by omega)
      simpa using Real.rpow_le_rpow_of_exponent_le hn_one
        (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 16)
    have hlhs : (2 : ℝ) + (2 : ℝ) ^ n.primeFactors.card
        ≤ 3 * (n : ℝ) ^ ((1 : ℝ) / 16) := by
      have h2le : (2 : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 16) := by
        nlinarith
      linarith
    have h3 : 3 * (n : ℝ) ^ ((1 : ℝ) / 16)
        ≤ (K : ℝ) / p * (1 / (3 * Real.log n)) := by
      nlinarith [h12, hnpow16_pos]
    exact le_trans hlhs h3
  have hcard_ge : (2 : ℝ) ≤ (good.map emb).card := by
    have htmp : (2 : ℝ) + (2 : ℝ) ^ n.primeFactors.card
        ≤ (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) := by
      exact le_trans hK_over_p (mul_le_mul_of_nonneg_left hmertens (by positivity))
    linarith [hlower, htmp]
  have hmap_le : (good.map emb).card ≤ (candidateKs a n p).card := Finset.card_le_card hgood_sub
  have hge_nat : 2 ≤ (candidateKs a n p).card := by
    exact le_trans (by exact_mod_cast hcard_ge) hmap_le
  exact lt_of_lt_of_le (by decide : 1 < 2) hge_nat

/-- Contradiction engine for the two Pollack-driven branches.

Once we have one odd prime `p` of Pollack-size such that `p ∤ a*n` and
`a*x^2 ≡ n [MOD p]` is solvable, the counting argument rules out `Pa a n`. -/
private lemma not_Pa_of_good_prime
    (a : ℕ) (ha : 1 ≤ a) :
    ∃ N0 : ℕ, ∀ {n p : ℕ},
      N0 ≤ n →
      p.Prime →
      p ≠ 2 →
      ¬ p ∣ a * n →
      SolvableAX2EqNMod a n p →
      (p : ℝ) ≤ pollackSizeBound a n →
      ¬ Pa a n := by
  obtain ⟨N0, hcount⟩ := many_candidates_of_pollack_size a ha
  refine ⟨N0, ?_⟩
  intro n p hn hp hp2 hpndvd hsol hpbound hPa
  have hgt : 1 < (candidateKs a n p).card :=
    hcount hn hp hp2 hpndvd hsol hpbound
  have hle : (candidateKs a n p).card ≤ 1 :=
    candidateKs_card_le_one ha hPa hp
  exact not_lt_of_ge hle hgt

/-! ## Square-case helpers based on the fixed coefficient `a` -/

/-- If `a = v^2` and `u^2 = a*n`, with `a ≥ 1`, then `n` is also a square. -/
private lemma n_is_square_of_square_case_and_square_coeff
    {a n u v : ℕ}
    (ha : 1 ≤ a)
    (haSq : a = v ^ 2)
    (hsq : u ^ 2 = a * n) :
    ∃ m : ℕ, n = m ^ 2 := by
  have hv_pos : 0 < v := by
    by_contra hv
    have hv0 : v = 0 := Nat.eq_zero_of_not_pos hv
    have ha0 : a = 0 := by
      simpa [hv0] using haSq
    omega
  have hv2_dvd : v ^ 2 ∣ u ^ 2 := by
    refine ⟨n, ?_⟩
    simpa [haSq, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsq
  have hv_dvd_u : v ∣ u := by
    exact (Nat.pow_dvd_pow_iff (show (2 : ℕ) ≠ 0 by decide)).1 hv2_dvd
  rcases hv_dvd_u with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  have hmain : v ^ 2 * m ^ 2 = v ^ 2 * n := by
    calc
      v ^ 2 * m ^ 2 = (v * m) ^ 2 := by
        simp [pow_two, Nat.mul_left_comm, Nat.mul_comm]
      _ = u ^ 2 := by
        simp [hm]
      _ = v ^ 2 * n := by
        simpa [haSq] using hsq
  have hm2 : m ^ 2 = n := Nat.eq_of_mul_eq_mul_left (pow_pos hv_pos 2) hmain
  exact hm2.symm

/-- If `a = v^2`, `n = m^2`, and `m` is sufficiently larger than `v`, then `Pa a n` already fails
at `k = 1`, since `n - a = (m-v)(m+v)` is composite. -/
private lemma not_Pa_of_large_square_difference
    {a n v m : ℕ}
    (haSq : a = v ^ 2)
    (hnSq : n = m ^ 2)
    (hm : v + 2 ≤ m) :
    ¬ Pa a n := by
  intro hPa
  have hvlt_aux : v < v + 2 := by
    exact Nat.lt_trans (Nat.lt_succ_self v) (Nat.lt_succ_self (v + 1))
  have hvlt : v < m := lt_of_lt_of_le hvlt_aux hm
  have hlt : a * 1 ^ 2 < n := by
    have hsq_lt : v ^ 2 < m ^ 2 := Nat.pow_lt_pow_left hvlt (by decide : (2 : ℕ) ≠ 0)
    simpa [haSq, hnSq] using hsq_lt
  have hprime : Nat.Prime (n - a * 1 ^ 2) :=
    hPa 1 (by decide) (by simp) hlt
  have hprod : n - a * 1 ^ 2 = (m + v) * (m - v) := by
    calc
      n - a * 1 ^ 2 = m ^ 2 - v ^ 2 := by
        simp [haSq, hnSq]
      _ = (m + v) * (m - v) := by
        simpa using Nat.sq_sub_sq m v
  have htwo_le_vaddtwo : 2 ≤ v + 2 := by
    simp
  have hm_ge_two : 2 ≤ m := le_trans htwo_le_vaddtwo hm
  have hmplus_ge_two : 2 ≤ m + v := le_trans hm_ge_two (Nat.le_add_right m v)
  have hmplus_ne_one : m + v ≠ 1 :=
    ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hmplus_ge_two)
  have hvle : v ≤ m := le_trans (Nat.le_add_right v 2) hm
  have hmsub_ge_two : 2 ≤ m - v :=
    (Nat.le_sub_iff_add_le hvle).2 (by simpa [Nat.add_comm] using hm)
  have hmsub_ne_one : m - v ≠ 1 :=
    ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hmsub_ge_two)
  have hnotprime : ¬ Nat.Prime ((m + v) * (m - v)) :=
    Nat.not_prime_mul hmplus_ne_one hmsub_ne_one
  exact hnotprime (hprod ▸ hprime)

/-- Square case, non-square coefficient branch.

Here `a = v^2*d` with squarefree `d > 1`.  From `a = v^2*d` we get `4*d ∣ 4*a*n`, so
Pollack applied with modulus `m = 4*a*n` produces a prime `p` of Pollack-size with `p ∤ a*n`;
the square identity `u^2 = a*n`
then makes `a*x^2 ≡ n [MOD p]` solvable, and the contradiction is delegated to
`not_Pa_of_good_prime`. -/
lemma square_case_nonsquare_coeff_impossible_of_coeff
    (a v d : ℕ)
    (ha : 1 ≤ a)
    (_hdSq : Squarefree d)
    (_hdGt : 1 < d)
    (hadecomp : v ^ 2 * d = a) :
    ∃ N0 : ℕ, ∀ {n u : ℕ},
      N0 ≤ n →
      u ^ 2 = a * n →
      ¬ Pa a n := by
  obtain ⟨M0, hPollack⟩ := exists_small_prime_from_pollack
  obtain ⟨Nbad, hbad⟩ := not_Pa_of_good_prime a ha
  refine ⟨max M0 Nbad, ?_⟩
  intro n u hn hsq
  have hm : M0 ≤ 4 * a * n := by
    exact le_trans (le_trans (le_max_left _ _) hn) (le_pollack_modulus ha)
  have hdvd : 4 * d ∣ 4 * a * n :=
    squarefree_coeff_dvd_pollack_modulus (n := n) hadecomp
  obtain ⟨p, hp, hp2, hpndvdMod, hpbound, _hres⟩ := hPollack hm hdvd
  have hpndvd : ¬ p ∣ a * n := not_dvd_an_of_not_dvd_pollack_modulus hpndvdMod
  have hsol : SolvableAX2EqNMod a n p :=
    solvable_of_square_case hsq hp hpndvd
  exact hbad (le_trans (le_max_right _ _) hn) hp hp2 hpndvd hsol (by
    simpa [pollackSizeBound] using hpbound)

/-- Square case, square coefficient branch.

Once `a = v^2`, the relation `u^2 = a*n` forces `n = m^2`.  For all sufficiently large `n`
we then have `m ≥ v + 2`, and `k = 1` gives a composite value `n - a`. -/
lemma square_case_square_coeff_impossible_of_coeff
    (a v : ℕ)
    (ha : 1 ≤ a)
    (haSq : a = v ^ 2) :
    ∃ N0 : ℕ, ∀ {n u : ℕ},
      N0 ≤ n →
      u ^ 2 = a * n →
      ¬ Pa a n := by
  refine ⟨(v + 2) ^ 2, ?_⟩
  intro n u hn hsq
  obtain ⟨m, hnSq⟩ := n_is_square_of_square_case_and_square_coeff ha haSq hsq
  have hm_sq : (v + 2) ^ 2 ≤ m ^ 2 := by
    simpa [hnSq] using hn
  have hm : v + 2 ≤ m :=
    (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).1 hm_sq
  exact not_Pa_of_large_square_difference haSq hnSq hm

/-! ## The two contradiction arguments -/

/-- Case 1: the squarefree part `d` of `a*n` is `> 1`.

The only nontrivial input is the existence of one good Pollack prime; once that is in hand,
the rest is again delegated to `not_Pa_of_good_prime`. -/
lemma case1_non_square_impossible
    (a : ℕ)
    (ha : 1 ≤ a) :
    ∃ N1 : ℕ, ∀ {n u d : ℕ},
      N1 ≤ n →
      Squarefree d →
      1 < d →
      u ^ 2 * d = a * n →
      ¬ Pa a n := by
  obtain ⟨M0, hPollack⟩ := exists_small_prime_from_pollack
  obtain ⟨Nbad, hbad⟩ := not_Pa_of_good_prime a ha
  refine ⟨max M0 Nbad, ?_⟩
  intro n u d hn _hdSq _hdGt hdecomp
  have hm : M0 ≤ 4 * a * n := by
    exact le_trans (le_trans (le_max_left _ _) hn) (le_pollack_modulus ha)
  have hdvd : 4 * d ∣ 4 * a * n :=
    squarefree_factor_dvd_pollack_modulus hdecomp
  obtain ⟨p, hp, hp2, hpndvdMod, hpbound, hres⟩ := hPollack hm hdvd
  have hpndvd : ¬ p ∣ a * n := not_dvd_an_of_not_dvd_pollack_modulus hpndvdMod
  have hsol : SolvableAX2EqNMod a n p :=
    solvable_of_squarefree_part hdecomp hp hpndvd hres
  exact hbad (le_trans (le_max_right _ _) hn) hp hp2 hpndvd hsol (by
    simpa [pollackSizeBound] using hpbound)

/-- Case 2: `a*n` is a square.

We factor the fixed coefficient `a = v^2*d` with `d` squarefree and split according to whether
`d > 1` or `d = 1`.  This removes the need for any separate small-prime lemma in the square case. -/
lemma case2_square_impossible
    (a : ℕ)
    (ha : 1 ≤ a) :
    ∃ N2 : ℕ, ∀ {n u : ℕ},
      N2 ≤ n →
      u ^ 2 = a * n →
      ¬ Pa a n := by
  obtain ⟨v, d, hadecomp, hdSq⟩ := exists_squarefree_factorization a
  by_cases hd1 : d = 1
  · have haSq : a = v ^ 2 := coeff_is_square_of_squarefree_part_eq_one hadecomp hd1
    exact square_case_square_coeff_impossible_of_coeff a v ha haSq
  · have hdGt : 1 < d := one_lt_of_squarefree_ne_one hdSq hd1
    exact square_case_nonsquare_coeff_impossible_of_coeff a v d ha hdSq hdGt hadecomp

/-! ## Main theorem -/

/-- Eventual failure of `Pa a n` for every fixed `a ≥ 1`. -/
theorem eventually_not_Pa (a : ℕ) (ha : 1 ≤ a) :
    ∃ N : ℕ, ∀ {n : ℕ}, N ≤ n → ¬ Pa a n := by
  obtain ⟨N1, h1⟩ := case1_non_square_impossible a ha
  obtain ⟨N2, h2⟩ := case2_square_impossible a ha
  refine ⟨max N1 N2, ?_⟩
  intro n hn hPa
  obtain ⟨u, d, hdecomp, hdSq⟩ := exists_squarefree_factorization (a * n)
  by_cases hd1 : d = 1
  · have hsq : u ^ 2 = a * n := by
      simpa [hd1] using hdecomp
    exact h2 (le_trans (le_max_right _ _) hn) hsq hPa
  · have hdGt : 1 < d := one_lt_of_squarefree_ne_one hdSq hd1
    exact h1 (le_trans (le_max_left _ _) hn) hdSq hdGt hdecomp hPa

/-- General finite-set formulation of the theorem. -/
theorem erdos_1141_variant_general (a : ℕ) (ha : 1 ≤ a) :
    Set.Finite {n : ℕ | Pa a n} := by
  obtain ⟨N, hN⟩ := eventually_not_Pa a ha
  refine (Set.finite_lt_nat N).subset ?_
  intro n hn
  by_contra hlt
  exact hN (n := n) (Nat.le_of_not_lt hlt) hn

/-- Paper-style `Pa` statement for `a = 1`, stronger than the Formal Conjectures
statement `erdos_1141` below. -/
theorem erdos_1141_variant : Set.Finite {n : ℕ | Pa 1 n} := by
  simpa using erdos_1141_variant_general 1 (by decide : 1 ≤ 1)

/-! ## Block Copied from Formal Conjectures -/

/-
The following block is copied as literally as possible from
https://github.com/google-deepmind/formal-conjectures/blob/main/
FormalConjectures/ErdosProblems/1141.lean
with only the proof of `erdos_1141` filled in via the stronger theorem
`erdos_1141_variant` above.
-/

open Nat Set

/--
The property that $n-k^2$ is prime for all $k$ with $(n,k)=1$ and $k^2 < n$.
-/
def Erdos1141Prop (n : ℕ) : Prop :=
  ∀ k, k ^ 2 < n → Coprime n k → (n - k ^ 2).Prime

instance (n : ℕ) : Decidable (Erdos1141Prop n) :=
  decidable_of_iff (∀ k ≤ .sqrt (n - 1), Coprime n k → (n - k ^ 2).Prime) <| by
    cases n with
    | zero => simp [Erdos1141Prop]
    | succ n' =>
      simp [Erdos1141Prop, Nat.le_sqrt, pow_two]

theorem erdos1141Prop_iff_pa_one_ne_one (n : ℕ) :
    Erdos1141Prop n ↔ Pa 1 n ∧ n ≠ 1 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro k hk hcop hlt
      simpa [one_mul] using h k (by simpa [one_mul] using hlt) hcop.symm
    · intro hn
      have h0 := h 0 (by simp [hn]) (by simp [hn])
      have h1 : Nat.Prime 1 := by simpa [hn] using h0
      exact Nat.not_prime_one h1
  · rintro ⟨hPa, hn1⟩ k hk hcop
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exfalso
      have : ¬ Coprime n 0 := by simpa [Nat.coprime_zero_right] using hn1
      exact this hcop
    · simpa [one_mul] using hPa k hkpos hcop.symm (by simpa [one_mul] using hk)

/--
Are there infinitely many $n$ such that $n-k^2$ is prime for all $k$ with $(n,k)=1$ and $k^2 < n$?

In [Va99] it is asked whether $968$ is the largest integer with this property, but this is an
error, since for example $968-9=7\cdot 137$.

The list of $n$ satisfying the given property is [A214583] in the OEIS. The largest known such $n$
is $1722$.
-/
theorem erdos_1141 :
    ¬ Infinite { n | Erdos1141Prop n } := by
  have hsubset : { n | Erdos1141Prop n } ⊆ { n | Pa 1 n } := by
    intro n hn
    exact (erdos1141Prop_iff_pa_one_ne_one n).1 hn |>.1
  exact Finite.not_infinite (erdos_1141_variant.subset hsubset).to_subtype

end

#print axioms erdos_1141
-- 'Erdos1141.erdos_1141' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1141
