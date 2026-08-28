import Mathlib

namespace Erdos937

/-
# Problem Description

Erdős Problem 937. Are there infinitely many four-term arithmetic progressions of coprime
powerful numbers (`n` is powerful if `p ∣ n` implies `p² ∣ n`)? `erdos_937` proves that there
are.

Fermat showed there are no four squares in arithmetic progression. Without the coprimality
condition the question is easy: from a progression of powerful numbers `a, …, a+(k-1)d` one
builds `a(a+kd)², …, (a+(k-1)d)(a+kd)², (a+kd)³`, so arbitrarily long progressions exist.
Erdős [Er76d] asked the coprime version, and it was answered affirmatively by Bajpai, Bennett
and Chan [BBC24], whose elliptic-curve parametrization is what is formalised here. The
statement, including `IsCoprimePowerfulAP4` (which requires `0 < d`, all four terms powerful,
and all six pairwise coprimality conditions), is that of the Formal Conjectures entry.

Erdős asks this on pp. 32--33 of [Er76d] ("Problems and results on number theoretic
properties of consecutive integers and related questions", Proc. Fifth Manitoba Conf. on
Numerical Mathematics, 25--44): "It is well known that there are infinitely many triples of
squares in an arithmetic progression, but four squares never form an arithmetic
[progression]. Are there infinitely many quadruples of relatively prime powerful numbers
which form an arithmetic progression? Relative primeness is obviously needed." He goes on to
define `A'(r)` as the largest number of relatively prime `r`-powerful numbers occurring in
infinitely many arithmetic progressions, conjecturing `A'(r) = 0` for `r ≥ 4` and `A'(3) = 3`.
`IsCoprimePowerfulAP4` below requires coprimality *pairwise*, which is the stronger reading of
"relatively prime", so the theorem also gives the setwise-gcd version.

The formalisation is by plby (github.com/plby/lean-proofs),
`src/latest/ErdosProblems/Erdos937.lean` together with
`src/latest/ErdosProblems/Erdos937/Erdos937Elliptic.lean`. The two files are concatenated
here in dependency order, with their project-internal imports removed so that `Mathlib` is
the only import, each module's contents kept in a `section` carrying its own `open` lines,
and the whole wrapped once in `namespace Erdos937` with the upstream trust-base print line
removed. No mathematical content is changed.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos937/Erdos937Elliptic.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Erdős Problem 937

Bajpai, Bennett, and Chan proved that there are infinitely many four-term arithmetic
progressions of pairwise coprime powerful numbers.  The mathematical reconstruction and the
formalization map are in `tex/937.tex`.
-/

section
open Nat

/-- A natural number is `k`-full when every prime factor occurs to exponent at least `k`.
This is the definition used by `FormalConjecturesUtil`. -/
def _root_.Nat.Full (k n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ k ∣ n

/-- Powerful (squarefull) natural numbers are the `2`-full numbers. -/
abbrev _root_.Nat.Powerful : ℕ → Prop := Full 2

end



open Nat Set

/-- The four numbers `a, a+d, a+2d, a+3d` form a nonconstant progression of pairwise
coprime powerful numbers.  This is the exact upstream specification. -/
def IsCoprimePowerfulAP4 (a d : ℕ) : Prop :=
  0 < d ∧
  a.Powerful ∧ (a + d).Powerful ∧ (a + 2 * d).Powerful ∧ (a + 3 * d).Powerful ∧
  a.Coprime (a + d) ∧ a.Coprime (a + 2 * d) ∧ a.Coprime (a + 3 * d) ∧
  (a + d).Coprime (a + 2 * d) ∧ (a + d).Coprime (a + 3 * d) ∧
  (a + 2 * d).Coprime (a + 3 * d)

/-! ## The three-square parametrization -/

/-- The first square root in the parametrization of three squares in arithmetic progression. -/
def apX (a b : ℤ) : ℤ := a ^ 2 - b ^ 2 + 2 * a * b

/-- The middle square root in the parametrization. -/
def apY (a b : ℤ) : ℤ := a ^ 2 + b ^ 2

/-- The third square root in the parametrization. -/
def apZ (a b : ℤ) : ℤ := a ^ 2 - b ^ 2 - 2 * a * b

/-- One quarter of the common difference. -/
def apDelta (a b : ℤ) : ℤ := a * b * (b ^ 2 - a ^ 2)

/-- The fourth member of the progression after the first three members have been squared. -/
def quartic (a b : ℤ) : ℤ :=
  a ^ 4 - 8 * a ^ 3 * b + 2 * a ^ 2 * b ^ 2 + 8 * a * b ^ 3 + b ^ 4

lemma apY_sq_sub_apX_sq (a b : ℤ) :
    apY a b ^ 2 - apX a b ^ 2 = 4 * apDelta a b := by
  simp only [apX, apY, apDelta]
  ring

lemma apZ_sq_sub_apY_sq (a b : ℤ) :
    apZ a b ^ 2 - apY a b ^ 2 = 4 * apDelta a b := by
  simp only [apZ, apY, apDelta]
  ring

lemma quartic_sub_apZ_sq (a b : ℤ) :
    quartic a b - apZ a b ^ 2 = 4 * apDelta a b := by
  simp only [quartic, apZ, apDelta]
  ring

lemma quartic_parity_transform (a b : ℤ) (hs : 2 ∣ a + b) (hd : 2 ∣ a - b) :
    4 * quartic ((a + b) / 2) ((a - b) / 2) = quartic a b := by
  obtain ⟨u, hu⟩ := hs
  obtain ⟨v, hv⟩ := hd
  have ha : a = u + v := by omega
  have hb : b = u - v := by omega
  subst a
  subst b
  have hsum : (u + v + (u - v)) / 2 = u := by omega
  have hdiff : (u + v - (u - v)) / 2 = v := by omega
  rw [hsum, hdiff]
  simp only [quartic]
  ring

/-! ## A fixed multiplication-by-five orbit

For the infinitude argument it is enough to iterate one fixed rational map.  We use the integral
short Weierstrass model obtained from the BBC curve.
-/

abbrev shortA : ℚ := -478842624
abbrev shortB : ℚ := 3011551764480

private def shortCurve : WeierstrassCurve ℚ := ⟨0, 0, 0, shortA, shortB⟩

def ShortOnCurve (P : ℚ × ℚ) : Prop :=
  P.2 ^ 2 = P.1 ^ 3 + shortA * P.1 + shortB

/-- Affine doubling on the short model.  Our orbit never meets a point with `y = 0`. -/
def shortDouble (P : ℚ × ℚ) : ℚ × ℚ :=
  let m := (3 * P.1 ^ 2 + shortA) / (2 * P.2)
  let x := m ^ 2 - 2 * P.1
  (x, m * (P.1 - x) - P.2)

/-- Affine addition when the two x-coordinates are distinct. -/
def shortAdd (P Q : ℚ × ℚ) : ℚ × ℚ :=
  let m := (Q.2 - P.2) / (Q.1 - P.1)
  let x := m ^ 2 - P.1 - Q.1
  (x, m * (P.1 - x) - P.2)

/-- Multiplication by five, implemented as `P + 2(2P)`. -/
def shortMulFive (P : ℚ × ℚ) : ℚ × ℚ :=
  shortAdd P (shortDouble (shortDouble P))

lemma shortCurve_equation_iff (P : ℚ × ℚ) :
    shortCurve.toAffine.Equation P.1 P.2 ↔ ShortOnCurve P := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [shortCurve, ShortOnCurve, shortA, shortB, WeierstrassCurve.toAffine]

lemma shortDouble_onCurve {P : ℚ × ℚ} (hP : ShortOnCurve P) (hy : P.2 ≠ 0) :
    ShortOnCurve (shortDouble P) := by
  have he : shortCurve.toAffine.Equation P.1 P.2 :=
    (shortCurve_equation_iff P).2 hP
  have hneg : P.2 ≠ shortCurve.toAffine.negY P.1 P.2 := by
    simp only [shortCurve, WeierstrassCurve.toAffine, WeierstrassCurve.Affine.negY]
    intro h
    apply hy
    linarith
  have hadd := shortCurve.toAffine.equation_add he he
    (fun h => hneg h.2)
  rw [shortCurve.toAffine.slope_of_Y_ne rfl hneg] at hadd
  have hm : P.2 + P.2 = 2 * P.2 := by ring
  apply (shortCurve_equation_iff (shortDouble P)).1
  convert hadd using 1
  case e'_2 => rfl
  case e'_4 =>
    simp [shortDouble, shortCurve, shortA, shortB, WeierstrassCurve.toAffine,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    rw [hm]
    ring
  case e'_5 =>
    simp [shortDouble, shortCurve, shortA, shortB, WeierstrassCurve.toAffine,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    rw [hm]
    ring

lemma shortAdd_onCurve {P Q : ℚ × ℚ} (hP : ShortOnCurve P) (hQ : ShortOnCurve Q)
    (hx : P.1 ≠ Q.1) : ShortOnCurve (shortAdd P Q) := by
  have heP : shortCurve.toAffine.Equation P.1 P.2 :=
    (shortCurve_equation_iff P).2 hP
  have heQ : shortCurve.toAffine.Equation Q.1 Q.2 :=
    (shortCurve_equation_iff Q).2 hQ
  have hadd := shortCurve.toAffine.equation_add heP heQ (fun h => hx h.1)
  rw [shortCurve.toAffine.slope_of_X_ne hx] at hadd
  have hm : (Q.2 - P.2) / (Q.1 - P.1) = (P.2 - Q.2) / (P.1 - Q.1) := by
    field_simp [sub_ne_zero.mpr hx, sub_ne_zero.mpr (Ne.symm hx)]
    ring
  apply (shortCurve_equation_iff (shortAdd P Q)).1
  convert hadd using 1
  case e'_2 => rfl
  case e'_4 =>
    simp [shortAdd, shortCurve, shortA, shortB, WeierstrassCurve.toAffine,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    rw [hm]
  case e'_5 =>
    simp [shortAdd, shortCurve, shortA, shortB, WeierstrassCurve.toAffine,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    rw [hm]
    ring

lemma shortMulFive_onCurve {P : ℚ × ℚ} (hP : ShortOnCurve P) (hy : P.2 ≠ 0)
    (hy2 : (shortDouble P).2 ≠ 0)
    (hx : P.1 ≠ (shortDouble (shortDouble P)).1) :
    ShortOnCurve (shortMulFive P) := by
  have h2 := shortDouble_onCurve hP hy
  have h4 := shortDouble_onCurve h2 hy2
  exact shortAdd_onCurve hP h4 hx

/-! ## The local calculation at five -/

private instance primeFactFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The subring of rationals integral at the prime `p`, expressed using `padicValRat`. -/
private def padicIntegral (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {q | 0 ≤ padicValRat p q}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro q r hq hr
    by_cases hqr : q + r = 0
    · simp [hqr]
    · exact (le_min hq hr).trans (padicValRat.min_le_padicValRat_add hqr)
  neg_mem' := by
    intro q hq
    simpa using hq
  mul_mem' := by
    intro q r hq hr
    change 0 ≤ padicValRat p q at hq
    change 0 ≤ padicValRat p r at hr
    change 0 ≤ padicValRat p (q * r)
    by_cases hq0 : q = 0
    · simp [hq0]
    by_cases hr0 : r = 0
    · simp [hr0]
    rw [padicValRat.mul hq0 hr0]
    omega

private lemma int_padicIntegral (p : ℕ) [Fact p.Prime] (z : ℤ) :
    0 ≤ padicValRat p (z : ℚ) := by
  rw [padicValRat.of_int]
  exact_mod_cast Nat.zero_le (padicValInt p z)

private lemma integral_add {q r : ℚ} (hq : 0 ≤ padicValRat 5 q)
    (hr : 0 ≤ padicValRat 5 r) : 0 ≤ padicValRat 5 (q + r) := by
  change q ∈ padicIntegral 5 at hq
  change r ∈ padicIntegral 5 at hr
  change q + r ∈ padicIntegral 5
  exact (padicIntegral 5).add_mem hq hr

private lemma integral_sub {q r : ℚ} (hq : 0 ≤ padicValRat 5 q)
    (hr : 0 ≤ padicValRat 5 r) : 0 ≤ padicValRat 5 (q - r) := by
  change q ∈ padicIntegral 5 at hq
  change r ∈ padicIntegral 5 at hr
  change q - r ∈ padicIntegral 5
  exact (padicIntegral 5).sub_mem hq hr

private lemma integral_mul {q r : ℚ} (hq : 0 ≤ padicValRat 5 q)
    (hr : 0 ≤ padicValRat 5 r) : 0 ≤ padicValRat 5 (q * r) := by
  change q ∈ padicIntegral 5 at hq
  change r ∈ padicIntegral 5 at hr
  change q * r ∈ padicIntegral 5
  exact (padicIntegral 5).mul_mem hq hr

private lemma integral_pow {q : ℚ} (hq : 0 ≤ padicValRat 5 q) (n : ℕ) :
    0 ≤ padicValRat 5 (q ^ n) := by
  change q ∈ padicIntegral 5 at hq
  change q ^ n ∈ padicIntegral 5
  exact (padicIntegral 5).pow_mem hq n

private lemma padicValRat_one_add_sq_mul {z t : ℚ}
    (hz : 0 < padicValRat 5 z) (ht : 0 ≤ padicValRat 5 t) :
    padicValRat 5 (1 + z ^ 2 * t) = 0 := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  by_cases ht0 : t = 0
  · simp [ht0]
  have hp0 : z ^ 2 * t ≠ 0 := mul_ne_zero (pow_ne_zero _ hz0) ht0
  have hp : padicValRat 5 (z ^ 2 * t) =
      (2 : ℤ) * padicValRat 5 z + padicValRat 5 t := by
    rw [padicValRat.mul (pow_ne_zero _ hz0) ht0, padicValRat.pow]
    norm_num
  have hp_pos : 0 < padicValRat 5 (z ^ 2 * t) := by omega
  have hsum : (1 : ℚ) + z ^ 2 * t ≠ 0 := by
    intro h
    have heq : z ^ 2 * t = -1 := by linarith
    rw [heq] at hp_pos
    simp at hp_pos
  simpa using padicValRat.add_eq_of_lt (p := 5) hsum one_ne_zero hp0
    (by simpa using hp_pos)

private lemma padicValRat_five_add_sq_mul {z t : ℚ}
    (hz : 0 < padicValRat 5 z) (ht : 0 ≤ padicValRat 5 t) :
    padicValRat 5 (5 + z ^ 2 * t) = 1 := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  by_cases ht0 : t = 0
  · subst t
    simpa using padicValRat.self (p := 5) (by norm_num)
  have hp0 : z ^ 2 * t ≠ 0 := mul_ne_zero (pow_ne_zero _ hz0) ht0
  have hp : padicValRat 5 (z ^ 2 * t) =
      (2 : ℤ) * padicValRat 5 z + padicValRat 5 t := by
    rw [padicValRat.mul (pow_ne_zero _ hz0) ht0, padicValRat.pow]
    norm_num
  have hp_gt : 1 < padicValRat 5 (z ^ 2 * t) := by omega
  have hsum : (5 : ℚ) + z ^ 2 * t ≠ 0 := by
    intro h
    have heq : z ^ 2 * t = -5 := by linarith
    rw [heq] at hp_gt
    rw [padicValRat.neg] at hp_gt
    have h5 : padicValRat 5 (5 : ℚ) = 1 := padicValRat.self (by norm_num)
    omega
  have h5 : padicValRat 5 (5 : ℚ) = 1 := padicValRat.self (by norm_num)
  simpa [h5] using padicValRat.add_eq_of_lt (p := 5) hsum (by norm_num) hp0 (by omega)

private lemma one_add_sq_mul_ne_zero {z t : ℚ}
    (hz : 0 < padicValRat 5 z) (ht : 0 ≤ padicValRat 5 t) :
    (1 : ℚ) + z ^ 2 * t ≠ 0 := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  by_cases ht0 : t = 0
  · simp [ht0]
  have hp0 : z ^ 2 * t ≠ 0 := mul_ne_zero (pow_ne_zero _ hz0) ht0
  have hp : padicValRat 5 (z ^ 2 * t) =
      (2 : ℤ) * padicValRat 5 z + padicValRat 5 t := by
    rw [padicValRat.mul (pow_ne_zero _ hz0) ht0, padicValRat.pow]
    norm_num
  have hp_pos : 0 < padicValRat 5 (z ^ 2 * t) := by omega
  intro h
  have heq : z ^ 2 * t = -1 := by linarith
  rw [heq] at hp_pos
  simp at hp_pos

private lemma five_add_sq_mul_ne_zero {z t : ℚ}
    (hz : 0 < padicValRat 5 z) (ht : 0 ≤ padicValRat 5 t) :
    (5 : ℚ) + z ^ 2 * t ≠ 0 := by
  intro h
  have hv := padicValRat_five_add_sq_mul hz ht
  rw [h] at hv
  simp at hv

private lemma padicValRat_three_add_sq_mul {z t : ℚ}
    (hz : 0 < padicValRat 5 z) (ht : 0 ≤ padicValRat 5 t) :
    padicValRat 5 (3 + z ^ 2 * t) = 0 := by
  have h3 : padicValRat 5 (3 : ℚ) = 0 := by
    change padicValRat 5 ((3 : ℤ) : ℚ) = 0
    rw [padicValRat.of_int]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd (p := 5) (z := (3 : ℤ)) (by norm_num)
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  by_cases ht0 : t = 0
  · simp [ht0, h3]
  have hp0 : z ^ 2 * t ≠ 0 := mul_ne_zero (pow_ne_zero _ hz0) ht0
  have hp : padicValRat 5 (z ^ 2 * t) =
      (2 : ℤ) * padicValRat 5 z + padicValRat 5 t := by
    rw [padicValRat.mul (pow_ne_zero _ hz0) ht0, padicValRat.pow]
    norm_num
  have hp_pos : 0 < padicValRat 5 (z ^ 2 * t) := by omega
  have hsum : (3 : ℚ) + z ^ 2 * t ≠ 0 := by
    intro h
    have heq : z ^ 2 * t = -3 := by linarith
    rw [heq, padicValRat.neg, h3] at hp_pos
    omega
  simpa [h3] using padicValRat.add_eq_of_lt (p := 5) hsum (by norm_num) hp0 (by omega)

private lemma three_add_sq_mul_ne_zero {z t : ℚ}
    (hz : 0 < padicValRat 5 z) (ht : 0 ≤ padicValRat 5 t) :
    (3 : ℚ) + z ^ 2 * t ≠ 0 := by
  have h3 : padicValRat 5 (3 : ℚ) = 0 := by
    change padicValRat 5 ((3 : ℤ) : ℚ) = 0
    rw [padicValRat.of_int]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd (p := 5) (z := (3 : ℤ)) (by norm_num)
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  by_cases ht0 : t = 0
  · simp [ht0]
  have hp : padicValRat 5 (z ^ 2 * t) =
      (2 : ℤ) * padicValRat 5 z + padicValRat 5 t := by
    rw [padicValRat.mul (pow_ne_zero _ hz0) ht0, padicValRat.pow]
    norm_num
  have hp_pos : 0 < padicValRat 5 (z ^ 2 * t) := by omega
  intro h
  have heq : z ^ 2 * t = -3 := by linarith
  rw [heq, padicValRat.neg, h3] at hp_pos
  omega

private def curveTail {R : Type*} [CommRing R] (A B z : R) : R := A + B * z

private def threeTail {R : Type*} [CommRing R] (A B z : R) : R :=
  6 * A + 12 * B * z - A ^ 2 * z ^ 2

private def fourTail {R : Type*} [CommRing R] (A B z : R) : R :=
  5 * A + 20 * B * z - 5 * A ^ 2 * z ^ 2 - 4 * A * B * z ^ 3 -
    (8 * B ^ 2 + A ^ 3) * z ^ 4

private def fiveTail {R : Type*} [CommRing R] (A B z : R) : R :=
  62 * A + 380 * B * z - 105 * A ^ 2 * z ^ 2 + 240 * A * B * z ^ 3 -
    (300 * A ^ 3 + 240 * B ^ 2) * z ^ 4 - 696 * A ^ 2 * B * z ^ 5 -
    (125 * A ^ 4 + 1920 * A * B ^ 2) * z ^ 6 -
    (80 * A ^ 3 * B + 1600 * B ^ 3) * z ^ 7 -
    (50 * A ^ 5 + 240 * A ^ 2 * B ^ 2) * z ^ 8 -
    (100 * A ^ 4 * B + 640 * A * B ^ 3) * z ^ 9 +
    (A ^ 6 - 32 * A ^ 3 * B ^ 2 - 256 * B ^ 4) * z ^ 10

private noncomputable def tailPolynomial (which : ℕ) : Polynomial ℤ :=
  let A := Polynomial.C (-478842624 : ℤ)
  let B := Polynomial.C (3011551764480 : ℤ)
  let z := Polynomial.X
  match which with
  | 0 => curveTail A B z
  | 1 => threeTail A B z
  | 2 => fourTail A B z
  | _ => fiveTail A B z

private lemma integral_eval_int (P : Polynomial ℤ) {z : ℚ}
    (hz : 0 ≤ padicValRat 5 z) :
    0 ≤ padicValRat 5 (P.eval₂ (Int.castRingHom ℚ) z) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa using integral_add hP hQ
  | monomial n a =>
      simp only [Polynomial.eval₂_monomial]
      exact integral_mul (int_padicIntegral 5 a) (integral_pow hz n)

private lemma tailPolynomial_eval (which : ℕ) (z : ℚ) :
    (tailPolynomial which).eval₂ (Int.castRingHom ℚ) z =
      (match which with
       | 0 => curveTail shortA shortB z
       | 1 => threeTail shortA shortB z
       | 2 => fourTail shortA shortB z
       | _ => fiveTail shortA shortB z) := by
  rcases which with _ | which
  · simp [tailPolynomial, curveTail, shortA, shortB, Polynomial.eval₂_pow]
  rcases which with _ | which
  · simp [tailPolynomial, threeTail, shortA, shortB, Polynomial.eval₂_pow]
  rcases which with _ | which
  · simp [tailPolynomial, fourTail, shortA, shortB, Polynomial.eval₂_pow]
  · simp [tailPolynomial, fiveTail, shortA, shortB, Polynomial.eval₂_pow]

private lemma integral_tail (which : ℕ) {z : ℚ} (hz : 0 ≤ padicValRat 5 z) :
    let A := shortA
    let B := shortB
    0 ≤ padicValRat 5
      (match which with
       | 0 => curveTail A B z
       | 1 => threeTail A B z
       | 2 => fourTail A B z
       | _ => fiveTail A B z) := by
  dsimp
  rw [← tailPolynomial_eval]
  exact integral_eval_int _ hz

def curvePoly (x : ℚ) : ℚ := x ^ 3 + shortA * x + shortB

def threePoly (x : ℚ) : ℚ :=
  3 * x ^ 4 + 6 * shortA * x ^ 2 + 12 * shortB * x - shortA ^ 2

def fourPoly (x : ℚ) : ℚ :=
  x ^ 6 + 5 * shortA * x ^ 4 + 20 * shortB * x ^ 3 - 5 * shortA ^ 2 * x ^ 2 -
    4 * shortA * shortB * x - 8 * shortB ^ 2 - shortA ^ 3

def fivePoly (x : ℚ) : ℚ :=
  32 * curvePoly x ^ 2 * fourPoly x - threePoly x ^ 3

def fivePhi (x : ℚ) : ℚ :=
  x * fivePoly x ^ 2 -
    8 * curvePoly x * threePoly x * fourPoly x * (fivePoly x - 4 * fourPoly x ^ 2)

def sevenPoly (x : ℚ) : ℚ :=
  fivePoly x * threePoly x ^ 3 - 128 * curvePoly x ^ 2 * fourPoly x ^ 3

def fiveYPoly (x : ℚ) : ℚ :=
  4 * fourPoly x ^ 2 * sevenPoly x -
    threePoly x ^ 3 * (fivePoly x - 4 * fourPoly x ^ 2) ^ 2

/-- Multiplication by five written only with the univariate division polynomials. -/
def fiveMap (P : ℚ × ℚ) : ℚ × ℚ :=
  (fivePhi P.1 / fivePoly P.1 ^ 2,
    P.2 * fiveYPoly P.1 / fivePoly P.1 ^ 3)

private lemma curvePoly_reverse {x : ℚ} (hx : x ≠ 0) :
    curvePoly x = x ^ 3 * (1 + x⁻¹ ^ 2 * curveTail shortA shortB x⁻¹) := by
  simp only [curvePoly, curveTail]
  simp only [inv_eq_one_div]
  field_simp [hx]
  ring

private lemma threePoly_reverse {x : ℚ} (hx : x ≠ 0) :
    threePoly x = x ^ 4 * (3 + x⁻¹ ^ 2 * threeTail shortA shortB x⁻¹) := by
  simp only [threePoly, threeTail]
  simp only [inv_eq_one_div]
  field_simp [hx]
  ring

private lemma fourPoly_reverse {x : ℚ} (hx : x ≠ 0) :
    fourPoly x = x ^ 6 * (1 + x⁻¹ ^ 2 * fourTail shortA shortB x⁻¹) := by
  simp only [fourPoly, fourTail]
  simp only [inv_eq_one_div]
  field_simp [hx]
  ring

private lemma fivePoly_reverse {x : ℚ} (hx : x ≠ 0) :
    fivePoly x = x ^ 12 * (5 + x⁻¹ ^ 2 * fiveTail shortA shortB x⁻¹) := by
  simp only [fivePoly, curvePoly, threePoly, fourPoly, fiveTail]
  simp only [inv_eq_one_div]
  field_simp [hx]
  ring

private lemma curvePoly_padicVal {x : ℚ} (hv : padicValRat 5 x < 0) :
    padicValRat 5 (curvePoly x) = 3 * padicValRat 5 x := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hz : 0 < padicValRat 5 x⁻¹ := by simp [hv]
  have ht : 0 ≤ padicValRat 5 (curveTail shortA shortB x⁻¹) := by
    simpa using integral_tail 0 (le_of_lt hz)
  have hr := padicValRat_one_add_sq_mul hz ht
  have hr0 := one_add_sq_mul_ne_zero hz ht
  rw [curvePoly_reverse hx, padicValRat.mul (pow_ne_zero _ hx) hr0,
    padicValRat.pow, hr]
  norm_num

private lemma threePoly_padicVal {x : ℚ} (hv : padicValRat 5 x < 0) :
    padicValRat 5 (threePoly x) = 4 * padicValRat 5 x := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hz : 0 < padicValRat 5 x⁻¹ := by simp [hv]
  have ht : 0 ≤ padicValRat 5 (threeTail shortA shortB x⁻¹) := by
    simpa using integral_tail 1 (le_of_lt hz)
  have hr := padicValRat_three_add_sq_mul hz ht
  have hr0 := three_add_sq_mul_ne_zero hz ht
  rw [threePoly_reverse hx, padicValRat.mul (pow_ne_zero _ hx) hr0,
    padicValRat.pow, hr]
  norm_num

private lemma fourPoly_padicVal {x : ℚ} (hv : padicValRat 5 x < 0) :
    padicValRat 5 (fourPoly x) = 6 * padicValRat 5 x := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hz : 0 < padicValRat 5 x⁻¹ := by simp [hv]
  have ht : 0 ≤ padicValRat 5 (fourTail shortA shortB x⁻¹) := by
    simpa using integral_tail 2 (le_of_lt hz)
  have hr := padicValRat_one_add_sq_mul hz ht
  have hr0 := one_add_sq_mul_ne_zero hz ht
  rw [fourPoly_reverse hx, padicValRat.mul (pow_ne_zero _ hx) hr0,
    padicValRat.pow, hr]
  norm_num

private lemma fivePoly_padicVal {x : ℚ} (hv : padicValRat 5 x < 0) :
    padicValRat 5 (fivePoly x) = 12 * padicValRat 5 x + 1 := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hz : 0 < padicValRat 5 x⁻¹ := by simp [hv]
  have ht : 0 ≤ padicValRat 5 (fiveTail shortA shortB x⁻¹) := by
    simpa using integral_tail 3 (le_of_lt hz)
  have hr := padicValRat_five_add_sq_mul hz ht
  have hr0 := five_add_sq_mul_ne_zero hz ht
  rw [fivePoly_reverse hx, padicValRat.mul (pow_ne_zero _ hx) hr0,
    padicValRat.pow, hr]
  norm_num

private lemma curvePoly_ne_zero {x : ℚ} (hv : padicValRat 5 x < 0) : curvePoly x ≠ 0 := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hz : 0 < padicValRat 5 x⁻¹ := by rw [padicValRat.inv]; omega
  rw [curvePoly_reverse hx]
  exact mul_ne_zero (pow_ne_zero _ hx)
    (one_add_sq_mul_ne_zero hz (by simpa using integral_tail 0 (le_of_lt hz)))

private lemma threePoly_ne_zero {x : ℚ} (hv : padicValRat 5 x < 0) : threePoly x ≠ 0 := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hz : 0 < padicValRat 5 x⁻¹ := by rw [padicValRat.inv]; omega
  rw [threePoly_reverse hx]
  exact mul_ne_zero (pow_ne_zero _ hx)
    (three_add_sq_mul_ne_zero hz (by simpa using integral_tail 1 (le_of_lt hz)))

private lemma fourPoly_ne_zero {x : ℚ} (hv : padicValRat 5 x < 0) : fourPoly x ≠ 0 := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hz : 0 < padicValRat 5 x⁻¹ := by rw [padicValRat.inv]; omega
  rw [fourPoly_reverse hx]
  exact mul_ne_zero (pow_ne_zero _ hx)
    (one_add_sq_mul_ne_zero hz (by simpa using integral_tail 2 (le_of_lt hz)))

private lemma fivePoly_ne_zero {x : ℚ} (hv : padicValRat 5 x < 0) : fivePoly x ≠ 0 := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hz : 0 < padicValRat 5 x⁻¹ := by rw [padicValRat.inv]; omega
  rw [fivePoly_reverse hx]
  exact mul_ne_zero (pow_ne_zero _ hx)
    (five_add_sq_mul_ne_zero hz (by simpa using integral_tail 3 (le_of_lt hz)))

private lemma intUnit_padicVal {z : ℤ} (hz : ¬(5 : ℤ) ∣ z) :
    padicValRat 5 (z : ℚ) = 0 := by
  rw [padicValRat.of_int]
  exact_mod_cast padicValInt.eq_zero_of_not_dvd hz

private lemma fiveMinusFourSq_padicVal {x : ℚ} (hv : padicValRat 5 x < 0) :
    padicValRat 5 (fivePoly x - 4 * fourPoly x ^ 2) = 12 * padicValRat 5 x := by
  have h5v := fivePoly_padicVal hv
  have h4v := fourPoly_padicVal hv
  have h50 := fivePoly_ne_zero hv
  have h40 := fourPoly_ne_zero hv
  have hc4 : padicValRat 5 (4 : ℚ) = 0 := intUnit_padicVal (by norm_num)
  have hs0 : (4 : ℚ) * fourPoly x ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ h40)
  have hsv : padicValRat 5 ((4 : ℚ) * fourPoly x ^ 2) =
      12 * padicValRat 5 x := by
    rw [padicValRat.mul (by norm_num) (pow_ne_zero _ h40), hc4, padicValRat.pow, h4v]
    ring
  have hlt : padicValRat 5 (-((4 : ℚ) * fourPoly x ^ 2)) <
      padicValRat 5 (fivePoly x) := by simp only [padicValRat.neg, hsv, h5v]; omega
  have hsum : -((4 : ℚ) * fourPoly x ^ 2) + fivePoly x ≠ 0 := by
    intro h
    have heq : fivePoly x = (4 : ℚ) * fourPoly x ^ 2 := by linarith
    have := congrArg (padicValRat 5) heq
    rw [h5v, hsv] at this
    omega
  have := padicValRat.add_eq_of_lt (p := 5) hsum (neg_ne_zero.mpr hs0) h50 hlt
  rw [padicValRat.neg, hsv] at this
  simpa [sub_eq_add_neg, add_comm] using this

private lemma fivePhi_padicVal {x : ℚ} (hv : padicValRat 5 x < 0) :
    padicValRat 5 (fivePhi x) = 25 * padicValRat 5 x := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hC0 := curvePoly_ne_zero hv
  have h30 := threePoly_ne_zero hv
  have h40 := fourPoly_ne_zero hv
  have h50 := fivePoly_ne_zero hv
  have hd0 : fivePoly x - 4 * fourPoly x ^ 2 ≠ 0 := by
    intro h
    have hv0 := fiveMinusFourSq_padicVal hv
    rw [h] at hv0
    simp at hv0
    omega
  have hCv := curvePoly_padicVal hv
  have h3v := threePoly_padicVal hv
  have h4v := fourPoly_padicVal hv
  have h5v := fivePoly_padicVal hv
  have hdv := fiveMinusFourSq_padicVal hv
  have h8v : padicValRat 5 (8 : ℚ) = 0 := intUnit_padicVal (by norm_num)
  let U := x * fivePoly x ^ 2
  let V := 8 * curvePoly x * threePoly x * fourPoly x *
    (fivePoly x - 4 * fourPoly x ^ 2)
  have hU0 : U ≠ 0 := mul_ne_zero hx (pow_ne_zero _ h50)
  have hV0 : V ≠ 0 := by
    dsimp [V]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hC0) h30) h40) hd0
  have hUv : padicValRat 5 U = 25 * padicValRat 5 x + 2 := by
    dsimp [U]
    rw [padicValRat.mul hx (pow_ne_zero _ h50), padicValRat.pow, h5v]
    ring
  have hVv : padicValRat 5 V = 25 * padicValRat 5 x := by
    dsimp [V]
    rw [padicValRat.mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hC0) h30) h40) hd0,
      padicValRat.mul (mul_ne_zero (mul_ne_zero (by norm_num) hC0) h30) h40,
      padicValRat.mul (mul_ne_zero (by norm_num) hC0) h30,
      padicValRat.mul (by norm_num) hC0, h8v, hCv, h3v, h4v, hdv]
    ring
  have hsum : -V + U ≠ 0 := by
    intro h
    have heq : U = V := by linarith
    have := congrArg (padicValRat 5) heq
    rw [hUv, hVv] at this
    omega
  have hval := padicValRat.add_eq_of_lt (p := 5) hsum (neg_ne_zero.mpr hV0) hU0 (by
    simp only [padicValRat.neg, hUv, hVv]
    omega)
  rw [padicValRat.neg, hVv] at hval
  simpa [fivePhi, U, V, sub_eq_add_neg, add_comm] using hval

private lemma fiveMap_fst_padicVal {P : ℚ × ℚ} (hv : padicValRat 5 P.1 < 0) :
    padicValRat 5 (fiveMap P).1 = padicValRat 5 P.1 - 2 := by
  have hphi0 : fivePhi P.1 ≠ 0 := by
    intro h
    have hv0 := fivePhi_padicVal hv
    rw [h] at hv0
    simp at hv0
    omega
  have h50 := fivePoly_ne_zero hv
  simp only [fiveMap, Prod.fst]
  rw [padicValRat.div hphi0 (pow_ne_zero _ h50), fivePhi_padicVal hv,
    padicValRat.pow, fivePoly_padicVal hv]
  ring

private lemma five_curve_polynomial_identity (x : ℚ) :
    curvePoly x * fiveYPoly x ^ 2 =
      fivePhi x ^ 3 + shortA * fivePhi x * fivePoly x ^ 4 + shortB * fivePoly x ^ 6 := by
  simp only [curvePoly, threePoly, fourPoly, fivePoly, fivePhi, sevenPoly, fiveYPoly,
    shortA, shortB]
  ring

lemma fiveMap_onCurve {P : ℚ × ℚ} (hP : ShortOnCurve P)
    (hv : padicValRat 5 P.1 < 0) : ShortOnCurve (fiveMap P) := by
  have h50 := fivePoly_ne_zero hv
  have hc : P.2 ^ 2 = curvePoly P.1 := by
    simpa [ShortOnCurve, curvePoly] using hP
  simp only [ShortOnCurve, fiveMap, Prod.fst, Prod.snd]
  field_simp [h50]
  rw [hc, five_curve_polynomial_identity]
  ring

/-- The point `2P₁` on the short model. -/
def shortStart : ℚ × ℚ :=
  (Rat.divInt 21443383536 511225,
    Rat.divInt (-2752977651830784) 365525875)

lemma shortStart_onCurve : ShortOnCurve shortStart := by
  norm_num [ShortOnCurve, shortStart, shortA, shortB, Rat.divInt_eq_div]

lemma shortStart_fst_padicVal : padicValRat 5 shortStart.1 = -2 := by
  simp only [shortStart, Prod.fst, padicValRat_def]
  rw [Rat.divInt_eq_div]
  rw [Rat.num_div_eq_of_coprime (by norm_num) (by norm_num)]
  have hdenrat : (((21443383536 : ℤ) : ℚ) / ((511225 : ℤ) : ℚ)).den = 511225 := by
    exact_mod_cast Rat.den_div_eq_of_coprime (a := 21443383536) (b := 511225)
      (by norm_num) (by norm_num)
  rw [hdenrat]
  have hn : padicValInt 5 21443383536 = 0 :=
    padicValInt.eq_zero_of_not_dvd (by norm_num)
  have hd : padicValNat 5 511225 = 2 := by
    apply le_antisymm
    · by_contra h
      have h3 : 3 ≤ padicValNat 5 511225 := by omega
      have := (pow_dvd_iff_le_padicValNat (p := 5) (k := 3) (n := 511225)
        (by norm_num) (by norm_num)).2 h3
      norm_num at this
    · exact (pow_dvd_iff_le_padicValNat (p := 5) (k := 2) (n := 511225)
        (by norm_num) (by norm_num)).1 (by norm_num)
  omega

lemma shortStart_snd_padicVal : padicValRat 5 shortStart.2 = -3 := by
  simp only [shortStart, Prod.snd, padicValRat_def]
  rw [Rat.divInt_eq_div]
  rw [Rat.num_div_eq_of_coprime (by norm_num) (by norm_num)]
  have hdenrat : (((-2752977651830784 : ℤ) : ℚ) /
      ((365525875 : ℤ) : ℚ)).den = 365525875 := by
    exact_mod_cast Rat.den_div_eq_of_coprime (a := -2752977651830784) (b := 365525875)
      (by norm_num) (by norm_num)
  rw [hdenrat]
  have hn : padicValInt 5 (-2752977651830784) = 0 :=
    padicValInt.eq_zero_of_not_dvd (by norm_num)
  have hd : padicValNat 5 365525875 = 3 := by
    apply le_antisymm
    · by_contra h
      have h4 : 4 ≤ padicValNat 5 365525875 := by omega
      have := (pow_dvd_iff_le_padicValNat (p := 5) (k := 4) (n := 365525875)
        (by norm_num) (by norm_num)).2 h4
      norm_num at this
    · exact (pow_dvd_iff_le_padicValNat (p := 5) (k := 3) (n := 365525875)
        (by norm_num) (by norm_num)).1 (by norm_num)
  omega

/-! ## The infinite rational orbit and the quartic -/

def orbit (n : ℕ) : ℚ × ℚ := (fiveMap^[n]) shortStart

lemma orbit_fst_padicVal (n : ℕ) : padicValRat 5 (orbit n).1 = -2 - 2 * n := by
  induction n with
  | zero => simpa [orbit] using shortStart_fst_padicVal
  | succ n ih =>
      rw [orbit, Function.iterate_succ_apply']
      rw [fiveMap_fst_padicVal]
      · simp only [orbit] at ih
        omega
      · simp only [orbit] at ih
        omega

lemma orbit_onCurve (n : ℕ) : ShortOnCurve (orbit n) := by
  induction n with
  | zero => simpa [orbit] using shortStart_onCurve
  | succ n ih =>
      rw [orbit, Function.iterate_succ_apply']
      apply fiveMap_onCurve
      · simpa [orbit] using ih
      · have hv := orbit_fst_padicVal n
        simp only [orbit] at hv ⊢
        omega

private lemma short_snd_padicVal {P : ℚ × ℚ} (hP : ShortOnCurve P)
    (hv : padicValRat 5 P.1 < 0) :
    padicValRat 5 P.2 = 3 * padicValRat 5 P.1 / 2 := by
  have hc : P.2 ^ 2 = curvePoly P.1 := by
    simpa [ShortOnCurve, curvePoly] using hP
  have hC0 := curvePoly_ne_zero hv
  have hy0 : P.2 ≠ 0 := by
    intro h
    rw [h] at hc
    simp at hc
    exact hC0 hc.symm
  have hval := congrArg (padicValRat 5) hc
  rw [padicValRat.pow, curvePoly_padicVal hv] at hval
  norm_num at hval
  omega

lemma orbit_snd_padicVal (n : ℕ) : padicValRat 5 (orbit n).2 = -3 - 3 * n := by
  have hx := orbit_fst_padicVal n
  have hy := short_snd_padicVal (orbit_onCurve n) (by omega : padicValRat 5 (orbit n).1 < 0)
  omega

/-- The old BBC `x`-coordinate recovered from the integral short model. -/
def bbcX (P : ℚ × ℚ) : ℚ :=
  (P.1 - ((17808 : ℤ) : ℚ)) / ((36 : ℤ) : ℚ)

/-- The old BBC `y`-coordinate recovered from the integral short model. -/
def bbcY (P : ℚ × ℚ) : ℚ :=
  (P.2 / ((108 : ℤ) : ℚ) + ((128 : ℤ) : ℚ) * bbcX P +
    ((3360 : ℤ) : ℚ)) / ((2 : ℤ) : ℚ)

def BBCOnCurve (P : ℚ × ℚ) : Prop :=
  P.2 ^ 2 - 128 * P.1 * P.2 - 3360 * P.2 =
    P.1 ^ 3 - 2612 * P.1 ^ 2 + 149568 * P.1

lemma short_to_BBC {P : ℚ × ℚ} (hP : ShortOnCurve P) :
    BBCOnCurve (bbcX P, bbcY P) := by
  simp only [ShortOnCurve, bbcX, bbcY, BBCOnCurve, Prod.fst, Prod.snd] at hP ⊢
  norm_num [shortA, shortB] at hP
  field_simp
  ring_nf at hP ⊢
  linarith

/-- The quartic parameter associated to a short-model point. -/
def quarticX (P : ℚ × ℚ) : ℚ := 146 * bbcX P / bbcY P - 2

def quarticY (P : ℚ × ℚ) : ℚ :=
  (bbcX P ^ 3 - 149568 * bbcX P - 3360 * bbcY P) / bbcY P ^ 2

lemma BBC_to_quartic {P : ℚ × ℚ} (hP : ShortOnCurve P) (hy : bbcY P ≠ 0) :
    quarticX P ^ 4 - 8 * quarticX P ^ 3 + 2 * quarticX P ^ 2 +
      8 * quarticX P + 1 = 73 * quarticY P ^ 2 := by
  have he := short_to_BBC hP
  simp only [BBCOnCurve, Prod.fst, Prod.snd] at he
  have he0 :
      bbcY P ^ 2 - 128 * bbcX P * bbcY P - 3360 * bbcY P -
        (bbcX P ^ 3 - 2612 * bbcX P ^ 2 + 149568 * bbcX P) = 0 :=
    sub_eq_zero.mpr he
  simp only [quarticX, quarticY]
  field_simp [hy]
  linear_combination (norm := ring)
    73 * (bbcX P ^ 3 + 2612 * bbcX P ^ 2 - 128 * bbcX P * bbcY P +
      149568 * bbcX P + bbcY P ^ 2 + 3360 * bbcY P) * he0

private lemma padicVal_sub_int {q : ℚ} (z : ℤ) (hq : padicValRat 5 q < 0) :
    padicValRat 5 (q - z) = padicValRat 5 q := by
  by_cases hz0 : z = 0
  · simp [hz0]
  have hz := int_padicIntegral 5 z
  have hq0 : q ≠ 0 := by intro h; simp [h] at hq
  have hnegz : -(z : ℚ) ≠ 0 := by
    exact neg_ne_zero.mpr (Int.cast_ne_zero.mpr hz0)
  have hsum : q + -(z : ℚ) ≠ 0 := by
    intro h
    have heq : q = (z : ℚ) := by linarith
    have := congrArg (padicValRat 5) heq
    rw [this] at hq
    omega
  have h := padicValRat.add_eq_of_lt (p := 5) hsum hq0 hnegz
    (by simpa using lt_of_lt_of_le hq hz)
  simpa [sub_eq_add_neg] using h

lemma orbit_bbcX_padicVal (n : ℕ) :
    padicValRat 5 (bbcX (orbit n)) = -2 - 2 * n := by
  have hx := orbit_fst_padicVal n
  have hnum := padicVal_sub_int (17808 : ℤ) (by omega : padicValRat 5 (orbit n).1 < 0)
  have hnum0 : (orbit n).1 - ((17808 : ℤ) : ℚ) ≠ 0 := by
    intro h
    rw [h] at hnum
    simp at hnum
    omega
  have h36 : padicValRat 5 (((36 : ℤ) : ℚ)) = 0 :=
    intUnit_padicVal (by norm_num)
  simp only [bbcX]
  rw [padicValRat.div hnum0 (by norm_num), hnum, h36, hx]
  omega

lemma orbit_bbcY_padicVal (n : ℕ) :
    padicValRat 5 (bbcY (orbit n)) = -3 - 3 * n := by
  let yterm : ℚ := (orbit n).2 / 108
  let xterm : ℚ := 128 * bbcX (orbit n)
  have hy := orbit_snd_padicVal n
  have hx := orbit_bbcX_padicVal n
  have hy0 : (orbit n).2 ≠ 0 := by intro h; simp [h] at hy; omega
  have h108 : padicValRat 5 (108 : ℚ) = 0 := intUnit_padicVal (by norm_num)
  have h128 : padicValRat 5 (128 : ℚ) = 0 := intUnit_padicVal (by norm_num)
  have hx0 : bbcX (orbit n) ≠ 0 := by intro h; simp [h] at hx; omega
  have hyv : padicValRat 5 yterm = -3 - 3 * n := by
    dsimp [yterm]
    rw [padicValRat.div hy0 (by norm_num), hy, h108]
    omega
  have hxv : padicValRat 5 xterm = -2 - 2 * n := by
    dsimp [xterm]
    rw [padicValRat.mul (by norm_num) hx0, h128, hx]
    omega
  have hyterm0 : yterm ≠ 0 := by intro h; rw [h] at hyv; simp at hyv; omega
  have hxterm0 : xterm ≠ 0 := by intro h; rw [h] at hxv; simp at hxv; omega
  have hxy0 : yterm + xterm ≠ 0 := by
    intro h
    have heq : yterm = -xterm := by linarith
    have := congrArg (padicValRat 5) heq
    rw [hyv, padicValRat.neg, hxv] at this
    omega
  have hxyv : padicValRat 5 (yterm + xterm) = -3 - 3 * n := by
    rw [padicValRat.add_eq_of_lt (p := 5) hxy0 hyterm0 hxterm0 (by omega), hyv]
  have h3360 : 0 ≤ padicValRat 5 (((3360 : ℤ) : ℚ)) :=
    int_padicIntegral 5 (3360 : ℤ)
  have hsum0 : yterm + xterm + ((3360 : ℤ) : ℚ) ≠ 0 := by
    intro h
    have heq : yterm + xterm = -(((3360 : ℤ) : ℚ)) := by linarith
    have := congrArg (padicValRat 5) heq
    rw [hxyv, padicValRat.neg] at this
    omega
  have hlt :
      padicValRat 5 (yterm + xterm) < padicValRat 5 (((3360 : ℤ) : ℚ)) := by
    rw [hxyv]
    exact lt_of_lt_of_le (by omega) h3360
  have hsumv :
      padicValRat 5 (yterm + xterm + ((3360 : ℤ) : ℚ)) = -3 - 3 * n := by
    rw [padicValRat.add_eq_of_lt (p := 5) hsum0 (by
      intro h; rw [h] at hxyv; simp at hxyv; omega) (by norm_num) hlt, hxyv]
  have h2 : padicValRat 5 (2 : ℚ) = 0 := intUnit_padicVal (by norm_num)
  simp only [bbcY]
  change padicValRat 5 ((yterm + xterm + ((3360 : ℤ) : ℚ)) / 2) = _
  rw [padicValRat.div hsum0 (by norm_num), hsumv, h2]
  omega

lemma orbit_bbcY_ne_zero (n : ℕ) : bbcY (orbit n) ≠ 0 := by
  intro h
  have hv := orbit_bbcY_padicVal n
  rw [h] at hv
  simp at hv
  omega

lemma orbit_quarticX_add_two_padicVal (n : ℕ) :
    padicValRat 5 (quarticX (orbit n) + 2) = 1 + n := by
  have hx := orbit_bbcX_padicVal n
  have hy := orbit_bbcY_padicVal n
  have hx0 : bbcX (orbit n) ≠ 0 := by intro h; simp [h] at hx; omega
  have hy0 := orbit_bbcY_ne_zero n
  have h146 : padicValRat 5 (146 : ℚ) = 0 := intUnit_padicVal (by norm_num)
  simp only [quarticX]
  rw [sub_add_cancel]
  rw [padicValRat.div (mul_ne_zero (by norm_num) hx0) hy0,
    padicValRat.mul (by norm_num) hx0, h146, hx, hy]
  omega

lemma quarticX_orbit_injective : Function.Injective (fun n : ℕ => quarticX (orbit n)) := by
  intro m n h
  have h' := congrArg (fun q : ℚ => padicValRat 5 (q + 2)) h
  rw [orbit_quarticX_add_two_padicVal, orbit_quarticX_add_two_padicVal] at h'
  omega

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos937.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 937.
https://www.erdosproblems.com/forum/thread/937

Informal authors:
- Prajeet Bajpai
- Michael A. Bennett
- Tsz Ho Chan

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos937.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/937.lean
-/



open Nat Set

/-! ## The orbit modulo 73

The short model has both coefficients divisible by 73.  Thus its reduction is the cuspidal
cubic `Y² = X³`; on its nonsingular locus multiplication by five sends `(X,Y)` to
`(X / 25, Y / 125)`.  We record reduction of rational numbers by an elementary relation,
so no nonexistent homomorphism from all of `ℚ` to `ZMod 73` is used. -/

private abbrev F73 := ZMod 73

private instance : Fact (Nat.Prime 73) := ⟨by decide⟩
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- `Reduces73 q z` means that `q` has a presentation with denominator prime to 73 whose
reduction is `z`. -/
private def Reduces73 (q : ℚ) (z : F73) : Prop :=
  ∃ a b : ℤ, (b : F73) ≠ 0 ∧
    q = (a : ℚ) / (b : ℚ) ∧ z = (a : F73) / (b : F73)

private lemma reduces73_int (a : ℤ) : Reduces73 (a : ℚ) (a : F73) := by
  refine ⟨a, 1, by norm_num, ?_, ?_⟩ <;> norm_num

private lemma reduces73_add {q r : ℚ} {x y : F73}
    (hq : Reduces73 q x) (hr : Reduces73 r y) : Reduces73 (q + r) (x + y) := by
  rcases hq with ⟨a, b, hb, hq, hx⟩
  rcases hr with ⟨c, d, hd, hr, hy⟩
  have hb0 : b ≠ 0 := by intro h; subst b; simp at hb
  have hd0 : d ≠ 0 := by intro h; subst d; simp at hd
  refine ⟨a * d + c * b, b * d, ?_, ?_, ?_⟩
  · simpa only [Int.cast_mul] using mul_ne_zero hb hd
  · rw [hq, hr]
    push_cast
    field_simp [hb0, hd0]
  · rw [hx, hy]
    push_cast
    field_simp [hb, hd]

private lemma reduces73_neg {q : ℚ} {x : F73} (hq : Reduces73 q x) :
    Reduces73 (-q) (-x) := by
  rcases hq with ⟨a, b, hb, hq, hx⟩
  refine ⟨-a, b, hb, ?_, ?_⟩
  · rw [hq]
    push_cast
    ring
  · rw [hx]
    push_cast
    ring

private lemma reduces73_sub {q r : ℚ} {x y : F73}
    (hq : Reduces73 q x) (hr : Reduces73 r y) : Reduces73 (q - r) (x - y) := by
  simpa [sub_eq_add_neg] using reduces73_add hq (reduces73_neg hr)

private lemma reduces73_mul {q r : ℚ} {x y : F73}
    (hq : Reduces73 q x) (hr : Reduces73 r y) : Reduces73 (q * r) (x * y) := by
  rcases hq with ⟨a, b, hb, hq, hx⟩
  rcases hr with ⟨c, d, hd, hr, hy⟩
  have hb0 : b ≠ 0 := by intro h; subst b; simp at hb
  have hd0 : d ≠ 0 := by intro h; subst d; simp at hd
  refine ⟨a * c, b * d, ?_, ?_, ?_⟩
  · simpa only [Int.cast_mul] using mul_ne_zero hb hd
  · rw [hq, hr]
    push_cast
    field_simp [hb0, hd0]
  · rw [hx, hy]
    push_cast
    field_simp [hb, hd]

private lemma reduces73_pow {q : ℚ} {x : F73} (hq : Reduces73 q x) (n : ℕ) :
    Reduces73 (q ^ n) (x ^ n) := by
  induction n with
  | zero => simpa using reduces73_int 1
  | succ n ih => simpa [pow_succ] using reduces73_mul ih hq

private lemma reduces73_inv {q : ℚ} {x : F73} (hq : Reduces73 q x) (hx0 : x ≠ 0) :
    Reduces73 q⁻¹ x⁻¹ := by
  rcases hq with ⟨a, b, hb, hq, hx⟩
  have ha : (a : F73) ≠ 0 := by
    intro ha
    apply hx0
    rw [hx, ha]
    simp
  have ha0 : a ≠ 0 := by intro h; subst a; simp at ha
  have hb0 : b ≠ 0 := by intro h; subst b; simp at hb
  refine ⟨b, a, ha, ?_, ?_⟩
  · rw [hq]
    push_cast
    field_simp [ha0, hb0]
  · rw [hx]
    push_cast
    field_simp [ha, hb]

private lemma reduces73_div {q r : ℚ} {x y : F73}
    (hq : Reduces73 q x) (hr : Reduces73 r y) (hy0 : y ≠ 0) :
    Reduces73 (q / r) (x / y) := by
  simpa [div_eq_mul_inv] using reduces73_mul hq (reduces73_inv hr hy0)

private lemma reduces73_right {q : ℚ} {x y : F73}
    (hq : Reduces73 q x) (hxy : x = y) : Reduces73 q y := by
  simpa [hxy] using hq

private lemma shortA_reduces73 : Reduces73 shortA 0 := by
  convert reduces73_int (-478842624) using 1
  · norm_num [shortA]
  · decide

private lemma shortB_reduces73 : Reduces73 shortB 0 := by
  convert reduces73_int 3011551764480 using 1
  · norm_num [shortB]
  · decide

private lemma curvePoly_reduces73 {q : ℚ} {x : F73} (hq : Reduces73 q x) :
    Reduces73 (curvePoly q) (x ^ 3) := by
  simpa [curvePoly] using
    reduces73_add (reduces73_add (reduces73_pow hq 3)
      (reduces73_mul shortA_reduces73 hq)) shortB_reduces73

private lemma threePoly_reduces73 {q : ℚ} {x : F73} (hq : Reduces73 q x) :
    Reduces73 (threePoly q) (3 * x ^ 4) := by
  have h3 := reduces73_int 3
  have h6 := reduces73_int 6
  have h12 := reduces73_int 12
  simpa [threePoly] using
    reduces73_sub
      (reduces73_add
        (reduces73_add (reduces73_mul h3 (reduces73_pow hq 4))
          (reduces73_mul (reduces73_mul h6 shortA_reduces73) (reduces73_pow hq 2)))
        (reduces73_mul (reduces73_mul h12 shortB_reduces73) hq))
      (reduces73_pow shortA_reduces73 2)

private lemma fourPoly_reduces73 {q : ℚ} {x : F73} (hq : Reduces73 q x) :
    Reduces73 (fourPoly q) (x ^ 6) := by
  have h4 := reduces73_int 4
  have h5 := reduces73_int 5
  have h8 := reduces73_int 8
  have h20 := reduces73_int 20
  have raw := reduces73_sub
      (reduces73_sub
        (reduces73_sub
          (reduces73_sub
            (reduces73_add
              (reduces73_add
                (reduces73_add (reduces73_pow hq 6)
                  (reduces73_mul (reduces73_mul h5 shortA_reduces73)
                    (reduces73_pow hq 4)))
                (reduces73_mul (reduces73_mul h20 shortB_reduces73)
                  (reduces73_pow hq 3)))
              (reduces73_neg (reduces73_mul
                (reduces73_mul h5 (reduces73_pow shortA_reduces73 2))
                (reduces73_pow hq 2))))
            (reduces73_mul
              (reduces73_mul (reduces73_mul h4 shortA_reduces73) shortB_reduces73) hq))
          (reduces73_mul h8 (reduces73_pow shortB_reduces73 2)))
        (reduces73_pow shortA_reduces73 3))
      (reduces73_int 0)
  convert raw using 1
  · simp only [fourPoly, shortA, shortB]
    ring
  · ring

private lemma fivePoly_reduces73 {q : ℚ} {x : F73} (hq : Reduces73 q x) :
    Reduces73 (fivePoly q) (5 * x ^ 12) := by
  have hc := curvePoly_reduces73 hq
  have h3 := threePoly_reduces73 hq
  have h4 := fourPoly_reduces73 hq
  have raw := reduces73_sub
    (reduces73_mul (reduces73_mul (reduces73_int 32) (reduces73_pow hc 2)) h4)
    (reduces73_pow h3 3)
  apply reduces73_right (by simpa [fivePoly] using raw)
  ring

private lemma fivePhi_reduces73 {q : ℚ} {x : F73} (hq : Reduces73 q x) :
    Reduces73 (fivePhi q) (x ^ 25) := by
  have hc := curvePoly_reduces73 hq
  have h3 := threePoly_reduces73 hq
  have h4 := fourPoly_reduces73 hq
  have h5 := fivePoly_reduces73 hq
  have raw := reduces73_sub
    (reduces73_mul hq (reduces73_pow h5 2))
    (reduces73_mul
      (reduces73_mul
        (reduces73_mul (reduces73_mul (reduces73_int 8) hc) h3) h4)
      (reduces73_sub h5
        (reduces73_mul (reduces73_int 4) (reduces73_pow h4 2))))
  apply reduces73_right (by simpa [fivePhi] using raw)
  ring

private lemma sevenPoly_reduces73 {q : ℚ} {x : F73} (hq : Reduces73 q x) :
    Reduces73 (sevenPoly q) (7 * x ^ 24) := by
  have hc := curvePoly_reduces73 hq
  have h3 := threePoly_reduces73 hq
  have h4 := fourPoly_reduces73 hq
  have h5 := fivePoly_reduces73 hq
  have raw := reduces73_sub
    (reduces73_mul h5 (reduces73_pow h3 3))
    (reduces73_mul
      (reduces73_mul (reduces73_int 128) (reduces73_pow hc 2))
      (reduces73_pow h4 3))
  apply reduces73_right (by simpa [sevenPoly] using raw)
  ring

private lemma fiveYPoly_reduces73 {q : ℚ} {x : F73} (hq : Reduces73 q x) :
    Reduces73 (fiveYPoly q) (x ^ 36) := by
  have h3 := threePoly_reduces73 hq
  have h4 := fourPoly_reduces73 hq
  have h5 := fivePoly_reduces73 hq
  have h7 := sevenPoly_reduces73 hq
  have raw := reduces73_sub
    (reduces73_mul (reduces73_mul (reduces73_int 4) (reduces73_pow h4 2)) h7)
    (reduces73_mul (reduces73_pow h3 3)
      (reduces73_pow (reduces73_sub h5
        (reduces73_mul (reduces73_int 4) (reduces73_pow h4 2))) 2))
  apply reduces73_right (by simpa [fiveYPoly] using raw)
  ring

private lemma fiveMap_reduces73 {P : ℚ × ℚ} {x y : F73}
    (hx : Reduces73 P.1 x) (hy : Reduces73 P.2 y) (hx0 : x ≠ 0) :
    Reduces73 (fiveMap P).1 (x / 25) ∧ Reduces73 (fiveMap P).2 (y / 125) := by
  have h5 := fivePoly_reduces73 hx
  have hphi := fivePhi_reduces73 hx
  have hY := fiveYPoly_reduces73 hx
  have h5z : (5 : F73) * x ^ 12 ≠ 0 :=
    mul_ne_zero (by decide) (pow_ne_zero _ hx0)
  constructor
  · have raw := reduces73_div hphi (reduces73_pow h5 2) (pow_ne_zero _ h5z)
    apply reduces73_right (by simpa [fiveMap] using raw)
    field_simp [hx0]
    ring
  · have raw := reduces73_div (reduces73_mul hy hY) (reduces73_pow h5 3)
      (pow_ne_zero _ h5z)
    apply reduces73_right (by simpa [fiveMap] using raw)
    field_simp [hx0]
    ring

private lemma shortStart_reduces73 :
    Reduces73 shortStart.1 48 ∧ Reduces73 shortStart.2 17 := by
  constructor
  · refine ⟨21443383536, 511225, by decide, ?_, ?_⟩
    simp [shortStart, Rat.divInt_eq_div]
    field_simp [show (511225 : F73) ≠ 0 by decide] <;> decide
  · refine ⟨-2752977651830784, 365525875, by decide, ?_, ?_⟩
    simp [shortStart, Rat.divInt_eq_div]
    field_simp [show (365525875 : F73) ≠ 0 by decide] <;> decide

private def orbitX73 (n : ℕ) : F73 := 48 / 25 ^ n
private def orbitY73 (n : ℕ) : F73 := 17 / 125 ^ n

private lemma orbit_reduces73 (n : ℕ) :
    Reduces73 (orbit n).1 (orbitX73 n) ∧ Reduces73 (orbit n).2 (orbitY73 n) := by
  induction n with
  | zero => simpa [orbit, orbitX73, orbitY73] using shortStart_reduces73
  | succ n ih =>
      rw [orbit, Function.iterate_succ_apply']
      have hn := fiveMap_reduces73 ih.1 ih.2 (by
        simp only [orbitX73]
        exact div_ne_zero (by decide) (pow_ne_zero _ (by decide)))
      constructor
      · apply reduces73_right hn.1
        simp only [orbitX73, pow_succ]
        field_simp
      · apply reduces73_right hn.2
        simp only [orbitY73, pow_succ]
        field_simp

private lemma orbit_sample_reduces73 (k : ℕ) :
    Reduces73 (orbit (57 + 72 * k)).1 57 ∧
      Reduces73 (orbit (57 + 72 * k)).2 49 := by
  have h := orbit_reduces73 (57 + 72 * k)
  have h25 : (25 : F73) ^ 72 = 1 := by decide
  have h125 : (125 : F73) ^ 72 = 1 := by decide
  constructor
  · apply reduces73_right h.1
    simp only [orbitX73, pow_add, pow_mul, h25, one_pow, mul_one]
    field_simp [show (25 : F73) ≠ 0 by decide] <;> decide
  · apply reduces73_right h.2
    simp only [orbitY73, pow_add, pow_mul, h125, one_pow, mul_one]
    field_simp [show (125 : F73) ≠ 0 by decide] <;> decide

lemma orbit_sample_old_ratio_reduces73 (k : ℕ) :
    Reduces73 (bbcX (orbit (57 + 72 * k)) / bbcY (orbit (57 + 72 * k))) 2 := by
  have h := orbit_sample_reduces73 k
  have hXraw := reduces73_div
    (reduces73_sub h.1 (reduces73_int 17808)) (reduces73_int 36) (by decide)
  have hX : Reduces73 (bbcX (orbit (57 + 72 * k))) 24 := by
    apply reduces73_right (by simpa [bbcX] using hXraw)
    field_simp [show (36 : F73) ≠ 0 by decide] <;> decide
  have hYraw := reduces73_div
    (reduces73_add
      (reduces73_add
        (reduces73_div h.2 (reduces73_int 108) (by decide))
        (reduces73_mul (reduces73_int 128) hX))
      (reduces73_int 3360))
    (reduces73_int 2) (by decide)
  have hY : Reduces73 (bbcY (orbit (57 + 72 * k))) 12 := by
    apply reduces73_right (by simpa [bbcY] using hYraw)
    field_simp [show (108 : F73) ≠ 0 by decide,
      show (2 : F73) ≠ 0 by decide] <;> decide
  have hr := reduces73_div hX hY (by decide)
  apply reduces73_right hr
  field_simp [show (12 : F73) ≠ 0 by decide] <;> decide

private lemma quarticX_num_congr_5329 {P : ℚ × ℚ}
    (h : Reduces73 (bbcX P / bbcY P) 2) :
    (5329 : ℤ) ∣ (quarticX P).num - 290 * ((quarticX P).den : ℤ) := by
  rcases h with ⟨u, v, hv, hr, hred⟩
  have hv0 : v ≠ 0 := by intro h; subst v; simp at hv
  have huv73 : (u : F73) = 2 * (v : F73) := by
    have huv := (div_eq_iff hv).mp hred.symm
    simpa [mul_comm] using huv
  have h73 : (73 : ℤ) ∣ u - 2 * v := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (u - 2 * v) 73).mp
    push_cast
    rw [huv73]
    ring
  obtain ⟨s, hs⟩ := h73
  let q := quarticX P
  have hformula : q = ((146 * u - 2 * v : ℤ) : ℚ) / (v : ℚ) := by
    dsimp [q]
    calc
      quarticX P = 146 * (bbcX P / bbcY P) - 2 := by
        simp only [quarticX]
        ring
      _ = 146 * ((u : ℚ) / (v : ℚ)) - 2 := by rw [hr]
      _ = ((146 * u - 2 * v : ℤ) : ℚ) / (v : ℚ) := by
        push_cast
        field_simp [hv0]
  have heqQ :
      (q.num : ℚ) / (q.den : ℚ) =
        ((146 * u - 2 * v : ℤ) : ℚ) / (v : ℚ) := by
    rw [q.num_div_den, hformula]
  have hcross : q.num * v = (146 * u - 2 * v) * (q.den : ℤ) := by
    field_simp [hv0, q.den_nz] at heqQ
    have hi : q.num * v = (q.den : ℤ) * (146 * u - 2 * v) := by
      exact_mod_cast heqQ
    simpa [mul_comm] using hi
  have hprodEq :
      (q.num - 290 * (q.den : ℤ)) * v =
        (73 : ℤ) ^ 2 * (2 * s * (q.den : ℤ)) := by
    calc
      (q.num - 290 * (q.den : ℤ)) * v =
          q.num * v - 290 * (q.den : ℤ) * v := by ring
      _ = (146 * u - 2 * v) * (q.den : ℤ) -
          290 * (q.den : ℤ) * v := by rw [hcross]
      _ = 146 * (u - 2 * v) * (q.den : ℤ) := by ring
      _ = (73 : ℤ) ^ 2 * (2 * s * (q.den : ℤ)) := by rw [hs]; ring
  have hprod : (73 : ℤ) ^ 2 ∣ (q.num - 290 * (q.den : ℤ)) * v :=
    ⟨2 * s * (q.den : ℤ), hprodEq⟩
  have hnot : ¬(73 : ℤ) ∣ v := by
    intro hd
    apply hv
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd v 73).2 hd
  have hnotNat : ¬73 ∣ v.natAbs := by
    intro hd
    exact hnot (Int.natCast_dvd.mpr hd)
  have hcopNat : Nat.Coprime (73 ^ 2) v.natAbs :=
    ((show Nat.Prime 73 by decide).coprime_iff_not_dvd.mpr hnotNat).pow_left _
  have hcop : IsCoprime ((73 : ℤ) ^ 2) v := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa using hcopNat
  change (73 : ℤ) ^ 2 ∣ q.num - 290 * (q.den : ℤ)
  exact hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using hprod)

lemma orbit_sample_quartic_num_congr_5329 (k : ℕ) :
    (5329 : ℤ) ∣ (quarticX (orbit (57 + 72 * k))).num -
      290 * ((quarticX (orbit (57 + 72 * k))).den : ℤ) :=
  quarticX_num_congr_5329 (orbit_sample_old_ratio_reduces73 k)

/-! ## Primitive integral points on the quartic -/

private lemma quartic_dvd_5329 {a b : ℤ}
    (h : (5329 : ℤ) ∣ a - 290 * b) : (5329 : ℤ) ∣ quartic a b := by
  obtain ⟨t, ht⟩ := h
  have ha : a = 290 * b + 5329 * t := by omega
  refine ⟨1290649 * b ^ 4 + 95538768 * b ^ 3 * t +
      2651934218 * b ^ 2 * t ^ 2 + 32714773632 * b * t ^ 3 +
      151334226289 * t ^ 4, ?_⟩
  rw [ha]
  simp only [quartic]
  ring

private lemma rat_eq_int_of_sq_eq_int {r : ℚ} {n : ℤ}
    (h : r ^ 2 = (n : ℚ)) : ∃ c : ℤ, r = (c : ℚ) := by
  have hd := congrArg Rat.den h
  simp only [Rat.den_pow, Rat.den_intCast] at hd
  have hd1 : r.den = 1 := by nlinarith [r.den_pos]
  refine ⟨r.num, ?_⟩
  rw [← r.num_div_den]
  simp [hd1]

/-- Each selected orbit point yields a primitive integral quartic solution with the required
extra factor `73²` in its square coordinate. -/
lemma orbit_sample_primitive_solution (k : ℕ) :
    ∃ a b c : ℤ,
      0 < b ∧ Nat.Coprime a.natAbs b.natAbs ∧
      quartic a b = (73 : ℤ) ^ 3 * c ^ 2 ∧
      quarticX (orbit (57 + 72 * k)) = (a : ℚ) / (b : ℚ) := by
  let P := orbit (57 + 72 * k)
  let q := quarticX P
  let a : ℤ := q.num
  let b : ℤ := q.den
  have hb : 0 < b := by simpa [b] using q.den_pos
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hcop : Nat.Coprime a.natAbs b.natAbs := by
    simpa [a, b] using q.reduced
  have hq : q = (a : ℚ) / (b : ℚ) := by
    simpa [a, b] using q.num_div_den.symm
  have he := BBC_to_quartic (orbit_onCurve (57 + 72 * k))
    (orbit_bbcY_ne_zero (57 + 72 * k))
  change q ^ 4 - 8 * q ^ 3 + 2 * q ^ 2 + 8 * q + 1 =
    73 * quarticY P ^ 2 at he
  rw [hq] at he
  have hhom :
      ((quartic a b : ℤ) : ℚ) =
        73 * (quarticY P * (b : ℚ) ^ 2) ^ 2 := by
    simp only [quartic]
    push_cast
    field_simp [hb0] at he
    linear_combination (norm := ring) he
  have hcon : (5329 : ℤ) ∣ a - 290 * b := by
    simpa [P, q, a, b] using orbit_sample_quartic_num_congr_5329 k
  have hdiv := quartic_dvd_5329 hcon
  obtain ⟨m, hm⟩ := hdiv
  have hrsq :
      (quarticY P * (b : ℚ) ^ 2) ^ 2 = ((73 * m : ℤ) : ℚ) := by
    rw [hm] at hhom
    push_cast at hhom ⊢
    ring_nf at hhom ⊢
    linarith
  obtain ⟨c, hc⟩ := rat_eq_int_of_sq_eq_int hrsq
  have hFc : quartic a b = (73 : ℤ) * c ^ 2 := by
    rw [hc] at hhom
    exact_mod_cast hhom
  obtain ⟨m', hm'⟩ := quartic_dvd_5329 hcon
  have hc2 : (73 : ℤ) ∣ c ^ 2 := by
    refine ⟨m', ?_⟩
    have hcancel : (73 : ℤ) * c ^ 2 = (73 : ℤ) * (73 * m') := by
      rw [← hFc, hm']
      ring
    exact mul_left_cancel₀ (by norm_num : (73 : ℤ) ≠ 0) hcancel
  have hcdiv : (73 : ℤ) ∣ c :=
    (show _root_.Prime (73 : ℤ) by decide).dvd_of_dvd_pow hc2
  obtain ⟨c', rfl⟩ := hcdiv
  refine ⟨a, b, c', hb, hcop, ?_, ?_⟩
  · rw [hFc]
    ring
  · simpa [P, q] using hq

/-! ## Parity normalization -/

/-- The two parameters have opposite parity.  Writing this as oddness of their sum is
particularly convenient for all three square roots below. -/
def OppositeParity (a b : ℤ) : Prop := Odd (a + b)

/-- A primitive quartic solution can be normalized to opposite parity.  If its two
parameters are odd, the half-sum/half-difference substitution divides the square
coordinate by two and preserves the required `73³` signature. -/
lemma orbit_sample_normalized_solution (k : ℕ) :
    ∃ a b c : ℤ,
      Nat.Coprime a.natAbs b.natAbs ∧ OppositeParity a b ∧
      quartic a b = (73 : ℤ) ^ 3 * c ^ 2 ∧
      (quarticX (orbit (57 + 72 * k)) = (a : ℚ) / (b : ℚ) ∨
        quarticX (orbit (57 + 72 * k)) =
          ((a + b : ℤ) : ℚ) / ((a - b : ℤ) : ℚ)) := by
  obtain ⟨a, b, c, hb, hab, hF, hq⟩ := orbit_sample_primitive_solution k
  have habZ : IsCoprime a b := Int.isCoprime_iff_nat_coprime.mpr hab
  rcases Int.even_or_odd a with ha | ha
  · rcases Int.even_or_odd b with hb' | hb'
    · have hu : IsUnit (2 : ℤ) := habZ.isUnit_of_dvd' ha.two_dvd hb'.two_dvd
      exfalso
      have hdiv : (2 : ℤ) ∣ 1 := IsUnit.dvd hu
      norm_num at hdiv
    · exact ⟨a, b, c, hab, ha.add_odd hb', hF, Or.inl hq⟩
  · rcases Int.even_or_odd b with hb' | hb'
    · exact ⟨a, b, c, hab, ha.add_even hb', hF, Or.inl hq⟩
    · obtain ⟨u, hu⟩ := (ha.add_odd hb').two_dvd
      obtain ⟨v, hv⟩ := (ha.sub_odd hb').two_dvd
      have hau : a = u + v := by omega
      have hbv : b = u - v := by omega
      have huvCoprime : Nat.Coprime u.natAbs v.natAbs := by
        apply Int.isCoprime_iff_nat_coprime.mp
        rcases habZ with ⟨r, s, hrs⟩
        refine ⟨r + s, r - s, ?_⟩
        rw [hau, hbv] at hrs
        linear_combination hrs
      have huvParity : OppositeParity u v := by
        rw [OppositeParity, ← hau]
        exact ha
      have hfour : 4 * quartic u v = (73 : ℤ) ^ 3 * c ^ 2 := by
        rw [← hF, hau, hbv]
        simp only [quartic]
        ring
      have htwo : (2 : ℤ) ∣ (73 : ℤ) ^ 3 * c ^ 2 := by
        rw [← hfour]
        exact ⟨2 * quartic u v, by ring⟩
      have hcSq : (2 : ℤ) ∣ c ^ 2 := by
        rcases (show _root_.Prime (2 : ℤ) by decide).dvd_mul.mp htwo with h73 | hc
        · have : (2 : ℤ) ∣ 73 :=
            (show _root_.Prime (2 : ℤ) by decide).dvd_of_dvd_pow h73
          norm_num at this
        · exact hc
      have hc : (2 : ℤ) ∣ c :=
        (show _root_.Prime (2 : ℤ) by decide).dvd_of_dvd_pow hcSq
      obtain ⟨c', rfl⟩ := hc
      have hnormalized : quartic u v = (73 : ℤ) ^ 3 * c' ^ 2 := by
        apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
        rw [hfour]
        ring
      refine ⟨u, v, c', huvCoprime, huvParity, hnormalized, Or.inr ?_⟩
      simpa [hau, hbv] using hq

/-! ## Resultant certificates for pairwise coprimality -/

private lemma odd_apX {a b : ℤ} (h : OppositeParity a b) : Odd (apX a b) := by
  rcases h with ⟨k, hk⟩
  refine ⟨2 * k ^ 2 + 2 * k - b ^ 2, ?_⟩
  have ha : a = 2 * k + 1 - b := by linarith
  rw [ha]
  simp only [apX]
  ring

private lemma odd_apY {a b : ℤ} (h : OppositeParity a b) : Odd (apY a b) := by
  rcases h with ⟨k, hk⟩
  refine ⟨2 * k ^ 2 + 2 * k - a * b, ?_⟩
  have ha : a = 2 * k + 1 - b := by linarith
  rw [ha]
  simp only [apY]
  ring

private lemma odd_apZ {a b : ℤ} (h : OppositeParity a b) : Odd (apZ a b) := by
  rcases h with ⟨k, hk⟩
  refine ⟨2 * k ^ 2 + 2 * k - 2 * a * b - b ^ 2, ?_⟩
  have ha : a = 2 * k + 1 - b := by linarith
  rw [ha]
  simp only [apZ]
  ring

/-- A homogeneous resultant identity proves coprimality once the first form is coprime
to the resultant constant and to the second parameter. -/
private lemma coprime_of_resultant {a b r s C U V t : ℤ} {n : ℕ}
    (hab : Nat.Coprime a.natAbs b.natAbs)
    (hrepr : r = a ^ 2 + b * t) (hC : IsCoprime r C)
    (hid : U * r + V * s = C * b ^ n) : Nat.Coprime r.natAbs s.natAbs := by
  have habZ : IsCoprime a b := Int.isCoprime_iff_nat_coprime.mpr hab
  have hrb : IsCoprime r b := by
    rw [hrepr]
    exact (habZ.pow_left).add_mul_left_left t
  have hrprod : IsCoprime r (C * b ^ n) := hC.mul_right hrb.pow_right
  have hcomb : IsCoprime r (U * r + V * s) := by rw [hid]; exact hrprod
  have hcomb' : IsCoprime r (V * s + U * r) := by simpa [add_comm] using hcomb
  have hVs : IsCoprime r (V * s) := IsCoprime.of_add_mul_right_right hcomb'
  exact Int.isCoprime_iff_nat_coprime.mp hVs.of_mul_right_right

private lemma coprime_apX_apY {a b : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) (hpar : OppositeParity a b) :
    Nat.Coprime (apX a b).natAbs (apY a b).natAbs := by
  have h2 : IsCoprime (apX a b) (2 : ℤ) := Int.isCoprime_two_right.mpr (odd_apX hpar)
  have h4 : IsCoprime (apX a b) (4 : ℤ) := by
    have hp : IsCoprime (apX a b) ((2 : ℤ) ^ 2) := h2.pow_right
    norm_num at hp ⊢
    exact hp
  apply coprime_of_resultant hab (t := 2 * a - b) (C := 4) (n := 3)
    (U := -a - b) (V := a + 3 * b)
  · simp only [apX]
    ring
  · exact h4
  · simp only [apX, apY]
    ring

private lemma coprime_pow_two_of_odd {r : ℤ} (hr : Odd r) (n : ℕ) :
    IsCoprime r ((2 : ℤ) ^ n) :=
  (Int.isCoprime_two_right.mpr hr).pow_right

private lemma coprime_apX_apZ {a b : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) (hpar : OppositeParity a b) :
    Nat.Coprime (apX a b).natAbs (apZ a b).natAbs := by
  have h4 : IsCoprime (apX a b) (4 : ℤ) := by
    simpa using coprime_pow_two_of_odd (odd_apX hpar) 2
  apply coprime_of_resultant hab (t := 2 * a - b) (C := 4) (n := 3)
    (U := a - 2 * b) (V := -a - 2 * b)
  · simp only [apX]
    ring
  · exact h4
  · simp only [apX, apZ]
    ring

private lemma coprime_apY_apZ {a b : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) (hpar : OppositeParity a b) :
    Nat.Coprime (apY a b).natAbs (apZ a b).natAbs := by
  have h4 : IsCoprime (apY a b) (4 : ℤ) := by
    simpa using coprime_pow_two_of_odd (odd_apY hpar) 2
  apply coprime_of_resultant hab (t := b) (C := 4) (n := 3)
    (U := 3 * b - a) (V := a - b)
  · simp only [apY]
    ring
  · exact h4
  · simp only [apY, apZ]
    ring

private abbrev F3 := ZMod 3

private lemma zmod3_apX_zero :
    ∀ x y : F3, x ^ 2 - y ^ 2 + 2 * x * y = 0 → x = 0 ∧ y = 0 := by
  decide

private lemma coprime_apX_three {a b : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) : IsCoprime (apX a b) (3 : ℤ) := by
  have habZ : IsCoprime a b := Int.isCoprime_iff_nat_coprime.mpr hab
  have hnot : ¬(3 : ℤ) ∣ apX a b := by
    intro hd
    have hz : (apX a b : F3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (apX a b) 3).2 hd
    have hz' : (a : F3) ^ 2 - (b : F3) ^ 2 + 2 * (a : F3) * (b : F3) = 0 := by
      simpa [apX] using hz
    have hzero := zmod3_apX_zero (a : F3) (b : F3) hz'
    have hda : (3 : ℤ) ∣ a :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).1 hzero.1
    have hdb : (3 : ℤ) ∣ b :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).1 hzero.2
    have hu : IsUnit (3 : ℤ) := habZ.isUnit_of_dvd' hda hdb
    have hdiv : (3 : ℤ) ∣ 1 := IsUnit.dvd hu
    norm_num at hdiv
  have hnotNat : ¬3 ∣ (apX a b).natAbs := by
    intro hd
    exact hnot (Int.natCast_dvd.mpr hd)
  have hcNat : Nat.Coprime 3 (apX a b).natAbs :=
    (show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr hnotNat
  have hc : IsCoprime (3 : ℤ) (apX a b) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa using hcNat
  exact hc.symm

private lemma coprime_apX_quartic {a b : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) (hpar : OppositeParity a b) :
    Nat.Coprime (apX a b).natAbs (quartic a b).natAbs := by
  have h8 : IsCoprime (apX a b) (8 : ℤ) := by
    simpa using coprime_pow_two_of_odd (odd_apX hpar) 3
  have h3 := coprime_apX_three hab
  have h24 : IsCoprime (apX a b) (24 : ℤ) := by
    have hm : IsCoprime (apX a b) ((3 : ℤ) * 8) := h3.mul_right h8
    norm_num at hm ⊢
    exact hm
  apply coprime_of_resultant hab (t := 2 * a - b) (C := 24) (n := 5)
    (U := -2 * a ^ 3 + 15 * a ^ 2 * b + 4 * a * b ^ 2 - 19 * b ^ 3)
    (V := 2 * a + 5 * b)
  · simp only [apX]
    ring
  · exact h24
  · simp only [apX, quartic]
    ring

private lemma coprime_apY_quartic {a b : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) (hpar : OppositeParity a b) :
    Nat.Coprime (apY a b).natAbs (quartic a b).natAbs := by
  have h16 : IsCoprime (apY a b) (16 : ℤ) := by
    simpa using coprime_pow_two_of_odd (odd_apY hpar) 4
  apply coprime_of_resultant hab (t := b) (C := 16) (n := 5)
    (U := a ^ 3 - 8 * a ^ 2 * b + a * b ^ 2 + 16 * b ^ 3) (V := -a)
  · simp only [apY]
    ring
  · exact h16
  · simp only [apY, quartic]
    ring

private lemma coprime_apZ_quartic {a b : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) (hpar : OppositeParity a b) :
    Nat.Coprime (apZ a b).natAbs (quartic a b).natAbs := by
  have h8 : IsCoprime (apZ a b) (8 : ℤ) := by
    simpa using coprime_pow_two_of_odd (odd_apZ hpar) 3
  apply coprime_of_resultant hab (t := -2 * a - b) (C := 8) (n := 5)
    (U := -2 * a ^ 3 + 17 * a ^ 2 * b - 12 * a * b ^ 2 - 13 * b ^ 3)
    (V := 2 * a - 5 * b)
  · simp only [apZ]
    ring
  · exact h8
  · simp only [apZ, quartic]
    ring

/-! ## The natural-number progression -/

private def squareNat (z : ℤ) : ℕ := z.natAbs ^ 2
private def fourthNat (a b : ℤ) : ℕ := (quartic a b).natAbs
private def apStep (a b : ℤ) : ℕ := (4 * apDelta a b).natAbs

/-- Reverse the progression exactly when its displayed integer common difference is
negative. -/
private def apProgression (p : ℤ × ℤ) : ℕ × ℕ :=
  if 0 ≤ apDelta p.1 p.2 then
    (squareNat (apX p.1 p.2), apStep p.1 p.2)
  else
    (fourthNat p.1 p.2, apStep p.1 p.2)

private lemma coe_squareNat (z : ℤ) : ((squareNat z : ℕ) : ℤ) = z ^ 2 := by
  simp [squareNat]

private lemma coe_apStep_of_nonneg {a b : ℤ} (h : 0 ≤ apDelta a b) :
    ((apStep a b : ℕ) : ℤ) = 4 * apDelta a b := by
  simp only [apStep, Int.natCast_natAbs]
  rw [abs_of_nonneg]
  exact mul_nonneg (by norm_num) h

private lemma coe_apStep_of_neg {a b : ℤ} (h : apDelta a b < 0) :
    ((apStep a b : ℕ) : ℤ) = -(4 * apDelta a b) := by
  simp only [apStep, Int.natCast_natAbs]
  rw [abs_of_neg]
  exact mul_neg_of_pos_of_neg (by norm_num) h

private lemma one_ne_73_cube_mul_sq (c : ℤ) :
    (1 : ℤ) ≠ (73 : ℤ) ^ 3 * c ^ 2 := by
  intro h
  have hd : (73 : ℤ) ∣ 1 := ⟨(73 : ℤ) ^ 2 * c ^ 2, by rw [h]; ring⟩
  norm_num at hd

private lemma apDelta_ne_zero {a b c : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) (hpar : OppositeParity a b)
    (hF : quartic a b = (73 : ℤ) ^ 3 * c ^ 2) : apDelta a b ≠ 0 := by
  intro hd
  have hprod : a * b = 0 ∨ b ^ 2 - a ^ 2 = 0 := by
    simpa [apDelta] using (mul_eq_zero.mp hd)
  rcases hprod with hab0 | hs
  · rcases mul_eq_zero.mp hab0 with ha | hb
    · subst a
      have hbabs : b.natAbs = 1 := by simpa using hab
      rcases Int.natAbs_eq_iff.mp hbabs with rfl | rfl <;>
        exact one_ne_73_cube_mul_sq c (by simpa [quartic] using hF)
    · subst b
      have haabs : a.natAbs = 1 := by simpa using hab
      rcases Int.natAbs_eq_iff.mp haabs with rfl | rfl <;>
        exact one_ne_73_cube_mul_sq c (by simpa [quartic] using hF)
  · have hfac : (b - a) * (b + a) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfac with hba | hba
    · have : b = a := by linarith
      subst b
      rcases hpar with ⟨k, hk⟩
      omega
    · have : b = -a := by linarith
      subst b
      rcases hpar with ⟨k, hk⟩
      omega

private lemma forward_progression_values {a b c : ℤ}
    (hD : 0 ≤ apDelta a b)
    (hF : quartic a b = (73 : ℤ) ^ 3 * c ^ 2) :
    squareNat (apY a b) = squareNat (apX a b) + apStep a b ∧
    squareNat (apZ a b) = squareNat (apX a b) + 2 * apStep a b ∧
    fourthNat a b = squareNat (apX a b) + 3 * apStep a b := by
  have hFn : 0 ≤ quartic a b := by rw [hF]; positivity
  have hs := coe_apStep_of_nonneg hD
  constructor
  · apply Int.ofNat_inj.mp
    push_cast
    rw [coe_squareNat, coe_squareNat, hs]
    linear_combination apY_sq_sub_apX_sq a b
  constructor
  · apply Int.ofNat_inj.mp
    push_cast
    rw [coe_squareNat, coe_squareNat, hs]
    linear_combination (apY_sq_sub_apX_sq a b) + (apZ_sq_sub_apY_sq a b)
  · apply Int.ofNat_inj.mp
    push_cast
    rw [coe_squareNat, hs]
    simp only [fourthNat, Int.natCast_natAbs, abs_of_nonneg hFn]
    linear_combination (apY_sq_sub_apX_sq a b) +
      (apZ_sq_sub_apY_sq a b) + (quartic_sub_apZ_sq a b)

private lemma reverse_progression_values {a b c : ℤ}
    (hD : apDelta a b < 0)
    (hF : quartic a b = (73 : ℤ) ^ 3 * c ^ 2) :
    squareNat (apZ a b) = fourthNat a b + apStep a b ∧
    squareNat (apY a b) = fourthNat a b + 2 * apStep a b ∧
    squareNat (apX a b) = fourthNat a b + 3 * apStep a b := by
  have hFn : 0 ≤ quartic a b := by rw [hF]; positivity
  have hs := coe_apStep_of_neg hD
  constructor
  · apply Int.ofNat_inj.mp
    push_cast
    rw [coe_squareNat, hs]
    simp only [fourthNat, Int.natCast_natAbs, abs_of_nonneg hFn]
    linear_combination -(quartic_sub_apZ_sq a b)
  constructor
  · apply Int.ofNat_inj.mp
    push_cast
    rw [coe_squareNat, hs]
    simp only [fourthNat, Int.natCast_natAbs, abs_of_nonneg hFn]
    linear_combination -(quartic_sub_apZ_sq a b) - (apZ_sq_sub_apY_sq a b)
  · apply Int.ofNat_inj.mp
    push_cast
    rw [coe_squareNat, hs]
    simp only [fourthNat, Int.natCast_natAbs, abs_of_nonneg hFn]
    linear_combination -(quartic_sub_apZ_sq a b) - (apZ_sq_sub_apY_sq a b) -
      (apY_sq_sub_apX_sq a b)

private lemma powerful_sq (n : ℕ) : Nat.Powerful (n ^ 2) := by
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have pd := Nat.dvd_of_mem_primeFactors hp
  have pn : p ∣ n := pp.dvd_of_dvd_pow pd
  exact pow_dvd_pow_of_dvd pn 2

private lemma powerful_cube (n : ℕ) : Nat.Powerful (n ^ 3) := by
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have pd := Nat.dvd_of_mem_primeFactors hp
  have pn : p ∣ n := pp.dvd_of_dvd_pow pd
  obtain ⟨d, rfl⟩ := pn
  refine ⟨d ^ 3 * p, ?_⟩
  ring

private lemma powerful_mul {m n : ℕ} (hm : Nat.Powerful m) (hn : Nat.Powerful n) :
    Nat.Powerful (m * n) := by
  intro p hp
  rcases Nat.mem_primeFactors.mp hp with ⟨pp, pd, hmn⟩
  have hm0 : m ≠ 0 := by intro h; subst m; simp at hmn
  have hn0 : n ≠ 0 := by intro h; subst n; simp at hmn
  rcases pp.dvd_mul.mp pd with hpm | hpn
  · exact dvd_mul_of_dvd_left (hm p (pp.mem_primeFactors hpm hm0)) n
  · exact dvd_mul_of_dvd_right (hn p (pp.mem_primeFactors hpn hn0)) m

private lemma goodParam_mem {a b c : ℤ}
    (hab : Nat.Coprime a.natAbs b.natAbs) (hpar : OppositeParity a b)
    (hF : quartic a b = (73 : ℤ) ^ 3 * c ^ 2) :
    IsCoprimePowerfulAP4 (apProgression (a, b)).1 (apProgression (a, b)).2 := by
  have hdelta := apDelta_ne_zero hab hpar hF
  have hdpos : 0 < apStep a b := by
    exact Int.natAbs_pos.mpr (mul_ne_zero (by norm_num) hdelta)
  have pX : Nat.Powerful (squareNat (apX a b)) := powerful_sq _
  have pY : Nat.Powerful (squareNat (apY a b)) := powerful_sq _
  have pZ : Nat.Powerful (squareNat (apZ a b)) := powerful_sq _
  have hfourth : fourthNat a b = 73 ^ 3 * c.natAbs ^ 2 := by
    simp [fourthNat, hF, Int.natAbs_mul, Int.natAbs_pow]
  have pF : Nat.Powerful (fourthNat a b) := by
    rw [hfourth]
    exact powerful_mul (powerful_cube 73) (powerful_sq c.natAbs)
  have hXY : Nat.Coprime (squareNat (apX a b)) (squareNat (apY a b)) := by
    simpa [squareNat] using (coprime_apX_apY hab hpar).pow 2 2
  have hXZ : Nat.Coprime (squareNat (apX a b)) (squareNat (apZ a b)) := by
    simpa [squareNat] using (coprime_apX_apZ hab hpar).pow 2 2
  have hYZ : Nat.Coprime (squareNat (apY a b)) (squareNat (apZ a b)) := by
    simpa [squareNat] using (coprime_apY_apZ hab hpar).pow 2 2
  have hXF : Nat.Coprime (squareNat (apX a b)) (fourthNat a b) := by
    simpa [squareNat, fourthNat] using (coprime_apX_quartic hab hpar).pow_left 2
  have hYF : Nat.Coprime (squareNat (apY a b)) (fourthNat a b) := by
    simpa [squareNat, fourthNat] using (coprime_apY_quartic hab hpar).pow_left 2
  have hZF : Nat.Coprime (squareNat (apZ a b)) (fourthNat a b) := by
    simpa [squareNat, fourthNat] using (coprime_apZ_quartic hab hpar).pow_left 2
  by_cases hD : 0 ≤ apDelta a b
  · have hv := forward_progression_values hD hF
    rw [show apProgression (a, b) =
      (squareNat (apX a b), apStep a b) by simp [apProgression, hD]]
    simp only [Prod.fst, Prod.snd]
    unfold IsCoprimePowerfulAP4
    rw [← hv.1, ← hv.2.1, ← hv.2.2]
    exact ⟨hdpos, pX, pY, pZ, pF, hXY, hXZ, hXF, hYZ, hYF, hZF⟩
  · have hD' : apDelta a b < 0 := lt_of_not_ge hD
    have hv := reverse_progression_values hD' hF
    rw [show apProgression (a, b) =
      (fourthNat a b, apStep a b) by simp [apProgression, hD]]
    simp only [Prod.fst, Prod.snd]
    unfold IsCoprimePowerfulAP4
    rw [← hv.1, ← hv.2.1, ← hv.2.2]
    exact ⟨hdpos, pF, pZ, pY, pX, hZF.symm, hYF.symm, hXF.symm,
      hYZ.symm, hXZ.symm, hXY.symm⟩

/-! ## Infinitely many parameters -/

private structure GoodParam (k : ℕ) where
  a : ℤ
  b : ℤ
  c : ℤ
  coprime : Nat.Coprime a.natAbs b.natAbs
  parity : OppositeParity a b
  signature : quartic a b = (73 : ℤ) ^ 3 * c ^ 2
  source :
    quarticX (orbit (57 + 72 * k)) = (a : ℚ) / (b : ℚ) ∨
    quarticX (orbit (57 + 72 * k)) =
      ((a + b : ℤ) : ℚ) / ((a - b : ℤ) : ℚ)

private noncomputable def goodParam (k : ℕ) : GoodParam k := by
  classical
  choose a b c hab hpar hF hsource using orbit_sample_normalized_solution k
  exact ⟨a, b, c, hab, hpar, hF, hsource⟩

private noncomputable def paramPair (k : ℕ) : ℤ × ℤ :=
  ((goodParam k).a, (goodParam k).b)

private lemma sampleQ_injective :
    Function.Injective (fun k : ℕ ↦ quarticX (orbit (57 + 72 * k))) := by
  intro k l h
  have hi := quarticX_orbit_injective h
  omega

private lemma paramPair_range_infinite : (Set.range paramPair).Infinite := by
  classical
  have hqinf :
      (Set.range (fun k : ℕ ↦ quarticX (orbit (57 + 72 * k)))).Infinite :=
    Set.infinite_range_of_injective sampleQ_injective
  intro hfinite
  apply hqinf
  let f₁ : ℤ × ℤ → ℚ := fun p ↦ (p.1 : ℚ) / (p.2 : ℚ)
  let f₂ : ℤ × ℤ → ℚ := fun p ↦
    ((p.1 + p.2 : ℤ) : ℚ) / ((p.1 - p.2 : ℤ) : ℚ)
  refine ((hfinite.image f₁).union (hfinite.image f₂)).subset ?_
  rintro q ⟨k, rfl⟩
  rcases (goodParam k).source with h | h
  · apply Set.mem_union_left
    refine ⟨paramPair k, ⟨k, rfl⟩, ?_⟩
    simpa [f₁, paramPair] using h.symm
  · apply Set.mem_union_right
    refine ⟨paramPair k, ⟨k, rfl⟩, ?_⟩
    simpa [f₂, paramPair] using h.symm

private lemma apY_natAbs (a b : ℤ) :
    (apY a b).natAbs = a.natAbs ^ 2 + b.natAbs ^ 2 := by
  apply Int.ofNat_inj.mp
  push_cast
  have hY : 0 ≤ apY a b := by
    simp only [apY]
    positivity
  rw [abs_of_nonneg hY]
  simp only [apY]
  rw [sq_abs, sq_abs]

private lemma progression_fiber_finite (x : ℕ × ℕ) :
    (Set.range paramPair ∩ apProgression ⁻¹' {x}).Finite := by
  classical
  let M : ℕ := x.1 + 3 * x.2
  let box : Set (ℤ × ℤ) :=
    Set.Icc (-(M : ℤ)) (M : ℤ) ×ˢ Set.Icc (-(M : ℤ)) (M : ℤ)
  have hbox : box.Finite := by
    dsimp [box]
    exact (Set.finite_Icc (-(M : ℤ)) (M : ℤ)).prod
      (Set.finite_Icc (-(M : ℤ)) (M : ℤ))
  apply hbox.subset
  rintro p ⟨⟨k, rfl⟩, hp⟩
  let a := (goodParam k).a
  let b := (goodParam k).b
  have hpair : paramPair k = (a, b) := by rfl
  have hprog : apProgression (a, b) = x := by
    simpa [hpair] using (show apProgression (paramPair k) ∈ ({x} : Set (ℕ × ℕ)) from hp)
  have hF : quartic a b = (73 : ℤ) ^ 3 * (goodParam k).c ^ 2 := by
    simpa [a, b] using (goodParam k).signature
  have hyBound : squareNat (apY a b) ≤ M := by
    by_cases hD : 0 ≤ apDelta a b
    · have hv := forward_progression_values hD hF
      have hx1 : x.1 = squareNat (apX a b) := by
        rw [← hprog]
        simp [apProgression, hD]
      have hx2 : x.2 = apStep a b := by
        rw [← hprog]
        simp [apProgression, hD]
      dsimp [M]
      omega
    · have hD' : apDelta a b < 0 := lt_of_not_ge hD
      have hv := reverse_progression_values hD' hF
      have hx1 : x.1 = fourthNat a b := by
        rw [← hprog]
        simp [apProgression, hD]
      have hx2 : x.2 = apStep a b := by
        rw [← hprog]
        simp [apProgression, hD]
      dsimp [M]
      omega
  have haYabs : a.natAbs ≤ (apY a b).natAbs := by
    rw [apY_natAbs]
    exact le_trans (Nat.le_mul_self a.natAbs) (by
      simpa [pow_two] using Nat.le_add_right (a.natAbs ^ 2) (b.natAbs ^ 2))
  have hbYabs : b.natAbs ≤ (apY a b).natAbs := by
    rw [apY_natAbs]
    exact le_trans (Nat.le_mul_self b.natAbs) (by
      simpa [pow_two] using Nat.le_add_left (b.natAbs ^ 2) (a.natAbs ^ 2))
  have hYsq : (apY a b).natAbs ≤ squareNat (apY a b) := by
    simpa [squareNat, pow_two] using Nat.le_mul_self (apY a b).natAbs
  have haM : a.natAbs ≤ M := haYabs.trans (hYsq.trans hyBound)
  have hbM : b.natAbs ≤ M := hbYabs.trans (hYsq.trans hyBound)
  have haCast : (a.natAbs : ℤ) ≤ (M : ℤ) := by exact_mod_cast haM
  have hbCast : (b.natAbs : ℤ) ≤ (M : ℤ) := by exact_mod_cast hbM
  have haAbs : |a| ≤ (M : ℤ) := by simpa only [Int.natCast_natAbs] using haCast
  have hbAbs : |b| ≤ (M : ℤ) := by simpa only [Int.natCast_natAbs] using hbCast
  rw [hpair]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (neg_le_neg haAbs).trans (neg_abs_le a)
  · exact (le_abs_self a).trans haAbs
  · exact (neg_le_neg hbAbs).trans (neg_abs_le b)
  · exact (le_abs_self b).trans hbAbs

private lemma coprime_powerful_progressions_infinite :
    {p : ℕ × ℕ | IsCoprimePowerfulAP4 p.1 p.2}.Infinite := by
  classical
  intro htarget
  apply paramPair_range_infinite
  apply Set.Finite.of_finite_fibers apProgression
  · apply htarget.subset
    rintro y ⟨p, ⟨k, rfl⟩, rfl⟩
    change IsCoprimePowerfulAP4 (apProgression (paramPair k)).1
      (apProgression (paramPair k)).2
    simpa [paramPair] using goodParam_mem (goodParam k).coprime
      (goodParam k).parity (goodParam k).signature
  · intro x _
    exact progression_fiber_finite x

/-- Erdős Problem 937: there are infinitely many nonconstant four-term arithmetic
progressions of pairwise coprime powerful natural numbers. -/
theorem erdos_937 :
    {p : ℕ × ℕ | IsCoprimePowerfulAP4 p.1 p.2}.Infinite := by
  refine Iff.mp ?_ trivial
  constructor
  · intro _
    exact coprime_powerful_progressions_infinite
  · intro _
    trivial

end

#print axioms erdos_937
-- 'Erdos937.erdos_937' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos937
