import Mathlib

namespace Erdos1141

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

* source: <https://gist.githubusercontent.com/pitmonticone/8ea0d1cdb963b6213ac639b11d33f811/raw/98a5824d16da14313f65d77eeab5563dd874613a/Erdos237.lean>

## External inputs

1. `pollack_theorem_1_3`: Pollack's Theorem 1.3 in the literal
   `DirichletCharacter`-based form from Pollack's paper
   <https://www.ams.org/journals/proc/2017-145-07/S0002-9939-2016-13432-1/S0002-9939-2016-13432-1.pdf>.

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

Thus the only deep external input remaining is Pollack Theorem 1.3.
Mertens' third theorem (effective form) is proved unconditionally below
(formalization by T. Woett, see https://github.com/Woett/Lean-files/blob/main/MertensThird.lean).
-/

noncomputable section

/-- The analytic cutoff `m^(1/4 + ε)` appearing in Theorem 1.3. -/
def residuePrimeUpperBound (m : ℕ) (ε : ℝ) : ℝ :=
  Real.rpow (m : ℝ) ((1 / 4 : ℝ) + ε)

/--
The finite set of primes `ℓ` with `ℓ ≤ m^(1/4 + ε)` and `χ(ℓ) = 1`.

This definition does **not** assume `χ` is quadratic; the quadraticity hypothesis
belongs only to `theorem_1_3`, matching the statement of the paper.
-/
def residuePrimesUpTo (m : ℕ) (χ : DirichletCharacter ℂ m) (ε : ℝ) : Finset ℕ := by
  classical
  exact
    ((Finset.range (Nat.ceil (residuePrimeUpperBound m ε) + 1)).filter fun ℓ =>
      Nat.Prime ℓ ∧
      (ℓ : ℝ) ≤ residuePrimeUpperBound m ε ∧
      χ (ℓ : ZMod m) = (1 : ℂ))

/--
Pollack, *Bounds for the First Several Prime Character Nonresidues*, Theorem 1.3.
-/
axiom pollack_theorem_1_3
    (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ m0 : ℕ, ∀ m : ℕ,
      m > m0 →
      ∀ χ : DirichletCharacter ℂ m,
        MulChar.IsQuadratic χ →
          Real.rpow (Real.log (m : ℝ)) A ≤
            ((residuePrimesUpTo m χ ε).card : ℝ)



end

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

/-- A lightweight paper-facing formalization of “`χ` is a quadratic character modulo `m`”.

We record exactly the properties used by Pollack's theorem and by the specialization to the
Jacobi symbol `jacobiSym d`. -/
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
    simpa using (Nat.coprime_one_left_iff m).2 trivial
  rcases χ.map_coprime hcop with h1 | h1
  · exact h1
  · have : False := by
      have hmul : χ (1 * 1) = χ 1 * χ 1 := χ.map_mul (a := 1) (b := 1) hcop hcop
      have hbad : (-1 : ℤ) = 1 := by
        simpa [h1] using hmul
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
      simpa using (ZMod.natCast_zmod_val (1 : ZMod m))
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
              simpa using (ZMod.natCast_zmod_val (a * b))
            _ = ((a.val : ZMod m) * (b.val : ZMod m)) := by
              simpa using congrArg2 (· * ·)
                (ZMod.natCast_zmod_val a).symm (ZMod.natCast_zmod_val b).symm
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

/-- The associated complex Dirichlet character is quadratic in Pollack's sense. -/
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

/-! ## Mertens' third theorem (effective form)

An unconditional formalization of `1 / (3 log n) ≤ ∏_{p ≤ n} (1 - 1/p)` for `n ≥ 3`.
Replaces the dependence so `pollack_theorem_1_3` becomes the sole remaining assumption.
Formalization due to T. Woett, obtained with Aristotle (Harmonic);
see https://github.com/Woett/Lean-files/blob/main/MertensThird.lean -/

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

section MertensThird
open ArithmeticFunction

noncomputable section

/-- ψ(n) = Σ_{m=1}^{n} Λ(m), the first Chebyshev function. -/
def chebyshevPsi (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), vonMangoldt m

/-- L_n = lcm(1, 2, ..., n). -/
def lcmRange (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm _root_.id

/-- S(n) = Σ_{m=2}^{n} Λ(m)/m. -/
def sumS (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 n, vonMangoldt m / m

/-- T(n) = Σ_{m=2}^{n} Λ(m)/(m * log m). -/
def sumT (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 n, vonMangoldt m / (m * Real.log m)

/-- P(n) = ∏_{p ≤ n, p prime} (1 - 1/p). -/
def prodP (n : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

end

noncomputable section

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
            haveI := Fact.mk ( Nat.prime_of_mem_primeFactors hp ) ; rw [ Nat.factorization_def ];
            · rw [ padicValNat_choose ];
              any_goals exact Nat.lt_succ_self _;
              · norm_num [ two_mul, Nat.add_div ];
                rw [ Finset.card_filter ];
                refine' Finset.sum_congr rfl fun x hx => _;
                rw [ Nat.add_div ( pow_pos ( Nat.Prime.pos ( Nat.prime_of_mem_primeFactors hp ) ) _ ) ] ; aesop;
              · linarith;
            · exact Nat.prime_of_mem_primeFactors hp;
          rw [hpa_div_choose];
          refine' le_trans _ ( Finset.single_le_sum ( fun x hx => Nat.zero_le _ ) ( Finset.mem_Ico.mpr ⟨ Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( show m.factorization p ≠ 0 from Finsupp.mem_support_iff.mp hp ) ), Nat.lt_succ_of_le ( Nat.le_log_of_pow_le ( Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hp ) ) ( show p ^ m.factorization p ≤ 2 * r from _ ) ) ⟩ ) );
          · norm_num [ Nat.div_eq_of_lt ( show r < p ^ m.factorization p from lt_of_not_ge hpa ) ];
            exact Nat.div_pos ( by linarith [ Finset.mem_Icc.mp hm, Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) ( Nat.ordProj_dvd m p ) ] ) ( pow_pos ( Nat.pos_of_mem_primeFactors hp ) _ );
          · exact le_trans ( Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) ( Nat.ordProj_dvd _ _ ) ) ( by linarith [ Finset.mem_Icc.mp hm ] );
        exact Nat.dvd_trans ( dvd_pow_self _ ( by linarith ) ) ( Nat.ordProj_dvd _ _ );
      convert Nat.mul_dvd_mul hpa_minus_one_div hpa_div_choose using 1 ; rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hp ) ) ) ];
  -- Since every prime power in the lcm divides the product, the lcm itself must divide the product.
  have h_lcm_div : ∀ m ∈ Finset.Icc 1 (2 * r), m ∣ lcmRange r * Nat.choose (2 * r) r := by
    intro m hm
    have h_prod_div : ∏ p ∈ Nat.primeFactors m, p ^ Nat.factorization m p ∣ lcmRange r * Nat.choose (2 * r) r := by
      convert Finset.lcm_dvd fun p hp => h_div m hm p hp using 1;
      -- The least common multiple of a set of numbers is equal to their product divided by their greatest common divisor.
      have h_lcm_prod : ∀ {S : Finset ℕ} {f : ℕ → ℕ}, (∀ p ∈ S, Nat.Prime p) → (∀ p q : ℕ, p ∈ S → q ∈ S → p ≠ q → Nat.gcd (p ^ f p) (q ^ f q) = 1) → Finset.lcm S (fun p => p ^ f p) = ∏ p ∈ S, p ^ f p := by
        intros S f hprime hgcd; induction S using Finset.induction <;> simp_all +decide ;
        exact Nat.Coprime.lcm_eq_mul <| Nat.Coprime.prod_right fun p hp => hgcd _ _ ( Or.inl rfl ) ( Or.inr hp ) <| by aesop;
      rw [ h_lcm_prod ( fun p hp => Nat.prime_of_mem_primeFactors hp ) ( fun p q hp hq hpq => by simpa [ hpq ] using Nat.coprime_pow_primes _ _ ( Nat.prime_of_mem_primeFactors hp ) ( Nat.prime_of_mem_primeFactors hq ) ) ];
    rwa [ ← Nat.factorization_prod_pow_eq_self ( by linarith [ Finset.mem_Icc.mp hm ] : m ≠ 0 ) ];
  exact Finset.lcm_dvd h_lcm_div

lemma lcmRange_dvd_odd (r : ℕ) (hr : 1 ≤ r) :
    lcmRange (2 * r + 1) ∣ lcmRange (r + 1) * Nat.choose (2 * r + 1) r := by
  -- For any prime power $p^a \leq 2r+1$, we need to show that $p^a$ divides $lcmRange(r+1) * (2r+1 choose r)$.
  have h_prime_power : ∀ p a : ℕ, Nat.Prime p → p^a ≤ 2 * r + 1 → p^a ∣ lcmRange (r + 1) * Nat.choose (2 * r + 1) r := by
    intro p a hp ha
    by_cases hpa : p^a ≤ r + 1;
    · refine' dvd_mul_of_dvd_left _ _;
      exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ hp.pos, hpa ⟩ );
    · -- Since $p^a > r + 1$, we have $p^{a-1} \leq r$.
      have hpa_minus_one : p^(a-1) ≤ r := by
        rcases a <;> simp_all +decide [ pow_succ' ];
        nlinarith [ hp.two_le ];
      -- Since $p^{a-1} \leq r$, we have $p^a \mid \binom{2r+1}{r}$.
      have hpa_div_choose : p^a ∣ Nat.choose (2 * r + 1) r * p^(a-1) := by
        have hpa_div_choose : padicValNat p (Nat.choose (2 * r + 1) r) ≥ 1 := by
          haveI := Fact.mk hp; rw [ padicValNat_choose ];
          any_goals exact Nat.lt_succ_self _;
          · refine' Finset.card_pos.mpr ⟨ a, _ ⟩ ; norm_num;
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
  induction' n using Nat.strong_induction_on with n ih;
  by_cases h₂ : n ≤ 4;
  · interval_cases n <;> decide;
  · rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩;
    · -- By lcmRange_dvd_even, lcmRange(2k) | lcmRange(k) * choose(2k,k).
      have h_div : lcmRange (2 * k) ∣ lcmRange k * Nat.choose (2 * k) k := by
        exact lcmRange_dvd_even k ( by linarith );
      -- Since $\binom{2k}{k} \leq 4^k$, we have $lcmRange (2 * k) \leq lcmRange k * 4^k$.
      have h_bound : lcmRange (2 * k) ≤ lcmRange k * 4 ^ k := by
        refine' le_trans ( Nat.le_of_dvd ( Nat.mul_pos ( lcmRange_pos k ( by linarith ) ) ( Nat.choose_pos ( by linarith ) ) ) h_div ) _;
        exact Nat.mul_le_mul_left _ ( centralBinom_le_four_pow k ( by linarith ) );
      exact h_bound.trans ( by rw [ pow_mul' ] ; exact Nat.mul_le_mul_right _ ( ih k ( by linarith ) ( by linarith ) ) |> le_trans <| by ring_nf; norm_num );
    · -- By lcmRange_dvd_odd, lcmRange(2k+1) | lcmRange(k+1) * choose(2k+1,k).
      have h_div : lcmRange (2 * k + 1) ∣ lcmRange (k + 1) * Nat.choose (2 * k + 1) k := by
        convert lcmRange_dvd_odd k ( by linarith ) using 1;
      -- By choose_odd_le_four_pow, choose(2k+1,k) ≤ 4^k.
      have h_choose : Nat.choose (2 * k + 1) k ≤ 4 ^ k := by
        convert choose_odd_le_four_pow k ( by linarith ) using 1;
      refine' le_trans ( Nat.le_of_dvd _ h_div ) _;
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
      intro m hm; rw [ ← Nat.factorization_prod_pow_eq_self ( by linarith [ Finset.mem_Icc.mp hm ] : m ≠ 0 ) ] ;
      rw [ ← Finset.prod_sdiff <| show m.primeFactors ⊆ Finset.filter Nat.Prime ( Finset.range ( n + 1 ) ) from fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_trans ( Nat.le_of_mem_primeFactors hp ) <| Finset.mem_Icc.mp hm |>.2, Nat.prime_of_mem_primeFactors hp ⟩ ];
      exact dvd_mul_of_dvd_right ( Finset.prod_dvd_prod_of_dvd _ _ fun p hp => pow_dvd_pow p <| Nat.le_log_of_pow_le ( Nat.prime_of_mem_primeFactors hp |> Nat.Prime.one_lt ) <| Nat.le_trans ( Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) <| Nat.ordProj_dvd _ _ ) <| Finset.mem_Icc.mp hm |>.2 ) _;
    refine' Nat.dvd_antisymm _ _;
    · exact Finset.lcm_dvd fun x hx => h_lcmRange_def x hx;
    · -- By definition of lcmRange, we know that lcmRange n is divisible by each prime power p^k where p is prime and k is such that p^k ≤ n.
      have h_lcmRange_div : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n) ∣ lcmRange n := by
        intros p hp
        have h_div : p ^ (Nat.log p n) ≤ n := by
          exact Nat.pow_log_le_self p ( by linarith );
        exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ), h_div ⟩ );
      convert Finset.lcm_dvd h_lcmRange_div using 1;
      -- The least common multiple of a set of numbers is equal to the product of the highest powers of all primes dividing any of the numbers.
      have h_lcm_eq_prod : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Finset.lcm S (fun p => p ^ (Nat.log p n)) = ∏ p ∈ S, p ^ (Nat.log p n) := by
        intros S hS; induction S using Finset.induction <;> simp_all +decide ;
        exact Nat.Coprime.lcm_eq_mul <| Nat.Coprime.prod_right fun p hp => Nat.Coprime.pow _ _ <| hS.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 p hp ) ; aesop;
      rw [ h_lcm_eq_prod fun p hp => Finset.mem_filter.mp hp |>.2 ];
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
        refine' Finset.sum_congr rfl fun x hx => _;
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
    refine le_trans ( Finset.sum_le_sum fun m hm => by convert h_ineq m hm using 1 ; ring ) ?_;
    rw [ ← h_log_factorial, Finset.sum_add_distrib ];
    exact add_le_add ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc ( by norm_num ) le_rfl ) fun _ _ _ => mul_nonneg ( by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg ) ( Nat.cast_nonneg _ ) ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc ( by norm_num ) le_rfl ) fun _ _ _ => by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg );
  convert div_le_div_of_nonneg_right h_rewrite ( Nat.cast_nonneg n ) using 1;
  · rw [ Finset.sum_div _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ mul_div_cancel_right₀ _ ( by positivity ) ] ;
  · unfold chebyshevPsi;
    erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num

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
    convert sumS_le_basic n ( by linarith ) |> le_trans <| div_le_div_of_nonneg_right ( h_final ) ( Nat.cast_nonneg _ ) using 1 ; ring_nf;
    simpa [ show n ≠ 0 by linarith ] using by ring;
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
        refine' Summable.tsum_le_tsum _ _ _;
        · intro i; rw [ div_pow ] ; rw [ div_mul_div_comm ] ; rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring_nf <;> norm_num;
          · exact Or.inr ⟨ ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ), pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩, pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩;
          · exact Or.inr ⟨ ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ), pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩, pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩;
        · norm_num +zetaDelta at *;
          exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun k => mul_le_of_le_one_right ( by positivity ) <| inv_le_one_of_one_le₀ <| by linarith ) <| by simpa using summable_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr hp.2.one_lt ) |> Summable.comp_injective <| by intros a b; aesop;
        · exact Summable.mul_left _ <| summable_geometric_of_lt_one ( by positivity ) <| by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2;
      convert h_tail_bound.trans h_sum_bound using 1;
      rw [ tsum_geometric_of_lt_one ( by positivity ) ( by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) ] ; ring_nf;
      rw [ ← mul_inv ] ; congr ; nlinarith only [ inv_mul_cancel_left₀ ( show ( p : ℝ ) ≠ 0 by norm_cast; exact Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ) ( p ^ Nat.log p n ), inv_mul_cancel₀ ( show ( p : ℝ ) ≠ 0 by norm_cast; exact Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ), show ( p : ℝ ) ≥ 2 by norm_cast; exact Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ] ;
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
      refine' le_trans ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 2 n : ℝ ) + 1 ≥ 8 by norm_cast; linarith ) ) ( by positivity ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 3 n : ℝ ) + 1 ≥ 5 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 5 n : ℝ ) + 1 ≥ 4 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 7 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 11 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 13 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) _ ; norm_num;
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
    refine' congr rfl ( Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun k hk => _ );
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
    rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_le_sum fun x hx => _ ; rcases eq_or_ne x 0 with rfl | hx' <;> simp_all +decide ; ring_nf
    rw [ mul_assoc ] ; exact mul_le_mul_of_nonneg_left ( by rw [ ← div_eq_mul_inv ] ; exact ( by rw [ le_div_iff₀ ( by positivity ) ] ; norm_cast; linarith [ Nat.div_mul_le_self n x ] ) ) ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by rw [ ArithmeticFunction.vonMangoldt_apply ] ; positivity ) ) ) ) ) ) ) ) ) ) ) ) ) ) )
  have h_sum_eq : ∑ m ∈ Finset.Icc 1 n, vonMangoldt m / (m : ℝ) = sumS n := by
    rw [ Finset.Icc_eq_cons_Ioc ( by linarith ), Finset.sum_cons ] ; aesop
  nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast, Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) ), log_factorial_ge' n ( by linarith ) ]

private lemma sumS_mono {a b : ℕ} (h : a ≤ b) : sumS a ≤ sumS b := by
  exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc_right h ) fun _ _ _ ↦ div_nonneg ( by
    exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg ) ( by norm_cast; linarith [ Finset.mem_Icc.mp ‹_› ] )

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
  convert Finset.sum_le_sum h_term ; induction hn <;> simp_all +decide [ Finset.sum_Ico_succ_top ]
  rename_i k hk ih; linarith [ ih fun m hm₁ hm₂ => h_term m hm₁ ( by linarith ) ]

private lemma log_200_ge' : Real.log 200 ≥ 1418 / 270 := by
  have h_log_200 : Real.log 200 = 3 * Real.log 2 + 2 * Real.log 5 := by
    norm_num [ ← Real.log_rpow, ← Real.log_mul ]
  rw [ h_log_200, show ( 5 : ℝ ) = 2 ^ 2 * 1.25 by norm_num, Real.log_mul, Real.log_pow ] <;> ring_nf <;> norm_num
  have := Real.log_two_gt_d9 ; norm_num at * ; have := Real.log_inv ( 5 / 4 ) ; norm_num at * ; linarith [ Real.log_le_sub_one_of_pos ( show 0 < 4 / 5 by norm_num ) ]

private lemma abel_identity_sumT (n : ℕ) (hn : 200 ≤ n) :
    ∑ m ∈ Finset.Icc 200 n, (Λ m) / (m * Real.log m) = ((sumS n) - (sumS 199)) / Real.log n + ∑ m ∈ Finset.Ico 200 n, ((sumS m) - (sumS 199)) * (1 / Real.log m - 1 / Real.log (m + 1)) := by
  induction' hn with k hk
  · simp [sumS]
    rw [ show ( Finset.Icc 2 200 : Finset ℕ ) = Finset.Icc 2 199 ∪ { 200 } by decide, Finset.sum_union ] <;> norm_num ; ring
  · simp_all +decide [(Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc)]
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
    convert sum_log_ratio_le_log_log' 200 n ( by norm_num ) hn using 1
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
  refine' lt_of_lt_of_le _ ( Real.log_le_log ( by positivity ) h_log_199.le );
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

end MertensThird


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

/-- If `4*d ∣ m`, then `d ∣ m`. -/
lemma d_dvd_of_four_d_dvd {d m : ℕ} (hdvd : 4 * d ∣ m) : d ∣ m := by
  exact dvd_trans (show d ∣ 4 * d by exact ⟨4, by ac_rfl⟩) hdvd

/-- If `4*d ∣ m`, then `2 ∣ m`. -/
lemma two_dvd_of_four_d_dvd {d m : ℕ} (hdvd : 4 * d ∣ m) : 2 ∣ m := by
  exact dvd_trans (show 2 ∣ 4 * d by exact ⟨2 * d, by ac_rfl⟩) hdvd

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
          simpa using congrArg (fun y : ZMod (p + 1) ↦ y ^ 2) (ZMod.natCast_val x)
        _ = (d : ZMod (p + 1)) := by
          simpa [pow_two] using hx.symm

/-! ## Bridge from Pollack's literal theorem to the Jacobi-symbol specialization -/

/-- The quadratic character attached to `d`, viewed modulo any multiple `m` of `4*d`.

On integers coprime to `m` it is the Jacobi symbol `jacobiSym d`; on non-coprime integers it
is `0`.  The congruence invariance modulo `m` comes from `jacobiSym.mod_right`.

This is the canonical character used in the rest of the file; we no longer keep a separate
`pollack_theorem_1_3` compatibility wrapper. -/
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
      simpa [h0] using haOdd
    have hb0 : b ≠ 0 := by
      intro h0
      simpa [h0] using hbOdd
    split_ifs at * with hab
    · exact jacobiSym.mul_right' (d : ℤ) ha0 hb0
    · exact (hab (Nat.coprime_mul_iff_left.2 ⟨ha, hb⟩)).elim

@[simp] lemma attachedQuadraticCharacter_apply_coprime {d m n : ℕ}
    (hdvd : 4 * d ∣ m) (hn : Nat.Coprime n m) :
    attachedQuadraticCharacter d m hdvd n = jacobiSym (d : ℤ) n := by
  simp [attachedQuadraticCharacter, hn]

@[simp] lemma attachedQuadraticCharacter_apply_not_coprime {d m n : ℕ}
    (hdvd : 4 * d ∣ m) (hn : ¬ Nat.Coprime n m) :
    attachedQuadraticCharacter d m hdvd n = 0 := by
  simp [attachedQuadraticCharacter, hn]

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
      simpa [hzero] using hχ
    norm_num at h01
  have hpndvd : ¬ p ∣ m := (hp.coprime_iff_not_dvd).1 hcop
  have hp2 : p ≠ 2 := by
    intro hp2
    apply hpndvd
    simpa [hp2] using two_dvd_of_four_d_dvd hdvd
  have hJacobi : jacobiSym (d : ℤ) p = 1 := by
    rw [attachedQuadraticCharacter_apply_coprime hdvd hcop] at hχ
    exact hχ
  haveI : Fact p.Prime := ⟨hp⟩
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
lemma, and never the full cardinality statement of `pollack_theorem_1_3`. -/
lemma exists_small_prime_from_pollack :
    ∃ M0 : ℕ, ∀ {m d : ℕ}, M0 ≤ m → 4 * d ∣ m →
      ∃ p : ℕ,
        p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ m ∧
        (p : ℝ) ≤ Real.rpow (m : ℝ) ((3 : ℝ) / 8) ∧
        QuadResidueMod d p := by
  classical
  obtain ⟨m0, hm0⟩ :=
    pollack_theorem_1_3 ((1 : ℝ) / 8) 1 (by norm_num) (by norm_num)
  refine ⟨max (m0 + 1) 2, ?_⟩
  intro m d hm hdvd
  have hm2 : 2 ≤ m := le_trans (le_max_right _ _) hm
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm2
  haveI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  set χ : QuadraticCharacterMod m := attachedQuadraticCharacter d m hdvd
  set P : Finset ℕ :=
    residuePrimesUpTo m χ.toDirichletCharacterComplex ((1 : ℝ) / 8)
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
      simpa [hcard0] using hcard_pos_real
    exact (lt_irrefl (0 : ℝ)) this
  obtain ⟨p, hpP⟩ := Finset.card_pos.mp hcard_pos
  have hpP' : p ∈ residuePrimesUpTo m χ.toDirichletCharacterComplex ((1 : ℝ) / 8) := by
    simpa [P] using hpP
  simp [residuePrimesUpTo, residuePrimeUpperBound] at hpP'
  rcases hpP' with ⟨_, hpp, hpbound, hχpComplex⟩
  have hχp : χ p = 1 := by
    exact χ.eq_one_of_toDirichletCharacterComplex_apply_nat_eq_one
      (n := p) (by simpa using hχpComplex)
  have hspec : p ≠ 2 ∧ ¬ p ∣ m ∧ QuadResidueMod d p := by
    simpa [χ] using attachedQuadraticCharacter_spec (d := d) (m := m) (p := p) hdvd hpp hχp
  rcases hspec with ⟨hp2, hpndvd, hres⟩
  refine ⟨p, hpp, hp2, hpndvd, ?_, hres⟩
  convert hpbound using 1 <;> norm_num

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
    apply Nat.eq_of_mul_eq_mul_left (show 0 < a by simpa using ha)
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
          simpa [f] using s.orderEmbOfFin_mem rfl ⟨0, hi⟩
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
      (∏ i : Fin s.card, f i) = ∏ x ∈ Finset.map (s.orderEmbOfFin rfl).toEmbedding Finset.univ, x := by
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
    simpa using (Nat.eventually_pow_lt_factorial_sub (2 ^ 16) 1)
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

private lemma mem_finset_inf_iff {ι α : Type*} [DecidableEq ι] [Fintype α] [DecidableEq α]
    {s : Finset ι} {f : ι → Finset α} {a : α} :
    a ∈ s.inf f ↔ ∀ i ∈ s, a ∈ f i := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert b s hb ih =>
      simp [Finset.inf_insert, hb, ih]

private lemma count_root_class_with_divisors
    {n p r K : ℕ} (hp : p.Prime) (hn0 : n ≠ 0) (hpn : ¬ p ∣ n)
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
    (ha : 1 ≤ a)
    (hn3 : 3 ≤ n)
    (hp : p.Prime)
    (hpndvd : ¬ p ∣ a * n)
    (hroot : Nat.ModEq p (a * r ^ 2) n)
    (hK : K = Nat.sqrt ((n - 1) / a) + 1) :
    let U : Finset ℕ := ((Finset.range K).filter fun k ↦ Nat.ModEq p k r)
    let α := {k : ℕ // k ∈ U}
    let emb : α ↪ ℕ := ⟨Subtype.val, by intro x y h; exact Subtype.ext h⟩
    let S : ℕ → Finset α := fun q ↦ (Finset.univ : Finset α).filter fun k ↦ q ∣ (k : ℕ)
    let good : Finset α := n.primeFactors.inf fun q ↦ (S q)ᶜ
    ((good.map emb).card : ℝ)
      ≥ (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ))
          - (2 : ℝ) ^ n.primeFactors.card := by
  classical
  let U : Finset ℕ := ((Finset.range K).filter fun k ↦ Nat.ModEq p k r)
  let α := {k : ℕ // k ∈ U}
  let emb : α ↪ ℕ := ⟨Subtype.val, by intro x y h; exact Subtype.ext h⟩
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
      split_ifs <;> norm_num
    have hbit_le_one :
        ((if v % m < K % m then 1 else 0 : ℕ) : ℝ) ≤ 1 := by
      split_ifs <;> norm_num
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
    have hqprime : q.Prime := (Finset.mem_filter.mp hq).2
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
  let emb : α ↪ ℕ := ⟨Subtype.val, by intro x y h; exact Subtype.ext h⟩
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
        simp [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = u ^ 2 := by
        simpa [hm]
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
    hPa 1 (by decide) (by simpa using Nat.coprime_one_left n) hlt
  have hprod : n - a * 1 ^ 2 = (m + v) * (m - v) := by
    calc
      n - a * 1 ^ 2 = m ^ 2 - v ^ 2 := by
        simpa [haSq, hnSq]
      _ = (m + v) * (m - v) := by
        simpa using Nat.sq_sub_sq m v
  have htwo_le_vaddtwo : 2 ≤ v + 2 := by
    simpa using Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le v))
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

/-- Paper-style `Pa` statement for `a = 1`, stronger than the Formal Conjectures statement `erdos_1141` below. -/
theorem erdos_1141_variant : Set.Finite {n : ℕ | Pa 1 n} := by
  simpa using erdos_1141_variant_general 1 (by decide : 1 ≤ 1)

/-! ## Block Copied from Formal Conjectures -/

/-
The following block is copied as literally as possible from
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1141.lean
with only the proof of `erdos_1141` filled in via the stronger theorem `erdos_1141_variant` above.
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
      have h0 := h 0 (by simpa [hn]) (by simpa [hn] using Nat.coprime_zero_right.2 rfl)
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
  simpa [Set.not_infinite] using (erdos_1141_variant.subset hsubset)

#print axioms erdos_1141
-- 'Erdos1141.erdos_1141' depends on axioms: [propext, Classical.choice, Erdos1141.pollack_theorem_1_3, Quot.sound]

end Erdos1141
