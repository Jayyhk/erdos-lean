import Mathlib

namespace Erdos610

/-
# Kim 1995 — `R(3,t) = Ω(t² / log t)`

Full proof of Kim's lower bound on the Ramsey number `R(3,t)`, which
discharges `kim_theorem` below. Everything in this section is proved; the
headline result is `Erdos610.KimProof.kim_theorem`.

Reference: J. H. Kim, "The Ramsey number `R(3,t)` has order of magnitude
`t²/log t`", Random Structures & Algorithms 7(3) (1995), 173–207.
-/

namespace KimProof

open Finset SimpleGraph MeasureTheory ProbabilityTheory ENNReal

/-! ## Phase 1 — Concentration toolkit

Three concentration results are used throughout Kim's proof.

**Azuma-Hoeffding** (vanilla, conditional-MGF form) is available in Mathlib as
`HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF` together with
`measure_sum_ge_le_of_hasCondSubgaussianMGF`.

**Kahn's martingale inequality** (Kim Lemma 3.1, simplified form of Kahn 1997
Proposition 3.8): for i.i.d. Bernoulli `τ₁, …, τ_m` with parameter `p` and
`Φ : {0,1}^m → ℝ` Lipschitz with constants `(cⱼ)`, for every `ρ > 0`,

  `Pr(|Φ − E[Φ]| ≥ λ) ≤ 2 exp(−ρλ + (ρ²/2) p(1-p) ∑ⱼ cⱼ² exp(ρcⱼ))`.

Two corollaries: 3.2 (`ρ max cⱼ ≤ log 2` → drop the `exp(ρcⱼ)` factor) and
3.3 (`Φ = ∑ 1_{Aⱼ}` with `Aⱼ` depending only on `τⱼ` → replace
`p(1-p) ∑ cⱼ²` with `E[Φ] exp(ρ)`).

**Erdős-Tetali disjointness** (Kim Lemma 3.4): for a collection `𝒜` of events
with `∑_{A∈𝒜} Pr(A) ≤ η`, the probability that there exist `ℓ` pairwise-
independent events in `𝒜` all occurring is at most `η^ℓ / ℓ!`.  This is not
isolated as a lemma here; §4.9 uses it inline, via `calT_mem_prob_le` together
with the `l! ≥ (l/e)^l` bound in `fam59_core`.
-/

section Phase1

/-! ### Status

* `IsCoordLipschitz` — Kim's hypothesis (18).
* `bernoulliPr_kahn` — Kim Lemma 3.1 on the canonical space `{0,1}^m` with the
  product Bernoulli measure, proved by a direct MGF/Markov argument.
* `kahn_concentration` — the same bound transported to an arbitrary probability
  space carrying i.i.d. Bernoulli coordinates, via `kahnMap`.  This is the API
  that Corollaries 3.2, 3.3 and Main Lemma 2.1 consume; the corollaries are
  applied inline at each use site rather than stated separately.
-/

/-! ### Coordinate-Lipschitz functionals -/

/-- `Φ : ({0,1})^m → ℝ` is coordinate-Lipschitz with constants `c : Fin m → ℝ`
if flipping the value of the `j`-th coordinate changes `Φ` by at most `c j`.
This is the hypothesis `(18)` of Kim Lemma 3.1. -/
def IsCoordLipschitz {m : ℕ} (Φ : (Fin m → Bool) → ℝ) (c : Fin m → ℝ) : Prop :=
  ∀ (j : Fin m) (τ τ' : Fin m → Bool),
    (∀ ℓ, ℓ ≠ j → τ ℓ = τ' ℓ) → |Φ τ - Φ τ'| ≤ c j

/-- A coord-Lipschitz functional has nonnegative constants. -/
lemma IsCoordLipschitz.nonneg {m : ℕ} {Φ : (Fin m → Bool) → ℝ} {c : Fin m → ℝ}
    (h : IsCoordLipschitz Φ c) (j : Fin m) : 0 ≤ c j := by
  have := h j (fun _ => false) (fun _ => false) (fun _ _ => rfl)
  simp at this
  exact this

/-! ### Finite Bernoulli product space (concrete route to Kahn 3.1)

Mathlib's `HasCondSubgaussianMGF` requires `[StandardBorelSpace Ω]`, which is
not among the hypotheses of `kahn_concentration`. We therefore work on the
*canonical* finite space `Fin m → Bool`, where the product Bernoulli(`p`)
measure is an explicit finite weighted sum and all conditional expectations
become finite sums. This turns Kahn's martingale argument into a finite
induction over coordinates. -/

/-- Weight of a single point `σ : Fin m → Bool` under the product
Bernoulli(`p`) measure: `∏ⱼ (p if σⱼ else 1-p)`. -/
noncomputable def bernoulliWeight {m : ℕ} (p : ℝ) (σ : Fin m → Bool) : ℝ :=
  ∏ j, (if σ j = true then p else 1 - p)

/-- Each factor of `bernoulliWeight` is nonnegative when `0 ≤ p ≤ 1`. -/
lemma bernoulliWeight_factor_nonneg {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (b : Bool) : 0 ≤ (if b = true then p else 1 - p) := by
  by_cases h : b = true
  · simp [h, hp₀]
  · simp [h]; linarith

/-- `bernoulliWeight` is nonnegative. -/
lemma bernoulliWeight_nonneg {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (σ : Fin m → Bool) : 0 ≤ bernoulliWeight p σ :=
  Finset.prod_nonneg fun j _ => bernoulliWeight_factor_nonneg hp₀ hp₁ (σ j)

/-- **Total mass one**: `∑_σ bernoulliWeight p σ = 1`. This is
`Finset.prod_univ_sum` (distributing the product of sums). -/
lemma sum_bernoulliWeight {m : ℕ} (p : ℝ) :
    ∑ σ : Fin m → Bool, bernoulliWeight p σ = 1 := by
  classical
  unfold bernoulliWeight
  have h := Finset.prod_univ_sum (ι := Fin m) (κ := fun _ => Bool)
    (fun _ => (Finset.univ : Finset Bool))
    (fun _ b => (if b = true then p else 1 - p))
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  simp

/-- Expectation of `f` under the finite product Bernoulli(`p`) measure. -/
noncomputable def bernoulliExp {m : ℕ} (p : ℝ) (f : (Fin m → Bool) → ℝ) : ℝ :=
  ∑ σ : Fin m → Bool, bernoulliWeight p σ * f σ

/-- `bernoulliExp` of a constant is that constant (total mass one). -/
lemma bernoulliExp_const {m : ℕ} (p : ℝ) (a : ℝ) :
    bernoulliExp p (fun _ : Fin m → Bool => a) = a := by
  unfold bernoulliExp
  rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]

/-- `bernoulliExp` is linear in `f` (additivity). -/
lemma bernoulliExp_add {m : ℕ} (p : ℝ) (f g : (Fin m → Bool) → ℝ) :
    bernoulliExp p (fun σ => f σ + g σ)
      = bernoulliExp p f + bernoulliExp p g := by
  unfold bernoulliExp
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun σ _ => by ring

/-- `bernoulliExp` is linear in `f` (subtraction). -/
lemma bernoulliExp_sub {m : ℕ} (p : ℝ) (f g : (Fin m → Bool) → ℝ) :
    bernoulliExp p (fun σ => f σ - g σ)
      = bernoulliExp p f - bernoulliExp p g := by
  unfold bernoulliExp
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun σ _ => by ring

/-- Monotonicity of `bernoulliExp` for `0 ≤ p ≤ 1`. -/
lemma bernoulliExp_mono {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {f g : (Fin m → Bool) → ℝ} (h : ∀ σ, f σ ≤ g σ) :
    bernoulliExp p f ≤ bernoulliExp p g := by
  unfold bernoulliExp
  refine Finset.sum_le_sum fun σ _ => ?_
  exact mul_le_mul_of_nonneg_left (h σ) (bernoulliWeight_nonneg hp₀ hp₁ σ)

/-- **Merge at stage `k`**: coordinates `< k` are taken from `σ`, coordinates
`≥ k` from `ρ`. This is the "freeze the first `k` coordinates" operation
underlying the finite Doob martingale. -/
def mergeAt {m : ℕ} (k : ℕ) (σ ρ : Fin m → Bool) : Fin m → Bool :=
  fun j => if (j : ℕ) < k then σ j else ρ j

/-- Merging at stage `0` keeps everything from `ρ`. -/
lemma mergeAt_zero {m : ℕ} (σ ρ : Fin m → Bool) : mergeAt 0 σ ρ = ρ := by
  funext j; simp [mergeAt]

/-- Merging at stage `≥ m` keeps everything from `σ`. -/
lemma mergeAt_of_le {m k : ℕ} (hk : m ≤ k) (σ ρ : Fin m → Bool) :
    mergeAt k σ ρ = σ := by
  funext j
  have : (j : ℕ) < k := lt_of_lt_of_le j.isLt hk
  simp [mergeAt, this]

/-- **Finite Doob conditional expectation** at stage `k`: average `Φ` over the
free coordinates `≥ k`, freezing coordinates `< k` at their values in `σ`. -/
noncomputable def condExpFin {m : ℕ} (p : ℝ) (Φ : (Fin m → Bool) → ℝ) (k : ℕ)
    (σ : Fin m → Bool) : ℝ :=
  bernoulliExp p (fun ρ => Φ (mergeAt k σ ρ))

/-- At stage `0` the conditional expectation is the unconditional one. -/
lemma condExpFin_zero {m : ℕ} (p : ℝ) (Φ : (Fin m → Bool) → ℝ)
    (σ : Fin m → Bool) : condExpFin p Φ 0 σ = bernoulliExp p Φ := by
  unfold condExpFin
  simp only [mergeAt_zero]

/-- At stage `m` (or beyond) the conditional expectation returns `Φ` itself. -/
lemma condExpFin_of_le {m k : ℕ} (hk : m ≤ k) (p : ℝ)
    (Φ : (Fin m → Bool) → ℝ) (σ : Fin m → Bool) :
    condExpFin p Φ k σ = Φ σ := by
  unfold condExpFin
  simp only [mergeAt_of_le hk]
  exact bernoulliExp_const p (Φ σ)

/-- **Finite Doob increment**: `Y_k(σ) = Z_{k+1}(σ) − Z_k(σ)`. -/
noncomputable def incFin {m : ℕ} (p : ℝ) (Φ : (Fin m → Bool) → ℝ) (k : ℕ)
    (σ : Fin m → Bool) : ℝ :=
  condExpFin p Φ (k + 1) σ - condExpFin p Φ k σ

/-- Beyond stage `m` the increments vanish: both conditional expectations
already equal `Φ σ`. -/
lemma incFin_of_le {m k : ℕ} (hk : m ≤ k) (p : ℝ) (Φ : (Fin m → Bool) → ℝ)
    (σ : Fin m → Bool) : incFin p Φ k σ = 0 := by
  unfold incFin
  rw [condExpFin_of_le (le_trans hk (Nat.le_succ k)) p Φ σ,
    condExpFin_of_le hk p Φ σ, sub_self]

/-- **The merge-swap involution**: `(σ, ρ) ↦ (mergeAt k σ ρ, mergeAt k ρ σ)`
recovers `σ` in the first slot when applied twice. -/
lemma mergeAt_mergeAt {m : ℕ} (k : ℕ) (σ ρ : Fin m → Bool) :
    mergeAt k (mergeAt k σ ρ) (mergeAt k ρ σ) = σ := by
  funext j
  simp only [mergeAt]
  by_cases h : (j : ℕ) < k
  · simp [h]
  · simp [h]

/-- **Weight is preserved by the merge-swap**: the pair of merged points has
the same product weight as the original pair, because at each coordinate the
two factors are just exchanged. -/
lemma bernoulliWeight_mergeAt_mul {m : ℕ} (p : ℝ) (k : ℕ) (σ ρ : Fin m → Bool) :
    bernoulliWeight p (mergeAt k σ ρ) * bernoulliWeight p (mergeAt k ρ σ)
      = bernoulliWeight p σ * bernoulliWeight p ρ := by
  unfold bernoulliWeight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases h : (j : ℕ) < k
  · have e1 : mergeAt k σ ρ j = σ j := by simp [mergeAt, h]
    have e2 : mergeAt k ρ σ j = ρ j := by simp [mergeAt, h]
    rw [e1, e2]
  · have e1 : mergeAt k σ ρ j = ρ j := by simp [mergeAt, h]
    have e2 : mergeAt k ρ σ j = σ j := by simp [mergeAt, h]
    rw [e1, e2]; ring

/-- The merge-swap as an explicit involutive equivalence on pairs. -/
def mergeSwapEquiv {m : ℕ} (k : ℕ) :
    ((Fin m → Bool) × (Fin m → Bool)) ≃ ((Fin m → Bool) × (Fin m → Bool)) where
  toFun q := (mergeAt k q.1 q.2, mergeAt k q.2 q.1)
  invFun q := (mergeAt k q.1 q.2, mergeAt k q.2 q.1)
  left_inv q := by
    ext1
    · exact mergeAt_mergeAt k q.1 q.2
    · exact mergeAt_mergeAt k q.2 q.1
  right_inv q := by
    ext1
    · exact mergeAt_mergeAt k q.1 q.2
    · exact mergeAt_mergeAt k q.2 q.1

/-- **Tower property (finite form)**: taking the conditional expectation at
stage `k` and then the full expectation recovers the full expectation,
`E[E[g | F_k]] = E[g]`. Proved by the merge-swap involution on pairs, which
preserves the product weight and turns `g (mergeAt k σ ρ)` into `g σ`. -/
lemma bernoulliExp_condExpFin {m : ℕ} (p : ℝ) (k : ℕ)
    (g : (Fin m → Bool) → ℝ) :
    bernoulliExp p (condExpFin p g k) = bernoulliExp p g := by
  classical
  simp only [bernoulliExp, condExpFin]
  -- Rewrite the iterated sum as a single sum over pairs.
  have h_pair :
      (∑ σ : Fin m → Bool, bernoulliWeight p σ
          * ∑ ρ : Fin m → Bool, bernoulliWeight p ρ * g (mergeAt k σ ρ))
        = ∑ q : (Fin m → Bool) × (Fin m → Bool),
            bernoulliWeight p q.1 * bernoulliWeight p q.2 * g (mergeAt k q.1 q.2) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ρ _ => by ring
  rw [h_pair]
  -- Reindex by the merge-swap involution.
  have h_swap := Equiv.sum_comp (mergeSwapEquiv (m := m) k)
    (fun q : (Fin m → Bool) × (Fin m → Bool) =>
      bernoulliWeight p q.1 * bernoulliWeight p q.2 * g (mergeAt k q.1 q.2))
  rw [← h_swap]
  -- After reindexing each summand collapses to `w σ * w ρ * g σ`.
  have h_simp : ∀ q : (Fin m → Bool) × (Fin m → Bool),
      bernoulliWeight p (mergeSwapEquiv k q).1
          * bernoulliWeight p (mergeSwapEquiv k q).2
          * g (mergeAt k (mergeSwapEquiv k q).1 (mergeSwapEquiv k q).2)
        = bernoulliWeight p q.1 * bernoulliWeight p q.2 * g q.1 := by
    intro q
    show bernoulliWeight p (mergeAt k q.1 q.2) * bernoulliWeight p (mergeAt k q.2 q.1)
        * g (mergeAt k (mergeAt k q.1 q.2) (mergeAt k q.2 q.1))
      = bernoulliWeight p q.1 * bernoulliWeight p q.2 * g q.1
    rw [mergeAt_mergeAt k q.1 q.2, bernoulliWeight_mergeAt_mul]
  simp only [h_simp]
  -- Finally, sum out the second coordinate (total mass one).
  rw [Fintype.sum_prod_type]
  have h_fac : ∀ σ : Fin m → Bool,
      (∑ _ρ : Fin m → Bool, bernoulliWeight p σ * bernoulliWeight p _ρ * g σ)
        = bernoulliWeight p σ * g σ := by
    intro σ
    rw [show (∑ _ρ : Fin m → Bool, bernoulliWeight p σ * bernoulliWeight p _ρ * g σ)
        = (bernoulliWeight p σ * g σ) * ∑ _ρ : Fin m → Bool, bernoulliWeight p _ρ from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ρ _ => by ring]
    rw [sum_bernoulliWeight, mul_one]
  simp only [h_fac]

/-! ### The centered-Bernoulli MGF and its Bennett bound

The conditional MGF of a Doob increment is exactly the MGF of a scaled
centered Bernoulli. We analyse it as an explicit function `bmgf p s` of the
tilt parameter `s`, computing two derivatives and deriving Kahn's
`(s²/2)·p(1-p)·e^s` bound by a pair of monotonicity arguments. -/

/-- The centered Bernoulli MGF `E[exp(s(X-p))] = (1-p)e^{-sp} + p·e^{s(1-p)}`,
as an explicit real function of the tilt `s`. -/
noncomputable def bmgf (p s : ℝ) : ℝ :=
  (1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p))

/-- Its first derivative `p(1-p)(e^{s(1-p)} − e^{-sp})`. -/
noncomputable def bmgf' (p s : ℝ) : ℝ :=
  p * (1 - p) * (Real.exp (s * (1 - p)) - Real.exp (-(s * p)))

/-- Its second derivative `p(1-p)(p·e^{-sp} + (1-p)·e^{s(1-p)})`. -/
noncomputable def bmgf'' (p s : ℝ) : ℝ :=
  p * (1 - p) * (p * Real.exp (-(s * p)) + (1 - p) * Real.exp (s * (1 - p)))

@[simp] lemma bmgf_zero (p : ℝ) : bmgf p 0 = 1 := by
  unfold bmgf; simp

@[simp] lemma bmgf'_zero (p : ℝ) : bmgf' p 0 = 0 := by
  unfold bmgf'; simp

/-- `bmgf p` is differentiable with derivative `bmgf' p`. -/
lemma hasDerivAt_bmgf (p s : ℝ) : HasDerivAt (bmgf p) (bmgf' p s) s := by
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (-(x * p)))
      (Real.exp (-(s * p)) * (-p)) s := by
    have hin : HasDerivAt (fun x : ℝ => -(x * p)) (-p) s := by
      simpa using ((hasDerivAt_id s).mul_const p).neg
    simpa using (Real.hasDerivAt_exp (-(s * p))).comp s hin
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (x * (1 - p)))
      (Real.exp (s * (1 - p)) * (1 - p)) s := by
    have hin : HasDerivAt (fun x : ℝ => x * (1 - p)) (1 - p) s := by
      simpa using (hasDerivAt_id s).mul_const (1 - p)
    simpa using (Real.hasDerivAt_exp (s * (1 - p))).comp s hin
  have := (h1.const_mul (1 - p)).add (h2.const_mul p)
  unfold bmgf bmgf'
  convert this using 1
  ring

/-- `bmgf' p` is differentiable with derivative `bmgf'' p`. -/
lemma hasDerivAt_bmgf' (p s : ℝ) : HasDerivAt (bmgf' p) (bmgf'' p s) s := by
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (-(x * p)))
      (Real.exp (-(s * p)) * (-p)) s := by
    have hin : HasDerivAt (fun x : ℝ => -(x * p)) (-p) s := by
      simpa using ((hasDerivAt_id s).mul_const p).neg
    simpa using (Real.hasDerivAt_exp (-(s * p))).comp s hin
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (x * (1 - p)))
      (Real.exp (s * (1 - p)) * (1 - p)) s := by
    have hin : HasDerivAt (fun x : ℝ => x * (1 - p)) (1 - p) s := by
      simpa using (hasDerivAt_id s).mul_const (1 - p)
    simpa using (Real.hasDerivAt_exp (s * (1 - p))).comp s hin
  have := (h2.sub h1).const_mul (p * (1 - p))
  unfold bmgf' bmgf''
  convert this using 1
  ring

/-- `bmgf` is strictly positive when `0 ≤ p ≤ 1`. -/
lemma bmgf_pos {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (s : ℝ) : 0 < bmgf p s := by
  unfold bmgf
  rcases eq_or_lt_of_le hp₀ with h | hp_pos
  · rw [← h]; simp [Real.exp_pos]
  rcases eq_or_lt_of_le hp₁ with h | hp_lt
  · rw [h]; simp [Real.exp_pos]
  have h1 : 0 < (1 - p) * Real.exp (-(s * p)) :=
    mul_pos (by linarith) (Real.exp_pos _)
  have h2 : 0 < p * Real.exp (s * (1 - p)) := mul_pos hp_pos (Real.exp_pos _)
  linarith

/-- For `s ≥ 0` the MGF is increasing: `bmgf' p s ≥ 0`. -/
lemma bmgf'_nonneg {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ bmgf' p s := by
  unfold bmgf'
  have hmul : 0 ≤ p * (1 - p) := mul_nonneg hp₀ (by linarith)
  have harg : -(s * p) ≤ s * (1 - p) := by nlinarith
  have hexp : Real.exp (-(s * p)) ≤ Real.exp (s * (1 - p)) :=
    Real.exp_le_exp.mpr harg
  exact mul_nonneg hmul (by linarith)

/-- **The second-derivative bound** `f'' ≤ p(1-p)·e^s·f` for `s ≥ 0`.
After cancelling `p(1-p)` this reduces to `p·e^{-sp} ≤ p·e^{s(2-p)}`, which
holds because `-sp ≤ s(2-p)`. This is the sharp Bennett/Kahn estimate: the
tilted variance never exceeds `p(1-p)e^s`. -/
lemma bmgf''_le {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) {s : ℝ} (hs : 0 ≤ s) :
    bmgf'' p s ≤ p * (1 - p) * Real.exp s * bmgf p s := by
  unfold bmgf'' bmgf
  have hmul : 0 ≤ p * (1 - p) := mul_nonneg hp₀ (by linarith)
  have e1 : Real.exp s * Real.exp (-(s * p)) = Real.exp (s * (1 - p)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp s * Real.exp (s * (1 - p)) = Real.exp (s * (2 - p)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hR : p * (1 - p) * Real.exp s
        * ((1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p)))
      = p * (1 - p) * ((1 - p) * (Real.exp s * Real.exp (-(s * p)))
          + p * (Real.exp s * Real.exp (s * (1 - p)))) := by ring
  rw [hR, e1, e2]
  refine mul_le_mul_of_nonneg_left ?_ hmul
  have key : Real.exp (-(s * p)) ≤ Real.exp (s * (2 - p)) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have := mul_le_mul_of_nonneg_left key hp₀
  linarith

/-- **First ODE comparison**: on `[0, S]` we have `f' ≤ M·s·f` where
`M := p(1-p)e^S`. Proved by showing `u(s) := M·s·f(s) − f'(s)` starts at `0`
and has nonnegative derivative `M·f + M·s·f' − f''`. -/
lemma bmgf'_le_mul {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) {S : ℝ} (hS : 0 ≤ S)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) S) :
    bmgf' p s ≤ (p * (1 - p) * Real.exp S) * s * bmgf p s := by
  set M : ℝ := p * (1 - p) * Real.exp S with hM_def
  have hM_nn : 0 ≤ M :=
    mul_nonneg (mul_nonneg hp₀ (by linarith)) (Real.exp_nonneg _)
  set u : ℝ → ℝ := fun x => M * x * bmgf p x - bmgf' p x with hu_def
  have hu_deriv : ∀ x : ℝ, HasDerivAt u
      (M * bmgf p x + M * x * bmgf' p x - bmgf'' p x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => M * y) M x := by
      simpa using (hasDerivAt_id x).const_mul M
    have h3 := h1.mul (hasDerivAt_bmgf p x)
    have h4 := hasDerivAt_bmgf' p x
    have hcomb := h3.sub h4
    convert hcomb using 1 <;> ring
  have hu_zero : u 0 = 0 := by simp [hu_def]
  have hu_nonneg_deriv : ∀ x ∈ interior (Set.Icc (0 : ℝ) S),
      0 ≤ M * bmgf p x + M * x * bmgf p x * 0 + (M * x * bmgf' p x - bmgf'' p x) := by
    intro x hx
    rw [interior_Icc] at hx
    obtain ⟨hx0, hxS⟩ := hx
    have hbpos := bmgf_pos hp₀ hp₁ x
    have hb'nn := bmgf'_nonneg hp₀ hp₁ (le_of_lt hx0)
    have hb''le := bmgf''_le hp₀ hp₁ (le_of_lt hx0)
    have hexp_le : Real.exp x ≤ Real.exp S := Real.exp_le_exp.mpr (le_of_lt hxS)
    have hstep : p * (1 - p) * Real.exp x * bmgf p x ≤ M * bmgf p x := by
      rw [hM_def]
      have hpp : 0 ≤ p * (1 - p) := mul_nonneg hp₀ (by linarith)
      have : p * (1 - p) * Real.exp x ≤ p * (1 - p) * Real.exp S :=
        mul_le_mul_of_nonneg_left hexp_le hpp
      exact mul_le_mul_of_nonneg_right this (le_of_lt hbpos)
    have hprod : 0 ≤ M * x * bmgf' p x :=
      mul_nonneg (mul_nonneg hM_nn (le_of_lt hx0)) hb'nn
    nlinarith [hb''le, hstep, hprod]
  have hmono : MonotoneOn u (Set.Icc (0 : ℝ) S) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) S)
      (fun x _ => (hu_deriv x).continuousAt.continuousWithinAt)
      (fun x _ => (hu_deriv x).hasDerivWithinAt)
    intro x hx
    have := hu_nonneg_deriv x hx
    linarith
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) S := Set.left_mem_Icc.mpr hS
  have := hmono h0mem hs hs.1
  rw [hu_zero] at this
  simp only [hu_def] at this
  linarith


/-- **Kahn's MGF bound (sharp Bennett form)**: for `S ≥ 0` and `p ∈ [0,1]`,
`(1-p)e^{-Sp} + p·e^{S(1-p)} ≤ exp((S²/2)·p(1-p)·e^S)`.

Proof: `h(x) := f(x)·exp(-M x²/2)` with `M := p(1-p)e^S` has derivative
`exp(…)·(f'(x) − M x f(x)) ≤ 0` on `[0,S]` by `bmgf'_le_mul`, so `h` is
antitone and `h(S) ≤ h(0) = 1`. -/
lemma bmgf_le_exp {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) {S : ℝ} (hS : 0 ≤ S) :
    bmgf p S ≤ Real.exp (S ^ 2 / 2 * (p * (1 - p) * Real.exp S)) := by
  set M : ℝ := p * (1 - p) * Real.exp S with hM_def
  set h : ℝ → ℝ := fun x => bmgf p x * Real.exp (-(M * x ^ 2 / 2)) with hh_def
  have hexp_deriv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.exp (-(M * y ^ 2 / 2)))
      (Real.exp (-(M * x ^ 2 / 2)) * (-(M * x))) x := by
    intro x
    have hsq : HasDerivAt (fun y : ℝ => M * y ^ 2 / 2) (M * x) x := by
      have hp2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have := (hp2.const_mul M).div_const 2
      convert this using 1
      ring
    exact (Real.hasDerivAt_exp _).comp x hsq.neg
  have hh_deriv : ∀ x : ℝ, HasDerivAt h
      ((bmgf' p x - M * x * bmgf p x) * Real.exp (-(M * x ^ 2 / 2))) x := by
    intro x
    have hcomb := (hasDerivAt_bmgf p x).mul (hexp_deriv x)
    convert hcomb using 1
    ring
  have hanti : AntitoneOn h (Set.Icc (0 : ℝ) S) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) S)
      (fun x _ => (hh_deriv x).continuousAt.continuousWithinAt)
      (fun x _ => (hh_deriv x).hasDerivWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    have hxmem : x ∈ Set.Icc (0 : ℝ) S := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hkey := bmgf'_le_mul hp₀ hp₁ hS hxmem
    have : bmgf' p x - M * x * bmgf p x ≤ 0 := by
      rw [hM_def]; linarith
    exact mul_nonpos_of_nonpos_of_nonneg this (Real.exp_nonneg _)
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) S := Set.left_mem_Icc.mpr hS
  have hSmem : S ∈ Set.Icc (0 : ℝ) S := Set.right_mem_Icc.mpr hS
  have hle := hanti h0mem hSmem hS
  have hh0 : h 0 = 1 := by simp [hh_def]
  rw [hh0] at hle
  -- hle : bmgf p S * exp(-(M * S^2/2)) ≤ 1
  have hpos : (0 : ℝ) < Real.exp (M * S ^ 2 / 2) := Real.exp_pos _
  have hEmul : Real.exp (-(M * S ^ 2 / 2)) * Real.exp (M * S ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt hpos)
  rw [mul_assoc, hEmul, mul_one, one_mul] at hmul
  calc bmgf p S ≤ Real.exp (M * S ^ 2 / 2) := hmul
    _ = Real.exp (S ^ 2 / 2 * (p * (1 - p) * Real.exp S)) := by congr 1; ring

/-- **Single-coordinate marginal**: averaging a function of one coordinate
gives the Bernoulli(`p`) average. Proved by the same product-of-sums
distribution used for `sum_bernoulliWeight`. -/
lemma bernoulliExp_coord {m : ℕ} (p : ℝ) (j : Fin m) (f : Bool → ℝ) :
    bernoulliExp p (fun ρ => f (ρ j)) = p * f true + (1 - p) * f false := by
  classical
  unfold bernoulliExp bernoulliWeight
  have hfac : ∀ ρ : Fin m → Bool,
      (∏ i, (if ρ i = true then p else 1 - p)) * f (ρ j)
        = ∏ i, ((if ρ i = true then p else 1 - p)
            * (if i = j then f (ρ i) else 1)) := by
    intro ρ
    rw [Finset.prod_mul_distrib]
    congr 1
    simp
  simp only [hfac]
  have h := Finset.prod_univ_sum (ι := Fin m) (κ := fun _ => Bool)
    (fun _ => (Finset.univ : Finset Bool))
    (fun i b => (if b = true then p else 1 - p) * (if i = j then f b else 1))
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  rw [Finset.prod_eq_single j]
  · simp [Fintype.sum_bool]
  · intro i _ hij
    simp [hij, Fintype.sum_bool]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- **Conditional expectations only see the frozen coordinates**: if `σ` and
`σ'` agree on all coordinates `< j`, their stage-`j` conditional expectations
coincide. -/
lemma condExpFin_congr {m : ℕ} (p : ℝ) (Φ : (Fin m → Bool) → ℝ) (j : ℕ)
    (σ σ' : Fin m → Bool) (h : ∀ l : Fin m, (l : ℕ) < j → σ l = σ' l) :
    condExpFin p Φ j σ = condExpFin p Φ j σ' := by
  unfold condExpFin
  congr 1
  funext ρ
  congr 1
  funext l
  simp only [mergeAt]
  by_cases hl : (l : ℕ) < j
  · rw [if_pos hl, if_pos hl]; exact h l hl
  · rw [if_neg hl, if_neg hl]

/-- Merging at stage `k` does not change the stage-`k` conditional
expectation. -/
lemma condExpFin_mergeAt {m : ℕ} (p : ℝ) (Φ : (Fin m → Bool) → ℝ) (k : ℕ)
    (σ ρ : Fin m → Bool) :
    condExpFin p Φ k (mergeAt k σ ρ) = condExpFin p Φ k σ := by
  refine condExpFin_congr p Φ k _ _ fun l hl => ?_
  simp [mergeAt, hl]

/-- **Merge-tower identity**: the level-`j` merge-swap applied inside a
level-`k` merge (with `k ≤ j`) collapses back to the level-`k` merge. This is
the combinatorial heart of the conditional tower property. -/
lemma mergeAt_tower {m : ℕ} {k j : ℕ} (hkj : k ≤ j) (σ ρ ρ' : Fin m → Bool) :
    mergeAt j (mergeAt k σ (mergeAt j ρ ρ')) (mergeAt j ρ' ρ) = mergeAt k σ ρ := by
  funext l
  simp only [mergeAt]
  by_cases h1 : (l : ℕ) < k
  · have h2 : (l : ℕ) < j := lt_of_lt_of_le h1 hkj
    simp [h1, h2]
  · by_cases h2 : (l : ℕ) < j
    · simp [h1, h2]
    · simp [h1, h2]

/-- **Conditional tower property** `E[E[Φ | F_j] | F_k] = E[Φ | F_k]` for
`k ≤ j`, in the finite Bernoulli model. Proved by the level-`j` merge-swap
involution, which preserves the product weight and collapses the nested merge
via `mergeAt_tower`. -/
lemma condExpFin_tower {m : ℕ} (p : ℝ) (Φ : (Fin m → Bool) → ℝ) {k j : ℕ}
    (hkj : k ≤ j) (σ : Fin m → Bool) :
    condExpFin p (fun σ' => condExpFin p Φ j σ') k σ = condExpFin p Φ k σ := by
  classical
  simp only [condExpFin, bernoulliExp]
  have h_pair : (∑ ρ : Fin m → Bool, bernoulliWeight p ρ *
        ∑ ρ' : Fin m → Bool, bernoulliWeight p ρ'
          * Φ (mergeAt j (mergeAt k σ ρ) ρ'))
      = ∑ q : (Fin m → Bool) × (Fin m → Bool),
          bernoulliWeight p q.1 * bernoulliWeight p q.2
            * Φ (mergeAt j (mergeAt k σ q.1) q.2) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ρ' _ => by ring
  rw [h_pair]
  have h_swap := Equiv.sum_comp (mergeSwapEquiv (m := m) j)
    (fun q : (Fin m → Bool) × (Fin m → Bool) =>
      bernoulliWeight p q.1 * bernoulliWeight p q.2
        * Φ (mergeAt j (mergeAt k σ q.1) q.2))
  rw [← h_swap]
  have h_simp : ∀ q : (Fin m → Bool) × (Fin m → Bool),
      bernoulliWeight p (mergeSwapEquiv j q).1
          * bernoulliWeight p (mergeSwapEquiv j q).2
          * Φ (mergeAt j (mergeAt k σ (mergeSwapEquiv j q).1)
              (mergeSwapEquiv j q).2)
        = bernoulliWeight p q.1 * bernoulliWeight p q.2
            * Φ (mergeAt k σ q.1) := by
    intro q
    show bernoulliWeight p (mergeAt j q.1 q.2)
        * bernoulliWeight p (mergeAt j q.2 q.1)
        * Φ (mergeAt j (mergeAt k σ (mergeAt j q.1 q.2)) (mergeAt j q.2 q.1))
      = bernoulliWeight p q.1 * bernoulliWeight p q.2 * Φ (mergeAt k σ q.1)
    rw [mergeAt_tower hkj σ q.1 q.2, bernoulliWeight_mergeAt_mul]
  simp only [h_simp]
  rw [Fintype.sum_prod_type]
  have h_fac : ∀ ρ : Fin m → Bool,
      (∑ _ρ' : Fin m → Bool, bernoulliWeight p ρ * bernoulliWeight p _ρ'
          * Φ (mergeAt k σ ρ))
        = bernoulliWeight p ρ * Φ (mergeAt k σ ρ) := by
    intro ρ
    rw [show (∑ _ρ' : Fin m → Bool, bernoulliWeight p ρ * bernoulliWeight p _ρ'
          * Φ (mergeAt k σ ρ))
        = (bernoulliWeight p ρ * Φ (mergeAt k σ ρ))
            * ∑ _ρ' : Fin m → Bool, bernoulliWeight p _ρ' from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ρ' _ => by ring]
    rw [sum_bernoulliWeight, mul_one]
  simp only [h_fac]

/-- The two possible stage-`(k+1)` conditional values obtained by setting
coordinate `k` to `true` or `false`. -/
noncomputable def stepVal {m : ℕ} (p : ℝ) (Φ : (Fin m → Bool) → ℝ) (k : ℕ)
    (hk : k < m) (σ : Fin m → Bool) (b : Bool) : ℝ :=
  condExpFin p Φ (k + 1) (Function.update σ (⟨k, hk⟩ : Fin m) b)

/-- The stage-`(k+1)` conditional expectation after a stage-`k` merge depends
on `ρ` only through coordinate `k`. -/
lemma condExpFin_succ_mergeAt {m : ℕ} (p : ℝ) (Φ : (Fin m → Bool) → ℝ) {k : ℕ}
    (hk : k < m) (σ ρ : Fin m → Bool) :
    condExpFin p Φ (k + 1) (mergeAt k σ ρ)
      = stepVal p Φ k hk σ (ρ (⟨k, hk⟩ : Fin m)) := by
  unfold stepVal
  refine condExpFin_congr p Φ (k + 1) _ _ fun l hl => ?_
  simp only [mergeAt]
  by_cases h : (l : ℕ) < k
  · have hne : l ≠ (⟨k, hk⟩ : Fin m) := by
      intro hcon; rw [hcon] at h; exact absurd h (lt_irrefl k)
    rw [if_pos h, Function.update_of_ne hne]
  · have hlk : (l : ℕ) = k := by omega
    have hle : l = (⟨k, hk⟩ : Fin m) := Fin.ext hlk
    rw [if_neg h, hle, Function.update_self]

/-- **One-step mixture identity**: the stage-`k` conditional expectation is the
Bernoulli(`p`) mixture of the two stage-`(k+1)` values. -/
lemma condExpFin_eq_mix {m : ℕ} (p : ℝ) (Φ : (Fin m → Bool) → ℝ) {k : ℕ}
    (hk : k < m) (σ : Fin m → Bool) :
    condExpFin p Φ k σ
      = p * stepVal p Φ k hk σ true + (1 - p) * stepVal p Φ k hk σ false := by
  have htow := condExpFin_tower p Φ (k := k) (j := k + 1) (Nat.le_succ k) σ
  rw [← htow]
  show bernoulliExp p (fun ρ => condExpFin p Φ (k + 1) (mergeAt k σ ρ)) = _
  have hrw : (fun ρ : Fin m → Bool => condExpFin p Φ (k + 1) (mergeAt k σ ρ))
      = fun ρ => stepVal p Φ k hk σ (ρ (⟨k, hk⟩ : Fin m)) := by
    funext ρ; exact condExpFin_succ_mergeAt p Φ hk σ ρ
  rw [hrw]
  exact bernoulliExp_coord p (⟨k, hk⟩ : Fin m) (stepVal p Φ k hk σ)

/-- **Two-point form of the increment**: conditionally on the first `k`
coordinates, the Doob increment equals `d·(1_{X=1} − p)` where
`d = stepVal true − stepVal false`. -/
lemma incFin_mergeAt_eq {m : ℕ} (p : ℝ) (Φ : (Fin m → Bool) → ℝ) {k : ℕ}
    (hk : k < m) (σ ρ : Fin m → Bool) :
    incFin p Φ k (mergeAt k σ ρ)
      = (if ρ (⟨k, hk⟩ : Fin m) = true then
            (1 - p) * (stepVal p Φ k hk σ true - stepVal p Φ k hk σ false)
          else -(p * (stepVal p Φ k hk σ true - stepVal p Φ k hk σ false))) := by
  unfold incFin
  rw [condExpFin_succ_mergeAt p Φ hk σ ρ, condExpFin_mergeAt p Φ k σ ρ,
    condExpFin_eq_mix p Φ hk σ]
  by_cases h : ρ (⟨k, hk⟩ : Fin m) = true
  · rw [h]; simp; ring
  · have hf : ρ (⟨k, hk⟩ : Fin m) = false := by
      cases hb : ρ (⟨k, hk⟩ : Fin m) with
      | false => rfl
      | true => exact absurd hb h
    rw [hf]; simp; ring

/-- Two stage-`(k+1)` merges with coordinate `k` flipped agree everywhere else. -/
lemma mergeAt_update_eq_off {m : ℕ} {k : ℕ} (hk : k < m) (σ ρ : Fin m → Bool)
    (l : Fin m) (hl : l ≠ (⟨k, hk⟩ : Fin m)) :
    mergeAt (k + 1) (Function.update σ (⟨k, hk⟩ : Fin m) true) ρ l
      = mergeAt (k + 1) (Function.update σ (⟨k, hk⟩ : Fin m) false) ρ l := by
  simp only [mergeAt]
  by_cases h : (l : ℕ) < k + 1
  · rw [if_pos h, if_pos h, Function.update_of_ne hl, Function.update_of_ne hl]
  · rw [if_neg h, if_neg h]

/-- **The two-point gap is Lipschitz-bounded**: `|d| ≤ c k`. -/
lemma abs_stepVal_diff_le {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {Φ : (Fin m → Bool) → ℝ} {c : Fin m → ℝ} (h_lip : IsCoordLipschitz Φ c)
    {k : ℕ} (hk : k < m) (σ : Fin m → Bool) :
    |stepVal p Φ k hk σ true - stepVal p Φ k hk σ false| ≤ c (⟨k, hk⟩ : Fin m) := by
  have h_eq : stepVal p Φ k hk σ true - stepVal p Φ k hk σ false
      = bernoulliExp p (fun ρ =>
          Φ (mergeAt (k + 1) (Function.update σ (⟨k, hk⟩ : Fin m) true) ρ)
          - Φ (mergeAt (k + 1) (Function.update σ (⟨k, hk⟩ : Fin m) false) ρ)) := by
    unfold stepVal condExpFin
    rw [bernoulliExp_sub]
  have h_pt : ∀ ρ : Fin m → Bool,
      |Φ (mergeAt (k + 1) (Function.update σ (⟨k, hk⟩ : Fin m) true) ρ)
        - Φ (mergeAt (k + 1) (Function.update σ (⟨k, hk⟩ : Fin m) false) ρ)|
        ≤ c (⟨k, hk⟩ : Fin m) :=
    fun ρ => h_lip _ _ _ (fun l hl => mergeAt_update_eq_off hk σ ρ l hl)
  rw [h_eq, abs_le]
  constructor
  · have := bernoulliExp_mono (m := m) hp₀ hp₁
      (f := fun _ => -c (⟨k, hk⟩ : Fin m))
      (g := fun ρ => Φ (mergeAt (k + 1) (Function.update σ (⟨k, hk⟩ : Fin m) true) ρ)
        - Φ (mergeAt (k + 1) (Function.update σ (⟨k, hk⟩ : Fin m) false) ρ))
      (fun ρ => (abs_le.mp (h_pt ρ)).1)
    rwa [bernoulliExp_const] at this
  · have := bernoulliExp_mono (m := m) hp₀ hp₁
      (f := fun ρ => Φ (mergeAt (k + 1) (Function.update σ (⟨k, hk⟩ : Fin m) true) ρ)
        - Φ (mergeAt (k + 1) (Function.update σ (⟨k, hk⟩ : Fin m) false) ρ))
      (g := fun _ => c (⟨k, hk⟩ : Fin m))
      (fun ρ => (abs_le.mp (h_pt ρ)).2)
    rwa [bernoulliExp_const] at this

/-- Reflection identity `bmgf p (-s) = bmgf (1-p) s`: negating the tilt swaps
the roles of `p` and `1-p`. -/
lemma bmgf_neg (p s : ℝ) : bmgf p (-s) = bmgf (1 - p) s := by
  unfold bmgf
  have e1 : -(-s * p) = s * p := by ring
  have e2 : -(s * (1 - p)) = -s * (1 - p) := by ring
  have e3 : s * (1 - (1 - p)) = s * p := by ring
  rw [e1, e3, ← e2]
  ring

/-- **Two-sided sharp Bennett bound**, valid for every real tilt `s`. -/
lemma bmgf_le_exp_abs {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (s : ℝ) :
    bmgf p s ≤ Real.exp (s ^ 2 / 2 * (p * (1 - p) * Real.exp |s|)) := by
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs]
    exact bmgf_le_exp hp₀ hp₁ hs
  · rw [abs_of_neg hs]
    have hns : (0 : ℝ) ≤ -s := by linarith
    have hrefl : bmgf p s = bmgf (1 - p) (-s) := by
      have := bmgf_neg p (-s)
      rwa [neg_neg] at this
    rw [hrefl]
    refine (bmgf_le_exp (p := 1 - p) (by linarith) (by linarith) hns).trans ?_
    apply Real.exp_le_exp.mpr
    have hsq : (-s) ^ 2 = s ^ 2 := by ring
    rw [hsq]
    have : (1 - p) * (1 - (1 - p)) = p * (1 - p) := by ring
    rw [this]

/-- **The conditional MGF of a Doob increment is exactly a scaled centered
Bernoulli MGF.** This is the bridge between the combinatorial construction and
the analytic Bennett bound. -/
lemma condMGF_eq_bmgf {m : ℕ} (p : ℝ) (Φ : (Fin m → Bool) → ℝ) {k : ℕ}
    (hk : k < m) (σ : Fin m → Bool) (t : ℝ) :
    bernoulliExp p (fun ρ => Real.exp (t * incFin p Φ k (mergeAt k σ ρ)))
      = bmgf p (t * (stepVal p Φ k hk σ true - stepVal p Φ k hk σ false)) := by
  set d : ℝ := stepVal p Φ k hk σ true - stepVal p Φ k hk σ false with hd_def
  have hrw : (fun ρ : Fin m → Bool => Real.exp (t * incFin p Φ k (mergeAt k σ ρ)))
      = fun ρ => (fun b : Bool =>
          Real.exp (t * (if b = true then (1 - p) * d else -(p * d)))) (ρ (⟨k, hk⟩ : Fin m)) := by
    funext ρ
    rw [incFin_mergeAt_eq p Φ hk σ ρ]
  rw [hrw]
  rw [bernoulliExp_coord p (⟨k, hk⟩ : Fin m)
    (fun b : Bool => Real.exp (t * (if b = true then (1 - p) * d else -(p * d))))]
  unfold bmgf
  simp only [if_pos rfl, Bool.false_eq_true, if_false, if_true]
  have e1 : t * ((1 - p) * d) = t * d * (1 - p) := by ring
  have e2 : t * (-(p * d)) = -(t * d * p) := by ring
  rw [e1, e2]
  ring

/-- **Conditional MGF bound**: for `t ≥ 0`, the conditional MGF of a Doob
increment is at most `exp((t·c_k)²/2 · p(1-p) · e^{t·c_k})` — exactly the
per-coordinate factor appearing in Kahn's Lemma 3.1. -/
lemma condMGF_le {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {Φ : (Fin m → Bool) → ℝ} {c : Fin m → ℝ} (h_lip : IsCoordLipschitz Φ c)
    {k : ℕ} (hk : k < m) (σ : Fin m → Bool) {t : ℝ} (ht : 0 ≤ t) :
    bernoulliExp p (fun ρ => Real.exp (t * incFin p Φ k (mergeAt k σ ρ)))
      ≤ Real.exp (t ^ 2 / 2 * (p * (1 - p)
          * (c (⟨k, hk⟩ : Fin m) ^ 2 * Real.exp (t * c (⟨k, hk⟩ : Fin m))))) := by
  set d : ℝ := stepVal p Φ k hk σ true - stepVal p Φ k hk σ false with hd_def
  have hck_nn : 0 ≤ c (⟨k, hk⟩ : Fin m) := h_lip.nonneg _
  have hd_abs : |d| ≤ c (⟨k, hk⟩ : Fin m) := abs_stepVal_diff_le hp₀ hp₁ h_lip hk σ
  rw [condMGF_eq_bmgf p Φ hk σ t]
  refine (bmgf_le_exp_abs hp₀ hp₁ (t * d)).trans ?_
  apply Real.exp_le_exp.mpr
  have hpp : 0 ≤ p * (1 - p) := mul_nonneg hp₀ (by linarith)
  -- (t*d)^2 ≤ t^2 * c^2
  have hd_sq : d ^ 2 ≤ c (⟨k, hk⟩ : Fin m) ^ 2 := by
    nlinarith [abs_nonneg d, sq_abs d, hd_abs, hck_nn]
  have hsq : (t * d) ^ 2 ≤ t ^ 2 * c (⟨k, hk⟩ : Fin m) ^ 2 := by
    nlinarith [sq_nonneg t, hd_sq]
  -- |t*d| ≤ t*c
  have habs : |t * d| ≤ t * c (⟨k, hk⟩ : Fin m) := by
    rw [abs_mul, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left hd_abs ht
  have hexp : Real.exp |t * d| ≤ Real.exp (t * c (⟨k, hk⟩ : Fin m)) :=
    Real.exp_le_exp.mpr habs
  have step1 : (t * d) ^ 2 * Real.exp |t * d|
      ≤ (t ^ 2 * c (⟨k, hk⟩ : Fin m) ^ 2) * Real.exp (t * c (⟨k, hk⟩ : Fin m)) := by
    have hXY : (t * d) ^ 2 * Real.exp |t * d|
        ≤ (t * d) ^ 2 * Real.exp (t * c (⟨k, hk⟩ : Fin m)) :=
      mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
    have hXZ : (t * d) ^ 2 * Real.exp (t * c (⟨k, hk⟩ : Fin m))
        ≤ (t ^ 2 * c (⟨k, hk⟩ : Fin m) ^ 2) * Real.exp (t * c (⟨k, hk⟩ : Fin m)) :=
      mul_le_mul_of_nonneg_right hsq (Real.exp_nonneg _)
    linarith
  calc (t * d) ^ 2 / 2 * (p * (1 - p) * Real.exp |t * d|)
      = (p * (1 - p) / 2) * ((t * d) ^ 2 * Real.exp |t * d|) := by ring
    _ ≤ (p * (1 - p) / 2) * ((t ^ 2 * c (⟨k, hk⟩ : Fin m) ^ 2)
          * Real.exp (t * c (⟨k, hk⟩ : Fin m))) :=
        mul_le_mul_of_nonneg_left step1 (by linarith)
    _ = t ^ 2 / 2 * (p * (1 - p)
          * (c (⟨k, hk⟩ : Fin m) ^ 2 * Real.exp (t * c (⟨k, hk⟩ : Fin m)))) := by ring

/-- Constants pull out of `bernoulliExp`. -/
lemma bernoulliExp_const_mul {m : ℕ} (p : ℝ) (a : ℝ) (f : (Fin m → Bool) → ℝ) :
    bernoulliExp p (fun σ => a * f σ) = a * bernoulliExp p f := by
  unfold bernoulliExp
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

/-- `bernoulliExp` is additive over a `Finset` sum. -/
lemma bernoulliExp_sum {m : ℕ} (p : ℝ) {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → (Fin m → Bool) → ℝ) :
    bernoulliExp p (fun σ => ∑ j ∈ S, f j σ)
      = ∑ j ∈ S, bernoulliExp p (f j) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact bernoulliExp_const p 0
  | insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      rw [bernoulliExp_add, ih]

/-- **`E[Φ] = p·|S|` for a count of selected trials.**

This is the expectation computation Kim performs for every property:
`E[|X' ∩ Γ(T)|] = (θ/√n)|Γ(T)|` in (38), `E[Φ_v] = p·d_Γ(v) ≤ bθ√n` in
Lemma 4.3(i), and so on. -/
lemma bernoulliExp_count {m : ℕ} (p : ℝ) (S : Finset (Fin m)) :
    bernoulliExp p (fun σ => ∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0))
      = p * S.card := by
  classical
  rw [bernoulliExp_sum]
  have hterm : ∀ j ∈ S,
      bernoulliExp p (fun σ => if σ j = true then (1 : ℝ) else 0) = p := by
    intro j _
    have h := bernoulliExp_coord p j (fun b : Bool => if b = true then (1 : ℝ) else 0)
    simpa using h
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The count functional `Φ(σ) = ∑_{j ∈ S} 1(σⱼ)` is coordinate-Lipschitz with
constants `1_{j ∈ S}`: flipping a coordinate outside `S` changes nothing, and
flipping one inside `S` changes `Φ` by at most `1`. -/
lemma count_isCoordLipschitz {m : ℕ} (S : Finset (Fin m)) :
    IsCoordLipschitz
      (fun σ : Fin m → Bool => ∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0))
      (fun j => if j ∈ S then 1 else 0) := by
  classical
  intro j τ τ' hoff
  show |(∑ i ∈ S, (if τ i = true then (1 : ℝ) else 0))
      - (∑ i ∈ S, (if τ' i = true then (1 : ℝ) else 0))|
    ≤ (if j ∈ S then (1 : ℝ) else 0)
  by_cases hjS : j ∈ S
  · rw [if_pos hjS]
    -- all terms but the `j`-th agree
    have hsplit : ∀ (ρ : Fin m → Bool),
        ∑ i ∈ S, (if ρ i = true then (1 : ℝ) else 0)
          = (if ρ j = true then (1 : ℝ) else 0)
            + ∑ i ∈ S.erase j, (if ρ i = true then (1 : ℝ) else 0) := by
      intro ρ
      rw [← Finset.add_sum_erase S _ hjS]
    rw [hsplit τ, hsplit τ']
    have hrest : ∑ i ∈ S.erase j, (if τ i = true then (1 : ℝ) else 0)
        = ∑ i ∈ S.erase j, (if τ' i = true then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hoff i (Finset.ne_of_mem_erase hi)]
    rw [hrest]
    have : (if τ j = true then (1 : ℝ) else 0)
        + ∑ i ∈ S.erase j, (if τ' i = true then (1 : ℝ) else 0)
        - ((if τ' j = true then (1 : ℝ) else 0)
        + ∑ i ∈ S.erase j, (if τ' i = true then (1 : ℝ) else 0))
        = (if τ j = true then (1 : ℝ) else 0)
          - (if τ' j = true then (1 : ℝ) else 0) := by ring
    rw [this]
    by_cases h1 : τ j = true <;> by_cases h2 : τ' j = true <;> simp [h1, h2]
  · rw [if_neg hjS]
    have hall : ∀ i ∈ S, (if τ i = true then (1 : ℝ) else 0)
        = (if τ' i = true then (1 : ℝ) else 0) := by
      intro i hi
      have hne : i ≠ j := fun hc => hjS (hc ▸ hi)
      rw [hoff i hne]
    rw [Finset.sum_congr rfl hall, sub_self, abs_zero]

/-- `∑ⱼ cⱼ²e^{t cⱼ} = |S|·e^t` for the indicator constants `cⱼ = 1_{j ∈ S}`. -/
lemma sum_indicator_sq_exp {m : ℕ} (S : Finset (Fin m)) (t : ℝ) :
    ∑ j : Fin m, (if j ∈ S then (1 : ℝ) else 0) ^ 2
        * Real.exp (t * (if j ∈ S then (1 : ℝ) else 0))
      = S.card * Real.exp t := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ S)]
  have hS : Finset.univ.filter (fun j : Fin m => j ∈ S) = S := by
    ext j; simp
  have hin : ∑ j ∈ Finset.univ.filter (fun j : Fin m => j ∈ S),
      (if j ∈ S then (1 : ℝ) else 0) ^ 2
        * Real.exp (t * (if j ∈ S then (1 : ℝ) else 0))
      = S.card * Real.exp t := by
    rw [hS]
    have hterm : ∀ j ∈ S, (if j ∈ S then (1 : ℝ) else 0) ^ 2
        * Real.exp (t * (if j ∈ S then (1 : ℝ) else 0)) = Real.exp t := by
      intro j hj; rw [if_pos hj]; norm_num
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hout : ∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬ (j ∈ S)),
      (if j ∈ S then (1 : ℝ) else 0) ^ 2
        * Real.exp (t * (if j ∈ S then (1 : ℝ) else 0)) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have : j ∉ S := (Finset.mem_filter.mp hj).2
    rw [if_neg this]; ring
  rw [hin, hout, add_zero]



/-- The Lipschitz constants re-indexed by `ℕ`, extended by `0` past `m`. -/
noncomputable def coordC {m : ℕ} (c : Fin m → ℝ) (k : ℕ) : ℝ :=
  if h : k < m then c ⟨k, h⟩ else 0

/-- The per-coordinate Kahn factor `exp(t²/2 · p(1-p) · c_k² · e^{t c_k})`. -/
noncomputable def kahnFactor {m : ℕ} (p : ℝ) (c : Fin m → ℝ) (t : ℝ) (k : ℕ) : ℝ :=
  Real.exp (t ^ 2 / 2 * (p * (1 - p)
    * (coordC c k ^ 2 * Real.exp (t * coordC c k))))

lemma kahnFactor_pos {m : ℕ} (p : ℝ) (c : Fin m → ℝ) (t : ℝ) (k : ℕ) :
    0 < kahnFactor p c t k := Real.exp_pos _

/-- Past stage `m` the Kahn factor is `1`. -/
lemma kahnFactor_of_le {m : ℕ} (p : ℝ) (c : Fin m → ℝ) (t : ℝ) {k : ℕ}
    (hk : m ≤ k) : kahnFactor p c t k = 1 := by
  unfold kahnFactor coordC
  rw [dif_neg (by omega)]
  simp

/-- **MGF product bound (induction over coordinates).** The MGF of the
partial Doob sum `Z_j − E[Φ]` is bounded by the product of the first `j`
Kahn factors. This is the finite Azuma/Kahn induction: at each step the
tower property isolates one coordinate whose conditional MGF is bounded by
`condMGF_le`. -/
lemma mgf_partial_le {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {Φ : (Fin m → Bool) → ℝ} {c : Fin m → ℝ} (h_lip : IsCoordLipschitz Φ c)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ j : ℕ,
      bernoulliExp p (fun σ =>
          Real.exp (t * (condExpFin p Φ j σ - bernoulliExp p Φ)))
        ≤ ∏ k ∈ Finset.range j, kahnFactor p c t k := by
  intro j
  induction j with
  | zero =>
      simp only [Finset.range_zero, Finset.prod_empty]
      have hz : (fun σ : Fin m → Bool =>
          Real.exp (t * (condExpFin p Φ 0 σ - bernoulliExp p Φ))) = fun _ => 1 := by
        funext σ
        rw [condExpFin_zero]
        simp
      rw [hz, bernoulliExp_const]
  | succ j ih =>
      rw [Finset.prod_range_succ]
      -- Split the exponential at stage j.
      have hsplit : ∀ σ : Fin m → Bool,
          Real.exp (t * (condExpFin p Φ (j + 1) σ - bernoulliExp p Φ))
            = Real.exp (t * (condExpFin p Φ j σ - bernoulliExp p Φ))
              * Real.exp (t * incFin p Φ j σ) := by
        intro σ
        rw [← Real.exp_add]
        congr 1
        unfold incFin
        ring
      -- Apply the tower at stage j.
      have htow := bernoulliExp_condExpFin p j
        (fun σ => Real.exp (t * (condExpFin p Φ (j + 1) σ - bernoulliExp p Φ)))
      rw [← htow]
      -- Inside the conditional expectation, the stage-j factor is constant.
      have hinner : ∀ σ : Fin m → Bool,
          condExpFin p
              (fun σ' => Real.exp (t * (condExpFin p Φ (j + 1) σ' - bernoulliExp p Φ))) j σ
            = Real.exp (t * (condExpFin p Φ j σ - bernoulliExp p Φ))
              * bernoulliExp p (fun ρ => Real.exp (t * incFin p Φ j (mergeAt j σ ρ))) := by
        intro σ
        show bernoulliExp p (fun ρ =>
            Real.exp (t * (condExpFin p Φ (j + 1) (mergeAt j σ ρ) - bernoulliExp p Φ))) = _
        have hre : (fun ρ : Fin m → Bool =>
            Real.exp (t * (condExpFin p Φ (j + 1) (mergeAt j σ ρ) - bernoulliExp p Φ)))
            = fun ρ => Real.exp (t * (condExpFin p Φ j σ - bernoulliExp p Φ))
                * Real.exp (t * incFin p Φ j (mergeAt j σ ρ)) := by
          funext ρ
          rw [hsplit (mergeAt j σ ρ), condExpFin_mergeAt p Φ j σ ρ]
        rw [hre, bernoulliExp_const_mul]
      -- Bound each conditional factor.
      have hbound : ∀ σ : Fin m → Bool,
          condExpFin p
              (fun σ' => Real.exp (t * (condExpFin p Φ (j + 1) σ' - bernoulliExp p Φ))) j σ
            ≤ Real.exp (t * (condExpFin p Φ j σ - bernoulliExp p Φ)) * kahnFactor p c t j := by
        intro σ
        rw [hinner σ]
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
        by_cases hj : j < m
        · have := condMGF_le hp₀ hp₁ h_lip hj σ ht
          unfold kahnFactor coordC
          rw [dif_pos hj]
          exact this
        · -- Past stage m the increments vanish and the factor is 1.
          have hzero : ∀ ρ : Fin m → Bool,
              Real.exp (t * incFin p Φ j (mergeAt j σ ρ)) = 1 := by
            intro ρ
            rw [incFin_of_le (by omega) p Φ (mergeAt j σ ρ)]
            simp
          have hfun : (fun ρ : Fin m → Bool =>
              Real.exp (t * incFin p Φ j (mergeAt j σ ρ))) = fun _ => 1 := by
            funext ρ; exact hzero ρ
          rw [hfun, bernoulliExp_const, kahnFactor_of_le p c t (by omega)]
      -- Integrate the pointwise bound.
      calc bernoulliExp p (fun σ => condExpFin p
              (fun σ' => Real.exp (t * (condExpFin p Φ (j + 1) σ' - bernoulliExp p Φ))) j σ)
          ≤ bernoulliExp p (fun σ =>
              Real.exp (t * (condExpFin p Φ j σ - bernoulliExp p Φ))
                * kahnFactor p c t j) := bernoulliExp_mono hp₀ hp₁ hbound
        _ = bernoulliExp p (fun σ =>
              kahnFactor p c t j
                * Real.exp (t * (condExpFin p Φ j σ - bernoulliExp p Φ))) := by
              unfold bernoulliExp
              exact Finset.sum_congr rfl fun σ _ => by ring
        _ = kahnFactor p c t j * bernoulliExp p (fun σ =>
              Real.exp (t * (condExpFin p Φ j σ - bernoulliExp p Φ))) :=
              bernoulliExp_const_mul _ _ _
        _ ≤ kahnFactor p c t j * ∏ k ∈ Finset.range j, kahnFactor p c t k :=
              mul_le_mul_of_nonneg_left ih (le_of_lt (kahnFactor_pos p c t j))
        _ = (∏ k ∈ Finset.range j, kahnFactor p c t k) * kahnFactor p c t j := by ring

lemma coordC_coe {m : ℕ} (c : Fin m → ℝ) (j : Fin m) :
    coordC c (j : ℕ) = c j := by
  unfold coordC
  rw [dif_pos j.isLt]

/-- The product of Kahn factors, written as a single exponential of the
Kahn exponent `t²/2 · p(1-p) · ∑ⱼ cⱼ²e^{tcⱼ}`. -/
lemma prod_kahnFactor {m : ℕ} (p : ℝ) (c : Fin m → ℝ) (t : ℝ) :
    ∏ k ∈ Finset.range m, kahnFactor p c t k
      = Real.exp (t ^ 2 / 2 * (p * (1 - p)
          * ∑ j : Fin m, c j ^ 2 * Real.exp (t * c j))) := by
  unfold kahnFactor
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => t ^ 2 / 2 * (p * (1 - p)
      * (coordC c k ^ 2 * Real.exp (t * coordC c k)))) m]
  exact Finset.sum_congr rfl fun j _ => by rw [coordC_coe]

/-- **Full MGF bound**: at stage `m` the conditional expectation is `Φ`
itself, so the Kahn product bounds the MGF of `Φ − E[Φ]`. -/
lemma mgf_full_le {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {Φ : (Fin m → Bool) → ℝ} {c : Fin m → ℝ} (h_lip : IsCoordLipschitz Φ c)
    {t : ℝ} (ht : 0 ≤ t) :
    bernoulliExp p (fun σ => Real.exp (t * (Φ σ - bernoulliExp p Φ)))
      ≤ Real.exp (t ^ 2 / 2 * (p * (1 - p)
          * ∑ j : Fin m, c j ^ 2 * Real.exp (t * c j))) := by
  have h := mgf_partial_le hp₀ hp₁ h_lip ht m
  have heq : (fun σ : Fin m → Bool =>
      Real.exp (t * (condExpFin p Φ m σ - bernoulliExp p Φ)))
      = fun σ => Real.exp (t * (Φ σ - bernoulliExp p Φ)) := by
    funext σ; rw [condExpFin_of_le (le_refl m)]
  rw [heq] at h
  rwa [prod_kahnFactor] at h

/-- Probability of a finite event under the product Bernoulli measure. -/
noncomputable def bernoulliPr {m : ℕ} (p : ℝ) (S : Finset (Fin m → Bool)) : ℝ :=
  ∑ σ ∈ S, bernoulliWeight p σ

/-- **Markov's inequality** on the finite Bernoulli space. -/
lemma bernoulliPr_mul_le {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (g : (Fin m → Bool) → ℝ) (hg : ∀ σ, 0 ≤ g σ) {a : ℝ}
    (S : Finset (Fin m → Bool)) (hS : ∀ σ ∈ S, a ≤ g σ) :
    bernoulliPr p S * a ≤ bernoulliExp p g := by
  classical
  unfold bernoulliPr bernoulliExp
  rw [Finset.sum_mul]
  have h1 : ∑ σ ∈ S, bernoulliWeight p σ * a
      ≤ ∑ σ ∈ S, bernoulliWeight p σ * g σ := by
    refine Finset.sum_le_sum fun σ hσ => ?_
    exact mul_le_mul_of_nonneg_left (hS σ hσ) (bernoulliWeight_nonneg hp₀ hp₁ σ)
  have h2 : ∑ σ ∈ S, bernoulliWeight p σ * g σ
      ≤ ∑ σ : Fin m → Bool, bernoulliWeight p σ * g σ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) ?_
    intro σ _ _
    exact mul_nonneg (bernoulliWeight_nonneg hp₀ hp₁ σ) (hg σ)
  linarith

/-- **Upper-tail bound (Chernoff) on the finite Bernoulli space.** -/
lemma bernoulliPr_upper_tail {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {Φ : (Fin m → Bool) → ℝ} {c : Fin m → ℝ} (h_lip : IsCoordLipschitz Φ c)
    {t lam : ℝ} (ht : 0 ≤ t) :
    bernoulliPr p (Finset.univ.filter
        (fun σ => lam ≤ Φ σ - bernoulliExp p Φ))
      ≤ Real.exp (-t * lam + t ^ 2 / 2 * (p * (1 - p)
          * ∑ j : Fin m, c j ^ 2 * Real.exp (t * c j))) := by
  classical
  set g : (Fin m → Bool) → ℝ :=
    fun σ => Real.exp (t * (Φ σ - bernoulliExp p Φ)) with hg_def
  set S : Finset (Fin m → Bool) :=
    Finset.univ.filter (fun σ => lam ≤ Φ σ - bernoulliExp p Φ) with hS_def
  have hS_bound : ∀ σ ∈ S, Real.exp (t * lam) ≤ g σ := by
    intro σ hσ
    rw [hS_def, Finset.mem_filter] at hσ
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ.2 ht)
  have hmarkov := bernoulliPr_mul_le hp₀ hp₁ g (fun _ => Real.exp_nonneg _) S hS_bound
  have hmgf := mgf_full_le hp₀ hp₁ h_lip ht
  have hchain : bernoulliPr p S * Real.exp (t * lam)
      ≤ Real.exp (t ^ 2 / 2 * (p * (1 - p)
          * ∑ j : Fin m, c j ^ 2 * Real.exp (t * c j))) := le_trans hmarkov hmgf
  have hpos : (0 : ℝ) < Real.exp (t * lam) := Real.exp_pos _
  rw [← le_div_iff₀ hpos] at hchain
  refine hchain.trans (le_of_eq ?_)
  rw [← Real.exp_sub]
  congr 1
  ring

/-- Negating a coordinate-Lipschitz functional preserves the constants. -/
lemma IsCoordLipschitz.neg {m : ℕ} {Φ : (Fin m → Bool) → ℝ} {c : Fin m → ℝ}
    (h : IsCoordLipschitz Φ c) : IsCoordLipschitz (fun σ => -Φ σ) c := by
  intro j τ τ' hoff
  have hb := h j τ τ' hoff
  have : -Φ τ - -Φ τ' = -(Φ τ - Φ τ') := by ring
  rw [this, abs_neg]
  exact hb

lemma bernoulliExp_neg {m : ℕ} (p : ℝ) (f : (Fin m → Bool) → ℝ) :
    bernoulliExp p (fun σ => -f σ) = -bernoulliExp p f := by
  unfold bernoulliExp
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun σ _ => by ring

/-- Subadditivity of `bernoulliPr` along a union. -/
lemma bernoulliPr_union_le {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (A B : Finset (Fin m → Bool)) :
    bernoulliPr p (A ∪ B) ≤ bernoulliPr p A + bernoulliPr p B := by
  classical
  unfold bernoulliPr
  have hui := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := bernoulliWeight p)
  have hinter_nn : 0 ≤ ∑ σ ∈ A ∩ B, bernoulliWeight p σ :=
    Finset.sum_nonneg fun σ _ => bernoulliWeight_nonneg hp₀ hp₁ σ
  linarith

lemma bernoulliPr_mono {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {A B : Finset (Fin m → Bool)} (h : A ⊆ B) :
    bernoulliPr p A ≤ bernoulliPr p B := by
  unfold bernoulliPr
  exact Finset.sum_le_sum_of_subset_of_nonneg h
    fun σ _ _ => bernoulliWeight_nonneg hp₀ hp₁ σ

/-- Total mass one, in `bernoulliPr` form. -/
lemma bernoulliPr_univ {m : ℕ} (p : ℝ) :
    bernoulliPr p (Finset.univ : Finset (Fin m → Bool)) = 1 :=
  sum_bernoulliWeight p

lemma bernoulliPr_nonneg {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (S : Finset (Fin m → Bool)) : 0 ≤ bernoulliPr p S :=
  Finset.sum_nonneg fun σ _ => bernoulliWeight_nonneg hp₀ hp₁ σ

@[simp] lemma bernoulliPr_empty {m : ℕ} (p : ℝ) :
    bernoulliPr p (∅ : Finset (Fin m → Bool)) = 0 := by
  simp [bernoulliPr]

/-- **Coordinate product formula.** Under the product Bernoulli(`p`) measure the
coordinates are independent, so the expectation of a product of one-coordinate
functions factorises. -/
lemma bernoulliExp_prod_coord {m : ℕ} (p : ℝ) (f : Fin m → Bool → ℝ) :
    bernoulliExp p (fun σ => ∏ j, f j (σ j))
      = ∏ j, (p * f j true + (1 - p) * f j false) := by
  classical
  have hfac : ∀ j : Fin m, p * f j true + (1 - p) * f j false
      = ∑ b : Bool, (if b = true then p else 1 - p) * f j b := by
    intro j; simp [Fintype.sum_bool]
  simp only [hfac]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  unfold bernoulliExp bernoulliWeight
  exact Finset.sum_congr rfl fun x _ => (Finset.prod_mul_distrib).symm

/-- Probability as an expectation of an indicator. -/
lemma bernoulliPr_eq_exp {m : ℕ} (p : ℝ) (S : Finset (Fin m → Bool)) :
    bernoulliPr p S = bernoulliExp p (fun σ => if σ ∈ S then (1 : ℝ) else 0) := by
  classical
  unfold bernoulliPr bernoulliExp
  have hpt : ∀ σ : Fin m → Bool,
      bernoulliWeight p σ * (if σ ∈ S then (1 : ℝ) else 0)
        = if σ ∈ S then bernoulliWeight p σ else 0 := fun σ => by
    by_cases h : σ ∈ S <;> simp [h]
  simp only [hpt]
  rw [← Finset.sum_filter]
  exact (Finset.sum_congr (by ext σ; simp) fun _ _ => rfl).symm

/-- **All-present probability**: the chance that every coordinate in `T` is
`true` is exactly `p^{|T|}`. This is the first-moment input for Kim's
Lemma 4.3(iii) and for the expected size of `𝒯'` in (55). -/
theorem bernoulliPr_all_true {m : ℕ} (p : ℝ) (T : Finset (Fin m)) :
    bernoulliPr p (Finset.univ.filter (fun σ => ∀ j ∈ T, σ j = true))
      = p ^ T.card := by
  classical
  set f : Fin m → Bool → ℝ :=
    fun j b => if j ∈ T then (if b = true then (1 : ℝ) else 0) else 1 with hf
  have hind : ∀ σ : Fin m → Bool,
      (if σ ∈ Finset.univ.filter (fun σ : Fin m → Bool => ∀ j ∈ T, σ j = true)
        then (1 : ℝ) else 0) = ∏ j, f j (σ j) := by
    intro σ
    by_cases h : ∀ j ∈ T, σ j = true
    · rw [if_pos (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)]
      refine (Finset.prod_eq_one fun j _ => ?_).symm
      by_cases hjT : j ∈ T
      · simp [hf, hjT, h j hjT]
      · simp [hf, hjT]
    · rw [if_neg (fun hc => h (Finset.mem_filter.mp hc).2)]
      push_neg at h
      obtain ⟨j, hjT, hj⟩ := h
      refine (Finset.prod_eq_zero (Finset.mem_univ j) ?_).symm
      simp [hf, hjT, hj]
  rw [bernoulliPr_eq_exp, funext hind, bernoulliExp_prod_coord]
  have hval : ∀ j : Fin m,
      p * f j true + (1 - p) * f j false = if j ∈ T then p else 1 := by
    intro j
    by_cases hjT : j ∈ T <;> simp [hf, hjT]
  simp only [hval]
  rw [← Finset.prod_filter,
    show (Finset.univ.filter (fun j : Fin m => j ∈ T)) = T from by ext j; simp]
  exact Finset.prod_const p

/-- **All-absent probability**: the chance that no coordinate in `T` is `true`
is exactly `(1−p)^{|T|}`. This is the exact computation behind Kim's
Lemma 4.1, `Pr(e ∉ Y') = (1−p)^{d_{Λ*}(e)}`. -/
theorem bernoulliPr_all_false {m : ℕ} (p : ℝ) (T : Finset (Fin m)) :
    bernoulliPr p (Finset.univ.filter (fun σ => ∀ j ∈ T, σ j = false))
      = (1 - p) ^ T.card := by
  classical
  set f : Fin m → Bool → ℝ :=
    fun j b => if j ∈ T then (if b = true then (0 : ℝ) else 1) else 1 with hf
  have hind : ∀ σ : Fin m → Bool,
      (if σ ∈ Finset.univ.filter (fun σ : Fin m → Bool => ∀ j ∈ T, σ j = false)
        then (1 : ℝ) else 0) = ∏ j, f j (σ j) := by
    intro σ
    by_cases h : ∀ j ∈ T, σ j = false
    · rw [if_pos (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)]
      refine (Finset.prod_eq_one fun j _ => ?_).symm
      by_cases hjT : j ∈ T
      · simp [hf, hjT, h j hjT]
      · simp [hf, hjT]
    · rw [if_neg (fun hc => h (Finset.mem_filter.mp hc).2)]
      push_neg at h
      obtain ⟨j, hjT, hj⟩ := h
      refine (Finset.prod_eq_zero (Finset.mem_univ j) ?_).symm
      have hjt : σ j = true := by revert hj; cases σ j <;> simp
      simp [hf, hjT, hjt]
  rw [bernoulliPr_eq_exp, funext hind, bernoulliExp_prod_coord]
  have hval : ∀ j : Fin m,
      p * f j true + (1 - p) * f j false = if j ∈ T then 1 - p else 1 := by
    intro j
    by_cases hjT : j ∈ T <;> simp [hf, hjT]
  simp only [hval]
  rw [← Finset.prod_filter,
    show (Finset.univ.filter (fun j : Fin m => j ∈ T)) = T from by ext j; simp]
  exact Finset.prod_const (1 - p)

open scoped Classical in
/-- **Exact MGF of a coordinate count.** Since the coordinates are independent
Bernoulli(`p`),

`E[exp(ρ·Σ_{j∈S} 1(σ_j))] = ((1−p) + p·e^ρ)^{|S|}`.

This is Kim's `E[exp(ρΦ_T)] = ∏_{e∈Γ(T)}(1 − p(1 − e^ρ))` in §4.9, and unlike
the Chernoff bounds it is an identity — which is what (58) needs, since there
`ρ < 0`. -/
theorem bernoulliExp_exp_count {m : ℕ} (p ρ : ℝ) (S : Finset (Fin m)) :
    bernoulliExp p (fun σ =>
        Real.exp (ρ * ∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0)))
      = ((1 - p) + p * Real.exp ρ) ^ S.card := by
  classical
  set f : Fin m → Bool → ℝ := fun j b =>
    if j ∈ S then (if b = true then Real.exp ρ else 1) else 1 with hf
  have hpt : ∀ σ : Fin m → Bool,
      Real.exp (ρ * ∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0))
        = ∏ j, f j (σ j) := by
    intro σ
    rw [Finset.mul_sum, Real.exp_sum]
    rw [show (∏ j, f j (σ j)) = ∏ j ∈ S, f j (σ j) from
      (Finset.prod_subset (Finset.subset_univ S)
        (fun j _ hjS => by simp [hf, hjS])).symm]
    refine Finset.prod_congr rfl fun j hj => ?_
    by_cases hσ : σ j = true
    · simp [hf, hj, hσ]
    · simp [hf, hj, hσ]
  rw [funext hpt, bernoulliExp_prod_coord]
  have hval : ∀ j : Fin m, p * f j true + (1 - p) * f j false
      = if j ∈ S then (1 - p) + p * Real.exp ρ else 1 := by
    intro j
    by_cases hj : j ∈ S <;> simp [hf, hj] <;> ring
  simp only [hval]
  rw [← Finset.prod_filter,
    show (Finset.univ.filter (fun j : Fin m => j ∈ S)) = S from by ext j; simp]
  exact Finset.prod_const _

open scoped Classical in
/-- **Kim's (58), Markov step.** For `ρ < 0`, exponentiating turns a lower tail
into an upper tail, and the exact MGF gives the bound. -/
theorem bernoulliPr_count_le_mgf {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (S : Finset (Fin m)) {ρ c : ℝ} (hρ : ρ < 0) :
    bernoulliPr p (Finset.univ.filter (fun σ =>
        (∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0)) ≤ c))
      ≤ ((1 - p) + p * Real.exp ρ) ^ S.card / Real.exp (ρ * c) := by
  classical
  set g : (Fin m → Bool) → ℝ := fun σ =>
    Real.exp (ρ * ∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0)) with hg
  set B : Finset (Fin m → Bool) := Finset.univ.filter (fun σ =>
    (∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0)) ≤ c) with hB
  have hlow : ∀ σ ∈ B, Real.exp (ρ * c) ≤ g σ := by
    intro σ hσ
    obtain ⟨-, hle⟩ := Finset.mem_filter.mp hσ
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hmarkov := bernoulliPr_mul_le hp₀ hp₁ g (fun _ => Real.exp_nonneg _) B hlow
  rw [hg, bernoulliExp_exp_count] at hmarkov
  rw [le_div_iff₀ (Real.exp_pos _)]
  exact hmarkov

/-- The first two terms of the binomial expansion. -/
lemma pow_add_two_terms_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (nn : ℕ) :
    b ^ (nn + 1) + (nn + 1) * a * b ^ nn ≤ (a + b) ^ (nn + 1) := by
  induction nn with
  | zero => simp; linarith
  | succ m ih =>
      have hab : (0 : ℝ) ≤ a + b := by linarith
      have hbm : (0 : ℝ) ≤ b ^ m := pow_nonneg hb m
      have hstep : (a + b) ^ (m + 2) = (a + b) * (a + b) ^ (m + 1) := by ring
      rw [hstep]
      have h1 : (a + b) * (b ^ (m + 1) + (m + 1) * a * b ^ m)
          ≤ (a + b) * (a + b) ^ (m + 1) :=
        mul_le_mul_of_nonneg_left ih hab
      refine le_trans ?_ h1
      have hbm1 : (0 : ℝ) ≤ b ^ (m + 1) := pow_nonneg hb (m + 1)
      have hexp : (a + b) * (b ^ (m + 1) + (m + 1) * a * b ^ m)
          = b ^ (m + 2) + ((m : ℝ) + 2) * a * b ^ (m + 1)
            + ((m : ℝ) + 1) * a ^ 2 * b ^ m := by ring
      rw [hexp]
      have hpos : (0 : ℝ) ≤ ((m : ℝ) + 1) * a ^ 2 * b ^ m := by positivity
      push_cast
      linarith

/-- **`l!·e_l(q) ≤ (Σ q)^l`** for nonnegative weights: the elementary
symmetric polynomial of degree `l` is dominated by `(Σ q)^l / l!`.

This is the combinatorial heart of Kim's (59): a union bound over *disjoint*
`l`-collections of forbidden configurations produces the elementary symmetric
polynomial, and the `1/l!` it carries is exactly what makes the bound
`(ηe/l)^l` small. -/
lemma factorial_mul_esymm_le {ι : Type*} [DecidableEq ι] (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (H : Finset ι) (l : ℕ) :
    (l.factorial : ℝ) * ∑ C ∈ H.powersetCard l, ∏ F ∈ C, q F
      ≤ (∑ F ∈ H, q F) ^ l := by
  classical
  induction H using Finset.induction_on generalizing l with
  | empty =>
      cases l with
      | zero => simp
      | succ m =>
          rw [show ((∅ : Finset ι).powersetCard (m + 1)) = ∅ from
            Finset.powersetCard_eq_empty.mpr (by simp)]
          simp
  | insert x s hx ih =>
      cases l with
      | zero => simp
      | succ m =>
          have hSs : (0 : ℝ) ≤ ∑ F ∈ s, q F :=
            Finset.sum_nonneg fun i _ => hq i
          -- split the `(m+1)`-subsets by whether they contain `x`
          have hdisj : Disjoint (s.powersetCard (m + 1))
              ((s.powersetCard m).image (insert x)) := by
            rw [Finset.disjoint_right]
            intro C hC hC'
            obtain ⟨C', hC', rfl⟩ := Finset.mem_image.mp hC
            exact hx ((Finset.mem_powersetCard.mp hC').1
              (Finset.mem_insert_self x C'))
          have hsplit : ∑ C ∈ (insert x s).powersetCard (m + 1), ∏ F ∈ C, q F
              = (∑ C ∈ s.powersetCard (m + 1), ∏ F ∈ C, q F)
                + q x * ∑ C ∈ s.powersetCard m, ∏ F ∈ C, q F := by
            rw [Finset.powersetCard_succ_insert hx, Finset.sum_union hdisj]
            congr 1
            rw [Finset.sum_image, Finset.mul_sum]
            · refine Finset.sum_congr rfl fun C hC => ?_
              have hxC : x ∉ C := fun h =>
                hx ((Finset.mem_powersetCard.mp hC).1 h)
              rw [Finset.prod_insert hxC]
            · intro C hC C' hC' hEq
              have hxC : x ∉ C := fun h =>
                hx ((Finset.mem_powersetCard.mp hC).1 h)
              have hxC' : x ∉ C' := fun h =>
                hx ((Finset.mem_powersetCard.mp hC').1 h)
              rw [← Finset.erase_insert hxC, ← Finset.erase_insert hxC', hEq]
          rw [hsplit, Finset.sum_insert hx]
          have hIH1 := ih (l := m + 1)
          have hIH2 := ih (l := m)
          have hfac : ((m + 1).factorial : ℝ)
              = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
            rw [Nat.factorial_succ]; push_cast; ring
          have hfacpos : (0 : ℝ) ≤ (m.factorial : ℝ) := by positivity
          have hkey : ((m + 1).factorial : ℝ)
              * ((∑ C ∈ s.powersetCard (m + 1), ∏ F ∈ C, q F)
                + q x * ∑ C ∈ s.powersetCard m, ∏ F ∈ C, q F)
              ≤ (∑ F ∈ s, q F) ^ (m + 1)
                + ((m : ℝ) + 1) * q x * (∑ F ∈ s, q F) ^ m := by
            rw [hfac]
            have h1 : ((m : ℝ) + 1) * ((m.factorial : ℝ)
                * ∑ C ∈ s.powersetCard (m + 1), ∏ F ∈ C, q F)
                ≤ ((m : ℝ) + 1) * ((∑ F ∈ s, q F) ^ (m + 1)
                  / ((m : ℝ) + 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              rw [le_div_iff₀ (by positivity)]
              calc (m.factorial : ℝ)
                    * (∑ C ∈ s.powersetCard (m + 1), ∏ F ∈ C, q F)
                      * ((m : ℝ) + 1)
                  = ((m + 1).factorial : ℝ)
                    * ∑ C ∈ s.powersetCard (m + 1), ∏ F ∈ C, q F := by
                      rw [hfac]; ring
                _ ≤ (∑ F ∈ s, q F) ^ (m + 1) := hIH1
            have h2 : ((m : ℝ) + 1) * (m.factorial : ℝ)
                * (q x * ∑ C ∈ s.powersetCard m, ∏ F ∈ C, q F)
                ≤ ((m : ℝ) + 1) * q x * (∑ F ∈ s, q F) ^ m := by
              have := mul_le_mul_of_nonneg_left hIH2
                (mul_nonneg (by positivity : (0:ℝ) ≤ (m : ℝ) + 1) (hq x))
              nlinarith [this, hq x, hIH2, hfacpos]
            have hdiv : ((m : ℝ) + 1) * ((∑ F ∈ s, q F) ^ (m + 1)
                / ((m : ℝ) + 1)) = (∑ F ∈ s, q F) ^ (m + 1) := by
              field_simp
            nlinarith [h1, h2, hdiv]
          refine le_trans hkey ?_
          exact pow_add_two_terms_le (hq x) hSs m


/-- **Expected number of survivors.** If every event `Ev i` has probability at
most `q`, the expected number of `i ∈ S` whose event occurs is at most `q|S|`.
This is Kim's `E[Φ_v] = Σ_{e ∈ N_Γ(v)} Pr(e ∉ Y') ≤ Pr·d_Γ(v)` in §4.3, and
the same computation drives §4.5–§4.7. -/
lemma bernoulliExp_count_le {m : ℕ} {p q : ℝ} {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (Ev : ι → Finset (Fin m → Bool))
    (hq : ∀ i ∈ S, bernoulliPr p (Ev i) ≤ q) :
    bernoulliExp p (fun σ => ∑ i ∈ S, (if σ ∈ Ev i then (1 : ℝ) else 0))
      ≤ q * S.card := by
  rw [bernoulliExp_sum]
  calc ∑ i ∈ S, bernoulliExp p (fun σ => if σ ∈ Ev i then (1 : ℝ) else 0)
      = ∑ i ∈ S, bernoulliPr p (Ev i) :=
        Finset.sum_congr rfl fun i _ => (bernoulliPr_eq_exp p (Ev i)).symm
    _ ≤ ∑ _i ∈ S, q := Finset.sum_le_sum hq
    _ = q * S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]


/-- Finite subadditivity of `bernoulliPr`. -/
lemma bernoulliPr_biUnion_le {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (Bad : ι → Finset (Fin m → Bool)) :
    bernoulliPr p (s.biUnion Bad) ≤ ∑ i ∈ s, bernoulliPr p (Bad i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bernoulliPr]
  | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      have h := bernoulliPr_union_le hp₀ hp₁ (Bad a) (s.biUnion Bad)
      linarith

/-- **Kim's §4.9 Markov step.** If `E[Φ] ≤ M` and every point of the bad event
`S` has `Φ ≥ N·M`, then `Pr(S) ≤ 1/N`.

Kim uses this with `Φ = |𝒯'|`, `M = nᵏ(n choose t)exp(…)` from (55), and
`N = n`, giving `Pr(|𝒯'| ≥ n^{k+1}(n choose t)exp(…)) ≤ 1/n`. -/
lemma bernoulliPr_markov {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (Φ : (Fin m → Bool) → ℝ) (hΦ : ∀ σ, 0 ≤ Φ σ)
    {M N : ℝ} (hN : 0 < N) (hM : 0 < M)
    (hE : bernoulliExp p Φ ≤ M)
    (S : Finset (Fin m → Bool)) (hS : ∀ σ ∈ S, N * M ≤ Φ σ) :
    bernoulliPr p S ≤ 1 / N := by
  have hNM : 0 < N * M := mul_pos hN hM
  have hmark := bernoulliPr_mul_le hp₀ hp₁ Φ hΦ S hS
  have hchain : bernoulliPr p S * (N * M) ≤ M := le_trans hmark hE
  rw [le_div_iff₀ hN]
  nlinarith [hchain, hNM, hM, hN]

/-- **Kahn's concentration inequality on the finite Bernoulli space.**
This is Kim 1995 Lemma 3.1 in its canonical-space form, with the sharp
Bennett constant `p(1-p)`. -/
theorem bernoulliPr_kahn {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {Φ : (Fin m → Bool) → ℝ} {c : Fin m → ℝ} (h_lip : IsCoordLipschitz Φ c)
    {t lam : ℝ} (ht : 0 ≤ t) :
    bernoulliPr p (Finset.univ.filter
        (fun σ => lam ≤ |Φ σ - bernoulliExp p Φ|))
      ≤ 2 * Real.exp (-t * lam + t ^ 2 / 2 * (p * (1 - p)
          * ∑ j : Fin m, c j ^ 2 * Real.exp (t * c j))) := by
  classical
  have hup := bernoulliPr_upper_tail hp₀ hp₁ h_lip (t := t) (lam := lam) ht
  have hdown := bernoulliPr_upper_tail hp₀ hp₁ h_lip.neg (t := t) (lam := lam) ht
  rw [bernoulliExp_neg] at hdown
  set A : Finset (Fin m → Bool) :=
    Finset.univ.filter (fun σ => lam ≤ Φ σ - bernoulliExp p Φ) with hA_def
  set B : Finset (Fin m → Bool) :=
    Finset.univ.filter (fun σ => lam ≤ -Φ σ - -bernoulliExp p Φ) with hB_def
  have hsub : (Finset.univ.filter
      (fun σ => lam ≤ |Φ σ - bernoulliExp p Φ|)) ⊆ A ∪ B := by
    intro σ hσ
    obtain ⟨-, hσ2⟩ := Finset.mem_filter.mp hσ
    rw [Finset.mem_union, hA_def, hB_def, Finset.mem_filter, Finset.mem_filter]
    by_cases h : 0 ≤ Φ σ - bernoulliExp p Φ
    · left
      refine ⟨Finset.mem_univ _, ?_⟩
      rwa [abs_of_nonneg h] at hσ2
    · right
      push_neg at h
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [abs_of_neg h] at hσ2
      linarith
  calc bernoulliPr p (Finset.univ.filter
        (fun σ => lam ≤ |Φ σ - bernoulliExp p Φ|))
      ≤ bernoulliPr p (A ∪ B) := bernoulliPr_mono hp₀ hp₁ hsub
    _ ≤ bernoulliPr p A + bernoulliPr p B := bernoulliPr_union_le hp₀ hp₁ A B
    _ ≤ 2 * Real.exp (-t * lam + t ^ 2 / 2 * (p * (1 - p)
          * ∑ j : Fin m, c j ^ 2 * Real.exp (t * c j))) := by linarith

/-! ### Freezing one coordinate to `false`

Kim's §4.5 estimate for `Φ⁽¹⁾` is stated *conditioned on* `e_vw ∉ X′`: he lets
`c_e := |N_Λ(e_vw,v) ∩ N_{Λ*}(e)|` only **for `e ≠ e_vw`**. Without that
restriction the single coordinate of `e_vw` has influence `M ≈ √n` — it kills
every `f ∈ N_Λ(e_vw,v)` at once — and the Bennett factor `exp(ρ c)` of
Lemma 3.1 would be `exp(n^{1/4})`.

We realise the conditioning by composing with `Function.update · j₀ false`.
This kills the `j₀` Lipschitz constant outright and costs only a factor
`(1−p)⁻¹` in the mean, which is exactly Kim's `(1+2p)` in (25). -/

/-- Turning coordinate `j₀` on multiplies the Bernoulli weight by `p/(1−p)`. -/
lemma bernoulliWeight_update_true {m : ℕ} (p : ℝ) (j₀ : Fin m)
    (σ : Fin m → Bool) (hσ : σ j₀ = false) :
    bernoulliWeight p (Function.update σ j₀ true) * (1 - p)
      = bernoulliWeight p σ * p := by
  classical
  have h1 : bernoulliWeight p (Function.update σ j₀ true)
      = p * ∏ x ∈ Finset.univ \ {j₀}, (if σ x = true then p else 1 - p) := by
    unfold bernoulliWeight
    rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ j₀)]
    congr 1
    · simp
    · refine Finset.prod_congr rfl (fun x hx => ?_)
      have hxne : x ≠ j₀ := by
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hx; exact hx.2
      simp [Function.update_apply, hxne]
  have h2 : bernoulliWeight p σ
      = (1 - p) * ∏ x ∈ Finset.univ \ {j₀}, (if σ x = true then p else 1 - p) := by
    unfold bernoulliWeight
    rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ j₀)]
    congr 1
    simp [hσ]
  rw [h1, h2]; ring

/-- **The cost of freezing a coordinate is `(1−p)⁻¹` in the mean.**
For nonnegative `Φ`, `(1−p)·E[Φ ∘ freeze] ≤ E[Φ]` — the conditional
expectation given `σ_{j₀} = false` is at most `E[Φ]/(1−p)`. -/
lemma bernoulliExp_freeze_le {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (j₀ : Fin m) (Φ : (Fin m → Bool) → ℝ) (hΦ : ∀ σ, 0 ≤ Φ σ) :
    (1 - p) * bernoulliExp p (fun σ => Φ (Function.update σ j₀ false))
      ≤ bernoulliExp p Φ := by
  classical
  set A : Finset (Fin m → Bool) :=
    Finset.univ.filter (fun σ : Fin m → Bool => σ j₀ = false) with hA
  set T : Finset (Fin m → Bool) :=
    Finset.univ.filter (fun σ : Fin m → Bool => σ j₀ = true) with hT
  have hmemA : ∀ σ : Fin m → Bool, σ ∈ A ↔ σ j₀ = false := by
    intro σ; rw [hA]; simp
  have hmemT : ∀ σ : Fin m → Bool, σ ∈ T ↔ σ j₀ = true := by
    intro σ; rw [hT]; simp
  have hnot : Finset.univ.filter (fun σ : Fin m → Bool => ¬ σ j₀ = true) = A := by
    rw [hA]; ext σ; simp [Bool.not_eq_true]
  -- split any sum along the value of coordinate `j₀`
  have hsplit : ∀ F : (Fin m → Bool) → ℝ,
      ∑ σ : Fin m → Bool, F σ = (∑ σ ∈ T, F σ) + ∑ σ ∈ A, F σ := by
    intro F
    rw [hT, ← hnot]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun σ : Fin m → Bool => σ j₀ = true) F).symm
  -- `A` maps bijectively onto `T` by turning `j₀` on
  have hAT : A.image (fun σ : Fin m → Bool => Function.update σ j₀ true) = T := by
    ext τ
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨σ, -, rfl⟩; rw [hmemT]; simp
    · intro hτ
      rw [hmemT] at hτ
      refine ⟨Function.update τ j₀ false, (hmemA _).mpr (by simp), ?_⟩
      funext x
      by_cases hx : x = j₀
      · subst hx; simp [hτ]
      · simp [Function.update_apply, hx]
  have hinj : ∀ x ∈ A, ∀ y ∈ A,
      Function.update x j₀ true = Function.update y j₀ true → x = y := by
    intro x hx y hy hxy
    have hx0 := (hmemA x).mp hx
    have hy0 := (hmemA y).mp hy
    funext z
    by_cases hz : z = j₀
    · subst hz; rw [hx0, hy0]
    · have := congrFun hxy z
      simpa [Function.update_apply, hz] using this
  -- the frozen mean, rewritten as a sum over `A`
  have hTsum : ∑ τ ∈ T, bernoulliWeight p τ * Φ (Function.update τ j₀ false)
      = ∑ σ ∈ A, bernoulliWeight p (Function.update σ j₀ true) * Φ σ := by
    rw [← hAT, Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun σ hσ => ?_)
    have hσ0 := (hmemA σ).mp hσ
    have : Function.update (Function.update σ j₀ true) j₀ false = σ := by
      funext x
      by_cases hx : x = j₀
      · subst hx; simp [hσ0]
      · simp [Function.update_apply, hx]
    rw [this]
  have hAsum : ∑ σ ∈ A, bernoulliWeight p σ * Φ (Function.update σ j₀ false)
      = ∑ σ ∈ A, bernoulliWeight p σ * Φ σ := by
    refine Finset.sum_congr rfl (fun σ hσ => ?_)
    have hσ0 := (hmemA σ).mp hσ
    have : Function.update σ j₀ false = σ := by
      funext x
      by_cases hx : x = j₀
      · subst hx; simp [hσ0]
      · simp [Function.update_apply, hx]
    rw [this]
  have hkey : (1 - p) * bernoulliExp p (fun σ => Φ (Function.update σ j₀ false))
      = ∑ σ ∈ A, bernoulliWeight p σ * Φ σ := by
    unfold bernoulliExp
    rw [hsplit (fun σ => bernoulliWeight p σ * Φ (Function.update σ j₀ false)),
      hTsum, hAsum, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun σ hσ => ?_)
    have hσ0 := (hmemA σ).mp hσ
    have hw := bernoulliWeight_update_true p j₀ σ hσ0
    have : (1 - p) * (bernoulliWeight p (Function.update σ j₀ true) * Φ σ)
        = bernoulliWeight p σ * p * Φ σ := by
      rw [← hw]; ring
    rw [this]
    ring
  rw [hkey]
  unfold bernoulliExp
  rw [hsplit (fun σ => bernoulliWeight p σ * Φ σ)]
  have hTnn : 0 ≤ ∑ σ ∈ T, bernoulliWeight p σ * Φ σ :=
    Finset.sum_nonneg fun σ _ =>
      mul_nonneg (bernoulliWeight_nonneg hp₀ hp₁ σ) (hΦ σ)
  linarith

/-- `eᵘ ≤ 1 + u + u²eᵘ` for `u ≥ 0`.

This replaces Kim's Taylor expansion with remainder `φ''(ρ*)/2` (his (51)): the
constant `1` in place of `1/2` is immaterial, and it follows from
`1 − e^{−u} ≤ u` applied twice, with no calculus. -/
lemma exp_le_one_add_add_sq {u : ℝ} (hu : 0 ≤ u) :
    Real.exp u ≤ 1 + u + u ^ 2 * Real.exp u := by
  have he : (0 : ℝ) < Real.exp u := Real.exp_pos u
  have h1 : Real.exp u - 1 ≤ u * Real.exp u := by
    have h := Real.add_one_le_exp (-u)
    rw [Real.exp_neg] at h
    have hmul := mul_le_mul_of_nonneg_right h he.le
    rw [inv_mul_cancel₀ (ne_of_gt he)] at hmul
    nlinarith [hmul]
  nlinarith [h1, hu, he]

/-- `x⁴ ≤ 4096·e^{x/2}` for `x ≥ 0`, from `1 + x/8 ≤ e^{x/8}`.

Kim's sharper constant (his `ω`-derivative computation) is not needed: the
term this controls is the *second-order* remainder, where any constant does. -/
lemma pow_four_le_exp_half {x : ℝ} (hx : 0 ≤ x) :
    x ^ 4 ≤ 4096 * Real.exp (x / 2) := by
  have h1 : x / 8 ≤ Real.exp (x / 8) := by
    have := Real.add_one_le_exp (x / 8); linarith
  have h2 : (x / 8) ^ 4 ≤ (Real.exp (x / 8)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) h1 4
  have h3 : (Real.exp (x / 8)) ^ 4 = Real.exp (x / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h3] at h2
  nlinarith [h2]

/-- **Kim's Claim (51), abstract form.**

If `0 ≤ Y ≤ Z²/2` and `ρY ≤ Z/2` pointwise, where `Z` counts the `true`
coordinates in a block `S`, then

`E[e^{ρY}] ≤ 1 + ρE[Y] + 1024ρ²(1−p+pe)^{|S|}`.

This is the per-vertex moment-generating bound behind Kim's (49): the linear
term carries the mean exactly, and the quadratic remainder is controlled by the
binomial MGF of the block. -/
lemma bernoulliExp_exp_le_of_count {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset (Fin m)) (Y : (Fin m → Bool) → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hY0 : ∀ σ, 0 ≤ Y σ)
    (hYZ : ∀ σ, Y σ
      ≤ (∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0)) ^ 2 / 2)
    (hρY : ∀ σ, ρ * Y σ
      ≤ (∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0)) / 2) :
    bernoulliExp p (fun σ => Real.exp (ρ * Y σ))
      ≤ 1 + ρ * bernoulliExp p Y
        + 1024 * ρ ^ 2 * ((1 - p) + p * Real.exp 1) ^ S.card := by
  classical
  have hZ0 : ∀ σ : Fin m → Bool,
      (0 : ℝ) ≤ ∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0) := by
    intro σ
    refine Finset.sum_nonneg fun j _ => ?_
    split <;> norm_num
  have hpt : ∀ σ : Fin m → Bool, Real.exp (ρ * Y σ)
      ≤ (1 + ρ * Y σ)
        + (1024 * ρ ^ 2)
          * Real.exp (1 * ∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0)) := by
    intro σ
    set Z : ℝ := ∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0) with hZdef
    have hZnn : (0 : ℝ) ≤ Z := hZ0 σ
    have hu : (0 : ℝ) ≤ ρ * Y σ := mul_nonneg hρ (hY0 σ)
    have htay := exp_le_one_add_add_sq hu
    -- `exp(ρY) ≤ exp(Z/2)`
    have hexple : Real.exp (ρ * Y σ) ≤ Real.exp (Z / 2) :=
      Real.exp_le_exp.mpr (hρY σ)
    -- `(ρY)² ≤ ρ²Z⁴/4`
    have hsq : (ρ * Y σ) ^ 2 ≤ ρ ^ 2 * (Z ^ 4 / 4) := by
      have h1 : Y σ ≤ Z ^ 2 / 2 := hYZ σ
      have h2 : Y σ ^ 2 ≤ (Z ^ 2 / 2) ^ 2 :=
        pow_le_pow_left₀ (hY0 σ) h1 2
      have h3 : (Z ^ 2 / 2) ^ 2 = Z ^ 4 / 4 := by ring
      nlinarith [h2, h3, sq_nonneg ρ]
    -- `Z⁴ ≤ 4096 exp(Z/2)`
    have hz4 := pow_four_le_exp_half hZnn
    have hexp2 : Real.exp (Z / 2) * Real.exp (Z / 2) = Real.exp (1 * Z) := by
      rw [← Real.exp_add]; congr 1; ring
    have hprod : (ρ * Y σ) ^ 2 * Real.exp (ρ * Y σ)
        ≤ (1024 * ρ ^ 2) * Real.exp (1 * Z) := by
      have hA : (ρ * Y σ) ^ 2 * Real.exp (ρ * Y σ)
          ≤ (ρ ^ 2 * (Z ^ 4 / 4)) * Real.exp (Z / 2) := by
        refine mul_le_mul hsq hexple (Real.exp_pos _).le ?_
        positivity
      have hB : (ρ ^ 2 * (Z ^ 4 / 4)) * Real.exp (Z / 2)
          ≤ (ρ ^ 2 * (4096 * Real.exp (Z / 2) / 4)) * Real.exp (Z / 2) := by
        have hnn : (0 : ℝ) ≤ ρ ^ 2 := sq_nonneg ρ
        have := mul_le_mul_of_nonneg_left hz4 hnn
        nlinarith [this, Real.exp_pos (Z / 2), hnn]
      have hC : (ρ ^ 2 * (4096 * Real.exp (Z / 2) / 4)) * Real.exp (Z / 2)
          = (1024 * ρ ^ 2) * Real.exp (1 * Z) := by
        rw [← hexp2]; ring
      linarith [hA, hB, hC]
    linarith [htay, hprod]
  refine le_trans (bernoulliExp_mono hp0 hp1 hpt) ?_
  have hsplit : bernoulliExp p (fun σ => (1 + ρ * Y σ)
      + (1024 * ρ ^ 2)
        * Real.exp (1 * ∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0)))
      = bernoulliExp p (fun σ => 1 + ρ * Y σ)
        + bernoulliExp p (fun σ => (1024 * ρ ^ 2)
            * Real.exp (1 * ∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0))) :=
    bernoulliExp_add p _ _
  rw [hsplit, bernoulliExp_const_mul, bernoulliExp_exp_count]
  have hlin : bernoulliExp p (fun σ => 1 + ρ * Y σ) = 1 + ρ * bernoulliExp p Y := by
    have h1 : bernoulliExp p (fun σ => (1 : ℝ) + ρ * Y σ)
        = bernoulliExp p (fun _ => (1 : ℝ)) + bernoulliExp p (fun σ => ρ * Y σ) :=
      bernoulliExp_add p _ _
    rw [h1, bernoulliExp_const, bernoulliExp_const_mul]
  rw [hlin]

/-- **Conditioning on one coordinate.** -/
lemma bernoulliExp_split_coord {m : ℕ} {p : ℝ} (a : Fin m)
    (Φ : (Fin m → Bool) → ℝ) :
    bernoulliExp p Φ
      = p * bernoulliExp p (fun σ => Φ (Function.update σ a true))
        + (1 - p) * bernoulliExp p (fun σ => Φ (Function.update σ a false)) := by
  classical
  set A : Finset (Fin m → Bool) :=
    Finset.univ.filter (fun σ : Fin m → Bool => σ a = false) with hA
  set T : Finset (Fin m → Bool) :=
    Finset.univ.filter (fun σ : Fin m → Bool => σ a = true) with hT
  have hmemA : ∀ σ : Fin m → Bool, σ ∈ A ↔ σ a = false := by
    intro σ; rw [hA]; simp
  have hmemT : ∀ σ : Fin m → Bool, σ ∈ T ↔ σ a = true := by
    intro σ; rw [hT]; simp
  have hnot : Finset.univ.filter (fun σ : Fin m → Bool => ¬ σ a = true) = A := by
    rw [hA]; ext σ; simp [Bool.not_eq_true]
  have hsplit : ∀ F : (Fin m → Bool) → ℝ,
      ∑ σ : Fin m → Bool, F σ = (∑ σ ∈ T, F σ) + ∑ σ ∈ A, F σ := by
    intro F
    rw [hT, ← hnot]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun σ : Fin m → Bool => σ a = true) F).symm
  have hAT : A.image (fun σ : Fin m → Bool => Function.update σ a true) = T := by
    ext τ
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨σ, -, rfl⟩; rw [hmemT]; simp
    · intro hτ
      rw [hmemT] at hτ
      refine ⟨Function.update τ a false, (hmemA _).mpr (by simp), ?_⟩
      funext x
      by_cases hx : x = a
      · subst hx; simp [hτ]
      · simp [Function.update_apply, hx]
  have hinj : ∀ x ∈ A, ∀ y ∈ A,
      Function.update x a true = Function.update y a true → x = y := by
    intro x hx y hy hxy
    have hx0 := (hmemA x).mp hx
    have hy0 := (hmemA y).mp hy
    funext z
    by_cases hz : z = a
    · subst hz; rw [hx0, hy0]
    · have := congrFun hxy z
      simpa [Function.update_apply, hz] using this
  have hidT : ∀ σ ∈ T, Function.update σ a true = σ := by
    intro σ hσ
    have h0 := (hmemT σ).mp hσ
    funext x
    by_cases hx : x = a
    · subst hx; simp [h0]
    · simp [Function.update_apply, hx]
  have hidA : ∀ σ ∈ A, Function.update σ a false = σ := by
    intro σ hσ
    have h0 := (hmemA σ).mp hσ
    funext x
    by_cases hx : x = a
    · subst hx; simp [h0]
    · simp [Function.update_apply, hx]
  have hcancel : ∀ σ ∈ A,
      Function.update (Function.update σ a true) a false = σ := by
    intro σ hσ
    have h0 := (hmemA σ).mp hσ
    funext x
    by_cases hx : x = a
    · subst hx; simp [h0]
    · simp [Function.update_apply, hx]
  -- the `true` half
  have htrue : p * bernoulliExp p (fun σ => Φ (Function.update σ a true))
      = ∑ σ ∈ T, bernoulliWeight p σ * Φ σ := by
    unfold bernoulliExp
    rw [hsplit (fun σ => bernoulliWeight p σ * Φ (Function.update σ a true))]
    have hTs : ∑ σ ∈ T, bernoulliWeight p σ * Φ (Function.update σ a true)
        = ∑ σ ∈ T, bernoulliWeight p σ * Φ σ :=
      Finset.sum_congr rfl fun σ hσ => by rw [hidT σ hσ]
    have hAs : ∑ σ ∈ A, bernoulliWeight p σ * Φ (Function.update σ a true)
        = ∑ τ ∈ T, bernoulliWeight p (Function.update τ a false) * Φ τ := by
      rw [← hAT, Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun σ hσ => ?_
      rw [hcancel σ hσ]
    rw [hTs, hAs, mul_add, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ hτ => ?_
    have hτ0 := (hmemT τ).mp hτ
    have hupd : Function.update (Function.update τ a false) a true = τ := by
      funext x
      by_cases hx : x = a
      · subst hx; simp [hτ0]
      · simp [Function.update_apply, hx]
    have hw := bernoulliWeight_update_true p a (Function.update τ a false)
      (by simp)
    rw [hupd] at hw
    have hstep : p * bernoulliWeight p (Function.update τ a false)
        = bernoulliWeight p τ * (1 - p) := by linarith [hw]
    calc p * (bernoulliWeight p τ * Φ τ)
          + p * (bernoulliWeight p (Function.update τ a false) * Φ τ)
        = p * bernoulliWeight p τ * Φ τ
          + (p * bernoulliWeight p (Function.update τ a false)) * Φ τ := by ring
      _ = p * bernoulliWeight p τ * Φ τ
          + (bernoulliWeight p τ * (1 - p)) * Φ τ := by rw [hstep]
      _ = bernoulliWeight p τ * Φ τ := by ring
  -- the `false` half
  have hfalse : (1 - p) * bernoulliExp p (fun σ => Φ (Function.update σ a false))
      = ∑ σ ∈ A, bernoulliWeight p σ * Φ σ := by
    unfold bernoulliExp
    rw [hsplit (fun σ => bernoulliWeight p σ * Φ (Function.update σ a false))]
    have hAs : ∑ σ ∈ A, bernoulliWeight p σ * Φ (Function.update σ a false)
        = ∑ σ ∈ A, bernoulliWeight p σ * Φ σ :=
      Finset.sum_congr rfl fun σ hσ => by rw [hidA σ hσ]
    have hTs : ∑ σ ∈ T, bernoulliWeight p σ * Φ (Function.update σ a false)
        = ∑ σ ∈ A, bernoulliWeight p (Function.update σ a true) * Φ σ := by
      rw [← hAT, Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun σ hσ => ?_
      rw [hcancel σ hσ]
    rw [hAs, hTs, mul_add, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    have hσ0 := (hmemA σ).mp hσ
    have hw := bernoulliWeight_update_true p a σ hσ0
    calc (1 - p) * (bernoulliWeight p (Function.update σ a true) * Φ σ)
          + (1 - p) * (bernoulliWeight p σ * Φ σ)
        = (bernoulliWeight p (Function.update σ a true) * (1 - p)) * Φ σ
          + (1 - p) * bernoulliWeight p σ * Φ σ := by ring
      _ = (bernoulliWeight p σ * p) * Φ σ
          + (1 - p) * bernoulliWeight p σ * Φ σ := by rw [hw]
      _ = bernoulliWeight p σ * Φ σ := by ring
  rw [htrue, hfalse]
  unfold bernoulliExp
  rw [hsplit (fun σ => bernoulliWeight p σ * Φ σ)]

/-- **Block independence.** Functionals depending on disjoint coordinate blocks
are uncorrelated. -/
lemma bernoulliExp_mul_of_disjoint {m : ℕ} {p : ℝ} :
    ∀ (A : Finset (Fin m)) (f g : (Fin m → Bool) → ℝ),
      (∀ σ τ : Fin m → Bool, (∀ j ∈ A, σ j = τ j) → f σ = f τ) →
      (∀ σ τ : Fin m → Bool, (∀ j, j ∉ A → σ j = τ j) → g σ = g τ) →
      bernoulliExp p (fun σ => f σ * g σ)
        = bernoulliExp p f * bernoulliExp p g := by
  classical
  intro A
  induction A using Finset.induction_on with
  | empty =>
      intro f g hf _
      have hconst : ∀ σ, f σ = f (fun _ => false) :=
        fun σ => hf σ _ (by simp)
      have hfeq : f = fun _ => f (fun _ => false) := by
        funext σ; exact hconst σ
      rw [hfeq, bernoulliExp_const, bernoulliExp_const_mul]
  | insert a A' ha ih =>
      intro f g hf hg
      have hga : ∀ (σ : Fin m → Bool) (b : Bool),
          g (Function.update σ a b) = g σ := by
        intro σ b
        refine hg _ _ fun j hj => ?_
        have hja : j ≠ a := by
          intro hc; exact hj (by rw [hc]; exact Finset.mem_insert_self _ _)
        simp [Function.update_apply, hja]
      have hgA' : ∀ σ τ : Fin m → Bool, (∀ j, j ∉ A' → σ j = τ j) → g σ = g τ := by
        intro σ τ hστ
        refine hg _ _ fun j hj => hστ j ?_
        intro hc; exact hj (Finset.mem_insert_of_mem hc)
      have hfupd : ∀ b : Bool, ∀ σ τ : Fin m → Bool, (∀ j ∈ A', σ j = τ j) →
          f (Function.update σ a b) = f (Function.update τ a b) := by
        intro b σ τ hστ
        refine hf _ _ fun j hj => ?_
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · simp
        · have hja : j ≠ a := by intro hc; exact ha (hc ▸ hj')
          simp [Function.update_apply, hja, hστ j hj']
      have hkey : ∀ b : Bool,
          bernoulliExp p (fun σ => f (Function.update σ a b) * g σ)
            = bernoulliExp p (fun σ => f (Function.update σ a b))
              * bernoulliExp p g :=
        fun b => ih _ g (hfupd b) hgA'
      have hprod : ∀ b : Bool,
          bernoulliExp p (fun σ =>
            (fun σ' => f σ' * g σ') (Function.update σ a b))
            = bernoulliExp p (fun σ => f (Function.update σ a b))
              * bernoulliExp p g := by
        intro b
        have hrw : (fun σ : Fin m → Bool =>
            (fun σ' => f σ' * g σ') (Function.update σ a b))
            = fun σ => f (Function.update σ a b) * g σ := by
          funext σ
          show f (Function.update σ a b) * g (Function.update σ a b)
            = f (Function.update σ a b) * g σ
          rw [hga σ b]
        rw [hrw]; exact hkey b
      rw [bernoulliExp_split_coord a (fun σ => f σ * g σ),
        bernoulliExp_split_coord a f, hprod true, hprod false]
      ring

/-- **Block independence for a family**: the expectation of a product of
functionals on pairwise-disjoint coordinate blocks factors. -/
lemma bernoulliExp_prod_blocks {m : ℕ} {p : ℝ} {ι : Type*} [DecidableEq ι]
    (C : ι → Finset (Fin m)) (g : ι → (Fin m → Bool) → ℝ)
    (hdep : ∀ i, ∀ σ τ : Fin m → Bool, (∀ j ∈ C i, σ j = τ j) → g i σ = g i τ) :
    ∀ S : Finset ι, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (C i) (C j)) →
      bernoulliExp p (fun σ => ∏ i ∈ S, g i σ) = ∏ i ∈ S, bernoulliExp p (g i) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro _
      simp [bernoulliExp_const]
  | insert a S' ha ih =>
      intro hdisj
      have hdisj' : ∀ i ∈ S', ∀ j ∈ S', i ≠ j → Disjoint (C i) (C j) :=
        fun i hi j hj hij => hdisj i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hij
      have hGdep : ∀ σ τ : Fin m → Bool, (∀ j, j ∉ C a → σ j = τ j) →
          (∏ i ∈ S', g i σ) = ∏ i ∈ S', g i τ := by
        intro σ τ hστ
        refine Finset.prod_congr rfl fun i hi => ?_
        refine hdep i _ _ fun j hj => ?_
        refine hστ j fun hc => ?_
        have hne : a ≠ i := fun hc' => ha (hc' ▸ hi)
        have := hdisj a (Finset.mem_insert_self _ _) i
          (Finset.mem_insert_of_mem hi) hne
        exact (Finset.disjoint_left.mp this hc) hj
      have hrw : (fun σ : Fin m → Bool => ∏ i ∈ insert a S', g i σ)
          = fun σ => g a σ * ∏ i ∈ S', g i σ := by
        funext σ; rw [Finset.prod_insert ha]
      rw [hrw, Finset.prod_insert ha, bernoulliExp_mul_of_disjoint (C a) (g a)
        (fun σ => ∏ i ∈ S', g i σ) (hdep a) hGdep, ih hdisj']

/-- Composing with `freeze j₀` kills the `j₀` Lipschitz constant. -/
lemma IsCoordLipschitz.freeze {m : ℕ} {Φ : (Fin m → Bool) → ℝ} {c : Fin m → ℝ}
    (h : IsCoordLipschitz Φ c) (j₀ : Fin m) :
    IsCoordLipschitz (fun σ => Φ (Function.update σ j₀ false))
      (Function.update c j₀ 0) := by
  classical
  intro j τ τ' hagree
  by_cases hj : j = j₀
  · subst hj
    have heq : Function.update τ j false = Function.update τ' j false := by
      funext x
      by_cases hx : x = j
      · subst hx; simp
      · simp [Function.update_apply, hx, hagree x hx]
    simp [heq]
  · have hbound : |Φ (Function.update τ j₀ false)
        - Φ (Function.update τ' j₀ false)| ≤ c j := by
      refine h j _ _ ?_
      intro ℓ hℓ
      by_cases hl : ℓ = j₀
      · subst hl; simp
      · simp [Function.update_apply, hl, hagree ℓ hℓ]
    simpa [Function.update_apply, hj] using hbound

/-- **Concentration for a count of selected trials.**

The concrete form of Kahn's inequality that every property in Kim §4 applies:
for `Φ(σ) = |{j ∈ S : σⱼ}|`, whose mean is `p|S|`,

`Pr(|Φ − p|S|| ≥ λ) ≤ 2·exp(−tλ + (t²/2)·p(1−p)·|S|·e^t)`.

Kim instantiates this with `S = N_Γ(v)` and `t = 4n^{-1/4}` for Lemma 4.3(i),
with `S = Γ(T)` and `t = n^{-5/17}` for (38), and so on. -/
theorem bernoulliPr_count_concentration {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p)
    (hp₁ : p ≤ 1) (S : Finset (Fin m)) {t lam : ℝ} (ht : 0 ≤ t) :
    bernoulliPr p (Finset.univ.filter (fun σ =>
        lam ≤ |(∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0)) - p * S.card|))
      ≤ 2 * Real.exp (-t * lam
          + t ^ 2 / 2 * (p * (1 - p) * ((S.card : ℝ) * Real.exp t))) := by
  classical
  have hkahn := bernoulliPr_kahn hp₀ hp₁ (count_isCoordLipschitz S)
    (t := t) (lam := lam) ht
  rw [bernoulliExp_count, sum_indicator_sq_exp] at hkahn
  exact hkahn

/-- **One-sided form** of `bernoulliPr_count_concentration`, which is what Kim
actually applies (e.g. Lemma 4.3(i): `Pr(Φ_v − E[Φ_v] ≥ n^{1/4}log n)`). -/
theorem bernoulliPr_count_upper {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (S : Finset (Fin m)) {t lam : ℝ} (ht : 0 ≤ t) :
    bernoulliPr p (Finset.univ.filter (fun σ =>
        lam ≤ (∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0)) - p * S.card))
      ≤ 2 * Real.exp (-t * lam
          + t ^ 2 / 2 * (p * (1 - p) * ((S.card : ℝ) * Real.exp t))) := by
  classical
  refine le_trans (bernoulliPr_mono hp₀ hp₁ ?_)
    (bernoulliPr_count_concentration hp₀ hp₁ S ht)
  intro σ hσ
  obtain ⟨-, hle⟩ := Finset.mem_filter.mp hσ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_trans hle (le_abs_self _)⟩

/-- **Threshold form**: `Pr(Φ ≥ p|S| + λ)` is bounded by the same quantity.
This is how Kim states the Property-1 and Property-2 failures. -/
theorem bernoulliPr_count_ge_threshold {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p)
    (hp₁ : p ≤ 1) (S : Finset (Fin m)) {t lam : ℝ} (ht : 0 ≤ t) :
    bernoulliPr p (Finset.univ.filter (fun σ =>
        p * S.card + lam ≤ ∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0)))
      ≤ 2 * Real.exp (-t * lam
          + t ^ 2 / 2 * (p * (1 - p) * ((S.card : ℝ) * Real.exp t))) := by
  classical
  refine le_trans (bernoulliPr_mono hp₀ hp₁ ?_)
    (bernoulliPr_count_upper hp₀ hp₁ S ht)
  intro σ hσ
  obtain ⟨-, hle⟩ := Finset.mem_filter.mp hσ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩

/-- `|A ∩ ⋃ B_j| ≤ ∑ |A ∩ B_j|`. -/
lemma card_inter_biUnion_le {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (A : Finset α) (s : Finset ι) (B : ι → Finset α) :
    (A ∩ s.biUnion B).card ≤ ∑ j ∈ s, (A ∩ B j).card := by
  classical
  rw [Finset.inter_biUnion]
  exact Finset.card_biUnion_le

/-- **Bonferroni's inequality (second order).**
`∑_{i∈s} |A i| ≤ |⋃_{i∈s} A i| + ∑_{i∈s} ∑_{j<i} |A i ∩ A j|`.

Induction on `s` by largest element: adding a new top element `a` contributes
`|A a| − |A a ∩ ⋃_s A| ≥ |A a| − ∑_{j∈s} |A a ∩ A j|`. -/
lemma bonferroni_card_biUnion {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    [LinearOrder ι] (s : Finset ι) (A : ι → Finset α) :
    ∑ i ∈ s, (A i).card
      ≤ (s.biUnion A).card
        + ∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), (A i ∩ A j).card := by
  classical
  induction s using Finset.induction_on_max with
  | h0 => simp
  | step a s hlt ih =>
      have hanot : a ∉ s := fun hc => absurd (hlt a hc) (lt_irrefl a)
      rw [Finset.sum_insert hanot, Finset.biUnion_insert,
        Finset.sum_insert hanot]
      -- the `i = a` inner sum ranges over all of `s`
      have hfilter_a : (insert a s).filter (fun j => j < a) = s := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hj | hj, hlt'⟩
          · exact absurd hlt' (by rw [hj]; exact lt_irrefl a)
          · exact hj
        · intro hj; exact ⟨Or.inr hj, hlt j hj⟩
      -- for `i ∈ s` the filter is unchanged (a is not `< i`)
      have hfilter_s : ∀ i ∈ s,
          (insert a s).filter (fun j => j < i) = s.filter (fun j => j < i) := by
        intro i hi
        ext j
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hj | hj, hlt'⟩
          · exact absurd (hj ▸ hlt') (asymm (hlt i hi))
          · exact ⟨hj, hlt'⟩
        · rintro ⟨hj, hlt'⟩; exact ⟨Or.inr hj, hlt'⟩
      rw [hfilter_a]
      have hsum_eq : ∑ i ∈ s, ∑ j ∈ (insert a s).filter (fun j => j < i),
            (A i ∩ A j).card
          = ∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), (A i ∩ A j).card :=
        Finset.sum_congr rfl (fun i hi => by rw [hfilter_s i hi])
      rw [hsum_eq]
      -- union cardinality bound
      have hunion : (A a).card + (s.biUnion A).card
          ≤ (A a ∪ s.biUnion A).card + (A a ∩ s.biUnion A).card :=
        le_of_eq (Finset.card_union_add_card_inter _ _).symm
      have hinter := card_inter_biUnion_le (A a) s A
      omega

/-- `2·∑_{i∈s} |{j ∈ s : j < i}| + |s| = |s|²`, i.e. the ordered-pair count is
`|s|(|s|−1)/2`, stated without truncated subtraction. -/
lemma sum_card_filter_lt {ι : Type*} [DecidableEq ι] [LinearOrder ι]
    (s : Finset ι) :
    2 * ∑ i ∈ s, (s.filter (fun j => j < i)).card + s.card = s.card * s.card := by
  classical
  induction s using Finset.induction_on_max with
  | h0 => simp
  | step a s hlt ih =>
      have hanot : a ∉ s := fun hc => absurd (hlt a hc) (lt_irrefl a)
      have hfilter_a : (insert a s).filter (fun j => j < a) = s := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hj | hj, hlt'⟩
          · exact absurd hlt' (by rw [hj]; exact lt_irrefl a)
          · exact hj
        · intro hj; exact ⟨Or.inr hj, hlt j hj⟩
      have hfilter_s : ∀ i ∈ s,
          (insert a s).filter (fun j => j < i) = s.filter (fun j => j < i) := by
        intro i hi
        ext j
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hj | hj, hlt'⟩
          · exact absurd (hj ▸ hlt') (asymm (hlt i hi))
          · exact ⟨hj, hlt'⟩
        · rintro ⟨hj, hlt'⟩; exact ⟨Or.inr hj, hlt'⟩
      rw [Finset.sum_insert hanot, hfilter_a]
      have hsum_eq : ∑ i ∈ s, ((insert a s).filter (fun j => j < i)).card
          = ∑ i ∈ s, (s.filter (fun j => j < i)).card :=
        Finset.sum_congr rfl (fun i hi => by rw [hfilter_s i hi])
      rw [hsum_eq, Finset.card_insert_of_notMem hanot]
      have hexp : (s.card + 1) * (s.card + 1)
          = s.card * s.card + 2 * s.card + 1 := by ring
      rw [hexp, ← ih]
      ring

/-- **Kim's Lemma 3.5, Bonferroni consequence.** For a family `A i ⊆ B`
(`i ∈ s`) with every `|A i| ≥ lo` and every pairwise intersection `≤ hi`,
writing `L = |s|`:

`lo·L ≤ |B| + (L² − L)/2 · hi`.

Kim contradicts this by taking `L = ⌊β⁻¹γ⁻¹√|B|⌋ + 1`, `lo = 2βγ√|B|`,
`hi = β²`. -/
lemma almost_disjoint_bonferroni {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    [LinearOrder ι] (B : Finset α) (s : Finset ι) (A : ι → Finset α)
    (hsub : ∀ i ∈ s, A i ⊆ B) {lo hi : ℝ} (hhi0 : 0 ≤ hi)
    (hlarge : ∀ i ∈ s, lo ≤ ((A i).card : ℝ))
    (hsmall : ∀ i ∈ s, ∀ j ∈ s, j < i → ((A i ∩ A j).card : ℝ) ≤ hi) :
    lo * (s.card : ℝ)
      ≤ (B.card : ℝ)
        + ((s.card : ℝ) * (s.card : ℝ) - (s.card : ℝ)) / 2 * hi := by
  classical
  set P : ℕ := ∑ i ∈ s, (s.filter (fun j => j < i)).card with hP
  have hcount : 2 * (P : ℝ) + (s.card : ℝ) = (s.card : ℝ) * (s.card : ℝ) := by
    have h := sum_card_filter_lt s
    rw [hP]
    exact_mod_cast h
  have hbon := bonferroni_card_biUnion s A
  have hunion_le : (s.biUnion A).card ≤ B.card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨i, hi', hxi⟩ := Finset.mem_biUnion.mp hx
    exact hsub i hi' hxi
  have hlow : lo * (s.card : ℝ) ≤ ∑ i ∈ s, ((A i).card : ℝ) := by
    rw [mul_comm]
    calc (s.card : ℝ) * lo = ∑ _i ∈ s, lo := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s, ((A i).card : ℝ) := Finset.sum_le_sum hlarge
  have hpair : ∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), ((A i ∩ A j).card : ℝ)
      ≤ (P : ℝ) * hi := by
    have hstep : ∀ i ∈ s,
        ∑ j ∈ s.filter (fun j => j < i), ((A i ∩ A j).card : ℝ)
          ≤ ((s.filter (fun j => j < i)).card : ℝ) * hi := by
      intro i hi'
      calc ∑ j ∈ s.filter (fun j => j < i), ((A i ∩ A j).card : ℝ)
          ≤ ∑ _j ∈ s.filter (fun j => j < i), hi :=
            Finset.sum_le_sum (fun j hj => by
              obtain ⟨hjs, hji⟩ := Finset.mem_filter.mp hj
              exact hsmall i hi' j hjs hji)
        _ = ((s.filter (fun j => j < i)).card : ℝ) * hi := by
            rw [Finset.sum_const, nsmul_eq_mul]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.sum_mul]
    apply le_of_eq
    congr 1
    rw [hP]
    push_cast
    ring
  have hbonR : (∑ i ∈ s, ((A i).card : ℝ))
      ≤ ((s.biUnion A).card : ℝ)
        + ∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), ((A i ∩ A j).card : ℝ) := by
    exact_mod_cast hbon
  have hBR : ((s.biUnion A).card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hunion_le
  have hPval : (P : ℝ) = ((s.card : ℝ) * (s.card : ℝ) - (s.card : ℝ)) / 2 := by
    linarith [hcount]
  have hPmul : (P : ℝ) * hi
      = ((s.card : ℝ) * (s.card : ℝ) - (s.card : ℝ)) / 2 * hi := by
    rw [hPval]
  linarith [hlow, hbonR, hBR, hpair, hPmul]

/-- **The sum form of the Bonferroni bound.** For an almost-disjoint family
inside `B`, the *total* size is at most `|B|` plus the pairwise overlap budget:

`∑_{i∈s} |A i| ≤ |B| + (L² − L)/2 · hi`, `L = |s|`.

Kim's §4.8 uses this (rather than the count form of Lemma 3.5) to bound
`Σ′ |A(w,T)| ≤ 2t` and `Σ″ |N_ℰ(w,T)| ≤ (1+θ)t`. -/
lemma sum_card_le_bonferroni {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    [LinearOrder ι] (B : Finset α) (s : Finset ι) (A : ι → Finset α)
    (hsub : ∀ i ∈ s, A i ⊆ B) {hi : ℝ}
    (hsmall : ∀ i ∈ s, ∀ j ∈ s, j < i → ((A i ∩ A j).card : ℝ) ≤ hi) :
    ∑ i ∈ s, ((A i).card : ℝ)
      ≤ (B.card : ℝ)
        + ((s.card : ℝ) * (s.card : ℝ) - (s.card : ℝ)) / 2 * hi := by
  classical
  set P : ℕ := ∑ i ∈ s, (s.filter (fun j => j < i)).card with hP
  have hcount : 2 * (P : ℝ) + (s.card : ℝ) = (s.card : ℝ) * (s.card : ℝ) := by
    have h := sum_card_filter_lt s
    rw [hP]
    exact_mod_cast h
  have hbon := bonferroni_card_biUnion s A
  have hunion_le : (s.biUnion A).card ≤ B.card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨i, hi', hxi⟩ := Finset.mem_biUnion.mp hx
    exact hsub i hi' hxi
  have hpair : ∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), ((A i ∩ A j).card : ℝ)
      ≤ (P : ℝ) * hi := by
    have hstep : ∀ i ∈ s,
        ∑ j ∈ s.filter (fun j => j < i), ((A i ∩ A j).card : ℝ)
          ≤ ((s.filter (fun j => j < i)).card : ℝ) * hi := by
      intro i hi'
      calc ∑ j ∈ s.filter (fun j => j < i), ((A i ∩ A j).card : ℝ)
          ≤ ∑ _j ∈ s.filter (fun j => j < i), hi :=
            Finset.sum_le_sum (fun j hj => by
              obtain ⟨hjs, hji⟩ := Finset.mem_filter.mp hj
              exact hsmall i hi' j hjs hji)
        _ = ((s.filter (fun j => j < i)).card : ℝ) * hi := by
            rw [Finset.sum_const, nsmul_eq_mul]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.sum_mul]
    apply le_of_eq
    congr 1
    rw [hP]
    push_cast
    ring
  have hbonR : (∑ i ∈ s, ((A i).card : ℝ))
      ≤ ((s.biUnion A).card : ℝ)
        + ∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), ((A i ∩ A j).card : ℝ) := by
    exact_mod_cast hbon
  have hBR : ((s.biUnion A).card : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast hunion_le
  have hPval : (P : ℝ) = ((s.card : ℝ) * (s.card : ℝ) - (s.card : ℝ)) / 2 := by
    linarith [hcount]
  have hPmul : (P : ℝ) * hi
      = ((s.card : ℝ) * (s.card : ℝ) - (s.card : ℝ)) / 2 * hi := by
    rw [hPval]
  linarith [hbonR, hBR, hpair, hPmul]

set_option maxHeartbeats 1000000 in
/-- **Kim's Lemma 3.5 (Almost Disjoint Covering), first part.**

If `Aᵢ ⊆ B` for `i ∈ s`, every `|Aᵢ| ≥ 2βγ√|B|`, every pairwise intersection
is `≤ β²`, and `1 ≤ β, γ` with `β ≤ √|B|/2`, then `|s| ≤ √|B|/(βγ)`.

Kim's proof: assume not, pass to a subfamily of size `l₀ = ⌊√|B|/(βγ)⌋+1`,
and apply the Bonferroni bound; the two sides give `2|B| ≤ 1.75|B|`. -/
theorem almost_disjoint_card_le {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    [LinearOrder ι] (B : Finset α) (s : Finset ι) (A : ι → Finset α)
    (hsub : ∀ i ∈ s, A i ⊆ B)
    {β γ : ℝ} (hβ1 : 1 ≤ β) (hγ1 : 1 ≤ γ)
    (hβB : β ≤ Real.sqrt B.card / 2) (hBpos : 0 < B.card)
    (hlarge : ∀ i ∈ s, 2 * β * γ * Real.sqrt B.card ≤ ((A i).card : ℝ))
    (hsmall : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ((A i ∩ A j).card : ℝ) ≤ β ^ 2) :
    (s.card : ℝ) ≤ Real.sqrt B.card / (β * γ) := by
  classical
  by_contra hcon
  push_neg at hcon
  have hβpos : (0 : ℝ) < β := by linarith
  have hγpos : (0 : ℝ) < γ := by linarith
  have hBR : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast hBpos
  have hsq_pos : (0 : ℝ) < Real.sqrt B.card := Real.sqrt_pos.mpr hBR
  have hsq_mul : Real.sqrt B.card * Real.sqrt B.card = (B.card : ℝ) :=
    Real.mul_self_sqrt hBR.le
  set x : ℝ := Real.sqrt B.card / (β * γ) with hx
  have hx_nonneg : 0 ≤ x := by positivity
  set l₀ : ℕ := ⌊x⌋₊ + 1 with hl₀
  have hl₀_le : l₀ ≤ s.card := by
    have hlt : ⌊x⌋₊ < s.card := by rw [Nat.floor_lt hx_nonneg]; exact hcon
    omega
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hl₀_le
  have hbon := almost_disjoint_bonferroni B t A
    (fun i hi => hsub i (hts hi)) (sq_nonneg β)
    (fun i hi => hlarge i (hts hi))
    (fun i hi j hj hji => hsmall i (hts hi) j (hts hj) (ne_of_gt hji))
  rw [htcard] at hbon
  have hxβ : x * β = Real.sqrt B.card / γ := by rw [hx]; field_simp
  have hxβγ : 2 * β * γ * Real.sqrt B.card * x = 2 * (B.card : ℝ) := by
    rw [hx]; field_simp; linarith [hsq_mul]
  have hl₀_lower : x ≤ (l₀ : ℝ) := by
    rw [hl₀]; push_cast; linarith [Nat.lt_floor_add_one x]
  have hl₀_sub : ((l₀ : ℝ) - 1) ≤ x := by
    rw [hl₀]; push_cast; simpa using Nat.floor_le hx_nonneg
  have hcoef_pos : (0 : ℝ) < 2 * β * γ * Real.sqrt B.card := by positivity
  have hlow : 2 * (B.card : ℝ) ≤ 2 * β * γ * Real.sqrt B.card * (l₀ : ℝ) := by
    calc 2 * (B.card : ℝ) = 2 * β * γ * Real.sqrt B.card * x := hxβγ.symm
      _ ≤ 2 * β * γ * Real.sqrt B.card * (l₀ : ℝ) :=
          mul_le_mul_of_nonneg_left hl₀_lower hcoef_pos.le
  have hγinv : Real.sqrt B.card / γ ≤ Real.sqrt B.card := by
    rw [div_le_iff₀ hγpos]; nlinarith [hsq_pos, hγ1]
  have hA : (l₀ : ℝ) * β ≤ (3 / 2) * Real.sqrt B.card := by
    have h1 : (l₀ : ℝ) * β ≤ (x + 1) * β :=
      mul_le_mul_of_nonneg_right (by linarith) hβpos.le
    have h2 : (x + 1) * β = x * β + β := by ring
    rw [h2, hxβ] at h1
    linarith [h1, hγinv, hβB]
  have hB' : ((l₀ : ℝ) - 1) * β ≤ Real.sqrt B.card := by
    have h1 : ((l₀ : ℝ) - 1) * β ≤ x * β :=
      mul_le_mul_of_nonneg_right hl₀_sub hβpos.le
    rw [hxβ] at h1
    linarith [h1, hγinv]
  have hl0_ge_one : (1 : ℝ) ≤ (l₀ : ℝ) := by
    rw [hl₀]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌊x⌋₊]
  have hB_nn : 0 ≤ ((l₀ : ℝ) - 1) * β := mul_nonneg (by linarith) hβpos.le
  have hhigh : ((l₀ : ℝ) * (l₀ : ℝ) - (l₀ : ℝ)) / 2 * β ^ 2
      ≤ (3 / 4) * (B.card : ℝ) := by
    have hfac : ((l₀ : ℝ) * (l₀ : ℝ) - (l₀ : ℝ)) / 2 * β ^ 2
        = ((l₀ : ℝ) * β) * (((l₀ : ℝ) - 1) * β) / 2 := by ring
    rw [hfac]
    have hprod : ((l₀ : ℝ) * β) * (((l₀ : ℝ) - 1) * β)
        ≤ ((3 / 2) * Real.sqrt B.card) * Real.sqrt B.card :=
      mul_le_mul hA hB' hB_nn (by positivity)
    calc ((l₀ : ℝ) * β) * (((l₀ : ℝ) - 1) * β) / 2
        ≤ (((3 / 2) * Real.sqrt B.card) * Real.sqrt B.card) / 2 := by linarith
      _ = (3 / 4) * (B.card : ℝ) := by rw [mul_assoc, hsq_mul]; ring
  linarith [hbon, hlow, hhigh, hBR]

/-- **Lemma 3.5, second conclusion.** Under the same hypotheses,
`Σⱼ |Aⱼ| ≤ |B| + |B|/(2γ²)`.

Kim states `(1 − 1/(2γ²))⁻¹|B|`; the Bonferroni route gives the slightly
sharper `(1 + 1/(2γ²))|B|`, which is all §4.7/§4.8 use (with `γ = 1` giving
`≤ 2|B|`, and `γ = log n` giving `≤ (1 + θ/2)|B|`). -/
lemma almost_disjoint_sum_card_le {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    [LinearOrder ι] (B : Finset α) (s : Finset ι) (A : ι → Finset α)
    (hsub : ∀ i ∈ s, A i ⊆ B)
    {β γ : ℝ} (hβ1 : 1 ≤ β) (hγ1 : 1 ≤ γ)
    (hβB : β ≤ Real.sqrt B.card / 2) (hBpos : 0 < B.card)
    (hlarge : ∀ i ∈ s, 2 * β * γ * Real.sqrt B.card ≤ ((A i).card : ℝ))
    (hsmall : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ((A i ∩ A j).card : ℝ) ≤ β ^ 2) :
    ∑ i ∈ s, ((A i).card : ℝ)
      ≤ (B.card : ℝ) + (B.card : ℝ) / (2 * γ ^ 2) := by
  have hβ0 : (0 : ℝ) < β := by linarith
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hB0 : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast hBpos
  have hl := almost_disjoint_card_le B s A hsub hβ1 hγ1 hβB hBpos hlarge hsmall
  have hbon := sum_card_le_bonferroni B s A hsub
    (hi := β ^ 2) (fun i hi j hj hlt => hsmall i hi j hj (ne_of_gt hlt))
  have hlnn : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have hsq2 : (s.card : ℝ) ^ 2 * (β ^ 2 * γ ^ 2) ≤ (B.card : ℝ) := by
    have hbg : (0 : ℝ) < β * γ := by positivity
    have h1 : (s.card : ℝ) * (β * γ) ≤ Real.sqrt (B.card) := by
      rw [← le_div_iff₀ hbg]; exact hl
    have h2 : ((s.card : ℝ) * (β * γ)) ^ 2 ≤ Real.sqrt (B.card) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [Real.sq_sqrt hB0.le] at h2
    calc (s.card : ℝ) ^ 2 * (β ^ 2 * γ ^ 2)
        = ((s.card : ℝ) * (β * γ)) ^ 2 := by ring
      _ ≤ (B.card : ℝ) := h2
  have hdivle : ((s.card : ℝ) * (s.card : ℝ) - (s.card : ℝ)) / 2 * β ^ 2
      ≤ (B.card : ℝ) / (2 * γ ^ 2) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * γ ^ 2)]
    have hlβγ : 0 ≤ (s.card : ℝ) * (β ^ 2 * γ ^ 2) :=
      mul_nonneg hlnn (by positivity)
    nlinarith [hsq2, hlβγ]
  linarith [hbon, hdivle]

/-- **Second-order Bernoulli bound** `(1-x)^h ≤ 1 - hx + h²x²/2` for
`x ∈ [0,1]`. Kim uses this (with the matching lower bound) in Lemma 4.1 to
evaluate `Pr(e ∉ Y') = (1-p)^{2b(a+5θ)√n}`.

Induction on `h`: the step needs only `x²/2 + m²x³/2 ≥ 0`. -/
lemma one_sub_pow_le_quadratic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (h : ℕ) :
    (1 - x) ^ h ≤ 1 - (h : ℝ) * x + (h : ℝ) ^ 2 * x ^ 2 / 2 := by
  induction h with
  | zero => simp
  | succ m ih =>
      have h1x : (0 : ℝ) ≤ 1 - x := by linarith
      have hstep : (1 - x) ^ (m + 1) ≤ (1 - (m : ℝ) * x + (m : ℝ) ^ 2 * x ^ 2 / 2) * (1 - x) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right ih h1x
      refine hstep.trans ?_
      push_cast
      nlinarith [sq_nonneg x, mul_nonneg (mul_nonneg hx0 hx0) hx0,
        sq_nonneg ((m : ℝ) * x), hx0]

/-- **Bernoulli's inequality**, lower half: `1 - hx ≤ (1-x)^h` for `x ≤ 1`. -/
lemma one_sub_mul_le_one_sub_pow {x : ℝ} (hx1 : x ≤ 1) (h : ℕ) :
    1 - (h : ℝ) * x ≤ (1 - x) ^ h := by
  have := one_add_mul_le_pow (a := -x) (by linarith) h
  simpa [sub_eq_add_neg, mul_comm] using this

/-- Kim's two-sided estimate for `(1-x)^h`, as used in Lemma 4.1. -/
lemma one_sub_pow_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (h : ℕ) :
    1 - (h : ℝ) * x ≤ (1 - x) ^ h
      ∧ (1 - x) ^ h ≤ 1 - (h : ℝ) * x + (h : ℝ) ^ 2 * x ^ 2 / 2 :=
  ⟨one_sub_mul_le_one_sub_pow hx1 h, one_sub_pow_le_quadratic hx0 hx1 h⟩


/-- `(1−p)^{a−I} ≤ (1−p)^a (1 + 2Ip)`: dropping `I` factors costs at most
`(1−p)^{-I}`, which for `2Ip ≤ 1` is at most `1 + 2Ip`. -/
lemma pow_sub_le_pow_mul {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a I : ℕ}
    (hIa : I ≤ a) (hpI : 2 * (I : ℝ) * p ≤ 1) :
    (1 - p) ^ (a - I) ≤ (1 - p) ^ a * (1 + 2 * I * p) := by
  have h1p : (0 : ℝ) ≤ 1 - p := by linarith
  have hIp0 : (0 : ℝ) ≤ (I : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0
  have hsplit : (1 - p) ^ a = (1 - p) ^ (a - I) * (1 - p) ^ I := by
    rw [← pow_add]; congr 1; omega
  have hlow : 1 - (I : ℝ) * p ≤ (1 - p) ^ I :=
    one_sub_mul_le_one_sub_pow hp1 I
  have hkey : (1 : ℝ) ≤ (1 + 2 * I * p) * (1 - p) ^ I := by
    nlinarith [hlow, hIp0, hpI]
  calc (1 - p) ^ (a - I) = (1 - p) ^ (a - I) * 1 := by ring
    _ ≤ (1 - p) ^ (a - I) * ((1 + 2 * I * p) * (1 - p) ^ I) :=
        mul_le_mul_of_nonneg_left hkey (pow_nonneg h1p _)
    _ = (1 - p) ^ a * (1 + 2 * I * p) := by rw [hsplit]; ring

end Phase1

/-! ## Phase 2 — Block construction

Fix a finite vertex set `V := Fin n` and let `K(V)` be the complete graph on
`V`. We work in the product probability space `({0,1}^{ℰ(K(V))})^ω` indexed by
stages `i ∈ ℕ`, with `θ := (log n)⁻²` and one Bernoulli per edge per stage.

`Step` is the one-step block construction `(ℰᵢ, Γᵢ, Gᵢ) ↦ (ℰᵢ₊₁, Γᵢ₊₁, Gᵢ₊₁)`
of Kim §1.1 (BC1–BC3):

1. Sample `Xᵢ₊₁ ⊆ Γᵢ` with each `e ∈ Γᵢ` included independently with
   probability `θ / √n`.
2. Form `Λ(Xᵢ₊₁) := {eᵤᵥ eᵥw ⊆ Xᵢ₊₁ : ewu ∈ ℰᵢ}` and
   `Δ(Xᵢ₊₁) := {eᵤᵥ eᵥw eᵥw ⊆ Xᵢ₊₁}`.
3. Choose a maximal disjoint collection `ℱᵢ₊₁ ⊆ Λ ∪ Δ`.
4. Set `ℰᵢ₊₁ := ℰᵢ ∪ Xᵢ₊₁`, `Gᵢ₊₁ := Gᵢ ∪ (Xᵢ₊₁ \ ⋃ℱᵢ₊₁)`, and
   `Γᵢ₊₁ := {e ∈ ℰ(K(V)) \ ℰᵢ₊₁ : ∀ f, g ∈ ℰᵢ₊₁, e f g not a triangle}`.

`Gᵢ` is triangle-free by maximality of `ℱᵢ₊₁` and the definition of `Γᵢ`.
-/

section Phase2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An edge of the complete graph on `V`: a non-diagonal `Sym2 V`. -/
abbrev Edge (V : Type*) := {e : Sym2 V // ¬ e.IsDiag}

instance [Fintype V] [DecidableEq V] : Fintype (Edge V) :=
  Subtype.fintype _

instance [DecidableEq V] : DecidableEq (Edge V) :=
  Subtype.instDecidableEq

/-- The full edge set of `K(V)`. -/
def allEdges (V : Type*) [Fintype V] [DecidableEq V] : Finset (Edge V) := Finset.univ

/-- Three edges of `K(V)` form a triangle if their underlying unordered pairs
share three distinct vertices forming a 3-cycle:
`e = {a,b}`, `f = {b,c}`, `g = {a,c}`. -/
def IsTriangle (e f g : Edge V) : Prop :=
  ∃ (a b c : V), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    e.val = s(a, b) ∧ f.val = s(b, c) ∧ g.val = s(a, c)

/-- Swapping the first two edges of a triangle gives another labelling. -/
lemma IsTriangle.swap12 {e f g : Edge V} (h : IsTriangle e f g) : IsTriangle f e g := by
  obtain ⟨a, b, c, hab, hbc, hac, heq, feq, geq⟩ := h
  refine ⟨c, b, a, hbc.symm, hab.symm, hac.symm, ?_, ?_, ?_⟩
  · rw [Sym2.eq_swap]; exact feq
  · rw [Sym2.eq_swap]; exact heq
  · rw [Sym2.eq_swap]; exact geq

/-- Swapping the last two edges of a triangle gives another labelling. -/
lemma IsTriangle.swap23 {e f g : Edge V} (h : IsTriangle e f g) : IsTriangle e g f := by
  obtain ⟨a, b, c, hab, hbc, hac, heq, feq, geq⟩ := h
  -- Want e = {a',b'}, g = {b',c'}, f = {a',c'}
  -- g = {a,c}, f = {b,c}, e = {a,b}
  -- Try a' = b, b' = a, c' = c. Then e = {b,a} = {a,b} ✓.
  -- g = {a,c} should = {a,c} = {b',c'} = {a, c} ✓.
  -- f = {b,c} should = {a',c'} = {b, c} ✓.
  refine ⟨b, a, c, hab.symm, hac, hbc, ?_, ?_, ?_⟩
  · rw [Sym2.eq_swap]; exact heq
  · exact geq
  · exact feq

/-- Cyclic rotation of edges. -/
lemma IsTriangle.rotate {e f g : Edge V} (h : IsTriangle e f g) : IsTriangle f g e := by
  exact (h.swap12.swap23)

/-- The reverse rotation. -/
lemma IsTriangle.rotate' {e f g : Edge V} (h : IsTriangle e f g) : IsTriangle g e f :=
  h.rotate.rotate

/-- A state of the block construction at stage `i`: the sampled edges `ℰᵢ`,
the surviving edges `Γᵢ`, and the triangle-free subgraph `Gᵢ`, together with
the maintained invariants of Kim §1.1. -/
structure BlockState (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Sampled edges `ℰᵢ ⊆ K(V)`. -/
  E : Finset (Edge V)
  /-- Surviving edges `Γᵢ ⊆ K(V) \ ℰᵢ`. An edge `e ∈ Γᵢ` cannot complete a
  triangle with two edges of `ℰᵢ`. -/
  Γ : Finset (Edge V)
  /-- The maintained triangle-free subgraph `Gᵢ ⊆ ℰᵢ`. -/
  G : Finset (Edge V)
  hG_subset_E : G ⊆ E
  hΓ_disjoint_E : Disjoint Γ E
  hΓ_no_triangle : ∀ e ∈ Γ, ∀ f ∈ E, ∀ g ∈ E, ¬ IsTriangle e f g
  hG_triangle_free : ∀ e ∈ G, ∀ f ∈ G, ∀ g ∈ G, ¬ IsTriangle e f g

/-- Initial state: nothing sampled, all edges surviving, empty graph. -/
def initBlockState (V : Type*) [Fintype V] [DecidableEq V] : BlockState V where
  E := ∅
  Γ := allEdges V
  G := ∅
  hG_subset_E := Finset.empty_subset _
  hΓ_disjoint_E := Finset.disjoint_empty_right _
  hΓ_no_triangle := by intros _ _ _ hf; exact absurd hf (Finset.notMem_empty _)
  hG_triangle_free := by intros _ he; exact absurd he (Finset.notMem_empty _)

/-- A forbidden configuration: a pair of `X`-edges completing a triangle with an
`ℰ`-edge (Kim's `Λ(X)`, (2)), or a triple of `X`-edges forming a triangle
(Kim's `Δ(X)`, (3)). -/
def IsForbidden (E X : Finset (Edge V)) (F : Finset (Edge V)) : Prop :=
  F ⊆ X ∧
    ((∃ e f : Edge V, F = {e, f} ∧ ∃ g ∈ E, IsTriangle e f g)
      ∨ (∃ e f g : Edge V, F = {e, f, g} ∧ IsTriangle e f g))

noncomputable instance (E X : Finset (Edge V)) (F : Finset (Edge V)) :
    Decidable (IsForbidden E X F) := Classical.dec _

/-- All forbidden configurations inside `X`. -/
noncomputable def forbiddenFams (E X : Finset (Edge V)) :
    Finset (Finset (Edge V)) := by
  classical
  exact X.powerset.filter (fun F => IsForbidden E X F)

lemma mem_forbiddenFams {E X F : Finset (Edge V)} :
    F ∈ forbiddenFams E X ↔ IsForbidden E X F := by
  classical
  show F ∈ Finset.filter _ _ ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_powerset.mpr h.1, h⟩⟩

/-- A collection of configurations is *disjoint* in Kim's sense. -/
def PairwiseDisjointFam (C : Finset (Finset (Edge V))) : Prop :=
  ∀ F ∈ C, ∀ G ∈ C, F ≠ G → Disjoint F G

noncomputable instance (C : Finset (Finset (Edge V))) :
    Decidable (PairwiseDisjointFam C) := Classical.dec _

/-- **A maximal disjoint subcollection exists.** Take one of largest
cardinality among the pairwise-disjoint subcollections; if some configuration
were disjoint from all of it, adding that configuration would give a larger
one. -/
lemma exists_maximal_disjoint (S : Finset (Finset (Edge V))) :
    ∃ C ⊆ S, PairwiseDisjointFam C ∧
      ∀ F ∈ S, F ∉ C → ∃ G ∈ C, ¬ Disjoint F G := by
  classical
  set P : Finset (Finset (Finset (Edge V))) :=
    S.powerset.filter (fun C => PairwiseDisjointFam C) with hP
  have hne : (∅ : Finset (Finset (Edge V))) ∈ P := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by simp), ?_⟩
    intro F hF; exact absurd hF (by simp)
  obtain ⟨C, hCP, hCmax⟩ := P.exists_max_image Finset.card ⟨_, hne⟩
  obtain ⟨hCS, hCdisj⟩ := Finset.mem_filter.mp hCP
  refine ⟨C, Finset.mem_powerset.mp hCS, hCdisj, ?_⟩
  intro F hFS hFC
  by_contra hcon
  push_neg at hcon
  have hins : insert F C ∈ P := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro G hG
      rcases Finset.mem_insert.mp hG with rfl | hG
      · exact hFS
      · exact (Finset.mem_powerset.mp hCS) hG
    · intro G hG G' hG' hne'
      rcases Finset.mem_insert.mp hG with h1 | h1
      · rcases Finset.mem_insert.mp hG' with h2 | h2
        · exact absurd (h1.trans h2.symm) hne'
        · rw [h1]; exact hcon G' h2
      · rcases Finset.mem_insert.mp hG' with h2 | h2
        · rw [h2]; exact (hcon G h1).symm
        · exact hCdisj G h1 G' h2 hne'
  have := hCmax _ hins
  rw [Finset.card_insert_of_notMem hFC] at this
  omega

/-- Kim's `ℱ` of (BC 3): a maximal disjoint collection of forbidden
configurations inside `X`. -/
noncomputable def kimFam (E X : Finset (Edge V)) : Finset (Finset (Edge V)) :=
  (exists_maximal_disjoint (forbiddenFams E X)).choose

lemma kimFam_spec (E X : Finset (Edge V)) :
    kimFam E X ⊆ forbiddenFams E X ∧ PairwiseDisjointFam (kimFam E X)
      ∧ ∀ F ∈ forbiddenFams E X, F ∉ kimFam E X →
          ∃ G ∈ kimFam E X, ¬ Disjoint F G :=
  (exists_maximal_disjoint (forbiddenFams E X)).choose_spec

/-- `E(ℱ)`: the edges Kim deletes from `X`. -/
noncomputable def kimRemoved (E X : Finset (Edge V)) : Finset (Edge V) :=
  (kimFam E X).biUnion id

/-- **Maximality of `ℱ`**: every forbidden configuration meets a deleted edge. -/
lemma forbidden_meets_removed (E X : Finset (Edge V)) {F : Finset (Edge V)}
    (hF : IsForbidden E X F) (hFne : F.Nonempty) :
    ∃ e ∈ F, e ∈ kimRemoved E X := by
  classical
  obtain ⟨hsub, hdisj, hmax⟩ := kimFam_spec E X
  by_cases hFC : F ∈ kimFam E X
  · obtain ⟨e, he⟩ := hFne
    exact ⟨e, he, Finset.mem_biUnion.mpr ⟨F, hFC, he⟩⟩
  · obtain ⟨G, hGC, hGnd⟩ := hmax F (mem_forbiddenFams.mpr hF) hFC
    rw [Finset.not_disjoint_iff] at hGnd
    obtain ⟨x, hxF, hxG⟩ := hGnd
    exact ⟨x, hxF, Finset.mem_biUnion.mpr ⟨G, hGC, hxG⟩⟩

/-- The two-edge forbidden configurations really are forbidden. -/
lemma isForbidden_pair {E X : Finset (Edge V)} {e f g : Edge V}
    (he : e ∈ X) (hf : f ∈ X) (hg : g ∈ E) (htri : IsTriangle e f g) :
    IsForbidden E X {e, f} := by
  refine ⟨?_, Or.inl ⟨e, f, rfl, g, hg, htri⟩⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact he
  · rw [Finset.mem_singleton] at hx; rw [hx]; exact hf

/-- The three-edge forbidden configurations really are forbidden. -/
lemma isForbidden_triple {E X : Finset (Edge V)} {e f g : Edge V}
    (he : e ∈ X) (hf : f ∈ X) (hg : g ∈ X) (htri : IsTriangle e f g) :
    IsForbidden E X {e, f, g} := by
  refine ⟨?_, Or.inr ⟨e, f, g, rfl, htri⟩⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact he
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hf
  · rw [Finset.mem_singleton] at hx; rw [hx]; exact hg

lemma pair_removed_contra {E X : Finset (Edge V)} {e f g : Edge V}
    (he : e ∈ X) (hf : f ∈ X) (hg : g ∈ E) (htri : IsTriangle e f g)
    (hne : e ∉ kimRemoved E X) (hnf : f ∉ kimRemoved E X) : False := by
  classical
  obtain ⟨x, hx, hxrem⟩ := forbidden_meets_removed E X
    (isForbidden_pair he hf hg htri) ⟨e, by simp⟩
  rcases Finset.mem_insert.mp hx with h | h
  · exact hne (h ▸ hxrem)
  · rw [Finset.mem_singleton] at h; exact hnf (h ▸ hxrem)

lemma triple_removed_contra {E X : Finset (Edge V)} {e f g : Edge V}
    (he : e ∈ X) (hf : f ∈ X) (hg : g ∈ X) (htri : IsTriangle e f g)
    (hne : e ∉ kimRemoved E X) (hnf : f ∉ kimRemoved E X)
    (hng : g ∉ kimRemoved E X) : False := by
  classical
  obtain ⟨x, hx, hxrem⟩ := forbidden_meets_removed E X
    (isForbidden_triple he hf hg htri) ⟨e, by simp⟩
  rcases Finset.mem_insert.mp hx with h | h
  · exact hne (h ▸ hxrem)
  rcases Finset.mem_insert.mp h with h | h
  · exact hnf (h ▸ hxrem)
  · rw [Finset.mem_singleton] at h; exact hng (h ▸ hxrem)

/-- One deterministic step `BC1–BC3` of Kim's block construction.

Construction:
* `Eᵢ₊₁ := Eᵢ ∪ X`
* `Gᵢ₊₁ := Gᵢ ∪ (X \ E(ℱ))`, with `ℱ` a maximal disjoint collection of
  forbidden pairs and triples (Kim's (BC 3))
* `Γᵢ₊₁ := {e ∈ Γᵢ ∖ X : ∀ f g ∈ Eᵢ₊₁, ¬ IsTriangle e f g}`

Note that `Γ` is *monotone decreasing* (`Γᵢ₊₁ ⊆ Γᵢ`), as in Kim §2: each step
removes the selected edges `X` together with everything that would now close a
triangle. (Rebuilding `Γ` maximally from `allEdges` would be unfaithful: it can
*grow* `Γ`, which breaks Property 2 propagation.)

The filter on `Gᵢ₊₁`'s `X`-component removes any new edge that participates in
a forbidden pair (with a previous-stage edge in `E`) or a forbidden triple
(with two other new edges). This is sufficient for triangle-freeness: in any
triangle `{e, f, g} ⊆ Eᵢ₊₁`, the symmetry of `IsTriangle` lets us rotate the
triple to apply maximality of `ℱ` or the previous-stage invariant
`hΓ_no_triangle`. (The maximal-disjoint refinement Kim uses is needed only
for the probabilistic Properties 4, 5 of the Main Lemma.) -/
noncomputable def blockStep (s : BlockState V) (X : Finset (Edge V))
    (hX : X ⊆ s.Γ) : BlockState V := by
  classical
  refine
    { E := s.E ∪ X,
      Γ := (s.Γ \ X).filter
        (fun e => ∀ f ∈ s.E ∪ X, ∀ g ∈ s.E ∪ X, ¬ IsTriangle e f g),
      G := s.G ∪ (X \ kimRemoved s.E X),
      hG_subset_E := ?_, hΓ_disjoint_E := ?_,
      hΓ_no_triangle := ?_, hG_triangle_free := ?_ }
  · -- G ⊆ E
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact Finset.mem_union_left _ (s.hG_subset_E he)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp he).1
  · -- Γ disjoint from E ∪ X
    rw [Finset.disjoint_left]
    intro e he he'
    have hmem := Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1
    rcases Finset.mem_union.mp he' with h | h
    · exact Finset.disjoint_left.mp s.hΓ_disjoint_E hmem.1 h
    · exact hmem.2 h
  · -- Γ no-triangle
    intro e he f hf g hg hTri
    exact (Finset.mem_filter.mp he).2 f hf g hg hTri
  · -- G triangle-free
    intro e he f hf g hg hTri
    -- X is disjoint from s.E (via s.hΓ_disjoint_E + hX).
    have h_X_not_E : ∀ x ∈ X, x ∉ s.E := fun x hx hxE =>
      Finset.disjoint_left.mp s.hΓ_disjoint_E (hX hx) hxE
    -- Decompose membership in G_{i+1}: each of e, f, g is in s.G or X-filter.
    have h_decomp : ∀ x ∈ s.G ∪ (X \ kimRemoved s.E X),
        x ∈ s.G ∨ (x ∈ X ∧ x ∉ kimRemoved s.E X) := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr ⟨(Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
    -- Per-edge: in s.G (hence s.E) or in X.
    have h_e_loc := h_decomp e he
    have h_f_loc := h_decomp f hf
    have h_g_loc := h_decomp g hg
    -- Eight cases; use rotate to normalise.
    rcases h_e_loc with he_G | ⟨he_X, he_filt⟩
    all_goals rcases h_f_loc with hf_G | ⟨hf_X, hf_filt⟩
    all_goals rcases h_g_loc with hg_G | ⟨hg_X, hg_filt⟩
    -- Case 1: e, f, g all in s.G.
    · exact s.hG_triangle_free e he_G f hf_G g hg_G hTri
    -- Case 2: e, f ∈ G ⊆ E; g ∈ X. Then g ∈ X ⊆ s.Γ, triangle has 2 E-edges.
    · exact s.hΓ_no_triangle g (hX hg_X) e (s.hG_subset_E he_G)
        f (s.hG_subset_E hf_G) hTri.rotate'
    -- Case 3: e, g ∈ G; f ∈ X.
    · exact s.hΓ_no_triangle f (hX hf_X) e (s.hG_subset_E he_G)
        g (s.hG_subset_E hg_G) hTri.swap12
    -- Case 4: e ∈ G ⊆ E; f, g ∈ X — a forbidden Λ-pair `{f, g}`.
    · exact pair_removed_contra hf_X hg_X (s.hG_subset_E he_G) hTri.rotate
        hf_filt hg_filt
    -- Case 5: e ∈ X; f, g ∈ G. Triangle with 2 E-edges.
    · exact s.hΓ_no_triangle e (hX he_X) f (s.hG_subset_E hf_G)
        g (s.hG_subset_E hg_G) hTri
    -- Case 6: e, g ∈ X; f ∈ G ⊆ E — a forbidden Λ-pair `{e, g}`.
    · exact pair_removed_contra he_X hg_X (s.hG_subset_E hf_G) hTri.swap23
        he_filt hg_filt
    -- Case 7: e, f ∈ X; g ∈ G ⊆ E — a forbidden Λ-pair `{e, f}`.
    · exact pair_removed_contra he_X hf_X (s.hG_subset_E hg_G) hTri
        he_filt hf_filt
    -- Case 8: all in X — a forbidden Δ-triple `{e, f, g}`.
    · exact triple_removed_contra he_X hf_X hg_X hTri he_filt hf_filt hg_filt

end Phase2

/-! ## Phase 3 — Spencer ODE, parameters, and Properties 1–8

`Ψ : ℝ → ℝ` is defined implicitly by `∫₀^{Ψ(x)} exp(ξ²) dξ = x`. It satisfies
`Ψ'(x) = exp(-Ψ²(x))` and `Ψ(x) ≈ √log x` for large `x`. With `θ := (log n)⁻²`
and `δ := 1/17 − 10⁻⁵`, the discretised parameters are

  `bᵢ := Ψ'(iθ) = exp(-Ψ²(iθ))`,
  `aᵢ := ∑_{j<i} bⱼ θ`,
  `μᵢ := 1 - 18 aᵢ θ - aᵢ / (3 √log n)`.

The eight Properties of Kim §2 bound (with high probability) the following
quantities at stage `i`:

  1. `d_{ℰᵢ}(v) ≤ aᵢ √n + i n^{1/4} log n` for all `v`,
  2. `d_{Γᵢ}(v) ≤ bᵢ n` for all `v`,
  3. `|N_{ℰᵢ}(v) ∩ N_{ℰᵢ}(w)| ≤ 3 i log n` for all `v ≠ w`,
  4. `d_{Λᵢ}(eᵥw, v) ≤ bᵢ (aᵢ + 5θ) √n` for all `eᵥw ∈ Γᵢ`,
  5. `d_{Δᵢ}(e) ≤ bᵢ² n` for all `e ∈ Γᵢ`,
  6. `|Γᵢ(A,B)| ≤ bᵢ |A| |B|` for disjoint `A,B` of size `≥ θ²bᵢ²√n`,
  7. `|Γᵢ(T)| ≥ bᵢ μᵢ (t choose 2)` for all `T ∈ 𝒯ᵢ`,
  8. `|𝒯ᵢ| ≤ nⁱ (n choose t) exp(-(1-ε) ∑_{j<i} bⱼμⱼθ/√n · (t choose 2))`
     with `ε := (log log n)^{-1/4}` and `t := ⌈9 √(n log n)⌉`.

The **Main Lemma 2.1** says: if `(ℰₖ, Γₖ, Gₖ)` satisfies (9) and Properties
1–8 at index `k`, then some `(ℰₖ₊₁, Γₖ₊₁, Gₖ₊₁)` produced by `Step` also
satisfies them at index `k+1`. (The proof is Kim §5; here we only state.)
-/

section Phase3

/-! ### Spencer's ODE solution `Ψ`

`Ψ : ℝ → ℝ` is the solution to `Ψ'(x) = exp(-Ψ²(x))` with `Ψ(0) = 0`,
defined implicitly by `∫₀^{Ψ(x)} exp(ξ²) dξ = x` (Kim eq. (6)). For our
purposes `Ψ` is the inverse of `Φ(t) := ∫₀^t exp(ξ²) dξ`. Since `exp(ξ²) > 0`,
`Φ` is strictly monotone, hence injective, hence `Ψ := Function.invFun Φ`
satisfies `Ψ ∘ Φ = id`.

For Kim's argument we need all of: (a) `Ψ(0) = 0`, (b) `Ψ'(x) = exp(-Ψ²(x))`
— via `HasDerivAt.of_local_left_inverse`, plus surjectivity of `Φ` for
`Φ(Ψ(x)) = x` — and (c) the two-sided bound `√log x − 1 ≤ Ψ(x) ≤ √log x + 1`
for `x ≥ 1` (Kim eq. (16)), which is
`spencerPsi_ge_sqrt_log_sub_one`/`spencerPsi_le_sqrt_log_add_one`.  All three
are proved below.
-/

/-- The integral `Φ(t) = ∫₀^t exp(ξ²) dξ`. Strictly increasing on `ℝ`, hence
injective; `Ψ` is its inverse (via `Function.invFun`). -/
noncomputable def spencerPhi (t : ℝ) : ℝ := ∫ ξ in (0 : ℝ)..t, Real.exp (ξ ^ 2)

/-- `Φ(0) = 0`. -/
lemma spencerPhi_zero : spencerPhi 0 = 0 := by
  unfold spencerPhi
  simp

/-- The integrand `exp(ξ²)` is continuous. -/
private lemma continuous_expSq : Continuous (fun ξ : ℝ => Real.exp (ξ ^ 2)) :=
  Real.continuous_exp.comp (continuous_pow 2)

/-- `Φ(y) ≤ y·e^{y²}` for `y ≥ 0`: bound the integrand by its maximum. -/
lemma spencerPhi_le_mul_exp {y : ℝ} (hy : 0 ≤ y) :
    spencerPhi y ≤ y * Real.exp (y ^ 2) := by
  unfold spencerPhi
  have hmono : ∀ ξ ∈ Set.Icc (0 : ℝ) y,
      Real.exp (ξ ^ 2) ≤ Real.exp (y ^ 2) := by
    intro ξ hξ
    exact Real.exp_le_exp.mpr (by nlinarith [hξ.1, hξ.2])
  have := intervalIntegral.integral_mono_on hy
    (continuous_expSq.intervalIntegrable 0 y)
    (intervalIntegrable_const (μ := MeasureTheory.volume)
      (a := (0 : ℝ)) (b := y) (c := Real.exp (y ^ 2))) hmono
  simpa using this

/-- `Φ(y) ≥ e^{(y-1)²}` for `y ≥ 1`: the last unit interval already
contributes that much. -/
lemma spencerPhi_ge_exp {y : ℝ} (hy : 1 ≤ y) :
    Real.exp ((y - 1) ^ 2) ≤ spencerPhi y := by
  have hy0 : (0 : ℝ) ≤ y - 1 := by linarith
  have hsplit : spencerPhi y
      = spencerPhi (y - 1) + ∫ ξ in (y - 1)..y, Real.exp (ξ ^ 2) := by
    unfold spencerPhi
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (continuous_expSq.intervalIntegrable 0 (y - 1))
      (continuous_expSq.intervalIntegrable (y - 1) y)]
  have hphi_nonneg : 0 ≤ spencerPhi (y - 1) := by
    unfold spencerPhi
    exact intervalIntegral.integral_nonneg hy0 (fun _ _ => (Real.exp_pos _).le)
  have hlow : Real.exp ((y - 1) ^ 2) ≤ ∫ ξ in (y - 1)..y, Real.exp (ξ ^ 2) := by
    have hmono : ∀ ξ ∈ Set.Icc (y - 1) y,
        Real.exp ((y - 1) ^ 2) ≤ Real.exp (ξ ^ 2) := by
      intro ξ hξ
      exact Real.exp_le_exp.mpr (by nlinarith [hξ.1, hξ.2])
    have hle : y - 1 ≤ y := by linarith
    have := intervalIntegral.integral_mono_on hle
      (intervalIntegrable_const (μ := MeasureTheory.volume)
        (a := y - 1) (b := y) (c := Real.exp ((y - 1) ^ 2)))
      (continuous_expSq.intervalIntegrable (y - 1) y) hmono
    simpa using this
  linarith


/-- `Φ` is strictly monotone on `ℝ`. -/
lemma spencerPhi_strictMono : StrictMono spencerPhi := by
  intro a b hab
  have h_pos : 0 < ∫ ξ in a..b, Real.exp (ξ ^ 2) :=
    intervalIntegral.integral_pos hab continuous_expSq.continuousOn
      (fun _ _ => (Real.exp_pos _).le) ⟨a, ⟨le_refl _, hab.le⟩, Real.exp_pos _⟩
  have h_diff : spencerPhi b - spencerPhi a = ∫ ξ in a..b, Real.exp (ξ ^ 2) := by
    unfold spencerPhi
    exact intervalIntegral.integral_interval_sub_left
      (continuous_expSq.intervalIntegrable 0 b)
      (continuous_expSq.intervalIntegrable 0 a)
  linarith

/-- `Φ` is injective. -/
lemma spencerPhi_injective : Function.Injective spencerPhi :=
  spencerPhi_strictMono.injective

/-- Spencer's `Ψ`: the inverse of `spencerPhi`. Implemented via
`Function.invFun`, which on the range of `spencerPhi` returns the unique
preimage (this is well-defined by injectivity). -/
noncomputable def spencerPsi : ℝ → ℝ := Function.invFun spencerPhi

/-- `Ψ` is a left inverse of `Φ`: `Ψ(Φ(t)) = t`. -/
lemma spencerPsi_apply_phi (t : ℝ) : spencerPsi (spencerPhi t) = t :=
  Function.leftInverse_invFun spencerPhi_injective t

/-- `Ψ(0) = 0`. -/
theorem spencerPsi_zero : spencerPsi 0 = 0 := by
  have h := spencerPsi_apply_phi 0
  rw [spencerPhi_zero] at h
  exact h

/-- `Φ` is continuous (FTC). -/
lemma spencerPhi_continuous : Continuous spencerPhi :=
  intervalIntegral.continuous_primitive
    (fun a b => continuous_expSq.intervalIntegrable a b) 0

/-- For `t ≥ 0`, `Φ(t) ≥ t`. (Since the integrand `exp(ξ²) ≥ 1` for all `ξ`.) -/
lemma spencerPhi_ge_self_of_nonneg {t : ℝ} (ht : 0 ≤ t) : t ≤ spencerPhi t := by
  have h_mono :
      (∫ _ in (0:ℝ)..t, (1 : ℝ)) ≤ ∫ ξ in (0:ℝ)..t, Real.exp (ξ ^ 2) := by
    apply intervalIntegral.integral_mono_on ht intervalIntegrable_const
      (continuous_expSq.intervalIntegrable _ _)
    intro x _
    exact Real.one_le_exp (sq_nonneg x)
  have h_const : (∫ _ in (0:ℝ)..t, (1 : ℝ)) = t := by
    simp [intervalIntegral.integral_const, ht]
  unfold spencerPhi
  linarith

/-- For `t ≤ 0`, `Φ(t) ≤ t`. -/
lemma spencerPhi_le_self_of_nonpos {t : ℝ} (ht : t ≤ 0) : spencerPhi t ≤ t := by
  have h_mono :
      (∫ _ in t..(0:ℝ), (1 : ℝ)) ≤ ∫ ξ in t..(0:ℝ), Real.exp (ξ ^ 2) := by
    apply intervalIntegral.integral_mono_on ht intervalIntegrable_const
      (continuous_expSq.intervalIntegrable _ _)
    intro x _
    exact Real.one_le_exp (sq_nonneg x)
  have h_const : (∫ _ in t..(0:ℝ), (1 : ℝ)) = -t := by
    simp [intervalIntegral.integral_const]
  have h_phi : spencerPhi t = -(∫ ξ in t..(0:ℝ), Real.exp (ξ ^ 2)) := by
    unfold spencerPhi
    rw [intervalIntegral.integral_symm]
  linarith

/-- `Φ(t) → ∞` as `t → ∞`. -/
lemma spencerPhi_tendsto_atTop : Filter.Tendsto spencerPhi Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono' Filter.atTop
    (Filter.eventually_atTop.mpr ⟨0, fun t ht => spencerPhi_ge_self_of_nonneg ht⟩)
  exact Filter.tendsto_id

/-- `Φ(t) → -∞` as `t → -∞`. -/
lemma spencerPhi_tendsto_atBot : Filter.Tendsto spencerPhi Filter.atBot Filter.atBot := by
  apply Filter.tendsto_atBot_mono' Filter.atBot
    (Filter.eventually_atBot.mpr ⟨0, fun t ht => spencerPhi_le_self_of_nonpos ht⟩)
  exact Filter.tendsto_id

/-- `Φ` is surjective onto `ℝ` (by IVT). -/
lemma spencerPhi_surjective : Function.Surjective spencerPhi := by
  intro y
  obtain ⟨M, hM⟩ :=
    (spencerPhi_tendsto_atTop.eventually_ge_atTop y).exists
  obtain ⟨m, hm⟩ :=
    (spencerPhi_tendsto_atBot.eventually_le_atBot y).exists
  have hmM : m ≤ M := by
    by_contra h
    push_neg at h
    have : spencerPhi M < spencerPhi m := spencerPhi_strictMono h
    linarith
  obtain ⟨t, _, ht⟩ :=
    intermediate_value_Icc hmM spencerPhi_continuous.continuousOn ⟨hm, hM⟩
  exact ⟨t, ht⟩

/-- `Ψ` is the right inverse of `Φ`: `Φ(Ψ(y)) = y`. -/
lemma spencerPhi_apply_psi (y : ℝ) : spencerPhi (spencerPsi y) = y := by
  obtain ⟨t, ht⟩ := spencerPhi_surjective y
  rw [← ht, spencerPsi_apply_phi]

/-- `Φ` as an order isomorphism `ℝ ≃o ℝ`. -/
noncomputable def spencerPhiOrderIso : ℝ ≃o ℝ :=
  spencerPhi_strictMono.orderIsoOfSurjective spencerPhi spencerPhi_surjective

/-- `Ψ` coincides with `spencerPhiOrderIso.symm`. -/
lemma spencerPsi_eq_orderIso_symm : (spencerPhiOrderIso.symm : ℝ → ℝ) = spencerPsi := by
  funext y
  apply spencerPhi_injective
  show spencerPhi (spencerPhiOrderIso.symm y) = spencerPhi (spencerPsi y)
  rw [spencerPhi_apply_psi]
  -- Goal: spencerPhi (spencerPhiOrderIso.symm y) = y
  -- spencerPhi = spencerPhiOrderIso as functions, by coe_orderIsoOfSurjective
  change (spencerPhiOrderIso : ℝ → ℝ) (spencerPhiOrderIso.symm y) = y
  exact spencerPhiOrderIso.apply_symm_apply y

/-- `Ψ` is continuous. -/
lemma spencerPsi_continuous : Continuous spencerPsi := by
  rw [← spencerPsi_eq_orderIso_symm]
  exact spencerPhiOrderIso.symm.continuous

/-- `Ψ` is differentiable on `ℝ` (not just `[0, ∞)`) with `Ψ'(x) = exp(-Ψ²(x))`. -/
theorem hasDerivAt_spencerPsi (x : ℝ) :
    HasDerivAt spencerPsi (Real.exp (-(spencerPsi x) ^ 2)) x := by
  -- FTC at t = Ψ x: Φ'(t) = exp(t²).
  have h_phi_deriv :
      HasDerivAt spencerPhi (Real.exp ((spencerPsi x) ^ 2)) (spencerPsi x) := by
    have := intervalIntegral.integral_hasDerivAt_right
      (continuous_expSq.intervalIntegrable 0 (spencerPsi x))
      continuous_expSq.aestronglyMeasurable.stronglyMeasurableAtFilter
      continuous_expSq.continuousAt
    exact this
  -- exp((Ψx)²) ≠ 0
  have h_ne : Real.exp ((spencerPsi x) ^ 2) ≠ 0 := (Real.exp_pos _).ne'
  -- Φ ∘ Ψ = id globally
  have h_right_inv : ∀ᶠ y in nhds x, spencerPhi (spencerPsi y) = y :=
    Filter.Eventually.of_forall spencerPhi_apply_psi
  -- Inverse-function derivative theorem
  have h_psi_deriv :
      HasDerivAt spencerPsi (Real.exp ((spencerPsi x) ^ 2))⁻¹ x :=
    h_phi_deriv.of_local_left_inverse spencerPsi_continuous.continuousAt h_ne h_right_inv
  -- Rewrite (exp t)⁻¹ = exp(-t)
  have h_inv_eq : (Real.exp ((spencerPsi x) ^ 2))⁻¹ = Real.exp (-(spencerPsi x) ^ 2) := by
    rw [← Real.exp_neg]
  rw [← h_inv_eq]
  exact h_psi_deriv

/-- `Ψ` is strictly monotone (inheriting from `Φ`). -/
lemma spencerPsi_strictMono : StrictMono spencerPsi := by
  rw [← spencerPsi_eq_orderIso_symm]
  exact spencerPhiOrderIso.symm.strictMono

/-- `Ψ(x) ≥ 0` for `x ≥ 0`. -/
lemma spencerPsi_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ spencerPsi x := by
  rw [← spencerPsi_zero]
  exact spencerPsi_strictMono.monotone hx

/-- **Kim (16), upper half**: `Ψ(x) ≤ √(log x) + 1` for `x ≥ 1`.
Since `Φ(√(log x)+1) ≥ e^{log x} = x = Φ(Ψ(x))` and `Φ` is strictly
monotone. -/
lemma spencerPsi_le_sqrt_log_add_one {x : ℝ} (hx : 1 ≤ x) :
    spencerPsi x ≤ Real.sqrt (Real.log x) + 1 := by
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  have hy1 : (1 : ℝ) ≤ Real.sqrt (Real.log x) + 1 := by
    have := Real.sqrt_nonneg (Real.log x); linarith
  have hge := spencerPhi_ge_exp hy1
  have heq : Real.exp ((Real.sqrt (Real.log x) + 1 - 1) ^ 2) = x := by
    have hsq : (Real.sqrt (Real.log x) + 1 - 1) ^ 2 = Real.log x := by
      rw [show Real.sqrt (Real.log x) + 1 - 1 = Real.sqrt (Real.log x) by ring]
      exact Real.sq_sqrt hlog_nn
    rw [hsq, Real.exp_log (by linarith)]
  rw [heq] at hge
  have hpsi : spencerPhi (spencerPsi x) = x := spencerPhi_apply_psi x
  have hfinal : spencerPhi (spencerPsi x)
      ≤ spencerPhi (Real.sqrt (Real.log x) + 1) := by
    rw [hpsi]; exact hge
  exact spencerPhi_strictMono.le_iff_le.mp hfinal

/-- **Kim (16), lower half**: `√(log x) − 1 ≤ Ψ(x)` for `x ≥ 1`.
Since `x = Φ(Ψ(x)) ≤ Ψ(x)e^{Ψ(x)²} ≤ e^{(Ψ(x)+1)²}`. -/
lemma spencerPsi_ge_sqrt_log_sub_one {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt (Real.log x) - 1 ≤ spencerPsi x := by
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  have hpsi_nn : 0 ≤ spencerPsi x := spencerPsi_nonneg (by linarith)
  set P := spencerPsi x with hP
  have hle := spencerPhi_le_mul_exp hpsi_nn
  have hphi : spencerPhi P = x := spencerPhi_apply_psi x
  rw [hphi] at hle
  -- P ≤ e^{2P+1}
  have hPe : P ≤ Real.exp (2 * P + 1) := by
    have := Real.add_one_le_exp (2 * P + 1); linarith
  have hprod : P * Real.exp (P ^ 2)
      ≤ Real.exp (2 * P + 1) * Real.exp (P ^ 2) :=
    mul_le_mul_of_nonneg_right hPe (Real.exp_nonneg _)
  have hcomb : Real.exp (2 * P + 1) * Real.exp (P ^ 2) = Real.exp ((P + 1) ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hchain : x ≤ Real.exp ((P + 1) ^ 2) := by
    rw [← hcomb]; linarith
  have hlogle : Real.log x ≤ (P + 1) ^ 2 := by
    have := Real.log_le_log (by linarith) hchain
    rwa [Real.log_exp] at this
  have hsqrt : Real.sqrt (Real.log x) ≤ P + 1 := by
    rw [show P + 1 = Real.sqrt ((P + 1) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt hlogle
  linarith

/-- The block-construction parameter `θ := 1/(log n)²`. -/
noncomputable def theta (n : ℕ) : ℝ := 1 / Real.log n ^ 2

/-- `bᵢ := Ψ'(i θ) = exp(-Ψ²(i θ))`. -/
noncomputable def bSeq (n : ℕ) (i : ℕ) : ℝ :=
  Real.exp (-(spencerPsi ((i : ℝ) * theta n)) ^ 2)

/-- `aᵢ := ∑_{j < i} bⱼ θ`. Telescopes to `Ψ(i θ)` since `b_j = Ψ'(j θ)`. -/
noncomputable def aSeq (n : ℕ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range i, bSeq n j * theta n

/-- `μᵢ := 1 - 18 aᵢ θ - aᵢ / (3 √log n)` (Kim §2). -/
noncomputable def μSeq (n : ℕ) (i : ℕ) : ℝ :=
  1 - 18 * aSeq n i * theta n - aSeq n i / (3 * Real.sqrt (Real.log n))

/-- The target independence-number bound: `t := ⌈9 √(n log n)⌉`. -/
noncomputable def tParam (n : ℕ) : ℕ :=
  ⌈9 * Real.sqrt ((n : ℝ) * Real.log n)⌉₊

/-- Per-edge inclusion probability `θ/√n` for Kim's `X` sampling. -/
noncomputable def edgeProb (n : ℕ) : ℝ := theta n / Real.sqrt n

/-- `θ ≥ 0`. -/
lemma theta_nonneg (n : ℕ) : 0 ≤ theta n := by
  unfold theta; positivity

/-- `edgeProb n ≥ 0`. -/
lemma edgeProb_nonneg (n : ℕ) : 0 ≤ edgeProb n :=
  div_nonneg (theta_nonneg n) (Real.sqrt_nonneg _)

/-- `θ ≤ 1` once `log N ≥ 1`. -/
lemma theta_le_one {N : ℕ} (h : 1 ≤ Real.log N) : theta N ≤ 1 := by
  rw [theta, div_le_one (by nlinarith)]
  nlinarith

/-- `1 ≤ √N` for `N ≥ 1`. -/
lemma one_le_sqrt_cast {N : ℕ} (h : 1 ≤ N) : 1 ≤ Real.sqrt N := by
  have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  exact Real.sqrt_le_sqrt this

lemma sqrt_mul_edgeProb {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt N * edgeProb N = theta N := by
  rw [edgeProb, mul_div_cancel₀]
  linarith [one_le_sqrt_cast hN]
/-- `p = θ/√n ≤ 1`. -/
lemma edgeProb_le_one' {N : ℕ} (hlog : 1 ≤ Real.log N) (hN : 1 ≤ N) :
    edgeProb N ≤ 1 := by
  have hsq : (1 : ℝ) ≤ Real.sqrt N := one_le_sqrt_cast hN
  rw [edgeProb, div_le_one (by linarith)]
  linarith [theta_le_one hlog]

/-- `L^m = exp(m·log L)` for `L > 0`. -/
lemma pow_eq_exp_mul_log {L : ℝ} (hL : 0 < L) (m : ℕ) :
    L ^ m = Real.exp ((m : ℝ) * Real.log L) := by
  rw [← Real.exp_log hL, ← Real.exp_nat_mul, Real.log_exp]

/-- **The `(iii)` estimate**: with `q = θ²` and `l = ⌈log n⌉`,
`q^l ≤ n⁻³`.

Indeed `q^l = (log n)^{−4l} = exp(−4l·log log n)` and `l ≥ log n`, so the
exponent is at most `−4 log n·log log n ≤ −3 log n` once `log log n ≥ 1`. -/
lemma theta_sq_pow_le {N : ℕ} (hN : 1 ≤ N) (hlog : Real.exp 1 ≤ Real.log N) :
    (theta N ^ 2) ^ (⌈Real.log N⌉₊) ≤ ((N : ℝ) ^ (3 : ℕ))⁻¹ := by
  set L : ℝ := Real.log N with hLdef
  have he1 : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hL1 : (1 : ℝ) < L := lt_of_lt_of_le he1 hlog
  have hL0 : (0 : ℝ) < L := by linarith
  have hlogL : (1 : ℝ) ≤ Real.log L := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_le_log (by positivity) hlog
  set l : ℕ := ⌈L⌉₊ with hl
  have hlL : L ≤ (l : ℝ) := Nat.le_ceil L
  -- `θ² = (L⁴)⁻¹`
  have hθsq : theta N ^ 2 = (L ^ (4 : ℕ))⁻¹ := by
    rw [theta, hLdef, div_pow, one_pow, ← pow_mul, one_div]
  -- `N³ ≤ (L⁴)^l`
  have hNpos : (0 : ℝ) < N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hkey : ((N : ℝ) ^ (3 : ℕ)) ≤ (L ^ (4 : ℕ)) ^ l := by
    rw [pow_eq_exp_mul_log hNpos 3, ← pow_mul,
      pow_eq_exp_mul_log hL0 (4 * l)]
    refine Real.exp_le_exp.mpr ?_
    have h4l : (4 : ℝ) * L ≤ ((4 * l : ℕ) : ℝ) := by
      push_cast; linarith
    calc (3 : ℝ) * L ≤ 4 * L * 1 := by linarith
      _ ≤ ((4 * l : ℕ) : ℝ) * Real.log L := by
          refine mul_le_mul h4l hlogL (by norm_num) ?_
          push_cast; linarith
  have hlhs : (theta N ^ 2) ^ l = ((L ^ (4 * l))⁻¹ : ℝ) := by
    rw [hθsq, inv_pow, ← pow_mul]
  rw [hlhs]
  have hpos : (0 : ℝ) < (N : ℝ) ^ (3 : ℕ) := by positivity
  have hposL : (0 : ℝ) < L ^ (4 * l) := by positivity
  rw [inv_le_inv₀ hposL hpos, pow_mul]
  exact hkey






/-- `θ > 0` for `n ≥ 2`. -/
lemma theta_pos {n : ℕ} (hn : 2 ≤ n) : 0 < theta n := by
  unfold theta
  have h_log_pos : 0 < Real.log n := by
    apply Real.log_pos
    exact_mod_cast (by linarith : 1 < n)
  positivity


/-- `bᵢ > 0`. -/
lemma bSeq_pos (n : ℕ) (i : ℕ) : 0 < bSeq n i := Real.exp_pos _

/-- `aᵢ ≥ 0`. -/
lemma aSeq_nonneg (n : ℕ) (i : ℕ) : 0 ≤ aSeq n i :=
  Finset.sum_nonneg fun j _ => mul_nonneg (bSeq_pos n j).le (theta_nonneg n)


/-- `aᵢ₊₁ = aᵢ + bᵢ · θ`. -/
lemma aSeq_succ (n : ℕ) (i : ℕ) : aSeq n (i + 1) = aSeq n i + bSeq n i * theta n := by
  unfold aSeq
  rw [Finset.sum_range_succ]

/-- `t·e^{-t} ≤ e^{-1}` for `t ≥ 0`: the classical maximum at `t = 1`.
Proof: `t ≤ e^{t-1}` (Bernoulli), so `t·e^{-t} ≤ e^{t-1}·e^{-t} = e^{-1}`. -/
lemma mul_exp_neg_le {t : ℝ} (ht : 0 ≤ t) : t * Real.exp (-t) ≤ Real.exp (-1) := by
  have hb : t ≤ Real.exp (t - 1) := by
    have := Real.add_one_le_exp (t - 1); linarith
  have hpos : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  calc t * Real.exp (-t) ≤ Real.exp (t - 1) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right hb hpos.le
    _ = Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring

/-- **Kim's `y²·exp(-y²) < 0.43`** (used for (10)). -/
lemma sq_mul_exp_neg_sq_lt (y : ℝ) :
    y ^ 2 * Real.exp (-(y ^ 2)) < 0.43 := by
  have h := mul_exp_neg_le (t := y ^ 2) (sq_nonneg y)
  have he : Real.exp (-1) < 0.43 := by
    rw [Real.exp_neg]
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    rw [inv_lt_comm₀ h2 (by norm_num)]
    linarith
  linarith

/-- **Kim's `y·exp(-y²) < 0.43`** (used for (10)). Squaring reduces it to
`t·e^{-2t} ≤ e^{-1}/2`, which is `mul_exp_neg_le` after `u = 2t`. -/
lemma mul_exp_neg_sq_lt {y : ℝ} (hy : 0 ≤ y) :
    y * Real.exp (-(y ^ 2)) < 0.43 := by
  have hexp2 : Real.exp (-(y ^ 2)) ^ 2 = Real.exp (-(2 * y ^ 2)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsq_eq : (y * Real.exp (-(y ^ 2))) ^ 2
      = (2 * y ^ 2) * Real.exp (-(2 * y ^ 2)) / 2 := by
    rw [mul_pow, hexp2]
    ring
  have hbound : (2 * y ^ 2) * Real.exp (-(2 * y ^ 2)) ≤ Real.exp (-1) :=
    mul_exp_neg_le (by positivity)
  have he : Real.exp (-1) / 2 < 0.43 ^ 2 := by
    rw [Real.exp_neg]
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have : (Real.exp 1)⁻¹ < 0.3698 := by
      rw [inv_lt_comm₀ h2 (by norm_num)]
      linarith
    nlinarith [this]
  have hnn : 0 ≤ y * Real.exp (-(y ^ 2)) := mul_nonneg hy (Real.exp_nonneg _)
  nlinarith [hsq_eq, hbound, he, hnn]


/-- **One-step increment bound for `Ψ`.** On `[jθ, (j+1)θ]` the derivative
`Ψ' = exp(-Ψ²)` is at most its left-endpoint value `bⱼ`, because `Ψ` is
increasing and nonnegative there. Hence `Ψ((j+1)θ) - Ψ(jθ) ≤ bⱼ θ`.

Proved by the usual monotonicity trick: `g(x) := bⱼ x - Ψ(x)` has `g' ≥ 0`. -/
lemma spencerPsi_step_le (N : ℕ) (j : ℕ) :
    spencerPsi (((j : ℝ) + 1) * theta N) - spencerPsi ((j : ℝ) * theta N)
      ≤ bSeq N j * theta N := by
  have hθ : 0 ≤ theta N := theta_nonneg N
  set c : ℝ := bSeq N j with hc_def
  set g : ℝ → ℝ := fun x => c * x - spencerPsi x with hg_def
  have hg_deriv : ∀ x : ℝ,
      HasDerivAt g (c - Real.exp (-(spencerPsi x) ^ 2)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => c * y) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    exact h1.sub (hasDerivAt_spencerPsi x)
  have hderiv_nonneg : ∀ x ∈ interior (Set.Ici ((j : ℝ) * theta N)),
      0 ≤ c - Real.exp (-(spencerPsi x) ^ 2) := by
    intro x hx
    rw [interior_Ici] at hx
    have hle : (j : ℝ) * theta N ≤ x := le_of_lt hx
    have hmono : spencerPsi ((j : ℝ) * theta N) ≤ spencerPsi x :=
      spencerPsi_strictMono.monotone hle
    have hnn : 0 ≤ spencerPsi ((j : ℝ) * theta N) :=
      spencerPsi_nonneg (mul_nonneg (Nat.cast_nonneg j) hθ)
    have hsq : (spencerPsi ((j : ℝ) * theta N)) ^ 2 ≤ (spencerPsi x) ^ 2 := by
      nlinarith [hmono, hnn]
    have hexp : Real.exp (-(spencerPsi x) ^ 2)
        ≤ Real.exp (-(spencerPsi ((j : ℝ) * theta N)) ^ 2) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [hc_def]
    unfold bSeq
    linarith
  have hmonoOn : MonotoneOn g (Set.Ici ((j : ℝ) * theta N)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
      (fun x _ => (hg_deriv x).continuousAt.continuousWithinAt)
      (fun x _ => (hg_deriv x).hasDerivWithinAt)
    exact hderiv_nonneg
  have hstep : ((j : ℝ) * theta N) ≤ ((j : ℝ) + 1) * theta N := by nlinarith
  have := hmonoOn (Set.left_mem_Ici) (Set.mem_Ici.mpr hstep) hstep
  simp only [hg_def] at this
  nlinarith [this]

/-- **Kim (10), upper half: `Ψ(iθ) ≤ aᵢ`.** Telescoping `spencerPsi_step_le`
over `j < i`, using `Ψ(0) = 0`. -/
lemma spencerPsi_le_aSeq (N : ℕ) (i : ℕ) :
    spencerPsi ((i : ℝ) * theta N) ≤ aSeq N i := by
  induction i with
  | zero => simp [aSeq, spencerPsi_zero]
  | succ m ih =>
      have hstep := spencerPsi_step_le N m
      have hsucc : aSeq N (m + 1) = aSeq N m + bSeq N m * theta N := aSeq_succ N m
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast, hsucc]
      linarith


/-- **Matching lower step bound**: `Ψ((j+1)θ) − Ψ(jθ) ≥ bⱼ₊₁ θ`, since on
`(-∞, (j+1)θ]` the derivative `Ψ' = exp(-Ψ²)` is at least its right-endpoint
value `bⱼ₊₁`. Same monotonicity trick with `h(x) := Ψ(x) − bⱼ₊₁ x`. -/
lemma spencerPsi_step_ge (N : ℕ) (j : ℕ) :
    bSeq N (j + 1) * theta N
      ≤ spencerPsi (((j : ℝ) + 1) * theta N) - spencerPsi ((j : ℝ) * theta N) := by
  have hθ : 0 ≤ theta N := theta_nonneg N
  have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  set R : ℝ := ((j : ℝ) + 1) * theta N with hR
  set c : ℝ := bSeq N (j + 1) with hc
  have hc_eq : c = Real.exp (-(spencerPsi R) ^ 2) := by
    rw [hc]; unfold bSeq; rw [hcast]
  set h : ℝ → ℝ := fun x => spencerPsi x - c * x with hh
  have hh_deriv : ∀ x : ℝ,
      HasDerivAt h (Real.exp (-(spencerPsi x) ^ 2) - c) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => c * y) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    exact (hasDerivAt_spencerPsi x).sub h1
  have hjR : (j : ℝ) * theta N ≤ R := by rw [hR]; nlinarith
  have hderiv_nonneg : ∀ x ∈ interior (Set.Icc ((j : ℝ) * theta N) R),
      0 ≤ Real.exp (-(spencerPsi x) ^ 2) - c := by
    intro x hx
    rw [interior_Icc] at hx
    obtain ⟨hxl, hxr⟩ := hx
    have hxR : x ≤ R := le_of_lt hxr
    have hmono : spencerPsi x ≤ spencerPsi R := spencerPsi_strictMono.monotone hxR
    have hxnn : 0 ≤ x :=
      le_trans (mul_nonneg (Nat.cast_nonneg j) hθ) (le_of_lt hxl)
    have hnn : 0 ≤ spencerPsi x := spencerPsi_nonneg hxnn
    have hsq : (spencerPsi x) ^ 2 ≤ (spencerPsi R) ^ 2 := by nlinarith [hmono, hnn]
    rw [hc_eq]
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hmonoOn : MonotoneOn h (Set.Icc ((j : ℝ) * theta N) R) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun x _ => (hh_deriv x).continuousAt.continuousWithinAt)
      (fun x _ => (hh_deriv x).hasDerivWithinAt)
    exact hderiv_nonneg
  have := hmonoOn (Set.left_mem_Icc.mpr hjR) (Set.right_mem_Icc.mpr hjR) hjR
  simp only [hh] at this
  rw [hR] at this ⊢
  nlinarith [this]

/-- **Kim (10), lower half**: `Ψ(iθ) ≥ aᵢ + bᵢθ − θ`, hence `aᵢ − Ψ(iθ) ≤ θ`.
Induction using `spencerPsi_step_ge` and `b₀ = 1`. -/
lemma aSeq_add_bSeq_sub_le_spencerPsi (N : ℕ) (i : ℕ) :
    aSeq N i + bSeq N i * theta N - theta N ≤ spencerPsi ((i : ℝ) * theta N) := by
  induction i with
  | zero =>
      have hb0 : bSeq N 0 = 1 := by
        unfold bSeq; norm_num [spencerPsi_zero]
      simp [aSeq, hb0, spencerPsi_zero]
  | succ m ih =>
      have hstep := spencerPsi_step_ge N m
      have hsucc : aSeq N (m + 1) = aSeq N m + bSeq N m * theta N := aSeq_succ N m
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast, hsucc]
      linarith

/-- **Kim (10), first part**: `0 ≤ aᵢ − Ψ(iθ) ≤ θ`. -/
lemma aSeq_sub_spencerPsi_bounds (N : ℕ) (i : ℕ) :
    0 ≤ aSeq N i - spencerPsi ((i : ℝ) * theta N)
      ∧ aSeq N i - spencerPsi ((i : ℝ) * theta N) ≤ theta N := by
  have hlo := spencerPsi_le_aSeq N i
  have hhi := aSeq_add_bSeq_sub_le_spencerPsi N i
  have hb_pos := bSeq_pos N i
  have hθ := theta_nonneg N
  exact ⟨by linarith, by nlinarith [hb_pos.le, hθ]⟩

/-- **Kim (10), part 4**: `bᵢ(aᵢ + 5θ)² < 1/2` once `θ ≤ 1/100`. -/
lemma bSeq_mul_aSeq_sq_lt_half {N : ℕ} (hθsmall : theta N ≤ 1 / 100) (i : ℕ) :
    bSeq N i * (aSeq N i + 5 * theta N) ^ 2 < 1 / 2 := by
  have hθ : 0 ≤ theta N := theta_nonneg N
  set P := spencerPsi ((i : ℝ) * theta N) with hP
  have hPnn : 0 ≤ P := spencerPsi_nonneg (mul_nonneg (Nat.cast_nonneg i) hθ)
  have hb : bSeq N i = Real.exp (-(P ^ 2)) := by rw [hP]; unfold bSeq; ring_nf
  have ha : aSeq N i ≤ P + theta N := by
    have := (aSeq_sub_spencerPsi_bounds N i).2; rw [← hP] at this; linarith
  have hann : 0 ≤ aSeq N i := aSeq_nonneg N i
  have hkey1 : P * Real.exp (-(P ^ 2)) < 0.43 := mul_exp_neg_sq_lt hPnn
  have hkey2 : P ^ 2 * Real.exp (-(P ^ 2)) < 0.43 := sq_mul_exp_neg_sq_lt P
  have hexp_le_one : Real.exp (-(P ^ 2)) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg P])
  have hexp_pos : 0 < Real.exp (-(P ^ 2)) := Real.exp_pos _
  rw [hb]
  -- (a+5θ)² ≤ (P+6θ)² = P² + 12θP + 36θ²
  have hsq : (aSeq N i + 5 * theta N) ^ 2 ≤ (P + 6 * theta N) ^ 2 := by
    have h1 : 0 ≤ aSeq N i + 5 * theta N := by linarith
    nlinarith [ha, hθ, h1]
  nlinarith [hsq, hkey1, hkey2, hexp_le_one, hexp_pos, hθ, hθsmall, hPnn]



/-- **Lemma 4.1 (arithmetic core).** Kim's padding arranges that the survival
probability of a `Γ`-edge is exactly `(1-p)^h` with `h·p = 2bᵢθ(aᵢ+5θ)`.
Given that, the two-sided Bernoulli bound plus (10) part 4 give

`1 − 2aᵢbᵢθ − 10bᵢθ² ≤ (1−p)^h ≤ 1 − 2aᵢbᵢθ − 9bᵢθ²`,

exactly the display in Kim's proof of Lemma 4.1. The upper bound uses
`2b²θ²(a+5θ)² ≤ bθ²`, i.e. `b(a+5θ)² ≤ 1/2`, which is (10) part 4. -/
lemma lemma41_bounds {N : ℕ} (i : ℕ) (hθsmall : theta N ≤ 1 / 100)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : ℕ) {err : ℝ} (herr : 0 ≤ err)
    (hhp_hi : (h : ℝ) * p
      ≤ 2 * bSeq N i * theta N * (aSeq N i + 5 * theta N))
    (hhp_lo : 2 * bSeq N i * theta N * (aSeq N i + 5 * theta N) - err
      ≤ (h : ℝ) * p) :
    1 - 2 * aSeq N i * bSeq N i * theta N - 10 * bSeq N i * theta N ^ 2
        ≤ (1 - p) ^ h
      ∧ (1 - p) ^ h
        ≤ 1 - 2 * aSeq N i * bSeq N i * theta N
          - 9 * bSeq N i * theta N ^ 2 + err := by
  have hθ : 0 ≤ theta N := theta_nonneg N
  have hb_pos := bSeq_pos N i
  have ha_nn := aSeq_nonneg N i
  obtain ⟨hlo, hhi⟩ := one_sub_pow_bounds hp0 hp1 h
  have hhp_nn : 0 ≤ (h : ℝ) * p := mul_nonneg (Nat.cast_nonneg h) hp0
  -- `2bθ(a+5θ)` expands to `2abθ + 10bθ²`
  have hexpand : 2 * bSeq N i * theta N * (aSeq N i + 5 * theta N)
      = 2 * aSeq N i * bSeq N i * theta N + 10 * bSeq N i * theta N ^ 2 := by
    ring
  -- `(h·p)²/2 ≤ 2b²θ²(a+5θ)² ≤ bθ²` by (10) part 4
  have hsq : (h : ℝ) ^ 2 * p ^ 2 / 2 ≤ bSeq N i * theta N ^ 2 := by
    have hkey : bSeq N i * (aSeq N i + 5 * theta N) ^ 2 < 1 / 2 :=
      bSeq_mul_aSeq_sq_lt_half hθsmall i
    have hsq_le : ((h : ℝ) * p) ^ 2
        ≤ (2 * bSeq N i * theta N * (aSeq N i + 5 * theta N)) ^ 2 := by
      refine sq_le_sq' ?_ hhp_hi
      nlinarith [hhp_nn, hb_pos.le, hθ, ha_nn]
    have hcast : (h : ℝ) ^ 2 * p ^ 2 = ((h : ℝ) * p) ^ 2 := by ring
    rw [hcast]
    have hbθ : 0 ≤ bSeq N i * theta N ^ 2 :=
      mul_nonneg hb_pos.le (sq_nonneg _)
    nlinarith [hsq_le, hkey, hb_pos.le, sq_nonneg (theta N), hθ, hbθ]
  constructor
  · linarith [hlo, hhp_hi, hexpand]
  · linarith [hhi, hhp_lo, hexpand, hsq]


/-- **Kim (15), discrete form**: `θ ∑_{j ≤ i} aⱼbⱼ ≤ Ψ(iθ)²/2 + (3/2)θΨ(iθ)`.

The induction closes with this indexing because the new term `a_{i+1}b_{i+1}θ`
is controlled by `spencerPsi_step_ge` *at index `i`*: with
`D := Ψ((i+1)θ) − Ψ(iθ)` we have `b_{i+1}θ ≤ D ≤ θ` and `a_{i+1} ≤ Ψ((i+1)θ)+θ`,
while the right-hand side increases by `QD − D²/2 + (3/2)θD`; the step reduces
to `D(D − θ) ≤ 0`. -/
lemma sum_aSeq_bSeq_le (N : ℕ) (i : ℕ) :
    ∑ j ∈ Finset.range (i + 1), aSeq N j * bSeq N j * theta N
      ≤ spencerPsi ((i : ℝ) * theta N) ^ 2 / 2
        + (3 / 2) * theta N * spencerPsi ((i : ℝ) * theta N) := by
  have hθ : 0 ≤ theta N := theta_nonneg N
  induction i with
  | zero =>
      have ha0 : aSeq N 0 = 0 := by simp [aSeq]
      rw [Finset.sum_range_one, ha0]
      simp [spencerPsi_zero]
  | succ m ih =>
      set P := spencerPsi ((m : ℝ) * theta N) with hP
      set Q := spencerPsi (((m : ℝ) + 1) * theta N) with hQ
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      have hPQ : P ≤ Q := spencerPsi_strictMono.monotone (by nlinarith)
      have hD_nn : 0 ≤ Q - P := by linarith
      have hb_le_one : bSeq N m ≤ 1 := by
        unfold bSeq
        rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
        exact Real.exp_le_exp.mpr
          (by nlinarith [sq_nonneg (spencerPsi ((m : ℝ) * theta N))])
      have hD_le : Q - P ≤ theta N := by
        have h := spencerPsi_step_le N m
        nlinarith [h, hb_le_one, hθ, bSeq_pos N m]
      have hstep_ge : bSeq N (m + 1) * theta N ≤ Q - P := spencerPsi_step_ge N m
      have ha : aSeq N (m + 1) ≤ Q + theta N := by
        have h := (aSeq_sub_spencerPsi_bounds N (m + 1)).2
        rw [hcast] at h
        rw [hQ]; linarith [h]
      have ha_nn : 0 ≤ aSeq N (m + 1) := aSeq_nonneg N (m + 1)
      have hbθ_nn : 0 ≤ bSeq N (m + 1) * theta N :=
        mul_nonneg (bSeq_pos N (m + 1)).le hθ
      have hQ_nn : 0 ≤ Q :=
        spencerPsi_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
      -- the new summand is at most `(Q + θ)(Q − P)`
      have hterm : aSeq N (m + 1) * bSeq N (m + 1) * theta N
          ≤ (Q + theta N) * (Q - P) := by
        have h1 : aSeq N (m + 1) * (bSeq N (m + 1) * theta N)
            ≤ (Q + theta N) * (Q - P) :=
          mul_le_mul ha hstep_ge hbθ_nn (by linarith)
        nlinarith [h1]
      rw [Finset.sum_range_succ, hcast]
      -- assemble: IH + term ≤ new right-hand side
      have hRHS : Q ^ 2 / 2 + (3 / 2) * theta N * Q
          - (P ^ 2 / 2 + (3 / 2) * theta N * P)
          = Q * (Q - P) - (Q - P) ^ 2 / 2 + (3 / 2) * theta N * (Q - P) := by
        ring
      nlinarith [ih, hterm, hRHS, hD_nn, hD_le, hθ]

/-- `bᵢ₊₁ = bᵢ · exp(-(Ψ((i+1)θ)² - Ψ(iθ)²))`. -/
lemma bSeq_succ_eq_mul_exp (N : ℕ) (i : ℕ) :
    bSeq N (i + 1)
      = bSeq N i * Real.exp (-((spencerPsi (((i : ℝ) + 1) * theta N)) ^ 2
          - (spencerPsi ((i : ℝ) * theta N)) ^ 2)) := by
  unfold bSeq
  rw [← Real.exp_add]
  have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  congr 1
  ring



/-- **Kim (13), lower half**: `bᵢ₊₁ ≥ bᵢ(1 − 2aᵢbᵢθ − bᵢθ²)`, i.e.
`bᵢ₊₁/bᵢ ≥ 1 − 2aᵢbᵢθ − bᵢθ²` (Kim allows slack `4bᵢθ²`).

With `D := Ψ((i+1)θ)² − Ψ(iθ)² = (Q+P)(Q−P)` we have `Q−P ≤ bᵢθ` and
`P ≤ aᵢ`, hence `D ≤ (2aᵢ + bᵢθ)bᵢθ = 2aᵢbᵢθ + bᵢ²θ²`; then
`bᵢ₊₁ = bᵢe^{−D} ≥ bᵢ(1−D)` and `bᵢ² ≤ bᵢ`. -/
lemma bSeq_ratio_lower (N : ℕ) (i : ℕ) :
    bSeq N i * (1 - 2 * aSeq N i * bSeq N i * theta N
        - bSeq N i * theta N ^ 2)
      ≤ bSeq N (i + 1) := by
  have hθ : 0 ≤ theta N := theta_nonneg N
  have hb_pos := bSeq_pos N i
  have hb_le_one : bSeq N i ≤ 1 := by
    unfold bSeq
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr
      (by nlinarith [sq_nonneg (spencerPsi ((i : ℝ) * theta N))])
  set P := spencerPsi ((i : ℝ) * theta N) with hP
  set Q := spencerPsi (((i : ℝ) + 1) * theta N) with hQ
  have hPnn : 0 ≤ P := spencerPsi_nonneg (mul_nonneg (Nat.cast_nonneg i) hθ)
  have hPQ : P ≤ Q := spencerPsi_strictMono.monotone (by nlinarith)
  have hstep : Q - P ≤ bSeq N i * theta N := spencerPsi_step_le N i
  have hPa : P ≤ aSeq N i := spencerPsi_le_aSeq N i
  set D := Q ^ 2 - P ^ 2 with hD
  have hD_le : D ≤ 2 * aSeq N i * bSeq N i * theta N
      + bSeq N i ^ 2 * theta N ^ 2 := by
    have hfac : D = (Q + P) * (Q - P) := by rw [hD]; ring
    have hdiff_nn : 0 ≤ Q - P := by linarith
    have hbθ_nn : 0 ≤ bSeq N i * theta N := mul_nonneg hb_pos.le hθ
    have hsum_le : Q + P ≤ 2 * aSeq N i + bSeq N i * theta N := by linarith
    have hsum_nn : 0 ≤ Q + P := by linarith
    calc D = (Q + P) * (Q - P) := hfac
      _ ≤ (2 * aSeq N i + bSeq N i * theta N) * (bSeq N i * theta N) := by
          nlinarith [hstep, hdiff_nn, hsum_le, hsum_nn]
      _ = 2 * aSeq N i * bSeq N i * theta N + bSeq N i ^ 2 * theta N ^ 2 := by ring
  have hexp : 1 - D ≤ Real.exp (-D) := by
    have := Real.add_one_le_exp (-D); linarith
  have hb_succ : bSeq N (i + 1) = bSeq N i * Real.exp (-D) := by
    rw [hD]; exact bSeq_succ_eq_mul_exp N i
  have hlow : bSeq N i * (1 - D) ≤ bSeq N (i + 1) := by
    rw [hb_succ]
    exact mul_le_mul_of_nonneg_left hexp hb_pos.le
  have hsq_le : bSeq N i ^ 2 * theta N ^ 2 ≤ bSeq N i * theta N ^ 2 := by
    have h1 : 0 ≤ bSeq N i * theta N ^ 2 := mul_nonneg hb_pos.le (sq_nonneg _)
    have h2 := mul_le_mul_of_nonneg_right hb_le_one h1
    nlinarith [h2]
  have hD_le' : D ≤ 2 * aSeq N i * bSeq N i * theta N + bSeq N i * theta N ^ 2 := by
    linarith
  have hmono : bSeq N i * (1 - 2 * aSeq N i * bSeq N i * theta N
      - bSeq N i * theta N ^ 2) ≤ bSeq N i * (1 - D) :=
    mul_le_mul_of_nonneg_left (by linarith) hb_pos.le
  linarith [hmono, hlow]

/-- **Property 2's expectation bound (Kim (29)-analogue for §4.3).**
`E[Φ_v] = Σ_{e ∈ N_Γ(v)} Pr(e ∉ Y') ≤ bn·(b'/b − 5bθ²) ≤ b'n − b²θ²n`.
Stated with `deg` for `d_Γ(v)` and `Pr` for the common survival probability. -/
lemma property2_mean_le {N : ℕ} (i : ℕ) {deg Pr nn : ℝ}
    (hnn : 0 ≤ nn) (hPr0 : 0 ≤ Pr) (hPr1 : Pr ≤ 1)
    (hdeg : deg ≤ bSeq N i * nn) (hdeg0 : 0 ≤ deg)
    (hsurv : bSeq N i * Pr ≤ bSeq N (i + 1) - 5 * bSeq N i ^ 2 * theta N ^ 2) :
    deg * Pr ≤ bSeq N (i + 1) * nn - bSeq N i ^ 2 * theta N ^ 2 * nn := by
  have hb_pos := bSeq_pos N i
  have hθ : 0 ≤ theta N := theta_nonneg N
  have hsq : 0 ≤ bSeq N i ^ 2 * theta N ^ 2 := by positivity
  have h1 : deg * Pr ≤ (bSeq N i * nn) * Pr :=
    mul_le_mul_of_nonneg_right hdeg hPr0
  have h2 : (bSeq N i * nn) * Pr = nn * (bSeq N i * Pr) := by ring
  have h3 : nn * (bSeq N i * Pr)
      ≤ nn * (bSeq N (i + 1) - 5 * bSeq N i ^ 2 * theta N ^ 2) :=
    mul_le_mul_of_nonneg_left hsurv hnn
  nlinarith [h1, h2, h3, hsq, hnn]

/-- **The survival hypothesis of `property2_mean_le`, discharged.**
Lemma 4.1 gives `Pr(e ∉ Y') ≤ 1 − 2abθ − 9bθ²`; combined with (13)
(`b' ≥ b(1 − 2abθ − bθ²)`) this yields Kim's `b·Pr ≤ b' − 5b²θ²`. -/
lemma bSeq_mul_surv_le (N : ℕ) (i : ℕ) {err : ℝ} (herr : 0 ≤ err)
    (hslack : bSeq N i * err ≤ 3 * bSeq N i ^ 2 * theta N ^ 2) {Pr : ℝ}
    (hPr : Pr ≤ 1 - 2 * aSeq N i * bSeq N i * theta N
      - 9 * bSeq N i * theta N ^ 2 + err) :
    bSeq N i * Pr ≤ bSeq N (i + 1) - 5 * bSeq N i ^ 2 * theta N ^ 2 := by
  have hb := bSeq_pos N i
  have hθ := theta_nonneg N
  have hratio := bSeq_ratio_lower N i
  have hscaled : bSeq N i * Pr
      ≤ bSeq N i * (1 - 2 * aSeq N i * bSeq N i * theta N
        - 9 * bSeq N i * theta N ^ 2 + err) :=
    mul_le_mul_of_nonneg_left hPr hb.le
  nlinarith [hscaled, hratio, hslack, hb.le,
    sq_nonneg (bSeq N i * theta N)]

/-- **Kim (14), the half used in §4.5**:
`bᵢ² − 2bᵢ²θ(aᵢ + 5θ) ≤ bᵢ₊₁ bᵢ`.

Proof: with `D := Ψ((i+1)θ)² − Ψ(iθ)²` we have `bᵢ₊₁ = bᵢe^{-D} ≥ bᵢ(1−D)`,
and `D = (Ψ'+Ψ)(Ψ'−Ψ) ≤ 2Ψ((i+1)θ)·bᵢθ ≤ 2(aᵢ+θ)bᵢθ ≤ 2(aᵢ+5θ)bᵢθ`
using `spencerPsi_step_le`, `spencerPsi_le_aSeq` and `bᵢ ≤ 1`. -/
lemma bSeq_sq_sub_le (N : ℕ) (i : ℕ) :
    bSeq N i ^ 2 - 2 * bSeq N i ^ 2 * theta N * (aSeq N i + 5 * theta N)
      ≤ bSeq N (i + 1) * bSeq N i := by
  have hθ : 0 ≤ theta N := theta_nonneg N
  have hb_pos := bSeq_pos N i
  have hb_le_one : bSeq N i ≤ 1 := by
    unfold bSeq
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr
      (by nlinarith [sq_nonneg (spencerPsi ((i : ℝ) * theta N))])
  have ha_nn := aSeq_nonneg N i
  set P := spencerPsi ((i : ℝ) * theta N) with hP
  set Q := spencerPsi (((i : ℝ) + 1) * theta N) with hQ
  have hP_nn : 0 ≤ P := spencerPsi_nonneg (mul_nonneg (Nat.cast_nonneg i) hθ)
  have hPQ : P ≤ Q := by
    apply spencerPsi_strictMono.monotone
    nlinarith
  have hstep : Q - P ≤ bSeq N i * theta N := spencerPsi_step_le N i
  -- Ψ((i+1)θ) ≤ a_{i+1} = a_i + b_i θ ≤ a_i + θ
  have hQ_le : Q ≤ aSeq N i + theta N := by
    have h1 := spencerPsi_le_aSeq N (i + 1)
    have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h1
    have h2 : aSeq N (i + 1) = aSeq N i + bSeq N i * theta N := aSeq_succ N i
    rw [h2] at h1
    nlinarith [h1, hb_le_one, hθ]
  -- D ≤ 2(a_i + 5θ) b_i θ
  set D := Q ^ 2 - P ^ 2 with hD
  have hD_le : D ≤ 2 * (aSeq N i + 5 * theta N) * bSeq N i * theta N := by
    have hfac : D = (Q + P) * (Q - P) := by rw [hD]; ring
    have hQP_nn : 0 ≤ Q + P := by linarith
    have hdiff_nn : 0 ≤ Q - P := by linarith
    have h1 : (Q + P) * (Q - P) ≤ (2 * Q) * (bSeq N i * theta N) := by
      have hQP_le : Q + P ≤ 2 * Q := by linarith
      nlinarith [hstep, hdiff_nn, hQP_le, hQP_nn]
    have h2 : (2 * Q) * (bSeq N i * theta N)
        ≤ 2 * (aSeq N i + 5 * theta N) * bSeq N i * theta N := by
      have : Q ≤ aSeq N i + 5 * theta N := by linarith
      nlinarith [this, hb_pos.le, hθ]
    linarith [hfac ▸ h1, h2]
  -- b_{i+1} = b_i e^{-D} ≥ b_i (1 - D)
  have hexp : 1 - D ≤ Real.exp (-D) := by
    have := Real.add_one_le_exp (-D); linarith
  have hb_succ : bSeq N (i + 1) = bSeq N i * Real.exp (-D) := by
    rw [hD]; exact bSeq_succ_eq_mul_exp N i
  have hlow : bSeq N i * (1 - D) ≤ bSeq N (i + 1) := by
    rw [hb_succ]
    exact mul_le_mul_of_nonneg_left hexp hb_pos.le
  -- Assemble, using b_i ≤ 1 to replace b_i³ by b_i².
  have hcube : bSeq N i ^ 3 ≤ bSeq N i ^ 2 := by nlinarith [hb_pos.le, hb_le_one]
  have hmul : bSeq N i * (1 - D) * bSeq N i ≤ bSeq N (i + 1) * bSeq N i :=
    mul_le_mul_of_nonneg_right hlow hb_pos.le
  have hb2D : bSeq N i ^ 2 * D
      ≤ bSeq N i ^ 2 * (2 * (aSeq N i + 5 * theta N) * bSeq N i * theta N) :=
    mul_le_mul_of_nonneg_left hD_le (sq_nonneg _)
  have hfactor_nn : 0 ≤ 2 * theta N * (aSeq N i + 5 * theta N) := by nlinarith
  have hstep2 : 2 * bSeq N i ^ 3 * theta N * (aSeq N i + 5 * theta N)
      ≤ 2 * bSeq N i ^ 2 * theta N * (aSeq N i + 5 * theta N) := by
    nlinarith [hcube, hfactor_nn]
  have hchain : bSeq N i ^ 2
      - 2 * bSeq N i ^ 3 * theta N * (aSeq N i + 5 * theta N)
      ≤ bSeq N i * (1 - D) * bSeq N i := by nlinarith [hb2D]
  linarith [hmul, hchain, hstep2]



/-- **Kim (12), lower half.** For `iθ ≤ n^δ`,
`b_i ≥ exp(−δ log n − 2√(δ log n) − 1)`.

By (16), `Ψ(x) ≤ √(log x) + 1` for `x ≥ 1`, and `Ψ(x) ≤ Ψ(1) ≤ 1` below that;
either way `Ψ(iθ)² ≤ δ log n + 2√(δ log n) + 1`. The `√`-term is `n^{o(1)}`,
which is why Kim's `δ = 1/17 − 10⁻⁵` leaves room for the stated `n^{−1/17}(log
n)³`. -/
lemma bSeq_ge_exp {N i : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (hN : 1 ≤ N)
    (hbound : (i : ℝ) * theta N ≤ Real.exp (δ * Real.log N)) :
    Real.exp (-(δ * Real.log N) - 2 * Real.sqrt (δ * Real.log N) - 1)
      ≤ bSeq N i := by
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hδlog : 0 ≤ δ * Real.log N := mul_nonneg hδ hlogN
  have hsq0 : 0 ≤ Real.sqrt (δ * Real.log N) := Real.sqrt_nonneg _
  set x : ℝ := (i : ℝ) * theta N with hx
  have hx0 : 0 ≤ x := mul_nonneg (Nat.cast_nonneg i) (theta_nonneg N)
  have hΨ0 : 0 ≤ spencerPsi x := spencerPsi_nonneg hx0
  have hkey : spencerPsi x ^ 2
      ≤ δ * Real.log N + 2 * Real.sqrt (δ * Real.log N) + 1 := by
    rcases le_or_gt x 1 with hle | hgt
    · have h1 : spencerPsi x ≤ spencerPsi 1 :=
        spencerPsi_strictMono.monotone hle
      have h2 : spencerPsi 1 ≤ Real.sqrt (Real.log 1) + 1 :=
        spencerPsi_le_sqrt_log_add_one le_rfl
      rw [Real.log_one, Real.sqrt_zero, zero_add] at h2
      nlinarith [h1, h2, hΨ0, hδlog, hsq0]
    · have h2 : spencerPsi x ≤ Real.sqrt (Real.log x) + 1 :=
        spencerPsi_le_sqrt_log_add_one hgt.le
      have hlogx : Real.log x ≤ δ * Real.log N := by
        calc Real.log x ≤ Real.log (Real.exp (δ * Real.log N)) :=
              Real.log_le_log (by linarith) hbound
          _ = δ * Real.log N := Real.log_exp _
      have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hgt.le
      have hsqle : Real.sqrt (Real.log x) ≤ Real.sqrt (δ * Real.log N) :=
        Real.sqrt_le_sqrt hlogx
      have hsqsq : Real.sqrt (Real.log x) ^ 2 = Real.log x :=
        Real.sq_sqrt hlogx0
      nlinarith [h2, hΨ0, Real.sqrt_nonneg (Real.log x), hsqle, hsqsq, hlogx]
  calc Real.exp (-(δ * Real.log N) - 2 * Real.sqrt (δ * Real.log N) - 1)
      ≤ Real.exp (-(spencerPsi x ^ 2)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = bSeq N i := by rw [bSeq]

/-- Kim's `δ := 1/17 − 10⁻⁵`, the exponent bounding the number of blocks. -/
noncomputable def kimDelta : ℝ := (1 : ℝ) / 17 - 10 ^ (-5 : ℤ)

lemma kimDelta_pos : 0 < kimDelta := by
  rw [kimDelta]; norm_num

lemma kimDelta_lt : kimDelta < 1 / 17 := by
  rw [kimDelta]; norm_num

/-- The block index constraint `k ≤ ⌊n^δ/θ⌋` gives `kθ ≤ n^δ`. -/
lemma kθ_le_rpow {N k : ℕ} (hθpos : 0 < theta N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    (k : ℝ) * theta N ≤ (N : ℝ) ^ kimDelta := by
  have hfloor : (k : ℝ) ≤ (N : ℝ) ^ kimDelta / theta N := by
    refine le_trans (Nat.cast_le.mpr hk) ?_
    exact Nat.floor_le (by positivity)
  rw [le_div_iff₀ hθpos] at hfloor
  exact hfloor

/-- **The uniform lower bound on `b_k`** across all blocks Kim uses.
For `k ≤ ⌊n^δ/θ⌋`, `b_k ≥ exp(−δ log n − 2√(δ log n) − 1) = n^{−δ−o(1)}`. -/
lemma bSeq_ge_of_k_le {N k : ℕ} (hN : 1 ≤ N) (hθpos : 0 < theta N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    Real.exp (-(kimDelta * Real.log N)
        - 2 * Real.sqrt (kimDelta * Real.log N) - 1)
      ≤ bSeq N k := by
  refine bSeq_ge_exp kimDelta_pos.le hN ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [show Real.exp (kimDelta * Real.log N) = (N : ℝ) ^ kimDelta from by
    rw [Real.rpow_def_of_pos hNpos]; ring_nf]
  exact kθ_le_rpow hθpos hk

/-- **Uniform upper bound on `Ψ(kθ)`** across Kim's blocks: for
`k ≤ ⌊n^δ/θ⌋`, `Ψ(kθ) ≤ √(δ log n) + 1`.

For `kθ ≥ 1` this is (16); below `1` we use `Ψ(kθ) ≤ Ψ(1) ≤ 1`. -/
lemma spencerPsi_le_of_k_le {N k : ℕ} (hN : 1 ≤ N) (hθpos : 0 < theta N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    spencerPsi ((k : ℝ) * theta N)
      ≤ Real.sqrt (kimDelta * Real.log N) + 1 := by
  have hNpos : (0 : ℝ) < N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hδlog : 0 ≤ kimDelta * Real.log N :=
    mul_nonneg kimDelta_pos.le hlogN
  have hsq0 : 0 ≤ Real.sqrt (kimDelta * Real.log N) := Real.sqrt_nonneg _
  set x : ℝ := (k : ℝ) * theta N with hx
  have hxle : x ≤ Real.exp (kimDelta * Real.log N) := by
    rw [show Real.exp (kimDelta * Real.log N) = (N : ℝ) ^ kimDelta from by
      rw [Real.rpow_def_of_pos hNpos]; ring_nf]
    exact kθ_le_rpow hθpos hk
  rcases le_or_gt x 1 with hle | hgt
  · have h1 : spencerPsi x ≤ spencerPsi 1 :=
      spencerPsi_strictMono.monotone hle
    have h2 : spencerPsi 1 ≤ Real.sqrt (Real.log 1) + 1 :=
      spencerPsi_le_sqrt_log_add_one le_rfl
    rw [Real.log_one, Real.sqrt_zero, zero_add] at h2
    linarith
  · have h2 : spencerPsi x ≤ Real.sqrt (Real.log x) + 1 :=
      spencerPsi_le_sqrt_log_add_one hgt.le
    have hlogx : Real.log x ≤ kimDelta * Real.log N := by
      calc Real.log x ≤ Real.log (Real.exp (kimDelta * Real.log N)) :=
            Real.log_le_log (by linarith) hxle
        _ = kimDelta * Real.log N := Real.log_exp _
    have := Real.sqrt_le_sqrt hlogx
    linarith

/-- **Uniform upper bound on `a_k`**: `a_k ≤ √(δ log n) + 1 + θ`.
Kim's (11) in the form §4 consumes it. -/
lemma aSeq_le_of_k_le {N k : ℕ} (hN : 1 ≤ N) (hθpos : 0 < theta N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    aSeq N k ≤ Real.sqrt (kimDelta * Real.log N) + 1 + theta N := by
  have h1 := (aSeq_sub_spencerPsi_bounds N k).2
  have h2 := spencerPsi_le_of_k_le hN hθpos hk
  linarith


/-- `bᵢ ≤ 1`. (Since `Ψ²(iθ) ≥ 0`, so `exp(-Ψ²) ≤ 1`.) -/
lemma bSeq_le_one (n : ℕ) (i : ℕ) : bSeq n i ≤ 1 := by
  unfold bSeq
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  apply Real.exp_le_exp.mpr
  rw [neg_le, neg_zero]
  exact sq_nonneg _

/-- `Ψ(iθ)²·bᵢ ≤ e⁻¹ ≤ 2/5`, since `bᵢ = e^{−Ψ(iθ)²}` and `x e^{−x} ≤ e⁻¹`. -/
lemma psiSq_mul_bSeq_le (N i : ℕ) :
    (spencerPsi ((i : ℝ) * theta N)) ^ 2 * bSeq N i ≤ 2 / 5 := by
  have h := mul_exp_neg_le (t := (spencerPsi ((i : ℝ) * theta N)) ^ 2)
    (sq_nonneg _)
  have hb : bSeq N i = Real.exp (-(spencerPsi ((i : ℝ) * theta N)) ^ 2) := rfl
  rw [hb]
  refine le_trans h ?_
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num : (0:ℝ) < 2/5)]
  linarith

/-- `Ψ(iθ)·bᵢ ≤ 1`. -/
lemma psi_mul_bSeq_le_one (N i : ℕ) :
    spencerPsi ((i : ℝ) * theta N) * bSeq N i ≤ 1 := by
  have hP0 : 0 ≤ spencerPsi ((i : ℝ) * theta N) :=
    spencerPsi_nonneg (mul_nonneg (Nat.cast_nonneg i) (theta_nonneg N))
  have hb1 := bSeq_le_one N i
  have hb0 := (bSeq_pos N i).le
  rcases le_or_gt (spencerPsi ((i : ℝ) * theta N)) 1 with h | h
  · nlinarith [hb1, hb0, hP0]
  · have hsq := psiSq_mul_bSeq_le N i
    nlinarith [hsq, hb0, h]

/-- **The §4.8 budget combination**: `6Ψ²b + (5/2)b ≤ 4`.

Both `Ψ²b` and `b` appear in the `θ²` ledger of Kim's `μ` recursion, and
bounding them separately (`6e⁻¹ + 5/2 ≈ 4.7`) overshoots the `18bθ²`
allowance once the other charges are added.  Jointly, `(6u + 5/2)e^{−u} ≤ 4`
because `e^u ≥ (1+u/2)²` turns it into `u² − 2u + 3/2 ≥ 0`. -/
lemma psiSq_combo_le (N i : ℕ) :
    6 * (spencerPsi ((i : ℝ) * theta N)) ^ 2 * bSeq N i
        + (5 / 2) * bSeq N i ≤ 4 := by
  set u : ℝ := (spencerPsi ((i : ℝ) * theta N)) ^ 2 with hu
  have hu0 : 0 ≤ u := sq_nonneg _
  have hb : bSeq N i = Real.exp (-u) := rfl
  have hhalf : (1 : ℝ) + u / 2 ≤ Real.exp (u / 2) := by
    have := Real.add_one_le_exp (u / 2); linarith
  have hsq : (1 + u / 2) ^ 2 ≤ Real.exp u := by
    have h1 : (1 + u / 2) ^ 2 ≤ (Real.exp (u / 2)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hhalf 2
    have h2 : (Real.exp (u / 2)) ^ 2 = Real.exp u := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    linarith [h1, h2.le, h2.ge]
  have hquad : 6 * u + 5 / 2 ≤ 4 * Real.exp u := by
    nlinarith [hsq, hu0, sq_nonneg (u - 1)]
  have hE : (0 : ℝ) < Real.exp u := Real.exp_pos u
  rw [hb, Real.exp_neg]
  rw [show 6 * u * (Real.exp u)⁻¹ + 5 / 2 * (Real.exp u)⁻¹
      = (6 * u + 5 / 2) * (Real.exp u)⁻¹ by ring,
    mul_inv_le_iff₀ hE]
  linarith [hquad]

/-- `e^{−x} ≤ 1 − x + x²/2` for `x ≥ 0`. -/
lemma exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hcube : 1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
    have h := Real.sum_le_exp_of_nonneg hx 4
    simpa [Finset.sum_range_succ, Nat.factorial] using h
  have hpos : (0 : ℝ) < Real.exp x := Real.exp_pos x
  have hfac : (0 : ℝ) ≤ 1 - x + x ^ 2 / 2 := by nlinarith [sq_nonneg (x - 1)]
  have hkey : 1 ≤ (1 - x + x ^ 2 / 2) * Real.exp x := by
    have hexpand : (1 - x + x ^ 2 / 2) * (1 + x + x ^ 2 / 2 + x ^ 3 / 6)
        = 1 + x ^ 3 / 6 + x ^ 4 / 12 + x ^ 5 / 12 := by ring
    nlinarith [mul_le_mul_of_nonneg_left hcube hfac, hexpand.le, hexpand.ge,
      pow_nonneg hx 3, pow_nonneg hx 4, pow_nonneg hx 5]
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hpos]
  linarith [hkey]

set_option maxHeartbeats 1000000 in
/-- The pure-real core of Kim (13)'s sharp upper half. -/
lemma bSeq_succ_upper_core {θ P Q b b' A D : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 100)
    (hb0 : 0 < b) (hb1 : b ≤ 1) (hb'0 : 0 < b')
    (hP0 : 0 ≤ P) (hPQ : P ≤ Q)
    (hsteple : Q - P ≤ b * θ) (hstepge : b' * θ ≤ Q - P)
    (haub : A - P ≤ θ) (hPb : P * b ≤ 1)
    (hDdef : D = Q ^ 2 - P ^ 2)
    (hb'eq : b' = b * Real.exp (-D)) :
    b' ≤ b - 2 * A * b ^ 2 * θ + (41 / 20) * b ^ 2 * θ ^ 2
      + 6 * P ^ 2 * b ^ 3 * θ ^ 2 := by
  have hD0 : 0 ≤ D := by rw [hDdef]; nlinarith [hPQ, hP0]
  have hDle : D ≤ 2 * P * b * θ + b ^ 2 * θ ^ 2 := by
    have hfac : D = (Q - P) * (Q + P) := by rw [hDdef]; ring
    have hsum : Q + P ≤ 2 * P + b * θ := by linarith
    have h0 : (0 : ℝ) ≤ Q - P := by linarith
    have hbθ0 : (0 : ℝ) ≤ b * θ := by positivity
    rw [hfac]
    nlinarith [h0, hsteple, hsum, hP0, hbθ0]
  have hDge : 2 * P * b' * θ ≤ D := by
    have hfac : D = (Q - P) * (Q + P) := by rw [hDdef]; ring
    have h1 : (0 : ℝ) ≤ b' * θ := by positivity
    have h3 : 2 * P ≤ Q + P := by linarith
    rw [hfac]
    nlinarith [h1, hstepge, h3, hP0]
  have hexp := exp_neg_le_quadratic hD0
  have hstep1 : b' ≤ b * (1 - D + D ^ 2 / 2) := by
    rw [hb'eq]
    exact mul_le_mul_of_nonneg_left hexp hb0.le
  have hb'ge : b * (1 - D) ≤ b' := by
    rw [hb'eq]
    exact mul_le_mul_of_nonneg_left
      (by linarith [Real.add_one_le_exp (-D)]) hb0.le
  have hk1 : b * (2 * P * b' * θ) ≤ b * D :=
    mul_le_mul_of_nonneg_left hDge hb0.le
  have hk2 : (2 * P * b * θ) * (b * (1 - D)) ≤ (2 * P * b * θ) * b' :=
    mul_le_mul_of_nonneg_left hb'ge (by positivity)
  have hkey : 2 * P * b ^ 2 * θ - 2 * P * b ^ 2 * θ * D ≤ b * D := by
    nlinarith [hk1, hk2]
  have hDcorr : 2 * P * b ^ 2 * θ * D
      ≤ 4 * P ^ 2 * b ^ 3 * θ ^ 2 + 2 * P * b ^ 4 * θ ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hDle
      (show (0 : ℝ) ≤ 2 * P * b ^ 2 * θ by positivity)
    nlinarith [h]
  have hDsq2 : b * D ^ 2 / 2
      ≤ 2 * P ^ 2 * b ^ 3 * θ ^ 2 + 2 * P * b ^ 4 * θ ^ 3
        + b ^ 5 * θ ^ 4 / 2 := by
    have hsq : D ^ 2 ≤ (2 * P * b * θ + b ^ 2 * θ ^ 2) ^ 2 :=
      pow_le_pow_left₀ hD0 hDle 2
    have h := mul_le_mul_of_nonneg_left hsq hb0.le
    nlinarith [h]
  have haθ : 2 * A * b ^ 2 * θ ≤ 2 * P * b ^ 2 * θ + 2 * b ^ 2 * θ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left haub
      (show (0 : ℝ) ≤ 2 * b ^ 2 * θ by positivity)
    nlinarith [h]
  have htail : 4 * P * b ^ 4 * θ ^ 3 + b ^ 5 * θ ^ 4 / 2
      ≤ (1 / 20) * b ^ 2 * θ ^ 2 := by
    have hb3 : b ^ 3 ≤ b ^ 2 := by nlinarith [hb0.le, hb1]
    have hb5 : b ^ 5 ≤ b ^ 2 := by nlinarith [hb0.le, hb1]
    have hth4 : θ ^ 4 ≤ θ ^ 3 := by nlinarith [pow_nonneg hθ0 3, hθ, hθ0]
    have hs1 : (P * b) * (b ^ 3 * θ ^ 3) ≤ 1 * (b ^ 3 * θ ^ 3) :=
      mul_le_mul_of_nonneg_right hPb (by positivity)
    have hs2 : b ^ 3 * θ ^ 3 ≤ b ^ 2 * θ ^ 3 :=
      mul_le_mul_of_nonneg_right hb3 (by positivity)
    have h1 : P * b ^ 4 * θ ^ 3 ≤ b ^ 2 * θ ^ 3 := by nlinarith [hs1, hs2]
    have hs3 : b ^ 5 * θ ^ 4 ≤ b ^ 5 * θ ^ 3 :=
      mul_le_mul_of_nonneg_left hth4 (by positivity)
    have hs4 : b ^ 5 * θ ^ 3 ≤ b ^ 2 * θ ^ 3 :=
      mul_le_mul_of_nonneg_right hb5 (by positivity)
    have h2 : b ^ 5 * θ ^ 4 ≤ b ^ 2 * θ ^ 3 := by linarith [hs3, hs4]
    have h3 : b ^ 2 * θ ^ 3 ≤ b ^ 2 * θ ^ 2 * (1 / 100) := by
      have h := mul_le_mul_of_nonneg_left hθ
        (show (0 : ℝ) ≤ b ^ 2 * θ ^ 2 by positivity)
      nlinarith [h]
    have hbθ : (0 : ℝ) ≤ b ^ 2 * θ ^ 2 := by positivity
    linarith [h1, h2, h3, hbθ]
  have hP2 : (0 : ℝ) ≤ P ^ 2 * b ^ 3 * θ ^ 2 := by positivity
  have hbθ2 : (0 : ℝ) ≤ b ^ 2 * θ ^ 2 := by positivity
  linarith [hstep1, hkey, hDcorr, hDsq2, haθ, htail, hP2, hbθ2]

/-- `Ψ(iθ)·bᵢ ≤ 9/20`, since `x e^{−x²} ≤ 1/√(2e) ≈ 0.4289`. -/
lemma psi_mul_bSeq_le_half (N i : ℕ) :
    spencerPsi ((i : ℝ) * theta N) * bSeq N i ≤ 9 / 20 := by
  have hP0 : 0 ≤ spencerPsi ((i : ℝ) * theta N) :=
    spencerPsi_nonneg (mul_nonneg (Nat.cast_nonneg i) (theta_nonneg N))
  have hb0 := (bSeq_pos N i).le
  have hb : bSeq N i = Real.exp (-(spencerPsi ((i : ℝ) * theta N)) ^ 2) := rfl
  have hkey := mul_exp_neg_le (t := 2 * (spencerPsi ((i : ℝ) * theta N)) ^ 2)
    (by positivity)
  have hsq : (spencerPsi ((i : ℝ) * theta N) * bSeq N i) ^ 2
      = (spencerPsi ((i : ℝ) * theta N)) ^ 2
        * Real.exp (-(2 * (spencerPsi ((i : ℝ) * theta N)) ^ 2)) := by
    rw [hb, mul_pow]
    congr 1
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have he : Real.exp (-1) ≤ 2 / 5 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num : (0:ℝ) < 2/5)]
    linarith
  have hbound : (spencerPsi ((i : ℝ) * theta N) * bSeq N i) ^ 2 ≤ 1 / 5 := by
    rw [hsq]
    nlinarith [hkey, he]
  nlinarith [hbound, hP0, hb0, mul_nonneg hP0 hb0]

/-- **Kim (14), first branch**: `bᵢ² ≤ bᵢ₊₁bᵢ(1 + θ)`, i.e. `bᵢ ≤ (1+θ)bᵢ₊₁`.

The ratio form.  Unlike the additive branch `bᵢ − bᵢ₊₁ ≤ 2bᵢθ(aᵢ+5θ)`, whose
`aᵢ ≈ Ψ ≈ √(δ log n)` is `O(√log n)`, this is `1 + O(θ)` — which is what §4.8's
`θ²` ledger needs.  It holds because `D = Ψ((i+1)θ)² − Ψ(iθ)² ≤ 2(Ψbᵢ)θ + θ²`
and `Ψbᵢ = Ψe^{−Ψ²} ≤ 1/2`. -/
lemma bSeq_le_succ_mul {N : ℕ} (hθ : theta N ≤ 1 / 100) (k : ℕ) :
    bSeq N k ≤ (1 + theta N) * bSeq N (k + 1) := by
  have hθ0 : 0 ≤ theta N := theta_nonneg N
  have hb0 : 0 < bSeq N k := bSeq_pos N k
  have hb1 : bSeq N k ≤ 1 := bSeq_le_one N k
  have hP0 : 0 ≤ spencerPsi ((k : ℝ) * theta N) :=
    spencerPsi_nonneg (mul_nonneg (Nat.cast_nonneg k) (theta_nonneg N))
  have hPQ : spencerPsi ((k : ℝ) * theta N)
      ≤ spencerPsi (((k : ℝ) + 1) * theta N) := by
    refine spencerPsi_strictMono.monotone ?_
    have hi : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [hθ0, hi]
  have hsteple : spencerPsi (((k : ℝ) + 1) * theta N)
      - spencerPsi ((k : ℝ) * theta N) ≤ bSeq N k * theta N :=
    spencerPsi_step_le N k
  have hPb := psi_mul_bSeq_le_half N k
  set D : ℝ := spencerPsi (((k : ℝ) + 1) * theta N) ^ 2
    - spencerPsi ((k : ℝ) * theta N) ^ 2 with hDdef
  have hD0 : 0 ≤ D := by rw [hDdef]; nlinarith [hPQ, hP0]
  have hDle : D ≤ (92 / 100) * theta N := by
    have hfac : D = (spencerPsi (((k : ℝ) + 1) * theta N)
        - spencerPsi ((k : ℝ) * theta N))
      * (spencerPsi (((k : ℝ) + 1) * theta N)
        + spencerPsi ((k : ℝ) * theta N)) := by rw [hDdef]; ring
    have hsum : spencerPsi (((k : ℝ) + 1) * theta N)
        + spencerPsi ((k : ℝ) * theta N)
        ≤ 2 * spencerPsi ((k : ℝ) * theta N) + bSeq N k * theta N := by
      linarith
    have h0 : (0 : ℝ) ≤ spencerPsi (((k : ℝ) + 1) * theta N)
        - spencerPsi ((k : ℝ) * theta N) := by linarith
    have hbθ0 : (0 : ℝ) ≤ bSeq N k * theta N := by positivity
    have hstep : D ≤ 2 * (spencerPsi ((k : ℝ) * theta N) * bSeq N k) * theta N
        + bSeq N k ^ 2 * theta N ^ 2 := by
      rw [hfac]
      nlinarith [h0, hsteple, hsum, hP0, hbθ0]
    have hA : 2 * (spencerPsi ((k : ℝ) * theta N) * bSeq N k) * theta N
        ≤ (9 / 10) * theta N := by
      nlinarith [mul_nonneg (by linarith [hPb] :
        (0:ℝ) ≤ 9 / 20 - spencerPsi ((k : ℝ) * theta N) * bSeq N k) hθ0]
    have hB : bSeq N k ^ 2 * theta N ^ 2 ≤ (1 / 100) * theta N := by
      have hb2 : bSeq N k ^ 2 ≤ 1 := by nlinarith [hb0.le, hb1]
      nlinarith [hb2, hθ, hθ0, sq_nonneg (theta N),
        mul_nonneg hθ0 hθ0]
    linarith [hstep, hA, hB]
  have hb'eq : bSeq N (k + 1) = bSeq N k * Real.exp (-D) :=
    bSeq_succ_eq_mul_exp N k
  have hexpD : Real.exp D ≤ 1 + theta N := by
    have hDsmall : D ≤ 92 / 10000 := by linarith [hDle, hθ]
    have hE : Real.exp D ≤ 1 / (1 - D) := by
      have h1 : (0 : ℝ) < 1 - D := by linarith
      have h2 : (1 : ℝ) - D ≤ Real.exp (-D) := by
        linarith [Real.add_one_le_exp (-D)]
      have h3 : (0 : ℝ) < Real.exp D := Real.exp_pos D
      rw [Real.exp_neg] at h2
      rw [le_div_iff₀ h1]
      have h4 := mul_le_mul_of_nonneg_right h2 h3.le
      rw [inv_mul_cancel₀ (ne_of_gt h3)] at h4
      linarith [h4]
    have hdiv : 1 / (1 - D) ≤ 1 + theta N := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - D)]
      nlinarith [hD0, hDle, hθ, hθ0]
    linarith [hE, hdiv]
  have hE0 : (0 : ℝ) < Real.exp (-D) := Real.exp_pos _
  have hcancel : Real.exp (-D) * Real.exp D = 1 := by
    rw [← Real.exp_add]; simp
  have hstep : bSeq N k ≤ bSeq N k * Real.exp (-D) * (1 + theta N) := by
    have h1 := mul_le_mul_of_nonneg_left hexpD
      (show (0 : ℝ) ≤ bSeq N k * Real.exp (-D) by positivity)
    nlinarith [h1, hcancel]
  rw [hb'eq]
  linarith [hstep]

/-- **Kim (13), the sharp upper half**:
`bᵢ₊₁ ≤ bᵢ − 2aᵢbᵢ²θ + (41/20)bᵢ²θ² + 6Ψ(iθ)²bᵢ³θ²`.

This is what the §4.8 budget turns on.  Linearising `bᵢ₊₁ = bᵢe^{−D}` with
`D = Ψ((i+1)θ)² − Ψ(iθ)²` costs a second-order term of order `Ψ²b³θ²`, which
is `log n` times the `18bθ²` allowance in `μ` unless one keeps `Ψ²b` together
— see `psiSq_combo_le`. -/
lemma bSeq_succ_upper {N : ℕ} (hθ : theta N ≤ 1 / 100) (i : ℕ) :
    bSeq N (i + 1)
      ≤ bSeq N i - 2 * aSeq N i * bSeq N i ^ 2 * theta N
        + (41 / 20) * bSeq N i ^ 2 * theta N ^ 2
        + 6 * (spencerPsi ((i : ℝ) * theta N)) ^ 2 * bSeq N i ^ 3
          * theta N ^ 2 := by
  have hP0 : 0 ≤ spencerPsi ((i : ℝ) * theta N) :=
    spencerPsi_nonneg (mul_nonneg (Nat.cast_nonneg i) (theta_nonneg N))
  have hPQ : spencerPsi ((i : ℝ) * theta N)
      ≤ spencerPsi (((i : ℝ) + 1) * theta N) := by
    refine spencerPsi_strictMono.monotone ?_
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    nlinarith [theta_nonneg N, hi]
  refine bSeq_succ_upper_core (Q := spencerPsi (((i : ℝ) + 1) * theta N))
    (D := (spencerPsi (((i : ℝ) + 1) * theta N)) ^ 2
      - (spencerPsi ((i : ℝ) * theta N)) ^ 2)
    (theta_nonneg N) hθ (bSeq_pos N i) (bSeq_le_one N i) (bSeq_pos N (i + 1))
    hP0 hPQ (spencerPsi_step_le N i) (spencerPsi_step_ge N i)
    (aSeq_sub_spencerPsi_bounds N i).2 (psi_mul_bSeq_le_one N i) rfl
    (bSeq_succ_eq_mul_exp N i)

/-- `tParam n ≥ 9√(n log n)`. -/
lemma tParam_ge (n : ℕ) : 9 * Real.sqrt ((n : ℝ) * Real.log n) ≤ (tParam n : ℝ) := by
  unfold tParam
  exact Nat.le_ceil _

/-- `tParam n ≥ 1` for `n ≥ 2`. -/
lemma tParam_pos {n : ℕ} (hn : 2 ≤ n) : 1 ≤ tParam n := by
  unfold tParam
  apply Nat.one_le_iff_ne_zero.mpr
  intro h
  rw [Nat.ceil_eq_zero] at h
  have h_log_pos : 0 < Real.log n := by
    rw [Real.log_pos_iff]
    · exact_mod_cast (by linarith : 1 < n)
    · exact_mod_cast Nat.zero_le n
  have h_n_pos : (0 : ℝ) < n := by exact_mod_cast (by linarith : 0 < n)
  have h_pos : 0 < 9 * Real.sqrt (↑n * Real.log ↑n) := by
    apply mul_pos (by norm_num : (0 : ℝ) < 9)
    exact Real.sqrt_pos.mpr (mul_pos h_n_pos h_log_pos)
  linarith

/-! ### Properties 1–8 of Kim §2

Each property bounds (with high probability) a particular degree-, codegree-,
or count-quantity at stage `i` against the parameters `(aᵢ, bᵢ, μᵢ)`. We
state each as a `Prop` over a `BlockState` so the Main Lemma can quantify
over all eight uniformly.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of vertices `n` is `|V|`. -/
local notation "n" => Fintype.card V

/-- The set of edges in `E` incident to `v`. -/
noncomputable def edgesAt (E : Finset (Edge V)) (v : V) : Finset (Edge V) := by
  classical exact E.filter (fun e => v ∈ e.val)

/-- The degree of `v` in an edge-set `E`: number of incident edges. -/
noncomputable def degEdges (E : Finset (Edge V)) (v : V) : ℕ :=
  (edgesAt E v).card

/-- `degEdges (E ∪ F) v ≤ degEdges E v + degEdges F v`. -/
lemma degEdges_union_le (E F : Finset (Edge V)) (v : V) :
    degEdges (E ∪ F) v ≤ degEdges E v + degEdges F v := by
  classical
  unfold degEdges edgesAt
  rw [Finset.filter_union]
  exact Finset.card_union_le _ _

/-! ### Monotonicity helpers for Property 1 propagation

These lemmas bundle the algebraic monotonicity facts needed when the
`blockStep` chooses the trivial sample `X = ∅` and we must verify that the
bound for Property 1 at step `k` continues to hold at step `k+1`. -/

/-- `w` is a common `F`-neighbour of `u` and `v`. -/
noncomputable def commonNbrs (F : Finset (Edge V)) (u v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w =>
    (w ≠ u ∧ w ≠ v) ∧
    (∃ e ∈ F, u ∈ e.val ∧ w ∈ e.val) ∧ (∃ f ∈ F, w ∈ f.val ∧ v ∈ f.val))

/-- The pair degree (codegree) of `u, v` in an edge set. -/
noncomputable def codegEdges (F : Finset (Edge V)) (u v : V) : ℕ :=
  (commonNbrs F u v).card



lemma mem_commonNbrs {F : Finset (Edge V)} {u v w : V} :
    w ∈ commonNbrs F u v ↔
      ((w ≠ u ∧ w ≠ v) ∧
        (∃ e ∈ F, u ∈ e.val ∧ w ∈ e.val) ∧ (∃ f ∈ F, w ∈ f.val ∧ v ∈ f.val)) := by
  classical
  show w ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ w, h⟩⟩

/-- The `F`-neighbourhood of `v`. -/
noncomputable def nbrs (F : Finset (Edge V)) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => u ≠ v ∧ ∃ e ∈ F, v ∈ e.val ∧ u ∈ e.val)

lemma mem_nbrs {F : Finset (Edge V)} {v u : V} :
    u ∈ nbrs F v ↔ u ≠ v ∧ ∃ e ∈ F, v ∈ e.val ∧ u ∈ e.val := by
  classical
  show u ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ u, h⟩⟩

/-- `commonNbrs` really is the intersection of the two neighbourhoods. -/
lemma commonNbrs_eq_inter (F : Finset (Edge V)) (v w : V) :
    commonNbrs F v w = nbrs F v ∩ nbrs F w := by
  classical
  ext u
  rw [Finset.mem_inter, mem_commonNbrs, mem_nbrs, mem_nbrs]
  constructor
  · rintro ⟨⟨hne, hne'⟩, ⟨e, heF, hv, hu⟩, ⟨f, hfF, hu', hw⟩⟩
    exact ⟨⟨hne, e, heF, hv, hu⟩, ⟨hne', f, hfF, hw, hu'⟩⟩
  · rintro ⟨⟨hne, e, heF, hv, hu⟩, ⟨hne', f, hfF, hw, hu'⟩⟩
    exact ⟨⟨hne, hne'⟩, ⟨e, heF, hv, hu⟩, ⟨f, hfF, hu', hw⟩⟩

/-- Neighbourhoods split along a union of edge sets. -/
lemma nbrs_union (E X : Finset (Edge V)) (v : V) :
    nbrs (E ∪ X) v = nbrs E v ∪ nbrs X v := by
  classical
  ext u
  rw [Finset.mem_union, mem_nbrs, mem_nbrs, mem_nbrs]
  constructor
  · rintro ⟨hne, e, heEX, hv, hu⟩
    rcases Finset.mem_union.mp heEX with h | h
    · exact Or.inl ⟨hne, e, h, hv, hu⟩
    · exact Or.inr ⟨hne, e, h, hv, hu⟩
  · rintro (⟨hne, e, h, hv, hu⟩ | ⟨hne, e, h, hv, hu⟩)
    · exact ⟨hne, e, Finset.mem_union_left _ h, hv, hu⟩
    · exact ⟨hne, e, Finset.mem_union_right _ h, hv, hu⟩

/-- **Property 3 decomposition — the deterministic core of Kim §4.4.**

`|N_{ℰ'}(v) ∩ N_{ℰ'}(w)| ≤ |N_ℰ(v) ∩ N_ℰ(w)| + |N_{X'}(v) ∩ N_ℰ(w)|
                        + |N_ℰ(v) ∩ N_{X'}(w)| + |N_{X'}(v) ∩ N_{X'}(w)|`.

The first summand is bounded by Property 3 at stage `k`; the remaining three
are Lemma 4.3(ii),(iii), the probabilistic input. -/
lemma commonNbrs_union_card_le (E X : Finset (Edge V)) (v w : V) :
    (commonNbrs (E ∪ X) v w).card
      ≤ (commonNbrs E v w).card
        + (nbrs X v ∩ nbrs E w).card
        + (nbrs E v ∩ nbrs X w).card
        + (commonNbrs X v w).card := by
  classical
  rw [commonNbrs_eq_inter, commonNbrs_eq_inter, commonNbrs_eq_inter,
    nbrs_union, nbrs_union]
  have hsplit : (nbrs E v ∪ nbrs X v) ∩ (nbrs E w ∪ nbrs X w)
      = ((nbrs E v ∩ nbrs E w) ∪ (nbrs E v ∩ nbrs X w))
        ∪ ((nbrs X v ∩ nbrs E w) ∪ (nbrs X v ∩ nbrs X w)) := by
    rw [Finset.union_inter_distrib_right, Finset.inter_union_distrib_left,
      Finset.inter_union_distrib_left]
  rw [hsplit]
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 := Finset.card_union_le (nbrs E v ∩ nbrs E w) (nbrs E v ∩ nbrs X w)
  have h2 := Finset.card_union_le (nbrs X v ∩ nbrs E w) (nbrs X v ∩ nbrs X w)
  omega

/-- Codegrees never exceed the number of vertices. -/
lemma codegEdges_le_card (F : Finset (Edge V)) (u v : V) :
    codegEdges F u v ≤ n := by
  classical
  exact le_trans (Finset.card_le_card (Finset.subset_univ _))
    (le_of_eq (Finset.card_univ))


/-! ### Properties 3–6 (Kim §2)

Verbatim from Kim 1995, p. 8:

* **Property 3.** For all `v ≠ w`, `|N_{ℰᵢ}(v) ∩ N_{ℰᵢ}(w)| ≤ 3i log n`.
* **Property 4.** For all `e_vw ∈ Γᵢ`, `d_{Λᵢ}(e_vw, v) ≤ bᵢ(aᵢ + 5θ)√n`.
* **Property 5.** For all `e ∈ Γᵢ`, `d_{Δᵢ}(e) ≤ bᵢ² n`.
* **Property 6.** For disjoint `A, B` with `|A|,|B| ≥ θ²bᵢ²√n`,
  `|Γᵢ(A,B)| ≤ bᵢ|A||B|`; and for `|A| ≥ θ²bᵢ²√n`, `|Γᵢ(A)| ≤ bᵢ(|A| choose 2)`.

These are stated here as standalone definitions and bundled into
`Properties1to8`, which is what Kim's Main Lemma quantifies over. -/

/-- The edge `{u, v}` for distinct `u, v`. -/
def mkEdge {u v : V} (h : u ≠ v) : Edge V :=
  ⟨s(u, v), by simpa using h⟩

@[simp] lemma mkEdge_val {u v : V} (h : u ≠ v) : (mkEdge h).val = s(u, v) := rfl

/-- `d_{Λᵢ}(e_vw, v)`: vertices `u` with `e_uv ∈ Γ` and `e_uw ∈ E`, i.e. the
`Γ`-edges at `v` that already form a forbidden pair with `e_vw` through `E`. -/
noncomputable def lambdaDeg (E Γ : Finset (Edge V)) (v w : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun u => (u ≠ v ∧ u ≠ w) ∧
    (∃ e ∈ Γ, u ∈ e.val ∧ v ∈ e.val) ∧ (∃ f ∈ E, u ∈ f.val ∧ w ∈ f.val))).card

/-- `Γᵢ(A, B)`: the `Γ`-edges running between `A` and `B`. -/
noncomputable def gammaBetween (Γ : Finset (Edge V)) (A B : Finset V) :
    Finset (Edge V) := by
  classical
  exact Γ.filter (fun e => ∃ v ∈ A, ∃ w ∈ B, v ≠ w ∧ v ∈ e.val ∧ w ∈ e.val)

/-- **Property 3 (Kim §2).** `|N_{ℰᵢ}(v) ∩ N_{ℰᵢ}(w)| ≤ 3 i log n`. -/
def Property3 (s : BlockState V) (i : ℕ) : Prop :=
  ∀ v w : V, v ≠ w → ((commonNbrs s.E v w).card : ℝ) ≤ 3 * i * Real.log n

/-- **Property 4 (Kim §2).** `d_{Λᵢ}(e_vw, v) ≤ bᵢ(aᵢ + 5θ)√n`. -/
def Property4 (s : BlockState V) (i : ℕ) : Prop :=
  ∀ (v w : V) (h : v ≠ w), mkEdge h ∈ s.Γ →
    (lambdaDeg s.E s.Γ v w : ℝ)
      ≤ bSeq n i * (aSeq n i + 5 * theta n) * Real.sqrt n

/-- **Property 5 (Kim §2).** `d_{Δᵢ}(e) ≤ bᵢ² n`: the number of `u` closing a
`Γ`-triangle on `e_vw` is at most `bᵢ² n`. -/
def Property5 (s : BlockState V) (i : ℕ) : Prop :=
  ∀ (v w : V) (h : v ≠ w), mkEdge h ∈ s.Γ →
    (codegEdges s.Γ v w : ℝ) ≤ bSeq n i ^ 2 * n

/-- **Kim's Property-6 threshold** `θ²bᵢ²√n` (§2, §4.7), frozen at the last
block `k₀ = ⌊n^δ/θ⌋`.

Freezing is the single place where Kim's expression cannot be used verbatim:
`θ²bᵢ²√n` *decreases* in `i` (since `b` is antitone), so the threshold
established at level `i` does not cover what level `i+1` needs, and the
induction cannot close.  Taking his own expression at `k₀` is the minimal
repair — every bound below still sees `θ²b²√n`, only with the smallest `b`. -/
noncomputable def mcutR (N : ℕ) : ℝ :=
  theta N ^ 2 * bSeq N ⌊(N : ℝ) ^ kimDelta / theta N⌋₊ ^ 2 * Real.sqrt N

noncomputable def mcut (N : ℕ) : ℕ := ⌊mcutR N⌋₊

/-- **Property 6 (Kim §2), bipartite half.** `|Γᵢ(A,B)| ≤ bᵢ|A||B|` for
disjoint `A, B` of size at least `mcut n`.

Kim also states a unipartite half (`|Γᵢ(A,A)| ≤ bᵢ·C(|A|,2)`, proved "by an
analogous argument"), but it is never consumed: the sole use of Property 6 is
in `card_killedY2_split`, i.e. Kim's (44)–(48), where the two sets
`N_ℰ(w) ∩ T` and `N_{X'}(w) ∩ T` are disjoint. -/
def Property6 (s : BlockState V) (i : ℕ) : Prop :=
  ∀ A B : Finset V, Disjoint A B → mcut n ≤ A.card → mcut n ≤ B.card →
    ((gammaBetween s.Γ A B).card : ℝ) ≤ bSeq n i * A.card * B.card

/-- All eight properties are automatic at stage `0` for the initial state,
where `ℰ₀ = G₀ = ∅` — Properties 3, 4 and 5 all reduce to `0 ≤ …`. -/
lemma property3_zero (s : BlockState V) (hE : s.E = ∅) : Property3 s 0 := by
  intro v w _
  rw [hE]
  have hcard : (commonNbrs (∅ : Finset (Edge V)) v w).card = 0 := by
    classical
    rw [Finset.card_eq_zero]
    ext u
    simp only [Finset.notMem_empty, iff_false]
    intro hu
    obtain ⟨-, ⟨e, he, _⟩, -⟩ := mem_commonNbrs.mp hu
    exact absurd he (Finset.notMem_empty e)
  rw [hcard]
  simp

/-- **Property 1 (Kim §2).** `d_{ℰᵢ}(v) ≤ aᵢ √n + i n^{1/4} log n` for all
`v`. -/
def Property1 (s : BlockState V) (i : ℕ) : Prop :=
  ∀ v : V, (degEdges s.E v : ℝ)
    ≤ aSeq n i * Real.sqrt n + i * (n : ℝ) ^ (1 / 4 : ℝ) * Real.log n

/-- **Property 2 (Kim §2).** `d_{Γᵢ}(v) ≤ bᵢ n` for all `v`. -/
def Property2 (s : BlockState V) (i : ℕ) : Prop :=
  ∀ v : V, (degEdges s.Γ v : ℝ) ≤ bSeq n i * n

/-- `ε := (log log n)^{-1/4}` (Kim §2, Property 8). -/
noncomputable def kimEps (N : ℕ) : ℝ :=
  (Real.log (Real.log N)) ^ (-(1 : ℝ) / 4)

/-- `𝒯ᵢ := {T ⊆ V : |T| = t, E(Gᵢ) ∩ Γ₀(T) = ∅}` — the `t`-element vertex sets
spanning no edge of `Gᵢ` (Kim §2). -/
noncomputable def calT (s : BlockState V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun T => T.card = tParam n ∧
    ∀ e ∈ s.G, ¬ (∃ v ∈ T, ∃ w ∈ T, v ≠ w ∧ v ∈ e.val ∧ w ∈ e.val))

/-- **Property 7 (Kim §2).** The heart of the argument: for every
`T ∈ 𝒯ᵢ` (a `t`-element vertex set with no edge of `Gᵢ` inside),
the count of surviving edges `Γᵢ(T)` is at least `bᵢ μᵢ · (t choose 2)`. -/
def Property7 (s : BlockState V) (i : ℕ) : Prop :=
  ∀ T ∈ calT s,
    bSeq n i * μSeq n i * ((tParam n).choose 2)
      ≤ ((gammaBetween s.Γ T T).card : ℝ)

/-- **Property 8 (Kim §2).** Population bound on `𝒯ᵢ`:
`|𝒯ᵢ| ≤ nⁱ · (n choose t) · exp(-(1-ε) ∑_{j<i} bⱼμⱼθ/√n · (t choose 2))`
where `ε := (log log n)^{-1/4}` and `t := tParam n`. -/
def Property8 (s : BlockState V) (i : ℕ) : Prop :=
  ((calT s).card : ℝ)
    ≤ (n : ℝ) ^ i * (Nat.choose (Fintype.card V) (tParam n))
      * Real.exp (-(1 - kimEps n)
          * ∑ j ∈ Finset.range i,
              bSeq n j * μSeq n j * theta n / Real.sqrt n
                * ((tParam n).choose 2))

/-- All eight Properties at index `i`. -/
def Properties1to8 (s : BlockState V) (i : ℕ) : Prop :=
  Property1 s i ∧ Property2 s i ∧ Property3 s i ∧ Property4 s i
    ∧ Property5 s i ∧ Property6 s i ∧ Property7 s i ∧ Property8 s i



/-! ### Random sampling for `blockStep`

The block-construction step samples a random subset `X ⊆ Γₖ` by including
each edge of `Γₖ` independently with probability `θ/√n` (= `edgeProb n`). To
make this rigorous we set up:

* `edgeProbNNReal n : ℝ≥0` — the inclusion probability as an `ℝ≥0`;
* `edgeBernoulliMeasure n hn h_bound : Measure (Edge V → Bool)` — the product
  of i.i.d. `Bernoulli(edgeProb n)` measures over the edge index `Edge V`,
  obtained via `Measure.infinitePi`
  (`Mathlib/Probability/ProductMeasure.lean:354`) applied to
  `(PMF.bernoulli _ _).toMeasure`
  (`Mathlib/Probability/ProbabilityMassFunction/Constructions.lean:297`);
* `randomXFrom s ω` — the actual random `X ⊆ s.Γ` extracted by filtering
  `s.Γ` on `{e | ω e = true}`.

The `IsProbabilityMeasure` instance for `edgeBernoulliMeasure` is provided
for free by `Mathlib/Probability/ProductMeasure.lean:377`. The marginal of
including a single edge `e` is exactly `edgeProb n`, by
`Measure.infinitePi_map_eval` and `PMF.toMeasure_apply_singleton`. -/

/-- The sampled edge subset determined by a Bernoulli sample `σ`: keep the
`Γ`-edges whose index is selected. This is Kim's `X_{k+1} = X*_{k+1} ∩ Γ_k`. -/
noncomputable def sampleEdges {m : ℕ} (ι : Edge V ↪ Fin m) (s : BlockState V)
    (σ : Fin m → Bool) : Finset (Edge V) := by
  classical
  exact s.Γ.filter (fun e => σ (ι e) = true)

lemma sampleEdges_subset {m : ℕ} (ι : Edge V ↪ Fin m) (s : BlockState V)
    (σ : Fin m → Bool) : sampleEdges ι s σ ⊆ s.Γ :=
  Finset.filter_subset _ _

/-- For any `A ⊆ Γ`, the sampled edges inside `A` are exactly `A` filtered by
the sample. -/
lemma inter_sampleEdges {m : ℕ} (ι : Edge V ↪ Fin m) (s : BlockState V)
    (σ : Fin m → Bool) {A : Finset (Edge V)}
    (hA : A ⊆ s.Γ) :
    A ∩ sampleEdges ι s σ = A.filter (fun e => σ (ι e) = true) := by
  classical
  ext e
  simp only [Finset.mem_inter, sampleEdges, Finset.mem_filter]
  constructor
  · rintro ⟨heA, -, hσ⟩; exact ⟨heA, hσ⟩
  · rintro ⟨heA, hσ⟩; exact ⟨heA, hA heA, hσ⟩

/-- **Master counting bridge**: for `A ⊆ Γ`, the number of sampled edges in `A`
is the count functional over `A`'s indices. Specialising `A` gives Kim's
`|N_{X'}(v)|` (Lemma 4.3(i)), `|N_ℰ(v) ∩ N_{X'}(w)|` (Lemma 4.3(ii)) and
`|X' ∩ Γ(T)|` ((38)). -/
lemma card_inter_sampleEdges_eq {m : ℕ} (ι : Edge V ↪ Fin m) (s : BlockState V)
    (σ : Fin m → Bool) {A : Finset (Edge V)}
    (hA : A ⊆ s.Γ) :
    ((A ∩ sampleEdges ι s σ).card : ℝ)
      = ∑ j ∈ A.image ι, (if σ j = true then (1 : ℝ) else 0) := by
  classical
  rw [Finset.sum_image (fun a _ b _ h => ι.injective h)]
  rw [inter_sampleEdges ι s σ hA, Finset.card_filter]
  push_cast
  rfl

lemma card_image_eq {m : ℕ} (ι : Edge V ↪ Fin m) (A : Finset (Edge V)) :
    (A.image ι).card = A.card :=
  Finset.card_image_of_injective _ ι.injective

/-- **Concentration for the number of sampled edges in any `A ⊆ Γ`.**

This is the single estimate behind Kim's Lemma 4.3(i),(ii) and (38):
`Pr( |A ∩ X'| ≥ p|A| + λ ) ≤ 2·exp(−tλ + (t²/2)·p(1−p)·|A|·e^t)`. -/
theorem sampleEdges_inter_concentration {m : ℕ} (ι : Edge V ↪ Fin m) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (s : BlockState V) {A : Finset (Edge V)} (hA : A ⊆ s.Γ)
    {t lam : ℝ} (ht : 0 ≤ t) :
    bernoulliPr p (Finset.univ.filter (fun σ =>
        p * (A.card : ℝ) + lam ≤ ((A ∩ sampleEdges ι s σ).card : ℝ)))
      ≤ 2 * Real.exp (-t * lam
          + t ^ 2 / 2 * (p * (1 - p) * ((A.card : ℝ) * Real.exp t))) := by
  classical
  set S : Finset (Fin m) := A.image ι with hS
  have hcard : (S.card : ℝ) = (A.card : ℝ) := by
    rw [hS, card_image_eq ι]
  have hset : (Finset.univ.filter (fun σ =>
        p * (A.card : ℝ) + lam ≤ ((A ∩ sampleEdges ι s σ).card : ℝ)))
      = (Finset.univ.filter (fun σ =>
        p * (S.card : ℝ) + lam
          ≤ ∑ j ∈ S, (if σ j = true then (1 : ℝ) else 0))) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [card_inter_sampleEdges_eq ι s σ hA, hcard, hS]
  rw [hset, ← hcard]
  exact bernoulliPr_count_ge_threshold hp₀ hp₁ S ht

/-- **Half-exponent packaging.** Whenever the variance term is at most half of
`tλ`, the concentration bound collapses to the clean form `2·exp(−tλ/2)`.
Every application of Kim's §4.3–4.6 estimates reduces to verifying this single
hypothesis and then bounding `tλ` from below. -/
theorem sampleEdges_inter_tail {m : ℕ} (ι : Edge V ↪ Fin m) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (s : BlockState V) {A : Finset (Edge V)} (hA : A ⊆ s.Γ)
    {t lam : ℝ} (ht : 0 ≤ t)
    (hvar : t ^ 2 / 2 * (p * (1 - p) * ((A.card : ℝ) * Real.exp t))
              ≤ t * lam / 2) :
    bernoulliPr p (Finset.univ.filter (fun σ =>
        p * (A.card : ℝ) + lam ≤ ((A ∩ sampleEdges ι s σ).card : ℝ)))
      ≤ 2 * Real.exp (-(t * lam) / 2) := by
  refine le_trans (sampleEdges_inter_concentration ι hp₀ hp₁ s hA ht) ?_
  have : -t * lam + t ^ 2 / 2 * (p * (1 - p) * ((A.card : ℝ) * Real.exp t))
      ≤ -(t * lam) / 2 := by linarith
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr this) (by norm_num)

/-- Bridge from a tail exponent to an `N⁻ᵐ` failure probability. -/
lemma two_exp_le_inv_pow {N : ℕ} (hN : 0 < N) (m : ℕ) {r : ℝ}
    (h : Real.log 2 + m * Real.log N ≤ r) :
    2 * Real.exp (-r) ≤ ((N : ℝ) ^ m)⁻¹ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hstep : 2 * Real.exp (-r)
      ≤ 2 * Real.exp (-(Real.log 2 + m * Real.log N)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  refine hstep.trans (le_of_eq ?_)
  rw [neg_add, Real.exp_add, Real.exp_neg,
    Real.exp_log (by norm_num : (0:ℝ) < 2), Real.exp_neg,
    show (m : ℝ) * Real.log N = Real.log ((N : ℝ) ^ m) by
      rw [Real.log_pow],
    Real.exp_log (by positivity)]
  field_simp

/-- **The shape every exponent estimate in §4 reduces to.**
`exp(−A + B) ≤ N^{−m}` exactly when the net exponent `A − B` beats
`m·log N`. -/
lemma exp_le_inv_pow {N : ℕ} (hN : 0 < N) (m : ℕ) {A B : ℝ}
    (h : (m : ℝ) * Real.log N ≤ A - B) :
    Real.exp (-A + B) ≤ ((N : ℝ) ^ m)⁻¹ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hrw : ((N : ℝ) ^ m)⁻¹ = Real.exp (-((m : ℝ) * Real.log N)) := by
    rw [Real.exp_neg,
      show (m : ℝ) * Real.log N = Real.log ((N : ℝ) ^ m) by
        rw [Real.log_pow],
      Real.exp_log (by positivity)]
  rw [hrw]
  exact Real.exp_le_exp.mpr (by linarith)


/-- Bridge from a tail exponent to Kim's `n⁻³` failure probability:
if the exponent is at least `log 2 + 3 log N`, the bound is at most `N⁻³`. -/
lemma two_exp_le_inv_cube {N : ℕ} (hN : 0 < N) {r : ℝ}
    (h : Real.log 2 + 3 * Real.log N ≤ r) :
    2 * Real.exp (-r) ≤ ((N : ℝ) ^ (3 : ℕ))⁻¹ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hstep : 2 * Real.exp (-r)
      ≤ 2 * Real.exp (-(Real.log 2 + 3 * Real.log N)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  refine hstep.trans (le_of_eq ?_)
  rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2),
    Real.exp_neg, show (3 : ℝ) * Real.log N = Real.log ((N : ℝ) ^ (3 : ℕ)) by
      rw [Real.log_pow]; push_cast; ring,
    Real.exp_log (by positivity)]
  field_simp

/-- **Kim's Lemma 4.3(i), packaged with the `n⁻³` failure probability.**
`Pr( |N_{X'}(v)| ≥ p·d_Γ(v) + λ ) ≤ n⁻³` under the two numeric side conditions. -/
theorem lemma43_i_cube {m : ℕ} (ι : Edge V ↪ Fin m) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (s : BlockState V) (v : V) {t lam : ℝ} (ht : 0 ≤ t) (hn : 0 < n)
    (hvar : t ^ 2 / 2
        * (p * (1 - p) * ((degEdges s.Γ v : ℝ) * Real.exp t)) ≤ t * lam / 2)
    (hexp : Real.log 2 + 3 * Real.log n ≤ t * lam / 2) :
    bernoulliPr p (Finset.univ.filter (fun σ =>
        p * (degEdges s.Γ v : ℝ) + lam ≤ (degEdges (sampleEdges ι s σ) v : ℝ)))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹ := by
  classical
  have hA : edgesAt s.Γ v ⊆ s.Γ := Finset.filter_subset _ _
  have hcard : ((edgesAt s.Γ v).card : ℝ) = (degEdges s.Γ v : ℝ) := by
    rw [degEdges]
  have hkey := sampleEdges_inter_tail ι hp₀ hp₁ s hA ht (by rw [hcard]; exact hvar)
  have hset : (Finset.univ.filter (fun σ =>
        p * (degEdges s.Γ v : ℝ) + lam ≤ (degEdges (sampleEdges ι s σ) v : ℝ)))
      = (Finset.univ.filter (fun σ =>
        p * ((edgesAt s.Γ v).card : ℝ) + lam
          ≤ (((edgesAt s.Γ v) ∩ sampleEdges ι s σ).card : ℝ))) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcard]
    rw [show ((edgesAt s.Γ v) ∩ sampleEdges ι s σ)
        = edgesAt (sampleEdges ι s σ) v from ?_]
    · rfl
    · ext e
      simp only [Finset.mem_inter, edgesAt, Finset.mem_filter, sampleEdges]
      tauto
  rw [hset]
  refine hkey.trans ?_
  rw [neg_div]
  exact two_exp_le_inv_cube hn hexp



/-! ### Structural facts about `blockStep`

With the (corrected, Kim-faithful) monotone definition of `Γ`, the following
inclusions hold unconditionally and are the backbone of any propagation
argument for Properties 1 and 2. -/

@[simp] lemma blockStep_E (s : BlockState V) (X : Finset (Edge V))
    (hX : X ⊆ s.Γ) : (blockStep s X hX).E = s.E ∪ X := rfl

lemma blockStep_Γ_subset_sdiff (s : BlockState V) (X : Finset (Edge V))
    (hX : X ⊆ s.Γ) : (blockStep s X hX).Γ ⊆ s.Γ \ X := by
  classical
  intro e he
  exact Finset.mem_of_mem_filter _ he

/-- **`Γ` is monotone decreasing along `blockStep`.** -/
lemma blockStep_Γ_subset (s : BlockState V) (X : Finset (Edge V))
    (hX : X ⊆ s.Γ) : (blockStep s X hX).Γ ⊆ s.Γ :=
  fun _ he => (Finset.mem_sdiff.mp (blockStep_Γ_subset_sdiff s X hX he)).1

/-- **Property 1 propagation — the deterministic core of Kim §4.2.**

Kim's computation is
`d_{ℰ'}(v) = d_ℰ(v) + |N_{X'}(v)| ≤ a√n + k·n^{1/4}log n + bθ√n + n^{1/4}log n
           = a'√n + (k+1)·n^{1/4}log n`,
using `a_{k+1} = a_k + b_k θ` (`aSeq_succ`). Everything except the bound on
the `X`-degree is deterministic; that bound is Lemma 4.3(i), the only
probabilistic input, and is exactly a linear indicator sum of the kind
`kahn_concentration` handles. -/
lemma property1_step (k : ℕ) (s : BlockState V) (X : Finset (Edge V))
    (hX : X ⊆ s.Γ) (h1 : Property1 s k)
    (hXdeg : ∀ v : V, (degEdges X v : ℝ)
      ≤ bSeq n k * theta n * Real.sqrt n
        + (n : ℝ) ^ (1 / 4 : ℝ) * Real.log n) :
    Property1 (blockStep s X hX) (k + 1) := by
  intro v
  rw [blockStep_E]
  have hunion : (degEdges (s.E ∪ X) v : ℝ)
      ≤ (degEdges s.E v : ℝ) + (degEdges X v : ℝ) := by
    exact_mod_cast degEdges_union_le s.E X v
  have hE := h1 v
  have hXv := hXdeg v
  have hsucc : aSeq n (k + 1) = aSeq n k + bSeq n k * theta n := aSeq_succ n k
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hsucc, hcast]
  nlinarith [hunion, hE, hXv]

/-- **Property 4 propagation (Kim §4.5), final combination.**

Kim's closing computation is
`Φ⁽¹⁾ + Φ⁽²⁾ ≤ b'(a+5θ)√n − 2b²θ²(a+5θ)√n + b²θ√n ≤ b'(a'+5θ)√n`,
where the two bounds on `Φ⁽¹⁾, Φ⁽²⁾` are (25) and (24) — the concentration
input — and the last inequality is Lemma 2.2(14) — now proved as `bSeq_sq_sub_le` —
scaled by `θ√n`, using `a' = a + bθ`. -/
lemma property4_combine {k : ℕ} {Phi1 Phi2 : ℝ}
    (hPhi1 : Phi1 ≤ bSeq n (k + 1) * (aSeq n k + 5 * theta n) * Real.sqrt n
        - 3 * bSeq n k ^ 2 * theta n ^ 2 * (aSeq n k + 5 * theta n)
          * Real.sqrt n)
    (hPhi2 : Phi2 ≤ bSeq n k ^ 2 * theta n * Real.sqrt n
        + bSeq n k ^ 2 * theta n ^ 2 * (aSeq n k + 5 * theta n)
          * Real.sqrt n) :
    Phi1 + Phi2
      ≤ bSeq n (k + 1) * (aSeq n (k + 1) + 5 * theta n) * Real.sqrt n := by
  have h14 := bSeq_sq_sub_le n k
  have hsucc : aSeq n (k + 1) = aSeq n k + bSeq n k * theta n := aSeq_succ n k
  have hθ : 0 ≤ theta n := theta_nonneg n
  have hsq : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  rw [hsucc]
  -- Multiply (14) by `θ√n ≥ 0` and add the two concentration bounds.
  have hscaled := mul_le_mul_of_nonneg_right h14 (mul_nonneg hθ hsq)
  nlinarith [hPhi1, hPhi2, hscaled, hθ, hsq]


/-- **Property 3 propagation (Kim §4.4), complete given Lemma 4.3(ii),(iii).**

`|N_{ℰ'}(v) ∩ N_{ℰ'}(w)| ≤ 3k log n + log n + log n + log n = 3(k+1) log n`,
where the first term is Property 3 at stage `k` and the last three are
Lemma 4.3(ii),(iii) — each a linear indicator sum handled by Corollary 3.3. -/
lemma property3_step (k : ℕ) (s : BlockState V) (X : Finset (Edge V))
    (hX : X ⊆ s.Γ) (h3 : Property3 s k)
    (hXE : ∀ v w : V, v ≠ w → ((nbrs X v ∩ nbrs s.E w).card : ℝ) ≤ Real.log n)
    (hEX : ∀ v w : V, v ≠ w → ((nbrs s.E v ∩ nbrs X w).card : ℝ) ≤ Real.log n)
    (hXX : ∀ v w : V, v ≠ w → ((commonNbrs X v w).card : ℝ) ≤ Real.log n) :
    Property3 (blockStep s X hX) (k + 1) := by
  intro v w hvw
  rw [blockStep_E]
  have hdecomp : ((commonNbrs (s.E ∪ X) v w).card : ℝ)
      ≤ ((commonNbrs s.E v w).card : ℝ)
        + ((nbrs X v ∩ nbrs s.E w).card : ℝ)
        + ((nbrs s.E v ∩ nbrs X w).card : ℝ)
        + ((commonNbrs X v w).card : ℝ) := by
    exact_mod_cast commonNbrs_union_card_le s.E X v w
  have hk := h3 v w hvw
  have h2 := hXE v w hvw
  have h3' := hEX v w hvw
  have h4 := hXX v w hvw
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  nlinarith [hdecomp, hk, h2, h3', h4]





/-- `d_{Λ}(e_vw, v)` counted as an intersection of neighbourhoods:
`N_Λ(e_vw, v) = N_Γ(v) ∩ N_ℰ(w)`. -/
lemma lambdaDeg_eq_card_inter (E Γ : Finset (Edge V)) (v w : V) :
    lambdaDeg E Γ v w = (nbrs Γ v ∩ nbrs E w).card := by
  classical
  have hset : (Finset.univ.filter (fun u => (u ≠ v ∧ u ≠ w) ∧
      (∃ e ∈ Γ, u ∈ e.val ∧ v ∈ e.val) ∧ (∃ f ∈ E, u ∈ f.val ∧ w ∈ f.val)))
      = nbrs Γ v ∩ nbrs E w := by
    ext u
    rw [Finset.mem_filter, Finset.mem_inter, mem_nbrs, mem_nbrs]
    constructor
    · rintro ⟨-, ⟨hnv, hnw⟩, ⟨e, he, hu, hv⟩, ⟨f, hf, hu', hw⟩⟩
      exact ⟨⟨hnv, e, he, hv, hu⟩, ⟨hnw, f, hf, hw, hu'⟩⟩
    · rintro ⟨⟨hnv, e, he, hv, hu⟩, ⟨hnw, f, hf, hw, hu'⟩⟩
      exact ⟨Finset.mem_univ u, ⟨hnv, hnw⟩, ⟨e, he, hu, hv⟩, ⟨f, hf, hu', hw⟩⟩
  show (Finset.univ.filter _).card = _
  rw [hset]

/-- `a₀ = 0`. -/
lemma aSeq_zero' (N : ℕ) : aSeq N 0 = 0 := by simp [aSeq]

/-- `b₀ = 1`. -/
lemma bSeq_zero' (N : ℕ) : bSeq N 0 = 1 := by
  unfold bSeq; norm_num [spencerPsi_zero]

/-- **Property 1 at stage 0**: `d_{∅}(v) = 0 ≤ 0`. -/
lemma property1_init : Property1 (initBlockState V) 0 := by
  intro v
  show ((degEdges (initBlockState V).E v : ℕ) : ℝ) ≤ _
  rw [show (initBlockState V).E = (∅ : Finset (Edge V)) from rfl, aSeq_zero']
  simp

/-- **Property 3 at stage 0**: `N_{∅}(v) ∩ N_{∅}(w) = ∅`. -/
lemma property3_init : Property3 (initBlockState V) 0 :=
  property3_zero (initBlockState V) rfl

/-- **Property 4 at stage 0**: `d_{Λ₀} = 0` since `ℰ₀ = ∅`. -/
lemma property4_init : Property4 (initBlockState V) 0 := by
  intro v w hvw _
  have hzero : lambdaDeg (initBlockState V).E (initBlockState V).Γ v w = 0 := by
    rw [lambdaDeg_eq_card_inter]
    have hemp : nbrs (initBlockState V).E w = ∅ := by
      classical
      ext u
      simp only [Finset.notMem_empty, iff_false, mem_nbrs]
      rintro ⟨-, e, he, -, -⟩
      exact absurd he (Finset.notMem_empty e)
    rw [hemp, Finset.inter_empty, Finset.card_empty]
  rw [hzero, aSeq_zero', bSeq_zero']
  have hθ : 0 ≤ theta n := theta_nonneg n
  have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  push_cast
  positivity

/-- **Property 5 at stage 0**: `d_{Δ₀}(e) ≤ n = b₀²·n`. -/
lemma property5_init : Property5 (initBlockState V) 0 := by
  intro v w hvw _
  rw [bSeq_zero']
  have h := codegEdges_le_card (initBlockState V).Γ v w
  have hcast : ((codegEdges (initBlockState V).Γ v w : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast h
  simpa using hcast

/-! ### Endpoints of an edge

`Edge V = {e : Sym2 V // ¬ e.IsDiag}`, so an edge containing `v` has a unique
other endpoint. This gives the basic degree bound `d_E(v) ≤ n` and the
counting facts Properties 2, 6, 7 need. -/

/-- The other endpoint of `e` at `v` (junk value `v` if `v ∉ e`). -/
noncomputable def otherEndOf (v : V) (e : Edge V) : V := by
  classical
  exact if h : v ∈ e.val then Sym2.Mem.other h else v

lemma edge_eq_of_otherEndOf {v : V} {e : Edge V} (h : v ∈ e.val) :
    e.val = s(v, otherEndOf v e) := by
  classical
  unfold otherEndOf
  rw [dif_pos h]
  exact (Sym2.other_spec h).symm

/-- Two distinct edges through `v` have distinct other ends. -/
lemma otherEndOf_ne_of_ne {u : V} {e g : Edge V} (he : u ∈ e.val)
    (hg : u ∈ g.val) (hne : e ≠ g) : otherEndOf u e ≠ otherEndOf u g := by
  intro hEq
  exact hne (Subtype.ext (by
    rw [edge_eq_of_otherEndOf he, edge_eq_of_otherEndOf hg, hEq]))

/-- The two endpoints of an edge: anything in it other than `y` is `y`'s
partner. -/
lemma eq_otherEndOf_of_mem {f : Edge V} {y z : V} (hy : y ∈ f.val)
    (hz : z ∈ f.val) (hne : z ≠ y) : z = otherEndOf y f := by
  have hval := edge_eq_of_otherEndOf hy
  rw [hval, Sym2.mem_iff] at hz
  rcases hz with h | h
  · exact absurd h hne
  · exact h

/-- `otherEndOf v` is injective on the edges incident to `v`. -/
lemma otherEndOf_injOn (E : Finset (Edge V)) (v : V) :
    Set.InjOn (otherEndOf v) (edgesAt E v : Set (Edge V)) := by
  classical
  intro e he e' he' hEq
  have hv : v ∈ e.val := by
    have := Finset.mem_coe.mp he
    exact (Finset.mem_filter.mp this).2
  have hv' : v ∈ e'.val := by
    have := Finset.mem_coe.mp he'
    exact (Finset.mem_filter.mp this).2
  apply Subtype.ext
  rw [edge_eq_of_otherEndOf hv, edge_eq_of_otherEndOf hv', hEq]

/-- **Degrees are at most `n`.** Each incident edge is determined by its other
endpoint. -/
lemma degEdges_le_card_verts (E : Finset (Edge V)) (v : V) :
    degEdges E v ≤ Fintype.card V := by
  classical
  unfold degEdges
  calc (edgesAt E v).card
      ≤ ((edgesAt E v).image (otherEndOf v)).card := by
        rw [Finset.card_image_of_injOn (otherEndOf_injOn E v)]
    _ ≤ (Finset.univ : Finset V).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card V := Finset.card_univ

/-- **Property 2 at stage 0**: `d_{Γ₀}(v) ≤ n = b₀·n`. -/
lemma property2_init : Property2 (initBlockState V) 0 := by
  intro v
  rw [bSeq_zero', one_mul]
  have h := degEdges_le_card_verts (initBlockState V).Γ v
  exact_mod_cast h

/-- The `Γ`-edges at `w` whose other endpoint is an `ℰ`-neighbour of `v`.
Sampling inside this set is exactly what produces `N_ℰ(v) ∩ N_{X'}(w)`. -/
noncomputable def crossEdges (s : BlockState V) (v w : V) : Finset (Edge V) := by
  classical
  exact (edgesAt s.Γ w).filter (fun e => otherEndOf w e ∈ nbrs s.E v)

lemma crossEdges_subset (s : BlockState V) (v w : V) :
    crossEdges s v w ⊆ s.Γ :=
  (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

/-- **Kim's Lemma 4.3(ii), combinatorial half.** Every vertex of
`N_ℰ(v) ∩ N_{X'}(w)` is the far endpoint of a sampled cross edge, so the
codegree is bounded by the number of sampled cross edges. -/
lemma card_nbrs_inter_sample_le {m : ℕ} (ι : Edge V ↪ Fin m) (s : BlockState V)
    (σ : Fin m → Bool) (v w : V) :
    (nbrs s.E v ∩ nbrs (sampleEdges ι s σ) w).card
      ≤ (crossEdges s v w ∩ sampleEdges ι s σ).card := by
  classical
  refine Finset.card_le_card_of_surjOn (otherEndOf w) ?_
  intro u hu
  obtain ⟨huE, huX⟩ := Finset.mem_inter.mp (Finset.mem_coe.mp hu)
  obtain ⟨hune, e, heX, hwe, hue⟩ := mem_nbrs.mp huX
  have hother : otherEndOf w e = u := by
    have hspec : e.val = s(w, otherEndOf w e) := edge_eq_of_otherEndOf hwe
    rw [hspec] at hue
    rcases Sym2.mem_iff.mp hue with h | h
    · exact absurd h hune
    · exact h.symm
  have heΓ : e ∈ s.Γ := (Finset.mem_filter.mp heX).1
  have hmem : e ∈ crossEdges s v w ∩ sampleEdges ι s σ := by
    refine Finset.mem_inter.mpr ⟨?_, heX⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heΓ, hwe⟩, ?_⟩
    rw [hother]; exact huE
  rw [← hother]
  exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hmem)

/-- The far-endpoint map is a bijection from `crossEdges s v w` onto
`N_Γ(w) ∩ N_ℰ(v)`. -/
lemma image_otherEndOf_crossEdges (s : BlockState V) (v w : V) :
    (crossEdges s v w).image (otherEndOf w) = nbrs s.Γ w ∩ nbrs s.E v := by
  classical
  ext u
  simp only [Finset.mem_image, Finset.mem_inter]
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨heAt, hEnd⟩ := Finset.mem_filter.mp he
    obtain ⟨heΓ, hwe⟩ := Finset.mem_filter.mp heAt
    have hne : otherEndOf w e ≠ w := by
      intro hEq
      have hspec : e.val = s(w, otherEndOf w e) := edge_eq_of_otherEndOf hwe
      exact e.2 (by rw [hspec, hEq]; simp)
    refine ⟨mem_nbrs.mpr ⟨hne, e, heΓ, hwe, ?_⟩, hEnd⟩
    rw [edge_eq_of_otherEndOf hwe]; simp
  · rintro ⟨hΓ, hE⟩
    obtain ⟨hne, e, heΓ, hwe, hue⟩ := mem_nbrs.mp hΓ
    have hother : otherEndOf w e = u := by
      have hspec : e.val = s(w, otherEndOf w e) := edge_eq_of_otherEndOf hwe
      rw [hspec] at hue
      rcases Sym2.mem_iff.mp hue with h | h
      · exact absurd h hne
      · exact h.symm
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heΓ, hwe⟩,
      by rw [hother]; exact hE⟩, hother⟩

/-- **`|Γ_w(v)| = d_Λ(e_vw, v)`.** Kim's `Λ`-degree counts vertices; the
concentration argument counts the corresponding edges. The two agree. -/
lemma card_crossEdges_eq_lambdaDeg (s : BlockState V) (v w : V) :
    (crossEdges s v w).card = lambdaDeg s.E s.Γ w v := by
  classical
  rw [lambdaDeg_eq_card_inter, ← image_otherEndOf_crossEdges s v w]
  refine (Finset.card_image_of_injOn ?_).symm
  intro e he e' he' hEq
  refine otherEndOf_injOn s.Γ w ?_ ?_ hEq
  · exact Finset.mem_coe.mpr (Finset.mem_filter.mp
      (Finset.mem_coe.mp he)).1
  · exact Finset.mem_coe.mpr (Finset.mem_filter.mp
      (Finset.mem_coe.mp he')).1

/-- The far-endpoint map identifies the edges at `v` with the neighbours of
`v`. -/
lemma image_otherEndOf_edgesAt (F : Finset (Edge V)) (v : V) :
    (edgesAt F v).image (otherEndOf v) = nbrs F v := by
  classical
  ext u
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨heF, hve⟩ := Finset.mem_filter.mp he
    have hne : otherEndOf v e ≠ v := by
      intro hEq
      exact e.2 (by rw [edge_eq_of_otherEndOf hve, hEq]; simp)
    refine mem_nbrs.mpr ⟨hne, e, heF, hve, ?_⟩
    rw [edge_eq_of_otherEndOf hve]; simp
  · intro hu
    obtain ⟨hne, e, heF, hve, hue⟩ := mem_nbrs.mp hu
    have hother : otherEndOf v e = u := by
      have hspec : e.val = s(v, otherEndOf v e) := edge_eq_of_otherEndOf hve
      rw [hspec] at hue
      rcases Sym2.mem_iff.mp hue with h | h
      · exact absurd h hne
      · exact h.symm
    exact ⟨e, Finset.mem_filter.mpr ⟨heF, hve⟩, hother⟩

/-- `|N_F(v)| = d_F(v)`: neighbours and incident edges are in bijection. -/
lemma card_nbrs_eq_degEdges (F : Finset (Edge V)) (v : V) :
    (nbrs F v).card = degEdges F v := by
  classical
  rw [← image_otherEndOf_edgesAt F v,
    Finset.card_image_of_injOn (otherEndOf_injOn F v)]
  rfl

/-- **Kim's `|Γ_w(v)| ≤ d_ℰ(v)`**, the bound behind `E[Φ⁽¹⁾_{v,w}] ≤ p·d_ℰ(v)`
in Lemma 4.3(ii): each cross edge is determined by its far endpoint, which is
an `ℰ`-neighbour of `v`. -/
lemma card_crossEdges_le_degE (s : BlockState V) (v w : V) :
    (crossEdges s v w).card ≤ degEdges s.E v := by
  classical
  rw [← card_nbrs_eq_degEdges s.E v]
  calc (crossEdges s v w).card
      = ((crossEdges s v w).image (otherEndOf w)).card := by
        refine (Finset.card_image_of_injOn ?_).symm
        intro e he e' he' hEq
        refine otherEndOf_injOn s.Γ w ?_ ?_ hEq
        · exact Finset.mem_coe.mpr (Finset.mem_filter.mp
            (Finset.mem_coe.mp he)).1
        · exact Finset.mem_coe.mpr (Finset.mem_filter.mp
            (Finset.mem_coe.mp he')).1
    _ = (nbrs s.Γ w ∩ nbrs s.E v).card := by
        rw [image_otherEndOf_crossEdges]
    _ ≤ (nbrs s.E v).card := Finset.card_le_card Finset.inter_subset_right


/-- The edges joining a vertex set `U` to the pair `{v, w}`. For `U` disjoint
from `{v,w}` this is exactly `{ {u,v} : u ∈ U } ∪ { {u,w} : u ∈ U }`, a set of
`2|U|` edges. -/
noncomputable def linkEdges (U : Finset V) (v w : V) : Finset (Edge V) := by
  classical
  exact Finset.univ.filter
    (fun e => ∃ u ∈ U, u ∈ e.val ∧ (v ∈ e.val ∨ w ∈ e.val))

lemma mem_linkEdges {U : Finset V} {v w : V} {e : Edge V} :
    e ∈ linkEdges U v w ↔ ∃ u ∈ U, u ∈ e.val ∧ (v ∈ e.val ∨ w ∈ e.val) := by
  classical
  show e ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ e, h⟩⟩

/-- The classifying map used to count `linkEdges`: an edge is sent to its
`U`-endpoint together with a flag saying which of `v, w` it meets. -/
noncomputable def linkTag (v w : V) (e : Edge V) : V × Bool := by
  classical
  exact if v ∈ e.val then (otherEndOf v e, true) else (otherEndOf w e, false)

/-- **`linkEdges` has at least `2|U|` elements.** Proved by exhibiting
`linkTag` as a surjection onto `U ×ˢ Bool`. -/
lemma two_mul_card_le_card_linkEdges {U : Finset V} {v w : V} (hvw : v ≠ w)
    (hU : ∀ u ∈ U, u ≠ v ∧ u ≠ w) :
    2 * U.card ≤ (linkEdges U v w).card := by
  classical
  have hsurj : Set.SurjOn (linkTag v w) (linkEdges U v w : Set (Edge V))
      ((U ×ˢ (Finset.univ : Finset Bool) : Finset (V × Bool)) : Set (V × Bool)) := by
    rintro ⟨u, b⟩ hub
    obtain ⟨huU, -⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hub)
    obtain ⟨hnv, hnw⟩ := hU u huU
    cases b with
    | true =>
        refine ⟨mkEdge hnv, Finset.mem_coe.mpr (mem_linkEdges.mpr
          ⟨u, huU, by simp, Or.inl (by simp)⟩), ?_⟩
        have hv : v ∈ (mkEdge hnv).val := by simp
        have hspec : (mkEdge hnv).val = s(v, otherEndOf v (mkEdge hnv)) :=
          edge_eq_of_otherEndOf hv
        rw [mkEdge_val, Sym2.eq_swap] at hspec
        have : u = otherEndOf v (mkEdge hnv) := (Sym2.congr_right).mp hspec
        show (if v ∈ (mkEdge hnv).val then _ else _) = _
        rw [if_pos hv, ← this]
    | false =>
        refine ⟨mkEdge hnw, Finset.mem_coe.mpr (mem_linkEdges.mpr
          ⟨u, huU, by simp, Or.inr (by simp)⟩), ?_⟩
        have hvnot : v ∉ (mkEdge hnw).val := by
          rw [mkEdge_val]
          simp only [Sym2.mem_iff]
          rintro (h | h)
          · exact hnv h.symm
          · exact hvw h
        have hw : w ∈ (mkEdge hnw).val := by simp
        have hspec : (mkEdge hnw).val = s(w, otherEndOf w (mkEdge hnw)) :=
          edge_eq_of_otherEndOf hw
        rw [mkEdge_val, Sym2.eq_swap] at hspec
        have : u = otherEndOf w (mkEdge hnw) := (Sym2.congr_right).mp hspec
        show (if v ∈ (mkEdge hnw).val then _ else _) = _
        rw [if_neg hvnot, ← this]
  have hcard := Finset.card_le_card_of_surjOn (linkTag v w) hsurj
  rwa [Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm] at hcard

/-- An edge containing two distinct vertices *is* that pair. -/
lemma edge_eq_of_two_mem {e : Edge V} {v w : V} (hv : v ∈ e.val)
    (hw : w ∈ e.val) (hvw : v ≠ w) : e.val = s(v, w) := by
  have hspec := Sym2.other_spec hv
  have hw' : w ∈ s(v, Sym2.Mem.other hv) := by rw [hspec]; exact hw
  rw [Sym2.mem_iff] at hw'
  rcases hw' with h | h
  · exact absurd h.symm hvw
  · rw [← hspec, h]

/-- If every vertex of `U` is a common `X'`-neighbour of `v` and `w`, then all
`2|U|` link edges of `U` are present in the sample. -/
lemma linkEdges_sampled {m : ℕ} (ι : Edge V ↪ Fin m) (s : BlockState V)
    (σ : Fin m → Bool) (v w : V) {U : Finset V}
    (hU : U ⊆ nbrs (sampleEdges ι s σ) v ∩ nbrs (sampleEdges ι s σ) w) :
    ∀ e ∈ linkEdges U v w, σ (ι e) = true := by
  classical
  intro e he
  obtain ⟨u, huU, hue, hvw'⟩ := mem_linkEdges.mp he
  obtain ⟨huv, huw⟩ := Finset.mem_inter.mp (hU huU)
  have key : ∀ x : V, x ∈ e.val → u ∈ nbrs (sampleEdges ι s σ) x →
      σ (ι e) = true := by
    intro x hxe hux
    obtain ⟨hne, f, hfX, hxf, huf⟩ := mem_nbrs.mp hux
    have hef : e = f := by
      apply Subtype.ext
      rw [edge_eq_of_two_mem hue hxe hne, edge_eq_of_two_mem huf hxf hne]
    rw [hef]
    exact (Finset.mem_filter.mp hfX).2
  rcases hvw' with h | h
  · exact key v h huv
  · exact key w h huw

/-- **Kim's Lemma 4.3(iii).** The chance that `v` and `w` acquire `l` common
neighbours in the sample is at most `C(n, l)·p^{2l}`: each of the `l` common
neighbours forces two independent edges to be present. -/
theorem lemma43_iii {m : ℕ} (ι : Edge V ↪ Fin m) (s : BlockState V) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (v w : V) (hvw : v ≠ w) (l : ℕ) :
    bernoulliPr p (Finset.univ.filter (fun σ =>
        l ≤ (nbrs (sampleEdges ι s σ) v ∩ nbrs (sampleEdges ι s σ) w).card))
      ≤ (Nat.choose n l : ℝ) * p ^ (2 * l) := by
  classical
  set W : Finset V := Finset.univ.filter (fun u => u ≠ v ∧ u ≠ w) with hW
  set Idx : Finset (Finset V) := W.powersetCard l with hIdx
  set Bad : Finset V → Finset (Fin m → Bool) :=
    fun U => Finset.univ.filter
      (fun σ => ∀ j ∈ (linkEdges U v w).image ι, σ j = true) with hBad
  -- Step 1: the event is covered by the `Bad U`.
  have hcover : (Finset.univ.filter (fun σ =>
      l ≤ (nbrs (sampleEdges ι s σ) v ∩ nbrs (sampleEdges ι s σ) w).card))
      ⊆ Idx.biUnion Bad := by
    intro σ hσ
    obtain ⟨-, hle⟩ := Finset.mem_filter.mp hσ
    obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq hle
    have hUW : U ⊆ W := by
      intro u hu
      obtain ⟨h1, h2⟩ := Finset.mem_inter.mp (hUsub hu)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u,
        (mem_nbrs.mp h1).1, (mem_nbrs.mp h2).1⟩
    refine Finset.mem_biUnion.mpr ⟨U, Finset.mem_powersetCard.mpr ⟨hUW, hUcard⟩, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro j hj
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
    exact linkEdges_sampled ι s σ v w hUsub e he
  -- Step 2: each `Bad U` has probability at most `p^{2l}`.
  have hBadPr : ∀ U ∈ Idx, bernoulliPr p (Bad U) ≤ p ^ (2 * l) := by
    intro U hUIdx
    obtain ⟨hUW, hUcard⟩ := Finset.mem_powersetCard.mp hUIdx
    rw [hBad, bernoulliPr_all_true, card_image_eq ι]
    refine pow_le_pow_of_le_one hp₀ hp₁ ?_
    rw [← hUcard]
    exact two_mul_card_le_card_linkEdges hvw
      (fun u hu => (Finset.mem_filter.mp (hUW hu)).2)
  -- Step 3: union bound.
  refine le_trans (bernoulliPr_mono hp₀ hp₁ hcover) ?_
  refine le_trans (bernoulliPr_biUnion_le hp₀ hp₁ Idx Bad) ?_
  refine le_trans (Finset.sum_le_sum hBadPr) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [hIdx, Finset.card_powersetCard]
  exact_mod_cast Nat.choose_le_choose l (Finset.card_le_univ W)

/-- **Lemma 4.3(iii), packaged with the `n⁻³` failure probability.**
With Kim's parameters `p = θ/√n` one has `n·p² = θ²`, so the bound reads
`θ^{2l}/l!`, which for `l = ⌈log n⌉` is far below `n⁻³`. -/
theorem lemma43_iii_cube {m : ℕ} (ι : Edge V ↪ Fin m) (s : BlockState V) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (v w : V) (hvw : v ≠ w) (l : ℕ) {q : ℝ}
    (hq : (n : ℝ) * p ^ 2 ≤ q)
    (hbound : q ^ l / (Nat.factorial l : ℝ) ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹) :
    bernoulliPr p (Finset.univ.filter (fun σ =>
        l ≤ (nbrs (sampleEdges ι s σ) v ∩ nbrs (sampleEdges ι s σ) w).card))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹ := by
  classical
  refine le_trans (lemma43_iii ι s hp₀ hp₁ v w hvw l) ?_
  have hfac : (0 : ℝ) < (Nat.factorial l : ℝ) := by
    exact_mod_cast Nat.factorial_pos l
  have hnp : (0 : ℝ) ≤ (n : ℝ) * p ^ 2 := by positivity
  calc (Nat.choose n l : ℝ) * p ^ (2 * l)
      ≤ ((n : ℝ) ^ l / (Nat.factorial l : ℝ)) * p ^ (2 * l) :=
        mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div l n) (by positivity)
    _ = ((n : ℝ) * p ^ 2) ^ l / (Nat.factorial l : ℝ) := by
        rw [pow_mul, mul_pow]; ring
    _ ≤ q ^ l / (Nat.factorial l : ℝ) := by
        exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hnp hq l) hfac.le
    _ ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹ := hbound

/-- Subadditivity over three events. -/
lemma bernoulliPr_union3_le {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (A B C : Finset (Fin m → Bool)) :
    bernoulliPr p (A ∪ B ∪ C)
      ≤ bernoulliPr p A + bernoulliPr p B + bernoulliPr p C := by
  have h1 := bernoulliPr_union_le hp₀ hp₁ (A ∪ B) C
  have h2 := bernoulliPr_union_le hp₀ hp₁ A B
  linarith

/-- The block state obtained by taking the sampled edge set as the new block. -/
noncomputable def blockStepSample {m : ℕ} (ι : Edge V ↪ Fin m) (s : BlockState V)
    (σ : Fin m → Bool) : BlockState V :=
  blockStep s (sampleEdges ι s σ) (sampleEdges_subset ι s σ)

open scoped Classical in
/-- **Property 3 survives one block step with probability at least `1 − 3/n`.**

The three hypotheses are exactly Kim's Lemma 4.3(ii) (in both orientations) and
Lemma 4.3(iii); a union bound over the at most `n²` ordered pairs of distinct
vertices turns the per-pair failure probability `n⁻³` into `3/n`. -/
theorem property3_prob {m : ℕ} (ι : Edge V ↪ Fin m) (k : ℕ) (s : BlockState V) {p : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (h3 : Property3 s k) (hn : 0 < n)
    (hA : ∀ v w : V, v ≠ w → bernoulliPr p (Finset.univ.filter (fun σ =>
        Real.log n < ((nbrs (sampleEdges ι s σ) v ∩ nbrs s.E w).card : ℝ)))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹)
    (hB : ∀ v w : V, v ≠ w → bernoulliPr p (Finset.univ.filter (fun σ =>
        Real.log n < ((nbrs s.E v ∩ nbrs (sampleEdges ι s σ) w).card : ℝ)))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹)
    (hC : ∀ v w : V, v ≠ w → bernoulliPr p (Finset.univ.filter (fun σ =>
        Real.log n < ((commonNbrs (sampleEdges ι s σ) v w).card : ℝ)))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹) :
    bernoulliPr p (Finset.univ.filter (fun σ =>
        ¬ Property3 (blockStepSample ι s σ) (k + 1))) ≤ 3 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcube0 : (0 : ℝ) ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹ := by positivity
  refine le_trans (bernoulliPr_mono hp₀ hp₁ (?_ :
      (Finset.univ.filter (fun σ => ¬ Property3 (blockStepSample ι s σ) (k + 1)))
      ⊆ (Finset.univ.filter (fun q : V × V => q.1 ≠ q.2)).biUnion (fun q =>
        (Finset.univ.filter (fun σ =>
          Real.log n < ((nbrs (sampleEdges ι s σ) q.1 ∩ nbrs s.E q.2).card : ℝ)))
        ∪ (Finset.univ.filter (fun σ =>
          Real.log n < ((nbrs s.E q.1 ∩ nbrs (sampleEdges ι s σ) q.2).card : ℝ)))
        ∪ (Finset.univ.filter (fun σ =>
          Real.log n
            < ((commonNbrs (sampleEdges ι s σ) q.1 q.2).card : ℝ)))))) ?_
  · intro σ hσ
    obtain ⟨-, hfail⟩ := Finset.mem_filter.mp hσ
    by_contra hcon
    refine hfail (property3_step k s (sampleEdges ι s σ) (sampleEdges_subset ι s σ)
      h3 ?_ ?_ ?_)
    all_goals
      intro v w hvw
      by_contra hlt
      push_neg at hlt
      refine hcon (Finset.mem_biUnion.mpr ⟨(v, w),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvw⟩, ?_⟩)
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
  refine le_trans (bernoulliPr_biUnion_le hp₀ hp₁ _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : V × V =>
      3 * ((n : ℝ) ^ (3 : ℕ))⁻¹) fun q hq => ?_) ?_
  · show (_ : ℝ) ≤ 3 * ((n : ℝ) ^ (3 : ℕ))⁻¹
    have hne := (Finset.mem_filter.mp hq).2
    exact le_trans (bernoulliPr_union3_le hp₀ hp₁ _ _ _)
      (le_trans (add_le_add (add_le_add (hA q.1 q.2 hne) (hB q.1 q.2 hne))
        (hC q.1 q.2 hne)) (le_of_eq (by ring)))
  · rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (((Finset.univ.filter
        (fun q : V × V => q.1 ≠ q.2)).card : ℕ) : ℝ) ≤ (n : ℝ) * n := by
      have h := Finset.card_le_univ
        (Finset.univ.filter (fun q : V × V => q.1 ≠ q.2))
      rw [Fintype.card_prod] at h
      calc (((Finset.univ.filter (fun q : V × V => q.1 ≠ q.2)).card : ℕ) : ℝ)
          ≤ ((Fintype.card V * Fintype.card V : ℕ) : ℝ) := by exact_mod_cast h
        _ = (n : ℝ) * n := by push_cast; ring
    refine le_trans (mul_le_mul_of_nonneg_right hcard (by positivity)) ?_
    rw [show (n : ℝ) * n * (3 * ((n : ℝ) ^ (3 : ℕ))⁻¹) = 3 / n by field_simp]

open scoped Classical in
/-- **Property 1 survives one block step with probability at least `1 − 1/n²`.**

The hypothesis is Kim's Lemma 4.3(i): for each vertex the sampled degree
exceeds `bₖθ√n + n^{1/4}log n` with probability at most `n⁻³`. A union bound
over the `n` vertices gives `1/n²`. -/
theorem property1_prob {m : ℕ} (ι : Edge V ↪ Fin m) (k : ℕ) (s : BlockState V) {p : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (h1 : Property1 s k) (hn : 0 < n)
    (hdeg : ∀ v : V, bernoulliPr p (Finset.univ.filter (fun σ =>
        bSeq n k * theta n * Real.sqrt n
            + (n : ℝ) ^ (1 / 4 : ℝ) * Real.log n
          < (degEdges (sampleEdges ι s σ) v : ℝ)))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹) :
    bernoulliPr p (Finset.univ.filter (fun σ =>
        ¬ Property1 (blockStepSample ι s σ) (k + 1))) ≤ ((n : ℝ) ^ (2 : ℕ))⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine le_trans (bernoulliPr_mono hp₀ hp₁ (?_ :
      (Finset.univ.filter (fun σ => ¬ Property1 (blockStepSample ι s σ) (k + 1)))
      ⊆ (Finset.univ : Finset V).biUnion (fun v =>
        Finset.univ.filter (fun σ =>
          bSeq n k * theta n * Real.sqrt n
              + (n : ℝ) ^ (1 / 4 : ℝ) * Real.log n
            < (degEdges (sampleEdges ι s σ) v : ℝ))))) ?_
  · intro σ hσ
    obtain ⟨-, hfail⟩ := Finset.mem_filter.mp hσ
    by_contra hcon
    refine hfail (property1_step k s (sampleEdges ι s σ) (sampleEdges_subset ι s σ)
      h1 fun v => ?_)
    by_contra hlt
    push_neg at hlt
    exact hcon (Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩⟩)
  refine le_trans (bernoulliPr_biUnion_le hp₀ hp₁ _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : V => ((n : ℝ) ^ (3 : ℕ))⁻¹)
    fun v _ => hdeg v) ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show ((Fintype.card V : ℕ) : ℝ) = (n : ℝ) from rfl]
  rw [show (n : ℝ) * ((n : ℝ) ^ (3 : ℕ))⁻¹ = ((n : ℝ) ^ (2 : ℕ))⁻¹ by
    field_simp]


/-- **`|Γ(A,B)| ≤ |A|·|B|` for disjoint `A, B`.** Each such edge has exactly
one endpoint in `A` and one in `B`, so it is determined by that pair. This is
the `b₀ = 1` case of Property 6, and the counting §4.7 rests on. -/
lemma card_gammaBetween_le (Γ : Finset (Edge V)) {A B : Finset V}
    (hAB : Disjoint A B) :
    (gammaBetween Γ A B).card ≤ A.card * B.card := by
  classical
  rcases Finset.eq_empty_or_nonempty A with hA | ⟨a₀, ha₀⟩
  · have hemp : gammaBetween Γ A B = ∅ := by
      ext e
      simp only [Finset.notMem_empty, iff_false]
      intro he
      obtain ⟨-, v, hv, -⟩ := Finset.mem_filter.mp he
      rw [hA] at hv
      exact absurd hv (Finset.notMem_empty v)
    rw [hemp]; simp
  rcases Finset.eq_empty_or_nonempty B with hB | ⟨b₀, hb₀⟩
  · have hemp : gammaBetween Γ A B = ∅ := by
      ext e
      simp only [Finset.notMem_empty, iff_false]
      intro he
      obtain ⟨-, -, -, w, hw, -⟩ := Finset.mem_filter.mp he
      rw [hB] at hw
      exact absurd hw (Finset.notMem_empty w)
    rw [hemp]; simp
  set P : Edge V → Prop :=
    fun e => ∃ v ∈ A, ∃ w ∈ B, v ≠ w ∧ v ∈ e.val ∧ w ∈ e.val with hP
  set f : Edge V → V × V := fun e =>
    if h : P e then (h.choose, (h.choose_spec.2).choose) else (a₀, b₀) with hf
  have hmaps : ∀ e ∈ gammaBetween Γ A B, f e ∈ A ×ˢ B := by
    intro e he
    obtain ⟨-, hPe⟩ := Finset.mem_filter.mp he
    have hPe' : P e := hPe
    rw [hf]
    simp only [dif_pos hPe']
    refine Finset.mem_product.mpr ⟨hPe'.choose_spec.1, ?_⟩
    exact (hPe'.choose_spec.2).choose_spec.1
  have hinj : Set.InjOn f (gammaBetween Γ A B : Set (Edge V)) := by
    intro e he e' he' hEq
    obtain ⟨-, hPe⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp he)
    obtain ⟨-, hPe'⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp he')
    have hPe1 : P e := hPe
    have hPe2 : P e' := hPe'
    rw [hf] at hEq
    simp only [dif_pos hPe1, dif_pos hPe2, Prod.mk.injEq] at hEq
    obtain ⟨h1, h2⟩ := hEq
    -- the chosen pair lies in e and in e'
    have hve : hPe1.choose ∈ e.val := (hPe1.choose_spec.2).choose_spec.2.2.1
    have hwe : (hPe1.choose_spec.2).choose ∈ e.val :=
      (hPe1.choose_spec.2).choose_spec.2.2.2
    have hve' : hPe2.choose ∈ e'.val := (hPe2.choose_spec.2).choose_spec.2.2.1
    have hwe' : (hPe2.choose_spec.2).choose ∈ e'.val :=
      (hPe2.choose_spec.2).choose_spec.2.2.2
    have hne : hPe1.choose ≠ (hPe1.choose_spec.2).choose :=
      (hPe1.choose_spec.2).choose_spec.2.1
    have hne' : hPe2.choose ≠ (hPe2.choose_spec.2).choose :=
      (hPe2.choose_spec.2).choose_spec.2.1
    apply Subtype.ext
    have hpair : ∀ a b c d : V, a = c → b = d → (s(a, b) : Sym2 V) = s(c, d) := by
      intro a b c d hac hbd; rw [hac, hbd]
    rw [edge_eq_of_two_mem hve hwe hne, edge_eq_of_two_mem hve' hwe' hne']
    exact hpair _ _ _ _ h1 h2
  calc (gammaBetween Γ A B).card ≤ (A ×ˢ B).card :=
        Finset.card_le_card_of_injOn f hmaps hinj
    _ = A.card * B.card := Finset.card_product A B


open scoped Classical in
/-- **`|Γ(A,B)| ≤ |A|·|B|` with no disjointness assumption.** Kim's §4.8 applies
this to `N_ℰ(w,T)` and `N_{X'}(w,T)`, which may well overlap. Each such edge is
`{v, w}` for some `v ∈ A`, `w ∈ B`, so it is hit by the obvious map from
`A ×ˢ B`. -/
lemma card_gammaBetween_le' (Γ : Finset (Edge V)) (A B : Finset V) :
    (gammaBetween Γ A B).card ≤ A.card * B.card := by
  classical
  rcases Finset.eq_empty_or_nonempty (gammaBetween Γ A B) with hemp | ⟨e₀, he₀⟩
  · rw [hemp, Finset.card_empty]; exact Nat.zero_le _
  · have hsurj : Set.SurjOn
        (fun q : V × V => if h : q.1 ≠ q.2 then mkEdge h else e₀)
        ((A ×ˢ B : Finset (V × V)) : Set (V × V))
        ((gammaBetween Γ A B : Finset (Edge V)) : Set (Edge V)) := by
      intro e he
      obtain ⟨-, v, hvA, w, hwB, hvw, hve, hwe⟩ :=
        Finset.mem_filter.mp (Finset.mem_coe.mp he)
      refine ⟨(v, w), Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hvA, hwB⟩), ?_⟩
      show (if h : v ≠ w then mkEdge h else e₀) = e
      rw [dif_pos hvw]
      exact Subtype.ext (by rw [mkEdge_val, edge_eq_of_two_mem hve hwe hvw])
    have := Finset.card_le_card_of_surjOn _ hsurj
    rwa [Finset.card_product] at this

/-- **Property 6 at stage 0**, first part: `|Γ₀(A,B)| ≤ |A||B| = b₀|A||B|`. -/
lemma property6_init_fst (A B : Finset V) (hAB : Disjoint A B) :
    ((gammaBetween (initBlockState V).Γ A B).card : ℝ)
      ≤ bSeq n 0 * A.card * B.card := by
  rw [bSeq_zero']
  have h := card_gammaBetween_le (initBlockState V).Γ hAB
  have : ((gammaBetween (initBlockState V).Γ A B).card : ℝ)
      ≤ ((A.card * B.card : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at this ⊢
  linarith

/-- `μ₀ = 1`. -/
lemma μSeq_zero' (N : ℕ) : μSeq N 0 = 1 := by
  unfold μSeq
  rw [aSeq_zero']
  simp

/-- `𝒯ᵢ` consists of `t`-element subsets, so it sits inside `powersetCard t`. -/
lemma calT_subset_powersetCard (s : BlockState V) :
    calT s ⊆ Finset.powersetCard (tParam n) (Finset.univ : Finset V) := by
  classical
  intro T hT
  have hmem : T ∈ Finset.univ.filter (fun T : Finset V => T.card = tParam n ∧
      ∀ e ∈ s.G, ¬ (∃ v ∈ T, ∃ w ∈ T, v ≠ w ∧ v ∈ e.val ∧ w ∈ e.val)) := hT
  obtain ⟨-, hcard, -⟩ := Finset.mem_filter.mp hmem
  rw [Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ T, hcard⟩

/-- `|𝒯ᵢ| ≤ (n choose t)`. -/
lemma card_calT_le (s : BlockState V) :
    (calT s).card ≤ Nat.choose (Fintype.card V) (tParam n) := by
  have h := Finset.card_le_card (calT_subset_powersetCard s)
  rwa [Finset.card_powersetCard, Finset.card_univ] at h

/-- **Property 8 at stage 0**: `|𝒯₀| ≤ (n choose t)`, since the exponential
factor is `exp 0 = 1` and `n⁰ = 1`. -/
lemma property8_init : Property8 (initBlockState V) 0 := by
  show ((calT (initBlockState V)).card : ℝ) ≤ _
  simp only [pow_zero, Finset.range_zero, Finset.sum_empty, mul_zero,
    neg_zero, Real.exp_zero, mul_one, one_mul]
  exact_mod_cast card_calT_le (initBlockState V)

/-- The (canonical) two-element vertex set of an edge. -/
noncomputable def edgeVerts (e : Edge V) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => x ∈ e.val)

lemma edgeVerts_mk {a b : V} (h : ¬ (s(a, b) : Sym2 V).IsDiag) :
    edgeVerts (⟨s(a, b), h⟩ : Edge V) = {a, b} := by
  classical
  ext x
  simp only [edgeVerts, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  exact Sym2.mem_iff

/-- **Property 7 at stage 0**: `Γ₀ = E(Kₙ)` contains all `C(t,2)` edges inside
a `t`-set `T`, and `b₀ = μ₀ = 1`. Proved by surjecting `Γ₀(T)` onto the
2-element subsets of `T` via `edgeVerts`. -/
lemma property7_init : Property7 (initBlockState V) 0 := by
  classical
  intro T hT
  rw [bSeq_zero', μSeq_zero', one_mul, one_mul]
  have hTcard : T.card = tParam n := by
    have hmem : T ∈ Finset.univ.filter (fun T : Finset V => T.card = tParam n ∧
        ∀ e ∈ (initBlockState V).G, ¬ (∃ v ∈ T, ∃ w ∈ T,
          v ≠ w ∧ v ∈ e.val ∧ w ∈ e.val)) := hT
    exact (Finset.mem_filter.mp hmem).2.1
  have hsurj : Set.SurjOn edgeVerts
      (gammaBetween (initBlockState V).Γ T T : Set (Edge V))
      (Finset.powersetCard 2 T : Set (Finset V)) := by
    intro P hP
    obtain ⟨hPT, hPcard⟩ := Finset.mem_powersetCard.mp (Finset.mem_coe.mp hP)
    obtain ⟨a, b, hab, hPeq⟩ := Finset.card_eq_two.mp hPcard
    have haT : a ∈ T := hPT (by rw [hPeq]; simp)
    have hbT : b ∈ T := hPT (by rw [hPeq]; simp)
    have hnd : ¬ (s(a, b) : Sym2 V).IsDiag := by simpa using hab
    refine ⟨(⟨s(a, b), hnd⟩ : Edge V), ?_, ?_⟩
    · refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      exact ⟨a, haT, b, hbT, hab, by simp, by simp⟩
    · rw [edgeVerts_mk hnd, hPeq]
  have hcard : (Finset.powersetCard 2 T).card
      ≤ (gammaBetween (initBlockState V).Γ T T).card :=
    Finset.card_le_card_of_surjOn edgeVerts hsurj
  rw [Finset.card_powersetCard, hTcard] at hcard
  exact_mod_cast hcard

lemma edgeVerts_card (e : Edge V) : (edgeVerts e).card = 2 := by
  classical
  obtain ⟨z, hz⟩ := e
  induction z using Sym2.ind with
  | _ a b =>
      have hab : a ≠ b := by simpa using hz
      rw [show (⟨s(a, b), hz⟩ : Edge V) = ⟨s(a, b), hz⟩ from rfl,
        edgeVerts_mk hz]
      rw [Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]

/-! ### Kim's padding (§4.1): the exact `Λ*`-degree

Kim adds, for every pair `(e_vw, v)` with `e_vw ∈ Γ`, a set of
`⌊b(a+5θ)√n⌋ − d_Λ(e_vw, v)` brand-new vertices, and the corresponding new
edges to `Γ*` and pairs to `Λ*`. Their only role is to supply extra
*independent* Bernoulli trials so that (19) holds:

`d_{Λ*}(e_vw, v) = ⌊b(a+5θ)√n⌋` for every `e_vw ∈ Γ`.

We realise this without enlarging the vertex set: the padded coordinate space
carries one Bernoulli coordinate per potential edge together with `M` dummy
slots for each (edge, endpoint) pair, of which the first `M − d_Λ(e,v)` are
used. -/

/-- The padded Bernoulli index set. -/
abbrev Coord (V : Type*) (M : ℕ) := Edge V ⊕ (Edge V × V × Fin M)

noncomputable def coordEquiv (V : Type*) [Fintype V] [DecidableEq V] (M : ℕ) :
    Coord V M ≃ Fin (Fintype.card (Coord V M)) := Fintype.equivFin _

/-- The `Λ`-partners of `e` at its endpoint `v`: the `Γ`-edges `e_uv` whose far
endpoint `u` is an `ℰ`-neighbour of the far endpoint `w` of `e`. -/
noncomputable def lambdaAt (s : BlockState V) (e : Edge V) (v : V) :
    Finset (Edge V) :=
  crossEdges s (otherEndOf v e) v

lemma card_lambdaAt (s : BlockState V) (e : Edge V) (v : V) :
    (lambdaAt s e v).card = lambdaDeg s.E s.Γ v (otherEndOf v e) :=
  card_crossEdges_eq_lambdaDeg s (otherEndOf v e) v

lemma lambdaAt_subset (s : BlockState V) (e : Edge V) (v : V) :
    lambdaAt s e v ⊆ s.Γ := crossEdges_subset s _ v

lemma mem_lambdaAt {s : BlockState V} {e : Edge V} {v : V} {f : Edge V} :
    f ∈ lambdaAt s e v ↔
      (f ∈ s.Γ ∧ v ∈ f.val) ∧ otherEndOf v f ∈ nbrs s.E (otherEndOf v e) := by
  classical
  show f ∈ Finset.filter _ (Finset.filter _ _) ↔ _
  rw [Finset.mem_filter, Finset.mem_filter]

/-- The padding slots for `(e, v)`: the first `M − d_Λ(e,v)` dummy
coordinates. -/
noncomputable def padAt (s : BlockState V) (M : ℕ) (e : Edge V) (v : V) :
    Finset (Coord V M) := by
  classical
  exact (Finset.univ.filter
    (fun i : Fin M => (i : ℕ) < M - (lambdaAt s e v).card)).image
      (fun i => Sum.inr (e, v, i))

lemma card_padAt (s : BlockState V) (M : ℕ) (e : Edge V) (v : V) :
    (padAt s M e v).card = M - (lambdaAt s e v).card := by
  classical
  set c : ℕ := M - (lambdaAt s e v).card with hc
  have hle : c ≤ M := Nat.sub_le _ _
  rw [padAt, Finset.card_image_of_injective _ (fun i j h => by simpa using h),
    ← Finset.card_image_of_injective _
      (fun (i j : Fin M) (h : (i : ℕ) = j) => Fin.ext h),
    show (Finset.univ.filter (fun i : Fin M => (i : ℕ) < c)).image Fin.val
      = Finset.range c from ?_, Finset.card_range]
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro hx; exact ⟨⟨x, lt_of_lt_of_le hx hle⟩, hx, rfl⟩

/-- Kim's `Λ*(e)`: the genuine `Λ`-partners at both endpoints of `e`, topped up
with dummy slots so the total is exactly `2M`. -/
noncomputable def lambdaStar (s : BlockState V) (M : ℕ) (e : Edge V) :
    Finset (Coord V M) := by
  classical
  exact (edgeVerts e).biUnion
    (fun v => (lambdaAt s e v).image Sum.inl ∪ padAt s M e v)

lemma mem_edgeVerts {e : Edge V} {v : V} : v ∈ edgeVerts e ↔ v ∈ e.val := by
  classical
  show v ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ v, h⟩⟩

lemma mem_padAt {s : BlockState V} {M : ℕ} {e : Edge V} {v : V}
    {x : Coord V M} (hx : x ∈ padAt s M e v) :
    ∃ i : Fin M, x = Sum.inr (e, v, i) := by
  classical
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨i, rfl⟩

/-- **Kim's `N_{Λ*}(e_vw, v) ∩ N_{Λ*}(e_vw, w) = ∅`.** The only edge meeting
both endpoints of `e` is `e` itself, and `e` is never its own `Λ`-partner
because a vertex is not one of its own `ℰ`-neighbours. -/
lemma lambdaAt_disjoint (s : BlockState V) (e : Edge V) {v w : V}
    (hv : v ∈ e.val) (hw : w ∈ e.val) (hvw : v ≠ w) :
    Disjoint (lambdaAt s e v) (lambdaAt s e w) := by
  classical
  rw [Finset.disjoint_left]
  intro f hfv hfw
  obtain ⟨⟨-, hvf⟩, hendv⟩ := mem_lambdaAt.mp hfv
  obtain ⟨⟨-, hwf⟩, -⟩ := mem_lambdaAt.mp hfw
  have hfe : f = e := Subtype.ext (by
    rw [edge_eq_of_two_mem hvf hwf hvw, edge_eq_of_two_mem hv hw hvw])
  subst hfe
  exact (mem_nbrs.mp hendv).1 rfl

/-- Each endpoint contributes exactly `M` coordinates: the genuine `Λ`-partners
plus the dummy slots that top them up. -/
lemma card_lambdaStar_part (s : BlockState V) (M : ℕ) (e : Edge V) (v : V)
    (hv : (lambdaAt s e v).card ≤ M) :
    (((lambdaAt s e v).image Sum.inl ∪ padAt s M e v)
      : Finset (Coord V M)).card = M := by
  classical
  have hdisj : Disjoint ((lambdaAt s e v).image (Sum.inl : Edge V → Coord V M))
      (padAt s M e v) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨i, hi⟩ := mem_padAt hx'
    exact absurd hi (by simp)
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ Sum.inl_injective, card_padAt]
  omega

/-- **Kim (19).** After padding, every `Γ`-edge has exactly `2M` coordinates in
its `Λ*`-neighbourhood, where `M = ⌊b(a+5θ)√n⌋`. This exactness is what makes
`Pr(e ∉ Y') = (1−p)^{2M}` an identity rather than an inequality, and hence what
makes Lemma 4.1's *upper* bound available. -/
lemma card_lambdaStar (s : BlockState V) (M : ℕ) (e : Edge V)
    (hM : ∀ v ∈ edgeVerts e, (lambdaAt s e v).card ≤ M) :
    (lambdaStar s M e).card = 2 * M := by
  classical
  have hpair : ∀ v ∈ edgeVerts e, ∀ w ∈ edgeVerts e, v ≠ w →
      Disjoint ((lambdaAt s e v).image (Sum.inl : Edge V → Coord V M)
          ∪ padAt s M e v)
        ((lambdaAt s e w).image Sum.inl ∪ padAt s M e w) := by
    intro v hv w hw hvw
    rw [Finset.disjoint_left]
    intro x hx hx'
    rcases Finset.mem_union.mp hx with hx1 | hx1 <;>
      rcases Finset.mem_union.mp hx' with hx2 | hx2
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hx1
      obtain ⟨g, hg, hgf⟩ := Finset.mem_image.mp hx2
      have : g = f := Sum.inl_injective hgf
      subst this
      exact (Finset.disjoint_left.mp (lambdaAt_disjoint s e
        (mem_edgeVerts.mp hv) (mem_edgeVerts.mp hw) hvw) hf) hg
    · obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hx1
      obtain ⟨i, hi⟩ := mem_padAt hx2
      exact absurd hi (by simp)
    · obtain ⟨i, hi⟩ := mem_padAt hx1
      obtain ⟨g, -, hg⟩ := Finset.mem_image.mp hx2
      exact absurd (hg.trans hi) (by simp)
    · obtain ⟨i, hi⟩ := mem_padAt hx1
      obtain ⟨j, hj⟩ := mem_padAt hx2
      rw [hi] at hj
      exact hvw (congrArg (fun z => z.2.1) (Sum.inr_injective hj))
  rw [lambdaStar, Finset.card_biUnion hpair,
    Finset.sum_congr rfl (fun v hv => card_lambdaStar_part s M e v (hM v hv)),
    Finset.sum_const, edgeVerts_card, smul_eq_mul]

/-- The padded sample `X*`, restricted to `Γ` (Kim's `X = X* ∩ Γ`). -/
noncomputable def sampleP (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) : Finset (Edge V) := by
  classical
  exact s.Γ.filter (fun e => σ (coordEquiv V M (Sum.inl e)) = true)

lemma sampleP_subset (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) : sampleP s M σ ⊆ s.Γ := by
  classical
  intro e he
  exact (Finset.mem_filter.mp he).1

/-- The edge coordinates sitting inside Kim's padded index space. -/
noncomputable def padEmb (V : Type*) [Fintype V] [DecidableEq V] (M : ℕ) :
    Edge V ↪ Fin (Fintype.card (Coord V M)) where
  toFun e := coordEquiv V M (Sum.inl e)
  inj' := fun a b h => Sum.inl_injective ((coordEquiv V M).injective h)

/-- The padded sample *is* the general sample taken along `padEmb`, so every
estimate of Lemma 4.3 applies verbatim in the padded model. -/
lemma sampleP_eq (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) :
    sampleP s M σ = sampleEdges (padEmb V M) s σ := by
  classical
  ext e
  simp only [sampleP, sampleEdges, Finset.mem_filter]
  rfl

/-- `(n^{1/4})² = √n`. -/
lemma quarter_sq {N : ℕ} (hN : 0 < N) :
    ((N : ℝ) ^ ((1 : ℝ) / 4)) ^ (2 : ℕ) = Real.sqrt N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 4)) 2, ← Real.rpow_mul hNpos.le,
    Real.sqrt_eq_rpow]
  norm_num

lemma quarter_pos {N : ℕ} (hN : 0 < N) : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 4) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  exact Real.rpow_pos_of_pos hNpos _

open scoped Classical in
/-- **Kim's Lemma 4.3(i) at concrete parameters.**

With `q := n^{1/4}`, tilt `t := 8/q` and deviation `λ := q log n`, the two
side conditions of `lemma43_i_cube` become `t·λ/2 = 4 log n` and a variance
term at most `32bθe^t`; Kim uses `ρ = 4n^{−1/4}`, and we double it because the
sharp Bennett form carries an extra `e^{tc}`. -/
theorem lemma43_i_numeric (s : BlockState V) (M : ℕ) (k : ℕ) (v : V)
    (hn : 0 < n) (hlogn : 1 ≤ Real.log n)
    (hmean : edgeProb n * ((degEdges s.Γ v : ℕ) : ℝ)
      ≤ bSeq n k * theta n * Real.sqrt n)
    (hsmall : 8 / ((n : ℝ) ^ ((1 : ℝ) / 4)) ≤ 1)
    (hlog2 : Real.log 2 ≤ Real.log n)
    (hvar' : 32 * (bSeq n k * theta n) * Real.exp 1 ≤ 4 * Real.log n) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          edgeProb n * ((degEdges s.Γ v : ℕ) : ℝ)
              + (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log n
            ≤ ((degEdges (sampleP s M σ) v : ℕ) : ℝ)))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹ := by
  classical
  set q : ℝ := (n : ℝ) ^ ((1 : ℝ) / 4) with hq
  have hq0 : 0 < q := quarter_pos hn
  have hqsq : q ^ (2 : ℕ) = Real.sqrt n := quarter_sq hn
  set p : ℝ := edgeProb n with hp
  have hp0 : 0 ≤ p := edgeProb_nonneg n
  have hp1 : p ≤ 1 := edgeProb_le_one' hlogn hn
  set t : ℝ := 8 / q with ht
  have ht0 : 0 ≤ t := by positivity
  have htlam : t * (q * Real.log n) / 2 = 4 * Real.log n := by
    rw [ht]; field_simp; ring
  have hd0 : (0 : ℝ) ≤ ((degEdges s.Γ v : ℕ) : ℝ) := Nat.cast_nonneg _
  have hexpt : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.mpr hsmall
  -- the variance condition
  have hvar : t ^ 2 / 2 * (p * (1 - p) * (((degEdges s.Γ v : ℕ) : ℝ)
        * Real.exp t)) ≤ t * (q * Real.log n) / 2 := by
    rw [htlam]
    have hstep : t ^ 2 / 2 * (p * (1 - p) * (((degEdges s.Γ v : ℕ) : ℝ)
          * Real.exp t))
        ≤ t ^ 2 / 2 * ((p * ((degEdges s.Γ v : ℕ) : ℝ)) * Real.exp 1) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h1 : p * (1 - p) * (((degEdges s.Γ v : ℕ) : ℝ) * Real.exp t)
          = (p * ((degEdges s.Γ v : ℕ) : ℝ)) * ((1 - p) * Real.exp t) := by ring
      rw [h1]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith [Real.exp_pos t, hexpt, hp0, hp1]
    refine hstep.trans ?_
    have hts : t ^ 2 = 64 / q ^ (2 : ℕ) := by rw [ht]; field_simp; ring
    rw [hts, hqsq]
    have hsqrt0 : (0 : ℝ) < Real.sqrt n := by
      rw [← hqsq]; positivity
    have hkey : 64 / Real.sqrt n / 2 * (p * ((degEdges s.Γ v : ℕ) : ℝ)
          * Real.exp 1)
        ≤ 64 / Real.sqrt n / 2 * ((bSeq n k * theta n * Real.sqrt n)
          * Real.exp 1) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right hmean (Real.exp_pos 1).le
    refine hkey.trans (le_of_eq ?_) |>.trans hvar'
    field_simp
    ring
  refine lemma43_i_cube (padEmb V M) hp0 hp1 s v ht0 hn ?_ ?_
  · exact hvar
  · rw [htlam]; linarith

/-- `n·p² = θ²` for `p = θ/√n`. -/
lemma n_mul_edgeProb_sq {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * edgeProb N ^ 2 = theta N ^ 2 := by
  have hNpos : (0 : ℝ) < N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hsq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt hNpos.le
  rw [edgeProb, div_pow, hsq]
  field_simp

open scoped Classical in
/-- **Kim's Lemma 4.3(iii) at concrete parameters.**

`n·p² = θ²`, so the union bound of `lemma43_iii_cube` reads `θ^{2l}/l! ≤ θ^{2l}`
with `l = ⌈log n⌉`, and `theta_sq_pow_le` puts that below `n⁻³`. -/
theorem lemma43_iii_numeric (s : BlockState V) (M : ℕ) (v w : V) (hvw : v ≠ w)
    (hn : 0 < n) (hlogn : 1 ≤ Real.log n)
    (hloglog : Real.exp 1 ≤ Real.log n) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          Real.log n
            < ((nbrs (sampleP s M σ) v ∩ nbrs (sampleP s M σ) w).card : ℝ)))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹ := by
  classical
  set p : ℝ := edgeProb n with hp
  have hp0 : 0 ≤ p := edgeProb_nonneg n
  have hp1 : p ≤ 1 := edgeProb_le_one' hlogn hn
  set l : ℕ := ⌈Real.log n⌉₊ with hl
  have hpow := theta_sq_pow_le (N := n) hn hloglog
  have hfacpos : (0 : ℝ) < (Nat.factorial l : ℝ) := by
    exact_mod_cast Nat.factorial_pos l
  have hfac1 : (1 : ℝ) ≤ (Nat.factorial l : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero l)
  have hqnn : (0 : ℝ) ≤ (theta n ^ 2) ^ l := by positivity
  have hbound : (theta n ^ 2) ^ l / (Nat.factorial l : ℝ)
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹ := by
    refine le_trans ?_ hpow
    rw [div_le_iff₀ hfacpos]
    nlinarith [hqnn, hfac1]
  have hmain := lemma43_iii_cube (padEmb V M) s hp0 hp1 v w hvw l
    (le_of_eq (n_mul_edgeProb_sq hn)) hbound
  refine le_trans (bernoulliPr_mono hp0 hp1 (?_ : _ ⊆ Finset.univ.filter
    (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
      l ≤ (nbrs (sampleEdges (padEmb V M) s σ) v
        ∩ nbrs (sampleEdges (padEmb V M) s σ) w).card))) hmain
  intro σ hσ
  obtain ⟨-, hgt⟩ := Finset.mem_filter.mp hσ
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [sampleP_eq] at hgt
  rw [hl]
  exact Nat.ceil_le.mpr hgt.le

open scoped Classical in
/-- **Kim's `E[Φ⁽¹⁾_{v,w}] ≤ p·d_ℰ(v) ≤ 1`**, the mean bound of Lemma 4.3(ii).

`p·d_ℰ(v) ≤ aθ + kθ·log n / n^{1/4}`, and both terms vanish: `a = O(√log n)`
against `θ = (log n)^{-2}`, and `kθ ≤ n^δ` against `n^{1/4}` with `δ < 1/4`. -/
lemma edgeProb_mul_crossEdges_le_one (s : BlockState V) (k : ℕ) (v w : V)
    (hn : 0 < n) (hθpos : 0 < theta n)
    (hk : k ≤ ⌊(n : ℝ) ^ kimDelta / theta n⌋₊) (h1 : Property1 s k)
    (hA : (Real.sqrt (kimDelta * Real.log n) + 1 + theta n) * theta n ≤ 1 / 2)
    (hB : (n : ℝ) ^ kimDelta * Real.log n / (n : ℝ) ^ ((1 : ℝ) / 4) ≤ 1 / 2) :
    edgeProb n * ((crossEdges s v w).card : ℝ) ≤ 1 := by
  classical
  have hnge : 1 ≤ n := hn
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  set q : ℝ := (n : ℝ) ^ ((1 : ℝ) / 4) with hq
  have hq0 : 0 < q := quarter_pos hn
  have hqsq : q ^ (2 : ℕ) = Real.sqrt n := quarter_sq hn
  have hsqrt0 : (0 : ℝ) < Real.sqrt n := by rw [← hqsq]; positivity
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  -- step 1: cross edges are at most the `ℰ`-degree
  have hstep1 : edgeProb n * ((crossEdges s v w).card : ℝ)
      ≤ edgeProb n * ((degEdges s.E v : ℕ) : ℝ) := by
    refine mul_le_mul_of_nonneg_left ?_ hp0
    exact_mod_cast card_crossEdges_le_degE s v w
  refine hstep1.trans ?_
  -- step 2: Property 1
  have hstep2 : edgeProb n * ((degEdges s.E v : ℕ) : ℝ)
      ≤ edgeProb n * (aSeq n k * Real.sqrt n + (k : ℝ) * q * Real.log n) :=
    mul_le_mul_of_nonneg_left (h1 v) hp0
  refine hstep2.trans ?_
  -- step 3: expand `p = θ/√n`
  have hexpand : edgeProb n * (aSeq n k * Real.sqrt n + (k : ℝ) * q * Real.log n)
      = aSeq n k * theta n + ((k : ℝ) * theta n) * Real.log n / q := by
    have hqn : Real.sqrt n = q * q := by rw [← hqsq]; ring
    rw [edgeProb, hqn]
    field_simp
  rw [hexpand]
  have hA' : aSeq n k * theta n ≤ 1 / 2 := by
    have ha := aSeq_le_of_k_le hnge hθpos hk
    calc aSeq n k * theta n
        ≤ (Real.sqrt (kimDelta * Real.log n) + 1 + theta n) * theta n :=
          mul_le_mul_of_nonneg_right ha hθpos.le
      _ ≤ 1 / 2 := hA
  have hB' : ((k : ℝ) * theta n) * Real.log n / q ≤ 1 / 2 := by
    have hkθ := kθ_le_rpow hθpos hk
    have hnum : ((k : ℝ) * theta n) * Real.log n
        ≤ ((n : ℝ) ^ kimDelta) * Real.log n :=
      mul_le_mul_of_nonneg_right hkθ hlog0
    calc ((k : ℝ) * theta n) * Real.log n / q
        ≤ ((n : ℝ) ^ kimDelta) * Real.log n / q := by gcongr
      _ ≤ 1 / 2 := hB
  linarith

open scoped Classical in
/-- **Kim's Lemma 4.3(ii) at concrete parameters.**

Kim takes `ρ = 5`; our Kahn bound carries the extra `e^{ρc}` factor of the
sharp Bennett form, so we take the tilt `14` instead and pay a (harmless,
since we only need it *eventually*) larger threshold on `n`. The mean
`p·|Γ_w(v)| ≤ p·d_ℰ(v) ≤ 1` is Kim's `E[Φ⁽¹⁾] ≤ θ^{1/2} ≤ 1`. -/
theorem lemma43_ii_numeric (s : BlockState V) (M : ℕ) (v w : V) (hn : 0 < n)
    (hmean : edgeProb n * ((crossEdges s v w).card : ℝ) ≤ 1)
    (hlog1 : Real.log 2 + 7 ≤ 4 * Real.log n)
    (hlog2 : 98 * Real.exp 14 + 7 ≤ 7 * Real.log n) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          Real.log n < ((nbrs s.E v ∩ nbrs (sampleP s M σ) w).card : ℝ)))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹ := by
  classical
  set p : ℝ := edgeProb n with hp
  have hp0 : 0 ≤ p := edgeProb_nonneg n
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : 1 ≤ Real.log n := by linarith
  have hp1 : p ≤ 1 := edgeProb_le_one' hlogn hn
  set A : Finset (Edge V) := crossEdges s v w with hA
  have hAΓ : A ⊆ s.Γ := crossEdges_subset s v w
  have hcard0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  -- variance condition at tilt `t = 14`, threshold `λ = log n − 1`
  have hvar : (14 : ℝ) ^ 2 / 2 * (p * (1 - p) * ((A.card : ℝ) * Real.exp 14))
      ≤ 14 * (Real.log n - 1) / 2 := by
    have hstep : p * (1 - p) * ((A.card : ℝ) * Real.exp 14)
        ≤ 1 * Real.exp 14 := by
      have h1 : p * (1 - p) * ((A.card : ℝ) * Real.exp 14)
          = (p * (A.card : ℝ)) * ((1 - p) * Real.exp 14) := by ring
      rw [h1]
      refine mul_le_mul hmean ?_
        (mul_nonneg (by linarith) (Real.exp_pos _).le) (by norm_num)
      nlinarith [Real.exp_pos (14 : ℝ)]
    nlinarith [hstep, Real.exp_pos (14 : ℝ), hlog2]
  have htail := sampleEdges_inter_tail (padEmb V M) hp0 hp1 s hAΓ
    (by norm_num : (0:ℝ) ≤ 14) hvar
  refine le_trans (bernoulliPr_mono hp0 hp1 (?_ : _ ⊆ Finset.univ.filter
    (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
      p * (A.card : ℝ) + (Real.log n - 1)
        ≤ ((A ∩ sampleEdges (padEmb V M) s σ).card : ℝ)))) ?_
  · intro σ hσ
    obtain ⟨-, hgt⟩ := Finset.mem_filter.mp hσ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hdom : ((nbrs s.E v ∩ nbrs (sampleEdges (padEmb V M) s σ) w).card : ℝ)
        ≤ ((A ∩ sampleEdges (padEmb V M) s σ).card : ℝ) := by
      exact_mod_cast card_nbrs_inter_sample_le (padEmb V M) s σ v w
    rw [sampleP_eq] at hgt
    linarith
  · refine htail.trans ?_
    rw [neg_div]
    refine two_exp_le_inv_cube hn ?_
    linarith


/-- Kim's `Y'`: the `Γ`-edges knocked out because some `Λ*`-partner was
selected. -/
noncomputable def killedY (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) : Finset (Edge V) := by
  classical
  exact s.Γ.filter
    (fun e => ∃ c ∈ lambdaStar s M e, σ (coordEquiv V M c) = true)

lemma mem_killedY {s : BlockState V} {M : ℕ}
    {σ : Fin (Fintype.card (Coord V M)) → Bool} {e : Edge V} :
    e ∈ killedY s M σ ↔
      e ∈ s.Γ ∧ ∃ c ∈ lambdaStar s M e, σ (coordEquiv V M c) = true := by
  classical
  show e ∈ Finset.filter _ _ ↔ _
  rw [Finset.mem_filter]

open scoped Classical in
/-- **Kim's `Pr(e ∉ Y') = (1−p)^{2M}`, exactly.** This is the identity that
Kim's padding (19) buys: without it one only gets an inequality in the wrong
direction, and Lemma 4.1's *upper* bound — the one Property 2 needs — would be
unavailable. -/
theorem bernoulliPr_survive (s : BlockState V) (M : ℕ) (p : ℝ) (e : Edge V)
    (hM : ∀ v ∈ edgeVerts e, (lambdaAt s e v).card ≤ M) :
    bernoulliPr p (Finset.univ.filter (fun σ =>
        ∀ c ∈ lambdaStar s M e, σ (coordEquiv V M c) = false))
      = (1 - p) ^ (2 * M) := by
  classical
  have hset : (Finset.univ.filter
      (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ∀ c ∈ lambdaStar s M e, σ (coordEquiv V M c) = false))
      = Finset.univ.filter (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ∀ j ∈ (lambdaStar s M e).image (coordEquiv V M), σ j = false) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      forall_exists_index, and_imp]
    exact ⟨fun h j c hc hjc => hjc ▸ h c hc, fun h c hc => h _ c hc rfl⟩
  rw [hset, bernoulliPr_all_false,
    Finset.card_image_of_injective _ (coordEquiv V M).injective,
    card_lambdaStar s M e hM]

open scoped Classical in
/-- **Kim's Lemma 4.1, in the padded model.** With `2M·p = 2bθ(a+5θ)` the exact
survival probability satisfies Kim's two-sided estimate
`1 − 2abθ − 10bθ² ≤ Pr(e ∉ Y') ≤ 1 − 2abθ − 9bθ²`. -/
theorem lemma41_padded (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (e : Edge V)
    (hM : ∀ v ∈ edgeVerts e, (lambdaAt s e v).card ≤ M)
    {N i : ℕ} (hθsmall : theta N ≤ 1 / 100) {err : ℝ} (herr : 0 ≤ err)
    (hMp_hi : ((2 * M : ℕ) : ℝ) * p
      ≤ 2 * bSeq N i * theta N * (aSeq N i + 5 * theta N))
    (hMp_lo : 2 * bSeq N i * theta N * (aSeq N i + 5 * theta N) - err
      ≤ ((2 * M : ℕ) : ℝ) * p) :
    1 - 2 * aSeq N i * bSeq N i * theta N - 10 * bSeq N i * theta N ^ 2
        ≤ bernoulliPr p (Finset.univ.filter (fun σ =>
            ∀ c ∈ lambdaStar s M e, σ (coordEquiv V M c) = false))
      ∧ bernoulliPr p (Finset.univ.filter (fun σ =>
            ∀ c ∈ lambdaStar s M e, σ (coordEquiv V M c) = false))
        ≤ 1 - 2 * aSeq N i * bSeq N i * theta N
          - 9 * bSeq N i * theta N ^ 2 + err := by
  rw [bernoulliPr_survive s M p e hM]
  exact lemma41_bounds i hθsmall hp0 hp1 (2 * M) herr hMp_hi hMp_lo

/-- The event that no `Λ*`-partner of *any* edge of `T` was selected. For a
singleton this is `survEvent`; Kim's Property 5 (§4.6) needs the two-element
case `T = {e_uv, e_wu}`. -/
noncomputable def survEventSet (s : BlockState V) (M : ℕ) (T : Finset (Edge V)) :
    Finset (Fin (Fintype.card (Coord V M)) → Bool) := by
  classical
  exact Finset.univ.filter (fun σ =>
    ∀ f ∈ T, ∀ c ∈ lambdaStar s M f, σ (coordEquiv V M c) = false)

open scoped Classical in
/-- **The exact joint survival probability**: `(1−p)` to the size of the union
of the `Λ*`-neighbourhoods. -/
theorem bernoulliPr_survEventSet (s : BlockState V) (M : ℕ) (p : ℝ)
    (T : Finset (Edge V)) :
    bernoulliPr p (survEventSet s M T)
      = (1 - p) ^ (T.biUnion (lambdaStar s M)).card := by
  classical
  have hset : survEventSet s M T
      = Finset.univ.filter (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ∀ j ∈ (T.biUnion (lambdaStar s M)).image (coordEquiv V M),
          σ j = false) := by
    ext σ
    simp only [survEventSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h j hj
      obtain ⟨c, hc, hcj⟩ := Finset.mem_image.mp hj
      obtain ⟨f, hfT, hcf⟩ := Finset.mem_biUnion.mp hc
      rw [← hcj]
      exact h f hfT c hcf
    · intro h f hfT c hc
      exact h _ (Finset.mem_image.mpr
        ⟨c, Finset.mem_biUnion.mpr ⟨f, hfT, hc⟩, rfl⟩)
  rw [hset, bernoulliPr_all_false,
    Finset.card_image_of_injective _ (coordEquiv V M).injective]

/-- For a pair of edges the union of the two `Λ*`-neighbourhoods has size
`4M − |intersection|`; Kim bounds the intersection by `3k log n` using
Property 3 and (26). -/
lemma card_biUnion_pair (s : BlockState V) (M : ℕ) {e f : Edge V}
    (he : (lambdaStar s M e).card = 2 * M)
    (hf : (lambdaStar s M f).card = 2 * M) :
    (({e, f} : Finset (Edge V)).biUnion (lambdaStar s M)).card
      = 4 * M - (lambdaStar s M e ∩ lambdaStar s M f).card := by
  classical
  have hbi : (({e, f} : Finset (Edge V)).biUnion (lambdaStar s M))
      = lambdaStar s M e ∪ lambdaStar s M f := by
    ext c
    rw [Finset.mem_biUnion, Finset.mem_union]
    constructor
    · rintro ⟨g, hg, hc⟩
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact Or.inl hc
      · rw [Finset.mem_singleton] at hg; subst hg; exact Or.inr hc
    · rintro (hc | hc)
      · exact ⟨e, Finset.mem_insert_self _ _, hc⟩
      · exact ⟨f, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hc⟩
  rw [hbi, Finset.card_union, he, hf]
  omega

/-- Consequently the joint survival probability is at most `(1−p)^{4M−I}`
whenever the two `Λ*`-neighbourhoods meet in at most `I` coordinates. -/
lemma card_biUnion_pair_ge (s : BlockState V) (M : ℕ) {e f : Edge V}
    (he : (lambdaStar s M e).card = 2 * M)
    (hf : (lambdaStar s M f).card = 2 * M) {I : ℕ}
    (hI : (lambdaStar s M e ∩ lambdaStar s M f).card ≤ I) :
    4 * M - I ≤ (({e, f} : Finset (Edge V)).biUnion (lambdaStar s M)).card := by
  rw [card_biUnion_pair s M he hf]
  omega

/-- The survival event for a single `Γ`-edge: none of its `Λ*`-partners was
selected. -/
noncomputable def survEvent (s : BlockState V) (M : ℕ) (e : Edge V) :
    Finset (Fin (Fintype.card (Coord V M)) → Bool) := by
  classical
  exact Finset.univ.filter
    (fun σ => ∀ c ∈ lambdaStar s M e, σ (coordEquiv V M c) = false)

open scoped Classical in
/-- **General survivor-count expectation.** `E[Φ_S] ≤ q·|S|`, where `q` is
Lemma 4.1's upper bound on the survival probability of a single `Γ`-edge.
Kim uses this with `S = N_Γ(v)` for Property 2 (§4.3) and with
`S = N_Λ(e_vw, v)` for Property 4 (§4.5). -/
theorem survivorCount_expectation (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Edge V)) {N i : ℕ}
    (hθsmall : theta N ≤ 1 / 100)
    (hM : ∀ f ∈ S, ∀ u ∈ edgeVerts f, (lambdaAt s f u).card ≤ M)
    {err : ℝ} (herr : 0 ≤ err)
    (hMp_hi : ((2 * M : ℕ) : ℝ) * p
      ≤ 2 * bSeq N i * theta N * (aSeq N i + 5 * theta N))
    (hMp_lo : 2 * bSeq N i * theta N * (aSeq N i + 5 * theta N) - err
      ≤ ((2 * M : ℕ) : ℝ) * p) :
    bernoulliExp p (fun σ =>
        ∑ f ∈ S, (if σ ∈ survEvent s M f then (1 : ℝ) else 0))
      ≤ (1 - 2 * aSeq N i * bSeq N i * theta N
          - 9 * bSeq N i * theta N ^ 2 + err) * S.card :=
  bernoulliExp_count_le S (survEvent s M)
    (fun f hf =>
      (lemma41_padded s M hp0 hp1 f (hM f hf) hθsmall herr hMp_hi hMp_lo).2)

open scoped Classical in
/-- **Kim §4.3, the expectation step for Property 2.**

`E[Φ_v] = Σ_{e ∈ N_Γ(v)} Pr(e ∉ Y') ≤ bn(b'/b − 5bθ²) ≤ b'n − b²θ²n`,

assembled from the exact survival probability (Lemma 4.1), Property 2 at stage
`i` (`d_Γ(v) ≤ bn`) and (13). -/
theorem property2_expectation (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V) {N i : ℕ} {nn : ℝ}
    (hθsmall : theta N ≤ 1 / 100)
    (hM : ∀ e ∈ edgesAt s.Γ v, ∀ u ∈ edgeVerts e, (lambdaAt s e u).card ≤ M)
    {err : ℝ} (herr : 0 ≤ err)
    (hMp_hi : ((2 * M : ℕ) : ℝ) * p
      ≤ 2 * bSeq N i * theta N * (aSeq N i + 5 * theta N))
    (hMp_lo : 2 * bSeq N i * theta N * (aSeq N i + 5 * theta N) - err
      ≤ ((2 * M : ℕ) : ℝ) * p)
    (hslack : bSeq N i * err ≤ 3 * bSeq N i ^ 2 * theta N ^ 2)
    (hnn : 0 ≤ nn) (hdeg : ((edgesAt s.Γ v).card : ℝ) ≤ bSeq N i * nn) :
    bernoulliExp p (fun σ => ∑ e ∈ edgesAt s.Γ v,
        (if σ ∈ survEvent s M e then (1 : ℝ) else 0))
      ≤ bSeq N (i + 1) * nn - bSeq N i ^ 2 * theta N ^ 2 * nn := by
  classical
  set q : ℝ := 1 - 2 * aSeq N i * bSeq N i * theta N
    - 9 * bSeq N i * theta N ^ 2 + err with hq
  have hθ := theta_nonneg N
  have hb := bSeq_pos N i
  have ha := aSeq_nonneg N i
  -- Every edge's survival probability is at most `q`, by Lemma 4.1.
  have hper : ∀ e ∈ edgesAt s.Γ v, bernoulliPr p (survEvent s M e) ≤ q := by
    intro e he
    exact (lemma41_padded s M hp0 hp1 e (hM e he) hθsmall herr hMp_hi hMp_lo).2
  -- and `q ≥ 0`, since it dominates an actual probability.
  have hq0 : 0 ≤ q := by
    rcases Finset.eq_empty_or_nonempty (edgesAt s.Γ v) with hemp | ⟨e, he⟩
    · have h := lemma41_bounds (N := N) i hθsmall hp0 hp1 (2 * M) herr
        hMp_hi hMp_lo
      have hpow : (0 : ℝ) ≤ (1 - p) ^ (2 * M) :=
        pow_nonneg (by linarith) _
      exact le_trans hpow h.2
    · exact le_trans (bernoulliPr_nonneg hp0 hp1 _) (hper e he)
  have hq1 : q ≤ 1 := by
    have h1 : 0 ≤ 2 * aSeq N i * bSeq N i * theta N :=
      mul_nonneg (mul_nonneg (by linarith) hb.le) hθ
    have h2 : 0 ≤ 9 * bSeq N i * theta N ^ 2 :=
      mul_nonneg (by linarith [hb.le]) (sq_nonneg _)
    have h3 : bSeq N i * err ≤ bSeq N i * (3 * bSeq N i * theta N ^ 2) := by
      calc bSeq N i * err ≤ 3 * bSeq N i ^ 2 * theta N ^ 2 := hslack
        _ = bSeq N i * (3 * bSeq N i * theta N ^ 2) := by ring
    have h5 : err ≤ 3 * bSeq N i * theta N ^ 2 :=
      le_of_mul_le_mul_left h3 hb
    have hb1 : bSeq N i ≤ 1 := bSeq_le_one N i
    rw [hq]
    nlinarith [h1, h2, h5, hb.le, hb1, sq_nonneg (theta N), hθ]
  have hmean := survivorCount_expectation s M hp0 hp1 (edgesAt s.Γ v) hθsmall
    (fun e _ u hu => hM e (by assumption) u hu) herr hMp_hi hMp_lo
  have hdeg0 : (0 : ℝ) ≤ ((edgesAt s.Γ v).card : ℝ) := Nat.cast_nonneg _
  have hfinal := property2_mean_le (N := N) i hnn hq0 hq1 hdeg hdeg0
    (bSeq_mul_surv_le N i herr hslack le_rfl)
  calc bernoulliExp p (fun σ => ∑ e ∈ edgesAt s.Γ v,
        (if σ ∈ survEvent s M e then (1 : ℝ) else 0))
      ≤ q * ((edgesAt s.Γ v).card : ℝ) := hmean
    _ = ((edgesAt s.Γ v).card : ℝ) * q := by ring
    _ ≤ bSeq N (i + 1) * nn - bSeq N i ^ 2 * theta N ^ 2 * nn := hfinal

open scoped Classical in
/-- Survival of `e` depends only on the coordinates in `Λ*(e)`. -/
lemma survEvent_congr (s : BlockState V) (M : ℕ) (e : Edge V)
    {τ τ' : Fin (Fintype.card (Coord V M)) → Bool}
    (h : ∀ c ∈ lambdaStar s M e,
      τ (coordEquiv V M c) = τ' (coordEquiv V M c)) :
    (τ ∈ survEvent s M e ↔ τ' ∈ survEvent s M e) := by
  classical
  simp only [survEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hτ c hc => (h c hc) ▸ hτ c hc,
    fun hτ c hc => (h c hc).symm ▸ hτ c hc⟩

open scoped Classical in
/-- **The Lipschitz structure of a survivor count.** Flipping one coordinate
can only change the survival status of those edges having it as a `Λ*`-partner,
so the count is coordinate-Lipschitz with

`c_j = #{f ∈ S : j ∈ Λ*(f)}`,

which is Kim's `c_e = |N_{Λ*}(e) ∩ N_Γ(v)|` in §4.3. -/
lemma isCoordLipschitz_survivorCount (s : BlockState V) (M : ℕ)
    (S : Finset (Edge V)) :
    IsCoordLipschitz
      (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ∑ f ∈ S, (if σ ∈ survEvent s M f then (1 : ℝ) else 0))
      (fun j => ((S.filter (fun f =>
        j ∈ (lambdaStar s M f).image (coordEquiv V M))).card : ℝ)) := by
  classical
  intro j τ τ' hagree
  set B : Finset (Edge V) := S.filter (fun f =>
    j ∈ (lambdaStar s M f).image (coordEquiv V M)) with hB
  have hzero : ∀ f ∈ S, f ∉ B →
      (if τ ∈ survEvent s M f then (1 : ℝ) else 0)
        - (if τ' ∈ survEvent s M f then (1 : ℝ) else 0) = 0 := by
    intro f hf hfB
    have hnot : j ∉ (lambdaStar s M f).image (coordEquiv V M) := by
      intro hj; exact hfB (Finset.mem_filter.mpr ⟨hf, hj⟩)
    have hcong : ∀ c ∈ lambdaStar s M f,
        τ (coordEquiv V M c) = τ' (coordEquiv V M c) := by
      intro c hc
      refine hagree _ (fun hEq => hnot ?_)
      exact Finset.mem_image.mpr ⟨c, hc, hEq⟩
    by_cases hs : τ ∈ survEvent s M f
    · rw [if_pos hs, if_pos ((survEvent_congr s M f hcong).mp hs), sub_self]
    · rw [if_neg hs, if_neg (fun hc => hs ((survEvent_congr s M f hcong).mpr hc)),
        sub_self]
  have hsplit : (∑ f ∈ S, (if τ ∈ survEvent s M f then (1 : ℝ) else 0))
      - (∑ f ∈ S, (if τ' ∈ survEvent s M f then (1 : ℝ) else 0))
      = ∑ f ∈ B, ((if τ ∈ survEvent s M f then (1 : ℝ) else 0)
          - (if τ' ∈ survEvent s M f then (1 : ℝ) else 0)) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro f hf hfB
    exact hzero f hf hfB
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : Edge V => (1 : ℝ))
    fun f _ => ?_) ?_
  · by_cases h1 : τ ∈ survEvent s M f <;> by_cases h2 : τ' ∈ survEvent s M f <;>
      simp [h1, h2]
  · rw [Finset.sum_const, nsmul_eq_mul, mul_one]

lemma nbrs_comm (E : Finset (Edge V)) (u w : V) :
    u ∈ nbrs E w ↔ w ∈ nbrs E u := by
  classical
  simp only [mem_nbrs]
  exact ⟨fun ⟨hne, e, he, hw, hu⟩ => ⟨hne.symm, e, he, hu, hw⟩,
    fun ⟨hne, e, he, hu, hw⟩ => ⟨hne.symm, e, he, hw, hu⟩⟩

lemma mem_lambdaStar {s : BlockState V} {M : ℕ} {f : Edge V}
    {c : Coord V M} :
    c ∈ lambdaStar s M f ↔ ∃ u ∈ edgeVerts f,
      c ∈ (lambdaAt s f u).image Sum.inl ∪ padAt s M f u := by
  classical
  show c ∈ Finset.biUnion _ _ ↔ _
  rw [Finset.mem_biUnion]

/-- **Symmetry of the `Λ*` relation on genuine edges.** If `g` is a
`Λ`-partner of `f` at the shared endpoint `u`, then `f` is a `Λ`-partner of `g`
at `u`. This is what lets Kim bound `c_e = |N_{Λ*}(e) ∩ N_Γ(v)|` by the
`Λ*`-degree of `e`. -/
lemma lambdaAt_symm {s : BlockState V} {f g : Edge V} {u : V}
    (hf : f ∈ s.Γ) (hu : u ∈ f.val) (h : g ∈ lambdaAt s f u) :
    f ∈ lambdaAt s g u := by
  obtain ⟨⟨hgΓ, hug⟩, hend⟩ := mem_lambdaAt.mp h
  exact mem_lambdaAt.mpr ⟨⟨hf, hu⟩, (nbrs_comm s.E _ _).mp hend⟩

open scoped Classical in
/-- **Kim's `c_e ≤ 2M`.** The edges having a fixed coordinate as a `Λ*`-partner
are themselves `Λ*`-partners of that coordinate, of which there are `2M`. -/
lemma card_filter_mem_lambdaStar_le (s : BlockState V) (M : ℕ)
    (S : Finset (Edge V)) (hS : S ⊆ s.Γ)
    (hM : ∀ g ∈ s.Γ, ∀ u ∈ edgeVerts g, (lambdaAt s g u).card ≤ M)
    (j : Fin (Fintype.card (Coord V M))) :
    (S.filter (fun f => j ∈ (lambdaStar s M f).image (coordEquiv V M))).card
      ≤ 2 * M := by
  classical
  set c : Coord V M := (coordEquiv V M).symm j with hc
  have hj : j = coordEquiv V M c := by rw [hc]; simp
  cases hcase : c with
  | inr q =>
      -- a padding coordinate belongs only to the `Λ*` of its own edge
      have hsub : (S.filter (fun f =>
          j ∈ (lambdaStar s M f).image (coordEquiv V M))) ⊆ {q.1} := by
        intro f hf
        obtain ⟨-, hjmem⟩ := Finset.mem_filter.mp hf
        obtain ⟨d, hd, hdj⟩ := Finset.mem_image.mp hjmem
        have hdc : d = c := (coordEquiv V M).injective (by rw [hdj, hj])
        obtain ⟨u, -, hu⟩ := mem_lambdaStar.mp hd
        rcases Finset.mem_union.mp hu with h1 | h1
        · obtain ⟨y, -, hy⟩ := Finset.mem_image.mp h1
          rw [hdc, hcase] at hy
          exact absurd hy (by simp)
        · obtain ⟨i, hi⟩ := mem_padAt h1
          rw [hdc, hcase] at hi
          have := Sum.inr_injective hi
          exact Finset.mem_singleton.mpr (congrArg (fun z => z.1) this).symm
      have hMpos : 1 ≤ M := by
        rcases Nat.eq_zero_or_pos M with hM0 | hMp
        · subst hM0; exact Fin.elim0 q.2.2
        · exact hMp
      calc (S.filter (fun f =>
              j ∈ (lambdaStar s M f).image (coordEquiv V M))).card
          ≤ ({q.1} : Finset (Edge V)).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton _
        _ ≤ 2 * M := by omega
  | inl g =>
      -- a genuine edge: every `f` with `g ∈ Λ*(f)` lies in `Λ*(g)`
      have hsub : (S.filter (fun f =>
          j ∈ (lambdaStar s M f).image (coordEquiv V M)))
          ⊆ (edgeVerts g).biUnion (lambdaAt s g) := by
        intro f hf
        obtain ⟨hfS, hjmem⟩ := Finset.mem_filter.mp hf
        obtain ⟨d, hd, hdj⟩ := Finset.mem_image.mp hjmem
        have hdc : d = c := (coordEquiv V M).injective (by rw [hdj, hj])
        obtain ⟨u, huf, hu⟩ := mem_lambdaStar.mp hd
        rcases Finset.mem_union.mp hu with h1 | h1
        · obtain ⟨y, hy, hyd⟩ := Finset.mem_image.mp h1
          have hyg : y = g := by
            have : (Sum.inl y : Coord V M) = Sum.inl g := by
              rw [hyd, hdc, hcase]
            exact Sum.inl_injective this
          subst hyg
          have hug : u ∈ y.val := (mem_lambdaAt.mp hy).1.2
          exact Finset.mem_biUnion.mpr ⟨u, mem_edgeVerts.mpr hug,
            lambdaAt_symm (hS hfS) (mem_edgeVerts.mp huf) hy⟩
        · obtain ⟨i, hi⟩ := mem_padAt h1
          rw [hdc, hcase] at hi
          exact absurd hi (by simp)
      -- if some edge is affected, `g` is itself a `Γ`-edge
      rcases Finset.eq_empty_or_nonempty (S.filter (fun f =>
          j ∈ (lambdaStar s M f).image (coordEquiv V M))) with hemp | ⟨f0, hf0⟩
      · rw [hemp]; simp
      · have hgΓ : g ∈ s.Γ := by
          obtain ⟨-, hjmem⟩ := Finset.mem_filter.mp hf0
          obtain ⟨d, hd, hdj⟩ := Finset.mem_image.mp hjmem
          have hdc : d = c := (coordEquiv V M).injective (by rw [hdj, hj])
          obtain ⟨u, -, hu⟩ := mem_lambdaStar.mp hd
          rcases Finset.mem_union.mp hu with h1 | h1
          · obtain ⟨y, hy, hyd⟩ := Finset.mem_image.mp h1
            have hyg : y = g := Sum.inl_injective (by rw [hyd, hdc, hcase])
            subst hyg
            exact (mem_lambdaAt.mp hy).1.1
          · obtain ⟨i, hi⟩ := mem_padAt h1
            rw [hdc, hcase] at hi
            exact absurd hi (by simp)
        refine le_trans (Finset.card_le_card hsub) ?_
        refine le_trans (Finset.card_biUnion_le) ?_
        calc ∑ u ∈ edgeVerts g, (lambdaAt s g u).card
            ≤ ∑ _u ∈ edgeVerts g, M :=
              Finset.sum_le_sum fun u hu => hM g hgΓ u hu
          _ = 2 * M := by
              rw [Finset.sum_const, edgeVerts_card, smul_eq_mul]

/-- `edgeVerts` is injective: an edge is determined by its endpoint set. -/
lemma edgeVerts_injective : Function.Injective (edgeVerts : Edge V → Finset V) := by
  classical
  intro e e' h
  obtain ⟨z, hz⟩ := e
  obtain ⟨z', hz'⟩ := e'
  induction z using Sym2.ind with
  | _ a b =>
    induction z' using Sym2.ind with
    | _ c d =>
      have hab : a ≠ b := by simpa using hz
      have hcd : c ≠ d := by simpa using hz'
      rw [edgeVerts_mk hz, edgeVerts_mk hz'] at h
      apply Subtype.ext
      show (s(a, b) : Sym2 V) = s(c, d)
      have hmem : a ∈ ({c, d} : Finset V) := by rw [← h]; simp
      have hmem2 : b ∈ ({c, d} : Finset V) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem hmem2
      rcases hmem with ha | ha <;> rcases hmem2 with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · rw [ha, hb]
      · rw [ha, hb]; exact Sym2.eq_swap
      · exact absurd (ha.trans hb.symm) hab

/-- **`|Γ(A)| ≤ C(|A|,2)`**: edges inside `A` inject into 2-subsets of `A`.
This is the `b₀ = 1` case of Property 6's second part. -/
lemma card_gammaBetween_self_le (Γ : Finset (Edge V)) (A : Finset V) :
    (gammaBetween Γ A A).card ≤ A.card.choose 2 := by
  classical
  have hmaps : ∀ e ∈ gammaBetween Γ A A, edgeVerts e ∈ Finset.powersetCard 2 A := by
    intro e he
    obtain ⟨-, v, hv, w, hw, hvw, hve, hwe⟩ := Finset.mem_filter.mp he
    rw [Finset.mem_powersetCard]
    refine ⟨?_, edgeVerts_card e⟩
    intro x hx
    have hxe : x ∈ e.val := by
      simpa [edgeVerts] using hx
    have hEq : e.val = s(v, w) := edge_eq_of_two_mem hve hwe hvw
    rw [hEq, Sym2.mem_iff] at hxe
    rcases hxe with h | h
    · rw [h]; exact hv
    · rw [h]; exact hw
  have := Finset.card_le_card_of_injOn edgeVerts hmaps
    (fun a _ b _ hab => edgeVerts_injective hab)
  rwa [Finset.card_powersetCard] at this

/-- **Property 6 at stage 0**, both parts. -/
lemma property6_init : Property6 (initBlockState V) 0 := by
  intro A B hAB _ _
  exact property6_init_fst A B hAB









/-! ### Kim's padding construction (§4.1)

Kim adjoins, for each pair `(e_vw, v)` with `e_vw ∈ Γ`, a private set
`U(e_vw, v)` of `⌊b(a+5θ)√n⌋ − d_Λ(e_vw, v)` fresh vertices, so that in the
padded structure `d_{Λ*}(e_vw, v) = M := ⌊b(a+5θ)√n⌋` *exactly* — see (19).
That exactness is what makes `Pr(e ∉ Y') = (1-p)^{2M}` uniform over `e`, which
`lemma41_bounds` then consumes.

We model the trials directly rather than constructing `V*`: a trial is either
a genuine `Γ`-edge or a dummy private to an `(edge, endpoint)` pair. -/

/-- **Double counting.** For any relation `R`,
`∑_{e ∈ S} |{f ∈ A : R e f}| = ∑_{f ∈ A} |{e ∈ S : R e f}|`. -/
lemma sum_card_filter_comm {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (A : Finset β) (R : α → β → Prop)
    [∀ e f, Decidable (R e f)] :
    ∑ e ∈ S, (A.filter (fun f => R e f)).card
      = ∑ f ∈ A, (S.filter (fun e => R e f)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- The real-valued form used in §4.5/§4.6/§4.7, where Kim bounds
`∑ cₑ²` by `(max cₑ)·∑ cₑ` and then applies Lemma 4.2. -/
lemma sum_sq_le_max_mul_sum {α : Type*} (S : Finset α) (c : α → ℝ)
    {M : ℝ} (hM : ∀ e ∈ S, c e ≤ M) (hc0 : ∀ e ∈ S, 0 ≤ c e) :
    ∑ e ∈ S, (c e) ^ 2 ≤ M * ∑ e ∈ S, c e := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun e he => ?_
  have : (c e) ^ 2 = c e * c e := sq (c e)
  rw [this]
  exact mul_le_mul_of_nonneg_right (hM e he) (hc0 e he)


open scoped Classical in
/-- **Kim's Lemma 4.2 for the padded structure**: `Σ_j c_j = 2M·|S|`. -/
lemma sum_card_filter_lambdaStar (s : BlockState V) (M : ℕ)
    (S : Finset (Edge V))
    (hM : ∀ f ∈ S, ∀ u ∈ edgeVerts f, (lambdaAt s f u).card ≤ M) :
    ∑ j : Fin (Fintype.card (Coord V M)),
        (S.filter (fun f =>
          j ∈ (lambdaStar s M f).image (coordEquiv V M))).card
      = 2 * M * S.card := by
  classical
  rw [sum_card_filter_comm (Finset.univ : Finset (Fin (Fintype.card (Coord V M))))
    S (fun j f => j ∈ (lambdaStar s M f).image (coordEquiv V M))]
  have hfil : ∀ f ∈ S, (Finset.univ.filter (fun j =>
      j ∈ (lambdaStar s M f).image (coordEquiv V M))).card = 2 * M := by
    intro f hf
    rw [show (Finset.univ.filter (fun j =>
        j ∈ (lambdaStar s M f).image (coordEquiv V M)))
      = (lambdaStar s M f).image (coordEquiv V M) from by ext j; simp,
      Finset.card_image_of_injective _ (coordEquiv V M).injective,
      card_lambdaStar s M f (hM f hf)]
  rw [Finset.sum_congr rfl hfil, Finset.sum_const, smul_eq_mul, mul_comm]

/-- If every Lipschitz constant is at most `C`, the weighted sum in Kahn's
inequality is controlled by `(∑ c_j²)·e^{tC}`. -/
lemma sum_sq_exp_le_of_bounded {m : ℕ} (c : Fin m → ℝ) {C T t : ℝ}
    (hc0 : ∀ j, 0 ≤ c j) (hcC : ∀ j, c j ≤ C) (ht : 0 ≤ t)
    (hsum : ∑ j, c j ^ 2 ≤ T) (hT : 0 ≤ T) :
    ∑ j, c j ^ 2 * Real.exp (t * c j) ≤ T * Real.exp (t * C) := by
  calc ∑ j, c j ^ 2 * Real.exp (t * c j)
      ≤ ∑ j, c j ^ 2 * Real.exp (t * C) := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hcC j) ht))
          (sq_nonneg _)
    _ = (∑ j, c j ^ 2) * Real.exp (t * C) := by rw [← Finset.sum_mul]
    _ ≤ T * Real.exp (t * C) :=
        mul_le_mul_of_nonneg_right hsum (Real.exp_nonneg _)

open scoped Classical in
/-- **General survivor-count concentration.** For any bound `C` on the
Lipschitz constants `c_j = #{f ∈ S : j ∈ Λ*(f)}`, Kahn's inequality gives

`Pr(Φ − E[Φ] ≥ λ) ≤ exp(−tλ + (t²/2)p(1−p)·C·2M|S|·e^{tC})`.

Kim uses `C = 2M` for Property 2 (§4.3) and the sharper `C = 1 + 3k log n`,
coming from Property 3 via (26), for Property 4 (§4.5). -/
theorem survivorCount_concentration (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Edge V))
    (hM : ∀ f ∈ S, ∀ u ∈ edgeVerts f, (lambdaAt s f u).card ≤ M)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ j : Fin (Fintype.card (Coord V M)),
      ((S.filter (fun f =>
        j ∈ (lambdaStar s M f).image (coordEquiv V M))).card : ℝ) ≤ C)
    {t lam : ℝ} (ht : 0 ≤ t) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          lam ≤ (∑ f ∈ S, (if σ ∈ survEvent s M f then (1 : ℝ) else 0))
            - bernoulliExp p (fun τ =>
                ∑ f ∈ S, (if τ ∈ survEvent s M f then (1 : ℝ) else 0))))
      ≤ Real.exp (-t * lam + t ^ 2 / 2 * (p * (1 - p)
          * (C * (2 * M * S.card) * Real.exp (t * C)))) := by
  classical
  refine le_trans (bernoulliPr_upper_tail hp0 hp1
    (isCoordLipschitz_survivorCount s M S) ht) ?_
  refine Real.exp_le_exp.mpr ?_
  have hpp : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  have hT : (0 : ℝ) ≤ C * (2 * M * S.card) := by positivity
  -- `Σ c_j² ≤ C · Σ c_j = C · 2M|S|` by Lemma 4.2.
  have hsumsq : ∑ j : Fin (Fintype.card (Coord V M)),
      ((S.filter (fun f =>
        j ∈ (lambdaStar s M f).image (coordEquiv V M))).card : ℝ) ^ 2
      ≤ C * (2 * M * S.card) := by
    refine le_trans (sum_sq_le_max_mul_sum Finset.univ _
      (fun j _ => hC j) (fun j _ => Nat.cast_nonneg _)) ?_
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hC0
    have hcount := sum_card_filter_lambdaStar s M S hM
    calc ∑ j : Fin (Fintype.card (Coord V M)),
          ((S.filter (fun f =>
            j ∈ (lambdaStar s M f).image (coordEquiv V M))).card : ℝ)
        = ((∑ j : Fin (Fintype.card (Coord V M)),
            (S.filter (fun f =>
              j ∈ (lambdaStar s M f).image (coordEquiv V M))).card : ℕ) : ℝ) := by
          push_cast; ring
      _ = ((2 * M * S.card : ℕ) : ℝ) := by rw [hcount]
      _ = 2 * M * S.card := by push_cast; ring
  have hinner := sum_sq_exp_le_of_bounded
    (fun j => ((S.filter (fun f =>
      j ∈ (lambdaStar s M f).image (coordEquiv V M))).card : ℝ))
    (fun j => Nat.cast_nonneg _) hC ht hsumsq hT
  have hscale := mul_le_mul_of_nonneg_left hinner hpp
  have hscale2 := mul_le_mul_of_nonneg_left hscale
    (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)
  linarith

open scoped Classical in
/-- Membership in `survEvent`. -/
lemma mem_survEvent {s : BlockState V} {M : ℕ} {f : Edge V}
    {σ : Fin (Fintype.card (Coord V M)) → Bool} :
    σ ∈ survEvent s M f ↔ ∀ c ∈ lambdaStar s M f, σ (coordEquiv V M c) = false := by
  classical
  show σ ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- Switching a coordinate off can only help an edge survive. -/
lemma survEvent_update_false (s : BlockState V) (M : ℕ) (f : Edge V)
    (j₀ : Fin (Fintype.card (Coord V M)))
    {σ : Fin (Fintype.card (Coord V M)) → Bool} (hσ : σ ∈ survEvent s M f) :
    Function.update σ j₀ false ∈ survEvent s M f := by
  classical
  refine mem_survEvent.mpr fun c hc => ?_
  by_cases hj : coordEquiv V M c = j₀
  · rw [hj]; simp
  · rw [Function.update_apply, if_neg hj]; exact mem_survEvent.mp hσ c hc

open scoped Classical in
/-- Hence the survivor count only grows under freezing, so the bad event for
the unfrozen count sits inside the bad event for the frozen one. -/
lemma survivorCount_le_freeze (s : BlockState V) (M : ℕ) (S : Finset (Edge V))
    (j₀ : Fin (Fintype.card (Coord V M)))
    (σ : Fin (Fintype.card (Coord V M)) → Bool) :
    (∑ f ∈ S, (if σ ∈ survEvent s M f then (1 : ℝ) else 0))
      ≤ ∑ f ∈ S, (if Function.update σ j₀ false ∈ survEvent s M f
          then (1 : ℝ) else 0) := by
  classical
  refine Finset.sum_le_sum fun f _ => ?_
  by_cases h : σ ∈ survEvent s M f
  · rw [if_pos h, if_pos (survEvent_update_false s M f j₀ h)]
  · rw [if_neg h]; split <;> norm_num

open scoped Classical in
/-- **Kim's §4.5 concentration, with the edge's own coordinate frozen off.**

This is `survivorCount_concentration` for the *frozen* functional
`σ ↦ Φ(σ with j₀ off)`. Because that functional ignores coordinate `j₀`, the
Lipschitz hypothesis is only needed for `j ≠ j₀` — which is exactly Kim's
`c_e ≤ 1 + 3k log n` "for all `e ∈ Γ* \ {e_vw}`". -/
theorem survivorCount_concentration_freeze (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Edge V))
    (hM : ∀ f ∈ S, ∀ u ∈ edgeVerts f, (lambdaAt s f u).card ≤ M)
    (j₀ : Fin (Fintype.card (Coord V M)))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ j : Fin (Fintype.card (Coord V M)), j ≠ j₀ →
      ((S.filter (fun f =>
        j ∈ (lambdaStar s M f).image (coordEquiv V M))).card : ℝ) ≤ C)
    {t lam : ℝ} (ht : 0 ≤ t) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          lam ≤ (∑ f ∈ S, (if Function.update σ j₀ false ∈ survEvent s M f
                then (1 : ℝ) else 0))
            - bernoulliExp p (fun τ =>
                ∑ f ∈ S, (if Function.update τ j₀ false ∈ survEvent s M f
                  then (1 : ℝ) else 0))))
      ≤ Real.exp (-t * lam + t ^ 2 / 2 * (p * (1 - p)
          * (C * (2 * M * S.card) * Real.exp (t * C)))) := by
  classical
  have hlip := (isCoordLipschitz_survivorCount s M S).freeze j₀
  refine le_trans (bernoulliPr_upper_tail hp0 hp1 hlip ht) ?_
  refine Real.exp_le_exp.mpr ?_
  set c : Fin (Fintype.card (Coord V M)) → ℝ := fun j =>
    ((S.filter (fun f =>
      j ∈ (lambdaStar s M f).image (coordEquiv V M))).card : ℝ) with hc
  set c' : Fin (Fintype.card (Coord V M)) → ℝ := Function.update c j₀ 0 with hc'
  have hcnn : ∀ j, 0 ≤ c j := by
    intro j; rw [hc]; exact Nat.cast_nonneg _
  have hc0 : ∀ j, 0 ≤ c' j := by
    intro j
    by_cases hj : j = j₀
    · subst hj; rw [hc']; simp
    · rw [hc', Function.update_apply, if_neg hj]; exact hcnn j
  have hcC : ∀ j, c' j ≤ C := by
    intro j
    by_cases hj : j = j₀
    · subst hj; rw [hc']; simpa using hC0
    · rw [hc', Function.update_apply, if_neg hj]; exact hC j hj
  have hle : ∀ j, c' j ≤ c j := by
    intro j
    by_cases hj : j = j₀
    · subst hj; rw [hc']; simpa using hcnn j
    · rw [hc', Function.update_apply, if_neg hj]
  have hsumc : ∑ j, c j = 2 * M * S.card := by
    have hcount := sum_card_filter_lambdaStar s M S hM
    calc ∑ j, c j
        = ((∑ j : Fin (Fintype.card (Coord V M)),
            (S.filter (fun f =>
              j ∈ (lambdaStar s M f).image (coordEquiv V M))).card : ℕ) : ℝ) := by
          rw [hc]; push_cast; ring
      _ = ((2 * M * S.card : ℕ) : ℝ) := by rw [hcount]
      _ = 2 * M * S.card := by push_cast; ring
  have hsumsq : ∑ j, c' j ^ 2 ≤ C * (2 * M * S.card) := by
    refine le_trans (sum_sq_le_max_mul_sum Finset.univ c'
      (fun j _ => hcC j) (fun j _ => hc0 j)) ?_
    refine mul_le_mul_of_nonneg_left ?_ hC0
    rw [← hsumc]
    exact Finset.sum_le_sum fun j _ => hle j
  have hT : (0 : ℝ) ≤ C * (2 * M * S.card) := by positivity
  have hinner := sum_sq_exp_le_of_bounded c' hc0 hcC ht hsumsq hT
  have hpp : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hinner hpp
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)
  linarith

open scoped Classical in
/-- **Kim §4.3, the concentration step for Property 2**: the `C = 2M` case. -/
theorem property2_concentration (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Edge V)) (hS : S ⊆ s.Γ)
    (hM : ∀ g ∈ s.Γ, ∀ u ∈ edgeVerts g, (lambdaAt s g u).card ≤ M)
    {t lam : ℝ} (ht : 0 ≤ t) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          lam ≤ (∑ f ∈ S, (if σ ∈ survEvent s M f then (1 : ℝ) else 0))
            - bernoulliExp p (fun τ =>
                ∑ f ∈ S, (if τ ∈ survEvent s M f then (1 : ℝ) else 0))))
      ≤ Real.exp (-t * lam + t ^ 2 / 2 * (p * (1 - p)
          * ((2 * M : ℝ) * (2 * M * S.card) * Real.exp (t * (2 * M))))) :=
  survivorCount_concentration s M hp0 hp1 S (fun f hf => hM f (hS hf)) (by positivity)
    (fun j => by exact_mod_cast card_filter_mem_lambdaStar_le s M S hS hM j) ht

/-- Removing edges from `Γ` preserves all `BlockState` invariants. -/
noncomputable def shrinkGamma (s : BlockState V) (D : Finset (Edge V)) :
    BlockState V where
  E := s.E
  Γ := s.Γ \ D
  G := s.G
  hG_subset_E := s.hG_subset_E
  hΓ_disjoint_E :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset s.hΓ_disjoint_E
  hΓ_no_triangle := fun e he => s.hΓ_no_triangle e (Finset.sdiff_subset he)
  hG_triangle_free := s.hG_triangle_free

/-- **Kim's block step with padding**, (21): `Γ' = Γ \ (X ∪ Y ∪ Z)`, where `Y`
collects the edges knocked out because a `Λ*`-partner was selected. Compared
with the unpadded `blockStep` only `Γ` shrinks; `ℰ` and `G` are unchanged, so
Properties 1 and 3 transfer verbatim. -/
noncomputable def blockStepP (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) : BlockState V :=
  shrinkGamma (blockStep s (sampleP s M σ) (sampleP_subset s M σ))
    (killedY s M σ)

@[simp] lemma blockStepP_E (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) :
    (blockStepP s M σ).E = s.E ∪ sampleP s M σ := rfl

lemma blockStepP_Γ_subset (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) :
    (blockStepP s M σ).Γ ⊆ s.Γ :=
  Finset.sdiff_subset.trans
    (blockStep_Γ_subset s (sampleP s M σ) (sampleP_subset s M σ))

open scoped Classical in
/-- **Kim's `d_{Γ'}(v) ≤ Φ_v`, from (21).** Every edge of `Γ'` at `v` is a
`Γ`-edge at `v` that escaped `Y'`. -/
lemma degEdges_blockStepP_le (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) (v : V) :
    (degEdges (blockStepP s M σ).Γ v : ℝ)
      ≤ ∑ f ∈ edgesAt s.Γ v, (if σ ∈ survEvent s M f then (1 : ℝ) else 0) := by
  classical
  have hsum : (∑ f ∈ edgesAt s.Γ v,
      (if σ ∈ survEvent s M f then (1 : ℝ) else 0))
      = (((edgesAt s.Γ v).filter (fun f => σ ∈ survEvent s M f)).card : ℝ) := by
    rw [Finset.card_filter]; push_cast; rfl
  rw [hsum]
  refine Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro f hf
  obtain ⟨hfΓ', hfv⟩ := Finset.mem_filter.mp hf
  have hfΓ : f ∈ s.Γ := blockStepP_Γ_subset s M σ hfΓ'
  have hnotY : f ∉ killedY s M σ := (Finset.mem_sdiff.mp hfΓ').2
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hfΓ, hfv⟩, ?_⟩
  simp only [survEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  intro c hc
  by_contra hcon
  refine hnotY (mem_killedY.mpr ⟨hfΓ, c, hc, ?_⟩)
  revert hcon; cases σ (coordEquiv V M c) <;> simp

/-- The `Γ`-edges at `w` whose far endpoint closes a `Γ`-triangle on `e_vw`:
Kim's index set for `Φ⁽²⁾` in §4.5. -/
noncomputable def deltaEdgesAt (s : BlockState V) (v w : V) :
    Finset (Edge V) := by
  classical
  exact (edgesAt s.Γ w).filter (fun f => otherEndOf w f ∈ commonNbrs s.Γ v w)

lemma deltaEdgesAt_subset (s : BlockState V) (v w : V) :
    deltaEdgesAt s v w ⊆ s.Γ :=
  (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

open scoped Classical in
/-- **Kim (23)**: `d_{Λ'}(e_vw, v) ≤ Φ⁽¹⁾_{v,w} + Φ⁽²⁾_{v,w}`.

A vertex counted on the left has a `Γ'`-edge to `v` and an `ℰ'`-edge to `w`.
If the latter lies in `ℰ` the vertex is caught by `Φ⁽¹⁾` (the surviving
`Λ`-partners of `e_vw` at `v`); if it lies in `X'` it is caught by `Φ⁽²⁾` (the
sampled `Δ`-edges at `w`). -/
lemma lambdaDeg_blockStepP_le (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) {v w : V} (hvw : v ≠ w) :
    ((lambdaDeg (blockStepP s M σ).E (blockStepP s M σ).Γ v w : ℕ) : ℝ)
      ≤ (∑ f ∈ lambdaAt s (mkEdge hvw) v,
            (if σ ∈ survEvent s M f then (1 : ℝ) else 0))
        + ((deltaEdgesAt s v w ∩ sampleP s M σ).card : ℝ) := by
  classical
  set X : Finset (Edge V) := sampleP s M σ with hX
  set L : Finset V := Finset.univ.filter (fun u => (u ≠ v ∧ u ≠ w) ∧
    (∃ e ∈ (blockStepP s M σ).Γ, u ∈ e.val ∧ v ∈ e.val) ∧
    (∃ f ∈ (blockStepP s M σ).E, u ∈ f.val ∧ w ∈ f.val)) with hL
  set L1 : Finset V := L.filter (fun u => ∃ f ∈ s.E, u ∈ f.val ∧ w ∈ f.val)
    with hL1
  set L2 : Finset V := L.filter (fun u => ¬ ∃ f ∈ s.E, u ∈ f.val ∧ w ∈ f.val)
    with hL2
  have hLsplit : (L.card : ℝ) = (L1.card : ℝ) + (L2.card : ℝ) := by
    rw [hL1, hL2]
    have := Finset.filter_card_add_filter_neg_card_eq_card
      (s := L) (p := fun u => ∃ f ∈ s.E, u ∈ f.val ∧ w ∈ f.val)
    push_cast [← this]; ring
  -- Φ⁽¹⁾ counts the surviving Λ-partners; every vertex of `L1` yields one.
  have hsurvsum : (∑ f ∈ lambdaAt s (mkEdge hvw) v,
      (if σ ∈ survEvent s M f then (1 : ℝ) else 0))
      = (((lambdaAt s (mkEdge hvw) v).filter
          (fun f => σ ∈ survEvent s M f)).card : ℝ) := by
    rw [Finset.card_filter]; push_cast; rfl
  have hother : otherEndOf v (mkEdge hvw) = w := by
    have hv : v ∈ (mkEdge hvw).val := by simp
    have hspec : (mkEdge hvw).val = s(v, otherEndOf v (mkEdge hvw)) :=
      edge_eq_of_otherEndOf hv
    rw [mkEdge_val] at hspec
    exact ((Sym2.congr_right).mp hspec).symm
  have h1 : (L1.card : ℝ)
      ≤ (((lambdaAt s (mkEdge hvw) v).filter
          (fun f => σ ∈ survEvent s M f)).card : ℝ) := by
    refine Nat.cast_le.mpr (Finset.card_le_card_of_surjOn (otherEndOf v) ?_)
    intro u hu
    obtain ⟨huL, hE⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hu)
    obtain ⟨-, ⟨hne, hnew⟩, ⟨g, hgΓ', hug, hvg⟩, -⟩ := Finset.mem_filter.mp huL
    obtain ⟨f, hfE, huf, hwf⟩ := hE
    have hgu : otherEndOf v g = u := by
      have hspec : g.val = s(v, otherEndOf v g) := edge_eq_of_otherEndOf hvg
      rw [hspec] at hug
      rcases Sym2.mem_iff.mp hug with h | h
      · exact absurd h hne
      · exact h.symm
    have hgΓ : g ∈ s.Γ := blockStepP_Γ_subset s M σ hgΓ'
    have hnotY : g ∉ killedY s M σ := (Finset.mem_sdiff.mp hgΓ').2
    have hmemΛ : g ∈ lambdaAt s (mkEdge hvw) v := by
      refine mem_lambdaAt.mpr ⟨⟨hgΓ, hvg⟩, ?_⟩
      rw [hgu, hother]
      exact mem_nbrs.mpr ⟨hnew, f, hfE, hwf, huf⟩
    have hsurv : σ ∈ survEvent s M g := by
      simp only [survEvent, Finset.mem_filter, Finset.mem_univ, true_and]
      intro c hc
      by_contra hcon
      refine hnotY (mem_killedY.mpr ⟨hgΓ, c, hc, ?_⟩)
      revert hcon; cases σ (coordEquiv V M c) <;> simp
    rw [← hgu]
    exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr
      (Finset.mem_filter.mpr ⟨hmemΛ, hsurv⟩))
  -- Φ⁽²⁾ counts the sampled Δ-edges; every vertex of `L2` yields one.
  have h2 : (L2.card : ℝ) ≤ ((deltaEdgesAt s v w ∩ X).card : ℝ) := by
    refine Nat.cast_le.mpr (Finset.card_le_card_of_surjOn (otherEndOf w) ?_)
    intro u hu
    obtain ⟨huL, hnE⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hu)
    obtain ⟨-, ⟨hnev, hnew⟩, ⟨g, hgΓ', hug, hvg⟩, ⟨f, hfE', huf, hwf⟩⟩ :=
      Finset.mem_filter.mp huL
    have hfX : f ∈ X := by
      rcases Finset.mem_union.mp hfE' with h | h
      · exact absurd ⟨f, h, huf, hwf⟩ hnE
      · exact h
    have hfΓ : f ∈ s.Γ := sampleP_subset s M σ hfX
    have hfu : otherEndOf w f = u := by
      have hspec : f.val = s(w, otherEndOf w f) := edge_eq_of_otherEndOf hwf
      rw [hspec] at huf
      rcases Sym2.mem_iff.mp huf with h | h
      · exact absurd h hnew
      · exact h.symm
    have hgΓ : g ∈ s.Γ := blockStepP_Γ_subset s M σ hgΓ'
    have hmemΔ : f ∈ deltaEdgesAt s v w := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hfΓ, hwf⟩, ?_⟩
      rw [hfu]
      exact mem_commonNbrs.mpr ⟨⟨hnev, hnew⟩, ⟨g, hgΓ, hvg, hug⟩,
        ⟨f, hfΓ, huf, hwf⟩⟩
    rw [← hfu]
    exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr
      (Finset.mem_inter.mpr ⟨hmemΔ, hfX⟩))
  have hLeq : (lambdaDeg (blockStepP s M σ).E (blockStepP s M σ).Γ v w : ℕ)
      = L.card := rfl
  rw [hLeq, hsurvsum, hLsplit]
  linarith

/-- The (at most two) edges joining `u` to `v` and to `w`. Kim's Property 5
indicator `1(e_uv e_wu ∩ Y' = ∅)` is the survival of this pair. -/
noncomputable def pairEdges (v w u : V) : Finset (Edge V) := by
  classical
  exact Finset.univ.filter (fun e => u ∈ e.val ∧ (v ∈ e.val ∨ w ∈ e.val))

open scoped Classical in
/-- **Kim (28)**: `d_{Δ'}(e_vw) ≤ Φ_vw`.

A vertex closing a `Γ'`-triangle on `e_vw` closes a `Γ`-triangle on it, and
both of its edges to `v` and `w` survived. -/
lemma codegEdges_blockStepP_le (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) (v w : V) :
    ((codegEdges (blockStepP s M σ).Γ v w : ℕ) : ℝ)
      ≤ ∑ u ∈ commonNbrs s.Γ v w,
          (if σ ∈ survEventSet s M (pairEdges v w u) then (1 : ℝ) else 0) := by
  classical
  have hsum : (∑ u ∈ commonNbrs s.Γ v w,
      (if σ ∈ survEventSet s M (pairEdges v w u) then (1 : ℝ) else 0))
      = (((commonNbrs s.Γ v w).filter
          (fun u => σ ∈ survEventSet s M (pairEdges v w u))).card : ℝ) := by
    rw [Finset.card_filter]; push_cast; rfl
  rw [hsum]
  refine Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro u hu
  obtain ⟨⟨hnv, hnw⟩, ⟨e, heΓ', hve, hue⟩, ⟨f, hfΓ', huf, hwf⟩⟩ :=
    mem_commonNbrs.mp hu
  have heΓ : e ∈ s.Γ := blockStepP_Γ_subset s M σ heΓ'
  have hfΓ : f ∈ s.Γ := blockStepP_Γ_subset s M σ hfΓ'
  refine Finset.mem_filter.mpr ⟨mem_commonNbrs.mpr
    ⟨⟨hnv, hnw⟩, ⟨e, heΓ, hve, hue⟩, ⟨f, hfΓ, huf, hwf⟩⟩, ?_⟩
  -- both incident edges survived, so the pair does
  have hsurv : ∀ g ∈ s.Γ, g ∉ killedY s M σ →
      ∀ c ∈ lambdaStar s M g, σ (coordEquiv V M c) = false := by
    intro g hgΓ hgY c hc
    by_contra hcon
    refine hgY (mem_killedY.mpr ⟨hgΓ, c, hc, ?_⟩)
    revert hcon; cases σ (coordEquiv V M c) <;> simp
  simp only [survEventSet, Finset.mem_filter, Finset.mem_univ, true_and]
  intro g hg c hc
  obtain ⟨-, hug, hvw'⟩ := Finset.mem_filter.mp hg
  rcases hvw' with hv | hw
  · have hge : g = e := Subtype.ext (by
      rw [edge_eq_of_two_mem hug hv hnv,
        edge_eq_of_two_mem hue hve hnv])
    subst hge
    exact hsurv g heΓ (Finset.mem_sdiff.mp heΓ').2 c hc
  · have hgf : g = f := Subtype.ext (by
      rw [edge_eq_of_two_mem hug hw hnw,
        edge_eq_of_two_mem huf hwf hnw])
    subst hgf
    exact hsurv g hfΓ (Finset.mem_sdiff.mp hfΓ').2 c hc

open scoped Classical in
/-- Joint survival of `T` depends only on the coordinates in `⋃_{f ∈ T} Λ*(f)`. -/
lemma survEventSet_congr (s : BlockState V) (M : ℕ) (T : Finset (Edge V))
    {τ τ' : Fin (Fintype.card (Coord V M)) → Bool}
    (h : ∀ c ∈ T.biUnion (lambdaStar s M),
      τ (coordEquiv V M c) = τ' (coordEquiv V M c)) :
    (τ ∈ survEventSet s M T ↔ τ' ∈ survEventSet s M T) := by
  classical
  simp only [survEventSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hτ f hf c hc
    rw [← h c (Finset.mem_biUnion.mpr ⟨f, hf, hc⟩)]; exact hτ f hf c hc
  · intro hτ f hf c hc
    rw [h c (Finset.mem_biUnion.mpr ⟨f, hf, hc⟩)]; exact hτ f hf c hc

open scoped Classical in
/-- **Lipschitz structure of a joint-survivor count.** Generalises
`isCoordLipschitz_survivorCount` from single edges to edge families; Kim's
Property 5 uses the two-element families `{e_uv, e_wu}`. -/
lemma isCoordLipschitz_survivorSetCount (s : BlockState V) (M : ℕ)
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (T : ι → Finset (Edge V)) :
    IsCoordLipschitz
      (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ∑ i ∈ S, (if σ ∈ survEventSet s M (T i) then (1 : ℝ) else 0))
      (fun j => ((S.filter (fun i =>
        j ∈ ((T i).biUnion (lambdaStar s M)).image (coordEquiv V M))).card : ℝ)) := by
  classical
  intro j τ τ' hagree
  set B : Finset ι := S.filter (fun i =>
    j ∈ ((T i).biUnion (lambdaStar s M)).image (coordEquiv V M)) with hB
  have hzero : ∀ i ∈ S, i ∉ B →
      (if τ ∈ survEventSet s M (T i) then (1 : ℝ) else 0)
        - (if τ' ∈ survEventSet s M (T i) then (1 : ℝ) else 0) = 0 := by
    intro i hi hiB
    have hnot : j ∉ ((T i).biUnion (lambdaStar s M)).image (coordEquiv V M) := by
      intro hj; exact hiB (Finset.mem_filter.mpr ⟨hi, hj⟩)
    have hcong : ∀ c ∈ (T i).biUnion (lambdaStar s M),
        τ (coordEquiv V M c) = τ' (coordEquiv V M c) := by
      intro c hc
      refine hagree _ (fun hEq => hnot (Finset.mem_image.mpr ⟨c, hc, hEq⟩))
    by_cases hs : τ ∈ survEventSet s M (T i)
    · rw [if_pos hs, if_pos ((survEventSet_congr s M (T i) hcong).mp hs), sub_self]
    · rw [if_neg hs,
        if_neg (fun hc => hs ((survEventSet_congr s M (T i) hcong).mpr hc)), sub_self]
  have hsplit : (∑ i ∈ S, (if τ ∈ survEventSet s M (T i) then (1 : ℝ) else 0))
      - (∑ i ∈ S, (if τ' ∈ survEventSet s M (T i) then (1 : ℝ) else 0))
      = ∑ i ∈ B, ((if τ ∈ survEventSet s M (T i) then (1 : ℝ) else 0)
          - (if τ' ∈ survEventSet s M (T i) then (1 : ℝ) else 0)) := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.sum_subset (Finset.filter_subset _ _)
      (fun i hi hiB => hzero i hi hiB)).symm
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : ι => (1 : ℝ))
    fun i _ => ?_) ?_
  · by_cases h1 : τ ∈ survEventSet s M (T i) <;>
      by_cases h2 : τ' ∈ survEventSet s M (T i) <;> simp [h1, h2]
  · rw [Finset.sum_const, nsmul_eq_mul, mul_one]

open scoped Classical in
/-- **General joint-survivor-count concentration.** The Lipschitz bound `C` and
the sum-of-squares bound are supplied per application; Kim's Property 5 (§4.6)
gets them from his three-case analysis of `c_e`. -/
theorem survivorSetCount_concentration (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (T : ι → Finset (Edge V)) {C Q : ℝ} (hC0 : 0 ≤ C) (hQ0 : 0 ≤ Q)
    (hC : ∀ j : Fin (Fintype.card (Coord V M)),
      ((S.filter (fun i =>
        j ∈ ((T i).biUnion (lambdaStar s M)).image
          (coordEquiv V M))).card : ℝ) ≤ C)
    (hQ : ∑ j : Fin (Fintype.card (Coord V M)),
      ((S.filter (fun i =>
        j ∈ ((T i).biUnion (lambdaStar s M)).image
          (coordEquiv V M))).card : ℝ) ^ 2 ≤ Q)
    {t lam : ℝ} (ht : 0 ≤ t) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          lam ≤ (∑ i ∈ S, (if σ ∈ survEventSet s M (T i) then (1 : ℝ) else 0))
            - bernoulliExp p (fun τ =>
                ∑ i ∈ S, (if τ ∈ survEventSet s M (T i) then (1 : ℝ) else 0))))
      ≤ Real.exp (-t * lam
          + t ^ 2 / 2 * (p * (1 - p) * (Q * Real.exp (t * C)))) := by
  classical
  refine le_trans (bernoulliPr_upper_tail hp0 hp1
    (isCoordLipschitz_survivorSetCount s M S T) ht) ?_
  refine Real.exp_le_exp.mpr ?_
  have hpp : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  have hinner := sum_sq_exp_le_of_bounded _ (fun j => Nat.cast_nonneg _) hC ht hQ hQ0
  have hscale := mul_le_mul_of_nonneg_left hinner hpp
  have hscale2 := mul_le_mul_of_nonneg_left hscale
    (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)
  linarith

open scoped Classical in
/-- **Kim (29), the expectation step for Property 5.**

`E[Φ_vw] = Σ_{u ∈ N_Δ(e_vw)} Pr(e_uv e_wu ∩ Y' = ∅) ≤ (1−p)^{4M−I}·d_Δ(e_vw)`,
where `I` bounds the overlap of the two `Λ*`-neighbourhoods (Kim gets
`I = 3k log n` from Property 3 via (26)). -/
theorem property5_expectation (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v w : V) {I : ℕ}
    (hU : ∀ u ∈ commonNbrs s.Γ v w,
      4 * M - I ≤ ((pairEdges v w u).biUnion (lambdaStar s M)).card) :
    bernoulliExp p (fun σ => ∑ u ∈ commonNbrs s.Γ v w,
        (if σ ∈ survEventSet s M (pairEdges v w u) then (1 : ℝ) else 0))
      ≤ (1 - p) ^ (4 * M - I) * (commonNbrs s.Γ v w).card :=
  bernoulliExp_count_le _ _ (fun u hu => by
    rw [bernoulliPr_survEventSet]
    exact pow_le_pow_of_le_one (by linarith) (by linarith) (hU u hu))

open scoped Classical in
/-- **Kim §4.6, the tail bound for Property 5.** Combining (29) with the
concentration inequality: exceeding the target `b'²n` forces a deviation of at
least `λ` above the mean. -/
theorem property5_tail (k : ℕ) (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v w : V) {I : ℕ} {lam : ℝ}
    (hU : ∀ u ∈ commonNbrs s.Γ v w,
      4 * M - I ≤ ((pairEdges v w u).biUnion (lambdaStar s M)).card)
    (hmean : (1 - p) ^ (4 * M - I) * ((commonNbrs s.Γ v w).card : ℝ)
      ≤ bSeq n (k + 1) ^ 2 * n - lam)
    {C Q : ℝ} (hC0 : 0 ≤ C) (hQ0 : 0 ≤ Q)
    (hC : ∀ j : Fin (Fintype.card (Coord V M)),
      (((commonNbrs s.Γ v w).filter (fun u =>
        j ∈ ((pairEdges v w u).biUnion (lambdaStar s M)).image
          (coordEquiv V M))).card : ℝ) ≤ C)
    (hQ : ∑ j : Fin (Fintype.card (Coord V M)),
      (((commonNbrs s.Γ v w).filter (fun u =>
        j ∈ ((pairEdges v w u).biUnion (lambdaStar s M)).image
          (coordEquiv V M))).card : ℝ) ^ 2 ≤ Q)
    {t : ℝ} (ht : 0 ≤ t) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          bSeq n (k + 1) ^ 2 * n < ∑ u ∈ commonNbrs s.Γ v w,
            (if σ ∈ survEventSet s M (pairEdges v w u) then (1 : ℝ) else 0)))
      ≤ Real.exp (-t * lam
          + t ^ 2 / 2 * (p * (1 - p) * (Q * Real.exp (t * C)))) := by
  classical
  refine le_trans (bernoulliPr_mono hp0 hp1 ?_)
    (survivorSetCount_concentration s M hp0 hp1 (commonNbrs s.Γ v w)
      (pairEdges v w) hC0 hQ0 hC hQ (lam := lam) ht)
  intro σ hσ
  obtain ⟨-, hgt⟩ := Finset.mem_filter.mp hσ
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have hE := property5_expectation s M hp0 hp1 v w hU
  linarith

open scoped Classical in
/-- **Property 5 survives one block step.**

Kim §4.6: `d_{Δ'}(e_vw) ≤ Φ_vw` by (28), `E[Φ_vw] ≤ b'²n − b³θ²n` by (29), and
the deviation is controlled by Kahn's inequality at `ρ = n^{−5/8}`. A union
bound over the `n²` ordered pairs turns `n⁻³` into `1/n`. -/
theorem property5_prob (k : ℕ) (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n)
    (hbad : ∀ (v w : V) (h : v ≠ w), mkEdge h ∈ s.Γ →
      bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          bSeq n (k + 1) ^ 2 * n < ∑ u ∈ commonNbrs s.Γ v w,
            (if σ ∈ survEventSet s M (pairEdges v w u) then (1 : ℝ) else 0)))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          ¬ Property5 (blockStepP s M σ) (k + 1))) ≤ 1 / n := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set P : Finset (V × V) := Finset.univ.filter
    (fun q : V × V => ∃ h : q.1 ≠ q.2, mkEdge h ∈ s.Γ) with hP
  refine le_trans (bernoulliPr_mono hp0 hp1 (?_ :
      (Finset.univ.filter (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ¬ Property5 (blockStepP s M σ) (k + 1)))
      ⊆ P.biUnion (fun q =>
        Finset.univ.filter (fun σ =>
          bSeq n (k + 1) ^ 2 * n < ∑ u ∈ commonNbrs s.Γ q.1 q.2,
            (if σ ∈ survEventSet s M (pairEdges q.1 q.2 u)
              then (1 : ℝ) else 0))))) ?_
  · intro σ hσ
    obtain ⟨-, hfail⟩ := Finset.mem_filter.mp hσ
    rw [Property5] at hfail
    push_neg at hfail
    obtain ⟨v, w, hvw, hmem, hgt⟩ := hfail
    refine Finset.mem_biUnion.mpr ⟨(v, w), ?_,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨hvw, blockStepP_Γ_subset s M σ hmem⟩⟩
    · exact lt_of_lt_of_le hgt (codegEdges_blockStepP_le s M σ v w)
  refine le_trans (bernoulliPr_biUnion_le hp0 hp1 _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : V × V =>
    ((n : ℝ) ^ (3 : ℕ))⁻¹) fun q hq => ?_) ?_
  · obtain ⟨h, hmem⟩ := (Finset.mem_filter.mp hq).2
    exact hbad q.1 q.2 h hmem
  · rw [Finset.sum_const, nsmul_eq_mul]
    have hle := Finset.card_le_univ P
    rw [Fintype.card_prod] at hle
    have hcard : (P.card : ℝ) ≤ (n : ℝ) * n := by
      calc (P.card : ℝ) ≤ ((Fintype.card V * Fintype.card V : ℕ) : ℝ) := by
            exact_mod_cast hle
        _ = (n : ℝ) * n := by push_cast; ring
    have hinv : (0 : ℝ) ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹ := by positivity
    calc (P.card : ℝ) * ((n : ℝ) ^ (3 : ℕ))⁻¹
        ≤ ((n : ℝ) * n) * ((n : ℝ) ^ (3 : ℕ))⁻¹ :=
          mul_le_mul_of_nonneg_right hcard hinv
      _ = 1 / n := by field_simp

/-! ### Property 6 (Kim §4.7): truncated survival

To keep the Lipschitz constants small Kim replaces `Y'` by the smaller set
`Y⁽¹⁾(A,B)`, in which only *low* pairs `(e,v)` — those whose `Λ*`-neighbourhood
meets `Γ(A,B)` in fewer than `4((k+1)log n)^{1/2}|A ∪ B|^{1/2}` edges — are
allowed to kill. Since `Y⁽¹⁾(A,B) ⊆ Y'`, the count `Φ_{A,B}` still dominates
`|Γ'(A,B)|`, which is (32). -/

/-- Kim's `L⁽¹⁾(A,B)` (30), as a predicate on a pair `(g, v)`. -/
noncomputable def IsLowPair (s : BlockState V) (A B : Finset V) (thr : ℝ)
    (g : Edge V) (v : V) : Prop :=
  (((lambdaAt s g v ∩ gammaBetween s.Γ A B).card : ℕ) : ℝ) < thr

noncomputable instance (s : BlockState V) (A B : Finset V) (thr : ℝ)
    (g : Edge V) (v : V) : Decidable (IsLowPair s A B thr g v) := by
  unfold IsLowPair; infer_instance

/-- The coordinates able to kill `e` through a *low* pair. Padding coordinates
always qualify: by (19) they have `Λ*`-degree `1`. -/
noncomputable def lowKillers (s : BlockState V) (M : ℕ) (A B : Finset V)
    (thr : ℝ) (e : Edge V) : Finset (Coord V M) := by
  classical
  exact (edgeVerts e).biUnion (fun v =>
    (((lambdaAt s e v).filter (fun g => IsLowPair s A B thr g v)).image Sum.inl)
    ∪ padAt s M e v)

lemma lowKillers_subset (s : BlockState V) (M : ℕ) (A B : Finset V) (thr : ℝ)
    (e : Edge V) : lowKillers s M A B thr e ⊆ lambdaStar s M e := by
  classical
  intro c hc
  obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
  refine mem_lambdaStar.mpr ⟨v, hv, ?_⟩
  rcases Finset.mem_union.mp hcv with h | h
  · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨g, (Finset.mem_filter.mp hg).1, rfl⟩)
  · exact Finset.mem_union_right _ h

/-- The truncated survival event: no *low* killer of `e` was selected. -/
noncomputable def survEventLow (s : BlockState V) (M : ℕ) (A B : Finset V)
    (thr : ℝ) (e : Edge V) :
    Finset (Fin (Fintype.card (Coord V M)) → Bool) := by
  classical
  exact Finset.univ.filter (fun σ =>
    ∀ c ∈ lowKillers s M A B thr e, σ (coordEquiv V M c) = false)

open scoped Classical in
/-- The truncated survival probability is exactly `(1−p)^{|lowKillers|}`. -/
theorem bernoulliPr_survEventLow (s : BlockState V) (M : ℕ) (A B : Finset V)
    (thr : ℝ) (p : ℝ) (e : Edge V) :
    bernoulliPr p (survEventLow s M A B thr e)
      = (1 - p) ^ (lowKillers s M A B thr e).card := by
  classical
  have hset : survEventLow s M A B thr e
      = Finset.univ.filter (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ∀ j ∈ (lowKillers s M A B thr e).image (coordEquiv V M),
          σ j = false) := by
    ext σ
    simp only [survEventLow, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h j hj
      obtain ⟨c, hc, hcj⟩ := Finset.mem_image.mp hj
      rw [← hcj]; exact h c hc
    · intro h c hc
      exact h _ (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  rw [hset, bernoulliPr_all_false,
    Finset.card_image_of_injective _ (coordEquiv V M).injective]

open scoped Classical in
/-- **Kim (32)**: `|Γ'(A,B)| ≤ Φ_{A,B}`. Surviving the full `Y'` implies
surviving the truncated `Y⁽¹⁾(A,B)`, because `lowKillers ⊆ Λ*`. -/
lemma card_gammaBetween_blockStepP_le (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) (A B : Finset V) (thr : ℝ) :
    ((gammaBetween (blockStepP s M σ).Γ A B).card : ℝ)
      ≤ ∑ e ∈ gammaBetween s.Γ A B,
          (if σ ∈ survEventLow s M A B thr e then (1 : ℝ) else 0) := by
  classical
  have hsum : (∑ e ∈ gammaBetween s.Γ A B,
      (if σ ∈ survEventLow s M A B thr e then (1 : ℝ) else 0))
      = (((gammaBetween s.Γ A B).filter
          (fun e => σ ∈ survEventLow s M A B thr e)).card : ℝ) := by
    rw [Finset.card_filter]; push_cast; rfl
  rw [hsum]
  refine Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro e he
  obtain ⟨heΓ', hAB⟩ := Finset.mem_filter.mp he
  have heΓ : e ∈ s.Γ := blockStepP_Γ_subset s M σ heΓ'
  have hnotY : e ∉ killedY s M σ := (Finset.mem_sdiff.mp heΓ').2
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heΓ, hAB⟩, ?_⟩
  simp only [survEventLow, Finset.mem_filter, Finset.mem_univ, true_and]
  intro c hc
  by_contra hcon
  refine hnotY (mem_killedY.mpr ⟨heΓ, c, lowKillers_subset s M A B thr e hc, ?_⟩)
  revert hcon; cases σ (coordEquiv V M c) <;> simp

lemma lambdaAt_subset_edgesAt (s : BlockState V) (g : Edge V) (v : V) :
    lambdaAt s g v ⊆ edgesAt s.Γ v := by
  classical
  intro f hf
  obtain ⟨⟨h1, h2⟩, -⟩ := mem_lambdaAt.mp hf
  exact Finset.mem_filter.mpr ⟨h1, h2⟩

open scoped Classical in
/-- **Kim (26), in the form §4.7 uses it**:
`|N_Λ(g,v) ∩ Γ(A,B)| ≤ |N_ℰ(u) ∩ (A ∪ B)|`, where `u` is the far endpoint of
`g` from `v`. Each `Λ`-partner of `g` at `v` is an edge of `Γ(A,B)` through
`v`, so its far endpoint lies in `A ∪ B` and is an `ℰ`-neighbour of `u`. -/
lemma card_lambdaAt_inter_gammaBetween_le (s : BlockState V) (A B : Finset V)
    (g : Edge V) (v : V) :
    (lambdaAt s g v ∩ gammaBetween s.Γ A B).card
      ≤ (nbrs s.E (otherEndOf v g) ∩ (A ∪ B)).card := by
  classical
  refine Finset.card_le_card_of_injOn (otherEndOf v) ?_ ?_
  · intro f hf
    obtain ⟨hfΛ, hfAB⟩ := Finset.mem_inter.mp hf
    obtain ⟨⟨hfΓ, hvf⟩, hend⟩ := mem_lambdaAt.mp hfΛ
    refine Finset.mem_inter.mpr ⟨hend, ?_⟩
    obtain ⟨-, x, hxA, y, hyB, hxy, hxf, hyf⟩ := Finset.mem_filter.mp hfAB
    -- `f = {x, y}` with `x ∈ A`, `y ∈ B`, and `v` is one of them
    have hfxy : f.val = s(x, y) := edge_eq_of_two_mem hxf hyf hxy
    have hvxy : v = x ∨ v = y := by
      have := hvf; rw [hfxy] at this; exact Sym2.mem_iff.mp this
    have hspec : f.val = s(v, otherEndOf v f) := edge_eq_of_otherEndOf hvf
    have hmem : otherEndOf v f ∈ f.val := by rw [hspec]; simp
    rw [hfxy, Sym2.mem_iff] at hmem
    rcases hmem with h | h
    · rw [h]; exact Finset.mem_union_left _ hxA
    · rw [h]; exact Finset.mem_union_right _ hyB
  · intro f hf f' hf' hEq
    refine otherEndOf_injOn s.Γ v ?_ ?_ hEq
    · exact Finset.mem_coe.mpr (lambdaAt_subset_edgesAt s g v
        (Finset.mem_inter.mp (Finset.mem_coe.mp hf)).1)
    · exact Finset.mem_coe.mpr (lambdaAt_subset_edgesAt s g v
        (Finset.mem_inter.mp (Finset.mem_coe.mp hf')).1)

open scoped Classical in
/-- **Kim (34)/(35)**: at most `√|A∪B|/(βγ)` of the `Λ`-partners of `e` at `v`
fail to be low.

Not being low forces `|N_ℰ(u) ∩ (A∪B)| ≥ thr ≥ 2βγ√|A∪B|` for the far endpoint
`u`, while Property 3 makes any two such neighbourhoods meet in at most `β²`
vertices. Lemma 3.5 (the almost-disjoint covering lemma) then caps the number
of such `u`. -/
theorem card_notLow_le (s : BlockState V) (A B : Finset V)
    (e : Edge V) (v : V) {β γ thr : ℝ}
    (hβ1 : 1 ≤ β) (hγ1 : 1 ≤ γ)
    (hβB : β ≤ Real.sqrt ((A ∪ B).card) / 2) (hABpos : 0 < (A ∪ B).card)
    (hthr : 2 * β * γ * Real.sqrt ((A ∪ B).card) ≤ thr)
    (h3 : ∀ u u' : V, u ≠ u' → ((commonNbrs s.E u u').card : ℝ) ≤ β ^ 2) :
    ((((lambdaAt s e v).filter
        (fun g => ¬ IsLowPair s A B thr g v)).card : ℕ) : ℝ)
      ≤ Real.sqrt ((A ∪ B).card) / (β * γ) := by
  classical
  set eq : V ≃ Fin (Fintype.card V) := Fintype.equivFin V with heq
  set S : Finset (Fin (Fintype.card V)) :=
    (((lambdaAt s e v).filter
      (fun g => ¬ IsLowPair s A B thr g v)).image (otherEndOf v)).image eq with hS
  have hcardS : S.card
      = ((lambdaAt s e v).filter (fun g => ¬ IsLowPair s A B thr g v)).card := by
    rw [hS, Finset.card_image_of_injective _ eq.injective,
      Finset.card_image_of_injOn]
    intro f hf f' hf' hEq
    refine otherEndOf_injOn s.Γ v ?_ ?_ hEq
    · exact Finset.mem_coe.mpr (lambdaAt_subset_edgesAt s e v
        (Finset.mem_filter.mp (Finset.mem_coe.mp hf)).1)
    · exact Finset.mem_coe.mpr (lambdaAt_subset_edgesAt s e v
        (Finset.mem_filter.mp (Finset.mem_coe.mp hf')).1)
  have hmain := almost_disjoint_card_le (A ∪ B) S
    (fun i => nbrs s.E (eq.symm i) ∩ (A ∪ B))
    (fun i _ => Finset.inter_subset_right) hβ1 hγ1 hβB hABpos ?_ ?_
  · rw [← hcardS]; exact hmain
  · -- every non-low partner has a large ℰ-neighbourhood inside `A ∪ B`
    intro i hi
    show 2 * β * γ * Real.sqrt ((A ∪ B).card)
      ≤ ((nbrs s.E (eq.symm i) ∩ (A ∪ B)).card : ℝ)
    obtain ⟨u, hu, hui⟩ := Finset.mem_image.mp (hS ▸ hi)
    obtain ⟨g, hg, hgu⟩ := Finset.mem_image.mp hu
    obtain ⟨hgΛ, hnlow⟩ := Finset.mem_filter.mp hg
    have hui' : eq.symm i = u := by rw [← hui]; simp
    rw [hui', ← hgu]
    have hnl : thr ≤ ((lambdaAt s g v ∩ gammaBetween s.Γ A B).card : ℝ) := by
      simpa [IsLowPair] using hnlow
    refine le_trans (le_trans hthr hnl) ?_
    exact_mod_cast card_lambdaAt_inter_gammaBetween_le s A B g v
  · -- Property 3 bounds the pairwise overlaps
    intro i _ j _ hij
    show (((nbrs s.E (eq.symm i) ∩ (A ∪ B))
      ∩ (nbrs s.E (eq.symm j) ∩ (A ∪ B))).card : ℝ) ≤ β ^ 2
    have hne : eq.symm i ≠ eq.symm j := fun h => hij (eq.symm.injective h)
    refine le_trans (le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_))
      (h3 _ _ hne)) le_rfl
    rw [commonNbrs_eq_inter]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx1).1,
      (Finset.mem_inter.mp hx2).1⟩

open scoped Classical in
/-- Everything in `Λ*(e)` that is *not* a low killer is a genuine, non-low
`Λ`-partner at one of the two endpoints. -/
lemma lambdaStar_sdiff_lowKillers_subset (s : BlockState V) (M : ℕ)
    (A B : Finset V) (thr : ℝ) (e : Edge V) :
    lambdaStar s M e \ lowKillers s M A B thr e
      ⊆ (edgeVerts e).biUnion (fun v =>
          ((lambdaAt s e v).filter
            (fun g => ¬ IsLowPair s A B thr g v)).image Sum.inl) := by
  classical
  intro c hc
  obtain ⟨hcΛ, hcnot⟩ := Finset.mem_sdiff.mp hc
  obtain ⟨v, hv, hcv⟩ := mem_lambdaStar.mp hcΛ
  rcases Finset.mem_union.mp hcv with h | h
  · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp h
    refine Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr
      ⟨g, Finset.mem_filter.mpr ⟨hg, fun hlow => hcnot ?_⟩, rfl⟩⟩
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, hlow⟩, rfl⟩)⟩
  · exact absurd (Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_union_right _ h⟩)
      hcnot

open scoped Classical in
/-- **Kim (33)'s combinatorial content**: truncating to low pairs loses at most
`2D` coordinates, where `D` is the (34)/(35) bound. Hence
`|lowKillers(e)| ≥ 2M − 2D`, and the truncated survival probability is at most
`(1−p)^{2M−2D}`. -/
lemma card_lowKillers_ge (s : BlockState V) (M : ℕ) (A B : Finset V) (thr : ℝ)
    (e : Edge V) (hM : ∀ v ∈ edgeVerts e, (lambdaAt s e v).card ≤ M)
    {D : ℕ} (hD : ∀ v ∈ edgeVerts e, ((lambdaAt s e v).filter
      (fun g => ¬ IsLowPair s A B thr g v)).card ≤ D) :
    2 * M - 2 * D ≤ (lowKillers s M A B thr e).card := by
  classical
  have hsub := lowKillers_subset s M A B thr e
  have hdiff : (lambdaStar s M e \ lowKillers s M A B thr e).card ≤ 2 * D := by
    refine le_trans (Finset.card_le_card
      (lambdaStar_sdiff_lowKillers_subset s M A B thr e)) ?_
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ v ∈ edgeVerts e, (((lambdaAt s e v).filter
            (fun g => ¬ IsLowPair s A B thr g v)).image
              (Sum.inl : Edge V → Coord V M)).card
        = ∑ v ∈ edgeVerts e, ((lambdaAt s e v).filter
            (fun g => ¬ IsLowPair s A B thr g v)).card :=
          Finset.sum_congr rfl fun v _ =>
            Finset.card_image_of_injective _ Sum.inl_injective
      _ ≤ ∑ _v ∈ edgeVerts e, D := Finset.sum_le_sum hD
      _ = 2 * D := by rw [Finset.sum_const, edgeVerts_card, smul_eq_mul]
  have hcardΛ := card_lambdaStar s M e hM
  have hsplit : (lambdaStar s M e \ lowKillers s M A B thr e).card
      = (lambdaStar s M e).card - (lowKillers s M A B thr e).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  have hle : (lowKillers s M A B thr e).card ≤ (lambdaStar s M e).card :=
    Finset.card_le_card hsub
  omega

open scoped Classical in
/-- **Kim (33)**: the truncated survival probability is at most `(1−p)^{2M−2D}`. -/
theorem bernoulliPr_survEventLow_le (s : BlockState V) (M : ℕ) (A B : Finset V)
    (thr : ℝ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (e : Edge V)
    (hM : ∀ v ∈ edgeVerts e, (lambdaAt s e v).card ≤ M)
    {D : ℕ} (hD : ∀ v ∈ edgeVerts e, ((lambdaAt s e v).filter
      (fun g => ¬ IsLowPair s A B thr g v)).card ≤ D) :
    bernoulliPr p (survEventLow s M A B thr e) ≤ (1 - p) ^ (2 * M - 2 * D) := by
  rw [bernoulliPr_survEventLow]
  exact pow_le_pow_of_le_one (by linarith) (by linarith)
    (card_lowKillers_ge s M A B thr e hM hD)

open scoped Classical in
/-- Truncated survival of `e` depends only on the coordinates in
`lowKillers(e)`. -/
lemma survEventLow_congr (s : BlockState V) (M : ℕ) (A B : Finset V) (thr : ℝ)
    (e : Edge V) {τ τ' : Fin (Fintype.card (Coord V M)) → Bool}
    (h : ∀ c ∈ lowKillers s M A B thr e,
      τ (coordEquiv V M c) = τ' (coordEquiv V M c)) :
    (τ ∈ survEventLow s M A B thr e ↔ τ' ∈ survEventLow s M A B thr e) := by
  classical
  simp only [survEventLow, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hτ c hc => (h c hc) ▸ hτ c hc,
    fun hτ c hc => (h c hc).symm ▸ hτ c hc⟩

open scoped Classical in
/-- Lipschitz structure of the truncated survivor count `Φ_{A,B}`. -/
lemma isCoordLipschitz_lowSurvivorCount (s : BlockState V) (M : ℕ)
    (A B : Finset V) (thr : ℝ) (S : Finset (Edge V)) :
    IsCoordLipschitz
      (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ∑ e ∈ S, (if σ ∈ survEventLow s M A B thr e then (1 : ℝ) else 0))
      (fun j => ((S.filter (fun e =>
        j ∈ (lowKillers s M A B thr e).image (coordEquiv V M))).card : ℝ)) := by
  classical
  intro j τ τ' hagree
  set Bd : Finset (Edge V) := S.filter (fun e =>
    j ∈ (lowKillers s M A B thr e).image (coordEquiv V M)) with hBd
  have hzero : ∀ e ∈ S, e ∉ Bd →
      (if τ ∈ survEventLow s M A B thr e then (1 : ℝ) else 0)
        - (if τ' ∈ survEventLow s M A B thr e then (1 : ℝ) else 0) = 0 := by
    intro e he heB
    have hnot : j ∉ (lowKillers s M A B thr e).image (coordEquiv V M) := by
      intro hj; exact heB (Finset.mem_filter.mpr ⟨he, hj⟩)
    have hcong : ∀ c ∈ lowKillers s M A B thr e,
        τ (coordEquiv V M c) = τ' (coordEquiv V M c) := by
      intro c hc
      exact hagree _ (fun hEq => hnot (Finset.mem_image.mpr ⟨c, hc, hEq⟩))
    by_cases hs : τ ∈ survEventLow s M A B thr e
    · rw [if_pos hs,
        if_pos ((survEventLow_congr s M A B thr e hcong).mp hs), sub_self]
    · rw [if_neg hs,
        if_neg (fun hc => hs ((survEventLow_congr s M A B thr e hcong).mpr hc)),
        sub_self]
  have hsplit :
      (∑ e ∈ S, (if τ ∈ survEventLow s M A B thr e then (1 : ℝ) else 0))
      - (∑ e ∈ S, (if τ' ∈ survEventLow s M A B thr e then (1 : ℝ) else 0))
      = ∑ e ∈ Bd, ((if τ ∈ survEventLow s M A B thr e then (1 : ℝ) else 0)
          - (if τ' ∈ survEventLow s M A B thr e then (1 : ℝ) else 0)) := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.sum_subset (Finset.filter_subset _ _)
      (fun e he heB => hzero e he heB)).symm
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : Edge V => (1 : ℝ))
    fun e _ => ?_) ?_
  · by_cases h1 : τ ∈ survEventLow s M A B thr e <;>
      by_cases h2 : τ' ∈ survEventLow s M A B thr e <;> simp [h1, h2]
  · rw [Finset.sum_const, nsmul_eq_mul, mul_one]

open scoped Classical in
/-- **Kim's truncated `c_e ≤ 2·thr`.** An edge killed by a genuine coordinate
`g` through the low pair `(g, v)` lies in `N_Λ(g,v) ∩ Γ(A,B)`, a set of size
below `thr` by the very definition of *low*; there are two endpoints. A padding
coordinate kills only its own edge. -/
lemma card_filter_mem_lowKillers_le (s : BlockState V) (M : ℕ)
    (A B : Finset V) {thr : ℝ} (hthr : 1 ≤ thr) (S : Finset (Edge V))
    (hS : S ⊆ gammaBetween s.Γ A B)
    (j : Fin (Fintype.card (Coord V M))) :
    ((S.filter (fun e =>
      j ∈ (lowKillers s M A B thr e).image (coordEquiv V M))).card : ℝ)
      ≤ 2 * thr := by
  classical
  set c : Coord V M := (coordEquiv V M).symm j with hc
  have hj : j = coordEquiv V M c := by rw [hc]; simp
  cases hcase : c with
  | inr q =>
      have hsub : (S.filter (fun e =>
          j ∈ (lowKillers s M A B thr e).image (coordEquiv V M)))
          ⊆ {q.1} := by
        intro e he
        obtain ⟨-, hjmem⟩ := Finset.mem_filter.mp he
        obtain ⟨d, hd, hdj⟩ := Finset.mem_image.mp hjmem
        have hdc : d = c := (coordEquiv V M).injective (by rw [hdj, hj])
        obtain ⟨v, -, hv⟩ := Finset.mem_biUnion.mp hd
        rcases Finset.mem_union.mp hv with h1 | h1
        · obtain ⟨y, -, hy⟩ := Finset.mem_image.mp h1
          rw [hdc, hcase] at hy
          exact absurd hy (by simp)
        · obtain ⟨i, hi⟩ := mem_padAt h1
          rw [hdc, hcase] at hi
          exact Finset.mem_singleton.mpr
            (congrArg (fun z => z.1) (Sum.inr_injective hi)).symm
      calc ((S.filter (fun e =>
              j ∈ (lowKillers s M A B thr e).image (coordEquiv V M))).card : ℝ)
          ≤ (({q.1} : Finset (Edge V)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ = 1 := by simp
        _ ≤ 2 * thr := by linarith
  | inl g =>
      have hsub : (S.filter (fun e =>
          j ∈ (lowKillers s M A B thr e).image (coordEquiv V M)))
          ⊆ ((edgeVerts g).filter (fun v => IsLowPair s A B thr g v)).biUnion
              (fun v => lambdaAt s g v ∩ gammaBetween s.Γ A B) := by
        intro e he
        obtain ⟨heS, hjmem⟩ := Finset.mem_filter.mp he
        obtain ⟨d, hd, hdj⟩ := Finset.mem_image.mp hjmem
        have hdc : d = c := (coordEquiv V M).injective (by rw [hdj, hj])
        obtain ⟨v, hve, hv⟩ := Finset.mem_biUnion.mp hd
        rcases Finset.mem_union.mp hv with h1 | h1
        · obtain ⟨y, hy, hyd⟩ := Finset.mem_image.mp h1
          have hyg : y = g := Sum.inl_injective (by rw [hyd, hdc, hcase])
          subst hyg
          obtain ⟨hyΛ, hylow⟩ := Finset.mem_filter.mp hy
          obtain ⟨⟨hyΓ, hvy⟩, -⟩ := mem_lambdaAt.mp hyΛ
          have heΓ : e ∈ s.Γ := (Finset.mem_filter.mp (hS heS)).1
          refine Finset.mem_biUnion.mpr ⟨v,
            Finset.mem_filter.mpr ⟨mem_edgeVerts.mpr hvy, hylow⟩, ?_⟩
          exact Finset.mem_inter.mpr
            ⟨lambdaAt_symm heΓ (mem_edgeVerts.mp hve) hyΛ, hS heS⟩
        · obtain ⟨i, hi⟩ := mem_padAt h1
          rw [hdc, hcase] at hi
          exact absurd hi (by simp)
      have hcard : ((S.filter (fun e =>
          j ∈ (lowKillers s M A B thr e).image (coordEquiv V M))).card : ℝ)
          ≤ ∑ v ∈ (edgeVerts g).filter (fun v => IsLowPair s A B thr g v),
              ((lambdaAt s g v ∩ gammaBetween s.Γ A B).card : ℝ) := by
        have h := le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
        calc ((S.filter (fun e =>
              j ∈ (lowKillers s M A B thr e).image (coordEquiv V M))).card : ℝ)
            ≤ ((∑ v ∈ (edgeVerts g).filter
                (fun v => IsLowPair s A B thr g v),
                  (lambdaAt s g v ∩ gammaBetween s.Γ A B).card : ℕ) : ℝ) := by
              exact_mod_cast h
          _ = _ := by push_cast; ring
      refine hcard.trans ?_
      have hterm : ∀ v ∈ (edgeVerts g).filter
          (fun v => IsLowPair s A B thr g v),
          ((lambdaAt s g v ∩ gammaBetween s.Γ A B).card : ℝ) ≤ thr :=
        fun v hv => le_of_lt (Finset.mem_filter.mp hv).2
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hlen : (((edgeVerts g).filter
          (fun v => IsLowPair s A B thr g v)).card : ℝ) ≤ 2 := by
        have := Finset.card_filter_le (edgeVerts g)
          (fun v => IsLowPair s A B thr g v)
        rw [edgeVerts_card] at this
        exact_mod_cast this
      nlinarith [hlen, hthr]

open scoped Classical in
/-- `Σ_j c_j ≤ 2M|S|` for the truncated killers, since `lowKillers ⊆ Λ*`. -/
lemma sum_card_filter_lowKillers_le (s : BlockState V) (M : ℕ)
    (A B : Finset V) (thr : ℝ) (S : Finset (Edge V))
    (hM : ∀ e ∈ S, ∀ v ∈ edgeVerts e, (lambdaAt s e v).card ≤ M) :
    ∑ j : Fin (Fintype.card (Coord V M)),
        (S.filter (fun e =>
          j ∈ (lowKillers s M A B thr e).image (coordEquiv V M))).card
      ≤ 2 * M * S.card := by
  classical
  rw [sum_card_filter_comm (Finset.univ : Finset (Fin (Fintype.card (Coord V M))))
    S (fun j e => j ∈ (lowKillers s M A B thr e).image (coordEquiv V M))]
  calc ∑ e ∈ S, (Finset.univ.filter (fun j =>
        j ∈ (lowKillers s M A B thr e).image (coordEquiv V M))).card
      = ∑ e ∈ S, (lowKillers s M A B thr e).card := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [show (Finset.univ.filter (fun j =>
            j ∈ (lowKillers s M A B thr e).image (coordEquiv V M)))
          = (lowKillers s M A B thr e).image (coordEquiv V M) from by
            ext j; simp,
          Finset.card_image_of_injective _ (coordEquiv V M).injective]
    _ ≤ ∑ e ∈ S, 2 * M := by
        refine Finset.sum_le_sum fun e he => ?_
        rw [← card_lambdaStar s M e (hM e he)]
        exact Finset.card_le_card (lowKillers_subset s M A B thr e)
    _ = 2 * M * S.card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

open scoped Classical in
/-- **Kim §4.7, the concentration step for Property 6.**

With `c_e ≤ 2·thr` and `Σ c_e² ≤ 2·thr·2M|Γ(A,B)|`, Kahn's inequality gives the
deviation bound Kim applies at `ρ = n^{−1/4−1/68}`. -/
theorem property6_concentration (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A B : Finset V) {thr : ℝ} (hthr : 1 ≤ thr)
    (S : Finset (Edge V)) (hS : S ⊆ gammaBetween s.Γ A B)
    (hM : ∀ e ∈ S, ∀ v ∈ edgeVerts e, (lambdaAt s e v).card ≤ M)
    {t lam : ℝ} (ht : 0 ≤ t) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          lam ≤ (∑ e ∈ S,
              (if σ ∈ survEventLow s M A B thr e then (1 : ℝ) else 0))
            - bernoulliExp p (fun τ => ∑ e ∈ S,
                (if τ ∈ survEventLow s M A B thr e then (1 : ℝ) else 0))))
      ≤ Real.exp (-t * lam + t ^ 2 / 2 * (p * (1 - p)
          * ((2 * thr) * (2 * M * S.card) * Real.exp (t * (2 * thr))))) := by
  classical
  refine le_trans (bernoulliPr_upper_tail hp0 hp1
    (isCoordLipschitz_lowSurvivorCount s M A B thr S) ht) ?_
  refine Real.exp_le_exp.mpr ?_
  have hpp : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  have hC := card_filter_mem_lowKillers_le s M A B hthr S hS
  have hQ0 : (0 : ℝ) ≤ (2 * thr) * (2 * M * S.card) := by
    have : (0 : ℝ) ≤ 2 * thr := by linarith
    positivity
  have hsumsq : ∑ j : Fin (Fintype.card (Coord V M)),
      ((S.filter (fun e =>
        j ∈ (lowKillers s M A B thr e).image (coordEquiv V M))).card : ℝ) ^ 2
      ≤ (2 * thr) * (2 * M * S.card) := by
    refine le_trans (sum_sq_le_max_mul_sum Finset.univ _
      (fun j _ => hC j) (fun j _ => Nat.cast_nonneg _)) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have hcount := sum_card_filter_lowKillers_le s M A B thr S hM
    calc ∑ j : Fin (Fintype.card (Coord V M)),
          ((S.filter (fun e =>
            j ∈ (lowKillers s M A B thr e).image (coordEquiv V M))).card : ℝ)
        = ((∑ j : Fin (Fintype.card (Coord V M)),
            (S.filter (fun e =>
              j ∈ (lowKillers s M A B thr e).image
                (coordEquiv V M))).card : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 * M * S.card : ℕ) : ℝ) := by exact_mod_cast hcount
      _ = 2 * M * S.card := by push_cast; ring
  have hinner := sum_sq_exp_le_of_bounded _ (fun j => Nat.cast_nonneg _) hC ht
    hsumsq hQ0
  have hscale := mul_le_mul_of_nonneg_left hinner hpp
  have hscale2 := mul_le_mul_of_nonneg_left hscale
    (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)
  linarith

open scoped Classical in
/-- The `m+1`-element subsets of `A` containing a fixed `a ∈ A` are in bijection
with the `m`-element subsets of `A.erase a`. -/
lemma card_powersetCard_filter_mem {A : Finset V} {a : V} (ha : a ∈ A) (m : ℕ) :
    ((A.powersetCard (m + 1)).filter (fun A₀ => a ∈ A₀)).card
      = (A.card - 1).choose m := by
  classical
  rw [show A.card - 1 = (A.erase a).card from (Finset.card_erase_of_mem ha).symm,
    ← Finset.card_powersetCard]
  refine Finset.card_nbij' (fun A₀ => A₀.erase a) (fun S => insert a S)
    ?_ ?_ ?_ ?_
  · intro A₀ hA₀
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hA₀).1
    have hmem : a ∈ A₀ := (Finset.mem_filter.mp hA₀).2
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro x hx
      have hxA₀ : x ∈ A₀ := Finset.mem_of_mem_erase hx
      exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hx, hsub hxA₀⟩
    · rw [Finset.card_erase_of_mem hmem, hcard]
      omega
  · intro S hS
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
    have hna : a ∉ S := fun hc => (Finset.mem_erase.mp (hsub hc)).1 rfl
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · exact Finset.mem_of_mem_erase (hsub hx)
    · rw [Finset.card_insert_of_notMem hna, hcard]
    · exact Finset.mem_insert_self _ _
  · intro A₀ hA₀
    have hmem : a ∈ A₀ := (Finset.mem_filter.mp hA₀).2
    exact Finset.insert_erase hmem
  · intro S hS
    obtain ⟨hsub, -⟩ := Finset.mem_powersetCard.mp hS
    have hna : a ∉ S := fun hc => (Finset.mem_erase.mp (hsub hc)).1 rfl
    exact Finset.erase_insert hna

lemma mem_gammaBetween {Γ : Finset (Edge V)} {A B : Finset V} {e : Edge V} :
    e ∈ gammaBetween Γ A B ↔
      e ∈ Γ ∧ ∃ v ∈ A, ∃ w ∈ B, v ≠ w ∧ v ∈ e.val ∧ w ∈ e.val := by
  classical
  show e ∈ Finset.filter _ _ ↔ _
  rw [Finset.mem_filter]

lemma gammaBetween_mono {Γ : Finset (Edge V)} {A A' B B' : Finset V}
    (hA : A' ⊆ A) (hB : B' ⊆ B) :
    gammaBetween Γ A' B' ⊆ gammaBetween Γ A B := by
  classical
  intro e he
  obtain ⟨heΓ, v, hv, w, hw, hvw, hve, hwe⟩ := mem_gammaBetween.mp he
  exact mem_gammaBetween.mpr ⟨heΓ, v, hA hv, w, hB hw, hvw, hve, hwe⟩

open scoped Classical in
/-- **Kim's reduction to `|A| = |B| = m` (§4.7, first line).**

If every pair of `m`-element subsets `A₀ ⊆ A`, `B₀ ⊆ B` satisfies
`|Γ(A₀,B₀)| ≤ c m²`, then `|Γ(A,B)| ≤ c|A||B|` — by double counting, since each
edge of `Γ(A,B)` lies in `Γ(A₀,B₀)` for `C(|A|−1,m−1)·C(|B|−1,m−1)` of the
`C(|A|,m)·C(|B|,m)` pairs, and `m·C(N,m) = N·C(N−1,m−1)`. No constant is
lost. -/
lemma card_gammaBetween_of_powersetCard (Γ : Finset (Edge V)) (A B : Finset V)
    {m : ℕ} (hmA : m + 1 ≤ A.card) (hmB : m + 1 ≤ B.card) {c : ℝ}
    (h : ∀ A₀ ∈ A.powersetCard (m + 1), ∀ B₀ ∈ B.powersetCard (m + 1),
      ((gammaBetween Γ A₀ B₀).card : ℝ) ≤ c * (m + 1) * (m + 1)) :
    ((gammaBetween Γ A B).card : ℝ) ≤ c * A.card * B.card := by
  classical
  set PA : Finset (Finset V) := A.powersetCard (m + 1) with hPA
  set PB : Finset (Finset V) := B.powersetCard (m + 1) with hPB
  set G : Finset (Edge V) := gammaBetween Γ A B with hG
  obtain ⟨N, hN⟩ : ∃ N, A.card = N + 1 := ⟨A.card - 1, by omega⟩
  obtain ⟨Nb, hNb⟩ : ∃ Nb, B.card = Nb + 1 := ⟨B.card - 1, by omega⟩
  have hA1 : A.card - 1 = N := by omega
  have hB1 : B.card - 1 = Nb := by omega
  have hmN : m ≤ N := by omega
  have hmNb : m ≤ Nb := by omega
  have hDA : 0 < N.choose m := Nat.choose_pos hmN
  have hDB : 0 < Nb.choose m := Nat.choose_pos hmNb
  -- each edge of `Γ(A,B)` is caught by many pairs
  have hlow : ∀ e ∈ G, N.choose m * Nb.choose m
      ≤ ((PA ×ˢ PB).filter (fun q => e ∈ gammaBetween Γ q.1 q.2)).card := by
    intro e he
    obtain ⟨heΓ, v, hv, w, hw, hvw, hve, hwe⟩ := mem_gammaBetween.mp (hG ▸ he)
    have hsub : (PA.filter (fun A₀ => v ∈ A₀)) ×ˢ (PB.filter (fun B₀ => w ∈ B₀))
        ⊆ (PA ×ˢ PB).filter (fun q => e ∈ gammaBetween Γ q.1 q.2) := by
      intro q hq
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hq
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hq.1.1, hq.2.1⟩, ?_⟩
      exact mem_gammaBetween.mpr ⟨heΓ, v, hq.1.2, w, hq.2.2, hvw, hve, hwe⟩
    have hcards := Finset.card_le_card hsub
    rwa [Finset.card_product, hPA, hPB, card_powersetCard_filter_mem hv,
      card_powersetCard_filter_mem hw, hA1, hB1] at hcards
  -- double counting
  have hcount : ∑ q ∈ PA ×ˢ PB, (gammaBetween Γ q.1 q.2).card
      = ∑ e ∈ G,
          ((PA ×ˢ PB).filter (fun q => e ∈ gammaBetween Γ q.1 q.2)).card := by
    have hstep : ∀ q ∈ PA ×ˢ PB, (gammaBetween Γ q.1 q.2).card
        = (G.filter (fun e => e ∈ gammaBetween Γ q.1 q.2)).card := by
      intro q hq
      rw [Finset.mem_product] at hq
      have hsub : gammaBetween Γ q.1 q.2 ⊆ G :=
        gammaBetween_mono (Finset.mem_powersetCard.mp (hPA ▸ hq.1)).1
          (Finset.mem_powersetCard.mp (hPB ▸ hq.2)).1
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
    rw [Finset.sum_congr rfl hstep]
    exact sum_card_filter_comm (PA ×ˢ PB) G
      (fun q e => e ∈ gammaBetween Γ q.1 q.2)
  have hL : G.card * (N.choose m * Nb.choose m)
      ≤ ∑ q ∈ PA ×ˢ PB, (gammaBetween Γ q.1 q.2).card := by
    rw [hcount]
    calc G.card * (N.choose m * Nb.choose m)
        = ∑ _e ∈ G, N.choose m * Nb.choose m := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hlow
  have hLR : (G.card : ℝ) * ((N.choose m : ℝ) * (Nb.choose m : ℝ))
      ≤ ∑ q ∈ PA ×ˢ PB, ((gammaBetween Γ q.1 q.2).card : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hL
    push_cast at this
    exact this
  have hU : (∑ q ∈ PA ×ˢ PB, ((gammaBetween Γ q.1 q.2).card : ℝ))
      ≤ ((A.card.choose (m + 1) : ℝ) * (B.card.choose (m + 1) : ℝ))
        * (c * (m + 1) * (m + 1)) := by
    calc ∑ q ∈ PA ×ˢ PB, ((gammaBetween Γ q.1 q.2).card : ℝ)
        ≤ ∑ _q ∈ PA ×ˢ PB, (c * ((m : ℝ) + 1) * ((m : ℝ) + 1)) := by
          refine Finset.sum_le_sum fun q hq => ?_
          rw [Finset.mem_product] at hq
          have := h q.1 (hPA ▸ hq.1) q.2 (hPB ▸ hq.2)
          push_cast at this ⊢
          exact this
      _ = ((PA ×ˢ PB).card : ℝ) * (c * ((m : ℝ) + 1) * ((m : ℝ) + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((A.card.choose (m + 1) : ℝ) * (B.card.choose (m + 1) : ℝ))
            * (c * ((m : ℝ) + 1) * ((m : ℝ) + 1)) := by
          rw [Finset.card_product, hPA, hPB, Finset.card_powersetCard,
            Finset.card_powersetCard]
          push_cast; ring
  -- `m·C(N+1, m+1) = (N+1)·C(N, m)`
  have hidA : (A.card.choose (m + 1) : ℝ) * ((m : ℝ) + 1)
      = (A.card : ℝ) * (N.choose m : ℝ) := by
    have hnat : A.card * N.choose m = A.card.choose (m + 1) * (m + 1) := by
      rw [hN]; exact Nat.succ_mul_choose_eq N m
    have := congrArg (fun x : ℕ => (x : ℝ)) hnat
    push_cast at this
    linarith [this]
  have hidB : (B.card.choose (m + 1) : ℝ) * ((m : ℝ) + 1)
      = (B.card : ℝ) * (Nb.choose m : ℝ) := by
    have hnat : B.card * Nb.choose m = B.card.choose (m + 1) * (m + 1) := by
      rw [hNb]; exact Nat.succ_mul_choose_eq Nb m
    have := congrArg (fun x : ℕ => (x : ℝ)) hnat
    push_cast at this
    linarith [this]
  have hDpos : (0 : ℝ) < (N.choose m : ℝ) * (Nb.choose m : ℝ) := by
    have h1 : (0 : ℝ) < (N.choose m : ℝ) := by exact_mod_cast hDA
    have h2 : (0 : ℝ) < (Nb.choose m : ℝ) := by exact_mod_cast hDB
    positivity
  refine le_of_mul_le_mul_right ?_ hDpos
  calc (G.card : ℝ) * ((N.choose m : ℝ) * (Nb.choose m : ℝ))
      ≤ ((A.card.choose (m + 1) : ℝ) * (B.card.choose (m + 1) : ℝ))
        * (c * ((m : ℝ) + 1) * ((m : ℝ) + 1)) := le_trans hLR hU
    _ = c * ((A.card.choose (m + 1) : ℝ) * ((m : ℝ) + 1))
          * ((B.card.choose (m + 1) : ℝ) * ((m : ℝ) + 1)) := by ring
    _ = c * ((A.card : ℝ) * (N.choose m : ℝ))
          * ((B.card : ℝ) * (Nb.choose m : ℝ)) := by rw [hidA, hidB]
    _ = c * A.card * B.card * ((N.choose m : ℝ) * (Nb.choose m : ℝ)) := by ring

/-- `#{S ⊆ A : |S| = m+1, x ∈ S, y ∉ S} = C(|A|−2, m)` for `x ≠ y` in `A`. -/
lemma card_powersetCard_filter_mem_not_mem {A : Finset V} {x y : V}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) (m : ℕ) :
    ((A.powersetCard (m + 1)).filter (fun S => x ∈ S ∧ y ∉ S)).card
      = (A.card - 2).choose m := by
  classical
  have hyx : y ∈ A.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
  have hcard2 : ((A.erase x).erase y).card = A.card - 2 := by
    rw [Finset.card_erase_of_mem hyx, Finset.card_erase_of_mem hx]
    omega
  rw [← hcard2, ← Finset.card_powersetCard]
  refine Finset.card_nbij' (fun S => S.erase x) (fun U => insert x U)
    ?_ ?_ ?_ ?_
  · intro S hS
    obtain ⟨hmem, hnot⟩ := (Finset.mem_filter.mp hS).2
    obtain ⟨hsub, hcard⟩ :=
      Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro z hz
      have hzS : z ∈ S := Finset.mem_of_mem_erase hz
      refine Finset.mem_erase.mpr ⟨fun hzy => hnot (hzy ▸ hzS), ?_⟩
      exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hz, hsub hzS⟩
    · rw [Finset.card_erase_of_mem hmem, hcard]
      omega
  · intro U hU
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hU
    have hxU : x ∉ U := fun hc =>
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase (hsub hc))).1 rfl
    have hyU : y ∉ U := fun hc => (Finset.mem_erase.mp (hsub hc)).1 rfl
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩,
      Finset.mem_insert_self _ _, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hsub hz))
    · rw [Finset.card_insert_of_notMem hxU, hcard]
    · intro hc
      rcases Finset.mem_insert.mp hc with h | h
      · exact hxy h.symm
      · exact hyU h
  · intro S hS
    exact Finset.insert_erase (Finset.mem_filter.mp hS).2.1
  · intro U hU
    obtain ⟨hsub, -⟩ := Finset.mem_powersetCard.mp hU
    have hxU : x ∉ U := fun hc =>
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase (hsub hc))).1 rfl
    exact Finset.erase_insert hxU

/-- `C(N+2,M+1)·(M+1)·(N+2−(M+1)) = (N+2)(N+1)·C(N,M)`. -/
lemma choose_mul_split_identity (N M : ℕ) :
    (N + 2).choose (M + 1) * (M + 1) * (N + 2 - (M + 1))
      = (N + 2) * (N + 1) * N.choose M := by
  have h1 : (N + 2) * (N + 1).choose M = (N + 2).choose (M + 1) * (M + 1) := by
    simpa using Nat.succ_mul_choose_eq (N + 1) M
  have h2 : (N + 1) * N.choose M = (N + 1).choose (M + 1) * (M + 1) := by
    simpa using Nat.succ_mul_choose_eq N M
  have h3 : (N + 1).choose (M + 1) * (M + 1) = (N + 1).choose M * (N + 1 - M) :=
    Nat.choose_succ_right_eq (N + 1) M
  have h4 : N + 2 - (M + 1) = N + 1 - M := by omega
  calc (N + 2).choose (M + 1) * (M + 1) * (N + 2 - (M + 1))
      = ((N + 2) * (N + 1).choose M) * (N + 1 - M) := by rw [h1, h4]
    _ = (N + 2) * ((N + 1).choose M * (N + 1 - M)) := by ring
    _ = (N + 2) * ((N + 1).choose (M + 1) * (M + 1)) := by rw [h3]
    _ = (N + 2) * ((N + 1) * N.choose M) := by rw [h2]
    _ = (N + 2) * (N + 1) * N.choose M := by ring

open scoped Classical in
/-- **The unipartite half of Property 6, from the bipartite half.**

Average over all splits `A = S ⊎ (A \ S)` with `|S| = m`: each edge of `Γ(A)`
crosses exactly `2·C(|A|−2, m−1)` of the `C(|A|,m)` splits, and
`C(|A|,m)·m·(|A|−m) = C(|A|−2,m−1)·|A|·(|A|−1)`, so the bipartite bound
`c·m·(|A|−m)` per split integrates to exactly `c·C(|A|,2)` — no constant lost.
This is how Kim's second Property-6 clause is recovered from the first. -/
lemma card_gammaBetween_self_of_split (Γ : Finset (Edge V)) (A : Finset V)
    {m : ℕ} (hm1 : 1 ≤ m) (hm : m < A.card) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ S ∈ A.powersetCard m, ((gammaBetween Γ S (A \ S)).card : ℝ)
      ≤ c * (m : ℝ) * ((A.card : ℝ) - m)) :
    ((gammaBetween Γ A A).card : ℝ) ≤ c * (A.card.choose 2 : ℕ) := by
  classical
  set P : Finset (Finset V) := A.powersetCard m with hP
  set G : Finset (Edge V) := gammaBetween Γ A A with hG
  obtain ⟨M, hM⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  obtain ⟨N, hN⟩ : ∃ N, A.card = N + 2 := ⟨A.card - 2, by omega⟩
  have hMN : M ≤ N := by omega
  have hpos : 0 < N.choose M := Nat.choose_pos hMN
  have hlow : ∀ e ∈ G, 2 * N.choose M
      ≤ (P.filter (fun S => e ∈ gammaBetween Γ S (A \ S))).card := by
    intro e he
    obtain ⟨heΓ, u, hu, v, hv, huv, hue, hve⟩ := mem_gammaBetween.mp (hG ▸ he)
    have hsub1 : (P.filter (fun S => u ∈ S ∧ v ∉ S))
        ⊆ P.filter (fun S => e ∈ gammaBetween Γ S (A \ S)) := by
      intro S hS
      obtain ⟨hSP, hin, hout⟩ := Finset.mem_filter.mp hS
      exact Finset.mem_filter.mpr ⟨hSP, mem_gammaBetween.mpr
        ⟨heΓ, u, hin, v, Finset.mem_sdiff.mpr ⟨hv, hout⟩, huv, hue, hve⟩⟩
    have hsub2 : (P.filter (fun S => v ∈ S ∧ u ∉ S))
        ⊆ P.filter (fun S => e ∈ gammaBetween Γ S (A \ S)) := by
      intro S hS
      obtain ⟨hSP, hin, hout⟩ := Finset.mem_filter.mp hS
      exact Finset.mem_filter.mpr ⟨hSP, mem_gammaBetween.mpr
        ⟨heΓ, v, hin, u, Finset.mem_sdiff.mpr ⟨hu, hout⟩, Ne.symm huv, hve, hue⟩⟩
    have hdisj : Disjoint (P.filter (fun S => u ∈ S ∧ v ∉ S))
        (P.filter (fun S => v ∈ S ∧ u ∉ S)) := by
      refine Finset.disjoint_left.mpr fun S hS1 hS2 => ?_
      exact (Finset.mem_filter.mp hS2).2.2 (Finset.mem_filter.mp hS1).2.1
    have hun : (P.filter (fun S => u ∈ S ∧ v ∉ S))
        ∪ (P.filter (fun S => v ∈ S ∧ u ∉ S))
        ⊆ P.filter (fun S => e ∈ gammaBetween Γ S (A \ S)) :=
      Finset.union_subset hsub1 hsub2
    have hcard := Finset.card_le_card hun
    rw [Finset.card_union_of_disjoint hdisj] at hcard
    have e1 : (P.filter (fun S => u ∈ S ∧ v ∉ S)).card = N.choose M := by
      rw [hP, hM, card_powersetCard_filter_mem_not_mem hu hv huv M, hN]
      norm_num
    have e2 : (P.filter (fun S => v ∈ S ∧ u ∉ S)).card = N.choose M := by
      rw [hP, hM, card_powersetCard_filter_mem_not_mem hv hu (Ne.symm huv) M, hN]
      norm_num
    omega
  have hcount : ∑ S ∈ P, (gammaBetween Γ S (A \ S)).card
      = ∑ e ∈ G, (P.filter (fun S => e ∈ gammaBetween Γ S (A \ S))).card := by
    have hstep : ∀ S ∈ P, (gammaBetween Γ S (A \ S)).card
        = (G.filter (fun e => e ∈ gammaBetween Γ S (A \ S))).card := by
      intro S hS
      have hSA : S ⊆ A := (Finset.mem_powersetCard.mp (hP ▸ hS)).1
      have hsub : gammaBetween Γ S (A \ S) ⊆ G :=
        gammaBetween_mono hSA Finset.sdiff_subset
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
    rw [Finset.sum_congr rfl hstep]
    exact sum_card_filter_comm P G (fun S e => e ∈ gammaBetween Γ S (A \ S))
  have hL : G.card * (2 * N.choose M)
      ≤ ∑ S ∈ P, (gammaBetween Γ S (A \ S)).card := by
    rw [hcount]
    calc G.card * (2 * N.choose M)
        = ∑ _e ∈ G, 2 * N.choose M := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hlow
  have hLR : (G.card : ℝ) * (2 * (N.choose M : ℝ))
      ≤ ∑ S ∈ P, ((gammaBetween Γ S (A \ S)).card : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hL
    push_cast at this
    exact this
  have hcardP : P.card = A.card.choose m := by
    rw [hP, Finset.card_powersetCard]
  have hU : (∑ S ∈ P, ((gammaBetween Γ S (A \ S)).card : ℝ))
      ≤ (A.card.choose m : ℝ) * (c * (m : ℝ) * ((A.card : ℝ) - m)) := by
    calc ∑ S ∈ P, ((gammaBetween Γ S (A \ S)).card : ℝ)
        ≤ ∑ _S ∈ P, (c * (m : ℝ) * ((A.card : ℝ) - m)) :=
          Finset.sum_le_sum fun S hS => h S (hP ▸ hS)
      _ = (P.card : ℝ) * (c * (m : ℝ) * ((A.card : ℝ) - m)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (A.card.choose m : ℝ) * (c * (m : ℝ) * ((A.card : ℝ) - m)) := by
          rw [hcardP]
  have hAm : (A.card : ℝ) - (m : ℝ) = ((A.card - m : ℕ) : ℝ) :=
    (Nat.cast_sub (le_of_lt hm)).symm
  have hid : (A.card.choose m : ℝ) * (m : ℝ) * ((A.card : ℝ) - m)
      = (N.choose M : ℝ) * ((N : ℝ) + 2) * ((N : ℝ) + 1) := by
    rw [hAm]
    have hnat := choose_mul_split_identity N M
    have hcast := congrArg (fun x : ℕ => (x : ℝ)) hnat
    push_cast at hcast
    rw [hN, hM]
    push_cast
    linarith [hcast]
  have hchoose2 : ((A.card.choose 2 : ℕ) : ℝ)
      = ((N : ℝ) + 2) * ((N : ℝ) + 1) / 2 := by
    rw [hN, Nat.cast_choose_two]
    push_cast
    ring
  have hposR : (0 : ℝ) < (N.choose M : ℝ) := by exact_mod_cast hpos
  have hcombine : (G.card : ℝ) * (2 * (N.choose M : ℝ))
      ≤ c * ((N.choose M : ℝ) * ((N : ℝ) + 2) * ((N : ℝ) + 1)) := by
    refine le_trans hLR (le_trans hU (le_of_eq ?_))
    rw [show (A.card.choose m : ℝ) * (c * (m : ℝ) * ((A.card : ℝ) - m))
        = c * ((A.card.choose m : ℝ) * (m : ℝ) * ((A.card : ℝ) - m)) by ring,
      hid]
  rw [hchoose2]
  nlinarith [hcombine, hposR, hc]

open scoped Classical in
/-- **Property 6's unipartite clause**, recovered from the bipartite one by
averaging over splits at the threshold `mcut`. -/
lemma Property6.self {s : BlockState V} {i : ℕ} (h6 : Property6 s i)
    (hcut : 1 ≤ mcut n) (A : Finset V) (hA : 2 * mcut n ≤ A.card) :
    ((gammaBetween s.Γ A A).card : ℝ)
      ≤ bSeq n i * (A.card.choose 2 : ℕ) := by
  refine card_gammaBetween_self_of_split s.Γ A (m := mcut n) hcut
    (by omega) (bSeq_pos n i).le ?_
  intro S hS
  obtain ⟨hSA, hScard⟩ := Finset.mem_powersetCard.mp hS
  have hdisj : Disjoint S (A \ S) := Finset.disjoint_sdiff
  have hSd : (A \ S).card = A.card - mcut n := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSA, hScard]
  have hSdge : mcut n ≤ (A \ S).card := by omega
  have hb := h6 S (A \ S) hdisj (le_of_eq hScard.symm) hSdge
  rw [hScard, hSd] at hb
  have hcast : ((A.card - mcut n : ℕ) : ℝ) = (A.card : ℝ) - (mcut n : ℝ) :=
    Nat.cast_sub (by omega)
  rw [hcast] at hb
  linarith [hb]

/-- `card_gammaBetween_of_powersetCard` with the subset size given as a
positive natural. -/
lemma card_gammaBetween_of_powersetCard' (Γ : Finset (Edge V)) (A B : Finset V)
    {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hmA : m₀ ≤ A.card) (hmB : m₀ ≤ B.card) {c : ℝ}
    (h : ∀ A₀ ∈ A.powersetCard m₀, ∀ B₀ ∈ B.powersetCard m₀,
      ((gammaBetween Γ A₀ B₀).card : ℝ) ≤ c * m₀ * m₀) :
    ((gammaBetween Γ A B).card : ℝ) ≤ c * A.card * B.card := by
  obtain ⟨m, rfl⟩ : ∃ m, m₀ = m + 1 := ⟨m₀ - 1, by omega⟩
  refine card_gammaBetween_of_powersetCard Γ A B hmA hmB ?_
  intro A₀ hA₀ B₀ hB₀
  have hb := h A₀ hA₀ B₀ hB₀
  push_cast at hb
  exact hb

open scoped Classical in
theorem property6_prob (k : ℕ) (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (thr : ℝ) (hcut : 1 ≤ mcut n)
    {q1 : ℝ} (hq1 : 0 ≤ q1)
    (hbad1 : ∀ A B : Finset V, Disjoint A B → A.card = mcut n → B.card = mcut n →
      bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          bSeq n (k + 1) * (mcut n : ℝ) * (mcut n : ℝ)
            < ∑ e ∈ gammaBetween s.Γ A B,
                (if σ ∈ survEventLow s M A B thr e then (1 : ℝ) else 0)))
      ≤ q1) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          ¬ Property6 (blockStepP s M σ) (k + 1)))
      ≤ ((n : ℕ).choose (mcut n) : ℝ) * ((n : ℕ).choose (mcut n) : ℝ) * q1 := by
  classical
  set Pw : Finset (Finset V) :=
    (Finset.univ : Finset V).powersetCard (mcut n) with hPw
  refine le_trans (bernoulliPr_mono hp0 hp1 (?_ :
      (Finset.univ.filter (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ¬ Property6 (blockStepP s M σ) (k + 1)))
      ⊆ ((Pw ×ˢ Pw).filter (fun q => Disjoint q.1 q.2)).biUnion (fun q =>
        Finset.univ.filter (fun σ =>
          bSeq n (k + 1) * (mcut n : ℝ) * (mcut n : ℝ)
            < ∑ e ∈ gammaBetween s.Γ q.1 q.2,
                (if σ ∈ survEventLow s M q.1 q.2 thr e
                  then (1 : ℝ) else 0))))) ?_
  · intro σ hσ
    obtain ⟨-, hfail⟩ := Finset.mem_filter.mp hσ
    rw [Property6] at hfail
    push_neg at hfail
    obtain ⟨A, B, hAB, hA, hB, hgt⟩ := hfail
    by_contra hcon
    have hall : ∀ A₀ ∈ A.powersetCard (mcut n), ∀ B₀ ∈ B.powersetCard (mcut n),
        ((gammaBetween (blockStepP s M σ).Γ A₀ B₀).card : ℝ)
          ≤ bSeq n (k + 1) * (mcut n : ℝ) * (mcut n : ℝ) := by
      intro A₀ hA₀ B₀ hB₀
      obtain ⟨-, hA₀card⟩ := Finset.mem_powersetCard.mp hA₀
      obtain ⟨-, hB₀card⟩ := Finset.mem_powersetCard.mp hB₀
      refine le_trans (card_gammaBetween_blockStepP_le s M σ A₀ B₀ thr) ?_
      by_contra hlt
      push_neg at hlt
      refine hcon (Finset.mem_biUnion.mpr ⟨(A₀, B₀), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hA₀card⟩,
            Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hB₀card⟩⟩,
          Finset.disjoint_of_subset_left (Finset.mem_powersetCard.mp hA₀).1
            (Finset.disjoint_of_subset_right
              (Finset.mem_powersetCard.mp hB₀).1 hAB)⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩⟩)
    exact absurd (card_gammaBetween_of_powersetCard' (blockStepP s M σ).Γ A B
      hcut hA hB hall) (not_le.mpr hgt)
  refine le_trans (bernoulliPr_biUnion_le hp0 hp1 _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : Finset V × Finset V => q1)
    fun q hq => ?_) ?_
  · obtain ⟨hqp, hqd⟩ := Finset.mem_filter.mp hq
    rw [Finset.mem_product] at hqp
    exact hbad1 q.1 q.2 hqd (Finset.mem_powersetCard.mp (hPw ▸ hqp.1)).2
      (Finset.mem_powersetCard.mp (hPw ▸ hqp.2)).2
  · rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (((Pw ×ˢ Pw).filter (fun q => Disjoint q.1 q.2)).card : ℝ)
        ≤ ((n : ℕ).choose (mcut n) : ℝ) * ((n : ℕ).choose (mcut n) : ℝ) := by
      have hle := Finset.card_filter_le (Pw ×ˢ Pw) (fun q => Disjoint q.1 q.2)
      rw [Finset.card_product, hPw, Finset.card_powersetCard,
        Finset.card_univ] at hle
      calc (((Pw ×ˢ Pw).filter (fun q => Disjoint q.1 q.2)).card : ℝ)
          ≤ (((n : ℕ).choose (mcut n) * (n : ℕ).choose (mcut n) : ℕ) : ℝ) := by
            exact_mod_cast hle
        _ = _ := by push_cast; ring
    calc (((Pw ×ˢ Pw).filter (fun q => Disjoint q.1 q.2)).card : ℝ) * q1
        ≤ (((n : ℕ).choose (mcut n) : ℝ)
            * ((n : ℕ).choose (mcut n) : ℝ)) * q1 :=
          mul_le_mul_of_nonneg_right hcard hq1
      _ = _ := by ring

open scoped Classical in
/-- **Lower-tail form of Kahn's inequality.** Kim's §4.8 needs a *lower* bound
on `Φ⁽¹⁾_T`, which is the upper tail for `−Φ`; the Lipschitz constants are
unchanged. -/
theorem bernoulliPr_lower_tail {m : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {Φ : (Fin m → Bool) → ℝ} {c : Fin m → ℝ} (h_lip : IsCoordLipschitz Φ c)
    {t lam : ℝ} (ht : 0 ≤ t) :
    bernoulliPr p (Finset.univ.filter
        (fun σ => Φ σ ≤ bernoulliExp p Φ - lam))
      ≤ Real.exp (-t * lam + t ^ 2 / 2 * (p * (1 - p)
          * ∑ j : Fin m, c j ^ 2 * Real.exp (t * c j))) := by
  classical
  have hmain := bernoulliPr_upper_tail hp₀ hp₁ h_lip.neg (t := t) (lam := lam) ht
  refine le_trans (le_of_eq ?_) hmain
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, bernoulliExp_neg]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- Kim's `Z'`: the `Γ`-edges removed because they close a triangle with two
edges of `ℰ ∪ X`. -/
noncomputable def killedZ (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) : Finset (Edge V) := by
  classical
  exact s.Γ.filter (fun e => ¬ ∀ f ∈ s.E ∪ sampleP s M σ,
    ∀ g ∈ s.E ∪ sampleP s M σ, ¬ IsTriangle e f g)

/-- Lower-bound companion of `bernoulliExp_count_le`. -/
lemma bernoulliExp_count_ge {m : ℕ} {p q : ℝ} {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (Ev : ι → Finset (Fin m → Bool))
    (hq : ∀ i ∈ S, q ≤ bernoulliPr p (Ev i)) :
    q * S.card
      ≤ bernoulliExp p (fun σ => ∑ i ∈ S, (if σ ∈ Ev i then (1 : ℝ) else 0)) := by
  rw [bernoulliExp_sum]
  calc q * S.card = ∑ _i ∈ S, q := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ S, bernoulliPr p (Ev i) := Finset.sum_le_sum hq
    _ = ∑ i ∈ S, bernoulliExp p (fun σ => if σ ∈ Ev i then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun i _ => bernoulliPr_eq_exp p (Ev i)

open scoped Classical in
/-- Truncating can only *increase* the survival probability: `lowKillers ⊆ Λ*`,
so `Pr(e ∉ Y⁽¹⁾) ≥ Pr(e ∉ Y') = (1−p)^{2M}`. This is the lower half of
Lemma 4.1 as §4.8 uses it. -/
theorem bernoulliPr_survEventLow_ge (s : BlockState V) (M : ℕ) (A B : Finset V)
    (thr : ℝ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (e : Edge V)
    (hM : ∀ v ∈ edgeVerts e, (lambdaAt s e v).card ≤ M) :
    (1 - p) ^ (2 * M) ≤ bernoulliPr p (survEventLow s M A B thr e) := by
  rw [bernoulliPr_survEventLow]
  refine pow_le_pow_of_le_one (by linarith) (by linarith) ?_
  rw [← card_lambdaStar s M e hM]
  exact Finset.card_le_card (lowKillers_subset s M A B thr e)

open scoped Classical in
/-- **Kim's `E[Φ⁽¹⁾_T] ≥ (1−p)^{2M}|Γ(T)|`**, the expectation input to (39). -/
theorem lowSurvivorCount_expectation_ge (s : BlockState V) (M : ℕ)
    (A B : Finset V) (thr : ℝ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset (Edge V))
    (hM : ∀ e ∈ S, ∀ v ∈ edgeVerts e, (lambdaAt s e v).card ≤ M) :
    (1 - p) ^ (2 * M) * S.card
      ≤ bernoulliExp p (fun σ =>
          ∑ e ∈ S, (if σ ∈ survEventLow s M A B thr e then (1 : ℝ) else 0)) :=
  bernoulliExp_count_ge S _
    (fun e he => bernoulliPr_survEventLow_ge s M A B thr hp0 hp1 e (hM e he))

open scoped Classical in
/-- **Kim (38)**: `Pr(|X' ∩ Γ(T)| ≥ p|Γ(T)| + λ)` is bounded by the master
sampled-edge estimate applied to `A = Γ(T)`. -/
theorem card_sample_inter_gammaT_tail (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (T : Finset V) {t lam : ℝ} (ht : 0 ≤ t)
    (hvar : t ^ 2 / 2 * (p * (1 - p)
        * (((gammaBetween s.Γ T T).card : ℝ) * Real.exp t)) ≤ t * lam / 2) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          p * ((gammaBetween s.Γ T T).card : ℝ) + lam
            ≤ ((gammaBetween s.Γ T T ∩ sampleP s M σ).card : ℝ)))
      ≤ 2 * Real.exp (-(t * lam) / 2) := by
  classical
  have h := sampleEdges_inter_tail (padEmb V M) hp0 hp1 s
    (A := gammaBetween s.Γ T T) (Finset.filter_subset _ _) ht hvar
  refine le_trans (le_of_eq ?_) h
  congr 1

open scoped Classical in
/-- **Kim (39)**: the lower tail for `Φ⁽¹⁾_T`. -/
theorem lowSurvivorCount_lower_tail (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (T : Finset V) {thr : ℝ} (hthr : 1 ≤ thr)
    (hM : ∀ e ∈ gammaBetween s.Γ T T, ∀ v ∈ edgeVerts e,
      (lambdaAt s e v).card ≤ M)
    {t lam target : ℝ} (ht : 0 ≤ t)
    (htarget : target ≤ (1 - p) ^ (2 * M) * ((gammaBetween s.Γ T T).card : ℝ)
      - lam) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          (∑ e ∈ gammaBetween s.Γ T T,
            (if σ ∈ survEventLow s M T T thr e then (1 : ℝ) else 0))
              ≤ target))
      ≤ Real.exp (-t * lam + t ^ 2 / 2 * (p * (1 - p)
          * ((2 * thr) * (2 * M * (gammaBetween s.Γ T T).card)
              * Real.exp (t * (2 * thr))))) := by
  classical
  set S : Finset (Edge V) := gammaBetween s.Γ T T with hS
  set Phi : (Fin (Fintype.card (Coord V M)) → Bool) → ℝ := fun σ =>
    ∑ e ∈ S, (if σ ∈ survEventLow s M T T thr e then (1 : ℝ) else 0) with hPhi
  have hmeanlb := lowSurvivorCount_expectation_ge s M T T thr hp0 hp1 S hM
  refine le_trans (bernoulliPr_mono hp0 hp1 (?_ :
      (Finset.univ.filter (fun σ => Phi σ ≤ target))
      ⊆ Finset.univ.filter (fun σ => Phi σ ≤ bernoulliExp p Phi - lam))) ?_
  · intro σ hσ
    obtain ⟨-, hle⟩ := Finset.mem_filter.mp hσ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩
  refine le_trans (bernoulliPr_lower_tail hp0 hp1
    (isCoordLipschitz_lowSurvivorCount s M T T thr S) ht) ?_
  refine Real.exp_le_exp.mpr ?_
  have hpp : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  have hC := card_filter_mem_lowKillers_le s M T T hthr S (le_of_eq hS)
  have hQ0 : (0 : ℝ) ≤ (2 * thr) * (2 * M * S.card) := by
    have : (0 : ℝ) ≤ 2 * thr := by linarith
    positivity
  have hsumsq : ∑ j : Fin (Fintype.card (Coord V M)),
      ((S.filter (fun e =>
        j ∈ (lowKillers s M T T thr e).image (coordEquiv V M))).card : ℝ) ^ 2
      ≤ (2 * thr) * (2 * M * S.card) := by
    refine le_trans (sum_sq_le_max_mul_sum Finset.univ _
      (fun j _ => hC j) (fun j _ => Nat.cast_nonneg _)) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have hcount := sum_card_filter_lowKillers_le s M T T thr S hM
    calc ∑ j : Fin (Fintype.card (Coord V M)),
          ((S.filter (fun e =>
            j ∈ (lowKillers s M T T thr e).image (coordEquiv V M))).card : ℝ)
        = ((∑ j : Fin (Fintype.card (Coord V M)),
            (S.filter (fun e =>
              j ∈ (lowKillers s M T T thr e).image
                (coordEquiv V M))).card : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 * M * S.card : ℕ) : ℝ) := by exact_mod_cast hcount
      _ = 2 * M * S.card := by push_cast; ring
  have hinner := sum_sq_exp_le_of_bounded _ (fun j => Nat.cast_nonneg _) hC ht
    hsumsq hQ0
  have hscale := mul_le_mul_of_nonneg_left hinner hpp
  have hscale2 := mul_le_mul_of_nonneg_left hscale
    (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)
  linarith

/-- Kim's `Y⁽²⁾(T)`: the `Γ(T)`-edges killed through a *high* (non-low) pair. -/
noncomputable def killedY2 (s : BlockState V) (M : ℕ) (T : Finset V) (thr : ℝ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) : Finset (Edge V) := by
  classical
  exact (gammaBetween s.Γ T T).filter (fun f =>
    ∃ v ∈ edgeVerts f, ∃ g ∈ lambdaAt s f v,
      ¬ IsLowPair s T T thr g v ∧ σ (padEmb V M g) = true)

/-- Kim's `W_T`: the vertices with many `ℰ`-neighbours inside `T`. -/
noncomputable def bigNbrs (s : BlockState V) (T : Finset V) (thr : ℝ) :
    Finset V := by
  classical
  exact Finset.univ.filter (fun w => thr ≤ ((nbrs s.E w ∩ T).card : ℝ))

lemma mem_bigNbrs {s : BlockState V} {T : Finset V} {thr : ℝ} {w : V} :
    w ∈ bigNbrs s T thr ↔ thr ≤ ((nbrs s.E w ∩ T).card : ℝ) := by
  classical
  show w ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

open scoped Classical in
/-- **Kim (43)**: `Y⁽²⁾(T) ⊆ ⋃_{w ∈ W_T} Γ(N_ℰ(w,T), N_{X'}(w,T))`.

If `f` is killed through the high pair `(e_vw, v)` then `v ∈ T` is an
`X'`-neighbour of `w`, the far endpoint `u` of `f` is an `ℰ`-neighbour of `w`
inside `T`, and being high forces `w ∈ W_T` by (26). -/
lemma killedY2_subset (s : BlockState V) (M : ℕ) (T : Finset V) (thr : ℝ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) :
    killedY2 s M T thr σ
      ⊆ (bigNbrs s T thr).biUnion (fun w =>
          gammaBetween s.Γ (nbrs s.E w ∩ T)
            (nbrs (sampleP s M σ) w ∩ T)) := by
  classical
  intro f hf
  obtain ⟨hfG, v, hvf, g, hgΛ, hhigh, hgsel⟩ := Finset.mem_filter.mp hf
  obtain ⟨hfΓ, hfTT⟩ := Finset.mem_filter.mp hfG
  obtain ⟨⟨hgΓ, hvg⟩, hend⟩ := mem_lambdaAt.mp hgΛ
  set w : V := otherEndOf v g with hw
  have hvfval : v ∈ f.val := mem_edgeVerts.mp hvf
  set u : V := otherEndOf v f with hu
  have hufval : u ∈ f.val := by
    rw [hu, edge_eq_of_otherEndOf hvfval]; simp
  have hnvu : v ≠ u := by
    intro hEq
    exact f.2 (by rw [edge_eq_of_otherEndOf hvfval, ← hu, ← hEq]; simp)
  -- `v` and `u` both lie in `T`, since `f ∈ Γ(T)`
  have hvT : v ∈ T ∧ u ∈ T := by
    obtain ⟨-, x, hxT, y, hyT, hxy, hxf, hyf⟩ := Finset.mem_filter.mp hfG
    have hfxy : f.val = s(x, y) := edge_eq_of_two_mem hxf hyf hxy
    constructor
    · have := hvfval; rw [hfxy, Sym2.mem_iff] at this
      rcases this with h | h
      · rw [h]; exact hxT
      · rw [h]; exact hyT
    · have := hufval; rw [hfxy, Sym2.mem_iff] at this
      rcases this with h | h
      · rw [h]; exact hxT
      · rw [h]; exact hyT
  -- `u` is an `ℰ`-neighbour of `w`, and `v` an `X'`-neighbour of `w`
  have huE : u ∈ nbrs s.E w ∩ T :=
    Finset.mem_inter.mpr ⟨(nbrs_comm s.E u w).mpr hend, hvT.2⟩
  have hgw : w ∈ g.val := by
    rw [hw, edge_eq_of_otherEndOf hvg]; simp
  have hnvw : v ≠ w := by
    intro hEq
    exact g.2 (by rw [edge_eq_of_otherEndOf hvg, ← hw, ← hEq]; simp)
  have hgX : g ∈ sampleP s M σ := Finset.mem_filter.mpr ⟨hgΓ, hgsel⟩
  have hvX : v ∈ nbrs (sampleP s M σ) w ∩ T :=
    Finset.mem_inter.mpr
      ⟨mem_nbrs.mpr ⟨hnvw, g, hgX, hgw, hvg⟩, hvT.1⟩
  -- being high puts `w` into `W_T`
  have hwW : w ∈ bigNbrs s T thr := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hhigh' : thr ≤ ((lambdaAt s g v ∩ gammaBetween s.Γ T T).card : ℝ) := by
      simpa [IsLowPair] using hhigh
    refine le_trans hhigh' ?_
    have := card_lambdaAt_inter_gammaBetween_le s T T g v
    rw [Finset.union_self] at this
    exact_mod_cast this
  exact Finset.mem_biUnion.mpr ⟨w, hwW,
    Finset.mem_filter.mpr ⟨hfΓ, u, huE, v, hvX, Ne.symm hnvu, hufval, hvfval⟩⟩

open scoped Classical in
/-- `N_ℰ(w)` and `N_{X'}(w)` are disjoint: the edge joining `u` to `w` cannot
lie in both `ℰ` and `Γ ⊇ X'`. This is what makes Property 6 — stated for
*disjoint* sets — applicable in §4.8. -/
lemma nbrs_E_disjoint_nbrs_sample (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) (w : V) :
    Disjoint (nbrs s.E w) (nbrs (sampleP s M σ) w) := by
  classical
  rw [Finset.disjoint_left]
  intro u huE huX
  obtain ⟨hne, e, heE, hwe, hue⟩ := mem_nbrs.mp huE
  obtain ⟨-, f, hfX, hwf, huf⟩ := mem_nbrs.mp huX
  have hfΓ : f ∈ s.Γ := sampleP_subset s M σ hfX
  have hef : e = f := Subtype.ext (by
    rw [edge_eq_of_two_mem hwe hue (Ne.symm hne),
      edge_eq_of_two_mem hwf huf (Ne.symm hne)])
  subst hef
  exact Finset.disjoint_left.mp s.hΓ_disjoint_E hfΓ heE

open scoped Classical in
/-- **Kim (44)–(48), the `Σ′/Σ″` split.**

By (43), `|Y⁽²⁾(T)|` is at most the total of `|Γ(N_ℰ(w,T), N_{X'}(w,T))|` over
`w ∈ W_T`. Where both sets are large, Property 6 applies and contributes
`b|A||B|`; elsewhere the trivial bound `|A||B|` is used. -/
lemma card_killedY2_split (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) (T : Finset V) (thr : ℝ)
    {b cut : ℝ}
    (h6 : ∀ A B : Finset V, Disjoint A B → cut ≤ (A.card : ℝ) →
      cut ≤ (B.card : ℝ) →
      ((gammaBetween s.Γ A B).card : ℝ) ≤ b * A.card * B.card) :
    ((killedY2 s M T thr σ).card : ℝ)
      ≤ (∑ w ∈ (bigNbrs s T thr).filter (fun w =>
            ¬ (cut ≤ ((nbrs s.E w ∩ T).card : ℝ)
              ∧ cut ≤ ((nbrs (sampleP s M σ) w ∩ T).card : ℝ))),
            ((nbrs s.E w ∩ T).card : ℝ)
              * ((nbrs (sampleP s M σ) w ∩ T).card : ℝ))
        + b * (∑ w ∈ (bigNbrs s T thr).filter (fun w =>
            cut ≤ ((nbrs s.E w ∩ T).card : ℝ)
              ∧ cut ≤ ((nbrs (sampleP s M σ) w ∩ T).card : ℝ)),
            ((nbrs s.E w ∩ T).card : ℝ)
              * ((nbrs (sampleP s M σ) w ∩ T).card : ℝ)) := by
  classical
  set W : Finset V := bigNbrs s T thr with hW
  set P : V → Prop := fun w => cut ≤ ((nbrs s.E w ∩ T).card : ℝ)
    ∧ cut ≤ ((nbrs (sampleP s M σ) w ∩ T).card : ℝ) with hP
  set G : V → Finset (Edge V) := fun w =>
    gammaBetween s.Γ (nbrs s.E w ∩ T) (nbrs (sampleP s M σ) w ∩ T) with hG
  -- (43): the total is at most the sum over `W`
  have hstep1 : ((killedY2 s M T thr σ).card : ℝ) ≤ ∑ w ∈ W, ((G w).card : ℝ) := by
    have h1 := Finset.card_le_card (killedY2_subset s M T thr σ)
    have h2 := Finset.card_biUnion_le (s := W) (t := G)
    exact_mod_cast le_trans h1 h2
  refine hstep1.trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not W P, Finset.mul_sum,
    add_comm (∑ x ∈ W.filter P, ((G x).card : ℝ))]
  refine add_le_add ?_ ?_
  · -- otherwise: the trivial bound
    refine Finset.sum_le_sum fun w _ => ?_
    exact_mod_cast card_gammaBetween_le' s.Γ (nbrs s.E w ∩ T)
      (nbrs (sampleP s M σ) w ∩ T)
  · -- large-large: Property 6
    refine Finset.sum_le_sum fun w hw => ?_
    obtain ⟨-, hPw⟩ := Finset.mem_filter.mp hw
    have := h6 (nbrs s.E w ∩ T) (nbrs (sampleP s M σ) w ∩ T)
      (Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left
          (nbrs_E_disjoint_nbrs_sample s M σ w))) hPw.1 hPw.2
    calc ((G w).card : ℝ) ≤ b * ((nbrs s.E w ∩ T).card : ℝ)
          * ((nbrs (sampleP s M σ) w ∩ T).card : ℝ) := this
      _ = b * (((nbrs s.E w ∩ T).card : ℝ)
            * ((nbrs (sampleP s M σ) w ∩ T).card : ℝ)) := by ring

open scoped Classical in
/-- **Kim (44)–(48), deterministic form.**

Split `W_T` by whether both `N_ℰ(w,T)` and `N_{X'}(w,T)` exceed `cut`. On the
small side the product is at most `cut·|A(w,T)|` where `A(w,T)` is the larger of
the two, and Lemma 3.5 with `γ = 1` gives `Σ′|A(w,T)| ≤ (3/2)|T|`. On the large
side Property 6 applies, and Lemma 3.5 with the given `γ` gives
`Σ″|N_ℰ(w,T)| ≤ |T| + |T|/(2γ²)`.

The almost-disjointness input is exactly Property 3 for the *stepped* state,
since `N_ℰ(w) ∪ N_{X'}(w)` is the `ℰ'`-neighbourhood of `w`. -/
theorem card_killedY2_le (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) (T : Finset V)
    {β γ : ℝ} (hβ1 : 1 ≤ β) (hγ1 : 1 ≤ γ)
    (hβT : β ≤ Real.sqrt T.card / 2) (hTpos : 0 < T.card)
    {thr : ℝ} (hthr : thr = 2 * β * Real.sqrt T.card)
    {cut : ℝ} (hcut0 : 0 ≤ cut) (hβγT : 2 * β * γ * Real.sqrt T.card ≤ cut)
    {Dx : ℝ} (hDx : ∀ w : V, ((nbrs (sampleP s M σ) w ∩ T).card : ℝ) ≤ Dx)
    {b : ℝ} (hb0 : 0 ≤ b)
    (h6 : ∀ A B : Finset V, Disjoint A B → cut ≤ (A.card : ℝ) →
      cut ≤ (B.card : ℝ) →
      ((gammaBetween s.Γ A B).card : ℝ) ≤ b * A.card * B.card)
    (hcodeg : ∀ v w : V, v ≠ w →
      ((commonNbrs (blockStepP s M σ).E v w).card : ℝ) ≤ β ^ 2) :
    ((killedY2 s M T thr σ).card : ℝ)
      ≤ cut * ((T.card : ℝ) + (T.card : ℝ) / 2)
        + b * Dx * ((T.card : ℝ) + (T.card : ℝ) / (2 * γ ^ 2)) := by
  classical
  set eqv : V ≃ Fin (Fintype.card V) := Fintype.equivFin V with heqv
  -- `N_ℰ(w) ∪ N_{X'}(w)` is the stepped neighbourhood
  have hnb : ∀ w : V, nbrs (blockStepP s M σ).E w
      = nbrs s.E w ∪ nbrs (sampleP s M σ) w := by
    intro w
    rw [blockStepP_E, nbrs_union]

  have hsubE : ∀ w : V, nbrs s.E w ⊆ nbrs (blockStepP s M σ).E w := by
    intro w; rw [hnb w]; exact Finset.subset_union_left
  have hsubX : ∀ w : V, nbrs (sampleP s M σ) w
      ⊆ nbrs (blockStepP s M σ).E w := by
    intro w; rw [hnb w]; exact Finset.subset_union_right
  -- the almost-disjointness input, for any pair of stepped neighbourhoods
  have hpair : ∀ (u u' : V), u ≠ u' → ∀ (X Y : Finset V),
      X ⊆ nbrs (blockStepP s M σ).E u → Y ⊆ nbrs (blockStepP s M σ).E u' →
      ((X ∩ Y).card : ℝ) ≤ β ^ 2 := by
    intro u u' huu' X Y hX hY
    refine le_trans ?_ (hcodeg u u' huu')
    have hsub : X ∩ Y ⊆ commonNbrs (blockStepP s M σ).E u u' := by
      rw [commonNbrs_eq_inter]
      exact Finset.inter_subset_inter hX hY
    exact_mod_cast Finset.card_le_card hsub
  set P : V → Prop := fun w => cut ≤ ((nbrs s.E w ∩ T).card : ℝ)
    ∧ cut ≤ ((nbrs (sampleP s M σ) w ∩ T).card : ℝ) with hPdef
  set W : Finset V := bigNbrs s T thr with hWdef
  -- the larger of the two neighbourhoods inside `T`
  set Amax : V → Finset V := fun w =>
    if ((nbrs (sampleP s M σ) w ∩ T).card : ℝ) ≤ ((nbrs s.E w ∩ T).card : ℝ)
      then nbrs s.E w ∩ T else nbrs (sampleP s M σ) w ∩ T with hAmax
  have hAmaxsub : ∀ w : V, Amax w ⊆ T := by
    intro w; rw [hAmax]; dsimp only
    split <;> exact Finset.inter_subset_right
  have hAmaxstep : ∀ w : V, Amax w ⊆ nbrs (blockStepP s M σ).E w := by
    intro w; rw [hAmax]; dsimp only
    split_ifs
    · exact Finset.Subset.trans Finset.inter_subset_left (hsubE w)
    · exact Finset.Subset.trans Finset.inter_subset_left (hsubX w)
  have hAmaxge : ∀ w : V, ((nbrs s.E w ∩ T).card : ℝ) ≤ ((Amax w).card : ℝ) := by
    intro w; rw [hAmax]; dsimp only
    split_ifs with h
    · exact le_refl _
    · push_neg at h; exact h.le
  have hWmem : ∀ w ∈ W, thr ≤ ((nbrs s.E w ∩ T).card : ℝ) := by
    intro w hw
    exact mem_bigNbrs.mp hw
  -- Lemma 3.5 for a family indexed through `eqv`
  have hL35 : ∀ (s₀ : Finset V) (F : V → Finset V) {γ₀ : ℝ}, 1 ≤ γ₀ →
      (∀ w : V, F w ⊆ T) → (∀ w : V, F w ⊆ nbrs (blockStepP s M σ).E w) →
      (∀ w ∈ s₀, 2 * β * γ₀ * Real.sqrt T.card ≤ ((F w).card : ℝ)) →
      ∑ w ∈ s₀, ((F w).card : ℝ)
        ≤ (T.card : ℝ) + (T.card : ℝ) / (2 * γ₀ ^ 2) := by
    intro s₀ F γ₀ hγ₀ hFT hFstep hFlarge
    have hinj : ∀ x ∈ s₀, ∀ y ∈ s₀, eqv x = eqv y → x = y :=
      fun x _ y _ h => eqv.injective h
    have hre : ∑ w ∈ s₀, ((F w).card : ℝ)
        = ∑ i ∈ s₀.image eqv, ((F (eqv.symm i)).card : ℝ) := by
      rw [Finset.sum_image hinj]
      exact Finset.sum_congr rfl fun w _ => by rw [Equiv.symm_apply_apply]
    rw [hre]
    refine almost_disjoint_sum_card_le T (s₀.image eqv)
      (fun i => F (eqv.symm i)) (fun i _ => hFT _) hβ1 hγ₀ hβT hTpos
      ?_ ?_
    · intro i hi
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hi
      simpa using hFlarge w hw
    · intro i _ j _ hij
      refine hpair (eqv.symm i) (eqv.symm j) ?_ _ _ (hFstep _) (hFstep _)
      intro hc
      exact hij (by rw [← Equiv.apply_symm_apply eqv i, hc,
        Equiv.apply_symm_apply])
  refine (card_killedY2_split s M σ T thr h6).trans ?_
  refine add_le_add ?_ ?_
  · -- small side
    have hterm : ∀ w ∈ W.filter (fun w => ¬ P w),
        ((nbrs s.E w ∩ T).card : ℝ) * ((nbrs (sampleP s M σ) w ∩ T).card : ℝ)
          ≤ cut * ((Amax w).card : ℝ) := by
      intro w hw
      obtain ⟨-, hnp⟩ := Finset.mem_filter.mp hw
      set x : ℝ := ((nbrs s.E w ∩ T).card : ℝ) with hx
      set y : ℝ := ((nbrs (sampleP s M σ) w ∩ T).card : ℝ) with hy
      have hor : x < cut ∨ y < cut := by
        rcases not_and_or.mp hnp with h | h
        · exact Or.inl (not_le.mp h)
        · exact Or.inr (not_le.mp h)
      have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
      have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg _
      rw [hAmax]; dsimp only
      by_cases hle : y ≤ x
      · rw [if_pos hle]
        have hylt : y < cut := by rcases hor with h | h <;> linarith
        nlinarith [hx0, hy0, hylt]
      · push_neg at hle
        rw [if_neg (not_le.mpr hle)]
        have hxlt : x < cut := by rcases hor with h | h <;> linarith
        nlinarith [hx0, hy0, hxlt]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hbound : ∑ w ∈ W.filter (fun w => ¬ P w), ((Amax w).card : ℝ)
        ≤ (T.card : ℝ) + (T.card : ℝ) / (2 * (1 : ℝ) ^ 2) := by
      refine hL35 _ Amax le_rfl hAmaxsub hAmaxstep ?_
      intro w hw
      have hwW : w ∈ W := (Finset.mem_filter.mp hw).1
      have := hWmem w hwW
      rw [hthr] at this
      calc 2 * β * (1 : ℝ) * Real.sqrt T.card = 2 * β * Real.sqrt T.card := by
            ring
        _ ≤ ((nbrs s.E w ∩ T).card : ℝ) := this
        _ ≤ ((Amax w).card : ℝ) := hAmaxge w
    have hsimp : (T.card : ℝ) + (T.card : ℝ) / (2 * (1 : ℝ) ^ 2)
        = (T.card : ℝ) + (T.card : ℝ) / 2 := by norm_num
    rw [hsimp] at hbound
    exact mul_le_mul_of_nonneg_left hbound hcut0
  · -- large side
    have hterm : ∀ w ∈ W.filter P,
        ((nbrs s.E w ∩ T).card : ℝ) * ((nbrs (sampleP s M σ) w ∩ T).card : ℝ)
          ≤ Dx * ((nbrs s.E w ∩ T).card : ℝ) := by
      intro w _
      have hx0 : (0 : ℝ) ≤ ((nbrs s.E w ∩ T).card : ℝ) := Nat.cast_nonneg _
      nlinarith [hDx w, hx0]
    have hDx0 : (0 : ℝ) ≤ Dx := by
      obtain ⟨v, -⟩ := Finset.card_pos.mp hTpos
      have hv := hDx v
      have h0 : (0 : ℝ) ≤ ((nbrs (sampleP s M σ) v ∩ T).card : ℝ) :=
        Nat.cast_nonneg _
      linarith
    have hsum : ∑ w ∈ W.filter P, ((nbrs s.E w ∩ T).card : ℝ)
        ≤ (T.card : ℝ) + (T.card : ℝ) / (2 * γ ^ 2) := by
      refine hL35 _ (fun w => nbrs s.E w ∩ T) hγ1
        (fun w => Finset.inter_subset_right)
        (fun w => Finset.Subset.trans Finset.inter_subset_left (hsubE w)) ?_
      intro w hw
      exact le_trans hβγT (Finset.mem_filter.mp hw).2.1
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hb0) ?_
    rw [← Finset.mul_sum, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hsum (mul_nonneg hb0 hDx0)

open scoped Classical in
/-- **Kim (54), deterministic form.**  The truncation excess

`Φ⁽⁴⁾(T) = Σ_{v : |N_{X'}(v,T)| ≥ h} |Γ(N_{X'}(v,T))|`

is bounded by splitting at `cut`: below it the trivial `|Γ(A)| ≤ C(|A|,2)`
gives `(cut/2)|A|`, above it Property 6's unipartite clause gives
`(b·Dx/2)|A|`, and Lemma 3.5 caps `Σ|A|` by `(3/2)|T|` and `(1+1/(2γ²))|T|`
respectively.  This replaces the cruder route of demanding that the truncation
never bite, which cannot be made to beat the `C(n,t)` union bound at any `h`. -/
theorem card_phi4_le (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) (T : Finset V)
    {β γ : ℝ} (hβ1 : 1 ≤ β) (hγ1 : 1 ≤ γ)
    (hβT : β ≤ Real.sqrt T.card / 2) (hTpos : 0 < T.card)
    (h : ℕ) (hhge : 2 * β * Real.sqrt T.card ≤ (h : ℝ))
    {cut : ℝ} (hcut0 : 0 ≤ cut) (hβγT : 2 * β * γ * Real.sqrt T.card ≤ cut)
    {Dx : ℝ} (hDx : ∀ v : V, ((nbrs (sampleP s M σ) v ∩ T).card : ℝ) ≤ Dx)
    {b : ℝ} (hb0 : 0 ≤ b)
    (hself : ∀ A : Finset V, cut ≤ (A.card : ℝ) →
      ((gammaBetween s.Γ A A).card : ℝ) ≤ b * (A.card.choose 2 : ℕ))
    (hcodeg : ∀ v w : V, v ≠ w →
      ((commonNbrs (blockStepP s M σ).E v w).card : ℝ) ≤ β ^ 2) :
    ∑ v ∈ Finset.univ.filter
        (fun v => h ≤ (nbrs (sampleP s M σ) v ∩ T).card),
        ((gammaBetween s.Γ (nbrs (sampleP s M σ) v ∩ T)
          (nbrs (sampleP s M σ) v ∩ T)).card : ℝ)
      ≤ (cut / 2) * ((T.card : ℝ) + (T.card : ℝ) / 2)
        + (b * Dx / 2) * ((T.card : ℝ) + (T.card : ℝ) / (2 * γ ^ 2)) := by
  classical
  set eqv : V ≃ Fin (Fintype.card V) := Fintype.equivFin V with heqv
  set A : V → Finset V := fun v => nbrs (sampleP s M σ) v ∩ T with hA
  have hnb : ∀ w : V, nbrs (blockStepP s M σ).E w
      = nbrs s.E w ∪ nbrs (sampleP s M σ) w := by
    intro w; rw [blockStepP_E, nbrs_union]
  have hAT : ∀ v : V, A v ⊆ T := fun v => Finset.inter_subset_right
  have hAstep : ∀ v : V, A v ⊆ nbrs (blockStepP s M σ).E v := by
    intro v
    rw [hnb v]
    exact Finset.Subset.trans Finset.inter_subset_left Finset.subset_union_right
  have hpair : ∀ (u u' : V), u ≠ u' →
      ((A u ∩ A u').card : ℝ) ≤ β ^ 2 := by
    intro u u' huu'
    refine le_trans ?_ (hcodeg u u' huu')
    have hsub : A u ∩ A u' ⊆ commonNbrs (blockStepP s M σ).E u u' := by
      rw [commonNbrs_eq_inter]
      exact Finset.inter_subset_inter (hAstep u) (hAstep u')
    exact_mod_cast Finset.card_le_card hsub
  have hL35 : ∀ (s₀ : Finset V) {γ₀ : ℝ}, 1 ≤ γ₀ →
      (∀ w ∈ s₀, 2 * β * γ₀ * Real.sqrt T.card ≤ ((A w).card : ℝ)) →
      ∑ w ∈ s₀, ((A w).card : ℝ)
        ≤ (T.card : ℝ) + (T.card : ℝ) / (2 * γ₀ ^ 2) := by
    intro s₀ γ₀ hγ₀ hFlarge
    have hinj : ∀ x ∈ s₀, ∀ y ∈ s₀, eqv x = eqv y → x = y :=
      fun x _ y _ hxy => eqv.injective hxy
    have hre : ∑ w ∈ s₀, ((A w).card : ℝ)
        = ∑ i ∈ s₀.image eqv, ((A (eqv.symm i)).card : ℝ) := by
      rw [Finset.sum_image hinj]
      exact Finset.sum_congr rfl fun w _ => by rw [Equiv.symm_apply_apply]
    rw [hre]
    refine almost_disjoint_sum_card_le T (s₀.image eqv)
      (fun i => A (eqv.symm i)) (fun i _ => hAT _) hβ1 hγ₀ hβT hTpos ?_ ?_
    · intro i hi
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hi
      simpa using hFlarge w hw
    · intro i _ j _ hij
      refine hpair (eqv.symm i) (eqv.symm j) ?_
      intro hc
      exact hij (by rw [← Equiv.apply_symm_apply eqv i, hc,
        Equiv.apply_symm_apply])
  set S : Finset V := Finset.univ.filter (fun v => h ≤ (A v).card) with hS
  have hSge : ∀ v ∈ S, 2 * β * Real.sqrt T.card ≤ ((A v).card : ℝ) := by
    intro v hv
    have hnat : h ≤ (A v).card := (Finset.mem_filter.mp hv).2
    have : (h : ℝ) ≤ ((A v).card : ℝ) := by exact_mod_cast hnat
    linarith [hhge]
  have hDx0 : (0 : ℝ) ≤ Dx := by
    obtain ⟨v, -⟩ := Finset.card_pos.mp hTpos
    have := hDx v
    have h0 : (0 : ℝ) ≤ ((A v).card : ℝ) := Nat.cast_nonneg _
    linarith
  have hchoose : ∀ (X : Finset V), ((X.card.choose 2 : ℕ) : ℝ)
      ≤ ((X.card : ℝ)) ^ 2 / 2 := by
    intro X
    rw [Nat.cast_choose_two]
    have h0 : (0 : ℝ) ≤ (X.card : ℝ) := Nat.cast_nonneg _
    nlinarith [h0]
  have hsplit : ∑ v ∈ S, ((gammaBetween s.Γ (A v) (A v)).card : ℝ)
      = (∑ v ∈ S.filter (fun v => ((A v).card : ℝ) < cut),
            ((gammaBetween s.Γ (A v) (A v)).card : ℝ))
        + ∑ v ∈ S.filter (fun v => ¬ ((A v).card : ℝ) < cut),
            ((gammaBetween s.Γ (A v) (A v)).card : ℝ) :=
    (Finset.sum_filter_add_sum_filter_not S _ _).symm
  rw [hsplit]
  refine add_le_add ?_ ?_
  · -- below the Property-6 threshold: the trivial bound
    have hterm : ∀ v ∈ S.filter (fun v => ((A v).card : ℝ) < cut),
        ((gammaBetween s.Γ (A v) (A v)).card : ℝ)
          ≤ (cut / 2) * ((A v).card : ℝ) := by
      intro v hv
      have hlt : ((A v).card : ℝ) < cut := (Finset.mem_filter.mp hv).2
      have h1 : ((gammaBetween s.Γ (A v) (A v)).card : ℝ)
          ≤ ((A v).card.choose 2 : ℕ) := by
        exact_mod_cast card_gammaBetween_self_le s.Γ (A v)
      have h0 : (0 : ℝ) ≤ ((A v).card : ℝ) := Nat.cast_nonneg _
      nlinarith [h1, hchoose (A v), hlt, h0]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hbound : ∑ v ∈ S.filter (fun v => ((A v).card : ℝ) < cut),
          ((A v).card : ℝ)
        ≤ (T.card : ℝ) + (T.card : ℝ) / (2 * (1 : ℝ) ^ 2) := by
      refine hL35 _ le_rfl ?_
      intro w hw
      have := hSge w (Finset.mem_filter.mp hw).1
      linarith
    have hsimp : (T.card : ℝ) + (T.card : ℝ) / (2 * (1 : ℝ) ^ 2)
        = (T.card : ℝ) + (T.card : ℝ) / 2 := by norm_num
    rw [hsimp] at hbound
    exact mul_le_mul_of_nonneg_left hbound (by linarith)
  · -- above the threshold: Property 6's unipartite clause
    have hterm : ∀ v ∈ S.filter (fun v => ¬ ((A v).card : ℝ) < cut),
        ((gammaBetween s.Γ (A v) (A v)).card : ℝ)
          ≤ (b * Dx / 2) * ((A v).card : ℝ) := by
      intro v hv
      have hge : cut ≤ ((A v).card : ℝ) := not_lt.mp (Finset.mem_filter.mp hv).2
      have h1 := hself (A v) hge
      have h0 : (0 : ℝ) ≤ ((A v).card : ℝ) := Nat.cast_nonneg _
      have h2 : ((A v).card.choose 2 : ℕ) ≤ ((A v).card : ℝ) ^ 2 / 2 :=
        hchoose (A v)
      have h3 : ((A v).card : ℝ) ^ 2 / 2 ≤ Dx / 2 * ((A v).card : ℝ) := by
        nlinarith [hDx v, h0]
      nlinarith [h1, h2, h3, hb0, h0]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hbound : ∑ v ∈ S.filter (fun v => ¬ ((A v).card : ℝ) < cut),
          ((A v).card : ℝ)
        ≤ (T.card : ℝ) + (T.card : ℝ) / (2 * γ ^ 2) := by
      refine hL35 _ hγ1 ?_
      intro w hw
      have hge : cut ≤ ((A w).card : ℝ) := not_lt.mp (Finset.mem_filter.mp hw).2
      linarith [hβγT]
    exact mul_le_mul_of_nonneg_left hbound (by positivity)

open scoped Classical in
lemma mem_sampleP {s : BlockState V} {M : ℕ}
    {σ : Fin (Fintype.card (Coord V M)) → Bool} {e : Edge V} :
    e ∈ sampleP s M σ ↔ e ∈ s.Γ ∧ σ (padEmb V M e) = true := by
  classical
  show e ∈ Finset.filter _ _ ↔ _
  rw [Finset.mem_filter]
  exact Iff.rfl

open scoped Classical in
/-- The `Γ`-edges from `v` into `T`. -/
noncomputable def edgesToSet (s : BlockState V) (v : V) (T : Finset V) :
    Finset (Edge V) := by
  classical
  exact s.Γ.filter (fun e => v ∈ e.val ∧ otherEndOf v e ∈ T)

lemma mem_edgesToSet {s : BlockState V} {v : V} {T : Finset V} {e : Edge V} :
    e ∈ edgesToSet s v T ↔ e ∈ s.Γ ∧ (v ∈ e.val ∧ otherEndOf v e ∈ T) := by
  classical
  show e ∈ Finset.filter _ _ ↔ _
  rw [Finset.mem_filter]

open scoped Classical in
/-- **Kim's coordinate block for `v` relative to `T`**: the sampling trials of
the `Γ`-edges joining `v` to `T`. These are exactly the coordinates that
`N_{X'}(v) ∩ T` depends on. -/
noncomputable def zBlock (s : BlockState V) (M : ℕ) (v : V) (T : Finset V) :
    Finset (Fin (Fintype.card (Coord V M))) :=
  (edgesToSet s v T).image (padEmb V M)

/-- **The blocks of distinct vertices outside `T` are disjoint.**

An edge in both blocks joins `v` to `T` and `v'` to `T`, hence is `e_{vv'}`,
forcing `v' ∈ T`. This is exactly why Kim separates `v ∈ T` from `v ∉ T`. -/
lemma zBlock_disjoint (s : BlockState V) (M : ℕ) (T : Finset V) {v v' : V}
    (hv' : v' ∉ T) (hne : v ≠ v') :
    Disjoint (zBlock s M v T) (zBlock s M v' T) := by
  classical
  rw [Finset.disjoint_left]
  intro j hj hj'
  obtain ⟨e, he, hje⟩ := Finset.mem_image.mp hj
  obtain ⟨e', he', hje'⟩ := Finset.mem_image.mp hj'
  have heq : e = e' := (padEmb V M).injective (hje.trans hje'.symm)
  subst heq
  obtain ⟨-, hve, hote⟩ := mem_edgesToSet.mp he
  obtain ⟨-, hv'e, -⟩ := mem_edgesToSet.mp he'
  have hoth : v' = otherEndOf v e :=
    eq_otherEndOf_of_mem hve hv'e (Ne.symm hne)
  rw [← hoth] at hote
  exact hv' hote

open scoped Classical in
/-- **The sampled neighbourhood of `v` inside `T` depends only on `v`'s
block.** -/
lemma nbrs_sample_inter_congr (s : BlockState V) (M : ℕ) (v : V) (T : Finset V)
    {σ τ : Fin (Fintype.card (Coord V M)) → Bool}
    (h : ∀ j ∈ zBlock s M v T, σ j = τ j) :
    nbrs (sampleP s M σ) v ∩ T = nbrs (sampleP s M τ) v ∩ T := by
  classical
  have hone : ∀ (σ' τ' : Fin (Fintype.card (Coord V M)) → Bool),
      (∀ j ∈ zBlock s M v T, σ' j = τ' j) →
      nbrs (sampleP s M σ') v ∩ T ⊆ nbrs (sampleP s M τ') v ∩ T := by
    intro σ' τ' h' u hu
    obtain ⟨hun, huT⟩ := Finset.mem_inter.mp hu
    obtain ⟨hne, e, he, hve, hue⟩ := mem_nbrs.mp hun
    obtain ⟨heΓ, hsel⟩ := mem_sampleP.mp he
    have hoth : u = otherEndOf v e := eq_otherEndOf_of_mem hve hue hne
    have hmem : e ∈ edgesToSet s v T :=
      mem_edgesToSet.mpr ⟨heΓ, hve, by rw [← hoth]; exact huT⟩
    have hjb : padEmb V M e ∈ zBlock s M v T :=
      Finset.mem_image.mpr ⟨e, hmem, rfl⟩
    refine Finset.mem_inter.mpr ⟨mem_nbrs.mpr ⟨hne, e, ?_, hve, hue⟩, huT⟩
    exact mem_sampleP.mpr ⟨heΓ, by rw [← h' _ hjb]; exact hsel⟩
  exact Finset.Subset.antisymm (hone σ τ h)
    (hone τ σ (fun j hj => (h j hj).symm))

open scoped Classical in
/-- `|N_{X'}(v) ∩ T|` is at most the number of `true` coordinates in `v`'s
block. -/
lemma card_nbrs_sample_inter_le (s : BlockState V) (M : ℕ) (v : V)
    (T : Finset V) (σ : Fin (Fintype.card (Coord V M)) → Bool) :
    ((nbrs (sampleP s M σ) v ∩ T).card : ℝ)
      ≤ ∑ j ∈ zBlock s M v T, (if σ j = true then (1 : ℝ) else 0) := by
  classical
  have hsum : ∑ j ∈ zBlock s M v T, (if σ j = true then (1 : ℝ) else 0)
      = (((zBlock s M v T).filter (fun j => σ j = true)).card : ℝ) := by
    rw [Finset.card_filter]; push_cast; rfl
  have hfilter : (zBlock s M v T).filter (fun j => σ j = true)
      = ((edgesToSet s v T).filter (fun e => σ (padEmb V M e) = true)).image
        (padEmb V M) := by
    ext j
    simp only [Finset.mem_filter, zBlock, Finset.mem_image]
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hσ⟩
      exact ⟨e, ⟨he, hσ⟩, rfl⟩
    · rintro ⟨e, ⟨he1, he2⟩, rfl⟩
      exact ⟨⟨e, he1, rfl⟩, he2⟩
  have hsub : nbrs (sampleP s M σ) v ∩ T
      ⊆ ((edgesToSet s v T).filter
          (fun e => σ (padEmb V M e) = true)).image (otherEndOf v) := by
    intro u hu
    obtain ⟨hun, huT⟩ := Finset.mem_inter.mp hu
    obtain ⟨hne, e, he, hve, hue⟩ := mem_nbrs.mp hun
    obtain ⟨heΓ, hsel⟩ := mem_sampleP.mp he
    have hoth : u = otherEndOf v e := eq_otherEndOf_of_mem hve hue hne
    refine Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨?_, hsel⟩, hoth.symm⟩
    exact mem_edgesToSet.mpr ⟨heΓ, hve, by rw [← hoth]; exact huT⟩
  rw [hsum, hfilter,
    Finset.card_image_of_injective _ (padEmb V M).injective]
  exact_mod_cast le_trans (Finset.card_le_card hsub) Finset.card_image_le

/-- Kim's `Z'`: the `Γ`-edges closing a triangle with *two selected* edges. -/
noncomputable def killedZpure (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) : Finset (Edge V) := by
  classical
  exact s.Γ.filter (fun e => ∃ f ∈ sampleP s M σ, ∃ g ∈ sampleP s M σ,
    IsTriangle e f g)

open scoped Classical in
/-- The crude removal set splits into Kim's `Y'` and `Z'`.

A triangle on `e ∈ Γ` with both other edges in `ℰ` is impossible (that is the
`BlockState` invariant); one `ℰ`-edge and one selected edge is exactly a
selected `Λ`-partner, i.e. `Y'`; two selected edges is `Z'`. -/
lemma killedZ_subset (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) :
    killedZ s M σ ⊆ killedY s M σ ∪ killedZpure s M σ := by
  classical
  intro e he
  obtain ⟨heΓ, htri⟩ := Finset.mem_filter.mp he
  push_neg at htri
  obtain ⟨f, hfEX, g, hgEX, htri⟩ := htri
  -- a selected `Λ`-partner puts `e` into `Y'`
  have hY : ∀ (f' g' : Edge V), f' ∈ s.E → g' ∈ sampleP s M σ →
      IsTriangle e f' g' → e ∈ killedY s M σ := by
    intro f' g' hf' hg' htri'
    obtain ⟨a, b, c, hab, hbc, hac, heq, feq, geq⟩ := htri'
    -- `e = {a,b}`, `f' = {b,c} ∈ ℰ`, `g' = {a,c}` selected; so `g' ∈ N_Λ(e,a)`
    have hae : a ∈ e.val := by rw [heq]; simp
    have hag' : a ∈ g'.val := by rw [geq]; simp
    have hg'Γ : g' ∈ s.Γ := (Finset.mem_filter.mp hg').1
    have hother_e : otherEndOf a e = b := by
      have hspec : e.val = s(a, otherEndOf a e) := edge_eq_of_otherEndOf hae
      rw [heq] at hspec
      exact ((Sym2.congr_right).mp hspec).symm
    have hother_g : otherEndOf a g' = c := by
      have hspec : g'.val = s(a, otherEndOf a g') := edge_eq_of_otherEndOf hag'
      rw [geq] at hspec
      exact ((Sym2.congr_right).mp hspec).symm
    have hmemΛ : g' ∈ lambdaAt s e a := by
      refine mem_lambdaAt.mpr ⟨⟨hg'Γ, hag'⟩, ?_⟩
      rw [hother_g, hother_e]
      exact mem_nbrs.mpr ⟨hbc.symm, f', hf', by rw [feq]; simp, by rw [feq]; simp⟩
    refine mem_killedY.mpr ⟨heΓ, Sum.inl g', ?_, (Finset.mem_filter.mp hg').2⟩
    exact mem_lambdaStar.mpr ⟨a, mem_edgeVerts.mpr hae,
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨g', hmemΛ, rfl⟩)⟩
  rcases Finset.mem_union.mp hfEX with hfE | hfX
  · rcases Finset.mem_union.mp hgEX with hgE | hgX
    · exact absurd htri (s.hΓ_no_triangle e heΓ f hfE g hgE)
    · exact Finset.mem_union_left _ (hY f g hfE hgX htri)
  · rcases Finset.mem_union.mp hgEX with hgE | hgX
    · exact Finset.mem_union_left _ (hY g f hgE hfX htri.swap23)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨heΓ, f, hfX, g, hgX, htri⟩)

open scoped Classical in
/-- **Kim's `Z' ∩ Γ(T) = ⋃_v Γ(N_{X'}(v,T))`**, the decomposition (45) rests on.
An edge closing a triangle with two selected edges has both endpoints among the
`X'`-neighbours of the triangle's third vertex. -/
lemma killedZpure_inter_gammaT_subset (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) (T : Finset V) :
    killedZpure s M σ ∩ gammaBetween s.Γ T T
      ⊆ (Finset.univ : Finset V).biUnion (fun v =>
          gammaBetween s.Γ (nbrs (sampleP s M σ) v ∩ T)
            (nbrs (sampleP s M σ) v ∩ T)) := by
  classical
  intro e he
  obtain ⟨heZ, heG⟩ := Finset.mem_inter.mp he
  obtain ⟨heΓ, f, hfX, g, hgX, htri⟩ := Finset.mem_filter.mp heZ
  obtain ⟨a, b, c, hab, hbc, hac, heq, feq, geq⟩ := htri
  obtain ⟨-, x, hxT, y, hyT, hxy, hxe, hye⟩ := Finset.mem_filter.mp heG
  -- `e = {a,b}` and `{x,y} = {a,b}`, so both `a, b ∈ T`
  have hexy : e.val = s(x, y) := edge_eq_of_two_mem hxe hye hxy
  have hae : a ∈ e.val := by rw [heq]; simp
  have hbe : b ∈ e.val := by rw [heq]; simp
  have hmemT : ∀ z : V, z ∈ e.val → z ∈ T := by
    intro z hz
    rw [hexy, Sym2.mem_iff] at hz
    rcases hz with h | h
    · rw [h]; exact hxT
    · rw [h]; exact hyT
  have haX : a ∈ nbrs (sampleP s M σ) c ∩ T :=
    Finset.mem_inter.mpr
      ⟨mem_nbrs.mpr ⟨hac, g, hgX, by rw [geq]; simp, by rw [geq]; simp⟩,
       hmemT a hae⟩
  have hbX : b ∈ nbrs (sampleP s M σ) c ∩ T :=
    Finset.mem_inter.mpr
      ⟨mem_nbrs.mpr ⟨hbc, f, hfX, by rw [feq]; simp, by rw [feq]; simp⟩,
       hmemT b hbe⟩
  exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _,
    Finset.mem_filter.mpr ⟨heΓ, a, haX, b, hbX, hab, hae, hbe⟩⟩

/-- A fixed linear ordering of `V`, used to make truncation *stable*. -/
noncomputable def vrank (x : V) : ℕ := ((Fintype.equivFin V) x : ℕ)

lemma vrank_injective : Function.Injective (vrank : V → ℕ) := by
  intro x y hxy
  have h : (Fintype.equivFin V) x = (Fintype.equivFin V) y := Fin.ext hxy
  exact (Fintype.equivFin V).injective h

open scoped Classical in
/-- Kim's `N̂`: the `h` elements of `S` of smallest `vrank`.

Order-stability is essential: adding one vertex to `S` changes `truncTo S h` by
at most one element, which is what bounds the Lipschitz constants of `Φ⁽⁵⁾` in
§4.8. A merely *chosen* `h`-subset would not do — one coordinate flip could
replace it wholesale. -/
noncomputable def truncTo (S : Finset V) (h : ℕ) : Finset V := by
  classical
  exact S.filter (fun x => (S.filter (fun y => vrank y < vrank x)).card < h)

lemma mem_truncTo {S : Finset V} {h : ℕ} {x : V} :
    x ∈ truncTo S h ↔
      x ∈ S ∧ (S.filter (fun y => vrank y < vrank x)).card < h := by
  classical
  show x ∈ Finset.filter _ _ ↔ _
  rw [Finset.mem_filter]

lemma truncTo_subset (S : Finset V) (h : ℕ) : truncTo S h ⊆ S :=
  fun _ hx => (mem_truncTo.mp hx).1

/-- The predecessor count is injective on `S`. -/
lemma predCount_injOn (S : Finset V) : ∀ x ∈ S, ∀ y ∈ S,
    (S.filter (fun z => vrank z < vrank x)).card
      = (S.filter (fun z => vrank z < vrank y)).card → x = y := by
  classical
  intro x hx y hy hcard
  by_contra hne
  have hrne : vrank x ≠ vrank y := fun hc => hne (vrank_injective hc)
  rcases lt_or_gt_of_ne hrne with hlt | hlt
  · have hss : S.filter (fun z => vrank z < vrank x)
        ⊂ S.filter (fun z => vrank z < vrank y) := by
      refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨x, ?_, ?_⟩
      · intro z hz
        obtain ⟨hzS, hzr⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hzS, lt_trans hzr hlt⟩
      · exact Finset.mem_filter.mpr ⟨hx, hlt⟩
      · intro hc
        exact absurd (Finset.mem_filter.mp hc).2 (lt_irrefl _)
    exact absurd hcard (ne_of_lt (Finset.card_lt_card hss))
  · have hss : S.filter (fun z => vrank z < vrank y)
        ⊂ S.filter (fun z => vrank z < vrank x) := by
      refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨y, ?_, ?_⟩
      · intro z hz
        obtain ⟨hzS, hzr⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hzS, lt_trans hzr hlt⟩
      · exact Finset.mem_filter.mpr ⟨hy, hlt⟩
      · intro hc
        exact absurd (Finset.mem_filter.mp hc).2 (lt_irrefl _)
    exact absurd hcard.symm (ne_of_lt (Finset.card_lt_card hss))

lemma truncTo_card_le (S : Finset V) (h : ℕ) : (truncTo S h).card ≤ h := by
  classical
  have hmap : ∀ x ∈ truncTo S h,
      (S.filter (fun z => vrank z < vrank x)).card ∈ Finset.range h := by
    intro x hx
    exact Finset.mem_range.mpr (mem_truncTo.mp hx).2
  have hinj : ∀ x ∈ truncTo S h, ∀ y ∈ truncTo S h,
      (S.filter (fun z => vrank z < vrank x)).card
        = (S.filter (fun z => vrank z < vrank y)).card → x = y := by
    intro x hx y hy hc
    exact predCount_injOn S x (mem_truncTo.mp hx).1 y (mem_truncTo.mp hy).1 hc
  calc (truncTo S h).card
      ≤ (Finset.range h).card :=
        Finset.card_le_card_of_injOn _ hmap (fun x hx y hy hc =>
          hinj x hx y hy hc)
    _ = h := Finset.card_range h

lemma truncTo_eq_self {S : Finset V} {h : ℕ} (hh : ¬ h ≤ S.card) :
    truncTo S h = S := by
  classical
  refine Finset.Subset.antisymm (truncTo_subset S h) fun x hx => ?_
  refine mem_truncTo.mpr ⟨hx, ?_⟩
  have hle : (S.filter (fun z => vrank z < vrank x)).card ≤ S.card :=
    Finset.card_filter_le _ _
  omega

open scoped Classical in
/-- **Stability, first half.** -/
lemma truncTo_insert_subset (S : Finset V) (h : ℕ) (u : V) :
    truncTo (insert u S) h ⊆ insert u (truncTo S h) := by
  classical
  intro x hx
  obtain ⟨hxS, hxc⟩ := mem_truncTo.mp hx
  by_cases hxu : x = u
  · subst hxu; exact Finset.mem_insert_self _ _
  · refine Finset.mem_insert_of_mem (mem_truncTo.mpr ⟨?_, ?_⟩)
    · rcases Finset.mem_insert.mp hxS with rfl | h'
      · exact absurd rfl hxu
      · exact h'
    · refine lt_of_le_of_lt ?_ hxc
      exact Finset.card_le_card (Finset.filter_subset_filter _
        (Finset.subset_insert u S))

open scoped Classical in
/-- **Stability, second half.** -/
lemma card_truncTo_sdiff_insert (S : Finset V) (h : ℕ) (u : V) :
    (truncTo S h \ truncTo (insert u S) h).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr fun x hx y hy => ?_
  obtain ⟨hxT, hxN⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hyT, hyN⟩ := Finset.mem_sdiff.mp hy
  obtain ⟨hxS, hxc⟩ := mem_truncTo.mp hxT
  obtain ⟨hyS, hyc⟩ := mem_truncTo.mp hyT
  -- membership in the inserted set fails only through the count
  have hstep : ∀ z : V, z ∈ S → (S.filter (fun w => vrank w < vrank z)).card < h →
      z ∉ truncTo (insert u S) h →
      (S.filter (fun w => vrank w < vrank z)).card = h - 1 ∧ 1 ≤ h := by
    intro z hzS hzc hznot
    have hsub : (insert u S).filter (fun w => vrank w < vrank z)
        ⊆ insert u (S.filter (fun w => vrank w < vrank z)) := by
      intro w hw
      obtain ⟨hwS, hwr⟩ := Finset.mem_filter.mp hw
      rcases Finset.mem_insert.mp hwS with rfl | h'
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h', hwr⟩)
    have hle : ((insert u S).filter (fun w => vrank w < vrank z)).card
        ≤ (S.filter (fun w => vrank w < vrank z)).card + 1 :=
      le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)
    have hge : ¬ ((insert u S).filter (fun w => vrank w < vrank z)).card < h := by
      intro hc
      exact hznot (mem_truncTo.mpr ⟨Finset.mem_insert_of_mem hzS, hc⟩)
    omega
  obtain ⟨hxeq, hh1⟩ := hstep x hxS hxc hxN
  obtain ⟨hyeq, -⟩ := hstep y hyS hyc hyN
  exact predCount_injOn S x hxS y hyS (by rw [hxeq, hyeq])

open scoped Classical in
/-- Removing vertices from `A` changes `|Γ(A,A)|` by at most `|A \ B|·|A|`. -/
lemma card_gammaBetween_sdiff_le (Γ : Finset (Edge V)) (A B : Finset V) :
    (gammaBetween Γ A A).card
      ≤ (gammaBetween Γ B B).card + (A \ B).card * A.card := by
  classical
  have hsub : gammaBetween Γ A A
      ⊆ gammaBetween Γ B B ∪ (A \ B).biUnion (fun u =>
          (edgesAt Γ u).filter (fun e => otherEndOf u e ∈ A)) := by
    intro e he
    obtain ⟨heΓ, v, hv, w, hw, hvw, hve, hwe⟩ := mem_gammaBetween.mp he
    by_cases hvB : v ∈ B
    · by_cases hwB : w ∈ B
      · exact Finset.mem_union_left _
          (mem_gammaBetween.mpr ⟨heΓ, v, hvB, w, hwB, hvw, hve, hwe⟩)
      · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨w, Finset.mem_sdiff.mpr ⟨hw, hwB⟩, ?_⟩)
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heΓ, hwe⟩, ?_⟩
        have hoth : v = otherEndOf w e := eq_otherEndOf_of_mem hwe hve hvw
        rw [← hoth]; exact hv
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvB⟩, ?_⟩)
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heΓ, hve⟩, ?_⟩
      have hoth : w = otherEndOf v e :=
        eq_otherEndOf_of_mem hve hwe (Ne.symm hvw)
      rw [← hoth]; exact hw
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  refine Nat.add_le_add_left ?_ _
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ A.card ?_) (by rw [smul_eq_mul])
  intro u _
  refine Finset.card_le_card_of_injOn (otherEndOf u) ?_ ?_
  · intro e he
    exact (Finset.mem_filter.mp he).2
  · intro e he e' he' hEq
    refine otherEndOf_injOn Γ u ?_ ?_ hEq
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp he)).1
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp he')).1

open scoped Classical in
/-- Adding one vertex changes `|Γ(N̂,N̂)|` by at most `h`, in either
direction. This is Kim's `c_e = 2h` for `Φ⁽⁵⁾` (two affected endpoints). -/
lemma card_gammaBetween_truncTo_insert (Γ : Finset (Edge V)) (S : Finset V)
    (h : ℕ) (u : V) :
    (gammaBetween Γ (truncTo (insert u S) h)
        (truncTo (insert u S) h)).card
      ≤ (gammaBetween Γ (truncTo S h) (truncTo S h)).card + h
    ∧ (gammaBetween Γ (truncTo S h) (truncTo S h)).card
      ≤ (gammaBetween Γ (truncTo (insert u S) h)
          (truncTo (insert u S) h)).card + h := by
  classical
  constructor
  · have hd : (truncTo (insert u S) h \ truncTo S h).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun x hx y hy => ?_
      obtain ⟨hxA, hxB⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨hyA, hyB⟩ := Finset.mem_sdiff.mp hy
      have hx' := truncTo_insert_subset S h u hxA
      have hy' := truncTo_insert_subset S h u hyA
      rcases Finset.mem_insert.mp hx' with rfl | hc
      · rcases Finset.mem_insert.mp hy' with rfl | hc'
        · rfl
        · exact absurd hc' hyB
      · exact absurd hc hxB
    refine le_trans (card_gammaBetween_sdiff_le Γ (truncTo (insert u S) h)
      (truncTo S h)) ?_
    have hc : (truncTo (insert u S) h).card ≤ h := truncTo_card_le _ _
    calc (gammaBetween Γ (truncTo S h) (truncTo S h)).card
          + (truncTo (insert u S) h \ truncTo S h).card
            * (truncTo (insert u S) h).card
        ≤ (gammaBetween Γ (truncTo S h) (truncTo S h)).card + 1 * h :=
          Nat.add_le_add_left (Nat.mul_le_mul hd hc) _
      _ = (gammaBetween Γ (truncTo S h) (truncTo S h)).card + h := by ring
  · have hd : (truncTo S h \ truncTo (insert u S) h).card ≤ 1 :=
      card_truncTo_sdiff_insert S h u
    refine le_trans (card_gammaBetween_sdiff_le Γ (truncTo S h)
      (truncTo (insert u S) h)) ?_
    have hc : (truncTo S h).card ≤ h := truncTo_card_le _ _
    calc (gammaBetween Γ (truncTo (insert u S) h)
              (truncTo (insert u S) h)).card
          + (truncTo S h \ truncTo (insert u S) h).card * (truncTo S h).card
        ≤ (gammaBetween Γ (truncTo (insert u S) h)
            (truncTo (insert u S) h)).card + 1 * h :=
          Nat.add_le_add_left (Nat.mul_le_mul hd hc) _
      _ = _ := by ring

open scoped Classical in
/-- Kim's per-vertex `Z'` contribution `|Γ(N̂_{X'}(v,T))|` (§4.8, `Φ⁽³⁾`). -/
noncomputable def zContrib (s : BlockState V) (M : ℕ) (h : ℕ) (T : Finset V)
    (v : V) (σ : Fin (Fintype.card (Coord V M)) → Bool) : ℝ :=
  ((gammaBetween s.Γ (truncTo (nbrs (sampleP s M σ) v ∩ T) h)
      (truncTo (nbrs (sampleP s M σ) v ∩ T) h)).card : ℝ)

lemma zContrib_nonneg (s : BlockState V) (M h : ℕ) (T : Finset V) (v : V)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) : 0 ≤ zContrib s M h T v σ :=
  Nat.cast_nonneg _

/-- `zContrib` depends only on `v`'s coordinate block. -/
lemma zContrib_congr (s : BlockState V) (M h : ℕ) (T : Finset V) (v : V)
    {σ τ : Fin (Fintype.card (Coord V M)) → Bool}
    (hστ : ∀ j ∈ zBlock s M v T, σ j = τ j) :
    zContrib s M h T v σ = zContrib s M h T v τ := by
  rw [zContrib, zContrib, nbrs_sample_inter_congr s M v T hστ]

open scoped Classical in
/-- `|Γ(N̂)| ≤ C(|N̂|,2)`, hence at most half the squared block count. -/
lemma zContrib_le_sq (s : BlockState V) (M h : ℕ) (T : Finset V) (v : V)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) :
    zContrib s M h T v σ
      ≤ (∑ j ∈ zBlock s M v T, (if σ j = true then (1 : ℝ) else 0)) ^ 2 / 2 := by
  classical
  set N : Finset V := nbrs (sampleP s M σ) v ∩ T with hN
  set Z : ℝ := ∑ j ∈ zBlock s M v T, (if σ j = true then (1 : ℝ) else 0) with hZ
  have hNZ : ((N.card : ℕ) : ℝ) ≤ Z := card_nbrs_sample_inter_le s M v T σ
  have hNnn : (0 : ℝ) ≤ ((N.card : ℕ) : ℝ) := Nat.cast_nonneg _
  have hch : (gammaBetween s.Γ (truncTo N h) (truncTo N h)).card
      ≤ (truncTo N h).card.choose 2 :=
    card_gammaBetween_self_le _ _
  have hle : ((truncTo N h).card.choose 2 : ℝ)
      ≤ ((truncTo N h).card : ℝ) ^ 2 / 2 := by
    have hc : ((truncTo N h).card.choose 2 : ℕ) * 2
        ≤ (truncTo N h).card * (truncTo N h).card := by
      rw [Nat.choose_two_right]
      have hm := Nat.div_mul_le_self ((truncTo N h).card *
        ((truncTo N h).card - 1)) 2
      calc (truncTo N h).card * ((truncTo N h).card - 1) / 2 * 2
          ≤ (truncTo N h).card * ((truncTo N h).card - 1) := hm
        _ ≤ (truncTo N h).card * (truncTo N h).card :=
            Nat.mul_le_mul_left _ (by omega)
    have hcR : (((truncTo N h).card.choose 2 : ℕ) : ℝ) * 2
        ≤ ((truncTo N h).card : ℝ) * ((truncTo N h).card : ℝ) := by
      exact_mod_cast hc
    linarith [hcR]
  have hsub : ((truncTo N h).card : ℝ) ≤ ((N.card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_le_card (truncTo_subset N h)
  have htnn : (0 : ℝ) ≤ ((truncTo N h).card : ℝ) := Nat.cast_nonneg _
  calc zContrib s M h T v σ
      ≤ ((truncTo N h).card.choose 2 : ℝ) := by
        rw [zContrib, ← hN]; exact_mod_cast hch
    _ ≤ ((truncTo N h).card : ℝ) ^ 2 / 2 := hle
    _ ≤ Z ^ 2 / 2 := by nlinarith [hsub, hNZ, htnn, hNnn]

open scoped Classical in
/-- With `ρh ≤ 1` the truncation makes `ρ·zContrib ≤ Z/2`. -/
lemma zContrib_mul_le (s : BlockState V) (M h : ℕ) (T : Finset V) (v : V)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρh : ρ * (h : ℝ) ≤ 1) :
    ρ * zContrib s M h T v σ
      ≤ (∑ j ∈ zBlock s M v T, (if σ j = true then (1 : ℝ) else 0)) / 2 := by
  classical
  set N : Finset V := nbrs (sampleP s M σ) v ∩ T with hN
  set Z : ℝ := ∑ j ∈ zBlock s M v T, (if σ j = true then (1 : ℝ) else 0) with hZ
  have hNZ : ((N.card : ℕ) : ℝ) ≤ Z := card_nbrs_sample_inter_le s M v T σ
  set c : ℝ := ((truncTo N h).card : ℝ) with hc
  have hcnn : (0 : ℝ) ≤ c := by rw [hc]; positivity
  have hch : c ≤ (h : ℝ) := by
    rw [hc]; exact_mod_cast truncTo_card_le N h
  have hsub : c ≤ ((N.card : ℕ) : ℝ) := by
    rw [hc]; exact_mod_cast Finset.card_le_card (truncTo_subset N h)
  have hY : zContrib s M h T v σ * 2 ≤ c * (h : ℝ) := by
    have hch2 : (gammaBetween s.Γ (truncTo N h) (truncTo N h)).card
        ≤ (truncTo N h).card.choose 2 := card_gammaBetween_self_le _ _
    have hnat : ((truncTo N h).card.choose 2 : ℕ) * 2
        ≤ (truncTo N h).card * (truncTo N h).card := by
      rw [Nat.choose_two_right]
      have hm := Nat.div_mul_le_self ((truncTo N h).card *
        ((truncTo N h).card - 1)) 2
      calc (truncTo N h).card * ((truncTo N h).card - 1) / 2 * 2
          ≤ (truncTo N h).card * ((truncTo N h).card - 1) := hm
        _ ≤ (truncTo N h).card * (truncTo N h).card :=
            Nat.mul_le_mul_left _ (by omega)
    have h1 : zContrib s M h T v σ ≤ ((truncTo N h).card.choose 2 : ℝ) := by
      rw [zContrib, ← hN]; exact_mod_cast hch2
    have h2 : (((truncTo N h).card.choose 2 : ℕ) : ℝ) * 2 ≤ c * c := by
      rw [hc]; exact_mod_cast hnat
    nlinarith [h1, h2, hch, hcnn]
  nlinarith [hY, hρ, hρh, hcnn, hsub, hNZ, hch]

open scoped Classical in
/-- For `v ∈ T`, `v`'s block sits inside the coordinates of `Γ(T,T)`. -/
lemma zBlock_subset_gammaT (s : BlockState V) (M : ℕ) {v : V} {T : Finset V}
    (hv : v ∈ T) :
    zBlock s M v T ⊆ (gammaBetween s.Γ T T).image (padEmb V M) := by
  classical
  intro j hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨heΓ, hve, hoth⟩ := mem_edgesToSet.mp he
  refine Finset.mem_image.mpr ⟨e, ?_, rfl⟩
  refine mem_gammaBetween.mpr ⟨heΓ, v, hv, otherEndOf v e, hoth, ?_, hve, ?_⟩
  · intro hc
    exact e.2 (by rw [edge_eq_of_otherEndOf hve, ← hc]; simp)
  · rw [edge_eq_of_otherEndOf hve]; simp

open scoped Classical in
/-- **A single coordinate flip moves `zContrib` by at most `2h`.**

The sampled neighbourhood changes by at most one vertex, the *stable*
truncation therefore changes by at most one element, and `Γ` of a set changes
by at most `h` per element removed. -/
lemma zContrib_flip_le (s : BlockState V) (M h : ℕ) (T : Finset V) (v : V)
    (j : Fin (Fintype.card (Coord V M)))
    {σ τ : Fin (Fintype.card (Coord V M)) → Bool}
    (hagree : ∀ ℓ, ℓ ≠ j → σ ℓ = τ ℓ) :
    |zContrib s M h T v σ - zContrib s M h T v τ| ≤ 2 * (h : ℝ) := by
  classical
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg _
  by_cases hj : j ∈ zBlock s M v T
  · obtain ⟨e, he, hje⟩ := Finset.mem_image.mp hj
    set u : V := otherEndOf v e with hu
    have key : ∀ (σ' τ' : Fin (Fintype.card (Coord V M)) → Bool),
        (∀ ℓ, ℓ ≠ j → σ' ℓ = τ' ℓ) →
        nbrs (sampleP s M σ') v ∩ T
          ⊆ insert u (nbrs (sampleP s M τ') v ∩ T) := by
      intro σ' τ' hag x hx
      obtain ⟨hxn, hxT⟩ := Finset.mem_inter.mp hx
      obtain ⟨hne, f, hf, hvf, hxf⟩ := mem_nbrs.mp hxn
      obtain ⟨hfΓ, hsel⟩ := mem_sampleP.mp hf
      by_cases hxu : x = u
      · rw [hxu]; exact Finset.mem_insert_self _ _
      · have hfe : f ≠ e := by
          intro hc
          subst hc
          exact hxu (eq_otherEndOf_of_mem hvf hxf hne)
        have hjne : padEmb V M f ≠ j := by
          rw [← hje]
          intro hc
          exact hfe ((padEmb V M).injective hc)
        refine Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨?_, hxT⟩)
        refine mem_nbrs.mpr ⟨hne, f, mem_sampleP.mpr ⟨hfΓ, ?_⟩, hvf, hxf⟩
        rw [← hag _ hjne]; exact hsel
    have hins : insert u (nbrs (sampleP s M σ) v ∩ T)
        = insert u (nbrs (sampleP s M τ) v ∩ T) := by
      refine Finset.Subset.antisymm ?_ ?_
      · exact Finset.insert_subset (Finset.mem_insert_self _ _)
          (key σ τ hagree)
      · exact Finset.insert_subset (Finset.mem_insert_self _ _)
          (key τ σ (fun ℓ hℓ => (hagree ℓ hℓ).symm))
    have h1 := (card_gammaBetween_truncTo_insert s.Γ
      (nbrs (sampleP s M σ) v ∩ T) h u).2
    have h2 := (card_gammaBetween_truncTo_insert s.Γ
      (nbrs (sampleP s M τ) v ∩ T) h u).1
    have h3 := (card_gammaBetween_truncTo_insert s.Γ
      (nbrs (sampleP s M τ) v ∩ T) h u).2
    have h4 := (card_gammaBetween_truncTo_insert s.Γ
      (nbrs (sampleP s M σ) v ∩ T) h u).1
    rw [hins] at h1 h4
    have hA : (gammaBetween s.Γ (truncTo (nbrs (sampleP s M σ) v ∩ T) h)
          (truncTo (nbrs (sampleP s M σ) v ∩ T) h)).card
        ≤ (gammaBetween s.Γ (truncTo (nbrs (sampleP s M τ) v ∩ T) h)
            (truncTo (nbrs (sampleP s M τ) v ∩ T) h)).card + 2 * h := by
      omega
    have hB : (gammaBetween s.Γ (truncTo (nbrs (sampleP s M τ) v ∩ T) h)
          (truncTo (nbrs (sampleP s M τ) v ∩ T) h)).card
        ≤ (gammaBetween s.Γ (truncTo (nbrs (sampleP s M σ) v ∩ T) h)
            (truncTo (nbrs (sampleP s M σ) v ∩ T) h)).card + 2 * h := by
      omega
    rw [zContrib, zContrib, abs_sub_le_iff]
    constructor
    · have hAR : ((gammaBetween s.Γ (truncTo (nbrs (sampleP s M σ) v ∩ T) h)
            (truncTo (nbrs (sampleP s M σ) v ∩ T) h)).card : ℝ)
          ≤ ((gammaBetween s.Γ (truncTo (nbrs (sampleP s M τ) v ∩ T) h)
              (truncTo (nbrs (sampleP s M τ) v ∩ T) h)).card : ℝ)
            + 2 * (h : ℝ) := by exact_mod_cast hA
      linarith
    · have hBR : ((gammaBetween s.Γ (truncTo (nbrs (sampleP s M τ) v ∩ T) h)
            (truncTo (nbrs (sampleP s M τ) v ∩ T) h)).card : ℝ)
          ≤ ((gammaBetween s.Γ (truncTo (nbrs (sampleP s M σ) v ∩ T) h)
              (truncTo (nbrs (sampleP s M σ) v ∩ T) h)).card : ℝ)
            + 2 * (h : ℝ) := by exact_mod_cast hB
      linarith
  · have heq : zContrib s M h T v σ = zContrib s M h T v τ := by
      refine zContrib_congr s M h T v fun ℓ hℓ => hagree ℓ ?_
      intro hc; exact hj (hc ▸ hℓ)
    rw [heq, sub_self, abs_zero]
    linarith

open scoped Classical in
/-- **Kim's `c_e = 2h` for `Φ⁽⁵⁾`** (we take `4h`: two endpoints, `2h` each).
The constants vanish off the coordinates of `Γ(T)`. -/
lemma isCoordLipschitz_zSumT (s : BlockState V) (M h : ℕ) (T : Finset V) :
    IsCoordLipschitz (fun σ => ∑ v ∈ T, zContrib s M h T v σ)
      (fun j => if j ∈ (gammaBetween s.Γ T T).image (padEmb V M)
        then 4 * (h : ℝ) else 0) := by
  classical
  intro j σ τ hagree
  show |(∑ v ∈ T, zContrib s M h T v σ) - ∑ v ∈ T, zContrib s M h T v τ|
    ≤ (if j ∈ (gammaBetween s.Γ T T).image (padEmb V M)
        then 4 * (h : ℝ) else 0)
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg _
  by_cases hj : j ∈ (gammaBetween s.Γ T T).image (padEmb V M)
  · rw [if_pos hj]
    obtain ⟨e, -, hje⟩ := Finset.mem_image.mp hj
    have hzero : ∀ v ∈ T, v ∉ edgeVerts e →
        zContrib s M h T v σ = zContrib s M h T v τ := by
      intro v _ hve
      refine zContrib_congr s M h T v fun ℓ hℓ => hagree ℓ ?_
      intro hc
      subst hc
      obtain ⟨f, hf, hfj⟩ := Finset.mem_image.mp hℓ
      have hfe : f = e := (padEmb V M).injective (hfj.trans hje.symm)
      subst hfe
      exact hve (mem_edgeVerts.mpr (mem_edgesToSet.mp hf).2.1)
    have hcard : ((T.filter (fun v => v ∈ edgeVerts e)).card : ℝ) ≤ 2 := by
      have hnat : (T.filter (fun v => v ∈ edgeVerts e)).card ≤ 2 := by
        refine le_trans (Finset.card_le_card ?_) (le_of_eq (edgeVerts_card e))
        intro v hv; exact (Finset.mem_filter.mp hv).2
      exact_mod_cast hnat
    calc |(∑ v ∈ T, zContrib s M h T v σ) - ∑ v ∈ T, zContrib s M h T v τ|
        = |∑ v ∈ T, (zContrib s M h T v σ - zContrib s M h T v τ)| := by
          rw [Finset.sum_sub_distrib]
      _ ≤ ∑ v ∈ T, |zContrib s M h T v σ - zContrib s M h T v τ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ v ∈ T.filter (fun v => v ∈ edgeVerts e),
            |zContrib s M h T v σ - zContrib s M h T v τ| := by
          rw [← Finset.sum_filter_add_sum_filter_not T
            (fun v => v ∈ edgeVerts e)]
          have hz : ∑ v ∈ T.filter (fun v => ¬ v ∈ edgeVerts e),
              |zContrib s M h T v σ - zContrib s M h T v τ| = 0 := by
            refine Finset.sum_eq_zero fun v hv => ?_
            obtain ⟨hvT, hvE⟩ := Finset.mem_filter.mp hv
            rw [hzero v hvT hvE, sub_self, abs_zero]
          rw [hz, add_zero]
      _ ≤ ∑ _v ∈ T.filter (fun v => v ∈ edgeVerts e), 2 * (h : ℝ) :=
          Finset.sum_le_sum fun v _ => zContrib_flip_le s M h T v j hagree
      _ = ((T.filter (fun v => v ∈ edgeVerts e)).card : ℝ) * (2 * (h : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 4 * (h : ℝ) := by nlinarith [hcard, hh0]
  · rw [if_neg hj]
    have heq : ∀ v ∈ T, zContrib s M h T v σ = zContrib s M h T v τ := by
      intro v hv
      refine zContrib_congr s M h T v fun ℓ hℓ => hagree ℓ ?_
      intro hc
      exact hj (hc ▸ zBlock_subset_gammaT s M hv hℓ)
    rw [Finset.sum_congr rfl heq, sub_self, abs_zero]

open scoped Classical in
/-- **Kim (48).** The `Z'`-contribution from vertices *inside* `T` does yield to
Kahn's inequality: its Lipschitz constants are `4h`, supported on the `|Γ(T)|`
coordinates of `Γ(T,T)`. -/
theorem zSumT_tail (s : BlockState V) (M h : ℕ) (T : Finset V) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {t lam : ℝ} (ht : 0 ≤ t) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          lam ≤ (∑ v ∈ T, zContrib s M h T v σ)
            - bernoulliExp p (fun τ => ∑ v ∈ T, zContrib s M h T v τ)))
      ≤ Real.exp (-t * lam + t ^ 2 / 2 * (p * (1 - p)
          * (((gammaBetween s.Γ T T).card : ℝ)
              * ((4 * (h : ℝ)) ^ 2 * Real.exp (t * (4 * (h : ℝ))))))) := by
  classical
  refine le_trans (bernoulliPr_upper_tail hp0 hp1
    (isCoordLipschitz_zSumT s M h T) ht) ?_
  refine Real.exp_le_exp.mpr ?_
  have hsum : ∑ j : Fin (Fintype.card (Coord V M)),
      (if j ∈ (gammaBetween s.Γ T T).image (padEmb V M)
        then 4 * (h : ℝ) else 0) ^ 2
      * Real.exp (t * (if j ∈ (gammaBetween s.Γ T T).image (padEmb V M)
        then 4 * (h : ℝ) else 0))
      = ((gammaBetween s.Γ T T).card : ℝ)
        * ((4 * (h : ℝ)) ^ 2 * Real.exp (t * (4 * (h : ℝ)))) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j => j ∈ (gammaBetween s.Γ T T).image (padEmb V M))]
    have hno : ∑ j ∈ Finset.univ.filter
        (fun j => ¬ j ∈ (gammaBetween s.Γ T T).image (padEmb V M)),
        (if j ∈ (gammaBetween s.Γ T T).image (padEmb V M)
          then 4 * (h : ℝ) else 0) ^ 2
        * Real.exp (t * (if j ∈ (gammaBetween s.Γ T T).image (padEmb V M)
          then 4 * (h : ℝ) else 0)) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [if_neg (Finset.mem_filter.mp hj).2]
      ring
    have hyes : ∑ j ∈ Finset.univ.filter
        (fun j => j ∈ (gammaBetween s.Γ T T).image (padEmb V M)),
        (if j ∈ (gammaBetween s.Γ T T).image (padEmb V M)
          then 4 * (h : ℝ) else 0) ^ 2
        * Real.exp (t * (if j ∈ (gammaBetween s.Γ T T).image (padEmb V M)
          then 4 * (h : ℝ) else 0))
        = ((gammaBetween s.Γ T T).card : ℝ)
          * ((4 * (h : ℝ)) ^ 2 * Real.exp (t * (4 * (h : ℝ)))) := by
      have hfil : Finset.univ.filter
          (fun j => j ∈ (gammaBetween s.Γ T T).image (padEmb V M))
          = (gammaBetween s.Γ T T).image (padEmb V M) := by
        ext j; simp
      rw [hfil]
      rw [Finset.sum_congr rfl (fun j hj => by
        rw [if_pos hj])]
      rw [Finset.sum_const, nsmul_eq_mul,
        Finset.card_image_of_injective _ (padEmb V M).injective]
    rw [hno, hyes, add_zero]
  rw [hsum]

open scoped Classical in
/-- **Kim (49).** The `Z'`-contribution from vertices *outside* `T` is a sum of
independent per-vertex terms, so its exponential moment factorises and Markov
gives a tail bound with only a *quadratic* penalty in `ρ`.

This is the step where Kahn's inequality is unavailable: the Lipschitz constants
of `Φ⁽⁶⁾` are supported on the `≈ nt` edges between `V \ T` and `T`, and
`ρ²p·Σc²` overwhelms `ρλ`. Independence across `v ∉ T` — which holds precisely
because the blocks `zBlock v T` are then pairwise disjoint — is what saves it. -/
theorem zSum_tail (s : BlockState V) (M h : ℕ) (T : Finset V) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρh : ρ * (h : ℝ) ≤ 1)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ v : V, ((1 - p) + p * Real.exp 1) ^ (zBlock s M v T).card ≤ K)
    {mean : ℝ} (hmean : ∑ v ∈ (Finset.univ : Finset V) \ T,
      bernoulliExp p (zContrib s M h T v) ≤ mean)
    (c : ℝ) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          c ≤ ∑ v ∈ (Finset.univ : Finset V) \ T, zContrib s M h T v σ))
      ≤ Real.exp (-(ρ * c) + (ρ * mean + 1024 * ρ ^ 2 * K * (n : ℝ))) := by
  classical
  set S : Finset V := (Finset.univ : Finset V) \ T with hS
  have hrw : (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        Real.exp (ρ * ∑ v ∈ S, zContrib s M h T v σ))
      = fun σ => ∏ v ∈ S, Real.exp (ρ * zContrib s M h T v σ) := by
    funext σ
    rw [Finset.mul_sum, Real.exp_sum]
  have hdisj : ∀ v ∈ S, ∀ v' ∈ S, v ≠ v' →
      Disjoint (zBlock s M v T) (zBlock s M v' T) := by
    intro v _ v' hv' hne
    exact zBlock_disjoint s M T (Finset.mem_sdiff.mp hv').2 hne
  have hdep : ∀ v : V, ∀ σ τ : Fin (Fintype.card (Coord V M)) → Bool,
      (∀ j ∈ zBlock s M v T, σ j = τ j) →
      Real.exp (ρ * zContrib s M h T v σ)
        = Real.exp (ρ * zContrib s M h T v τ) := by
    intro v σ τ hστ
    rw [zContrib_congr s M h T v hστ]
  have hfac : bernoulliExp p (fun σ =>
        Real.exp (ρ * ∑ v ∈ S, zContrib s M h T v σ))
      = ∏ v ∈ S, bernoulliExp p (fun σ =>
          Real.exp (ρ * zContrib s M h T v σ)) := by
    rw [hrw]
    exact bernoulliExp_prod_blocks (fun v => zBlock s M v T)
      (fun v σ => Real.exp (ρ * zContrib s M h T v σ)) hdep S hdisj
  have hfactor : ∀ v ∈ S,
      bernoulliExp p (fun σ => Real.exp (ρ * zContrib s M h T v σ))
        ≤ Real.exp (ρ * bernoulliExp p (zContrib s M h T v)
            + 1024 * ρ ^ 2 * K) := by
    intro v _
    have hcl := bernoulliExp_exp_le_of_count hp0 hp1 (zBlock s M v T)
      (zContrib s M h T v) hρ (zContrib_nonneg s M h T v)
      (fun σ => zContrib_le_sq s M h T v σ)
      (fun σ => zContrib_mul_le s M h T v σ hρ hρh)
    have hKv : 1024 * ρ ^ 2
          * ((1 - p) + p * Real.exp 1) ^ (zBlock s M v T).card
        ≤ 1024 * ρ ^ 2 * K :=
      mul_le_mul_of_nonneg_left (hK v) (by positivity)
    calc bernoulliExp p (fun σ => Real.exp (ρ * zContrib s M h T v σ))
        ≤ 1 + ρ * bernoulliExp p (zContrib s M h T v)
          + 1024 * ρ ^ 2
            * ((1 - p) + p * Real.exp 1) ^ (zBlock s M v T).card := hcl
      _ ≤ 1 + (ρ * bernoulliExp p (zContrib s M h T v)
            + 1024 * ρ ^ 2 * K) := by linarith [hKv]
      _ ≤ Real.exp (ρ * bernoulliExp p (zContrib s M h T v)
            + 1024 * ρ ^ 2 * K) := by
          have hae := Real.add_one_le_exp (ρ * bernoulliExp p
            (zContrib s M h T v) + 1024 * ρ ^ 2 * K)
          linarith [hae]
  have hnn : ∀ v ∈ S, (0 : ℝ)
      ≤ bernoulliExp p (fun σ => Real.exp (ρ * zContrib s M h T v σ)) := by
    intro v _
    have hm := bernoulliExp_mono hp0 hp1
      (f := fun _ : Fin (Fintype.card (Coord V M)) → Bool => (0 : ℝ))
      (g := fun σ => Real.exp (ρ * zContrib s M h T v σ))
      (fun σ => (Real.exp_pos _).le)
    rwa [bernoulliExp_const] at hm
  have hprod : bernoulliExp p (fun σ =>
        Real.exp (ρ * ∑ v ∈ S, zContrib s M h T v σ))
      ≤ Real.exp (ρ * mean + 1024 * ρ ^ 2 * K * (n : ℝ)) := by
    rw [hfac]
    refine le_trans (Finset.prod_le_prod hnn hfactor) ?_
    rw [← Real.exp_sum]
    refine Real.exp_le_exp.mpr ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul]
    have hcard : ((S.card : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Finset.card_le_univ S
    have h1 : ρ * ∑ v ∈ S, bernoulliExp p (zContrib s M h T v) ≤ ρ * mean :=
      mul_le_mul_of_nonneg_left hmean hρ
    have h2 : (S.card : ℝ) * (1024 * ρ ^ 2 * K)
        ≤ 1024 * ρ ^ 2 * K * (n : ℝ) := by
      have hnn2 : (0 : ℝ) ≤ 1024 * ρ ^ 2 * K := by positivity
      nlinarith [hcard, hnn2]
    linarith [h1, h2]
  have hexp0 : (0 : ℝ) < Real.exp (ρ * c) := Real.exp_pos _
  have hmark := bernoulliPr_mul_le hp0 hp1
    (fun σ => Real.exp (ρ * ∑ v ∈ S, zContrib s M h T v σ))
    (fun σ => (Real.exp_pos _).le)
    (a := Real.exp (ρ * c))
    (Finset.univ.filter (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
      c ≤ ∑ v ∈ S, zContrib s M h T v σ))
    (fun σ hσ => Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hσ).2 hρ))
  have hfin := le_trans hmark hprod
  rw [← le_div_iff₀ hexp0] at hfin
  refine le_trans hfin (le_of_eq ?_)
  rw [← Real.exp_sub]
  congr 1
  ring

open scoped Classical in
/-- **Kim (45)**: `|Z' ∩ Γ(T)| ≤ Φ⁽³⁾_T + Φ⁽⁴⁾_T`.

Each `Γ(N_{X'}(v,T))` is either already small — in which case truncation does
nothing and it sits in `Φ⁽³⁾` — or `v` has at least `h` sampled neighbours in
`T`, in which case it sits in `Φ⁽⁴⁾`. -/
lemma killedZpure_cover (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) (T : Finset V) (h : ℕ) :
    killedZpure s M σ ∩ gammaBetween s.Γ T T
      ⊆ ((Finset.univ : Finset V).biUnion (fun v =>
          gammaBetween s.Γ (truncTo (nbrs (sampleP s M σ) v ∩ T) h)
            (truncTo (nbrs (sampleP s M σ) v ∩ T) h)))
        ∪ ((Finset.univ.filter
            (fun v => h ≤ (nbrs (sampleP s M σ) v ∩ T).card)).biUnion
          (fun v => gammaBetween s.Γ (nbrs (sampleP s M σ) v ∩ T)
            (nbrs (sampleP s M σ) v ∩ T))) := by
  classical
  intro e he
  obtain ⟨v, -, hv⟩ := Finset.mem_biUnion.mp
    (killedZpure_inter_gammaT_subset s M σ T he)
  by_cases hbig : h ≤ (nbrs (sampleP s M σ) v ∩ T).card
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbig⟩, hv⟩)
  · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨v,
      Finset.mem_univ _, ?_⟩)
    rw [truncTo_eq_self hbig]
    exact hv

open scoped Classical in
/-- The cardinality form of (45). -/
lemma card_killedZpure_inter_le (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) (T : Finset V) (h : ℕ) :
    ((killedZpure s M σ ∩ gammaBetween s.Γ T T).card : ℝ)
      ≤ (∑ v : V, ((gammaBetween s.Γ (truncTo (nbrs (sampleP s M σ) v ∩ T) h)
            (truncTo (nbrs (sampleP s M σ) v ∩ T) h)).card : ℝ))
        + (∑ v ∈ Finset.univ.filter
              (fun v => h ≤ (nbrs (sampleP s M σ) v ∩ T).card),
            ((gammaBetween s.Γ (nbrs (sampleP s M σ) v ∩ T)
              (nbrs (sampleP s M σ) v ∩ T)).card : ℝ)) := by
  classical
  have hsub := killedZpure_cover s M σ T h
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le
    ((Finset.univ : Finset V).biUnion (fun v =>
      gammaBetween s.Γ (truncTo (nbrs (sampleP s M σ) v ∩ T) h)
        (truncTo (nbrs (sampleP s M σ) v ∩ T) h)))
    ((Finset.univ.filter
      (fun v => h ≤ (nbrs (sampleP s M σ) v ∩ T).card)).biUnion
      (fun v => gammaBetween s.Γ (nbrs (sampleP s M σ) v ∩ T)
        (nbrs (sampleP s M σ) v ∩ T)))
  have h3 := Finset.card_biUnion_le (s := (Finset.univ : Finset V))
    (t := fun v => gammaBetween s.Γ (truncTo (nbrs (sampleP s M σ) v ∩ T) h)
      (truncTo (nbrs (sampleP s M σ) v ∩ T) h))
  have h4 := Finset.card_biUnion_le
    (s := Finset.univ.filter (fun v => h ≤ (nbrs (sampleP s M σ) v ∩ T).card))
    (t := fun v => gammaBetween s.Γ (nbrs (sampleP s M σ) v ∩ T)
      (nbrs (sampleP s M σ) v ∩ T))
  have hnat : (killedZpure s M σ ∩ gammaBetween s.Γ T T).card
      ≤ (∑ v : V, (gammaBetween s.Γ (truncTo (nbrs (sampleP s M σ) v ∩ T) h)
            (truncTo (nbrs (sampleP s M σ) v ∩ T) h)).card)
        + (∑ v ∈ Finset.univ.filter
              (fun v => h ≤ (nbrs (sampleP s M σ) v ∩ T).card),
            (gammaBetween s.Γ (nbrs (sampleP s M σ) v ∩ T)
              (nbrs (sampleP s M σ) v ∩ T)).card) := by
    omega
  exact_mod_cast hnat

open scoped Classical in
/-- Every killer of a `Γ(T)`-edge is either low — in which case the edge fails
the truncated survival test — or high, in which case the edge lies in
`Y⁽²⁾(T)`. -/
lemma killedY_inter_gammaT_subset (s : BlockState V) (M : ℕ) (T : Finset V)
    (thr : ℝ) (σ : Fin (Fintype.card (Coord V M)) → Bool) :
    killedY s M σ ∩ gammaBetween s.Γ T T
      ⊆ ((gammaBetween s.Γ T T).filter
          (fun e => σ ∉ survEventLow s M T T thr e))
        ∪ killedY2 s M T thr σ := by
  classical
  intro e he
  obtain ⟨heY, heG⟩ := Finset.mem_inter.mp he
  obtain ⟨heΓ, c, hcΛ, hcsel⟩ := mem_killedY.mp heY
  by_cases hlow : c ∈ lowKillers s M T T thr e
  · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heG, ?_⟩)
    intro hsurv
    have := (Finset.mem_filter.mp hsurv).2 c hlow
    rw [this] at hcsel
    exact Bool.noConfusion hcsel
  · refine Finset.mem_union_right _ ?_
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp
      (lambdaStar_sdiff_lowKillers_subset s M T T thr e
        (Finset.mem_sdiff.mpr ⟨hcΛ, hlow⟩))
    obtain ⟨g, hg, hgc⟩ := Finset.mem_image.mp hcv
    obtain ⟨hgΛ, hghigh⟩ := Finset.mem_filter.mp hg
    refine Finset.mem_filter.mpr ⟨heG, v, hv, g, hgΛ, hghigh, ?_⟩
    show σ (coordEquiv V M (Sum.inl g)) = true
    rw [hgc]; exact hcsel

open scoped Classical in
/-- **Kim's §4.8 deterministic core**, combining (37), (45) and the
low/high split:

`|Γ'(T)| ≥ Φ⁽¹⁾_T − |Y⁽²⁾(T)| − |X'∩Γ(T)| − |Z'∩Γ(T)|`. -/
lemma card_gammaT_blockStepP_ge (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) (T : Finset V) (thr : ℝ) :
    (∑ e ∈ gammaBetween s.Γ T T,
        (if σ ∈ survEventLow s M T T thr e then (1 : ℝ) else 0))
        - ((killedY2 s M T thr σ).card : ℝ)
        - ((gammaBetween s.Γ T T ∩ sampleP s M σ).card : ℝ)
        - ((gammaBetween s.Γ T T ∩ killedZpure s M σ).card : ℝ)
      ≤ ((gammaBetween (blockStepP s M σ).Γ T T).card : ℝ) := by
  classical
  set GT : Finset (Edge V) := gammaBetween s.Γ T T with hGT
  set Surv : Finset (Edge V) :=
    GT.filter (fun e => σ ∈ survEventLow s M T T thr e) with hSurv
  set U : Finset (Edge V) := ((GT ∩ sampleP s M σ) ∪ (GT \ Surv))
    ∪ (killedY2 s M T thr σ ∪ (GT ∩ killedZpure s M σ)) with hU
  have hsub : GT \ U ⊆ gammaBetween (blockStepP s M σ).Γ T T := by
    intro e he
    obtain ⟨heG, hnU⟩ := Finset.mem_sdiff.mp he
    obtain ⟨heΓ, hTT⟩ := Finset.mem_filter.mp heG
    have hnX : e ∉ sampleP s M σ := fun h => hnU (hU ▸ Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨heG, h⟩)))
    have hnY : e ∉ killedY s M σ := by
      intro h
      rcases Finset.mem_union.mp (killedY_inter_gammaT_subset s M T thr σ
        (Finset.mem_inter.mpr ⟨h, heG⟩)) with h1 | h1
      · exact hnU (hU ▸ Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨heG, fun hc =>
            (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp hc).2⟩)))
      · exact hnU (hU ▸ Finset.mem_union_right _ (Finset.mem_union_left _ h1))
    have hnZ : e ∉ killedZ s M σ := by
      intro h
      rcases Finset.mem_union.mp (killedZ_subset s M σ h) with h1 | h1
      · exact hnY h1
      · exact hnU (hU ▸ Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨heG, h1⟩)))
    have htri : ∀ f ∈ s.E ∪ sampleP s M σ, ∀ g ∈ s.E ∪ sampleP s M σ,
        ¬ IsTriangle e f g := by
      by_contra hcon
      exact hnZ (Finset.mem_filter.mpr ⟨heΓ, hcon⟩)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨heΓ, hnX⟩, htri⟩, hnY⟩,
       hTT⟩
  have hUcard : U.card ≤ (GT ∩ sampleP s M σ).card + (GT \ Surv).card
      + ((killedY2 s M T thr σ).card + (GT ∩ killedZpure s M σ).card) := by
    refine le_trans (Finset.card_union_le _ _) ?_
    have h1 := Finset.card_union_le (GT ∩ sampleP s M σ) (GT \ Surv)
    have h2 := Finset.card_union_le (killedY2 s M T thr σ)
      (GT ∩ killedZpure s M σ)
    omega
  have hSurvSub : Surv ⊆ GT := Finset.filter_subset _ _
  have hSdiff : (GT \ Surv).card = GT.card - Surv.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSurvSub]
  have hSle : Surv.card ≤ GT.card := Finset.card_le_card hSurvSub
  have hdiff : GT.card ≤ (GT \ U).card + U.card := by
    have h1 := Finset.card_sdiff_add_card GT U
    have h2 : GT.card ≤ (GT ∪ U).card :=
      Finset.card_le_card Finset.subset_union_left
    omega
  have hfin : (GT \ U).card ≤ (gammaBetween (blockStepP s M σ).Γ T T).card :=
    Finset.card_le_card hsub
  have hsum : (∑ e ∈ GT, (if σ ∈ survEventLow s M T T thr e then (1 : ℝ) else 0))
      = (Surv.card : ℝ) := by
    rw [hSurv, Finset.card_filter]; push_cast; rfl
  rw [hsum]
  have hkey : GT.card ≤ (gammaBetween (blockStepP s M σ).Γ T T).card
      + ((GT ∩ sampleP s M σ).card + (GT.card - Surv.card)
        + ((killedY2 s M T thr σ).card + (GT ∩ killedZpure s M σ).card)) := by
    omega
  have hkeyR : (GT.card : ℝ)
      ≤ ((gammaBetween (blockStepP s M σ).Γ T T).card : ℝ)
        + (((GT ∩ sampleP s M σ).card : ℝ) + ((GT.card : ℝ) - (Surv.card : ℝ))
          + (((killedY2 s M T thr σ).card : ℝ)
            + ((GT ∩ killedZpure s M σ).card : ℝ))) := by
    have hcast : ((GT.card - Surv.card : ℕ) : ℝ)
        = (GT.card : ℝ) - (Surv.card : ℝ) := by
      have : (Surv.card : ℝ) ≤ (GT.card : ℝ) := by exact_mod_cast hSle
      push_cast [Nat.cast_sub hSle]; ring
    have := hkey
    have hR : ((GT.card : ℕ) : ℝ)
        ≤ (((gammaBetween (blockStepP s M σ).Γ T T).card
          + ((GT ∩ sampleP s M σ).card + (GT.card - Surv.card)
            + ((killedY2 s M T thr σ).card
              + (GT ∩ killedZpure s M σ).card)) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast [Nat.cast_sub hSle] at hR
    linarith
  linarith

open scoped Classical in
/-- **`𝒯' ⊆ 𝒯`**: the graph only grows, so a `t`-set free of `G'`-edges was
already free of `G`-edges. This is what lets Kim sum (55) over `𝒯_k` and feed
in Property 8 at stage `k`, so that the exponential factor accumulates. -/
lemma calT_blockStepP_subset (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) :
    calT (blockStepP s M σ) ⊆ calT s := by
  classical
  intro T hT
  obtain ⟨-, hcard, hno⟩ := Finset.mem_filter.mp hT
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard, fun e he => ?_⟩
  exact hno e (Finset.mem_union_left _ he)

open scoped Classical in
/-- **Property 7's union bound, with the global events pulled out.**

Kim's (40) and (54) bound *global* events — Property 3 surviving the step, and
the sampled degrees — so they must be charged once, not `C(n,t)` times.  Only
(39), (38) and (46) are genuinely per-`T`, and their tails
(`exp(−√n(log n)²)`) do beat `C(n,t) ≈ exp(4.5√n(log n)^{3/2})`. -/
theorem property7_prob' (k : ℕ) (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (thr : ℝ) {c1 c2 c3 c4 : ℝ}
    (hsplit : c1 - c2 - c3 - c4
      = bSeq n (k + 1) * μSeq n (k + 1) * ((tParam n).choose 2))
    (Good : Finset (Fin (Fintype.card (Coord V M)) → Bool))
    {q0 q1 q3 q4 : ℝ}
    (hq0Good : bernoulliPr p (Finset.univ \ Good) ≤ q0)
    (hb1 : ∀ T ∈ calT s, bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          (∑ e ∈ gammaBetween s.Γ T T,
            (if σ ∈ survEventLow s M T T thr e then (1 : ℝ) else 0)) < c1))
      ≤ q1)
    (hb2 : ∀ T ∈ calT s, Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          c2 < ((killedY2 s M T thr σ).card : ℝ)) ⊆ Finset.univ \ Good)
    (hb3 : ∀ T ∈ calT s, bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          c3 < ((gammaBetween s.Γ T T ∩ sampleP s M σ).card : ℝ))) ≤ q3)
    (hb4 : ∀ T ∈ calT s, bernoulliPr p ((Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          c4 < ((gammaBetween s.Γ T T ∩ killedZpure s M σ).card : ℝ))) ∩ Good)
      ≤ q4)
    (hq : 0 ≤ q1 + q3 + q4) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          ¬ Property7 (blockStepP s M σ) (k + 1)))
      ≤ q0 + ((n : ℕ).choose (tParam n) : ℝ) * (q1 + q3 + q4) := by
  classical
  refine le_trans (bernoulliPr_mono hp0 hp1 (?_ :
      (Finset.univ.filter (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ¬ Property7 (blockStepP s M σ) (k + 1)))
      ⊆ (Finset.univ \ Good) ∪ (calT s).biUnion (fun T =>
          (Finset.univ.filter (fun σ =>
            (∑ e ∈ gammaBetween s.Γ T T,
              (if σ ∈ survEventLow s M T T thr e then (1 : ℝ) else 0)) < c1))
          ∪ ((Finset.univ.filter (fun σ =>
              c3 < ((gammaBetween s.Γ T T ∩ sampleP s M σ).card : ℝ)))
            ∪ ((Finset.univ.filter (fun σ =>
              c4 < ((gammaBetween s.Γ T T ∩ killedZpure s M σ).card : ℝ)))
              ∩ Good))))) ?_
  · intro σ hσ
    obtain ⟨-, hfail⟩ := Finset.mem_filter.mp hσ
    rw [Property7] at hfail
    push_neg at hfail
    obtain ⟨T, hTmem, hlt⟩ := hfail
    by_cases hG : σ ∈ Good
    · have hTs : T ∈ calT s := calT_blockStepP_subset s M σ hTmem
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨T, hTs, ?_⟩)
      by_contra hcon
      have h1 : ¬ ((∑ e ∈ gammaBetween s.Γ T T,
          (if σ ∈ survEventLow s M T T thr e then (1 : ℝ) else 0)) < c1) :=
        fun hc => hcon (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩))
      have h3 : ¬ (c3 < ((gammaBetween s.Γ T T ∩ sampleP s M σ).card : ℝ)) :=
        fun hc => hcon (Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)))
      have h4 : ¬ (c4 < ((gammaBetween s.Γ T T
          ∩ killedZpure s M σ).card : ℝ)) :=
        fun hc => hcon (Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_inter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, hG⟩)))
      have h2 : ¬ (c2 < ((killedY2 s M T thr σ).card : ℝ)) := by
        intro hc
        have hbad := hb2 T hTs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
        exact (Finset.mem_sdiff.mp hbad).2 hG
      push_neg at h1 h2 h3 h4
      have hdet := card_gammaT_blockStepP_ge s M σ T thr
      rw [← hsplit] at hlt
      linarith
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hG⟩)
  · refine le_trans (bernoulliPr_union_le hp0 hp1 _ _) ?_
    have hbi : bernoulliPr p ((calT s).biUnion (fun T =>
        (Finset.univ.filter (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          (∑ e ∈ gammaBetween s.Γ T T,
            (if σ ∈ survEventLow s M T T thr e then (1 : ℝ) else 0)) < c1))
        ∪ ((Finset.univ.filter (fun σ =>
            c3 < ((gammaBetween s.Γ T T ∩ sampleP s M σ).card : ℝ)))
          ∪ ((Finset.univ.filter (fun σ =>
            c4 < ((gammaBetween s.Γ T T ∩ killedZpure s M σ).card : ℝ)))
            ∩ Good))))
        ≤ ((n : ℕ).choose (tParam n) : ℝ) * (q1 + q3 + q4) := by
      refine le_trans (bernoulliPr_biUnion_le hp0 hp1 _ _) ?_
      refine le_trans (Finset.sum_le_sum
        (g := fun _ : Finset V => q1 + q3 + q4) fun T hT => ?_) ?_
      · show (_ : ℝ) ≤ q1 + q3 + q4
        have hu1 := bernoulliPr_union_le hp0 hp1
          (Finset.univ.filter (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
            (∑ e ∈ gammaBetween s.Γ T T,
              (if σ ∈ survEventLow s M T T thr e then (1 : ℝ) else 0)) < c1))
          ((Finset.univ.filter (fun σ =>
              c3 < ((gammaBetween s.Γ T T ∩ sampleP s M σ).card : ℝ)))
            ∪ ((Finset.univ.filter (fun σ =>
              c4 < ((gammaBetween s.Γ T T ∩ killedZpure s M σ).card : ℝ)))
              ∩ Good))
        have hu2 := bernoulliPr_union_le hp0 hp1
          (Finset.univ.filter (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
            c3 < ((gammaBetween s.Γ T T ∩ sampleP s M σ).card : ℝ)))
          ((Finset.univ.filter (fun σ =>
            c4 < ((gammaBetween s.Γ T T ∩ killedZpure s M σ).card : ℝ)))
            ∩ Good)
        linarith [hb1 T hT, hb3 T hT, hb4 T hT, hu1, hu2]
      · rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((calT s).card : ℝ)
            ≤ ((n : ℕ).choose (tParam n) : ℝ) := by
          exact_mod_cast card_calT_le s
        exact mul_le_mul_of_nonneg_right hcard hq
    linarith [hq0Good, hbi]

lemma card_forbidden_le_three {E X F : Finset (Edge V)}
    (h : IsForbidden E X F) : F.card ≤ 3 := by
  classical
  obtain ⟨-, hcase⟩ := h
  rcases hcase with ⟨e, f, rfl, -⟩ | ⟨e, f, g, rfl, -⟩
  · exact le_trans (Finset.card_insert_le _ _) (by simp)
  · refine le_trans (Finset.card_insert_le _ _) ?_
    refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
    simp

/-- Kim's `ℱ'(T)`: the members of the maximal disjoint collection that meet
`Γ(T)`. -/
noncomputable def kimFamHitting (E X G : Finset (Edge V)) :
    Finset (Finset (Edge V)) := by
  classical
  exact (kimFam E X).filter (fun F => (F ∩ G).Nonempty)

open scoped Classical in
/-- **Kim's `|X' ∩ Γ(T)| ≤ 3|ℱ'(T)|`** — the inequality (57) rests on.

If no edge of `G'` lies inside `T`, then every selected edge of `Γ(T)` was
deleted, hence lies in some member of `ℱ'` meeting `Γ(T)`; and each member has
at most three edges. -/
theorem card_sample_inter_le_three_mul (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) (T : Finset V)
    (hempty : ∀ e ∈ (blockStepP s M σ).G, e ∉ gammaBetween s.Γ T T) :
    (gammaBetween s.Γ T T ∩ sampleP s M σ).card
      ≤ 3 * (kimFamHitting s.E (sampleP s M σ)
          (gammaBetween s.Γ T T)).card := by
  classical
  set X : Finset (Edge V) := sampleP s M σ with hX
  set GT : Finset (Edge V) := gammaBetween s.Γ T T with hGT
  set Fam : Finset (Finset (Edge V)) := kimFamHitting s.E X GT with hFam
  have hsub : GT ∩ X ⊆ Fam.biUnion id := by
    intro e he
    obtain ⟨heG, heX⟩ := Finset.mem_inter.mp he
    have hrem : e ∈ kimRemoved s.E X := by
      by_contra hcon
      exact hempty e (Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨heX, hcon⟩)) heG
    obtain ⟨F, hF, heF⟩ := Finset.mem_biUnion.mp hrem
    exact Finset.mem_biUnion.mpr ⟨F,
      Finset.mem_filter.mpr ⟨hF, ⟨e, Finset.mem_inter.mpr ⟨heF, heG⟩⟩⟩, heF⟩
  calc (GT ∩ X).card ≤ (Fam.biUnion id).card := Finset.card_le_card hsub
    _ ≤ ∑ F ∈ Fam, (id F).card := Finset.card_biUnion_le
    _ ≤ ∑ _F ∈ Fam, 3 := by
        refine Finset.sum_le_sum fun F hF => ?_
        exact card_forbidden_le_three
          (mem_forbiddenFams.mp ((kimFam_spec s.E X).1
            (Finset.mem_filter.mp hF).1))
    _ = 3 * Fam.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

lemma IsForbidden.mono {E X Y : Finset (Edge V)} (hXY : X ⊆ Y)
    {F : Finset (Edge V)} (h : IsForbidden E X F) : IsForbidden E Y F :=
  ⟨h.1.trans hXY, h.2⟩

/-- Kim's `Λ ∪ Δ` restricted to configurations meeting `Γ(T)`: the σ-independent
family the union bound of (59) ranges over. -/
noncomputable def hitFams (s : BlockState V) (T : Finset V) :
    Finset (Finset (Edge V)) := by
  classical
  exact (forbiddenFams s.E s.Γ).filter
    (fun F => (F ∩ gammaBetween s.Γ T T).Nonempty)

open scoped Classical in
/-- For a pairwise-disjoint family `C` of edge sets inside `Γ`, the chance that
every member is entirely selected is `∏_{F ∈ C} p^{|F|}`. -/
theorem bernoulliPr_all_subsets (s : BlockState V) (M : ℕ) (p : ℝ)
    (C : Finset (Finset (Edge V))) (hCΓ : ∀ F ∈ C, F ⊆ s.Γ)
    (hCd : PairwiseDisjointFam C) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          ∀ F ∈ C, F ⊆ sampleP s M σ))
      = ∏ F ∈ C, p ^ F.card := by
  classical
  have hset : (Finset.univ.filter
      (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ∀ F ∈ C, F ⊆ sampleP s M σ))
      = Finset.univ.filter (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ∀ j ∈ (C.biUnion id).image (padEmb V M), σ j = true) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h j hj
      obtain ⟨e, he, hej⟩ := Finset.mem_image.mp hj
      obtain ⟨F, hF, heF⟩ := Finset.mem_biUnion.mp he
      have := h F hF heF
      rw [← hej]
      exact (Finset.mem_filter.mp this).2
    · intro h F hF e heF
      refine Finset.mem_filter.mpr ⟨hCΓ F hF heF, ?_⟩
      exact h _ (Finset.mem_image.mpr
        ⟨e, Finset.mem_biUnion.mpr ⟨F, hF, heF⟩, rfl⟩)
  rw [hset, bernoulliPr_all_true,
    Finset.card_image_of_injective _ (padEmb V M).injective]
  rw [show (C.biUnion id).card = ∑ F ∈ C, F.card from
    Finset.card_biUnion (fun F hF G hG hne => hCd F hF G hG hne)]
  rw [Finset.prod_pow_eq_pow_sum]

open scoped Classical in
/-- **Kim (59)**: `Pr(|ℱ'(T)| ≥ l) ≤ η^l / l!` with
`η = Σ_{F ∈ Λ∪Δ, F∩Γ(T)≠∅} p^{|F|}`.

If `ℱ'` has `l` members meeting `Γ(T)`, they form a pairwise-disjoint
`l`-family of forbidden configurations entirely inside `X'`; the union bound
over such families is an elementary symmetric polynomial, which
`factorial_mul_esymm_le` bounds by `η^l/l!`. -/
theorem card_kimFamHitting_tail (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (T : Finset V) (l : ℕ) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          l ≤ (kimFamHitting s.E (sampleP s M σ)
            (gammaBetween s.Γ T T)).card))
      ≤ (∑ F ∈ hitFams s T, p ^ F.card) ^ l / (l.factorial : ℝ) := by
  classical
  set Hit : Finset (Finset (Edge V)) := hitFams s T with hHit
  set Idx : Finset (Finset (Finset (Edge V))) :=
    (Hit.powersetCard l).filter (fun C => PairwiseDisjointFam C) with hIdx
  -- Step 1: the event is covered by the disjoint `l`-families.
  have hcover : (Finset.univ.filter
      (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        l ≤ (kimFamHitting s.E (sampleP s M σ)
          (gammaBetween s.Γ T T)).card))
      ⊆ Idx.biUnion (fun C => Finset.univ.filter (fun σ =>
          ∀ F ∈ C, F ⊆ sampleP s M σ)) := by
    intro σ hσ
    obtain ⟨-, hle⟩ := Finset.mem_filter.mp hσ
    obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hle
    have hCF : ∀ F ∈ C, F ∈ kimFam s.E (sampleP s M σ) :=
      fun F hF => (Finset.mem_filter.mp (hCsub hF)).1
    have hCforb : ∀ F ∈ C, IsForbidden s.E (sampleP s M σ) F :=
      fun F hF => mem_forbiddenFams.mp ((kimFam_spec s.E _).1 (hCF F hF))
    refine Finset.mem_biUnion.mpr ⟨C, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, hCcard⟩, ?_⟩
      · intro F hF
        refine Finset.mem_filter.mpr ⟨mem_forbiddenFams.mpr
          ((hCforb F hF).mono (sampleP_subset s M σ)), ?_⟩
        exact (Finset.mem_filter.mp (hCsub hF)).2
      · intro F hF G hG hne
        exact (kimFam_spec s.E _).2.1 F (hCF F hF) G (hCF G hG) hne
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        fun F hF => (hCforb F hF).1⟩
  -- Step 2: each disjoint family has probability `∏ p^{|F|}`.
  have hper : ∀ C ∈ Idx,
      bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          ∀ F ∈ C, F ⊆ sampleP s M σ)) = ∏ F ∈ C, p ^ F.card := by
    intro C hC
    obtain ⟨hCsub, hCd⟩ := Finset.mem_filter.mp hC
    refine bernoulliPr_all_subsets s M p C (fun F hF => ?_) hCd
    have := (Finset.mem_powersetCard.mp hCsub).1 hF
    exact (mem_forbiddenFams.mp (Finset.mem_filter.mp this).1).1
  -- Step 3: sum over all `l`-subsets and apply the symmetric-function bound.
  refine le_trans (bernoulliPr_mono hp0 hp1 hcover) ?_
  refine le_trans (bernoulliPr_biUnion_le hp0 hp1 _ _) ?_
  rw [Finset.sum_congr rfl hper]
  have hnn : ∀ F : Finset (Edge V), (0 : ℝ) ≤ p ^ F.card :=
    fun F => pow_nonneg hp0 _
  have hext : ∑ C ∈ Idx, ∏ F ∈ C, p ^ F.card
      ≤ ∑ C ∈ Hit.powersetCard l, ∏ F ∈ C, p ^ F.card := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro C _ _
    exact Finset.prod_nonneg fun F _ => hnn F
  refine le_trans hext ?_
  have hfac := factorial_mul_esymm_le (fun F : Finset (Edge V) => p ^ F.card)
    hnn Hit l
  have hfacpos : (0 : ℝ) < (l.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos l
  rw [le_div_iff₀ hfacpos]
  linarith

open scoped Classical in
/-- A `T` that survives into `𝒯'` has no `G'`-edge inside it, hence
`G' ∩ Γ(T) = ∅`. -/
lemma mem_calT_gives_empty (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) {T : Finset V}
    (hT : T ∈ calT (blockStepP s M σ)) :
    ∀ e ∈ (blockStepP s M σ).G, e ∉ gammaBetween s.Γ T T := by
  classical
  obtain ⟨-, -, hno⟩ := Finset.mem_filter.mp hT
  intro e heG heΓ
  obtain ⟨-, v, hvT, w, hwT, hvw, hve, hwe⟩ := Finset.mem_filter.mp heΓ
  exact hno e heG ⟨v, hvT, w, hwT, hvw, hve, hwe⟩

open scoped Classical in
/-- **Kim (57)**: the chance that a given `t`-set survives is bounded by the
lower tail of `|X'∩Γ(T)|` plus the upper tail of `|ℱ'(T)|`.

If `T` survives then `|X'∩Γ(T)| ≤ 3|ℱ'(T)|`, so either `ℱ'(T)` is large or
`|X'∩Γ(T)|` is small. -/
theorem calT_mem_prob (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (T : Finset V) (l : ℕ) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          T ∈ calT (blockStepP s M σ)))
      ≤ bernoulliPr p (Finset.univ.filter
          (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
            ((gammaBetween s.Γ T T ∩ sampleP s M σ).card : ℝ) ≤ 3 * l))
        + (∑ F ∈ hitFams s T, p ^ F.card) ^ l / (l.factorial : ℝ) := by
  classical
  refine le_trans (bernoulliPr_mono hp0 hp1 (?_ :
      (Finset.univ.filter (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        T ∈ calT (blockStepP s M σ)))
      ⊆ (Finset.univ.filter (fun σ =>
          ((gammaBetween s.Γ T T ∩ sampleP s M σ).card : ℝ) ≤ 3 * l))
        ∪ (Finset.univ.filter (fun σ =>
          l ≤ (kimFamHitting s.E (sampleP s M σ)
            (gammaBetween s.Γ T T)).card)))) ?_
  · intro σ hσ
    obtain ⟨-, hT⟩ := Finset.mem_filter.mp hσ
    by_cases hbig : l ≤ (kimFamHitting s.E (sampleP s M σ)
        (gammaBetween s.Γ T T)).card
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbig⟩)
    · push_neg at hbig
      refine Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      have hkey := card_sample_inter_le_three_mul s M σ T
        (mem_calT_gives_empty s M σ hT)
      have hnat : (gammaBetween s.Γ T T ∩ sampleP s M σ).card ≤ 3 * l := by
        omega
      have : ((gammaBetween s.Γ T T ∩ sampleP s M σ).card : ℝ)
          ≤ ((3 * l : ℕ) : ℝ) := by exact_mod_cast hnat
      rw [show ((3 * l : ℕ) : ℝ) = 3 * (l : ℝ) by push_cast; ring] at this
      exact this
  refine le_trans (bernoulliPr_union_le hp0 hp1 _ _) ?_
  have := card_kimFamHitting_tail s M hp0 hp1 T l
  linarith

open scoped Classical in
open scoped Classical in
/-- `|Γ(T) ∩ X'|` is the number of `true` coordinates among `Γ(T)`'s. -/
lemma card_gammaT_inter_sample_eq (s : BlockState V) (M : ℕ)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) (T : Finset V) :
    ((gammaBetween s.Γ T T ∩ sampleP s M σ).card : ℝ)
      = ∑ j ∈ (gammaBetween s.Γ T T).image (padEmb V M),
          (if σ j = true then (1 : ℝ) else 0) := by
  classical
  have hL : gammaBetween s.Γ T T ∩ sampleP s M σ
      = (gammaBetween s.Γ T T).filter (fun e => σ (padEmb V M e) = true) := by
    ext e
    simp only [Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨he, hs⟩
      exact ⟨he, (mem_sampleP.mp hs).2⟩
    · rintro ⟨he, hs⟩
      exact ⟨he, mem_sampleP.mpr ⟨(mem_gammaBetween.mp he).1, hs⟩⟩
  have hR : ∑ j ∈ (gammaBetween s.Γ T T).image (padEmb V M),
      (if σ j = true then (1 : ℝ) else 0)
      = ((((gammaBetween s.Γ T T).image (padEmb V M)).filter
          (fun j => σ j = true)).card : ℝ) := by
    rw [Finset.card_filter]; push_cast; rfl
  have hIm : ((gammaBetween s.Γ T T).image (padEmb V M)).filter
      (fun j => σ j = true)
      = ((gammaBetween s.Γ T T).filter
          (fun e => σ (padEmb V M e) = true)).image (padEmb V M) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hσ⟩
      exact ⟨e, ⟨he, hσ⟩, rfl⟩
    · rintro ⟨e, ⟨he, hσ⟩, rfl⟩
      exact ⟨⟨e, he, rfl⟩, hσ⟩
  rw [hL, hR, hIm, Finset.card_image_of_injective _ (padEmb V M).injective]

open scoped Classical in
/-- **Kim's per-`T` survival bound (§4.9).** A `t`-set stays in `𝒯` only if it
received few sampled edges — a binomial lower tail — or a whole forbidden
family was sampled. -/
theorem calT_mem_prob_le (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (T : Finset V) (l : ℕ) {ρ : ℝ} (hρ : ρ < 0)
    {W : ℝ} (hW : (∑ F ∈ hitFams s T, p ^ F.card) ≤ W) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          T ∈ calT (blockStepP s M σ)))
      ≤ ((1 - p) + p * Real.exp ρ) ^ (gammaBetween s.Γ T T).card
          / Real.exp (ρ * (3 * l))
        + W ^ l / (l.factorial : ℝ) := by
  classical
  refine le_trans (calT_mem_prob s M hp0 hp1 T l) ?_
  refine add_le_add ?_ ?_
  · have hset : (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          ((gammaBetween s.Γ T T ∩ sampleP s M σ).card : ℝ) ≤ 3 * l))
        = Finset.univ.filter
          (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
            (∑ j ∈ (gammaBetween s.Γ T T).image (padEmb V M),
              (if σ j = true then (1 : ℝ) else 0)) ≤ 3 * l) := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [card_gammaT_inter_sample_eq]
    rw [hset]
    refine le_trans (bernoulliPr_count_le_mgf hp0 hp1
      ((gammaBetween s.Γ T T).image (padEmb V M)) hρ) ?_
    rw [Finset.card_image_of_injective _ (padEmb V M).injective]
  · have hnn : (0 : ℝ) ≤ ∑ F ∈ hitFams s T, p ^ F.card :=
      Finset.sum_nonneg fun F _ => pow_nonneg hp0 _
    have hpow : (∑ F ∈ hitFams s T, p ^ F.card) ^ l ≤ W ^ l :=
      pow_le_pow_left₀ hnn hW l
    have hfac : (0 : ℝ) < (l.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos l
    have hstep := mul_le_mul_of_nonneg_right hpow
      (le_of_lt (inv_pos.mpr hfac))
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact hstep

open scoped Classical in
/-- **Kim (55)**: `E[|𝒯'|] = Σ_{T ∈ 𝒯} Pr(T ∈ 𝒯')`.

The sum runs over `𝒯_k`, not over all `t`-sets: that is what lets Property 8 at
stage `k` be fed in, so the exponential factor accumulates from stage to
stage. -/
theorem expectation_card_calT (s : BlockState V) (M : ℕ) (p : ℝ) :
    bernoulliExp p (fun σ => ((calT (blockStepP s M σ)).card : ℝ))
      = ∑ T ∈ calT s,
          bernoulliPr p (Finset.univ.filter
            (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
              T ∈ calT (blockStepP s M σ))) := by
  classical
  have hpt : ∀ σ : Fin (Fintype.card (Coord V M)) → Bool,
      ((calT (blockStepP s M σ)).card : ℝ)
        = ∑ T ∈ calT s, (if σ ∈ Finset.univ.filter
            (fun τ : Fin (Fintype.card (Coord V M)) → Bool =>
              T ∈ calT (blockStepP s M τ)) then (1 : ℝ) else 0) := by
    intro σ
    rw [show (∑ T ∈ calT s, (if σ ∈ Finset.univ.filter
        (fun τ : Fin (Fintype.card (Coord V M)) → Bool =>
          T ∈ calT (blockStepP s M τ)) then (1 : ℝ) else 0))
      = ∑ T ∈ calT s, (if T ∈ calT (blockStepP s M σ) then (1 : ℝ) else 0)
      from Finset.sum_congr rfl fun T _ => by
        by_cases h : T ∈ calT (blockStepP s M σ) <;> simp [h]]
    rw [Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr (calT_blockStepP_subset s M σ),
      Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [funext hpt, bernoulliExp_sum]
  exact Finset.sum_congr rfl fun T _ => (bernoulliPr_eq_exp p _).symm

open scoped Classical in
/-- **Property 8 survives one block step.**

Kim §4.9: `E[|𝒯'|] = Σ_{T ∈ 𝒯} Pr(T ∈ 𝒯') ≤ |𝒯_k|·B` with `B` the per-`T`
survival bound of (56); Property 8 at stage `k` bounds `|𝒯_k|`, and Markov's
inequality at threshold `n` turns this into `Pr(…) ≤ 1/n`. -/
theorem property8_prob (k : ℕ) (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) {B : ℝ} (hB0 : 0 < B)
    (hper : ∀ T ∈ calT s, bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          T ∈ calT (blockStepP s M σ))) ≤ B)
    (htarget : (n : ℝ) * (((calT s).card : ℝ) * B)
      ≤ (n : ℝ) ^ (k + 1) * (Nat.choose (Fintype.card V) (tParam n))
        * Real.exp (-(1 - kimEps n)
            * ∑ j ∈ Finset.range (k + 1),
                bSeq n j * μSeq n j * theta n / Real.sqrt n
                  * ((tParam n).choose 2))) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          ¬ Property8 (blockStepP s M σ) (k + 1))) ≤ 1 / n := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rcases Finset.eq_empty_or_nonempty (calT s) with hemp | hne
  · -- `𝒯_k = ∅` forces `𝒯' = ∅`, and Property 8 then holds outright
    have hall : ∀ σ : Fin (Fintype.card (Coord V M)) → Bool,
        Property8 (blockStepP s M σ) (k + 1) := by
      intro σ
      have hE : calT (blockStepP s M σ) = ∅ :=
        Finset.eq_empty_of_forall_notMem fun T hT => by
          have := calT_blockStepP_subset s M σ hT
          rw [hemp] at this
          exact absurd this (Finset.notMem_empty T)
      rw [Property8, hE, Finset.card_empty]
      push_cast
      positivity
    rw [show (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          ¬ Property8 (blockStepP s M σ) (k + 1))) = ∅ from
      Finset.eq_empty_of_forall_notMem fun σ hσ =>
        (Finset.mem_filter.mp hσ).2 (hall σ), bernoulliPr_empty]
    positivity
  · have hcardpos : (0 : ℝ) < ((calT s).card : ℝ) := by
      have : 0 < (calT s).card := Finset.card_pos.mpr hne
      exact_mod_cast this
    have hmean : bernoulliExp p (fun σ => ((calT (blockStepP s M σ)).card : ℝ))
        ≤ ((calT s).card : ℝ) * B := by
      rw [expectation_card_calT]
      calc ∑ T ∈ calT s,
            bernoulliPr p (Finset.univ.filter
              (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
                T ∈ calT (blockStepP s M σ)))
          ≤ ∑ _T ∈ calT s, B := Finset.sum_le_sum fun T hT => hper T hT
        _ = ((calT s).card : ℝ) * B := by
            rw [Finset.sum_const, nsmul_eq_mul]
    refine bernoulliPr_markov hp0 hp1 _ (fun σ => Nat.cast_nonneg _) hnR
      (by positivity) hmean _ ?_
    intro σ hσ
    obtain ⟨-, hfail⟩ := Finset.mem_filter.mp hσ
    rw [Property8] at hfail
    push_neg at hfail
    linarith


/-- `|Edge V| ≤ n²`: an edge is determined by its two endpoints. -/
lemma card_Edge_le_sq : Fintype.card (Edge V) ≤ n * n := by
  classical
  have hmaps : ∀ e ∈ (Finset.univ : Finset (Edge V)),
      edgeVerts e ∈ Finset.powersetCard 2 (Finset.univ : Finset V) :=
    fun e _ => Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, edgeVerts_card e⟩
  have h := Finset.card_le_card_of_injOn edgeVerts hmaps
    (fun a _ b _ hab => edgeVerts_injective hab)
  rw [Finset.card_powersetCard, Finset.card_univ] at h
  rw [Finset.card_univ] at h
  refine le_trans h ?_
  rw [Nat.choose_two_right]
  exact le_trans (Nat.div_le_self _ 2)
    (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

/-- Each `Δ`-edge at `w` is determined by its far endpoint, which closes a
`Γ`-triangle on `e_vw`. -/
lemma card_deltaEdgesAt_le (s : BlockState V) (v w : V) :
    (deltaEdgesAt s v w).card ≤ codegEdges s.Γ v w := by
  classical
  rw [codegEdges]
  refine Finset.card_le_card_of_injOn (otherEndOf w) ?_ ?_
  · intro f hf
    exact (Finset.mem_filter.mp hf).2
  · intro f hf f' hf' hEq
    refine otherEndOf_injOn s.Γ w ?_ ?_ hEq
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hf)).1
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hf')).1

/-- **Kim's `E[Φ⁽²⁾_{v,w}] = p·d_Δ(e_vw) ≤ b²θ√n`** (§4.5), from Property 5. -/
lemma edgeProb_mul_deltaEdgesAt_le (s : BlockState V) (k : ℕ) (e : Edge V)
    (v : V) (he : e ∈ s.Γ) (hv : v ∈ edgeVerts e) (hn : 0 < n)
    (h5 : Property5 s k) :
    edgeProb n * ((deltaEdgesAt s v (otherEndOf v e)).card : ℝ)
      ≤ bSeq n k ^ 2 * theta n * Real.sqrt n := by
  classical
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hve : v ∈ e.val := mem_edgeVerts.mp hv
  set w : V := otherEndOf v e with hw
  have hspec : e.val = s(v, w) := edge_eq_of_otherEndOf hve
  have hvw : v ≠ w := by
    intro hEq
    exact e.2 (by rw [hspec, ← hEq]; simp)
  have hmk : mkEdge hvw = e := Subtype.ext (by rw [mkEdge_val, hspec])
  have h5' : (codegEdges s.Γ v w : ℝ) ≤ bSeq n k ^ 2 * n :=
    h5 v w hvw (by rw [hmk]; exact he)
  calc edgeProb n * ((deltaEdgesAt s v w).card : ℝ)
      ≤ edgeProb n * ((codegEdges s.Γ v w : ℕ) : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ hp0
        exact_mod_cast card_deltaEdgesAt_le s v w
    _ ≤ edgeProb n * (bSeq n k ^ 2 * n) := mul_le_mul_of_nonneg_left h5' hp0
    _ = bSeq n k ^ 2 * theta n * Real.sqrt n := by
        have hdiv : (n : ℝ) / Real.sqrt n = Real.sqrt n := Real.div_sqrt
        rw [edgeProb]
        calc theta n / Real.sqrt n * (bSeq n k ^ 2 * n)
            = bSeq n k ^ 2 * theta n * ((n : ℝ) / Real.sqrt n) := by ring
          _ = bSeq n k ^ 2 * theta n * Real.sqrt n := by rw [hdiv]

/-- **Kim's (26) consequence**: two `Λ`-partner sets at the *same* endpoint meet
in at most `|N_ℰ(w) ∩ N_ℰ(w')|` edges, which Property 3 bounds by `3k log n`. -/
lemma card_lambdaAt_inter_same_le (s : BlockState V) (e g : Edge V) (v : V) :
    (lambdaAt s e v ∩ lambdaAt s g v).card
      ≤ (commonNbrs s.E (otherEndOf v e) (otherEndOf v g)).card := by
  classical
  refine Finset.card_le_card_of_injOn (otherEndOf v) ?_ ?_
  · intro f hf
    obtain ⟨hfe, hfg⟩ := Finset.mem_inter.mp hf
    obtain ⟨⟨hfΓ, hvf⟩, hende⟩ := mem_lambdaAt.mp hfe
    obtain ⟨-, hendg⟩ := mem_lambdaAt.mp hfg
    rw [commonNbrs_eq_inter]
    exact Finset.mem_inter.mpr ⟨hende, hendg⟩
  · intro f hf f' hf' hEq
    refine otherEndOf_injOn s.Γ v ?_ ?_ hEq
    · exact Finset.mem_coe.mpr (lambdaAt_subset_edgesAt s e v
        (Finset.mem_inter.mp (Finset.mem_coe.mp hf)).1)
    · exact Finset.mem_coe.mpr (lambdaAt_subset_edgesAt s e v
        (Finset.mem_inter.mp (Finset.mem_coe.mp hf')).1)

/-- `Λ`-partner sets at *different* endpoints meet in at most one edge: any
common member joins those two vertices. -/
lemma card_lambdaAt_inter_diff_le (s : BlockState V) (e g : Edge V) {u v : V}
    (huv : u ≠ v) : (lambdaAt s e v ∩ lambdaAt s g u).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr fun f hf f' hf' => ?_
  obtain ⟨hfe, hfg⟩ := Finset.mem_inter.mp hf
  obtain ⟨hf'e, hf'g⟩ := Finset.mem_inter.mp hf'
  have hvf : v ∈ f.val := (mem_lambdaAt.mp hfe).1.2
  have huf : u ∈ f.val := (mem_lambdaAt.mp hfg).1.2
  have hvf' : v ∈ f'.val := (mem_lambdaAt.mp hf'e).1.2
  have huf' : u ∈ f'.val := (mem_lambdaAt.mp hf'g).1.2
  exact Subtype.ext (by
    rw [edge_eq_of_two_mem hvf huf (Ne.symm huv),
      edge_eq_of_two_mem hvf' huf' (Ne.symm huv)])

open scoped Classical in
/-- **Kim's `c_e ≤ 1 + 3k log n`** for Property 4 (§4.5), in the form
`c_e ≤ C + 2` where `C` bounds every `ℰ`-codegree.

A coordinate `g` affects only those `Λ`-partners of `e` at `v` that are also
`Λ`-partners of `g`. At the shared endpoint `v` that intersection is bounded by
an `ℰ`-codegree — Kim's (26); at the other endpoint it has at most one
element. -/
lemma card_filter_lambdaAt_le (s : BlockState V) (M : ℕ) (e : Edge V) (v : V)
    (hv : v ∈ edgeVerts e) {C : ℝ} (hC0 : 0 ≤ C)
    (hbound : ∀ w w' : V, w ≠ w' → ((commonNbrs s.E w w').card : ℝ) ≤ C)
    (j : Fin (Fintype.card (Coord V M)))
    (hjne : j ≠ coordEquiv V M (Sum.inl e)) :
    (((lambdaAt s e v).filter (fun f =>
      j ∈ (lambdaStar s M f).image (coordEquiv V M))).card : ℝ) ≤ C + 2 := by
  classical
  set S : Finset (Edge V) := lambdaAt s e v with hS
  set c : Coord V M := (coordEquiv V M).symm j with hc
  have hj : j = coordEquiv V M c := by rw [hc]; simp
  cases hcase : c with
  | inr q =>
      have hsub : (S.filter (fun f =>
          j ∈ (lambdaStar s M f).image (coordEquiv V M))) ⊆ {q.1} := by
        intro f hf
        obtain ⟨-, hjmem⟩ := Finset.mem_filter.mp hf
        obtain ⟨d, hd, hdj⟩ := Finset.mem_image.mp hjmem
        have hdc : d = c := (coordEquiv V M).injective (by rw [hdj, hj])
        obtain ⟨u, -, hu⟩ := mem_lambdaStar.mp hd
        rcases Finset.mem_union.mp hu with h1 | h1
        · obtain ⟨y, -, hy⟩ := Finset.mem_image.mp h1
          rw [hdc, hcase] at hy
          exact absurd hy (by simp)
        · obtain ⟨i, hi⟩ := mem_padAt h1
          rw [hdc, hcase] at hi
          exact Finset.mem_singleton.mpr
            (congrArg (fun z => z.1) (Sum.inr_injective hi)).symm
      calc ((S.filter (fun f =>
            j ∈ (lambdaStar s M f).image (coordEquiv V M))).card : ℝ)
          ≤ (({q.1} : Finset (Edge V)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ = 1 := by simp
        _ ≤ C + 2 := by linarith
  | inl g =>
      have hsub : (S.filter (fun f =>
          j ∈ (lambdaStar s M f).image (coordEquiv V M)))
          ⊆ (edgeVerts g).biUnion (fun u => S ∩ lambdaAt s g u) := by
        intro f hf
        obtain ⟨hfS, hjmem⟩ := Finset.mem_filter.mp hf
        obtain ⟨d, hd, hdj⟩ := Finset.mem_image.mp hjmem
        have hdc : d = c := (coordEquiv V M).injective (by rw [hdj, hj])
        obtain ⟨u, huf, hu⟩ := mem_lambdaStar.mp hd
        rcases Finset.mem_union.mp hu with h1 | h1
        · obtain ⟨y, hy, hyd⟩ := Finset.mem_image.mp h1
          have hyg : y = g := Sum.inl_injective (by rw [hyd, hdc, hcase])
          subst hyg
          obtain ⟨⟨hyΓ, hvy⟩, -⟩ := mem_lambdaAt.mp hy
          have hfΓ : f ∈ s.Γ := (mem_lambdaAt.mp hfS).1.1
          exact Finset.mem_biUnion.mpr ⟨u, mem_edgeVerts.mpr hvy,
            Finset.mem_inter.mpr ⟨hfS,
              lambdaAt_symm hfΓ (mem_edgeVerts.mp huf) hy⟩⟩
        · obtain ⟨i, hi⟩ := mem_padAt h1
          rw [hdc, hcase] at hi
          exact absurd hi (by simp)
      have hstep : ((S.filter (fun f =>
          j ∈ (lambdaStar s M f).image (coordEquiv V M))).card : ℝ)
          ≤ ∑ u ∈ edgeVerts g, ((S ∩ lambdaAt s g u).card : ℝ) := by
        have h1 := le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
        calc ((S.filter (fun f =>
              j ∈ (lambdaStar s M f).image (coordEquiv V M))).card : ℝ)
            ≤ ((∑ u ∈ edgeVerts g, (S ∩ lambdaAt s g u).card : ℕ) : ℝ) := by
              exact_mod_cast h1
          _ = _ := by push_cast; ring
      refine hstep.trans ?_
      -- split the two endpoints: the shared one gives an `ℰ`-codegree, the
      -- other at most one edge
      rw [← Finset.sum_filter_add_sum_filter_not (edgeVerts g) (fun u => u = v)]
      refine add_le_add ?_ ?_
      · have hcard1 : (((edgeVerts g).filter (fun u => u = v)).card : ℝ) ≤ 1 := by
          have : ((edgeVerts g).filter (fun u => u = v)) ⊆ {v} := by
            intro u hu
            exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hu).2
          calc (((edgeVerts g).filter (fun u => u = v)).card : ℝ)
              ≤ (({v} : Finset V).card : ℝ) := by
                exact_mod_cast Finset.card_le_card this
            _ = 1 := by simp
        refine le_trans (Finset.sum_le_sum
          (g := fun _ : V => C) fun u hu => ?_) ?_
        · have huv : u = v := (Finset.mem_filter.mp hu).2
          have hug : u ∈ edgeVerts g := (Finset.mem_filter.mp hu).1
          subst huv
          have hne : e ≠ g := by
            intro hEq
            exact hjne (by rw [hj, hcase, hEq])
          calc ((S ∩ lambdaAt s g u).card : ℝ)
              ≤ ((commonNbrs s.E (otherEndOf u e) (otherEndOf u g)).card : ℝ) := by
                exact_mod_cast card_lambdaAt_inter_same_le s e g u
            _ ≤ C := hbound _ _ (otherEndOf_ne_of_ne (mem_edgeVerts.mp hv)
                  (mem_edgeVerts.mp hug) hne)
        · rw [Finset.sum_const, nsmul_eq_mul]
          nlinarith [hcard1, hC0]
      · have hcard2 : (((edgeVerts g).filter (fun u => ¬ u = v)).card : ℝ)
            ≤ 2 := by
          calc (((edgeVerts g).filter (fun u => ¬ u = v)).card : ℝ)
              ≤ ((edgeVerts g).card : ℝ) := by
                exact_mod_cast Finset.card_filter_le _ _
            _ = 2 := by rw [edgeVerts_card]; norm_num
        refine le_trans (Finset.sum_le_sum
          (g := fun _ : V => (1 : ℝ)) fun u hu => ?_) ?_
        · have huv : u ≠ v := (Finset.mem_filter.mp hu).2
          show ((S ∩ lambdaAt s g u).card : ℝ) ≤ 1
          rw [hS]
          exact_mod_cast card_lambdaAt_inter_diff_le s e g huv
        · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          exact hcard2


lemma IsTriangle.ne12 {e f g : Edge V} (h : IsTriangle e f g) : e ≠ f := by
  obtain ⟨a, b, c, hab, hbc, hac, heq, hfeq, -⟩ := h
  intro hc
  rw [hc, hfeq] at heq
  have : a ∈ ({b, c} : Finset V) := by
    have hm : a ∈ (s(b, c) : Sym2 V) := by rw [heq]; simp
    simpa using hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h' | h'
  · exact hab h'
  · exact hac h'

lemma IsTriangle.ne13 {e f g : Edge V} (h : IsTriangle e f g) : e ≠ g := by
  obtain ⟨a, b, c, hab, hbc, hac, heq, -, hgeq⟩ := h
  intro hcon
  rw [hcon, hgeq] at heq
  have hm : b ∈ (s(a, c) : Sym2 V) := by rw [heq]; simp
  have : b ∈ ({a, c} : Finset V) := by simpa using hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h' | h'
  · exact hab h'.symm
  · exact hbc h'

lemma IsTriangle.ne23 {e f g : Edge V} (h : IsTriangle e f g) : f ≠ g :=
  h.swap12.ne13

open scoped Classical in
/-- The forbidden configurations through a fixed edge. -/
noncomputable def famsThrough (s : BlockState V) (e : Edge V) :
    Finset (Finset (Edge V)) := by
  classical
  exact (forbiddenFams s.E s.Γ).filter (fun F => e ∈ F)

lemma mem_famsThrough {s : BlockState V} {e : Edge V} {F : Finset (Edge V)} :
    F ∈ famsThrough s e ↔ IsForbidden s.E s.Γ F ∧ e ∈ F := by
  classical
  show F ∈ Finset.filter _ _ ↔ _
  rw [Finset.mem_filter, mem_forbiddenFams]

open scoped Classical in
/-- Every forbidden family meeting `Γ(T)` passes through one of its edges. -/
lemma hitFams_subset_biUnion (s : BlockState V) (T : Finset V) :
    hitFams s T ⊆ (gammaBetween s.Γ T T).biUnion (famsThrough s) := by
  classical
  intro F hF
  have hF' : F ∈ (forbiddenFams s.E s.Γ).filter
      (fun F => (F ∩ gammaBetween s.Γ T T).Nonempty) := hF
  obtain ⟨hFf, hne⟩ := Finset.mem_filter.mp hF'
  obtain ⟨e, he⟩ := hne
  obtain ⟨heF, heT⟩ := Finset.mem_inter.mp he
  exact Finset.mem_biUnion.mpr ⟨e, heT,
    mem_famsThrough.mpr ⟨mem_forbiddenFams.mp hFf, heF⟩⟩

open scoped Classical in
/-- **The two-edge configurations through `e` are indexed by `e`'s
`Λ`-partners.** If `{e, f}` is forbidden through an `ℰ`-edge `g`, then `f` is a
`Γ`-edge at an endpoint `v` of `e` whose far end is `ℰ`-adjacent to the other
endpoint — that is, `f ∈ N_Λ(e, v)`. -/
lemma famsThrough_two_subset (s : BlockState V) (e : Edge V) :
    (famsThrough s e).filter (fun F => F.card = 2)
      ⊆ ((edgeVerts e).biUnion (fun v => lambdaAt s e v)).image
          (fun f => ({e, f} : Finset (Edge V))) := by
  classical
  intro F hF
  obtain ⟨hFm, hcard⟩ := Finset.mem_filter.mp hF
  obtain ⟨hforb, heF⟩ := mem_famsThrough.mp hFm
  obtain ⟨hFΓ, hcase⟩ := hforb
  rcases hcase with ⟨e₁, e₂, hFeq, g, hgE, htri⟩ | ⟨e₁, e₂, e₃, hFeq, htri⟩
  · -- pair case: normalise so that `e = e₁`
    have hkey : ∀ (x y : Edge V), F = {x, y} → e = x →
        ∀ (gg : Edge V), gg ∈ s.E → IsTriangle x y gg →
        F ∈ ((edgeVerts e).biUnion (fun v => lambdaAt s e v)).image
          (fun f => ({e, f} : Finset (Edge V))) := by
      intro x y hFxy hex gg hggE htri'
      obtain ⟨a, b, c, hab, hbc, hac, hxeq, hyeq, hgeq⟩ := htri'
      have hyΓ : y ∈ s.Γ := hFΓ (by rw [hFxy]; simp)
      have hbx : b ∈ x.val := by rw [hxeq]; simp
      have hby : b ∈ y.val := by rw [hyeq]; simp
      have hbe : b ∈ edgeVerts e := by rw [hex]; exact mem_edgeVerts.mpr hbx
      have hoe : otherEndOf b e = a := by
        rw [hex]
        have hh := eq_otherEndOf_of_mem hbx (by rw [hxeq]; simp : a ∈ x.val) hab
        exact hh.symm
      have hoy : otherEndOf b y = c := by
        have hh := eq_otherEndOf_of_mem hby
          (by rw [hyeq]; simp : c ∈ y.val) (Ne.symm hbc)
        exact hh.symm
      have hcn : c ∈ nbrs s.E a := by
        refine mem_nbrs.mpr ⟨hac.symm, gg, hggE, ?_, ?_⟩
        · rw [hgeq]; simp
        · rw [hgeq]; simp
      refine Finset.mem_image.mpr ⟨y, Finset.mem_biUnion.mpr ⟨b, hbe, ?_⟩, ?_⟩
      · refine mem_lambdaAt.mpr ⟨⟨hyΓ, hby⟩, ?_⟩
        rw [hoy, hoe]; exact hcn
      · rw [hFxy, hex]
    rcases (by
      have : e ∈ ({e₁, e₂} : Finset (Edge V)) := by rw [← hFeq]; exact heF
      simpa using this : e = e₁ ∨ e = e₂) with hee | hee
    · exact hkey e₁ e₂ hFeq hee g hgE htri
    · refine hkey e₂ e₁ ?_ hee g hgE htri.swap12
      rw [hFeq]; exact Finset.pair_comm _ _
  · -- triple case: the card is 3, contradicting `hcard`
    exfalso
    have h12 := htri.ne12
    have h13 := htri.ne13
    have h23 := htri.ne23
    rw [hFeq, Finset.card_insert_of_notMem (by simp [h12, h13]),
      Finset.card_insert_of_notMem (by simp [h23]),
      Finset.card_singleton] at hcard
    omega

open scoped Classical in
/-- Any edge inside a triangle's vertex set is one of the triangle's edges. -/
lemma mem_of_edgeVerts_subset {e₁ e₂ e₃ : Edge V} {a b c : V}
    (huv : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h1 : e₁.val = s(a, b)) (h2 : e₂.val = s(b, c)) (h3 : e₃.val = s(a, c))
    {x : Edge V} (hx : edgeVerts x ⊆ ({a, b, c} : Finset V)) :
    x ∈ ({e₁, e₂, e₃} : Finset (Edge V)) := by
  classical
  obtain ⟨z, hz⟩ := x
  induction z using Sym2.ind with
  | _ u v =>
    have hne : u ≠ v := by simpa using hz
    have hu : u ∈ ({a, b, c} : Finset V) :=
      hx (mem_edgeVerts.mpr (by simp))
    have hv : v ∈ ({a, b, c} : Finset V) :=
      hx (mem_edgeVerts.mpr (by simp))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    have key : (⟨s(u, v), hz⟩ : Edge V) = e₁
        ∨ (⟨s(u, v), hz⟩ : Edge V) = e₂
        ∨ (⟨s(u, v), hz⟩ : Edge V) = e₃ := by
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
      · exact absurd rfl hne
      · exact Or.inl (Subtype.ext (by rw [h1]))
      · exact Or.inr (Or.inr (Subtype.ext (by rw [h3])))
      · exact Or.inl (Subtype.ext (by rw [h1]; exact Sym2.eq_swap))
      · exact absurd rfl hne
      · exact Or.inr (Or.inl (Subtype.ext (by rw [h2])))
      · exact Or.inr (Or.inr (Subtype.ext (by rw [h3]; exact Sym2.eq_swap)))
      · exact Or.inr (Or.inl (Subtype.ext (by rw [h2]; exact Sym2.eq_swap)))
      · exact absurd rfl hne
    rcases key with h | h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))

open scoped Classical in
/-- A triangle's vertex set is exactly `{a, b, c}`. -/
lemma triangle_biUnion_edgeVerts {e₁ e₂ e₃ : Edge V} {a b c : V}
    (h1 : e₁.val = s(a, b)) (h2 : e₂.val = s(b, c)) (h3 : e₃.val = s(a, c)) :
    ({e₁, e₂, e₃} : Finset (Edge V)).biUnion edgeVerts
      = ({a, b, c} : Finset V) := by
  classical
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hxv : x ∈ y.val := mem_edgeVerts.mp hxy
    rcases hy with rfl | rfl | rfl
    · rw [h1] at hxv
      have hd : x = a ∨ x = b := by simpa using hxv
      tauto
    · rw [h2] at hxv
      have hd : x = b ∨ x = c := by simpa using hxv
      tauto
    · rw [h3] at hxv
      have hd : x = a ∨ x = c := by simpa using hxv
      tauto
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨e₁, Or.inl rfl, mem_edgeVerts.mpr (by rw [h1]; simp)⟩
    · exact ⟨e₁, Or.inl rfl, mem_edgeVerts.mpr (by rw [h1]; simp)⟩
    · exact ⟨e₂, Or.inr (Or.inl rfl), mem_edgeVerts.mpr (by rw [h2]; simp)⟩

open scoped Classical in
/-- **A triangle is determined by its vertex set.** -/
lemma triangle_eq_of_biUnion_eq {F F' : Finset (Edge V)}
    (hF : ∃ e₁ e₂ e₃ : Edge V, F = {e₁, e₂, e₃} ∧ IsTriangle e₁ e₂ e₃)
    (hF' : ∃ e₁ e₂ e₃ : Edge V, F' = {e₁, e₂, e₃} ∧ IsTriangle e₁ e₂ e₃)
    (h : F.biUnion edgeVerts = F'.biUnion edgeVerts) : F = F' := by
  classical
  have key : ∀ (G G' : Finset (Edge V)),
      (∃ e₁ e₂ e₃ : Edge V, G = {e₁, e₂, e₃} ∧ IsTriangle e₁ e₂ e₃) →
      (∃ e₁ e₂ e₃ : Edge V, G' = {e₁, e₂, e₃} ∧ IsTriangle e₁ e₂ e₃) →
      G.biUnion edgeVerts = G'.biUnion edgeVerts → G ⊆ G' := by
    intro G G' hG hG' hGG x hx
    obtain ⟨f₁, f₂, f₃, hGeq, ha, hb, hc, hab, hbc, hac, k1, k2, k3⟩ := hG'
    subst hGeq
    refine mem_of_edgeVerts_subset hab hbc hac k1 k2 k3 ?_
    rw [← triangle_biUnion_edgeVerts k1 k2 k3, ← hGG]
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨x, hx, hz⟩
  exact Finset.Subset.antisymm (key F F' hF hF' h) (key F' F hF' hF h.symm)

open scoped Classical in
/-- A forbidden family of cardinality `3` is a triangle. -/
lemma famsThrough_three_triple (s : BlockState V) (e : Edge V)
    {F : Finset (Edge V)}
    (hF : F ∈ (famsThrough s e).filter (fun F => F.card = 3)) :
    ∃ e₁ e₂ e₃ : Edge V, F = {e₁, e₂, e₃} ∧ IsTriangle e₁ e₂ e₃ := by
  classical
  obtain ⟨hFm, hcard⟩ := Finset.mem_filter.mp hF
  obtain ⟨hforb, -⟩ := mem_famsThrough.mp hFm
  obtain ⟨-, hcase⟩ := hforb
  rcases hcase with ⟨x, y, hFeq, g, -, htri⟩ | ⟨e₁, e₂, e₃, hFeq, htri⟩
  · exfalso
    rw [hFeq, Finset.card_insert_of_notMem (by simpa using htri.ne12),
      Finset.card_singleton] at hcard
    omega
  · exact ⟨e₁, e₂, e₃, hFeq, htri⟩

open scoped Classical in
/-- **The three-edge configurations through `e = e_ab` are indexed by the common
`Γ`-neighbours of `a` and `b`** — Property 5's quantity. -/
lemma card_famsThrough_three_le (s : BlockState V) {a b : V} (hab : a ≠ b)
    (e : Edge V) (he : e.val = s(a, b)) :
    ((famsThrough s e).filter (fun F => F.card = 3)).card
      ≤ (commonNbrs s.Γ a b).card := by
  classical
  have hmain : ((famsThrough s e).filter (fun F => F.card = 3)).card
      ≤ ((commonNbrs s.Γ a b).image
          (fun c => ({a, b, c} : Finset V))).card := by
   refine Finset.card_le_card_of_injOn (fun F => F.biUnion edgeVerts) ?_ ?_
   · intro F hF
     obtain ⟨e₁, e₂, e₃, hFeq, htri⟩ := famsThrough_three_triple s e hF
     obtain ⟨a', b', c', hab', hbc', hac', k1, k2, k3⟩ := htri
     have hW : F.biUnion edgeVerts = ({a', b', c'} : Finset V) := by
       rw [hFeq]; exact triangle_biUnion_edgeVerts k1 k2 k3
     obtain ⟨hFm, -⟩ := Finset.mem_filter.mp hF
     obtain ⟨hforb, heF⟩ := mem_famsThrough.mp hFm
     have hFΓ : F ⊆ s.Γ := hforb.1
     have haW : a ∈ F.biUnion edgeVerts :=
       Finset.mem_biUnion.mpr ⟨e, heF, mem_edgeVerts.mpr (by rw [he]; simp)⟩
     have hbW : b ∈ F.biUnion edgeVerts :=
       Finset.mem_biUnion.mpr ⟨e, heF, mem_edgeVerts.mpr (by rw [he]; simp)⟩
     have hWcard : (F.biUnion edgeVerts).card = 3 := by
       rw [hW, Finset.card_insert_of_notMem (by simp [hab', hac']),
         Finset.card_insert_of_notMem (by simp [hbc']), Finset.card_singleton]
     have hsub : ({a, b} : Finset V) ⊆ F.biUnion edgeVerts := by
       intro z hz
       rcases Finset.mem_insert.mp hz with rfl | hz'
       · exact haW
       · rw [Finset.mem_singleton] at hz'; subst hz'; exact hbW
     have hdiff : ((F.biUnion edgeVerts) \ ({a, b} : Finset V)).card = 1 := by
       have hint : ({a, b} : Finset V) ∩ (F.biUnion edgeVerts)
           = ({a, b} : Finset V) := Finset.inter_eq_left.mpr hsub
       rw [Finset.card_sdiff, hint, hWcard,
         Finset.card_insert_of_notMem (by simpa using hab),
         Finset.card_singleton]
     obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hdiff
     have hcmem : c ∈ (F.biUnion edgeVerts) \ ({a, b} : Finset V) := by
       rw [hc]; exact Finset.mem_singleton_self _
     have hcW : c ∈ F.biUnion edgeVerts := (Finset.mem_sdiff.mp hcmem).1
     have hcab : c ∉ ({a, b} : Finset V) := (Finset.mem_sdiff.mp hcmem).2
     have hca : a ≠ c := fun h => hcab (by rw [← h]; simp)
     have hcb : b ≠ c := fun h => hcab (by rw [← h]; simp)
     have hWabc : F.biUnion edgeVerts = ({a, b, c} : Finset V) := by
       have hu := Finset.sdiff_union_of_subset hsub
       rw [hc] at hu
       rw [← hu]
       ext z; simp; tauto
     -- both edges from `c` lie in `F`, hence in `Γ`
     have hacF : mkEdge hca ∈ F := by
       rw [hFeq]
       refine mem_of_edgeVerts_subset hab' hbc' hac' k1 k2 k3 ?_
       rw [mkEdge, edgeVerts_mk, ← hW]
       intro z hz
       rcases Finset.mem_insert.mp hz with rfl | hz'
       · exact haW
       · rw [Finset.mem_singleton] at hz'; subst hz'; exact hcW
     have hbcF : mkEdge hcb ∈ F := by
       rw [hFeq]
       refine mem_of_edgeVerts_subset hab' hbc' hac' k1 k2 k3 ?_
       rw [mkEdge, edgeVerts_mk, ← hW]
       intro z hz
       rcases Finset.mem_insert.mp hz with rfl | hz'
       · exact hbW
       · rw [Finset.mem_singleton] at hz'; subst hz'; exact hcW
     have hccommon : c ∈ commonNbrs s.Γ a b := by
       refine mem_commonNbrs.mpr ⟨⟨Ne.symm hca, Ne.symm hcb⟩, ?_, ?_⟩
       · exact ⟨mkEdge hca, hFΓ hacF, by simp, by simp⟩
       · exact ⟨mkEdge hcb, hFΓ hbcF, by simp, by simp⟩
     exact Finset.mem_image.mpr ⟨c, hccommon, hWabc.symm⟩
   · intro F hF F' hF' hEq
     exact triangle_eq_of_biUnion_eq
       (famsThrough_three_triple s e (Finset.mem_coe.mp hF))
       (famsThrough_three_triple s e (Finset.mem_coe.mp hF')) hEq
  exact le_trans hmain Finset.card_image_le

lemma sum_union_le_of_nonneg {α : Type*} [DecidableEq α] (A B : Finset α)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ A ∪ B, f x ≤ (∑ x ∈ A, f x) + ∑ x ∈ B, f x := by
  classical
  have h1 : A ∪ B = A ∪ (B \ A) := (Finset.union_sdiff_self_eq_union).symm
  rw [h1, Finset.sum_union Finset.disjoint_sdiff]
  have h2 : ∑ x ∈ B \ A, f x ≤ ∑ x ∈ B, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun i _ _ => hf i)
  linarith

lemma sum_biUnion_le_of_nonneg {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (t : ι → Finset α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ s : Finset ι, ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s' ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact le_trans (sum_union_le_of_nonneg _ _ f hf) (by linarith [ih])

open scoped Classical in
/-- Every forbidden family has two or three edges. -/
lemma famsThrough_card (s : BlockState V) (e : Edge V) {F : Finset (Edge V)}
    (hF : F ∈ famsThrough s e) : F.card = 2 ∨ F.card = 3 := by
  classical
  obtain ⟨⟨-, hcase⟩, -⟩ := mem_famsThrough.mp hF
  rcases hcase with ⟨x, y, hFeq, g, -, htri⟩ | ⟨e₁, e₂, e₃, hFeq, htri⟩
  · left
    rw [hFeq, Finset.card_insert_of_notMem (by simpa using htri.ne12),
      Finset.card_singleton]
  · right
    rw [hFeq,
      Finset.card_insert_of_notMem (by simp [htri.ne12, htri.ne13]),
      Finset.card_insert_of_notMem (by simp [htri.ne23]),
      Finset.card_singleton]

open scoped Classical in
/-- **Kim's (57) input**: the total weight of the forbidden configurations
meeting `Γ(T)` is at most `|Γ(T)|·(2Mp² + d_Δ p³)`.

The two terms are Property 4's and Property 5's quantities: a forbidden *pair*
through `e` is a `Λ`-partner of `e`, a forbidden *triple* is a common
`Γ`-neighbour of `e`'s endpoints. -/
theorem sum_hitFams_le (s : BlockState V) (T : Finset V) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {M Dc : ℕ}
    (hM : ∀ g ∈ s.Γ, ∀ x ∈ edgeVerts g, (lambdaAt s g x).card ≤ M)
    (hD : ∀ (x y : V) (hxy : x ≠ y), mkEdge hxy ∈ s.Γ →
      (commonNbrs s.Γ x y).card ≤ Dc) :
    (∑ F ∈ hitFams s T, p ^ F.card)
      ≤ ((gammaBetween s.Γ T T).card : ℝ)
        * (2 * (M : ℝ) * p ^ 2 + (Dc : ℝ) * p ^ 3) := by
  classical
  have hfnn : ∀ F : Finset (Edge V), (0 : ℝ) ≤ p ^ F.card := fun F =>
    pow_nonneg hp0 _
  -- per-edge bound
  have hedge : ∀ e ∈ gammaBetween s.Γ T T,
      (∑ F ∈ famsThrough s e, p ^ F.card)
        ≤ 2 * (M : ℝ) * p ^ 2 + (Dc : ℝ) * p ^ 3 := by
    intro e he
    have heΓ : e ∈ s.Γ := (mem_gammaBetween.mp he).1
    obtain ⟨z, hz⟩ := e
    induction z using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := by simpa using hz
      set e : Edge V := ⟨s(a, b), hz⟩ with hedef
      have hsplit : famsThrough s e
          = (famsThrough s e).filter (fun F => F.card = 2)
            ∪ (famsThrough s e).filter (fun F => F.card = 3) := by
        ext F
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hF
          rcases famsThrough_card s e hF with h2 | h3
          · exact Or.inl ⟨hF, h2⟩
          · exact Or.inr ⟨hF, h3⟩
        · rintro (⟨hF, -⟩ | ⟨hF, -⟩) <;> exact hF
      have h2card : ((famsThrough s e).filter (fun F => F.card = 2)).card
          ≤ 2 * M := by
        refine le_trans (Finset.card_le_card (famsThrough_two_subset s e)) ?_
        refine le_trans Finset.card_image_le ?_
        refine le_trans Finset.card_biUnion_le ?_
        calc ∑ v ∈ edgeVerts e, (lambdaAt s e v).card
            ≤ ∑ _v ∈ edgeVerts e, M :=
              Finset.sum_le_sum fun v hv => hM e heΓ v hv
          _ = 2 * M := by
              rw [Finset.sum_const, edgeVerts_card, smul_eq_mul]
      have h3card : ((famsThrough s e).filter (fun F => F.card = 3)).card
          ≤ Dc :=
        le_trans (card_famsThrough_three_le s hab e rfl)
          (hD a b hab (show mkEdge hab ∈ s.Γ from heΓ))
      have hs2 : (∑ F ∈ (famsThrough s e).filter (fun F => F.card = 2),
          p ^ F.card) ≤ 2 * (M : ℝ) * p ^ 2 := by
        have hcongr : ∀ F ∈ (famsThrough s e).filter (fun F => F.card = 2),
            p ^ F.card = p ^ 2 := by
          intro F hF; rw [(Finset.mem_filter.mp hF).2]
        rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
        have hc : (((famsThrough s e).filter (fun F => F.card = 2)).card : ℝ)
            ≤ 2 * (M : ℝ) := by exact_mod_cast h2card
        have := mul_le_mul_of_nonneg_right hc (pow_nonneg hp0 2)
        linarith [this]
      have hs3 : (∑ F ∈ (famsThrough s e).filter (fun F => F.card = 3),
          p ^ F.card) ≤ (Dc : ℝ) * p ^ 3 := by
        have hcongr : ∀ F ∈ (famsThrough s e).filter (fun F => F.card = 3),
            p ^ F.card = p ^ 3 := by
          intro F hF; rw [(Finset.mem_filter.mp hF).2]
        rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
        have hc : (((famsThrough s e).filter (fun F => F.card = 3)).card : ℝ)
            ≤ (Dc : ℝ) := by exact_mod_cast h3card
        exact mul_le_mul_of_nonneg_right hc (pow_nonneg hp0 3)
      have hunion := sum_union_le_of_nonneg
        ((famsThrough s e).filter (fun F => F.card = 2))
        ((famsThrough s e).filter (fun F => F.card = 3))
        (fun F => p ^ F.card) hfnn
      calc (∑ F ∈ famsThrough s e, p ^ F.card)
          = ∑ F ∈ (famsThrough s e).filter (fun F => F.card = 2)
              ∪ (famsThrough s e).filter (fun F => F.card = 3),
              p ^ F.card := by rw [← hsplit]
        _ ≤ (∑ F ∈ (famsThrough s e).filter (fun F => F.card = 2),
                p ^ F.card)
            + ∑ F ∈ (famsThrough s e).filter (fun F => F.card = 3),
                p ^ F.card := hunion
        _ ≤ 2 * (M : ℝ) * p ^ 2 + (Dc : ℝ) * p ^ 3 := by linarith [hs2, hs3]
  calc (∑ F ∈ hitFams s T, p ^ F.card)
      ≤ ∑ F ∈ (gammaBetween s.Γ T T).biUnion (famsThrough s), p ^ F.card :=
        Finset.sum_le_sum_of_subset_of_nonneg (hitFams_subset_biUnion s T)
          (fun F _ _ => hfnn F)
    _ ≤ ∑ e ∈ gammaBetween s.Γ T T, ∑ F ∈ famsThrough s e, p ^ F.card :=
        sum_biUnion_le_of_nonneg _ _ hfnn _
    _ ≤ ∑ _e ∈ gammaBetween s.Γ T T,
          (2 * (M : ℝ) * p ^ 2 + (Dc : ℝ) * p ^ 3) :=
        Finset.sum_le_sum hedge
    _ = ((gammaBetween s.Γ T T).card : ℝ)
          * (2 * (M : ℝ) * p ^ 2 + (Dc : ℝ) * p ^ 3) := by
        rw [Finset.sum_const, nsmul_eq_mul]

open scoped Classical in
/-- **The `Λ*`-overlap of two distinct edges is `O(ℰ`-codegree`)`.**

Padding coordinates belong to a single edge, so distinct edges share only
genuine `Λ`-partners; at a shared endpoint those are bounded by an `ℰ`-codegree
(Kim's (26)), and at distinct endpoints by one. There are four endpoint pairs,
giving `4C`.

Kim states this as `|N_Λ(e_uv,u) ∩ N_Λ(e_wu,u)| ≤ |N_ℰ(v) ∩ N_ℰ(w)| ≤ 3k log n`
in §4.6; the constant is immaterial to the numerics. -/
lemma card_lambdaStar_inter_le (s : BlockState V) (M : ℕ) {e g : Edge V}
    (heg : e ≠ g) {C : ℝ} (hC1 : 1 ≤ C)
    (hbound : ∀ w w' : V, w ≠ w' → ((commonNbrs s.E w w').card : ℝ) ≤ C) :
    ((lambdaStar s M e ∩ lambdaStar s M g).card : ℝ) ≤ 4 * C := by
  classical
  have hsub : lambdaStar s M e ∩ lambdaStar s M g
      ⊆ (edgeVerts e).biUnion (fun u => (edgeVerts g).biUnion (fun u' =>
          (lambdaAt s e u ∩ lambdaAt s g u').image Sum.inl)) := by
    intro c hc
    obtain ⟨hce, hcg⟩ := Finset.mem_inter.mp hc
    obtain ⟨u, hue, hcu⟩ := mem_lambdaStar.mp hce
    obtain ⟨u', hug, hcu'⟩ := mem_lambdaStar.mp hcg
    rcases Finset.mem_union.mp hcu with h1 | h1
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp h1
      rcases Finset.mem_union.mp hcu' with h2 | h2
      · obtain ⟨f', hf', hff'⟩ := Finset.mem_image.mp h2
        have : f' = f := Sum.inl_injective hff'
        subst this
        exact Finset.mem_biUnion.mpr ⟨u, hue, Finset.mem_biUnion.mpr
          ⟨u', hug, Finset.mem_image.mpr
            ⟨f', Finset.mem_inter.mpr ⟨hf, hf'⟩, rfl⟩⟩⟩
      · obtain ⟨i, hi⟩ := mem_padAt h2
        exact absurd hi (by simp)
    · obtain ⟨i, hi⟩ := mem_padAt h1
      rcases Finset.mem_union.mp hcu' with h2 | h2
      · obtain ⟨f', -, hf'⟩ := Finset.mem_image.mp h2
        exact absurd (hf'.trans hi) (by simp)
      · obtain ⟨i', hi'⟩ := mem_padAt h2
        rw [hi] at hi'
        exact absurd (congrArg (fun z => z.1) (Sum.inr_injective hi')) heg
  have hstep : ((lambdaStar s M e ∩ lambdaStar s M g).card : ℝ)
      ≤ ∑ u ∈ edgeVerts e, ∑ u' ∈ edgeVerts g,
          ((lambdaAt s e u ∩ lambdaAt s g u').card : ℝ) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le (s := edgeVerts e)
      (t := fun u => (edgeVerts g).biUnion (fun u' =>
        (lambdaAt s e u ∩ lambdaAt s g u').image
          (Sum.inl : Edge V → Coord V M)))
    have h3 : ∀ u : V, ((edgeVerts g).biUnion (fun u' =>
        (lambdaAt s e u ∩ lambdaAt s g u').image
          (Sum.inl : Edge V → Coord V M))).card
        ≤ ∑ u' ∈ edgeVerts g, (lambdaAt s e u ∩ lambdaAt s g u').card := by
      intro u
      refine le_trans Finset.card_biUnion_le ?_
      exact Finset.sum_le_sum fun u' _ =>
        le_of_eq (Finset.card_image_of_injective _ Sum.inl_injective)
    have hnat : (lambdaStar s M e ∩ lambdaStar s M g).card
        ≤ ∑ u ∈ edgeVerts e, ∑ u' ∈ edgeVerts g,
            (lambdaAt s e u ∩ lambdaAt s g u').card := by
      refine le_trans h1 (le_trans h2 ?_)
      exact Finset.sum_le_sum fun u _ => h3 u
    exact_mod_cast hnat
  refine hstep.trans ?_
  -- each of the four terms is at most `C`
  have hterm : ∀ u ∈ edgeVerts e, ∀ u' ∈ edgeVerts g,
      ((lambdaAt s e u ∩ lambdaAt s g u').card : ℝ) ≤ C := by
    intro u hu u' hu'
    by_cases huu' : u = u'
    · subst huu'
      calc ((lambdaAt s e u ∩ lambdaAt s g u).card : ℝ)
          ≤ ((commonNbrs s.E (otherEndOf u e) (otherEndOf u g)).card : ℝ) := by
            exact_mod_cast card_lambdaAt_inter_same_le s e g u
        _ ≤ C := hbound _ _ (otherEndOf_ne_of_ne (mem_edgeVerts.mp hu)
              (mem_edgeVerts.mp hu') heg)
    · calc ((lambdaAt s e u ∩ lambdaAt s g u').card : ℝ)
          ≤ 1 := by
            exact_mod_cast card_lambdaAt_inter_diff_le s e g (Ne.symm huu')
        _ ≤ C := hC1
  calc ∑ u ∈ edgeVerts e, ∑ u' ∈ edgeVerts g,
        ((lambdaAt s e u ∩ lambdaAt s g u').card : ℝ)
      ≤ ∑ _u ∈ edgeVerts e, ∑ _u' ∈ edgeVerts g, C :=
        Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun u' hu' =>
          hterm u hu u' hu'
    _ = 4 * C := by
        rw [Finset.sum_const, Finset.sum_const, edgeVerts_card, edgeVerts_card]
        push_cast; ring

open scoped Classical in
/-- For `u ∉ {v, w}` the pair `pairEdges v w u` is exactly `{e_uv, e_uw}`. -/
lemma pairEdges_eq {v w u : V} (huv : u ≠ v) (huw : u ≠ w) :
    pairEdges v w u = {mkEdge huv, mkEdge huw} := by
  classical
  ext e
  simp only [pairEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hue, hvw⟩
    rcases hvw with hv | hw
    · exact Or.inl (Subtype.ext (by
        rw [edge_eq_of_two_mem hue hv huv, mkEdge_val]))
    · exact Or.inr (Subtype.ext (by
        rw [edge_eq_of_two_mem hue hw huw, mkEdge_val]))
  · rintro (rfl | rfl)
    · exact ⟨by simp, Or.inl (by simp)⟩
    · exact ⟨by simp, Or.inr (by simp)⟩

open scoped Classical in
/-- The event that both edges from `v` to the endpoints of `f` are sampled. -/
noncomputable def cherryEvent (s : BlockState V) (M : ℕ) (f : Edge V) (v : V) :
    Finset (Fin (Fintype.card (Coord V M)) → Bool) := by
  classical
  exact Finset.univ.filter (fun σ => edgeVerts f ⊆ nbrs (sampleP s M σ) v)

lemma mem_cherryEvent {s : BlockState V} {M : ℕ} {f : Edge V} {v : V}
    {σ : Fin (Fintype.card (Coord V M)) → Bool} :
    σ ∈ cherryEvent s M f v ↔ edgeVerts f ⊆ nbrs (sampleP s M σ) v := by
  classical
  show σ ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

open scoped Classical in
/-- `|Γ(N̂(v,T))|` is at most the number of `Γ(T)`-edges both of whose endpoints
`v` reaches through sampled edges. -/
lemma zContrib_le_cherry (s : BlockState V) (M h : ℕ) (T : Finset V) (v : V)
    (σ : Fin (Fintype.card (Coord V M)) → Bool) :
    zContrib s M h T v σ
      ≤ ∑ f ∈ gammaBetween s.Γ T T,
          (if σ ∈ cherryEvent s M f v then (1 : ℝ) else 0) := by
  classical
  have hsub : gammaBetween s.Γ (truncTo (nbrs (sampleP s M σ) v ∩ T) h)
      (truncTo (nbrs (sampleP s M σ) v ∩ T) h)
      ⊆ (gammaBetween s.Γ T T).filter
          (fun f => σ ∈ cherryEvent s M f v) := by
    intro g hg
    obtain ⟨hgΓ, x, hx, y, hy, hxy, hxg, hyg⟩ := mem_gammaBetween.mp hg
    have hxN : x ∈ nbrs (sampleP s M σ) v ∩ T := truncTo_subset _ _ hx
    have hyN : y ∈ nbrs (sampleP s M σ) v ∩ T := truncTo_subset _ _ hy
    have hgval : g.val = s(x, y) := edge_eq_of_two_mem hxg hyg hxy
    have hgv : edgeVerts g = {x, y} := by
      have hgg : g = ⟨s(x, y), by rw [← hgval]; exact g.2⟩ := Subtype.ext hgval
      rw [hgg, edgeVerts_mk]
    refine Finset.mem_filter.mpr ⟨mem_gammaBetween.mpr
      ⟨hgΓ, x, (Finset.mem_inter.mp hxN).2, y,
        (Finset.mem_inter.mp hyN).2, hxy, hxg, hyg⟩, ?_⟩
    refine mem_cherryEvent.mpr ?_
    rw [hgv]
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact (Finset.mem_inter.mp hxN).1
    · rw [Finset.mem_singleton] at hz'
      subst hz'
      exact (Finset.mem_inter.mp hyN).1
  have hcount : ∑ f ∈ gammaBetween s.Γ T T,
      (if σ ∈ cherryEvent s M f v then (1 : ℝ) else 0)
      = (((gammaBetween s.Γ T T).filter
          (fun f => σ ∈ cherryEvent s M f v)).card : ℝ) := by
    rw [Finset.card_filter]; push_cast; rfl
  rw [hcount, zContrib]
  exact_mod_cast Finset.card_le_card hsub

open scoped Classical in
/-- `Pr(both edges from `v` sampled) ≤ p²`. -/
lemma bernoulliPr_cherryEvent_le (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Edge V) (v : V)
    (hv : edgeVerts f ⊆ nbrs s.Γ v) :
    bernoulliPr p (cherryEvent s M f v) ≤ p ^ 2 := by
  classical
  obtain ⟨z, hz⟩ := f
  induction z using Sym2.ind with
  | _ x y =>
    have hxy : x ≠ y := by simpa using hz
    have hgv : edgeVerts (⟨s(x, y), hz⟩ : Edge V) = {x, y} := edgeVerts_mk hz
    have hxmem : x ∈ edgeVerts (⟨s(x, y), hz⟩ : Edge V) := by
      rw [hgv]; exact Finset.mem_insert_self _ _
    have hymem : y ∈ edgeVerts (⟨s(x, y), hz⟩ : Edge V) := by
      rw [hgv]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hxv : x ∈ nbrs s.Γ v := hv hxmem
    have hyv : y ∈ nbrs s.Γ v := hv hymem
    have hvx : v ≠ x := fun hc => (mem_nbrs.mp hxv).1 hc.symm
    have hvy : v ≠ y := fun hc => (mem_nbrs.mp hyv).1 hc.symm
    have hmkx : mkEdge hvx ∈ s.Γ := by
      obtain ⟨-, e, heΓ, hve, hxe⟩ := mem_nbrs.mp hxv
      have hval : e.val = s(v, x) := edge_eq_of_two_mem hve hxe hvx
      have heq : e = mkEdge hvx := Subtype.ext (by rw [hval, mkEdge_val])
      rwa [heq] at heΓ
    have hmky : mkEdge hvy ∈ s.Γ := by
      obtain ⟨-, e, heΓ, hve, hye⟩ := mem_nbrs.mp hyv
      have hval : e.val = s(v, y) := edge_eq_of_two_mem hve hye hvy
      have heq : e = mkEdge hvy := Subtype.ext (by rw [hval, mkEdge_val])
      rwa [heq] at heΓ
    have hpair : pairEdges x y v = {mkEdge hvx, mkEdge hvy} :=
      pairEdges_eq hvx hvy
    have hne : mkEdge hvx ≠ mkEdge hvy := by
      intro hEq
      have hss : (s(v, x) : Sym2 V) = s(v, y) := by
        rw [← mkEdge_val hvx, ← mkEdge_val hvy, hEq]
      exact hxy ((Sym2.congr_right).mp hss)
    have hcard : (pairEdges x y v).card = 2 := by
      rw [hpair, Finset.card_insert_of_notMem (by simpa using hne),
        Finset.card_singleton]
    have hCΓ : ∀ F ∈ ({pairEdges x y v} : Finset (Finset (Edge V))),
        F ⊆ s.Γ := by
      intro F hF
      rw [Finset.mem_singleton] at hF
      subst hF
      rw [hpair]
      intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg'
      · exact hmkx
      · rw [Finset.mem_singleton] at hg'; subst hg'; exact hmky
    have hCd : PairwiseDisjointFam
        ({pairEdges x y v} : Finset (Finset (Edge V))) := by
      intro F hF G hG hFG
      rw [Finset.mem_singleton] at hF hG
      exact absurd (hF.trans hG.symm) hFG
    have hall := bernoulliPr_all_subsets s M p
      ({pairEdges x y v} : Finset (Finset (Edge V))) hCΓ hCd
    rw [Finset.prod_singleton, hcard] at hall
    refine le_trans (bernoulliPr_mono hp0 hp1 ?_) (le_of_eq hall)
    intro σ hσ
    have hσ' : edgeVerts (⟨s(x, y), hz⟩ : Edge V) ⊆ nbrs (sampleP s M σ) v :=
      mem_cherryEvent.mp hσ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro F hF
    rw [Finset.mem_singleton] at hF
    subst hF
    rw [hpair]
    intro g hg
    rcases Finset.mem_insert.mp hg with rfl | hg'
    · obtain ⟨-, e, heS, hve, hxe⟩ := mem_nbrs.mp (hσ' hxmem)
      have hval : e.val = s(v, x) := edge_eq_of_two_mem hve hxe hvx
      have heq : e = mkEdge hvx := Subtype.ext (by rw [hval, mkEdge_val])
      rwa [heq] at heS
    · rw [Finset.mem_singleton] at hg'
      subst hg'
      obtain ⟨-, e, heS, hve, hye⟩ := mem_nbrs.mp (hσ' hymem)
      have hval : e.val = s(v, y) := edge_eq_of_two_mem hve hye hvy
      have heq : e = mkEdge hvy := Subtype.ext (by rw [hval, mkEdge_val])
      rwa [heq] at heS

lemma nbrs_mono {F G : Finset (Edge V)} (h : F ⊆ G) (v : V) :
    nbrs F v ⊆ nbrs G v := by
  classical
  intro u hu
  obtain ⟨hne, e, heF, hve, hue⟩ := mem_nbrs.mp hu
  exact mem_nbrs.mpr ⟨hne, e, h heF, hve, hue⟩

open scoped Classical in
/-- **Kim's `E[Φ⁽³⁾] ≤ p²·d_Δ·|Γ(T)|`.**

Each `Γ(T)`-edge `f` contributes only through the common `Γ`-neighbours of its
endpoints, and each such `v` needs *two* specific edges sampled. -/
theorem zContrib_mean_le (s : BlockState V) (M h : ℕ) (T : Finset V) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset V) {D : ℝ}
    (hD : ∀ f ∈ gammaBetween s.Γ T T,
      ((A.filter (fun v => edgeVerts f ⊆ nbrs s.Γ v)).card : ℝ) ≤ D) :
    ∑ v ∈ A, bernoulliExp p (zContrib s M h T v)
      ≤ p ^ 2 * D * ((gammaBetween s.Γ T T).card : ℝ) := by
  classical
  have hp2 : (0 : ℝ) ≤ p ^ 2 := sq_nonneg p
  -- per-vertex: the mean is at most the sum of the cherry probabilities
  have hstep : ∀ v : V, bernoulliExp p (zContrib s M h T v)
      ≤ ∑ f ∈ gammaBetween s.Γ T T, bernoulliPr p (cherryEvent s M f v) := by
    intro v
    have hmono := bernoulliExp_mono hp0 hp1
      (f := zContrib s M h T v)
      (g := fun σ => ∑ f ∈ gammaBetween s.Γ T T,
        (if σ ∈ cherryEvent s M f v then (1 : ℝ) else 0))
      (fun σ => zContrib_le_cherry s M h T v σ)
    refine le_trans hmono (le_of_eq ?_)
    rw [bernoulliExp_sum]
    exact Finset.sum_congr rfl fun f _ => (bernoulliPr_eq_exp p _).symm
  -- per-edge: the cherry probabilities sum to at most `p²·D`
  have hedge : ∀ f ∈ gammaBetween s.Γ T T,
      ∑ v ∈ A, bernoulliPr p (cherryEvent s M f v) ≤ p ^ 2 * D := by
    intro f hf
    have hsplit := (Finset.sum_filter_add_sum_filter_not A
      (fun v => edgeVerts f ⊆ nbrs s.Γ v)
      (fun v => bernoulliPr p (cherryEvent s M f v))).symm
    have hzero : ∑ v ∈ A.filter (fun v => ¬ edgeVerts f ⊆ nbrs s.Γ v),
        bernoulliPr p (cherryEvent s M f v) = 0 := by
      refine Finset.sum_eq_zero fun v hv => ?_
      obtain ⟨-, hvn⟩ := Finset.mem_filter.mp hv
      have hempty : cherryEvent s M f v = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun σ hσ => ?_
        exact hvn (Finset.Subset.trans (mem_cherryEvent.mp hσ)
          (nbrs_mono (sampleP_subset s M σ) v))
      rw [hempty, bernoulliPr_empty]
    have hyes : ∑ v ∈ A.filter (fun v => edgeVerts f ⊆ nbrs s.Γ v),
        bernoulliPr p (cherryEvent s M f v)
        ≤ p ^ 2 * ((A.filter (fun v => edgeVerts f ⊆ nbrs s.Γ v)).card : ℝ) := by
      refine le_trans (Finset.sum_le_sum (g := fun _ : V => p ^ 2)
        fun v hv => ?_) ?_
      · exact bernoulliPr_cherryEvent_le s M hp0 hp1 f v
          (Finset.mem_filter.mp hv).2
      · rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hDf := hD f hf
    calc ∑ v ∈ A, bernoulliPr p (cherryEvent s M f v)
        = (∑ v ∈ A.filter (fun v => edgeVerts f ⊆ nbrs s.Γ v),
            bernoulliPr p (cherryEvent s M f v))
          + ∑ v ∈ A.filter (fun v => ¬ edgeVerts f ⊆ nbrs s.Γ v),
            bernoulliPr p (cherryEvent s M f v) := hsplit
      _ = ∑ v ∈ A.filter (fun v => edgeVerts f ⊆ nbrs s.Γ v),
            bernoulliPr p (cherryEvent s M f v) := by rw [hzero, add_zero]
      _ ≤ p ^ 2 * ((A.filter (fun v => edgeVerts f ⊆ nbrs s.Γ v)).card : ℝ) :=
          hyes
      _ ≤ p ^ 2 * D := mul_le_mul_of_nonneg_left hDf hp2
  calc ∑ v ∈ A, bernoulliExp p (zContrib s M h T v)
      ≤ ∑ v ∈ A, ∑ f ∈ gammaBetween s.Γ T T,
          bernoulliPr p (cherryEvent s M f v) :=
        Finset.sum_le_sum fun v _ => hstep v
    _ = ∑ f ∈ gammaBetween s.Γ T T, ∑ v ∈ A,
          bernoulliPr p (cherryEvent s M f v) := Finset.sum_comm
    _ ≤ ∑ _f ∈ gammaBetween s.Γ T T, p ^ 2 * D :=
        Finset.sum_le_sum hedge
    _ = p ^ 2 * D * ((gammaBetween s.Γ T T).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

open scoped Classical in
/-- **Kim (45) with the truncation excess (54) accounted for.**

On a good event `Good` — one on which Kim's `Φ⁽⁴⁾` is at most `c7` — the
killed-`Z` count exceeds `c5 + c6 + c7` only if one of the two *truncated*
sums is large.  No event of the form "the truncation never bites" is needed —
that event cannot be made small enough to survive the `C(n,t)` union over
`𝒯`, which is why Kim's `Φ⁽⁴⁾` bound (54) is used instead. -/
theorem card_killedZpure_prob' (s : BlockState V) (M h : ℕ) (T : Finset V)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {c5 c6 c7 q5 q6 : ℝ}
    (Good : Finset (Fin (Fintype.card (Coord V M)) → Bool))
    (hGood : ∀ σ ∈ Good,
      (∑ v ∈ Finset.univ.filter
          (fun v => h ≤ (nbrs (sampleP s M σ) v ∩ T).card),
        ((gammaBetween s.Γ (nbrs (sampleP s M σ) v ∩ T)
          (nbrs (sampleP s M σ) v ∩ T)).card : ℝ)) ≤ c7)
    (hq5 : bernoulliPr p (Finset.univ.filter
      (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        c5 < ∑ v ∈ T, zContrib s M h T v σ)) ≤ q5)
    (hq6 : bernoulliPr p (Finset.univ.filter
      (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        c6 ≤ ∑ v ∈ (Finset.univ : Finset V) \ T, zContrib s M h T v σ)) ≤ q6) :
    bernoulliPr p ((Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          c5 + c6 + c7
            < ((gammaBetween s.Γ T T ∩ killedZpure s M σ).card : ℝ))) ∩ Good)
      ≤ q5 + q6 := by
  classical
  refine le_trans (bernoulliPr_mono hp0 hp1 (?_ :
      _ ⊆ (Finset.univ.filter
          (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
            c5 < ∑ v ∈ T, zContrib s M h T v σ))
        ∪ (Finset.univ.filter
          (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
            c6 ≤ ∑ v ∈ (Finset.univ : Finset V) \ T,
              zContrib s M h T v σ)))) ?_
  · intro σ hσ
    obtain ⟨hσ1, hσG⟩ := Finset.mem_inter.mp hσ
    obtain ⟨-, hgt⟩ := Finset.mem_filter.mp hσ1
    by_contra hcon
    rw [Finset.mem_union] at hcon
    push_neg at hcon
    obtain ⟨h5, h6⟩ := hcon
    have hTle : ∑ v ∈ T, zContrib s M h T v σ ≤ c5 := by
      by_contra hc
      exact h5 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_le.mp hc⟩)
    have hStle : (∑ v ∈ (Finset.univ : Finset V) \ T, zContrib s M h T v σ)
        < c6 := by
      by_contra hc
      exact h6 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hc⟩)
    have hdet := card_killedZpure_inter_le s M σ T h
    have hsplit : (∑ v ∈ (Finset.univ : Finset V) \ T, zContrib s M h T v σ)
        + ∑ v ∈ T, zContrib s M h T v σ
        = ∑ v : V, zContrib s M h T v σ :=
      Finset.sum_sdiff (Finset.subset_univ T)
    have hzc : ∑ v : V, zContrib s M h T v σ
        = ∑ v : V, ((gammaBetween s.Γ
            (truncTo (nbrs (sampleP s M σ) v ∩ T) h)
            (truncTo (nbrs (sampleP s M σ) v ∩ T) h)).card : ℝ) := rfl
    rw [← hzc] at hdet
    rw [Finset.inter_comm] at hgt
    linarith [hgt, hdet, hsplit, hTle, hStle, hGood σ hσG]
  · exact le_trans (bernoulliPr_union_le hp0 hp1 _ _) (by linarith [hq5, hq6])

open scoped Classical in
/-- **Kim's overlap input to (29)**: for every common `Γ`-neighbour `u` of
`v, w`, the two edges `e_uv, e_uw` have `4M − 4C` distinct `Λ*`-coordinates
between them. -/
lemma card_biUnion_pairEdges_ge (s : BlockState V) (M : ℕ) (v w : V)
    (hvw : v ≠ w) {C : ℝ} (hC1 : 1 ≤ C)
    (hbound : ∀ x y : V, x ≠ y → ((commonNbrs s.E x y).card : ℝ) ≤ C)
    (hM : ∀ g ∈ s.Γ, ∀ x ∈ edgeVerts g, (lambdaAt s g x).card ≤ M)
    (u : V) (hu : u ∈ commonNbrs s.Γ v w) {I : ℕ} (hI : 4 * C ≤ (I : ℝ)) :
    4 * M - I ≤ ((pairEdges v w u).biUnion (lambdaStar s M)).card := by
  classical
  obtain ⟨⟨huv, huw⟩, ⟨e1, he1, hve1, hue1⟩, ⟨e2, he2, hue2, hwe2⟩⟩ :=
    mem_commonNbrs.mp hu
  have hmk1 : mkEdge huv ∈ s.Γ := by
    have hval : e1.val = s(u, v) := edge_eq_of_two_mem hue1 hve1 huv
    have hee : e1 = mkEdge huv := Subtype.ext (by rw [hval, mkEdge_val])
    rwa [hee] at he1
  have hmk2 : mkEdge huw ∈ s.Γ := by
    have hval : e2.val = s(u, w) := edge_eq_of_two_mem hue2 hwe2 huw
    have hee : e2 = mkEdge huw := Subtype.ext (by rw [hval, mkEdge_val])
    rwa [hee] at he2
  have hne : mkEdge huv ≠ mkEdge huw := by
    intro hEq
    have : (s(u, v) : Sym2 V) = s(u, w) := by
      rw [← mkEdge_val huv, ← mkEdge_val huw, hEq]
    exact hvw ((Sym2.congr_right).mp this)
  rw [pairEdges_eq huv huw]
  refine card_biUnion_pair_ge s M (card_lambdaStar s M _ (hM _ hmk1))
    (card_lambdaStar s M _ (hM _ hmk2)) ?_
  have hoverlap := card_lambdaStar_inter_le s M hne hC1 hbound
  have : ((lambdaStar s M (mkEdge huv) ∩ lambdaStar s M (mkEdge huw)).card : ℝ)
      ≤ (I : ℝ) := le_trans hoverlap hI
  exact_mod_cast this

lemma mem_pairEdges {v w u : V} {e : Edge V} :
    e ∈ pairEdges v w u ↔ u ∈ e.val ∧ (v ∈ e.val ∨ w ∈ e.val) := by
  classical
  show e ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

open scoped Classical in
/-- **Kim's `c_e` for §4.6.** Fix a coordinate `j`. The common `Γ`-neighbours
`u` of `v, w` for which `j` is a `Λ*`-coordinate of `e_uv` or `e_uw` number at
most `2M + 4`.

Kim's three cases: a padding coordinate belongs to one edge only (`≤ 2`); a
genuine coordinate `g` can be a `Λ`-partner *at `u`* only if `u ∈ g` (`≤ 2`);
and *at `v`* only if `u ∈ N_ℰ(otherEnd(v,g)) ∩ N_Γ(v)`, which is the far-end
image of `N_Λ(g, v)` and so has size `≤ M` by Property 4 — likewise at `w`. -/
lemma card_filter_pairEdges_le (s : BlockState V) (M : ℕ) (v w : V)
    (hM : ∀ g ∈ s.Γ, ∀ x ∈ edgeVerts g, (lambdaAt s g x).card ≤ M)
    (j : Fin (Fintype.card (Coord V M))) :
    (((commonNbrs s.Γ v w).filter (fun u =>
      j ∈ ((pairEdges v w u).biUnion (lambdaStar s M)).image
        (coordEquiv V M))).card : ℝ) ≤ 2 * M + 4 := by
  classical
  set F : Finset V := (commonNbrs s.Γ v w).filter (fun u =>
    j ∈ ((pairEdges v w u).biUnion (lambdaStar s M)).image
      (coordEquiv V M)) with hF
  set c : Coord V M := (coordEquiv V M).symm j with hc
  have hj : j = coordEquiv V M c := by rw [hc]; simp
  -- unwind membership of `F`
  have hunfold : ∀ u ∈ F, u ∈ commonNbrs s.Γ v w ∧
      ∃ f ∈ pairEdges v w u, ∃ y ∈ edgeVerts f,
        c ∈ (lambdaAt s f y).image Sum.inl ∪ padAt s M f y := by
    intro u hu
    obtain ⟨hcom, hjmem⟩ := Finset.mem_filter.mp (hF ▸ hu)
    obtain ⟨d, hd, hdj⟩ := Finset.mem_image.mp hjmem
    have hdc : d = c := (coordEquiv V M).injective (by rw [hdj, hj])
    obtain ⟨f, hf, hdf⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨y, hy, hyd⟩ := mem_lambdaStar.mp hdf
    exact ⟨hcom, f, hf, y, hy, hdc ▸ hyd⟩
  cases hcase : c with
  | inr q =>
      have hsub : F ⊆ edgeVerts q.1 := by
        intro u hu
        obtain ⟨-, f, hf, y, -, hyd⟩ := hunfold u hu
        rcases Finset.mem_union.mp hyd with h1 | h1
        · obtain ⟨z, -, hz⟩ := Finset.mem_image.mp h1
          rw [hcase] at hz
          exact absurd hz (by simp)
        · obtain ⟨i, hi⟩ := mem_padAt h1
          rw [hcase] at hi
          have hfq : f = q.1 :=
            (congrArg (fun z => z.1) (Sum.inr_injective hi)).symm
          have huf : u ∈ f.val := (mem_pairEdges.mp hf).1
          rw [hfq] at huf
          exact mem_edgeVerts.mpr huf
      have hcard : F.card ≤ 2 := by
        have := Finset.card_le_card hsub
        rwa [edgeVerts_card] at this
      have hMn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
      have : (F.card : ℝ) ≤ 2 := by exact_mod_cast hcard
      linarith
  | inl g =>
      by_cases hgΓ : g ∈ s.Γ
      · set Bv : Finset V := if v ∈ g.val then
            nbrs s.Γ v ∩ nbrs s.E (otherEndOf v g) else ∅ with hBv
        set Bw : Finset V := if w ∈ g.val then
            nbrs s.Γ w ∩ nbrs s.E (otherEndOf w g) else ∅ with hBw
        have hsub : F ⊆ edgeVerts g ∪ Bv ∪ Bw := by
          intro u hu
          obtain ⟨hcom, f, hf, y, hyf, hyd⟩ := hunfold u hu
          have hglam : g ∈ lambdaAt s f y := by
            rcases Finset.mem_union.mp hyd with h1 | h1
            · obtain ⟨z, hz, hzg⟩ := Finset.mem_image.mp h1
              rw [hcase] at hzg
              exact (Sum.inl_injective hzg) ▸ hz
            · obtain ⟨i, hi⟩ := mem_padAt h1
              rw [hcase] at hi
              exact absurd hi (by simp)
          obtain ⟨⟨-, hyg⟩, hend⟩ := mem_lambdaAt.mp hglam
          obtain ⟨⟨huv, huw⟩, hΓv, hΓw⟩ := mem_commonNbrs.mp hcom
          have huf : u ∈ f.val := (mem_pairEdges.mp hf).1
          have hyfv : y ∈ f.val := mem_edgeVerts.mp hyf
          by_cases hyu : y = u
          · subst hyu
            exact Finset.mem_union_left _ (Finset.mem_union_left _
              (mem_edgeVerts.mpr hyg))
          · -- `y ∈ {v, w}`
            have hother : u = otherEndOf y f :=
              eq_otherEndOf_of_mem hyfv huf (fun h => hyu h.symm)
            have hend' : u ∈ nbrs s.E (otherEndOf y g) := by
              rw [← hother] at hend
              exact (nbrs_comm s.E _ _).mp hend
            rcases (mem_pairEdges.mp hf).2 with hvf | hwf
            · have hyv : y = v := by
                rcases eq_or_ne v y with h | h
                · exact h.symm
                · exact absurd (eq_otherEndOf_of_mem hyfv hvf h)
                    (by rw [← hother]; exact fun hc => huv hc.symm)
              subst hyv
              refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
              rw [hBv, if_pos hyg]
              refine Finset.mem_inter.mpr ⟨?_, hend'⟩
              obtain ⟨e, he, hye, hue⟩ := hΓv
              exact mem_nbrs.mpr ⟨huv, e, he, hye, hue⟩
            · have hyw : y = w := by
                rcases eq_or_ne w y with h | h
                · exact h.symm
                · exact absurd (eq_otherEndOf_of_mem hyfv hwf h)
                    (by rw [← hother]; exact fun hc => huw hc.symm)
              subst hyw
              refine Finset.mem_union_right _ ?_
              rw [hBw, if_pos hyg]
              refine Finset.mem_inter.mpr ⟨?_, hend'⟩
              obtain ⟨e, he, hue, hye⟩ := hΓw
              exact mem_nbrs.mpr ⟨huw, e, he, hye, hue⟩
        have hBvM : Bv.card ≤ M := by
          rw [hBv]
          by_cases hv : v ∈ g.val
          · rw [if_pos hv]
            refine le_trans ?_ (hM g hgΓ v (mem_edgeVerts.mpr hv))
            rw [lambdaAt, ← image_otherEndOf_crossEdges s (otherEndOf v g) v]
            exact Finset.card_image_le
          · rw [if_neg hv]; simp
        have hBwM : Bw.card ≤ M := by
          rw [hBw]
          by_cases hw : w ∈ g.val
          · rw [if_pos hw]
            refine le_trans ?_ (hM g hgΓ w (mem_edgeVerts.mpr hw))
            rw [lambdaAt, ← image_otherEndOf_crossEdges s (otherEndOf w g) w]
            exact Finset.card_image_le
          · rw [if_neg hw]; simp
        have hcard : F.card ≤ 2 + M + M := by
          refine le_trans (Finset.card_le_card hsub) ?_
          refine le_trans (Finset.card_union_le _ _) ?_
          have h1 := Finset.card_union_le (edgeVerts g) Bv
          rw [edgeVerts_card] at h1
          omega
        have : (F.card : ℝ) ≤ 2 + M + M := by exact_mod_cast hcard
        linarith
      · have hempty : F = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun u hu => ?_
          obtain ⟨-, f, -, y, -, hyd⟩ := hunfold u hu
          rcases Finset.mem_union.mp hyd with h1 | h1
          · obtain ⟨z, hz, hzg⟩ := Finset.mem_image.mp h1
            rw [hcase] at hzg
            have : z = g := Sum.inl_injective hzg
            subst this
            exact hgΓ (mem_lambdaAt.mp hz).1.1
          · obtain ⟨i, hi⟩ := mem_padAt h1
            rw [hcase] at hi
            exact absurd hi (by simp)
        rw [hempty]
        have hMn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
        simp
        linarith

open scoped Classical in
/-- The two `Γ`-edges `e_uv`, `e_uw` witnessing a common `Γ`-neighbour. -/
lemma pairEdges_mem_gamma (s : BlockState V) {v w u : V}
    (hu : u ∈ commonNbrs s.Γ v w) :
    ∃ (huv : u ≠ v) (huw : u ≠ w),
      mkEdge huv ∈ s.Γ ∧ mkEdge huw ∈ s.Γ := by
  classical
  obtain ⟨⟨huv, huw⟩, ⟨e1, he1, hve1, hue1⟩, ⟨e2, he2, hue2, hwe2⟩⟩ :=
    mem_commonNbrs.mp hu
  refine ⟨huv, huw, ?_, ?_⟩
  · have hval : e1.val = s(u, v) := edge_eq_of_two_mem hue1 hve1 huv
    have : e1 = mkEdge huv := Subtype.ext (by rw [hval, mkEdge_val])
    rwa [this] at he1
  · have hval : e2.val = s(u, w) := edge_eq_of_two_mem hue2 hwe2 huw
    have : e2 = mkEdge huw := Subtype.ext (by rw [hval, mkEdge_val])
    rwa [this] at he2

open scoped Classical in
/-- **Kim's `Σ c_e ≤ 4M·d_Δ(e_vw)` for §4.6** (his Lemma 4.2 in this setting):
each `u` contributes the `≤ 4M` coordinates of `Λ*(e_uv) ∪ Λ*(e_uw)`. -/
lemma sum_card_filter_pairEdges_le (s : BlockState V) (M : ℕ) (v w : V)
    (hM : ∀ g ∈ s.Γ, ∀ x ∈ edgeVerts g, (lambdaAt s g x).card ≤ M) :
    ∑ j : Fin (Fintype.card (Coord V M)),
        ((commonNbrs s.Γ v w).filter (fun u =>
          j ∈ ((pairEdges v w u).biUnion (lambdaStar s M)).image
            (coordEquiv V M))).card
      ≤ 4 * M * (commonNbrs s.Γ v w).card := by
  classical
  rw [← sum_card_filter_comm (commonNbrs s.Γ v w)
    (Finset.univ : Finset (Fin (Fintype.card (Coord V M))))
    (fun u j => j ∈ ((pairEdges v w u).biUnion (lambdaStar s M)).image
      (coordEquiv V M))]
  refine le_trans (Finset.sum_le_sum (g := fun _ : V => 4 * M)
    (fun u hu => ?_)) ?_
  · obtain ⟨huv, huw, hmk1, hmk2⟩ := pairEdges_mem_gamma s hu
    have hstar : ∀ f ∈ pairEdges v w u, (lambdaStar s M f).card ≤ 2 * M := by
      intro f hf
      rw [pairEdges_eq huv huw] at hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact le_of_eq (card_lambdaStar s M _ (hM _ hmk1))
      · rw [Finset.mem_singleton] at hf
        subst hf
        exact le_of_eq (card_lambdaStar s M _ (hM _ hmk2))
    have hpc : (pairEdges v w u).card ≤ 2 := by
      rw [pairEdges_eq huv huw]
      exact le_trans (Finset.card_insert_le _ _) (by simp)
    have hbi : ((pairEdges v w u).biUnion (lambdaStar s M)).card ≤ 4 * M := by
      refine le_trans Finset.card_biUnion_le ?_
      refine le_trans (Finset.sum_le_card_nsmul _ _ (2 * M) hstar) ?_
      rw [smul_eq_mul]
      calc (pairEdges v w u).card * (2 * M) ≤ 2 * (2 * M) :=
            Nat.mul_le_mul_right _ hpc
        _ = 4 * M := by ring
    calc (Finset.univ.filter (fun j : Fin (Fintype.card (Coord V M)) =>
            j ∈ ((pairEdges v w u).biUnion (lambdaStar s M)).image
              (coordEquiv V M))).card
        = (((pairEdges v w u).biUnion (lambdaStar s M)).image
            (coordEquiv V M)).card := by
          congr 1
          ext jj
          simp
      _ ≤ ((pairEdges v w u).biUnion (lambdaStar s M)).card :=
          Finset.card_image_le
      _ ≤ 4 * M := hbi
  · rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

open scoped Classical in
open scoped Classical in
/-- **Kim (36)**: `E[Φ_{A,B}] ≤ (1−p)^{2M−2D}·|Γ(A,B)| ≤ b'|A||B| − b⁶θ⁶n`.

By (33) each truncated survival probability is at most `(1−p)^{2M−2D}`, where
`D` is the (34)/(35) bound on the non-low `Λ`-partners; the number of terms is
`|Γ(A,B)|`, which Property 6 bounds by `b|A||B|`. -/
theorem property6_mean_le (s : BlockState V) (M : ℕ) (A B : Finset V)
    (thr : ℝ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {D : ℕ}
    (hM : ∀ e ∈ gammaBetween s.Γ A B, ∀ v ∈ edgeVerts e,
      (lambdaAt s e v).card ≤ M)
    (hD : ∀ e ∈ gammaBetween s.Γ A B, ∀ v ∈ edgeVerts e,
      ((lambdaAt s e v).filter
        (fun g => ¬ IsLowPair s A B thr g v)).card ≤ D)
    {target : ℝ}
    (hnum : (1 - p) ^ (2 * M - 2 * D)
      * ((gammaBetween s.Γ A B).card : ℝ) ≤ target) :
    bernoulliExp p (fun σ =>
        ∑ e ∈ gammaBetween s.Γ A B,
          (if σ ∈ survEventLow s M A B thr e then (1 : ℝ) else 0))
      ≤ target :=
  le_trans
    (bernoulliExp_count_le (gammaBetween s.Γ A B) (survEventLow s M A B thr)
      (fun e he => bernoulliPr_survEventLow_le s M A B thr hp0 hp1 e
        (hM e he) (hD e he)))
    hnum

open scoped Classical in
/-- **Kim §4.7's tail**: exceeding the target forces a deviation of `λ` above
the mean, which Kahn's inequality with `c_e ≤ 2·thr` controls. -/
theorem property6_tail (s : BlockState V) (M : ℕ) (A B : Finset V)
    {thr : ℝ} (hthr : 1 ≤ thr) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {D : ℕ}
    (hM : ∀ e ∈ gammaBetween s.Γ A B, ∀ v ∈ edgeVerts e,
      (lambdaAt s e v).card ≤ M)
    (hD : ∀ e ∈ gammaBetween s.Γ A B, ∀ v ∈ edgeVerts e,
      ((lambdaAt s e v).filter
        (fun g => ¬ IsLowPair s A B thr g v)).card ≤ D)
    {t lam target : ℝ} (ht : 0 ≤ t)
    (hmean : (1 - p) ^ (2 * M - 2 * D)
      * ((gammaBetween s.Γ A B).card : ℝ) ≤ target - lam) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          target < ∑ e ∈ gammaBetween s.Γ A B,
            (if σ ∈ survEventLow s M A B thr e then (1 : ℝ) else 0)))
      ≤ Real.exp (-t * lam + t ^ 2 / 2 * (p * (1 - p)
          * ((2 * thr) * (2 * M * (gammaBetween s.Γ A B).card)
            * Real.exp (t * (2 * thr))))) := by
  classical
  have hE := property6_mean_le s M A B thr hp0 hp1 hM hD hmean
  refine le_trans (bernoulliPr_mono hp0 hp1 ?_)
    (property6_concentration s M hp0 hp1 A B hthr (gammaBetween s.Γ A B)
      (Finset.Subset.refl _) hM (lam := lam) ht)
  intro σ hσ
  obtain ⟨-, hgt⟩ := Finset.mem_filter.mp hσ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩

open scoped Classical in
/-- **Kim (24)**: the `Φ⁽²⁾` tail for Property 4.

`E[Φ⁽²⁾] = p·d_Δ(e_vw) ≤ b²θ√n` by Property 5, and the master sampled-edge
estimate controls the deviation `b²θ²(a+5θ)√n`; Kim uses `ρ = n^{−1/4}`. -/
theorem property4_Phi2_tail (s : BlockState V) (M : ℕ) (k : ℕ) (e : Edge V)
    (v : V) (he : e ∈ s.Γ) (hv : v ∈ edgeVerts e) (hn : 0 < n)
    (hlogn : 1 ≤ Real.log n) (h5 : Property5 s k) {t : ℝ} (ht : 0 ≤ t)
    (hvar : t ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
        * (((deltaEdgesAt s v (otherEndOf v e)).card : ℝ) * Real.exp t))
      ≤ t * (bSeq n k ^ 2 * theta n ^ 2 * (aSeq n k + 5 * theta n)
          * Real.sqrt n) / 2)
    (hexp : Real.log 2 + 4 * Real.log n
      ≤ t * (bSeq n k ^ 2 * theta n ^ 2 * (aSeq n k + 5 * theta n)
          * Real.sqrt n) / 2) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          bSeq n k ^ 2 * theta n * Real.sqrt n
              + bSeq n k ^ 2 * theta n ^ 2 * (aSeq n k + 5 * theta n)
                * Real.sqrt n
            < ((deltaEdgesAt s v (otherEndOf v e) ∩ sampleP s M σ).card : ℝ)))
      ≤ ((n : ℝ) ^ (4 : ℕ))⁻¹ := by
  classical
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  set A : Finset (Edge V) := deltaEdgesAt s v (otherEndOf v e) with hA
  have hAΓ : A ⊆ s.Γ := deltaEdgesAt_subset s v (otherEndOf v e)
  have hmean := edgeProb_mul_deltaEdgesAt_le s k e v he hv hn h5
  have htail := sampleEdges_inter_tail (padEmb V M) hp0 hp1 s hAΓ ht hvar
  refine le_trans (bernoulliPr_mono hp0 hp1 (?_ : _ ⊆ Finset.univ.filter
    (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
      edgeProb n * (A.card : ℝ)
          + bSeq n k ^ 2 * theta n ^ 2 * (aSeq n k + 5 * theta n)
            * Real.sqrt n
        ≤ ((A ∩ sampleEdges (padEmb V M) s σ).card : ℝ)))) ?_
  · intro σ hσ
    obtain ⟨-, hgt⟩ := Finset.mem_filter.mp hσ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [sampleP_eq] at hgt
    linarith
  · refine htail.trans ?_
    rw [neg_div]
    exact two_exp_le_inv_pow hn 4 hexp

open scoped Classical in
/-- **Property 4 survives one block step.**

Kim §4.5: `d_{Λ'}(e_vw, v) ≤ Φ⁽¹⁾ + Φ⁽²⁾` by (23); `Φ⁽¹⁾` is a survivor count
over `N_Λ(e_vw, v)` (handled by Lemma 4.1 and Kahn with `c_e ≤ 1 + 3k log n`),
and `Φ⁽²⁾` is a sampled-edge count over the `Δ`-edges at `w` (handled by the
master estimate). The union runs over (edge, endpoint) pairs. -/
theorem property4_prob (k : ℕ) (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n)
    (hΦ1 : ∀ e ∈ s.Γ, ∀ v ∈ edgeVerts e, bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          bSeq n (k + 1) * (aSeq n k + 5 * theta n) * Real.sqrt n
              - 3 * bSeq n k ^ 2 * theta n ^ 2
                * (aSeq n k + 5 * theta n) * Real.sqrt n
            < ∑ f ∈ lambdaAt s e v,
                (if σ ∈ survEvent s M f then (1 : ℝ) else 0)))
      ≤ ((n : ℝ) ^ (4 : ℕ))⁻¹)
    (hΦ2 : ∀ e ∈ s.Γ, ∀ v ∈ edgeVerts e, bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          bSeq n k ^ 2 * theta n * Real.sqrt n
              + bSeq n k ^ 2 * theta n ^ 2 * (aSeq n k + 5 * theta n)
                * Real.sqrt n
            < ((deltaEdgesAt s v (otherEndOf v e) ∩ sampleP s M σ).card : ℝ)))
      ≤ ((n : ℝ) ^ (4 : ℕ))⁻¹) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          ¬ Property4 (blockStepP s M σ) (k + 1)))
      ≤ 2 * ((Fintype.card (Edge V) : ℝ) * n) * ((n : ℝ) ^ (4 : ℕ))⁻¹ := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine le_trans (bernoulliPr_mono hp0 hp1 (?_ :
      (Finset.univ.filter (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ¬ Property4 (blockStepP s M σ) (k + 1)))
      ⊆ (Finset.univ.filter (fun q : Edge V × V =>
          q.1 ∈ s.Γ ∧ q.2 ∈ edgeVerts q.1)).biUnion (fun q =>
        (Finset.univ.filter (fun σ =>
          bSeq n (k + 1) * (aSeq n k + 5 * theta n) * Real.sqrt n
              - 3 * bSeq n k ^ 2 * theta n ^ 2
                * (aSeq n k + 5 * theta n) * Real.sqrt n
            < ∑ f ∈ lambdaAt s q.1 q.2,
                (if σ ∈ survEvent s M f then (1 : ℝ) else 0)))
        ∪ (Finset.univ.filter (fun σ =>
          bSeq n k ^ 2 * theta n * Real.sqrt n
              + bSeq n k ^ 2 * theta n ^ 2 * (aSeq n k + 5 * theta n)
                * Real.sqrt n
            < ((deltaEdgesAt s q.2 (otherEndOf q.2 q.1)
                ∩ sampleP s M σ).card : ℝ)))))) ?_
  · intro σ hσ
    obtain ⟨-, hfail⟩ := Finset.mem_filter.mp hσ
    rw [Property4] at hfail
    push_neg at hfail
    obtain ⟨v, w, hvw, hmem, hgt⟩ := hfail
    have hother : otherEndOf v (mkEdge hvw) = w := by
      have hv : v ∈ (mkEdge hvw).val := by simp
      have hspec : (mkEdge hvw).val = s(v, otherEndOf v (mkEdge hvw)) :=
        edge_eq_of_otherEndOf hv
      rw [mkEdge_val] at hspec
      exact ((Sym2.congr_right).mp hspec).symm
    refine Finset.mem_biUnion.mpr ⟨(mkEdge hvw, v),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        blockStepP_Γ_subset s M σ hmem, mem_edgeVerts.mpr (by simp)⟩, ?_⟩
    by_contra hcon
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, not_or, not_lt] at hcon
    obtain ⟨h1, h2⟩ := hcon
    rw [hother] at h2
    exact absurd (le_trans (lambdaDeg_blockStepP_le s M σ hvw)
      (property4_combine h1 h2)) (not_le.mpr hgt)
  refine le_trans (bernoulliPr_biUnion_le hp0 hp1 _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : Edge V × V =>
    2 * ((n : ℝ) ^ (4 : ℕ))⁻¹) fun q hq' => ?_) ?_
  · show (_ : ℝ) ≤ 2 * ((n : ℝ) ^ (4 : ℕ))⁻¹
    refine le_trans (bernoulliPr_union_le hp0 hp1 _ _) ?_
    have hq := (Finset.mem_filter.mp hq').2
    have := hΦ1 q.1 hq.1 q.2 hq.2
    have := hΦ2 q.1 hq.1 q.2 hq.2
    linarith
  · rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ.filter (fun q : Edge V × V =>
        q.1 ∈ s.Γ ∧ q.2 ∈ edgeVerts q.1)).card : ℝ)
        ≤ (Fintype.card (Edge V) : ℝ) * n := by
      have h := Finset.card_le_univ (Finset.univ.filter
        (fun q : Edge V × V => q.1 ∈ s.Γ ∧ q.2 ∈ edgeVerts q.1))
      rw [Fintype.card_prod] at h
      calc ((Finset.univ.filter (fun q : Edge V × V =>
            q.1 ∈ s.Γ ∧ q.2 ∈ edgeVerts q.1)).card : ℝ)
          ≤ ((Fintype.card (Edge V) * Fintype.card V : ℕ) : ℝ) := by
            exact_mod_cast h
        _ = (Fintype.card (Edge V) : ℝ) * n := by push_cast; ring
    have hpos : (0 : ℝ) ≤ 2 * ((n : ℝ) ^ (4 : ℕ))⁻¹ := by positivity
    calc ((Finset.univ.filter (fun q : Edge V × V =>
          q.1 ∈ s.Γ ∧ q.2 ∈ edgeVerts q.1)).card : ℝ)
            * (2 * ((n : ℝ) ^ (4 : ℕ))⁻¹)
        ≤ ((Fintype.card (Edge V) : ℝ) * n) * (2 * ((n : ℝ) ^ (4 : ℕ))⁻¹) :=
          mul_le_mul_of_nonneg_right hcard hpos
      _ = 2 * ((Fintype.card (Edge V) : ℝ) * n) * ((n : ℝ) ^ (4 : ℕ))⁻¹ := by
          ring

open scoped Classical in
/-- **Property 1 in the padded model.** -/
theorem property1_probP (k : ℕ) (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (h1 : Property1 s k) (hn : 0 < n)
    (hdeg : ∀ v : V, bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          bSeq n k * theta n * Real.sqrt n
              + (n : ℝ) ^ (1 / 4 : ℝ) * Real.log n
            < (degEdges (sampleP s M σ) v : ℝ)))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          ¬ Property1 (blockStepP s M σ) (k + 1)))
      ≤ ((n : ℝ) ^ (2 : ℕ))⁻¹ := by
  classical
  have hmain := property1_prob (padEmb V M) k s hp₀ hp₁ h1 hn
    (by simpa only [sampleP_eq] using hdeg)
  refine le_trans (le_of_eq ?_) hmain
  congr 1

open scoped Classical in
/-- **Property 3 in the padded model.** -/
theorem property3_probP (k : ℕ) (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (h3 : Property3 s k) (hn : 0 < n)
    (hA : ∀ v w : V, v ≠ w → bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          Real.log n < ((nbrs (sampleP s M σ) v ∩ nbrs s.E w).card : ℝ)))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹)
    (hB : ∀ v w : V, v ≠ w → bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          Real.log n < ((nbrs s.E v ∩ nbrs (sampleP s M σ) w).card : ℝ)))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹)
    (hC : ∀ v w : V, v ≠ w → bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          Real.log n < ((commonNbrs (sampleP s M σ) v w).card : ℝ)))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          ¬ Property3 (blockStepP s M σ) (k + 1))) ≤ 3 / n := by
  classical
  have hmain := property3_prob (padEmb V M) k s hp₀ hp₁ h3 hn
    (by simpa only [sampleP_eq] using hA)
    (by simpa only [sampleP_eq] using hB)
    (by simpa only [sampleP_eq] using hC)
  refine le_trans (le_of_eq ?_) hmain
  congr 1

/-- **Property 2 gives Kim's mean `p·d_Γ(v) ≤ bθ√n`** for Lemma 4.3(i). -/
lemma edgeProb_mul_degGamma_le (s : BlockState V) (k : ℕ) (v : V)
    (hn : 0 < n) (h2 : Property2 s k) :
    edgeProb n * ((degEdges s.Γ v : ℕ) : ℝ)
      ≤ bSeq n k * theta n * Real.sqrt n := by
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt0 : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnR.le
  calc edgeProb n * ((degEdges s.Γ v : ℕ) : ℝ)
      ≤ edgeProb n * (bSeq n k * n) := mul_le_mul_of_nonneg_left (h2 v) hp0
    _ = bSeq n k * theta n * Real.sqrt n := by
        have hdiv : (n : ℝ) / Real.sqrt n = Real.sqrt n := Real.div_sqrt
        rw [edgeProb]
        calc theta n / Real.sqrt n * (bSeq n k * n)
            = bSeq n k * theta n * ((n : ℝ) / Real.sqrt n) := by ring
          _ = bSeq n k * theta n * Real.sqrt n := by rw [hdiv]

/-- **Kim's padding budget** `M = ⌊b_k(a_k + 5θ)√n⌋`, the exact `Λ*`-degree of
(19). -/
noncomputable def kimM (N : ℕ) (k : ℕ) : ℕ :=
  ⌊bSeq N k * (aSeq N k + 5 * theta N) * Real.sqrt N⌋₊

/-- `M = ⌊b(a+5θ)√N⌋ ≤ b(a+5θ)√N`. -/
lemma kimM_le (N k : ℕ) :
    (kimM N k : ℝ) ≤ bSeq N k * (aSeq N k + 5 * theta N) * Real.sqrt N := by
  refine Nat.floor_le ?_
  have := (bSeq_pos N k).le
  have := aSeq_nonneg N k
  have := theta_nonneg N
  positivity

/-- `b(a+5θ)√N < M + 1`. -/
lemma lt_kimM_add_one (N k : ℕ) :
    bSeq N k * (aSeq N k + 5 * theta N) * Real.sqrt N < (kimM N k : ℝ) + 1 :=
  Nat.lt_floor_add_one _

/-- **The padding budget is right, up to the floor.** `2M·p ≤ 2bθ(a+5θ)`. -/
lemma two_kimM_mul_edgeProb_le {N : ℕ} (k : ℕ) (hN : 1 ≤ N) :
    ((2 * kimM N k : ℕ) : ℝ) * edgeProb N
      ≤ 2 * bSeq N k * theta N * (aSeq N k + 5 * theta N) := by
  have hsq : (1 : ℝ) ≤ Real.sqrt N := one_le_sqrt_cast hN
  have hp : 0 ≤ edgeProb N := edgeProb_nonneg N
  have hstep : ((2 * kimM N k : ℕ) : ℝ) * edgeProb N
      ≤ (2 * (bSeq N k * (aSeq N k + 5 * theta N) * Real.sqrt N))
        * edgeProb N := by
    refine mul_le_mul_of_nonneg_right ?_ hp
    push_cast
    linarith [kimM_le N k]
  refine hstep.trans (le_of_eq ?_)
  have hkey := sqrt_mul_edgeProb hN
  linear_combination (2 * bSeq N k * (aSeq N k + 5 * theta N)) * hkey

/-- The floor costs at most `2p`: `2bθ(a+5θ) − 2p ≤ 2M·p`. -/
lemma two_kimM_mul_edgeProb_ge {N : ℕ} (k : ℕ) (hN : 1 ≤ N) :
    2 * bSeq N k * theta N * (aSeq N k + 5 * theta N) - 2 * edgeProb N
      ≤ ((2 * kimM N k : ℕ) : ℝ) * edgeProb N := by
  have hsq : (1 : ℝ) ≤ Real.sqrt N := one_le_sqrt_cast hN
  have hp : 0 ≤ edgeProb N := edgeProb_nonneg N
  have hstep : (2 * (bSeq N k * (aSeq N k + 5 * theta N) * Real.sqrt N) - 2)
      * edgeProb N ≤ ((2 * kimM N k : ℕ) : ℝ) * edgeProb N := by
    refine mul_le_mul_of_nonneg_right ?_ hp
    push_cast
    linarith [lt_kimM_add_one N k]
  refine le_trans (le_of_eq ?_) hstep
  have hkey := sqrt_mul_edgeProb hN
  linear_combination (-(2 * bSeq N k * (aSeq N k + 5 * theta N))) * hkey

open scoped Classical in

/-- **Property 4 supplies Kim's padding budget.** For every `Γ`-edge and either
of its endpoints, the number of genuine `Λ`-partners is at most
`M = ⌊b_k(a_k+5θ)√n⌋`, which is exactly what the padding of (19) tops up. -/
lemma lambdaAt_card_le_kimM (k : ℕ) (s : BlockState V) (h4 : Property4 s k) :
    ∀ g ∈ s.Γ, ∀ u ∈ edgeVerts g, (lambdaAt s g u).card ≤ kimM n k := by
  classical
  intro g hg u hu
  have hug : u ∈ g.val := mem_edgeVerts.mp hu
  set w : V := otherEndOf u g with hw
  have hspec : g.val = s(u, w) := edge_eq_of_otherEndOf hug
  have huw : u ≠ w := by
    intro hEq
    exact g.2 (by rw [hspec, ← hEq]; simp)
  have hgmk : mkEdge huw = g := Subtype.ext (by rw [mkEdge_val, hspec])
  have hbound := h4 u w huw (by rw [hgmk]; exact hg)
  rw [card_lambdaAt s g u, ← hw]
  refine Nat.le_floor ?_
  exact hbound


open scoped Classical in
/-- **Property 1 propagates, unconditionally on numerics.**

Kim §4.2: `d_{ℰ'}(v) = d_ℰ(v) + |N_{X'}(v)|`, and Lemma 4.3(i) bounds the second
term by `bθ√n + n^{1/4}log n`. -/
theorem property1_numeric (k : ℕ) (s : BlockState V) (M : ℕ)
    (hn : 0 < n) (hlogn : 1 ≤ Real.log n)
    (h1 : Property1 s k) (h2 : Property2 s k)
    (hsmall : 8 / ((n : ℝ) ^ ((1 : ℝ) / 4)) ≤ 1)
    (hlog2 : Real.log 2 ≤ Real.log n)
    (hvar' : 32 * (bSeq n k * theta n) * Real.exp 1 ≤ 4 * Real.log n) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          ¬ Property1 (blockStepP s M σ) (k + 1)))
      ≤ ((n : ℝ) ^ (2 : ℕ))⁻¹ := by
  classical
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  refine property1_probP k s M hp0 hp1 h1 hn fun v => ?_
  have hmain := lemma43_i_numeric s M k v hn hlogn
    (edgeProb_mul_degGamma_le s k v hn h2) hsmall hlog2 hvar'
  refine le_trans (bernoulliPr_mono hp0 hp1 ?_) hmain
  intro σ hσ
  obtain ⟨-, hgt⟩ := Finset.mem_filter.mp hσ
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have hmean := edgeProb_mul_degGamma_le s k v hn h2
  linarith

open scoped Classical in
/-- **Property 3 propagates, unconditionally on numerics.**

Kim §4.4: the three codegree terms are Lemma 4.3(ii) (in both orientations) and
Lemma 4.3(iii); all three are now instantiated at concrete parameters, so the
only remaining hypotheses are largeness facts about `n`. -/
theorem property3_numeric (k : ℕ) (s : BlockState V) (M : ℕ)
    (hn : 0 < n) (hθpos : 0 < theta n) (hlogn : 1 ≤ Real.log n)
    (hloglog : Real.exp 1 ≤ Real.log n)
    (hk : k ≤ ⌊(n : ℝ) ^ kimDelta / theta n⌋₊)
    (h1 : Property1 s k) (h3 : Property3 s k)
    (hA : (Real.sqrt (kimDelta * Real.log n) + 1 + theta n) * theta n ≤ 1 / 2)
    (hB : (n : ℝ) ^ kimDelta * Real.log n / (n : ℝ) ^ ((1 : ℝ) / 4) ≤ 1 / 2)
    (hlog1 : Real.log 2 + 7 ≤ 4 * Real.log n)
    (hlog2 : 98 * Real.exp 14 + 7 ≤ 7 * Real.log n) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          ¬ Property3 (blockStepP s M σ) (k + 1))) ≤ 3 / n := by
  classical
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  have hmean : ∀ x y : V, edgeProb n * ((crossEdges s x y).card : ℝ) ≤ 1 :=
    fun x y => edgeProb_mul_crossEdges_le_one s k x y hn hθpos hk h1 hA hB
  refine property3_probP k s M hp0 hp1 h3 hn ?_ ?_ ?_
  · -- `|N_{X'}(v) ∩ N_ℰ(w)|`: Lemma 4.3(ii) with the roles swapped
    intro v w hvw
    have := lemma43_ii_numeric s M w v hn (hmean w v) hlog1 hlog2
    refine le_trans (le_of_eq ?_) this
    congr 1
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.inter_comm (nbrs (sampleP s M σ) v) (nbrs s.E w)]
  · -- `|N_ℰ(v) ∩ N_{X'}(w)|`: Lemma 4.3(ii) directly
    intro v w hvw
    exact lemma43_ii_numeric s M v w hn (hmean v w) hlog1 hlog2
  · -- `|N_{X'}(v) ∩ N_{X'}(w)|`: Lemma 4.3(iii)
    intro v w hvw
    have := lemma43_iii_numeric s M v w hvw hn hlogn hloglog
    refine le_trans (le_of_eq ?_) this
    congr 1
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      commonNbrs_eq_inter]


open scoped Classical in
/-- **Property 2 survives one block step with probability at least `1 − 1/n²`.**

This is Kim §4.3 in full: `d_{Γ'}(v) ≤ Φ_v` by (21), `E[Φ_v] ≤ b'n − b²θ²n` by
Lemma 4.1 and (13), and `Pr(Φ_v − E[Φ_v] ≥ b²θ²n)` is bounded by Kahn's
inequality with `c_e ≤ 2M`, `Σc_e² ≤ 4M²d_Γ(v)`. A union bound over the `n`
vertices gives `1/n²`. -/
theorem property2_prob (k : ℕ) (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h2 : Property2 s k) (hn : 0 < n)
    (hθsmall : theta n ≤ 1 / 100)
    (hM : ∀ g ∈ s.Γ, ∀ u ∈ edgeVerts g, (lambdaAt s g u).card ≤ M)
    {err : ℝ} (herr : 0 ≤ err)
    (hMp_hi : ((2 * M : ℕ) : ℝ) * p
      ≤ 2 * bSeq n k * theta n * (aSeq n k + 5 * theta n))
    (hMp_lo : 2 * bSeq n k * theta n * (aSeq n k + 5 * theta n) - err
      ≤ ((2 * M : ℕ) : ℝ) * p)
    (hslack : bSeq n k * err ≤ 3 * bSeq n k ^ 2 * theta n ^ 2)
    {t : ℝ} (ht : 0 ≤ t)
    (hexp : ∀ v : V, Real.exp (-t * (bSeq n k ^ 2 * theta n ^ 2 * n)
        + t ^ 2 / 2 * (p * (1 - p) * ((2 * M : ℝ)
          * (2 * M * (edgesAt s.Γ v).card) * Real.exp (t * (2 * M)))))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹) :
    bernoulliPr p (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          ¬ Property2 (blockStepP s M σ) (k + 1)))
      ≤ ((n : ℝ) ^ (2 : ℕ))⁻¹ := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set lam : ℝ := bSeq n k ^ 2 * theta n ^ 2 * n with hlam
  set Phi : V → (Fin (Fintype.card (Coord V M)) → Bool) → ℝ := fun v σ =>
    ∑ f ∈ edgesAt s.Γ v, (if σ ∈ survEvent s M f then (1 : ℝ) else 0) with hPhi
  -- Each vertex's mean is small enough that exceeding `b'n` forces a deviation.
  have hmean : ∀ v : V, bernoulliExp p (Phi v)
      ≤ bSeq n (k + 1) * n - lam := by
    intro v
    refine property2_expectation s M hp0 hp1 v hθsmall
      (fun e he u hu => hM e (Finset.mem_filter.mp he).1 u hu)
      herr hMp_hi hMp_lo hslack (le_of_lt hnR) ?_
    exact h2 v
  refine le_trans (bernoulliPr_mono hp0 hp1 (?_ :
      (Finset.univ.filter (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ¬ Property2 (blockStepP s M σ) (k + 1)))
      ⊆ (Finset.univ : Finset V).biUnion (fun v =>
        Finset.univ.filter (fun σ =>
          lam ≤ Phi v σ - bernoulliExp p (Phi v))))) ?_
  · intro σ hσ
    obtain ⟨-, hfail⟩ := Finset.mem_filter.mp hσ
    rw [Property2] at hfail
    push_neg at hfail
    obtain ⟨v, hv⟩ := hfail
    refine Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have hdom := degEdges_blockStepP_le s M σ v
    have hm := hmean v
    linarith
  refine le_trans (bernoulliPr_biUnion_le hp0 hp1 _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : V => ((n : ℝ) ^ (3 : ℕ))⁻¹)
    fun v _ => ?_) ?_
  · exact le_trans (property2_concentration s M hp0 hp1 (edgesAt s.Γ v)
      (Finset.filter_subset _ _) hM ht) (hexp v)
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [show ((Fintype.card V : ℕ) : ℝ) = (n : ℝ) from rfl]
    rw [show (n : ℝ) * ((n : ℝ) ^ (3 : ℕ))⁻¹ = ((n : ℝ) ^ (2 : ℕ))⁻¹ by
      field_simp]

open scoped Classical in
/-- **Kim (25)**: `E[Φ⁽¹⁾_{v,w}] ≤ b'(a+5θ)√n − 4b²θ²(a+5θ)√n`.

Lemma 4.1 bounds each survival probability, Property 4 bounds the number of
terms by `b(a+5θ)√n`, and (13) turns `b·Pr` into `b' − 5b²θ²`.

Kim carries an extra `(1+2p)` from conditioning on `e_vw ∉ X'`; we do not need
it, because our (23) is proved unconditionally. -/
theorem property4_Phi1_mean (s : BlockState V) (k : ℕ) (e : Edge V) (v : V)
    (he : e ∈ s.Γ) (hv : v ∈ edgeVerts e) (hn : 0 < n)
    (hlogn : 1 ≤ Real.log n) (hθsmall : theta n ≤ 1 / 100)
    (h4 : Property4 s k)
    (hslack : 2 * edgeProb n ≤ 3 * bSeq n k * theta n ^ 2) :
    bernoulliExp (edgeProb n) (fun σ =>
        ∑ f ∈ lambdaAt s e v,
          (if σ ∈ survEvent s (kimM n k) f then (1 : ℝ) else 0))
      ≤ bSeq n (k + 1) * (aSeq n k + 5 * theta n) * Real.sqrt n
        - 5 * bSeq n k ^ 2 * theta n ^ 2 * (aSeq n k + 5 * theta n)
          * Real.sqrt n := by
  classical
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  have hb := bSeq_pos n k
  have hθ := theta_nonneg n
  have ha := aSeq_nonneg n k
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  set err : ℝ := 2 * edgeProb n with herrdef
  have herr : 0 ≤ err := by positivity
  set q : ℝ := 1 - 2 * aSeq n k * bSeq n k * theta n
    - 9 * bSeq n k * theta n ^ 2 + err with hq
  have hslack' : bSeq n k * err ≤ 3 * bSeq n k ^ 2 * theta n ^ 2 := by
    calc bSeq n k * err ≤ bSeq n k * (3 * bSeq n k * theta n ^ 2) :=
          mul_le_mul_of_nonneg_left hslack hb.le
      _ = 3 * bSeq n k ^ 2 * theta n ^ 2 := by ring
  -- `E[Φ] ≤ q·|S|`
  have hmean := survivorCount_expectation s (kimM n k) hp0 hp1 (lambdaAt s e v)
    hθsmall (fun f hf u hu => lambdaAt_card_le_kimM k s h4 f
      (lambdaAt_subset s e v hf |> fun h => h) u hu)
    herr (two_kimM_mul_edgeProb_le k hn) (two_kimM_mul_edgeProb_ge k hn)
  -- `q ≥ 0`
  have hq0 : 0 ≤ q := by
    have h := lemma41_bounds (N := n) k hθsmall hp0 hp1 (2 * kimM n k) herr
      (two_kimM_mul_edgeProb_le k hn) (two_kimM_mul_edgeProb_ge k hn)
    have hpow : (0 : ℝ) ≤ (1 - edgeProb n) ^ (2 * kimM n k) :=
      pow_nonneg (by linarith) _
    exact le_trans hpow h.2
  -- `|S| ≤ b(a+5θ)√n` by Property 4
  have hcard : ((lambdaAt s e v).card : ℝ)
      ≤ bSeq n k * (aSeq n k + 5 * theta n) * Real.sqrt n := by
    have hve : v ∈ e.val := mem_edgeVerts.mp hv
    set w : V := otherEndOf v e with hw
    have hspec : e.val = s(v, w) := edge_eq_of_otherEndOf hve
    have hvw : v ≠ w := by
      intro hEq
      exact e.2 (by rw [hspec, ← hEq]; simp)
    have hmk : mkEdge hvw = e := Subtype.ext (by rw [mkEdge_val, hspec])
    have := h4 v w hvw (by rw [hmk]; exact he)
    rw [card_lambdaAt s e v, ← hw]
    exact this
  refine hmean.trans ?_
  -- combine with (13)
  have hsurv := bSeq_mul_surv_le n k herr hslack' (le_refl q)
  have hstep : q * ((lambdaAt s e v).card : ℝ)
      ≤ q * (bSeq n k * (aSeq n k + 5 * theta n) * Real.sqrt n) :=
    mul_le_mul_of_nonneg_left hcard hq0
  refine hstep.trans ?_
  have hpos : 0 ≤ (aSeq n k + 5 * theta n) * Real.sqrt n := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hsurv hpos, hpos]

open scoped Classical in
/-- **Kim (27)**: the `Φ⁽¹⁾` tail for Property 4.

`E[Φ⁽¹⁾] ≤ b'(a+5θ)√n − 4b²θ²(a+5θ)√n` by (25), so exceeding
`b'(a+5θ)√n − 3b²θ²(a+5θ)√n` forces a deviation of `b²θ²(a+5θ)√n`; Kahn's
inequality with `c_e ≤ C+2` (Kim's `1 + 3k log n`) controls it. -/
theorem property4_Phi1_tail (s : BlockState V) (k : ℕ) (e : Edge V) (v : V)
    (he : e ∈ s.Γ) (hv : v ∈ edgeVerts e) (hn : 0 < n)
    (hlogn : 1 ≤ Real.log n) (hθsmall : theta n ≤ 1 / 100)
    (h4 : Property4 s k)
    (hslack : 2 * edgeProb n ≤ 3 * bSeq n k * theta n ^ 2)
    (hp2 : edgeProb n ≤ 1 / 2)
    (hbb : bSeq n (k + 1) ≤ bSeq n k ^ 2 * theta n * Real.sqrt n)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hbound : ∀ w w' : V, w ≠ w' → ((commonNbrs s.E w w').card : ℝ) ≤ C)
    {t : ℝ} (ht : 0 ≤ t)
    (hexp : Real.exp (-t * (bSeq n k ^ 2 * theta n ^ 2
          * (aSeq n k + 5 * theta n) * Real.sqrt n)
        + t ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
          * ((C + 2) * (2 * kimM n k * (lambdaAt s e v).card)
            * Real.exp (t * (C + 2)))))
      ≤ ((n : ℝ) ^ (4 : ℕ))⁻¹) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          bSeq n (k + 1) * (aSeq n k + 5 * theta n) * Real.sqrt n
              - 3 * bSeq n k ^ 2 * theta n ^ 2 * (aSeq n k + 5 * theta n)
                * Real.sqrt n
            < ∑ f ∈ lambdaAt s e v,
                (if σ ∈ survEvent s (kimM n k) f then (1 : ℝ) else 0)))
      ≤ ((n : ℝ) ^ (4 : ℕ))⁻¹ := by
  classical
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  have hn1 : 1 ≤ n := hn
  have hb := bSeq_pos n k
  have hθ := theta_nonneg n
  have ha := aSeq_nonneg n k
  have hsq0 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hP : (0 : ℝ) ≤ (aSeq n k + 5 * theta n) * Real.sqrt n := by positivity
  have hYnn : (0 : ℝ) ≤ bSeq n k ^ 2 * theta n ^ 2
      * (aSeq n k + 5 * theta n) * Real.sqrt n := by positivity
  -- Kim's `(1 + 2p)` conditioning factor: freeze the coordinate of `e` itself
  set j₀ : Fin (Fintype.card (Coord V (kimM n k))) :=
    coordEquiv V (kimM n k) (Sum.inl e) with hj₀
  have hnonneg : ∀ σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool,
      (0 : ℝ) ≤ ∑ f ∈ lambdaAt s e v,
        (if σ ∈ survEvent s (kimM n k) f then (1 : ℝ) else 0) :=
    fun σ => Finset.sum_nonneg fun f _ => by split <;> norm_num
  have hfrz := bernoulliExp_freeze_le hp0 hp1 j₀
    (fun σ => ∑ f ∈ lambdaAt s e v,
      (if σ ∈ survEvent s (kimM n k) f then (1 : ℝ) else 0)) hnonneg
  have hmeanΦ := property4_Phi1_mean s k e v he hv hn hlogn hθsmall h4 hslack
  -- `p·b'(a+5θ)√n ≤ b²θ²(a+5θ)√n`, which absorbs the conditioning factor
  have hsqe : Real.sqrt n * edgeProb n = theta n := sqrt_mul_edgeProb hn1
  have hpX : edgeProb n * (bSeq n (k + 1) * (aSeq n k + 5 * theta n)
        * Real.sqrt n)
      ≤ bSeq n k ^ 2 * theta n ^ 2 * (aSeq n k + 5 * theta n) * Real.sqrt n := by
    have hrw : edgeProb n * (bSeq n (k + 1) * (aSeq n k + 5 * theta n)
          * Real.sqrt n)
        = theta n * (bSeq n (k + 1) * (aSeq n k + 5 * theta n)) := by
      rw [← hsqe]; ring
    rw [hrw]
    have hstep : bSeq n (k + 1) * (aSeq n k + 5 * theta n)
        ≤ bSeq n k ^ 2 * theta n * Real.sqrt n * (aSeq n k + 5 * theta n) :=
      mul_le_mul_of_nonneg_right hbb (by positivity)
    nlinarith [hstep, hθ, hb.le]
  have hmeanΨ : bernoulliExp (edgeProb n) (fun σ =>
        ∑ f ∈ lambdaAt s e v,
          (if Function.update σ j₀ false ∈ survEvent s (kimM n k) f
            then (1 : ℝ) else 0))
      ≤ bSeq n (k + 1) * (aSeq n k + 5 * theta n) * Real.sqrt n
        - 4 * bSeq n k ^ 2 * theta n ^ 2 * (aSeq n k + 5 * theta n)
          * Real.sqrt n := by
    have h1p : (0 : ℝ) < 1 - edgeProb n := by linarith
    refine le_of_mul_le_mul_left ?_ h1p
    refine le_trans hfrz (le_trans hmeanΦ ?_)
    nlinarith [hpX, hYnn, hp0]
  have hconc := survivorCount_concentration_freeze s (kimM n k) hp0 hp1
    (lambdaAt s e v)
    (fun f hf u hu => lambdaAt_card_le_kimM k s h4 f
      (lambdaAt_subset s e v hf) u hu)
    j₀ (by linarith : (0 : ℝ) ≤ C + 2)
    (fun j hj => card_filter_lambdaAt_le s (kimM n k) e v hv hC0 hbound j hj)
    (lam := bSeq n k ^ 2 * theta n ^ 2 * (aSeq n k + 5 * theta n)
      * Real.sqrt n) ht
  refine le_trans (bernoulliPr_mono hp0 hp1 ?_) (le_trans hconc hexp)
  intro σ hσ
  obtain ⟨-, hgt⟩ := Finset.mem_filter.mp hσ
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have hmono := survivorCount_le_freeze s (kimM n k) (lambdaAt s e v) j₀ σ
  linarith [hmeanΨ, hmono, hgt]

open scoped Classical in
/-- **Property 4 propagates**, with the padding budget, the two mean bounds and
the Lipschitz constant all discharged.

What remains are Kim's two exponent estimates, at `ρ = n^{−1/4}` for `Φ⁽²⁾`
(24) and `ρ = n^{−1/4−1/17}` for `Φ⁽¹⁾` (27). -/
theorem property4_numeric (k : ℕ) (s : BlockState V)
    (hn : 0 < n) (hlogn : 1 ≤ Real.log n) (hθsmall : theta n ≤ 1 / 100)
    (h4 : Property4 s k) (h5 : Property5 s k)
    (hslack : 2 * edgeProb n ≤ 3 * bSeq n k * theta n ^ 2)
    (hp2 : edgeProb n ≤ 1 / 2)
    (hbb : bSeq n (k + 1) ≤ bSeq n k ^ 2 * theta n * Real.sqrt n)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hbound : ∀ w w' : V, w ≠ w' → ((commonNbrs s.E w w').card : ℝ) ≤ C)
    {t1 t2 : ℝ} (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2)
    (hexp1 : ∀ e ∈ s.Γ, ∀ v ∈ edgeVerts e,
      Real.exp (-t1 * (bSeq n k ^ 2 * theta n ^ 2
            * (aSeq n k + 5 * theta n) * Real.sqrt n)
          + t1 ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
            * ((C + 2) * (2 * kimM n k * (lambdaAt s e v).card)
              * Real.exp (t1 * (C + 2)))))
        ≤ ((n : ℝ) ^ (4 : ℕ))⁻¹)
    (hvar2 : ∀ e ∈ s.Γ, ∀ v ∈ edgeVerts e,
      t2 ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
          * (((deltaEdgesAt s v (otherEndOf v e)).card : ℝ) * Real.exp t2))
        ≤ t2 * (bSeq n k ^ 2 * theta n ^ 2 * (aSeq n k + 5 * theta n)
            * Real.sqrt n) / 2)
    (hexp2 : Real.log 2 + 4 * Real.log n
      ≤ t2 * (bSeq n k ^ 2 * theta n ^ 2 * (aSeq n k + 5 * theta n)
          * Real.sqrt n) / 2) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property4 (blockStepP s (kimM n k) σ) (k + 1)))
      ≤ 2 * ((Fintype.card (Edge V) : ℝ) * n) * ((n : ℝ) ^ (4 : ℕ))⁻¹ := by
  classical
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  refine property4_prob k s (kimM n k) hp0 hp1 hn ?_ ?_
  · intro e he v hv
    exact property4_Phi1_tail s k e v he hv hn hlogn hθsmall h4 hslack hp2 hbb
      hC0 hbound ht1 (hexp1 e he v hv)
  · intro e he v hv
    exact property4_Phi2_tail s (kimM n k) k e v he hv hn hlogn h5 ht2
      (hvar2 e he v hv) hexp2

open scoped Classical in
lemma card_of_mem_calT {s : BlockState V} {T : Finset V} (hT : T ∈ calT s) :
    T.card = tParam n := by
  classical
  have h : T ∈ Finset.univ.filter (fun T => T.card = tParam n ∧
      ∀ e ∈ s.G, ¬ (∃ v ∈ T, ∃ w ∈ T, v ≠ w ∧ v ∈ e.val ∧ w ∈ e.val)) := hT
  exact ((Finset.mem_filter.mp h).2).1

open scoped Classical in
/-- **Property 7's step**, with the global events charged once: (40) enters as
a set inclusion into the complement of the good event and (47) is conditioned
on it, so neither is paid for `C(n,t)` times. -/
theorem property7_numeric' (k : ℕ) (s : BlockState V)
    (hn : 0 < n) (hlogn : 1 ≤ Real.log n)
    (h4 : Property4 s k) (h7 : Property7 s k)
    (thr : ℝ) (hthr : 1 ≤ thr)
    {c1 c2 c3 c4 : ℝ}
    (hsplit : c1 - c2 - c3 - c4
      = bSeq n (k + 1) * μSeq n (k + 1) * ((tParam n).choose 2))
    (Good : Finset (Fin (Fintype.card (Coord V (kimM n k))) → Bool))
    {q0 : ℝ} (hq0Good : bernoulliPr (edgeProb n) (Finset.univ \ Good) ≤ q0)
    {GG : ℝ} (hGG : ∀ T ∈ calT s,
      ((gammaBetween s.Γ T T).card : ℝ) ≤ GG)
    {L lam1 : ℝ} (hL0 : 0 ≤ L)
    (hL : L ≤ (1 - edgeProb n) ^ (2 * kimM n k))
    (hc1 : c1 + lam1
      ≤ L * (bSeq n k * μSeq n k * ((tParam n).choose 2)))
    {t1 : ℝ} (ht1 : 0 ≤ t1) {q1 : ℝ}
    (hq1 : Real.exp (-t1 * lam1 + t1 ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
        * ((2 * thr) * (2 * (kimM n k : ℝ) * GG)
            * Real.exp (t1 * (2 * thr))))) ≤ q1)
    {t3 lam3 : ℝ} (ht3 : 0 ≤ t3)
    (hvar3 : t3 ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
        * (GG * Real.exp t3)) ≤ t3 * lam3 / 2)
    (hc3 : edgeProb n * GG + lam3 ≤ c3)
    {q3 : ℝ} (hq3 : 2 * Real.exp (-(t3 * lam3) / 2) ≤ q3)
    {q4 : ℝ}
    (hb2 : ∀ T ∈ calT s, Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          c2 < ((killedY2 s (kimM n k) T thr σ).card : ℝ))
      ⊆ Finset.univ \ Good)
    (hb4 : ∀ T ∈ calT s, bernoulliPr (edgeProb n) ((Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          c4 < ((gammaBetween s.Γ T T
            ∩ killedZpure s (kimM n k) σ).card : ℝ))) ∩ Good) ≤ q4)
    (hq : 0 ≤ q1 + q3 + q4) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property7 (blockStepP s (kimM n k) σ) (k + 1)))
      ≤ q0 + ((n : ℕ).choose (tParam n) : ℝ) * (q1 + q3 + q4) := by
  classical
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  refine property7_prob' k s (kimM n k) hp0 hp1 thr hsplit Good
    hq0Good ?_ hb2 ?_ hb4 hq
  · -- (39)
    intro T hT
    have hM : ∀ e ∈ gammaBetween s.Γ T T, ∀ v ∈ edgeVerts e,
        (lambdaAt s e v).card ≤ kimM n k := fun e he v hv =>
      lambdaAt_card_le_kimM k s h4 e (mem_gammaBetween.mp he).1 v hv
    have hΓlb : bSeq n k * μSeq n k * ((tParam n).choose 2)
        ≤ ((gammaBetween s.Γ T T).card : ℝ) := h7 T hT
    have hpow : L * (bSeq n k * μSeq n k * ((tParam n).choose 2))
        ≤ (1 - edgeProb n) ^ (2 * kimM n k)
          * ((gammaBetween s.Γ T T).card : ℝ) := by
      have hstep : L * (bSeq n k * μSeq n k * ((tParam n).choose 2))
          ≤ L * ((gammaBetween s.Γ T T).card : ℝ) :=
        mul_le_mul_of_nonneg_left hΓlb hL0
      have hnn : (0 : ℝ) ≤ ((gammaBetween s.Γ T T).card : ℝ) :=
        Nat.cast_nonneg _
      nlinarith [hstep, mul_le_mul_of_nonneg_right hL hnn]
    have htarget : c1 ≤ (1 - edgeProb n) ^ (2 * kimM n k)
        * ((gammaBetween s.Γ T T).card : ℝ) - lam1 := by linarith
    refine le_trans (bernoulliPr_mono hp0 hp1 ?_)
      (le_trans (lowSurvivorCount_lower_tail s (kimM n k) hp0 hp1 T hthr hM
        ht1 htarget) ?_)
    · intro σ hσ
      obtain ⟨-, hlt⟩ := Finset.mem_filter.mp hσ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_lt hlt⟩
    · refine le_trans (Real.exp_le_exp.mpr ?_) hq1
      have hG : ((gammaBetween s.Γ T T).card : ℝ) ≤ GG := hGG T hT
      have hnn : (0 : ℝ) ≤ t1 ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
          * ((2 * thr) * (2 * (kimM n k : ℝ)) * Real.exp (t1 * (2 * thr)))) := by
        have hpp : (0 : ℝ) ≤ edgeProb n * (1 - edgeProb n) :=
          mul_nonneg hp0 (by linarith)
        have : (0 : ℝ) ≤ 2 * thr := by linarith
        positivity
      nlinarith [hG, hnn]
  · -- (38)
    intro T hT
    have hG : ((gammaBetween s.Γ T T).card : ℝ) ≤ GG := hGG T hT
    have hvar : t3 ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
        * (((gammaBetween s.Γ T T).card : ℝ) * Real.exp t3))
        ≤ t3 * lam3 / 2 := by
      refine le_trans ?_ hvar3
      have hpp : (0 : ℝ) ≤ edgeProb n * (1 - edgeProb n) :=
        mul_nonneg hp0 (by linarith)
      have hcoef : (0 : ℝ) ≤ t3 ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
        * Real.exp t3) := by positivity
      nlinarith [hG, hcoef]
    refine le_trans (bernoulliPr_mono hp0 hp1 ?_)
      (le_trans (card_sample_inter_gammaT_tail s (kimM n k) hp0 hp1 T ht3 hvar)
        hq3)
    intro σ hσ
    obtain ⟨-, hlt⟩ := Finset.mem_filter.mp hσ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hpG : edgeProb n * ((gammaBetween s.Γ T T).card : ℝ)
        ≤ edgeProb n * GG := mul_le_mul_of_nonneg_left hG hp0
    linarith


set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **Property 8 propagates.** Kim §4.9: each `t`-set survives with probability
at most `B`, and Markov with a factor `n` turns `E[|𝒯'|] ≤ |𝒯|·B` into the
population bound. -/
theorem property8_numeric (k : ℕ) (s : BlockState V)
    (hn : 0 < n) (hlogn : 1 ≤ Real.log n)
    (h4 : Property4 s k)
    {Dc : ℕ} (hDc : ∀ (x y : V) (hxy : x ≠ y), mkEdge hxy ∈ s.Γ →
      (commonNbrs s.Γ x y).card ≤ Dc)
    (l : ℕ) {ρ : ℝ} (hρ : ρ < 0) {B : ℝ} (hB0 : 0 < B)
    (hbin : ∀ T ∈ calT s,
      ((1 - edgeProb n) + edgeProb n * Real.exp ρ)
          ^ (gammaBetween s.Γ T T).card
        / Real.exp (ρ * (3 * l)) ≤ B / 2)
    (hfam : ∀ T ∈ calT s,
      (((gammaBetween s.Γ T T).card : ℝ)
        * (2 * (kimM n k : ℝ) * edgeProb n ^ 2
          + (Dc : ℝ) * edgeProb n ^ 3)) ^ l
        / (l.factorial : ℝ) ≤ B / 2)
    (htarget : (n : ℝ) * (((calT s).card : ℝ) * B)
      ≤ (n : ℝ) ^ (k + 1) * (Nat.choose (Fintype.card V) (tParam n))
        * Real.exp (-(1 - kimEps n)
            * ∑ j ∈ Finset.range (k + 1),
                bSeq n j * μSeq n j * theta n / Real.sqrt n
                  * ((tParam n).choose 2))) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property8 (blockStepP s (kimM n k) σ) (k + 1))) ≤ 1 / n := by
  classical
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  refine property8_prob k s (kimM n k) hp0 hp1 hn hB0 ?_ htarget
  intro T hT
  have hW := sum_hitFams_le s T hp0 hp1
    (lambdaAt_card_le_kimM k s h4) hDc
  refine le_trans (calT_mem_prob_le s (kimM n k) hp0 hp1 T l hρ hW) ?_
  linarith [hbin T hT, hfam T hT]

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **Property 5 propagates.** Kim §4.6: `(28)`, `(29)`, and Corollary 3.2 at
`ρ = n^{−5/8}`.

`I` is Kim's overlap allowance `4·3k log n`: the two edges `e_uv, e_uw` share at
most that many `Λ*`-coordinates, so their joint survival probability is at most
`(1−p)^{4M−I}`, which costs the factor `(1−p)^{−3k log n} ≤ 1 + 2Ip`. -/
theorem property5_numeric (k : ℕ) (s : BlockState V)
    (hn : 0 < n) (hlogn : 1 ≤ Real.log n) (hθsmall : theta n ≤ 1 / 100)
    (h3 : Property3 s k) (h4 : Property4 s k) (h5 : Property5 s k)
    (hslack : 2 * edgeProb n ≤ 3 * bSeq n k * theta n ^ 2)
    (hbb2 : bSeq n k ≤ 2 * bSeq n (k + 1))
    {I : ℕ} (hI : 4 * (3 * (k : ℝ) * Real.log n + 1) ≤ (I : ℝ))
    (hI4M : I ≤ 4 * kimM n k)
    (hIp2 : 2 * (I : ℝ) * edgeProb n ≤ 1)
    (hIp : 2 * (I : ℝ) * edgeProb n * bSeq n (k + 1) ^ 2
      ≤ 2 * bSeq n k ^ 3 * theta n ^ 2)
    {t : ℝ} (ht : 0 ≤ t)
    (hexp : ∀ (v w : V) (h : v ≠ w), mkEdge h ∈ s.Γ →
      Real.exp (-t * (bSeq n k ^ 3 * theta n ^ 2 * n)
        + t ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
          * (((2 * (kimM n k : ℝ) + 4)
              * (4 * (kimM n k : ℝ) * (commonNbrs s.Γ v w).card))
            * Real.exp (t * (2 * (kimM n k : ℝ) + 4)))))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property5 (blockStepP s (kimM n k) σ) (k + 1))) ≤ 1 / n := by
  classical
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  have hb : 0 < bSeq n k := bSeq_pos n k
  have hb' : 0 < bSeq n (k + 1) := bSeq_pos n (k + 1)
  have hble : bSeq n k ≤ 1 := bSeq_le_one n k
  have hθ0 : 0 ≤ theta n := theta_nonneg n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hMlam : ∀ g ∈ s.Γ, ∀ x ∈ edgeVerts g, (lambdaAt s g x).card ≤ kimM n k :=
    lambdaAt_card_le_kimM k s h4
  -- Kim's (13): the one-step survival bound
  set err : ℝ := 2 * edgeProb n with herrdef
  have herr : 0 ≤ err := by rw [herrdef]; linarith
  set q : ℝ := 1 - 2 * aSeq n k * bSeq n k * theta n
    - 9 * bSeq n k * theta n ^ 2 + err with hqdef
  have hslack' : bSeq n k * err ≤ 3 * bSeq n k ^ 2 * theta n ^ 2 := by
    calc bSeq n k * err ≤ bSeq n k * (3 * bSeq n k * theta n ^ 2) :=
          mul_le_mul_of_nonneg_left hslack hb.le
      _ = 3 * bSeq n k ^ 2 * theta n ^ 2 := by ring
  have h41 := lemma41_bounds (N := n) k hθsmall hp0 hp1 (2 * kimM n k) herr
    (two_kimM_mul_edgeProb_le k hn) (two_kimM_mul_edgeProb_ge k hn)
  have hq0 : 0 ≤ q :=
    le_trans (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - edgeProb n) _) h41.2
  have hsurv := bSeq_mul_surv_le n k herr hslack' (le_refl q)
  have hqpow : (1 - edgeProb n) ^ (4 * kimM n k) ≤ q ^ 2 := by
    have h4m : 4 * kimM n k = 2 * kimM n k * 2 := by ring
    rw [h4m, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg (by linarith) _) h41.2 2
  -- the key algebraic step of (29)
  have hθsq : theta n ^ 2 ≤ 1 / 10000 := by nlinarith [hθsmall, hθ0]
  have hbsq : bSeq n k ^ 2 ≤ bSeq n k := by nlinarith [hble, hb.le]
  have h5b : 5 * bSeq n k ^ 2 * theta n ^ 2 ≤ bSeq n k / 2 := by
    have h1 : 5 * bSeq n k ^ 2 * theta n ^ 2 ≤ 5 * bSeq n k * theta n ^ 2 := by
      nlinarith [hbsq, sq_nonneg (theta n)]
    have h2 : 5 * bSeq n k * theta n ^ 2 ≤ 5 * bSeq n k * (1 / 10000) := by
      nlinarith [hθsq, hb.le]
    linarith
  have hA0 : 0 ≤ bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2 := by
    linarith [hbb2, h5b]
  have hkey : (1 + 2 * (I : ℝ) * edgeProb n)
        * (bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2) ^ 2
      ≤ bSeq n (k + 1) ^ 2 - bSeq n k ^ 3 * theta n ^ 2 := by
    have hAle : bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2
        ≤ bSeq n (k + 1) := by nlinarith [hb.le, hθ0]
    have hAsq : (bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2) ^ 2
        ≤ bSeq n (k + 1) ^ 2 := pow_le_pow_left₀ hA0 hAle 2
    have hE0 : (0 : ℝ) ≤ 2 * (I : ℝ) * edgeProb n :=
      mul_nonneg (by positivity) hp0
    have hEA : 2 * (I : ℝ) * edgeProb n
          * (bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2) ^ 2
        ≤ 2 * bSeq n k ^ 3 * theta n ^ 2 :=
      le_trans (mul_le_mul_of_nonneg_left hAsq hE0) hIp
    have h25 : 25 * bSeq n k ^ 4 * theta n ^ 4
        ≤ bSeq n k ^ 3 * theta n ^ 2 := by
      have hfac : bSeq n k ^ 4 * theta n ^ 4
          = bSeq n k ^ 3 * theta n ^ 2 * (bSeq n k * theta n ^ 2) := by ring
      have hbase : (0 : ℝ) ≤ bSeq n k ^ 3 * theta n ^ 2 := by positivity
      have hsmall : 25 * (bSeq n k * theta n ^ 2) ≤ 1 := by
        nlinarith [hble, hθsq, hb.le, hθ0]
      nlinarith [hbase, hsmall, hfac]
    have h10 : 5 * bSeq n k ^ 3 * theta n ^ 2
        ≤ 10 * bSeq n (k + 1) * bSeq n k ^ 2 * theta n ^ 2 := by
      have hfac : (0 : ℝ) ≤ bSeq n k ^ 2 * theta n ^ 2 := by positivity
      nlinarith [hbb2, hfac]
    have hbt : (0 : ℝ) ≤ bSeq n k ^ 3 * theta n ^ 2 := by positivity
    have hsplit : (1 + 2 * (I : ℝ) * edgeProb n)
          * (bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2) ^ 2
        = (bSeq n (k + 1) ^ 2
            - 10 * bSeq n (k + 1) * bSeq n k ^ 2 * theta n ^ 2
            + 25 * bSeq n k ^ 4 * theta n ^ 4)
          + 2 * (I : ℝ) * edgeProb n
            * (bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2) ^ 2 := by
      ring
    rw [hsplit]
    linarith [hEA, h25, h10, hbt]
  refine property5_prob k s (kimM n k) hp0 hp1 hn ?_
  intro v w hvw hmem
  have hC1 : (1 : ℝ) ≤ 3 * (k : ℝ) * Real.log n + 1 := by
    have hnn : (0 : ℝ) ≤ 3 * (k : ℝ) * Real.log n := by positivity
    linarith
  have hbd : ∀ x y : V, x ≠ y →
      ((commonNbrs s.E x y).card : ℝ) ≤ 3 * (k : ℝ) * Real.log n + 1 := by
    intro x y hxy
    have h := h3 x y hxy
    linarith
  have hU : ∀ u ∈ commonNbrs s.Γ v w,
      4 * kimM n k - I
        ≤ ((pairEdges v w u).biUnion (lambdaStar s (kimM n k))).card :=
    fun u hu =>
      card_biUnion_pairEdges_ge s (kimM n k) v w hvw hC1 hbd hMlam u hu hI
  have hcodeg : ((commonNbrs s.Γ v w).card : ℝ) ≤ bSeq n k ^ 2 * n := by
    have h := h5 v w hvw hmem
    rwa [codegEdges] at h
  have hpownn : (0 : ℝ) ≤ (1 - edgeProb n) ^ (4 * kimM n k - I) :=
    pow_nonneg (by linarith) _
  have hbn : (0 : ℝ) ≤ bSeq n k ^ 2 * n := by positivity
  have hE0 : (0 : ℝ) ≤ 1 + 2 * (I : ℝ) * edgeProb n := by
    have : (0 : ℝ) ≤ 2 * (I : ℝ) * edgeProb n :=
      mul_nonneg (by positivity) hp0
    linarith
  have hqb : q ^ 2 * bSeq n k ^ 2
      ≤ (bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2) ^ 2 := by
    have h2 : 0 ≤ bSeq n k * q := mul_nonneg hb.le hq0
    have hsq : q ^ 2 * bSeq n k ^ 2 = (bSeq n k * q) ^ 2 := by ring
    rw [hsq]
    exact pow_le_pow_left₀ h2 hsurv 2
  have hpow := pow_sub_le_pow_mul (p := edgeProb n) hp0 hp1 hI4M hIp2
  have hmean : (1 - edgeProb n) ^ (4 * kimM n k - I)
        * ((commonNbrs s.Γ v w).card : ℝ)
      ≤ bSeq n (k + 1) ^ 2 * n - bSeq n k ^ 3 * theta n ^ 2 * n := by
    calc (1 - edgeProb n) ^ (4 * kimM n k - I)
            * ((commonNbrs s.Γ v w).card : ℝ)
        ≤ (1 - edgeProb n) ^ (4 * kimM n k - I) * (bSeq n k ^ 2 * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hcodeg hpownn
      _ ≤ ((1 - edgeProb n) ^ (4 * kimM n k)
            * (1 + 2 * (I : ℝ) * edgeProb n)) * (bSeq n k ^ 2 * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hpow hbn
      _ ≤ (q ^ 2 * (1 + 2 * (I : ℝ) * edgeProb n))
            * (bSeq n k ^ 2 * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hqpow hE0) hbn
      _ = (1 + 2 * (I : ℝ) * edgeProb n) * (q ^ 2 * bSeq n k ^ 2) * (n : ℝ) := by
          ring
      _ ≤ (1 + 2 * (I : ℝ) * edgeProb n)
            * (bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2) ^ 2
            * (n : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqb hE0) hn0
      _ ≤ (bSeq n (k + 1) ^ 2 - bSeq n k ^ 3 * theta n ^ 2) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hkey hn0
      _ = bSeq n (k + 1) ^ 2 * n - bSeq n k ^ 3 * theta n ^ 2 * n := by ring
  have hCbound : ∀ j : Fin (Fintype.card (Coord V (kimM n k))),
      (((commonNbrs s.Γ v w).filter (fun u =>
        j ∈ ((pairEdges v w u).biUnion (lambdaStar s (kimM n k))).image
          (coordEquiv V (kimM n k)))).card : ℝ)
        ≤ 2 * (kimM n k : ℝ) + 4 :=
    fun j => card_filter_pairEdges_le s (kimM n k) v w hMlam j
  have hQbound : ∑ j : Fin (Fintype.card (Coord V (kimM n k))),
      (((commonNbrs s.Γ v w).filter (fun u =>
        j ∈ ((pairEdges v w u).biUnion (lambdaStar s (kimM n k))).image
          (coordEquiv V (kimM n k)))).card : ℝ) ^ 2
      ≤ (2 * (kimM n k : ℝ) + 4)
        * (4 * (kimM n k : ℝ) * (commonNbrs s.Γ v w).card) := by
    refine le_trans (sum_sq_le_max_mul_sum Finset.univ _
      (fun j _ => hCbound j) (fun j _ => Nat.cast_nonneg _)) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hnat := sum_card_filter_pairEdges_le s (kimM n k) v w hMlam
    calc ∑ j : Fin (Fintype.card (Coord V (kimM n k))),
          (((commonNbrs s.Γ v w).filter (fun u =>
            j ∈ ((pairEdges v w u).biUnion (lambdaStar s (kimM n k))).image
              (coordEquiv V (kimM n k)))).card : ℝ)
        = ((∑ j : Fin (Fintype.card (Coord V (kimM n k))),
            ((commonNbrs s.Γ v w).filter (fun u =>
              j ∈ ((pairEdges v w u).biUnion (lambdaStar s (kimM n k))).image
                (coordEquiv V (kimM n k)))).card : ℕ) : ℝ) := by
          push_cast; ring
      _ ≤ ((4 * kimM n k * (commonNbrs s.Γ v w).card : ℕ) : ℝ) := by
          exact_mod_cast hnat
      _ = 4 * (kimM n k : ℝ) * (commonNbrs s.Γ v w).card := by push_cast; ring
  exact le_trans (property5_tail k s (kimM n k) hp0 hp1 v w hU hmean
    (by positivity) (by positivity) hCbound hQbound ht) (hexp v w hvw hmem)

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **Property 6 propagates.** Kim §4.7: (32), (33)–(36), and Corollary 3.2 at
`ρ = n^{−1/4−1/68}`, with the truncation threshold `thr` of (30) and the
`L⁽¹⁾`-defect bound `D` of (34)/(35) supplied numerically. -/
theorem property6_numeric (k : ℕ) (s : BlockState V)
    (hn : 0 < n) (hlogn : 1 ≤ Real.log n) (hθsmall : theta n ≤ 1 / 100)
    (h3 : Property3 s k) (h4 : Property4 s k) (h6 : Property6 s k)
    (hslack : 2 * edgeProb n ≤ 3 * bSeq n k * theta n ^ 2)
    (hbb2 : bSeq n k ≤ 2 * bSeq n (k + 1))
    (hcut : 1 ≤ mcut n)
    (hβ1 : 1 ≤ Real.sqrt (3 * ((k : ℝ) + 1) * Real.log n))
    (hβcut : 2 * Real.sqrt (3 * ((k : ℝ) + 1) * Real.log n)
      ≤ Real.sqrt ((mcut n : ℝ)))
    (thr : ℝ) (hthr1 : 1 ≤ thr)
    (hthrge : 2 * Real.sqrt (3 * ((k : ℝ) + 1) * Real.log n)
      * Real.sqrt (2 * (mcut n : ℝ)) ≤ thr)
    {D : ℕ}
    (hD : Real.sqrt (2 * (mcut n : ℝ))
      / Real.sqrt (3 * ((k : ℝ) + 1) * Real.log n) ≤ (D : ℝ))
    (hD2M : 2 * D ≤ 2 * kimM n k)
    (hDp2 : 4 * (D : ℝ) * edgeProb n ≤ 1)
    (hDp : 4 * (D : ℝ) * edgeProb n ≤ 4 * bSeq n k ^ 2 * theta n ^ 2)
    {t : ℝ} (ht : 0 ≤ t) {q1 : ℝ} (hq1 : 0 ≤ q1)
    (hexp : ∀ A B : Finset V, Disjoint A B →
      A.card = mcut n → B.card = mcut n →
      Real.exp (-t * (bSeq n k ^ 2 * theta n ^ 2 * (mcut n : ℝ) * (mcut n : ℝ))
        + t ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
          * ((2 * thr) * (2 * (kimM n k : ℝ) * (gammaBetween s.Γ A B).card)
            * Real.exp (t * (2 * thr))))) ≤ q1) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property6 (blockStepP s (kimM n k) σ) (k + 1)))
      ≤ ((n : ℕ).choose (mcut n) : ℝ) * ((n : ℕ).choose (mcut n) : ℝ) * q1 := by
  classical
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  have hb := bSeq_pos n k
  have hb' := bSeq_pos n (k + 1)
  have hble := bSeq_le_one n k
  have hb'le := bSeq_le_one n (k + 1)
  have hθ0 := theta_nonneg n
  have hcutR : (1 : ℝ) ≤ (mcut n : ℝ) := by exact_mod_cast hcut
  have hβ0 : (0 : ℝ) < Real.sqrt (3 * ((k : ℝ) + 1) * Real.log n) := by
    linarith
  -- Kim's (13)
  set err : ℝ := 2 * edgeProb n with herrdef
  have herr : 0 ≤ err := by rw [herrdef]; linarith
  set q : ℝ := 1 - 2 * aSeq n k * bSeq n k * theta n
    - 9 * bSeq n k * theta n ^ 2 + err with hqdef
  have hslack' : bSeq n k * err ≤ 3 * bSeq n k ^ 2 * theta n ^ 2 := by
    calc bSeq n k * err ≤ bSeq n k * (3 * bSeq n k * theta n ^ 2) :=
          mul_le_mul_of_nonneg_left hslack hb.le
      _ = 3 * bSeq n k ^ 2 * theta n ^ 2 := by ring
  have h41 := lemma41_bounds (N := n) k hθsmall hp0 hp1 (2 * kimM n k) herr
    (two_kimM_mul_edgeProb_le k hn) (two_kimM_mul_edgeProb_ge k hn)
  have hq0 : 0 ≤ q :=
    le_trans (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - edgeProb n) _) h41.2
  have hsurv := bSeq_mul_surv_le n k herr hslack' (le_refl q)
  have hθsq : theta n ^ 2 ≤ 1 / 10000 := by nlinarith [hθsmall, hθ0]
  have hbsq : bSeq n k ^ 2 ≤ bSeq n k := by nlinarith [hble, hb.le]
  have h5b : 5 * bSeq n k ^ 2 * theta n ^ 2 ≤ bSeq n k / 2 := by
    have h1 : 5 * bSeq n k ^ 2 * theta n ^ 2 ≤ 5 * bSeq n k * theta n ^ 2 := by
      nlinarith [hbsq, sq_nonneg (theta n)]
    have h2 : 5 * bSeq n k * theta n ^ 2 ≤ 5 * bSeq n k * (1 / 10000) := by
      nlinarith [hθsq, hb.le]
    linarith
  have hA0 : 0 ≤ bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2 := by
    linarith [hbb2, h5b]
  have hA1 : bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2 ≤ 1 := by
    have hnn : (0 : ℝ) ≤ bSeq n k ^ 2 * theta n ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith [hb'le, hnn]
  refine property6_prob k s (kimM n k) hp0 hp1 thr hcut hq1 ?_
  intro A B hABdisj hAcard hBcard
  have hMlam : ∀ e ∈ gammaBetween s.Γ A B, ∀ v ∈ edgeVerts e,
      (lambdaAt s e v).card ≤ kimM n k := by
    intro e he v hv
    exact lambdaAt_card_le_kimM k s h4 e (mem_gammaBetween.mp he).1 v hv
  have hmcutAB : mcut n ≤ (A ∪ B).card := by
    rw [← hAcard]; exact Finset.card_le_card Finset.subset_union_left
  have hABpos : 0 < (A ∪ B).card := by omega
  have hABge : (mcut n : ℝ) ≤ ((A ∪ B).card : ℝ) := by exact_mod_cast hmcutAB
  have hABle : ((A ∪ B).card : ℝ) ≤ 2 * (mcut n : ℝ) := by
    have hcu := Finset.card_union_le A B
    rw [hAcard, hBcard] at hcu
    have hcast : ((A ∪ B).card : ℝ) ≤ ((mcut n + mcut n : ℕ) : ℝ) := by
      exact_mod_cast hcu
    push_cast at hcast; linarith
  have hβB : Real.sqrt (3 * ((k : ℝ) + 1) * Real.log n)
      ≤ Real.sqrt (((A ∪ B).card : ℝ)) / 2 := by
    have hs : Real.sqrt ((mcut n : ℝ)) ≤ Real.sqrt (((A ∪ B).card : ℝ)) :=
      Real.sqrt_le_sqrt hABge
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    linarith [hβcut, hs]
  have hsAB : Real.sqrt (((A ∪ B).card : ℝ))
      ≤ Real.sqrt (2 * (mcut n : ℝ)) := Real.sqrt_le_sqrt hABle
  have hthrle : 2 * Real.sqrt (3 * ((k : ℝ) + 1) * Real.log n) * 1
      * Real.sqrt (((A ∪ B).card : ℝ)) ≤ thr := by
    refine le_trans ?_ hthrge
    rw [mul_one]
    exact mul_le_mul_of_nonneg_left hsAB (by linarith)
  have hβsq : Real.sqrt (3 * ((k : ℝ) + 1) * Real.log n) ^ 2
      = 3 * ((k : ℝ) + 1) * Real.log n := Real.sq_sqrt (by positivity)
  have h3' : ∀ u u' : V, u ≠ u' →
      ((commonNbrs s.E u u').card : ℝ)
        ≤ Real.sqrt (3 * ((k : ℝ) + 1) * Real.log n) ^ 2 := by
    intro u u' huu'
    rw [hβsq]
    have hcn := h3 u u' huu'
    nlinarith [hcn, hlogn]
  have hDbound : ∀ e ∈ gammaBetween s.Γ A B, ∀ v ∈ edgeVerts e,
      ((lambdaAt s e v).filter
        (fun g => ¬ IsLowPair s A B thr g v)).card ≤ D := by
    intro e _he v hv
    have hcn := card_notLow_le s A B e v hβ1 (le_refl 1) hβB hABpos hthrle h3'
    have hle : (((lambdaAt s e v).filter
        (fun g => ¬ IsLowPair s A B thr g v)).card : ℝ) ≤ (D : ℝ) := by
      refine le_trans hcn ?_
      rw [mul_one]
      refine le_trans ?_ hD
      gcongr
    exact_mod_cast hle
  have hΓcard : ((gammaBetween s.Γ A B).card : ℝ)
      ≤ bSeq n k * (mcut n : ℝ) * (mcut n : ℝ) := by
    have hg := h6 A B hABdisj (le_of_eq hAcard.symm) (le_of_eq hBcard.symm)
    rw [hAcard, hBcard] at hg
    exact hg
  have hpow : (1 - edgeProb n) ^ (2 * kimM n k - 2 * D)
      ≤ (1 - edgeProb n) ^ (2 * kimM n k)
        * (1 + 4 * (D : ℝ) * edgeProb n) := by
    have hcast : 2 * ((2 * D : ℕ) : ℝ) * edgeProb n ≤ 1 := by
      push_cast; linarith [hDp2]
    have hh := pow_sub_le_pow_mul (p := edgeProb n) hp0 hp1 hD2M hcast
    have heq : (1 - edgeProb n) ^ (2 * kimM n k)
          * (1 + 2 * ((2 * D : ℕ) : ℝ) * edgeProb n)
        = (1 - edgeProb n) ^ (2 * kimM n k)
          * (1 + 4 * (D : ℝ) * edgeProb n) := by push_cast; ring
    rw [heq] at hh; exact hh
  have hmcut2 : (0 : ℝ) ≤ (mcut n : ℝ) * (mcut n : ℝ) := by positivity
  have hmean : (1 - edgeProb n) ^ (2 * kimM n k - 2 * D)
        * ((gammaBetween s.Γ A B).card : ℝ)
      ≤ bSeq n (k + 1) * (mcut n : ℝ) * (mcut n : ℝ)
        - bSeq n k ^ 2 * theta n ^ 2 * (mcut n : ℝ) * (mcut n : ℝ) := by
    have hpownn : (0 : ℝ) ≤ (1 - edgeProb n) ^ (2 * kimM n k - 2 * D) :=
      pow_nonneg (by linarith) _
    have hE0 : (0 : ℝ) ≤ 1 + 4 * (D : ℝ) * edgeProb n := by
      have hnn : (0 : ℝ) ≤ 4 * (D : ℝ) * edgeProb n :=
        mul_nonneg (by positivity) hp0
      linarith
    have hkey : (1 + 4 * (D : ℝ) * edgeProb n) * (q * bSeq n k)
        ≤ bSeq n (k + 1) - bSeq n k ^ 2 * theta n ^ 2 := by
      have hqb : q * bSeq n k
          ≤ bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2 := by
        rw [mul_comm]; exact hsurv
      have hstep : (1 + 4 * (D : ℝ) * edgeProb n) * (q * bSeq n k)
          ≤ (1 + 4 * (D : ℝ) * edgeProb n)
            * (bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2) :=
        mul_le_mul_of_nonneg_left hqb hE0
      have hDpnn : (0 : ℝ) ≤ 4 * (D : ℝ) * edgeProb n :=
        mul_nonneg (by positivity) hp0
      have hE : 4 * (D : ℝ) * edgeProb n
            * (bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2)
          ≤ 4 * bSeq n k ^ 2 * theta n ^ 2 := by
        calc 4 * (D : ℝ) * edgeProb n
              * (bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2)
            ≤ 4 * (D : ℝ) * edgeProb n * 1 :=
              mul_le_mul_of_nonneg_left hA1 hDpnn
          _ = 4 * (D : ℝ) * edgeProb n := by ring
          _ ≤ 4 * bSeq n k ^ 2 * theta n ^ 2 := hDp
      have hexpand : (1 + 4 * (D : ℝ) * edgeProb n)
            * (bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2)
          = (bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2)
            + 4 * (D : ℝ) * edgeProb n
              * (bSeq n (k + 1) - 5 * bSeq n k ^ 2 * theta n ^ 2) := by ring
      linarith [hstep, hE, hexpand]
    calc (1 - edgeProb n) ^ (2 * kimM n k - 2 * D)
            * ((gammaBetween s.Γ A B).card : ℝ)
        ≤ (1 - edgeProb n) ^ (2 * kimM n k - 2 * D)
            * (bSeq n k * (mcut n : ℝ) * (mcut n : ℝ)) :=
          mul_le_mul_of_nonneg_left hΓcard hpownn
      _ ≤ ((1 - edgeProb n) ^ (2 * kimM n k)
            * (1 + 4 * (D : ℝ) * edgeProb n))
            * (bSeq n k * (mcut n : ℝ) * (mcut n : ℝ)) := by
          refine mul_le_mul_of_nonneg_right hpow ?_
          have := hb.le; positivity
      _ ≤ (q * (1 + 4 * (D : ℝ) * edgeProb n))
            * (bSeq n k * (mcut n : ℝ) * (mcut n : ℝ)) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h41.2 hE0) ?_
          have := hb.le; positivity
      _ = ((1 + 4 * (D : ℝ) * edgeProb n) * (q * bSeq n k))
            * ((mcut n : ℝ) * (mcut n : ℝ)) := by ring
      _ ≤ (bSeq n (k + 1) - bSeq n k ^ 2 * theta n ^ 2)
            * ((mcut n : ℝ) * (mcut n : ℝ)) :=
          mul_le_mul_of_nonneg_right hkey hmcut2
      _ = bSeq n (k + 1) * (mcut n : ℝ) * (mcut n : ℝ)
            - bSeq n k ^ 2 * theta n ^ 2 * (mcut n : ℝ) * (mcut n : ℝ) := by
          ring
  exact le_trans (property6_tail s (kimM n k) A B hthr1 hp0 hp1 hMlam hDbound
    ht hmean) (hexp A B hABdisj hAcard hBcard)

open scoped Classical in
/-- **Property 2 propagates**, with the padding budget, the floor error and the
survival slack all discharged.

`M := ⌊b(a+5θ)√n⌋` is validated by Property 4; the floor costs at most `2p`,
absorbed by the slack condition `2p ≤ 3bθ²`. What remains is Kim's exponent
estimate at `ρ = n^{−3/4}`. -/
theorem property2_numeric (k : ℕ) (s : BlockState V)
    (hn : 0 < n) (hlogn : 1 ≤ Real.log n) (hθsmall : theta n ≤ 1 / 100)
    (h2 : Property2 s k) (h4 : Property4 s k)
    (hslack : 2 * edgeProb n ≤ 3 * bSeq n k * theta n ^ 2)
    {t : ℝ} (ht : 0 ≤ t)
    (hexp : ∀ v : V, Real.exp (-t * (bSeq n k ^ 2 * theta n ^ 2 * n)
        + t ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
          * ((2 * kimM n k : ℝ)
            * (2 * kimM n k * (edgesAt s.Γ v).card)
            * Real.exp (t * (2 * kimM n k)))))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property2 (blockStepP s (kimM n k) σ) (k + 1)))
      ≤ ((n : ℝ) ^ (2 : ℕ))⁻¹ := by
  classical
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  have hb := bSeq_pos n k
  refine property2_prob k s (kimM n k) hp0 hp1 h2 hn hθsmall
    (lambdaAt_card_le_kimM k s h4)
    (by positivity : (0 : ℝ) ≤ 2 * edgeProb n)
    (two_kimM_mul_edgeProb_le k hn) (two_kimM_mul_edgeProb_ge k hn) ?_ ht hexp
  -- the slack condition, scaled by `b`
  calc bSeq n k * (2 * edgeProb n)
      ≤ bSeq n k * (3 * bSeq n k * theta n ^ 2) :=
        mul_le_mul_of_nonneg_left hslack hb.le
    _ = 3 * bSeq n k ^ 2 * theta n ^ 2 := by ring

open scoped Classical in
/-- **The combination step of Kim's Main Lemma 2.1.**

Kim verifies each of the eight properties separately and concludes
`Pr((ℰ',Γ',G') satisfies Properties 1–8) > 0` by a union bound over the eight
failure events. This lemma is that union bound: given per-property failure
bounds summing to less than one, some sample makes all eight hold
simultaneously. -/
theorem main_lemma_of_bad_bounds (k : ℕ) (s : BlockState V) (M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {q1 q2 q3 q4 q5 q6 q7 q8 : ℝ}
    (hb1 : bernoulliPr p (Finset.univ.filter
      (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ¬ Property1 (blockStepP s M σ) (k + 1))) ≤ q1)
    (hb2 : bernoulliPr p (Finset.univ.filter
      (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ¬ Property2 (blockStepP s M σ) (k + 1))) ≤ q2)
    (hb3 : bernoulliPr p (Finset.univ.filter
      (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ¬ Property3 (blockStepP s M σ) (k + 1))) ≤ q3)
    (hb4 : bernoulliPr p (Finset.univ.filter
      (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ¬ Property4 (blockStepP s M σ) (k + 1))) ≤ q4)
    (hb5 : bernoulliPr p (Finset.univ.filter
      (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ¬ Property5 (blockStepP s M σ) (k + 1))) ≤ q5)
    (hb6 : bernoulliPr p (Finset.univ.filter
      (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ¬ Property6 (blockStepP s M σ) (k + 1))) ≤ q6)
    (hb7 : bernoulliPr p (Finset.univ.filter
      (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ¬ Property7 (blockStepP s M σ) (k + 1))) ≤ q7)
    (hb8 : bernoulliPr p (Finset.univ.filter
      (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        ¬ Property8 (blockStepP s M σ) (k + 1))) ≤ q8)
    (hsum : q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 < 1) :
    ∃ σ : Fin (Fintype.card (Coord V M)) → Bool,
      Properties1to8 (blockStepP s M σ) (k + 1) := by
  classical
  set B1 := Finset.univ.filter
    (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
      ¬ Property1 (blockStepP s M σ) (k + 1)) with hB1
  set B2 := Finset.univ.filter
    (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
      ¬ Property2 (blockStepP s M σ) (k + 1)) with hB2
  set B3 := Finset.univ.filter
    (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
      ¬ Property3 (blockStepP s M σ) (k + 1)) with hB3
  set B4 := Finset.univ.filter
    (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
      ¬ Property4 (blockStepP s M σ) (k + 1)) with hB4
  set B5 := Finset.univ.filter
    (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
      ¬ Property5 (blockStepP s M σ) (k + 1)) with hB5
  set B6 := Finset.univ.filter
    (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
      ¬ Property6 (blockStepP s M σ) (k + 1)) with hB6
  set B7 := Finset.univ.filter
    (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
      ¬ Property7 (blockStepP s M σ) (k + 1)) with hB7
  set B8 := Finset.univ.filter
    (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
      ¬ Property8 (blockStepP s M σ) (k + 1)) with hB8
  set U := B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6 ∪ B7 ∪ B8 with hU
  have hUle : bernoulliPr p U ≤ q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 := by
    have u1 := bernoulliPr_union_le hp0 hp1 B1 B2
    have u2 := bernoulliPr_union_le hp0 hp1 (B1 ∪ B2) B3
    have u3 := bernoulliPr_union_le hp0 hp1 (B1 ∪ B2 ∪ B3) B4
    have u4 := bernoulliPr_union_le hp0 hp1 (B1 ∪ B2 ∪ B3 ∪ B4) B5
    have u5 := bernoulliPr_union_le hp0 hp1 (B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5) B6
    have u6 := bernoulliPr_union_le hp0 hp1 (B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6) B7
    have u7 := bernoulliPr_union_le hp0 hp1
      (B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6 ∪ B7) B8
    rw [hU]
    linarith
  -- the eight bad events do not cover everything
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin (Fintype.card (Coord V M)) → Bool, σ ∉ U := by
    by_contra hc
    push_neg at hc
    rw [Finset.eq_univ_of_forall hc, bernoulliPr_univ] at hUle
    linarith
  rw [hU] at hσ
  simp only [Finset.mem_union, not_or] at hσ
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hσ
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hc; exact h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  · by_contra hc; exact h2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  · by_contra hc; exact h3 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  · by_contra hc; exact h4 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  · by_contra hc; exact h5 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  · by_contra hc; exact h6 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  · by_contra hc; exact h7 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  · by_contra hc; exact h8 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)


/-- The twelve asymptotic estimates of §§4.4–4.9, bundled. Each conjunct is
exactly the corresponding `eventually_property*` lemma above; `KimAsym` lets
`KimLarge` carry them all through one projection. -/
def KimAsym (N : ℕ) : Prop :=
  (3 * Real.log N + Real.exp 1 / 2
      ≤ Real.exp (((1 : ℝ) / 4 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2) / (Real.log N) ^ 4)
  ∧ (2 * Real.log N
      ≤ Real.exp (((1 : ℝ) / 4 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2) / (Real.log N) ^ 6)
  ∧ (20 * (Real.log N) ^ 8
      ≤ Real.exp (((1 : ℝ) / 4 - 3 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2))
  ∧ (2 * Real.log N
      ≤ Real.exp (((1 : ℝ) / 2 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2) / (Real.log N) ^ 10)
  ∧ (6 * Real.log N
      ≤ Real.exp (((3 : ℝ) / 8 - 3 * kimDelta) * Real.log N
          - 6 * Real.sqrt (Real.log N) - 3) / (Real.log N) ^ 4)
  ∧ (108 * (Real.log N) ^ 3 ≤ (N : ℝ) ^ ((1 : ℝ) / 68))
  ∧ (11 * (Real.log N) ^ 5
      ≤ Real.exp (((1 : ℝ) / 4 - kimDelta) * Real.log N
          - 2 * Real.sqrt (Real.log N) - 1))
  ∧ (960 * (Real.log N) ^ 6
      ≤ Real.exp (((1 : ℝ) / 6 - kimDelta) * Real.log N))
  ∧ (12 * (Real.log N) ^ 5
      ≤ Real.exp (((1 : ℝ) / 4 - 1 / 17 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2))
  ∧ (3072 * (Real.log N) ^ 6
      ≤ Real.exp (((1 : ℝ) / 17 - kimDelta / 2) * Real.log N
          - 2 * Real.sqrt (Real.log N) - 1))
  ∧ (1000000 * (Real.log N) ^ 8
      ≤ Real.exp (((1 : ℝ) / 4 + 1 / 17 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2))
  ∧ (12 * Real.log N
      ≤ Real.exp (((1 : ℝ) / 4 - 1 / 68 - 4 * kimDelta) * Real.log N
          - 8 * Real.sqrt (Real.log N) - 4) / (Real.log N) ^ 8)
  ∧ (960 * (Real.log N) ^ 14
      ≤ Real.exp (((1 : ℝ) / 2 - 5 * kimDelta) * Real.log N
          - 8 * Real.sqrt (Real.log N) - 4))
  ∧ (Real.exp (-(1 / (4 * kimEps N))) ≤ kimEps N / 8)

/-- **The concrete content of Kim's "for sufficiently large `n`".**

Kim states his estimates for large `n` without fixing a threshold. We record
the largeness facts the argument actually consumes; each is a statement about
`n` alone, and all of them hold once `n` is large. -/
def KimLarge (N : ℕ) : Prop :=
  8 < (N : ℝ) ∧ theta N ≤ 1 / 100 ∧ Real.exp 1 ≤ Real.log N
    ∧ 0 < Nat.choose N (tParam N)
    ∧ 8 / ((N : ℝ) ^ ((1 : ℝ) / 4)) ≤ 1
    ∧ 32 * theta N * Real.exp 1 ≤ 4 * Real.log N
    ∧ (Real.sqrt (kimDelta * Real.log N) + 1 + theta N) * theta N ≤ 1 / 2
    ∧ (N : ℝ) ^ kimDelta * Real.log N / (N : ℝ) ^ ((1 : ℝ) / 4) ≤ 1 / 2
    ∧ Real.log 2 + 7 ≤ 4 * Real.log N
    ∧ 98 * Real.exp 14 + 7 ≤ 7 * Real.log N
    ∧ (N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 4
        ≤ (Real.exp (-(kimDelta * Real.log N)
          - 2 * Real.sqrt (kimDelta * Real.log N) - 1)) ^ 2
          * theta N * Real.sqrt N
    ∧ (Real.sqrt (kimDelta * Real.log N) + 1 + theta N) * theta N ≤ 1 / 8
    ∧ 25 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3) + 1
        ≤ (N : ℝ) ^ ((1 : ℝ) / 4)
    ∧ (Real.log N) ^ 20 ≤ (N : ℝ) ^ ((1 : ℝ) / 8)
    ∧ KimAsym N

lemma KimLarge.asym {N : ℕ} (h : KimLarge N) : KimAsym N :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2

lemma KimLarge.card_pos {N : ℕ} (h : KimLarge N) : 0 < N := by
  have h8 : (8 : ℝ) < N := h.1
  have : (0 : ℝ) < N := by linarith
  exact_mod_cast this

lemma tendsto_log_natCast_atTop :
    Filter.Tendsto (fun N : ℕ => Real.log N) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_loglog_atTop :
    Filter.Tendsto (fun N : ℕ => Real.log (Real.log N))
      Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp tendsto_log_natCast_atTop

lemma eventually_log_ge (c : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, c ≤ Real.log N :=
  tendsto_log_natCast_atTop.eventually_ge_atTop c

lemma eventually_theta_le (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in Filter.atTop, theta N ≤ c := by
  filter_upwards [eventually_log_ge (Real.sqrt (1 / c)),
    eventually_log_ge 1] with N hN h1
  have hsq : Real.sqrt (1 / c) ^ 2 = 1 / c :=
    Real.sq_sqrt (by positivity)
  have hpos : (0 : ℝ) < Real.log N ^ 2 := by nlinarith
  have hsqnn : 0 ≤ Real.sqrt (1 / c) := Real.sqrt_nonneg _
  have hsqle : Real.sqrt (1 / c) ^ 2 ≤ Real.log N ^ 2 := by nlinarith
  have hinv : 1 / c ≤ Real.log N ^ 2 := by rw [← hsq]; exact hsqle
  rw [theta, div_le_iff₀ hpos]
  rw [div_le_iff₀ hc] at hinv
  linarith

/-- `81 log N ≤ N` eventually: `log` is `o(id)`. -/
lemma eventually_log_lin :
    ∀ᶠ N : ℕ in Filter.atTop, 81 * Real.log N ≤ (N : ℝ) := by
  have h := Real.isLittleO_log_id_atTop.bound (c := 1 / 81) (by norm_num)
  have h' : ∀ᶠ x : ℕ in Filter.atTop,
      ‖Real.log x‖ ≤ (1 / 81) * ‖(x : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h', Filter.eventually_ge_atTop 1] with N hN h1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hNpos] at hN
  have hlog : Real.log N ≤ |Real.log N| := le_abs_self _
  linarith

/-- `t = ⌈9√(n log n)⌉ ≤ n` eventually, so `C(n, t) > 0`. -/
lemma eventually_tParam_le :
    ∀ᶠ N : ℕ in Filter.atTop, tParam N ≤ N := by
  filter_upwards [eventually_log_lin, Filter.eventually_ge_atTop 1]
    with N hlin h1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast h1
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  refine Nat.ceil_le.mpr ?_
  have hsq : Real.sqrt ((N : ℝ) * Real.log N) ≤ (N : ℝ) / 9 := by
    rw [show (N : ℝ) / 9 = Real.sqrt (((N : ℝ) / 9) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [div_pow]
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 9 ^ 2)]
    nlinarith [hlin, hNpos, hlog0]
  linarith

/-- `8 ≤ N^{1/4}` eventually. -/
lemma eventually_eight_le_quarter :
    ∀ᶠ N : ℕ in Filter.atTop, 8 / ((N : ℝ) ^ ((1 : ℝ) / 4)) ≤ 1 := by
  filter_upwards [Filter.eventually_ge_atTop 4096] with N hN
  have hNR : (4096 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h8 : (8 : ℝ) = (4096 : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [show (4096 : ℝ) = (8 : ℝ) ^ (4 : ℕ) by norm_num,
      ← Real.rpow_natCast (8 : ℝ) 4, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hmono : (4096 : ℝ) ^ ((1 : ℝ) / 4) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (by norm_num) hNR (by norm_num)
  have hpos : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 4) := by
    refine Real.rpow_pos_of_pos ?_ _
    linarith
  rw [div_le_one hpos]
  linarith [h8 ▸ hmono]

/-- `32θe ≤ 4 log N` eventually. -/
lemma eventually_theta_exp_le :
    ∀ᶠ N : ℕ in Filter.atTop, 32 * theta N * Real.exp 1 ≤ 4 * Real.log N := by
  filter_upwards [eventually_theta_le (1 / (32 * Real.exp 1))
      (by positivity), eventually_log_ge 1] with N hθ hlog
  have hexp : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h1 : 32 * theta N * Real.exp 1 ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hθ (by positivity : (0:ℝ) ≤ 32 * Real.exp 1)
    calc 32 * theta N * Real.exp 1 = (32 * Real.exp 1) * theta N := by ring
      _ ≤ (32 * Real.exp 1) * (1 / (32 * Real.exp 1)) := by
          exact mul_le_mul_of_nonneg_left hθ (by positivity)
      _ = 1 := by field_simp
  linarith

/-- `(√(δ log N) + 1 + θ)·θ ≤ 1/2` eventually. -/
lemma eventually_aTheta_le :
    ∀ᶠ N : ℕ in Filter.atTop,
      (Real.sqrt (kimDelta * Real.log N) + 1 + theta N) * theta N ≤ 1 / 2 := by
  filter_upwards [eventually_log_ge 4] with N hlog
  set L : ℝ := Real.log N with hL
  have hL4 : (4 : ℝ) ≤ L := hlog
  have hL0 : (0 : ℝ) < L := by linarith
  set s : ℝ := Real.sqrt L with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hssq : s ^ 2 = L := Real.sq_sqrt (by linarith)
  have hs2 : (2 : ℝ) ≤ s := by nlinarith [hssq, hs0]
  have hθ : theta N = 1 / L ^ 2 := by rw [theta, hL]
  have hδ : Real.sqrt (kimDelta * L) ≤ s := by
    rw [hs]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [kimDelta_lt, kimDelta_pos, hL0]
  have hθ0 : 0 < theta N := by rw [hθ]; positivity
  have hθle : theta N ≤ 1 / 16 := by
    rw [hθ]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL4]
  rw [hθ]
  have hLsq : L ^ 2 = s ^ 4 := by rw [← hssq]; ring
  rw [hLsq]
  have hs4 : (0 : ℝ) < s ^ 4 := by positivity
  have hinv : (1 : ℝ) / s ^ 4 ≤ 1 := by
    rw [div_le_one hs4]; nlinarith [hs2]
  have hnum : Real.sqrt (kimDelta * L) + 1 + 1 / s ^ 4 ≤ s + 2 := by
    linarith [hδ, hinv]
  have hkey : (s + 2) * (1 / s ^ 4) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ hs4 (by norm_num)]
    nlinarith [hs2]
  calc (Real.sqrt (kimDelta * L) + 1 + 1 / s ^ 4) * (1 / s ^ 4)
      ≤ (s + 2) * (1 / s ^ 4) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ ≤ 1 / 2 := hkey

/-- `N^δ·log N / N^{1/4} ≤ 1/2` eventually, since `δ < 1/4` and `log` is
`o(x^r)` for every `r > 0`. -/
lemma eventually_rpow_delta_le :
    ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) ^ kimDelta * Real.log N / (N : ℝ) ^ ((1 : ℝ) / 4) ≤ 1 / 2 := by
  have hr : 0 < (1 : ℝ) / 4 - kimDelta := by
    have h := kimDelta_lt
    have : (1 : ℝ) / 17 < 1 / 4 := by norm_num
    linarith
  have h := (isLittleO_log_rpow_atTop hr).bound (c := 1 / 2) (by norm_num)
  have h' := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h', Filter.eventually_ge_atTop 1] with N hN h1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast h1
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hrp : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 4 - kimDelta) :=
    Real.rpow_pos_of_pos hNpos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hrp,
    abs_of_nonneg hlog0] at hN
  have hsplit : (N : ℝ) ^ ((1 : ℝ) / 4)
      = (N : ℝ) ^ kimDelta * (N : ℝ) ^ ((1 : ℝ) / 4 - kimDelta) := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hδp : (0 : ℝ) < (N : ℝ) ^ kimDelta := Real.rpow_pos_of_pos hNpos _
  rw [hsplit]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hN, hδp, hrp]


/-- `log x ≤ 2√x` for `x > 0`: `log x = 2 log √x ≤ 2(√x − 1)`. -/
lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos hsx
  have h2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  rw [h2] at h1
  linarith

/-- **The step every `≤ exp(−n^c)` line in Kim §4 performs.**
`K ≤ exp(E)/L^d` whenever `log K + d·log L ≤ E`; we use `log L ≤ 2√L`. -/
lemma le_exp_div_pow {L E K : ℝ} {d : ℕ} (hL : 0 < L) (hK : 0 < K)
    (h : Real.log K + 2 * (d : ℝ) * Real.sqrt L ≤ E) :
    K ≤ Real.exp E / L ^ d := by
  have hLd : (0 : ℝ) < L ^ d := by positivity
  rw [le_div_iff₀ hLd]
  have hprod : (0 : ℝ) < K * L ^ d := by positivity
  rw [← Real.exp_log hprod]
  refine Real.exp_le_exp.mpr ?_
  rw [Real.log_mul (ne_of_gt hK) (ne_of_gt hLd), Real.log_pow]
  have hlogL : Real.log L ≤ 2 * Real.sqrt L := log_le_two_sqrt hL
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  nlinarith [h, hlogL, hd]

/-- `A√L + B ≤ cL` eventually, for `c > 0`. The generic form of the
`n^{c} ≫ polylog` comparisons in §4. -/
lemma eventually_sqrt_lin_le {c A B : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in Filter.atTop, A * Real.sqrt L + B ≤ c * L := by
  filter_upwards [Filter.eventually_ge_atTop
    (max 1 (((A + B + 1) / c) ^ 2))] with L hL
  have hL1 : (1 : ℝ) ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : (((A + B + 1) / c) ^ 2 : ℝ) ≤ L := le_trans (le_max_right _ _) hL
  have hs1 : (1 : ℝ) ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hL1
  have hs : (A + B + 1) / c ≤ Real.sqrt L := by
    have h := Real.sqrt_le_sqrt hL2
    rwa [Real.sqrt_sq (by positivity)] at h
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (by linarith)
  have hstep : ((A + B + 1) / c) * Real.sqrt L ≤ Real.sqrt L * Real.sqrt L :=
    mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg L)
  rw [hsq, div_mul_eq_mul_div, div_le_iff₀ hc] at hstep
  nlinarith [hstep, hs1, hA, hB]

/-- **`n^r` beats `K·(log n)^d`**, for any `r, c, K > 0` and any degree `d`.
This is the comparison behind every `≤ exp(−n^{c})` in Kim §4. -/
lemma eventually_polylog_le_rpow {r c K : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hK : 0 < K) (d : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop, K * (Real.log N) ^ d ≤ c * (N : ℝ) ^ r := by
  have hbase := tendsto_log_natCast_atTop.eventually
    ((eventually_sqrt_lin_le (c := r) (A := 2 * (d : ℝ))
        (B := |Real.log (K / c)|) hr (by positivity) (abs_nonneg _)).and
      (Filter.eventually_gt_atTop (0 : ℝ)))
  filter_upwards [hbase, Filter.eventually_ge_atTop 1] with N hN h1
  obtain ⟨hbig, hLpos⟩ := hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast h1
  set L : ℝ := Real.log N with hL
  have hrpow : (N : ℝ) ^ r = Real.exp (r * L) := by
    rw [Real.rpow_def_of_pos hNpos, hL]; ring_nf
  rw [hrpow]
  have hkey : K / c ≤ Real.exp (r * L) / L ^ d := by
    refine le_exp_div_pow hLpos (by positivity) ?_
    have hle : Real.log (K / c) ≤ |Real.log (K / c)| := le_abs_self _
    linarith
  rw [le_div_iff₀ (by positivity : (0:ℝ) < L ^ d)] at hkey
  rw [div_mul_eq_mul_div, div_le_iff₀ hc] at hkey
  linarith [hkey]

/-- **Kim's §4 exponent lines, in one uniform form.**

Every `≤ exp(−n^{c})` step compares a polynomial `K·L^m` in `L = log n` against
`exp(cL − A√L − B)/L^d`, where `cL` comes from the power of `n` surviving after
the tilt is substituted, `A√L` from the `b ≥ n^{−δ−o(1)}` bound, and `L^d` from
the powers of `θ = L⁻²`. Since `c > 0`, the exponential wins. -/
lemma eventually_exponent_beats {c A B K : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hK : 0 < K) (m d : ℕ) :
    ∀ᶠ L : ℝ in Filter.atTop,
      K * L ^ m ≤ Real.exp (c * L - A * Real.sqrt L - B) / L ^ d := by
  filter_upwards [eventually_sqrt_lin_le (c := c)
      (A := 2 * (m : ℝ) + 2 * (d : ℝ) + A) (B := |Real.log K| + B) hc
      (by positivity) (by positivity),
    Filter.eventually_gt_atTop (0 : ℝ),
    Filter.eventually_ge_atTop (1 : ℝ)] with L hbig hL0 hL1
  refine le_exp_div_pow hL0 (by positivity) ?_
  have hlogKL : Real.log (K * L ^ m) = Real.log K + (m : ℝ) * Real.log L := by
    rw [Real.log_mul (ne_of_gt hK) (by positivity), Real.log_pow]
  have hlogL : Real.log L ≤ 2 * Real.sqrt L := log_le_two_sqrt hL0
  have hKabs : Real.log K ≤ |Real.log K| := le_abs_self _
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [hlogKL]
  nlinarith [hbig, hlogL, hKabs, hm, Real.sqrt_nonneg L]

/-- **Kim's §4.3 exponent, in reduced form.** With `ρ = n^{−3/4}` the net
exponent is `b²θ²n^{1/4} − θe/2`; using `b ≥ exp(−δL − 2√(δL) − 1)` and
`θ = L⁻²` this is at least `exp((1/4−2δ)L − 4√(δL) − 2)/L⁴`, and
`1/4 − 2δ ≈ 0.132 > 0` makes it beat `3L`. -/
lemma property2_exponent_reduce {L : ℝ} (hL : 0 < L) {c : ℝ} (hc : 0 < c)
    (hbig : 16 * Real.sqrt L + 6 ≤ c * L)
    (hK : (3 : ℝ) * L + Real.exp 1 / 2 ≤ 3 * L + 2) :
    (3 : ℝ) * L + Real.exp 1 / 2
      ≤ Real.exp (c * L - 4 * Real.sqrt L - 2) / L ^ 4 := by
  have hs0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hL4 : (0 : ℝ) < L ^ 4 := by positivity
  rw [le_div_iff₀ hL4]
  -- it suffices that the exponent beats `log ((3L+2)·L⁴)`
  have hpos : (0 : ℝ) < (3 * L + 2) * L ^ 4 := by positivity
  refine le_trans (mul_le_mul_of_nonneg_right hK (le_of_lt hL4)) ?_
  rw [← Real.exp_log hpos]
  refine Real.exp_le_exp.mpr ?_
  have hlogprod : Real.log ((3 * L + 2) * L ^ 4)
      = Real.log (3 * L + 2) + 4 * Real.log L := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  rw [hlogprod]
  have h1 : Real.log (3 * L + 2) ≤ 2 * Real.sqrt (3 * L + 2) := by
    exact log_le_two_sqrt (by positivity)
  have h2 : Real.log L ≤ 2 * Real.sqrt L := log_le_two_sqrt hL
  have h3 : Real.sqrt (3 * L + 2) ≤ 2 * Real.sqrt L + 2 := by
    have hle : (3 : ℝ) * L + 2 ≤ (2 * Real.sqrt L + 2) ^ 2 := by
      have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
      nlinarith [hs0, hsq]
    calc Real.sqrt (3 * L + 2) ≤ Real.sqrt ((2 * Real.sqrt L + 2) ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = 2 * Real.sqrt L + 2 := Real.sqrt_sq (by positivity)
  linarith

/-- `16√L + 6 ≤ cL` eventually, for any `c > 0`. -/
lemma eventually_sixteen_sqrt_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in Filter.atTop, 16 * Real.sqrt L + 6 ≤ c * L := by
  filter_upwards [Filter.eventually_ge_atTop (max 1 ((22 / c) ^ 2))] with L hL
  have hL1 : (1 : ℝ) ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : ((22 / c) ^ 2 : ℝ) ≤ L := le_trans (le_max_right _ _) hL
  have hs : Real.sqrt L ≥ 22 / c := by
    have h := Real.sqrt_le_sqrt hL2
    rwa [Real.sqrt_sq (by positivity)] at h
  have hs1 : (1 : ℝ) ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hL1
  have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt (by linarith)
  have hkey : 22 * Real.sqrt L ≤ c * L := by
    have hstep : (22 / c) * Real.sqrt L ≤ Real.sqrt L * Real.sqrt L :=
      mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg L)
    have hsq' : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (by linarith)
    rw [hsq', div_mul_eq_mul_div, div_le_iff₀ hc] at hstep
    linarith
  nlinarith [hkey, hs1]

/-- **Kim's §4.3 exponent estimate holds eventually.** -/
lemma eventually_property2_exponent :
    ∀ᶠ N : ℕ in Filter.atTop,
      3 * Real.log N + Real.exp 1 / 2
        ≤ Real.exp (((1 : ℝ) / 4 - 2 * kimDelta) * Real.log N
            - 4 * Real.sqrt (Real.log N) - 2) / (Real.log N) ^ 4 := by
  have hc : (0 : ℝ) < (1 : ℝ) / 4 - 2 * kimDelta := by
    have h := kimDelta_lt
    have : (2 : ℝ) * kimDelta < 2 * (1 / 17) := by linarith
    norm_num at this ⊢
    linarith
  have hL := tendsto_log_natCast_atTop.eventually
    ((eventually_sixteen_sqrt_le hc).and (Filter.eventually_gt_atTop (0 : ℝ)))
  filter_upwards [hL] with N hN
  obtain ⟨hbig, hpos⟩ := hN
  refine property2_exponent_reduce hpos hc hbig ?_
  have : Real.exp 1 ≤ 3 := by
    have h := Real.exp_one_lt_d9
    linarith
  linarith

lemma kimDelta_quarter_pos : (0 : ℝ) < (1 : ℝ) / 4 - 2 * kimDelta := by
  have h := kimDelta_lt
  have h2 : (2 : ℝ) * kimDelta < 2 * (1 / 17) := by linarith
  norm_num at h2 ⊢
  linarith

lemma kimDelta_c3_pos : (0 : ℝ) < (1 : ℝ) / 4 - 3 * kimDelta := by
  have h := kimDelta_lt
  have h2 : (3 : ℝ) * kimDelta < 3 * (1 / 17) := by linarith
  norm_num at h2 ⊢; linarith

/-- `1/17 − δ = 10⁻⁵ > 0`.  This is the whole content of Kim's choice
`δ = 1/17 − 10⁻⁵`: (39)'s variance/drift ratio is `O((log n)^{4.25}·n^{δ−1/17})`
and converges only because this is strictly positive. -/
lemma kimDelta_c14_pos : (0 : ℝ) < (3 : ℝ) / 8 - 3 * kimDelta := by
  rw [kimDelta]; norm_num

lemma kimDelta_c11_pos :
    (0 : ℝ) < (1 : ℝ) / 4 - 1 / 17 - 2 * kimDelta := by
  rw [kimDelta]; norm_num

lemma kimDelta_c9_pos : (0 : ℝ) < (1 : ℝ) / 6 - kimDelta := by
  rw [kimDelta]; norm_num

lemma kimDelta_c8_pos : (0 : ℝ) < (1 : ℝ) / 4 - kimDelta := by
  rw [kimDelta]; norm_num

lemma kimDelta_c18_pos : (0 : ℝ) < (1 : ℝ) / 17 - kimDelta / 2 := by
  have h := kimDelta_lt
  have hp := kimDelta_pos
  linarith

lemma kimDelta_c19_pos :
    (0 : ℝ) < (1 : ℝ) / 4 + 1 / 17 - 2 * kimDelta := by
  have h := kimDelta_lt
  have h2 : (2 : ℝ) * kimDelta < 2 * (1 / 17) := by linarith
  norm_num at h2 ⊢; linarith

lemma kimDelta_c17_pos : (0 : ℝ) < (1 : ℝ) / 2 - 5 * kimDelta := by
  have h := kimDelta_lt
  have h2 : (5 : ℝ) * kimDelta < 5 * (1 / 17) := by linarith
  norm_num at h2 ⊢; linarith

/-- `1/4 − 1/68 − 4δ = 4·10⁻⁵ > 0`.  With Kim's `δ = 1/17 − 10⁻⁵` this is
*exactly* `4·10⁻⁵`: at `δ = 1/17` the §4.7 drift-versus-union comparison is a
dead heat, and the `10⁻⁵` in his `δ` is what breaks the tie. -/
lemma kimDelta_c16_pos : (0 : ℝ) < (1 : ℝ) / 4 - 1 / 68 - 4 * kimDelta := by
  rw [kimDelta]; norm_num

lemma kimDelta_c4_pos : (0 : ℝ) < (1 : ℝ) / 2 - 2 * kimDelta := by
  have h := kimDelta_lt
  have h2 : (2 : ℝ) * kimDelta < 2 * (1 / 17) := by linarith
  norm_num at h2 ⊢; linarith

/-- **Kim's §4.6 exponent estimate.** `b³θ²n^{3/8} ≥ 6L`, with surviving
exponent `3/8 − 3δ ≈ 0.199 > 0`. -/
lemma eventually_property5_exp :
    ∀ᶠ N : ℕ in Filter.atTop,
      6 * Real.log N
        ≤ Real.exp (((3 : ℝ) / 8 - 3 * kimDelta) * Real.log N
            - 6 * Real.sqrt (Real.log N) - 3) / (Real.log N) ^ 4 := by
  have h := tendsto_log_natCast_atTop.eventually
    (eventually_exponent_beats kimDelta_c14_pos (by norm_num : (0:ℝ) ≤ 6)
      (by norm_num : (0:ℝ) ≤ 3) (by norm_num : (0:ℝ) < 6) 1 4)
  filter_upwards [h] with N hN
  simpa using hN

/-- `t ≤ 9√n·√(log n) + 1`. -/
lemma tParam_le_bound {N : ℕ} (hN : 1 ≤ N) :
    (tParam N : ℝ) ≤ 9 * Real.sqrt N * Real.sqrt (Real.log N) + 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsplit : Real.sqrt ((N : ℝ) * Real.log N)
      = Real.sqrt N * Real.sqrt (Real.log N) := Real.sqrt_mul hNpos.le _
  have h := Nat.ceil_lt_add_one
    (show (0:ℝ) ≤ 9 * Real.sqrt ((N : ℝ) * Real.log N) by positivity)
  rw [hsplit] at h
  rw [tParam, hsplit]
  linarith [h.le]



/-- **§4.5 drift**, at the tilt `ρ = n^{−1/4}`: `b²θ³√n·n^{−1/4} ≥ 8L/5`. -/
lemma eventually_property4_drift :
    ∀ᶠ N : ℕ in Filter.atTop,
      2 * Real.log N
        ≤ Real.exp (((1 : ℝ) / 4 - 2 * kimDelta) * Real.log N
            - 4 * Real.sqrt (Real.log N) - 2) / (Real.log N) ^ 6 := by
  have h := tendsto_log_natCast_atTop.eventually
    (eventually_exponent_beats kimDelta_quarter_pos (by norm_num : (0:ℝ) ≤ 4)
      (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) < 2) 1 6)
  filter_upwards [h] with N hN
  simpa using hN

/-- **§4.5 variance**, at the tilt `ρ = n^{−1/4}`: `20 n^δ L⁸ ≤ b²n^{1/4}`. -/
lemma eventually_property4_var :
    ∀ᶠ N : ℕ in Filter.atTop,
      20 * (Real.log N) ^ 8
        ≤ Real.exp (((1 : ℝ) / 4 - 3 * kimDelta) * Real.log N
            - 4 * Real.sqrt (Real.log N) - 2) := by
  have h := tendsto_log_natCast_atTop.eventually
    (eventually_exponent_beats kimDelta_c3_pos (by norm_num : (0:ℝ) ≤ 4)
      (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) < 20) 8 0)
  filter_upwards [h] with N hN
  simpa using hN

/-- **§4.5 second exponent**, at the tilt `ρ = θ²`: `b²θ⁵√n ≥ 2L`. -/
lemma eventually_property4_exp2' :
    ∀ᶠ N : ℕ in Filter.atTop,
      2 * Real.log N
        ≤ Real.exp (((1 : ℝ) / 2 - 2 * kimDelta) * Real.log N
            - 4 * Real.sqrt (Real.log N) - 2) / (Real.log N) ^ 10 := by
  have h := tendsto_log_natCast_atTop.eventually
    (eventually_exponent_beats kimDelta_c4_pos (by norm_num : (0:ℝ) ≤ 4)
      (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) < 2) 1 10)
  filter_upwards [h] with N hN
  simpa using hN

/-- **§4.7 tilt admissibility**: `96 L⁵ ≤ n^{1/100}`. -/
lemma eventually_property6_ab :
    ∀ᶠ N : ℕ in Filter.atTop,
      108 * (Real.log N) ^ 3 ≤ (N : ℝ) ^ ((1 : ℝ) / 68) := by
  have h := eventually_polylog_le_rpow (r := (1 : ℝ) / 68) (c := 1)
    (K := 108) (by norm_num) (by norm_num) (by norm_num) 3
  filter_upwards [h] with N hN
  linarith [hN]

/-- **§4.7 drift**: `t·b²θ²·n^{1/3} ≥ 12 L` at `t = kimRho6`. -/
lemma eventually_property6_c :
    ∀ᶠ N : ℕ in Filter.atTop,
      12 * Real.log N
        ≤ Real.exp (((1 : ℝ) / 4 - 1 / 68 - 4 * kimDelta) * Real.log N
            - 8 * Real.sqrt (Real.log N) - 4) / (Real.log N) ^ 8 := by
  have h := tendsto_log_natCast_atTop.eventually
    (eventually_exponent_beats kimDelta_c16_pos (by norm_num : (0:ℝ) ≤ 8)
      (by norm_num : (0:ℝ) ≤ 4) (by norm_num : (0:ℝ) < 12) 1 8)
  filter_upwards [h] with N hN
  simpa using hN

/-- **§4.7's lower bound on the frozen threshold**:
`27n^δ(log n)³ ≤ e^{(1/2−2δ)L−4√L−2}/L⁴ ≤ θ²b_{k₀}²√n`. -/
lemma eventually_property7_mcutlow :
    ∀ᶠ N : ℕ in Filter.atTop,
      960 * (Real.log N) ^ 14
        ≤ Real.exp (((1 : ℝ) / 2 - 5 * kimDelta) * Real.log N
            - 8 * Real.sqrt (Real.log N) - 4) := by
  have h := tendsto_log_natCast_atTop.eventually
    (eventually_exponent_beats kimDelta_c17_pos (by norm_num : (0:ℝ) ≤ 8)
      (by norm_num : (0:ℝ) ≤ 4) (by norm_num : (0:ℝ) < 960) 14 0)
  filter_upwards [h] with N hN
  simpa using hN

/-- **§4.8 (40)'s `n^{1/4}log n` residue**: `11 L⁵ ≤ n^{1/4−δ}·e^{−2√L−1}`. -/
lemma eventually_property7_quarter :
    ∀ᶠ N : ℕ in Filter.atTop,
      11 * (Real.log N) ^ 5
        ≤ Real.exp (((1 : ℝ) / 4 - kimDelta) * Real.log N
            - 2 * Real.sqrt (Real.log N) - 1) := by
  have h := tendsto_log_natCast_atTop.eventually
    (eventually_exponent_beats kimDelta_c8_pos (by norm_num : (0:ℝ) ≤ 2)
      (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) < 11) 5 0)
  filter_upwards [h] with N hN
  simpa using hN

/-- **§4.8's almost-disjointness scale**: `960 L⁶ ≤ n^{1/6−δ}`. -/
lemma eventually_property7_beta :
    ∀ᶠ N : ℕ in Filter.atTop,
      960 * (Real.log N) ^ 6
        ≤ Real.exp (((1 : ℝ) / 6 - kimDelta) * Real.log N) := by
  have h := tendsto_log_natCast_atTop.eventually
    (eventually_exponent_beats kimDelta_c9_pos (by norm_num : (0:ℝ) ≤ 0)
      (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) < 960) 6 0)
  filter_upwards [h] with N hN
  simpa using hN

/-- **§4.8's drift beats the `C(n,t)` union.**  At Kim's `ρ = n^{−1/4−1/17}`
each per-`T` drift is `≈ b²n^{3/4−1/17}`, against `exp(t·log n)`; the surviving
exponent is `1/4 − 1/17 − 2δ ≈ 0.0736 > 0`. -/
lemma eventually_property7_drift :
    ∀ᶠ N : ℕ in Filter.atTop,
      12 * (Real.log N) ^ 5
        ≤ Real.exp (((1 : ℝ) / 4 - 1 / 17 - 2 * kimDelta) * Real.log N
            - 4 * Real.sqrt (Real.log N) - 2) := by
  have h := tendsto_log_natCast_atTop.eventually
    (eventually_exponent_beats kimDelta_c11_pos (by norm_num : (0:ℝ) ≤ 4)
      (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) < 12) 5 0)
  filter_upwards [h] with N hN
  simpa using hN

/-- **§4.8 (39)'s variance condition.**  `1000(log n)⁵ ≤ n^{1/17−δ}·e^{−2√L−1}`
— the `10⁻⁵` clause. -/
lemma eventually_property7_39var :
    ∀ᶠ N : ℕ in Filter.atTop,
      3072 * (Real.log N) ^ 6
        ≤ Real.exp (((1 : ℝ) / 17 - kimDelta / 2) * Real.log N
            - 2 * Real.sqrt (Real.log N) - 1) := by
  have h := tendsto_log_natCast_atTop.eventually
    (eventually_exponent_beats kimDelta_c18_pos (by norm_num : (0:ℝ) ≤ 2)
      (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) < 3072) 6 0)
  filter_upwards [h] with N hN
  simpa using hN

/-- **§4.8 (46)'s variance condition.** -/
lemma eventually_property7_46var :
    ∀ᶠ N : ℕ in Filter.atTop,
      1000000 * (Real.log N) ^ 8
        ≤ Real.exp (((1 : ℝ) / 4 + 1 / 17 - 2 * kimDelta) * Real.log N
            - 4 * Real.sqrt (Real.log N) - 2) := by
  have h := tendsto_log_natCast_atTop.eventually
    (eventually_exponent_beats kimDelta_c19_pos (by norm_num : (0:ℝ) ≤ 4)
      (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) < 1000000) 8 0)
  filter_upwards [h] with N hN
  simpa using hN

/-- **`e^{−1/(4ε)} ≤ ε/8`.**  With `v := (log log n)^{1/4} = ε⁻¹` this is
`8v ≤ e^{v/4}`, which `e^x ≥ x²/2` gives once `v ≥ 256`. -/
lemma eventually_property8_eps :
    ∀ᶠ N : ℕ in Filter.atTop,
      Real.exp (-(1 / (4 * kimEps N))) ≤ kimEps N / 8 := by
  filter_upwards [tendsto_loglog_atTop.eventually_ge_atTop
    ((256 : ℝ) ^ (4 : ℕ))] with N hN
  have hbig : (0 : ℝ) < (256 : ℝ) ^ (4 : ℕ) := by positivity
  have hw0 : (0 : ℝ) < Real.log (Real.log N) := by linarith
  set v : ℝ := (Real.log (Real.log N)) ^ ((1 : ℝ) / 4) with hvdef
  have hv0 : (0 : ℝ) < v := Real.rpow_pos_of_pos hw0 _
  have hv256 : (256 : ℝ) ≤ v := by
    have hbase : ((256 : ℝ) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) ≤ v :=
      Real.rpow_le_rpow (by positivity) hN (by norm_num)
    have heq : ((256 : ℝ) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) = 256 := by
      rw [← Real.rpow_natCast (256 : ℝ) 4, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith [hbase, heq.le, heq.ge]
  have heps : kimEps N = v⁻¹ := by
    rw [kimEps, show -(1 : ℝ) / 4 = -((1 : ℝ) / 4) by ring,
      Real.rpow_neg hw0.le, hvdef]
  rw [heps]
  have hinv : 1 / (4 * v⁻¹) = v / 4 := by field_simp
  rw [hinv]
  -- `e^{v/4} ≥ (v/4)²/2 = v²/32 ≥ 8v`
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ v / 4)
  have hlow : 8 * v ≤ Real.exp (v / 4) := by nlinarith [hq, hv256, hv0]
  have hE0 : (0 : ℝ) < Real.exp (v / 4) := Real.exp_pos _
  have hgoal : v⁻¹ / 8 = (8 * v)⁻¹ := by field_simp
  rw [Real.exp_neg, hgoal, inv_le_inv₀ hE0 (by positivity)]
  exact hlow

lemma eventually_kimAsym : ∀ᶠ N : ℕ in Filter.atTop, KimAsym N := by
  filter_upwards [
    eventually_property2_exponent, eventually_property4_drift,
    eventually_property4_var, eventually_property4_exp2',
    eventually_property5_exp, eventually_property6_ab,
    eventually_property7_quarter, eventually_property7_beta,
    eventually_property7_drift, eventually_property7_39var,
    eventually_property7_46var, eventually_property6_c,
    eventually_property7_mcutlow, eventually_property8_eps]
    with N a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩

namespace KimAsym

variable {N : ℕ}

lemma p2_exp (h : KimAsym N) :
    3 * Real.log N + Real.exp 1 / 2
      ≤ Real.exp (((1 : ℝ) / 4 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2) / (Real.log N) ^ 4 := h.1
lemma p4_drift (h : KimAsym N) :
    2 * Real.log N
      ≤ Real.exp (((1 : ℝ) / 4 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2) / (Real.log N) ^ 6 := h.2.1
lemma p4_var (h : KimAsym N) :
    20 * (Real.log N) ^ 8
      ≤ Real.exp (((1 : ℝ) / 4 - 3 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2) := h.2.2.1
lemma p4_exp2 (h : KimAsym N) :
    2 * Real.log N
      ≤ Real.exp (((1 : ℝ) / 2 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2) / (Real.log N) ^ 10 := h.2.2.2.1
lemma p5_exp (h : KimAsym N) :
    6 * Real.log N
      ≤ Real.exp (((3 : ℝ) / 8 - 3 * kimDelta) * Real.log N
          - 6 * Real.sqrt (Real.log N) - 3) / (Real.log N) ^ 4 := h.2.2.2.2.1
lemma p6_thr (h : KimAsym N) :
    108 * (Real.log N) ^ 3 ≤ (N : ℝ) ^ ((1 : ℝ) / 68) := h.2.2.2.2.2.1
lemma p7_quarter (h : KimAsym N) :
    11 * (Real.log N) ^ 5
      ≤ Real.exp (((1 : ℝ) / 4 - kimDelta) * Real.log N
          - 2 * Real.sqrt (Real.log N) - 1) := h.2.2.2.2.2.2.1
lemma p7_beta (h : KimAsym N) :
    960 * (Real.log N) ^ 6
      ≤ Real.exp (((1 : ℝ) / 6 - kimDelta) * Real.log N) := h.2.2.2.2.2.2.2.1
lemma p7_drift (h : KimAsym N) :
    12 * (Real.log N) ^ 5
      ≤ Real.exp (((1 : ℝ) / 4 - 1 / 17 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2) := h.2.2.2.2.2.2.2.2.1
lemma p7_39var (h : KimAsym N) :
    3072 * (Real.log N) ^ 6
      ≤ Real.exp (((1 : ℝ) / 17 - kimDelta / 2) * Real.log N
          - 2 * Real.sqrt (Real.log N) - 1) := h.2.2.2.2.2.2.2.2.2.1
lemma p7_46var (h : KimAsym N) :
    1000000 * (Real.log N) ^ 8
      ≤ Real.exp (((1 : ℝ) / 4 + 1 / 17 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2) := h.2.2.2.2.2.2.2.2.2.2.1
lemma p6_drift (h : KimAsym N) :
    12 * Real.log N
      ≤ Real.exp (((1 : ℝ) / 4 - 1 / 68 - 4 * kimDelta) * Real.log N
          - 8 * Real.sqrt (Real.log N) - 4) / (Real.log N) ^ 8 := h.2.2.2.2.2.2.2.2.2.2.2.1
lemma p7_mcutlow (h : KimAsym N) :
    960 * (Real.log N) ^ 14
      ≤ Real.exp (((1 : ℝ) / 2 - 5 * kimDelta) * Real.log N
          - 8 * Real.sqrt (Real.log N) - 4) := h.2.2.2.2.2.2.2.2.2.2.2.2.1
/-- **Kim's `ρ = −ε⁻¹/4` in §4.9 (58)**: `e^ρ ≤ ε/8`.  This is the only place
the argument needs `ε → 0` rather than merely `ε` small. -/
lemma p8_eps (h : KimAsym N) :
    Real.exp (-(1 / (4 * kimEps N))) ≤ kimEps N / 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2
end KimAsym

/-- Kim's block count `k₀ = ⌊n^δ/θ⌋`. -/
noncomputable def kimK0 (N : ℕ) : ℕ := ⌊(N : ℝ) ^ kimDelta / theta N⌋₊

lemma kimK0_le (N : ℕ) :
    kimK0 N ≤ ⌊(N : ℝ) ^ ((1 : ℝ) / 17 - 10 ^ (-5 : ℤ)) / theta N⌋₊ := by
  rw [kimK0, kimDelta]

/-- `k₀θ ≤ n^δ`, and `k₀θ > n^δ − θ`: the floor costs at most `θ`. -/
lemma kimK0_theta_bounds {N : ℕ} (hθpos : 0 < theta N) :
    (kimK0 N : ℝ) * theta N ≤ (N : ℝ) ^ kimDelta
      ∧ (N : ℝ) ^ kimDelta - theta N < (kimK0 N : ℝ) * theta N := by
  constructor
  · have hfl : (kimK0 N : ℝ) ≤ (N : ℝ) ^ kimDelta / theta N := by
      rw [kimK0]; exact Nat.floor_le (by positivity)
    rw [← le_div_iff₀ hθpos]; exact hfl
  · have hfl : (N : ℝ) ^ kimDelta / theta N < (kimK0 N : ℝ) + 1 := by
      rw [kimK0]; exact Nat.lt_floor_add_one _
    rw [div_lt_iff₀ hθpos] at hfl
    linarith

/-- `log(k₀θ) ≥ δ·log n − log 2` once `θ ≤ n^δ/2`, and `≤ δ·log n`. -/
lemma log_kimK0_theta_bounds {N : ℕ} (hθpos : 0 < theta N) (hN : 1 ≤ N)
    (hsmall : theta N ≤ (N : ℝ) ^ kimDelta / 2) :
    kimDelta * Real.log N - Real.log 2
        ≤ Real.log ((kimK0 N : ℝ) * theta N)
      ∧ Real.log ((kimK0 N : ℝ) * theta N) ≤ kimDelta * Real.log N := by
  have hNpos : (0 : ℝ) < N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hrp : (0 : ℝ) < (N : ℝ) ^ kimDelta := Real.rpow_pos_of_pos hNpos _
  obtain ⟨hup, hlo⟩ := kimK0_theta_bounds (N := N) hθpos
  have hpos : (0 : ℝ) < (kimK0 N : ℝ) * theta N := by linarith
  have hlogrp : Real.log ((N : ℝ) ^ kimDelta) = kimDelta * Real.log N :=
    Real.log_rpow hNpos _
  constructor
  · have hhalf : (N : ℝ) ^ kimDelta / 2 ≤ (kimK0 N : ℝ) * theta N := by
      linarith
    calc kimDelta * Real.log N - Real.log 2
        = Real.log ((N : ℝ) ^ kimDelta / 2) := by
          rw [Real.log_div (ne_of_gt hrp) (by norm_num), hlogrp]
      _ ≤ Real.log ((kimK0 N : ℝ) * theta N) :=
          Real.log_le_log (by positivity) hhalf
  · calc Real.log ((kimK0 N : ℝ) * theta N)
        ≤ Real.log ((N : ℝ) ^ kimDelta) := Real.log_le_log hpos hup
      _ = kimDelta * Real.log N := hlogrp

lemma kimDelta_val : kimDelta = 1 / 17 - 1 / 100000 := by
  rw [kimDelta]; norm_num

/-- `√δ ≥ 0.2424`. Kim's `0.23` in (17) comes from `√δ − δ/6 ≈ 0.2327`, and
the final comparison needs `> 0.2222`, so this constant carries the whole
margin. -/
lemma sqrt_kimDelta_ge : (2424 : ℝ) / 10000 ≤ Real.sqrt kimDelta := by
  rw [show (2424 : ℝ) / 10000 = Real.sqrt (((2424 : ℝ) / 10000) ^ 2) from
    (Real.sqrt_sq (by norm_num)).symm]
  refine Real.sqrt_le_sqrt ?_
  rw [kimDelta_val]
  norm_num

/-- **The core estimate behind Kim's `θ∑b_jμ_j ≥ 0.23√(log n)`**, stated over
plain reals: `s = √L`, `sd = √δ`, `r = √u`, `θ = L⁻²`.

The subtracted term is at most `sd²s/6 + 1`, so the bound is
`s(sd − sd²/6) − 3 ≥ 0.2325s − 3`, which clears `0.223s` once `s ≥ 400`. -/
lemma sum_bmu_core {s r sd u θ Sm : ℝ}
    (hs400 : 400 ≤ s) (hsd : 2424 / 10000 ≤ sd) (hsd1 : sd ≤ 1)
    (hsdsq : sd ^ 2 ≤ 1 / 17) (hθ : θ = 1 / (s ^ 2) ^ 2)
    (hr0 : 0 < r) (hu2 : u ≤ sd ^ 2 * s ^ 2)
    (hrup : r ≤ sd * s) (hrlo : sd * s - 1 ≤ r)
    (hSm : r - 1 - (18 * θ + 1 / (3 * s))
        * ((u + 2 * r + 1) / 2 + (3 / 2) * θ * (r + 1)) ≤ Sm) :
    (223 : ℝ) / 1000 * s ≤ Sm := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hθ0 : (0 : ℝ) < θ := by rw [hθ]; positivity
  have hrs : r ≤ s := by nlinarith [hrup, hsd1, hs0]
  -- `(s²)² ≥ 64·10⁶·s`, which the degree-4 denominators need
  have hstep1 : (400 : ℝ) * s ≤ s ^ 2 := by nlinarith [hs400, hs0]
  have hstep2 : ((400 : ℝ) * s) ^ 2 ≤ (s ^ 2) ^ 2 := by
    nlinarith [hstep1, hs0, hs400]
  have hs4 : (64000000 : ℝ) * s ≤ (s ^ 2) ^ 2 := by
    have hexp : ((400 : ℝ) * s) ^ 2 = 160000 * s ^ 2 := by ring
    rw [hexp] at hstep2
    nlinarith [hstep2, hstep1, hs0]
  -- `S ≤ sd²s²/2 + s + 1`
  have hS : (u + 2 * r + 1) / 2 + (3 / 2) * θ * (r + 1)
      ≤ sd ^ 2 * s ^ 2 / 2 + s + 1 := by
    have hsmall : (3 / 2) * θ * (r + 1) ≤ 1 / 2 := by
      rw [hθ]
      rw [show (3 : ℝ) / 2 * (1 / (s ^ 2) ^ 2) * (r + 1)
          = (3 * (r + 1)) / (2 * (s ^ 2) ^ 2) by ring,
        div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hrs, hs400, hs0, hs4]
    linarith
  have hcoef : (0 : ℝ) < 18 * θ + 1 / (3 * s) := by positivity
  have hmono : (18 * θ + 1 / (3 * s))
      * ((u + 2 * r + 1) / 2 + (3 / 2) * θ * (r + 1))
      ≤ (18 * θ + 1 / (3 * s)) * (sd ^ 2 * s ^ 2 / 2 + s + 1) :=
    mul_le_mul_of_nonneg_left hS hcoef.le
  -- `T ≤ sd²s/6 + 1`
  have hT : (18 * θ + 1 / (3 * s)) * (sd ^ 2 * s ^ 2 / 2 + s + 1)
      ≤ sd ^ 2 * s / 6 + 1 := by
    have hexp : (18 * θ + 1 / (3 * s)) * (sd ^ 2 * s ^ 2 / 2 + s + 1)
        = 18 * θ * (sd ^ 2 * s ^ 2 / 2 + s + 1)
          + (sd ^ 2 * s ^ 2 / 2 + s + 1) / (3 * s) := by ring
    rw [hexp]
    have hA : 18 * θ * (sd ^ 2 * s ^ 2 / 2 + s + 1) ≤ 1 / 2 := by
      rw [hθ]
      rw [show (18 : ℝ) * (1 / (s ^ 2) ^ 2) * (sd ^ 2 * s ^ 2 / 2 + s + 1)
          = (18 * (sd ^ 2 * s ^ 2 / 2 + s + 1)) / (s ^ 2) ^ 2 by ring,
        div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hsdsq, hs400, hs0, hsd1, hs4, hstep1]
    have hB : (sd ^ 2 * s ^ 2 / 2 + s + 1) / (3 * s) ≤ sd ^ 2 * s / 6 + 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hs400, hs0]
    linarith
  -- assemble
  have hkey : sd * s - 2 - (sd ^ 2 * s / 6 + 1) ≤ Sm := by
    linarith [hSm, hmono, hT, hrlo]
  nlinarith [hkey, hsd, hsdsq, hs400, hs0]

/-! ### Kim's parameter choices

The tilts `ρ` of §4.3–§4.8 and the auxiliary integer parameters, as explicit
functions of `n` and `k`. -/

/-- Kim's `ρ = n^{−3/4}` for Property 2 (§4.3). -/
noncomputable def kimRho2 (N : ℕ) : ℝ := (N : ℝ) ^ (-(3 : ℝ) / 4)

/-- Kim's `ρ = n^{−1/4}` for `Φ⁽²⁾` in Property 4 (§4.5, (24)). -/
noncomputable def kimRho4b (N : ℕ) : ℝ := (N : ℝ) ^ (-((1 : ℝ) / 4))

/-- Kim's `ρ = n^{−5/8}` for Property 5 (§4.6). -/
noncomputable def kimRho5 (N : ℕ) : ℝ := (N : ℝ) ^ (-(5 : ℝ) / 8)

/-- **Kim's §4.7 tilt** `ρ = n^{−1/4−ε₀}` with `ε₀ := 1/4 − 4/17 = 1/68`.

The drift-versus-union comparison it has to win is
`1/4 − ε₀ − 4δ = 17/68 − 1/68 − 16/68 + 4·10⁻⁵ = 4·10⁻⁵ > 0`:
at `δ = 1/17` exactly it would be a dead heat, and the `10⁻⁵` in Kim's
`δ = 1/17 − 10⁻⁵` is what breaks the tie.  The variance side needs the
coupling `β·b ≤ 3(log n)^{3/2}` — see `KimLarge.thr6_le`. -/
noncomputable def kimRho6 (N : ℕ) : ℝ :=
  (N : ℝ) ^ (-((1 : ℝ) / 4) - (1 : ℝ) / 68)

/-- **Kim's `ρ = n^{−1/4−1/17}` for §4.8 (39), (46), (49).**  Note the exponent
is `1/17`, *not* `δ = 1/17 − 10⁻⁵`: the whole point of `δ` being strictly below
`1/17` is that (39)'s variance/drift ratio is `O((log n)^{4.25}·n^{δ−1/17})`,
which converges only because of that `10⁻⁵`. -/
noncomputable def kimRho7 (N : ℕ) : ℝ :=
  (N : ℝ) ^ (-((1 : ℝ) / 4) - (1 : ℝ) / 17)

/-- Kim's `ρ = n^{−5/17}` for §4.8 (38). -/
noncomputable def kimRho38 (N : ℕ) : ℝ := (N : ℝ) ^ (-(5 : ℝ) / 17)

lemma kimRho38_nonneg (N : ℕ) : 0 ≤ kimRho38 N :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma kimRho2_nonneg (N : ℕ) : 0 ≤ kimRho2 N :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _
lemma kimRho4b_nonneg (N : ℕ) : 0 ≤ kimRho4b N :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _
lemma kimRho5_nonneg (N : ℕ) : 0 ≤ kimRho5 N :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _
lemma kimRho6_nonneg (N : ℕ) : 0 ≤ kimRho6 N :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma kimRho6_pos {N : ℕ} (hN : 0 < N) : 0 < kimRho6 N :=
  Real.rpow_pos_of_pos (by exact_mod_cast hN) _

lemma kimRho7_nonneg (N : ℕ) : 0 ≤ kimRho7 N :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- Kim's `β = (3(k+1)log n)^{1/2}` (§4.7, §4.8). -/
noncomputable def kimBeta (N k : ℕ) : ℝ :=
  Real.sqrt (3 * ((k : ℝ) + 1) * Real.log N)

/-- Kim's overlap allowance `I ≈ 12k log n` (§4.6). -/
noncomputable def kimI (N k : ℕ) : ℕ := ⌈4 * (3 * (k : ℝ) * Real.log N + 1)⌉₊

/-- Kim's `L⁽¹⁾`-defect bound `D` (§4.7, (34)/(35)). -/
noncomputable def kimDpar (N k : ℕ) : ℕ :=
  ⌈Real.sqrt (2 * (mcut N : ℝ)) / kimBeta N k⌉₊

/-- Kim's truncation threshold `thr = 2β√(2·mcut)` (§4.7) and its `T`-version
`2β√t` (§4.8). -/
noncomputable def kimThr6 (N k : ℕ) : ℝ :=
  2 * kimBeta N k * Real.sqrt (2 * (mcut N : ℝ))

noncomputable def kimThr7 (N k : ℕ) : ℝ :=
  2 * kimBeta N k * Real.sqrt ((tParam N : ℕ) : ℝ)

/-- Kim's `h = ⌈4((k+1)log n)^{1/2}t^{1/2}⌉` (§4.8). -/
noncomputable def kimHpar (N k : ℕ) : ℕ :=
  ⌈2 * kimBeta N k * Real.sqrt ((tParam N : ℕ) : ℝ)⌉₊

lemma kimI_ge (N k : ℕ) :
    4 * (3 * (k : ℝ) * Real.log N + 1) ≤ (kimI N k : ℝ) := Nat.le_ceil _

lemma kimDpar_ge (N k : ℕ) :
    Real.sqrt (2 * (mcut N : ℝ)) / kimBeta N k ≤ (kimDpar N k : ℝ) :=
  Nat.le_ceil _

lemma kimBeta_nonneg (N k : ℕ) : 0 ≤ kimBeta N k := Real.sqrt_nonneg _

lemma kimBeta_sq (N k : ℕ) (h : 0 ≤ Real.log N) :
    kimBeta N k ^ 2 = 3 * ((k : ℝ) + 1) * Real.log N := by
  rw [kimBeta]
  refine Real.sq_sqrt ?_
  positivity

/-- **`b_min·θ·√n ≥ n^δ(log n)⁴` eventually**, where
`b_min = exp(−δ log n − 2√(δ log n) − 1)` is Kim's uniform lower bound for `b_k`
over all `k ≤ k₀`. This one fact yields the slack condition, `b_{k+1} ≤ b_k²θ√n`,
and all of §4.6–§4.8's size comparisons (`I ≤ 4M`, `2D ≤ 2M`, …), since every
one of those is of the form "polylog·n^δ ≪ n^{1/2−δ}". -/
lemma eventually_kim_bmin :
    ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 4
        ≤ (Real.exp (-(kimDelta * Real.log N)
            - 2 * Real.sqrt (kimDelta * Real.log N) - 1)) ^ 2
          * theta N * Real.sqrt N := by
  have hc : (0 : ℝ) < 1 / 4 - 2 * kimDelta := by
    have h := kimDelta_lt; norm_num at h ⊢; linarith
  have hbeat := eventually_exponent_beats (c := (1 : ℝ) / 4 - 2 * kimDelta)
    (A := 4) (B := 2) (K := 1) hc (by norm_num) (by norm_num)
    (by norm_num) 6 0
  filter_upwards [tendsto_log_natCast_atTop.eventually hbeat,
    eventually_log_ge 1, Filter.eventually_ge_atTop 1] with N hb hL h1N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast h1N
  have hL1 : (1 : ℝ) ≤ Real.log N := hL
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hθ : theta N = 1 / Real.log N ^ 2 := by rw [theta]
  have hsqrt : Real.sqrt (N : ℝ) = Real.exp (Real.log N / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNpos]
    congr 1
    ring
  have hrpow : (N : ℝ) ^ ((1 : ℝ) / 4)
      = Real.exp ((1 : ℝ) / 4 * Real.log N) := by
    rw [Real.rpow_def_of_pos hNpos]
    congr 1
    ring
  simp only [pow_zero, div_one, one_mul] at hb
  have hδsq : Real.sqrt (kimDelta * Real.log N) ≤ Real.sqrt (Real.log N) := by
    refine Real.sqrt_le_sqrt ?_
    have hδ1 : kimDelta ≤ 1 := by
      have h := kimDelta_lt; norm_num at h ⊢; linarith
    nlinarith [hδ1, hL0.le, kimDelta_pos.le]
  have hkey : Real.log N ^ 6
      ≤ Real.exp (((1 : ℝ) / 4 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (kimDelta * Real.log N) - 2) := by
    refine le_trans hb (Real.exp_le_exp.mpr ?_)
    linarith [hδsq]
  -- assemble
  have hEsq : (Real.exp (-(kimDelta * Real.log N)
        - 2 * Real.sqrt (kimDelta * Real.log N) - 1)) ^ 2
      = Real.exp (2 * (-(kimDelta * Real.log N)
          - 2 * Real.sqrt (kimDelta * Real.log N) - 1)) := by
    rw [← Real.exp_nat_mul]
    congr 1
  have hsplit : Real.exp ((1 : ℝ) / 4 * Real.log N)
      * Real.exp (((1 : ℝ) / 4 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (kimDelta * Real.log N) - 2)
      = Real.sqrt (N : ℝ) * Real.exp (2 * (-(kimDelta * Real.log N)
          - 2 * Real.sqrt (kimDelta * Real.log N) - 1)) := by
    rw [hsqrt, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hexp0 : (0 : ℝ) < Real.exp ((1 : ℝ) / 4 * Real.log N) := Real.exp_pos _
  have hgoal : Real.exp ((1 : ℝ) / 4 * Real.log N) * Real.log N ^ 6
      ≤ Real.sqrt (N : ℝ) * Real.exp (2 * (-(kimDelta * Real.log N)
          - 2 * Real.sqrt (kimDelta * Real.log N) - 1)) := by
    rw [← hsplit]
    exact mul_le_mul_of_nonneg_left hkey hexp0.le
  have hLsq : (0 : ℝ) < Real.log N ^ 2 := by positivity
  have hEq : (Real.exp (-(kimDelta * Real.log N)
        - 2 * Real.sqrt (kimDelta * Real.log N) - 1)) ^ 2
        * theta N * Real.sqrt N
      = (Real.sqrt (N : ℝ) * Real.exp (2 * (-(kimDelta * Real.log N)
          - 2 * Real.sqrt (kimDelta * Real.log N) - 1))) / Real.log N ^ 2 := by
    rw [hθ, hEsq]; field_simp
  rw [hrpow, hEq, le_div_iff₀ hLsq]
  nlinarith [hgoal, hLsq]

/-- `(√(δ log n) + 1 + θ)·θ ≤ 1/8` eventually — the sharper form of
`eventually_aTheta_le` needed for `b_k ≤ 2b_{k+1}`. -/
lemma eventually_aTheta_le_eighth :
    ∀ᶠ N : ℕ in Filter.atTop,
      (Real.sqrt (kimDelta * Real.log N) + 1 + theta N) * theta N
        ≤ 1 / 8 := by
  filter_upwards [eventually_log_ge 16] with N hlog
  set L : ℝ := Real.log N with hL
  have hL16 : (16 : ℝ) ≤ L := hlog
  have hL0 : (0 : ℝ) < L := by linarith
  set s : ℝ := Real.sqrt L with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hssq : s ^ 2 = L := Real.sq_sqrt (by linarith)
  have hs4 : (4 : ℝ) ≤ s := by nlinarith [hssq, hs0]
  have hθ : theta N = 1 / L ^ 2 := by rw [theta, ← hL]
  have hθ0 : 0 < theta N := by rw [hθ]; positivity
  have hδ : Real.sqrt (kimDelta * L) ≤ s := by
    rw [hs]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [kimDelta_lt, kimDelta_pos, hL0]
  have hθle : theta N ≤ 1 := by
    rw [hθ]
    rw [div_le_one (by positivity)]
    nlinarith [hL16]
  have hnum : Real.sqrt (kimDelta * L) + 1 + theta N ≤ s + 2 := by
    linarith [hδ, hθle]
  have hprod : (Real.sqrt (kimDelta * L) + 1 + theta N) * theta N
      ≤ (s + 2) * theta N := by nlinarith [hnum, hθ0.le]
  have hfin : (s + 2) * theta N ≤ 1 / 8 := by
    rw [hθ, ← hssq, mul_one_div,
      div_le_iff₀ (by positivity : (0 : ℝ) < (s ^ 2) ^ 2)]
    nlinarith [hs4]
  linarith [hprod, hfin]

/-- `25n^δ(log n)³ + 1 ≤ n^{1/3}` eventually — the comparison behind
`2β ≤ √(mcut n)` and `2D ≤ 2M`. -/
lemma eventually_kim_mcut :
    ∀ᶠ N : ℕ in Filter.atTop,
      25 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3) + 1
        ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
  have hr : (0 : ℝ) < 1 / 4 - kimDelta := by
    have h := kimDelta_lt; norm_num at h ⊢; linarith
  have hpl := eventually_polylog_le_rpow (r := (1 : ℝ) / 4 - kimDelta)
    (c := 1 / 2) (K := 25) hr (by norm_num) (by norm_num) 3
  have hpl0 := eventually_polylog_le_rpow (r := (1 : ℝ) / 4 - kimDelta)
    (c := 1 / 2) (K := 1) hr (by norm_num) (by norm_num) 0
  filter_upwards [hpl, hpl0, Filter.eventually_ge_atTop 1] with N hN hN0 h1N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast h1N
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1N
  have hrp : (0 : ℝ) < (N : ℝ) ^ kimDelta := Real.rpow_pos_of_pos hNpos _
  have hrp1 : (1 : ℝ) ≤ (N : ℝ) ^ kimDelta :=
    Real.one_le_rpow hNR kimDelta_pos.le
  have hsplit : (N : ℝ) ^ kimDelta * (N : ℝ) ^ ((1 : ℝ) / 4 - kimDelta)
      = (N : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hstep1 : 25 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3)
      ≤ (N : ℝ) ^ kimDelta * ((1 / 2) * (N : ℝ) ^ ((1 : ℝ) / 4 - kimDelta)) := by
    have h1 : 25 * (Real.log N) ^ 3
        ≤ (1 / 2) * (N : ℝ) ^ ((1 : ℝ) / 4 - kimDelta) := hN
    nlinarith [h1, hrp.le]
  have hstep2 : (1 : ℝ)
      ≤ (N : ℝ) ^ kimDelta * ((1 / 2) * (N : ℝ) ^ ((1 : ℝ) / 4 - kimDelta)) := by
    have h1 : (1 : ℝ) * (Real.log N) ^ 0
        ≤ (1 / 2) * (N : ℝ) ^ ((1 : ℝ) / 4 - kimDelta) := hN0
    simp only [pow_zero, mul_one] at h1
    nlinarith [h1, hrp1]
  have hsum : 25 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3) + 1
      ≤ (N : ℝ) ^ kimDelta * (N : ℝ) ^ ((1 : ℝ) / 4 - kimDelta) := by
    have hd : (N : ℝ) ^ kimDelta
          * ((1 / 2) * (N : ℝ) ^ ((1 : ℝ) / 4 - kimDelta))
        + (N : ℝ) ^ kimDelta
          * ((1 / 2) * (N : ℝ) ^ ((1 : ℝ) / 4 - kimDelta))
        = (N : ℝ) ^ kimDelta * (N : ℝ) ^ ((1 : ℝ) / 4 - kimDelta) := by ring
    linarith [hstep1, hstep2, hd]
  rw [← hsplit]
  exact hsum

/-- `(log N)^20 ≤ N^{1/8}` eventually: logs are polynomially negligible. -/
lemma eventually_kim_polylog :
    ∀ᶠ N : ℕ in Filter.atTop,
      (Real.log N) ^ 20 ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
  have h := eventually_polylog_le_rpow (r := (1 : ℝ) / 8) (c := 1) (K := 1)
    (by norm_num) (by norm_num) (by norm_num) 20
  filter_upwards [h] with N hN
  simpa using hN

/-- Eventually, all of Kim's largeness conditions hold at once. -/
lemma eventually_kimLarge : ∀ᶠ N : ℕ in Filter.atTop, KimLarge N := by
  filter_upwards [eventually_theta_le (1 / 100) (by norm_num),
    eventually_log_ge (Real.exp 1), eventually_tParam_le,
    Filter.eventually_gt_atTop 8, eventually_eight_le_quarter,
    eventually_theta_exp_le, eventually_aTheta_le, eventually_rpow_delta_le,
    eventually_log_ge ((Real.log 2 + 7) / 4),
    eventually_log_ge ((98 * Real.exp 14 + 7) / 7),
    eventually_kim_bmin, eventually_aTheta_le_eighth, eventually_kim_mcut,
    eventually_kim_polylog, eventually_kimAsym]
    with N hθ hlog ht hN8 h8q hθe haθ hrp hl1 hl2 hbmin haθ8 hmc hpl hasym
  refine ⟨by exact_mod_cast hN8, hθ, hlog, Nat.choose_pos ht, h8q, hθe, haθ,
    hrp, ?_, ?_, hbmin, haθ8, hmc, hpl, hasym⟩
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 4)] at hl1
    linarith
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 7)] at hl2
    linarith

lemma KimLarge.edgeProb_le_half {N : ℕ} (h : KimLarge N) : edgeProb N ≤ 1 / 2 := by
  have hN : 1 ≤ N := by
    have h8 : (8 : ℝ) < N := h.1
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hsq : (1 : ℝ) ≤ Real.sqrt N := one_le_sqrt_cast hN
  have hθ0 : 0 ≤ theta N := theta_nonneg N
  have hstep : theta N / Real.sqrt N ≤ theta N := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hθ0, hsq]
  have := h.2.1
  rw [edgeProb]
  linarith [hstep]

lemma KimLarge.logn_ge_one {N : ℕ} (h : KimLarge N) : 1 ≤ Real.log N := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  linarith [h.2.2.1]

lemma KimLarge.theta_pos' {N : ℕ} (h : KimLarge N) : 0 < theta N := by
  have hN : 2 ≤ N := by
    have h8 : (8 : ℝ) < N := h.1
    have : (2 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  exact theta_pos hN

lemma KimLarge.beta_ge_one {N : ℕ} (h : KimLarge N) (k : ℕ) :
    1 ≤ kimBeta N k := by
  have hL := h.logn_ge_one
  have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  have hx : (1 : ℝ) ≤ 3 * ((k : ℝ) + 1) * Real.log N := by nlinarith [hL, hk]
  rw [kimBeta]
  have h1 : Real.sqrt 1 ≤ Real.sqrt (3 * ((k : ℝ) + 1) * Real.log N) :=
    Real.sqrt_le_sqrt hx
  simpa using h1

lemma KimLarge.thr7_ge_one {N : ℕ} (h : KimLarge N) (k : ℕ) :
    1 ≤ kimThr7 N k := by
  have hβ := h.beta_ge_one k
  have hN2 : 2 ≤ N := by
    have h8 : (8 : ℝ) < N := h.1
    have : (2 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have ht : 1 ≤ tParam N := tParam_pos hN2
  have htR : (1 : ℝ) ≤ ((tParam N : ℕ) : ℝ) := by exact_mod_cast ht
  have hs : (1 : ℝ) ≤ Real.sqrt ((tParam N : ℕ) : ℝ) := by
    have h1 : Real.sqrt 1 ≤ Real.sqrt ((tParam N : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt htR
    simpa using h1
  rw [kimThr7]
  nlinarith [hβ, hs]

/-- The unsquared form of the `b_min` clause. -/
lemma KimLarge.bmin1 {N : ℕ} (h : KimLarge N) :
    (N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 4
      ≤ Real.exp (-(kimDelta * Real.log N)
          - 2 * Real.sqrt (kimDelta * Real.log N) - 1)
        * theta N * Real.sqrt N := by
  have hcl := h.2.2.2.2.2.2.2.2.2.2.1
  have hE0 : (0 : ℝ) < Real.exp (-(kimDelta * Real.log N)
      - 2 * Real.sqrt (kimDelta * Real.log N) - 1) := Real.exp_pos _
  have hE1 : Real.exp (-(kimDelta * Real.log N)
      - 2 * Real.sqrt (kimDelta * Real.log N) - 1) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h1 : (0 : ℝ) ≤ kimDelta * Real.log N := by
      have := h.logn_ge_one
      nlinarith [kimDelta_pos.le]
    have h2 : (0 : ℝ) ≤ Real.sqrt (kimDelta * Real.log N) := Real.sqrt_nonneg _
    linarith
  have hθ0 : (0 : ℝ) ≤ theta N := theta_nonneg N
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hsq : (Real.exp (-(kimDelta * Real.log N)
        - 2 * Real.sqrt (kimDelta * Real.log N) - 1)) ^ 2
      ≤ Real.exp (-(kimDelta * Real.log N)
        - 2 * Real.sqrt (kimDelta * Real.log N) - 1) := by
    nlinarith [hE0.le, hE1]
  have hstep : (Real.exp (-(kimDelta * Real.log N)
        - 2 * Real.sqrt (kimDelta * Real.log N) - 1)) ^ 2
        * theta N * Real.sqrt N
      ≤ Real.exp (-(kimDelta * Real.log N)
        - 2 * Real.sqrt (kimDelta * Real.log N) - 1) * theta N * Real.sqrt N :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsq hθ0) hsq0
  linarith [hcl, hstep]

/-- `k ≤ n^δ(log n)²` for every `k ≤ k₀`. -/
lemma KimLarge.k_le {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    (k : ℝ) ≤ (N : ℝ) ^ kimDelta * (Real.log N) ^ 2 := by
  have hθpos : 0 < theta N := h.theta_pos'
  have hkR : (k : ℝ) ≤ (N : ℝ) ^ kimDelta / theta N := by
    refine le_trans ?_ (Nat.floor_le (by positivity))
    exact_mod_cast hk
  have hθ : theta N = 1 / (Real.log N) ^ 2 := by rw [theta]
  rw [hθ] at hkR
  have hL0 : (0 : ℝ) < (Real.log N) ^ 2 := by
    have := h.logn_ge_one; positivity
  rw [div_div_eq_mul_div, div_one] at hkR
  exact hkR

/-- `M = ⌊b(a+5θ)√n⌋ ≥ 5n^δ(log n)⁴ − 1`, uniformly over `k ≤ k₀`. -/
lemma KimLarge.kimM_ge {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    5 * ((N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 4) - 1
      ≤ (kimM N k : ℝ) := by
  have hN1 : 1 ≤ N := h.card_pos
  have hθpos : 0 < theta N := h.theta_pos'
  have hbmin := bSeq_ge_of_k_le hN1 hθpos hk
  have hcl := h.bmin1
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have ha0 : 0 ≤ aSeq N k := aSeq_nonneg N k
  have hb0 : (0 : ℝ) ≤ bSeq N k := (bSeq_pos N k).le
  have h1 : Real.exp (-(kimDelta * Real.log N)
        - 2 * Real.sqrt (kimDelta * Real.log N) - 1) * theta N * Real.sqrt N
      ≤ bSeq N k * theta N * Real.sqrt N :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbmin hθpos.le) hsq0
  have h2 : bSeq N k * (5 * theta N) * Real.sqrt N
      ≤ bSeq N k * (aSeq N k + 5 * theta N) * Real.sqrt N := by
    have hstep : bSeq N k * (5 * theta N)
        ≤ bSeq N k * (aSeq N k + 5 * theta N) :=
      mul_le_mul_of_nonneg_left (by linarith [ha0]) hb0
    exact mul_le_mul_of_nonneg_right hstep hsq0
  have hx : 5 * ((N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 4)
      ≤ bSeq N k * (aSeq N k + 5 * theta N) * Real.sqrt N := by
    linarith [hcl, h1, h2]
  have hfl := Nat.lt_floor_add_one
    (bSeq N k * (aSeq N k + 5 * theta N) * Real.sqrt N)
  rw [kimM]
  linarith [hx, hfl]

/-- `√n ≥ n^δ(log n)⁶`, a convenient repackaging of the `b_min` clause. -/
lemma KimLarge.sqrtN_ge {N : ℕ} (h : KimLarge N) :
    (N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 6 ≤ Real.sqrt (N : ℝ) := by
  have hcl := h.bmin1
  have hE1 : Real.exp (-(kimDelta * Real.log N)
      - 2 * Real.sqrt (kimDelta * Real.log N) - 1) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h1 : (0 : ℝ) ≤ kimDelta * Real.log N := by
      have := h.logn_ge_one
      nlinarith [kimDelta_pos.le]
    have h2 : (0 : ℝ) ≤ Real.sqrt (kimDelta * Real.log N) := Real.sqrt_nonneg _
    linarith
  have hθ : theta N = 1 / (Real.log N) ^ 2 := by rw [theta]
  have hL := h.logn_ge_one
  have hL2 : (0 : ℝ) < (Real.log N) ^ 2 := by positivity
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hθ0 : (0 : ℝ) ≤ theta N := theta_nonneg N
  have hstep : Real.exp (-(kimDelta * Real.log N)
        - 2 * Real.sqrt (kimDelta * Real.log N) - 1) * theta N * Real.sqrt N
      ≤ theta N * Real.sqrt N := by
    nlinarith [hE1, hθ0, hsq0, mul_nonneg hθ0 hsq0]
  have hcl2 : (N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 4
      ≤ theta N * Real.sqrt N := by linarith [hcl, hstep]
  rw [hθ] at hcl2
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hL2] at hcl2
  nlinarith [hcl2]

/-- `I ≤ 12n^δ(log n)³ + 5`. -/
lemma KimLarge.kimI_le_poly {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    ((kimI N k : ℕ) : ℝ)
      ≤ 12 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3) + 5 := by
  have hkle := h.k_le hk
  have hL := h.logn_ge_one
  have hceil := Nat.ceil_lt_add_one
    (show (0 : ℝ) ≤ 4 * (3 * (k : ℝ) * Real.log N + 1) by positivity)
  have hIR : ((kimI N k : ℕ) : ℝ) ≤ 4 * (3 * (k : ℝ) * Real.log N + 1) + 1 := by
    rw [kimI]; linarith [hceil]
  have hkL : 12 * (k : ℝ) * Real.log N
      ≤ 12 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3) := by
    have hstep : (k : ℝ) * Real.log N
        ≤ ((N : ℝ) ^ kimDelta * (Real.log N) ^ 2) * Real.log N :=
      mul_le_mul_of_nonneg_right hkle (by linarith)
    nlinarith [hstep]
  linarith [hIR, hkL]

/-- `2Ip ≤ 1`. -/
lemma KimLarge.kimI_p_le {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    2 * ((kimI N k : ℕ) : ℝ) * edgeProb N ≤ 1 := by
  have hI := h.kimI_le_poly hk
  have hs := h.sqrtN_ge
  have hL := h.logn_ge_one
  have hN1 : 1 ≤ N := h.card_pos
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hrp : (1 : ℝ) ≤ (N : ℝ) ^ kimDelta :=
    Real.one_le_rpow hNR kimDelta_pos.le
  have hLe : Real.exp 1 ≤ Real.log N := h.2.2.1
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hL2 : (2 : ℝ) ≤ Real.log N := by linarith
  have hsq0 : (0 : ℝ) < Real.sqrt (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := one_le_sqrt_cast hN1
    linarith
  have hLsq : (0 : ℝ) < (Real.log N) ^ 2 := by positivity
  -- reduce to `2I ≤ L²√N`
  have hkey : 2 * ((kimI N k : ℕ) : ℝ) ≤ (Real.log N) ^ 2 * Real.sqrt (N : ℝ) := by
    have hbig : (Real.log N) ^ 2 * ((N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 6)
        ≤ (Real.log N) ^ 2 * Real.sqrt (N : ℝ) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    have hL5 : (32 : ℝ) ≤ (Real.log N) ^ 5 := by
      have h1 : (2 : ℝ) ^ 5 ≤ (Real.log N) ^ 5 :=
        pow_le_pow_left₀ (by norm_num) hL2 5
      norm_num at h1; linarith
    have hL3 : (8 : ℝ) ≤ (Real.log N) ^ 3 := by
      have h1 : (2 : ℝ) ^ 3 ≤ (Real.log N) ^ 3 :=
        pow_le_pow_left₀ (by norm_num) hL2 3
      norm_num at h1; linarith
    have hδ14 : (N : ℝ) ^ kimDelta ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
      refine Real.rpow_le_rpow_of_exponent_le hNR ?_
      have := kimDelta_lt; norm_num at this ⊢; linarith
    have hXge : (8 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 3 := by
      nlinarith [hrp, hL3]
    have heq : (Real.log N) ^ 2 * ((N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 6)
        = ((N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 3)
          * (Real.log N) ^ 5 := by ring
    have hmono : 12 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3)
        ≤ 12 * ((N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 3) := by
      nlinarith [hδ14, hL3]
    have hdom : 2 * (12 * ((N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 3) + 5)
        ≤ (Real.log N) ^ 2 * ((N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 6) := by
      rw [heq]
      nlinarith [hXge, hL5]
    linarith [hI, hbig, hdom, hmono]
  rw [edgeProb, theta, div_div, mul_one_div, div_le_one (by positivity)]
  exact hkey

lemma bSeq_succ_le (N k : ℕ) (hθ : 0 < theta N) :
    bSeq N (k + 1) ≤ bSeq N k := by
  rw [bSeq_succ_eq_mul_exp]
  have hk0 : (0 : ℝ) ≤ (k : ℝ) * theta N := by positivity
  have hmono : spencerPsi ((k : ℝ) * theta N)
      ≤ spencerPsi (((k : ℝ) + 1) * theta N) := by
    refine spencerPsi_strictMono.monotone ?_
    nlinarith [hθ, Nat.cast_nonneg (α := ℝ) k]
  have hnn : 0 ≤ spencerPsi ((k : ℝ) * theta N) := spencerPsi_nonneg hk0
  have hsq : spencerPsi ((k : ℝ) * theta N) ^ 2
      ≤ spencerPsi (((k : ℝ) + 1) * theta N) ^ 2 := by
    nlinarith [hmono, hnn]
  have hexp : Real.exp (-(spencerPsi (((k : ℝ) + 1) * theta N) ^ 2
      - spencerPsi ((k : ℝ) * theta N) ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  nlinarith [hexp, (bSeq_pos N k).le]

/-- `log n ≥ 13`, from the last `KimLarge` clause. -/
lemma KimLarge.logn_big {N : ℕ} (h : KimLarge N) : 13 ≤ Real.log N := by
  have hcl := h.2.2.2.2.2.2.2.2.2.1
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h14 : Real.exp 1 ^ 14 ≤ Real.exp 14 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpow : (2.7182818283 : ℝ) ^ 14 ≤ Real.exp 1 ^ 14 :=
    pow_le_pow_left₀ (by norm_num) he.le 14
  have hbig : (100000 : ℝ) ≤ Real.exp 14 := by
    have : (100000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 14 := by norm_num
    linarith [hpow, h14]
  linarith [hcl, hbig]

/-- `log n ≥ 1000`, from the same clause. -/
lemma KimLarge.logn_large {N : ℕ} (h : KimLarge N) : 1000 ≤ Real.log N := by
  have hcl := h.2.2.2.2.2.2.2.2.2.1
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h14 : Real.exp 1 ^ 14 ≤ Real.exp 14 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpow : (2.7182818283 : ℝ) ^ 14 ≤ Real.exp 1 ^ 14 :=
    pow_le_pow_left₀ (by norm_num) he.le 14
  have hbig : (100000 : ℝ) ≤ Real.exp 14 := by
    have : (100000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 14 := by norm_num
    linarith [hpow, h14]
  linarith [hcl, hbig]

/-- `log n ≥ 10⁶`, from the same clause. -/
lemma KimLarge.logn_vast {N : ℕ} (h : KimLarge N) : 1000000 ≤ Real.log N := by
  have hcl := h.2.2.2.2.2.2.2.2.2.1
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h14 : Real.exp 1 ^ 14 ≤ Real.exp 14 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpow : (2.7182818283 : ℝ) ^ 14 ≤ Real.exp 1 ^ 14 :=
    pow_le_pow_left₀ (by norm_num) he.le 14
  have hbig : (1000000 : ℝ) ≤ Real.exp 14 := by
    have : (1000000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 14 := by norm_num
    linarith [hpow, h14]
  linarith [hcl, hbig]

/-- `bᵢ` is antitone in `i`. -/
lemma bSeq_antitone (N : ℕ) {i j : ℕ} (hij : i ≤ j) : bSeq N j ≤ bSeq N i := by
  have hθ0 := theta_nonneg N
  have hcast : ((i : ℝ)) * theta N ≤ ((j : ℝ)) * theta N := by
    have hij' : ((i : ℝ)) ≤ ((j : ℝ)) := by exact_mod_cast hij
    nlinarith [hθ0, hij']
  have hP0 : 0 ≤ spencerPsi ((i : ℝ) * theta N) :=
    spencerPsi_nonneg (mul_nonneg (Nat.cast_nonneg i) hθ0)
  have hmono : spencerPsi ((i : ℝ) * theta N) ≤ spencerPsi ((j : ℝ) * theta N) :=
    spencerPsi_strictMono.monotone hcast
  have hsq : (spencerPsi ((i : ℝ) * theta N)) ^ 2
      ≤ (spencerPsi ((j : ℝ) * theta N)) ^ 2 := by nlinarith [hmono, hP0]
  exact Real.exp_le_exp.mpr (by linarith)

/-- `k·b_k·θ ≤ a_k`, since `a_k = Σ_{j<k} b_jθ` and `b` is antitone. -/
lemma aSeq_ge_k_mul (N k : ℕ) :
    (k : ℝ) * bSeq N k * theta N ≤ aSeq N k := by
  have hθ0 := theta_nonneg N
  have hsum : ∑ _j ∈ Finset.range k, bSeq N k * theta N
      ≤ ∑ j ∈ Finset.range k, bSeq N j * theta N := by
    refine Finset.sum_le_sum fun j hj => ?_
    exact mul_le_mul_of_nonneg_right
      (bSeq_antitone N (le_of_lt (Finset.mem_range.mp hj))) hθ0
  rw [aSeq]
  refine le_trans (le_of_eq ?_) hsum
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- `a_k·b_k ≤ 2`.  The coupling that makes Kim's estimates work: `a_k ≈ Ψ(kθ)`
and `b_k = e^{−Ψ(kθ)²}`, so `a_kb_k ≈ Ψe^{−Ψ²} ≤ 1/√(2e)`.  Reading
`a_k ≈ √(δ log n)` and `b_k ≈ 1` at the same time is impossible. -/
lemma KimLarge.ab_le {N k : ℕ} (h : KimLarge N) :
    aSeq N k * bSeq N k ≤ 2 := by
  have hθ : theta N ≤ 1 / 100 := h.2.1
  have hθ0 := theta_nonneg N
  have hb0 := (bSeq_pos N k).le
  have hb1 := bSeq_le_one N k
  have hΨb := psi_mul_bSeq_le_one N k
  have haub : aSeq N k - spencerPsi ((k : ℝ) * theta N) ≤ theta N :=
    (aSeq_sub_spencerPsi_bounds N k).2
  nlinarith [hΨb, haub, hb0, hb1, hθ, hθ0]

/-- `(k+1)·b_k²·θ ≤ 3`, the form the §4.8 variance uses. -/
lemma KimLarge.k_bSq_theta_le {N k : ℕ} (h : KimLarge N) :
    ((k : ℝ) + 1) * bSeq N k ^ 2 * theta N ≤ 3 := by
  have hθ : theta N ≤ 1 / 100 := h.2.1
  have hθ0 := theta_nonneg N
  have hb0 := (bSeq_pos N k).le
  have hb1 := bSeq_le_one N k
  have hab := h.ab_le (k := k)
  have hkb := aSeq_ge_k_mul N k
  have hstep : (k : ℝ) * bSeq N k ^ 2 * theta N ≤ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hkb hb0
    nlinarith [h1, hab, hb0]
  nlinarith [hstep, hb0, hb1, hθ, hθ0]

/-- **`β·b² ≤ 3b·log n·√log n`.**  The `√(k+1)` in Kim's truncation threshold
is never large at the same time as `b`: `β²b⁴ = 3L·((k+1)b²θ)·b²/θ`. -/
lemma KimLarge.beta_bSq_le {N k : ℕ} (h : KimLarge N) :
    kimBeta N k * bSeq N k ^ 2
      ≤ 3 * bSeq N k * Real.log N * Real.sqrt (Real.log N) := by
  have hL0 : (0 : ℝ) < Real.log N := by linarith [h.logn_vast]
  have hb0 := (bSeq_pos N k).le
  have hβ0 := kimBeta_nonneg N k
  have hk3 := h.k_bSq_theta_le (k := k)
  have hθe : theta N = 1 / Real.log N ^ 2 := by rw [theta]
  have hsq : Real.sqrt (Real.log N) ^ 2 = Real.log N := Real.sq_sqrt hL0.le
  have hβsq := kimBeta_sq N k hL0.le
  have hlhs : (kimBeta N k * bSeq N k ^ 2) ^ 2
      ≤ (3 * bSeq N k * Real.log N * Real.sqrt (Real.log N)) ^ 2 := by
    have hR : (3 * bSeq N k * Real.log N * Real.sqrt (Real.log N)) ^ 2
        = 9 * bSeq N k ^ 2 * Real.log N ^ 3 := by
      rw [mul_pow, mul_pow, mul_pow, hsq]; ring
    have hLHS : (kimBeta N k * bSeq N k ^ 2) ^ 2
        = 3 * ((k : ℝ) + 1) * Real.log N * bSeq N k ^ 4 := by
      rw [mul_pow, hβsq]; ring
    rw [hR, hLHS]
    have hcoef : (0 : ℝ) ≤ 3 * Real.log N ^ 3 * bSeq N k ^ 2 := by positivity
    have hk3' : ((k : ℝ) + 1) * bSeq N k ^ 2 * (1 / Real.log N ^ 2) ≤ 3 := by
      rw [← hθe]; exact hk3
    have hmul := mul_le_mul_of_nonneg_left hk3' hcoef
    have hrw : 3 * Real.log N ^ 3 * bSeq N k ^ 2
          * (((k : ℝ) + 1) * bSeq N k ^ 2 * (1 / Real.log N ^ 2))
        = 3 * ((k : ℝ) + 1) * Real.log N * bSeq N k ^ 4 := by
      field_simp
      try ring
    linarith [hmul, hrw.le, hrw.ge]
  have hr0 : (0 : ℝ) ≤ 3 * bSeq N k * Real.log N * Real.sqrt (Real.log N) := by
    positivity
  nlinarith [hlhs, hr0, mul_nonneg hβ0 (sq_nonneg (bSeq N k))]

/-- `(log N)^j ≤ N^{1/8}` for every `j ≤ 20`. -/
lemma KimLarge.polylog {N : ℕ} (h : KimLarge N) {j : ℕ} (hj : j ≤ 20) :
    (Real.log N) ^ j ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
  have hcl := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hL := h.logn_ge_one
  exact le_trans (pow_le_pow_right₀ hL hj) hcl

/-- `(log N)^j ≤ N^r` for every `j ≤ 20` and `r ≥ 1/8`. -/
lemma KimLarge.polylog' {N : ℕ} (h : KimLarge N) {j : ℕ} (hj : j ≤ 20)
    {r : ℝ} (hr : (1 : ℝ) / 8 ≤ r) :
    (Real.log N) ^ j ≤ (N : ℝ) ^ r := by
  have hN1 : 1 ≤ N := h.card_pos
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  exact le_trans (h.polylog hj) (Real.rpow_le_rpow_of_exponent_le hNR hr)

/-- `M ≤ √(log N)·√N`, from `a_k ≤ √(δ log N) + 1 + θ` and `b_k ≤ 1`. -/
lemma KimLarge.kimM_le' {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    (kimM N k : ℝ) ≤ Real.sqrt (Real.log N) * Real.sqrt N := by
  have hN1 : 1 ≤ N := h.card_pos
  have hθpos := h.theta_pos'
  have hθ : theta N ≤ 1 / 100 := h.2.1
  have hL := h.logn_big
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hale := aSeq_le_of_k_le hN1 hθpos hk
  have hb := bSeq_le_one N k
  have hb0 := (bSeq_pos N k).le
  have ha0 := aSeq_nonneg N k
  -- `√(δ log N) ≤ √(log N)/4`
  have hdq : Real.sqrt (kimDelta * Real.log N) ≤ Real.sqrt (Real.log N) / 4 := by
    have h1 : kimDelta * Real.log N ≤ (Real.sqrt (Real.log N) / 4) ^ 2 := by
      have hsq : (Real.sqrt (Real.log N)) ^ 2 = Real.log N :=
        Real.sq_sqrt (by linarith)
      have : (Real.sqrt (Real.log N) / 4) ^ 2 = Real.log N / 16 := by
        rw [div_pow, hsq]; norm_num
      rw [this, kimDelta]
      nlinarith [hL]
    have h2 : (0 : ℝ) ≤ Real.sqrt (Real.log N) / 4 := by positivity
    calc Real.sqrt (kimDelta * Real.log N)
        ≤ Real.sqrt ((Real.sqrt (Real.log N) / 4) ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt (Real.log N) / 4 := Real.sqrt_sq h2
  -- `√(log N) ≥ 3`
  have hs3 : (3 : ℝ) ≤ Real.sqrt (Real.log N) := by
    have : Real.sqrt (9 : ℝ) ≤ Real.sqrt (Real.log N) :=
      Real.sqrt_le_sqrt (by linarith)
    have h9 : Real.sqrt (9 : ℝ) = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
    linarith [this, h9.le, h9.ge]
  have hsum : aSeq N k + 5 * theta N ≤ Real.sqrt (Real.log N) := by
    have := hale
    nlinarith [hdq, hs3, hθ, hθpos.le]
  have hstep : bSeq N k * (aSeq N k + 5 * theta N) * Real.sqrt N
      ≤ Real.sqrt (Real.log N) * Real.sqrt N := by
    have h1 : bSeq N k * (aSeq N k + 5 * theta N) ≤ Real.sqrt (Real.log N) := by
      nlinarith [hb, hb0, ha0, hθpos.le, hsum]
    exact mul_le_mul_of_nonneg_right h1 hsq0
  exact le_trans (kimM_le N k) hstep

/-- `a_k + 5θ ≤ √(log n)`. -/
lemma KimLarge.aSum_le {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    aSeq N k + 5 * theta N ≤ Real.sqrt (Real.log N) := by
  have hN1 : 1 ≤ N := h.card_pos
  have hθpos := h.theta_pos'
  have hθ : theta N ≤ 1 / 100 := h.2.1
  have hL := h.logn_big
  have hale := aSeq_le_of_k_le hN1 hθpos hk
  have hsq : (Real.sqrt (Real.log N)) ^ 2 = Real.log N :=
    Real.sq_sqrt (by linarith)
  have hdq : Real.sqrt (kimDelta * Real.log N)
      ≤ Real.sqrt (Real.log N) / 4 := by
    have h1 : kimDelta * Real.log N ≤ (Real.sqrt (Real.log N) / 4) ^ 2 := by
      have he : (Real.sqrt (Real.log N) / 4) ^ 2 = Real.log N / 16 := by
        rw [div_pow, hsq]; norm_num
      rw [he, kimDelta]
      nlinarith [hL]
    calc Real.sqrt (kimDelta * Real.log N)
        ≤ Real.sqrt ((Real.sqrt (Real.log N) / 4) ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt (Real.log N) / 4 := Real.sqrt_sq (by positivity)
  have hs3 : (3 : ℝ) ≤ Real.sqrt (Real.log N) := by
    have h1 : Real.sqrt (9 : ℝ) ≤ Real.sqrt (Real.log N) :=
      Real.sqrt_le_sqrt (by linarith)
    have h9 : Real.sqrt (9 : ℝ) = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
    linarith [h1, h9.le, h9.ge]
  nlinarith [hale, hdq, hs3, hθ, hθpos.le]

/-- `M ≤ b_k·√(log n)·√n`, the `b`-keeping form of `kimM_le'`. -/
lemma KimLarge.kimM_le_b {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    (kimM N k : ℝ) ≤ bSeq N k * Real.sqrt (Real.log N) * Real.sqrt N := by
  have hsum := h.aSum_le hk
  have hb0 := (bSeq_pos N k).le
  have hs0 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  refine le_trans (kimM_le N k) ?_
  have h1 : bSeq N k * (aSeq N k + 5 * theta N)
      ≤ bSeq N k * Real.sqrt (Real.log N) :=
    mul_le_mul_of_nonneg_left hsum hb0
  exact mul_le_mul_of_nonneg_right h1 hs0


/-- `I ≤ b_k θ √N`, the size comparison behind §4.6's `2Ipb'² ≤ 2b³θ²`. -/
lemma KimLarge.kimI_le_bmin {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    ((kimI N k : ℕ) : ℝ) ≤ bSeq N k * theta N * Real.sqrt N := by
  have hN1 : 1 ≤ N := h.card_pos
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hθpos := h.theta_pos'
  have hsq0 : (0 : ℝ) < Real.sqrt (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := one_le_sqrt_cast hN1
    linarith
  have hI := h.kimI_le_poly hk
  have hbmin1 := h.bmin1
  have hbmin := bSeq_ge_of_k_le hN1 hθpos hk
  have hbig : (N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 4
      ≤ bSeq N k * theta N * Real.sqrt N := by
    refine le_trans hbmin1 ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbmin hθpos.le) hsq0.le
  have hL := h.logn_big
  have hδq : (N : ℝ) ^ kimDelta ≤ (N : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le hNR (by rw [kimDelta]; norm_num)
  have hq1 : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.one_le_rpow hNR (by norm_num)
  have hL3 : (2197 : ℝ) ≤ (Real.log N) ^ 3 := by
    have h1 : (13 : ℝ) ^ 3 ≤ (Real.log N) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hL 3
    norm_num at h1; linarith
  have hL0 : (0 : ℝ) ≤ (Real.log N) ^ 3 := by linarith
  -- `12 n^δ L³ + 5 ≤ n^{1/4} L⁴`
  have hstep : 12 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3) + 5
      ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 4 := by
    have h1 : (N : ℝ) ^ kimDelta * (Real.log N) ^ 3
        ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 3 :=
      mul_le_mul_of_nonneg_right hδq hL0
    have h2 : (13 : ℝ) * ((N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 3)
        ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 4 := by
      have : (13 : ℝ) * (Real.log N) ^ 3 ≤ Real.log N * (Real.log N) ^ 3 :=
        mul_le_mul_of_nonneg_right hL hL0
      nlinarith [this, hq1]
    have h3 : (5 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 3 := by
      nlinarith [hq1, hL3]
    linarith
  linarith [hI, hstep, hbig]

/-- `2Ipb'² ≤ 2b³θ²`, §4.6's variance side-condition. -/
lemma KimLarge.kimI_bb_le {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    2 * ((kimI N k : ℕ) : ℝ) * edgeProb N * bSeq N (k + 1) ^ 2
      ≤ 2 * bSeq N k ^ 3 * theta N ^ 2 := by
  have hN1 : 1 ≤ N := h.card_pos
  have hθpos := h.theta_pos'
  have hsq0 : (0 : ℝ) < Real.sqrt (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := one_le_sqrt_cast hN1
    linarith
  have hmain := h.kimI_le_bmin hk
  have hb0 := (bSeq_pos N k).le
  have hb'0 := (bSeq_pos N (k + 1)).le
  have hbb := bSeq_succ_le N k hθpos
  have hsq : bSeq N (k + 1) ^ 2 ≤ bSeq N k ^ 2 := pow_le_pow_left₀ hb'0 hbb 2
  have hI0 : (0 : ℝ) ≤ ((kimI N k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hp0 : (0 : ℝ) ≤ edgeProb N := by
    rw [edgeProb]; positivity
  -- `Ip ≤ b θ²`
  have hIp : ((kimI N k : ℕ) : ℝ) * edgeProb N ≤ bSeq N k * theta N ^ 2 := by
    rw [edgeProb, mul_div_assoc', div_le_iff₀ hsq0]
    nlinarith [hmain, hθpos, hsq0]
  calc 2 * ((kimI N k : ℕ) : ℝ) * edgeProb N * bSeq N (k + 1) ^ 2
      ≤ 2 * ((kimI N k : ℕ) : ℝ) * edgeProb N * bSeq N k ^ 2 := by
        refine mul_le_mul_of_nonneg_left hsq ?_
        positivity
    _ ≤ 2 * bSeq N k ^ 3 * theta N ^ 2 := by
        have := mul_le_mul_of_nonneg_left hIp
          (show (0 : ℝ) ≤ 2 * bSeq N k ^ 2 by positivity)
        nlinarith [this]

/-- With `R := N^{1/4}`: `R⁴ = N`, `R² = √N`, and `ρ₂ = R⁻³`. -/
lemma quarter_pow_facts {N : ℕ} (hN : 0 < N) :
    (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 4)
      ∧ ((N : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = (N : ℝ)
      ∧ ((N : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt N
      ∧ kimRho2 N * ((N : ℝ) ^ ((1 : ℝ) / 4)) ^ 3 = 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨Real.rpow_pos_of_pos hNpos _, ?_, ?_, ?_⟩
  · rw [← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 4)) 4,
      ← Real.rpow_mul hNpos.le]
    norm_num
  · rw [← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 4)) 2,
      ← Real.rpow_mul hNpos.le, Real.sqrt_eq_rpow]
    norm_num
  · rw [kimRho2, ← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 4)) 3,
      ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
    norm_num

/-- `N^{1/4} = exp((log N)/4)`. -/
lemma rpow_quarter_eq_exp {N : ℕ} (hN : 0 < N) :
    (N : ℝ) ^ ((1 : ℝ) / 4) = Real.exp (Real.log N / 4) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_def_of_pos hNpos]
  congr 1
  ring

lemma exp_sq (a : ℝ) : (Real.exp a) ^ 2 = Real.exp (2 * a) := by
  rw [two_mul, Real.exp_add]; ring

/-- `b_k² ≥ exp(−2δL − 4√L − 2)`, the uniform lower bound on the squared
block density in the form the exponent estimates are stated in. -/
lemma KimLarge.bSq_ge {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    Real.exp (-(2 * kimDelta * Real.log N)
        - 4 * Real.sqrt (Real.log N) - 2) ≤ bSeq N k ^ 2 := by
  have hn : 0 < N := h.card_pos
  have hL : (13 : ℝ) ≤ Real.log N := h.logn_big
  have hbmin := bSeq_ge_of_k_le hn h.theta_pos' hk
  have hE0 : (0 : ℝ) < Real.exp (-(kimDelta * Real.log N)
      - 2 * Real.sqrt (kimDelta * Real.log N) - 1) := Real.exp_pos _
  have hsqle : Real.sqrt (kimDelta * Real.log N) ≤ Real.sqrt (Real.log N) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith [kimDelta_lt, kimDelta_pos, hL]
  refine le_trans ?_ (pow_le_pow_left₀ hE0.le hbmin 2)
  rw [exp_sq]
  refine Real.exp_le_exp.mpr ?_
  linarith [hsqle]

/-- The pure arithmetic behind §4.4's exponent condition, with `R = n^{1/4}`,
`L = log n`, `ρ = R⁻³`, `p = L⁻²R⁻²`. -/
lemma hexp_p2_core {R L b M p ρ E : ℝ}
    (hR0 : 0 < R) (hL : 13 ≤ L) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hM0 : 0 ≤ M)
    (hE0 : 0 < E) (hLR : L ≤ R)
    (hρ : ρ = 1 / R ^ 3) (hp : p = 1 / (L ^ 2 * R ^ 2))
    (hMle : M ≤ Real.sqrt L * R ^ 2) (hEb : E ≤ b ^ 2)
    (hasym : 3 * L + Real.exp 1 / 2 ≤ R * E / L ^ 4) :
    3 * L ≤ ρ * (b ^ 2 * (1 / L ^ 2) ^ 2 * R ^ 4)
      - ρ ^ 2 / 2 * (p * ((2 * M) * (2 * M * (b * R ^ 4))
          * Real.exp (ρ * (2 * M)))) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hsL : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hsL0 : (0 : ℝ) ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hMsq : M ^ 2 ≤ L * R ^ 4 := by
    have h1 : M ^ 2 ≤ (Real.sqrt L * R ^ 2) ^ 2 := pow_le_pow_left₀ hM0 hMle 2
    nlinarith [h1, hsL]
  -- Term 1
  have ht1 : ρ * (b ^ 2 * (1 / L ^ 2) ^ 2 * R ^ 4) = R * b ^ 2 / L ^ 4 := by
    rw [hρ]; field_simp
  have ht1' : R * E / L ^ 4 ≤ R * b ^ 2 / L ^ 4 := by
    have h1 : R * E ≤ R * b ^ 2 := mul_le_mul_of_nonneg_left hEb hR0.le
    have h2 : (0 : ℝ) < L ^ 4 := by positivity
    exact div_le_div_of_nonneg_right h1 h2.le
  -- Term 2
  have hρ2M : ρ * (2 * M) ≤ 1 := by
    rw [hρ, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    have h2s : 2 * Real.sqrt L ≤ L := by nlinarith [hsL, hsL0, hL]
    have hfin : 2 * (Real.sqrt L * R ^ 2) ≤ R ^ 3 := by
      nlinarith [h2s, hLR, hR0, hL0]
    linarith [hMle, hfin]
  have hexpb : Real.exp (ρ * (2 * M)) ≤ Real.exp 1 := Real.exp_le_exp.mpr hρ2M
  have hexp0 : (0 : ℝ) < Real.exp (ρ * (2 * M)) := Real.exp_pos _
  have key : ρ ^ 2 / 2 * (p * ((2 * M) * (2 * M * (b * R ^ 4))
        * Real.exp (ρ * (2 * M))))
      = 2 * M ^ 2 * b * Real.exp (ρ * (2 * M)) / (L ^ 2 * R ^ 4) := by
    rw [hρ, hp]; field_simp
  have ht2 : ρ ^ 2 / 2 * (p * ((2 * M) * (2 * M * (b * R ^ 4))
        * Real.exp (ρ * (2 * M))))
      ≤ Real.exp 1 / 2 := by
    rw [key, div_le_iff₀ (by positivity : (0 : ℝ) < L ^ 2 * R ^ 4)]
    have hstep1 : 2 * M ^ 2 * b * Real.exp (ρ * (2 * M))
        ≤ 2 * (L * R ^ 4) * Real.exp 1 := by
      have hA : 2 * M ^ 2 * b ≤ 2 * (L * R ^ 4) := by
        nlinarith [hMsq, hb0, hb1, sq_nonneg M]
      have hA0 : (0 : ℝ) ≤ 2 * M ^ 2 * b := by positivity
      calc 2 * M ^ 2 * b * Real.exp (ρ * (2 * M))
          ≤ (2 * M ^ 2 * b) * Real.exp 1 :=
            mul_le_mul_of_nonneg_left hexpb hA0
        _ ≤ (2 * (L * R ^ 4)) * Real.exp 1 :=
            mul_le_mul_of_nonneg_right hA (Real.exp_pos 1).le
    have hstep2 : 2 * (L * R ^ 4) * Real.exp 1
        ≤ Real.exp 1 / 2 * (L ^ 2 * R ^ 4) := by
      have hR4 : (0 : ℝ) < R ^ 4 := by positivity
      have hfac : (0 : ℝ) ≤ Real.exp 1 * (L * R ^ 4) * (L / 2 - 2) :=
        mul_nonneg (mul_nonneg (Real.exp_pos 1).le
          (mul_nonneg hL0.le hR4.le)) (by linarith)
      linarith [hfac]
    linarith
  linarith [hasym, ht1, ht1', ht2]

/-- **Kim's §4.4 exponent condition**, at the tilt `ρ₂ = n^{−3/4}`. -/
lemma KimLarge.hexp_p2 {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    3 * Real.log N
      ≤ kimRho2 N * (bSeq N k ^ 2 * theta N ^ 2 * N)
        - kimRho2 N ^ 2 / 2 * (edgeProb N * ((2 * (kimM N k : ℝ))
            * (2 * (kimM N k : ℝ) * (bSeq N k * N))
            * Real.exp (kimRho2 N * (2 * (kimM N k : ℝ))))) := by
  have hn : 0 < N := h.card_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hn
  have hL : (13 : ℝ) ≤ Real.log N := h.logn_big
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hasym := h.asym.p2_exp
  have hbsq := h.bSq_ge hk
  have hMle0 := h.kimM_le' hk
  have hLR0 : (Real.log N) ^ 1 ≤ (N : ℝ) ^ ((1 : ℝ) / 4) :=
    h.polylog' (by norm_num) (by norm_num)
  have hRexp0 := rpow_quarter_eq_exp hn
  obtain ⟨hR0, hR4, hR2, hρR⟩ := quarter_pow_facts hn
  have hRne : ((N : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 := ne_of_gt hR0
  have hLne : Real.log N ≠ 0 := ne_of_gt hL0
  have hρeq : kimRho2 N = 1 / ((N : ℝ) ^ ((1 : ℝ) / 4)) ^ 3 := by
    rw [_root_.eq_div_iff (by positivity)]; exact hρR
  have hpeq : edgeProb N
      = 1 / ((Real.log N) ^ 2 * ((N : ℝ) ^ ((1 : ℝ) / 4)) ^ 2) := by
    rw [edgeProb, theta, hR2]
    have hsq0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
    field_simp
  have hθsq : theta N ^ 2 = (1 / (Real.log N) ^ 2) ^ 2 := by rw [theta]
  have hasym' : 3 * Real.log N + Real.exp 1 / 2
      ≤ (N : ℝ) ^ ((1 : ℝ) / 4)
        * Real.exp (-(2 * kimDelta * Real.log N)
            - 4 * Real.sqrt (Real.log N) - 2) / (Real.log N) ^ 4 := by
    refine le_trans hasym (le_of_eq ?_)
    rw [hRexp0, ← Real.exp_add]
    congr 2
    ring
  have hcore := hexp_p2_core (R := (N : ℝ) ^ ((1 : ℝ) / 4))
    (L := Real.log N) (b := bSeq N k) (M := (kimM N k : ℝ))
    (p := edgeProb N) (ρ := kimRho2 N)
    (E := Real.exp (-(2 * kimDelta * Real.log N)
      - 4 * Real.sqrt (Real.log N) - 2))
    hR0 hL (bSeq_pos N k).le (bSeq_le_one N k) (Nat.cast_nonneg _)
    (Real.exp_pos _) (by simpa using hLR0) hρeq hpeq
    (by rw [hR2]; exact hMle0) hbsq hasym'
  rw [← hθsq, hR4] at hcore
  exact hcore

/-- `b_k³ ≥ exp(−3δL − 6√L − 3)`. -/
lemma KimLarge.bCube_ge {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    Real.exp (-(3 * kimDelta * Real.log N)
        - 6 * Real.sqrt (Real.log N) - 3) ≤ bSeq N k ^ 3 := by
  have hn : 0 < N := h.card_pos
  have hL : (13 : ℝ) ≤ Real.log N := h.logn_big
  have hbmin := bSeq_ge_of_k_le hn h.theta_pos' hk
  have hE0 : (0 : ℝ) < Real.exp (-(kimDelta * Real.log N)
      - 2 * Real.sqrt (kimDelta * Real.log N) - 1) := Real.exp_pos _
  have hsqle : Real.sqrt (kimDelta * Real.log N) ≤ Real.sqrt (Real.log N) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith [kimDelta_lt, kimDelta_pos, hL]
  refine le_trans ?_ (pow_le_pow_left₀ hE0.le hbmin 3)
  have hcube : ∀ a : ℝ, (Real.exp a) ^ 3 = Real.exp (3 * a) := by
    intro a
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, add_mul, add_mul, one_mul,
      Real.exp_add, Real.exp_add]
    ring
  rw [hcube]
  refine Real.exp_le_exp.mpr ?_
  linarith [hsqle]

/-- With `R := n^{1/8}`: `R⁸ = n`, `R⁴ = √n`, and `ρ₅ = R⁻⁵`. -/
lemma eighth_pow_facts {N : ℕ} (hN : 0 < N) :
    (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8)
      ∧ ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 8 = (N : ℝ)
      ∧ ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 4 = Real.sqrt N
      ∧ kimRho5 N * ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 5 = 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨Real.rpow_pos_of_pos hNpos _, ?_, ?_, ?_⟩
  · rw [← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 8)) 8,
      ← Real.rpow_mul hNpos.le]
    norm_num
  · rw [← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 8)) 4,
      ← Real.rpow_mul hNpos.le, Real.sqrt_eq_rpow]
    norm_num
  · rw [kimRho5, ← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 8)) 5,
      ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
    norm_num

/-- `n^{3/8} = exp(3(log n)/8)`. -/
lemma rpow_eighth_cube_eq_exp {N : ℕ} (hN : 0 < N) :
    ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 3 = Real.exp (3 * Real.log N / 8) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 8)) 3,
    ← Real.rpow_mul hNpos.le, Real.rpow_def_of_pos hNpos]
  congr 1
  push_cast
  ring

set_option maxHeartbeats 1000000 in
/-- The pure arithmetic behind §4.6's exponent condition, at Kim's
`ρ₅ = n^{−5/8} = R⁻⁵` with `R = n^{1/8}`. -/
lemma hexp_p5_core {R L b M p ρ E : ℝ}
    (hR0 : 0 < R) (hL : 1000 ≤ L) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hM0 : 0 ≤ M)
    (hE0 : 0 < E) (hRL : 36 * L ^ 3 ≤ R)
    (hρ : ρ = 1 / R ^ 5) (hp : p = 1 / (L ^ 2 * R ^ 4))
    (hMle : M ≤ b * Real.sqrt L * R ^ 4) (hEb : E ≤ b ^ 3)
    (hasym : 6 * L ≤ R ^ 3 * E / L ^ 4) :
    3 * L ≤ ρ * (b ^ 3 * (1 / L ^ 2) ^ 2 * R ^ 8)
      - ρ ^ 2 / 2 * (p * ((2 * M + 4) * (4 * M * (b ^ 2 * R ^ 8))
          * Real.exp (ρ * (2 * M + 4)))) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hsL0 : (0 : ℝ) ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hsL3 : (30 : ℝ) ≤ Real.sqrt L := by nlinarith [hsq, hsL0, hL]
  have hsLL : Real.sqrt L ≤ L := by nlinarith [hsq, hsL0, hL0]
  have hRbig : 36 * L ^ 3 ≤ R := hRL
  have hR1 : (1 : ℝ) ≤ R := by nlinarith [hRbig, hL0, hL]
  have hR4 : (1 : ℝ) ≤ R ^ 4 := one_le_pow₀ hR1
  -- term 1
  have ht1 : ρ * (b ^ 3 * (1 / L ^ 2) ^ 2 * R ^ 8) = R ^ 3 * b ^ 3 / L ^ 4 := by
    rw [hρ]; field_simp; try ring
  have ht1' : R ^ 3 * E / L ^ 4 ≤ R ^ 3 * b ^ 3 / L ^ 4 :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hEb (by positivity)) (by positivity)
  -- Lipschitz constant
  have hc : 2 * M + 4 ≤ 3 * (Real.sqrt L * R ^ 4) := by
    nlinarith [hMle, hsL3, hR4, hb0, hb1, hsL0]
  have hc0 : (0 : ℝ) ≤ 2 * M + 4 := by linarith
  have hρc : ρ * (2 * M + 4) ≤ 1 := by
    rw [hρ, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    have h3s : 3 * Real.sqrt L ≤ R := by nlinarith [hRbig, hsLL, hL0, hL]
    nlinarith [hc, h3s, hR4, hsL0, hR0]
  have hexpb : Real.exp (ρ * (2 * M + 4)) ≤ 3 := by
    have h1 : Real.exp (ρ * (2 * M + 4)) ≤ Real.exp 1 := Real.exp_le_exp.mpr hρc
    have h2 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  have hexp0 : (0 : ℝ) < Real.exp (ρ * (2 * M + 4)) := Real.exp_pos _
  -- term 2
  have hprod : (2 * M + 4) * (4 * M * (b ^ 2 * R ^ 8)) ≤ 12 * b ^ 3 * L * R ^ 16 := by
    have hMb : 4 * M * (b ^ 2 * R ^ 8) ≤ 4 * (b * Real.sqrt L * R ^ 4) * (b ^ 2 * R ^ 8) := by
      have hb20 : (0 : ℝ) ≤ b ^ 2 * R ^ 8 := by positivity
      nlinarith [hMle, hb20]
    have hnn : (0 : ℝ) ≤ 4 * (b * Real.sqrt L * R ^ 4) * (b ^ 2 * R ^ 8) := by
      positivity
    calc (2 * M + 4) * (4 * M * (b ^ 2 * R ^ 8))
        ≤ (2 * M + 4) * (4 * (b * Real.sqrt L * R ^ 4) * (b ^ 2 * R ^ 8)) :=
          mul_le_mul_of_nonneg_left hMb hc0
      _ ≤ (3 * (Real.sqrt L * R ^ 4))
            * (4 * (b * Real.sqrt L * R ^ 4) * (b ^ 2 * R ^ 8)) :=
          mul_le_mul_of_nonneg_right hc hnn
      _ = 12 * b ^ 3 * L * R ^ 16 := by
          linear_combination (12 * b ^ 3 * R ^ 16) * hsq
  have hprod0 : (0 : ℝ) ≤ (2 * M + 4) * (4 * M * (b ^ 2 * R ^ 8)) := by
    have : (0 : ℝ) ≤ 4 * M * (b ^ 2 * R ^ 8) := by positivity
    exact mul_nonneg hc0 this
  have hp0 : (0 : ℝ) ≤ p := by rw [hp]; positivity
  have hρ20 : (0 : ℝ) ≤ ρ ^ 2 / 2 := by positivity
  have hstep : (2 * M + 4) * (4 * M * (b ^ 2 * R ^ 8))
        * Real.exp (ρ * (2 * M + 4))
      ≤ 12 * b ^ 3 * L * R ^ 16 * 3 := by
    calc (2 * M + 4) * (4 * M * (b ^ 2 * R ^ 8)) * Real.exp (ρ * (2 * M + 4))
        ≤ (2 * M + 4) * (4 * M * (b ^ 2 * R ^ 8)) * 3 :=
          mul_le_mul_of_nonneg_left hexpb hprod0
      _ ≤ 12 * b ^ 3 * L * R ^ 16 * 3 :=
          mul_le_mul_of_nonneg_right hprod (by norm_num)
  have hchain := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hstep hp0) hρ20
  have heq : ρ ^ 2 / 2 * (p * (12 * b ^ 3 * L * R ^ 16 * 3))
      = 18 * b ^ 3 * R ^ 2 / L := by
    rw [hρ, hp]; field_simp; try ring
  -- variance ≤ half the drift
  have hhalf : 18 * b ^ 3 * R ^ 2 / L ≤ (R ^ 3 * b ^ 3 / L ^ 4) / 2 := by
    rw [div_le_div_iff₀ hL0 (by positivity : (0 : ℝ) < 2)]
    have hb30 : (0 : ℝ) ≤ b ^ 3 := by positivity
    have hR20 : (0 : ℝ) < R ^ 2 := by positivity
    have hkey : 36 * L ^ 3 * (b ^ 3 * R ^ 2) ≤ R * (b ^ 3 * R ^ 2) :=
      mul_le_mul_of_nonneg_right hRbig (by positivity)
    have hL40 : (0 : ℝ) < L ^ 4 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hL40]
    nlinarith [hkey, hb30, hR20, hL0]
  linarith [hasym, ht1, ht1', hchain, heq.le, heq.ge, hhalf]

set_option maxHeartbeats 1000000 in
/-- **Kim's §4.6 exponent condition**, at his tilt `ρ₅ = n^{−5/8}`. -/
lemma KimLarge.hexp_p5 {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    3 * Real.log N
      ≤ kimRho5 N * (bSeq N k ^ 3 * theta N ^ 2 * N)
        - kimRho5 N ^ 2 / 2 * (edgeProb N * ((2 * (kimM N k : ℝ) + 4)
            * (4 * (kimM N k : ℝ) * (bSeq N k ^ 2 * (N : ℝ)))
            * Real.exp (kimRho5 N * (2 * (kimM N k : ℝ) + 4)))) := by
  have hn : 0 < N := h.card_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hn
  have hL := h.logn_big
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hasym := h.asym.p5_exp
  have hbc := h.bCube_ge hk
  have hMle0 := h.kimM_le_b hk
  obtain ⟨hR0, hR8, hR4, hρR⟩ := eighth_pow_facts hn
  have hRcube := rpow_eighth_cube_eq_exp hn
  have hρeq : kimRho5 N = 1 / ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 5 := by
    rw [_root_.eq_div_iff (by positivity)]; exact hρR
  have hpeq : edgeProb N
      = 1 / ((Real.log N) ^ 2 * ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 4) := by
    rw [edgeProb, theta, hR4]
    have hsq0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
    field_simp
  have hθsq : theta N ^ 2 = (1 / (Real.log N) ^ 2) ^ 2 := by rw [theta]
  -- `36 L³ ≤ n^{1/8}`
  have hRL : 36 * (Real.log N) ^ 3 ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
    have hp4 := h.polylog (j := 4) (by norm_num)
    have hLv := h.logn_vast
    nlinarith [hp4, hLv, hL0, pow_nonneg hL0.le 3]
  have hasym' : 6 * Real.log N
      ≤ ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 3
        * Real.exp (-(3 * kimDelta * Real.log N)
            - 6 * Real.sqrt (Real.log N) - 3) / (Real.log N) ^ 4 := by
    refine le_trans hasym (le_of_eq ?_)
    rw [hRcube, ← Real.exp_add]
    congr 2
    ring
  have hcore := hexp_p5_core (R := (N : ℝ) ^ ((1 : ℝ) / 8))
    (L := Real.log N) (b := bSeq N k) (M := (kimM N k : ℝ))
    (p := edgeProb N) (ρ := kimRho5 N)
    (E := Real.exp (-(3 * kimDelta * Real.log N)
      - 6 * Real.sqrt (Real.log N) - 3))
    hR0 (by linarith [h.logn_vast] : (1000 : ℝ) ≤ Real.log N)
    (bSeq_pos N k).le (bSeq_le_one N k) (Nat.cast_nonneg _)
    (Real.exp_pos _) hRL hρeq hpeq (by rw [hR4]; exact hMle0) hbc hasym'
  rw [← hθsq, hR8] at hcore
  exact hcore

/-- `√n = exp((log n)/2)`. -/
lemma sqrtN_eq_exp {N : ℕ} (hN : 0 < N) :
    Real.sqrt N = Real.exp (Real.log N / 2) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNpos]
  congr 1
  ring

/-- `27n^δ(log n)³ ≤ e^{(1/2−2δ)L−4√L−2}/L⁴`, the `n^δ`-shift of the clause. -/
lemma KimLarge.mcutlow_shift {N : ℕ} (h : KimLarge N) :
    27 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3)
      ≤ Real.exp (((1 : ℝ) / 2 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2) / (Real.log N) ^ 4 := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hL := h.logn_big
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log N := by linarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Real.log N) := Real.sqrt_nonneg _
  have hcl := h.asym.p7_mcutlow
  have hδ : (N : ℝ) ^ kimDelta = Real.exp (kimDelta * Real.log N) := by
    rw [Real.rpow_def_of_pos hNR]; ring_nf
  have hE0 : (0 : ℝ) < Real.exp (kimDelta * Real.log N) := Real.exp_pos _
  -- weaken the exponent from `(1/2−5δ)L−8√L−4` to `(1/2−3δ)L−4√L−2`
  have hweak : Real.exp (((1 : ℝ) / 2 - 5 * kimDelta) * Real.log N
        - 8 * Real.sqrt (Real.log N) - 4)
      ≤ Real.exp (((1 : ℝ) / 2 - 3 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [kimDelta_pos, hL0, hs0]
  have hcl' : 960 * (Real.log N) ^ 14
      ≤ Real.exp (((1 : ℝ) / 2 - 3 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2) := by linarith [hcl, hweak]
  have hmul := mul_le_mul_of_nonneg_right hcl' hE0.le
  have hsplit : Real.exp (((1 : ℝ) / 2 - 3 * kimDelta) * Real.log N
        - 4 * Real.sqrt (Real.log N) - 2) * Real.exp (kimDelta * Real.log N)
      = Real.exp (((1 : ℝ) / 2 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hδ, le_div_iff₀ (by positivity : (0 : ℝ) < (Real.log N) ^ 4)]
  have hpow : (Real.log N) ^ 7 ≤ (Real.log N) ^ 14 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  have hstep : 27 * (Real.exp (kimDelta * Real.log N) * (Real.log N) ^ 3)
        * (Real.log N) ^ 4
      ≤ 960 * (Real.log N) ^ 14 * Real.exp (kimDelta * Real.log N) := by
    have hrw : 27 * (Real.exp (kimDelta * Real.log N) * (Real.log N) ^ 3)
          * (Real.log N) ^ 4
        = 27 * (Real.log N) ^ 7 * Real.exp (kimDelta * Real.log N) := by ring
    rw [hrw]
    have := mul_le_mul_of_nonneg_right hpow hE0.le
    nlinarith [this, hE0, pow_pos hL0 7, pow_pos hL0 14]
  linarith [hstep, hmul, hsplit.le, hsplit.ge]

/-- **`θ²b_{k₀}²√n ≥ 27n^δ(log n)³`**, from `b_{k₀}² ≥ e^{−2δL−4√L−2}`. -/
lemma KimLarge.mcutR_ge {N : ℕ} (h : KimLarge N) :
    27 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3) ≤ mcutR N := by
  have hn := h.card_pos
  have hL := h.logn_big
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hcl : 27 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3)
      ≤ Real.exp (((1 : ℝ) / 2 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2) / (Real.log N) ^ 4 :=
    h.mcutlow_shift
  have hbsq := h.bSq_ge (k := ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) le_rfl
  have hsN := sqrtN_eq_exp hn
  have hθe : theta N ^ 2 = 1 / (Real.log N) ^ 4 := by rw [theta]; field_simp
  have hL4 : (0 : ℝ) < (Real.log N) ^ 4 := by positivity
  have hcomb : Real.exp (-(2 * kimDelta * Real.log N)
        - 4 * Real.sqrt (Real.log N) - 2) * Real.exp (Real.log N / 2)
      = Real.exp (((1 : ℝ) / 2 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hS0 : (0 : ℝ) < Real.exp (Real.log N / 2) := Real.exp_pos _
  have hstep : Real.exp (-(2 * kimDelta * Real.log N)
        - 4 * Real.sqrt (Real.log N) - 2) * Real.exp (Real.log N / 2)
      ≤ bSeq N ⌊(N : ℝ) ^ kimDelta / theta N⌋₊ ^ 2 * Real.exp (Real.log N / 2) :=
    mul_le_mul_of_nonneg_right hbsq hS0.le
  have hgoal : mcutR N
      = bSeq N ⌊(N : ℝ) ^ kimDelta / theta N⌋₊ ^ 2 * Real.exp (Real.log N / 2)
        / (Real.log N) ^ 4 := by
    rw [mcutR, hsN, hθe]; field_simp; try ring
  rw [hgoal]
  have hdiv : Real.exp (((1 : ℝ) / 2 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2) / (Real.log N) ^ 4
      ≤ bSeq N ⌊(N : ℝ) ^ kimDelta / theta N⌋₊ ^ 2
          * Real.exp (Real.log N / 2) / (Real.log N) ^ 4 := by
    rw [← hcomb]
    exact div_le_div_of_nonneg_right hstep hL4.le
  linarith [hcl, hdiv]

lemma KimLarge.mcut_pos {N : ℕ} (h : KimLarge N) : 1 ≤ mcut N := by
  have hge := h.mcutR_ge
  have hN : 1 ≤ N := h.card_pos
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hδ : (1 : ℝ) ≤ (N : ℝ) ^ kimDelta :=
    Real.one_le_rpow hNR kimDelta_pos.le
  have hL := h.logn_ge_one
  have hL3 : (1 : ℝ) ≤ (Real.log N) ^ 3 := one_le_pow₀ hL
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ kimDelta * (Real.log N) ^ 3 := by
    nlinarith [hδ, hL3]
  have h27 : (1 : ℝ) ≤ mcutR N := by linarith [hge, h1]
  rw [mcut]
  exact Nat.le_floor (by exact_mod_cast h27)

lemma KimLarge.thr6_ge_one {N : ℕ} (h : KimLarge N) (k : ℕ) :
    1 ≤ kimThr6 N k := by
  have hβ := h.beta_ge_one k
  have hm : 1 ≤ mcut N := h.mcut_pos
  have hmR : (1 : ℝ) ≤ (mcut N : ℝ) := by exact_mod_cast hm
  have hs : (1 : ℝ) ≤ Real.sqrt (2 * (mcut N : ℝ)) := by
    have h1 : Real.sqrt 1 ≤ Real.sqrt (2 * (mcut N : ℝ)) :=
      Real.sqrt_le_sqrt (by linarith)
    simpa using h1
  rw [kimThr6]
  nlinarith [hβ, hs]

/-- `mcut ≤ θ²b_{k₀}²√n`, the floor. -/
lemma KimLarge.mcut_le_mcutR {N : ℕ} (h : KimLarge N) :
    (mcut N : ℝ) ≤ mcutR N := by
  have hb0 := bSeq_pos N ⌊(N : ℝ) ^ kimDelta / theta N⌋₊
  have h0 : (0 : ℝ) ≤ mcutR N := by
    rw [mcutR]; positivity
  rw [mcut]; exact Nat.floor_le h0

/-- `θ²b_{k₀}²√n ≤ 2·mcut`: the floor loses at most a factor `2`. -/
lemma KimLarge.mcutR_le_two_mcut {N : ℕ} (h : KimLarge N) :
    mcutR N ≤ 2 * (mcut N : ℝ) := by
  have hpos := h.mcut_pos
  have hposR : (1 : ℝ) ≤ (mcut N : ℝ) := by exact_mod_cast hpos
  have hfl : mcutR N < (mcut N : ℝ) + 1 := by
    rw [mcut]; exact Nat.lt_floor_add_one _
  linarith

/-- **`mcut ≥ e^{−2δL−4√L−2}·√n/(2L⁴)`**, the form the §4.7/§4.8 exponents use. -/
lemma KimLarge.mcut_ge_exp {N : ℕ} (h : KimLarge N) :
    Real.exp (-(2 * kimDelta * Real.log N) - 4 * Real.sqrt (Real.log N) - 2)
        * Real.sqrt N / (2 * (Real.log N) ^ 4)
      ≤ (mcut N : ℝ) := by
  have hn := h.card_pos
  have hL := h.logn_big
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hL4 : (0 : ℝ) < (Real.log N) ^ 4 := by positivity
  have hb0sq := h.bSq_ge (k := ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) le_rfl
  have hmh := h.mcutR_le_two_mcut
  have hsN := sqrtN_eq_exp hn
  have hX0 : (0 : ℝ) < Real.sqrt N := by rw [hsN]; exact Real.exp_pos _
  have hmcR : Real.exp (-(2 * kimDelta * Real.log N)
        - 4 * Real.sqrt (Real.log N) - 2) * Real.sqrt N / (Real.log N) ^ 4
      ≤ mcutR N := by
    have hgoal : mcutR N
        = bSeq N ⌊(N : ℝ) ^ kimDelta / theta N⌋₊ ^ 2
          * Real.sqrt N / (Real.log N) ^ 4 := by
      rw [mcutR, theta]; field_simp; try ring
    rw [hgoal]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hb0sq hX0.le) hL4.le
  have heq : Real.exp (-(2 * kimDelta * Real.log N)
        - 4 * Real.sqrt (Real.log N) - 2) * Real.sqrt N / (2 * (Real.log N) ^ 4)
      = Real.exp (-(2 * kimDelta * Real.log N)
        - 4 * Real.sqrt (Real.log N) - 2) * Real.sqrt N / (Real.log N) ^ 4
        / 2 := by
    field_simp; try ring
  rw [heq]
  linarith [hmcR, hmh]

/-- `mcut n ≥ 25n^δ(log n)³`. -/
lemma KimLarge.mcut_ge {N : ℕ} (h : KimLarge N) :
    25 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3) ≤ (mcut N : ℝ) := by
  have hge := h.mcutR_ge
  have hfl : mcutR N < (mcut N : ℝ) + 1 := by
    rw [mcut]; exact Nat.lt_floor_add_one _
  have hN : 1 ≤ N := h.card_pos
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hδ : (1 : ℝ) ≤ (N : ℝ) ^ kimDelta :=
    Real.one_le_rpow hNR kimDelta_pos.le
  have hL := h.logn_ge_one
  have hL3 : (1 : ℝ) ≤ (Real.log N) ^ 3 := one_le_pow₀ hL
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ kimDelta * (Real.log N) ^ 3 := by
    nlinarith [hδ, hL3]
  linarith [hge, hfl, h1]

/-- `2β ≤ √(mcut n)`, §4.7's requirement on the almost-disjointness scale. -/
lemma KimLarge.beta_le_sqrt_mcut {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    2 * kimBeta N k ≤ Real.sqrt ((mcut N : ℝ)) := by
  have hkle := h.k_le hk
  have hL := h.logn_ge_one
  have hmc := h.mcut_ge
  have hN1 : 1 ≤ N := h.card_pos
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hrp : (1 : ℝ) ≤ (N : ℝ) ^ kimDelta :=
    Real.one_le_rpow hNR kimDelta_pos.le
  have hβ0 : (0 : ℝ) ≤ 2 * kimBeta N k := by
    have := kimBeta_nonneg N k; linarith
  have hβsq : (2 * kimBeta N k) ^ 2 ≤ (mcut N : ℝ) := by
    have hb2 := kimBeta_sq N k (by linarith)
    have h4 : (2 * kimBeta N k) ^ 2 = 4 * (3 * ((k : ℝ) + 1) * Real.log N) := by
      rw [mul_pow, hb2]; ring
    rw [h4]
    have hL3 : Real.log N ≤ (Real.log N) ^ 3 := by nlinarith [hL]
    have hstep : (k : ℝ) * Real.log N
        ≤ ((N : ℝ) ^ kimDelta * (Real.log N) ^ 2) * Real.log N :=
      mul_le_mul_of_nonneg_right hkle (by linarith)
    have hkL : 4 * (3 * ((k : ℝ) + 1) * Real.log N)
        ≤ 25 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3) := by
      nlinarith [hstep, hL3, hrp, hL]
    linarith [hkL, hmc]
  have hstep := Real.sqrt_le_sqrt hβsq
  rwa [Real.sqrt_sq hβ0] at hstep

/-- `mcut ≤ √n`, since `θ²b² ≤ 1`. -/
lemma KimLarge.mcut_le_sqrtN {N : ℕ} (h : KimLarge N) :
    (mcut N : ℝ) ≤ Real.sqrt N := by
  have hle := h.mcut_le_mcutR
  have hθ : theta N ≤ 1 / 100 := h.2.1
  have hθ0 := theta_nonneg N
  have hb0 := (bSeq_pos N ⌊(N : ℝ) ^ kimDelta / theta N⌋₊).le
  have hb1 := bSeq_le_one N ⌊(N : ℝ) ^ kimDelta / theta N⌋₊
  have hS0 : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hR : mcutR N ≤ Real.sqrt N := by
    rw [mcutR]
    have hθ2 : theta N ^ 2 ≤ 1 := by nlinarith [hθ, hθ0]
    have hb2 : bSeq N ⌊(N : ℝ) ^ kimDelta / theta N⌋₊ ^ 2 ≤ 1 := by
      nlinarith [hb0, hb1]
    have hb2' : (0 : ℝ) ≤ bSeq N ⌊(N : ℝ) ^ kimDelta / theta N⌋₊ ^ 2 := by
      positivity
    have hprod : theta N ^ 2 * bSeq N ⌊(N : ℝ) ^ kimDelta / theta N⌋₊ ^ 2 ≤ 1 := by
      nlinarith [hθ2, hb2, hb2', sq_nonneg (theta N)]
    nlinarith [hprod, hS0]
  linarith

/-- `√(mcut n) ≤ n^{1/4}`. -/
lemma KimLarge.sqrt_mcut_le {N : ℕ} (h : KimLarge N) :
    Real.sqrt ((mcut N : ℝ)) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hstep := Real.sqrt_le_sqrt h.mcut_le_sqrtN
  have heq : Real.sqrt (Real.sqrt N) = (N : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hNnn]
    norm_num
  rwa [heq] at hstep

/-- `2D ≤ 2M`: §4.7's defect bound fits inside the padding budget. -/
lemma KimLarge.kimDpar_le {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    2 * kimDpar N k ≤ 2 * kimM N k := by
  have hM := h.kimM_ge hk
  have hβ := h.beta_ge_one k
  have hsm := h.sqrt_mcut_le
  have hN1 : 1 ≤ N := h.card_pos
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have h16 : (N : ℝ) ^ ((1 : ℝ) / 6) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le hNR (by norm_num)
  have h14 : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.one_le_rpow hNR (by norm_num)
  have hLe : Real.exp 1 ≤ Real.log N := h.2.2.1
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hL2 : (2 : ℝ) ≤ Real.log N := by linarith
  have hL4 : (16 : ℝ) ≤ (Real.log N) ^ 4 := by
    have h1 : (2 : ℝ) ^ 4 ≤ (Real.log N) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) hL2 4
    norm_num at h1; linarith
  have hs4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hs2' : Real.sqrt 2 ≤ 2 := by
    rw [← hs4]; exact Real.sqrt_le_sqrt (by norm_num)
  have hs2 : Real.sqrt (2 * (mcut N : ℝ)) ≤ 2 * (N : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hsn : (0 : ℝ) ≤ Real.sqrt ((mcut N : ℝ)) := Real.sqrt_nonneg _
    nlinarith [hs2', hsm, h16, hsn]
  have hβ0 : (0 : ℝ) < kimBeta N k := by linarith
  have hceil := Nat.ceil_lt_add_one
    (show (0 : ℝ) ≤ Real.sqrt (2 * (mcut N : ℝ)) / kimBeta N k by positivity)
  have hD : ((kimDpar N k : ℕ) : ℝ)
      ≤ Real.sqrt (2 * (mcut N : ℝ)) / kimBeta N k + 1 := by
    rw [kimDpar]; linarith [hceil]
  have hdiv : Real.sqrt (2 * (mcut N : ℝ)) / kimBeta N k
      ≤ Real.sqrt (2 * (mcut N : ℝ)) := by
    rw [div_le_iff₀ hβ0]
    nlinarith [hβ, Real.sqrt_nonneg (2 * (mcut N : ℝ))]
  have hMbig : 80 * (N : ℝ) ^ ((1 : ℝ) / 4) - 1 ≤ ((kimM N k : ℕ) : ℝ) := by
    have hprod : 16 * (N : ℝ) ^ ((1 : ℝ) / 4)
        ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 4 := by
      nlinarith [hL4, h14]
    linarith [hM, hprod]
  have hfin : ((kimDpar N k : ℕ) : ℝ) ≤ ((kimM N k : ℕ) : ℝ) := by
    linarith [hD, hdiv, hs2, hMbig, h14]
  have hnat : kimDpar N k ≤ kimM N k := by exact_mod_cast hfin
  omega

/-- `4Dp ≤ 4b²θ²`, and hence `4Dp ≤ 1`. -/
lemma KimLarge.kimDpar_p_le {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    4 * ((kimDpar N k : ℕ) : ℝ) * edgeProb N
      ≤ 4 * bSeq N k ^ 2 * theta N ^ 2 := by
  have hN1 : 1 ≤ N := h.card_pos
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hθpos : 0 < theta N := h.theta_pos'
  have hβ := h.beta_ge_one k
  have hsm := h.sqrt_mcut_le
  have hcl := h.2.2.2.2.2.2.2.2.2.2.1
  have hbmin := bSeq_ge_of_k_le hN1 hθpos hk
  have hE0 : (0 : ℝ) ≤ Real.exp (-(kimDelta * Real.log N)
      - 2 * Real.sqrt (kimDelta * Real.log N) - 1) := (Real.exp_pos _).le
  have hsq0 : (0 : ℝ) < Real.sqrt (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := one_le_sqrt_cast hN1
    linarith
  have h16 : (N : ℝ) ^ ((1 : ℝ) / 6) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le hNR (by norm_num)
  have h14 : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.one_le_rpow hNR (by norm_num)
  have h16' : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 6) :=
    Real.one_le_rpow hNR (by norm_num)
  have hL := h.logn_big
  have hL4 : (16 : ℝ) ≤ (Real.log N) ^ 4 := by
    have h1 : (2 : ℝ) ^ 4 ≤ (Real.log N) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 4
    norm_num at h1; linarith
  -- `b² θ √N ≥ n^{1/4}(log n)^4`
  have hEsq : (Real.exp (-(kimDelta * Real.log N)
        - 2 * Real.sqrt (kimDelta * Real.log N) - 1)) ^ 2 ≤ bSeq N k ^ 2 :=
    pow_le_pow_left₀ hE0 hbmin 2
  have hbig : (N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 4
      ≤ bSeq N k ^ 2 * theta N * Real.sqrt N := by
    refine le_trans hcl ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hEsq hθpos.le) hsq0.le
  -- `D ≤ 3n^{1/6}`
  have hs2' : Real.sqrt 2 ≤ 2 := by
    have hs4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← hs4]; exact Real.sqrt_le_sqrt (by norm_num)
  have hβ0 : (0 : ℝ) < kimBeta N k := by linarith
  have hceil := Nat.ceil_lt_add_one
    (show (0 : ℝ) ≤ Real.sqrt (2 * (mcut N : ℝ)) / kimBeta N k by positivity)
  have hD : ((kimDpar N k : ℕ) : ℝ)
      ≤ Real.sqrt (2 * (mcut N : ℝ)) / kimBeta N k + 1 := by
    rw [kimDpar]; linarith [hceil]
  have hdiv : Real.sqrt (2 * (mcut N : ℝ)) / kimBeta N k
      ≤ Real.sqrt (2 * (mcut N : ℝ)) := by
    rw [div_le_iff₀ hβ0]
    nlinarith [hβ, Real.sqrt_nonneg (2 * (mcut N : ℝ))]
  have hsm2 : Real.sqrt (2 * (mcut N : ℝ)) ≤ 2 * (N : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [hs2', hsm, Real.sqrt_nonneg ((mcut N : ℝ))]
  have hDle : ((kimDpar N k : ℕ) : ℝ) ≤ 3 * (N : ℝ) ^ ((1 : ℝ) / 4) := by
    linarith [hD, hdiv, hsm2, h14]
  -- combine
  have hmain : ((kimDpar N k : ℕ) : ℝ) ≤ bSeq N k ^ 2 * theta N * Real.sqrt N := by
    have hstep : 3 * (N : ℝ) ^ ((1 : ℝ) / 4)
        ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 4 := by
      nlinarith [hL4, h14]
    linarith [hDle, hstep, hbig]
  rw [edgeProb]
  rw [show 4 * ((kimDpar N k : ℕ) : ℝ) * (theta N / Real.sqrt N)
      = (4 * ((kimDpar N k : ℕ) : ℝ) * theta N) / Real.sqrt N by ring,
    div_le_iff₀ hsq0]
  nlinarith [hmain, hθpos, hsq0]

/-- `4Dp ≤ 1`. -/
lemma KimLarge.kimDpar_p_le_one {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    4 * ((kimDpar N k : ℕ) : ℝ) * edgeProb N ≤ 1 := by
  have hm := h.kimDpar_p_le hk
  have hb := bSeq_le_one N k
  have hb0 := (bSeq_pos N k).le
  have hθ : theta N ≤ 1 / 100 := h.2.1
  have hθ0 := h.theta_pos'.le
  have hb2 : bSeq N k ^ 2 ≤ 1 := by nlinarith [hb, hb0]
  have hθ2 : theta N ^ 2 ≤ 1 / 10000 := by nlinarith [hθ, hθ0]
  have : 4 * bSeq N k ^ 2 * theta N ^ 2 ≤ 4 * 1 * (1 / 10000 : ℝ) := by
    have h1 : (0 : ℝ) ≤ theta N ^ 2 := by positivity
    nlinarith [hb2, hθ2, h1]
  linarith [hm, this]

lemma inv_pow_eq_exp {N : ℕ} (hN : 0 < N) (m : ℕ) :
    (((N : ℝ) ^ m)⁻¹) = Real.exp (-((m : ℝ) * Real.log N)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ((N : ℝ)) ^ m = Real.exp ((m : ℝ) * Real.log N) := by
    rw [Real.exp_nat_mul, Real.exp_log hNpos]
  rw [h1, ← Real.exp_neg]

/-- `n^δ = exp(δ·log n)`. -/
lemma rpow_delta_eq_exp {N : ℕ} (hN : 0 < N) :
    (N : ℝ) ^ kimDelta = Real.exp (kimDelta * Real.log N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_def_of_pos hNpos]
  congr 1
  ring

/-- `b²θ²(a+5θ)√n ≥ 5b²√n/L⁶`: the §4.5 drift, bounded below by its `5θ` part. -/
lemma KimLarge.drift_ge {N k : ℕ} (h : KimLarge N) :
    5 * bSeq N k ^ 2 * Real.sqrt N / (Real.log N) ^ 6
      ≤ bSeq N k ^ 2 * theta N ^ 2 * (aSeq N k + 5 * theta N)
        * Real.sqrt N := by
  have hL := h.logn_big
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have ha := aSeq_nonneg N k
  have hb0 : (0 : ℝ) ≤ bSeq N k ^ 2 := by positivity
  have hs0 : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hstep : 5 / (Real.log N) ^ 6
      ≤ theta N ^ 2 * (aSeq N k + 5 * theta N) := by
    rw [theta]
    have h5 : (5 : ℝ) / (Real.log N) ^ 2
        ≤ aSeq N k + 5 * (1 / (Real.log N) ^ 2) := by
      have he : (5 : ℝ) * (1 / (Real.log N) ^ 2) = 5 / (Real.log N) ^ 2 := by
        ring
      linarith [ha, he.le, he.ge]
    have hsq : (0 : ℝ) < (1 / (Real.log N) ^ 2) ^ 2 := by positivity
    calc (5 : ℝ) / (Real.log N) ^ 6
        = (1 / (Real.log N) ^ 2) ^ 2 * (5 / (Real.log N) ^ 2) := by
          field_simp; try ring
      _ ≤ (1 / (Real.log N) ^ 2) ^ 2
          * (aSeq N k + 5 * (1 / (Real.log N) ^ 2)) :=
          mul_le_mul_of_nonneg_left h5 hsq.le
  have hmul := mul_le_mul_of_nonneg_left hstep (mul_nonneg hb0 hs0)
  calc 5 * bSeq N k ^ 2 * Real.sqrt N / (Real.log N) ^ 6
      = bSeq N k ^ 2 * Real.sqrt N * (5 / (Real.log N) ^ 6) := by ring
    _ ≤ bSeq N k ^ 2 * Real.sqrt N
        * (theta N ^ 2 * (aSeq N k + 5 * theta N)) := hmul
    _ = bSeq N k ^ 2 * theta N ^ 2 * (aSeq N k + 5 * theta N)
        * Real.sqrt N := by ring

/-- `√n·b_k² ≥ 2L·L¹⁰`, from the §4.5 second exponent estimate. -/
lemma KimLarge.sqrtN_bsq_ge {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    2 * Real.log N ≤ Real.sqrt N * bSeq N k ^ 2 / (Real.log N) ^ 10 := by
  have hn : 0 < N := h.card_pos
  have hL := h.logn_big
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hasym := h.asym.p4_exp2
  have hbsq := h.bSq_ge hk
  have hsN : Real.sqrt N = Real.exp (Real.log N / 2) := sqrtN_eq_exp hn
  have hsplit : Real.exp (((1 : ℝ) / 2 - 2 * kimDelta) * Real.log N
        - 4 * Real.sqrt (Real.log N) - 2)
      = Real.exp (Real.log N / 2)
        * Real.exp (-(2 * kimDelta * Real.log N)
            - 4 * Real.sqrt (Real.log N) - 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit] at hasym
  have h1 : Real.exp (Real.log N / 2)
        * Real.exp (-(2 * kimDelta * Real.log N)
          - 4 * Real.sqrt (Real.log N) - 2) / (Real.log N) ^ 10
      ≤ Real.exp (Real.log N / 2) * bSeq N k ^ 2 / (Real.log N) ^ 10 :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbsq (Real.exp_pos _).le)
      (by positivity : (0 : ℝ) ≤ (Real.log N) ^ 10)
  rw [hsN]
  linarith [hasym, h1]

/-- **Kim's §4.5 second exponent condition**, at the tilt `t₂ = θ²`. -/
lemma KimLarge.hexp2_p4 {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    Real.log 2 + 4 * Real.log N
      ≤ theta N ^ 2 * (bSeq N k ^ 2 * theta N ^ 2
          * (aSeq N k + 5 * theta N) * Real.sqrt N) / 2 := by
  have hL := h.logn_big
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hX := h.sqrtN_bsq_ge hk
  have hdr := h.drift_ge (k := k)
  have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hθ0 : (0 : ℝ) ≤ theta N ^ 2 := by positivity
  have h1 : theta N ^ 2 * (5 * bSeq N k ^ 2 * Real.sqrt N / (Real.log N) ^ 6)
      ≤ theta N ^ 2 * (bSeq N k ^ 2 * theta N ^ 2
          * (aSeq N k + 5 * theta N) * Real.sqrt N) :=
    mul_le_mul_of_nonneg_left hdr hθ0
  have h2 : theta N ^ 2 * (5 * bSeq N k ^ 2 * Real.sqrt N / (Real.log N) ^ 6)
      = 5 * (Real.sqrt N * bSeq N k ^ 2 / (Real.log N) ^ 10) := by
    rw [theta]; field_simp; try ring
  linarith [hX, h1, h2.le, h2.ge]

/-- **Kim's §4.5 variance condition**, at the tilt `t₂ = θ²`. -/
lemma KimLarge.hvar2_p4 {N k : ℕ} (h : KimLarge N) :
    (theta N ^ 2) ^ 2 / 2 * (edgeProb N
        * ((bSeq N k ^ 2 * (N : ℝ)) * Real.exp (theta N ^ 2)))
      ≤ theta N ^ 2 * (bSeq N k ^ 2 * theta N ^ 2
          * (aSeq N k + 5 * theta N) * Real.sqrt N) / 2 := by
  have hn : 0 < N := h.card_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hn
  have hL := h.logn_big
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hθ : theta N ≤ 1 / 100 := h.2.1
  have hθp := h.theta_pos'
  have hdr := h.drift_ge (k := k)
  have hθ0 : (0 : ℝ) ≤ theta N ^ 2 := by positivity
  have hS0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
  have hb0 : (0 : ℝ) ≤ bSeq N k ^ 2 := by positivity
  have hLHS : (theta N ^ 2) ^ 2 / 2 * (edgeProb N
        * ((bSeq N k ^ 2 * (N : ℝ)) * Real.exp (theta N ^ 2)))
      = theta N ^ 5 * bSeq N k ^ 2 * ((N : ℝ) / Real.sqrt N)
        * Real.exp (theta N ^ 2) / 2 := by
    rw [edgeProb]
    field_simp
    try ring
  have h1 : theta N ^ 2 * (5 * bSeq N k ^ 2 * Real.sqrt N / (Real.log N) ^ 6)
      ≤ theta N ^ 2 * (bSeq N k ^ 2 * theta N ^ 2
          * (aSeq N k + 5 * theta N) * Real.sqrt N) :=
    mul_le_mul_of_nonneg_left hdr hθ0
  have h2 : theta N ^ 2 * (5 * bSeq N k ^ 2 * Real.sqrt N / (Real.log N) ^ 6)
      = 5 * theta N ^ 5 * bSeq N k ^ 2 * Real.sqrt N := by
    rw [theta]; field_simp; try ring
  have hexp5 : Real.exp (theta N ^ 2) ≤ 5 := by
    have h1' : theta N ^ 2 ≤ 1 := by nlinarith [hθ, hθp.le]
    calc Real.exp (theta N ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr h1'
      _ ≤ 5 := by have := Real.exp_one_lt_d9; linarith
  have hpos : (0 : ℝ) ≤ theta N ^ 5 * bSeq N k ^ 2 * Real.sqrt N := by
    have : (0 : ℝ) ≤ theta N ^ 5 := by positivity
    positivity
  have hfin : theta N ^ 5 * bSeq N k ^ 2 * Real.sqrt N * Real.exp (theta N ^ 2)
      ≤ 5 * theta N ^ 5 * bSeq N k ^ 2 * Real.sqrt N := by
    nlinarith [mul_le_mul_of_nonneg_left hexp5 hpos]
  rw [hLHS, Real.div_sqrt]
  linarith [hfin, h1, h2.le, h2.ge]

/-- `R·b_k² ≥ 20 n^δ L⁸`, the §4.5 variance comparison. -/
lemma KimLarge.var_cmp_p4 {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    20 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 8)
      ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * bSeq N k ^ 2 := by
  have hn : 0 < N := h.card_pos
  have hasym := h.asym.p4_var
  have hbsq := h.bSq_ge hk
  have hRexp := rpow_quarter_eq_exp hn
  have hδexp := rpow_delta_eq_exp hn
  have hδ0 : (0 : ℝ) < (N : ℝ) ^ kimDelta := by rw [hδexp]; exact Real.exp_pos _
  have hstep : (N : ℝ) ^ kimDelta * (20 * (Real.log N) ^ 8)
      ≤ (N : ℝ) ^ kimDelta
        * Real.exp (((1 : ℝ) / 4 - 3 * kimDelta) * Real.log N
            - 4 * Real.sqrt (Real.log N) - 2) :=
    mul_le_mul_of_nonneg_left hasym hδ0.le
  have heq : (N : ℝ) ^ kimDelta
        * Real.exp (((1 : ℝ) / 4 - 3 * kimDelta) * Real.log N
            - 4 * Real.sqrt (Real.log N) - 2)
      = (N : ℝ) ^ ((1 : ℝ) / 4)
        * Real.exp (-(2 * kimDelta * Real.log N)
            - 4 * Real.sqrt (Real.log N) - 2) := by
    rw [hδexp, hRexp, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hfin : (N : ℝ) ^ ((1 : ℝ) / 4)
        * Real.exp (-(2 * kimDelta * Real.log N)
            - 4 * Real.sqrt (Real.log N) - 2)
      ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * bSeq N k ^ 2 :=
    mul_le_mul_of_nonneg_left hbsq (Real.rpow_nonneg (by positivity) _)
  have hL : 20 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 8)
      = (N : ℝ) ^ kimDelta * (20 * (Real.log N) ^ 8) := by ring
  linarith [hstep, heq.le, heq.ge, hfin, hL.le, hL.ge]

set_option maxHeartbeats 1000000 in
/-- The pure arithmetic behind §4.5's first exponent condition, at `t = R⁻¹`. -/
lemma hexp1_p4_core {R L b M p t A c : ℝ}
    (hR0 : 0 < R) (hL : 13 ≤ L) (hb0 : 0 ≤ b) (hM0 : 0 ≤ M) (hc0 : 0 ≤ c)
    (ht : t = 1 / R) (hp : p = 1 / (L ^ 2 * R ^ 2))
    (hMle : M ≤ Real.sqrt L * R ^ 2)
    (hA : 5 * b ^ 2 * R ^ 2 / L ^ 6 ≤ A)
    (hdrift : 2 * L ≤ R * b ^ 2 / L ^ 6)
    (hcR : c ≤ R)
    (hcvar : 2 * Real.exp 1 * L ^ 5 * c ≤ 5 * b ^ 2 * R) :
    -(t * A) + t ^ 2 / 2 * (p * (c * (2 * M * M) * Real.exp (t * c)))
      ≤ -(4 * L) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hsL : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hsL0 : (0 : ℝ) ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hMsq : M * M ≤ L * R ^ 4 := by
    have h1 : M * M ≤ (Real.sqrt L * R ^ 2) * (Real.sqrt L * R ^ 2) :=
      mul_le_mul hMle hMle hM0 (by positivity)
    nlinarith [h1, hsL]
  have ht0 : (0 : ℝ) < t := by rw [ht]; positivity
  have htA : 10 * L ≤ t * A := by
    have h2 : t * (5 * b ^ 2 * R ^ 2 / L ^ 6) ≤ t * A :=
      mul_le_mul_of_nonneg_left hA ht0.le
    have h3 : t * (5 * b ^ 2 * R ^ 2 / L ^ 6) = 5 * (R * b ^ 2 / L ^ 6) := by
      rw [ht]; field_simp; try ring
    linarith [hdrift, h2, h3.le, h3.ge]
  have htc : t * c ≤ 1 := by
    rw [ht, div_mul_eq_mul_div, one_mul, div_le_one hR0]; exact hcR
  have hexpc : Real.exp (t * c) ≤ Real.exp 1 := Real.exp_le_exp.mpr htc
  have hp0 : (0 : ℝ) ≤ p := by rw [hp]; positivity
  have ht20 : (0 : ℝ) ≤ t ^ 2 / 2 := by positivity
  have hvar : t ^ 2 / 2 * (p * (c * (2 * M * M) * Real.exp (t * c)))
      ≤ c * Real.exp 1 / L := by
    have hA1 : c * (2 * M * M) ≤ c * (2 * (L * R ^ 4)) := by
      nlinarith [hMsq, hc0]
    have hA0 : (0 : ℝ) ≤ c * (2 * M * M) := by positivity
    have hstep1 : c * (2 * M * M) * Real.exp (t * c)
        ≤ c * (2 * (L * R ^ 4)) * Real.exp 1 := by
      calc c * (2 * M * M) * Real.exp (t * c)
          ≤ c * (2 * M * M) * Real.exp 1 :=
            mul_le_mul_of_nonneg_left hexpc hA0
        _ ≤ c * (2 * (L * R ^ 4)) * Real.exp 1 :=
            mul_le_mul_of_nonneg_right hA1 (Real.exp_pos 1).le
    have hchain := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hstep1 hp0) ht20
    have heq : t ^ 2 / 2 * (p * (c * (2 * (L * R ^ 4)) * Real.exp 1))
        = c * Real.exp 1 / L := by
      rw [ht, hp]; field_simp; try ring
    linarith [hchain, heq.le, heq.ge]
  have hhalf : c * Real.exp 1 / L ≤ t * A / 2 := by
    have h1 : c * Real.exp 1 / L ≤ 5 * b ^ 2 * R / (2 * L ^ 6) := by
      rw [div_le_div_iff₀ hL0 (by positivity)]
      nlinarith [hcvar, hL0]
    have h2 : 5 * b ^ 2 * R / (2 * L ^ 6) ≤ t * A / 2 := by
      have h3 : t * (5 * b ^ 2 * R ^ 2 / L ^ 6) ≤ t * A :=
        mul_le_mul_of_nonneg_left hA (by rw [ht]; positivity)
      have h4 : t * (5 * b ^ 2 * R ^ 2 / L ^ 6) = 5 * b ^ 2 * R / L ^ 6 := by
        rw [ht]; field_simp; try ring
      have h5 : 5 * b ^ 2 * R / (2 * L ^ 6) = (5 * b ^ 2 * R / L ^ 6) / 2 := by
        field_simp; try ring
      linarith [h3, h4.le, h4.ge, h5.le, h5.ge]
    linarith
  linarith [htA, hvar, hhalf]

set_option maxHeartbeats 1000000 in
/-- **Kim's §4.5 first exponent condition**, at the tilt `t₁ = n^{−1/4}`. -/
lemma KimLarge.hexp1_p4 {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    Real.exp (-(kimRho4b N * (bSeq N k ^ 2 * theta N ^ 2
            * (aSeq N k + 5 * theta N) * Real.sqrt N))
        + kimRho4b N ^ 2 / 2 * (edgeProb N
          * ((3 * (k : ℝ) * Real.log N + 2)
            * (2 * (kimM N k : ℝ) * (kimM N k : ℝ))
            * Real.exp (kimRho4b N * (3 * (k : ℝ) * Real.log N + 2)))))
      ≤ ((N : ℝ) ^ (4 : ℕ))⁻¹ := by
  have hn : 0 < N := h.card_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hn
  have hL := h.logn_big
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  obtain ⟨hR0, hR4, hR2, hρR⟩ := quarter_pow_facts hn
  have hMle0 := h.kimM_le' hk
  have hδexp := rpow_delta_eq_exp hn
  have hδ0 : (0 : ℝ) < (N : ℝ) ^ kimDelta := by rw [hδexp]; exact Real.exp_pos _
  have hδ1 : (1 : ℝ) ≤ (N : ℝ) ^ kimDelta :=
    Real.one_le_rpow (Nat.one_le_cast.mpr hn) kimDelta_pos.le
  have hb0 := (bSeq_pos N k).le
  have hbsq0 : (0 : ℝ) ≤ bSeq N k ^ 2 := by positivity
  have hteq : kimRho4b N = 1 / (N : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [kimRho4b, Real.rpow_neg hNR.le, one_div]
    norm_num
  have hpeq : edgeProb N
      = 1 / ((Real.log N) ^ 2 * ((N : ℝ) ^ ((1 : ℝ) / 4)) ^ 2) := by
    rw [edgeProb, theta, hR2]
    have hsq0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
    field_simp
  have hA : 5 * bSeq N k ^ 2 * ((N : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 / (Real.log N) ^ 6
      ≤ bSeq N k ^ 2 * theta N ^ 2 * (aSeq N k + 5 * theta N)
        * Real.sqrt N := by
    rw [hR2]; exact h.drift_ge
  have hdrift : 2 * Real.log N
      ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * bSeq N k ^ 2 / (Real.log N) ^ 6 := by
    have hasym := h.asym.p4_drift
    have hbsq := h.bSq_ge hk
    have hRexp := rpow_quarter_eq_exp hn
    have hsplit : Real.exp (((1 : ℝ) / 4 - 2 * kimDelta) * Real.log N
          - 4 * Real.sqrt (Real.log N) - 2)
        = (N : ℝ) ^ ((1 : ℝ) / 4)
          * Real.exp (-(2 * kimDelta * Real.log N)
              - 4 * Real.sqrt (Real.log N) - 2) := by
      rw [hRexp, ← Real.exp_add]; congr 1; ring
    rw [hsplit] at hasym
    have h1 : (N : ℝ) ^ ((1 : ℝ) / 4)
          * Real.exp (-(2 * kimDelta * Real.log N)
            - 4 * Real.sqrt (Real.log N) - 2) / (Real.log N) ^ 6
        ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * bSeq N k ^ 2 / (Real.log N) ^ 6 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbsq hR0.le)
        (by positivity : (0 : ℝ) ≤ (Real.log N) ^ 6)
    linarith [hasym, h1]
  have hkle := h.k_le hk
  have hL3 : (2197 : ℝ) ≤ (Real.log N) ^ 3 := by
    have h1 : (13 : ℝ) ^ 3 ≤ (Real.log N) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hL 3
    norm_num at h1; linarith
  have hc4 : 3 * (k : ℝ) * Real.log N + 2
      ≤ 4 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3) := by
    have hmul := mul_le_mul_of_nonneg_right hkle hL0.le
    have hring : (N : ℝ) ^ kimDelta * (Real.log N) ^ 2 * Real.log N
        = (N : ℝ) ^ kimDelta * (Real.log N) ^ 3 := by ring
    have h1 : 3 * (k : ℝ) * Real.log N
        ≤ 3 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3) := by
      linarith [hmul, hring.le, hring.ge]
    have h2 : (2 : ℝ) ≤ (N : ℝ) ^ kimDelta * (Real.log N) ^ 3 := by
      have hm := mul_le_mul_of_nonneg_right hδ1
        (by positivity : (0 : ℝ) ≤ (Real.log N) ^ 3)
      linarith [hm, hL3]
    linarith
  have hX0 : (0 : ℝ) ≤ (N : ℝ) ^ kimDelta * (Real.log N) ^ 3 :=
    mul_nonneg hδ0.le (by positivity)
  have hcR : 3 * (k : ℝ) * Real.log N + 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
    have hcl := h.2.2.2.2.2.2.2.2.2.2.2.2.1
    linarith [hc4, hcl, hX0]
  have hcvar : 2 * Real.exp 1 * (Real.log N) ^ 5
        * (3 * (k : ℝ) * Real.log N + 2)
      ≤ 5 * bSeq N k ^ 2 * (N : ℝ) ^ ((1 : ℝ) / 4) := by
    have hvc := h.var_cmp_p4 hk
    have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have hL50 : (0 : ℝ) ≤ (Real.log N) ^ 5 := by positivity
    have hstep : 2 * Real.exp 1 * (Real.log N) ^ 5
          * (3 * (k : ℝ) * Real.log N + 2)
        ≤ 24 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 8) := by
      have h1 : 2 * Real.exp 1 * (Real.log N) ^ 5 ≤ 6 * (Real.log N) ^ 5 := by
        nlinarith [he3, hL50]
      have h2 : (0 : ℝ) ≤ 3 * (k : ℝ) * Real.log N + 2 := by positivity
      have h3 : 2 * Real.exp 1 * (Real.log N) ^ 5
            * (3 * (k : ℝ) * Real.log N + 2)
          ≤ 6 * (Real.log N) ^ 5 * (3 * (k : ℝ) * Real.log N + 2) :=
        mul_le_mul_of_nonneg_right h1 h2
      have h4 : 6 * (Real.log N) ^ 5 * (3 * (k : ℝ) * Real.log N + 2)
          ≤ 6 * (Real.log N) ^ 5 * (4 * ((N : ℝ) ^ kimDelta
              * (Real.log N) ^ 3)) :=
        mul_le_mul_of_nonneg_left hc4 (by positivity)
      have h5 : 6 * (Real.log N) ^ 5 * (4 * ((N : ℝ) ^ kimDelta
            * (Real.log N) ^ 3))
          = 24 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 8) := by ring
      linarith [h3, h4, h5.le, h5.ge]
    have hRb : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * bSeq N k ^ 2 :=
      mul_nonneg hR0.le hbsq0
    linarith [hstep, hvc, hRb]
  have hcore := hexp1_p4_core (R := (N : ℝ) ^ ((1 : ℝ) / 4))
    (L := Real.log N) (b := bSeq N k) (M := (kimM N k : ℝ))
    (p := edgeProb N) (t := kimRho4b N)
    (A := bSeq N k ^ 2 * theta N ^ 2 * (aSeq N k + 5 * theta N) * Real.sqrt N)
    (c := 3 * (k : ℝ) * Real.log N + 2)
    hR0 hL hb0 (Nat.cast_nonneg _)
    (by positivity) hteq hpeq (by rw [hR2]; exact hMle0) hA hdrift hcR hcvar
  rw [inv_pow_eq_exp hn 4]
  refine Real.exp_le_exp.mpr ?_
  push_cast
  linarith [hcore]

/-- `β ≤ 2·n^{δ/2}·(log n)²`. -/
lemma KimLarge.beta_le {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    kimBeta N k
      ≤ 2 * Real.exp (kimDelta * Real.log N / 2) * (Real.log N) ^ 2 := by
  have hn : 0 < N := h.card_pos
  have hL := h.logn_big
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hkle := h.k_le hk
  have hδexp := rpow_delta_eq_exp hn
  have hδ1 : (1 : ℝ) ≤ (N : ℝ) ^ kimDelta :=
    Real.one_le_rpow (Nat.one_le_cast.mpr hn) kimDelta_pos.le
  have hδ0 : (0 : ℝ) < (N : ℝ) ^ kimDelta := by linarith
  have hbnd : 3 * ((k : ℝ) + 1) * Real.log N
      ≤ (2 * Real.exp (kimDelta * Real.log N / 2) * (Real.log N) ^ 2) ^ 2 := by
    have he2 : Real.exp (kimDelta * Real.log N / 2) ^ 2
        = Real.exp (kimDelta * Real.log N) := by
      rw [exp_sq]; congr 1; ring
    have hsq : (2 * Real.exp (kimDelta * Real.log N / 2) * (Real.log N) ^ 2) ^ 2
        = 4 * (N : ℝ) ^ kimDelta * (Real.log N) ^ 4 := by
      rw [hδexp, mul_pow, mul_pow, he2]
      ring
    rw [hsq]
    have h1 : 3 * (k : ℝ) * Real.log N
        ≤ 3 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3) := by
      have hmul := mul_le_mul_of_nonneg_right hkle hL0.le
      have hring : (N : ℝ) ^ kimDelta * (Real.log N) ^ 2 * Real.log N
          = (N : ℝ) ^ kimDelta * (Real.log N) ^ 3 := by ring
      linarith [hmul, hring.le, hring.ge]
    have h2 : (N : ℝ) ^ kimDelta * (Real.log N) ^ 3
        ≤ (N : ℝ) ^ kimDelta * (Real.log N) ^ 4 := by
      have hpp : (Real.log N) ^ 3 ≤ (Real.log N) ^ 4 :=
        pow_le_pow_right₀ (by linarith) (by norm_num)
      exact mul_le_mul_of_nonneg_left hpp hδ0.le
    have h3 : 3 * Real.log N ≤ (N : ℝ) ^ kimDelta * (Real.log N) ^ 4 := by
      have h4 : 3 * Real.log N ≤ (Real.log N) ^ 4 := by
        have hp3 : Real.log N ^ 3 ≤ Real.log N ^ 4 :=
          pow_le_pow_right₀ (by linarith) (by norm_num)
        have h13 : (3 : ℝ) * Real.log N ≤ Real.log N ^ 3 := by
          nlinarith [hL, hL0]
        linarith
      nlinarith [h4, hδ1, pow_pos hL0 4]
    linarith [h1, h2, h3]
  rw [kimBeta]
  calc Real.sqrt (3 * ((k : ℝ) + 1) * Real.log N)
      ≤ Real.sqrt ((2 * Real.exp (kimDelta * Real.log N / 2)
          * (Real.log N) ^ 2) ^ 2) := Real.sqrt_le_sqrt hbnd
    _ = 2 * Real.exp (kimDelta * Real.log N / 2) * (Real.log N) ^ 2 :=
        Real.sqrt_sq (by positivity)

/-- **`thr₆ ≤ 9·n^{1/4}/√log n`.**

Kim's threshold is `thr = 2β|A ∪ B|^{1/2}` with `|A| = |B| = b²θ²√n`, so
`|A ∪ B|^{1/2} = √2·bθn^{1/4}` and `thr = 2√2·(βb)·θn^{1/4}`.  The product
`βb` is bounded — `β²b² = 3(k+1)L·b² ≤ 9L³` by `(k+1)b²θ ≤ 3` — so the `√(k+1)`
never bites at the same time as `b`.  This is the coupling Kim uses silently
in his `ce ≤ 6((k+1)log n)^{1/2}bθn^{1/4}`. -/
lemma KimLarge.thr6_le {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    kimThr6 N k
      ≤ 9 * (N : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt (Real.log N) := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hL := h.logn_big
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have hsq : Real.sqrt (Real.log N) ^ 2 = Real.log N := Real.sq_sqrt hL0.le
  have hβ0 := kimBeta_nonneg N k
  have hb0 := (bSeq_pos N k).le
  have hbpos := bSeq_pos N k
  set k₀ := ⌊(N : ℝ) ^ kimDelta / theta N⌋₊ with hk₀
  have hb₀0 := (bSeq_pos N k₀).le
  have hmono : bSeq N k₀ ≤ bSeq N k := bSeq_antitone N hk
  -- `βb ≤ 3L√L`
  have hcoup : kimBeta N k * bSeq N k ≤ 3 * Real.log N * Real.sqrt (Real.log N) := by
    have h1 := h.beta_bSq_le (k := k)
    have h2 : kimBeta N k * bSeq N k * bSeq N k
        ≤ 3 * Real.log N * Real.sqrt (Real.log N) * bSeq N k := by
      have hr : kimBeta N k * bSeq N k ^ 2 = kimBeta N k * bSeq N k * bSeq N k := by
        ring
      have hr2 : 3 * bSeq N k * Real.log N * Real.sqrt (Real.log N)
          = 3 * Real.log N * Real.sqrt (Real.log N) * bSeq N k := by ring
      linarith [h1, hr.le, hr.ge, hr2.le, hr2.ge]
    exact le_of_mul_le_mul_right (by linarith [h2]) hbpos
  have hcoup₀ : kimBeta N k * bSeq N k₀
      ≤ 3 * Real.log N * Real.sqrt (Real.log N) := by
    have := mul_le_mul_of_nonneg_left hmono hβ0
    linarith [hcoup]
  -- `√(2 mcut) ≤ √2·θ·b_{k₀}·n^{1/4}`
  have hmc := h.mcut_le_mcutR
  have hn4 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hNR _
  have hn4sq : ((N : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt N := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 4)) 2,
      ← Real.rpow_mul hNR.le, Real.sqrt_eq_rpow]
    norm_num
  have hs2' : Real.sqrt 2 ≤ 3 / 2 := by
    have h94 : Real.sqrt ((3 / 2 : ℝ) ^ 2) = 3 / 2 :=
      Real.sqrt_sq (by norm_num)
    rw [← h94]; exact Real.sqrt_le_sqrt (by norm_num)
  have hθ0 := h.theta_pos'
  have hsm : Real.sqrt (2 * (mcut N : ℝ))
      ≤ (3 / 2) * (theta N * bSeq N k₀ * (N : ℝ) ^ ((1 : ℝ) / 4)) := by
    have hR : 2 * (mcut N : ℝ)
        ≤ 2 * (theta N * bSeq N k₀ * (N : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by
      have hexp : (theta N * bSeq N k₀ * (N : ℝ) ^ ((1 : ℝ) / 4)) ^ 2
          = mcutR N := by
        rw [mcutR, mul_pow, mul_pow, hn4sq, ← hk₀]; try ring
      rw [hexp]; linarith [hmc]
    have hQ0 : (0 : ℝ) ≤ theta N * bSeq N k₀ * (N : ℝ) ^ ((1 : ℝ) / 4) := by
      positivity
    calc Real.sqrt (2 * (mcut N : ℝ))
        ≤ Real.sqrt (2 * (theta N * bSeq N k₀ * (N : ℝ) ^ ((1 : ℝ) / 4)) ^ 2) :=
          Real.sqrt_le_sqrt hR
      _ = Real.sqrt 2 * (theta N * bSeq N k₀ * (N : ℝ) ^ ((1 : ℝ) / 4)) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hQ0]
      _ ≤ (3 / 2) * (theta N * bSeq N k₀ * (N : ℝ) ^ ((1 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_right hs2' hQ0
  -- combine
  rw [kimThr6]
  have hstep : 2 * kimBeta N k * Real.sqrt (2 * (mcut N : ℝ))
      ≤ 2 * kimBeta N k
        * ((3 / 2) * (theta N * bSeq N k₀ * (N : ℝ) ^ ((1 : ℝ) / 4))) :=
    mul_le_mul_of_nonneg_left hsm (by positivity)
  have hre : 2 * kimBeta N k
        * ((3 / 2) * (theta N * bSeq N k₀ * (N : ℝ) ^ ((1 : ℝ) / 4)))
      = 3 * theta N * (kimBeta N k * bSeq N k₀) * (N : ℝ) ^ ((1 : ℝ) / 4) := by
    ring
  have hcoef : (0 : ℝ) ≤ 3 * theta N * (N : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  have hstep2 : 3 * theta N * (kimBeta N k * bSeq N k₀) * (N : ℝ) ^ ((1 : ℝ) / 4)
      ≤ 3 * theta N * (3 * Real.log N * Real.sqrt (Real.log N))
        * (N : ℝ) ^ ((1 : ℝ) / 4) := by
    have := mul_le_mul_of_nonneg_left hcoup₀
      (by positivity : (0 : ℝ) ≤ 3 * theta N)
    exact mul_le_mul_of_nonneg_right this hn4.le
  -- the last step is an *equality*: `3θ·3L√L = 9/√L`
  have hfin : 3 * theta N * (3 * Real.log N * Real.sqrt (Real.log N))
        * (N : ℝ) ^ ((1 : ℝ) / 4)
      = 9 * (N : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt (Real.log N) := by
    rw [theta, _root_.eq_div_iff (ne_of_gt hs0)]
    have h1 : 3 * (1 / Real.log N ^ 2)
          * (3 * Real.log N * Real.sqrt (Real.log N))
          * (N : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (Real.log N)
        = 9 * (N : ℝ) ^ ((1 : ℝ) / 4)
          * (Real.sqrt (Real.log N) ^ 2 / Real.log N) := by
      field_simp; try ring
    rw [h1, hsq, div_self (ne_of_gt hL0), mul_one]
  linarith [hstep, hre.le, hre.ge, hstep2, hfin.le, hfin.ge]

/-- `12·(log n)³·ρ₆·thr₆ ≤ 1`: **Kim's tilt `ρ₆ = n^{−1/4−ε₀}`** is admissible,
with `ε₀ := 1/4 − 4/17 = 1/68` (§4.7). -/
lemma KimLarge.rho6_thr6 {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    12 * (Real.log N) ^ 3 * kimRho6 N * kimThr6 N k ≤ 1 := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hL := h.logn_big
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have hs1 : (1 : ℝ) ≤ Real.sqrt (Real.log N) := by
    have h1 : Real.sqrt 1 ≤ Real.sqrt (Real.log N) :=
      Real.sqrt_le_sqrt (by linarith)
    simpa using h1
  have hthr := h.thr6_le hk
  have hcl := h.asym.p6_thr
  have hρ0 : (0 : ℝ) < kimRho6 N := kimRho6_pos hn
  have hpre : (0 : ℝ) ≤ 12 * (Real.log N) ^ 3 * kimRho6 N := by positivity
  have hstep : 12 * (Real.log N) ^ 3 * kimRho6 N * kimThr6 N k
      ≤ 12 * (Real.log N) ^ 3 * kimRho6 N
        * (9 * (N : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt (Real.log N)) :=
    mul_le_mul_of_nonneg_left hthr hpre
  -- `ρ₆·n^{1/4}·n^{1/68} = 1`, i.e. `ρ₆ = n^{−1/4−ε₀}` exactly cancels
  have hn4 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hNR _
  have hn68 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 68) := Real.rpow_pos_of_pos hNR _
  have hone : kimRho6 N * (N : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((1 : ℝ) / 68)
      = 1 := by
    rw [kimRho6, ← Real.rpow_add hNR, ← Real.rpow_add hNR,
      show -((1 : ℝ) / 4) - (1 : ℝ) / 68 + (1 : ℝ) / 4 + (1 : ℝ) / 68 = 0 by
        ring, Real.rpow_zero]
  have hdrop : 9 * (N : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt (Real.log N)
      ≤ 9 * (N : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [div_le_iff₀ hs0]
    nlinarith [hs1, hn4.le]
  have hstep2 : 12 * (Real.log N) ^ 3 * kimRho6 N
        * (9 * (N : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt (Real.log N))
      ≤ 12 * (Real.log N) ^ 3 * kimRho6 N * (9 * (N : ℝ) ^ ((1 : ℝ) / 4)) :=
    mul_le_mul_of_nonneg_left hdrop hpre
  have heq : 12 * (Real.log N) ^ 3 * kimRho6 N * (9 * (N : ℝ) ^ ((1 : ℝ) / 4))
      = 108 * (Real.log N) ^ 3 / (N : ℝ) ^ ((1 : ℝ) / 68) := by
    rw [_root_.eq_div_iff (ne_of_gt hn68)]
    linear_combination (108 * (Real.log N) ^ 3) * hone
  have hfin : 108 * (Real.log N) ^ 3 / (N : ℝ) ^ ((1 : ℝ) / 68) ≤ 1 := by
    rw [div_le_one hn68]; exact hcl
  linarith [hstep, hstep2, heq.le, heq.ge, hfin]

set_option maxHeartbeats 1000000 in
/-- The pure arithmetic behind §4.7's exponent condition. -/
lemma hexpn_p6_core {L b M p t thr m th : ℝ}
    (hL : 13 ≤ L) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hm0 : 0 ≤ m)
    (ht0 : 0 < t) (hthr1 : 1 ≤ thr) {S : ℝ} (hS0 : 0 < S)
    (hth : th = 1 / L ^ 2) (hp : p = th / S)
    (hM0 : 0 ≤ M) (hM : M ≤ b * Real.sqrt L * S)
    (hkey : 12 * L ^ 3 * t * thr ≤ 1)
    (hC : 6 * L ≤ t * (b ^ 2 * th ^ 2 * m)) :
    -(t * (b ^ 2 * th ^ 2 * m * m))
      + t ^ 2 / 2 * (p * ((2 * thr) * (2 * M * (b * (m * m)))
          * Real.exp (t * (2 * thr))))
      ≤ -(3 * m * L) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hth0 : (0 : ℝ) < th := by rw [hth]; positivity
  have hL3 : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ (by linarith)
  have hsqL0 : (0 : ℝ) ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hsqL : Real.sqrt L ≤ L := by nlinarith [hsq, hsqL0, hL0]
  have h12 : 12 * t * thr ≤ 1 := by nlinarith [hkey, hL3, ht0, hthr1]
  have h2tt : t * (2 * thr) ≤ 1 := by nlinarith [h12, ht0, hthr1]
  have hexp3 : Real.exp (t * (2 * thr)) ≤ 3 := by
    have h1 : Real.exp (t * (2 * thr)) ≤ Real.exp 1 := Real.exp_le_exp.mpr h2tt
    have h2 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  have hthr0 : (0 : ℝ) < thr := by linarith
  have hmm0 : (0 : ℝ) ≤ m * m := mul_nonneg hm0 hm0
  have hin : (2 * thr) * (2 * M * (b * (m * m))) * Real.exp (t * (2 * thr))
      ≤ (2 * thr) * (2 * (b * Real.sqrt L * S) * (b * (m * m))) * 3 := by
    have hA : 2 * M * (b * (m * m))
        ≤ 2 * (b * Real.sqrt L * S) * (b * (m * m)) := by
      have h1 : (2 : ℝ) * M ≤ 2 * (b * Real.sqrt L * S) := by linarith
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hA0 : (0 : ℝ) ≤ (2 * thr) * (2 * M * (b * (m * m))) := by positivity
    calc (2 * thr) * (2 * M * (b * (m * m))) * Real.exp (t * (2 * thr))
        ≤ (2 * thr) * (2 * M * (b * (m * m))) * 3 :=
          mul_le_mul_of_nonneg_left hexp3 hA0
      _ ≤ (2 * thr) * (2 * (b * Real.sqrt L * S) * (b * (m * m))) * 3 := by
          have := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ 2 * thr)
          linarith
  have hp0 : (0 : ℝ) ≤ p := by rw [hp]; positivity
  have ht20 : (0 : ℝ) ≤ t ^ 2 / 2 := by positivity
  have hchain := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hin hp0) ht20
  have heq : t ^ 2 / 2 * (p * ((2 * thr)
        * (2 * (b * Real.sqrt L * S) * (b * (m * m))) * 3))
      = 6 * t ^ 2 * th * thr * b ^ 2 * Real.sqrt L * (m * m) := by
    rw [hp]; field_simp; try ring
  have hthrL : 12 * t * thr * Real.sqrt L ≤ th := by
    have h1 : 12 * t * thr * Real.sqrt L ≤ 12 * t * thr * L :=
      mul_le_mul_of_nonneg_left hsqL (by positivity)
    have h2 : 12 * t * thr * L * L ^ 2 ≤ 1 := by nlinarith [hkey]
    have h3 : 12 * t * thr * L ≤ th := by
      rw [hth, le_div_iff₀ (by positivity : (0 : ℝ) < L ^ 2)]
      linarith [h2]
    linarith
  have hhalf : 6 * t ^ 2 * th * thr * b ^ 2 * Real.sqrt L * (m * m)
      ≤ t * (b ^ 2 * th ^ 2 * m * m) / 2 := by
    have hcoef : (0 : ℝ) ≤ t * b ^ 2 * th * (m * m) / 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hthrL hcoef
    nlinarith [hmul]
  have hDft : 6 * L * m ≤ t * (b ^ 2 * th ^ 2 * m * m) := by
    have hm := mul_le_mul_of_nonneg_right hC hm0
    nlinarith [hm]
  linarith [hchain, heq.le, heq.ge, hhalf, hDft]

set_option maxHeartbeats 1000000 in
/-- **Kim's §4.7 exponent condition**, at the tilt `ρ₆`. -/
lemma KimLarge.hexpn_p6 {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    Real.exp (-(kimRho6 N * (bSeq N k ^ 2 * theta N ^ 2
            * (mcut N : ℝ) * (mcut N : ℝ)))
        + kimRho6 N ^ 2 / 2 * (edgeProb N * ((2 * kimThr6 N k)
            * (2 * (kimM N k : ℝ)
              * (bSeq N k * ((mcut N : ℝ) * (mcut N : ℝ))))
            * Real.exp (kimRho6 N * (2 * kimThr6 N k)))))
      ≤ Real.exp (-(3 * (mcut N : ℝ) * Real.log N)) := by
  have hn : 0 < N := h.card_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hn
  have hL := h.logn_big
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hS0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
  have hρ0 : (0 : ℝ) < kimRho6 N := kimRho6_pos hn
  have hm0 : (0 : ℝ) ≤ (mcut N : ℝ) := Nat.cast_nonneg _
  have hρe : kimRho6 N
      = Real.exp (-(((1 : ℝ) / 4 + 1 / 68) * Real.log N)) := by
    rw [kimRho6, Real.rpow_def_of_pos hNR]; congr 1; ring
  -- **Kim's drift beats the `C(n,mcut)²` union bound.**  The exponent is
  -- `1/4 − ε₀ − 4δ = 4·10⁻⁵`, positive only because `δ = 1/17 − 10⁻⁵`.
  have hC : 6 * Real.log N
      ≤ kimRho6 N * (bSeq N k ^ 2 * theta N ^ 2 * (mcut N : ℝ)) := by
    have hpc := h.asym.p6_drift
    have hbsq := h.bSq_ge hk
    have hb0sq := h.bSq_ge (k := ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) le_rfl
    have hmh := h.mcutR_le_two_mcut
    have hsN := sqrtN_eq_exp hn
    have hL4 : (0 : ℝ) < (Real.log N) ^ 4 := by positivity
    have hL8 : (0 : ℝ) < (Real.log N) ^ 8 := by positivity
    set E := Real.exp (-(2 * kimDelta * Real.log N)
        - 4 * Real.sqrt (Real.log N) - 2) with hEdef
    have hE0 : (0 : ℝ) < E := Real.exp_pos _
    set R := Real.exp (-(((1 : ℝ) / 4 + 1 / 68) * Real.log N)) with hRdef
    have hR0 : (0 : ℝ) < R := Real.exp_pos _
    have hX0 : (0 : ℝ) < Real.exp (Real.log N / 2) := Real.exp_pos _
    -- lower bound on `mcut`
    have hmcR : E * Real.exp (Real.log N / 2) / (Real.log N) ^ 4 ≤ mcutR N := by
      have hgoal : mcutR N
          = bSeq N ⌊(N : ℝ) ^ kimDelta / theta N⌋₊ ^ 2
            * Real.exp (Real.log N / 2) / (Real.log N) ^ 4 := by
        rw [mcutR, hsN, theta]; field_simp; try ring
      rw [hgoal]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hb0sq hX0.le) hL4.le
    have hmlow : E * Real.exp (Real.log N / 2) / (2 * (Real.log N) ^ 4)
        ≤ (mcut N : ℝ) := by
      have heq : E * Real.exp (Real.log N / 2) / (2 * (Real.log N) ^ 4)
          = E * Real.exp (Real.log N / 2) / (Real.log N) ^ 4 / 2 := by
        field_simp; try ring
      rw [heq]; linarith [hmcR, hmh]
    have hmlow0 : (0 : ℝ)
        ≤ E * Real.exp (Real.log N / 2) / (2 * (Real.log N) ^ 4) := by
      positivity
    -- lower bound on `ρ₆b²θ²`
    have hlow2 : R * E / (Real.log N) ^ 4
        ≤ kimRho6 N * (bSeq N k ^ 2 * theta N ^ 2) := by
      have hgoal : kimRho6 N * (bSeq N k ^ 2 * theta N ^ 2)
          = R * bSeq N k ^ 2 / (Real.log N) ^ 4 := by
        rw [hρe, theta]; field_simp; try ring
      rw [hgoal]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbsq hR0.le) hL4.le
    have hlow20 : (0 : ℝ) ≤ R * E / (Real.log N) ^ 4 := by positivity
    -- multiply
    have hmul : (R * E / (Real.log N) ^ 4)
          * (E * Real.exp (Real.log N / 2) / (2 * (Real.log N) ^ 4))
        ≤ kimRho6 N * (bSeq N k ^ 2 * theta N ^ 2) * (mcut N : ℝ) :=
      mul_le_mul hlow2 hmlow hmlow0 (by positivity)
    -- identify the product with Kim's exponent
    have hEsq : E ^ 2 = Real.exp (-(4 * kimDelta * Real.log N)
        - 8 * Real.sqrt (Real.log N) - 4) := by
      rw [hEdef, exp_sq]; congr 1; ring
    have hprod : R * E ^ 2 * Real.exp (Real.log N / 2)
        = Real.exp (((1 : ℝ) / 4 - 1 / 68 - 4 * kimDelta) * Real.log N
            - 8 * Real.sqrt (Real.log N) - 4) := by
      rw [hEsq, hRdef, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hcol2 : ∀ x : ℝ,
        x / (2 * (Real.log N) ^ 8) = x / (Real.log N) ^ 8 / 2 := by
      intro x; rw [div_div]; ring_nf
    have hcollapse : (R * E / (Real.log N) ^ 4)
          * (E * Real.exp (Real.log N / 2) / (2 * (Real.log N) ^ 4))
        = Real.exp (((1 : ℝ) / 4 - 1 / 68 - 4 * kimDelta) * Real.log N
            - 8 * Real.sqrt (Real.log N) - 4) / (Real.log N) ^ 8 / 2 := by
      calc (R * E / (Real.log N) ^ 4)
            * (E * Real.exp (Real.log N / 2) / (2 * (Real.log N) ^ 4))
          = R * E ^ 2 * Real.exp (Real.log N / 2)
              / (2 * (Real.log N) ^ 8) := by field_simp; try ring
        _ = Real.exp (((1 : ℝ) / 4 - 1 / 68 - 4 * kimDelta) * Real.log N
              - 8 * Real.sqrt (Real.log N) - 4) / (2 * (Real.log N) ^ 8) := by
              rw [hprod]
        _ = _ := hcol2 _
    have hfin : 6 * Real.log N
        ≤ Real.exp (((1 : ℝ) / 4 - 1 / 68 - 4 * kimDelta) * Real.log N
            - 8 * Real.sqrt (Real.log N) - 4) / (Real.log N) ^ 8 / 2 := by
      linarith [hpc]
    have hassoc : kimRho6 N * (bSeq N k ^ 2 * theta N ^ 2) * (mcut N : ℝ)
        = kimRho6 N * (bSeq N k ^ 2 * theta N ^ 2 * (mcut N : ℝ)) := by ring
    linarith [hmul, hcollapse.le, hcollapse.ge, hfin, hassoc.le, hassoc.ge]
  refine Real.exp_le_exp.mpr ?_
  have hcore := hexpn_p6_core (L := Real.log N) (b := bSeq N k)
    (M := (kimM N k : ℝ)) (p := edgeProb N) (t := kimRho6 N)
    (thr := kimThr6 N k) (m := (mcut N : ℝ)) (S := Real.sqrt N)
    (th := theta N)
    hL (bSeq_pos N k).le (bSeq_le_one N k) hm0 hρ0 (h.thr6_ge_one k) hS0
    (by rw [theta]) rfl (Nat.cast_nonneg _) (h.kimM_le_b hk)
    (h.rho6_thr6 hk) hC
  linarith [hcore]

/-- **The §4.7 union bound closes**: `C(n,mcut)²·exp(−3·mcut·log n) ≤ 1/n`. -/
lemma KimLarge.union6 {N : ℕ} (h : KimLarge N) :
    (Nat.choose N (mcut N) : ℝ) * (Nat.choose N (mcut N) : ℝ)
        * Real.exp (-(3 * (mcut N : ℝ) * Real.log N))
      ≤ 1 / (N : ℝ) := by
  have hn : 0 < N := h.card_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hn
  have hL := h.logn_big
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hmc : 1 ≤ mcut N := h.mcut_pos
  have hmcR : (1 : ℝ) ≤ (mcut N : ℝ) := by exact_mod_cast hmc
  have hpow : ((N : ℝ)) ^ (mcut N) = Real.exp ((mcut N : ℝ) * Real.log N) := by
    rw [Real.exp_nat_mul, Real.exp_log hNR]
  have hc : (Nat.choose N (mcut N) : ℝ)
      ≤ Real.exp ((mcut N : ℝ) * Real.log N) := by
    rw [← hpow]
    exact_mod_cast Nat.choose_le_pow N (mcut N)
  have hc0 : (0 : ℝ) ≤ (Nat.choose N (mcut N) : ℝ) := Nat.cast_nonneg _
  have hE0 : (0 : ℝ) < Real.exp ((mcut N : ℝ) * Real.log N) := Real.exp_pos _
  have hsq : (Nat.choose N (mcut N) : ℝ) * (Nat.choose N (mcut N) : ℝ)
      ≤ Real.exp ((mcut N : ℝ) * Real.log N)
        * Real.exp ((mcut N : ℝ) * Real.log N) :=
    mul_le_mul hc hc hc0 hE0.le
  have hstep : (Nat.choose N (mcut N) : ℝ) * (Nat.choose N (mcut N) : ℝ)
        * Real.exp (-(3 * (mcut N : ℝ) * Real.log N))
      ≤ Real.exp ((mcut N : ℝ) * Real.log N)
        * Real.exp ((mcut N : ℝ) * Real.log N)
        * Real.exp (-(3 * (mcut N : ℝ) * Real.log N)) :=
    mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
  have hcollapse : Real.exp ((mcut N : ℝ) * Real.log N)
        * Real.exp ((mcut N : ℝ) * Real.log N)
        * Real.exp (-(3 * (mcut N : ℝ) * Real.log N))
      = Real.exp (-((mcut N : ℝ) * Real.log N)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hfin : Real.exp (-((mcut N : ℝ) * Real.log N)) ≤ 1 / (N : ℝ) := by
    have h1 : Real.exp (-((mcut N : ℝ) * Real.log N))
        ≤ Real.exp (-Real.log N) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hmcR, hL0]
    have h2 : Real.exp (-Real.log N) = 1 / (N : ℝ) := by
      rw [Real.exp_neg, Real.exp_log hNR, one_div]
    linarith [h1, h2.le, h2.ge]
  linarith [hstep, hcollapse.le, hcollapse.ge, hfin]

/-- `I ≤ 4M`, §4.6's overlap allowance against the padding budget. -/
lemma KimLarge.kimI_le {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    kimI N k ≤ 4 * kimM N k := by
  have hM := h.kimM_ge hk
  have hkle := h.k_le hk
  have hN1 : 1 ≤ N := h.card_pos
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hrp : (1 : ℝ) ≤ (N : ℝ) ^ kimDelta :=
    Real.one_le_rpow hNR kimDelta_pos.le
  have hLe : Real.exp 1 ≤ Real.log N := h.2.2.1
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hL2 : (2 : ℝ) ≤ Real.log N := by linarith
  have hceil := Nat.ceil_lt_add_one
    (show (0 : ℝ) ≤ 4 * (3 * (k : ℝ) * Real.log N + 1) by positivity)
  have hIR : ((kimI N k : ℕ) : ℝ) ≤ 4 * (3 * (k : ℝ) * Real.log N + 1) + 1 := by
    rw [kimI]
    linarith [hceil]
  -- `12·k·L ≤ 12·n^δ·L³` and `20n^δL⁴` dominates
  have hkL : 12 * (k : ℝ) * Real.log N
      ≤ 12 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3) := by
    have hstep : (k : ℝ) * Real.log N
        ≤ ((N : ℝ) ^ kimDelta * (Real.log N) ^ 2) * Real.log N :=
      mul_le_mul_of_nonneg_right hkle (by linarith)
    nlinarith [hstep]
  have hδ14 : (N : ℝ) ^ kimDelta ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
    refine Real.rpow_le_rpow_of_exponent_le hNR ?_
    have := kimDelta_lt; norm_num at this ⊢; linarith
  have hL3 : (8 : ℝ) ≤ (Real.log N) ^ 3 := by
    have h1 : (2 : ℝ) ^ 3 ≤ (Real.log N) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hL2 3
    norm_num at h1; linarith
  have hmono : 12 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3)
      ≤ 12 * ((N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 3) := by
    nlinarith [hδ14, hL3]
  have hrp4 : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.one_le_rpow hNR (by norm_num)
  have hdom : 12 * ((N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 3) + 9
      ≤ 20 * ((N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 4) := by
    nlinarith [hrp4, hL2]
  have hfinal : ((kimI N k : ℕ) : ℝ) ≤ 4 * ((kimM N k : ℕ) : ℝ) := by
    linarith [hIR, hkL, hdom, hM, hmono]
  exact_mod_cast hfinal

/-- The weak form of the `b_min` clause: `b_min·θ·√n ≥ 2`. -/
lemma KimLarge.bmin_two {N : ℕ} (h : KimLarge N) :
    2 ≤ Real.exp (-(kimDelta * Real.log N)
        - 2 * Real.sqrt (kimDelta * Real.log N) - 1)
      * theta N * Real.sqrt N := by
  have hcl := h.bmin1
  have hN1 : 1 ≤ N := h.card_pos
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hrp : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.one_le_rpow hNR (by norm_num)
  have hLe : Real.exp 1 ≤ Real.log N := h.2.2.1
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hL2 : (2 : ℝ) ≤ Real.log N := by linarith
  have hL4 : (2 : ℝ) ≤ Real.log N ^ 4 := by
    have h1 : (2 : ℝ) ^ 4 ≤ Real.log N ^ 4 :=
      pow_le_pow_left₀ (by norm_num) hL2 4
    norm_num at h1
    linarith
  nlinarith [hcl, hrp, hL4]

/-- `2p ≤ 3b_kθ²` for every `k ≤ k₀`. -/
lemma KimLarge.slack {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    2 * edgeProb N ≤ 3 * bSeq N k * theta N ^ 2 := by
  have hN1 : 1 ≤ N := h.card_pos
  have hθpos : 0 < theta N := h.theta_pos'
  have hsq0 : (0 : ℝ) < Real.sqrt (N : ℝ) := by
    have : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := one_le_sqrt_cast hN1
    linarith
  have hbmin := bSeq_ge_of_k_le hN1 hθpos hk
  have hcl := h.bmin_two
  have h1 : Real.exp (-(kimDelta * Real.log N)
        - 2 * Real.sqrt (kimDelta * Real.log N) - 1) * theta N * Real.sqrt N
      ≤ bSeq N k * theta N * Real.sqrt N :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbmin hθpos.le) hsq0.le
  have h2 : (2 : ℝ) ≤ bSeq N k * theta N * Real.sqrt N := by linarith [hcl, h1]
  rw [edgeProb, ← mul_div_assoc, div_le_iff₀ hsq0]
  nlinarith [h2, hθpos]

/-- `b_{k+1} ≤ b_k²θ√n` for every `k ≤ k₀`. -/
lemma KimLarge.bb {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    bSeq N (k + 1) ≤ bSeq N k ^ 2 * theta N * Real.sqrt N := by
  have hN1 : 1 ≤ N := h.card_pos
  have hθpos : 0 < theta N := h.theta_pos'
  have hsq0 : (0 : ℝ) < Real.sqrt (N : ℝ) := by
    have : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := one_le_sqrt_cast hN1
    linarith
  have hbmin := bSeq_ge_of_k_le hN1 hθpos hk
  have hcl := h.bmin_two
  have h1 : Real.exp (-(kimDelta * Real.log N)
        - 2 * Real.sqrt (kimDelta * Real.log N) - 1) * theta N * Real.sqrt N
      ≤ bSeq N k * theta N * Real.sqrt N :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbmin hθpos.le) hsq0.le
  have h2 : (1 : ℝ) ≤ bSeq N k * theta N * Real.sqrt N := by
    linarith [hcl, h1]
  have hle := bSeq_succ_le N k hθpos
  nlinarith [h2, hle, (bSeq_pos N k).le]

/-- `b_k ≤ 2b_{k+1}` for every `k ≤ k₀`. -/
lemma KimLarge.bb2 {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    bSeq N k ≤ 2 * bSeq N (k + 1) := by
  have hN1 : 1 ≤ N := h.card_pos
  have hθpos : 0 < theta N := h.theta_pos'
  have hθ0 : 0 ≤ theta N := hθpos.le
  have hb0 : 0 < bSeq N k := bSeq_pos N k
  have hble : bSeq N k ≤ 1 := bSeq_le_one N k
  have hale := aSeq_le_of_k_le hN1 hθpos hk
  have ha0 : 0 ≤ aSeq N k := aSeq_nonneg N k
  have hcl8 := h.2.2.2.2.2.2.2.2.2.2.2.1
  have hθsmall := h.2.1
  have hratio := bSeq_ratio_lower N k
  have haθ : aSeq N k * theta N ≤ 1 / 8 := by
    nlinarith [hale, hcl8, hθ0]
  have hfac : (1 : ℝ) / 2
      ≤ 1 - 2 * aSeq N k * bSeq N k * theta N - bSeq N k * theta N ^ 2 := by
    have h1 : 2 * aSeq N k * bSeq N k * theta N ≤ 1 / 4 := by
      nlinarith [haθ, hble, hb0.le, ha0, hθ0]
    have h2 : bSeq N k * theta N ^ 2 ≤ 1 / 10000 := by
      nlinarith [hble, hb0.le, hθsmall, hθ0]
    linarith
  nlinarith [hratio, hfac, hb0.le]

open scoped Classical in
/-- **Property 1's bad-event bound**, from `KimLarge` alone. -/
lemma bad1_bound (k : ℕ) (s : BlockState V) (M : ℕ) (hN : KimLarge n)
    (h1 : Property1 s k) (h2 : Property2 s k) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          ¬ Property1 (blockStepP s M σ) (k + 1)))
      ≤ ((n : ℝ) ^ (2 : ℕ))⁻¹ := by
  have hn : 0 < n := hN.card_pos
  have hlogn : 1 ≤ Real.log n := hN.logn_ge_one
  have hlog2 : Real.log 2 ≤ Real.log n := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := by linarith [hN.1]
    exact Real.log_le_log (by norm_num) h2n
  have hvar' : 32 * (bSeq n k * theta n) * Real.exp 1 ≤ 4 * Real.log n := by
    have hb := bSeq_le_one n k
    have hb0 := (bSeq_pos n k).le
    have hθ0 := theta_nonneg n
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hprod : bSeq n k * theta n ≤ theta n := by nlinarith [hb, hθ0]
    have hstep : 32 * (bSeq n k * theta n) * Real.exp 1
        ≤ 32 * theta n * Real.exp 1 := by nlinarith [hprod, he.le]
    linarith [hN.2.2.2.2.2.1, hstep]
  exact property1_numeric k s M hn hlogn h1 h2 hN.2.2.2.2.1 hlog2 hvar'

open scoped Classical in
/-- **Property 3's bad-event bound**, from `KimLarge` and `k ≤ k₀`. -/
lemma bad3_bound (k : ℕ) (s : BlockState V) (M : ℕ) (hN : KimLarge n)
    (hk : k ≤ ⌊(n : ℝ) ^ ((1 : ℝ) / 17 - 10 ^ (-5 : ℤ)) / theta n⌋₊)
    (h1 : Property1 s k) (h3 : Property3 s k) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          ¬ Property3 (blockStepP s M σ) (k + 1))) ≤ 3 / n := by
  have hn : 0 < n := hN.card_pos
  have hlogn : 1 ≤ Real.log n := hN.logn_ge_one
  have hk' : k ≤ ⌊(n : ℝ) ^ kimDelta / theta n⌋₊ := by
    rw [kimDelta]; exact hk
  exact property3_numeric k s M hn hN.theta_pos' hlogn hN.2.2.1 hk' h1 h3
    hN.2.2.2.2.2.2.1 hN.2.2.2.2.2.2.2.1 hN.2.2.2.2.2.2.2.2.1
    hN.2.2.2.2.2.2.2.2.2.1

open scoped Classical in
/-- **Property 2's bad-event bound**, reduced to one numeric inequality
(Kim's §4.3 exponent estimate at `ρ = n^{−3/4}`). -/
lemma bad2_bound (k : ℕ) (s : BlockState V) (hN : KimLarge n)
    (h2 : Property2 s k) (h4 : Property4 s k)
    (hslack : 2 * edgeProb n ≤ 3 * bSeq n k * theta n ^ 2)
    {t : ℝ} (ht : 0 ≤ t)
    (hexp : 3 * Real.log n
      ≤ t * (bSeq n k ^ 2 * theta n ^ 2 * n)
        - t ^ 2 / 2 * (edgeProb n * ((2 * (kimM n k : ℝ))
            * (2 * (kimM n k : ℝ) * (bSeq n k * n))
            * Real.exp (t * (2 * (kimM n k : ℝ)))))) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property2 (blockStepP s (kimM n k) σ) (k + 1)))
      ≤ ((n : ℝ) ^ (2 : ℕ))⁻¹ := by
  have hn : 0 < n := hN.card_pos
  have hlogn : 1 ≤ Real.log n := hN.logn_ge_one
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  refine property2_numeric k s hn hlogn hN.2.1 h2 h4 hslack ht ?_
  intro v
  rw [neg_mul]
  refine exp_le_inv_pow hn 3 ?_
  have hdeg : ((edgesAt s.Γ v).card : ℝ) ≤ bSeq n k * n := by
    have hv := h2 v
    rwa [degEdges] at hv
  have hMnn : (0 : ℝ) ≤ (kimM n k : ℝ) := Nat.cast_nonneg _
  have hE : (0 : ℝ) < Real.exp (t * (2 * (kimM n k : ℝ))) := Real.exp_pos _
  have hZnn : (0 : ℝ) ≤ (2 * (kimM n k : ℝ))
      * (2 * (kimM n k : ℝ) * ((edgesAt s.Γ v).card : ℝ))
      * Real.exp (t * (2 * (kimM n k : ℝ))) := by positivity
  have hZle : (2 * (kimM n k : ℝ))
        * (2 * (kimM n k : ℝ) * ((edgesAt s.Γ v).card : ℝ))
        * Real.exp (t * (2 * (kimM n k : ℝ)))
      ≤ (2 * (kimM n k : ℝ))
        * (2 * (kimM n k : ℝ) * (bSeq n k * n))
        * Real.exp (t * (2 * (kimM n k : ℝ))) := by
    have h1 : (2 * (kimM n k : ℝ) * ((edgesAt s.Γ v).card : ℝ))
        ≤ (2 * (kimM n k : ℝ) * (bSeq n k * n)) :=
      mul_le_mul_of_nonneg_left hdeg (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1
      (by positivity : (0 : ℝ) ≤ 2 * (kimM n k : ℝ))
    exact mul_le_mul_of_nonneg_right h2 hE.le
  have hA : edgeProb n * (1 - edgeProb n)
        * ((2 * (kimM n k : ℝ))
          * (2 * (kimM n k : ℝ) * ((edgesAt s.Γ v).card : ℝ))
          * Real.exp (t * (2 * (kimM n k : ℝ))))
      ≤ edgeProb n * ((2 * (kimM n k : ℝ))
          * (2 * (kimM n k : ℝ) * (bSeq n k * n))
          * Real.exp (t * (2 * (kimM n k : ℝ)))) := by
    have hstep1 : edgeProb n * (1 - edgeProb n)
          * ((2 * (kimM n k : ℝ))
            * (2 * (kimM n k : ℝ) * ((edgesAt s.Γ v).card : ℝ))
            * Real.exp (t * (2 * (kimM n k : ℝ))))
        ≤ edgeProb n * ((2 * (kimM n k : ℝ))
            * (2 * (kimM n k : ℝ) * ((edgesAt s.Γ v).card : ℝ))
            * Real.exp (t * (2 * (kimM n k : ℝ)))) := by
      nlinarith [mul_nonneg hp0 (mul_nonneg hp0 hZnn), hp0, hp1, hZnn]
    have hstep2 := mul_le_mul_of_nonneg_left hZle hp0
    linarith [hstep1, hstep2]
  have hvar : t ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
        * ((2 * (kimM n k : ℝ))
          * (2 * (kimM n k : ℝ) * ((edgesAt s.Γ v).card : ℝ))
          * Real.exp (t * (2 * (kimM n k : ℝ)))))
      ≤ t ^ 2 / 2 * (edgeProb n * ((2 * (kimM n k : ℝ))
          * (2 * (kimM n k : ℝ) * (bSeq n k * n))
          * Real.exp (t * (2 * (kimM n k : ℝ))))) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  push_cast
  linarith [hexp, hvar]

open scoped Classical in
/-- **Property 4's bad-event bound**, reduced to Kim's two exponent estimates
(24) at `ρ = n^{−1/4}` and (27) at `ρ = n^{−1/4−1/17}`. -/
lemma bad4_bound (k : ℕ) (s : BlockState V) (hN : KimLarge n)
    (h3 : Property3 s k) (h4 : Property4 s k) (h5 : Property5 s k)
    (hslack : 2 * edgeProb n ≤ 3 * bSeq n k * theta n ^ 2)
    (hp2 : edgeProb n ≤ 1 / 2)
    (hbb : bSeq n (k + 1) ≤ bSeq n k ^ 2 * theta n * Real.sqrt n)
    {t1 t2 : ℝ} (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2)
    (hexp1 : Real.exp (-(t1 * (bSeq n k ^ 2 * theta n ^ 2
            * (aSeq n k + 5 * theta n) * Real.sqrt n))
        + t1 ^ 2 / 2 * (edgeProb n * ((3 * (k : ℝ) * Real.log n + 2)
            * (2 * (kimM n k : ℝ) * (kimM n k : ℝ))
            * Real.exp (t1 * (3 * (k : ℝ) * Real.log n + 2)))))
      ≤ ((n : ℝ) ^ (4 : ℕ))⁻¹)
    (hvar2 : t2 ^ 2 / 2 * (edgeProb n
        * ((bSeq n k ^ 2 * (n : ℝ)) * Real.exp t2))
      ≤ t2 * (bSeq n k ^ 2 * theta n ^ 2 * (aSeq n k + 5 * theta n)
          * Real.sqrt n) / 2)
    (hexp2 : Real.log 2 + 4 * Real.log n
      ≤ t2 * (bSeq n k ^ 2 * theta n ^ 2 * (aSeq n k + 5 * theta n)
          * Real.sqrt n) / 2) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property4 (blockStepP s (kimM n k) σ) (k + 1)))
      ≤ 2 * ((Fintype.card (Edge V) : ℝ) * n) * ((n : ℝ) ^ (4 : ℕ))⁻¹ := by
  have hn : 0 < n := hN.card_pos
  have hlogn : 1 ≤ Real.log n := hN.logn_ge_one
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  have hC0 : (0 : ℝ) ≤ 3 * (k : ℝ) * Real.log n := by positivity
  have hbound : ∀ w w' : V, w ≠ w' →
      ((commonNbrs s.E w w').card : ℝ) ≤ 3 * (k : ℝ) * Real.log n :=
    fun w w' hww' => h3 w w' hww'
  refine property4_numeric k s hn hlogn hN.2.1 h4 h5 hslack hp2 hbb hC0 hbound
    ht1 ht2 ?_ ?_ hexp2
  · -- (27)
    intro e he v hv
    refine le_trans (Real.exp_le_exp.mpr ?_) hexp1
    have hlamM : ((lambdaAt s e v).card : ℝ) ≤ (kimM n k : ℝ) := by
      exact_mod_cast lambdaAt_card_le_kimM k s h4 e he v hv
    have hMnn : (0 : ℝ) ≤ (kimM n k : ℝ) := Nat.cast_nonneg _
    have hCnn : (0 : ℝ) ≤ 3 * (k : ℝ) * Real.log n + 2 := by linarith
    have hE : (0 : ℝ) < Real.exp (t1 * (3 * (k : ℝ) * Real.log n + 2)) :=
      Real.exp_pos _
    have hstep : (3 * (k : ℝ) * Real.log n + 2)
          * (2 * (kimM n k : ℝ) * ((lambdaAt s e v).card : ℝ))
          * Real.exp (t1 * (3 * (k : ℝ) * Real.log n + 2))
        ≤ (3 * (k : ℝ) * Real.log n + 2)
          * (2 * (kimM n k : ℝ) * (kimM n k : ℝ))
          * Real.exp (t1 * (3 * (k : ℝ) * Real.log n + 2)) := by
      have h1 : 2 * (kimM n k : ℝ) * ((lambdaAt s e v).card : ℝ)
          ≤ 2 * (kimM n k : ℝ) * (kimM n k : ℝ) :=
        mul_le_mul_of_nonneg_left hlamM (by positivity)
      have h2 := mul_le_mul_of_nonneg_left h1 hCnn
      exact mul_le_mul_of_nonneg_right h2 hE.le
    have hZnn : (0 : ℝ) ≤ (3 * (k : ℝ) * Real.log n + 2)
        * (2 * (kimM n k : ℝ) * ((lambdaAt s e v).card : ℝ))
        * Real.exp (t1 * (3 * (k : ℝ) * Real.log n + 2)) := by positivity
    have hA : edgeProb n * (1 - edgeProb n)
          * ((3 * (k : ℝ) * Real.log n + 2)
            * (2 * (kimM n k : ℝ) * ((lambdaAt s e v).card : ℝ))
            * Real.exp (t1 * (3 * (k : ℝ) * Real.log n + 2)))
        ≤ edgeProb n * ((3 * (k : ℝ) * Real.log n + 2)
            * (2 * (kimM n k : ℝ) * (kimM n k : ℝ))
            * Real.exp (t1 * (3 * (k : ℝ) * Real.log n + 2))) := by
      have hstep1 : edgeProb n * (1 - edgeProb n)
            * ((3 * (k : ℝ) * Real.log n + 2)
              * (2 * (kimM n k : ℝ) * ((lambdaAt s e v).card : ℝ))
              * Real.exp (t1 * (3 * (k : ℝ) * Real.log n + 2)))
          ≤ edgeProb n * ((3 * (k : ℝ) * Real.log n + 2)
              * (2 * (kimM n k : ℝ) * ((lambdaAt s e v).card : ℝ))
              * Real.exp (t1 * (3 * (k : ℝ) * Real.log n + 2))) := by
        nlinarith [mul_nonneg hp0 (mul_nonneg hp0 hZnn), hp0, hp1, hZnn]
      have hstep2 := mul_le_mul_of_nonneg_left hstep hp0
      linarith [hstep1, hstep2]
    have hfin := mul_le_mul_of_nonneg_left hA
      (by positivity : (0 : ℝ) ≤ t1 ^ 2 / 2)
    linarith [hfin]
  · -- (24)
    intro e he v hv
    refine le_trans ?_ hvar2
    have hΔ : ((deltaEdgesAt s v (otherEndOf v e)).card : ℝ)
        ≤ bSeq n k ^ 2 * (n : ℝ) := by
      have hve : v ∈ e.val := mem_edgeVerts.mp hv
      set w : V := otherEndOf v e with hw
      have hspec : e.val = s(v, w) := edge_eq_of_otherEndOf hve
      have hvw : v ≠ w := by
        intro hEq
        exact e.2 (by rw [hspec, ← hEq]; simp)
      have hmk : mkEdge hvw = e := Subtype.ext (by rw [mkEdge_val, hspec])
      have hcod := h5 v w hvw (by rw [hmk]; exact he)
      have hd : ((deltaEdgesAt s v w).card : ℝ)
          ≤ (codegEdges s.Γ v w : ℝ) := by
        exact_mod_cast card_deltaEdgesAt_le s v w
      linarith [hd, hcod]
    have hE : (0 : ℝ) < Real.exp t2 := Real.exp_pos _
    have hpp : (0 : ℝ) ≤ edgeProb n * (1 - edgeProb n) :=
      mul_nonneg hp0 (by linarith)
    have hle : edgeProb n * (1 - edgeProb n) ≤ edgeProb n := by
      nlinarith [hp0, hp1]
    have hstep : ((deltaEdgesAt s v (otherEndOf v e)).card : ℝ) * Real.exp t2
        ≤ (bSeq n k ^ 2 * (n : ℝ)) * Real.exp t2 :=
      mul_le_mul_of_nonneg_right hΔ hE.le
    have hnn : (0 : ℝ) ≤ ((deltaEdgesAt s v (otherEndOf v e)).card : ℝ)
        * Real.exp t2 := by positivity
    have hA : edgeProb n * (1 - edgeProb n)
          * (((deltaEdgesAt s v (otherEndOf v e)).card : ℝ) * Real.exp t2)
        ≤ edgeProb n * ((bSeq n k ^ 2 * (n : ℝ)) * Real.exp t2) := by
      have hstep1 : edgeProb n * (1 - edgeProb n)
            * (((deltaEdgesAt s v (otherEndOf v e)).card : ℝ) * Real.exp t2)
          ≤ edgeProb n
            * (((deltaEdgesAt s v (otherEndOf v e)).card : ℝ)
              * Real.exp t2) := by
        nlinarith [mul_nonneg hp0 (mul_nonneg hp0 hnn), hp0, hp1, hnn]
      have hstep2 := mul_le_mul_of_nonneg_left hstep hp0
      linarith [hstep1, hstep2]
    have hfin := mul_le_mul_of_nonneg_left hA
      (by positivity : (0 : ℝ) ≤ t2 ^ 2 / 2)
    linarith [hfin]

open scoped Classical in
/-- **Property 5's bad-event bound**, reduced to Kim's §4.6 exponent estimate at
`ρ = n^{−5/8}`. -/
lemma bad5_bound (k : ℕ) (s : BlockState V) (hN : KimLarge n)
    (h3 : Property3 s k) (h4 : Property4 s k) (h5 : Property5 s k)
    (hslack : 2 * edgeProb n ≤ 3 * bSeq n k * theta n ^ 2)
    (hbb2 : bSeq n k ≤ 2 * bSeq n (k + 1))
    {I : ℕ} (hI : 4 * (3 * (k : ℝ) * Real.log n + 1) ≤ (I : ℝ))
    (hI4M : I ≤ 4 * kimM n k)
    (hIp2 : 2 * (I : ℝ) * edgeProb n ≤ 1)
    (hIp : 2 * (I : ℝ) * edgeProb n * bSeq n (k + 1) ^ 2
      ≤ 2 * bSeq n k ^ 3 * theta n ^ 2)
    {t : ℝ} (ht : 0 ≤ t)
    (hexp : 3 * Real.log n
      ≤ t * (bSeq n k ^ 3 * theta n ^ 2 * n)
        - t ^ 2 / 2 * (edgeProb n * ((2 * (kimM n k : ℝ) + 4)
            * (4 * (kimM n k : ℝ) * (bSeq n k ^ 2 * (n : ℝ)))
            * Real.exp (t * (2 * (kimM n k : ℝ) + 4))))) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property5 (blockStepP s (kimM n k) σ) (k + 1))) ≤ 1 / n := by
  have hn : 0 < n := hN.card_pos
  have hlogn : 1 ≤ Real.log n := hN.logn_ge_one
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  refine property5_numeric k s hn hlogn hN.2.1 h3 h4 h5 hslack hbb2 hI hI4M
    hIp2 hIp ht ?_
  intro v w hvw hmem
  rw [neg_mul]
  refine exp_le_inv_pow hn 3 ?_
  have hcod : ((commonNbrs s.Γ v w).card : ℝ) ≤ bSeq n k ^ 2 * (n : ℝ) := by
    have hc := h5 v w hvw hmem
    rwa [codegEdges] at hc
  have hE : (0 : ℝ) < Real.exp (t * (2 * (kimM n k : ℝ) + 4)) := Real.exp_pos _
  have hMnn : (0 : ℝ) ≤ (kimM n k : ℝ) := Nat.cast_nonneg _
  have hZnn : (0 : ℝ) ≤ (2 * (kimM n k : ℝ) + 4)
      * (4 * (kimM n k : ℝ) * ((commonNbrs s.Γ v w).card : ℝ))
      * Real.exp (t * (2 * (kimM n k : ℝ) + 4)) := by positivity
  have hstep : (2 * (kimM n k : ℝ) + 4)
        * (4 * (kimM n k : ℝ) * ((commonNbrs s.Γ v w).card : ℝ))
        * Real.exp (t * (2 * (kimM n k : ℝ) + 4))
      ≤ (2 * (kimM n k : ℝ) + 4)
        * (4 * (kimM n k : ℝ) * (bSeq n k ^ 2 * (n : ℝ)))
        * Real.exp (t * (2 * (kimM n k : ℝ) + 4)) := by
    have h1 : 4 * (kimM n k : ℝ) * ((commonNbrs s.Γ v w).card : ℝ)
        ≤ 4 * (kimM n k : ℝ) * (bSeq n k ^ 2 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hcod (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1
      (by positivity : (0 : ℝ) ≤ 2 * (kimM n k : ℝ) + 4)
    exact mul_le_mul_of_nonneg_right h2 hE.le
  have hA : edgeProb n * (1 - edgeProb n)
        * ((2 * (kimM n k : ℝ) + 4)
          * (4 * (kimM n k : ℝ) * ((commonNbrs s.Γ v w).card : ℝ))
          * Real.exp (t * (2 * (kimM n k : ℝ) + 4)))
      ≤ edgeProb n * ((2 * (kimM n k : ℝ) + 4)
          * (4 * (kimM n k : ℝ) * (bSeq n k ^ 2 * (n : ℝ)))
          * Real.exp (t * (2 * (kimM n k : ℝ) + 4))) := by
    have hstep1 : edgeProb n * (1 - edgeProb n)
          * ((2 * (kimM n k : ℝ) + 4)
            * (4 * (kimM n k : ℝ) * ((commonNbrs s.Γ v w).card : ℝ))
            * Real.exp (t * (2 * (kimM n k : ℝ) + 4)))
        ≤ edgeProb n * ((2 * (kimM n k : ℝ) + 4)
            * (4 * (kimM n k : ℝ) * ((commonNbrs s.Γ v w).card : ℝ))
            * Real.exp (t * (2 * (kimM n k : ℝ) + 4))) := by
      nlinarith [mul_nonneg hp0 (mul_nonneg hp0 hZnn), hp0, hp1, hZnn]
    have hstep2 := mul_le_mul_of_nonneg_left hstep hp0
    linarith [hstep1, hstep2]
  have hfin := mul_le_mul_of_nonneg_left hA
    (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)
  push_cast
  linarith [hexp, hfin]

open scoped Classical in
/-- **Property 6's bad-event bound**, reduced to Kim's §4.7 exponent estimate at
`ρ = n^{−1/4−1/68}`. -/
lemma bad6_bound (k : ℕ) (s : BlockState V) (hN : KimLarge n)
    (h3 : Property3 s k) (h4 : Property4 s k) (h6 : Property6 s k)
    (hslack : 2 * edgeProb n ≤ 3 * bSeq n k * theta n ^ 2)
    (hbb2 : bSeq n k ≤ 2 * bSeq n (k + 1))
    (hcut : 1 ≤ mcut n)
    (hβ1 : 1 ≤ Real.sqrt (3 * ((k : ℝ) + 1) * Real.log n))
    (hβcut : 2 * Real.sqrt (3 * ((k : ℝ) + 1) * Real.log n)
      ≤ Real.sqrt ((mcut n : ℝ)))
    (thr : ℝ) (hthr1 : 1 ≤ thr)
    (hthrge : 2 * Real.sqrt (3 * ((k : ℝ) + 1) * Real.log n)
      * Real.sqrt (2 * (mcut n : ℝ)) ≤ thr)
    {D : ℕ}
    (hD : Real.sqrt (2 * (mcut n : ℝ))
      / Real.sqrt (3 * ((k : ℝ) + 1) * Real.log n) ≤ (D : ℝ))
    (hD2M : 2 * D ≤ 2 * kimM n k)
    (hDp2 : 4 * (D : ℝ) * edgeProb n ≤ 1)
    (hDp : 4 * (D : ℝ) * edgeProb n ≤ 4 * bSeq n k ^ 2 * theta n ^ 2)
    {t : ℝ} (ht : 0 ≤ t) {q1 : ℝ} (hq1 : 0 ≤ q1)
    (hexpn : Real.exp (-(t * (bSeq n k ^ 2 * theta n ^ 2
            * (mcut n : ℝ) * (mcut n : ℝ)))
        + t ^ 2 / 2 * (edgeProb n * ((2 * thr)
            * (2 * (kimM n k : ℝ)
              * (bSeq n k * ((mcut n : ℝ) * (mcut n : ℝ))))
            * Real.exp (t * (2 * thr))))) ≤ q1) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property6 (blockStepP s (kimM n k) σ) (k + 1)))
      ≤ ((n : ℕ).choose (mcut n) : ℝ) * ((n : ℕ).choose (mcut n) : ℝ) * q1 := by
  have hn : 0 < n := hN.card_pos
  have hlogn : 1 ≤ Real.log n := hN.logn_ge_one
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  refine property6_numeric k s hn hlogn hN.2.1 h3 h4 h6 hslack hbb2 hcut hβ1
    hβcut thr hthr1 hthrge hD hD2M hDp2 hDp ht hq1 ?_
  intro A B hABdisj hAcard hBcard
  refine le_trans (Real.exp_le_exp.mpr ?_) hexpn
  have hG : ((gammaBetween s.Γ A B).card : ℝ)
      ≤ bSeq n k * ((mcut n : ℝ) * (mcut n : ℝ)) := by
    have hc := h6 A B hABdisj (le_of_eq hAcard.symm) (le_of_eq hBcard.symm)
    rw [hAcard, hBcard] at hc
    linarith [hc]
  have hE : (0 : ℝ) < Real.exp (t * (2 * thr)) := Real.exp_pos _
  have hthrnn : (0 : ℝ) ≤ 2 * thr := by linarith
  have hMnn : (0 : ℝ) ≤ (kimM n k : ℝ) := Nat.cast_nonneg _
  have hZnn : (0 : ℝ) ≤ (2 * thr)
      * (2 * (kimM n k : ℝ) * ((gammaBetween s.Γ A B).card : ℝ))
      * Real.exp (t * (2 * thr)) := by positivity
  have hstep : (2 * thr)
        * (2 * (kimM n k : ℝ) * ((gammaBetween s.Γ A B).card : ℝ))
        * Real.exp (t * (2 * thr))
      ≤ (2 * thr)
        * (2 * (kimM n k : ℝ) * (bSeq n k * ((mcut n : ℝ) * (mcut n : ℝ))))
        * Real.exp (t * (2 * thr)) := by
    have h1 : 2 * (kimM n k : ℝ) * ((gammaBetween s.Γ A B).card : ℝ)
        ≤ 2 * (kimM n k : ℝ) * (bSeq n k * ((mcut n : ℝ) * (mcut n : ℝ))) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 hthrnn
    exact mul_le_mul_of_nonneg_right h2 hE.le
  have hA : edgeProb n * (1 - edgeProb n)
        * ((2 * thr)
          * (2 * (kimM n k : ℝ) * ((gammaBetween s.Γ A B).card : ℝ))
          * Real.exp (t * (2 * thr)))
      ≤ edgeProb n * ((2 * thr)
          * (2 * (kimM n k : ℝ) * (bSeq n k * ((mcut n : ℝ) * (mcut n : ℝ))))
          * Real.exp (t * (2 * thr))) := by
    have hstep1 : edgeProb n * (1 - edgeProb n)
          * ((2 * thr)
            * (2 * (kimM n k : ℝ) * ((gammaBetween s.Γ A B).card : ℝ))
            * Real.exp (t * (2 * thr)))
        ≤ edgeProb n * ((2 * thr)
            * (2 * (kimM n k : ℝ) * ((gammaBetween s.Γ A B).card : ℝ))
            * Real.exp (t * (2 * thr))) := by
      nlinarith [mul_nonneg hp0 (mul_nonneg hp0 hZnn), hp0, hp1, hZnn]
    have hstep2 := mul_le_mul_of_nonneg_left hstep hp0
    linarith [hstep1, hstep2]
  have hfin := mul_le_mul_of_nonneg_left hA
    (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)
  have hneg : -t * (bSeq n k ^ 2 * theta n ^ 2 * (mcut n : ℝ) * (mcut n : ℝ))
      = -(t * (bSeq n k ^ 2 * theta n ^ 2 * (mcut n : ℝ) * (mcut n : ℝ))) := by
    ring
  rw [hneg]
  linarith [hfin]

open scoped Classical in
/-- **Property 2's failure probability**, fully instantiated. -/
lemma bad2_final (k : ℕ) (s : BlockState V) (hN : KimLarge n)
    (hk : k ≤ ⌊(n : ℝ) ^ kimDelta / theta n⌋₊)
    (h2 : Property2 s k) (h4 : Property4 s k) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property2 (blockStepP s (kimM n k) σ) (k + 1)))
      ≤ ((n : ℝ) ^ (2 : ℕ))⁻¹ :=
  bad2_bound k s hN h2 h4 (hN.slack hk) (kimRho2_nonneg n) (hN.hexp_p2 hk)

open scoped Classical in
/-- **Property 4's failure probability**, fully instantiated. -/
lemma bad4_final (k : ℕ) (s : BlockState V) (hN : KimLarge n)
    (hk : k ≤ ⌊(n : ℝ) ^ kimDelta / theta n⌋₊)
    (h3 : Property3 s k) (h4 : Property4 s k) (h5 : Property5 s k) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property4 (blockStepP s (kimM n k) σ) (k + 1)))
      ≤ 2 * ((Fintype.card (Edge V) : ℝ) * n) * ((n : ℝ) ^ (4 : ℕ))⁻¹ :=
  bad4_bound k s hN h3 h4 h5 (hN.slack hk) hN.edgeProb_le_half (hN.bb hk)
    (kimRho4b_nonneg n) (by positivity) (hN.hexp1_p4 hk) hN.hvar2_p4
    (hN.hexp2_p4 hk)

open scoped Classical in
/-- **Property 5's failure probability**, fully instantiated. -/
lemma bad5_final (k : ℕ) (s : BlockState V) (hN : KimLarge n)
    (hk : k ≤ ⌊(n : ℝ) ^ kimDelta / theta n⌋₊)
    (h3 : Property3 s k) (h4 : Property4 s k) (h5 : Property5 s k) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property5 (blockStepP s (kimM n k) σ) (k + 1)))
      ≤ 1 / n :=
  bad5_bound k s hN h3 h4 h5 (hN.slack hk) (hN.bb2 hk) (kimI_ge n k)
    (hN.kimI_le hk) (hN.kimI_p_le hk) (hN.kimI_bb_le hk)
    (kimRho5_nonneg n) (hN.hexp_p5 hk)

open scoped Classical in
/-- **Property 6's failure probability**, fully instantiated. -/
lemma bad6_final (k : ℕ) (s : BlockState V) (hN : KimLarge n)
    (hk : k ≤ ⌊(n : ℝ) ^ kimDelta / theta n⌋₊)
    (h3 : Property3 s k) (h4 : Property4 s k) (h6 : Property6 s k) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property6 (blockStepP s (kimM n k) σ) (k + 1)))
      ≤ 1 / n := by
  refine le_trans (bad6_bound k s hN h3 h4 h6 (hN.slack hk) (hN.bb2 hk)
    hN.mcut_pos (hN.beta_ge_one k) (hN.beta_le_sqrt_mcut hk)
    (kimThr6 n k) (hN.thr6_ge_one k) (by rw [kimThr6, kimBeta])
    (kimDpar_ge n k) (hN.kimDpar_le hk) (hN.kimDpar_p_le_one hk)
    (hN.kimDpar_p_le hk) (kimRho6_nonneg n) (Real.exp_pos _).le
    (hN.hexpn_p6 hk)) hN.union6

open scoped Classical in
open scoped Classical in
/-- **Lemma 4.3(i), global form.**  The sampled degree of `w` in the whole
vertex set — no `T` — so the event is available for a union over all `T ∈ 𝒯`
at cost `1` rather than `C(n,t)`. -/
lemma sample_deg_bound (k : ℕ) (s : BlockState V) (M : ℕ)
    (hN : KimLarge n) (h2 : Property2 s k) (w : V) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
          bSeq n k * theta n * Real.sqrt n
              + (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log n
            < ((degEdges (sampleP s M σ) w : ℕ) : ℝ)))
      ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹ := by
  have hn : 0 < n := hN.card_pos
  have hlogn : 1 ≤ Real.log n := hN.logn_ge_one
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  have hlog2 : Real.log 2 ≤ Real.log n := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := by linarith [hN.1]
    exact Real.log_le_log (by norm_num) h2n
  have hvar' : 32 * (bSeq n k * theta n) * Real.exp 1 ≤ 4 * Real.log n := by
    have hb := bSeq_le_one n k
    have hθ0 := theta_nonneg n
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hprod : bSeq n k * theta n ≤ theta n := by nlinarith [hb, hθ0]
    have hstep : 32 * (bSeq n k * theta n) * Real.exp 1
        ≤ 32 * theta n * Real.exp 1 := by nlinarith [hprod, he.le]
    linarith [hN.2.2.2.2.2.1, hstep]
  have hmean := edgeProb_mul_degGamma_le s k w hn h2
  refine le_trans (bernoulliPr_mono hp0 hp1 ?_)
    (lemma43_i_numeric s M k w hn hlogn hmean hN.2.2.2.2.1 hlog2 hvar')
  intro σ hσ
  obtain ⟨-, hgt⟩ := Finset.mem_filter.mp hσ
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  linarith [hmean, hgt]

open scoped Classical in
/-- **The global good event of §4.8**: Property 3 survives the step, and no
vertex acquires too many sampled neighbours.  Both are `T`-free, so the union
over `𝒯` costs nothing. -/
noncomputable def goodSample (s : BlockState V) (M k : ℕ) (Dx : ℝ) :
    Finset (Fin (Fintype.card (Coord V M)) → Bool) := by
  classical
  exact Finset.univ.filter (fun σ =>
    Property3 (blockStepP s M σ) (k + 1)
      ∧ ∀ v : V, ((degEdges (sampleP s M σ) v : ℕ) : ℝ) ≤ Dx)

open scoped Classical in
lemma mem_goodSample {s : BlockState V} {M k : ℕ} {Dx : ℝ}
    {σ : Fin (Fintype.card (Coord V M)) → Bool} :
    σ ∈ goodSample s M k Dx ↔ Property3 (blockStepP s M σ) (k + 1)
      ∧ ∀ v : V, ((degEdges (sampleP s M σ) v : ℕ) : ℝ) ≤ Dx := by
  classical
  show σ ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

open scoped Classical in
/-- The good event fails with probability `3/n + n⁻²`. -/
lemma bernoulliPr_goodSample_compl (k : ℕ) (s : BlockState V) (hN : KimLarge n)
    (hk : k ≤ ⌊(n : ℝ) ^ ((1 : ℝ) / 17 - 10 ^ (-5 : ℤ)) / theta n⌋₊)
    (h1 : Property1 s k) (h2 : Property2 s k) (h3 : Property3 s k) :
    bernoulliPr (edgeProb n) (Finset.univ \ goodSample s (kimM n k) k
        (bSeq n k * theta n * Real.sqrt n
          + (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log n))
      ≤ 3 / n + (n : ℝ) * ((n : ℝ) ^ (3 : ℕ))⁻¹ := by
  classical
  have hn : 0 < n := hN.card_pos
  have hlogn : 1 ≤ Real.log n := hN.logn_ge_one
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  set Dx : ℝ := bSeq n k * theta n * Real.sqrt n
    + (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log n with hDxdef
  refine le_trans (bernoulliPr_mono hp0 hp1 (?_ :
      _ ⊆ (Finset.univ.filter
          (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
            ¬ Property3 (blockStepP s (kimM n k) σ) (k + 1)))
        ∪ (Finset.univ : Finset V).biUnion (fun v =>
            Finset.univ.filter (fun σ =>
              Dx < ((degEdges (sampleP s (kimM n k) σ) v : ℕ) : ℝ))))) ?_
  · intro σ hσ
    have hnot : σ ∉ goodSample s (kimM n k) k Dx := (Finset.mem_sdiff.mp hσ).2
    rw [mem_goodSample] at hnot
    push_neg at hnot
    by_cases h3' : Property3 (blockStepP s (kimM n k) σ) (k + 1)
    · obtain ⟨v, hv⟩ := hnot h3'
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨v, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3'⟩)
  · refine le_trans (bernoulliPr_union_le hp0 hp1 _ _) ?_
    have hA := bad3_bound k s (kimM n k) hN hk h1 h3
    have hB := bernoulliPr_biUnion_le hp0 hp1 (Finset.univ : Finset V)
      (fun v => Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          Dx < ((degEdges (sampleP s (kimM n k) σ) v : ℕ) : ℝ)))
    have hC : ∑ v : V, bernoulliPr (edgeProb n) (Finset.univ.filter
          (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
            Dx < ((degEdges (sampleP s (kimM n k) σ) v : ℕ) : ℝ)))
        ≤ (n : ℝ) * ((n : ℝ) ^ (3 : ℕ))⁻¹ := by
      refine le_trans (Finset.sum_le_sum
        (g := fun _ : V => ((n : ℝ) ^ (3 : ℕ))⁻¹) fun v _ => ?_) ?_
      · exact sample_deg_bound k s (kimM n k) hN h2 v
      · rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    linarith [hA, hB, hC]

open scoped Classical in
/-- **Kim (40) as a set inclusion.**  The `Y⁽²⁾` count exceeds its
deterministic bound only *off* the global good event — so the union over
`T ∈ 𝒯` costs nothing. -/
lemma killedY2_subset_bad (s : BlockState V) (M : ℕ) (k : ℕ) (T : Finset V)
    {β γ : ℝ} (hβ1 : 1 ≤ β) (hγ1 : 1 ≤ γ)
    (hβT : β ≤ Real.sqrt T.card / 2) (hTpos : 0 < T.card)
    {thr : ℝ} (hthr : thr = 2 * β * Real.sqrt T.card)
    {cut : ℝ} (hcut0 : 0 ≤ cut) (hβγT : 2 * β * γ * Real.sqrt T.card ≤ cut)
    {Dx b : ℝ} (hb0 : 0 ≤ b)
    (h6 : ∀ A B : Finset V, Disjoint A B → cut ≤ (A.card : ℝ) →
      cut ≤ (B.card : ℝ) →
      ((gammaBetween s.Γ A B).card : ℝ) ≤ b * A.card * B.card)
    (hβ3 : 3 * ((k : ℝ) + 1) * Real.log n ≤ β ^ 2) :
    Finset.univ.filter (fun σ : Fin (Fintype.card (Coord V M)) → Bool =>
        cut * ((T.card : ℝ) + (T.card : ℝ) / 2)
          + b * Dx * ((T.card : ℝ) + (T.card : ℝ) / (2 * γ ^ 2))
            < ((killedY2 s M T thr σ).card : ℝ))
      ⊆ Finset.univ \ goodSample s M k Dx := by
  classical
  intro σ hσ
  obtain ⟨-, hgt⟩ := Finset.mem_filter.mp hσ
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
  intro hgood
  obtain ⟨h3, hdeg⟩ := mem_goodSample.mp hgood
  have hDxgood : ∀ w : V, ((nbrs (sampleP s M σ) w ∩ T).card : ℝ) ≤ Dx := by
    intro w
    refine le_trans ?_ (hdeg w)
    have h1 : (nbrs (sampleP s M σ) w ∩ T).card
        ≤ (nbrs (sampleP s M σ) w).card :=
      Finset.card_le_card Finset.inter_subset_left
    have h2' : (nbrs (sampleP s M σ) w).card = degEdges (sampleP s M σ) w :=
      card_nbrs_eq_degEdges _ _
    rw [h2'] at h1
    exact_mod_cast h1
  have hcodeg : ∀ v w : V, v ≠ w →
      ((commonNbrs (blockStepP s M σ).E v w).card : ℝ) ≤ β ^ 2 := by
    intro v w hvw
    refine le_trans (h3 v w hvw) (le_trans ?_ hβ3)
    push_cast
    linarith
  exact absurd (card_killedY2_le s M σ T hβ1 hγ1 hβT hTpos hthr hcut0 hβγT
    hDxgood hb0 h6 hcodeg) (not_le.mpr hgt)

open scoped Classical in
/-- **Kim's (40)**, in the form Property 7 consumes: a set inclusion into the
global bad event. -/
lemma bad7_hb2' (k : ℕ) (s : BlockState V) (hN : KimLarge n)
    (h6 : Property6 s k)
    {β γ : ℝ} (hβ1 : 1 ≤ β) (hγ1 : 1 ≤ γ)
    (hβT : β ≤ Real.sqrt ((tParam n : ℕ) : ℝ) / 2) (hTpos : 0 < tParam n)
    (thr : ℝ) (hthr : thr = 2 * β * Real.sqrt ((tParam n : ℕ) : ℝ))
    (hβγT : 2 * β * γ * Real.sqrt ((tParam n : ℕ) : ℝ) ≤ (mcut n : ℝ))
    (hβ3 : 3 * ((k : ℝ) + 1) * Real.log n ≤ β ^ 2)
    {Dx : ℝ} (hDxdef : Dx = bSeq n k * theta n * Real.sqrt n
      + (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log n) :
    ∀ T ∈ calT s, Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          (mcut n : ℝ) * (((tParam n : ℕ) : ℝ) + ((tParam n : ℕ) : ℝ) / 2)
            + bSeq n k * Dx
              * (((tParam n : ℕ) : ℝ)
                + ((tParam n : ℕ) : ℝ) / (2 * γ ^ 2))
            < ((killedY2 s (kimM n k) T thr σ).card : ℝ))
      ⊆ Finset.univ \ goodSample s (kimM n k) k Dx := by
  intro T hT
  have hcardT : T.card = tParam n := card_of_mem_calT hT
  have hcut0 : (0 : ℝ) ≤ (mcut n : ℝ) := Nat.cast_nonneg _
  have hβT' : β ≤ Real.sqrt (T.card : ℝ) / 2 := by rw [hcardT]; exact hβT
  have hTpos' : 0 < T.card := by rw [hcardT]; exact hTpos
  have hthr' : thr = 2 * β * Real.sqrt (T.card : ℝ) := by
    rw [hcardT]; exact hthr
  have hβγT' : 2 * β * γ * Real.sqrt (T.card : ℝ) ≤ (mcut n : ℝ) := by
    rw [hcardT]; exact hβγT
  have h6' : ∀ A B : Finset V, Disjoint A B → (mcut n : ℝ) ≤ (A.card : ℝ) →
      (mcut n : ℝ) ≤ (B.card : ℝ) →
      ((gammaBetween s.Γ A B).card : ℝ) ≤ bSeq n k * A.card * B.card := by
    intro A B hAB hA hB
    refine h6 A B hAB ?_ ?_
    · exact_mod_cast hA
    · exact_mod_cast hB
  have hres := killedY2_subset_bad s (kimM n k) k T (Dx := Dx) hβ1 hγ1 hβT'
    hTpos' hthr' hcut0 hβγT' (bSeq_pos n k).le h6' hβ3
  rw [hcardT] at hres
  exact hres

open scoped Classical in
/-- **Kim (47), with the truncation excess (54) folded in.**  The `Φ⁽⁵⁾` half
is Kahn with Lipschitz constant `4h`, the `Φ⁽⁶⁾` half is supplied, and the
excess `Φ⁽⁴⁾` is bounded deterministically on `goodSample`. -/
lemma bad7_hb4' (k : ℕ) (s : BlockState V) (hN : KimLarge n)
    (h5 : Property5 s k) (h6 : Property6 s k) (hh : ℕ)
    {GG : ℝ} (hGG : ∀ T ∈ calT s, ((gammaBetween s.Γ T T).card : ℝ) ≤ GG)
    {c5 c6 c7 q5 q6 : ℝ} {t5 lam5 : ℝ} (ht5 : 0 ≤ t5)
    (hc5 : edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ)) * GG + lam5 ≤ c5)
    (hq5exp : Real.exp (-t5 * lam5 + t5 ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
        * (GG * ((4 * (hh : ℝ)) ^ 2
            * Real.exp (t5 * (4 * (hh : ℝ))))))) ≤ q5)
    (hq6 : ∀ T ∈ calT s, bernoulliPr (edgeProb n) (Finset.univ.filter
      (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
        c6 ≤ ∑ v ∈ (Finset.univ : Finset V) \ T,
          zContrib s (kimM n k) hh T v σ)) ≤ q6)
    {β γ : ℝ} (hβ1 : 1 ≤ β) (hγ1 : 1 ≤ γ)
    (hβT : β ≤ Real.sqrt ((tParam n : ℕ) : ℝ) / 2) (hTpos : 0 < tParam n)
    (hhge : 2 * β * Real.sqrt ((tParam n : ℕ) : ℝ) ≤ (hh : ℝ))
    (hβγT : 2 * β * γ * Real.sqrt ((tParam n : ℕ) : ℝ) ≤ 2 * (mcut n : ℝ))
    (hβ3 : 3 * ((k : ℝ) + 1) * Real.log n ≤ β ^ 2)
    {Dx : ℝ} (hDxdef : Dx = bSeq n k * theta n * Real.sqrt n
      + (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log n)
    (hc7 : (2 * (mcut n : ℝ)) / 2 * (((tParam n : ℕ) : ℝ)
          + ((tParam n : ℕ) : ℝ) / 2)
        + (bSeq n k * Dx / 2) * (((tParam n : ℕ) : ℝ)
          + ((tParam n : ℕ) : ℝ) / (2 * γ ^ 2)) ≤ c7) :
    ∀ T ∈ calT s, bernoulliPr (edgeProb n)
        ((Finset.univ.filter
          (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
            c5 + c6 + c7 < ((gammaBetween s.Γ T T
              ∩ killedZpure s (kimM n k) σ).card : ℝ)))
          ∩ goodSample s (kimM n k) k Dx)
      ≤ q5 + q6 := by
  intro T hT
  have hcardT : T.card = tParam n := card_of_mem_calT hT
  have hn : 0 < n := hN.card_pos
  have hlogn : 1 ≤ Real.log n := hN.logn_ge_one
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  have hGle : ((gammaBetween s.Γ T T).card : ℝ) ≤ GG := hGG T hT
  have hD : ∀ f ∈ gammaBetween s.Γ T T,
      ((T.filter (fun v => edgeVerts f ⊆ nbrs s.Γ v)).card : ℝ)
        ≤ bSeq n k ^ 2 * (n : ℝ) := by
    intro f hf
    obtain ⟨hfΓ, -⟩ := mem_gammaBetween.mp hf
    obtain ⟨z, hz⟩ := f
    induction z using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := by simpa using hz
      have hgv : edgeVerts (⟨s(a, b), hz⟩ : Edge V) = {a, b} := edgeVerts_mk hz
      have hsub : T.filter (fun v =>
          edgeVerts (⟨s(a, b), hz⟩ : Edge V) ⊆ nbrs s.Γ v)
          ⊆ commonNbrs s.Γ a b := by
        intro v hv
        obtain ⟨-, hvf⟩ := Finset.mem_filter.mp hv
        rw [hgv] at hvf
        have ha : a ∈ nbrs s.Γ v := hvf (Finset.mem_insert_self _ _)
        have hb : b ∈ nbrs s.Γ v :=
          hvf (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        obtain ⟨hane, e1, he1, hve1, hae1⟩ := mem_nbrs.mp ha
        obtain ⟨hbne, e2, he2, hve2, hbe2⟩ := mem_nbrs.mp hb
        exact mem_commonNbrs.mpr ⟨⟨fun hc => hane hc.symm,
          fun hc => hbne hc.symm⟩,
          ⟨e1, he1, hae1, hve1⟩, ⟨e2, he2, hve2, hbe2⟩⟩
      have hmk : mkEdge hab = (⟨s(a, b), hz⟩ : Edge V) := rfl
      have hcod := h5 a b hab (by rw [hmk]; exact hfΓ)
      rw [codegEdges] at hcod
      refine le_trans ?_ hcod
      exact_mod_cast Finset.card_le_card hsub
  have hmean := zContrib_mean_le s (kimM n k) hh T hp0 hp1 T hD
  have hEsum : bernoulliExp (edgeProb n)
      (fun τ => ∑ v ∈ T, zContrib s (kimM n k) hh T v τ)
      = ∑ v ∈ T, bernoulliExp (edgeProb n) (zContrib s (kimM n k) hh T v) :=
    bernoulliExp_sum _ _ _
  have hEle : bernoulliExp (edgeProb n)
        (fun τ => ∑ v ∈ T, zContrib s (kimM n k) hh T v τ)
      ≤ edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ)) * GG := by
    rw [hEsum]
    refine le_trans hmean ?_
    have hcoef : (0 : ℝ) ≤ edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ)) := by
      have := (bSeq_pos n k).le
      positivity
    exact mul_le_mul_of_nonneg_left hGle hcoef
  have hq5' : bernoulliPr (edgeProb n) (Finset.univ.filter
      (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
        c5 < ∑ v ∈ T, zContrib s (kimM n k) hh T v σ)) ≤ q5 := by
    refine le_trans (bernoulliPr_mono hp0 hp1 ?_)
      (le_trans (zSumT_tail s (kimM n k) hh T hp0 hp1 (t := t5) (lam := lam5)
        ht5) ?_)
    · intro σ hσ
      obtain ⟨-, hlt⟩ := Finset.mem_filter.mp hσ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩
    · refine le_trans (Real.exp_le_exp.mpr ?_) hq5exp
      have hcoef : (0 : ℝ) ≤ t5 ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
          * ((4 * (hh : ℝ)) ^ 2 * Real.exp (t5 * (4 * (hh : ℝ))))) := by
        have hpp : (0 : ℝ) ≤ edgeProb n * (1 - edgeProb n) :=
          mul_nonneg hp0 (by linarith)
        have := Real.exp_pos (t5 * (4 * (hh : ℝ)))
        positivity
      nlinarith [hGle, hcoef]
  -- the deterministic `Φ⁽⁴⁾` bound on the good event
  have hTpos' : 0 < T.card := by rw [hcardT]; exact hTpos
  have hβT' : β ≤ Real.sqrt (T.card : ℝ) / 2 := by rw [hcardT]; exact hβT
  have hhge' : 2 * β * Real.sqrt (T.card : ℝ) ≤ (hh : ℝ) := by
    rw [hcardT]; exact hhge
  have hβγT' : 2 * β * γ * Real.sqrt (T.card : ℝ) ≤ 2 * (mcut n : ℝ) := by
    rw [hcardT]; exact hβγT
  have hGood : ∀ σ ∈ goodSample s (kimM n k) k Dx,
      (∑ v ∈ Finset.univ.filter
          (fun v => hh ≤ (nbrs (sampleP s (kimM n k) σ) v ∩ T).card),
        ((gammaBetween s.Γ (nbrs (sampleP s (kimM n k) σ) v ∩ T)
          (nbrs (sampleP s (kimM n k) σ) v ∩ T)).card : ℝ)) ≤ c7 := by
    intro σ hσ
    obtain ⟨h3', hdeg⟩ := mem_goodSample.mp hσ
    have hDx' : ∀ v : V,
        ((nbrs (sampleP s (kimM n k) σ) v ∩ T).card : ℝ) ≤ Dx := by
      intro v
      refine le_trans ?_ (hdeg v)
      have h1 : (nbrs (sampleP s (kimM n k) σ) v ∩ T).card
          ≤ (nbrs (sampleP s (kimM n k) σ) v).card :=
        Finset.card_le_card Finset.inter_subset_left
      have h2' : (nbrs (sampleP s (kimM n k) σ) v).card
          = degEdges (sampleP s (kimM n k) σ) v := card_nbrs_eq_degEdges _ _
      rw [h2'] at h1
      exact_mod_cast h1
    have hcodeg : ∀ v w : V, v ≠ w →
        ((commonNbrs (blockStepP s (kimM n k) σ).E v w).card : ℝ) ≤ β ^ 2 := by
      intro v w hvw
      refine le_trans (h3' v w hvw) (le_trans ?_ hβ3)
      push_cast
      linarith
    have hself : ∀ A : Finset V, 2 * (mcut n : ℝ) ≤ (A.card : ℝ) →
        ((gammaBetween s.Γ A A).card : ℝ)
          ≤ bSeq n k * (A.card.choose 2 : ℕ) := by
      intro A hA
      refine h6.self hN.mcut_pos A ?_
      exact_mod_cast hA
    have hres := card_phi4_le s (kimM n k) σ T hβ1 hγ1 hβT' hTpos' hh hhge'
      (by positivity : (0 : ℝ) ≤ 2 * (mcut n : ℝ)) hβγT' hDx'
      (bSeq_pos n k).le hself hcodeg
    rw [hcardT] at hres
    exact le_trans hres hc7
  exact card_killedZpure_prob' s (kimM n k) hh T hp0 hp1
    (goodSample s (kimM n k) k Dx) hGood hq5' (hq6 T hT)

open scoped Classical in
/-- **Property 8's bad-event bound**, with the codegree budget taken from
Property 5. -/
lemma bad8_bound (k : ℕ) (s : BlockState V) (hN : KimLarge n)
    (h4 : Property4 s k) (h5 : Property5 s k)
    (l : ℕ) {ρ : ℝ} (hρ : ρ < 0) {B : ℝ} (hB0 : 0 < B)
    (hbin : ∀ T ∈ calT s,
      ((1 - edgeProb n) + edgeProb n * Real.exp ρ)
          ^ (gammaBetween s.Γ T T).card
        / Real.exp (ρ * (3 * l)) ≤ B / 2)
    (hfam : ∀ T ∈ calT s,
      (((gammaBetween s.Γ T T).card : ℝ)
        * (2 * (kimM n k : ℝ) * edgeProb n ^ 2
          + (bSeq n k ^ 2 * (n : ℝ)) * edgeProb n ^ 3)) ^ l
        / (l.factorial : ℝ) ≤ B / 2)
    (htarget : (n : ℝ) * (((calT s).card : ℝ) * B)
      ≤ (n : ℝ) ^ (k + 1) * (Nat.choose (Fintype.card V) (tParam n))
        * Real.exp (-(1 - kimEps n)
            * ∑ j ∈ Finset.range (k + 1),
                bSeq n j * μSeq n j * theta n / Real.sqrt n
                  * ((tParam n).choose 2))) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property8 (blockStepP s (kimM n k) σ) (k + 1))) ≤ 1 / n := by
  have hn : 0 < n := hN.card_pos
  have hlogn : 1 ≤ Real.log n := hN.logn_ge_one
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  set Dc : ℕ := ⌊bSeq n k ^ 2 * (n : ℝ)⌋₊ with hDcdef
  have hbn : (0 : ℝ) ≤ bSeq n k ^ 2 * (n : ℝ) := by positivity
  have hDcle : (Dc : ℝ) ≤ bSeq n k ^ 2 * (n : ℝ) := by
    rw [hDcdef]; exact Nat.floor_le hbn
  have hDc : ∀ (x y : V) (hxy : x ≠ y), mkEdge hxy ∈ s.Γ →
      (commonNbrs s.Γ x y).card ≤ Dc := by
    intro x y hxy hmem
    have hc := h5 x y hxy hmem
    rw [codegEdges] at hc
    rw [hDcdef]
    exact Nat.le_floor hc
  refine property8_numeric k s hn hlogn h4 hDc l hρ hB0 hbin ?_ htarget
  intro T hT
  refine le_trans ?_ (hfam T hT)
  have hGnn : (0 : ℝ) ≤ ((gammaBetween s.Γ T T).card : ℝ) := Nat.cast_nonneg _
  have hp3 : (0 : ℝ) ≤ edgeProb n ^ 3 := by positivity
  have hinner : ((gammaBetween s.Γ T T).card : ℝ)
        * (2 * (kimM n k : ℝ) * edgeProb n ^ 2 + (Dc : ℝ) * edgeProb n ^ 3)
      ≤ ((gammaBetween s.Γ T T).card : ℝ)
        * (2 * (kimM n k : ℝ) * edgeProb n ^ 2
          + (bSeq n k ^ 2 * (n : ℝ)) * edgeProb n ^ 3) := by
    have h1 : (Dc : ℝ) * edgeProb n ^ 3
        ≤ (bSeq n k ^ 2 * (n : ℝ)) * edgeProb n ^ 3 :=
      mul_le_mul_of_nonneg_right hDcle hp3
    nlinarith [h1, hGnn]
  have hbase : (0 : ℝ) ≤ ((gammaBetween s.Γ T T).card : ℝ)
      * (2 * (kimM n k : ℝ) * edgeProb n ^ 2 + (Dc : ℝ) * edgeProb n ^ 3) := by
    have hMnn : (0 : ℝ) ≤ (kimM n k : ℝ) := Nat.cast_nonneg _
    have hDnn : (0 : ℝ) ≤ (Dc : ℝ) := Nat.cast_nonneg _
    positivity
  have hpow := pow_le_pow_left₀ hbase hinner l
  have hfac : (0 : ℝ) < (l.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos l
  have hstep := mul_le_mul_of_nonneg_right hpow (le_of_lt (inv_pos.mpr hfac))
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact hstep

open scoped Classical in
open scoped Classical in
open scoped Classical in
/-- `v`'s coordinate block has at most `|T|` coordinates. -/
lemma card_zBlock_le (s : BlockState V) (M : ℕ) (v : V) (T : Finset V) :
    (zBlock s M v T).card ≤ T.card := by
  classical
  rw [zBlock, Finset.card_image_of_injective _ (padEmb V M).injective]
  refine Finset.card_le_card_of_injOn (otherEndOf v) ?_ ?_
  · intro e he
    exact (mem_edgesToSet.mp he).2.2
  · intro e he e' he' hEq
    have hmem : ∀ f : Edge V, f ∈ edgesToSet s v T → f ∈ edgesAt s.Γ v := by
      intro f hf
      obtain ⟨hfΓ, hvf, -⟩ := mem_edgesToSet.mp hf
      exact Finset.mem_filter.mpr ⟨hfΓ, hvf⟩
    exact otherEndOf_injOn s.Γ v
      (Finset.mem_coe.mpr (hmem e (Finset.mem_coe.mp he)))
      (Finset.mem_coe.mpr (hmem e' (Finset.mem_coe.mp he'))) hEq

open scoped Classical in
open scoped Classical in
lemma bad7_hq6' (k : ℕ) (s : BlockState V) (hN : KimLarge n)
    (h5 : Property5 s k) (hh : ℕ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρh : ρ * (hh : ℝ) ≤ 1) (c6 : ℝ)
    (GG : ℝ) (hGG : ∀ T ∈ calT s, ((gammaBetween s.Γ T T).card : ℝ) ≤ GG) :
    ∀ T ∈ calT s, bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          c6 ≤ ∑ v ∈ (Finset.univ : Finset V) \ T,
            zContrib s (kimM n k) hh T v σ))
      ≤ Real.exp (-(ρ * c6)
          + (ρ * (edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ)) * GG)
            + 1024 * ρ ^ 2
              * ((1 - edgeProb n) + edgeProb n * Real.exp 1) ^ (tParam n)
              * (n : ℝ))) := by
  intro T hT
  have hcardT : T.card = tParam n := card_of_mem_calT hT
  have hn : 0 < n := hN.card_pos
  have hlogn : 1 ≤ Real.log n := hN.logn_ge_one
  have hp0 : 0 ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := edgeProb_le_one' hlogn hn
  have hbase1 : (1 : ℝ) ≤ (1 - edgeProb n) + edgeProb n * Real.exp 1 := by
    have he : (1 : ℝ) ≤ Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    nlinarith [hp0, he]
  have hK0 : (0 : ℝ)
      ≤ ((1 - edgeProb n) + edgeProb n * Real.exp 1) ^ (tParam n) := by
    positivity
  have hK : ∀ v : V, ((1 - edgeProb n) + edgeProb n * Real.exp 1)
      ^ (zBlock s (kimM n k) v T).card
      ≤ ((1 - edgeProb n) + edgeProb n * Real.exp 1) ^ (tParam n) := by
    intro v
    refine pow_le_pow_right₀ hbase1 ?_
    rw [← hcardT]
    exact card_zBlock_le s (kimM n k) v T
  have hGle : ((gammaBetween s.Γ T T).card : ℝ) ≤ GG := hGG T hT
  have hD : ∀ f ∈ gammaBetween s.Γ T T,
      ((((Finset.univ : Finset V) \ T).filter
        (fun v => edgeVerts f ⊆ nbrs s.Γ v)).card : ℝ)
        ≤ bSeq n k ^ 2 * (n : ℝ) := by
    intro f hf
    obtain ⟨hfΓ, -⟩ := mem_gammaBetween.mp hf
    obtain ⟨z, hz⟩ := f
    induction z using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := by simpa using hz
      have hgv : edgeVerts (⟨s(a, b), hz⟩ : Edge V) = {a, b} := edgeVerts_mk hz
      have hsub : ((Finset.univ : Finset V) \ T).filter (fun v =>
          edgeVerts (⟨s(a, b), hz⟩ : Edge V) ⊆ nbrs s.Γ v)
          ⊆ commonNbrs s.Γ a b := by
        intro v hv
        obtain ⟨-, hvf⟩ := Finset.mem_filter.mp hv
        rw [hgv] at hvf
        have ha : a ∈ nbrs s.Γ v := hvf (Finset.mem_insert_self _ _)
        have hb : b ∈ nbrs s.Γ v :=
          hvf (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        obtain ⟨hane, e1, he1, hve1, hae1⟩ := mem_nbrs.mp ha
        obtain ⟨hbne, e2, he2, hve2, hbe2⟩ := mem_nbrs.mp hb
        exact mem_commonNbrs.mpr ⟨⟨fun hc => hane hc.symm,
          fun hc => hbne hc.symm⟩,
          ⟨e1, he1, hae1, hve1⟩, ⟨e2, he2, hve2, hbe2⟩⟩
      have hmk : mkEdge hab = (⟨s(a, b), hz⟩ : Edge V) := rfl
      have hcod := h5 a b hab (by rw [hmk]; exact hfΓ)
      rw [codegEdges] at hcod
      refine le_trans ?_ hcod
      exact_mod_cast Finset.card_le_card hsub
  have hmean := zContrib_mean_le s (kimM n k) hh T hp0 hp1
    ((Finset.univ : Finset V) \ T) hD
  have hmean' : ∑ v ∈ (Finset.univ : Finset V) \ T,
      bernoulliExp (edgeProb n) (zContrib s (kimM n k) hh T v)
      ≤ edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ)) * GG := by
    refine le_trans hmean ?_
    have hcoef : (0 : ℝ) ≤ edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ)) := by
      have := (bSeq_pos n k).le
      positivity
    exact mul_le_mul_of_nonneg_left hGle hcoef
  exact zSum_tail s (kimM n k) hh T hp0 hp1 hρ hρh hK0 hK hmean' c6

open scoped Classical in
set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- `μ_k ∈ [1/2, 1]` — Kim's (12) — for `k` in the admissible range. -/
lemma KimLarge.mu_bounds {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    1 / 2 ≤ μSeq N k ∧ μSeq N k ≤ 1 := by
  have hN1 : 1 ≤ N := h.card_pos
  have hθpos := h.theta_pos'
  have hθ : theta N ≤ 1 / 100 := h.2.1
  have hL := h.logn_big
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have ha0 := aSeq_nonneg N k
  have hale := aSeq_le_of_k_le hN1 hθpos hk
  have hsL : (3 : ℝ) ≤ Real.sqrt (Real.log N) := by
    have h1 : Real.sqrt (9 : ℝ) ≤ Real.sqrt (Real.log N) :=
      Real.sqrt_le_sqrt (by linarith)
    have h9 : Real.sqrt (9 : ℝ) = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
    linarith [h1, h9.le, h9.ge]
  have hsq : Real.sqrt (Real.log N) ^ 2 = Real.log N := Real.sq_sqrt hL0.le
  -- `a ≤ √(δ log N) + 1 + θ ≤ √(log N)/4 + 2`
  have hdq : Real.sqrt (kimDelta * Real.log N) ≤ Real.sqrt (Real.log N) / 4 := by
    have h1 : kimDelta * Real.log N ≤ (Real.sqrt (Real.log N) / 4) ^ 2 := by
      have he : (Real.sqrt (Real.log N) / 4) ^ 2 = Real.log N / 16 := by
        rw [div_pow, hsq]; norm_num
      rw [he, kimDelta]
      nlinarith [hL]
    calc Real.sqrt (kimDelta * Real.log N)
        ≤ Real.sqrt ((Real.sqrt (Real.log N) / 4) ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt (Real.log N) / 4 := Real.sqrt_sq (by positivity)
  have hasm : aSeq N k ≤ Real.sqrt (Real.log N) / 4 + 2 := by
    linarith [hale, hdq, hθ, hθpos.le]
  refine ⟨?_, ?_⟩
  · rw [μSeq]
    have hLbig := h.logn_large
    have hs : Real.sqrt (Real.log N) ≤ Real.log N := by
      nlinarith [hsq, hsL, hL]
    have h1 : 18 * aSeq N k * theta N ≤ 1 / 4 := by
      have hstep : aSeq N k * theta N
          ≤ (Real.sqrt (Real.log N) / 4 + 2) * theta N :=
        mul_le_mul_of_nonneg_right hasm hθpos.le
      have hb : (Real.sqrt (Real.log N) / 4 + 2) * theta N ≤ 1 / 72 := by
        rw [theta, mul_one_div,
          div_le_iff₀ (by positivity : (0 : ℝ) < Real.log N ^ 2)]
        nlinarith [hs, hLbig, hL0]
      linarith [hstep, hb]
    have h2 : aSeq N k / (3 * Real.sqrt (Real.log N)) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * Real.sqrt (Real.log N))]
      nlinarith [hasm, hsL]
    linarith [h1, h2]
  · rw [μSeq]
    have h1 : (0 : ℝ) ≤ 18 * aSeq N k * theta N := by positivity
    have h2 : (0 : ℝ) ≤ aSeq N k / (3 * Real.sqrt (Real.log N)) := by
      have : (0 : ℝ) < 3 * Real.sqrt (Real.log N) := by positivity
      positivity
    linarith

/-- `μ_k − μ_{k+1} = 18b_kθ² + b_kθ/(3√log n)`. -/
lemma muSeq_step (N k : ℕ) :
    μSeq N k - μSeq N (k + 1)
      = 18 * bSeq N k * theta N ^ 2
        + bSeq N k * theta N / (3 * Real.sqrt (Real.log N)) := by
  rw [μSeq, μSeq, aSeq_succ]
  ring

/-- **The survival gap.**  `b_{k+1} − b_k(1−p)^{2M} ≤ (321/20)b²θ² − (5/2)b³θ²`.

The `(1−p)^{2M}` survival factor of §4.8 (39) and the true ratio `b'/b` agree
to first order; the discrepancy is `10b²θ²` from the `5θ` in `M`, `(41/20)b²θ²`
from `a_k ≤ Ψ + θ`, and a second-order `6Ψ²b³θ²` which only fits inside `μ`'s
`18bθ²` allowance when kept together with the `Φ⁽³⁾` charge — see
`psiSq_combo_le`. -/
lemma KimLarge.surv_gap {N k : ℕ} (h : KimLarge N) :
    bSeq N (k + 1)
        - bSeq N k * (1 - edgeProb N) ^ (2 * kimM N k)
      ≤ (321 / 20) * bSeq N k ^ 2 * theta N ^ 2
        - (5 / 2) * bSeq N k ^ 3 * theta N ^ 2 := by
  have hN1 : 1 ≤ N := h.card_pos
  have hθ : theta N ≤ 1 / 100 := h.2.1
  have hp0 : 0 ≤ edgeProb N := edgeProb_nonneg N
  have hp1 : edgeProb N ≤ 1 := edgeProb_le_one' h.logn_ge_one h.card_pos
  have hb0 := (bSeq_pos N k).le
  have hθ0 := theta_nonneg N
  have herr : (0 : ℝ) ≤ 2 * edgeProb N := by linarith
  have h41 := lemma41_bounds (N := N) k hθ hp0 hp1 (2 * kimM N k) herr
    (two_kimM_mul_edgeProb_le k hN1) (two_kimM_mul_edgeProb_ge k hN1)
  have hlow : 1 - 2 * aSeq N k * bSeq N k * theta N
      - 10 * bSeq N k * theta N ^ 2 ≤ (1 - edgeProb N) ^ (2 * kimM N k) :=
    h41.1
  have hmul := mul_le_mul_of_nonneg_left hlow hb0
  have hup := bSeq_succ_upper hθ k
  have hcombo := psiSq_combo_le N k
  have hb2 : (0 : ℝ) ≤ bSeq N k ^ 2 * theta N ^ 2 := by positivity
  have hpsi : 6 * (spencerPsi ((k : ℝ) * theta N)) ^ 2 * bSeq N k ^ 3
        * theta N ^ 2
      ≤ (4 - (5 / 2) * bSeq N k) * (bSeq N k ^ 2 * theta N ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hcombo hb2
    nlinarith [h]
  nlinarith [hmul, hup, hpsi, hb0, hθ0]

/-- `2a_kb_kθ + b_kθ² ≤ 1/100`. -/
lemma KimLarge.ratio_small {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    2 * aSeq N k * bSeq N k * theta N + bSeq N k * theta N ^ 2 ≤ 1 / 100 := by
  have hN1 : 1 ≤ N := h.card_pos
  have hθpos := h.theta_pos'
  have hθ : theta N ≤ 1 / 100 := h.2.1
  have hLbig := h.logn_large
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hb0 := (bSeq_pos N k).le
  have hb1 := bSeq_le_one N k
  have ha0 := aSeq_nonneg N k
  have hale := aSeq_le_of_k_le hN1 hθpos hk
  have hsq : Real.sqrt (Real.log N) ^ 2 = Real.log N := Real.sq_sqrt hL0.le
  have hsL : Real.sqrt (Real.log N) ≤ Real.log N := by
    nlinarith [hsq, Real.sqrt_nonneg (Real.log N), hLbig]
  have hdq : Real.sqrt (kimDelta * Real.log N) ≤ Real.sqrt (Real.log N) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith [kimDelta_lt, kimDelta_pos, hL0]
  have ha : aSeq N k ≤ Real.log N + 2 := by linarith [hale, hdq, hsL, hθ]
  have hθe : theta N = 1 / Real.log N ^ 2 := by rw [theta]
  have h1 : 2 * (Real.log N + 2) * theta N ≤ 1 / 200 := by
    rw [hθe, mul_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < Real.log N ^ 2)]
    nlinarith [hLbig, hL0]
  have h2 : 2 * aSeq N k * bSeq N k * theta N ≤ 2 * (Real.log N + 2) * theta N := by
    have hstep : aSeq N k * bSeq N k ≤ Real.log N + 2 := by
      nlinarith [ha, hb0, hb1, ha0]
    have := mul_le_mul_of_nonneg_right hstep (by linarith : (0:ℝ) ≤ 2 * theta N)
    linarith [this]
  have h3 : bSeq N k * theta N ^ 2 ≤ 1 / 10000 := by
    nlinarith [hb0, hb1, hθ, hθpos.le]
  linarith [h1, h2, h3]

/-- **The §4.8 budget.**  What Property 7's step has to spend, per `T`:

`(1−p)^{2M}·b_kμ_k − b_{k+1}μ_{k+1} ≥ (7/4)b²θ² + (5/4)b³θ² + b b′θ/(3√log n)`.

The `18bθ²` allowance in `μ` is almost entirely consumed by the survival gap
(`surv_gap`, ≈16.05 of 18); the `(5/4)b³θ²` that survives is exactly what pays
for `Φ⁽³⁾` and `lam₁`, and the `√log n` term pays for `Y⁽²⁾` and `Φ⁽⁴⁾`. -/
lemma KimLarge.budget_lower {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    (8 / 5) * bSeq N k ^ 2 * theta N ^ 2
        + (5 / 4) * bSeq N k ^ 3 * theta N ^ 2
        + bSeq N k * bSeq N (k + 1) * theta N / (3 * Real.sqrt (Real.log N))
      ≤ (1 - edgeProb N) ^ (2 * kimM N k) * bSeq N k * μSeq N k
        - bSeq N (k + 1) * μSeq N (k + 1) := by
  have hb0 := (bSeq_pos N k).le
  have hb1 := bSeq_le_one N k
  have hθ0 := theta_nonneg N
  have hgap := h.surv_gap (k := k)
  obtain ⟨hμlo, hμhi⟩ := h.mu_bounds hk
  have hstep := muSeq_step N k
  have hratio := bSeq_ratio_lower N k
  have hsmall := h.ratio_small hk
  set L : ℝ := (1 - edgeProb N) ^ (2 * kimM N k) with hLdef
  set b : ℝ := bSeq N k with hbdef
  set b' : ℝ := bSeq N (k + 1) with hb'def
  set θ : ℝ := theta N with hθdef
  set μ : ℝ := μSeq N k with hμdef
  set μ' : ℝ := μSeq N (k + 1) with hμ'def
  -- the survival gap, as `Lb − b′ ≥ −(A − B)`
  have hA0 : (0 : ℝ) ≤ (321 / 20) * b ^ 2 * θ ^ 2
      - (5 / 2) * b ^ 3 * θ ^ 2 := by nlinarith [hb0, hb1, sq_nonneg (b * θ)]
  have hB0 : (0 : ℝ) ≤ (5 / 2) * b ^ 3 * θ ^ 2 := by positivity
  have hAA : (0 : ℝ) ≤ (321 / 20) * b ^ 2 * θ ^ 2 := by positivity
  have hmul1 : ((321 / 20) * b ^ 2 * θ ^ 2 - (5 / 2) * b ^ 3 * θ ^ 2) * μ
      ≤ (321 / 20) * b ^ 2 * θ ^ 2 - (5 / 4) * b ^ 3 * θ ^ 2 := by
    nlinarith [hμlo, hμhi, hAA, hB0]
  have hmul2 : (L * b - b') * μ
      ≥ -((321 / 20) * b ^ 2 * θ ^ 2 - (5 / 4) * b ^ 3 * θ ^ 2) := by
    have hge : -((321 / 20) * b ^ 2 * θ ^ 2 - (5 / 2) * b ^ 3 * θ ^ 2)
        ≤ L * b - b' := by linarith [hgap]
    nlinarith [hge, hμlo, hmul1, hμhi]
  -- the `μ` decrement
  have hbb : b ^ 2 * (1 - (2 * aSeq N k * b * θ + b * θ ^ 2)) ≤ b * b' := by
    have := mul_le_mul_of_nonneg_left hratio hb0
    nlinarith [this]
  have hbbge : (99 / 100) * b ^ 2 ≤ b * b' := by
    nlinarith [hbb, hsmall, sq_nonneg b, hb0]
  have hdec : b' * (μ - μ')
      = 18 * b * b' * θ ^ 2 + b * b' * θ / (3 * Real.sqrt (Real.log N)) := by
    rw [hstep]; ring
  have h18 : (89 / 5 : ℝ) * b ^ 2 * θ ^ 2 ≤ 18 * b * b' * θ ^ 2 := by
    nlinarith [hbbge, sq_nonneg θ, hθ0]
  have hsplit : L * b * μ - b' * μ' = (L * b - b') * μ + b' * (μ - μ') := by
    ring
  rw [hsplit, hdec]
  linarith [hmul2, h18]

/-- `1000 ≤ √log n`. -/
lemma KimLarge.sqrt_logn_ge {N : ℕ} (h : KimLarge N) :
    1000 ≤ Real.sqrt (Real.log N) := by
  have hLv := h.logn_vast
  have h1 : Real.sqrt ((1000 : ℝ) ^ 2) ≤ Real.sqrt (Real.log N) :=
    Real.sqrt_le_sqrt (by norm_num; linarith)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1000)] at h1

/-- `t ≥ 18(log n)²√log n`, hence `t` dwarfs every polylog. -/
lemma KimLarge.tParam_huge {N : ℕ} (h : KimLarge N) :
    18 * (Real.log N) ^ 2 * Real.sqrt (Real.log N) ≤ ((tParam N : ℕ) : ℝ) := by
  have hn : 0 < N := h.card_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hn
  have hL0 : (0 : ℝ) < Real.log N := by linarith [h.logn_vast]
  have hs0 : (0 : ℝ) < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have hsN : (2 : ℝ) * (Real.log N) ^ 2 ≤ Real.sqrt N := by
    have hp := h.polylog (j := 2) (by norm_num)
    have h8N : (8 : ℝ) < (N : ℝ) := h.1
    have h38 : (2 : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 8) := by
      have hb : ((8 : ℝ)) ^ ((3 : ℝ) / 8) ≤ (N : ℝ) ^ ((3 : ℝ) / 8) :=
        Real.rpow_le_rpow (by norm_num) h8N.le (by norm_num)
      have h8e : ((8 : ℝ)) ^ ((3 : ℝ) / 8) = 2 ^ ((9 : ℝ) / 8) := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num,
          ← Real.rpow_natCast (2 : ℝ) 3, ← Real.rpow_mul (by norm_num)]
        norm_num
      have h2 : (2 : ℝ) ≤ 2 ^ ((9 : ℝ) / 8) := by
        have hone := Real.one_le_rpow (x := (2 : ℝ)) (by norm_num)
          (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 8)
        have hrw : (2 : ℝ) ^ ((9 : ℝ) / 8)
            = 2 ^ ((1 : ℝ)) * 2 ^ ((1 : ℝ) / 8) := by
          rw [← Real.rpow_add (by norm_num)]; ring_nf
        rw [hrw, Real.rpow_one]
        linarith
      linarith [hb, h8e.le, h8e.ge, h2]
    have hsplit : (N : ℝ) ^ ((1 : ℝ) / 2)
        = (N : ℝ) ^ ((1 : ℝ) / 8) * (N : ℝ) ^ ((3 : ℝ) / 8) := by
      rw [← Real.rpow_add hNR]; ring_nf
    have hq0 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hNR _
    have h8 : (2 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [hsplit]; nlinarith [h38, hq0]
    have hs : Real.sqrt (N : ℝ) = (N : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
    rw [hs]; linarith [hp, h8]
  have htge : 9 * Real.sqrt ((N : ℝ) * Real.log N) ≤ ((tParam N : ℕ) : ℝ) :=
    tParam_ge N
  have hsplit : Real.sqrt ((N : ℝ) * Real.log N)
      = Real.sqrt N * Real.sqrt (Real.log N) := Real.sqrt_mul hNR.le _
  rw [hsplit] at htge
  nlinarith [htge, hsN, hs0.le]

/-- `t ≥ 9·e^{L/2}·√L`. -/
lemma KimLarge.tParam_exp {N : ℕ} (h : KimLarge N) :
    9 * Real.exp (Real.log N / 2) * Real.sqrt (Real.log N)
      ≤ ((tParam N : ℕ) : ℝ) := by
  have hn : 0 < N := h.card_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hn
  have htge : 9 * Real.sqrt ((N : ℝ) * Real.log N) ≤ ((tParam N : ℕ) : ℝ) :=
    tParam_ge N
  have hsplit : Real.sqrt ((N : ℝ) * Real.log N)
      = Real.sqrt N * Real.sqrt (Real.log N) := Real.sqrt_mul hNR.le _
  rw [hsplit, sqrtN_eq_exp hn] at htge
  linarith [htge]

/-- `b_k ≥ exp(−δL − 2√L − 1)`. -/
lemma KimLarge.bmin_exp {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    Real.exp (-(kimDelta * Real.log N) - 2 * Real.sqrt (Real.log N) - 1)
      ≤ bSeq N k := by
  have hbmin := bSeq_ge_of_k_le h.card_pos h.theta_pos' hk
  refine le_trans (Real.exp_le_exp.mpr ?_) hbmin
  have hL0 : (0 : ℝ) < Real.log N := by linarith [h.logn_vast]
  have hsq : Real.sqrt (kimDelta * Real.log N) ≤ Real.sqrt (Real.log N) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith [kimDelta_lt, kimDelta_pos, hL0]
  linarith

/-- `40 ≤ b_k²·θ·√n`. -/
lemma KimLarge.bsq_theta_sqrtN {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    (40 : ℝ) ≤ bSeq N k ^ 2 * theta N * Real.sqrt N := by
  have hn : 0 < N := h.card_pos
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
  have hcl := h.2.2.2.2.2.2.2.2.2.2.1
  have hθ0 := (h.theta_pos').le
  have hs0 : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hE : (Real.exp (-(kimDelta * Real.log N)
      - 2 * Real.sqrt (kimDelta * Real.log N) - 1)) ^ 2 * theta N * Real.sqrt N
      ≤ bSeq N k ^ 2 * theta N * Real.sqrt N := by
    have hle : (Real.exp (-(kimDelta * Real.log N)
        - 2 * Real.sqrt (kimDelta * Real.log N) - 1)) ^ 2
        ≤ bSeq N k ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos _).le
        (bSeq_ge_of_k_le h.card_pos h.theta_pos' hk) 2
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hle hθ0) hs0
  have hq : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.one_le_rpow hNR (by norm_num)
  have hL := h.logn_vast
  have hL4 : (40 : ℝ) ≤ (Real.log N) ^ 4 := by
    have h1 : (3 : ℝ) ^ 4 ≤ (Real.log N) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 4
    norm_num at h1; linarith
  have hL40 : (0 : ℝ) ≤ (Real.log N) ^ 4 := by positivity
  have hprod : (40 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log N) ^ 4 := by
    nlinarith [hq, hL4, hL40,
      mul_nonneg (by linarith : (0:ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) - 1) hL40]
  linarith [hcl, hE, hprod]

/-- `(1/20)·b²θ²·C(t,2) ≥ p·C(t,2)`. -/
lemma KimLarge.hF3_bound {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    edgeProb N * (((tParam N).choose 2 : ℕ) : ℝ)
      ≤ (1 / 20) * bSeq N k ^ 2 * theta N ^ 2
        * (((tParam N).choose 2 : ℕ) : ℝ) := by
  have hn : 0 < N := h.card_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hn
  have hs0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
  have hθp := h.theta_pos'
  have hT20 : (0 : ℝ) ≤ (((tParam N).choose 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h40 := h.bsq_theta_sqrtN hk
  have hkey : edgeProb N ≤ (1 / 20) * bSeq N k ^ 2 * theta N ^ 2 := by
    rw [edgeProb, div_le_iff₀ hs0]
    nlinarith [h40, hθp, hs0]
  nlinarith [hkey, hT20]

/-- `12(k+1)·log n ≤ t`. -/
lemma KimLarge.twelve_k_le_t {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    12 * ((k : ℝ) + 1) * Real.log N ≤ ((tParam N : ℕ) : ℝ) := by
  have hn : 0 < N := h.card_pos
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
  have hL := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hkle := h.k_le hk
  have hcl := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hδ1 : (1 : ℝ) ≤ (N : ℝ) ^ kimDelta :=
    Real.one_le_rpow hNR kimDelta_pos.le
  have hL3 : (0 : ℝ) ≤ (Real.log N) ^ 3 := by positivity
  have hX : (Real.log N) ^ 3 ≤ (N : ℝ) ^ kimDelta * (Real.log N) ^ 3 := by
    nlinarith [hδ1, hL3]
  have hLL : Real.log N ≤ (Real.log N) ^ 3 := by nlinarith [hL, hL0]
  have hstep : 12 * ((k : ℝ) + 1) * Real.log N
      ≤ 25 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 3) + 1 := by
    have hkl : (k : ℝ) * Real.log N
        ≤ (N : ℝ) ^ kimDelta * (Real.log N) ^ 3 := by
      have hm := mul_le_mul_of_nonneg_right hkle hL0.le
      nlinarith [hm]
    linarith [hkl, hX, hLL]
  have hq : (N : ℝ) ^ ((1 : ℝ) / 4) ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hNR (by norm_num)
  have htge : 9 * Real.sqrt ((N : ℝ) * Real.log N) ≤ ((tParam N : ℕ) : ℝ) :=
    tParam_ge N
  have hsplit : Real.sqrt ((N : ℝ) * Real.log N)
      = Real.sqrt N * Real.sqrt (Real.log N) := Real.sqrt_mul (by linarith) _
  have hs1 : (1 : ℝ) ≤ Real.sqrt (Real.log N) := by
    have h1 : Real.sqrt 1 ≤ Real.sqrt (Real.log N) :=
      Real.sqrt_le_sqrt (by linarith)
    simpa using h1
  have hs0 : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
  rw [hsplit] at htge
  nlinarith [hstep, hcl, hq, htge, hs1, hs0]

/-- `β ≤ √t/2`. -/
lemma KimLarge.beta_le_sqrt_t {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    kimBeta N k ≤ Real.sqrt ((tParam N : ℕ) : ℝ) / 2 := by
  have hL0 : (0 : ℝ) < Real.log N := by linarith [h.logn_vast]
  have h12 := h.twelve_k_le_t hk
  have hsq : (2 * kimBeta N k) ^ 2 = 12 * ((k : ℝ) + 1) * Real.log N := by
    rw [kimBeta, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hβ0 : (0 : ℝ) ≤ 2 * kimBeta N k := by
    have := kimBeta_nonneg N k; linarith
  have hle : 2 * kimBeta N k ≤ Real.sqrt ((tParam N : ℕ) : ℝ) := by
    have h1 : (2 * kimBeta N k) ^ 2 ≤ ((tParam N : ℕ) : ℝ) := by
      rw [hsq]; exact h12
    calc 2 * kimBeta N k = Real.sqrt ((2 * kimBeta N k) ^ 2) :=
          (Real.sqrt_sq hβ0).symm
      _ ≤ Real.sqrt ((tParam N : ℕ) : ℝ) := Real.sqrt_le_sqrt h1
  linarith

set_option maxHeartbeats 1000000 in
/-- `2βγ√t ≤ mcut` with `γ = log n`. -/
lemma KimLarge.beta_gamma_t_le {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    2 * kimBeta N k * Real.log N * Real.sqrt ((tParam N : ℕ) : ℝ)
      ≤ (mcut N : ℝ) := by
  have hn : 0 < N := h.card_pos
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
  have hL := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have ht0 : (0 : ℝ) ≤ ((tParam N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hβ0 := kimBeta_nonneg N k
  have hmc0 : (0 : ℝ) ≤ (mcut N : ℝ) := Nat.cast_nonneg _
  have hsq : (2 * kimBeta N k * Real.log N) ^ 2
      = 12 * ((k : ℝ) + 1) * (Real.log N) ^ 3 := by
    rw [kimBeta, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have htle : ((tParam N : ℕ) : ℝ) ≤ 10 * Real.sqrt N * Real.log N := by
    have h1 := tParam_le_bound hn
    have hs1 : Real.sqrt (Real.log N) ≤ Real.log N := by
      nlinarith [Real.sq_sqrt hL0.le, Real.sqrt_nonneg (Real.log N), hL]
    have hs0 : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
    have hsN : (1 : ℝ) ≤ Real.sqrt N := one_le_sqrt_cast hn
    nlinarith [h1, hs1, hs0, hsN, hL0]
  have hkle := h.k_le hk
  have hδ1 : (1 : ℝ) ≤ (N : ℝ) ^ kimDelta :=
    Real.one_le_rpow hNR kimDelta_pos.le
  have hk1 : (k : ℝ) + 1 ≤ 2 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 2) := by
    have hL2 : (1 : ℝ) ≤ (Real.log N) ^ 2 := by nlinarith [hL, hL0]
    nlinarith [hkle, hδ1, hL2]
  have hδexp := rpow_delta_eq_exp hn
  have hsNexp := sqrtN_eq_exp hn
  have hmch := h.mcut_ge_exp
  have hcl := h.asym.p7_beta
  have hkey : 12 * ((k : ℝ) + 1) * (Real.log N) ^ 3 * ((tParam N : ℕ) : ℝ)
      ≤ (mcut N : ℝ) ^ 2 := by
    have hA : 12 * ((k : ℝ) + 1) * (Real.log N) ^ 3 * ((tParam N : ℕ) : ℝ)
        ≤ 240 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 6) * Real.sqrt N := by
      have h1 : 12 * ((k : ℝ) + 1) * (Real.log N) ^ 3
          ≤ 24 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 5) := by
        nlinarith [hk1, hL0, pow_nonneg hL0.le 3]
      have h2 : (0 : ℝ) ≤ 24 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 5) := by
        have hd : (0 : ℝ) < (N : ℝ) ^ kimDelta := by linarith
        positivity
      nlinarith [h1, h2, htle, ht0, Real.sqrt_nonneg (N : ℝ), hL0]
    -- `960n^δL¹⁴ ≤ E²√n`, exactly the clause shifted by `n^δ`
    have hsq0 : (0 : ℝ) < Real.sqrt N := by rw [hsNexp]; exact Real.exp_pos _
    have hL8 : (0 : ℝ) < (Real.log N) ^ 8 := by positivity
    have hcl2 := h.asym.p7_mcutlow
    have hkeyE : 960 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 14)
        ≤ (Real.exp (-(2 * kimDelta * Real.log N)
            - 4 * Real.sqrt (Real.log N) - 2)) ^ 2 * Real.sqrt N := by
      rw [hδexp, hsNexp, exp_sq]
      have hcomb : Real.exp (2 * (-(2 * kimDelta * Real.log N)
            - 4 * Real.sqrt (Real.log N) - 2)) * Real.exp (Real.log N / 2)
          = Real.exp (((1 : ℝ) / 2 - 5 * kimDelta) * Real.log N
              - 8 * Real.sqrt (Real.log N) - 4)
            * Real.exp (kimDelta * Real.log N) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      rw [hcomb]
      have hexp0 : (0 : ℝ) < Real.exp (kimDelta * Real.log N) := Real.exp_pos _
      have hstep := mul_le_mul_of_nonneg_right hcl2 hexp0.le
      linarith [hstep]
    have hQ0 : (0 : ℝ) ≤ Real.exp (-(2 * kimDelta * Real.log N)
        - 4 * Real.sqrt (Real.log N) - 2) * Real.sqrt N
        / (2 * (Real.log N) ^ 4) := by positivity
    have hmsq : (Real.exp (-(2 * kimDelta * Real.log N)
          - 4 * Real.sqrt (Real.log N) - 2) * Real.sqrt N
          / (2 * (Real.log N) ^ 4)) ^ 2 ≤ (mcut N : ℝ) ^ 2 :=
      pow_le_pow_left₀ hQ0 hmch 2
    have hQeq : (Real.exp (-(2 * kimDelta * Real.log N)
          - 4 * Real.sqrt (Real.log N) - 2) * Real.sqrt N
          / (2 * (Real.log N) ^ 4)) ^ 2
        = (Real.exp (-(2 * kimDelta * Real.log N)
            - 4 * Real.sqrt (Real.log N) - 2)) ^ 2
          * Real.sqrt N * Real.sqrt N / (4 * (Real.log N) ^ 8) := by
      field_simp; try ring
    have hfinal : 240 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 6) * Real.sqrt N
        ≤ (Real.exp (-(2 * kimDelta * Real.log N)
            - 4 * Real.sqrt (Real.log N) - 2)) ^ 2
          * Real.sqrt N * Real.sqrt N / (4 * (Real.log N) ^ 8) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (Real.log N) ^ 8)]
      have hmul := mul_le_mul_of_nonneg_right hkeyE hsq0.le
      have hlhs : 240 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 6) * Real.sqrt N
            * (4 * (Real.log N) ^ 8)
          = 960 * ((N : ℝ) ^ kimDelta * (Real.log N) ^ 14) * Real.sqrt N := by
        ring
      rw [hlhs]
      linarith [hmul]
    linarith [hA, hfinal, hmsq, hQeq.le, hQeq.ge]
  have hprod : (2 * kimBeta N k * Real.log N
        * Real.sqrt ((tParam N : ℕ) : ℝ)) ^ 2 ≤ (mcut N : ℝ) ^ 2 := by
    have hs : Real.sqrt ((tParam N : ℕ) : ℝ) ^ 2 = ((tParam N : ℕ) : ℝ) :=
      Real.sq_sqrt ht0
    rw [mul_pow, hs, hsq]
    exact hkey
  have hlhs0 : (0 : ℝ) ≤ 2 * kimBeta N k * Real.log N
      * Real.sqrt ((tParam N : ℕ) : ℝ) := by positivity
  nlinarith [hprod, hlhs0, hmc0]

set_option maxHeartbeats 1000000 in
/-- **`3·mcut·t` fits in `(1/20)b²θ²·C(t,2)`.** -/
lemma KimLarge.hF1_bound {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    3 * (mcut N : ℝ) * ((tParam N : ℕ) : ℝ)
      ≤ (1 / 20) * bSeq N k ^ 2 * theta N ^ 2
        * (((tParam N).choose 2 : ℕ) : ℝ) := by
  have hn : 0 < N := h.card_pos
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have hs1000 := h.sqrt_logn_ge
  have ht0 : (0 : ℝ) ≤ ((tParam N : ℕ) : ℝ) := Nat.cast_nonneg _
  have htb := h.tParam_huge
  have hprod0 : (1000000 : ℝ) * 1000 ≤ Real.log N * Real.sqrt (Real.log N) :=
    mul_le_mul hLv hs1000 (by norm_num) (by linarith)
  have h6 : 6 * Real.log N * Real.sqrt (Real.log N) ≤ ((tParam N : ℕ) : ℝ) := by
    nlinarith [htb, hLv, hL0, hs0.le]
  have ht3 : (3 : ℝ) ≤ ((tParam N : ℕ) : ℝ) := by linarith [h6, hprod0]
  have hT2third : ((tParam N : ℕ) : ℝ) ^ 2 / 3
      ≤ (((tParam N).choose 2 : ℕ) : ℝ) := by
    rw [Nat.cast_choose_two]
    nlinarith [mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ ((tParam N : ℕ) : ℝ) - 3)]
  -- With Kim's threshold the `b²θ²` on both sides cancels outright and
  -- `3·mcut·t ≤ (1/20)b²θ²C(t,2)` reduces to `180√n ≤ t`.
  have hcore : 180 * (mcut N : ℝ) ≤ bSeq N k ^ 2 * theta N ^ 2
      * ((tParam N : ℕ) : ℝ) := by
    have hmc := h.mcut_le_mcutR
    have hmono : bSeq N ⌊(N : ℝ) ^ kimDelta / theta N⌋₊ ≤ bSeq N k :=
      bSeq_antitone N hk
    have hb₀0 := (bSeq_pos N ⌊(N : ℝ) ^ kimDelta / theta N⌋₊).le
    have hsN0 : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
    have hθ0 : (0 : ℝ) ≤ theta N ^ 2 := by positivity
    -- `mcutR ≤ θ²b_k²√n`
    have hup : mcutR N ≤ theta N ^ 2 * bSeq N k ^ 2 * Real.sqrt N := by
      rw [mcutR]
      have hbsq : bSeq N ⌊(N : ℝ) ^ kimDelta / theta N⌋₊ ^ 2 ≤ bSeq N k ^ 2 :=
        pow_le_pow_left₀ hb₀0 hmono 2
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbsq hθ0) hsN0
    -- `180√n ≤ t`
    have ht180 : 180 * Real.sqrt N ≤ ((tParam N : ℕ) : ℝ) := by
      have ht := tParam_ge N
      have hsplit : Real.sqrt ((N : ℝ) * Real.log N)
          = Real.sqrt N * Real.sqrt (Real.log N) :=
        Real.sqrt_mul (Nat.cast_nonneg _) _
      have hs20 : (20 : ℝ) ≤ Real.sqrt (Real.log N) := by
        linarith [hs1000]
      nlinarith [ht, hsplit.le, hsplit.ge, hs20, hsN0]
    have hmul := mul_le_mul_of_nonneg_left ht180
      (show (0 : ℝ) ≤ bSeq N k ^ 2 * theta N ^ 2 by positivity)
    have hrw : bSeq N k ^ 2 * theta N ^ 2 * (180 * Real.sqrt N)
        = 180 * (theta N ^ 2 * bSeq N k ^ 2 * Real.sqrt N) := by ring
    linarith [hmc, hup, hmul, hrw.le, hrw.ge]
  have hb2θ0 : (0 : ℝ) ≤ bSeq N k ^ 2 * theta N ^ 2 := by positivity
  have hstep2 : 3 * (mcut N : ℝ) * ((tParam N : ℕ) : ℝ)
      ≤ (1 / 60) * (bSeq N k ^ 2 * theta N ^ 2 * ((tParam N : ℕ) : ℝ))
        * ((tParam N : ℕ) : ℝ) := by
    nlinarith [hcore, ht0]
  have hstep3 : (1 / 60) * (bSeq N k ^ 2 * theta N ^ 2
        * ((tParam N : ℕ) : ℝ)) * ((tParam N : ℕ) : ℝ)
      ≤ (1 / 20) * bSeq N k ^ 2 * theta N ^ 2
        * (((tParam N).choose 2 : ℕ) : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hT2third
      (show (0 : ℝ) ≤ (1 / 20) * (bSeq N k ^ 2 * theta N ^ 2) by positivity)
    nlinarith [hm]
  linarith [hstep2, hstep3]

set_option maxHeartbeats 1000000 in
/-- **`(3/2)b·n^{1/4}log n·t·(1+θ/2)` fits in `(1/20)b²θ²·C(t,2)`.** -/
lemma KimLarge.hF2_bound {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    (3 / 2) * bSeq N k * ((N : ℝ) ^ ((1 : ℝ) / 4) * Real.log N)
        * ((tParam N : ℕ) : ℝ) * (1 + theta N / 2)
      ≤ (1 / 20) * bSeq N k ^ 2 * theta N ^ 2
        * (((tParam N).choose 2 : ℕ) : ℝ) := by
  have hn : 0 < N := h.card_pos
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hL4 : (0 : ℝ) < (Real.log N) ^ 4 := by positivity
  have hs0 : (0 : ℝ) < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have hs1000 := h.sqrt_logn_ge
  have ht0 : (0 : ℝ) ≤ ((tParam N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hb0 := (bSeq_pos N k).le
  have hθ : theta N ≤ 1 / 100 := h.2.1
  have hθ0 := (h.theta_pos').le
  have htb := h.tParam_huge
  have hprod0 : (1000000 : ℝ) * 1000 ≤ Real.log N * Real.sqrt (Real.log N) :=
    mul_le_mul hLv hs1000 (by norm_num) (by linarith)
  have h6 : 6 * Real.log N * Real.sqrt (Real.log N) ≤ ((tParam N : ℕ) : ℝ) := by
    nlinarith [htb, hLv, hL0, hs0.le]
  have ht3 : (3 : ℝ) ≤ ((tParam N : ℕ) : ℝ) := by linarith [h6, hprod0]
  have hT2third : ((tParam N : ℕ) : ℝ) ^ 2 / 3
      ≤ (((tParam N).choose 2 : ℕ) : ℝ) := by
    rw [Nat.cast_choose_two]
    nlinarith [mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ ((tParam N : ℕ) : ℝ) - 3)]
  have hcore : 180 * ((N : ℝ) ^ ((1 : ℝ) / 4) * Real.log N)
      ≤ bSeq N k * theta N ^ 2 * ((tParam N : ℕ) : ℝ) := by
    have hRe := rpow_quarter_eq_exp hn
    have hbe := h.bmin_exp hk
    have hte := h.tParam_exp
    have hcl := h.asym.p7_quarter
    have hθe : theta N ^ 2 = 1 / (Real.log N) ^ 4 := by rw [theta]; field_simp
    have hcomb : Real.exp (-(kimDelta * Real.log N)
          - 2 * Real.sqrt (Real.log N) - 1) * Real.exp (Real.log N / 2)
        = Real.exp (Real.log N / 4)
          * Real.exp (((1 : ℝ) / 4 - kimDelta) * Real.log N
            - 2 * Real.sqrt (Real.log N) - 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hE0 : (0 : ℝ) < Real.exp (Real.log N / 4) := Real.exp_pos _
    have hQ0 : (0 : ℝ) ≤ Real.exp (((1 : ℝ) / 4 - kimDelta) * Real.log N
        - 2 * Real.sqrt (Real.log N) - 1) := (Real.exp_pos _).le
    have hQs : 20 * (Real.log N) ^ 5
        ≤ Real.exp (((1 : ℝ) / 4 - kimDelta) * Real.log N
            - 2 * Real.sqrt (Real.log N) - 1) * Real.sqrt (Real.log N) := by
      nlinarith [hcl, hs1000, hQ0, hL4, hL0]
    have hstep : 180 * (Real.exp (Real.log N / 4) * Real.log N)
        ≤ Real.exp (-(kimDelta * Real.log N)
              - 2 * Real.sqrt (Real.log N) - 1) * (1 / (Real.log N) ^ 4)
            * (9 * Real.exp (Real.log N / 2) * Real.sqrt (Real.log N)) := by
      have hrw : Real.exp (-(kimDelta * Real.log N)
              - 2 * Real.sqrt (Real.log N) - 1) * (1 / (Real.log N) ^ 4)
            * (9 * Real.exp (Real.log N / 2) * Real.sqrt (Real.log N))
          = 9 * (Real.exp (-(kimDelta * Real.log N)
              - 2 * Real.sqrt (Real.log N) - 1) * Real.exp (Real.log N / 2))
            * Real.sqrt (Real.log N) / (Real.log N) ^ 4 := by
        field_simp
        try ring
      rw [hrw, hcomb, le_div_iff₀ hL4]
      nlinarith [hQs, hE0, hL0]
    have hchain : Real.exp (-(kimDelta * Real.log N)
            - 2 * Real.sqrt (Real.log N) - 1) * (1 / (Real.log N) ^ 4)
          * (9 * Real.exp (Real.log N / 2) * Real.sqrt (Real.log N))
        ≤ bSeq N k * theta N ^ 2 * ((tParam N : ℕ) : ℝ) := by
      rw [hθe]
      have hc1 : (0 : ℝ) ≤ 1 / (Real.log N) ^ 4 := by positivity
      have hc2 : (0 : ℝ) ≤ 9 * Real.exp (Real.log N / 2)
          * Real.sqrt (Real.log N) := by positivity
      have hA := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbe hc1) hc2
      have hB := mul_le_mul_of_nonneg_left hte
        (show (0 : ℝ) ≤ bSeq N k * (1 / (Real.log N) ^ 4) by positivity)
      nlinarith [hA, hB]
    rw [hRe]
    linarith [hstep, hchain]
  have hbt0 : (0 : ℝ) ≤ bSeq N k * ((tParam N : ℕ) : ℝ) := by positivity
  have hstep2 : 3 * bSeq N k * ((N : ℝ) ^ ((1 : ℝ) / 4) * Real.log N)
        * ((tParam N : ℕ) : ℝ)
      ≤ (1 / 60) * (bSeq N k ^ 2 * theta N ^ 2 * ((tParam N : ℕ) : ℝ) ^ 2) := by
    have hm := mul_le_mul_of_nonneg_right hcore hbt0
    nlinarith [hm]
  have hstep3 : (1 / 60) * (bSeq N k ^ 2 * theta N ^ 2
        * ((tParam N : ℕ) : ℝ) ^ 2)
      ≤ (1 / 20) * bSeq N k ^ 2 * theta N ^ 2
        * (((tParam N).choose 2 : ℕ) : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hT2third
      (show (0 : ℝ) ≤ (1 / 20) * (bSeq N k ^ 2 * theta N ^ 2) by positivity)
    nlinarith [hm]
  have hlhs : (3 / 2) * bSeq N k * ((N : ℝ) ^ ((1 : ℝ) / 4) * Real.log N)
        * ((tParam N : ℕ) : ℝ) * (1 + theta N / 2)
      ≤ 3 * bSeq N k * ((N : ℝ) ^ ((1 : ℝ) / 4) * Real.log N)
        * ((tParam N : ℕ) : ℝ) := by
    have hpos : (0 : ℝ) ≤ (3 / 2) * bSeq N k
        * ((N : ℝ) ^ ((1 : ℝ) / 4) * Real.log N) * ((tParam N : ℕ) : ℝ) := by
      have hq : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      positivity
    nlinarith [hpos, hθ, hθ0]
  linarith [hlhs, hstep2, hstep3]

set_option maxHeartbeats 1000000 in
/-- **The `√log n` ledger of §4.8.**  The `Y⁽²⁾` and `Φ⁽⁴⁾` charges together
have leading term `(3/2)b²θ√n·t·(1+θ/2)`, and the allowance is
`b b′θ·C(t,2)/(3√log n)`.  These match exactly — Kim's (40) and (54) targets
are `2X` and `X` with `3X` the whole allowance — so the comparison is made
with Kim's (14) in ratio form, `b ≤ (1+θ)b′`.  Using the additive branch
`b − b′ ≤ 2bθ(a+5θ)` instead would leave a residue of order `a ≈ √(δ log n)`,
which is `O(1)` on the `θ²` ledger; the ratio form leaves `O(1/√log n)`. -/
lemma sqrtlog_ledger {N k : ℕ} (h : KimLarge N) :
    (3 / 2) * bSeq N k ^ 2 * theta N * Real.sqrt N * ((tParam N : ℕ) : ℝ)
        * (1 + theta N / 2)
      ≤ bSeq N k * bSeq N (k + 1) * theta N
          * (((tParam N).choose 2 : ℕ) : ℝ) / (3 * Real.sqrt (Real.log N))
        + (4 * bSeq N k * bSeq N (k + 1) * theta N ^ 2
              * (((tParam N).choose 2 : ℕ) : ℝ)
            + 2 * bSeq N k * bSeq N (k + 1) * theta N
              * ((tParam N : ℕ) : ℝ))
          / (6 * Real.sqrt (Real.log N)) := by
  have hn : 0 < N := h.card_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hn
  have hL := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hsL : (0 : ℝ) < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have hb0 := (bSeq_pos N k).le
  have hb'0 := (bSeq_pos N (k + 1)).le
  have hθ0 := theta_nonneg N
  have hθ : theta N ≤ 1 / 100 := h.2.1
  have ht0 : (0 : ℝ) ≤ ((tParam N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hT20 : (0 : ℝ) ≤ (((tParam N).choose 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsn0 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hbb0 : (0 : ℝ) ≤ bSeq N k * bSeq N (k + 1) := by positivity
  have htge : 9 * Real.sqrt ((N : ℝ) * Real.log N) ≤ ((tParam N : ℕ) : ℝ) :=
    tParam_ge N
  have hsplit : Real.sqrt ((N : ℝ) * Real.log N)
      = Real.sqrt N * Real.sqrt (Real.log N) := Real.sqrt_mul hNR.le _
  have hA9 : 9 * Real.sqrt N * Real.sqrt (Real.log N)
      ≤ ((tParam N : ℕ) : ℝ) := by rw [hsplit] at htge; linarith [htge]
  have hT2sq : ((tParam N : ℕ) : ℝ) ^ 2
      = 2 * (((tParam N).choose 2 : ℕ) : ℝ) + ((tParam N : ℕ) : ℝ) := by
    rw [Nat.cast_choose_two]; ring
  -- step 1: replace `9√n·√log n` by `t`
  have hstep1 : 9 * bSeq N k ^ 2 * theta N * Real.sqrt N
        * ((tParam N : ℕ) : ℝ) * (1 + theta N / 2) * Real.sqrt (Real.log N)
      ≤ bSeq N k ^ 2 * theta N * ((tParam N : ℕ) : ℝ) ^ 2
        * (1 + theta N / 2) := by
    have hcoef : (0 : ℝ) ≤ bSeq N k ^ 2 * theta N * ((tParam N : ℕ) : ℝ)
        * (1 + theta N / 2) := by positivity
    nlinarith [hA9, hcoef, hsn0, hsL.le]
  -- step 2: Kim (14) in ratio form
  have hratio : bSeq N k ^ 2
      ≤ (1 + theta N) * (bSeq N k * bSeq N (k + 1)) := by
    have h14 := bSeq_le_succ_mul hθ k
    nlinarith [h14, bSeq_pos N k, bSeq_pos N (k + 1)]
  have hfac : (1 + theta N) * (1 + theta N / 2) ≤ 1 + 2 * theta N := by
    nlinarith [hθ, hθ0]
  have hXpos : (0 : ℝ) ≤ bSeq N k * bSeq N (k + 1) * theta N
      * (2 * (((tParam N).choose 2 : ℕ) : ℝ) + ((tParam N : ℕ) : ℝ)) := by
    positivity
  have hstep2 : bSeq N k ^ 2 * theta N * ((tParam N : ℕ) : ℝ) ^ 2
        * (1 + theta N / 2)
      ≤ 2 * (bSeq N k * bSeq N (k + 1)) * theta N
          * (((tParam N).choose 2 : ℕ) : ℝ)
        + (4 * bSeq N k * bSeq N (k + 1) * theta N ^ 2
              * (((tParam N).choose 2 : ℕ) : ℝ)
            + 2 * bSeq N k * bSeq N (k + 1) * theta N
              * ((tParam N : ℕ) : ℝ)) := by
    have hcoef : (0 : ℝ) ≤ theta N * ((tParam N : ℕ) : ℝ) ^ 2
        * (1 + theta N / 2) := by positivity
    have hm := mul_le_mul_of_nonneg_right hratio hcoef
    have hA : (1 + theta N) * (bSeq N k * bSeq N (k + 1))
          * (theta N * ((tParam N : ℕ) : ℝ) ^ 2 * (1 + theta N / 2))
        ≤ (1 + 2 * theta N) * (bSeq N k * bSeq N (k + 1) * theta N
            * (2 * (((tParam N).choose 2 : ℕ) : ℝ) + ((tParam N : ℕ) : ℝ))) := by
      rw [hT2sq]
      nlinarith [hfac, hXpos]
    have hB : (1 + 2 * theta N) * (bSeq N k * bSeq N (k + 1) * theta N
          * (2 * (((tParam N).choose 2 : ℕ) : ℝ) + ((tParam N : ℕ) : ℝ)))
        ≤ 2 * (bSeq N k * bSeq N (k + 1)) * theta N
            * (((tParam N).choose 2 : ℕ) : ℝ)
          + (4 * bSeq N k * bSeq N (k + 1) * theta N ^ 2
                * (((tParam N).choose 2 : ℕ) : ℝ)
              + 2 * bSeq N k * bSeq N (k + 1) * theta N
                * ((tParam N : ℕ) : ℝ)) := by
      have hkey : (0 : ℝ) ≤ (bSeq N k * bSeq N (k + 1) * theta N
          * ((tParam N : ℕ) : ℝ)) * (1 - 2 * theta N) :=
        mul_nonneg (by positivity) (by linarith [hθ])
      nlinarith [hkey]
    linarith [hm, hA, hB]
  -- combine and divide
  have hden : (0 : ℝ) < 6 * Real.sqrt (Real.log N) := by linarith
  have hrw : bSeq N k * bSeq N (k + 1) * theta N
          * (((tParam N).choose 2 : ℕ) : ℝ) / (3 * Real.sqrt (Real.log N))
        + (4 * bSeq N k * bSeq N (k + 1) * theta N ^ 2
              * (((tParam N).choose 2 : ℕ) : ℝ)
            + 2 * bSeq N k * bSeq N (k + 1) * theta N
              * ((tParam N : ℕ) : ℝ))
          / (6 * Real.sqrt (Real.log N))
      = (2 * (bSeq N k * bSeq N (k + 1)) * theta N
            * (((tParam N).choose 2 : ℕ) : ℝ)
          + (4 * bSeq N k * bSeq N (k + 1) * theta N ^ 2
                * (((tParam N).choose 2 : ℕ) : ℝ)
              + 2 * bSeq N k * bSeq N (k + 1) * theta N
                * ((tParam N : ℕ) : ℝ)))
        / (6 * Real.sqrt (Real.log N)) := by
    field_simp
    ring
  rw [hrw, le_div_iff₀ hden]
  nlinarith [hstep1, hstep2]

set_option maxHeartbeats 1000000 in
/-- **The `√log n` residue of §4.8 is negligible.**  With Kim's (14) in ratio
form the residue is `O(1/√log n)` on the `θ²` ledger, not `O(1)`. -/
lemma KimLarge.slack_le {N k : ℕ} (h : KimLarge N) :
    (4 * bSeq N k * bSeq N (k + 1) * theta N ^ 2
          * (((tParam N).choose 2 : ℕ) : ℝ)
        + 2 * bSeq N k * bSeq N (k + 1) * theta N * ((tParam N : ℕ) : ℝ))
      / (6 * Real.sqrt (Real.log N))
    ≤ (1 / 50) * bSeq N k ^ 2 * theta N ^ 2
      * (((tParam N).choose 2 : ℕ) : ℝ) := by
  have hn : 0 < N := h.card_pos
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hsq : Real.sqrt (Real.log N) ^ 2 = Real.log N := Real.sq_sqrt hL0.le
  have hs0 : (0 : ℝ) < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have hs1000 := h.sqrt_logn_ge
  have hb0 := (bSeq_pos N k).le
  have hbb' := bSeq_succ_le N k h.theta_pos'
  have hθ0 := theta_nonneg N
  have hθ : theta N ≤ 1 / 100 := h.2.1
  have ht0 : (0 : ℝ) ≤ ((tParam N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hT20 : (0 : ℝ) ≤ (((tParam N).choose 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have htb := h.tParam_huge
  have hX0 : (0 : ℝ) ≤ bSeq N k ^ 2 * theta N ^ 2 := by positivity
  have hXT0 : (0 : ℝ) ≤ bSeq N k ^ 2 * theta N ^ 2
      * (((tParam N).choose 2 : ℕ) : ℝ) := by positivity
  -- `b·b′ ≤ b²`
  have hbb2 : bSeq N k * bSeq N (k + 1) ≤ bSeq N k ^ 2 := by nlinarith [hbb', hb0]
  have h6 : 6 * Real.log N * Real.sqrt (Real.log N) ≤ ((tParam N : ℕ) : ℝ) := by
    nlinarith [htb, hLv, hL0, hs0.le]
  have hprod0 : (1000000 : ℝ) * 1000 ≤ Real.log N * Real.sqrt (Real.log N) :=
    mul_le_mul hLv hs1000 (by norm_num) (by linarith)
  have ht3 : (3 : ℝ) ≤ ((tParam N : ℕ) : ℝ) := by linarith [h6, hprod0]
  have hT2third : ((tParam N : ℕ) : ℝ) ^ 2 / 3
      ≤ (((tParam N).choose 2 : ℕ) : ℝ) := by
    rw [Nat.cast_choose_two]
    nlinarith [mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ ((tParam N : ℕ) : ℝ) - 3)]
  -- `θ·√L·t ≥ 100`
  have hθe : theta N = 1 / Real.log N ^ 2 := by rw [theta]
  have hprod : (100 : ℝ) * Real.log N ^ 2
      ≤ Real.sqrt (Real.log N) * ((tParam N : ℕ) : ℝ) := by
    nlinarith [htb, hsq, hs0.le, hL0, hLv]
  have hkey2 : (100 : ℝ)
      ≤ Real.sqrt (Real.log N) * theta N * ((tParam N : ℕ) : ℝ) := by
    rw [hθe, show Real.sqrt (Real.log N) * (1 / Real.log N ^ 2)
        * ((tParam N : ℕ) : ℝ)
      = Real.sqrt (Real.log N) * ((tParam N : ℕ) : ℝ) / Real.log N ^ 2 by ring,
      le_div_iff₀ (by positivity : (0 : ℝ) < Real.log N ^ 2)]
    linarith [hprod]
  have hden : (0 : ℝ) < 6 * Real.sqrt (Real.log N) := by linarith
  rw [div_le_iff₀ hden]
  -- term 1
  have hA : 4 * bSeq N k * bSeq N (k + 1) * theta N ^ 2
        * (((tParam N).choose 2 : ℕ) : ℝ)
      ≤ (1 / 200) * (bSeq N k ^ 2 * theta N ^ 2
        * (((tParam N).choose 2 : ℕ) : ℝ)) * (6 * Real.sqrt (Real.log N)) := by
    have h1 : 4 * bSeq N k * bSeq N (k + 1) * theta N ^ 2
          * (((tParam N).choose 2 : ℕ) : ℝ)
        ≤ 4 * (bSeq N k ^ 2 * theta N ^ 2
          * (((tParam N).choose 2 : ℕ) : ℝ)) := by
      nlinarith [hbb2, hθ0, hT20, sq_nonneg (theta N),
        mul_nonneg (sq_nonneg (theta N)) hT20]
    nlinarith [h1, hs1000, hXT0]
  -- term 2
  have hB : 2 * bSeq N k * bSeq N (k + 1) * theta N * ((tParam N : ℕ) : ℝ)
      ≤ (1 / 100) * (bSeq N k ^ 2 * theta N ^ 2
        * (((tParam N).choose 2 : ℕ) : ℝ)) * (6 * Real.sqrt (Real.log N)) := by
    have h1 : 2 * bSeq N k * bSeq N (k + 1) * theta N * ((tParam N : ℕ) : ℝ)
        ≤ 2 * (bSeq N k ^ 2 * theta N * ((tParam N : ℕ) : ℝ)) := by
      nlinarith [hbb2, hθ0, ht0, mul_nonneg hθ0 ht0]
    -- `2 b²θt ≤ (6/100)·√L·b²θ²·T2`
    have hcoef : (0 : ℝ) ≤ bSeq N k ^ 2 * theta N := by positivity
    have h2 := mul_le_mul_of_nonneg_left hT2third
      (show (0 : ℝ) ≤ (6 / 100) * (bSeq N k ^ 2 * theta N ^ 2)
        * Real.sqrt (Real.log N) by positivity)
    have h3 := mul_le_mul_of_nonneg_left hkey2
      (show (0 : ℝ) ≤ (1 / 50) * (bSeq N k ^ 2 * theta N)
        * ((tParam N : ℕ) : ℝ) by positivity)
    nlinarith [h1, h2, h3, hcoef, ht0, hT20, hθ0, hX0]
  have hpos : (0 : ℝ) ≤ (bSeq N k ^ 2 * theta N ^ 2
      * (((tParam N).choose 2 : ℕ) : ℝ)) * (6 * Real.sqrt (Real.log N)) := by
    positivity
  linarith [hA, hB, hpos]

set_option maxHeartbeats 1000000 in
/-- **The §4.8 charge total.**  Everything Property 7's step charges, against
`budget_lower`'s allowance:  `1/50 + 3·(1/20) + 3/4 + 1/4 = 1.17` against
`8/5`. -/
lemma KimLarge.charges_le {N k : ℕ} (h : KimLarge N)
    (hF1 : 3 * (mcut N : ℝ) * ((tParam N : ℕ) : ℝ)
      ≤ (1 / 20) * bSeq N k ^ 2 * theta N ^ 2
        * (((tParam N).choose 2 : ℕ) : ℝ))
    (hF2 : (3 / 2) * bSeq N k * ((N : ℝ) ^ ((1 : ℝ) / 4) * Real.log N)
        * ((tParam N : ℕ) : ℝ) * (1 + theta N / 2)
      ≤ (1 / 20) * bSeq N k ^ 2 * theta N ^ 2
        * (((tParam N).choose 2 : ℕ) : ℝ))
    (hF3 : edgeProb N * (((tParam N).choose 2 : ℕ) : ℝ)
      ≤ (1 / 20) * bSeq N k ^ 2 * theta N ^ 2
        * (((tParam N).choose 2 : ℕ) : ℝ))
    (hSlack : (4 * bSeq N k * bSeq N (k + 1) * theta N ^ 2
            * (((tParam N).choose 2 : ℕ) : ℝ)
          + 2 * bSeq N k * bSeq N (k + 1) * theta N * ((tParam N : ℕ) : ℝ))
        / (6 * Real.sqrt (Real.log N))
      ≤ (1 / 50) * bSeq N k ^ 2 * theta N ^ 2
        * (((tParam N).choose 2 : ℕ) : ℝ)) :
    3 * (mcut N : ℝ) * ((tParam N : ℕ) : ℝ)
        + (3 / 2) * bSeq N k
          * (bSeq N k * theta N * Real.sqrt N
            + (N : ℝ) ^ ((1 : ℝ) / 4) * Real.log N)
          * (((tParam N : ℕ) : ℝ)
            + ((tParam N : ℕ) : ℝ) / (2 * Real.log N ^ 2))
        + 2 * bSeq N k ^ 3 * theta N ^ 2
          * (((tParam N).choose 2 : ℕ) : ℝ)
        + (1 / 4) * bSeq N k ^ 2 * theta N ^ 2
          * (((tParam N).choose 2 : ℕ) : ℝ)
        + edgeProb N * (((tParam N).choose 2 : ℕ) : ℝ)
      ≤ (8 / 5) * bSeq N k ^ 2 * theta N ^ 2
          * (((tParam N).choose 2 : ℕ) : ℝ)
        + (5 / 4) * bSeq N k ^ 3 * theta N ^ 2
          * (((tParam N).choose 2 : ℕ) : ℝ)
        + bSeq N k * bSeq N (k + 1) * theta N
          * (((tParam N).choose 2 : ℕ) : ℝ) / (3 * Real.sqrt (Real.log N)) := by
  have hn : 0 < N := h.card_pos
  have hL0 : (0 : ℝ) < Real.log N := by linarith [h.logn_vast]
  have hb0 := (bSeq_pos N k).le
  have hb1 := bSeq_le_one N k
  have hθ0 := theta_nonneg N
  have hT20 : (0 : ℝ) ≤ (((tParam N).choose 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hγ : ((tParam N : ℕ) : ℝ) / (2 * Real.log N ^ 2)
      = ((tParam N : ℕ) : ℝ) * theta N / 2 := by
    rw [theta]
    field_simp
    try ring
  rw [hγ]
  have hexp : (((tParam N : ℕ) : ℝ) + ((tParam N : ℕ) : ℝ) * theta N / 2)
      = ((tParam N : ℕ) : ℝ) * (1 + theta N / 2) := by ring
  rw [hexp]
  have hsplit : (3 / 2) * bSeq N k
        * (bSeq N k * theta N * Real.sqrt N
          + (N : ℝ) ^ ((1 : ℝ) / 4) * Real.log N)
        * (((tParam N : ℕ) : ℝ) * (1 + theta N / 2))
      = (3 / 2) * bSeq N k ^ 2 * theta N * Real.sqrt N
          * ((tParam N : ℕ) : ℝ) * (1 + theta N / 2)
        + (3 / 2) * bSeq N k * ((N : ℝ) ^ ((1 : ℝ) / 4) * Real.log N)
          * ((tParam N : ℕ) : ℝ) * (1 + theta N / 2) := by ring
  rw [hsplit]
  have hled := sqrtlog_ledger (N := N) (k := k) h
  have hcube : bSeq N k ^ 3 ≤ bSeq N k ^ 2 := by nlinarith [hb0, hb1]
  have hcube' : 2 * bSeq N k ^ 3 * theta N ^ 2
        * (((tParam N).choose 2 : ℕ) : ℝ)
      ≤ (5 / 4) * bSeq N k ^ 3 * theta N ^ 2
          * (((tParam N).choose 2 : ℕ) : ℝ)
        + (3 / 4) * bSeq N k ^ 2 * theta N ^ 2
          * (((tParam N).choose 2 : ℕ) : ℝ) := by
    have hc := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcube (sq_nonneg (theta N))) hT20
    nlinarith [hc]
  have hX0 : (0 : ℝ) ≤ bSeq N k ^ 2 * theta N ^ 2
      * (((tParam N).choose 2 : ℕ) : ℝ) := by positivity
  linarith [hled, hSlack, hF1, hF2, hF3, hcube', hX0]

/-- **Kim's §4.8 master inequality.**  Everything Property 7's step charges is
covered by what `μ`'s recursion and the survival factor provide. -/
lemma KimLarge.hc1_master {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    3 * (mcut N : ℝ) * ((tParam N : ℕ) : ℝ)
        + (3 / 2) * bSeq N k
          * (bSeq N k * theta N * Real.sqrt N
            + (N : ℝ) ^ ((1 : ℝ) / 4) * Real.log N)
          * (((tParam N : ℕ) : ℝ)
            + ((tParam N : ℕ) : ℝ) / (2 * Real.log N ^ 2))
        + 2 * bSeq N k ^ 3 * theta N ^ 2
          * (((tParam N).choose 2 : ℕ) : ℝ)
        + (1 / 4) * bSeq N k ^ 2 * theta N ^ 2
          * (((tParam N).choose 2 : ℕ) : ℝ)
        + edgeProb N * (((tParam N).choose 2 : ℕ) : ℝ)
      ≤ (1 - edgeProb N) ^ (2 * kimM N k) * bSeq N k * μSeq N k
          * (((tParam N).choose 2 : ℕ) : ℝ)
        - bSeq N (k + 1) * μSeq N (k + 1)
          * (((tParam N).choose 2 : ℕ) : ℝ) := by
  have hch := h.charges_le (k := k) (h.hF1_bound hk) (h.hF2_bound hk)
    (h.hF3_bound hk) (h.slack_le (k := k))
  have hbud := h.budget_lower hk
  have hT20 : (0 : ℝ) ≤ (((tParam N).choose 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hbud hT20
  have heq1 : ((8 / 5) * bSeq N k ^ 2 * theta N ^ 2
        + (5 / 4) * bSeq N k ^ 3 * theta N ^ 2
        + bSeq N k * bSeq N (k + 1) * theta N / (3 * Real.sqrt (Real.log N)))
      * (((tParam N).choose 2 : ℕ) : ℝ)
      = (8 / 5) * bSeq N k ^ 2 * theta N ^ 2
          * (((tParam N).choose 2 : ℕ) : ℝ)
        + (5 / 4) * bSeq N k ^ 3 * theta N ^ 2
          * (((tParam N).choose 2 : ℕ) : ℝ)
        + bSeq N k * bSeq N (k + 1) * theta N
          * (((tParam N).choose 2 : ℕ) : ℝ)
          / (3 * Real.sqrt (Real.log N)) := by
    ring
  have heq2 : ((1 - edgeProb N) ^ (2 * kimM N k) * bSeq N k * μSeq N k
        - bSeq N (k + 1) * μSeq N (k + 1)) * (((tParam N).choose 2 : ℕ) : ℝ)
      = (1 - edgeProb N) ^ (2 * kimM N k) * bSeq N k * μSeq N k
          * (((tParam N).choose 2 : ℕ) : ℝ)
        - bSeq N (k + 1) * μSeq N (k + 1)
          * (((tParam N).choose 2 : ℕ) : ℝ) := by ring
  rw [heq1, heq2] at hmul
  linarith [hch, hmul]

set_option maxHeartbeats 1000000 in
/-- **Each per-`T` drift beats the `C(n,t)` union.**  At Kim's
`ρ = n^{−1/4−1/17}` and deviation `λ = b²θ²C(t,2)/16`, half the drift already
exceeds `(t+3)log n`, so `C(n,t)·q ≤ exp(−log n)` for each of (38), (39), (46),
(49). -/
lemma KimLarge.drift_beats_union {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    ((tParam N : ℕ) : ℝ) * Real.log N + 3 * Real.log N
      ≤ kimRho7 N * (bSeq N k ^ 2 * theta N ^ 2
          * (((tParam N).choose 2 : ℕ) : ℝ) / 16) / 2 := by
  have hn : 0 < N := h.card_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hn
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have hs1000 := h.sqrt_logn_ge
  have hsq : Real.sqrt (Real.log N) ^ 2 = Real.log N := Real.sq_sqrt hL0.le
  have hsL : Real.sqrt (Real.log N) ≤ Real.log N := by
    nlinarith [hsq, hs0.le, hLv]
  have hexpL : (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log hNR).symm
  have hsqrtN := sqrtN_eq_exp hn
  have hbsq := h.bSq_ge hk
  have hθ2 : theta N ^ 2 = 1 / (Real.log N) ^ 4 := by rw [theta]; field_simp
  have ht0 : (0 : ℝ) ≤ ((tParam N : ℕ) : ℝ) := Nat.cast_nonneg _
  -- `C(t,2) ≥ 27·n·log n`
  have htge : 9 * Real.sqrt ((N : ℝ) * Real.log N) ≤ ((tParam N : ℕ) : ℝ) :=
    tParam_ge N
  have hmul : Real.sqrt ((N : ℝ) * Real.log N) ^ 2 = (N : ℝ) * Real.log N :=
    Real.sq_sqrt (by positivity)
  have htsq : 81 * ((N : ℝ) * Real.log N) ≤ ((tParam N : ℕ) : ℝ) ^ 2 := by
    nlinarith [htge, hmul, Real.sqrt_nonneg ((N : ℝ) * Real.log N)]
  have ht3 : (3 : ℝ) ≤ ((tParam N : ℕ) : ℝ) := by
    have hnL : (1 : ℝ) ≤ (N : ℝ) * Real.log N := by
      nlinarith [h.1, hLv, hNR]
    have h1 : Real.sqrt 1 ≤ Real.sqrt ((N : ℝ) * Real.log N) :=
      Real.sqrt_le_sqrt hnL
    rw [Real.sqrt_one] at h1
    linarith [htge, h1]
  have hT2third : ((tParam N : ℕ) : ℝ) ^ 2 / 3
      ≤ (((tParam N).choose 2 : ℕ) : ℝ) := by
    rw [Nat.cast_choose_two]
    nlinarith [mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ ((tParam N : ℕ) : ℝ) - 3)]
  have hT2ge : 27 * ((N : ℝ) * Real.log N)
      ≤ (((tParam N).choose 2 : ℕ) : ℝ) := by linarith [htsq, hT2third]
  -- `t + 3 ≤ 10√n√log n`
  have htle : ((tParam N : ℕ) : ℝ) + 3
      ≤ 10 * Real.sqrt N * Real.sqrt (Real.log N) := by
    have h1 := tParam_le_bound hn
    have hsN : (1 : ℝ) ≤ Real.sqrt N := one_le_sqrt_cast hn
    nlinarith [h1, hsN, hs1000]
  -- the exponential comparison
  have hρ : kimRho7 N
      = Real.exp (-(((1 : ℝ) / 4 + 1 / 17) * Real.log N)) := by
    rw [kimRho7, Real.rpow_def_of_pos hNR]
    congr 1
    ring
  have hcl := h.asym.p7_drift
  have hQ : Real.exp (((1 : ℝ) / 4 - 1 / 17 - 2 * kimDelta) * Real.log N
        - 4 * Real.sqrt (Real.log N) - 2) * Real.exp (Real.log N / 2)
      = Real.exp (((3 : ℝ) / 4 - 1 / 17 - 2 * kimDelta) * Real.log N
        - 4 * Real.sqrt (Real.log N) - 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE0 : (0 : ℝ) < Real.exp (Real.log N / 2) := Real.exp_pos _
  have hbig : 12 * (Real.log N) ^ 5 * Real.exp (Real.log N / 2)
      ≤ Real.exp (((3 : ℝ) / 4 - 1 / 17 - 2 * kimDelta) * Real.log N
        - 4 * Real.sqrt (Real.log N) - 2) := by
    rw [← hQ]
    exact mul_le_mul_of_nonneg_right hcl hE0.le
  -- the right-hand side, from below
  have hL4 : (0 : ℝ) < (Real.log N) ^ 4 := by positivity
  have hkey : (27 / 32) * (Real.exp (((3 : ℝ) / 4 - 1 / 17 - 2 * kimDelta)
          * Real.log N - 4 * Real.sqrt (Real.log N) - 2) / (Real.log N) ^ 3)
      ≤ kimRho7 N * (bSeq N k ^ 2 * theta N ^ 2
          * (((tParam N).choose 2 : ℕ) : ℝ) / 16) / 2 := by
    rw [hρ, hθ2]
    have hcomb : Real.exp (-(((1 : ℝ) / 4 + 1 / 17) * Real.log N))
          * Real.exp (-(2 * kimDelta * Real.log N)
            - 4 * Real.sqrt (Real.log N) - 2) * Real.exp (Real.log N)
        = Real.exp (((3 : ℝ) / 4 - 1 / 17 - 2 * kimDelta) * Real.log N
            - 4 * Real.sqrt (Real.log N) - 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hρ0 : (0 : ℝ) < Real.exp (-(((1 : ℝ) / 4 + 1 / 17) * Real.log N)) :=
      Real.exp_pos _
    have hA : Real.exp (-(((1 : ℝ) / 4 + 1 / 17) * Real.log N))
          * (Real.exp (-(2 * kimDelta * Real.log N)
              - 4 * Real.sqrt (Real.log N) - 2)
            * (1 / (Real.log N) ^ 4) * (27 * ((N : ℝ) * Real.log N)) / 16) / 2
        ≤ Real.exp (-(((1 : ℝ) / 4 + 1 / 17) * Real.log N))
          * (bSeq N k ^ 2 * (1 / (Real.log N) ^ 4)
            * (((tParam N).choose 2 : ℕ) : ℝ) / 16) / 2 := by
      have hc : (0 : ℝ) ≤ 1 / (Real.log N) ^ 4 := by positivity
      have h1 := mul_le_mul_of_nonneg_right hbsq hc
      have h2 : Real.exp (-(2 * kimDelta * Real.log N)
            - 4 * Real.sqrt (Real.log N) - 2) * (1 / (Real.log N) ^ 4)
            * (27 * ((N : ℝ) * Real.log N))
          ≤ bSeq N k ^ 2 * (1 / (Real.log N) ^ 4)
            * (((tParam N).choose 2 : ℕ) : ℝ) := by
        have hnn : (0 : ℝ) ≤ 27 * ((N : ℝ) * Real.log N) := by positivity
        nlinarith [h1, hT2ge, hnn, mul_nonneg (sq_nonneg (bSeq N k)) hc]
      nlinarith [h2, hρ0]
    refine le_trans (le_of_eq ?_) hA
    rw [← hcomb, ← hexpL]
    field_simp
    ring
  -- assemble
  have hfin : ((tParam N : ℕ) : ℝ) * Real.log N + 3 * Real.log N
      ≤ (27 / 32) * (Real.exp (((3 : ℝ) / 4 - 1 / 17 - 2 * kimDelta)
          * Real.log N - 4 * Real.sqrt (Real.log N) - 2)
        / (Real.log N) ^ 3) := by
    have hlhs : ((tParam N : ℕ) : ℝ) * Real.log N + 3 * Real.log N
        ≤ 10 * Real.exp (Real.log N / 2) * (Real.log N) ^ 2 := by
      have h1 : ((tParam N : ℕ) : ℝ) + 3
          ≤ 10 * Real.exp (Real.log N / 2) * Real.sqrt (Real.log N) := by
        rw [← hsqrtN]; exact htle
      have h2 := mul_le_mul_of_nonneg_right h1 hL0.le
      have h3 := mul_le_mul_of_nonneg_left hsL
        (show (0 : ℝ) ≤ 10 * Real.exp (Real.log N / 2) * Real.log N by
          positivity)
      linarith [h2, h3]
    have hrhs : 10 * Real.exp (Real.log N / 2) * (Real.log N) ^ 2
        ≤ (27 / 32) * (Real.exp (((3 : ℝ) / 4 - 1 / 17 - 2 * kimDelta)
            * Real.log N - 4 * Real.sqrt (Real.log N) - 2)
          / (Real.log N) ^ 3) := by
      have hX0 : (0 : ℝ) ≤ (Real.log N) ^ 5 * Real.exp (Real.log N / 2) := by
        positivity
      rw [mul_div_assoc',
        le_div_iff₀ (by positivity : (0 : ℝ) < (Real.log N) ^ 3)]
      nlinarith [hbig, hX0]
    linarith [hlhs, hrhs]
  linarith [hfin, hkey]

open scoped Classical in
/-- **`|Γ(T)| ≤ b_k·C(t,2)` for `T ∈ 𝒯`**, from Property 6's unipartite clause.

The extra factor `b` is what makes the `θ²` ledger of §4.8 close: charging
`Φ⁽³⁾` and `lam₁` against `|Γ(T)| ≤ C(t,2)` would cost `2` and `1/2` where the
allowance `18b·b′θ²` only affords `O(b)`. -/
lemma Property6.gammaT_le {s : BlockState V} {i : ℕ} (h6 : Property6 s i)
    (hcut : 1 ≤ mcut n) (htcut : 2 * mcut n ≤ tParam n)
    {T : Finset V} (hT : T ∈ calT s) :
    ((gammaBetween s.Γ T T).card : ℝ)
      ≤ bSeq n i * (((tParam n).choose 2 : ℕ) : ℝ) := by
  have hcardT : T.card = tParam n := card_of_mem_calT hT
  have h := h6.self hcut T (by rw [hcardT]; exact htcut)
  rwa [hcardT] at h

/-- `2·mcut n ≤ t`. -/
lemma KimLarge.two_mcut_le_t {N : ℕ} (h : KimLarge N) : 2 * mcut N ≤ tParam N := by
  have hn : 0 < N := h.card_pos
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
  have hL := h.logn_big
  have hmc : (mcut N : ℝ) ≤ Real.sqrt N := h.mcut_le_sqrtN
  have ht : 9 * Real.sqrt ((N : ℝ) * Real.log N) ≤ (tParam N : ℝ) :=
    tParam_ge N
  have hsq : Real.sqrt ((N : ℝ) * Real.log N)
      = Real.sqrt N * Real.sqrt (Real.log N) :=
    Real.sqrt_mul (by linarith) _
  have hsL : (1 : ℝ) ≤ Real.sqrt (Real.log N) := by
    have h1 : Real.sqrt 1 ≤ Real.sqrt (Real.log N) :=
      Real.sqrt_le_sqrt (by linarith)
    simpa using h1
  have hsN : Real.sqrt N ≤ Real.sqrt N := le_rfl
  have hsN0 : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hfin : 2 * (mcut N : ℝ) ≤ (tParam N : ℝ) := by
    have h1 : Real.sqrt N ≤ Real.sqrt N * Real.sqrt (Real.log N) := by
      nlinarith [hsL, hsN0]
    nlinarith [hmc, hsN, h1, ht, hsq.le, hsq.ge]
  exact_mod_cast hfin


/-- `C(t,2) ≥ 27·n·log n`. -/
lemma KimLarge.T2_ge {N : ℕ} (h : KimLarge N) :
    27 * ((N : ℝ) * Real.log N) ≤ (((tParam N).choose 2 : ℕ) : ℝ) := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hLv := h.logn_vast
  have ht0 : (0 : ℝ) ≤ ((tParam N : ℕ) : ℝ) := Nat.cast_nonneg _
  have htge : 9 * Real.sqrt ((N : ℝ) * Real.log N) ≤ ((tParam N : ℕ) : ℝ) :=
    tParam_ge N
  have hmul : Real.sqrt ((N : ℝ) * Real.log N) ^ 2 = (N : ℝ) * Real.log N :=
    Real.sq_sqrt (by positivity)
  have htsq : 81 * ((N : ℝ) * Real.log N) ≤ ((tParam N : ℕ) : ℝ) ^ 2 := by
    nlinarith [htge, hmul, Real.sqrt_nonneg ((N : ℝ) * Real.log N)]
  have ht3 : (3 : ℝ) ≤ ((tParam N : ℕ) : ℝ) := by
    have hnL : (1 : ℝ) ≤ (N : ℝ) * Real.log N := by nlinarith [h.1, hLv, hNR]
    have h1 : Real.sqrt 1 ≤ Real.sqrt ((N : ℝ) * Real.log N) :=
      Real.sqrt_le_sqrt hnL
    rw [Real.sqrt_one] at h1
    linarith [htge, h1]
  have hT2third : ((tParam N : ℕ) : ℝ) ^ 2 / 3
      ≤ (((tParam N).choose 2 : ℕ) : ℝ) := by
    rw [Nat.cast_choose_two]
    nlinarith [mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ ((tParam N : ℕ) : ℝ) - 3)]
  linarith [htsq, hT2third]

/-- `t ≤ 10√n·√log n`. -/
lemma KimLarge.tParam_le' {N : ℕ} (h : KimLarge N) :
    ((tParam N : ℕ) : ℝ) ≤ 10 * Real.sqrt N * Real.sqrt (Real.log N) := by
  have hn := h.card_pos
  have h1 := tParam_le_bound hn
  have hsN : (1 : ℝ) ≤ Real.sqrt N := one_le_sqrt_cast hn
  have hs1000 := h.sqrt_logn_ge
  nlinarith [h1, hsN, hs1000]

/-- `√t ≤ 4·n^{1/4}·log n`. -/
lemma KimLarge.sqrt_tParam_le {N : ℕ} (h : KimLarge N) :
    Real.sqrt ((tParam N : ℕ) : ℝ)
      ≤ 4 * Real.exp (Real.log N / 4) * Real.log N := by
  have hn := h.card_pos
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hs1000 := h.sqrt_logn_ge
  have hsq : Real.sqrt (Real.log N) ^ 2 = Real.log N := Real.sq_sqrt hL0.le
  have hsL : Real.sqrt (Real.log N) ≤ Real.log N := by
    nlinarith [hsq, Real.sqrt_nonneg (Real.log N), hLv]
  have hsN := sqrtN_eq_exp hn
  have hQ0 : (0 : ℝ) ≤ 4 * Real.exp (Real.log N / 4) * Real.log N := by
    positivity
  have hquarter : Real.exp (Real.log N / 4) ^ 2 = Real.sqrt N := by
    rw [exp_sq, hsN]; congr 1; ring
  have hbig : ((tParam N : ℕ) : ℝ)
      ≤ (4 * Real.exp (Real.log N / 4) * Real.log N) ^ 2 := by
    have hrw : (4 * Real.exp (Real.log N / 4) * Real.log N) ^ 2
        = 16 * Real.sqrt N * (Real.log N) ^ 2 := by
      rw [mul_pow, mul_pow, hquarter]; ring
    rw [hrw]
    have hle := h.tParam_le'
    have hsN0 : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
    have hL2 : Real.sqrt (Real.log N) ≤ (Real.log N) ^ 2 := by
      nlinarith [hsL, hL0, hLv]
    have hin : 10 * Real.sqrt (Real.log N) ≤ 16 * (Real.log N) ^ 2 := by
      linarith [hL2, sq_nonneg (Real.log N)]
    have hstep : 10 * Real.sqrt N * Real.sqrt (Real.log N)
        ≤ 16 * Real.sqrt N * (Real.log N) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hin hsN0
      linarith [this]
    linarith [hle, hstep]
  calc Real.sqrt ((tParam N : ℕ) : ℝ)
      ≤ Real.sqrt ((4 * Real.exp (Real.log N / 4) * Real.log N) ^ 2) :=
        Real.sqrt_le_sqrt hbig
    _ = 4 * Real.exp (Real.log N / 4) * Real.log N := Real.sqrt_sq hQ0

/-- **`192·ρ₇·thr·(log n)³ ≤ 1`**: Kim's §4.8 tilt is admissible against his
truncation threshold `thr = 2β√t`.  The exponent is `1/17 − δ/2 = 0.029`. -/
lemma KimLarge.rho7_thr7_le {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    192 * kimRho7 N * kimThr7 N k * (Real.log N) ^ 3 ≤ 1 := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hβ := h.beta_le hk
  have hβ0 := kimBeta_nonneg N k
  have hst := h.sqrt_tParam_le
  have hst0 : (0 : ℝ) ≤ Real.sqrt ((tParam N : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hρ0 : (0 : ℝ) < kimRho7 N := Real.rpow_pos_of_pos hNR _
  have hcl := h.asym.p7_39var
  -- `thr ≤ 16·e^{δL/2}·e^{L/4}·L³`
  have hthr : kimThr7 N k
      ≤ 16 * Real.exp (kimDelta * Real.log N / 2)
        * Real.exp (Real.log N / 4) * (Real.log N) ^ 3 := by
    rw [kimThr7]
    have hA : 2 * kimBeta N k
        ≤ 2 * (2 * Real.exp (kimDelta * Real.log N / 2) * (Real.log N) ^ 2) := by
      linarith
    have hB0 : (0 : ℝ) ≤ 2 * (2 * Real.exp (kimDelta * Real.log N / 2)
        * (Real.log N) ^ 2) := by positivity
    calc 2 * kimBeta N k * Real.sqrt ((tParam N : ℕ) : ℝ)
        ≤ 2 * (2 * Real.exp (kimDelta * Real.log N / 2) * (Real.log N) ^ 2)
            * Real.sqrt ((tParam N : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hA hst0
      _ ≤ 2 * (2 * Real.exp (kimDelta * Real.log N / 2) * (Real.log N) ^ 2)
            * (4 * Real.exp (Real.log N / 4) * Real.log N) :=
          mul_le_mul_of_nonneg_left hst hB0
      _ = 16 * Real.exp (kimDelta * Real.log N / 2)
            * Real.exp (Real.log N / 4) * (Real.log N) ^ 3 := by ring
  -- `192ρ·(that)·L³ = 3072L⁶·e^{(δ/2−1/17)L}`
  have hρe : kimRho7 N
      = Real.exp (-(((1 : ℝ) / 4 + 1 / 17) * Real.log N)) := by
    rw [kimRho7, Real.rpow_def_of_pos hNR]; congr 1; ring
  have hcollapse : 192 * kimRho7 N
        * (16 * Real.exp (kimDelta * Real.log N / 2)
          * Real.exp (Real.log N / 4) * (Real.log N) ^ 3) * (Real.log N) ^ 3
      = 3072 * (Real.log N) ^ 6
        / Real.exp (((1 : ℝ) / 17 - kimDelta / 2) * Real.log N) := by
    rw [hρe, _root_.eq_div_iff (ne_of_gt (Real.exp_pos _))]
    have hprod : Real.exp (-(((1 : ℝ) / 4 + 1 / 17) * Real.log N))
        * Real.exp (kimDelta * Real.log N / 2)
        * Real.exp (Real.log N / 4)
        * Real.exp (((1 : ℝ) / 17 - kimDelta / 2) * Real.log N) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
        show -(((1 : ℝ) / 4 + 1 / 17) * Real.log N)
          + kimDelta * Real.log N / 2 + Real.log N / 4
          + ((1 : ℝ) / 17 - kimDelta / 2) * Real.log N = 0 by ring,
        Real.exp_zero]
    linear_combination (3072 * (Real.log N) ^ 6) * hprod
  have hfin : 3072 * (Real.log N) ^ 6
      / Real.exp (((1 : ℝ) / 17 - kimDelta / 2) * Real.log N) ≤ 1 := by
    rw [div_le_one (Real.exp_pos _)]
    have hmono : Real.exp (((1 : ℝ) / 17 - kimDelta / 2) * Real.log N
          - 2 * Real.sqrt (Real.log N) - 1)
        ≤ Real.exp (((1 : ℝ) / 17 - kimDelta / 2) * Real.log N) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [Real.sqrt_nonneg (Real.log N)]
    linarith [hcl, hmono]
  have hpre : (0 : ℝ) ≤ 192 * kimRho7 N := by positivity
  have hstep : 192 * kimRho7 N * kimThr7 N k * (Real.log N) ^ 3
      ≤ 192 * kimRho7 N
        * (16 * Real.exp (kimDelta * Real.log N / 2)
          * Real.exp (Real.log N / 4) * (Real.log N) ^ 3)
        * (Real.log N) ^ 3 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hthr hpre)
      (by positivity)
  linarith [hstep, hcollapse.le, hcollapse.ge, hfin]

/-- `ρ₇·thr ≤ 1/192`, hence `exp(2ρ₇thr) ≤ 3`. -/
lemma KimLarge.rho7_thr7_small {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    kimRho7 N * kimThr7 N k ≤ 1 / 192 := by
  have hkey := h.rho7_thr7_le hk
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hL3 : (1 : ℝ) ≤ (Real.log N) ^ 3 := one_le_pow₀ (by linarith)
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hρ0 : (0 : ℝ) < kimRho7 N := Real.rpow_pos_of_pos hNR _
  have hthr0 : (0 : ℝ) ≤ kimThr7 N k := by
    rw [kimThr7]
    have := kimBeta_nonneg N k
    positivity
  nlinarith [hkey, hL3, mul_nonneg hρ0.le hthr0]

/-- Kim's deviation scale `λ = b²θ²C(t,2)/16` for (38), (39), (46) and (49). -/
noncomputable def kimLam (N k : ℕ) : ℝ :=
  bSeq N k ^ 2 * theta N ^ 2 * (((tParam N).choose 2 : ℕ) : ℝ) / 16

lemma kimLam_nonneg (N k : ℕ) : 0 ≤ kimLam N k := by
  rw [kimLam]; positivity

/-- **`b ≥ e^{−δL−2√L−1}`**, in the `√L` form the tail estimates use. -/
lemma KimLarge.bSeq_ge' {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    Real.exp (-(kimDelta * Real.log N) - 2 * Real.sqrt (Real.log N) - 1)
      ≤ bSeq N k := by
  have hn := h.card_pos
  have hL := h.logn_big
  have hb := bSeq_ge_of_k_le hn h.theta_pos' hk
  refine le_trans (Real.exp_le_exp.mpr ?_) hb
  have hsq : Real.sqrt (kimDelta * Real.log N) ≤ Real.sqrt (Real.log N) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith [kimDelta_lt, kimDelta_pos, hL]
  linarith

/-- **`48p ≤ bθ²`.**  The edge probability is `n^{−1/2}` up to polylogs while
`b` is at worst `n^{−δ}`, so `p` is smaller than `bθ²` by `n^{1/2−δ}`. -/
lemma KimLarge.p_le_b_theta_sq {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    48 * edgeProb N ≤ bSeq N k * theta N ^ 2 := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hL := h.logn_big
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hb := h.bSeq_ge' hk
  have hcl := h.asym.p7_quarter
  have hsN := sqrtN_eq_exp hn
  have hθ : theta N ^ 2 = 1 / (Real.log N) ^ 4 := by rw [theta]; field_simp
  rw [hθ, mul_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < (Real.log N) ^ 4)]
  have hval : 48 * edgeProb N * (Real.log N) ^ 4
      = 48 * (Real.log N) ^ 2 * Real.exp (-(Real.log N / 2)) := by
    rw [edgeProb, theta, hsN, Real.exp_neg]
    field_simp
    try ring
  rw [hval]
  have hmono : Real.exp (((1 : ℝ) / 4 - kimDelta) * Real.log N
        - 2 * Real.sqrt (Real.log N) - 1)
      ≤ Real.exp (((1 : ℝ) / 2 - kimDelta) * Real.log N
          - 2 * Real.sqrt (Real.log N) - 1) :=
    Real.exp_le_exp.mpr (by nlinarith [hL0])
  have h48 : 48 * (Real.log N) ^ 2 ≤ 11 * (Real.log N) ^ 5 := by
    have hL3 : (5 : ℝ) ≤ (Real.log N) ^ 3 := by nlinarith [hL, hL0]
    have hL2 : (0 : ℝ) < (Real.log N) ^ 2 := by positivity
    have hsplit : 11 * (Real.log N) ^ 5
        = 11 * (Real.log N) ^ 2 * (Real.log N) ^ 3 := by ring
    nlinarith [hL3, hL2, hsplit.le, hsplit.ge]
  have hstep : 48 * (Real.log N) ^ 2
      ≤ Real.exp (((1 : ℝ) / 2 - kimDelta) * Real.log N
          - 2 * Real.sqrt (Real.log N) - 1) := by
    linarith [hcl, hmono, h48]
  have hEexp : Real.exp (((1 : ℝ) / 2 - kimDelta) * Real.log N
        - 2 * Real.sqrt (Real.log N) - 1) * Real.exp (-(Real.log N / 2))
      = Real.exp (-(kimDelta * Real.log N)
          - 2 * Real.sqrt (Real.log N) - 1) := by
    rw [← Real.exp_add]; congr 1; ring
  have hX0 : (0 : ℝ) < Real.exp (-(Real.log N / 2)) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right hstep hX0.le
  rw [hEexp] at hmul
  linarith [hmul, hb]

/-- The scalar shape of the (38) variance comparison. -/
lemma var38_core {ρ p b T θ2 E : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hb0 : 0 ≤ b) (hT0 : 0 ≤ T)
    (hE0 : 0 ≤ E) (hE : E ≤ 3) (hθ0 : 0 ≤ θ2) (hkey : 48 * p ≤ b * θ2) :
    ρ ^ 2 / 2 * (p * (1 - p) * ((b * T) * E)) ≤ ρ * (b ^ 2 * θ2 * T / 16) / 2 := by
  have hcoef : (0 : ℝ) ≤ ρ * b * T / 32 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hkey hcoef
  -- `48p·(ρbT/32) ≤ bθ₂·(ρbT/32)`, i.e. `(3/2)ρpbT ≤ ρb²θ₂T/32`
  have hbt : (0 : ℝ) ≤ b * T := mul_nonneg hb0 hT0
  have h1a : (b * T) * E ≤ (b * T) * 3 := mul_le_mul_of_nonneg_left hE hbt
  have h1c : (0 : ℝ) ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  have h1b : p * (1 - p) ≤ p := by nlinarith [hp0, hp1]
  have h1 : p * (1 - p) * ((b * T) * E) ≤ p * ((b * T) * 3) :=
    calc p * (1 - p) * ((b * T) * E)
        ≤ p * (1 - p) * ((b * T) * 3) := mul_le_mul_of_nonneg_left h1a h1c
      _ ≤ p * ((b * T) * 3) :=
          mul_le_mul_of_nonneg_right h1b (by linarith [hbt])
  have h2 : ρ ^ 2 / 2 ≤ ρ / 2 := by nlinarith [hρ0, hρ1]
  have h3 : (0 : ℝ) ≤ p * (1 - p) * ((b * T) * E) := by
    have h1p : (0 : ℝ) ≤ 1 - p := by linarith
    have : (0 : ℝ) ≤ (b * T) * E := mul_nonneg hbt hE0
    exact mul_nonneg h1c this
  have hA : ρ ^ 2 / 2 * (p * (1 - p) * ((b * T) * E))
      ≤ ρ / 2 * (p * (1 - p) * ((b * T) * E)) :=
    mul_le_mul_of_nonneg_right h2 h3
  have hB : ρ / 2 * (p * (1 - p) * ((b * T) * E))
      ≤ ρ / 2 * (p * ((b * T) * 3)) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have hC : ρ / 2 * (p * ((b * T) * 3)) = 3 / 2 * (ρ * p * b * T) := by ring
  have hmul2 : 3 / 2 * (ρ * p * b * T) ≤ ρ * (b ^ 2 * θ2 * T / 16) / 2 := by
    linear_combination hmul
  linarith [hA, hB, hC.le, hC.ge, hmul2]

/-- **Kim's §4.8 (38) variance condition** at his tilt `ρ = n^{−5/17}`. -/
lemma KimLarge.var38 {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    kimRho38 N ^ 2 / 2 * (edgeProb N * (1 - edgeProb N)
        * ((bSeq N k * (((tParam N).choose 2 : ℕ) : ℝ))
          * Real.exp (kimRho38 N)))
      ≤ kimRho38 N * kimLam N k / 2 := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hρ0 : (0 : ℝ) ≤ kimRho38 N := kimRho38_nonneg N
  have hρ1 : kimRho38 N ≤ 1 := by
    rw [kimRho38]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast hn) (by norm_num)
  have hp0 : (0 : ℝ) ≤ edgeProb N := by
    rw [edgeProb]
    exact le_of_lt (div_pos h.theta_pos' (Real.sqrt_pos.mpr hNR))
  have hp1 : edgeProb N ≤ 1 := by linarith [h.edgeProb_le_half]
  have hexpρ : Real.exp (kimRho38 N) ≤ 3 := by
    have h1 : Real.exp (kimRho38 N) ≤ Real.exp 1 := Real.exp_le_exp.mpr hρ1
    have h2 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  rw [kimLam]
  exact var38_core hρ0 hρ1 hp0 hp1 (bSeq_pos N k).le (Nat.cast_nonneg _)
    (Real.exp_pos _).le hexpρ (by positivity) (h.p_le_b_theta_sq hk)


/-- The scalar shape of the (39) variance comparison. -/
lemma var39_core {ρ p thr M b T θ E : ℝ}
    (hρ0 : 0 ≤ ρ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hthr0 : 0 ≤ thr) (hM0 : 0 ≤ M) (hb0 : 0 ≤ b) (hT0 : 0 ≤ T)
    (hE0 : 0 ≤ E) (hE : E ≤ 3)
    (hkey : 192 * ρ * p * thr * M ≤ b * θ ^ 2) :
    ρ ^ 2 / 2 * (p * (1 - p) * ((2 * thr) * (2 * M * (b * T)) * E))
      ≤ ρ * (b ^ 2 * θ ^ 2 * T / 16) / 2 := by
  have hQ0 : (0 : ℝ) ≤ (2 * thr) * (2 * M * (b * T)) := by
    have : (0 : ℝ) ≤ b * T := mul_nonneg hb0 hT0
    have h2 : (0 : ℝ) ≤ 2 * M * (b * T) := by nlinarith [hM0, this]
    nlinarith [hthr0, h2]
  have h1 : (2 * thr) * (2 * M * (b * T)) * E
      ≤ (2 * thr) * (2 * M * (b * T)) * 3 := mul_le_mul_of_nonneg_left hE hQ0
  have h1c : (0 : ℝ) ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  have h2 : p * (1 - p) ≤ p := by nlinarith [hp0, hp1]
  have hX : p * (1 - p) * ((2 * thr) * (2 * M * (b * T)) * E)
      ≤ 12 * (p * thr * M * b * T) :=
    calc p * (1 - p) * ((2 * thr) * (2 * M * (b * T)) * E)
        ≤ p * (1 - p) * ((2 * thr) * (2 * M * (b * T)) * 3) :=
          mul_le_mul_of_nonneg_left h1 h1c
      _ ≤ p * ((2 * thr) * (2 * M * (b * T)) * 3) :=
          mul_le_mul_of_nonneg_right h2 (by linarith [hQ0])
      _ = 12 * (p * thr * M * b * T) := by ring
  have hA : ρ ^ 2 / 2 * (p * (1 - p) * ((2 * thr) * (2 * M * (b * T)) * E))
      ≤ ρ ^ 2 / 2 * (12 * (p * thr * M * b * T)) :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  have hbT0 : (0 : ℝ) ≤ b * T / 32 := by positivity
  have hC : 192 * ρ * p * thr * M * (b * T / 32)
      ≤ b * θ ^ 2 * (b * T / 32) := mul_le_mul_of_nonneg_right hkey hbT0
  have hD : ρ * (192 * ρ * p * thr * M * (b * T / 32))
      ≤ ρ * (b * θ ^ 2 * (b * T / 32)) := mul_le_mul_of_nonneg_left hC hρ0
  have hB : ρ ^ 2 / 2 * (12 * (p * thr * M * b * T))
      = ρ * (192 * ρ * p * thr * M * (b * T / 32)) := by ring
  have hF : ρ * (b * θ ^ 2 * (b * T / 32)) = ρ * (b ^ 2 * θ ^ 2 * T / 16) / 2 := by
    ring
  linarith [hA, hB.le, hB.ge, hD, hF.le, hF.ge]

/-- **`192·ρ₇·p·thr·M ≤ bθ²`**, the scalar behind Kim's (39).

`pM ≤ θb√log n` (Kim's `M = ⌈b(a+5θ)√n⌉` against `p = θ/√n`), so this is
`192ρ₇·thr·√log n ≤ θ`, i.e. `rho7_thr7_le`. -/
lemma KimLarge.key39 {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    192 * kimRho7 N * edgeProb N * kimThr7 N k * (kimM N k : ℝ)
      ≤ bSeq N k * theta N ^ 2 := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hsN0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have hsq : Real.sqrt (Real.log N) ^ 2 = Real.log N := Real.sq_sqrt hL0.le
  have hsL : Real.sqrt (Real.log N) ≤ Real.log N := by
    nlinarith [hsq, hs0.le, hLv]
  have hθ0 := h.theta_pos'
  have hb0 := bSeq_pos N k
  have hthr0 : (0 : ℝ) ≤ kimThr7 N k := by
    rw [kimThr7]
    have := kimBeta_nonneg N k
    have := Real.sqrt_nonneg ((tParam N : ℕ) : ℝ)
    positivity
  have hρ0 : (0 : ℝ) < kimRho7 N := Real.rpow_pos_of_pos hNR _
  -- `pM ≤ θb√L`
  have hpM : edgeProb N * (kimM N k : ℝ)
      ≤ theta N * bSeq N k * Real.sqrt (Real.log N) := by
    have hM := h.kimM_le_b hk
    have hpp : (0 : ℝ) ≤ edgeProb N := by
      rw [edgeProb]; exact le_of_lt (div_pos hθ0 hsN0)
    have hstep : edgeProb N * (kimM N k : ℝ)
        ≤ edgeProb N * (bSeq N k * Real.sqrt (Real.log N) * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left hM hpp
    have heq : edgeProb N * (bSeq N k * Real.sqrt (Real.log N) * Real.sqrt N)
        = theta N * bSeq N k * Real.sqrt (Real.log N) := by
      rw [edgeProb]; field_simp; try ring
    linarith [hstep, heq.le, heq.ge]
  -- `192ρ·thr·√L ≤ θ`
  have hmain : 192 * kimRho7 N * kimThr7 N k * Real.sqrt (Real.log N)
      ≤ theta N := by
    have hkey := h.rho7_thr7_le hk
    have hpre : (0 : ℝ) ≤ 192 * kimRho7 N * kimThr7 N k := by positivity
    have hL2 : (0 : ℝ) < (Real.log N) ^ 2 := by positivity
    rw [theta, le_div_iff₀ hL2]
    have hcube : Real.sqrt (Real.log N) * (Real.log N) ^ 2
        ≤ (Real.log N) ^ 3 := by nlinarith [hsL, hL2]
    have hstep : 192 * kimRho7 N * kimThr7 N k
          * (Real.sqrt (Real.log N) * (Real.log N) ^ 2)
        ≤ 192 * kimRho7 N * kimThr7 N k * (Real.log N) ^ 3 :=
      mul_le_mul_of_nonneg_left hcube hpre
    nlinarith [hstep, hkey]
  -- combine
  have hpre2 : (0 : ℝ) ≤ 192 * kimRho7 N * kimThr7 N k := by positivity
  have hstep2 : 192 * kimRho7 N * kimThr7 N k * (edgeProb N * (kimM N k : ℝ))
      ≤ 192 * kimRho7 N * kimThr7 N k
        * (theta N * bSeq N k * Real.sqrt (Real.log N)) :=
    mul_le_mul_of_nonneg_left hpM hpre2
  have hstep3 : 192 * kimRho7 N * kimThr7 N k * Real.sqrt (Real.log N)
        * (theta N * bSeq N k)
      ≤ theta N * (theta N * bSeq N k) :=
    mul_le_mul_of_nonneg_right hmain (by positivity)
  have hr1 : 192 * kimRho7 N * edgeProb N * kimThr7 N k * (kimM N k : ℝ)
      = 192 * kimRho7 N * kimThr7 N k * (edgeProb N * (kimM N k : ℝ)) := by ring
  have hr2 : 192 * kimRho7 N * kimThr7 N k
        * (theta N * bSeq N k * Real.sqrt (Real.log N))
      = 192 * kimRho7 N * kimThr7 N k * Real.sqrt (Real.log N)
        * (theta N * bSeq N k) := by ring
  have hr3 : theta N * (theta N * bSeq N k) = bSeq N k * theta N ^ 2 := by ring
  linarith [hstep2, hstep3, hr1.le, hr1.ge, hr2.le, hr2.ge, hr3.le, hr3.ge]

/-- **Kim's §4.8 (39) variance condition** at his tilt `ρ = n^{−1/4−1/17}`. -/
lemma KimLarge.var39 {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    kimRho7 N ^ 2 / 2 * (edgeProb N * (1 - edgeProb N)
        * ((2 * kimThr7 N k) * (2 * (kimM N k : ℝ)
            * (bSeq N k * (((tParam N).choose 2 : ℕ) : ℝ)))
            * Real.exp (kimRho7 N * (2 * kimThr7 N k))))
      ≤ kimRho7 N * kimLam N k / 2 := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hρ0 : (0 : ℝ) ≤ kimRho7 N := kimRho7_nonneg N
  have hp0 : (0 : ℝ) ≤ edgeProb N := by
    rw [edgeProb]
    exact le_of_lt (div_pos h.theta_pos' (Real.sqrt_pos.mpr hNR))
  have hp1 : edgeProb N ≤ 1 := by linarith [h.edgeProb_le_half]
  have hthr0 : (0 : ℝ) ≤ kimThr7 N k := by
    rw [kimThr7]
    have := kimBeta_nonneg N k
    have := Real.sqrt_nonneg ((tParam N : ℕ) : ℝ)
    positivity
  have hsmall := h.rho7_thr7_small hk
  have hexp : Real.exp (kimRho7 N * (2 * kimThr7 N k)) ≤ 3 := by
    have h1 : kimRho7 N * (2 * kimThr7 N k) ≤ 1 := by
      nlinarith [hsmall, mul_nonneg hρ0 hthr0]
    have h2 : Real.exp (kimRho7 N * (2 * kimThr7 N k)) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr h1
    have h3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  rw [kimLam]
  exact var39_core hρ0 hp0 hp1 hthr0 (Nat.cast_nonneg _) (bSeq_pos N k).le
    (Nat.cast_nonneg _) (Real.exp_pos _).le hexp (h.key39 hk)


/-- `h = ⌈thr⌉ ≤ 2·thr`. -/
lemma KimLarge.hpar_le {N k : ℕ} (h : KimLarge N) :
    ((kimHpar N k : ℕ) : ℝ) ≤ 2 * kimThr7 N k := by
  have hthr1 := h.thr7_ge_one k
  have hceil := Nat.ceil_lt_add_one
    (show (0 : ℝ) ≤ 2 * kimBeta N k * Real.sqrt ((tParam N : ℕ) : ℝ) by
      have := kimBeta_nonneg N k
      have := Real.sqrt_nonneg ((tParam N : ℕ) : ℝ)
      positivity)
  rw [kimHpar]
  rw [kimThr7] at hthr1 ⊢
  linarith [hceil]

/-- `thr² ≤ 256·n^δ·√n·(log n)⁶`. -/
lemma KimLarge.thr7_sq_le {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    kimThr7 N k ^ 2
      ≤ 256 * Real.exp (kimDelta * Real.log N) * Real.sqrt N
        * (Real.log N) ^ 6 := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hβ := h.beta_le hk
  have hβ0 := kimBeta_nonneg N k
  have hst := h.sqrt_tParam_le
  have hst0 : (0 : ℝ) ≤ Real.sqrt ((tParam N : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hthr : kimThr7 N k
      ≤ 16 * Real.exp (kimDelta * Real.log N / 2)
        * Real.exp (Real.log N / 4) * (Real.log N) ^ 3 := by
    rw [kimThr7]
    have hA : 2 * kimBeta N k
        ≤ 2 * (2 * Real.exp (kimDelta * Real.log N / 2)
          * (Real.log N) ^ 2) := by linarith
    have hB0 : (0 : ℝ) ≤ 2 * (2 * Real.exp (kimDelta * Real.log N / 2)
        * (Real.log N) ^ 2) := by positivity
    calc 2 * kimBeta N k * Real.sqrt ((tParam N : ℕ) : ℝ)
        ≤ 2 * (2 * Real.exp (kimDelta * Real.log N / 2) * (Real.log N) ^ 2)
            * Real.sqrt ((tParam N : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hA hst0
      _ ≤ 2 * (2 * Real.exp (kimDelta * Real.log N / 2) * (Real.log N) ^ 2)
            * (4 * Real.exp (Real.log N / 4) * Real.log N) :=
          mul_le_mul_of_nonneg_left hst hB0
      _ = 16 * Real.exp (kimDelta * Real.log N / 2)
            * Real.exp (Real.log N / 4) * (Real.log N) ^ 3 := by ring
  have hthr0 : (0 : ℝ) ≤ kimThr7 N k := by
    rw [kimThr7]
    exact mul_nonneg (by linarith [kimBeta_nonneg N k]) (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ hthr0 hthr 2
  have heq : (16 * Real.exp (kimDelta * Real.log N / 2)
        * Real.exp (Real.log N / 4) * (Real.log N) ^ 3) ^ 2
      = 256 * Real.exp (kimDelta * Real.log N) * Real.sqrt N
        * (Real.log N) ^ 6 := by
    have h1 : Real.exp (kimDelta * Real.log N / 2) ^ 2
        = Real.exp (kimDelta * Real.log N) := by rw [exp_sq]; congr 1; ring
    have h2 : Real.exp (Real.log N / 4) ^ 2 = Real.sqrt N := by
      rw [exp_sq, sqrtN_eq_exp hn]; congr 1; ring
    rw [mul_pow, mul_pow, mul_pow, h1, h2]
    ring
  linarith [hsq, heq.le, heq.ge]

/-- **`768·ρ₇·p·h² ≤ bθ²`**, the scalar behind Kim's (46). -/
lemma KimLarge.key46 {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    768 * kimRho7 N * edgeProb N * ((kimHpar N k : ℕ) : ℝ) ^ 2
      ≤ bSeq N k * theta N ^ 2 := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hsN0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Real.log N) := Real.sqrt_nonneg _
  have hθ0 := h.theta_pos'
  have hρ0 : (0 : ℝ) < kimRho7 N := Real.rpow_pos_of_pos hNR _
  have hp0 : (0 : ℝ) < edgeProb N := by
    rw [edgeProb]; exact div_pos hθ0 hsN0
  have hthr0 : (0 : ℝ) ≤ kimThr7 N k := by
    rw [kimThr7]
    exact mul_nonneg (by linarith [kimBeta_nonneg N k]) (Real.sqrt_nonneg _)
  have hh0 : (0 : ℝ) ≤ ((kimHpar N k : ℕ) : ℝ) := Nat.cast_nonneg _
  -- `h² ≤ 4·thr²`
  have hhsq : ((kimHpar N k : ℕ) : ℝ) ^ 2 ≤ 4 * kimThr7 N k ^ 2 := by
    have := h.hpar_le (k := k)
    nlinarith [this, hh0, hthr0]
  have hthr2 := h.thr7_sq_le hk
  -- chain to `786432·ρ·θ·e^{δL}·L⁶`
  have hpre : (0 : ℝ) ≤ 768 * kimRho7 N * edgeProb N := by positivity
  have hstep1 : 768 * kimRho7 N * edgeProb N * ((kimHpar N k : ℕ) : ℝ) ^ 2
      ≤ 768 * kimRho7 N * edgeProb N
        * (4 * (256 * Real.exp (kimDelta * Real.log N) * Real.sqrt N
            * (Real.log N) ^ 6)) := by
    refine mul_le_mul_of_nonneg_left ?_ hpre
    have h4 : (0 : ℝ) ≤ (4 : ℝ) := by norm_num
    linarith [hhsq, mul_le_mul_of_nonneg_left hthr2 h4]
  have hval : 768 * kimRho7 N * edgeProb N
        * (4 * (256 * Real.exp (kimDelta * Real.log N) * Real.sqrt N
            * (Real.log N) ^ 6))
      = 786432 * kimRho7 N * Real.exp (kimDelta * Real.log N)
        * (Real.log N) ^ 4 := by
    rw [edgeProb, theta]
    field_simp
    ring
  -- `786432·ρ·e^{δL}·L⁴ ≤ b/L⁴`
  have hb := h.bSeq_ge' hk
  have hcl := h.asym.p7_46var
  have hmono : Real.exp (((1 : ℝ) / 4 + 1 / 17 - 2 * kimDelta) * Real.log N
        - 4 * Real.sqrt (Real.log N) - 2)
      ≤ Real.exp (((1 : ℝ) / 4 + 1 / 17 - 2 * kimDelta) * Real.log N
          - 2 * Real.sqrt (Real.log N) - 1) :=
    Real.exp_le_exp.mpr (by linarith [hs0])
  have hL8 : 786432 * (Real.log N) ^ 8
      ≤ Real.exp (((1 : ℝ) / 4 + 1 / 17 - 2 * kimDelta) * Real.log N
          - 2 * Real.sqrt (Real.log N) - 1) := by
    have hp8 : (0 : ℝ) ≤ (Real.log N) ^ 8 := by positivity
    linarith [hcl, hmono, hp8]
  have hρe : kimRho7 N
      = Real.exp (-(((1 : ℝ) / 4 + 1 / 17) * Real.log N)) := by
    rw [kimRho7, Real.rpow_def_of_pos hNR]; congr 1; ring
  have hprod : Real.exp (-(((1 : ℝ) / 4 + 1 / 17) * Real.log N))
      * Real.exp (kimDelta * Real.log N)
      * Real.exp (((1 : ℝ) / 4 + 1 / 17 - 2 * kimDelta) * Real.log N
          - 2 * Real.sqrt (Real.log N) - 1)
      = Real.exp (-(kimDelta * Real.log N)
          - 2 * Real.sqrt (Real.log N) - 1) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hL4pos : (0 : ℝ) < (Real.log N) ^ 4 := by positivity
  have hgoal : 786432 * kimRho7 N * Real.exp (kimDelta * Real.log N)
        * (Real.log N) ^ 4 ≤ bSeq N k * theta N ^ 2 := by
    have hθ : theta N ^ 2 = 1 / (Real.log N) ^ 4 := by rw [theta]; field_simp
    rw [hθ, mul_one_div, le_div_iff₀ hL4pos]
    have hR0 : (0 : ℝ) < kimRho7 N * Real.exp (kimDelta * Real.log N) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hL8 hR0.le
    have hlhs : 786432 * kimRho7 N * Real.exp (kimDelta * Real.log N)
          * (Real.log N) ^ 4 * (Real.log N) ^ 4
        = kimRho7 N * Real.exp (kimDelta * Real.log N)
          * (786432 * (Real.log N) ^ 8) := by ring
    rw [hlhs]
    have hcol : kimRho7 N * Real.exp (kimDelta * Real.log N)
          * Real.exp (((1 : ℝ) / 4 + 1 / 17 - 2 * kimDelta) * Real.log N
            - 2 * Real.sqrt (Real.log N) - 1)
        = Real.exp (-(kimDelta * Real.log N)
            - 2 * Real.sqrt (Real.log N) - 1) := by
      rw [hρe]; exact hprod
    linarith [hmul, hcol.le, hcol.ge, hb]
  linarith [hstep1, hval.le, hval.ge, hgoal]

/-- The scalar shape of the (46) variance comparison. -/
lemma var46_core {ρ p b T θ hh E : ℝ}
    (hρ0 : 0 ≤ ρ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hb0 : 0 ≤ b) (hT0 : 0 ≤ T)
    (hh0 : 0 ≤ hh) (hE0 : 0 ≤ E) (hE : E ≤ 3)
    (hkey : 768 * ρ * p * hh ^ 2 ≤ b * θ ^ 2) :
    ρ ^ 2 / 2 * (p * (1 - p) * ((b * T) * ((4 * hh) ^ 2 * E)))
      ≤ ρ * (b ^ 2 * θ ^ 2 * T / 16) / 2 := by
  have hbT0 : (0 : ℝ) ≤ b * T := mul_nonneg hb0 hT0
  have hQ0 : (0 : ℝ) ≤ (b * T) * (4 * hh) ^ 2 := by positivity
  have h1 : (b * T) * ((4 * hh) ^ 2 * E) ≤ (b * T) * ((4 * hh) ^ 2 * 3) := by
    nlinarith [hE, hQ0, hE0]
  have h1c : (0 : ℝ) ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  have h2 : p * (1 - p) ≤ p := by nlinarith [hp0, hp1]
  have hX : p * (1 - p) * ((b * T) * ((4 * hh) ^ 2 * E))
      ≤ 48 * (p * hh ^ 2 * b * T) :=
    calc p * (1 - p) * ((b * T) * ((4 * hh) ^ 2 * E))
        ≤ p * (1 - p) * ((b * T) * ((4 * hh) ^ 2 * 3)) :=
          mul_le_mul_of_nonneg_left h1 h1c
      _ ≤ p * ((b * T) * ((4 * hh) ^ 2 * 3)) :=
          mul_le_mul_of_nonneg_right h2 (by nlinarith [hQ0])
      _ = 48 * (p * hh ^ 2 * b * T) := by ring
  have hA : ρ ^ 2 / 2 * (p * (1 - p) * ((b * T) * ((4 * hh) ^ 2 * E)))
      ≤ ρ ^ 2 / 2 * (48 * (p * hh ^ 2 * b * T)) :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  have hbT32 : (0 : ℝ) ≤ b * T / 32 := by positivity
  have hC : 768 * ρ * p * hh ^ 2 * (b * T / 32)
      ≤ b * θ ^ 2 * (b * T / 32) := mul_le_mul_of_nonneg_right hkey hbT32
  have hD : ρ * (768 * ρ * p * hh ^ 2 * (b * T / 32))
      ≤ ρ * (b * θ ^ 2 * (b * T / 32)) := mul_le_mul_of_nonneg_left hC hρ0
  have hB : ρ ^ 2 / 2 * (48 * (p * hh ^ 2 * b * T))
      = ρ * (768 * ρ * p * hh ^ 2 * (b * T / 32)) := by ring
  have hF : ρ * (b * θ ^ 2 * (b * T / 32))
      = ρ * (b ^ 2 * θ ^ 2 * T / 16) / 2 := by ring
  linarith [hA, hB.le, hB.ge, hD, hF.le, hF.ge]

/-- **Kim's §4.8 (46) variance condition** at his tilt `ρ = n^{−1/4−1/17}`. -/
lemma KimLarge.var46 {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    kimRho7 N ^ 2 / 2 * (edgeProb N * (1 - edgeProb N)
        * ((bSeq N k * (((tParam N).choose 2 : ℕ) : ℝ))
          * ((4 * ((kimHpar N k : ℕ) : ℝ)) ^ 2
            * Real.exp (kimRho7 N * (4 * ((kimHpar N k : ℕ) : ℝ))))))
      ≤ kimRho7 N * kimLam N k / 2 := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hρ0 : (0 : ℝ) ≤ kimRho7 N := kimRho7_nonneg N
  have hp0 : (0 : ℝ) ≤ edgeProb N := by
    rw [edgeProb]
    exact le_of_lt (div_pos h.theta_pos' (Real.sqrt_pos.mpr hNR))
  have hp1 : edgeProb N ≤ 1 := by linarith [h.edgeProb_le_half]
  have hh0 : (0 : ℝ) ≤ ((kimHpar N k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hthr0 : (0 : ℝ) ≤ kimThr7 N k := by
    rw [kimThr7]
    exact mul_nonneg (by linarith [kimBeta_nonneg N k]) (Real.sqrt_nonneg _)
  have hsmall := h.rho7_thr7_small hk
  have hhle := h.hpar_le (k := k)
  have hexp : Real.exp (kimRho7 N * (4 * ((kimHpar N k : ℕ) : ℝ))) ≤ 3 := by
    have h1 : kimRho7 N * (4 * ((kimHpar N k : ℕ) : ℝ)) ≤ 1 := by
      nlinarith [hsmall, hhle, hρ0, hthr0, hh0]
    have h2 : Real.exp (kimRho7 N * (4 * ((kimHpar N k : ℕ) : ℝ)))
        ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
    have h3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  rw [kimLam]
  exact var46_core hρ0 hp0 hp1 (bSeq_pos N k).le (Nat.cast_nonneg _) hh0
    (Real.exp_pos _).le hexp (h.key46 hk)


/-- `((1−p) + p·e)^t ≤ 3`: Kim's (49) moment factor is `1 + O(1/log n)`. -/
lemma KimLarge.momentFactor_le {N : ℕ} (h : KimLarge N) :
    ((1 - edgeProb N) + edgeProb N * Real.exp 1) ^ (tParam N) ≤ 3 := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hsN0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Real.log N) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (Real.log N) ^ 2 = Real.log N := Real.sq_sqrt hL0.le
  have hsL : Real.sqrt (Real.log N) ≤ Real.log N := by nlinarith [hsq, hs0, hLv]
  have hθ0 := h.theta_pos'
  have hp0 : (0 : ℝ) < edgeProb N := by rw [edgeProb]; exact div_pos hθ0 hsN0
  have hp1 := h.edgeProb_le_half
  have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (0 : ℝ); simpa using this
  have hK0 : (0 : ℝ) ≤ (1 - edgeProb N) + edgeProb N * Real.exp 1 := by
    nlinarith [hp0.le, hp1, he1]
  have hKe : (1 - edgeProb N) + edgeProb N * Real.exp 1
      ≤ Real.exp (edgeProb N * (Real.exp 1 - 1)) := by
    have := Real.add_one_le_exp (edgeProb N * (Real.exp 1 - 1))
    linarith
  have hpow := pow_le_pow_left₀ hK0 hKe (tParam N)
  have hexp : (Real.exp (edgeProb N * (Real.exp 1 - 1))) ^ (tParam N)
      = Real.exp (((tParam N : ℕ) : ℝ) * (edgeProb N * (Real.exp 1 - 1))) := by
    rw [Real.exp_nat_mul]
  -- `t·p·(e−1) ≤ 1`
  have htp : ((tParam N : ℕ) : ℝ) * edgeProb N
      ≤ 10 * theta N * Real.sqrt (Real.log N) := by
    have ht := h.tParam_le'
    have hstep : ((tParam N : ℕ) : ℝ) * edgeProb N
        ≤ (10 * Real.sqrt N * Real.sqrt (Real.log N)) * edgeProb N :=
      mul_le_mul_of_nonneg_right ht hp0.le
    have heq : (10 * Real.sqrt N * Real.sqrt (Real.log N)) * edgeProb N
        = 10 * theta N * Real.sqrt (Real.log N) := by
      rw [edgeProb]; field_simp; try ring
    linarith [hstep, heq.le, heq.ge]
  have hsmall : ((tParam N : ℕ) : ℝ) * (edgeProb N * (Real.exp 1 - 1)) ≤ 1 := by
    have hθv : theta N * Real.sqrt (Real.log N) ≤ 1 / Real.log N := by
      rw [theta]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hL0]
      nlinarith [hsL, hL0]
    have hL1 : (1 : ℝ) / Real.log N ≤ 1 / 1000000 := by
      rw [div_le_div_iff₀ hL0 (by norm_num)]
      linarith
    have hlow : ((tParam N : ℕ) : ℝ) * edgeProb N ≤ 10 / 1000000 := by
      nlinarith [htp, hθv, hL1]
    have hfac : Real.exp 1 - 1 ≤ 2 := by linarith
    have ht0 : (0 : ℝ) ≤ ((tParam N : ℕ) : ℝ) * edgeProb N := by positivity
    nlinarith [hlow, hfac, ht0, hp0.le]
  have hle3 : Real.exp (((tParam N : ℕ) : ℝ) * (edgeProb N * (Real.exp 1 - 1)))
      ≤ 3 := by
    have h1 := Real.exp_le_exp.mpr hsmall
    linarith [h1, he]
  linarith [hpow, hexp.le, hexp.ge, hle3]

/-- **`98304·ρ₇·n ≤ b²θ²C(t,2)`**, the scalar behind Kim's (49). -/
lemma KimLarge.key49 {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    98304 * kimRho7 N * (N : ℝ)
      ≤ bSeq N k ^ 2 * theta N ^ 2 * (((tParam N).choose 2 : ℕ) : ℝ) := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log N := by linarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Real.log N) := Real.sqrt_nonneg _
  have hρ0 : (0 : ℝ) < kimRho7 N := Real.rpow_pos_of_pos hNR _
  have hbsq := h.bSq_ge hk
  have hT := h.T2_ge
  have hcl := h.asym.p7_46var
  have hθ : theta N ^ 2 = 1 / (Real.log N) ^ 4 := by rw [theta]; field_simp
  have hL3 : (0 : ℝ) < (Real.log N) ^ 3 := by positivity
  have hL4 : (0 : ℝ) < (Real.log N) ^ 4 := by positivity
  set E2 := Real.exp (-(2 * kimDelta * Real.log N)
      - 4 * Real.sqrt (Real.log N) - 2) with hE2
  have hE20 : (0 : ℝ) < E2 := Real.exp_pos _
  -- `98304ρ₇L³ ≤ 27E₂`
  have hid : kimRho7 N
      * Real.exp (((1 : ℝ) / 4 + 1 / 17 - 2 * kimDelta) * Real.log N
        - 4 * Real.sqrt (Real.log N) - 2) = E2 := by
    have hρe : kimRho7 N
        = Real.exp (-(((1 : ℝ) / 4 + 1 / 17) * Real.log N)) := by
      rw [kimRho7, Real.rpow_def_of_pos hNR]; congr 1; ring
    rw [hρe, ← Real.exp_add, hE2]; congr 1; ring
  have hpp : 98304 * (Real.log N) ^ 3
      ≤ 27 * (1000000 * (Real.log N) ^ 8) := by
    have hpw : (Real.log N) ^ 3 ≤ (Real.log N) ^ 8 :=
      pow_le_pow_right₀ hL1 (by norm_num)
    nlinarith [hpw, hL3]
  have hmain : 98304 * kimRho7 N * (Real.log N) ^ 3 ≤ 27 * E2 := by
    have h1 : 98304 * (Real.log N) ^ 3
        ≤ 27 * Real.exp (((1 : ℝ) / 4 + 1 / 17 - 2 * kimDelta) * Real.log N
            - 4 * Real.sqrt (Real.log N) - 2) := by linarith [hcl, hpp]
    have hmul := mul_le_mul_of_nonneg_left h1 hρ0.le
    have hlhs : kimRho7 N * (98304 * (Real.log N) ^ 3)
        = 98304 * kimRho7 N * (Real.log N) ^ 3 := by ring
    have hrhs : kimRho7 N
          * (27 * Real.exp (((1 : ℝ) / 4 + 1 / 17 - 2 * kimDelta) * Real.log N
              - 4 * Real.sqrt (Real.log N) - 2)) = 27 * E2 := by
      rw [← hid]; ring
    linarith [hmul, hlhs.le, hlhs.ge, hrhs.le, hrhs.ge]
  -- `b²θ²C(t,2) ≥ 27·n·E₂/L³`
  have hlow : 27 * (N : ℝ) * E2 / (Real.log N) ^ 3
      ≤ bSeq N k ^ 2 * theta N ^ 2 * (((tParam N).choose 2 : ℕ) : ℝ) := by
    rw [hθ]
    have hA : E2 * (1 / (Real.log N) ^ 4) * (27 * ((N : ℝ) * Real.log N))
        ≤ bSeq N k ^ 2 * (1 / (Real.log N) ^ 4)
          * (((tParam N).choose 2 : ℕ) : ℝ) := by
      have h1 : E2 * (1 / (Real.log N) ^ 4)
          ≤ bSeq N k ^ 2 * (1 / (Real.log N) ^ 4) :=
        mul_le_mul_of_nonneg_right hbsq (by positivity)
      have h2 : (0 : ℝ) ≤ 27 * ((N : ℝ) * Real.log N) := by positivity
      have h3 : (0 : ℝ) ≤ bSeq N k ^ 2 * (1 / (Real.log N) ^ 4) := by
        positivity
      calc E2 * (1 / (Real.log N) ^ 4) * (27 * ((N : ℝ) * Real.log N))
          ≤ bSeq N k ^ 2 * (1 / (Real.log N) ^ 4)
              * (27 * ((N : ℝ) * Real.log N)) :=
            mul_le_mul_of_nonneg_right h1 h2
        _ ≤ bSeq N k ^ 2 * (1 / (Real.log N) ^ 4)
              * (((tParam N).choose 2 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hT h3
      done
    have heq : E2 * (1 / (Real.log N) ^ 4) * (27 * ((N : ℝ) * Real.log N))
        = 27 * (N : ℝ) * E2 / (Real.log N) ^ 3 := by
      field_simp; try ring
    linarith [hA, heq.le, heq.ge]
  -- combine
  have hcoef : (0 : ℝ) ≤ (N : ℝ) / (Real.log N) ^ 3 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hmain hcoef
  have hl : 98304 * kimRho7 N * (Real.log N) ^ 3 * ((N : ℝ) / (Real.log N) ^ 3)
      = 98304 * kimRho7 N * (N : ℝ) := by
    field_simp
  have hr : 27 * E2 * ((N : ℝ) / (Real.log N) ^ 3)
      = 27 * (N : ℝ) * E2 / (Real.log N) ^ 3 := by ring
  linarith [hmul, hl.le, hl.ge, hr.le, hr.ge, hlow]

/-- **Kim's §4.9 (49) tail condition** at his tilt `ρ = n^{−1/4−1/17}`. -/
lemma KimLarge.var49 {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    1024 * kimRho7 N ^ 2
        * ((1 - edgeProb N) + edgeProb N * Real.exp 1) ^ (tParam N) * (N : ℝ)
      ≤ kimRho7 N * kimLam N k / 2 := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hρ0 : (0 : ℝ) < kimRho7 N := Real.rpow_pos_of_pos hNR _
  have hK := h.momentFactor_le
  have hK0 : (0 : ℝ) ≤ ((1 - edgeProb N) + edgeProb N * Real.exp 1) ^ (tParam N) := by
    refine pow_nonneg ?_ _
    have hp1 := h.edgeProb_le_half
    have hp0 : (0 : ℝ) ≤ edgeProb N := by
      rw [edgeProb]
      exact le_of_lt (div_pos h.theta_pos' (Real.sqrt_pos.mpr hNR))
    have he1 : (1 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (0 : ℝ); simpa using this
    nlinarith [hp0, hp1, he1]
  have hkey := h.key49 hk
  have hstep : 1024 * kimRho7 N ^ 2
        * ((1 - edgeProb N) + edgeProb N * Real.exp 1) ^ (tParam N) * (N : ℝ)
      ≤ 1024 * kimRho7 N ^ 2 * 3 * (N : ℝ) := by
    have hc : (0 : ℝ) ≤ 1024 * kimRho7 N ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hK hc
    exact mul_le_mul_of_nonneg_right h1 (le_of_lt hNR)
  have hfin : 1024 * kimRho7 N ^ 2 * 3 * (N : ℝ)
      ≤ kimRho7 N * kimLam N k / 2 := by
    rw [kimLam]
    have hmul := mul_le_mul_of_nonneg_left hkey hρ0.le
    have hl : kimRho7 N * (98304 * kimRho7 N * (N : ℝ))
        = 1024 * kimRho7 N ^ 2 * 3 * (N : ℝ) * 32 := by ring
    have hr : kimRho7 N
          * (bSeq N k ^ 2 * theta N ^ 2 * (((tParam N).choose 2 : ℕ) : ℝ))
        = kimRho7 N * (bSeq N k ^ 2 * theta N ^ 2
            * (((tParam N).choose 2 : ℕ) : ℝ) / 16) / 2 * 32 := by ring
    linarith [hmul, hl.le, hl.ge, hr.le, hr.ge]
  linarith [hstep, hfin]

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **Property 7's failure probability**, with Kim's global events (40)/(54)
charged once instead of `C(n,t)` times. -/
lemma bad7_bound' (k : ℕ) (s : BlockState V) (hN : KimLarge n)
    (hk : k ≤ ⌊(n : ℝ) ^ ((1 : ℝ) / 17 - 10 ^ (-5 : ℤ)) / theta n⌋₊)
    (h1 : Property1 s k) (h2 : Property2 s k) (h3 : Property3 s k)
    (h4 : Property4 s k) (h5 : Property5 s k) (h6 : Property6 s k)
    (h7 : Property7 s k)
    {β γ : ℝ} (hβ1 : 1 ≤ β) (hγ1 : 1 ≤ γ)
    (hβT : β ≤ Real.sqrt ((tParam n : ℕ) : ℝ) / 2) (hTpos : 0 < tParam n)
    (thr : ℝ) (hthrdef : thr = 2 * β * Real.sqrt ((tParam n : ℕ) : ℝ))
    (hthr1 : 1 ≤ thr)
    (hβγT : 2 * β * γ * Real.sqrt ((tParam n : ℕ) : ℝ) ≤ (mcut n : ℝ))
    (hβ3 : 3 * ((k : ℝ) + 1) * Real.log n ≤ β ^ 2)
    {Dx : ℝ} (hDxdef : Dx = bSeq n k * theta n * Real.sqrt n
      + (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log n)
    {c2 : ℝ}
    (hc2def : c2 = (mcut n : ℝ)
        * (((tParam n : ℕ) : ℝ) + ((tParam n : ℕ) : ℝ) / 2)
        + bSeq n k * Dx
          * (((tParam n : ℕ) : ℝ) + ((tParam n : ℕ) : ℝ) / (2 * γ ^ 2)))
    (hh : ℕ) {c5 c6 c7 q5 q6 : ℝ} {t5 lam5 : ℝ} (ht5 : 0 ≤ t5)
    (hc5 : edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ))
        * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)) + lam5 ≤ c5)
    (hq5exp : Real.exp (-t5 * lam5 + t5 ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
        * ((bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ))
            * ((4 * (hh : ℝ)) ^ 2 * Real.exp (t5 * (4 * (hh : ℝ))))))) ≤ q5)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρh : ρ * (hh : ℝ) ≤ 1)
    (hq6le : Real.exp (-(ρ * c6)
        + (ρ * (edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ))
              * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)))
          + 1024 * ρ ^ 2
            * ((1 - edgeProb n) + edgeProb n * Real.exp 1) ^ (tParam n)
            * (n : ℝ))) ≤ q6)
    (hhge : 2 * β * Real.sqrt ((tParam n : ℕ) : ℝ) ≤ (hh : ℝ))
    (hc7 : (2 * (mcut n : ℝ)) / 2 * (((tParam n : ℕ) : ℝ)
          + ((tParam n : ℕ) : ℝ) / 2)
        + (bSeq n k * Dx / 2) * (((tParam n : ℕ) : ℝ)
          + ((tParam n : ℕ) : ℝ) / (2 * γ ^ 2)) ≤ c7)
    {c4 : ℝ} (hc4def : c4 = c5 + c6 + c7)
    {c1 c3 : ℝ}
    (hsplit : c1 - c2 - c3 - c4
      = bSeq n (k + 1) * μSeq n (k + 1) * ((tParam n).choose 2))
    {L lam1 : ℝ} (hL0 : 0 ≤ L)
    (hL : L ≤ (1 - edgeProb n) ^ (2 * kimM n k))
    (hc1 : c1 + lam1 ≤ L * (bSeq n k * μSeq n k * ((tParam n).choose 2)))
    {t1 : ℝ} (ht1 : 0 ≤ t1) {q1 : ℝ}
    (hq1 : Real.exp (-t1 * lam1 + t1 ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
        * ((2 * thr) * (2 * (kimM n k : ℝ)
            * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)))
            * Real.exp (t1 * (2 * thr))))) ≤ q1)
    {t3 lam3 : ℝ} (ht3 : 0 ≤ t3)
    (hvar3 : t3 ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
        * ((bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)) * Real.exp t3))
      ≤ t3 * lam3 / 2)
    (hc3 : edgeProb n * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ))
      + lam3 ≤ c3)
    {q3 : ℝ} (hq3 : 2 * Real.exp (-(t3 * lam3) / 2) ≤ q3)
    (hq : 0 ≤ q1 + q3 + (q5 + q6)) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property7 (blockStepP s (kimM n k) σ) (k + 1)))
      ≤ (3 / n + (n : ℝ) * ((n : ℝ) ^ (3 : ℕ))⁻¹)
        + ((n : ℕ).choose (tParam n) : ℝ) * (q1 + q3 + (q5 + q6)) := by
  have hn : 0 < n := hN.card_pos
  have hlogn : 1 ≤ Real.log n := hN.logn_ge_one
  subst hDxdef
  have hGG : ∀ T' ∈ calT s, ((gammaBetween s.Γ T' T').card : ℝ)
      ≤ bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ) := fun T' hT' =>
    h6.gammaT_le hN.mcut_pos hN.two_mcut_le_t hT'
  refine property7_numeric' k s hn hlogn h4 h7 thr hthr1 hsplit
    (goodSample s (kimM n k) k _)
    (bernoulliPr_goodSample_compl k s hN hk h1 h2 h3) hGG hL0 hL hc1 ht1 hq1
    ht3 hvar3 hc3 hq3 ?_ ?_ hq
  · intro T hT
    rw [hc2def]
    exact bad7_hb2' k s hN h6 hβ1 hγ1 hβT hTpos thr hthrdef hβγT hβ3 rfl T hT
  · intro T hT
    rw [hc4def]
    have hβγ2 : 2 * β * γ * Real.sqrt ((tParam n : ℕ) : ℝ)
        ≤ 2 * (mcut n : ℝ) := by
      have : (0 : ℝ) ≤ (mcut n : ℝ) := Nat.cast_nonneg _
      linarith [hβγT]
    refine bad7_hb4' k s hN h5 h6 hh hGG ht5 hc5 hq5exp ?_ hβ1 hγ1 hβT hTpos
      hhge hβγ2 hβ3 rfl hc7 T hT
    intro T' hT'
    exact le_trans (bad7_hq6' k s hN h5 hh hρ hρh c6 _ hGG T' hT') hq6le



/-- Kim's per-step exponent `bᵢμᵢθ(t choose 2)/√n` of (55). -/
noncomputable def kimS (N k : ℕ) : ℝ :=
  bSeq N k * μSeq N k * theta N / Real.sqrt N * (((tParam N).choose 2 : ℕ) : ℝ)

/-- A `k`-free lower bound for `kimS`. -/
noncomputable def kimSlow (N : ℕ) : ℝ :=
  13 * Real.exp (-(kimDelta * Real.log N) - 2 * Real.sqrt (Real.log N) - 1)
    * Real.sqrt N / Real.log N

lemma kimS_nonneg {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) : 0 ≤ kimS N k := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hmu := (h.mu_bounds hk).1
  rw [kimS]
  have hb0 := (bSeq_pos N k).le
  have hθ0 := theta_nonneg N
  have hs0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
  have hT0 : (0 : ℝ) ≤ (((tParam N).choose 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hμ0 : (0 : ℝ) ≤ μSeq N k := by linarith
  positivity

/-- `1/ε² = √(log log n)`. -/
lemma KimLarge.eps_sq_inv {N : ℕ} (h : KimLarge N) :
    1 / kimEps N ^ 2 = Real.sqrt (Real.log (Real.log N)) := by
  have hn := h.card_pos
  have hLv := h.logn_vast
  have hL1 : (1 : ℝ) < Real.log N := by linarith
  have hw0 : (0 : ℝ) < Real.log (Real.log N) := Real.log_pos hL1
  have hsq : kimEps N ^ 2 = (Real.log (Real.log N)) ^ (-((1 : ℝ) / 2)) := by
    rw [kimEps, ← Real.rpow_natCast ((Real.log (Real.log N))
        ^ (-(1 : ℝ) / 4)) 2, ← Real.rpow_mul hw0.le]
    norm_num
  rw [hsq, Real.rpow_neg hw0.le, one_div, inv_inv, Real.sqrt_eq_rpow]

/-- `0 < ε ≤ 1`. -/
lemma KimLarge.eps_pos {N : ℕ} (h : KimLarge N) : 0 < kimEps N := by
  have hn := h.card_pos
  have hLv := h.logn_vast
  have hL1 : (1 : ℝ) < Real.log N := by linarith
  have hw0 : (0 : ℝ) < Real.log (Real.log N) := Real.log_pos hL1
  rw [kimEps]
  exact Real.rpow_pos_of_pos hw0 _

lemma KimLarge.eps_le_one {N : ℕ} (h : KimLarge N) : kimEps N ≤ 1 := by
  have hLv := h.logn_vast
  have hL1 : (1 : ℝ) < Real.log N := by linarith
  have hw0 : (0 : ℝ) < Real.log (Real.log N) := Real.log_pos hL1
  have hwbig : (1 : ℝ) ≤ Real.log (Real.log N) := by
    have h13 : Real.exp 1 ≤ Real.log N := by
      have := Real.exp_one_lt_d9; linarith
    have hmono := Real.log_le_log (Real.exp_pos 1) h13
    rw [Real.log_exp] at hmono
    linarith
  rw [kimEps, show -(1 : ℝ) / 4 = -((1 : ℝ) / 4) by ring,
    Real.rpow_neg hw0.le]
  have hge : (1 : ℝ) ≤ (Real.log (Real.log N)) ^ ((1 : ℝ) / 4) :=
    Real.one_le_rpow hwbig (by norm_num)
  rw [inv_le_one_iff₀]
  right
  exact hge

/-- `1/ε² ≤ √log n`. -/
lemma KimLarge.eps_sq_inv_le {N : ℕ} (h : KimLarge N) :
    1 / kimEps N ^ 2 ≤ Real.sqrt (Real.log N) := by
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  rw [h.eps_sq_inv]
  refine Real.sqrt_le_sqrt ?_
  have := Real.log_le_sub_one_of_pos hL0
  linarith

/-- `exp(1/ε²) ≤ 2√log n`. -/
lemma KimLarge.exp_eps_sq_inv_le {N : ℕ} (h : KimLarge N) :
    Real.exp (1 / kimEps N ^ 2) ≤ 2 * Real.sqrt (Real.log N) := by
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hL1 : (1 : ℝ) < Real.log N := by linarith
  have hw0 : (0 : ℝ) < Real.log (Real.log N) := Real.log_pos hL1
  have hsw : Real.sqrt (Real.log (Real.log N)) ^ 2 = Real.log (Real.log N) :=
    Real.sq_sqrt hw0.le
  have hsw0 : (0 : ℝ) ≤ Real.sqrt (Real.log (Real.log N)) := Real.sqrt_nonneg _
  -- `√w ≤ (w+1)/2`
  have hhalf : Real.sqrt (Real.log (Real.log N))
      ≤ (Real.log (Real.log N) + 1) / 2 := by
    nlinarith [hsw, hsw0, sq_nonneg (Real.sqrt (Real.log (Real.log N)) - 1)]
  rw [h.eps_sq_inv]
  have hstep : Real.exp (Real.sqrt (Real.log (Real.log N)))
      ≤ Real.exp ((Real.log (Real.log N) + 1) / 2) := Real.exp_le_exp.mpr hhalf
  have hsplit : Real.exp ((Real.log (Real.log N) + 1) / 2)
      = Real.sqrt (Real.log N) * Real.exp (1 / 2) := by
    rw [show (Real.log (Real.log N) + 1) / 2
        = Real.log (Real.log N) / 2 + 1 / 2 by ring, Real.exp_add]
    congr 1
    rw [show Real.log (Real.log N) / 2 = 1 / 2 * Real.log (Real.log N) by ring,
      ← Real.log_rpow hL0, Real.exp_log (Real.rpow_pos_of_pos hL0 _),
      Real.sqrt_eq_rpow]
  have he2 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have h1 : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
      rw [exp_sq]; congr 1; ring
    have h2 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    nlinarith [h1, h2, (Real.exp_pos (1 / 2 : ℝ)).le]
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Real.log N) := Real.sqrt_nonneg _
  calc Real.exp (Real.sqrt (Real.log (Real.log N)))
      ≤ Real.sqrt (Real.log N) * Real.exp (1 / 2) := by
        rw [← hsplit]; exact hstep
    _ ≤ Real.sqrt (Real.log N) * 2 := mul_le_mul_of_nonneg_left he2 hs0
    _ = 2 * Real.sqrt (Real.log N) := by ring

/-- `1/log n ≤ ε`. -/
lemma KimLarge.eps_ge {N : ℕ} (h : KimLarge N) : 1 / Real.log N ≤ kimEps N := by
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have hsq : Real.sqrt (Real.log N) ^ 2 = Real.log N := Real.sq_sqrt hL0.le
  have hsL : Real.sqrt (Real.log N) ≤ Real.log N := by nlinarith [hsq, hs0.le]
  have hε0 := h.eps_pos
  have hε1 := h.eps_le_one
  have hinv := h.eps_sq_inv_le
  -- `ε ≥ ε² = 1/(1/ε²) ≥ 1/√L ≥ 1/L`
  have hsq2 : kimEps N ^ 2 ≤ kimEps N := by nlinarith [hε0, hε1]
  have hlow : 1 / Real.sqrt (Real.log N) ≤ kimEps N ^ 2 := by
    rw [div_le_iff₀ hs0]
    have hpos : (0 : ℝ) < 1 / kimEps N ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hinv (le_of_lt (pow_pos hε0 2))
    rw [mul_one_div_cancel (ne_of_gt (pow_pos hε0 2))] at this
    linarith [this]
  have hcmp : 1 / Real.log N ≤ 1 / Real.sqrt (Real.log N) := by
    rw [div_le_div_iff₀ hL0 hs0]
    linarith [hsL]
  linarith [hcmp, hlow, hsq2]



/-- `kimSlow ≤ kimS`, a `k`-free lower bound: `b ≥ e^{−δL−2√L−1}`, `μ ≥ 1/2`,
`C(t,2) ≥ 27n log n`. -/
lemma KimLarge.kimSlow_le {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    kimSlow N ≤ kimS N k := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hs0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hb := h.bSeq_ge' hk
  have hb0 := (bSeq_pos N k).le
  have hmu := (h.mu_bounds hk).1
  have hT := h.T2_ge
  set E : ℝ := Real.exp (-(kimDelta * Real.log N)
      - 2 * Real.sqrt (Real.log N) - 1) with hEdef
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hbmu : E / 2 ≤ bSeq N k * μSeq N k := by nlinarith [hb, hmu, hE0]
  have hdiv : (N : ℝ) / Real.sqrt N = Real.sqrt N := Real.div_sqrt
  -- `θ/√N·C(t,2) ≥ 27√N/log n`
  have hsecond : 27 * Real.sqrt N / Real.log N
      ≤ theta N / Real.sqrt N * (((tParam N).choose 2 : ℕ) : ℝ) := by
    have hc : (0 : ℝ) ≤ theta N / Real.sqrt N := by rw [theta]; positivity
    have hstep : theta N / Real.sqrt N * (27 * ((N : ℝ) * Real.log N))
        ≤ theta N / Real.sqrt N * (((tParam N).choose 2 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hT hc
    have heq : theta N / Real.sqrt N * (27 * ((N : ℝ) * Real.log N))
        = 27 * ((N : ℝ) / Real.sqrt N) / Real.log N := by
      rw [theta]; field_simp; try ring
    rw [heq, hdiv] at hstep
    exact hstep
  have hfirst0 : (0 : ℝ) ≤ 27 * Real.sqrt N / Real.log N := by positivity
  have hbmu0 : (0 : ℝ) ≤ bSeq N k * μSeq N k := by nlinarith [hb0, hmu]
  have hprod : (E / 2) * (27 * Real.sqrt N / Real.log N)
      ≤ bSeq N k * μSeq N k
        * (theta N / Real.sqrt N * (((tParam N).choose 2 : ℕ) : ℝ)) :=
    mul_le_mul hbmu hsecond hfirst0 hbmu0
  have hlhs : kimSlow N ≤ (E / 2) * (27 * Real.sqrt N / Real.log N) := by
    rw [kimSlow, ← hEdef]
    have hrw : E / 2 * (27 * Real.sqrt N / Real.log N)
        = 27 / 2 * E * Real.sqrt N / Real.log N := by ring
    rw [hrw, div_le_div_iff₀ hL0 hL0]
    have hnn : (0 : ℝ) ≤ E * Real.sqrt N * Real.log N := by positivity
    nlinarith [hnn]
  have hrhs : bSeq N k * μSeq N k
        * (theta N / Real.sqrt N * (((tParam N).choose 2 : ℕ) : ℝ))
      = kimS N k := by rw [kimS]; ring
  linarith [hlhs, hprod, hrhs.le, hrhs.ge]


/-- **`9/ε² + 8 ≤ ε·kimS`**, the slack Kim's (58)/(59) need.

`1/ε² ≤ √log n` and `ε ≥ 1/log n`, so the left side is `O(log n)` while
`ε·kimS ≥ 13e^{(1/2−δ)L−2√L−1}/(log n)²`. -/
lemma KimLarge.p8_S {N k : ℕ} (h : KimLarge N)
    (hk : k ≤ ⌊(N : ℝ) ^ kimDelta / theta N⌋₊) :
    9 / kimEps N ^ 2 + 8 ≤ kimEps N * kimS N k := by
  have hn := h.card_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have hsq : Real.sqrt (Real.log N) ^ 2 = Real.log N := Real.sq_sqrt hL0.le
  have hsL : Real.sqrt (Real.log N) ≤ Real.log N := by nlinarith [hsq, hs0.le]
  have hεinv := h.eps_sq_inv_le
  have hεge := h.eps_ge
  have hε0 := h.eps_pos
  have hslow := h.kimSlow_le hk
  have hcl := h.asym.p7_quarter
  have hsN := sqrtN_eq_exp hn
  -- the left side is at most `10 log n`
  have hlhs : 9 / kimEps N ^ 2 + 8 ≤ 10 * Real.log N := by
    have h1 : 9 / kimEps N ^ 2 ≤ 9 * Real.sqrt (Real.log N) := by
      rw [div_eq_mul_one_div]; nlinarith [hεinv]
    linarith [h1, hsL, hLv]
  -- `13·e^{−δL−2√L−1}·√n = 13·e^{(1/2−δ)L−2√L−1}`
  have hE : Real.exp (-(kimDelta * Real.log N)
        - 2 * Real.sqrt (Real.log N) - 1) * Real.sqrt N
      = Real.exp (((1 : ℝ) / 2 - kimDelta) * Real.log N
          - 2 * Real.sqrt (Real.log N) - 1) := by
    rw [hsN, ← Real.exp_add]; congr 1; ring
  have hmono : Real.exp (((1 : ℝ) / 4 - kimDelta) * Real.log N
        - 2 * Real.sqrt (Real.log N) - 1)
      ≤ Real.exp (((1 : ℝ) / 2 - kimDelta) * Real.log N
          - 2 * Real.sqrt (Real.log N) - 1) :=
    Real.exp_le_exp.mpr (by nlinarith [hL0])
  have hbig : 10 * (Real.log N) ^ 3
      ≤ Real.exp (((1 : ℝ) / 2 - kimDelta) * Real.log N
          - 2 * Real.sqrt (Real.log N) - 1) := by
    have hp : (Real.log N) ^ 3 ≤ (Real.log N) ^ 5 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    have hp5 : (0 : ℝ) ≤ (Real.log N) ^ 5 := by positivity
    linarith [hcl, hmono, hp, hp5]
  have hslow' : 10 * (Real.log N) ^ 3 / Real.log N ≤ kimSlow N := by
    rw [kimSlow, div_le_div_iff₀ hL0 hL0]
    have hEE : 13 * Real.exp (-(kimDelta * Real.log N)
          - 2 * Real.sqrt (Real.log N) - 1) * Real.sqrt N
        = 13 * Real.exp (((1 : ℝ) / 2 - kimDelta) * Real.log N
            - 2 * Real.sqrt (Real.log N) - 1) := by
      rw [← hE]; ring
    rw [hEE]
    have hstep := mul_le_mul_of_nonneg_right hbig hL0.le
    have hEL : (0 : ℝ) ≤ Real.exp (((1 : ℝ) / 2 - kimDelta) * Real.log N
        - 2 * Real.sqrt (Real.log N) - 1) * Real.log N := by positivity
    nlinarith [hstep, hEL]
  have hslow0 : (0 : ℝ) ≤ kimSlow N := by
    have hp : (0 : ℝ) ≤ 10 * (Real.log N) ^ 3 / Real.log N := by positivity
    linarith [hslow', hp]
  have hmul : 1 / Real.log N * kimSlow N ≤ kimEps N * kimS N k := by
    have h1 : 1 / Real.log N * kimSlow N ≤ kimEps N * kimSlow N :=
      mul_le_mul_of_nonneg_right hεge hslow0
    have h2 : kimEps N * kimSlow N ≤ kimEps N * kimS N k :=
      mul_le_mul_of_nonneg_left hslow hε0.le
    linarith
  have hfin : 10 * Real.log N ≤ 1 / Real.log N * kimSlow N := by
    have hstep : 1 / Real.log N * (10 * (Real.log N) ^ 3 / Real.log N)
        ≤ 1 / Real.log N * kimSlow N :=
      mul_le_mul_of_nonneg_left hslow' (by positivity)
    have heq : 1 / Real.log N * (10 * (Real.log N) ^ 3 / Real.log N)
        = 10 * Real.log N := by field_simp; try ring
    linarith [hstep, heq.le, heq.ge]
  linarith [hlhs, hfin, hmul]



/-- **`12e√(log n)·θ/ε² ≤ e^{−1/ε²−1}`**, the base bound behind Kim's (59).

Equivalently `24e²/ε² ≤ log n`, which holds since `1/ε² = √(log log n) ≤ √log n`
and `log n ≥ 10⁶`. -/
lemma KimLarge.p8_A {N : ℕ} (h : KimLarge N) :
    12 * Real.exp 1 * Real.sqrt (Real.log N) * theta N / kimEps N ^ 2
      ≤ Real.exp (-(1 / kimEps N ^ 2) - 1) := by
  have hLv := h.logn_vast
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have hms : Real.sqrt (Real.log N) * Real.sqrt (Real.log N) = Real.log N :=
    Real.mul_self_sqrt hL0.le
  have hs1000 := h.sqrt_logn_ge
  have hε0 := h.eps_pos
  have hεsq0 : (0 : ℝ) < kimEps N ^ 2 := by positivity
  have hεinv := h.eps_sq_inv_le
  have hexpinv := h.exp_eps_sq_inv_le
  have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (0 : ℝ); simpa using this
  set A : ℝ := 12 * Real.exp 1 * Real.sqrt (Real.log N)
    * (1 / (Real.log N) ^ 2) with hAdef
  set D : ℝ := Real.exp (1 / kimEps N ^ 2) * Real.exp 1 with hDdef
  have hD0 : (0 : ℝ) < D := by rw [hDdef]; positivity
  have hA0 : (0 : ℝ) ≤ A := by rw [hAdef]; positivity
  -- `A·D ≤ ε²`
  have hkey : A * D ≤ kimEps N ^ 2 := by
    have hA : D ≤ 2 * Real.sqrt (Real.log N) * Real.exp 1 := by
      rw [hDdef]
      exact mul_le_mul_of_nonneg_right hexpinv (by linarith)
    refine le_trans (mul_le_mul_of_nonneg_left hA hA0) ?_
    have heq : A * (2 * Real.sqrt (Real.log N) * Real.exp 1)
        = 24 * Real.exp 1 * Real.exp 1
          * (Real.sqrt (Real.log N) * Real.sqrt (Real.log N))
          / (Real.log N) ^ 2 := by rw [hAdef]; ring
    rw [heq, hms]
    have hval : 24 * Real.exp 1 * Real.exp 1 * Real.log N / (Real.log N) ^ 2
        = 24 * Real.exp 1 * Real.exp 1 / Real.log N := by
      field_simp
      try ring
    rw [hval]
    have hlow : 1 / Real.sqrt (Real.log N) ≤ kimEps N ^ 2 := by
      rw [div_le_iff₀ hs0]
      have hm : (1 / kimEps N ^ 2) * kimEps N ^ 2
          ≤ Real.sqrt (Real.log N) * kimEps N ^ 2 :=
        mul_le_mul_of_nonneg_right hεinv hεsq0.le
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hεsq0)] at hm
      linarith [hm]
    have h24 : 24 * Real.exp 1 * Real.exp 1 ≤ 216 := by nlinarith [he3, he1]
    have hgoal : 24 * Real.exp 1 * Real.exp 1 / Real.log N
        ≤ 1 / Real.sqrt (Real.log N) := by
      rw [div_le_div_iff₀ hL0 hs0]
      nlinarith [h24, hs1000, hs0, hms]
    linarith [hgoal, hlow]
  -- `e^{−1/ε²−1}·D = 1`, so `A ≤ ε²·e^{−1/ε²−1}`
  have hED : Real.exp (-(1 / kimEps N ^ 2) - 1) * D = 1 := by
    rw [hDdef, ← Real.exp_add, ← Real.exp_add,
      show -(1 / kimEps N ^ 2) - 1 + (1 / kimEps N ^ 2 + 1) = (0 : ℝ) by ring,
      Real.exp_zero]
  have hE0' : (0 : ℝ) ≤ Real.exp (-(1 / kimEps N ^ 2) - 1) := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hkey hE0'
  have hid : Real.exp (-(1 / kimEps N ^ 2) - 1) * (A * D) = A := by
    calc Real.exp (-(1 / kimEps N ^ 2) - 1) * (A * D)
        = A * (Real.exp (-(1 / kimEps N ^ 2) - 1) * D) := by ring
      _ = A := by rw [hED]; ring
  rw [hid] at hmul
  rw [theta, div_le_iff₀ hεsq0]
  have hAgoal : 12 * Real.exp 1 * Real.sqrt (Real.log N)
      * (1 / (Real.log N) ^ 2) = A := hAdef.symm
  rw [hAgoal]
  linarith [hmul]


/-- **The scalar shape of Kim's (58).**  With `ρ = −1/(4ε)` and
`l ≤ ε²S`, the exponent is `−S(1 − ε/8 − 3ε/4) ≤ −(1−ε)S − log 2`, the last
step being `log 2 ≤ εS/8`. -/
lemma bin58_core {p ρ ε S : ℝ} (G l : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hρ : ρ = -(1 / (4 * ε))) (hexpρ : Real.exp ρ ≤ ε / 8)
    (hlS : (l : ℝ) ≤ ε ^ 2 * S) (hS0 : 0 ≤ S)
    (hpG : S ≤ p * (G : ℝ)) (hslack : 8 ≤ ε * S) :
    ((1 - p) + p * Real.exp ρ) ^ G / Real.exp (ρ * (3 * l))
      ≤ Real.exp (-(1 - ε) * S) / 2 := by
  have hEρ0 : (0 : ℝ) < Real.exp ρ := Real.exp_pos _
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg _
  have hG0 : (0 : ℝ) ≤ (G : ℝ) := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ (1 - p) + p * Real.exp ρ := by
    nlinarith [hp0, hp1, hEρ0.le]
  have hKle : (1 - p) + p * Real.exp ρ
      ≤ Real.exp (-(p * (1 - Real.exp ρ))) := by
    have := Real.add_one_le_exp (-(p * (1 - Real.exp ρ)))
    linarith
  have hpow : ((1 - p) + p * Real.exp ρ) ^ G
      ≤ (Real.exp (-(p * (1 - Real.exp ρ)))) ^ G :=
    pow_le_pow_left₀ hK0 hKle G
  have hexpG : (Real.exp (-(p * (1 - Real.exp ρ)))) ^ G
      = Real.exp ((G : ℝ) * (-(p * (1 - Real.exp ρ)))) := by
    rw [Real.exp_nat_mul]
  have hdivpos : (0 : ℝ) < Real.exp (ρ * (3 * l)) := Real.exp_pos _
  have hstep1 : ((1 - p) + p * Real.exp ρ) ^ G / Real.exp (ρ * (3 * l))
      ≤ Real.exp ((G : ℝ) * (-(p * (1 - Real.exp ρ))))
        / Real.exp (ρ * (3 * l)) := by
    rw [div_le_div_iff₀ hdivpos hdivpos]
    have := hpow
    rw [hexpG] at this
    nlinarith [this, hdivpos.le]
  have hcollapse : Real.exp ((G : ℝ) * (-(p * (1 - Real.exp ρ))))
        / Real.exp (ρ * (3 * l))
      = Real.exp ((G : ℝ) * (-(p * (1 - Real.exp ρ))) - ρ * (3 * l)) := by
    rw [Real.exp_sub]
  have hhalf : Real.exp (-(1 - ε) * S) / 2
      = Real.exp (-(1 - ε) * S - Real.log 2) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hhalf]
  refine le_trans hstep1 ?_
  rw [hcollapse]
  refine Real.exp_le_exp.mpr ?_
  -- `G·p·(1 − e^ρ) ≥ S(1 − ε/8)` and `−3ρl ≤ 3εS/4`
  have hone : (0 : ℝ) ≤ 1 - Real.exp ρ := by
    have : ε / 8 ≤ 1 := by linarith
    linarith [hexpρ, this]
  have hlow : S * (1 - ε / 8) ≤ (G : ℝ) * (p * (1 - Real.exp ρ)) := by
    have h1 : S * (1 - Real.exp ρ) ≤ (p * (G : ℝ)) * (1 - Real.exp ρ) :=
      mul_le_mul_of_nonneg_right hpG hone
    have h2 : S * (1 - ε / 8) ≤ S * (1 - Real.exp ρ) := by
      nlinarith [hS0, hexpρ]
    have h3 : (p * (G : ℝ)) * (1 - Real.exp ρ)
        = (G : ℝ) * (p * (1 - Real.exp ρ)) := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hdrift : -(ρ * (3 * (l : ℝ))) ≤ 3 * ε * S / 4 := by
    rw [hρ]
    have hval : -(-(1 / (4 * ε)) * (3 * (l : ℝ))) = 3 * (l : ℝ) / (4 * ε) := by
      field_simp
    rw [hval, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ε)]
    nlinarith [hlS, hε0, hε1, hS0]
  have hlog2 : Real.log 2 ≤ 1 := by
    have h1 : Real.log 2 ≤ 2 - 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have hslack' : 1 ≤ ε * S / 8 := by linarith [hslack]
  nlinarith [hlow, hdrift, hlog2, hslack', hS0]


/-- **The scalar shape of Kim's (59).**  `η^l/l! ≤ (ηe/l)^l ≤ A^l` via
`l! ≥ (l/e)^l`, and then `A ≤ e^{−1/ε²−1}` with `l ≥ ε²S − 1` gives the
exponent `−S + 1/ε² − l ≤ −(1−ε)S − log 2`. -/
lemma fam59_core {η A ε S : ℝ} (l : ℕ)
    (hη0 : 0 ≤ η) (hηl : η ≤ A * (l : ℝ) / Real.exp 1)
    (hA0 : 0 < A) (hAle : A ≤ Real.exp (-(1 / ε ^ 2) - 1))
    (hlow : ε ^ 2 * S - 1 ≤ (l : ℝ)) (hε0 : 0 < ε)
    (hslack : 1 / ε ^ 2 + Real.log 2 ≤ ε * S) :
    η ^ l / (l.factorial : ℝ) ≤ Real.exp (-(1 - ε) * S) / 2 := by
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg _
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hfacpos : (0 : ℝ) < (l.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos l
  have hEl0 : (0 : ℝ) < Real.exp (l : ℝ) := Real.exp_pos _
  -- `l! ≥ l^l/e^l`
  have hfact : (l : ℝ) ^ l / (l.factorial : ℝ) ≤ Real.exp (l : ℝ) :=
    Real.pow_div_factorial_le_exp (l : ℝ) hl0 l
  have hLL : (l : ℝ) ^ l ≤ Real.exp (l : ℝ) * (l.factorial : ℝ) := by
    rw [div_le_iff₀ hfacpos] at hfact
    linarith [hfact]
  have hE1 : (Real.exp 1) ^ l = Real.exp (l : ℝ) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hAl0 : (0 : ℝ) ≤ A ^ l := by positivity
  -- `η^l/l! ≤ A^l`
  have hηpow : η ^ l ≤ (A * (l : ℝ) / Real.exp 1) ^ l :=
    pow_le_pow_left₀ hη0 hηl l
  have hstep : η ^ l / (l.factorial : ℝ) ≤ A ^ l := by
    rw [div_le_iff₀ hfacpos]
    have h1 : η ^ l ≤ A ^ l * (l : ℝ) ^ l / Real.exp (l : ℝ) := by
      refine le_trans hηpow (le_of_eq ?_)
      rw [div_pow, mul_pow, hE1]
    have h2 : A ^ l * (l : ℝ) ^ l / Real.exp (l : ℝ)
        ≤ A ^ l * (l.factorial : ℝ) := by
      rw [div_le_iff₀ hEl0]
      nlinarith [hLL, hAl0, hEl0.le]
    linarith
  refine le_trans hstep ?_
  -- `A^l ≤ e^{l(−1/ε²−1)}`
  have hAC : A ^ l ≤ (Real.exp (-(1 / ε ^ 2) - 1)) ^ l :=
    pow_le_pow_left₀ hA0.le hAle l
  have hCl : (Real.exp (-(1 / ε ^ 2) - 1)) ^ l
      = Real.exp ((l : ℝ) * (-(1 / ε ^ 2) - 1)) := by
    rw [Real.exp_nat_mul]
  have hhalf : Real.exp (-(1 - ε) * S) / 2
      = Real.exp (-(1 - ε) * S - Real.log 2) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hhalf]
  refine le_trans hAC ?_
  rw [hCl]
  refine Real.exp_le_exp.mpr ?_
  have hkey2 : S - 1 / ε ^ 2 ≤ (l : ℝ) / ε ^ 2 := by
    rw [le_div_iff₀ hε2]
    have hid : (S - 1 / ε ^ 2) * ε ^ 2 = ε ^ 2 * S - 1 := by
      field_simp
    rw [hid]
    exact hlow
  have hexp : (l : ℝ) * (-(1 / ε ^ 2) - 1)
      = -((l : ℝ) / ε ^ 2) - (l : ℝ) := by
    field_simp
    try ring
  rw [hexp]
  linarith [hkey2, hslack, hl0]

set_option maxHeartbeats 4000000 in
open scoped Classical in
/-- **Property 7's failure probability at Kim's parameters.**

`β = (3(k+1)log n)^{1/2}`, `γ = log n`, `thr = 2β√t`, `h = ⌈thr⌉`, the
deviation `λ = b²θ²C(t,2)/16`, and the tilts `n^{−5/17}` for (38) and
`n^{−1/4−1/17}` for (39), (46), (49) — all Kim's. -/
lemma bad7_final (k : ℕ) (s : BlockState V) (hN : KimLarge n)
    (hk : k ≤ ⌊(n : ℝ) ^ ((1 : ℝ) / 17 - 10 ^ (-5 : ℤ)) / theta n⌋₊)
    (h1 : Property1 s k) (h2 : Property2 s k) (h3 : Property3 s k)
    (h4 : Property4 s k) (h5 : Property5 s k) (h6 : Property6 s k)
    (h7 : Property7 s k) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property7 (blockStepP s (kimM n k) σ) (k + 1)))
      ≤ 4 / n := by
  have hn : 0 < n := hN.card_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn8 : (8 : ℝ) < (n : ℝ) := hN.1
  have hn2 : 2 ≤ n := by
    have : (2 : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  have hk' : k ≤ ⌊(n : ℝ) ^ kimDelta / theta n⌋₊ := by rwa [kimDelta]
  have hlogn := hN.logn_ge_one
  have hLv := hN.logn_vast
  have hL0 : (0 : ℝ) < Real.log n := by linarith
  have hρ70 : (0 : ℝ) ≤ kimRho7 n := kimRho7_nonneg n
  have hρ380 : (0 : ℝ) ≤ kimRho38 n := kimRho38_nonneg n
  have hlam0 : (0 : ℝ) ≤ kimLam n k := kimLam_nonneg n k
  have hthr0 : (0 : ℝ) ≤ kimThr7 n k := by
    rw [kimThr7]
    exact mul_nonneg (by linarith [kimBeta_nonneg n k]) (Real.sqrt_nonneg _)
  set q7 : ℝ := Real.exp (-(kimRho7 n * kimLam n k) / 2) with hq7def
  set q38 : ℝ := 2 * Real.exp (-(kimRho38 n * kimLam n k) / 2) with hq38def
  -- side conditions, in Kim's order
  have hs46 : Real.exp (-(kimRho7 n) * kimLam n k
      + kimRho7 n ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
        * ((bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ))
          * ((4 * ((kimHpar n k : ℕ) : ℝ)) ^ 2
            * Real.exp (kimRho7 n * (4 * ((kimHpar n k : ℕ) : ℝ))))))) ≤ q7 := by
    rw [hq7def]
    exact Real.exp_le_exp.mpr (by linarith [hN.var46 hk'])
  have hrhoh : kimRho7 n * ((kimHpar n k : ℕ) : ℝ) ≤ 1 := by
    have hsmall := hN.rho7_thr7_small hk'
    have hhle := hN.hpar_le (k := k)
    nlinarith [hsmall, hhle, hρ70, hthr0,
      Nat.cast_nonneg (α := ℝ) (kimHpar n k)]
  have hs49 : Real.exp (-(kimRho7 n * ((edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ)) * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)) + kimLam n k)))
      + (kimRho7 n * (edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ))
            * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)))
        + 1024 * kimRho7 n ^ 2
          * ((1 - edgeProb n) + edgeProb n * Real.exp 1) ^ (tParam n)
          * (n : ℝ))) ≤ q7 := by
    rw [hq7def]
    refine Real.exp_le_exp.mpr ?_
    have hv := hN.var49 hk'
    have hexp : kimRho7 n * ((edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ)) * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)) + kimLam n k))
        = kimRho7 n * (edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ))
            * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)))
          + kimRho7 n * kimLam n k := by ring
    rw [hexp]
    linarith [hv]
  have hs39 : Real.exp (-(kimRho7 n) * kimLam n k
      + kimRho7 n ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
        * ((2 * kimThr7 n k) * (2 * (kimM n k : ℝ)
            * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)))
            * Real.exp (kimRho7 n * (2 * kimThr7 n k))))) ≤ q7 := by
    rw [hq7def]
    exact Real.exp_le_exp.mpr (by linarith [hN.var39 hk'])
  have hs38 : kimRho38 n ^ 2 / 2 * (edgeProb n * (1 - edgeProb n)
        * ((bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ))
          * Real.exp (kimRho38 n)))
      ≤ kimRho38 n * kimLam n k / 2 := hN.var38 hk'
  have hsc1 : ((((mcut n : ℝ) * (((tParam n : ℕ) : ℝ) + ((tParam n : ℕ) : ℝ) / 2) + bSeq n k * (bSeq n k * theta n * Real.sqrt n + (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log n) * (((tParam n : ℕ) : ℝ) + ((tParam n : ℕ) : ℝ) / (2 * Real.log n ^ 2))) + (edgeProb n * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)) + kimLam n k) + ((edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ)) * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)) + kimLam n k) + (edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ)) * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)) + kimLam n k) + ((2 * (mcut n : ℝ)) / 2 * (((tParam n : ℕ) : ℝ) + ((tParam n : ℕ) : ℝ) / 2) + (bSeq n k * (bSeq n k * theta n * Real.sqrt n + (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log n) / 2) * (((tParam n : ℕ) : ℝ) + ((tParam n : ℕ) : ℝ) / (2 * Real.log n ^ 2)))) + bSeq n (k + 1) * μSeq n (k + 1) * (((tParam n).choose 2 : ℕ) : ℝ))) + kimLam n k
      ≤ (1 - edgeProb n) ^ (2 * kimM n k)
        * (bSeq n k * μSeq n k * ((tParam n).choose 2)) := by
    have hm := hN.hc1_master hk'
    have hb1 := bSeq_le_one n k
    have hb0 := (bSeq_pos n k).le
    have hT0 : (0 : ℝ) ≤ (((tParam n).choose 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hp0 : (0 : ℝ) ≤ edgeProb n := edgeProb_nonneg n
    have hpb : edgeProb n * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ))
        ≤ edgeProb n * (((tParam n).choose 2 : ℕ) : ℝ) := by
      refine mul_le_mul_of_nonneg_left ?_ hp0
      nlinarith [hb1, hb0, hT0]
    have hcube : edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ))
          * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ))
        = bSeq n k ^ 3 * theta n ^ 2 * (((tParam n).choose 2 : ℕ) : ℝ) := by
      have hp2 : edgeProb n ^ 2 = theta n ^ 2 / (n : ℝ) := by
        rw [edgeProb, div_pow, Real.sq_sqrt hnR.le]
      rw [hp2]
      field_simp
      try ring
    rw [kimLam]
    linarith [hm, hpb, hcube.le, hcube.ge]
  have hbound := bad7_bound' (V := V) k s hN hk h1 h2 h3 h4 h5 h6 h7
    (β := kimBeta n k) (γ := Real.log n)
    (hN.beta_ge_one k) hlogn (hN.beta_le_sqrt_t hk') (tParam_pos hn2)
    (kimThr7 n k) (by rw [kimThr7]) (hN.thr7_ge_one k)
    (hN.beta_gamma_t_le hk') (by rw [kimBeta_sq n k hL0.le]) rfl rfl
    (kimHpar n k) (t5 := kimRho7 n) (lam5 := kimLam n k) hρ70
    (c5 := (edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ)) * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)) + kimLam n k)) le_rfl (q5 := q7) hs46
    (ρ := kimRho7 n) hρ70 hrhoh
    (c6 := (edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ)) * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)) + kimLam n k)) (q6 := q7) hs49 (Nat.le_ceil _)
    (c7 := ((2 * (mcut n : ℝ)) / 2 * (((tParam n : ℕ) : ℝ) + ((tParam n : ℕ) : ℝ) / 2) + (bSeq n k * (bSeq n k * theta n * Real.sqrt n + (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log n) / 2) * (((tParam n : ℕ) : ℝ) + ((tParam n : ℕ) : ℝ) / (2 * Real.log n ^ 2)))) le_rfl rfl
    (c1 := (((mcut n : ℝ) * (((tParam n : ℕ) : ℝ) + ((tParam n : ℕ) : ℝ) / 2) + bSeq n k * (bSeq n k * theta n * Real.sqrt n + (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log n) * (((tParam n : ℕ) : ℝ) + ((tParam n : ℕ) : ℝ) / (2 * Real.log n ^ 2))) + (edgeProb n * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)) + kimLam n k) + ((edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ)) * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)) + kimLam n k) + (edgeProb n ^ 2 * (bSeq n k ^ 2 * (n : ℝ)) * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)) + kimLam n k) + ((2 * (mcut n : ℝ)) / 2 * (((tParam n : ℕ) : ℝ) + ((tParam n : ℕ) : ℝ) / 2) + (bSeq n k * (bSeq n k * theta n * Real.sqrt n + (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log n) / 2) * (((tParam n : ℕ) : ℝ) + ((tParam n : ℕ) : ℝ) / (2 * Real.log n ^ 2)))) + bSeq n (k + 1) * μSeq n (k + 1) * (((tParam n).choose 2 : ℕ) : ℝ))) (hsplit := by ring)
    (L := (1 - edgeProb n) ^ (2 * kimM n k))
    (pow_nonneg (by linarith [hN.edgeProb_le_half]) _) le_rfl
    (lam1 := kimLam n k) hsc1 (t1 := kimRho7 n) hρ70 (q1 := q7) hs39
    (t3 := kimRho38 n) (lam3 := kimLam n k) hρ380 hs38
    (c3 := (edgeProb n * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ)) + kimLam n k)) le_rfl (q3 := q38) le_rfl
    (by positivity)
  -- the `C(n,t)` union bound
  have hdb := hN.drift_beats_union hk'
  have hdb' : ((tParam n : ℕ) : ℝ) * Real.log n + 3 * Real.log n
      ≤ kimRho7 n * kimLam n k / 2 := by
    rw [kimLam]; linarith [hdb]
  have hchoose : ((n : ℕ).choose (tParam n) : ℝ)
      ≤ Real.exp (((tParam n : ℕ) : ℝ) * Real.log n) := by
    have hpow : ((n : ℝ)) ^ (tParam n)
        = Real.exp (((tParam n : ℕ) : ℝ) * Real.log n) := by
      rw [Real.exp_nat_mul, Real.exp_log hnR]
    rw [← hpow]
    exact_mod_cast Nat.choose_le_pow n (tParam n)
  have hC0 : (0 : ℝ) ≤ ((n : ℕ).choose (tParam n) : ℝ) := Nat.cast_nonneg _
  have hcube : Real.exp (-(3 * Real.log n)) = 1 / (n : ℝ) ^ (3 : ℕ) := by
    rw [Real.exp_neg, one_div]
    congr 1
    rw [show (3 : ℝ) * Real.log n = ((3 : ℕ) : ℝ) * Real.log n by norm_num,
      Real.exp_nat_mul, Real.exp_log hnR]
  have hq7le : ((n : ℕ).choose (tParam n) : ℝ) * q7 ≤ 1 / (n : ℝ) ^ (3 : ℕ) := by
    rw [hq7def]
    refine le_trans (mul_le_mul_of_nonneg_right hchoose (Real.exp_pos _).le) ?_
    rw [← Real.exp_add, ← hcube]
    exact Real.exp_le_exp.mpr (by linarith [hdb'])
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hρcmp : kimRho7 n ≤ kimRho38 n := by
    rw [kimRho7, kimRho38]
    exact Real.rpow_le_rpow_of_exponent_le hn1R (by norm_num)
  have hq38le : ((n : ℕ).choose (tParam n) : ℝ) * q38
      ≤ 2 * (1 / (n : ℝ) ^ (3 : ℕ)) := by
    rw [hq38def]
    have hstep : ((n : ℕ).choose (tParam n) : ℝ)
          * Real.exp (-(kimRho38 n * kimLam n k) / 2)
        ≤ 1 / (n : ℝ) ^ (3 : ℕ) := by
      refine le_trans (mul_le_mul_of_nonneg_right hchoose (Real.exp_pos _).le) ?_
      rw [← Real.exp_add, ← hcube]
      refine Real.exp_le_exp.mpr ?_
      have hmono : kimRho7 n * kimLam n k ≤ kimRho38 n * kimLam n k :=
        mul_le_mul_of_nonneg_right hρcmp hlam0
      linarith [hdb', hmono]
    nlinarith [hstep, hC0, Real.exp_pos (-(kimRho38 n * kimLam n k) / 2)]
  have hq7pos : (0 : ℝ) < q7 := by rw [hq7def]; exact Real.exp_pos _
  have hsumle : ((n : ℕ).choose (tParam n) : ℝ) * (q7 + q38 + (q7 + q7))
      ≤ 5 * (1 / (n : ℝ) ^ (3 : ℕ)) := by
    have hexp : ((n : ℕ).choose (tParam n) : ℝ) * (q7 + q38 + (q7 + q7))
        = ((n : ℕ).choose (tParam n) : ℝ) * q7
          + ((n : ℕ).choose (tParam n) : ℝ) * q38
          + (((n : ℕ).choose (tParam n) : ℝ) * q7
            + ((n : ℕ).choose (tParam n) : ℝ) * q7) := by ring
    rw [hexp]
    linarith [hq7le, hq38le]
  have hn3 : (0 : ℝ) < (n : ℝ) ^ (3 : ℕ) := by positivity
  have hfin : (3 / (n : ℝ) + (n : ℝ) * ((n : ℝ) ^ (3 : ℕ))⁻¹)
      + 5 * (1 / (n : ℝ) ^ (3 : ℕ)) ≤ 4 / (n : ℝ) := by
    rw [← sub_nonneg]
    have hkey : 4 / (n : ℝ) - ((3 / (n : ℝ) + (n : ℝ) * ((n : ℝ) ^ (3 : ℕ))⁻¹)
        + 5 * (1 / (n : ℝ) ^ (3 : ℕ)))
        = ((n : ℝ) * (n : ℝ) - (n : ℝ) - 5) / (n : ℝ) ^ (3 : ℕ) := by
      field_simp
      ring
    rw [hkey]
    have hnn : (0 : ℝ) ≤ (n : ℝ) * (n : ℝ) - (n : ℝ) - 5 := by nlinarith [hn8]
    positivity
  linarith [hbound, hsumle, hfin]


set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **Property 8's failure probability at Kim's parameters** (§4.9).

`ρ = −ε⁻¹/4`, `l = ⌊ε²·bμθ(t choose 2)/√n⌋` and
`B = exp(−(1−ε)·bμθ(t choose 2)/√n)`, all Kim's. -/
lemma bad8_final (k : ℕ) (s : BlockState V) (hN : KimLarge n)
    (hk : k ≤ ⌊(n : ℝ) ^ ((1 : ℝ) / 17 - 10 ^ (-5 : ℤ)) / theta n⌋₊)
    (h4 : Property4 s k) (h5 : Property5 s k) (h6 : Property6 s k)
    (h7 : Property7 s k) (h8 : Property8 s k) :
    bernoulliPr (edgeProb n) (Finset.univ.filter
        (fun σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool =>
          ¬ Property8 (blockStepP s (kimM n k) σ) (k + 1)))
      ≤ 1 / n := by
  have hn : 0 < n := hN.card_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsN0 : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hk' : k ≤ ⌊(n : ℝ) ^ kimDelta / theta n⌋₊ := by rwa [kimDelta]
  have hLv := hN.logn_vast
  have hL0 : (0 : ℝ) < Real.log n := by linarith
  have hθ0 := hN.theta_pos'
  have hε0 := hN.eps_pos
  have hε1 := hN.eps_le_one
  have hεsq0 : (0 : ℝ) < kimEps n ^ 2 := by positivity
  have hS0 : (0 : ℝ) ≤ kimS n k := kimS_nonneg hN hk'
  have hp0 : (0 : ℝ) ≤ edgeProb n := edgeProb_nonneg n
  have hp1 : edgeProb n ≤ 1 := by linarith [hN.edgeProb_le_half]
  have hpS := hN.p8_S hk'
  have hslack8 : (8 : ℝ) ≤ kimEps n * kimS n k := by
    have : (0 : ℝ) ≤ 9 / kimEps n ^ 2 := by positivity
    linarith [hpS]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  -- the floor `l`
  set l : ℕ := ⌊kimEps n ^ 2 * kimS n k⌋₊ with hldef
  have hεS0 : (0 : ℝ) ≤ kimEps n ^ 2 * kimS n k := by positivity
  have hlle : (l : ℝ) ≤ kimEps n ^ 2 * kimS n k := by
    rw [hldef]; exact Nat.floor_le hεS0
  have hlge : kimEps n ^ 2 * kimS n k - 1 ≤ (l : ℝ) := by
    have := Nat.lt_floor_add_one (kimEps n ^ 2 * kimS n k)
    rw [hldef]; linarith
  -- `ε²S ≥ 9`, so `l ≥ ε²S/2`
  have hεS9 : (9 : ℝ) ≤ kimEps n ^ 2 * kimS n k := by
    have h1 : kimEps n * (kimEps n * kimS n k)
        = kimEps n ^ 2 * kimS n k := by ring
    have h2 : 9 / kimEps n ^ 2 ≤ kimEps n * kimS n k := by linarith [hpS]
    have h3 : (9 : ℝ) / kimEps n ≤ kimEps n * (kimEps n * kimS n k) := by
      have hm := mul_le_mul_of_nonneg_left h2 hε0.le
      have heq : kimEps n * (9 / kimEps n ^ 2) = 9 / kimEps n := by
        field_simp; try ring
      linarith [hm, heq.le, heq.ge]
    have h4 : (9 : ℝ) ≤ 9 / kimEps n := by
      rw [le_div_iff₀ hε0]; nlinarith [hε1, hε0]
    linarith [h1.le, h1.ge, h3, h4]
  have hlhalf : kimEps n ^ 2 * kimS n k / 2 ≤ (l : ℝ) := by linarith [hlge, hεS9]
  refine bad8_bound k s hN h4 h5 l
    (ρ := -(1 / (4 * kimEps n)))
    (by linarith [show (0 : ℝ) < 1 / (4 * kimEps n) by positivity])
    (B := Real.exp (-(1 - kimEps n) * kimS n k)) (Real.exp_pos _) ?_ ?_ ?_
  · -- (58)
    intro T hT
    have hpG : kimS n k ≤ edgeProb n * ((gammaBetween s.Γ T T).card : ℝ) := by
      have hg := h7 T hT
      have hstep := mul_le_mul_of_nonneg_left hg hp0
      have heq : edgeProb n
            * (bSeq n k * μSeq n k * (((tParam n).choose 2 : ℕ) : ℝ))
          = kimS n k := by
        rw [edgeProb, kimS]; field_simp; try ring
      linarith [hstep, heq.le, heq.ge]
    exact bin58_core _ l hp0 hp1 hε0 hε1 rfl hN.asym.p8_eps hlle hS0 hpG
      hslack8
  · -- (59)
    intro T hT
    have hG0 : (0 : ℝ) ≤ ((gammaBetween s.Γ T T).card : ℝ) := Nat.cast_nonneg _
    have hb0 := (bSeq_pos n k).le
    have hb1 := bSeq_le_one n k
    have hM := hN.kimM_le_b hk'
    have hs0 : (0 : ℝ) < Real.sqrt (Real.log n) := Real.sqrt_pos.mpr hL0
    have hsq : Real.sqrt (Real.log n) ^ 2 = Real.log n := Real.sq_sqrt hL0.le
    have hs1 : (1 : ℝ) ≤ Real.sqrt (Real.log n) := by
      nlinarith [hsq, hs0.le, hLv]
    have hθ1 : theta n ≤ 1 := by
      have := hN.2.1; linarith
    -- `2Mp² + b²np³ ≤ 3√(log n)·θ²/√n`
    have hinner : 2 * (kimM n k : ℝ) * edgeProb n ^ 2
          + (bSeq n k ^ 2 * (n : ℝ)) * edgeProb n ^ 3
        ≤ 3 * Real.sqrt (Real.log n) * theta n ^ 2 / Real.sqrt n := by
      have hp2 : edgeProb n ^ 2 = theta n ^ 2 / (n : ℝ) := by
        rw [edgeProb, div_pow, Real.sq_sqrt hnR.le]
      have hp3 : edgeProb n ^ 3
          = theta n ^ 3 / ((n : ℝ) * Real.sqrt n) := by
        rw [edgeProb, div_pow]
        congr 1
        rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, Real.sq_sqrt hnR.le,
          pow_one]
      have hA : 2 * (kimM n k : ℝ) * edgeProb n ^ 2
          ≤ 2 * Real.sqrt (Real.log n) * theta n ^ 2 / Real.sqrt n := by
        rw [hp2]
        have hMb : (kimM n k : ℝ)
            ≤ Real.sqrt (Real.log n) * Real.sqrt n := by
          nlinarith [hM, hb1, hb0,
            mul_nonneg (Real.sqrt_nonneg (Real.log n))
              (Real.sqrt_nonneg (n : ℝ))]
        have hc : (0 : ℝ) ≤ theta n ^ 2 / (n : ℝ) := by positivity
        have hstep := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hMb (by norm_num : (0:ℝ) ≤ 2)) hc
        refine le_trans hstep (le_of_eq ?_)
        have hkeyn : Real.sqrt n / (n : ℝ) = 1 / Real.sqrt n := by
          rw [div_eq_div_iff (ne_of_gt hnR) (ne_of_gt hsN0), one_mul,
            Real.mul_self_sqrt hnR.le]
        rw [show 2 * (Real.sqrt (Real.log n) * Real.sqrt n)
              * (theta n ^ 2 / (n : ℝ))
            = 2 * Real.sqrt (Real.log n) * theta n ^ 2
              * (Real.sqrt n / (n : ℝ)) by ring, hkeyn]
        ring
      have hB : (bSeq n k ^ 2 * (n : ℝ)) * edgeProb n ^ 3
          ≤ Real.sqrt (Real.log n) * theta n ^ 2 / Real.sqrt n := by
        rw [hp3]
        have hbb : bSeq n k ^ 2 ≤ 1 := by nlinarith [hb0, hb1]
        have heq : (1 * (n : ℝ)) * (theta n ^ 3 / ((n : ℝ) * Real.sqrt n))
            = theta n ^ 3 / Real.sqrt n := by field_simp; try ring
        have hstep : (bSeq n k ^ 2 * (n : ℝ))
              * (theta n ^ 3 / ((n : ℝ) * Real.sqrt n))
            ≤ (1 * (n : ℝ)) * (theta n ^ 3 / ((n : ℝ) * Real.sqrt n)) := by
          have hc : (0 : ℝ) ≤ (theta n ^ 3 / ((n : ℝ) * Real.sqrt n)) := by
            positivity
          have := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hbb hnR.le) hc
          linarith [this]
        rw [heq] at hstep
        refine le_trans hstep ?_
        rw [div_le_div_iff₀ hsN0 hsN0]
        have hθ3 : theta n ^ 3 ≤ Real.sqrt (Real.log n) * theta n ^ 2 := by
          nlinarith [hθ1, hθ0.le, hs1, sq_nonneg (theta n)]
        nlinarith [hθ3, hsN0.le, mul_nonneg (Real.sqrt_nonneg (Real.log n))
          (sq_nonneg (theta n))]
      have hX : (3 : ℝ) * Real.sqrt (Real.log n) * theta n ^ 2 / Real.sqrt n
          = 2 * Real.sqrt (Real.log n) * theta n ^ 2 / Real.sqrt n
            + Real.sqrt (Real.log n) * theta n ^ 2 / Real.sqrt n := by
        field_simp
        try ring
      linarith [hA, hB, hX.le, hX.ge]
    -- `η ≤ 6√(log n)·θ·S`
    have hGb : ((gammaBetween s.Γ T T).card : ℝ)
        ≤ bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ) :=
      h6.gammaT_le hN.mcut_pos hN.two_mcut_le_t hT
    have hmu := (hN.mu_bounds hk').1
    have hST : theta n / Real.sqrt n * ((gammaBetween s.Γ T T).card : ℝ)
        ≤ 2 * kimS n k := by
      have hc : (0 : ℝ) ≤ theta n / Real.sqrt n := by positivity
      have hstep := mul_le_mul_of_nonneg_left hGb hc
      have heq : theta n / Real.sqrt n
            * (bSeq n k * (((tParam n).choose 2 : ℕ) : ℝ))
          = bSeq n k * theta n / Real.sqrt n
            * (((tParam n).choose 2 : ℕ) : ℝ) := by ring
      rw [heq] at hstep
      have hmul : bSeq n k * theta n / Real.sqrt n
            * (((tParam n).choose 2 : ℕ) : ℝ)
          ≤ 2 * kimS n k := by
        rw [kimS]
        have hc2 : (0 : ℝ) ≤ bSeq n k * theta n / Real.sqrt n
            * (((tParam n).choose 2 : ℕ) : ℝ) := by positivity
        have hkeyμ : bSeq n k * theta n / Real.sqrt n
              * (((tParam n).choose 2 : ℕ) : ℝ) * (1 / 2)
            ≤ bSeq n k * theta n / Real.sqrt n
              * (((tParam n).choose 2 : ℕ) : ℝ) * μSeq n k :=
          mul_le_mul_of_nonneg_left hmu hc2
        have heqμ : bSeq n k * theta n / Real.sqrt n
              * (((tParam n).choose 2 : ℕ) : ℝ) * μSeq n k
            = bSeq n k * μSeq n k * theta n / Real.sqrt n
              * (((tParam n).choose 2 : ℕ) : ℝ) := by ring
        linarith [hkeyμ, heqμ.le, heqμ.ge]
      linarith [hstep, hmul]
    have hη : ((gammaBetween s.Γ T T).card : ℝ)
          * (2 * (kimM n k : ℝ) * edgeProb n ^ 2
            + (bSeq n k ^ 2 * (n : ℝ)) * edgeProb n ^ 3)
        ≤ 6 * Real.sqrt (Real.log n) * theta n * kimS n k := by
      have hstep := mul_le_mul_of_nonneg_left hinner hG0
      have heq : ((gammaBetween s.Γ T T).card : ℝ)
            * (3 * Real.sqrt (Real.log n) * theta n ^ 2 / Real.sqrt n)
          = 3 * Real.sqrt (Real.log n) * theta n
            * (theta n / Real.sqrt n
              * ((gammaBetween s.Γ T T).card : ℝ)) := by ring
      rw [heq] at hstep
      have hc : (0 : ℝ) ≤ 3 * Real.sqrt (Real.log n) * theta n := by positivity
      have hfin := mul_le_mul_of_nonneg_left hST hc
      have heq2 : 3 * Real.sqrt (Real.log n) * theta n * (2 * kimS n k)
          = 6 * Real.sqrt (Real.log n) * theta n * kimS n k := by ring
      linarith [hstep, hfin, heq2.le, heq2.ge]
    -- apply `fam59_core`
    refine fam59_core l (by positivity) ?_ (by positivity) (hN.p8_A) hlge hε0 ?_
    · -- `η ≤ A·l/e`
      have hAe : 12 * Real.exp 1 * Real.sqrt (Real.log n) * theta n
            / kimEps n ^ 2 * (l : ℝ) / Real.exp 1
          = 12 * Real.sqrt (Real.log n) * theta n * (l : ℝ) / kimEps n ^ 2 := by
        field_simp
        try ring
      rw [hAe]
      refine le_trans hη ?_
      rw [le_div_iff₀ hεsq0]
      have hc : (0 : ℝ) ≤ 12 * Real.sqrt (Real.log n) * theta n := by positivity
      have hstep := mul_le_mul_of_nonneg_left hlhalf hc
      have heq : 12 * Real.sqrt (Real.log n) * theta n
            * (kimEps n ^ 2 * kimS n k / 2)
          = 6 * Real.sqrt (Real.log n) * theta n * kimS n k
            * kimEps n ^ 2 := by ring
      rw [heq] at hstep
      linarith [hstep]
    · -- slack
      have h1 : 1 / kimEps n ^ 2 ≤ 9 / kimEps n ^ 2 := by
        rw [div_le_div_iff₀ hεsq0 hεsq0]; nlinarith [hεsq0]
      linarith [hpS, hlog2, h1]
  · -- the population target
    have hexp : ∑ j ∈ Finset.range (k + 1),
          bSeq n j * μSeq n j * theta n / Real.sqrt n
            * (((tParam n).choose 2 : ℕ) : ℝ)
        = (∑ j ∈ Finset.range k,
            bSeq n j * μSeq n j * theta n / Real.sqrt n
              * (((tParam n).choose 2 : ℕ) : ℝ)) + kimS n k := by
      rw [Finset.sum_range_succ, kimS]
    have hC0 : (0 : ℝ) ≤ (Nat.choose (Fintype.card V) (tParam n) : ℝ) :=
      Nat.cast_nonneg _
    have hnk : (0 : ℝ) ≤ (n : ℝ) ^ k := by positivity
    have hB0 : (0 : ℝ) < Real.exp (-(1 - kimEps n) * kimS n k) := Real.exp_pos _
    have hstep := mul_le_mul_of_nonneg_right h8 hB0.le
    have hmul := mul_le_mul_of_nonneg_left hstep hnR.le
    refine le_trans hmul (le_of_eq ?_)
    rw [hexp]
    rw [show -(1 - kimEps n)
        * ((∑ j ∈ Finset.range k,
            bSeq n j * μSeq n j * theta n / Real.sqrt n
              * (((tParam n).choose 2 : ℕ) : ℝ)) + kimS n k)
        = -(1 - kimEps n)
            * (∑ j ∈ Finset.range k,
              bSeq n j * μSeq n j * theta n / Real.sqrt n
                * (((tParam n).choose 2 : ℕ) : ℝ))
          + -(1 - kimEps n) * kimS n k by ring, Real.exp_add]
    ring

/-- **Kim Main Lemma 2.1.** From a state satisfying Properties 1–8 at stage
`k`, the block construction produces — for some sample `σ` — a state
satisfying them at stage `k+1`.

The conclusion is stated for `blockStepP`, which realises Kim's `Γ_{k+1}` of
(21): `Γ \ (X ∪ Y ∪ Z)` with `Y` taken with respect to the *padded* `Λ*`. The
unpadded `blockStep` alone would leave `Γ_{k+1}` too large for Properties 2, 5
and 6, which bound `Γ`-quantities from above. -/
theorem main_lemma_2_1 (k : ℕ) (s : BlockState V) (hN : KimLarge n)
    (hk : k ≤ ⌊(n : ℝ) ^ ((1 : ℝ) / 17 - 10 ^ (-5 : ℤ)) / theta n⌋₊)
    (h_props : Properties1to8 s k) :
    ∃ σ : Fin (Fintype.card (Coord V (kimM n k))) → Bool,
      Properties1to8 (blockStepP s (kimM n k) σ) (k + 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h_props
  have hn : 0 < n := hN.card_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hk' : k ≤ ⌊(n : ℝ) ^ kimDelta / theta n⌋₊ := by rwa [kimDelta]
  have hLv := hN.logn_vast
  have hn100 : (100 : ℝ) ≤ (n : ℝ) := by
    have hstep : Real.exp (1000000 : ℝ) ≤ Real.exp (Real.log n) :=
      Real.exp_le_exp.mpr hLv
    rw [Real.exp_log hnR] at hstep
    have hlin : (1000000 : ℝ) + 1 ≤ Real.exp (1000000 : ℝ) := by
      have := Real.add_one_le_exp (1000000 : ℝ); linarith
    linarith
  have hE : (Fintype.card (Edge V) : ℝ) ≤ (n : ℝ) * n := by
    exact_mod_cast card_Edge_le_sq (V := V)
  refine main_lemma_of_bad_bounds k s (kimM n k) (edgeProb_nonneg n)
    (by linarith [hN.edgeProb_le_half])
    (bad1_bound k s (kimM n k) hN h1 h2)
    (bad2_final k s hN hk' h2 h4)
    (bad3_bound k s (kimM n k) hN hk h1 h3)
    (bad4_final k s hN hk' h3 h4 h5)
    (bad5_final k s hN hk' h3 h4 h5)
    (bad6_final k s hN hk' h3 h4 h6)
    (bad7_final k s hN hk h1 h2 h3 h4 h5 h6 h7)
    (bad8_final k s hN hk h4 h5 h6 h7 h8) ?_
  -- `Σᵢ qᵢ ≤ 14/n < 1`
  have h2b : ((n : ℝ) ^ (2 : ℕ))⁻¹ ≤ 1 / n := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hnR]
    nlinarith [hn100]
  have h4b : 2 * ((Fintype.card (Edge V) : ℝ) * n) * ((n : ℝ) ^ (4 : ℕ))⁻¹
      ≤ 2 / n := by
    have hc : (0 : ℝ) ≤ ((n : ℝ) ^ (4 : ℕ))⁻¹ := by positivity
    have hEn := mul_le_mul_of_nonneg_right hE hnR.le
    have hstep : 2 * ((Fintype.card (Edge V) : ℝ) * n)
          * ((n : ℝ) ^ (4 : ℕ))⁻¹
        ≤ 2 * ((n : ℝ) * n * n) * ((n : ℝ) ^ (4 : ℕ))⁻¹ := by
      nlinarith [hEn, hc]
    have heq : 2 * ((n : ℝ) * n * n) * ((n : ℝ) ^ (4 : ℕ))⁻¹ = 2 / n := by
      field_simp
      try ring
    linarith [hstep, heq.le, heq.ge]
  have hfin : (14 : ℝ) / n < 1 := by
    rw [div_lt_one hnR]; linarith [hn100]
  have hsum : (1 : ℝ) / n + 1 / n + 3 / n + 2 / n + 1 / n + 1 / n + 4 / n
      + 1 / n = 14 / (n : ℝ) := by ring
  linarith [h2b, h4b, hfin, hsum.le, hsum.ge]

/-! ### Phase 5 — iterating the Main Lemma (Kim, proof of Theorem 1.1)

Kim sets `k₀ := ⌊n^δ/θ⌋ + 1` and applies Lemma 2.1 repeatedly to reach a
triangle-free `G_{k₀}` satisfying Property 8; (17) then forces `|𝒯_{k₀}| < 1`,
i.e. `𝒯_{k₀} = ∅`, i.e. `α(G_{k₀}) < t = ⌈9√(n log n)⌉`. -/

/-- **Iterating Lemma 2.1.** From a state satisfying the Properties at stage
`0`, we reach a state satisfying them at every stage `k ≤ ⌊n^δ/θ⌋`. -/
theorem iterate_main_lemma (hN : KimLarge n)
    (s₀ : BlockState V) (h₀ : Properties1to8 s₀ 0) :
    ∀ k : ℕ, k ≤ ⌊(n : ℝ) ^ ((1 : ℝ) / 17 - 10 ^ (-5 : ℤ)) / theta n⌋₊ →
      ∃ s : BlockState V, Properties1to8 s k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨s₀, h₀⟩
  | succ m ih =>
      intro hk
      have hm : m ≤ ⌊(n : ℝ) ^ ((1 : ℝ) / 17 - 10 ^ (-5 : ℤ)) / theta n⌋₊ :=
        le_trans (Nat.le_succ m) hk
      obtain ⟨s, hs⟩ := ih hm
      obtain ⟨σ, hprops⟩ := main_lemma_2_1 m s hN hm hs
      exact ⟨blockStepP s (kimM n m) σ, hprops⟩

/-- **Kim, p. 9: "all properties are automatic for `i = 0`".**

For the initial triple `(ℰ₀, Γ₀, G₀) = (∅, E(Kₙ), ∅)` with `a₀ = 0`,
`b₀ = μ₀ = 1`, all eight properties hold. This is the base case of the
induction driven by `iterate_main_lemma`. -/
theorem properties1to8_init : Properties1to8 (initBlockState V) 0 :=
  ⟨property1_init, property2_init, property3_init, property4_init,
    property5_init, property6_init, property7_init, property8_init⟩

/-- **Consequence of the base case plus the Main Lemma**: a state satisfying
all eight properties exists at every stage `k ≤ ⌊n^δ/θ⌋`. -/
theorem exists_state_at (hN : KimLarge n) (k : ℕ)
    (hk : k ≤ ⌊(n : ℝ) ^ ((1 : ℝ) / 17 - 10 ^ (-5 : ℤ)) / theta n⌋₊) :
    ∃ s : BlockState V, Properties1to8 s k :=
  iterate_main_lemma hN (initBlockState V) properties1to8_init k hk

/-! ### Phase 6 — from the block construction to a triangle-free graph -/

/-- The simple graph whose edge set is `s.G`. -/
noncomputable def toGraph (s : BlockState V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ e ∈ s.G, u ∈ e.val ∧ v ∈ e.val
  symm := by
    rintro u v ⟨hne, e, he, hu, hv⟩
    exact ⟨hne.symm, e, he, hv, hu⟩
  loopless := by
    refine ⟨fun u hu => ?_⟩
    exact hu.1 rfl

open scoped Classical in
/-- **The block construction's graph is triangle-free.** A `3`-clique would
give three `G`-edges forming a triangle, which the `BlockState` invariant
forbids. -/
theorem toGraph_cliqueFree (s : BlockState V) : (toGraph s).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨hclique, hcard⟩ := ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  have hmem : ∀ x ∈ ({a, b, c} : Finset V), x ∈ ({a, b, c} : Finset V) :=
    fun x hx => hx
  have hA : (toGraph s).Adj a b :=
    hclique (by simp) (by simp) hab
  have hB : (toGraph s).Adj b c :=
    hclique (by simp) (by simp) hbc
  have hC : (toGraph s).Adj a c :=
    hclique (by simp) (by simp) hac
  obtain ⟨-, eab, heab, haab, hbab⟩ := hA
  obtain ⟨-, ebc, hebc, hbbc, hcbc⟩ := hB
  obtain ⟨-, eac, heac, haac, hcac⟩ := hC
  refine s.hG_triangle_free eab heab ebc hebc eac heac ?_
  exact ⟨a, b, c, hab, hbc, hac,
    edge_eq_of_two_mem haab hbab hab,
    edge_eq_of_two_mem hbbc hcbc hbc,
    edge_eq_of_two_mem haac hcac hac⟩

open scoped Classical in
/-- An independent set in `toGraph s` spans no `G`-edge. -/
lemma isIndepSet_iff {s : BlockState V} {I : Finset V} :
    (toGraph s).IsIndepSet (↑I : Set V) ↔
      ∀ e ∈ s.G, ¬ (∃ v ∈ I, ∃ w ∈ I, v ≠ w ∧ v ∈ e.val ∧ w ∈ e.val) := by
  classical
  constructor
  · intro hI e he ⟨v, hv, w, hw, hvw, hve, hwe⟩
    exact hI (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hw) hvw
      ⟨hvw, e, he, hve, hwe⟩
  · intro h u hu v hv huv hadj
    obtain ⟨-, e, he, hue, hve⟩ := hadj
    exact h e he ⟨u, Finset.mem_coe.mp hu, v, Finset.mem_coe.mp hv,
      huv, hue, hve⟩

open scoped Classical in
/-- **`𝒯 = ∅` bounds the independence number.** If no `t`-set is free of
`G`-edges then every independent set has fewer than `t` vertices. -/
theorem card_lt_tParam_of_calT_empty (s : BlockState V) (h : calT s = ∅)
    {I : Finset V} (hI : (toGraph s).IsIndepSet (↑I : Set V)) :
    I.card < tParam n := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcon
  have hTmem : T ∈ calT s := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTcard, fun e he => ?_⟩
    rintro ⟨v, hv, w, hw, hvw, hve, hwe⟩
    exact (isIndepSet_iff.mp hI) e he
      ⟨v, hTsub hv, w, hTsub hw, hvw, hve, hwe⟩
  rw [h] at hTmem
  exact absurd hTmem (Finset.notMem_empty T)

/-- If the `𝒯`-count is `< 1` then `𝒯` is empty (a `Finset` card is a
natural number). This is how Kim's (17) is used. -/
lemma calT_empty_of_card_lt_one (s : BlockState V)
    (h : ((calT s).card : ℝ) < 1) : calT s = ∅ := by
  have : (calT s).card = 0 := by
    by_contra hc
    have h1 : 1 ≤ (calT s).card := Nat.one_le_iff_ne_zero.mpr hc
    have : (1 : ℝ) ≤ ((calT s).card : ℝ) := by exact_mod_cast h1
    linarith
  exact Finset.card_eq_zero.mp this
/-- **(15) over `range k`.** Terms are nonnegative, so the bound for
`range (k+1)` dominates. -/
lemma sum_aSeq_bSeq_range_le (N k : ℕ) :
    ∑ j ∈ Finset.range k, aSeq N j * bSeq N j * theta N
      ≤ spencerPsi ((k : ℝ) * theta N) ^ 2 / 2
        + (3 / 2) * theta N * spencerPsi ((k : ℝ) * theta N) := by
  refine le_trans ?_ (sum_aSeq_bSeq_le N k)
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (fun x hx => Finset.mem_range.mpr
      (lt_trans (Finset.mem_range.mp hx) (Nat.lt_succ_self k))) ?_
  intro j _ _
  exact mul_nonneg (mul_nonneg (aSeq_nonneg N j) (bSeq_pos N j).le)
    (theta_nonneg N)

/-- **(15) in logarithmic form**, via (16) `Ψ(x) ≤ √(log x) + 1`.

`θ∑_{j<k} a_jb_j ≤ (log x + 2√(log x) + 1)/2 + (3/2)θ(√(log x) + 1)`,
where `x = kθ`. Kim writes this as `(1/2 + θ^{1/5})log x`; the `θ^{1/5}log x`
slack absorbs the `√(log x)` terms because `θ = (log n)^{-2}` makes
`θ^{1/5}log x` of order `(log n)^{3/5}`, beating `(log n)^{1/2}`. -/
lemma sum_aSeq_bSeq_le_log (N k : ℕ) (hk : 1 ≤ (k : ℝ) * theta N) :
    ∑ j ∈ Finset.range k, aSeq N j * bSeq N j * theta N
      ≤ (Real.log ((k : ℝ) * theta N)
            + 2 * Real.sqrt (Real.log ((k : ℝ) * theta N)) + 1) / 2
        + (3 / 2) * theta N
          * (Real.sqrt (Real.log ((k : ℝ) * theta N)) + 1) := by
  set x : ℝ := (k : ℝ) * theta N with hx
  have hΨ : spencerPsi x ≤ Real.sqrt (Real.log x) + 1 :=
    spencerPsi_le_sqrt_log_add_one hk
  have hΨ0 : 0 ≤ spencerPsi x :=
    spencerPsi_nonneg (by linarith)
  have hsqrt0 : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have hθ : 0 ≤ theta N := theta_nonneg N
  have hsq : Real.sqrt (Real.log x) ^ 2 = Real.log x :=
    Real.sq_sqrt (Real.log_nonneg hk)
  refine le_trans (sum_aSeq_bSeq_range_le N k) ?_
  have h1 : spencerPsi x ^ 2 / 2
      ≤ (Real.log x + 2 * Real.sqrt (Real.log x) + 1) / 2 := by
    nlinarith [hΨ, hΨ0, hsqrt0, hsq]
  have h2 : (3 / 2) * theta N * spencerPsi x
      ≤ (3 / 2) * theta N * (Real.sqrt (Real.log x) + 1) := by
    refine mul_le_mul_of_nonneg_left hΨ ?_
    linarith
  linarith

/-- **Kim's decomposition of `θ∑ b_jμ_j`** (the first display in his proof
of (17)):

`θ∑_{j<k} b_jμ_j = a_k − 18θ·(θ∑ a_jb_j) − (3√log n)⁻¹·(θ∑ a_jb_j)`,

using `θ∑_{j<k} b_j = a_k` — which is the *definition* of `a_k`. -/
lemma sum_bSeq_mul_μSeq (N k : ℕ) :
    ∑ j ∈ Finset.range k, bSeq N j * μSeq N j * theta N
      = aSeq N k
        - 18 * theta N
          * (∑ j ∈ Finset.range k, aSeq N j * bSeq N j * theta N)
        - (1 / (3 * Real.sqrt (Real.log N)))
          * (∑ j ∈ Finset.range k, aSeq N j * bSeq N j * theta N) := by
  rw [aSeq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [μSeq]
  ring

/-- **Kim's lower bound on `θ∑ b_jμ_j`.** Combining the decomposition with an
upper bound `S` on `θ∑ a_jb_j` (Kim's (15)). -/
lemma sum_bSeq_mul_μSeq_ge (N k : ℕ) {S : ℝ}
    (hS : ∑ j ∈ Finset.range k, aSeq N j * bSeq N j * theta N ≤ S)
    (hθ : 0 ≤ theta N) (hlog : 0 ≤ Real.sqrt (Real.log N)) :
    aSeq N k - (18 * theta N + 1 / (3 * Real.sqrt (Real.log N))) * S
      ≤ ∑ j ∈ Finset.range k, bSeq N j * μSeq N j * theta N := by
  rw [sum_bSeq_mul_μSeq]
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range k, aSeq N j * bSeq N j * theta N :=
    Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (aSeq_nonneg N j) (bSeq_pos N j).le) hθ
  have h1 : 18 * theta N
        * (∑ j ∈ Finset.range k, aSeq N j * bSeq N j * theta N)
      ≤ 18 * theta N * S :=
    mul_le_mul_of_nonneg_left hS (by linarith)
  have h2 : (1 / (3 * Real.sqrt (Real.log N)))
        * (∑ j ∈ Finset.range k, aSeq N j * bSeq N j * theta N)
      ≤ (1 / (3 * Real.sqrt (Real.log N))) * S := by
    refine mul_le_mul_of_nonneg_left hS ?_
    positivity
  linarith

/-- **Kim's (11), lower half**: `a_k ≥ √(log(kθ)) − 1`, via `Ψ(kθ) ≤ a_k`
and (16). -/
lemma aSeq_ge_sqrt_log (N k : ℕ) (hk : 1 ≤ (k : ℝ) * theta N) :
    Real.sqrt (Real.log ((k : ℝ) * theta N)) - 1 ≤ aSeq N k :=
  le_trans (spencerPsi_ge_sqrt_log_sub_one hk) (spencerPsi_le_aSeq N k)

/-- **Kim's lower bound on `θ∑_{j<k} b_jμ_j`**, assembled from (11) and (15).

`θ∑ b_jμ_j ≥ √(log x) − 1 − (18θ + (3√log n)⁻¹)·S`, where `x = kθ` and `S` is
the (15) bound on `θ∑ a_jb_j`. With `x ≈ n^δ` the leading term is
`√(δ log n)` and the correction is `≈ δ√(log n)/6`, leaving Kim's
`0.23√(log n)`. -/
theorem sum_bSeq_mul_μSeq_lower (N k : ℕ) (hk : 1 ≤ (k : ℝ) * theta N) :
    Real.sqrt (Real.log ((k : ℝ) * theta N)) - 1
        - (18 * theta N + 1 / (3 * Real.sqrt (Real.log N)))
          * ((Real.log ((k : ℝ) * theta N)
                + 2 * Real.sqrt (Real.log ((k : ℝ) * theta N)) + 1) / 2
              + (3 / 2) * theta N
                * (Real.sqrt (Real.log ((k : ℝ) * theta N)) + 1))
      ≤ ∑ j ∈ Finset.range k, bSeq N j * μSeq N j * theta N := by
  have hθ : 0 ≤ theta N := theta_nonneg N
  have hlog : 0 ≤ Real.sqrt (Real.log N) := Real.sqrt_nonneg _
  refine le_trans ?_ (sum_bSeq_mul_μSeq_ge N k (sum_aSeq_bSeq_le_log N k hk)
    hθ hlog)
  have ha := aSeq_ge_sqrt_log N k hk
  linarith

/-- **`ε = (log log n)^{−1/4} → 0`.** The final comparison in (17) needs
`ε < 0.0338`; we prove the stronger `ε ≤ 1/1000`, which costs nothing since
everything is `Eventually`. -/
lemma eventually_kimEps_le :
    ∀ᶠ N : ℕ in Filter.atTop, kimEps N ≤ 1 / 1000 := by
  filter_upwards [tendsto_loglog_atTop.eventually_ge_atTop ((10 : ℝ) ^ 12)]
    with N hN
  have h0 : (0 : ℝ) < Real.log (Real.log N) := by
    have : (0 : ℝ) < (10 : ℝ) ^ 12 := by positivity
    linarith
  rw [kimEps, show -(1 : ℝ) / 4 = -((1 : ℝ) / 4) by ring,
    Real.rpow_neg h0.le]
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  have hbase : ((10 : ℝ) ^ 12) ^ ((1 : ℝ) / 4)
      ≤ (Real.log (Real.log N)) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (by positivity) hN (by norm_num)
  refine le_trans ?_ hbase
  rw [show ((10 : ℝ) ^ 12) = ((1000 : ℝ)) ^ (4 : ℕ) by norm_num,
    ← Real.rpow_natCast (1000 : ℝ) 4, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `C(t,2) = t(t−1)/2` over `ℝ`. -/
lemma choose_two_real {t : ℕ} (ht : 1 ≤ t) :
    ((t.choose 2 : ℕ) : ℝ) = (t : ℝ) * ((t : ℝ) - 1) / 2 := by
  have hnat : 2 * t.choose 2 = t * (t - 1) := by
    rw [Nat.choose_two_right]
    obtain ⟨m, hm⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
    subst hm
    simp only [Nat.add_sub_cancel]
    obtain ⟨c, hc⟩ := Nat.even_mul_succ_self m
    have hmul : (m + 1) * m = 2 * c := by rw [Nat.mul_comm]; omega
    rw [hmul]
    omega
  have hcast : (2 : ℝ) * ((t.choose 2 : ℕ) : ℝ) = (t : ℝ) * ((t : ℝ) - 1) := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) hnat
    push_cast [Nat.cast_sub ht] at h
    linarith [h]
  linarith [hcast]

/-- `t ≥ 9√(n log n)`. -/
lemma tParam_ge_bound (N : ℕ) :
    9 * Real.sqrt ((N : ℝ) * Real.log N) ≤ (tParam N : ℝ) := by
  rw [tParam]; exact Nat.le_ceil _

/-- **The slack condition of (17)**: `k₀·L + 2.003L + 1 ≤ 0.022·√n·L^{3/2}`.
Since `k₀ ≤ n^δ·L²` and `δ < 1/2`, the `k₀·L` term is `o(√n·L^{3/2})`. -/
lemma eventually_ineq17_slack :
    ∀ᶠ N : ℕ in Filter.atTop,
      (kimK0 N : ℝ) * Real.log N + 2003 / 1000 * Real.log N + 1
        ≤ 22 / 1000 * (Real.sqrt N * (Real.sqrt (Real.log N)) ^ 3) := by
  have hr : (0 : ℝ) < 1 / 2 - kimDelta := by
    have h := kimDelta_lt; norm_num at h ⊢; linarith
  have h1 := eventually_polylog_le_rpow (r := (1:ℝ)/2 - kimDelta)
    (c := 11 / 1000) (K := 1) hr (by norm_num) (by norm_num) 2
  have h2 := eventually_polylog_le_rpow (r := (1:ℝ)/2) (c := 11/4000)
    (K := 1) (by norm_num) (by norm_num) (by norm_num) 0
  filter_upwards [h1, h2, eventually_log_ge 1, Filter.eventually_ge_atTop 1]
    with N h1' h2' hL h1N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast h1N
  set L : ℝ := Real.log N with hLdef
  have hL1 : (1 : ℝ) ≤ L := hL
  set sL : ℝ := Real.sqrt L with hsLdef
  have hsL0 : (0 : ℝ) < sL := Real.sqrt_pos.mpr (by linarith)
  have hsLsq : sL ^ 2 = L := Real.sq_sqrt (by linarith)
  have hsL1 : (1 : ℝ) ≤ sL := by nlinarith [hsLsq, hsL0, hL1]
  have hsN : Real.sqrt (N : ℝ) = (N : ℝ) ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow _
  have hsN0 : (0 : ℝ) < Real.sqrt (N : ℝ) := by
    rw [hsN]; exact Real.rpow_pos_of_pos hNpos _
  have hL0 : (0 : ℝ) < L := by linarith
  have hθpos : 0 < theta N := by
    rw [theta, ← hLdef]; exact div_pos one_pos (pow_pos hL0 2)
  -- `k₀ ≤ n^δ·L²`
  have hk0 : (kimK0 N : ℝ) ≤ (N : ℝ) ^ kimDelta * L ^ 2 := by
    have h := (kimK0_theta_bounds (N := N) hθpos).1
    have hθ : theta N = 1 / L ^ 2 := by rw [hLdef, theta]
    rw [hθ] at h
    have hL2 : (0:ℝ) < L ^ 2 := pow_pos hL0 2
    have hmul : (kimK0 N : ℝ) * (1 / L ^ 2) * L ^ 2 ≤ (N : ℝ) ^ kimDelta * L ^ 2 :=
      mul_le_mul_of_nonneg_right h (le_of_lt hL2)
    calc (kimK0 N : ℝ) = (kimK0 N : ℝ) * (1 / L ^ 2) * L ^ 2 := by
          field_simp
      _ ≤ (N : ℝ) ^ kimDelta * L ^ 2 := hmul
  -- split `n^δ = n^{1/2}·n^{δ−1/2}`
  have hsplit : (N : ℝ) ^ kimDelta * ((N : ℝ) ^ ((1:ℝ)/2 - kimDelta))
      = (N : ℝ) ^ ((1:ℝ)/2) := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hA : (kimK0 N : ℝ) * L ≤ 11 / 1000 * (Real.sqrt N * (sL ^ 3)) := by
    have hstep : (N : ℝ) ^ kimDelta * L ^ 2 * L
        ≤ (N : ℝ) ^ kimDelta * (11 / 1000 * (N : ℝ) ^ ((1:ℝ)/2 - kimDelta)) * L := by
      have hp : (0 : ℝ) < (N : ℝ) ^ kimDelta := Real.rpow_pos_of_pos hNpos _
      have := h1'
      simp only [one_mul] at this
      nlinarith [this, hp, hL1]
    have heq : (N : ℝ) ^ kimDelta * (11 / 1000 * (N : ℝ) ^ ((1:ℝ)/2 - kimDelta)) * L
        = 11 / 1000 * (Real.sqrt N * L) := by
      rw [hsN]
      rw [show (N : ℝ) ^ kimDelta * (11 / 1000 * (N : ℝ) ^ ((1:ℝ)/2 - kimDelta))
          = 11 / 1000 * ((N : ℝ) ^ kimDelta * (N : ℝ) ^ ((1:ℝ)/2 - kimDelta))
          by ring, hsplit]
      ring
    have hfin : 11 / 1000 * (Real.sqrt N * L)
        ≤ 11 / 1000 * (Real.sqrt N * sL ^ 3) := by
      have : L ≤ sL ^ 3 := by nlinarith [hsLsq, hsL1, hsL0]
      nlinarith [this, hsN0]
    nlinarith [hk0, hstep, heq, hfin, hL1]
  have hB : 2003 / 1000 * L + 1 ≤ 11 / 1000 * (Real.sqrt N * sL ^ 3) := by
    have hbig : (4000 : ℝ) / 11 ≤ Real.sqrt (N : ℝ) := by
      rw [hsN]
      have := h2'
      simp only [pow_zero, mul_one] at this
      linarith [this]
    have hcube : L ≤ sL ^ 3 := by nlinarith [hsLsq, hsL1, hsL0]
    nlinarith [hbig, hcube, hL1, hsL1, hsL0]
  linarith [hA, hB]

/-- **The final comparison of Kim's (17)**, over plain reals.

`sN = √n`, `sL = √L`, `t ≈ 9·sN·sL`, `C = C(t,2)`. The right side is
`≈ 9.03·sN·sL³` and the left `≈ 9·sN·sL³`, so the `0.022·sN·sL³` of slack is
what the hypothesis `hk` must absorb. -/
lemma ineq17_core {L sN sL k t C Sm eps : ℝ}
    (hL : 160000 ≤ L) (hsL : sL ^ 2 = L) (hsL0 : 0 < sL) (hsN1 : 1 ≤ sN)
    (ht_lo : 9 * sN * sL ≤ t) (ht_hi : t ≤ 9 * sN * sL + 1)
    (hC : C = t * (t - 1) / 2)
    (hSm : 223 / 1000 * sL ≤ Sm)
    (heps : eps ≤ 1 / 1000) (heps0 : 0 ≤ eps)
    (hk : k * L + 2003 / 1000 * L + 1 ≤ 22 / 1000 * (sN * sL ^ 3)) :
    k * L + t * L < (1 - eps) * ((C / sN) * Sm) := by
  have hsN0 : (0 : ℝ) < sN := by linarith
  have hsL400 : (400 : ℝ) ≤ sL := by nlinarith [hsL, hsL0, hL]
  have hT1 : (1 : ℝ) ≤ 9 * sN * sL := by nlinarith [hsN1, hsL400]
  have ht0 : (0 : ℝ) < t := by linarith
  -- `t² − t ≥ 81 sN² sL² − 9 sN sL`, since `x ↦ x²−x` is increasing past `1/2`
  have hkey : 81 * sN ^ 2 * sL ^ 2 - 9 * sN * sL ≤ t ^ 2 - t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht_lo)
      (by linarith : (0:ℝ) ≤ t + 9 * sN * sL - 1)]
  have hCbound : (81 * sN * sL ^ 2 - 9 * sL) / 2 ≤ C / sN := by
    rw [hC, div_le_div_iff₀ (by norm_num) hsN0]
    nlinarith [hkey, hsN0]
  have hCnn : (0 : ℝ) ≤ C / sN := by
    refine le_trans ?_ hCbound
    nlinarith [hT1, hsL0, hsN0]
  have hSm0 : (0 : ℝ) ≤ Sm := by nlinarith [hSm, hsL0]
  have hprod : (223 / 1000 * sL) * ((81 * sN * sL ^ 2 - 9 * sL) / 2)
      ≤ (C / sN) * Sm := by
    have h1 : (223 / 1000 * sL) * ((81 * sN * sL ^ 2 - 9 * sL) / 2)
        ≤ (223 / 1000 * sL) * (C / sN) :=
      mul_le_mul_of_nonneg_left hCbound (by positivity)
    have h2 : (223 / 1000 * sL) * (C / sN) ≤ (C / sN) * Sm := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hSm hCnn
    linarith
  have hbase0 : (0 : ℝ)
      ≤ (223 / 1000 * sL) * ((81 * sN * sL ^ 2 - 9 * sL) / 2) := by
    nlinarith [hT1, hsL0, hsN0]
  have hCSm0 : (0 : ℝ) ≤ (C / sN) * Sm := mul_nonneg hCnn hSm0
  have hdisc : (999 / 1000) * ((223 / 1000 * sL)
      * ((81 * sN * sL ^ 2 - 9 * sL) / 2)) ≤ (1 - eps) * ((C / sN) * Sm) := by
    have h1 : (999 / 1000) * ((223 / 1000 * sL)
        * ((81 * sN * sL ^ 2 - 9 * sL) / 2))
        ≤ (999 / 1000) * ((C / sN) * Sm) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    have h2 : (999 / 1000) * ((C / sN) * Sm) ≤ (1 - eps) * ((C / sN) * Sm) :=
      mul_le_mul_of_nonneg_right (by linarith) hCSm0
    linarith
  have hLHS : k * L + t * L ≤ k * L + 9 * (sN * sL ^ 3) + L := by
    have hLsL : L = sL ^ 2 := hsL.symm
    nlinarith [ht_hi, hsL0, hsL400, hLsL, hsN0]
  have hRHS : k * L + 9 * (sN * sL ^ 3) + L
      < (999 / 1000) * ((223 / 1000 * sL)
        * ((81 * sN * sL ^ 2 - 9 * sL) / 2)) := by
    have hexp : (999 / 1000) * ((223 / 1000 * sL)
        * ((81 * sN * sL ^ 2 - 9 * sL) / 2))
        = (999 * 223 * 81 / 2000000) * (sN * sL ^ 3)
          - (999 * 223 * 9 / 2000000) * sL ^ 2 := by ring
    rw [hexp, ← hsL]
    nlinarith [hk, hsL0, hsN0, hsL400]
  linarith [hLHS, hRHS, hdisc]

/-- **Kim's `θ∑_{j<k₀} b_jμ_j ≥ 0.223√(log n)`**, the first half of (17). -/
theorem eventually_sum_bmu_ge :
    ∀ᶠ N : ℕ in Filter.atTop,
      (223 : ℝ) / 1000 * Real.sqrt (Real.log N)
        ≤ ∑ j ∈ Finset.range (kimK0 N), bSeq N j * μSeq N j * theta N := by
  have hrpow : ∀ᶠ N : ℕ in Filter.atTop, (2 : ℝ) ≤ (N : ℝ) ^ kimDelta := by
    have h := eventually_polylog_le_rpow (r := kimDelta) (c := 1) (K := 2)
      kimDelta_pos (by norm_num) (by norm_num) 0
    filter_upwards [h] with N hN; simpa using hN
  filter_upwards [eventually_log_ge 160000, hrpow,
    eventually_theta_le 1 (by norm_num), Filter.eventually_ge_atTop 1]
    with N hL hrp hθ1 h1N
  set L : ℝ := Real.log N with hLdef
  have hL0 : (0 : ℝ) < L := by linarith
  have hθdef : theta N = 1 / L ^ 2 := by rw [theta, hLdef]
  have hθpos : 0 < theta N := by rw [hθdef]; positivity
  set s : ℝ := Real.sqrt L with hsdef
  have hs0 : (0 : ℝ) < s := Real.sqrt_pos.mpr hL0
  have hssq : s ^ 2 = L := Real.sq_sqrt hL0.le
  have hs400 : (400 : ℝ) ≤ s := by nlinarith [hssq, hs0, hL]
  -- the block index and its `log`
  obtain ⟨hup, hlo⟩ := kimK0_theta_bounds (N := N) hθpos
  have hx1 : (1 : ℝ) ≤ (kimK0 N : ℝ) * theta N := by linarith
  obtain ⟨hu1, hu2⟩ := log_kimK0_theta_bounds hθpos h1N (by linarith)
  rw [← hLdef] at hu1 hu2
  set u : ℝ := Real.log ((kimK0 N : ℝ) * theta N) with hudef
  have hδlo : (1 : ℝ) / 20 ≤ kimDelta := by rw [kimDelta_val]; norm_num
  have hu0 : (0 : ℝ) < u := by
    have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    nlinarith [hu1, hδlo, hL, hlog2]
  set r : ℝ := Real.sqrt u with hrdef
  have hr0 : (0 : ℝ) < r := Real.sqrt_pos.mpr hu0
  set sd : ℝ := Real.sqrt kimDelta with hsddef
  have hsdsq : sd ^ 2 = kimDelta := Real.sq_sqrt kimDelta_pos.le
  have hsd : (2424 : ℝ) / 10000 ≤ sd := sqrt_kimDelta_ge
  have hsd1 : sd ≤ 1 := by
    nlinarith [hsdsq, Real.sqrt_nonneg kimDelta, le_of_lt kimDelta_lt]
  have hsdL : sd * s = Real.sqrt (kimDelta * L) := by
    rw [hsddef, hsdef, ← Real.sqrt_mul kimDelta_pos.le]
  -- `√u ≤ √δ·s` and `√δ·s − 1 ≤ √u`
  have hrup : r ≤ sd * s := by
    rw [hsdL, hrdef]
    exact Real.sqrt_le_sqrt hu2
  have hrlo : sd * s - 1 ≤ r := by
    have hδLsq : Real.sqrt (kimDelta * L) ^ 2 = kimDelta * L :=
      Real.sq_sqrt (by nlinarith [kimDelta_pos, hL0])
    have hbig : (2 : ℝ) ≤ Real.sqrt (kimDelta * L) := by
      nlinarith [hδLsq, Real.sqrt_nonneg (kimDelta * L), hsdL, hsd, hs400, hs0]
    have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    have hkey : (Real.sqrt (kimDelta * L) - 1) ^ 2 ≤ u := by
      nlinarith [hδLsq, hbig, hu1, hlog2]
    have := Real.sqrt_le_sqrt hkey
    rwa [Real.sqrt_sq (by linarith), ← hsdL] at this
  -- Kim's decomposition, then the core estimate
  have hSm := sum_bSeq_mul_μSeq_lower N (kimK0 N) hx1
  refine sum_bmu_core (s := s) (r := r) (sd := sd) (u := u)
    (θ := theta N) hs400 hsd hsd1 (by rw [hsdsq]; exact le_of_lt kimDelta_lt)
    (by rw [hθdef, hssq]) hr0 (by rw [hsdsq, hssq]; exact hu2) hrup hrlo ?_
  refine le_trans (le_of_eq ?_) hSm
  rw [hrdef, hudef]


/-- The Property-8 exponent factors as `(C(t,2)/√n)·∑_j b_jμ_jθ`. -/
lemma property8_exponent_factor (N k : ℕ) :
    ∑ j ∈ Finset.range k,
        bSeq N j * μSeq N j * theta N / Real.sqrt N * ((tParam N).choose 2)
      = (((tParam N).choose 2 : ℝ) / Real.sqrt N)
        * ∑ j ∈ Finset.range k, bSeq N j * μSeq N j * theta N := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- If `log a + log b < c` then `a·b·e^{−c} < 1`. -/
lemma mul_exp_neg_lt_one {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : Real.log a + Real.log b < c) : a * b * Real.exp (-c) < 1 := by
  have hab : a * b = Real.exp (Real.log a + Real.log b) := by
    rw [Real.exp_add, Real.exp_log ha, Real.exp_log hb]
  rw [hab, ← Real.exp_add]
  exact Real.exp_lt_one_iff.mpr (by linarith)

/-- `log C(N, t) ≤ t·log N`. -/
lemma log_choose_le {N t : ℕ} (hN : 0 < N) (ht : 0 < Nat.choose N t) :
    Real.log (Nat.choose N t) ≤ (t : ℝ) * Real.log N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : ((Nat.choose N t : ℕ) : ℝ) ≤ (N : ℝ) ^ t := by
    exact_mod_cast Nat.choose_le_pow N t
  have hchoose0 : (0 : ℝ) < (Nat.choose N t : ℕ) := by exact_mod_cast ht
  calc Real.log (Nat.choose N t) ≤ Real.log ((N : ℝ) ^ t) :=
        Real.log_le_log hchoose0 hle
    _ = (t : ℝ) * Real.log N := by rw [Real.log_pow]

/-- **Kim's (17), reduced to its logarithmic form.**

`n^{k₀}C(n,t)exp(−(1−ε)S) < 1` follows from
`k₀ log n + t log n < (1−ε)·(C(t,2)/√n)·∑_j b_jμ_jθ`. -/
theorem ineq17_of_log (k₀ : ℕ) (hn : 0 < n)
    (hchoose : 0 < Nat.choose (Fintype.card V) (tParam n))
    (hlog : (k₀ : ℝ) * Real.log n + (tParam n : ℝ) * Real.log n
      < (1 - kimEps n) * ((((tParam n).choose 2 : ℝ) / Real.sqrt n)
          * ∑ j ∈ Finset.range k₀, bSeq n j * μSeq n j * theta n)) :
    (n : ℝ) ^ k₀ * (Nat.choose (Fintype.card V) (tParam n))
        * Real.exp (-(1 - kimEps n)
            * ∑ j ∈ Finset.range k₀,
                bSeq n j * μSeq n j * theta n / Real.sqrt n
                  * ((tParam n).choose 2))
      < 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hchooseR : (0 : ℝ) < (Nat.choose (Fintype.card V) (tParam n) : ℕ) := by
    exact_mod_cast hchoose
  rw [property8_exponent_factor]
  rw [show -(1 - kimEps n) * ((((tParam n).choose 2 : ℝ) / Real.sqrt n)
      * ∑ j ∈ Finset.range k₀, bSeq n j * μSeq n j * theta n)
      = -((1 - kimEps n) * ((((tParam n).choose 2 : ℝ) / Real.sqrt n)
        * ∑ j ∈ Finset.range k₀, bSeq n j * μSeq n j * theta n)) from by ring]
  refine mul_exp_neg_lt_one (by positivity) hchooseR ?_
  have hpow : Real.log ((n : ℝ) ^ k₀) = (k₀ : ℝ) * Real.log n := by
    rw [Real.log_pow]
  have hch := log_choose_le (N := Fintype.card V) (t := tParam n) hn hchoose
  rw [hpow]
  calc (k₀ : ℝ) * Real.log n
        + Real.log (Nat.choose (Fintype.card V) (tParam n))
      ≤ (k₀ : ℝ) * Real.log n + (tParam n : ℝ) * Real.log n := by
        linarith [hch]
    _ < _ := hlog

/-- **Kim's (17) in the form the proof consumes.** Once the Property-8 bound
drops below `1`, the family `𝒯` is empty — a `Finset` card is a natural
number. -/
theorem calT_empty_of_ineq17 (s : BlockState V) (k : ℕ) (h8 : Property8 s k)
    (h17 : (n : ℝ) ^ k * (Nat.choose (Fintype.card V) (tParam n))
        * Real.exp (-(1 - kimEps n)
            * ∑ j ∈ Finset.range k,
                bSeq n j * μSeq n j * theta n / Real.sqrt n
                  * ((tParam n).choose 2))
      < 1) :
    calT s = ∅ :=
  calT_empty_of_card_lt_one s (lt_of_le_of_lt h8 h17)

/-- **Kim's Theorem 1.1, in the form the block construction delivers it.**

Iterating the Main Lemma to stage `k₀` produces a triangle-free graph whose
independent sets all have fewer than `t = ⌈9√(n log n)⌉ ` vertices. -/
theorem exists_triangleFree_indep_lt (hN : KimLarge n) (k₀ : ℕ)
    (hk₀ : k₀ ≤ ⌊(n : ℝ) ^ ((1 : ℝ) / 17 - 10 ^ (-5 : ℤ)) / theta n⌋₊)
    (h17 : ∀ s : BlockState V, Property8 s k₀ → calT s = ∅) :
    ∃ G : SimpleGraph V, G.CliqueFree 3 ∧
      ∀ I : Finset V, G.IsIndepSet (↑I : Set V) → I.card < tParam n := by
  obtain ⟨s, hs⟩ := exists_state_at hN k₀ hk₀
  exact ⟨toGraph s, toGraph_cliqueFree s, fun I hI =>
    card_lt_tParam_of_calT_empty s (h17 s hs.2.2.2.2.2.2.2) hI⟩

end Phase3

/-! ## Phase 6 — Matching the signature

The headline theorem `Erdos610.KimProof.kim_theorem` reproduces the exact
statement shape of `Erdos610.kim_theorem`, which it discharges below.
-/

section Phase6

open scoped Classical in
/-- **Kim's Theorem 1.1**, in the exact shape of `kim_theorem`, given
his inequality (17).

For every sufficiently large `m` the block construction, run to stage `k₀`,
produces a triangle-free graph on `Fin m` whose independent sets all have fewer
than `t = ⌈9√(m log m)⌉` vertices; so `B = 9` works. -/
theorem kim_theorem_of_ineq17
    (h17 : ∀ᶠ m : ℕ in Filter.atTop, KimLarge (Fintype.card (Fin m)) ∧
      ∃ k₀ : ℕ,
        k₀ ≤ ⌊(Fintype.card (Fin m) : ℝ)
            ^ ((1 : ℝ) / 17 - 10 ^ (-5 : ℤ))
            / theta (Fintype.card (Fin m))⌋₊ ∧
        ∀ s : BlockState (Fin m), Property8 s k₀ → calT s = ∅) :
    ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ m ≥ N₀,
      ∃ G : SimpleGraph (Fin m),
        G.CliqueFree 3 ∧ ∀ I : Finset (Fin m),
          G.IsIndepSet (↑I : Set (Fin m)) →
            (I.card : ℝ) ≤ B * Real.sqrt ((m : ℝ) * Real.log m) := by
  classical
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h17
  refine ⟨9, by norm_num, N₀, fun m hm => ?_⟩
  obtain ⟨hlarge, k₀, hk₀, hcal⟩ := hN₀ m hm
  obtain ⟨G, hfree, hindep⟩ :=
    exists_triangleFree_indep_lt (V := Fin m) hlarge k₀ hk₀ hcal
  refine ⟨G, hfree, fun I hI => ?_⟩
  have hlt := hindep I hI
  -- `t = ⌈9√(m log m)⌉`, so `|I| < t` gives `|I| < 9√(m log m)`
  have hcard : (I.card : ℝ)
      < 9 * Real.sqrt ((Fintype.card (Fin m) : ℝ)
          * Real.log (Fintype.card (Fin m))) := by
    have := Nat.lt_ceil.mp (by rw [tParam] at hlt; exact hlt)
    exact this
  rw [Fintype.card_fin] at hcard
  exact hcard.le

/-- **Kim's inequality (17) in logarithmic form**, for all large `N`:
`k₀ log n + t log n < (1−ε)·(C(t,2)/√n)·∑ⱼ bⱼμⱼθ`. -/
lemma eventually_ineq17_log :
    ∀ᶠ N : ℕ in Filter.atTop,
      (kimK0 N : ℝ) * Real.log N + (tParam N : ℝ) * Real.log N
        < (1 - kimEps N) * ((((tParam N).choose 2 : ℝ) / Real.sqrt N)
            * ∑ j ∈ Finset.range (kimK0 N), bSeq N j * μSeq N j * theta N) := by
  filter_upwards [eventually_log_ge 160000, eventually_sum_bmu_ge,
    eventually_kimEps_le, eventually_ineq17_slack,
    Filter.eventually_ge_atTop 1] with N hL hSm heps hslack h1N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast h1N
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hsN1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast h1N)
  have hsL0 : (0 : ℝ) < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have hsLsq : Real.sqrt (Real.log N) ^ 2 = Real.log N := Real.sq_sqrt hL0.le
  have heps0 : (0 : ℝ) ≤ kimEps N := by
    rw [kimEps]
    exact Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have ht1 : 1 ≤ tParam N := by
    have h := tParam_ge_bound N
    have hml : (0 : ℝ) < (N : ℝ) * Real.log N := mul_pos hNpos hL0
    have hs := Real.sqrt_pos.mpr hml
    have : (0 : ℝ) < (tParam N : ℝ) := by linarith
    exact_mod_cast this
  refine ineq17_core (L := Real.log N) (sN := Real.sqrt N)
    (sL := Real.sqrt (Real.log N)) (k := (kimK0 N : ℝ)) (t := (tParam N : ℝ))
    (C := (((tParam N).choose 2 : ℕ) : ℝ))
    (Sm := ∑ j ∈ Finset.range (kimK0 N), bSeq N j * μSeq N j * theta N)
    (eps := kimEps N) hL hsLsq hsL0 hsN1 ?_ (tParam_le_bound h1N)
    (choose_two_real ht1) hSm heps heps0 hslack
  have h := tParam_ge_bound N
  rwa [Real.sqrt_mul hNpos.le, ← mul_assoc] at h

/-- **Kim's inequality (17)**, in the form Phase 6 consumes: for all
sufficiently large `m` there is a block index `k₀ ≤ ⌊n^δ/θ⌋` at which the
Property-8 bound has dropped below `1`, forcing `𝒯 = ∅`.

Kim's §2 proof: `θ∑_{j<k₀} b_jμ_j ≥ 0.223√(log n)` by (15) and (11), whence
`k₀ log n + t log n < (1−ε)(C(t,2)/√n)·0.223√(log n)`. -/
theorem ineq17_eventually :
    ∀ᶠ m : ℕ in Filter.atTop, KimLarge (Fintype.card (Fin m)) ∧
      ∃ k₀ : ℕ,
        k₀ ≤ ⌊(Fintype.card (Fin m) : ℝ)
            ^ ((1 : ℝ) / 17 - 10 ^ (-5 : ℤ))
            / theta (Fintype.card (Fin m))⌋₊ ∧
        ∀ s : BlockState (Fin m), Property8 s k₀ → calT s = ∅ := by
  filter_upwards [eventually_kimLarge, eventually_ineq17_log] with m hlarge hlog
  have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
  have hm0 : 0 < m := by
    have h8 := hlarge.1
    have : (0 : ℝ) < (m : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨by rw [hcard]; exact hlarge, kimK0 m, ?_, ?_⟩
  · rw [hcard]; exact kimK0_le m
  · intro s h8
    refine calT_empty_of_ineq17 s (kimK0 m) h8 ?_
    refine ineq17_of_log (V := Fin m) (kimK0 m) (by rw [hcard]; exact hm0)
      (by rw [hcard]; exact hlarge.2.2.2.1) ?_
    rw [hcard]
    exact hlog

/-- **Theorem (Kim, 1995).** There is a `B > 0` such that for every
sufficiently large `n` some triangle-free graph on `n` vertices has every
independent set of size at most `B√(n log n)`.

This is the statement of `Erdos610.kim_theorem`, which is defined to be this
theorem. -/
theorem kim_theorem : ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ G : SimpleGraph (Fin n),
      G.CliqueFree 3 ∧ ∀ I : Finset (Fin n), G.IsIndepSet (↑I) →
        (I.card : ℝ) ≤ B * Real.sqrt (↑n * Real.log ↑n) :=
  kim_theorem_of_ineq17 ineq17_eventually

end Phase6

end KimProof

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Formalization of "A note on the clique-transversal number"

This file formalizes the paper resolving Erdős Problem #610, showing that
`T(n) = n - Θ(√(n log n))`, where `T(n)` is the maximum clique-transversal number
over all n-vertex graphs.

Let `τ(G)` denote the minimum size of a set of vertices meeting every maximal clique
of size at least 2 in a graph `G`. The paper proves:

- **Upper bound** (via clique colourings): `τ(G) ≤ n - c√(n log n)` for some `c > 0`
  and all sufficiently large `n`, using the JMRS bound on the clique chromatic number.
- **Lower bound** (from triangle-free graphs): `T(n) ≥ n - C√(n log n)` for some `C > 0`,
  using Kim's Ramsey-theoretic construction.

## References

* P. Erdős, T. Gallai, Zs. Tuza, "Covering the cliques of a graph with vertices" (1992)
* G. Joret, P. Micek, B. Reed, M. Smid, "Tight bounds on the clique chromatic number" (2021)
* J. H. Kim, "The Ramsey number R(3,t) has order of magnitude t²/log t" (1995)
-/

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Definitions -/

/-- A finset `S` is a **maximal clique of size ≥ 2** in graph `G`:
it is a clique, has at least 2 vertices, and no strict superset is a clique. -/
def IsMaxClique2 (G : SimpleGraph V) (S : Finset V) : Prop :=
  G.IsClique (↑S) ∧ 2 ≤ S.card ∧ ∀ T : Finset V, S ⊆ T → G.IsClique (↑T) → S = T

/-- A **clique transversal**: a set of vertices that meets every maximal clique of size ≥ 2. -/
def IsCliqueTransversal (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ S, IsMaxClique2 G S → (T ∩ S).Nonempty

/-- A **clique coloring** with `q` colors: no maximal clique of size ≥ 2 is monochromatic. -/
def IsCliqueColoring (G : SimpleGraph V) {q : ℕ} (c : V → Fin q) : Prop :=
  ∀ S, IsMaxClique2 G S → ∃ u ∈ S, ∃ v ∈ S, c u ≠ c v

/-- A **vertex cover**: a set of vertices that meets every edge. -/
def IsVertexCover (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T

/-! ## Section 3: The lower bound from triangle-free graphs -/

/-
In a triangle-free graph, if `u` and `v` are adjacent, then `{u, v}` is a maximal
clique of size 2. No third vertex can be adjacent to both (that would create a triangle).
-/
lemma triangleFree_edge_isMaxClique2 (G : SimpleGraph V)
    (hG : G.CliqueFree 3) {u v : V} (huv : G.Adj u v) :
    IsMaxClique2 G {u, v} := by
  refine' ⟨ _, _, _ ⟩;
  · simp +decide [ *, Set.Pairwise ];
  · rw [ Finset.card_pair huv.ne ];
  · intro T hT₁ hT₂; ext w; simp_all +decide [ Finset.subset_iff, SimpleGraph.isClique_iff ] ;
    contrapose! hG;
    simp +decide [ SimpleGraph.CliqueFree ];
    use {u, v, w};
    rw [ SimpleGraph.isNClique_iff ];
    rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> aesop

/-
In a triangle-free graph, every clique transversal is a vertex cover.
-/
lemma triangleFree_transversal_isVertexCover (G : SimpleGraph V)
    (hG : G.CliqueFree 3) (T : Finset V) (hT : IsCliqueTransversal G T) :
    IsVertexCover G T := by
  intro u v huv;
  exact hT { u, v } (( triangleFree_edge_isMaxClique2 G hG ) huv) |> fun ⟨ x, hx ⟩ => by aesop;

/-
The complement of a vertex cover is an independent set.
-/
lemma vertexCover_compl_isIndepSet (G : SimpleGraph V)
    (T : Finset V) (hT : IsVertexCover G T) :
    G.IsIndepSet (↑(univ \ T)) := by
  intro v hv w hw hvw; specialize hT v w; aesop;

/-
**Lemma 4c** (Triangle-free, transversal → independent set):
In a triangle-free graph, the complement of any clique transversal is an independent set.
-/
theorem triangleFree_transversal_gives_indep (G : SimpleGraph V)
    (hG : G.CliqueFree 3) (T : Finset V) (hT : IsCliqueTransversal G T) :
    G.IsIndepSet (↑(univ \ T)) := by
  exact vertexCover_compl_isIndepSet G T ( triangleFree_transversal_isVertexCover G hG T hT )

/-! ## Input theorems -/

/-- **JMRS clique-colouring input** (the one unproven ingredient).

A *clique colouring* assigns colours to vertices so that no maximal clique of
size ≥ 2 is monochromatic.  This is JMRS Corollary 2: every large
`n`-vertex graph has a clique colouring with `q ≤ A·√(n/log n)` colours.

The upper bound of Erdős 610 follows via `free_set_of_cliqueColoring_bound`:
the largest colour class of such a colouring is a free set of size
`≥ n/q ≥ √(n log n)/(2A)`, and the complement of a free set is exactly a
clique transversal.

Status: the only published route to this statement is JMRS Theorem 1
(`χ_c = O(Δ/log Δ)` for all graphs), whose proof does not go through as
written: the recolouring lists `L^v_u` enforce an invariant that costs `Ω(Δ)`
colours on line graphs. The triangle-free case *is*
proved, unconditionally, as `theorem1_triangleFree` in the same file (Molloy's
theorem: free = independent for triangle-free, plus the degree peel).  For
general graphs the statement remains open.

Note this assumes **strictly more** than the upper bound needs: the free-set
form derived below is implied by this colouring bound, but not conversely.

Reference: Joret, Micek, Reed, Smid, "Tight Bounds on the Clique Chromatic
Number", Electronic J. Combinatorics 28(3) (2021); Erdős–Gallai–Tuza,
"Covering the cliques of a graph with vertices", Discrete Math. 108 (1992)
(which gives the weaker `√(2n)` unconditionally). -/
axiom jmrs_corollary2 : ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ G : SimpleGraph (Fin n),
      ∃ q : ℕ, 0 < q ∧ (∃ c : Fin n → Fin q, IsCliqueColoring G c) ∧
        (q : ℝ) ≤ A * Real.sqrt (↑n / Real.log ↑n)

/-
**Pigeonhole principle** for color classes: if `V` is colored with `q > 0` colors,
some color class has size ≥ `|V| / q`.
-/
lemma exists_large_color_class {q : ℕ} (hq : 0 < q) (c : V → Fin q) :
    ∃ i : Fin q, Fintype.card V / q ≤ (univ.filter (fun v => c v = i)).card := by
  have h_pigeonhole : ∑ i : Fin q, Finset.card (Finset.filter (fun v => c v = i) Finset.univ) = Fintype.card V := by
    simp +decide only [card_filter];
    rw [ Finset.sum_comm ] ; simp +decide;
  contrapose! h_pigeonhole;
  exact ne_of_lt ( lt_of_lt_of_le ( Finset.sum_lt_sum_of_nonempty ⟨ ⟨ 0, hq ⟩, Finset.mem_univ _ ⟩ fun i _ => h_pigeonhole i ) ( by simp +decide [ mul_comm ] ; nlinarith [ Nat.div_mul_le_self ( Fintype.card V ) q ] ) )

/-- The JMRS clique-colouring bound yields a **free set** — a vertex set
containing no maximal clique of size ≥ 2, whose complement is exactly a
clique transversal: the largest colour class is such a set, of size
`≥ n/q ≥ √(n log n)/(2A)`.
Stated with the colouring bound as a hypothesis so that a future proof of
JMRS Corollary 2 can be plugged in directly. -/
theorem free_set_of_cliqueColoring_bound
    (h : ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ G : SimpleGraph (Fin n),
      ∃ q : ℕ, 0 < q ∧ (∃ c : Fin n → Fin q, IsCliqueColoring G c) ∧
        (q : ℝ) ≤ A * Real.sqrt (↑n / Real.log ↑n)) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ G : SimpleGraph (Fin n),
      ∃ S : Finset (Fin n), (∀ K, IsMaxClique2 G K → ¬ K ⊆ S) ∧
        c * Real.sqrt (↑n * Real.log ↑n) ≤ (S.card : ℝ) := by
  obtain ⟨A, hA_pos, N₀, h_coloring⟩ := h
  refine ⟨1 / (2 * A), by positivity, N₀ + ⌈(4 * A ^ 2)⌉₊ + 1, fun n hn G => ?_⟩
  obtain ⟨q, hq_pos, ⟨c, hc⟩, hq_bound⟩ := h_coloring n (by linarith) G
  obtain ⟨i, hi⟩ := exists_large_color_class hq_pos c
  refine ⟨univ.filter (fun v => c v = i), ?_, ?_⟩
  · intro K hK hsub
    obtain ⟨u, huK, v, hvK, huv⟩ := hc K hK
    have hu := hsub huK
    have hv := hsub hvK
    rw [Finset.mem_filter] at hu hv
    exact huv (hu.2.trans hv.2.symm)
  · -- `|class| ≥ n/q ≥ √(n log n)/A − 1 ≥ √(n log n)/(2A)`
    have h_floor : ((n / q : ℕ) : ℝ) ≥ Real.sqrt (n * Real.log n) / A - 1 := by
      have h_div : (n / q : ℝ) ≥ Real.sqrt (n * Real.log n) / A := by
        field_simp;
        convert mul_le_mul_of_nonneg_left hq_bound ( Real.sqrt_nonneg ( n * Real.log n ) ) using 1 ; ring;
        rw [ mul_assoc, ← Real.sqrt_mul ( by positivity ) ] ; ring_nf ; norm_num [ show n ≠ 0 by linarith, show Real.log n ≠ 0 by exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Nat.ceil_pos.mpr <| show 0 < 4 * A ^ 2 by positivity ] ] ; ring;
      exact le_trans ( sub_le_iff_le_add.mpr <| by linarith [ Nat.lt_floor_add_one <| ( n : ℝ ) / q, show ( n : ℝ ) / q ≤ ↑ ( n / q ) + 1 from by rw [ div_le_iff₀ <| Nat.cast_pos.mpr hq_pos ] ; norm_cast ; linarith [ Nat.div_add_mod n q, Nat.mod_lt n hq_pos ] ] ) le_rfl;
    have h_one_le : 1 ≤ Real.sqrt (n * Real.log n) / (2 * A) := by
      rw [ le_div_iff₀ ( by positivity ) ];
      refine' Real.le_sqrt_of_sq_le _;
      nlinarith [ Nat.le_ceil ( 4 * A ^ 2 ), show ( n : ℝ ) ≥ N₀ + ⌈4 * A ^ 2⌉₊ + 1 by exact_mod_cast hn, Real.log_inv ( n : ℝ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( show ( n : ℝ ) > 0 by norm_cast; linarith ) ), mul_inv_cancel₀ ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ), Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; linarith ) ];
    have hi' : n / q ≤ (univ.filter (fun v => c v = i)).card := by
      have hfin : Fintype.card (Fin n) = n := Fintype.card_fin n
      rwa [hfin] at hi
    have hcard : ((n / q : ℕ) : ℝ) ≤ ((univ.filter (fun v => c v = i)).card : ℝ) := by
      exact_mod_cast hi'
    calc 1 / (2 * A) * Real.sqrt (↑n * Real.log ↑n)
        = Real.sqrt (↑n * Real.log ↑n) / (2 * A) := by ring
      _ ≤ Real.sqrt (↑n * Real.log ↑n) / A - 1 := by
          have hApos : (0 : ℝ) < A := hA_pos
          have hs : (0 : ℝ) ≤ Real.sqrt (↑n * Real.log ↑n) := Real.sqrt_nonneg _
          have : Real.sqrt (↑n * Real.log ↑n) / (2 * A) + 1
              ≤ Real.sqrt (↑n * Real.log ↑n) / (2 * A)
                + Real.sqrt (↑n * Real.log ↑n) / (2 * A) := by linarith
          calc Real.sqrt (↑n * Real.log ↑n) / (2 * A)
              ≤ Real.sqrt (↑n * Real.log ↑n) / (2 * A)
                + (Real.sqrt (↑n * Real.log ↑n) / (2 * A) - 1) := by linarith
            _ = Real.sqrt (↑n * Real.log ↑n) / A - 1 := by ring
      _ ≤ ((n / q : ℕ) : ℝ) := h_floor
      _ ≤ _ := hcard

/-- **Theorem (Kim, 1995)**: There exists `B > 0` such that for all sufficiently large `n`,
there exists a triangle-free graph on `n` vertices where every independent set has size at
most `B √(n log n)`. This follows from Kim's lower bound `R(3,t) ≥ a · t² / log t`.

Reference: J. H. Kim, "The Ramsey number R(3,t) has order of magnitude t²/log t",
Random Structures & Algorithms 7(3) (1995), 173–207. -/
theorem kim_theorem : ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ G : SimpleGraph (Fin n),
      G.CliqueFree 3 ∧ ∀ I : Finset (Fin n), G.IsIndepSet (↑I) →
        (I.card : ℝ) ≤ B * Real.sqrt (↑n * Real.log ↑n) :=
  KimProof.kim_theorem

/-! ## Corollaries and main theorem -/

/-
**Corollary 3** (Upper bound): There exists `c > 0` such that for all sufficiently large `n`,
every `n`-vertex graph has a clique transversal of size at most `n - c√(n log n)`.
This follows from Lemma 2 and the JMRS theorem.

*Proof sketch*: By JMRS, `G` has a clique coloring with `q ≤ A√(n/log n)` colors.
By Lemma 2, `G` has a transversal of size `≤ n - n/q ≤ n - √(n log n)/A`.
-/
theorem upper_bound : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
    ∀ G : SimpleGraph (Fin n),
      ∃ T : Finset (Fin n), IsCliqueTransversal G T ∧
        (T.card : ℝ) ≤ ↑n - c * Real.sqrt (↑n * Real.log ↑n) := by
  obtain ⟨c, hc, N₀, h⟩ := free_set_of_cliqueColoring_bound jmrs_corollary2
  refine ⟨c, hc, N₀, fun n hn G => ?_⟩
  obtain ⟨S, hSfree, hScard⟩ := h n hn G
  refine ⟨Finset.univ \ S, ?_, ?_⟩
  · -- the complement of a free set meets every maximal clique
    intro K hK
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    refine hSfree K hK (fun v hv => ?_)
    by_contra hvS
    have hmem : v ∈ (Finset.univ \ S) ∩ K :=
      Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvS⟩, hv⟩
    rw [hemp] at hmem
    exact absurd hmem (Finset.notMem_empty v)
  · have hSn : S.card ≤ n := by
      calc S.card ≤ Finset.univ.card := Finset.card_le_univ S
        _ = n := by rw [Finset.card_univ, Fintype.card_fin]
    have hcard : (Finset.univ \ S).card = n - S.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
        Fintype.card_fin]
    rw [hcard, Nat.cast_sub hSn]
    linarith

/-
**Corollary 5** (Lower bound): There exists `C > 0` such that for all sufficiently large `n`,
there exists an `n`-vertex graph where every clique transversal has size ≥ `n - C√(n log n)`.
This follows from Lemma 4 and Kim's theorem.

*Proof sketch*: By Kim, there exists a triangle-free graph `G` with `α(G) ≤ B√(n log n)`.
For any transversal `T`, `V \ T` is independent (Lemma 4c), so `|V \ T| ≤ B√(n log n)`,
hence `|T| ≥ n - B√(n log n)`.
-/
theorem lower_bound : ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
    ∃ G : SimpleGraph (Fin n),
      ∀ T : Finset (Fin n), IsCliqueTransversal G T →
        (n : ℝ) - C * Real.sqrt (↑n * Real.log ↑n) ≤ ↑T.card := by
  obtain ⟨ B, hB₀, N, hN ⟩ := kim_theorem;
  use B, hB₀, N;
  intro n hn; obtain ⟨ G, hG₁, hG₂ ⟩ := hN n hn; use G; intro T hT; have := hG₂ ( Finset.univ \ T ) ; simp_all +decide [ Finset.card_sdiff ] ;
  rw [ Nat.cast_sub ] at this;
  · linarith [ this ( by simpa [ Set.diff_eq ] using triangleFree_transversal_gives_indep G hG₁ T hT ) ];
  · exact le_trans ( Finset.card_le_univ _ ) ( by norm_num )

/-- **Erdős Problem 610** ([EGT92; Er94; Er99], resolved). The clique-transversal
number `τ(G)` is the minimum size of a vertex set meeting every maximal clique of
`G` (excluding isolated vertices). Erdős asked whether every `n`-vertex graph
satisfies `τ(G) ≤ n − c√(n log n)` for some absolute `c > 0`; the answer is
**yes** and the rate is tight. This theorem proves both directions —
`T(n) = n − Θ(√(n log n))` — assuming only the Joret–Micek–Reed–Smid
clique-colouring bound (`jmrs_corollary2`), from which the free set the upper
bound needs is derived; Kim's lower bound on `R(3,t)` (`kim_theorem`) is
proved in full above, in `Erdos610.KimProof`. -/
theorem erdos_610 :
    (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n),
        ∃ T : Finset (Fin n), IsCliqueTransversal G T ∧
          (T.card : ℝ) ≤ ↑n - c * Real.sqrt (↑n * Real.log ↑n)) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : SimpleGraph (Fin n),
        ∀ T : Finset (Fin n), IsCliqueTransversal G T →
          (n : ℝ) - C * Real.sqrt (↑n * Real.log ↑n) ≤ ↑T.card) :=
  ⟨upper_bound, lower_bound⟩

#print axioms erdos_610
-- 'Erdos610.erdos_610' depends on axioms: [propext, Classical.choice, Erdos610.jmrs_corollary2, Quot.sound]

end Erdos610
