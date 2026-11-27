import Mathlib

namespace Erdos1147

/-
# Erdős Problem 1147

Let $\alpha > 0$ be an irrational number. Is the set
$$A = \left\{ n \geq 1 : \| \alpha n^2 \| < \frac{1}{\log n} \right\},$$
where $\|\cdot\|$ denotes the distance to the nearest integer, an additive basis of order $2$?

The answer is **no**: Konieczny [Ko16b] showed that it fails for almost every $\alpha > 0$, and
specifically for $\alpha = \sqrt{2}$. `erdos_1147` formalises the explicit counterexample
$\alpha = \sqrt{2}$, reading "additive basis of order $2$" as in Konieczny's paper: every
sufficiently large integer is a sum of exactly two elements of $A$, as in `formal-conjectures`.
`sqrtTwo_recSet_not_basis` proves more: for $\alpha = \sqrt{2}$, the set
$\{n \geq 1 : \|\sqrt{2} n^2\| \leq \epsilon(n)\}$ is not such a basis for any $\epsilon(n) \to 0$.

Formalised by Collin Yuanjie Ren in `CollinYuanjieRen/awards` (submission JSP-000952); the four
modules forming the closure of `erdos_1147` are flattened here in dependency order, with the
final theorem renamed from upstream `not_erdos_1147`.

Declarations that `erdos_1147` does not depend on have been removed.
-/

/-! ### Upstream module `Proof/Defs.lean` -/

/-!
# Erdős Problem 1147: definitions

For a real number `x`, `nd x` is the distance from `x` to the nearest integer (written `‖x‖` in
the literature).  A set `A ⊆ ℕ` is an *asymptotic additive basis of order 2* when every
sufficiently large natural number is a sum of two elements of `A` (Konieczny's convention for
"basis of order 2"; the reading "every positive integer" is vacuous for sets of positive integers,
since `1` is not a sum of two of them, and is therefore not used).  The set displayed in Erdős Problem 1147 is
`{n ≥ 1 : ‖α n²‖ < 1 / log n}`; the recurrence set with threshold function `ε` is
`{n ≥ 1 : ‖α n²‖ ≤ ε n}`.
-/

/-- Distance from `x` to the nearest integer. -/
noncomputable def nd (x : ℝ) : ℝ := |x - round x|

theorem nd_nonneg (x : ℝ) : 0 ≤ nd x := abs_nonneg _

/-- The nearest integer is at least as close as any other integer. -/
theorem nd_le_abs_sub_int (x : ℝ) (m : ℤ) : nd x ≤ |x - m| := by
  exact round_le x m

theorem nd_add_int (x : ℝ) (m : ℤ) : nd (x + m) = nd x := by
  rw [nd, nd, round_add_intCast]
  congr 1
  push_cast
  ring

/-- Reflecting a real number does not increase its distance to the nearest integer. -/
private theorem nd_neg_le (x : ℝ) : nd (-x) ≤ nd x := by
  have h : nd (-x) ≤ |(-x) - ((-round x : ℤ) : ℝ)| := nd_le_abs_sub_int (-x) (-round x)
  have key : |(-x) - ((-round x : ℤ) : ℝ)| = nd x := by
    rw [nd, ← abs_neg (x - (round x : ℝ))]
    congr 1
    push_cast
    ring
  rwa [key] at h

theorem nd_neg (x : ℝ) : nd (-x) = nd x := by
  refine le_antisymm (nd_neg_le x) ?_
  have h : nd (- -x) ≤ nd (-x) := nd_neg_le (-x)
  rwa [neg_neg] at h

theorem nd_add_le (x y : ℝ) : nd (x + y) ≤ nd x + nd y := by
  have h : nd (x + y) ≤ |x + y - ((round x + round y : ℤ) : ℝ)| :=
    nd_le_abs_sub_int (x + y) (round x + round y)
  have e : x + y - ((round x + round y : ℤ) : ℝ)
      = (x - (round x : ℝ)) + (y - (round y : ℝ)) := by
    push_cast
    ring
  rw [e] at h
  exact h.trans (abs_add_le _ _)

theorem nd_sub_le (x y : ℝ) : nd (x - y) ≤ nd x + nd y := by
  have h : nd (x + -y) ≤ nd x + nd (-y) := nd_add_le x (-y)
  rwa [← sub_eq_add_neg, nd_neg] at h

/-- `nd` is `1`-Lipschitz. -/
theorem nd_le_nd_add_abs_sub (x y : ℝ) : nd x ≤ nd y + |x - y| := by
  have h : nd x ≤ |x - (round y : ℝ)| := nd_le_abs_sub_int x (round y)
  have key : |x - (round y : ℝ)| ≤ |x - y| + |y - (round y : ℝ)| := abs_sub_le x y _
  have hy : nd y = |y - (round y : ℝ)| := rfl
  linarith

theorem nd_eq_zero_iff (x : ℝ) : nd x = 0 ↔ ∃ m : ℤ, x = m := by
  constructor
  · intro h
    rw [nd, abs_eq_zero, sub_eq_zero] at h
    exact ⟨round x, h⟩
  · rintro ⟨m, rfl⟩
    rw [nd, round_intCast, sub_self, abs_zero]

/-- Every integer is at distance at least `1 / 2` from `1 / 2`. -/
private theorem half_le_abs_half_sub_intCast (m : ℤ) : (1 : ℝ) / 2 ≤ |1 / 2 - (m : ℝ)| := by
  rcases le_or_gt m 0 with hm | hm
  · have hm' : (m : ℝ) ≤ 0 := by exact_mod_cast hm
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- Points of the form `1/2 + t` with `|t| ≤ 1/2` are at distance at least `1/2 - |t|`
from the integers. -/
theorem half_sub_abs_le_nd_half_add (t : ℝ) (ht : |t| ≤ 1 / 2) : 1 / 2 - |t| ≤ nd (1 / 2 + t) := by
  have hle : 0 ≤ 1 / 2 - |t| := by linarith
  have h1 : (1 : ℝ) / 2 ≤ |1 / 2 - ((round (1 / 2 + t) : ℤ) : ℝ)| :=
    half_le_abs_half_sub_intCast _
  have h2 : |1 / 2 - ((round (1 / 2 + t) : ℤ) : ℝ)|
      ≤ |1 / 2 + t - ((round (1 / 2 + t) : ℤ) : ℝ)| + |t| := by
    have e : (1 : ℝ) / 2 - ((round (1 / 2 + t) : ℤ) : ℝ)
        = (1 / 2 + t - ((round (1 / 2 + t) : ℤ) : ℝ)) + (-t) := by ring
    calc |1 / 2 - ((round (1 / 2 + t) : ℤ) : ℝ)|
        = |(1 / 2 + t - ((round (1 / 2 + t) : ℤ) : ℝ)) + (-t)| := by rw [e]
      _ ≤ |1 / 2 + t - ((round (1 / 2 + t) : ℤ) : ℝ)| + |(-t)| := abs_add_le _ _
      _ = |1 / 2 + t - ((round (1 / 2 + t) : ℤ) : ℝ)| + |t| := by rw [abs_neg]
  have h3 : nd (1 / 2 + t) = |1 / 2 + t - ((round (1 / 2 + t) : ℤ) : ℝ)| := rfl
  linarith

/-- For an odd integer `m`, `m / 2` differs from `1 / 2` by an integer. -/
theorem nd_odd_div_two_add (m : ℤ) (hm : Odd m) (t : ℝ) :
    nd ((m : ℝ) / 2 + t) = nd (1 / 2 + t) := by
  obtain ⟨k, rfl⟩ := hm
  have e : ((2 * k + 1 : ℤ) : ℝ) / 2 + t = (1 / 2 + t) + ((k : ℤ) : ℝ) := by
    push_cast
    ring
  rw [e]
  exact nd_add_int _ _

/-- Every sufficiently large natural number is a sum of two elements of `A`. -/
def IsAsymptoticBasis2 (A : Set ℕ) : Prop :=
  ∃ n₀ : ℕ, ∀ m : ℕ, n₀ ≤ m → ∃ a ∈ A, ∃ b ∈ A, a + b = m

theorem IsAsymptoticBasis2.mono {A B : Set ℕ} (hAB : A ⊆ B) (hA : IsAsymptoticBasis2 A) :
    IsAsymptoticBasis2 B := by
  obtain ⟨n₀, h⟩ := hA
  exact ⟨n₀, fun m hm => by
    obtain ⟨a, ha, b, hb, hab⟩ := h m hm
    exact ⟨a, hAB ha, b, hAB hb, hab⟩⟩

/-- The recurrence set `{n ≥ 1 : ‖α n²‖ ≤ ε n}`. -/
def recSet (α : ℝ) (ε : ℕ → ℝ) : Set ℕ := {n | 1 ≤ n ∧ nd (α * (n : ℝ) ^ 2) ≤ ε n}

/-- The set displayed in Erdős Problem 1147: `{n ≥ 1 : ‖α n²‖ < 1 / log n}`. -/
def erdosSet (α : ℝ) : Set ℕ := {n | 1 ≤ n ∧ nd (α * (n : ℝ) ^ 2) < 1 / Real.log n}

theorem erdosSet_subset_recSet (α : ℝ) : erdosSet α ⊆ recSet α (fun n => 1 / Real.log n) :=
  fun _ h => ⟨h.1, h.2.le⟩

/-! ### Upstream module `Proof/Pell.lean` -/

/-!
# Erdős Problem 1147: the Pell sequence for `√2`

The pairs `(x_j, y_j)` with `x_j + y_j √2 = (3 + 2√2)^(2j+1)` satisfy `x_j² - 2 y_j² = 1`, `x_j`
is odd and `y_j ≡ 2 (mod 4)`.  We set `N_j := y_j / 2` (an odd positive integer, tending to
infinity) and `P_j := x_j`, so that `P_j² = 8 N_j² + 1`.  The defect `η_j := P_j - 2√2 N_j` is
positive and tiny, and `ρ_j := η_j N_j` tends to `1 / (4√2)`.
-/

/-- `pell j = (x_j, y_j)` with `x_j + y_j √2 = (3 + 2√2)^(2j+1)`; each step multiplies by
`(3 + 2√2)² = 17 + 12√2`. -/
def pell : ℕ → ℕ × ℕ
  | 0 => (3, 2)
  | j + 1 => (17 * (pell j).1 + 24 * (pell j).2, 12 * (pell j).1 + 17 * (pell j).2)

/-- `P_j = x_j`. -/
def pP (j : ℕ) : ℕ := (pell j).1

/-- `y_j`. -/
def pY (j : ℕ) : ℕ := (pell j).2

/-- `N_j = y_j / 2`. -/
def pN (j : ℕ) : ℕ := pY j / 2

theorem pP_succ (j : ℕ) : pP (j + 1) = 17 * pP j + 24 * pY j := rfl

theorem pY_succ (j : ℕ) : pY (j + 1) = 12 * pP j + 17 * pY j := rfl

theorem pell_identity (j : ℕ) : pP j ^ 2 = 2 * pY j ^ 2 + 1 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [pP_succ, pY_succ]
    zify at ih ⊢
    linear_combination ih

theorem pP_odd (j : ℕ) : Odd (pP j) := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Nat.odd_iff] at ih ⊢
    rw [pP_succ]
    omega

theorem pY_mod_four (j : ℕ) : pY j % 4 = 2 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [pY_succ]
    omega

theorem two_mul_pN (j : ℕ) : 2 * pN j = pY j := by
  have h := pY_mod_four j
  unfold pN
  omega

theorem pN_odd (j : ℕ) : Odd (pN j) := by
  have h := pY_mod_four j
  rw [Nat.odd_iff]
  unfold pN
  omega

theorem pN_pos (j : ℕ) : 0 < pN j := by
  have h := pY_mod_four j
  unfold pN
  omega

/-- `N_{j+1} ≥ 17 N_j`, hence `N_j ≥ j + 1`. -/
theorem succ_le_pN (j : ℕ) : j + 1 ≤ pN j := by
  induction j with
  | zero => decide
  | succ j ih =>
    have h1 := two_mul_pN (j + 1)
    have h2 := two_mul_pN j
    have h3 := pY_succ j
    have h4 := Nat.odd_iff.1 (pP_odd j)
    omega

/-- `P_j² = 8 N_j² + 1` in `ℝ`. -/
theorem pP_sq_real (j : ℕ) : (pP j : ℝ) ^ 2 = 8 * (pN j : ℝ) ^ 2 + 1 := by
  have h : (pP j : ℝ) ^ 2 = 2 * (pY j : ℝ) ^ 2 + 1 := by exact_mod_cast pell_identity j
  have h2 : (pY j : ℝ) = 2 * (pN j : ℝ) := by exact_mod_cast (two_mul_pN j).symm
  rw [h2] at h
  linarith

/-- The defect `η_j = P_j - 2√2 N_j`. -/
noncomputable def eta (j : ℕ) : ℝ := (pP j : ℝ) - 2 * Real.sqrt 2 * pN j

theorem eta_mul (j : ℕ) : eta j * ((pP j : ℝ) + 2 * Real.sqrt 2 * pN j) = 1 := by
  have hdef : eta j = (pP j : ℝ) - 2 * Real.sqrt 2 * (pN j : ℝ) := rfl
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [hdef]
  linear_combination pP_sq_real j - 4 * (pN j : ℝ) ^ 2 * hsq

theorem eta_pos (j : ℕ) : 0 < eta j := by
  have hP : 0 < pP j := by
    have h := Nat.odd_iff.1 (pP_odd j)
    omega
  have hP' : (0 : ℝ) < (pP j : ℝ) := by exact_mod_cast hP
  have hden : (0 : ℝ) < (pP j : ℝ) + 2 * Real.sqrt 2 * pN j := by
    have h : (0 : ℝ) ≤ 2 * Real.sqrt 2 * (pN j : ℝ) := by positivity
    linarith
  nlinarith [eta_mul j, hden]

/-- `η_j ≤ 1 / (4√2 N_j)`. -/
theorem eta_le (j : ℕ) : eta j ≤ 1 / (4 * Real.sqrt 2 * pN j) := by
  have hNpos : (0 : ℝ) < (pN j : ℝ) := by exact_mod_cast pN_pos j
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hc : (0 : ℝ) < 4 * Real.sqrt 2 * (pN j : ℝ) := mul_pos (by linarith) hNpos
  rw [le_div_iff₀ hc]
  have hkey : eta j * (4 * Real.sqrt 2 * (pN j : ℝ)) + eta j * eta j
      = eta j * ((pP j : ℝ) + 2 * Real.sqrt 2 * pN j) := by
    unfold eta
    ring
  linarith [eta_mul j, hkey, mul_self_nonneg (eta j)]

/-- `ρ_j = η_j N_j`. -/
noncomputable def rho (j : ℕ) : ℝ := eta j * pN j

/-- The exact gap to the limit: `1 / (4√2) - ρ_j = η_j² / (4√2)`. -/
private theorem one_div_sub_rho (j : ℕ) :
    1 / (4 * Real.sqrt 2) - rho j = eta j ^ 2 / (4 * Real.sqrt 2) := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h4 : (4 : ℝ) * Real.sqrt 2 ≠ 0 := by positivity
  have hdef : eta j = (pP j : ℝ) - 2 * Real.sqrt 2 * (pN j : ℝ) := rfl
  have hrho : rho j = eta j * (pN j : ℝ) := rfl
  have hkey : 1 - 4 * Real.sqrt 2 * rho j = eta j ^ 2 := by
    rw [hrho]
    linear_combination (-1 : ℝ) * eta_mul j - eta j * hdef
  field_simp
  linarith [hkey]

/-- `ρ_j < 1 / (4√2)`. -/
theorem rho_lt (j : ℕ) : rho j < 1 / (4 * Real.sqrt 2) := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h := one_div_sub_rho j
  have hpos : 0 < eta j ^ 2 / (4 * Real.sqrt 2) :=
    div_pos (pow_pos (eta_pos j) 2) (by linarith)
  linarith

/-- Numerical form: `ρ_j < 9 / 50` (note `1 / (4√2) ≈ 0.1768`). -/
theorem rho_lt_num (j : ℕ) : rho j < 9 / 50 := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h25 : (25 : ℝ) / 18 < Real.sqrt 2 := by nlinarith
  have h : 1 / (4 * Real.sqrt 2) < 9 / 50 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith
  linarith [rho_lt j]

/-- `|1 / (4√2) - ρ_j| ≤ 1 / (32 N_j²)`. -/
theorem abs_rho_sub_le (j : ℕ) : |1 / (4 * Real.sqrt 2) - rho j| ≤ 1 / (32 * (pN j : ℝ) ^ 2) := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hN1 : (1 : ℝ) ≤ (pN j : ℝ) := by
    have h1 : 1 ≤ pN j := pN_pos j
    exact_mod_cast h1
  have hid := one_div_sub_rho j
  have hnn : 0 ≤ 1 / (4 * Real.sqrt 2) - rho j := by
    rw [hid]
    positivity
  rw [abs_of_nonneg hnn, hid]
  have hc : (0 : ℝ) < 4 * Real.sqrt 2 * (pN j : ℝ) := by nlinarith
  have h1 : eta j * (4 * Real.sqrt 2 * (pN j : ℝ)) ≤ 1 := by
    rw [← le_div_iff₀ hc]
    exact eta_le j
  have h0 : 0 ≤ eta j * (4 * Real.sqrt 2 * (pN j : ℝ)) := mul_nonneg (eta_pos j).le hc.le
  have hsqle : (eta j * (4 * Real.sqrt 2 * (pN j : ℝ))) ^ 2 ≤ 1 := by nlinarith
  have hexp : (eta j * (4 * Real.sqrt 2 * (pN j : ℝ))) ^ 2
      = eta j ^ 2 * (32 * (pN j : ℝ) ^ 2) := by
    linear_combination (16 * eta j ^ 2 * (pN j : ℝ) ^ 2) * hsq
  rw [hexp] at hsqle
  rw [div_le_div_iff₀ (by linarith) (by nlinarith)]
  linarith

/-! ### Upstream module `Proof/Phase.lean` -/

/-!
# Erdős Problem 1147: the phase identity at the Pell scales

For `N = N_j`, `P = P_j` and a split `N = n₁ + n₂`, one has
`√2 n₂² = ((N - 2 n₁) P) / 2 - ρ_j / 2 + n₁ η_j + √2 n₁²`.
Since `(N - 2 n₁) P` is odd, `√2 n₂² ≡ 1/2 + t + √2 n₁² (mod 1)` with
`t = n₁ η_j - ρ_j / 2`, `|t| ≤ ρ_j / 2 < 9 / 100`.

Two consequences:
* (both summands close to integers is impossible) if `‖√2 n₁²‖ ≤ ε₀` and `‖√2 n₂²‖ ≤ ε₀` with
  `ε₀ ≤ 1/5`, then `‖√2 n₂² - √2 n₁²‖ ≤ 2/5`, while it equals `‖1/2 + t‖ ≥ 1/2 - 9/100`;
* (a fixed first summand) for fixed `n₁ ≥ 1`, `‖√2 (N_j - n₁)²‖` stays bounded away from `0`
  for large `j`, because its phase tends to `θ = 1/2 - 1/(8√2) + √2 n₁²`, which is not an
  integer as `√2` is irrational.
-/

/-- The exact phase identity. -/
theorem phase_identity (j n₁ : ℕ) (h : n₁ ≤ pN j) :
    Real.sqrt 2 * ((pN j - n₁ : ℕ) : ℝ) ^ 2 =
      (((pN j : ℤ) - 2 * n₁) * (pP j : ℤ) : ℤ) / 2 - rho j / 2 + n₁ * eta j
        + Real.sqrt 2 * (n₁ : ℝ) ^ 2 := by
  have hP : (pP j : ℝ) = eta j + 2 * Real.sqrt 2 * (pN j : ℝ) := by
    rw [eta]; ring
  have hr : rho j = eta j * (pN j : ℝ) := rfl
  rw [Nat.cast_sub h, hr]
  push_cast
  linear_combination (2 * (n₁ : ℝ) - (pN j : ℝ)) / 2 * hP

/-- `(N_j - 2 n₁) P_j` is odd. -/
theorem odd_phase_int (j n₁ : ℕ) : Odd (((pN j : ℤ) - 2 * n₁) * (pP j : ℤ)) := by
  obtain ⟨k, hk⟩ := pN_odd j
  obtain ⟨l, hl⟩ := pP_odd j
  refine Odd.mul ⟨(k : ℤ) - n₁, ?_⟩ ⟨(l : ℤ), ?_⟩
  · rw [hk]; push_cast; ring
  · rw [hl]; push_cast; ring

/-- `nd (√2 n₂²) = nd (1/2 + t + √2 n₁²)` with `t = n₁ η_j - ρ_j / 2`. -/
theorem nd_phase (j n₁ : ℕ) (h : n₁ ≤ pN j) :
    nd (Real.sqrt 2 * ((pN j - n₁ : ℕ) : ℝ) ^ 2) =
      nd (1 / 2 + (n₁ * eta j - rho j / 2) + Real.sqrt 2 * (n₁ : ℝ) ^ 2) := by
  rw [phase_identity j n₁ h]
  have hsplit : (((pN j : ℤ) - 2 * n₁) * (pP j : ℤ) : ℤ) / 2 - rho j / 2 + n₁ * eta j
        + Real.sqrt 2 * (n₁ : ℝ) ^ 2
      = ((((pN j : ℤ) - 2 * n₁) * (pP j : ℤ) : ℤ) : ℝ) / 2
        + ((n₁ : ℝ) * eta j - rho j / 2 + Real.sqrt 2 * (n₁ : ℝ) ^ 2) := by
    ring
  rw [hsplit, nd_odd_div_two_add _ (odd_phase_int j n₁)]
  congr 1
  ring

/-- `|n₁ η_j - ρ_j / 2| ≤ ρ_j / 2` for `n₁ ≤ N_j`. -/
theorem abs_shift_le (j n₁ : ℕ) (h : n₁ ≤ pN j) : |n₁ * eta j - rho j / 2| ≤ rho j / 2 := by
  have hr : rho j = eta j * (pN j : ℝ) := rfl
  have h0 : (0 : ℝ) ≤ (n₁ : ℝ) * eta j := mul_nonneg (Nat.cast_nonneg _) (eta_pos j).le
  have h1 : (n₁ : ℝ) * eta j ≤ rho j := by
    rw [hr, mul_comm (eta j) ((pN j : ℝ))]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 h) (eta_pos j).le
  rw [abs_le]
  constructor <;> linarith

/-- Both summands of a split of `N_j` cannot both have `‖√2 n²‖ ≤ ε₀` when `ε₀ ≤ 1/5`. -/
theorem not_both_close (j n₁ : ℕ) (h : n₁ ≤ pN j) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1 / 5)
    (h₁ : nd (Real.sqrt 2 * (n₁ : ℝ) ^ 2) ≤ ε₀)
    (h₂ : nd (Real.sqrt 2 * ((pN j - n₁ : ℕ) : ℝ) ^ 2) ≤ ε₀) : False := by
  have hsub := nd_sub_le (Real.sqrt 2 * ((pN j - n₁ : ℕ) : ℝ) ^ 2) (Real.sqrt 2 * (n₁ : ℝ) ^ 2)
  have hshift := abs_shift_le j n₁ h
  have hrho := rho_lt_num j
  have ht : |(n₁ : ℝ) * eta j - rho j / 2| ≤ 1 / 2 := by linarith
  have key : Real.sqrt 2 * ((pN j - n₁ : ℕ) : ℝ) ^ 2 - Real.sqrt 2 * (n₁ : ℝ) ^ 2
      = ((((pN j : ℤ) - 2 * n₁) * (pP j : ℤ) : ℤ) : ℝ) / 2
        + ((n₁ : ℝ) * eta j - rho j / 2) := by
    rw [phase_identity j n₁ h]; ring
  rw [key, nd_odd_div_two_add _ (odd_phase_int j n₁)] at hsub
  have hlow := half_sub_abs_le_nd_half_add _ ht
  linarith

/-- The limiting phase for a fixed first summand `n₁`. -/
noncomputable def theta (n₁ : ℕ) : ℝ := 1 / 2 - 1 / (8 * Real.sqrt 2) + Real.sqrt 2 * (n₁ : ℝ) ^ 2

/-- `θ n₁` is never an integer (for `n₁ ≥ 1`, and in fact for all `n₁`, since `16 n₁² ≠ 1`). -/
theorem nd_theta_pos (n₁ : ℕ) : 0 < nd (theta n₁) := by
  rcases (nd_nonneg (theta n₁)).lt_or_eq with h | h
  · exact h
  exfalso
  obtain ⟨m, hm⟩ := (nd_eq_zero_iff (theta n₁)).1 h.symm
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hspos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h8 : 1 / (8 * Real.sqrt 2) = Real.sqrt 2 / 16 := by
    rw [eq_div_iff (by norm_num : (16 : ℝ) ≠ 0), div_mul_eq_mul_div,
      div_eq_iff (by positivity : (8 : ℝ) * Real.sqrt 2 ≠ 0)]
    linear_combination -8 * hs
  rw [theta, h8] at hm
  have hkey : Real.sqrt 2 * (16 * (n₁ : ℝ) ^ 2 - 1) = 16 * (m : ℝ) - 8 := by
    linear_combination 16 * hm
  have hd : (16 * (n₁ : ℝ) ^ 2 - 1) ≠ 0 := by
    rcases Nat.eq_zero_or_pos n₁ with h0 | h0
    · rw [h0]; norm_num
    · have h1 : (1 : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast h0
      have : (0 : ℝ) < 16 * (n₁ : ℝ) ^ 2 - 1 := by nlinarith
      exact ne_of_gt this
  refine irrational_sqrt_two ⟨(16 * (m : ℚ) - 8) / (16 * (n₁ : ℚ) ^ 2 - 1), ?_⟩
  push_cast
  rw [div_eq_iff hd]
  linarith [hkey]

/-- For a fixed first summand, the second summand's phase is eventually bounded away from the
integers: `nd (√2 (N_j - n₁)²) ≥ nd (θ n₁) / 2` once `N_j` is large. -/
theorem nd_second_summand_ge (n₁ : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      nd (theta n₁) / 2 ≤ nd (Real.sqrt 2 * ((pN j - n₁ : ℕ) : ℝ) ^ 2) := by
  have hc : 0 < nd (theta n₁) := nd_theta_pos n₁
  refine ⟨n₁ + ⌈2 * ((n₁ : ℝ) + 1) / nd (theta n₁)⌉₊ + 1, fun j hj => ?_⟩
  have hjN : j + 1 ≤ pN j := succ_le_pN j
  have hle : n₁ ≤ pN j := by omega
  have hKle : ⌈2 * ((n₁ : ℝ) + 1) / nd (theta n₁)⌉₊ ≤ pN j := by omega
  have hn0 : (0 : ℝ) ≤ (n₁ : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ (pN j : ℝ) := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ (pN j : ℝ) := by exact_mod_cast pN_pos j
  have hNpos : (0 : ℝ) < (pN j : ℝ) := by linarith
  have hNr : 2 * ((n₁ : ℝ) + 1) / nd (theta n₁) ≤ (pN j : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hKle)
  have hNc : 2 * ((n₁ : ℝ) + 1) ≤ (pN j : ℝ) * nd (theta n₁) := (div_le_iff₀ hc).1 hNr
  rw [nd_phase j n₁ hle]
  have h8 : 1 / (8 * Real.sqrt 2) = 1 / (4 * Real.sqrt 2) / 2 := by
    rw [div_div]; ring_nf
  have hdiff : theta n₁ - (1 / 2 + ((n₁ : ℝ) * eta j - rho j / 2)
        + Real.sqrt 2 * (n₁ : ℝ) ^ 2)
      = -((n₁ : ℝ) * eta j) - (1 / (4 * Real.sqrt 2) - rho j) / 2 := by
    rw [theta, h8]; ring
  have hA0 : (0 : ℝ) ≤ (n₁ : ℝ) * eta j := mul_nonneg hn0 (eta_pos j).le
  have hB := abs_rho_sub_le j
  have hB0 : (0 : ℝ) ≤ |1 / (4 * Real.sqrt 2) - rho j| := abs_nonneg _
  have e1 : |theta n₁ - (1 / 2 + ((n₁ : ℝ) * eta j - rho j / 2)
        + Real.sqrt 2 * (n₁ : ℝ) ^ 2)|
      ≤ (n₁ : ℝ) * eta j + |1 / (4 * Real.sqrt 2) - rho j| / 2 := by
    rw [hdiff, abs_le]
    refine ⟨?_, ?_⟩
    · linarith [le_abs_self (1 / (4 * Real.sqrt 2) - rho j)]
    · linarith [neg_abs_le (1 / (4 * Real.sqrt 2) - rho j)]
  have hBN : |1 / (4 * Real.sqrt 2) - rho j| * (32 * (pN j : ℝ) ^ 2) ≤ 1 :=
    (le_div_iff₀ (by positivity)).1 hB
  have e4 : |1 / (4 * Real.sqrt 2) - rho j| * (pN j : ℝ) ≤ 1 := by
    nlinarith [mul_nonneg hB0 (show (0 : ℝ) ≤ 32 * (pN j : ℝ) ^ 2 - (pN j : ℝ) by nlinarith)]
  have e2 : (n₁ : ℝ) * eta j * (pN j : ℝ) = (n₁ : ℝ) * rho j := by
    rw [rho]; ring
  have e3 : (n₁ : ℝ) * rho j ≤ (n₁ : ℝ) := by
    have h9 : rho j ≤ 1 := by linarith [rho_lt_num j]
    nlinarith
  have hmul : |theta n₁ - (1 / 2 + ((n₁ : ℝ) * eta j - rho j / 2)
        + Real.sqrt 2 * (n₁ : ℝ) ^ 2)| * (pN j : ℝ) ≤ (n₁ : ℝ) + 1 := by
    calc _ ≤ ((n₁ : ℝ) * eta j + |1 / (4 * Real.sqrt 2) - rho j| / 2) * (pN j : ℝ) :=
          mul_le_mul_of_nonneg_right e1 hN0
      _ = (n₁ : ℝ) * eta j * (pN j : ℝ)
            + |1 / (4 * Real.sqrt 2) - rho j| * (pN j : ℝ) / 2 := by ring
      _ ≤ (n₁ : ℝ) + 1 := by rw [e2]; linarith
  have key := (le_div_iff₀ hNpos).2 hmul
  have hfin : ((n₁ : ℝ) + 1) / (pN j : ℝ) ≤ nd (theta n₁) / 2 := by
    rw [div_le_iff₀ hNpos]; linarith
  have hlip := nd_le_nd_add_abs_sub (theta n₁)
    (1 / 2 + ((n₁ : ℝ) * eta j - rho j / 2) + Real.sqrt 2 * (n₁ : ℝ) ^ 2)
  linarith

/-! ### Upstream module `Proof/Main.lean` -/

section
/-!
# Erdős Problem 1147: the negative answer (Konieczny 2016, Proposition 1.3)

For every threshold function `ε : ℕ → ℝ` with `ε n → 0`, the set `{n ≥ 1 : ‖√2 n²‖ ≤ ε n}` is not
an asymptotic additive basis of order `2`: none of the Pell numbers `N_j` (for `j` large) is a sum
of two of its elements.  In particular the set `{n ≥ 1 : ‖α n²‖ < 1 / log n}` is not a basis of
order `2` for `α = √2`, which answers Erdős's question negatively.
-/

open _root_.Filter

/-- The second horn of the argument: if a split `a + b = N_j` has `‖√2 a²‖ > 1/5`, then `a` is
below the threshold `M` where `ε` has dropped under `1/5`, hence `a` is one of finitely many
values; for those, `‖√2 b²‖ = ‖√2 (N_j - a)²‖` is bounded below by `nd (θ a) / 2`, which `ε b`
has already dropped under.  So `b` cannot lie in the recurrence set. -/
private theorem bad_summand {ε : ℕ → ℝ} {J M₂ : ℕ → ℕ} {M Ms j a b : ℕ} (hab : a + b = pN j)
    (ha : nd (Real.sqrt 2 * (a : ℝ) ^ 2) ≤ ε a) (hb : nd (Real.sqrt 2 * (b : ℝ) ^ 2) ≤ ε b)
    (hbig : 1 / 5 < nd (Real.sqrt 2 * (a : ℝ) ^ 2))
    (hJ : ∀ n₁ i : ℕ, J n₁ ≤ i →
      nd (theta n₁) / 2 ≤ nd (Real.sqrt 2 * ((pN i - n₁ : ℕ) : ℝ) ^ 2))
    (hjJ : ∀ n₁ : ℕ, n₁ < M → J n₁ ≤ j) (hM : ∀ n : ℕ, M ≤ n → ε n < 1 / 5)
    (hM₂ : ∀ n₁ n : ℕ, M₂ n₁ ≤ n → ε n < nd (theta n₁) / 2)
    (hsup : ∀ n₁ : ℕ, n₁ < M → M₂ n₁ ≤ Ms) (hNj : M + Ms ≤ pN j) : False := by
  have haM : a < M := by
    by_contra hcon
    have hlt : ε a < 1 / 5 := hM a (not_lt.1 hcon)
    linarith
  have hMb : M₂ a ≤ b := by
    have := hsup a haM
    omega
  have key : nd (theta a) / 2 ≤ nd (Real.sqrt 2 * (b : ℝ) ^ 2) := by
    have h := hJ a j (hjJ a haM)
    rwa [show (pN j - a : ℕ) = b from by omega] at h
  have hlt : ε b < nd (theta a) / 2 := hM₂ a b hMb
  linarith

/-- **Konieczny, Proposition 1.3 (case `ε n → 0`).** -/
theorem sqrtTwo_recSet_not_basis (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0)) :
    ¬ IsAsymptoticBasis2 (recSet (Real.sqrt 2) ε) := by
  rintro ⟨n₀, hbasis⟩
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 hε).2 (1 / 5) (by norm_num))
  choose J hJ using nd_second_summand_ge
  have hthr : ∀ n₁ : ℕ, ∃ K : ℕ, ∀ n : ℕ, K ≤ n → ε n < nd (theta n₁) / 2 := fun n₁ =>
    Filter.eventually_atTop.1 ((tendsto_order.1 hε).2 _ (by linarith [nd_theta_pos n₁]))
  choose M₂ hM₂ using hthr
  obtain ⟨Ms, hsup⟩ : ∃ Ms : ℕ, ∀ n₁ : ℕ, n₁ < M → M₂ n₁ ≤ Ms :=
    ⟨(Finset.range M).sup M₂, fun _ h => Finset.le_sup (Finset.mem_range.2 h)⟩
  obtain ⟨j, hjJ, hjle⟩ : ∃ j : ℕ, (∀ n₁ : ℕ, n₁ < M → J n₁ ≤ j) ∧ n₀ + M + Ms ≤ j :=
    ⟨max ((Finset.range M).sup J) (n₀ + M + Ms),
      fun _ h => le_trans (Finset.le_sup (Finset.mem_range.2 h)) (le_max_left _ _),
      le_max_right _ _⟩
  have hpN : j + 1 ≤ pN j := succ_le_pN j
  obtain ⟨a, ha, b, hb, hab⟩ := hbasis (pN j) (by omega)
  obtain ⟨-, ha2⟩ := ha
  obtain ⟨-, hb2⟩ := hb
  by_cases h₁ : nd (Real.sqrt 2 * (a : ℝ) ^ 2) ≤ 1 / 5
  · by_cases h₂ : nd (Real.sqrt 2 * (b : ℝ) ^ 2) ≤ 1 / 5
    · exact not_both_close j a (by omega) (le_refl ((1 : ℝ) / 5)) h₁
        (by rwa [show (pN j - a : ℕ) = b from by omega])
    · exact bad_summand (by omega) hb2 ha2 (not_le.1 h₂) hJ hjJ hM hM₂ hsup (by omega)
  · exact bad_summand hab ha2 hb2 (not_le.1 h₁) hJ hjJ hM hM₂ hsup (by omega)

/-- The recurrence set with threshold `1 / log n` for `α = √2` is not an asymptotic basis. -/
theorem sqrtTwo_recSet_log_not_basis :
    ¬ IsAsymptoticBasis2 (recSet (Real.sqrt 2) (fun n => 1 / Real.log n)) := by
  refine sqrtTwo_recSet_not_basis _ ?_
  have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  simpa [Function.comp_def, Pi.inv_def, one_div] using h

/-- The set displayed in Erdős Problem 1147 with `α = √2` is not an asymptotic basis of
order `2`. -/
theorem sqrtTwo_erdosSet_not_basis : ¬ IsAsymptoticBasis2 (erdosSet (Real.sqrt 2)) := by
  intro h
  exact sqrtTwo_recSet_log_not_basis (h.mono (erdosSet_subset_recSet _))

/-- **Erdős Problem 1147 has a negative answer**: it is not the case that for every positive
irrational `α` the set `{n ≥ 1 : ‖α n²‖ < 1 / log n}` is an asymptotic basis of order `2`. -/
theorem erdos_1147 :
    ¬ ∀ α : ℝ, 0 < α → Irrational α → IsAsymptoticBasis2 (erdosSet α) := by
  intro h
  exact sqrtTwo_erdosSet_not_basis (h (Real.sqrt 2) (by positivity) irrational_sqrt_two)

end

#print axioms erdos_1147
-- 'Erdos1147.erdos_1147' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1147
