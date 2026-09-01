import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos171

/-
# Problem Description

Erdős Problem 171, the density Hales--Jewett problem. Is it true that for every `ε > 0` and
integer `t ≥ 1`, if `N` is sufficiently large and `A ⊆ [t]^N` has size at least `ε tᴺ`, then
`A` contains a combinatorial line — a set `P = {p₁, …, p_t}` in which each coordinate is
either constant or equal to the index `i`? `erdos_171` proves that it is.

Proved by Furstenberg and Katznelson; a later elementary proof with quantitative bounds is
due to the Polymath project.

`Word t n` is `Fin n → Fin t`, i.e. the discrete cube `[t]^N`. `ContainsLine A` is
`∃ l : Combinatorics.Line (Fin t) (Fin n), Set.range l ⊆ A`, using Mathlib's own
`Combinatorics.Line`, which carries the properness requirement that at least one coordinate
actually varies — so the line cannot degenerate to a single point. `N₀` is chosen after `ε`
and `t`, which is the "sufficiently large" of the question.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/IncrementArithmetic.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Arithmetic for the density-increment step in Erdős 171

This file isolates the real-number bookkeeping in the Dodos--Kanellopoulos--Tyros
proof of density Hales--Jewett.  It contains no combinatorial definitions.  The
constants are

* `theta δ q = δ / (4q)`, where `q` is the number of lines in a fixed cube;
* `eta δ θ = δθ / 48`;
* `gamma δ η k = δη² / k`.

The remaining lemmas are the numerical estimates used in Lemmas 8 and 10,
Corollary 11, and the last tiling/averaging step of that proof.
-/

namespace IncrementArithmetic

open scoped BigOperators

/-- The line-correlation threshold, with `q` possible line templates. -/
noncomputable def theta (δ q : ℝ) : ℝ := δ / (4 * q)

/-- The error parameter in the DKT density-increment argument. -/
noncomputable def eta (δ θ : ℝ) : ℝ := δ * θ / 48

/-- The density increment supplied by a structured set. -/
noncomputable def gamma (δ η k : ℝ) : ℝ := δ * η ^ 2 / k

theorem theta_pos {δ q : ℝ} (hδ : 0 < δ) (hq : 0 < q) :
    0 < theta δ q := by
  unfold theta
  positivity

theorem theta_le_delta_div_four {δ q : ℝ} (hδ : 0 ≤ δ) (hq : 1 ≤ q) :
    theta δ q ≤ δ / 4 := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  unfold theta
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * q) (by norm_num)).2
  nlinarith [mul_le_mul_of_nonneg_left hq hδ]

theorem eta_pos {δ θ : ℝ} (hδ : 0 < δ) (hθ : 0 < θ) :
    0 < eta δ θ := by
  unfold eta
  positivity

theorem gamma_pos {δ η k : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hk : 0 < k) :
    0 < gamma δ η k := by
  unfold gamma
  positivity

/-- In the paper `δ ≤ 1`; this very coarse estimate is enough to make the
two large sets in Lemma 8 intersect. -/
theorem eta_lt_theta_div_two {δ θ : ℝ}
    (hδ_one : δ ≤ 1) (hθ : 0 < θ) :
    eta δ θ < θ / 2 := by
  have hmul : δ * θ ≤ θ := by
    simpa using mul_le_mul_of_nonneg_right hδ_one hθ.le
  unfold eta
  nlinarith

/-- A convenient bound ensuring that removing `3η` leaves positive density. -/
theorem three_eta_lt_delta {δ θ : ℝ}
    (hδ : 0 < δ) (hθ_one : θ ≤ 1) :
    3 * eta δ θ < δ := by
  have hmul : δ * θ ≤ δ := by
    simpa using mul_le_mul_of_nonneg_left hθ_one hδ.le
  unfold eta
  nlinarith

theorem eta_lt_one {δ θ : ℝ}
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) (hθ : 0 < θ) (hθ_one : θ ≤ 1) :
    eta δ θ < 1 := by
  have hη := eta_pos hδ hθ
  have hmul_delta : δ * θ ≤ δ := by
    simpa using mul_le_mul_of_nonneg_left hθ_one hδ.le
  have hmul : δ * θ ≤ 1 := hmul_delta.trans hδ_one
  unfold eta at hη ⊢
  nlinarith

/-- The first branch of Corollary 11 has an increment at least `γ`. -/
theorem gamma_le_eta_sq_div_two {δ η k : ℝ}
    (_hδ_nonneg : 0 ≤ δ) (hδ_one : δ ≤ 1) (hk : 2 ≤ k) :
    gamma δ η k ≤ η ^ 2 / 2 := by
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hηsq : 0 ≤ η ^ 2 := sq_nonneg η
  have hleft : δ * η ^ 2 ≤ η ^ 2 := by
    simpa using mul_le_mul_of_nonneg_right hδ_one hηsq
  have hright : η ^ 2 ≤ (η ^ 2 / 2) * k := by
    nlinarith [mul_le_mul_of_nonneg_left hk hηsq]
  unfold gamma
  rw [div_le_iff₀ hkpos]
  exact hleft.trans hright

/-- The structured-set increment is much smaller than the `3η` relative
increment selected in the partition argument. -/
theorem gamma_lt_three_eta {δ η k : ℝ}
    (hδ_nonneg : 0 ≤ δ) (hδ_one : δ ≤ 1)
    (hη : 0 < η) (hη_one : η < 1) (hk : 2 ≤ k) :
    gamma δ η k < 3 * η := by
  have hγ := gamma_le_eta_sq_div_two (η := η) hδ_nonneg hδ_one hk
  nlinarith [mul_pos hη (sub_pos.mpr hη_one)]

/-- The scalar contradiction used to show that the set `H₁` in Lemma 8 has
density greater than `1 - η`. -/
theorem bad_fiber_average_lt {δ η : ℝ} (hη : 0 < η) :
    η * (δ - 2 * η) + (1 - η) * (δ + η ^ 2 / 2) < δ - η ^ 2 / 2 := by
  nlinarith [sq_pos_of_pos hη, mul_pos (sq_pos_of_pos hη) hη]

/-- The scalar contradiction used to show that the set `H₂` in Lemma 8 has
density greater than `θ/2`. -/
theorem line_rich_average_lt {θ : ℝ} (hθ : 0 < θ) :
    θ / 2 + (1 - θ / 2) * (θ / 2) < θ := by
  nlinarith [sq_pos_of_pos hθ]

/-- The lower bound for the density of the structured set in Lemma 10. -/
theorem theta_div_four_lt {θ η : ℝ} (hθ : 0 < θ) (hη : η < 1 / 2) :
    θ / 4 < (θ / 2) * (1 - η) := by
  have hprod : 0 < θ * (1 - 2 * η) :=
    mul_pos hθ (by nlinarith)
  nlinarith

/-- The main conditional-density calculation in Lemma 10.

After deleting a structured set of density at least `θ/4`, at most `3η` of
the mass of `A` has been lost.  With the paper's choice `η = δθ/48`, the
remaining conditional density is strictly larger than `δ + 6η`.
-/
theorem conditional_density_increment {δ θ : ℝ}
    (hδ : 0 < δ) (hθ : 0 < θ) (hθ_four : θ < 4) :
    δ + 6 * eta δ θ < (δ - 3 * eta δ θ) / (1 - θ / 4) := by
  have hden : 0 < 1 - θ / 4 := by nlinarith
  rw [lt_div_iff₀ hden]
  unfold eta
  have hδθ : 0 < δ * θ := mul_pos hδ hθ
  have hδθθ : 0 ≤ (δ * θ) * θ := mul_nonneg hδθ.le hθ.le
  nlinarith

/-- The multiplicative form of the conditional-density estimate with
parameters frozen at a lower density `δ₀`, but the current density equal to
some `ρ ≥ δ₀`.  This is the form needed for a rigorous density-increment
iteration with a fixed positive increment. -/
theorem fixed_lower_density_increment_mul {δ₀ ρ θ : ℝ}
    (hδ₀ : 0 < δ₀) (hδρ : δ₀ ≤ ρ) (hθ : 0 < θ) :
    (ρ + 6 * eta δ₀ θ) * (1 - θ / 4) < ρ - 3 * eta δ₀ θ := by
  have hρθ : δ₀ * θ ≤ ρ * θ :=
    mul_le_mul_of_nonneg_right hδρ hθ.le
  have hδθ : 0 < δ₀ * θ := mul_pos hδ₀ hθ
  have hδθθ : 0 ≤ (δ₀ * θ) * θ := mul_nonneg hδθ.le hθ.le
  unfold eta
  nlinarith

/-- Quotient form of `fixed_lower_density_increment_mul`.  The paper has
`0 < θ ≤ 1`, which in particular makes the denominator positive. -/
theorem fixed_lower_conditional_density_increment {δ₀ ρ θ : ℝ}
    (hδ₀ : 0 < δ₀) (hδρ : δ₀ ≤ ρ)
    (hθ : 0 < θ) (hθ_one : θ ≤ 1) :
    ρ + 6 * eta δ₀ θ < (ρ - 3 * eta δ₀ θ) / (1 - θ / 4) := by
  have hden : 0 < 1 - θ / 4 := by nlinarith
  rw [lt_div_iff₀ hden]
  exact fixed_lower_density_increment_mul hδ₀ hδρ hθ

/-- The density of the structured piece selected in Corollary 11 exceeds
`γ`.  The hypotheses `δ,θ ≤ 1` are the coarse bounds available in DKT. -/
theorem gamma_lt_structured_piece {δ θ k : ℝ}
    (hδ : 0 < δ) (hδ_one : δ ≤ 1)
    (hθ : 0 < θ) (hθ_one : θ ≤ 1) (hk : 0 < k) :
    gamma δ (eta δ θ) k <
      (3 * eta δ θ / k) * (δ - 3 * eta δ θ) := by
  have hη : 0 < eta δ θ := eta_pos hδ hθ
  have hη_le : eta δ θ ≤ δ / 48 := by
    unfold eta
    have := mul_le_mul_of_nonneg_left hθ_one hδ.le
    nlinarith
  have hδη : δ * eta δ θ ≤ eta δ θ := by
    simpa using mul_le_mul_of_nonneg_right hδ_one hη.le
  have hinside : 0 < 3 * δ - δ * eta δ θ - 9 * eta δ θ := by
    nlinarith
  have hnum : δ * (eta δ θ) ^ 2 <
      3 * eta δ θ * (δ - 3 * eta δ θ) := by
    nlinarith [mul_pos hη hinside]
  unfold gamma
  calc
    δ * eta δ θ ^ 2 / k <
        (3 * eta δ θ * (δ - 3 * eta δ θ)) / k :=
      (div_lt_div_iff_of_pos_right hk).2 hnum
    _ = (3 * eta δ θ / k) * (δ - 3 * eta δ θ) := by ring

/-- The structured-piece estimate at a current density `ρ`, while `eta` and
`gamma` remain frozen at the original lower density `δ₀`. -/
theorem fixed_gamma_lt_structured_piece {δ₀ ρ θ k : ℝ}
    (hδ₀ : 0 < δ₀) (hδ₀_one : δ₀ ≤ 1) (hδρ : δ₀ ≤ ρ)
    (hθ : 0 < θ) (hθ_one : θ ≤ 1) (hk : 0 < k) :
    gamma δ₀ (eta δ₀ θ) k <
      (3 * eta δ₀ θ / k) * (ρ - 3 * eta δ₀ θ) := by
  have hbase := gamma_lt_structured_piece hδ₀ hδ₀_one hθ hθ_one hk
  have hcoef : 0 ≤ 3 * eta δ₀ θ / k := by
    exact div_nonneg (mul_nonneg (by norm_num) (eta_pos hδ₀ hθ).le) hk.le
  have hmono :
      (3 * eta δ₀ θ / k) * (δ₀ - 3 * eta δ₀ θ) ≤
        (3 * eta δ₀ θ / k) * (ρ - 3 * eta δ₀ θ) := by
    exact mul_le_mul_of_nonneg_left (by linarith) hcoef
  exact hbase.trans_le hmono

/-- All coarse bounds on the frozen DKT parameters used by the iteration,
packaged so later files do not have to reproduce their arithmetic. -/
theorem fixed_parameter_bounds {δ₀ θ k : ℝ}
    (hδ₀ : 0 < δ₀) (hδ₀_one : δ₀ ≤ 1)
    (hθ : 0 < θ) (hθ_one : θ ≤ 1) (hk : 2 ≤ k) :
    let η := eta δ₀ θ
    let γ := gamma δ₀ η k
    0 < η ∧ η < θ / 2 ∧ 3 * η < δ₀ ∧
      0 < γ ∧ γ ≤ η ^ 2 / 2 ∧ γ < 3 * η ∧
      γ < δ₀ ∧ γ < 1 ∧ γ < 2 := by
  dsimp only
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hη : 0 < eta δ₀ θ := eta_pos hδ₀ hθ
  have hηθ : eta δ₀ θ < θ / 2 := eta_lt_theta_div_two hδ₀_one hθ
  have h3η : 3 * eta δ₀ θ < δ₀ := three_eta_lt_delta hδ₀ hθ_one
  have hηone : eta δ₀ θ < 1 := eta_lt_one hδ₀ hδ₀_one hθ hθ_one
  have hγ : 0 < gamma δ₀ (eta δ₀ θ) k := gamma_pos hδ₀ hη hkpos
  have hγsq : gamma δ₀ (eta δ₀ θ) k ≤ (eta δ₀ θ) ^ 2 / 2 :=
    gamma_le_eta_sq_div_two hδ₀.le hδ₀_one hk
  have hγ3 : gamma δ₀ (eta δ₀ θ) k < 3 * eta δ₀ θ :=
    gamma_lt_three_eta hδ₀.le hδ₀_one hη hηone hk
  have hγδ : gamma δ₀ (eta δ₀ θ) k < δ₀ := hγ3.trans h3η
  exact ⟨hη, hηθ, h3η, hγ, hγsq, hγ3, hγδ,
    hγδ.trans_le hδ₀_one,
    lt_trans (hγδ.trans_le hδ₀_one) (by norm_num)⟩

/-- In particular, the frozen increment stays below every later density
`ρ ≥ δ₀`. -/
theorem fixed_gamma_lt_current_density {δ₀ ρ θ k : ℝ}
    (hδ₀ : 0 < δ₀) (hδ₀_one : δ₀ ≤ 1) (hδρ : δ₀ ≤ ρ)
    (hθ : 0 < θ) (hθ_one : θ ≤ 1) (hk : 2 ≤ k) :
    gamma δ₀ (eta δ₀ θ) k < ρ := by
  have hbounds := fixed_parameter_bounds hδ₀ hδ₀_one hθ hθ_one hk
  exact hbounds.2.2.2.2.2.2.1.trans_le hδρ

/-- A weighted partition whose total relative density is too large has a
part which is simultaneously non-negligible and has increased relative
density.  This is the averaging step in Corollary 11.

The estimate deliberately overcounts every small-weight part by `3η/k`.
This avoids introducing a filtered subpartition and is convenient in Lean.
-/
theorem exists_large_weight_and_value
    {ι : Type*} (s : Finset ι) (weight value : ι → ℝ)
    {k δ η : ℝ}
    (hk : 0 < k) (hcard : (s.card : ℝ) ≤ k) (hη : 0 < η)
    (hweight : ∀ i ∈ s, 0 ≤ weight i)
    (hvalue : ∀ i ∈ s, value i ≤ 1)
    (hweight_sum : ∑ i ∈ s, weight i = 1)
    (hbase : 0 ≤ δ + 3 * η)
    (haverage : δ + 6 * η < ∑ i ∈ s, weight i * value i) :
    ∃ i ∈ s, 3 * η / k < weight i ∧ δ + 3 * η < value i := by
  classical
  by_contra! hnone
  have hlarge : ∀ i ∈ s, 3 * η / k < weight i → value i ≤ δ + 3 * η := by
    intro i hi hwi
    exact hnone i hi hwi
  have hsmall_nonneg : 0 ≤ 3 * η / k := by positivity
  have hpoint : ∀ i ∈ s,
      weight i * value i ≤ 3 * η / k + (δ + 3 * η) * weight i := by
    intro i hi
    by_cases hsmall : weight i ≤ 3 * η / k
    · have hmul : weight i * value i ≤ weight i := by
        simpa using mul_le_mul_of_nonneg_left (hvalue i hi) (hweight i hi)
      have htail : 0 ≤ (δ + 3 * η) * weight i :=
        mul_nonneg hbase (hweight i hi)
      linarith
    · have hwi : 3 * η / k < weight i := lt_of_not_ge hsmall
      have hmul := mul_le_mul_of_nonneg_left (hlarge i hi hwi) (hweight i hi)
      nlinarith
  have hsum_le :
      (∑ i ∈ s, weight i * value i) ≤
        ∑ i ∈ s, (3 * η / k + (δ + 3 * η) * weight i) := by
    gcongr with i hi
    exact hpoint i hi
  have hcard_mul : (s.card : ℝ) * (3 * η / k) ≤ 3 * η := by
    have hmul := mul_le_mul_of_nonneg_right hcard
      (show (0 : ℝ) ≤ 3 * η by positivity)
    have heq : (s.card : ℝ) * (3 * η / k) =
        ((s.card : ℝ) * (3 * η)) / k := by ring
    rw [heq, div_le_iff₀ hk]
    nlinarith [hmul]
  have hsum_rhs :
      (∑ i ∈ s, (3 * η / k + (δ + 3 * η) * weight i)) =
        (s.card : ℝ) * (3 * η / k) + (δ + 3 * η) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.mul_sum, hweight_sum, mul_one]
  rw [hsum_rhs] at hsum_le
  linarith

/-- Removing mass less than `γ²/2` from a structured set of density greater
than `γ` preserves a density increment of `γ/2` on its covered part.

Here `d` is the mass of the structured set, `u` the covered mass, `r` the
uncovered mass, and `c` the mass of `A` on the covered part.
-/
theorem uncovered_mass_density_increment
    {δ γ d u r c : ℝ}
    (hδ : 0 ≤ δ) (hγ : 0 < γ) (hd : γ < d)
    (hr : r < γ ^ 2 / 2) (hu : u ≤ d)
    (hc : (δ + γ) * d - r ≤ c) :
    (δ + γ / 2) * u < c := by
  have hcoefficient : 0 ≤ δ + γ / 2 := by positivity
  have hutarget : (δ + γ / 2) * u ≤ (δ + γ / 2) * d :=
    mul_le_mul_of_nonneg_left hu hcoefficient
  have hgap : r < (γ / 2) * d := by
    nlinarith [mul_lt_mul_of_pos_left hd hγ]
  nlinarith

/-- The error threshold in the final tiling is exactly `γ²/2`. -/
theorem tiling_error_identity {γ k : ℝ} (hk : k ≠ 0) :
    2 * k * (γ ^ 2 / (4 * k)) = γ ^ 2 / 2 := by
  field_simp
  ring

/-- A positive increment smaller than `2` dominates the final tiling error. -/
theorem tiling_error_lt_gamma {γ : ℝ} (hγ : 0 < γ) (hγ_two : γ < 2) :
    γ ^ 2 / 2 < γ := by
  nlinarith [mul_pos hγ (sub_pos.mpr hγ_two)]

end IncrementArithmetic

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/Basic.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Basic finite-word and combinatorial-line infrastructure for Erdős 171

This file fixes the concrete convention used in the formalization: a word in
`[t]^n` is a function `Fin n → Fin t`, and a combinatorial line is Mathlib's
proper `Combinatorics.Line (Fin t) (Fin n)`.  It also records the elementary
injectivity and composition facts used throughout the density argument.
-/



open Set

/-- The discrete cube `[t]^n`, represented as words of length `n` over `Fin t`. -/
abbrev Word (t n : ℕ) := Fin n → Fin t

/-- A set of words contains a (proper) combinatorial line. -/
def ContainsLine {t n : ℕ} (A : Set (Word t n)) : Prop :=
  ∃ l : Combinatorics.Line (Fin t) (Fin n), Set.range l ⊆ A

theorem containsLine_iff {t n : ℕ} {A : Set (Word t n)} :
    ContainsLine A ↔
      ∃ l : Combinatorics.Line (Fin t) (Fin n), ∀ a : Fin t, l a ∈ A := by
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l, fun a ↦ hl ⟨a, rfl⟩⟩
  · rintro ⟨l, hl⟩
    refine ⟨l, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact hl a

theorem ContainsLine.mono {t n : ℕ} {A B : Set (Word t n)}
    (hA : ContainsLine A) (hAB : A ⊆ B) : ContainsLine B := by
  obtain ⟨l, hl⟩ := hA
  exact ⟨l, hl.trans hAB⟩

theorem containsLine_coe_finset_iff {t n : ℕ} {A : Finset (Word t n)} :
    ContainsLine (A : Set (Word t n)) ↔
      ∃ l : Combinatorics.Line (Fin t) (Fin n), ∀ a : Fin t, l a ∈ A := by
  simpa only [Finset.mem_coe] using (containsLine_iff (A := (A : Set (Word t n))))

@[simp] theorem card_word (t n : ℕ) : Fintype.card (Word t n) = t ^ n := by
  simp [Word]



section
open Combinatorics

section
open Combinatorics.Line

/-- The collection of lines in a finite cube is finite. -/
private noncomputable instance _root_.Combinatorics.Line.instFintype {α ι : Type*} [Fintype α] [Fintype ι] :
    Fintype (Line α ι) := by
  classical
  exact Fintype.ofInjective Line.idxFun fun _ _ h ↦ Line.ext h

/-- A line template without any wildcard coordinates. -/
private def _root_.Combinatorics.Line.NoWildcard {α ι : Type*} (f : ι → Option α) : Prop :=
  ∀ i, f i ≠ none

/-- A line is exactly a template which is not wildcard-free. -/
private noncomputable def _root_.Combinatorics.Line.templateEquiv {α ι : Type*} :
    Line α ι ≃ {f : ι → Option α // ¬ NoWildcard f} where
  toFun l := ⟨l.idxFun, by
    intro h
    obtain ⟨i, hi⟩ := l.proper
    exact h i hi⟩
  invFun f :=
    { idxFun := f
      proper := by
        classical
        simpa only [NoWildcard, not_forall, not_ne_iff] using f.property }
  left_inv l := by
    apply Line.ext
    rfl
  right_inv f := by
    apply Subtype.ext
    rfl

/-- Wildcard-free templates are exactly ordinary words. -/
private noncomputable def _root_.Combinatorics.Line.fixedTemplateEquiv {α ι : Type*} :
    (ι → α) ≃ {f : ι → Option α // NoWildcard f} where
  toFun x := ⟨fun i ↦ some (x i), fun _ ↦ Option.some_ne_none _⟩
  invFun f i := (f.1 i).get (Option.ne_none_iff_isSome.mp (f.2 i))
  left_inv x := by
    funext i
    rfl
  right_inv f := by
    apply Subtype.ext
    funext i
    exact Option.some_get _

/-- The number of proper line templates is the number of all templates minus
the number of wildcard-free templates. -/
private theorem _root_.Combinatorics.Line.card_eq_templates_sub_words {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι] :
    Fintype.card (Line α ι) =
      (Fintype.card α + 1) ^ Fintype.card ι -
        Fintype.card α ^ Fintype.card ι := by
  classical
  rw [Fintype.card_congr (templateEquiv (α := α) (ι := ι))]
  rw [Fintype.card_subtype_compl (NoWildcard (α := α) (ι := ι))]
  rw [← Fintype.card_congr (fixedTemplateEquiv (α := α) (ι := ι))]
  simp

/-- In `[k]^m` there are `(k+1)^m-k^m` proper combinatorial lines. -/
@[simp] private theorem _root_.Combinatorics.Line.card_fin (k m : ℕ) :
    Fintype.card (Line (Fin k) (Fin m)) = (k + 1) ^ m - k ^ m := by
  simpa using
    (card_eq_templates_sub_words (α := Fin k) (ι := Fin m))

/-- A proper combinatorial line is injective in its alphabet parameter. -/
private theorem _root_.Combinatorics.Line.parameter_injective {α ι : Type*} (l : Line α ι) : Function.Injective l := by
  intro a b hab
  obtain ⟨i, hi⟩ := l.proper
  have hiab := congrFun hab i
  simpa only [l.apply_none a i hi, l.apply_none b i hi] using hiab

private theorem _root_.Combinatorics.Line.ncard_range [Finite α] {ι : Type*} (l : Line α ι) :
    Set.ncard (Set.range l) = Nat.card α := by
  rw [Set.ncard_range_of_injective l.parameter_injective]

private theorem _root_.Combinatorics.Line.card_range {ι : Type*} [Fintype α] [DecidableEq (ι → α)] (l : Line α ι) :
    (Finset.univ.image l).card = Fintype.card α := by
  rw [Finset.card_image_of_injective _ l.parameter_injective, Finset.card_univ]

end

section
open Combinatorics.Subspace

/-- The collection of subspaces between finite cubes is finite. -/
private noncomputable instance _root_.Combinatorics.Subspace.instFintype {η α ι : Type*} [Fintype η] [Fintype α]
    [Fintype ι] : Fintype (Subspace η α ι) := by
  classical
  exact Fintype.ofInjective Subspace.idxFun fun _ _ h ↦ Subspace.ext h

/-- Evaluation on a proper subspace is injective in the parameter word. -/
private theorem _root_.Combinatorics.Subspace.parameter_injective {η α ι : Type*} (U : Subspace η α ι) :
    Function.Injective U := by
  intro x y hxy
  funext e
  obtain ⟨i, hi⟩ := U.proper e
  have hcoord := congrFun hxy i
  simpa only [U.apply_inr (x := x) hi, U.apply_inr (x := y) hi] using hcoord

/-- Compose a line in the parameter cube with a combinatorial subspace. -/
private def _root_.Combinatorics.Subspace.lineMap {η α ι : Type*} (U : Subspace η α ι) (l : Line α η) : Line α ι where
  idxFun i := (U.idxFun i).elim some l.idxFun
  proper := by
    obtain ⟨e, he⟩ := l.proper
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨i, by simp [hi, he]⟩

@[simp] private theorem _root_.Combinatorics.Subspace.lineMap_idxFun_inl {η α ι : Type*} (U : Subspace η α ι)
    (l : Line α η) {i : ι} {a : α} (hi : U.idxFun i = Sum.inl a) :
    (U.lineMap l).idxFun i = some a := by
  simp [lineMap, hi]

@[simp] private theorem _root_.Combinatorics.Subspace.lineMap_idxFun_inr {η α ι : Type*} (U : Subspace η α ι)
    (l : Line α η) {i : ι} {e : η} (hi : U.idxFun i = Sum.inr e) :
    (U.lineMap l).idxFun i = l.idxFun e := by
  simp [lineMap, hi]

/-- Distinct parameter-space lines remain distinct after composition with a proper subspace. -/
private theorem _root_.Combinatorics.Subspace.lineMap_injective {η α ι : Type*} (U : Subspace η α ι) :
    Function.Injective U.lineMap := by
  intro l₁ l₂ h
  apply Line.ext
  funext e
  obtain ⟨i, hi⟩ := U.proper e
  have hcoord := congrArg (fun l : Line α ι ↦ l.idxFun i) h
  simpa [lineMap, hi] using hcoord

@[simp] private theorem _root_.Combinatorics.Subspace.lineMap_apply {η α ι : Type*} (U : Subspace η α ι)
    (l : Line α η) (a : α) : U.lineMap l a = U (l a) := by
  funext i
  cases hi : U.idxFun i with
  | inl b => simp [lineMap, Line.coe_apply, Subspace.coe_apply, hi]
  | inr e =>
      cases he : l.idxFun e <;>
        simp [lineMap, Line.coe_apply, Subspace.coe_apply, hi, he]

private theorem _root_.Combinatorics.Subspace.lineMap_range {η α ι : Type*} (U : Subspace η α ι) (l : Line α η) :
    Set.range (U.lineMap l) = U '' Set.range l := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨l a, ⟨a, rfl⟩, (lineMap_apply U l a).symm⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, lineMap_apply U l a⟩

private theorem _root_.Combinatorics.Subspace.ncard_range [Finite η] [Finite α] {ι : Type*} (U : Subspace η α ι) :
    Set.ncard (Set.range U) = Nat.card (η → α) := by
  rw [Set.ncard_range_of_injective U.parameter_injective]

private theorem _root_.Combinatorics.Subspace.card_range {ι : Type*} [Fintype η] [DecidableEq η] [Fintype α]
    [DecidableEq (ι → α)]
    (U : Subspace η α ι) :
    (Finset.univ.image U).card = Fintype.card (η → α) := by
  rw [Finset.card_image_of_injective _ U.parameter_injective, Finset.card_univ]

end

end



/-- Embed a word over `Fin k` into the same-length cube over `Fin (k+1)`. -/
def restrictWord {k m : ℕ} (w : Word k m) : Word (k + 1) m :=
  fun i ↦ Fin.castSucc (w i)

theorem restrictWord_injective {k m : ℕ} : Function.Injective (restrictWord (k := k) (m := m)) := by
  intro x y h
  funext i
  exact Fin.castSucc_inj.mp (by simpa only [restrictWord] using congrFun h i)

/-- A word over `Fin (k+1)` lies entirely in its initial `Fin k` alphabet. -/
def IsRestrictedWord {k m : ℕ} (w : Word (k + 1) m) : Prop :=
  ∀ i, w i ≠ Fin.last k

/-- Ordinary `Fin k` words are equivalent to `Fin (k+1)` words which avoid the
new last letter. -/
noncomputable def restrictedWordEquiv (k m : ℕ) :
    Word k m ≃ {w : Word (k + 1) m // IsRestrictedWord w} where
  toFun w := ⟨restrictWord w, fun i ↦ Fin.castSucc_ne_last (w i)⟩
  invFun w := fun i ↦ (w.1 i).castPred (w.2 i)
  left_inv w := by
    funext i
    exact Fin.castPred_castSucc
  right_inv w := by
    apply Subtype.ext
    funext i
    exact Fin.castSucc_castPred (w.1 i) (w.2 i)

theorem range_restrictWord {k m : ℕ} :
    Set.range (restrictWord (k := k) (m := m)) =
      {w : Word (k + 1) m | IsRestrictedWord w} := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    exact fun i ↦ Fin.castSucc_ne_last (v i)
  · intro hw
    let w' : {w : Word (k + 1) m // IsRestrictedWord w} := ⟨w, hw⟩
    refine ⟨(restrictedWordEquiv k m).symm w', ?_⟩
    exact congrArg Subtype.val ((restrictedWordEquiv k m).apply_symm_apply w')

/-- Replace every wildcard in a line template by the new last letter.  This is
the endpoint at the additional letter in the density-Hales--Jewett argument. -/
def templateEndpoint {k m : ℕ} (l : Combinatorics.Line (Fin k) (Fin m)) :
    Word (k + 1) m :=
  fun i ↦ finSuccEquivLast.symm (l.idxFun i)

/-- Regard an internal `Fin k` line template as a line over `Fin (k+1)` by
embedding all of its fixed letters. -/
def templateExtension {k m : ℕ} (l : Combinatorics.Line (Fin k) (Fin m)) :
    Combinatorics.Line (Fin (k + 1)) (Fin m) :=
  l.map Fin.castSucc

@[simp] theorem templateExtension_castSucc {k m : ℕ}
    (l : Combinatorics.Line (Fin k) (Fin m)) (a : Fin k) :
    templateExtension l (Fin.castSucc a) = restrictWord (l a) := by
  funext i
  cases hi : l.idxFun i with
  | none =>
      simp [templateExtension, restrictWord, Combinatorics.Line.map,
        Combinatorics.Line.coe_apply, hi]
  | some b =>
      simp [templateExtension, restrictWord, Combinatorics.Line.map,
        Combinatorics.Line.coe_apply, hi]

@[simp] theorem templateExtension_last {k m : ℕ}
    (l : Combinatorics.Line (Fin k) (Fin m)) :
    templateExtension l (Fin.last k) = templateEndpoint l := by
  funext i
  cases hi : l.idxFun i with
  | none =>
      simp [templateExtension, templateEndpoint, Combinatorics.Line.map,
        Combinatorics.Line.coe_apply, hi]
  | some a =>
      simp [templateExtension, templateEndpoint, Combinatorics.Line.map,
        Combinatorics.Line.coe_apply, hi]

@[simp] theorem templateEndpoint_of_none {k m : ℕ}
    (l : Combinatorics.Line (Fin k) (Fin m)) {i : Fin m}
    (hi : l.idxFun i = none) :
    templateEndpoint l i = Fin.last k := by
  simp [templateEndpoint, hi]

@[simp] theorem templateEndpoint_of_some {k m : ℕ}
    (l : Combinatorics.Line (Fin k) (Fin m)) {i : Fin m} {a : Fin k}
    (hi : l.idxFun i = some a) :
    templateEndpoint l i = Fin.castSucc a := by
  simp [templateEndpoint, hi]

theorem templateEndpoint_not_restricted {k m : ℕ}
    (l : Combinatorics.Line (Fin k) (Fin m)) :
    ¬ IsRestrictedWord (templateEndpoint l) := by
  intro h
  obtain ⟨i, hi⟩ := l.proper
  exact h i (templateEndpoint_of_none l hi)

/-- Proper internal line templates are in bijection with the words which use
the new last letter in at least one coordinate. -/
noncomputable def templateEndpointEquiv (k m : ℕ) :
    Combinatorics.Line (Fin k) (Fin m) ≃
      {w : Word (k + 1) m // ¬ IsRestrictedWord w} where
  toFun l := ⟨templateEndpoint l, templateEndpoint_not_restricted l⟩
  invFun w :=
    { idxFun := fun i ↦ finSuccEquivLast (w.1 i)
      proper := by
        classical
        have hw : ∃ i, w.1 i = Fin.last k := by
          simpa only [IsRestrictedWord, not_forall, not_ne_iff] using w.2
        obtain ⟨i, hi⟩ := hw
        exact ⟨i, by simp [hi]⟩ }
  left_inv l := by
    apply Combinatorics.Line.ext
    funext i
    simp [templateEndpoint]
  right_inv w := by
    apply Subtype.ext
    funext i
    simp [templateEndpoint]

theorem templateEndpoint_injective {k m : ℕ} :
    Function.Injective (templateEndpoint (k := k) (m := m)) := by
  intro l₁ l₂ h
  apply (templateEndpointEquiv k m).injective
  apply Subtype.ext
  exact h

theorem range_templateEndpoint {k m : ℕ} :
    Set.range (templateEndpoint (k := k) (m := m)) =
      {w : Word (k + 1) m | ¬ IsRestrictedWord w} := by
  ext w
  constructor
  · rintro ⟨l, rfl⟩
    exact templateEndpoint_not_restricted l
  · intro hw
    let w' : {w : Word (k + 1) m // ¬ IsRestrictedWord w} := ⟨w, hw⟩
    refine ⟨(templateEndpointEquiv k m).symm w', ?_⟩
    exact congrArg Subtype.val ((templateEndpointEquiv k m).apply_symm_apply w')

theorem range_templateEndpoint_eq_compl_restrictWord {k m : ℕ} :
    Set.range (templateEndpoint (k := k) (m := m)) =
      (Set.range (restrictWord (k := k) (m := m)))ᶜ := by
  rw [range_templateEndpoint, range_restrictWord]
  rfl

@[simp] theorem ncard_range_templateEndpoint (k m : ℕ) :
    Set.ncard (Set.range (templateEndpoint (k := k) (m := m))) =
      (k + 1) ^ m - k ^ m := by
  rw [Set.ncard_range_of_injective templateEndpoint_injective]
  simp only [Nat.card_eq_fintype_card, Combinatorics.Line.card_fin]

/-- A line in a subspace pullback gives a line in the original set. -/
theorem containsLine_of_subspace_preimage {t m n : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n))
    {A : Set (Word t n)} (h : ContainsLine (U ⁻¹' A)) : ContainsLine A := by
  obtain ⟨l, hl⟩ := h
  refine ⟨U.lineMap l, ?_⟩
  rintro _ ⟨a, rfl⟩
  rw [Combinatorics.Subspace.lineMap_apply]
  exact hl ⟨a, rfl⟩

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/Density.lean` -/

section
/-!
# Uniform density on finite types

This file collects the elementary finite-probability identities used in the
formalization of the density Hales--Jewett theorem.  The definitions take values in
`ℝ`; this is convenient for the density-increment estimates, while the proofs reduce
to exact finite sums.
-/

open scoped BigOperators



section Density

variable {α β : Type*}

/-- The uniform average of a real-valued function on a finite type. -/
noncomputable def average [Fintype α] (f : α → ℝ) : ℝ :=
  𝔼 x, f x

/-- The density of a finset in its ambient finite type, as a real number. -/
noncomputable def density [Fintype α] (A : Finset α) : ℝ :=
  (A.card : ℝ) / Fintype.card α

@[simp]
theorem average_eq_sum_div_card [Fintype α] (f : α → ℝ) :
    average f = (∑ x, f x) / Fintype.card α := by
  simp [average, Fintype.expect_eq_sum_div_card]

@[simp]
theorem density_eq_card_div_card [Fintype α] (A : Finset α) :
    density A = (A.card : ℝ) / Fintype.card α := by
  rfl

theorem density_eq_coe_dens [Fintype α] (A : Finset α) :
    density A = (A.dens : ℝ) := by
  rw [density_eq_card_div_card, Finset.nnratCast_dens]

@[simp]
theorem density_empty [Fintype α] : density (∅ : Finset α) = 0 := by
  simp [density]

@[simp]
theorem density_univ [Fintype α] [Nonempty α] :
    density (Finset.univ : Finset α) = 1 := by
  simp [density]

theorem density_nonneg [Fintype α] (A : Finset α) : 0 ≤ density A := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem density_le_one [Fintype α] (A : Finset α) : density A ≤ 1 := by
  cases isEmpty_or_nonempty α with
  | inl h =>
      letI := h
      have hA : A = ∅ := by
        ext x
        exact isEmptyElim x
      simp [hA]
  | inr h =>
      letI := h
      rw [density, div_le_one (by positivity)]
      exact_mod_cast Finset.card_le_univ A

theorem density_mono [Fintype α] {A B : Finset α} (h : A ⊆ B) :
    density A ≤ density B := by
  unfold density
  gcongr

@[simp]
theorem density_eq_zero [Fintype α] (A : Finset α) :
    density A = 0 ↔ A = ∅ := by
  cases isEmpty_or_nonempty α with
  | inl h =>
      letI := h
      have hA : A = ∅ := by
        ext x
        exact isEmptyElim x
      simp [hA]
  | inr h =>
      letI := h
      simp [density]

@[simp]
theorem density_pos [Fintype α] (A : Finset α) :
    0 < density A ↔ A.Nonempty := by
  constructor
  · intro h
    rw [Finset.nonempty_iff_ne_empty]
    intro hA
    simpa [hA] using h
  · intro h
    rw [lt_iff_le_and_ne]
    refine ⟨density_nonneg A, ?_⟩
    intro hd
    exact h.ne_empty ((density_eq_zero A).1 hd.symm)

theorem average_const [Fintype α] [Nonempty α] (c : ℝ) :
    average (fun _ : α ↦ c) = c := by
  simp [average, Fintype.expect_const]

theorem average_add [Fintype α] (f g : α → ℝ) :
    average (fun x ↦ f x + g x) = average f + average g := by
  simp [average, Finset.expect_add_distrib]

theorem average_sub [Fintype α] (f g : α → ℝ) :
    average (fun x ↦ f x - g x) = average f - average g := by
  simp [average, Finset.expect_sub_distrib]

theorem average_mul_const [Fintype α] (f : α → ℝ) (c : ℝ) :
    average (fun x ↦ f x * c) = average f * c := by
  simp [average, Finset.expect_mul]

theorem average_const_mul [Fintype α] (c : ℝ) (f : α → ℝ) :
    average (fun x ↦ c * f x) = c * average f := by
  simp [average, Finset.mul_expect]

/-- Fubini's identity for the uniform average on a finite product. -/
theorem average_product [Fintype α] [Fintype β] (f : α × β → ℝ) :
    average f = average fun a ↦ average fun b ↦ f (a, b) := by
  unfold average
  rw [← Finset.univ_product_univ]
  exact Finset.expect_product Finset.univ Finset.univ f

/-- Uniform finite averages commute. -/
theorem average_comm [Fintype α] [Fintype β] (f : α → β → ℝ) :
    average (fun a ↦ average fun b ↦ f a b) =
      average (fun b ↦ average fun a ↦ f a b) := by
  unfold average
  exact Finset.expect_comm Finset.univ Finset.univ f

/-- The elementary second-moment inequality for a uniform finite average. -/
theorem sq_average_le_average_sq [Fintype α] (f : α → ℝ) :
    (average f) ^ 2 ≤ average fun x ↦ (f x) ^ 2 := by
  simpa only [average_eq_sum_div_card, Finset.card_univ] using
    (sum_div_card_sq_le_sum_sq_div_card
      (s := Finset.univ) (f := f))

/-- The average of a function over a specified finite subset. -/
noncomputable def averageOn (A : Finset α) (f : α → ℝ) : ℝ :=
  𝔼 x ∈ A, f x

@[simp]
theorem averageOn_eq_sum_div_card (A : Finset α) (f : α → ℝ) :
    averageOn A f = (∑ x ∈ A, f x) / A.card := by
  simp [averageOn, Finset.expect_eq_sum_div_card]

/-- Some point of a nonempty finite set attains at least the average on that set. -/
theorem exists_averageOn_le {A : Finset α} (hA : A.Nonempty) (f : α → ℝ) :
    ∃ x ∈ A, averageOn A f ≤ f x := by
  by_contra! h
  have hsum : (∑ x ∈ A, f x) < ∑ _x ∈ A, averageOn A f :=
    Finset.sum_lt_sum_of_nonempty hA (fun x hx ↦ h x hx)
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_ne_zero
  rw [averageOn_eq_sum_div_card, Finset.sum_const, nsmul_eq_mul] at hsum
  have hcancel : (A.card : ℝ) * ((∑ x ∈ A, f x) / A.card) = ∑ x ∈ A, f x := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hcard
  rw [hcancel] at hsum
  exact hsum.false

theorem average_mono [Fintype α] {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    average f ≤ average g := by
  simp only [average_eq_sum_div_card]
  gcongr with x
  exact h x

theorem average_nonneg [Fintype α] {f : α → ℝ} (h : ∀ x, 0 ≤ f x) :
    0 ≤ average f := by
  simpa only [average, Finset.expect_const_zero] using
    average_mono (f := fun _ : α ↦ 0) (g := f) h

theorem average_le_const [Fintype α] [Nonempty α] {f : α → ℝ} {c : ℝ}
    (h : ∀ x, f x ≤ c) : average f ≤ c := by
  simpa [average_const] using average_mono (f := f) (g := fun _ ↦ c) h

theorem const_le_average [Fintype α] [Nonempty α] {f : α → ℝ} {c : ℝ}
    (h : ∀ x, c ≤ f x) : c ≤ average f := by
  simpa [average_const] using average_mono (f := fun _ ↦ c) (g := f) h

/-- Some value of a function is at least its uniform average. -/
theorem exists_average_le [Fintype α] [Nonempty α] (f : α → ℝ) :
    ∃ x, average f ≤ f x := by
  by_contra! h
  have hsum : (∑ x, f x) < ∑ _x : α, average f :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun x _ ↦ h x)
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by positivity
  rw [average_eq_sum_div_card, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hcancel : (Fintype.card α : ℝ) *
      ((∑ x, f x) / Fintype.card α) = ∑ x, f x := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hcard
  rw [hcancel] at hsum
  exact hsum.false

/-- Some value of a function is at most its uniform average. -/
theorem exists_le_average [Fintype α] [Nonempty α] (f : α → ℝ) :
    ∃ x, f x ≤ average f := by
  obtain ⟨x, hx⟩ := exists_average_le (fun x ↦ -f x)
  have hneg : average (fun x ↦ -f x) = -average f := by
    simp [average_eq_sum_div_card]
    ring
  exact ⟨x, by rw [hneg] at hx; linarith⟩

theorem exists_ge_of_le_average [Fintype α] [Nonempty α] {f : α → ℝ} {c : ℝ}
    (h : c ≤ average f) : ∃ x, c ≤ f x := by
  obtain ⟨x, hx⟩ := exists_average_le f
  exact ⟨x, h.trans hx⟩

theorem exists_gt_of_lt_average [Fintype α] [Nonempty α] {f : α → ℝ} {c : ℝ}
    (h : c < average f) : ∃ x, c < f x := by
  obtain ⟨x, hx⟩ := exists_average_le f
  exact ⟨x, h.trans_le hx⟩

/-- A fibre of a subset of a product, with the first coordinate fixed. -/
noncomputable def fiber [Fintype β] (A : Finset (α × β)) (a : α) : Finset β :=
  by
    classical
    exact Finset.univ.filter fun b ↦ (a, b) ∈ A

@[simp]
theorem mem_fiber [Fintype β] (A : Finset (α × β)) (a : α) (b : β) :
    b ∈ fiber A a ↔ (a, b) ∈ A := by
  classical
  simp [fiber]

/-- Exact fibrewise counting for a subset of a product. -/
theorem card_eq_sum_card_fiber [Fintype α] [Fintype β] (A : Finset (α × β)) :
    A.card = ∑ a, (fiber A a).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (s := A) (t := Finset.univ) (f := Prod.fst) (by simp)]
  apply Finset.sum_congr rfl
  intro a _
  refine Finset.card_bij (fun p _ ↦ p.2) ?_ ?_ ?_
  · intro p hp
    have hp' := Finset.mem_filter.1 hp
    apply (mem_fiber A a p.2).2
    rw [← hp'.2]
    simpa using hp'.1
  · intro p hp q hq hpq
    apply Prod.ext
    · have hp' := (Finset.mem_filter.1 hp).2
      have hq' := (Finset.mem_filter.1 hq).2
      simpa [hp', hq']
    · exact hpq
  · intro b hb
    refine ⟨(a, b), ?_, rfl⟩
    have hb' : (a, b) ∈ A := (mem_fiber A a b).1 hb
    simp [hb']

/-- Uniform density on a product is the average of the densities of its fibres. -/
theorem density_eq_average_fiber [Fintype α] [Fintype β]
    (A : Finset (α × β)) :
    density A = average fun a ↦ density (fiber A a) := by
  cases isEmpty_or_nonempty α with
  | inl hα =>
      letI := hα
      simp [density_eq_card_div_card, average_eq_sum_div_card]
  | inr hα =>
      letI := hα
      cases isEmpty_or_nonempty β with
      | inl hβ =>
          letI := hβ
          simp [density_eq_card_div_card, average_eq_sum_div_card]
      | inr hβ =>
          letI := hβ
          rw [density_eq_card_div_card, average_eq_sum_div_card]
          rw [card_eq_sum_card_fiber]
          simp only [density_eq_card_div_card]
          rw [Fintype.card_prod]
          push_cast
          rw [← Finset.sum_div]
          have ha : (Fintype.card α : ℝ) ≠ 0 := by positivity
          have hb : (Fintype.card β : ℝ) ≠ 0 := by positivity
          field_simp

/-- The indicator of a finset has average equal to its density. -/
theorem average_indicator [Fintype α] [DecidableEq α] (A : Finset α) :
    average (fun x ↦ if x ∈ A then (1 : ℝ) else 0) = density A := by
  classical
  simp [average_eq_sum_div_card, density_eq_card_div_card,
    Finset.sum_boole]

/-- The exact uniform average of a two-valued function. -/
theorem average_piecewise_const [Fintype α] [Nonempty α] [DecidableEq α]
    (A : Finset α) (a b : ℝ) :
    average (fun x ↦ if x ∈ A then a else b) =
      density A * a + (1 - density A) * b := by
  let ι : α → ℝ := fun x ↦ if x ∈ A then 1 else 0
  have hpoint : (fun x ↦ if x ∈ A then a else b) =
      fun x ↦ ι x * a + (1 - ι x) * b := by
    funext x
    simp only [ι]
    split <;> ring
  rw [hpoint, average_add, average_mul_const, average_mul_const,
    average_sub, average_const, average_indicator]

/-- A pointwise upper bound on and off a set gives the corresponding upper bound
for the uniform average. -/
theorem average_le_density_mul_add [Fintype α] [Nonempty α] [DecidableEq α]
    (A : Finset α) (f : α → ℝ) (a b : ℝ)
    (hA : ∀ x ∈ A, f x ≤ a) (hAc : ∀ x ∉ A, f x ≤ b) :
    average f ≤ density A * a + (1 - density A) * b := by
  rw [← average_piecewise_const A a b]
  apply average_mono
  intro x
  by_cases hx : x ∈ A
  · simpa [hx] using hA x hx
  · simpa [hx] using hAc x hx

/-- A pointwise lower bound on and off a set gives the corresponding lower bound
for the uniform average. -/
theorem density_mul_add_le_average [Fintype α] [Nonempty α] [DecidableEq α]
    (A : Finset α) (f : α → ℝ) (a b : ℝ)
    (hA : ∀ x ∈ A, a ≤ f x) (hAc : ∀ x ∉ A, b ≤ f x) :
    density A * a + (1 - density A) * b ≤ average f := by
  rw [← average_piecewise_const A a b]
  apply average_mono
  intro x
  by_cases hx : x ∈ A
  · simpa [hx] using hA x hx
  · simpa [hx] using hAc x hx

/-- The set on which a real-valued function is at least a given threshold. -/
noncomputable def superlevel [Fintype α] (f : α → ℝ) (c : ℝ) : Finset α := by
  classical
  exact Finset.univ.filter fun x ↦ c ≤ f x

@[simp]
theorem mem_superlevel [Fintype α] (f : α → ℝ) (c : ℝ) (x : α) :
    x ∈ superlevel f c ↔ c ≤ f x := by
  classical
  simp [superlevel]

/-- Quantitative averaging: if `f ≤ B` and its average is at least `μ`, then
the density of the set where `f ≥ c` is at least `(μ-c)/(B-c)`. -/
theorem density_superlevel_ge [Fintype α] [Nonempty α] [DecidableEq α]
    (f : α → ℝ) {μ c B : ℝ} (havg : μ ≤ average f)
    (hub : ∀ x, f x ≤ B) (hcB : c < B) :
    (μ - c) / (B - c) ≤ density (superlevel f c) := by
  have havg' : average f ≤ density (superlevel f c) * B +
      (1 - density (superlevel f c)) * c := by
    apply average_le_density_mul_add
    · intro x _
      exact hub x
    · intro x hx
      exact le_of_lt (not_le.1 (by simpa using hx))
  rw [div_le_iff₀ (sub_pos.2 hcB)]
  nlinarith

/-- The particularly useful half-threshold form of quantitative averaging. -/
theorem half_le_density_superlevel [Fintype α] [Nonempty α] [DecidableEq α]
    (f : α → ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ) (havg : δ ≤ average f)
    (hub : ∀ x, f x ≤ 1) :
    δ / 2 ≤ density (superlevel f (δ / 2)) := by
  have havg' : average f ≤ density (superlevel f (δ / 2)) +
      (1 - density (superlevel f (δ / 2))) * (δ / 2) := by
    convert average_le_density_mul_add (superlevel f (δ / 2)) f 1 (δ / 2)
      (fun x _ ↦ hub x) (fun x hx ↦ le_of_lt (not_le.1 (by simpa using hx))) using 1 <;> ring
  have hdle : density (superlevel f (δ / 2)) ≤ 1 := density_le_one _
  have hd0 : 0 ≤ density (superlevel f (δ / 2)) := density_nonneg _
  have hδle : δ ≤ 1 := havg.trans (average_le_const hub)
  nlinarith

/-- Markov's inequality for the finite uniform distribution. -/
theorem density_superlevel_le [Fintype α] [Nonempty α] [DecidableEq α]
    (f : α → ℝ) {μ c : ℝ} (havg : average f ≤ μ)
    (hnonneg : ∀ x, 0 ≤ f x) (hc : 0 < c) :
    density (superlevel f c) ≤ μ / c := by
  have hlower : density (superlevel f c) * c ≤ average f := by
    convert density_mul_add_le_average (superlevel f c) f c 0
      (fun x hx ↦ (mem_superlevel f c x).1 hx)
      (fun x _ ↦ hnonneg x) using 1 <;> ring
  rw [le_div_iff₀ hc]
  exact hlower.trans havg

/-- Turn a set into the finset of all its elements in a finite ambient type. -/
noncomputable def setFinset [Fintype α] (A : Set α) : Finset α := by
  classical
  exact Finset.univ.filter fun x ↦ x ∈ A

@[simp]
theorem mem_setFinset [Fintype α] (A : Set α) (x : α) :
    x ∈ setFinset A ↔ x ∈ A := by
  classical
  simp [setFinset]

/-- Uniform density of a set in a finite ambient type. -/
noncomputable def setDensity [Fintype α] (A : Set α) : ℝ :=
  density (setFinset A)

@[simp]
theorem setDensity_empty [Fintype α] : setDensity (∅ : Set α) = 0 := by
  classical
  simp [setDensity, setFinset]

@[simp]
theorem setDensity_univ [Fintype α] [Nonempty α] :
    setDensity (Set.univ : Set α) = 1 := by
  classical
  simp [setDensity, setFinset]

theorem setDensity_nonneg [Fintype α] (A : Set α) : 0 ≤ setDensity A :=
  density_nonneg _

theorem setDensity_le_one [Fintype α] (A : Set α) : setDensity A ≤ 1 :=
  density_le_one _

theorem setDensity_mono [Fintype α] {A B : Set α} (h : A ⊆ B) :
    setDensity A ≤ setDensity B := by
  apply density_mono
  intro x hx
  exact (mem_setFinset B x).2 (h (mem_setFinset A x |>.1 hx))

/-- A fibre of a set in a product. -/
def setFiber (A : Set (α × β)) (a : α) : Set β :=
  {b | (a, b) ∈ A}

@[simp]
theorem mem_setFiber (A : Set (α × β)) (a : α) (b : β) :
    b ∈ setFiber A a ↔ (a, b) ∈ A := Iff.rfl

/-- Set-valued version of the exact product/fibre density identity. -/
theorem setDensity_eq_average_fiber [Fintype α] [Fintype β]
    (A : Set (α × β)) :
    setDensity A = average fun a ↦ setDensity (setFiber A a) := by
  classical
  rw [setDensity, density_eq_average_fiber]
  apply congrArg average
  funext a
  unfold setDensity
  congr 1
  ext b
  simp [setFiber]

/-- Density is preserved by equivalences of finite ambient types. -/
theorem density_map_equiv [Fintype α] [Fintype β] (e : α ≃ β) (A : Finset α) :
    density (A.map e.toEmbedding) = density A := by
  simp [density, Fintype.card_congr e]

/-- The density of a Cartesian product is the product of the two densities. -/
theorem density_product [Fintype α] [Fintype β] (A : Finset α) (B : Finset β) :
    density (A ×ˢ B) = density A * density B := by
  simp [density_eq_card_div_card, Finset.card_product, Fintype.card_prod]
  ring

/-! ## Incidence Fubini identities -/

/-- The column of a finset of pairs at a fixed second coordinate. -/
noncomputable def columnFiber [Fintype α] (A : Finset (α × β)) (b : β) : Finset α := by
  classical
  exact Finset.univ.filter fun a ↦ (a, b) ∈ A

@[simp]
theorem mem_columnFiber [Fintype α] (A : Finset (α × β)) (a : α) (b : β) :
    a ∈ columnFiber A b ↔ (a, b) ∈ A := by
  classical
  simp [columnFiber]

/-- The product-density identity counted by columns rather than rows. -/
theorem density_eq_average_columnFiber [Fintype α] [Fintype β]
    (A : Finset (α × β)) :
    density A = average fun b ↦ density (columnFiber A b) := by
  classical
  let e : α × β ≃ β × α := Equiv.prodComm α β
  let A' : Finset (β × α) := A.map e.toEmbedding
  have hmap : density A' = density A := by
    exact density_map_equiv e A
  have hfiber (b : β) : fiber A' b = columnFiber A b := by
    ext a
    simp [A', e]
  calc
    density A = density A' := hmap.symm
    _ = average (fun b ↦ density (fiber A' b)) := density_eq_average_fiber A'
    _ = average (fun b ↦ density (columnFiber A b)) := by
      apply congrArg average
      funext b
      rw [hfiber]

/-- Double-counting incidences: average row density equals average column density. -/
theorem average_density_fiber_eq_columnFiber [Fintype α] [Fintype β]
    (A : Finset (α × β)) :
    average (fun a ↦ density (fiber A a)) =
      average (fun b ↦ density (columnFiber A b)) := by
  rw [← density_eq_average_fiber, ← density_eq_average_columnFiber]

/-- The row set of a binary relation. -/
def relationRow (R : α → β → Prop) (a : α) : Set β :=
  {b | R a b}

/-- The column set of a binary relation. -/
def relationColumn (R : α → β → Prop) (b : β) : Set α :=
  {a | R a b}

@[simp]
theorem mem_relationRow (R : α → β → Prop) (a : α) (b : β) :
    b ∈ relationRow R a ↔ R a b := Iff.rfl

@[simp]
theorem mem_relationColumn (R : α → β → Prop) (a : α) (b : β) :
    a ∈ relationColumn R b ↔ R a b := Iff.rfl

/-- Predicate/set form of finite incidence double-counting. -/
theorem average_setDensity_relationRow_eq_relationColumn [Fintype α] [Fintype β]
    (R : α → β → Prop) :
    average (fun a ↦ setDensity (relationRow R a)) =
      average (fun b ↦ setDensity (relationColumn R b)) := by
  classical
  let A : Finset (α × β) := setFinset {p | R p.1 p.2}
  have hrow (a : α) : setFinset (relationRow R a) = fiber A a := by
    ext b
    simp [A, relationRow]
  have hcolumn (b : β) : setFinset (relationColumn R b) = columnFiber A b := by
    ext a
    simp [A, relationColumn]
  simpa only [setDensity, hrow, hcolumn] using average_density_fiber_eq_columnFiber A

/-- The average density of pairwise row intersections is the average square of
the column densities.  This is the second-moment form of incidence Fubini. -/
theorem average_pairwise_intersection_relationRow [Fintype α] [Fintype β]
    (R : α → β → Prop) :
    average (fun p : α × α ↦
      setDensity (relationRow R p.1 ∩ relationRow R p.2)) =
      average (fun b ↦ (setDensity (relationColumn R b)) ^ 2) := by
  classical
  let R₂ : α × α → β → Prop := fun p b ↦ R p.1 b ∧ R p.2 b
  have hfubini := average_setDensity_relationRow_eq_relationColumn R₂
  calc
    average (fun p : α × α ↦
        setDensity (relationRow R p.1 ∩ relationRow R p.2)) =
        average (fun p ↦ setDensity (relationRow R₂ p)) := by
      apply congrArg average
      funext p
      congr 1
    _ = average (fun b ↦ setDensity (relationColumn R₂ b)) := hfubini
    _ = average (fun b ↦ setDensity {p : α × α | R p.1 b ∧ R p.2 b}) := by
      apply congrArg average
      funext b
      congr 1
    _ = average (fun b ↦ (setDensity (relationColumn R b)) ^ 2) := by
      apply congrArg average
      funext b
      unfold setDensity
      have hprod : setFinset {p : α × α | R p.1 b ∧ R p.2 b} =
          setFinset (relationColumn R b) ×ˢ setFinset (relationColumn R b) := by
        ext p
        simp [relationColumn]
      rw [hprod, density_product, pow_two]

/-- Nested-average version of `average_pairwise_intersection_relationRow`. -/
theorem average_average_intersection_relationRow [Fintype α] [Fintype β]
    (R : α → β → Prop) :
    average (fun a ↦ average fun a' ↦
      setDensity (relationRow R a ∩ relationRow R a')) =
      average (fun b ↦ (setDensity (relationColumn R b)) ^ 2) := by
  calc
    average (fun a ↦ average fun a' ↦
        setDensity (relationRow R a ∩ relationRow R a')) =
        average (fun p : α × α ↦
          setDensity (relationRow R p.1 ∩ relationRow R p.2)) :=
      (average_product (fun p : α × α ↦
        setDensity (relationRow R p.1 ∩ relationRow R p.2))).symm
    _ = average (fun b ↦ (setDensity (relationColumn R b)) ^ 2) :=
      average_pairwise_intersection_relationRow R

/-- A relation of average row density `δ` has average pairwise-row-intersection
density at least `δ²`. -/
theorem sq_average_relationRow_le_average_pairwise_intersection
    [Fintype α] [Fintype β] (R : α → β → Prop) :
    (average (fun a ↦ setDensity (relationRow R a))) ^ 2 ≤
      average (fun p : α × α ↦
        setDensity (relationRow R p.1 ∩ relationRow R p.2)) := by
  calc
    (average (fun a ↦ setDensity (relationRow R a))) ^ 2 =
        (average (fun b ↦ setDensity (relationColumn R b))) ^ 2 := by
      rw [average_setDensity_relationRow_eq_relationColumn]
    _ ≤ average (fun b ↦ (setDensity (relationColumn R b)) ^ 2) :=
      sq_average_le_average_sq _
    _ = average (fun p : α × α ↦
        setDensity (relationRow R p.1 ∩ relationRow R p.2)) :=
      (average_pairwise_intersection_relationRow R).symm

section Lattice

variable [Fintype α] [DecidableEq α]

theorem density_union_add_density_inter (A B : Finset α) :
    density (A ∪ B) + density (A ∩ B) = density A + density B := by
  simp only [density_eq_coe_dens]
  exact_mod_cast Finset.dens_union_add_dens_inter A B

theorem density_sdiff_add_density_inter (A B : Finset α) :
    density (A \ B) + density (A ∩ B) = density A := by
  simp only [density_eq_coe_dens]
  exact_mod_cast Finset.dens_sdiff_add_dens_inter A B

theorem density_inter_add_density_sdiff (A B : Finset α) :
    density (A ∩ B) + density (A \ B) = density A := by
  rw [add_comm, density_sdiff_add_density_inter]

/-- The elementary union-bound form most useful in density arguments. -/
theorem density_add_sub_one_le_density_inter (A B : Finset α) :
    density A + density B - 1 ≤ density (A ∩ B) := by
  have h := density_union_add_density_inter A B
  have hu := density_le_one (A ∪ B)
  linarith

theorem density_union_le_add (A B : Finset α) :
    density (A ∪ B) ≤ density A + density B := by
  have h := density_union_add_density_inter A B
  have hi := density_nonneg (A ∩ B)
  linarith

theorem density_inter_le_left (A B : Finset α) : density (A ∩ B) ≤ density A :=
  density_mono Finset.inter_subset_left

theorem density_inter_le_right (A B : Finset α) : density (A ∩ B) ≤ density B :=
  density_mono Finset.inter_subset_right

theorem density_compl [Nonempty α] (A : Finset α) :
    density (Finset.univ \ A) = 1 - density A := by
  have h := density_sdiff_add_density_inter Finset.univ A
  simp at h
  unfold density
  linarith

end Lattice

end Density

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/SubspaceOps.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Operations on combinatorial subspaces for Erdős 171

This file supplies the algebra of subspaces used by the density argument.  In
particular, it contains composition, independent products and coordinate
concatenation.  The final section records carefully the two distinct operations
involving the inclusion `Fin k → Fin (k + 1)`:

* restrict the *parameters* of a large-alphabet subspace to the old alphabet;
* lift a small-alphabet subspace by mapping all of its fixed letters into the
  large alphabet.

A large-alphabet subspace can be turned back into a small-alphabet subspace
exactly when none of its fixed letters is the new last letter.
-/

section
open Combinatorics

section
open Combinatorics.Subspace

variable {η ζ ξ α ι κ υ : Type*}

/-- Composition of combinatorial subspaces.  The convention is functional:
`U.comp V` first evaluates `V` and then evaluates `U`. -/
private def _root_.Combinatorics.Subspace.comp (U : Subspace η α ι) (V : Subspace ζ α η) : Subspace ζ α ι where
  idxFun i := (U.idxFun i).elim Sum.inl V.idxFun
  proper z := by
    obtain ⟨e, he⟩ := V.proper z
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨i, by simp [hi, he]⟩

@[simp] private theorem _root_.Combinatorics.Subspace.comp_idxFun (U : Subspace η α ι) (V : Subspace ζ α η) (i : ι) :
    (U.comp V).idxFun i = (U.idxFun i).elim Sum.inl V.idxFun := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.comp_apply (U : Subspace η α ι) (V : Subspace ζ α η)
    (x : ζ → α) : U.comp V x = U (V x) := by
  funext i
  cases hi : U.idxFun i <;> simp [comp, coe_apply, hi]

private theorem _root_.Combinatorics.Subspace.comp_assoc (U : Subspace η α ι) (V : Subspace ζ α η)
    (W : Subspace ξ α ζ) :
    (U.comp V).comp W = U.comp (V.comp W) := by
  ext i
  cases hU : U.idxFun i with
  | inl a => simp [comp, hU]
  | inr e =>
      cases hV : V.idxFun e <;> simp [comp, hU, hV]

private theorem _root_.Combinatorics.Subspace.comp_parameter_injective (U : Subspace η α ι) (V : Subspace ζ α η) :
    Function.Injective (U.comp V) :=
  (U.comp V).parameter_injective

private theorem _root_.Combinatorics.Subspace.range_comp (U : Subspace η α ι) (V : Subspace ζ α η) :
    Set.range (U.comp V) = U '' Set.range V := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨V x, ⟨x, rfl⟩, (comp_apply U V x).symm⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, comp_apply U V x⟩

private theorem _root_.Combinatorics.Subspace.range_comp_subset_range (U : Subspace η α ι) (V : Subspace ζ α η) :
    Set.range (U.comp V) ⊆ Set.range U := by
  rw [range_comp]
  exact Set.image_subset_range U _

private theorem _root_.Combinatorics.Subspace.range_comp_subset_iff (U : Subspace η α ι) (V : Subspace ζ α η)
    (A : Set (ι → α)) :
    Set.range (U.comp V) ⊆ A ↔ Set.range V ⊆ U ⁻¹' A := by
  simp only [Set.range_subset_iff, Set.mem_preimage, comp_apply]

private theorem _root_.Combinatorics.Subspace.image_comp (U : Subspace η α ι) (V : Subspace ζ α η)
    (A : Set (ζ → α)) :
    U '' (V '' A) = U.comp V '' A := by
  rw [Set.image_image]
  simp only [comp_apply]

private theorem _root_.Combinatorics.Subspace.preimage_comp (U : Subspace η α ι) (V : Subspace ζ α η)
    (A : Set (ι → α)) :
    U.comp V ⁻¹' A = V ⁻¹' (U ⁻¹' A) := by
  ext x
  simp [comp_apply]

@[simp] private theorem _root_.Combinatorics.Subspace.lineMap_comp (U : Subspace η α ι) (V : Subspace ζ α η)
    (l : Line α ζ) :
    (U.comp V).lineMap l = U.lineMap (V.lineMap l) := by
  ext i
  cases hU : U.idxFun i with
  | inl a => simp [comp, lineMap, hU]
  | inr e =>
      cases hV : V.idxFun e <;> simp [comp, lineMap, hU, hV]

/-- Independent product of two subspaces.  Its parameter directions and its
ambient coordinates are both disjoint sums. -/
private def _root_.Combinatorics.Subspace.sum (U : Subspace η α ι) (V : Subspace ζ α κ) :
    Subspace (η ⊕ ζ) α (ι ⊕ κ) where
  idxFun
    | Sum.inl i => (U.idxFun i).map id Sum.inl
    | Sum.inr j => (V.idxFun j).map id Sum.inr
  proper
    | Sum.inl e => by
        obtain ⟨i, hi⟩ := U.proper e
        exact ⟨Sum.inl i, by simp [hi]⟩
    | Sum.inr f => by
        obtain ⟨j, hj⟩ := V.proper f
        exact ⟨Sum.inr j, by simp [hj]⟩

@[simp] private theorem _root_.Combinatorics.Subspace.sum_idxFun_inl (U : Subspace η α ι) (V : Subspace ζ α κ)
    (i : ι) :
    (U.sum V).idxFun (Sum.inl i) = (U.idxFun i).map id Sum.inl := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.sum_idxFun_inr (U : Subspace η α ι) (V : Subspace ζ α κ)
    (j : κ) :
    (U.sum V).idxFun (Sum.inr j) = (V.idxFun j).map id Sum.inr := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.sum_apply_inl (U : Subspace η α ι) (V : Subspace ζ α κ)
    (x : η ⊕ ζ → α) (i : ι) :
    U.sum V x (Sum.inl i) = U (x ∘ Sum.inl) i := by
  cases hi : U.idxFun i <;> simp [sum, coe_apply, hi]

@[simp] private theorem _root_.Combinatorics.Subspace.sum_apply_inr (U : Subspace η α ι) (V : Subspace ζ α κ)
    (x : η ⊕ ζ → α) (j : κ) :
    U.sum V x (Sum.inr j) = V (x ∘ Sum.inr) j := by
  cases hj : V.idxFun j <;> simp [sum, coe_apply, hj]

/-- Join two words on disjoint coordinate sets. -/
private def _root_.Combinatorics.Subspace.sumWord (x : η → α) (y : ζ → α) : η ⊕ ζ → α :=
  Sum.elim x y

@[simp] private theorem _root_.Combinatorics.Subspace.sumWord_inl (x : η → α) (y : ζ → α) (e : η) :
    sumWord x y (Sum.inl e) = x e := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.sumWord_inr (x : η → α) (y : ζ → α) (f : ζ) :
    sumWord x y (Sum.inr f) = y f := rfl

private theorem _root_.Combinatorics.Subspace.sumWord_injective :
    Function.Injective2 (sumWord : (η → α) → (ζ → α) → η ⊕ ζ → α) := by
  intro x y x' y' h
  constructor
  · funext e
    exact congrFun h (Sum.inl e)
  · funext f
    exact congrFun h (Sum.inr f)

@[simp] private theorem _root_.Combinatorics.Subspace.sum_apply_sumWord (U : Subspace η α ι) (V : Subspace ζ α κ)
    (x : η → α) (y : ζ → α) :
    U.sum V (sumWord x y) = sumWord (U x) (V y) := by
  have hx : sumWord x y ∘ Sum.inl = x := by funext e; rfl
  have hy : sumWord x y ∘ Sum.inr = y := by funext f; rfl
  funext q
  cases q with
  | inl i => simpa [hx] using sum_apply_inl U V (sumWord x y) i
  | inr j => simpa [hy] using sum_apply_inr U V (sumWord x y) j

private theorem _root_.Combinatorics.Subspace.sum_parameter_injective (U : Subspace η α ι) (V : Subspace ζ α κ) :
    Function.Injective (U.sum V) :=
  (U.sum V).parameter_injective

/-- Concatenate two ambient coordinate blocks while sharing the same parameter
directions. -/
private def _root_.Combinatorics.Subspace.concat (U : Subspace η α ι) (V : Subspace η α κ) :
    Subspace η α (ι ⊕ κ) where
  idxFun
    | Sum.inl i => U.idxFun i
    | Sum.inr j => V.idxFun j
  proper e := by
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨Sum.inl i, hi⟩

@[simp] private theorem _root_.Combinatorics.Subspace.concat_idxFun_inl (U : Subspace η α ι) (V : Subspace η α κ)
    (i : ι) : (U.concat V).idxFun (Sum.inl i) = U.idxFun i := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.concat_idxFun_inr (U : Subspace η α ι) (V : Subspace η α κ)
    (j : κ) : (U.concat V).idxFun (Sum.inr j) = V.idxFun j := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.concat_apply (U : Subspace η α ι) (V : Subspace η α κ)
    (x : η → α) :
    U.concat V x = sumWord (U x) (V x) := by
  funext q
  cases q with
  | inl i => simp [concat, coe_apply, sumWord]
  | inr j => simp [concat, coe_apply, sumWord]

private theorem _root_.Combinatorics.Subspace.concat_parameter_injective (U : Subspace η α ι) (V : Subspace η α κ) :
    Function.Injective (U.concat V) :=
  (U.concat V).parameter_injective

/-- Extend a subspace by a block of fixed suffix coordinates. -/
private def _root_.Combinatorics.Subspace.extendRightWord (U : Subspace η α ι) (y : κ → α) :
    Subspace η α (ι ⊕ κ) where
  idxFun
    | Sum.inl i => U.idxFun i
    | Sum.inr j => Sum.inl (y j)
  proper e := by
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨Sum.inl i, hi⟩

@[simp] private theorem _root_.Combinatorics.Subspace.extendRightWord_idxFun_inl (U : Subspace η α ι) (y : κ → α)
    (i : ι) : (U.extendRightWord y).idxFun (Sum.inl i) = U.idxFun i := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.extendRightWord_idxFun_inr (U : Subspace η α ι) (y : κ → α)
    (j : κ) : (U.extendRightWord y).idxFun (Sum.inr j) = Sum.inl (y j) := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.extendRightWord_apply (U : Subspace η α ι) (y : κ → α)
    (x : η → α) :
    U.extendRightWord y x = sumWord (U x) y := by
  funext q
  cases q with
  | inl i => simp [extendRightWord, coe_apply, sumWord]
  | inr j => simp [extendRightWord, coe_apply, sumWord]

private theorem _root_.Combinatorics.Subspace.extendRightWord_parameter_injective (U : Subspace η α ι) (y : κ → α) :
    Function.Injective (U.extendRightWord y) :=
  (U.extendRightWord y).parameter_injective

/-- The canonical coordinate face on the first `m₀` coordinates.  All later
coordinates are fixed at `default`. -/
private def _root_.Combinatorics.Subspace.coordinateFace {m₀ m : ℕ} [Inhabited α] (h : m₀ ≤ m) :
    Subspace (Fin m₀) α (Fin m) where
  idxFun i := if hi : i.val < m₀ then Sum.inr ⟨i.val, hi⟩ else Sum.inl default
  proper e := by
    refine ⟨Fin.castLE h e, ?_⟩
    simp [e.isLt]

@[simp] private theorem _root_.Combinatorics.Subspace.coordinateFace_idxFun_castLE {m₀ m : ℕ} [Inhabited α]
    (h : m₀ ≤ m) (e : Fin m₀) :
    (coordinateFace (α := α) h).idxFun (Fin.castLE h e) = Sum.inr e := by
  simp [coordinateFace, e.isLt]

@[simp] private theorem _root_.Combinatorics.Subspace.coordinateFace_apply_castLE {m₀ m : ℕ} [Inhabited α]
    (h : m₀ ≤ m) (x : Fin m₀ → α) (e : Fin m₀) :
    coordinateFace (α := α) h x (Fin.castLE h e) = x e := by
  rw [apply_inr (coordinateFace_idxFun_castLE h e)]

private theorem _root_.Combinatorics.Subspace.coordinateFace_apply {m₀ m : ℕ} [Inhabited α] (h : m₀ ≤ m)
    (x : Fin m₀ → α) (i : Fin m) :
    coordinateFace (α := α) h x i =
      if hi : i.val < m₀ then x ⟨i.val, hi⟩ else default := by
  by_cases hi : i.val < m₀ <;> simp [coordinateFace, coe_apply, hi]

private theorem _root_.Combinatorics.Subspace.coordinateFace_parameter_injective {m₀ m : ℕ} [Inhabited α]
    (h : m₀ ≤ m) :
    Function.Injective (coordinateFace (α := α) h) :=
  (coordinateFace (α := α) h).parameter_injective

@[simp] private theorem _root_.Combinatorics.Subspace.coordinateFace_comp {m₀ m₁ m₂ : ℕ} [Inhabited α]
    (h₀₁ : m₀ ≤ m₁) (h₁₂ : m₁ ≤ m₂) :
    (coordinateFace (α := α) h₁₂).comp (coordinateFace (α := α) h₀₁) =
      coordinateFace (α := α) (h₀₁.trans h₁₂) := by
  ext i
  by_cases h₀ : i.val < m₀
  · have h₁ : i.val < m₁ := lt_of_lt_of_le h₀ h₀₁
    simp [comp, coordinateFace, h₀, h₁]
  · by_cases h₁ : i.val < m₁ <;> simp [comp, coordinateFace, h₀, h₁]

/-- Map all fixed letters of a subspace through a function.  Variable
coordinates are unchanged. -/
private def _root_.Combinatorics.Subspace.mapAlphabet (U : Subspace η α ι) (f : α → υ) : Subspace η υ ι where
  idxFun i := (U.idxFun i).map f id
  proper e := by
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨i, by simp [hi]⟩

@[simp] private theorem _root_.Combinatorics.Subspace.mapAlphabet_idxFun (U : Subspace η α ι) (f : α → υ) (i : ι) :
    (U.mapAlphabet f).idxFun i = (U.idxFun i).map f id := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.mapAlphabet_apply (U : Subspace η α ι) (f : α → υ)
    (x : η → α) :
    U.mapAlphabet f (f ∘ x) = f ∘ U x := by
  funext i
  cases hi : U.idxFun i <;> simp [mapAlphabet, coe_apply, hi]

@[simp] private theorem _root_.Combinatorics.Subspace.mapAlphabet_id (U : Subspace η α ι) :
    U.mapAlphabet id = U := by
  ext i
  cases hi : U.idxFun i <;> simp [mapAlphabet, hi]

private theorem _root_.Combinatorics.Subspace.mapAlphabet_comp (U : Subspace η α ι) (f : α → υ) (g : υ → ξ) :
    (U.mapAlphabet f).mapAlphabet g = U.mapAlphabet (g ∘ f) := by
  ext i
  cases hi : U.idxFun i <;> simp [mapAlphabet, hi]

end

end



open Set

variable {η ζ α ι κ : Type*}

/-- The product set of two families of words on disjoint coordinate types. -/
def sumSet (A : Set (η → α)) (B : Set (ζ → α)) : Set (η ⊕ ζ → α) :=
  {x | (x ∘ Sum.inl) ∈ A ∧ (x ∘ Sum.inr) ∈ B}

@[simp] theorem mem_sumSet {A : Set (η → α)} {B : Set (ζ → α)}
    {x : η ⊕ ζ → α} :
    x ∈ sumSet A B ↔ (x ∘ Sum.inl) ∈ A ∧ (x ∘ Sum.inr) ∈ B :=
  Iff.rfl

@[simp] theorem sumWord_mem_sumSet {A : Set (η → α)} {B : Set (ζ → α)}
    {x : η → α} {y : ζ → α} :
    Combinatorics.Subspace.sumWord x y ∈ sumSet A B ↔ x ∈ A ∧ y ∈ B := by
  rfl

theorem range_sum (U : Combinatorics.Subspace η α ι)
    (V : Combinatorics.Subspace ζ α κ) :
    Set.range (U.sum V) = sumSet (Set.range U) (Set.range V) := by
  ext w
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨⟨z ∘ Sum.inl, by funext i; simp⟩,
      ⟨z ∘ Sum.inr, by funext j; simp⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨Combinatorics.Subspace.sumWord x y, ?_⟩
    rw [Combinatorics.Subspace.sum_apply_sumWord, hx, hy]
    funext q
    cases q <;> rfl

theorem preimage_sumSet (U : Combinatorics.Subspace η α ι)
    (V : Combinatorics.Subspace ζ α κ) (A : Set (ι → α)) (B : Set (κ → α)) :
    U.sum V ⁻¹' sumSet A B = sumSet (U ⁻¹' A) (V ⁻¹' B) := by
  ext x
  have hleft : (U.sum V x) ∘ Sum.inl = U (x ∘ Sum.inl) := by
    funext i
    exact U.sum_apply_inl V x i
  have hright : (U.sum V x) ∘ Sum.inr = V (x ∘ Sum.inr) := by
    funext j
    exact U.sum_apply_inr V x j
  simp only [Set.mem_preimage, mem_sumSet, hleft, hright]

section FinAlphabet

variable {k : ℕ}

/-- Include an old-alphabet word into the alphabet with one new last letter. -/
def liftWord (x : η → Fin k) : η → Fin (k + 1) :=
  fun e ↦ (x e).castSucc

@[simp] theorem liftWord_apply (x : η → Fin k) (e : η) :
    liftWord x e = (x e).castSucc := rfl

theorem liftWord_injective : Function.Injective (liftWord : (η → Fin k) → η → Fin (k + 1)) := by
  intro x y h
  funext e
  exact Fin.castSucc_injective k (congrFun h e)

/-- Image of a set of words under inclusion of the old alphabet. -/
def liftSet (A : Set (η → Fin k)) : Set (η → Fin (k + 1)) :=
  liftWord '' A

/-- Pull a set over the enlarged alphabet back to words using only old letters. -/
def restrictSet (B : Set (η → Fin (k + 1))) : Set (η → Fin k) :=
  liftWord ⁻¹' B

@[simp] theorem mem_restrictSet {B : Set (η → Fin (k + 1))} {x : η → Fin k} :
    x ∈ restrictSet B ↔ liftWord x ∈ B :=
  Iff.rfl

@[simp] theorem liftWord_mem_liftSet {A : Set (η → Fin k)} {x : η → Fin k} :
    liftWord x ∈ liftSet A ↔ x ∈ A := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (liftWord_injective hxy).symm ▸ hy
  · exact fun hx ↦ ⟨x, hx, rfl⟩

@[simp] theorem restrictSet_liftSet (A : Set (η → Fin k)) :
    restrictSet (liftSet A) = A := by
  ext x
  simp

theorem liftSet_restrictSet (B : Set (η → Fin (k + 1))) :
    liftSet (restrictSet B) = B ∩ Set.range liftWord := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, ⟨y, rfl⟩⟩
  · rintro ⟨hx, y, rfl⟩
    exact ⟨y, hx, rfl⟩

/-- Finset version of `liftSet`. -/
def liftFinset [DecidableEq (η → Fin (k + 1))] (A : Finset (η → Fin k)) :
    Finset (η → Fin (k + 1)) :=
  A.map ⟨liftWord, liftWord_injective⟩

@[simp] theorem mem_liftFinset [DecidableEq (η → Fin (k + 1))]
    {A : Finset (η → Fin k)} {x : η → Fin k} :
    liftWord x ∈ liftFinset A ↔ x ∈ A := by
  simp [liftFinset, liftWord_injective.eq_iff]

@[simp] theorem card_liftFinset [DecidableEq (η → Fin (k + 1))]
    (A : Finset (η → Fin k)) :
    (liftFinset A).card = A.card := by
  simp [liftFinset]

end FinAlphabet



section
open Combinatorics

section
open Combinatorics.Subspace

open Erdos171

variable {η ι : Type*} {k : ℕ}

/-- Lift a small-alphabet subspace into the alphabet with one new last letter. -/
private def _root_.Combinatorics.Subspace.finLift (U : Subspace η (Fin k) ι) : Subspace η (Fin (k + 1)) ι :=
  U.mapAlphabet Fin.castSucc

@[simp] private theorem _root_.Combinatorics.Subspace.finLift_apply (U : Subspace η (Fin k) ι) (x : η → Fin k) :
    U.finLift (liftWord x) = liftWord (U x) := by
  exact U.mapAlphabet_apply Fin.castSucc x

private theorem _root_.Combinatorics.Subspace.finLift_parameter_injective (U : Subspace η (Fin k) ι) :
    Function.Injective U.finLift :=
  U.finLift.parameter_injective

/-- A large-alphabet subspace has only old fixed letters. -/
private def _root_.Combinatorics.Subspace.FixedLettersOld (U : Subspace η (Fin (k + 1)) ι) : Prop :=
  ∀ i a, U.idxFun i = Sum.inl a → a ≠ Fin.last k

private theorem _root_.Combinatorics.Subspace.FixedLettersOld.ne_last {U : Subspace η (Fin (k + 1)) ι}
    (hU : U.FixedLettersOld) {i : ι} {a : Fin (k + 1)}
    (hi : U.idxFun i = Sum.inl a) : a ≠ Fin.last k :=
  hU i a hi

private theorem _root_.Combinatorics.Subspace.finLift_fixedLettersOld (U : Subspace η (Fin k) ι) :
    U.finLift.FixedLettersOld := by
  intro i a hi ha
  cases hU : U.idxFun i with
  | inl b =>
      have hab : b.castSucc = a := by simpa [finLift, mapAlphabet, hU] using hi
      rw [← hab] at ha
      exact Fin.castSucc_ne_last b ha
  | inr e =>
      simp [finLift, mapAlphabet, hU] at hi

/-- A total retraction from `Fin (k + 1)` to the old alphabet.  Its value on the
new last letter is irrelevant; on every old letter it is inverse to
`Fin.castSucc`. -/
private def _root_.Combinatorics.Subspace.dropLast [Inhabited (Fin k)] (a : Fin (k + 1)) : Fin k :=
  if h : a = Fin.last k then default else a.castPred h

@[simp] private theorem _root_.Combinatorics.Subspace.dropLast_castSucc [Inhabited (Fin k)] (a : Fin k) :
    dropLast a.castSucc = a := by
  simp [dropLast, Fin.castSucc_ne_last, Fin.castPred_castSucc]

private theorem _root_.Combinatorics.Subspace.castSucc_dropLast [Inhabited (Fin k)] {a : Fin (k + 1)}
    (ha : a ≠ Fin.last k) :
    (dropLast a).castSucc = a := by
  simp [dropLast, ha, Fin.castSucc_castPred]

/-- Restrict the fixed letters of a large-alphabet subspace through `dropLast`.
When all fixed letters are old, `finLift` recovers the original subspace. -/
private def _root_.Combinatorics.Subspace.finRestrict [Inhabited (Fin k)] (U : Subspace η (Fin (k + 1)) ι) :
    Subspace η (Fin k) ι :=
  U.mapAlphabet dropLast

@[simp] private theorem _root_.Combinatorics.Subspace.finRestrict_apply
    [Inhabited (Fin k)]
    (U : Subspace η (Fin (k + 1)) ι)
    (hU : U.FixedLettersOld) (x : η → Fin k) :
    liftWord (U.finRestrict x) = U (liftWord x) := by
  funext i
  cases hi : U.idxFun i with
  | inl a =>
      simp [finRestrict, mapAlphabet, coe_apply, hi,
        castSucc_dropLast (hU.ne_last hi)]
  | inr e =>
      simp [finRestrict, mapAlphabet, coe_apply, hi]

@[simp] private theorem _root_.Combinatorics.Subspace.finRestrict_finLift [Inhabited (Fin k)]
    (U : Subspace η (Fin k) ι) :
    U.finLift.finRestrict = U := by
  ext i
  cases hi : U.idxFun i with
  | inl a =>
      simp [finRestrict, finLift, mapAlphabet, hi]
  | inr e =>
      simp [finRestrict, finLift, mapAlphabet, hi]

@[simp] private theorem _root_.Combinatorics.Subspace.finLift_finRestrict
    [Inhabited (Fin k)]
    (U : Subspace η (Fin (k + 1)) ι)
    (hU : U.FixedLettersOld) :
    U.finRestrict.finLift = U := by
  ext i
  cases hi : U.idxFun i with
  | inl a =>
      simp [finRestrict, finLift, mapAlphabet, hi,
        castSucc_dropLast (hU.ne_last hi)]
  | inr e =>
      simp [finRestrict, finLift, mapAlphabet, hi]

end

end



open Set

variable {η ι : Type*} {k : ℕ}

section FinAlphabet

/-- Pull back an ambient set along a subspace while restricting its parameters
to old-alphabet words. -/
def restrictedPreimage (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Set (ι → Fin (k + 1))) : Set (η → Fin k) :=
  {x | U (liftWord x) ∈ A}

@[simp] theorem mem_restrictedPreimage
    {U : Combinatorics.Subspace η (Fin (k + 1)) ι}
    {A : Set (ι → Fin (k + 1))} {x : η → Fin k} :
    x ∈ restrictedPreimage U A ↔ U (liftWord x) ∈ A :=
  Iff.rfl

theorem restrictedPreimage_eq (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Set (ι → Fin (k + 1))) :
    restrictedPreimage U A = liftWord ⁻¹' (U ⁻¹' A) :=
  rfl

theorem restricted_image_subset_iff
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Set (ι → Fin (k + 1))) (B : Set (η → Fin k)) :
    (fun x ↦ U (liftWord x)) '' B ⊆ A ↔ B ⊆ restrictedPreimage U A := by
  rw [Set.image_subset_iff]
  rfl

theorem restricted_range_subset_iff
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Set (ι → Fin (k + 1))) :
    Set.range (fun x ↦ U (liftWord x)) ⊆ A ↔ restrictedPreimage U A = Set.univ := by
  rw [Set.range_subset_iff]
  constructor
  · intro h
    ext x
    simp [h]
  · intro h x
    have hx : x ∈ restrictedPreimage U A := by rw [h]; trivial
    exact hx

theorem restricted_parameter_injective
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι) :
    Function.Injective (fun x : η → Fin k ↦ U (liftWord x)) :=
  U.parameter_injective.comp liftWord_injective

end FinAlphabet

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/Framework.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Finitary density-Hales--Jewett frameworks

The density of a finset in Mathlib is an exact nonnegative rational number.
This file records two equivalent quantifier arrangements for density
Hales--Jewett: it is enough to obtain one dimension for each positive density,
because a dense fibre in every larger cube contains the same line.  We also
state the corresponding finite-dimensional-subspace property.
-/



open scoped BigOperators

/-- A set of words contains an `m`-dimensional combinatorial subspace. -/
def ContainsSubspace (m : ℕ) {t n : ℕ} (A : Set (Word t n)) : Prop :=
  ∃ U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n), Set.range U ⊆ A

theorem containsSubspace_iff (m : ℕ) {t n : ℕ} {A : Set (Word t n)} :
    ContainsSubspace m A ↔
      ∃ U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n),
        ∀ x : Word t m, U x ∈ A := by
  constructor
  · rintro ⟨U, hU⟩
    exact ⟨U, fun x ↦ hU ⟨x, rfl⟩⟩
  · rintro ⟨U, hU⟩
    refine ⟨U, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hU x

/-- One-witness formulation of density Hales--Jewett. -/
def FiniteDensityHJ (t : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n : ℕ, ∀ A : Finset (Word t n),
      δ ≤ density A → ContainsLine (A : Set (Word t n))

/-- Eventual formulation of density Hales--Jewett. -/
def EventualDensityHJ (t : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ A : Finset (Word t n),
      δ ≤ density A → ContainsLine (A : Set (Word t n))

/-- The one-witness formulation for an `m`-dimensional subspace. -/
def FiniteDensityMDHJ (t m : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n : ℕ, ∀ A : Finset (Word t n),
      δ ≤ density A → ContainsSubspace m (A : Set (Word t n))

/-- The eventual formulation for an `m`-dimensional subspace. -/
def EventualDensityMDHJ (t m : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ A : Finset (Word t n),
      δ ≤ density A → ContainsSubspace m (A : Set (Word t n))

/-- Split a word into an initial and a final block. -/
def wordAddEquiv (t m r : ℕ) : Word t (m + r) ≃ Word t m × Word t r :=
  (Equiv.piCongrLeft (fun _ : Fin (m + r) ↦ Fin t) finSumFinEquiv).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin r) (Fin t))

@[simp] theorem wordAddEquiv_apply_fst (t m r : ℕ) (w : Word t (m + r))
    (i : Fin m) : (wordAddEquiv t m r w).1 i = w (Fin.castAdd r i) := by
  simp [wordAddEquiv]

@[simp] theorem wordAddEquiv_apply_snd (t m r : ℕ) (w : Word t (m + r))
    (i : Fin r) : (wordAddEquiv t m r w).2 i = w (Fin.natAdd m i) := by
  simp [wordAddEquiv]

/-- Split a word, with the final block placed first for fibrewise counting. -/
def wordFiberEquiv (t m r : ℕ) : Word t (m + r) ≃ Word t r × Word t m :=
  (wordAddEquiv t m r).trans (Equiv.prodComm _ _)

/-- A line on an initial block, extended by a fixed final block. -/
def extendLineRight {t m r : ℕ}
    (l : Combinatorics.Line (Fin t) (Fin m)) (z : Word t r) :
    Combinatorics.Line (Fin t) (Fin (m + r)) where
  idxFun i := match finSumFinEquiv.symm i with
    | Sum.inl j => l.idxFun j
    | Sum.inr j => some (z j)
  proper := by
    obtain ⟨j, hj⟩ := l.proper
    exact ⟨Fin.castAdd r j, by simp [hj]⟩

@[simp] theorem extendLineRight_apply {t m r : ℕ}
    (l : Combinatorics.Line (Fin t) (Fin m)) (z : Word t r) (a : Fin t) :
    wordFiberEquiv t m r (extendLineRight l z a) = (z, l a) := by
  apply Prod.ext
  · funext i
    change extendLineRight l z a (Fin.natAdd m i) = z i
    simp [extendLineRight, Combinatorics.Line.coe_apply]
  · funext i
    change extendLineRight l z a (Fin.castAdd r i) = l a i
    simp [extendLineRight, Combinatorics.Line.coe_apply]

/-- Regard a combinatorial line as a one-dimensional subspace. -/
def lineSubspace {α ι : Type*} (l : Combinatorics.Line α ι) :
    Combinatorics.Subspace (Fin 1) α ι where
  idxFun i := (l.idxFun i).elim (Sum.inr 0) Sum.inl
  proper e := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i, by simp [hi, Fin.eq_zero e]⟩

@[simp] theorem lineSubspace_apply {α ι : Type*} (l : Combinatorics.Line α ι)
    (x : Fin 1 → α) : lineSubspace l x = l (x 0) := by
  funext i
  cases hi : l.idxFun i <;>
    simp [lineSubspace, Combinatorics.Line.coe_apply,
      Combinatorics.Subspace.coe_apply, hi]

/-- Independently join an `m`-subspace on an initial coordinate block and a
line on a final coordinate block. -/
def appendSubspaceLine {t m n r : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n))
    (l : Combinatorics.Line (Fin t) (Fin r)) :
    Combinatorics.Subspace (Fin (m + 1)) (Fin t) (Fin (n + r)) :=
  (U.sum (lineSubspace l)).reindex finSumFinEquiv (Equiv.refl _) finSumFinEquiv

@[simp] theorem wordAddEquiv_appendSubspaceLine_apply {t m n r : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n))
    (l : Combinatorics.Line (Fin t) (Fin r))
    (x : Word t (m + 1)) :
    wordAddEquiv t n r (appendSubspaceLine U l x) =
      (U (fun i ↦ x (Fin.castAdd 1 i)), l (x (Fin.last m))) := by
  apply Prod.ext
  · funext i
    simp only [wordAddEquiv_apply_fst, appendSubspaceLine,
      Combinatorics.Subspace.reindex_apply, Equiv.refl_apply,
      Equiv.refl_symm, finSumFinEquiv_symm_apply_castAdd,
      Combinatorics.Subspace.sum_apply_inl, Function.comp_apply,
      finSumFinEquiv_apply_left]
    have hf :
        ((⇑(Equiv.refl (Fin t)) ∘ x ∘ ⇑finSumFinEquiv) ∘ Sum.inl) =
          (fun j : Fin m ↦ x (Fin.castAdd 1 j)) := by
      funext j
      simp
    rw [hf]
  · funext i
    simp only [wordAddEquiv_apply_snd, appendSubspaceLine,
      Combinatorics.Subspace.reindex_apply, Equiv.refl_apply,
      Equiv.refl_symm, finSumFinEquiv_symm_apply_natAdd,
      Combinatorics.Subspace.sum_apply_inr, Function.comp_apply,
      lineSubspace_apply]
    have hz : Fin.natAdd m (0 : Fin 1) = Fin.last m := by ext; simp
    rw [finSumFinEquiv_apply_right, hz]

/-- Extend a subspace on an initial coordinate block by a fixed final word. -/
def extendSubspaceRight {t m n r : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n)) (z : Word t r) :
    Combinatorics.Subspace (Fin m) (Fin t) (Fin (n + r)) :=
  (U.extendRightWord z).reindex (Equiv.refl _) (Equiv.refl _) finSumFinEquiv

@[simp] theorem extendSubspaceRight_apply {t m n r : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n)) (z : Word t r)
    (x : Word t m) :
    wordFiberEquiv t n r (extendSubspaceRight U z x) = (z, U x) := by
  apply Prod.ext
  · funext i
    change extendSubspaceRight U z x (Fin.natAdd n i) = z i
    simp [extendSubspaceRight, Combinatorics.Subspace.reindex_apply]
  · funext i
    change extendSubspaceRight U z x (Fin.castAdd r i) = U x i
    simp [extendSubspaceRight, Combinatorics.Subspace.reindex_apply]

/-- Some fibre of a nonempty finite product has density at least the density of
the whole set.  This is the exact finite averaging principle needed for
cylinder lifting. -/
theorem exists_fiber_density_ge {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (A : Finset (X × Y)) :
    ∃ x : X, density A ≤ density (fiber A x) := by
  rw [density_eq_average_fiber]
  exact exists_average_le _

/-- The graph of a finite colouring, restricted to a finset. -/
noncomputable def colorGraph {X C : Type*} (D : Finset X) (color : X → C) :
    Finset (C × X) := by
  classical
  exact D.map
    ⟨fun x ↦ (color x, x), fun _ _ h ↦ congrArg Prod.snd h⟩

@[simp] theorem mem_colorGraph {X C : Type*} (D : Finset X) (color : X → C)
    (c : C) (x : X) :
    (c, x) ∈ colorGraph D color ↔ x ∈ D ∧ color x = c := by
  classical
  constructor
  · rw [colorGraph, Finset.mem_map]
    rintro ⟨y, hy, hpair⟩
    have hyx : y = x := congrArg Prod.snd hpair
    subst y
    exact ⟨hy, congrArg Prod.fst hpair⟩
  · rintro ⟨hx, hcolor⟩
    rw [colorGraph, Finset.mem_map]
    exact ⟨x, hx, Prod.ext hcolor rfl⟩

theorem density_colorGraph {X C : Type*} [Fintype X] [Fintype C]
    (D : Finset X) (color : X → C) :
    density (colorGraph D color) = density D / Fintype.card C := by
  classical
  simp only [density_eq_card_div_card, colorGraph, Finset.card_map, Fintype.card_prod]
  push_cast
  ring

/-- One colour class, regarded as a finset in the original ambient type. -/
noncomputable def colorClass {X C : Type*} [Fintype X]
    (D : Finset X) (color : X → C) (c : C) : Finset X := by
  classical
  exact Finset.univ.filter fun x ↦ x ∈ D ∧ color x = c

@[simp] theorem mem_colorClass {X C : Type*} [Fintype X]
    (D : Finset X) (color : X → C) (c : C) (x : X) :
    x ∈ colorClass D color c ↔ x ∈ D ∧ color x = c := by
  classical
  simp [colorClass]

/-- A finite colouring has a colour class whose ambient density is at least
the density of the coloured set divided by the number of colours. -/
theorem exists_dense_colorClass {X C : Type*} [Fintype X] [Fintype C]
    [Nonempty X] [Nonempty C] (D : Finset X) (color : X → C) :
    ∃ c : C, density D / Fintype.card C ≤
      density (colorClass D color c) := by
  classical
  obtain ⟨c, hc⟩ := exists_fiber_density_ge (colorGraph D color)
  have hfiber : fiber (colorGraph D color) c = colorClass D color c := by
    ext x
    simp
  refine ⟨c, ?_⟩
  rw [density_colorGraph] at hc
  simpa only [hfiber] using hc

/-- A single witnessing dimension for every positive density automatically
works in every larger dimension. -/
theorem FiniteDensityHJ.eventual {t : ℕ} (h : FiniteDensityHJ t) (ht : 0 < t) :
    EventualDensityHJ t := by
  intro δ hδ
  obtain ⟨m, hm⟩ := h δ hδ
  refine ⟨m, ?_⟩
  intro n hmn A hA
  letI : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hmn
  classical
  let e := wordFiberEquiv t m r
  let B : Finset (Word t r × Word t m) := A.map e.toEmbedding
  have hB : δ ≤ density B := by
    change δ ≤ density (A.map e.toEmbedding)
    rw [density_map_equiv]
    exact hA
  obtain ⟨z, hz⟩ := exists_fiber_density_ge B
  obtain ⟨l, hl⟩ := hm (fiber B z) (hB.trans hz)
  refine ⟨extendLineRight l z, ?_⟩
  rintro _ ⟨a, rfl⟩
  have hmemB : (z, l a) ∈ B := (mem_fiber B z (l a)).1 (hl ⟨a, rfl⟩)
  have hmemA : e.symm (z, l a) ∈ A := by simpa [B] using hmemB
  have heq : e.symm (z, l a) = extendLineRight l z a := by
    apply e.injective
    simp [e]
  simpa [heq] using hmemA

/-- Density Hales--Jewett implies its finite-dimensional version.  The proof
is the standard dense-fibre induction: choose a line in every dense suffix
fibre, pigeonhole a common line, find an `m`-subspace in its prefix colour
class, and take the independent sum. -/
theorem FiniteDensityHJ.finiteDensityMDHJ {t : ℕ} (h : FiniteDensityHJ t)
    (ht : 0 < t) (m : ℕ) : FiniteDensityMDHJ t m := by
  letI : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  induction m with
  | zero =>
      intro δ hδ
      refine ⟨0, ?_⟩
      intro A hA
      have hApos : 0 < density A := hδ.trans_le hA
      have hAne : A.Nonempty := (density_pos A).1 hApos
      let U : Combinatorics.Subspace (Fin 0) (Fin t) (Fin 0) :=
        { idxFun := Fin.elim0
          proper := fun e ↦ Fin.elim0 e }
      refine ⟨U, ?_⟩
      rintro _ ⟨x, rfl⟩
      obtain ⟨w, hw⟩ := hAne
      change U x ∈ A
      rw [Subsingleton.elim (U x) w]
      exact hw
  | succ m ih =>
      intro δ hδ
      by_cases hδ1 : δ ≤ 1
      swap
      · refine ⟨0, ?_⟩
        intro A hA
        exfalso
        exact hδ1 (hA.trans (density_le_one A))
      have hδhalf : 0 < δ / 2 := half_pos hδ
      obtain ⟨r, hr⟩ := h (δ / 2) hδhalf
      have huniv : δ / 2 ≤ density (Finset.univ : Finset (Word t r)) := by
        rw [density_univ]
        linarith
      obtain ⟨l₀, hl₀⟩ := hr Finset.univ huniv
      letI : Nonempty (Combinatorics.Line (Fin t) (Fin r)) := ⟨l₀⟩
      have hq : (0 : ℝ) < Fintype.card (Combinatorics.Line (Fin t) (Fin r)) := by
        positivity
      have htheta : 0 <
          δ / (2 * Fintype.card (Combinatorics.Line (Fin t) (Fin r))) := by
        exact div_pos hδ (mul_pos (by norm_num) hq)
      obtain ⟨n, hn⟩ := ih _ htheta
      refine ⟨n + r, ?_⟩
      intro A hA
      classical
      let e := wordAddEquiv t n r
      let B : Finset (Word t n × Word t r) := A.map e.toEmbedding
      have hB : δ ≤ density B := by
        change δ ≤ density (A.map e.toEmbedding)
        rw [density_map_equiv]
        exact hA
      let f : Word t n → ℝ := fun x ↦ density (fiber B x)
      let D : Finset (Word t n) := superlevel f (δ / 2)
      have havg : δ ≤ average f := by
        change δ ≤ average fun x ↦ density (fiber B x)
        rw [← density_eq_average_fiber]
        exact hB
      have hD : δ / 2 ≤ density D := by
        apply half_le_density_superlevel f (le_of_lt hδ) havg
        intro x
        exact density_le_one _
      let selected : Word t n → Combinatorics.Line (Fin t) (Fin r) := fun x ↦
        if hx : x ∈ D then
          Classical.choose (hr (fiber B x) ((mem_superlevel f (δ / 2) x).1 hx))
        else l₀
      have hselected (x : Word t n) (hx : x ∈ D) :
          Set.range (selected x) ⊆ (fiber B x : Set (Word t r)) := by
        dsimp only [selected]
        rw [dif_pos hx]
        exact Classical.choose_spec
          (hr (fiber B x) ((mem_superlevel f (δ / 2) x).1 hx))
      obtain ⟨l, hl⟩ := exists_dense_colorClass D selected
      have hclass :
          δ / (2 * Fintype.card (Combinatorics.Line (Fin t) (Fin r))) ≤
            density (colorClass D selected l) := by
        have hdiv := div_le_div_of_nonneg_right hD (le_of_lt hq)
        have heq :
            δ / (2 * Fintype.card (Combinatorics.Line (Fin t) (Fin r))) =
              (δ / 2) / Fintype.card (Combinatorics.Line (Fin t) (Fin r)) := by
          ring
        rw [heq]
        exact hdiv.trans hl
      obtain ⟨U, hU⟩ := hn (colorClass D selected l) hclass
      refine ⟨appendSubspaceLine U l, ?_⟩
      rintro _ ⟨x, rfl⟩
      let xp : Word t m := fun i ↦ x (Fin.castAdd 1 i)
      have hprefix : U xp ∈ colorClass D selected l := hU ⟨xp, rfl⟩
      have hprefix' : U xp ∈ D ∧ selected (U xp) = l :=
        (mem_colorClass D selected l (U xp)).1 hprefix
      have hsuffix : l (x (Fin.last m)) ∈ fiber B (U xp) := by
        rw [← hprefix'.2]
        exact hselected (U xp) hprefix'.1 ⟨x (Fin.last m), rfl⟩
      have hpair : (U xp, l (x (Fin.last m))) ∈ B :=
        (mem_fiber B (U xp) (l (x (Fin.last m)))).1 hsuffix
      have hmemA : e.symm (U xp, l (x (Fin.last m))) ∈ A := by
        simpa [B] using hpair
      have heval :
          e.symm (U xp, l (x (Fin.last m))) = appendSubspaceLine U l x := by
        apply e.injective
        simpa [e, xp] using wordAddEquiv_appendSubspaceLine_apply U l x
      simpa [heval] using hmemA

/-- As for lines, a single witnessing dimension for an `m`-subspace works in
every larger dimension by fixing a dense fibre. -/
theorem FiniteDensityMDHJ.eventual {t m : ℕ} (h : FiniteDensityMDHJ t m)
    (ht : 0 < t) : EventualDensityMDHJ t m := by
  intro δ hδ
  obtain ⟨n₀, hn₀⟩ := h δ hδ
  refine ⟨n₀, ?_⟩
  intro n hn A hA
  letI : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  classical
  let e := wordFiberEquiv t n₀ r
  let B : Finset (Word t r × Word t n₀) := A.map e.toEmbedding
  have hB : δ ≤ density B := by
    change δ ≤ density (A.map e.toEmbedding)
    rw [density_map_equiv]
    exact hA
  obtain ⟨z, hz⟩ := exists_fiber_density_ge B
  obtain ⟨U, hU⟩ := hn₀ (fiber B z) (hB.trans hz)
  refine ⟨extendSubspaceRight U z, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hmemB : (z, U x) ∈ B := (mem_fiber B z (U x)).1 (hU ⟨x, rfl⟩)
  have hmemA : e.symm (z, U x) ∈ A := by simpa [B] using hmemB
  have heq : e.symm (z, U x) = extendSubspaceRight U z x := by
    apply e.injective
    simp [e]
  simpa [heq] using hmemA

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/Iteration.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Iterating a density increment

This file contains the final, purely formal iteration in the density
Hales--Jewett argument.  The combinatorial input is isolated in
`DensityIncrementStep`: at a fixed baseline density it supplies one positive
increment, and for every requested output dimension it supplies an ambient
dimension in which every sufficiently dense family either already contains a
line or has increased pullback density on a subspace of the requested
dimension.

Starting from the last requested dimension, `backwardDimension` recursively
chooses all preceding ambient dimensions.  Thus every increment lands in
exactly the cube needed for the next increment.  After sufficiently many
iterations the density would exceed one, contradicting `density_le_one`.

There is no assumed density-increment theorem in this file.  All uses of the
combinatorial increment are explicit hypotheses to the implication theorems
at the end of the file.
-/



open Combinatorics

/-- Density Hales--Jewett at one fixed density. -/
def FiniteDensityHJAt (t : ℕ) (delta : ℝ) : Prop :=
  ∃ n : ℕ, ∀ A : Finset (Word t n),
    delta ≤ density A → ContainsLine (A : Set (Word t n))

theorem finiteDensityHJ_iff_forall_at {t : ℕ} :
    FiniteDensityHJ t ↔ ∀ delta : ℝ, 0 < delta → FiniteDensityHJAt t delta := by
  rfl

/-- Pull an ambient family back to the parameter cube of a subspace.  This
local version keeps the iteration independent of the later quantitative
subspace-density API. -/
noncomputable def iterationPullback {d t n : ℕ}
    (U : Subspace (Fin d) (Fin t) (Fin n)) (A : Finset (Word t n)) :
    Finset (Word t d) := by
  classical
  exact Finset.univ.filter fun x ↦ U x ∈ A

@[simp] theorem mem_iterationPullback {d t n : ℕ}
    (U : Subspace (Fin d) (Fin t) (Fin n)) (A : Finset (Word t n))
    (x : Word t d) :
    x ∈ iterationPullback U A ↔ U x ∈ A := by
  classical
  simp [iterationPullback]

/-- The abstract combinatorial input required by the density-increment
iteration at one fixed baseline density.

The threshold is recorded as a function of the desired target dimension.  It
is enough to state the conclusion at that threshold itself: `FiniteDensityHJ`
only asks for one witnessing dimension.  An eventual density-increment lemma
specializes to this form by using its threshold as the ambient dimension. -/
structure DensityIncrementStep (t : ℕ) (delta : ℝ) where
  /-- The density gain, uniform over all current densities at least `delta`. -/
  increment : ℝ
  increment_pos : 0 < increment
  /-- An ambient dimension for each desired output dimension. -/
  threshold : ℕ → ℕ
  /-- Either a line is already present, or restriction to a subspace raises
  the current density by at least `increment`. -/
  force :
    ∀ d : ℕ, ∀ A : Finset (Word t (threshold d)),
      delta ≤ density A →
        ContainsLine (A : Set (Word t (threshold d))) ∨
          ∃ U : Subspace (Fin d) (Fin t) (Fin (threshold d)),
            density A + increment ≤ density (iterationPullback U A)

namespace DensityIncrementStep

variable {t : ℕ} {delta : ℝ}

/-- Dimensions selected backwards from the terminal cube.  To perform
`r + 1` increments, first work in `threshold (backwardDimension r)` and ask
the increment step to return a `backwardDimension r`-dimensional subspace. -/
def backwardDimension (step : DensityIncrementStep t delta) : ℕ → ℕ
  | 0 => 0
  | r + 1 => step.threshold (backwardDimension step r)

@[simp] theorem backwardDimension_zero (step : DensityIncrementStep t delta) :
    backwardDimension step 0 = 0 := rfl

@[simp] theorem backwardDimension_succ (step : DensityIncrementStep t delta)
    (r : ℕ) :
    backwardDimension step (r + 1) =
      step.threshold (backwardDimension step r) := rfl

/-- A line in the finite pullback of a family gives a line in the family. -/
theorem containsLine_of_pullbackFinset
    {d n : ℕ} (U : Subspace (Fin d) (Fin t) (Fin n))
    (A : Finset (Word t n))
    (h : ContainsLine
      ((iterationPullback U A : Finset (Word t d)) : Set (Word t d))) :
    ContainsLine (A : Set (Word t n)) := by
  apply containsLine_of_subspace_preimage U
  have hpull :
      ((iterationPullback U A : Finset (Word t d)) : Set (Word t d)) =
        U ⁻¹' (A : Set (Word t n)) := by
    ext x
    simp
  rw [← hpull]
  exact h

/-- After `r` successful increments, either a line has appeared or a family
in the terminal zero-dimensional cube has density at least the initial
density plus `r * increment`.

This is the backward-dimension recursion.  The line branch is transported
out of every pullback immediately, so the conclusion always concerns the
family with which the recursion was started. -/
theorem iterate_or_terminal_density (step : DensityIncrementStep t delta) :
    ∀ r : ℕ, ∀ A : Finset (Word t (backwardDimension step r)),
      delta ≤ density A →
        ContainsLine
            (A : Set (Word t (backwardDimension step r))) ∨
          ∃ B : Finset (Word t (backwardDimension step 0)),
            density A + (r : ℝ) * step.increment ≤ density B := by
  intro r
  induction r with
  | zero =>
      intro A _hA
      right
      exact ⟨A, by simpa using (le_refl (density A))⟩
  | succ r ih =>
      intro A hA
      rcases step.force (backwardDimension step r) A hA with hline | ⟨U, hU⟩
      · exact Or.inl hline
      · have hBdelta : delta ≤ density (iterationPullback U A) := by
          calc
            delta ≤ density A := hA
            _ ≤ density A + step.increment :=
              le_add_of_nonneg_right step.increment_pos.le
            _ ≤ density (iterationPullback U A) := hU
        rcases ih (iterationPullback U A) hBdelta with hlineB | ⟨C, hC⟩
        · exact Or.inl (containsLine_of_pullbackFinset U A hlineB)
        · right
          refine ⟨C, ?_⟩
          calc
            density A + ((r + 1 : ℕ) : ℝ) * step.increment =
                (density A + step.increment) +
                  (r : ℝ) * step.increment := by
                    rw [Nat.cast_add, Nat.cast_one]
                    ring
            _ ≤ density (iterationPullback U A) +
                (r : ℝ) * step.increment :=
              add_le_add hU le_rfl
            _ ≤ density C := hC

/-- A uniform positive density increment at `delta` proves density
Hales--Jewett at `delta`. -/
theorem finiteDensityHJAt (step : DensityIncrementStep t delta) :
    FiniteDensityHJAt t delta := by
  obtain ⟨r, hr⟩ := exists_lt_nsmul step.increment_pos (1 - delta)
  have hr' : 1 - delta < (r : ℝ) * step.increment := by
    simpa using hr
  have hone : 1 < delta + (r : ℝ) * step.increment := by
    linarith
  refine ⟨backwardDimension step r, ?_⟩
  intro A hA
  rcases iterate_or_terminal_density step r A hA with hline | ⟨B, hB⟩
  · exact hline
  · exfalso
    have hlarge : 1 < density B := by
      calc
        1 < delta + (r : ℝ) * step.increment := hone
        _ ≤ density A + (r : ℝ) * step.increment :=
          add_le_add hA le_rfl
        _ ≤ density B := hB
    exact (not_lt_of_ge (density_le_one B)) hlarge

end DensityIncrementStep

/-- If the density-increment statement is available at every positive
density, then the finite density Hales--Jewett theorem follows. -/
theorem finiteDensityHJ_of_densityIncrement
    {t : ℕ}
    (step : ∀ delta : ℝ, 0 < delta → DensityIncrementStep t delta) :
    FiniteDensityHJ t := by
  intro delta hdelta
  exact (step delta hdelta).finiteDensityHJAt

/-- Successor-alphabet packaging of the iteration.  A proof of the
combinatorial increment for the `(k+1)`-letter alphabet at every positive
density is exactly what remains after the density-increment argument has used
the induction hypothesis for the `k`-letter alphabet. -/
theorem finiteDensityHJ_succ_of_densityIncrement
    {k : ℕ}
    (step : ∀ delta : ℝ, 0 < delta → DensityIncrementStep (k + 1) delta) :
    FiniteDensityHJ (k + 1) :=
  finiteDensityHJ_of_densityIncrement step

/-- Alphabet-induction interface in a form convenient for the eventual DKT
increment theorem: that theorem may consume the induction hypothesis and
return all successor-alphabet increment steps. -/
theorem FiniteDensityHJ.succ_of_densityIncrement
    {k : ℕ} (hk : FiniteDensityHJ k)
    (step : FiniteDensityHJ k →
      ∀ delta : ℝ, 0 < delta → DensityIncrementStep (k + 1) delta) :
    FiniteDensityHJ (k + 1) :=
  finiteDensityHJ_succ_of_densityIncrement (step hk)

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/Insensitive.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Insensitive subsets of a finite word cube

This file formalizes the elementary ``insensitive-set'' constructions used in
the density-increment proof of density Hales--Jewett.  The distinguished symbol
in `Fin (k + 1)` is `Fin.last k`.  Replacing every occurrence of that symbol by
`i.castSucc` gives a canonical representative for the equivalence relation
which permits independent changes between these two symbols.
-/



open Set

section Replacement

variable {k n : ℕ}

/-- Replace the distinguished last letter of `Fin (k + 1)` by `i`. -/
def replaceLastLetter (i : Fin k) (a : Fin (k + 1)) : Fin (k + 1) :=
  if a = Fin.last k then i.castSucc else a

@[simp] theorem replaceLastLetter_last (i : Fin k) :
    replaceLastLetter i (Fin.last k) = i.castSucc := by
  simp [replaceLastLetter]

@[simp] theorem replaceLastLetter_castSucc (i a : Fin k) :
    replaceLastLetter i a.castSucc = a.castSucc := by
  simp [replaceLastLetter, Fin.castSucc_ne_last]

theorem replaceLastLetter_ne_last (i : Fin k) (a : Fin (k + 1)) :
    replaceLastLetter i a ≠ Fin.last k := by
  by_cases h : a = Fin.last k
  · simp [h]
  · simpa [replaceLastLetter, h] using h

@[simp] theorem replaceLastLetter_idem (i : Fin k) (a : Fin (k + 1)) :
    replaceLastLetter i (replaceLastLetter i a) = replaceLastLetter i a := by
  change (if replaceLastLetter i a = Fin.last k then i.castSucc else replaceLastLetter i a) = _
  rw [if_neg (replaceLastLetter_ne_last i a)]

/-- Replace every occurrence of the distinguished last letter in a word by `i`. -/
def replaceLast (i : Fin k) (x : Word (k + 1) n) : Word (k + 1) n :=
  fun r ↦ replaceLastLetter i (x r)

@[simp] theorem replaceLast_apply (i : Fin k) (x : Word (k + 1) n) (r : Fin n) :
    replaceLast i x r = replaceLastLetter i (x r) := rfl

@[simp] theorem replaceLast_idem (i : Fin k) (x : Word (k + 1) n) :
    replaceLast i (replaceLast i x) = replaceLast i x := by
  funext r
  exact replaceLastLetter_idem i (x r)

theorem replaceLast_ne_last (i : Fin k) (x : Word (k + 1) n) (r : Fin n) :
    replaceLast i x r ≠ Fin.last k :=
  replaceLastLetter_ne_last i (x r)

/-- The word in the smaller alphabet obtained by treating every last letter as `i`. -/
def endpoint (i : Fin k) (x : Word (k + 1) n) : Word k n :=
  fun r ↦ (replaceLast i x r).castPred (replaceLast_ne_last i x r)

@[simp] theorem endpoint_last (i : Fin k) (r : Fin n) :
    endpoint i (fun _ : Fin n ↦ Fin.last k) r = i := by
  apply Fin.castSucc_injective
  simp [endpoint]

@[simp] theorem endpoint_castSucc (i : Fin k) (x : Word k n) :
    endpoint i (fun r ↦ (x r).castSucc) = x := by
  funext r
  apply Fin.castSucc_injective
  simp [endpoint]

@[simp] theorem castSucc_endpoint (i : Fin k) (x : Word (k + 1) n) (r : Fin n) :
    (endpoint i x r).castSucc = replaceLast i x r := by
  simp [endpoint]

theorem endpoint_eq_iff_replaceLast_eq (i : Fin k) (x y : Word (k + 1) n) :
    endpoint i x = endpoint i y ↔ replaceLast i x = replaceLast i y := by
  constructor
  · intro h
    funext r
    rw [← castSucc_endpoint i x r, ← castSucc_endpoint i y r, h]
  · intro h
    funext r
    apply Fin.castSucc_injective
    simpa only [castSucc_endpoint] using congrFun h r

/-- Two words are `(i,last)`-equivalent if changing `i` and the last letter independently
at any coordinates cannot distinguish them. -/
def LastEquivalent (i : Fin k) (x y : Word (k + 1) n) : Prop :=
  replaceLast i x = replaceLast i y

@[refl] theorem LastEquivalent.refl (i : Fin k) (x : Word (k + 1) n) :
    LastEquivalent i x x := rfl

@[symm] theorem LastEquivalent.symm (i : Fin k) {x y : Word (k + 1) n}
    (h : LastEquivalent i x y) : LastEquivalent i y x := Eq.symm h

@[trans] theorem LastEquivalent.trans (i : Fin k) {x y z : Word (k + 1) n}
    (hxy : LastEquivalent i x y) (hyz : LastEquivalent i y z) :
    LastEquivalent i x z := Eq.trans hxy hyz

theorem lastEquivalent_equivalence (i : Fin k) :
    Equivalence (LastEquivalent (n := n) i) :=
  ⟨LastEquivalent.refl i, LastEquivalent.symm i, LastEquivalent.trans i⟩

theorem lastEquivalent_iff_endpoint_eq (i : Fin k) (x y : Word (k + 1) n) :
    LastEquivalent i x y ↔ endpoint i x = endpoint i y := by
  rw [endpoint_eq_iff_replaceLast_eq]
  rfl

theorem lastEquivalent_replaceLast_left (i : Fin k) (x : Word (k + 1) n) :
    LastEquivalent i (replaceLast i x) x := by
  exact replaceLast_idem i x

theorem lastEquivalent_iff_coordinatewise (i : Fin k) (x y : Word (k + 1) n) :
    LastEquivalent i x y ↔
      ∀ r, x r = y r ∨
        ((x r = i.castSucc ∨ x r = Fin.last k) ∧
          (y r = i.castSucc ∨ y r = Fin.last k)) := by
  simp only [LastEquivalent, funext_iff, replaceLast_apply]
  apply forall_congr'
  intro r
  grind [replaceLastLetter]

end Replacement

section Insensitive

variable {k n : ℕ}

/-- A set is `(i,last)`-insensitive when it is constant on `LastEquivalent` classes. -/
def IsLastInsensitive (i : Fin k) (C : Set (Word (k + 1) n)) : Prop :=
  ∀ x y, LastEquivalent i x y → (x ∈ C ↔ y ∈ C)

theorem isLastInsensitive_iff_mem_replaceLast (i : Fin k)
    (C : Set (Word (k + 1) n)) :
    IsLastInsensitive i C ↔ ∀ x, x ∈ C ↔ replaceLast i x ∈ C := by
  constructor
  · intro h x
    exact (h (replaceLast i x) x (lastEquivalent_replaceLast_left i x)).symm
  · intro h x y hxy
    rw [h x, h y, hxy]

theorem isLastInsensitive_iff_saturated (i : Fin k)
    (C : Set (Word (k + 1) n)) :
    IsLastInsensitive i C ↔ replaceLast i ⁻¹' (replaceLast i '' C) = C := by
  rw [isLastInsensitive_iff_mem_replaceLast]
  constructor
  · intro h
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [h x]
      rw [← hyx]
      simpa only [replaceLast_idem] using (h y).mp hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  · intro h x
    constructor
    · intro hx
      have hx' : replaceLast i x ∈ replaceLast i ⁻¹' (replaceLast i '' C) :=
        ⟨x, hx, (replaceLast_idem i x).symm⟩
      simpa only [h] using hx'
    · intro hx
      rw [← h]
      exact ⟨replaceLast i x, hx, replaceLast_idem i x⟩

theorem isLastInsensitive_iff_preimage (i : Fin k)
    (C : Set (Word (k + 1) n)) :
    IsLastInsensitive i C ↔ ∃ B : Set (Word k n), C = endpoint i ⁻¹' B := by
  constructor
  · intro h
    refine ⟨endpoint i '' C, ?_⟩
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact (h x y ((lastEquivalent_iff_endpoint_eq i x y).2 hyx.symm)).mpr hy
  · rintro ⟨B, rfl⟩ x y hxy
    simpa only [Set.mem_preimage, (lastEquivalent_iff_endpoint_eq i x y).mp hxy]

theorem IsLastInsensitive.compl {i : Fin k} {C : Set (Word (k + 1) n)}
    (hC : IsLastInsensitive i C) : IsLastInsensitive i Cᶜ := by
  intro x y hxy
  simpa only [Set.mem_compl_iff] using not_congr (hC x y hxy)

theorem IsLastInsensitive.inter {i : Fin k} {C D : Set (Word (k + 1) n)}
    (hC : IsLastInsensitive i C) (hD : IsLastInsensitive i D) :
    IsLastInsensitive i (C ∩ D) := by
  intro x y hxy
  simpa only [Set.mem_inter_iff] using and_congr (hC x y hxy) (hD x y hxy)

theorem IsLastInsensitive.union {i : Fin k} {C D : Set (Word (k + 1) n)}
    (hC : IsLastInsensitive i C) (hD : IsLastInsensitive i D) :
    IsLastInsensitive i (C ∪ D) := by
  intro x y hxy
  simpa only [Set.mem_union] using or_congr (hC x y hxy) (hD x y hxy)

theorem IsLastInsensitive.diff {i : Fin k} {C D : Set (Word (k + 1) n)}
    (hC : IsLastInsensitive i C) (hD : IsLastInsensitive i D) :
    IsLastInsensitive i (C \ D) := by
  intro x y hxy
  simpa only [Set.mem_sdiff] using and_congr (hC x y hxy) (not_congr (hD x y hxy))

theorem IsLastInsensitive.iInter {i : Fin k} {J : Type*}
    {C : J → Set (Word (k + 1) n)} (hC : ∀ j, IsLastInsensitive i (C j)) :
    IsLastInsensitive i (⋂ j, C j) := by
  intro x y hxy
  simp only [Set.mem_iInter]
  exact forall_congr' fun j ↦ hC j x y hxy

end Insensitive

section EndpointConstruction

variable {k n : ℕ}

/-- The `(i,last)`-insensitive cylinder generated by a set in the restricted cube `[k]^n`. -/
def endpointCylinder (i : Fin k) (A : Set (Word k n)) : Set (Word (k + 1) n) :=
  endpoint i ⁻¹' A

@[simp] theorem mem_endpointCylinder (i : Fin k) (A : Set (Word k n))
    (x : Word (k + 1) n) : x ∈ endpointCylinder i A ↔ endpoint i x ∈ A :=
  Iff.rfl

theorem endpointCylinder_isLastInsensitive (i : Fin k) (A : Set (Word k n)) :
    IsLastInsensitive i (endpointCylinder i A) := by
  intro x y hxy
  simpa only [mem_endpointCylinder, (lastEquivalent_iff_endpoint_eq i x y).mp hxy]

@[simp] theorem mem_iInter_endpointCylinder (A : Set (Word k n))
    (x : Word (k + 1) n) :
    x ∈ ⋂ i : Fin k, endpointCylinder i A ↔ ∀ i : Fin k, endpoint i x ∈ A := by
  simp

/-- Taking the `i`-endpoint of the wildcard word attached to a line recovers
the `i`-point of that line. -/
@[simp] theorem endpoint_templateEndpoint (i : Fin k)
    (l : Combinatorics.Line (Fin k) (Fin n)) :
    endpoint i (templateEndpoint l) = l i := by
  funext r
  cases hr : l.idxFun r with
  | none =>
      simp [endpoint, replaceLast, replaceLastLetter, Combinatorics.Line.coe_apply, hr]
  | some a =>
      simp [endpoint, replaceLast, replaceLastLetter, Combinatorics.Line.coe_apply, hr]

@[simp] theorem endpoint_templateExtension_last (i : Fin k)
    (l : Combinatorics.Line (Fin k) (Fin n)) :
    endpoint i (templateExtension l (Fin.last k)) = l i := by
  simp

@[simp] theorem endpoint_templateExtension_castSucc (i a : Fin k)
    (l : Combinatorics.Line (Fin k) (Fin n)) :
    endpoint i (templateExtension l a.castSucc) = l a := by
  rw [templateExtension_castSucc]
  change endpoint i (fun r ↦ (l a r).castSucc) = l a
  exact endpoint_castSucc i (l a)

/-- The wildcard endpoint of a line belongs to all of the insensitive cylinders
generated by `A` exactly when every point of the original line belongs to `A`. -/
@[simp] theorem templateEndpoint_mem_iInter_endpointCylinder_iff
    (A : Set (Word k n)) (l : Combinatorics.Line (Fin k) (Fin n)) :
    templateEndpoint l ∈ ⋂ i : Fin k, endpointCylinder i A ↔
      Set.range l ⊆ A := by
  rw [mem_iInter_endpointCylinder]
  simp only [endpoint_templateEndpoint]
  constructor
  · intro h _ hx
    obtain ⟨i, rfl⟩ := hx
    exact h i
  · intro h i
    exact h ⟨i, rfl⟩

/-- A word containing the last letter encodes a proper line in the restricted cube: last-letter
coordinates are wildcard coordinates, and every other coordinate is held constant. -/
def endpointLine (x : Word (k + 1) n)
    (hx : ∃ r, x r = Fin.last k) : Combinatorics.Line (Fin k) (Fin n) where
  idxFun r := if h : x r = Fin.last k then none else some ((x r).castPred h)
  proper := by
    obtain ⟨r, hr⟩ := hx
    exact ⟨r, by simp [hr]⟩

@[simp] theorem endpointLine_apply (x : Word (k + 1) n)
    (hx : ∃ r, x r = Fin.last k) (i : Fin k) :
    endpointLine x hx i = endpoint i x := by
  funext r
  by_cases h : x r = Fin.last k
  · simp [endpointLine, Combinatorics.Line.coe_apply, endpoint, replaceLast,
      replaceLastLetter, h]
  · simp [endpointLine, Combinatorics.Line.coe_apply, endpoint, replaceLast,
      replaceLastLetter, h]

theorem iInter_endpointCylinder_iff_line (A : Set (Word k n))
    (x : Word (k + 1) n) (hx : ∃ r, x r = Fin.last k) :
    x ∈ ⋂ i : Fin k, endpointCylinder i A ↔
      Set.range (endpointLine x hx) ⊆ A := by
  rw [mem_iInter_endpointCylinder]
  constructor
  · intro h _ hy
    obtain ⟨i, rfl⟩ := hy
    simpa only [endpointLine_apply] using h i
  · intro h i
    exact h ⟨i, by simp⟩

theorem iInter_endpointCylinder_subset_lineEndpoints (A : Set (Word k n)) :
    (⋂ i : Fin k, endpointCylinder i A) ∩
        {x : Word (k + 1) n | ∃ r, x r = Fin.last k} =
      {x | ∃ hx : ∃ r, x r = Fin.last k, Set.range (endpointLine x hx) ⊆ A} := by
  ext x
  constructor
  · rintro ⟨hxC, hxlast⟩
    exact ⟨hxlast, (iInter_endpointCylinder_iff_line A x hxlast).mp hxC⟩
  · rintro ⟨hxlast, hxline⟩
    exact ⟨(iInter_endpointCylinder_iff_line A x hxlast).mpr hxline, hxlast⟩

end EndpointConstruction

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/Tiling.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Finite tilings by combinatorial subspaces

This file contains the bookkeeping common to the insensitive-set tiling
argument.  A tile is represented by the finite range of a proper Mathlib
`Combinatorics.Subspace`; a tiling is a finite, pairwise-disjoint family of
such ranges.  The density lemmas below are deliberately stated for arbitrary
finite families, so that the final intersection argument can sum a relative
error estimate over all of its large tiles.
-/

open scoped BigOperators



open Combinatorics

@[simp] theorem mem_finsetMap_equiv {A B : Type*} [DecidableEq A]
    [DecidableEq B] (e : A ≃ B) (D : Finset A) (x : B) :
    x ∈ D.map e.toEmbedding ↔ e.symm x ∈ D := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    simpa using hy
  · intro hx
    exact Finset.mem_map.mpr ⟨e.symm x, hx, by simp⟩

section SubspacePoints

variable {eta alpha iota : Type*}

/-- The finite set of points parametrized by a combinatorial subspace. -/
noncomputable def subspacePoints [Fintype (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota) :
    Finset (iota → alpha) :=
  Finset.univ.image U

@[simp] theorem mem_subspacePoints [Fintype (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (x : iota → alpha) :
    x ∈ subspacePoints U ↔ x ∈ Set.range U := by
  simp [subspacePoints]

@[simp] theorem card_subspacePoints [Fintype (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota) :
    (subspacePoints U).card = Fintype.card (eta → alpha) := by
  rw [subspacePoints, Finset.card_image_of_injective _ U.parameter_injective,
    Finset.card_univ]

@[simp] theorem card_subspacePoints_fin {m q : ℕ}
    [DecidableEq (iota → Fin q)] (U : Subspace (Fin m) (Fin q) iota) :
    (subspacePoints U).card = q ^ m := by
  rw [card_subspacePoints, Fintype.card_fun]
  simp

theorem subspacePoints_nonempty [Fintype (eta → alpha)]
    [Nonempty (eta → alpha)] [DecidableEq (iota → alpha)]
    (U : Subspace eta alpha iota) : (subspacePoints U).Nonempty := by
  inhabit eta → alpha
  exact ⟨U default, by simp⟩

end SubspacePoints

section Pullback

variable {eta zeta alpha iota : Type*}

/-- Pull a finite set in the ambient cube back to the parameter cube of a
subspace.  Its density is the usual relative density inside that subspace. -/
noncomputable def subspacePullback [Fintype (eta → alpha)]
    (U : Subspace eta alpha iota) (D : Finset (iota → alpha)) :
    Finset (eta → alpha) := by
  classical
  exact Finset.univ.filter fun x ↦ U x ∈ D

@[simp] theorem mem_subspacePullback [Fintype (eta → alpha)]
    (U : Subspace eta alpha iota) (D : Finset (iota → alpha))
    (x : eta → alpha) :
    x ∈ subspacePullback U D ↔ U x ∈ D := by
  classical
  simp [subspacePullback]

theorem image_subspacePullback [Fintype (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (D : Finset (iota → alpha)) :
    (subspacePullback U D).image U = subspacePoints U ∩ D := by
  classical
  ext x
  constructor
  · simp only [Finset.mem_image, mem_subspacePullback, Finset.mem_inter,
      mem_subspacePoints]
    rintro ⟨y, hyD, rfl⟩
    exact ⟨⟨y, rfl⟩, hyD⟩
  · simp only [Finset.mem_inter, mem_subspacePoints, Finset.mem_image,
      mem_subspacePullback]
    rintro ⟨⟨y, rfl⟩, hyD⟩
    exact ⟨y, hyD, rfl⟩

theorem card_inter_subspacePoints [Fintype (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (D : Finset (iota → alpha)) :
    (subspacePoints U ∩ D).card = (subspacePullback U D).card := by
  rw [← image_subspacePullback U D,
    Finset.card_image_of_injective _ U.parameter_injective]

/-- Ambient density factors as the density of the large tile times relative
density in its parameter cube. -/
theorem density_inter_subspacePoints [Fintype (eta → alpha)]
    [Nonempty (eta → alpha)] [Fintype (iota → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (D : Finset (iota → alpha)) :
    density (subspacePoints U ∩ D) =
      density (subspacePoints U) * density (subspacePullback U D) := by
  simp only [density_eq_card_div_card, card_inter_subspacePoints]
  rw [card_subspacePoints]
  have heta : (Fintype.card (eta → alpha) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Density scaling for an arbitrary finite subset of a subspace's parameter
cube. -/
theorem density_image_subspace [Fintype (eta → alpha)]
    [Nonempty (eta → alpha)] [Fintype (iota → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (B : Finset (eta → alpha)) :
    density (B.image U) = density (subspacePoints U) * density B := by
  simp only [density_eq_card_div_card,
    Finset.card_image_of_injective _ U.parameter_injective, card_subspacePoints]
  have heta : (Fintype.card (eta → alpha) : ℝ) ≠ 0 := by positivity
  field_simp

theorem subspacePoints_comp [Fintype (zeta → alpha)]
    [Fintype (eta → alpha)] [DecidableEq (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (V : Subspace zeta alpha eta) :
    subspacePoints (U.comp V) = (subspacePoints V).image U := by
  classical
  ext x
  simp only [mem_subspacePoints, Finset.mem_image, Set.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨V z, ⟨z, rfl⟩, (Subspace.comp_apply U V z).symm⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, Subspace.comp_apply U V z⟩

theorem subspacePoints_comp_subset_iff [Fintype (zeta → alpha)]
    [Fintype (eta → alpha)] [DecidableEq (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (V : Subspace zeta alpha eta) (D : Finset (iota → alpha)) :
    subspacePoints (U.comp V) ⊆ D ↔
      subspacePoints V ⊆ subspacePullback U D := by
  constructor
  · intro h x hx
    rw [mem_subspacePullback]
    rw [mem_subspacePoints] at hx
    obtain ⟨z, rfl⟩ := hx
    apply h
    rw [mem_subspacePoints]
    exact ⟨z, Subspace.comp_apply U V z⟩
  · intro h x hx
    rw [mem_subspacePoints] at hx
    obtain ⟨z, rfl⟩ := hx
    have hz : U (V z) ∈ D := by
      rw [← mem_subspacePullback]
      apply h
      rw [mem_subspacePoints]
      exact ⟨z, rfl⟩
    simpa only [Subspace.comp_apply] using hz

theorem subspacePoints_comp_subset [Fintype (zeta → alpha)]
    [Fintype (eta → alpha)] [DecidableEq (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (V : Subspace zeta alpha eta) :
    subspacePoints (U.comp V) ⊆ subspacePoints U := by
  rw [subspacePoints_comp]
  intro x hx
  simp only [Finset.mem_image] at hx
  obtain ⟨y, _hy, rfl⟩ := hx
  simp

end Pullback

section InsensitivePullback

variable {k m n : ℕ}

/-- Subspaces preserve `(i,last)`-equivalence of parameter words. -/
theorem lastEquivalent_subspace (i : Fin k)
    (U : Subspace (Fin m) (Fin (k + 1)) (Fin n))
    {x y : Word (k + 1) m} (hxy : LastEquivalent i x y) :
    LastEquivalent i (U x) (U y) := by
  rw [LastEquivalent] at hxy ⊢
  funext r
  cases hr : U.idxFun r with
  | inl a => simp [replaceLast, Subspace.coe_apply, hr]
  | inr e =>
      simpa [replaceLast, Subspace.coe_apply, hr] using congrFun hxy e

/-- Pulling an insensitive set back through a combinatorial subspace again
gives an insensitive set in the parameter cube. -/
theorem IsLastInsensitive.subspacePullback (i : Fin k)
    (U : Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (D : Finset (Word (k + 1) n))
    (hD : IsLastInsensitive i (D : Set (Word (k + 1) n))) :
    IsLastInsensitive i (subspacePullback U D : Set (Word (k + 1) m)) := by
  intro x y hxy
  simp only [Finset.mem_coe, mem_subspacePullback]
  exact hD (U x) (U y) (lastEquivalent_subspace i U hxy)

end InsensitivePullback

section Families

variable {eta alpha iota : Type*} [Fintype (eta → alpha)]
  [DecidableEq (iota → alpha)]

/-- A finite pairwise-disjoint family of equal-dimensional combinatorial
subspaces.  Containment in a target set is kept separate, since the same
family is used with several successive remainders in the greedy argument. -/
structure SubspaceTiling (eta alpha iota : Type*)
    [Fintype (eta → alpha)] [DecidableEq (iota → alpha)] where
  tiles : Finset (Subspace eta alpha iota)
  pairwiseDisjoint : (tiles : Set (Subspace eta alpha iota)).PairwiseDisjoint
    subspacePoints

namespace SubspaceTiling

variable {zeta : Type*} [Fintype (zeta → alpha)]
  [DecidableEq (eta → alpha)]

/-- The empty tiling. -/
noncomputable def empty : SubspaceTiling eta alpha iota := by
  classical
  exact ⟨∅, by simp⟩

@[simp] theorem tiles_empty : (empty : SubspaceTiling eta alpha iota).tiles = ∅ := rfl

/-- The union of all points in all tiles. -/
noncomputable def covered (T : SubspaceTiling eta alpha iota) :
    Finset (iota → alpha) :=
  T.tiles.biUnion subspacePoints

@[simp] theorem covered_empty : (empty : SubspaceTiling eta alpha iota).covered = ∅ := by
  classical
  simp [covered, empty]

/-- Join two tilings whose covered point sets are disjoint. -/
noncomputable def disjointUnion (T S : SubspaceTiling eta alpha iota)
    (h : Disjoint T.covered S.covered) :
    SubspaceTiling eta alpha iota := by
  classical
  exact
    { tiles := T.tiles ∪ S.tiles
      pairwiseDisjoint := by
        intro U hU V hV hUV
        change U ∈ T.tiles ∪ S.tiles at hU
        change V ∈ T.tiles ∪ S.tiles at hV
        rw [Finset.mem_union] at hU hV
        rcases hU with hUT | hUS <;> rcases hV with hVT | hVS
        · exact T.pairwiseDisjoint hUT hVT hUV
        · exact h.mono
            (fun x hx ↦ Finset.mem_biUnion.mpr ⟨U, hUT, hx⟩)
            (fun x hx ↦ Finset.mem_biUnion.mpr ⟨V, hVS, hx⟩)
        · exact h.symm.mono
            (fun x hx ↦ Finset.mem_biUnion.mpr ⟨U, hUS, hx⟩)
            (fun x hx ↦ Finset.mem_biUnion.mpr ⟨V, hVT, hx⟩)
        · exact S.pairwiseDisjoint hUS hVS hUV }

theorem covered_disjointUnion (T S : SubspaceTiling eta alpha iota)
    (h : Disjoint T.covered S.covered) :
    (T.disjointUnion S h).covered = T.covered ∪ S.covered := by
  classical
  exact Finset.union_biUnion

@[simp] theorem mem_covered (T : SubspaceTiling eta alpha iota)
    (x : iota → alpha) :
    x ∈ T.covered ↔ ∃ U ∈ T.tiles, x ∈ subspacePoints U := by
  classical
  simp [covered]

theorem tile_subset_covered (T : SubspaceTiling eta alpha iota)
    {U : Subspace eta alpha iota} (hU : U ∈ T.tiles) :
    subspacePoints U ⊆ T.covered := by
  classical
  intro x hx
  exact (T.mem_covered x).2 ⟨U, hU, hx⟩

section AmbientReindex

variable {kappa : Type*} [DecidableEq (kappa → alpha)]

/-- The word equivalence induced by reindexing ambient coordinates. -/
def ambientWordEquiv (e : iota ≃ kappa) :
    (iota → alpha) ≃ (kappa → alpha) :=
  e.arrowCongr (Equiv.refl alpha)

theorem ambientWordEquiv_symm (e : iota ≃ kappa) :
    (ambientWordEquiv (alpha := alpha) e).symm = ambientWordEquiv e.symm := by
  ext x j
  rfl

@[simp] theorem mem_map_ambientWordEquiv (e : iota ≃ kappa)
    (D : Finset (iota → alpha)) (x : kappa → alpha) :
    x ∈ D.map (ambientWordEquiv e).toEmbedding ↔
      (ambientWordEquiv e).symm x ∈ D := by
  exact mem_finsetMap_equiv (ambientWordEquiv e) D x

theorem ambientReindex_injective (e : iota ≃ kappa) :
    Function.Injective (fun U : Subspace eta alpha iota ↦
      U.reindex (Equiv.refl eta) (Equiv.refl alpha) e) := by
  intro U V hUV
  apply Subspace.ext
  funext i
  have hi := congrArg
    (fun W : Subspace eta alpha kappa ↦ W.idxFun (e i)) hUV
  simpa [Subspace.reindex] using hi

noncomputable def ambientReindexEmbedding (e : iota ≃ kappa) :
    Subspace eta alpha iota ↪ Subspace eta alpha kappa :=
  ⟨fun U ↦ U.reindex (Equiv.refl eta) (Equiv.refl alpha) e,
    ambientReindex_injective e⟩

theorem subspacePoints_ambientReindex (e : iota ≃ kappa)
    (U : Subspace eta alpha iota) :
    subspacePoints (U.reindex (Equiv.refl eta) (Equiv.refl alpha) e) =
      (subspacePoints U).map (ambientWordEquiv e).toEmbedding := by
  classical
  ext x
  constructor
  · intro hx
    rw [mem_subspacePoints] at hx
    obtain ⟨a, rfl⟩ := hx
    apply Finset.mem_map.mpr
    refine ⟨U a, by simp, ?_⟩
    funext j
    simp [ambientWordEquiv, Function.comp_def]
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    rw [mem_subspacePoints] at hy ⊢
    obtain ⟨a, rfl⟩ := hy
    refine ⟨a, ?_⟩
    funext j
    simp [ambientWordEquiv, Function.comp_def]

/-- Transport every tile through an equivalence of ambient coordinate types. -/
noncomputable def ambientReindex (T : SubspaceTiling eta alpha iota)
    (e : iota ≃ kappa) : SubspaceTiling eta alpha kappa := by
  classical
  exact
    { tiles := T.tiles.map (ambientReindexEmbedding e)
      pairwiseDisjoint := by
        intro U hU V hV hUV
        obtain ⟨U₀, hU₀, rfl⟩ := Finset.mem_map.mp hU
        obtain ⟨V₀, hV₀, rfl⟩ := Finset.mem_map.mp hV
        have hUV₀ : U₀ ≠ V₀ := fun h ↦
          hUV (congrArg (fun W ↦
            W.reindex (Equiv.refl eta) (Equiv.refl alpha) e) h)
        change Disjoint
          (subspacePoints
            (U₀.reindex (Equiv.refl eta) (Equiv.refl alpha) e))
          (subspacePoints
            (V₀.reindex (Equiv.refl eta) (Equiv.refl alpha) e))
        rw [subspacePoints_ambientReindex, subspacePoints_ambientReindex,
          Finset.disjoint_map]
        exact T.pairwiseDisjoint hU₀ hV₀ hUV₀ }

theorem covered_ambientReindex (T : SubspaceTiling eta alpha iota)
    (e : iota ≃ kappa) :
    (T.ambientReindex e).covered =
      T.covered.map (ambientWordEquiv e).toEmbedding := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨U, hU, hxU⟩ := ((T.ambientReindex e).mem_covered x).mp hx
    change U ∈ T.tiles.map (ambientReindexEmbedding e) at hU
    obtain ⟨U₀, hU₀, rfl⟩ := Finset.mem_map.mp hU
    change x ∈ subspacePoints
      (U₀.reindex (Equiv.refl eta) (Equiv.refl alpha) e) at hxU
    rw [subspacePoints_ambientReindex] at hxU
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hxU
    exact Finset.mem_map.mpr ⟨y, T.tile_subset_covered hU₀ hy, rfl⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨U, hU, hyU⟩ := (T.mem_covered y).mp hy
    apply ((T.ambientReindex e).mem_covered _).mpr
    refine ⟨U.reindex (Equiv.refl eta) (Equiv.refl alpha) e, ?_, ?_⟩
    · change U.reindex (Equiv.refl eta) (Equiv.refl alpha) e ∈
        T.tiles.map (ambientReindexEmbedding e)
      exact Finset.mem_map.mpr ⟨U, hU, rfl⟩
    · rw [subspacePoints_ambientReindex]
      exact Finset.mem_map.mpr ⟨y, hyU, rfl⟩

end AmbientReindex

/-- Every tile in `T` is contained in `D`. -/
def IsContainedIn (T : SubspaceTiling eta alpha iota)
    (D : Finset (iota → alpha)) : Prop :=
  ∀ U ∈ T.tiles, subspacePoints U ⊆ D

theorem covered_subset_iff (T : SubspaceTiling eta alpha iota)
    (D : Finset (iota → alpha)) :
    T.covered ⊆ D ↔ T.IsContainedIn D := by
  classical
  constructor
  · intro h U hU
    exact (T.tile_subset_covered hU).trans h
  · intro h x hx
    obtain ⟨U, hU, hxU⟩ := (T.mem_covered x).1 hx
    exact h U hU hxU

section AmbientReindexContainment

variable {kappa : Type*} [DecidableEq (kappa → alpha)]

/-- Containment after an ambient reindex is equivalent to containment in the
pullback of the target finset. -/
theorem ambientReindex_isContainedIn_iff
    (T : SubspaceTiling eta alpha iota) (e : iota ≃ kappa)
    (D : Finset (kappa → alpha)) :
    (T.ambientReindex e).IsContainedIn D ↔
      T.IsContainedIn
        (D.map (ambientWordEquiv e).symm.toEmbedding) := by
  rw [← (T.ambientReindex e).covered_subset_iff D,
    ← T.covered_subset_iff, covered_ambientReindex]
  constructor
  · intro h x hx
    apply Finset.mem_map.mpr
    refine ⟨ambientWordEquiv e x, h ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    · simp
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    have hy' := h hy
    obtain ⟨z, hz, hzy⟩ := Finset.mem_map.mp hy'
    simpa [← hzy] using hz

/-- Exact residual-set transport under an ambient coordinate equivalence. -/
theorem sdiff_covered_ambientReindex
    (T : SubspaceTiling eta alpha iota) (e : iota ≃ kappa)
    (D : Finset (kappa → alpha)) :
    D \ (T.ambientReindex e).covered =
      ((D.map (ambientWordEquiv e).symm.toEmbedding) \ T.covered).map
        (ambientWordEquiv e).toEmbedding := by
  classical
  rw [covered_ambientReindex]
  ext x
  constructor
  · intro hx
    have hx' := Finset.mem_sdiff.mp hx
    apply Finset.mem_map.mpr
    refine ⟨(ambientWordEquiv e).symm x, Finset.mem_sdiff.mpr ⟨?_, ?_⟩, by simp⟩
    · exact Finset.mem_map.mpr ⟨x, hx'.1, by simp⟩
    · intro hcover
      apply hx'.2
      exact Finset.mem_map.mpr
        ⟨(ambientWordEquiv e).symm x, hcover, by simp⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
    have hy' := Finset.mem_sdiff.mp hy
    obtain ⟨z, hzD, hzy⟩ := Finset.mem_map.mp hy'.1
    apply Finset.mem_sdiff.mpr
    constructor
    · have hzx : z = x := by
        rw [← hyx, ← hzy]
        simp
      simpa [hzx] using hzD
    · intro hxcover
      obtain ⟨w, hwcover, hwx⟩ := Finset.mem_map.mp hxcover
      apply hy'.2
      have hwy : w = y := by
        apply (ambientWordEquiv e).injective
        exact hwx.trans hyx.symm
      simpa [hwy] using hwcover

theorem density_sdiff_covered_ambientReindex
    [Fintype (iota → alpha)] [Fintype (kappa → alpha)]
    (T : SubspaceTiling eta alpha iota) (e : iota ≃ kappa)
    (D : Finset (kappa → alpha)) :
    density (D \ (T.ambientReindex e).covered) =
      density (D.map (ambientWordEquiv e).symm.toEmbedding \ T.covered) := by
  rw [sdiff_covered_ambientReindex,
    density_map_equiv (ambientWordEquiv e)]

end AmbientReindexContainment

theorem card_covered (T : SubspaceTiling eta alpha iota) :
    T.covered.card = ∑ U ∈ T.tiles, (subspacePoints U).card := by
  classical
  exact Finset.card_biUnion T.pairwiseDisjoint

theorem comp_left_injective (U : Subspace eta alpha iota) :
    Function.Injective (U.comp : Subspace zeta alpha eta → Subspace zeta alpha iota) := by
  intro V W hVW
  apply Subspace.ext
  funext e
  obtain ⟨i, hi⟩ := U.proper e
  have hcoord := congrArg (fun X : Subspace zeta alpha iota ↦ X.idxFun i) hVW
  simpa [Subspace.comp, hi] using hcoord

noncomputable def compEmbedding (U : Subspace eta alpha iota) :
    Subspace zeta alpha eta ↪ Subspace zeta alpha iota :=
  ⟨U.comp, comp_left_injective U⟩

/-- Map every tile in a parameter cube into an outer combinatorial subspace. -/
noncomputable def comp (T : SubspaceTiling zeta alpha eta)
    (U : Subspace eta alpha iota) : SubspaceTiling zeta alpha iota := by
  classical
  exact
    { tiles := T.tiles.map (compEmbedding U)
      pairwiseDisjoint := by
        intro V hV W hW hne
        obtain ⟨V₀, hV₀, hVeq⟩ := Finset.mem_map.1 hV
        obtain ⟨W₀, hW₀, hWeq⟩ := Finset.mem_map.1 hW
        subst V
        subst W
        have hne₀ : V₀ ≠ W₀ := fun h ↦ hne (congrArg U.comp h)
        change Disjoint (subspacePoints (U.comp V₀)) (subspacePoints (U.comp W₀))
        rw [subspacePoints_comp, subspacePoints_comp,
          Finset.disjoint_image U.parameter_injective]
        exact T.pairwiseDisjoint hV₀ hW₀ hne₀ }

theorem covered_comp (T : SubspaceTiling zeta alpha eta)
    (U : Subspace eta alpha iota) :
    (T.comp U).covered = T.covered.image U := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨V, hV, hxV⟩ := ((T.comp U).mem_covered x).1 hx
    change V ∈ T.tiles.map (compEmbedding U) at hV
    obtain ⟨V₀, hV₀, hVeq⟩ := Finset.mem_map.1 hV
    subst V
    change x ∈ subspacePoints (U.comp V₀) at hxV
    rw [subspacePoints_comp] at hxV
    simp only [Finset.mem_image] at hxV ⊢
    obtain ⟨y, hy, rfl⟩ := hxV
    exact ⟨y, T.tile_subset_covered hV₀ hy, rfl⟩
  · intro hx
    simp only [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨V, hV, hyV⟩ := (T.mem_covered y).1 hy
    apply ((T.comp U).mem_covered (U y)).2
    refine ⟨U.comp V, ?_, ?_⟩
    · change U.comp V ∈ T.tiles.map (compEmbedding U)
      exact Finset.mem_map.2 ⟨V, hV, rfl⟩
    · rw [subspacePoints_comp]
      exact Finset.mem_image_of_mem U hyV

theorem covered_comp_subset_subspacePoints
    (T : SubspaceTiling zeta alpha eta) (U : Subspace eta alpha iota) :
    (T.comp U).covered ⊆ subspacePoints U := by
  rw [covered_comp]
  intro x hx
  simp only [Finset.mem_image] at hx
  obtain ⟨y, _hy, rfl⟩ := hx
  simp

theorem comp_isContainedIn_iff (T : SubspaceTiling zeta alpha eta)
    (U : Subspace eta alpha iota) (D : Finset (iota → alpha)) :
    (T.comp U).IsContainedIn D ↔ T.IsContainedIn (subspacePullback U D) := by
  classical
  constructor
  · intro h V hV
    rw [← subspacePoints_comp_subset_iff U V D]
    apply h (U.comp V)
    change U.comp V ∈ T.tiles.map (compEmbedding U)
    exact Finset.mem_map.2 ⟨V, hV, rfl⟩
  · intro h V hV
    change V ∈ T.tiles.map (compEmbedding U) at hV
    obtain ⟨V₀, hV₀, hVeq⟩ := Finset.mem_map.1 hV
    subst V
    change subspacePoints (U.comp V₀) ⊆ D
    rw [subspacePoints_comp_subset_iff]
    exact h V₀ hV₀

/-- Refine every tile of `T` by an inner tiling in its parameter cube and
flatten all the resulting composed subspaces into one tiling. -/
noncomputable def bind (T : SubspaceTiling eta alpha iota)
    (R : Subspace eta alpha iota → SubspaceTiling zeta alpha eta) :
    SubspaceTiling zeta alpha iota := by
  classical
  exact
    { tiles := T.tiles.biUnion fun U ↦ (R U).comp U |>.tiles
      pairwiseDisjoint := by
        intro A hA B hB hAB
        change A ∈ T.tiles.biUnion (fun U ↦ ((R U).comp U).tiles) at hA
        change B ∈ T.tiles.biUnion (fun U ↦ ((R U).comp U).tiles) at hB
        obtain ⟨U, hU, hAU⟩ := Finset.mem_biUnion.mp hA
        obtain ⟨V, hV, hBV⟩ := Finset.mem_biUnion.mp hB
        by_cases hUV : U = V
        · subst V
          exact ((R U).comp U).pairwiseDisjoint hAU hBV hAB
        · exact (T.pairwiseDisjoint hU hV hUV).mono
            (((R U).comp U).tile_subset_covered hAU |>.trans
              ((R U).covered_comp_subset_subspacePoints U))
            (((R V).comp V).tile_subset_covered hBV |>.trans
              ((R V).covered_comp_subset_subspacePoints V)) }

theorem covered_bind (T : SubspaceTiling eta alpha iota)
    (R : Subspace eta alpha iota → SubspaceTiling zeta alpha eta) :
    (T.bind R).covered =
      T.tiles.biUnion fun U ↦ ((R U).comp U).covered := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨A, hA, hxA⟩ := ((T.bind R).mem_covered x).1 hx
    change A ∈ T.tiles.biUnion (fun U ↦ ((R U).comp U).tiles) at hA
    obtain ⟨U, hU, hAU⟩ := Finset.mem_biUnion.mp hA
    apply Finset.mem_biUnion.mpr
    exact ⟨U, hU, (((R U).comp U).mem_covered x).2 ⟨A, hAU, hxA⟩⟩
  · intro hx
    obtain ⟨U, hU, hxU⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨A, hAU, hxA⟩ := (((R U).comp U).mem_covered x).1 hxU
    apply ((T.bind R).mem_covered x).2
    refine ⟨A, ?_, hxA⟩
    change A ∈ T.tiles.biUnion (fun V ↦ ((R V).comp V).tiles)
    exact Finset.mem_biUnion.mpr ⟨U, hU, hAU⟩

theorem density_covered [Fintype (iota → alpha)]
    (T : SubspaceTiling eta alpha iota) :
    density T.covered = ∑ U ∈ T.tiles, density (subspacePoints U) := by
  classical
  simp only [density]
  rw [T.card_covered]
  push_cast
  rw [Finset.sum_div]

end SubspaceTiling

/-- A set is tiled by `eta`-dimensional combinatorial subspaces if it is the
covered set of a pairwise-disjoint finite subspace family. -/
def IsSubspaceTiled (E : Finset (iota → alpha)) : Prop :=
  ∃ T : SubspaceTiling eta alpha iota, T.covered = E

end Families

section DensityOfDisjointUnions

variable {A I : Type*} [Fintype A] [DecidableEq A]

/-- Density is additive on a finite pairwise-disjoint union. -/
theorem density_biUnion {s : Finset I} {f : I → Finset A}
    (h : (s : Set I).PairwiseDisjoint f) :
    density (s.biUnion f) = ∑ i ∈ s, density (f i) := by
  classical
  simp only [density]
  rw [Finset.card_biUnion h]
  push_cast
  rw [Finset.sum_div]

/-- Sum a uniform relative-density bound over pairwise-disjoint ambient
pieces.  This is the quantitative bookkeeping used in the induction from one
insensitive factor to an intersection of insensitive factors. -/
theorem density_biUnion_le_mul_density_biUnion
    {s : Finset I} {p q : I → Finset A}
    (hp : (s : Set I).PairwiseDisjoint p)
    (hq : ∀ i ∈ s, q i ⊆ p i) {c : ℝ}
    (hlocal : ∀ i ∈ s, density (q i) ≤ c * density (p i)) :
    density (s.biUnion q) ≤ c * density (s.biUnion p) := by
  classical
  have hqdisj : (s : Set I).PairwiseDisjoint q := by
    intro i hi j hj hij
    exact (hp hi hj hij).mono (hq i hi) (hq j hj)
  rw [density_biUnion hqdisj, density_biUnion hp, Finset.mul_sum]
  gcongr with i hi
  exact hlocal i hi

/-- A convenient cardinality form of the preceding lemma. -/
theorem density_biUnion_le_mul_of_card
    {s : Finset I} {p q : I → Finset A}
    (hp : (s : Set I).PairwiseDisjoint p)
    (hq : ∀ i ∈ s, q i ⊆ p i) {c : ℝ}
    (hcard : ∀ i ∈ s, (q i).card ≤ c * (p i).card) :
    density (s.biUnion q) ≤ c * density (s.biUnion p) := by
  apply density_biUnion_le_mul_density_biUnion hp hq
  intro i hi
  simp only [density_eq_card_div_card]
  have hA : 0 ≤ (Fintype.card A : ℝ) := by positivity
  calc
    (q i).card / (Fintype.card A : ℝ) ≤
        (c * (p i).card) / (Fintype.card A : ℝ) :=
      div_le_div_of_nonneg_right (hcard i hi) hA
    _ = c * ((p i).card / (Fintype.card A : ℝ)) := by ring

end DensityOfDisjointUnions

section TilingStatements

/-- Intersection of a finite family of finsets, taken inside the full finite
ambient type. -/
noncomputable def familyInter {X : Type*} [Fintype X] {r : ℕ}
    (D : Fin r → Finset X) : Finset X := by
  classical
  exact Finset.univ.filter fun x ↦ ∀ j, x ∈ D j

@[simp] theorem mem_familyInter {X : Type*} [Fintype X] {r : ℕ}
    (D : Fin r → Finset X) (x : X) :
    x ∈ familyInter D ↔ ∀ j, x ∈ D j := by
  classical
  simp [familyInter]

theorem familyInter_subset {X : Type*} [Fintype X] {r : ℕ}
    (D : Fin r → Finset X) (j : Fin r) : familyInter D ⊆ D j := by
  intro x hx
  exact (mem_familyInter D x).1 hx j

@[simp] theorem familyInter_one {X : Type*} [Fintype X]
    (D : Fin 1 → Finset X) : familyInter D = D 0 := by
  ext x
  simp only [mem_familyInter]
  constructor
  · exact fun h ↦ h 0
  · intro hx j
    simpa only [Subsingleton.elim j 0] using hx

theorem familyInter_succ {X : Type*} [Fintype X] [DecidableEq X] {r : ℕ}
    (D : Fin (r + 1) → Finset X) :
    familyInter D =
      familyInter (fun j : Fin r ↦ D j.castSucc) ∩ D (Fin.last r) := by
  ext x
  simp only [mem_familyInter, Finset.mem_inter]
  constructor
  · intro h
    exact ⟨fun j ↦ h j.castSucc, h (Fin.last r)⟩
  · rintro ⟨hinit, hlast⟩ j
    exact Fin.lastCases hlast hinit j

/-- Exact-dimension form of DKT Lemma 12. -/
def OneInsensitiveTilingAt (k m n : ℕ) (beta : ℝ) : Prop :=
  ∀ (i : Fin k) (D : Finset (Word (k + 1) n)),
    IsLastInsensitive i (D : Set (Word (k + 1) n)) →
    2 * beta < density D →
    ∃ T : SubspaceTiling (Fin m) (Fin (k + 1)) (Fin n),
      T.IsContainedIn D ∧ density (D \ T.covered) < 2 * beta

/-- Exact-dimension form of DKT Corollary 13.  `label` records which old
letter each insensitive factor is paired with; the proof does not require
these labels to be distinct. -/
def InsensitiveIntersectionTilingAt (k r m n : ℕ) (beta : ℝ) : Prop :=
  ∀ (label : Fin r → Fin k) (D : Fin r → Finset (Word (k + 1) n)),
    (∀ j, IsLastInsensitive (label j) (D j : Set (Word (k + 1) n))) →
    2 * (r : ℝ) * beta < density (familyInter D) →
    ∃ T : SubspaceTiling (Fin m) (Fin (k + 1)) (Fin n),
      T.IsContainedIn (familyInter D) ∧
        density (familyInter D \ T.covered) < 2 * (r : ℝ) * beta

/-- Inductive step in DKT Corollary 13: first tile the intersection of the
first `r` factors by `F`-dimensional subspaces, then use the one-factor tiling
inside every retained large tile. -/
theorem InsensitiveIntersectionTilingAt.succ {k r F m n : ℕ} {beta : ℝ}
    (hbeta : 0 < beta) (hrpos : 0 < r)
    (hprev : InsensitiveIntersectionTilingAt k r F n beta)
    (hone : OneInsensitiveTilingAt k m F beta) :
    InsensitiveIntersectionTilingAt k (r + 1) m n beta := by
  classical
  intro label D hD hden
  let Dpre : Fin r → Finset (Word (k + 1) n) := fun j ↦ D j.castSucc
  let labelPre : Fin r → Fin k := fun j ↦ label j.castSucc
  let jlast : Fin (r + 1) := Fin.last r
  let Dlast : Finset (Word (k + 1) n) := D jlast
  have hsplit : familyInter D = familyInter Dpre ∩ Dlast := by
    simpa [Dpre, Dlast, jlast] using familyInter_succ D
  have hall_sub_pre : familyInter D ⊆ familyInter Dpre := by
    rw [hsplit]
    exact Finset.inter_subset_left
  have hmono : density (familyInter D) ≤ density (familyInter Dpre) :=
    density_mono hall_sub_pre
  have hrposR : (0 : ℝ) < r := by exact_mod_cast hrpos
  have hpreDen : 2 * (r : ℝ) * beta < density (familyInter Dpre) := by
    have hden' : 2 * ((r : ℝ) + 1) * beta < density (familyInter D) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hden
    nlinarith
  obtain ⟨T, hTsub, hTloss⟩ :=
    hprev labelPre Dpre (fun j ↦ hD j.castSucc) hpreDen
  have hlastInsensitive :
      IsLastInsensitive (label jlast) (Dlast : Set (Word (k + 1) n)) := by
    simpa [Dlast] using hD jlast
  have hinner : ∀ U : Combinatorics.Subspace (Fin F) (Fin (k + 1)) (Fin n),
      ∃ R : SubspaceTiling (Fin m) (Fin (k + 1)) (Fin F),
        R.IsContainedIn (subspacePullback U Dlast) ∧
          density (subspacePullback U Dlast \ R.covered) ≤ 2 * beta := by
    intro U
    have hins := hlastInsensitive.subspacePullback (label jlast) U Dlast
    by_cases hdense : 2 * beta < density (subspacePullback U Dlast)
    · obtain ⟨R, hRsub, hRloss⟩ :=
        hone (label jlast) (subspacePullback U Dlast) hins hdense
      exact ⟨R, hRsub, hRloss.le⟩
    · refine ⟨SubspaceTiling.empty, ?_, ?_⟩
      · intro V hV
        simp at hV
      · simpa using le_of_not_gt hdense
  choose R hRsub hRloss using hinner
  let S : SubspaceTiling (Fin m) (Fin (k + 1)) (Fin n) := T.bind R
  have hSpre : S.covered ⊆ familyInter Dpre := by
    intro x hx
    rw [show S.covered = T.tiles.biUnion (fun U ↦ ((R U).comp U).covered) by
      exact T.covered_bind R] at hx
    obtain ⟨U, hU, hxU⟩ := Finset.mem_biUnion.mp hx
    exact hTsub U hU (((R U).covered_comp_subset_subspacePoints U) hxU)
  have hSlast : S.covered ⊆ Dlast := by
    intro x hx
    rw [show S.covered = T.tiles.biUnion (fun U ↦ ((R U).comp U).covered) by
      exact T.covered_bind R] at hx
    obtain ⟨U, _hU, hxU⟩ := Finset.mem_biUnion.mp hx
    have hcomp : ((R U).comp U).IsContainedIn Dlast :=
      (((R U).comp_isContainedIn_iff U Dlast)).2 (hRsub U)
    exact (((R U).comp U).covered_subset_iff Dlast).2 hcomp hxU
  have hSsub : S.IsContainedIn (familyInter D) := by
    rw [← S.covered_subset_iff]
    rw [hsplit]
    exact fun _ hx ↦ Finset.mem_inter.mpr ⟨hSpre hx, hSlast hx⟩
  let q := fun U : Combinatorics.Subspace (Fin F) (Fin (k + 1)) (Fin n) ↦
    (subspacePullback U Dlast \ (R U).covered).image U
  have hqsub : ∀ U ∈ T.tiles, q U ⊆ subspacePoints U := by
    intro U _hU x hx
    simp only [q, Finset.mem_image] at hx
    obtain ⟨y, _hy, rfl⟩ := hx
    simp
  have hqlocal : ∀ U ∈ T.tiles,
      density (q U) ≤ (2 * beta) * density (subspacePoints U) := by
    intro U _hU
    rw [show density (q U) = density (subspacePoints U) *
        density (subspacePullback U Dlast \ (R U).covered) by
      exact density_image_subspace U _]
    have hpnonneg := density_nonneg (subspacePoints U)
    have := mul_le_mul_of_nonneg_left (hRloss U) hpnonneg
    nlinarith
  have hqUnion :
      density (T.tiles.biUnion q) ≤ 2 * beta := by
    have hsum := density_biUnion_le_mul_density_biUnion
      T.pairwiseDisjoint hqsub hqlocal
    have hcover : T.tiles.biUnion subspacePoints = T.covered := rfl
    rw [hcover] at hsum
    have hTle := density_le_one T.covered
    have hbnonneg : 0 ≤ 2 * beta := by positivity
    nlinarith
  have hresSub : familyInter D \ S.covered ⊆
      (familyInter Dpre \ T.covered) ∪ T.tiles.biUnion q := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    have hxall := hx'.1
    have hxnotS := hx'.2
    have hxpre : x ∈ familyInter Dpre := hall_sub_pre hxall
    have hxlast : x ∈ Dlast := by
      rw [hsplit] at hxall
      exact (Finset.mem_inter.mp hxall).2
    by_cases hxT : x ∈ T.covered
    · apply Finset.mem_union.mpr
      apply Or.inr
      obtain ⟨U, hU, hxU⟩ := (T.mem_covered x).1 hxT
      apply Finset.mem_biUnion.mpr
      refine ⟨U, hU, ?_⟩
      rw [show q U =
          (subspacePullback U Dlast \ (R U).covered).image U by rfl]
      rw [mem_subspacePoints] at hxU
      obtain ⟨y, hy⟩ := hxU
      subst x
      apply Finset.mem_image.mpr
      refine ⟨y, Finset.mem_sdiff.mpr ⟨?_, ?_⟩, rfl⟩
      · exact (mem_subspacePullback U Dlast y).2 hxlast
      · intro hycover
        apply hxnotS
        rw [show S.covered = T.tiles.biUnion
            (fun V ↦ ((R V).comp V).covered) by exact T.covered_bind R]
        apply Finset.mem_biUnion.mpr
        refine ⟨U, hU, ?_⟩
        rw [(R U).covered_comp U]
        exact Finset.mem_image_of_mem U hycover
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hxpre, hxT⟩))
  refine ⟨S, hSsub, ?_⟩
  have hresDen := density_mono hresSub
  have hunion := density_union_le_add
    (familyInter Dpre \ T.covered) (T.tiles.biUnion q)
  have htarget' :
      density (familyInter D \ S.covered) < 2 * (r : ℝ) * beta + 2 * beta := by
    linarith
  have hcast : (r + 1 : ℕ) = r + 1 := rfl
  push_cast
  nlinarith

/-- Qualitative form of DKT Corollary 13.  If the one-insensitive-set tiling
lemma is available in some dimension for every requested tile dimension,
then the same is true for every nonempty finite intersection of insensitive
sets. -/
theorem exists_insensitiveIntersectionTilingAt {k : ℕ} {beta : ℝ}
    (hbeta : 0 < beta)
    (hone : ∀ m, ∃ n, OneInsensitiveTilingAt k m n beta) :
    ∀ r m, ∃ n, InsensitiveIntersectionTilingAt k (r + 1) m n beta := by
  intro r
  induction r with
  | zero =>
      intro m
      obtain ⟨n, hn⟩ := hone m
      refine ⟨n, ?_⟩
      intro label D hD hden
      have hden₀ : 2 * beta < density (D 0) := by
        simpa [familyInter_one] using hden
      obtain ⟨T, hTsub, hTloss⟩ := hn (label 0) (D 0) (hD 0) hden₀
      refine ⟨T, ?_, ?_⟩
      · simpa [familyInter_one] using hTsub
      · simpa [familyInter_one] using hTloss
  | succ r ihr =>
      intro m
      obtain ⟨F, hF⟩ := hone m
      obtain ⟨n, hn⟩ := ihr F
      exact ⟨n, hn.succ hbeta (Nat.succ_pos r) hF⟩

/-- Lower-bound-preserving form of the qualitative intersection tiling
theorem.  Only the outermost recursive tiling needs to meet the requested
ambient-dimension bound; dimensions used for the inner tilings may be chosen
freely. -/
theorem exists_insensitiveIntersectionTilingAt_ge {k : ℕ} {beta : ℝ}
    (hbeta : 0 < beta)
    (hone : ∀ m N, ∃ n, N ≤ n ∧ OneInsensitiveTilingAt k m n beta) :
    ∀ r m N, ∃ n, N ≤ n ∧
      InsensitiveIntersectionTilingAt k (r + 1) m n beta := by
  intro r
  induction r with
  | zero =>
      intro m N
      obtain ⟨n, hNn, hn⟩ := hone m N
      refine ⟨n, hNn, ?_⟩
      intro label D hD hden
      have hden₀ : 2 * beta < density (D 0) := by
        simpa [familyInter_one] using hden
      obtain ⟨T, hTsub, hTloss⟩ := hn (label 0) (D 0) (hD 0) hden₀
      refine ⟨T, ?_, ?_⟩
      · simpa [familyInter_one] using hTsub
      · simpa [familyInter_one] using hTloss
  | succ r ihr =>
      intro m N
      obtain ⟨F, _hzeroF, hF⟩ := hone m 0
      obtain ⟨n, hNn, hn⟩ := ihr F N
      exact ⟨n, hNn, hn.succ hbeta (Nat.succ_pos r) hF⟩

end TilingStatements

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/SubspaceDensity.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Density inside combinatorial subspaces

This file connects the combinatorial `Subspace` API with the uniform-density
API used in the density Hales--Jewett argument.  Pullback density is the density
of the parameter words whose images belong to the ambient family.  Since every
proper subspace is injective in its parameter word, this is exactly relative
density inside the image of the subspace.

The second half gives two exact counting identities used repeatedly later:

* averaging the pullback densities of all fixed-suffix extensions is the
  pullback density on the corresponding sum-coordinate subspace;
* the fraction of internal lines contained in a family is both a finite
  density and the average of the corresponding containment indicator.
-/

open scoped BigOperators



open Set

attribute [local instance 1] Classical.dec

variable {η ζ α ι κ : Type*}

/-! ## Pullback and relative density -/

/-- Pull an ambient finset back to the parameter cube of a subspace. -/
noncomputable def pullbackFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    Finset (η → α) := by
  classical
  exact Finset.univ.filter fun x ↦ U x ∈ A

@[simp] theorem mem_pullbackFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) (x : η → α) :
    x ∈ pullbackFinset U A ↔ U x ∈ A := by
  classical
  simp [pullbackFinset]

/-- Pull an ambient set back to the parameter cube, represented as a finset. -/
noncomputable def pullbackSetFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Set (ι → α)) :
    Finset (η → α) := by
  classical
  exact Finset.univ.filter fun x ↦ U x ∈ A

@[simp] theorem mem_pullbackSetFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Set (ι → α)) (x : η → α) :
    x ∈ pullbackSetFinset U A ↔ U x ∈ A := by
  classical
  simp [pullbackSetFinset]

@[simp] theorem pullback_setFinset [Fintype (η → α)] [Fintype (ι → α)]
    (U : Combinatorics.Subspace η α ι) (A : Set (ι → α)) :
    pullbackFinset U (setFinset A) = pullbackSetFinset U A := by
  classical
  ext x
  simp

/-- Density of an ambient finset when viewed in the coordinates of a subspace. -/
noncomputable def subspaceDensityFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : ℝ :=
  density (pullbackFinset U A)

/-- Density of an ambient set when viewed in the coordinates of a subspace. -/
noncomputable def subspaceDensity [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Set (ι → α)) : ℝ :=
  density (pullbackSetFinset U A)

@[simp] theorem subspaceDensity_setFinset [Fintype (η → α)] [Fintype (ι → α)]
    (U : Combinatorics.Subspace η α ι) (A : Set (ι → α)) :
    subspaceDensityFinset U (setFinset A) = subspaceDensity U A := by
  rw [subspaceDensityFinset, subspaceDensity, pullback_setFinset]

/-- The finite image of a subspace. -/
noncomputable def subspaceImageFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) : Finset (ι → α) := by
  classical
  exact Finset.univ.image U

@[simp] theorem mem_subspaceImageFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (y : ι → α) :
    y ∈ subspaceImageFinset U ↔ y ∈ Set.range U := by
  classical
  simp [subspaceImageFinset]

theorem card_subspaceImageFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) :
    (subspaceImageFinset U).card = Fintype.card (η → α) := by
  classical
  simp [subspaceImageFinset, Finset.card_image_of_injective _ U.parameter_injective]

/-- Relative density of `A` inside the finite reference family `S`. -/
noncomputable def relativeDensityFinset {γ : Type*} [DecidableEq γ]
    (A S : Finset γ) : ℝ :=
  ((A ∩ S).card : ℝ) / S.card

/-- Relative density of `A` inside `S`, for sets in a finite ambient type. -/
noncomputable def relativeDensity [Fintype α] [DecidableEq α]
    (A S : Set α) : ℝ :=
  relativeDensityFinset (setFinset A) (setFinset S)

theorem card_pullback_eq_inter_image [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    (pullbackFinset U A).card = (A ∩ subspaceImageFinset U).card := by
  classical
  refine Finset.card_bij (fun x _ ↦ U x) ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_inter.2 ⟨(mem_pullbackFinset U A x).1 hx,
      (mem_subspaceImageFinset U (U x)).2 ⟨x, rfl⟩⟩
  · intro x hx y hy hxy
    exact U.parameter_injective hxy
  · intro y hy
    obtain ⟨hyA, hyU⟩ := Finset.mem_inter.1 hy
    obtain ⟨x, rfl⟩ := (mem_subspaceImageFinset U y).1 hyU
    exact ⟨x, (mem_pullbackFinset U A x).2 hyA, rfl⟩

/-- Pullback density is relative density inside the subspace image. -/
theorem subspaceDensityFinset_eq_relative [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    subspaceDensityFinset U A = relativeDensityFinset A (subspaceImageFinset U) := by
  rw [subspaceDensityFinset, density_eq_card_div_card, relativeDensityFinset,
    card_pullback_eq_inter_image, card_subspaceImageFinset]

theorem setFinset_range_subspace [Fintype (η → α)] [Fintype (ι → α)]
    (U : Combinatorics.Subspace η α ι) :
    setFinset (Set.range U) = subspaceImageFinset U := by
  classical
  ext y
  simp

/-- Set-valued form of pullback density as relative density in the image. -/
theorem subspaceDensity_eq_relative [Fintype (η → α)] [Fintype (ι → α)]
    (U : Combinatorics.Subspace η α ι) (A : Set (ι → α)) :
    subspaceDensity U A = relativeDensity A (Set.range U) := by
  rw [← subspaceDensity_setFinset, subspaceDensityFinset_eq_relative,
    relativeDensity, setFinset_range_subspace]

@[simp] theorem pullbackFinset_comp [Fintype (η → α)] [Fintype (ζ → α)]
    (U : Combinatorics.Subspace η α ι) (V : Combinatorics.Subspace ζ α η)
    (A : Finset (ι → α)) :
    pullbackFinset (U.comp V) A = pullbackFinset V (pullbackFinset U A) := by
  classical
  ext x
  simp [Combinatorics.Subspace.comp_apply]

@[simp] theorem pullbackSetFinset_comp [Fintype (η → α)] [Fintype (ζ → α)]
    (U : Combinatorics.Subspace η α ι) (V : Combinatorics.Subspace ζ α η)
    (A : Set (ι → α)) :
    pullbackSetFinset (U.comp V) A = pullbackSetFinset V (U ⁻¹' A) := by
  classical
  ext x
  simp [Combinatorics.Subspace.comp_apply]

@[simp] theorem subspaceDensityFinset_comp [Fintype (η → α)] [Fintype (ζ → α)]
    (U : Combinatorics.Subspace η α ι) (V : Combinatorics.Subspace ζ α η)
    (A : Finset (ι → α)) :
    subspaceDensityFinset (U.comp V) A =
      subspaceDensityFinset V (pullbackFinset U A) := by
  simp [subspaceDensityFinset]

@[simp] theorem subspaceDensity_comp [Fintype (η → α)] [Fintype (ζ → α)]
    (U : Combinatorics.Subspace η α ι) (V : Combinatorics.Subspace ζ α η)
    (A : Set (ι → α)) :
    subspaceDensity (U.comp V) A = subspaceDensity V (U ⁻¹' A) := by
  simp [subspaceDensity]

/-! ## Exact average over fixed-suffix extensions -/



section
open Combinatorics

section
open Combinatorics.Subspace

/-- The identity combinatorial subspace. -/
private def _root_.Combinatorics.Subspace.coordinateIdentity (α η : Type*) : Subspace η α η where
  idxFun := Sum.inr
  proper e := ⟨e, rfl⟩

@[simp] private theorem _root_.Combinatorics.Subspace.coordinateIdentity_apply (x : η → α) :
    coordinateIdentity α η x = x := by
  funext e
  rfl

end

end



open Set

attribute [local instance 1] Classical.dec

variable {η ζ α ι κ : Type*}

/-- The set of pairs `(suffix, parameter)` whose extended word lies in `A`. -/
noncomputable def extensionPullback [Fintype (κ → α)] [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α)) :
    Finset ((κ → α) × (η → α)) := by
  classical
  exact Finset.univ.filter fun p ↦
    Combinatorics.Subspace.sumWord (U p.2) p.1 ∈ A

@[simp] theorem mem_extensionPullback [Fintype (κ → α)] [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α))
    (p : (κ → α) × (η → α)) :
    p ∈ extensionPullback U A ↔
      Combinatorics.Subspace.sumWord (U p.2) p.1 ∈ A := by
  classical
  simp [extensionPullback]

theorem fiber_extensionPullback [Fintype (κ → α)] [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α))
    (y : κ → α) :
    fiber (extensionPullback U A) y = pullbackFinset (U.extendRightWord y) A := by
  classical
  ext x
  simp [Combinatorics.Subspace.extendRightWord_apply]

/-- Fubini's identity for all fixed-suffix extensions of a subspace. -/
theorem density_extensionPullback_eq_average
    [Fintype (η → α)] [Fintype (κ → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α)) :
    density (extensionPullback U A) =
      average fun y : κ → α ↦ subspaceDensityFinset (U.extendRightWord y) A := by
  rw [density_eq_average_fiber]
  apply congrArg average
  funext y
  rw [fiber_extensionPullback]
  rfl

/-- Rebracket a pair `(suffix, parameter)` as a word on a sum of coordinate
types. -/
def extensionWordEquiv : ((κ → α) × (η → α)) ≃ (η ⊕ κ → α) where
  toFun p := Combinatorics.Subspace.sumWord p.2 p.1
  invFun z := (z ∘ Sum.inr, z ∘ Sum.inl)
  left_inv p := by
    ext q
    · rfl
    · rfl
  right_inv z := by
    funext q
    cases q <;> rfl

theorem extensionWord_mem_sumPullback
    [Fintype (η ⊕ κ → α)] [Fintype (κ → α)] [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α))
    (p : (κ → α) × (η → α)) :
    extensionWordEquiv p ∈
        pullbackFinset (U.sum (Combinatorics.Subspace.coordinateIdentity α κ)) A ↔
      p ∈ extensionPullback U A := by
  classical
  simp [extensionWordEquiv, Combinatorics.Subspace.sum_apply_sumWord]

theorem card_extensionPullback_eq_sumPullback
    [Fintype (η ⊕ κ → α)] [Fintype (κ → α)] [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α)) :
    (extensionPullback U A).card =
      (pullbackFinset
        (U.sum (Combinatorics.Subspace.coordinateIdentity α κ)) A).card := by
  classical
  refine Finset.card_bij (fun p _ ↦ extensionWordEquiv p) ?_ ?_ ?_
  · intro p hp
    exact (extensionWord_mem_sumPullback U A p).2 hp
  · intro p hp q hq hpq
    exact extensionWordEquiv.injective hpq
  · intro z hz
    refine ⟨extensionWordEquiv.symm z, ?_, extensionWordEquiv.apply_symm_apply z⟩
    apply (extensionWord_mem_sumPullback U A (extensionWordEquiv.symm z)).1
    rw [extensionWordEquiv.apply_symm_apply]
    exact hz

/-- The pair-model extension pullback and the sum-subspace pullback have the
same density, including their ambient denominators. -/
theorem density_extensionPullback_eq_sumSubspaceDensity
    [Fintype (η ⊕ κ → α)] [Fintype (κ → α)] [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α)) :
    density (extensionPullback U A) =
      subspaceDensityFinset
        (U.sum (Combinatorics.Subspace.coordinateIdentity α κ)) A := by
  unfold subspaceDensityFinset density
  rw [card_extensionPullback_eq_sumPullback]
  congr 1
  norm_cast
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  exact Nat.card_congr
    (extensionWordEquiv : ((κ → α) × (η → α)) ≃ (η ⊕ κ → α))

/-- Exact average of the densities on all fixed-suffix extensions. -/
theorem average_subspaceDensity_extendRightWord
    [Fintype (η ⊕ κ → α)] [Fintype (η → α)] [Fintype (κ → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α)) :
    average (fun y : κ → α ↦ subspaceDensityFinset (U.extendRightWord y) A) =
      subspaceDensityFinset
        (U.sum (Combinatorics.Subspace.coordinateIdentity α κ)) A := by
  rw [← density_extensionPullback_eq_average,
    density_extensionPullback_eq_sumSubspaceDensity]

/-! ## Counting internal lines -/

/-- Internal parameter lines all of whose points map into `A`. -/
noncomputable def internalLines [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    Finset (Combinatorics.Line α η) := by
  classical
  exact Finset.univ.filter fun l ↦ ∀ a, U (l a) ∈ A

@[simp] theorem mem_internalLines [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α))
    (l : Combinatorics.Line α η) :
    l ∈ internalLines U A ↔ ∀ a, U (l a) ∈ A := by
  classical
  simp [internalLines]

/-- Fraction of the internal lines of `U` that are contained in `A`. -/
noncomputable def internalLineFraction [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : ℝ :=
  density (internalLines U A)

theorem internalLineFraction_eq_card [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    internalLineFraction U A =
      ((internalLines U A).card : ℝ) / Fintype.card (Combinatorics.Line α η) := by
  rfl

theorem internalLineFraction_nonneg [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    0 ≤ internalLineFraction U A :=
  density_nonneg _

theorem internalLineFraction_le_one [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    internalLineFraction U A ≤ 1 :=
  density_le_one _

/-- Internal-line fraction as an exact average of containment indicators. -/
theorem internalLineFraction_eq_average_indicator [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    internalLineFraction U A =
      average fun l : Combinatorics.Line α η ↦
        if ∀ a, U (l a) ∈ A then (1 : ℝ) else 0 := by
  classical
  rw [internalLineFraction, ← average_indicator]
  apply congrArg average
  funext l
  simp

/-- Equivalent product form of the internal-line containment indicator. -/
theorem internalLineFraction_eq_average_prod [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    internalLineFraction U A =
      average fun l : Combinatorics.Line α η ↦
        ∏ a, if U (l a) ∈ A then (1 : ℝ) else 0 := by
  rw [internalLineFraction_eq_average_indicator]
  apply congrArg average
  funext l
  classical
  by_cases h : ∀ a, U (l a) ∈ A
  · simp [h]
  · push Not at h
    obtain ⟨a, ha⟩ := h
    have hn : ¬ ∀ b, U (l b) ∈ A := fun hall ↦ ha (hall a)
    simp only [hn, if_false]
    exact (Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])).symm

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/DensityBridges.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Compatibility bridges for the Erdős 171 density APIs

`SubspaceDensity` and `Tiling` introduced the same two finite constructions
under names adapted to their respective uses.  This file keeps both public
APIs stable and records their extensional equality.  It also records the exact
ambient-denominator change when a finset of words is included from `Fin k` into
`Fin (k + 1)`.
-/

open Combinatorics



section SubspaceAPIs

variable {eta alpha iota : Type*}

/-- The density API's pullback and the tiling API's pullback are the same
finset of parameter words. -/
@[simp] theorem pullbackFinset_eq_subspacePullback
    [Fintype (eta → alpha)]
    (U : Subspace eta alpha iota) (D : Finset (iota → alpha)) :
    pullbackFinset U D = subspacePullback U D := by
  classical
  ext x
  simp

/-- The density API's finite subspace image is the tiling API's tile. -/
@[simp] theorem subspaceImageFinset_eq_subspacePoints
    [Fintype (eta → alpha)] [DecidableEq (iota → alpha)]
    (U : Subspace eta alpha iota) :
    subspaceImageFinset U = subspacePoints U := by
  classical
  ext x
  simp

/-- Pullback density may equivalently be expressed using the tiling pullback. -/
theorem subspaceDensityFinset_eq_density_subspacePullback
    [Fintype (eta → alpha)]
    (U : Subspace eta alpha iota) (D : Finset (iota → alpha)) :
    subspaceDensityFinset U D = density (subspacePullback U D) := by
  rw [subspaceDensityFinset, pullbackFinset_eq_subspacePullback]

/-- Relative density inside the density API's image is the same expression
with the tiling API's tile. -/
theorem subspaceDensityFinset_eq_relative_subspacePoints
    [Fintype (eta → alpha)] [DecidableEq (iota → alpha)]
    (U : Subspace eta alpha iota) (D : Finset (iota → alpha)) :
    subspaceDensityFinset U D = relativeDensityFinset D (subspacePoints U) := by
  rw [subspaceDensityFinset_eq_relative,
    subspaceImageFinset_eq_subspacePoints]
  congr

/-- The iteration module's specialized pullback is the canonical density
pullback. -/
@[simp] theorem iterationPullback_eq_pullbackFinset {d t n : ℕ}
    (U : Subspace (Fin d) (Fin t) (Fin n)) (A : Finset (Word t n)) :
    iterationPullback U A = pullbackFinset U A := by
  classical
  ext x
  simp

/-- Direct compatibility between the iteration and tiling pullback names. -/
theorem iterationPullback_eq_subspacePullback {d t n : ℕ}
    (U : Subspace (Fin d) (Fin t) (Fin n)) (A : Finset (Word t n)) :
    iterationPullback U A = subspacePullback U A := by
  rw [iterationPullback_eq_pullbackFinset,
    pullbackFinset_eq_subspacePullback]

end SubspaceAPIs

section AlphabetInclusion

variable {eta : Type*} {k : ℕ}

/-- The older finite-word name and the generic sum-coordinate name for the
alphabet inclusion agree.  The orientation makes mixed files normalize to
`liftWord`. -/
@[simp] theorem restrictWord_eq_liftWord {m : ℕ} (x : Word k m) :
    restrictWord x = liftWord x :=
  rfl

/-- Exact density after including a finset into the alphabet with one new
letter.  Its cardinality is unchanged, but the uniform ambient denominator is
the cardinality of the enlarged word cube. -/
theorem density_liftFinset_exact
    [Fintype (eta → Fin (k + 1))] [DecidableEq (eta → Fin (k + 1))]
    (A : Finset (eta → Fin k)) :
    density (liftFinset A) =
      (A.card : ℝ) / Fintype.card (eta → Fin (k + 1)) := by
  rw [density_eq_card_div_card, card_liftFinset]

/-- Natural-number specialization of `density_liftFinset_exact`: the new
ambient cube has exactly `(k+1)^m` words. -/
theorem density_liftFinset_fin_exact {m : ℕ} (A : Finset (Word k m)) :
    density (liftFinset A) = (A.card : ℝ) / (k + 1) ^ m := by
  rw [density_liftFinset_exact]
  simp [Word]

/-- The numerator in the preceding formula is unchanged. -/
theorem card_liftFinset_exact
    [DecidableEq (eta → Fin (k + 1))] (A : Finset (eta → Fin k)) :
    (liftFinset A).card = A.card :=
  card_liftFinset A

end AlphabetInclusion

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/GrahamRothschild.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The line case of the finite Graham--Rothschild theorem

This file proves the precise finite Ramsey theorem for combinatorial lines used
by Dodos--Kanellopoulos--Tyros in their proof of density Hales--Jewett.  The
proof is the standard repeated-Hales--Jewett fusion (Shelah's ``first moving
block'' proof): after passing to a block subspace, the color of a line depends
only on its first moving block.  A final pigeonhole argument makes those block
colors equal.

Only the line case is stated.  A superficially stronger statement obtained by
coloring Mathlib's *labelled* higher-dimensional `Subspace`s is false without
an ordering convention: in dimension two one may color a parameter word by
which labelled variable occurs first.  Lines have only one variable, so this
obstruction is absent here.
-/



open Function
open Combinatorics

namespace GrahamRothschild

universe u v w x

variable {α : Type u} {P : Type v} {B : Type w} {I : Type x}

/-- A line already moves in the old (prefix) coordinates. -/
def PrefixMoving (q : Line α (P ⊕ Fin m)) : Prop :=
  ∃ p : P, q.idxFun (Sum.inl p) = none

/-- Two lines have the same first moving coordinate among their `Fin m` tail
coordinates.  This definition remains useful when either line also moves in
the prefix. -/
def SameFirstTail (q r : Line α (P ⊕ Fin m)) : Prop :=
  ∃ i : Fin m,
    q.idxFun (Sum.inr i) = none ∧
      r.idxFun (Sum.inr i) = none ∧
      ∀ j : Fin m, j < i →
        q.idxFun (Sum.inr j) ≠ none ∧ r.idxFun (Sum.inr j) ≠ none

/-- The fusion invariant.  Lines agreeing on the prefix have equal colors if
the prefix already moves, or if their first moving tail block is the same. -/
def IsFirstBlockCanonical (C : Line α I → Bool)
    (U : Subspace (P ⊕ Fin m) α I) : Prop :=
  ∀ q r : Line α (P ⊕ Fin m),
    (∀ p : P, q.idxFun (Sum.inl p) = r.idxFun (Sum.inl p)) →
    (PrefixMoving q ∨ SameFirstTail q r) →
    C (U.lineMap q) = C (U.lineMap r)

/-- Replace the current block by a word over letters and pointers into the
prefix.  The current block is the `0` coordinate of `Fin (m+1)`; all later
blocks are shifted down by one. -/
def specializeIdx (x : B → α ⊕ P) (q : Line α (P ⊕ Fin (m + 1))) :
    ((P ⊕ B) ⊕ Fin m) → Option α
  | Sum.inl (Sum.inl p) => q.idxFun (Sum.inl p)
  | Sum.inl (Sum.inr b) => (x b).elim some (fun p => q.idxFun (Sum.inl p))
  | Sum.inr j => q.idxFun (Sum.inr j.succ)

/-- The patterns for which specializing the current block still leaves a
proper line.  The only excluded case is when the current block is the unique
source of a wildcard before all later blocks. -/
def Specializable (q : Line α (P ⊕ Fin (m + 1))) : Prop :=
  PrefixMoving q ∨ q.idxFun (Sum.inr 0) ≠ none

theorem specializeIdx_proper (x : B → α ⊕ P)
    (q : Line α (P ⊕ Fin (m + 1))) (hq : Specializable q) :
    ∃ i, specializeIdx x q i = none := by
  rcases hq with hp | h0
  · obtain ⟨p, hp⟩ := hp
    exact ⟨Sum.inl (Sum.inl p), hp⟩
  · obtain ⟨i, hi⟩ := q.proper
    cases i with
    | inl p => exact ⟨Sum.inl (Sum.inl p), hi⟩
    | inr i =>
      cases i using Fin.cases with
      | zero => exact (h0 hi).elim
      | succ j => exact ⟨Sum.inr j, hi⟩

/-- Specialization as a proper line. -/
def specializeLine (x : B → α ⊕ P) (q : Line α (P ⊕ Fin (m + 1)))
    (hq : Specializable q) : Line α ((P ⊕ B) ⊕ Fin m) where
  idxFun := specializeIdx x q
  proper := specializeIdx_proper x q hq

/-- Compress a Hales--Jewett line in the current block to one new parameter
coordinate. -/
def compressSubspace (h : Line (α ⊕ P) B) :
    Subspace (P ⊕ Fin (m + 1)) α ((P ⊕ B) ⊕ Fin m) where
  idxFun
    | Sum.inl (Sum.inl p) => Sum.inr (Sum.inl p)
    | Sum.inl (Sum.inr b) =>
        (h.idxFun b).elim (Sum.inr (Sum.inr 0)) (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl))
    | Sum.inr j => Sum.inr (Sum.inr j.succ)
  proper
    | Sum.inl p => ⟨Sum.inl (Sum.inl p), rfl⟩
    | Sum.inr i => by
        cases i using Fin.cases with
        | zero =>
            obtain ⟨b, hb⟩ := h.proper
            exact ⟨Sum.inl (Sum.inr b), by simp [hb]⟩
        | succ j => exact ⟨Sum.inr j, rfl⟩

theorem compress_lineMap_eq_specialize_inl
    (h : Line (α ⊕ P) B) (q : Line α (P ⊕ Fin (m + 1)))
    (hq : Specializable q) (a : α)
    (h0 : q.idxFun (Sum.inr 0) = some a) :
    (compressSubspace (m := m) h).lineMap q =
      specializeLine (h (Sum.inl a)) q hq := by
  ext i
  cases i with
  | inl i =>
    cases i with
    | inl p => rfl
    | inr b =>
      cases hb : h.idxFun b with
      | none => simp [compressSubspace, Subspace.lineMap, specializeLine, specializeIdx, hb, h0]
      | some z =>
        cases z <;>
          simp [compressSubspace, Subspace.lineMap, specializeLine, specializeIdx, hb,
            Line.coe_apply]
  | inr j => rfl

theorem compress_lineMap_eq_specialize_inr
    (h : Line (α ⊕ P) B) (q : Line α (P ⊕ Fin (m + 1)))
    (hq : Specializable q) (p : P)
    (h0 : q.idxFun (Sum.inr 0) = q.idxFun (Sum.inl p)) :
    (compressSubspace (m := m) h).lineMap q = specializeLine (h (Sum.inr p)) q hq := by
  ext i
  cases i with
  | inl i =>
    cases i with
    | inl p' => rfl
    | inr b =>
      cases hb : h.idxFun b with
      | none => simp [compressSubspace, Subspace.lineMap, specializeLine, specializeIdx, hb, h0]
      | some z =>
        cases z <;>
          simp [compressSubspace, Subspace.lineMap, specializeLine, specializeIdx, hb,
            Line.coe_apply]
  | inr j => rfl

theorem specialize_prefix_eq (x : B → α ⊕ P)
    (q r : Line α (P ⊕ Fin (m + 1)))
    (hq : Specializable q) (hr : Specializable r)
    (hpre : ∀ p : P, q.idxFun (Sum.inl p) = r.idxFun (Sum.inl p)) :
    ∀ s : P ⊕ B,
      (specializeLine x q hq).idxFun (Sum.inl s) =
        (specializeLine x r hr).idxFun (Sum.inl s) := by
  intro s
  cases s with
  | inl p => exact hpre p
  | inr b =>
      cases hx : x b with
      | inl a => simp [specializeLine, specializeIdx, hx]
      | inr p => simpa [specializeLine, specializeIdx, hx] using hpre p

theorem specialize_prefixMoving (x : B → α ⊕ P)
    (q : Line α (P ⊕ Fin (m + 1))) (hq : Specializable q)
    (hp : PrefixMoving q) :
    PrefixMoving (P := P ⊕ B) (m := m) (specializeLine x q hq) := by
  obtain ⟨p, hp⟩ := hp
  exact ⟨Sum.inl p, hp⟩

theorem specialize_sameFirstTail_succ (x : B → α ⊕ P)
    (q r : Line α (P ⊕ Fin (m + 1)))
    (hq : Specializable q) (hr : Specializable r) (i : Fin m)
    (hqi : q.idxFun (Sum.inr i.succ) = none)
    (hri : r.idxFun (Sum.inr i.succ) = none)
    (hmin : ∀ j : Fin (m + 1), j < i.succ →
      q.idxFun (Sum.inr j) ≠ none ∧ r.idxFun (Sum.inr j) ≠ none) :
    SameFirstTail (P := P ⊕ B) (specializeLine x q hq) (specializeLine x r hr) := by
  refine ⟨i, hqi, hri, ?_⟩
  intro j hj
  exact hmin j.succ (by simpa using hj)

theorem compress_prefix_eq_of_current_none
    (h : Line (α ⊕ P) B) (q r : Line α (P ⊕ Fin (m + 1)))
    (hpre : ∀ p : P, q.idxFun (Sum.inl p) = r.idxFun (Sum.inl p))
    (hq0 : q.idxFun (Sum.inr 0) = none)
    (hr0 : r.idxFun (Sum.inr 0) = none) :
    ∀ s : P ⊕ B,
      ((compressSubspace (m := m) h).lineMap q).idxFun (Sum.inl s) =
        ((compressSubspace (m := m) h).lineMap r).idxFun (Sum.inl s) := by
  intro s
  cases s with
  | inl p => exact hpre p
  | inr b =>
      cases hb : h.idxFun b with
      | none => simp [compressSubspace, Subspace.lineMap, hb, hq0, hr0]
      | some z =>
          cases z with
          | inl a => simp [compressSubspace, Subspace.lineMap, hb]
          | inr p => simpa [compressSubspace, Subspace.lineMap, hb] using hpre p

theorem compress_prefixMoving_of_current_none
    (h : Line (α ⊕ P) B) (q : Line α (P ⊕ Fin (m + 1)))
    (hq0 : q.idxFun (Sum.inr 0) = none) :
    PrefixMoving (P := P ⊕ B) (m := m) ((compressSubspace (m := m) h).lineMap q) := by
  obtain ⟨b, hb⟩ := h.proper
  refine ⟨Sum.inr b, ?_⟩
  simp [compressSubspace, Subspace.lineMap, hb, hq0]

/-- Repeated Hales--Jewett fusion.  The returned subspace is canonical for the
first moving tail block, relative to an arbitrary finite prefix type `P`. -/
theorem exists_firstBlockCanonical (α : Type) [Finite α] (P : Type) [Finite P] :
    ∀ m : ℕ, ∃ (I : Type) (_ : Fintype I),
      ∀ C : Line α I → Bool,
        ∃ U : Subspace (P ⊕ Fin m) α I, IsFirstBlockCanonical C U := by
  classical
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite P
  intro m
  induction m generalizing P with
  | zero =>
      refine ⟨P ⊕ Fin 0, inferInstance, fun C => ⟨default, ?_⟩⟩
      intro q r hpre _
      have hqr : q = r := by
        apply Line.ext
        funext i
        cases i with
        | inl p => exact hpre p
        | inr i => exact Fin.elim0 i
      subst r
      rfl
  | succ m ih =>
      let pattern := {q : Line α (P ⊕ Fin (m + 1)) // Specializable q}
      obtain ⟨B, instB, hB⟩ :=
        Line.exists_mono_in_high_dimension (α ⊕ P) (pattern → Bool)
      letI : Fintype B := instB
      obtain ⟨I, instI, hI⟩ := ih (P := P ⊕ B)
      letI : Fintype I := instI
      refine ⟨I, instI, fun C => ?_⟩
      obtain ⟨V, hV⟩ := hI C
      let D : (B → α ⊕ P) → pattern → Bool := fun x q =>
        C (V.lineMap (specializeLine x q.1 q.2))
      obtain ⟨h, c, hc⟩ := hB D
      let Q : Subspace (P ⊕ Fin (m + 1)) α ((P ⊕ B) ⊕ Fin m) :=
        compressSubspace h
      refine ⟨V.comp Q, ?_⟩
      intro q r hpre hkey
      have hcolors (z z' : α ⊕ P) : D (h z) = D (h z') :=
        (hc z).trans (hc z').symm
      rcases hkey with hp | htail
      · obtain ⟨p, hp⟩ := hp
        have hrp : r.idxFun (Sum.inl p) = none := by rw [← hpre p]; exact hp
        have hsq : Specializable q := Or.inl ⟨p, hp⟩
        have hsr : Specializable r := Or.inl ⟨p, hrp⟩
        cases hq0 : q.idxFun (Sum.inr 0) with
        | none =>
          cases hr0 : r.idxFun (Sum.inr 0) with
          | none =>
            have hqcomp := compress_lineMap_eq_specialize_inr
              (m := m) h q hsq p (by rw [hq0, hp])
            have hrcomp := compress_lineMap_eq_specialize_inr
              (m := m) h r hsr p (by rw [hr0, hrp])
            calc
              C ((V.comp Q).lineMap q) =
                  C (V.lineMap (specializeLine (h (Sum.inr p)) q hsq)) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hqcomp]
              _ = C (V.lineMap (specializeLine (h (Sum.inr p)) r hsr)) := by
                    apply hV
                    · exact specialize_prefix_eq _ q r hsq hsr hpre
                    · exact Or.inl (specialize_prefixMoving _ q hsq ⟨p, hp⟩)
              _ = C ((V.comp Q).lineMap r) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hrcomp]
          | some b =>
            have hqcomp := compress_lineMap_eq_specialize_inr
              (m := m) h q hsq p (by rw [hq0, hp])
            have hrcomp := compress_lineMap_eq_specialize_inl
              (m := m) h r hsr b hr0
            have hmono := congrFun (hcolors (Sum.inr p) (Sum.inl b)) ⟨q, hsq⟩
            calc
              C ((V.comp Q).lineMap q) =
                  C (V.lineMap (specializeLine (h (Sum.inr p)) q hsq)) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hqcomp]
              _ = C (V.lineMap (specializeLine (h (Sum.inl b)) q hsq)) := hmono
              _ = C (V.lineMap (specializeLine (h (Sum.inl b)) r hsr)) := by
                    apply hV
                    · exact specialize_prefix_eq _ q r hsq hsr hpre
                    · exact Or.inl (specialize_prefixMoving _ q hsq ⟨p, hp⟩)
              _ = C ((V.comp Q).lineMap r) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hrcomp]
        | some a =>
          cases hr0 : r.idxFun (Sum.inr 0) with
          | none =>
            have hqcomp := compress_lineMap_eq_specialize_inl
              (m := m) h q hsq a hq0
            have hrcomp := compress_lineMap_eq_specialize_inr
              (m := m) h r hsr p (by rw [hr0, hrp])
            have hmono := congrFun (hcolors (Sum.inl a) (Sum.inr p)) ⟨q, hsq⟩
            calc
              C ((V.comp Q).lineMap q) =
                  C (V.lineMap (specializeLine (h (Sum.inl a)) q hsq)) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hqcomp]
              _ = C (V.lineMap (specializeLine (h (Sum.inr p)) q hsq)) := hmono
              _ = C (V.lineMap (specializeLine (h (Sum.inr p)) r hsr)) := by
                    apply hV
                    · exact specialize_prefix_eq _ q r hsq hsr hpre
                    · exact Or.inl (specialize_prefixMoving _ q hsq ⟨p, hp⟩)
              _ = C ((V.comp Q).lineMap r) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hrcomp]
          | some b =>
            have hqcomp := compress_lineMap_eq_specialize_inl
              (m := m) h q hsq a hq0
            have hrcomp := compress_lineMap_eq_specialize_inl
              (m := m) h r hsr b hr0
            have hmono := congrFun (hcolors (Sum.inl a) (Sum.inl b)) ⟨q, hsq⟩
            calc
              C ((V.comp Q).lineMap q) =
                  C (V.lineMap (specializeLine (h (Sum.inl a)) q hsq)) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hqcomp]
              _ = C (V.lineMap (specializeLine (h (Sum.inl b)) q hsq)) := hmono
              _ = C (V.lineMap (specializeLine (h (Sum.inl b)) r hsr)) := by
                    apply hV
                    · exact specialize_prefix_eq _ q r hsq hsr hpre
                    · exact Or.inl (specialize_prefixMoving _ q hsq ⟨p, hp⟩)
              _ = C ((V.comp Q).lineMap r) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hrcomp]
      · obtain ⟨i, hqi, hri, hmin⟩ := htail
        cases i using Fin.cases with
        | zero =>
          have hpref := compress_prefix_eq_of_current_none h q r hpre hqi hri
          have hmov := compress_prefixMoving_of_current_none h q hqi
          rw [Subspace.lineMap_comp, Subspace.lineMap_comp]
          exact hV _ _ hpref (Or.inl hmov)
        | succ i =>
          have hq0ne := (hmin 0 (by simp)).1
          have hr0ne := (hmin 0 (by simp)).2
          cases hq0 : q.idxFun (Sum.inr 0) with
          | none => exact (hq0ne hq0).elim
          | some a =>
            cases hr0 : r.idxFun (Sum.inr 0) with
            | none => exact (hr0ne hr0).elim
            | some b =>
              have hsq : Specializable q := Or.inr (by simp [hq0])
              have hsr : Specializable r := Or.inr (by simp [hr0])
              have hqcomp := compress_lineMap_eq_specialize_inl
                (m := m) h q hsq a hq0
              have hrcomp := compress_lineMap_eq_specialize_inl
                (m := m) h r hsr b hr0
              have hmono := congrFun (hcolors (Sum.inl a) (Sum.inl b)) ⟨q, hsq⟩
              calc
                C ((V.comp Q).lineMap q) =
                    C (V.lineMap (specializeLine (h (Sum.inl a)) q hsq)) := by
                      rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hqcomp]
                _ = C (V.lineMap (specializeLine (h (Sum.inl b)) q hsq)) := hmono
                _ = C (V.lineMap (specializeLine (h (Sum.inl b)) r hsr)) := by
                      apply hV
                      · exact specialize_prefix_eq _ q r hsq hsr hpre
                      · exact Or.inr (specialize_sameFirstTail_succ _ q r hsq hsr i hqi hri hmin)
                _ = C ((V.comp Q).lineMap r) := by
                      rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hrcomp]

/-- A line moving in exactly one tail coordinate. -/
def singletonTailLine (a₀ : α) (i : Fin m) : Line α (Empty ⊕ Fin m) where
  idxFun
    | Sum.inl e => nomatch e
    | Sum.inr j => if j = i then none else some a₀
  proper := ⟨Sum.inr i, by simp⟩

/-- Moving tail coordinates of a line with empty prefix. -/
def tailMoving (q : Line α (Empty ⊕ Fin m)) : Finset (Fin m) :=
  Finset.univ.filter fun i => q.idxFun (Sum.inr i) = none

theorem tailMoving_nonempty (q : Line α (Empty ⊕ Fin m)) :
    (tailMoving q).Nonempty := by
  obtain ⟨i, hi⟩ := q.proper
  cases i with
  | inl e => exact Empty.elim e
  | inr i => exact ⟨i, by simpa [tailMoving] using hi⟩

noncomputable def firstTailMoving (q : Line α (Empty ⊕ Fin m)) : Fin m :=
  (tailMoving q).min' (tailMoving_nonempty q)

theorem firstTailMoving_mem (q : Line α (Empty ⊕ Fin m)) :
    firstTailMoving q ∈ tailMoving q :=
  Finset.min'_mem _ _

theorem firstTailMoving_idxFun (q : Line α (Empty ⊕ Fin m)) :
    q.idxFun (Sum.inr (firstTailMoving q)) = none := by
  simpa [tailMoving] using firstTailMoving_mem q

theorem firstTailMoving_min (q : Line α (Empty ⊕ Fin m)) (j : Fin m)
    (hj : j < firstTailMoving q) : q.idxFun (Sum.inr j) ≠ none := by
  intro hnone
  have hjmem : j ∈ tailMoving q := by simpa [tailMoving, hnone]
  exact (not_le_of_gt hj) (Finset.min'_le _ _ hjmem)

theorem sameFirstTail_singleton (a₀ : α) (q : Line α (Empty ⊕ Fin m)) :
    SameFirstTail q (singletonTailLine a₀ (firstTailMoving q)) := by
  refine ⟨firstTailMoving q, firstTailMoving_idxFun q, by simp [singletonTailLine], ?_⟩
  intro j hj
  exact ⟨firstTailMoving_min q j hj, by simp [singletonTailLine, ne_of_lt hj]⟩

/-- Restrict a finite parameter cube to the coordinates in `s`, using the
increasing enumeration of `s` as the new parameter order. -/
noncomputable def restrictToFinset (a₀ : α) (s : Finset (Fin M))
    {d : ℕ} (hs : s.card = d) : Subspace (Fin d) α (Empty ⊕ Fin M) where
  idxFun
    | Sum.inl e => nomatch e
    | Sum.inr i => if hi : i ∈ s then
        Sum.inr ((s.orderIsoOfFin hs).symm ⟨i, hi⟩)
      else Sum.inl a₀
  proper j := by
    let i : Fin M := s.orderEmbOfFin hs j
    have hi : i ∈ s := s.orderEmbOfFin_mem hs j
    refine ⟨Sum.inr i, ?_⟩
    change (if hi' : i ∈ s then
      Sum.inr ((s.orderIsoOfFin hs).symm ⟨i, hi'⟩) else Sum.inl a₀) = Sum.inr j
    rw [dif_pos hi]
    have hsub : (⟨i, hi⟩ : s) = s.orderIsoOfFin hs j := by
      apply Subtype.ext
      rfl
    rw [hsub, (s.orderIsoOfFin hs).symm_apply_apply]

theorem restrictToFinset_moving_mem (a₀ : α) (s : Finset (Fin M))
    {d : ℕ} (hs : s.card = d) (q : Line α (Fin d)) (i : Fin M)
    (hi : ((restrictToFinset a₀ s hs).lineMap q).idxFun (Sum.inr i) = none) :
    i ∈ s := by
  by_contra his
  simp [restrictToFinset, Subspace.lineMap, his] at hi

/-- Boolean pigeonhole in the exact form used after fusion. -/
theorem exists_bool_homogeneous_finset (d : ℕ) (f : Fin (2 * d) → Bool) :
    ∃ (s : Finset (Fin (2 * d))) (c : Bool),
      s.card = d ∧ ∀ i ∈ s, f i = c := by
  classical
  let st : Finset (Fin (2 * d)) := Finset.univ.filter fun i => f i = true
  let sf : Finset (Fin (2 * d)) := Finset.univ.filter fun i => f i ≠ true
  have hsum : st.card + sf.card = 2 * d := by
    simpa [st, sf] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * d))))
        (fun i => f i = true))
  by_cases ht : d ≤ st.card
  · obtain ⟨s, hsst, hcard⟩ := Finset.exists_subset_card_eq ht
    exact ⟨s, true, hcard, fun i hi => (Finset.mem_filter.mp (hsst hi)).2⟩
  · have hf : d ≤ sf.card := by omega
    obtain ⟨s, hssf, hcard⟩ := Finset.exists_subset_card_eq hf
    refine ⟨s, false, hcard, ?_⟩
    intro i hi
    have hne : f i ≠ true := (Finset.mem_filter.mp (hssf hi)).2
    cases h : f i <;> simp_all

/-- The finite line-color Graham--Rothschild theorem, with an arbitrary finite
ambient coordinate type. -/
theorem exists_mono_lines_fintype (α : Type) [Finite α] [Nonempty α] (d : ℕ) :
    ∃ (I : Type) (_ : Fintype I), ∀ C : Line α I → Bool,
      ∃ U : Subspace (Fin d) α I, ∃ c : Bool,
        ∀ q : Line α (Fin d), C (U.lineMap q) = c := by
  classical
  obtain ⟨I, instI, hI⟩ := exists_firstBlockCanonical α Empty (2 * d)
  refine ⟨I, instI, fun C => ?_⟩
  letI : Fintype I := instI
  obtain ⟨V, hV⟩ := hI C
  let a₀ : α := Classical.arbitrary α
  let blockColor : Fin (2 * d) → Bool := fun i =>
    C (V.lineMap (singletonTailLine a₀ i))
  obtain ⟨s, c, hs, hsc⟩ := exists_bool_homogeneous_finset d blockColor
  let Q : Subspace (Fin d) α (Empty ⊕ Fin (2 * d)) := restrictToFinset a₀ s hs
  refine ⟨V.comp Q, c, ?_⟩
  intro q
  let r : Line α (Empty ⊕ Fin (2 * d)) := Q.lineMap q
  let i : Fin (2 * d) := firstTailMoving r
  have hi0 : r.idxFun (Sum.inr i) = none := firstTailMoving_idxFun r
  have his : i ∈ s := restrictToFinset_moving_mem a₀ s hs q i hi0
  have hcanon : C (V.lineMap r) = C (V.lineMap (singletonTailLine a₀ i)) := by
    apply hV
    · intro e
      exact Empty.elim e
    · exact Or.inr (sameFirstTail_singleton a₀ r)
  calc
    C ((V.comp Q).lineMap q) = C (V.lineMap r) := by
      rw [Subspace.lineMap_comp]
    _ = C (V.lineMap (singletonTailLine a₀ i)) := hcanon
    _ = blockColor i := rfl
    _ = c := hsc i his

/-- Reindex the coordinates of a line. -/
def lineReindex (e : I ≃ J) (q : Line α I) : Line α J where
  idxFun j := q.idxFun (e.symm j)
  proper := by
    obtain ⟨i, hi⟩ := q.proper
    exact ⟨e i, by simpa⟩

@[simp] theorem reindex_lineMap {η α I J : Type*}
    (e : I ≃ J) (U : Subspace η α I) (q : Line α η) :
    (U.reindex (Equiv.refl _) (Equiv.refl _) e).lineMap q =
      lineReindex e (U.lineMap q) := by
  apply Line.ext
  funext j
  cases h : U.idxFun (e.symm j) <;>
    simp [Subspace.reindex, Subspace.lineMap, lineReindex, h]

/-- Fin-indexed form of finite Graham--Rothschild for line colorings. -/
theorem exists_mono_lines_fin (α : Type) [Finite α] [Nonempty α] (d : ℕ) :
    ∃ n : ℕ, ∀ C : Line α (Fin n) → Bool,
      ∃ U : Subspace (Fin d) α (Fin n), ∃ c : Bool,
        ∀ q : Line α (Fin d), C (U.lineMap q) = c := by
  classical
  obtain ⟨I, instI, hI⟩ := exists_mono_lines_fintype α d
  letI : Fintype I := instI
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, fun C => ?_⟩
  let D : Line α I → Bool := fun q => C (lineReindex e q)
  obtain ⟨U, c, hU⟩ := hI D
  refine ⟨U.reindex (Equiv.refl _) (Equiv.refl _) e, c, ?_⟩
  intro q
  rw [reindex_lineMap]
  exact hU q

/-- Embed the first `n` coordinates as an `n`-dimensional subspace of a
larger cube, fixing all remaining coordinates. -/
def initialSubspace (a₀ : α) {n N : ℕ} (h : n ≤ N) :
    Subspace (Fin n) α (Fin N) where
  idxFun i := if hi : i.val < n then Sum.inr ⟨i.val, hi⟩ else Sum.inl a₀
  proper j := by
    let i : Fin N := ⟨j.val, j.isLt.trans_le h⟩
    refine ⟨i, ?_⟩
    change (if hi : i.val < n then Sum.inr ⟨i.val, hi⟩ else Sum.inl a₀) = Sum.inr j
    rw [dif_pos j.isLt]

/-- Threshold form: every sufficiently high finite cube has the line-color
Graham--Rothschild property. -/
theorem exists_mono_lines_fin_of_ge (α : Type) [Finite α] [Nonempty α] (d : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ C : Line α (Fin n) → Bool,
      ∃ U : Subspace (Fin d) α (Fin n), ∃ c : Bool,
        ∀ q : Line α (Fin d), C (U.lineMap q) = c := by
  classical
  obtain ⟨N, hN⟩ := exists_mono_lines_fin α d
  refine ⟨N, ?_⟩
  intro n hn C
  let a₀ : α := Classical.arbitrary α
  let E : Subspace (Fin N) α (Fin n) := initialSubspace a₀ hn
  let D : Line α (Fin N) → Bool := fun q => C (E.lineMap q)
  obtain ⟨U, c, hU⟩ := hN D
  refine ⟨E.comp U, c, ?_⟩
  intro q
  rw [Subspace.lineMap_comp]
  exact hU q

/-- Set-coloring formulation matching Proposition 2 of
Dodos--Kanellopoulos--Tyros: inside every sufficiently high cube, every family
of lines has a finite-dimensional subspace whose lines all belong to the family
or all avoid it. -/
theorem exists_subspace_lines_subset_or_disjoint
    (α : Type) [Finite α] [Nonempty α] (d : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ ℒ : Set (Line α (Fin n)),
      ∃ U : Subspace (Fin d) α (Fin n),
        (∀ q : Line α (Fin d), U.lineMap q ∈ ℒ) ∨
          (∀ q : Line α (Fin d), U.lineMap q ∉ ℒ) := by
  classical
  obtain ⟨N, hN⟩ := exists_mono_lines_fin_of_ge α d
  refine ⟨N, ?_⟩
  intro n hn ℒ
  let C : Line α (Fin n) → Bool := fun q => decide (q ∈ ℒ)
  obtain ⟨U, c, hU⟩ := hN n hn C
  refine ⟨U, ?_⟩
  cases c with
  | false =>
      right
      intro q hq
      have hc := hU q
      simp [C, hq] at hc
  | true =>
      left
      intro q
      have hc := hU q
      simpa [C] using hc

end GrahamRothschild

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/Correlation.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Correlated sections and many restricted lines

This file formalizes Lemmas 7 and 8 in the Dodos--Kanellopoulos--Tyros
density-increment proof.  The key convention is that the constants are chosen
at a fixed density floor `δ₀`, while `ρ` denotes the actual density of the set
under consideration and may be larger than `δ₀`.

The first part is a purely finite averaging argument.  It says that if the
average density of a family of fibres is close to `ρ`, no fibre has a density
increment, and the average fraction of restricted internal lines is at least
`θ`, then one fibre is simultaneously dense and line-rich.  The second part
connects this statement with combinatorial subspaces and correlated tail
sections.
-/

open scoped BigOperators



/-! ## Pure finite averaging (DKT Lemma 8) -/

/-- The strict superlevel set of a real-valued function on a finite type. -/
noncomputable def strictSuperlevel {X : Type*} [Fintype X]
    (f : X → ℝ) (c : ℝ) : Finset X :=
  Finset.univ.filter fun x ↦ c < f x

@[simp] theorem mem_strictSuperlevel {X : Type*} [Fintype X]
    (f : X → ℝ) (c : ℝ) (x : X) :
    x ∈ strictSuperlevel f c ↔ c < f x := by
  simp [strictSuperlevel]

/-- The numerical averaging core of DKT Lemma 8.

The function `f` is the density of a fixed-tail extension and `g` is the
fraction of restricted internal lines contained in the set.  The upper bound
on `f` is exactly the negation of the density-increment alternative. -/
theorem exists_dense_and_lineRich_of_averages
    {X : Type*} [Fintype X] [Nonempty X]
    (f g : X → ℝ) (ρ η θ : ℝ)
    (hη : 0 < η) (hθ : 0 < θ) (hηθ : η < θ / 2)
    (hfavg : ρ - η ^ 2 / 2 ≤ average f)
    (hfupper : ∀ x, f x ≤ ρ + η ^ 2 / 2)
    (hgavg : θ ≤ average g)
    (hgupper : ∀ x, g x ≤ 1) :
    ∃ x, ρ - 2 * η < f x ∧ θ / 2 < g x := by
  classical
  let H₁ : Finset X := strictSuperlevel f (ρ - 2 * η)
  let H₂ : Finset X := strictSuperlevel g (θ / 2)
  have hH₁ : 1 - η < density H₁ := by
    by_contra hnot
    have hH₁le : density H₁ ≤ 1 - η := le_of_not_gt hnot
    have hfavgUpper :
        average f ≤ density H₁ * (ρ + η ^ 2 / 2) +
          (1 - density H₁) * (ρ - 2 * η) := by
      apply average_le_density_mul_add H₁ f
      · intro x _
        exact hfupper x
      · intro x hx
        exact le_of_not_gt (by simpa [H₁] using hx)
    have hweighted :
        density H₁ * (ρ + η ^ 2 / 2) +
            (1 - density H₁) * (ρ - 2 * η) ≤
          (1 - η) * (ρ + η ^ 2 / 2) + η * (ρ - 2 * η) := by
      have hH₁nonneg := density_nonneg H₁
      nlinarith [sq_nonneg η]
    have hscalar := IncrementArithmetic.bad_fiber_average_lt (δ := ρ) hη
    have havglt : average f < ρ - η ^ 2 / 2 := by
      calc
        average f ≤ density H₁ * (ρ + η ^ 2 / 2) +
            (1 - density H₁) * (ρ - 2 * η) := hfavgUpper
        _ ≤ (1 - η) * (ρ + η ^ 2 / 2) +
            η * (ρ - 2 * η) := hweighted
        _ = η * (ρ - 2 * η) +
            (1 - η) * (ρ + η ^ 2 / 2) := by ring
        _ < ρ - η ^ 2 / 2 := hscalar
    exact (not_lt_of_ge hfavg) havglt
  have hθone : θ ≤ 1 := by
    exact hgavg.trans (average_le_const hgupper)
  have hH₂ : θ / 2 < density H₂ := by
    by_contra hnot
    have hH₂le : density H₂ ≤ θ / 2 := le_of_not_gt hnot
    have hgavgUpper :
        average g ≤ density H₂ * 1 +
          (1 - density H₂) * (θ / 2) := by
      apply average_le_density_mul_add H₂ g
      · intro x _
        exact hgupper x
      · intro x hx
        exact le_of_not_gt (by simpa [H₂] using hx)
    have hweighted :
        density H₂ * 1 + (1 - density H₂) * (θ / 2) ≤
          θ / 2 + (1 - θ / 2) * (θ / 2) := by
      have hH₂nonneg := density_nonneg H₂
      nlinarith
    have hscalar := IncrementArithmetic.line_rich_average_lt hθ
    have havglt : average g < θ := by
      calc
        average g ≤ density H₂ * 1 +
            (1 - density H₂) * (θ / 2) := hgavgUpper
        _ ≤ θ / 2 + (1 - θ / 2) * (θ / 2) := hweighted
        _ < θ := hscalar
    exact (not_lt_of_ge hgavg) havglt
  have hinterPos : 0 < density (H₁ ∩ H₂) := by
    have hinter := density_add_sub_one_le_density_inter H₁ H₂
    have hsum : 0 < density H₁ + density H₂ - 1 := by
      nlinarith
    exact hsum.trans_le hinter
  obtain ⟨x, hx⟩ := (density_pos (H₁ ∩ H₂)).1 hinterPos
  have hx₁ : x ∈ H₁ := (Finset.mem_inter.1 hx).1
  have hx₂ : x ∈ H₂ := (Finset.mem_inter.1 hx).2
  exact ⟨x, (mem_strictSuperlevel f _ x).1 hx₁,
    (mem_strictSuperlevel g _ x).1 hx₂⟩

/-! ## Restricted internal lines and tail sections -/

/-- Restricted parameter lines all of whose old-alphabet points map into
`A`.  The ambient subspace uses the enlarged alphabet `Fin (k+1)`, while the
line itself and its parameters use only `Fin k`. -/
noncomputable def restrictedInternalLines {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1))) :
    Finset (Combinatorics.Line (Fin k) η) := by
  classical
  exact Finset.univ.filter fun l ↦
    ∀ a : Fin k, U (liftWord (l a)) ∈ A

@[simp] theorem mem_restrictedInternalLines {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1)))
    (l : Combinatorics.Line (Fin k) η) :
    l ∈ restrictedInternalLines U A ↔
      ∀ a : Fin k, U (liftWord (l a)) ∈ A := by
  simp [restrictedInternalLines]

/-- Fraction of the restricted internal lines of `U` that are wholly
contained in `A`. -/
noncomputable def restrictedInternalLineFraction {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1))) : ℝ :=
  density (restrictedInternalLines U A)

theorem restrictedInternalLineFraction_nonneg {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1))) :
    0 ≤ restrictedInternalLineFraction U A :=
  density_nonneg _

theorem restrictedInternalLineFraction_le_one {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1))) :
    restrictedInternalLineFraction U A ≤ 1 :=
  density_le_one _

/-- Tails for which the section at a fixed parameter word belongs to `A`. -/
noncomputable def sectionTails {η ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (x : η → Fin (k + 1)) : Finset (κ → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun y ↦
    Combinatorics.Subspace.sumWord (U x) y ∈ A

@[simp] theorem mem_sectionTails {η ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (x : η → Fin (k + 1)) (y : κ → Fin (k + 1)) :
    y ∈ sectionTails U A x ↔
      Combinatorics.Subspace.sumWord (U x) y ∈ A := by
  simp [sectionTails]

@[simp] theorem sectionTails_comp {η ζ ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (V : Combinatorics.Subspace ζ (Fin (k + 1)) η)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (x : ζ → Fin (k + 1)) :
    sectionTails (U.comp V) A x = sectionTails U A (V x) := by
  ext y
  simp [Combinatorics.Subspace.comp_apply]

/-- Tails on which all old-alphabet points of a fixed restricted parameter
line belong to `A`.  This is the finite section intersection appearing in
DKT Lemma 7. -/
noncomputable def restrictedLineTails {η ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (l : Combinatorics.Line (Fin k) η) :
    Finset (κ → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun y ↦
    ∀ a : Fin k,
      Combinatorics.Subspace.sumWord (U (liftWord (l a))) y ∈ A

@[simp] theorem mem_restrictedLineTails {η ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (l : Combinatorics.Line (Fin k) η)
    (y : κ → Fin (k + 1)) :
    y ∈ restrictedLineTails U A l ↔
      ∀ a : Fin k,
        Combinatorics.Subspace.sumWord (U (liftWord (l a))) y ∈ A := by
  simp [restrictedLineTails]

/-- Old-alphabet parameter words whose images under a large-alphabet
subspace belong to `A`. -/
noncomputable def restrictedPullbackFinset {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1))) : Finset (η → Fin k) := by
  classical
  exact Finset.univ.filter fun x ↦ U (liftWord x) ∈ A

@[simp] theorem mem_restrictedPullbackFinset {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1))) (x : η → Fin k) :
    x ∈ restrictedPullbackFinset U A ↔ U (liftWord x) ∈ A := by
  simp [restrictedPullbackFinset]

/-- Fubini identity for point sections: averaging the densities of the
fixed-tail extensions is the same as averaging the densities of the tail
sections at parameter words. -/
theorem average_extensionDensity_eq_average_sectionTails
    {η ι κ : Type*} {k : ℕ}
    [Fintype η] [DecidableEq η] [Fintype κ] [DecidableEq κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) :
    average (fun y : κ → Fin (k + 1) ↦
        subspaceDensityFinset (U.extendRightWord y) A) =
      average (fun x : η → Fin (k + 1) ↦ density (sectionTails U A x)) := by
  rw [← density_extensionPullback_eq_average,
    density_eq_average_columnFiber]
  apply congrArg average
  funext x
  congr 1
  ext y
  simp

/-- Fubini identity for restricted lines: the average line fraction on a
fixed-tail extension equals the average density of the correlated tail
intersections, one for each restricted parameter line. -/
theorem average_restrictedLineFraction_eq_average_restrictedLineTails
    {η ι κ : Type*} {k : ℕ}
    [Fintype η] [Fintype κ] [DecidableEq κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) :
    average (fun y : κ → Fin (k + 1) ↦
        restrictedInternalLineFraction (U.extendRightWord y) A) =
      average (fun l : Combinatorics.Line (Fin k) η ↦
        density (restrictedLineTails U A l)) := by
  let R : Combinatorics.Line (Fin k) η → (κ → Fin (k + 1)) → Prop :=
    fun l y ↦ ∀ a : Fin k,
      Combinatorics.Subspace.sumWord (U (liftWord (l a))) y ∈ A
  have hfubini := average_setDensity_relationRow_eq_relationColumn R
  have hrow (l : Combinatorics.Line (Fin k) η) :
      setFinset (relationRow R l) = restrictedLineTails U A l := by
    ext y
    simp [R, relationRow]
  have hcolumn (y : κ → Fin (k + 1)) :
      setFinset (relationColumn R y) =
        restrictedInternalLines (U.extendRightWord y) A := by
    ext l
    simp [R, relationColumn,
      Combinatorics.Subspace.extendRightWord_apply]
  simpa only [setDensity, restrictedInternalLineFraction, hrow, hcolumn] using
    hfubini.symm

/-- Fubini identity for the old-alphabet pullbacks of fixed-tail extensions. -/
theorem average_restrictedPullbackDensity_eq_average_sectionTails
    {η ι κ : Type*} {k : ℕ}
    [Fintype η] [DecidableEq η] [Fintype κ] [DecidableEq κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) :
    average (fun y : κ → Fin (k + 1) ↦
        density (restrictedPullbackFinset (U.extendRightWord y) A)) =
      average (fun x : η → Fin k ↦ density (sectionTails U A (liftWord x))) := by
  let R : (η → Fin k) → (κ → Fin (k + 1)) → Prop :=
    fun x y ↦ Combinatorics.Subspace.sumWord (U (liftWord x)) y ∈ A
  have hfubini := average_setDensity_relationRow_eq_relationColumn R
  have hrow (x : η → Fin k) :
      setFinset (relationRow R x) = sectionTails U A (liftWord x) := by
    ext y
    simp [R, relationRow]
  have hcolumn (y : κ → Fin (k + 1)) :
      setFinset (relationColumn R y) =
        restrictedPullbackFinset (U.extendRightWord y) A := by
    ext x
    simp [R, relationColumn,
      Combinatorics.Subspace.extendRightWord_apply]
  simpa only [setDensity, hrow, hcolumn] using hfubini.symm

/-- The pigeonhole step at the heart of DKT Lemma 7.  If every old-alphabet
point section has density at least `δ₀/2`, and density Hales--Jewett is known
at density `δ₀/4` in this parameter cube, then one restricted line has a tail
intersection of density at least `theta δ₀ q`, where `q` is the exact number
of line templates. -/
theorem exists_correlated_restricted_line
    {η ι κ : Type*} {k : ℕ}
    [Fintype η] [DecidableEq η] [Nonempty η]
    [Fintype κ] [DecidableEq κ] [Nonempty (Fin k)]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hsection : ∀ x : η → Fin k,
      δ₀ / 2 ≤ density (sectionTails U A (liftWord x)))
    (hDHJ : ∀ B : Finset (η → Fin k),
      δ₀ / 4 ≤ density B →
        ∃ l : Combinatorics.Line (Fin k) η, ∀ a, l a ∈ B) :
    ∃ l : Combinatorics.Line (Fin k) η,
      IncrementArithmetic.theta δ₀
          (Fintype.card (Combinatorics.Line (Fin k) η)) ≤
        density (restrictedLineTails U A l) := by
  classical
  let f : (κ → Fin (k + 1)) → ℝ := fun y ↦
    density (restrictedPullbackFinset (U.extendRightWord y) A)
  let D : Finset (κ → Fin (k + 1)) := superlevel f (δ₀ / 4)
  have hfavg : δ₀ / 2 ≤ average f := by
    rw [average_restrictedPullbackDensity_eq_average_sectionTails]
    exact const_le_average hsection
  have hD : δ₀ / 4 ≤ density D := by
    have hhalf := half_le_density_superlevel f
      (δ := δ₀ / 2) (by positivity) hfavg
      (fun y ↦ density_le_one _)
    have hthreshold : (δ₀ / 2) / 2 = δ₀ / 4 := by ring
    simpa only [hthreshold, D] using hhalf
  let chosen : (κ → Fin (k + 1)) → Combinatorics.Line (Fin k) η :=
    fun y ↦ if hy : y ∈ D then
      Classical.choose (hDHJ (restrictedPullbackFinset (U.extendRightWord y) A)
        ((mem_superlevel f (δ₀ / 4) y).1 (by simpa [D] using hy)))
    else default
  have hchosen (y : κ → Fin (k + 1)) (hy : y ∈ D) :
      ∀ a, chosen y a ∈ restrictedPullbackFinset (U.extendRightWord y) A := by
    dsimp [chosen]
    rw [dif_pos hy]
    exact Classical.choose_spec
      (hDHJ (restrictedPullbackFinset (U.extendRightWord y) A)
        ((mem_superlevel f (δ₀ / 4) y).1 (by simpa [D] using hy)))
  obtain ⟨l, hl⟩ := exists_dense_colorClass D chosen
  refine ⟨l, ?_⟩
  have hclassSubset : colorClass D chosen l ⊆ restrictedLineTails U A l := by
    intro y hy
    have hy' := (mem_colorClass D chosen l y).1 hy
    apply (mem_restrictedLineTails U A l y).2
    intro a
    have hmem := (mem_restrictedPullbackFinset
      (U.extendRightWord y) A (chosen y a)).1 (hchosen y hy'.1 a)
    simpa [Combinatorics.Subspace.extendRightWord_apply, hy'.2] using hmem
  have hmono : density (colorClass D chosen l) ≤
      density (restrictedLineTails U A l) := density_mono hclassSubset
  have hcardpos : (0 : ℝ) <
      Fintype.card (Combinatorics.Line (Fin k) η) := by positivity
  have hdiv : (δ₀ / 4) /
        Fintype.card (Combinatorics.Line (Fin k) η) ≤
      density D / Fintype.card (Combinatorics.Line (Fin k) η) := by
    exact div_le_div_of_nonneg_right hD hcardpos.le
  unfold IncrementArithmetic.theta
  calc
    δ₀ / (4 * Fintype.card (Combinatorics.Line (Fin k) η)) =
        (δ₀ / 4) / Fintype.card (Combinatorics.Line (Fin k) η) := by ring
    _ ≤ density D / Fintype.card (Combinatorics.Line (Fin k) η) := hdiv
    _ ≤ density (colorClass D chosen l) := hl
    _ ≤ density (restrictedLineTails U A l) := hmono

/-- Restricted correlated-tail sets are natural under composition with the
lift of an old-alphabet subspace. -/
@[simp] theorem restrictedLineTails_comp_finLift
    {η ζ ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (V : Combinatorics.Subspace ζ (Fin k) η)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (l : Combinatorics.Line (Fin k) ζ) :
    restrictedLineTails (U.comp V.finLift) A l =
      restrictedLineTails U A (V.lineMap l) := by
  ext y
  simp [Combinatorics.Subspace.comp_apply,
    Combinatorics.Subspace.lineMap_apply]

/-! ## Correlated restricted lines (DKT Lemma 7) -/

/-- DKT Lemma 7, starting from a prefix subspace whose point sections have
already been uniformized.  The constants `η₀` and `theta` are selected at the
fixed density floor `δ₀`, while the section bound tracks the actual density
`ρ ≥ δ₀`.

The proof colors a restricted line good when its common tail section has
density at least `theta`.  Finite Graham--Rothschild gives an `m`-subspace on
which all lines have one color.  The all-bad color is excluded by applying the
assumed density-Hales--Jewett statement in an `m₀`-face, then pigeonholing the
line supplied on each dense tail. -/
theorem exists_correlated_subspace_of_uniform_sections
    (k m₀ m : ℕ) (hk : 0 < k) (hm₀ : 0 < m₀) (hm₀m : m₀ ≤ m)
    (δ₀ η₀ : ℝ) (hδ₀ : 0 < δ₀) (herror : η₀ ^ 2 / 2 ≤ δ₀ / 2)
    (hDHJ : ∀ B : Finset (Word k m₀),
      δ₀ / 4 ≤ density B → ContainsLine (B : Set (Word k m₀))) :
    ∃ N : ℕ, ∀ {ι κ : Type*} [Fintype κ] [DecidableEq κ], ∀ r ≥ N,
      ∀ (U : Combinatorics.Subspace (Fin r) (Fin (k + 1)) ι)
        (A : Finset (ι ⊕ κ → Fin (k + 1))) (ρ : ℝ),
        δ₀ ≤ ρ →
        (∀ x : Word (k + 1) r,
          ρ - η₀ ^ 2 / 2 ≤ density (sectionTails U A x)) →
        ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
          (∀ x : Word (k + 1) m,
            ρ - η₀ ^ 2 / 2 ≤ density (sectionTails V A x)) ∧
          ∀ l : Combinatorics.Line (Fin k) (Fin m),
            IncrementArithmetic.theta δ₀
                (Fintype.card (Combinatorics.Line (Fin k) (Fin m₀))) ≤
              density (restrictedLineTails V A l) := by
  classical
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  letI : Inhabited (Fin k) := ⟨⟨0, hk⟩⟩
  letI : Nonempty (Fin m₀) := Fin.pos_iff_nonempty.mp hm₀
  obtain ⟨N, hN⟩ :=
    GrahamRothschild.exists_subspace_lines_subset_or_disjoint (Fin k) m
  refine ⟨N, ?_⟩
  intro ι κ _ _
  intro r hr U A ρ hρ hsection
  let θ : ℝ := IncrementArithmetic.theta δ₀
    (Fintype.card (Combinatorics.Line (Fin k) (Fin m₀)))
  let good : Set (Combinatorics.Line (Fin k) (Fin r)) :=
    {l | θ ≤ density (restrictedLineTails U A l)}
  obtain ⟨Y, hYgood | hYbad⟩ := hN r hr good
  · let V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι :=
      U.comp Y.finLift
    refine ⟨V, ?_, ?_⟩
    · intro x
      change ρ - η₀ ^ 2 / 2 ≤
        density (sectionTails (U.comp Y.finLift) A x)
      rw [sectionTails_comp]
      exact hsection (Y.finLift x)
    · intro l
      have hgood := hYgood l
      change θ ≤ density (restrictedLineTails U A (Y.lineMap l)) at hgood
      simpa [V, θ] using hgood
  · exfalso
    let F : Combinatorics.Subspace (Fin m₀) (Fin k) (Fin m) :=
      Combinatorics.Subspace.coordinateFace hm₀m
    let Zold : Combinatorics.Subspace (Fin m₀) (Fin k) (Fin r) := Y.comp F
    let Z : Combinatorics.Subspace (Fin m₀) (Fin (k + 1)) ι :=
      U.comp Zold.finLift
    have hbase : δ₀ / 2 ≤ ρ - η₀ ^ 2 / 2 := by linarith
    have hZsection : ∀ x : Word k m₀,
        δ₀ / 2 ≤ density (sectionTails Z A (liftWord x)) := by
      intro x
      apply hbase.trans
      change ρ - η₀ ^ 2 / 2 ≤
        density (sectionTails (U.comp Zold.finLift) A (liftWord x))
      rw [sectionTails_comp]
      exact hsection (Zold.finLift (liftWord x))
    have hDHJ' : ∀ B : Finset (Word k m₀),
        δ₀ / 4 ≤ density B →
          ∃ l : Combinatorics.Line (Fin k) (Fin m₀), ∀ a, l a ∈ B := by
      intro B hB
      exact (containsLine_coe_finset_iff.mp (hDHJ B hB))
    have hcorr : ∃ l : Combinatorics.Line (Fin k) (Fin m₀),
        IncrementArithmetic.theta δ₀
            (Fintype.card (Combinatorics.Line (Fin k) (Fin m₀))) ≤
          density (restrictedLineTails Z A l) := by
      apply exists_correlated_restricted_line
      · exact hδ₀
      · exact hZsection
      · exact hDHJ'
    obtain ⟨l, hl⟩ := hcorr
    have hl' : θ ≤ density
        (restrictedLineTails U A (Y.lineMap (F.lineMap l))) := by
      change θ ≤ density (restrictedLineTails (U.comp Zold.finLift) A l) at hl
      rw [restrictedLineTails_comp_finLift] at hl
      change θ ≤ density (restrictedLineTails U A (Zold.lineMap l)) at hl
      rw [show Zold = Y.comp F from rfl,
        Combinatorics.Subspace.lineMap_comp] at hl
      exact hl
    have hbad := hYbad (F.lineMap l)
    change ¬θ ≤ density
      (restrictedLineTails U A (Y.lineMap (F.lineMap l))) at hbad
    exact hbad hl'

/-! ## Many restricted lines from correlated sections -/

/-- DKT Lemma 8 for a fixed subspace of prefixes.  Point-section density and
restricted-line correlation are hypotheses; the conclusion supplies one fixed
tail on which both the density and the restricted-line fraction are large,
provided no such extension already gives the prescribed increment. -/
theorem exists_dense_extension_with_many_restricted_lines
    {η ι κ : Type*} {k : ℕ}
    [Fintype η] [DecidableEq η] [Nonempty η]
    [Fintype κ] [DecidableEq κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (ρ η₀ θ : ℝ)
    (hη₀ : 0 < η₀) (hθ : 0 < θ) (hηθ : η₀ < θ / 2)
    (hsection : ∀ x : η → Fin (k + 1),
      ρ - η₀ ^ 2 / 2 ≤ density (sectionTails U A x))
    (hupper : ∀ y : κ → Fin (k + 1),
      subspaceDensityFinset (U.extendRightWord y) A ≤
        ρ + η₀ ^ 2 / 2)
    (hcorrelation : ∀ l : Combinatorics.Line (Fin k) η,
      θ ≤ density (restrictedLineTails U A l)) :
    ∃ y : κ → Fin (k + 1),
      ρ - 2 * η₀ < subspaceDensityFinset (U.extendRightWord y) A ∧
        θ / 2 < restrictedInternalLineFraction (U.extendRightWord y) A := by
  let f : (κ → Fin (k + 1)) → ℝ := fun y ↦
    subspaceDensityFinset (U.extendRightWord y) A
  let g : (κ → Fin (k + 1)) → ℝ := fun y ↦
    restrictedInternalLineFraction (U.extendRightWord y) A
  have hfavg : ρ - η₀ ^ 2 / 2 ≤ average f := by
    rw [average_extensionDensity_eq_average_sectionTails]
    exact const_le_average hsection
  have hgavg : θ ≤ average g := by
    rw [average_restrictedLineFraction_eq_average_restrictedLineTails]
    exact const_le_average hcorrelation
  exact exists_dense_and_lineRich_of_averages f g ρ η₀ θ hη₀ hθ hηθ
    hfavg hupper hgavg fun y ↦ restrictedInternalLineFraction_le_one _ _

/-- The disjunctive form of DKT Lemma 8 used by the density-increment
iteration.  The first branch is a genuine density increment on an arbitrary
`η`-dimensional subspace.  If it fails, every fixed-tail extension of `U` has
the upper bound needed by the finite averaging lemma, yielding the second
branch.

The parameters `η₀` and `θ` are normally selected using a fixed lower density
`δ₀`; the density `ρ` in this statement is the actual density and is not
silently replaced by `δ₀`. -/
theorem density_increment_or_many_restricted_lines
    {η ι κ : Type*} {k : ℕ}
    [Fintype η] [DecidableEq η] [Nonempty η]
    [Fintype κ] [DecidableEq κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (ρ η₀ θ : ℝ)
    (hη₀ : 0 < η₀) (hθ : 0 < θ) (hηθ : η₀ < θ / 2)
    (hsection : ∀ x : η → Fin (k + 1),
      ρ - η₀ ^ 2 / 2 ≤ density (sectionTails U A x))
    (hcorrelation : ∀ l : Combinatorics.Line (Fin k) η,
      θ ≤ density (restrictedLineTails U A l)) :
    (∃ W : Combinatorics.Subspace η (Fin (k + 1)) (ι ⊕ κ),
        ρ + η₀ ^ 2 / 2 < subspaceDensityFinset W A) ∨
      ∃ W : Combinatorics.Subspace η (Fin (k + 1)) (ι ⊕ κ),
        ρ - 2 * η₀ < subspaceDensityFinset W A ∧
          θ / 2 < restrictedInternalLineFraction W A := by
  classical
  by_cases hinc : ∃ W : Combinatorics.Subspace η (Fin (k + 1)) (ι ⊕ κ),
      ρ + η₀ ^ 2 / 2 < subspaceDensityFinset W A
  · exact Or.inl hinc
  · right
    push Not at hinc
    obtain ⟨y, hyDensity, hyLines⟩ :=
      exists_dense_extension_with_many_restricted_lines U A ρ η₀ θ
        hη₀ hθ hηθ hsection
        (fun y ↦ hinc (U.extendRightWord y)) hcorrelation
    exact ⟨U.extendRightWord y, hyDensity, hyLines⟩

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/UniformFibres.lean` -/

section
/-!
# Uniform fibres by a finite energy-increment argument

This file proves the elementary uniform-fibres lemma used in the Dodos--
Kanellopoulos--Tyros proof of density Hales--Jewett.  The exact argument is
carried out with Mathlib's rational `Finset.dens`; a wrapper supplies real
inequalities for the rest of the development.
-/



open scoped BigOperators

abbrev BlockTower.{u} (X Y : Type u) : Nat → Type u
  | 0 => Y
  | n + 1 => X × BlockTower X Y n

namespace BlockTower

variable {X Y : Type u} [Fintype X] [Fintype Y]

noncomputable instance instFintype : ∀ r, Fintype (BlockTower X Y r)
  | 0 => inferInstanceAs (Fintype Y)
  | n + 1 => @instFintypeProd X (BlockTower X Y n) inferInstance (instFintype n)

noncomputable def fibre {r : ℕ} (A : Finset (BlockTower X Y (r + 1))) (x : X) :
    Finset (BlockTower X Y r) := by
  classical exact Finset.univ.filter (fun z ↦ (x, z) ∈ A)

@[simp] theorem mem_fibre {r : ℕ} (A : Finset (BlockTower X Y (r + 1)))
    (x : X) (z : BlockTower X Y r) : z ∈ fibre A x ↔ (x, z) ∈ A := by
  classical simp [fibre]

theorem card_eq_sum_card_fibre {r : ℕ} (A : Finset (BlockTower X Y (r + 1))) :
    A.card = ∑ x : X, (fibre A x).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (s := A) (t := Finset.univ)
    (f := fun z ↦ z.1) (by simp)]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.card_bij (fun z hz ↦ z.2)
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzA, hzx⟩
    simpa [fibre, ← hzx] using hzA
  · intro a ha b hb hab
    apply Prod.ext
    · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    · exact hab
  · intro z hz
    exact ⟨(x, z), by simpa [fibre] using hz, rfl⟩

theorem dens_eq_average_fibre [Nonempty X] {r : ℕ}
    (A : Finset (BlockTower X Y (r + 1))) :
    (A.dens : ℚ) = (∑ x : X, ((fibre A x).dens : ℚ)) / Fintype.card X := by
  rw [Finset.dens, card_eq_sum_card_fibre]
  simp only [Nat.cast_sum, Finset.dens, Nat.cast_mul, Fintype.card_prod]
  push_cast
  simp [div_eq_mul_inv, Finset.sum_mul, mul_assoc]

/-- Split a word at a block boundary. -/
def wordAddEquiv (t m n : ℕ) :
    Word t (m + n) ≃ Word t m × Word t n :=
  (Equiv.piCongrLeft (fun _ : Fin (m + n) ↦ Fin t) finSumFinEquiv).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) (Fin t))

/-- Flatten an iterated tower of `m`-letter blocks followed by an `s`-letter
suffix into an ordinary word. -/
def wordEquiv (t m s : ℕ) : ∀ r : ℕ,
    BlockTower (Word t m) (Word t s) r ≃ Word t (r * m + s)
  | 0 => by simpa using Equiv.refl (Word t s)
  | r + 1 =>
      ((Equiv.refl (Word t m)).prodCongr (wordEquiv t m s r)).trans <|
        (wordAddEquiv t m (r * m + s)).symm.trans <|
          Equiv.piCongrLeft (fun _ : Fin ((r + 1) * m + s) ↦ Fin t) <|
            finCongr (by simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm])

@[simp] theorem dens_map_wordEquiv (t m s r : ℕ)
    (A : Finset (BlockTower (Word t m) (Word t s) r)) :
    (A.map (wordEquiv t m s r).toEmbedding).dens = A.dens := by
  exact Finset.dens_map_equiv _

end BlockTower

namespace UniformFibres

open BlockTower

variable {X : Type u} [Fintype X]

/-- If one value lies `ε` below a lower bound for the average, another value
lies at least `ε/(|X|-1)` above the average. -/
theorem exists_average_add_le [Nonempty X] (hX : 1 < Fintype.card X)
    (f : X → ℚ) (d e mu : ℚ)
    (havg : mu = (∑ x : X, f x) / Fintype.card X)
    (hd : d ≤ mu) (x : X) (hx : f x ≤ d - e) :
    ∃ y : X, mu + e / (Fintype.card X - 1) ≤ f y := by
  classical
  let q : ℚ := Fintype.card X
  let rho : ℚ := e / (q - 1)
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast hX
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  have hqm1 : q - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  have hrho : (q - 1) * rho = e := by
    dsimp [rho]
    field_simp
  have hsum : ∑ y : X, f y = q * mu := by
    rw [havg]
    field_simp
    simp [q]
  have hxin : x ∈ (Finset.univ : Finset X) := Finset.mem_univ x
  have hsplit : ∑ y : X, f y = f x + ∑ y ∈ (Finset.univ.erase x), f y := by
    calc
      ∑ y : X, f y = (∑ y ∈ (Finset.univ.erase x), f y) + f x :=
        (Finset.sum_erase_add _ _ hxin).symm
      _ = f x + ∑ y ∈ (Finset.univ.erase x), f y := add_comm _ _
  have herase : (q - 1) * (mu + rho) ≤
      ∑ y ∈ (Finset.univ.erase x), f y := by
    linarith
  have hne : (Finset.univ.erase x : Finset X).Nonempty := by
    exact (Finset.one_lt_card_iff_nontrivial.mp (by simpa using hX)).erase_nonempty
  obtain ⟨y, hy, hyf⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ : X ↦ mu + rho) (g := f) (by
      simpa [q, Finset.card_erase_of_mem hxin, Nat.cast_sub (by omega : 1 ≤ Fintype.card X),
        mul_add] using herase)
  exact ⟨y, by simpa [rho, q] using hyf⟩

variable {Y : Type u} [Fintype Y]

/-- Along some initial chain of frozen blocks there is a next block all of
whose fibres lie above the indicated threshold.  This recursive formulation
retains the unused blocks as part of the suffix. -/
def HasUniformBlock (d e : ℚ) : {r : ℕ} →
    Finset (BlockTower X Y r) → Prop
  | 0, _ => False
  | _r + 1, A =>
      (∀ x : X, d - e ≤ ((BlockTower.fibre A x).dens : ℚ)) ∨
      ∃ x : X, HasUniformBlock d e (BlockTower.fibre A x)

/-- Real-valued interface to `HasUniformBlock`, matching the density
convention used by the rest of the Erdős 171 development. -/
def HasUniformBlockReal (d e : ℝ) : {r : ℕ} →
    Finset (BlockTower X Y r) → Prop
  | 0, _ => False
  | _r + 1, A =>
      (∀ x : X, d - e ≤ ((BlockTower.fibre A x).dens : ℝ)) ∨
      ∃ x : X, HasUniformBlockReal d e (BlockTower.fibre A x)

theorem HasUniformBlock.toReal {d e : ℚ} : ∀ {r : ℕ}
    {A : Finset (BlockTower X Y r)}, HasUniformBlock d e A →
      HasUniformBlockReal (d : ℝ) (e : ℝ) A := by
  intro r
  induction r with
  | zero => simp [HasUniformBlock]
  | succ r ih =>
      intro A h
      rw [HasUniformBlock] at h
      rw [HasUniformBlockReal]
      rcases h with h | ⟨x, hx⟩
      · left
        intro x
        exact_mod_cast h x
      · exact Or.inr ⟨x, ih hx⟩

theorem HasUniformBlockReal.mono_error {d e e' : ℝ} (hee : e ≤ e') :
    ∀ {r : ℕ} {A : Finset (BlockTower X Y r)},
      HasUniformBlockReal d e A → HasUniformBlockReal d e' A := by
  intro r
  induction r with
  | zero => simp [HasUniformBlockReal]
  | succ r ih =>
      intro A h
      rw [HasUniformBlockReal] at h ⊢
      rcases h with h | ⟨x, hx⟩
      · left
        intro x
        exact (sub_le_sub_left hee d).trans (h x)
      · exact Or.inr ⟨x, ih hx⟩

/-- A record of the initial blocks frozen before the uniform block.  The two
indices are the original and remaining tower heights. -/
inductive FrozenPrefix (X : Type u) : ℕ → ℕ → Type u
  | nil (r : ℕ) : FrozenPrefix X r r
  | cons {r q : ℕ} (x : X) (p : FrozenPrefix X r q) : FrozenPrefix X (r + 1) q

namespace FrozenPrefix

/-- Insert the frozen blocks in front of a remaining tower word. -/
def prepend {X Y : Type u} : {r q : ℕ} → FrozenPrefix X r q →
    BlockTower X Y q → BlockTower X Y r
  | _, _, .nil _, z => z
  | _, _, .cons x p, z => (x, prepend p z)

theorem prepend_injective {X Y : Type u} : ∀ {r q : ℕ}
    (p : FrozenPrefix X r q), Function.Injective (prepend (Y := Y) p)
  | _, _, .nil _ => Function.injective_id
  | _, _, .cons _ p => fun _ _ h ↦ prepend_injective p (congrArg Prod.snd h)

noncomputable def iterFibre {X Y : Type u} [Fintype X] [Fintype Y] :
    {r q : ℕ} → FrozenPrefix X r q → Finset (BlockTower X Y r) →
      Finset (BlockTower X Y q)
  | _, _, .nil _, A => A
  | _, _, .cons x p, A => iterFibre p (BlockTower.fibre A x)

@[simp] theorem iterFibre_nil {X Y : Type u} [Fintype X] [Fintype Y]
    (r : ℕ) (A : Finset (BlockTower X Y r)) :
    iterFibre (.nil r : FrozenPrefix X r r) A = A := rfl

@[simp] theorem iterFibre_cons {X Y : Type u} [Fintype X] [Fintype Y]
    {r q : ℕ} (x : X) (p : FrozenPrefix X r q)
    (A : Finset (BlockTower X Y (r + 1))) :
    iterFibre (.cons x p) A = iterFibre p (BlockTower.fibre A x) := rfl

@[simp] theorem mem_iterFibre {X Y : Type u} [Fintype X] [Fintype Y] :
    ∀ {r q : ℕ} (p : FrozenPrefix X r q)
      (A : Finset (BlockTower X Y r)) (z : BlockTower X Y q),
      z ∈ p.iterFibre A ↔ prepend p z ∈ A
  | _, _, .nil _, A, z => Iff.rfl
  | _, _, .cons x p, A, z => by
      rw [iterFibre_cons, mem_iterFibre, mem_fibre]
      rfl

end FrozenPrefix

/-- Extract the concrete frozen prefix and the next uniform block from the
recursive stopping predicate. -/
theorem HasUniformBlockReal.exists_frozenPrefix {d e : ℝ} : ∀ {r : ℕ}
    {A : Finset (BlockTower X Y r)}, HasUniformBlockReal d e A →
      ∃ q : ℕ, ∃ p : FrozenPrefix X r (q + 1),
        ∀ x : X, d - e ≤
          ((BlockTower.fibre (p.iterFibre A) x).dens : ℝ) := by
  intro r
  induction r with
  | zero => simp [HasUniformBlockReal]
  | succ r ih =>
      intro A h
      rw [HasUniformBlockReal] at h
      rcases h with h | ⟨x, hx⟩
      · refine ⟨r, .nil (r + 1), ?_⟩
        intro x
        change d - e ≤ ((BlockTower.fibre A x).dens : ℝ)
        exact h x
      · obtain ⟨q, p, hp⟩ := ih hx
        refine ⟨q, .cons x p, ?_⟩
        intro y
        change d - e ≤
          ((BlockTower.fibre (p.iterFibre (BlockTower.fibre A x)) y).dens : ℝ)
        exact hp y

/-- The finite energy-increment argument.  If there are `R+1` available
blocks and `b + R * (ε/(|X|-1)) > 1`, a uniform block must occur before
the possible density increments exhaust the interval `[0,1]`. -/
theorem hasUniformBlock_of_growth [Nonempty X] (hX : 1 < Fintype.card X)
    (d b e : ℚ) (he : 0 ≤ e) (hdb : d ≤ b) : ∀ (R : ℕ)
    (A : Finset (BlockTower X Y (R + 1))),
    b ≤ (A.dens : ℚ) →
    1 < b + R * (e / (Fintype.card X - 1)) →
    HasUniformBlock d e A := by
  intro R
  induction R generalizing b with
  | zero =>
      intro A hA hcap
      exfalso
      have hle : (A.dens : ℚ) ≤ 1 := by exact_mod_cast A.dens_le_one
      norm_num at hcap
      linarith
  | succ R ih =>
      intro A hA hcap
      rw [HasUniformBlock]
      by_cases hunif : ∀ x : X, d - e ≤ ((BlockTower.fibre A x).dens : ℚ)
      · exact Or.inl hunif
      · right
        push Not at hunif
        obtain ⟨x, hx⟩ := hunif
        let mu : ℚ := (A.dens : ℚ)
        let rho : ℚ := e / (Fintype.card X - 1)
        have hrho : 0 ≤ rho := by
          dsimp [rho]
          apply div_nonneg he
          have : (1 : ℚ) < Fintype.card X := by exact_mod_cast hX
          linarith
        obtain ⟨y, hy⟩ := exists_average_add_le hX
          (fun z : X ↦ ((BlockTower.fibre A z).dens : ℚ)) d e mu
          (BlockTower.dens_eq_average_fibre A) (hdb.trans hA) x hx.le
        refine ⟨y, ih (b := b + rho) (by linarith) (BlockTower.fibre A y) ?_ ?_⟩
        · dsimp [mu, rho] at hy ⊢
          linarith
        · dsimp [rho]
          push_cast at hcap ⊢
          ring_nf at hcap ⊢
          exact hcap

/-- Qualitative form of uniformization: the number of available blocks can
be chosen from `X` and `ε` alone, independently of the terminal suffix and
of the set. -/
theorem exists_blockCount_uniform [Nonempty X] (hX : 1 < Fintype.card X)
    (e : ℚ) (he : 0 < e) :
    ∃ R : ℕ, ∀ A : Finset (BlockTower X Y (R + 1)),
      HasUniformBlock (A.dens : ℚ) e A := by
  let rho : ℚ := e / (Fintype.card X - 1)
  have hden : (0 : ℚ) < Fintype.card X - 1 := by
    have : (1 : ℚ) < Fintype.card X := by exact_mod_cast hX
    linarith
  have hrho : 0 < rho := div_pos he hden
  obtain ⟨R, hR⟩ := exists_nat_gt (1 / rho)
  have hRrho : (1 : ℚ) < R * rho := by
    apply (div_lt_iff₀ hrho).mp
    simpa [div_eq_mul_inv, mul_comm] using hR
  refine ⟨R, fun A ↦ hasUniformBlock_of_growth hX
    (A.dens : ℚ) (A.dens : ℚ) e he.le le_rfl R A le_rfl ?_⟩
  have hdens : (0 : ℚ) ≤ (A.dens : ℚ) := by positivity
  dsimp [rho] at hRrho ⊢
  linarith

/-- Real-density wrapper.  It chooses a smaller positive rational error,
runs the exact rational argument, and weakens the resulting estimate to the
requested real error. -/
theorem exists_blockCount_uniform_real [Nonempty X] (hX : 1 < Fintype.card X)
    (e : ℝ) (he : 0 < e) :
    ∃ R : ℕ, ∀ A : Finset (BlockTower X Y (R + 1)),
      HasUniformBlockReal (A.dens : ℝ) e A := by
  obtain ⟨q : ℚ, hq, hqe⟩ := exists_pos_rat_lt he
  obtain ⟨R, hR⟩ := exists_blockCount_uniform (X := X) (Y := Y) hX q hq
  refine ⟨R, fun A ↦ ?_⟩
  have hreal := (hR A).toReal
  exact hreal.mono_error hqe.le

/-- The directly consumable real-density form: after freezing some initial
blocks, every value of the next block has a suffix fibre whose density is at
least the original density minus `e`. -/
theorem exists_uniform_frozenPrefix_real [Nonempty X]
    (hX : 1 < Fintype.card X) (e : ℝ) (he : 0 < e) :
    ∃ R : ℕ, ∀ A : Finset (BlockTower X Y (R + 1)),
      ∃ q : ℕ, ∃ p : FrozenPrefix X (R + 1) (q + 1),
        ∀ x : X, (A.dens : ℝ) - e ≤
          ((BlockTower.fibre (p.iterFibre A) x).dens : ℝ) := by
  obtain ⟨R, hR⟩ := exists_blockCount_uniform_real (X := X) (Y := Y) hX e he
  exact ⟨R, fun A ↦ (hR A).exists_frozenPrefix⟩

end UniformFibres

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/RestrictedMDHJ.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Restricted multidimensional density Hales--Jewett

This file formalizes Corollary 5 of Dodos--Kanellopoulos--Tyros.  Assuming
density Hales--Jewett for the alphabet `Fin k`, every dense subset of a large
cube over `Fin (k + 1)` contains the old-alphabet face of an arbitrarily
high-dimensional combinatorial subspace.
-/




/-- The nested coordinate type corresponding to a tower of word blocks. -/
abbrev BlockCoord (M s : ℕ) : ℕ → Type
  | 0 => Fin s
  | r + 1 => Fin M ⊕ BlockCoord M s r

namespace BlockCoord

/-- Flatten the nested coordinate type of a block tower. -/
def equivFin (M s : ℕ) : ∀ r : ℕ, BlockCoord M s r ≃ Fin (r * M + s)
  | 0 => finCongr (by simp)
  | r + 1 =>
      ((Equiv.refl (Fin M)).sumCongr (equivFin M s r)).trans <|
        finSumFinEquiv.trans <| finCongr (by
          simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm])

end BlockCoord

namespace BlockTower

universe u

theorem nonempty {X Y : Type u} [Nonempty X] [Nonempty Y] :
    ∀ r : ℕ, Nonempty (BlockTower X Y r)
  | 0 => inferInstance
  | r + 1 => by
      letI : Nonempty (BlockTower X Y r) :=
        nonempty (X := X) (Y := Y) r
      infer_instance

/-- View a tower of word blocks as a word on the corresponding nested
coordinate type. -/
def functionEquiv (t M s : ℕ) : ∀ r : ℕ,
    BlockTower (Word t M) (Word t s) r ≃ (BlockCoord M s r → Fin t)
  | 0 => Equiv.refl _
  | r + 1 =>
      ((Equiv.refl (Word t M)).prodCongr (functionEquiv t M s r)).trans
        (Equiv.sumArrowEquivProdArrow (Fin M) (BlockCoord M s r) (Fin t)).symm

@[simp] theorem functionEquiv_zero_apply (t M s : ℕ) (z : Word t s) :
    functionEquiv t M s 0 z = z := rfl

@[simp] theorem functionEquiv_succ_apply (t M s r : ℕ)
    (z : Word t M) (y : BlockTower (Word t M) (Word t s) r) :
    functionEquiv t M s (r + 1) (z, y) =
      Sum.elim z (functionEquiv t M s r y) := by
  rfl

/-- A block-tower/ordinary-word equivalence factored through its explicit
coordinate equivalence. -/
def coordinateWordEquiv (t M s r : ℕ) :
    BlockTower (Word t M) (Word t s) r ≃ Word t (r * M + s) :=
  (functionEquiv t M s r).trans <|
    Equiv.piCongrLeft (fun _ : Fin (r * M + s) ↦ Fin t) (BlockCoord.equivFin M s r)

@[simp] theorem coordinateWordEquiv_apply (t M s r : ℕ)
    (z : BlockTower (Word t M) (Word t s) r) (i : Fin (r * M + s)) :
    coordinateWordEquiv t M s r z i =
      functionEquiv t M s r z ((BlockCoord.equivFin M s r).symm i) := by
  simp only [coordinateWordEquiv, Equiv.trans_apply]
  rw [Equiv.piCongrLeft_apply]
  simp

end BlockTower

/-- Prepend a fixed coordinate block without changing the parameter
directions of a subspace. -/
def fixedLeft {eta alpha iota kappa : Type*} (z : kappa → alpha)
    (U : Combinatorics.Subspace eta alpha iota) :
    Combinatorics.Subspace eta alpha (kappa ⊕ iota) where
  idxFun
    | Sum.inl i => Sum.inl (z i)
    | Sum.inr j => U.idxFun j
  proper e := by
    obtain ⟨j, hj⟩ := U.proper e
    exact ⟨Sum.inr j, hj⟩

@[simp] theorem fixedLeft_apply {eta alpha iota kappa : Type*}
    (z : kappa → alpha) (U : Combinatorics.Subspace eta alpha iota)
    (x : eta → alpha) :
    fixedLeft z U x = Sum.elim z (U x) := by
  funext i
  cases i <;> simp [fixedLeft, Combinatorics.Subspace.coe_apply]

namespace UniformFibres.FrozenPrefix

open BlockTower

/-- Realize a frozen prefix, a subspace in the next block, and a fixed
remaining suffix as a subspace in the original flattened word cube. -/
def realizeNested {t M s m q : ℕ} : ∀ {r : ℕ},
    FrozenPrefix (Word t M) r (q + 1) →
      Combinatorics.Subspace (Fin m) (Fin t) (Fin M) →
      BlockTower (Word t M) (Word t s) q →
      Combinatorics.Subspace (Fin m) (Fin t) (BlockCoord M s r)
  | _, .nil _, V, y =>
      V.extendRightWord (BlockTower.functionEquiv t M s q y)
  | _, .cons z p, V, y =>
      fixedLeft z (realizeNested p V y)

@[simp] theorem realizeNested_apply {t M s m : ℕ} : ∀ {q r : ℕ}
    (p : FrozenPrefix (Word t M) r (q + 1))
    (V : Combinatorics.Subspace (Fin m) (Fin t) (Fin M))
    (y : BlockTower (Word t M) (Word t s) q) (x : Word t m),
    realizeNested p V y x =
      BlockTower.functionEquiv t M s r (p.prepend (V x, y))
  | q, _, .nil _, V, y, x => by
      rw [show realizeNested (.nil (q + 1)) V y x =
          Sum.elim (V x) (BlockTower.functionEquiv t M s q y) by
        simp [realizeNested, Combinatorics.Subspace.extendRightWord_apply,
          Combinatorics.Subspace.sumWord]]
      exact (BlockTower.functionEquiv_succ_apply t M s q (V x) y).symm
  | q, _, .cons z p, V, y, x => by
      rw [show realizeNested (.cons z p) V y x =
          Sum.elim z (realizeNested p V y x) by
        simp [realizeNested]]
      rw [realizeNested_apply p V y x]
      exact (BlockTower.functionEquiv_succ_apply t M s _ z
        (p.prepend (V x, y))).symm

/-- Flatten `realizeNested` to an ordinary `Fin`-indexed word cube. -/
def realize {t M s m q r : ℕ}
    (p : FrozenPrefix (Word t M) r (q + 1))
    (V : Combinatorics.Subspace (Fin m) (Fin t) (Fin M))
    (y : BlockTower (Word t M) (Word t s) q) :
    Combinatorics.Subspace (Fin m) (Fin t) (Fin (r * M + s)) :=
  (realizeNested p V y).reindex (Equiv.refl _) (Equiv.refl _)
    (BlockCoord.equivFin M s r)

@[simp] theorem realize_apply {t M s m q r : ℕ}
    (p : FrozenPrefix (Word t M) r (q + 1))
    (V : Combinatorics.Subspace (Fin m) (Fin t) (Fin M))
    (y : BlockTower (Word t M) (Word t s) q) (x : Word t m) :
    realize p V y x =
      BlockTower.coordinateWordEquiv t M s r (p.prepend (V x, y)) := by
  funext i
  simp [realize,
    Combinatorics.Subspace.reindex_apply]

end UniformFibres.FrozenPrefix

/-- A set in a cube over `Fin (k + 1)` contains the restriction to the old
alphabet `Fin k` of an `m`-dimensional combinatorial subspace. -/
def ContainsRestrictedSubspace (m : ℕ) {k n : ℕ}
    (A : Set (Word (k + 1) n)) : Prop :=
  ∃ U : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
    Set.range (fun x : Word k m ↦ U (liftWord x)) ⊆ A

theorem containsRestrictedSubspace_iff (m : ℕ) {k n : ℕ}
    {A : Set (Word (k + 1) n)} :
    ContainsRestrictedSubspace m A ↔
      ∃ U : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
        ∀ x : Word k m, U (liftWord x) ∈ A := by
  constructor
  · rintro ⟨U, hU⟩
    exact ⟨U, fun x ↦ hU ⟨x, rfl⟩⟩
  · rintro ⟨U, hU⟩
    refine ⟨U, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hU x

theorem ContainsRestrictedSubspace.mono {m k n : ℕ}
    {A B : Set (Word (k + 1) n)}
    (hA : ContainsRestrictedSubspace m A) (hAB : A ⊆ B) :
    ContainsRestrictedSubspace m B := by
  obtain ⟨U, hU⟩ := hA
  exact ⟨U, hU.trans hAB⟩

/-- One-witness form of the restricted multidimensional density theorem. -/
def FiniteRestrictedMDHJ (k m : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n : ℕ, ∀ A : Finset (Word (k + 1) n),
      δ ≤ density A → ContainsRestrictedSubspace m (A : Set (Word (k + 1) n))

/-- Eventual form of the restricted multidimensional density theorem. -/
def EventualRestrictedMDHJ (k m : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ A : Finset (Word (k + 1) n),
      δ ≤ density A → ContainsRestrictedSubspace m (A : Set (Word (k + 1) n))

/-- Dodos--Kanellopoulos--Tyros, Corollary 5: density Hales--Jewett on the
old alphabet gives arbitrarily high-dimensional restricted subspaces in a
dense cube over the alphabet with one new letter. -/
theorem FiniteDensityHJ.finiteRestrictedMDHJ {k : ℕ} (h : FiniteDensityHJ k)
    (hk : 0 < k) (m : ℕ) : FiniteRestrictedMDHJ k m := by
  intro δ hδ
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  letI : Nonempty (Fin (k + 1)) := Fin.pos_iff_nonempty.mp (by omega)
  have hMD := (h.finiteDensityMDHJ hk m).eventual hk
  obtain ⟨M₀, hM₀⟩ := hMD (δ / 2) (half_pos hδ)
  let M : ℕ := max M₀ 1
  have hM₀M : M₀ ≤ M := Nat.le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _)
  have hM := hM₀ M hM₀M
  let X := Word (k + 1) M
  let Y := Word (k + 1) 0
  have hXcard : 1 < Fintype.card X := by
    rw [show Fintype.card X = (k + 1) ^ M by simp [X, Word]]
    exact one_lt_pow' (by omega) hMpos.ne'
  obtain ⟨R, hR⟩ := UniformFibres.exists_uniform_frozenPrefix_real
    (X := X) (Y := Y) hXcard (δ / 2) (half_pos hδ)
  refine ⟨(R + 1) * M + 0, ?_⟩
  intro A hA
  classical
  let e := BlockTower.coordinateWordEquiv (k + 1) M 0 (R + 1)
  let AT : Finset (BlockTower X Y (R + 1)) := A.map e.symm.toEmbedding
  have hATdens : density AT = density A := by
    simpa [AT, e, X, Y] using density_map_equiv e.symm A
  obtain ⟨q, p, hp⟩ := hR AT
  let Aₚ : Finset (BlockTower X Y (q + 1)) := p.iterFibre AT
  have hrow (x : Word k M) :
      δ / 2 ≤ density (BlockTower.fibre Aₚ (liftWord x)) := by
    have hpx : density AT - δ / 2 ≤
        density (BlockTower.fibre Aₚ (liftWord x)) := by
      simpa only [density_eq_coe_dens, Aₚ] using hp (liftWord x)
    have hbase : δ / 2 ≤ density AT - δ / 2 := by
      rw [hATdens]
      linarith
    exact hbase.trans hpx
  let C : Finset (Word k M × BlockTower X Y q) :=
    Finset.univ.filter fun z ↦ (liftWord z.1, z.2) ∈ Aₚ
  have hCfiber (x : Word k M) :
      fiber C x = BlockTower.fibre Aₚ (liftWord x) := by
    ext y
    simp [C]
  have hCdense : δ / 2 ≤ density C := by
    rw [density_eq_average_fiber]
    apply const_le_average
    intro x
    rw [hCfiber]
    exact hrow x
  letI : Nonempty (BlockTower X Y q) := BlockTower.nonempty q
  have hCcolumns :
      δ / 2 ≤ average fun y : BlockTower X Y q ↦ density (columnFiber C y) := by
    rwa [← density_eq_average_columnFiber]
  obtain ⟨y, hy⟩ := exists_ge_of_le_average hCcolumns
  let B : Finset (Word k M) := columnFiber C y
  have hBdense : δ / 2 ≤ density B := by
    simpa [B] using hy
  obtain ⟨V, hV⟩ := hM B hBdense
  refine ⟨p.realize V.finLift y, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hxB : V x ∈ B := hV ⟨x, rfl⟩
  have hxAₚ : (liftWord (V x), y) ∈ Aₚ := by
    simpa [B, C] using hxB
  have hxAT : p.prepend (liftWord (V x), y) ∈ AT := by
    exact (UniformFibres.FrozenPrefix.mem_iterFibre p AT _).1 hxAₚ
  have hxA : e (p.prepend (liftWord (V x), y)) ∈ A := by
    simpa [AT, e] using hxAT
  simpa only [UniformFibres.FrozenPrefix.realize_apply,
    Combinatorics.Subspace.finLift_apply, e, Finset.mem_coe] using hxA

/-- A witnessing dimension for the restricted theorem works in every larger
ambient dimension, by restricting to a dense fibre and fixing the added
coordinates. -/
theorem FiniteRestrictedMDHJ.eventual {k m : ℕ} (h : FiniteRestrictedMDHJ k m) :
    EventualRestrictedMDHJ k m := by
  intro δ hδ
  obtain ⟨n₀, hn₀⟩ := h δ hδ
  refine ⟨n₀, ?_⟩
  intro n hn A hA
  letI : Nonempty (Fin (k + 1)) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  classical
  let e := wordFiberEquiv (k + 1) n₀ r
  let B : Finset (Word (k + 1) r × Word (k + 1) n₀) := A.map e.toEmbedding
  have hB : δ ≤ density B := by
    change δ ≤ density (A.map e.toEmbedding)
    rw [density_map_equiv]
    exact hA
  obtain ⟨z, hz⟩ := exists_fiber_density_ge B
  obtain ⟨U, hU⟩ := hn₀ (fiber B z) (hB.trans hz)
  refine ⟨extendSubspaceRight U z, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hmemB : (z, U (liftWord x)) ∈ B :=
    (mem_fiber B z (U (liftWord x))).1 (hU ⟨x, rfl⟩)
  have hmemA : e.symm (z, U (liftWord x)) ∈ A := by
    simpa [B] using hmemB
  have heq : e.symm (z, U (liftWord x)) =
      extendSubspaceRight U z (liftWord x) := by
    apply e.injective
    simp [e]
  simpa [heq] using hmemA

/-- Positive-dimension witness form, convenient when the ambient cube will
later be repeated in blocks. -/
theorem FiniteRestrictedMDHJ.positiveWitness {k m : ℕ}
    (h : FiniteRestrictedMDHJ k m) (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ ∀ A : Finset (Word (k + 1) n),
      δ ≤ density A → ContainsRestrictedSubspace m (A : Set (Word (k + 1) n)) := by
  obtain ⟨n₀, hn₀⟩ := h.eventual δ hδ
  refine ⟨max n₀ 1, lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _), ?_⟩
  exact hn₀ _ (Nat.le_max_left _ _)

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/UniformWordFibres.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Uniform fibres in ordinary finite word cubes

`UniformFibres.exists_uniform_frozenPrefix_real` is proved on a recursively
nested product of word blocks.  This file transports that result through
`BlockTower.wordEquiv`, so its conclusion can be consumed without leaving the
usual model `Word t n = Fin n → Fin t`.
-/



open BlockTower
open UniformFibres

namespace UniformWordFibres

/-- The subspace obtained by letting the first block vary and fixing the
flattened remainder of a block tower. -/
def towerHeadSubspace {t m s r : ℕ}
    (z : BlockTower (Word t m) (Word t s) r) :
    Combinatorics.Subspace (Fin m) (Fin t) (Fin ((r + 1) * m + s)) :=
  ((default : Combinatorics.Subspace (Fin m) (Fin t) (Fin m)).extendRightWord
      (wordEquiv t m s r z)).reindex (Equiv.refl _) (Equiv.refl _) <|
    finSumFinEquiv.trans (finCongr (by
      simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm]))

@[simp] theorem towerHeadSubspace_apply {t m s r : ℕ}
    (z : BlockTower (Word t m) (Word t s) r) (x : Word t m) :
    towerHeadSubspace z x = wordEquiv t m s (r + 1) (x, z) := by
  funext i
  simp [towerHeadSubspace, BlockTower.wordEquiv, BlockTower.wordAddEquiv,
    Combinatorics.Subspace.reindex_apply,
    Combinatorics.Subspace.extendRightWord_apply,
    Combinatorics.Subspace.sumWord, Equiv.piCongrLeft_apply]
  cases h : finSumFinEquiv.symm (Fin.cast _ i) <;> rfl

/-- Add one fixed word block in front of a subspace which already describes
the remaining block tower. -/
def towerPrependSubspace {t m s r : ℕ} (a : Word t m)
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin (r * m + s))) :
    Combinatorics.Subspace (Fin m) (Fin t) (Fin ((r + 1) * m + s)) :=
  (U.extendRightWord a).reindex (Equiv.refl _) (Equiv.refl _) <|
    (((Equiv.sumComm (Fin (r * m + s)) (Fin m)).trans finSumFinEquiv).trans
      (finCongr (by
        simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm])))

@[simp] theorem towerPrependSubspace_apply {t m s r : ℕ} (a : Word t m)
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin (r * m + s)))
    (x : Word t m) :
    towerPrependSubspace a U x =
      wordEquiv t m s (r + 1) (a, (wordEquiv t m s r).symm (U x)) := by
  funext i
  simp [towerPrependSubspace, BlockTower.wordEquiv, BlockTower.wordAddEquiv,
    Combinatorics.Subspace.reindex_apply,
    Combinatorics.Subspace.extendRightWord_apply,
    Combinatorics.Subspace.sumWord, Equiv.piCongrLeft_apply]
  cases h : finSumFinEquiv.symm (Fin.cast _ i) <;> rfl

/-- Generic version of `towerPrependSubspace`: the parameter type is
arbitrary, so the subspace may involve any collection of directions in all
remaining tower coordinates. -/
def towerPrependSubspaceGeneric {η : Type*} {t m s r : ℕ} (a : Word t m)
    (U : Combinatorics.Subspace η (Fin t) (Fin (r * m + s))) :
    Combinatorics.Subspace η (Fin t) (Fin ((r + 1) * m + s)) :=
  (U.extendRightWord a).reindex (Equiv.refl _) (Equiv.refl _) <|
    (((Equiv.sumComm (Fin (r * m + s)) (Fin m)).trans finSumFinEquiv).trans
      (finCongr (by
        simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm])))

@[simp] theorem towerPrependSubspaceGeneric_apply {η : Type*}
    {t m s r : ℕ} (a : Word t m)
    (U : Combinatorics.Subspace η (Fin t) (Fin (r * m + s)))
    (x : η → Fin t) :
    towerPrependSubspaceGeneric a U x =
      wordEquiv t m s (r + 1) (a, (wordEquiv t m s r).symm (U x)) := by
  funext i
  simp [towerPrependSubspaceGeneric, BlockTower.wordEquiv,
    BlockTower.wordAddEquiv, Combinatorics.Subspace.reindex_apply,
    Combinatorics.Subspace.extendRightWord_apply,
    Combinatorics.Subspace.sumWord, Equiv.piCongrLeft_apply]
  cases h : finSumFinEquiv.symm (Fin.cast _ i) <;> rfl

/-- Recursively insert an arbitrary subspace on all remaining flattened tower
coordinates behind a frozen prefix. -/
def frozenPrefixSubspaceGeneric {η : Type*} {t m s : ℕ} : {r q : ℕ} →
    (p : FrozenPrefix (Word t m) r q) →
    Combinatorics.Subspace η (Fin t) (Fin (q * m + s)) →
      Combinatorics.Subspace η (Fin t) (Fin (r * m + s))
  | _, _, .nil _, U => U
  | _, _, .cons a p, U =>
      towerPrependSubspaceGeneric a (frozenPrefixSubspaceGeneric p U)

@[simp] theorem frozenPrefixSubspaceGeneric_apply {η : Type*}
    {t m s : ℕ} : ∀ {r q : ℕ}
    (p : FrozenPrefix (Word t m) r q)
    (U : Combinatorics.Subspace η (Fin t) (Fin (q * m + s)))
    (x : η → Fin t),
    frozenPrefixSubspaceGeneric p U x =
      wordEquiv t m s r
        (p.prepend ((wordEquiv t m s q).symm (U x)))
  | _, _, .nil _, U, x => by
      simp [frozenPrefixSubspaceGeneric, FrozenPrefix.prepend]
  | _, _, .cons a p, U, x => by
      rw [frozenPrefixSubspaceGeneric, towerPrependSubspaceGeneric_apply,
        frozenPrefixSubspaceGeneric_apply]
      simp [FrozenPrefix.prepend]

/-- The concrete `m`-dimensional subspace selected by a frozen prefix, after
also fixing one word in the surviving suffix cube. -/
def frozenPrefixSubspace {t m s : ℕ} : {r q : ℕ} →
    (p : FrozenPrefix (Word t m) r (q + 1)) →
    BlockTower (Word t m) (Word t s) q →
      Combinatorics.Subspace (Fin m) (Fin t) (Fin (r * m + s))
  | _, _, .nil _, z => towerHeadSubspace z
  | _, _, .cons a p, z => towerPrependSubspace a (frozenPrefixSubspace p z)

@[simp] theorem frozenPrefixSubspace_apply {t m s : ℕ} : ∀ {r q : ℕ}
    (p : FrozenPrefix (Word t m) r (q + 1))
    (z : BlockTower (Word t m) (Word t s) q) (x : Word t m),
    frozenPrefixSubspace p z x =
      wordEquiv t m s r (p.prepend (x, z))
  | _, _, .nil _, z, x => towerHeadSubspace_apply z x
  | _, _, .cons a p, z, x => by
      rw [frozenPrefixSubspace, towerPrependSubspace_apply,
        frozenPrefixSubspace_apply]
      simp [FrozenPrefix.prepend]

/-- Pull a finite set of ordinary words back to the corresponding block tower. -/
noncomputable def towerPullback (t m s r : ℕ)
    (A : Finset (Word t (r * m + s))) :
    Finset (BlockTower (Word t m) (Word t s) r) :=
  A.map (wordEquiv t m s r).symm.toEmbedding

@[simp] theorem dens_towerPullback (t m s r : ℕ)
    (A : Finset (Word t (r * m + s))) :
    (towerPullback t m s r A).dens = A.dens := by
  simp [towerPullback]

/-- After freezing `p`, flatten all remaining tower coordinates back to one
ordinary word cube. -/
noncomputable def frozenPrefixWordPullback {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r q) :
    Finset (Word t (q * m + s)) :=
  (p.iterFibre (towerPullback t m s r A)).map
    (wordEquiv t m s q).toEmbedding

@[simp] theorem dens_frozenPrefixWordPullback {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r q) :
    (frozenPrefixWordPullback A p).dens =
      (p.iterFibre (towerPullback t m s r A)).dens := by
  simp [frozenPrefixWordPullback]

@[simp] theorem mem_frozenPrefixWordPullback {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r q) (z : Word t (q * m + s)) :
    z ∈ frozenPrefixWordPullback A p ↔
      wordEquiv t m s r
        (p.prepend ((wordEquiv t m s q).symm z)) ∈ A := by
  simp [frozenPrefixWordPullback]
  simp [towerPullback]

/-- Pulling the frozen-prefix word set back along an arbitrary remaining
subspace is exactly the same membership test as evaluating its realization
in the original cube. -/
@[simp] theorem mem_frozenPrefixWordPullback_subspace {η : Type*}
    {t m s r q : ℕ} (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r q)
    (U : Combinatorics.Subspace η (Fin t) (Fin (q * m + s)))
    (x : η → Fin t) :
    U x ∈ frozenPrefixWordPullback A p ↔
      frozenPrefixSubspaceGeneric p U x ∈ A := by
  rw [mem_frozenPrefixWordPullback, frozenPrefixSubspaceGeneric_apply]

theorem frozenPrefixSubspaceGeneric_mem_iff {η : Type*}
    {t m s r q : ℕ} (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r q)
    (U : Combinatorics.Subspace η (Fin t) (Fin (q * m + s)))
    (x : η → Fin t) :
    frozenPrefixSubspaceGeneric p U x ∈ A ↔
      U x ∈ frozenPrefixWordPullback A p :=
  (mem_frozenPrefixWordPullback_subspace A p U x).symm

/-- A line in the remaining word pullback maps to a line in the original set. -/
theorem containsLine_of_frozenPrefixWordPullback {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r q)
    (h : ContainsLine
      (frozenPrefixWordPullback A p : Set (Word t (q * m + s)))) :
    ContainsLine (A : Set (Word t (r * m + s))) := by
  obtain ⟨l, hl⟩ := h
  let I : Combinatorics.Subspace (Fin (q * m + s)) (Fin t)
      (Fin (q * m + s)) := default
  let U := frozenPrefixSubspaceGeneric p I
  refine ⟨U.lineMap l, ?_⟩
  rintro _ ⟨a, rfl⟩
  rw [Combinatorics.Subspace.lineMap_apply]
  apply (mem_frozenPrefixWordPullback_subspace A p I (l a)).1
  change l a ∈ frozenPrefixWordPullback A p
  exact hl ⟨a, rfl⟩

theorem not_containsLine_frozenPrefixWordPullback {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r q)
    (hA : ¬ ContainsLine (A : Set (Word t (r * m + s)))) :
    ¬ ContainsLine
      (frozenPrefixWordPullback A p : Set (Word t (q * m + s))) :=
  fun h ↦ hA (containsLine_of_frozenPrefixWordPullback A p h)

/-- The suffix fibre, expressed again as an ordinary word cube, after freezing
the prefix recorded by `p` and assigning `x` to the selected `m`-letter block. -/
noncomputable def wordFibre {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r (q + 1)) (x : Word t m) :
    Finset (Word t (q * m + s)) :=
  (BlockTower.fibre (p.iterFibre (towerPullback t m s r A)) x).map
    (wordEquiv t m s q).toEmbedding

@[simp] theorem dens_wordFibre {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r (q + 1)) (x : Word t m) :
    (wordFibre A p x).dens =
      (BlockTower.fibre (p.iterFibre (towerPullback t m s r A)) x).dens := by
  simp [wordFibre]

@[simp] theorem mem_wordFibre {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r (q + 1))
    (x : Word t m) (z : Word t (q * m + s)) :
    z ∈ wordFibre A p x ↔
      wordEquiv t m s r
        (p.prepend (x, (wordEquiv t m s q).symm z)) ∈ A := by
  simp [wordFibre]
  rw [FrozenPrefix.mem_iterFibre]
  simp [towerPullback]

/-- Membership in a suffix fibre is the same as membership of the
corresponding point of the concrete selected block subspace. -/
@[simp] theorem frozenPrefixSubspace_mem_iff_wordFibre {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r (q + 1))
    (x : Word t m) (z : Word t (q * m + s)) :
    frozenPrefixSubspace p ((wordEquiv t m s q).symm z) x ∈ A ↔
      z ∈ wordFibre A p x := by
  simpa only [frozenPrefixSubspace_apply] using (mem_wordFibre A p x z).symm

/-- Ordinary-word version of the uniform-fibres lemma, with an arbitrary
terminal suffix length `s`.  The total dimension is `(R+1)m+s`; after a
frozen prefix, every assignment to the next `m`-letter block leaves a suffix
fibre of density at least the original density minus `e`. -/
theorem exists_uniform_wordFibres (t m s : ℕ) (ht : 2 ≤ t) (hm : 0 < m)
    (e : ℝ) (he : 0 < e) :
    ∃ R : ℕ, ∀ A : Finset (Word t ((R + 1) * m + s)),
      ∃ q : ℕ, ∃ p : FrozenPrefix (Word t m) (R + 1) (q + 1),
        ∀ x : Word t m,
          (A.dens : ℝ) - e ≤ (wordFibre A p x).dens := by
  let _ : Nonempty (Fin t) := ⟨⟨0, by omega⟩⟩
  let _ : Nonempty (Word t m) := Pi.instNonempty
  have hcard : 1 < Fintype.card (Word t m) := by
    rw [card_word]
    exact one_lt_pow₀ (by omega) (Nat.ne_of_gt hm)
  obtain ⟨R, hR⟩ :=
    exists_uniform_frozenPrefix_real
      (X := Word t m) (Y := Word t s) hcard e he
  refine ⟨R, fun A ↦ ?_⟩
  obtain ⟨q, p, hp⟩ := hR (towerPullback t m s (R + 1) A)
  refine ⟨q, p, fun x ↦ ?_⟩
  have hA : ((towerPullback t m s (R + 1) A).dens : ℝ) = (A.dens : ℝ) := by
    exact_mod_cast dens_towerPullback t m s (R + 1) A
  have hF : ((wordFibre A p x).dens : ℝ) =
      ((BlockTower.fibre
        (p.iterFibre (towerPullback t m s (R + 1) A)) x).dens : ℝ) := by
    exact_mod_cast dens_wordFibre A p x
  rw [hF, ← hA]
  exact hp x

/-- A version with no terminal coordinates.  Thus one may choose the total
dimension to be a positive multiple `(R+1)m` of the target block size. -/
theorem exists_uniform_wordFibres_zeroSuffix (t m : ℕ) (ht : 2 ≤ t)
    (hm : 0 < m) (e : ℝ) (he : 0 < e) :
    ∃ R : ℕ, ∀ A : Finset (Word t ((R + 1) * m)),
      ∃ q : ℕ, ∃ p : FrozenPrefix (Word t m) (R + 1) (q + 1),
        ∀ x : Word t m,
          (A.dens : ℝ) - e ≤ (wordFibre (s := 0) A p x).dens := by
  simpa using exists_uniform_wordFibres t m 0 ht hm e he

/-- Packaged form exposing both the uniform density estimate and the concrete
subspace whose points realize the suffix fibres. -/
theorem exists_uniform_wordFibres_with_subspaces (t m s : ℕ)
    (ht : 2 ≤ t) (hm : 0 < m) (e : ℝ) (he : 0 < e) :
    ∃ R : ℕ, ∀ A : Finset (Word t ((R + 1) * m + s)),
      ∃ q : ℕ, ∃ p : FrozenPrefix (Word t m) (R + 1) (q + 1),
        (∀ x : Word t m,
          (A.dens : ℝ) - e ≤ (wordFibre A p x).dens) ∧
        ∀ (x : Word t m) (z : Word t (q * m + s)),
          frozenPrefixSubspace p ((wordEquiv t m s q).symm z) x ∈ A ↔
            z ∈ wordFibre A p x := by
  obtain ⟨R, hR⟩ := exists_uniform_wordFibres t m s ht hm e he
  refine ⟨R, fun A ↦ ?_⟩
  obtain ⟨q, p, hp⟩ := hR A
  exact ⟨q, p, hp, fun x z ↦ frozenPrefixSubspace_mem_iff_wordFibre A p x z⟩

end UniformWordFibres

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/FaceDensity.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Density of the old-alphabet face

Inside `[k+1]^m`, the words using only the first `k` letters form the image
of `[k]^m` under `liftWord`.  This file records their exact density and the
fact that this density tends to zero with the dimension.
-/



open Filter Finset

/-- The old-alphabet face in `[k+1]^m` has density `(k/(k+1))^m`. -/
theorem density_liftFinset_univ (k m : ℕ) :
    density (liftFinset (Finset.univ : Finset (Word k m))) =
      ((k : ℝ) / (k + 1)) ^ m := by
  rw [density_eq_card_div_card, card_liftFinset]
  simp only [Finset.card_univ, card_word, Nat.cast_pow, Nat.cast_add,
    Nat.cast_one, div_pow]

/-- The ratio between the old alphabet and the enlarged alphabet lies in
`[0,1)`. -/
theorem oldAlphabetRatio_nonneg_lt_one (k : ℕ) :
    0 ≤ (k : ℝ) / (k + 1) ∧ (k : ℝ) / (k + 1) < 1 := by
  constructor
  · positivity
  · rw [div_lt_one (by positivity : (0 : ℝ) < k + 1)]
    norm_num

/-- The density of the old-alphabet face tends to zero. -/
theorem tendsto_density_liftFinset_univ (k : ℕ) :
    Tendsto
      (fun m ↦ density (liftFinset (Finset.univ : Finset (Word k m))))
      atTop (nhds 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (oldAlphabetRatio_nonneg_lt_one k).1 (oldAlphabetRatio_nonneg_lt_one k).2
  exact hpow.congr' (Filter.Eventually.of_forall fun m ↦ (density_liftFinset_univ k m).symm)

/-- In sufficiently high dimension the old-alphabet face has density below
any prescribed positive threshold. -/
theorem eventually_density_liftFinset_univ_lt (k : ℕ) {eta : ℝ}
    (heta : 0 < eta) :
    ∃ M : ℕ, ∀ m ≥ M,
      density (liftFinset (Finset.univ : Finset (Word k m))) < eta := by
  have hevent : ∀ᶠ m : ℕ in atTop,
      density (liftFinset (Finset.univ : Finset (Word k m))) < eta :=
    (tendsto_order.mp (tendsto_density_liftFinset_univ k)).2 eta heta
  exact Filter.eventually_atTop.mp hevent

/-- Explicitly quantified version used by the density-increment argument. -/
theorem exists_faceDensity_lt (k : ℕ) (_hk : 0 < k) :
    ∀ eta : ℝ, 0 < eta →
      ∃ M : ℕ, ∀ m ≥ M,
        density (liftFinset (Finset.univ : Finset (Word k m))) < eta := by
  intro eta heta
  exact eventually_density_liftFinset_univ_lt k heta

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/StructuredCorrelation.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The structured correlation alternative

This file formalizes Dodos--Kanellopoulos--Tyros Lemma 10 and Corollary 11.
The numerical parameters `eta` and `gamma` are frozen at an initial density
floor `delta0`, while `rho` is the density at the current stage of the
iteration.
-/

open scoped BigOperators



attribute [local instance] Classical.dec

/-! ## Endpoint cylinders -/

/-- The old-alphabet part of a set in the enlarged cube. -/
noncomputable def oldPart {k m : ℕ} (A : Finset (Word (k + 1) m)) :
    Finset (Word k m) :=
  Finset.univ.filter fun x ↦ liftWord x ∈ A

@[simp] theorem mem_oldPart {k m : ℕ} (A : Finset (Word (k + 1) m))
    (x : Word k m) : x ∈ oldPart A ↔ liftWord x ∈ A := by
  simp [oldPart]

/-- The `(i,last)`-insensitive cylinder generated by the old part of `A`. -/
noncomputable def endpointCell {k m : ℕ} (i : Fin k)
    (A : Finset (Word (k + 1) m)) : Finset (Word (k + 1) m) :=
  setFinset (endpointCylinder i (oldPart A : Set (Word k m)))

@[simp] theorem mem_endpointCell {k m : ℕ} (i : Fin k)
    (A : Finset (Word (k + 1) m)) (x : Word (k + 1) m) :
    x ∈ endpointCell i A ↔ liftWord (endpoint i x) ∈ A := by
  simp [endpointCell]

theorem endpointCell_isLastInsensitive {k m : ℕ} (i : Fin k)
    (A : Finset (Word (k + 1) m)) :
    IsLastInsensitive i (endpointCell i A : Set (Word (k + 1) m)) := by
  intro x y hxy
  simpa [endpointCell] using
    (endpointCylinder_isLastInsensitive i (oldPart A : Set (Word k m)) x y hxy)

/-- The structured endpoint set: all old-letter endpoints must lie in `A`. -/
noncomputable def endpointCore {k m : ℕ} (A : Finset (Word (k + 1) m)) :
    Finset (Word (k + 1) m) :=
  familyInter fun i : Fin k ↦ endpointCell i A

@[simp] theorem mem_endpointCore {k m : ℕ} (A : Finset (Word (k + 1) m))
    (x : Word (k + 1) m) :
    x ∈ endpointCore A ↔ ∀ i : Fin k, liftWord (endpoint i x) ∈ A := by
  simp [endpointCore]

/-- Wildcard words associated to restricted internal lines contained in `A`. -/
noncomputable def cubeRestrictedLines {k m : ℕ}
    (A : Finset (Word (k + 1) m)) :
    Finset (Combinatorics.Line (Fin k) (Fin m)) :=
  Finset.univ.filter fun l ↦ ∀ a : Fin k, liftWord (l a) ∈ A

@[simp] theorem mem_cubeRestrictedLines {k m : ℕ}
    (A : Finset (Word (k + 1) m))
    (l : Combinatorics.Line (Fin k) (Fin m)) :
    l ∈ cubeRestrictedLines A ↔ ∀ a : Fin k, liftWord (l a) ∈ A := by
  simp [cubeRestrictedLines]

/-- Fraction of internal old-alphabet lines contained in `A`. -/
noncomputable def cubeRestrictedLineFraction {k m : ℕ}
    (A : Finset (Word (k + 1) m)) : ℝ :=
  density (cubeRestrictedLines A)

noncomputable def restrictedEndpointSet {k m : ℕ}
    (A : Finset (Word (k + 1) m)) : Finset (Word (k + 1) m) :=
  (cubeRestrictedLines A).image templateEndpoint

@[simp] theorem mem_restrictedEndpointSet {k m : ℕ}
    (A : Finset (Word (k + 1) m)) (x : Word (k + 1) m) :
    x ∈ restrictedEndpointSet A ↔
      ∃ l : Combinatorics.Line (Fin k) (Fin m),
        (∀ a : Fin k, liftWord (l a) ∈ A) ∧ templateEndpoint l = x := by
  simp [restrictedEndpointSet]

theorem restrictedEndpointSet_subset_endpointCore {k m : ℕ}
    (A : Finset (Word (k + 1) m)) :
    restrictedEndpointSet A ⊆ endpointCore A := by
  intro x hx
  rw [mem_restrictedEndpointSet] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  rw [mem_endpointCore]
  simpa only [endpoint_templateEndpoint] using hl

theorem card_restrictedEndpointSet {k m : ℕ}
    (A : Finset (Word (k + 1) m)) :
    (restrictedEndpointSet A).card =
      (cubeRestrictedLines A).card := by
  simp [restrictedEndpointSet, Finset.card_image_of_injective,
    templateEndpoint_injective]

/-- Endpoint templates occupy the same fraction of the non-old face as the
corresponding restricted lines occupy among all internal lines. -/
theorem density_restrictedEndpointSet_eq {k m : ℕ}
    (A : Finset (Word (k + 1) m)) (hR : (cubeRestrictedLines A).Nonempty) :
    density (restrictedEndpointSet A) =
      cubeRestrictedLineFraction A *
        (1 - density (liftFinset (Finset.univ : Finset (Word k m)))) := by
  letI : Nonempty (Combinatorics.Line (Fin k) (Fin m)) := ⟨hR.choose⟩
  have hq : ((Fintype.card (Combinatorics.Line (Fin k) (Fin m)) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hN : (((k + 1) ^ m : ℕ) : ℝ) ≠ 0 := by positivity
  have hle : k ^ m ≤ (k + 1) ^ m := by
    simpa [Nat.succ_eq_add_one] using Nat.pow_le_pow_left (Nat.le_succ k) m
  have hqeq :
      ((Fintype.card (Combinatorics.Line (Fin k) (Fin m)) : ℕ) : ℝ) =
        (((k + 1) ^ m : ℕ) : ℝ) - ((k ^ m : ℕ) : ℝ) := by
    rw [Combinatorics.Line.card_fin, Nat.cast_sub hle]
  rw [density_eq_card_div_card, card_restrictedEndpointSet,
    cubeRestrictedLineFraction, density_eq_card_div_card,
    density_eq_card_div_card]
  simp only [card_word, card_liftFinset, Finset.card_univ]
  field_simp [hq, hN]
  rw [hqeq]

/-- Many restricted lines and a sparse old face give a genuinely dense
endpoint core. -/
theorem endpointCore_density_lower_bound {k m : ℕ}
    (A : Finset (Word (k + 1) m)) {theta eta : ℝ}
    (htheta : 0 < theta) (heta : eta < 1 / 2)
    (hface : density (liftFinset (Finset.univ : Finset (Word k m))) < eta)
    (hlines : theta / 2 < cubeRestrictedLineFraction A) :
    theta / 4 < density (endpointCore A) := by
  have hRpos : 0 < density (cubeRestrictedLines A) := by
    exact (lt_trans (half_pos htheta) hlines)
  have hR : (cubeRestrictedLines A).Nonempty :=
    (density_pos (cubeRestrictedLines A)).1 hRpos
  have hendpoint : (theta / 2) * (1 - eta) <
      density (restrictedEndpointSet A) := by
    rw [density_restrictedEndpointSet_eq A hR]
    have hone : 0 < 1 - density
        (liftFinset (Finset.univ : Finset (Word k m))) := by
      have hnonneg := density_nonneg
        (liftFinset (Finset.univ : Finset (Word k m)))
      nlinarith
    exact mul_lt_mul hlines (by linarith) (by linarith) hRpos.le
  have hquarter := IncrementArithmetic.theta_div_four_lt htheta heta
  exact hquarter.trans (hendpoint.trans_le
    (density_mono (restrictedEndpointSet_subset_endpointCore A)))

/-! ## The line-free restriction -/

theorem templateEndpoint_endpointLine {k m : ℕ} (x : Word (k + 1) m)
    (hx : ∃ r, x r = Fin.last k) :
    templateEndpoint (endpointLine x hx) = x := by
  funext r
  by_cases hr : x r = Fin.last k
  · simp [endpointLine, templateEndpoint, hr]
  · simp [endpointLine, templateEndpoint, hr]

/-- If `A` is line-free, an element of `A` in all endpoint cylinders must
belong to the old-alphabet face. -/
theorem inter_endpointCore_subset_oldFace {k m : ℕ}
    (A : Finset (Word (k + 1) m))
    (hA : ¬ ContainsLine (A : Set (Word (k + 1) m))) :
    A ∩ endpointCore A ⊆ liftFinset (Finset.univ : Finset (Word k m)) := by
  intro x hx
  have hxA := (Finset.mem_inter.1 hx).1
  have hxC := (Finset.mem_inter.1 hx).2
  by_contra hxold
  have hxlast : ∃ r, x r = Fin.last k := by
    have hxnr : ¬IsRestrictedWord x := by
      intro hxr
      obtain ⟨y, hy⟩ := (Set.ext_iff.1 range_restrictWord x).2 hxr
      subst x
      apply hxold
      change liftWord y ∈ liftFinset (Finset.univ : Finset (Word k m))
      simp
    simpa only [IsRestrictedWord, not_forall, not_ne_iff] using hxnr
  apply hA
  rw [containsLine_coe_finset_iff]
  refine ⟨templateExtension (endpointLine x hxlast), ?_⟩
  intro a
  refine Fin.lastCases ?_ (fun i ↦ ?_) a
  · simpa [templateEndpoint_endpointLine x hxlast] using hxA
  · rw [templateExtension_castSucc]
    change liftWord (endpointLine x hxlast i) ∈ A
    rw [endpointLine_apply]
    exact (mem_endpointCore A x).1 hxC i

/-! ## First-failed-cell partition -/

/-- Words for which `i` is the first endpoint condition that fails. -/
noncomputable def firstFailedPiece {k m : ℕ} (A : Finset (Word (k + 1) m))
    (i : Fin k) : Finset (Word (k + 1) m) :=
  Finset.univ.filter fun x ↦
    (∀ j : Fin k, j < i → x ∈ endpointCell j A) ∧ x ∉ endpointCell i A

@[simp] theorem mem_firstFailedPiece {k m : ℕ}
    (A : Finset (Word (k + 1) m)) (i : Fin k) (x : Word (k + 1) m) :
    x ∈ firstFailedPiece A i ↔
      (∀ j : Fin k, j < i → x ∈ endpointCell j A) ∧ x ∉ endpointCell i A := by
  simp [firstFailedPiece]

theorem firstFailedPiece_pairwiseDisjoint {k m : ℕ}
    (A : Finset (Word (k + 1) m)) :
    ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (firstFailedPiece A) := by
  intro i _ j _ hij
  change Disjoint (firstFailedPiece A i) (firstFailedPiece A j)
  rw [Finset.disjoint_left]
  intro x hxi hxj
  have hi := (mem_firstFailedPiece A i x).1 hxi
  have hj := (mem_firstFailedPiece A j x).1 hxj
  rcases lt_trichotomy i j with hij' | hij' | hij'
  · exact hi.2 (hj.1 i hij')
  · exact hij hij'
  · exact hj.2 (hi.1 j hij')

/-- The first-failed pieces partition the complement of the endpoint core. -/
theorem biUnion_firstFailedPiece {k m : ℕ} (_hk : 0 < k)
    (A : Finset (Word (k + 1) m)) :
    Finset.univ.biUnion (firstFailedPiece A) = Finset.univ \ endpointCore A := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.1 hx
    have hi := (mem_firstFailedPiece A i x).1 hxi
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hxC
    exact hi.2 ((mem_endpointCell i A x).2 ((mem_endpointCore A x).1 hxC i))
  · intro hx
    have hxnot : ¬∀ i : Fin k, x ∈ endpointCell i A := by
      simpa [mem_endpointCore] using (Finset.mem_sdiff.1 hx).2
    push Not at hxnot
    let i : Fin k := Fin.find (fun j ↦ x ∉ endpointCell j A) hxnot
    have hi : x ∉ endpointCell i A :=
      Fin.find_spec hxnot
    have hprev : ∀ j : Fin k, j < i → x ∈ endpointCell j A := by
      intro j hj
      exact not_not.mp (Fin.find_min hxnot hj)
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i,
      (mem_firstFailedPiece A i x).2 ⟨hprev, hi⟩⟩

/-- Factors whose intersection is a prescribed first-failed piece.  Earlier
conditions are imposed positively, the selected condition negatively, and
later factors impose no restriction. -/
noncomputable def structuredFactors {k m : ℕ}
    (A : Finset (Word (k + 1) m)) (i : Fin k) (j : Fin k) :
    Finset (Word (k + 1) m) :=
  if j < i then endpointCell j A
  else if j = i then Finset.univ \ endpointCell j A
  else Finset.univ

theorem structuredFactors_isLastInsensitive {k m : ℕ}
    (A : Finset (Word (k + 1) m)) (i j : Fin k) :
    IsLastInsensitive j
      (structuredFactors A i j : Set (Word (k + 1) m)) := by
  by_cases hji : j < i
  · simpa [structuredFactors, hji] using endpointCell_isLastInsensitive j A
  · by_cases hEq : j = i
    · have hcell := endpointCell_isLastInsensitive j A
      intro x y hxy
      simpa [structuredFactors, hji, hEq] using not_congr (hcell x y hxy)
    · intro x y _
      simp [structuredFactors, hji, hEq]

theorem familyInter_structuredFactors {k m : ℕ}
    (A : Finset (Word (k + 1) m)) (i : Fin k) :
    familyInter (structuredFactors A i) = firstFailedPiece A i := by
  ext x
  rw [mem_familyInter, mem_firstFailedPiece]
  constructor
  · intro hx
    constructor
    · intro j hj
      simpa [structuredFactors, hj, ne_of_lt hj] using hx j
    · simpa [structuredFactors] using hx i
  · rintro ⟨hprev, hi⟩ j
    by_cases hj : j < i
    · simpa [structuredFactors, hj, ne_of_lt hj] using hprev j hj
    · by_cases hEq : j = i
      · subst j
        simpa [structuredFactors] using hi
      · simp [structuredFactors, hj, hEq]

theorem biUnion_inter_firstFailedPiece {k m : ℕ} (hk : 0 < k)
    (A : Finset (Word (k + 1) m)) :
    Finset.univ.biUnion (fun i : Fin k ↦ A ∩ firstFailedPiece A i) =
      A ∩ (Finset.univ \ endpointCore A) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.1 hx
    refine Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hxi).1, ?_⟩
    rw [← biUnion_firstFailedPiece hk A]
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, (Finset.mem_inter.1 hxi).2⟩
  · intro hx
    have hxQ : x ∈ Finset.univ.biUnion (firstFailedPiece A) := by
      rw [biUnion_firstFailedPiece hk A]
      exact (Finset.mem_inter.1 hx).2
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.1 hxQ
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i,
      Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hx).1, hxi⟩⟩

/-! ## DKT Lemma 10 and Corollary 11 on a coordinate cube -/

/-- The many-restricted-lines branch yields a positive-density intersection
of `k` insensitive sets on which `A` has a fixed relative increment.

The error and increment are frozen at `delta0`; `rho` is the actual current
density. -/
theorem structured_correlation_of_many_lines
    {k m : ℕ} (hk : 2 ≤ k)
    (A : Finset (Word (k + 1) m))
    (hlineFree : ¬ContainsLine (A : Set (Word (k + 1) m)))
    (delta0 rho theta : ℝ)
    (hdelta0 : 0 < delta0) (hdelta0_one : delta0 ≤ 1)
    (hdelta_rho : delta0 ≤ rho)
    (htheta : 0 < theta) (htheta_one : theta ≤ 1)
    (hface : density (liftFinset (Finset.univ : Finset (Word k m))) <
      IncrementArithmetic.eta delta0 theta)
    (hAdense : rho - 2 * IncrementArithmetic.eta delta0 theta < density A)
    (hlines : theta / 2 < cubeRestrictedLineFraction A) :
    ∃ D : Fin k → Finset (Word (k + 1) m),
      (∀ i, IsLastInsensitive i (D i : Set (Word (k + 1) m))) ∧
      IncrementArithmetic.gamma delta0 (IncrementArithmetic.eta delta0 theta) k <
        density (familyInter D) ∧
      (rho + IncrementArithmetic.gamma delta0
          (IncrementArithmetic.eta delta0 theta) k) * density (familyInter D) <
        density (A ∩ familyInter D) := by
  let eta := IncrementArithmetic.eta delta0 theta
  let gamma := IncrementArithmetic.gamma delta0 eta k
  let C := endpointCore A
  let Q : Finset (Word (k + 1) m) := Finset.univ \ C
  let P : Fin k → Finset (Word (k + 1) m) := firstFailedPiece A
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hk)
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hknat : 0 < k := lt_of_lt_of_le (by omega) hk
  have heta_pos : 0 < eta := IncrementArithmetic.eta_pos hdelta0 htheta
  have hparam := IncrementArithmetic.fixed_parameter_bounds
    hdelta0 hdelta0_one htheta htheta_one hkreal
  have heta_half : eta < 1 / 2 := hparam.2.1.trans_le (by linarith [htheta_one])
  have hthree_eta : 3 * eta < delta0 := hparam.2.2.1
  have hgamma_pos : 0 < gamma := hparam.2.2.2.1
  have hgamma_three : gamma < 3 * eta := hparam.2.2.2.2.2.1
  have hCdense : theta / 4 < density C := by
    exact endpointCore_density_lower_bound A htheta heta_half hface hlines
  have hACface : A ∩ C ⊆ liftFinset (Finset.univ : Finset (Word k m)) := by
    exact inter_endpointCore_subset_oldFace A hlineFree
  have hACsmall : density (A ∩ C) < eta :=
    (density_mono hACface).trans_lt hface
  have hAQ : rho - 3 * eta < density (A ∩ Q) := by
    have hsplit := density_sdiff_add_density_inter A C
    have hdiff : A \ C = A ∩ Q := by
      ext x
      simp [Q, C]
    rw [hdiff] at hsplit
    linarith
  have hQpos : 0 < density Q := by
    have hbase : 0 < rho - 3 * eta := by linarith
    exact hbase.trans hAQ |>.trans_le (density_inter_le_right A Q)
  have hQupper : density Q < 1 - theta / 4 := by
    have hcomp : density Q = 1 - density C := by
      simpa only [Q] using density_compl C
    rw [hcomp]
    linarith
  have hconditional :
      (rho + 6 * eta) * density Q < density (A ∩ Q) := by
    have hcoef : 0 ≤ rho + 6 * eta := by linarith
    have hmul : (rho + 6 * eta) * density Q <
        (rho + 6 * eta) * (1 - theta / 4) :=
      mul_lt_mul_of_pos_left hQupper (by linarith)
    have hfixed := IncrementArithmetic.fixed_lower_density_increment_mul
      hdelta0 hdelta_rho htheta
    exact hmul.trans (hfixed.trans hAQ)
  have hPdisj :
      ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint P :=
    firstFailedPiece_pairwiseDisjoint A
  have hPunion : Finset.univ.biUnion P = Q := by
    simpa [P, Q, C] using biUnion_firstFailedPiece hknat A
  have hAPdisj :
      ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
        (fun i ↦ A ∩ P i) := by
    intro i _ j _ hij
    exact (hPdisj (Finset.mem_univ i) (Finset.mem_univ j) hij).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hAPunion : Finset.univ.biUnion (fun i ↦ A ∩ P i) = A ∩ Q := by
    simpa [P, Q, C] using biUnion_inter_firstFailedPiece hknat A
  let weight : Fin k → ℝ := fun i ↦ density (P i) / density Q
  let value : Fin k → ℝ := fun i ↦
    if density (P i) = 0 then 0 else density (A ∩ P i) / density (P i)
  have hweight_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin k)), 0 ≤ weight i := by
    intro i _
    exact div_nonneg (density_nonneg _) hQpos.le
  have hvalue_le : ∀ i ∈ (Finset.univ : Finset (Fin k)), value i ≤ 1 := by
    intro i _
    by_cases hi : density (P i) = 0
    · change (if density (P i) = 0 then 0 else
          density (A ∩ P i) / density (P i)) ≤ 1
      rw [if_pos hi]
      norm_num
    · change (if density (P i) = 0 then 0 else
          density (A ∩ P i) / density (P i)) ≤ 1
      rw [if_neg hi]
      rw [div_le_one (lt_of_le_of_ne (density_nonneg _) (Ne.symm hi))]
      exact density_inter_le_right A (P i)
  have hweight_sum : ∑ i ∈ (Finset.univ : Finset (Fin k)), weight i = 1 := by
    change (∑ i ∈ (Finset.univ : Finset (Fin k)),
      density (P i) / density Q) = 1
    rw [← Finset.sum_div]
    rw [← density_biUnion hPdisj, hPunion]
    exact div_self hQpos.ne'
  have hpoint (i : Fin k) :
      weight i * value i = density (A ∩ P i) / density Q := by
    by_cases hi : density (P i) = 0
    · have hPi : P i = ∅ := (density_eq_zero (P i)).1 hi
      simp [weight, value, hPi]
    · simp only [weight, value, hi, if_false]
      field_simp [hi, hQpos.ne']
  have haverage_eq :
      (∑ i ∈ (Finset.univ : Finset (Fin k)), weight i * value i) =
        density (A ∩ Q) / density Q := by
    simp_rw [hpoint]
    rw [← Finset.sum_div, ← density_biUnion hAPdisj, hAPunion]
  have haverage : rho + 6 * eta <
      ∑ i ∈ (Finset.univ : Finset (Fin k)), weight i * value i := by
    rw [haverage_eq, lt_div_iff₀ hQpos]
    exact hconditional
  obtain ⟨i, _, hweight, hvalue⟩ :=
    IncrementArithmetic.exists_large_weight_and_value
      (Finset.univ : Finset (Fin k)) weight value
      hkpos (by simp) heta_pos hweight_nonneg hvalue_le hweight_sum
      (by linarith) haverage
  have hPi_pos : 0 < density (P i) := by
    have hsmallpos : 0 < 3 * eta / (k : ℝ) := by positivity
    have : 0 < weight i := hsmallpos.trans hweight
    by_contra hnot
    have hzero : density (P i) = 0 := le_antisymm (le_of_not_gt hnot) (density_nonneg _)
    have : weight i = 0 := by
      change density (P i) / density Q = 0
      rw [hzero, zero_div]
    linarith
  have hPi_lower :
      (3 * eta / (k : ℝ)) * (rho - 3 * eta) < density (P i) := by
    have hweight_mul : (3 * eta / (k : ℝ)) * density Q < density (P i) := by
      change 3 * eta / (k : ℝ) < density (P i) / density Q at hweight
      exact (lt_div_iff₀ hQpos).mp hweight
    have hqbase : rho - 3 * eta < density Q :=
      hAQ.trans_le (density_inter_le_right A Q)
    have hcoef : 0 < 3 * eta / (k : ℝ) := by positivity
    exact (mul_lt_mul_of_pos_left hqbase hcoef).trans hweight_mul
  have hPi_gamma : gamma < density (P i) := by
    exact (IncrementArithmetic.fixed_gamma_lt_structured_piece
      hdelta0 hdelta0_one hdelta_rho htheta htheta_one hkpos).trans hPi_lower
  have hAPi : (rho + 3 * eta) * density (P i) < density (A ∩ P i) := by
    simp only [value, hPi_pos.ne', if_false] at hvalue
    exact (lt_div_iff₀ hPi_pos).mp hvalue
  have hAPi_gamma :
      (rho + gamma) * density (P i) < density (A ∩ P i) := by
    have hleft : (rho + gamma) * density (P i) <
        (rho + 3 * eta) * density (P i) :=
      mul_lt_mul_of_pos_right (by linarith) hPi_pos
    exact hleft.trans hAPi
  refine ⟨structuredFactors A i, structuredFactors_isLastInsensitive A i,
    ?_, ?_⟩
  · simpa [gamma, P, familyInter_structuredFactors] using hPi_gamma
  · simpa [gamma, P, familyInter_structuredFactors] using hAPi_gamma

/-! ## Transport to an arbitrary subspace and the Lemma 8 alternative -/

theorem cubeRestrictedLines_pullback {k m : ℕ} {iota : Type*}
    (W : Combinatorics.Subspace (Fin m) (Fin (k + 1)) iota)
    (A : Finset (iota → Fin (k + 1))) :
    cubeRestrictedLines (pullbackFinset W A) = restrictedInternalLines W A := by
  ext l
  simp [cubeRestrictedLines, restrictedInternalLines]

theorem cubeRestrictedLineFraction_pullback {k m : ℕ} {iota : Type*}
    (W : Combinatorics.Subspace (Fin m) (Fin (k + 1)) iota)
    (A : Finset (iota → Fin (k + 1))) :
    cubeRestrictedLineFraction (pullbackFinset W A) =
      restrictedInternalLineFraction W A := by
  rw [cubeRestrictedLineFraction, restrictedInternalLineFraction,
    cubeRestrictedLines_pullback]

/-- Coordinate-type-independent form of line containment, needed because the
correlation step naturally uses a sum of coordinate types. -/
def ContainsLineOn {alpha iota : Type*} (A : Set (iota → alpha)) : Prop :=
  ∃ l : Combinatorics.Line alpha iota, Set.range l ⊆ A

theorem pullback_lineFree {k m : ℕ} {iota : Type*}
    (W : Combinatorics.Subspace (Fin m) (Fin (k + 1)) iota)
    (A : Finset (iota → Fin (k + 1)))
    (hA : ¬ContainsLineOn (A : Set (iota → Fin (k + 1)))) :
    ¬ContainsLine (pullbackFinset W A : Set (Word (k + 1) m)) := by
  intro h
  apply hA
  obtain ⟨l, hl⟩ := h
  refine ⟨W.lineMap l, ?_⟩
  rintro _ ⟨a, rfl⟩
  rw [Combinatorics.Subspace.lineMap_apply]
  exact (mem_pullbackFinset W A (l a)).1 (hl ⟨a, rfl⟩)

/-- Subspace form of the many-lines branch. -/
theorem structured_correlation_on_subspace_of_many_lines
    {k m : ℕ} (hk : 2 ≤ k) {iota : Type*}
    (W : Combinatorics.Subspace (Fin m) (Fin (k + 1)) iota)
    (A : Finset (iota → Fin (k + 1)))
    (hlineFree : ¬ContainsLineOn (A : Set (iota → Fin (k + 1))))
    (delta0 rho theta : ℝ)
    (hdelta0 : 0 < delta0) (hdelta0_one : delta0 ≤ 1)
    (hdelta_rho : delta0 ≤ rho)
    (htheta : 0 < theta) (htheta_one : theta ≤ 1)
    (hface : density (liftFinset (Finset.univ : Finset (Word k m))) <
      IncrementArithmetic.eta delta0 theta)
    (hWdense : rho - 2 * IncrementArithmetic.eta delta0 theta <
      subspaceDensityFinset W A)
    (hWlines : theta / 2 < restrictedInternalLineFraction W A) :
    ∃ D : Fin k → Finset (Word (k + 1) m),
      (∀ i, IsLastInsensitive i (D i : Set (Word (k + 1) m))) ∧
      IncrementArithmetic.gamma delta0 (IncrementArithmetic.eta delta0 theta) k <
        density (familyInter D) ∧
      (rho + IncrementArithmetic.gamma delta0
          (IncrementArithmetic.eta delta0 theta) k) * density (familyInter D) <
        density (pullbackFinset W A ∩ familyInter D) := by
  apply structured_correlation_of_many_lines hk (pullbackFinset W A)
    (pullback_lineFree W A hlineFree) delta0 rho theta hdelta0 hdelta0_one
    hdelta_rho htheta htheta_one hface
  · exact hWdense
  · simpa only [cubeRestrictedLineFraction_pullback] using hWlines

/-- DKT Corollary 11 directly from the disjunction in Correlation Lemma 8.
Both branches have the same structured conclusion: in the direct increment
branch all insensitive factors are the whole cube. -/
theorem structured_correlation_of_correlated_sections
    {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m) {iota kappa : Type*}
    [Fintype kappa]
    (U : Combinatorics.Subspace (Fin m) (Fin (k + 1)) iota)
    (A : Finset (iota ⊕ kappa → Fin (k + 1)))
    (hlineFree : ¬ContainsLineOn (A : Set (iota ⊕ kappa → Fin (k + 1))))
    (delta0 rho theta : ℝ)
    (hdelta0 : 0 < delta0) (hdelta0_one : delta0 ≤ 1)
    (hdelta_rho : delta0 ≤ rho)
    (htheta : 0 < theta) (htheta_one : theta ≤ 1)
    (hface : density (liftFinset (Finset.univ : Finset (Word k m))) <
      IncrementArithmetic.eta delta0 theta)
    (hsection : ∀ x : Word (k + 1) m,
      rho - (IncrementArithmetic.eta delta0 theta) ^ 2 / 2 ≤
        density (sectionTails U A x))
    (hcorrelation : ∀ l : Combinatorics.Line (Fin k) (Fin m),
      theta ≤ density (restrictedLineTails U A l)) :
    ∃ W : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (iota ⊕ kappa),
      ∃ D : Fin k → Finset (Word (k + 1) m),
        (∀ i, IsLastInsensitive i (D i : Set (Word (k + 1) m))) ∧
        IncrementArithmetic.gamma delta0 (IncrementArithmetic.eta delta0 theta) k <
          density (familyInter D) ∧
        (rho + IncrementArithmetic.gamma delta0
            (IncrementArithmetic.eta delta0 theta) k) * density (familyInter D) <
          density (pullbackFinset W A ∩ familyInter D) := by
  let eta := IncrementArithmetic.eta delta0 theta
  let gamma := IncrementArithmetic.gamma delta0 eta k
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hparam := IncrementArithmetic.fixed_parameter_bounds
    hdelta0 hdelta0_one htheta htheta_one hkreal
  have heta_pos : 0 < eta := hparam.1
  have heta_theta : eta < theta / 2 := hparam.2.1
  have hgamma_pos : 0 < gamma := hparam.2.2.2.1
  have hgamma_half : gamma ≤ eta ^ 2 / 2 := hparam.2.2.2.2.1
  have hgamma_one : gamma < 1 := hparam.2.2.2.2.2.2.2.1
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  rcases density_increment_or_many_restricted_lines U A rho eta theta
      heta_pos htheta heta_theta hsection hcorrelation with hinc | hmany
  · obtain ⟨W, hW⟩ := hinc
    let D : Fin k → Finset (Word (k + 1) m) := fun _ ↦ Finset.univ
    refine ⟨W, D, ?_, ?_, ?_⟩
    · intro i x y _
      simp [D]
    · have : density (familyInter D) = 1 := by
        haveI : Nonempty (Word (k + 1) m) := inferInstance
        rw [show familyInter D = Finset.univ by ext x; simp [D], density_univ]
      change gamma < density (familyInter D)
      rw [this]
      exact hgamma_one
    · have hinter : pullbackFinset W A ∩ familyInter D = pullbackFinset W A := by
        ext x
        simp [D]
      rw [hinter]
      have hden : subspaceDensityFinset W A = density (pullbackFinset W A) := rfl
      rw [hden] at hW
      have hfamily : density (familyInter D) = 1 := by
        haveI : Nonempty (Word (k + 1) m) := inferInstance
        rw [show familyInter D = Finset.univ by ext x; simp [D], density_univ]
      rw [hfamily, mul_one]
      nlinarith
  · obtain ⟨W, hWdense, hWlines⟩ := hmany
    refine ⟨W, ?_⟩
    exact structured_correlation_on_subspace_of_many_lines hk W A hlineFree
      delta0 rho theta hdelta0 hdelta0_one hdelta_rho htheta htheta_one
      hface hWdense hWlines

/-- Lemma 7 followed by Lemma 8 and Corollary 11.  This is the uniform-section
interface used by the density-increment iteration: once all point sections of
a sufficiently large prefix subspace have the required lower bound, the
conclusion is a structured relative increment on an `m`-dimensional subspace. -/
theorem structured_correlation_of_uniform_sections
    (k m0 m : ℕ) (hk : 2 ≤ k) (hm0 : 0 < m0) (hm0m : m0 ≤ m)
    {iota kappa : Type*} [Fintype kappa]
    (delta0 : ℝ) (hdelta0 : 0 < delta0) (hdelta0_one : delta0 ≤ 1)
    (htheta : 0 < IncrementArithmetic.theta delta0
      (Fintype.card (Combinatorics.Line (Fin k) (Fin m0))))
    (htheta_one : IncrementArithmetic.theta delta0
      (Fintype.card (Combinatorics.Line (Fin k) (Fin m0))) ≤ 1)
    (herror : (IncrementArithmetic.eta delta0
      (IncrementArithmetic.theta delta0
        (Fintype.card (Combinatorics.Line (Fin k) (Fin m0))))) ^ 2 / 2 ≤
        delta0 / 2)
    (hface : density (liftFinset (Finset.univ : Finset (Word k m))) <
      IncrementArithmetic.eta delta0
        (IncrementArithmetic.theta delta0
          (Fintype.card (Combinatorics.Line (Fin k) (Fin m0)))))
    (hDHJ : ∀ B : Finset (Word k m0),
      delta0 / 4 ≤ density B → ContainsLine (B : Set (Word k m0))) :
    ∃ N : ℕ, ∀ r ≥ N,
      ∀ (U : Combinatorics.Subspace (Fin r) (Fin (k + 1)) iota)
        (A : Finset (iota ⊕ kappa → Fin (k + 1))) (rho : ℝ),
        delta0 ≤ rho →
        ¬ContainsLineOn (A : Set (iota ⊕ kappa → Fin (k + 1))) →
        (∀ x : Word (k + 1) r,
          rho - (IncrementArithmetic.eta delta0
            (IncrementArithmetic.theta delta0
              (Fintype.card (Combinatorics.Line (Fin k) (Fin m0))))) ^ 2 / 2 ≤
            density (sectionTails U A x)) →
        ∃ W : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (iota ⊕ kappa),
          ∃ D : Fin k → Finset (Word (k + 1) m),
            (∀ i, IsLastInsensitive i (D i : Set (Word (k + 1) m))) ∧
            IncrementArithmetic.gamma delta0
                (IncrementArithmetic.eta delta0
                  (IncrementArithmetic.theta delta0
                    (Fintype.card (Combinatorics.Line (Fin k) (Fin m0))))) k <
              density (familyInter D) ∧
            (rho + IncrementArithmetic.gamma delta0
                (IncrementArithmetic.eta delta0
                  (IncrementArithmetic.theta delta0
                    (Fintype.card (Combinatorics.Line (Fin k) (Fin m0))))) k) *
                density (familyInter D) <
              density (pullbackFinset W A ∩ familyInter D) := by
  let theta : ℝ := IncrementArithmetic.theta delta0
    (Fintype.card (Combinatorics.Line (Fin k) (Fin m0)))
  let eta : ℝ := IncrementArithmetic.eta delta0 theta
  have hkpos : 0 < k := lt_of_lt_of_le (by omega) hk
  have hm : 0 < m := hm0.trans_le hm0m
  obtain ⟨N, hN⟩ := exists_correlated_subspace_of_uniform_sections
    k m0 m hkpos hm0 hm0m delta0 eta hdelta0 herror hDHJ
  refine ⟨N, ?_⟩
  intro r hr U A rho hdelta_rho hlineFree hsection
  obtain ⟨V, hVsection, hVcorrelation⟩ :=
    hN r hr U A rho hdelta_rho hsection
  exact structured_correlation_of_correlated_sections hk hm V A hlineFree
    delta0 rho theta hdelta0 hdelta0_one hdelta_rho htheta htheta_one
    hface hVsection hVcorrelation

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/UniformCorrelation.lean` -/

section
open Combinatorics

namespace UniformCorrelation

attribute [local instance] Classical.dec

/-- A local finiteness instance for nested block coordinates.  It is local
to this file so consumers may choose their own representation of the split
coordinate cube. -/
noncomputable local instance instFintypeBlockCoord (M s r : ℕ) :
    Fintype (BlockCoord M s r) :=
  Fintype.ofEquiv (Fin (r * M + s)) (BlockCoord.equivFin M s r).symm

namespace FrozenPrefix

open BlockTower

def freeBlockTailNested {t M s q : ℕ} : ∀ {r : ℕ},
    UniformFibres.FrozenPrefix (Word t M) r (q + 1) →
      Subspace (Fin M ⊕ BlockCoord M s q) (Fin t) (BlockCoord M s r)
  | _, .nil _ => default
  | _, .cons z p => fixedLeft z (freeBlockTailNested p)

@[simp] theorem freeBlockTailNested_apply {t M s q : ℕ} : ∀ {r : ℕ}
    (p : UniformFibres.FrozenPrefix (Word t M) r (q + 1))
    (x : Word t M) (y : BlockCoord M s q → Fin t),
    freeBlockTailNested (s := s) p (Subspace.sumWord x y) =
      BlockTower.functionEquiv t M s r
        (p.prepend (x, (BlockTower.functionEquiv t M s q).symm y))
  | _, .nil _, x, y => by
      change Sum.elim x y =
        BlockTower.functionEquiv t M s (q + 1)
          (x, (BlockTower.functionEquiv t M s q).symm y)
      rw [BlockTower.functionEquiv_succ_apply]
      simp
  | _, .cons z p, x, y => by
      rw [freeBlockTailNested, fixedLeft_apply,
        BlockTower.functionEquiv_succ_apply]
      exact congrArg (Sum.elim z)
        (freeBlockTailNested_apply (s := s) p x y)

def freeBlockTail {t M s q r : ℕ}
    (p : UniformFibres.FrozenPrefix (Word t M) r (q + 1)) :
    Subspace (Fin M ⊕ BlockCoord M s q) (Fin t) (Fin (r * M + s)) :=
  (freeBlockTailNested (s := s) p).reindex (Equiv.refl _) (Equiv.refl _)
    (BlockCoord.equivFin M s r)

@[simp] theorem freeBlockTail_apply_sumWord {t M s q r : ℕ}
    (p : UniformFibres.FrozenPrefix (Word t M) r (q + 1))
    (x : Word t M) (y : BlockCoord M s q → Fin t) :
    freeBlockTail p (Subspace.sumWord x y) =
      BlockTower.coordinateWordEquiv t M s r
        (p.prepend (x, (BlockTower.functionEquiv t M s q).symm y)) := by
  funext i
  simp [freeBlockTail, BlockTower.coordinateWordEquiv_apply,
    Subspace.reindex_apply]

end FrozenPrefix

@[simp] theorem defaultSubspace_apply {alpha iota : Type*}
    (x : iota → alpha) :
    (default : Subspace iota alpha iota) x = x := rfl

/-- Change from the block flattening used by `UniformWordFibres` to the
explicit nested-coordinate flattening used by `FrozenPrefix.freeBlockTail`. -/
noncomputable def uniformCoordinatePullback (t M s r : ℕ)
    (A : Finset (Word t (r * M + s))) :
    Finset (Word t (r * M + s)) :=
  A.map (((BlockTower.wordEquiv t M s r).symm.trans
    (BlockTower.coordinateWordEquiv t M s r)).symm.toEmbedding)

@[simp] theorem density_uniformCoordinatePullback (t M s r : ℕ)
    (A : Finset (Word t (r * M + s))) :
    density (uniformCoordinatePullback t M s r A) = density A := by
  rw [uniformCoordinatePullback, density_map_equiv]

@[simp] theorem wordEquiv_mem_uniformCoordinatePullback
    (t M s r : ℕ) (A : Finset (Word t (r * M + s)))
    (z : BlockTower (Word t M) (Word t s) r) :
    BlockTower.wordEquiv t M s r z ∈ uniformCoordinatePullback t M s r A ↔
      BlockTower.coordinateWordEquiv t M s r z ∈ A := by
  simp only [uniformCoordinatePullback, Finset.mem_map,
    Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨a, ha, h⟩
    have hz : (BlockTower.coordinateWordEquiv t M s r).symm a = z := by
      apply (BlockTower.wordEquiv t M s r).injective
      exact h
    have haeq : a = BlockTower.coordinateWordEquiv t M s r z := by
      apply (BlockTower.coordinateWordEquiv t M s r).symm.injective
      simpa using hz
    exact haeq ▸ ha
  · intro hz
    exact ⟨BlockTower.coordinateWordEquiv t M s r z, hz, by simp⟩

theorem density_sectionTails_freeBlockTail_eq_wordFibre
    {k M s q r : ℕ}
    (A : Finset (Word (k + 1) (r * M + s)))
    (p : UniformFibres.FrozenPrefix (Word (k + 1) M) r (q + 1))
    (x : Word (k + 1) M) :
    density (sectionTails
      (default : Subspace (Fin M) (Fin (k + 1)) (Fin M))
      (pullbackFinset (FrozenPrefix.freeBlockTail p) A) x) =
      density (UniformWordFibres.wordFibre
        (uniformCoordinatePullback (k + 1) M s r A) p x) := by
  classical
  let e : (BlockCoord M s q → Fin (k + 1)) ≃ Word (k + 1) (q * M + s) :=
    (BlockTower.functionEquiv (k + 1) M s q).symm.trans
      (BlockTower.wordEquiv (k + 1) M s q)
  have hset :
      sectionTails (default : Subspace (Fin M) (Fin (k + 1)) (Fin M))
          (pullbackFinset (FrozenPrefix.freeBlockTail p) A) x =
        (UniformWordFibres.wordFibre
          (uniformCoordinatePullback (k + 1) M s r A) p x).map
            e.symm.toEmbedding := by
    ext y
    simp only [mem_sectionTails, mem_pullbackFinset, Finset.mem_map,
      Equiv.toEmbedding_apply, UniformWordFibres.mem_wordFibre,
      wordEquiv_mem_uniformCoordinatePullback, defaultSubspace_apply]
    change FrozenPrefix.freeBlockTail p (Subspace.sumWord x y) ∈ A ↔ _
    rw [FrozenPrefix.freeBlockTail_apply_sumWord p x y]
    constructor
    · intro hy
      refine ⟨e y, ?_, ?_⟩
      · simpa [e] using hy
      · exact e.symm_apply_apply y
    · rintro ⟨a, ha, hay⟩
      have haeq : a = e y := by
        apply e.symm.injective
        simpa using hay
      subst a
      simpa [e] using ha
  rw [hset]
  exact density_map_equiv e.symm _

theorem pullback_lineFreeOn {alpha eta iota : Type*}
    [Fintype alpha] [DecidableEq alpha] [Fintype eta] [DecidableEq eta]
    (U : Subspace eta alpha iota) (A : Finset (iota → alpha))
    (hA : ¬ ContainsLineOn (A : Set (iota → alpha))) :
    ¬ ContainsLineOn (pullbackFinset U A : Set (eta → alpha)) := by
  intro h
  apply hA
  obtain ⟨l, hl⟩ := h
  refine ⟨U.lineMap l, ?_⟩
  rintro _ ⟨a, rfl⟩
  rw [Subspace.lineMap_apply]
  exact (mem_pullbackFinset U A (l a)).1 (hl ⟨a, rfl⟩)

theorem exists_structured_correlation_at
    (k m0 m : ℕ) (hk : 2 ≤ k) (hm0 : 0 < m0) (hm0m : m0 ≤ m)
    (delta0 : ℝ) (hdelta0 : 0 < delta0) (hdelta0_one : delta0 ≤ 1)
    (htheta : 0 < IncrementArithmetic.theta delta0
      (Fintype.card (Line (Fin k) (Fin m0))))
    (htheta_one : IncrementArithmetic.theta delta0
      (Fintype.card (Line (Fin k) (Fin m0))) ≤ 1)
    (herror : (IncrementArithmetic.eta delta0
      (IncrementArithmetic.theta delta0
        (Fintype.card (Line (Fin k) (Fin m0))))) ^ 2 / 2 ≤ delta0 / 2)
    (hface : density (liftFinset (Finset.univ : Finset (Word k m))) <
      IncrementArithmetic.eta delta0
        (IncrementArithmetic.theta delta0
          (Fintype.card (Line (Fin k) (Fin m0)))))
    (hDHJ : ∀ B : Finset (Word k m0), delta0 / 4 ≤ density B →
      ContainsLine (B : Set (Word k m0))) :
    ∃ n : ℕ, ∀ A : Finset (Word (k + 1) n), delta0 ≤ density A →
      ¬ContainsLine (A : Set (Word (k + 1) n)) →
        ∃ W : Subspace (Fin m) (Fin (k + 1)) (Fin n),
        ∃ D : Fin k → Finset (Word (k + 1) m),
          (∀ i, IsLastInsensitive i (D i : Set (Word (k + 1) m))) ∧
          IncrementArithmetic.gamma delta0
              (IncrementArithmetic.eta delta0
                (IncrementArithmetic.theta delta0
                  (Fintype.card (Line (Fin k) (Fin m0))))) k <
            density (familyInter D) ∧
          (density A + IncrementArithmetic.gamma delta0
              (IncrementArithmetic.eta delta0
                (IncrementArithmetic.theta delta0
                  (Fintype.card (Line (Fin k) (Fin m0))))) k) *
              density (familyInter D) <
            density (pullbackFinset W A ∩ familyInter D) := by
  let theta : ℝ := IncrementArithmetic.theta delta0
    (Fintype.card (Line (Fin k) (Fin m0)))
  let eta : ℝ := IncrementArithmetic.eta delta0 theta
  have heta : 0 < eta := IncrementArithmetic.eta_pos hdelta0 htheta
  have hkpos : 0 < k := lt_of_lt_of_le (by omega) hk
  have hm : 0 < m := hm0.trans_le hm0m
  obtain ⟨N, hN⟩ := exists_correlated_subspace_of_uniform_sections
    k m0 m hkpos hm0 hm0m delta0 eta hdelta0 herror hDHJ
  let M := N + 1
  have hM : 0 < M := by simp [M]
  have hk1 : 2 ≤ k + 1 := by omega
  obtain ⟨R, hR⟩ := UniformWordFibres.exists_uniform_wordFibres_zeroSuffix
    (k + 1) M hk1 hM (eta ^ 2 / 2) (by positivity)
  refine ⟨(R + 1) * M, ?_⟩
  intro A hAdense hline
  let A0 := uniformCoordinatePullback (k + 1) M 0 (R + 1) A
  obtain ⟨q, p, hp⟩ := hR A0
  let P := FrozenPrefix.freeBlockTail (s := 0) p
  let B := pullbackFinset P A
  have hlineOnA : ¬ ContainsLineOn (A : Set (Word (k + 1) ((R + 1) * M))) := by
    simpa only [ContainsLine, ContainsLineOn] using hline
  have hlineB : ¬ ContainsLineOn
      (B : Set ((Fin M ⊕ BlockCoord M 0 q) → Fin (k + 1))) :=
    by simpa only [B] using pullback_lineFreeOn P A hlineOnA
  have hsections : ∀ x : Word (k + 1) M,
      density A - eta ^ 2 / 2 ≤
        density (sectionTails
          (default : Subspace (Fin M) (Fin (k + 1)) (Fin M)) B x) := by
    intro x
    rw [density_sectionTails_freeBlockTail_eq_wordFibre
      (M := M) (s := 0) (q := q) (r := R + 1) A p x]
    have hx := hp x
    have hA0 : (A0.dens : ℝ) = (A.dens : ℝ) := by
      calc
        (A0.dens : ℝ) = density A0 := (density_eq_coe_dens A0).symm
        _ = density A := by simp only [A0, density_uniformCoordinatePullback]
        _ = (A.dens : ℝ) := density_eq_coe_dens A
    simpa only [density_eq_coe_dens, hA0] using hx
  have hNM : N ≤ M := by simp [M]
  obtain ⟨V, hVsections, hVcorrelation⟩ :=
    hN M hNM (default : Subspace (Fin M) (Fin (k + 1)) (Fin M))
      B (density A) hAdense hsections
  obtain ⟨W, D, hDins, hDdense, hDcorr⟩ :=
    structured_correlation_of_correlated_sections hk hm V B hlineB
      delta0 (density A) theta hdelta0 hdelta0_one hAdense htheta
      htheta_one hface hVsections hVcorrelation
  refine ⟨P.comp W, D, hDins, hDdense, ?_⟩
  -- `subspacePullback` and `pullbackFinset` are the same filter declared in two
  -- independent upstream modules; only the latter has a `comp` law, so supply the
  -- former's here.
  have hcomp : subspacePullback (P.comp W) A =
      subspacePullback W (subspacePullback P A) := by
    classical
    ext x
    simp [Combinatorics.Subspace.comp_apply]
  simpa [B, P, theta, pullbackFinset_comp, hcomp] using hDcorr

end UniformCorrelation

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/InsensitiveTiling.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Tiling an insensitive set

This file contains the tiling step in the Dodos--Kanellopoulos--Tyros proof.
The first lemma is its elementary geometric core: on an `(i,last)`-insensitive
set, containment of the old-alphabet restriction of a subspace upgrades to
containment of the whole subspace.
-/



open Combinatorics

/-- Membership in the image of a finite set under an equivalence. -/
@[simp] theorem mem_map_equiv_toEmbedding {A B : Type*}
    [DecidableEq A] [DecidableEq B] (e : A ≃ B) (S : Finset A) (b : B) :
    b ∈ S.map e.toEmbedding ↔ e.symm b ∈ S := by
  constructor
  · intro hb
    obtain ⟨a, ha, hab⟩ := Finset.mem_map.mp hb
    simpa [← hab] using ha
  · intro hb
    exact Finset.mem_map.mpr ⟨e.symm b, hb, e.apply_symm_apply b⟩

/-- The family of all translates of a common block template over its
support.  It is defined early because both the geometric tiling construction
and the fresh-block invariant use the same finite set. -/
noncomputable def commonBlockLayer {X B Y : Type*}
    [Fintype X] [Fintype B] [Fintype Y]
    (S : Finset (X × Y)) (V : Finset B) : Finset ((X × B) × Y) := by
  classical
  exact Finset.univ.filter fun z ↦ (z.1.1, z.2) ∈ S ∧ z.1.2 ∈ V

@[simp] theorem mem_commonBlockLayer {X B Y : Type*}
    [Fintype X] [Fintype B] [Fintype Y]
    (S : Finset (X × Y)) (V : Finset B) (z : (X × B) × Y) :
    z ∈ commonBlockLayer S V ↔ (z.1.1, z.2) ∈ S ∧ z.1.2 ∈ V := by
  classical
  simp [commonBlockLayer]

section MiddleSubspaces

variable {eta alpha xi mu upsilon : Type*}

/-- Insert a subspace in a middle coordinate block, fixing the coordinates
on both sides. -/
def middleSubspace (x : xi → alpha) (U : Subspace eta alpha mu)
    (y : upsilon → alpha) : Subspace eta alpha ((xi ⊕ mu) ⊕ upsilon) where
  idxFun
    | Sum.inl (Sum.inl a) => Sum.inl (x a)
    | Sum.inl (Sum.inr b) => U.idxFun b
    | Sum.inr c => Sum.inl (y c)
  proper e := by
    obtain ⟨b, hb⟩ := U.proper e
    exact ⟨Sum.inl (Sum.inr b), hb⟩

@[simp] theorem middleSubspace_apply (x : xi → alpha)
    (U : Subspace eta alpha mu) (y : upsilon → alpha) (a : eta → alpha) :
    middleSubspace x U y a = Sum.elim (Sum.elim x (U a)) y := by
  funext c
  rcases c with (c | c) | c <;> simp [middleSubspace, Subspace.coe_apply]

/-- Split a word into the unused coordinates, current block, and used
suffix. -/
def splitMiddleWord : (((xi ⊕ mu) ⊕ upsilon) → alpha) ≃
    (((xi → alpha) × (mu → alpha)) × (upsilon → alpha)) :=
  (Equiv.sumArrowEquivProdArrow (xi ⊕ mu) upsilon alpha).trans
    ((Equiv.sumArrowEquivProdArrow xi mu alpha).prodCongr (Equiv.refl _))

@[simp] theorem splitMiddleWord_middleSubspace_apply
    (x : xi → alpha) (U : Subspace eta alpha mu)
    (y : upsilon → alpha) (a : eta → alpha) :
    splitMiddleWord (middleSubspace x U y a) = ((x, U a), y) := by
  rfl

variable [Fintype (eta → alpha)] [Fintype (xi → alpha)]
  [Fintype (mu → alpha)] [Fintype (upsilon → alpha)]
  [DecidableEq (mu → alpha)]
  [DecidableEq (((xi ⊕ mu) ⊕ upsilon) → alpha)]

/-- The translates of one common middle-block template form a disjoint
subspace tiling. -/
noncomputable def commonBlockTiling
    (S : Finset ((xi → alpha) × (upsilon → alpha)))
    (U : Subspace eta alpha mu) :
    SubspaceTiling eta alpha ((xi ⊕ mu) ⊕ upsilon) := by
  classical
  exact
    { tiles := S.image fun p ↦ middleSubspace p.1 U p.2
      pairwiseDisjoint := by
        intro A hA B hB hAB
        obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨q, hqS, rfl⟩ := Finset.mem_image.mp hB
        change Disjoint (subspacePoints (middleSubspace p.1 U p.2))
          (subspacePoints (middleSubspace q.1 U q.2))
        rw [Finset.disjoint_left]
        intro z hzP hzQ
        rw [mem_subspacePoints] at hzP hzQ
        obtain ⟨a, ha⟩ := hzP
        obtain ⟨b, hb⟩ := hzQ
        have heq : ((p.1, U a), p.2) = ((q.1, U b), q.2) := by
          rw [← splitMiddleWord_middleSubspace_apply p.1 U p.2 a,
            ← splitMiddleWord_middleSubspace_apply q.1 U q.2 b,
            ha, hb]
        have hpq : p = q := by
          apply Prod.ext
          · exact congrArg (fun w ↦ w.1.1) heq
          · exact congrArg
              (fun w : (((xi → alpha) × (mu → alpha)) × (upsilon → alpha)) ↦ w.2) heq
        exact hAB (congrArg (fun r ↦ middleSubspace r.1 U r.2) hpq) }

/-- The covered set of the common-block tiling is exactly the layer obtained
by taking its support times the point set of the template. -/
theorem image_covered_commonBlockTiling
    (S : Finset ((xi → alpha) × (upsilon → alpha)))
    (U : Subspace eta alpha mu) :
    (commonBlockTiling S U).covered.map splitMiddleWord.toEmbedding =
      commonBlockLayer S (subspacePoints U) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_map.mp hz
    obtain ⟨V, hV, hwV⟩ := ((commonBlockTiling S U).mem_covered w).mp hw
    obtain ⟨p, hpS, hpV⟩ := Finset.mem_image.mp hV
    subst V
    rw [mem_subspacePoints] at hwV
    obtain ⟨a, rfl⟩ := hwV
    have hz : z = ((p.1, U a), p.2) := hwz.symm
    subst z
    change ((p.1, U a), p.2) ∈ commonBlockLayer S (subspacePoints U)
    exact (mem_commonBlockLayer S (subspacePoints U) _).mpr
      ⟨hpS, by simp⟩
  · intro hz
    have hz' := (mem_commonBlockLayer S (subspacePoints U) z).mp hz
    rw [mem_subspacePoints] at hz'
    obtain ⟨b, hb⟩ := hz'.2
    apply Finset.mem_map.mpr
    refine ⟨middleSubspace z.1.1 U z.2 b, ?_, ?_⟩
    swap
    · change splitMiddleWord (middleSubspace z.1.1 U z.2 b) = z
      rw [splitMiddleWord_middleSubspace_apply]
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · exact hb
      · rfl
    apply ((commonBlockTiling S U).mem_covered _).2
    refine ⟨middleSubspace z.1.1 U z.2, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(z.1.1, z.2), hz'.1, rfl⟩
    · simp

end MiddleSubspaces

/-- If the old-alphabet restriction of a subspace lies in an insensitive set,
then its entire parameter cube lies in that set. -/
theorem subspacePoints_subset_of_restricted_of_isLastInsensitive
    {k m n : ℕ} (i : Fin k) (D : Finset (Word (k + 1) n))
    (hD : IsLastInsensitive i (D : Set (Word (k + 1) n)))
    (U : Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (hU : ∀ x : Word k m, U (liftWord x) ∈ D) :
    subspacePoints U ⊆ D := by
  intro z hz
  rw [mem_subspacePoints] at hz
  obtain ⟨y, rfl⟩ := hz
  have heq : LastEquivalent i (U (liftWord (endpoint i y))) (U y) := by
    rw [LastEquivalent]
    funext r
    cases hr : U.idxFun r with
    | inl a =>
        simp [replaceLast, Subspace.coe_apply, hr]
    | inr e =>
        simp [replaceLast, Subspace.coe_apply, hr, liftWord,
          castSucc_endpoint]
  exact (hD _ _ heq).mp (hU (endpoint i y))

/-- The restricted multidimensional theorem extracts a full tile from every
dense insensitive set. -/
theorem FiniteRestrictedMDHJ.exists_subspacePoints_subset_of_insensitive
    {k d : ℕ} (hMDHJ : FiniteRestrictedMDHJ k d)
    (beta : ℝ) (hbeta : 0 < beta) :
    ∃ n : ℕ, ∀ (i : Fin k) (D : Finset (Word (k + 1) n)),
      IsLastInsensitive i (D : Set (Word (k + 1) n)) →
      beta ≤ density D →
      ∃ U : Subspace (Fin d) (Fin (k + 1)) (Fin n),
        subspacePoints U ⊆ D := by
  obtain ⟨n, hn⟩ := hMDHJ beta hbeta
  refine ⟨n, ?_⟩
  intro i D hD hden
  obtain ⟨U, hU⟩ := (containsRestrictedSubspace_iff d).mp (hn D hden)
  exact ⟨U, subspacePoints_subset_of_restricted_of_isLastInsensitive i D hD U hU⟩

section CommonBlock

variable {P : Type*} [Fintype P] [Nonempty P]

/-- The one-step extraction in the greedy tiling algorithm.  If a set in a
product cube has insensitive block fibres and density greater than `2 * beta`,
then a positive-density set of outside coordinates admits one and the same
block subspace.  Pigeonholing the common template is what makes the union of
the resulting translates insensitive in the still-unused coordinates. -/
theorem exists_common_block_subspace
    {k d M : ℕ} (i : Fin k) (beta : ℝ) (hbeta : 0 < beta)
    (hblock : ∀ A : Finset (Word (k + 1) M),
      beta ≤ density A → ContainsRestrictedSubspace d
        (A : Set (Word (k + 1) M)))
    (D : Finset (P × Word (k + 1) M))
    (hD : ∀ p : P, IsLastInsensitive i
      (fiber D p : Set (Word (k + 1) M)))
    (hden : 2 * beta ≤ density D) :
    ∃ (U : Subspace (Fin d) (Fin (k + 1)) (Fin M)) (S : Finset P),
      beta / Fintype.card (Subspace (Fin d) (Fin (k + 1)) (Fin M)) ≤
        density S ∧
      ∀ p ∈ S, subspacePoints U ⊆ fiber D p := by
  classical
  let f : P → ℝ := fun p ↦ density (fiber D p)
  let T : Finset P := superlevel f beta
  have havg : 2 * beta ≤ average f := by
    rw [show average f = density D by
      simpa only [f] using (density_eq_average_fiber D).symm]
    exact hden
  have hTden : beta ≤ density T := by
    have hhalf := half_le_density_superlevel f (δ := 2 * beta)
      (by positivity) havg (fun p ↦ density_le_one (fiber D p))
    simpa only [T, show (2 * beta) / 2 = beta by ring] using hhalf
  have hTpos : 0 < density T := hbeta.trans_le hTden
  have hTne : T.Nonempty := (density_pos T).mp hTpos
  obtain ⟨p₀, hp₀⟩ := hTne
  have hex (p : P) (hp : p ∈ T) :
      ∃ U : Subspace (Fin d) (Fin (k + 1)) (Fin M),
        subspacePoints U ⊆ fiber D p := by
    have hpden : beta ≤ density (fiber D p) := by
      exact (mem_superlevel f beta p).mp hp
    obtain ⟨U, hU⟩ := (containsRestrictedSubspace_iff d).mp
      (hblock (fiber D p) hpden)
    exact ⟨U, subspacePoints_subset_of_restricted_of_isLastInsensitive
      i (fiber D p) (hD p) U hU⟩
  obtain ⟨U₀, hU₀⟩ := hex p₀ hp₀
  letI : Nonempty (Subspace (Fin d) (Fin (k + 1)) (Fin M)) := ⟨U₀⟩
  have hall : ∀ p : P, ∃ U : Subspace (Fin d) (Fin (k + 1)) (Fin M),
      p ∈ T → subspacePoints U ⊆ fiber D p := by
    intro p
    by_cases hp : p ∈ T
    · obtain ⟨U, hU⟩ := hex p hp
      exact ⟨U, fun _ ↦ hU⟩
    · exact ⟨U₀, fun hp' ↦ (hp hp').elim⟩
  choose selected hselected using hall
  obtain ⟨U, hUden⟩ := exists_dense_colorClass T selected
  let S : Finset P := colorClass T selected U
  refine ⟨U, S, ?_, ?_⟩
  · exact (div_le_div_of_nonneg_right hTden (by positivity)).trans hUden
  · intro p hp
    have hp' := (mem_colorClass T selected U p).mp hp
    rw [← hp'.2]
    exact hselected p hp'.1

end CommonBlock

section FreshBlockInvariant

variable {X B Y : Type*} [Fintype X] [Fintype B] [Fintype Y]
  [DecidableEq X] [DecidableEq B] [DecidableEq Y]

/-- Coordinate-type-polymorphic version of `LastEquivalent`. -/
def LastEquivalentOn {k : ℕ} (i : Fin k) {I : Type*}
    (x y : I → Fin (k + 1)) : Prop :=
  (fun r ↦ replaceLastLetter i (x r)) =
    (fun r ↦ replaceLastLetter i (y r))

@[refl] theorem LastEquivalentOn.refl {k : ℕ} (i : Fin k)
    {I : Type*} (x : I → Fin (k + 1)) : LastEquivalentOn i x x := rfl

theorem lastEquivalentOn_fin_iff {k n : ℕ} (i : Fin k)
    (x y : Word (k + 1) n) :
    LastEquivalentOn i x y ↔ LastEquivalent i x y := Iff.rfl

/-- A finite set is constant on the classes of a relation.  The fresh-block
argument uses this with `(i,last)`-equivalence, first on a product of unused
coordinates and then on the unused coordinates alone. -/
def IsRelationInsensitive (r : X → X → Prop) (C : Finset X) : Prop :=
  ∀ x x', r x x' → (x ∈ C ↔ x' ∈ C)

/-- Product of two equivalence relations, used for an unused prefix followed
by the current fresh block. -/
def ProductRelation (rX : X → X → Prop) (rB : B → B → Prop) :
    X × B → X × B → Prop :=
  fun z z' ↦ rX z.1 z'.1 ∧ rB z.2 z'.2

/-- Splitting a word across a sum of coordinate types identifies generic
last-equivalence with the product of the two last-equivalences. -/
theorem lastEquivalentOn_sum_iff {k : ℕ} (i : Fin k)
    {I J : Type*} (x y : (I ⊕ J) → Fin (k + 1)) :
    LastEquivalentOn i x y ↔
      ProductRelation (LastEquivalentOn (I := I) i)
        (LastEquivalentOn (I := J) i)
        (Equiv.sumArrowEquivProdArrow I J (Fin (k + 1)) x)
        (Equiv.sumArrowEquivProdArrow I J (Fin (k + 1)) y) := by
  constructor
  · intro h
    constructor <;> funext r
    · exact congrFun h (Sum.inl r)
    · exact congrFun h (Sum.inr r)
  · rintro ⟨hI, hJ⟩
    funext r
    cases r with
    | inl r => exact congrFun hI r
    | inr r => exact congrFun hJ r

/-- Freeze the already used suffix of a three-part word. -/
noncomputable def prefixSection (R : Finset ((X × B) × Y)) (y : Y) :
    Finset (X × B) := by
  classical
  exact Finset.univ.filter fun z ↦ (z, y) ∈ R

/-- Freeze the unused prefix and used suffix, leaving the current block. -/
noncomputable def middleFiber (R : Finset ((X × B) × Y))
    (x : X) (y : Y) : Finset B := by
  classical
  exact Finset.univ.filter fun b ↦ ((x, b), y) ∈ R

/-- Outside coordinates on which every point of the common block template
is still present in the remainder. -/
noncomputable def commonBlockSupport (R : Finset ((X × B) × Y))
    (V : Finset B) : Finset (X × Y) := by
  classical
  exact Finset.univ.filter fun p ↦ ∀ b ∈ V, ((p.1, b), p.2) ∈ R

/-- A support fibre in the coordinates which remain unused. -/
noncomputable def supportFiber (S : Finset (X × Y)) (y : Y) : Finset X := by
  classical
  exact Finset.univ.filter fun x ↦ (x, y) ∈ S

/-- A fibre of the remainder after both the current block and the used suffix
have been frozen. -/
noncomputable def futureFiber (R : Finset ((X × B) × Y))
    (b : B) (y : Y) : Finset X := by
  classical
  exact Finset.univ.filter fun x ↦ ((x, b), y) ∈ R

@[simp] theorem mem_prefixSection (R : Finset ((X × B) × Y))
    (y : Y) (z : X × B) : z ∈ prefixSection R y ↔ (z, y) ∈ R := by
  classical
  simp [prefixSection]

@[simp] theorem mem_middleFiber (R : Finset ((X × B) × Y))
    (x : X) (y : Y) (b : B) : b ∈ middleFiber R x y ↔ ((x, b), y) ∈ R := by
  classical
  simp [middleFiber]

@[simp] theorem mem_commonBlockSupport (R : Finset ((X × B) × Y))
    (V : Finset B) (p : X × Y) :
    p ∈ commonBlockSupport R V ↔ ∀ b ∈ V, ((p.1, b), p.2) ∈ R := by
  classical
  simp [commonBlockSupport]

@[simp] theorem mem_supportFiber (S : Finset (X × Y))
    (y : Y) (x : X) : x ∈ supportFiber S y ↔ (x, y) ∈ S := by
  classical
  simp [supportFiber]

@[simp] theorem mem_futureFiber (R : Finset ((X × B) × Y))
    (b : B) (y : Y) (x : X) : x ∈ futureFiber R b y ↔ ((x, b), y) ∈ R := by
  classical
  simp [futureFiber]

theorem commonBlockLayer_subset (R : Finset ((X × B) × Y))
    (V : Finset B) :
    commonBlockLayer (commonBlockSupport R V) V ⊆ R := by
  intro z hz
  have hz' := (mem_commonBlockLayer _ _ _).mp hz
  exact (mem_commonBlockSupport R V (z.1.1, z.2)).mp hz'.1 z.1.2 hz'.2

/-- Joint insensitivity on unused coordinates and the current block implies
insensitivity of every current-block fibre. -/
theorem IsRelationInsensitive.middleFiber
    (rX : X → X → Prop) (rB : B → B → Prop)
    (hreflX : Reflexive rX) (R : Finset ((X × B) × Y))
    (hR : ∀ y, IsRelationInsensitive (ProductRelation rX rB)
      (prefixSection R y)) (x : X) (y : Y) :
    IsRelationInsensitive rB (middleFiber R x y) := by
  intro b b' hbb'
  simpa only [mem_middleFiber, ← mem_prefixSection] using
    hR y (x, b) (x, b') ⟨hreflX x, hbb'⟩

/-- The set of unused prefixes supporting a fixed common block template is
insensitive. -/
theorem IsRelationInsensitive.supportFiber
    (rX : X → X → Prop) (rB : B → B → Prop)
    (hreflB : Reflexive rB) (R : Finset ((X × B) × Y))
    (hR : ∀ y, IsRelationInsensitive (ProductRelation rX rB)
      (prefixSection R y)) (V : Finset B) (y : Y) :
    IsRelationInsensitive rX (supportFiber (commonBlockSupport R V) y) := by
  intro x x' hxx'
  simp only [mem_supportFiber, mem_commonBlockSupport]
  constructor
  · intro hx b hb
    have hmem : (x, b) ∈ prefixSection R y := by simpa using hx b hb
    have := (hR y (x, b) (x', b) ⟨hxx', hreflB b⟩).mp hmem
    simpa using this
  · intro hx b hb
    have hmem : (x', b) ∈ prefixSection R y := by simpa using hx b hb
    have := (hR y (x, b) (x', b) ⟨hxx', hreflB b⟩).mpr hmem
    simpa using this

/-- Before subtraction, every future fibre is insensitive. -/
theorem IsRelationInsensitive.futureFiber
    (rX : X → X → Prop) (rB : B → B → Prop)
    (hreflB : Reflexive rB) (R : Finset ((X × B) × Y))
    (hR : ∀ y, IsRelationInsensitive (ProductRelation rX rB)
      (prefixSection R y)) (b : B) (y : Y) :
    IsRelationInsensitive rX (futureFiber R b y) := by
  intro x x' hxx'
  simpa only [mem_futureFiber, ← mem_prefixSection] using
    hR y (x, b) (x', b) ⟨hxx', hreflB b⟩

/-- Fresh-block preservation: after all translates of the common template
are removed, every fibre over the enlarged used suffix is still insensitive
in all coordinates which remain unused.  This is the precise invariant used
at the next greedy stage. -/
theorem IsRelationInsensitive.residual_futureFiber
    (rX : X → X → Prop) (rB : B → B → Prop)
    (hreflB : Reflexive rB) (R : Finset ((X × B) × Y))
    (hR : ∀ y, IsRelationInsensitive (ProductRelation rX rB)
      (prefixSection R y)) (V : Finset B) (b : B) (y : Y) :
    IsRelationInsensitive rX
      (Erdos171.futureFiber
        (R \ commonBlockLayer (commonBlockSupport R V) V) b y) := by
  have hold := IsRelationInsensitive.futureFiber rX rB hreflB R hR b y
  have hsupp := IsRelationInsensitive.supportFiber rX rB hreflB R hR V y
  intro x x' hxx'
  simp only [mem_futureFiber, Finset.mem_sdiff, mem_commonBlockLayer,
    mem_commonBlockSupport]
  have hold' : (((x, b), y) ∈ R ↔ ((x', b), y) ∈ R) := by
    simpa only [mem_futureFiber] using hold x x' hxx'
  have hsupp' :
      ((∀ c ∈ V, ((x, c), y) ∈ R) ↔
        ∀ c ∈ V, ((x', c), y) ∈ R) := by
    simpa only [mem_supportFiber, mem_commonBlockSupport] using
      hsupp x x' hxx'
  exact and_congr hold' (not_congr (and_congr hsupp' Iff.rfl))

end FreshBlockInvariant

section CommonFreshBlock

variable {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
  [DecidableEq X] [DecidableEq Y]

/-- Reassociate the three blocks so that the current block is the fibre
coordinate used by `exists_common_block_subspace`. -/
def outsideMiddleEquiv (B : Type*) : ((X × B) × Y) ≃ ((X × Y) × B) where
  toFun z := ((z.1.1, z.2), z.1.2)
  invFun z := ((z.1.1, z.2), z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The complete one-step form used in DKT Lemma 12.  It selects a common
subspace template in the current coordinate block, takes its full support,
and removes all corresponding translates.  The removed layer has a uniform
positive density, lies in the old remainder, and the new remainder satisfies
the fresh-block invariant. -/
theorem exists_common_block_layer
    {k d M : ℕ} (i : Fin k) (beta : ℝ) (hbeta : 0 < beta)
    (rX : X → X → Prop) (hreflX : Reflexive rX)
    (hblock : ∀ A : Finset (Word (k + 1) M),
      beta ≤ density A → ContainsRestrictedSubspace d
        (A : Set (Word (k + 1) M)))
    (R : Finset ((X × Word (k + 1) M) × Y))
    (hR : ∀ y, IsRelationInsensitive
      (ProductRelation rX (LastEquivalent i)) (prefixSection R y))
    (hden : 2 * beta ≤ density R) :
    ∃ U : Subspace (Fin d) (Fin (k + 1)) (Fin M),
      let S := commonBlockSupport R (subspacePoints U)
      let L := commonBlockLayer S (subspacePoints U)
      beta / Fintype.card (Subspace (Fin d) (Fin (k + 1)) (Fin M)) ≤
          density S ∧
        L ⊆ R ∧
        beta / Fintype.card (Subspace (Fin d) (Fin (k + 1)) (Fin M)) *
            density (subspacePoints U) ≤ density L ∧
        ∀ b y, IsRelationInsensitive rX (futureFiber (R \ L) b y) := by
  classical
  let e := outsideMiddleEquiv (X := X) (Y := Y) (Word (k + 1) M)
  let D : Finset ((X × Y) × Word (k + 1) M) := R.map e.toEmbedding
  have hDden : density D = density R := by
    simpa [D, e] using density_map_equiv e R
  have hfiber (p : X × Y) : fiber D p = middleFiber R p.1 p.2 := by
    ext b
    simp [D, e, outsideMiddleEquiv]
  have hDins : ∀ p : X × Y,
      IsLastInsensitive i (fiber D p : Set (Word (k + 1) M)) := by
    intro p
    rw [hfiber]
    exact IsRelationInsensitive.middleFiber rX (LastEquivalent i) hreflX R hR p.1 p.2
  obtain ⟨U, S₀, hS₀den, hS₀⟩ := exists_common_block_subspace
    i beta hbeta hblock D hDins (by simpa only [hDden] using hden)
  let V : Finset (Word (k + 1) M) := subspacePoints U
  let S : Finset (X × Y) := commonBlockSupport R V
  let L : Finset ((X × Word (k + 1) M) × Y) := commonBlockLayer S V
  have hS₀S : S₀ ⊆ S := by
    intro p hp
    rw [show S = commonBlockSupport R V by rfl, mem_commonBlockSupport]
    intro b hb
    have hb' : b ∈ fiber D p := hS₀ p hp (by simpa [V] using hb)
    simpa [hfiber p] using hb'
  have hSden :
      beta / Fintype.card (Subspace (Fin d) (Fin (k + 1)) (Fin M)) ≤
        density S := hS₀den.trans (density_mono hS₀S)
  have hLsub : L ⊆ R := by
    simpa [L, S] using commonBlockLayer_subset R V
  have hLprod :
      L = (S.product V).map e.symm.toEmbedding := by
    ext z
    simp [L, commonBlockLayer, e, outsideMiddleEquiv]
  have hLden : density L = density S * density V := by
    rw [hLprod, density_map_equiv]
    exact density_product S V
  refine ⟨U, ?_⟩
  dsimp only
  refine ⟨hSden, hLsub, ?_, ?_⟩
  · rw [hLden]
    exact mul_le_mul_of_nonneg_right hSden (density_nonneg V)
  · intro b y
    exact IsRelationInsensitive.residual_futureFiber rX (LastEquivalent i)
      (LastEquivalent.refl i) R hR V b y

end CommonFreshBlock

section GeometricFreshBlockStep

variable {xi upsilon : Type*}

/-- Geometric one-step producer: the common layer returned by
`exists_common_block_layer` is realized as an actual `SubspaceTiling` in the
three-block word cube. -/
theorem exists_common_block_tiling_step
    {k d M : ℕ}
    [Fintype (xi → Fin (k + 1))] [Nonempty (xi → Fin (k + 1))]
    [Fintype (upsilon → Fin (k + 1))] [Nonempty (upsilon → Fin (k + 1))]
    [DecidableEq (xi → Fin (k + 1))]
    [DecidableEq (upsilon → Fin (k + 1))]
    [Fintype (((xi ⊕ Fin M) ⊕ upsilon) → Fin (k + 1))]
    [DecidableEq (((xi ⊕ Fin M) ⊕ upsilon) → Fin (k + 1))]
    (i : Fin k) (beta : ℝ) (hbeta : 0 < beta)
    (rX : (xi → Fin (k + 1)) → (xi → Fin (k + 1)) → Prop)
    (hreflX : Reflexive rX)
    (hblock : ∀ A : Finset (Word (k + 1) M),
      beta ≤ density A → ContainsRestrictedSubspace d
        (A : Set (Word (k + 1) M)))
    (R : Finset (((xi ⊕ Fin M) ⊕ upsilon) → Fin (k + 1)))
    (hR : ∀ y, IsRelationInsensitive
      (ProductRelation rX (LastEquivalent i))
      (prefixSection (R.map splitMiddleWord.toEmbedding) y))
    (hden : 2 * beta ≤ density R) :
    ∃ (U : Subspace (Fin d) (Fin (k + 1)) (Fin M))
      (T : SubspaceTiling (Fin d) (Fin (k + 1)) ((xi ⊕ Fin M) ⊕ upsilon)),
      T.IsContainedIn R ∧
      beta / Fintype.card
          (Subspace (Fin d) (Fin (k + 1)) (Fin M)) *
          density (subspacePoints U) ≤
        density T.covered ∧
      ∀ b y, IsRelationInsensitive rX
        (futureFiber
          (R.map splitMiddleWord.toEmbedding \ T.covered.map splitMiddleWord.toEmbedding)
          b y) := by
  classical
  let D := R.map splitMiddleWord.toEmbedding
  have hDden : density D = density R := by
    simpa [D] using density_map_equiv
      (splitMiddleWord (xi := xi) (mu := Fin M) (upsilon := upsilon)
        (alpha := Fin (k + 1))) R
  obtain ⟨U, hSden, hLsub, hLden, hres⟩ := exists_common_block_layer
    i beta hbeta rX hreflX hblock D hR (by simpa only [hDden] using hden)
  let S := commonBlockSupport D (subspacePoints U)
  let T : SubspaceTiling (Fin d) (Fin (k + 1)) ((xi ⊕ Fin M) ⊕ upsilon) :=
    commonBlockTiling S U
  have hcoverImage :
      T.covered.map splitMiddleWord.toEmbedding =
        commonBlockLayer S (subspacePoints U) := by
    exact image_covered_commonBlockTiling S U
  have hTsub : T.IsContainedIn R := by
    rw [← T.covered_subset_iff]
    intro x hx
    have hxL : splitMiddleWord x ∈ commonBlockLayer S (subspacePoints U) := by
      rw [← hcoverImage]
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    have hxD : splitMiddleWord x ∈ D := hLsub hxL
    simpa [D] using hxD
  have hTden :
      beta / Fintype.card
          (Subspace (Fin d) (Fin (k + 1)) (Fin M)) *
          density (subspacePoints U) ≤ density T.covered := by
    calc
      _ ≤ density (commonBlockLayer S (subspacePoints U)) := hLden
      _ = density (T.covered.map splitMiddleWord.toEmbedding) := by rw [hcoverImage]
      _ = density T.covered := density_map_equiv splitMiddleWord T.covered
  refine ⟨U, T, hTsub, hTden, ?_⟩
  intro b y
  simpa only [D, T, hcoverImage] using hres b y

end GeometricFreshBlockStep

section BlockRecursionCoordinates

/-- Coordinates in the blocks which have not yet been processed. -/
abbrev UnusedBlockCoord (M : ℕ) : ℕ → Type
  | 0 => Fin 0
  | r + 1 => UnusedBlockCoord M r ⊕ Fin M

/-- The recursive unused-block coordinate type is finite. -/
@[instance_reducible] noncomputable def unusedBlockCoordFintype (M : ℕ) :
    ∀ r, Fintype (UnusedBlockCoord M r)
  | 0 => inferInstanceAs (Fintype (Fin 0))
  | r + 1 => by
      letI := unusedBlockCoordFintype M r
      exact inferInstanceAs (Fintype (UnusedBlockCoord M r ⊕ Fin M))

/-- Decidable equality on the recursive unused-block coordinate type. -/
@[instance_reducible] def unusedBlockCoordDecidableEq (M : ℕ) :
    ∀ r, DecidableEq (UnusedBlockCoord M r)
  | 0 => inferInstanceAs (DecidableEq (Fin 0))
  | r + 1 => by
      letI := unusedBlockCoordDecidableEq M r
      exact inferInstanceAs (DecidableEq (UnusedBlockCoord M r ⊕ Fin M))

attribute [local instance] unusedBlockCoordFintype unusedBlockCoordDecidableEq

@[simp] theorem card_unusedBlockCoord (M s : ℕ) :
    Fintype.card (UnusedBlockCoord M s) = s * M := by
  induction s with
  | zero => simp [UnusedBlockCoord]
  | succ s ih => simp [UnusedBlockCoord, ih, Nat.succ_mul]

/-- Coordinates in the blocks already processed by the greedy algorithm. -/
abbrev UsedBlockCoord (M : ℕ) : ℕ → Type
  | 0 => Fin 0
  | s + 1 => Fin M ⊕ UsedBlockCoord M s

/-- Reassociate one newly processed block from the unused side to the used
side. -/
def blockAssocEquiv (M r s : ℕ) :
    ((UnusedBlockCoord M r ⊕ Fin M) ⊕ UsedBlockCoord M s) ≃
      (UnusedBlockCoord M r ⊕ (Fin M ⊕ UsedBlockCoord M s)) where
  toFun
    | Sum.inl (Sum.inl x) => Sum.inl x
    | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
    | Sum.inr y => Sum.inr (Sum.inr y)
  invFun
    | Sum.inl x => Sum.inl (Sum.inl x)
    | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
    | Sum.inr (Sum.inr y) => Sum.inr y
  left_inv
    | Sum.inl (Sum.inl x) => rfl
    | Sum.inl (Sum.inr b) => rfl
    | Sum.inr y => rfl
  right_inv
    | Sum.inl x => rfl
    | Sum.inr (Sum.inl b) => rfl
    | Sum.inr (Sum.inr y) => rfl

/-- Freeze the used coordinate suffix of a word set. -/
noncomputable def sumSection {A C alpha : Type*}
    [Fintype (A → alpha)] (R : Finset ((A ⊕ C) → alpha))
    (y : C → alpha) : Finset (A → alpha) := by
  classical
  exact Finset.univ.filter fun x ↦ Sum.elim x y ∈ R

@[simp] theorem mem_sumSection {A C alpha : Type*}
    [Fintype (A → alpha)] (R : Finset ((A ⊕ C) → alpha))
    (y : C → alpha) (x : A → alpha) :
    x ∈ sumSection R y ↔ Sum.elim x y ∈ R := by
  classical
  simp [sumSection]

/-- The invariant at a greedy stage: after the used suffix is frozen, the
entire remaining prefix is `(i,last)`-insensitive. -/
def HasFreshBlockInvariant {k : ℕ} (i : Fin k)
    {A C : Type*} [Fintype (A → Fin (k + 1))]
    (R : Finset ((A ⊕ C) → Fin (k + 1))) : Prop :=
  ∀ y, IsRelationInsensitive (LastEquivalentOn (I := A) i) (sumSection R y)

end BlockRecursionCoordinates

section GreedyBlockRun

attribute [local instance] unusedBlockCoordFintype unusedBlockCoordDecidableEq

/-- The uniform density gained at every unsuccessful fresh-block stage. -/
noncomputable def insensitiveBlockGain (k d M : ℕ) (beta : ℝ) : ℝ :=
  beta / Fintype.card (Subspace (Fin d) (Fin (k + 1)) (Fin M)) *
    ((k + 1 : ℝ) ^ d / (k + 1 : ℝ) ^ M)

theorem density_subspacePoints_block {k d M : ℕ}
    (U : Subspace (Fin d) (Fin (k + 1)) (Fin M)) :
    density (subspacePoints U) =
      (k + 1 : ℝ) ^ d / (k + 1 : ℝ) ^ M := by
  simp [density_eq_card_div_card, card_subspacePoints_fin, Word]

/-- The finite fresh-block recursion.  Either it already leaves a remainder
of density below `2 * beta`, or its disjoint tiles occupy at least one copy of
the uniform gain for every available block. -/
theorem exists_tiling_or_density_gain
    {k d M : ℕ} (i : Fin k) (beta : ℝ) (hbeta : 0 < beta)
    (hblock : ∀ A : Finset (Word (k + 1) M),
      beta ≤ density A → ContainsRestrictedSubspace d
        (A : Set (Word (k + 1) M))) :
    ∀ (s : ℕ) {C : Type*} [Fintype C] [DecidableEq C]
      (Q : Finset ((UnusedBlockCoord M s ⊕ C) → Fin (k + 1))),
      HasFreshBlockInvariant i Q →
      ∃ T : SubspaceTiling (Fin d) (Fin (k + 1))
          (UnusedBlockCoord M s ⊕ C),
        T.IsContainedIn Q ∧
          (density (Q \ T.covered) < 2 * beta ∨
            (s : ℝ) * insensitiveBlockGain k d M beta ≤ density T.covered) := by
  intro s
  induction s with
  | zero =>
      intro C _inst _dec Q hQ
      refine ⟨SubspaceTiling.empty, ?_, Or.inr ?_⟩
      · intro U hU
        simp at hU
      · simp [insensitiveBlockGain]
  | succ s ih =>
      intro C _inst _dec Q hQ
      by_cases hsmall : density Q < 2 * beta
      · refine ⟨SubspaceTiling.empty, ?_, Or.inl ?_⟩
        · intro U hU
          simp at hU
        · simpa only [SubspaceTiling.covered_empty, Finset.sdiff_empty] using hsmall
      let D := Q.map splitMiddleWord.toEmbedding
      have hstepInv : ∀ y, IsRelationInsensitive
          (ProductRelation
            (LastEquivalentOn (I := UnusedBlockCoord M s) i)
            (LastEquivalent i)) (prefixSection D y) := by
        intro y p p' hpp'
        let x : (UnusedBlockCoord M s ⊕ Fin M) → Fin (k + 1) :=
          Sum.elim p.1 p.2
        let x' : (UnusedBlockCoord M s ⊕ Fin M) → Fin (k + 1) :=
          Sum.elim p'.1 p'.2
        have hxx' : LastEquivalentOn i x x' := by
          apply (lastEquivalentOn_sum_iff i x x').mpr
          exact ⟨hpp'.1, (lastEquivalentOn_fin_iff i p.2 p'.2).mpr hpp'.2⟩
        have hxmem := hQ y x x' hxx'
        have hxmem' : Sum.elim x y ∈ Q ↔ Sum.elim x' y ∈ Q := by
          simpa only [mem_sumSection] using hxmem
        rw [mem_prefixSection, mem_prefixSection]
        have hp : (p, y) ∈ D ↔ Sum.elim x y ∈ Q := by
          simp only [D, mem_map_equiv_toEmbedding]
          rfl
        have hp' : (p', y) ∈ D ↔ Sum.elim x' y ∈ Q := by
          simp only [D, mem_map_equiv_toEmbedding]
          rfl
        exact hp.trans (hxmem'.trans hp'.symm)
      obtain ⟨U, L, hLsub, hLgain, hres⟩ := exists_common_block_tiling_step
        i beta hbeta (LastEquivalentOn (I := UnusedBlockCoord M s) i)
          (LastEquivalentOn.refl i) hblock Q hstepInv (not_lt.mp hsmall)
      let Q₀ := Q \ L.covered
      let e := blockAssocEquiv M s 0
      -- The suffix type is arbitrary; use the same associator with `C`.
      let eC :
          ((UnusedBlockCoord M s ⊕ Fin M) ⊕ C) ≃
            (UnusedBlockCoord M s ⊕ (Fin M ⊕ C)) :=
        { toFun
            | Sum.inl (Sum.inl x) => Sum.inl x
            | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
            | Sum.inr y => Sum.inr (Sum.inr y)
          invFun
            | Sum.inl x => Sum.inl (Sum.inl x)
            | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
            | Sum.inr (Sum.inr y) => Sum.inr y
          left_inv
            | Sum.inl (Sum.inl x) => rfl
            | Sum.inl (Sum.inr b) => rfl
            | Sum.inr y => rfl
          right_inv
            | Sum.inl x => rfl
            | Sum.inr (Sum.inl b) => rfl
            | Sum.inr (Sum.inr y) => rfl }
      let Q' := Q₀.map (SubspaceTiling.ambientWordEquiv eC).toEmbedding
      have hQ'inv : HasFreshBlockInvariant i Q' := by
        intro y' x x' hxx'
        let b : Word (k + 1) M := fun r ↦ y' (Sum.inl r)
        let y : C → Fin (k + 1) := fun r ↦ y' (Sum.inr r)
        have hh := hres b y x x' hxx'
        let ew := SubspaceTiling.ambientWordEquiv
          (alpha := Fin (k + 1)) eC
        have hamb (z : UnusedBlockCoord M s → Fin (k + 1)) :
            ew.symm (Sum.elim z y') = Sum.elim (Sum.elim z b) y := by
          funext q
          rcases q with (q | q)
          · rcases q with q | q <;> rfl
          · rfl
        have hmem (z : UnusedBlockCoord M s → Fin (k + 1)) :
            Sum.elim z y' ∈ Q' ↔
              z ∈ futureFiber
                (D \ L.covered.map splitMiddleWord.toEmbedding) b y := by
          dsimp only [Q']
          rw [mem_map_equiv_toEmbedding, hamb]
          simp only [Q₀, mem_futureFiber, Finset.mem_sdiff, D,
            mem_map_equiv_toEmbedding]
          rfl
        rw [mem_sumSection, mem_sumSection]
        exact (hmem x).trans (hh.trans (hmem x').symm)
      obtain ⟨T', hT'sub, hT'out⟩ := ih (C := Fin M ⊕ C) Q' hQ'inv
      let T₀ := T'.ambientReindex eC.symm
      have hT₀contained : T₀.IsContainedIn Q₀ := by
        change (T'.ambientReindex eC.symm).IsContainedIn Q₀
        rw [SubspaceTiling.ambientReindex_isContainedIn_iff]
        simpa [Q', SubspaceTiling.ambientWordEquiv, Function.comp_def] using hT'sub
      have hT₀sub : T₀.covered ⊆ Q₀ :=
        (T₀.covered_subset_iff Q₀).mpr hT₀contained
      have hdisj : Disjoint L.covered T₀.covered := by
        rw [Finset.disjoint_left]
        intro x hxL hxT
        exact (Finset.mem_sdiff.mp (hT₀sub hxT)).2 hxL
      let T := L.disjointUnion T₀ hdisj
      have hTsub : T.IsContainedIn Q := by
        rw [← T.covered_subset_iff]
        rw [SubspaceTiling.covered_disjointUnion]
        intro x hx
        rcases Finset.mem_union.mp hx with hxL | hxT
        · exact ((L.covered_subset_iff Q).mpr hLsub) hxL
        · exact (Finset.mem_sdiff.mp (hT₀sub hxT)).1
      refine ⟨T, hTsub, ?_⟩
      rcases hT'out with hT'small | hT'gain
      · left
        have heq : density (Q₀ \ T₀.covered) =
            density (Q' \ T'.covered) := by
          have h := SubspaceTiling.density_sdiff_covered_ambientReindex
            T' eC.symm Q₀
          simpa [T₀, Q', SubspaceTiling.ambientWordEquiv,
            Function.comp_def] using h
        have hresEq : Q \ T.covered = Q₀ \ T₀.covered := by
          have hcover : T.covered = L.covered ∪ T₀.covered :=
            SubspaceTiling.covered_disjointUnion L T₀ hdisj
          rw [hcover]
          ext x
          simp only [Q₀, Finset.mem_sdiff, Finset.mem_union]
          tauto
        rw [hresEq, heq]
        exact hT'small
      · right
        have hT₀den : density T₀.covered = density T'.covered := by
          change density (T'.ambientReindex eC.symm).covered = density T'.covered
          rw [SubspaceTiling.covered_ambientReindex]
          exact density_map_equiv
            (SubspaceTiling.ambientWordEquiv eC.symm) T'.covered
        have hinter : L.covered ∩ T₀.covered = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdisj
        have hadd : density T.covered = density L.covered + density T₀.covered := by
          rw [show T.covered = L.covered ∪ T₀.covered by
            exact SubspaceTiling.covered_disjointUnion L T₀ hdisj]
          have hu := density_union_add_density_inter L.covered T₀.covered
          rw [hinter, density_empty] at hu
          linarith
        have hgain' : insensitiveBlockGain k d M beta ≤ density L.covered := by
          simpa [insensitiveBlockGain, density_subspacePoints_block U] using hLgain
        rw [hadd, hT₀den]
        push_cast
        nlinarith

end GreedyBlockRun

section OneInsensitiveTiling

attribute [local instance] unusedBlockCoordFintype unusedBlockCoordDecidableEq

/-- Dodos--Kanellopoulos--Tyros, Lemma 12, with an arbitrary lower bound on
the ambient dimension. -/
theorem FiniteRestrictedMDHJ.exists_oneInsensitiveTilingAt_ge
    {k d : ℕ} (hMDHJ : FiniteRestrictedMDHJ k d)
    {beta : ℝ} (hbeta : 0 < beta) (N : ℕ) :
    ∃ n, N ≤ n ∧ OneInsensitiveTilingAt k d n beta := by
  by_cases htriv : 1 ≤ 2 * beta
  · refine ⟨N, le_rfl, ?_⟩
    intro i D hD hden
    exact (not_lt_of_ge ((density_le_one D).trans htriv) hden).elim
  obtain ⟨M, hMpos, hblock⟩ := hMDHJ.positiveWitness beta hbeta
  have hbeta1 : beta ≤ 1 := by linarith
  obtain ⟨U, hU⟩ := hblock (Finset.univ : Finset (Word (k + 1) M))
    (by rw [density_univ]; exact hbeta1)
  letI : Nonempty (Subspace (Fin d) (Fin (k + 1)) (Fin M)) := ⟨U⟩
  let theta := insensitiveBlockGain k d M beta
  have htheta : 0 < theta := by
    dsimp only [theta, insensitiveBlockGain]
    positivity
  obtain ⟨R₀, hR₀⟩ := exists_nat_gt (1 / theta)
  let R := max R₀ N
  have hR₀R : (R₀ : ℝ) ≤ R := by
    exact_mod_cast Nat.le_max_left R₀ N
  have hRgain₀ : 1 < (R₀ : ℝ) * theta :=
    (div_lt_iff₀ htheta).mp hR₀
  have hRgain : 1 < (R : ℝ) * theta := by
    nlinarith
  have hNRM : N ≤ R * M := by
    have hNR : N ≤ R := Nat.le_max_right R₀ N
    have hRM : R ≤ R * M := by
      nlinarith [hMpos]
    exact hNR.trans hRM
  let I := UnusedBlockCoord M R ⊕ Fin 0
  have hIcard : Fintype.card I = R * M := by
    simp [I]
  let e : I ≃ Fin (R * M) := Fintype.equivFinOfCardEq hIcard
  refine ⟨R * M, hNRM, ?_⟩
  intro i D hD hDden
  let ew := SubspaceTiling.ambientWordEquiv
    (alpha := Fin (k + 1)) e
  let Q : Finset (I → Fin (k + 1)) := D.map ew.symm.toEmbedding
  have hQinv : HasFreshBlockInvariant i Q := by
    intro y x x' hxx'
    rw [mem_sumSection, mem_sumSection]
    have hsum : LastEquivalentOn i (Sum.elim x y) (Sum.elim x' y) :=
      (lastEquivalentOn_sum_iff i _ _).mpr
        ⟨hxx', LastEquivalentOn.refl i y⟩
    have hew : LastEquivalentOn i (ew (Sum.elim x y))
        (ew (Sum.elim x' y)) := by
      funext r
      exact congrFun hsum (e.symm r)
    have hmem := hD (ew (Sum.elim x y)) (ew (Sum.elim x' y))
      ((lastEquivalentOn_fin_iff i _ _).mp hew)
    simpa only [Q, mem_map_equiv_toEmbedding, Equiv.symm_symm,
      Finset.mem_coe] using hmem
  obtain ⟨T, hTsub, hout⟩ := exists_tiling_or_density_gain
    i beta hbeta hblock R (C := Fin 0) Q hQinv
  rcases hout with hsmall | hgain
  · let Tout := T.ambientReindex e
    refine ⟨Tout, ?_, ?_⟩
    · change (T.ambientReindex e).IsContainedIn D
      apply (SubspaceTiling.ambientReindex_isContainedIn_iff T e D).mpr
      simpa only [Q] using hTsub
    · change density (D \ (T.ambientReindex e).covered) < 2 * beta
      rw [SubspaceTiling.density_sdiff_covered_ambientReindex]
      simpa only [Q] using hsmall
  · have hcap := density_le_one T.covered
    exact (not_lt_of_ge hcap (hRgain.trans_le hgain)).elim

end OneInsensitiveTiling

section FiniteGreedyIteration

variable {Omega : Type*} [Fintype Omega]

/-- A process which gains a fixed positive density whenever it has not
terminated must terminate before more than `1 / theta` steps.  The geometric
fresh-block lemmas supply `covered`, `remainder`, and the step inequality. -/
theorem exists_small_remainder_of_density_gain
    (covered remainder : ℕ → Finset Omega) (theta beta : ℝ) (R : ℕ)
    (htheta : 0 < theta) (hR : 1 < (R : ℝ) * theta)
    (hstep : ∀ j < R, ¬ density (remainder j) < 2 * beta →
      density (covered j) + theta ≤ density (covered (j + 1))) :
    ∃ j ≤ R, density (remainder j) < 2 * beta := by
  by_contra hstop
  push_neg at hstop
  have hlower : ∀ j ≤ R, (j : ℝ) * theta ≤ density (covered j) := by
    intro j hj
    induction j with
    | zero =>
        simpa using density_nonneg (covered 0)
    | succ j ih =>
        have hjR : j < R := by omega
        have hgain := hstep j hjR (not_lt.mpr (hstop j (by omega)))
        have hprev := ih (by omega)
        push_cast
        nlinarith
  have hcap := density_le_one (covered R)
  have := hlower R le_rfl
  nlinarith

end FiniteGreedyIteration

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/Binary.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The binary density Hales--Jewett theorem

For the alphabet `Fin 2`, a combinatorial-line-free family is an antichain in
the Boolean lattice.  Sperner's theorem therefore bounds it by the middle
binomial coefficient.  An elementary squared central-binomial estimate then
shows that this bound has density tending to zero.
-/



open Finset Set Function

/-- The support of a binary word: the coordinates carrying the letter `1`. -/
def binarySupport {n : ℕ} (x : Word 2 n) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ x i = 1)

@[simp] theorem mem_binarySupport {n : ℕ} {x : Word 2 n} {i : Fin n} :
    i ∈ binarySupport x ↔ x i = 1 := by
  simp [binarySupport]

theorem binarySupport_injective (n : ℕ) :
    Function.Injective (@binarySupport n) := by
  intro x y h
  funext i
  have hi : (x i = 1) ↔ (y i = 1) := by
    simpa only [mem_binarySupport] using Finset.ext_iff.mp h i
  apply Fin.ext
  omega

theorem binarySupport_subset_iff {n : ℕ} {x y : Word 2 n} :
    binarySupport x ⊆ binarySupport y ↔ ∀ i, x i ≤ y i := by
  constructor
  · intro h i
    have hi : x i = 1 → y i = 1 := by
      simpa only [mem_binarySupport] using @h i
    exact Fin.le_iff_val_le_val.mpr (by omega)
  · intro h i hi
    rw [mem_binarySupport] at hi ⊢
    have := h i
    apply Fin.ext
    omega

/-- Two binary words form an oriented combinatorial line when they are
distinct and coordinatewise ordered. -/
def BinaryLine {n : ℕ} (x y : Word 2 n) : Prop :=
  x ≠ y ∧ ∀ i, x i ≤ y i

theorem binaryLine_iff_support_ssubset {n : ℕ} {x y : Word 2 n} :
    BinaryLine x y ↔ binarySupport x ⊂ binarySupport y := by
  rw [BinaryLine, Finset.ssubset_iff_subset_ne, binarySupport_subset_iff]
  constructor
  · rintro ⟨hne, hle⟩
    exact ⟨hle, fun h ↦ hne ((binarySupport_injective n) h)⟩
  · rintro ⟨hle, hne⟩
    exact ⟨fun h ↦ hne (congrArg binarySupport h), hle⟩

/-- The proper Mathlib combinatorial line determined by an oriented pair of
binary words.  A coordinate is a wildcard exactly where the endpoints differ. -/
def lineOfBinaryLine {n : ℕ} (x y : Word 2 n) (h : BinaryLine x y) :
    Combinatorics.Line (Fin 2) (Fin n) where
  idxFun i := if x i = y i then some (x i) else none
  proper := by
    by_contra! hall
    apply h.1
    funext i
    simpa using hall i

@[simp] theorem lineOfBinaryLine_zero {n : ℕ} (x y : Word 2 n)
    (h : BinaryLine x y) : lineOfBinaryLine x y h 0 = x := by
  funext i
  by_cases hi : x i = y i
  · simp [lineOfBinaryLine, Combinatorics.Line.coe_apply, hi]
  · have hle := h.2 i
    apply Fin.ext
    simp [lineOfBinaryLine, Combinatorics.Line.coe_apply, hi]
    omega

@[simp] theorem lineOfBinaryLine_one {n : ℕ} (x y : Word 2 n)
    (h : BinaryLine x y) : lineOfBinaryLine x y h 1 = y := by
  funext i
  by_cases hi : x i = y i
  · simp [lineOfBinaryLine, Combinatorics.Line.coe_apply, hi]
  · have hle := h.2 i
    apply Fin.ext
    simp [lineOfBinaryLine, Combinatorics.Line.coe_apply, hi]
    omega

/-- An oriented binary pair in a set supplies a proper `Combinatorics.Line`. -/
theorem containsLine_of_binaryLine {n : ℕ} {A : Set (Word 2 n)}
    {x y : Word 2 n} (hx : x ∈ A) (hy : y ∈ A) (hxy : BinaryLine x y) :
    ContainsLine A := by
  refine ⟨lineOfBinaryLine x y hxy, ?_⟩
  rintro _ ⟨a, rfl⟩
  fin_cases a
  · simpa using hx
  · simpa using hy

/-- The endpoints `0` and `1` of every proper binary line form an oriented
binary pair. -/
theorem binaryLine_zero_one (l : Combinatorics.Line (Fin 2) (Fin n)) :
    BinaryLine (l 0) (l 1) := by
  constructor
  · exact l.parameter_injective.ne (by decide)
  · intro i
    cases hi : l.idxFun i with
    | none => simp [Combinatorics.Line.coe_apply, hi]
    | some a => simp [Combinatorics.Line.coe_apply, hi]

theorem antichain_image_binarySupport {n : ℕ} (A : Finset (Word 2 n))
    (hA : ∀ x ∈ A, ∀ y ∈ A, ¬ BinaryLine x y) :
    IsAntichain (· ⊆ ·)
      ((A.image binarySupport : Finset (Finset (Fin n))) : Set (Finset (Fin n))) := by
  intro s hs t ht hne hst
  simp only [Finset.mem_coe, Finset.mem_image] at hs ht
  obtain ⟨x, hxA, rfl⟩ := hs
  obtain ⟨y, hyA, hy⟩ := ht
  subst hy
  apply hA x hxA y hyA
  rw [binaryLine_iff_support_ssubset, Finset.ssubset_iff_subset_ne]
  exact ⟨hst, hne⟩

/-- Sperner's sharp upper bound for a binary line-free family. -/
theorem binary_line_free_card_le_choose {n : ℕ} (A : Finset (Word 2 n))
    (hA : ¬ ContainsLine (A : Set (Word 2 n))) :
    A.card ≤ n.choose (n / 2) := by
  have hpair : ∀ x ∈ A, ∀ y ∈ A, ¬ BinaryLine x y := by
    intro x hx y hy hxy
    exact hA (containsLine_of_binaryLine hx hy hxy)
  have hanti := antichain_image_binarySupport A hpair
  have hs := hanti.sperner
  rw [Finset.card_image_of_injective A (binarySupport_injective n)] at hs
  simpa using hs

/-- A convenient squared estimate for the central binomial coefficient. -/
theorem centralBinom_sq_bound : ∀ m : ℕ,
    (m + 1) * (Nat.centralBinom m) ^ 2 ≤ 16 ^ m := by
  intro m
  induction m with
  | zero => norm_num [Nat.centralBinom]
  | succ m ih =>
      have hrec := Nat.succ_mul_centralBinom_succ m
      have hpoly : (m + 2) * (2 * (2 * m + 1)) ^ 2 ≤ 16 * (m + 1) ^ 3 := by
        nlinarith
      have hmul :
          (m + 2) * (m + 1) ^ 2 * (Nat.centralBinom (m + 1)) ^ 2 ≤
            16 * (m + 1) ^ 2 * 16 ^ m := by
        calc
          (m + 2) * (m + 1) ^ 2 * (Nat.centralBinom (m + 1)) ^ 2
              = (m + 2) * (2 * (2 * m + 1)) ^ 2 * (Nat.centralBinom m) ^ 2 := by
                  have hrec_sq := congrArg (fun z : ℕ ↦ z ^ 2) hrec
                  nlinarith
          _ ≤ 16 * (m + 1) ^ 3 * (Nat.centralBinom m) ^ 2 := by gcongr
          _ = 16 * (m + 1) ^ 2 * ((m + 1) * (Nat.centralBinom m) ^ 2) := by ring
          _ ≤ 16 * (m + 1) ^ 2 * 16 ^ m := by gcongr
      have hpos : 0 < (m + 1) ^ 2 := by positivity
      refine Nat.le_of_mul_le_mul_left ?_ hpos
      rw [pow_succ]
      convert hmul using 1 <;> ring

/-- Uniform (even and odd dimension) squared upper bound for the middle
binomial coefficient. -/
theorem choose_middle_sq_bound (n : ℕ) :
    (n / 2 + 1) * (n.choose (n / 2)) ^ 2 ≤ 2 ^ (2 * n) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · simpa [Nat.centralBinom, pow_mul] using centralBinom_sq_bound m
  · have hchoose : (2 * m + 1).choose m ≤ 2 * Nat.centralBinom m := by
      cases m with
      | zero => norm_num [Nat.centralBinom]
      | succ k =>
          rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 by omega,
            Nat.choose_succ_succ' (2 * (k + 1)) k]
          rw [two_mul]
          simpa [two_mul] using
            Nat.add_le_add (Nat.choose_le_centralBinom k (k + 1))
              (Nat.choose_le_centralBinom (k + 1) (k + 1))
    calc
      ((2 * m + 1) / 2 + 1) * ((2 * m + 1).choose ((2 * m + 1) / 2)) ^ 2
          ≤ (m + 1) * (2 * Nat.centralBinom m) ^ 2 := by
              rw [show (2 * m + 1) / 2 = m by omega]
              exact Nat.mul_le_mul_left (m + 1) (Nat.pow_le_pow_left hchoose 2)
      _ = 4 * ((m + 1) * (Nat.centralBinom m) ^ 2) := by ring
      _ ≤ 4 * 16 ^ m := by gcongr; exact centralBinom_sq_bound m
      _ = 2 ^ (2 * (2 * m + 1)) := by
        rw [show 4 = 2 ^ 2 by norm_num, show 16 = 2 ^ 4 by norm_num,
          ← pow_mul, ← pow_add]
        congr 1
        omega

/-- The density Hales--Jewett theorem for the binary alphabet, for finite
families.  The proof gives the explicit threshold `2 * M` for any natural
`M > (ε²)⁻¹`. -/
theorem exists_containsLine_of_dense_binary_finset (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset (Word 2 n),
      eps * (2 : ℝ) ^ n ≤ A.card → ContainsLine (A : Set (Word 2 n)) := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (eps ^ 2)⁻¹ < M := exists_nat_gt ((eps ^ 2)⁻¹)
  refine ⟨2 * M, ?_⟩
  intro n hn A hdense
  by_contra hfree
  have hcard := binary_line_free_card_le_choose A hfree
  have hcardR : (A.card : ℝ) ≤ n.choose (n / 2) := by exact_mod_cast hcard
  have hdense' : eps * (2 : ℝ) ^ n ≤ n.choose (n / 2) := hdense.trans hcardR
  have hsq : (eps * (2 : ℝ) ^ n) ^ 2 ≤ ((n.choose (n / 2) : ℕ) : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hdense'
  have hbound :
      (((n / 2 + 1 : ℕ) : ℝ) * ((n.choose (n / 2) : ℕ) : ℝ) ^ 2) ≤
        ((2 : ℝ) ^ n) ^ 2 := by
    have hb := choose_middle_sq_bound n
    have hbR :
        (((n / 2 + 1 : ℕ) : ℝ) * ((n.choose (n / 2) : ℕ) : ℝ) ^ 2) ≤
          (2 : ℝ) ^ (2 * n) := by
      exact_mod_cast hb
    simpa [pow_two, ← pow_add, two_mul] using hbR
  have hcombined :
      (((n / 2 + 1 : ℕ) : ℝ) * eps ^ 2) * ((2 : ℝ) ^ n) ^ 2 ≤
        ((2 : ℝ) ^ n) ^ 2 := by
    calc
      (((n / 2 + 1 : ℕ) : ℝ) * eps ^ 2) * ((2 : ℝ) ^ n) ^ 2 =
          ((n / 2 + 1 : ℕ) : ℝ) * (eps * (2 : ℝ) ^ n) ^ 2 := by ring
      _ ≤ ((n / 2 + 1 : ℕ) : ℝ) * ((n.choose (n / 2) : ℕ) : ℝ) ^ 2 := by
        gcongr
      _ ≤ ((2 : ℝ) ^ n) ^ 2 := hbound
  have hcoef : ((n / 2 + 1 : ℕ) : ℝ) * eps ^ 2 ≤ 1 := by
    have hq : 0 < ((2 : ℝ) ^ n) ^ 2 := by positivity
    exact le_of_mul_le_mul_right (by simpa using hcombined) hq
  have hMdiv : M ≤ n / 2 := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hMcast : (M : ℝ) ≤ ((n / 2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast (hMdiv.trans (by omega))
  have hepssq : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hMinv : (eps ^ 2)⁻¹ * eps ^ 2 = 1 := by
    field_simp
  have hlarge : 1 < ((n / 2 + 1 : ℕ) : ℝ) * eps ^ 2 := by
    have := mul_lt_mul_of_pos_right (hM.trans_le hMcast) hepssq
    nlinarith
  exact (not_lt_of_ge hcoef) hlarge

/-- Set-valued form of the binary density Hales--Jewett theorem. -/
theorem exists_containsLine_of_dense_binary (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Set (Word 2 n),
      eps * (2 : ℝ) ^ n ≤ A.ncard → ContainsLine A := by
  obtain ⟨N, hN⟩ := exists_containsLine_of_dense_binary_finset eps heps
  refine ⟨N, ?_⟩
  intro n hn A hdense
  let hfin : A.Finite := Set.toFinite A
  let s := hfin.toFinset
  have hsCard : s.card = A.ncard := by
    exact (Set.ncard_eq_toFinset_card A hfin).symm
  have hsLine : ContainsLine (s : Set (Word 2 n)) :=
    hN n hn s (by simpa [hsCard] using hdense)
  simpa [s, Set.Finite.coe_toFinset] using hsLine

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/BaseCases.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The one-letter base case of density Hales--Jewett

A proper line needs at least one coordinate even when the alphabet has one
letter.  In every positive dimension the cube itself is a singleton, so a
positive-density set contains its unique word and hence contains a line.
-/



open Set

/-- The all-wildcard line over the one-letter alphabet. -/
def oneLetterLine (n : ℕ) (hn : 1 ≤ n) :
    Combinatorics.Line (Fin 1) (Fin n) where
  idxFun _ := none
  proper := ⟨⟨0, hn⟩, rfl⟩

@[simp] theorem oneLetterLine_apply (n : ℕ) (hn : 1 ≤ n) (a : Fin 1) :
    oneLetterLine n hn a = fun _ ↦ 0 := by
  funext i
  simpa [oneLetterLine, Combinatorics.Line.coe_apply] using
    (Subsingleton.elim a (0 : Fin 1))

/-- Every nonempty set in a positive-dimensional one-letter cube contains a
proper combinatorial line. -/
theorem containsLine_one_of_nonempty {n : ℕ} (hn : 1 ≤ n)
    {A : Set (Word 1 n)} (hA : A.Nonempty) : ContainsLine A := by
  obtain ⟨w, hw⟩ := hA
  refine ⟨oneLetterLine n hn, ?_⟩
  rintro _ ⟨a, rfl⟩
  convert hw using 1

/-- Set/cardinality form of the eventual density Hales--Jewett theorem for the
one-letter alphabet.  The exact threshold is `N = 1`. -/
theorem exists_containsLine_of_dense_one (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Set (Word 1 n),
      eps * (1 : ℝ) ^ n ≤ A.ncard → ContainsLine A := by
  refine ⟨1, ?_⟩
  intro n hn A hdense
  have hncardR : 0 < (A.ncard : ℝ) := by
    have hle : eps ≤ (A.ncard : ℝ) := by simpa using hdense
    exact heps.trans_le hle
  have hncard : 0 < A.ncard := by exact_mod_cast hncardR
  exact containsLine_one_of_nonempty hn ((Set.ncard_pos (Set.toFinite A)).mp hncard)

/-- Finset form of the same exact one-letter base case. -/
theorem exists_containsLine_of_dense_one_finset (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset (Word 1 n),
      eps * (1 : ℝ) ^ n ≤ A.card → ContainsLine (A : Set (Word 1 n)) := by
  obtain ⟨N, hN⟩ := exists_containsLine_of_dense_one eps heps
  refine ⟨N, ?_⟩
  intro n hn A hdense
  apply hN n hn (A : Set (Word 1 n))
  simpa only [Set.ncard_coe_finset] using hdense

/-- Predicate-level wrapper for the exact eventual density-Hales--Jewett
framework at alphabet size one. -/
theorem eventualDensityHJ_one : EventualDensityHJ 1 := by
  intro delta hdelta
  refine ⟨1, ?_⟩
  intro n hn A hA
  apply containsLine_one_of_nonempty hn
  exact (density_pos A).mp (hdelta.trans_le hA)

/-- Predicate-level wrapper for the binary Sperner proof. -/
theorem eventualDensityHJ_two : EventualDensityHJ 2 := by
  intro delta hdelta
  obtain ⟨N, hN⟩ := exists_containsLine_of_dense_binary_finset delta hdelta
  refine ⟨N, ?_⟩
  intro n hn A hA
  apply hN n hn A
  have hden : delta ≤ (A.card : ℝ) / (2 : ℝ) ^ n := by
    simpa [density, card_word] using hA
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mp hden

/-- One-witness density Hales--Jewett for the one-letter alphabet. -/
theorem finiteDensityHJ_one : FiniteDensityHJ 1 := by
  intro delta hdelta
  obtain ⟨n₀, hn₀⟩ := eventualDensityHJ_one delta hdelta
  exact ⟨n₀, hn₀ n₀ le_rfl⟩

/-- One-witness density Hales--Jewett for the binary alphabet. -/
theorem finiteDensityHJ_two : FiniteDensityHJ 2 := by
  intro delta hdelta
  obtain ⟨n₀, hn₀⟩ := eventualDensityHJ_two delta hdelta
  exact ⟨n₀, hn₀ n₀ le_rfl⟩

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/Packaging.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Public statement of Erdős Problem 171

This file connects the internal real-valued density formulation of density
Hales--Jewett to the cardinality inequality in the statement of Erdős Problem
171.  It also spells out Mathlib's combinatorial-line structure coordinate by
coordinate: every coordinate is either the alphabet parameter or a constant,
and at least one coordinate is the parameter.

No density-Hales--Jewett result is assumed globally here.  The packaging
theorems take `EventualDensityHJ t` as an explicit hypothesis.
-/



open Set

/-- A parametrized family of words has the coordinate pattern of a proper
combinatorial line: every coordinate is either the parameter itself or is
constant, and at least one coordinate is the parameter. -/
def IsCoordinateLine {t n : ℕ} (p : Fin t → Word t n) : Prop :=
  (∀ j : Fin n,
      (∀ a : Fin t, p a j = a) ∨
        ∃ c : Fin t, ∀ a : Fin t, p a j = c) ∧
    ∃ j : Fin n, ∀ a : Fin t, p a j = a

/-- The wildcard coordinate makes a coordinatewise line parametrization
injective, so its range really consists of `t` parametrized points. -/
theorem IsCoordinateLine.injective {t n : ℕ} {p : Fin t → Word t n}
    (hp : IsCoordinateLine p) : Function.Injective p := by
  intro a b hab
  obtain ⟨j, hj⟩ := hp.2
  have hcoord := congrFun hab j
  simpa only [hj a, hj b] using hcoord

/-- A coordinatewise line over `Fin t` has exactly `t` points. -/
theorem IsCoordinateLine.ncard_range {t n : ℕ} {p : Fin t → Word t n}
    (hp : IsCoordinateLine p) : Set.ncard (Set.range p) = t := by
  rw [Set.ncard_range_of_injective hp.injective]
  simp

/-- Evaluation of a Mathlib combinatorial line has the coordinatewise form
used in the statement of Erdős Problem 171. -/
theorem isCoordinateLine_of_line {t n : ℕ}
    (l : Combinatorics.Line (Fin t) (Fin n)) : IsCoordinateLine l := by
  constructor
  · intro j
    cases hj : l.idxFun j with
    | none =>
        exact Or.inl fun a ↦ l.apply_none a j hj
    | some c =>
        exact Or.inr ⟨c, fun _ ↦ l.apply_some hj⟩
  · obtain ⟨j, hj⟩ := l.proper
    exact ⟨j, fun a ↦ l.apply_none a j hj⟩

/-- A coordinatewise line parametrization determines Mathlib's proper
combinatorial line with exactly the same evaluation map. -/
theorem exists_line_eq_of_isCoordinateLine {t n : ℕ} {p : Fin t → Word t n}
    (hp : IsCoordinateLine p) :
    ∃ l : Combinatorics.Line (Fin t) (Fin n), (⇑l) = p := by
  classical
  let idx : Fin n → Option (Fin t) := fun j ↦
    if h : ∀ a : Fin t, p a j = a then none
    else some (Classical.choose ((hp.1 j).resolve_left h))
  have hproper : ∃ j, idx j = none := by
    obtain ⟨j, hj⟩ := hp.2
    exact ⟨j, by simp [idx, hj]⟩
  let l : Combinatorics.Line (Fin t) (Fin n) :=
    { idxFun := idx
      proper := hproper }
  refine ⟨l, ?_⟩
  funext a j
  by_cases hj : ∀ b : Fin t, p b j = b
  · simp [l, idx, hj, Combinatorics.Line.coe_apply]
  · have hc := Classical.choose_spec ((hp.1 j).resolve_left hj)
    simpa [l, idx, hj, Combinatorics.Line.coe_apply] using (hc a).symm

/-- Coordinatewise characterization of `ContainsLine`, including membership
of every parametrized word in the ambient set. -/
theorem containsLine_iff_exists_coordinateLine {t n : ℕ}
    {A : Set (Word t n)} :
    ContainsLine A ↔
      ∃ p : Fin t → Word t n,
        IsCoordinateLine p ∧ ∀ a : Fin t, p a ∈ A := by
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l, isCoordinateLine_of_line l, fun a ↦ hl ⟨a, rfl⟩⟩
  · rintro ⟨p, hp, hA⟩
    obtain ⟨l, rfl⟩ := exists_line_eq_of_isCoordinateLine hp
    exact (containsLine_iff (A := A)).2 ⟨l, hA⟩

/-- Finset version of the coordinatewise characterization of
`ContainsLine`. -/
theorem containsLine_coe_finset_iff_exists_coordinateLine {t n : ℕ}
    {A : Finset (Word t n)} :
    ContainsLine (A : Set (Word t n)) ↔
      ∃ p : Fin t → Word t n,
        IsCoordinateLine p ∧ ∀ a : Fin t, p a ∈ A := by
  simpa only [Finset.mem_coe] using
    (containsLine_iff_exists_coordinateLine
      (A := (A : Set (Word t n))))

/-- The cardinality formulation of the eventual density Hales--Jewett
property for the alphabet `Fin t`.  This is the literal quantitative
hypothesis in Erdős Problem 171. -/
def CardinalityEventualDensityHJ (t : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset (Word t N),
      ε * (t : ℝ) ^ N ≤ (A.card : ℝ) →
        ContainsLine (A : Set (Word t N))

/-- For a nonempty alphabet, the real-valued density formulation implies the
literal cardinality formulation in Erdős Problem 171. -/
theorem EventualDensityHJ.cardinality {t : ℕ} (ht : 0 < t)
    (h : EventualDensityHJ t) : CardinalityEventualDensityHJ t := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := h ε hε
  refine ⟨N₀, ?_⟩
  intro N hN A hcard
  apply hN₀ N hN A
  rw [density_eq_card_div_card, card_word]
  simpa only [Nat.cast_pow] using
    (le_div_iff₀ (by positivity : (0 : ℝ) < (t : ℝ) ^ N)).2 hcard

/-- For a nonempty alphabet, the cardinality formulation also implies the
real-valued density formulation. -/
theorem CardinalityEventualDensityHJ.eventual {t : ℕ} (ht : 0 < t)
    (h : CardinalityEventualDensityHJ t) : EventualDensityHJ t := by
  intro δ hδ
  obtain ⟨N₀, hN₀⟩ := h δ hδ
  refine ⟨N₀, ?_⟩
  intro N hN A hdensity
  apply hN₀ N hN A
  rw [density_eq_card_div_card, card_word] at hdensity
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (t : ℝ) ^ N)).1
  simpa only [Nat.cast_pow] using hdensity

/-- For every positive alphabet size, the internal real-density statement and
the cardinality statement from Erdős Problem 171 are equivalent. -/
theorem eventualDensityHJ_iff_cardinality {t : ℕ} (ht : 0 < t) :
    EventualDensityHJ t ↔ CardinalityEventualDensityHJ t :=
  ⟨fun h ↦ h.cardinality ht, fun h ↦ h.eventual ht⟩

/-- The exact all-alphabet statement asked in Erdős Problem 171. -/
def Erdos171Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ t : ℕ, 1 ≤ t →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset (Word t N),
      ε * (t : ℝ) ^ N ≤ (A.card : ℝ) →
        ContainsLine (A : Set (Word t N))

/-- Package a proof of eventual density Hales--Jewett for every nonempty
finite alphabet into the exact statement of Erdős Problem 171. -/
theorem erdos171Statement_of_eventualDensityHJ
    (h : ∀ t : ℕ, 0 < t → EventualDensityHJ t) :
    Erdos171Statement := by
  intro ε hε t ht
  exact (h t (by omega)).cardinality (by omega) ε hε

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/AlphabetInduction.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Alphabet induction for Erdős Problem 171

This file contains the formal induction on the alphabet size in the
Dodos--Kanellopoulos--Tyros proof.  Its sole combinatorial hypothesis says
that density Hales--Jewett for a `k`-letter alphabet, with `k ≥ 2`, supplies
the fixed-density increment step for the `(k+1)`-letter alphabet.  The
iteration of each such step is already proved in `Iteration`.

The one- and two-letter cases are unconditional.  Strong induction then
proves the finite theorem for every nonempty alphabet; the framework turns
that into the eventual theorem, and `Packaging` gives the literal statement
of Erdős Problem 171.
-/



/-- The exact successor-alphabet input required by the DKT alphabet
induction.  It remains an explicit theorem hypothesis in this helper; the
main development must instantiate it with the combinatorial proof. -/
def AlphabetDensityIncrementHypothesis : Type :=
  ∀ k : ℕ, 2 ≤ k → FiniteDensityHJ k →
    ∀ δ : ℝ, 0 < δ → DensityIncrementStep (k + 1) δ

/-- Strong induction on the alphabet size packages the two base cases and
the successor density-increment theorem into one-witness density
Hales--Jewett for every nonempty finite alphabet. -/
theorem finiteDensityHJ_all_of_alphabetDensityIncrement
    (step : AlphabetDensityIncrementHypothesis) :
    ∀ t : ℕ, 1 ≤ t → FiniteDensityHJ t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro ht
      by_cases ht1 : t = 1
      · simpa [ht1] using finiteDensityHJ_one
      by_cases ht2 : t = 2
      · simpa [ht2] using finiteDensityHJ_two
      have ht3 : 3 ≤ t := by omega
      let k := t - 1
      have hk2 : 2 ≤ k := by
        dsimp [k]
        omega
      have hkt : k < t := by
        dsimp [k]
        omega
      have hkpos : 1 ≤ k := hk2.trans' (by omega)
      have hk : FiniteDensityHJ k := ih k hkt hkpos
      have hs : k + 1 = t := by
        dsimp [k]
        omega
      rw [← hs]
      exact hk.succ_of_densityIncrement (step k hk2)

/-- The alphabet induction in the eventual formulation used by Erdős 171. -/
theorem eventualDensityHJ_all_of_alphabetDensityIncrement
    (step : AlphabetDensityIncrementHypothesis) :
    ∀ t : ℕ, 1 ≤ t → EventualDensityHJ t := by
  intro t ht
  exact (finiteDensityHJ_all_of_alphabetDensityIncrement step t ht).eventual
    (by omega)

/-- The exact cardinality-and-coordinate statement of Erdős Problem 171,
conditional only on the successor-alphabet density-increment theorem. -/
theorem erdos171Statement_of_alphabetDensityIncrement
    (step : AlphabetDensityIncrementHypothesis) :
    Erdos171Statement := by
  apply erdos171Statement_of_eventualDensityHJ
  intro t ht
  exact eventualDensityHJ_all_of_alphabetDensityIncrement step t (by omega)

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/DKT.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The final density-increment integration for Erdős 171

This file combines the two quantitative outputs of the Dodos--Kanellopoulos--
Tyros argument.  A structured set `D` is positively correlated with the
ambient family `A`, and a tiling covers all but a quadratically small part of
`D`.  The correlation therefore survives on the covered part.  Since the
tiles are pairwise disjoint, one tile has increased pullback density.

The constants in this lemma are deliberately abstract.  Later in the file
they are instantiated by the frozen constants supplied by the correlation
and insensitive-tiling modules.
-/



open Combinatorics

attribute [local instance] Classical.dec

/-- At a density threshold above one the increment statement is vacuous,
because every finite-set density is at most one. -/
def vacuousDensityIncrementStep {t : ℕ} {delta : ℝ} (hdelta : 1 < delta) :
    DensityIncrementStep t delta where
  increment := 1
  increment_pos := zero_lt_one
  threshold := fun _ ↦ 0
  force _ A hA := by
    exfalso
    exact (not_lt_of_ge (hA.trans (density_le_one A))) hdelta

/-- The qualitative intersection-tiling theorem specialized to the `k`
insensitive factors produced by structured correlation. -/
theorem exists_k_intersection_tiling
    {k : ℕ} (hk : 0 < k) {beta : ℝ} (hbeta : 0 < beta)
    (hone : ∀ d, ∃ n, OneInsensitiveTilingAt k d n beta) :
    ∀ d, ∃ n, InsensitiveIntersectionTilingAt k k d n beta := by
  intro d
  obtain ⟨n, hn⟩ :=
    exists_insensitiveIntersectionTilingAt hbeta hone (k - 1) d
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hn' : InsensitiveIntersectionTilingAt k k d n beta := by
    simpa only [hpred] using hn
  exact ⟨n, hn'⟩

/-- The preceding specialization while preserving a prescribed lower bound
on the ambient tiling dimension. -/
theorem exists_k_intersection_tiling_ge
    {k : ℕ} (hk : 0 < k) {beta : ℝ} (hbeta : 0 < beta)
    (hone : ∀ d N, ∃ n, N ≤ n ∧ OneInsensitiveTilingAt k d n beta) :
    ∀ d N, ∃ n, N ≤ n ∧
      InsensitiveIntersectionTilingAt k k d n beta := by
  intro d N
  obtain ⟨n, hNn, hn⟩ :=
    exists_insensitiveIntersectionTilingAt_ge hbeta hone (k - 1) d N
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hn' : InsensitiveIntersectionTilingAt k k d n beta := by
    simpa only [hpred] using hn
  exact ⟨n, hNn, hn'⟩

/-- Choose the frozen small cube and all numerical parameters used by the
DKT increment argument.  The small cube is chosen at density `delta / 4`
and then enlarged, if necessary, to have positive dimension. -/
theorem exists_frozen_DKT_parameters
    {k : ℕ} (hk : 2 ≤ k) (hDHJfinite : FiniteDensityHJ k)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) :
    ∃ m0 : ℕ, 0 < m0 ∧
      (∀ B : Finset (Word k m0), delta / 4 ≤ density B →
        ContainsLine (B : Set (Word k m0))) ∧
      let theta := IncrementArithmetic.theta delta
        (Fintype.card (Line (Fin k) (Fin m0)))
      let eta := IncrementArithmetic.eta delta theta
      let gamma := IncrementArithmetic.gamma delta eta k
      0 < theta ∧ theta ≤ 1 ∧ eta ^ 2 / 2 ≤ delta / 2 ∧
        0 < eta ∧ 0 < gamma ∧ gamma < 2 := by
  have hkpos : 0 < k := lt_of_lt_of_le (by omega) hk
  obtain ⟨m0raw, hm0raw⟩ :=
    hDHJfinite.eventual hkpos (delta / 4) (by positivity)
  let m0 := max m0raw 1
  have hm0raw_le : m0raw ≤ m0 := Nat.le_max_left _ _
  have hm0pos : 0 < m0 :=
    lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _)
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hkpos
  have hsmall : ∀ B : Finset (Word k m0), delta / 4 ≤ density B →
      ContainsLine (B : Set (Word k m0)) := hm0raw m0 hm0raw_le
  have huniv : delta / 4 ≤
      density (Finset.univ : Finset (Word k m0)) := by
    rw [density_univ]
    linarith
  obtain ⟨l0, hl0⟩ := hsmall Finset.univ huniv
  letI : Nonempty (Line (Fin k) (Fin m0)) := ⟨l0⟩
  have hqpos : (0 : ℝ) < Fintype.card (Line (Fin k) (Fin m0)) := by
    positivity
  have hqone : (1 : ℝ) ≤ Fintype.card (Line (Fin k) (Fin m0)) := by
    exact_mod_cast Fintype.card_pos
  let theta := IncrementArithmetic.theta delta
    (Fintype.card (Line (Fin k) (Fin m0)))
  let eta := IncrementArithmetic.eta delta theta
  let gamma := IncrementArithmetic.gamma delta eta k
  have htheta : 0 < theta :=
    IncrementArithmetic.theta_pos hdelta hqpos
  have htheta_delta : theta ≤ delta / 4 :=
    IncrementArithmetic.theta_le_delta_div_four hdelta.le hqone
  have htheta_one : theta ≤ 1 := by linarith
  have hbounds := IncrementArithmetic.fixed_parameter_bounds
    hdelta hdelta_one htheta htheta_one
      (show (2 : ℝ) ≤ (k : ℝ) by exact_mod_cast hk)
  have heta_one : eta < 1 := by
    have h3eta : 3 * eta < delta := hbounds.2.2.1
    linarith
  have heta_sq_lt : eta ^ 2 < delta := by
    have heta : 0 < eta := hbounds.1
    have heta_sq_lt_eta : eta ^ 2 < eta := by
      nlinarith [mul_pos heta (sub_pos.mpr heta_one)]
    have h3eta : 3 * eta < delta := hbounds.2.2.1
    linarith
  refine ⟨m0, hm0pos, hsmall, ?_⟩
  dsimp only
  exact ⟨htheta, htheta_one, by linarith, hbounds.1,
    hbounds.2.2.2.1, hbounds.2.2.2.2.2.2.2.2⟩

namespace BlockCoord

/-- Finiteness of a nested block-coordinate type, transported from its
ordinary finite index type. -/
noncomputable instance instFintype (M s r : ℕ) :
    Fintype (BlockCoord M s r) :=
  Fintype.ofEquiv (Fin (r * M + s)) (equivFin M s r).symm

end BlockCoord

namespace UniformFibres.FrozenPrefix

open BlockTower

/-- A frozen prefix leaves one distinguished word block and the whole
remaining suffix free.  This subspace exposes those two pieces as one sum
parameter cube. -/
def freeBlockTailNested {t M s q : ℕ} : ∀ {r : ℕ},
    FrozenPrefix (Word t M) r (q + 1) →
      Subspace (Fin M ⊕ BlockCoord M s q) (Fin t) (BlockCoord M s r)
  | _, .nil _ => default
  | _, .cons z p => fixedLeft z (freeBlockTailNested p)

@[simp] theorem freeBlockTailNested_apply {t M s q : ℕ} : ∀ {r : ℕ}
    (p : FrozenPrefix (Word t M) r (q + 1))
    (x : Word t M) (y : BlockCoord M s q → Fin t),
    freeBlockTailNested (s := s) p (Subspace.sumWord x y) =
      BlockTower.functionEquiv t M s r
        (p.prepend (x, (BlockTower.functionEquiv t M s q).symm y))
  | _, .nil _, x, y => by
      change Sum.elim x y =
        BlockTower.functionEquiv t M s (q + 1)
          (x, (BlockTower.functionEquiv t M s q).symm y)
      rw [BlockTower.functionEquiv_succ_apply]
      simp
  | _, .cons z p, x, y => by
      rw [freeBlockTailNested, fixedLeft_apply,
        BlockTower.functionEquiv_succ_apply]
      exact congrArg (Sum.elim z)
        (freeBlockTailNested_apply (s := s) p x y)

/-- Flatten `freeBlockTailNested` back to the ordinary `Fin`-indexed ambient
cube. -/
def freeBlockTail {t M s q r : ℕ}
    (p : FrozenPrefix (Word t M) r (q + 1)) :
    Subspace (Fin M ⊕ BlockCoord M s q) (Fin t) (Fin (r * M + s)) :=
  (freeBlockTailNested (s := s) p).reindex (Equiv.refl _) (Equiv.refl _)
    (BlockCoord.equivFin M s r)

@[simp] theorem freeBlockTail_apply_sumWord {t M s q r : ℕ}
    (p : FrozenPrefix (Word t M) r (q + 1))
    (x : Word t M) (y : BlockCoord M s q → Fin t) :
    freeBlockTail p (Subspace.sumWord x y) =
      BlockTower.coordinateWordEquiv t M s r
        (p.prepend (x, (BlockTower.functionEquiv t M s q).symm y)) := by
  funext i
  simp [freeBlockTail, BlockTower.coordinateWordEquiv_apply,
    Subspace.reindex_apply]

end UniformFibres.FrozenPrefix

@[simp] theorem defaultSubspace_apply {α ι : Type*}
    (x : ι → α) : (default : Subspace ι α ι) x = x := rfl

/-- Change from the block flattening used by `UniformWordFibres` to the
explicit nested-coordinate flattening used by `freeBlockTail`. -/
noncomputable def uniformCoordinatePullback (t M s r : ℕ)
    (A : Finset (Word t (r * M + s))) :
    Finset (Word t (r * M + s)) :=
  A.map (((BlockTower.wordEquiv t M s r).symm.trans
    (BlockTower.coordinateWordEquiv t M s r)).symm.toEmbedding)

@[simp] theorem density_uniformCoordinatePullback (t M s r : ℕ)
    (A : Finset (Word t (r * M + s))) :
    density (uniformCoordinatePullback t M s r A) = density A := by
  rw [uniformCoordinatePullback, density_map_equiv]

@[simp] theorem wordEquiv_mem_uniformCoordinatePullback
    (t M s r : ℕ) (A : Finset (Word t (r * M + s)))
    (z : BlockTower (Word t M) (Word t s) r) :
    BlockTower.wordEquiv t M s r z ∈ uniformCoordinatePullback t M s r A ↔
      BlockTower.coordinateWordEquiv t M s r z ∈ A := by
  simp only [uniformCoordinatePullback, Finset.mem_map,
    Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨a, ha, h⟩
    have hz : (BlockTower.coordinateWordEquiv t M s r).symm a = z := by
      apply (BlockTower.wordEquiv t M s r).injective
      exact h
    have haeq : a = BlockTower.coordinateWordEquiv t M s r z := by
      apply (BlockTower.coordinateWordEquiv t M s r).symm.injective
      simpa using hz
    exact haeq ▸ ha
  · intro hz
    exact ⟨BlockTower.coordinateWordEquiv t M s r z, hz, by simp⟩

/-- The tails in the pullback through `freeBlockTail` are precisely the word
fibres selected by the uniform-fibres lemma, up to the canonical coordinate
equivalence on the tail. -/
theorem density_sectionTails_freeBlockTail_eq_wordFibre
    {k M s q r : ℕ}
    (A : Finset (Word (k + 1) (r * M + s)))
    (p : UniformFibres.FrozenPrefix (Word (k + 1) M) r (q + 1))
    (x : Word (k + 1) M) :
    density (sectionTails
      (default : Subspace (Fin M) (Fin (k + 1)) (Fin M))
      (pullbackFinset p.freeBlockTail A) x) =
      density (UniformWordFibres.wordFibre
        (uniformCoordinatePullback (k + 1) M s r A) p x) := by
  classical
  let e : (BlockCoord M s q → Fin (k + 1)) ≃ Word (k + 1) (q * M + s) :=
    (BlockTower.functionEquiv (k + 1) M s q).symm.trans
      (BlockTower.wordEquiv (k + 1) M s q)
  have hset :
      sectionTails (default : Subspace (Fin M) (Fin (k + 1)) (Fin M))
          (pullbackFinset p.freeBlockTail A) x =
        (UniformWordFibres.wordFibre
          (uniformCoordinatePullback (k + 1) M s r A) p x).map
            e.symm.toEmbedding := by
    ext y
    simp only [mem_sectionTails, mem_pullbackFinset, Finset.mem_map,
      Equiv.toEmbedding_apply, UniformWordFibres.mem_wordFibre,
      wordEquiv_mem_uniformCoordinatePullback, defaultSubspace_apply]
    change p.freeBlockTail (Subspace.sumWord x y) ∈ A ↔ _
    rw [UniformFibres.FrozenPrefix.freeBlockTail_apply_sumWord p x y]
    constructor
    · intro hy
      refine ⟨e y, ?_, ?_⟩
      · simpa [e] using hy
      · exact e.symm_apply_apply y
    · rintro ⟨a, ha, hay⟩
      have haeq : a = e y := by
        apply e.symm.injective
        simpa using hay
      subst a
      simpa [e] using ha
  rw [hset]
  exact density_map_equiv e.symm _

/-- Pulling back through a composite subspace is the same as performing the
two pullbacks successively. -/
@[simp] theorem iterationPullback_comp
    {e d t n : ℕ} (U : Subspace (Fin d) (Fin t) (Fin n))
    (V : Subspace (Fin e) (Fin t) (Fin d))
    (A : Finset (Word t n)) :
    iterationPullback (U.comp V) A =
      iterationPullback V (iterationPullback U A) := by
  simp only [iterationPullback_eq_pullbackFinset, pullbackFinset_comp]

/-- A line in a pullback over an arbitrary finite coordinate type maps to a
line in the original family. -/
theorem not_containsLineOn_pullbackFinset
    {alpha eta iota : Type*} [Fintype (eta → alpha)]
    (U : Subspace eta alpha iota) (A : Finset (iota → alpha))
    (hA : ¬ContainsLineOn (A : Set (iota → alpha))) :
    ¬ContainsLineOn (pullbackFinset U A : Set (eta → alpha)) := by
  intro h
  apply hA
  obtain ⟨l, hl⟩ := h
  refine ⟨U.lineMap l, ?_⟩
  rintro _ ⟨a, rfl⟩
  rw [Subspace.lineMap_apply]
  exact (mem_pullbackFinset U A (l a)).1 (hl ⟨a, rfl⟩)

/-- Removing the part of `D` not covered by a tiling loses at most its whole
density from the correlation with `A`. -/
theorem correlated_density_on_covered
    {X : Type*} [Fintype X] [DecidableEq X]
    (A D E : Finset X) {rho gamma : ℝ}
    (hcorr : (rho + gamma) * density D < density (A ∩ D)) :
    (rho + gamma) * density D - density (D \ E) < density (A ∩ E) := by
  have hsub : A ∩ D ⊆ (A ∩ E) ∪ (D \ E) := by
    intro x hx
    by_cases hxE : x ∈ E
    · exact Finset.mem_union.mpr <|
        Or.inl (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hxE⟩)
    · exact Finset.mem_union.mpr <|
        Or.inr (Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx).2, hxE⟩)
  have hmono : density (A ∩ D) ≤ density ((A ∩ E) ∪ (D \ E)) :=
    density_mono hsub
  have hunion : density ((A ∩ E) ∪ (D \ E)) ≤
      density (A ∩ E) + density (D \ E) :=
    density_union_le_add _ _
  linarith

/-- A structured correlation which is tiled up to error `gamma²/2` forces
one tile to have density strictly larger than `rho + gamma/2`.

This is the last averaging step of the DKT density-increment proof.  Notice
that `rho` is the actual density, whereas `gamma` may have been frozen at a
smaller baseline density. -/
theorem exists_increment_tile_of_structured_tiling
    {k d n : ℕ} {rho gamma : ℝ}
    (A D : Finset (Word (k + 1) n))
    (T : SubspaceTiling (Fin d) (Fin (k + 1)) (Fin n))
    (hrho : 0 ≤ rho) (hgamma : 0 < gamma)
    (hD : gamma < density D)
    (hcorr : (rho + gamma) * density D < density (A ∩ D))
    (hcontained : T.IsContainedIn D)
    (hloss : density (D \ T.covered) < gamma ^ 2 / 2) :
    ∃ U ∈ T.tiles,
      rho + gamma / 2 < density (iterationPullback U A) := by
  letI : Nonempty (Fin (k + 1)) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Word (k + 1) d) := Pi.instNonempty
  have hcover : T.covered ⊆ D := (T.covered_subset_iff D).2 hcontained
  have hcoverDensity : density T.covered ≤ density D := density_mono hcover
  have hcoveredCorrelation :
      (rho + gamma) * density D - density (D \ T.covered) <
        density (A ∩ T.covered) :=
    correlated_density_on_covered A D T.covered hcorr
  have hcoveredIncrement :
      (rho + gamma / 2) * density T.covered <
        density (A ∩ T.covered) := by
    apply IncrementArithmetic.uncovered_mass_density_increment
      hrho hgamma hD hloss hcoverDensity
    exact hcoveredCorrelation.le
  by_contra! hall
  let q : Subspace (Fin d) (Fin (k + 1)) (Fin n) →
      Finset (Word (k + 1) n) := fun U ↦ subspacePoints U ∩ A
  have hqsub : ∀ U ∈ T.tiles, q U ⊆ subspacePoints U := by
    intro U _
    exact Finset.inter_subset_left
  have hqlocal : ∀ U ∈ T.tiles,
      density (q U) ≤
        (rho + gamma / 2) * density (subspacePoints U) := by
    intro U hU
    have hpull : density (subspacePullback U A) ≤ rho + gamma / 2 := by
      simpa only [iterationPullback_eq_subspacePullback] using hall U hU
    rw [show q U = subspacePoints U ∩ A by rfl,
      density_inter_subspacePoints]
    have htileNonneg : 0 ≤ density (subspacePoints U) := density_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hpull htileNonneg
    nlinarith
  have hsum := density_biUnion_le_mul_density_biUnion
    T.pairwiseDisjoint hqsub hqlocal
  have hpUnion : T.tiles.biUnion subspacePoints = T.covered := rfl
  have hqUnion : T.tiles.biUnion q = T.covered ∩ A := by
    ext x
    simp only [q, Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · rintro ⟨U, hU, hxU, hxA⟩
      exact ⟨T.mem_covered x |>.2 ⟨U, hU, hxU⟩, hxA⟩
    · rintro ⟨hxT, hxA⟩
      obtain ⟨U, hU, hxU⟩ := (T.mem_covered x).1 hxT
      exact ⟨U, hU, hxU, hxA⟩
  rw [hqUnion, hpUnion] at hsum
  have hcomm : T.covered ∩ A = A ∩ T.covered := Finset.inter_comm _ _
  rw [hcomm] at hsum
  exact (not_le_of_gt hcoveredIncrement) hsum

/-- Weak-inequality interface expected by `DensityIncrementStep.force`. -/
theorem exists_increment_subspace_of_structured_tiling
    {k d n : ℕ} {rho gamma : ℝ}
    (A D : Finset (Word (k + 1) n))
    (T : SubspaceTiling (Fin d) (Fin (k + 1)) (Fin n))
    (hrho : 0 ≤ rho) (hgamma : 0 < gamma)
    (hD : gamma < density D)
    (hcorr : (rho + gamma) * density D < density (A ∩ D))
    (hcontained : T.IsContainedIn D)
    (hloss : density (D \ T.covered) < gamma ^ 2 / 2) :
    ∃ U : Subspace (Fin d) (Fin (k + 1)) (Fin n),
      rho + gamma / 2 ≤ density (iterationPullback U A) := by
  obtain ⟨U, _hU, hinc⟩ := exists_increment_tile_of_structured_tiling
    A D T hrho hgamma hD hcorr hcontained hloss
  exact ⟨U, hinc.le⟩

/-- Combine one structured-correlation output with an exact-dimension
intersection tiling.  This is the target-dimension instance from which the
`force` field of the final density-increment step is assembled.

The disjunctive hypothesis is exactly the useful conclusion of the
structured-correlation module: either the original family already has a
line, or its pullback to `W` correlates with an intersection of `k`
insensitive sets. -/
theorem force_of_structured_correlation_and_tiling
    {k d m n : ℕ} (hk : 2 ≤ k)
    {gamma : ℝ} (hgamma : 0 < gamma) (hgamma_two : gamma < 2)
    (A : Finset (Word (k + 1) n))
    (hstructured :
      ContainsLine (A : Set (Word (k + 1) n)) ∨
        ∃ W : Subspace (Fin m) (Fin (k + 1)) (Fin n),
        ∃ D : Fin k → Finset (Word (k + 1) m),
          (∀ i, IsLastInsensitive i (D i : Set (Word (k + 1) m))) ∧
          gamma < density (familyInter D) ∧
          (density A + gamma) * density (familyInter D) <
            density (iterationPullback W A ∩ familyInter D))
    (htiling : InsensitiveIntersectionTilingAt k k d m
      (gamma ^ 2 / (4 * (k : ℝ)))) :
    ContainsLine (A : Set (Word (k + 1) n)) ∨
      ∃ U : Subspace (Fin d) (Fin (k + 1)) (Fin n),
        density A + gamma / 2 ≤ density (iterationPullback U A) := by
  rcases hstructured with hline | ⟨W, D, hDins, hDdense, hDcorr⟩
  · exact Or.inl hline
  · right
    have hkR : (k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega : 0 < 2) hk))
    have herror :
        2 * (k : ℝ) * (gamma ^ 2 / (4 * (k : ℝ))) = gamma ^ 2 / 2 :=
      IncrementArithmetic.tiling_error_identity hkR
    have hthreshold :
        2 * (k : ℝ) * (gamma ^ 2 / (4 * (k : ℝ))) <
          density (familyInter D) := by
      rw [herror]
      exact (IncrementArithmetic.tiling_error_lt_gamma hgamma hgamma_two).trans
        hDdense
    obtain ⟨T, hTcontained, hTloss⟩ :=
      htiling (fun i : Fin k ↦ i) D hDins hthreshold
    have hrho : 0 ≤ density A := density_nonneg A
    obtain ⟨V, hV⟩ := exists_increment_subspace_of_structured_tiling
      (iterationPullback W A) (familyInter D) T hrho hgamma hDdense hDcorr
        hTcontained (by simpa only [herror] using hTloss)
    refine ⟨W.comp V, ?_⟩
    simpa only [iterationPullback_comp] using hV

/-- Package target-dependent structured-correlation and tiling dimensions as
a `DensityIncrementStep`.  The middle dimension may depend on the requested
tile dimension, and the ambient threshold may in turn depend on that middle
dimension; no monotonicity of either choice is required. -/
noncomputable def densityIncrementStep_of_structured_tilings
    {k : ℕ} (hk : 2 ≤ k) {delta gamma : ℝ}
    (hgamma : 0 < gamma) (hgamma_two : gamma < 2)
    (middle threshold : ℕ → ℕ)
    (hstructured : ∀ d : ℕ,
      ∀ A : Finset (Word (k + 1) (threshold d)),
        delta ≤ density A →
          ContainsLine (A : Set (Word (k + 1) (threshold d))) ∨
            ∃ W : Subspace (Fin (middle d)) (Fin (k + 1))
                (Fin (threshold d)),
            ∃ D : Fin k → Finset (Word (k + 1) (middle d)),
              (∀ i, IsLastInsensitive i
                (D i : Set (Word (k + 1) (middle d)))) ∧
              gamma < density (familyInter D) ∧
              (density A + gamma) * density (familyInter D) <
                density (iterationPullback W A ∩ familyInter D))
    (htiling : ∀ d : ℕ,
      InsensitiveIntersectionTilingAt k k d (middle d)
        (gamma ^ 2 / (4 * (k : ℝ)))) :
    DensityIncrementStep (k + 1) delta where
  increment := gamma / 2
  increment_pos := half_pos hgamma
  threshold := threshold
  force d A hA :=
    force_of_structured_correlation_and_tiling hk hgamma hgamma_two A
      (hstructured d A hA) (htiling d)

/-- A structured-correlation conclusion at fixed middle and ambient
dimensions.  Naming this interface keeps the dimension-selection layer
independent of how the uniform-fibres argument constructs its witness. -/
def StructuredIncrementAt (k m n : ℕ) (delta gamma : ℝ) : Prop :=
  ∀ A : Finset (Word (k + 1) n), delta ≤ density A →
    ContainsLine (A : Set (Word (k + 1) n)) ∨
      ∃ W : Subspace (Fin m) (Fin (k + 1)) (Fin n),
      ∃ D : Fin k → Finset (Word (k + 1) m),
        (∀ i, IsLastInsensitive i (D i : Set (Word (k + 1) m))) ∧
        gamma < density (familyInter D) ∧
        (density A + gamma) * density (familyInter D) <
          density (iterationPullback W A ∩ familyInter D)

/-- Abstract interface of the uniform-fibres/correlation half of DKT. -/
def UniformStructuredCorrelationPrinciple : Prop :=
  ∀ (k m0 m : ℕ), 2 ≤ k → 0 < m0 → m0 ≤ m →
    ∀ delta0 : ℝ, 0 < delta0 → delta0 ≤ 1 →
    0 < IncrementArithmetic.theta delta0
      (Fintype.card (Line (Fin k) (Fin m0))) →
    IncrementArithmetic.theta delta0
      (Fintype.card (Line (Fin k) (Fin m0))) ≤ 1 →
    (IncrementArithmetic.eta delta0
      (IncrementArithmetic.theta delta0
        (Fintype.card (Line (Fin k) (Fin m0))))) ^ 2 / 2 ≤ delta0 / 2 →
    density (liftFinset (Finset.univ : Finset (Word k m))) <
      IncrementArithmetic.eta delta0
        (IncrementArithmetic.theta delta0
          (Fintype.card (Line (Fin k) (Fin m0)))) →
    (∀ B : Finset (Word k m0), delta0 / 4 ≤ density B →
      ContainsLine (B : Set (Word k m0))) →
    ∃ n : ℕ, ∀ A : Finset (Word (k + 1) n),
      delta0 ≤ density A →
      ¬ContainsLine (A : Set (Word (k + 1) n)) →
      ∃ W : Subspace (Fin m) (Fin (k + 1)) (Fin n),
      ∃ D : Fin k → Finset (Word (k + 1) m),
        (∀ i, IsLastInsensitive i (D i : Set (Word (k + 1) m))) ∧
        IncrementArithmetic.gamma delta0
            (IncrementArithmetic.eta delta0
              (IncrementArithmetic.theta delta0
                (Fintype.card (Line (Fin k) (Fin m0))))) k <
          density (familyInter D) ∧
        (density A + IncrementArithmetic.gamma delta0
            (IncrementArithmetic.eta delta0
              (IncrementArithmetic.theta delta0
                (Fintype.card (Line (Fin k) (Fin m0))))) k) *
            density (familyInter D) <
          density (pullbackFinset W A ∩ familyInter D)

/-- Abstract lower-bound-preserving interface of DKT Lemma 12. -/
def EventualOneInsensitiveTilingPrinciple : Prop :=
  ∀ (k : ℕ), 0 < k → FiniteDensityHJ k →
    ∀ beta : ℝ, 0 < beta →
    ∀ d N : ℕ, ∃ n, N ≤ n ∧ OneInsensitiveTilingAt k d n beta

/-- The uniform-correlation development supplies its abstract interface. -/
theorem uniformStructuredCorrelationPrinciple :
    UniformStructuredCorrelationPrinciple := by
  intro k m0 m hk hm0 hm0m delta0 hdelta0 hdelta0_one htheta
    htheta_one herror hface hDHJ
  exact UniformCorrelation.exists_structured_correlation_at
    k m0 m hk hm0 hm0m delta0 hdelta0 hdelta0_one htheta htheta_one
      herror hface hDHJ

/-- The greedy insensitive-tiling development supplies its abstract
lower-bound-preserving interface. -/
theorem eventualOneInsensitiveTilingPrinciple :
    EventualOneInsensitiveTilingPrinciple := by
  intro k hk hDHJ beta hbeta d N
  exact (hDHJ.finiteRestrictedMDHJ hk d).exists_oneInsensitiveTilingAt_ge
    hbeta N

/-- Choose the middle tiling dimension separately for every requested target
dimension, subject to a common lower bound, and only then choose the ambient
correlation dimension.  This is the quantifier order needed to combine face
decay with insensitive tiling. -/
noncomputable def densityIncrementStep_of_eventual_structured_tilings
    {k : ℕ} (hk : 2 ≤ k) {delta gamma : ℝ}
    (hgamma : 0 < gamma) (hgamma_two : gamma < 2) (base : ℕ)
    (htilingExists : ∀ d N, ∃ m, N ≤ m ∧
      InsensitiveIntersectionTilingAt k k d m
        (gamma ^ 2 / (4 * (k : ℝ))))
    (hstructuredExists : ∀ m, base ≤ m →
      ∃ n, StructuredIncrementAt k m n delta gamma) :
    DensityIncrementStep (k + 1) delta := by
  let middle : ℕ → ℕ := fun d ↦ (htilingExists d base).choose
  have hmiddle (d : ℕ) : base ≤ middle d :=
    (htilingExists d base).choose_spec.1
  have htiling (d : ℕ) :
      InsensitiveIntersectionTilingAt k k d (middle d)
        (gamma ^ 2 / (4 * (k : ℝ))) :=
    (htilingExists d base).choose_spec.2
  let threshold : ℕ → ℕ := fun d ↦
    (hstructuredExists (middle d) (hmiddle d)).choose
  have hstructured (d : ℕ) :
      StructuredIncrementAt k (middle d) (threshold d) delta gamma :=
    (hstructuredExists (middle d) (hmiddle d)).choose_spec
  exact densityIncrementStep_of_structured_tilings hk hgamma hgamma_two
    middle threshold (fun d ↦ hstructured d) htiling

/-- Complete parameter and dimension assembly from the two concrete DKT
principles.  All constants are frozen at the input lower density `delta`. -/
noncomputable def densityIncrementStep_of_DKT_principles
    (huniform : UniformStructuredCorrelationPrinciple)
    (hone : EventualOneInsensitiveTilingPrinciple)
    {k : ℕ} (hk : 2 ≤ k) (hDHJfinite : FiniteDensityHJ k)
    (delta : ℝ) (hdelta : 0 < delta) :
    DensityIncrementStep (k + 1) delta := by
  by_cases hlarge : 1 < delta
  · exact vacuousDensityIncrementStep hlarge
  have hdelta_one : delta ≤ 1 := le_of_not_gt hlarge
  let m0 :=
    (exists_frozen_DKT_parameters hk hDHJfinite hdelta hdelta_one).choose
  have hparameters :=
    (exists_frozen_DKT_parameters hk hDHJfinite hdelta hdelta_one).choose_spec
  have hm0 : 0 < m0 := hparameters.1
  have hDHJ0 : ∀ B : Finset (Word k m0), delta / 4 ≤ density B →
      ContainsLine (B : Set (Word k m0)) := hparameters.2.1
  let theta := IncrementArithmetic.theta delta
    (Fintype.card (Line (Fin k) (Fin m0)))
  let eta := IncrementArithmetic.eta delta theta
  let gamma := IncrementArithmetic.gamma delta eta k
  have htheta : 0 < theta := hparameters.2.2.1
  have htheta_one : theta ≤ 1 := hparameters.2.2.2.1
  have herror : eta ^ 2 / 2 ≤ delta / 2 := hparameters.2.2.2.2.1
  have heta : 0 < eta := hparameters.2.2.2.2.2.1
  have hgamma : 0 < gamma := hparameters.2.2.2.2.2.2.1
  have hgamma_two : gamma < 2 := hparameters.2.2.2.2.2.2.2
  let Mface := (eventually_density_liftFinset_univ_lt k heta).choose
  have hMface := (eventually_density_liftFinset_univ_lt k heta).choose_spec
  let base := max m0 Mface
  have hm0base : m0 ≤ base := Nat.le_max_left _ _
  have hMfacebase : Mface ≤ base := Nat.le_max_right _ _
  have hkpos : 0 < k := lt_of_lt_of_le (by omega) hk
  let beta : ℝ := gamma ^ 2 / (4 * (k : ℝ))
  have hbeta : 0 < beta := by
    dsimp only [beta]
    positivity
  have hone' : ∀ d N, ∃ n, N ≤ n ∧
      OneInsensitiveTilingAt k d n beta :=
    hone k hkpos hDHJfinite beta hbeta
  have htilingExists : ∀ d N, ∃ m, N ≤ m ∧
      InsensitiveIntersectionTilingAt k k d m beta :=
    exists_k_intersection_tiling_ge hkpos hbeta hone'
  have hstructuredExists : ∀ m, base ≤ m →
      ∃ n, StructuredIncrementAt k m n delta gamma := by
    intro m hbasem
    have hm0m : m0 ≤ m := hm0base.trans hbasem
    have hfacem : density
        (liftFinset (Finset.univ : Finset (Word k m))) < eta :=
      hMface m (hMfacebase.trans hbasem)
    let n := (huniform k m0 m hk hm0 hm0m delta hdelta hdelta_one
      htheta htheta_one herror hfacem hDHJ0).choose
    have hn := (huniform k m0 m hk hm0 hm0m delta hdelta hdelta_one
      htheta htheta_one herror hfacem hDHJ0).choose_spec
    refine ⟨n, ?_⟩
    intro A hA
    by_cases hline : ContainsLine (A : Set (Word (k + 1) n))
    · exact Or.inl hline
    · right
      obtain ⟨W, D, hDins, hDdense, hDcorr⟩ := hn A hA hline
      exact ⟨W, D, hDins, hDdense, by
        simpa only [iterationPullback_eq_pullbackFinset] using hDcorr⟩
  exact densityIncrementStep_of_eventual_structured_tilings hk hgamma
    hgamma_two base (by simpa only [beta] using htilingExists)
      hstructuredExists

/-- The unconditional DKT density-increment step from density
Hales--Jewett on the preceding alphabet. -/
noncomputable def densityIncrementStep_succ
    {k : ℕ} (hk : 2 ≤ k) (hDHJfinite : FiniteDensityHJ k)
    (delta : ℝ) (hdelta : 0 < delta) :
    DensityIncrementStep (k + 1) delta :=
  densityIncrementStep_of_DKT_principles
    uniformStructuredCorrelationPrinciple
    eventualOneInsensitiveTilingPrinciple hk hDHJfinite delta hdelta

/-- The density-increment hypothesis required by alphabet induction. -/
noncomputable def alphabetDensityIncrement :
    AlphabetDensityIncrementHypothesis :=
  fun k hk hDHJfinite delta hdelta ↦
    densityIncrementStep_succ hk hDHJfinite delta hdelta

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 171.
https://www.erdosproblems.com/forum/thread/171

Informal authors:
- Pandelis Dodos
- Vassilis Kanellopoulos
- Konstantinos Tyros

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos171.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Erdős Problem 171

The density Hales--Jewett theorem: every subset of `[t]^N` of fixed positive
density contains a combinatorial line once `N` is sufficiently large.

The proof formalized here follows the uniform-measure density-increment
argument of Dodos--Kanellopoulos--Tyros.  Its principal inputs are the
Hales--Jewett theorem, a derived line-coloring Graham--Rothschild theorem,
Sperner's theorem for the binary base case, uniform-fibre regularization,
structured correlation by insensitive sets, and a greedy subspace tiling.
-/



/-- The affirmative resolution of Erdős Problem 171. -/
theorem erdos_171 :
    ∀ ε : ℝ, 0 < ε → ∀ t : ℕ, 1 ≤ t →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset (Word t N),
        ε * (t : ℝ) ^ N ≤ (A.card : ℝ) →
          ContainsLine (A : Set (Word t N)) :=
  erdos171Statement_of_alphabetDensityIncrement alphabetDensityIncrement

end

#print axioms erdos_171
-- 'Erdos171.erdos_171' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos171
