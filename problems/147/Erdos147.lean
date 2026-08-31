import Mathlib

set_option linter.constructorNameAsVariable false
set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos147

/-
# Problem Description

Erdős Problem 147 ($500), the Erdős--Simonovits conjecture: if `H` is bipartite with minimum
degree `r`, then there is some `ε = ε(H) > 0` with

  `ex(n; H) ≫ n ^ (2 - 1/(r-1) + ε)`.

`erdos_147` proves this is false. The conjecture was disproved by Janzer, for even `r ≥ 4`.

The witness formalized here is `C₁₂[2]`, the 2-fold blow-up of the 12-cycle: bipartite and
4-regular, so of minimum degree `r = 4`, and with extremal exponent at most `139/84`, which
is below the conjectured `2 - 1/(4-1) = 5/3`.

`HasConjecturedLowerBound H r` is `∃ ε > 0, polynomialGrowth (2 - 1/(r-1) + ε) =O[atTop]
extremalGrowth H`, which is the `≫` of the statement; the division in the exponent is real
division.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos888/ColoredGraph.lean` -/

section
/-!
# Coloured finite bipartite graphs

This file supplies the finite graph estimate used in the proof of Erdős
problem 888.  A graph is represented by a relation between two finite types.
All counting functions take values in `ℝ`; their summands are zero-one
indicators, so they are definitionally the usual edge, two-path, and ordered
rectangle counts (the ordered rectangle count is four times the unlabelled
one).
-/

open scoped BigOperators

namespace Erdos888
namespace ColoredGraph

noncomputable section

attribute [local instance] Classical.propDecidable

universe u v w

/-- A finite bipartite graph, presented as its adjacency relation. -/
abbrev BipartiteGraph (L : Type u) (R : Type v) := L → R → Prop

variable {L : Type u} {R : Type v} [Fintype L] [Fintype R]

/-- The zero-one real indicator of an edge. -/
def edgeIndicator (G : BipartiteGraph L R) (x : L) (y : R) : ℝ :=
  if G x y then 1 else 0

/-- Number of edges, viewed as a real number. -/
def edgeCount (G : BipartiteGraph L R) : ℝ :=
  ∑ y : R, ∑ x : L, edgeIndicator G x y

/-- The finite set of edges of a finite bipartite graph. -/
def edgeFinset (G : BipartiteGraph L R) : Finset (L × R) :=
  Finset.univ.filter fun e ↦ G e.1 e.2

@[simp] lemma mem_edgeFinset (G : BipartiteGraph L R) (x : L) (y : R) :
    (x, y) ∈ edgeFinset G ↔ G x y := by
  simp [edgeFinset]

/-- The real-valued edge sum is the cast of the ordinary edge-finset
cardinality. -/
lemma edgeCount_eq_card_edgeFinset (G : BipartiteGraph L R) :
    edgeCount G = ((edgeFinset G).card : ℝ) := by
  simp only [edgeCount, edgeIndicator, edgeFinset, Finset.card_eq_sum_ones,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_filter,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- Degree of a right vertex. -/
def rightDegree (G : BipartiteGraph L R) (y : R) : ℝ :=
  ∑ x : L, edgeIndicator G x y

/-- Common right degree of two left vertices. -/
def codegree (G : BipartiteGraph L R) (x x' : L) : ℝ :=
  ∑ y : R, edgeIndicator G x y * edgeIndicator G x' y

/-- Ordered length-two paths with distinct left endpoints. -/
def twoPathCount (G : BipartiteGraph L R) : ℝ :=
  ∑ x : L, ∑ x' : L, if x = x' then 0 else codegree G x x'

/-- Ordered `2 × 2` rectangles.  Each unlabelled rectangle is counted four times. -/
def rectangleCount (G : BipartiteGraph L R) : ℝ :=
  ∑ x : L, ∑ x' : L, if x = x' then 0 else
    ∑ y : R, ∑ y' : R, if y = y' then 0 else
      edgeIndicator G x y * edgeIndicator G x' y *
        edgeIndicator G x y' * edgeIndicator G x' y'

@[simp] lemma edgeIndicator_nonneg (G : BipartiteGraph L R) (x : L) (y : R) :
    0 ≤ edgeIndicator G x y := by
  by_cases h : G x y <;> simp [edgeIndicator, h]

@[simp] lemma edgeIndicator_sq (G : BipartiteGraph L R) (x : L) (y : R) :
    edgeIndicator G x y * edgeIndicator G x y = edgeIndicator G x y := by
  simp [edgeIndicator]

lemma rightDegree_nonneg (G : BipartiteGraph L R) (y : R) :
    0 ≤ rightDegree G y := by
  exact Finset.sum_nonneg fun _ _ ↦ edgeIndicator_nonneg G _ _

lemma codegree_nonneg (G : BipartiteGraph L R) (x x' : L) :
    0 ≤ codegree G x x' := by
  exact Finset.sum_nonneg fun _ _ ↦ mul_nonneg (edgeIndicator_nonneg G _ _)
    (edgeIndicator_nonneg G _ _)

lemma edgeCount_nonneg (G : BipartiteGraph L R) : 0 ≤ edgeCount G := by
  exact Finset.sum_nonneg fun _ _ ↦ rightDegree_nonneg G _

lemma twoPathCount_nonneg (G : BipartiteGraph L R) : 0 ≤ twoPathCount G := by
  apply Finset.sum_nonneg
  intro x hx
  apply Finset.sum_nonneg
  intro x' hx'
  split_ifs
  · exact le_rfl
  · exact codegree_nonneg G x x'

lemma rectangleCount_nonneg (G : BipartiteGraph L R) : 0 ≤ rectangleCount G := by
  apply Finset.sum_nonneg
  intro x hx
  apply Finset.sum_nonneg
  intro x' hx'
  split_ifs
  · exact le_rfl
  · apply Finset.sum_nonneg
    intro y hy
    apply Finset.sum_nonneg
    intro y' hy'
    split_ifs
    · exact le_rfl
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (edgeIndicator_nonneg G _ _) (edgeIndicator_nonneg G _ _))
          (edgeIndicator_nonneg G _ _))
        (edgeIndicator_nonneg G _ _)

lemma edgeCount_eq_sum_rightDegree (G : BipartiteGraph L R) :
    edgeCount G = ∑ y : R, rightDegree G y := by
  rfl

/-! The next two identities are the exact double-counting core of KST. -/

private lemma rightDegree_sq (G : BipartiteGraph L R) (y : R) :
    (rightDegree G y) ^ 2 = rightDegree G y +
      ∑ x : L, ∑ x' : L, if x = x' then 0 else
        edgeIndicator G x y * edgeIndicator G x' y := by
  classical
  simp only [rightDegree, pow_two]
  rw [Finset.sum_mul_sum]
  calc
    (∑ x : L, ∑ x' : L, edgeIndicator G x y * edgeIndicator G x' y) =
        ∑ x : L, ∑ x' : L,
          ((if x = x' then edgeIndicator G x y else 0) +
            (if x = x' then 0 else edgeIndicator G x y * edgeIndicator G x' y)) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro x' hx'
      by_cases h : x = x'
      · subst x'
        simp [edgeIndicator_sq]
      · simp [h]
    _ = ∑ x : L, (edgeIndicator G x y +
          ∑ x' : L, if x = x' then 0 else
            edgeIndicator G x y * edgeIndicator G x' y) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_add_distrib]
      simp
    _ = _ := by rw [Finset.sum_add_distrib]

lemma sum_rightDegree_sq (G : BipartiteGraph L R) :
    (∑ y : R, (rightDegree G y) ^ 2) = edgeCount G + twoPathCount G := by
  classical
  simp_rw [rightDegree_sq]
  rw [Finset.sum_add_distrib]
  congr 1
  simp only [twoPathCount, codegree]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x' hx'
  by_cases h : x = x' <;> simp [h]

private lemma codegree_sq (G : BipartiteGraph L R) (x x' : L) :
    (codegree G x x') ^ 2 = codegree G x x' +
      ∑ y : R, ∑ y' : R, if y = y' then 0 else
        edgeIndicator G x y * edgeIndicator G x' y *
          edgeIndicator G x y' * edgeIndicator G x' y' := by
  classical
  simp only [codegree, pow_two]
  rw [Finset.sum_mul_sum]
  calc
    (∑ y : R, ∑ y' : R,
        (edgeIndicator G x y * edgeIndicator G x' y) *
          (edgeIndicator G x y' * edgeIndicator G x' y')) =
      ∑ y : R, ∑ y' : R,
        ((if y = y' then edgeIndicator G x y * edgeIndicator G x' y else 0) +
         (if y = y' then 0 else edgeIndicator G x y * edgeIndicator G x' y *
          edgeIndicator G x y' * edgeIndicator G x' y')) := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro y' hy'
      by_cases h : y = y'
      · subst y'
        by_cases hxy : G x y <;> by_cases hx'y : G x' y <;>
          simp [edgeIndicator, hxy, hx'y]
      · simp [h]
        ring
    _ = ∑ y : R, (edgeIndicator G x y * edgeIndicator G x' y +
        ∑ y' : R, if y = y' then 0 else edgeIndicator G x y * edgeIndicator G x' y *
          edgeIndicator G x y' * edgeIndicator G x' y') := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_add_distrib]
      simp
    _ = _ := by rw [Finset.sum_add_distrib]

lemma sum_codegree_sq_offDiagonal (G : BipartiteGraph L R) :
    (∑ x : L, ∑ x' : L, if x = x' then 0 else (codegree G x x') ^ 2) =
      twoPathCount G + rectangleCount G := by
  classical
  simp only [twoPathCount, rectangleCount]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x' hx'
  by_cases hxx : x = x'
  · simp [hxx]
  · simp only [hxx, ↓reduceIte, codegree_sq]

/-- First Cauchy--Schwarz step: edges are controlled by right degrees and
ordered two-paths. -/
lemma edgeCount_sq_le (G : BipartiteGraph L R) :
    (edgeCount G) ^ 2 ≤ (Fintype.card R : ℝ) *
      (edgeCount G + twoPathCount G) := by
  rw [edgeCount_eq_sum_rightDegree]
  calc
    (∑ y : R, rightDegree G y) ^ 2 ≤ (Fintype.card R : ℝ) *
        ∑ y : R, (rightDegree G y) ^ 2 := by
      simpa using
        (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset R))
          (f := rightDegree G))
    _ = _ := by rw [sum_rightDegree_sq, edgeCount_eq_sum_rightDegree]

/-- Second Cauchy--Schwarz step: two-paths are controlled by rectangles. -/
lemma twoPathCount_sq_le (G : BipartiteGraph L R) :
    (twoPathCount G) ^ 2 ≤ (Fintype.card L : ℝ) ^ 2 *
      (twoPathCount G + rectangleCount G) := by
  let f : L × L → ℝ := fun z ↦
    if z.1 = z.2 then 0 else codegree G z.1 z.2
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (L × L))) (f := f)
  have hsum : (∑ z : L × L, f z) = twoPathCount G := by
    simp only [f, twoPathCount, Fintype.sum_prod_type]
  have hsumsq : (∑ z : L × L, (f z) ^ 2) =
      twoPathCount G + rectangleCount G := by
    simp only [f, Fintype.sum_prod_type]
    simpa only [ite_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      sum_codegree_sq_offDiagonal G
  rw [hsum, hsumsq] at hcs
  simpa [Fintype.card_prod, Nat.cast_mul, pow_two] using hcs

/-! ### The analytic extraction of fourth roots -/

/-- A convenient explicit extraction of the two quadratic estimates in the
Kővári--Sós--Turán argument.  Keeping it separate from the counting makes
the constants and all degenerate terms completely transparent. -/
lemma kst_numeric {E S Q M N : ℝ}
    (hE : 0 ≤ E) (hS : 0 ≤ S) (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hES : E ^ 2 ≤ N * (E + S))
    (hSQ : S ^ 2 ≤ M ^ 2 * (S + Q)) :
    E ≤ 2 * N + 2 * M * Real.sqrt N +
      2 * Real.sqrt (M * N) * Real.sqrt (Real.sqrt Q) := by
  have hsN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hsMN : 0 ≤ Real.sqrt (M * N) := Real.sqrt_nonneg (M * N)
  have hsQ : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg Q
  have hssQ : 0 ≤ Real.sqrt (Real.sqrt Q) := Real.sqrt_nonneg (Real.sqrt Q)
  have hsN_sq : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hN
  have hsMN_sq : (Real.sqrt (M * N)) ^ 2 = M * N :=
    Real.sq_sqrt (mul_nonneg hM hN)
  have hsQ_sq : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ
  have hssQ_sq : (Real.sqrt (Real.sqrt Q)) ^ 2 = Real.sqrt Q :=
    Real.sq_sqrt hsQ
  by_cases hsmallE : E ≤ 2 * N
  · nlinarith
  have hE_two : 2 * N < E := lt_of_not_ge hsmallE
  have hES' : E ^ 2 ≤ 2 * N * S := by
    nlinarith [mul_nonneg hN hE]
  by_cases hsmallS : S ≤ 2 * M ^ 2
  · have hEroot : E ≤ 2 * M * Real.sqrt N := by
      have hNS := mul_le_mul_of_nonneg_left hsmallS hN
      have hsq : E ^ 2 ≤ (2 * M * Real.sqrt N) ^ 2 := by
        nlinarith [hES', hNS]
      exact (sq_le_sq₀ hE (mul_nonneg (mul_nonneg (by positivity) hM) hsN)).mp hsq
    nlinarith [mul_nonneg hsMN hssQ]
  · have hS_two : 2 * M ^ 2 < S := lt_of_not_ge hsmallS
    have hSQ' : S ^ 2 ≤ 2 * M ^ 2 * Q := by
      nlinarith [mul_nonneg (sq_nonneg M) hS]
    have hSroot : S ≤ 2 * M * Real.sqrt Q := by
      have hsq : S ^ 2 ≤ (2 * M * Real.sqrt Q) ^ 2 := by
        nlinarith [mul_nonneg (sq_nonneg M) hQ]
      exact (sq_le_sq₀ hS (mul_nonneg (mul_nonneg (by positivity) hM) hsQ)).mp hsq
    have hEroot : E ≤ 2 * Real.sqrt (M * N) * Real.sqrt (Real.sqrt Q) := by
      have hNS := mul_le_mul_of_nonneg_left hSroot hN
      have hsq : E ^ 2 ≤
          (2 * Real.sqrt (M * N) * Real.sqrt (Real.sqrt Q)) ^ 2 := by
        nlinarith [hES', hNS]
      exact (sq_le_sq₀ hE
        (mul_nonneg (mul_nonneg (by positivity) hsMN) hssQ)).mp hsq
    nlinarith [mul_nonneg hM hsN]

/-- Rectangle supersaturation / KST with explicit constant `2`, for the
ordered rectangle convention of this file. -/
theorem edgeCount_le (G : BipartiteGraph L R) :
    edgeCount G ≤ 2 * (Fintype.card R : ℝ) +
      2 * (Fintype.card L : ℝ) * Real.sqrt (Fintype.card R : ℝ) +
      2 * Real.sqrt ((Fintype.card L : ℝ) * Fintype.card R) *
        Real.sqrt (Real.sqrt (rectangleCount G)) := by
  apply kst_numeric (hE := edgeCount_nonneg G) (hS := twoPathCount_nonneg G)
    (hQ := rectangleCount_nonneg G) (hM := Nat.cast_nonneg _) (hN := Nat.cast_nonneg _)
    (edgeCount_sq_le G)
  exact twoPathCount_sq_le G

/-! ### Coloured rectangles -/

/-- A specified ordered quadruple is a genuine rectangle in `G`. -/
def ContainsRectangle (G : BipartiteGraph L R) (x x' : L) (y y' : R) : Prop :=
  x ≠ x' ∧ y ≠ y' ∧ G x y ∧ G x' y ∧ G x y' ∧ G x' y'

/-- Indicator of a specified ordered rectangle. -/
def rectangleIndicator (G : BipartiteGraph L R) (x x' : L) (y y' : R) : ℝ :=
  if ContainsRectangle G x x' y y' then 1 else 0

lemma rectangleCount_eq_sum_indicator (G : BipartiteGraph L R) :
    rectangleCount G =
      ∑ x : L, ∑ x' : L, ∑ y : R, ∑ y' : R,
        rectangleIndicator G x x' y y' := by
  classical
  simp only [rectangleCount]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro x' hx'
  by_cases hxx : x = x'
  · simp [hxx, rectangleIndicator, ContainsRectangle]
  simp only [hxx, ↓reduceIte]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro y' hy'
  simp only [rectangleIndicator, ContainsRectangle]
  by_cases hyy : y = y'
  · simp [hyy]
  by_cases h1 : G x y <;> by_cases h2 : G x' y <;>
    by_cases h3 : G x y' <;> by_cases h4 : G x' y' <;>
    simp [hxx, hyy, h1, h2, h3, h4, edgeIndicator]

/-- Distinct colors never contain the same ordered rectangle. -/
def NoRepeatedRectangle {Γ : Type w} [Fintype Γ]
    (G : Γ → BipartiteGraph L R) : Prop :=
  ∀ γ δ, γ ≠ δ → ∀ x x' y y',
    ContainsRectangle (G γ) x x' y y' → ¬ ContainsRectangle (G δ) x x' y y'

variable {Γ : Type w} [Fintype Γ]

private lemma sum_rectangleIndicator_le_one (G : Γ → BipartiteGraph L R)
    (hG : NoRepeatedRectangle G) (x x' : L) (y y' : R) :
    (∑ γ : Γ, rectangleIndicator (G γ) x x' y y') ≤ 1 := by
  classical
  let s : Finset Γ := Finset.univ.filter fun γ ↦ ContainsRectangle (G γ) x x' y y'
  have hs : s.card ≤ 1 := Finset.card_le_one.mpr (by
    intro γ hγ δ hδ
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hγ hδ
    by_contra hne
    exact (hG γ δ hne x x' y y' hγ) hδ)
  have hsum : (∑ γ : Γ, rectangleIndicator (G γ) x x' y y') = (s.card : ℝ) := by
    simp [rectangleIndicator, s]
  rw [hsum]
  exact_mod_cast hs

/-- Under the no-repetition hypothesis, the total ordered rectangle count is
at most the number of ordered quadruples. -/
theorem sum_rectangleCount_le (G : Γ → BipartiteGraph L R)
    (hG : NoRepeatedRectangle G) :
    (∑ γ : Γ, rectangleCount (G γ)) ≤
      (Fintype.card L : ℝ) ^ 2 * (Fintype.card R : ℝ) ^ 2 := by
  simp_rw [rectangleCount_eq_sum_indicator]
  calc
    (∑ γ : Γ, ∑ x : L, ∑ x' : L, ∑ y : R, ∑ y' : R,
        rectangleIndicator (G γ) x x' y y') =
      ∑ x : L, ∑ x' : L, ∑ y : R, ∑ y' : R, ∑ γ : Γ,
        rectangleIndicator (G γ) x x' y y' := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x' hx'
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_comm]
    _ ≤ ∑ _x : L, ∑ _x' : L, ∑ _y : R, ∑ _y' : R, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro x' hx'
      apply Finset.sum_le_sum
      intro y hy
      apply Finset.sum_le_sum
      intro y' hy'
      exact sum_rectangleIndicator_le_one G hG x x' y y'
    _ = _ := by
      simp [pow_two]
      ring

/-- Finite Hölder at exponent four, in the nested-square-root form used by
the colored KST estimate. -/
lemma sum_sqrt_sqrt_le (f : Γ → ℝ) (hf : ∀ γ, 0 ≤ f γ) :
    (∑ γ : Γ, Real.sqrt (Real.sqrt (f γ))) ≤
      Real.sqrt ((Fintype.card Γ : ℝ) *
        Real.sqrt ((Fintype.card Γ : ℝ) * ∑ γ : Γ, f γ)) := by
  let a : Γ → ℝ := fun γ ↦ Real.sqrt (Real.sqrt (f γ))
  let A : ℝ := ∑ γ : Γ, a γ
  let T : ℝ := Fintype.card Γ
  let Q : ℝ := ∑ γ : Γ, f γ
  let B : ℝ := Real.sqrt (T * Real.sqrt (T * Q))
  have ha : ∀ γ, 0 ≤ a γ := fun γ ↦ Real.sqrt_nonneg _
  have hA : 0 ≤ A := Finset.sum_nonneg fun γ _ ↦ ha γ
  have hT : 0 ≤ T := by simp [T]
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun γ _ ↦ hf γ
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have ha4 : ∀ γ, (a γ) ^ 4 = f γ := by
    intro γ
    have h1 : (Real.sqrt (f γ)) ^ 2 = f γ := Real.sq_sqrt (hf γ)
    have h2 : (Real.sqrt (Real.sqrt (f γ))) ^ 2 = Real.sqrt (f γ) :=
      Real.sq_sqrt (Real.sqrt_nonneg _)
    simp only [a]
    calc
      (Real.sqrt (Real.sqrt (f γ))) ^ 4 =
          ((Real.sqrt (Real.sqrt (f γ))) ^ 2) ^ 2 := by ring
      _ = _ := by rw [h2, h1]
  have hp := pow_sum_le_card_mul_sum_pow
    (s := (Finset.univ : Finset Γ)) (f := a) (fun γ _ ↦ ha γ) 3
  have hp' : A ^ 4 ≤ T ^ 3 * Q := by
    simpa only [A, T, Q, Nat.reduceAdd, Finset.card_univ, ha4] using hp
  have hTQ : 0 ≤ T * Q := mul_nonneg hT hQ
  have hTsqrt : 0 ≤ T * Real.sqrt (T * Q) :=
    mul_nonneg hT (Real.sqrt_nonneg _)
  have hinner : (Real.sqrt (T * Q)) ^ 2 = T * Q := Real.sq_sqrt hTQ
  have houter : B ^ 2 = T * Real.sqrt (T * Q) := by
    simp only [B]
    exact Real.sq_sqrt hTsqrt
  have hB4 : B ^ 4 = T ^ 3 * Q := by
    calc
      B ^ 4 = (B ^ 2) ^ 2 := by ring
      _ = (T * Real.sqrt (T * Q)) ^ 2 := by rw [houter]
      _ = T ^ 3 * Q := by rw [mul_pow, hinner]; ring
  have hfour : A ^ 4 ≤ B ^ 4 := by rwa [hB4]
  have hsq : A ^ 2 ≤ B ^ 2 := by
    apply (sq_le_sq₀ (sq_nonneg A) (sq_nonneg B)).mp
    calc
      (A ^ 2) ^ 2 = A ^ 4 := by ring
      _ ≤ B ^ 4 := hfour
      _ = (B ^ 2) ^ 2 := by ring
  have hAB : A ≤ B := (sq_le_sq₀ hA hB).mp hsq
  simpa only [A, B, T, Q, a] using hAB

/-- Colored KST / rectangle supersaturation.  The first two terms are the
degenerate contribution.  The final nested square root is exactly
`T^(3/4) M N`, written without real powers; thus this is the explicit-constant
version of Lemma 6.2 in the mathematical write-up. -/
theorem sum_edgeCount_le (G : Γ → BipartiteGraph L R)
    (hG : NoRepeatedRectangle G) :
    (∑ γ : Γ, edgeCount (G γ)) ≤
      2 * (Fintype.card Γ : ℝ) * Fintype.card R +
      2 * (Fintype.card Γ : ℝ) * Fintype.card L *
        Real.sqrt (Fintype.card R : ℝ) +
      2 * Real.sqrt ((Fintype.card L : ℝ) * Fintype.card R) *
        Real.sqrt ((Fintype.card Γ : ℝ) *
          Real.sqrt ((Fintype.card Γ : ℝ) *
            (Fintype.card L : ℝ) ^ 2 * (Fintype.card R : ℝ) ^ 2)) := by
  let T : ℝ := Fintype.card Γ
  let M : ℝ := Fintype.card L
  let N : ℝ := Fintype.card R
  let C : ℝ := 2 * Real.sqrt (M * N)
  let D : ℝ := 2 * N + 2 * M * Real.sqrt N
  let Q : Γ → ℝ := fun γ ↦ rectangleCount (G γ)
  have hT : 0 ≤ T := by simp [T]
  have hC : 0 ≤ C := by positivity
  have hsum : (∑ γ : Γ, edgeCount (G γ)) ≤
      T * D + C * ∑ γ : Γ, Real.sqrt (Real.sqrt (Q γ)) := by
    calc
      (∑ γ : Γ, edgeCount (G γ)) ≤
          ∑ γ : Γ, (D + C * Real.sqrt (Real.sqrt (Q γ))) := by
        apply Finset.sum_le_sum
        intro γ hγ
        simpa only [D, C, M, N, Q, add_assoc] using edgeCount_le (G γ)
      _ = T * D + C * ∑ γ : Γ, Real.sqrt (Real.sqrt (Q γ)) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum, Finset.card_univ]
        simp only [T]
  have hholder : (∑ γ : Γ, Real.sqrt (Real.sqrt (Q γ))) ≤
      Real.sqrt (T * Real.sqrt (T * ∑ γ : Γ, Q γ)) := by
    simpa only [T, Q] using
      sum_sqrt_sqrt_le Q (fun γ ↦ rectangleCount_nonneg (G γ))
  have hrect : (∑ γ : Γ, Q γ) ≤ M ^ 2 * N ^ 2 := by
    simpa only [Q, M, N] using sum_rectangleCount_le G hG
  have hinner : T * (∑ γ : Γ, Q γ) ≤ T * (M ^ 2 * N ^ 2) :=
    mul_le_mul_of_nonneg_left hrect hT
  have hsqrtInner : Real.sqrt (T * ∑ γ : Γ, Q γ) ≤
      Real.sqrt (T * (M ^ 2 * N ^ 2)) := Real.sqrt_le_sqrt hinner
  have houter : T * Real.sqrt (T * ∑ γ : Γ, Q γ) ≤
      T * Real.sqrt (T * (M ^ 2 * N ^ 2)) :=
    mul_le_mul_of_nonneg_left hsqrtInner hT
  have hnested : Real.sqrt (T * Real.sqrt (T * ∑ γ : Γ, Q γ)) ≤
      Real.sqrt (T * Real.sqrt (T * (M ^ 2 * N ^ 2))) := Real.sqrt_le_sqrt houter
  calc
    (∑ γ : Γ, edgeCount (G γ)) ≤
        T * D + C * ∑ γ : Γ, Real.sqrt (Real.sqrt (Q γ)) := hsum
    _ ≤ T * D + C * Real.sqrt (T * Real.sqrt (T * ∑ γ : Γ, Q γ)) := by
      gcongr
    _ ≤ T * D + C * Real.sqrt (T * Real.sqrt (T * (M ^ 2 * N ^ 2))) := by
      gcongr
    _ = _ := by
      simp only [T, M, N, C, D]
      ring

end
end ColoredGraph
end Erdos888

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos147/Basic.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Erdős Problem 147

This file formalizes the negative resolution of the Erdős--Simonovits
minimum-degree conjecture.  The concrete counterexample is the two-fold
blow-up of the twelve-cycle, `C₁₂[2]`.  It is bipartite and 4-regular, while
Janzer's blow-up-cycle estimate gives an extremal exponent strictly below
`2 - 1 / (4 - 1) = 5 / 3`.

The detailed mathematical reconstruction, including the complete dependency
list for Janzer's counting argument, is in `tex/147.tex`.
-/

open Filter
open Asymptotics
open scoped SimpleGraph Topology



set_option autoImplicit false

/-- The real-valued extremal-number function of a fixed finite graph. -/
noncomputable def extremalGrowth {W : Type*} (H : SimpleGraph W) (n : ℕ) : ℝ :=
  SimpleGraph.extremalNumber n H

/-- The real power `n ↦ n ^ a` on natural inputs. -/
noncomputable def polynomialGrowth (a : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ a

/-- The lower bound predicted by Erdős and Simonovits for a graph of minimum
degree `r`.  The division in the exponent is real division. -/
def HasConjecturedLowerBound {W : Type*} (H : SimpleGraph W) (r : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    (polynomialGrowth (2 - 1 / ((r : ℝ) - 1) + ε)) =O[atTop] extremalGrowth H

/-- The `r`-fold blow-up of the cycle on `m` vertices. -/
def blowupCycle (m r : ℕ) : SimpleGraph (Fin m × Fin r) :=
  (SimpleGraph.cycleGraph m).comap Prod.fst

instance blowupCycle.instDecidableAdj (m r : ℕ) :
    DecidableRel (blowupCycle m r).Adj := by
  dsimp only [blowupCycle]
  infer_instance

/-- The fixed graph used to refute the conjecture. -/
abbrev counterexampleGraph : SimpleGraph (Fin 12 × Fin 2) := blowupCycle 12 2

lemma counterexampleGraph_isBipartite : counterexampleGraph.IsBipartite := by
  let c : (SimpleGraph.cycleGraph 12).Coloring Bool :=
    SimpleGraph.cycleGraph.bicoloring_of_even 12 ⟨6, by norm_num⟩
  exact (c.comap (SimpleGraph.Hom.comap Prod.fst
    (SimpleGraph.cycleGraph 12))).colorable

lemma counterexampleGraph_isRegular : counterexampleGraph.IsRegularOfDegree 4 := by
  intro v
  fin_cases v <;> decide

lemma counterexampleGraph_minDegree : counterexampleGraph.minDegree = 4 :=
  counterexampleGraph_isRegular.minDegree_eq

/-! ## The ordered-pair auxiliary graph -/

/-- Ordered pairs of distinct vertices.  Retaining the order removes all
quotients from the finite counting argument; each unordered two-set occurs
twice. -/
abbrev OrderedPair (V : Type*) := {p : V × V // p.1 ≠ p.2}

def orderedPairSupport {V : Type*} [DecidableEq V] (p : OrderedPair V) : Finset V :=
  {p.1.1, p.1.2}

@[simp] lemma mem_orderedPairSupport {V : Type*} [DecidableEq V]
    (p : OrderedPair V) (v : V) :
    v ∈ orderedPairSupport p ↔ v = p.1.1 ∨ v = p.1.2 := by
  simp [orderedPairSupport]

/-- Two ordered pairs are adjacent when they span a complete bipartite
`K₂,₂` in the host graph. -/
def pairComplete {V : Type*} (G : SimpleGraph V)
    (p q : OrderedPair V) : Prop :=
  G.Adj p.1.1 q.1.1 ∧ G.Adj p.1.1 q.1.2 ∧
    G.Adj p.1.2 q.1.1 ∧ G.Adj p.1.2 q.1.2

lemma pairComplete_comm {V : Type*} (G : SimpleGraph V) (p q : OrderedPair V) :
    pairComplete G p q ↔ pairComplete G q p := by
  constructor
  · rintro ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩
    exact ⟨h₁₁.symm, h₂₁.symm, h₁₂.symm, h₂₂.symm⟩
  · rintro ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩
    exact ⟨h₁₁.symm, h₂₁.symm, h₁₂.symm, h₂₂.symm⟩

lemma pairComplete_irrefl {V : Type*} (G : SimpleGraph V) (p : OrderedPair V) :
    ¬pairComplete G p p := by
  intro h
  exact G.irrefl h.1

def pairAuxGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph (OrderedPair V) where
  Adj := pairComplete G
  symm := by
    constructor
    exact fun _ _ h ↦ (pairComplete_comm G _ _).mp h
  loopless := by
    constructor
    exact pairComplete_irrefl G

instance pairAuxGraph.instDecidableAdj {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] : DecidableRel (pairAuxGraph G).Adj := by
  intro p q
  dsimp only [pairAuxGraph, pairComplete]
  infer_instance

lemma pairComplete_support_disjoint {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {p q : OrderedPair V} (hpq : pairComplete G p q) :
    Disjoint (orderedPairSupport p) (orderedPairSupport q) := by
  rw [Finset.disjoint_left]
  intro v hvp hvq
  simp only [mem_orderedPairSupport] at hvp hvq
  rcases hvp with hvp | hvp <;> rcases hvq with hvq | hvq
  · exact hpq.1.ne (hvp.symm.trans hvq)
  · exact hpq.2.1.ne (hvp.symm.trans hvq)
  · exact hpq.2.2.1.ne (hvp.symm.trans hvq)
  · exact hpq.2.2.2.ne (hvp.symm.trans hvq)

def orderedPairEntry {V : Type*} (p : OrderedPair V) (i : Fin 2) : V :=
  if i = 0 then p.1.1 else p.1.2

def pairCommonFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : OrderedPair V) : Finset V :=
  G.neighborFinset p.1.1 ∩ G.neighborFinset p.1.2

@[simp] lemma mem_pairCommonFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : OrderedPair V) (v : V) :
    v ∈ pairCommonFinset G p ↔ G.Adj p.1.1 v ∧ G.Adj p.1.2 v := by
  simp [pairCommonFinset]

lemma pairAuxGraph_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : OrderedPair V) :
    (pairAuxGraph G).degree p =
      (pairCommonFinset G p).card * ((pairCommonFinset G p).card - 1) := by
  classical
  let s := pairCommonFinset G p
  have hcard : ((pairAuxGraph G).neighborFinset p).card = s.offDiag.card := by
    apply Finset.card_bij (fun q _ ↦ q.1)
    · intro q hq
      rw [Finset.mem_offDiag]
      have hadj := ((pairAuxGraph G).mem_neighborFinset p q).mp hq
      exact ⟨by simpa [s] using ⟨hadj.1, hadj.2.2.1⟩,
        by simpa [s] using ⟨hadj.2.1, hadj.2.2.2⟩, q.property⟩
    · intro q₁ hq₁ q₂ hq₂ heq
      exact Subtype.ext heq
    · intro z hz
      rw [Finset.mem_offDiag] at hz
      let q : OrderedPair V := ⟨z, hz.2.2⟩
      refine ⟨q, ?_, rfl⟩
      rw [(pairAuxGraph G).mem_neighborFinset]
      have hz₁ := (mem_pairCommonFinset G p z.1).mp (by simpa [s] using hz.1)
      have hz₂ := (mem_pairCommonFinset G p z.2).mp (by simpa [s] using hz.2.1)
      exact ⟨hz₁.1, hz₂.1, hz₁.2, hz₂.2⟩
  rw [SimpleGraph.degree, hcard, Finset.offDiag_card]
  simp [s, mul_tsub_one]

abbrev LocalConflictNeighbor {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : OrderedPair V) :=
  {z : OrderedPair V // pairComplete G y z ∧
    ¬Disjoint (orderedPairSupport x) (orderedPairSupport z)}

def conflictDecoder {V : Type*} (x : OrderedPair V) (r : Fin 4 × V) : V × V :=
  if r.1 = 0 then (x.1.1, r.2)
  else if r.1 = 1 then (x.1.2, r.2)
  else if r.1 = 2 then (r.2, x.1.1)
  else (r.2, x.1.2)

lemma localConflictNeighbor_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : OrderedPair V) :
    Nat.card (LocalConflictNeighbor G x y) ≤
      4 * (pairCommonFinset G y).card := by
  classical
  letI : Fintype (LocalConflictNeighbor G x y) := Fintype.ofFinite _
  let s := pairCommonFinset G y
  have hrepr : ∀ z : LocalConflictNeighbor G x y,
      ∃ r : Fin 4 × {v // v ∈ s}, conflictDecoder x (r.1, r.2.1) = z.1.1 := by
    intro z
    have hadj := z.2.1
    have hcases :
        z.1.1.1 = x.1.1 ∨ z.1.1.1 = x.1.2 ∨
        z.1.1.2 = x.1.1 ∨ z.1.1.2 = x.1.2 := by
      have hn := z.2.2
      simp only [Finset.not_disjoint_iff] at hn
      obtain ⟨v, hvx, hvz⟩ := hn
      simp only [mem_orderedPairSupport] at hvx hvz
      rcases hvx with hvx | hvx <;> rcases hvz with hvz | hvz
      · exact Or.inl (hvz.symm.trans hvx)
      · exact Or.inr (Or.inr (Or.inl (hvz.symm.trans hvx)))
      · exact Or.inr (Or.inl (hvz.symm.trans hvx))
      · exact Or.inr (Or.inr (Or.inr (hvz.symm.trans hvx)))
    rcases hcases with h | h | h | h
    · refine ⟨(0, ⟨z.1.1.2, ?_⟩), ?_⟩
      · simpa [s] using (show G.Adj y.1.1 z.1.1.2 ∧ G.Adj y.1.2 z.1.1.2 from
          ⟨hadj.2.1, hadj.2.2.2⟩)
      · apply Prod.ext
        · simpa [conflictDecoder] using h.symm
        · simp [conflictDecoder]
    · refine ⟨(1, ⟨z.1.1.2, ?_⟩), ?_⟩
      · simpa [s] using (show G.Adj y.1.1 z.1.1.2 ∧ G.Adj y.1.2 z.1.1.2 from
          ⟨hadj.2.1, hadj.2.2.2⟩)
      · apply Prod.ext
        · simpa [conflictDecoder] using h.symm
        · simp [conflictDecoder]
    · refine ⟨(2, ⟨z.1.1.1, ?_⟩), ?_⟩
      · simpa [s] using (show G.Adj y.1.1 z.1.1.1 ∧ G.Adj y.1.2 z.1.1.1 from
          ⟨hadj.1, hadj.2.2.1⟩)
      · apply Prod.ext
        · simp [conflictDecoder]
        · simpa [conflictDecoder] using h.symm
    · refine ⟨(3, ⟨z.1.1.1, ?_⟩), ?_⟩
      · simpa [s] using (show G.Adj y.1.1 z.1.1.1 ∧ G.Adj y.1.2 z.1.1.1 from
          ⟨hadj.1, hadj.2.2.1⟩)
      · have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        apply Prod.ext
        · simp [conflictDecoder, h30, h31, h32]
        · simpa [conflictDecoder, h30, h31, h32] using h.symm
  let encode : LocalConflictNeighbor G x y → Fin 4 × {v // v ∈ s} :=
    fun z ↦ Classical.choose (hrepr z)
  have hencode : ∀ z, conflictDecoder x ((encode z).1, (encode z).2.1) = z.1.1 :=
    fun z ↦ Classical.choose_spec (hrepr z)
  have hinj : Function.Injective encode := by
    intro z w hzw
    apply Subtype.ext
    apply Subtype.ext
    rw [← hencode z, ← hencode w, hzw]
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card (LocalConflictNeighbor G x y) ≤
        Fintype.card (Fin 4 × {v // v ∈ s}) := Fintype.card_le_of_injective encode hinj
    _ = 4 * s.card := by simp [Fintype.card_prod]
    _ = 4 * (pairCommonFinset G y).card := by rfl

lemma commonCard_le_sqrt_degree_add_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : OrderedPair V) :
    ((pairCommonFinset G p).card : ℝ) ≤
      Real.sqrt ((pairAuxGraph G).degree p : ℝ) + 1 := by
  let d := (pairCommonFinset G p).card
  by_cases hd : d = 0
  · have hdegree0 : (pairAuxGraph G).degree p = 0 := by
      rw [pairAuxGraph_degree]
      simp [d, hd]
    simp [d, hd, hdegree0]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
  have hd1nat : (1 : ℕ) ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  have hdegree : ((pairAuxGraph G).degree p : ℝ) = (d : ℝ) * (d - 1) := by
    rw [pairAuxGraph_degree]
    change (↑(d * (d - 1)) : ℝ) = (d : ℝ) * (d - 1)
    rw [Nat.cast_mul, Nat.cast_sub hd1nat, Nat.cast_one]
  have hprod : 0 ≤ (d : ℝ) * (d - 1) := mul_nonneg (by positivity) (sub_nonneg.mpr hd1)
  have hsqrt_sq : (Real.sqrt ((d : ℝ) * (d - 1))) ^ 2 = (d : ℝ) * (d - 1) :=
    Real.sq_sqrt hprod
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((d : ℝ) * (d - 1)) := Real.sqrt_nonneg _
  rw [hdegree]
  nlinarith [sq_nonneg ((d : ℝ) - 1)]

lemma localConflictNeighbor_card_real_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : OrderedPair V) :
    (Nat.card (LocalConflictNeighbor G x y) : ℝ) ≤
      4 * (Real.sqrt ((pairAuxGraph G).degree y : ℝ) + 1) := by
  calc
    (Nat.card (LocalConflictNeighbor G x y) : ℝ) ≤
        4 * ((pairCommonFinset G y).card : ℝ) := by
      exact_mod_cast localConflictNeighbor_card_le G x y
    _ ≤ 4 * (Real.sqrt ((pairAuxGraph G).degree y : ℝ) + 1) := by
      gcongr
      exact commonCard_le_sqrt_degree_add_one G y

lemma orderedPairEntry_mem_support {V : Type*} [DecidableEq V]
    (p : OrderedPair V) (i : Fin 2) :
    orderedPairEntry p i ∈ orderedPairSupport p := by
  fin_cases i <;> simp [orderedPairEntry, orderedPairSupport]

lemma orderedPairEntry_injective {V : Type*} (p : OrderedPair V) :
    Function.Injective (orderedPairEntry p) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact (p.property (by simpa [orderedPairEntry] using hij)).elim
  · exact (p.property (by simpa [orderedPairEntry] using hij.symm)).elim
  · rfl

lemma pairComplete_entries {V : Type*} (G : SimpleGraph V)
    {p q : OrderedPair V} (hpq : pairComplete G p q) (i j : Fin 2) :
    G.Adj (orderedPairEntry p i) (orderedPairEntry q j) := by
  fin_cases i <;> fin_cases j
  · simpa [orderedPairEntry] using hpq.1
  · simpa [orderedPairEntry] using hpq.2.1
  · simpa [orderedPairEntry] using hpq.2.2.1
  · simpa [orderedPairEntry] using hpq.2.2.2

/-- A cycle in the auxiliary graph whose ordered pairs have pairwise
disjoint supports is an actual copy of `C₁₂[2]` in the host graph. -/
lemma counterexampleGraph_isContained_of_disjoint_auxCycle
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (c : SimpleGraph.cycleGraph 12 →g pairAuxGraph G)
    (hdisjoint : ∀ i j : Fin 12, i ≠ j →
      Disjoint (orderedPairSupport (c i)) (orderedPairSupport (c j))) :
    counterexampleGraph ⊑ G := by
  let f : Fin 12 × Fin 2 → V := fun x ↦ orderedPairEntry (c x.1) x.2
  let hom : counterexampleGraph →g G :=
    { toFun := f
      map_rel' := by
        intro x y hxy
        exact pairComplete_entries G (c.map_adj hxy) x.2 y.2 }
  have hinj : Function.Injective f := by
    intro x y hxy
    by_cases hfirst : x.1 = y.1
    · apply Prod.ext hfirst
      apply orderedPairEntry_injective (c x.1)
      simpa [f, hfirst] using hxy
    · have hxmem : f x ∈ orderedPairSupport (c x.1) :=
        orderedPairEntry_mem_support _ _
      have hymem : f y ∈ orderedPairSupport (c y.1) :=
        orderedPairEntry_mem_support _ _
      have hd := Finset.disjoint_left.mp (hdisjoint x.1 y.1 hfirst)
      exact (hd hxmem (hxy ▸ hymem)).elim
  exact ⟨hom.toCopy hinj⟩

/-! ## Closed-walk counts -/

noncomputable def walkCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (u v : V) : ℝ :=
  (G.adjMatrix ℝ ^ j) u v

noncomputable def homCycleCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) : ℝ :=
  Matrix.trace (G.adjMatrix ℝ ^ j)

lemma walkCount_eq_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (u v : V) :
    walkCount G j u v = Fintype.card {p : G.Walk u v // p.length = j} := by
  exact G.adjMatrix_pow_apply_eq_card_walk j u v

lemma walkCount_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (u v : V) :
    0 ≤ walkCount G j u v := by
  rw [walkCount_eq_card]
  positivity

lemma walkCount_comm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (u v : V) :
    walkCount G j u v = walkCount G j v u := by
  change (G.adjMatrix ℝ ^ j) u v = (G.adjMatrix ℝ ^ j) v u
  have htranspose : Matrix.transpose (G.adjMatrix ℝ ^ j) = G.adjMatrix ℝ ^ j := by
    rw [Matrix.transpose_pow, G.transpose_adjMatrix]
  simpa [Matrix.transpose_apply] using congrFun₂ htranspose v u

lemma homCycleCount_even_eq_sum_sq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) :
    homCycleCount G (2 * j) = ∑ u : V, ∑ v : V, walkCount G j u v ^ 2 := by
  rw [homCycleCount]
  have hpow : G.adjMatrix ℝ ^ (2 * j) =
      G.adjMatrix ℝ ^ j * G.adjMatrix ℝ ^ j := by
    rw [show 2 * j = j + j by omega, pow_add]
  rw [hpow]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  change walkCount G j u v * walkCount G j v u = walkCount G j u v ^ 2
  rw [walkCount_comm]
  ring

lemma homCycleCount_even_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) :
    0 ≤ homCycleCount G (2 * j) := by
  rw [homCycleCount_even_eq_sum_sq]
  positivity

lemma homCycleCount_add_eq_sum_mul {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b : ℕ) :
    homCycleCount G (a + b) =
      ∑ u : V, ∑ v : V, walkCount G a u v * walkCount G b u v := by
  rw [homCycleCount, pow_add]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  change walkCount G a u v * walkCount G b v u =
    walkCount G a u v * walkCount G b u v
  rw [walkCount_comm G b v u]

lemma homCycleCount_logConvex {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (hj : 1 ≤ j) :
    homCycleCount G (2 * j) ^ 2 ≤
      homCycleCount G (2 * (j - 1)) * homCycleCount G (2 * (j + 1)) := by
  let f : V × V → ℝ := fun z ↦ walkCount G (j - 1) z.1 z.2
  let g : V × V → ℝ := fun z ↦ walkCount G (j + 1) z.1 z.2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (V × V)) f g
  have hmiddle : homCycleCount G (2 * j) = ∑ z : V × V, f z * g z := by
    rw [show 2 * j = (j - 1) + (j + 1) by omega,
      homCycleCount_add_eq_sum_mul]
    simp only [f, g, Fintype.sum_prod_type]
  have hleft : homCycleCount G (2 * (j - 1)) = ∑ z : V × V, f z ^ 2 := by
    rw [homCycleCount_even_eq_sum_sq]
    simp only [f, Fintype.sum_prod_type]
  have hright : homCycleCount G (2 * (j + 1)) = ∑ z : V × V, g z ^ 2 := by
    rw [homCycleCount_even_eq_sum_sq]
    simp only [g, Fintype.sum_prod_type]
  rwa [← hmiddle, ← hleft, ← hright] at hcs

lemma homCycleCount_ten_pow_five_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    homCycleCount G 10 ^ 5 ≤ homCycleCount G 2 * homCycleCount G 12 ^ 4 := by
  let h1 := homCycleCount G 2
  let h2 := homCycleCount G 4
  let h3 := homCycleCount G 6
  let h4 := homCycleCount G 8
  let h5 := homCycleCount G 10
  let h6 := homCycleCount G 12
  have hn1 : 0 ≤ h1 := by simpa [h1] using homCycleCount_even_nonneg G 1
  have hn2 : 0 ≤ h2 := by simpa [h2] using homCycleCount_even_nonneg G 2
  have hn3 : 0 ≤ h3 := by simpa [h3] using homCycleCount_even_nonneg G 3
  have hn4 : 0 ≤ h4 := by simpa [h4] using homCycleCount_even_nonneg G 4
  have hn5 : 0 ≤ h5 := by simpa [h5] using homCycleCount_even_nonneg G 5
  have hn6 : 0 ≤ h6 := by simpa [h6] using homCycleCount_even_nonneg G 6
  have hc2 : h2 ^ 2 ≤ h1 * h3 := by
    simpa [h1, h2, h3] using homCycleCount_logConvex G 2 (by omega)
  have hc3 : h3 ^ 2 ≤ h2 * h4 := by
    simpa [h2, h3, h4] using homCycleCount_logConvex G 3 (by omega)
  have hc4 : h4 ^ 2 ≤ h3 * h5 := by
    simpa [h3, h4, h5] using homCycleCount_logConvex G 4 (by omega)
  have hc5 : h5 ^ 2 ≤ h4 * h6 := by
    simpa [h4, h5, h6] using homCycleCount_logConvex G 5 (by omega)
  change h5 ^ 5 ≤ h1 * h6 ^ 4
  by_cases hz : h5 = 0
  · simpa [hz] using mul_nonneg hn1 (pow_nonneg hn6 4)
  have hp5 : 0 < h5 := lt_of_le_of_ne hn5 (Ne.symm hz)
  have hp4 : 0 < h4 := by
    have hp : 0 < h4 * h6 := (sq_pos_of_pos hp5).trans_le hc5
    exact pos_of_mul_pos_left hp hn6
  have hp3 : 0 < h3 := by
    have hp : 0 < h3 * h5 := (sq_pos_of_pos hp4).trans_le hc4
    exact pos_of_mul_pos_left hp hn5
  have hp2 : 0 < h2 := by
    have hp : 0 < h2 * h4 := (sq_pos_of_pos hp3).trans_le hc3
    exact pos_of_mul_pos_left hp hn4
  have hp1 : 0 < h1 := by
    have hp : 0 < h1 * h3 := (sq_pos_of_pos hp2).trans_le hc2
    exact pos_of_mul_pos_left hp hn3
  have hr2 : h2 / h1 ≤ h3 / h2 := by
    rw [div_le_div_iff₀ hp1 hp2]
    simpa [pow_two, mul_comm] using hc2
  have hr3 : h3 / h2 ≤ h4 / h3 := by
    rw [div_le_div_iff₀ hp2 hp3]
    simpa [pow_two, mul_comm] using hc3
  have hr4 : h4 / h3 ≤ h5 / h4 := by
    rw [div_le_div_iff₀ hp3 hp4]
    simpa [pow_two, mul_comm] using hc4
  have hr5 : h5 / h4 ≤ h6 / h5 := by
    rw [div_le_div_iff₀ hp4 hp5]
    simpa [pow_two, mul_comm] using hc5
  have htel : h5 / h1 =
      (h2 / h1) * (h3 / h2) * (h4 / h3) * (h5 / h4) := by
    field_simp
  have hq : 0 ≤ h6 / h5 := div_nonneg hn6 hn5
  have hs2 : h2 ≤ (h6 / h5) * h1 :=
    (div_le_iff₀ hp1).mp (hr2.trans (hr3.trans (hr4.trans hr5)))
  have hs3 : h3 ≤ (h6 / h5) * h2 :=
    (div_le_iff₀ hp2).mp (hr3.trans (hr4.trans hr5))
  have hs4 : h4 ≤ (h6 / h5) * h3 :=
    (div_le_iff₀ hp3).mp (hr4.trans hr5)
  have hs5 : h5 ≤ (h6 / h5) * h4 :=
    (div_le_iff₀ hp4).mp hr5
  have hratio' : h5 ≤ (h6 / h5) ^ 4 * h1 := by
    calc
      h5 ≤ (h6 / h5) * h4 := hs5
      _ ≤ (h6 / h5) * ((h6 / h5) * h3) :=
        mul_le_mul_of_nonneg_left hs4 hq
      _ ≤ (h6 / h5) * ((h6 / h5) * ((h6 / h5) * h2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hs3 hq) hq
      _ ≤ (h6 / h5) * ((h6 / h5) * ((h6 / h5) * ((h6 / h5) * h1))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hs2 hq) hq) hq
      _ = (h6 / h5) ^ 4 * h1 := by ring
  calc
    h5 ^ 5 = h5 * h5 ^ 4 := by ring
    _ ≤ ((h6 / h5) ^ 4 * h1) * h5 ^ 4 :=
      mul_le_mul_of_nonneg_right hratio' (pow_nonneg hn5 4)
    _ = h1 * h6 ^ 4 := by field_simp

abbrev ClosedWalk {V : Type*} (G : SimpleGraph V) (j : ℕ) :=
  Σ v : V, {p : G.Walk v v // p.length = j}

lemma homCycleCount_eq_card_closedWalk {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) :
    homCycleCount G j = Nat.card (ClosedWalk G j) := by
  rw [homCycleCount, Matrix.trace]
  simp only [Matrix.diag_apply, G.adjMatrix_pow_apply_eq_card_walk]
  rw [← Nat.cast_sum]
  norm_cast
  rw [Nat.card_sigma]
  simp only [Nat.card_eq_fintype_card]
  apply Finset.sum_congr rfl
  intro v hv
  rfl

lemma cycleGraph12_adj_iff (i j : Fin 12) :
    (SimpleGraph.cycleGraph 12).Adj i j ↔
      i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 ∨
      (i.1 = 11 ∧ j.1 = 0) ∨ (j.1 = 11 ∧ i.1 = 0) := by
  decide +revert

def ClosedWalk.HasDisjointPairSupports {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : ClosedWalk (pairAuxGraph G) 12) : Prop :=
  ∀ i j : Fin 12, i ≠ j →
    Disjoint (orderedPairSupport (w.2.1.getVert i.1))
      (orderedPairSupport (w.2.1.getVert j.1))

lemma counterexampleGraph_isContained_of_goodClosedWalk
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : ClosedWalk (pairAuxGraph G) 12)
    (hw : w.HasDisjointPairSupports G) :
    counterexampleGraph ⊑ G := by
  let p := w.2.1
  have hpLength : p.length = 12 := w.2.2
  let c : SimpleGraph.cycleGraph 12 →g pairAuxGraph G :=
    { toFun := fun i ↦ p.getVert i.1
      map_rel' := by
        intro i j hij
        rcases (cycleGraph12_adj_iff i j).mp hij with h | h | h | h
        · have hadj := p.adj_getVert_succ (i := i.1) (by omega : i.1 < p.length)
          simpa [h] using hadj
        · have hadj := p.adj_getVert_succ (i := j.1) (by omega : j.1 < p.length)
          simpa [h] using hadj.symm
        · have hadj := p.adj_getVert_succ (i := 11) (by omega : 11 < p.length)
          have hend : p.getVert 12 = p.getVert 0 := by
            rw [p.getVert_of_length_le (by omega), p.getVert_zero]
          simpa [h.1, h.2, hend] using hadj
        · have hadj := p.adj_getVert_succ (i := 11) (by omega : 11 < p.length)
          have hend : p.getVert 12 = p.getVert 0 := by
            rw [p.getVert_of_length_le (by omega), p.getVert_zero]
          simpa [h.1, h.2, hend] using hadj.symm }
  apply counterexampleGraph_isContained_of_disjoint_auxCycle G c
  intro i j hij
  exact hw i j hij

abbrev BadClosedWalk {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  {w : ClosedWalk (pairAuxGraph G) 12 // ¬w.HasDisjointPairSupports G}

lemma homCycleCount_eq_card_badClosedWalk_of_free
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : counterexampleGraph.Free G) :
    homCycleCount (pairAuxGraph G) 12 = Nat.card (BadClosedWalk G) := by
  rw [homCycleCount_eq_card_closedWalk]
  apply congrArg Nat.cast
  apply Nat.card_congr
  let toBad : ClosedWalk (pairAuxGraph G) 12 → BadClosedWalk G := fun w ↦
    ⟨w, fun hw ↦ hfree (counterexampleGraph_isContained_of_goodClosedWalk G w hw)⟩
  exact
    { toFun := toBad
      invFun := fun w ↦ w.1
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-! ## The fixed `5+1+6` decomposition of a twelve-cycle -/

abbrev WalkOfLength {V : Type*} (G : SimpleGraph V) (j : ℕ) (u v : V) :=
  {p : G.Walk u v // p.length = j}

structure CycleSplit {V : Type*} (G : SimpleGraph V) where
  x₁ : V
  x₂ : V
  x₈ : V
  bridge : G.Adj x₁ x₂
  middle : WalkOfLength G 6 x₂ x₈
  tail : WalkOfLength G 5 x₈ x₁

instance CycleSplit.instFinite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finite (CycleSplit G) := by
  let e : CycleSplit G →
      Σ x₁ x₂ x₈ : V,
        WalkOfLength G 6 x₂ x₈ × WalkOfLength G 5 x₈ x₁ := fun c ↦
    ⟨c.x₁, c.x₂, c.x₈, c.middle, c.tail⟩
  exact Finite.of_injective e (by
    intro c d h
    cases c
    cases d
    cases h
    rfl)

def CycleSplit.toClosedWalk {V : Type*} {G : SimpleGraph V}
    (c : CycleSplit G) : ClosedWalk G 12 :=
  ⟨c.x₁, ⟨(c.middle.1.cons c.bridge).append c.tail.1, by
    simp [c.middle.2, c.tail.2]⟩⟩

noncomputable def CycleSplit.ofClosedWalk {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) : CycleSplit G := by
  let p := w.2.1
  have hp : p.length = 12 := w.2.2
  let x₂ := p.getVert 1
  let x₈ := p.getVert 7
  have hb : G.Adj w.1 x₂ := by
    simpa [p, x₂] using p.adj_getVert_succ (i := 0) (by omega)
  have hmLen : ((p.drop 1).take 6).length = 6 := by
    simp [hp]
  have hmEnd : (p.drop 1).getVert 6 = x₈ := by simp [x₈]
  let middle : WalkOfLength G 6 x₂ x₈ :=
    ⟨((p.drop 1).take 6).copy (by simp [x₂]) hmEnd, by simpa using hmLen⟩
  have htLen : (p.drop 7).length = 5 := by simp [hp]
  let tail : WalkOfLength G 5 x₈ w.1 :=
    ⟨(p.drop 7).copy (by simp [x₈]) rfl, by simpa using htLen⟩
  exact ⟨w.1, x₂, x₈, hb, middle, tail⟩

lemma CycleSplit.toClosedWalk_ofClosedWalk {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) :
    (CycleSplit.ofClosedWalk w).toClosedWalk = w := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Subtype.ext
  apply SimpleGraph.Walk.ext_getVert_le_length
  · exact (CycleSplit.ofClosedWalk w).toClosedWalk.2.2.trans w.2.2.symm
  intro k hk
  have hk' : k ≤ 12 := by
    rw [(CycleSplit.ofClosedWalk w).toClosedWalk.2.2] at hk
    exact hk
  interval_cases k <;>
    simp [CycleSplit.toClosedWalk, CycleSplit.ofClosedWalk, w.2.2,
      SimpleGraph.Walk.getVert_append, SimpleGraph.Walk.getVert_cons,
      SimpleGraph.Walk.take_getVert, SimpleGraph.Walk.drop_getVert]

lemma CycleSplit.ofClosedWalk_injective {V : Type*} {G : SimpleGraph V} :
    Function.Injective (CycleSplit.ofClosedWalk : ClosedWalk G 12 → CycleSplit G) := by
  intro w z h
  rw [← CycleSplit.toClosedWalk_ofClosedWalk w,
    ← CycleSplit.toClosedWalk_ofClosedWalk z, h]

@[simp] lemma CycleSplit.ofClosedWalk_middle_getVert {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) (i : Fin 6) :
    (CycleSplit.ofClosedWalk w).middle.1.getVert i.1 =
      w.2.1.getVert (i.1 + 1) := by
  simp [CycleSplit.ofClosedWalk, SimpleGraph.Walk.take_getVert,
    SimpleGraph.Walk.drop_getVert, Nat.add_comm]

/-- Cyclically move the first `i` edges of a closed twelve-walk to its end. -/
noncomputable def ClosedWalk.rotate12 {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) (i : Fin 12) : ClosedWalk G 12 := by
  let p := w.2.1
  have hp : p.length = 12 := w.2.2
  let q := (p.drop i.1).append (p.take i.1)
  have hq : q.length = 12 := by
    simp [q, hp]
  exact ⟨p.getVert i.1, ⟨q, hq⟩⟩

def ClosedWalk.cycleSupport {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) : List V :=
  w.2.1.support.dropLast

lemma ClosedWalk.cycleSupport_length {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) : w.cycleSupport.length = 12 := by
  simp [ClosedWalk.cycleSupport, w.2.2]

lemma ClosedWalk.cycleSupport_getElem? {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) (k : Fin 12) :
    w.cycleSupport[k.1]? = some (w.2.1.getVert k.1) := by
  rw [ClosedWalk.cycleSupport, List.getElem?_dropLast,
    if_pos (by simpa [SimpleGraph.Walk.length_support, w.2.2] using k.2)]
  exact (w.2.1.getVert_eq_support_getElem? (by rw [w.2.2]; exact k.2.le)).symm

lemma ClosedWalk.cycleSupport_rotate12 {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) (i : Fin 12) :
    (w.rotate12 i).cycleSupport = w.cycleSupport.rotate i.1 := by
  simp [ClosedWalk.cycleSupport, ClosedWalk.rotate12,
    SimpleGraph.Walk.support_append_eq_support_dropLast_append,
    List.rotate_eq_drop_append_take, w.2.2]
  rw [List.dropLast_drop_eq_drop_dropLast]
  rw [SimpleGraph.Walk.support_take, List.dropLast_take_eq_take_dropLast]
  simp

lemma ClosedWalk.rotate12_getVert {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) (i k : Fin 12) :
    (w.rotate12 i).2.1.getVert k.1 =
      w.2.1.getVert ((k.1 + i.1) % 12) := by
  let t : Fin 12 := ⟨(k.1 + i.1) % 12, Nat.mod_lt _ (by norm_num)⟩
  apply Option.some_injective
  calc
    some ((w.rotate12 i).2.1.getVert k.1) = (w.rotate12 i).cycleSupport[k.1]? :=
      ((w.rotate12 i).cycleSupport_getElem? k).symm
    _ = (w.cycleSupport.rotate i.1)[k.1]? := by rw [w.cycleSupport_rotate12]
    _ = w.cycleSupport[(k.1 + i.1) % 12]? := by
      simpa [w.cycleSupport_length] using
        (List.getElem?_rotate (l := w.cycleSupport) (n := i.1) (m := k.1)
          (by rw [w.cycleSupport_length]; exact k.2))
    _ = some (w.2.1.getVert ((k.1 + i.1) % 12)) := w.cycleSupport_getElem? t

lemma ClosedWalk.cycleSupport_injective {V : Type*} {G : SimpleGraph V} :
    Function.Injective (ClosedWalk.cycleSupport : ClosedWalk G 12 → List V) := by
  intro w z h
  rcases w with ⟨v, p, hp⟩
  rcases z with ⟨v', q, hq⟩
  have hv : v = v' := by
    have hh := congrArg List.head? h
    simp only [ClosedWalk.cycleSupport, List.dropLast_eq_take] at hh
    simp only [SimpleGraph.Walk.length_support, hp, hq, Nat.add_sub_cancel] at hh
    rw [← p.cons_tail_support, ← q.cons_tail_support] at hh
    simpa only [List.take_succ_cons, List.head?_cons, Option.some.injEq] using hh
  subst v'
  have hsupp : p.support = q.support := by
    calc
      p.support = p.support.dropLast ++ [v] := by
        symm
        simpa using (List.dropLast_append_getLast p.support_ne_nil)
      _ = q.support.dropLast ++ [v] := by
        simpa [ClosedWalk.cycleSupport] using congrArg (fun l : List V ↦ l ++ [v]) h
      _ = q.support := by
        simpa using (List.dropLast_append_getLast q.support_ne_nil)
  have hpq : p = q := SimpleGraph.Walk.ext_support hsupp
  subst q
  rfl

lemma ClosedWalk.rotate12_injective {V : Type*} {G : SimpleGraph V} (i : Fin 12) :
    Function.Injective (fun w : ClosedWalk G 12 ↦ w.rotate12 i) := by
  intro w z h
  apply ClosedWalk.cycleSupport_injective
  apply List.rotate_injective i.1
  change w.cycleSupport.rotate i.1 = z.cycleSupport.rotate i.1
  rw [← w.cycleSupport_rotate12 i, ← z.cycleSupport_rotate12 i]
  change w.rotate12 i = z.rotate12 i at h
  exact congrArg ClosedWalk.cycleSupport h

/-! ## Finite bipartite relations used by regularization -/

def bipartiteRelGraph {L R : Type*} (B : L → R → Prop) :
    SimpleGraph (L ⊕ R) where
  Adj x y := match x, y with
    | Sum.inl l, Sum.inr r => B l r
    | Sum.inr r, Sum.inl l => B l r
    | _, _ => False
  symm.symm := by
    rintro (l | r) (l' | r') <;> simp_all
  loopless.irrefl := by
    rintro (l | r) <;> simp

instance bipartiteRelGraph.instDecidableAdj
    {L R : Type*} (B : L → R → Prop) [∀ l r, Decidable (B l r)] :
    DecidableRel (bipartiteRelGraph B).Adj := by
  intro x y
  rcases x with l | r <;> rcases y with l' | r' <;>
    simp only [bipartiteRelGraph] <;> infer_instance

/-- The two sides of a graph constructed from a bipartite relation. -/
def bipartiteSide {L R : Type*} : L ⊕ R → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

lemma bipartiteSide_ne_of_adj
    {L R : Type*} {B : L → R → Prop} {x y : L ⊕ R}
    (hxy : (bipartiteRelGraph B).Adj x y) :
    bipartiteSide x ≠ bipartiteSide y := by
  rcases x with l | r <;> rcases y with l' | r' <;>
    simp [bipartiteRelGraph, bipartiteSide] at hxy ⊢

lemma bool_eq_of_ne_of_ne {a b c : Bool} (hab : a ≠ b) (hbc : b ≠ c) : a = c := by
  cases a <;> cases b <;> cases c <;> simp_all

lemma bipartiteWalk_length_five_side_ne
    {L R : Type*} {B : L → R → Prop} {x y : L ⊕ R}
    (p : (bipartiteRelGraph B).Walk x y) (hp : p.length = 5) :
    bipartiteSide x ≠ bipartiteSide y := by
  have h0 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 0) (by omega))
  have h1 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 1) (by omega))
  have h2 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 2) (by omega))
  have h3 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 3) (by omega))
  have h4 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 4) (by omega))
  have h02 : bipartiteSide x = bipartiteSide (p.getVert 2) := by
    simpa using bool_eq_of_ne_of_ne h0 h1
  have h24 : bipartiteSide (p.getVert 2) = bipartiteSide (p.getVert 4) :=
    bool_eq_of_ne_of_ne h2 h3
  have h4y : bipartiteSide (p.getVert 4) ≠ bipartiteSide y := by
    simpa [p.getVert_of_length_le (by omega : p.length ≤ 5), hp] using h4
  intro hxy
  exact h4y ((h02.trans h24).symm.trans hxy)

/-- A relation-preserving map on each side induces a graph homomorphism from
the associated bipartite-relation graph. -/
def bipartiteRelGraphHom
    {L R V : Type*} {B : L → R → Prop} (G : SimpleGraph V)
    (fL : L → V) (fR : R → V)
    (hmap : ∀ l r, B l r → G.Adj (fL l) (fR r)) :
    bipartiteRelGraph B →g G where
  toFun := Sum.elim fL fR
  map_rel' := by
    rintro (l | r) (l' | r') h
    · simp [bipartiteRelGraph] at h
    · exact hmap l r' h
    · exact G.adj_symm (hmap l' r h)
    · simp [bipartiteRelGraph] at h

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos147/Core.lean` -/

section
open Filter
open Asymptotics
open scoped SimpleGraph Topology



set_option autoImplicit false

/-! ## A two-sided finite minimum-degree core -/

def relEdgeFinset {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] : Finset (L × R) :=
  Finset.univ.filter fun e ↦ B e.1 e.2

@[simp] lemma mem_relEdgeFinset {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] (l : L) (r : R) :
    (l, r) ∈ relEdgeFinset B ↔ B l r := by
  simp [relEdgeFinset]

noncomputable def restrictedRelEdgeFinset {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (S : Finset L) (T : Finset R) : Finset (L × R) := by
  classical
  exact (relEdgeFinset B).filter fun e ↦ e.1 ∈ S ∧ e.2 ∈ T

@[simp] lemma mem_restrictedRelEdgeFinset {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (S : Finset L) (T : Finset R) (l : L) (r : R) :
    (l, r) ∈ restrictedRelEdgeFinset B S T ↔ B l r ∧ l ∈ S ∧ r ∈ T := by
  simp [restrictedRelEdgeFinset, and_assoc]

noncomputable def restrictedLeftDegree {L R : Type*} [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (T : Finset R) (l : L) : ℕ := by
  classical
  exact (T.filter fun r ↦ B l r).card

noncomputable def restrictedRightDegree {L R : Type*} [Fintype L]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (S : Finset L) (r : R) : ℕ := by
  classical
  exact (S.filter fun l ↦ B l r).card

lemma restrictedRelEdgeFinset_card_erase_left
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (S : Finset L) (T : Finset R) {l : L} (hl : l ∈ S) :
    (restrictedRelEdgeFinset B (S.erase l) T).card +
        restrictedLeftDegree B T l =
      (restrictedRelEdgeFinset B S T).card := by
  classical
  let U := (relEdgeFinset B).filter fun e ↦ e.1 ∈ S ∧ e.2 ∈ T
  let A := U.filter fun e ↦ e.1 = l
  let C := U.filter fun e ↦ e.1 ≠ l
  have hdisj : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro e heA heC
    exact (Finset.mem_filter.mp heC).2 ((Finset.mem_filter.mp heA).2)
  have hunion : A ∪ C = U := by
    ext e
    by_cases h : e.1 = l <;> simp [A, C, h]
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion] at hcard
  have hA : A.card = restrictedLeftDegree B T l := by
    apply Finset.card_bij (fun e _ ↦ e.2)
    · intro e he
      have heA := Finset.mem_filter.mp (show e ∈ U.filter (fun e ↦ e.1 = l) from he)
      have heU := Finset.mem_filter.mp heA.1
      have hb : B e.1 e.2 := (mem_relEdgeFinset B e.1 e.2).mp heU.1
      have hb' : B l e.2 := by rwa [heA.2] at hb
      exact Finset.mem_filter.mpr ⟨heU.2.2, hb'⟩
    · intro e₁ he₁ e₂ he₂ h
      have he₁A := Finset.mem_filter.mp (show e₁ ∈ U.filter (fun e ↦ e.1 = l) from he₁)
      have he₂A := Finset.mem_filter.mp (show e₂ ∈ U.filter (fun e ↦ e.1 = l) from he₂)
      apply Prod.ext
      · exact he₁A.2.trans he₂A.2.symm
      · exact h
    · intro r hr
      simp only [restrictedLeftDegree, Finset.mem_filter] at hr
      refine ⟨(l, r), ?_, rfl⟩
      simp [A, U, hl, hr]
  have hC : C = restrictedRelEdgeFinset B (S.erase l) T := by
    ext e
    by_cases h : e.1 = l <;> simp [C, U, restrictedRelEdgeFinset, h, hl]
  have hU : U = restrictedRelEdgeFinset B S T := by
    ext e
    simp [U, restrictedRelEdgeFinset]
  rw [← hC, ← hA]
  rw [← hU]
  omega

lemma restrictedRelEdgeFinset_card_erase_right
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (S : Finset L) (T : Finset R) {r : R} (hr : r ∈ T) :
    (restrictedRelEdgeFinset B S (T.erase r)).card +
        restrictedRightDegree B S r =
      (restrictedRelEdgeFinset B S T).card := by
  classical
  let B' : R → L → Prop := fun r l ↦ B l r
  have h := restrictedRelEdgeFinset_card_erase_left B' T S hr
  have hcard (U : Finset R) (W : Finset L) :
      (restrictedRelEdgeFinset B' U W).card =
        (restrictedRelEdgeFinset B W U).card := by
    apply Finset.card_bij (fun e _ ↦ (e.2, e.1))
    · intro e he
      rw [mem_restrictedRelEdgeFinset] at he ⊢
      simpa [B', and_left_comm, and_comm] using he
    · intro e₁ h₁ e₂ h₂ he
      exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
    · intro e he
      refine ⟨(e.2, e.1), ?_, rfl⟩
      rw [mem_restrictedRelEdgeFinset] at he ⊢
      simpa [B', and_left_comm, and_comm] using he
  simpa [B', restrictedRightDegree, restrictedLeftDegree, hcard] using h

noncomputable def relCorePotential {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (q : ℕ) (z : Finset L × Finset R) : ℤ :=
  4 * Fintype.card L * Fintype.card R *
      (restrictedRelEdgeFinset B z.1 z.2).card -
    q * Fintype.card R * z.1.card - q * Fintype.card L * z.2.card

/-- Every nonempty finite bipartite relation has a nonempty induced core in
which each left degree is at least one quarter of the original left average,
and similarly on the right.  The inequalities are cross-multiplied to avoid
rounding. -/
lemma exists_twoSided_relCore
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (hE : (relEdgeFinset B).Nonempty) :
    ∃ (S : Finset L) (T : Finset R), S.Nonempty ∧ T.Nonempty ∧
      (∀ l ∈ S, (relEdgeFinset B).card ≤
        4 * Fintype.card L * restrictedLeftDegree B T l) ∧
      (∀ r ∈ T, (relEdgeFinset B).card ≤
        4 * Fintype.card R * restrictedRightDegree B S r) := by
  classical
  let q := (relEdgeFinset B).card
  obtain ⟨z, hz⟩ := Finite.exists_max (relCorePotential B q)
  let S := z.1
  let T := z.2
  have hq : 0 < q := Finset.card_pos.mpr hE
  have hL : 0 < Fintype.card L := by
    obtain ⟨⟨l, r⟩, he⟩ := hE
    exact Fintype.card_pos_iff.mpr ⟨l⟩
  have hR : 0 < Fintype.card R := by
    obtain ⟨⟨l, r⟩, he⟩ := hE
    exact Fintype.card_pos_iff.mpr ⟨r⟩
  have hfull : relCorePotential B q (Finset.univ, Finset.univ) =
      2 * (Fintype.card L : ℤ) * Fintype.card R * q := by
    have heq : restrictedRelEdgeFinset B Finset.univ Finset.univ =
        relEdgeFinset B := by
      ext e
      rcases e with ⟨l, r⟩
      simp
    simp [relCorePotential, q, heq]
    ring
  have hpos : 0 < relCorePotential B q z := by
    have hle := hz (Finset.univ, Finset.univ)
    rw [hfull] at hle
    have hp : (0 : ℤ) < 2 * (Fintype.card L : ℤ) * Fintype.card R * q := by
      positivity
    exact hp.trans_le hle
  have hSne : S.Nonempty := by
    by_contra h
    have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have : relCorePotential B q z ≤ 0 := by
      change relCorePotential B q (S, T) ≤ 0
      rw [hS]
      simp [relCorePotential, restrictedRelEdgeFinset]
      exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity)
    exact (not_lt_of_ge this) hpos
  have hTne : T.Nonempty := by
    by_contra h
    have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have : relCorePotential B q z ≤ 0 := by
      change relCorePotential B q (S, T) ≤ 0
      rw [hT]
      simp [relCorePotential, restrictedRelEdgeFinset]
      exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity)
    exact (not_lt_of_ge this) hpos
  refine ⟨S, T, hSne, hTne, ?_, ?_⟩
  · intro l hl
    have hmax := hz (S.erase l, T)
    have hedge := restrictedRelEdgeFinset_card_erase_left B S T hl
    change relCorePotential B q (S.erase l, T) ≤
      relCorePotential B q (S, T) at hmax
    simp only [relCorePotential, Prod.fst, Prod.snd, Finset.card_erase_of_mem hl] at hmax
    have hedgeZ :
        ((restrictedRelEdgeFinset B (S.erase l) T).card : ℤ) +
            restrictedLeftDegree B T l =
          (restrictedRelEdgeFinset B S T).card := by exact_mod_cast hedge
    have hScard : 1 ≤ S.card := Finset.one_le_card.mpr hSne
    rw [Nat.cast_sub hScard] at hmax
    rw [← hedgeZ] at hmax
    have hmul : (q : ℤ) * Fintype.card R ≤
        (4 * Fintype.card L * restrictedLeftDegree B T l : ℤ) *
          Fintype.card R := by
      push_cast at hmax
      ring_nf at hmax ⊢
      linarith
    have hcancel : (q : ℤ) ≤
        4 * Fintype.card L * restrictedLeftDegree B T l := by
      have hRz : (0 : ℤ) < Fintype.card R := by exact_mod_cast hR
      by_contra hn
      have hlt : (4 * Fintype.card L * restrictedLeftDegree B T l : ℤ) < q :=
        lt_of_not_ge hn
      nlinarith
    exact_mod_cast hcancel
  · intro r hr
    have hmax := hz (S, T.erase r)
    have hedge := restrictedRelEdgeFinset_card_erase_right B S T hr
    change relCorePotential B q (S, T.erase r) ≤
      relCorePotential B q (S, T) at hmax
    simp only [relCorePotential, Prod.fst, Prod.snd, Finset.card_erase_of_mem hr] at hmax
    have hedgeZ :
        ((restrictedRelEdgeFinset B S (T.erase r)).card : ℤ) +
            restrictedRightDegree B S r =
          (restrictedRelEdgeFinset B S T).card := by exact_mod_cast hedge
    have hTcard : 1 ≤ T.card := Finset.one_le_card.mpr hTne
    rw [Nat.cast_sub hTcard] at hmax
    rw [← hedgeZ] at hmax
    have hmul : (q : ℤ) * Fintype.card L ≤
        (4 * Fintype.card R * restrictedRightDegree B S r : ℤ) *
          Fintype.card L := by
      push_cast at hmax
      ring_nf at hmax ⊢
      linarith
    have hcancel : (q : ℤ) ≤
        4 * Fintype.card R * restrictedRightDegree B S r := by
      have hLz : (0 : ℤ) < Fintype.card L := by exact_mod_cast hL
      by_contra hn
      have hlt : (4 * Fintype.card R * restrictedRightDegree B S r : ℤ) < q :=
        lt_of_not_ge hn
      nlinarith
    exact_mod_cast hcancel

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos147/Conflict.lean` -/

section
open Filter
open Asymptotics
open scoped SimpleGraph Topology



set_option autoImplicit false

/-! ## Janzer's threshold split, specialized to twelve-cycles -/

structure LeftCycleSplit {L R : Type*} (B : L → R → Prop) where
  x₁ : L
  x₂ : R
  x₈ : R
  bridge : B x₁ x₂
  middle : WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈)
  tail : WalkOfLength (bipartiteRelGraph B) 5 (Sum.inr x₈) (Sum.inl x₁)

instance LeftCycleSplit.instFinite
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] :
    Finite (LeftCycleSplit B) := by
  let e : LeftCycleSplit B →
      Σ x₁ : L, Σ x₂ x₈ : R,
        WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈) ×
          WalkOfLength (bipartiteRelGraph B) 5 (Sum.inr x₈) (Sum.inl x₁) :=
    fun c ↦ ⟨c.x₁, c.x₂, c.x₈, c.middle, c.tail⟩
  exact Finite.of_injective e (by
    intro c d h
    cases c
    cases d
    cases h
    rfl)

noncomputable def CycleSplit.toLeftCycleSplit
    {L R : Type*} (B : L → R → Prop)
    (c : CycleSplit (bipartiteRelGraph B)) (l : L) (hl : c.x₁ = Sum.inl l) :
    LeftCycleSplit B := by
  rcases c with ⟨x₁, x₂, x₈, bridge, middle, tail⟩
  dsimp at hl
  subst x₁
  cases x₂ with
  | inl l₂ => simp [bipartiteRelGraph] at bridge
  | inr r₂ =>
      cases x₈ with
      | inl l₈ =>
          have hn := bipartiteWalk_length_five_side_ne tail.1 tail.2
          simp [bipartiteSide] at hn
      | inr r₈ => exact ⟨l, r₂, r₈, bridge, middle, tail⟩

def LeftCycleSplit.toCycleSplit
    {L R : Type*} {B : L → R → Prop} (c : LeftCycleSplit B) :
    CycleSplit (bipartiteRelGraph B) :=
  { x₁ := Sum.inl c.x₁
    x₂ := Sum.inr c.x₂
    x₈ := Sum.inr c.x₈
    bridge := c.bridge
    middle := c.middle
    tail := c.tail }

lemma CycleSplit.toCycleSplit_toLeftCycleSplit
    {L R : Type*} (B : L → R → Prop)
    (c : CycleSplit (bipartiteRelGraph B)) (l : L) (hl : c.x₁ = Sum.inl l) :
    (c.toLeftCycleSplit B l hl).toCycleSplit = c := by
  rcases c with ⟨x₁, x₂, x₈, bridge, middle, tail⟩
  dsimp at hl
  subst x₁
  cases x₂ with
  | inl l₂ => simp [bipartiteRelGraph] at bridge
  | inr r₂ =>
      cases x₈ with
      | inl l₈ =>
          have hn := bipartiteWalk_length_five_side_ne tail.1 tail.2
          simp [bipartiteSide] at hn
      | inr r₈ => rfl

lemma CycleSplit.toLeftCycleSplit_conflict
    {L R : Type*} (B : L → R → Prop)
    (C : (L ⊕ R) → (L ⊕ R) → Prop)
    (c : CycleSplit (bipartiteRelGraph B)) (l : L) (hl : c.x₁ = Sum.inl l)
    (i : Fin 6) (hC : C c.x₁ (c.middle.1.getVert i.1)) :
    C (Sum.inl (c.toLeftCycleSplit B l hl).x₁)
      ((c.toLeftCycleSplit B l hl).middle.1.getVert i.1) := by
  rcases c with ⟨x₁, x₂, x₈, bridge, middle, tail⟩
  dsimp at hl
  subst x₁
  cases x₂ with
  | inl l₂ => simp [bipartiteRelGraph] at bridge
  | inr r₂ =>
      cases x₈ with
      | inl l₈ =>
          have hn := bipartiteWalk_length_five_side_ne tail.1 tail.2
          simp [bipartiteSide] at hn
      | inr r₈ => exact hC

def bipartiteRelGraphSwapIso {L R : Type*} (B : L → R → Prop) :
    bipartiteRelGraph (fun r l ↦ B l r) ≃g bipartiteRelGraph B :=
  ⟨Equiv.sumComm R L, by
    rintro (r | l) (r' | l') <;> simp [bipartiteRelGraph]⟩

def ClosedWalk.mapIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (w : ClosedWalk G 12) : ClosedWalk H 12 :=
  ⟨e w.1, ⟨w.2.1.map e.toHom, by simpa using w.2.2⟩⟩

lemma ClosedWalk.cycleSupport_mapIso {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) (w : ClosedWalk G 12) :
    (w.mapIso e).cycleSupport = w.cycleSupport.map e := by
  simp [ClosedWalk.mapIso, ClosedWalk.cycleSupport, SimpleGraph.Walk.support_map,
    List.map_dropLast]

lemma ClosedWalk.mapIso_injective {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) :
    Function.Injective (ClosedWalk.mapIso e : ClosedWalk G 12 → ClosedWalk H 12) := by
  intro w z h
  apply ClosedWalk.cycleSupport_injective
  apply (List.map_injective_iff.mpr e.injective)
  rw [← w.cycleSupport_mapIso e, ← z.cycleSupport_mapIso e,
    congrArg ClosedWalk.cycleSupport h]

def swapConflict {L R : Type*} (C : (L ⊕ R) → (L ⊕ R) → Prop) :
    (R ⊕ L) → (R ⊕ L) → Prop :=
  fun x y ↦ C (Equiv.sumComm R L x) (Equiv.sumComm R L y)

instance swapConflict.instDecidableRel {L R : Type*}
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C] :
    DecidableRel (swapConflict C) := by
  intro x y
  exact inferInstanceAs (Decidable (C (Equiv.sumComm R L x) (Equiv.sumComm R L y)))

noncomputable def leftTailMultiplicity
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] (x₁ : L) (x₈ : R) : ℝ :=
  walkCount (bipartiteRelGraph B) 5 (Sum.inr x₈) (Sum.inl x₁)

noncomputable def leftMiddleMultiplicity
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] (x₂ x₈ : R) : ℝ :=
  walkCount (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈)

abbrev LeftLowCode
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] (q : ℝ) :=
  Σ x₁ : L, Σ x₂ x₈ : R,
    {p : WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈) ×
        WalkOfLength (bipartiteRelGraph B) 5 (Sum.inr x₈) (Sum.inl x₁) //
      B x₁ x₂ ∧
        leftMiddleMultiplicity B x₂ x₈ < q * leftTailMultiplicity B x₁ x₈}

lemma card_leftLowCode
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] (q : ℝ) :
    (Nat.card (LeftLowCode B q) : ℝ) =
      ∑ x₁ : L, ∑ x₂ : R, ∑ x₈ : R,
        if B x₁ x₂ ∧
            leftMiddleMultiplicity B x₂ x₈ < q * leftTailMultiplicity B x₁ x₈ then
          leftMiddleMultiplicity B x₂ x₈ * leftTailMultiplicity B x₁ x₈ else 0 := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp only [LeftLowCode, Fintype.card_sigma, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x₁ hx₁
  apply Finset.sum_congr rfl
  intro x₂ hx₂
  apply Finset.sum_congr rfl
  intro x₈ hx₈
  by_cases h : B x₁ x₂ ∧
      leftMiddleMultiplicity B x₂ x₈ < q * leftTailMultiplicity B x₁ x₈
  · let A :=
      WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈) ×
        WalkOfLength (bipartiteRelGraph B) 5 (Sum.inr x₈) (Sum.inl x₁)
    have hsubcard : Fintype.card {p : A // B x₁ x₂ ∧
        leftMiddleMultiplicity B x₂ x₈ < q * leftTailMultiplicity B x₁ x₈} =
        Fintype.card A := by
      let e : {p : A // B x₁ x₂ ∧
          leftMiddleMultiplicity B x₂ x₈ < q * leftTailMultiplicity B x₁ x₈} ≃ A :=
        { toFun := fun z ↦ z.1
          invFun := fun p ↦ ⟨p, h⟩
          left_inv := fun z ↦ Subtype.ext rfl
          right_inv := fun _ ↦ rfl }
      exact Fintype.card_congr e
    rw [if_pos h, hsubcard]
    simp [A, Fintype.card_prod, leftMiddleMultiplicity, leftTailMultiplicity,
      walkCount_eq_card]
  · simp [h]

noncomputable def relLeftDegreeReal
    {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] (l : L) : ℝ :=
  ∑ r : R, if B l r then 1 else 0

lemma leftTailSquareSum_le_homCycleCount_ten
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] :
    (∑ x₁ : L, ∑ x₈ : R, leftTailMultiplicity B x₁ x₈ ^ 2) ≤
      homCycleCount (bipartiteRelGraph B) 10 := by
  rw [show 10 = 2 * 5 by norm_num, homCycleCount_even_eq_sum_sq]
  simp only [Fintype.sum_sum_type]
  have hcomm : (∑ x₁ : L, ∑ x₈ : R, leftTailMultiplicity B x₁ x₈ ^ 2) =
      ∑ x₁ : L, ∑ x₈ : R,
        walkCount (bipartiteRelGraph B) 5 (Sum.inl x₁) (Sum.inr x₈) ^ 2 := by
    apply Finset.sum_congr rfl
    intro x₁ hx₁
    apply Finset.sum_congr rfl
    intro x₈ hx₈
    rw [leftTailMultiplicity, walkCount_comm]
  rw [hcomm]
  simp_rw [Finset.sum_add_distrib]
  have hll : 0 ≤ ∑ x : L, ∑ y : L,
      walkCount (bipartiteRelGraph B) 5 (Sum.inl x) (Sum.inl y) ^ 2 := by
    positivity
  have hrl : 0 ≤ ∑ x : R, ∑ y : L,
      walkCount (bipartiteRelGraph B) 5 (Sum.inr x) (Sum.inl y) ^ 2 := by
    positivity
  have hrr : 0 ≤ ∑ x : R, ∑ y : R,
      walkCount (bipartiteRelGraph B) 5 (Sum.inr x) (Sum.inr y) ^ 2 := by
    positivity
  nlinarith

lemma card_leftLowCode_le
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (q D : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D)
    (hdeg : ∀ l, relLeftDegreeReal B l ≤ D) :
    (Nat.card (LeftLowCode B q) : ℝ) ≤
      q * D * homCycleCount (bipartiteRelGraph B) 10 := by
  rw [card_leftLowCode]
  calc
    (∑ x₁ : L, ∑ x₂ : R, ∑ x₈ : R,
        if B x₁ x₂ ∧
            leftMiddleMultiplicity B x₂ x₈ < q * leftTailMultiplicity B x₁ x₈ then
          leftMiddleMultiplicity B x₂ x₈ * leftTailMultiplicity B x₁ x₈ else 0) ≤
        ∑ x₁ : L, ∑ x₂ : R, ∑ x₈ : R,
          if B x₁ x₂ then q * leftTailMultiplicity B x₁ x₈ ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro x₁ hx₁
      apply Finset.sum_le_sum
      intro x₂ hx₂
      apply Finset.sum_le_sum
      intro x₈ hx₈
      by_cases hlow : B x₁ x₂ ∧
          leftMiddleMultiplicity B x₂ x₈ < q * leftTailMultiplicity B x₁ x₈
      · rw [if_pos hlow, if_pos hlow.1]
        have ha := walkCount_nonneg (bipartiteRelGraph B) 5
          (Sum.inr x₈) (Sum.inl x₁)
        have hmul := mul_le_mul_of_nonneg_right (le_of_lt hlow.2) ha
        simpa [leftTailMultiplicity, pow_two, mul_assoc] using hmul
      · rw [if_neg hlow]
        positivity
    _ = ∑ x₁ : L, ∑ x₈ : R,
          q * leftTailMultiplicity B x₁ x₈ ^ 2 * relLeftDegreeReal B x₁ := by
      apply Finset.sum_congr rfl
      intro x₁ hx₁
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x₈ hx₈
      rw [relLeftDegreeReal, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x₂ hx₂
      by_cases he : B x₁ x₂ <;> simp [he]
    _ ≤ ∑ x₁ : L, ∑ x₈ : R,
          q * leftTailMultiplicity B x₁ x₈ ^ 2 * D := by
      apply Finset.sum_le_sum
      intro x₁ hx₁
      apply Finset.sum_le_sum
      intro x₈ hx₈
      exact mul_le_mul_of_nonneg_left (hdeg x₁)
        (mul_nonneg hq (sq_nonneg _))
    _ = q * D * (∑ x₁ : L, ∑ x₈ : R,
          leftTailMultiplicity B x₁ x₈ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x₁ hx₁
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x₈ hx₈
      ring
    _ ≤ q * D * homCycleCount (bipartiteRelGraph B) 10 := by
      exact mul_le_mul_of_nonneg_left (leftTailSquareSum_le_homCycleCount_ten B)
        (mul_nonneg hq hD)

noncomputable def leftConflictDegreeReal
    {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (u : L ⊕ R) (x₂ : R) : ℝ :=
  ∑ x₁ : L, if B x₁ x₂ ∧ C (Sum.inl x₁) u then 1 else 0

abbrev LeftHighCode
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C] (q : ℝ) :=
  Σ x₂ x₈ : R,
    Σ middle : WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈),
      Σ i : Fin 6, Σ x₁ : L,
        {tail : WalkOfLength (bipartiteRelGraph B) 5 (Sum.inr x₈) (Sum.inl x₁) //
          B x₁ x₂ ∧ C (Sum.inl x₁) (middle.1.getVert i.1) ∧
            q * leftTailMultiplicity B x₁ x₈ ≤ leftMiddleMultiplicity B x₂ x₈}

lemma card_leftHighCode
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C] (q : ℝ) :
    (Nat.card (LeftHighCode B C q) : ℝ) =
      ∑ x₂ : R, ∑ x₈ : R,
        ∑ middle : WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈),
          ∑ i : Fin 6, ∑ x₁ : L,
            if B x₁ x₂ ∧ C (Sum.inl x₁) (middle.1.getVert i.1) ∧
                q * leftTailMultiplicity B x₁ x₈ ≤ leftMiddleMultiplicity B x₂ x₈ then
              leftTailMultiplicity B x₁ x₈ else 0 := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp only [LeftHighCode, Fintype.card_sigma, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x₂ hx₂
  apply Finset.sum_congr rfl
  intro x₈ hx₈
  apply Finset.sum_congr rfl
  intro middle hmiddle
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro x₁ hx₁
  let A := WalkOfLength (bipartiteRelGraph B) 5 (Sum.inr x₈) (Sum.inl x₁)
  let P : Prop := B x₁ x₂ ∧ C (Sum.inl x₁) (middle.1.getVert i.1) ∧
    q * leftTailMultiplicity B x₁ x₈ ≤ leftMiddleMultiplicity B x₂ x₈
  by_cases h : P
  · have hsubcard : Fintype.card {tail : A // P} = Fintype.card A := by
      let e : {tail : A // P} ≃ A :=
        { toFun := fun z ↦ z.1
          invFun := fun tail ↦ ⟨tail, h⟩
          left_inv := fun z ↦ Subtype.ext rfl
          right_inv := fun _ ↦ rfl }
      exact Fintype.card_congr e
    rw [if_pos h, hsubcard]
    simp [A, P, leftTailMultiplicity, walkCount_eq_card]
  · simp [P, h]

lemma leftMiddleSquareSum_le_homCycleCount_twelve
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] :
    (∑ x₂ : R, ∑ x₈ : R, leftMiddleMultiplicity B x₂ x₈ ^ 2) ≤
      homCycleCount (bipartiteRelGraph B) 12 := by
  rw [show 12 = 2 * 6 by norm_num, homCycleCount_even_eq_sum_sq]
  simp only [Fintype.sum_sum_type]
  simp_rw [Finset.sum_add_distrib]
  have hll : 0 ≤ ∑ x : L, ∑ y : L,
      walkCount (bipartiteRelGraph B) 6 (Sum.inl x) (Sum.inl y) ^ 2 := by
    positivity
  have hlr : 0 ≤ ∑ x : L, ∑ y : R,
      walkCount (bipartiteRelGraph B) 6 (Sum.inl x) (Sum.inr y) ^ 2 := by
    positivity
  have hrl : 0 ≤ ∑ x : R, ∑ y : L,
      walkCount (bipartiteRelGraph B) 6 (Sum.inr x) (Sum.inl y) ^ 2 := by
    positivity
  simp only [leftMiddleMultiplicity]
  nlinarith

lemma card_leftHighCode_le
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (q s : ℝ) (hq : 0 < q) (hs : 0 ≤ s)
    (hconf : ∀ u x₂, leftConflictDegreeReal B C u x₂ ≤ s) :
    (Nat.card (LeftHighCode B C q) : ℝ) ≤
      (6 * s / q) * homCycleCount (bipartiteRelGraph B) 12 := by
  rw [card_leftHighCode]
  calc
    (∑ x₂ : R, ∑ x₈ : R,
        ∑ middle : WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈),
          ∑ i : Fin 6, ∑ x₁ : L,
            if B x₁ x₂ ∧ C (Sum.inl x₁) (middle.1.getVert i.1) ∧
                q * leftTailMultiplicity B x₁ x₈ ≤ leftMiddleMultiplicity B x₂ x₈ then
              leftTailMultiplicity B x₁ x₈ else 0) ≤
        ∑ x₂ : R, ∑ x₈ : R,
          ∑ middle : WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈),
            ∑ i : Fin 6, ∑ x₁ : L,
              if B x₁ x₂ ∧ C (Sum.inl x₁) (middle.1.getVert i.1) then
                leftMiddleMultiplicity B x₂ x₈ / q else 0 := by
      apply Finset.sum_le_sum
      intro x₂ hx₂
      apply Finset.sum_le_sum
      intro x₈ hx₈
      apply Finset.sum_le_sum
      intro middle hmiddle
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro x₁ hx₁
      by_cases hall : B x₁ x₂ ∧ C (Sum.inl x₁) (middle.1.getVert i.1) ∧
          q * leftTailMultiplicity B x₁ x₈ ≤ leftMiddleMultiplicity B x₂ x₈
      · rw [if_pos hall, if_pos ⟨hall.1, hall.2.1⟩]
        apply (le_div_iff₀ hq).2
        simpa [mul_comm] using hall.2.2
      · rw [if_neg hall]
        by_cases hc : B x₁ x₂ ∧ C (Sum.inl x₁) (middle.1.getVert i.1)
        · rw [if_pos hc]
          exact div_nonneg (walkCount_nonneg (bipartiteRelGraph B) 6 _ _) hq.le
        · simp [hc]
    _ = ∑ x₂ : R, ∑ x₈ : R,
          ∑ middle : WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈),
            ∑ i : Fin 6,
              (leftMiddleMultiplicity B x₂ x₈ / q) *
                leftConflictDegreeReal B C (middle.1.getVert i.1) x₂ := by
      apply Finset.sum_congr rfl
      intro x₂ hx₂
      apply Finset.sum_congr rfl
      intro x₈ hx₈
      apply Finset.sum_congr rfl
      intro middle hmiddle
      apply Finset.sum_congr rfl
      intro i hi
      rw [leftConflictDegreeReal, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x₁ hx₁
      by_cases hc : B x₁ x₂ ∧ C (Sum.inl x₁) (middle.1.getVert i.1) <;>
        simp [hc]
    _ ≤ ∑ x₂ : R, ∑ x₈ : R,
          ∑ middle : WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈),
            ∑ _i : Fin 6, (leftMiddleMultiplicity B x₂ x₈ / q) * s := by
      apply Finset.sum_le_sum
      intro x₂ hx₂
      apply Finset.sum_le_sum
      intro x₈ hx₈
      apply Finset.sum_le_sum
      intro middle hmiddle
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hconf (middle.1.getVert i.1) x₂)
        (div_nonneg (walkCount_nonneg (bipartiteRelGraph B) 6 _ _) hq.le)
    _ = ∑ x₂ : R, ∑ x₈ : R,
          (6 * s / q) * leftMiddleMultiplicity B x₂ x₈ ^ 2 := by
      apply Finset.sum_congr rfl
      intro x₂ hx₂
      apply Finset.sum_congr rfl
      intro x₈ hx₈
      simp [leftMiddleMultiplicity, walkCount_eq_card]
      ring
    _ = (6 * s / q) * (∑ x₂ : R, ∑ x₈ : R,
          leftMiddleMultiplicity B x₂ x₈ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x₂ hx₂
      rw [Finset.mul_sum]
    _ ≤ (6 * s / q) * homCycleCount (bipartiteRelGraph B) 12 := by
      exact mul_le_mul_of_nonneg_left (leftMiddleSquareSum_le_homCycleCount_twelve B)
        (div_nonneg (mul_nonneg (show (0 : ℝ) ≤ 6 by norm_num) hs) hq.le)

abbrev LeftBadSplit
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C] :=
  {c : LeftCycleSplit B // ∃ i : Fin 6,
    C (Sum.inl c.x₁) (c.middle.1.getVert i.1)}

noncomputable def leftBadSplitOfClosedWalk
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (w : ClosedWalk (bipartiteRelGraph B) 12) (k : Fin 6)
    (hC : C w.1 (w.2.1.getVert (k.1 + 1)))
    (l : L) (hl : w.1 = Sum.inl l) : LeftBadSplit B C := by
  let c := CycleSplit.ofClosedWalk w
  let d := c.toLeftCycleSplit B l hl
  refine ⟨d, k, ?_⟩
  apply c.toLeftCycleSplit_conflict B C l hl k
  change C w.1 ((CycleSplit.ofClosedWalk w).middle.1.getVert k.1)
  rw [CycleSplit.ofClosedWalk_middle_getVert]
  exact hC

noncomputable def rightBadSplitOfClosedWalk
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (w : ClosedWalk (bipartiteRelGraph B) 12) (k : Fin 6)
    (hC : C w.1 (w.2.1.getVert (k.1 + 1)))
    (r : R) (hr : w.1 = Sum.inr r) :
    LeftBadSplit (fun r l ↦ B l r) (swapConflict C) := by
  let e := (bipartiteRelGraphSwapIso B).symm
  let w' := w.mapIso e
  have hr' : w'.1 = Sum.inl r := by
    change e w.1 = Sum.inl r
    rw [hr]
    rfl
  have hC' : swapConflict C w'.1 (w'.2.1.getVert (k.1 + 1)) := by
    dsimp only [w', ClosedWalk.mapIso]
    have hswap (x : L ⊕ R) : Equiv.sumComm R L (e x) = x := by
      cases x <;> rfl
    have hswapHom (x : L ⊕ R) : Equiv.sumComm R L (e.toHom x) = x := by
      cases x <;> rfl
    simpa only [swapConflict, SimpleGraph.Walk.getVert_map, hswap, hswapHom] using hC
  exact leftBadSplitOfClosedWalk (fun r l ↦ B l r) (swapConflict C) w' k hC' r hr'

lemma ClosedWalk.mapIso_symm_mapIso {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) (w : ClosedWalk G 12) :
    (w.mapIso e).mapIso e.symm = w := by
  apply ClosedWalk.cycleSupport_injective
  rw [(w.mapIso e).cycleSupport_mapIso e.symm, w.cycleSupport_mapIso e]
  simp

lemma leftBadSplitOfClosedWalk_toCycleSplit
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (w : ClosedWalk (bipartiteRelGraph B) 12) (k : Fin 6)
    (hC : C w.1 (w.2.1.getVert (k.1 + 1)))
    (l : L) (hl : w.1 = Sum.inl l) :
    (leftBadSplitOfClosedWalk B C w k hC l hl).1.toCycleSplit =
      CycleSplit.ofClosedWalk w := by
  apply CycleSplit.toCycleSplit_toLeftCycleSplit B

lemma rightBadSplitOfClosedWalk_toClosedWalk
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (w : ClosedWalk (bipartiteRelGraph B) 12) (k : Fin 6)
    (hC : C w.1 (w.2.1.getVert (k.1 + 1)))
    (r : R) (hr : w.1 = Sum.inr r) :
    (((rightBadSplitOfClosedWalk B C w k hC r hr).1.toCycleSplit.toClosedWalk).mapIso
        (bipartiteRelGraphSwapIso B)) = w := by
  let e := (bipartiteRelGraphSwapIso B).symm
  let w' := w.mapIso e
  have hr' : w'.1 = Sum.inl r := by
    change e w.1 = Sum.inl r
    rw [hr]
    rfl
  have hC' : swapConflict C w'.1 (w'.2.1.getVert (k.1 + 1)) := by
    dsimp only [w', ClosedWalk.mapIso]
    have hswap (x : L ⊕ R) : Equiv.sumComm R L (e x) = x := by
      cases x <;> rfl
    have hswapHom (x : L ⊕ R) : Equiv.sumComm R L (e.toHom x) = x := by
      cases x <;> rfl
    simpa only [swapConflict, SimpleGraph.Walk.getVert_map, hswap, hswapHom] using hC
  rw [show rightBadSplitOfClosedWalk B C w k hC r hr =
      leftBadSplitOfClosedWalk (fun r l ↦ B l r) (swapConflict C) w' k hC' r hr' by rfl]
  rw [leftBadSplitOfClosedWalk_toCycleSplit, CycleSplit.toClosedWalk_ofClosedWalk]
  exact ClosedWalk.mapIso_symm_mapIso e w

def cycleForwardDistance (i j : Fin 12) : ℕ := (j.1 + 12 - i.1) % 12

def cycleConflictStart (i j : Fin 12) : Fin 12 :=
  if cycleForwardDistance i j ≤ 6 then i else j

def cycleConflictOffset (i j : Fin 12) : Fin 6 := by
  let d := cycleForwardDistance i j
  by_cases h : d ≤ 6
  · exact ⟨d - 1, by
      omega⟩
  · exact ⟨12 - d - 1, by
      have hdlt : d < 12 := Nat.mod_lt _ (by norm_num)
      omega⟩

lemma cycleConflictStart_offset (i j : Fin 12) (hij : i ≠ j) :
    (cycleConflictStart i j = i ∧
        ((cycleConflictOffset i j).1 + 1 + (cycleConflictStart i j).1) % 12 = j.1) ∨
      (cycleConflictStart i j = j ∧
        ((cycleConflictOffset i j).1 + 1 + (cycleConflictStart i j).1) % 12 = i.1) := by
  decide +revert

lemma ClosedWalk.rotate12_has_oriented_conflict
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (hCsymm : Symmetric C) (w : ClosedWalk (bipartiteRelGraph B) 12)
    (i j : Fin 12) (hij : i ≠ j)
    (hC : C (w.2.1.getVert i.1) (w.2.1.getVert j.1)) :
    let w' := w.rotate12 (cycleConflictStart i j)
    C w'.1 (w'.2.1.getVert ((cycleConflictOffset i j).1 + 1)) := by
  dsimp only
  have hs := cycleConflictStart_offset i j hij
  let k : Fin 12 := ⟨(cycleConflictOffset i j).1 + 1, by
    have := (cycleConflictOffset i j).2
    omega⟩
  change C (w.2.1.getVert (cycleConflictStart i j).1)
    ((w.rotate12 (cycleConflictStart i j)).2.1.getVert k.1)
  rw [w.rotate12_getVert (cycleConflictStart i j) k]
  rcases hs with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [hs]
    have ht' : (k.1 + i.1) % 12 = j.1 := by
      simpa [k, hs, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht
    rw [ht']
    exact hC
  · rw [hs]
    have ht' : (k.1 + j.1) % 12 = i.1 := by
      simpa [k, hs, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht
    rw [ht']
    exact hCsymm hC

abbrev ConflictClosedWalk
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C] :=
  {w : ClosedWalk (bipartiteRelGraph B) 12 //
    ∃ i j : Fin 12, i ≠ j ∧ C (w.2.1.getVert i.1) (w.2.1.getVert j.1)}

noncomputable def conflictFirstIndex
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    {B : L → R → Prop} [∀ l r, Decidable (B l r)]
    {C : (L ⊕ R) → (L ⊕ R) → Prop} [DecidableRel C]
    (z : ConflictClosedWalk B C) : Fin 12 := Classical.choose z.2

noncomputable def conflictSecondIndex
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    {B : L → R → Prop} [∀ l r, Decidable (B l r)]
    {C : (L ⊕ R) → (L ⊕ R) → Prop} [DecidableRel C]
    (z : ConflictClosedWalk B C) : Fin 12 := Classical.choose (Classical.choose_spec z.2)

lemma conflictIndex_spec
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    {B : L → R → Prop} [∀ l r, Decidable (B l r)]
    {C : (L ⊕ R) → (L ⊕ R) → Prop} [DecidableRel C]
    (z : ConflictClosedWalk B C) :
    conflictFirstIndex z ≠ conflictSecondIndex z ∧
      C (z.1.2.1.getVert (conflictFirstIndex z).1)
        (z.1.2.1.getVert (conflictSecondIndex z).1) :=
  Classical.choose_spec (Classical.choose_spec z.2)

noncomputable def badSplitOfClosedWalk
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (w : ClosedWalk (bipartiteRelGraph B) 12) (k : Fin 6)
    (hC : C w.1 (w.2.1.getVert (k.1 + 1))) :
    LeftBadSplit B C ⊕ LeftBadSplit (fun r l ↦ B l r) (swapConflict C) :=
  match h : w.1 with
  | Sum.inl l => Sum.inl (leftBadSplitOfClosedWalk B C w k hC l h)
  | Sum.inr r => Sum.inr (rightBadSplitOfClosedWalk B C w k hC r h)

noncomputable def badSplitRotatedWalk
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C] :
    LeftBadSplit B C ⊕ LeftBadSplit (fun r l ↦ B l r) (swapConflict C) →
      ClosedWalk (bipartiteRelGraph B) 12
  | Sum.inl z => z.1.toCycleSplit.toClosedWalk
  | Sum.inr z => z.1.toCycleSplit.toClosedWalk.mapIso (bipartiteRelGraphSwapIso B)

lemma badSplitRotatedWalk_badSplitOfClosedWalk
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (w : ClosedWalk (bipartiteRelGraph B) 12) (k : Fin 6)
    (hC : C w.1 (w.2.1.getVert (k.1 + 1))) :
    badSplitRotatedWalk B C (badSplitOfClosedWalk B C w k hC) = w := by
  unfold badSplitOfClosedWalk
  split
  · simp only [badSplitRotatedWalk]
    rw [leftBadSplitOfClosedWalk_toCycleSplit, CycleSplit.toClosedWalk_ofClosedWalk]
  · simp only [badSplitRotatedWalk]
    apply rightBadSplitOfClosedWalk_toClosedWalk

noncomputable def encodeConflictClosedWalk
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (hCsymm : Symmetric C) (z : ConflictClosedWalk B C) :
    (Fin 12 × Fin 12) ×
      (LeftBadSplit B C ⊕ LeftBadSplit (fun r l ↦ B l r) (swapConflict C)) := by
  let i := conflictFirstIndex z
  let j := conflictSecondIndex z
  let w := z.1.rotate12 (cycleConflictStart i j)
  let k := cycleConflictOffset i j
  have hC : C w.1 (w.2.1.getVert (k.1 + 1)) :=
    z.1.rotate12_has_oriented_conflict B C hCsymm i j
      (conflictIndex_spec z).1 (conflictIndex_spec z).2
  exact ((i, j), badSplitOfClosedWalk B C w k hC)

lemma encodeConflictClosedWalk_injective
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (hCsymm : Symmetric C) : Function.Injective (encodeConflictClosedWalk B C hCsymm) := by
  intro z z' hzz'
  let i := conflictFirstIndex z
  let j := conflictSecondIndex z
  let i' := conflictFirstIndex z'
  let j' := conflictSecondIndex z'
  have htag : (i, j) = (i', j') := congrArg Prod.fst hzz'
  have hi : i = i' := congrArg Prod.fst htag
  have hj : j = j' := congrArg Prod.snd htag
  have hcode : (encodeConflictClosedWalk B C hCsymm z).2 =
      (encodeConflictClosedWalk B C hCsymm z').2 := congrArg Prod.snd hzz'
  have hrot : z.1.rotate12 (cycleConflictStart i j) =
      z'.1.rotate12 (cycleConflictStart i j) := by
    calc
      z.1.rotate12 (cycleConflictStart i j) =
          badSplitRotatedWalk B C (encodeConflictClosedWalk B C hCsymm z).2 := by
            symm
            apply badSplitRotatedWalk_badSplitOfClosedWalk
      _ = badSplitRotatedWalk B C (encodeConflictClosedWalk B C hCsymm z').2 := by
            rw [hcode]
      _ = z'.1.rotate12 (cycleConflictStart i' j') := by
            apply badSplitRotatedWalk_badSplitOfClosedWalk
      _ = z'.1.rotate12 (cycleConflictStart i j) := by rw [hi, hj]
  apply Subtype.ext
  exact ClosedWalk.rotate12_injective (cycleConflictStart i j) hrot

lemma card_conflictClosedWalk_le
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (hCsymm : Symmetric C) :
    (Nat.card (ConflictClosedWalk B C) : ℝ) ≤ 144 *
      (Nat.card (LeftBadSplit B C) +
        Nat.card (LeftBadSplit (fun r l ↦ B l r) (swapConflict C))) := by
  letI : Fintype (LeftBadSplit B C) := Fintype.ofFinite _
  letI : Fintype (LeftBadSplit (fun r l ↦ B l r) (swapConflict C)) := Fintype.ofFinite _
  have hcard := Nat.card_le_card_of_injective (encodeConflictClosedWalk B C hCsymm)
    (encodeConflictClosedWalk_injective B C hCsymm)
  have hcard' : Nat.card (ConflictClosedWalk B C) ≤ 144 *
      (Nat.card (LeftBadSplit B C) +
        Nat.card (LeftBadSplit (fun r l ↦ B l r) (swapConflict C))) := by
    simpa only [Nat.card_prod, Nat.card_fin, Nat.card_sum] using hcard
  exact_mod_cast hcard'

def ClosedWalk.mapIsoN {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {j : ℕ} (e : G ≃g H) (w : ClosedWalk G j) : ClosedWalk H j :=
  ⟨e w.1, ⟨w.2.1.map e.toHom, by simpa using w.2.2⟩⟩

def ClosedWalk.supportCode {V : Type*} {G : SimpleGraph V} {j : ℕ}
    (w : ClosedWalk G j) : List V := w.2.1.support

lemma ClosedWalk.supportCode_injective {V : Type*} {G : SimpleGraph V} {j : ℕ} :
    Function.Injective (ClosedWalk.supportCode : ClosedWalk G j → List V) := by
  intro w z h
  rcases w with ⟨v, p, hp⟩
  rcases z with ⟨v', q, hq⟩
  have hv : v = v' := by
    have hh := congrArg List.head? h
    simp only [ClosedWalk.supportCode] at hh
    rw [← p.cons_tail_support, ← q.cons_tail_support] at hh
    simpa only [List.head?_cons, Option.some.injEq] using hh
  subst v'
  have hpq : p = q := SimpleGraph.Walk.ext_support h
  subst q
  rfl

lemma ClosedWalk.supportCode_mapIsoN {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} {j : ℕ} (e : G ≃g H) (w : ClosedWalk G j) :
    (w.mapIsoN e).supportCode = w.supportCode.map e := by
  simp [ClosedWalk.mapIsoN, ClosedWalk.supportCode, SimpleGraph.Walk.support_map]

lemma ClosedWalk.mapIsoN_injective {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} {j : ℕ} (e : G ≃g H) :
    Function.Injective (ClosedWalk.mapIsoN e : ClosedWalk G j → ClosedWalk H j) := by
  intro w z h
  apply ClosedWalk.supportCode_injective
  apply (List.map_injective_iff.mpr e.injective)
  rw [← w.supportCode_mapIsoN e, ← z.supportCode_mapIsoN e,
    congrArg ClosedWalk.supportCode h]

lemma homCycleCount_eq_of_iso {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) (j : ℕ) :
    homCycleCount G j = homCycleCount H j := by
  rw [homCycleCount_eq_card_closedWalk, homCycleCount_eq_card_closedWalk]
  congr 1
  apply le_antisymm
  · exact Nat.card_le_card_of_injective (ClosedWalk.mapIsoN e)
      (ClosedWalk.mapIsoN_injective e)
  · exact Nat.card_le_card_of_injective (ClosedWalk.mapIsoN e.symm)
      (ClosedWalk.mapIsoN_injective e.symm)

lemma card_leftBadSplit_le_low_add_high
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C] (q : ℝ) :
    (Nat.card (LeftBadSplit B C) : ℝ) ≤
      Nat.card (LeftLowCode B q) + Nat.card (LeftHighCode B C q) := by
  classical
  let encode : LeftBadSplit B C → LeftLowCode B q ⊕ LeftHighCode B C q := fun z ↦
    if hlow : leftMiddleMultiplicity B z.1.x₂ z.1.x₈ <
        q * leftTailMultiplicity B z.1.x₁ z.1.x₈ then
      Sum.inl ⟨z.1.x₁, z.1.x₂, z.1.x₈,
        ⟨(z.1.middle, z.1.tail), z.1.bridge, hlow⟩⟩
    else
      let i := Classical.choose z.2
      Sum.inr ⟨z.1.x₂, z.1.x₈, z.1.middle, i, z.1.x₁,
        ⟨z.1.tail, z.1.bridge, Classical.choose_spec z.2, le_of_not_gt hlow⟩⟩
  let decode : LeftLowCode B q ⊕ LeftHighCode B C q → LeftCycleSplit B
    | Sum.inl z =>
        { x₁ := z.1
          x₂ := z.2.1
          x₈ := z.2.2.1
          bridge := z.2.2.2.2.1
          middle := z.2.2.2.1.1
          tail := z.2.2.2.1.2 }
    | Sum.inr z =>
        { x₁ := z.2.2.2.2.1
          x₂ := z.1
          x₈ := z.2.1
          bridge := z.2.2.2.2.2.2.1
          middle := z.2.2.1
          tail := z.2.2.2.2.2.1 }
  have hdecode : ∀ z : LeftBadSplit B C, decode (encode z) = z.1 := by
    intro z
    by_cases hlow : leftMiddleMultiplicity B z.1.x₂ z.1.x₈ <
        q * leftTailMultiplicity B z.1.x₁ z.1.x₈
    · simp [encode, decode, hlow]
    · simp [encode, decode, hlow]
  have hinj : Function.Injective encode := by
    intro z w hzw
    apply Subtype.ext
    rw [← hdecode z, ← hdecode w, hzw]
  letI : Fintype (LeftLowCode B q) := inferInstance
  letI : Fintype (LeftHighCode B C q) := inferInstance
  have hcard := Nat.card_le_card_of_injective encode hinj
  have hcard' : Nat.card (LeftBadSplit B C) ≤
      Nat.card (LeftLowCode B q) + Nat.card (LeftHighCode B C q) := by
    simpa only [Nat.card_sum] using hcard
  exact_mod_cast hcard'

lemma card_leftBadSplit_le
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (q D s : ℝ) (hq : 0 < q) (hD : 0 ≤ D) (hs : 0 ≤ s)
    (hdeg : ∀ l, relLeftDegreeReal B l ≤ D)
    (hconf : ∀ u x₂, leftConflictDegreeReal B C u x₂ ≤ s) :
    (Nat.card (LeftBadSplit B C) : ℝ) ≤
      q * D * homCycleCount (bipartiteRelGraph B) 10 +
        (6 * s / q) * homCycleCount (bipartiteRelGraph B) 12 := by
  calc
    (Nat.card (LeftBadSplit B C) : ℝ) ≤
        Nat.card (LeftLowCode B q) + Nat.card (LeftHighCode B C q) :=
      card_leftBadSplit_le_low_add_high B C q
    _ ≤ q * D * homCycleCount (bipartiteRelGraph B) 10 +
        (6 * s / q) * homCycleCount (bipartiteRelGraph B) 12 :=
      add_le_add (card_leftLowCode_le B q D hq.le hD hdeg)
        (card_leftHighCode_le B C q s hq hs hconf)

lemma threshold_balance
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    let q := Real.sqrt (B / A)
    q * A + B / q = 2 * Real.sqrt (A * B) := by
  dsimp only
  let q := Real.sqrt (B / A)
  have hBA : 0 < B / A := div_pos hB hA
  have hq : 0 < q := Real.sqrt_pos.2 hBA
  have hq2 : q ^ 2 = B / A := Real.sq_sqrt hBA.le
  have hBq : B / q = q * A := by
    rw [div_eq_iff hq.ne']
    have hBA' : B = q ^ 2 * A := by
      rw [hq2]
      field_simp
    nlinarith
  have hqA : q * A = Real.sqrt (A * B) := by
    have hnonneg : 0 ≤ q * A := mul_nonneg hq.le hA.le
    have hsnonneg : 0 ≤ Real.sqrt (A * B) := Real.sqrt_nonneg _
    have hsquare : (q * A) ^ 2 = (Real.sqrt (A * B)) ^ 2 := by
      rw [Real.sq_sqrt (mul_nonneg hA.le hB.le)]
      have hBA' : B = q ^ 2 * A := by
        rw [hq2]
        field_simp
      nlinarith
    nlinarith
  rw [hBq, hqA]
  ring

lemma homCycleCount_twelve_le_of_all_conflicting
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (hCsymm : Symmetric C) (D₁ D₂ s₁ s₂ : ℝ)
    (hD₁ : 0 < D₁) (hD₂ : 0 < D₂) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hDord : D₁ ≤ D₂)
    (hdeg₁ : ∀ l, relLeftDegreeReal B l ≤ D₁)
    (hdeg₂ : ∀ r, relLeftDegreeReal (fun r l ↦ B l r) r ≤ D₂)
    (hconf₁ : ∀ u r, leftConflictDegreeReal B C u r ≤ s₁)
    (hconf₂ : ∀ u l, leftConflictDegreeReal (fun r l ↦ B l r)
      (swapConflict C) u l ≤ s₂)
    (hs₁bound : s₁ ≤ 8 * Real.sqrt D₂)
    (hs₂bound : s₂ ≤ 8 * Real.sqrt D₁)
    (hall : ∀ w : ClosedWalk (bipartiteRelGraph B) 12,
      ∃ i j : Fin 12, i ≠ j ∧
        C (w.2.1.getVert i.1) (w.2.1.getVert j.1)) :
    homCycleCount (bipartiteRelGraph B) 12 ≤
      16000000 * (D₂ * Real.sqrt D₁) *
        homCycleCount (bipartiteRelGraph B) 10 := by
  let Q := bipartiteRelGraph B
  let x := homCycleCount Q 10
  let y := homCycleCount Q 12
  have hx0 : 0 ≤ x := by simpa [x, Q] using homCycleCount_even_nonneg Q 5
  have hy0 : 0 ≤ y := by simpa [y, Q] using homCycleCount_even_nonneg Q 6
  have hrhs0 : 0 ≤ 16000000 * (D₂ * Real.sqrt D₁) * x :=
    mul_nonneg (mul_nonneg (by positivity)
      (mul_nonneg hD₂.le (Real.sqrt_nonneg _))) hx0
  by_cases hy : y = 0
  · change y ≤ 16000000 * (D₂ * Real.sqrt D₁) * x
    exact hy.le.trans hrhs0
  have hyp : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy)
  have hxp : 0 < x := by
    have hycard : Nat.card (ClosedWalk Q 12) ≠ 0 := by
      intro hz
      apply hy
      rw [show y = homCycleCount Q 12 by rfl, homCycleCount_eq_card_closedWalk]
      exact_mod_cast hz
    obtain ⟨⟨w⟩, _⟩ := Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hycard)
    let p : ClosedWalk Q 10 :=
      ⟨w.1, ⟨(w.2.1.take 5).append (w.2.1.take 5).reverse, by simp [w.2.2]⟩⟩
    rw [show x = homCycleCount Q 10 by rfl, homCycleCount_eq_card_closedWalk]
    exact_mod_cast Nat.card_pos_iff.mpr ⟨⟨p⟩, inferInstance⟩
  let q₁ := Real.sqrt ((6 * s₁ * y) / (D₁ * x))
  let q₂ := Real.sqrt ((6 * s₂ * y) / (D₂ * x))
  have hq₁ : 0 < q₁ := Real.sqrt_pos.2 (div_pos
    (mul_pos (mul_pos (by norm_num) hs₁) hyp) (mul_pos hD₁ hxp))
  have hq₂ : 0 < q₂ := Real.sqrt_pos.2 (div_pos
    (mul_pos (mul_pos (by norm_num) hs₂) hyp) (mul_pos hD₂ hxp))
  have hcount : y = Nat.card (ConflictClosedWalk B C) := by
    rw [show y = homCycleCount Q 12 by rfl, homCycleCount_eq_card_closedWalk]
    congr 1
    apply le_antisymm
    · exact Nat.card_le_card_of_injective
        (fun w : ClosedWalk Q 12 ↦ ⟨w, hall w⟩) (fun _ _ h ↦ Subtype.ext_iff.mp h)
    · exact Nat.card_le_card_of_injective (fun w : ConflictClosedWalk B C ↦ w.1)
        (fun _ _ h ↦ Subtype.ext h)
  have hleft := card_leftBadSplit_le B C q₁ D₁ s₁ hq₁ hD₁.le hs₁.le hdeg₁ hconf₁
  change (Nat.card (LeftBadSplit B C) : ℝ) ≤
    q₁ * D₁ * x + (6 * s₁ / q₁) * y at hleft
  have hright := card_leftBadSplit_le (fun r l ↦ B l r) (swapConflict C)
    q₂ D₂ s₂ hq₂ hD₂.le hs₂.le hdeg₂ hconf₂
  have hiso10 : homCycleCount (bipartiteRelGraph (fun r l ↦ B l r)) 10 = x := by
    simpa [Q, x] using homCycleCount_eq_of_iso
      (bipartiteRelGraph (fun r l ↦ B l r)) Q (bipartiteRelGraphSwapIso B) 10
  have hiso12 : homCycleCount (bipartiteRelGraph (fun r l ↦ B l r)) 12 = y := by
    simpa [Q, y] using homCycleCount_eq_of_iso
      (bipartiteRelGraph (fun r l ↦ B l r)) Q (bipartiteRelGraphSwapIso B) 12
  rw [hiso10, hiso12] at hright
  have hcard := card_conflictClosedWalk_le B C hCsymm
  rw [← hcount] at hcard
  have hbal₁ : q₁ * (D₁ * x) + (6 * s₁ * y) / q₁ =
      2 * Real.sqrt ((D₁ * x) * (6 * s₁ * y)) := by
    simpa [q₁] using threshold_balance (mul_pos hD₁ hxp)
      (mul_pos (mul_pos (by norm_num) hs₁) hyp)
  have hbal₂ : q₂ * (D₂ * x) + (6 * s₂ * y) / q₂ =
      2 * Real.sqrt ((D₂ * x) * (6 * s₂ * y)) := by
    simpa [q₂] using threshold_balance (mul_pos hD₂ hxp)
      (mul_pos (mul_pos (by norm_num) hs₂) hyp)
  have hrough : y ≤ 576 * Real.sqrt
      (48 * (D₂ * Real.sqrt D₁) * x * y) := by
    have hsqrtord : Real.sqrt D₁ ≤ Real.sqrt D₂ := Real.sqrt_le_sqrt hDord
    have hmix : D₁ * Real.sqrt D₂ ≤ D₂ * Real.sqrt D₁ := by
      have hsq₁ : (Real.sqrt D₁) ^ 2 = D₁ := Real.sq_sqrt hD₁.le
      have hsq₂ : (Real.sqrt D₂) ^ 2 = D₂ := Real.sq_sqrt hD₂.le
      calc
        D₁ * Real.sqrt D₂ = (Real.sqrt D₁) ^ 2 * Real.sqrt D₂ := by rw [hsq₁]
        _ = Real.sqrt D₁ * (Real.sqrt D₁ * Real.sqrt D₂) := by ring
        _ ≤ Real.sqrt D₂ * (Real.sqrt D₁ * Real.sqrt D₂) :=
          mul_le_mul_of_nonneg_right hsqrtord
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        _ = (Real.sqrt D₂) ^ 2 * Real.sqrt D₁ := by ring
        _ = D₂ * Real.sqrt D₁ := by rw [hsq₂]
    have hprod₁ : (D₁ * x) * (6 * s₁ * y) ≤
        48 * (D₂ * Real.sqrt D₁) * x * y := by
      calc
        (D₁ * x) * (6 * s₁ * y) = 6 * (D₁ * s₁) * (x * y) := by ring
        _ ≤ 6 * (8 * (D₁ * Real.sqrt D₂)) * (x * y) := by
          have hDs := mul_le_mul_of_nonneg_left hs₁bound hD₁.le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by nlinarith [hDs]) (by norm_num))
            (mul_nonneg hx0 hy0)
        _ ≤ 6 * (8 * (D₂ * Real.sqrt D₁)) * (x * y) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hmix (by norm_num)) (by norm_num))
            (mul_nonneg hx0 hy0)
        _ = 48 * (D₂ * Real.sqrt D₁) * x * y := by ring
    have hprod₂ : (D₂ * x) * (6 * s₂ * y) ≤
        48 * (D₂ * Real.sqrt D₁) * x * y := by
      calc
        (D₂ * x) * (6 * s₂ * y) = 6 * (D₂ * s₂) * (x * y) := by ring
        _ ≤ 6 * (D₂ * (8 * Real.sqrt D₁)) * (x * y) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hs₂bound hD₂.le) (by norm_num))
            (mul_nonneg hx0 hy0)
        _ = 48 * (D₂ * Real.sqrt D₁) * x * y := by ring
    have hroot₁ : Real.sqrt ((D₁ * x) * (6 * s₁ * y)) ≤
        Real.sqrt (48 * (D₂ * Real.sqrt D₁) * x * y) := by
      exact Real.sqrt_le_sqrt hprod₁
    have hroot₂ : Real.sqrt ((D₂ * x) * (6 * s₂ * y)) ≤
        Real.sqrt (48 * (D₂ * Real.sqrt D₁) * x * y) := by
      exact Real.sqrt_le_sqrt hprod₂
    have hsum := add_le_add hleft hright
    have hscaled := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 144 by norm_num)
    calc
      y ≤ 144 * (Nat.card (LeftBadSplit B C) +
          Nat.card (LeftBadSplit (fun r l ↦ B l r) (swapConflict C))) := hcard
      _ ≤ 144 * ((q₁ * D₁ * x + (6 * s₁ / q₁) * y) +
          (q₂ * D₂ * x + (6 * s₂ / q₂) * y)) := hscaled
      _ = 144 * (2 * Real.sqrt ((D₁ * x) * (6 * s₁ * y)) +
          2 * Real.sqrt ((D₂ * x) * (6 * s₂ * y))) := by
            rw [← hbal₁, ← hbal₂]
            ring
      _ ≤ 576 * Real.sqrt (48 * (D₂ * Real.sqrt D₁) * x * y) := by
            nlinarith
  have hM0 : 0 ≤ D₂ * Real.sqrt D₁ :=
    mul_nonneg hD₂.le (Real.sqrt_nonneg _)
  have hZ : 0 ≤ 48 * (D₂ * Real.sqrt D₁) * x * y :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0) hx0) hy0
  have hsquare := Real.sq_sqrt hZ
  have hy2 : y ^ 2 ≤ 576 ^ 2 *
      (48 * (D₂ * Real.sqrt D₁) * x * y) := by nlinarith [sq_nonneg y]
  have hcancel : y ≤ (576 ^ 2 * 48) * (D₂ * Real.sqrt D₁) * x := by
    by_contra hn
    have hlt : (576 ^ 2 * 48) * (D₂ * Real.sqrt D₁) * x < y :=
      lt_of_not_ge hn
    have hmul := mul_lt_mul_of_pos_right hlt hyp
    nlinarith
  change y ≤ 16000000 * (D₂ * Real.sqrt D₁) * x
  calc
    y ≤ 15925248 * (D₂ * Real.sqrt D₁) * x := by norm_num at hcancel ⊢; exact hcancel
    _ ≤ 16000000 * (D₂ * Real.sqrt D₁) * x := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (by norm_num) hM0) hx0

lemma homCycleCount_twelve_le_two_of_ten_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : ℝ) (hK : 0 ≤ K)
    (hbound : homCycleCount G 12 ≤ K * homCycleCount G 10) :
    homCycleCount G 12 ≤ K ^ 5 * homCycleCount G 2 := by
  let a := homCycleCount G 2
  let x := homCycleCount G 10
  let y := homCycleCount G 12
  have ha0 : 0 ≤ a := by simpa [a] using homCycleCount_even_nonneg G 1
  have hx0 : 0 ≤ x := by simpa [x] using homCycleCount_even_nonneg G 5
  have hy0 : 0 ≤ y := by simpa [y] using homCycleCount_even_nonneg G 6
  change y ≤ K ^ 5 * a
  change y ≤ K * x at hbound
  by_cases hy : y = 0
  · exact hy.le.trans (mul_nonneg (pow_nonneg hK 5) ha0)
  have hyp : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy)
  have hpow : y ^ 5 ≤ (K * x) ^ 5 := pow_le_pow_left₀ hy0 hbound 5
  have hinterp : x ^ 5 ≤ a * y ^ 4 := by
    simpa [a, x, y] using homCycleCount_ten_pow_five_le G
  have hfive : y ^ 5 ≤ K ^ 5 * a * y ^ 4 := by
    calc
      y ^ 5 ≤ (K * x) ^ 5 := hpow
      _ = K ^ 5 * x ^ 5 := by ring
      _ ≤ K ^ 5 * (a * y ^ 4) :=
        mul_le_mul_of_nonneg_left hinterp (pow_nonneg hK 5)
      _ = K ^ 5 * a * y ^ 4 := by ring
  have hy4 : 0 < y ^ 4 := pow_pos hyp 4
  by_contra hn
  have hlt : K ^ 5 * a < y := lt_of_not_ge hn
  have hstrict := mul_lt_mul_of_pos_right hlt hy4
  apply (not_lt_of_ge hfive)
  simpa [pow_succ'] using hstrict

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos147/Regularization.lean` -/

section
open Filter
open Asymptotics
open scoped SimpleGraph Topology



set_option autoImplicit false

noncomputable def walkTotal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (u : V) : ℝ :=
  ∑ v : V, walkCount G j u v

lemma walkTotal_zero {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : walkTotal G 0 u = 1 := by
  classical
  simp [walkTotal, walkCount, Matrix.one_apply, Pi.single_apply]

lemma walkTotal_succ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (u : V) :
    walkTotal G (j + 1) u =
      ∑ z : V, (if G.Adj u z then 1 else 0) * walkTotal G j z := by
  rw [walkTotal]
  have hpow : G.adjMatrix ℝ ^ (j + 1) = G.adjMatrix ℝ * G.adjMatrix ℝ ^ j := by
    rw [show j + 1 = 1 + j by omega, pow_add]
    simp
  simp only [walkCount, hpow, Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.mul_sum]
  by_cases h : G.Adj u z <;>
    simp [SimpleGraph.adjMatrix_apply, h, walkTotal, walkCount]

lemma walkTotal_succ_left_lower
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (j : ℕ) (A s : ℝ) (hA : 0 ≤ A)
    (hright : ∀ r, A ≤ walkTotal (bipartiteRelGraph B) j (Sum.inr r))
    (hdeg : ∀ l, s ≤ relLeftDegreeReal B l) (l : L) :
    s * A ≤ walkTotal (bipartiteRelGraph B) (j + 1) (Sum.inl l) := by
  rw [walkTotal_succ]
  simp only [Fintype.sum_sum_type, bipartiteRelGraph, ite_false, zero_mul,
    Finset.sum_const_zero, zero_add, ite_mul, one_mul]
  calc
    s * A ≤ relLeftDegreeReal B l * A :=
      mul_le_mul_of_nonneg_right (hdeg l) hA
    _ = ∑ r : R, if B l r then A else 0 := by
      rw [relLeftDegreeReal, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases h : B l r <;> simp [h]
    _ ≤ ∑ r : R, if B l r then walkTotal (bipartiteRelGraph B) j (Sum.inr r) else 0 := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases h : B l r <;> simp [h, hright]
    _ = ∑ r : R, (if B l r then 1 else 0) *
        walkTotal (bipartiteRelGraph B) j (Sum.inr r) := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases h : B l r <;> simp [h]

lemma walkTotal_succ_right_lower
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (j : ℕ) (A t : ℝ) (hA : 0 ≤ A)
    (hleft : ∀ l, A ≤ walkTotal (bipartiteRelGraph B) j (Sum.inl l))
    (hdeg : ∀ r, t ≤ relLeftDegreeReal (fun r l ↦ B l r) r) (r : R) :
    t * A ≤ walkTotal (bipartiteRelGraph B) (j + 1) (Sum.inr r) := by
  rw [walkTotal_succ]
  simp only [Fintype.sum_sum_type, bipartiteRelGraph, ite_false, zero_mul,
    Finset.sum_const_zero, add_zero, ite_mul, one_mul]
  calc
    t * A ≤ relLeftDegreeReal (fun r l ↦ B l r) r * A :=
      mul_le_mul_of_nonneg_right (hdeg r) hA
    _ = ∑ l : L, if B l r then A else 0 := by
      rw [relLeftDegreeReal, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      by_cases h : B l r <;> simp [h]
    _ ≤ ∑ l : L, if B l r then walkTotal (bipartiteRelGraph B) j (Sum.inl l) else 0 := by
      apply Finset.sum_le_sum
      intro l hl
      by_cases h : B l r <;> simp [h, hleft]
    _ = ∑ l : L, (if B l r then 1 else 0) *
        walkTotal (bipartiteRelGraph B) j (Sum.inl l) := by
      apply Finset.sum_congr rfl
      intro l hl
      by_cases h : B l r <;> simp [h]

lemma bipartiteWalk_length_six_side_eq
    {L R : Type*} {B : L → R → Prop} {x y : L ⊕ R}
    (p : (bipartiteRelGraph B).Walk x y) (hp : p.length = 6) :
    bipartiteSide x = bipartiteSide y := by
  have h0 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 0) (by omega))
  have h1 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 1) (by omega))
  have h2 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 2) (by omega))
  have h3 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 3) (by omega))
  have h4 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 4) (by omega))
  have h5 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 5) (by omega))
  have h02 : bipartiteSide x = bipartiteSide (p.getVert 2) := by
    have := bool_eq_of_ne_of_ne h0 h1
    simpa using this
  have h24 : bipartiteSide (p.getVert 2) = bipartiteSide (p.getVert 4) :=
    bool_eq_of_ne_of_ne h2 h3
  have h46 : bipartiteSide (p.getVert 4) = bipartiteSide y := by
    have := bool_eq_of_ne_of_ne h4 h5
    simpa [p.getVert_of_length_le (by omega : p.length ≤ 6), hp] using this
  exact h02.trans (h24.trans h46)

lemma walkCount_six_left_right_eq_zero
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] (l : L) (r : R) :
    walkCount (bipartiteRelGraph B) 6 (Sum.inl l) (Sum.inr r) = 0 := by
  rw [walkCount_eq_card]
  norm_cast
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun p ↦ by
    have hside := bipartiteWalk_length_six_side_eq p.1 p.2
    simp [bipartiteSide] at hside⟩

lemma homCycleCount_twelve_lower_of_minDegrees
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    [Nonempty L]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hdegL : ∀ l, s ≤ relLeftDegreeReal B l)
    (hdegR : ∀ r, t ≤ relLeftDegreeReal (fun r l ↦ B l r) r) :
    (s * t) ^ 6 ≤ homCycleCount (bipartiteRelGraph B) 12 := by
  let Q := bipartiteRelGraph B
  have hL0 : ∀ l, (1 : ℝ) ≤ walkTotal Q 0 (Sum.inl l) := by
    intro l
    rw [walkTotal_zero]
  have hR0 : ∀ r, (1 : ℝ) ≤ walkTotal Q 0 (Sum.inr r) := by
    intro r
    rw [walkTotal_zero]
  have hL1 : ∀ l, s ≤ walkTotal Q 1 (Sum.inl l) := by
    intro l
    simpa [Q] using walkTotal_succ_left_lower B 0 1 s (by norm_num) hR0 hdegL l
  have hR1 : ∀ r, t ≤ walkTotal Q 1 (Sum.inr r) := by
    intro r
    simpa [Q] using walkTotal_succ_right_lower B 0 1 t (by norm_num) hL0 hdegR r
  have hL2 : ∀ l, s * t ≤ walkTotal Q 2 (Sum.inl l) := by
    intro l
    simpa [Q] using walkTotal_succ_left_lower B 1 t s ht hR1 hdegL l
  have hR2 : ∀ r, t * s ≤ walkTotal Q 2 (Sum.inr r) := by
    intro r
    simpa [Q] using walkTotal_succ_right_lower B 1 s t hs hL1 hdegR r
  have hL3 : ∀ l, s * (t * s) ≤ walkTotal Q 3 (Sum.inl l) := by
    intro l
    simpa [Q] using walkTotal_succ_left_lower B 2 (t * s) s
      (mul_nonneg ht hs) hR2 hdegL l
  have hR3 : ∀ r, t * (s * t) ≤ walkTotal Q 3 (Sum.inr r) := by
    intro r
    simpa [Q] using walkTotal_succ_right_lower B 2 (s * t) t
      (mul_nonneg hs ht) hL2 hdegR r
  have hL4 : ∀ l, (s * t) ^ 2 ≤ walkTotal Q 4 (Sum.inl l) := by
    intro l
    have := walkTotal_succ_left_lower B 3 (t * (s * t)) s
      (mul_nonneg ht (mul_nonneg hs ht)) hR3 hdegL l
    convert this using 1 <;> ring
  have hR4 : ∀ r, (s * t) ^ 2 ≤ walkTotal Q 4 (Sum.inr r) := by
    intro r
    have := walkTotal_succ_right_lower B 3 (s * (t * s)) t
      (mul_nonneg hs (mul_nonneg ht hs)) hL3 hdegR r
    convert this using 1 <;> ring
  have hL5 : ∀ l, s * (s * t) ^ 2 ≤ walkTotal Q 5 (Sum.inl l) := by
    intro l
    simpa [Q] using walkTotal_succ_left_lower B 4 ((s * t) ^ 2) s
      (sq_nonneg _) hR4 hdegL l
  have hR5 : ∀ r, t * (s * t) ^ 2 ≤ walkTotal Q 5 (Sum.inr r) := by
    intro r
    simpa [Q] using walkTotal_succ_right_lower B 4 ((s * t) ^ 2) t
      (sq_nonneg _) hL4 hdegR r
  have hL6 : ∀ l, (s * t) ^ 3 ≤ walkTotal Q 6 (Sum.inl l) := by
    intro l
    have := walkTotal_succ_left_lower B 5 (t * (s * t) ^ 2) s
      (mul_nonneg ht (sq_nonneg _)) hR5 hdegL l
    convert this using 1 <;> ring
  let T : ℝ := ∑ l : L, ∑ l' : L, walkCount Q 6 (Sum.inl l) (Sum.inl l')
  let S : ℝ := ∑ l : L, ∑ l' : L, walkCount Q 6 (Sum.inl l) (Sum.inl l') ^ 2
  have htotal_l (l : L) : (s * t) ^ 3 ≤
      ∑ l' : L, walkCount Q 6 (Sum.inl l) (Sum.inl l') := by
    have htot := hL6 l
    rw [walkTotal] at htot
    simp only [Fintype.sum_sum_type, Q] at htot
    simpa [walkCount_six_left_right_eq_zero] using htot
  have hTlower : (Fintype.card L : ℝ) * (s * t) ^ 3 ≤ T := by
    dsimp [T]
    calc
      (Fintype.card L : ℝ) * (s * t) ^ 3 = ∑ _l : L, (s * t) ^ 3 := by simp
      _ ≤ ∑ l : L, ∑ l' : L, walkCount Q 6 (Sum.inl l) (Sum.inl l') := by
        apply Finset.sum_le_sum
        intro l hl
        exact htotal_l l
  have hcs : T ^ 2 ≤ (Fintype.card L : ℝ) ^ 2 * S := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (L × L)))
      (f := fun z ↦ walkCount Q 6 (Sum.inl z.1) (Sum.inl z.2))
    simpa [T, S, Fintype.sum_prod_type, Fintype.card_prod, pow_two] using h
  have hcardL : (0 : ℝ) < Fintype.card L := by positivity
  have hST : (s * t) ^ 6 ≤ S := by
    have hsq := pow_le_pow_left₀
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (mul_nonneg hs ht) 3)) hTlower 2
    have hmul : (Fintype.card L : ℝ) ^ 2 * (s * t) ^ 6 ≤
        (Fintype.card L : ℝ) ^ 2 * S := by
      calc
        (Fintype.card L : ℝ) ^ 2 * (s * t) ^ 6 =
            ((Fintype.card L : ℝ) * (s * t) ^ 3) ^ 2 := by ring
        _ ≤ T ^ 2 := hsq
        _ ≤ (Fintype.card L : ℝ) ^ 2 * S := hcs
    by_contra hn
    have hlt : S < (s * t) ^ 6 := lt_of_not_ge hn
    have hstrict := mul_lt_mul_of_pos_left hlt (sq_pos_of_pos hcardL)
    exact (not_lt_of_ge hmul) hstrict
  calc
    (s * t) ^ 6 ≤ S := hST
    _ ≤ homCycleCount Q 12 := by
      rw [show 12 = 2 * 6 by norm_num, homCycleCount_even_eq_sum_sq]
      simp only [Fintype.sum_sum_type, Q, S]
      simp_rw [Finset.sum_add_distrib]
      have h₁ : 0 ≤ ∑ x : L, ∑ y : R,
          walkCount (bipartiteRelGraph B) 6 (Sum.inl x) (Sum.inr y) ^ 2 := by positivity
      have h₂ : 0 ≤ ∑ x : R, ∑ y : L,
          walkCount (bipartiteRelGraph B) 6 (Sum.inr x) (Sum.inl y) ^ 2 := by positivity
      have h₃ : 0 ≤ ∑ x : R, ∑ y : R,
          walkCount (bipartiteRelGraph B) 6 (Sum.inr x) (Sum.inr y) ^ 2 := by positivity
      linarith

def directedEdgeFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (V × V) :=
  Finset.univ.filter fun e ↦ G.Adj e.1 e.2

@[simp] lemma mem_directedEdgeFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    (u, v) ∈ directedEdgeFinset G ↔ G.Adj u v := by
  simp [directedEdgeFinset]

lemma directedEdgeFinset_card_eq_sum_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (directedEdgeFinset G).card = ∑ v : V, G.degree v := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (t := Finset.univ)
    (f := Prod.fst) (s := directedEdgeFinset G) (by simp)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [SimpleGraph.degree]
  apply Finset.card_bij (fun e _ ↦ e.2)
  · intro e he
    rw [Finset.mem_filter] at he
    have hadj := (mem_directedEdgeFinset G e.1 e.2).mp he.1
    simpa [he.2] using hadj
  · intro e₁ he₁ e₂ he₂ h
    have h₁ := (Finset.mem_filter.mp he₁).2
    have h₂ := (Finset.mem_filter.mp he₂).2
    exact Prod.ext (h₁.trans h₂.symm) h
  · intro w hw
    refine ⟨(v, w), ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨(mem_directedEdgeFinset G v w).mpr (by simpa using hw), rfl⟩

noncomputable def degreeIndex200 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (v : V) : Fin 200 :=
  ⟨Nat.log b (G.degree v), Nat.log_lt_of_lt_pow' (by norm_num) (hdegree v)⟩

lemma degreeIndex200_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (v : V) (hv : G.degree v ≠ 0) :
    b ^ (degreeIndex200 G b hdegree v).1 ≤ G.degree v :=
  Nat.pow_log_le_self b hv

lemma degreeIndex200_upper {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ) (hb : 1 < b)
    (hdegree : ∀ v, G.degree v < b ^ 200) (v : V) :
    G.degree v < b ^ ((degreeIndex200 G b hdegree v).1 + 1) :=
  Nat.lt_pow_succ_log_self hb _

abbrev DegreeBin200 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (i : Fin 200) :=
  {v : V // degreeIndex200 G b hdegree v = i ∧ G.degree v ≠ 0}

def degreeBinRel {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (i j : Fin 200) :
    DegreeBin200 G b hdegree i → DegreeBin200 G b hdegree j → Prop :=
  fun u v ↦ G.Adj u.1 v.1

instance degreeBinRel.instDecidable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (i j : Fin 200) :
    ∀ u v, Decidable (degreeBinRel G b hdegree i j u v) := by
  intro u v
  exact inferInstanceAs (Decidable (G.Adj u.1 v.1))

noncomputable def degreeEdgeFiber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (ij : Fin 200 × Fin 200) :
    Finset (V × V) :=
  (directedEdgeFinset G).filter fun e ↦
    (degreeIndex200 G b hdegree e.1, degreeIndex200 G b hdegree e.2) = ij

lemma degreeEdgeFiber_card_eq_rel {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (i j : Fin 200) :
    (degreeEdgeFiber G b hdegree (i, j)).card =
      (relEdgeFinset (degreeBinRel G b hdegree i j)).card := by
  classical
  apply Finset.card_bij (fun e he ↦
    (⟨e.1, congrArg Prod.fst (Finset.mem_filter.mp he).2,
      ((mem_directedEdgeFinset G e.1 e.2).mp (Finset.mem_filter.mp he).1).degree_pos_left.ne'⟩,
      ⟨e.2, congrArg Prod.snd (Finset.mem_filter.mp he).2,
      ((mem_directedEdgeFinset G e.1 e.2).mp (Finset.mem_filter.mp he).1).degree_pos_right.ne'⟩))
  · intro e he
    rw [mem_relEdgeFinset]
    exact (mem_directedEdgeFinset G e.1 e.2).mp (Finset.mem_filter.mp he).1
  · intro e₁ he₁ e₂ he₂ h
    exact Prod.ext (congrArg (fun z ↦ z.1.1) h) (congrArg (fun z ↦ z.2.1) h)
  · intro e he
    refine ⟨(e.1.1, e.2.1), ?_, rfl⟩
    rw [degreeEdgeFiber, Finset.mem_filter]
    have he' : degreeBinRel G b hdegree i j e.1 e.2 :=
      (mem_relEdgeFinset (degreeBinRel G b hdegree i j) e.1 e.2).mp he
    exact ⟨(mem_directedEdgeFinset G _ _).mpr he', Prod.ext e.1.2.1 e.2.2.1⟩

lemma exists_large_degreeEdgeFiber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) :
    ∃ ij : Fin 200 × Fin 200, (directedEdgeFinset G).card ≤
      40000 * (degreeEdgeFiber G b hdegree ij).card := by
  classical
  let f : Fin 200 × Fin 200 → ℕ := fun ij ↦ (degreeEdgeFiber G b hdegree ij).card
  obtain ⟨ij, hij⟩ := Finite.exists_max f
  refine ⟨ij, ?_⟩
  calc
    (directedEdgeFinset G).card = ∑ z : Fin 200 × Fin 200, f z := by
      rw [Finset.card_eq_sum_card_fiberwise (t := Finset.univ)
        (f := fun e ↦ (degreeIndex200 G b hdegree e.1,
          degreeIndex200 G b hdegree e.2)) (s := directedEdgeFinset G) (by simp)]
      apply Finset.sum_congr rfl
      intro z hz
      rfl
    _ ≤ ∑ _z : Fin 200 × Fin 200, f ij := by
      apply Finset.sum_le_sum
      intro z hz
      exact hij z
    _ = 40000 * (degreeEdgeFiber G b hdegree ij).card := by
      simp [f]

def sumPairMap {L R V : Type*} (fL : L → OrderedPair V)
    (fR : R → OrderedPair V) : L ⊕ R → OrderedPair V
  | Sum.inl l => fL l
  | Sum.inr r => fR r

def pairSupportConflictVia {L R V : Type*} [DecidableEq V]
    (fL : L → OrderedPair V) (fR : R → OrderedPair V) :
    (L ⊕ R) → (L ⊕ R) → Prop :=
  fun x y ↦ ¬Disjoint (orderedPairSupport (sumPairMap fL fR x))
    (orderedPairSupport (sumPairMap fL fR y))

noncomputable instance pairSupportConflictVia.instDecidableRel
    {L R V : Type*} [DecidableEq V]
    (fL : L → OrderedPair V) (fR : R → OrderedPair V) :
    DecidableRel (pairSupportConflictVia fL fR) := by
  intro x y
  exact Classical.propDecidable _

lemma pairSupportConflictVia_symm {L R V : Type*} [DecidableEq V]
    (fL : L → OrderedPair V) (fR : R → OrderedPair V) :
    Symmetric (pairSupportConflictVia fL fR) := by
  intro x y h
  exact fun hdisj ↦ h hdisj.symm

def ClosedWalk.mapHom12 {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (w : ClosedWalk G 12) : ClosedWalk H 12 :=
  ⟨f w.1, ⟨w.2.1.map f, by simpa using w.2.2⟩⟩

@[simp] lemma ClosedWalk.mapHom12_getVert {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (f : G →g H) (w : ClosedWalk G 12) (i : ℕ) :
    (w.mapHom12 f).2.1.getVert i = f (w.2.1.getVert i) := by
  simp [ClosedWalk.mapHom12, SimpleGraph.Walk.getVert_map]

lemma all_closedWalks_conflicting_of_free
    {L R V : Type*} [Fintype L] [Fintype R] [Fintype V]
    [DecidableEq L] [DecidableEq R] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (fL : L → OrderedPair V) (fR : R → OrderedPair V)
    (hmap : ∀ l r, B l r → pairComplete G (fL l) (fR r))
    (hfree : counterexampleGraph.Free G)
    (w : ClosedWalk (bipartiteRelGraph B) 12) :
    ∃ i j : Fin 12, i ≠ j ∧
      pairSupportConflictVia fL fR (w.2.1.getVert i.1) (w.2.1.getVert j.1) := by
  let f := bipartiteRelGraphHom (pairAuxGraph G) fL fR hmap
  let w' := w.mapHom12 f
  by_contra hn
  push_neg at hn
  have hgood : w'.HasDisjointPairSupports G := by
    intro i j hij
    have := hn i j hij
    dsimp only [w', ClosedWalk.mapHom12]
    simp only [SimpleGraph.Walk.getVert_map]
    dsimp only [f, bipartiteRelGraphHom]
    simp only [RelHom.coeFn_mk]
    have hsum (x : L ⊕ R) : Sum.elim fL fR x = sumPairMap fL fR x := by
      cases x <;> rfl
    rw [hsum, hsum]
    exact Classical.not_not.mp this
  exact hfree (counterexampleGraph_isContained_of_goodClosedWalk G w' hgood)

lemma relLeftDegreeReal_le_auxDegree
    {L R V : Type*} [Fintype L] [Fintype R] [Fintype V]
    [DecidableEq L] [DecidableEq R] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (fL : L → OrderedPair V) (fR : R → OrderedPair V)
    (hfR : Function.Injective fR)
    (hmap : ∀ l r, B l r → pairComplete G (fL l) (fR r)) (l : L) :
    relLeftDegreeReal B l ≤ (pairAuxGraph G).degree (fL l) := by
  classical
  let candidates := Finset.univ.filter fun r ↦ B l r
  have hcard : (candidates.card : ℝ) = relLeftDegreeReal B l := by
    rw [relLeftDegreeReal]
    simp [candidates, apply_ite]
  rw [← hcard]
  norm_cast
  apply Finset.card_le_card_of_injOn fR
  · intro r hr
    change fR r ∈ (pairAuxGraph G).neighborFinset (fL l)
    rw [(pairAuxGraph G).mem_neighborFinset]
    exact hmap l r (Finset.mem_filter.mp hr).2
  · exact fun _ _ _ _ h ↦ hfR h

lemma leftConflictDegreeReal_le_auxConflict
    {L R V : Type*} [Fintype L] [Fintype R] [Fintype V]
    [DecidableEq L] [DecidableEq R] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (fL : L → OrderedPair V) (fR : R → OrderedPair V)
    (hfL : Function.Injective fL)
    (hmap : ∀ l r, B l r → pairComplete G (fL l) (fR r))
    (u : L ⊕ R) (r : R) :
    leftConflictDegreeReal B (pairSupportConflictVia fL fR) u r ≤
      4 * (Real.sqrt ((pairAuxGraph G).degree (fR r) : ℝ) + 1) := by
  classical
  let candidates := {l : L // B l r ∧
    pairSupportConflictVia fL fR (Sum.inl l) u}
  have hcard : (Nat.card candidates : ℝ) =
      leftConflictDegreeReal B (pairSupportConflictVia fL fR) u r := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, leftConflictDegreeReal]
    simp [candidates]
  rw [← hcard]
  let encode : candidates →
      LocalConflictNeighbor G (sumPairMap fL fR u) (fR r) := fun z ↦
    ⟨fL z.1, (pairComplete_comm G _ _).mpr (hmap z.1 r z.2.1),
      fun hd ↦ z.2.2 hd.symm⟩
  have hencode : Function.Injective encode := by
    intro z z' h
    apply Subtype.ext
    apply hfL
    exact congrArg Subtype.val h
  calc
    (Nat.card candidates : ℝ) ≤
        Nat.card (LocalConflictNeighbor G (sumPairMap fL fR u) (fR r)) := by
      exact_mod_cast Nat.card_le_card_of_injective encode hencode
    _ ≤ 4 * (Real.sqrt ((pairAuxGraph G).degree (fR r) : ℝ) + 1) :=
      localConflictNeighbor_card_real_le G _ _

abbrev CoreLeft {L : Type*} (S : Finset L) := {l : L // l ∈ S}
abbrev CoreRight {R : Type*} (T : Finset R) := {r : R // r ∈ T}

def coreRel {L R : Type*} (B : L → R → Prop) (S : Finset L) (T : Finset R) :
    CoreLeft S → CoreRight T → Prop := fun l r ↦ B l.1 r.1

instance coreRel.instDecidable {L R : Type*} (B : L → R → Prop)
    [∀ l r, Decidable (B l r)] (S : Finset L) (T : Finset R) :
    ∀ l r, Decidable (coreRel B S T l r) := by
  intro l r
  exact inferInstanceAs (Decidable (B l.1 r.1))

lemma relLeftDegreeReal_coreRel
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (S : Finset L) (T : Finset R) (l : CoreLeft S) :
    relLeftDegreeReal (coreRel B S T) l = restrictedLeftDegree B T l.1 := by
  classical
  rw [relLeftDegreeReal]
  have hpoint (r : CoreRight T) :
      (if coreRel B S T l r then (1 : ℝ) else 0) =
        if B l.1 r.1 then 1 else 0 := by
    by_cases h : B l.1 r.1 <;> simp [coreRel, h]
  simp_rw [hpoint]
  calc
    (∑ r : CoreRight T, if B l.1 r.1 then (1 : ℝ) else 0) =
        ∑ r ∈ T, if B l.1 r then 1 else 0 :=
      (Finset.sum_subtype T (fun _ ↦ Iff.rfl)
        (fun r ↦ if B l.1 r then (1 : ℝ) else 0)).symm
    _ = restrictedLeftDegree B T l.1 := by
      simpa [restrictedLeftDegree] using
        (Finset.sum_boole (R := ℝ) (fun r : R ↦ B l.1 r) T)

lemma relRightDegreeReal_coreRel
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (S : Finset L) (T : Finset R) (r : CoreRight T) :
    relLeftDegreeReal (fun r l ↦ coreRel B S T l r) r =
      restrictedRightDegree B S r.1 := by
  classical
  rw [relLeftDegreeReal]
  have hpoint (l : CoreLeft S) :
      (if coreRel B S T l r then (1 : ℝ) else 0) =
        if B l.1 r.1 then 1 else 0 := by
    by_cases h : B l.1 r.1 <;> simp [coreRel, h]
  simp_rw [hpoint]
  calc
    (∑ l : CoreLeft S, if B l.1 r.1 then (1 : ℝ) else 0) =
        ∑ l ∈ S, if B l r.1 then 1 else 0 :=
      (Finset.sum_subtype S (fun _ ↦ Iff.rfl)
        (fun l ↦ if B l r.1 then (1 : ℝ) else 0)).symm
    _ = restrictedRightDegree B S r.1 := by
      simpa [restrictedRightDegree] using
        (Finset.sum_boole (R := ℝ) (fun l : L ↦ B l r.1) S)

lemma relEdgeFinset_card_real_eq_sum_left
    {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] :
    ((relEdgeFinset B).card : ℝ) = ∑ l : L, relLeftDegreeReal B l := by
  simp only [relLeftDegreeReal]
  rw [← Finset.sum_product' (Finset.univ : Finset L) (Finset.univ : Finset R)]
  rw [Finset.univ_product_univ]
  rw [relEdgeFinset]
  exact (Finset.sum_boole (R := ℝ) (fun e : L × R ↦ B e.1 e.2)
    (Finset.univ : Finset (L × R))).symm

lemma relLeftDegreeReal_le_graphDegree
    {L R V : Type*} [Fintype L] [Fintype R] [Fintype V]
    [DecidableEq R] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (fL : L → V) (fR : R → V) (hfR : Function.Injective fR)
    (hmap : ∀ l r, B l r → G.Adj (fL l) (fR r)) (l : L) :
    relLeftDegreeReal B l ≤ G.degree (fL l) := by
  classical
  let candidates := Finset.univ.filter fun r ↦ B l r
  have hcard : (candidates.card : ℝ) = relLeftDegreeReal B l := by
    rw [relLeftDegreeReal]
    simpa [candidates] using
      (Finset.sum_boole (R := ℝ) (fun r : R ↦ B l r) Finset.univ).symm
  rw [← hcard]
  norm_cast
  apply Finset.card_le_card_of_injOn fR
  · intro r hr
    simpa using hmap l r (Finset.mem_filter.mp hr).2
  · exact fun _ _ _ _ h ↦ hfR h

lemma relEdgeFinset_coreRel_card_le
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (S : Finset L) (T : Finset R) :
    (relEdgeFinset (coreRel B S T)).card ≤ (relEdgeFinset B).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun e ↦ (e.1.1, e.2.1))
  · intro e he
    exact (mem_relEdgeFinset B _ _).mpr ((mem_relEdgeFinset (coreRel B S T) _ _).mp he)
  · intro e₁ he₁ e₂ he₂ h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

lemma homCycleCount_bipartiteRel_two
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] :
    homCycleCount (bipartiteRelGraph B) 2 = 2 * (relEdgeFinset B).card := by
  rw [show 2 = 2 * 1 by norm_num, homCycleCount_even_eq_sum_sq]
  simp only [Fintype.sum_sum_type]
  have hwalk (l : L) (r : R) :
      walkCount (bipartiteRelGraph B) 1 (Sum.inl l) (Sum.inr r) =
        if B l r then 1 else 0 := by
    rw [walkCount, pow_one]
    change (if B l r then 1 else 0) = _
    rfl
  have hwalk' (r : R) (l : L) :
      walkCount (bipartiteRelGraph B) 1 (Sum.inr r) (Sum.inl l) =
        if B l r then 1 else 0 := by
    rw [walkCount, pow_one]
    change (if B l r then 1 else 0) = _
    rfl
  have hzeroLL (l l' : L) :
      walkCount (bipartiteRelGraph B) 1 (Sum.inl l) (Sum.inl l') = 0 := by
    rw [walkCount, pow_one]
    change (if False then 1 else 0) = 0
    simp
  have hzeroRR (r r' : R) :
      walkCount (bipartiteRelGraph B) 1 (Sum.inr r) (Sum.inr r') = 0 := by
    rw [walkCount, pow_one]
    change (if False then 1 else 0) = 0
    simp
  simp_rw [hwalk, hwalk', hzeroLL, hzeroRR]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero,
    zero_add, add_zero]
  have hcount :
      (∑ l : L, ∑ r : R, (if B l r then (1 : ℝ) else 0) ^ 2) =
        (relEdgeFinset B).card := by
    calc
      (∑ l : L, ∑ r : R, (if B l r then (1 : ℝ) else 0) ^ 2) =
          ∑ e : L × R, (if B e.1 e.2 then (1 : ℝ) else 0) ^ 2 :=
        by
          simpa only [Finset.univ_product_univ] using
            (Finset.sum_product' (Finset.univ : Finset L)
              (Finset.univ : Finset R)
              (fun l r ↦ (if B l r then (1 : ℝ) else 0) ^ 2)).symm
      _ = (relEdgeFinset B).card := by
        have hsq (e : L × R) :
            (if B e.1 e.2 then (1 : ℝ) else 0) ^ 2 =
              if B e.1 e.2 then 1 else 0 := by
          by_cases h : B e.1 e.2 <;> simp [h]
        simp_rw [hsq]
        rw [relEdgeFinset]
        exact Finset.sum_boole (R := ℝ) (fun e : L × R ↦ B e.1 e.2)
          (Finset.univ : Finset (L × R))
  have hcount' :
      (∑ r : R, ∑ l : L, (if B l r then (1 : ℝ) else 0) ^ 2) =
        (relEdgeFinset B).card := by
    rw [Finset.sum_comm]
    exact hcount
  rw [hcount]
  rw [hcount']
  ring

lemma degreeBin_card_mul_lower_le_directedEdge_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (i : Fin 200) :
    Fintype.card (DegreeBin200 G b hdegree i) * b ^ i.1 ≤
      (directedEdgeFinset G).card := by
  classical
  rw [directedEdgeFinset_card_eq_sum_degree]
  calc
    Fintype.card (DegreeBin200 G b hdegree i) * b ^ i.1 =
        ∑ _v : DegreeBin200 G b hdegree i, b ^ i.1 := by simp
    _ ≤ ∑ v : DegreeBin200 G b hdegree i, G.degree v.1 := by
      apply Finset.sum_le_sum
      intro v hv
      simpa [v.2.1] using degreeIndex200_lower G b hdegree v.1 v.2.2
    _ ≤ ∑ v : V, G.degree v := by
      rw [← Finset.sum_subtype
        ((Finset.univ : Finset V).filter fun v ↦
          degreeIndex200 G b hdegree v = i ∧ G.degree v ≠ 0)
        (fun v ↦ by simp) (fun v ↦ G.degree v)]
      exact Finset.sum_le_sum_of_subset (by simp)

lemma degreeBinRel_edge_card_le_card_mul_upper
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ) (hb : 1 < b)
    (hdegree : ∀ v, G.degree v < b ^ 200) (i j : Fin 200) :
    (relEdgeFinset (degreeBinRel G b hdegree i j)).card ≤
      Fintype.card (DegreeBin200 G b hdegree i) * b ^ (i.1 + 1) := by
  have hsum := relEdgeFinset_card_real_eq_sum_left
    (degreeBinRel G b hdegree i j)
  have hdeg (l : DegreeBin200 G b hdegree i) :
      relLeftDegreeReal (degreeBinRel G b hdegree i j) l ≤
        (b ^ (i.1 + 1) : ℕ) := by
    calc
      relLeftDegreeReal (degreeBinRel G b hdegree i j) l ≤ G.degree l.1 :=
        relLeftDegreeReal_le_graphDegree G (degreeBinRel G b hdegree i j)
          (fun u ↦ u.1) (fun v ↦ v.1)
          (fun _ _ h ↦ Subtype.ext h) (fun _ _ h ↦ h) l
      _ ≤ (b ^ (i.1 + 1) : ℕ) := by
        have hu := (degreeIndex200_upper G b hb hdegree l.1).le
        rw [l.2.1] at hu
        exact_mod_cast hu
  have hreal :
      ((relEdgeFinset (degreeBinRel G b hdegree i j)).card : ℝ) ≤
        Fintype.card (DegreeBin200 G b hdegree i) *
          (b ^ (i.1 + 1) : ℕ) := by
    rw [hsum]
    calc
      (∑ l : DegreeBin200 G b hdegree i,
          relLeftDegreeReal (degreeBinRel G b hdegree i j) l) ≤
          ∑ _l : DegreeBin200 G b hdegree i,
            ((b ^ (i.1 + 1) : ℕ) : ℝ) := by
        exact Finset.sum_le_sum fun l _ ↦ hdeg l
      _ = Fintype.card (DegreeBin200 G b hdegree i) *
          (b ^ (i.1 + 1) : ℕ) := by simp
  exact_mod_cast hreal

lemma relEdgeFinset_transpose_card
    {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] :
    (relEdgeFinset (fun r l ↦ B l r)).card = (relEdgeFinset B).card := by
  classical
  apply Finset.card_bij (fun e _ ↦ (e.2, e.1))
  · intro e he
    simpa using (mem_relEdgeFinset (fun r l ↦ B l r) e.1 e.2).mp he
  · intro e₁ h₁ e₂ h₂ h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · intro e he
    refine ⟨(e.2, e.1), ?_, rfl⟩
    simpa using (mem_relEdgeFinset B e.1 e.2).mp he

/-- The explicit absolute constant in the seventh-power bound for the
ordered-pair auxiliary graph.  Its size is irrelevant; keeping it factored
makes the arithmetic proof transparent. -/
noncomputable def auxiliarySeventhPowerConstant : ℝ :=
  40000 ^ 7 * (2 * 160000 ^ 12 * 16000000 ^ 5) ^ 2

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos147.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 147.
https://www.erdosproblems.com/forum/thread/147

Informal authors:
- Oliver Janzer

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos147.md
-/

open Filter
open Asymptotics
open scoped SimpleGraph Topology



set_option autoImplicit false

lemma degreeFiber_seventh_power_bound_of_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : ℕ) (hb : 1 < b)
    (hdegree : ∀ p : OrderedPair V, (pairAuxGraph G).degree p < b ^ 200)
    (i j : Fin 200)
    (hlarge : (directedEdgeFinset (pairAuxGraph G)).card ≤
      40000 * (relEdgeFinset
        (degreeBinRel (pairAuxGraph G) b hdegree i j)).card)
    (horder : b ^ (i.1 + 1) ≤ b ^ (j.1 + 1))
    (hfree : counterexampleGraph.Free G) :
    ((directedEdgeFinset (pairAuxGraph G)).card : ℝ) ^ 7 ≤
      auxiliarySeventhPowerConstant *
        (Fintype.card (OrderedPair V) : ℝ) ^ 9 * (b : ℝ) ^ 24 := by
  classical
  let A := pairAuxGraph G
  let L₀ := DegreeBin200 A b hdegree i
  let R₀ := DegreeBin200 A b hdegree j
  let B₀ : L₀ → R₀ → Prop := degreeBinRel A b hdegree i j
  let q : ℝ := (directedEdgeFinset A).card
  let e : ℝ := (relEdgeFinset B₀).card
  let N : ℝ := Fintype.card (OrderedPair V)
  let D₁ : ℝ := b ^ (i.1 + 1)
  let D₂ : ℝ := b ^ (j.1 + 1)
  change q ^ 7 ≤ auxiliarySeventhPowerConstant * N ^ 9 * (b : ℝ) ^ 24
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (lt_trans (by omega : 0 < 1) hb)
  have hN0 : 0 ≤ N := by positivity
  have hD₁ : 0 < D₁ := by positivity
  have hD₂ : 0 < D₂ := by positivity
  have hDord : D₁ ≤ D₂ := by
    dsimp [D₁, D₂]
    exact_mod_cast horder
  have hlargeR : q ≤ 40000 * e := by
    dsimp [q, e, A, B₀, L₀, R₀]
    exact_mod_cast hlarge
  by_cases hqzero : q = 0
  · have hconst : 0 ≤ auxiliarySeventhPowerConstant := by
      dsimp [auxiliarySeventhPowerConstant]
      positivity
    calc
      q ^ 7 = 0 := by rw [hqzero]; norm_num
      _ ≤ auxiliarySeventhPowerConstant * N ^ 9 * (b : ℝ) ^ 24 :=
        mul_nonneg (mul_nonneg hconst (pow_nonneg hN0 9))
          (pow_nonneg hb0.le 24)
  have hq : 0 < q := lt_of_le_of_ne (by positivity) (Ne.symm hqzero)
  have he : 0 < e := by nlinarith
  have hB₀nonempty : (relEdgeFinset B₀).Nonempty := by
    apply Finset.card_pos.mp
    dsimp [e] at he
    exact_mod_cast he
  obtain ⟨S, T, hS, hT, hcoreL, hcoreR⟩ :=
    exists_twoSided_relCore B₀ hB₀nonempty
  let B : CoreLeft S → CoreRight T → Prop := coreRel B₀ S T
  let fL : CoreLeft S → OrderedPair V := fun l ↦ l.1.1
  let fR : CoreRight T → OrderedPair V := fun r ↦ r.1.1
  have hfL : Function.Injective fL := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hfR : Function.Injective fR := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hmap : ∀ l r, B l r → pairComplete G (fL l) (fR r) := by
    intro l r hlr
    exact hlr
  have hcardLpos : (0 : ℝ) < Fintype.card L₀ := by
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty L₀ from ⟨hS.choose⟩)
  have hcardRpos : (0 : ℝ) < Fintype.card R₀ := by
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty R₀ from ⟨hT.choose⟩)
  have hbinL := degreeBin_card_mul_lower_le_directedEdge_card A b hdegree i
  have hbinR := degreeBin_card_mul_lower_le_directedEdge_card A b hdegree j
  have hbinLR :
      (Fintype.card L₀ : ℝ) * D₁ ≤ (b : ℝ) * q := by
    have hnat : Fintype.card L₀ * b ^ i.1 ≤ (directedEdgeFinset A).card := by
      simpa [L₀] using hbinL
    have hreal : (Fintype.card L₀ : ℝ) * (b : ℝ) ^ i.1 ≤ q := by
      dsimp [q]
      exact_mod_cast hnat
    have h := mul_le_mul_of_nonneg_left hreal (Nat.cast_nonneg b)
    calc
      (Fintype.card L₀ : ℝ) * D₁ =
          (b : ℝ) * ((Fintype.card L₀ : ℝ) * (b : ℝ) ^ i.1) := by
        dsimp [D₁]
        rw [pow_succ]
        ring
      _ ≤ (b : ℝ) * q := h
  have hbinRR :
      (Fintype.card R₀ : ℝ) * D₂ ≤ (b : ℝ) * q := by
    have hnat : Fintype.card R₀ * b ^ j.1 ≤ (directedEdgeFinset A).card := by
      simpa [R₀] using hbinR
    have hreal : (Fintype.card R₀ : ℝ) * (b : ℝ) ^ j.1 ≤ q := by
      dsimp [q]
      exact_mod_cast hnat
    have h := mul_le_mul_of_nonneg_left hreal (Nat.cast_nonneg b)
    calc
      (Fintype.card R₀ : ℝ) * D₂ =
          (b : ℝ) * ((Fintype.card R₀ : ℝ) * (b : ℝ) ^ j.1) := by
        dsimp [D₂]
        rw [pow_succ]
        ring
      _ ≤ (b : ℝ) * q := h
  have hminL (l : CoreLeft S) :
      D₁ / (160000 * (b : ℝ)) ≤ relLeftDegreeReal B l := by
    have hc : e ≤ 4 * Fintype.card L₀ * restrictedLeftDegree B₀ T l.1 := by
      dsimp [e]
      exact_mod_cast hcoreL l.1 l.2
    have h₁ := mul_le_mul_of_nonneg_left hlargeR (Nat.cast_nonneg b)
    have h₂ := mul_le_mul_of_nonneg_left hc
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 40000) (Nat.cast_nonneg b))
    have hcross : D₁ ≤
        160000 * (b : ℝ) * restrictedLeftDegree B₀ T l.1 := by
      have : (Fintype.card L₀ : ℝ) * D₁ ≤
          (Fintype.card L₀ : ℝ) *
            (160000 * (b : ℝ) * restrictedLeftDegree B₀ T l.1) := by
        calc
          (Fintype.card L₀ : ℝ) * D₁ ≤ (b : ℝ) * q := hbinLR
          _ ≤ (b : ℝ) * (40000 * e) := h₁
          _ ≤ (Fintype.card L₀ : ℝ) *
              (160000 * (b : ℝ) * restrictedLeftDegree B₀ T l.1) := by
            nlinarith [h₂]
      nlinarith
    rw [relLeftDegreeReal_coreRel B₀ S T l]
    exact (div_le_iff₀ (mul_pos (by norm_num) hb0)).2 (by nlinarith)
  have hminR (r : CoreRight T) :
      D₂ / (160000 * (b : ℝ)) ≤
        relLeftDegreeReal (fun r l ↦ B l r) r := by
    have hc : e ≤ 4 * Fintype.card R₀ * restrictedRightDegree B₀ S r.1 := by
      dsimp [e]
      exact_mod_cast hcoreR r.1 r.2
    have h₁ := mul_le_mul_of_nonneg_left hlargeR (Nat.cast_nonneg b)
    have h₂ := mul_le_mul_of_nonneg_left hc
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 40000) (Nat.cast_nonneg b))
    have hcross : D₂ ≤
        160000 * (b : ℝ) * restrictedRightDegree B₀ S r.1 := by
      have : (Fintype.card R₀ : ℝ) * D₂ ≤
          (Fintype.card R₀ : ℝ) *
            (160000 * (b : ℝ) * restrictedRightDegree B₀ S r.1) := by
        calc
          (Fintype.card R₀ : ℝ) * D₂ ≤ (b : ℝ) * q := hbinRR
          _ ≤ (b : ℝ) * (40000 * e) := h₁
          _ ≤ (Fintype.card R₀ : ℝ) *
              (160000 * (b : ℝ) * restrictedRightDegree B₀ S r.1) := by
            nlinarith [h₂]
      nlinarith
    rw [relRightDegreeReal_coreRel B₀ S T r]
    exact (div_le_iff₀ (mul_pos (by norm_num) hb0)).2 (by nlinarith)
  have hmaxL (l : CoreLeft S) : relLeftDegreeReal B l ≤ D₁ := by
    calc
      relLeftDegreeReal B l ≤ A.degree (fL l) :=
        relLeftDegreeReal_le_auxDegree G B fL fR hfR hmap l
      _ ≤ D₁ := by
        have hu := (degreeIndex200_upper A b hb hdegree (fL l)).le
        rw [l.1.2.1] at hu
        dsimp [D₁]
        exact_mod_cast hu
  have hmaxR (r : CoreRight T) :
      relLeftDegreeReal (fun r l ↦ B l r) r ≤ D₂ := by
    calc
      relLeftDegreeReal (fun r l ↦ B l r) r ≤ A.degree (fR r) :=
        relLeftDegreeReal_le_auxDegree G (fun r l ↦ B l r) fR fL hfL
          (fun r l h ↦ (pairComplete_comm G _ _).mpr (hmap l r h)) r
      _ ≤ D₂ := by
        have hu := (degreeIndex200_upper A b hb hdegree (fR r)).le
        rw [r.1.2.1] at hu
        dsimp [D₂]
        exact_mod_cast hu
  let C := pairSupportConflictVia fL fR
  have hconfL (u : CoreLeft S ⊕ CoreRight T) (r : CoreRight T) :
      leftConflictDegreeReal B C u r ≤ 8 * Real.sqrt D₂ := by
    have hlocal := leftConflictDegreeReal_le_auxConflict G B fL fR hfL hmap u r
    have hdeg : (A.degree (fR r) : ℝ) ≤ D₂ := by
      have hu := (degreeIndex200_upper A b hb hdegree (fR r)).le
      rw [r.1.2.1] at hu
      dsimp [D₂]
      exact_mod_cast hu
    have hsqrt := Real.sqrt_le_sqrt hdeg
    have hone : (1 : ℝ) ≤ Real.sqrt D₂ := by
      rw [Real.one_le_sqrt]
      dsimp [D₂]
      exact one_le_pow₀ (by exact_mod_cast (le_of_lt hb))
    nlinarith
  have hconfR (u : CoreRight T ⊕ CoreLeft S) (l : CoreLeft S) :
      leftConflictDegreeReal (fun r l ↦ B l r) (swapConflict C) u l ≤
        8 * Real.sqrt D₁ := by
    have hlocal := leftConflictDegreeReal_le_auxConflict G
      (fun r l ↦ B l r) fR fL hfR
      (fun r l h ↦ (pairComplete_comm G _ _).mpr (hmap l r h)) u l
    have hswap : ∀ x y,
        swapConflict C x y ↔ pairSupportConflictVia fR fL x y := by
      rintro (r | l') (r' | l'') <;>
        simp [C, swapConflict, pairSupportConflictVia, sumPairMap]
    have heq :
        leftConflictDegreeReal (fun r l ↦ B l r) (swapConflict C) u l =
          leftConflictDegreeReal (fun r l ↦ B l r)
            (pairSupportConflictVia fR fL) u l := by
      simp only [leftConflictDegreeReal]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hB : B l r
      · by_cases hC : swapConflict C (Sum.inl r) u
        · have hC' := (hswap (Sum.inl r) u).mp hC
          simp [hB, hC, hC']
        · have hC' : ¬pairSupportConflictVia fR fL (Sum.inl r) u :=
            fun h ↦ hC ((hswap (Sum.inl r) u).mpr h)
          simp [hB, hC, hC']
      · simp [hB]
    rw [heq]
    have hdeg : (A.degree (fL l) : ℝ) ≤ D₁ := by
      have hu := (degreeIndex200_upper A b hb hdegree (fL l)).le
      rw [l.1.2.1] at hu
      dsimp [D₁]
      exact_mod_cast hu
    have hsqrt := Real.sqrt_le_sqrt hdeg
    have hone : (1 : ℝ) ≤ Real.sqrt D₁ := by
      rw [Real.one_le_sqrt]
      dsimp [D₁]
      exact one_le_pow₀ (by exact_mod_cast (le_of_lt hb))
    nlinarith
  have hall (w : ClosedWalk (bipartiteRelGraph B) 12) :
      ∃ a c : Fin 12, a ≠ c ∧ C (w.2.1.getVert a.1) (w.2.1.getVert c.1) :=
    all_closedWalks_conflicting_of_free G B fL fR hmap hfree w
  have hcycle := homCycleCount_twelve_le_of_all_conflicting B C
    (pairSupportConflictVia_symm fL fR) D₁ D₂
    (8 * Real.sqrt D₂) (8 * Real.sqrt D₁) hD₁ hD₂
    (by positivity) (by positivity) hDord hmaxL hmaxR hconfL hconfR
    le_rfl le_rfl hall
  let K : ℝ := 16000000 * (D₂ * Real.sqrt D₁)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcycle₂ := homCycleCount_twelve_le_two_of_ten_bound
    (bipartiteRelGraph B) K hK (by simpa [K] using hcycle)
  have hLnonempty : Nonempty (CoreLeft S) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  have hlower := homCycleCount_twelve_lower_of_minDegrees B
    (D₁ / (160000 * (b : ℝ))) (D₂ / (160000 * (b : ℝ)))
    (by positivity) (by positivity) hminL hminR
  have hcoreEdge :
      ((relEdgeFinset B).card : ℝ) ≤ N * D₁ := by
    have hsub := relEdgeFinset_coreRel_card_le B₀ S T
    have hupper := degreeBinRel_edge_card_le_card_mul_upper A b hb hdegree i j
    have hcardLN : (Fintype.card L₀ : ℝ) ≤ N := by
      dsimp [N]
      exact_mod_cast Fintype.card_le_of_injective (fun l : L₀ ↦ l.1)
        (fun _ _ h ↦ Subtype.ext h)
    calc
      ((relEdgeFinset B).card : ℝ) ≤ (relEdgeFinset B₀).card := by
        exact_mod_cast hsub
      _ ≤ (Fintype.card L₀ : ℝ) * D₁ := by
        dsimp [B₀, L₀, D₁, A]
        exact_mod_cast hupper
      _ ≤ N * D₁ := mul_le_mul_of_nonneg_right hcardLN hD₁.le
  have htwo : homCycleCount (bipartiteRelGraph B) 2 ≤ 2 * N * D₁ := by
    rw [homCycleCount_bipartiteRel_two B]
    nlinarith
  have hcombined :
      ((D₁ / (160000 * (b : ℝ))) *
        (D₂ / (160000 * (b : ℝ)))) ^ 6 ≤
        K ^ 5 * (2 * N * D₁) :=
    hlower.trans (hcycle₂.trans (mul_le_mul_of_nonneg_left htwo (pow_nonneg hK 5)))
  let x := Real.sqrt D₁
  have hx : 0 < x := Real.sqrt_pos.2 hD₁
  have hx2 : x ^ 2 = D₁ := Real.sq_sqrt hD₁.le
  let M : ℝ := 2 * 160000 ^ 12 * 16000000 ^ 5
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hpoly : x ^ 12 * D₂ ^ 6 ≤ M * N * (b : ℝ) ^ 12 * x ^ 7 * D₂ ^ 5 := by
    have hden : 0 < (160000 * (b : ℝ)) ^ 12 := by positivity
    have hcross : (D₁ * D₂) ^ 6 ≤
        (K ^ 5 * (2 * N * D₁)) * (160000 * (b : ℝ)) ^ 12 := by
      have heq :
          ((D₁ / (160000 * (b : ℝ))) *
            (D₂ / (160000 * (b : ℝ)))) ^ 6 =
            (D₁ * D₂) ^ 6 / (160000 * (b : ℝ)) ^ 12 := by
        field_simp
      rw [heq] at hcombined
      exact (div_le_iff₀ hden).mp hcombined
    dsimp [K, M] at hcross ⊢
    rw [← hx2] at hcross
    rw [Real.sqrt_sq hx.le] at hcross
    convert hcross using 1 <;> ring
  have hxD : x ^ 7 ≤ M * N * (b : ℝ) ^ 12 := by
    have hfactor : 0 < x ^ 7 * D₂ ^ 5 := mul_pos (pow_pos hx 7) (pow_pos hD₂ 5)
    have hcancel : x ^ 5 * D₂ ≤ M * N * (b : ℝ) ^ 12 := by
      by_contra hn
      have hlt := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hfactor
      apply (not_lt_of_ge hpoly)
      convert hlt using 1 <;> ring
    have hxd2 : x ^ 2 ≤ D₂ := by rw [hx2]; exact hDord
    calc
      x ^ 7 = x ^ 5 * x ^ 2 := by ring
      _ ≤ x ^ 5 * D₂ := mul_le_mul_of_nonneg_left hxd2 (pow_nonneg hx.le 5)
      _ ≤ M * N * (b : ℝ) ^ 12 := hcancel
  have hDpow : D₁ ^ 7 ≤ M ^ 2 * N ^ 2 * (b : ℝ) ^ 24 := by
    have hsquare := pow_le_pow_left₀ (by positivity) hxD 2
    rw [← hx2]
    calc
      (x ^ 2) ^ 7 = (x ^ 7) ^ 2 := by ring
      _ ≤ (M * N * (b : ℝ) ^ 12) ^ 2 := hsquare
      _ = M ^ 2 * N ^ 2 * (b : ℝ) ^ 24 := by ring
  have hqD : q ≤ 40000 * N * D₁ := by
    have hupper := degreeBinRel_edge_card_le_card_mul_upper A b hb hdegree i j
    have hcardLN : (Fintype.card L₀ : ℝ) ≤ N := by
      dsimp [N]
      exact_mod_cast Fintype.card_le_of_injective (fun l : L₀ ↦ l.1)
        (fun _ _ h ↦ Subtype.ext h)
    calc
      q ≤ 40000 * e := hlargeR
      _ ≤ 40000 * ((Fintype.card L₀ : ℝ) * D₁) := by
        gcongr
        dsimp [e, B₀, L₀, D₁, A]
        exact_mod_cast hupper
      _ ≤ 40000 * (N * D₁) := by gcongr
      _ = 40000 * N * D₁ := by ring
  have hqpow := pow_le_pow_left₀ (by positivity : 0 ≤ q) hqD 7
  calc
    q ^ 7 ≤ (40000 * N * D₁) ^ 7 := hqpow
    _ = 40000 ^ 7 * N ^ 7 * D₁ ^ 7 := by ring
    _ ≤ 40000 ^ 7 * N ^ 7 * (M ^ 2 * N ^ 2 * (b : ℝ) ^ 24) := by
      gcongr
    _ = auxiliarySeventhPowerConstant * N ^ 9 * (b : ℝ) ^ 24 := by
      dsimp [auxiliarySeventhPowerConstant, M]
      ring

lemma degreeBinRel_swap_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (i j : Fin 200) :
    (relEdgeFinset (degreeBinRel G b hdegree i j)).card =
      (relEdgeFinset (degreeBinRel G b hdegree j i)).card := by
  classical
  apply Finset.card_bij (fun e _ ↦ (e.2, e.1))
  · intro e he
    rw [mem_relEdgeFinset]
    exact ((mem_relEdgeFinset (degreeBinRel G b hdegree i j) e.1 e.2).mp he).symm
  · intro e₁ h₁ e₂ h₂ h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · intro e he
    refine ⟨(e.2, e.1), ?_, rfl⟩
    rw [mem_relEdgeFinset]
    exact ((mem_relEdgeFinset (degreeBinRel G b hdegree j i) e.1 e.2).mp he).symm

lemma pairAuxGraph_seventh_power_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : ℕ) (hb : 1 < b)
    (hdegree : ∀ p : OrderedPair V, (pairAuxGraph G).degree p < b ^ 200)
    (hfree : counterexampleGraph.Free G) :
    ((directedEdgeFinset (pairAuxGraph G)).card : ℝ) ^ 7 ≤
      auxiliarySeventhPowerConstant *
        (Fintype.card (OrderedPair V) : ℝ) ^ 9 * (b : ℝ) ^ 24 := by
  obtain ⟨⟨i, j⟩, hlarge⟩ :=
    exists_large_degreeEdgeFiber (pairAuxGraph G) b hdegree
  have hlarge' : (directedEdgeFinset (pairAuxGraph G)).card ≤
      40000 * (relEdgeFinset
        (degreeBinRel (pairAuxGraph G) b hdegree i j)).card := by
    simpa [degreeEdgeFiber_card_eq_rel] using hlarge
  by_cases hord : b ^ (i.1 + 1) ≤ b ^ (j.1 + 1)
  · exact degreeFiber_seventh_power_bound_of_order G b hb hdegree i j
      hlarge' hord hfree
  · have hord' : b ^ (j.1 + 1) ≤ b ^ (i.1 + 1) := le_of_lt (lt_of_not_ge hord)
    have hlarge'' : (directedEdgeFinset (pairAuxGraph G)).card ≤
        40000 * (relEdgeFinset
          (degreeBinRel (pairAuxGraph G) b hdegree j i)).card := by
      rw [← degreeBinRel_swap_card (pairAuxGraph G) b hdegree i j]
      exact hlarge'
    exact degreeFiber_seventh_power_bound_of_order G b hb hdegree j i
      hlarge'' hord' hfree

def orderedRectangleFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset ((V × V) × (V × V)) :=
  Finset.univ.filter fun z ↦
    z.1.1 ≠ z.1.2 ∧ z.2.1 ≠ z.2.2 ∧
      G.Adj z.1.1 z.2.1 ∧ G.Adj z.1.2 z.2.1 ∧
      G.Adj z.1.1 z.2.2 ∧ G.Adj z.1.2 z.2.2

@[simp] lemma mem_orderedRectangleFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : (V × V) × (V × V)) :
    z ∈ orderedRectangleFinset G ↔
      z.1.1 ≠ z.1.2 ∧ z.2.1 ≠ z.2.2 ∧
        G.Adj z.1.1 z.2.1 ∧ G.Adj z.1.2 z.2.1 ∧
        G.Adj z.1.1 z.2.2 ∧ G.Adj z.1.2 z.2.2 := by
  simp [orderedRectangleFinset]

lemma colored_rectangleCount_eq_orderedRectangleFinset_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Erdos888.ColoredGraph.rectangleCount (fun x y ↦ G.Adj x y) =
      (orderedRectangleFinset G).card := by
  classical
  rw [Erdos888.ColoredGraph.rectangleCount_eq_sum_indicator]
  have hind (x x' y y' : V) :
      Erdos888.ColoredGraph.rectangleIndicator (fun a b ↦ G.Adj a b) x x' y y' =
        if x ≠ x' ∧ y ≠ y' ∧ G.Adj x y ∧ G.Adj x' y ∧
          G.Adj x y' ∧ G.Adj x' y' then 1 else 0 := by
    by_cases h : x ≠ x' ∧ y ≠ y' ∧ G.Adj x y ∧ G.Adj x' y ∧
        G.Adj x y' ∧ G.Adj x' y'
    · simp [Erdos888.ColoredGraph.rectangleIndicator,
        Erdos888.ColoredGraph.ContainsRectangle, h]
    · simp [Erdos888.ColoredGraph.rectangleIndicator,
        Erdos888.ColoredGraph.ContainsRectangle, h]
  simp_rw [hind]
  have hprod :
      (∑ x : V, ∑ x' : V, ∑ y : V, ∑ y' : V,
        if x ≠ x' ∧ y ≠ y' ∧ G.Adj x y ∧ G.Adj x' y ∧
          G.Adj x y' ∧ G.Adj x' y' then (1 : ℝ) else 0) =
      ∑ z : (V × V) × (V × V),
        if z.1.1 ≠ z.1.2 ∧ z.2.1 ≠ z.2.2 ∧
          G.Adj z.1.1 z.2.1 ∧ G.Adj z.1.2 z.2.1 ∧
          G.Adj z.1.1 z.2.2 ∧ G.Adj z.1.2 z.2.2 then (1 : ℝ) else 0 := by
    calc
      (∑ x : V, ∑ x' : V, ∑ y : V, ∑ y' : V,
          if x ≠ x' ∧ y ≠ y' ∧ G.Adj x y ∧ G.Adj x' y ∧
            G.Adj x y' ∧ G.Adj x' y' then (1 : ℝ) else 0) =
          ∑ p : V × V, ∑ y : V, ∑ y' : V,
            if p.1 ≠ p.2 ∧ y ≠ y' ∧ G.Adj p.1 y ∧ G.Adj p.2 y ∧
              G.Adj p.1 y' ∧ G.Adj p.2 y' then (1 : ℝ) else 0 :=
        (Fintype.sum_prod_type (fun p : V × V ↦
          ∑ y : V, ∑ y' : V,
            if p.1 ≠ p.2 ∧ y ≠ y' ∧ G.Adj p.1 y ∧ G.Adj p.2 y ∧
              G.Adj p.1 y' ∧ G.Adj p.2 y' then (1 : ℝ) else 0)).symm
      _ = ∑ p : V × V, ∑ q : V × V,
            if p.1 ≠ p.2 ∧ q.1 ≠ q.2 ∧ G.Adj p.1 q.1 ∧ G.Adj p.2 q.1 ∧
              G.Adj p.1 q.2 ∧ G.Adj p.2 q.2 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        exact (Fintype.sum_prod_type (fun q : V × V ↦
          if p.1 ≠ p.2 ∧ q.1 ≠ q.2 ∧ G.Adj p.1 q.1 ∧ G.Adj p.2 q.1 ∧
            G.Adj p.1 q.2 ∧ G.Adj p.2 q.2 then (1 : ℝ) else 0)).symm
      _ = _ :=
        (Fintype.sum_prod_type (fun z : (V × V) × (V × V) ↦
          if z.1.1 ≠ z.1.2 ∧ z.2.1 ≠ z.2.2 ∧
            G.Adj z.1.1 z.2.1 ∧ G.Adj z.1.2 z.2.1 ∧
            G.Adj z.1.1 z.2.2 ∧ G.Adj z.1.2 z.2.2 then (1 : ℝ) else 0)).symm
  rw [hprod]
  rw [orderedRectangleFinset]
  exact Finset.sum_boole (R := ℝ) (fun z : (V × V) × (V × V) ↦
    z.1.1 ≠ z.1.2 ∧ z.2.1 ≠ z.2.2 ∧
      G.Adj z.1.1 z.2.1 ∧ G.Adj z.1.2 z.2.1 ∧
      G.Adj z.1.1 z.2.2 ∧ G.Adj z.1.2 z.2.2) Finset.univ

lemma orderedRectangleFinset_card_eq_pairAux_directedEdge_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (orderedRectangleFinset G).card =
      (directedEdgeFinset (pairAuxGraph G)).card := by
  classical
  apply Finset.card_bij (fun z hz ↦
    (⟨z.1, ((mem_orderedRectangleFinset G z).mp hz).1⟩,
      ⟨z.2, ((mem_orderedRectangleFinset G z).mp hz).2.1⟩))
  · intro z hz
    rw [mem_directedEdgeFinset]
    have h := ((mem_orderedRectangleFinset G z).mp hz).2.2
    exact ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩
  · intro z₁ h₁ z₂ h₂ h
    exact Prod.ext (congrArg (fun e ↦ e.1.1) h) (congrArg (fun e ↦ e.2.1) h)
  · intro e he
    refine ⟨(e.1.1, e.2.1), ?_, rfl⟩
    have hadj := (mem_directedEdgeFinset (pairAuxGraph G) e.1 e.2).mp he
    exact (mem_orderedRectangleFinset G _).mpr
      ⟨e.1.2, e.2.2, hadj.1, hadj.2.2.1, hadj.2.1, hadj.2.2.2⟩

lemma colored_rectangleCount_eq_pairAux_directedEdge_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Erdos888.ColoredGraph.rectangleCount (fun x y ↦ G.Adj x y) =
      (directedEdgeFinset (pairAuxGraph G)).card := by
  rw [colored_rectangleCount_eq_orderedRectangleFinset_card,
    orderedRectangleFinset_card_eq_pairAux_directedEdge_card]

lemma colored_edgeCount_eq_twice_card_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Erdos888.ColoredGraph.edgeCount (fun x y ↦ G.Adj x y) =
      2 * (G.edgeFinset.card : ℝ) := by
  rw [Erdos888.ColoredGraph.edgeCount_eq_card_edgeFinset]
  simp only [Erdos888.ColoredGraph.edgeFinset]
  norm_cast
  exact G.two_mul_card_edgeFinset.symm

/-- The 200-bin scale used for an `n`-vertex host. -/
noncomputable def degreeBase (n : ℕ) : ℕ :=
  Nat.ceil ((n : ℝ) ^ (1 / 100 : ℝ)) + 2

lemma degreeBase_gt_one (n : ℕ) : 1 < degreeBase n := by
  dsimp [degreeBase]
  omega

lemma card_orderedPair_fin_le_sq (n : ℕ) :
    Fintype.card (OrderedPair (Fin n)) ≤ n ^ 2 := by
  calc
    Fintype.card (OrderedPair (Fin n)) ≤ Fintype.card (Fin n × Fin n) :=
      Fintype.card_le_of_injective (fun p : OrderedPair (Fin n) ↦ p.1)
        (fun _ _ h ↦ Subtype.ext h)
    _ = n ^ 2 := by simp [pow_two]

lemma degreeBase_pow_two_hundred_ge_sq (n : ℕ) :
    n ^ 2 ≤ degreeBase n ^ 200 := by
  let x : ℝ := (n : ℝ) ^ (1 / 100 : ℝ)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hceil : x ≤ (degreeBase n : ℝ) := by
    change x ≤ ((Nat.ceil x + 2 : ℕ) : ℝ)
    calc
      x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
      _ ≤ ((Nat.ceil x + 2 : ℕ) : ℝ) := by
        norm_cast
        omega
  have hpow := pow_le_pow_left₀ hx0 hceil 200
  have hxpow : x ^ 200 = (n : ℝ) ^ 2 := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  rw [hxpow] at hpow
  exact_mod_cast hpow

lemma pairAuxGraph_degree_lt_degreeBase_pow
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : OrderedPair (Fin n)) :
    (pairAuxGraph G).degree p < degreeBase n ^ 200 := by
  exact lt_of_lt_of_le ((pairAuxGraph G).degree_lt_card_verts p)
    ((card_orderedPair_fin_le_sq n).trans (degreeBase_pow_two_hundred_ge_sq n))

lemma degreeBase_cast_le_four_rpow :
    ∀ᶠ n : ℕ in atTop,
      (degreeBase n : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 100 : ℝ) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  let x : ℝ := (n : ℝ) ^ (1 / 100 : ℝ)
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx1 : 1 ≤ x := by
    dsimp [x]
    simpa using Real.one_le_rpow hnreal (by norm_num : (0 : ℝ) ≤ 1 / 100)
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx1
  have hceil := Nat.ceil_lt_add_one hx0
  dsimp [degreeBase]
  push_cast
  dsimp [x] at hceil ⊢
  linarith

noncomputable def fourthRootMajorantConstant : ℝ :=
  auxiliarySeventhPowerConstant + 1

lemma fourthRoot_pairAux_le
    (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : counterexampleGraph.Free G) :
    Real.sqrt (Real.sqrt
      ((directedEdgeFinset (pairAuxGraph G)).card : ℝ)) ≤
      fourthRootMajorantConstant * (n : ℝ) ^ (9 / 14 : ℝ) * degreeBase n := by
  let q : ℝ := (directedEdgeFinset (pairAuxGraph G)).card
  let N : ℝ := Fintype.card (OrderedPair (Fin n))
  let b : ℝ := degreeBase n
  let c : ℝ := fourthRootMajorantConstant
  let z : ℝ := c * (n : ℝ) ^ (9 / 14 : ℝ) * b
  have hA0 : 0 ≤ auxiliarySeventhPowerConstant := by
    dsimp [auxiliarySeventhPowerConstant]
    positivity
  have hc1 : 1 ≤ c := by dsimp [c, fourthRootMajorantConstant]; linarith
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc1
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hb1 : 1 ≤ b := by
    dsimp [b]
    exact_mod_cast (le_of_lt (degreeBase_gt_one n))
  have hN : N ≤ (n : ℝ) ^ 2 := by
    dsimp [N]
    exact_mod_cast card_orderedPair_fin_le_sq n
  have hq7 : q ^ 7 ≤ auxiliarySeventhPowerConstant * N ^ 9 * b ^ 24 := by
    dsimp [q, N, b]
    exact pairAuxGraph_seventh_power_bound G (degreeBase n)
      (degreeBase_gt_one n) (pairAuxGraph_degree_lt_degreeBase_pow n G) hfree
  have hnPower : ((n : ℝ) ^ (9 / 14 : ℝ)) ^ 28 = (n : ℝ) ^ 18 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    norm_num
  have hqz : q ^ 7 ≤ z ^ 28 := by
    have hNpow : N ^ 9 ≤ (n : ℝ) ^ 18 := by
      calc
        N ^ 9 ≤ ((n : ℝ) ^ 2) ^ 9 := pow_le_pow_left₀ (by positivity) hN 9
        _ = (n : ℝ) ^ 18 := by ring
    have hbpow : b ^ 24 ≤ b ^ 28 := pow_le_pow_right₀ hb1 (by omega)
    have hc : auxiliarySeventhPowerConstant ≤ c ^ 28 :=
      (show auxiliarySeventhPowerConstant ≤ c by
        dsimp [c, fourthRootMajorantConstant]
        linarith).trans (le_self_pow₀ hc1 (by norm_num))
    calc
      q ^ 7 ≤ auxiliarySeventhPowerConstant * N ^ 9 * b ^ 24 := hq7
      _ ≤ c ^ 28 * ((n : ℝ) ^ 18) * b ^ 28 := by gcongr
      _ = c ^ 28 * (((n : ℝ) ^ (9 / 14 : ℝ)) ^ 28) * b ^ 28 := by
        rw [hnPower]
      _ = z ^ 28 := by
        dsimp [z]
        ring
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hz0 : 0 ≤ z := by dsimp [z, b]; positivity
  have hqz4 : q ≤ z ^ 4 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (7 : ℕ) ≠ 0) (pow_nonneg hz0 4)
    calc
      q ^ 7 ≤ z ^ 28 := hqz
      _ = (z ^ 4) ^ 7 := by ring
  have hsqrt0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hfourth0 : 0 ≤ Real.sqrt (Real.sqrt q) := Real.sqrt_nonneg _
  have hfourthPow : (Real.sqrt (Real.sqrt q)) ^ 4 = q := by
    have h₁ := Real.sq_sqrt hq0
    have h₂ := Real.sq_sqrt hsqrt0
    nlinarith [sq_nonneg (Real.sqrt (Real.sqrt q))]
  have hroot : Real.sqrt (Real.sqrt q) ≤ z := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hz0
    rw [hfourthPow]
    exact hqz4
  simpa [q, z, c, b] using hroot

lemma host_edge_card_le_degreeBase_bound
    (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : counterexampleGraph.Free G) :
    (G.edgeFinset.card : ℝ) ≤
      (n : ℝ) + (n : ℝ) * Real.sqrt n +
        (n : ℝ) * (fourthRootMajorantConstant *
          (n : ℝ) ^ (9 / 14 : ℝ) * degreeBase n) := by
  have hkst := Erdos888.ColoredGraph.edgeCount_le
    (fun x : Fin n ↦ fun y : Fin n ↦ G.Adj x y)
  rw [colored_edgeCount_eq_twice_card_edges G,
    colored_rectangleCount_eq_pairAux_directedEdge_card G] at hkst
  simp only [Fintype.card_fin] at hkst
  have hnn : (0 : ℝ) ≤ n := by positivity
  have hsqrtmul : Real.sqrt ((n : ℝ) * n) = n := by
    rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_nonneg hnn]
  rw [hsqrtmul] at hkst
  have hroot := fourthRoot_pairAux_le n hn G hfree
  have hterm := mul_le_mul_of_nonneg_left hroot
    (show (0 : ℝ) ≤ 2 * n by positivity)
  nlinarith

/-- The rational exponent used after absorbing the bin-scale factor. -/
noncomputable def witnessUpperExponent : ℝ := 139 / 84

noncomputable def extremalUpperConstant : ℝ :=
  2 + 4 * fourthRootMajorantConstant

lemma host_edge_card_le_power
    (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : counterexampleGraph.Free G)
    (hbase : (degreeBase n : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 100 : ℝ)) :
    (G.edgeFinset.card : ℝ) ≤
      extremalUpperConstant * polynomialGrowth witnessUpperExponent n := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnreal
  have hn0 : (0 : ℝ) ≤ n := hnpos.le
  have hc0 : 0 ≤ fourthRootMajorantConstant := by
    dsimp [fourthRootMajorantConstant, auxiliarySeventhPowerConstant]
    positivity
  have hpow1 : (n : ℝ) ≤ (n : ℝ) ^ witnessUpperExponent := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hnreal
        (show (1 : ℝ) ≤ witnessUpperExponent by
          norm_num [witnessUpperExponent])
  have hsqrtpow : (n : ℝ) * Real.sqrt n = (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
      Real.rpow_add hnpos, Real.rpow_one]
  have hpowThreeHalves :
      (n : ℝ) * Real.sqrt n ≤ (n : ℝ) ^ witnessUpperExponent := by
    rw [hsqrtpow]
    exact Real.rpow_le_rpow_of_exponent_le hnreal (by
      norm_num [witnessUpperExponent])
  have hbaseMul :
      (n : ℝ) * (fourthRootMajorantConstant * (n : ℝ) ^ (9 / 14 : ℝ) *
        degreeBase n) ≤
      (n : ℝ) * (fourthRootMajorantConstant * (n : ℝ) ^ (9 / 14 : ℝ) *
        (4 * (n : ℝ) ^ (1 / 100 : ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ hn0
    exact mul_le_mul_of_nonneg_left hbase
      (mul_nonneg hc0 (Real.rpow_nonneg hn0 _))
  have hpowerIdentity :
      (n : ℝ) * (fourthRootMajorantConstant * (n : ℝ) ^ (9 / 14 : ℝ) *
        (4 * (n : ℝ) ^ (1 / 100 : ℝ))) =
      4 * fourthRootMajorantConstant *
        (n : ℝ) ^ (1 + 9 / 14 + 1 / 100 : ℝ) := by
    rw [Real.rpow_add hnpos (1 + 9 / 14) (1 / 100),
      Real.rpow_add hnpos 1 (9 / 14), Real.rpow_one]
    ring
  have hsmallExponent :
      (n : ℝ) ^ (1 + 9 / 14 + 1 / 100 : ℝ) ≤
        (n : ℝ) ^ witnessUpperExponent :=
    Real.rpow_le_rpow_of_exponent_le hnreal (by
      norm_num [witnessUpperExponent])
  have hthird :
      (n : ℝ) * (fourthRootMajorantConstant * (n : ℝ) ^ (9 / 14 : ℝ) *
        degreeBase n) ≤
      4 * fourthRootMajorantConstant * (n : ℝ) ^ witnessUpperExponent := by
    calc
      (n : ℝ) * (fourthRootMajorantConstant * (n : ℝ) ^ (9 / 14 : ℝ) *
          degreeBase n) ≤
          (n : ℝ) * (fourthRootMajorantConstant * (n : ℝ) ^ (9 / 14 : ℝ) *
            (4 * (n : ℝ) ^ (1 / 100 : ℝ))) := hbaseMul
      _ = 4 * fourthRootMajorantConstant *
          (n : ℝ) ^ (1 + 9 / 14 + 1 / 100 : ℝ) := hpowerIdentity
      _ ≤ 4 * fourthRootMajorantConstant *
          (n : ℝ) ^ witnessUpperExponent :=
        mul_le_mul_of_nonneg_left hsmallExponent (by positivity)
  calc
    (G.edgeFinset.card : ℝ) ≤
        (n : ℝ) + (n : ℝ) * Real.sqrt n +
          (n : ℝ) * (fourthRootMajorantConstant *
            (n : ℝ) ^ (9 / 14 : ℝ) * degreeBase n) :=
      host_edge_card_le_degreeBase_bound n hn G hfree
    _ ≤ (n : ℝ) ^ witnessUpperExponent +
          (n : ℝ) ^ witnessUpperExponent +
          4 * fourthRootMajorantConstant * (n : ℝ) ^ witnessUpperExponent :=
      add_le_add (add_le_add hpow1 hpowThreeHalves) hthird
    _ = extremalUpperConstant * polynomialGrowth witnessUpperExponent n := by
      dsimp [extremalUpperConstant, polynomialGrowth]
      ring

lemma counterexampleGraph_eventually_extremal_bound :
    ∀ᶠ n : ℕ in atTop,
      extremalGrowth counterexampleGraph n ≤
        extremalUpperConstant * polynomialGrowth witnessUpperExponent n := by
  filter_upwards [degreeBase_cast_le_four_rpow, eventually_ge_atTop 1] with n hbase hn
  have hconstant :
      0 ≤ extremalUpperConstant * polynomialGrowth witnessUpperExponent n := by
    dsimp [extremalUpperConstant, fourthRootMajorantConstant,
      auxiliarySeventhPowerConstant, polynomialGrowth]
    positivity
  have hext :
      (SimpleGraph.extremalNumber (Fintype.card (Fin n)) counterexampleGraph : ℝ) ≤
        extremalUpperConstant * polynomialGrowth witnessUpperExponent n := by
    apply (SimpleGraph.extremalNumber_le_iff_of_nonneg
      (V := Fin n) counterexampleGraph hconstant).2
    intro G _ hfree
    exact host_edge_card_le_power n hn G hfree hbase
  simpa [extremalGrowth] using hext

/-- The fully proved finite estimate, packaged in the asymptotic notation used
by the Erdős--Simonovits conjecture. -/
theorem counterexampleGraph_extremal_upper :
    extremalGrowth counterexampleGraph =O[atTop]
      polynomialGrowth witnessUpperExponent := by
  refine IsBigO.of_bound extremalUpperConstant ?_
  filter_upwards [counterexampleGraph_eventually_extremal_bound] with n hn
  have hf : 0 ≤ extremalGrowth counterexampleGraph n := by
    dsimp [extremalGrowth]
    positivity
  have hg : 0 ≤ polynomialGrowth witnessUpperExponent n := by
    dsimp [polynomialGrowth]
    positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg hg] using hn

lemma polynomialGrowth_isLittleO {a b : ℝ} (hab : a < b) :
    polynomialGrowth a =o[atTop] polynomialGrowth b := by
  refine isLittleO_of_tendsto' ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    intro hz
    have hp : 0 < polynomialGrowth b n := by
      dsimp [polynomialGrowth]
      exact Real.rpow_pos_of_pos (by exact_mod_cast hn) b
    exact (hp.ne' hz).elim
  · have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (a - b)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp
        tendsto_natCast_atTop_atTop
      rw [show a - b = -(b - a) by ring]
      exact h
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [polynomialGrowth]
    rw [← Real.rpow_sub (by exact_mod_cast hn : (0 : ℝ) < n)]

lemma not_polynomialGrowth_isBigO_of_lt {a b : ℝ} (hab : a < b) :
    ¬polynomialGrowth b =O[atTop] polynomialGrowth a := by
  have hnonzero : ∀ᶠ n : ℕ in atTop, polynomialGrowth a n ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (Real.rpow_pos_of_pos (by exact_mod_cast hn : (0 : ℝ) < n) a).ne'
  exact (polynomialGrowth_isLittleO hab).not_isBigO
    (Filter.Eventually.frequently hnonzero)

/-- Erdős Problem 147 has a negative answer.  The witness is the bipartite,
4-regular graph `C₁₂[2]`, whose extremal exponent is at most `139/84 < 5/3`. -/
theorem erdos_147 :
    ¬ (∀ (W : Type) [Fintype W] [Nonempty W]
      (H : SimpleGraph W) [DecidableRel H.Adj] (r : ℕ),
        H.IsBipartite → H.minDegree = r → HasConjecturedLowerBound H r) := by
  intro hconjecture
  obtain ⟨ε, hε, hlower⟩ := hconjecture (Fin 12 × Fin 2)
    counterexampleGraph 4 counterexampleGraph_isBipartite
    counterexampleGraph_minDegree
  have hlt : witnessUpperExponent <
      2 - 1 / ((4 : ℝ) - 1) + ε := by
    dsimp [witnessUpperExponent]
    norm_num at hε ⊢
    linarith
  exact (not_polynomialGrowth_isBigO_of_lt hlt)
    (hlower.trans counterexampleGraph_extremal_upper)

end

#print axioms erdos_147
-- 'Erdos147.erdos_147' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos147
