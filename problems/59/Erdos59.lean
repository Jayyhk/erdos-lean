import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos59

/-
# Problem Description

Erdős Problem 59. Is it true that the number of graphs on `n` vertices containing no copy of
`G` is at most `2 ^ ((1 + o(1)) · ex(n; G))`? `erdos_59` proves that it is not.

For non-bipartite `G` the answer is yes, by Erdős, Frankl and Rödl. It fails for `G = C₆`:
Morris and Saxton showed there are at least `2 ^ ((1 + c) · ex(n; C₆))` such graphs for
infinitely many `n`, for some `c > 0`. The witness here is explicit, `c = 1/100`.

The conclusion bundles both halves. `HasErdos59UpperBound H` is
`∀ ε > 0, ∃ N, ∀ n ≥ N, labelledFreeGraphCount H n ≤ 2 ^ ((1 + ε) * ex(n, H))`, which is the
`(1 + o(1))` of the question; `HasMorrisSaxtonLowerBound H` is `∃ c > 0` such that
`{n | 2 ^ ((1 + c) * ex(n, H)) ≤ labelledFreeGraphCount H n}` is infinite. Counts are of
labelled graphs.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/Core.lean` -/

section
/-!
# Erdős Problem 59: counting labelled forbidden-subgraph-free graphs

This file packages the finite counting statement and the two asymptotic
properties used in Erdős Problem 59.  All graphs counted here are labelled:
their vertex type is literally `Fin n`.
-/

open SimpleGraph

/-- The finite type of labelled `H`-free graphs on the vertex set `Fin n`. -/
abbrev LabelledFreeGraphs {W : Type*} (H : SimpleGraph W) (n : ℕ) :=
  {G : SimpleGraph (Fin n) // H.Free G}

/-- The exact number of labelled `H`-free graphs on `Fin n`. -/
noncomputable def labelledFreeGraphCount {W : Type*} (H : SimpleGraph W) (n : ℕ) : ℕ :=
  Nat.card (LabelledFreeGraphs H n)

@[simp]
theorem labelledFreeGraphCount_eq_card {W : Type*} (H : SimpleGraph W) (n : ℕ) :
    labelledFreeGraphCount H n = Nat.card (LabelledFreeGraphs H n) := by
  rfl

/-- The Erdős--Frankl--Rödl type upper bound asked for in Problem 59. -/
def HasErdos59UpperBound {W : Type*} (H : SimpleGraph W) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (labelledFreeGraphCount H n : ℝ) ≤
      Real.rpow 2 ((1 + ε) * (SimpleGraph.extremalNumber n H : ℝ))

/-- The indices at which a fixed multiplicative improvement over the
`2 ^ extremalNumber` exponent holds. -/
def lowerBoundIndices {W : Type*} (H : SimpleGraph W) (c : ℝ) : Set ℕ :=
  {n | Real.rpow 2 ((1 + c) * (SimpleGraph.extremalNumber n H : ℝ)) ≤
    (labelledFreeGraphCount H n : ℝ)}

/-- A Morris--Saxton type counterexample lower bound: one fixed positive
constant improves the exponent for infinitely many orders. -/
def HasMorrisSaxtonLowerBound {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ c : ℝ, 0 < c ∧ (lowerBoundIndices H c).Infinite

/-- The mild nondegeneracy condition needed to separate the exponents in the
upper and lower bounds. -/
def EventuallyPositiveExtremalNumber {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < SimpleGraph.extremalNumber n H

/-- A six-cycle written as six distinct, cyclically adjacent indexed
vertices.  This is the convenient pointwise form of containment of
`cycleGraph 6`. -/
def IsC6 {V : Type*} (G : SimpleGraph V) (v : Fin 6 → V) : Prop :=
  Function.Injective v ∧ ∀ i, G.Adj (v i) (v (i + 1))

private theorem cycleGraph_six_adj_succ (i : Fin 6) :
    (SimpleGraph.cycleGraph 6).Adj i (i + 1) := by
  fin_cases i <;> decide

private theorem cycleGraph_six_adj_iff (i j : Fin 6) :
    (SimpleGraph.cycleGraph 6).Adj i j ↔ j = i + 1 ∨ i = j + 1 := by
  fin_cases i <;> fin_cases j <;> decide

/-- The indexed definition of a six-cycle is exactly containment of the
standard six-cycle graph. -/
theorem exists_isC6_iff_cycleGraph_six_isContained {V : Type*}
    (G : SimpleGraph V) :
    (∃ v : Fin 6 → V, IsC6 G v) ↔ SimpleGraph.cycleGraph 6 ⊑ G := by
  constructor
  · rintro ⟨v, hv_injective, hv_adj⟩
    refine ⟨{
      toHom := {
        toFun := v
        map_rel' := ?_ }
      injective' := hv_injective }⟩
    intro i j hij
    rcases (cycleGraph_six_adj_iff i j).mp hij with h | h
    · subst j
      exact hv_adj i
    · subst i
      exact (hv_adj j).symm
  · rintro ⟨f⟩
    refine ⟨f, f.injective, fun i ↦ ?_⟩
    exact f.toHom.map_rel (cycleGraph_six_adj_succ i)

/-- Pointwise six-cycle-freeness is exactly Mathlib's `Free` predicate for
the standard six-cycle graph. -/
theorem cycleGraph_six_free_iff_forall_not_isC6 {V : Type*}
    (G : SimpleGraph V) :
    (SimpleGraph.cycleGraph 6).Free G ↔ ∀ v : Fin 6 → V, ¬ IsC6 G v := by
  rw [SimpleGraph.Free, ← not_exists]
  exact not_congr (exists_isC6_iff_cycleGraph_six_isContained G).symm

private theorem cycleGraph_six_card_edgeFinset :
    (SimpleGraph.cycleGraph 6).edgeFinset.card = 6 := by
  have h := (SimpleGraph.cycleGraph 6).sum_degrees_eq_twice_card_edges
  simp [SimpleGraph.cycleGraph_degree_three_le] at h
  omega

private theorem cycleGraph_six_free_edge {V : Type*} [Fintype V]
    {u v : V} (huv : u ≠ v) :
    (SimpleGraph.cycleGraph 6).Free (SimpleGraph.edge u v) := by
  classical
  rintro ⟨f⟩
  have hcard := Fintype.card_le_of_embedding f.mapEdgeSet
  rw [SimpleGraph.card_edgeSet, SimpleGraph.card_edgeSet,
    cycleGraph_six_card_edgeFinset] at hcard
  have hedge : (SimpleGraph.edge u v).edgeFinset.card = 1 := by
    simp [SimpleGraph.edgeFinset, SimpleGraph.edgeSet_edge_of_ne huv]
  rw [hedge] at hcard
  omega

/-- The extremal number for `C₆` is positive from order two onward: a single
edge is already `C₆`-free. -/
theorem eventuallyPositiveExtremalNumber_cycleGraph_six :
    EventuallyPositiveExtremalNumber (SimpleGraph.cycleGraph 6) := by
  refine ⟨2, fun n hn ↦ ?_⟩
  let u : Fin n := ⟨0, by omega⟩
  let v : Fin n := ⟨1, by omega⟩
  have huv : u ≠ v := by
    intro h
    have hval := congrArg Fin.val h
    simp [u, v] at hval
  have hpositive :
      0 < SimpleGraph.extremalNumber (Fintype.card (Fin n))
        (SimpleGraph.cycleGraph 6) := by
    rw [SimpleGraph.lt_extremalNumber_iff]
    refine ⟨SimpleGraph.edge u v, inferInstance,
      cycleGraph_six_free_edge huv, ?_⟩
    simp [SimpleGraph.edgeFinset, SimpleGraph.edgeSet_edge_of_ne huv]
  simpa using hpositive

/-- A fixed positive improvement in the exponent on infinitely many indices
contradicts the Problem 59 upper bound as soon as the extremal number is
eventually positive. -/
theorem fixed_c_frequently_lowerBound_contradicts_upperBound {W : Type*}
    {H : SimpleGraph W} {c : ℝ} (hc : 0 < c)
    (hlower : (lowerBoundIndices H c).Infinite)
    (hpositive : EventuallyPositiveExtremalNumber H) :
    ¬ HasErdos59UpperBound H := by
  intro hupper
  obtain ⟨Nupper, hNupper⟩ := hupper (c / 2) (by linarith)
  obtain ⟨Npositive, hNpositive⟩ := hpositive
  obtain ⟨n, hnmem, hn⟩ := hlower.exists_gt (max Nupper Npositive)
  change Real.rpow 2 ((1 + c) * (SimpleGraph.extremalNumber n H : ℝ)) ≤
    (labelledFreeGraphCount H n : ℝ) at hnmem
  have hnupper : Nupper ≤ n := (le_max_left _ _).trans hn.le
  have hnpositive : Npositive ≤ n := (le_max_right _ _).trans hn.le
  have hexpos : (0 : ℝ) < SimpleGraph.extremalNumber n H := by
    exact_mod_cast hNpositive n hnpositive
  have hexponent :
      (1 + c / 2) * (SimpleGraph.extremalNumber n H : ℝ) <
        (1 + c) * (SimpleGraph.extremalNumber n H : ℝ) := by
    nlinarith
  have hrpow := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hexponent
  exact (not_lt_of_ge hnmem) ((hNupper n hnupper).trans_lt hrpow)

/-- Packaged form of the logical incompatibility between the two asymptotic
properties. -/
theorem hasMorrisSaxtonLowerBound_not_hasErdos59UpperBound {W : Type*}
    {H : SimpleGraph W} (hlower : HasMorrisSaxtonLowerBound H)
    (hpositive : EventuallyPositiveExtremalNumber H) :
    ¬ HasErdos59UpperBound H := by
  obtain ⟨c, hc, hinf⟩ := hlower
  exact fixed_c_frequently_lowerBound_contradicts_upperBound hc hinf hpositive

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/AffinePolarity.lean` -/

section
/-!
# The affine polarity construction for Erdős Problem 59

This file gives the affine part of the generalized-quadrangle construction used
in the lower bound for the number of hexagon-free graphs.  For
`F = 𝔽_(2^(2*a+1))`, points and lines are copies of `F³`, with

`(x,y,z) I [u,v,w]  ↔  v-y=u*x ∧ w-z=v*x`.

The exceptional polarity exists because the exponent `θ = 2^a` satisfies
`2*θ^2 = |F|`.  Everything below is proved from these coordinates.
-/

open Finset Function

namespace AffinePolarity

noncomputable section

/-- The field of order `2^(2*a+1)`. -/
abbrev F (a : ℕ) := GaloisField 2 (2 * a + 1)

/-- Affine coordinates, used both for points and for lines. -/
@[ext]
structure Coord (K : Type*) where
  x : K
  y : K
  z : K
deriving DecidableEq

private def coordEquivProd (K : Type*) : Coord K ≃ (K × K × K) where
  toFun p := (p.x, p.y, p.z)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv p := by ext <;> rfl
  right_inv p := by rcases p with ⟨x, y, z⟩; rfl

instance fintypeF (a : ℕ) : Fintype (F a) := Fintype.ofFinite _

instance coordFintype (K : Type*) [Fintype K] : Fintype (Coord K) :=
  Fintype.ofEquiv (K × K × K) (coordEquivProd K).symm

abbrev Point (a : ℕ) := Coord (F a)
abbrev Line (a : ℕ) := Coord (F a)

/-- The Tits exponent `θ = 2^a`. -/
def theta (a : ℕ) : ℕ := 2 ^ a

lemma two_mul_theta_sq (a : ℕ) : 2 * theta a * theta a = 2 ^ (2 * a + 1) := by
  simp only [theta]
  calc
    2 * 2 ^ a * 2 ^ a = 2 ^ a * 2 ^ a * 2 := by ring
    _ = 2 ^ (a + a + 1) := by rw [pow_succ, pow_add]
    _ = 2 ^ (2 * a + 1) := by congr 2 <;> omega

lemma two_mul_theta (a : ℕ) : 2 * theta a = 2 ^ (a + 1) := by
  simp [theta, pow_succ, mul_comm]

lemma field_natCard (a : ℕ) : Nat.card (F a) = 2 ^ (2 * a + 1) := by
  simpa using GaloisField.card 2 (2 * a + 1) (by omega)

lemma field_card (a : ℕ) : Fintype.card (F a) = 2 ^ (2 * a + 1) := by
  rw [Fintype.card_eq_nat_card, field_natCard]

lemma coord_card (a : ℕ) : Fintype.card (Point a) = (2 ^ (2 * a + 1)) ^ 3 := by
  rw [Fintype.card_congr (coordEquivProd (F a))]
  simp only [Fintype.card_prod, field_card]
  ring

lemma pow_fieldCard (a : ℕ) (x : F a) : x ^ (2 ^ (2 * a + 1)) = x := by
  have h := FiniteField.pow_card x
  rwa [field_card] at h

lemma pow_two_theta_sq (a : ℕ) (x : F a) : x ^ (2 * theta a * theta a) = x := by
  rw [two_mul_theta_sq]
  exact pow_fieldCard a x

/-- Affine incidence. -/
def Incident {a : ℕ} (p : Point a) (l : Line a) : Prop :=
  l.y - p.y = l.x * p.x ∧ l.z - p.z = l.y * p.x

instance incidentDecidable (a : ℕ) : DecidableRel (@Incident a) :=
  fun _ _ => Classical.propDecidable _

/-- The unique line with prescribed first coordinate through a point. -/
def lineThrough {a : ℕ} (p : Point a) (u : F a) : Line a :=
  ⟨u, p.y + u * p.x, p.z + (p.y + u * p.x) * p.x⟩

@[simp] lemma lineThrough_x {a : ℕ} (p : Point a) (u : F a) :
    (lineThrough p u).x = u := rfl

lemma incident_lineThrough {a : ℕ} (p : Point a) (u : F a) :
    Incident p (lineThrough p u) := by
  constructor
  · simp only [Incident, lineThrough, CharTwo.sub_eq_add]
    calc
      p.y + u * p.x + p.y = (p.y + p.y) + u * p.x := by ring
      _ = u * p.x := by rw [CharTwo.add_self_eq_zero, zero_add]
  · simp only [Incident, lineThrough, CharTwo.sub_eq_add]
    calc
      p.z + (p.y + u * p.x) * p.x + p.z =
          (p.z + p.z) + (p.y + u * p.x) * p.x := by ring
      _ = (p.y + u * p.x) * p.x := by rw [CharTwo.add_self_eq_zero, zero_add]

lemma lineThrough_eq_of_incident {a : ℕ} {p : Point a} {l : Line a}
    (h : Incident p l) : lineThrough p l.x = l := by
  rcases h with ⟨hy, hz⟩
  ext
  · rfl
  · simp only [lineThrough]
    linear_combination -hy
  · simp only [lineThrough]
    rw [show p.y + l.x * p.x = l.y by
      linear_combination -hy]
    linear_combination -hz

/-- The lines through a point are parametrized by their first coordinate. -/
def incidentLineEquiv {a : ℕ} (p : Point a) :
    F a ≃ {l : Line a // Incident p l} where
  toFun u := ⟨lineThrough p u, incident_lineThrough p u⟩
  invFun l := l.1.x
  left_inv _ := rfl
  right_inv l := Subtype.ext (lineThrough_eq_of_incident l.2)

lemma card_incident_lines (a : ℕ) (p : Point a) :
    Fintype.card {l : Line a // Incident p l} = 2 ^ (2 * a + 1) := by
  exact (Fintype.card_congr (incidentLineEquiv p)).symm.trans (field_card a)

/-- Two points on the same line with the same first coordinate coincide. -/
lemma point_eq_of_same_x_of_incident {a : ℕ} {p q : Point a} {l : Line a}
    (hx : p.x = q.x) (hp : Incident p l) (hq : Incident q l) : p = q := by
  rcases hp with ⟨hpy, hpz⟩
  rcases hq with ⟨hqy, hqz⟩
  ext
  · exact hx
  · rw [hx] at hpy
    linear_combination hqy - hpy
  · rw [hx] at hpz
    linear_combination hqz - hpz

/-- Two distinct points have at most one common line. -/
lemma common_line_unique {a : ℕ} {p q : Point a} (hpq : p ≠ q)
    {l m : Line a} (hpl : Incident p l) (hql : Incident q l)
    (hpm : Incident p m) (hqm : Incident q m) : l = m := by
  have hpx : p.x ≠ q.x := by
    intro hx
    exact hpq (point_eq_of_same_x_of_incident hx hpl hql)
  rcases hpl with ⟨hply, hplz⟩
  rcases hql with ⟨hqly, hqlz⟩
  rcases hpm with ⟨hpmy, hpmz⟩
  rcases hqm with ⟨hqmy, hqmz⟩
  have hlmx : l.x = m.x := by
    have hprod : (l.x - m.x) * (p.x - q.x) = 0 := by
      linear_combination -hply + hqly + hpmy - hqmy
    rcases mul_eq_zero.mp hprod with h | h
    · exact sub_eq_zero.mp h
    · exact ((sub_ne_zero.mpr hpx) h).elim
  ext
  · exact hlmx
  · rw [hlmx] at hply
    linear_combination hply - hpmy
  · rw [show l.y = m.y by
      rw [hlmx] at hply
      linear_combination hply - hpmy] at hplz
    linear_combination hplz - hpmz

/-- For a fixed point, the first coordinate determines an incident line. -/
lemma line_eq_of_same_x_of_incident {a : ℕ} {p : Point a} {l m : Line a}
    (hx : l.x = m.x) (hl : Incident p l) (hm : Incident p m) : l = m := by
  calc
    l = lineThrough p l.x := (lineThrough_eq_of_incident hl).symm
    _ = lineThrough p m.x := by rw [hx]
    _ = m := lineThrough_eq_of_incident hm

/-- There is no incidence quadrilateral with two distinct points and lines. -/
theorem no_incidence_C4 {a : ℕ} :
    ¬ ∃ p q : Point a, ∃ l m : Line a,
      p ≠ q ∧ l ≠ m ∧ Incident p l ∧ Incident q l ∧ Incident p m ∧ Incident q m := by
  rintro ⟨p, q, l, m, hpq, hlm, hpl, hql, hpm, hqm⟩
  exact hlm (common_line_unique hpq hpl hql hpm hqm)

/-- Difference identities for two lines through the same affine point. -/
lemma line_differences_at_point {a : ℕ} {p : Point a} {l m : Line a}
    (hl : Incident p l) (hm : Incident p m) :
    l.y - m.y = (l.x - m.x) * p.x ∧
      l.z - m.z = (l.x - m.x) * p.x ^ 2 := by
  rcases hl with ⟨hly, hlz⟩
  rcases hm with ⟨hmy, hmz⟩
  constructor
  · linear_combination hly - hmy
  · linear_combination hlz - hmz + p.x * (hly - hmy)

/-- The three-by-three Vandermonde calculation used to exclude an incidence hexagon. -/
lemma vandermonde_three {a : ℕ} {x₀ x₁ x₂ s₀ s₁ s₂ : F a}
    (h01 : x₀ ≠ x₁) (h12 : x₁ ≠ x₂) (h20 : x₂ ≠ x₀)
    (h0 : s₀ + s₁ + s₂ = 0)
    (h1 : s₀ * x₀ + s₁ * x₁ + s₂ * x₂ = 0)
    (h2 : s₀ * x₀ ^ 2 + s₁ * x₁ ^ 2 + s₂ * x₂ ^ 2 = 0) :
    s₀ = 0 ∧ s₁ = 0 ∧ s₂ = 0 := by
  have hs₀ : s₀ * (x₀ - x₁) * (x₀ - x₂) = 0 := by
    linear_combination h2 - (x₁ + x₂) * h1 + (x₁ * x₂) * h0
  have hs₁ : s₁ * (x₁ - x₀) * (x₁ - x₂) = 0 := by
    linear_combination h2 - (x₀ + x₂) * h1 + (x₀ * x₂) * h0
  have hs₂ : s₂ * (x₂ - x₀) * (x₂ - x₁) = 0 := by
    linear_combination h2 - (x₀ + x₁) * h1 + (x₀ * x₁) * h0
  have hne₀ : (x₀ - x₁) * (x₀ - x₂) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr h01) (sub_ne_zero.mpr (Ne.symm h20))
  have hne₁ : (x₁ - x₀) * (x₁ - x₂) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr h01.symm) (sub_ne_zero.mpr h12)
  have hne₂ : (x₂ - x₀) * (x₂ - x₁) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr h20) (sub_ne_zero.mpr h12.symm)
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp (by simpa [mul_assoc] using hs₀)).resolve_right hne₀
  · exact (mul_eq_zero.mp (by simpa [mul_assoc] using hs₁)).resolve_right hne₁
  · exact (mul_eq_zero.mp (by simpa [mul_assoc] using hs₂)).resolve_right hne₂

/-- The affine incidence graph has no simple hexagon. -/
theorem no_incidence_C6 {a : ℕ} :
    ¬ ∃ p₀ p₁ p₂ : Point a, ∃ l₀ l₁ l₂ : Line a,
      p₀ ≠ p₁ ∧ p₁ ≠ p₂ ∧ p₂ ≠ p₀ ∧
      l₀ ≠ l₁ ∧ l₁ ≠ l₂ ∧ l₂ ≠ l₀ ∧
      Incident p₀ l₀ ∧ Incident p₁ l₀ ∧
      Incident p₁ l₁ ∧ Incident p₂ l₁ ∧
      Incident p₂ l₂ ∧ Incident p₀ l₂ := by
  rintro ⟨p₀, p₁, p₂, l₀, l₁, l₂, hp01, hp12, hp20,
    hl01, hl12, hl20, hp0l0, hp1l0, hp1l1, hp2l1, hp2l2, hp0l2⟩
  have hx01 : p₀.x ≠ p₁.x := by
    intro h
    exact hp01 (point_eq_of_same_x_of_incident h hp0l0 hp1l0)
  have hx12 : p₁.x ≠ p₂.x := by
    intro h
    exact hp12 (point_eq_of_same_x_of_incident h hp1l1 hp2l1)
  have hx20 : p₂.x ≠ p₀.x := by
    intro h
    exact hp20 (point_eq_of_same_x_of_incident h hp2l2 hp0l2)
  let s₀ : F a := l₀.x - l₂.x
  let s₁ : F a := l₁.x - l₀.x
  let s₂ : F a := l₂.x - l₁.x
  have hd₀ := line_differences_at_point hp0l0 hp0l2
  have hd₁ := line_differences_at_point hp1l1 hp1l0
  have hd₂ := line_differences_at_point hp2l2 hp2l1
  have hs0 : s₀ + s₁ + s₂ = 0 := by
    simp only [s₀, s₁, s₂]
    ring
  have hs1 : s₀ * p₀.x + s₁ * p₁.x + s₂ * p₂.x = 0 := by
    simp only [s₀, s₁, s₂]
    linear_combination -hd₀.1 - hd₁.1 - hd₂.1
  have hs2 : s₀ * p₀.x ^ 2 + s₁ * p₁.x ^ 2 + s₂ * p₂.x ^ 2 = 0 := by
    simp only [s₀, s₁, s₂]
    linear_combination -hd₀.2 - hd₁.2 - hd₂.2
  have hs := vandermonde_three hx01 hx12 hx20 hs0 hs1 hs2
  have hxline : l₀.x = l₂.x := by
    exact sub_eq_zero.mp hs.1
  exact hl20 (line_eq_of_same_x_of_incident hxline hp0l0 hp0l2).symm

/-- The point-to-line half of the exceptional polarity. -/
def pointToLine {a : ℕ} (p : Point a) : Line a :=
  ⟨p.x ^ (2 * theta a), (p.x * p.y) ^ theta a + p.z ^ theta a,
    p.y ^ (2 * theta a)⟩

/-- The line-to-point half of the exceptional polarity. -/
def lineToPoint {a : ℕ} (l : Line a) : Point a :=
  ⟨l.x ^ theta a, l.z ^ theta a,
    (l.x * l.z) ^ theta a + l.y ^ (2 * theta a)⟩

private lemma pow_mul_theta {a : ℕ} (x : F a) (m n : ℕ) :
    (x ^ m) ^ n = x ^ (m * n) := by simp [pow_mul]

lemma add_pow_theta {a : ℕ} (x y : F a) :
    (x + y) ^ theta a = x ^ theta a + y ^ theta a := by
  simpa [theta] using (add_pow_expChar_pow x y (p := 2) (n := a))

lemma add_pow_two_theta {a : ℕ} (x y : F a) :
    (x + y) ^ (2 * theta a) = x ^ (2 * theta a) + y ^ (2 * theta a) := by
  rw [two_mul_theta]
  exact add_pow_expChar_pow x y (p := 2) (n := a + 1)

lemma pow_theta_pow_two_theta {a : ℕ} (x : F a) :
    (x ^ theta a) ^ (2 * theta a) = x := by
  rw [pow_mul_theta]
  convert pow_two_theta_sq a x using 1 <;> ring

lemma pow_two_theta_pow_theta {a : ℕ} (x : F a) :
    (x ^ (2 * theta a)) ^ theta a = x := by
  rw [pow_mul_theta]
  exact pow_two_theta_sq a x

lemma lineToPoint_pointToLine {a : ℕ} (p : Point a) :
    lineToPoint (pointToLine p) = p := by
  ext
  · simp only [lineToPoint, pointToLine]
    rw [pow_mul_theta]
    exact pow_two_theta_sq a p.x
  · simp only [lineToPoint, pointToLine]
    rw [pow_mul_theta]
    exact pow_two_theta_sq a p.y
  · simp only [lineToPoint, pointToLine]
    rw [mul_pow, add_pow_two_theta]
    rw [pow_two_theta_pow_theta, pow_two_theta_pow_theta]
    rw [pow_theta_pow_two_theta, pow_theta_pow_two_theta]
    exact CharTwo.add_cancel_left _ _

lemma pointToLine_lineToPoint {a : ℕ} (l : Line a) :
    pointToLine (lineToPoint l) = l := by
  ext
  · simp only [pointToLine, lineToPoint]
    exact pow_theta_pow_two_theta l.x
  · simp only [pointToLine, lineToPoint]
    rw [mul_pow, add_pow_theta, pow_two_theta_pow_theta]
    have hsame :
        (l.x ^ theta a) ^ theta a * (l.z ^ theta a) ^ theta a =
          ((l.x * l.z) ^ theta a) ^ theta a := by
      simp only [mul_pow]
    rw [hsame, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  · simp only [pointToLine, lineToPoint]
    exact pow_theta_pow_two_theta l.z

/-- The polarity is a genuine equivalence between affine points and lines. -/
def polarityEquiv (a : ℕ) : Point a ≃ Line a where
  toFun := pointToLine
  invFun := lineToPoint
  left_inv := lineToPoint_pointToLine
  right_inv := pointToLine_lineToPoint

private lemma pow_two_theta_eq_theta_sq {a : ℕ} (x : F a) :
    x ^ (2 * theta a) = (x ^ theta a) ^ 2 := by
  simpa only [mul_comm] using (pow_mul x (theta a) 2)

private lemma polarity_incident_first {a : ℕ} {x y z u v w : F a}
    (hvy : v - y = u * x) (hwz : w - z = v * x) :
    (x * y) ^ theta a + z ^ theta a - w ^ theta a =
      x ^ (2 * theta a) * u ^ theta a := by
  have hvy' : v + y = u * x := by
    simpa only [CharTwo.sub_eq_add] using hvy
  have hwz' : w + z = v * x := by
    simpa only [CharTwo.sub_eq_add] using hwz
  have hθvy := congrArg (fun t : F a => t ^ theta a) hvy'
  have hθwz := congrArg (fun t : F a => t ^ theta a) hwz'
  rw [add_pow_theta, mul_pow] at hθvy hθwz
  rw [CharTwo.sub_eq_add, mul_pow, pow_two_theta_eq_theta_sq]
  linear_combination (x ^ theta a) * hθvy + hθwz

private lemma polarity_incident_second {a : ℕ} {x y z u v w : F a}
    (hvy : v - y = u * x) (hwz : w - z = v * x) :
    y ^ (2 * theta a) - ((u * w) ^ theta a + v ^ (2 * theta a)) =
      ((x * y) ^ theta a + z ^ theta a) * u ^ theta a := by
  have hvy' : v + y = u * x := by
    simpa only [CharTwo.sub_eq_add] using hvy
  have hwz' : w + z = v * x := by
    simpa only [CharTwo.sub_eq_add] using hwz
  have hθvy := congrArg (fun t : F a => t ^ theta a) hvy'
  have hθwz := congrArg (fun t : F a => t ^ theta a) hwz'
  rw [add_pow_theta, mul_pow] at hθvy hθwz
  have hsq := congrArg (fun t : F a => t ^ 2) hθvy
  rw [CharTwo.add_sq, mul_pow] at hsq
  have htwo : (2 : F a) = 0 := CharTwo.two_eq_zero
  rw [CharTwo.sub_eq_add, mul_pow, mul_pow,
    pow_two_theta_eq_theta_sq, pow_two_theta_eq_theta_sq]
  linear_combination hsq + (u ^ theta a) * hθwz +
    (u ^ theta a * x ^ theta a) * hθvy -
    (u ^ theta a *
      (z ^ theta a + x ^ theta a * y ^ theta a -
        u ^ theta a * (x ^ theta a) ^ 2)) * htwo

/-- Incidence is preserved when point and line are interchanged by the polarity. -/
lemma incident_polarity_forward {a : ℕ} {p : Point a} {l : Line a}
    (h : Incident p l) : Incident (lineToPoint l) (pointToLine p) := by
  exact ⟨polarity_incident_first h.1 h.2, polarity_incident_second h.1 h.2⟩

/-- The two incidence equations are invariant under the exceptional polarity. -/
theorem incident_polarity {a : ℕ} (p : Point a) (l : Line a) :
    Incident p l ↔ Incident (lineToPoint l) (pointToLine p) := by
  constructor
  · exact incident_polarity_forward
  · intro h
    have h' := incident_polarity_forward h
    simpa only [lineToPoint_pointToLine, pointToLine_lineToPoint] using h'

/-- Symmetric incidence after identifying lines with points by the polarity. -/
theorem incident_pointToLine_comm {a : ℕ} (p q : Point a) :
    Incident p (pointToLine q) ↔ Incident q (pointToLine p) := by
  simpa only [lineToPoint_pointToLine] using incident_polarity p (pointToLine q)

/-- The simple graph obtained by identifying the two sides of the incidence graph. -/
def polarityGraph (a : ℕ) : SimpleGraph (Point a) where
  Adj p q := p ≠ q ∧ Incident p (pointToLine q)
  symm := ⟨by
    intro p q h
    exact ⟨h.1.symm, (incident_pointToLine_comm p q).mp h.2⟩⟩
  loopless := ⟨by intro p h; exact h.1 rfl⟩

instance polarityGraphDecidableRel (a : ℕ) : DecidableRel (polarityGraph a).Adj :=
  fun _ _ => Classical.propDecidable _

@[simp] lemma polarityGraph_adj {a : ℕ} {p q : Point a} :
    (polarityGraph a).Adj p q ↔ p ≠ q ∧ Incident p (pointToLine q) := Iff.rfl

/-- A labelled triangle in a simple graph. -/
def IsC3 {V : Type*} (G : SimpleGraph V) (v₀ v₁ v₂ : V) : Prop :=
  v₀ ≠ v₁ ∧ v₁ ≠ v₂ ∧ v₂ ≠ v₀ ∧
    G.Adj v₀ v₁ ∧ G.Adj v₁ v₂ ∧ G.Adj v₂ v₀

/-- A labelled simple quadrilateral in a simple graph. -/
def IsC4 {V : Type*} (G : SimpleGraph V) (v₀ v₁ v₂ v₃ : V) : Prop :=
  v₀ ≠ v₁ ∧ v₀ ≠ v₂ ∧ v₀ ≠ v₃ ∧ v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ ∧
    G.Adj v₀ v₁ ∧ G.Adj v₁ v₂ ∧ G.Adj v₂ v₃ ∧ G.Adj v₃ v₀

/-- A labelled simple hexagon in a simple graph. -/
def IsC6 {V : Type*} (G : SimpleGraph V) (v₀ v₁ v₂ v₃ v₄ v₅ : V) : Prop :=
  v₀ ≠ v₁ ∧ v₀ ≠ v₂ ∧ v₀ ≠ v₃ ∧ v₀ ≠ v₄ ∧ v₀ ≠ v₅ ∧
  v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₁ ≠ v₄ ∧ v₁ ≠ v₅ ∧
  v₂ ≠ v₃ ∧ v₂ ≠ v₄ ∧ v₂ ≠ v₅ ∧
  v₃ ≠ v₄ ∧ v₃ ≠ v₅ ∧ v₄ ≠ v₅ ∧
  G.Adj v₀ v₁ ∧ G.Adj v₁ v₂ ∧ G.Adj v₂ v₃ ∧
  G.Adj v₃ v₄ ∧ G.Adj v₄ v₅ ∧ G.Adj v₅ v₀

/-- A triangle in the polarity graph would lift to an incidence hexagon. -/
theorem polarityGraph_no_C3 (a : ℕ) :
    ¬ ∃ p₀ p₁ p₂ : Point a, IsC3 (polarityGraph a) p₀ p₁ p₂ := by
  rintro ⟨p₀, p₁, p₂, hp01, hp12, hp20, h01, h12, h20⟩
  apply no_incidence_C6
  refine ⟨p₀, p₂, p₁, pointToLine p₁, pointToLine p₀, pointToLine p₂,
    hp20.symm, hp12.symm, hp01.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hp01 ((polarityEquiv a).injective h.symm)
  · exact fun h => hp20 ((polarityEquiv a).injective h.symm)
  · exact fun h => hp12 ((polarityEquiv a).injective h.symm)
  · exact h01.2
  · exact (incident_pointToLine_comm p₁ p₂).mp h12.2
  · exact h20.2
  · exact (incident_pointToLine_comm p₀ p₁).mp h01.2
  · exact h12.2
  · exact (incident_pointToLine_comm p₂ p₀).mp h20.2

/-- A quadrilateral in the polarity graph would lift to an incidence quadrilateral. -/
theorem polarityGraph_no_C4 (a : ℕ) :
    ¬ ∃ p₀ p₁ p₂ p₃ : Point a, IsC4 (polarityGraph a) p₀ p₁ p₂ p₃ := by
  rintro ⟨p₀, p₁, p₂, p₃, hp01, hp02, hp03, hp12, hp13, hp23,
    h01, h12, h23, h30⟩
  apply no_incidence_C4
  refine ⟨p₀, p₂, pointToLine p₁, pointToLine p₃,
    hp02, fun h => hp13 ((polarityEquiv a).injective h), ?_, ?_, ?_, ?_⟩
  · exact h01.2
  · exact (incident_pointToLine_comm p₁ p₂).mp h12.2
  · exact (incident_pointToLine_comm p₃ p₀).mp h30.2
  · exact h23.2

/-- A hexagon in the polarity graph would lift, using alternating vertices,
to an incidence hexagon. -/
theorem polarityGraph_no_C6 (a : ℕ) :
    ¬ ∃ p₀ p₁ p₂ p₃ p₄ p₅ : Point a,
      IsC6 (polarityGraph a) p₀ p₁ p₂ p₃ p₄ p₅ := by
  rintro ⟨p₀, p₁, p₂, p₃, p₄, p₅,
    hp01, hp02, hp03, hp04, hp05, hp12, hp13, hp14, hp15,
    hp23, hp24, hp25, hp34, hp35, hp45,
    h01, h12, h23, h34, h45, h50⟩
  apply no_incidence_C6
  refine ⟨p₀, p₂, p₄, pointToLine p₁, pointToLine p₃, pointToLine p₅,
    hp02, hp24, hp04.symm,
    fun h => hp13 ((polarityEquiv a).injective h),
    fun h => hp35 ((polarityEquiv a).injective h),
    fun h => hp15.symm ((polarityEquiv a).injective h),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h01.2
  · exact (incident_pointToLine_comm p₁ p₂).mp h12.2
  · exact h23.2
  · exact (incident_pointToLine_comm p₃ p₄).mp h34.2
  · exact h45.2
  · exact (incident_pointToLine_comm p₅ p₀).mp h50.2

/-- The `z`-coordinate of the absolute point with prescribed `x,y`. -/
def absoluteZ {a : ℕ} (x y : F a) : F a :=
  x ^ (2 * theta a + 2) + x * y + y ^ (2 * theta a)

/-- The absolute point parametrized by `(x,y)`. -/
def absolutePoint {a : ℕ} (x y : F a) : Point a :=
  ⟨x, y, absoluteZ x y⟩

/-- A point is absolute when it is incident with its polar line. -/
def IsAbsolute {a : ℕ} (p : Point a) : Prop := Incident p (pointToLine p)

instance isAbsoluteDecidable (a : ℕ) : DecidablePred (@IsAbsolute a) :=
  fun _ => Classical.propDecidable _

lemma pow_absoluteZ_leading {a : ℕ} (x : F a) :
    (x ^ (2 * theta a + 2)) ^ theta a = x ^ (2 * theta a) * x := by
  rw [pow_mul_theta]
  rw [show (2 * theta a + 2) * theta a =
      2 * theta a * theta a + 2 * theta a by ring]
  rw [pow_add, pow_two_theta_sq]
  ring

lemma pow_absolute_converse_leading {a : ℕ} (x : F a) :
    (x ^ (2 * theta a + 1)) ^ (2 * theta a) = x ^ (2 * theta a + 2) := by
  rw [pow_mul_theta]
  rw [show (2 * theta a + 1) * (2 * theta a) =
      (2 * theta a * theta a) * 2 + 2 * theta a by ring]
  rw [pow_add]
  have hqpow : x ^ ((2 * theta a * theta a) * 2) = x ^ 2 := by
    rw [pow_mul, pow_two_theta_sq]
  rw [hqpow, ← pow_add]
  congr 1 <;> ring

lemma absolutePoint_isAbsolute {a : ℕ} (x y : F a) :
    IsAbsolute (absolutePoint x y) := by
  have hzpow : (absoluteZ x y) ^ theta a =
      x ^ (2 * theta a) * x + (x * y) ^ theta a + y := by
    simp only [absoluteZ, add_pow_theta, pow_absoluteZ_leading,
      pow_two_theta_pow_theta]
  have hfirst :
      (x * y) ^ theta a + (absoluteZ x y) ^ theta a + y =
        x ^ (2 * theta a) * x := by
    rw [hzpow]
    have htwo : (2 : F a) = 0 := CharTwo.two_eq_zero
    linear_combination ((x * y) ^ theta a + y) * htwo
  constructor
  · simpa only [IsAbsolute, Incident, absolutePoint, pointToLine,
      CharTwo.sub_eq_add] using hfirst
  · simp only [IsAbsolute, Incident, absolutePoint, pointToLine,
      CharTwo.sub_eq_add]
    have hv : (x * y) ^ theta a + (absoluteZ x y) ^ theta a =
        x ^ (2 * theta a) * x + y := by
      exact (CharTwo.add_eq_iff_eq_add.mp hfirst)
    rw [hv, absoluteZ]
    have htwo : (2 : F a) = 0 := CharTwo.two_eq_zero
    linear_combination (y ^ (2 * theta a)) * htwo

/-- Exact affine parametrization of the absolute points. -/
theorem isAbsolute_iff {a : ℕ} (p : Point a) :
    IsAbsolute p ↔ p.z = absoluteZ p.x p.y := by
  constructor
  · intro h
    have hy := h.1
    rw [CharTwo.sub_eq_add] at hy
    have hztheta : p.z ^ theta a =
        (p.x * p.y) ^ theta a + p.y + p.x ^ (2 * theta a + 1) := by
      simp only [pointToLine] at hy
      have htwo : (2 : F a) = 0 := CharTwo.two_eq_zero
      linear_combination hy - ((p.x * p.y) ^ theta a + p.y) * htwo
    have hp := congrArg (fun z : F a => z ^ (2 * theta a)) hztheta
    rw [add_pow_two_theta, add_pow_two_theta, pow_theta_pow_two_theta,
      pow_theta_pow_two_theta, pow_absolute_converse_leading] at hp
    simpa only [absoluteZ, add_assoc, add_comm, add_left_comm] using hp
  · intro h
    have hp : p = absolutePoint p.x p.y := by
      ext <;> simp [absolutePoint, h]
    rw [hp]
    exact absolutePoint_isAbsolute p.x p.y

/-- Absolute points are in bijection with `F²`. -/
def absoluteEquiv (a : ℕ) :
    F a × F a ≃ {p : Point a // IsAbsolute p} where
  toFun xy := ⟨absolutePoint xy.1 xy.2, absolutePoint_isAbsolute xy.1 xy.2⟩
  invFun p := (p.1.x, p.1.y)
  left_inv xy := by rcases xy with ⟨x, y⟩; rfl
  right_inv p := by
    apply Subtype.ext
    ext
    · rfl
    · rfl
    · exact (isAbsolute_iff p.1).mp p.2 |>.symm

lemma absolute_card (a : ℕ) :
    Fintype.card {p : Point a // IsAbsolute p} = (2 ^ (2 * a + 1)) ^ 2 := by
  calc
    Fintype.card {p : Point a // IsAbsolute p} = Fintype.card (F a × F a) :=
      (Fintype.card_congr (absoluteEquiv a)).symm
    _ = (2 ^ (2 * a + 1)) ^ 2 := by simp [field_card, pow_two]

/-- Neighbors of `p` correspond to its incident lines other than its own polar line. -/
def neighborLineEquiv {a : ℕ} (p : Point a) :
    (polarityGraph a).neighborSet p ≃
      {l : Line a // Incident p l ∧ l ≠ pointToLine p} where
  toFun q := ⟨pointToLine q.1, q.2.2,
    fun h => q.2.1 ((polarityEquiv a).injective h.symm)⟩
  invFun l := by
    refine ⟨lineToPoint l.1, ?_⟩
    rw [SimpleGraph.mem_neighborSet, polarityGraph_adj]
    constructor
    · intro h
      apply l.2.2
      calc
        l.1 = pointToLine (lineToPoint l.1) := (pointToLine_lineToPoint l.1).symm
        _ = pointToLine p := congrArg pointToLine h.symm
    · simpa only [pointToLine_lineToPoint] using l.2.1
  left_inv q := by
    apply Subtype.ext
    exact lineToPoint_pointToLine q.1
  right_inv l := by
    apply Subtype.ext
    exact pointToLine_lineToPoint l.1

private def nonpolarIncidentEquivOfAbsolute {a : ℕ} (p : Point a) (hp : IsAbsolute p) :
    {l : Line a // Incident p l ∧ l ≠ pointToLine p} ≃
      {l : {l : Line a // Incident p l} // l ≠ ⟨pointToLine p, hp⟩} where
  toFun l := ⟨⟨l.1, l.2.1⟩, fun h => l.2.2 (congrArg Subtype.val h)⟩
  invFun l := ⟨l.1.1, l.1.2, fun h => l.2 (Subtype.ext h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def nonpolarIncidentEquivOfNonabsolute {a : ℕ} (p : Point a)
    (hp : ¬IsAbsolute p) :
    {l : Line a // Incident p l ∧ l ≠ pointToLine p} ≃
      {l : Line a // Incident p l} where
  toFun l := ⟨l.1, l.2.1⟩
  invFun l := ⟨l.1, l.2, fun h => by
    apply hp
    simpa [IsAbsolute, h] using l.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Vertices have degree `q-1` at absolute points and degree `q` otherwise. -/
theorem polarityGraph_degree (a : ℕ) (p : Point a) :
    (polarityGraph a).degree p =
      if IsAbsolute p then 2 ^ (2 * a + 1) - 1 else 2 ^ (2 * a + 1) := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  rw [Fintype.card_congr (neighborLineEquiv p)]
  split_ifs with hp
  · rw [Fintype.card_congr (nonpolarIncidentEquivOfAbsolute p hp)]
    rw [Fintype.card_subtype_compl (fun l : {l : Line a // Incident p l} =>
      l = ⟨pointToLine p, hp⟩)]
    simp only [Fintype.card_unique, card_incident_lines]
  · rw [Fintype.card_congr (nonpolarIncidentEquivOfNonabsolute p hp)]
    exact card_incident_lines a p

lemma absolute_filter_card (a : ℕ) :
    #(Finset.univ.filter fun p : Point a => IsAbsolute p) = (2 ^ (2 * a + 1)) ^ 2 := by
  rw [← Fintype.card_subtype (fun p : Point a => IsAbsolute p)]
  exact absolute_card a

/-- Degree sum in the affine polarity graph. -/
theorem polarityGraph_sum_degrees (a : ℕ) :
    ∑ p : Point a, (polarityGraph a).degree p =
      (2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 := by
  let q := 2 ^ (2 * a + 1)
  have hq : 0 < q := by simp [q]
  have hdegAbs : ∀ p ∈ (Finset.univ.filter fun p : Point a => IsAbsolute p),
      (polarityGraph a).degree p = q - 1 := by
    intro p hp
    rw [polarityGraph_degree a p]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp [hp, q]
  have hdegNon : ∀ p ∈ (Finset.univ.filter fun p : Point a => ¬IsAbsolute p),
      (polarityGraph a).degree p = q := by
    intro p hp
    rw [polarityGraph_degree a p]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp [hp, q]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Point a => IsAbsolute p)]
  rw [Finset.sum_congr rfl hdegAbs, Finset.sum_const]
  rw [Finset.sum_congr rfl hdegNon, Finset.sum_const]
  simp only [nsmul_eq_mul, Nat.cast_id]
  have habs : #(Finset.univ.filter fun p : Point a => IsAbsolute p) = q ^ 2 := by
    simpa [q] using absolute_filter_card a
  have hnon : #(Finset.univ.filter fun p : Point a => ¬IsAbsolute p) = q ^ 3 - q ^ 2 := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Point a))) (p := fun p => IsAbsolute p)
    rw [habs, Finset.card_univ, coord_card] at hpartition
    simpa [q] using (Nat.eq_sub_of_add_eq' hpartition)
  rw [habs, hnon]
  have hA : q ^ 2 * (q - 1) = q ^ 3 - q ^ 2 := by
    rw [Nat.mul_sub_left_distrib]
    ring
  have hB : (q ^ 3 - q ^ 2) * q = q ^ 4 - q ^ 3 := by
    rw [Nat.mul_sub_right_distrib]
    ring
  have h23 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right hq (by omega)
  have h34 : q ^ 3 ≤ q ^ 4 := Nat.pow_le_pow_right hq (by omega)
  rw [hA, hB]
  change (q ^ 3 - q ^ 2) + (q ^ 4 - q ^ 3) = q ^ 4 - q ^ 2
  omega

/-- Twice the number of edges is `q^4-q^2`. -/
theorem polarityGraph_twice_edge_card (a : ℕ) :
    2 * #(polarityGraph a).edgeFinset =
      (2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 := by
  rw [← (polarityGraph a).sum_degrees_eq_twice_card_edges]
  exact polarityGraph_sum_degrees a

/-- Exact edge count of the affine quotient graph. -/
theorem polarityGraph_edge_card (a : ℕ) :
    #(polarityGraph a).edgeFinset =
      ((2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2) / 2 := by
  have h := polarityGraph_twice_edge_card a
  omega

/-- A labelled copy of the affine polarity graph on `Fin (q^3)`. -/
noncomputable def finitePolarityGraph (a : ℕ) :
    SimpleGraph (Fin ((2 ^ (2 * a + 1)) ^ 3)) :=
  (polarityGraph a).overFin (coord_card a)

noncomputable instance finitePolarityGraphDecidableRel (a : ℕ) :
    DecidableRel (finitePolarityGraph a).Adj :=
  fun _ _ => Classical.propDecidable _

end

end AffinePolarity

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/AffineCount.lean` -/

section
/-!
# Counting and relabelling the affine polarity graph

This file packages the coordinate construction from `AffinePolarity` in the
standard finite-graph language used by the rest of the development.  In
particular, it records all cardinalities with `q = 2^(2a+1)`, relabels the
graph on `Fin (q^3)`, and converts the explicit labelled-cycle exclusions to
Mathlib's `CliqueFree` and `Free` predicates.
-/

open Finset Function

namespace AffineCount

noncomputable section

open AffinePolarity

/-- The order of the finite field in the affine construction. -/
abbrev q (a : ℕ) : ℕ := 2 ^ (2 * a + 1)

/-- The affine polarity graph has `q³` vertices. -/
theorem card_polarityGraph_vertices (a : ℕ) :
    Fintype.card (Point a) = q a ^ 3 := by
  exact coord_card a

/-- The exact number of (undirected) edges in the affine polarity graph. -/
theorem card_polarityGraph_edges (a : ℕ) :
    (polarityGraph a).edgeFinset.card = (q a ^ 4 - q a ^ 2) / 2 := by
  exact polarityGraph_edge_card a

/-- A coordinate-free relabelling of the affine graph on `Fin (q³)`. -/
def graph (a : ℕ) : SimpleGraph (Fin (q a ^ 3)) :=
  (polarityGraph a).overFin (card_polarityGraph_vertices a)

noncomputable instance graphAdjDecidable (a : ℕ) : DecidableRel (graph a).Adj :=
  Classical.decRel _

/-- Relabelling by `Fin (q³)` is a graph isomorphism. -/
def graphIso (a : ℕ) : polarityGraph a ≃g graph a :=
  (polarityGraph a).overFinIso (card_polarityGraph_vertices a)

/-- The exact edge count is unchanged by the relabelling. -/
theorem card_graph_edges (a : ℕ) :
    (graph a).edgeFinset.card = (q a ^ 4 - q a ^ 2) / 2 := by
  rw [← (graphIso a).card_edgeFinset_eq]
  exact card_polarityGraph_edges a

/-- An explicit exclusion of labelled triangles implies Mathlib's
`CliqueFree 3` predicate. -/
theorem cliqueFree_three_of_no_C3 {V : Type*} {G : SimpleGraph V}
    (hG : ¬ ∃ v₀ v₁ v₂, IsC3 G v₀ v₁ v₂) : G.CliqueFree 3 := by
  by_contra h
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree h
  apply hG
  refine ⟨f 0, f 1, f 2, f.injective.ne (by decide),
    f.injective.ne (by decide), f.injective.ne (by decide), ?_, ?_, ?_⟩
  · exact f.toHom.map_adj (by simp)
  · exact f.toHom.map_adj (by simp)
  · exact f.toHom.map_adj (by simp)

/-- An explicit exclusion of labelled simple hexagons implies that the graph
contains no copy of Mathlib's six-cycle. -/
theorem cycleGraph_six_free_of_no_C6 {V : Type*} {G : SimpleGraph V}
    (hG : ¬ ∃ v₀ v₁ v₂ v₃ v₄ v₅,
      AffinePolarity.IsC6 G v₀ v₁ v₂ v₃ v₄ v₅) :
    (SimpleGraph.cycleGraph 6).Free G := by
  rintro ⟨f⟩
  apply hG
  refine ⟨f 0, f 1, f 2, f 3, f 4, f 5,
    f.injective.ne (by decide), f.injective.ne (by decide),
    f.injective.ne (by decide), f.injective.ne (by decide),
    f.injective.ne (by decide), f.injective.ne (by decide),
    f.injective.ne (by decide), f.injective.ne (by decide),
    f.injective.ne (by decide), f.injective.ne (by decide),
    f.injective.ne (by decide), f.injective.ne (by decide),
    f.injective.ne (by decide), f.injective.ne (by decide),
    f.injective.ne (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals exact f.toHom.map_adj (by decide)

/-- The coordinate polarity graph is triangle-free in Mathlib's standard
sense. -/
theorem polarityGraph_cliqueFree_three (a : ℕ) :
    (polarityGraph a).CliqueFree 3 :=
  cliqueFree_three_of_no_C3 (polarityGraph_no_C3 a)

/-- The coordinate polarity graph is free of Mathlib's six-cycle. -/
theorem polarityGraph_cycleGraph_six_free (a : ℕ) :
    (SimpleGraph.cycleGraph 6).Free (polarityGraph a) :=
  cycleGraph_six_free_of_no_C6 (polarityGraph_no_C6 a)

/-- Triangle-freeness transfers to the graph on `Fin (q³)`. -/
theorem graph_cliqueFree_three (a : ℕ) : (graph a).CliqueFree 3 :=
  (polarityGraph_cliqueFree_three a).comap
    (graphIso a).symm.toEmbedding.isContained

/-- Six-cycle-freeness transfers to the graph on `Fin (q³)`. -/
theorem graph_cycleGraph_six_free (a : ℕ) :
    (SimpleGraph.cycleGraph 6).Free (graph a) :=
  (SimpleGraph.free_congr_right (graphIso a)).mp
    (polarityGraph_cycleGraph_six_free a)

end

end AffineCount

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/Duplication.lean` -/

section
/-!
# The Füredi--Naor--Verstraëte duplication construction

This file isolates the purely graph-theoretic part of the lower construction
used for Erdős problem 59.  A set `A` of vertices is copied.  Edges from `A`
to its complement are copied, while an edge inside `A` is copied in the
direction selected by an orientation.
-/

open scoped BigOperators
open Finset

namespace FNV

variable {V : Type*} (G : SimpleGraph V) (A : Finset V)

/-- An orientation of the edges of `G` induced by `A`. -/
structure Orientation where
  /-- `Dir x y` means that the edge is directed from `x` to `y`. -/
  Dir : V → V → Prop
  dir_adj : ∀ {x y}, Dir x y → G.Adj x y
  dir_fst_mem : ∀ {x y}, Dir x y → x ∈ A
  dir_snd_mem : ∀ {x y}, Dir x y → y ∈ A
  exactly_one : ∀ {x y}, G.Adj x y → x ∈ A → y ∈ A → (Dir x y ↔ ¬ Dir y x)

namespace Orientation

variable {G A} (O : Orientation G A)

lemma not_rev {x y : V} (h : O.Dir x y) : ¬ O.Dir y x := by
  exact (O.exactly_one (O.dir_adj h) (O.dir_fst_mem h) (O.dir_snd_mem h)).mp h

lemma resolve {x y : V} (hxy : G.Adj x y) (hx : x ∈ A) (hy : y ∈ A) :
    O.Dir x y ∨ O.Dir y x := by
  by_cases h : O.Dir x y
  · exact Or.inl h
  · exact Or.inr <| not_not.mp <| (O.exactly_one hxy hx hy).not.mp h

end Orientation

/-- The old vertices together with a disjoint copy of `A`. -/
abbrev DuplicateVertex := Sum V A

/-- Collapse a copied vertex back to its old vertex. -/
def project : DuplicateVertex A → V
  | .inl v => v
  | .inr a => a.1

variable (O : Orientation G A)

/-- The FNV graph obtained by duplicating `A` according to `O`. -/
def duplication : SimpleGraph (DuplicateVertex A) where
  Adj x y :=
    match x, y with
    | .inl x, .inl y => G.Adj x y
    | .inl x, .inr y => G.Adj x y ∧ (x ∉ A ∨ O.Dir y x)
    | .inr x, .inl y => G.Adj x y ∧ (y ∉ A ∨ O.Dir x y)
    | .inr _, .inr _ => False
  symm := ⟨by
    rintro (x | x) (y | y) h
    · exact h.symm
    · exact ⟨h.1.symm, h.2⟩
    · exact ⟨h.1.symm, h.2⟩
    · exact h⟩
  loopless := ⟨by
    rintro (x | x) h
    · exact G.loopless.irrefl _ h
    · exact h⟩

instance [DecidableEq V] [DecidableRel G.Adj] [DecidableRel O.Dir] :
    DecidableRel (duplication G A O).Adj := by
  intro x y
  cases x <;> cases y <;> simp only [duplication] <;> infer_instance

@[simp] lemma duplication_adj_old_old (x y : V) :
    (duplication G A O).Adj (.inl x) (.inl y) ↔ G.Adj x y := Iff.rfl

@[simp] lemma duplication_adj_old_new (x : V) (y : A) :
    (duplication G A O).Adj (.inl x) (.inr y) ↔
      G.Adj x y ∧ (x ∉ A ∨ O.Dir y x) := Iff.rfl

@[simp] lemma duplication_adj_new_old (x : A) (y : V) :
    (duplication G A O).Adj (.inr x) (.inl y) ↔
      G.Adj x y ∧ (y ∉ A ∨ O.Dir x y) := Iff.rfl

@[simp] lemma duplication_not_adj_new_new (x y : A) :
    ¬ (duplication G A O).Adj (.inr x) (.inr y) := by simp [duplication]

/-- Every new edge projects to an old edge. -/
def projectionHom : duplication G A O →g G where
  toFun := project A
  map_rel' := by
    intro x y h
    cases x <;> cases y <;> simp_all [duplication, project]

@[simp] lemma projectionHom_apply (x : DuplicateVertex A) :
    projectionHom G A O x = project A x := rfl

/-- A cycle is represented by six distinct cyclically adjacent vertices. -/
def IsSixCycle (H : SimpleGraph V) (x : Fin 6 → V) : Prop :=
  Function.Injective x ∧ ∀ i, H.Adj (x i) (x (i + 1))

/-- `H` has no cycle of length six. -/
def C6Free (H : SimpleGraph V) : Prop :=
  ∀ x : Fin 6 → V, ¬ IsSixCycle H x

/-- The analogous indexed definition of quadrilateral-freeness. -/
def C4Free (H : SimpleGraph V) : Prop :=
  ∀ x : Fin 4 → V, ¬ (Function.Injective x ∧ ∀ i, H.Adj (x i) (x (i + 1)))

/-- Triangle-freeness, stated using Mathlib's clique predicate. -/
abbrev TriangleFree (H : SimpleGraph V) : Prop := H.CliqueFree 3

private lemma project_eq_of_ne {x y : DuplicateVertex A}
    (hxy : project A x = project A y) (hne : x ≠ y) :
    (∃ a : A, x = .inl a.1 ∧ y = .inr a) ∨
      ∃ a : A, x = .inr a ∧ y = .inl a.1 := by
  cases x with
  | inl x =>
      cases y with
      | inl y => exact False.elim <| hne <| congrArg Sum.inl hxy
      | inr y => exact Or.inl ⟨y, by simpa [project] using hxy, rfl⟩
  | inr x =>
      cases y with
      | inl y => exact Or.inr ⟨x, rfl, by simpa [project] using hxy.symm⟩
      | inr y =>
          exact False.elim <| hne <| congrArg Sum.inr <| Subtype.ext hxy

private lemma project_fiber_three {x y z : DuplicateVertex A}
    (hxy : project A x = project A y) (hxz : project A x = project A z) :
    x = y ∨ x = z ∨ y = z := by
  cases x with
  | inl x =>
      cases y with
      | inl y => exact Or.inl <| congrArg Sum.inl hxy
      | inr y =>
          cases z with
          | inl z => exact Or.inr <| Or.inl <| congrArg Sum.inl hxz
          | inr z =>
              right; right
              exact congrArg Sum.inr <| Subtype.ext <| hxy.symm.trans hxz
  | inr x =>
      cases y with
      | inl y =>
          cases z with
          | inl z =>
              right; right
              exact congrArg Sum.inl <| hxy.symm.trans hxz
          | inr z => exact Or.inr <| Or.inl <| congrArg Sum.inr <| Subtype.ext hxz
      | inr y => exact Or.inl <| congrArg Sum.inr <| Subtype.ext hxy

private lemma c4_collision {a b c d : V} (hfree : C4Free G)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) :
    a = c ∨ b = d := by
  by_contra h
  push_neg at h
  apply hfree ![a, b, c, d]
  constructor
  · intro i j hij
    have hab' := hab.ne
    have hbc' := hbc.ne
    have hcd' := hcd.ne
    have hda' := hda.ne
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    · exact hab
    · exact hbc
    · exact hcd
    · simpa using hda

private lemma fin6_pair_cases (i j : Fin 6) (hij : i ≠ j) :
    j = i + 1 ∨ i = j + 1 ∨ j = i + 3 ∨
      (∃ k : Fin 6, i = k ∧ j = k + 2) ∨
      ∃ k : Fin 6, j = k ∧ i = k + 2 := by
  fin_cases i <;> fin_cases j <;> simp_all

private lemma triangle_of_opposite_collision
    (htri : TriangleFree G) {x : Fin 6 → DuplicateVertex A}
    (hadj : ∀ i, (duplication G A O).Adj (x i) (x (i + 1)))
    {i : Fin 6} (hopp : project A (x (i + 3)) = project A (x i)) : False := by
  classical
  let a := project A (x i)
  let b := project A (x (i + 1))
  let c := project A (x ((i + 1) + 1))
  have hab : G.Adj a b := (projectionHom G A O).map_rel (hadj i)
  have hbc : G.Adj b c := (projectionHom G A O).map_rel (hadj (i + 1))
  have hca : G.Adj c a := by
    have h := (projectionHom G A O).map_rel (hadj ((i + 1) + 1))
    simpa [a, c, add_assoc, hopp] using h
  exact htri {a, b, c} <| SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hca.symm, hbc⟩

private lemma gap_two_orientation_contradiction
    (h4 : C4Free G) {x : Fin 6 → DuplicateVertex A} (hinj : Function.Injective x)
    (hadj : ∀ i, (duplication G A O).Adj (x i) (x (i + 1)))
    {k : Fin 6} (hgap : project A (x k) = project A (x (k + 2))) : False := by
  let y : Fin 6 → DuplicateVertex A := fun i ↦ x (k + i)
  have hyinj : Function.Injective y := fun _ _ h ↦ by
    exact add_left_cancel (hinj h)
  have hyadj : ∀ i, (duplication G A O).Adj (y i) (y (i + 1)) := by
    intro i
    simpa [y, add_assoc] using hadj (k + i)
  have h02 : project A (y 0) = project A (y 2) := by simpa [y] using hgap
  have h03 : G.Adj (project A (y 0)) (project A (y 3)) := by
    rw [h02]
    simpa using (projectionHom G A O).map_rel (hyadj 2)
  have h34 : G.Adj (project A (y 3)) (project A (y 4)) := by
    simpa using (projectionHom G A O).map_rel (hyadj 3)
  have h45 : G.Adj (project A (y 4)) (project A (y 5)) := by
    simpa using (projectionHom G A O).map_rel (hyadj 4)
  have h50 : G.Adj (project A (y 5)) (project A (y 0)) := by
    simpa using (projectionHom G A O).map_rel (hyadj 5)
  have hc := c4_collision (G := G) h4 h03 h34 h45 h50
  have h35 : project A (y 3) = project A (y 5) := by
    rcases hc with h04 | h35
    · exact False.elim <| by
        rcases project_fiber_three (A := A) h02 h04 with h | h | h
        · exact (show (0 : Fin 6) ≠ 2 by decide) (hyinj (show y 0 = y 2 from h))
        · exact (show (0 : Fin 6) ≠ 4 by decide) (hyinj (show y 0 = y 4 from h))
        · exact (show (2 : Fin 6) ≠ 4 by decide) (hyinj (show y 2 = y 4 from h))
    · exact h35
  have hne02 : y 0 ≠ y 2 := fun h ↦ by exact (by decide : (0 : Fin 6) ≠ 2) (hyinj h)
  have hne35 : y 3 ≠ y 5 := fun h ↦ by exact (by decide : (3 : Fin 6) ≠ 5) (hyinj h)
  have he23 := hyadj 2
  have he50 := hyadj 5
  rcases project_eq_of_ne (A := A) h02 hne02 with ⟨a, h0, h2⟩ | ⟨a, h0, h2⟩ <;>
    rcases project_eq_of_ne (A := A) h35 hne35 with ⟨b, h3, h5⟩ | ⟨b, h3, h5⟩
  · have he23' : G.Adj a b ∧ O.Dir a b := by
      simpa [h2, h3, duplication] using he23
    have he50' : G.Adj b a ∧ O.Dir b a := by
      simpa [h5, h0, duplication] using he50
    have hab : O.Dir a b := he23'.2
    have hba : O.Dir b a := he50'.2
    exact O.not_rev hab hba
  · simpa [h2, h3, duplication] using he23
  · simpa [h5, h0, duplication] using he50
  · have he23' : G.Adj a b ∧ O.Dir b a := by
      simpa [h2, h3, duplication] using he23
    have he50' : G.Adj b a ∧ O.Dir a b := by
      simpa [h5, h0, duplication] using he50
    have hba : O.Dir b a := he23'.2
    have hab : O.Dir a b := he50'.2
    exact O.not_rev hab hba

/-- The FNV projection lemma: duplication preserves hexagon-freeness. -/
theorem duplication_c6Free (h3 : TriangleFree G) (h4 : C4Free G) (h6 : C6Free G) :
    C6Free (duplication G A O) := by
  intro x hx
  rcases hx with ⟨hinj, hadj⟩
  let p : Fin 6 → V := fun i ↦ project A (x i)
  have padj : ∀ i, G.Adj (p i) (p (i + 1)) := fun i ↦
    (projectionHom G A O).map_rel (hadj i)
  by_cases hp : Function.Injective p
  · exact h6 p ⟨hp, padj⟩
  · rw [Function.Injective] at hp
    push_neg at hp
    obtain ⟨i, j, hpij, hij⟩ := hp
    rcases fin6_pair_cases i j hij with h | h | h | h | h
    · exact (padj i).ne <| by simpa [h] using hpij
    · exact (padj j).ne <| by simpa [h] using hpij.symm
    · exact triangle_of_opposite_collision (G := G) (A := A) (O := O)
        h3 hadj (by simpa [p, h] using hpij.symm)
    · rcases h with ⟨k, rfl, rfl⟩
      exact gap_two_orientation_contradiction (G := G) (A := A) (O := O)
        h4 hinj hadj (by simpa [p] using hpij)
    · rcases h with ⟨k, rfl, rfl⟩
      exact gap_two_orientation_contradiction (G := G) (A := A) (O := O)
        h4 hinj hadj (by simpa [p] using hpij.symm)

/-- The projection is injective on any clique of the duplicated graph. -/
private lemma project_injOn_clique {s : Finset (DuplicateVertex A)}
    (hs : (duplication G A O).IsClique s) : Set.InjOn (project A) s := by
  intro x hx y hy hxy
  by_contra hne
  exact ((projectionHom G A O).map_rel
    (hs (x := x) (y := y) hx hy hne)).ne hxy

/-- Duplication of a triangle-free graph is triangle-free. -/
theorem duplication_triangleFree (h3 : TriangleFree G) :
    TriangleFree (duplication G A O) := by
  classical
  intro s hs
  let t := s.image (project A)
  have hcard : t.card = 3 := by
    simp only [t, card_image_iff.mpr
      (project_injOn_clique (G := G) (A := A) (O := O) hs.isClique), hs.card_eq]
  apply h3 t
  refine ⟨?_, hcard⟩
  intro x hx y hy hxy
  change x ∈ t at hx
  change y ∈ t at hy
  simp only [t, Finset.mem_image] at hx hy
  obtain ⟨x', hx's, rfl⟩ := hx
  obtain ⟨y', hy's, rfl⟩ := hy
  have hxy' : x' ≠ y' := fun h ↦ hxy (congrArg (project A) h)
  exact (projectionHom G A O).map_rel (hs.isClique hx's hy's hxy')

/-! ## The exact edge increment -/

section Counting

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [DecidableRel O.Dir]

/-- Pairs `(a,x)` which give an edge from the new copy of `a` to the old `x`. -/
def addedPairs : Finset (A × V) :=
  Finset.univ.filter fun p ↦ G.Adj p.1 p.2 ∧ (p.2 ∉ A ∨ O.Dir p.1 p.2)

@[simp] lemma mem_addedPairs (p : A × V) :
    p ∈ addedPairs G A O ↔
      G.Adj p.1 p.2 ∧ (p.2 ∉ A ∨ O.Dir p.1 p.2) := by
  simp [addedPairs]

/-- The base edges with at least one endpoint in `A`. -/
def incidentEdges : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ ∃ a ∈ A, a ∈ e

@[simp] lemma mem_incidentEdges (e : Sym2 V) :
    e ∈ incidentEdges G A ↔ e ∈ G.edgeFinset ∧ ∃ a ∈ A, a ∈ e := by
  simp [incidentEdges]

private def oldEmbedding : V ↪ DuplicateVertex A :=
  ⟨Sum.inl, Sum.inl_injective⟩

private def crossEdgeEmbedding : A × V ↪ Sym2 (DuplicateVertex A) where
  toFun p := s(Sum.inr p.1, Sum.inl p.2)
  inj' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h₁, h₂⟩ | ⟨h, -⟩
    · exact Prod.ext (Sum.inr.inj h₁) (Sum.inl.inj h₂)
    · exact False.elim <| Sum.inr_ne_inl h

private def oldEdges : Finset (Sym2 (DuplicateVertex A)) :=
  G.edgeFinset.map (oldEmbedding A).sym2Map

private def addedEdges : Finset (Sym2 (DuplicateVertex A)) :=
  (addedPairs G A O).map (crossEdgeEmbedding A)

private lemma mem_oldEdges_iff (e : Sym2 (DuplicateVertex A)) :
    e ∈ oldEdges G A ↔
      ∃ x y : V, G.Adj x y ∧ e = s(Sum.inl x, Sum.inl y) := by
  constructor
  · rw [oldEdges, Finset.mem_map]
    rintro ⟨e', he', rfl⟩
    induction e' using Sym2.inductionOn with
    | _ x y =>
        refine ⟨x, y, ?_, ?_⟩
        · simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he'
        · simp [oldEmbedding]
  · rintro ⟨x, y, hxy, rfl⟩
    rw [oldEdges, Finset.mem_map]
    refine ⟨s(x, y), ?_, ?_⟩
    · simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hxy
    · simp [oldEmbedding]

private lemma mem_addedEdges_iff (e : Sym2 (DuplicateVertex A)) :
    e ∈ addedEdges G A O ↔
      ∃ a : A, ∃ x : V,
        G.Adj a x ∧ (x ∉ A ∨ O.Dir a x) ∧ e = s(Sum.inr a, Sum.inl x) := by
  constructor
  · rw [addedEdges, Finset.mem_map]
    rintro ⟨⟨a, x⟩, hp, rfl⟩
    have hp' := (mem_addedPairs (G := G) (A := A) (O := O) (a, x)).mp hp
    exact ⟨a, x, hp'.1, hp'.2, rfl⟩
  · rintro ⟨a, x, hAdj, hcond, rfl⟩
    rw [addedEdges, Finset.mem_map]
    exact ⟨(a, x),
      (mem_addedPairs (G := G) (A := A) (O := O) (a, x)).mpr ⟨hAdj, hcond⟩,
      rfl⟩

private lemma edgeFinset_duplication :
    (duplication G A O).edgeFinset = oldEdges G A ∪ addedEdges G A O := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      rw [mem_oldEdges_iff, mem_addedEdges_iff]
      cases x with
      | inl x =>
          cases y with
          | inl y =>
              simp [duplication, Sym2.eq_iff, G.adj_comm]
              constructor
              · intro hxy
                exact ⟨x, y, hxy, Or.inl ⟨rfl, rfl⟩⟩
              · rintro ⟨u, v, huv, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
                · exact huv
                · exact huv.symm
          | inr y => simp [duplication, Sym2.eq_iff, G.adj_comm]
      | inr x =>
          cases y with
          | inl y => simp [duplication, Sym2.eq_iff, G.adj_comm]
          | inr y => simp [duplication, Sym2.eq_iff, G.adj_comm]

private lemma oldEdges_disjoint_addedEdges :
    Disjoint (oldEdges G A) (addedEdges G A O) := by
  rw [Finset.disjoint_left]
  intro e heold headd
  simp only [oldEdges, mem_map] at heold
  simp only [addedEdges, mem_map] at headd
  rcases heold with ⟨e', -, rfl⟩
  rcases headd with ⟨p, -, hp⟩
  induction e' using Sym2.inductionOn with
  | _ x y =>
      change s(Sum.inr p.1, Sum.inl p.2) = s(Sum.inl x, Sum.inl y) at hp
      rw [Sym2.eq_iff] at hp
      rcases hp with ⟨h, -⟩ | ⟨h, -⟩
      · exact Sum.inr_ne_inl h
      · exact Sum.inr_ne_inl h

private lemma card_oldEdges : (oldEdges G A).card = G.edgeFinset.card := by
  simp [oldEdges]

private lemma baseEdge_injOn_addedPairs :
    Set.InjOn (fun p : A × V ↦ s(p.1.1, p.2)) (addedPairs G A O) := by
  rintro ⟨a, x⟩ ha ⟨b, y⟩ hb h
  have ha := (mem_addedPairs (G := G) (A := A) (O := O) (a, x)).mp ha
  have hb := (mem_addedPairs (G := G) (A := A) (O := O) (b, y)).mp hb
  rw [Sym2.eq_iff] at h
  change (a.1 = b.1 ∧ x = y) ∨ (a.1 = y ∧ x = b.1) at h
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Prod.ext (Subtype.ext h₁) h₂
  · have hxA : x ∈ A := h₂ ▸ b.2
    have hyA : y ∈ A := h₁.symm ▸ a.2
    have hdax : O.Dir a x := ha.2.resolve_left (by simpa using hxA)
    have hdby : O.Dir b y := hb.2.resolve_left (by simpa using hyA)
    exact False.elim <| O.not_rev hdax <| by simpa [h₁, h₂] using hdby

private lemma image_baseEdge_addedPairs :
    (addedPairs G A O).image (fun p : A × V ↦ s(p.1.1, p.2)) = incidentEdges G A := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [Finset.mem_image, mem_addedPairs, mem_incidentEdges,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Sym2.eq_iff,
        Sym2.mem_iff]
      constructor
      · rintro ⟨⟨a, z⟩, ⟨haz, -⟩, h⟩
        rcases h with ⟨hax, hzy⟩ | ⟨hay, hzx⟩ <;> subst_vars
        · exact ⟨haz, a, a.2, Or.inl rfl⟩
        · exact ⟨haz.symm, a, a.2, Or.inr rfl⟩
      · rintro ⟨hxy, a, haA, ha⟩
        rcases ha with hax | hay
        · have hayAdj : G.Adj a y := by simpa [hax] using hxy
          by_cases hyA : y ∈ A
          · rcases O.resolve hayAdj haA hyA with hdir | hdir
            · exact ⟨(⟨a, haA⟩, y), ⟨hayAdj, Or.inr hdir⟩,
                Or.inl ⟨hax, rfl⟩⟩
            · exact ⟨(⟨y, hyA⟩, a), ⟨hayAdj.symm, Or.inr hdir⟩,
                Or.inr ⟨rfl, hax⟩⟩
          · exact ⟨(⟨a, haA⟩, y), ⟨hayAdj, Or.inl hyA⟩,
              Or.inl ⟨hax, rfl⟩⟩
        · have hxaAdj : G.Adj x a := by simpa [hay] using hxy
          by_cases hxA : x ∈ A
          · rcases O.resolve hxaAdj hxA haA with hdir | hdir
            · exact ⟨(⟨x, hxA⟩, a), ⟨hxaAdj, Or.inr hdir⟩,
                Or.inl ⟨rfl, hay⟩⟩
            · exact ⟨(⟨a, haA⟩, x), ⟨hxaAdj.symm, Or.inr hdir⟩,
                Or.inr ⟨hay, rfl⟩⟩
          · exact ⟨(⟨a, haA⟩, x), ⟨hxaAdj.symm, Or.inl hxA⟩,
              Or.inr ⟨hay, rfl⟩⟩

private lemma card_addedPairs_eq_incidentEdges :
    (addedPairs G A O).card = (incidentEdges G A).card := by
  rw [← image_baseEdge_addedPairs (G := G) (A := A) (O := O),
    Finset.card_image_iff.mpr (baseEdge_injOn_addedPairs (G := G) (A := A) (O := O))]

/-- The number of new edges is exactly the number of old edges incident to `A`. -/
theorem card_edgeFinset_duplication :
    (duplication G A O).edgeFinset.card =
      G.edgeFinset.card + (incidentEdges G A).card := by
  rw [edgeFinset_duplication (G := G) (A := A) (O := O),
    Finset.card_union_of_disjoint (oldEdges_disjoint_addedEdges (G := G) (A := A) (O := O)),
    card_oldEdges (G := G) (A := A)]
  simp only [addedEdges, card_map,
    card_addedPairs_eq_incidentEdges (G := G) (A := A) (O := O)]

end Counting

/-! ## Deterministic double counting over fixed-size subsets -/

section Averaging

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private lemma card_incident_subset_filter (K : ℕ) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) :
    ((Finset.univ.powersetCard K).filter fun B : Finset V ↦
      ∃ a ∈ B, a ∈ e).card =
      (Fintype.card V).choose K - (Fintype.card V - 2).choose K := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : G.Adj x y := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      let S := (Finset.univ : Finset V).powersetCard K
      have havoid :
          (S.filter fun B : Finset V ↦ ¬ ∃ a ∈ B, a ∈ s(x, y)) =
            ((Finset.univ : Finset V) \ {x, y}).powersetCard K := by
        ext B
        simp only [S, Finset.mem_filter, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨-, hcard⟩, hav⟩
          refine ⟨?_, hcard⟩
          intro z hz
          rw [Finset.mem_sdiff]
          refine ⟨Finset.mem_univ z, ?_⟩
          intro hzxy
          exact hav ⟨z, hz, by simpa [Sym2.mem_iff] using hzxy⟩
        · rintro ⟨hsub, hcard⟩
          refine ⟨⟨Finset.subset_univ B, hcard⟩, ?_⟩
          rintro ⟨z, hz, hzxy⟩
          have hznot : z ∉ ({x, y} : Finset V) := (Finset.mem_sdiff.mp (hsub hz)).2
          exact hznot (by simpa [Sym2.mem_iff] using hzxy)
      have hpartition :
          (S.filter fun B : Finset V ↦ ∃ a ∈ B, a ∈ s(x, y)) =
            S \ (S.filter fun B : Finset V ↦ ¬ ∃ a ∈ B, a ∈ s(x, y)) := by
        ext B
        simp only [Finset.mem_filter, Finset.mem_sdiff]
        constructor
        · rintro ⟨hBS, hP⟩
          exact ⟨hBS, fun hneg ↦ hneg.2 hP⟩
        · rintro ⟨hBS, hnot⟩
          refine ⟨hBS, ?_⟩
          by_contra hP
          exact hnot ⟨hBS, hP⟩
      rw [show (Finset.univ.powersetCard K) = S from rfl, hpartition,
        Finset.card_sdiff_of_subset (Finset.filter_subset _ _), havoid,
        Finset.card_powersetCard, Finset.card_powersetCard]
      have hpair : #({x, y} : Finset V) = 2 := by simp [hxy.ne]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ {x, y}),
        Finset.card_univ, hpair]

/-- Every edge is counted in exactly
`choose |V| K - choose (|V|-2) K` of the `K`-subsets. -/
theorem sum_card_incidentEdges_powersetCard (K : ℕ) :
    ∑ B ∈ (Finset.univ : Finset V).powersetCard K, (incidentEdges G B).card =
      G.edgeFinset.card *
        ((Fintype.card V).choose K - (Fintype.card V - 2).choose K) := by
  classical
  calc
    ∑ B ∈ (Finset.univ : Finset V).powersetCard K, (incidentEdges G B).card =
        ∑ B ∈ (Finset.univ : Finset V).powersetCard K,
          ∑ e ∈ G.edgeFinset, if ∃ a ∈ B, a ∈ e then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro B hB
            simp [incidentEdges]
    _ = ∑ e ∈ G.edgeFinset,
          ∑ B ∈ (Finset.univ : Finset V).powersetCard K,
            if ∃ a ∈ B, a ∈ e then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ e ∈ G.edgeFinset,
          ((Finset.univ.powersetCard K).filter fun B : Finset V ↦
            ∃ a ∈ B, a ∈ e).card := by
          apply Finset.sum_congr rfl
          intro e he
          simp
    _ = ∑ _e ∈ G.edgeFinset,
          ((Fintype.card V).choose K - (Fintype.card V - 2).choose K) := by
          apply Finset.sum_congr rfl
          intro e he
          exact card_incident_subset_filter (G := G) K he
    _ = G.edgeFinset.card *
          ((Fintype.card V).choose K - (Fintype.card V - 2).choose K) := by simp

/-- A deterministic averaging conclusion: some `K`-subset receives at least
the average number of incident edges, with denominators cleared. -/
theorem exists_subset_incidentEdges_average {K : ℕ} (hK : K ≤ Fintype.card V) :
    ∃ B : Finset V, B.card = K ∧
      G.edgeFinset.card *
          ((Fintype.card V).choose K - (Fintype.card V - 2).choose K) ≤
        (Fintype.card V).choose K * (incidentEdges G B).card := by
  classical
  let S := (Finset.univ : Finset V).powersetCard K
  have hS : S.Nonempty := by
    exact Finset.powersetCard_nonempty_of_le (by simpa [S] using hK)
  obtain ⟨B, hBS, hmax⟩ :=
    Finset.exists_max_image S (fun B ↦ (incidentEdges G B).card) hS
  refine ⟨B, Finset.mem_powersetCard_univ.mp hBS, ?_⟩
  have hsum :
      ∑ C ∈ S, (incidentEdges G C).card ≤ S.card * (incidentEdges G B).card := by
    calc
      ∑ C ∈ S, (incidentEdges G C).card ≤
          ∑ _C ∈ S, (incidentEdges G B).card :=
        Finset.sum_le_sum fun C hC ↦ hmax C hC
      _ = S.card * (incidentEdges G B).card := by simp
  rw [show S = (Finset.univ : Finset V).powersetCard K from rfl,
    sum_card_incidentEdges_powersetCard (G := G) K,
    Finset.card_powersetCard, Finset.card_univ] at hsum
  exact hsum

end Averaging

end FNV

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/Averaging.lean` -/

section
/-!
# The deterministic averaging step in the FNV duplication construction

This file rewrites the fixed-size-subset double count from `Duplication` in
the form used by Füredi--Naor--Verstraëte.  If a graph has `N` vertices and
`e` edges, some `K` vertices meet at least

`e * (K / N) * (2 - (K - 1) / (N - 1))`

edges.  The main theorem below is over the natural numbers with both
denominators cleared.  Thus it also covers the degenerate cases `N < 2`
without making any division convention part of the statement.
-/

open scoped BigOperators
open Finset

namespace FNV

/-! ## The binomial coefficient in the double count -/

private lemma choose_avoid_mul_denominator {N K : ℕ} (hN : 2 ≤ N) :
    (N - 2).choose K * (N * (N - 1)) =
      N.choose K * ((N - K) * (N - K - 1)) := by
  have h₁ := Nat.choose_mul_succ_eq (N - 2) K
  have h₂ := Nat.choose_mul_succ_eq (N - 1) K
  have hNm2 : N - 2 + 1 = N - 1 := by omega
  have hNm1 : N - 1 + 1 = N := by omega
  rw [hNm2] at h₁
  rw [hNm1] at h₂
  have hsub₁ : N - 1 - K = N - K - 1 := by omega
  rw [hsub₁] at h₁
  calc
    (N - 2).choose K * (N * (N - 1)) =
        ((N - 2).choose K * (N - 1)) * N := by ring
    _ = ((N - 1).choose K * (N - K - 1)) * N := by rw [h₁]
    _ = ((N - 1).choose K * N) * (N - K - 1) := by ring
    _ = (N.choose K * (N - K)) * (N - K - 1) := by rw [h₂]
    _ = N.choose K * ((N - K) * (N - K - 1)) := by ring

/-- The proportion of `K`-subsets meeting a fixed two-element edge,
expressed with all denominators cleared. -/
theorem choose_incident_mul_denominator {N K : ℕ} (hN : 2 ≤ N)
    (hK : K ≤ N) :
    (N.choose K - (N - 2).choose K) * (N * (N - 1)) =
      N.choose K * (K * (2 * N - K - 1)) := by
  have havoid := choose_avoid_mul_denominator (N := N) (K := K) hN
  have hnum :
      (N - K) * (N - K - 1) + K * (2 * N - K - 1) =
        N * (N - 1) := by
    by_cases hKN : K = N
    · subst K
      have hself : 2 * N - N - 1 = N - 1 := by omega
      rw [hself]
      simp
    · have hKlt : K < N := lt_of_le_of_ne hK hKN
      have hsplit₁ : N - K - 1 + K = N - 1 := by omega
      have hsplit₂ : 2 * N - K - 1 = (N - K) + (N - 1) := by omega
      rw [hsplit₂]
      calc
        (N - K) * (N - K - 1) + K * ((N - K) + (N - 1)) =
            (N - K) * ((N - K - 1) + K) + K * (N - 1) := by ring
        _ = (N - K) * (N - 1) + K * (N - 1) := by rw [hsplit₁]
        _ = ((N - K) + K) * (N - 1) := by ring
        _ = N * (N - 1) := by rw [Nat.sub_add_cancel hK]
  rw [Nat.sub_mul, havoid, ← Nat.mul_sub_left_distrib]
  congr 1
  omega

/-! ## A subset attaining the deterministic average -/

section Averaging

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Some `K`-set meets the FNV fraction of all edges.  This is the natural-number
form of
`e * K/N * (2 - (K-1)/(N-1)) ≤ incidentEdges`; its denominators are cleared.

The proof is deterministic: it sums over the finite set of all `K`-subsets
and selects one with maximal incident-edge count. -/
theorem exists_subset_incidentEdges_fnv {K : ℕ}
    (hK : K ≤ Fintype.card V) :
    ∃ A : Finset V, A.card = K ∧
      G.edgeFinset.card *
          (K * (2 * Fintype.card V - K - 1)) ≤
        (incidentEdges G A).card *
          (Fintype.card V * (Fintype.card V - 1)) := by
  classical
  let N := Fintype.card V
  obtain ⟨A, hAcard, haverage⟩ :=
    exists_subset_incidentEdges_average (G := G) hK
  refine ⟨A, hAcard, ?_⟩
  by_cases hN : 2 ≤ N
  · have hid := choose_incident_mul_denominator (N := N) (K := K) hN hK
    have hscaled := Nat.mul_le_mul_right (N * (N - 1)) haverage
    have hchoose : 0 < N.choose K := Nat.choose_pos hK
    dsimp [N] at hid hscaled hchoose ⊢
    rw [mul_assoc, hid] at hscaled
    apply le_of_mul_le_mul_left (a := (Fintype.card V).choose K) ?_ hchoose
    calc
      (Fintype.card V).choose K *
          (G.edgeFinset.card * (K * (2 * Fintype.card V - K - 1))) =
        G.edgeFinset.card *
          ((Fintype.card V).choose K * (K * (2 * Fintype.card V - K - 1))) := by
            ring
      _ ≤ (Fintype.card V).choose K * (incidentEdges G A).card *
          (Fintype.card V * (Fintype.card V - 1)) := hscaled
      _ = (Fintype.card V).choose K *
          ((incidentEdges G A).card *
            (Fintype.card V * (Fintype.card V - 1))) := by ring
  · have hcard : Fintype.card V ≤ 1 := by omega
    have hedge : G.edgeFinset.card = 0 := by
      have hedgeBound := G.card_edgeFinset_le_card_choose_two
      have hchooseTwo : (Fintype.card V).choose 2 = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      omega
    simp [hedge]

/-- The same conclusion in the literal rational form used in the paper. -/
theorem exists_subset_incidentEdges_fnv_rat {K : ℕ}
    (hN : 2 ≤ Fintype.card V) (hK : K ≤ Fintype.card V) :
    ∃ A : Finset V, A.card = K ∧
      (G.edgeFinset.card : ℚ) * (K : ℚ) / (Fintype.card V : ℚ) *
          (2 - ((K : ℚ) - 1) / ((Fintype.card V : ℚ) - 1)) ≤
        ((incidentEdges G A).card : ℚ) := by
  obtain ⟨A, hAcard, hbound⟩ := exists_subset_incidentEdges_fnv (G := G) hK
  refine ⟨A, hAcard, ?_⟩
  have hcastNum :
      (((2 * Fintype.card V - K - 1 : ℕ) : ℚ)) =
        2 * (Fintype.card V : ℚ) - (K : ℚ) - 1 := by
    calc
      (((2 * Fintype.card V - K - 1 : ℕ) : ℚ)) =
          ((2 * Fintype.card V - K : ℕ) : ℚ) - 1 := by
            exact Nat.cast_sub (by omega : 1 ≤ 2 * Fintype.card V - K)
      _ = ((2 * Fintype.card V : ℕ) : ℚ) - (K : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : K ≤ 2 * Fintype.card V)]
      _ = 2 * (Fintype.card V : ℚ) - (K : ℚ) - 1 := by norm_num
  have hboundQ :
      (G.edgeFinset.card : ℚ) *
          ((K : ℚ) * (((2 * Fintype.card V - K - 1 : ℕ) : ℚ))) ≤
        ((incidentEdges G A).card : ℚ) *
          ((Fintype.card V : ℚ) * (((Fintype.card V - 1 : ℕ) : ℚ))) := by
    exact_mod_cast hbound
  rw [hcastNum, Nat.cast_sub (by omega : 1 ≤ Fintype.card V)] at hboundQ
  norm_num at hboundQ
  have hNQ : (0 : ℚ) < (Fintype.card V : ℚ) := by positivity
  have hNsubQ : (0 : ℚ) < (Fintype.card V : ℚ) - 1 := by
    apply sub_pos.mpr
    exact_mod_cast (show 1 < Fintype.card V by omega)
  rw [show
      (G.edgeFinset.card : ℚ) * (K : ℚ) / (Fintype.card V : ℚ) *
          (2 - ((K : ℚ) - 1) / ((Fintype.card V : ℚ) - 1)) =
        ((G.edgeFinset.card : ℚ) * (K : ℚ) *
            (2 * (Fintype.card V : ℚ) - (K : ℚ) - 1)) /
          ((Fintype.card V : ℚ) * ((Fintype.card V : ℚ) - 1)) by
        field_simp [ne_of_gt hNQ, ne_of_gt hNsubQ]
        ring]
  exact (div_le_iff₀ (mul_pos hNQ hNsubQ)).2 (by nlinarith)

/-! ## Transfer to the exact duplication edge count -/

end Averaging

end FNV

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/Matching.lean` -/

section
/-!
# Matchings between two three-element fibres

A matching is represented by its finite set of edges.  The defining predicate
says directly that the sets of edges over every left and right vertex have
cardinality at most one.
-/

/-- Either fibre of the bipartite graph. -/
abbrev Fibre := Fin 3

/-- An edge joins a point of the left fibre to a point of the right fibre. -/
abbrev Edge := Fibre × Fibre

/-- The edges in `s` incident to the left vertex `i`. -/
def leftEdges (s : Finset Edge) (i : Fibre) : Finset Edge :=
  s.filter fun e ↦ e.1 = i

/-- The edges in `s` incident to the right vertex `j`. -/
def rightEdges (s : Finset Edge) (j : Fibre) : Finset Edge :=
  s.filter fun e ↦ e.2 = j

/-- A computable check of the three left-degree bounds. -/
private def leftCode (s : Finset Edge) : Bool :=
  decide ((leftEdges s 0).card ≤ 1) &&
    decide ((leftEdges s 1).card ≤ 1) &&
      decide ((leftEdges s 2).card ≤ 1)

/-- A computable check of the three right-degree bounds. -/
private def rightCode (s : Finset Edge) : Bool :=
  decide ((rightEdges s 0).card ≤ 1) &&
    decide ((rightEdges s 1).card ≤ 1) &&
      decide ((rightEdges s 2).card ≤ 1)

/-- Both sides of an edge set have degree at most one. -/
def IsMatching (s : Finset Edge) : Prop :=
  leftCode s && rightCode s = true

instance (s : Finset Edge) : Decidable (IsMatching s) := by
  unfold IsMatching
  exact inferInstance

/-- Matchings between two labelled three-element fibres. -/
def Matching := {s : Finset Edge // IsMatching s}

deriving instance DecidableEq for Matching
deriving instance Fintype for Matching

namespace Matching

/-- The edge set underlying a matching. -/
def edges (M : Matching) : Finset Edge :=
  M.1

/-- Construct a matching from an edge set satisfying the two degree bounds. -/
def ofEdges (s : Finset Edge) (hs : IsMatching s) : Matching :=
  ⟨s, hs⟩

@[simp] theorem edges_ofEdges (s : Finset Edge) (hs : IsMatching s) :
    (ofEdges s hs).edges = s := rfl

theorem isMatching (M : Matching) : IsMatching M.edges :=
  M.2

/-- The incidence relation associated to a matching. -/
def Rel (M : Matching) (i j : Fibre) : Prop :=
  (i, j) ∈ M.edges

instance (M : Matching) : DecidableRel M.Rel := fun i j ↦ by
  unfold Rel edges
  exact inferInstance

@[simp] theorem rel_ofEdges (s : Finset Edge) (hs : IsMatching s) (i j : Fibre) :
    (ofEdges s hs).Rel i j ↔ (i, j) ∈ s := Iff.rfl

/-- The underlying edge set determines a matching. -/
theorem edges_injective : Function.Injective edges := by
  intro M N h
  exact Subtype.ext h

/-- Extensionality in terms of the incidence relation. -/
@[ext] theorem ext {M N : Matching}
    (h : ∀ i j, M.Rel i j ↔ N.Rel i j) : M = N := by
  apply edges_injective
  ext e
  exact h e.1 e.2

/-- The edge-degree bound at a left vertex. -/
theorem left_degree_le_one (M : Matching) (i : Fibre) :
    (leftEdges M.edges i).card ≤ 1 := by
  have h := Bool.and_eq_true_iff.mp M.isMatching |>.1
  simp only [leftCode, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  fin_cases i
  · simpa using h.1.1
  · simpa using h.1.2
  · simpa using h.2

/-- The edge-degree bound at a right vertex. -/
theorem right_degree_le_one (M : Matching) (j : Fibre) :
    (rightEdges M.edges j).card ≤ 1 := by
  have h := Bool.and_eq_true_iff.mp M.isMatching |>.2
  simp only [rightCode, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  fin_cases j
  · simpa using h.1.1
  · simpa using h.1.2
  · simpa using h.2

/-- A left vertex has at most one partner. -/
theorem left_unique (M : Matching) {i j j' : Fibre}
    (h : M.Rel i j) (h' : M.Rel i j') : j = j' := by
  have hp : (i, j) = (i, j') :=
    Finset.card_le_one_iff.mp (M.left_degree_le_one i)
      (by simpa [leftEdges, Rel] using h)
      (by simpa [leftEdges, Rel] using h')
  exact congrArg Prod.snd hp

/-- A right vertex has at most one partner. -/
theorem right_unique (M : Matching) {i i' j : Fibre}
    (h : M.Rel i j) (h' : M.Rel i' j) : i = i' := by
  have hp : (i, j) = (i', j) :=
    Finset.card_le_one_iff.mp (M.right_degree_le_one j)
      (by simpa [rightEdges, Rel] using h)
      (by simpa [rightEdges, Rel] using h')
  exact congrArg Prod.fst hp

/-- The possible right partners of `i`. -/
def rights (M : Matching) (i : Fibre) : Finset Fibre :=
  (leftEdges M.edges i).image Prod.snd

/-- The possible left partners of `j`. -/
def lefts (M : Matching) (j : Fibre) : Finset Fibre :=
  (rightEdges M.edges j).image Prod.fst

@[simp] theorem mem_rights (M : Matching) (i j : Fibre) :
    j ∈ M.rights i ↔ M.Rel i j := by
  simp [rights, leftEdges, Rel]

@[simp] theorem mem_lefts (M : Matching) (i j : Fibre) :
    i ∈ M.lefts j ↔ M.Rel i j := by
  simp [lefts, rightEdges, Rel]

end Matching

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/Blowup.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Three-fold matching blowups

This file isolates the elementary graph-theoretic part of the construction used
for Erdős Problem 59.  Every vertex of a base graph is replaced by a fibre of
three vertices, and every base edge is replaced by an arbitrary matching
between the corresponding fibres.

The projection of a simple six-cycle in the blowup is a closed walk of length
six in the base.  It cannot immediately backtrack: two successive matching
edges over the same base edge would return to the same vertex in the fibre.
Consequently, a repeated vertex in the projected walk gives a triangle; if
there is no repeated vertex, the projected walk is a six-cycle.
-/

/-- Independently choose one of the 34 matchings for each unordered base
edge. -/
abbrev MatchingChoice {V : Type*} (G : SimpleGraph V) := G.edgeSet → Matching

/-- The edge of `G` certified by an adjacency proof. -/
def certifiedEdge {V : Type*} {G : SimpleGraph V} {u v : V} (h : G.Adj u v) :
    G.edgeSet :=
  ⟨s(u, v), h⟩

/-- Interpret the matching on an unordered edge from the orientation `u → v`.
The linear order is used only to decide which endpoint is the left fibre. -/
def matchingChoiceRel {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    (C : MatchingChoice G) {u v : V} (h : G.Adj u v) (i j : Fibre) : Prop :=
  if u < v then (C (certifiedEdge h)).Rel i j
  else (C (certifiedEdge h)).Rel j i

lemma matchingChoiceRel_symmetric {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoice G) {u v : V} (h : G.Adj u v)
    (i j : Fibre) :
    matchingChoiceRel C h i j ↔ matchingChoiceRel C h.symm j i := by
  by_cases huv : u < v
  · have hvu : ¬v < u := not_lt_of_ge huv.le
    have he : certifiedEdge h.symm = certifiedEdge h := by
      apply Subtype.ext
      exact Sym2.eq_swap
    simp [matchingChoiceRel, huv, hvu, he]
  · have hvu : v < u := lt_of_le_of_ne (le_of_not_gt huv) h.ne.symm
    have he : certifiedEdge h.symm = certifiedEdge h := by
      apply Subtype.ext
      exact Sym2.eq_swap
    simp [matchingChoiceRel, huv, hvu, he]

/-- The three-fold matching blowup specified by `C`. -/
def matchingBlowup {V : Type*} [LinearOrder V]
    (G : SimpleGraph V) (C : MatchingChoice G) : SimpleGraph (V × Fibre) where
  Adj x y := ∃ h : G.Adj x.1 y.1, matchingChoiceRel C h x.2 y.2
  symm := ⟨by
    rintro x y ⟨h, hC⟩
    exact ⟨h.symm, (matchingChoiceRel_symmetric C h _ _).mp hC⟩⟩
  loopless := ⟨by
    rintro x ⟨h, -⟩
    exact h.ne rfl⟩

@[simp] lemma matchingBlowup_adj {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    (C : MatchingChoice G) (x y : V × Fibre) :
    (matchingBlowup G C).Adj x y ↔
      ∃ h : G.Adj x.1 y.1, matchingChoiceRel C h x.2 y.2 :=
  Iff.rfl

/-- The first projection is a graph homomorphism from a matching blowup to its
base graph. -/
def matchingBlowupProjection {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    (C : MatchingChoice G) : matchingBlowup G C →g G where
  toFun := Prod.fst
  map_rel' := by
    rintro x y ⟨h, -⟩
    exact h

@[simp] lemma matchingBlowupProjection_apply {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoice G) (x : V × Fibre) :
    matchingBlowupProjection C x = x.1 :=
  rfl

/-- Triangle-freeness in an edge-oriented form convenient for projected
walks. -/
def TriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬G.Adj c a

/-- A graph is `C₆`-free if no six distinct vertices occur consecutively
around a closed six-edge walk. -/
def C6Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c d e f : V⦄,
    G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d e → G.Adj e f → G.Adj f a →
    ¬[a, b, c, d, e, f].Nodup

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/CycleAdapters.lean` -/

section
/-!
# Cycle and relabelling adapters for Erdős Problem 59

The construction files use several convenient pointwise presentations of
triangles, quadrilaterals, and hexagons.  This file identifies all of them with
Mathlib's standard forbidden-subgraph predicates.  It also packages transport
of graphs, free graphs, and edge counts across a finite relabelling.
-/

namespace CycleAdapters

open SimpleGraph

/-- The cyclic successor on `Fin n`.  The input itself witnesses that `n` is
positive, so this definition needs no extra positivity hypothesis. -/
def cyclicSucc {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- A simple `n`-cycle presented by cyclically adjacent indexed vertices. -/
def IndexedCycle {V : Type*} (n : ℕ) (G : SimpleGraph V) (v : Fin n → V) : Prop :=
  Function.Injective v ∧ ∀ i, G.Adj (v i) (v (cyclicSucc i))

private theorem exists_indexedCycle_iff_isContained_of_adj
    {V : Type*} {n : ℕ} (G : SimpleGraph V)
    (hadj : ∀ i j : Fin n,
      (SimpleGraph.cycleGraph n).Adj i j ↔
        j = cyclicSucc i ∨ i = cyclicSucc j) :
    (∃ v : Fin n → V, IndexedCycle n G v) ↔
      SimpleGraph.cycleGraph n ⊑ G := by
  constructor
  · rintro ⟨v, hv⟩
    rw [IndexedCycle] at hv
    rcases hv with ⟨hinj, hcycle⟩
    refine ⟨{
      toHom := {
        toFun := v
        map_rel' := ?_ }
      injective' := hinj }⟩
    intro i j hij
    rcases (hadj i j).mp hij with h | h
    · subst j
      exact hcycle i
    · subst i
      exact (hcycle j).symm
  · rintro ⟨f⟩
    refine ⟨f, ?_⟩
    rw [IndexedCycle]
    exact ⟨f.injective, fun i ↦
      f.toHom.map_rel ((hadj i (cyclicSucc i)).mpr (Or.inl rfl))⟩

private theorem cycleGraph_four_adj_succ_iff (i j : Fin 4) :
    (SimpleGraph.cycleGraph 4).Adj i j ↔
      j = cyclicSucc i ∨ i = cyclicSucc j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem cycleGraph_six_adj_succ_iff (i j : Fin 6) :
    (SimpleGraph.cycleGraph 6).Adj i j ↔
      j = cyclicSucc i ∨ i = cyclicSucc j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem cyclicSucc_fin_four (i : Fin 4) : cyclicSucc i = i + 1 := by
  fin_cases i <;> decide

private theorem cyclicSucc_fin_six (i : Fin 6) : cyclicSucc i = i + 1 := by
  fin_cases i <;> decide

/-- Indexed quadrilaterals are exactly copies of the standard quadrilateral. -/
theorem exists_indexedCycle_four_iff_isContained {V : Type*}
    (G : SimpleGraph V) :
    (∃ v : Fin 4 → V, IndexedCycle 4 G v) ↔
      SimpleGraph.cycleGraph 4 ⊑ G :=
  exists_indexedCycle_iff_isContained_of_adj G cycleGraph_four_adj_succ_iff

/-- Indexed hexagons are exactly copies of the standard hexagon. -/
theorem exists_indexedCycle_six_iff_isContained {V : Type*}
    (G : SimpleGraph V) :
    (∃ v : Fin 6 → V, IndexedCycle 6 G v) ↔
      SimpleGraph.cycleGraph 6 ⊑ G :=
  exists_indexedCycle_iff_isContained_of_adj G cycleGraph_six_adj_succ_iff

/-- The indexed and closed-walk presentations of a quadrilateral agree. -/
theorem exists_indexedCycle_four_iff_exists_isCycle_walk {V : Type*}
    (G : SimpleGraph V) :
    (∃ v : Fin 4 → V, IndexedCycle 4 G v) ↔
      ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = 4 :=
  (exists_indexedCycle_four_iff_isContained G).trans
    (SimpleGraph.cycleGraph_isContained_iff (by omega))

/-- The indexed and closed-walk presentations of a hexagon agree. -/
theorem exists_indexedCycle_six_iff_exists_isCycle_walk {V : Type*}
    (G : SimpleGraph V) :
    (∃ v : Fin 6 → V, IndexedCycle 6 G v) ↔
      ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = 6 :=
  (exists_indexedCycle_six_iff_isContained G).trans
    (SimpleGraph.cycleGraph_isContained_iff (by omega))

/-- Mathlib quadrilateral-freeness is the absence of indexed quadrilaterals. -/
theorem cycleGraph_four_free_iff {V : Type*} (G : SimpleGraph V) :
    (SimpleGraph.cycleGraph 4).Free G ↔
      ∀ v : Fin 4 → V, ¬IndexedCycle 4 G v := by
  rw [SimpleGraph.Free, SimpleGraph.cycleGraph_isContained_iff (by omega),
    ← exists_indexedCycle_four_iff_exists_isCycle_walk]
  simp only [not_exists]

/-- Mathlib hexagon-freeness is the absence of indexed hexagons. -/
theorem cycleGraph_six_free_iff {V : Type*} (G : SimpleGraph V) :
    (SimpleGraph.cycleGraph 6).Free G ↔
      ∀ v : Fin 6 → V, ¬IndexedCycle 6 G v := by
  rw [SimpleGraph.Free, SimpleGraph.cycleGraph_isContained_iff (by omega),
    ← exists_indexedCycle_six_iff_exists_isCycle_walk]
  simp only [not_exists]

private theorem affine_exists_c4_iff_indexed {V : Type*} (G : SimpleGraph V) :
    (∃ v₀ v₁ v₂ v₃, AffinePolarity.IsC4 G v₀ v₁ v₂ v₃) ↔
      ∃ v : Fin 4 → V, IndexedCycle 4 G v := by
  constructor
  · rintro ⟨v₀, v₁, v₂, v₃, h₀₁, h₀₂, h₀₃, h₁₂, h₁₃, h₂₃,
      e₀₁, e₁₂, e₂₃, e₃₀⟩
    refine ⟨![v₀, v₁, v₂, v₃], ?_⟩
    rw [IndexedCycle]
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i
      fin_cases i
      · simpa [cyclicSucc] using e₀₁
      · simpa [cyclicSucc] using e₁₂
      · simpa [cyclicSucc] using e₂₃
      · simpa [cyclicSucc] using e₃₀
  · rintro ⟨v, hv⟩
    rw [IndexedCycle] at hv
    rcases hv with ⟨hinj, hadj⟩
    refine ⟨v 0, v 1, v 2, v 3,
      hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide),
      hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide),
      ?_, ?_, ?_, ?_⟩
    · simpa [cyclicSucc] using hadj 0
    · simpa [cyclicSucc] using hadj 1
    · simpa [cyclicSucc] using hadj 2
    · simpa [cyclicSucc] using hadj 3

/-- The affine-polarity explicit quadrilateral exclusion is Mathlib `C₄`-freeness. -/
theorem affine_no_c4_iff_cycleGraph_four_free {V : Type*} (G : SimpleGraph V) :
    (¬ ∃ v₀ v₁ v₂ v₃, AffinePolarity.IsC4 G v₀ v₁ v₂ v₃) ↔
      (SimpleGraph.cycleGraph 4).Free G := by
  rw [cycleGraph_four_free_iff, ← not_exists, affine_exists_c4_iff_indexed]

/-- The duplication file's indexed quadrilateral predicate is Mathlib `C₄`-freeness. -/
theorem duplication_c4Free_iff_cycleGraph_four_free {V : Type*}
    (G : SimpleGraph V) :
    FNV.C4Free G ↔ (SimpleGraph.cycleGraph 4).Free G := by
  rw [cycleGraph_four_free_iff]
  constructor
  · intro h v hv
    apply h v
    rcases hv with ⟨hinj, hadj⟩
    exact ⟨hinj, fun i ↦ by simpa only [cyclicSucc_fin_four] using hadj i⟩
  · intro h v hv
    apply h v
    rcases hv with ⟨hinj, hadj⟩
    rw [IndexedCycle]
    exact ⟨hinj, fun i ↦ by simpa only [cyclicSucc_fin_four] using hadj i⟩

/-- The duplication file's indexed hexagon predicate is Mathlib `C₆`-freeness. -/
theorem duplication_c6Free_iff_cycleGraph_six_free {V : Type*}
    (G : SimpleGraph V) :
    FNV.C6Free G ↔ (SimpleGraph.cycleGraph 6).Free G := by
  rw [cycleGraph_six_free_iff]
  constructor
  · intro h v hv
    apply h v
    rcases hv with ⟨hinj, hadj⟩
    exact ⟨hinj, fun i ↦ by simpa only [cyclicSucc_fin_six] using hadj i⟩
  · intro h v hv
    apply h v
    rcases hv with ⟨hinj, hadj⟩
    rw [IndexedCycle]
    exact ⟨hinj, fun i ↦ by simpa only [cyclicSucc_fin_six] using hadj i⟩

section Relabelling

variable {V W : Type*} [Fintype V]

/-- The canonical equivalence from a finite vertex type to its labelled `Fin` type. -/
noncomputable def vertexEquivFin : V ≃ Fin (Fintype.card V) :=
  Fintype.equivFin V

/-- Relabel a graph on a finite type by `Fin (card V)`. -/
noncomputable def relabelGraph (G : SimpleGraph V) :
    SimpleGraph (Fin (Fintype.card V)) :=
  (vertexEquivFin (V := V)).simpleGraph G

/-- Relabelling is an equivalence on the full type of graphs. -/
noncomputable def graphEquivFin :
    SimpleGraph V ≃ SimpleGraph (Fin (Fintype.card V)) :=
  (vertexEquivFin (V := V)).simpleGraph

@[simp] theorem graphEquivFin_apply (G : SimpleGraph V) :
    graphEquivFin G = relabelGraph G :=
  rfl

end Relabelling

section ThreeFoldRelabelling

/-- The standard three-fold fibre labelling, ordered with fibre coordinate
varying fastest. -/
def finThreeEquiv (n : ℕ) : Fin n × Fin 3 ≃ Fin (3 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 3))

/-- Relabel a graph on `Fin n × Fin 3` by `Fin (3 * n)`. -/
def relabelFinThreeGraph {n : ℕ} (G : SimpleGraph (Fin n × Fin 3)) :
    SimpleGraph (Fin (3 * n)) :=
  (finThreeEquiv n).simpleGraph G

/-- Three-fold fibre relabelling is an equivalence on graphs. -/
def graphFinThreeEquiv (n : ℕ) :
    SimpleGraph (Fin n × Fin 3) ≃ SimpleGraph (Fin (3 * n)) :=
  (finThreeEquiv n).simpleGraph

@[simp] theorem graphFinThreeEquiv_apply {n : ℕ}
    (G : SimpleGraph (Fin n × Fin 3)) :
    graphFinThreeEquiv n G = relabelFinThreeGraph G :=
  rfl

end ThreeFoldRelabelling

end CycleAdapters

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/DensityAsymptotics.lean` -/

section
/-!
# The density calculation in the Füredi--Naor--Verstraëte construction

This file isolates the real-arithmetic part of the affine lower construction.
The graph-theoretic input is deliberately represented by a hypothesis in the
last theorem.  Thus none of the results below assert the existence of the
finite-geometric graph before that input has been supplied.

For `q = 2^(2a+1)`, the affine graph has `N = q^3` vertices and
`(q^4-q^2)/2` edges.  Cloning a set of
`K = floor ((sqrt 5 - 2) N)` vertices gives, by averaging, the edge lower
bound recorded in `fnvLower`.  We prove directly (with rational bounds, rather
than asymptotic notation) that this lower bound is greater than
`(2669/5000) n^(4/3)` once `a ≥ 3`.
-/

/-- The prime-power parameter used by the affine FNV construction. -/
def fnvQ (a : ℕ) : ℕ := 2 ^ (2 * a + 1)

/-- The number of vertices in the affine base graph. -/
def fnvN (a : ℕ) : ℕ := fnvQ a ^ 3

/-- The number of vertices cloned in the FNV construction. -/
noncomputable def fnvK (a : ℕ) : ℕ :=
  Nat.floor ((Real.sqrt 5 - 2) * fnvN a)

/-- The number of vertices after cloning. -/
noncomputable def fnvVertices (a : ℕ) : ℕ := fnvN a + fnvK a

/-- The exact number of edges in the affine base graph, viewed in `ℝ`. -/
noncomputable def fnvBaseEdges (a : ℕ) : ℝ :=
  ((fnvQ a : ℝ) ^ 4 - (fnvQ a : ℝ) ^ 2) / 2

/--
The lower bound delivered by the averaging argument.  An old edge acquires
an extra copy with probability
`(K/N) * (2 - (K-1)/(N-1))`.
-/
noncomputable def fnvLower (a : ℕ) : ℝ :=
  fnvBaseEdges a *
    (1 + (fnvK a : ℝ) / fnvN a *
      (2 - ((fnvK a : ℝ) - 1) / ((fnvN a : ℝ) - 1)))

private lemma sqrt_five_lower :
    (2360679 / 10000000 : ℝ) < Real.sqrt 5 - 2 := by
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by norm_num
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith [hs]

private lemma sqrt_five_upper :
    Real.sqrt 5 - 2 < (236068 / 1000000 : ℝ) := by
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by norm_num
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith [hs]

private lemma rpow_four_thirds_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 4 ≤ y ^ 3) : x ^ (4 / 3 : ℝ) ≤ y := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hy
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num
  simpa [Real.rpow_natCast] using h

private lemma fnvQ_ge_128 {a : ℕ} (ha : 3 ≤ a) : 128 ≤ fnvQ a := by
  rw [fnvQ, show 128 = 2 ^ 7 by norm_num]
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).2 (by omega)

private lemma fnvN_ge_threshold {a : ℕ} (ha : 3 ≤ a) : 2097152 ≤ fnvN a := by
  rw [fnvN]
  exact Nat.pow_le_pow_left (fnvQ_ge_128 ha) 3

private lemma fnvK_ratio_lower {a : ℕ} (ha : 3 ≤ a) :
    (236067 / 1000000 : ℝ) ≤ (fnvK a : ℝ) / fnvN a := by
  have hNnat := fnvN_ge_threshold ha
  have hN : (2097152 : ℝ) ≤ fnvN a := by exact_mod_cast hNnat
  have hNpos : (0 : ℝ) < fnvN a := by exact_mod_cast (show 0 < fnvN a by
    simp [fnvN, fnvQ])
  have hfloor : (Real.sqrt 5 - 2) * (fnvN a : ℝ) < (fnvK a : ℝ) + 1 := by
    exact Nat.lt_floor_add_one _
  have hs := sqrt_five_lower
  rw [le_div_iff₀ hNpos]
  nlinarith [mul_pos (sub_pos.mpr hs) hNpos]

private lemma fnvK_ratio_upper (a : ℕ) :
    (fnvK a : ℝ) / fnvN a ≤ (236068 / 1000000 : ℝ) := by
  have hNpos : (0 : ℝ) < fnvN a := by
    exact_mod_cast (show 0 < fnvN a by simp [fnvN, fnvQ])
  have hs : 0 ≤ Real.sqrt 5 - 2 := by
    have hs2 : (2 : ℝ) ≤ Real.sqrt 5 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]
    linarith
  have hfloor : (fnvK a : ℝ) ≤
      (Real.sqrt 5 - 2) * (fnvN a : ℝ) := by
    exact Nat.floor_le (mul_nonneg hs (by positivity))
  rw [div_le_iff₀ hNpos]
  nlinarith [sqrt_five_upper, mul_pos hNpos (sub_pos.mpr sqrt_five_upper)]

private lemma fnvK_le_N (a : ℕ) : fnvK a ≤ fnvN a := by
  have hNpos : (0 : ℝ) < fnvN a := by
    exact_mod_cast (show 0 < fnvN a by simp [fnvN, fnvQ])
  have hu := fnvK_ratio_upper a
  rw [div_le_iff₀ hNpos] at hu
  exact_mod_cast (show (fnvK a : ℝ) ≤ fnvN a by nlinarith)

private lemma fnv_sampling_factor_lower {a : ℕ} (ha : 3 ≤ a) :
    (1 + (236067 / 1000000 : ℝ) * (2 - 236068 / 1000000)) ≤
      1 + (fnvK a : ℝ) / fnvN a *
        (2 - ((fnvK a : ℝ) - 1) / ((fnvN a : ℝ) - 1)) := by
  have hNnat := fnvN_ge_threshold ha
  have hN : (1 : ℝ) < fnvN a := by exact_mod_cast (show 1 < fnvN a by omega)
  have hKle : (fnvK a : ℝ) ≤ fnvN a := by exact_mod_cast fnvK_le_N a
  have hratio : ((fnvK a : ℝ) - 1) / ((fnvN a : ℝ) - 1) ≤
      (fnvK a : ℝ) / fnvN a := by
    rw [div_le_div_iff₀ (sub_pos.mpr hN) (by positivity : (0 : ℝ) < fnvN a)]
    nlinarith
  have hlo := fnvK_ratio_lower ha
  have hup := fnvK_ratio_upper a
  have hright : (0 : ℝ) ≤
      2 - ((fnvK a : ℝ) - 1) / ((fnvN a : ℝ) - 1) := by
    nlinarith
  have hconst : (0 : ℝ) ≤ 2 - 236068 / 1000000 := by norm_num
  nlinarith [mul_le_mul hlo (by nlinarith :
      (2 - 236068 / 1000000 : ℝ) ≤
        2 - ((fnvK a : ℝ) - 1) / ((fnvN a : ℝ) - 1)) hconst
      (by positivity : (0 : ℝ) ≤ (fnvK a : ℝ) / fnvN a)]

private lemma fnv_base_edges_lower {a : ℕ} (ha : 3 ≤ a) :
    ((1 - 1 / (128 : ℝ) ^ 2) / 2) * (fnvQ a : ℝ) ^ 4 ≤
      fnvBaseEdges a := by
  have hq : (128 : ℝ) ≤ fnvQ a := by exact_mod_cast fnvQ_ge_128 ha
  have hq0 : (0 : ℝ) ≤ fnvQ a := by positivity
  rw [fnvBaseEdges]
  have hq2 : (128 : ℝ) ^ 2 ≤ (fnvQ a : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hq 2
  nlinarith [sq_nonneg ((fnvQ a : ℝ) ^ 2 - 128 ^ 2)]

private lemma fnv_vertices_rpow_upper (a : ℕ) :
    (fnvVertices a : ℝ) ^ (4 / 3 : ℝ) ≤
      (132655 / 100000 : ℝ) * (fnvQ a : ℝ) ^ 4 := by
  let Q : ℝ := fnvQ a
  let x : ℝ := fnvVertices a
  let y : ℝ := (132655 / 100000 : ℝ) * Q ^ 4
  have hQ : 0 ≤ Q := by positivity
  have hNpos : (0 : ℝ) < fnvN a := by
    exact_mod_cast (show 0 < fnvN a by simp [fnvN, fnvQ])
  have hK := fnvK_ratio_upper a
  rw [div_le_iff₀ hNpos] at hK
  have hx : x ≤ (1236068 / 1000000 : ℝ) * Q ^ 3 := by
    dsimp [x, Q, fnvVertices]
    push_cast
    rw [fnvN, Nat.cast_pow] at hK ⊢
    nlinarith
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  apply rpow_four_thirds_le hx0 hy0
  calc
    x ^ 4 ≤ ((1236068 / 1000000 : ℝ) * Q ^ 3) ^ 4 :=
      pow_le_pow_left₀ hx0 hx 4
    _ = (1236068 / 1000000 : ℝ) ^ 4 * Q ^ 12 := by ring
    _ ≤ (132655 / 100000 : ℝ) ^ 3 * Q ^ 12 := by
      gcongr
      norm_num
    _ = y ^ 3 := by dsimp [y]; ring

/-- The full FNV arithmetic estimate, including the floor and affine error. -/
theorem fnvLower_gt {a : ℕ} (ha : 3 ≤ a) :
    fnvLower a > (2669 / 5000 : ℝ) *
      (fnvVertices a : ℝ) ^ (4 / 3 : ℝ) := by
  have hb := fnv_base_edges_lower ha
  have hf := fnv_sampling_factor_lower ha
  have hp := fnv_vertices_rpow_upper a
  have hbase : 0 ≤ fnvBaseEdges a := by
    rw [fnvBaseEdges]
    have hq : (1 : ℝ) ≤ fnvQ a := by
      exact_mod_cast (show 1 ≤ fnvQ a by
        exact Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (by norm_num)))
    have hpow : (fnvQ a : ℝ) ^ 2 ≤ (fnvQ a : ℝ) ^ 4 :=
      pow_le_pow_right₀ hq (by omega)
    linarith
  have hfactor : 0 ≤
      1 + (fnvK a : ℝ) / fnvN a *
        (2 - ((fnvK a : ℝ) - 1) / ((fnvN a : ℝ) - 1)) := by
    exact hf.trans' (by norm_num)
  have hQpos : (0 : ℝ) < (fnvQ a : ℝ) ^ 4 := by
    positivity [show 0 < fnvQ a by simp [fnvQ]]
  have hc :
      ((1 - 1 / (128 : ℝ) ^ 2) / 2) *
          (1 + (236067 / 1000000 : ℝ) * (2 - 236068 / 1000000)) >
        (2669 / 5000 : ℝ) * (132655 / 100000) := by norm_num
  rw [fnvLower]
  calc
    fnvBaseEdges a *
          (1 + (fnvK a : ℝ) / fnvN a *
            (2 - ((fnvK a : ℝ) - 1) / ((fnvN a : ℝ) - 1)))
        ≥ (((1 - 1 / (128 : ℝ) ^ 2) / 2) * (fnvQ a : ℝ) ^ 4) *
          (1 + (236067 / 1000000 : ℝ) * (2 - 236068 / 1000000)) := by
            exact mul_le_mul hb hf (by norm_num) hbase
    _ = (((1 - 1 / (128 : ℝ) ^ 2) / 2) *
          (1 + (236067 / 1000000 : ℝ) * (2 - 236068 / 1000000))) *
          (fnvQ a : ℝ) ^ 4 := by ring
    _ > ((2669 / 5000 : ℝ) * (132655 / 100000)) *
          (fnvQ a : ℝ) ^ 4 := mul_lt_mul_of_pos_right hc hQpos
    _ ≥ (2669 / 5000 : ℝ) *
          (fnvVertices a : ℝ) ^ (4 / 3 : ℝ) := by
            nlinarith

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/LowerConstruction.lean` -/

section
/-!
# The dense triangle- and hexagon-free FNV graphs

This file joins the affine polarity graph, the deterministic fixed-size
averaging lemma, and the FNV duplication construction.  Its final theorem is
the unconditional lower construction used in the negative solution of
Erdős problem 59: at unbounded orders there is a labelled triangle-free and
`C₆`-free graph with more than

`(2669 / 5000) n ^ (4 / 3)`

edges.  All powers and inequalities in the density conclusion are over
`ℝ`, exactly as in `DensityAsymptotics`.
-/

open Finset
open scoped BigOperators

namespace LowerConstruction

noncomputable section

open AffinePolarity

private noncomputable instance graphAdjDecidable {n : ℕ}
    (G : SimpleGraph (Fin n)) : DecidableRel G.Adj :=
  Classical.decRel _

private def increasingOrientation {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) : FNV.Orientation G A where
  Dir x y := G.Adj x y ∧ x ∈ A ∧ y ∈ A ∧ x < y
  dir_adj h := h.1
  dir_fst_mem h := h.2.1
  dir_snd_mem h := h.2.2.1
  exactly_one := by
    intro x y hxy hx hy
    constructor
    · rintro ⟨_, _, _, hlt⟩ ⟨_, _, _, hrev⟩
      exact hlt.asymm hrev
    · intro hnrev
      refine ⟨hxy, hx, hy, ?_⟩
      have hnlt : ¬ y < x := by
        intro hyx
        exact hnrev ⟨hxy.symm, hy, hx, hyx⟩
      exact lt_of_le_of_ne (le_of_not_gt hnlt) hxy.ne

private noncomputable instance increasingOrientationDecidable {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) :
    DecidableRel (increasingOrientation G A).Dir :=
  Classical.decRel _

private theorem fnvK_le_fnvN (a : ℕ) : fnvK a ≤ fnvN a := by
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by norm_num
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsqrt_lower : (2 : ℝ) ≤ Real.sqrt 5 := by nlinarith
  have hsqrt_upper : Real.sqrt 5 - 2 ≤ 1 := by nlinarith
  have hNnonneg : (0 : ℝ) ≤ fnvN a := by positivity
  have hfloor : (fnvK a : ℝ) ≤
      (Real.sqrt 5 - 2) * (fnvN a : ℝ) := by
    exact Nat.floor_le (mul_nonneg (sub_nonneg.mpr hsqrt_lower) hNnonneg)
  exact_mod_cast (show (fnvK a : ℝ) ≤ fnvN a by
    nlinarith [mul_le_mul_of_nonneg_right hsqrt_upper hNnonneg])

private theorem two_le_fnvN (a : ℕ) : 2 ≤ fnvN a := by
  have hq : 2 ≤ fnvQ a := by
    rw [fnvQ, show 2 * a + 1 = 2 * a + 1 from rfl, pow_succ]
    have hpos : 0 < 2 ^ (2 * a) := pow_pos (by norm_num) _
    omega
  rw [fnvN]
  exact hq.trans (le_self_pow₀ (by omega) (by norm_num))

private theorem baseEdgeCard_cast (a : ℕ) :
    ((AffineCount.graph a).edgeFinset.card : ℝ) = fnvBaseEdges a := by
  rw [AffineCount.card_graph_edges, fnvBaseEdges]
  have h2q : 2 ∣ AffineCount.q a := by
    rw [AffineCount.q, show 2 * a + 1 = 2 * a + 1 from rfl, pow_succ]
    simpa [mul_comm] using dvd_mul_right 2 (2 ^ (2 * a))
  have h2q2 : 2 ∣ AffineCount.q a ^ 2 :=
    dvd_pow h2q (by norm_num)
  have h2q4 : 2 ∣ AffineCount.q a ^ 4 :=
    dvd_pow h2q (by norm_num)
  have hdiv : 2 ∣ AffineCount.q a ^ 4 - AffineCount.q a ^ 2 :=
    Nat.dvd_sub h2q4 h2q2
  have hle : AffineCount.q a ^ 2 ≤ AffineCount.q a ^ 4 := by
    rw [show AffineCount.q a ^ 4 =
      AffineCount.q a ^ 2 * AffineCount.q a ^ 2 by ring]
    exact Nat.le_mul_of_pos_right _ (pow_pos (by simp [AffineCount.q]) _)
  rw [Nat.cast_div hdiv (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Nat.cast_sub hle]
  norm_num [AffineCount.q, fnvQ]

private theorem baseC4Free (a : ℕ) :
    FNV.C4Free (AffineCount.graph a) := by
  apply (CycleAdapters.duplication_c4Free_iff_cycleGraph_four_free _).2
  apply (SimpleGraph.free_congr_right (AffineCount.graphIso a)).mp
  exact (CycleAdapters.affine_no_c4_iff_cycleGraph_four_free _).1
    (AffinePolarity.polarityGraph_no_C4 a)

/-- For every affine parameter `a ≥ 3`, the complete FNV construction gives
a labelled graph on exactly `fnvVertices a` vertices with the required
forbidden subgraphs and density. -/
theorem exists_graph (a : ℕ) (ha : 3 ≤ a) :
    ∃ B : SimpleGraph (Fin (fnvVertices a)),
      B.CliqueFree 3 ∧
      (SimpleGraph.cycleGraph 6).Free B ∧
      (B.edgeFinset.card : ℝ) >
        (2669 / 5000 : ℝ) *
          (fnvVertices a : ℝ) ^ (4 / 3 : ℝ) := by
  classical
  let G := AffineCount.graph a
  have hcardG : Fintype.card (Fin (AffineCount.q a ^ 3)) = fnvN a := by
    simp [fnvN, fnvQ, AffineCount.q]
  have hN : 2 ≤ Fintype.card (Fin (AffineCount.q a ^ 3)) := by
    simpa [hcardG] using two_le_fnvN a
  have hK : fnvK a ≤ Fintype.card (Fin (AffineCount.q a ^ 3)) := by
    simpa [hcardG] using fnvK_le_fnvN a
  obtain ⟨A, hAcard, haverage⟩ :=
    FNV.exists_subset_incidentEdges_fnv_rat (G := G) hN hK
  let O : FNV.Orientation G A := increasingOrientation G A
  let D : SimpleGraph (FNV.DuplicateVertex A) := FNV.duplication G A O
  have htriG : FNV.TriangleFree G := AffineCount.graph_cliqueFree_three a
  have hfourG : FNV.C4Free G := baseC4Free a
  have hsixG : FNV.C6Free G :=
    (CycleAdapters.duplication_c6Free_iff_cycleGraph_six_free G).2
      (AffineCount.graph_cycleGraph_six_free a)
  have htriD : D.CliqueFree 3 := by
    exact FNV.duplication_triangleFree (G := G) (A := A) (O := O) htriG
  have hsixD : (SimpleGraph.cycleGraph 6).Free D := by
    apply (CycleAdapters.duplication_c6Free_iff_cycleGraph_six_free D).1
    exact FNV.duplication_c6Free (G := G) (A := A) (O := O)
      htriG hfourG hsixG
  have hcardD : Fintype.card (FNV.DuplicateVertex A) = fnvVertices a := by
    simp [FNV.DuplicateVertex, fnvVertices, hcardG, hAcard]
  let B : SimpleGraph (Fin (fnvVertices a)) := D.overFin hcardD
  letI : DecidableRel B.Adj := Classical.decRel _
  let e : D ≃g B := D.overFinIso hcardD
  have haverageR :
      (G.edgeFinset.card : ℝ) * (fnvK a : ℝ) / (fnvN a : ℝ) *
          (2 - ((fnvK a : ℝ) - 1) / ((fnvN a : ℝ) - 1)) ≤
        ((FNV.incidentEdges G A).card : ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).2 haverage
    simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_div, Rat.cast_sub,
      Rat.cast_one, Rat.cast_ofNat] at hcast
    simpa [hcardG] using hcast
  have hlowerD : fnvLower a ≤ (D.edgeFinset.card : ℝ) := by
    have hbase : (G.edgeFinset.card : ℝ) = fnvBaseEdges a := by
      simpa [G] using baseEdgeCard_cast a
    rw [fnvLower, ← hbase]
    rw [FNV.card_edgeFinset_duplication (G := G) (A := A) (O := O)]
    push_cast
    convert add_le_add_left haverageR (G.edgeFinset.card : ℝ) using 1 <;> ring
  have hlowerB : fnvLower a ≤ (B.edgeFinset.card : ℝ) := by
    rw [← e.card_edgeFinset_eq]
    exact hlowerD
  refine ⟨B, ?_, ?_, ?_⟩
  · exact htriD.comap e.symm.toEmbedding.isContained
  · exact (SimpleGraph.free_congr_right e).mp hsixD
  · exact lt_of_lt_of_le (fnvLower_gt ha) hlowerB

/-- The dense labelled graphs above occur at unbounded vertex counts. -/
theorem infinitely_often :
    ∀ M : ℕ, ∃ a : ℕ, ∃ B : SimpleGraph (Fin (fnvVertices a)),
      M ≤ fnvVertices a ∧
      B.CliqueFree 3 ∧
      (SimpleGraph.cycleGraph 6).Free B ∧
      (B.edgeFinset.card : ℝ) >
        (2669 / 5000 : ℝ) *
          (fnvVertices a : ℝ) ^ (4 / 3 : ℝ) := by
  intro M
  let a := M + 3
  have ha : 3 ≤ a := by simp [a]
  have hMq : M < fnvQ a := by
    apply lt_of_le_of_lt (show M ≤ 2 * a + 1 by dsimp [a]; omega)
    simpa [fnvQ] using (2 * a + 1).lt_two_pow_self
  have hqN : fnvQ a ≤ fnvN a := by
    rw [fnvN]
    exact le_self_pow₀ (show 1 ≤ fnvQ a by
      exact Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (by norm_num))) (by norm_num)
  have hM : M ≤ fnvVertices a :=
    hMq.le.trans (hqN.trans (Nat.le_add_right _ _))
  obtain ⟨B, htri, hsix, hdense⟩ := exists_graph a ha
  exact ⟨a, B, hM, htri, hsix, hdense⟩

end

end LowerConstruction

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/BlowupFour.lean` -/

section
/-!
# Four-fold matching blowups

This is the four-point-fibre analogue of the Morris--Saxton matching blowup.
There are exactly `209` matchings in `K_{4,4}`.  Choosing one independently
over every edge of a triangle-free, `C₆`-free base graph produces distinct
labelled `C₆`-free graphs.
-/

open SimpleGraph

/-! ## Matchings in `K_{4,4}` -/

/-- Either four-element fibre of the local bipartite graph. -/
abbrev FibreFour := Fin 4

/-- A possible local edge between two four-element fibres. -/
abbrev EdgeFour := FibreFour × FibreFour

/-- Edges incident to a fixed left vertex. -/
def leftEdgesFour (s : Finset EdgeFour) (i : FibreFour) : Finset EdgeFour :=
  s.filter fun e ↦ e.1 = i

/-- Edges incident to a fixed right vertex. -/
def rightEdgesFour (s : Finset EdgeFour) (j : FibreFour) : Finset EdgeFour :=
  s.filter fun e ↦ e.2 = j

/-- The local edge set has degree at most one at every vertex on both sides. -/
def IsMatchingFour (s : Finset EdgeFour) : Prop :=
  (∀ i : FibreFour, (leftEdgesFour s i).card ≤ 1) ∧
    ∀ j : FibreFour, (rightEdgesFour s j).card ≤ 1

instance (s : Finset EdgeFour) : Decidable (IsMatchingFour s) := by
  unfold IsMatchingFour
  exact inferInstance

/-- Matchings between two labelled four-element fibres. -/
def MatchingFour := {s : Finset EdgeFour // IsMatchingFour s}

deriving instance DecidableEq for MatchingFour
deriving instance Fintype for MatchingFour

namespace MatchingFour

/-- The edge set underlying a four-fibre matching. -/
def edges (M : MatchingFour) : Finset EdgeFour := M.1

/-- The incidence relation of a four-fibre matching. -/
def Rel (M : MatchingFour) (i j : FibreFour) : Prop := (i, j) ∈ M.edges

instance (M : MatchingFour) : DecidableRel M.Rel := fun _ _ ↦ by
  unfold Rel edges
  exact inferInstance

/-- A matching is determined by its incidence relation. -/
@[ext] theorem ext {M N : MatchingFour}
    (h : ∀ i j, M.Rel i j ↔ N.Rel i j) : M = N := by
  apply Subtype.ext
  ext e
  exact h e.1 e.2

/-- A fixed left vertex has at most one partner. -/
theorem left_unique (M : MatchingFour) {i j j' : FibreFour}
    (h : M.Rel i j) (h' : M.Rel i j') : j = j' := by
  have hp : (i, j) = (i, j') :=
    Finset.card_le_one_iff.mp (M.2.1 i)
      (by simpa [leftEdgesFour, Rel, edges] using h)
      (by simpa [leftEdgesFour, Rel, edges] using h')
  exact congrArg Prod.snd hp

/-- A fixed right vertex has at most one partner. -/
theorem right_unique (M : MatchingFour) {i i' j : FibreFour}
    (h : M.Rel i j) (h' : M.Rel i' j) : i = i' := by
  have hp : (i, j) = (i', j) :=
    Finset.card_le_one_iff.mp (M.2.2 j)
      (by simpa [rightEdgesFour, Rel, edges] using h)
      (by simpa [rightEdgesFour, Rel, edges] using h')
  exact congrArg Prod.fst hp

end MatchingFour

/-- The set of left vertices used by a four-fibre matching. -/
def MatchingFour.leftSupport (M : MatchingFour) : Finset FibreFour :=
  M.edges.image Prod.fst

lemma MatchingFour.exists_partner_of_mem_leftSupport (M : MatchingFour)
    {i : FibreFour} (hi : i ∈ M.leftSupport) : ∃ j, M.Rel i j := by
  rcases Finset.mem_image.mp hi with ⟨e, he, hei⟩
  refine ⟨e.2, ?_⟩
  change (i, e.2) ∈ M.edges
  simpa [← hei] using he

/-- The matching which is the graph of an embedding defined on a subset of
the left fibre. -/
def matchingFourOfEmbedding (S : Finset FibreFour)
    (f : (S : Type) ↪ FibreFour) : MatchingFour := by
  refine ⟨Finset.image (fun i : (S : Type) ↦ (i.1, f i)) S.attach, ?_⟩
  constructor
  · intro i
    rw [Finset.card_le_one_iff]
    intro e e' he he'
    obtain ⟨he, hei⟩ := Finset.mem_filter.mp he
    obtain ⟨he', hei'⟩ := Finset.mem_filter.mp he'
    rcases Finset.mem_image.mp he with ⟨x, -, rfl⟩
    rcases Finset.mem_image.mp he' with ⟨x', -, rfl⟩
    have hxx' : x = x' := Subtype.ext <|
      hei.trans hei'.symm
    subst x'
    rfl
  · intro j
    rw [Finset.card_le_one_iff]
    intro e e' he he'
    obtain ⟨he, hfx⟩ := Finset.mem_filter.mp he
    obtain ⟨he', hfx'⟩ := Finset.mem_filter.mp he'
    rcases Finset.mem_image.mp he with ⟨x, -, rfl⟩
    rcases Finset.mem_image.mp he' with ⟨x', -, rfl⟩
    have hxx' : x = x' := f.injective (hfx.trans hfx'.symm)
    subst x'
    rfl

@[simp] lemma matchingFourOfEmbedding_rel (S : Finset FibreFour)
    (f : (S : Type) ↪ FibreFour) (i j : FibreFour) :
    (matchingFourOfEmbedding S f).Rel i j ↔
      ∃ hi : i ∈ S, f ⟨i, hi⟩ = j := by
  simp [matchingFourOfEmbedding, MatchingFour.Rel, MatchingFour.edges]

@[simp] lemma matchingFourOfEmbedding_leftSupport (S : Finset FibreFour)
    (f : (S : Type) ↪ FibreFour) :
    (matchingFourOfEmbedding S f).leftSupport = S := by
  ext i
  simp [MatchingFour.leftSupport, matchingFourOfEmbedding,
    MatchingFour.edges]

/-- The right partner selected by a matching whose left support is `S`. -/
noncomputable def matchingFourFiberPartner (S : Finset FibreFour)
    (M : {M : MatchingFour // M.leftSupport = S}) (i : (S : Type)) :
    FibreFour :=
  Classical.choose <| M.1.exists_partner_of_mem_leftSupport <| by
    rw [M.2]
    exact i.2

lemma matchingFourFiberPartner_spec (S : Finset FibreFour)
    (M : {M : MatchingFour // M.leftSupport = S}) (i : (S : Type)) :
    M.1.Rel i.1 (matchingFourFiberPartner S M i) :=
  Classical.choose_spec <| M.1.exists_partner_of_mem_leftSupport <| by
    rw [M.2]
    exact i.2

/-- A matching with prescribed left support is the same as an embedding of
that support in the right fibre. -/
noncomputable def matchingFourFiberEquiv (S : Finset FibreFour) :
    {M : MatchingFour // M.leftSupport = S} ≃ ((S : Type) ↪ FibreFour) where
  toFun M :=
    ⟨matchingFourFiberPartner S M, by
      intro i i' hii'
      apply Subtype.ext
      apply M.1.right_unique (matchingFourFiberPartner_spec S M i)
      have hi' := matchingFourFiberPartner_spec S M i'
      rwa [← hii'] at hi'⟩
  invFun f := ⟨matchingFourOfEmbedding S f,
    matchingFourOfEmbedding_leftSupport S f⟩
  left_inv M := by
    apply Subtype.ext
    apply MatchingFour.ext
    intro i j
    constructor
    · intro hij
      rw [matchingFourOfEmbedding_rel] at hij
      rcases hij with ⟨hiS, hij⟩
      exact hij ▸ matchingFourFiberPartner_spec S M ⟨i, hiS⟩
    · intro hij
      have hiS : i ∈ S := by
        rw [← M.2]
        apply Finset.mem_image.mpr
        refine ⟨(i, j), ?_, rfl⟩
        exact hij
      rw [matchingFourOfEmbedding_rel]
      refine ⟨hiS, ?_⟩
      exact M.1.left_unique
        (matchingFourFiberPartner_spec S M ⟨i, hiS⟩) hij
  right_inv f := by
    apply DFunLike.ext _ _
    intro i
    apply (matchingFourOfEmbedding S f).left_unique
      (matchingFourFiberPartner_spec S
        ⟨matchingFourOfEmbedding S f,
          matchingFourOfEmbedding_leftSupport S f⟩ i)
    exact matchingFourOfEmbedding_rel S f i.1 (f i) |>.2 ⟨i.2, rfl⟩

/-- Decompose a matching according to its left support. -/
noncomputable def matchingFourEquiv :
    MatchingFour ≃ Σ S : Finset FibreFour, ((S : Type) ↪ FibreFour) :=
  (Equiv.sigmaFiberEquiv MatchingFour.leftSupport).symm.trans <|
    Equiv.sigmaCongrRight matchingFourFiberEquiv

/-- There are exactly `209` matchings in the labelled `K_{4,4}`. -/
theorem matchingFour_card : Fintype.card MatchingFour = 209 := by
  rw [Fintype.card_congr matchingFourEquiv, Fintype.card_sigma]
  simp only [Fintype.card_embedding_eq, Fintype.card_coe]
  decide

/-! ## The matching blowup and recovery of its choices -/

/-- Independently choose a four-fibre matching for every base edge. -/
abbrev MatchingChoiceFour {V : Type*} (G : SimpleGraph V) :=
  G.edgeSet → MatchingFour

/-- Package an adjacency proof as its unordered certified base edge. -/
def certifiedEdgeFour {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : G.Adj u v) : G.edgeSet := ⟨s(u, v), h⟩

/-- Read the selected matching in the orientation `u → v`. -/
def matchingChoiceRelFour {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    (C : MatchingChoiceFour G) {u v : V} (h : G.Adj u v)
    (i j : FibreFour) : Prop :=
  if u < v then (C (certifiedEdgeFour h)).Rel i j
  else (C (certifiedEdgeFour h)).Rel j i

lemma matchingChoiceRelFour_symmetric {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoiceFour G) {u v : V}
    (h : G.Adj u v) (i j : FibreFour) :
    matchingChoiceRelFour C h i j ↔
      matchingChoiceRelFour C h.symm j i := by
  by_cases huv : u < v
  · have hvu : ¬ v < u := not_lt_of_ge huv.le
    have he : certifiedEdgeFour h.symm = certifiedEdgeFour h := by
      apply Subtype.ext
      exact Sym2.eq_swap
    simp [matchingChoiceRelFour, huv, hvu, he]
  · have hvu : v < u := lt_of_le_of_ne (le_of_not_gt huv) h.ne.symm
    have he : certifiedEdgeFour h.symm = certifiedEdgeFour h := by
      apply Subtype.ext
      exact Sym2.eq_swap
    simp [matchingChoiceRelFour, huv, hvu, he]

lemma matchingChoiceRelFour_left_unique {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoiceFour G) {u v : V}
    (h : G.Adj u v) {i j j' : FibreFour}
    (hj : matchingChoiceRelFour C h i j)
    (hj' : matchingChoiceRelFour C h i j') : j = j' := by
  by_cases huv : u < v
  · exact (C (certifiedEdgeFour h)).left_unique
      (by simpa [matchingChoiceRelFour, huv] using hj)
      (by simpa [matchingChoiceRelFour, huv] using hj')
  · exact (C (certifiedEdgeFour h)).right_unique
      (by simpa [matchingChoiceRelFour, huv] using hj)
      (by simpa [matchingChoiceRelFour, huv] using hj')

lemma matchingChoiceRelFour_right_unique {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoiceFour G) {u v : V}
    (h : G.Adj u v) {i i' j : FibreFour}
    (hi : matchingChoiceRelFour C h i j)
    (hi' : matchingChoiceRelFour C h i' j) : i = i' := by
  have hr : matchingChoiceRelFour C h.symm j i :=
    (matchingChoiceRelFour_symmetric C h i j).mp hi
  have hr' : matchingChoiceRelFour C h.symm j i' :=
    (matchingChoiceRelFour_symmetric C h i' j).mp hi'
  exact matchingChoiceRelFour_left_unique C h.symm hr hr'

/-- The graph obtained by replacing each base vertex by four points and each
base edge by its chosen matching. -/
def matchingBlowupFour {V : Type*} [LinearOrder V]
    (G : SimpleGraph V) (C : MatchingChoiceFour G) :
    SimpleGraph (V × FibreFour) where
  Adj x y := ∃ h : G.Adj x.1 y.1, matchingChoiceRelFour C h x.2 y.2
  symm := ⟨by
    rintro x y ⟨h, hC⟩
    exact ⟨h.symm, (matchingChoiceRelFour_symmetric C h _ _).mp hC⟩⟩
  loopless := ⟨by
    rintro x ⟨h, -⟩
    exact h.ne rfl⟩

@[simp] lemma matchingBlowupFour_adj {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoiceFour G)
    (x y : V × FibreFour) :
    (matchingBlowupFour G C).Adj x y ↔
      ∃ h : G.Adj x.1 y.1, matchingChoiceRelFour C h x.2 y.2 :=
  Iff.rfl

lemma matchingRelFour_iff_adj {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoiceFour G) {u v : V}
    (h : G.Adj u v) (i j : FibreFour) :
    matchingChoiceRelFour C h i j ↔
      (matchingBlowupFour G C).Adj (u, i) (v, j) := by
  constructor
  · exact fun hij ↦ ⟨h, hij⟩
  · rintro ⟨h', hij⟩
    simpa only [Subsingleton.elim h' h] using hij

/-- The blowup retains every independent local matching choice. -/
theorem matchingBlowupFour_injective {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} : Function.Injective (matchingBlowupFour G) := by
  intro A B hAB
  funext e
  apply MatchingFour.ext
  intro i j
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := he
      by_cases hlt : u < v
      · calc
          (A ⟨s(u, v), he⟩).Rel i j ↔ matchingChoiceRelFour A huv i j := by
            simp [matchingChoiceRelFour, hlt, certifiedEdgeFour]
          _ ↔ (matchingBlowupFour G A).Adj (u, i) (v, j) :=
            matchingRelFour_iff_adj A huv i j
          _ ↔ (matchingBlowupFour G B).Adj (u, i) (v, j) := by rw [hAB]
          _ ↔ matchingChoiceRelFour B huv i j :=
            (matchingRelFour_iff_adj B huv i j).symm
          _ ↔ (B ⟨s(u, v), he⟩).Rel i j := by
            simp [matchingChoiceRelFour, hlt, certifiedEdgeFour]
      · have hgt : v < u := lt_of_le_of_ne (le_of_not_gt hlt) huv.ne.symm
        calc
          (A ⟨s(u, v), he⟩).Rel i j ↔
              matchingChoiceRelFour A huv.symm i j := by
            simp [matchingChoiceRelFour, hgt, certifiedEdgeFour, Sym2.eq_swap]
          _ ↔ (matchingBlowupFour G A).Adj (v, i) (u, j) :=
            matchingRelFour_iff_adj A huv.symm i j
          _ ↔ (matchingBlowupFour G B).Adj (v, i) (u, j) := by rw [hAB]
          _ ↔ matchingChoiceRelFour B huv.symm i j :=
            (matchingRelFour_iff_adj B huv.symm i j).symm
          _ ↔ (B ⟨s(u, v), he⟩).Rel i j := by
            simp [matchingChoiceRelFour, hgt, certifiedEdgeFour, Sym2.eq_swap]

/-- Projection from the blowup to its base graph. -/
def matchingBlowupFourProjection {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoiceFour G) :
    matchingBlowupFour G C →g G where
  toFun := Prod.fst
  map_rel' := by
    rintro x y ⟨h, -⟩
    exact h

lemma eq_of_adj_adj_of_fst_eq_four {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} {C : MatchingChoiceFour G}
    {x y z : V × FibreFour}
    (hxy : (matchingBlowupFour G C).Adj x y)
    (hyz : (matchingBlowupFour G C).Adj y z)
    (hxz : x.1 = z.1) : x = z := by
  rcases x with ⟨xv, xi⟩
  rcases y with ⟨yv, yi⟩
  rcases z with ⟨zv, zi⟩
  change xv = zv at hxz
  subst zv
  rcases hxy with ⟨h, hC⟩
  rcases hyz with ⟨h', hC'⟩
  have hidx : xi = zi := by
    apply matchingChoiceRelFour_right_unique C h hC
    have hC'' : matchingChoiceRelFour C h.symm yi zi := by
      simpa only [Subsingleton.elim h' h.symm] using hC'
    exact (matchingChoiceRelFour_symmetric C h _ _).mpr hC''
  exact Prod.ext rfl hidx

lemma fst_ne_of_adj_adj_of_ne_four {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} {C : MatchingChoiceFour G}
    {x y z : V × FibreFour}
    (hxy : (matchingBlowupFour G C).Adj x y)
    (hyz : (matchingBlowupFour G C).Adj y z) (hxz : x ≠ z) :
    x.1 ≠ z.1 := by
  intro h
  exact hxz (eq_of_adj_adj_of_fst_eq_four hxy hyz h)

/-! ## Preservation of triangle- and six-cycle-freeness -/

/-- Edge-oriented triangle-freeness. -/
def TriangleFreeFour {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj c a

/-- Six-cycle-freeness in the explicit six-vertex presentation. -/
def C6FreeFour {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c d e f : V⦄,
    G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d e → G.Adj e f → G.Adj f a →
    ¬ [a, b, c, d, e, f].Nodup

lemma projected_six_nodup_four {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} {C : MatchingChoiceFour G}
    (htriangle : TriangleFreeFour G)
    {x₀ x₁ x₂ x₃ x₄ x₅ : V × FibreFour}
    (h₀₁ : (matchingBlowupFour G C).Adj x₀ x₁)
    (h₁₂ : (matchingBlowupFour G C).Adj x₁ x₂)
    (h₂₃ : (matchingBlowupFour G C).Adj x₂ x₃)
    (h₃₄ : (matchingBlowupFour G C).Adj x₃ x₄)
    (h₄₅ : (matchingBlowupFour G C).Adj x₄ x₅)
    (h₅₀ : (matchingBlowupFour G C).Adj x₅ x₀)
    (hnodup : [x₀, x₁, x₂, x₃, x₄, x₅].Nodup) :
    [x₀.1, x₁.1, x₂.1, x₃.1, x₄.1, x₅.1].Nodup := by
  have b₀₁ : G.Adj x₀.1 x₁.1 := (matchingBlowupFourProjection C).map_rel h₀₁
  have b₁₂ : G.Adj x₁.1 x₂.1 := (matchingBlowupFourProjection C).map_rel h₁₂
  have b₂₃ : G.Adj x₂.1 x₃.1 := (matchingBlowupFourProjection C).map_rel h₂₃
  have b₃₄ : G.Adj x₃.1 x₄.1 := (matchingBlowupFourProjection C).map_rel h₃₄
  have b₄₅ : G.Adj x₄.1 x₅.1 := (matchingBlowupFourProjection C).map_rel h₄₅
  have b₅₀ : G.Adj x₅.1 x₀.1 := (matchingBlowupFourProjection C).map_rel h₅₀
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    or_false, not_or] at hnodup ⊢
  rcases hnodup with ⟨h₀, h₁, h₂, h₃, n₄₅, -, -⟩
  rcases h₀ with ⟨n₀₁, n₀₂, n₀₃, n₀₄, n₀₅⟩
  rcases h₁ with ⟨n₁₂, n₁₃, n₁₄, n₁₅⟩
  rcases h₂ with ⟨n₂₃, n₂₄, n₂₅⟩
  rcases h₃ with ⟨n₃₄, n₃₅⟩
  have p₀₁ : x₀.1 ≠ x₁.1 := b₀₁.ne
  have p₀₂ : x₀.1 ≠ x₂.1 := fst_ne_of_adj_adj_of_ne_four h₀₁ h₁₂ n₀₂
  have p₀₄ : x₀.1 ≠ x₄.1 :=
    (fst_ne_of_adj_adj_of_ne_four h₄₅ h₅₀ (Ne.symm n₀₄)).symm
  have p₀₅ : x₀.1 ≠ x₅.1 := b₅₀.ne.symm
  have p₁₂ : x₁.1 ≠ x₂.1 := b₁₂.ne
  have p₁₃ : x₁.1 ≠ x₃.1 := fst_ne_of_adj_adj_of_ne_four h₁₂ h₂₃ n₁₃
  have p₁₅ : x₁.1 ≠ x₅.1 :=
    (fst_ne_of_adj_adj_of_ne_four h₅₀ h₀₁ (Ne.symm n₁₅)).symm
  have p₂₃ : x₂.1 ≠ x₃.1 := b₂₃.ne
  have p₂₄ : x₂.1 ≠ x₄.1 := fst_ne_of_adj_adj_of_ne_four h₂₃ h₃₄ n₂₄
  have p₃₄ : x₃.1 ≠ x₄.1 := b₃₄.ne
  have p₃₅ : x₃.1 ≠ x₅.1 := fst_ne_of_adj_adj_of_ne_four h₃₄ h₄₅ n₃₅
  have p₄₅ : x₄.1 ≠ x₅.1 := b₄₅.ne
  have p₀₃ : x₀.1 ≠ x₃.1 := by
    intro h
    apply htriangle b₀₁ b₁₂
    simpa [h] using b₂₃
  have p₁₄ : x₁.1 ≠ x₄.1 := by
    intro h
    apply htriangle b₁₂ b₂₃
    simpa [h] using b₃₄
  have p₂₅ : x₂.1 ≠ x₅.1 := by
    intro h
    apply htriangle b₂₃ b₃₄
    simpa [h] using b₄₅
  exact ⟨⟨p₀₁, p₀₂, p₀₃, p₀₄, p₀₅⟩,
    ⟨p₁₂, p₁₃, p₁₄, p₁₅⟩, ⟨p₂₃, p₂₄, p₂₅⟩,
    ⟨p₃₄, p₃₅⟩, p₄₅, trivial, List.nodup_nil⟩

/-- Four-fold matching blowups preserve `C₆`-freeness under the necessary
triangle-free hypothesis on the base. -/
theorem matchingBlowupFour_c6Free {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoiceFour G)
    (htriangle : TriangleFreeFour G) (hC6 : C6FreeFour G) :
    C6FreeFour (matchingBlowupFour G C) := by
  intro x₀ x₁ x₂ x₃ x₄ x₅ h₀₁ h₁₂ h₂₃ h₃₄ h₄₅ h₅₀ hnodup
  apply hC6
    ((matchingBlowupFourProjection C).map_rel h₀₁)
    ((matchingBlowupFourProjection C).map_rel h₁₂)
    ((matchingBlowupFourProjection C).map_rel h₂₃)
    ((matchingBlowupFourProjection C).map_rel h₃₄)
    ((matchingBlowupFourProjection C).map_rel h₄₅)
    ((matchingBlowupFourProjection C).map_rel h₅₀)
  exact projected_six_nodup_four htriangle h₀₁ h₁₂ h₂₃ h₃₄ h₄₅ h₅₀ hnodup

/-- The edge-oriented triangle predicate is standard triangle-freeness. -/
theorem triangleFreeFour_iff_cliqueFree_three {V : Type*}
    (G : SimpleGraph V) : TriangleFreeFour G ↔ G.CliqueFree 3 := by
  classical
  constructor
  · intro h s hs
    rw [SimpleGraph.is3Clique_iff] at hs
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hs
    exact False.elim (h hab hbc hac.symm)
  · intro h a b c hab hbc hca
    exact h {a, b, c}
      (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hca.symm, hbc⟩)

/-- The explicit six-tuple predicate is Mathlib's standard `C₆`-freeness. -/
theorem c6FreeFour_iff_cycleGraph_six_free {V : Type*}
    (G : SimpleGraph V) :
    C6FreeFour G ↔ (SimpleGraph.cycleGraph 6).Free G := by
  rw [cycleGraph_six_free_iff_forall_not_isC6]
  constructor
  · intro h v hv
    rcases hv with ⟨hinj, hadj⟩
    apply h (by simpa using hadj 0) (by simpa using hadj 1)
      (by simpa using hadj 2) (by simpa using hadj 3)
      (by simpa using hadj 4) (by simpa using hadj 5)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_false_eq_true, or_false, not_or]
    exact ⟨⟨hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide),
      hinj.ne (by decide), hinj.ne (by decide)⟩,
      ⟨hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide),
        hinj.ne (by decide)⟩,
      ⟨hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide)⟩,
      ⟨hinj.ne (by decide), hinj.ne (by decide)⟩,
      hinj.ne (by decide), trivial, List.nodup_nil⟩
  · intro h a b c d e f hab hbc hcd hde hef hfa hnodup
    apply h ![a, b, c, d, e, f]
    exact ⟨by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all,
      fun i ↦ by
        fin_cases i
        · simpa using hab
        · simpa using hbc
        · simpa using hcd
        · simpa using hde
        · simpa using hef
        · simpa using hfa⟩

/-- Standard-form preservation theorem. -/
theorem matchingBlowupFour_cycleGraph_six_free {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoiceFour G)
    (htriangle : G.CliqueFree 3)
    (hC6 : (SimpleGraph.cycleGraph 6).Free G) :
    (SimpleGraph.cycleGraph 6).Free (matchingBlowupFour G C) := by
  rw [← c6FreeFour_iff_cycleGraph_six_free]
  exact matchingBlowupFour_c6Free C
    ((triangleFreeFour_iff_cliqueFree_three G).mpr htriangle)
    ((c6FreeFour_iff_cycleGraph_six_free G).mpr hC6)

/-! ## Exact family size and canonical labelling -/

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The exact number of independent four-fibre matching choices. -/
theorem matchingChoiceFour_card (B : SimpleGraph V) [DecidableRel B.Adj] :
    Fintype.card (MatchingChoiceFour B) = 209 ^ B.edgeFinset.card := by
  rw [Fintype.card_fun, matchingFour_card, SimpleGraph.card_edgeSet]

/-- The standard four-fold fibre labelling. -/
def finFourEquiv (n : ℕ) : Fin n × Fin 4 ≃ Fin (4 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 4))

/-- Relabel a four-fold graph on the canonical `Fin (4*n)` vertex set. -/
def relabelFinFourGraph {n : ℕ} (G : SimpleGraph (Fin n × Fin 4)) :
    SimpleGraph (Fin (4 * n)) :=
  (finFourEquiv n).simpleGraph G

/-- Four-fold relabelling is injective on graphs. -/
def graphFinFourEquiv (n : ℕ) :
    SimpleGraph (Fin n × Fin 4) ≃ SimpleGraph (Fin (4 * n)) :=
  (finFourEquiv n).simpleGraph

/-- A graph is isomorphic to its four-fold relabelling. -/
def relabelFinFourGraphIso {n : ℕ} (G : SimpleGraph (Fin n × Fin 4)) :
    G ≃g relabelFinFourGraph G :=
  (SimpleGraph.Iso.comap (finFourEquiv n).symm G).symm

/-- Relabelling preserves every forbidden-subgraph predicate. -/
theorem relabelFinFourGraph_free_iff {W : Type*} (H : SimpleGraph W)
    {n : ℕ} (G : SimpleGraph (Fin n × Fin 4)) :
    H.Free (relabelFinFourGraph G) ↔ H.Free G :=
  (SimpleGraph.free_congr_right (relabelFinFourGraphIso G)).symm

/-- Each independent matching choice gives a distinct canonically labelled
`C₆`-free graph. -/
noncomputable def matchingChoiceFourFreeEmbedding {n : ℕ}
    (B : SimpleGraph (Fin n)) [DecidableRel B.Adj]
    (htriangle : B.CliqueFree 3)
    (hC6 : (SimpleGraph.cycleGraph 6).Free B) :
    MatchingChoiceFour B ↪
      LabelledFreeGraphs (SimpleGraph.cycleGraph 6) (4 * n) where
  toFun C := ⟨relabelFinFourGraph (matchingBlowupFour B C),
    (relabelFinFourGraph_free_iff _ _).mpr
      (matchingBlowupFour_cycleGraph_six_free C htriangle hC6)⟩
  inj' A C h := by
    apply matchingBlowupFour_injective
    apply (graphFinFourEquiv n).injective
    exact Subtype.ext_iff.mp h

/-- The four-fold matching construction supplies `209 ^ e(B)` distinct
labelled `C₆`-free graphs on `4*n` vertices. -/
theorem matchingBlowupFour_labelledFreeGraphCount_lower_bound {n : ℕ}
    (B : SimpleGraph (Fin n)) [DecidableRel B.Adj]
    (htriangle : B.CliqueFree 3)
    (hC6 : (SimpleGraph.cycleGraph 6).Free B) :
    209 ^ B.edgeFinset.card ≤
      labelledFreeGraphCount (SimpleGraph.cycleGraph 6) (4 * n) := by
  calc
    209 ^ B.edgeFinset.card = Nat.card (MatchingChoiceFour B) := by
      rw [Nat.card_eq_fintype_card, matchingChoiceFour_card]
    _ ≤ Nat.card (LabelledFreeGraphs (SimpleGraph.cycleGraph 6) (4 * n)) :=
      Nat.card_le_card_of_injective
        (matchingChoiceFourFreeEmbedding B htriangle hC6)
        (matchingChoiceFourFreeEmbedding B htriangle hC6).injective
    _ = labelledFreeGraphCount (SimpleGraph.cycleGraph 6) (4 * n) := rfl

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/NumericsFour.lean` -/

section
/-!
# Exact numerical certificate for the four-fold blow-up in Erdős problem 59

The transcendental inequalities in this file are reduced to exact comparisons
of natural-number or rational powers.
-/

/-- The exact logarithmic lower bound supplied by `209 ^ 10 > 2 ^ 77`. -/
theorem logb_two_209_gt : (77 : ℝ) / 10 < Real.logb 2 209 := by
  rw [Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 209)]
  rw [← Real.rpow_lt_rpow_iff
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    (by norm_num : (0 : ℝ) ≤ 209) (by norm_num : (0 : ℝ) < 10)]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [Real.rpow_natCast]

/-- The exact upper bound `4 ^ (4 / 3) < 108 / 17`. -/
theorem four_rpow_four_thirds_lt :
    (4 : ℝ) ^ ((4 : ℝ) / 3) < (108 : ℝ) / 17 := by
  rw [← Real.rpow_lt_rpow_iff
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)
    (by norm_num : (0 : ℝ) ≤ (108 : ℝ) / 17)
    (by norm_num : (0 : ℝ) < 3)]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num [Real.rpow_natCast]

/-- The strict coefficient comparison needed for the four-fold shortcut. -/
theorem numerical_four_certificate :
    ((2669 : ℝ) / 5000) * Real.logb 2 209 >
      ((101 : ℝ) / 100) * ((16 : ℝ) / 25) *
        (4 : ℝ) ^ ((4 : ℝ) / 3) := by
  have hlog := mul_lt_mul_of_pos_left logb_two_209_gt
    (by norm_num : (0 : ℝ) < (2669 : ℝ) / 5000)
  have hrpow := mul_lt_mul_of_pos_left four_rpow_four_thirds_lt
    (by norm_num :
      (0 : ℝ) < ((101 : ℝ) / 100) * ((16 : ℝ) / 25))
  norm_num at hlog hrpow ⊢
  exact hrpow.trans ((by norm_num : (43632 : ℝ) / 10625 < 205513 / 50000).trans hlog)

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/GirthDegree.lean` -/

section
/-!
# The large-girth reduction and the degree comparison for Erdős problem 59

This file isolates the finite bipartite combinatorics in U2--U3 of
Füredi--Naor--Verstraëte.  A `Bigraph A B` is used rather than a graph on a
tagged sum: this makes the two minimum degrees, and the three breadth-first
layers, explicit in their types.
-/

namespace GirthDegree

open Finset

/-- A finite bipartite graph with named left and right vertex types. -/
structure Bigraph (A B : Type*) where
  Adj : A → B → Prop

namespace Bigraph

variable {A B : Type*}

/-- Edge inclusion for bigraphs on the same two parts. -/
def LE (F G : Bigraph A B) : Prop :=
  ∀ ⦃a b⦄, F.Adj a b → G.Adj a b

/-- The degree of a left vertex. -/
def leftDegree [Fintype B] (G : Bigraph A B) [DecidableRel G.Adj] (a : A) : ℕ :=
  (Finset.univ.filter fun b ↦ G.Adj a b).card

/-- The degree of a right vertex. -/
def rightDegree [Fintype A] (G : Bigraph A B) [DecidableRel G.Adj] (b : B) : ℕ :=
  (Finset.univ.filter fun a ↦ G.Adj a b).card

/-- The usual vertex-distinct formulation of exclusion of a quadrilateral. -/
def NoFourCycle (G : Bigraph A B) : Prop :=
  ∀ ⦃a₀ a₁ b₀ b₁⦄, a₀ ≠ a₁ → b₀ ≠ b₁ →
    G.Adj a₀ b₀ → G.Adj a₁ b₀ → G.Adj a₁ b₁ → G.Adj a₀ b₁ → False

/-- The usual vertex-distinct formulation of exclusion of a hexagon. -/
def NoSixCycle (G : Bigraph A B) : Prop :=
  ∀ ⦃a₀ a₁ a₂ b₀ b₁ b₂⦄,
    a₀ ≠ a₁ → a₁ ≠ a₂ → a₂ ≠ a₀ →
    b₀ ≠ b₁ → b₁ ≠ b₂ → b₂ ≠ b₀ →
    G.Adj a₀ b₀ → G.Adj a₁ b₀ → G.Adj a₁ b₁ →
    G.Adj a₂ b₁ → G.Adj a₂ b₂ → G.Adj a₀ b₂ → False

/-- For a bipartite simple graph, girth at least eight is exactly exclusion
of four- and six-cycles. -/
def GirthAtLeastEight (G : Bigraph A B) : Prop :=
  G.NoFourCycle ∧ G.NoSixCycle

theorem NoFourCycle.mono {F G : Bigraph A B} (hFG : F.LE G) (hG : G.NoFourCycle) :
    F.NoFourCycle := by
  intro a₀ a₁ b₀ b₁ ha hb h₀ h₁ h₂ h₃
  exact hG ha hb (hFG h₀) (hFG h₁) (hFG h₂) (hFG h₃)

theorem NoSixCycle.mono {F G : Bigraph A B} (hFG : F.LE G) (hG : G.NoSixCycle) :
    F.NoSixCycle := by
  intro a₀ a₁ a₂ b₀ b₁ b₂ ha₀ ha₁ ha₂ hb₀ hb₁ hb₂ h₀ h₁ h₂ h₃ h₄ h₅
  exact hG ha₀ ha₁ ha₂ hb₀ hb₁ hb₂
    (hFG h₀) (hFG h₁) (hFG h₂) (hFG h₃) (hFG h₄) (hFG h₅)

theorem GirthAtLeastEight.mono {F G : Bigraph A B} (hFG : F.LE G)
    (hG : G.GirthAtLeastEight) : F.GirthAtLeastEight :=
  ⟨hG.1.mono hFG, hG.2.mono hFG⟩

/-- Exchange the two sides of a bigraph. -/
def swap (G : Bigraph A B) : Bigraph B A where
  Adj b a := G.Adj a b

instance (G : Bigraph A B) [DecidableRel G.Adj] : DecidableRel G.swap.Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (G.Adj _ _))

@[simp] theorem swap_adj (G : Bigraph A B) (a : A) (b : B) :
    G.swap.Adj b a ↔ G.Adj a b := Iff.rfl

@[simp] theorem swap_swap (G : Bigraph A B) : G.swap.swap = G := rfl

theorem NoFourCycle.swap {G : Bigraph A B} (hG : G.NoFourCycle) :
    G.swap.NoFourCycle := by
  intro b₀ b₁ a₀ a₁ hb ha h₀ h₁ h₂ h₃
  exact hG ha hb h₀ h₃ h₂ h₁

theorem NoSixCycle.swap {G : Bigraph A B} (hG : G.NoSixCycle) :
    G.swap.NoSixCycle := by
  intro b₀ b₁ b₂ a₀ a₁ a₂ hb₀ hb₁ hb₂ ha₀ ha₁ ha₂
    h₀ h₁ h₂ h₃ h₄ h₅
  exact hG (Ne.symm ha₂) (Ne.symm ha₁) (Ne.symm ha₀)
    (Ne.symm hb₂) (Ne.symm hb₁) (Ne.symm hb₀) h₀ h₅ h₄ h₃ h₂ h₁

theorem GirthAtLeastEight.swap {G : Bigraph A B} (hG : G.GirthAtLeastEight) :
    G.swap.GirthAtLeastEight := ⟨hG.1.swap, hG.2.swap⟩

section Degrees

variable [Fintype A] [Fintype B]
variable (G : Bigraph A B) [DecidableRel G.Adj]

@[simp] theorem leftDegree_eq_card_filter (a : A) :
    G.leftDegree a = (Finset.univ.filter fun b ↦ G.Adj a b).card := rfl

@[simp] theorem rightDegree_eq_card_filter (b : B) :
    G.rightDegree b = (Finset.univ.filter fun a ↦ G.Adj a b).card := rfl

@[simp] theorem swap_leftDegree (b : B) : G.swap.leftDegree b = G.rightDegree b := rfl

@[simp] theorem swap_rightDegree (a : A) : G.swap.rightDegree a = G.leftDegree a := rfl

end Degrees

section LargeGirthReduction

variable [Fintype A] [Fintype B]
variable (G : Bigraph A B) [DecidableRel G.Adj]

/-- The exact output required from the quadrilateral-component forest
selection.  This certificate is deliberately independent of the particular
component representation: the component file only has to provide the chosen
edge relation, inclusion, deletion of all quadrilaterals, and the two local
half-degree estimates. -/
structure QuadrilateralForestCertificate where
  F : Bigraph A B
  decidableAdj : DecidableRel F.Adj
  le_graph : F.LE G
  noFourCycle : F.NoFourCycle
  half_left : ∀ a, G.leftDegree a ≤ 2 * @leftDegree A B _ F decidableAdj a
  half_right : ∀ b, G.rightDegree b ≤ 2 * @rightDegree A B _ F decidableAdj b

end LargeGirthReduction

section BreadthFirst

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (F : Bigraph A B) [DecidableRel F.Adj]

/-- Non-backtracking length-three paths starting at a left vertex.  The
coordinates are `(first right vertex, middle left vertex, endpoint)`. -/
def leftThreePaths (x : A) : Finset (B × A × B) :=
  Finset.univ.filter fun p ↦
    F.Adj x p.1 ∧ p.2.1 ≠ x ∧ F.Adj p.2.1 p.1 ∧
      p.2.2 ≠ p.1 ∧ F.Adj p.2.1 p.2.2

@[simp] theorem mem_leftThreePaths {x : A} {p : B × A × B} :
    p ∈ F.leftThreePaths x ↔
      F.Adj x p.1 ∧ p.2.1 ≠ x ∧ F.Adj p.2.1 p.1 ∧
        p.2.2 ≠ p.1 ∧ F.Adj p.2.1 p.2.2 := by
  simp [leftThreePaths]

/-- In girth at least eight, two non-backtracking three-paths from the same
root cannot have the same endpoint.  The three cases in the proof close a
quadrilateral, another quadrilateral, or a hexagon. -/
theorem leftThreePath_endpoint_injOn (hF : F.GirthAtLeastEight) (x : A) :
    Set.InjOn (fun p : B × A × B ↦ p.2.2) (F.leftThreePaths x : Set (B × A × B)) := by
  rintro ⟨b, a, c⟩ hp ⟨b', a', c'⟩ hp' hc
  change (b, a, c) ∈ F.leftThreePaths x at hp
  change (b', a', c') ∈ F.leftThreePaths x at hp'
  rw [mem_leftThreePaths] at hp hp'
  rcases hp with ⟨hxb, hax, hab, hcb, hac⟩
  rcases hp' with ⟨hxb', ha'x, ha'b', hc'b', ha'c'⟩
  dsimp only at hc
  subst c'
  by_cases haa' : a = a'
  · subst a'
    have hbb' : b = b' := by
      by_contra hne
      exact hF.1 hax.symm hne hxb hab ha'b' hxb'
    subst b'
    rfl
  · have hbb' : b = b' := by
      by_contra hne
      exfalso
      exact hF.2 hax.symm haa' ha'x (Ne.symm hcb) hc'b' (Ne.symm hne)
        hxb hab hac ha'c' ha'b' hxb'
    subst b'
    exfalso
    exact hF.1 haa' (Ne.symm hcb) hab ha'b' ha'c' hac

/-- The third breadth-first layer from a left root injects into the right
part. -/
theorem card_leftThreePaths_le (hF : F.GirthAtLeastEight) (x : A) :
    (F.leftThreePaths x).card ≤ Fintype.card B := by
  simpa using Finset.card_le_card_of_injOn (fun p : B × A × B ↦ p.2.2)
    (s := F.leftThreePaths x) (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_univ _) (F.leftThreePath_endpoint_injOn hF x)

/-- First BFS layer from a left root. -/
def leftFirst (x : A) : Finset B :=
  Finset.univ.filter fun b ↦ F.Adj x b

/-- Children of `b` in the second BFS layer, with the parent deleted. -/
def leftSecond (x : A) (b : B) : Finset A :=
  Finset.univ.filter fun a ↦ a ≠ x ∧ F.Adj a b

/-- Children of `a` in the third BFS layer, with the parent deleted. -/
def leftThird (b : B) (a : A) : Finset B :=
  Finset.univ.filter fun c ↦ c ≠ b ∧ F.Adj a c

/-- The dependent finset of non-backtracking three-paths from `x`. -/
def leftPathSigma (x : A) : Finset (Σ _ : B, Σ _ : A, B) :=
  (F.leftFirst x).sigma fun b ↦
    (F.leftSecond x b).sigma fun a ↦ F.leftThird b a

/-- Forget the dependent packaging of a three-path. -/
def flattenLeftPath : (Σ _ : B, Σ _ : A, B) ↪ (B × A × B) where
  toFun p := (p.1, p.2.1, p.2.2)
  inj' := by
    rintro ⟨b, a, c⟩ ⟨b', a', c'⟩ h
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    rfl

theorem card_leftPathSigma_le_leftThreePaths (x : A) :
    (F.leftPathSigma x).card ≤ (F.leftThreePaths x).card := by
  apply Finset.card_le_card_of_injOn (flattenLeftPath (A := A) (B := B))
  · rintro ⟨b, a, c⟩ hp
    change (⟨b, ⟨a, c⟩⟩ : Σ _ : B, Σ _ : A, B) ∈ F.leftPathSigma x at hp
    rw [leftPathSigma, Finset.mem_sigma, Finset.mem_sigma] at hp
    rcases hp with ⟨hb, ha, hc⟩
    simp only [leftFirst, leftSecond, leftThird, Finset.mem_filter,
      Finset.mem_univ, true_and] at hb ha hc
    change (b, a, c) ∈ F.leftThreePaths x
    rw [mem_leftThreePaths]
    exact ⟨hb, ha.1, ha.2, hc.1, hc.2⟩
  · intro p _ q _ hpq
    exact (flattenLeftPath (A := A) (B := B)).injective hpq

/-- Quantitative BFS expansion.  If the first layer has at least `d₀`
vertices, every second-layer fibre has at least `d₁` children, and every
third-layer fibre has at least `d₂` children, then there are at least the
product many non-backtracking three-paths. -/
theorem mul_le_card_leftPathSigma (x : A) (d₀ d₁ d₂ : ℕ)
    (h₀ : d₀ ≤ F.leftDegree x)
    (h₁ : ∀ ⦃b⦄, F.Adj x b → d₁ + 1 ≤ F.rightDegree b)
    (h₂ : ∀ ⦃b a⦄, F.Adj x b → a ≠ x → F.Adj a b →
      d₂ + 1 ≤ F.leftDegree a) :
    d₀ * d₁ * d₂ ≤ (F.leftPathSigma x).card := by
  have hfirst : d₀ ≤ (F.leftFirst x).card := by
    simpa [leftFirst, leftDegree] using h₀
  have hsecond : ∀ b ∈ F.leftFirst x, d₁ ≤ (F.leftSecond x b).card := by
    intro b hb
    have hadj : F.Adj x b := by simpa [leftFirst] using hb
    have hxmem : x ∈ (Finset.univ.filter fun a ↦ F.Adj a b) := by simp [hadj]
    have heq : F.leftSecond x b = (Finset.univ.filter fun a ↦ F.Adj a b).erase x := by
      ext a
      simp [leftSecond, and_left_comm, eq_comm]
    rw [heq, Finset.card_erase_of_mem hxmem]
    simpa [rightDegree] using Nat.sub_le_sub_right (h₁ hadj) 1
  have hthird : ∀ b ∈ F.leftFirst x, ∀ a ∈ F.leftSecond x b,
      d₂ ≤ (F.leftThird b a).card := by
    intro b hb a ha
    have hadj : F.Adj x b := by simpa [leftFirst] using hb
    have hha : a ≠ x ∧ F.Adj a b := by simpa [leftSecond] using ha
    have hax : a ≠ x := hha.1
    have hab : F.Adj a b := hha.2
    have hbmem : b ∈ (Finset.univ.filter fun c ↦ F.Adj a c) := by simp [hab]
    have heq : F.leftThird b a = (Finset.univ.filter fun c ↦ F.Adj a c).erase b := by
      ext c
      simp [leftThird, and_left_comm, eq_comm]
    rw [heq, Finset.card_erase_of_mem hbmem]
    simpa [leftDegree] using Nat.sub_le_sub_right (h₂ hadj hax hab) 1
  rw [leftPathSigma, Finset.card_sigma]
  calc
    d₀ * d₁ * d₂ = d₀ * (d₁ * d₂) := Nat.mul_assoc _ _ _
    _ ≤ (F.leftFirst x).card * (d₁ * d₂) :=
      Nat.mul_le_mul_right (d₁ * d₂) hfirst
    _ = ∑ b ∈ F.leftFirst x, d₁ * d₂ := by simp
    _ ≤ ∑ b ∈ F.leftFirst x, (F.leftSecond x b).card * d₂ := by
      gcongr with b hb
      exact hsecond b hb
    _ = ∑ b ∈ F.leftFirst x, ∑ a ∈ F.leftSecond x b, d₂ := by
      apply Finset.sum_congr rfl
      intro b _
      simp
    _ ≤ ∑ b ∈ F.leftFirst x, ∑ a ∈ F.leftSecond x b,
        (F.leftThird b a).card := by
      gcongr with b hb a ha
      exact hthird b hb a ha
    _ = ∑ b ∈ F.leftFirst x,
        ((F.leftSecond x b).sigma fun a ↦ F.leftThird b a).card := by
      simp only [Finset.card_sigma]

/-- The left-root form of the FNV breadth-first estimate. -/
theorem left_bfs_layer_bound (hF : F.GirthAtLeastEight) (x : A) (d₀ d₁ d₂ : ℕ)
    (h₀ : d₀ ≤ F.leftDegree x)
    (h₁ : ∀ ⦃b⦄, F.Adj x b → d₁ + 1 ≤ F.rightDegree b)
    (h₂ : ∀ ⦃b a⦄, F.Adj x b → a ≠ x → F.Adj a b →
      d₂ + 1 ≤ F.leftDegree a) :
    d₀ * d₁ * d₂ ≤ Fintype.card B :=
  (F.mul_le_card_leftPathSigma x d₀ d₁ d₂ h₀ h₁ h₂).trans
    ((F.card_leftPathSigma_le_leftThreePaths x).trans (F.card_leftThreePaths_le hF x))

/-- The symmetric, right-root form of the breadth-first estimate. -/
theorem right_bfs_layer_bound (hF : F.GirthAtLeastEight) (x : B) (d₀ d₁ d₂ : ℕ)
    (h₀ : d₀ ≤ F.rightDegree x)
    (h₁ : ∀ ⦃a⦄, F.Adj a x → d₁ + 1 ≤ F.leftDegree a)
    (h₂ : ∀ ⦃a b⦄, F.Adj a x → b ≠ x → F.Adj a b →
      d₂ + 1 ≤ F.rightDegree b) :
    d₀ * d₁ * d₂ ≤ Fintype.card A := by
  exact F.swap.left_bfs_layer_bound hF.swap x d₀ d₁ d₂ h₀ h₁ h₂

end BreadthFirst

section DegreeComparison

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

private lemma ceil_half_le_of_le_two_mul {x y : ℕ} (h : x ≤ 2 * y) :
    (x + 1) / 2 ≤ y := by omega

private lemma shifted_half_le_of_le_two_mul {x y : ℕ} (h : x ≤ 2 * y)
    (hy : 1 ≤ y) : (x - 1) / 2 + 1 ≤ y := by omega

/-- FNV U3 for a bipartite graph, stated with the U2 subgraph explicit.
`F` has girth at least eight and retains at least half of every degree of
`G`.  The maximum-degree witness may lie in either part. -/
theorem bipartite_degree_comparison (G F : Bigraph A B)
    [DecidableRel G.Adj] [DecidableRel F.Adj]
    (hF : F.GirthAtLeastEight)
    (hhalfLeft : ∀ a, G.leftDegree a ≤ 2 * F.leftDegree a)
    (hhalfRight : ∀ b, G.rightDegree b ≤ 2 * F.rightDegree b)
    (deltaA deltaB Delta : ℕ)
    (hdeltaA : ∀ a, deltaA ≤ G.leftDegree a)
    (hdeltaB : ∀ b, deltaB ≤ G.rightDegree b)
    (hmax : (∃ a, G.leftDegree a = Delta) ∨ (∃ b, G.rightDegree b = Delta)) :
    Delta * (deltaA - 2) * (deltaB - 2) ≤
      8 * max (Fintype.card A) (Fintype.card B) := by
  let d₀ := (Delta + 1) / 2
  let dA := (deltaA - 1) / 2
  let dB := (deltaB - 1) / 2
  have hs₀ : Delta ≤ 2 * d₀ := by
    dsimp [d₀]
    omega
  have hsA : deltaA - 2 ≤ 2 * dA := by
    dsimp [dA]
    omega
  have hsB : deltaB - 2 ≤ 2 * dB := by
    dsimp [dB]
    omega
  rcases hmax with ⟨a, ha⟩ | ⟨b, hb⟩
  · have hroot : d₀ ≤ F.leftDegree a := by
      have hh := hhalfLeft a
      rw [ha] at hh
      simpa [d₀] using ceil_half_le_of_le_two_mul hh
    have hright : ∀ ⦃b⦄, F.Adj a b → dB + 1 ≤ F.rightDegree b := by
      intro b hab
      have hh : deltaB ≤ 2 * F.rightDegree b := (hdeltaB b).trans (hhalfRight b)
      have hpos : 1 ≤ F.rightDegree b := by
        rw [rightDegree]
        exact Finset.card_pos.mpr ⟨a, by simp [hab]⟩
      simpa [dB] using shifted_half_le_of_le_two_mul hh hpos
    have hleft : ∀ ⦃b a'⦄, F.Adj a b → a' ≠ a → F.Adj a' b →
        dA + 1 ≤ F.leftDegree a' := by
      intro b a' _ _ ha'b
      have hh : deltaA ≤ 2 * F.leftDegree a' := (hdeltaA a').trans (hhalfLeft a')
      have hpos : 1 ≤ F.leftDegree a' := by
        rw [leftDegree]
        exact Finset.card_pos.mpr ⟨b, by simp [ha'b]⟩
      simpa [dA] using shifted_half_le_of_le_two_mul hh hpos
    have hbfs : d₀ * dB * dA ≤ Fintype.card B :=
      F.left_bfs_layer_bound hF a d₀ dB dA hroot hright hleft
    calc
      Delta * (deltaA - 2) * (deltaB - 2) =
          Delta * (deltaB - 2) * (deltaA - 2) := by ac_rfl
      _ ≤ (2 * d₀) * (2 * dB) * (2 * dA) :=
        Nat.mul_le_mul (Nat.mul_le_mul hs₀ hsB) hsA
      _ = 8 * (d₀ * dB * dA) := by ring
      _ ≤ 8 * Fintype.card B := Nat.mul_le_mul_left 8 hbfs
      _ ≤ 8 * max (Fintype.card A) (Fintype.card B) :=
        Nat.mul_le_mul_left 8 (Nat.le_max_right _ _)
  · have hroot : d₀ ≤ F.rightDegree b := by
      have hh := hhalfRight b
      rw [hb] at hh
      simpa [d₀] using ceil_half_le_of_le_two_mul hh
    have hleft : ∀ ⦃a⦄, F.Adj a b → dA + 1 ≤ F.leftDegree a := by
      intro a hab
      have hh : deltaA ≤ 2 * F.leftDegree a := (hdeltaA a).trans (hhalfLeft a)
      have hpos : 1 ≤ F.leftDegree a := by
        rw [leftDegree]
        exact Finset.card_pos.mpr ⟨b, by simp [hab]⟩
      simpa [dA] using shifted_half_le_of_le_two_mul hh hpos
    have hright : ∀ ⦃a b'⦄, F.Adj a b → b' ≠ b → F.Adj a b' →
        dB + 1 ≤ F.rightDegree b' := by
      intro a b' _ _ hab'
      have hh : deltaB ≤ 2 * F.rightDegree b' := (hdeltaB b').trans (hhalfRight b')
      have hpos : 1 ≤ F.rightDegree b' := by
        rw [rightDegree]
        exact Finset.card_pos.mpr ⟨a, by simp [hab']⟩
      simpa [dB] using shifted_half_le_of_le_two_mul hh hpos
    have hbfs : d₀ * dA * dB ≤ Fintype.card A :=
      F.right_bfs_layer_bound hF b d₀ dA dB hroot hleft hright
    calc
      Delta * (deltaA - 2) * (deltaB - 2) ≤
          (2 * d₀) * (2 * dA) * (2 * dB) :=
        Nat.mul_le_mul (Nat.mul_le_mul hs₀ hsA) hsB
      _ = 8 * (d₀ * dA * dB) := by ring
      _ ≤ 8 * Fintype.card A := Nat.mul_le_mul_left 8 hbfs
      _ ≤ 8 * max (Fintype.card A) (Fintype.card B) :=
        Nat.mul_le_mul_left 8 (Nat.le_max_left _ _)

/-- The numerical bridge from a locally balanced bipartition to the general
FNV degree estimate.  Here `H` is the crossing bigraph, `D` is its maximum
degree, and `F` is its U2 large-girth subgraph.  The hypotheses `hDelta` and
`hdelta*` are precisely the degree losses from the locally maximal cut. -/
theorem degree_comparison (H F : Bigraph A B)
    [DecidableRel H.Adj] [DecidableRel F.Adj]
    (hF : F.GirthAtLeastEight)
    (hhalfLeft : ∀ a, H.leftDegree a ≤ 2 * F.leftDegree a)
    (hhalfRight : ∀ b, H.rightDegree b ≤ 2 * F.rightDegree b)
    (n delta Delta D : ℕ)
    (hcard : Fintype.card A + Fintype.card B = n)
    (hdeltaLeft : ∀ a, (delta + 1) / 2 ≤ H.leftDegree a)
    (hdeltaRight : ∀ b, (delta + 1) / 2 ≤ H.rightDegree b)
    (hmax : (∃ a, H.leftDegree a = D) ∨ (∃ b, H.rightDegree b = D))
    (hDelta : Delta ≤ 2 * D) :
    Delta * (delta - 4) ^ 2 ≤ 64 * n := by
  have hU₃ := bipartite_degree_comparison H F hF hhalfLeft hhalfRight
    ((delta + 1) / 2) ((delta + 1) / 2) D hdeltaLeft hdeltaRight hmax
  have hpart : max (Fintype.card A) (Fintype.card B) ≤ n := by
    rw [← hcard]
    apply max_le <;> omega
  have hU₃' : D * (((delta + 1) / 2) - 2) ^ 2 ≤ 8 * n := by
    calc
      D * (((delta + 1) / 2) - 2) ^ 2 =
          D * (((delta + 1) / 2) - 2) * (((delta + 1) / 2) - 2) := by ring
      _ ≤ 8 * max (Fintype.card A) (Fintype.card B) := hU₃
      _ ≤ 8 * n := Nat.mul_le_mul_left 8 hpart
  let d := ((delta + 1) / 2) - 2
  have hscale : delta - 4 ≤ 2 * d := by
    dsimp [d]
    omega
  calc
    Delta * (delta - 4) ^ 2 ≤ (2 * D) * (2 * d) ^ 2 := by
      gcongr
    _ = 8 * (D * d ^ 2) := by ring
    _ ≤ 8 * (8 * n) := Nat.mul_le_mul_left 8 hU₃'
    _ = 64 * n := by ring

end DegreeComparison

end Bigraph

/-! ## A deterministic locally balanced cut -/

section LocallyBalancedCut

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Toggle one vertex of a Boolean bipartition. -/
def flipColor (c : V → Bool) (v : V) : V → Bool :=
  fun w ↦ if w = v then !(c w) else c w

private def cutRelSymm (c : V → Bool) : Std.Symm (fun u w ↦ c u ≠ c w) :=
  ⟨fun _ _ ↦ Ne.symm⟩

/-- Edges crossing a Boolean bipartition. -/
def cutEdgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ e ∈ Sym2.fromRel (cutRelSymm c)

@[simp] theorem sym2_mem_cutEdgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (u w : V) :
    s(u, w) ∈ cutEdgeFinset G c ↔ G.Adj u w ∧ c u ≠ c w := by
  simp [cutEdgeFinset, cutRelSymm, SimpleGraph.mem_edgeFinset]

/-- Flipping one vertex toggles precisely its incident edges in the cut. -/
theorem cutEdgeFinset_flipColor (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (v : V) :
    cutEdgeFinset G (flipColor c v) =
      (G.incidenceFinset v \ cutEdgeFinset G c) ∪
        (cutEdgeFinset G c \ G.incidenceFinset v) := by
  ext e
  by_cases he : e ∈ G.edgeFinset
  · induction e using Sym2.inductionOn with | _ u w =>
    have hadj : G.Adj u w := by simpa [SimpleGraph.mem_edgeFinset] using he
    have huw : u ≠ w := G.ne_of_adj hadj
    simp only [sym2_mem_cutEdgeFinset, hadj, true_and, Finset.mem_union,
      Finset.mem_sdiff]
    by_cases hu : u = v
    · subst u
      have hw : w ≠ v := Ne.symm huw
      simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, flipColor,
        hadj, hw]
    · by_cases hw : w = v
      · subst w
        simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, flipColor,
          hadj, hu]
      · simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, flipColor,
          hadj, hu, hw, Ne.symm hu, Ne.symm hw]
  · have hinc : e ∉ G.incidenceFinset v := fun h ↦
      he (G.incidenceFinset_subset v h)
    simp [cutEdgeFinset, he, hinc]

/-- The number of neighbours of `v` lying across the cut. -/
def cutDegree (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) (v : V) : ℕ :=
  (G.neighborFinset v |>.filter fun w ↦ c w ≠ c v).card

theorem card_cutEdges_inter_incidence (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (v : V) :
    ((cutEdgeFinset G c) ∩ G.incidenceFinset v).card = cutDegree G c v := by
  let N := (G.neighborFinset v).filter fun w ↦ c w ≠ c v
  have himage : N.map (Sym2.mkEmbedding v) =
      (cutEdgeFinset G c) ∩ G.incidenceFinset v := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_map.mp he with ⟨w, hw, rfl⟩
      have hw' : G.Adj v w ∧ c w ≠ c v := by simpa [N] using hw
      simp [hw'.1, hw'.2, Ne.symm hw'.2, SimpleGraph.mem_incidenceFinset]
    · intro he
      have hinc : e ∈ G.incidenceFinset v := (Finset.mem_inter.mp he).2
      have hve : v ∈ e := by
        exact ((G.mem_incidenceFinset v e).mp hinc).2
      rcases Sym2.mem_iff_exists.mp hve with ⟨w, rfl⟩
      apply Finset.mem_map.mpr
      refine ⟨w, ?_, rfl⟩
      have hcut := (Finset.mem_inter.mp he).1
      have hh := (sym2_mem_cutEdgeFinset G c v w).mp hcut
      simp [N, hh.1, Ne.symm hh.2]
  rw [← himage, Finset.card_map]
  rfl

/-- A cut is locally balanced when at least half of the edges incident with
each vertex cross it. -/
def IsLocallyBalancedCut (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) : Prop :=
  ∀ v, G.degree v ≤ 2 * cutDegree G c v

/-- Every finite graph has a locally balanced bipartition.  Choose a cut with
the maximum possible number of crossing edges.  If a vertex saw fewer than
half of its incident edges across the cut, flipping it would strictly enlarge
the cut. -/
theorem exists_locallyBalancedCut (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ c : V → Bool, IsLocallyBalancedCut G c := by
  classical
  obtain ⟨c, _, hc⟩ := Finset.exists_max_image (Finset.univ : Finset (V → Bool))
    (fun c ↦ (cutEdgeFinset G c).card) ⟨fun _ ↦ false, Finset.mem_univ _⟩
  refine ⟨c, fun v ↦ ?_⟩
  by_contra hbad
  have hltDegree : 2 * cutDegree G c v < G.degree v := by
    omega
  let C := cutEdgeFinset G c
  let I := G.incidenceFinset v
  have hIC : (C ∩ I).card < (I \ C).card := by
    have hIcard : I.card = G.degree v := by
      simpa [I] using G.card_incidenceFinset_eq_degree v
    have hsplit : (I \ C).card = I.card - (C ∩ I).card := by
      simpa [Finset.inter_comm] using Finset.card_sdiff (s := C) (t := I)
    have hcross : (C ∩ I).card = cutDegree G c v := by
      simpa [C, I] using card_cutEdges_inter_incidence G c v
    omega
  have hCold : C = (C \ I) ∪ (C ∩ I) := by
    ext e
    by_cases he : e ∈ I <;> simp [he]
  have hdisjOld : Disjoint (C \ I) (C ∩ I) := by
    apply Finset.disjoint_left.mpr
    intro e he₀ he₁
    rw [Finset.mem_sdiff] at he₀
    rw [Finset.mem_inter] at he₁
    exact he₀.2 he₁.2
  have hdisjNew : Disjoint (I \ C) (C \ I) := by
    apply Finset.disjoint_left.mpr
    intro e he₀ he₁
    rw [Finset.mem_sdiff] at he₀ he₁
    exact he₀.2 he₁.1
  have hscore : C.card < (cutEdgeFinset G (flipColor c v)).card := by
    have hnew : (cutEdgeFinset G (flipColor c v)).card =
        (I \ C).card + (C \ I).card := by
      rw [cutEdgeFinset_flipColor, show G.incidenceFinset v = I from rfl,
        show cutEdgeFinset G c = C from rfl, Finset.card_union_of_disjoint hdisjNew]
    have hold : C.card = (C \ I).card + (C ∩ I).card := by
      calc
        C.card = ((C \ I) ∪ (C ∩ I)).card := congrArg Finset.card hCold
        _ = _ := Finset.card_union_of_disjoint hdisjOld
    rw [hnew, hold]
    omega
  exact (Nat.not_lt_of_ge (hc (flipColor c v) (Finset.mem_univ _))) hscore

/-- The two vertex types cut out by a Boolean colouring. -/
abbrev CutLeft (c : V → Bool) := {v : V // c v = false}
abbrev CutRight (c : V → Bool) := {v : V // c v = true}

/-- The crossing edges of a cut, regarded as a bigraph. -/
def crossingBigraph (G : SimpleGraph V) (c : V → Bool) :
    Bigraph (CutLeft c) (CutRight c) where
  Adj a b := G.Adj a.1 b.1

instance (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) :
    DecidableRel (crossingBigraph G c).Adj :=
  fun a b ↦ inferInstanceAs (Decidable (G.Adj a.1 b.1))

theorem crossingBigraph_leftDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (a : CutLeft c) :
    (crossingBigraph G c).leftDegree a = cutDegree G c a.1 := by
  let S := Finset.univ.filter fun b : CutRight c ↦ G.Adj a.1 b.1
  have himage : S.map (Function.Embedding.subtype _) =
      (G.neighborFinset a.1).filter fun w ↦ c w ≠ c a.1 := by
    ext w
    simp [S, a.2, SimpleGraph.mem_neighborFinset]
  unfold Bigraph.leftDegree cutDegree
  change S.card = _
  calc
    S.card = (S.map (Function.Embedding.subtype _)).card := by simp
    _ = _ := by rw [himage]

theorem crossingBigraph_rightDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (b : CutRight c) :
    (crossingBigraph G c).rightDegree b = cutDegree G c b.1 := by
  let S := Finset.univ.filter fun a : CutLeft c ↦ G.Adj a.1 b.1
  have himage : S.map (Function.Embedding.subtype _) =
      (G.neighborFinset b.1).filter fun w ↦ c w ≠ c b.1 := by
    ext w
    simp [S, b.2, SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]
  unfold Bigraph.rightDegree cutDegree
  change S.card = _
  calc
    S.card = (S.map (Function.Embedding.subtype _)).card := by simp
    _ = _ := by rw [himage]

theorem card_cut_parts (c : V → Bool) :
    Fintype.card (CutLeft c) + Fintype.card (CutRight c) = Fintype.card V := by
  simpa using Fintype.card_congr (Equiv.sumCompl fun v : V ↦ c v = false)

/-- A standard `cycleGraph 6` freeness hypothesis passes to every crossing
bigraph of a Boolean cut. -/
theorem crossingBigraph_noSixCycle_of_free (G : SimpleGraph V)
    (hG : (SimpleGraph.cycleGraph 6).Free G) (c : V → Bool) :
    (crossingBigraph G c).NoSixCycle := by
  intro a₀ a₁ a₂ b₀ b₁ b₂ ha₀ ha₁ ha₂ hb₀ hb₁ hb₂
    h₀ h₁ h₂ h₃ h₄ h₅
  have hfree := (cycleGraph_six_free_iff_forall_not_isC6 G).mp hG
  apply hfree ![a₀.1, b₀.1, a₁.1, b₁.1, a₂.1, b₂.1]
  constructor
  · have hcross : ∀ (a : CutLeft c) (b : CutRight c), a.1 ≠ b.1 := by
      intro a b hab
      have hc := congrArg c hab
      simp [a.2, b.2] at hc
    have ha₀' : a₀.1 ≠ a₁.1 := fun h ↦ ha₀ (Subtype.ext h)
    have ha₁' : a₁.1 ≠ a₂.1 := fun h ↦ ha₁ (Subtype.ext h)
    have ha₂' : a₂.1 ≠ a₀.1 := fun h ↦ ha₂ (Subtype.ext h)
    have hb₀' : b₀.1 ≠ b₁.1 := fun h ↦ hb₀ (Subtype.ext h)
    have hb₁' : b₁.1 ≠ b₂.1 := fun h ↦ hb₁ (Subtype.ext h)
    have hb₂' : b₂.1 ≠ b₀.1 := fun h ↦ hb₂ (Subtype.ext h)
    have hx₀₀ := hcross a₀ b₀
    have hx₀₁ := hcross a₀ b₁
    have hx₀₂ := hcross a₀ b₂
    have hx₁₀ := hcross a₁ b₀
    have hx₁₁ := hcross a₁ b₁
    have hx₁₂ := hcross a₁ b₂
    have hx₂₀ := hcross a₂ b₀
    have hx₂₁ := hcross a₂ b₁
    have hx₂₂ := hcross a₂ b₂
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    · simpa [crossingBigraph] using h₀
    · simpa [crossingBigraph] using h₁.symm
    · simpa [crossingBigraph] using h₂
    · simpa [crossingBigraph] using h₃.symm
    · simpa [crossingBigraph] using h₄
    · simpa [crossingBigraph] using h₅.symm

/-- The general constant-64 comparison, assembled from the deterministic
locally balanced cut and U2 on its crossing bigraph.  `hSix` is the direct
typed form of the fact that C6-freeness passes to a spanning subgraph; the
quadrilateral-component development supplies `hforest`. -/
theorem general_degree_comparison_of_u2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (delta Delta : ℕ)
    (hmin : ∀ v, delta ≤ G.degree v)
    (hmax : ∃ v, G.degree v = Delta)
    (hSix : ∀ c : V → Bool, (crossingBigraph G c).NoSixCycle)
    (hforest : ∀ (c : V → Bool), IsLocallyBalancedCut G c →
      Bigraph.QuadrilateralForestCertificate (crossingBigraph G c)) :
    Delta * (delta - 4) ^ 2 ≤ 64 * Fintype.card V := by
  classical
  obtain ⟨c, hc⟩ := exists_locallyBalancedCut G
  let H := crossingBigraph G c
  obtain ⟨vmax, hvmax⟩ := hmax
  obtain ⟨vD, _, hvD⟩ := Finset.exists_max_image (Finset.univ : Finset V)
    (cutDegree G c) ⟨vmax, Finset.mem_univ _⟩
  let D := cutDegree G c vD
  have hmaxH : (∃ a, H.leftDegree a = D) ∨ (∃ b, H.rightDegree b = D) := by
    cases hcolor : c vD with
    | false =>
        left
        refine ⟨⟨vD, hcolor⟩, ?_⟩
        exact crossingBigraph_leftDegree G c ⟨vD, hcolor⟩
    | true =>
        right
        refine ⟨⟨vD, hcolor⟩, ?_⟩
        exact crossingBigraph_rightDegree G c ⟨vD, hcolor⟩
  have hdeltaLeft : ∀ a, (delta + 1) / 2 ≤ H.leftDegree a := by
    intro a
    have h₀ := hmin a.1
    have h₁ := hc a.1
    rw [crossingBigraph_leftDegree]
    omega
  have hdeltaRight : ∀ b, (delta + 1) / 2 ≤ H.rightDegree b := by
    intro b
    have h₀ := hmin b.1
    have h₁ := hc b.1
    rw [crossingBigraph_rightDegree]
    omega
  have hDelta : Delta ≤ 2 * D := by
    have h₀ := hc vmax
    have h₁ := hvD vmax (Finset.mem_univ _)
    rw [hvmax] at h₀
    dsimp [D]
    omega
  let C := hforest c hc
  letI : DecidableRel C.F.Adj := C.decidableAdj
  have hFgirth : C.F.GirthAtLeastEight :=
    ⟨C.noFourCycle, (hSix c).mono C.le_graph⟩
  exact Bigraph.degree_comparison H C.F hFgirth C.half_left C.half_right
    (Fintype.card V) delta Delta D (card_cut_parts c) hdeltaLeft hdeltaRight hmaxH hDelta

/-- The deterministic-bipartition form of the general FNV degree comparison,
with standard Mathlib `cycleGraph 6` freeness.  The remaining argument is the
concrete U2 forest selector for each crossing bigraph. -/
theorem degree_comparison (G : SimpleGraph V) [DecidableRel G.Adj]
    (delta Delta : ℕ)
    (hmin : ∀ v, delta ≤ G.degree v)
    (hmax : ∃ v, G.degree v = Delta)
    (hfree : (SimpleGraph.cycleGraph 6).Free G)
    (hforest : ∀ (c : V → Bool), IsLocallyBalancedCut G c →
      Bigraph.QuadrilateralForestCertificate (crossingBigraph G c)) :
    Delta * (delta - 4) ^ 2 ≤ 64 * Fintype.card V := by
  apply general_degree_comparison_of_u2 G delta Delta hmin hmax
  · exact fun c ↦ crossingBigraph_noSixCycle_of_free G hfree c
  · exact hforest

end LocallyBalancedCut

end GirthDegree

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/U2Direct.lean` -/

section
/-!
# A direct finite proof of the FNV large-girth reduction

This file proves the quadrilateral-component forest selection used in FNV U2
for a concrete finite bipartite graph.  In a hexagon-free bipartite graph, two
quadrilaterals sharing an edge have a whole vertex side in common.  Consequently
the equivalence classes generated by sharing a quadrilateral are complete
bipartite graphs, and one of their two sides has size at most two.
-/

namespace GirthDegree

open Finset

namespace Bigraph

noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B]
variable (G : Bigraph A B) [DecidableRel G.Adj]

local instance instDecidableEqLeft : DecidableEq A := Classical.decEq A
local instance instDecidableEqRight : DecidableEq B := Classical.decEq B

/-- An edge of a bigraph, with its incidence proof. -/
abbrev QEdge := {e : A × B // G.Adj e.1 e.2}

/-- A quadrilateral based at `e`, named by its opposite left and right vertices. -/
structure SquareAt (e : QEdge G) (a : A) (b : B) : Prop where
  left_ne : a ≠ e.1.1
  right_ne : b ≠ e.1.2
  left_base : G.Adj a e.1.2
  base_right : G.Adj e.1.1 b
  corner : G.Adj a b

/-- Membership of an edge in the four positions of a based quadrilateral. -/
def InSquareAt (e : QEdge G) (a : A) (b : B) (f : QEdge G) : Prop :=
  (f.1.1 = e.1.1 ∨ f.1.1 = a) ∧ (f.1.2 = e.1.2 ∨ f.1.2 = b)

/-- Two edges occur in one quadrilateral. -/
def SharesSquare (e f : QEdge G) : Prop :=
  ∃ a b, SquareAt G e a b ∧ InSquareAt G e a b f

private lemma adj_of_inSquareAt {e f : QEdge G} {a : A} {b : B}
    (hs : SquareAt G e a b) (hf : InSquareAt G e a b f) :
    G.Adj e.1.1 f.1.2 ∧ G.Adj a f.1.2 ∧
      G.Adj f.1.1 e.1.2 ∧ G.Adj f.1.1 b := by
  rcases hf with ⟨hfa | hfa, hfb | hfb⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hfb] using e.2
    · simpa [hfb] using hs.left_base
    · simpa [hfa] using e.2
    · simpa [hfa] using hs.base_right
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hfb] using hs.base_right
    · simpa [hfb] using hs.corner
    · simpa [hfa] using e.2
    · simpa [hfa] using hs.base_right
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hfb] using e.2
    · simpa [hfb] using hs.left_base
    · simpa [hfa] using hs.left_base
    · simpa [hfa] using hs.corner
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hfb] using hs.base_right
    · simpa [hfb] using hs.corner
    · simpa [hfa] using hs.left_base
    · simpa [hfa] using hs.corner

theorem sharesSquare_symm {e f : QEdge G} :
    SharesSquare G e f → SharesSquare G f e := by
  rintro ⟨a, b, hs, ⟨hfa | hfa, hfb | hfb⟩⟩
  · have hef : f = e := Subtype.ext (Prod.ext hfa hfb)
    subst f
    exact ⟨a, b, hs, ⟨Or.inl rfl, Or.inl rfl⟩⟩
  · refine ⟨a, e.1.2, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro ha
        exact hs.left_ne (ha.trans hfa)
      · intro hb
        exact hs.right_ne (hfb.symm.trans hb.symm)
      · simpa [hfb] using hs.corner
      · simpa [hfa] using e.2
      · simpa [hfb] using hs.left_base
    · exact ⟨Or.inl hfa.symm, Or.inr rfl⟩
  · refine ⟨e.1.1, b, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro ha
        exact hs.left_ne (hfa.symm.trans ha.symm)
      · intro hb
        exact hs.right_ne (hb.trans hfb)
      · simpa [hfb] using e.2
      · simpa [hfa] using hs.corner
      · simpa [hfa] using hs.base_right
    · exact ⟨Or.inr rfl, Or.inl hfb.symm⟩
  · refine ⟨e.1.1, e.1.2, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro ha
        exact hs.left_ne (hfa.symm.trans ha.symm)
      · intro hb
        exact hs.right_ne (hfb.symm.trans hb.symm)
      · simpa [hfa, hfb] using hs.base_right
      · simpa [hfa, hfb] using hs.left_base
      · exact e.2
    · exact ⟨Or.inr rfl, Or.inr rfl⟩

private lemma sharesSquare_of_two_left {e f : QEdge G} {x y : A}
    (hxy : x ≠ y)
    (heA : e.1.1 = x ∨ e.1.1 = y) (hfA : f.1.1 = x ∨ f.1.1 = y)
    (he : G.Adj x e.1.2 ∧ G.Adj y e.1.2)
    (hf : G.Adj x f.1.2 ∧ G.Adj y f.1.2)
    {b₀ b₁ : B} (hb : b₀ ≠ b₁)
    (hb₀ : G.Adj x b₀ ∧ G.Adj y b₀)
    (hb₁ : G.Adj x b₁ ∧ G.Adj y b₁) : SharesSquare G e f := by
  classical
  have hleft : (if e.1.1 = x then y else x) ≠ e.1.1 := by
    split_ifs with hx
    · simpa [hx] using hxy.symm
    · rcases heA with heA | heA
      · exact (hx heA).elim
      · simpa [heA] using hxy
  let z : A := if e.1.1 = x then y else x
  have hz : z = x ∨ z = y := by
    dsimp [z]
    split_ifs <;> simp
  have hze : G.Adj z e.1.2 := by
    rcases hz with hz | hz
    · simpa [hz] using he.1
    · simpa [hz] using he.2
  have hpair : ∀ w : A, w = x ∨ w = y → w = e.1.1 ∨ w = z := by
    intro w hw
    dsimp [z]
    split_ifs with hex
    · rcases hw with hw | hw
      · exact Or.inl (hw.trans hex.symm)
      · exact Or.inr hw
    · have hey : e.1.1 = y := heA.resolve_left hex
      rcases hw with hw | hw
      · exact Or.inr hw
      · exact Or.inl (hw.trans hey.symm)
  by_cases hefB : e.1.2 = f.1.2
  · let c : B := if e.1.2 = b₀ then b₁ else b₀
    have hcne : c ≠ e.1.2 := by
      dsimp [c]
      split_ifs with he0
      · simpa [he0] using hb.symm
      · exact fun h ↦ he0 h.symm
    have hxc : G.Adj x c := by
      dsimp [c]
      split_ifs
      · exact hb₁.1
      · exact hb₀.1
    have hyc : G.Adj y c := by
      dsimp [c]
      split_ifs
      · exact hb₁.2
      · exact hb₀.2
    have hec : G.Adj e.1.1 c := by
      rcases heA with heA | heA
      · simpa [heA] using hxc
      · simpa [heA] using hyc
    have hzc : G.Adj z c := by
      rcases hz with hz | hz
      · simpa [hz] using hxc
      · simpa [hz] using hyc
    exact ⟨z, c, ⟨hleft, hcne, hze, hec, hzc⟩,
      hpair f.1.1 hfA, Or.inl hefB.symm⟩
  ·
    have hbaseRight : G.Adj e.1.1 f.1.2 := by
      rcases heA with heA | heA
      · simpa [heA] using hf.1
      · simpa [heA] using hf.2
    have hcorner : G.Adj z f.1.2 := by
      rcases hz with hz | hz
      · simpa [hz] using hf.1
      · simpa [hz] using hf.2
    exact ⟨z, f.1.2, ⟨hleft, Ne.symm hefB, hze, hbaseRight, hcorner⟩,
      hpair f.1.1 hfA, Or.inr rfl⟩

private lemma sharesSquare_of_two_right {e f : QEdge G} {x y : B}
    (hxy : x ≠ y)
    (heB : e.1.2 = x ∨ e.1.2 = y) (hfB : f.1.2 = x ∨ f.1.2 = y)
    (he : G.Adj e.1.1 x ∧ G.Adj e.1.1 y)
    (hf : G.Adj f.1.1 x ∧ G.Adj f.1.1 y)
    {a₀ a₁ : A} (ha : a₀ ≠ a₁)
    (ha₀ : G.Adj a₀ x ∧ G.Adj a₀ y)
    (ha₁ : G.Adj a₁ x ∧ G.Adj a₁ y) : SharesSquare G e f := by
  classical
  have hright : (if e.1.2 = x then y else x) ≠ e.1.2 := by
    split_ifs with hx
    · simpa [hx] using hxy.symm
    · rcases heB with heB | heB
      · exact (hx heB).elim
      · simpa [heB] using hxy
  let z : B := if e.1.2 = x then y else x
  have hz : z = x ∨ z = y := by
    dsimp [z]
    split_ifs <;> simp
  have hez : G.Adj e.1.1 z := by
    rcases hz with hz | hz
    · simpa [hz] using he.1
    · simpa [hz] using he.2
  have hpair : ∀ w : B, w = x ∨ w = y → w = e.1.2 ∨ w = z := by
    intro w hw
    dsimp [z]
    split_ifs with hex
    · rcases hw with hw | hw
      · exact Or.inl (hw.trans hex.symm)
      · exact Or.inr hw
    · have hey : e.1.2 = y := heB.resolve_left hex
      rcases hw with hw | hw
      · exact Or.inr hw
      · exact Or.inl (hw.trans hey.symm)
  by_cases hefA : e.1.1 = f.1.1
  · let c : A := if e.1.1 = a₀ then a₁ else a₀
    have hcne : c ≠ e.1.1 := by
      dsimp [c]
      split_ifs with he0
      · simpa [he0] using ha.symm
      · exact fun h ↦ he0 h.symm
    have hcx : G.Adj c x := by
      dsimp [c]
      split_ifs
      · exact ha₁.1
      · exact ha₀.1
    have hcy : G.Adj c y := by
      dsimp [c]
      split_ifs
      · exact ha₁.2
      · exact ha₀.2
    have hce : G.Adj c e.1.2 := by
      rcases heB with heB | heB
      · simpa [heB] using hcx
      · simpa [heB] using hcy
    have hcz : G.Adj c z := by
      rcases hz with hz | hz
      · simpa [hz] using hcx
      · simpa [hz] using hcy
    exact ⟨c, z, ⟨hcne, hright, hce, hez, hcz⟩,
      Or.inl hefA.symm, hpair f.1.2 hfB⟩
  ·
    have hleftBase : G.Adj f.1.1 e.1.2 := by
      rcases heB with heB | heB
      · simpa [heB] using hf.1
      · simpa [heB] using hf.2
    have hcorner : G.Adj f.1.1 z := by
      rcases hz with hz | hz
      · simpa [hz] using hf.1
      · simpa [hz] using hf.2
    exact ⟨f.1.1, z, ⟨Ne.symm hefA, hright, hleftBase, hez, hcorner⟩,
      Or.inr rfl, hpair f.1.2 hfB⟩

theorem sharesSquare_trans (hG₆ : G.NoSixCycle) {e f k : QEdge G}
    (hef : SharesSquare G e f) (hfk : SharesSquare G f k) :
    SharesSquare G e k := by
  obtain ⟨a₁, b₁, hs₁, he₁⟩ := sharesSquare_symm G hef
  obtain ⟨a₂, b₂, hs₂, hk₂⟩ := hfk
  have merge : a₁ = a₂ ∨ b₁ = b₂ := by
    by_cases ha : a₁ = a₂
    · exact Or.inl ha
    by_cases hb : b₁ = b₂
    · exact Or.inr hb
    exfalso
    exact hG₆ hs₁.left_ne.symm ha hs₂.left_ne
      hs₁.right_ne hs₂.right_ne.symm (Ne.symm hb)
      hs₁.base_right hs₁.corner hs₁.left_base
      hs₂.left_base hs₂.corner hs₂.base_right
  rcases merge with ha | hb
  · subst a₂
    apply sharesSquare_of_two_left G hs₁.left_ne.symm he₁.1 hk₂.1
      (b₀ := f.1.2) (b₁ := b₁)
    · have h := adj_of_inSquareAt G hs₁ he₁
      exact ⟨h.1, h.2.1⟩
    · have h := adj_of_inSquareAt G hs₂ hk₂
      exact ⟨h.1, h.2.1⟩
    · exact hs₁.right_ne.symm
    · exact ⟨f.2, hs₁.left_base⟩
    · exact ⟨hs₁.base_right, hs₁.corner⟩
  · subst b₂
    apply sharesSquare_of_two_right G hs₁.right_ne.symm he₁.2 hk₂.2
      (a₀ := f.1.1) (a₁ := a₁)
    · exact ⟨(adj_of_inSquareAt G hs₁ he₁).2.2.1,
        (adj_of_inSquareAt G hs₁ he₁).2.2.2⟩
    · exact ⟨(adj_of_inSquareAt G hs₂ hk₂).2.2.1,
        (adj_of_inSquareAt G hs₂ hk₂).2.2.2⟩
    · exact hs₁.left_ne.symm
    · exact ⟨f.2, hs₁.base_right⟩
    · exact ⟨hs₁.left_base, hs₁.corner⟩

/-- In a hexagon-free bigraph, equality-or-sharing-a-square is already the
equivalence relation generated by sharing a square. -/
def QuadrilateralEquivalent (hG₆ : G.NoSixCycle) (e f : QEdge G) : Prop :=
  e = f ∨ SharesSquare G e f

theorem quadrilateralEquivalent_equivalence (hG₆ : G.NoSixCycle) :
    Equivalence (QuadrilateralEquivalent G hG₆) := by
  refine ⟨fun e ↦ Or.inl rfl, ?_, ?_⟩
  · rintro e f (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr (sharesSquare_symm G h)
  · rintro e f k (rfl | hef) (rfl | hfk)
    · exact Or.inl rfl
    · exact Or.inr hfk
    · exact Or.inr hef
    · exact Or.inr (sharesSquare_trans G hG₆ hef hfk)

def quadrilateralSetoid (hG₆ : G.NoSixCycle) : Setoid (QEdge G) :=
  ⟨QuadrilateralEquivalent G hG₆,
    quadrilateralEquivalent_equivalence G hG₆⟩

abbrev QuadrilateralClass (hG₆ : G.NoSixCycle) :=
  Quotient (quadrilateralSetoid G hG₆)

noncomputable instance instFintypeQuadrilateralClass (hG₆ : G.NoSixCycle) :
    Fintype (QuadrilateralClass G hG₆) :=
  Fintype.ofFinite _

def quadrilateralClassOf (hG₆ : G.NoSixCycle) (e : QEdge G) :
    QuadrilateralClass G hG₆ := Quotient.mk (quadrilateralSetoid G hG₆) e

variable (hG₆ : G.NoSixCycle)

/-- The finite edge set of one quadrilateral-sharing class. -/
noncomputable def classEdges (C : QuadrilateralClass G hG₆) : Finset (QEdge G) := by
  classical
  exact Finset.univ.filter fun e ↦ quadrilateralClassOf G hG₆ e = C

@[simp] theorem mem_classEdges {C : QuadrilateralClass G hG₆} {e : QEdge G} :
    e ∈ classEdges G hG₆ C ↔ quadrilateralClassOf G hG₆ e = C := by
  simp [classEdges]

/-- Left vertices incident with a class. -/
noncomputable def classLeft (C : QuadrilateralClass G hG₆) : Finset A := by
  classical
  exact Finset.univ.filter fun a ↦
    ∃ e : QEdge G, quadrilateralClassOf G hG₆ e = C ∧ e.1.1 = a

/-- Right vertices incident with a class. -/
noncomputable def classRight (C : QuadrilateralClass G hG₆) : Finset B := by
  classical
  exact Finset.univ.filter fun b ↦
    ∃ e : QEdge G, quadrilateralClassOf G hG₆ e = C ∧ e.1.2 = b

@[simp] theorem mem_classLeft {C : QuadrilateralClass G hG₆} {a : A} :
    a ∈ classLeft G hG₆ C ↔
      ∃ e : QEdge G, quadrilateralClassOf G hG₆ e = C ∧ e.1.1 = a := by
  simp [classLeft]

@[simp] theorem mem_classRight {C : QuadrilateralClass G hG₆} {b : B} :
    b ∈ classRight G hG₆ C ↔
      ∃ e : QEdge G, quadrilateralClassOf G hG₆ e = C ∧ e.1.2 = b := by
  simp [classRight]

theorem quadrilateralEquivalent_of_same_class {e f : QEdge G}
    (h : quadrilateralClassOf G hG₆ e = quadrilateralClassOf G hG₆ f) :
    QuadrilateralEquivalent G hG₆ e f := by
  exact Quotient.exact h

theorem same_class_of_quadrilateralEquivalent {e f : QEdge G}
    (h : QuadrilateralEquivalent G hG₆ e f) :
    quadrilateralClassOf G hG₆ e = quadrilateralClassOf G hG₆ f := by
  exact Quotient.sound h

/-- Every two edges of a class have both crossed incidences. -/
theorem adj_cross_of_same_class {e f : QEdge G}
    (h : quadrilateralClassOf G hG₆ e = quadrilateralClassOf G hG₆ f) :
    G.Adj e.1.1 f.1.2 ∧ G.Adj f.1.1 e.1.2 := by
  rcases quadrilateralEquivalent_of_same_class G hG₆ h with rfl | hef
  · exact ⟨e.2, e.2⟩
  · obtain ⟨a, b, hs, hf⟩ := hef
    have hcross := adj_of_inSquareAt G hs hf
    exact ⟨hcross.1, hcross.2.2.1⟩

/-- A quadrilateral class is complete between its incident vertex sides. -/
theorem class_complete {C : QuadrilateralClass G hG₆}
    {a : A} (ha : a ∈ classLeft G hG₆ C)
    {b : B} (hb : b ∈ classRight G hG₆ C) : G.Adj a b := by
  obtain ⟨e, heC, hea⟩ := (mem_classLeft G hG₆).1 ha
  obtain ⟨f, hfC, hfb⟩ := (mem_classRight G hG₆).1 hb
  have hcross := adj_cross_of_same_class G hG₆ (heC.trans hfC.symm)
  simpa [hea, hfb] using hcross.1

/-- Hexagon-freeness forces the smaller side of every complete class to have
at most two vertices. -/
theorem class_small_side (C : QuadrilateralClass G hG₆) :
    (classLeft G hG₆ C).card ≤ 2 ∨ (classRight G hG₆ C).card ≤ 2 := by
  classical
  by_contra h
  push_neg at h
  have hAL : Fintype.card (Fin 3) ≤ Fintype.card {a // a ∈ classLeft G hG₆ C} := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      (show 3 ≤ (classLeft G hG₆ C).card by omega)
  have hBR : Fintype.card (Fin 3) ≤ Fintype.card {b // b ∈ classRight G hG₆ C} := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      (show 3 ≤ (classRight G hG₆ C).card by omega)
  let ea : Fin 3 ↪ {a // a ∈ classLeft G hG₆ C} :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hAL)
  let eb : Fin 3 ↪ {b // b ∈ classRight G hG₆ C} :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hBR)
  let a₀ : A := ea 0
  let a₁ : A := ea 1
  let a₂ : A := ea 2
  let b₀ : B := eb 0
  let b₁ : B := eb 1
  let b₂ : B := eb 2
  have ha01 : a₀ ≠ a₁ := by
    intro hEq
    exact (by decide : (0 : Fin 3) ≠ 1) (ea.injective (Subtype.ext hEq))
  have ha12 : a₁ ≠ a₂ := by
    intro hEq
    exact (by decide : (1 : Fin 3) ≠ 2) (ea.injective (Subtype.ext hEq))
  have ha20 : a₂ ≠ a₀ := by
    intro hEq
    exact (by decide : (2 : Fin 3) ≠ 0) (ea.injective (Subtype.ext hEq))
  have hb01 : b₀ ≠ b₁ := by
    intro hEq
    exact (by decide : (0 : Fin 3) ≠ 1) (eb.injective (Subtype.ext hEq))
  have hb12 : b₁ ≠ b₂ := by
    intro hEq
    exact (by decide : (1 : Fin 3) ≠ 2) (eb.injective (Subtype.ext hEq))
  have hb20 : b₂ ≠ b₀ := by
    intro hEq
    exact (by decide : (2 : Fin 3) ≠ 0) (eb.injective (Subtype.ext hEq))
  exact hG₆ ha01 ha12 ha20 hb01 hb12 hb20
    (class_complete G hG₆ (ea 0).2 (eb 0).2)
    (class_complete G hG₆ (ea 1).2 (eb 0).2)
    (class_complete G hG₆ (ea 1).2 (eb 1).2)
    (class_complete G hG₆ (ea 2).2 (eb 1).2)
    (class_complete G hG₆ (ea 2).2 (eb 2).2)
    (class_complete G hG₆ (ea 0).2 (eb 2).2)

/-- A class is nontrivial when it contains two distinct edges. -/
def ClassNontrivial (C : QuadrilateralClass G hG₆) : Prop :=
  ∃ e f : QEdge G,
    quadrilateralClassOf G hG₆ e = C ∧
      quadrilateralClassOf G hG₆ f = C ∧ e ≠ f

private theorem sharesSquare_of_mem_nontrivial
    {C : QuadrilateralClass G hG₆} (hC : ClassNontrivial G hG₆ C)
    {e : QEdge G} (heC : quadrilateralClassOf G hG₆ e = C) :
    ∃ f : QEdge G, SharesSquare G e f := by
  obtain ⟨p, q, hpC, hqC, hpq⟩ := hC
  rcases quadrilateralEquivalent_of_same_class G hG₆ (heC.trans hpC.symm) with hep | hep
  · subst p
    rcases quadrilateralEquivalent_of_same_class G hG₆ (heC.trans hqC.symm) with heq | heq
    · exact (hpq heq).elim
    · exact ⟨q, heq⟩
  · exact ⟨p, hep⟩

/-- Every actual crossing of the two incident sides belongs to the class.
Together with `class_complete`, this says that a class is exactly a complete
bipartite graph. -/
theorem cross_edge_mem_class {C : QuadrilateralClass G hG₆}
    {a : A} (ha : a ∈ classLeft G hG₆ C)
    {b : B} (hb : b ∈ classRight G hG₆ C) (hab : G.Adj a b) :
    quadrilateralClassOf G hG₆ (⟨(a, b), hab⟩ : QEdge G) = C := by
  classical
  obtain ⟨e, heC, hea⟩ := (mem_classLeft G hG₆).1 ha
  by_cases hC : ClassNontrivial G hG₆ C
  · obtain ⟨f, hef⟩ := sharesSquare_of_mem_nontrivial G hG₆ hC heC
    obtain ⟨x, y, hs, hf⟩ := hef
    let ex : QEdge G := ⟨(x, e.1.2), hs.left_base⟩
    have heex : SharesSquare G e ex := by
      exact ⟨x, y, hs, Or.inr rfl, Or.inl rfl⟩
    have hexC : quadrilateralClassOf G hG₆ ex = C := by
      exact (same_class_of_quadrilateralEquivalent G hG₆ (Or.inr heex)).symm.trans heC
    have hxL : x ∈ classLeft G hG₆ C := by
      exact (mem_classLeft G hG₆).2 ⟨ex, hexC, rfl⟩
    by_cases hbe : b = e.1.2
    · have hge : (⟨(a, b), hab⟩ : QEdge G) = e := by
        apply Subtype.ext
        exact Prod.ext hea.symm hbe
      exact (congrArg (quadrilateralClassOf G hG₆) hge).trans heC
    · have hxb : G.Adj x b := class_complete G hG₆ hxL hb
      let g : QEdge G := ⟨(a, b), hab⟩
      have heg : SharesSquare G e g := by
        refine ⟨x, b, ?_, ?_⟩
        · exact ⟨hs.left_ne, hbe, hs.left_base,
            by simpa [hea] using hab, hxb⟩
        · exact ⟨Or.inl hea.symm, Or.inr rfl⟩
      exact (same_class_of_quadrilateralEquivalent G hG₆ (Or.inr heg)).symm.trans heC
  · obtain ⟨f, hfC, hfb⟩ := (mem_classRight G hG₆).1 hb
    have hef : e = f := by
      by_contra hne
      exact hC ⟨e, f, heC, hfC, hne⟩
    have hge : (⟨(a, b), hab⟩ : QEdge G) = e := by
      apply Subtype.ext
      exact Prod.ext hea.symm ((congrArg (fun z : QEdge G ↦ z.1.2) hef).trans hfb).symm
    exact (congrArg (quadrilateralClassOf G hG₆) hge).trans heC

/-- A componentwise edge choice.  The numerical fields say that at least
half of every degree inside the complete bipartite class is retained. -/
structure ComponentChoice (C : QuadrilateralClass G hG₆) where
  keep : A → B → Prop
  decidableKeep : DecidableRel keep
  keep_left : ∀ ⦃a b⦄, keep a b → a ∈ classLeft G hG₆ C
  keep_right : ∀ ⦃a b⦄, keep a b → b ∈ classRight G hG₆ C
  half_left : ∀ a ∈ classLeft G hG₆ C,
    (classRight G hG₆ C).card ≤
      2 * ((classRight G hG₆ C).filter fun b ↦ keep a b).card
  half_right : ∀ b ∈ classRight G hG₆ C,
    (classLeft G hG₆ C).card ≤
      2 * ((classLeft G hG₆ C).filter fun a ↦ keep a b).card
  no_four : ∀ ⦃a₀ a₁ b₀ b₁⦄, a₀ ≠ a₁ → b₀ ≠ b₁ →
    keep a₀ b₀ → keep a₁ b₀ → keep a₁ b₁ → keep a₀ b₁ → False

private noncomputable def allChoiceOfLeftSmall
    (C : QuadrilateralClass G hG₆) (hsmall : (classLeft G hG₆ C).card ≤ 1) :
    ComponentChoice G hG₆ C := by
  classical
  let K : A → B → Prop := fun a b ↦
    a ∈ classLeft G hG₆ C ∧ b ∈ classRight G hG₆ C
  letI : DecidableRel K := fun _ _ ↦ Classical.propDecidable _
  refine
    { keep := K
      decidableKeep := fun _ _ ↦ Classical.propDecidable _
      keep_left := by intro a b h; exact h.1
      keep_right := by intro a b h; exact h.2
      half_left := ?_
      half_right := ?_
      no_four := ?_ }
  · intro a ha
    have heq : (classRight G hG₆ C).filter (fun b ↦ K a b) =
        classRight G hG₆ C := by
      ext b
      constructor
      · exact fun h ↦ (Finset.mem_filter.mp h).1
      · exact fun h ↦ Finset.mem_filter.mpr ⟨h, ha, h⟩
    have hc := congrArg Finset.card heq
    calc
      (classRight G hG₆ C).card =
          ((classRight G hG₆ C).filter fun b ↦ K a b).card := hc.symm
      _ ≤ 2 * ((classRight G hG₆ C).filter fun b ↦ K a b).card := by
        omega
  · intro b hb
    have heq : (classLeft G hG₆ C).filter (fun a ↦ K a b) =
        classLeft G hG₆ C := by
      ext a
      constructor
      · exact fun h ↦ (Finset.mem_filter.mp h).1
      · exact fun h ↦ Finset.mem_filter.mpr ⟨h, h, hb⟩
    have hc := congrArg Finset.card heq
    calc
      (classLeft G hG₆ C).card =
          ((classLeft G hG₆ C).filter fun a ↦ K a b).card := hc.symm
      _ ≤ 2 * ((classLeft G hG₆ C).filter fun a ↦ K a b).card := by
        omega
  · intro a₀ a₁ b₀ b₁ ha hb h₀ h₁ h₂ h₃
    have hp : ({a₀, a₁} : Finset A) ⊆ classLeft G hG₆ C := by
      intro a ha'
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha'
      rcases ha' with rfl | rfl
      · exact h₀.1
      · exact h₁.1
    have hc := Finset.card_le_card hp
    simp [ha] at hc
    omega

private noncomputable def allChoiceOfRightSmall
    (C : QuadrilateralClass G hG₆) (hsmall : (classRight G hG₆ C).card ≤ 1) :
    ComponentChoice G hG₆ C := by
  classical
  let K : A → B → Prop := fun a b ↦
    a ∈ classLeft G hG₆ C ∧ b ∈ classRight G hG₆ C
  letI : DecidableRel K := fun _ _ ↦ Classical.propDecidable _
  refine
    { keep := K
      decidableKeep := fun _ _ ↦ Classical.propDecidable _
      keep_left := by intro a b h; exact h.1
      keep_right := by intro a b h; exact h.2
      half_left := ?_
      half_right := ?_
      no_four := ?_ }
  · intro a ha
    have heq : (classRight G hG₆ C).filter (fun b ↦ K a b) =
        classRight G hG₆ C := by
      ext b
      constructor
      · exact fun h ↦ (Finset.mem_filter.mp h).1
      · exact fun h ↦ Finset.mem_filter.mpr ⟨h, ha, h⟩
    have hc := congrArg Finset.card heq
    calc
      (classRight G hG₆ C).card =
          ((classRight G hG₆ C).filter fun b ↦ K a b).card := hc.symm
      _ ≤ 2 * ((classRight G hG₆ C).filter fun b ↦ K a b).card := by
        omega
  · intro b hb
    have heq : (classLeft G hG₆ C).filter (fun a ↦ K a b) =
        classLeft G hG₆ C := by
      ext a
      constructor
      · exact fun h ↦ (Finset.mem_filter.mp h).1
      · exact fun h ↦ Finset.mem_filter.mpr ⟨h, h, hb⟩
    have hc := congrArg Finset.card heq
    calc
      (classLeft G hG₆ C).card =
          ((classLeft G hG₆ C).filter fun a ↦ K a b).card := hc.symm
      _ ≤ 2 * ((classLeft G hG₆ C).filter fun a ↦ K a b).card := by
        omega
  · intro a₀ a₁ b₀ b₁ ha hb h₀ h₁ h₂ h₃
    have hp : ({b₀, b₁} : Finset B) ⊆ classRight G hG₆ C := by
      intro b hb'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
      rcases hb' with rfl | rfl
      · exact h₀.2
      · exact h₂.2
    have hc := Finset.card_le_card hp
    simp [hb] at hc
    omega

private noncomputable def choiceOfLeftTwo
    (C : QuadrilateralClass G hG₆)
    (hL : (classLeft G hG₆ C).card = 2)
    (hR : 2 ≤ (classRight G hG₆ C).card) : ComponentChoice G hG₆ C := by
  classical
  have hp := Finset.card_eq_two.mp hL
  let x : A := Classical.choose hp
  have hp' := Classical.choose_spec hp
  let y : A := Classical.choose hp'
  have hps := Classical.choose_spec hp'
  have hxy : x ≠ y := hps.1
  have hLeq : classLeft G hG₆ C = {x, y} := hps.2
  let R := classRight G hG₆ C
  have hTex := Finset.exists_subset_card_eq (s := R) (n := R.card / 2)
    (Nat.div_le_self _ _)
  let T : Finset B := Classical.choose hTex
  have hTs := Classical.choose_spec hTex
  have hTR : T ⊆ R := hTs.1
  have hTcard : T.card = R.card / 2 := hTs.2
  have hTlt : T.card < R.card := by
    rw [hTcard]
    have hR' : 0 < R.card := by simpa [R] using (show 0 < (classRight G hG₆ C).card by omega)
    exact Nat.div_lt_self hR' (by omega)
  have hnsub : ¬ R ⊆ T := by
    intro hRT
    exact (not_le_of_gt hTlt) (Finset.card_le_card hRT)
  have hrex : ∃ r, r ∈ R ∧ r ∉ T := by
    rw [Finset.not_subset] at hnsub
    exact hnsub
  let r : B := Classical.choose hrex
  have hrs := Classical.choose_spec hrex
  have hrR : r ∈ R := hrs.1
  have hrT : r ∉ T := hrs.2
  let K : A → B → Prop := fun a b ↦
    a ∈ classLeft G hG₆ C ∧ b ∈ R ∧
      ((a = x ∧ (b ∈ T ∨ b = r)) ∨ (a = y ∧ b ∉ T))
  letI : DecidableRel K := fun _ _ ↦ Classical.propDecidable _
  have hxL : x ∈ classLeft G hG₆ C := by simp [hLeq]
  have hyL : y ∈ classLeft G hG₆ C := by simp [hLeq]
  have hKx (b : B) (hb : b ∈ R) : K x b ↔ b ∈ T ∨ b = r := by
    constructor
    · intro h
      rcases h.2.2 with h | h
      · exact h.2
      · exact (hxy h.1).elim
    · intro h
      exact ⟨hxL, hb, Or.inl ⟨rfl, h⟩⟩
  have hKy (b : B) (hb : b ∈ R) : K y b ↔ b ∉ T := by
    constructor
    · intro h
      rcases h.2.2 with h | h
      · exact (hxy.symm h.1).elim
      · exact h.2
    · intro h
      exact ⟨hyL, hb, Or.inr ⟨rfl, h⟩⟩
  refine
    { keep := K
      decidableKeep := fun _ _ ↦ Classical.propDecidable _
      keep_left := by intro a b h; exact h.1
      keep_right := by intro a b h; exact h.2.1
      half_left := ?_
      half_right := ?_
      no_four := ?_ }
  · intro a ha
    have ha' : a = x ∨ a = y := by simpa [hLeq] using ha
    rcases ha' with rfl | rfl
    · have heq : R.filter (fun b ↦ K x b) = insert r T := by
        ext b
        constructor
        · intro hb
          have hbR := (Finset.mem_filter.mp hb).1
          rcases (hKx b hbR).mp (Finset.mem_filter.mp hb).2 with hbT | hbr
          · exact Finset.mem_insert.mpr (Or.inr hbT)
          · exact Finset.mem_insert.mpr (Or.inl hbr)
        · intro hb
          have hb' := Finset.mem_insert.mp hb
          have hbR : b ∈ R := by
            rcases hb' with rfl | hbT
            · exact hrR
            · exact hTR hbT
          exact Finset.mem_filter.mpr ⟨hbR, (hKx b hbR).mpr hb'.symm⟩
      have hc := congrArg Finset.card heq
      rw [Finset.card_insert_of_notMem hrT, hTcard] at hc
      have hi : R.card ≤ 2 * (R.filter fun b ↦ K x b).card := by omega
      simpa [R] using hi
    · have heq : R.filter (fun b ↦ K y b) = R \ T := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_sdiff]
        exact and_congr_right fun hbR ↦ hKy b hbR
      have hc := congrArg Finset.card heq
      rw [Finset.card_sdiff_of_subset hTR, hTcard] at hc
      have hi : R.card ≤ 2 * (R.filter fun b ↦ K y b).card := by omega
      simpa [R] using hi
  · intro b hb
    have hpos : 0 < ((classLeft G hG₆ C).filter fun a ↦ K a b).card := by
      apply Finset.card_pos.mpr
      by_cases hbT : b ∈ T
      · refine ⟨x, Finset.mem_filter.mpr ⟨hxL, ?_⟩⟩
        exact (hKx b hb).mpr (Or.inl hbT)
      · refine ⟨y, Finset.mem_filter.mpr ⟨hyL, ?_⟩⟩
        exact (hKy b hb).mpr hbT
    calc
      (classLeft G hG₆ C).card = 2 := hL
      _ ≤ 2 * ((classLeft G hG₆ C).filter fun a ↦ K a b).card := by
        omega
  · intro a₀ a₁ b₀ b₁ ha hb h₀ h₁ h₂ h₃
    have ha₀ : a₀ = x ∨ a₀ = y := by simpa [hLeq] using h₀.1
    have ha₁ : a₁ = x ∨ a₁ = y := by simpa [hLeq] using h₁.1
    have common : ∀ b ∈ R, K x b → K y b → b = r := by
      intro b hbR hxb hyb
      rcases (hKx b hbR).mp hxb with hbT | hbr
      · exact ((hKy b hbR).mp hyb hbT).elim
      · exact hbr
    rcases ha₀ with ha₀ | ha₀ <;> rcases ha₁ with ha₁ | ha₁
    · exact (ha (ha₀.trans ha₁.symm)).elim
    · have hb0r := common b₀ h₀.2.1 (ha₀ ▸ h₀) (ha₁ ▸ h₁)
      have hb1r := common b₁ h₂.2.1 (ha₀ ▸ h₃) (ha₁ ▸ h₂)
      exact hb (hb0r.trans hb1r.symm)
    · have hb0r := common b₀ h₀.2.1 (ha₁ ▸ h₁) (ha₀ ▸ h₀)
      have hb1r := common b₁ h₂.2.1 (ha₁ ▸ h₂) (ha₀ ▸ h₃)
      exact hb (hb0r.trans hb1r.symm)
    · exact (ha (ha₀.trans ha₁.symm)).elim

private noncomputable def choiceOfRightTwo
    (C : QuadrilateralClass G hG₆)
    (hR : (classRight G hG₆ C).card = 2)
    (hL : 2 ≤ (classLeft G hG₆ C).card) : ComponentChoice G hG₆ C := by
  classical
  have hp := Finset.card_eq_two.mp hR
  let x : B := Classical.choose hp
  have hp' := Classical.choose_spec hp
  let y : B := Classical.choose hp'
  have hps := Classical.choose_spec hp'
  have hxy : x ≠ y := hps.1
  have hReq : classRight G hG₆ C = {x, y} := hps.2
  let L := classLeft G hG₆ C
  have hTex := Finset.exists_subset_card_eq (s := L) (n := L.card / 2)
    (Nat.div_le_self _ _)
  let T : Finset A := Classical.choose hTex
  have hTs := Classical.choose_spec hTex
  have hTL : T ⊆ L := hTs.1
  have hTcard : T.card = L.card / 2 := hTs.2
  have hTlt : T.card < L.card := by
    rw [hTcard]
    have hL' : 0 < L.card := by simpa [L] using (show 0 < (classLeft G hG₆ C).card by omega)
    exact Nat.div_lt_self hL' (by omega)
  have hnsub : ¬ L ⊆ T := by
    intro hLT
    exact (not_le_of_gt hTlt) (Finset.card_le_card hLT)
  have hrex : ∃ r, r ∈ L ∧ r ∉ T := by
    rw [Finset.not_subset] at hnsub
    exact hnsub
  let r : A := Classical.choose hrex
  have hrs := Classical.choose_spec hrex
  have hrL : r ∈ L := hrs.1
  have hrT : r ∉ T := hrs.2
  let K : A → B → Prop := fun a b ↦
    a ∈ L ∧ b ∈ classRight G hG₆ C ∧
      ((b = x ∧ (a ∈ T ∨ a = r)) ∨ (b = y ∧ a ∉ T))
  letI : DecidableRel K := fun _ _ ↦ Classical.propDecidable _
  have hxR : x ∈ classRight G hG₆ C := by simp [hReq]
  have hyR : y ∈ classRight G hG₆ C := by simp [hReq]
  have hKx (a : A) (ha : a ∈ L) : K a x ↔ a ∈ T ∨ a = r := by
    constructor
    · intro h
      rcases h.2.2 with h | h
      · exact h.2
      · exact (hxy h.1).elim
    · intro h
      exact ⟨ha, hxR, Or.inl ⟨rfl, h⟩⟩
  have hKy (a : A) (ha : a ∈ L) : K a y ↔ a ∉ T := by
    constructor
    · intro h
      rcases h.2.2 with h | h
      · exact (hxy.symm h.1).elim
      · exact h.2
    · intro h
      exact ⟨ha, hyR, Or.inr ⟨rfl, h⟩⟩
  refine
    { keep := K
      decidableKeep := fun _ _ ↦ Classical.propDecidable _
      keep_left := by intro a b h; exact h.1
      keep_right := by intro a b h; exact h.2.1
      half_left := ?_
      half_right := ?_
      no_four := ?_ }
  · intro a ha
    have hpos : 0 < ((classRight G hG₆ C).filter fun b ↦ K a b).card := by
      apply Finset.card_pos.mpr
      by_cases haT : a ∈ T
      · refine ⟨x, Finset.mem_filter.mpr ⟨hxR, ?_⟩⟩
        exact (hKx a ha).mpr (Or.inl haT)
      · refine ⟨y, Finset.mem_filter.mpr ⟨hyR, ?_⟩⟩
        exact (hKy a ha).mpr haT
    calc
      (classRight G hG₆ C).card = 2 := hR
      _ ≤ 2 * ((classRight G hG₆ C).filter fun b ↦ K a b).card := by
        omega
  · intro b hb
    have hb' : b = x ∨ b = y := by simpa [hReq] using hb
    rcases hb' with rfl | rfl
    · have heq : L.filter (fun a ↦ K a x) = insert r T := by
        ext a
        constructor
        · intro ha
          have haL := (Finset.mem_filter.mp ha).1
          rcases (hKx a haL).mp (Finset.mem_filter.mp ha).2 with haT | har
          · exact Finset.mem_insert.mpr (Or.inr haT)
          · exact Finset.mem_insert.mpr (Or.inl har)
        · intro ha
          have ha' := Finset.mem_insert.mp ha
          have haL : a ∈ L := by
            rcases ha' with rfl | haT
            · exact hrL
            · exact hTL haT
          exact Finset.mem_filter.mpr ⟨haL, (hKx a haL).mpr ha'.symm⟩
      have hc := congrArg Finset.card heq
      rw [Finset.card_insert_of_notMem hrT, hTcard] at hc
      have hi : L.card ≤ 2 * (L.filter fun a ↦ K a x).card := by omega
      simpa [L] using hi
    · have heq : L.filter (fun a ↦ K a y) = L \ T := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_sdiff]
        exact and_congr_right fun haL ↦ hKy a haL
      have hc := congrArg Finset.card heq
      rw [Finset.card_sdiff_of_subset hTL, hTcard] at hc
      have hi : L.card ≤ 2 * (L.filter fun a ↦ K a y).card := by omega
      simpa [L] using hi
  · intro a₀ a₁ b₀ b₁ ha hb h₀ h₁ h₂ h₃
    have hb₀ : b₀ = x ∨ b₀ = y := by simpa [hReq] using h₀.2.1
    have hb₁ : b₁ = x ∨ b₁ = y := by simpa [hReq] using h₂.2.1
    have common : ∀ a ∈ L, K a x → K a y → a = r := by
      intro a haL hax hay
      rcases (hKx a haL).mp hax with haT | har
      · exact ((hKy a haL).mp hay haT).elim
      · exact har
    rcases hb₀ with hb₀ | hb₀ <;> rcases hb₁ with hb₁ | hb₁
    · exact (hb (hb₀.trans hb₁.symm)).elim
    · have ha0r := common a₀ h₀.1 (hb₀ ▸ h₀) (hb₁ ▸ h₃)
      have ha1r := common a₁ h₁.1 (hb₀ ▸ h₁) (hb₁ ▸ h₂)
      exact ha (ha0r.trans ha1r.symm)
    · have ha0r := common a₀ h₀.1 (hb₁ ▸ h₃) (hb₀ ▸ h₀)
      have ha1r := common a₁ h₁.1 (hb₁ ▸ h₂) (hb₀ ▸ h₁)
      exact ha (ha0r.trans ha1r.symm)
    · exact (hb (hb₀.trans hb₁.symm)).elim

/-- The balanced spanning-tree choice in every quadrilateral class. -/
noncomputable def componentChoice (C : QuadrilateralClass G hG₆) :
    ComponentChoice G hG₆ C := by
  classical
  by_cases hL₁ : (classLeft G hG₆ C).card ≤ 1
  · exact allChoiceOfLeftSmall G hG₆ C hL₁
  by_cases hR₁ : (classRight G hG₆ C).card ≤ 1
  · exact allChoiceOfRightSmall G hG₆ C hR₁
  by_cases hL₂ : (classLeft G hG₆ C).card ≤ 2
  · apply choiceOfLeftTwo G hG₆ C
    · omega
    · omega
  · apply choiceOfRightTwo G hG₆ C
    · rcases class_small_side G hG₆ C with h | h
      · exact (hL₂ h).elim
      · omega
    · omega

noncomputable local instance componentChoiceDecidableKeep
    (C : QuadrilateralClass G hG₆) :
    DecidableRel (componentChoice G hG₆ C).keep :=
  fun _ _ ↦ Classical.propDecidable _

noncomputable def incidentLeftEdges (C : QuadrilateralClass G hG₆) (a : A) :
    Finset (QEdge G) := by
  classical
  exact (classEdges G hG₆ C).filter fun e ↦ e.1.1 = a

noncomputable def incidentRightEdges (C : QuadrilateralClass G hG₆) (b : B) :
    Finset (QEdge G) := by
  classical
  exact (classEdges G hG₆ C).filter fun e ↦ e.1.2 = b

noncomputable def selectedLeftEdges (C : QuadrilateralClass G hG₆) (a : A) :
    Finset (QEdge G) := by
  classical
  exact (incidentLeftEdges G hG₆ C a).filter fun e ↦
    (componentChoice G hG₆ C).keep e.1.1 e.1.2

noncomputable def selectedRightEdges (C : QuadrilateralClass G hG₆) (b : B) :
    Finset (QEdge G) := by
  classical
  exact (incidentRightEdges G hG₆ C b).filter fun e ↦
    (componentChoice G hG₆ C).keep e.1.1 e.1.2

private theorem card_incidentLeftEdges (C : QuadrilateralClass G hG₆) (a : A) :
    (incidentLeftEdges G hG₆ C a).card =
      if a ∈ classLeft G hG₆ C then (classRight G hG₆ C).card else 0 := by
  classical
  by_cases ha : a ∈ classLeft G hG₆ C
  · rw [if_pos ha]
    have himage : (incidentLeftEdges G hG₆ C a).image (fun e ↦ e.1.2) =
        classRight G hG₆ C := by
      ext b
      constructor
      · intro hb
        obtain ⟨e, he, heb⟩ := Finset.mem_image.mp hb
        have he' := Finset.mem_filter.mp he
        exact (mem_classRight G hG₆).2
          ⟨e, (mem_classEdges G hG₆).1 he'.1, heb⟩
      · intro hb
        have hab := class_complete G hG₆ ha hb
        let e : QEdge G := ⟨(a, b), hab⟩
        have heC := cross_edge_mem_class G hG₆ ha hb hab
        apply Finset.mem_image.mpr
        exact ⟨e, Finset.mem_filter.mpr ⟨(mem_classEdges G hG₆).2 heC, rfl⟩, rfl⟩
    have hcard : ((incidentLeftEdges G hG₆ C a).image fun e ↦ e.1.2).card =
        (incidentLeftEdges G hG₆ C a).card := by
      rw [Finset.card_image_iff]
      intro e he f hf hef
      have hea := (Finset.mem_filter.mp he).2
      have hfa := (Finset.mem_filter.mp hf).2
      apply Subtype.ext
      exact Prod.ext (hea.trans hfa.symm) hef
    calc
      (incidentLeftEdges G hG₆ C a).card =
          ((incidentLeftEdges G hG₆ C a).image fun e ↦ e.1.2).card := hcard.symm
      _ = (classRight G hG₆ C).card := congrArg Finset.card himage
  · rw [if_neg ha]
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    have he' := Finset.mem_filter.mp he
    exact ha ((mem_classLeft G hG₆).2
      ⟨e, (mem_classEdges G hG₆).1 he'.1, he'.2⟩)

private theorem card_incidentRightEdges (C : QuadrilateralClass G hG₆) (b : B) :
    (incidentRightEdges G hG₆ C b).card =
      if b ∈ classRight G hG₆ C then (classLeft G hG₆ C).card else 0 := by
  classical
  by_cases hb : b ∈ classRight G hG₆ C
  · rw [if_pos hb]
    have himage : (incidentRightEdges G hG₆ C b).image (fun e ↦ e.1.1) =
        classLeft G hG₆ C := by
      ext a
      constructor
      · intro ha
        obtain ⟨e, he, hea⟩ := Finset.mem_image.mp ha
        have he' := Finset.mem_filter.mp he
        exact (mem_classLeft G hG₆).2
          ⟨e, (mem_classEdges G hG₆).1 he'.1, hea⟩
      · intro ha
        have hab := class_complete G hG₆ ha hb
        let e : QEdge G := ⟨(a, b), hab⟩
        have heC := cross_edge_mem_class G hG₆ ha hb hab
        apply Finset.mem_image.mpr
        exact ⟨e, Finset.mem_filter.mpr ⟨(mem_classEdges G hG₆).2 heC, rfl⟩, rfl⟩
    have hcard : ((incidentRightEdges G hG₆ C b).image fun e ↦ e.1.1).card =
        (incidentRightEdges G hG₆ C b).card := by
      rw [Finset.card_image_iff]
      intro e he f hf hef
      have heb := (Finset.mem_filter.mp he).2
      have hfb := (Finset.mem_filter.mp hf).2
      apply Subtype.ext
      exact Prod.ext hef (heb.trans hfb.symm)
    calc
      (incidentRightEdges G hG₆ C b).card =
          ((incidentRightEdges G hG₆ C b).image fun e ↦ e.1.1).card := hcard.symm
      _ = (classLeft G hG₆ C).card := congrArg Finset.card himage
  · rw [if_neg hb]
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    have he' := Finset.mem_filter.mp he
    exact hb ((mem_classRight G hG₆).2
      ⟨e, (mem_classEdges G hG₆).1 he'.1, he'.2⟩)

private theorem card_selectedLeftEdges (C : QuadrilateralClass G hG₆) (a : A) :
    (selectedLeftEdges G hG₆ C a).card =
      ((classRight G hG₆ C).filter fun b ↦
        (componentChoice G hG₆ C).keep a b).card := by
  classical
  let K := (componentChoice G hG₆ C).keep
  have himage : (selectedLeftEdges G hG₆ C a).image (fun e ↦ e.1.2) =
      (classRight G hG₆ C).filter fun b ↦ K a b := by
    ext b
    constructor
    · intro hb
      obtain ⟨e, he, heb⟩ := Finset.mem_image.mp hb
      have he' := Finset.mem_filter.mp he
      have hk : (componentChoice G hG₆ C).keep e.1.1 b := by
        rw [← heb]
        exact he'.2
      exact Finset.mem_filter.mpr ⟨(componentChoice G hG₆ C).keep_right hk,
        by simpa [K, (Finset.mem_filter.mp he'.1).2, heb] using he'.2⟩
    · intro hb
      have hb' := Finset.mem_filter.mp hb
      have ha := (componentChoice G hG₆ C).keep_left hb'.2
      have hab := class_complete G hG₆ ha hb'.1
      let e : QEdge G := ⟨(a, b), hab⟩
      have heC := cross_edge_mem_class G hG₆ ha hb'.1 hab
      apply Finset.mem_image.mpr
      exact ⟨e, Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨(mem_classEdges G hG₆).2 heC, rfl⟩, hb'.2⟩, rfl⟩
  have hcard : ((selectedLeftEdges G hG₆ C a).image fun e ↦ e.1.2).card =
      (selectedLeftEdges G hG₆ C a).card := by
    rw [Finset.card_image_iff]
    intro e he f hf hef
    have hea := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
    have hfa := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2
    apply Subtype.ext
    exact Prod.ext (hea.trans hfa.symm) hef
  exact hcard.symm.trans (congrArg Finset.card himage)

private theorem card_selectedRightEdges (C : QuadrilateralClass G hG₆) (b : B) :
    (selectedRightEdges G hG₆ C b).card =
      ((classLeft G hG₆ C).filter fun a ↦
        (componentChoice G hG₆ C).keep a b).card := by
  classical
  let K := (componentChoice G hG₆ C).keep
  have himage : (selectedRightEdges G hG₆ C b).image (fun e ↦ e.1.1) =
      (classLeft G hG₆ C).filter fun a ↦ K a b := by
    ext a
    constructor
    · intro ha
      obtain ⟨e, he, hea⟩ := Finset.mem_image.mp ha
      have he' := Finset.mem_filter.mp he
      have hk : (componentChoice G hG₆ C).keep a e.1.2 := by
        rw [← hea]
        exact he'.2
      exact Finset.mem_filter.mpr ⟨(componentChoice G hG₆ C).keep_left hk,
        by simpa [K, (Finset.mem_filter.mp he'.1).2, hea] using he'.2⟩
    · intro ha
      have ha' := Finset.mem_filter.mp ha
      have hb := (componentChoice G hG₆ C).keep_right ha'.2
      have hab := class_complete G hG₆ ha'.1 hb
      let e : QEdge G := ⟨(a, b), hab⟩
      have heC := cross_edge_mem_class G hG₆ ha'.1 hb hab
      apply Finset.mem_image.mpr
      exact ⟨e, Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨(mem_classEdges G hG₆).2 heC, rfl⟩, ha'.2⟩, rfl⟩
  have hcard : ((selectedRightEdges G hG₆ C b).image fun e ↦ e.1.1).card =
      (selectedRightEdges G hG₆ C b).card := by
    rw [Finset.card_image_iff]
    intro e he f hf hef
    have heb := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
    have hfb := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2
    apply Subtype.ext
    exact Prod.ext hef (heb.trans hfb.symm)
  exact hcard.symm.trans (congrArg Finset.card himage)

private theorem incidentLeft_half (C : QuadrilateralClass G hG₆) (a : A) :
    (incidentLeftEdges G hG₆ C a).card ≤
      2 * (selectedLeftEdges G hG₆ C a).card := by
  classical
  rw [card_incidentLeftEdges G hG₆, card_selectedLeftEdges G hG₆]
  by_cases ha : a ∈ classLeft G hG₆ C
  · rw [if_pos ha]
    have h := (componentChoice G hG₆ C).half_left a ha
    have hf :
        @Finset.filter B
            (fun b ↦ (componentChoice G hG₆ C).keep a b)
            ((componentChoice G hG₆ C).decidableKeep a)
            (classRight G hG₆ C) =
          (classRight G hG₆ C).filter fun b ↦
            (componentChoice G hG₆ C).keep a b :=
      Finset.filter_congr_decidable _ _ _
    rw [hf] at h
    exact h
  · rw [if_neg ha]
    omega

private theorem incidentRight_half (C : QuadrilateralClass G hG₆) (b : B) :
    (incidentRightEdges G hG₆ C b).card ≤
      2 * (selectedRightEdges G hG₆ C b).card := by
  classical
  rw [card_incidentRightEdges G hG₆, card_selectedRightEdges G hG₆]
  by_cases hb : b ∈ classRight G hG₆ C
  · rw [if_pos hb]
    have h := (componentChoice G hG₆ C).half_right b hb
    have hf :
        @Finset.filter A
            (fun a ↦ (componentChoice G hG₆ C).keep a b)
            (fun a ↦ (componentChoice G hG₆ C).decidableKeep a b)
            (classLeft G hG₆ C) =
          (classLeft G hG₆ C).filter fun a ↦
            (componentChoice G hG₆ C).keep a b :=
      Finset.filter_congr_decidable _ _ _
    rw [hf] at h
    exact h
  · rw [if_neg hb]
    omega

/-- The union of the balanced choices over all quadrilateral classes. -/
noncomputable def directLargeGirthSubgraph : Bigraph A B where
  Adj a b := ∃ h : G.Adj a b,
    (componentChoice G hG₆ (quadrilateralClassOf G hG₆ ⟨(a, b), h⟩)).keep a b

private theorem directLargeGirthSubgraph_le :
    (directLargeGirthSubgraph G hG₆).LE G := by
  rintro a b ⟨h, -⟩
  exact h

private theorem directLargeGirthSubgraph_noFour :
    (directLargeGirthSubgraph G hG₆).NoFourCycle := by
  classical
  intro a₀ a₁ b₀ b₁ ha hb h₀ h₁ h₂ h₃
  obtain ⟨hg₀, hk₀⟩ := h₀
  obtain ⟨hg₁, hk₁⟩ := h₁
  obtain ⟨hg₂, hk₂⟩ := h₂
  obtain ⟨hg₃, hk₃⟩ := h₃
  let e₀ : QEdge G := ⟨(a₀, b₀), hg₀⟩
  let e₁ : QEdge G := ⟨(a₁, b₀), hg₁⟩
  let e₂ : QEdge G := ⟨(a₁, b₁), hg₂⟩
  let e₃ : QEdge G := ⟨(a₀, b₁), hg₃⟩
  have hs : SquareAt G e₀ a₁ b₁ :=
    ⟨ha.symm, hb.symm, hg₁, hg₃, hg₂⟩
  have hin₁ : InSquareAt G e₀ a₁ b₁ e₁ := by
    simp [InSquareAt, e₀, e₁]
  have hin₂ : InSquareAt G e₀ a₁ b₁ e₂ := by
    simp [InSquareAt, e₀, e₂]
  have hin₃ : InSquareAt G e₀ a₁ b₁ e₃ := by
    simp [InSquareAt, e₀, e₃]
  have hc₁ : quadrilateralClassOf G hG₆ e₁ = quadrilateralClassOf G hG₆ e₀ := by
    exact (same_class_of_quadrilateralEquivalent G hG₆
      (Or.inr ⟨a₁, b₁, hs, hin₁⟩)).symm
  have hc₂ : quadrilateralClassOf G hG₆ e₂ = quadrilateralClassOf G hG₆ e₀ := by
    exact (same_class_of_quadrilateralEquivalent G hG₆
      (Or.inr ⟨a₁, b₁, hs, hin₂⟩)).symm
  have hc₃ : quadrilateralClassOf G hG₆ e₃ = quadrilateralClassOf G hG₆ e₀ := by
    exact (same_class_of_quadrilateralEquivalent G hG₆
      (Or.inr ⟨a₁, b₁, hs, hin₃⟩)).symm
  have hk₁' : (componentChoice G hG₆ (quadrilateralClassOf G hG₆ e₀)).keep a₁ b₀ := by
    change (componentChoice G hG₆ (quadrilateralClassOf G hG₆ e₁)).keep a₁ b₀ at hk₁
    rw [hc₁] at hk₁
    exact hk₁
  have hk₂' : (componentChoice G hG₆ (quadrilateralClassOf G hG₆ e₀)).keep a₁ b₁ := by
    change (componentChoice G hG₆ (quadrilateralClassOf G hG₆ e₂)).keep a₁ b₁ at hk₂
    rw [hc₂] at hk₂
    exact hk₂
  have hk₃' : (componentChoice G hG₆ (quadrilateralClassOf G hG₆ e₀)).keep a₀ b₁ := by
    change (componentChoice G hG₆ (quadrilateralClassOf G hG₆ e₃)).keep a₀ b₁ at hk₃
    rw [hc₃] at hk₃
    exact hk₃
  exact (componentChoice G hG₆ (quadrilateralClassOf G hG₆ e₀)).no_four
    ha hb hk₀ hk₁' hk₂' hk₃'

noncomputable def allLeftEdges (a : A) : Finset (QEdge G) := by
  classical
  exact Finset.univ.filter fun e ↦ e.1.1 = a

noncomputable def allRightEdges (b : B) : Finset (QEdge G) := by
  classical
  exact Finset.univ.filter fun e ↦ e.1.2 = b

noncomputable def allSelectedEdges : Finset (QEdge G) := by
  classical
  exact Finset.univ.filter fun e ↦
    (componentChoice G hG₆ (quadrilateralClassOf G hG₆ e)).keep e.1.1 e.1.2

noncomputable def allSelectedLeftEdges (a : A) : Finset (QEdge G) := by
  classical
  exact (allSelectedEdges G hG₆).filter fun e ↦ e.1.1 = a

noncomputable def allSelectedRightEdges (b : B) : Finset (QEdge G) := by
  classical
  exact (allSelectedEdges G hG₆).filter fun e ↦ e.1.2 = b

private theorem card_allLeftEdges (a : A) :
    (allLeftEdges G a).card = G.leftDegree a := by
  classical
  have himage : (allLeftEdges G a).image (fun e ↦ e.1.2) =
      Finset.univ.filter fun b ↦ G.Adj a b := by
    ext b
    constructor
    · intro hb
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hb
      have hea := (Finset.mem_filter.mp he).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hea] using e.2⟩
    · intro hb
      have hab := (Finset.mem_filter.mp hb).2
      let e : QEdge G := ⟨(a, b), hab⟩
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
  have hcard : ((allLeftEdges G a).image fun e ↦ e.1.2).card =
      (allLeftEdges G a).card := by
    rw [Finset.card_image_iff]
    intro e he f hf hef
    apply Subtype.ext
    exact Prod.ext ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm) hef
  exact hcard.symm.trans (congrArg Finset.card himage)

private theorem card_allRightEdges (b : B) :
    (allRightEdges G b).card = G.rightDegree b := by
  classical
  have himage : (allRightEdges G b).image (fun e ↦ e.1.1) =
      Finset.univ.filter fun a ↦ G.Adj a b := by
    ext a
    constructor
    · intro ha
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
      have heb := (Finset.mem_filter.mp he).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [heb] using e.2⟩
    · intro ha
      have hab := (Finset.mem_filter.mp ha).2
      let e : QEdge G := ⟨(a, b), hab⟩
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
  have hcard : ((allRightEdges G b).image fun e ↦ e.1.1).card =
      (allRightEdges G b).card := by
    rw [Finset.card_image_iff]
    intro e he f hf hef
    apply Subtype.ext
    exact Prod.ext hef ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
  exact hcard.symm.trans (congrArg Finset.card himage)

private theorem card_allSelectedLeftEdges (a : A) :
    (allSelectedLeftEdges G hG₆ a).card =
      @leftDegree A B _ (directLargeGirthSubgraph G hG₆)
        (fun _ _ ↦ Classical.propDecidable _) a := by
  classical
  have himage : (allSelectedLeftEdges G hG₆ a).image (fun e ↦ e.1.2) =
      Finset.univ.filter fun b ↦ (directLargeGirthSubgraph G hG₆).Adj a b := by
    ext b
    constructor
    · intro hb
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hb
      have he' := Finset.mem_filter.mp he
      have hea := he'.2
      have hk := (Finset.mem_filter.mp he'.1).2
      have hab : G.Adj a e.1.2 := by simpa [hea] using e.2
      let f : QEdge G := ⟨(a, e.1.2), hab⟩
      have hfe : f = e := by
        apply Subtype.ext
        exact Prod.ext hea.symm rfl
      have hkf :
          (componentChoice G hG₆ (quadrilateralClassOf G hG₆ f)).keep a e.1.2 := by
        rw [hfe]
        simpa [hea] using hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hab, hkf⟩⟩
    · intro hb
      obtain ⟨hab, hk⟩ := (Finset.mem_filter.mp hb).2
      let e : QEdge G := ⟨(a, b), hab⟩
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩, rfl⟩
  have hcard : ((allSelectedLeftEdges G hG₆ a).image fun e ↦ e.1.2).card =
      (allSelectedLeftEdges G hG₆ a).card := by
    rw [Finset.card_image_iff]
    intro e he f hf hef
    apply Subtype.ext
    exact Prod.ext ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm) hef
  exact hcard.symm.trans (congrArg Finset.card himage)

private theorem card_allSelectedRightEdges (b : B) :
    (allSelectedRightEdges G hG₆ b).card =
      @rightDegree A B _ (directLargeGirthSubgraph G hG₆)
        (fun _ _ ↦ Classical.propDecidable _) b := by
  classical
  have himage : (allSelectedRightEdges G hG₆ b).image (fun e ↦ e.1.1) =
      Finset.univ.filter fun a ↦ (directLargeGirthSubgraph G hG₆).Adj a b := by
    ext a
    constructor
    · intro ha
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
      have he' := Finset.mem_filter.mp he
      have heb := he'.2
      have hk := (Finset.mem_filter.mp he'.1).2
      have hab : G.Adj e.1.1 b := by simpa [heb] using e.2
      let f : QEdge G := ⟨(e.1.1, b), hab⟩
      have hfe : f = e := by
        apply Subtype.ext
        exact Prod.ext rfl heb.symm
      have hkf :
          (componentChoice G hG₆ (quadrilateralClassOf G hG₆ f)).keep e.1.1 b := by
        rw [hfe]
        simpa [heb] using hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hab, hkf⟩⟩
    · intro ha
      obtain ⟨hab, hk⟩ := (Finset.mem_filter.mp ha).2
      let e : QEdge G := ⟨(a, b), hab⟩
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩, rfl⟩
  have hcard : ((allSelectedRightEdges G hG₆ b).image fun e ↦ e.1.1).card =
      (allSelectedRightEdges G hG₆ b).card := by
    rw [Finset.card_image_iff]
    intro e he f hf hef
    apply Subtype.ext
    exact Prod.ext hef ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
  exact hcard.symm.trans (congrArg Finset.card himage)

private theorem allLeftEdges_partition (a : A) :
    (allLeftEdges G a).card =
      ∑ C : QuadrilateralClass G hG₆, (incidentLeftEdges G hG₆ C a).card := by
  classical
  calc
    (allLeftEdges G a).card =
        ∑ C ∈ (Finset.univ : Finset (QuadrilateralClass G hG₆)),
          ((allLeftEdges G a).filter fun e ↦
            quadrilateralClassOf G hG₆ e = C).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro e he
      exact Finset.mem_univ _
    _ = ∑ C : QuadrilateralClass G hG₆,
        (incidentLeftEdges G hG₆ C a).card := by
      apply Finset.sum_congr rfl
      intro C hC
      congr 1
      ext e
      simp [allLeftEdges, incidentLeftEdges, classEdges, and_comm]

private theorem allRightEdges_partition (b : B) :
    (allRightEdges G b).card =
      ∑ C : QuadrilateralClass G hG₆, (incidentRightEdges G hG₆ C b).card := by
  classical
  calc
    (allRightEdges G b).card =
        ∑ C ∈ (Finset.univ : Finset (QuadrilateralClass G hG₆)),
          ((allRightEdges G b).filter fun e ↦
            quadrilateralClassOf G hG₆ e = C).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro e he
      exact Finset.mem_univ _
    _ = ∑ C : QuadrilateralClass G hG₆,
        (incidentRightEdges G hG₆ C b).card := by
      apply Finset.sum_congr rfl
      intro C hC
      congr 1
      ext e
      simp [allRightEdges, incidentRightEdges, classEdges, and_comm]

private theorem allSelectedLeftEdges_partition (a : A) :
    (allSelectedLeftEdges G hG₆ a).card =
      ∑ C : QuadrilateralClass G hG₆, (selectedLeftEdges G hG₆ C a).card := by
  classical
  calc
    (allSelectedLeftEdges G hG₆ a).card =
        ∑ C ∈ (Finset.univ : Finset (QuadrilateralClass G hG₆)),
          ((allSelectedLeftEdges G hG₆ a).filter fun e ↦
            quadrilateralClassOf G hG₆ e = C).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro e he
      exact Finset.mem_univ _
    _ = ∑ C : QuadrilateralClass G hG₆,
        (selectedLeftEdges G hG₆ C a).card := by
      apply Finset.sum_congr rfl
      intro C hC
      congr 1
      ext e
      simp only [allSelectedLeftEdges, allSelectedEdges, selectedLeftEdges,
        incidentLeftEdges, classEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hk, hea⟩, heC⟩
        rw [heC] at hk
        exact ⟨⟨heC, hea⟩, hk⟩
      · rintro ⟨⟨heC, hea⟩, hk⟩
        subst C
        exact ⟨⟨hk, hea⟩, rfl⟩

private theorem allSelectedRightEdges_partition (b : B) :
    (allSelectedRightEdges G hG₆ b).card =
      ∑ C : QuadrilateralClass G hG₆, (selectedRightEdges G hG₆ C b).card := by
  classical
  calc
    (allSelectedRightEdges G hG₆ b).card =
        ∑ C ∈ (Finset.univ : Finset (QuadrilateralClass G hG₆)),
          ((allSelectedRightEdges G hG₆ b).filter fun e ↦
            quadrilateralClassOf G hG₆ e = C).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro e he
      exact Finset.mem_univ _
    _ = ∑ C : QuadrilateralClass G hG₆,
        (selectedRightEdges G hG₆ C b).card := by
      apply Finset.sum_congr rfl
      intro C hC
      congr 1
      ext e
      simp only [allSelectedRightEdges, allSelectedEdges, selectedRightEdges,
        incidentRightEdges, classEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hk, heb⟩, heC⟩
        rw [heC] at hk
        exact ⟨⟨heC, heb⟩, hk⟩
      · rintro ⟨⟨heC, heb⟩, hk⟩
        subst C
        exact ⟨⟨hk, heb⟩, rfl⟩

private theorem directLargeGirthSubgraph_half_left (a : A) :
    G.leftDegree a ≤
      2 * @leftDegree A B _ (directLargeGirthSubgraph G hG₆)
        (fun _ _ ↦ Classical.propDecidable _) a := by
  classical
  calc
    G.leftDegree a = (allLeftEdges G a).card := (card_allLeftEdges G a).symm
    _ = ∑ C : QuadrilateralClass G hG₆,
        (incidentLeftEdges G hG₆ C a).card := allLeftEdges_partition G hG₆ a
    _ ≤ ∑ C : QuadrilateralClass G hG₆,
        2 * (selectedLeftEdges G hG₆ C a).card := by
      exact Finset.sum_le_sum fun C hC ↦ incidentLeft_half G hG₆ C a
    _ = 2 * ∑ C : QuadrilateralClass G hG₆,
        (selectedLeftEdges G hG₆ C a).card := by rw [Finset.mul_sum]
    _ = 2 * (allSelectedLeftEdges G hG₆ a).card := by
      rw [allSelectedLeftEdges_partition G hG₆ a]
    _ = 2 * @leftDegree A B _ (directLargeGirthSubgraph G hG₆)
        (fun _ _ ↦ Classical.propDecidable _) a := by
      rw [card_allSelectedLeftEdges G hG₆ a]

private theorem directLargeGirthSubgraph_half_right (b : B) :
    G.rightDegree b ≤
      2 * @rightDegree A B _ (directLargeGirthSubgraph G hG₆)
        (fun _ _ ↦ Classical.propDecidable _) b := by
  classical
  calc
    G.rightDegree b = (allRightEdges G b).card := (card_allRightEdges G b).symm
    _ = ∑ C : QuadrilateralClass G hG₆,
        (incidentRightEdges G hG₆ C b).card := allRightEdges_partition G hG₆ b
    _ ≤ ∑ C : QuadrilateralClass G hG₆,
        2 * (selectedRightEdges G hG₆ C b).card := by
      exact Finset.sum_le_sum fun C hC ↦ incidentRight_half G hG₆ C b
    _ = 2 * ∑ C : QuadrilateralClass G hG₆,
        (selectedRightEdges G hG₆ C b).card := by rw [Finset.mul_sum]
    _ = 2 * (allSelectedRightEdges G hG₆ b).card := by
      rw [allSelectedRightEdges_partition G hG₆ b]
    _ = 2 * @rightDegree A B _ (directLargeGirthSubgraph G hG₆)
        (fun _ _ ↦ Classical.propDecidable _) b := by
      rw [card_allSelectedRightEdges G hG₆ b]

/-- The unconditional quadrilateral-forest certificate obtained directly from
hexagon-freeness. -/
noncomputable def quadrilateralForestCertificate_direct (hG₆ : G.NoSixCycle) :
    QuadrilateralForestCertificate G where
  F := directLargeGirthSubgraph G hG₆
  decidableAdj := fun _ _ ↦ Classical.propDecidable _
  le_graph := directLargeGirthSubgraph_le G hG₆
  noFourCycle := directLargeGirthSubgraph_noFour G hG₆
  half_left := directLargeGirthSubgraph_half_left G hG₆
  half_right := directLargeGirthSubgraph_half_right G hG₆

end

end Bigraph

end GirthDegree

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/U4Final.lean` -/

section
/-!
# The unconditional FNV U4 path bounds

This file proves the finite Hölder inequality, closes the global
Blakley--Roy/Hoory step, and then deletes the walks with a repeated vertex.
Thus the two final statements have no analytic or graph-theoretic hypotheses
beyond finiteness (and the displayed bipartition in the second statement).
-/

open scoped BigOperators

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Finite Hölder -/

private lemma u4_sum_mul_mul_pow_three_le
    {I : Type*} (s : Finset I) (a b c : I → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hc : ∀ i ∈ s, 0 ≤ c i) :
    (∑ i ∈ s, a i * b i * c i) ^ 3 ≤
      (∑ i ∈ s, a i ^ 3) * (∑ i ∈ s, b i ^ 3) *
        (∑ i ∈ s, c i ^ 3) := by
  have hthree : (3 : ℝ).HolderConjugate (3 / 2 : ℝ) := by
    constructor <;> norm_num
  have htwo : (2 : ℝ).HolderConjugate 2 := by
    constructor <;> norm_num
  have hA := Real.inner_le_Lp_mul_Lq_of_nonneg s hthree ha
    (fun i hi ↦ mul_nonneg (hb i hi) (hc i hi))
  have hBC := Real.inner_le_Lp_mul_Lq_of_nonneg s htwo
    (fun i hi ↦ Real.rpow_nonneg (hb i hi) _)
    (fun i hi ↦ Real.rpow_nonneg (hc i hi) _)
    (f := fun i ↦ b i ^ (3 / 2 : ℝ)) (g := fun i ↦ c i ^ (3 / 2 : ℝ))
  norm_num at hA hBC
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, a i * b i * c i :=
    Finset.sum_nonneg fun i hi ↦
      mul_nonneg (mul_nonneg (ha i hi) (hb i hi)) (hc i hi)
  have hA3 : 0 ≤ ∑ i ∈ s, a i ^ 3 :=
    Finset.sum_nonneg fun i hi ↦ pow_nonneg (ha i hi) _
  have hB3 : 0 ≤ ∑ i ∈ s, b i ^ 3 :=
    Finset.sum_nonneg fun i hi ↦ pow_nonneg (hb i hi) _
  have hC3 : 0 ≤ ∑ i ∈ s, c i ^ 3 :=
    Finset.sum_nonneg fun i hi ↦ pow_nonneg (hc i hi) _
  have hBC' :
      ∑ i ∈ s, (b i * c i) ^ (3 / 2 : ℝ) ≤
        (∑ i ∈ s, b i ^ 3) ^ (1 / 2 : ℝ) *
          (∑ i ∈ s, c i ^ 3) ^ (1 / 2 : ℝ) := by
    have hbpow :
        ∑ i ∈ s, (b i ^ (3 / 2 : ℝ)) ^ 2 = ∑ i ∈ s, b i ^ 3 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hb i hi)]
      norm_num
    have hcpow :
        ∑ i ∈ s, (c i ^ (3 / 2 : ℝ)) ^ 2 = ∑ i ∈ s, c i ^ 3 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hc i hi)]
      norm_num
    calc
      _ = ∑ i ∈ s, b i ^ (3 / 2 : ℝ) * c i ^ (3 / 2 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Real.mul_rpow (hb i hi) (hc i hi)
      _ ≤ ((∑ i ∈ s, (b i ^ (3 / 2 : ℝ)) ^ 2) ^ (1 / 2 : ℝ)) *
          ((∑ i ∈ s, (c i ^ (3 / 2 : ℝ)) ^ 2) ^ (1 / 2 : ℝ)) := hBC
      _ = _ := by rw [hbpow, hcpow]
  have hA' :
      ∑ i ∈ s, a i * b i * c i ≤
        (∑ i ∈ s, a i ^ 3) ^ (1 / 3 : ℝ) *
          (∑ i ∈ s, (b i * c i) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
    simpa only [mul_assoc] using hA
  calc
    (∑ i ∈ s, a i * b i * c i) ^ 3 ≤
        ((∑ i ∈ s, a i ^ 3) ^ (1 / 3 : ℝ) *
          (∑ i ∈ s, (b i * c i) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) ^ 3 :=
      pow_le_pow_left₀ hsum_nonneg hA' 3
    _ ≤ ((∑ i ∈ s, a i ^ 3) ^ (1 / 3 : ℝ) *
          (((∑ i ∈ s, b i ^ 3) ^ (1 / 2 : ℝ) *
            (∑ i ∈ s, c i ^ 3) ^ (1 / 2 : ℝ)) ^ (2 / 3 : ℝ))) ^ 3 := by
      apply pow_le_pow_left₀
      · exact mul_nonneg (Real.rpow_nonneg hA3 _)
          (Real.rpow_nonneg (Finset.sum_nonneg fun i hi ↦
            Real.rpow_nonneg (mul_nonneg (hb i hi) (hc i hi)) _) _)
      · apply mul_le_mul_of_nonneg_left
        · exact Real.rpow_le_rpow
            (Finset.sum_nonneg fun i hi ↦
              Real.rpow_nonneg (mul_nonneg (hb i hi) (hc i hi)) _)
            hBC' (by norm_num)
        · exact Real.rpow_nonneg hA3 _
    _ = (∑ i ∈ s, a i ^ 3) * (∑ i ∈ s, b i ^ 3) *
          (∑ i ∈ s, c i ^ 3) := by
      have hx : ((∑ i ∈ s, a i ^ 3) ^ (1 / 3 : ℝ)) ^ 3 =
          ∑ i ∈ s, a i ^ 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hA3]
        norm_num
      have hy : ((∑ i ∈ s, b i ^ 3) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) =
          ∑ i ∈ s, b i ^ 3 := by
        rw [← Real.rpow_mul hB3]
        norm_num
      have hz : ((∑ i ∈ s, c i ^ 3) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) =
          ∑ i ∈ s, c i ^ 3 := by
        rw [← Real.rpow_mul hC3]
        norm_num
      have hyz :
          ((((∑ i ∈ s, b i ^ 3) ^ (1 / 2 : ℝ) *
            (∑ i ∈ s, c i ^ 3) ^ (1 / 2 : ℝ)) ^ (2 / 3 : ℝ))) ^ 3 =
              (∑ i ∈ s, b i ^ 3) * (∑ i ∈ s, c i ^ 3) := by
        have hrootB : 0 ≤ (∑ i ∈ s, b i ^ 3) ^ (1 / 2 : ℝ) :=
          Real.rpow_nonneg hB3 _
        have hrootC : 0 ≤ (∑ i ∈ s, c i ^ 3) ^ (1 / 2 : ℝ) :=
          Real.rpow_nonneg hC3 _
        calc
          _ = (((∑ i ∈ s, b i ^ 3) ^ (1 / 2 : ℝ) *
              (∑ i ∈ s, c i ^ 3) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul
              (mul_nonneg hrootB hrootC)]
            norm_num
          _ = ((∑ i ∈ s, b i ^ 3) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) *
              ((∑ i ∈ s, c i ^ 3) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
            exact Real.mul_rpow hrootB hrootC
          _ = _ := by rw [hy, hz]
      rw [mul_pow, hx, hyz]
      ring

/-! ## Walk and path counts -/

def u4LocalPaths (u v : V) : Finset (V × V) :=
  (G.neighborFinset u ×ˢ G.neighborFinset v).filter fun p ↦
    p.1 ≠ v ∧ p.2 ≠ u ∧ p.1 ≠ p.2

def u4OrientedPathCount : ℕ :=
  ∑ u, ∑ v ∈ G.neighborFinset u, (u4LocalPaths G u v).card

def u4PathCount : ℝ := (u4OrientedPathCount G : ℝ) / 2

def u4OrientedWalkCount : ℕ :=
  ∑ u, ∑ v ∈ G.neighborFinset u, G.degree u * G.degree v

def u4OrientedEdgesBetween (A B : Finset V) : Finset (V × V) :=
  (A ×ˢ B).filter fun p ↦ G.Adj p.1 p.2

def u4WalkWeightBetween (A B : Finset V) : ℝ :=
  ∑ p ∈ u4OrientedEdgesBetween G A B,
    (G.degree p.1 : ℝ) * (G.degree p.2 : ℝ)

private lemma u4_rpow_third_mul_inv_thirds {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x * y) ^ (1 / 3 : ℝ) * x ^ (-1 / 3 : ℝ) * y ^ (-1 / 3 : ℝ) = 1 := by
  rw [Real.mul_rpow hx.le hy.le]
  calc
    (x ^ (1 / 3 : ℝ) * y ^ (1 / 3 : ℝ)) * x ^ (-1 / 3 : ℝ) *
        y ^ (-1 / 3 : ℝ) =
        (x ^ (1 / 3 : ℝ) * x ^ (-1 / 3 : ℝ)) *
          (y ^ (1 / 3 : ℝ) * y ^ (-1 / 3 : ℝ)) := by ring
    _ = x ^ ((1 / 3 : ℝ) + (-1 / 3 : ℝ)) *
          y ^ ((1 / 3 : ℝ) + (-1 / 3 : ℝ)) := by
      rw [Real.rpow_add hx, Real.rpow_add hy]
    _ = 1 := by norm_num

private lemma u4_rpow_third_cube {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private lemma u4_rpow_neg_third_cube {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (-1 / 3 : ℝ)) ^ 3 = x⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num [Real.rpow_neg_one]

private lemma u4_sum_inv_left_le (A B : Finset V) :
    ∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.1 : ℝ)⁻¹ ≤
      (A.card : ℝ) := by
  have hinner : ∀ u : V,
      (∑ v ∈ B, if G.Adj u v then (G.degree u : ℝ)⁻¹ else 0) =
        ((B.filter fun v ↦ G.Adj u v).card : ℝ) * (G.degree u : ℝ)⁻¹ := by
    intro u
    calc
      _ = (∑ v ∈ B, if G.Adj u v then (1 : ℝ) else 0) *
          (G.degree u : ℝ)⁻¹ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v hv
        split <;> simp_all
      _ = _ := by rw [Finset.sum_boole]
  calc
    ∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.1 : ℝ)⁻¹ =
        ∑ u ∈ A, ((B.filter fun v ↦ G.Adj u v).card : ℝ) *
          (G.degree u : ℝ)⁻¹ := by
      simp only [u4OrientedEdgesBetween, Finset.sum_filter, Finset.sum_product]
      exact Finset.sum_congr rfl fun u hu ↦ hinner u
    _ ≤ ∑ _u ∈ A, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      have hcard : (B.filter fun v ↦ G.Adj u v).card ≤ G.degree u := by
        rw [← G.card_neighborFinset_eq_degree]
        apply Finset.card_le_card
        intro v hv
        exact (G.mem_neighborFinset u v).2 (Finset.mem_filter.mp hv).2
      by_cases hd : G.degree u = 0
      · have hz : (B.filter fun v ↦ G.Adj u v).card = 0 := by omega
        simp [hd, hz]
      · rw [mul_inv_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd))]
        simpa only [one_mul] using (show
          ((B.filter fun v ↦ G.Adj u v).card : ℝ) ≤ G.degree u by
            exact_mod_cast hcard)
    _ = (A.card : ℝ) := by simp

private lemma u4_sum_inv_right_le (A B : Finset V) :
    ∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.2 : ℝ)⁻¹ ≤
      (B.card : ℝ) := by
  have hinner : ∀ v : V,
      (∑ u ∈ A, if G.Adj u v then (G.degree v : ℝ)⁻¹ else 0) =
        ((A.filter fun u ↦ G.Adj u v).card : ℝ) * (G.degree v : ℝ)⁻¹ := by
    intro v
    calc
      _ = (∑ u ∈ A, if G.Adj u v then (1 : ℝ) else 0) *
          (G.degree v : ℝ)⁻¹ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u hu
        split <;> simp_all
      _ = _ := by rw [Finset.sum_boole]
  calc
    ∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.2 : ℝ)⁻¹ =
        ∑ v ∈ B, ((A.filter fun u ↦ G.Adj u v).card : ℝ) *
          (G.degree v : ℝ)⁻¹ := by
      simp only [u4OrientedEdgesBetween, Finset.sum_filter, Finset.sum_product]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v hv
      exact hinner v
    _ ≤ ∑ _v ∈ B, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      have hcard : (A.filter fun u ↦ G.Adj u v).card ≤ G.degree v := by
        rw [← G.card_neighborFinset_eq_degree]
        apply Finset.card_le_card
        intro u hu
        exact (G.mem_neighborFinset v u).2 (Finset.mem_filter.mp hu).2.symm
      by_cases hd : G.degree v = 0
      · have hz : (A.filter fun u ↦ G.Adj u v).card = 0 := by omega
        simp [hd, hz]
      · rw [mul_inv_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd))]
        simpa only [one_mul] using (show
          ((A.filter fun u ↦ G.Adj u v).card : ℝ) ≤ G.degree v by
            exact_mod_cast hcard)
    _ = (B.card : ℝ) := by simp

private theorem u4_walkWeight_lower_bound (A B : Finset V) :
    ((u4OrientedEdgesBetween G A B).card : ℝ) ^ 3 /
        ((A.card : ℝ) * (B.card : ℝ)) ≤
      u4WalkWeightBetween G A B := by
  let E := u4OrientedEdgesBetween G A B
  let a : V × V → ℝ := fun p ↦
    ((G.degree p.1 : ℝ) * (G.degree p.2 : ℝ)) ^ (1 / 3 : ℝ)
  let b : V × V → ℝ := fun p ↦ (G.degree p.1 : ℝ) ^ (-1 / 3 : ℝ)
  let c : V × V → ℝ := fun p ↦ (G.degree p.2 : ℝ) ^ (-1 / 3 : ℝ)
  have hH := u4_sum_mul_mul_pow_three_le E a b c
    (fun p hp ↦ Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)
    (fun p hp ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun p hp ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hprod : ∑ p ∈ E, a p * b p * c p = (E.card : ℝ) := by
    calc
      _ = ∑ _p ∈ E, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hadj : G.Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
        exact u4_rpow_third_mul_inv_thirds
          (Nat.cast_pos.mpr hadj.degree_pos_left)
          (Nat.cast_pos.mpr hadj.degree_pos_right)
      _ = (E.card : ℝ) := by simp
  have ha3 : ∑ p ∈ E, a p ^ 3 = u4WalkWeightBetween G A B := by
    apply Finset.sum_congr rfl
    intro p hp
    exact u4_rpow_third_cube (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hb3 : ∑ p ∈ E, b p ^ 3 =
      ∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.1 : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro p hp
    exact u4_rpow_neg_third_cube (Nat.cast_nonneg _)
  have hc3 : ∑ p ∈ E, c p ^ 3 =
      ∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.2 : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro p hp
    exact u4_rpow_neg_third_cube (Nat.cast_nonneg _)
  rw [hprod, ha3, hb3, hc3] at hH
  have hweight : 0 ≤ u4WalkWeightBetween G A B := by
    exact Finset.sum_nonneg fun p hp ↦
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hmul : ((u4OrientedEdgesBetween G A B).card : ℝ) ^ 3 ≤
      u4WalkWeightBetween G A B * (A.card : ℝ) * (B.card : ℝ) := by
    calc
      _ ≤ u4WalkWeightBetween G A B *
          (∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.1 : ℝ)⁻¹) *
          (∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.2 : ℝ)⁻¹) := hH
      _ ≤ u4WalkWeightBetween G A B * (A.card : ℝ) *
          (∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.2 : ℝ)⁻¹) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (u4_sum_inv_left_le G A B) hweight
        · exact Finset.sum_nonneg fun p hp ↦ inv_nonneg.mpr (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (u4_sum_inv_right_le G A B)
        (mul_nonneg hweight (Nat.cast_nonneg _))
  by_cases hA : A.card = 0
  · simpa [hA, u4OrientedEdgesBetween] using hweight
  by_cases hB : B.card = 0
  · simpa [hB, u4OrientedEdgesBetween] using hweight
  rw [div_le_iff₀ (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hA))
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hB)))]
  simpa only [mul_assoc] using hmul

private lemma u4_orientedEdgesBetween_card_eq_sum (A B : Finset V) :
    (u4OrientedEdgesBetween G A B).card =
      ∑ u ∈ A, (B.filter fun v ↦ G.Adj u v).card := by
  calc
    _ = ∑ p ∈ u4OrientedEdgesBetween G A B, (1 : ℕ) := by simp
    _ = _ := by
      simp only [u4OrientedEdgesBetween, Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_boole (R := ℕ)]
      norm_num

private lemma u4_orientedEdgesBetween_univ_card :
    (u4OrientedEdgesBetween G Finset.univ Finset.univ).card =
      2 * G.edgeFinset.card := by
  rw [u4_orientedEdgesBetween_card_eq_sum]
  have hfilter : ∀ u : V,
      (Finset.univ.filter fun v ↦ G.Adj u v) = G.neighborFinset u := by
    intro u
    ext v
    simp [G.mem_neighborFinset]
  simp_rw [hfilter]
  simpa [G.card_neighborFinset_eq_degree] using G.sum_degrees_eq_twice_card_edges

private lemma u4_lengthThreeWalkWeightBetween_univ :
    u4WalkWeightBetween G Finset.univ Finset.univ =
      (u4OrientedWalkCount G : ℝ) := by
  have hfilter : ∀ u : V,
      (Finset.univ.filter fun v ↦ G.Adj u v) = G.neighborFinset u := by
    intro u
    ext v
    simp [G.mem_neighborFinset]
  have hinner : ∀ u : V,
      (∑ v, if G.Adj u v then
          (G.degree u : ℝ) * (G.degree v : ℝ) else 0) =
        ∑ v ∈ G.neighborFinset u,
          (G.degree u : ℝ) * (G.degree v : ℝ) := by
    intro u
    rw [← hfilter u, Finset.sum_filter]
  unfold u4WalkWeightBetween u4OrientedWalkCount
  push_cast
  simp only [u4OrientedEdgesBetween, Finset.sum_filter, Finset.sum_product,
    Finset.mem_univ, true_and]
  exact Finset.sum_congr rfl fun u hu ↦ hinner u

/-- The global Blakley--Roy inequality obtained from the finite three-factor
Hölder estimate, rather than assumed as an additional hypothesis. -/
theorem fnv_u4_oriented_walk_lower_bound :
    8 * (G.edgeFinset.card : ℝ) ^ 3 / (Fintype.card V : ℝ) ^ 2 ≤
      (u4OrientedWalkCount G : ℝ) := by
  have h := u4_walkWeight_lower_bound G
    (Finset.univ : Finset V) (Finset.univ : Finset V)
  rw [u4_orientedEdgesBetween_univ_card G,
    u4_lengthThreeWalkWeightBetween_univ G] at h
  norm_num [Nat.cast_mul, pow_two] at h ⊢
  convert h using 1 <;> ring

/-! ## Deleting repeated-vertex walks -/

private def u4BadLeft (u v : V) : Finset (V × V) :=
  (G.neighborFinset u ×ˢ G.neighborFinset v).filter fun p ↦ p.1 = v

private def u4BadRight (u v : V) : Finset (V × V) :=
  (G.neighborFinset u ×ˢ G.neighborFinset v).filter fun p ↦ p.2 = u

private def u4BadRepeat (u v : V) : Finset (V × V) :=
  (G.neighborFinset u ×ˢ G.neighborFinset v).filter fun p ↦ p.1 = p.2

private def u4BadChoices (u v : V) : Finset (V × V) :=
  (G.neighborFinset u ×ˢ G.neighborFinset v).filter fun p ↦
    ¬ (p.1 ≠ v ∧ p.2 ≠ u ∧ p.1 ≠ p.2)

private lemma u4_card_badLeft_le (u v : V) :
    (u4BadLeft G u v).card ≤ G.degree v := by
  rw [← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp q hq hpq
    apply Prod.ext
    · calc
        p.1 = v := (Finset.mem_filter.mp hp).2
        _ = q.1 := (Finset.mem_filter.mp hq).2.symm
    · exact hpq

private lemma u4_card_badRight_le (u v : V) :
    (u4BadRight G u v).card ≤ G.degree u := by
  rw [← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp q hq hpq
    apply Prod.ext
    · exact hpq
    · calc
        p.2 = u := (Finset.mem_filter.mp hp).2
        _ = q.2 := (Finset.mem_filter.mp hq).2.symm

private lemma u4_card_badRepeat_le (u v : V) :
    (u4BadRepeat G u v).card ≤ G.degree u := by
  rw [← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp q hq hpq
    apply Prod.ext hpq
    calc
      p.2 = p.1 := (Finset.mem_filter.mp hp).2.symm
      _ = q.1 := hpq
      _ = q.2 := (Finset.mem_filter.mp hq).2

private lemma u4_badChoices_subset (u v : V) :
    u4BadChoices G u v ⊆
      u4BadLeft G u v ∪ u4BadRight G u v ∪ u4BadRepeat G u v := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  simp only [u4BadLeft, u4BadRight, u4BadRepeat, Finset.mem_union,
    Finset.mem_filter]
  by_cases h₁ : p.1 = v
  · exact Or.inl (Or.inl ⟨hp'.1, h₁⟩)
  by_cases h₂ : p.2 = u
  · exact Or.inl (Or.inr ⟨hp'.1, h₂⟩)
  have h₃ : p.1 = p.2 := by
    by_contra h₃
    exact hp'.2 ⟨h₁, h₂, h₃⟩
  exact Or.inr ⟨hp'.1, h₃⟩

private lemma u4_local_walk_le_path_add {u v : V} (huv : G.Adj u v) :
    G.degree u * G.degree v ≤
      (u4LocalPaths G u v).card + G.degree v + G.degree u + G.maxDegree := by
  have hpartition :
      (u4LocalPaths G u v).card + (u4BadChoices G u v).card =
        G.degree u * G.degree v := by
    simpa [u4LocalPaths, u4BadChoices, Finset.card_product,
      G.card_neighborFinset_eq_degree] using
      (Finset.card_filter_add_card_filter_not
        (s := G.neighborFinset u ×ˢ G.neighborFinset v)
        (p := fun p : V × V ↦ p.1 ≠ v ∧ p.2 ≠ u ∧ p.1 ≠ p.2))
  have hbad : (u4BadChoices G u v).card ≤
      (u4BadLeft G u v).card + (u4BadRight G u v).card +
        (u4BadRepeat G u v).card := by
    exact (Finset.card_le_card (u4_badChoices_subset G u v)).trans
      ((Finset.card_union_le (u4BadLeft G u v ∪ u4BadRight G u v)
        (u4BadRepeat G u v)).trans (Nat.add_le_add_right
          (Finset.card_union_le (u4BadLeft G u v) (u4BadRight G u v)) _))
  have hrepeat := (u4_card_badRepeat_le G u v).trans (G.degree_le_maxDegree u)
  have hleft := u4_card_badLeft_le G u v
  have hright := u4_card_badRight_le G u v
  omega

private lemma u4_walk_le_path_add_six :
    u4OrientedWalkCount G ≤
      u4OrientedPathCount G + 6 * G.maxDegree * G.edgeFinset.card := by
  have hconst :
      (∑ u, ∑ _v ∈ G.neighborFinset u, 3 * G.maxDegree) =
        6 * G.maxDegree * G.edgeFinset.card := by
    calc
      _ = ∑ u, G.degree u * (3 * G.maxDegree) := by
        apply Finset.sum_congr rfl
        intro u hu
        simp [G.card_neighborFinset_eq_degree]
      _ = (∑ u, G.degree u) * (3 * G.maxDegree) := by
        rw [Finset.sum_mul]
      _ = _ := by
        rw [G.sum_degrees_eq_twice_card_edges]
        ring
  unfold u4OrientedWalkCount u4OrientedPathCount
  calc
    (∑ u, ∑ v ∈ G.neighborFinset u, G.degree u * G.degree v) ≤
        ∑ u, ∑ v ∈ G.neighborFinset u,
          ((u4LocalPaths G u v).card + 3 * G.maxDegree) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      have huv := (G.mem_neighborFinset u v).1 hv
      have hlocal := u4_local_walk_le_path_add G huv
      have huD := G.degree_le_maxDegree u
      have hvD := G.degree_le_maxDegree v
      omega
    _ = (∑ u, ∑ v ∈ G.neighborFinset u,
          (u4LocalPaths G u v).card) +
          (∑ u, ∑ _v ∈ G.neighborFinset u, 3 * G.maxDegree) := by
      simp_rw [Finset.sum_add_distrib]
    _ = _ := by rw [hconst]

/-- FNV U4, general form: an `n`-vertex finite simple graph with `e` edges
and maximum degree `Δ` has at least `4e³/n² - 3Δe` unoriented
three-edge paths. -/
theorem fnv_u4_general :
    4 * (G.edgeFinset.card : ℝ) ^ 3 / (Fintype.card V : ℝ) ^ 2 -
        3 * (G.maxDegree : ℝ) * G.edgeFinset.card ≤
      u4PathCount G := by
  have hwalk := fnv_u4_oriented_walk_lower_bound G
  have hdeleteNat := u4_walk_le_path_add_six G
  have hdelete : (u4OrientedWalkCount G : ℝ) ≤
      u4OrientedPathCount G +
        6 * (G.maxDegree : ℝ) * G.edgeFinset.card := by
    exact_mod_cast hdeleteNat
  unfold u4PathCount
  calc
    4 * (G.edgeFinset.card : ℝ) ^ 3 / (Fintype.card V : ℝ) ^ 2 -
        3 * (G.maxDegree : ℝ) * G.edgeFinset.card ≤
        ((u4OrientedWalkCount G : ℝ) -
          6 * (G.maxDegree : ℝ) * G.edgeFinset.card) / 2 := by
      rw [show 4 * (G.edgeFinset.card : ℝ) ^ 3 /
          (Fintype.card V : ℝ) ^ 2 -
          3 * (G.maxDegree : ℝ) * G.edgeFinset.card =
          (8 * (G.edgeFinset.card : ℝ) ^ 3 /
            (Fintype.card V : ℝ) ^ 2 -
            6 * (G.maxDegree : ℝ) * G.edgeFinset.card) / 2 by ring]
      exact div_le_div_of_nonneg_right
        (sub_le_sub_right hwalk _) (by norm_num)
    _ ≤ (u4OrientedPathCount G : ℝ) / 2 := by linarith

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/QuadrilateralComponents.lean` -/

section
/-!
# Quadrilateral components in a hexagon-free graph

This file supplies the finite, edge-level language used in the
Füredi--Naor--Verstraëte analysis of `C₆`-free graphs.  Two edges are related
when they occur on a common quadrilateral, and a quadrilateral component is an
equivalence class for the relation generated by these elementary moves.

The definitions near the end of the file are a literal certificate interface
for the structural lemma U1.  They record the three exceptional configurations
from the paper, strong inducedness, and a cover by at most ten maximal complete
bipartite pieces.  Keeping this data in one certificate makes the exact
dependency of the later multiplicity arguments explicit.
-/

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

attribute [local instance] Classical.propDecidable

noncomputable local instance : DecidableEq V := Classical.typeDecidableEq V

/-- An edge of `G`, carrying its proof of membership in the edge set. -/
abbrev GraphEdge := G.edgeSet

/-- Two edges share a quadrilateral when a simple closed walk of length four
contains both.  The edges need not be distinct. -/
def SharesQuadrilateral (e f : GraphEdge G) : Prop :=
  ∃ (v : V) (q : G.Walk v v), q.IsCycle ∧ q.length = 4 ∧
    e.1 ∈ q.edges ∧ f.1 ∈ q.edges

/-- The setoid generated by the quadrilateral relation. -/
def quadrilateralSetoid : Setoid (GraphEdge G) :=
  Relation.EqvGen.setoid (SharesQuadrilateral G)

/-- A quadrilateral component is an equivalence class of edges. -/
abbrev QuadrilateralComponent := Quotient (quadrilateralSetoid G)

/-- The component containing an edge. -/
def componentOf (e : GraphEdge G) : QuadrilateralComponent G :=
  Quotient.mk (quadrilateralSetoid G) e

section Finite

variable [Fintype V]

/-- The finite set of edges in a quadrilateral component. -/
def componentEdges (C : QuadrilateralComponent G) : Finset (GraphEdge G) :=
  Finset.univ.filter fun e ↦ componentOf G e = C

@[simp] theorem mem_componentEdges {C : QuadrilateralComponent G} {e : GraphEdge G} :
    e ∈ componentEdges G C ↔ componentOf G e = C := by
  simp [componentEdges]

@[simp] theorem mem_own_component (e : GraphEdge G) :
    e ∈ componentEdges G (componentOf G e) := by
  simp

theorem componentEdges_nonempty (C : QuadrilateralComponent G) :
    (componentEdges G C).Nonempty := by
  refine Quotient.inductionOn C ?_
  intro e
  exact ⟨e, mem_own_component G e⟩

theorem componentEdges_injective : Function.Injective (componentEdges G) := by
  intro C D hCD
  obtain ⟨e, heC⟩ := componentEdges_nonempty G C
  have heD : e ∈ componentEdges G D := by simpa [hCD] using heC
  exact ((mem_componentEdges G).1 heC).symm.trans ((mem_componentEdges G).1 heD)

@[simp] theorem componentEdges_eq_iff {C D : QuadrilateralComponent G} :
    componentEdges G C = componentEdges G D ↔ C = D := by
  exact componentEdges_injective G |>.eq_iff

/-- Vertices incident with at least one edge in the component. -/
def componentVertices (C : QuadrilateralComponent G) : Finset V :=
  Finset.univ.filter fun v ↦
    ∃ e ∈ componentEdges G C, v ∈ e.1.toFinset

@[simp] theorem mem_componentVertices {C : QuadrilateralComponent G} {v : V} :
    v ∈ componentVertices G C ↔
      ∃ e ∈ componentEdges G C, v ∈ e.1.toFinset := by
  simp [componentVertices]

/-- A component not participating in any quadrilateral is a singleton. -/
def IsSingletonComponent (C : QuadrilateralComponent G) : Prop :=
  (componentEdges G C).card = 1

end Finite

/-! ## Complete bipartite pieces -/

section Pieces

variable [Fintype V]

/-- An edge crosses two named vertex sets. -/
def EdgeCrosses (L R : Finset V) (e : GraphEdge G) : Prop :=
  ∃ x ∈ L, ∃ y ∈ R, e.1 = s(x, y)

/-- `p` is exactly the edge set of a complete bipartite graph with both sides
of size at least two.  Thus a piece always contains a quadrilateral. -/
def IsCompleteBipartitePiece (p : Finset (GraphEdge G)) : Prop :=
  ∃ L R : Finset V,
    Disjoint L R ∧ 2 ≤ L.card ∧ 2 ≤ R.card ∧
    (∀ x ∈ L, ∀ y ∈ R, G.Adj x y) ∧
    ∀ e : GraphEdge G, e ∈ p ↔ EdgeCrosses G L R e

/-- A maximal complete bipartite piece, maximal by inclusion of edge sets. -/
def IsMaximalCompleteBipartitePiece (p : Finset (GraphEdge G)) : Prop :=
  IsCompleteBipartitePiece G p ∧
    ∀ q : Finset (GraphEdge G), IsCompleteBipartitePiece G q → p ⊆ q → q = p

/-- A quadrilateral component which itself is one maximal complete bipartite
piece. -/
def IsMaximalCompleteBipartiteComponent (C : QuadrilateralComponent G) : Prop :=
  IsMaximalCompleteBipartitePiece G (componentEdges G C)

/-- A family of maximal complete bipartite pieces covers the component. -/
def IsMaximalBicliqueCover (C : QuadrilateralComponent G)
    (pieces : Finset (Finset (GraphEdge G))) : Prop :=
  (∀ p ∈ pieces, IsMaximalCompleteBipartitePiece G p) ∧
    componentEdges G C = pieces.biUnion id

/-- The uniform numerical part of U1. -/
def HasAtMostTenBicliquePieces (C : QuadrilateralComponent G) : Prop :=
  ∃ pieces : Finset (Finset (GraphEdge G)),
    pieces.card ≤ 10 ∧ IsMaximalBicliqueCover G C pieces

end Pieces

/-! ## Strong inducedness and the three exceptional types -/

/-- Exclusion of a simple six-cycle. -/
def WalkC6Free : Prop :=
  ∀ (v : V) (q : G.Walk v v), q.IsCycle → q.length ≠ 6

/-- Every path of length at most four whose endpoints lie in `S` stays in
`S`.  Since the exceptional component is induced on `S`, this is precisely
the strongly-induced condition used by Füredi--Naor--Verstraëte. -/
def StronglyInduced (S : Set V) : Prop :=
  ∀ ⦃u v : V⦄ (p : G.Walk u v), p.IsPath → p.length ≤ 4 →
    u ∈ S → v ∈ S → ∀ x ∈ p.support, x ∈ S

section Exceptional

variable [Fintype V]

/-- `p` contains exactly the edges of `G` induced by `S`. -/
def IsInducedEdgeSet (S : Finset V) (p : Finset (GraphEdge G)) : Prop :=
  ∀ e : GraphEdge G, e ∈ p ↔ e.1.toFinset ⊆ S

/-- The first exceptional FNV configuration: a triangle `a b c`, together
with all additional common neighbours of `a,b` and of `a,c`; the two sets
of additional neighbours are nonempty and disjoint. -/
structure ExceptionalTypeOne (C : QuadrilateralComponent G) where
  a : V
  b : V
  c : V
  A : Finset V
  B : Finset V
  triangle_ab : G.Adj a b
  triangle_bc : G.Adj b c
  triangle_ca : G.Adj c a
  A_nonempty : A.Nonempty
  B_nonempty : B.Nonempty
  A_disjoint_B : Disjoint A B
  mem_A : ∀ x, x ∈ A ↔ x ≠ c ∧ G.Adj a x ∧ G.Adj b x
  mem_B : ∀ x, x ∈ B ↔ x ≠ b ∧ G.Adj a x ∧ G.Adj c x
  vertices : componentVertices G C = insert a (insert b (insert c (A ∪ B)))
  induced : IsInducedEdgeSet G (componentVertices G C) (componentEdges G C)
  stronglyInduced : StronglyInduced G (componentVertices G C : Set V)

/-- The second exceptional FNV configuration: a `K₄` on `a,b,c,d`,
together with all the other common neighbours of `a,b`. -/
structure ExceptionalTypeTwo (C : QuadrilateralComponent G) where
  a : V
  b : V
  c : V
  d : V
  A : Finset V
  core_card : ({a, b, c, d} : Finset V).card = 4
  core_clique : ∀ x ∈ ({a, b, c, d} : Finset V),
    ∀ y ∈ ({a, b, c, d} : Finset V), x ≠ y → G.Adj x y
  mem_A : ∀ x, x ∈ A ↔ x ≠ c ∧ x ≠ d ∧ G.Adj a x ∧ G.Adj b x
  vertices : componentVertices G C = insert a (insert b (insert c (insert d A)))
  induced : IsInducedEdgeSet G (componentVertices G C) (componentEdges G C)
  stronglyInduced : StronglyInduced G (componentVertices G C : Set V)

/-- The third exceptional FNV configuration: an induced five-vertex graph
of minimum internal degree at least three. -/
structure ExceptionalTypeThree (C : QuadrilateralComponent G) where
  S : Finset V
  card_S : S.card = 5
  vertices : componentVertices G C = S
  induced : IsInducedEdgeSet G S (componentEdges G C)
  minDegree : ∀ x ∈ S, 3 ≤ (S.erase x |>.filter fun y ↦ G.Adj x y).card
  stronglyInduced : StronglyInduced G (S : Set V)

/-- The disjunction of the three exceptional configurations. -/
def IsExceptionalComponent (C : QuadrilateralComponent G) : Prop :=
  Nonempty (ExceptionalTypeOne G C) ∨ Nonempty (ExceptionalTypeTwo G C) ∨
    Nonempty (ExceptionalTypeThree G C)

end Exceptional

/-! ## The finite U1 certificate -/

section Certificate

variable [Fintype V]

/-- The five mutually named outcomes in the U1 classification.  A bounded
biclique cover is stored for exceptional components because it is the exact
piece of the Appendix classification consumed by the later path-counting
argument. -/
inductive U1ComponentClassification (C : QuadrilateralComponent G) : Prop
  | singleton (h : IsSingletonComponent G C)
  | maximalBiclique (h : IsMaximalCompleteBipartiteComponent G C)
  | exceptionalOne (shape : ExceptionalTypeOne G C)
      (pieces : HasAtMostTenBicliquePieces G C)
  | exceptionalTwo (shape : ExceptionalTypeTwo G C)
      (pieces : HasAtMostTenBicliquePieces G C)
  | exceptionalThree (shape : ExceptionalTypeThree G C)
      (pieces : HasAtMostTenBicliquePieces G C)

/-- A finite certificate for FNV U1 on `G`. -/
structure U1Certificate : Prop where
  c6Free : WalkC6Free G
  classify : ∀ C : QuadrilateralComponent G, U1ComponentClassification G C

theorem U1ComponentClassification.shape_disjunction
    {C : QuadrilateralComponent G} (h : U1ComponentClassification G C) :
    IsSingletonComponent G C ∨ IsMaximalCompleteBipartiteComponent G C ∨
      IsExceptionalComponent G C := by
  cases h with
  | singleton hs => exact Or.inl hs
  | maximalBiclique hb => exact Or.inr (Or.inl hb)
  | exceptionalOne hs _ => exact Or.inr (Or.inr (Or.inl ⟨hs⟩))
  | exceptionalTwo hs _ => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hs⟩)))
  | exceptionalThree hs _ => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hs⟩)))

/-- U1, projected to its classification statement. -/
theorem U1Certificate.classification (h : U1Certificate G)
    (C : QuadrilateralComponent G) :
    IsSingletonComponent G C ∨ IsMaximalCompleteBipartiteComponent G C ∨
      IsExceptionalComponent G C :=
  (h.classify C).shape_disjunction

end Certificate

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/GeneralMultiplicity.lean` -/

section
/-!
# The Füredi--Naor--Verstraëte general multiplicity estimate

This file isolates the finite counting part of Lemma 8.1 of Füredi--Naor--Verstraëte.
Length-three paths are stored with their smaller endpoint first, so every unoriented path is
counted exactly once.  The central (degenerate) contribution is charged to closed
neighbourhoods and costs `25 * Δ * e`; the remaining pairs are charged to the
quadrilateral components and cost `10 * Δ * e`.

The lengthy local classification of quadrilateral components is represented by the concrete
certificate `GeneralMultiplicityCertificate`.  Its fields are precisely the three estimates
used in the published proof: the Erdos--Gallai open-neighbourhood estimate, the count by pairs
of disjoint edges in a closed neighbourhood, and the ten-piece component charge.  No
asymptotic or infinitary assertion occurs here.
-/

open scoped BigOperators
open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

attribute [local instance] Classical.propDecidable

/-- An unordered pair, represented by putting its smaller vertex first. -/
abbrev EndpointPair (V : Type u) [LinearOrder V] := {q : V × V // q.1 < q.2}

/-- A four-tuple is a three-edge simple path when consecutive vertices are adjacent and all
four vertices are different. -/
def IsPath3 (p : Fin 4 → V) : Prop :=
  Function.Injective p ∧
    G.Adj (p 0) (p 1) ∧ G.Adj (p 1) (p 2) ∧ G.Adj (p 2) (p 3)

/-- Unoriented paths of length three.  The endpoint order chooses one of the two orientations. -/
def Path3 := {p : Fin 4 → V // IsPath3 G p ∧ p 0 < p 3}

noncomputable instance : Fintype (Path3 G) :=
  Fintype.subtype
    (Finset.univ.filter fun p : Fin 4 → V ↦ IsPath3 G p ∧ p 0 < p 3)
    (fun _ ↦ by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
instance : DecidableEq (Path3 G) := inferInstance

namespace Path3

/-- The vertex at position `i` of a length-three path. -/
def vertex {G : SimpleGraph V} (p : Path3 G) (i : Fin 4) : V := p.1 i

@[simp] theorem vertex_mk {G : SimpleGraph V} (p : Fin 4 → V) (hp) (i : Fin 4) :
    (show Path3 G from ⟨p, hp⟩).vertex i = p i := rfl

/-- The (canonically ordered) endpoint pair of a path. -/
def endpoints {G : SimpleGraph V} (p : Path3 G) : EndpointPair V :=
  ⟨(p.vertex 0, p.vertex 3), p.2.2⟩

@[simp] theorem endpoints_fst {G : SimpleGraph V} (p : Path3 G) :
    p.endpoints.1.1 = p.vertex 0 := rfl
@[simp] theorem endpoints_snd {G : SimpleGraph V} (p : Path3 G) :
    p.endpoints.1.2 = p.vertex 3 := rfl

theorem injective {G : SimpleGraph V} (p : Path3 G) : Function.Injective p.vertex := p.2.1.1

theorem adj_zero_one {G : SimpleGraph V} (p : Path3 G) :
    G.Adj (p.vertex 0) (p.vertex 1) := p.2.1.2.1
theorem adj_one_two {G : SimpleGraph V} (p : Path3 G) :
    G.Adj (p.vertex 1) (p.vertex 2) := p.2.1.2.2.1
theorem adj_two_three {G : SimpleGraph V} (p : Path3 G) :
    G.Adj (p.vertex 2) (p.vertex 3) := p.2.1.2.2.2

end Path3

/-- All length-three paths with endpoint pair `pi`. -/
def pathFiber (pi : EndpointPair V) : Finset (Path3 G) :=
  Finset.univ.filter fun p ↦ p.endpoints = pi

@[simp] theorem mem_pathFiber {pi : EndpointPair V} {p : Path3 G} :
    p ∈ pathFiber G pi ↔ p.endpoints = pi := by
  simp [pathFiber]

/-- The FNV multiplicity `|pi|`. -/
def pathMultiplicity (pi : EndpointPair V) : ℕ := (pathFiber G pi).card

/-- The closed neighbourhood of a vertex. -/
def closedNeighborFinset (v : V) : Finset V := insert v (G.neighborFinset v)

@[simp] theorem mem_closedNeighborFinset {v w : V} :
    w ∈ closedNeighborFinset G v ↔ w = v ∨ G.Adj v w := by
  simp [closedNeighborFinset]

/-- Paths lying wholly in the closed neighbourhood of `v`. -/
def closedNeighborhoodPaths (v : V) : Finset (Path3 G) :=
  Finset.univ.filter fun p ↦ ∀ i, p.vertex i ∈ closedNeighborFinset G v

@[simp] theorem mem_closedNeighborhoodPaths {v : V} {p : Path3 G} :
    p ∈ closedNeighborhoodPaths G v ↔
      ∀ i, p.vertex i ∈ closedNeighborFinset G v := by
  simp [closedNeighborhoodPaths]

/-- Edges having both endpoints in the open neighbourhood of `v`. -/
def openNeighborhoodEdges (v : V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ ∀ w ∈ e, w ∈ G.neighborFinset v

/-- The number of edges in the closed neighbourhood, split into the `degree v` star edges
and the edges internal to the open neighbourhood. -/
def closedNeighborhoodEdgeCount (v : V) : ℕ :=
  G.degree v + (openNeighborhoodEdges G v).card

/-- A path fibre is central when all its paths lie in one closed neighbourhood.  This is the
spanning-star characterization in FNV Lemma 5.2. -/
def IsCentralPair (pi : EndpointPair V) : Prop :=
  ∃ v, ∀ p ∈ pathFiber G pi, ∀ i, p.vertex i ∈ closedNeighborFinset G v

/-- FNV degeneracy, using the equivalent central-union characterization of Lemma 5.2. -/
def IsDegeneratePair (pi : EndpointPair V) : Prop := IsCentralPair G pi

/-- Pairs used in FNV Lemma 6.1: adjacent pairs of multiplicity at least two, and all pairs
of multiplicity at least three. -/
def ordinaryExceptionalPairs : Finset (EndpointPair V) :=
  Finset.univ.filter fun pi ↦
    (2 ≤ pathMultiplicity G pi ∧
      G.Adj pi.1.1 pi.1.2) ∨ 3 ≤ pathMultiplicity G pi

/-- Degenerate pairs having at least two paths. -/
def degeneratePairs : Finset (EndpointPair V) :=
  Finset.univ.filter fun pi ↦ 2 ≤ pathMultiplicity G pi ∧ IsDegeneratePair G pi

/-- The concrete set `Pi ∪ Pi*` from FNV Lemma 8.1. -/
def generalExceptionalPairs : Finset (EndpointPair V) :=
  ordinaryExceptionalPairs G ∪ degeneratePairs G

/-- The part of `Pi` not already charged as degenerate. -/
def nondegenerateExceptionalPairs : Finset (EndpointPair V) :=
  ordinaryExceptionalPairs G \ degeneratePairs G

/-- Sum of the endpoint-pair multiplicities over a finite family. -/
def multiplicitySum (pairs : Finset (EndpointPair V)) : ℕ :=
  ∑ pi ∈ pairs, pathMultiplicity G pi

theorem generalExceptionalPairs_eq :
    generalExceptionalPairs G =
      degeneratePairs G ∪ nondegenerateExceptionalPairs G := by
  ext pi
  simp only [generalExceptionalPairs, nondegenerateExceptionalPairs, mem_union, mem_sdiff]
  tauto

theorem degenerate_disjoint_nondegenerate :
    Disjoint (degeneratePairs G) (nondegenerateExceptionalPairs G) := by
  unfold nondegenerateExceptionalPairs
  exact Finset.disjoint_sdiff

/-- The actual edge sets of the exceptional quadrilateral components. -/
abbrev ComponentEdgeSet (V : Type u) := Finset (Sym2 V)

/-- A component charge records the at-most-ten maximal-complete-bipartite-piece part of the
FNV quadrilateral-component classification.  The edge sets remain concrete edge sets of `G`.
-/
structure ExceptionalComponentCharge where
  components : Finset (ComponentEdgeSet V)
  componentOf : EndpointPair V → ComponentEdgeSet V
  component_mem : ∀ pi ∈ nondegenerateExceptionalPairs G,
    componentOf pi ∈ components
  edge_subset : ∀ C ∈ components, C ⊆ G.edgeFinset
  pieces : ComponentEdgeSet V → Finset (ComponentEdgeSet V)
  pieces_le_ten : ∀ C ∈ components, (pieces C).card ≤ 10
  local_charge : ∀ C ∈ components,
    ∑ pi ∈ (nondegenerateExceptionalPairs G).filter (componentOf · = C),
        pathMultiplicity G pi ≤ 10 * G.maxDegree * C.card
  edge_budget : ∑ C ∈ components, C.card ≤ G.edgeFinset.card

/-- The precise finite hypotheses consumed by the counting part of FNV Lemma 8.1. -/
structure GeneralMultiplicityCertificate where
  /-- Lemma 5.2, including a consistent choice of a centre for every degenerate pair. -/
  center : EndpointPair V → V
  center_spec : ∀ pi ∈ degeneratePairs G, ∀ p ∈ pathFiber G pi, ∀ i,
    p.vertex i ∈ closedNeighborFinset G (center pi)
  /-- Disjoint endpoint fibres charged to their chosen central closed neighbourhoods. -/
  central_charge :
    multiplicitySum G (degeneratePairs G) ≤
      ∑ v, (closedNeighborhoodPaths G v).card
  /-- Choosing two disjoint end edges of a path gives the factor `2 e[v]^2`. -/
  closed_path_pair_count : ∀ v,
    (closedNeighborhoodPaths G v).card ≤ 2 * (closedNeighborhoodEdgeCount G v) ^ 2
  /-- Erdos--Gallai on the `P_5`-free graph induced by the open neighbourhood. -/
  erdos_gallai_neighborhood : ∀ v,
    2 * (openNeighborhoodEdges G v).card ≤ 3 * G.degree v
  /-- The exceptional-component classification and its at-most-ten-piece charge. -/
  exceptionalComponents : ExceptionalComponentCharge G

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/ErdosGallai.lean` -/

section
/-!
# The finite Erdős--Gallai bound for `P₅`

The result is stated directly in the form used in the FNV closed-neighbourhood
argument: a finite simple graph with no injective four-edge path has at most
`3 |V| / 2` edges.
-/

noncomputable section

private lemma fin5_vector_injective {V : Type*} {a b c d e : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    Function.Injective ![a, b, c, d, e] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private lemma exists_path5_of_min_degree_two_of_degree_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hmin : ∀ w : V, 2 ≤ H.degree w) {v : V} (hv : 4 ≤ H.degree v) :
    ∃ p : Fin 5 → V, Function.Injective p ∧
      H.Adj (p 0) (p 1) ∧ H.Adj (p 1) (p 2) ∧
        H.Adj (p 2) (p 3) ∧ H.Adj (p 3) (p 4) := by
  have hvcard : 3 < (H.neighborFinset v).card := by
    rw [H.card_neighborFinset_eq_degree]
    omega
  obtain ⟨a, b₀, c₀, d₀, ha, hb₀, hc₀, hd₀,
      hab₀, hac₀, had₀, hb₀c₀, hb₀d₀, hc₀d₀⟩ :=
    Finset.three_lt_card_iff.mp hvcard
  have hva : H.Adj v a := (H.mem_neighborFinset v a).1 ha
  have hav : a ≠ v := hva.ne.symm
  have hacard : 1 < (H.neighborFinset a).card := by
    rw [H.card_neighborFinset_eq_degree]
    exact (hmin a)
  obtain ⟨x, hxmem, hxv⟩ := Finset.exists_mem_ne hacard v
  have hax : H.Adj a x := (H.mem_neighborFinset a x).1 hxmem
  have hxa : x ≠ a := hax.ne.symm
  obtain ⟨b, c, hb, hc, hab, hac, hbc, hxb, hxc⟩ :
      ∃ b c : V, b ∈ H.neighborFinset v ∧ c ∈ H.neighborFinset v ∧
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ x ≠ b ∧ x ≠ c := by
    by_cases hxb₀ : x = b₀
    · refine ⟨c₀, d₀, hc₀, hd₀, hac₀, had₀, hc₀d₀, ?_, ?_⟩
      · simpa [hxb₀] using hb₀c₀
      · simpa [hxb₀] using hb₀d₀
    · by_cases hxc₀ : x = c₀
      · refine ⟨b₀, d₀, hb₀, hd₀, hab₀, had₀, hb₀d₀,
          hxb₀, ?_⟩
        simpa [hxc₀] using hc₀d₀
      · exact ⟨b₀, c₀, hb₀, hc₀, hab₀, hac₀, hb₀c₀,
          hxb₀, hxc₀⟩
  have hvb : H.Adj v b := (H.mem_neighborFinset v b).1 hb
  have hvc : H.Adj v c := (H.mem_neighborFinset v c).1 hc
  have hbv : b ≠ v := hvb.ne.symm
  have hcv : c ≠ v := hvc.ne.symm
  have hbcard : 1 < (H.neighborFinset b).card := by
    rw [H.card_neighborFinset_eq_degree]
    exact hmin b
  obtain ⟨y, hymem, hyv⟩ := Finset.exists_mem_ne hbcard v
  have hby : H.Adj b y := (H.mem_neighborFinset b y).1 hymem
  have hyb : y ≠ b := hby.ne.symm
  by_cases hya : y = a
  · let p : Fin 5 → V := ![x, a, b, v, c]
    refine ⟨p, ?_, ?_⟩
    · exact fin5_vector_injective hxa hxb hxv hxc hab hav hac hbv hbc hcv.symm
    · dsimp [p]
      exact ⟨hax.symm, hya ▸ hby.symm, hvb.symm, hvc⟩
  · by_cases hyx : y = x
    · let p : Fin 5 → V := ![c, v, a, x, b]
      refine ⟨p, ?_, ?_⟩
      · exact fin5_vector_injective hcv hac.symm hxc.symm hbc.symm hav.symm
          hxv.symm hbv.symm hxa.symm hab hxb
      · dsimp [p]
        exact ⟨hvc.symm, hva, hax, hyx ▸ hby.symm⟩
    · let p : Fin 5 → V := ![x, a, v, b, y]
      refine ⟨p, ?_, ?_⟩
      · exact fin5_vector_injective hxa hxv hxb (Ne.symm hyx) hav hab (Ne.symm hya)
          hbv.symm hyv.symm hby.ne
      · dsimp [p]
        exact ⟨hax.symm, hva.symm, hvb, hby⟩

/-- The exact finite `P₅` case of the Erdős--Gallai path theorem. -/
theorem erdosGallai_path5
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hP5 : ¬ ∃ p : Fin 5 → V, Function.Injective p ∧
      H.Adj (p 0) (p 1) ∧ H.Adj (p 1) (p 2) ∧
        H.Adj (p 2) (p 3) ∧ H.Adj (p 3) (p 4)) :
    2 * H.edgeFinset.card ≤ 3 * Fintype.card V := by
  classical
  induction n : Fintype.card V using Nat.strong_induction_on generalizing V H with
  | h n ih =>
      by_cases hlow : ∃ v : V, H.degree v ≤ 1
      · obtain ⟨v, hv⟩ := hlow
        let W : Set V := {v}ᶜ
        let H' : SimpleGraph W := H.induce W
        have hcardW : Fintype.card W = Fintype.card V - 1 := by
          dsimp [W]
          rw [Fintype.card_compl_set]
          simp
        have hcard_ltV : Fintype.card W < Fintype.card V := by
          rw [hcardW]
          have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
          omega
        have hP5' : ¬ ∃ p : Fin 5 → W, Function.Injective p ∧
            H'.Adj (p 0) (p 1) ∧ H'.Adj (p 1) (p 2) ∧
              H'.Adj (p 2) (p 3) ∧ H'.Adj (p 3) (p 4) := by
          rintro ⟨p, hp, hp01, hp12, hp23, hp34⟩
          apply hP5
          refine ⟨fun i ↦ (p i).1, ?_, ?_, ?_, ?_, ?_⟩
          · intro i j hij
            exact hp (Subtype.ext hij)
          all_goals simpa [H'] using ‹H'.Adj _ _›
        have hind : 2 * H'.edgeFinset.card ≤ 3 * Fintype.card W :=
          ih (Fintype.card W) (by rw [← n]; exact hcard_ltV) H' hP5' rfl
        have hedge' : H'.edgeFinset.card = H.edgeFinset.card - H.degree v := by
          exact (H.card_edgeFinset_induce_compl_singleton v).trans
            (H.card_edgeFinset_deleteIncidenceSet v)
        have hdeg_edge : H.degree v ≤ H.edgeFinset.card := H.degree_le_card_edgeFinset v
        have hedge : H.edgeFinset.card = H'.edgeFinset.card + H.degree v := by
          rw [hedge', Nat.sub_add_cancel hdeg_edge]
        rw [hedge]
        have hcardrel : Fintype.card W + 1 = Fintype.card V := by
          rw [hcardW]
          have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
          omega
        omega
      · have hmin : ∀ v : V, 2 ≤ H.degree v := by
          intro v
          have : ¬ H.degree v ≤ 1 := fun hv ↦ hlow ⟨v, hv⟩
          omega
        have hmax : ∀ v : V, H.degree v ≤ 3 := by
          intro v
          by_contra hv
          have hv4 : 4 ≤ H.degree v := by omega
          exact hP5 (exists_path5_of_min_degree_two_of_degree_four H hmin hv4)
        rw [← H.sum_degrees_eq_twice_card_edges]
        calc
          ∑ v, H.degree v ≤ ∑ _v : V, 3 := Finset.sum_le_sum fun v _ ↦ hmax v
          _ = 3 * Fintype.card V := by simp [Nat.mul_comm]
          _ = _ := by omega

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/U8Direct.lean` -/

section
/-!
# The unconditional FNV U8 multiplicity estimate

This file discharges the finite certificates used by `GeneralMultiplicity`
from the concrete assumption that the ambient graph has no simple hexagon.
The two parts of the argument are kept public: central fibres are charged to
closed neighbourhoods at cost `25 * Δ * e`, while noncentral fibres are
charged to the quadrilateral components classified by U1 at cost
`10 * Δ * e`.
-/

open scoped BigOperators
open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

attribute [local instance] Classical.propDecidable

/-! ## Concrete hexagon eliminators -/

/-- Six distinct cyclically adjacent vertices contradict `WalkC6Free`.
This explicit form is convenient in all of the local path classifications
below. -/
private theorem false_of_six_cycle_direct (hC6 : WalkC6Free G)
    {a b c d e f : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hef : G.Adj e f) (hfa : G.Adj f a)
    (hpair : [a, b, c, d, e, f].Nodup) : False := by
  let q : G.Walk a a :=
    .cons hab (.cons hbc (.cons hcd (.cons hde (.cons hef (.cons hfa .nil)))))
  have hq : q.IsCycle := by
    simp only [q, Walk.cons_isCycle_iff]
    simp_all [Walk.isPath_def, List.nodup_cons, eq_comm]
  exact hC6 a q hq (by simp [q])

/-- A four-edge path cannot lie in the open neighbourhood of one vertex in
a hexagon-free graph. -/
private theorem false_of_openNeighborhood_path_four (hC6 : WalkC6Free G)
    {v a b c d e : V}
    (hva : G.Adj v a) (hvb : G.Adj v b) (hvc : G.Adj v c)
    (hvd : G.Adj v d) (hve : G.Adj v e)
    (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hde : G.Adj d e)
    (hpath : [a, b, c, d, e].Nodup) : False := by
  apply false_of_six_cycle_direct G hC6 hva hab hbc hcd hde hve.symm
  apply List.nodup_cons.mpr
  constructor
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hva.ne, hvb.ne, hvc.ne, hvd.ne, hve.ne⟩
  · exact hpath

/-! ## The local noncentral-pair kernel -/

/-- The middle edge of a length-three path. -/
def Path3.u8MiddleEdge (p : Path3 G) : Sym2 V :=
  s(p.vertex 1, p.vertex 2)

@[simp] theorem Path3.u8MiddleEdge_toFinset (p : Path3 G) :
    p.u8MiddleEdge.toFinset = {p.vertex 1, p.vertex 2} := by
  simp only [Path3.u8MiddleEdge, Sym2.toFinset_mk_eq]

/-- In a hexagon-free graph, middle edges belonging to two paths with the
same endpoints must intersect.  If they were disjoint, the two paths, one
traversed backwards, would be a simple hexagon. -/
theorem pathFiber_middleEdges_not_disjoint (hC6 : WalkC6Free G)
    {pi : EndpointPair V} {p q : Path3 G}
    (hp : p ∈ pathFiber G pi) (hq : q ∈ pathFiber G pi) :
    ¬ Disjoint p.u8MiddleEdge.toFinset q.u8MiddleEdge.toFinset := by
  intro hd
  have he : p.endpoints = q.endpoints :=
    ((mem_pathFiber (G := G)).mp hp).trans
      ((mem_pathFiber (G := G)).mp hq).symm
  have h0 : p.vertex 0 = q.vertex 0 := by
    exact congrArg (fun z : EndpointPair V ↦ z.1.1) he
  have h3 : p.vertex 3 = q.vertex 3 := by
    exact congrArg (fun z : EndpointPair V ↦ z.1.2) he
  have hpne (i j : Fin 4) (hij : i ≠ j) : p.vertex i ≠ p.vertex j :=
    p.injective.ne hij
  have hqne (i j : Fin 4) (hij : i ≠ j) : q.vertex i ≠ q.vertex j :=
    q.injective.ne hij
  have hcross :
      p.vertex 1 ≠ q.vertex 1 ∧ p.vertex 1 ≠ q.vertex 2 ∧
      p.vertex 2 ≠ q.vertex 1 ∧ p.vertex 2 ≠ q.vertex 2 := by
    rw [Path3.u8MiddleEdge_toFinset, Path3.u8MiddleEdge_toFinset,
      Finset.disjoint_left] at hd
    exact ⟨
      fun h ↦ hd (a := p.vertex 1) (by simp) (by simpa [h]),
      fun h ↦ hd (a := p.vertex 1) (by simp) (by simpa [h]),
      fun h ↦ hd (a := p.vertex 2) (by simp) (by simpa [h]),
      fun h ↦ hd (a := p.vertex 2) (by simp) (by simpa [h])⟩
  have hbq : G.Adj (p.vertex 3) (q.vertex 2) := by
    rw [h3]
    exact q.adj_two_three.symm
  have hqa : G.Adj (q.vertex 1) (p.vertex 0) := by
    rw [h0]
    exact q.adj_zero_one.symm
  have hp1q3 : p.vertex 1 ≠ q.vertex 3 := by
    intro h
    exact (hpne 1 3 (by decide)) (h.trans h3.symm)
  have hp2q3 : p.vertex 2 ≠ q.vertex 3 := by
    intro h
    exact (hpne 2 3 (by decide)) (h.trans h3.symm)
  apply false_of_six_cycle_direct G hC6
    p.adj_zero_one p.adj_one_two p.adj_two_three
    hbq q.adj_one_two.symm hqa
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, true_and]
  aesop

private theorem finset_eq_pair_of_card_two_mem {X : Type*} [DecidableEq X]
    {S : Finset X} {x : X} (hS : S.card = 2) (hx : x ∈ S) :
    ∃ y, y ≠ x ∧ S = {x, y} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨b, hab.symm, rfl⟩
  · exact ⟨a, hab, by rw [Finset.pair_comm]⟩

/-- A pairwise-intersecting finite family of two-sets is a star or is
contained in the three edges of a triangle. -/
private theorem twoSet_family_star_or_triangle {X : Type*} [DecidableEq X]
    (F : Finset (Finset X)) (hne : F.Nonempty)
    (hcard : ∀ S ∈ F, S.card = 2)
    (hinter : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) :
    (∃ x, ∀ S ∈ F, x ∈ S) ∨
      ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        {a, b} ∈ F ∧ {a, c} ∈ F ∧ {b, c} ∈ F ∧
        ∀ S ∈ F, S = {a, b} ∨ S = {a, c} ∨ S = {b, c} := by
  classical
  obtain ⟨S, hSF⟩ := hne
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hcard S hSF)
  by_cases ha : ∀ T ∈ F, a ∈ T
  · exact Or.inl ⟨a, ha⟩
  by_cases hb : ∀ T ∈ F, b ∈ T
  · exact Or.inl ⟨b, hb⟩
  push_neg at ha hb
  obtain ⟨T, hTF, haT⟩ := ha
  obtain ⟨U, hUF, hbU⟩ := hb
  have hbT : b ∈ T := by
    obtain ⟨x, hx⟩ := hinter {a, b} hSF T hTF
    have hxS := (Finset.mem_inter.mp hx).1
    have hxT := (Finset.mem_inter.mp hx).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxS
    rcases hxS with rfl | rfl
    · exact (haT hxT).elim
    · exact hxT
  have haU : a ∈ U := by
    obtain ⟨x, hx⟩ := hinter {a, b} hSF U hUF
    have hxS := (Finset.mem_inter.mp hx).1
    have hxU := (Finset.mem_inter.mp hx).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxS
    rcases hxS with rfl | rfl
    · exact hxU
    · exact (hbU hxU).elim
  obtain ⟨c, hcb, hT⟩ :=
    finset_eq_pair_of_card_two_mem (hcard T hTF) hbT
  obtain ⟨d, hda, hU⟩ :=
    finset_eq_pair_of_card_two_mem (hcard U hUF) haU
  have hac : a ≠ c := by
    intro hac
    apply haT
    rw [hT, hac]
    simp
  have hbd : b ≠ d := by
    intro hbd
    apply hbU
    rw [hU, hbd]
    simp
  have hcd : c = d := by
    obtain ⟨x, hx⟩ := hinter T hTF U hUF
    have hxT := (Finset.mem_inter.mp hx).1
    have hxU := (Finset.mem_inter.mp hx).2
    rw [hT] at hxT
    rw [hU] at hxU
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxT hxU
    rcases hxT with rfl | rfl <;> rcases hxU with rfl | rfl
    · exact (hab rfl).elim
    · exact (hbd rfl).elim
    · exact (hac rfl).elim
    · rfl
  subst d
  have habF : {a, b} ∈ F := hSF
  have hacF : {a, c} ∈ F := by simpa [hU] using hUF
  have hbcF : {b, c} ∈ F := by simpa [hT] using hTF
  refine Or.inr ⟨a, b, c, hab, hac, hcb.symm, habF, hacF, hbcF, ?_⟩
  intro R hRF
  obtain ⟨x, y, hxy, hR⟩ := Finset.card_eq_two.mp (hcard R hRF)
  subst R
  have hRS := hinter {x, y} hRF {a, b} hSF
  have hRT := hinter {x, y} hRF T hTF
  have hRU := hinter {x, y} hRF U hUF
  rw [hT] at hRT
  rw [hU] at hRU
  obtain ⟨z, hz⟩ := hRS
  obtain ⟨w, hw⟩ := hRT
  obtain ⟨t, ht⟩ := hRU
  have hzR := (Finset.mem_inter.mp hz).1
  have hzS := (Finset.mem_inter.mp hz).2
  have hwR := (Finset.mem_inter.mp hw).1
  have hwT := (Finset.mem_inter.mp hw).2
  have htR := (Finset.mem_inter.mp ht).1
  have htU := (Finset.mem_inter.mp ht).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzR hzS hwR hwT htR htU
  have hcases :
      (x = a ∧ y = b) ∨ (x = b ∧ y = a) ∨
      (x = a ∧ y = c) ∨ (x = c ∧ y = a) ∨
      (x = b ∧ y = c) ∨ (x = c ∧ y = b) := by
    grind
  rcases hcases with h | h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;> simp [Finset.pair_comm]

/-- The finite family of all middle edges in one endpoint fibre. -/
def middleEdgeFamily (pi : EndpointPair V) : Finset (Finset V) :=
  (pathFiber G pi).image fun p ↦ p.u8MiddleEdge.toFinset

@[simp] theorem mem_middleEdgeFamily {pi : EndpointPair V} {S : Finset V} :
    S ∈ middleEdgeFamily G pi ↔
      ∃ p ∈ pathFiber G pi, p.u8MiddleEdge.toFinset = S := by
  simp [middleEdgeFamily]

theorem middleEdgeFamily_nonempty {pi : EndpointPair V}
    (hpi : 1 ≤ pathMultiplicity G pi) : (middleEdgeFamily G pi).Nonempty := by
  have hf : (pathFiber G pi).Nonempty := by
    rw [← Finset.card_pos]
    simpa [pathMultiplicity] using hpi
  obtain ⟨p, hp⟩ := hf
  exact ⟨p.u8MiddleEdge.toFinset, by simp only [mem_middleEdgeFamily]; exact ⟨p, hp, rfl⟩⟩

theorem middleEdgeFamily_card_two {pi : EndpointPair V}
    {S : Finset V} (hS : S ∈ middleEdgeFamily G pi) : S.card = 2 := by
  obtain ⟨p, -, rfl⟩ := (mem_middleEdgeFamily (G := G)).mp hS
  rw [Path3.u8MiddleEdge_toFinset]
  exact Finset.card_pair (p.injective.ne (by decide))

theorem middleEdgeFamily_inter_nonempty (hC6 : WalkC6Free G)
    {pi : EndpointPair V} {S T : Finset V}
    (hS : S ∈ middleEdgeFamily G pi) (hT : T ∈ middleEdgeFamily G pi) :
    (S ∩ T).Nonempty := by
  obtain ⟨p, hp, rfl⟩ := (mem_middleEdgeFamily (G := G)).mp hS
  obtain ⟨q, hq, rfl⟩ := (mem_middleEdgeFamily (G := G)).mp hT
  rw [← not_disjoint_iff_nonempty_inter]
  exact pathFiber_middleEdges_not_disjoint G hC6 hp hq

private theorem endpointAdjacency_of_middle_pair {pi : EndpointPair V} {a b : V}
    (hab : {a, b} ∈ middleEdgeFamily G pi) :
    G.Adj a b ∧
      ((G.Adj pi.1.1 a ∧ G.Adj b pi.1.2) ∨
        (G.Adj pi.1.1 b ∧ G.Adj a pi.1.2)) := by
  obtain ⟨p, hp, he⟩ := (mem_middleEdgeFamily (G := G)).mp hab
  rw [Path3.u8MiddleEdge_toFinset] at he
  have he' : ({p.vertex 1, p.vertex 2} : Set V) = {a, b} := by
    simpa only [Finset.coe_pair] using
      congrArg (fun S : Finset V ↦ (S : Set V)) he
  have hend : p.vertex 0 = pi.1.1 ∧ p.vertex 3 = pi.1.2 := by
    have h := (mem_pathFiber (G := G)).mp hp
    exact ⟨congrArg (fun z : EndpointPair V ↦ z.1.1) h,
      congrArg (fun z : EndpointPair V ↦ z.1.2) h⟩
  rcases Set.pair_eq_pair_iff.mp he' with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨p.adj_one_two, Or.inl ⟨hend.1 ▸ p.adj_zero_one,
      hend.2 ▸ p.adj_two_three⟩⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨p.adj_one_two.symm, Or.inr ⟨hend.1 ▸ p.adj_zero_one,
      hend.2 ▸ p.adj_two_three⟩⟩

private theorem centralPair_of_triangle_middleFamily {pi : EndpointPair V}
    {a b c : V} (habF : {a, b} ∈ middleEdgeFamily G pi)
    (hacF : {a, c} ∈ middleEdgeFamily G pi)
    (hbcF : {b, c} ∈ middleEdgeFamily G pi)
    (hall : ∀ S ∈ middleEdgeFamily G pi,
      S = {a, b} ∨ S = {a, c} ∨ S = {b, c}) :
    IsCentralPair G pi := by
  obtain ⟨hab, habd⟩ := endpointAdjacency_of_middle_pair G habF
  obtain ⟨hac, hacd⟩ := endpointAdjacency_of_middle_pair G hacF
  obtain ⟨hbc, hbcd⟩ := endpointAdjacency_of_middle_pair G hbcF
  have hcenter : ∃ w, (w = a ∨ w = b ∨ w = c) ∧
      G.Adj pi.1.1 w ∧ G.Adj w pi.1.2 := by
    rcases habd with habd | habd <;>
      rcases hacd with hacd | hacd <;>
      rcases hbcd with hbcd | hbcd <;> aesop
  obtain ⟨w, hw, hxw, hwy⟩ := hcenter
  have ha : a ∈ closedNeighborFinset G w := by
    rw [mem_closedNeighborFinset]
    rcases hw with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hab.symm
    · exact Or.inr hac.symm
  have hb : b ∈ closedNeighborFinset G w := by
    rw [mem_closedNeighborFinset]
    rcases hw with rfl | rfl | rfl
    · exact Or.inr hab
    · exact Or.inl rfl
    · exact Or.inr hbc.symm
  have hc : c ∈ closedNeighborFinset G w := by
    rw [mem_closedNeighborFinset]
    rcases hw with rfl | rfl | rfl
    · exact Or.inr hac
    · exact Or.inr hbc
    · exact Or.inl rfl
  refine ⟨w, ?_⟩
  intro p hp i
  have hend := (mem_pathFiber (G := G)).mp hp
  have h0 : p.vertex 0 = pi.1.1 :=
    congrArg (fun z : EndpointPair V ↦ z.1.1) hend
  have h3 : p.vertex 3 = pi.1.2 :=
    congrArg (fun z : EndpointPair V ↦ z.1.2) hend
  have hmid : p.u8MiddleEdge.toFinset ∈ middleEdgeFamily G pi := by
    rw [mem_middleEdgeFamily]
    exact ⟨p, hp, rfl⟩
  have hpairs := hall _ hmid
  have h1 : p.vertex 1 = a ∨ p.vertex 1 = b ∨ p.vertex 1 = c := by
    have hpairs1 := hpairs
    rw [Path3.u8MiddleEdge_toFinset] at hpairs1
    rcases hpairs1 with h | h | h
    · have hm : p.vertex 1 ∈ ({a, b} : Finset V) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Or.inl hm
      · exact Or.inr (Or.inl hm)
    · have hm : p.vertex 1 ∈ ({a, c} : Finset V) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Or.inl hm
      · exact Or.inr (Or.inr hm)
    · have hm : p.vertex 1 ∈ ({b, c} : Finset V) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Or.inr (Or.inl hm)
      · exact Or.inr (Or.inr hm)
  have h2 : p.vertex 2 = a ∨ p.vertex 2 = b ∨ p.vertex 2 = c := by
    have hpairs2 := hpairs
    rw [Path3.u8MiddleEdge_toFinset] at hpairs2
    rcases hpairs2 with h | h | h
    · have hm : p.vertex 2 ∈ ({a, b} : Finset V) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Or.inl hm
      · exact Or.inr (Or.inl hm)
    · have hm : p.vertex 2 ∈ ({a, c} : Finset V) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Or.inl hm
      · exact Or.inr (Or.inr hm)
    · have hm : p.vertex 2 ∈ ({b, c} : Finset V) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Or.inr (Or.inl hm)
      · exact Or.inr (Or.inr hm)
  fin_cases i
  · change p.vertex 0 ∈ closedNeighborFinset G w
    rw [h0, mem_closedNeighborFinset]
    exact Or.inr hxw.symm
  · rcases h1 with rfl | rfl | rfl <;> assumption
  · rcases h2 with rfl | rfl | rfl <;> assumption
  · change p.vertex 3 ∈ closedNeighborFinset G w
    rw [h3, mem_closedNeighborFinset]
    exact Or.inr hwy

/-- The middle edges in a noncentral endpoint fibre form a genuine star.
This is the local combinatorial kernel of FNV Lemma 5.1. -/
theorem exists_common_middleVertex_of_not_central (hC6 : WalkC6Free G)
    {pi : EndpointPair V} (hmul : 1 ≤ pathMultiplicity G pi)
    (hnc : ¬ IsCentralPair G pi) :
    ∃ w, ∀ p ∈ pathFiber G pi, w ∈ p.u8MiddleEdge.toFinset := by
  have hne : (middleEdgeFamily G pi).Nonempty :=
    middleEdgeFamily_nonempty G hmul
  have hclass := twoSet_family_star_or_triangle (middleEdgeFamily G pi) hne
    (fun S hS ↦ middleEdgeFamily_card_two G hS)
    (fun S hS T hT ↦ middleEdgeFamily_inter_nonempty G hC6 hS hT)
  rcases hclass with ⟨w, hw⟩ | ⟨a, b, c, -, -, -, hab, hac, hbc, hall⟩
  · refine ⟨w, ?_⟩
    intro p hp
    exact hw _ ((mem_middleEdgeFamily (G := G)).mpr ⟨p, hp, rfl⟩)
  · exact (hnc (centralPair_of_triangle_middleFamily G hab hac hbc hall)).elim

private theorem centralPair_of_mixed_common_middle {pi : EndpointPair V} {w : V}
    (hcommon : ∀ p ∈ pathFiber G pi, w ∈ p.u8MiddleEdge.toFinset)
    {p q : Path3 G} (hp : p ∈ pathFiber G pi) (hq : q ∈ pathFiber G pi)
    (hpw : w = p.vertex 1) (hqw : w = q.vertex 2) :
    IsCentralPair G pi := by
  have hep := (mem_pathFiber (G := G)).mp hp
  have heq := (mem_pathFiber (G := G)).mp hq
  have hp0 : p.vertex 0 = pi.1.1 :=
    congrArg (fun z : EndpointPair V ↦ z.1.1) hep
  have hq3 : q.vertex 3 = pi.1.2 :=
    congrArg (fun z : EndpointPair V ↦ z.1.2) heq
  have hxw : G.Adj pi.1.1 w := by
    rw [hpw, ← hp0]
    exact p.adj_zero_one
  have hwy : G.Adj w pi.1.2 := by
    rw [hqw, ← hq3]
    exact q.adj_two_three
  refine ⟨w, ?_⟩
  intro r hr i
  have her := (mem_pathFiber (G := G)).mp hr
  have hr0 : r.vertex 0 = pi.1.1 :=
    congrArg (fun z : EndpointPair V ↦ z.1.1) her
  have hr3 : r.vertex 3 = pi.1.2 :=
    congrArg (fun z : EndpointPair V ↦ z.1.2) her
  have hrw := hcommon r hr
  rw [Path3.u8MiddleEdge_toFinset] at hrw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hrw
  fin_cases i
  · change r.vertex 0 ∈ closedNeighborFinset G w
    rw [hr0, mem_closedNeighborFinset]
    exact Or.inr hxw.symm
  · rw [mem_closedNeighborFinset]
    rcases hrw with h | h
    · exact Or.inl h.symm
    · exact Or.inr (h ▸ r.adj_one_two.symm)
  · rw [mem_closedNeighborFinset]
    rcases hrw with h | h
    · exact Or.inr (h ▸ r.adj_one_two)
    · exact Or.inl h.symm
  · change r.vertex 3 ∈ closedNeighborFinset G w
    rw [hr3, mem_closedNeighborFinset]
    exact Or.inr hwy

/-- On a noncentral fibre the common middle vertex occurs consistently on
one side.  Consequently every path is encoded by its other middle vertex. -/
theorem noncentral_middle_star_normal_form (hC6 : WalkC6Free G)
    {pi : EndpointPair V} (hmul : 1 ≤ pathMultiplicity G pi)
    (hnc : ¬ IsCentralPair G pi) :
    ∃ w, (∀ p ∈ pathFiber G pi, w = p.vertex 1) ∨
      ∀ p ∈ pathFiber G pi, w = p.vertex 2 := by
  obtain ⟨w, hcommon⟩ :=
    exists_common_middleVertex_of_not_central G hC6 hmul hnc
  by_cases hleft : ∀ p ∈ pathFiber G pi, w = p.vertex 1
  · exact ⟨w, Or.inl hleft⟩
  · push_neg at hleft
    obtain ⟨p, hp, hpne⟩ := hleft
    have hpw := hcommon p hp
    rw [Path3.u8MiddleEdge_toFinset] at hpw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpw
    have hp2 : w = p.vertex 2 := hpw.resolve_left hpne
    refine ⟨w, Or.inr ?_⟩
    intro q hq
    have hqw := hcommon q hq
    rw [Path3.u8MiddleEdge_toFinset] at hqw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hqw
    rcases hqw with hq1 | hq2
    · exact (hnc (centralPair_of_mixed_common_middle G hcommon hq hp hq1 hp2)).elim
    · exact hq2

theorem nondegenerateExceptional_two_le {pi : EndpointPair V}
    (hpi : pi ∈ nondegenerateExceptionalPairs G) :
    2 ≤ pathMultiplicity G pi := by
  have hord : pi ∈ ordinaryExceptionalPairs G :=
    (Finset.mem_sdiff.mp hpi).1
  have h := (Finset.mem_filter.mp hord).2
  rcases h with h | h
  · exact h.1
  · omega

theorem nondegenerateExceptional_not_central {pi : EndpointPair V}
    (hpi : pi ∈ nondegenerateExceptionalPairs G) :
    ¬ IsCentralPair G pi := by
  have hnot : pi ∉ degeneratePairs G := (Finset.mem_sdiff.mp hpi).2
  intro hc
  apply hnot
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ⟨nondegenerateExceptional_two_le G hpi, hc⟩⟩

theorem nondegenerate_middle_star_normal_form (hC6 : WalkC6Free G)
    {pi : EndpointPair V} (hpi : pi ∈ nondegenerateExceptionalPairs G) :
    ∃ w, (∀ p ∈ pathFiber G pi, w = p.vertex 1) ∨
      ∀ p ∈ pathFiber G pi, w = p.vertex 2 := by
  exact noncentral_middle_star_normal_form G hC6
    (Nat.one_le_iff_ne_zero.mpr (by
      have := nondegenerateExceptional_two_le G hpi
      omega))
    (nondegenerateExceptional_not_central G hpi)

/-! ## The concrete biclique attached to a noncentral pair -/

noncomputable def nondegenerateStarCentre (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) : V :=
  (nondegenerate_middle_star_normal_form G hC6 hpi).choose

def nondegenerateStarOnLeft (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) : Prop :=
  ∀ p ∈ pathFiber G pi,
    nondegenerateStarCentre G hC6 pi hpi = p.vertex 1

theorem nondegenerateStarCentre_spec (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) :
    nondegenerateStarOnLeft G hC6 pi hpi ∨
      ∀ p ∈ pathFiber G pi,
        nondegenerateStarCentre G hC6 pi hpi = p.vertex 2 :=
  (nondegenerate_middle_star_normal_form G hC6 hpi).choose_spec

theorem nondegenerateStarCentre_spec_right (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G)
    (hr : ¬ nondegenerateStarOnLeft G hC6 pi hpi) :
    ∀ p ∈ pathFiber G pi,
      nondegenerateStarCentre G hC6 pi hpi = p.vertex 2 :=
  (nondegenerateStarCentre_spec G hC6 pi hpi).resolve_left hr

noncomputable def nondegenerateOtherMiddles (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) : Finset V :=
  if nondegenerateStarOnLeft G hC6 pi hpi then
    (pathFiber G pi).image fun p ↦ p.vertex 2
  else
    (pathFiber G pi).image fun p ↦ p.vertex 1

noncomputable def nondegenerateBaseSide (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) : Finset V :=
  if nondegenerateStarOnLeft G hC6 pi hpi then
    {nondegenerateStarCentre G hC6 pi hpi, pi.1.2}
  else
    {pi.1.1, nondegenerateStarCentre G hC6 pi hpi}

private theorem card_image_vertex_two_of_star_left (hC6 : WalkC6Free G)
    {pi : EndpointPair V} (hpi : pi ∈ nondegenerateExceptionalPairs G)
    (hl : nondegenerateStarOnLeft G hC6 pi hpi) :
    ((pathFiber G pi).image fun p ↦ p.vertex 2).card =
      (pathFiber G pi).card := by
  rw [Finset.card_image_iff]
  intro p hp q hq he
  apply Subtype.ext
  funext i
  have hep := (mem_pathFiber (G := G)).mp hp
  have heq := (mem_pathFiber (G := G)).mp hq
  fin_cases i
  · exact (congrArg (fun z : EndpointPair V ↦ z.1.1) hep).trans
      (congrArg (fun z : EndpointPair V ↦ z.1.1) heq).symm
  · exact (hl p hp).symm.trans (hl q hq)
  · exact he
  · exact (congrArg (fun z : EndpointPair V ↦ z.1.2) hep).trans
      (congrArg (fun z : EndpointPair V ↦ z.1.2) heq).symm

private theorem card_image_vertex_one_of_star_right (hC6 : WalkC6Free G)
    {pi : EndpointPair V} (hpi : pi ∈ nondegenerateExceptionalPairs G)
    (hr : ¬ nondegenerateStarOnLeft G hC6 pi hpi) :
    ((pathFiber G pi).image fun p ↦ p.vertex 1).card =
      (pathFiber G pi).card := by
  have hs := nondegenerateStarCentre_spec_right G hC6 pi hpi hr
  rw [Finset.card_image_iff]
  intro p hp q hq he
  apply Subtype.ext
  funext i
  have hep := (mem_pathFiber (G := G)).mp hp
  have heq := (mem_pathFiber (G := G)).mp hq
  fin_cases i
  · exact (congrArg (fun z : EndpointPair V ↦ z.1.1) hep).trans
      (congrArg (fun z : EndpointPair V ↦ z.1.1) heq).symm
  · exact he
  · exact (hs p hp).symm.trans (hs q hq)
  · exact (congrArg (fun z : EndpointPair V ↦ z.1.2) hep).trans
      (congrArg (fun z : EndpointPair V ↦ z.1.2) heq).symm

theorem card_nondegenerateOtherMiddles (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) :
    (nondegenerateOtherMiddles G hC6 pi hpi).card = pathMultiplicity G pi := by
  classical
  unfold nondegenerateOtherMiddles pathMultiplicity
  split_ifs with h
  · exact card_image_vertex_two_of_star_left G hC6 hpi h
  · exact card_image_vertex_one_of_star_right G hC6 hpi h

/-- The canonical base side is complete to the canonical set of varying
middle vertices. -/
theorem nondegenerateBaseOther_adj (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G)
    {x y : V} (hx : x ∈ nondegenerateBaseSide G hC6 pi hpi)
    (hy : y ∈ nondegenerateOtherMiddles G hC6 pi hpi) :
    G.Adj x y := by
  by_cases hl : nondegenerateStarOnLeft G hC6 pi hpi
  · simp only [nondegenerateBaseSide, if_pos hl, Finset.mem_insert,
      Finset.mem_singleton] at hx
    simp only [nondegenerateOtherMiddles, if_pos hl] at hy
    obtain ⟨p, hp, hpy⟩ := Finset.mem_image.mp hy
    rcases hx with rfl | rfl
    · change G.Adj (nondegenerateStarCentre G hC6 pi hpi) y
      rw [hl p hp, ← hpy]
      exact p.adj_one_two
    · have hend := (mem_pathFiber (G := G)).mp hp
      have h3 : p.vertex 3 = pi.1.2 :=
        congrArg (fun z : EndpointPair V ↦ z.1.2) hend
      rw [← h3, ← hpy]
      exact p.adj_two_three.symm
  · have hs := nondegenerateStarCentre_spec_right G hC6 pi hpi hl
    simp only [nondegenerateBaseSide, if_neg hl, Finset.mem_insert,
      Finset.mem_singleton] at hx
    simp only [nondegenerateOtherMiddles, if_neg hl] at hy
    obtain ⟨p, hp, hpy⟩ := Finset.mem_image.mp hy
    rcases hx with rfl | rfl
    · have hend := (mem_pathFiber (G := G)).mp hp
      have h0 : p.vertex 0 = pi.1.1 :=
        congrArg (fun z : EndpointPair V ↦ z.1.1) hend
      rw [← h0, ← hpy]
      exact p.adj_zero_one
    · change G.Adj (nondegenerateStarCentre G hC6 pi hpi) y
      rw [hs p hp, ← hpy]
      exact p.adj_one_two.symm

/-- The canonical base of a nondegenerate exceptional fibre has exactly
two vertices. -/
theorem card_nondegenerateBaseSide (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) :
    (nondegenerateBaseSide G hC6 pi hpi).card = 2 := by
  have hpos : 0 < pathMultiplicity G pi := by
    have htwo := nondegenerateExceptional_two_le G hpi
    omega
  obtain ⟨p, hp⟩ : (pathFiber G pi).Nonempty := by
    rw [← Finset.card_pos]
    simpa only [pathMultiplicity] using hpos
  by_cases hl : nondegenerateStarOnLeft G hC6 pi hpi
  · rw [nondegenerateBaseSide, if_pos hl]
    apply Finset.card_pair
    intro heq
    have hend := (mem_pathFiber (G := G)).mp hp
    have h3 : p.vertex 3 = pi.1.2 :=
      congrArg (fun z : EndpointPair V ↦ z.1.2) hend
    exact p.injective.ne (by decide)
      ((hl p hp).symm.trans (heq.trans h3.symm))
  · rw [nondegenerateBaseSide, if_neg hl]
    apply Finset.card_pair
    intro heq
    have hend := (mem_pathFiber (G := G)).mp hp
    have h0 : p.vertex 0 = pi.1.1 :=
      congrArg (fun z : EndpointPair V ↦ z.1.1) hend
    have hs := nondegenerateStarCentre_spec_right G hC6 pi hpi hl p hp
    exact p.injective.ne (by decide) (h0.trans (heq.trans hs))

/-- The two canonical base vertices are disjoint from all varying middle
vertices. -/
theorem disjoint_nondegenerateBaseOther (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) :
    Disjoint (nondegenerateBaseSide G hC6 pi hpi)
      (nondegenerateOtherMiddles G hC6 pi hpi) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  by_cases hl : nondegenerateStarOnLeft G hC6 pi hpi
  · simp only [nondegenerateBaseSide, if_pos hl, Finset.mem_insert,
      Finset.mem_singleton] at hx
    simp only [nondegenerateOtherMiddles, if_pos hl] at hy
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hy
    rcases hx with rfl | rfl
    · exact p.injective.ne (by decide) ((hl p hp).symm.trans hpx.symm)
    · have hend := (mem_pathFiber (G := G)).mp hp
      have h3 : p.vertex 3 = pi.1.2 :=
        congrArg (fun z : EndpointPair V ↦ z.1.2) hend
      exact p.injective.ne (by decide) (h3.trans hpx.symm)
  · have hs := nondegenerateStarCentre_spec_right G hC6 pi hpi hl
    simp only [nondegenerateBaseSide, if_neg hl, Finset.mem_insert,
      Finset.mem_singleton] at hx
    simp only [nondegenerateOtherMiddles, if_neg hl] at hy
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hy
    rcases hx with rfl | rfl
    · have hend := (mem_pathFiber (G := G)).mp hp
      have h0 : p.vertex 0 = pi.1.1 :=
        congrArg (fun z : EndpointPair V ↦ z.1.1) hend
      exact p.injective.ne (by decide) (h0.trans hpx.symm)
    · exact p.injective.ne (by decide) ((hs p hp).symm.trans hpx.symm)

private noncomputable def crossingGraphEdges (L R : Finset V) :
    Finset (GraphEdge G) :=
  Finset.univ.filter fun e ↦ EdgeCrosses G L R e

@[simp] private theorem mem_crossingGraphEdges {L R : Finset V} {e : GraphEdge G} :
    e ∈ crossingGraphEdges G L R ↔ EdgeCrosses G L R e := by
  simp [crossingGraphEdges]

/-! ## Canonical charging of central fibres -/

/-- A canonical centre for a central endpoint pair.  The fallback is only
used away from central pairs and makes the definition work even without an
`Inhabited V` instance. -/
def chosenCentralVertex (pi : EndpointPair V) : V :=
  if h : IsCentralPair G pi then h.choose else pi.1.1

theorem chosenCentralVertex_spec {pi : EndpointPair V}
    (hpi : pi ∈ degeneratePairs G) {p : Path3 G}
    (hp : p ∈ pathFiber G pi) (i : Fin 4) :
    p.vertex i ∈ closedNeighborFinset G (chosenCentralVertex G pi) := by
  have hc : IsCentralPair G pi := by
    simpa [degeneratePairs, IsDegeneratePair] using (Finset.mem_filter.mp hpi).2.2
  rw [chosenCentralVertex, dif_pos hc]
  exact hc.choose_spec p hp i

/-- The endpoint fibres assigned to their chosen centres inject into the
corresponding closed-neighbourhood path sets. -/
theorem central_charge_direct :
    multiplicitySum G (degeneratePairs G) ≤
      ∑ v, (closedNeighborhoodPaths G v).card := by
  let A := Σ pi : {pi // pi ∈ degeneratePairs G},
    {p // p ∈ pathFiber G pi.1}
  let B := Σ v : V, {p // p ∈ closedNeighborhoodPaths G v}
  let charge : A → B := fun x ↦
    ⟨chosenCentralVertex G x.1.1,
      ⟨x.2.1, by
        rw [mem_closedNeighborhoodPaths]
        exact fun i ↦ chosenCentralVertex_spec G x.1.2 x.2.2 i⟩⟩
  have hinj : Function.Injective charge := by
    rintro ⟨⟨pi, hpi⟩, ⟨p, hp⟩⟩ ⟨⟨rho, hrho⟩, ⟨q, hq⟩⟩ h
    have hpq : p = q := by
      exact congrArg (fun z : B ↦ z.2.1) h
    have hpi_rho : pi = rho := by
      have hep : p.endpoints = pi := (mem_pathFiber (G := G)).mp hp
      have heq : q.endpoints = rho := (mem_pathFiber (G := G)).mp hq
      exact hep.symm.trans ((congrArg Path3.endpoints hpq).trans heq)
    subst rho
    subst q
    rfl
  have hcard : Fintype.card A ≤ Fintype.card B :=
    Fintype.card_le_of_injective charge hinj
  have hA : Fintype.card A = multiplicitySum G (degeneratePairs G) := by
    dsimp only [A]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    unfold multiplicitySum pathMultiplicity
    have hatt : (degeneratePairs G).attach =
        (Finset.univ : Finset {pi // pi ∈ degeneratePairs G}) := by
      ext pi
      simp
    have hs := Finset.sum_attach (degeneratePairs G)
      (fun pi : EndpointPair V ↦ (pathFiber G pi).card)
    rw [hatt] at hs
    exact hs
  have hB : Fintype.card B = ∑ v, (closedNeighborhoodPaths G v).card := by
    dsimp only [B]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
  rwa [hA, hB] at hcard

/-! ## Counting paths in a closed neighbourhood -/

/-- The edges induced by a closed neighbourhood split into the star at its
centre and the edges internal to the open neighbourhood. -/
theorem card_induced_closedNeighbor_eq (v : V) :
    (G.induce (closedNeighborFinset G v : Set V)).edgeFinset.card =
      closedNeighborhoodEdgeCount G v := by
  rw [← G.card_filter_edgeFinset_toFinset_subset (closedNeighborFinset G v)]
  have hsplit :
      (G.edgeFinset.filter fun e ↦ e.toFinset ⊆ closedNeighborFinset G v) =
        G.incidenceFinset v ∪ openNeighborhoodEdges G v := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
        simp only [Finset.mem_filter, Finset.mem_union, Sym2.toFinset_mk_eq,
          Finset.insert_subset_iff, Finset.singleton_subset_iff]
        rw [G.mem_incidenceFinset]
        simp only [G.mk'_mem_incidenceSet_iff]
        simp [closedNeighborFinset, openNeighborhoodEdges,
          SimpleGraph.mem_edgeFinset, G.adj_comm, eq_comm]
        constructor
        · rintro ⟨hab, ha, hb⟩
          rcases ha with rfl | hva
          · exact Or.inl ⟨hab, Or.inl rfl⟩
          rcases hb with rfl | hvb
          · exact Or.inl ⟨hab, Or.inr rfl⟩
          · exact Or.inr ⟨hab, fun z hz ↦ by
              rcases hz with rfl | rfl
              · exact hva
              · exact hvb⟩
        · rintro (⟨hab, hv⟩ | ⟨hab, hopen⟩)
          · rcases hv with rfl | rfl
            · exact ⟨hab, Or.inl rfl, Or.inr hab⟩
            · exact ⟨hab, Or.inr hab.symm, Or.inl rfl⟩
          · exact ⟨hab, Or.inr (hopen a (Or.inl rfl)),
              Or.inr (hopen b (Or.inr rfl))⟩
  rw [hsplit, Finset.card_union_of_disjoint]
  · simp [closedNeighborhoodEdgeCount, G.card_incidenceFinset_eq_degree]
  · rw [Finset.disjoint_left]
    intro e heI heO
    induction e using Sym2.ind with
    | _ a b =>
        rw [G.mem_incidenceFinset] at heI
        simp only [G.mk'_mem_incidenceSet_iff] at heI
        simp only [openNeighborhoodEdges, Finset.mem_filter,
          Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
          Finset.singleton_subset_iff] at heO
        rcases heI.2 with (rfl | rfl) <;> simp_all

/-- Ordered pairs of darts whose initial vertices are increasing occupy at
most half of all ordered dart pairs. -/
private theorem twice_card_increasingDartPairs_le
    {W : Type*} [Fintype W] [LinearOrder W]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    2 * Fintype.card {z : H.Dart × H.Dart // z.1.fst < z.2.fst} ≤
      (Fintype.card H.Dart) ^ 2 := by
  let A := {z : H.Dart × H.Dart // z.1.fst < z.2.fst}
  let f : A ⊕ A → H.Dart × H.Dart
    | Sum.inl z => z.1
    | Sum.inr z => (z.1.2, z.1.1)
  have hf : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            congr 1
            exact Subtype.ext hxy
        | inr y =>
            exfalso
            have h1 : x.1.1 = y.1.2 := congrArg Prod.fst hxy
            have h2 : x.1.2 = y.1.1 := congrArg Prod.snd hxy
            have hyx : x.1.2.fst < x.1.1.fst := by
              rw [h2, h1]
              exact y.2
            exact (lt_asymm x.2 hyx)
    | inr x =>
        cases y with
        | inl y =>
            exfalso
            have h1 : x.1.2 = y.1.1 := congrArg Prod.fst hxy
            have h2 : x.1.1 = y.1.2 := congrArg Prod.snd hxy
            have hyx : x.1.2.fst < x.1.1.fst := by
              rw [h1, h2]
              exact y.2
            exact (lt_asymm x.2 hyx)
        | inr y =>
            congr 1
            apply Subtype.ext
            exact Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [A, Fintype.card_sum, Fintype.card_prod, two_mul, pow_two] using hcard

/-- Choosing the two outward-oriented end edges injects a path in a closed
neighbourhood into an increasing pair of darts of the induced graph. -/
theorem closed_path_pair_count_direct (v : V) :
    (closedNeighborhoodPaths G v).card ≤
      2 * (closedNeighborhoodEdgeCount G v) ^ 2 := by
  let S : Set V := closedNeighborFinset G v
  let H : SimpleGraph S := G.induce S
  let A := {p // p ∈ closedNeighborhoodPaths G v}
  let B := {z : H.Dart × H.Dart // z.1.fst < z.2.fst}
  let code : A → B := fun p ↦ by
    have hp := (mem_closedNeighborhoodPaths (G := G)).mp p.2
    let x0 : S := ⟨p.1.vertex 0, hp 0⟩
    let x1 : S := ⟨p.1.vertex 1, hp 1⟩
    let x2 : S := ⟨p.1.vertex 2, hp 2⟩
    let x3 : S := ⟨p.1.vertex 3, hp 3⟩
    let d0 : H.Dart := ⟨(x0, x1), p.1.adj_zero_one⟩
    let d3 : H.Dart := ⟨(x3, x2), p.1.adj_two_three.symm⟩
    exact ⟨(d0, d3), p.1.2.2⟩
  have hcode : Function.Injective code := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i
    · exact congrArg (fun z : B ↦ z.1.1.fst.1) hpq
    · exact congrArg (fun z : B ↦ z.1.1.snd.1) hpq
    · exact congrArg (fun z : B ↦ z.1.2.snd.1) hpq
    · exact congrArg (fun z : B ↦ z.1.2.fst.1) hpq
  have hAB : Fintype.card A ≤ Fintype.card B :=
    Fintype.card_le_of_injective code hcode
  have hB : 2 * Fintype.card B ≤ (Fintype.card H.Dart) ^ 2 :=
    twice_card_increasingDartPairs_le H
  have hD : Fintype.card H.Dart =
      2 * closedNeighborhoodEdgeCount G v := by
    dsimp only [H, S]
    rw [(G.induce (closedNeighborFinset G v : Set V)).dart_card_eq_twice_card_edges,
      card_induced_closedNeighbor_eq G]
  have hA : Fintype.card A = (closedNeighborhoodPaths G v).card := by
    change Fintype.card ↑(closedNeighborhoodPaths G v) = _
    exact Fintype.card_coe _
  rw [hD] at hB
  rw [← hA]
  apply hAB.trans
  exact Nat.le_of_mul_le_mul_left (by
    calc
      2 * Fintype.card B ≤ (2 * closedNeighborhoodEdgeCount G v) ^ 2 := hB
      _ = 2 * (2 * (closedNeighborhoodEdgeCount G v) ^ 2) := by ring)
    Nat.two_pos

/-! ## The direct central `25 Δ e` estimate -/

/-- The graph induced by an open neighbourhood is `P₅`-free, since a
four-edge path there closes with its centre to a simple hexagon. -/
theorem erdos_gallai_neighborhood_direct (hC6 : WalkC6Free G) (v : V) :
    2 * (openNeighborhoodEdges G v).card ≤ 3 * G.degree v := by
  classical
  let S : Finset V := G.neighborFinset v
  let H : SimpleGraph (S : Set V) := G.induce (S : Set V)
  have hP5 : ¬ ∃ p : Fin 5 → (S : Set V), Function.Injective p ∧
      H.Adj (p 0) (p 1) ∧ H.Adj (p 1) (p 2) ∧
      H.Adj (p 2) (p 3) ∧ H.Adj (p 3) (p 4) := by
    rintro ⟨p, hp, h01, h12, h23, h34⟩
    have hpval : Function.Injective (fun i ↦ (p i).1) := by
      intro i j hij
      exact hp (Subtype.ext hij)
    have hv (i : Fin 5) : G.Adj v (p i).1 := by
      apply (G.mem_neighborFinset _ _).1
      simpa only [S, Finset.mem_coe] using (p i).2
    apply false_of_openNeighborhood_path_four G hC6
      (hv 0) (hv 1) (hv 2) (hv 3) (hv 4)
    · exact h01
    · exact h12
    · exact h23
    · exact h34
    · change List.Nodup (List.ofFn fun i : Fin 5 ↦ (p i).1)
      exact List.nodup_ofFn.mpr hpval
  have hEG := erdosGallai_path5 H hP5
  have hS : Fintype.card (S : Set V) = G.degree v := by
    simpa only [S, G.coe_neighborFinset] using
      G.card_neighborSet_eq_degree v
  have hedge : H.edgeFinset.card = (openNeighborhoodEdges G v).card := by
    dsimp only [H]
    rw [← G.card_filter_edgeFinset_toFinset_subset S]
    congr 1
    ext e
    simp only [Finset.mem_filter, openNeighborhoodEdges]
    constructor
    · rintro ⟨he, hsub⟩
      refine ⟨he, ?_⟩
      intro w hw
      change w ∈ S
      exact hsub (by simpa using hw)
    · rintro ⟨he, hadj⟩
      refine ⟨he, ?_⟩
      intro w hw
      change w ∈ S
      exact hadj w (by simpa using hw)
  rw [hedge, hS] at hEG
  exact hEG

/-- The direct open-neighbourhood estimate gives
`2 e[N[v]] ≤ 5 d(v)`. -/
theorem closedNeighborhoodEdgeCount_le_five_halves_direct
    (hC6 : WalkC6Free G) (v : V) :
    2 * closedNeighborhoodEdgeCount G v ≤ 5 * G.degree v := by
  dsimp [closedNeighborhoodEdgeCount]
  have h := erdos_gallai_neighborhood_direct G hC6 v
  omega

/-- The doubled number of paths charged to one closed neighbourhood is at
most `25 Δ d(v)`. -/
theorem twice_closedNeighborhoodPaths_le_direct
    (hC6 : WalkC6Free G) (v : V) :
    2 * (closedNeighborhoodPaths G v).card ≤
      25 * G.maxDegree * G.degree v := by
  let c := closedNeighborhoodEdgeCount G v
  let p := (closedNeighborhoodPaths G v).card
  have hp : p ≤ 2 * c ^ 2 := closed_path_pair_count_direct G v
  have hc : 2 * c ≤ 5 * G.degree v :=
    closedNeighborhoodEdgeCount_le_five_halves_direct G hC6 v
  have hd : G.degree v ≤ G.maxDegree := G.degree_le_maxDegree v
  calc
    2 * p ≤ 2 * (2 * c ^ 2) := Nat.mul_le_mul_left 2 hp
    _ = (2 * c) ^ 2 := by ring
    _ ≤ (5 * G.degree v) ^ 2 := Nat.pow_le_pow_left hc 2
    _ = 25 * G.degree v * G.degree v := by ring
    _ ≤ 25 * G.maxDegree * G.degree v := by
      exact Nat.mul_le_mul_right (G.degree v) (Nat.mul_le_mul_left 25 hd)

/-- The unconditional central/degenerate half of FNV Lemma 8.1. -/
theorem degenerate_multiplicity_bound_direct (hC6 : WalkC6Free G) :
    multiplicitySum G (degeneratePairs G) ≤
      25 * G.maxDegree * G.edgeFinset.card := by
  have hlocal :
      2 * (∑ v, (closedNeighborhoodPaths G v).card) ≤
        ∑ v, 25 * G.maxDegree * G.degree v := by
    simpa only [Finset.mul_sum] using
      Finset.sum_le_sum (fun v _ ↦
        twice_closedNeighborhoodPaths_le_direct G hC6 v)
  have hdegree : ∑ v, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have hcentral := Nat.mul_le_mul_left 2 (central_charge_direct G)
  have htwo :
      2 * multiplicitySum G (degeneratePairs G) ≤
        2 * (25 * G.maxDegree * G.edgeFinset.card) := by
    calc
      2 * multiplicitySum G (degeneratePairs G)
          ≤ 2 * (∑ v, (closedNeighborhoodPaths G v).card) := hcentral
      _ ≤ ∑ v, 25 * G.maxDegree * G.degree v := hlocal
      _ = 2 * (25 * G.maxDegree * G.edgeFinset.card) := by
        rw [← Finset.mul_sum, hdegree]
        ring
  exact Nat.le_of_mul_le_mul_left htwo Nat.two_pos

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/U8Shortcut.lean` -/

section
/-!
# A direct wedge injection for the nondegenerate U8 charge

This file replaces the quadrilateral-component classification in the
nondegenerate half of FNV Lemma 8.1.  A path occurrence is encoded by its
oriented outside edge, followed by its varying middle vertex.  Hexagon
freeness makes this code injective.
-/

open scoped BigOperators
open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

attribute [local instance] Classical.propDecidable

private theorem false_of_six_cycle_shortcut (hC6 : WalkC6Free G)
    {a b c d e f : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hef : G.Adj e f) (hfa : G.Adj f a)
    (hpair : [a, b, c, d, e, f].Nodup) : False := by
  let q : G.Walk a a :=
    .cons hab (.cons hbc (.cons hcd (.cons hde (.cons hef (.cons hfa .nil)))))
  have hq : q.IsCycle := by
    simp only [q, Walk.cons_isCycle_iff]
    simp_all [Walk.isPath_def, List.nodup_cons, eq_comm]
  exact hC6 a q hq (by simp [q])

/-- A path occurrence belonging to a nondegenerate exceptional endpoint
pair. -/
abbrev NondegenerateOccurrence :=
  Σ pi : {pi // pi ∈ nondegenerateExceptionalPairs G},
    {p // p ∈ pathFiber G pi.1}

namespace NondegenerateOccurrence

variable {G}

def pair (o : NondegenerateOccurrence G) : EndpointPair V := o.1.1

def pair_mem (o : NondegenerateOccurrence G) :
    o.pair ∈ nondegenerateExceptionalPairs G := o.1.2

def path (o : NondegenerateOccurrence G) : Path3 G := o.2.1

def path_mem (o : NondegenerateOccurrence G) :
    o.path ∈ pathFiber G o.pair := o.2.2

noncomputable def centre (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) : V :=
  nondegenerateStarCentre G hC6 o.pair o.pair_mem

def onLeft (hC6 : WalkC6Free G) (o : NondegenerateOccurrence G) : Prop :=
  nondegenerateStarOnLeft G hC6 o.pair o.pair_mem

noncomputable def outside (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) : V :=
  if o.onLeft hC6 then o.pair.1.1 else o.pair.1.2

noncomputable def far (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) : V :=
  if o.onLeft hC6 then o.pair.1.2 else o.pair.1.1

noncomputable def varying (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) : V :=
  if o.onLeft hC6 then o.path.vertex 2 else o.path.vertex 1

theorem varying_mem (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    o.varying hC6 ∈
      nondegenerateOtherMiddles G hC6 o.pair o.pair_mem := by
  by_cases hl : o.onLeft hC6
  · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    rw [varying, onLeft, if_pos hl, nondegenerateOtherMiddles, if_pos hl]
    exact Finset.mem_image.mpr ⟨o.path, o.path_mem, rfl⟩
  · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    rw [varying, onLeft, if_neg hl, nondegenerateOtherMiddles, if_neg hl]
    exact Finset.mem_image.mpr ⟨o.path, o.path_mem, rfl⟩

theorem centre_mem_base (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    o.centre hC6 ∈ nondegenerateBaseSide G hC6 o.pair o.pair_mem := by
  by_cases hl : o.onLeft hC6
  · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    rw [centre, nondegenerateBaseSide, if_pos hl]
    simp
  · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    rw [centre, nondegenerateBaseSide, if_neg hl]
    simp

theorem far_mem_base (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    o.far hC6 ∈ nondegenerateBaseSide G hC6 o.pair o.pair_mem := by
  by_cases hl : o.onLeft hC6
  · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    rw [far, onLeft, if_pos hl, nondegenerateBaseSide, if_pos hl]
    simp
  · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    rw [far, onLeft, if_neg hl, nondegenerateBaseSide, if_neg hl]
    simp

theorem centre_adj_other (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) {x : V}
    (hx : x ∈ nondegenerateOtherMiddles G hC6 o.pair o.pair_mem) :
    G.Adj (o.centre hC6) x :=
  nondegenerateBaseOther_adj G hC6 o.pair o.pair_mem
    (o.centre_mem_base hC6) hx

theorem far_adj_other (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) {x : V}
    (hx : x ∈ nondegenerateOtherMiddles G hC6 o.pair o.pair_mem) :
    G.Adj (o.far hC6) x :=
  nondegenerateBaseOther_adj G hC6 o.pair o.pair_mem
    (o.far_mem_base hC6) hx

theorem centre_not_mem_other (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    o.centre hC6 ∉ nondegenerateOtherMiddles G hC6 o.pair o.pair_mem := by
  exact Finset.disjoint_left.mp
    (disjoint_nondegenerateBaseOther G hC6 o.pair o.pair_mem)
    (o.centre_mem_base hC6)

theorem far_not_mem_other (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    o.far hC6 ∉ nondegenerateOtherMiddles G hC6 o.pair o.pair_mem := by
  exact Finset.disjoint_left.mp
    (disjoint_nondegenerateBaseOther G hC6 o.pair o.pair_mem)
    (o.far_mem_base hC6)

theorem centre_ne_far (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) : o.centre hC6 ≠ o.far hC6 := by
  intro heq
  have hcard := card_nondegenerateBaseSide G hC6 o.pair o.pair_mem
  by_cases hl : o.onLeft hC6
  · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    change nondegenerateStarCentre G hC6 o.pair o.pair_mem =
      (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then o.pair.1.2
       else o.pair.1.1) at heq
    rw [if_pos hl] at heq
    rw [nondegenerateBaseSide, if_pos hl, heq] at hcard
    simp at hcard
  · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    change nondegenerateStarCentre G hC6 o.pair o.pair_mem =
      (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then o.pair.1.2
       else o.pair.1.1) at heq
    rw [if_neg hl] at heq
    rw [nondegenerateBaseSide, if_neg hl, heq] at hcard
    simp at hcard

theorem outside_adj_centre (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    G.Adj (o.outside hC6) (o.centre hC6) := by
  have hend := (mem_pathFiber (G := G)).mp o.path_mem
  by_cases hl : o.onLeft hC6
  · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    have h0 : o.path.vertex 0 = o.pair.1.1 :=
      congrArg (fun z : EndpointPair V ↦ z.1.1) hend
    rw [outside, onLeft, if_pos hl, centre, ← h0, hl o.path o.path_mem]
    exact o.path.adj_zero_one
  · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    have h3 : o.path.vertex 3 = o.pair.1.2 :=
      congrArg (fun z : EndpointPair V ↦ z.1.2) hend
    rw [outside, onLeft, if_neg hl, centre, ← h3,
      nondegenerateStarCentre_spec_right G hC6 o.pair o.pair_mem hl
        o.path o.path_mem]
    exact o.path.adj_two_three.symm

theorem centre_adj_varying (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    G.Adj (o.centre hC6) (o.varying hC6) :=
  o.centre_adj_other hC6 (o.varying_mem hC6)

theorem far_adj_varying (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    G.Adj (o.far hC6) (o.varying hC6) :=
  o.far_adj_other hC6 (o.varying_mem hC6)

theorem outside_not_mem_other (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    o.outside hC6 ∉ nondegenerateOtherMiddles G hC6 o.pair o.pair_mem := by
  by_cases hl : o.onLeft hC6
  · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    rw [nondegenerateOtherMiddles, if_pos hl]
    intro hout
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hout
    have hend := (mem_pathFiber (G := G)).mp hp
    have h0 : p.vertex 0 = o.pair.1.1 :=
      congrArg (fun z : EndpointPair V ↦ z.1.1) hend
    apply p.injective.ne (show (0 : Fin 4) ≠ 2 by decide)
    have hout_eq : o.outside hC6 = o.pair.1.1 := by
      rw [outside, onLeft, if_pos hl]
    exact h0.trans (hout_eq.symm.trans heq.symm)
  · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    rw [nondegenerateOtherMiddles, if_neg hl]
    intro hout
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hout
    have hend := (mem_pathFiber (G := G)).mp hp
    have h3 : p.vertex 3 = o.pair.1.2 :=
      congrArg (fun z : EndpointPair V ↦ z.1.2) hend
    apply p.injective.ne (show (3 : Fin 4) ≠ 1 by decide)
    have hout_eq : o.outside hC6 = o.pair.1.2 := by
      rw [outside, onLeft, if_neg hl]
    exact h3.trans (hout_eq.symm.trans heq.symm)

/-- The far endpoint is not adjacent to the common star centre.  Otherwise
that centre's closed neighbourhood would contain every path in the fibre,
contrary to nondegeneracy. -/
theorem not_adj_centre_far (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) :
    ¬ G.Adj (o.centre hC6) (o.far hC6) := by
  intro hfar
  apply nondegenerateExceptional_not_central G o.pair_mem
  refine ⟨o.centre hC6, ?_⟩
  intro p hp i
  rw [mem_closedNeighborFinset]
  have hend := (mem_pathFiber (G := G)).mp hp
  have h0 : p.vertex 0 = o.pair.1.1 :=
    congrArg (fun z : EndpointPair V ↦ z.1.1) hend
  have h3 : p.vertex 3 = o.pair.1.2 :=
    congrArg (fun z : EndpointPair V ↦ z.1.2) hend
  by_cases hl : o.onLeft hC6
  · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    have hs := hl p hp
    unfold centre at hfar ⊢
    fin_cases i
    · right
      change G.Adj (nondegenerateStarCentre G hC6 o.pair o.pair_mem)
        (p.vertex (0 : Fin 4))
      rw [hs]
      exact p.adj_zero_one.symm
    · exact Or.inl hs.symm
    · right
      rw [hs]
      exact p.adj_one_two
    · right
      rw [far, onLeft, if_pos hl, ← h3] at hfar
      exact hfar
  · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
    have hs := nondegenerateStarCentre_spec_right G hC6 o.pair o.pair_mem hl p hp
    unfold centre at hfar ⊢
    fin_cases i
    · right
      rw [far, onLeft, if_neg hl, ← h0] at hfar
      exact hfar
    · right
      rw [hs]
      exact p.adj_one_two.symm
    · exact Or.inl hs.symm
    · right
      change G.Adj (nondegenerateStarCentre G hC6 o.pair o.pair_mem)
        (p.vertex (3 : Fin 4))
      rw [hs]
      exact p.adj_two_three

/-- A multiplicity-two ordinary exceptional pair has adjacent endpoints. -/
theorem outside_adj_far_of_multiplicity_eq_two (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G)
    (hmul : pathMultiplicity G o.pair = 2) :
    G.Adj (o.outside hC6) (o.far hC6) := by
  have hord : o.pair ∈ ordinaryExceptionalPairs G :=
    (Finset.mem_sdiff.mp o.pair_mem).1
  rcases (Finset.mem_filter.mp hord).2 with hadj | hthree
  · by_cases hl : o.onLeft hC6
    · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
      rw [outside, far, onLeft, if_pos hl, if_pos hl]
      exact hadj.2
    · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hl
      rw [outside, far, onLeft, if_neg hl, if_neg hl]
      exact hadj.2.symm
  · omega

/-- Two nondegenerate occurrences with the same outside endpoint, star
centre, and varying middle vertex have the same far endpoint.  The proof is
the two-hexagon collision argument behind the wedge injection. -/
theorem far_eq_of_code (hC6 : WalkC6Free G)
    {o r : NondegenerateOccurrence G}
    (ha : o.outside hC6 = r.outside hC6)
    (hw : o.centre hC6 = r.centre hC6)
    (hx : o.varying hC6 = r.varying hC6) :
    o.far hC6 = r.far hC6 := by
  by_contra hfar
  let X := nondegenerateOtherMiddles G hC6 o.pair o.pair_mem
  let Y := nondegenerateOtherMiddles G hC6 r.pair r.pair_mem
  have hxX : o.varying hC6 ∈ X := o.varying_mem hC6
  have hxY : r.varying hC6 ∈ Y := r.varying_mem hC6
  have hcardX : 2 ≤ X.card := by
    rw [card_nondegenerateOtherMiddles G hC6 o.pair o.pair_mem]
    exact nondegenerateExceptional_two_le G o.pair_mem
  have hcardY : 2 ≤ Y.card := by
    rw [card_nondegenerateOtherMiddles G hC6 r.pair r.pair_mem]
    exact nondegenerateExceptional_two_le G r.pair_mem
  obtain ⟨y, hy, hyx⟩ := X.exists_mem_ne (by omega) (o.varying hC6)
  obtain ⟨z, hz, hzx⟩ := Y.exists_mem_ne (by omega) (r.varying hC6)
  have halternates : ∀ {y z : V}, y ∈ X → y ≠ o.varying hC6 →
      z ∈ Y → z ≠ r.varying hC6 → y = z := by
    intro y z hy' hyx' hz' hzx'
    by_contra hyz
    have hboz : o.far hC6 ≠ z := by
      intro e
      apply o.not_adj_centre_far hC6
      rw [e, hw]
      exact r.centre_adj_other hC6 hz'
    have hbry : r.far hC6 ≠ y := by
      intro e
      apply r.not_adj_centre_far hC6
      rw [e, ← hw]
      exact o.centre_adj_other hC6 hy'
    have hboy : o.far hC6 ≠ y := by
      intro e
      apply o.far_not_mem_other hC6
      rw [e]
      exact hy'
    have hbow : o.far hC6 ≠ o.centre hC6 := (o.centre_ne_far hC6).symm
    have hbox : o.far hC6 ≠ o.varying hC6 := by
      intro e
      apply o.far_not_mem_other hC6
      rw [e]
      exact hxX
    have hyw : y ≠ o.centre hC6 := by
      intro e
      apply o.centre_not_mem_other hC6
      rw [← e]
      exact hy'
    have hyxo : y ≠ o.varying hC6 := hyx'
    have hwz : o.centre hC6 ≠ z := by
      intro e
      apply r.centre_not_mem_other hC6
      rw [← hw, e]
      exact hz'
    have hwbr : o.centre hC6 ≠ r.far hC6 := by
      rw [hw]
      exact r.centre_ne_far hC6
    have hwx : o.centre hC6 ≠ o.varying hC6 := by
      intro e
      apply o.centre_not_mem_other hC6
      rw [e]
      exact hxX
    have hzbr : z ≠ r.far hC6 := by
      intro e
      apply r.far_not_mem_other hC6
      rw [← e]
      exact hz'
    have hzx_o : z ≠ o.varying hC6 := by
      intro e
      exact hzx' (e.trans hx)
    have hbrx : r.far hC6 ≠ o.varying hC6 := by
      intro e
      apply r.far_not_mem_other hC6
      rw [e, hx]
      exact hxY
    apply false_of_six_cycle_shortcut G hC6
      (o.far_adj_other hC6 hy')
      (o.centre_adj_other hC6 hy').symm
      (by rw [hw]; exact r.centre_adj_other hC6 hz')
      (r.far_adj_other hC6 hz').symm
      (by rw [hx]; exact r.far_adj_varying hC6)
      (o.far_adj_varying hC6).symm
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or]
    aesop
  have hyz : y = z := halternates hy hyx hz hzx
  have hsubX : X ⊆ {o.varying hC6, y} := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases htx : t = o.varying hC6
    · exact Or.inl htx
    · exact Or.inr ((halternates ht htx hz hzx).trans hyz.symm)
  have hsubY : Y ⊆ {r.varying hC6, y} := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases htx : t = r.varying hC6
    · exact Or.inl htx
    · exact Or.inr (halternates hy hyx ht htx).symm
  have hcardX' : X.card = 2 := by
    have hle := Finset.card_le_card hsubX
    have hp : ({o.varying hC6, y} : Finset V).card = 2 :=
      Finset.card_pair hyx.symm
    omega
  have hcardY' : Y.card = 2 := by
    have hle := Finset.card_le_card hsubY
    have hp : ({r.varying hC6, y} : Finset V).card = 2 := by
      apply Finset.card_pair
      intro e
      apply hyx
      rw [← e, ← hx]
    omega
  have hmulO : pathMultiplicity G o.pair = 2 := by
    rw [← card_nondegenerateOtherMiddles G hC6 o.pair o.pair_mem]
    exact hcardX'
  have hmulR : pathMultiplicity G r.pair = 2 := by
    rw [← card_nondegenerateOtherMiddles G hC6 r.pair r.pair_mem]
    exact hcardY'
  have hyY : y ∈ Y := by rw [hyz]; exact hz
  have ha_bo := o.outside_adj_far_of_multiplicity_eq_two hC6 hmulO
  have ha_br : G.Adj (o.outside hC6) (r.far hC6) := by
    rw [ha]
    exact r.outside_adj_far_of_multiplicity_eq_two hC6 hmulR
  have habo : o.outside hC6 ≠ o.far hC6 := ha_bo.ne
  have hax : o.outside hC6 ≠ o.varying hC6 := by
    intro e
    apply o.outside_not_mem_other hC6
    rw [e]
    exact hxX
  have habr : o.outside hC6 ≠ r.far hC6 := ha_br.ne
  have hay : o.outside hC6 ≠ y := by
    intro e
    apply o.outside_not_mem_other hC6
    rw [e]
    exact hy
  have haw : o.outside hC6 ≠ o.centre hC6 := (o.outside_adj_centre hC6).ne
  have hbox : o.far hC6 ≠ o.varying hC6 := by
    intro e
    apply o.far_not_mem_other hC6
    rw [e]
    exact hxX
  have hboy : o.far hC6 ≠ y := by
    intro e
    apply o.far_not_mem_other hC6
    rw [e]
    exact hy
  have hbow : o.far hC6 ≠ o.centre hC6 := (o.centre_ne_far hC6).symm
  have hxbr : o.varying hC6 ≠ r.far hC6 := by
    intro e
    apply r.far_not_mem_other hC6
    rw [← e, hx]
    exact hxY
  have hxy : o.varying hC6 ≠ y := hyx.symm
  have hxw : o.varying hC6 ≠ o.centre hC6 := by
    intro e
    apply o.centre_not_mem_other hC6
    rw [← e]
    exact hxX
  have hbry : r.far hC6 ≠ y := by
    intro e
    apply r.far_not_mem_other hC6
    rw [e]
    exact hyY
  have hbrw : r.far hC6 ≠ o.centre hC6 := by
    rw [hw]
    exact (r.centre_ne_far hC6).symm
  have hyw : y ≠ o.centre hC6 := by
    intro e
    apply o.centre_not_mem_other hC6
    rw [← e]
    exact hy
  apply false_of_six_cycle_shortcut G hC6
    ha_bo (o.far_adj_varying hC6)
    (by rw [hx]; exact (r.far_adj_varying hC6).symm)
    (r.far_adj_other hC6 hyY)
    (o.centre_adj_other hC6 hy).symm
    (o.outside_adj_centre hC6).symm
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or]
  aesop

end NondegenerateOccurrence

/-- The finite universe of oriented length-two wedges. -/
abbrev OrientedWedge :=
  Σ w : V, (↥(G.neighborFinset w)) × (↥(G.neighborFinset w))

/-- The outside edge followed by the varying middle vertex. -/
noncomputable def nondegenerateWedgeCode (hC6 : WalkC6Free G)
    (o : NondegenerateOccurrence G) : OrientedWedge G :=
  ⟨o.centre hC6,
    (⟨o.outside hC6, (G.mem_neighborFinset _ _).mpr (o.outside_adj_centre hC6).symm⟩,
     ⟨o.varying hC6, (G.mem_neighborFinset _ _).mpr (o.centre_adj_varying hC6)⟩)⟩

private theorem occurrence_eq_of_code_data (hC6 : WalkC6Free G)
    {o r : NondegenerateOccurrence G}
    (ha : o.outside hC6 = r.outside hC6)
    (hw : o.centre hC6 = r.centre hC6)
    (hx : o.varying hC6 = r.varying hC6)
    (hb : o.far hC6 = r.far hC6) : o = r := by
  have hendo := (mem_pathFiber (G := G)).mp o.path_mem
  have hendr := (mem_pathFiber (G := G)).mp r.path_mem
  have ho0 : o.path.vertex 0 = o.pair.1.1 :=
    congrArg (fun z : EndpointPair V ↦ z.1.1) hendo
  have ho3 : o.path.vertex 3 = o.pair.1.2 :=
    congrArg (fun z : EndpointPair V ↦ z.1.2) hendo
  have hr0 : r.path.vertex 0 = r.pair.1.1 :=
    congrArg (fun z : EndpointPair V ↦ z.1.1) hendr
  have hr3 : r.path.vertex 3 = r.pair.1.2 :=
    congrArg (fun z : EndpointPair V ↦ z.1.2) hendr
  by_cases hlo : o.onLeft hC6
  · change nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hlo
    by_cases hlr : r.onLeft hC6
    · change nondegenerateStarOnLeft G hC6 r.pair r.pair_mem at hlr
      have ha' : o.pair.1.1 = r.pair.1.1 := by
        change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
          o.pair.1.1 else o.pair.1.2) =
          (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
            r.pair.1.1 else r.pair.1.2) at ha
        rw [if_pos hlo, if_pos hlr] at ha
        exact ha
      have hb' : o.pair.1.2 = r.pair.1.2 := by
        change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
          o.pair.1.2 else o.pair.1.1) =
          (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
            r.pair.1.2 else r.pair.1.1) at hb
        rw [if_pos hlo, if_pos hlr] at hb
        exact hb
      have hpair : o.pair = r.pair := Subtype.ext (Prod.ext ha' hb')
      have hpath : o.path = r.path := by
        apply Subtype.ext
        funext i
        fin_cases i
        · exact ho0.trans (ha'.trans hr0.symm)
        · exact (hlo o.path o.path_mem).symm.trans
            (hw.trans (hlr r.path r.path_mem))
        · change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
            o.path.vertex 2 else o.path.vertex 1) =
            (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
              r.path.vertex 2 else r.path.vertex 1) at hx
          rw [if_pos hlo, if_pos hlr] at hx
          exact hx
        · exact ho3.trans (hb'.trans hr3.symm)
      rcases o with ⟨⟨opi, ohpi⟩, ⟨op, ohp⟩⟩
      rcases r with ⟨⟨rpi, rhpi⟩, ⟨rp, rhp⟩⟩
      change opi = rpi at hpair
      change op = rp at hpath
      subst rpi
      subst rp
      rfl
    · change ¬ nondegenerateStarOnLeft G hC6 r.pair r.pair_mem at hlr
      have ha' : o.pair.1.1 = r.pair.1.2 := by
        change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
          o.pair.1.1 else o.pair.1.2) =
          (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
            r.pair.1.1 else r.pair.1.2) at ha
        rw [if_pos hlo, if_neg hlr] at ha
        exact ha
      have hb' : o.pair.1.2 = r.pair.1.1 := by
        change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
          o.pair.1.2 else o.pair.1.1) =
          (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
            r.pair.1.2 else r.pair.1.1) at hb
        rw [if_pos hlo, if_neg hlr] at hb
        exact hb
      exfalso
      have hrev : o.pair.1.2 < o.pair.1.1 := by
        calc
          o.pair.1.2 = r.pair.1.1 := hb'
          _ < r.pair.1.2 := r.pair.2
          _ = o.pair.1.1 := ha'.symm
      exact (lt_asymm o.pair.2 hrev).elim
  · change ¬ nondegenerateStarOnLeft G hC6 o.pair o.pair_mem at hlo
    by_cases hlr : r.onLeft hC6
    · change nondegenerateStarOnLeft G hC6 r.pair r.pair_mem at hlr
      have ha' : o.pair.1.2 = r.pair.1.1 := by
        change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
          o.pair.1.1 else o.pair.1.2) =
          (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
            r.pair.1.1 else r.pair.1.2) at ha
        rw [if_neg hlo, if_pos hlr] at ha
        exact ha
      have hb' : o.pair.1.1 = r.pair.1.2 := by
        change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
          o.pair.1.2 else o.pair.1.1) =
          (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
            r.pair.1.2 else r.pair.1.1) at hb
        rw [if_neg hlo, if_pos hlr] at hb
        exact hb
      exfalso
      have hrev : o.pair.1.2 < o.pair.1.1 := by
        calc
          o.pair.1.2 = r.pair.1.1 := ha'
          _ < r.pair.1.2 := r.pair.2
          _ = o.pair.1.1 := hb'.symm
      exact (lt_asymm o.pair.2 hrev).elim
    · change ¬ nondegenerateStarOnLeft G hC6 r.pair r.pair_mem at hlr
      have ha' : o.pair.1.2 = r.pair.1.2 := by
        change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
          o.pair.1.1 else o.pair.1.2) =
          (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
            r.pair.1.1 else r.pair.1.2) at ha
        rw [if_neg hlo, if_neg hlr] at ha
        exact ha
      have hb' : o.pair.1.1 = r.pair.1.1 := by
        change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
          o.pair.1.2 else o.pair.1.1) =
          (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
            r.pair.1.2 else r.pair.1.1) at hb
        rw [if_neg hlo, if_neg hlr] at hb
        exact hb
      have hpair : o.pair = r.pair := Subtype.ext (Prod.ext hb' ha')
      have hso := nondegenerateStarCentre_spec_right G hC6 o.pair o.pair_mem hlo
      have hsr := nondegenerateStarCentre_spec_right G hC6 r.pair r.pair_mem hlr
      have hpath : o.path = r.path := by
        apply Subtype.ext
        funext i
        fin_cases i
        · exact ho0.trans (hb'.trans hr0.symm)
        · change (if nondegenerateStarOnLeft G hC6 o.pair o.pair_mem then
            o.path.vertex 2 else o.path.vertex 1) =
            (if nondegenerateStarOnLeft G hC6 r.pair r.pair_mem then
              r.path.vertex 2 else r.path.vertex 1) at hx
          rw [if_neg hlo, if_neg hlr] at hx
          exact hx
        · exact (hso o.path o.path_mem).symm.trans
            (hw.trans (hsr r.path r.path_mem))
        · exact ho3.trans (ha'.trans hr3.symm)
      rcases o with ⟨⟨opi, ohpi⟩, ⟨op, ohp⟩⟩
      rcases r with ⟨⟨rpi, rhpi⟩, ⟨rp, rhp⟩⟩
      change opi = rpi at hpair
      change op = rp at hpath
      subst rpi
      subst rp
      rfl

theorem nondegenerateWedgeCode_injective (hC6 : WalkC6Free G) :
    Function.Injective (nondegenerateWedgeCode G hC6) := by
  intro o r hcode
  have hw : o.centre hC6 = r.centre hC6 :=
    congrArg Sigma.fst hcode
  have ha : o.outside hC6 = r.outside hC6 :=
    congrArg (fun z : OrientedWedge G ↦ z.2.1.1) hcode
  have hx : o.varying hC6 = r.varying hC6 :=
    congrArg (fun z : OrientedWedge G ↦ z.2.2.1) hcode
  exact occurrence_eq_of_code_data G hC6 ha hw hx
    (NondegenerateOccurrence.far_eq_of_code hC6 ha hw hx)

theorem card_nondegenerateOccurrence_eq_multiplicitySum :
    Fintype.card (NondegenerateOccurrence G) =
      multiplicitySum G (nondegenerateExceptionalPairs G) := by
  calc
    Fintype.card (NondegenerateOccurrence G) =
        ∑ pi : {pi // pi ∈ nondegenerateExceptionalPairs G},
          Fintype.card {p // p ∈ pathFiber G pi.1} := by
      simp only [NondegenerateOccurrence, Fintype.card_sigma]
    _ = ∑ pi : {pi // pi ∈ nondegenerateExceptionalPairs G},
          (pathFiber G pi.1).card := by
      simp only [Fintype.card_coe]
    _ = multiplicitySum G (nondegenerateExceptionalPairs G) := by
      unfold multiplicitySum pathMultiplicity
      have hatt : (nondegenerateExceptionalPairs G).attach =
          (Finset.univ : Finset
            {pi // pi ∈ nondegenerateExceptionalPairs G}) := by
        ext pi
        simp
      have hs := Finset.sum_attach (nondegenerateExceptionalPairs G)
        (fun pi : EndpointPair V ↦ (pathFiber G pi).card)
      rw [hatt] at hs
      exact hs

theorem card_orientedWedge_eq_sum_degree_sq :
    Fintype.card (OrientedWedge G) = ∑ v, G.degree v * G.degree v := by
  simp only [OrientedWedge, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_coe, G.card_neighborFinset_eq_degree]

/-- The U1-free nondegenerate half: every occurrence injects into an
oriented wedge, of which there are at most `2 * Δ * e`. -/
theorem nondegenerate_multiplicity_bound_shortcut (hC6 : WalkC6Free G) :
    multiplicitySum G (nondegenerateExceptionalPairs G) ≤
      2 * G.maxDegree * G.edgeFinset.card := by
  have hinj : Fintype.card (NondegenerateOccurrence G) ≤
      Fintype.card (OrientedWedge G) :=
    Fintype.card_le_of_injective (nondegenerateWedgeCode G hC6)
      (nondegenerateWedgeCode_injective G hC6)
  have hsquares : (∑ v, G.degree v * G.degree v) ≤
      ∑ v, G.maxDegree * G.degree v := by
    exact Finset.sum_le_sum fun v _ ↦
      Nat.mul_le_mul_right (G.degree v) (G.degree_le_maxDegree v)
  rw [card_nondegenerateOccurrence_eq_multiplicitySum G,
    card_orientedWedge_eq_sum_degree_sq G] at hinj
  calc
    multiplicitySum G (nondegenerateExceptionalPairs G)
        ≤ ∑ v, G.degree v * G.degree v := hinj
    _ ≤ ∑ v, G.maxDegree * G.degree v := hsquares
    _ = G.maxDegree * (∑ v, G.degree v) := by rw [Finset.mul_sum]
    _ = G.maxDegree * (2 * G.edgeFinset.card) := by
      rw [G.sum_degrees_eq_twice_card_edges]
    _ = 2 * G.maxDegree * G.edgeFinset.card := by ring

/-- Unconditional FNV U8.  The wedge injection gives the stronger constant
`27`; the displayed `35` is the traditional statement consumed downstream. -/
theorem fnvU8Direct (hC6 : WalkC6Free G) :
    multiplicitySum G (generalExceptionalPairs G) ≤
      35 * G.maxDegree * G.edgeFinset.card := by
  have hd := degenerate_multiplicity_bound_direct G hC6
  have hn := nondegenerate_multiplicity_bound_shortcut G hC6
  unfold multiplicitySum at hd hn ⊢
  rw [generalExceptionalPairs_eq G]
  rw [Finset.sum_union (degenerate_disjoint_nondegenerate G)]
  calc
    (∑ pi ∈ degeneratePairs G, pathMultiplicity G pi) +
          ∑ pi ∈ nondegenerateExceptionalPairs G, pathMultiplicity G pi
        ≤ 25 * G.maxDegree * G.edgeFinset.card +
          2 * G.maxDegree * G.edgeFinset.card := Nat.add_le_add hd hn
    _ = 27 * (G.maxDegree * G.edgeFinset.card) := by ring
    _ ≤ 35 * (G.maxDegree * G.edgeFinset.card) :=
      Nat.mul_le_mul_right (G.maxDegree * G.edgeFinset.card) (by omega)
    _ = 35 * G.maxDegree * G.edgeFinset.card := by ring

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/WeakUpper.lean` -/

section
/-!
# A coarse unconditional upper bound for the hexagon extremal number

The sharp Füredi--Naor--Verstraëte upper constant is not needed for the
Morris--Saxton counterexample when the four-fold matching blow-up is used.
This file proves the simpler eventual estimate

`ex(n, C₆) < (16 / 25) n^(4/3)`.

The proof uses only the large-girth degree comparison (U2--U3), the general
three-edge-path lower bound (U4), and the exceptional-multiplicity estimate
(U8).  A least counterexample to a bound with leading constant `63 / 100`
has minimum degree large enough for U3 to give `Δ ≤ 200 n^(1/3)`.
U4 and U8 then give an impossible scalar inequality.  Finally the strict
gap `63/100 < 16/25` absorbs the fixed linear error.
-/

open scoped BigOperators
open Finset SimpleGraph

noncomputable section

private def weakLeading : ℝ := 63 / 100

private def weakLinear : ℝ := 10000

private def weakThreshold (n : ℕ) : ℝ :=
  weakLeading * (n : ℝ) ^ (4 / 3 : ℝ) + weakLinear * n

private theorem weakLeading_pos : 0 < weakLeading := by
  norm_num [weakLeading]

/-! ## Elementary real-power calculus -/

/-- An elementary lower secant estimate used when one vertex is deleted. -/
private theorem rpow_four_thirds_step_lower {x : ℝ} (hx : 1 ≤ x) :
    x ^ (1 / 3 : ℝ) - 1 ≤
      x ^ (4 / 3 : ℝ) - (x - 1) ^ (4 / 3 : ℝ) := by
  by_cases hxeq : x = 1
  · subst x
    norm_num
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hxsubpos : 0 < x - 1 := sub_pos.mpr (lt_of_le_of_ne hx (Ne.symm hxeq))
  have hroot : x ^ (1 / 3 : ℝ) ≤ (x - 1) ^ (1 / 3 : ℝ) + 1 := by
    have h := Real.rpow_add_le_add_rpow (sub_nonneg.mpr hx) (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) ≤ 1)
    simpa using h
  have hmono : (x - 1) ^ (1 / 3 : ℝ) ≤ x ^ (1 / 3 : ℝ) := by
    exact Real.rpow_le_rpow (sub_nonneg.mpr hx) (by linarith) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hmono hxpos.le
  have hxpow : x ^ (4 / 3 : ℝ) = x * x ^ (1 / 3 : ℝ) := by
    calc
      x ^ (4 / 3 : ℝ) = x ^ ((1 : ℝ) + 1 / 3) := by norm_num
      _ = x ^ (1 : ℝ) * x ^ (1 / 3 : ℝ) := Real.rpow_add hxpos 1 (1 / 3)
      _ = _ := by rw [Real.rpow_one]
  have hxsubpow :
      (x - 1) ^ (4 / 3 : ℝ) = (x - 1) * (x - 1) ^ (1 / 3 : ℝ) := by
    calc
      (x - 1) ^ (4 / 3 : ℝ) = (x - 1) ^ ((1 : ℝ) + 1 / 3) := by norm_num
      _ = (x - 1) ^ (1 : ℝ) * (x - 1) ^ (1 / 3 : ℝ) :=
        Real.rpow_add hxsubpos 1 (1 / 3)
      _ = _ := by rw [Real.rpow_one]
  rw [hxpow, hxsubpow]
  nlinarith

private theorem weakThreshold_step_lower {n : ℕ} (hn : 0 < n) :
    (63 / 100 : ℝ) * ((n : ℝ) ^ (1 / 3 : ℝ) - 1) + weakLinear ≤
      weakThreshold n - weakThreshold (n - 1) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdiff := rpow_four_thirds_step_lower hn1
  have hmul := mul_le_mul_of_nonneg_left hdiff weakLeading_pos.le
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne')]
    norm_num
  unfold weakThreshold weakLeading weakLinear
  rw [hcast]
  norm_num at hmul ⊢
  nlinarith

private theorem nat_rpow_one_third_cube {n : ℕ} (hn : 0 < n) :
    ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = n := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
  norm_num

private theorem nat_rpow_four_thirds_eq {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (4 / 3 : ℝ) =
      (n : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hnℝ : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    (n : ℝ) ^ (4 / 3 : ℝ) =
        (n : ℝ) ^ ((1 : ℝ) + 1 / 3) := by norm_num
    _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) :=
      Real.rpow_add hnℝ 1 (1 / 3)
    _ = _ := by rw [Real.rpow_one]

/-! ## Direct U3 and the standard cycle predicate -/

private theorem walkC6Free_of_free {V : Type*} (G : SimpleGraph V)
    (hfree : (SimpleGraph.cycleGraph 6).Free G) : WalkC6Free G := by
  intro v q hq hlen
  apply hfree
  rw [SimpleGraph.cycleGraph_isContained_iff (by omega : 2 < 6)]
  exact ⟨v, q, hq, hlen⟩

/-- U2 supplies the certificate required by the graph-level U3 theorem. -/
private theorem degree_comparison_direct
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : (SimpleGraph.cycleGraph 6).Free G) :
    G.maxDegree * (G.minDegree - 4) ^ 2 ≤ 64 * Fintype.card V := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h => simp
  | inr h =>
      apply GirthDegree.degree_comparison G G.minDegree G.maxDegree
      · exact fun v ↦ G.minDegree_le_degree v
      · obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
        exact ⟨v, hv.symm⟩
      · exact hfree
      · intro c _hc
        exact GirthDegree.Bigraph.quadrilateralForestCertificate_direct
          (GirthDegree.crossingBigraph G c)
          (GirthDegree.crossingBigraph_noSixCycle_of_free G hfree c)

/-! ## Identifying the U4 and U8 path counts -/

private abbrev U4PathIndex {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  Σ u : V, Σ v : {v // v ∈ G.neighborFinset u},
    {p : V × V // p ∈ u4LocalPaths G u v}

private def u4IndexPath {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : U4PathIndex G) :
    Fin 4 → V :=
  ![z.2.2.1.1, z.1, z.2.1.1, z.2.2.1.2]

private theorem u4IndexPath_isPath3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : U4PathIndex G) :
    IsPath3 G (u4IndexPath G z) := by
  rcases Finset.mem_filter.mp z.2.2.2 with ⟨hp, hne⟩
  rcases Finset.mem_product.mp hp with ⟨hx, hy⟩
  have huv : G.Adj z.1 z.2.1.1 := (G.mem_neighborFinset _ _).1 z.2.1.2
  have hux : G.Adj z.1 z.2.2.1.1 := (G.mem_neighborFinset _ _).1 hx
  have hvy : G.Adj z.2.1.1 z.2.2.1.2 := (G.mem_neighborFinset _ _).1 hy
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [u4IndexPath, G.loopless]
  · exact ⟨hux.symm, huv, hvy⟩

private def path3ToU4Index {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Path3 G ⊕ Path3 G → U4PathIndex G
  | Sum.inl p =>
      ⟨p.vertex 1, ⟨⟨p.vertex 2, by
          apply (G.mem_neighborFinset _ _).2
          exact p.adj_one_two⟩,
        ⟨(p.vertex 0, p.vertex 3), by
          rw [u4LocalPaths, Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨(G.mem_neighborFinset _ _).2 p.adj_zero_one.symm,
            (G.mem_neighborFinset _ _).2 p.adj_two_three⟩,
            p.injective.ne (by decide), p.injective.ne (by decide),
            p.injective.ne (by decide)⟩⟩⟩⟩
  | Sum.inr p =>
      ⟨p.vertex 2, ⟨⟨p.vertex 1, by
          apply (G.mem_neighborFinset _ _).2
          exact p.adj_one_two.symm⟩,
        ⟨(p.vertex 3, p.vertex 0), by
          rw [u4LocalPaths, Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨(G.mem_neighborFinset _ _).2 p.adj_two_three,
            (G.mem_neighborFinset _ _).2 p.adj_zero_one.symm⟩,
            p.injective.ne (by decide), p.injective.ne (by decide),
            p.injective.ne (by decide)⟩⟩⟩⟩

private def u4IndexToPath3 {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    U4PathIndex G → Path3 G ⊕ Path3 G := fun z ↦
  if h : z.2.2.1.1 < z.2.2.1.2 then
    Sum.inl ⟨u4IndexPath G z, u4IndexPath_isPath3 G z, h⟩
  else
    Sum.inr ⟨u4IndexPath G z ∘ Fin.rev, by
      have hp := u4IndexPath_isPath3 G z
      constructor
      · exact hp.1.comp Fin.rev_injective
      · exact ⟨by simpa [Function.comp_def] using hp.2.2.2.symm,
          by simpa [Function.comp_def] using hp.2.2.1.symm,
          by simpa [Function.comp_def] using hp.2.1.symm⟩,
      by
        have hne := (u4IndexPath_isPath3 G z).1.ne
          (show (0 : Fin 4) ≠ 3 by decide)
        simpa [Function.comp_def, u4IndexPath] using
          (lt_of_le_of_ne (le_of_not_gt h) hne.symm)⟩

private def u4PathIndexEquivPath3Sum {V : Type*} [Fintype V] [DecidableEq V]
    [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    U4PathIndex G ≃ Path3 G ⊕ Path3 G where
  toFun := u4IndexToPath3 G
  invFun := path3ToU4Index G
  left_inv := by
    intro z
    rw [u4IndexToPath3]
    split_ifs with h
    · rfl
    · rfl
  right_inv := by
    intro p
    cases p with
    | inl p =>
        rw [path3ToU4Index, u4IndexToPath3]
        split_ifs with h
        · apply congrArg Sum.inl
          apply Subtype.ext
          funext i
          fin_cases i <;> rfl
        · exact (h p.2.2).elim
    | inr p =>
        rw [path3ToU4Index, u4IndexToPath3]
        split_ifs with h
        · exact (lt_asymm h p.2.2).elim
        · apply congrArg Sum.inr
          apply Subtype.ext
          funext i
          fin_cases i <;> rfl

private theorem card_u4PathIndex {V : Type*} [Fintype V] [DecidableEq V]
    [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card (U4PathIndex G) = u4OrientedPathCount G := by
  simp only [U4PathIndex, Fintype.card_sigma, Fintype.card_coe]
  unfold u4OrientedPathCount
  apply Finset.sum_congr rfl
  intro u _hu
  exact Finset.sum_attach (G.neighborFinset u)
    (fun v ↦ (u4LocalPaths G u v).card)

private theorem u4PathCount_eq_card_path3 {V : Type*} [Fintype V]
    [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    u4PathCount G = Fintype.card (Path3 G) := by
  have hcard := Fintype.card_congr (u4PathIndexEquivPath3Sum G)
  rw [card_u4PathIndex G] at hcard
  simp only [Fintype.card_sum] at hcard
  unfold u4PathCount
  rw [hcard]
  norm_num

private theorem card_endpointPair_twice_le {V : Type*} [Fintype V] [LinearOrder V] :
    2 * Fintype.card (EndpointPair V) ≤ Fintype.card V ^ 2 := by
  let f : EndpointPair V ⊕ EndpointPair V → V × V
    | Sum.inl z => z.1
    | Sum.inr z => (z.1.2, z.1.1)
  have hf : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            congr 1
            exact Subtype.ext hxy
        | inr y =>
            exfalso
            have h1 : x.1.1 = y.1.2 := congrArg Prod.fst hxy
            have h2 : x.1.2 = y.1.1 := congrArg Prod.snd hxy
            exact (lt_asymm x.2 (by simpa [h1, h2] using y.2))
    | inr x =>
        cases y with
        | inl y =>
            exfalso
            have h1 : x.1.2 = y.1.1 := congrArg Prod.fst hxy
            have h2 : x.1.1 = y.1.2 := congrArg Prod.snd hxy
            exact (lt_asymm x.2 (by simpa [h1, h2] using y.2))
        | inr y =>
            congr 1
            apply Subtype.ext
            exact Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_sum, Fintype.card_prod, two_mul, pow_two] using hcard

private noncomputable def path3SigmaEquiv
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Path3 G ≃ Σ pi : EndpointPair V, pathFiber G pi where
  toFun p := ⟨p.endpoints, ⟨p, by simp⟩⟩
  invFun z := z.2.1
  left_inv p := rfl
  right_inv z := by
    rcases z with ⟨pi, ⟨p, hp⟩⟩
    have hpi : p.endpoints = pi := (mem_pathFiber G).1 hp
    cases hpi
    rfl

private theorem card_path3_eq_sum_multiplicity
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card (Path3 G) = ∑ pi, pathMultiplicity G pi := by
  calc
    Fintype.card (Path3 G) =
        Fintype.card (Σ pi : EndpointPair V, pathFiber G pi) :=
      Fintype.card_congr (path3SigmaEquiv G)
    _ = ∑ pi : EndpointPair V, (pathFiber G pi).card := by
      simp only [Fintype.card_sigma, Fintype.card_coe]
    _ = ∑ pi, pathMultiplicity G pi := by
      rfl

private theorem card_path3_le_sq_add_exceptional
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card (Path3 G) ≤
      Fintype.card V ^ 2 +
        ∑ pi ∈ generalExceptionalPairs G, pathMultiplicity G pi := by
  classical
  letI : DecidableEq V := Classical.typeDecidableEq V
  let E := generalExceptionalPairs G
  have hsmall : ∀ pi ∈ (Finset.univ : Finset (EndpointPair V)) \ E,
      pathMultiplicity G pi ≤ 2 := by
    intro pi hpi
    have hn : pi ∉ ordinaryExceptionalPairs G := by
      intro h
      exact (Finset.mem_sdiff.mp hpi).2 (Finset.mem_union_left _ h)
    simp only [ordinaryExceptionalPairs, Finset.mem_filter, Finset.mem_univ,
      true_and, not_or] at hn
    omega
  have hrest :
      ∑ pi ∈ (Finset.univ : Finset (EndpointPair V)) \ E,
          pathMultiplicity G pi ≤ Fintype.card V ^ 2 := by
    calc
      ∑ pi ∈ (Finset.univ : Finset (EndpointPair V)) \ E,
          pathMultiplicity G pi ≤
          ∑ _pi ∈ (Finset.univ : Finset (EndpointPair V)) \ E, 2 := by
            exact Finset.sum_le_sum hsmall
      _ = 2 * ((Finset.univ : Finset (EndpointPair V)) \ E).card := by
        have hsum := Finset.sum_const_nat
          (s := (Finset.univ : Finset (EndpointPair V)) \ E)
          (m := 2) (f := fun _pi : EndpointPair V ↦ 2) (by simp)
        simpa [Nat.mul_comm] using hsum
      _ ≤ 2 * Fintype.card (EndpointPair V) := by
        exact Nat.mul_le_mul_left 2 (Finset.card_le_univ _)
      _ ≤ Fintype.card V ^ 2 := card_endpointPair_twice_le
  rw [card_path3_eq_sum_multiplicity G]
  have hsplit :
      ∑ pi : EndpointPair V, pathMultiplicity G pi =
        (∑ pi ∈ E, pathMultiplicity G pi) +
          ∑ pi ∈ (Finset.univ : Finset (EndpointPair V)) \ E,
            pathMultiplicity G pi := by
    have h := Finset.sum_sdiff (f := pathMultiplicity G)
      (Finset.subset_univ E)
    simpa [add_comm] using h.symm
  rw [hsplit]
  calc
    (∑ pi ∈ E, pathMultiplicity G pi) +
          ∑ pi ∈ (Finset.univ : Finset (EndpointPair V)) \ E,
            pathMultiplicity G pi ≤
        (∑ pi ∈ E, pathMultiplicity G pi) + Fintype.card V ^ 2 :=
      Nat.add_le_add_left hrest _
    _ = Fintype.card V ^ 2 +
        ∑ pi ∈ E, pathMultiplicity G pi := Nat.add_comm _ _

private theorem u4PathCount_le_sq_add_thirtyfive
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hC6 : WalkC6Free G) :
    u4PathCount G ≤ (Fintype.card V : ℝ) ^ 2 +
      35 * (G.maxDegree : ℝ) * G.edgeFinset.card := by
  have hcard := card_path3_le_sq_add_exceptional G
  have hexceptional := fnvU8Direct G hC6
  unfold multiplicitySum at hexceptional
  rw [u4PathCount_eq_card_path3 G]
  have hnat := hcard.trans (Nat.add_le_add_left hexceptional _)
  exact_mod_cast hnat

/-! ## Least-counterexample setup -/

private theorem exists_minimal_weak_counterexample
    (hfail : ¬ ∀ n : ℕ,
      (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 6) : ℝ) ≤
        weakThreshold n) :
    ∃ n : ℕ,
      weakThreshold n <
          (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 6) : ℝ) ∧
        ∀ m < n,
          (SimpleGraph.extremalNumber m (SimpleGraph.cycleGraph 6) : ℝ) ≤
            weakThreshold m := by
  push_neg at hfail
  let n := Nat.find hfail
  refine ⟨n, Nat.find_spec hfail, ?_⟩
  intro m hm
  exact le_of_not_gt fun hbad ↦ Nat.find_min hfail hm hbad

/-! ## Scalar contradiction -/

/-- The numerical inequality at the end of the coarse U3--U4--U8 argument.
Writing `t=n^(1/3)`, U4--U8 gives the first displayed hypothesis; U3 gives
the second.  The assumed edge lower bound makes them inconsistent. -/
private theorem no_weak_scalar_counterexample
    {n e Delta t : ℝ}
    (hn : 0 < n) (ht : 0 < t) (ht3 : t ^ 3 = n)
    (he : n * ((63 / 100 : ℝ) * t + 10000) < e)
    (hDelta : Delta ≤ 200 * t)
    (hpaths : 4 * e ^ 3 / n ^ 2 ≤ n ^ 2 + 38 * Delta * e) : False := by
  have hfactor : 0 < (63 / 100 : ℝ) * t + 10000 := by positivity
  have he0 : 0 < e := (mul_pos hn hfactor).trans he
  have hratio : (63 / 100 : ℝ) * t + 10000 < e / n := by
    exact (lt_div_iff₀ hn).2 (by nlinarith)
  have hmain : 4 * (e / n) ^ 2 ≤ n ^ 2 / e + 38 * Delta := by
    calc
      4 * (e / n) ^ 2 = (4 * e ^ 3 / n ^ 2) / e := by field_simp
      _ ≤ (n ^ 2 + 38 * Delta * e) / e :=
        div_le_div_of_nonneg_right hpaths he0.le
      _ = n ^ 2 / e + 38 * Delta := by field_simp
  have hleft :
      4 * ((63 / 100 : ℝ) * t + 10000) ^ 2 < 4 * (e / n) ^ 2 := by
    have hbase : 0 ≤ (63 / 100 : ℝ) * t + 10000 := by positivity
    nlinarith [sq_nonneg (e / n - ((63 / 100 : ℝ) * t + 10000))]
  have hcoarse : (63 / 100 : ℝ) * t * n < e := by
    nlinarith
  have hright : n ^ 2 / e < (100 / 63 : ℝ) * t ^ 2 := by
    apply (div_lt_iff₀ he0).2
    have hmul := mul_lt_mul_of_pos_left hcoarse (show 0 < (100 / 63 : ℝ) * t ^ 2 by positivity)
    rw [← ht3] at hmul ⊢
    nlinarith
  have hDelta' : 38 * Delta ≤ 7600 * t := by nlinarith
  have hfinal :
      4 * ((63 / 100 : ℝ) * t + 10000) ^ 2 <
        (100 / 63 : ℝ) * t ^ 2 + 7600 * t := by
    linarith
  nlinarith [sq_nonneg t]

/-! ## The all-orders estimate with a linear error -/

private theorem extremalNumber_cycleGraph_six_le_weakThreshold (n : ℕ) :
    (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 6) : ℝ) ≤
      weakThreshold n := by
  by_contra hthis
  have hglobal : ¬ ∀ m : ℕ,
      (SimpleGraph.extremalNumber m (SimpleGraph.cycleGraph 6) : ℝ) ≤
        weakThreshold m := by
    intro h
    exact hthis (h n)
  obtain ⟨m, hmfail, hmmin⟩ := exists_minimal_weak_counterexample hglobal
  have hm : 0 < m := by
    by_contra hm0
    have : m = 0 := Nat.eq_zero_of_not_pos hm0
    subst m
    have hex0 : SimpleGraph.extremalNumber 0 (SimpleGraph.cycleGraph 6) = 0 := by
      have hle : SimpleGraph.extremalNumber 0 (SimpleGraph.cycleGraph 6) ≤ 0 := by
        rw [← Fintype.card_fin 0, SimpleGraph.extremalNumber_le_iff]
        intro G _inst _hfree
        have hbot : G = ⊥ := Subsingleton.elim _ _
        simp [hbot]
      omega
    simp [weakThreshold, hex0] at hmfail
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let t : ℝ := (m : ℝ) ^ (1 / 3 : ℝ)
  have hmℝ : 0 < (m : ℝ) := by exact_mod_cast hm
  have ht : 0 < t := by positivity
  have ht3 : t ^ 3 = (m : ℝ) := by
    simpa [t] using nat_rpow_one_third_cube hm
  have hpow : (m : ℝ) ^ (4 / 3 : ℝ) = (m : ℝ) * t := by
    simpa [t] using nat_rpow_four_thirds_eq hm

  obtain ⟨G, inst, hGext⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists
      ((SimpleGraph.cycleGraph 6).Free : SimpleGraph (Fin m) → Prop)).2
      ⟨⊥, SimpleGraph.free_bot (by
        intro hbot
        have hadj : (SimpleGraph.cycleGraph 6).Adj 0 1 := by decide
        rw [hbot] at hadj
        exact hadj)⟩
  letI : DecidableRel G.Adj := inst
  have hfree : (SimpleGraph.cycleGraph 6).Free G := hGext.prop
  have hedgeNat : G.edgeFinset.card =
      SimpleGraph.extremalNumber m (SimpleGraph.cycleGraph 6) := by
    simpa using SimpleGraph.card_edgeFinset_of_isExtremal_free hGext
  let e : ℝ := G.edgeFinset.card
  have he : weakThreshold m < e := by simpa [e, hedgeNat] using hmfail
  have heExpanded :
      (m : ℝ) * ((63 / 100 : ℝ) * t + 10000) < e := by
    rw [weakThreshold, weakLeading, weakLinear, hpow] at he
    nlinarith

  have hdegree : ∀ v : Fin m,
      weakThreshold m - weakThreshold (m - 1) < (G.degree v : ℝ) := by
    intro v
    have hdelNat := G.card_edgeFinset_deleteIncidenceSet_le_extremalNumber hfree v
    have hprev := hmmin (m - 1) (by omega)
    have hdel : ((G.deleteIncidenceSet v).edgeFinset.card : ℝ) ≤
        weakThreshold (m - 1) := by
      have hdel' : ((G.deleteIncidenceSet v).edgeFinset.card : ℝ) ≤
          (SimpleGraph.extremalNumber (m - 1)
            (SimpleGraph.cycleGraph 6) : ℝ) := by
        have hdelNat' : (G.deleteIncidenceSet v).edgeFinset.card ≤
            SimpleGraph.extremalNumber (m - 1) (SimpleGraph.cycleGraph 6) := by
          simpa using hdelNat
        exact_mod_cast hdelNat'
      exact hdel'.trans hprev
    have hdeg_le : G.degree v ≤ G.edgeFinset.card := by
      rw [← G.card_incidenceFinset_eq_degree]
      exact Finset.card_le_card (G.incidenceFinset_subset v)
    have hdelete : ((G.deleteIncidenceSet v).edgeFinset.card : ℝ) =
        e - G.degree v := by
      rw [G.card_edgeFinset_deleteIncidenceSet, Nat.cast_sub hdeg_le]
    rw [hdelete] at hdel
    linarith
  obtain ⟨vmin, hvmin⟩ := G.exists_minimal_degree_vertex
  have hstep := weakThreshold_step_lower hm
  have hmindtStrong :
      (63 / 100 : ℝ) * (t - 1) + 10000 < G.minDegree := by
    have hv := hdegree vmin
    rw [← hvmin] at hv
    norm_num [weakLinear] at hstep
    nlinarith
  have hmindt : (63 / 100 : ℝ) * t < G.minDegree := by
    nlinarith
  have hmin4 : 4 ≤ G.minDegree := by
    have ht0 : 0 ≤ t := ht.le
    exact_mod_cast (show (4 : ℝ) ≤ G.minDegree by nlinarith)

  have hcompNat := degree_comparison_direct G hfree
  have hcomp : (G.maxDegree : ℝ) * ((G.minDegree - 4 : ℕ) : ℝ) ^ 2 ≤
      64 * (m : ℝ) := by
    have hcompNat' : G.maxDegree * (G.minDegree - 4) ^ 2 ≤ 64 * m := by
      simpa using hcompNat
    exact_mod_cast hcompNat'
  have hsub : ((G.minDegree - 4 : ℕ) : ℝ) = (G.minDegree : ℝ) - 4 := by
    rw [Nat.cast_sub hmin4]
    norm_num
  have hdt : (63 / 100 : ℝ) * t < ((G.minDegree - 4 : ℕ) : ℝ) := by
    rw [hsub]
    nlinarith [hmindtStrong]
  have hsq : ((63 / 100 : ℝ) * t) ^ 2 ≤
      (((G.minDegree - 4 : ℕ) : ℝ)) ^ 2 := by
    have hleft : 0 ≤ (63 / 100 : ℝ) * t := by positivity
    nlinarith [sq_nonneg
      (((G.minDegree - 4 : ℕ) : ℝ) - (63 / 100 : ℝ) * t)]
  have hcomp' : (G.maxDegree : ℝ) * ((63 / 100 : ℝ) * t) ^ 2 ≤
      64 * (m : ℝ) := by
    calc
      (G.maxDegree : ℝ) * ((63 / 100 : ℝ) * t) ^ 2 ≤
          (G.maxDegree : ℝ) * (((G.minDegree - 4 : ℕ) : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ _ := hcomp
  have hDelta : (G.maxDegree : ℝ) ≤ 200 * t := by
    by_contra hnot
    have hgt : 200 * t < (G.maxDegree : ℝ) := lt_of_not_ge hnot
    have hpos : 0 < ((63 / 100 : ℝ) * t) ^ 2 := by positivity
    have hmul := mul_lt_mul_of_pos_right hgt hpos
    rw [← ht3] at hcomp'
    nlinarith [sq_pos_of_pos ht]

  have hwalk : WalkC6Free G := walkC6Free_of_free G hfree
  have hu4 := fnv_u4_general G
  have hu8 := u4PathCount_le_sq_add_thirtyfive G hwalk
  have hu4' : 4 * e ^ 3 / (m : ℝ) ^ 2 -
      3 * (G.maxDegree : ℝ) * e ≤ u4PathCount G := by
    simpa [e] using hu4
  have hu8' : u4PathCount G ≤
      (m : ℝ) ^ 2 + 35 * (G.maxDegree : ℝ) * e := by
    simpa [e] using hu8
  have hpaths : 4 * e ^ 3 / (m : ℝ) ^ 2 ≤
      (m : ℝ) ^ 2 + 38 * (G.maxDegree : ℝ) * e := by
    linarith
  exact no_weak_scalar_counterexample hmℝ ht ht3 heExpanded hDelta hpaths

/-! ## Absorbing the linear error at an explicit threshold -/

/-- A concrete finite version of the coarse upper bound.  The intentionally
large threshold keeps the final absorption calculation entirely rational. -/
theorem extremalNumber_cycleGraph_six_lt_sixteen_twentyfifths_of_ge
    {n : ℕ} (hn : 1000001 ^ 3 ≤ n) :
    (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 6) : ℝ) <
      (16 / 25 : ℝ) * (n : ℝ) ^ (4 / 3 : ℝ) := by
  have hnpos : 0 < n := by omega
  have hbase : (0 : ℝ) ≤ (1000001 : ℝ) ^ 3 := by positivity
  have hcast : ((1000001 : ℝ) ^ 3) ≤ (n : ℝ) := by exact_mod_cast hn
  have hrootMono :=
    Real.rpow_le_rpow hbase hcast (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hleft : (((1000001 : ℝ) ^ 3) ^ (1 / 3 : ℝ)) = 1000001 := by
    rw [← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1000001)]
    norm_num
  rw [hleft] at hrootMono
  have hnroot : (1000000 : ℝ) < (n : ℝ) ^ (1 / 3 : ℝ) := by
    linarith
  have hpow := nat_rpow_four_thirds_eq hnpos
  have hthreshold : weakThreshold n <
      (16 / 25 : ℝ) * (n : ℝ) ^ (4 / 3 : ℝ) := by
    unfold weakThreshold weakLeading weakLinear
    rw [hpow]
    nlinarith
  exact (extremalNumber_cycleGraph_six_le_weakThreshold n).trans_lt hthreshold

/-- The unconditional coarse FNV upper bound used by the four-fold
Morris--Saxton construction. -/
theorem eventually_extremalNumber_cycleGraph_six_lt_sixteen_twentyfifths :
    ∀ᶠ n : ℕ in Filter.atTop,
      (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 6) : ℝ) <
        (16 / 25 : ℝ) * (n : ℝ) ^ (4 / 3 : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (1000001 ^ 3)] with n hn
  exact extremalNumber_cycleGraph_six_lt_sixteen_twentyfifths_of_ge hn

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59/MorrisSaxtonFinal.lean` -/

section
/-!
# The Morris--Saxton counterexample for Erdős problem 59

This file combines the two quantitative Füredi--Naor--Verstraëte estimates
with the four-fold matching blowup.  The constant is made completely
explicit: `c = 1 / 100`.
-/

open SimpleGraph

private theorem matching_power_as_rpow (e : ℕ) :
    (209 ^ e : ℝ) = Real.rpow 2 (Real.logb 2 209 * (e : ℝ)) := by
  change (209 ^ e : ℝ) = (2 : ℝ) ^ (Real.logb 2 209 * (e : ℝ))
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1) (by norm_num : (0 : ℝ) < 209)]
  rw [Real.rpow_natCast]

/-- The counting conclusion of Morris--Saxton, separated from the
graph-theoretic proof of the eventual FNV upper estimate. -/
private theorem morrisSaxtonArbitrarilyLarge_of_eventual_extremal_upper
    (hupper : ∀ᶠ n : ℕ in Filter.atTop,
      (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 6) : ℝ) <
        (16 / 25 : ℝ) * (n : ℝ) ^ (4 / 3 : ℝ)) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      Real.rpow 2
          ((1 + (1 / 100 : ℝ)) *
            (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 6) : ℝ)) ≤
        (labelledFreeGraphCount (SimpleGraph.cycleGraph 6) n : ℝ) := by
  obtain ⟨Nupper, hNupper⟩ := Filter.eventually_atTop.mp hupper
  intro N
  obtain ⟨a, B, hm, htriangle, hC6, hedges⟩ :=
    LowerConstruction.infinitely_often (max (N + 1) Nupper)
  letI : DecidableRel B.Adj := Classical.decRel _
  let m := fnvVertices a
  have hm_lower : max (N + 1) Nupper ≤ m := by simpa [m] using hm
  have hm_pos_nat : 0 < m := by omega
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm_pos_nat
  have hmpow_pos : (0 : ℝ) < (m : ℝ) ^ (4 / 3 : ℝ) :=
    Real.rpow_pos_of_pos hm_pos _
  have hn_upper : Nupper ≤ 4 * m := by omega
  have hex_upper := hNupper (4 * m) hn_upper
  have hfour_mul :
      ((4 * m : ℕ) : ℝ) ^ (4 / 3 : ℝ) =
        (4 : ℝ) ^ (4 / 3 : ℝ) * (m : ℝ) ^ (4 / 3 : ℝ) := by
    rw [Nat.cast_mul, Real.mul_rpow (by norm_num) (Nat.cast_nonneg m)]
    norm_num
  have hedges' :
      (2669 / 5000 : ℝ) * (m : ℝ) ^ (4 / 3 : ℝ) <
        (B.edgeFinset.card : ℝ) := by
    simpa [m] using hedges
  have hlog_pos : (0 : ℝ) < Real.logb 2 209 :=
    Real.logb_pos (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (1 : ℝ) < 209)
  have hconstant := numerical_four_certificate
  have hscaled := mul_lt_mul_of_pos_right hconstant hmpow_pos
  have hscaled' :
      ((1 + (1 / 100 : ℝ)) * (16 / 25 : ℝ) *
          (4 : ℝ) ^ (4 / 3 : ℝ)) *
        (m : ℝ) ^ (4 / 3 : ℝ) <
      ((2669 / 5000 : ℝ) * Real.logb 2 209) *
        (m : ℝ) ^ (4 / 3 : ℝ) := by
    simpa only [show (1 + (1 / 100 : ℝ)) = 101 / 100 by norm_num]
      using hscaled
  have hexponent :
      (1 + (1 / 100 : ℝ)) *
          (SimpleGraph.extremalNumber (4 * m)
            (SimpleGraph.cycleGraph 6) : ℝ) <
        Real.logb 2 209 * (B.edgeFinset.card : ℝ) := by
    rw [hfour_mul] at hex_upper
    have hupper_scaled := mul_lt_mul_of_pos_left hex_upper
      (by norm_num : (0 : ℝ) < 1 + 1 / 100)
    have hedge_scaled := mul_lt_mul_of_pos_left hedges' hlog_pos
    calc
      (1 + (1 / 100 : ℝ)) *
          (SimpleGraph.extremalNumber (4 * m)
            (SimpleGraph.cycleGraph 6) : ℝ) <
          (1 + (1 / 100 : ℝ)) *
            ((16 / 25 : ℝ) *
              ((4 : ℝ) ^ (4 / 3 : ℝ) *
                (m : ℝ) ^ (4 / 3 : ℝ))) := hupper_scaled
      _ = ((1 + (1 / 100 : ℝ)) * (16 / 25 : ℝ) *
            (4 : ℝ) ^ (4 / 3 : ℝ)) *
          (m : ℝ) ^ (4 / 3 : ℝ) := by ring
      _ < ((2669 / 5000 : ℝ) * Real.logb 2 209) *
          (m : ℝ) ^ (4 / 3 : ℝ) := hscaled'
      _ = Real.logb 2 209 *
          ((2669 / 5000 : ℝ) * (m : ℝ) ^ (4 / 3 : ℝ)) := by ring
      _ < Real.logb 2 209 * (B.edgeFinset.card : ℝ) := hedge_scaled
  have hcountNat := matchingBlowupFour_labelledFreeGraphCount_lower_bound B
    htriangle hC6
  have hcountReal :
      (209 ^ B.edgeFinset.card : ℝ) ≤
        (labelledFreeGraphCount (SimpleGraph.cycleGraph 6) (4 * m) : ℝ) := by
    exact_mod_cast hcountNat
  refine ⟨4 * m, by omega, ?_⟩
  calc
    Real.rpow 2
        ((1 + (1 / 100 : ℝ)) *
          (SimpleGraph.extremalNumber (4 * m)
            (SimpleGraph.cycleGraph 6) : ℝ))
        ≤ Real.rpow 2
            (Real.logb 2 209 * (B.edgeFinset.card : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent.le
    _ = (209 ^ B.edgeFinset.card : ℝ) :=
      (matching_power_as_rpow B.edgeFinset.card).symm
    _ ≤ (labelledFreeGraphCount (SimpleGraph.cycleGraph 6) (4 * m) : ℝ) :=
      hcountReal

/-- The explicit infinite subsequence on which the Morris--Saxton
improvement holds. -/
theorem morrisSaxtonLowerBoundIndices_cycleGraph_six :
    (lowerBoundIndices (SimpleGraph.cycleGraph 6) (1 / 100)).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hn, hbound⟩ :=
    morrisSaxtonArbitrarilyLarge_of_eventual_extremal_upper
      eventually_extremalNumber_cycleGraph_six_lt_sixteen_twentyfifths (N + 1)
  exact ⟨n, hbound, by omega⟩

/-- The quantitative Morris--Saxton lower bound, witnessed explicitly by
`c = 1 / 100`. -/
theorem hasMorrisSaxtonLowerBound_cycleGraph_six :
    HasMorrisSaxtonLowerBound (SimpleGraph.cycleGraph 6) :=
  ⟨1 / 100, by norm_num, morrisSaxtonLowerBoundIndices_cycleGraph_six⟩

/-- Consequently the proposed `2 ^ ((1 + o(1)) ex(n,C₆))` upper bound is
false. -/
theorem morrisSaxtonDisprovesErdos59 :
    ¬ HasErdos59UpperBound (SimpleGraph.cycleGraph 6) :=
  hasMorrisSaxtonLowerBound_not_hasErdos59UpperBound
    hasMorrisSaxtonLowerBound_cycleGraph_six
    eventuallyPositiveExtremalNumber_cycleGraph_six

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos59.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 59.
https://www.erdosproblems.com/forum/thread/59

Informal authors:
- Paul Erdős
- Péter Frankl
- Vojtěch Rödl
- Robert Morris
- David Saxton
- Zoltán Füredi
- Assaf Naor
- Jacques Verstraëte

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos59.md
-/
/-
This is a Lean formalization of the negative resolution of Erdős Problem 59.
https://www.erdosproblems.com/59

Informal authors:
- Erdős, Frankl, and Rödl (the non-bipartite positive case)
- Morris and Saxton (the C₆ counterexample)
- Füredi, Naor, and Verstraëte (the extremal graph inputs)

Formal author:
- OpenAI Codex
-/

/-- The established negative resolution of Erdős Problem 59.

For the six-cycle there is an explicit constant `c = 1 / 100 > 0` and
infinitely many orders on which the number of labelled `C₆`-free graphs is
at least `2 ^ ((1 + c) * ex(n,C₆))`.  Consequently the proposed
`2 ^ ((1 + o(1)) * ex(n,C₆))` upper bound is false in general. -/
theorem erdos_59 :
    HasMorrisSaxtonLowerBound (SimpleGraph.cycleGraph 6) ∧
      ¬ HasErdos59UpperBound (SimpleGraph.cycleGraph 6) :=
  ⟨hasMorrisSaxtonLowerBound_cycleGraph_six,
    morrisSaxtonDisprovesErdos59⟩

end

#print axioms erdos_59
-- 'Erdos59.erdos_59' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos59
