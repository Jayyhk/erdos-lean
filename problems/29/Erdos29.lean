import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos29

/-
# Problem Description

Erdős Problem 29 ($100), asked of Erdős by Sidon in 1932. Is there an *explicit*
construction of a set `A ⊆ ℕ` with `A + A = ℕ` but `1_A ∗ 1_A (n) = o(n ^ ε)` for every
`ε > 0`? `erdos_29` proves that there is. An explicit construction was given by Jain, Pham,
Sawhney and Zakharov.

`addRepCount A n` is the ordered representation count `#{(a, b) : a + b = n, a ∈ A, b ∈ A}`,
which is `1_A ∗ 1_A (n)`, and `A + A = Set.univ` is `A + A = ℕ`.

A caveat on faithfulness. Erdős had already proved *existence* probabilistically; the point
of this problem is constructivity, and "explicit" is not expressible as a Lean proposition.
So the `∃ A` statement of `erdos_29` is, on its own, weaker than the question asked. The
constructive content lives in the witness: `erdos_29` is discharged by
`exists_solvesErdos29`, whose witness is `explicitBasis = MixedRadix.basis explicitSystem`,
a concrete mixed-radix set with no probabilistic step. The named-witness form is available
directly above as `explicitBasis_solves : SolvesErdos29 explicitBasis`.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos29/AllowedNonsquare.lean` -/

section
/-!
# An allowed nonsquare for the local construction in Erdős Problem 29

For an odd prime `p` we search the canonical representatives `0, …, p - 1`.
The predicate used by the search is a genuinely finite computation: a residue is
declared square precisely when it occurs among the `p` explicitly enumerated
squares.  For `p ≥ 11`, four distinct square multiples of any nonsquare show
that at least one nonsquare avoids the three exceptional values needed below.
-/



/-- The natural representatives of all squares modulo `p`. -/
def squareResidues (p : ℕ) : Finset ℕ :=
  (Finset.range p).image fun x ↦ x * x % p

/-- The finite collection searched for the distinguished nonsquare. -/
def allowedCandidates (p : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun n ↦
    n ∉ squareResidues p ∧
      (n : ZMod p) ≠ -1 ∧
      (n : ZMod p) ≠ -3 ∧
      (n : ZMod p) ≠ -((3 : ZMod p)⁻¹)

/-- A bounded, executable search for the first allowed nonsquare, with a harmless
default value in the parameter ranges where no candidate exists. -/
def allowedT (p : ℕ) : ℕ :=
  (allowedCandidates p).min.untopD 0

lemma mem_squareResidues_iff_isSquare {p n : ℕ} (hp : 0 < p) (hn : n < p) :
    n ∈ squareResidues p ↔ IsSquare (n : ZMod p) := by
  letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
  constructor
  · intro h
    rw [isSquare_iff_exists_mul_self]
    simp only [squareResidues, Finset.mem_image] at h
    obtain ⟨x, hx, hxn⟩ := h
    have hxp : x < p := Finset.mem_range.mp hx
    refine ⟨(x : ZMod p), ?_⟩
    apply ZMod.val_injective
    rw [ZMod.val_natCast_of_lt hn, ZMod.val_mul, ZMod.val_natCast_of_lt hxp]
    exact hxn.symm
  · intro h
    rw [isSquare_iff_exists_mul_self] at h
    obtain ⟨x, hx⟩ := h
    simp only [squareResidues, Finset.mem_image]
    refine ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ?_⟩
    have hv := congrArg ZMod.val hx
    rw [ZMod.val_natCast_of_lt hn, ZMod.val_mul] at hv
    exact hv.symm

private lemma exists_allowed_residue {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    ∃ t : ZMod p,
      ¬ IsSquare t ∧ t ≠ -1 ∧ t ≠ -3 ∧ t ≠ -((3 : ZMod p)⁻¹) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := lt_of_lt_of_le (by omega) hp11
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  obtain ⟨q, hq⟩ := FiniteField.exists_nonsquare (F := ZMod p) hchar
  have hq0 : q ≠ 0 := by
    intro h
    apply hq
    rw [h]
    exact IsSquare.zero
  have hqChar : quadraticChar (ZMod p) q = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hq
  let S : Finset (ZMod p) :=
    (Finset.Icc 1 4 : Finset ℕ).image fun r : ℕ ↦ (r : ZMod p) ^ 2 * q
  have hInjective : Set.InjOn (fun r : ℕ ↦ (r : ZMod p) ^ 2 * q)
      (Finset.Icc 1 4 : Finset ℕ) := by
    intro r hr s hs hrs
    simp only [Finset.coe_Icc, Set.mem_Icc] at hr hs
    have hrp : r < p := by omega
    have hsp : s < p := by omega
    have hsquares : (r : ZMod p) ^ 2 = (s : ZMod p) ^ 2 :=
      mul_right_cancel₀ hq0 hrs
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with heq | hneg
    · have hv := congrArg ZMod.val heq
      simpa [ZMod.val_natCast_of_lt hrp, ZMod.val_natCast_of_lt hsp] using hv
    · exfalso
      have hzero : ((r + s : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_add, hneg]
        simp
      have hdvd : p ∣ r + s := (CharP.cast_eq_zero_iff (ZMod p) p (r + s)).mp hzero
      exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdvd
  have hcardS : S.card = 4 := by
    rw [show S = (Finset.Icc 1 4 : Finset ℕ).image
        (fun r : ℕ ↦ (r : ZMod p) ^ 2 * q) from rfl]
    rw [Finset.card_image_iff.mpr hInjective, Nat.card_Icc]
  have hS_nonsquare : ∀ x ∈ S, ¬ IsSquare x := by
    intro x hx
    simp only [S, Finset.mem_image] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    have hrBounds := Finset.mem_Icc.mp hr
    have hrp : r < p := by omega
    have hr0 : (r : ZMod p) ≠ 0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      rw [ZMod.val_natCast_of_lt hrp, ZMod.val_zero] at hv
      omega
    apply quadraticChar_neg_one_iff_not_isSquare.mp
    rw [map_mul, quadraticChar_sq_one' hr0, hqChar, one_mul]
  let F : Finset (ZMod p) := {-1, -3, -((3 : ZMod p)⁻¹)}
  have hcardF : F.card ≤ 3 := by
    have h1 := Finset.card_insert_le (-1 : ZMod p) {-3, -((3 : ZMod p)⁻¹)}
    have h2 := Finset.card_insert_le (-3 : ZMod p) {-((3 : ZMod p)⁻¹)}
    simpa [F] using h1.trans (Nat.add_le_add_right h2 1)
  have hnsub : ¬ S ⊆ F := by
    intro hsub
    have hc := Finset.card_le_card hsub
    omega
  obtain ⟨t, htS, htF⟩ := Finset.not_subset.mp hnsub
  have htAvoid : t ≠ -1 ∧ t ≠ -3 ∧ t ≠ -((3 : ZMod p)⁻¹) := by
    simpa [F] using htF
  exact ⟨t, hS_nonsquare t htS, htAvoid⟩

private lemma allowedCandidates_nonempty {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (allowedCandidates p).Nonempty := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := lt_of_lt_of_le (by omega) hp11
  obtain ⟨t, htSquare, ht1, ht3, htInv3⟩ := exists_allowed_residue hp hp11
  refine ⟨t.val, ?_⟩
  simp only [allowedCandidates, Finset.mem_filter, Finset.mem_range]
  have htlt : t.val < p := ZMod.val_lt t
  refine ⟨htlt, ?_, ?_, ?_, ?_⟩
  · intro h
    apply htSquare
    simpa only [ZMod.natCast_zmod_val] using
      (mem_squareResidues_iff_isSquare hp0 htlt).mp h
  · simpa only [ZMod.natCast_zmod_val] using ht1
  · simpa only [ZMod.natCast_zmod_val] using ht3
  · simpa only [ZMod.natCast_zmod_val] using htInv3

lemma allowedT_mem_candidates {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    allowedT p ∈ allowedCandidates p := by
  have hne := allowedCandidates_nonempty hp hp11
  obtain ⟨a, ha⟩ := Finset.min_of_nonempty hne
  have hvalue : allowedT p = a := by
    simp only [allowedT, ha, WithTop.untopD_coe]
  rw [hvalue]
  exact Finset.mem_of_min ha

theorem allowedT_spec {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    allowedT p < p ∧
      ¬ IsSquare (allowedT p : ZMod p) ∧
      (allowedT p : ZMod p) ≠ -1 ∧
      (allowedT p : ZMod p) ≠ -3 ∧
      (allowedT p : ZMod p) ≠ -((3 : ZMod p)⁻¹) := by
  have hp0 : 0 < p := hp.pos
  have hm := allowedT_mem_candidates hp hp11
  simp only [allowedCandidates, Finset.mem_filter, Finset.mem_range] at hm
  refine ⟨hm.1, ?_, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2⟩
  exact fun hs ↦ hm.2.1 ((mem_squareResidues_iff_isSquare hp0 hm.1).mpr hs)

theorem allowedT_not_isSquare {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    ¬ IsSquare (allowedT p : ZMod p) :=
  (allowedT_spec hp hp11).2.1

theorem allowedT_ne_neg_one {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (allowedT p : ZMod p) ≠ -1 :=
  (allowedT_spec hp hp11).2.2.1

theorem allowedT_ne_neg_three {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (allowedT p : ZMod p) ≠ -3 :=
  (allowedT_spec hp hp11).2.2.2.1

theorem allowedT_ne_neg_inv_three {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (allowedT p : ZMod p) ≠ -((3 : ZMod p)⁻¹) :=
  (allowedT_spec hp hp11).2.2.2.2

/-- The three parabola coefficients attached to the allowed nonsquare. -/
def parabolaCoefficients (p : ℕ) : Finset (ZMod p) :=
  let t : ZMod p := allowedT p
  {2, 1 + t, 1 + t⁻¹}

private lemma allowedT_ne_zero {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (allowedT p : ZMod p) ≠ 0 := by
  intro h
  apply allowedT_not_isSquare hp hp11
  rw [h]
  exact IsSquare.zero

private lemma two_ne_zero {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (2 : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

private lemma four_ne_zero {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (4 : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  intro h
  have hdvd : p ∣ 4 := (CharP.cast_eq_zero_iff (ZMod p) p 4).mp h
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

private lemma allowedT_inv_ne_neg_one {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (allowedT p : ZMod p)⁻¹ ≠ -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  intro h
  apply allowedT_ne_neg_one hp hp11
  have hi := congrArg Inv.inv h
  simpa only [inv_inv, inv_neg, inv_one] using hi

private lemma allowedT_inv_ne_neg_three {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (allowedT p : ZMod p)⁻¹ ≠ -3 := by
  letI : Fact p.Prime := ⟨hp⟩
  intro h
  apply allowedT_ne_neg_inv_three hp hp11
  have hi := congrArg Inv.inv h
  simpa only [inv_inv, inv_neg] using hi

/-- Every ordered sum of two selected parabola coefficients is nonzero. -/
theorem parabolaCoefficients_add_ne_zero {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {c d : ZMod p} (hc : c ∈ parabolaCoefficients p) (hd : d ∈ parabolaCoefficients p) :
    c + d ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  let t : ZMod p := allowedT p
  have ht0 : t ≠ 0 := allowedT_ne_zero hp hp11
  have ht1 : t ≠ -1 := allowedT_ne_neg_one hp hp11
  have ht3 : t ≠ -3 := allowedT_ne_neg_three hp hp11
  have hti1 : t⁻¹ ≠ -1 := allowedT_inv_ne_neg_one hp hp11
  have hti3 : t⁻¹ ≠ -3 := allowedT_inv_ne_neg_three hp hp11
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero hp hp11
  have h4 : (4 : ZMod p) ≠ 0 := four_ne_zero hp hp11
  have hdouble (z : ZMod p) (hz : z ≠ -1) : (1 + z) + (1 + z) ≠ 0 := by
    intro h
    have hf : (2 : ZMod p) * (1 + z) = 0 := by
      calc
        (2 : ZMod p) * (1 + z) = (1 + z) + (1 + z) := by ring
        _ = 0 := h
    have := (mul_eq_zero.mp hf).resolve_left h2
    apply hz
    linear_combination this
  have hcross : (1 + t) + (1 + t⁻¹) ≠ 0 := by
    intro h
    have hsquare : (t + 1) ^ 2 = 0 := by
      calc
        (t + 1) ^ 2 = t * ((1 + t) + (1 + t⁻¹)) := by
          field_simp [ht0]
          <;> ring
        _ = 0 := by rw [h, mul_zero]
    have hz : t + 1 = 0 := (sq_eq_zero_iff).mp hsquare
    exact ht1 (eq_neg_of_add_eq_zero_left hz)
  simp only [parabolaCoefficients, Finset.mem_insert, Finset.mem_singleton] at hc hd
  rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl
  · convert h4 using 1 <;> ring
  · intro h; apply ht3; linear_combination h
  · intro h; apply hti3; linear_combination h
  · intro h; apply ht3; linear_combination h
  · exact hdouble t ht1
  · exact hcross
  · intro h; apply hti3; linear_combination h
  · simpa [add_comm] using hcross
  · exact hdouble t⁻¹ hti1

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos29/QuadraticFiber.lean` -/

section
/-!
# Quadratic fiber bounds

This file packages the elementary root-counting fact used in the modular
construction for Erdős Problem 29.  Its statements are deliberately phrased
using `Finset.univ.filter`, so that they can be applied directly to finite-field
representation counts.
-/

namespace QuadraticFiber

open Polynomial

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The finite set of roots of the displayed quadratic expression. -/
def quadraticRoots (a b c : K) : Finset K :=
  Finset.univ.filter fun x ↦ a * x ^ 2 + b * x + c = 0

/-- A genuinely quadratic polynomial over a finite field has at most two
distinct roots. -/
theorem quadraticRoots_card_le_two (a b c : K) (ha : a ≠ 0) :
    (quadraticRoots a b c).card ≤ 2 := by
  classical
  let P : K[X] := C a * X ^ 2 + C b * X + C c
  have hP : P ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun Q : K[X] ↦ Q.coeff 2) h
    simp [P, ha] at hcoeff
  have hsubset : (quadraticRoots a b c).val ⊆ P.roots := by
    intro x hx
    rw [Polynomial.mem_roots hP]
    have hx' : a * x ^ 2 + b * x + c = 0 :=
      (Finset.mem_filter.mp hx).2
    simpa [P] using hx'
  calc
    (quadraticRoots a b c).card ≤ P.natDegree :=
      Polynomial.card_le_degree_of_subset_roots hsubset
    _ = 2 := Polynomial.natDegree_quadratic ha

/-- The same quadratic root bound without the helper-definition wrapper. -/
theorem univ_filter_quadratic_card_le_two (a b c : K) (ha : a ≠ 0) :
    (Finset.univ.filter fun x : K ↦ a * x ^ 2 + b * x + c = 0).card ≤ 2 := by
  simpa only [quadraticRoots] using quadraticRoots_card_le_two a b c ha

/-- The subtype of solutions of a nondegenerate quadratic equation has at
most two elements. -/
theorem fintypeCard_quadratic_solution_le_two (a b c : K) (ha : a ≠ 0) :
    Fintype.card {x : K // a * x ^ 2 + b * x + c = 0} ≤ 2 := by
  classical
  rw [Fintype.card_subtype]
  exact univ_filter_quadratic_card_le_two a b c ha

/-- Ordered pairs lying simultaneously on a line `x + y = u` and on the
diagonal quadratic curve `c*x² + d*y² = v`. -/
def lineQuadraticFiber (c d u v : K) : Finset (K × K) :=
  Finset.univ.filter fun xy ↦
    xy.1 + xy.2 = u ∧ c * xy.1 ^ 2 + d * xy.2 ^ 2 = v

/-- If `c + d` is nonzero, a line meets the diagonal quadratic curve in at
most two ordered pairs. -/
theorem lineQuadraticFiber_card_le_two (c d u v : K) (hcd : c + d ≠ 0) :
    (lineQuadraticFiber c d u v).card ≤ 2 := by
  classical
  let T : Finset K := quadraticRoots (c + d) (-2 * d * u) (d * u ^ 2 - v)
  have hmaps : Set.MapsTo Prod.fst (lineQuadraticFiber c d u v : Set (K × K))
      (T : Set K) := by
    intro xy hxy
    have hxy' := (Finset.mem_filter.mp hxy).2
    have hsum : xy.1 + xy.2 = u := hxy'.1
    have hcurve : c * xy.1 ^ 2 + d * xy.2 ^ 2 = v := hxy'.2
    have hy : xy.2 = u - xy.1 := eq_sub_of_add_eq' hsum
    simp only [T, quadraticRoots, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [hy] at hcurve
    linear_combination hcurve
  have hinj : Set.InjOn Prod.fst (lineQuadraticFiber c d u v : Set (K × K)) := by
    intro xy hxy zw hzw hfst
    have hsumxy : xy.1 + xy.2 = u := ((Finset.mem_filter.mp hxy).2).1
    have hsumzw : zw.1 + zw.2 = u := ((Finset.mem_filter.mp hzw).2).1
    apply Prod.ext hfst
    rw [eq_sub_of_add_eq' hsumxy, eq_sub_of_add_eq' hsumzw, hfst]
  calc
    (lineQuadraticFiber c d u v).card ≤ T.card :=
      Finset.card_le_card_of_injOn Prod.fst hmaps hinj
    _ ≤ 2 := by
      simpa only [T] using
        quadraticRoots_card_le_two (c + d) (-2 * d * u) (d * u ^ 2 - v) hcd

/-- The pair-fiber estimate stated directly for an unwrapped filter. -/
theorem univ_filter_line_quadratic_card_le_two (c d u v : K) (hcd : c + d ≠ 0) :
    (Finset.univ.filter fun xy : K × K ↦
      xy.1 + xy.2 = u ∧ c * xy.1 ^ 2 + d * xy.2 ^ 2 = v).card ≤ 2 := by
  simpa only [lineQuadraticFiber] using lineQuadraticFiber_card_le_two c d u v hcd

/-- The subtype form of the line--quadratic fiber estimate. -/
theorem fintypeCard_line_quadratic_solution_le_two (c d u v : K) (hcd : c + d ≠ 0) :
    Fintype.card {xy : K × K //
      xy.1 + xy.2 = u ∧ c * xy.1 ^ 2 + d * xy.2 ^ 2 = v} ≤ 2 := by
  classical
  rw [Fintype.card_subtype]
  exact univ_filter_line_quadratic_card_le_two c d u v hcd

end QuadraticFiber

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos29/ModularLift.lean` -/

section
/-!
# The uniform `p^2` modular lift for Erdős Problem 29

This file separates the elementary lifting and counting argument from the
particular choice of three parabolas.  A `CoefficientSystem p` records three
coefficients over `ZMod p`, a cover of every point of the affine plane by a
sum of two of their parabolas, and the nonvanishing of every ordered sum of
two coefficients.

The lifted tagged atom is

`x + p * val (c * x^2 + s)  (mod p^2)`,

where `s` is either `-1` or `0`.  The negative shift removes the carry in the
standard representatives of two low coordinates.  Thus every residue modulo
`p^2` is covered.  The tagged representation count is at most
`(3 * 2)^2 * 2 * 2 = 144`: after fixing four tags and the low-coordinate
carry, the first low coordinate satisfies a genuine quadratic.
-/

namespace ModularLift

open scoped BigOperators

private abbrev F (p : ℕ) := ZMod p

/-- Abstract finite-field data required by the uniform lift. -/
structure CoefficientSystem (p : ℕ) where
  coeff : Fin 3 → F p
  cover : ∀ u v : F p, ∃ i j : Fin 3, ∃ x y : F p,
    x + y = u ∧ coeff i * x ^ 2 + coeff j * y ^ 2 = v
  coeff_add_ne_zero : ∀ i j : Fin 3, coeff i + coeff j ≠ 0

/-- The two carry-correcting high-coordinate shifts, `-1` and `0`. -/
def shift (p : ℕ) : Fin 2 → F p
  | i => if i = 0 then -1 else 0

@[simp] theorem shift_zero (p : ℕ) : shift p 0 = -1 := by simp [shift]
@[simp] theorem shift_one (p : ℕ) : shift p 1 = 0 := by simp [shift]

/-- A tagged lifted atom: coefficient tag, shift tag, and low coordinate. -/
abbrev Parameter (p : ℕ) := Fin 3 × Fin 2 × F p

/-- The high coordinate of a tagged lifted atom. -/
def high {p : ℕ} (S : CoefficientSystem p) (a : Parameter p) : F p :=
  S.coeff a.1 * a.2.2 ^ 2 + shift p a.2.1

/-- Encode a tagged atom as a residue modulo `p^2`, using standard
representatives in both coordinates. -/
def value {p : ℕ} (S : CoefficientSystem p) (a : Parameter p) : ZMod (p ^ 2) :=
  (a.2.2.val + p * (high S a).val : ℕ)

/-- The finite set of lifted residues. -/
def residueDigitSet {p : ℕ} [NeZero p]
    (S : CoefficientSystem p) : Finset (ZMod (p ^ 2)) :=
  Finset.univ.image (value S)

/-- Standard natural representatives of the lifted residues. -/
def digitSet {p : ℕ} [NeZero p] (S : CoefficientSystem p) : Finset ℕ :=
  (residueDigitSet S).image ZMod.val

@[simp] theorem value_mem_residueDigitSet {p : ℕ} [NeZero p]
    (S : CoefficientSystem p)
    (a : Parameter p) : value S a ∈ residueDigitSet S := by
  classical
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩

theorem value_val_mem_digitSet {p : ℕ} [NeZero p] (S : CoefficientSystem p)
    (a : Parameter p) : (value S a).val ∈ digitSet S := by
  classical
  exact Finset.mem_image.mpr ⟨value S a, value_mem_residueDigitSet S a, rfl⟩

theorem mem_digitSet_lt {p : ℕ} [NeZero p]
    (S : CoefficientSystem p) (hp0 : 0 < p)
    {d : ℕ} (hd : d ∈ digitSet S) : d < p ^ 2 := by
  classical
  rcases Finset.mem_image.mp hd with ⟨z, _hz, rfl⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp0)⟩
  exact z.val_lt

private theorem value_add_eq_of_carry {p : ℕ} (hp0 : 0 < p)
    (S : CoefficientSystem p) (a b : Parameter p) (u : ZMod (p ^ 2))
    (r h e : ℕ)
    (hlow : a.2.2.val + b.2.2.val = r + p * e)
    (hhigh : high S a + high S b + (e : F p) = (h : F p))
    (hu : u.val = r + p * h) :
    value S a + value S b = u := by
  haveI : NeZero p := ⟨Nat.ne_of_gt hp0⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp0)⟩
  have hm : (high S a).val + (high S b).val + e ≡ h [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hhigh
  have hm' := hm.mul_left' p
  have hm'' := Nat.ModEq.add_left r hm'
  rw [← u.natCast_zmod_val]
  change ((a.2.2.val + p * (high S a).val : ℕ) : ZMod (p ^ 2)) +
      (b.2.2.val + p * (high S b).val : ℕ) = (u.val : ZMod (p ^ 2))
  rw [← Nat.cast_add]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).2
  have hraw : a.2.2.val + p * (high S a).val +
      (b.2.2.val + p * (high S b).val) =
      r + p * ((high S a).val + (high S b).val + e) := by
    calc
      a.2.2.val + p * (high S a).val +
          (b.2.2.val + p * (high S b).val) =
          (a.2.2.val + b.2.2.val) +
            p * ((high S a).val + (high S b).val) := by ring
      _ = (r + p * e) + p * ((high S a).val + (high S b).val) := by rw [hlow]
      _ = r + p * ((high S a).val + (high S b).val + e) := by ring
  rw [hraw, hu]
  simpa only [pow_two] using hm''

/-- Every residue modulo `p^2` is the sum of two tagged lifted atoms. -/
theorem exists_value_add_eq {p : ℕ} (hp : p.Prime) (S : CoefficientSystem p)
    (u : ZMod (p ^ 2)) :
    ∃ a b : Parameter p, value S a + value S b = u := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let r := u.val % p
  let h := u.val / p
  have hr : r < p := Nat.mod_lt _ hp0
  have hu : u.val = r + p * h := by
    dsimp [r, h]
    exact (Nat.mod_add_div u.val p).symm
  rcases S.cover (r : F p) (h : F p) with ⟨i, j, x, y, hxy, hcurve⟩
  have haddval : (x + y).val = r := by
    rw [hxy]
    exact ZMod.val_natCast_of_lt hr
  by_cases hs : x.val + y.val < p
  · have hlow : x.val + y.val = r := by
      rw [← ZMod.val_add_of_lt hs, haddval]
    refine ⟨(i, 1, x), (j, 1, y),
      value_add_eq_of_carry hp0 S _ _ u r h 0 ?_ ?_ hu⟩
    · simpa using hlow
    · simp only [high, shift_one, add_zero, Nat.cast_zero]
      simpa using hcurve
  · have hlow : x.val + y.val = r + p := by
      calc
        x.val + y.val = (x + y).val + p :=
          ZMod.val_add_val_of_le (not_lt.mp hs)
        _ = r + p := by rw [haddval]
    refine ⟨(i, 0, x), (j, 1, y),
      value_add_eq_of_carry hp0 S _ _ u r h 1 ?_ ?_ hu⟩
    · simpa using hlow
    · simp only [high, shift_zero, shift_one, add_zero, Nat.cast_one]
      linear_combination hcurve

/-- The residue digit set is an additive basis of `ZMod (p^2)`. -/
theorem residueDigitSet_add_cover {p : ℕ} [NeZero p]
    (hp : p.Prime) (S : CoefficientSystem p)
    (u : ZMod (p ^ 2)) :
    ∃ a ∈ residueDigitSet S, ∃ b ∈ residueDigitSet S, a + b = u := by
  rcases exists_value_add_eq hp S u with ⟨a, b, hab⟩
  exact ⟨value S a, value_mem_residueDigitSet S a,
    value S b, value_mem_residueDigitSet S b, hab⟩

/-! ## Uniform tagged representation bound -/

/-- The carry of the two standard low-coordinate representatives. -/
def carry {p : ℕ} (a b : Parameter p) : Fin 2 :=
  if a.2.2.val + b.2.2.val < p then 0 else 1

@[simp] private theorem carry_eq_zero {p : ℕ} {a b : Parameter p}
    (h : a.2.2.val + b.2.2.val < p) : carry a b = 0 := by
  simp [carry, h]

@[simp] private theorem carry_eq_one {p : ℕ} {a b : Parameter p}
    (h : ¬ a.2.2.val + b.2.2.val < p) : carry a b = 1 := by
  simp [carry, h]

private theorem raw_modEq_of_value_add_eq {p : ℕ} (hp : p.Prime)
    (S : CoefficientSystem p) {a b : Parameter p} {u : ZMod (p ^ 2)}
    (hab : value S a + value S b = u) :
    a.2.2.val + p * (high S a).val +
        (b.2.2.val + p * (high S b).val) ≡ u.val [MOD p ^ 2] := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  calc
    ((a.2.2.val + p * (high S a).val +
        (b.2.2.val + p * (high S b).val) : ℕ) : ZMod (p ^ 2)) =
        value S a + value S b := by
          simp only [value, Nat.cast_add]
    _ = u := hab
    _ = (u.val : ZMod (p ^ 2)) := u.natCast_zmod_val.symm

private theorem low_equation_of_value_add_eq {p : ℕ} (hp : p.Prime)
    (S : CoefficientSystem p) {a b : Parameter p} {u : ZMod (p ^ 2)}
    (hab : value S a + value S b = u) :
    a.2.2 + b.2.2 = ((u.val % p : ℕ) : F p) := by
  letI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hm2 := raw_modEq_of_value_add_eq hp S hab
  have hm2' : a.2.2.val + p * (high S a).val +
      (b.2.2.val + p * (high S b).val) ≡ u.val [MOD p * p] := by
    simpa only [pow_two] using hm2
  have hm : a.2.2.val + p * (high S a).val +
      (b.2.2.val + p * (high S b).val) ≡ u.val [MOD p] :=
    hm2'.of_mul_left p
  have hz : ((a.2.2.val + p * (high S a).val +
      (b.2.2.val + p * (high S b).val) : ℕ) : F p) = (u.val : F p) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact hm
  simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul,
    add_zero, ZMod.natCast_zmod_val, ZMod.natCast_mod] using hz

private theorem low_val_add_eq {p : ℕ} (hp : p.Prime)
    (S : CoefficientSystem p) {a b : Parameter p} {u : ZMod (p ^ 2)}
    (hab : value S a + value S b = u) :
    a.2.2.val + b.2.2.val = u.val % p + p * (carry a b).val := by
  letI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hfield := low_equation_of_value_add_eq hp S hab
  have hr : u.val % p < p := Nat.mod_lt _ hp.pos
  have hval : (a.2.2 + b.2.2).val = u.val % p := by
    rw [hfield]
    exact ZMod.val_natCast_of_lt hr
  by_cases hs : a.2.2.val + b.2.2.val < p
  · rw [carry_eq_zero hs]
    simpa using (show a.2.2.val + b.2.2.val = u.val % p by
      rw [← ZMod.val_add_of_lt hs, hval])
  · rw [carry_eq_one hs]
    simpa using (show a.2.2.val + b.2.2.val = u.val % p + p by
      calc
        a.2.2.val + b.2.2.val = (a.2.2 + b.2.2).val + p :=
          ZMod.val_add_val_of_le (not_lt.mp hs)
        _ = u.val % p + p := by rw [hval])

private theorem high_equation_of_value_add_eq {p : ℕ} (hp : p.Prime)
    (S : CoefficientSystem p) {a b : Parameter p} {u : ZMod (p ^ 2)}
    (hab : value S a + value S b = u) :
    high S a + high S b + ((carry a b).val : F p) =
      ((u.val / p : ℕ) : F p) := by
  letI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hm2 := raw_modEq_of_value_add_eq hp S hab
  have hlow := low_val_add_eq hp S hab
  let r := u.val % p
  let h := u.val / p
  have hu : u.val = r + p * h := by
    dsimp [r, h]
    exact (Nat.mod_add_div u.val p).symm
  have hraw : a.2.2.val + p * (high S a).val +
      (b.2.2.val + p * (high S b).val) =
      r + p * ((high S a).val + (high S b).val + (carry a b).val) := by
    calc
      a.2.2.val + p * (high S a).val +
          (b.2.2.val + p * (high S b).val) =
          (a.2.2.val + b.2.2.val) +
            p * ((high S a).val + (high S b).val) := by ring
      _ = (r + p * (carry a b).val) +
            p * ((high S a).val + (high S b).val) := by rw [hlow]
      _ = r + p * ((high S a).val + (high S b).val + (carry a b).val) := by ring
  rw [hraw, hu] at hm2
  have hcancel : (high S a).val + (high S b).val + (carry a b).val ≡ h [MOD p] := by
    have hc : p * ((high S a).val + (high S b).val + (carry a b).val) ≡
        p * h [MOD p ^ 2] := Nat.ModEq.add_left_cancel' r hm2
    rw [pow_two] at hc
    exact Nat.ModEq.mul_left_cancel' hp.ne_zero hc
  have hz : (((high S a).val + (high S b).val + (carry a b).val : ℕ) : F p) =
      (h : F p) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact hcancel
  simpa only [Nat.cast_add, ZMod.natCast_zmod_val, h] using hz

/-- All discrete tags of an ordered lifted representation, including its
low-coordinate carry. -/
abbrev SliceTag := (Fin 3 × Fin 2) × (Fin 3 × Fin 2) × Fin 2

/-- The tag by which the representation set is partitioned. -/
def sliceTag {p : ℕ} (ab : Parameter p × Parameter p) : SliceTag :=
  ((ab.1.1, ab.1.2.1), (ab.2.1, ab.2.2.1), carry ab.1 ab.2)

/-- Ordered tagged representations of one residue. -/
def taggedRepresentations {p : ℕ} [NeZero p]
    (S : CoefficientSystem p) (u : ZMod (p ^ 2)) :
    Finset (Parameter p × Parameter p) :=
  Finset.univ.filter fun ab ↦ value S ab.1 + value S ab.2 = u

/-- A fixed coefficient/shift/carry slice contains at most two tagged
representations. -/
theorem tagged_slice_card_le_two {p : ℕ} [NeZero p] (hp : p.Prime)
    (S : CoefficientSystem p) (u : ZMod (p ^ 2)) (t : SliceTag) :
    ((taggedRepresentations S u).filter fun ab ↦ sliceTag ab = t).card ≤ 2 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let r : F p := (u.val % p : ℕ)
  let v : F p := (u.val / p : ℕ) - shift p t.1.2 -
    shift p t.2.1.2 - t.2.2.val
  let Q := QuadraticFiber.lineQuadraticFiber
      (S.coeff t.1.1) (S.coeff t.2.1.1) r v
  have hmaps : Set.MapsTo (fun ab : Parameter p × Parameter p ↦
      (ab.1.2.2, ab.2.2.2))
      (((taggedRepresentations S u).filter fun ab ↦ sliceTag ab = t) :
        Set (Parameter p × Parameter p)) (Q : Set (F p × F p)) := by
    intro ab hab
    have hab' := (Finset.mem_filter.mp hab).1
    have htag := (Finset.mem_filter.mp hab).2
    have hsum : value S ab.1 + value S ab.2 = u :=
      (Finset.mem_filter.mp hab').2
    have hlow := low_equation_of_value_add_eq hp S hsum
    have hhigh := high_equation_of_value_add_eq hp S hsum
    have hi : ab.1.1 = t.1.1 := by
      simpa [sliceTag] using congrArg (fun z ↦ z.1.1) htag
    have hsi : ab.1.2.1 = t.1.2 := by
      simpa [sliceTag] using congrArg (fun z ↦ z.1.2) htag
    have hj : ab.2.1 = t.2.1.1 := by
      simpa [sliceTag] using congrArg (fun z ↦ z.2.1.1) htag
    have hsj : ab.2.2.1 = t.2.1.2 := by
      simpa [sliceTag] using congrArg (fun z ↦ z.2.1.2) htag
    have he : carry ab.1 ab.2 = t.2.2 := by
      simpa [sliceTag] using congrArg (fun z ↦ z.2.2) htag
    simp only [Q, QuadraticFiber.lineQuadraticFiber, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by simpa [r] using hlow, ?_⟩
    dsimp [high] at hhigh
    dsimp [v]
    rw [hi, hsi, hj, hsj, he] at hhigh
    linear_combination hhigh
  have hinj : Set.InjOn (fun ab : Parameter p × Parameter p ↦
      (ab.1.2.2, ab.2.2.2))
      (((taggedRepresentations S u).filter fun ab ↦ sliceTag ab = t) :
        Set (Parameter p × Parameter p)) := by
    intro ab hab cd hcd hlow
    have habtag := (Finset.mem_filter.mp hab).2
    have hcdtag := (Finset.mem_filter.mp hcd).2
    have htags : sliceTag ab = sliceTag cd := habtag.trans hcdtag.symm
    rcases ab with ⟨⟨ia, sa, xa⟩, ⟨ja, ta, ya⟩⟩
    rcases cd with ⟨⟨ib, sb, xb⟩, ⟨jb, tb, yb⟩⟩
    simp only [sliceTag, Prod.mk.injEq] at htags hlow ⊢
    aesop
  calc
    ((taggedRepresentations S u).filter fun ab ↦ sliceTag ab = t).card ≤ Q.card :=
      Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ 2 := QuadraticFiber.lineQuadraticFiber_card_le_two _ _ _ _
      (S.coeff_add_ne_zero _ _)

/-- Uniform bound for ordered tagged representations of a residue modulo
`p^2`. -/
theorem taggedRepresentations_card_le {p : ℕ} [NeZero p] (hp : p.Prime)
    (S : CoefficientSystem p) (u : ZMod (p ^ 2)) :
    (taggedRepresentations S u).card ≤ 144 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  calc
    (taggedRepresentations S u).card =
        ∑ t : SliceTag,
          ((taggedRepresentations S u).filter fun ab ↦ sliceTag ab = t).card := by
      exact Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (by simp)
    _ ≤ ∑ _t : SliceTag, 2 := Finset.sum_le_sum fun t _ ↦ tagged_slice_card_le_two hp S u t
    _ = 144 := by norm_num [Fintype.card_prod, Fintype.card_fin]

/-! ## Untagged residue and natural-representative APIs -/

/-- Ordered representations using the untagged residue digit set. -/
def residueRepresentations {p : ℕ} [NeZero p]
    (S : CoefficientSystem p) (u : ZMod (p ^ 2)) :
    Finset (ZMod (p ^ 2) × ZMod (p ^ 2)) :=
  ((residueDigitSet S).product (residueDigitSet S)).filter fun ab ↦ ab.1 + ab.2 = u

/-- Forgetting the tags cannot increase the representation count. -/
theorem residueRepresentations_card_le {p : ℕ} [NeZero p] (hp : p.Prime)
    (S : CoefficientSystem p) (u : ZMod (p ^ 2)) :
    (residueRepresentations S u).card ≤ 144 := by
  classical
  let f : Parameter p × Parameter p → ZMod (p ^ 2) × ZMod (p ^ 2) :=
    fun ab ↦ (value S ab.1, value S ab.2)
  have hsurj : Set.SurjOn f (taggedRepresentations S u : Set _)
      (residueRepresentations S u : Set _) := by
    intro zw hzw
    have hprod := (Finset.mem_filter.mp hzw).1
    have hsum := (Finset.mem_filter.mp hzw).2
    have hza := (Finset.mem_product.mp hprod).1
    have hzb := (Finset.mem_product.mp hprod).2
    rcases Finset.mem_image.mp hza with ⟨a, _ha, hva⟩
    rcases Finset.mem_image.mp hzb with ⟨b, _hb, hvb⟩
    refine ⟨(a, b), ?_, ?_⟩
    · simp only [taggedRepresentations, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_univ, true_and]
      simpa [f, hva, hvb] using hsum
    · simp [f, hva, hvb]
  exact (Finset.card_le_card_of_surjOn f hsurj).trans
    (taggedRepresentations_card_le hp S u)

/-- Ordered representations by standard natural digit representatives. -/
def digitRepresentations {p : ℕ} [NeZero p]
    (S : CoefficientSystem p) (n : ℕ) : Finset (ℕ × ℕ) :=
  ((digitSet S).product (digitSet S)).filter fun ab ↦ ab.1 + ab.2 = n

theorem natCast_mem_residueDigitSet {p : ℕ} [NeZero p]
    (S : CoefficientSystem p) {d : ℕ} (hd : d ∈ digitSet S) :
    (d : ZMod (p ^ 2)) ∈ residueDigitSet S := by
  classical
  rcases Finset.mem_image.mp hd with ⟨z, hz, hzd⟩
  rw [← hzd, z.natCast_zmod_val]
  exact hz

/-- The natural representative digit set has at most `144` ordered
representations of every integer. -/
theorem digitRepresentations_card_le {p : ℕ} [NeZero p] (hp : p.Prime)
    (S : CoefficientSystem p) (n : ℕ) :
    (digitRepresentations S n).card ≤ 144 := by
  classical
  let f : ℕ × ℕ → ZMod (p ^ 2) × ZMod (p ^ 2) :=
    fun ab ↦ (ab.1, ab.2)
  have hmaps : Set.MapsTo f (digitRepresentations S n : Set _)
      (residueRepresentations S (n : ZMod (p ^ 2)) : Set _) := by
    rintro ⟨x, y⟩ hab
    have hprod := (Finset.mem_filter.mp hab).1
    have hsum := (Finset.mem_filter.mp hab).2
    have hxa := (Finset.mem_product.mp hprod).1
    have hxb := (Finset.mem_product.mp hprod).2
    rcases Finset.mem_image.mp hxa with ⟨za, hza, hxaeq⟩
    rcases Finset.mem_image.mp hxb with ⟨zb, hzb, hxbeq⟩
    simp only at hsum hxaeq hxbeq
    subst x
    subst y
    change f (za.val, zb.val) ∈
      ((residueDigitSet S).product (residueDigitSet S)).filter
        (fun ab ↦ ab.1 + ab.2 = (n : ZMod (p ^ 2)))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · simpa [f] using hza
    · simpa [f] using hzb
    · dsimp [f]
      rw [← Nat.cast_add, hsum]
  have hinj : Set.InjOn f (digitRepresentations S n : Set _) := by
    intro ab hab cd hcd heq
    have habp := (Finset.mem_filter.mp hab).1
    have hcdp := (Finset.mem_filter.mp hcd).1
    have hab1 := (Finset.mem_product.mp habp).1
    have hab2 := (Finset.mem_product.mp habp).2
    have hcd1 := (Finset.mem_product.mp hcdp).1
    have hcd2 := (Finset.mem_product.mp hcdp).2
    have ha_lt := mem_digitSet_lt S hp.pos hab1
    have hb_lt := mem_digitSet_lt S hp.pos hab2
    have hc_lt := mem_digitSet_lt S hp.pos hcd1
    have hd_lt := mem_digitSet_lt S hp.pos hcd2
    apply Prod.ext
    · have hz := congrArg Prod.fst heq
      simpa [f, ZMod.val_natCast_of_lt ha_lt, ZMod.val_natCast_of_lt hc_lt] using
        congrArg ZMod.val hz
    · have hz := congrArg Prod.snd heq
      simpa [f, ZMod.val_natCast_of_lt hb_lt, ZMod.val_natCast_of_lt hd_lt] using
        congrArg ZMod.val hz
  exact (Finset.card_le_card_of_injOn f hmaps hinj).trans
    (residueRepresentations_card_le hp S (n : ZMod (p ^ 2)))

/-- Ordered natural digit pairs whose sum lies in a prescribed residue class
modulo `p^2`.  This is the local multiplicity interface used in the global
mixed-radix count. -/
def digitModRepresentations {p : ℕ} [NeZero p]
    (S : CoefficientSystem p) (r : ℕ) : Finset (ℕ × ℕ) :=
  ((digitSet S).product (digitSet S)).filter fun ab ↦
    (ab.1 + ab.2) % (p ^ 2) = r

/-- Every residue class modulo `p^2` has at most `144` ordered
representations by natural digits. -/
theorem digitModRepresentations_card_le {p : ℕ} [NeZero p]
    (hp : p.Prime) (S : CoefficientSystem p) (r : ℕ) (hr : r < p ^ 2) :
    (digitModRepresentations S r).card ≤ 144 := by
  classical
  let f : ℕ × ℕ → ZMod (p ^ 2) × ZMod (p ^ 2) :=
    fun ab ↦ (ab.1, ab.2)
  have hmaps : Set.MapsTo f (digitModRepresentations S r : Set _)
      (residueRepresentations S (r : ZMod (p ^ 2)) : Set _) := by
    intro ab hab
    have hprod := (Finset.mem_filter.mp hab).1
    have hsum := (Finset.mem_filter.mp hab).2
    have hxa := (Finset.mem_product.mp hprod).1
    have hxb := (Finset.mem_product.mp hprod).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨natCast_mem_residueDigitSet S hxa,
      natCast_mem_residueDigitSet S hxb⟩, ?_⟩
    rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
    show ab.1 + ab.2 ≡ r [MOD p ^ 2]
    simp only [Nat.ModEq, hsum, Nat.mod_eq_of_lt hr]
  have hinj : Set.InjOn f (digitModRepresentations S r : Set _) := by
    intro ab hab cd hcd heq
    have habp := (Finset.mem_filter.mp hab).1
    have hcdp := (Finset.mem_filter.mp hcd).1
    have hab1 := (Finset.mem_product.mp habp).1
    have hab2 := (Finset.mem_product.mp habp).2
    have hcd1 := (Finset.mem_product.mp hcdp).1
    have hcd2 := (Finset.mem_product.mp hcdp).2
    have ha_lt := mem_digitSet_lt S hp.pos hab1
    have hb_lt := mem_digitSet_lt S hp.pos hab2
    have hc_lt := mem_digitSet_lt S hp.pos hcd1
    have hd_lt := mem_digitSet_lt S hp.pos hcd2
    apply Prod.ext
    · have hz := congrArg Prod.fst heq
      simpa [f, ZMod.val_natCast_of_lt ha_lt, ZMod.val_natCast_of_lt hc_lt] using
        congrArg ZMod.val hz
    · have hz := congrArg Prod.snd heq
      simpa [f, ZMod.val_natCast_of_lt hb_lt, ZMod.val_natCast_of_lt hd_lt] using
        congrArg ZMod.val hz
  exact (Finset.card_le_card_of_injOn f hmaps hinj).trans
    (residueRepresentations_card_le hp S (r : ZMod (p ^ 2)))

/-- Carry-aware local coverage in exactly the form required by the
mixed-radix construction. -/
theorem digit_carryCover {p : ℕ} [NeZero p] (hp : p.Prime)
    (S : CoefficientSystem p) (r c : ℕ) (hr : r < p ^ 2) (hc : c ≤ 1) :
    ∃ x ∈ digitSet S, ∃ y ∈ digitSet S, ∃ c' ≤ 1,
      x + y + c = r + p ^ 2 * c' := by
  classical
  let u : ZMod (p ^ 2) := (r : ZMod (p ^ 2)) - c
  rcases residueDigitSet_add_cover hp S u with ⟨a, ha, b, hb, hab⟩
  let x := a.val
  let y := b.val
  have hx : x ∈ digitSet S := Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hy : y ∈ digitSet S := Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hxlt : x < p ^ 2 := mem_digitSet_lt S hp.pos hx
  have hylt : y < p ^ 2 := mem_digitSet_lt S hp.pos hy
  let N := x + y + c
  have hcast : (N : ZMod (p ^ 2)) = (r : ZMod (p ^ 2)) := by
    dsimp [N, x, y]
    rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, hab]
    dsimp [u]
    ring
  have hmodEq : N ≡ r [MOD p ^ 2] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    exact hcast
  have hmod : N % (p ^ 2) = r := by
    rw [hmodEq]
    exact Nat.mod_eq_of_lt hr
  let c' := N / (p ^ 2)
  have hbase : 0 < p ^ 2 := pow_pos hp.pos 2
  have hNlt : N < 2 * (p ^ 2) := by
    dsimp [N, x, y]
    omega
  have hc'lt : c' < 2 := by
    exact (Nat.div_lt_iff_lt_mul hbase).2 (by simpa [Nat.mul_comm] using hNlt)
  refine ⟨x, hx, y, hy, c', by omega, ?_⟩
  have hdecomp := Nat.mod_add_div N (p ^ 2)
  dsimp [c']
  omega

end ModularLift

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos29/Modular.lean` -/

section
/-!
# The finite modular ingredient for Erdős Problem 29

This file formalizes the flat-parabola construction used by Ruzsa and by
Jain--Pham--Sawhney--Zakharov.  The finite-field part is kept separate from
the elementary lift from `ZMod p × ZMod p` to `ZMod (p ^ 2)`.
-/

namespace Modular

open scoped BigOperators

private abbrev F (p : ℕ) := ZMod p

/-- The three quadratic coefficients `3, 4, 6`. -/
def coefficient (p : ℕ) : Fin 3 → F p
  | i => if i = 0 then 3 else if i = 1 then 4 else 6

/-- The three carry-correcting shifts `-1, 0, 1`. -/
def shift (p : ℕ) : Fin 3 → F p
  | i => if i = 0 then -1 else if i = 1 then 0 else 1

@[simp] lemma coefficient_zero (p : ℕ) : coefficient p 0 = 3 := by simp [coefficient]
@[simp] lemma coefficient_one (p : ℕ) : coefficient p 1 = 4 := by simp [coefficient]
@[simp] lemma coefficient_two (p : ℕ) : coefficient p 2 = 6 := by simp [coefficient]

@[simp] lemma shift_zero (p : ℕ) : shift p 0 = -1 := by simp [shift]
@[simp] lemma shift_one (p : ℕ) : shift p 1 = 0 := by simp [shift]
@[simp] lemma shift_two (p : ℕ) : shift p 2 = 1 := by simp [shift]

/-- A tagged point on one of the three shifted parabolas. -/
abbrev Parameter (p : ℕ) := Fin 3 × Fin 3 × F p

/-- The high coordinate of a tagged point. -/
def high (p : ℕ) (a : Parameter p) : F p :=
  2 * coefficient p a.1 * a.2.2 ^ 2 + shift p a.2.1

/-- The unshifted parabola equation used to cover `F_p²`. -/
def parabolaEquation (c d x y : F p) (q : F p × F p) : Prop :=
  x + y = q.1 ∧ c * x ^ 2 + d * y ^ 2 = q.2

private lemma two_ne_zero {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) : (2 : F p) ≠ 0 := by
  change ¬ (((2 : ℕ) : ZMod p) = 0)
  rw [ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

private lemma three_ne_zero {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) : (3 : F p) ≠ 0 := by
  change ¬ (((3 : ℕ) : ZMod p) = 0)
  rw [ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

private lemma four_ne_zero {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) : (4 : F p) ≠ 0 := by
  change ¬ (((4 : ℕ) : ZMod p) = 0)
  rw [ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

/-- The two pairs of parabolas cover every point of `F_p²` when `2` is a
nonsquare.  This is the finite-field heart of Ruzsa's construction. -/
theorem exists_parabola_representation {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (h2 : ¬ IsSquare (2 : F p)) (u v : F p) :
    (∃ x y, x + y = u ∧ 3 * x ^ 2 + 6 * y ^ 2 = v) ∨
      ∃ x y, x + y = u ∧ 4 * x ^ 2 + 4 * y ^ 2 = v := by
  letI : Fact p.Prime := ⟨hp⟩
  let T : F p := v - 2 * u ^ 2
  by_cases hT : IsSquare T
  · rcases hT with ⟨z, hz⟩
    left
    refine ⟨(2 * u + z) / 3, (u - z) / 3, ?_, ?_⟩
    · field_simp [three_ne_zero hp hp11]
      ring
    · dsimp [T] at hz
      have hv : v = 2 * u ^ 2 + z ^ 2 := by
        linear_combination hz
      rw [hv]
      field_simp [three_ne_zero hp hp11]
      ring
  · have hT0 : T ≠ 0 := fun h ↦ hT (h ▸ IsSquare.zero)
    have h20 : (2 : F p) ≠ 0 := fun h ↦ h2 (h ▸ IsSquare.zero)
    have hchar : ringChar (F p) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      omega
    have hprod : IsSquare ((2 : F p) * T) := by
      have hc2 : quadraticChar (F p) (2 : F p) = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr h2
      have hcT : quadraticChar (F p) T = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr hT
      have hc : quadraticChar (F p) ((2 : F p) * T) = 1 := by
        rw [map_mul, hc2, hcT]
        norm_num
      exact (quadraticChar_one_iff_isSquare (mul_ne_zero h20 hT0)).mp hc
    rcases hprod with ⟨z, hz⟩
    right
    refine ⟨(2 * u + z) / 4, (2 * u - z) / 4, ?_, ?_⟩
    · field_simp [four_ne_zero hp hp11]
      ring
    · dsimp [T] at hz
      have hv : v = 2 * u ^ 2 + z ^ 2 / 2 := by
        field_simp [two_ne_zero hp hp11]
        linear_combination hz
      rw [hv]
      field_simp [two_ne_zero hp hp11, four_ne_zero hp hp11]
      ring

/-- Encode a low coordinate and a high coordinate as a residue modulo `p²`. -/
def encode (p : ℕ) (x q : F p) : ZMod (p ^ 2) :=
  (x.val + p * q.val : ℕ)

/-- The residue represented by a tagged shifted-parabola parameter. -/
def value (p : ℕ) (a : Parameter p) : ZMod (p ^ 2) :=
  encode p a.2.2 (high p a)

/-- The explicit finite modular digit set. -/
def legacyDigitSetZMod (p : ℕ) : Finset (ZMod (p ^ 2)) :=
  if hp : 0 < p then
    letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
    Finset.univ.image (value p)
  else ∅

@[simp] theorem value_mem_legacyDigitSetZMod (p : ℕ) (hp : 0 < p) (a : Parameter p) :
    value p a ∈ legacyDigitSetZMod p := by
  classical
  simp only [legacyDigitSetZMod, dif_pos hp, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨a, rfl⟩

private lemma value_add_eq_of_carry {p : ℕ} (hp0 : 0 < p) (a b : Parameter p)
    (u : ZMod (p ^ 2)) (r h e : ℕ)
    (hlow : a.2.2.val + b.2.2.val = r + p * e)
    (hhigh : high p a + high p b + (e : F p) = (h : F p))
    (hu : u.val = r + p * h) : value p a + value p b = u := by
  haveI : NeZero p := ⟨Nat.ne_of_gt hp0⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp0)⟩
  have hm : (high p a).val + (high p b).val + e ≡ h [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hhigh
  have hm' := hm.mul_left' p
  have hm'' := Nat.ModEq.add_left r hm'
  rw [← u.natCast_zmod_val]
  change ((a.2.2.val + p * (high p a).val : ℕ) : ZMod (p ^ 2)) +
      (b.2.2.val + p * (high p b).val : ℕ) = (u.val : ZMod (p ^ 2))
  rw [← Nat.cast_add]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).2
  have hraw : a.2.2.val + p * (high p a).val +
      (b.2.2.val + p * (high p b).val) =
      r + p * ((high p a).val + (high p b).val + e) := by
    calc
      a.2.2.val + p * (high p a).val + (b.2.2.val + p * (high p b).val) =
          (a.2.2.val + b.2.2.val) + p * ((high p a).val + (high p b).val) := by ring
      _ = (r + p * e) + p * ((high p a).val + (high p b).val) := by rw [hlow]
      _ = r + p * ((high p a).val + (high p b).val + e) := by ring
  rw [hraw, hu]
  simpa only [pow_two] using hm''

private lemma high_add_eq {p : ℕ} (i j s t : Fin 3) (x y : F p) (q e η h : ℕ)
    (hcurve : coefficient p i * x ^ 2 + coefficient p j * y ^ 2 = (q : F p))
    (hshift : shift p s + shift p t + (e : F p) = (η : F p))
    (hh : 2 * q + η = h) :
    high p (i, s, x) + high p (j, t, y) + (e : F p) = (h : F p) := by
  have hh' : ((2 * q + η : ℕ) : F p) = (h : F p) := congrArg (· : ℕ → F p) hh
  simp only [Nat.cast_add, Nat.cast_mul] at hh'
  dsimp [high]
  linear_combination 2 * hcurve + hshift + hh'

/-- Every residue modulo `p²` is the sum of two tagged values. -/
theorem exists_value_add_eq {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (h2 : ¬ IsSquare (2 : F p)) (u : ZMod (p ^ 2)) :
    ∃ a b : Parameter p, value p a + value p b = u := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let r := u.val % p
  let h := u.val / p
  let q := h / 2
  let η := h % 2
  have hr : r < p := Nat.mod_lt _ hp0
  have hhval : h < p := by
    apply (Nat.div_lt_iff_lt_mul hp0).2
    simpa only [pow_two] using u.val_lt
  have hη : η = 0 ∨ η = 1 := Nat.mod_two_eq_zero_or_one h
  have hhq : 2 * q + η = h := by
    dsimp [q, η]
    omega
  have hu : u.val = r + p * h := by
    dsimp [r, h]
    exact (Nat.mod_add_div u.val p).symm
  rcases exists_parabola_representation hp hp11 h2 (r : F p) (q : F p) with
      h36 | h44
  · rcases h36 with ⟨x, y, hxy, hcurve⟩
    have haddval : (x + y).val = r := by
      rw [hxy]
      exact ZMod.val_natCast_of_lt hr
    have hlow : x.val + y.val = r ∨ x.val + y.val = r + p := by
      by_cases hs : x.val + y.val < p
      · left
        rw [← ZMod.val_add_of_lt hs, haddval]
      · right
        calc
          x.val + y.val = (x + y).val + p := ZMod.val_add_val_of_le (not_lt.mp hs)
          _ = r + p := by rw [haddval]
    rcases hlow with hlow | hlow
    · rcases hη with hη | hη
      · refine ⟨(0, 1, x), (2, 1, y), value_add_eq_of_carry hp0 _ _ u r h 0 ?_ ?_ hu⟩
        · simpa using hlow
        · apply high_add_eq (q := q) (e := 0) (η := 0) (h := h) <;>
            simp_all [coefficient, shift]
      · refine ⟨(0, 2, x), (2, 1, y), value_add_eq_of_carry hp0 _ _ u r h 0 ?_ ?_ hu⟩
        · simpa using hlow
        · apply high_add_eq (q := q) (e := 0) (η := 1) (h := h) <;>
            simp_all [coefficient, shift]
    · rcases hη with hη | hη
      · refine ⟨(0, 0, x), (2, 1, y), value_add_eq_of_carry hp0 _ _ u r h 1 ?_ ?_ hu⟩
        · simpa using hlow
        · apply high_add_eq (q := q) (e := 1) (η := 0) (h := h) <;>
            simp_all [coefficient, shift]
      · refine ⟨(0, 1, x), (2, 1, y), value_add_eq_of_carry hp0 _ _ u r h 1 ?_ ?_ hu⟩
        · simpa using hlow
        · apply high_add_eq (q := q) (e := 1) (η := 1) (h := h) <;>
            simp_all [coefficient, shift]
  · rcases h44 with ⟨x, y, hxy, hcurve⟩
    have haddval : (x + y).val = r := by
      rw [hxy]
      exact ZMod.val_natCast_of_lt hr
    have hlow : x.val + y.val = r ∨ x.val + y.val = r + p := by
      by_cases hs : x.val + y.val < p
      · left
        rw [← ZMod.val_add_of_lt hs, haddval]
      · right
        calc
          x.val + y.val = (x + y).val + p := ZMod.val_add_val_of_le (not_lt.mp hs)
          _ = r + p := by rw [haddval]
    rcases hlow with hlow | hlow
    · rcases hη with hη | hη
      · refine ⟨(1, 1, x), (1, 1, y), value_add_eq_of_carry hp0 _ _ u r h 0 ?_ ?_ hu⟩
        · simpa using hlow
        · apply high_add_eq (q := q) (e := 0) (η := 0) (h := h) <;>
            simp_all [coefficient, shift]
      · refine ⟨(1, 2, x), (1, 1, y), value_add_eq_of_carry hp0 _ _ u r h 0 ?_ ?_ hu⟩
        · simpa using hlow
        · apply high_add_eq (q := q) (e := 0) (η := 1) (h := h) <;>
            simp_all [coefficient, shift]
    · rcases hη with hη | hη
      · refine ⟨(1, 0, x), (1, 1, y), value_add_eq_of_carry hp0 _ _ u r h 1 ?_ ?_ hu⟩
        · simpa using hlow
        · apply high_add_eq (q := q) (e := 1) (η := 0) (h := h) <;>
            simp_all [coefficient, shift]
      · refine ⟨(1, 1, x), (1, 1, y), value_add_eq_of_carry hp0 _ _ u r h 1 ?_ ?_ hu⟩
        · simpa using hlow
        · apply high_add_eq (q := q) (e := 1) (η := 1) (h := h) <;>
            simp_all [coefficient, shift]

/-- The explicit digit set covers every residue by two summands. -/
theorem legacyDigitSetZMod_add_cover {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (h2 : ¬ IsSquare (2 : F p)) (u : ZMod (p ^ 2)) :
    ∃ a ∈ legacyDigitSetZMod p, ∃ b ∈ legacyDigitSetZMod p, a + b = u := by
  rcases exists_value_add_eq hp hp11 h2 u with ⟨a, b, hab⟩
  exact ⟨value p a, value_mem_legacyDigitSetZMod p hp.pos a,
    value p b, value_mem_legacyDigitSetZMod p hp.pos b, hab⟩

/-! ## The all-prime refinement -/

/-- Coefficients `2, 1+t, 1+t⁻¹` used for an arbitrary chosen nonsquare `t`. -/
def allCoefficient (p : ℕ) (t : F p) : Fin 3 → F p
  | i => if i = 0 then 2 else if i = 1 then 1 + t else 1 + t⁻¹

@[simp] lemma allCoefficient_zero (p : ℕ) (t : F p) : allCoefficient p t 0 = 2 := by
  simp [allCoefficient]

@[simp] lemma allCoefficient_one (p : ℕ) (t : F p) : allCoefficient p t 1 = 1 + t := by
  simp [allCoefficient]

@[simp] lemma allCoefficient_two (p : ℕ) (t : F p) : allCoefficient p t 2 = 1 + t⁻¹ := by
  simp [allCoefficient]

/-- The two lift shifts `-1,0`. -/
def allShift (p : ℕ) : Fin 2 → F p
  | i => if i = 0 then -1 else 0

@[simp] lemma allShift_zero (p : ℕ) : allShift p 0 = -1 := by simp [allShift]
@[simp] lemma allShift_one (p : ℕ) : allShift p 1 = 0 := by simp [allShift]

/-- The three all-prime parabolas cover every point of `F_p²`. -/
theorem exists_all_parabola_representation {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (t : F p) (ht : ¬ IsSquare t) (ht1 : t ≠ -1) (u v : F p) :
    ∃ i j : Fin 3, ∃ x y : F p,
      x + y = u ∧ allCoefficient p t i * x ^ 2 + allCoefficient p t j * y ^ 2 = v := by
  letI : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : F p) ≠ 0 := two_ne_zero hp hp11
  have ht0 : t ≠ 0 := fun h ↦ ht (h ▸ IsSquare.zero)
  have htadd : t + 1 ≠ 0 := by
    intro h
    apply ht1
    linear_combination h
  let T : F p := v - u ^ 2
  by_cases hT : IsSquare T
  · rcases hT with ⟨z, hz⟩
    refine ⟨0, 0, (u + z) / 2, (u - z) / 2, ?_, ?_⟩
    · field_simp [htwo]
      ring
    · dsimp [T] at hz
      have hv : v = u ^ 2 + z ^ 2 := by linear_combination hz
      rw [hv]
      simp only [allCoefficient_zero]
      field_simp [htwo]
      ring
  · have hT0 : T ≠ 0 := fun h ↦ hT (h ▸ IsSquare.zero)
    have hprod : IsSquare (t * T) := by
      have hct : quadraticChar (F p) t = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr ht
      have hcT : quadraticChar (F p) T = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr hT
      have hc : quadraticChar (F p) (t * T) = 1 := by
        rw [map_mul, hct, hcT]
        norm_num
      exact (quadraticChar_one_iff_isSquare (mul_ne_zero ht0 hT0)).mp hc
    rcases hprod with ⟨z, hz⟩
    refine ⟨1, 2, (u + z) / (t + 1), (t * u - z) / (t + 1), ?_, ?_⟩
    · field_simp [htadd]
      ring
    · dsimp [T] at hz
      simp only [allCoefficient_one, allCoefficient_two]
      rw [inv_eq_one_div]
      field_simp [ht0, htadd]
      linear_combination -(t + 1) ^ 2 * hz

/-- Tagged parameters for the all-prime construction. -/
abbrev AllParameter (p : ℕ) := Fin 3 × Fin 2 × F p

/-- High digit in the all-prime construction. -/
def allHigh (p : ℕ) (t : F p) (a : AllParameter p) : F p :=
  allCoefficient p t a.1 * a.2.2 ^ 2 + allShift p a.2.1

/-- Lift an all-prime parameter to `ZMod (p²)`. -/
def allValue (p : ℕ) (t : F p) (a : AllParameter p) : ZMod (p ^ 2) :=
  encode p a.2.2 (allHigh p t a)

/-- The finite set of residues produced by all-prime parameters. -/
def allDigitSetZMod (p : ℕ) (t : F p) : Finset (ZMod (p ^ 2)) :=
  if hp : 0 < p then
    letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
    Finset.univ.image (allValue p t)
  else ∅

@[simp] theorem allValue_mem (p : ℕ) (hp : 0 < p) (t : F p) (a : AllParameter p) :
    allValue p t a ∈ allDigitSetZMod p t := by
  classical
  simp only [allDigitSetZMod, dif_pos hp, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨a, rfl⟩

private lemma allValue_add_eq_of_carry {p : ℕ} (hp0 : 0 < p) (t : F p)
    (a b : AllParameter p) (u : ZMod (p ^ 2)) (r h e : ℕ)
    (hlow : a.2.2.val + b.2.2.val = r + p * e)
    (hhigh : allHigh p t a + allHigh p t b + (e : F p) = (h : F p))
    (hu : u.val = r + p * h) : allValue p t a + allValue p t b = u := by
  haveI : NeZero p := ⟨Nat.ne_of_gt hp0⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp0)⟩
  have hm : (allHigh p t a).val + (allHigh p t b).val + e ≡ h [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hhigh
  have hm'' := Nat.ModEq.add_left r (hm.mul_left' p)
  rw [← u.natCast_zmod_val]
  change ((a.2.2.val + p * (allHigh p t a).val : ℕ) : ZMod (p ^ 2)) +
      (b.2.2.val + p * (allHigh p t b).val : ℕ) = (u.val : ZMod (p ^ 2))
  rw [← Nat.cast_add]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).2
  have hraw : a.2.2.val + p * (allHigh p t a).val +
      (b.2.2.val + p * (allHigh p t b).val) =
      r + p * ((allHigh p t a).val + (allHigh p t b).val + e) := by
    calc
      a.2.2.val + p * (allHigh p t a).val +
          (b.2.2.val + p * (allHigh p t b).val) =
          (a.2.2.val + b.2.2.val) +
            p * ((allHigh p t a).val + (allHigh p t b).val) := by ring
      _ = (r + p * e) + p * ((allHigh p t a).val + (allHigh p t b).val) := by rw [hlow]
      _ = r + p * ((allHigh p t a).val + (allHigh p t b).val + e) := by ring
  rw [hraw, hu]
  simpa only [pow_two] using hm''

private lemma allHigh_add_eq {p : ℕ} (t : F p) (i j : Fin 3) (s w : Fin 2)
    (x y : F p) (h e : ℕ)
    (hcurve : allCoefficient p t i * x ^ 2 + allCoefficient p t j * y ^ 2 = (h : F p))
    (hshift : allShift p s + allShift p w + (e : F p) = 0) :
    allHigh p t (i, s, x) + allHigh p t (j, w, y) + (e : F p) = (h : F p) := by
  dsimp [allHigh]
  linear_combination hcurve + hshift

/-- All-prime modular coverage for any admissible nonsquare `t`. -/
theorem exists_allValue_add_eq {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (t : F p) (ht : ¬ IsSquare t) (ht1 : t ≠ -1) (u : ZMod (p ^ 2)) :
    ∃ a b : AllParameter p, allValue p t a + allValue p t b = u := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let r := u.val % p
  let h := u.val / p
  have hr : r < p := Nat.mod_lt _ hp0
  have hu : u.val = r + p * h := by
    dsimp [r, h]
    exact (Nat.mod_add_div u.val p).symm
  rcases exists_all_parabola_representation hp hp11 t ht ht1 (r : F p) (h : F p) with
    ⟨i, j, x, y, hxy, hcurve⟩
  have haddval : (x + y).val = r := by
    rw [hxy]
    exact ZMod.val_natCast_of_lt hr
  by_cases hs : x.val + y.val < p
  · have hlow : x.val + y.val = r := by rw [← ZMod.val_add_of_lt hs, haddval]
    refine ⟨(i, 1, x), (j, 1, y), allValue_add_eq_of_carry hp0 t _ _ u r h 0 ?_ ?_ hu⟩
    · simpa using hlow
    · apply allHigh_add_eq (h := h) (e := 0) <;> simp_all [allShift]
  · have hlow : x.val + y.val = r + p := by
      calc
        x.val + y.val = (x + y).val + p := ZMod.val_add_val_of_le (not_lt.mp hs)
        _ = r + p := by rw [haddval]
    refine ⟨(i, 0, x), (j, 1, y), allValue_add_eq_of_carry hp0 t _ _ u r h 1 ?_ ?_ hu⟩
    · simpa using hlow
    · apply allHigh_add_eq (h := h) (e := 1) <;> simp_all [allShift]

/-- Natural representatives of the all-prime digit residues. -/
def allDigitSetNat (p : ℕ) (t : F p) : Finset ℕ :=
  (allDigitSetZMod p t).image ZMod.val

theorem allDigitSetNat_subset_range (p : ℕ) (hp : 0 < p) (t : F p) :
    allDigitSetNat p t ⊆ Finset.range (p ^ 2) := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp)⟩
  intro a ha
  simp only [allDigitSetNat, Finset.mem_image] at ha
  rcases ha with ⟨z, -, rfl⟩
  exact Finset.mem_range.mpr z.val_lt

/-- Natural-form modular coverage, in the exact shape used by mixed-radix digits. -/
theorem allDigitSetNat_cover {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (t : F p) (ht : ¬ IsSquare t) (ht1 : t ≠ -1) {r : ℕ} (hr : r < p ^ 2) :
    ∃ a ∈ allDigitSetNat p t, ∃ b ∈ allDigitSetNat p t, (a + b) % (p ^ 2) = r := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rcases exists_allValue_add_eq hp hp11 t ht ht1 (r : ZMod (p ^ 2)) with ⟨a, b, hab⟩
  refine ⟨(allValue p t a).val, ?_, (allValue p t b).val, ?_, ?_⟩
  · simp only [allDigitSetNat, Finset.mem_image]
    exact ⟨allValue p t a, allValue_mem p hp.pos t a, rfl⟩
  · simp only [allDigitSetNat, Finset.mem_image]
    exact ⟨allValue p t b, allValue_mem p hp.pos t b, rfl⟩
  · rw [← ZMod.val_add, hab, ZMod.val_natCast_of_lt hr]

/-! ## Public local digit set -/

/-- The coefficient system obtained from the bounded-search allowed nonsquare.
It works for every prime at least `11`; no congruence restriction on the prime
is imposed. -/
def allPrimeCoefficientSystem (p : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p) :
    ModularLift.CoefficientSystem p where
  coeff := allCoefficient p (Erdos29.allowedT p)
  cover := exists_all_parabola_representation hp hp11 (Erdos29.allowedT p)
    (Erdos29.allowedT_not_isSquare hp hp11) (Erdos29.allowedT_ne_neg_one hp hp11)
  coeff_add_ne_zero := by
    intro i j
    apply Erdos29.parabolaCoefficients_add_ne_zero hp hp11
    · fin_cases i <;> simp [allCoefficient, Erdos29.parabolaCoefficients]
    · fin_cases j <;> simp [allCoefficient, Erdos29.parabolaCoefficients]

/-- The completely explicit local digit set used in the global construction.
The nonsquare is selected by the bounded search in `AllowedNonsquare.lean`.
In particular, the definition itself does not contain primality proofs. -/
def digitSet (p : ℕ) : Finset ℕ :=
  allDigitSetNat p (Erdos29.allowedT p)

theorem digitSet_subset_range {p : ℕ} (hp : p.Prime) :
    digitSet p ⊆ Finset.range (p ^ 2) := by
  exact allDigitSetNat_subset_range p hp.pos (Erdos29.allowedT p)

theorem digitSet_mem_lt {p d : ℕ} (hp : p.Prime) (hd : d ∈ digitSet p) :
    d < p ^ 2 := Finset.mem_range.mp (digitSet_subset_range hp hd)

/-- Exact modular coverage by natural representatives. -/
theorem digitSet_cover {p r : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) (hr : r < p ^ 2) :
    ∃ a ∈ digitSet p, ∃ b ∈ digitSet p, (a + b) % (p ^ 2) = r := by
  exact allDigitSetNat_cover hp hp11 (Erdos29.allowedT p)
    (Erdos29.allowedT_not_isSquare hp hp11)
    (Erdos29.allowedT_ne_neg_one hp hp11) hr

/-- At a prime at least `11`, the proof-independent digit set agrees with the
natural digit set attached to `allPrimeCoefficientSystem`. -/
theorem digitSet_eq_lift {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    digitSet p = ModularLift.digitSet (allPrimeCoefficientSystem p hp hp11) := by
  classical
  simp only [digitSet, allDigitSetNat, allDigitSetZMod, dif_pos hp.pos,
    ModularLift.digitSet, ModularLift.residueDigitSet]
  congr 2

/-- Carry-aware local coverage, with an incoming and outgoing carry in
`{0,1}`, in the exact natural-number form used by mixed-radix arguments. -/
theorem digitSet_carryCover {p r c : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (hr : r < p ^ 2) (hc : c ≤ 1) :
    ∃ x ∈ digitSet p, ∃ y ∈ digitSet p, ∃ c' ≤ 1,
      x + y + c = r + p ^ 2 * c' := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [digitSet_eq_lift hp hp11]
  exact ModularLift.digit_carryCover hp (allPrimeCoefficientSystem p hp hp11)
    r c hr hc

/-- Ordered representations of `n` by the explicit natural local digits. -/
def digitRepresentations (p n : ℕ) : Finset (ℕ × ℕ) :=
  ((digitSet p).product (digitSet p)).filter fun ab ↦ ab.1 + ab.2 = n

/-- Every integer has at most `144` ordered exact-sum representations by the
local digit set. -/
theorem digitRepresentations_card_le {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (n : ℕ) : (digitRepresentations p n).card ≤ 144 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [digitRepresentations, digitSet_eq_lift hp hp11]
  exact ModularLift.digitRepresentations_card_le hp
    (allPrimeCoefficientSystem p hp hp11) n

/-- Ordered natural digit pairs whose sum is a prescribed residue modulo
`p^2`. -/
def digitModRepresentations (p r : ℕ) : Finset (ℕ × ℕ) :=
  ((digitSet p).product (digitSet p)).filter fun ab ↦
    (ab.1 + ab.2) % (p ^ 2) = r

/-- The explicit digit set has at most `144` ordered representations of each
residue modulo `p^2`. -/
theorem digitModRepresentations_card_le {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (r : ℕ) (hr : r < p ^ 2) : (digitModRepresentations p r).card ≤ 144 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [digitModRepresentations, digitSet_eq_lift hp hp11]
  exact ModularLift.digitModRepresentations_card_le hp
    (allPrimeCoefficientSystem p hp hp11) r hr

end Modular

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos29/Schedule.lean` -/

section
/-!
# The explicit radix schedule for Erdős problem 29

For the digit construction we need, at level `i`, a prime which is larger than
`i + 11` but at most twice that number.  `primeAt` is the least such prime in
the indicated *finite* interval.  Thus this is an executable bounded search;
Bertrand's postulate is used only to prove that its search interval is nonempty.

The radix at level `i` is the square of this prime, and `place k` is the
product of the first `k` radices.
-/



open scoped BigOperators

/-- The finite search space used to choose the prime at level `i`. -/
def primeCandidates (i : ℕ) : Finset ℕ :=
  (Finset.Icc (i + 12) (2 * (i + 11))).filter Nat.Prime

theorem primeCandidates_nonempty (i : ℕ) : (primeCandidates i).Nonempty := by
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.bertrand (i + 11) (by omega)
  refine ⟨p, ?_⟩
  simp only [primeCandidates, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, hhi⟩, hp⟩

/--
The least prime strictly larger than `i + 11` and at most `2 * (i + 11)`.

This definition is computational: `Finset.min'` searches the bounded finset
`primeCandidates i`; its proof argument is erased by code generation.
-/
def primeAt (i : ℕ) : ℕ :=
  (primeCandidates i).min' (primeCandidates_nonempty i)

theorem primeAt_mem (i : ℕ) : primeAt i ∈ primeCandidates i := by
  exact Finset.min'_mem _ _

theorem primeAt_prime (i : ℕ) : Nat.Prime (primeAt i) := by
  exact (Finset.mem_filter.mp (primeAt_mem i)).2

theorem primeAt_lower (i : ℕ) : i + 11 < primeAt i := by
  have h := (Finset.mem_Icc.mp (Finset.mem_of_mem_filter (primeAt i) (primeAt_mem i))).1
  omega

theorem primeAt_ge (i : ℕ) : i + 12 ≤ primeAt i := by
  have h := primeAt_lower i
  omega

theorem primeAt_upper (i : ℕ) : primeAt i ≤ 2 * (i + 11) := by
  exact (Finset.mem_Icc.mp (Finset.mem_of_mem_filter (primeAt i) (primeAt_mem i))).2

theorem primeAt_minimal {i q : ℕ} (hqPrime : Nat.Prime q)
    (hqLower : i + 11 < q) (hqUpper : q ≤ 2 * (i + 11)) : primeAt i ≤ q := by
  apply Finset.min'_le
  simp only [primeCandidates, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, hqUpper⟩, hqPrime⟩

theorem primeAt_mono : Monotone primeAt := by
  intro i j hij
  by_cases hq : primeAt j ≤ 2 * (i + 11)
  · apply primeAt_minimal (primeAt_prime j)
    · exact lt_of_le_of_lt (Nat.add_le_add_right hij 11) (primeAt_lower j)
    · exact hq
  · exact (primeAt_upper i).trans (Nat.le_of_lt (not_le.mp hq))

theorem twelve_le_primeAt (i : ℕ) : 12 ≤ primeAt i := by
  have h := primeAt_ge i
  omega

/-- The mixed-radix base at level `i`. -/
def radix (i : ℕ) : ℕ := (primeAt i) ^ 2

theorem radix_eq (i : ℕ) : radix i = (primeAt i) ^ 2 := rfl

theorem radix_prime_sq (i : ℕ) : ∃ p : ℕ, Nat.Prime p ∧ radix i = p ^ 2 := by
  exact ⟨primeAt i, primeAt_prime i, rfl⟩

theorem radix_pos (i : ℕ) : 0 < radix i := by
  simp only [radix, pow_two]
  exact Nat.mul_pos (primeAt_prime i).pos (primeAt_prime i).pos

theorem radix_ne_zero (i : ℕ) : radix i ≠ 0 := (radix_pos i).ne'

theorem one_lt_radix (i : ℕ) : 1 < radix i := by
  have hp := twelve_le_primeAt i
  simp only [radix, pow_two]
  nlinarith

theorem radix_lower_index (i : ℕ) : (i + 12) ^ 2 ≤ radix i := by
  exact Nat.pow_le_pow_left (primeAt_ge i) 2

theorem radix_lower_factorial (i : ℕ) : (i + 1) ^ 2 ≤ radix i := by
  apply Nat.pow_le_pow_left
  have h := primeAt_ge i
  omega

theorem one_hundred_twenty_one_le_radix (i : ℕ) : 121 ≤ radix i := by
  calc
    121 = 11 ^ 2 := by norm_num
    _ ≤ radix i := Nat.pow_le_pow_left (by
      have h := primeAt_ge i
      omega) 2

theorem radix_upper (i : ℕ) : radix i ≤ 4 * (i + 11) ^ 2 := by
  calc
    radix i ≤ (2 * (i + 11)) ^ 2 := Nat.pow_le_pow_left (primeAt_upper i) 2
    _ = 4 * (i + 11) ^ 2 := by ring

theorem radix_mono : Monotone radix := by
  intro i j hij
  exact Nat.pow_le_pow_left (primeAt_mono hij) 2

/-- The place value immediately above the first `k` digits. -/
def place (k : ℕ) : ℕ := ∏ i ∈ Finset.range k, radix i

@[simp] theorem place_zero : place 0 = 1 := by
  simp [place]

theorem place_succ (k : ℕ) : place (k + 1) = place k * radix k := by
  simp [place, Finset.prod_range_succ]

theorem place_pos (k : ℕ) : 0 < place k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show k + 1 = Nat.succ k by omega, place_succ]
      exact Nat.mul_pos ih (radix_pos k)

theorem place_ne_zero (k : ℕ) : place k ≠ 0 := (place_pos k).ne'

theorem place_lt_place_succ (k : ℕ) : place k < place (k + 1) := by
  rw [place_succ]
  exact lt_mul_of_one_lt_right (place_pos k) (one_lt_radix k)

theorem place_strictMono : StrictMono place :=
  strictMono_nat_of_lt_succ place_lt_place_succ

theorem place_mono : Monotone place := place_strictMono.monotone

theorem place_dvd_place_succ (k : ℕ) : place k ∣ place (k + 1) := by
  rw [place_succ]
  exact dvd_mul_right _ _

theorem place_dvd_place {i j : ℕ} (hij : i ≤ j) : place i ∣ place j := by
  induction hij with
  | refl => exact dvd_rfl
  | @step j _ ih => exact ih.trans (place_dvd_place_succ j)

theorem pow_radix_lower_le_place (k : ℕ) : 121 ^ k ≤ place k := by
  simp only [place]
  calc
    121 ^ k = ∏ _i ∈ Finset.range k, 121 := by simp
    _ ≤ ∏ i ∈ Finset.range k, radix i := by
      exact Finset.prod_le_prod' fun i _hi ↦ one_hundred_twenty_one_le_radix i

theorem factorial_sq_le_place (k : ℕ) : (Nat.factorial k) ^ 2 ≤ place k := by
  rw [← Finset.prod_range_add_one_eq_factorial]
  rw [← Finset.prod_pow]
  exact Finset.prod_le_prod' fun i _hi ↦ radix_lower_factorial i

/-- The place value grows at least as fast as the superexponential scale used
by the final little-o estimate. -/
theorem half_pow_le_factorial_sq (k : ℕ) : (k / 2) ^ k ≤ (Nat.factorial k) ^ 2 := by
  by_cases hm : k / 2 = 0
  · have hk : k < 2 := by omega
    interval_cases k <;> norm_num
  · have hmpos : 0 < k / 2 := Nat.pos_of_ne_zero hm
    have hmle : k / 2 ≤ k := Nat.div_le_self _ _
    have htail := Nat.factorial_mul_pow_sub_le_factorial hmle
    have hpow : (k / 2) ^ (k - k / 2) ≤ Nat.factorial k :=
      (Nat.le_mul_of_pos_left _ (Nat.factorial_pos (k / 2))).trans htail
    have hexp : k ≤ 2 * (k - k / 2) := by omega
    calc
      (k / 2) ^ k ≤ (k / 2) ^ (2 * (k - k / 2)) :=
        Nat.pow_le_pow_right hmpos hexp
      _ = ((k / 2) ^ (k - k / 2)) ^ 2 := by
        rw [pow_two, ← pow_add]
        congr 1
        omega
      _ ≤ (Nat.factorial k) ^ 2 := Nat.pow_le_pow_left hpow 2

theorem half_pow_le_place (k : ℕ) : (k / 2) ^ k ≤ place k :=
  (half_pow_le_factorial_sq k).trans (factorial_sq_le_place k)

theorem place_upper (k : ℕ) : place k ≤ (4 * (k + 11) ^ 2) ^ k := by
  simp only [place]
  calc
    (∏ i ∈ Finset.range k, radix i) ≤
        ∏ _i ∈ Finset.range k, (4 * (k + 11) ^ 2) := by
      apply Finset.prod_le_prod'
      intro i hi
      refine (radix_upper i).trans ?_
      exact Nat.mul_le_mul_left 4
        (Nat.pow_le_pow_left (by simpa using (Finset.mem_range.mp hi).le : i + 11 ≤ k + 11) 2)
    _ = (4 * (k + 11) ^ 2) ^ k := by simp

theorem index_lt_place_succ (n : ℕ) : n < place (n + 1) := by
  calc
    n < 2 ^ n := n.lt_two_pow_self
    _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ 121 ^ (n + 1) := Nat.pow_le_pow_left (by norm_num) (n + 1)
    _ ≤ place (n + 1) := pow_radix_lower_le_place (n + 1)

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos29/Digital.lean` -/

section
/-!
# Mixed-radix gluing for Erdős Problem 29

This file isolates the digital part of the construction.  A `LocalSystem`
consists of bases and a finite set of permitted digits in every position.
The local hypothesis says that every digit, with either possible incoming
carry, is the sum of two permitted digits with an outgoing carry in `{0,1}`.

The global set has permitted digits below its most significant digit and an
unrestricted most significant digit.  The definitions below use an inductive
description of finite digit strings; in particular they do not rely on a
choice of representatives.
-/



namespace MixedRadix

open scoped Pointwise

/-- Finite local data sufficient for the digital gluing argument. -/
structure LocalSystem where
  base : ℕ → ℕ
  digits : ℕ → Finset ℕ
  two_le_base : ∀ i, 2 ≤ base i
  digit_lt : ∀ i d, d ∈ digits i → d < base i
  carryCover : ∀ i r c, r < base i → c ≤ 1 →
    ∃ x ∈ digits i, ∃ y ∈ digits i, ∃ c' ≤ 1,
      x + y + c = r + base i * c'

/-- Package ordinary modular additive coverage into the carry-aware local
system used by the gluing theorem. -/
def LocalSystem.ofModular (base : ℕ → ℕ) (digits : ℕ → Finset ℕ)
    (hbase : ∀ i, 2 ≤ base i)
    (hdigit : ∀ i d, d ∈ digits i → d < base i)
    (hcover : ∀ i r, r < base i →
      ∃ x ∈ digits i, ∃ y ∈ digits i, (x + y) % base i = r) :
    LocalSystem where
  base := base
  digits := digits
  two_le_base := hbase
  digit_lt := hdigit
  carryCover := by
    intro i r c hr hc
    have hB : 0 < base i := lt_of_lt_of_le Nat.zero_lt_two (hbase i)
    let t := (r + base i - c) % base i
    obtain ⟨x, hx, y, hy, hxy⟩ := hcover i t (Nat.mod_lt _ hB)
    have hcr : c ≤ r + base i := by omega
    have hadd : r + base i - c + c = r + base i := Nat.sub_add_cancel hcr
    have hmod : (x + y + c) % base i = r := by
      have hxy' : Nat.ModEq (base i) (x + y) (r + base i - c) := hxy
      have hradd : Nat.ModEq (base i) (r + base i) r := by
        change (r + base i) % base i = r % base i
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt hr]
      have hxyc : Nat.ModEq (base i) (x + y + c) (r + base i) := by
        rw [← hadd]
        exact hxy'.add_right c
      have hmodEq := hxyc.trans hradd
      exact (show (x + y + c) % base i = r % base i from hmodEq).trans
        (Nat.mod_eq_of_lt hr)
    refine ⟨x, hx, y, hy, (x + y + c) / base i, ?_, ?_⟩
    · have hxlt := hdigit i x hx
      have hylt := hdigit i y hy
      have hsum : x + y + c < 2 * base i := by omega
      have hdiv : (x + y + c) / base i < 2 :=
        (Nat.div_lt_iff_lt_mul hB).2 (by simpa [Nat.mul_comm] using hsum)
      omega
    · calc
        x + y + c = (x + y + c) % base i +
            base i * ((x + y + c) / base i) :=
          (Nat.mod_add_div _ _).symm
        _ = r + base i * ((x + y + c) / base i) := by rw [hmod]

variable (S : LocalSystem)

/-- Place value of position `k`. -/
def place : ℕ → ℕ
  | 0 => 1
  | k + 1 => place k * S.base k

@[simp] theorem place_zero : place S 0 = 1 := rfl

@[simp] theorem place_succ (k : ℕ) :
    place S (k + 1) = place S k * S.base k := rfl

theorem place_pos (k : ℕ) : 0 < place S k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [place_succ]
      exact Nat.mul_pos ih (lt_of_lt_of_le Nat.zero_lt_two (S.two_le_base k))

/-- A number represented by exactly `k` permitted low digits. -/
inductive LowWord : ℕ → ℕ → Prop
  | zero : LowWord 0 0
  | succ {k n d} : LowWord k n → d ∈ S.digits k →
      LowWord (k + 1) (n + d * place S k)

theorem lowWord_lt_place {k n : ℕ} (h : LowWord S k n) : n < place S k := by
  induction h with
  | zero => simp
  | @succ k n d hn hd ih =>
      rw [place_succ]
      have hdlt := S.digit_lt k d hd
      have hp := place_pos S k
      nlinarith

/-- The global mixed-radix set.  The `top` digit is unrestricted. -/
def basis : Set ℕ :=
  {n | ∃ k low top, LowWord S k low ∧ top < S.base k ∧
      n = low + top * place S k}

theorem zero_mem_basis : 0 ∈ basis S := by
  refine ⟨0, 0, 0, LowWord.zero, ?_, by simp⟩
  exact lt_of_lt_of_le Nat.zero_lt_two (S.two_le_base 0)

/-- The largest occupied mixed-radix position.  The search is bounded by `n`;
`place_ge_succ` below shows that this bound loses no positions. -/
def level (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => place S k ≤ n) n

theorem place_ge_succ (k : ℕ) : k + 1 ≤ place S k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [place_succ]
      have hb := S.two_le_base k
      have hp := place_pos S k
      nlinarith

theorem level_le (n : ℕ) : level S n ≤ n :=
  Nat.findGreatest_le n

@[simp] theorem level_zero : level S 0 = 0 := by
  simp [level]

theorem place_dvd_of_le {i k : ℕ} (hik : i ≤ k) :
    place S i ∣ place S k := by
  induction k with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact dvd_rfl
  | succ k ih =>
      by_cases h : i = k + 1
      · subst i
        exact dvd_rfl
      · have hik' : i ≤ k := Nat.le_of_lt_succ (lt_of_le_of_ne hik h)
        exact (ih hik').trans (by simp [place_succ])

theorem place_mono : Monotone (place S) := by
  intro i k hik
  exact Nat.le_of_dvd (place_pos S k) (place_dvd_of_le S hik)

theorem place_level_le {n : ℕ} (hn : 0 < n) :
    place S (level S n) ≤ n := by
  unfold level
  exact Nat.findGreatest_spec (P := fun k => place S k ≤ n)
    (Nat.zero_le n) (by simp only [place_zero]; omega)

theorem lt_place_level_succ {n : ℕ} (hn : 0 < n) :
    n < place S (level S n + 1) := by
  apply Nat.lt_of_not_ge
  intro hplace
  have hkn : level S n + 1 ≤ n :=
    (Nat.le_succ (level S n + 1)).trans
      ((place_ge_succ S (level S n + 1)).trans hplace)
  exact Nat.findGreatest_is_greatest (P := fun k => place S k ≤ n)
    (Nat.lt_succ_self _) hkn hplace

theorem level_mono : Monotone (level S) := by
  intro m n hmn
  by_cases hm : m = 0
  · simp [hm]
  · apply Nat.le_findGreatest
    · exact (level_le S m).trans hmn
    · exact (place_level_le S (Nat.pos_of_ne_zero hm)).trans hmn

theorem lowWord_mod {i k n : ℕ} (hik : i ≤ k) (h : LowWord S k n) :
    LowWord S i (n % place S i) := by
  induction h with
  | zero =>
      have : i = 0 := by omega
      subst i
      simpa using LowWord.zero (S := S)
  | @succ k n d hn hd ih =>
      by_cases hi : i = k + 1
      · subst i
        rw [Nat.mod_eq_of_lt (lowWord_lt_place S (LowWord.succ hn hd))]
        exact LowWord.succ hn hd
      · have hik' : i ≤ k := Nat.le_of_lt_succ (lt_of_le_of_ne hik hi)
        have hdvd : place S i ∣ place S k := place_dvd_of_le S hik'
        have hmod : place S k % place S i = 0 := Nat.mod_eq_zero_of_dvd hdvd
        simpa [Nat.add_mod, Nat.mul_mod, hmod] using ih hik'

theorem basis_lt_place_succ {n k low top : ℕ}
    (hlow : LowWord S k low) (htop : top < S.base k)
    (hn : n = low + top * place S k) : n < place S (k + 1) := by
  rw [hn, place_succ]
  have hl := lowWord_lt_place S hlow
  have hp := place_pos S k
  nlinarith

/-- Membership gives the permitted canonical prefix below `level n`. -/
theorem lowWord_level_of_mem {n : ℕ} (hn : n ∈ basis S) :
    LowWord S (level S n) (n % place S (level S n)) := by
  rcases hn with ⟨k, low, top, hlow, htop, rfl⟩
  by_cases hz : low + top * place S k = 0
  · rw [hz]
    simpa using LowWord.zero (S := S)
  · have hnpos : 0 < low + top * place S k := Nat.pos_of_ne_zero hz
    have hlevel : level S (low + top * place S k) ≤ k := by
      apply Nat.le_of_not_lt
      intro hk
      have hs : k + 1 ≤ level S (low + top * place S k) := hk
      have hplace : place S (k + 1) ≤ low + top * place S k :=
        (place_mono S hs).trans (place_level_le S hnpos)
      exact (Nat.not_le_of_gt (basis_lt_place_succ S hlow htop rfl)) hplace
    have hprefix := lowWord_mod S hlevel hlow
    have hdvd : place S (level S (low + top * place S k)) ∣ place S k :=
      place_dvd_of_le S hlevel
    have hmod : place S k % place S (level S (low + top * place S k)) = 0 :=
      Nat.mod_eq_zero_of_dvd hdvd
    simpa [Nat.add_mod, Nat.mul_mod, hmod] using hprefix

theorem lowWord_prefix_of_mem {i n : ℕ} (hi : i ≤ level S n)
    (hn : n ∈ basis S) : LowWord S i (n % place S i) := by
  have h := lowWord_mod S hi (lowWord_level_of_mem S hn)
  have hdvd : place S i ∣ place S (level S n) := place_dvd_of_le S hi
  simpa [Nat.mod_mod_of_dvd _ hdvd] using h

/-- Coverage of a finite low block, recording its outgoing carry. -/
theorem lower_cover : ∀ k r, r < place S k →
    ∃ a b c, LowWord S k a ∧ LowWord S k b ∧ c ≤ 1 ∧
      a + b = r + c * place S k := by
  intro k
  induction k with
  | zero =>
      intro r hr
      have hr0 : r = 0 := by simpa using hr
      subst r
      exact ⟨0, 0, 0, LowWord.zero, LowWord.zero, by simp, by simp⟩
  | succ k ih =>
      intro r hr
      have hP : 0 < place S k := place_pos S k
      have hr0 : r % place S k < place S k := Nat.mod_lt r hP
      obtain ⟨a, b, c, ha, hb, hc, hab⟩ := ih (r % place S k) hr0
      have hq : r / place S k < S.base k := by
        apply (Nat.div_lt_iff_lt_mul hP).2
        simpa [place_succ, Nat.mul_comm] using hr
      obtain ⟨x, hx, y, hy, c', hc', hxy⟩ :=
        S.carryCover k (r / place S k) c hq hc
      refine ⟨a + x * place S k, b + y * place S k, c', ?_, ?_, hc', ?_⟩
      · exact LowWord.succ ha hx
      · exact LowWord.succ hb hy
      · calc
          (a + x * place S k) + (b + y * place S k) =
              (a + b) + (x + y) * place S k := by ring
          _ = (r % place S k + c * place S k) +
              (x + y) * place S k := by rw [hab]
          _ = r % place S k + (x + y + c) * place S k := by ring
          _ = r % place S k +
              (r / place S k + S.base k * c') * place S k := by rw [hxy]
          _ = (r % place S k + place S k * (r / place S k)) +
              c' * (place S k * S.base k) := by ring
          _ = r + c' * place S (k + 1) := by
            rw [Nat.mod_add_div, place_succ]

/-- Every natural number is a sum of two members of the mixed-radix set. -/
theorem basis_add_basis : basis S + basis S = Set.univ := by
  apply Set.eq_univ_of_forall
  intro n
  rw [Set.mem_add]
  by_cases hn : n = 0
  · subst n
    exact ⟨0, zero_mem_basis S, 0, zero_mem_basis S, by simp⟩
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let k := level S n
    let P := place S k
    let B := S.base k
    have hPle : P ≤ n := by simpa [P, k] using place_level_le S hnpos
    have hnlt : n < P * B := by
      simpa [P, B, k, place_succ] using lt_place_level_succ S hnpos
    have hqpos : 0 < n / P := Nat.div_pos hPle (place_pos S k)
    have hqlt : n / P < B := by
      apply (Nat.div_lt_iff_lt_mul (place_pos S k)).2
      simpa [P, B, Nat.mul_comm] using hnlt
    obtain ⟨a, b, c, ha, hb, hc, hab⟩ :=
      lower_cover S k (n % P) (Nat.mod_lt _ (place_pos S k))
    have hcq : c ≤ n / P := hc.trans hqpos
    let u := n / P - c
    have hult : u < B := lt_of_le_of_lt (Nat.sub_le _ _) hqlt
    have hzeroB : 0 < B := lt_of_lt_of_le Nat.zero_lt_two (S.two_le_base k)
    refine ⟨a + u * P, ?_, b, ?_, ?_⟩
    · exact ⟨k, a, u, ha, hult, rfl⟩
    · exact ⟨k, b, 0, hb, hzeroB, by simp⟩
    · have hsub : u + c = n / P := Nat.sub_add_cancel hcq
      calc
        a + u * P + b = (a + b) + u * P := by ring
        _ = (n % P + c * P) + u * P := by rw [hab]
        _ = n % P + (u + c) * P := by ring
        _ = n % P + (n / P) * P := by rw [hsub]
        _ = n := by rw [Nat.mul_comm, Nat.mod_add_div]

/-! ## Counting representations -/

/-- The finite set of all permitted words of length `k`. -/
def lowWords : ℕ → Finset ℕ
  | 0 => {0}
  | k + 1 => (S.digits k).biUnion fun d =>
      (lowWords k).image fun n => n + d * place S k

@[simp] theorem mem_lowWords_iff {k n : ℕ} :
    n ∈ lowWords S k ↔ LowWord S k n := by
  constructor
  · intro hn
    induction k generalizing n with
    | zero =>
        simp only [lowWords, Finset.mem_singleton] at hn
        subst n
        exact LowWord.zero
    | succ k ih =>
        simp only [lowWords, Finset.mem_biUnion, Finset.mem_image] at hn
        obtain ⟨d, hd, a, ha, rfl⟩ := hn
        exact LowWord.succ (ih ha) hd
  · intro hn
    induction hn with
    | zero => simp [lowWords]
    | @succ k n d hn hd ih =>
        simp only [lowWords, Finset.mem_biUnion, Finset.mem_image]
        exact ⟨d, hd, n, ih, rfl⟩

/-- Ordered permitted low-word pairs which have the prescribed sum modulo
the first `k` bases. -/
def prefixPairs (k r : ℕ) : Finset (ℕ × ℕ) :=
  ((lowWords S k).product (lowWords S k)).filter fun ab =>
    (ab.1 + ab.2) % place S k = r % place S k

/-- Number of ordered representations supplied by the first `k` digits. -/
def prefixRepCount (k r : ℕ) : ℕ := (prefixPairs S k r).card

/-- Ordered local digit pairs with a prescribed residue. -/
def localPairs (i r : ℕ) : Finset (ℕ × ℕ) :=
  ((S.digits i).product (S.digits i)).filter fun xy =>
    (xy.1 + xy.2) % S.base i = r % S.base i

/-- The same local fiber with an incoming carry. -/
def localCarryPairs (i r c : ℕ) : Finset (ℕ × ℕ) :=
  ((S.digits i).product (S.digits i)).filter fun xy =>
    (xy.1 + xy.2 + c) % S.base i = r % S.base i

theorem localCarryPairs_card_le_of_flat {M : ℕ}
    (hflat : ∀ i r, (localPairs S i r).card ≤ M)
    (i r c : ℕ) (hc : c ≤ 1) :
    (localCarryPairs S i r c).card ≤ M := by
  have hbase := S.two_le_base i
  have hcr : c ≤ r + S.base i := by omega
  have hadd : r + S.base i - c + c = r + S.base i := Nat.sub_add_cancel hcr
  have heq : localCarryPairs S i r c =
      localPairs S i (r + S.base i - c) := by
    ext xy
    simp only [localCarryPairs, localPairs, Finset.mem_filter, Finset.mem_product]
    apply and_congr_right
    intro _
    change Nat.ModEq (S.base i) (xy.1 + xy.2 + c) r ↔
      Nat.ModEq (S.base i) (xy.1 + xy.2) (r + S.base i - c)
    have hradd : Nat.ModEq (S.base i) (r + S.base i) r := by
      change (r + S.base i) % S.base i = r % S.base i
      simp
    constructor
    · intro h
      apply Nat.ModEq.add_right_cancel' c
      exact h.trans (by simpa [hadd] using hradd.symm)
    · intro h
      exact h.add_right c |>.trans (by simpa [hadd] using hradd)
  rw [heq]
  exact hflat i (r + S.base i - c)

theorem lowWord_succ_split {k n : ℕ} (h : LowWord S (k + 1) n) :
    LowWord S k (n % place S k) ∧ n / place S k ∈ S.digits k := by
  cases h with
  | @succ _ low d hlow hd =>
      have hlt := lowWord_lt_place S hlow
      have hp := place_pos S k
      constructor
      · simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hlt] using hlow
      · have heq : (low + d * place S k) / place S k = d := by
          rw [Nat.mul_comm d, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hlt,
            zero_add]
        simpa [heq] using hd

private theorem add_div_eq_div_add_carry (a b P : ℕ) (hP : 0 < P) :
    (a + b) / P = a / P + b / P + (a % P + b % P) / P := by
  rw [Nat.add_div hP]
  by_cases h : P ≤ a % P + b % P
  · have ha := Nat.mod_lt a hP
    have hb := Nat.mod_lt b hP
    have hlt : a % P + b % P < (1 + 1) * P := by omega
    have hdiv : (a % P + b % P) / P = 1 :=
      Nat.div_eq_of_lt_le (by simpa using h) hlt
    simp [h, hdiv]
  · have hlt : a % P + b % P < P := Nat.lt_of_not_ge h
    have hdiv : (a % P + b % P) / P = 0 := Nat.div_eq_of_lt hlt
    simp [h, hdiv]

/-- A finite superset of the length-`k+1` prefix pairs, obtained by extending
each length-`k` pair by one local carry fiber. -/
def prefixExtensions (k r : ℕ) : Finset (ℕ × ℕ) :=
  (prefixPairs S k r).biUnion fun low =>
    (localCarryPairs S k (r / place S k)
      ((low.1 + low.2) / place S k)).image fun top =>
        (low.1 + top.1 * place S k, low.2 + top.2 * place S k)

theorem prefixPairs_succ_subset_extensions (k r : ℕ) :
    prefixPairs S (k + 1) r ⊆ prefixExtensions S k r := by
  intro ab hab
  rw [prefixPairs, Finset.mem_filter] at hab
  rcases hab with ⟨habWords, habMod⟩
  have habWords' := Finset.mem_product.mp habWords
  have haSplit := lowWord_succ_split S ((mem_lowWords_iff (S := S)).1 habWords'.1)
  have hbSplit := lowWord_succ_split S ((mem_lowWords_iff (S := S)).1 habWords'.2)
  let low : ℕ × ℕ := (ab.1 % place S k, ab.2 % place S k)
  let top : ℕ × ℕ := (ab.1 / place S k, ab.2 / place S k)
  have hlow : low ∈ prefixPairs S k r := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (mem_lowWords_iff (S := S)).2 haSplit.1
    · exact (mem_lowWords_iff (S := S)).2 hbSplit.1
    · have hdvd : place S k ∣ place S (k + 1) := by simp [place_succ]
      have := congrArg (fun z => z % place S k) habMod
      simpa [low, Nat.add_mod, Nat.mod_mod_of_dvd _ hdvd] using this
  have htop : top ∈ localCarryPairs S k (r / place S k)
      ((low.1 + low.2) / place S k) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨haSplit.2, hbSplit.2⟩, ?_⟩
    have hquot := congrArg (fun z => z / place S k) habMod
    have hP := place_pos S k
    have hadd := add_div_eq_div_add_carry ab.1 ab.2 (place S k) hP
    rw [place_succ, Nat.mul_comm] at hquot
    rw [Nat.mod_mul_left_div_self, Nat.mod_mul_left_div_self] at hquot
    simpa [top, low, hadd] using hquot
  apply Finset.mem_biUnion.mpr
  refine ⟨low, hlow, Finset.mem_image.mpr ⟨top, htop, ?_⟩⟩
  apply Prod.ext <;> simp only [top, low]
  · simpa [Nat.mul_comm] using Nat.mod_add_div ab.1 (place S k)
  · simpa [Nat.mul_comm] using Nat.mod_add_div ab.2 (place S k)

theorem prefixExtensions_card_le {M : ℕ}
    (hflat : ∀ i r, (localPairs S i r).card ≤ M) (k r : ℕ) :
    (prefixExtensions S k r).card ≤ prefixRepCount S k r * M := by
  classical
  calc
    (prefixExtensions S k r).card ≤
        ∑ low ∈ prefixPairs S k r,
          ((localCarryPairs S k (r / place S k)
            ((low.1 + low.2) / place S k)).image fun top =>
              (low.1 + top.1 * place S k,
                low.2 + top.2 * place S k)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _low ∈ prefixPairs S k r, M := by
      apply Finset.sum_le_sum
      intro low hlow
      apply Finset.card_image_le.trans
      apply localCarryPairs_card_le_of_flat S hflat
      rw [prefixPairs, Finset.mem_filter] at hlow
      have hpairs := Finset.mem_product.mp hlow.1
      have hlow1 := lowWord_lt_place S ((mem_lowWords_iff (S := S)).1 hpairs.1)
      have hlow2 := lowWord_lt_place S ((mem_lowWords_iff (S := S)).1 hpairs.2)
      have hP := place_pos S k
      have hsum : low.1 + low.2 < 2 * place S k := by omega
      have hdiv : (low.1 + low.2) / place S k < 2 :=
        (Nat.div_lt_iff_lt_mul hP).2 (by simpa [Nat.mul_comm] using hsum)
      omega
    _ = prefixRepCount S k r * M := by simp [prefixRepCount]

/-- Uniform flatness of every local ordered sum fiber multiplies across the
mixed-radix prefix. -/
theorem prefixRepCount_le_pow {M : ℕ}
    (hflat : ∀ i r, (localPairs S i r).card ≤ M) :
    ∀ k r, prefixRepCount S k r ≤ M ^ k := by
  intro k
  induction k with
  | zero =>
      intro r
      have hcard := Finset.card_filter_le
        ({(0, 0)} : Finset (ℕ × ℕ))
        (fun ab : ℕ × ℕ => (ab.1 + ab.2) % 1 = r % 1)
      simpa [prefixRepCount, prefixPairs, lowWords, place] using hcard
  | succ k ih =>
      intro r
      calc
        prefixRepCount S (k + 1) r ≤ (prefixExtensions S k r).card :=
          Finset.card_le_card (prefixPairs_succ_subset_extensions S k r)
        _ ≤ prefixRepCount S k r * M := prefixExtensions_card_le S hflat k r
        _ ≤ M ^ k * M := Nat.mul_le_mul_right M (ih r)
        _ = M ^ (k + 1) := by rw [pow_succ]

/-- The ordered convolution of the global set. -/
noncomputable def basisRepFinset (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.HasAntidiagonal.antidiagonal
    (self := Finset.Nat.instHasAntidiagonal) n : Finset (ℕ × ℕ)).filter fun ab =>
    ab.1 ∈ basis S ∧ ab.2 ∈ basis S

noncomputable def basisRepCount (n : ℕ) : ℕ := (basisRepFinset S n).card

theorem div_place_level_lt_base (n : ℕ) :
    n / place S (level S n) < S.base (level S n) := by
  by_cases hn : n = 0
  · subst n
    simp only [level_zero, Nat.zero_div]
    exact lt_of_lt_of_le Nat.zero_lt_two (S.two_le_base 0)
  · apply (Nat.div_lt_iff_lt_mul (place_pos S (level S n))).2
    simpa [place_succ, Nat.mul_comm] using lt_place_level_succ S (Nat.pos_of_ne_zero hn)

/-- A code for an oriented representation. -/
structure RepCode where
  level : ℕ
  lowSmall : ℕ
  lowLarge : ℕ
  topSmall : ℕ
  deriving DecidableEq

/-- Codes allowed at one possible level of the smaller summand. -/
def codesAt (n l : ℕ) : Finset RepCode :=
  ((prefixPairs S l n).product (Finset.range (S.base l))).image fun p =>
    { level := l, lowSmall := p.1.1, lowLarge := p.1.2, topSmall := p.2 }

/-- All oriented codes which can occur in a representation of `n`. -/
def codeSpace (n : ℕ) : Finset (Bool × RepCode) :=
  Finset.univ.product <| (Finset.range (level S n + 1)).biUnion (codesAt S n)

/-- The code remembers which summand was smaller, its level, both low
prefixes, and the top digit of the smaller summand. -/
def repCode (ab : ℕ × ℕ) : Bool × RepCode :=
  if ab.1 ≤ ab.2 then
    (false, ⟨level S ab.1,
      ab.1 % place S (level S ab.1),
      ab.2 % place S (level S ab.1),
      ab.1 / place S (level S ab.1)⟩)
  else
    (true, ⟨level S ab.2,
      ab.2 % place S (level S ab.2),
      ab.1 % place S (level S ab.2),
      ab.2 / place S (level S ab.2)⟩)

/-- The natural digital upper bound before inserting a uniform local bound. -/
def digitalBound (n : ℕ) : ℕ :=
  2 * ∑ l ∈ Finset.range (level S n + 1),
    S.base l * prefixRepCount S l n

theorem repCode_mem_codeSpace {n : ℕ × ℕ} {N : ℕ}
    (hn : n ∈ basisRepFinset S N) : repCode S n ∈ codeSpace S N := by
  classical
  rw [basisRepFinset, Finset.mem_filter] at hn
  have hsum : n.1 + n.2 = N := Finset.HasAntidiagonal.mem_antidiagonal.mp hn.1
  have hn1 : n.1 ∈ basis S := hn.2.1
  have hn2 : n.2 ∈ basis S := hn.2.2
  by_cases hle : n.1 ≤ n.2
  · rw [repCode, if_pos hle]
    unfold codeSpace
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨level S n.1, ?_, ?_⟩
    · apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le <| level_mono S (by omega)
    · apply Finset.mem_image.mpr
      refine ⟨((n.1 % place S (level S n.1),
        n.2 % place S (level S n.1)),
        n.1 / place S (level S n.1)), ?_, rfl⟩
      apply Finset.mem_product.mpr
      constructor
      · change (n.1 % place S (level S n.1),
          n.2 % place S (level S n.1)) ∈ prefixPairs S (level S n.1) N
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
        · simpa using lowWord_level_of_mem S hn1
        · simpa using lowWord_prefix_of_mem S (level_mono S hle) hn2
        · rw [← Nat.add_mod, hsum]
      · exact Finset.mem_range.mpr (div_place_level_lt_base S n.1)
  · have hle' : n.2 ≤ n.1 := Nat.le_of_not_ge hle
    rw [repCode, if_neg hle]
    unfold codeSpace
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨level S n.2, ?_, ?_⟩
    · apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le <| level_mono S (by omega)
    · apply Finset.mem_image.mpr
      refine ⟨((n.2 % place S (level S n.2),
        n.1 % place S (level S n.2)),
        n.2 / place S (level S n.2)), ?_, rfl⟩
      apply Finset.mem_product.mpr
      constructor
      · change (n.2 % place S (level S n.2),
          n.1 % place S (level S n.2)) ∈ prefixPairs S (level S n.2) N
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
        · simpa using lowWord_level_of_mem S hn2
        · simpa using lowWord_prefix_of_mem S (level_mono S hle') hn1
        · rw [Nat.add_comm, ← Nat.add_mod, hsum]
      · exact Finset.mem_range.mpr (div_place_level_lt_base S n.2)

private theorem eq_of_level_mod_div_eq {a b : ℕ}
    (hl : level S a = level S b)
    (hm : a % place S (level S a) = b % place S (level S b))
    (hd : a / place S (level S a) = b / place S (level S b)) : a = b := by
  calc
    a = a % place S (level S a) +
        place S (level S a) * (a / place S (level S a)) :=
      (Nat.mod_add_div _ _).symm
    _ = b % place S (level S b) +
        place S (level S b) * (b / place S (level S b)) := by
      rw [hl] at hm hd ⊢
      rw [hm, hd]
    _ = b := Nat.mod_add_div _ _

theorem repCode_injOn (N : ℕ) :
    Set.InjOn (repCode S) (basisRepFinset S N) := by
  classical
  intro a ha b hb hcode
  change a ∈ basisRepFinset S N at ha
  change b ∈ basisRepFinset S N at hb
  rw [basisRepFinset, Finset.mem_filter] at ha hb
  have haSum : a.1 + a.2 = N := Finset.HasAntidiagonal.mem_antidiagonal.mp ha.1
  have hbSum : b.1 + b.2 = N := Finset.HasAntidiagonal.mem_antidiagonal.mp hb.1
  by_cases haLe : a.1 ≤ a.2 <;> by_cases hbLe : b.1 ≤ b.2
  · rw [repCode, if_pos haLe, repCode, if_pos hbLe] at hcode
    have hp := congrArg Prod.snd hcode
    have hl := congrArg RepCode.level hp
    have hm := congrArg RepCode.lowSmall hp
    have hd := congrArg RepCode.topSmall hp
    have hfirst : a.1 = b.1 := eq_of_level_mod_div_eq S hl hm hd
    apply Prod.ext hfirst
    omega
  · rw [repCode, if_pos haLe, repCode, if_neg hbLe] at hcode
    simp at hcode
  · rw [repCode, if_neg haLe, repCode, if_pos hbLe] at hcode
    simp at hcode
  · rw [repCode, if_neg haLe, repCode, if_neg hbLe] at hcode
    have hp := congrArg Prod.snd hcode
    have hl := congrArg RepCode.level hp
    have hm := congrArg RepCode.lowSmall hp
    have hd := congrArg RepCode.topSmall hp
    have hsecond : a.2 = b.2 := eq_of_level_mod_div_eq S hl hm hd
    apply Prod.ext
    · omega
    · exact hsecond

theorem basisRepCount_le_codeSpace (N : ℕ) :
    basisRepCount S N ≤ (codeSpace S N).card := by
  classical
  unfold basisRepCount
  exact Finset.card_le_card_of_injOn (repCode S)
    (fun _ hn => repCode_mem_codeSpace S hn) (repCode_injOn S N)

theorem codeSpace_card_le_digitalBound (N : ℕ) :
    (codeSpace S N).card ≤ digitalBound S N := by
  classical
  let U := (Finset.range (level S N + 1)).biUnion (codesAt S N)
  calc
    (codeSpace S N).card = 2 * U.card := by
      unfold codeSpace U
      simpa using Finset.card_product (Finset.univ : Finset Bool)
        ((Finset.range (level S N + 1)).biUnion (codesAt S N))
    _ ≤ 2 * ∑ l ∈ Finset.range (level S N + 1),
          S.base l * prefixRepCount S l N := by
      apply Nat.mul_le_mul_left 2
      refine Finset.card_biUnion_le.trans ?_
      apply Finset.sum_le_sum
      intro l hl
      calc
        (codesAt S N l).card ≤
            ((prefixPairs S l N).product (Finset.range (S.base l))).card :=
          Finset.card_image_le
        _ = prefixRepCount S l N * S.base l := by
          simp [prefixRepCount, Finset.card_product]
        _ = S.base l * prefixRepCount S l N := Nat.mul_comm _ _
    _ = digitalBound S N := rfl

/-- The ordered global convolution is controlled by the product of the local
prefix counts, with one unrestricted top digit and two orientations. -/
theorem basisRepCount_le_digitalBound (N : ℕ) :
    basisRepCount S N ≤ digitalBound S N :=
  (basisRepCount_le_codeSpace S N).trans (codeSpace_card_le_digitalBound S N)

/-- A convenient form for applications: once a separate local-to-prefix
argument gives `M^k`, the global count is bounded by the displayed sum. -/
theorem basisRepCount_le_of_prefix_bound (M N : ℕ)
    (hprefix : ∀ k r, prefixRepCount S k r ≤ M ^ k) :
    basisRepCount S N ≤
      2 * ∑ l ∈ Finset.range (level S N + 1), S.base l * M ^ l := by
  apply (basisRepCount_le_digitalBound S N).trans
  rw [digitalBound]
  gcongr with l hl
  exact hprefix l N

/-- Fully local version of the global counting theorem. -/
theorem basisRepCount_le_of_local_flat (M N : ℕ)
    (hflat : ∀ i r, (localPairs S i r).card ≤ M) :
    basisRepCount S N ≤
      2 * ∑ l ∈ Finset.range (level S N + 1), S.base l * M ^ l :=
  basisRepCount_le_of_prefix_bound S M N (prefixRepCount_le_pow S hflat)

/-- If bases up to the active level have a common upper bound, the sum in the
preceding theorem has the standard polynomial-times-exponential form. -/
theorem basisRepCount_le_uniform (M Q N : ℕ) (hM : 1 ≤ M)
    (hflat : ∀ i r, (localPairs S i r).card ≤ M)
    (hbase : ∀ i ≤ level S N, S.base i ≤ Q) :
    basisRepCount S N ≤
      2 * (level S N + 1) * Q * M ^ level S N := by
  apply (basisRepCount_le_of_local_flat S M N hflat).trans
  calc
    2 * ∑ l ∈ Finset.range (level S N + 1), S.base l * M ^ l ≤
        2 * ∑ _l ∈ Finset.range (level S N + 1),
          Q * M ^ level S N := by
      gcongr with l hl
      · exact hbase l (Nat.le_of_lt_succ (Finset.mem_range.mp hl))
      · exact Nat.le_of_lt_succ (Finset.mem_range.mp hl)
    _ = 2 * (level S N + 1) * Q * M ^ level S N := by
      simp [mul_assoc]

theorem tendsto_level : Filter.Tendsto (level S) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro k
  refine ⟨place S k, ?_⟩
  intro n hn
  apply Nat.le_findGreatest
  · exact (Nat.le_succ k).trans ((place_ge_succ S k).trans hn)
  · exact hn

end MixedRadix

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos29/Analytic.lean` -/

section
/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-!
# Analytic estimates for Erdős Problem 29

The mixed-radix construction used for Problem 29 has two elementary
asymptotic features.  At digit level `k`, its representation count is bounded
by a polynomial in `k` times a fixed exponential `M ^ k`.  On the other hand,
the place value below an integer of level `k` is at least
`(k / 2) ^ k`.  This file isolates the resulting analytic implication: the
representation count is smaller than every positive real power of the
integer.

The lemmas are stated for an arbitrary level map and arbitrary real-valued
function, so the combinatorial files need only supply the indicated pointwise
bounds.
-/

open Filter Topology

namespace Analytic

open scoped NNReal

/-! ## Polynomial times exponential growth along a level map -/

/-- A polynomial times a fixed exponential remains little-o of every strictly
larger exponential after composition with a level map tending to infinity. -/
theorem levelPolynomialExponential_isLittleO
    (level : ℕ → ℕ) (hlevel : Tendsto level atTop atTop)
    (d : ℕ) (C M R : ℝ) (hMR : |M| < R) :
    (fun n : ℕ ↦ C * (level n : ℝ) ^ d * M ^ level n) =o[atTop]
      (fun n : ℕ ↦ R ^ level n) := by
  have hR : 0 < R := (abs_nonneg M).trans_lt hMR
  have hratio : |M / R| < 1 := by
    rw [abs_div, abs_of_pos hR]
    exact (div_lt_one hR).2 hMR
  have hzero :
      Tendsto (fun k : ℕ ↦ (k : ℝ) ^ d * (M / R) ^ k) atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one d hratio
  have hbase :
      (fun k : ℕ ↦ C * (k : ℝ) ^ d * M ^ k) =o[atTop]
        (fun k : ℕ ↦ R ^ k) := by
    have hzeroC :
        Tendsto (fun k : ℕ ↦ C * ((k : ℝ) ^ d * (M / R) ^ k)) atTop (nhds 0) := by
      simpa using hzero.const_mul C
    rw [Asymptotics.isLittleO_iff_tendsto']
    · convert hzeroC using 1
      ext k
      rw [div_pow]
      ring
    · filter_upwards [] with k hk
      exact False.elim ((pow_ne_zero k hR.ne') hk)
  change
    ((fun k : ℕ ↦ C * (k : ℝ) ^ d * M ^ k) ∘ level) =o[atTop]
      ((fun k : ℕ ↦ R ^ k) ∘ level)
  exact hbase.comp_tendsto hlevel

/-- Transfer the preceding estimate through an eventual upper bound for the
function and an eventual lower bound for the target scale. -/
theorem isLittleO_of_levelExponential_bounds
    (f g : ℕ → ℝ) (level : ℕ → ℕ)
    (hlevel : Tendsto level atTop atTop)
    (d : ℕ) (C M R : ℝ)
    (_hC : 0 ≤ C) (hM : 0 ≤ M) (hR : 0 ≤ R) (hMR : M < R)
    (hf : ∀ᶠ n in atTop,
      |f n| ≤ C * (level n : ℝ) ^ d * M ^ level n)
    (hg : ∀ᶠ n in atTop, R ^ level n ≤ |g n|) :
    f =o[atTop] g := by
  have hMabs : |M| < R := by simpa [abs_of_nonneg hM] using hMR
  have hpoly :
      (fun n : ℕ ↦ C * (level n : ℝ) ^ d * M ^ level n) =o[atTop]
        (fun n : ℕ ↦ R ^ level n) :=
    levelPolynomialExponential_isLittleO level hlevel d C M R hMabs
  have hfO :
      f =O[atTop] (fun n : ℕ ↦ C * (level n : ℝ) ^ d * M ^ level n) := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    filter_upwards [hf] with n hn
    simpa [Real.norm_eq_abs] using hn
  have hgO : (fun n : ℕ ↦ R ^ level n) =O[atTop] g := by
    apply Asymptotics.IsBigO.of_bound'
    filter_upwards [hg] with n hn
    simpa [Real.norm_eq_abs, abs_pow, abs_of_nonneg hR] using hn
  exact (hfO.trans_isLittleO hpoly).trans_isBigO hgO

/-! ## Superexponential place values dominate every fixed exponential -/

/-- Division by two still tends to infinity along every natural-valued map
tending to infinity. -/
theorem tendsto_level_div_two_atTop
    (level : ℕ → ℕ) (hlevel : Tendsto level atTop atTop) :
    Tendsto (fun n ↦ level n / 2) atTop atTop := by
  have hdiv : Tendsto (fun k : ℕ ↦ k / 2) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨2 * b, ?_⟩
    intro a ha
    omega
  exact hdiv.comp hlevel

/-- If `n` dominates `(level n / 2) ^ level n`, then every fixed exponential
in the level is eventually bounded by `n ^ ε` for each `ε > 0`.

The exponent on the right is real (`Real.rpow`), as required by the exact
statement of Problem 29. -/
theorem eventually_constPowLevel_le_rpow_of_superexponential
    (level : ℕ → ℕ) (hlevel : Tendsto level atTop atTop)
    (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε)
    (hgrowth : ∀ᶠ n in atTop, (level n / 2) ^ level n ≤ n) :
    ∀ᶠ n in atTop, (2 * M) ^ level n ≤ (n : ℝ) ^ ε := by
  let B : ℝ := (2 * M) ^ ε⁻¹
  have hB0 : 0 ≤ B := Real.rpow_nonneg (mul_nonneg (by norm_num) hM) _
  have hcastDiv :
      Tendsto (fun n ↦ ((level n / 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_level_div_two_atTop level hlevel)
  have hB : ∀ᶠ n in atTop, B ≤ ((level n / 2 : ℕ) : ℝ) :=
    hcastDiv.eventually_ge_atTop B
  filter_upwards [hB, hgrowth] with n hnB hnGrowth
  let q : ℕ := level n / 2
  have hbase : 2 * M ≤ (q : ℝ) ^ ε := by
    calc
      2 * M = B ^ ε := by
        symm
        simpa only [B] using
          (Real.rpow_inv_rpow (mul_nonneg (by norm_num) hM) hε.ne')
      _ ≤ (q : ℝ) ^ ε := Real.rpow_le_rpow hB0 hnB hε.le
  calc
    (2 * M) ^ level n ≤ ((q : ℝ) ^ ε) ^ level n := by
      gcongr
    _ = (((q ^ level n : ℕ) : ℝ) ^ ε) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg q), mul_comm,
        Real.rpow_natCast_mul (Nat.cast_nonneg q), Nat.cast_pow]
    _ ≤ (n : ℝ) ^ ε := by
      apply Real.rpow_le_rpow (by positivity) _ hε.le
      exact_mod_cast hnGrowth

/-! ## End-to-end little-o criterion -/

/-- A convenient end-to-end criterion for the mixed-radix construction.

The three substantive hypotheses are precisely the outputs expected from the
digital part of the proof:

* the level tends to infinity;
* the integer at that level is at least `(level / 2) ^ level`;
* the representation count is bounded by `C * level ^ d * M ^ level`.

The conclusion is the exact real-valued little-o assertion used in Problem 29.
-/
theorem isLittleO_rpow_of_level_superexponential
    (f : ℕ → ℝ) (level : ℕ → ℕ)
    (d : ℕ) (C M ε : ℝ)
    (hC : 0 ≤ C) (hM : 0 < M) (hε : 0 < ε)
    (hlevel : Tendsto level atTop atTop)
    (hgrowth : ∀ᶠ n in atTop, (level n / 2) ^ level n ≤ n)
    (hf : ∀ᶠ n in atTop,
      |f n| ≤ C * (level n : ℝ) ^ d * M ^ level n) :
    f =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ ε) := by
  apply isLittleO_of_levelExponential_bounds
      f (fun n : ℕ ↦ (n : ℝ) ^ ε) level hlevel d C M (2 * M)
      hC hM.le (mul_nonneg (by norm_num) hM.le) (by linarith)
      hf
  simpa [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using
    eventually_constPowLevel_le_rpow_of_superexponential
    level hlevel M ε hM.le hε hgrowth

end Analytic

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos29/Assembly.lean` -/

section
/-!
# Assembly of the mixed-radix construction for Erdős Problem 29

This file is the interface between the three reusable parts of the proof.
The radices and their growth come from `Schedule`, the carry and counting
arguments come from `Digital`, and the final limiting argument comes from
`Analytic`.

The only data still left abstract are the finite permitted digit sets.  The
main theorem below assumes exactly the two properties supplied by the local
modular construction:

* exact coverage with an incoming and outgoing binary carry;
* a uniform bound on every ordered local sum fiber.
-/



namespace Assembly

open Filter
open scoped Pointwise

/-- The actual number of ordered permitted digit pairs in a given residue
class.  This is the local convolution used in the assembly theorem. -/
def localRepCount (digits : ℕ → Finset ℕ) (i r : ℕ) : ℕ :=
  (((digits i).product (digits i)).filter fun xy ↦
    (xy.1 + xy.2) % radix i = r % radix i).card

/-- Install permitted digit sets in the explicit prime-square radix schedule.
The coverage hypothesis is the exact natural-representative form of modular
coverage; `LocalSystem.ofModular` performs the binary-carry bookkeeping. -/
def scheduleSystem (digits : ℕ → Finset ℕ)
    (hdigit : ∀ i d, d ∈ digits i → d < radix i)
    (hcover : ∀ i r, r < radix i →
      ∃ x ∈ digits i, ∃ y ∈ digits i, (x + y) % radix i = r) :
    MixedRadix.LocalSystem :=
  MixedRadix.LocalSystem.ofModular radix digits
    (fun i ↦ by
      have h := one_hundred_twenty_one_le_radix i
      omega)
    hdigit hcover

/-- The recursive place function of the generic digital construction agrees
with the product place function of the explicit schedule. -/
theorem scheduleSystem_place (digits : ℕ → Finset ℕ)
    (hdigit : ∀ i d, d ∈ digits i → d < radix i)
    (hcover : ∀ i r, r < radix i →
      ∃ x ∈ digits i, ∃ y ∈ digits i, (x + y) % radix i = r) :
    ∀ k, MixedRadix.place (scheduleSystem digits hdigit hcover) k = place k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [MixedRadix.place_succ, place_succ, ih]
      rfl

/-- The level selected by the scheduled mixed-radix system tends to infinity. -/
theorem scheduleSystem_level_tendsto (digits : ℕ → Finset ℕ)
    (hdigit : ∀ i d, d ∈ digits i → d < radix i)
    (hcover : ∀ i r, r < radix i →
      ∃ x ∈ digits i, ∃ y ∈ digits i, (x + y) % radix i = r) :
    Tendsto (MixedRadix.level (scheduleSystem digits hdigit hcover)) atTop atTop :=
  MixedRadix.tendsto_level (scheduleSystem digits hdigit hcover)

/-- An integer dominates the superexponential scale associated with its
active scheduled level. -/
theorem scheduleSystem_eventually_superexponential
    (digits : ℕ → Finset ℕ)
    (hdigit : ∀ i d, d ∈ digits i → d < radix i)
    (hcover : ∀ i r, r < radix i →
      ∃ x ∈ digits i, ∃ y ∈ digits i, (x + y) % radix i = r) :
    ∀ᶠ n in atTop,
      (MixedRadix.level (scheduleSystem digits hdigit hcover) n / 2) ^
          MixedRadix.level (scheduleSystem digits hdigit hcover) n ≤ n := by
  let S := scheduleSystem digits hdigit hcover
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0 < n := by omega
  let k := MixedRadix.level S n
  calc
    (k / 2) ^ k ≤ place k := half_pow_le_place k
    _ = MixedRadix.place S k := (scheduleSystem_place digits hdigit hcover k).symm
    _ ≤ n := MixedRadix.place_level_le S hnpos

/-- The explicit schedule turns a uniform local fiber bound into the concrete
global estimate `2304 * k^3 * M^k`. -/
theorem scheduleSystem_basisRepCount_le
    (digits : ℕ → Finset ℕ)
    (hdigit : ∀ i d, d ∈ digits i → d < radix i)
    (hcover : ∀ i r, r < radix i →
      ∃ x ∈ digits i, ∃ y ∈ digits i, (x + y) % radix i = r)
    (M : ℕ) (hM : 1 ≤ M)
    (hflat : ∀ i r, localRepCount digits i r ≤ M)
    (N : ℕ) (hlevel : 1 ≤ MixedRadix.level (scheduleSystem digits hdigit hcover) N) :
    MixedRadix.basisRepCount (scheduleSystem digits hdigit hcover) N ≤
      2304 * MixedRadix.level (scheduleSystem digits hdigit hcover) N ^ 3 *
        M ^ MixedRadix.level (scheduleSystem digits hdigit hcover) N := by
  let S := scheduleSystem digits hdigit hcover
  let k := MixedRadix.level S N
  have hflatS : ∀ i r, (MixedRadix.localPairs S i r).card ≤ M := by
    intro i r
    change localRepCount digits i r ≤ M
    exact hflat i r
  have hbase : ∀ i ≤ MixedRadix.level S N,
      S.base i ≤ 4 * (MixedRadix.level S N + 11) ^ 2 := by
    intro i hi
    change radix i ≤ 4 * (MixedRadix.level S N + 11) ^ 2
    refine (radix_upper i).trans ?_
    gcongr
  have hglobal := MixedRadix.basisRepCount_le_uniform S M
    (4 * (MixedRadix.level S N + 11) ^ 2) N hM hflatS hbase
  have hkpos : 1 ≤ k := by
    simpa [k, S] using hlevel
  have hk1 : k + 1 ≤ 2 * k := by
    omega
  have hk11 : k + 11 ≤ 12 * k := by
    omega
  change MixedRadix.basisRepCount S N ≤ 2304 * k ^ 3 * M ^ k
  calc
    MixedRadix.basisRepCount S N ≤
        2 * (k + 1) * (4 * (k + 11) ^ 2) * M ^ k := by
      simpa [k] using hglobal
    _ ≤ 2 * (2 * k) * (4 * (12 * k) ^ 2) * M ^ k := by
      gcongr
    _ = 2304 * k ^ 3 * M ^ k := by ring

/-- Assemble any family of local digit sets satisfying exact binary-carry
coverage and a positive uniform ordered-fiber bound.

The conclusion simultaneously gives the exact additive-basis identity and
the ordered-antidiagonal little-o estimate required in Problem 29.  The local
construction used by the final file instantiates `M` with `144`.
-/
theorem assemble_schedule
    (digits : ℕ → Finset ℕ)
    (hdigit : ∀ i d, d ∈ digits i → d < radix i)
    (hcover : ∀ i r, r < radix i →
      ∃ x ∈ digits i, ∃ y ∈ digits i, (x + y) % radix i = r)
    (M : ℕ) (hM : 1 ≤ M)
    (hflat : ∀ i r, localRepCount digits i r ≤ M) :
    let S := scheduleSystem digits hdigit hcover
    MixedRadix.basis S + MixedRadix.basis S = Set.univ ∧
      ∀ ε : ℝ, 0 < ε →
        (fun n : ℕ ↦ (MixedRadix.basisRepCount S n : ℝ)) =o[atTop]
          (fun n : ℕ ↦ (n : ℝ) ^ ε) := by
  dsimp only
  let S := scheduleSystem digits hdigit hcover
  constructor
  · exact MixedRadix.basis_add_basis S
  · intro ε hε
    have hlevel : Tendsto (MixedRadix.level S) atTop atTop :=
      MixedRadix.tendsto_level S
    apply Analytic.isLittleO_rpow_of_level_superexponential
      (fun n : ℕ ↦ (MixedRadix.basisRepCount S n : ℝ)) (MixedRadix.level S)
      3 2304 (M : ℝ) ε (by norm_num) (by exact_mod_cast hM) hε hlevel
      (by
        simpa [S] using
          scheduleSystem_eventually_superexponential digits hdigit hcover)
    filter_upwards [hlevel.eventually_ge_atTop (1 : ℕ)] with n hn
    have hNat := scheduleSystem_basisRepCount_le digits hdigit hcover
      M hM hflat n hn
    have hReal : (MixedRadix.basisRepCount S n : ℝ) ≤
        2304 * (MixedRadix.level S n : ℝ) ^ 3 *
          (M : ℝ) ^ MixedRadix.level S n := by
      exact_mod_cast hNat
    simpa [abs_of_nonneg] using hReal

end Assembly

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos29.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 29.
https://www.erdosproblems.com/forum/thread/29

Informal authors:
- Paul Erdős

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos29.md
-/

/-!
  Erdős Problem 29

  Construct an additive basis of the natural numbers whose ordered
  representation function grows more slowly than every positive power.
-/



open Filter
open scoped Pointwise Real

/-- The ordered number of representations of `n` as a sum of two members of `A`. -/
noncomputable def addRepCount (A : Set ℕ) (n : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.HasAntidiagonal.antidiagonal
      (self := Finset.Nat.instHasAntidiagonal) n : Finset (ℕ × ℕ)).filter
      fun ab : ℕ × ℕ => ab.1 ∈ A ∧ ab.2 ∈ A).card

/-- The exact assertion in Erdős Problem 29, with ordered representations. -/
def SolvesErdos29 (A : Set ℕ) : Prop :=
  A + A = Set.univ ∧
    ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsLittleO Filter.atTop
        (fun n : ℕ => (addRepCount A n : ℝ))
        (fun n : ℕ => (n : ℝ) ^ ε)

/-! ## The explicit construction -/

/-- At position `i`, use the finite additive basis modulo the square of the
least prime strictly larger than `i + 11`.  Every search occurring in this
definition is bounded. -/
def explicitDigits (i : ℕ) : Finset ℕ :=
  Modular.digitSet (primeAt i)

theorem explicitDigits_lt (i d : ℕ) (hd : d ∈ explicitDigits i) :
    d < radix i := by
  exact Modular.digitSet_mem_lt (primeAt_prime i) hd

theorem explicitDigits_cover (i r : ℕ) (hr : r < radix i) :
    ∃ x ∈ explicitDigits i, ∃ y ∈ explicitDigits i,
      (x + y) % radix i = r := by
  exact Modular.digitSet_cover (primeAt_prime i)
    (le_trans (by omega) (primeAt_ge i)) hr

/-- The concrete mixed-radix system underlying the answer. -/
def explicitSystem : MixedRadix.LocalSystem :=
  Assembly.scheduleSystem explicitDigits explicitDigits_lt explicitDigits_cover

/-- The explicit additive basis: all non-leading mixed-radix digits belong to
`explicitDigits`, while the leading digit is unrestricted. -/
def explicitBasis : Set ℕ :=
  MixedRadix.basis explicitSystem

theorem explicitDigits_flat (i r : ℕ) :
    Assembly.localRepCount explicitDigits i r ≤ 144 := by
  have hp := primeAt_prime i
  have hp11 : 11 ≤ primeAt i := le_trans (by omega) (primeAt_ge i)
  have hr : r % radix i < primeAt i ^ 2 := by
    exact Nat.mod_lt _ (radix_pos i)
  change (Modular.digitModRepresentations (primeAt i) (r % radix i)).card ≤ 144
  exact Modular.digitModRepresentations_card_le hp hp11 (r % radix i) hr

theorem addRepCount_explicitBasis (n : ℕ) :
    addRepCount explicitBasis n = MixedRadix.basisRepCount explicitSystem n := by
  rfl

theorem explicitBasis_solves : SolvesErdos29 explicitBasis := by
  have h := Assembly.assemble_schedule explicitDigits explicitDigits_lt
    explicitDigits_cover 144 (by norm_num) explicitDigits_flat
  rcases h with ⟨hcover, hsmall⟩
  constructor
  · exact hcover
  · intro ε hε
    simpa only [addRepCount_explicitBasis, explicitSystem] using hsmall ε hε

theorem exists_solvesErdos29 : ∃ A : Set ℕ, SolvesErdos29 A :=
  ⟨explicitBasis, explicitBasis_solves⟩

/-- **Erdős Problem 29.**  The explicitly constructed set `explicitBasis` of
Jain--Pham--Sawhney--Zakharov is an additive basis whose ordered representation
function grows more slowly than every positive power.

The problem asks for an *explicit* construction: mere existence was already proved
by Erdős in the 1950s by the probabilistic method, so an `∃ A, …` statement would
formalize the wrong question.  The weaker existential form is `exists_solvesErdos29`
above. -/
theorem erdos_29 :
    explicitBasis + explicitBasis = Set.univ ∧
      ∀ ε : ℝ, 0 < ε →
        Asymptotics.IsLittleO Filter.atTop
          (fun n : ℕ => (addRepCount explicitBasis n : ℝ))
          (fun n : ℕ => (n : ℝ) ^ ε) :=
  explicitBasis_solves

end

#print axioms erdos_29
-- 'Erdos29.erdos_29' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos29
