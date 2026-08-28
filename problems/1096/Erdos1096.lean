import Mathlib

namespace Erdos1096

/-
# Problem Description

Erdős Problem 1096. For `1 < q < 1 + ε`, order the numbers `∑_{i ∈ S} qⁱ` (over finite `S`) by
size as `0 = x₁ < x₂ < ⋯`. Is it true that, for `ε > 0` small enough, `x_{k+1} - x_k → 0`?
`erdos_1096` proves that it is.

A problem of Erdős and Joó from the 1991 Great Western Number Theory problem session
[GWNT91]. They speculated the threshold might be `q₀ ≈ 1.3247`, the real root of `x³ = x + 1`
and the smallest Pisot--Vijayaraghavan number; in [EJK90] Erdős, Joó and Komornik showed no
Pisot--Vijayaraghavan number has the property, and that `x_{k+1} - x_k ≤ 1` for all `k` when
`1 < q ≤ 2`. In the statement below, "ordered by size" is rendered as `StrictMono x` together
with `Set.range x` being exactly the set of subset sums.

The formalisation is by plby (github.com/plby/lean-proofs),
`src/latest/ErdosProblems/Erdos1096.lean` together with the five modules of
`src/latest/ErdosProblems/Erdos1096/`. The six files are concatenated here in dependency
order, with their project-internal imports removed so that `Mathlib` is the only import, each
module's contents kept in a `section` carrying its own `open` lines, four unclosed upstream
scopes closed explicitly, and the whole wrapped once in `namespace Erdos1096` with the
upstream trust-base print line removed. No mathematical content is changed.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos1096/Erdos1096Core.lean` -/

section
/-!
# Erdős Problem 1096: combinatorial and analytic core

The increasing enumeration of the finite binary spectrum in every sufficiently
small base greater than one has successive gaps tending to zero.

The mathematical proof and a detailed Leanization guide are in `tex/1096.tex`.
-/

open Filter Set
open scoped BigOperators Pointwise Topology



noncomputable section

/-- Finite sums of distinct nonnegative powers of `q`. -/
def Spectrum (q : ℝ) : Set ℝ :=
  {a | ∃ S : Finset ℕ, a = ∑ i ∈ S, q ^ i}

/-- Every sufficiently large interval immediately to the right of its left
endpoint contains a member of `A`, with arbitrary prescribed length. -/
def EventuallyRightDense (A : Set ℝ) : Prop :=
  ∀ η > 0, ∃ B : ℝ, ∀ t, B ≤ t → ∃ a ∈ A, t < a ∧ a < t + η

/-- `U` contains finite increasing chains of arbitrarily small mesh and
arbitrarily large span. -/
def HasFineChains (U : Set ℝ) : Prop :=
  ∀ η > 0, ∀ D > 0, ∃ n : ℕ, ∃ u : ℕ → ℝ,
    (∀ k ≤ n, u k ∈ U) ∧
    (∀ k < n, u k < u (k + 1) ∧ u (k + 1) - u k < η) ∧
    D < u n - u 0

/-- Far enough out, every point has a member of `V` at most `D` to its
left.  This is the form of bounded coarse gaps used in the sumset argument. -/
def EventuallyLeftDense (V : Set ℝ) (D : ℝ) : Prop :=
  ∃ B : ℝ, ∀ t, B ≤ t → ∃ v ∈ V, t - D < v ∧ v ≤ t

/-- Pointwise multiplication of a real set by a positive scale. -/
def scaleSet (c : ℝ) (A : Set ℝ) : Set ℝ := (fun a ↦ c * a) '' A

/-- Arbitrarily small positive signed binary sums, with their positive and
negative supports already cancelled. -/
def SmallDisjointDifferences (r : ℝ) : Prop :=
  ∀ ε > 0, ∃ A B : Finset ℕ, Disjoint A B ∧
    0 < (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i ∧
    (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i < ε

/-- Zero is approached by nonzero differences of finite binary sums. -/
def SmallSpectrumDifferences (r : ℝ) : Prop :=
  ∀ ε > 0, ∃ A B : Finset ℕ,
    0 < |(∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i| ∧
    |(∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i| < ε

/-! ### The finite collision dichotomy -/

private def supportPolynomial (S : Finset ℕ) : Polynomial ℤ :=
  ∑ i ∈ S, Polynomial.X ^ i

private lemma eval₂_supportPolynomial (q : ℝ) (S : Finset ℕ) :
    (supportPolynomial S).eval₂ (algebraMap ℤ ℝ) q = ∑ i ∈ S, q ^ i := by
  rw [supportPolynomial, Polynomial.eval₂_finsetSum]
  simp

private lemma supportPolynomial_natDegree_le {S : Finset ℕ} {d : ℕ}
    (hS : ∀ i ∈ S, i ≤ d) : (supportPolynomial S).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [supportPolynomial, ← Polynomial.lcoeff_apply, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hiD := hS i hi
  have hNi : N ≠ i := by omega
  simp [Polynomial.coeff_X_pow, hNi]

/-- Orienting the largest exponent of two disjoint supports makes their signed
support polynomial monic. -/
private lemma supportPolynomial_sub_monic {P N : Finset ℕ} {d : ℕ}
    (hPN : Disjoint P N) (hdP : d ∈ P)
    (hmax : ∀ i ∈ P ∪ N, i ≤ d) :
    (supportPolynomial P - supportPolynomial N).Monic := by
  have hdN : d ∉ N := Finset.disjoint_left.mp hPN hdP
  have hP : ∀ i ∈ P, i ≤ d :=
    fun i hi ↦ hmax i (Finset.mem_union_left N hi)
  have hN : ∀ i ∈ N, i ≤ d :=
    fun i hi ↦ hmax i (Finset.mem_union_right P hi)
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one d
  · exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (supportPolynomial_natDegree_le hP) (supportPolynomial_natDegree_le hN))
  · simp [supportPolynomial, hdP, hdN]

/-- An exact collision between two distinct binary power sums gives an
explicit monic integer polynomial having the base as a root. -/
lemma isIntegral_of_powerSum_eq {q : ℝ} {A B : Finset ℕ} (hAB : A ≠ B)
    (hsum : (∑ i ∈ A, q ^ i) = ∑ i ∈ B, q ^ i) : IsIntegral ℤ q := by
  let P := A \ B
  let N := B \ A
  let U := P ∪ N
  have hPN : Disjoint P N := by
    dsimp [P, N]
    exact disjoint_sdiff_sdiff
  have hU : U.Nonempty := by
    by_contra hne
    have hUempty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    apply hAB
    apply Finset.Subset.antisymm
    · intro i hiA
      by_contra hiB
      have hiP : i ∈ P := by simpa [P] using And.intro hiA hiB
      have hiU : i ∈ U := Finset.mem_union_left N hiP
      rw [hUempty] at hiU
      simp at hiU
    · intro i hiB
      by_contra hiA
      have hiN : i ∈ N := by simpa [N] using And.intro hiB hiA
      have hiU : i ∈ U := Finset.mem_union_right P hiN
      rw [hUempty] at hiU
      simp at hiU
  let d := U.max' hU
  have hdU : d ∈ U := Finset.max'_mem U hU
  have hmax : ∀ i ∈ P ∪ N, i ≤ d := by
    intro i hi
    exact Finset.le_max' U i hi
  have hdiff : (∑ i ∈ P, q ^ i) - ∑ i ∈ N, q ^ i = 0 := by
    dsimp [P, N]
    rw [Finset.sum_sdiff_sub_sum_sdiff]
    linarith
  rcases Finset.mem_union.mp hdU with hdP | hdN
  · refine ⟨supportPolynomial P - supportPolynomial N,
      supportPolynomial_sub_monic hPN hdP hmax, ?_⟩
    rw [Polynomial.eval₂_sub, eval₂_supportPolynomial, eval₂_supportPolynomial]
    exact hdiff
  · refine ⟨supportPolynomial N - supportPolynomial P,
      supportPolynomial_sub_monic hPN.symm hdN (by simpa [Finset.union_comm] using hmax), ?_⟩
    have : (∑ i ∈ N, q ^ i) - ∑ i ∈ P, q ^ i = 0 := by linarith
    rw [Polynomial.eval₂_sub, eval₂_supportPolynomial, eval₂_supportPolynomial]
    exact this

private lemma exists_geometric_packing_scale {q ε : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (hε : 0 < ε) :
    ∃ n : ℕ, q ^ n / (q - 1) < ε * ((2 : ℝ) ^ n - 1) := by
  have hc0 : 0 ≤ q / 2 := by positivity
  have hc1 : q / 2 < 1 := by linarith
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1
  have htarget : 0 < ε * (q - 1) / 2 := by positivity
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨N, hN⟩ := ht (ε * (q - 1) / 2) htarget
  let n := N + 1
  have hnN : N ≤ n := by dsimp [n]; omega
  have hsmall : (q / 2) ^ n < ε * (q - 1) / 2 := by
    have := hN n hnN
    simpa [Real.dist_eq, abs_of_pos (by linarith : 0 < q)] using this
  have htwo_pos : 0 < (2 : ℝ) ^ n := by positivity
  have htwo : 2 ≤ (2 : ℝ) ^ n := by
    dsimp [n]
    rw [pow_succ]
    have hone : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    nlinarith
  have hratio : q ^ n / (2 : ℝ) ^ n < ε * (q - 1) / 2 := by
    simpa [div_pow] using hsmall
  have hqpow : q ^ n < (ε * (q - 1) / 2) * (2 : ℝ) ^ n :=
    (div_lt_iff₀ htwo_pos).mp hratio
  have hqden : 0 < q - 1 := by linarith
  apply Exists.intro n
  apply (div_lt_iff₀ hqden).mpr
  nlinarith

/-- For a nonintegral base below two, the elementary powerset pigeonhole
argument already gives arbitrarily small nonzero signed binary sums. -/
lemma smallSpectrumDifferences_of_not_isIntegral {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (hq_nonintegral : ¬ IsIntegral ℤ q) : SmallSpectrumDifferences q := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_geometric_packing_scale hq1 hq2 hε
  have hnpos : 0 < n := by
    by_contra h
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    norm_num at hn
    have hden : 0 < q - 1 := by linarith
    have hone : 0 < 1 / (q - 1) := one_div_pos.mpr hden
    linarith
  let K : ℕ := 2 ^ n - 1
  let F : Finset (Finset ℕ) := (Finset.range n).powerset
  let bin : Finset ℕ → ℕ := fun S ↦ ⌊(∑ i ∈ S, q ^ i) / ε⌋₊
  have hpow_one : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  have hcastK : (K : ℝ) = (2 : ℝ) ^ n - 1 := by
    dsimp [K]
    rw [Nat.cast_sub hpow_one]
    norm_num
  have hq0 : 0 ≤ q := by linarith
  have hqden : 0 < q - 1 := by linarith
  have hmaps : Set.MapsTo bin (F : Set (Finset ℕ)) (Finset.range K : Set ℕ) := by
    intro S hSF
    have hS : S ⊆ Finset.range n := Finset.mem_powerset.mp hSF
    have hsum0 : 0 ≤ ∑ i ∈ S, q ^ i := by positivity
    have hsum_le : (∑ i ∈ S, q ^ i) ≤ ∑ i ∈ Finset.range n, q ^ i :=
      Finset.sum_le_sum_of_subset_of_nonneg hS (by
        intro i hi hiS
        positivity)
    have hfull_lt : (∑ i ∈ Finset.range n, q ^ i) < q ^ n / (q - 1) := by
      rw [geom_sum_eq (by linarith)]
      calc
        (q ^ n - 1) / (q - 1) = q ^ n / (q - 1) - 1 / (q - 1) := by ring
        _ < q ^ n / (q - 1) := by
          have hinv : 0 < 1 / (q - 1) := one_div_pos.mpr hqden
          linarith
    have hsum_lt : (∑ i ∈ S, q ^ i) < ε * ((2 : ℝ) ^ n - 1) :=
      lt_of_le_of_lt hsum_le (hfull_lt.trans hn)
    change bin S ∈ Finset.range K
    rw [Finset.mem_range]
    apply (Nat.floor_lt (div_nonneg hsum0 hε.le)).mpr
    rw [hcastK]
    exact (div_lt_iff₀ hε).mpr (by nlinarith)
  have hcard : (Finset.range K).card < F.card := by
    have hpowpos : 0 < 2 ^ n := pow_pos (by omega) n
    simp only [Finset.card_range, F, Finset.card_powerset, Finset.card_range]
    dsimp [K]
    omega
  obtain ⟨A, hAF, B, hBF, hAB, hbin⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  let a : ℝ := ∑ i ∈ A, q ^ i
  let b : ℝ := ∑ i ∈ B, q ^ i
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hfloor : ⌊a / ε⌋₊ = ⌊b / ε⌋₊ := by simpa [bin, a, b] using hbin
  let k : ℕ := ⌊a / ε⌋₊
  have halo : (k : ℝ) ≤ a / ε := by
    dsimp [k]
    exact Nat.floor_le (div_nonneg ha0 hε.le)
  have hahi : a / ε < (k : ℝ) + 1 := by
    dsimp [k]
    exact Nat.lt_floor_add_one (a / ε)
  have hblo : (k : ℝ) ≤ b / ε := by
    rw [show k = ⌊b / ε⌋₊ by exact hfloor]
    exact Nat.floor_le (div_nonneg hb0 hε.le)
  have hbhi : b / ε < (k : ℝ) + 1 := by
    rw [show k = ⌊b / ε⌋₊ by exact hfloor]
    exact Nat.lt_floor_add_one (b / ε)
  have hab_ne : b - a ≠ 0 := by
    intro hz
    have hab : a = b := by linarith
    apply hq_nonintegral
    apply isIntegral_of_powerSum_eq hAB
    simpa [a, b] using hab
  have hba_div : (b - a) / ε < 1 := by
    rw [sub_div]
    linarith
  have hab_div : (a - b) / ε < 1 := by
    rw [sub_div]
    linarith
  have hba_lt : b - a < ε := by
    have := (div_lt_iff₀ hε).mp hba_div
    nlinarith
  have hab_lt : a - b < ε := by
    have := (div_lt_iff₀ hε).mp hab_div
    nlinarith
  refine ⟨A, B, ?_, ?_⟩
  · dsimp [a, b] at hab_ne ⊢
    exact abs_pos.mpr hab_ne
  · dsimp [a, b] at hba_lt hab_lt ⊢
    rw [abs_lt]
    constructor <;> linarith

/-! ### The lazy binary-expansion engine -/

private def binaryRemainder (q x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if binaryRemainder q x n ≤ (q⁻¹) ^ (n + 1) / (q - 1) then
        binaryRemainder q x n
      else
        binaryRemainder q x n - (q⁻¹) ^ (n + 1)

private def binaryDigit (q x : ℝ) (n : ℕ) : ℕ :=
  if binaryRemainder q x n ≤ (q⁻¹) ^ (n + 1) / (q - 1) then 0 else 1

private lemma binaryDigit_eq_zero_or_one (q x : ℝ) (n : ℕ) :
    binaryDigit q x n = 0 ∨ binaryDigit q x n = 1 := by
  unfold binaryDigit
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma binaryRemainder_succ (q x : ℝ) (n : ℕ) :
    binaryRemainder q x (n + 1) = binaryRemainder q x n -
      (binaryDigit q x n : ℝ) * (q⁻¹) ^ (n + 1) := by
  simp only [binaryRemainder, binaryDigit]
  split_ifs <;> simp

private lemma inverse_geometric_step {q : ℝ} (hq : 1 < q) (n : ℕ) :
    (q⁻¹) ^ n / (q - 1) - (q⁻¹) ^ (n + 1) =
      (q⁻¹) ^ (n + 1) / (q - 1) := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  have hqm1 : q - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  rw [pow_succ]
  field_simp
  ring

private lemma binaryRemainder_bounds {q x : ℝ} (hq1 : 1 < q) (hq2 : q ≤ 2)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / (q - 1)) (n : ℕ) :
    0 ≤ binaryRemainder q x n ∧
      binaryRemainder q x n ≤ (q⁻¹) ^ n / (q - 1) := by
  induction n with
  | zero => simpa [binaryRemainder] using And.intro hx0 hx1
  | succ n ih =>
      have hden : 0 < q - 1 := sub_pos.mpr hq1
      have hpow : 0 ≤ (q⁻¹) ^ (n + 1) := pow_nonneg (inv_nonneg.mpr (le_trans zero_le_one hq1.le)) _
      have hweight_le : (q⁻¹) ^ (n + 1) ≤ (q⁻¹) ^ (n + 1) / (q - 1) := by
        rw [le_div_iff₀ hden]
        nlinarith
      rw [binaryRemainder]
      split_ifs with hsmall
      · exact ⟨ih.1, hsmall⟩
      · have hlarge : (q⁻¹) ^ (n + 1) < binaryRemainder q x n :=
          lt_of_le_of_lt hweight_le (lt_of_not_ge hsmall)
        constructor
        · linarith
        · rw [← inverse_geometric_step hq1 n]
          linarith [ih.2]

private lemma binaryRemainder_eq_sub_sum (q x : ℝ) (n : ℕ) :
    binaryRemainder q x n = x -
      ∑ i ∈ Finset.range n, (binaryDigit q x i : ℝ) * (q⁻¹) ^ (i + 1) := by
  induction n with
  | zero => simp [binaryRemainder]
  | succ n ih =>
      rw [binaryRemainder_succ, ih, Finset.sum_range_succ]
      ring

private lemma binaryRemainder_tendsto_zero {q x : ℝ} (hq1 : 1 < q) (hq2 : q ≤ 2)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / (q - 1)) :
    Tendsto (binaryRemainder q x) atTop (𝓝 0) := by
  have hq0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (le_trans zero_le_one hq1.le)
  have hqinv : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
  have hpow : Tendsto (fun n : ℕ ↦ (q⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hqinv
  have hcap : Tendsto (fun n : ℕ ↦ (q⁻¹) ^ n / (q - 1)) atTop (𝓝 0) := by
    simpa using hpow.div_const (q - 1)
  exact squeeze_zero
    (fun n ↦ (binaryRemainder_bounds hq1 hq2 hx0 hx1 n).1)
    (fun n ↦ (binaryRemainder_bounds hq1 hq2 hx0 hx1 n).2) hcap

lemma exists_binary_expansion {q x : ℝ} (hq1 : 1 < q) (hq2 : q ≤ 2)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / (q - 1)) :
    ∃ d : ℕ → ℕ, (∀ n, d n = 0 ∨ d n = 1) ∧
      Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
        (d i : ℝ) * (q⁻¹) ^ (i + 1)) atTop (𝓝 x) := by
  refine ⟨binaryDigit q x, binaryDigit_eq_zero_or_one q x, ?_⟩
  have hrem := binaryRemainder_tendsto_zero hq1 hq2 hx0 hx1
  convert tendsto_const_nhds.sub hrem using 1
  · funext n
    rw [binaryRemainder_eq_sub_sum]
    ring
  · ring

/-- The greedy/lazy binary expansion above, retaining the geometric bound on
its finite remainders. -/
lemma exists_binary_expansion_with_remainder_bounds {q x : ℝ}
    (hq1 : 1 < q) (hq2 : q ≤ 2)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / (q - 1)) :
    ∃ d : ℕ → ℕ, (∀ n, d n = 0 ∨ d n = 1) ∧
      ∀ n, 0 ≤ x - ∑ i ∈ Finset.range n,
        (d i : ℝ) * (q⁻¹) ^ (i + 1) ∧
      x - ∑ i ∈ Finset.range n,
        (d i : ℝ) * (q⁻¹) ^ (i + 1) ≤ (q⁻¹) ^ n / (q - 1) := by
  refine ⟨binaryDigit q x, binaryDigit_eq_zero_or_one q x, fun n ↦ ?_⟩
  rw [← binaryRemainder_eq_sub_sum]
  exact binaryRemainder_bounds hq1 hq2 hx0 hx1 n

lemma smallDisjointDifferences_of_smallSpectrumDifferences {r : ℝ}
    (h : SmallSpectrumDifferences r) : SmallDisjointDifferences r := by
  intro ε hε
  obtain ⟨A, B, hne, hlt⟩ := h ε hε
  have hdifference :
      (∑ i ∈ B \ A, r ^ i) - ∑ i ∈ A \ B, r ^ i =
        (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i := by
    rw [Finset.sum_sdiff_sub_sum_sdiff]
  by_cases hpos : 0 < (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i
  · refine ⟨A \ B, B \ A, disjoint_sdiff_sdiff, ?_, ?_⟩
    · rwa [hdifference]
    · calc
        (∑ i ∈ B \ A, r ^ i) - ∑ i ∈ A \ B, r ^ i =
            (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i := hdifference
        _ < ε := by simpa [abs_of_pos hpos] using hlt
  · have hneg : (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i < 0 := by
      have hnonzero : (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i ≠ 0 := by
        intro hz
        rw [hz, abs_zero] at hne
        exact lt_irrefl 0 hne
      exact lt_of_le_of_ne (le_of_not_gt hpos) hnonzero
    refine ⟨B \ A, A \ B, disjoint_sdiff_sdiff, ?_, ?_⟩
    · have := hdifference
      linarith
    · have := hdifference
      rw [abs_of_neg hneg] at hlt
      linarith

private def shiftSupport (N : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image (fun i ↦ N + i)

private lemma sum_shiftSupport (r : ℝ) (N : ℕ) (S : Finset ℕ) :
    (∑ k ∈ shiftSupport N S, r ^ k) = r ^ N * ∑ i ∈ S, r ^ i := by
  rw [shiftSupport, Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_add]
  · intro i hi j hj hij
    change N + i = N + j at hij
    omega

private lemma shiftSupport_disjoint {N : ℕ} {A B : Finset ℕ} (h : Disjoint A B) :
    Disjoint (shiftSupport N A) (shiftSupport N B) := by
  rw [Finset.disjoint_left] at h ⊢
  intro k hkA hkB
  rcases Finset.mem_image.mp hkA with ⟨i, hiA, hik⟩
  rcases Finset.mem_image.mp hkB with ⟨j, hjB, hjk⟩
  have : i = j := by omega
  subst j
  exact h hiA hjB

private lemma le_of_mem_shiftSupport {N : ℕ} {S : Finset ℕ} {i : ℕ}
    (hi : i ∈ shiftSupport N S) : N ≤ i := by
  rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
  omega

/-- A tiny signed value may be shifted and rescaled to a prescribed support
tail while keeping its size between `δ` and `2δ`. -/
lemma exists_close_pair_above {r : ℝ} (hr1 : 1 < r) (hr2 : r < 2)
    (hsmall : SmallDisjointDifferences r) {δ : ℝ} (hδ : 0 < δ) (H : ℕ) :
    ∃ A B : Finset ℕ, Disjoint A B ∧
      (∀ i ∈ A, H ≤ i) ∧ (∀ i ∈ B, H ≤ i) ∧
      δ < (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i ∧
      (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i < 2 * δ := by
  have hr0 : 0 < r := by linarith
  have hrH : 0 < r ^ H := by positivity
  obtain ⟨A₀, B₀, hAB₀, hdpos, hdlt⟩ := hsmall (δ / r ^ H) (div_pos hδ hrH)
  let d := (∑ i ∈ B₀, r ^ i) - ∑ i ∈ A₀, r ^ i
  have hd : 0 < d := hdpos
  have hdHlt : r ^ H * d < δ := by
    dsimp [d]
    have h := (lt_div_iff₀ hrH).mp hdlt
    nlinarith
  have hdHpos : 0 < r ^ H * d := mul_pos hrH hd
  have hpow := tendsto_pow_atTop_atTop_of_one_lt hr1
  obtain ⟨N₀, hN₀⟩ :=
    tendsto_atTop_atTop.mp hpow (δ / (r ^ H * d) + 1)
  have hex : ∃ N : ℕ, δ < r ^ N * (r ^ H * d) := by
    refine ⟨N₀, ?_⟩
    have hp := hN₀ N₀ le_rfl
    have hden : 0 < r ^ H * d := hdHpos
    exact (div_lt_iff₀ hden).mp
      (lt_of_lt_of_le (lt_add_one (δ / (r ^ H * d))) hp)
  let N := Nat.find hex
  have hNspec : δ < r ^ N * (r ^ H * d) := Nat.find_spec hex
  have hNpos : 0 < N := by
    by_contra hnot
    have hNzero : N = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hNzero, pow_zero, one_mul] at hNspec
    linarith
  have hNmin : r ^ (N - 1) * (r ^ H * d) ≤ δ := by
    have hnot := Nat.find_min hex (Nat.pred_lt hNpos.ne')
    simpa only [Nat.pred_eq_sub_one, not_lt] using hnot
  let K := H + N
  refine ⟨shiftSupport K A₀, shiftSupport K B₀, shiftSupport_disjoint hAB₀,
    ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact le_trans (Nat.le_add_right H N) (le_of_mem_shiftSupport hi)
  · intro i hi
    exact le_trans (Nat.le_add_right H N) (le_of_mem_shiftSupport hi)
  · rw [sum_shiftSupport, sum_shiftSupport]
    dsimp [K]
    rw [pow_add]
    dsimp [d] at hNspec ⊢
    nlinarith
  · rw [sum_shiftSupport, sum_shiftSupport]
    dsimp [K]
    rw [pow_add]
    have hpowN : r ^ N = r * r ^ (N - 1) := by
      obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hNpos.ne'
      rw [hM]
      simp [pow_succ, mul_comm]
    dsimp [d] at hNmin ⊢
    rw [hpowN]
    nlinarith

/-- Iterating high disjoint close pairs gives a chain of binary supports.
The quantitative lower bound on its span is retained for the later crossing
argument. -/
private lemma exists_support_chain {r : ℝ} (hr1 : 1 < r) (hr2 : r < 2)
    (hsmall : SmallDisjointDifferences r) {δ : ℝ} (hδ : 0 < δ) :
    ∀ M H : ℕ, ∃ W : ℕ → Finset ℕ,
      (∀ k ≤ M, ∀ i ∈ W k, H ≤ i) ∧
      (∀ k < M, δ < (∑ i ∈ W (k + 1), r ^ i) - ∑ i ∈ W k, r ^ i ∧
        (∑ i ∈ W (k + 1), r ^ i) - ∑ i ∈ W k, r ^ i < 2 * δ) ∧
      (M : ℝ) * δ ≤ (∑ i ∈ W M, r ^ i) - ∑ i ∈ W 0, r ^ i := by
  intro M
  induction M with
  | zero =>
      intro H
      refine ⟨fun _ ↦ ∅, ?_, ?_, ?_⟩
      · simp
      · simp
      · simp
  | succ M ih =>
      intro H
      obtain ⟨A, B, hAB, hAabove, hBabove, hdlo, hdhi⟩ :=
        exists_close_pair_above hr1 hr2 hsmall hδ H
      let H₁ := H + (A ∪ B).sup id + 1
      obtain ⟨W, hWabove, hWstep, hWspan⟩ := ih H₁
      let W' : ℕ → Finset ℕ
        | 0 => A ∪ W 0
        | k + 1 => B ∪ W k
      have hHH₁ : H ≤ H₁ := by dsimp [H₁]; omega
      have hpair_lt {i : ℕ} (hi : i ∈ A ∪ B) : i < H₁ := by
        have hisup : i ≤ (A ∪ B).sup id := Finset.le_sup (f := id) hi
        dsimp [H₁]
        omega
      have hAdisj (k : ℕ) (hk : k ≤ M) : Disjoint A (W k) := by
        rw [Finset.disjoint_left]
        intro i hiA hiW
        have hilt : i < H₁ := hpair_lt (Finset.mem_union_left B hiA)
        have hige : H₁ ≤ i := hWabove k hk i hiW
        omega
      have hBdisj (k : ℕ) (hk : k ≤ M) : Disjoint B (W k) := by
        rw [Finset.disjoint_left]
        intro i hiB hiW
        have hilt : i < H₁ := hpair_lt (Finset.mem_union_right A hiB)
        have hige : H₁ ≤ i := hWabove k hk i hiW
        omega
      refine ⟨W', ?_, ?_, ?_⟩
      · intro k hk i hi
        cases k with
        | zero =>
            simp only [W'] at hi
            rcases Finset.mem_union.mp hi with hiA | hiW
            · exact hAabove i hiA
            · exact hHH₁.trans (hWabove 0 (Nat.zero_le M) i hiW)
        | succ k =>
            simp only [W'] at hi
            have hkM : k ≤ M := by omega
            rcases Finset.mem_union.mp hi with hiB | hiW
            · exact hBabove i hiB
            · exact hHH₁.trans (hWabove k hkM i hiW)
      · intro k hk
        cases k with
        | zero =>
            simp only [W', zero_add]
            rw [Finset.sum_union (hBdisj 0 (Nat.zero_le M))]
            rw [Finset.sum_union (hAdisj 0 (Nat.zero_le M))]
            constructor <;> linarith
        | succ k =>
            have hkM : k < M := by omega
            simp only [W']
            rw [Finset.sum_union (hBdisj (k + 1) (by omega))]
            rw [Finset.sum_union (hBdisj k hkM.le)]
            have hs := hWstep k hkM
            constructor <;> linarith
      · simp only [W']
        rw [Finset.sum_union (hBdisj M le_rfl)]
        rw [Finset.sum_union (hAdisj 0 (Nat.zero_le M))]
        norm_num [Nat.cast_add, Nat.cast_one]
        nlinarith

/-- The elementary Erdős--Joó--Komornik replacement-chain lemma. -/
lemma spectrum_hasFineChains_of_smallDifferences {r : ℝ} (hr1 : 1 < r) (hr2 : r < 2)
    (hsmall : SmallDisjointDifferences r) : HasFineChains (Spectrum r) := by
  intro η hη D hD
  have hhalf : 0 < η / 2 := by linarith
  obtain ⟨M, hM⟩ : ∃ M : ℕ, D < (M : ℝ) * (η / 2) := by
    obtain ⟨M, hM⟩ := exists_nat_gt (D / (η / 2))
    refine ⟨M, ?_⟩
    have := (div_lt_iff₀ hhalf).mp hM
    nlinarith
  obtain ⟨W, hWabove, hWstep, hWspan⟩ :=
    exists_support_chain hr1 hr2 hsmall hhalf M 0
  let u : ℕ → ℝ := fun k ↦ ∑ i ∈ W k, r ^ i
  refine ⟨M, u, ?_, ?_, ?_⟩
  · intro k hk
    exact ⟨W k, rfl⟩
  · intro k hk
    have hs := hWstep k hk
    dsimp [u]
    constructor <;> linarith
  · dsimp [u]
    linarith

@[simp] lemma mem_spectrum_iff {q a : ℝ} :
    a ∈ Spectrum q ↔ ∃ S : Finset ℕ, a = ∑ i ∈ S, q ^ i := Iff.rfl

lemma pow_mem_spectrum (q : ℝ) (n : ℕ) : q ^ n ∈ Spectrum q := by
  refine ⟨{n}, ?_⟩
  simp

lemma spectrum_nonneg {q : ℝ} (hq : 0 ≤ q) {a : ℝ} (ha : a ∈ Spectrum q) : 0 ≤ a := by
  rcases ha with ⟨S, rfl⟩
  positivity

/-- Binary sums using only exponents below `n` approximate every point of
`[0,q^n)` from below with error less than one when `q ≤ 2`. -/
lemma exists_powerSum_below_of_lt_pow {q : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 2) :
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t < q ^ n →
      ∃ S : Finset ℕ, S ⊆ Finset.range n ∧
        t - 1 < ∑ i ∈ S, q ^ i ∧ (∑ i ∈ S, q ^ i) ≤ t := by
  intro n
  induction n with
  | zero =>
      intro t ht0 ht1
      refine ⟨∅, by simp, ?_, by simp [ht0]⟩
      simpa using ht1
  | succ n ih =>
      intro t ht0 htpow
      by_cases hlow : t < q ^ n
      · obtain ⟨S, hS, hlo, hhi⟩ := ih t ht0 hlow
        exact ⟨S, hS.trans (Finset.range_mono (Nat.le_succ n)), hlo, hhi⟩
      · have hqn : 0 ≤ q ^ n := by positivity
        have hrem0 : 0 ≤ t - q ^ n := sub_nonneg.mpr (le_of_not_gt hlow)
        have hrem_lt : t - q ^ n < q ^ n := by
          rw [pow_succ] at htpow
          nlinarith
        obtain ⟨S, hS, hlo, hhi⟩ := ih (t - q ^ n) hrem0 hrem_lt
        have hnS : n ∉ S := by
          intro hn
          have := hS hn
          simp only [Finset.mem_range] at this
          omega
        refine ⟨insert n S, ?_, ?_, ?_⟩
        · intro i hi
          simp only [Finset.mem_insert] at hi
          simp only [Finset.mem_range]
          rcases hi with hi | hi
          · subst i
            exact Nat.lt_succ_self n
          · exact (Finset.mem_range.mp (hS hi)).trans_le (Nat.le_succ n)
        · rw [Finset.sum_insert hnS]
          linarith
        · rw [Finset.sum_insert hnS]
          linarith

/-- For bases at most two the binary spectrum meets every interval `(t-1,t]`
with `t ≥ 0`. -/
lemma spectrum_one_left_dense {q : ℝ} (hq : 1 < q) (hq2 : q ≤ 2) :
    ∀ t : ℝ, 0 ≤ t → ∃ a ∈ Spectrum q, t - 1 < a ∧ a ≤ t := by
  intro t ht
  have hpow := tendsto_pow_atTop_atTop_of_one_lt hq
  obtain ⟨n, hn⟩ := tendsto_atTop_atTop.mp hpow (t + 1)
  have htlt : t < q ^ n := lt_of_lt_of_le (lt_add_one t) (hn n le_rfl)
  obtain ⟨S, hS, hlo, hhi⟩ :=
    exists_powerSum_below_of_lt_pow (q := q) (by linarith) hq2 n t ht htlt
  exact ⟨∑ i ∈ S, q ^ i, ⟨S, rfl⟩, hlo, hhi⟩

lemma spectrum_eventuallyLeftDense_one {q : ℝ} (hq : 1 < q) (hq2 : q ≤ 2) :
    EventuallyLeftDense (Spectrum q) 1 := by
  refine ⟨0, fun t ht ↦ ?_⟩
  exact spectrum_one_left_dense hq hq2 t ht

lemma scaleSet_spectrum_eventuallyLeftDense {c r : ℝ} (hc : 0 < c)
    (hr : 1 < r) (hr2 : r ≤ 2) :
    EventuallyLeftDense (scaleSet c (Spectrum r)) c := by
  refine ⟨0, fun t ht ↦ ?_⟩
  have htc : 0 ≤ t / c := div_nonneg ht hc.le
  obtain ⟨a, ha, hlo, hhi⟩ := spectrum_one_left_dense hr hr2 (t / c) htc
  have hcne : c ≠ 0 := ne_of_gt hc
  have hcancel : c * (t / c) = t := by field_simp
  refine ⟨c * a, ⟨a, ha, rfl⟩, ?_, ?_⟩ <;> nlinarith

private def evenSupport (S : Finset ℕ) : Finset ℕ := S.image (fun i ↦ 2 * i)

private def oddSupport (S : Finset ℕ) : Finset ℕ := S.image (fun i ↦ 2 * i + 1)

private lemma evenSupport_disjoint_oddSupport (S T : Finset ℕ) :
    Disjoint (evenSupport S) (oddSupport T) := by
  rw [Finset.disjoint_left]
  intro k hkS hkT
  rcases Finset.mem_image.mp hkS with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hkT with ⟨j, hj, h⟩
  omega

private lemma sum_evenSupport (q : ℝ) (S : Finset ℕ) :
    (∑ k ∈ evenSupport S, q ^ k) = ∑ i ∈ S, (q ^ 2) ^ i := by
  rw [evenSupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [pow_mul]
  · intro i hi j hj hij
    change 2 * i = 2 * j at hij
    omega

private lemma sum_oddSupport (q : ℝ) (S : Finset ℕ) :
    (∑ k ∈ oddSupport S, q ^ k) = q * ∑ i ∈ S, (q ^ 2) ^ i := by
  rw [oddSupport, Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ, pow_mul]
    ring
  · intro i hi j hj hij
    change 2 * i + 1 = 2 * j + 1 at hij
    omega

/-- The even powers represented by `Spectrum (q^2)` and a scaled copy using
the odd powers add without digit collisions to a binary `q`-spectrum value. -/
lemma add_scaleSet_square_subset_spectrum (q : ℝ) :
    ∀ u ∈ Spectrum (q ^ 2), ∀ v ∈ scaleSet q (Spectrum (q ^ 2)), u + v ∈ Spectrum q := by
  intro u hu v hv
  rcases hu with ⟨S, rfl⟩
  rcases hv with ⟨a, ⟨T, rfl⟩, rfl⟩
  refine ⟨evenSupport S ∪ oddSupport T, ?_⟩
  rw [Finset.sum_union (evenSupport_disjoint_oddSupport S T)]
  rw [sum_evenSupport, sum_oddSupport]

/-- The supplied increasing enumeration tends to infinity.  Strict
monotonicity alone would not suffice; the range equality supplies the
unbounded singleton powers. -/
lemma strictMono_spectrum_tendsto_atTop {q : ℝ} (hq : 1 < q)
    {x : ℕ → ℝ} (hx : StrictMono x) (hrange : Set.range x = Spectrum q) :
    Tendsto x atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b ≤ q ^ n := by
    have hpow := tendsto_pow_atTop_atTop_of_one_lt hq
    obtain ⟨n, hn⟩ := tendsto_atTop_atTop.mp hpow b
    exact ⟨n, hn n le_rfl⟩
  have hmem : q ^ n ∈ Set.range x := by
    rw [hrange]
    exact pow_mem_spectrum q n
  rcases hmem with ⟨k, hk⟩
  refine ⟨k, fun m hkm ↦ ?_⟩
  calc
    b ≤ q ^ n := hn
    _ = x k := hk.symm
    _ ≤ x m := hx.monotone hkm

/-- Eventual right-density forces the gaps in any increasing, unbounded exact
enumeration to tend to zero. -/
lemma gaps_tendsto_zero_of_eventuallyRightDense {A : Set ℝ} {x : ℕ → ℝ}
    (hx : StrictMono x) (hrange : Set.range x = A)
    (hxtop : Tendsto x atTop atTop) (hA : EventuallyRightDense A) :
    Tendsto (fun k ↦ x (k + 1) - x k) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  rcases hA η hη with ⟨B, hB⟩
  have hxB : ∀ᶠ k in atTop, B ≤ x k := hxtop.eventually (eventually_ge_atTop B)
  rw [eventually_atTop] at hxB
  rcases hxB with ⟨K, hK⟩
  refine ⟨K, fun k hk ↦ ?_⟩
  have hkB := hK k hk
  rcases hB (x k) hkB with ⟨a, haA, hka, hakη⟩
  rw [← hrange] at haA
  rcases haA with ⟨j, rfl⟩
  have hkj : k < j := hx.lt_iff_lt.mp hka
  have hsucc : k + 1 ≤ j := hkj
  have hgap_nonneg : 0 ≤ x (k + 1) - x k := sub_nonneg.mpr (hx.monotone (Nat.le_succ k))
  have hgap_lt : x (k + 1) - x k < η := by
    have := hx.monotone hsucc
    linarith
  simpa [Real.dist_eq, abs_of_nonneg hgap_nonneg] using hgap_lt

/-- A long fine chain translated by a coarsely left-dense set crosses every
sufficiently late target in a step shorter than the fine mesh. -/
lemma eventuallyRightDense_of_fineChains_add_leftDense
    {U V Z : Set ℝ} {D : ℝ} (hD : 0 < D)
    (hU : HasFineChains U) (hV : EventuallyLeftDense V D)
    (hadd : ∀ u ∈ U, ∀ v ∈ V, u + v ∈ Z) :
    EventuallyRightDense Z := by
  intro η hη
  obtain ⟨n, u, huU, hstep, hspan⟩ := hU η hη D hD
  obtain ⟨C, hC⟩ := hV
  refine ⟨C + u 0, fun t ht ↦ ?_⟩
  have htC : C ≤ t - u 0 := by linarith
  obtain ⟨v, hvV, hvlo, hvhi⟩ := hC (t - u 0) htC
  have hcross : t < u n + v := by linarith
  let P : ℕ → Prop := fun k ↦ k ≤ n ∧ t < u k + v
  have hex : ∃ k, P k := ⟨n, le_rfl, hcross⟩
  let k := Nat.find hex
  have hk : k ≤ n ∧ t < u k + v := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    rw [hkzero] at hk
    linarith
  let j := k - 1
  have hjk : j < k := by
    dsimp [j]
    omega
  have hjle : j ≤ n := hjk.le.trans hk.1
  have hprev : u j + v ≤ t := by
    by_contra hnotle
    have hjcross : t < u j + v := lt_of_not_ge hnotle
    exact Nat.find_min hex hjk ⟨hjle, hjcross⟩
  have hjn : j < n := hjk.trans_le hk.1
  have hjstep := (hstep j hjn).2
  have hjsk : j + 1 = k := by
    dsimp [j]
    omega
  rw [hjsk] at hjstep
  refine ⟨u k + v, hadd (u k) (huU k hk.1) v hvV, hk.2, ?_⟩
  linarith

/-- Complete elementary even/odd bridge: small signed values in base `q²`
force arbitrary eventual mesh in the binary spectrum of base `q`. -/
lemma spectrum_eventuallyRightDense_of_square_smallDifferences {q : ℝ}
    (hq : 1 < q) (hq_sq : q ^ 2 < 2)
    (hsmall : SmallDisjointDifferences (q ^ 2)) :
    EventuallyRightDense (Spectrum q) := by
  have hq0 : 0 < q := by linarith
  have hsq1 : 1 < q ^ 2 := by nlinarith
  have hfine : HasFineChains (Spectrum (q ^ 2)) :=
    spectrum_hasFineChains_of_smallDifferences hsq1 hq_sq hsmall
  have hleft : EventuallyLeftDense (scaleSet q (Spectrum (q ^ 2))) q :=
    scaleSet_spectrum_eventuallyLeftDense hq0 hsq1 hq_sq.le
  exact eventuallyRightDense_of_fineChains_add_leftDense hq0 hfine hleft
    (add_scaleSet_square_subset_spectrum q)

/-- Once the small-base signed-spectrum input is available, this is the exact
statement of Problem 1096.  Keeping the front end as an explicit argument
makes the analytic/combinatorial transfer independently checkable. -/
lemma erdos_1096_of_small_base_spectral
    (hspectral : ∀ r : ℝ, 1 < r → r < 121 / 100 → SmallSpectrumDifferences r) :
    ∃ ε > 0, ∀ q, 1 < q → q < 1 + ε →
      ∀ x : ℕ → ℝ, StrictMono x →
        Set.range x = { ∑ i ∈ S, q ^ i | S : Finset ℕ } →
        Tendsto (fun k ↦ x (k + 1) - x k) atTop (𝓝 0) := by
  refine Iff.mp ?_ trivial
  constructor
  · intro htrue
    refine ⟨1 / 10, by norm_num, fun q hq hqε x hx hrange ↦ ?_⟩
    have hqbound : q < 11 / 10 := by norm_num at hqε ⊢; exact hqε
    have hsq1 : 1 < q ^ 2 := by nlinarith
    have hsqbound : q ^ 2 < 121 / 100 := by nlinarith
    have hsq2 : q ^ 2 < 2 := by nlinarith
    have hsmall : SmallDisjointDifferences (q ^ 2) :=
      smallDisjointDifferences_of_smallSpectrumDifferences
        (hspectral (q ^ 2) hsq1 hsqbound)
    have hdense : EventuallyRightDense (Spectrum q) :=
      spectrum_eventuallyRightDense_of_square_smallDifferences hq hsq2 hsmall
    have hrange' : Set.range x = Spectrum q := by
      rw [hrange]
      ext a
      simp only [Spectrum, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨S, rfl⟩
        exact ⟨S, rfl⟩
      · rintro ⟨S, rfl⟩
        exact ⟨S, rfl⟩
    exact gaps_tendsto_zero_of_eventuallyRightDense hx hrange'
      (strictMono_spectrum_tendsto_atTop hq hx hrange') hdense
  · intro h
    trivial

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos1096/Erdos1096Smyth.lean` -/

section
open Filter Set Polynomial
open scoped BigOperators Pointwise Topology ComplexConjugate

noncomputable section

private def diskMobius (c z : ℂ) : ℂ :=
  (z - c) / (1 - (starRingEnd ℂ) c * z)

private lemma diskMobius_norm_le_one {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖diskMobius c z‖ ≤ 1 := by
  have hden : 1 - (starRingEnd ℂ) c * z ≠ 0 := by
    intro h
    have heq : (1 : ℂ) = (starRingEnd ℂ) c * z := sub_eq_zero.mp h
    have : (1 : ℝ) = ‖c‖ * ‖z‖ := by
      simpa using congrArg norm heq
    have hmul : ‖c‖ * ‖z‖ < 1 :=
      (mul_le_mul_of_nonneg_left hz (norm_nonneg c)).trans_lt (by simpa using hc)
    linarith
  rw [diskMobius, norm_div, div_le_one (norm_pos_iff.mpr hden)]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_sub, Complex.normSq_sub]
  simp only [Complex.normSq_one, Complex.normSq_mul, Complex.normSq_conj,
    Complex.mul_re, Complex.one_re, Complex.one_im, Complex.conj_re,
    Complex.conj_im, mul_one, zero_mul, sub_zero]
  have hc2 : ‖c‖ ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hc) (add_pos_of_nonneg_of_pos (norm_nonneg c) zero_lt_one)]
  have hz2 : ‖z‖ ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz) (add_nonneg (norm_nonneg z) zero_le_one)]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  nlinarith [mul_nonneg (sub_nonneg.mpr hc2.le) (sub_nonneg.mpr hz2)]

private lemma diskMobius_norm_eq_one {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ = 1) :
    ‖diskMobius c z‖ = 1 := by
  have hden : 1 - (starRingEnd ℂ) c * z ≠ 0 := by
    intro h
    have heq : (1 : ℂ) = (starRingEnd ℂ) c * z := sub_eq_zero.mp h
    have : (1 : ℝ) = ‖c‖ * ‖z‖ := by simpa using congrArg norm heq
    rw [hz, mul_one] at this
    linarith
  rw [diskMobius, norm_div]
  apply (div_eq_one_iff_eq (norm_ne_zero_iff.mpr hden)).2
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_conj,
    Complex.normSq_one, Complex.mul_re, Complex.one_re, Complex.one_im,
    Complex.conj_re, Complex.conj_im, mul_one, zero_mul, sub_zero]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hz]
  ring

private lemma diskMobius_sub (c u v : ℂ)
    (hu : 1 - (starRingEnd ℂ) c * u ≠ 0)
    (hv : 1 - (starRingEnd ℂ) c * v ≠ 0) :
    diskMobius c u - diskMobius c v =
      (1 - (Complex.normSq c : ℂ)) * (u - v) /
        ((1 - (starRingEnd ℂ) c * u) * (1 - (starRingEnd ℂ) c * v)) := by
  have hu' : 1 - u * (starRingEnd ℂ) c ≠ 0 := by simpa [mul_comm] using hu
  have hv' : 1 - v * (starRingEnd ℂ) c ≠ 0 := by simpa [mul_comm] using hv
  rw [diskMobius, diskMobius]
  rw [Complex.normSq_eq_conj_mul_self]
  field_simp [hu, hv, hu', hv']
  ring

private lemma norm_le_one_of_schwarz_factor {H J : ℂ → ℂ} {k : ℕ} (hk : 0 < k)
    (hHdiff : DifferentiableOn ℂ H (Metric.ball 0 1))
    (hHmap : MapsTo H (Metric.ball 0 1) (Metric.closedBall 0 1))
    (hH0 : H 0 = 0) (hJcont : ContinuousAt J 0)
    (hfactor : ∀ z ∈ Metric.ball (0 : ℂ) 1, H z = z ^ k * J z) :
    ‖J 0‖ ≤ 1 := by
  have hpred : k - 1 < k := Nat.sub_lt hk zero_lt_one
  have hsmall : (H · - H 0) =o[𝓝 (0 : ℂ)] (fun z ↦ z ^ (k - 1)) := by
    have hpow := Asymptotics.isLittleO_pow_pow (𝕜 := ℂ) hpred
    have hprod := hpow.mul_isBigO hJcont.isBigO
    refine hprod.congr' ?_ ?_
    · filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
      rw [hH0, sub_zero, hfactor z hz]
    · exact Eventually.of_forall (fun z ↦ by simp)
  have hbound {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      ‖H z‖ ≤ ‖z‖ ^ k := by
    have hsmall' : (H · - H 0) =o[𝓝 (0 : ℂ)] (fun z ↦ ‖z‖ ^ (k - 1)) := by
      simpa [norm_pow] using hsmall.norm_right
    have hHmap' : MapsTo H (Metric.ball (0 : ℂ) 1) (Metric.closedBall (H 0) 1) := by
      simpa [hH0] using hHmap
    have hsmall'' : (H · - H 0) =o[𝓝 (0 : ℂ)]
        (fun w ↦ ‖w - 0‖ ^ (k - 1)) := by simpa using hsmall'
    have hs := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
      (n := k - 1) hHdiff hHmap' hsmall'' hz
    simpa [hH0, Nat.sub_add_cancel hk, Complex.dist_eq, norm_pow] using hs
  have htend : Tendsto (fun z ↦ ‖J z‖) (𝓝[≠] (0 : ℂ)) (𝓝 ‖J 0‖) :=
    hJcont.norm.tendsto.mono_left inf_le_left
  apply le_of_tendsto htend
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with z hz0 hzball
  have hz_ne : z ≠ 0 := by simpa using hz0
  have hzpos : 0 < ‖z‖ ^ k := pow_pos (norm_pos_iff.mpr hz_ne) _
  have := hbound hzball
  rw [hfactor z hzball, norm_mul, norm_pow] at this
  exact le_of_mul_le_mul_left (by simpa only [mul_one] using this) hzpos

private lemma leading_factor_bound {f g j : ℂ → ℂ} {c : ℂ} {k : ℕ}
    (hc : ‖c‖ < 1) (hk : 0 < k)
    (hfdiff : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hgdiff : DifferentiableOn ℂ g (Metric.ball 0 1))
    (hfmap : MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 1))
    (hgmap : MapsTo g (Metric.ball 0 1) (Metric.closedBall 0 1))
    (hf0 : f 0 = c) (hg0 : g 0 = c) (hjcont : ContinuousAt j 0)
    (hfactor : ∀ z ∈ Metric.ball (0 : ℂ) 1, f z - g z = z ^ k * j z) :
    ‖j 0‖ ≤ 2 * (1 - ‖c‖ ^ 2) := by
  let F : ℂ → ℂ := fun z ↦ diskMobius c (f z)
  let G : ℂ → ℂ := fun z ↦ diskMobius c (g z)
  let H : ℂ → ℂ := fun z ↦ (F z - G z) / 2
  let J : ℂ → ℂ := fun z ↦
    ((1 - (Complex.normSq c : ℂ)) * j z) /
      (2 * ((1 - (starRingEnd ℂ) c * f z) * (1 - (starRingEnd ℂ) c * g z)))
  have hden_f {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      1 - (starRingEnd ℂ) c * f z ≠ 0 := by
    intro heq
    have heq' : (1 : ℂ) = (starRingEnd ℂ) c * f z := sub_eq_zero.mp heq
    have hone : (1 : ℝ) = ‖c‖ * ‖f z‖ := by simpa using congrArg norm heq'
    have hfz : ‖f z‖ ≤ 1 := by simpa using hfmap hz
    have : ‖c‖ * ‖f z‖ < 1 :=
      (mul_le_mul_of_nonneg_left hfz (norm_nonneg c)).trans_lt (by simpa using hc)
    linarith
  have hden_g {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      1 - (starRingEnd ℂ) c * g z ≠ 0 := by
    intro heq
    have heq' : (1 : ℂ) = (starRingEnd ℂ) c * g z := sub_eq_zero.mp heq
    have hone : (1 : ℝ) = ‖c‖ * ‖g z‖ := by simpa using congrArg norm heq'
    have hgz : ‖g z‖ ≤ 1 := by simpa using hgmap hz
    have : ‖c‖ * ‖g z‖ < 1 :=
      (mul_le_mul_of_nonneg_left hgz (norm_nonneg c)).trans_lt (by simpa using hc)
    linarith
  have hHdiff : DifferentiableOn ℂ H (Metric.ball 0 1) := by
    intro z hz
    have hfz : DifferentiableAt ℂ f z :=
      (hfdiff z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    have hgz : DifferentiableAt ℂ g z :=
      (hgdiff z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    have hFdiff : DifferentiableAt ℂ F z := by
      dsimp only [F, diskMobius]
      exact (hfz.sub (differentiableAt_const c)).div
        ((differentiableAt_const (1 : ℂ)).sub
          ((differentiableAt_const ((starRingEnd ℂ) c)).mul hfz)) (hden_f hz)
    have hGdiff : DifferentiableAt ℂ G z := by
      dsimp only [G, diskMobius]
      exact (hgz.sub (differentiableAt_const c)).div
        ((differentiableAt_const (1 : ℂ)).sub
          ((differentiableAt_const ((starRingEnd ℂ) c)).mul hgz)) (hden_g hz)
    exact (hFdiff.sub hGdiff).div_const 2 |>.differentiableWithinAt
  have hHmap : MapsTo H (Metric.ball 0 1) (Metric.closedBall 0 1) := by
    intro z hz
    have hF : ‖F z‖ ≤ 1 := diskMobius_norm_le_one hc (by simpa using hfmap hz)
    have hG : ‖G z‖ ≤ 1 := diskMobius_norm_le_one hc (by simpa using hgmap hz)
    simp only [Metric.mem_closedBall, dist_zero_right, H, norm_div]
    calc
      ‖F z - G z‖ / ‖(2 : ℂ)‖ ≤ (‖F z‖ + ‖G z‖) / 2 := by
        norm_num
        gcongr
        exact norm_sub_le _ _
      _ ≤ 1 := by linarith
  have hH0 : H 0 = 0 := by simp [H, F, G, hf0, hg0]
  have hpos : 0 < 1 - ‖c‖ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hc) (add_pos_of_nonneg_of_pos (norm_nonneg c) zero_lt_one)]
  have hJcont : ContinuousAt J 0 := by
    have hden0 : 1 - (starRingEnd ℂ) c * c ≠ 0 := by
      rw [← Complex.normSq_eq_conj_mul_self]
      have hr : (1 : ℝ) - Complex.normSq c ≠ 0 := by
        rw [Complex.normSq_eq_norm_sq]
        exact ne_of_gt hpos
      exact_mod_cast hr
    have hfcont : ContinuousAt f 0 :=
      ((hfdiff 0 (by simp)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (by simp))).continuousAt
    have hgcont : ContinuousAt g 0 :=
      ((hgdiff 0 (by simp)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (by simp))).continuousAt
    dsimp only [J]
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa [hf0, hg0, ← Complex.normSq_eq_conj_mul_self] using
        mul_ne_zero (OfNat.ofNat_ne_zero 2) (mul_ne_zero hden0 hden0)
  have hHJ : ∀ z ∈ Metric.ball (0 : ℂ) 1, H z = z ^ k * J z := by
    intro z hz
    dsimp only [H, F, G]
    rw [diskMobius_sub c (f z) (g z) (hden_f hz) (hden_g hz), hfactor z hz]
    dsimp only [J]
    field_simp
  have hJ := norm_le_one_of_schwarz_factor hk hHdiff hHmap hH0 hJcont hHJ
  have hnormsq : Complex.normSq c = ‖c‖ ^ 2 := Complex.normSq_eq_norm_sq c
  have hJ0 : ‖J 0‖ = ‖j 0‖ / (2 * (1 - ‖c‖ ^ 2)) := by
    dsimp only [J]
    rw [hf0, hg0, ← Complex.normSq_eq_conj_mul_self]
    have hone : (1 : ℂ) - (Complex.normSq c : ℂ) =
        ((1 - ‖c‖ ^ 2 : ℝ) : ℂ) := by
      norm_cast
      rw [hnormsq]
    rw [hone]
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    norm_num
    field_simp
  rw [hJ0] at hJ
  exact (div_le_one (mul_pos two_pos hpos)).mp hJ

def IsPisot1096 (θ : ℝ) : Prop :=
  1 < θ ∧ IsIntegral ℤ θ ∧
    ∀ z : ℂ, ((minpoly ℤ θ).map (algebraMap ℤ ℂ)).eval z = 0 →
      z ≠ (θ : ℂ) → ‖z‖ < 1

private def iterDivX {R : Type*} [Semiring R] (k : ℕ) (p : R[X]) : R[X] :=
  (Polynomial.divX^[k]) p

private lemma coeff_iterDivX {R : Type*} [Semiring R] (k n : ℕ) (p : R[X]) :
    (iterDivX k p).coeff n = p.coeff (n + k) := by
  induction k generalizing n with
  | zero => simp [iterDivX]
  | succ k ih =>
      rw [iterDivX, Function.iterate_succ_apply', Polynomial.coeff_divX]
      change (iterDivX k p).coeff (n + 1) = _
      rw [ih]
      congr 1
      omega

private lemma eq_X_pow_mul_iterDivX {R : Type*} [CommSemiring R] (k : ℕ) (p : R[X])
    (hzero : ∀ n < k, p.coeff n = 0) :
    p = X ^ k * iterDivX k p := by
  ext n
  rw [coeff_X_pow_mul']
  by_cases hnk : k ≤ n
  · rw [if_pos hnk, coeff_iterDivX]
    congr 1
    omega
  · rw [if_neg hnk]
    exact hzero n (lt_of_not_ge hnk)

private lemma map_reverse_of_injective {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (hf : Function.Injective f) (p : R[X]) :
    p.reverse.map f = (p.map f).reverse := by
  ext n
  rw [coeff_map, coeff_reverse, coeff_reverse, coeff_map,
    natDegree_map_eq_of_injective hf]

private lemma norm_eval_map_int_conj (r : ℤ[X]) (z : ℂ) :
    ‖(r.map (algebraMap ℤ ℂ)).eval (starRingEnd ℂ z)‖ =
      ‖(r.map (algebraMap ℤ ℂ)).eval z‖ := by
  let rR : ℝ[X] := r.map (algebraMap ℤ ℝ)
  have hcomp : (algebraMap ℤ ℂ) = (algebraMap ℝ ℂ).comp (algebraMap ℤ ℝ) := by
    ext n
    simp
  have hleft : (r.map (algebraMap ℤ ℂ)).eval (starRingEnd ℂ z) =
      aeval (starRingEnd ℂ z) rR := by
    rw [hcomp]
    simp [rR, aeval_def, eval_map, eval₂_map]
  have hright : (r.map (algebraMap ℤ ℂ)).eval z = aeval z rR := by
    rw [hcomp]
    simp [rR, aeval_def, eval_map, eval₂_map]
  rw [hleft, hright, Polynomial.aeval_conj]
  exact RCLike.norm_conj _

private lemma reverse_X_sub_C (a : ℂ) :
    (X - C a).reverse = 1 - C a * X := by
  have hrevX : (X : ℂ[X]).reverse = 1 := by
    rw [← one_mul X, ← C_1, reverse_mul_X, reverse_C, C_1]
  calc
    (X - C a).reverse = (X + C (-a)).reverse := by rw [C_neg, sub_eq_add_neg]
    _ = X.reverse + C (-a) * X ^ X.natDegree := reverse_add_C X (-a)
    _ = 1 + C (-a) * X := by rw [hrevX, natDegree_X, pow_one]
    _ = 1 - C a * X := by rw [C_neg, neg_mul, sub_eq_add_neg]

private lemma reverse_prod_X_sub_C (s : Multiset ℂ) :
    ((s.map (fun a ↦ X - C a)).prod).reverse =
      (s.map (fun a ↦ 1 - C a * X)).prod := by
  induction s using Multiset.induction_on with
  | empty =>
      change (1 : ℂ[X]).reverse = 1
      rw [← C_1, reverse_C, C_1]
  | @cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [reverse_mul_of_domain, reverse_X_sub_C, ih]

private lemma multiset_prod_le_one {s : Multiset ℝ}
    (h0 : ∀ a ∈ s, 0 ≤ a) (h1 : ∀ a ∈ s, a ≤ 1) : s.prod ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.prod_cons]
      have ha0 : 0 ≤ a := h0 a (by simp)
      have ha1 : a ≤ 1 := h1 a (by simp)
      have hs0 : ∀ b ∈ s, 0 ≤ b := by
        intro b hb
        exact h0 b (by simp [hb])
      have hs1 : ∀ b ∈ s, b ≤ 1 := by
        intro b hb
        exact h1 b (by simp [hb])
      have hsprod := ih hs0 hs1
      have hsprod0 : 0 ≤ s.prod := Multiset.prod_nonneg hs0
      nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hsprod)]

private lemma norm_multiset_prod (s : Multiset ℂ) :
    ‖s.prod‖ = (s.map norm).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp [ih]

private lemma pisot_minpoly_coeff_zero_abs_eq_one
    {θ : ℝ} (hθ1 : 1 < θ) (hθsmall : θ < 11 / 10)
    (hθint : IsIntegral ℤ θ)
    (hpsep : ((minpoly ℤ θ).map (algebraMap ℤ ℂ)).Separable)
    (hother : ∀ z : ℂ, ((minpoly ℤ θ).map (algebraMap ℤ ℂ)).eval z = 0 →
      z ≠ (θ : ℂ) → ‖z‖ < 1) :
    |(minpoly ℤ θ).coeff 0| = 1 := by
  let p : ℤ[X] := minpoly ℤ θ
  let P : ℂ[X] := p.map (algebraMap ℤ ℂ)
  let θc : ℂ := (θ : ℂ)
  let roots : Multiset ℂ := P.roots
  have hpmonic : p.Monic := minpoly.monic hθint
  have hPmonic : P.Monic := hpmonic.map _
  have hPne : P ≠ 0 := hPmonic.ne_zero
  have hθroot : θc ∈ roots := by
    rw [show roots = P.roots by rfl, mem_roots hPne]
    change (p.map (algebraMap ℤ ℂ)).eval (θ : ℂ) = 0
    have hr : (p.map (algebraMap ℤ ℝ)).eval θ = 0 := by
      simpa [p, ← eval_map_algebraMap] using minpoly.aeval ℤ θ
    have hc := congrArg (algebraMap ℝ ℂ) hr
    simpa [eval_map, eval₂_map] using hc
  let others : Multiset ℂ := roots.erase θc
  have hroots : roots = θc ::ₘ others := (Multiset.cons_erase hθroot).symm
  have hnodup : roots.Nodup := by
    apply nodup_roots
    simpa [P, p] using hpsep
  have hother_mem {z : ℂ} (hz : z ∈ others) : ‖z‖ < 1 := by
    apply hother z
    · exact (mem_roots hPne).mp (Multiset.mem_of_mem_erase hz)
    · intro h
      subst z
      exact hnodup.notMem_erase hz
  have hothers_norm : ‖others.prod‖ ≤ 1 := by
    rw [norm_multiset_prod]
    apply multiset_prod_le_one
    · intro a ha
      rw [Multiset.mem_map] at ha
      obtain ⟨z, -, rfl⟩ := ha
      exact norm_nonneg z
    · intro a ha
      rw [Multiset.mem_map] at ha
      obtain ⟨z, hz, rfl⟩ := ha
      exact (hother_mem hz).le
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hcoeff := hsplit.coeff_zero_eq_prod_roots_of_monic hPmonic
  have hcoeffnorm := congrArg norm hcoeff
  have hp0lt : |p.coeff 0| < 2 := by
    have hθpos : 0 < θ := lt_trans zero_lt_one hθ1
    rw [show P.coeff 0 = (p.coeff 0 : ℂ) by simp [P]] at hcoeffnorm
    rw [show roots.prod = θc * others.prod by rw [hroots]; simp] at hcoeffnorm
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at hcoeffnorm
    have hθnorm : ‖θc‖ = θ := by
      simp [θc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθpos]
    have hp0norm : ‖(p.coeff 0 : ℂ)‖ = |p.coeff 0| := by
      simp [Complex.norm_intCast]
    rw [hθnorm, hp0norm] at hcoeffnorm
    have hp0ltR : ((|p.coeff 0| : ℤ) : ℝ) < 2 := by
      rw [hcoeffnorm]
      have hθ2 : θ < (2 : ℝ) := by nlinarith
      simpa using (mul_le_mul_of_nonneg_left hothers_norm hθpos.le).trans_lt
        (show θ * 1 < (2 : ℝ) by simpa using hθ2)
    exact_mod_cast hp0ltR
  have hp0ne : p.coeff 0 ≠ 0 := by
    have hθintQ : IsIntegral ℚ θ := hθint.tower_top
    have hq0 : (minpoly ℚ θ).coeff 0 ≠ 0 :=
      minpoly.coeff_zero_ne_zero hθintQ (ne_of_gt (lt_trans zero_lt_one hθ1))
    have hpQ : minpoly ℚ θ = p.map (algebraMap ℤ ℚ) := by
      simpa [p] using
        (minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) (K := ℚ) hθint)
    rw [hpQ, coeff_map] at hq0
    exact fun hp0 ↦ hq0 (by simp [hp0])
  have hp0pos : (0 : ℤ) < |p.coeff 0| := abs_pos.mpr hp0ne
  have hp0one : |p.coeff 0| = 1 := by omega
  simpa [p] using hp0one

private lemma minpoly_int_map_complex_separable {θ : ℝ} (hθint : IsIntegral ℤ θ) :
    ((minpoly ℤ θ).map (algebraMap ℤ ℂ)).Separable := by
  have hθintQ : IsIntegral ℚ θ := hθint.tower_top
  have hsepQ : (minpoly ℚ θ).Separable := (minpoly.irreducible hθintQ).separable
  have hsepC := hsepQ.map (f := algebraMap ℚ ℂ)
  have hpQ : minpoly ℚ θ = (minpoly ℤ θ).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) (K := ℚ) hθint
  rw [hpQ, Polynomial.map_map] at hsepC
  convert hsepC using 1
  ext n
  simp

private lemma reciprocal_pisot_not_lt
    {θ : ℝ} (hθ1 : 1 < θ) (hθsmall : θ < 11 / 10)
    (p : ℤ[X]) (hpmonic : p.Monic)
    (hproot : (p.map (algebraMap ℤ ℂ)).eval (θ : ℂ) = 0)
    (hpsep : (p.map (algebraMap ℤ ℂ)).Separable)
    (hother : ∀ z : ℂ, (p.map (algebraMap ℤ ℂ)).eval z = 0 →
      z ≠ (θ : ℂ) → ‖z‖ < 1)
    (hp0 : |p.coeff 0| = 1)
    (hrecip : C (p.coeff 0) * p - p.reverse = 0) : False := by
  let P : ℂ[X] := p.map (algebraMap ℤ ℂ)
  let θc : ℂ := (θ : ℂ)
  let c : ℂ := ((θ⁻¹ : ℝ) : ℂ)
  let roots : Multiset ℂ := P.roots
  have hPmonic : P.Monic := hpmonic.map _
  have hPne : P ≠ 0 := hPmonic.ne_zero
  have hθroot : θc ∈ roots := by
    rw [show roots = P.roots by rfl, mem_roots hPne]
    exact hproot
  have hnodup : roots.Nodup := nodup_roots hpsep
  have hp0ne : p.coeff 0 ≠ 0 := by
    intro h
    rw [h, abs_zero] at hp0
    omega
  have hp0neC : (p.coeff 0 : ℂ) ≠ 0 := by exact_mod_cast hp0ne
  have hrecipC : P.reverse = C (p.coeff 0 : ℂ) * P := by
    have hm := congrArg (fun r : ℤ[X] ↦ r.map (algebraMap ℤ ℂ)) hrecip
    simp only [Polynomial.map_sub, Polynomial.map_mul, map_C, map_zero] at hm
    rw [map_reverse_of_injective (algebraMap ℤ ℂ)
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℂ))] at hm
    have hm' : C (p.coeff 0 : ℂ) * P - P.reverse = 0 := by
      convert hm using 1 <;> simp [P]
    exact sub_eq_zero.mp hm' |>.symm
  have hroot_ne_zero {z : ℂ} (hz : z ∈ roots) : z ≠ 0 := by
    intro hz0
    subst z
    have hzero : P.eval 0 = 0 := (mem_roots hPne).mp hz
    have : (p.coeff 0 : ℂ) = 0 := by
      simpa [P, ← coeff_zero_eq_eval_zero] using hzero
    exact hp0neC this
  have hinv_root {z : ℂ} (hz : z ∈ roots) : z⁻¹ ∈ roots := by
    have hz0 := hroot_ne_zero hz
    letI : Invertible z := invertibleOfNonzero hz0
    have hzroot : P.eval z = 0 := (mem_roots hPne).mp hz
    have hr : P.reverse.eval z⁻¹ = 0 := by
      have := (eval₂_reverse_eq_zero_iff (RingHom.id ℂ) z P).2 hzroot
      simpa using this
    rw [hrecipC] at hr
    simp only [eval_mul, eval_C] at hr
    have : P.eval z⁻¹ = 0 := (mul_eq_zero.mp hr).resolve_left hp0neC
    exact (mem_roots hPne).2 this
  have hcroot : c ∈ roots := by
    simpa [c, θc] using hinv_root hθroot
  have hθpos : 0 < θ := lt_trans zero_lt_one hθ1
  have hcne : c ≠ θc := by
    intro h
    have hr : θ⁻¹ = θ := by
      dsimp only [c, θc] at h
      exact_mod_cast h
    have hinvlt : θ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hθ1
    linarith
  have hclass {z : ℂ} (hz : z ∈ roots) : z = θc ∨ z = c := by
    by_cases hzθ : z = θc
    · exact Or.inl hzθ
    · have hznorm : ‖z‖ < 1 := hother z ((mem_roots hPne).mp hz) hzθ
      have hzinvroot := hinv_root hz
      have hzinvnorm : 1 < ‖z⁻¹‖ := by
        rw [norm_inv]
        exact (one_lt_inv₀ (norm_pos_iff.mpr (hroot_ne_zero hz))).2 hznorm
      have hzinvθ : z⁻¹ = θc := by
        by_contra hne
        have := hother z⁻¹ ((mem_roots hPne).mp hzinvroot) hne
        linarith
      right
      apply inv_injective
      simpa [θc, c] using hzinvθ
  have hroots_eq : roots = {θc, c} := by
    apply (Multiset.Nodup.ext hnodup (by simp [hcne.symm])).2
    intro z
    constructor
    · intro hz
      rcases hclass hz with rfl | rfl <;> simp
    · intro hz
      have hz' : z = θc ∨ z = c := by simpa using hz
      rcases hz' with rfl | rfl
      · exact hθroot
      · exact hcroot
  have hPprod : P = (roots.map (fun z ↦ X - C z)).prod :=
    (IsAlgClosed.splits P).eq_prod_roots_of_monic hPmonic
  have hPfactor : P = (X - C θc) * (X - C c) := by
    rw [hPprod, hroots_eq]
    simp
  have hcoeff1 := congrArg (fun r : ℂ[X] ↦ r.coeff 1) hPfactor
  have htrace : θ + θ⁻¹ = -(p.coeff 1 : ℝ) := by
    have hpoly : (X - C θc) * (X - C c) =
        X ^ 2 - C (θc + c) * X + C (θc * c) := by
      simp only [map_add, map_mul]
      ring
    rw [hpoly] at hcoeff1
    apply_fun Complex.re at hcoeff1
    have hh : (p.coeff 1 : ℝ) = -θ⁻¹ + -θ := by
      simpa [P, θc, c] using hcoeff1
    linarith
  have hinvpos : 0 < θ⁻¹ := inv_pos.mpr hθpos
  have hmul : θ * θ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hθpos)
  have hlower : 2 < θ + θ⁻¹ := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hθ1)]
  have hinvlt : θ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hθ1
  have hupper : θ + θ⁻¹ < 3 := by nlinarith
  have hlowerZ : (2 : ℤ) < -(p.coeff 1) := by
    exact_mod_cast (htrace ▸ hlower)
  have hupperZ : -(p.coeff 1) < (3 : ℤ) := by
    exact_mod_cast (htrace ▸ hupper)
  omega

private lemma nonreciprocal_pisot_not_lt
    {θ : ℝ} (hθ1 : 1 < θ) (hθsmall : θ < 11 / 10)
    (p : ℤ[X]) (hpmonic : p.Monic)
    (hproot : (p.map (algebraMap ℤ ℂ)).eval (θ : ℂ) = 0)
    (hpsep : (p.map (algebraMap ℤ ℂ)).Separable)
    (hother : ∀ z : ℂ, (p.map (algebraMap ℤ ℂ)).eval z = 0 →
      z ≠ (θ : ℂ) → ‖z‖ < 1)
    (hp0 : |p.coeff 0| = 1)
    (hrecip : C (p.coeff 0) * p - p.reverse ≠ 0) : False := by
  let P : ℂ[X] := p.map (algebraMap ℤ ℂ)
  let θc : ℂ := (θ : ℂ)
  let c : ℂ := ((θ⁻¹ : ℝ) : ℂ)
  let roots : Multiset ℂ := P.roots
  have hPmonic : P.Monic := hpmonic.map _
  have hPne : P ≠ 0 := hPmonic.ne_zero
  have hθroot : θc ∈ roots := by
    change θc ∈ P.roots
    rw [mem_roots hPne]
    exact hproot
  let others : Multiset ℂ := roots.erase θc
  have hroots : roots = θc ::ₘ others := (Multiset.cons_erase hθroot).symm
  have hnodup : roots.Nodup := nodup_roots hpsep
  have hother_mem {z : ℂ} (hz : z ∈ others) : ‖z‖ < 1 := by
    have hzroots : z ∈ roots := Multiset.mem_of_mem_erase hz
    have hzne : z ≠ θc := by
      intro h
      subst z
      exact hnodup.notMem_erase hz
    apply hother z
    · exact (mem_roots hPne).mp hzroots
    · exact hzne
  let RP : ℂ[X] := (others.map (fun z ↦ 1 - C z * X)).prod
  have hPprod : P = (roots.map (fun z ↦ X - C z)).prod :=
    (IsAlgClosed.splits P).eq_prod_roots_of_monic hPmonic
  have hPrev : P.reverse = (roots.map (fun z ↦ 1 - C z * X)).prod := by
    rw [hPprod, reverse_prod_X_sub_C]
  have hPrev_factor : P.reverse = (1 - C θc * X) * RP := by
    rw [hPrev, hroots]
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rfl
  have hRP_eval (z : ℂ) : RP.eval z = (others.map (fun w ↦ 1 - w * z)).prod := by
    dsimp only [RP]
    induction others using Multiset.induction_on with
    | empty => simp
    | @cons a s ih => simp [ih]
  have hθpos : 0 < θ := lt_trans zero_lt_one hθ1
  have hθc0 : θc ≠ 0 := by
    change (θ : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt hθpos)
  have hc_norm : ‖c‖ = θ⁻¹ := by
    simp [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθpos]
  have hc_lt : ‖c‖ < 1 := by
    rw [hc_norm]
    exact inv_lt_one_of_one_lt₀ hθ1
  have hRP_ne {z : ℂ} (hz : ‖z‖ ≤ 1) : RP.eval z ≠ 0 := by
    rw [hRP_eval]
    apply Multiset.prod_ne_zero
    intro hmem
    rw [Multiset.mem_map] at hmem
    obtain ⟨b, hb, heq⟩ := hmem
    have heq : 1 - b * z = 0 := heq
    have hone : (1 : ℂ) = b * z := sub_eq_zero.mp heq
    have hone_norm : (1 : ℝ) = ‖b‖ * ‖z‖ := by simpa using congrArg norm hone
    have hlt : ‖b‖ * ‖z‖ < 1 :=
      (mul_le_mul_of_nonneg_left hz (norm_nonneg b)).trans_lt (by simpa using hother_mem hb)
    linarith
  have hcz_ne {z : ℂ} (hz : ‖z‖ ≤ 1) : 1 - c * z ≠ 0 := by
    intro heq
    have hone : (1 : ℂ) = c * z := sub_eq_zero.mp heq
    have hone_norm : (1 : ℝ) = ‖c‖ * ‖z‖ := by simpa using congrArg norm hone
    have hlt : ‖c‖ * ‖z‖ < 1 :=
      (mul_le_mul_of_nonneg_left hz (norm_nonneg c)).trans_lt (by simpa using hc_lt)
    linarith
  let D : ℂ → ℂ := fun z ↦ (-θc) * RP.eval z * (1 - c * z)
  have hD_ne {z : ℂ} (hz : ‖z‖ ≤ 1) : D z ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hθc0) (hRP_ne hz)) (hcz_ne hz)
  have hcθ : θc * c = 1 := by
    dsimp only [θc, c]
    norm_cast
    exact mul_inv_cancel₀ (ne_of_gt (lt_trans zero_lt_one hθ1))
  have hPrev_eval (z : ℂ) : P.reverse.eval z = (-θc) * (z - c) * RP.eval z := by
    rw [hPrev_factor]
    simp only [eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_C_mul]
    rw [show 1 - θc * z = (-θc) * (z - c) by
      calc
        1 - θc * z = θc * c - θc * z := by rw [hcθ]
        _ = (-θc) * (z - c) := by ring]
  have hp0sqZ : p.coeff 0 * p.coeff 0 = 1 := by
    have := congrArg (fun n : ℤ ↦ n * n) hp0
    simpa using this
  have hp0sqC : ((p.coeff 0 : ℂ) * (p.coeff 0 : ℂ)) = 1 := by exact_mod_cast hp0sqZ
  let f : ℂ → ℂ := fun z ↦ ((p.coeff 0 : ℂ) * P.eval z) / D z
  let g : ℂ → ℂ := fun z ↦ diskMobius c z
  let NZ : ℤ[X] := C (p.coeff 0) * p - p.reverse
  let k : ℕ := NZ.natTrailingDegree
  let TZ : ℤ[X] := iterDivX k NZ
  let T : ℂ[X] := TZ.map (algebraMap ℤ ℂ)
  let j : ℂ → ℂ := fun z ↦ T.eval z / D z
  have hNZ : NZ ≠ 0 := by simpa [NZ] using hrecip
  have hNZ0 : NZ.coeff 0 = 0 := by
    simp [NZ, hp0sqZ, hpmonic.leadingCoeff]
  have hk : 0 < k := by
    have hkne : k ≠ 0 := by
      intro hk0
      have hcoeff := (coeff_natTrailingDegree_ne_zero (p := NZ)).mpr hNZ
      change NZ.natTrailingDegree = 0 at hk0
      rw [hk0, hNZ0] at hcoeff
      exact hcoeff rfl
    omega
  have hNZfactor : NZ = X ^ k * TZ := by
    exact eq_X_pow_mul_iterDivX k NZ (fun n hn ↦ coeff_eq_zero_of_lt_natTrailingDegree hn)
  have hmapNZ : NZ.map (algebraMap ℤ ℂ) = C (p.coeff 0 : ℂ) * P - P.reverse := by
    calc
      NZ.map (algebraMap ℤ ℂ) =
          (C (p.coeff 0) * p - p.reverse).map (algebraMap ℤ ℂ) := rfl
      _ = C (p.coeff 0 : ℂ) * p.map (algebraMap ℤ ℂ) -
          (p.reverse.map (algebraMap ℤ ℂ)) := by
            rw [Polynomial.map_sub, Polynomial.map_mul, map_C]
            congr 2
      _ = C (p.coeff 0 : ℂ) * P - P.reverse := by
        rw [map_reverse_of_injective (algebraMap ℤ ℂ)
          (Int.cast_injective : Function.Injective (algebraMap ℤ ℂ))]
  have hfg_factor : ∀ z ∈ Metric.ball (0 : ℂ) 1, f z - g z = z ^ k * j z := by
    intro z hz
    have hzle : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
    have hD := hD_ne hzle
    have hden_g : 1 - c * z ≠ 0 := hcz_ne hzle
    have hN_eval : ((C (p.coeff 0 : ℂ) * P - P.reverse).eval z) = z ^ k * T.eval z := by
      rw [← hmapNZ, hNZfactor]
      dsimp only [T]
      simp
    have hN_eval' : (p.coeff 0 : ℂ) * P.eval z - P.reverse.eval z =
        z ^ k * T.eval z := by simpa using hN_eval
    dsimp only [f, g, j, diskMobius]
    rw [show (starRingEnd ℂ) c = c by simp [c]]
    have hg_as_reverse : (z - c) / (1 - c * z) = P.reverse.eval z / D z := by
      apply (div_eq_div_iff hden_g hD).2
      rw [hPrev_eval]
      dsimp only [D]
      ring
    rw [hg_as_reverse]
    calc
      (p.coeff 0 : ℂ) * P.eval z / D z - P.reverse.eval z / D z =
          ((p.coeff 0 : ℂ) * P.eval z - P.reverse.eval z) / D z := by
            rw [sub_div]
      _ = (z ^ k * T.eval z) / D z := by rw [hN_eval']
      _ = z ^ k * (T.eval z / D z) := by ring
  have hP0 : P.eval 0 = (p.coeff 0 : ℂ) := by
    change (p.map (algebraMap ℤ ℂ)).eval 0 = _
    rw [eval_map]
    simp
  have hRP0 : RP.eval 0 = 1 := by rw [hRP_eval]; simp
  have hD0 : D 0 = -θc := by simp [D, hRP0]
  have hf0 : f 0 = -c := by
    dsimp only [f]
    rw [hP0, hD0, hp0sqC]
    dsimp only [c, θc]
    norm_cast
    field_simp
  have hg0 : g 0 = -c := by simp [g, diskMobius]
  have hfdiff_closed : DifferentiableOn ℂ f (Metric.closedBall 0 1) := by
    intro z hz
    have hzle : ‖z‖ ≤ 1 := by simpa using hz
    dsimp only [f, D]
    apply DifferentiableWithinAt.div
    · exact (differentiableWithinAt_const (c := (p.coeff 0 : ℂ))).mul P.differentiableWithinAt
    · exact ((differentiableWithinAt_const (c := -θc)).mul RP.differentiableWithinAt).mul
        ((differentiableWithinAt_const (c := (1 : ℂ))).sub
          ((differentiableWithinAt_const (c := c)).mul differentiableWithinAt_id))
    · exact hD_ne hzle
  have hgdif : DifferentiableOn ℂ g (Metric.ball 0 1) := by
    intro z hz
    have hzle : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
    dsimp only [g, diskMobius]
    have hcstar : (starRingEnd ℂ) c = c := by simp [c]
    rw [hcstar]
    exact (differentiableWithinAt_id.sub (differentiableWithinAt_const (c := c))).div
      ((differentiableWithinAt_const (c := (1 : ℂ))).sub
        ((differentiableWithinAt_const (c := c)).mul differentiableWithinAt_id)) (hcz_ne hzle)
  have hgmap : MapsTo g (Metric.ball 0 1) (Metric.closedBall 0 1) := by
    intro z hz
    simpa [g, Metric.mem_closedBall, dist_zero_right] using
      diskMobius_norm_le_one hc_lt (mem_ball_zero_iff.mp hz).le
  have hboundary (z : ℂ) (hz : z ∈ frontier (Metric.ball (0 : ℂ) 1)) : ‖f z‖ ≤ 1 := by
    have hzsphere : z ∈ Metric.sphere (0 : ℂ) 1 := Metric.frontier_ball_subset_sphere hz
    have hznorm : ‖z‖ = 1 := by simpa using hzsphere
    have hD := hD_ne hznorm.le
    have hzg : 1 - c * z ≠ 0 := hcz_ne hznorm.le
    have hPnorm : ‖P.eval z‖ = ‖P.reverse.eval z‖ := by
      have hz0 : z ≠ 0 := by
        intro hz0
        rw [hz0, norm_zero] at hznorm
        norm_num at hznorm
      letI : Invertible z := invertibleOfNonzero hz0
      have hrev := eval₂_reverse_mul_pow (RingHom.id ℂ) z P
      have hrevnorm : ‖P.reverse.eval z⁻¹‖ = ‖P.eval z‖ := by
        simpa [hznorm] using congrArg norm hrev
      have hPrev_map : P.reverse = p.reverse.map (algebraMap ℤ ℂ) := by
        symm
        exact map_reverse_of_injective (algebraMap ℤ ℂ)
          (Int.cast_injective : Function.Injective (algebraMap ℤ ℂ)) p
      have hconjnorm : ‖P.reverse.eval z⁻¹‖ = ‖P.reverse.eval z‖ := by
        rw [Complex.inv_eq_conj hznorm, hPrev_map]
        exact norm_eval_map_int_conj p.reverse z
      exact hrevnorm.symm.trans hconjnorm
    have hg_norm : ‖g z‖ = 1 := by
      exact diskMobius_norm_eq_one hc_lt hznorm
    have hg_as_reverse : g z = P.reverse.eval z / D z := by
      dsimp only [g, diskMobius]
      rw [show (starRingEnd ℂ) c = c by simp [c]]
      apply (div_eq_div_iff hzg hD).2
      rw [hPrev_eval]
      dsimp only [D]
      ring
    have hDnorm : ‖D z‖ = ‖P.reverse.eval z‖ := by
      rw [hg_as_reverse, norm_div] at hg_norm
      exact (div_eq_one_iff_eq (norm_ne_zero_iff.mpr hD)).mp hg_norm |>.symm
    dsimp only [f]
    rw [norm_div, norm_mul]
    have hp0norm : ‖(p.coeff 0 : ℂ)‖ = 1 := by
      exact_mod_cast hp0
    rw [hp0norm, one_mul, hPnorm, hDnorm]
    exact div_self_le_one _
  have hfmap : MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 1) := by
    intro z hz
    have hle := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
      (hfdiff_closed.diffContOnCl_ball subset_rfl) hboundary (subset_closure hz)
    simpa using hle
  have hjcont : ContinuousAt j 0 := by
    have hD0ne : D 0 ≠ 0 := hD_ne (by simp)
    dsimp only [j, D]
    fun_prop
  have hlead := leading_factor_bound (c := -c) (by simpa using hc_lt) hk
    (hfdiff_closed.mono Metric.ball_subset_closedBall) hgdif hfmap hgmap hf0 hg0 hjcont hfg_factor
  have hTZ0 : TZ.coeff 0 = NZ.coeff k := by
    change (iterDivX k NZ).coeff 0 = NZ.coeff k
    simpa using coeff_iterDivX k 0 NZ
  have hTZ0ne : TZ.coeff 0 ≠ 0 := by
    rw [hTZ0]
    exact (coeff_natTrailingDegree_ne_zero (p := NZ)).mpr hNZ
  have hT0norm : 1 ≤ ‖T.eval 0‖ := by
    have hz : (1 : ℝ) ≤ |TZ.coeff 0| := by exact_mod_cast Int.one_le_abs hTZ0ne
    rw [← T.coeff_zero_eq_eval_zero, show T.coeff 0 = (TZ.coeff 0 : ℂ) by simp [T]]
    simpa [Complex.norm_intCast] using hz
  have hj0_lower : θ⁻¹ ≤ ‖j 0‖ := by
    dsimp only [j]
    rw [hD0, norm_div, norm_neg, show ‖θc‖ = θ by
      simp [θc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_trans zero_lt_one hθ1)]]
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right hT0norm hθpos.le
  have hineq : θ⁻¹ ≤ 2 * (1 - θ⁻¹ ^ 2) := by
    calc
      θ⁻¹ ≤ ‖j 0‖ := hj0_lower
      _ ≤ 2 * (1 - ‖c‖ ^ 2) := by simpa using hlead
      _ = 2 * (1 - θ⁻¹ ^ 2) := by rw [hc_norm]
  have hθpos : 0 < θ := lt_trans zero_lt_one hθ1
  have hθinv : θ⁻¹ > 10 / 11 := by
    rw [show (10 / 11 : ℝ) = (11 / 10 : ℝ)⁻¹ by norm_num]
    exact (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 11 / 10) hθpos).2 hθsmall
  have hθinv_le_one : θ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hθ1
  nlinarith

theorem no_pisot_below_eleven_tenths {θ : ℝ} (hθsmall : θ < 11 / 10) :
    ¬ IsPisot1096 θ := by
  rintro ⟨hθ1, hθint, hother⟩
  let p : ℤ[X] := minpoly ℤ θ
  have hpmonic : p.Monic := minpoly.monic hθint
  have hpsep : (p.map (algebraMap ℤ ℂ)).Separable := by
    simpa [p] using minpoly_int_map_complex_separable hθint
  have hproot : (p.map (algebraMap ℤ ℂ)).eval (θ : ℂ) = 0 := by
    have hr : (p.map (algebraMap ℤ ℝ)).eval θ = 0 := by
      simpa [p, ← eval_map_algebraMap] using minpoly.aeval ℤ θ
    have hc := congrArg (algebraMap ℝ ℂ) hr
    simpa [eval_map, eval₂_map] using hc
  have hp0 : |p.coeff 0| = 1 := by
    simpa [p] using
      pisot_minpoly_coeff_zero_abs_eq_one hθ1 hθsmall hθint hpsep hother
  by_cases hrecip : C (p.coeff 0) * p - p.reverse = 0
  · exact reciprocal_pisot_not_lt hθ1 hθsmall p hpmonic hproot hpsep hother hp0 hrecip
  · exact nonreciprocal_pisot_not_lt hθ1 hθsmall p hpmonic hproot hpsep hother hp0 hrecip

end
end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos1096/Erdos1096SignedSpectrum.lean` -/

section
open Filter Set Polynomial
open scoped BigOperators Pointwise Topology ComplexConjugate

noncomputable section



def SignedSpectrum (q : ℝ) : Set ℝ :=
  {y | ∃ p : ℤ[X], (∀ i, |p.coeff i| ≤ 1) ∧
    y = p.eval₂ (algebraMap ℤ ℝ) q}

def HasAccumulation (A : Set ℝ) : Prop :=
  ∃ a : ℝ, AccPt a (Filter.principal A)

lemma finite_bounded_of_no_accumulation {A : Set ℝ} (hA : ¬ HasAccumulation A)
    (M : ℝ) : (A ∩ Set.Icc (-M) M).Finite := by
  by_contra hinf
  have hinf' : (A ∩ Set.Icc (-M) M).Infinite := hinf
  obtain ⟨a, ha, hacc⟩ :=
    hinf'.exists_accPt_of_subset_isCompact
      (isCompact_Icc : IsCompact (Set.Icc (-M) M)) inter_subset_right
  apply hA
  refine ⟨a, ?_⟩
  exact hacc.mono (Filter.principal_mono.mpr inter_subset_left)

lemma finite_of_bounded_subset_no_accumulation {A B : Set ℝ}
    (hA : ¬ HasAccumulation A) (hBA : B ⊆ A) (M : ℝ)
    (hbound : B ⊆ Set.Icc (-M) M) : B.Finite := by
  exact (finite_bounded_of_no_accumulation hA M).subset
    (fun x hx ↦ ⟨hBA hx, hbound hx⟩)

def reversedPolynomial (s : ℕ → ℤ) (n : ℕ) : ℤ[X] :=
  Polynomial.ofFn (n + 1) (fun j ↦ s (n - j.1))

lemma reversedPolynomial_coeff (s : ℕ → ℤ) (n i : ℕ) :
    (reversedPolynomial s n).coeff i = if i ≤ n then s (n - i) else 0 := by
  by_cases hi : i ≤ n
  · rw [if_pos hi]
    exact Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega)
  · rw [if_neg hi]
    exact Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)

lemma reversedPolynomial_height_one {s : ℕ → ℤ}
    (hs : ∀ i, |s i| ≤ 1) (n i : ℕ) :
    |(reversedPolynomial s n).coeff i| ≤ 1 := by
  rw [reversedPolynomial_coeff]
  split_ifs
  · exact hs _
  · norm_num

lemma eval₂_reversedPolynomial (q : ℝ) (s : ℕ → ℤ) (n : ℕ) :
    (reversedPolynomial s n).eval₂ (algebraMap ℤ ℝ) q =
      ∑ i ∈ Finset.range (n + 1), (s i : ℝ) * q ^ (n - i) := by
  rw [reversedPolynomial, Polynomial.eval₂_eq_sum_range' (algebraMap ℤ ℝ)
    (Polynomial.ofFn_natDegree_lt (by omega) (fun j : Fin (n + 1) ↦ s (n - j.1))) q]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := by simpa using hi
  rw [Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega)]
  simp only [Nat.add_sub_cancel, Nat.succ_sub_succ_eq_sub]
  simp [Nat.sub_sub_self hi']

lemma reversedPolynomial_eval_mem_signedSpectrum {q : ℝ} {s : ℕ → ℤ}
    (hs : ∀ i, |s i| ≤ 1) (n : ℕ) :
    (reversedPolynomial s n).eval₂ (algebraMap ℤ ℝ) q ∈ SignedSpectrum q := by
  exact ⟨reversedPolynomial s n, reversedPolynomial_height_one hs n, rfl⟩

def expansionSignedDigits (d : ℕ → ℕ) : ℕ → ℤ
  | 0 => -1
  | n + 1 => d n

def SignedExpansion (q : ℝ) (s : ℕ → ℤ) : Prop :=
  HasSum (fun i ↦ (s i : ℝ) * q⁻¹ ^ i) 0

lemma expansionSignedDigits_height_one {d : ℕ → ℕ}
    (hd : ∀ n, d n = 0 ∨ d n = 1) (i : ℕ) :
    |expansionSignedDigits d i| ≤ 1 := by
  cases i with
  | zero => norm_num [expansionSignedDigits]
  | succ i => rcases hd i with h | h <;> simp [expansionSignedDigits, h]

lemma summable_signed_series {q : ℝ} (hq : 1 < q) {s : ℕ → ℤ}
    (hs : ∀ i, |s i| ≤ 1) :
    Summable (fun i ↦ (s i : ℝ) * q⁻¹ ^ i) := by
  have hqinv0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (by linarith)
  have hqinv1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  apply Summable.of_norm_bounded
    (summable_geometric_of_lt_one hqinv0 hqinv1)
  intro i
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hqinv0]
  have hscast : |(s i : ℝ)| ≤ 1 := by exact_mod_cast hs i
  exact mul_le_of_le_one_left (pow_nonneg hqinv0 _) hscast

lemma hasSum_expansionSignedDigits_value {q x : ℝ} (hq : 1 < q)
    {d : ℕ → ℕ} (hd : ∀ n, d n = 0 ∨ d n = 1)
    (hdsum : Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
      (d i : ℝ) * q⁻¹ ^ (i + 1)) atTop (𝓝 x)) :
    HasSum (fun i ↦ (expansionSignedDigits d i : ℝ) * q⁻¹ ^ i) (-1 + x) := by
  let s := expansionSignedDigits d
  have hs : ∀ i, |s i| ≤ 1 := expansionSignedDigits_height_one hd
  have hsummable := summable_signed_series (q := q) hq hs
  rw [hsummable.hasSum_iff_tendsto_nat]
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hconst : Tendsto (fun _ : ℕ ↦ (-1 : ℝ)) atTop (𝓝 (-1)) :=
    tendsto_const_nhds
  convert hconst.add hdsum using 1
  funext n
  have heq : ∀ m : ℕ,
      (∑ i ∈ Finset.range (m + 1), (s i : ℝ) * q⁻¹ ^ i) =
        -1 + ∑ i ∈ Finset.range m, (d i : ℝ) * q⁻¹ ^ (i + 1) := by
    intro m
    induction m with
    | zero => simp [s, expansionSignedDigits]
    | succ m ih =>
        calc
          (∑ i ∈ Finset.range (m + 1 + 1), (s i : ℝ) * q⁻¹ ^ i) =
              (∑ i ∈ Finset.range (m + 1), (s i : ℝ) * q⁻¹ ^ i) +
                (s (m + 1) : ℝ) * q⁻¹ ^ (m + 1) := by
            rw [Finset.sum_range_succ]
          _ = (-1 + ∑ i ∈ Finset.range m, (d i : ℝ) * q⁻¹ ^ (i + 1)) +
                (s (m + 1) : ℝ) * q⁻¹ ^ (m + 1) := by rw [ih]
          _ = -1 + ∑ i ∈ Finset.range (m + 1),
                (d i : ℝ) * q⁻¹ ^ (i + 1) := by
            rw [Finset.sum_range_succ]
            simp only [s, expansionSignedDigits, Int.cast_natCast]
            ring
  · exact heq n

lemma hasSum_expansionSignedDigits {q : ℝ} (hq : 1 < q)
    {d : ℕ → ℕ} (hd : ∀ n, d n = 0 ∨ d n = 1)
    (hdsum : Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
      (d i : ℝ) * q⁻¹ ^ (i + 1)) atTop (𝓝 1)) :
    SignedExpansion q (expansionSignedDigits d) := by
  simpa [SignedExpansion] using hasSum_expansionSignedDigits_value hq hd hdsum

lemma exists_signed_expansion_of_one {q : ℝ} (hq1 : 1 < q) (hq2 : q ≤ 2) :
    ∃ s : ℕ → ℤ, (∀ i, |s i| ≤ 1) ∧ s 0 = -1 ∧ SignedExpansion q s := by
  have hone : (1 : ℝ) ≤ 1 / (q - 1) := by
    rw [le_div_iff₀ (sub_pos.mpr hq1)]
    linarith
  obtain ⟨d, hd, hdsum⟩ := exists_binary_expansion hq1 hq2 zero_le_one hone
  refine ⟨expansionSignedDigits d, expansionSignedDigits_height_one hd, rfl, ?_⟩
  exact hasSum_expansionSignedDigits hq1 hd hdsum

lemma tsum_inv_pow_succ {q : ℝ} (hq : 1 < q) :
    (∑' n : ℕ, q⁻¹ ^ (n + 1)) = 1 / (q - 1) := by
  have hq0 : q ≠ 0 := by linarith
  have hqi0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (by linarith)
  have hqi1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  rw [show (fun n : ℕ ↦ q⁻¹ ^ (n + 1)) = fun n ↦ q⁻¹ * q⁻¹ ^ n by
    funext n; rw [pow_succ, mul_comm]]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
  · field_simp
  · simpa [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < q)]

def lazySignedDigits (P : Set ℕ) [DecidablePred (· ∈ P)] (d : ℕ → ℕ) : ℕ → ℤ
  | 0 => -1
  | n + 1 => if n ∈ P then d n else (d n : ℤ) - 1

lemma lazySignedDigits_height_one {P : Set ℕ} [DecidablePred (· ∈ P)] {d : ℕ → ℕ}
    (hd : ∀ n, d n = 0 ∨ d n = 1) (i : ℕ) :
    |lazySignedDigits P d i| ≤ 1 := by
  cases i with
  | zero => norm_num [lazySignedDigits]
  | succ i =>
      rcases hd i with hi | hi <;> by_cases hP : i ∈ P <;>
        simp [lazySignedDigits, hi, hP]

lemma exists_lazy_signed_expansion {q : ℝ} (hq1 : 1 < q) (hq2 : q ≤ 2)
    (P : Set ℕ) [DecidablePred (· ∈ P)]
    (hPmass : 1 ≤ ∑' n : ℕ, if n ∈ P then q⁻¹ ^ (n + 1) else 0) :
    ∃ s : ℕ → ℤ, (∀ i, |s i| ≤ 1) ∧ s 0 = -1 ∧ SignedExpansion q s ∧
      (∀ n ∈ P, 0 ≤ s (n + 1)) ∧ (∀ n ∉ P, s (n + 1) ≤ 0) := by
  let a : ℕ → ℝ := fun n ↦ if n ∈ P then q⁻¹ ^ (n + 1) else 0
  let b : ℕ → ℝ := fun n ↦ if n ∈ P then 0 else q⁻¹ ^ (n + 1)
  have hqi0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (by linarith)
  have hqi1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
  have hgeom : Summable (fun n : ℕ ↦ q⁻¹ ^ (n + 1)) := by
    simpa [pow_succ, mul_comm] using
      (summable_geometric_of_lt_one hqi0 hqi1).mul_left q⁻¹
  have ha0 : ∀ n, 0 ≤ a n := by
    intro n
    simp only [a]
    split_ifs <;> positivity
  have hb0 : ∀ n, 0 ≤ b n := by
    intro n
    simp only [b]
    split_ifs <;> positivity
  have ha_le : ∀ n, a n ≤ q⁻¹ ^ (n + 1) := by
    intro n
    by_cases hP : n ∈ P
    · simp [a, hP]
    · simp [a, hP]
      exact pow_nonneg (by linarith) _
  have hb_le : ∀ n, b n ≤ q⁻¹ ^ (n + 1) := by
    intro n
    by_cases hP : n ∈ P
    · simp [b, hP]
      exact pow_nonneg (by linarith) _
    · simp [b, hP]
  have hasum : Summable a := Summable.of_nonneg_of_le ha0 ha_le hgeom
  have hbsum : Summable b := Summable.of_nonneg_of_le hb0 hb_le hgeom
  have hab (n : ℕ) : a n + b n = q⁻¹ ^ (n + 1) := by
    simp only [a, b]
    by_cases hP : n ∈ P <;> simp [hP]
  have htotal : (∑' n, a n) + ∑' n, b n = 1 / (q - 1) := by
    rw [← (hasum.tsum_add hbsum)]
    rw [show (fun n ↦ a n + b n) = fun n ↦ q⁻¹ ^ (n + 1) by
      funext n; exact hab n]
    exact tsum_inv_pow_succ hq1
  let x : ℝ := 1 + ∑' n, b n
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    exact add_nonneg zero_le_one (tsum_nonneg hb0)
  have hx1 : x ≤ 1 / (q - 1) := by
    have hmass : 1 ≤ ∑' n, a n := by simpa [a] using hPmass
    dsimp only [x]
    linarith
  obtain ⟨d, hd, hdsum⟩ := exists_binary_expansion hq1 hq2 hx0 hx1
  let base : ℕ → ℤ := expansionSignedDigits d
  let c : ℕ → ℤ
    | 0 => 0
    | n + 1 => if n ∈ P then 0 else -1
  let s : ℕ → ℤ := lazySignedDigits P d
  have hbase : HasSum (fun i ↦ (base i : ℝ) * q⁻¹ ^ i) (∑' n, b n) := by
    have := hasSum_expansionSignedDigits_value hq1 hd hdsum
    simpa [base, x] using this
  have hcsum : Summable (fun i ↦ (c i : ℝ) * q⁻¹ ^ i) := by
    apply Summable.of_norm_bounded
      (summable_geometric_of_lt_one hqi0 hqi1)
    intro i
    cases i with
    | zero => simp [c]
    | succ i =>
        by_cases hP : i ∈ P
        · simp [c, hP]
          positivity
        · simp [c, hP, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < q)]
  have hctsum : (∑' i, (c i : ℝ) * q⁻¹ ^ i) = -(∑' n, b n) := by
    have hsplit := hcsum.sum_add_tsum_nat_add 1
    have htail : (∑' n, (c (n + 1) : ℝ) * q⁻¹ ^ (n + 1)) = -(∑' n, b n) := by
      rw [← tsum_neg]
      apply tsum_congr
      intro n
      by_cases hP : n ∈ P <;> simp [c, b, hP]
    calc
      (∑' i, (c i : ℝ) * q⁻¹ ^ i) =
          (∑ i ∈ Finset.range 1, (c i : ℝ) * q⁻¹ ^ i) +
            ∑' i, (c (i + 1) : ℝ) * q⁻¹ ^ (i + 1) := hsplit.symm
      _ = -(∑' n, b n) := by rw [htail]; simp [c]
  have hc : HasSum (fun i ↦ (c i : ℝ) * q⁻¹ ^ i) (-(∑' n, b n)) := by
    rw [← hctsum]
    exact hcsum.hasSum
  have hsPoint (i : ℕ) : (base i : ℝ) * q⁻¹ ^ i + (c i : ℝ) * q⁻¹ ^ i =
      (s i : ℝ) * q⁻¹ ^ i := by
    rw [← add_mul]
    congr 1
    cases i with
    | zero => norm_num [base, c, s, expansionSignedDigits, lazySignedDigits]
    | succ i =>
        by_cases hP : i ∈ P <;>
          simp [base, c, s, expansionSignedDigits, lazySignedDigits, hP] <;> ring
  have hsExp : SignedExpansion q s := by
    rw [SignedExpansion]
    convert hbase.add hc using 1
    · funext i
      exact (hsPoint i).symm
    · ring
  refine ⟨s, ?_, by simp [s, lazySignedDigits], hsExp, ?_, ?_⟩
  · intro i
    exact lazySignedDigits_height_one hd i
  · intro n hn
    rcases hd n with hd0 | hd1
    · simp [s, lazySignedDigits, hn, hd0]
    · simp [s, lazySignedDigits, hn, hd1]
  · intro n hn
    rcases hd n with hd0 | hd1
    · simp [s, lazySignedDigits, hn, hd0]
    · simp [s, lazySignedDigits, hn, hd1]

lemma exists_positive_term_with_nonpositive_tails {a : ℕ → ℝ}
    (ha : HasSum a 0) (ha0 : 0 < a 0) :
    ∃ n : ℕ, 0 < a n ∧ ∀ k : ℕ, ∑ i ∈ Finset.range k, a (n + 1 + i) ≤ 0 := by
  classical
  let S : ℕ → ℝ := fun n ↦ ∑ i ∈ Finset.range (n + 1), a i
  have hStend : Tendsto S atTop (𝓝 0) := by
    have h := ha.tendsto_sum_nat
    have hc := h.comp (tendsto_add_atTop_nat 1)
    convert hc using 1
    funext n
    simp [S, Function.comp_apply, Nat.add_comm]
  have hS0 : 0 < S 0 := by simpa [S] using ha0
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hStend) (S 0 / 2) (by linarith)
  have hlate : ∀ k, N ≤ k → S k < S 0 := by
    intro k hk
    have hkdist := hN k hk
    rw [Real.dist_eq, sub_zero, abs_lt] at hkdist
    linarith
  have hrange : (Finset.range (N + 1)).Nonempty := by simp
  obtain ⟨r, hrmem, hrmax⟩ := Finset.exists_max_image (Finset.range (N + 1)) S hrange
  have hrGlobal : ∀ k, S k ≤ S r := by
    intro k
    by_cases hk : k < N + 1
    · exact hrmax k (by simpa using hk)
    · have hkN : N ≤ k := by omega
      have hlt := hlate k hkN
      have h0mem : 0 ∈ Finset.range (N + 1) := by simp
      exact hlt.le.trans (hrmax 0 h0mem)
  let G : ℕ → Prop := fun n ↦ ∀ k, S k ≤ S n
  have hG : ∃ n, G n := ⟨r, hrGlobal⟩
  let n := Nat.find hG
  have hnG : G n := Nat.find_spec hG
  have hapos : 0 < a n := by
    by_cases hn0 : n = 0
    · simpa [hn0] using ha0
    · let m := n - 1
      have hmn : m + 1 = n := by dsimp [m]; omega
      have hstep : S n = S m + a n := by
        rw [← hmn]
        simp [S, Finset.sum_range_succ]
      by_contra hnot
      have hale : a n ≤ 0 := le_of_not_gt hnot
      have hSnm : S n ≤ S m := by linarith
      have hmnlt : m < n := by dsimp [m]; omega
      have hmG : G m := by
        intro k
        exact (hnG k).trans hSnm
      have hfind : m < Nat.find hG := by simpa [n] using hmnlt
      exact Nat.find_min hG hfind hmG
  refine ⟨n, hapos, fun k ↦ ?_⟩
  have htail : S (n + k) = S n + ∑ i ∈ Finset.range k, a (n + 1 + i) := by
    dsimp only [S]
    rw [show n + k + 1 = (n + 1) + k by omega, Finset.sum_range_add]
  have := hnG (n + k)
  linarith

lemma exists_complex_separator_of_norm_gt_one {p : ℂ} (hp : 1 < ‖p‖)
    (hpNonpos : p.re < 1 ∨ p.im ≠ 0) :
    ∃ w : ℂ, 0 < w.re ∧
      ∀ k : ℕ, ∑ i ∈ Finset.range k, (w * p⁻¹ ^ (i + 1)).re ≤ 0 := by
  have hp0 : p ≠ 0 := by
    intro h
    norm_num [h] at hp
  by_cases hpre : p.re < 1
  · refine ⟨1 - p, by simp; linarith, fun k ↦ ?_⟩
    have htel : ∑ i ∈ Finset.range k, (1 - p) * p⁻¹ ^ (i + 1) = p⁻¹ ^ k - 1 := by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Finset.sum_range_succ, ih]
          have hcancel : p * p⁻¹ ^ (k + 1) = p⁻¹ ^ k := by
            rw [pow_succ]
            calc
              p * (p⁻¹ ^ k * p⁻¹) = p⁻¹ ^ k * (p * p⁻¹) := by ring
              _ = p⁻¹ ^ k := by simp [hp0]
          rw [sub_mul, one_mul, hcancel]
          ring
    have hreSum :
        (∑ i ∈ Finset.range k, ((1 - p) * p⁻¹ ^ (i + 1)).re) =
          (∑ i ∈ Finset.range k, (1 - p) * p⁻¹ ^ (i + 1)).re := by
      simpa only [Complex.reCLM_apply] using
        (map_sum (Complex.reCLM : ℂ →L[ℝ] ℝ)
          (fun i ↦ (1 - p) * p⁻¹ ^ (i + 1)) (Finset.range k)).symm
    rw [hreSum, htel]
    calc
      (p⁻¹ ^ k - 1).re = (p⁻¹ ^ k).re - 1 := by simp
      _ ≤ ‖p⁻¹ ^ k‖ - 1 := sub_le_sub_right (Complex.re_le_norm _) 1
      _ ≤ 0 := by
        rw [norm_pow, norm_inv]
        have hinv : ‖p‖⁻¹ ≤ 1 := (inv_le_one₀ (norm_pos_iff.mpr hp0)).2 hp.le
        linarith [pow_le_one₀ (n := k) (inv_nonneg.mpr (norm_nonneg p)) hinv]
  · have hpim : p.im ≠ 0 := hpNonpos.resolve_left hpre
    let z0 : ℂ := (1 - p⁻¹) * Complex.I
    have hz0re : z0.re ≠ 0 := by
      have hnormsq : Complex.normSq p ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hp0)
      have hinvim : p⁻¹.im ≠ 0 := by
        rw [Complex.inv_im]
        exact div_ne_zero (neg_ne_zero.mpr hpim) hnormsq
      simpa [z0, Complex.mul_re] using hinvim
    let z : ℂ := if 0 < z0.re then z0 else -z0
    have hzre : 0 < z.re := by
      dsimp only [z]
      split_ifs with hpos
      · exact hpos
      · simp only [Complex.neg_re]
        exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hz0re)
    have hpinv : ‖p⁻¹‖ < 1 := by
      rw [norm_inv, inv_lt_one₀ (norm_pos_iff.mpr hp0)]
      exact hp
    have hgeom : HasSum (fun i : ℕ ↦ p⁻¹ ^ i) (1 - p⁻¹)⁻¹ :=
      hasSum_geometric_of_norm_lt_one hpinv
    have hz0sumC : HasSum (fun i : ℕ ↦ z0 * p⁻¹ ^ i) Complex.I := by
      have hmul := hgeom.mul_left z0
      have hone : 1 - p⁻¹ ≠ 0 := by
        intro h
        have : p = 1 := by
          apply inv_injective
          simpa using sub_eq_zero.mp h
        subst p
        norm_num at hp
      have hval : z0 * (1 - p⁻¹)⁻¹ = Complex.I := by
        dsimp only [z0]
        field_simp
        exact div_self (sub_ne_zero.mpr (by
          intro h
          subst p
          norm_num at hp))
      rw [← hval]
      exact hmul
    have hz0sumR : HasSum (fun i : ℕ ↦ (z0 * p⁻¹ ^ i).re) 0 := by
      simpa using Complex.hasSum_re hz0sumC
    have hzsumR : HasSum (fun i : ℕ ↦ (z * p⁻¹ ^ i).re) 0 := by
      dsimp only [z]
      split_ifs with hpos
      · exact hz0sumR
      · simpa using hz0sumR.neg
    obtain ⟨n, han, htail⟩ :=
      exists_positive_term_with_nonpositive_tails hzsumR (by simpa using hzre)
    let w : ℂ := z * p⁻¹ ^ n
    refine ⟨w, by simpa [w] using han, fun k ↦ ?_⟩
    have heq : (fun i : ℕ ↦ (w * p⁻¹ ^ (i + 1)).re) =
        fun i ↦ (z * p⁻¹ ^ (n + 1 + i)).re := by
      funext i
      dsimp only [w]
      congr 1
      rw [show n + 1 + i = n + (i + 1) by omega, pow_add]
      ring
    rw [heq]
    exact htail k

lemma signed_expansion_coefficient_eq_one_of_remove_mass_lt {q : ℝ} (hq : 1 < q)
    {P : Set ℕ} [DecidablePred (· ∈ P)] {s : ℕ → ℤ}
    (hs : ∀ i, |s i| ≤ 1) (hs0 : s 0 = -1) (hexp : SignedExpansion q s)
    (hsP : ∀ n ∈ P, 0 ≤ s (n + 1)) (hsPc : ∀ n ∉ P, s (n + 1) ≤ 0)
    {j : ℕ} (hjP : j ∈ P)
    (hmass : (∑' n : ℕ, if n ∈ P ∧ n ≠ j then q⁻¹ ^ (n + 1) else 0) < 1) :
    s (j + 1) = 1 := by
  by_contra hsj
  have hsj0 : s (j + 1) = 0 := by
    have hnonneg := hsP j hjP
    have hle : s (j + 1) ≤ 1 := le_trans (le_abs_self _) (hs (j + 1))
    omega
  let f : ℕ → ℝ := fun n ↦ (s (n + 1) : ℝ) * q⁻¹ ^ (n + 1)
  let g : ℕ → ℝ := fun n ↦ if n ∈ P ∧ n ≠ j then q⁻¹ ^ (n + 1) else 0
  have hqi0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (by linarith)
  have hqi1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hgeom : Summable (fun n : ℕ ↦ q⁻¹ ^ (n + 1)) := by
    simpa [pow_succ, mul_comm] using
      (summable_geometric_of_lt_one hqi0 hqi1).mul_left q⁻¹
  have hgle : ∀ n, g n ≤ q⁻¹ ^ (n + 1) := by
    intro n
    by_cases hn : n ∈ P ∧ n ≠ j
    · simp [g, hn]
    · simp [g, hn]
      exact pow_nonneg (by linarith) _
  have hg0 : ∀ n, 0 ≤ g n := by
    intro n
    simp only [g]
    split_ifs <;> positivity
  have hgsum : Summable g := Summable.of_nonneg_of_le hg0 hgle hgeom
  have hfsum : Summable f := by
    have hfull := summable_signed_series (q := q) hq hs
    have hshift := (summable_nat_add_iff 1).mpr hfull
    simpa [f, Nat.add_assoc] using hshift
  have hfg : ∀ n, f n ≤ g n := by
    intro n
    by_cases hnP : n ∈ P
    · by_cases hnj : n = j
      · subst n
        simp [f, g, hjP, hsj0]
      · rw [show g n = q⁻¹ ^ (n + 1) by simp [g, hnP, hnj]]
        dsimp only [f]
        have hcoeff : (s (n + 1) : ℝ) ≤ 1 := by
          exact_mod_cast (le_trans (le_abs_self _) (hs (n + 1)))
        exact mul_le_of_le_one_left (pow_nonneg hqi0 _) hcoeff
    · simp only [g, hnP, false_and, ↓reduceIte]
      exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hsPc n hnP)
        (pow_nonneg hqi0 _)
  have hftsum : ∑' n, f n = 1 := by
    have hfull := (summable_signed_series (q := q) hq hs).sum_add_tsum_nat_add 1
    have htotal := hexp.tsum_eq
    rw [htotal] at hfull
    have hEq : -1 + ∑' n, f n = 0 := by simpa [f, hs0] using hfull
    linarith
  have hle : (∑' n, f n) ≤ ∑' n, g n :=
    Summable.tsum_le_tsum hfg hfsum hgsum
  have hgmass : (∑' n, g n) < 1 := by simpa [g] using hmass
  linarith

lemma tsum_indicator_le_add_single {P Q : Set ℕ} {weight : ℕ → ℝ} {j : ℕ}
    [DecidablePred (· ∈ P)] [DecidablePred (· ∈ Q)]
    (hP : Summable (fun n : ℕ ↦ if n ∈ P then weight n else 0))
    (hQ : Summable (fun n : ℕ ↦ if n ∈ Q then weight n else 0))
    (hweight0 : ∀ n, 0 ≤ weight n)
    (hsub : ∀ n, n ∈ P → n ∈ Q ∨ n = j) :
    (∑' n : ℕ, if n ∈ P then weight n else 0) ≤
      (∑' n : ℕ, if n ∈ Q then weight n else 0) + weight j := by
  classical
  let f : ℕ → ℝ := fun n ↦ if n ∈ P then weight n else 0
  let g : ℕ → ℝ := fun n ↦
    (if n ∈ Q then weight n else 0) + if n = j then weight j else 0
  have hsingle : Summable (fun n : ℕ ↦ if n = j then weight j else 0) := by
    apply summable_of_ne_finset_zero (s := {j})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [hn]
  have hgsum : Summable g := hQ.add hsingle
  have hfg : ∀ n, f n ≤ g n := by
    intro n
    by_cases hnP : n ∈ P
    · rcases hsub n hnP with hnQ | hnj
      · rw [show f n = weight n by simp [f, hnP]]
        rw [show g n = weight n + (if n = j then weight j else 0) by simp [g, hnQ]]
        exact le_add_of_nonneg_right (by
          by_cases h : n = j
          · simp [h, hweight0]
          · simp [h])
      · subst n
        rw [show f j = weight j by simp [f, hnP]]
        rw [show g j = (if j ∈ Q then weight j else 0) + weight j by simp [g]]
        exact le_add_of_nonneg_left (by
          by_cases h : j ∈ Q
          · rw [if_pos h]
            exact hweight0 j
          · rw [if_neg h])
    · rw [show f n = 0 by simp [f, hnP]]
      apply add_nonneg
      · by_cases h : n ∈ Q
        · rw [if_pos h]
          exact hweight0 n
        · rw [if_neg h]
      · by_cases h : n = j
        · rw [if_pos h]
          exact hweight0 j
        · rw [if_neg h]
  have hle := Summable.tsum_le_tsum hfg hP hgsum
  have hgval : (∑' n, g n) =
      (∑' n : ℕ, if n ∈ Q then weight n else 0) + weight j := by
    rw [Summable.tsum_add hQ hsingle, tsum_ite_eq]
  change (∑' n : ℕ, if n ∈ P then weight n else 0) ≤ _ at hle
  exact hle.trans_eq hgval

lemma exists_lazy_expansion_for_separator {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (a : ℕ → ℝ) :
    ∃ K : ℕ, ∃ s : ℕ → ℤ,
      (∀ i, |s i| ≤ 1) ∧ s 0 = -1 ∧ SignedExpansion q s ∧
      (∀ n, n < K ∨ a n ≤ 0 → 0 ≤ s (n + 1)) ∧
      (∀ n, ¬(n < K ∨ a n ≤ 0) → s (n + 1) ≤ 0) ∧
      (∀ j, j < K → a j < 0 → s (j + 1) = 1) := by
  classical
  let weight : ℕ → ℝ := fun n ↦ q⁻¹ ^ (n + 1)
  let P : ℕ → Set ℕ := fun K ↦ {n | n < K ∨ a n ≤ 0}
  let mass : ℕ → ℝ := fun K ↦ ∑' n : ℕ, if n ∈ P K then weight n else 0
  have hqi0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (by linarith)
  have hqi1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
  have hqi_le : q⁻¹ ≤ 1 := hqi1.le
  have hweight0 : ∀ n, 0 ≤ weight n := fun n ↦ by
    exact pow_nonneg hqi0 _
  have hweightSum : Summable weight := by
    simpa [weight, pow_succ, mul_comm] using
      (summable_geometric_of_lt_one hqi0 hqi1).mul_left q⁻¹
  have hmassSum (K : ℕ) : Summable (fun n : ℕ ↦ if n ∈ P K then weight n else 0) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hweightSum
    · intro n
      split_ifs <;> positivity
    · intro n
      by_cases hn : n ∈ P K
      · simp [hn]
      · simp [hn, hweight0]
  have htotal : 1 < ∑' n, weight n := by
    rw [show (∑' n, weight n) = 1 / (q - 1) by simpa [weight] using tsum_inv_pow_succ hq1]
    rw [one_lt_div (sub_pos.mpr hq1)]
    linarith
  have hpartialTend : Tendsto (fun K ↦ ∑ n ∈ Finset.range K, weight n)
      atTop (𝓝 (∑' n, weight n)) := hweightSum.hasSum.tendsto_sum_nat
  have hevent : ∀ᶠ K in atTop, 1 < ∑ n ∈ Finset.range K, weight n :=
    hpartialTend.eventually (Ioi_mem_nhds htotal)
  rcases (eventually_atTop.1 hevent) with ⟨L, hL⟩
  have hmassL : 1 ≤ mass L := by
    have hle : (∑ n ∈ Finset.range L, weight n) ≤ mass L := by
      have heq : (∑ n ∈ Finset.range L, weight n) =
          ∑ n ∈ Finset.range L, (if n ∈ P L then weight n else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [if_pos]
        exact Or.inl (Finset.mem_range.mp hn)
      rw [heq]
      dsimp only [mass]
      apply (hmassSum L).sum_le_tsum (Finset.range L)
      · intro n hn
        positivity
    exact (hL L le_rfl).le.trans hle
  have hexK : ∃ K, 1 ≤ mass K := ⟨L, hmassL⟩
  let K := Nat.find hexK
  have hKmass : 1 ≤ mass K := Nat.find_spec hexK
  let PK : Set ℕ := P K
  have hPKmass : 1 ≤ ∑' n : ℕ, if n ∈ PK then q⁻¹ ^ (n + 1) else 0 := by
    calc
      1 ≤ mass K := hKmass
      _ = ∑' n : ℕ, if n ∈ PK then q⁻¹ ^ (n + 1) else 0 := by
        apply tsum_congr
        intro n
        by_cases hn : n ∈ P K
        · simp [mass, PK, weight, hn]
        · simp [mass, PK, weight, hn]
  obtain ⟨s, hs, hs0, hsExp, hsP, hsPc⟩ :=
    exists_lazy_signed_expansion hq1 hq2.le PK hPKmass
  have hmassStep : K ≠ 0 → mass K ≤ mass (K - 1) + weight (K - 1) := by
    intro hK0
    dsimp only [mass]
    exact tsum_indicator_le_add_single (P := P K) (Q := P (K - 1))
      (weight := weight) (j := K - 1) (hmassSum K) (hmassSum (K - 1)) hweight0
      (by
        intro n hn
        simp only [P, Set.mem_ofPred_eq] at hn ⊢
        rcases hn with hnlt | hna
        · by_cases hlt : n < K - 1
          · exact Or.inl (Or.inl hlt)
          · exact Or.inr (by omega)
        · exact Or.inl (Or.inr hna))
  have hcoeffOne {j : ℕ} (hjK : j < K) (hja : a j < 0) : s (j + 1) = 1 := by
    have hK0 : K ≠ 0 := by omega
    have hprev : mass (K - 1) < 1 := by
      have hnot : ¬ 1 ≤ mass (K - 1) := by
        intro h
        have hlt : K - 1 < K := by omega
        have : K - 1 < Nat.find hexK := by simpa [K] using hlt
        exact Nat.find_min hexK this h
      exact lt_of_not_ge hnot
    let remove : ℕ → ℝ := fun n ↦
      if n ∈ PK ∧ n ≠ j then weight n else 0
    have hjPK : j ∈ PK := by simp [PK, P, hjK]
    have hremoveSum : Summable remove := by
      refine Summable.of_nonneg_of_le ?_ ?_ hweightSum
      · intro n; simp only [remove]; split_ifs <;> positivity
      · intro n
        by_cases hn : n ∈ PK ∧ n ≠ j
        · simp [remove, hn]
        · simp [remove, hn, hweight0]
    have hmassRemove : (∑' n, remove n) = mass K - weight j := by
      have hsplit := (hmassSum K).tsum_eq_add_tsum_ite j
      have hrest : (∑' n, if n = j then 0 else if n ∈ P K then weight n else 0) =
          ∑' n, remove n := by
        apply tsum_congr
        intro n
        by_cases hnj : n = j
        · subst n; simp [remove]
        · simp [remove, PK, hnj]
      have hmassSplit : mass K = weight j + ∑' n, remove n := by
        calc
          mass K = (if j ∈ P K then weight j else 0) +
              ∑' n, if n = j then 0 else if n ∈ P K then weight n else 0 := by
                simpa only [mass] using hsplit
          _ = weight j + ∑' n, remove n := by rw [if_pos (by simpa [PK] using hjPK), hrest]
      linarith
    have hweightOrder : weight (K - 1) ≤ weight j := by
      dsimp only [weight]
      exact pow_le_pow_of_le_one hqi0 hqi_le (by omega)
    have hremoveLt : (∑' n, remove n) < 1 := by
      rw [hmassRemove]
      have hstep := hmassStep hK0
      linarith
    apply signed_expansion_coefficient_eq_one_of_remove_mass_lt hq1 hs hs0 hsExp hsP hsPc
      hjPK
    simpa [remove, PK, weight, inv_pow] using hremoveLt
  refine ⟨K, s, hs, hs0, hsExp, ?_, ?_, ?_⟩
  · intro n hn
    exact hsP n (by simpa [PK, P] using hn)
  · intro n hn
    exact hsPc n (by simpa [PK, P] using hn)
  · intro j hjK hja
    exact hcoeffOne hjK hja

lemma exists_signed_expansion_separating_at_large_conjugate {q : ℝ} {p : ℂ}
    (hq1 : 1 < q) (hq2 : q < 2) (hp : 1 < ‖p‖)
    (hpNonpos : p.re < 1 ∨ p.im ≠ 0) :
    ∃ s : ℕ → ℤ, (∀ i, |s i| ≤ 1) ∧ SignedExpansion q s ∧
      ¬ HasSum (fun i ↦ (s i : ℂ) * p⁻¹ ^ i) 0 := by
  classical
  obtain ⟨w, hwpos, hwpartial⟩ := exists_complex_separator_of_norm_gt_one hp hpNonpos
  let a : ℕ → ℝ := fun n ↦ (w * p⁻¹ ^ (n + 1)).re
  obtain ⟨K, s, hs, hs0, hsExp, hsP, hsPc, hcoeffOne⟩ :=
    exists_lazy_expansion_for_separator hq1 hq2 a
  let t : ℕ → ℝ := fun n ↦ (s (n + 1) : ℝ) * a n
  let b : ℕ → ℝ := fun n ↦ if n < K then a n else 0
  have hp0 : p ≠ 0 := by
    intro h
    norm_num [h] at hp
  have hpinv : ‖p⁻¹‖ < 1 := by
    rw [norm_inv, inv_lt_one₀ (norm_pos_iff.mpr hp0)]
    exact hp
  have htsum : Summable t := by
    apply Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (norm_nonneg p⁻¹) hpinv).mul_left ‖w‖)
    intro n
    dsimp only [t, a]
    rw [Real.norm_eq_abs, abs_mul]
    have hsreal : |(s (n + 1) : ℝ)| ≤ 1 := by exact_mod_cast hs (n + 1)
    calc
      |(s (n + 1) : ℝ)| * |(w * p⁻¹ ^ (n + 1)).re| ≤
          1 * ‖w * p⁻¹ ^ (n + 1)‖ := by
        have hre : |(w * p⁻¹ ^ (n + 1)).re| ≤ ‖w * p⁻¹ ^ (n + 1)‖ := by
          simpa [Real.norm_eq_abs] using RCLike.norm_re_le_norm (w * p⁻¹ ^ (n + 1))
        exact mul_le_mul hsreal hre (abs_nonneg _) zero_le_one
      _ = ‖w‖ * ‖p⁻¹‖ ^ (n + 1) := by simp
      _ ≤ ‖w‖ * ‖p⁻¹‖ ^ n := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
        exact pow_le_pow_of_le_one (norm_nonneg p⁻¹) hpinv.le (by omega)
  have hbsum : Summable b := by
    apply summable_of_ne_finset_zero (s := Finset.range K)
    intro n hn
    have hnK : ¬n < K := by simpa using hn
    simp [b, hnK]
  have htb : ∀ n, t n ≤ b n := by
    intro n
    by_cases hnK : n < K
    · rw [show b n = a n by simp [b, hnK]]
      by_cases hapos : 0 ≤ a n
      · have hsle : (s (n + 1) : ℝ) ≤ 1 := by
          exact_mod_cast (le_trans (le_abs_self _) (hs (n + 1)))
        dsimp only [t]
        nlinarith
      · have haneg : a n < 0 := lt_of_not_ge hapos
        dsimp only [t]
        rw [hcoeffOne n hnK haneg]
        norm_num
    · rw [show b n = 0 by simp [b, hnK]]
      by_cases han : a n ≤ 0
      · exact mul_nonpos_of_nonneg_of_nonpos
          (by exact_mod_cast hsP n (Or.inr han)) han
      · exact mul_nonpos_of_nonpos_of_nonneg
          (by exact_mod_cast hsPc n (not_or_intro hnK han)) (le_of_not_ge han)
  have htbound : (∑' n, t n) ≤ ∑ n ∈ Finset.range K, a n := by
    have hle := Summable.tsum_le_tsum htb htsum hbsum
    have hbval : (∑' n, b n) = ∑ n ∈ Finset.range K, a n := by
      rw [tsum_eq_sum (s := Finset.range K)]
      · apply Finset.sum_congr rfl
        intro n hn
        simp [b, Finset.mem_range.mp hn]
      · intro n hn
        have hnK : ¬n < K := by simpa using hn
        simp [b, hnK]
    simpa [hbval] using hle
  have hprefix : ∑ n ∈ Finset.range K, a n ≤ 0 := by
    simpa [a] using hwpartial K
  have hcomplexSum : Summable (fun i ↦ (s i : ℂ) * p⁻¹ ^ i) := by
    apply Summable.of_norm_bounded
      (summable_geometric_of_lt_one (norm_nonneg p⁻¹) hpinv)
    intro i
    rw [norm_mul, norm_pow]
    have hsc : ‖(s i : ℂ)‖ ≤ 1 := by
      have hscR : |(s i : ℝ)| ≤ 1 := by exact_mod_cast hs i
      simpa using hscR
    simpa using mul_le_mul_of_nonneg_right hsc (pow_nonneg (norm_nonneg p⁻¹) i)
  let Z : ℂ := ∑' i, (s i : ℂ) * p⁻¹ ^ i
  have hreal : (w * Z).re = -w.re + ∑' n, t n := by
    have hmul : (∑' i, w * ((s i : ℂ) * p⁻¹ ^ i)) = w * Z := by
      simpa [Z] using (tsum_mul_left :
        (∑' i, w * ((s i : ℂ) * p⁻¹ ^ i)) = w * ∑' i, (s i : ℂ) * p⁻¹ ^ i)
    have husum : Summable (fun i ↦ w * ((s i : ℂ) * p⁻¹ ^ i)) :=
      hcomplexSum.mul_left w
    have hre : (w * Z).re = ∑' i, (w * ((s i : ℂ) * p⁻¹ ^ i)).re := by
      rw [← hmul]
      exact (Complex.hasSum_re husum.hasSum).tsum_eq.symm
    have hsplit := ((Complex.hasSum_re husum.hasSum).summable).sum_add_tsum_nat_add 1
    have htailEq : (fun n ↦ (w * ((s (n + 1) : ℂ) * p⁻¹ ^ (n + 1))).re) = t := by
      funext n
      dsimp only [t, a]
      rw [show w * ((s (n + 1) : ℂ) * p⁻¹ ^ (n + 1)) =
          (s (n + 1) : ℝ) • (w * p⁻¹ ^ (n + 1)) by
        norm_cast; ring]
      simp
    rw [htailEq] at hsplit
    have hzero : (w * ((s 0 : ℂ) * p⁻¹ ^ 0)).re = -w.re := by simp [hs0]
    calc
      (w * Z).re = ∑' i, (w * ((s i : ℂ) * p⁻¹ ^ i)).re := hre
      _ = (w * ((s 0 : ℂ) * p⁻¹ ^ 0)).re + ∑' n, t n := by
        simpa only [Finset.sum_range_one] using hsplit.symm
      _ = -w.re + ∑' n, t n := by rw [hzero]
  have hneg : (w * Z).re < 0 := by
    rw [hreal]
    linarith
  refine ⟨s, hs, hsExp, ?_⟩
  intro hzero
  have : Z = 0 := hzero.tsum_eq
  rw [this, mul_zero, Complex.zero_re] at hneg
  exact lt_irrefl 0 hneg

lemma eval₂_reversedPolynomial_succ (q : ℝ) (s : ℕ → ℤ) (n : ℕ) :
    (reversedPolynomial s (n + 1)).eval₂ (algebraMap ℤ ℝ) q =
      q * (reversedPolynomial s n).eval₂ (algebraMap ℤ ℝ) q + s (n + 1) := by
  rw [eval₂_reversedPolynomial, eval₂_reversedPolynomial, Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, mul_one]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := by simpa using hi
  rw [show n + 1 - i = (n - i) + 1 by omega, pow_succ]
  ring

def expansionRemainder (q : ℝ) (d : ℕ → ℕ) (n : ℕ) : ℝ :=
  1 - ∑ i ∈ Finset.range n, (d i : ℝ) * (q⁻¹) ^ (i + 1)

lemma expansionRemainder_succ (q : ℝ) (d : ℕ → ℕ) (n : ℕ) :
    expansionRemainder q d (n + 1) =
      expansionRemainder q d n - (d n : ℝ) * (q⁻¹) ^ (n + 1) := by
  simp [expansionRemainder, Finset.sum_range_succ]
  ring

lemma expansion_tail_identity {q : ℝ} (hq0 : q ≠ 0) (d : ℕ → ℕ) (n : ℕ) :
    (reversedPolynomial (expansionSignedDigits d) n).eval₂ (algebraMap ℤ ℝ) q =
      -q ^ n * expansionRemainder q d n := by
  induction n with
  | zero => rw [eval₂_reversedPolynomial]; norm_num [expansionSignedDigits, expansionRemainder]
  | succ n ih =>
      rw [eval₂_reversedPolynomial_succ, ih, expansionRemainder_succ]
      simp only [expansionSignedDigits, Int.cast_natCast]
      have hcancel : q ^ (n + 1) * (q⁻¹) ^ (n + 1) = 1 := by
        rw [← mul_pow]
        simp [hq0]
      have hterm :
          q ^ (n + 1) * ((d n : ℝ) * (q⁻¹) ^ (n + 1)) = (d n : ℝ) := by
        calc
          _ = (d n : ℝ) * (q ^ (n + 1) * (q⁻¹) ^ (n + 1)) := by ring
          _ = (d n : ℝ) := by rw [hcancel, mul_one]
      have htermneg :
          -q ^ (n + 1) * ((d n : ℝ) * (q⁻¹) ^ (n + 1)) = -(d n : ℝ) := by
        rw [neg_mul, hterm]
      rw [mul_sub]
      rw [htermneg, pow_succ]
      ring

lemma reversed_tail_bound_of_signedExpansion {q : ℝ} (hq : 1 < q)
    {s : ℕ → ℤ} (hs : ∀ i, |s i| ≤ 1) (hexp : SignedExpansion q s)
    (n : ℕ) :
    |(reversedPolynomial s n).eval₂ (algebraMap ℤ ℝ) q| ≤ 1 / (q - 1) := by
  let f : ℕ → ℝ := fun i ↦ (s i : ℝ) * q⁻¹ ^ i
  have hq0 : q ≠ 0 := by linarith
  have hqi0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (by linarith)
  have hqi1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hfsum : Summable f := summable_signed_series (q := q) hq hs
  have htotal : ∑' i, f i = 0 := hexp.tsum_eq
  have hsplit := hfsum.sum_add_tsum_nat_add (n + 1)
  have hpartial : (∑ i ∈ Finset.range (n + 1), f i) =
      -(∑' i, f (i + (n + 1))) := by
    rw [htotal] at hsplit
    linarith
  have heval :
      (reversedPolynomial s n).eval₂ (algebraMap ℤ ℝ) q =
        q ^ n * ∑ i ∈ Finset.range (n + 1), f i := by
    rw [eval₂_reversedPolynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i ≤ n := by simpa using hi
    dsimp only [f]
    rw [pow_sub₀ q hq0 hin]
    simp only [inv_pow]
    ring
  have hgeom : Summable (fun i : ℕ ↦ q⁻¹ ^ (i + (n + 1))) := by
    simpa only [pow_add, mul_comm] using
      (summable_geometric_of_lt_one hqi0 hqi1).mul_left (q⁻¹ ^ (n + 1))
  have hterm_le (i : ℕ) : |f (i + (n + 1))| ≤ q⁻¹ ^ (i + (n + 1)) := by
    dsimp only [f]
    rw [abs_mul, abs_pow, abs_of_nonneg hqi0]
    have hscast : |(s (i + (n + 1)) : ℝ)| ≤ 1 := by
      exact_mod_cast hs (i + (n + 1))
    exact mul_le_of_le_one_left (pow_nonneg hqi0 _) hscast
  have htail_le : |∑' i, f (i + (n + 1))| ≤
      ∑' i : ℕ, q⁻¹ ^ (i + (n + 1)) := by
    simpa only [Real.norm_eq_abs] using
      (tsum_of_norm_bounded (f := fun i ↦ f (i + (n + 1))) hgeom.hasSum
        (fun i ↦ by simpa only [Real.norm_eq_abs] using hterm_le i))
  have hgeom_value : (∑' i : ℕ, q⁻¹ ^ (i + (n + 1))) =
      q⁻¹ ^ (n + 1) / (1 - q⁻¹) := by
    rw [show (fun i : ℕ ↦ q⁻¹ ^ (i + (n + 1))) =
        fun i ↦ q⁻¹ ^ (n + 1) * q⁻¹ ^ i by
      funext i; rw [pow_add, mul_comm]]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · rw [div_eq_mul_inv]
    · simpa [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < q)] using hqi1
  rw [heval, hpartial, abs_mul, abs_neg, abs_pow, abs_of_pos (by linarith)]
  calc
    q ^ n * |∑' i, f (i + (n + 1))| ≤
        q ^ n * (q⁻¹ ^ (n + 1) / (1 - q⁻¹)) := by
      rw [← hgeom_value]
      exact mul_le_mul_of_nonneg_left htail_le (pow_nonneg (by linarith) _)
    _ = 1 / (q - 1) := by
      have hprod : q ^ n * q⁻¹ ^ (n + 1) = q⁻¹ := by
        rw [pow_succ]
        calc
          q ^ n * (q⁻¹ ^ n * q⁻¹) = (q * q⁻¹) ^ n * q⁻¹ := by
            rw [mul_pow]
            ring
          _ = q⁻¹ := by simp [hq0]
      calc
        q ^ n * (q⁻¹ ^ (n + 1) / (1 - q⁻¹)) =
            (q ^ n * q⁻¹ ^ (n + 1)) / (1 - q⁻¹) := by ring
        _ = q⁻¹ / (1 - q⁻¹) := by rw [hprod]
        _ = 1 / (q - 1) := by field_simp

lemma summable_binary_digit_series {p : ℝ} (hp : 1 < p)
    {d : ℕ → ℕ} (hd : ∀ i, d i = 0 ∨ d i = 1) :
    Summable (fun i ↦ (d i : ℝ) * p⁻¹ ^ (i + 1)) := by
  have hp0 : 0 ≤ p⁻¹ := inv_nonneg.mpr (by linarith)
  have hp1 : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  apply Summable.of_nonneg_of_le
    (fun i ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
    (fun i ↦ ?_)
    ((summable_geometric_of_lt_one hp0 hp1).mul_left p⁻¹)
  rcases hd i with hi | hi
  · simp [hi]
    positivity
  · simp [hi, pow_succ, mul_comm]

lemma tsum_expansionSignedDigits {p : ℝ} (hp : 1 < p)
    {d : ℕ → ℕ} (hd : ∀ i, d i = 0 ∨ d i = 1) :
    ∑' i, (expansionSignedDigits d i : ℝ) * p⁻¹ ^ i =
      -1 + ∑' i, (d i : ℝ) * p⁻¹ ^ (i + 1) := by
  let s := expansionSignedDigits d
  have hs : ∀ i, |s i| ≤ 1 := expansionSignedDigits_height_one hd
  have hsum : Summable (fun i ↦ (s i : ℝ) * p⁻¹ ^ i) :=
    summable_signed_series (q := p) hp hs
  have hsplit := hsum.sum_add_tsum_nat_add 1
  convert hsplit.symm using 1 <;>
    simp only [Finset.sum_range_one, s, expansionSignedDigits, Int.cast_negSucc,
      Int.cast_zero, pow_zero, mul_one, zero_add, Nat.zero_add, Int.cast_natCast] <;>
    norm_num

lemma exists_one_digit_of_tendsto_one {q : ℝ} {d : ℕ → ℕ}
    (hd : ∀ i, d i = 0 ∨ d i = 1)
    (hdsum : Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
      (d i : ℝ) * q⁻¹ ^ (i + 1)) atTop (𝓝 1)) :
    ∃ i, d i = 1 := by
  by_contra hnone
  have hall : ∀ i, d i = 0 := by
    intro i
    rcases hd i with hi | hi
    · exact hi
    · exact (hnone ⟨i, hi⟩).elim
  have hzero : (fun n ↦ ∑ i ∈ Finset.range n,
      (d i : ℝ) * q⁻¹ ^ (i + 1)) = fun _ ↦ 0 := by
    funext n
    simp [hall]
  rw [hzero] at hdsum
  have : (0 : ℝ) = 1 := tendsto_nhds_unique tendsto_const_nhds hdsum
  norm_num at this

lemma binary_digit_tsum_ne_one_of_ne {q p : ℝ} (hq : 1 < q) (hp : 1 < p)
    (hpq : p ≠ q) {d : ℕ → ℕ} (hd : ∀ i, d i = 0 ∨ d i = 1)
    (hdsum : Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
      (d i : ℝ) * q⁻¹ ^ (i + 1)) atTop (𝓝 1)) :
    (∑' i, (d i : ℝ) * p⁻¹ ^ (i + 1)) ≠ 1 := by
  have hqsum : Summable (fun i ↦ (d i : ℝ) * q⁻¹ ^ (i + 1)) :=
    summable_binary_digit_series hq hd
  have hpsum : Summable (fun i ↦ (d i : ℝ) * p⁻¹ ^ (i + 1)) :=
    summable_binary_digit_series hp hd
  have hqtsum : (∑' i, (d i : ℝ) * q⁻¹ ^ (i + 1)) = 1 := by
    exact (hqsum.hasSum_iff_tendsto_nat.mpr hdsum).tsum_eq
  obtain ⟨j, hj⟩ := exists_one_digit_of_tendsto_one hd hdsum
  rcases lt_or_gt_of_ne hpq with hp_lt_q | hq_lt_p
  · have hlt : (∑' i, (d i : ℝ) * q⁻¹ ^ (i + 1)) <
        ∑' i, (d i : ℝ) * p⁻¹ ^ (i + 1) := by
      apply Summable.tsum_lt_tsum_of_nonneg
        (fun i ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (inv_nonneg.mpr (by linarith)) _))
      · intro i
        gcongr
      · rw [hj]
        norm_num
        simpa only [inv_pow, Nat.succ_eq_add_one] using
          (pow_lt_pow_left₀
            ((inv_lt_inv₀ (by linarith) (by linarith)).2 hp_lt_q)
            (inv_nonneg.mpr (by linarith)) (Nat.succ_ne_zero j))
      · exact hpsum
    rw [hqtsum] at hlt
    exact ne_of_gt hlt
  · have hlt : (∑' i, (d i : ℝ) * p⁻¹ ^ (i + 1)) <
        ∑' i, (d i : ℝ) * q⁻¹ ^ (i + 1) := by
      apply Summable.tsum_lt_tsum_of_nonneg
        (fun i ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (inv_nonneg.mpr (by linarith)) _))
      · intro i
        gcongr
      · rw [hj]
        norm_num
        simpa only [inv_pow, Nat.succ_eq_add_one] using
          (pow_lt_pow_left₀
            ((inv_lt_inv₀ (by linarith) (by linarith)).2 hq_lt_p)
            (inv_nonneg.mpr (by linarith)) (Nat.succ_ne_zero j))
      · exact hqsum
    rw [hqtsum] at hlt
    exact ne_of_lt hlt

lemma integral_of_no_signedSpectrum_accumulation {q : ℝ}
    (hq1 : 1 < q) (hq2 : q < 2) (hno : ¬ HasAccumulation (SignedSpectrum q)) :
    IsIntegral ℤ q := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq1)
  have hden : 0 < q - 1 := sub_pos.mpr hq1
  have hone : (1 : ℝ) ≤ 1 / (q - 1) := by
    rw [le_div_iff₀ hden]
    linarith
  obtain ⟨d, hd, hrem⟩ :=
    exists_binary_expansion_with_remainder_bounds hq1 hq2.le zero_le_one hone
  let s : ℕ → ℤ := expansionSignedDigits d
  let f : ℕ → ℝ := fun n ↦
    (reversedPolynomial s n).eval₂ (algebraMap ℤ ℝ) q
  have hs : ∀ i, |s i| ≤ 1 := expansionSignedDigits_height_one hd
  have hfmem : ∀ n, f n ∈ SignedSpectrum q := fun n ↦
    reversedPolynomial_eval_mem_signedSpectrum hs n
  have hfabs : ∀ n, |f n| ≤ 1 / (q - 1) := by
    intro n
    have hident : f n = -q ^ n * expansionRemainder q d n := by
      simpa [f, s] using expansion_tail_identity hq0 d n
    have hrem' :
        0 ≤ expansionRemainder q d n ∧
          expansionRemainder q d n ≤ (q⁻¹) ^ n / (q - 1) := by
      simpa [expansionRemainder] using hrem n
    rw [hident]
    have habs : |-q ^ n * expansionRemainder q d n| =
        q ^ n * expansionRemainder q d n := by
      rw [abs_mul, abs_neg, abs_pow, abs_of_pos (lt_trans zero_lt_one hq1),
        abs_of_nonneg hrem'.1]
    rw [habs]
    calc
      q ^ n * expansionRemainder q d n ≤
          q ^ n * ((q⁻¹) ^ n / (q - 1)) :=
        mul_le_mul_of_nonneg_left hrem'.2 (pow_nonneg (le_trans zero_le_one hq1.le) n)
      _ = 1 / (q - 1) := by
        rw [div_eq_mul_inv, ← mul_assoc, ← mul_pow]
        simp [hq0]
  have hfinite : (Set.range f).Finite :=
    finite_of_bounded_subset_no_accumulation hno
      (by rintro _ ⟨n, rfl⟩; exact hfmem n) (1 / (q - 1))
      (by
        rintro _ ⟨n, rfl⟩
        exact (abs_le.mp (hfabs n)))
  let g : ℕ → Set.range f := fun n ↦ ⟨f n, Set.mem_range_self n⟩
  letI : Finite (Set.range f) := hfinite
  obtain ⟨m, n, hmn, heq⟩ := Finite.exists_ne_map_eq_of_infinite g
  have heq' : f m = f n := congr_arg Subtype.val heq
  have pair_integral : ∀ {a b : ℕ}, a < b → f a = f b → IsIntegral ℤ q := by
    intro a b hab heval
    let p : ℤ[X] := -(reversedPolynomial s b - reversedPolynomial s a)
    have hbdeg : (reversedPolynomial s b).natDegree ≤ b := by
      unfold reversedPolynomial
      exact Nat.lt_succ_iff.mp (Polynomial.ofFn_natDegree_lt (by omega) _)
    have hadeg : (reversedPolynomial s a).natDegree ≤ b := by
      apply le_trans _ hab.le
      unfold reversedPolynomial
      exact Nat.lt_succ_iff.mp (Polynomial.ofFn_natDegree_lt (by omega) _)
    have hpdeg : p.natDegree ≤ b := by
      have hsub := Polynomial.natDegree_sub_le_of_le hbdeg hadeg
      simpa [p] using Polynomial.natDegree_neg_le_of_le hsub
    have hpcoeff : p.coeff b = 1 := by
      simp [p, reversedPolynomial_coeff, hab.le, not_le.mpr hab,
        s, expansionSignedDigits]
    have hpmonic : p.Monic :=
      Polynomial.monic_of_natDegree_le_of_coeff_eq_one b hpdeg hpcoeff
    have hpeval : p.eval₂ (algebraMap ℤ ℝ) q = 0 := by
      simp [p, f] at heval ⊢
      linarith
    exact ⟨p, hpmonic, hpeval⟩
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact pair_integral hlt heq'
  · exact pair_integral hgt heq'.symm

lemma eval₂_eq_at_conjugate_of_eval₂_eq {q : ℝ} (hqint : IsIntegral ℤ q)
    {z : ℂ}
    (hz : ((minpoly ℤ q).map (algebraMap ℤ ℂ)).eval z = 0)
    {P Q : ℤ[X]}
    (hPQ : P.eval₂ (algebraMap ℤ ℝ) q = Q.eval₂ (algebraMap ℤ ℝ) q) :
    P.eval₂ (algebraMap ℤ ℂ) z = Q.eval₂ (algebraMap ℤ ℂ) z := by
  have hrootq : Polynomial.aeval q (P - Q) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_sub, hPQ, sub_self]
  obtain ⟨C, hC⟩ := minpoly.isIntegrallyClosed_dvd hqint hrootq
  have hrootz : (P - Q).eval₂ (algebraMap ℤ ℂ) z = 0 := by
    rw [hC, Polynomial.eval₂_mul]
    have hz' : (minpoly ℤ q).eval₂ (algebraMap ℤ ℂ) z = 0 := by
      simpa [Polynomial.eval₂_eq_eval_map] using hz
    rw [hz', zero_mul]
  simpa [Polynomial.eval₂_sub, sub_eq_zero] using hrootz

lemma finite_reversed_tail_range_at_conjugate {q : ℝ}
    (hqint : IsIntegral ℤ q) (hno : ¬ HasAccumulation (SignedSpectrum q))
    {z : ℂ} (hz : ((minpoly ℤ q).map (algebraMap ℤ ℂ)).eval z = 0)
    {s : ℕ → ℤ} (hs : ∀ i, |s i| ≤ 1) {M : ℝ}
    (hbound : ∀ n,
      |(reversedPolynomial s n).eval₂ (algebraMap ℤ ℝ) q| ≤ M) :
    (Set.range fun n ↦
      (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z).Finite := by
  let fq : ℕ → ℝ := fun n ↦
    (reversedPolynomial s n).eval₂ (algebraMap ℤ ℝ) q
  let fz : ℕ → ℂ := fun n ↦
    (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z
  have hqfinite : (Set.range fq).Finite :=
    finite_of_bounded_subset_no_accumulation hno
      (by
        rintro _ ⟨n, rfl⟩
        exact reversedPolynomial_eval_mem_signedSpectrum hs n)
      M
      (by
        rintro _ ⟨n, rfl⟩
        exact abs_le.mp (hbound n))
  let chooseIndex : Set.range fq → ℕ := fun y ↦ Classical.choose y.property
  have hchoose : ∀ y : Set.range fq, fq (chooseIndex y) = y := by
    intro y
    exact Classical.choose_spec y.property
  letI : Finite (Set.range fq) := hqfinite
  let F : Set.range fq → ℂ := fun y ↦ fz (chooseIndex y)
  have hFrange : (Set.range F).Finite := Set.finite_range F
  apply hFrange.subset
  rintro _ ⟨n, rfl⟩
  let y : Set.range fq := ⟨fq n, Set.mem_range_self n⟩
  refine ⟨y, ?_⟩
  have hqeq : fq (chooseIndex y) = fq n := by
    simpa [y] using hchoose y
  have hzeq : fz (chooseIndex y) = fz n := by
    apply eval₂_eq_at_conjugate_of_eval₂_eq hqint hz
    exact hqeq
  simpa [F, fz] using hzeq

lemma inv_pow_mul_eval₂_reversedPolynomial {z : ℂ} (hz0 : z ≠ 0)
    (s : ℕ → ℤ) (n : ℕ) :
    z⁻¹ ^ n * (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z =
      ∑ i ∈ Finset.range (n + 1), (s i : ℂ) * z⁻¹ ^ i := by
  have heval (r : ℕ) :
      (reversedPolynomial s r).eval₂ (algebraMap ℤ ℂ) z =
        ∑ i ∈ Finset.range (r + 1), (s i : ℂ) * z ^ (r - i) := by
    rw [reversedPolynomial, Polynomial.eval₂_eq_sum_range' (algebraMap ℤ ℂ)
      (Polynomial.ofFn_natDegree_lt (by omega) (fun j : Fin (r + 1) ↦ s (r - j.1))) z]
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ r := by simpa using hi
    rw [Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega)]
    simp only [Nat.succ_sub_succ_eq_sub]
    simp [Nat.sub_sub_self hi']
  have hsucc (r : ℕ) :
      (reversedPolynomial s (r + 1)).eval₂ (algebraMap ℤ ℂ) z =
        z * (reversedPolynomial s r).eval₂ (algebraMap ℤ ℂ) z + s (r + 1) := by
    rw [heval, heval, Finset.sum_range_succ]
    simp only [Nat.sub_self, pow_zero, mul_one]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ r := by simpa using hi
    rw [show r + 1 - i = (r - i) + 1 by omega, pow_succ]
    ring
  induction n with
  | zero =>
      rw [heval]
      simp
  | succ n ih =>
      rw [hsucc, Finset.sum_range_succ]
      rw [pow_succ z⁻¹, mul_add]
      have hcancel : z⁻¹ * z = 1 := inv_mul_cancel₀ hz0
      calc
        z⁻¹ ^ n * z⁻¹ * (z *
              (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z) +
            z⁻¹ ^ n * z⁻¹ * (s (n + 1) : ℂ) =
            z⁻¹ ^ n * (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z +
              z⁻¹ ^ n * (z⁻¹ * (s (n + 1) : ℂ)) := by
          have hfirst :
              z⁻¹ ^ n * z⁻¹ *
                  (z * (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z) =
                z⁻¹ ^ n * (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z := by
            calc
              _ = z⁻¹ ^ n * ((z⁻¹ * z) *
                    (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z) := by ring
              _ = _ := by rw [hcancel, one_mul]
          rw [hfirst]
          ring
        _ = ∑ i ∈ Finset.range (n + 1), (s i : ℂ) * z⁻¹ ^ i +
              (s (n + 1) : ℂ) * (z⁻¹ ^ n * z⁻¹) := by
          rw [ih]
          ring

lemma hasSum_zero_of_finite_reversed_tail_range {z : ℂ} (hz : 1 < ‖z‖)
    {s : ℕ → ℤ} (hs : ∀ i, |s i| ≤ 1)
    (hfinite : (Set.range fun n ↦
      (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z).Finite) :
    HasSum (fun i ↦ (s i : ℂ) * z⁻¹ ^ i) 0 := by
  have hz0 : z ≠ 0 := by
    intro h
    norm_num [h] at hz
  have hinv : ‖z⁻¹‖ < 1 := by
    rw [norm_inv, inv_lt_one₀ (norm_pos_iff.mpr hz0)]
    exact hz
  have hsummable : Summable (fun i ↦ (s i : ℂ) * z⁻¹ ^ i) := by
    apply Summable.of_norm_bounded
      (summable_geometric_of_lt_one (norm_nonneg z⁻¹) hinv)
    intro i
    rw [norm_mul, norm_pow]
    have hscast : ‖(s i : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast hs i
    exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) hscast
  let f : ℕ → ℂ := fun n ↦
    (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z
  obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.mp hfinite.isCompact.isBounded
  have hC0 : 0 ≤ C := le_trans (dist_nonneg : 0 ≤ dist (f 0) (f 0)) (hC 0 0)
  have hfnorm : ∀ n, ‖f n‖ ≤ C + ‖f 0‖ := by
    intro n
    calc
      ‖f n‖ = ‖(f n - f 0) + f 0‖ := by ring_nf
      _ ≤ ‖f n - f 0‖ + ‖f 0‖ := norm_add_le _ _
      _ = dist (f n) (f 0) + ‖f 0‖ := by rw [dist_eq_norm]
      _ ≤ C + ‖f 0‖ := by
        have hCn : dist (f n) (f 0) ≤ C := by
          change dist
            ((reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z)
            ((reversedPolynomial s 0).eval₂ (algebraMap ℤ ℂ) z) ≤ C
          exact hC n 0
        simpa [add_comm] using add_le_add_right hCn ‖f 0‖
  have hpow : Tendsto (fun n : ℕ ↦ ‖z⁻¹‖ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hinv
  have hcap : Tendsto (fun n : ℕ ↦ ‖z⁻¹‖ ^ n * (C + ‖f 0‖)) atTop (𝓝 0) := by
    simpa using hpow.mul_const (C + ‖f 0‖)
  have hprod : Tendsto (fun n ↦ z⁻¹ ^ n * f n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (g := fun n ↦ ‖z⁻¹‖ ^ n * (C + ‖f 0‖)) ?_ ?_ hcap
    · intro n; positivity
    · intro n
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hfnorm n) (pow_nonneg (norm_nonneg _) _)
  apply (hsummable.hasSum_iff_tendsto_nat).mpr
  apply (tendsto_add_atTop_iff_nat 1).mp
  convert hprod using 1
  funext n
  simpa [f, Nat.add_comm] using (inv_pow_mul_eval₂_reversedPolynomial hz0 s n).symm

lemma conjugate_not_positive_real_of_no_accumulation {q p : ℝ}
    (hq1 : 1 < q) (hq2 : q < 2)
    (hno : ¬ HasAccumulation (SignedSpectrum q))
    (hp1 : 1 < p) (hpq : p ≠ q)
    (hpRoot : ((minpoly ℤ q).map (algebraMap ℤ ℂ)).eval (p : ℂ) = 0) : False := by
  have hqint : IsIntegral ℤ q := integral_of_no_signedSpectrum_accumulation hq1 hq2 hno
  have hone : (1 : ℝ) ≤ 1 / (q - 1) := by
    rw [le_div_iff₀ (sub_pos.mpr hq1)]
    linarith
  obtain ⟨d, hd, hdsum⟩ := exists_binary_expansion hq1 hq2.le zero_le_one hone
  let s : ℕ → ℤ := expansionSignedDigits d
  have hs : ∀ i, |s i| ≤ 1 := expansionSignedDigits_height_one hd
  have hsExp : SignedExpansion q s := hasSum_expansionSignedDigits hq1 hd hdsum
  have hfinite : (Set.range fun n ↦
      (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) (p : ℂ)).Finite :=
    finite_reversed_tail_range_at_conjugate hqint hno hpRoot hs
      (fun n ↦ reversed_tail_bound_of_signedExpansion hq1 hs hsExp n)
  have hpNorm : 1 < ‖(p : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact hp1
  have hsumC : HasSum (fun i ↦ (s i : ℂ) * (p : ℂ)⁻¹ ^ i) 0 :=
    hasSum_zero_of_finite_reversed_tail_range hpNorm hs hfinite
  have hsumR : HasSum (fun i ↦ (s i : ℝ) * p⁻¹ ^ i) 0 := by
    apply Complex.hasSum_ofReal.mp
    convert hsumC using 1
    · funext i
      norm_cast
    · rfl
  have hne : (∑' i, (s i : ℝ) * p⁻¹ ^ i) ≠ 0 := by
    rw [show (∑' i, (s i : ℝ) * p⁻¹ ^ i) =
        -1 + ∑' i, (d i : ℝ) * p⁻¹ ^ (i + 1) by
      simpa [s] using tsum_expansionSignedDigits hp1 hd]
    intro hz
    have honep : (∑' i, (d i : ℝ) * p⁻¹ ^ (i + 1)) = 1 := by linarith
    exact binary_digit_tsum_ne_one_of_ne hq1 hp1 hpq hd hdsum honep
  exact hne hsumR.tsum_eq

end
end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos1096/Erdos1096UnitCircle.lean` -/

section
open Filter Set Polynomial
open scoped BigOperators Pointwise Topology ComplexConjugate

noncomputable section



lemma unit_separator_prefix {p : ℂ} (hpNorm : ‖p‖ = 1) (hpNe : p ≠ 1) :
    let w : ℂ := 1 - p
    0 < w.re ∧ ∀ k : ℕ,
      ∑ i ∈ Finset.range k, (w * p⁻¹ ^ (i + 1)).re < w.re := by
  let w : ℂ := 1 - p
  have hp0 : p ≠ 0 := by
    intro hp
    simp [hp] at hpNorm
  have hpre : p.re < 1 := by
    have hle : p.re ≤ ‖p‖ := Complex.re_le_norm p
    rw [hpNorm] at hle
    exact lt_of_le_of_ne hle (by
      intro h
      have hre : p.re = 1 := h
      have him : p.im = 0 := by
        have hnormSq : Complex.normSq p = 1 := by
          rw [show Complex.normSq p = ‖p‖ ^ 2 from RCLike.normSq_eq_def' p, hpNorm]
          norm_num
        rw [Complex.normSq_apply, hre] at hnormSq
        nlinarith [sq_nonneg p.im]
      apply hpNe
      apply Complex.ext
      · simpa using hre
      · simpa using him)
  refine ⟨by simp [w]; linarith, fun k ↦ ?_⟩
  have htel : ∑ i ∈ Finset.range k, (1 - p) * p⁻¹ ^ (i + 1) = p⁻¹ ^ k - 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        have hcancel : p * p⁻¹ ^ (k + 1) = p⁻¹ ^ k := by
          rw [pow_succ]
          calc
            p * (p⁻¹ ^ k * p⁻¹) = p⁻¹ ^ k * (p * p⁻¹) := by ring
            _ = p⁻¹ ^ k := by simp [hp0]
        rw [sub_mul, one_mul, hcancel]
        ring
  have hreSum :
      (∑ i ∈ Finset.range k, ((1 - p) * p⁻¹ ^ (i + 1)).re) =
        (∑ i ∈ Finset.range k, (1 - p) * p⁻¹ ^ (i + 1)).re := by
    simpa only [Complex.reCLM_apply] using
      (map_sum (Complex.reCLM : ℂ →L[ℝ] ℝ)
        (fun i ↦ (1 - p) * p⁻¹ ^ (i + 1)) (Finset.range k)).symm
  rw [hreSum, htel]
  calc
    (p⁻¹ ^ k - 1).re ≤ ‖p⁻¹ ^ k‖ - 1 := by
      simp only [map_sub, Complex.sub_re, Complex.one_re]
      exact sub_le_sub_right (Complex.re_le_norm _) 1
    _ = 0 := by rw [norm_pow, norm_inv, hpNorm]; norm_num
    _ < (1 - p).re := by simp; linarith

lemma unit_separator_term_ne_zero {p : ℂ} (hpNorm : ‖p‖ = 1) (hpNe : p ≠ 1)
    (hpow : ∀ m : ℕ, 0 < m → p ^ m ≠ 1) (n : ℕ) :
    ((1 - p) * p⁻¹ ^ (n + 1)).re ≠ 0 := by
  have hp0 : p ≠ 0 := by
    intro hp
    simp [hp] at hpNorm
  intro hz
  let z : ℂ := (1 - p) * p⁻¹ ^ (n + 1)
  have hz' : z.re = 0 := by simpa [z] using hz
  have hzconj : conj z = -z := by
    apply Complex.ext
    · simp only [Complex.conj_re, Complex.neg_re, hz', neg_zero]
    · simp only [Complex.conj_im, Complex.neg_im]
  have hconjp : conj p = p⁻¹ := (Complex.inv_eq_conj hpNorm).symm
  have hconjz : conj z = (1 - p⁻¹) * p ^ (n + 1) := by
    simp [z, map_mul, hconjp, Complex.conj_inv, hp0]
  have hzsum : (1 - p) * p⁻¹ ^ (n + 1) + (1 - p⁻¹) * p ^ (n + 1) = 0 := by
    change z + (1 - p⁻¹) * p ^ (n + 1) = 0
    rw [← hconjz, hzconj, add_neg_cancel]
  have hfactor : (1 - p) * (1 - p ^ (2 * n + 1)) = 0 := by
    have hcancelSucc : p ^ (n + 1) * p⁻¹ ^ (n + 1) = 1 := by
      rw [← mul_pow]
      simp [hp0]
    have hinvPow : p⁻¹ * p ^ (n + 1) = p ^ n := by
      rw [pow_succ]
      calc
        p⁻¹ * (p ^ n * p) = p ^ n * (p⁻¹ * p) := by ring
        _ = p ^ n := by simp [hp0]
    have hterm1 : p ^ (n + 1) * ((1 - p) * p⁻¹ ^ (n + 1)) = 1 - p := by
      calc
        _ = (1 - p) * (p ^ (n + 1) * p⁻¹ ^ (n + 1)) := by ring
        _ = 1 - p := by rw [hcancelSucc, mul_one]
    have hinner : (1 - p⁻¹) * p ^ (n + 1) = (p - 1) * p ^ n := by
      rw [sub_mul, one_mul, hinvPow]
      rw [pow_succ]
      ring
    have hterm2 : p ^ (n + 1) * ((1 - p⁻¹) * p ^ (n + 1)) =
        (p - 1) * p ^ (2 * n + 1) := by
      rw [hinner]
      calc
        p ^ (n + 1) * ((p - 1) * p ^ n) = (p - 1) * (p ^ (n + 1) * p ^ n) := by ring
        _ = (p - 1) * p ^ (2 * n + 1) := by
          rw [← pow_add]
          congr 2
          omega
    calc
      (1 - p) * (1 - p ^ (2 * n + 1)) = p ^ (n + 1) *
          ((1 - p) * p⁻¹ ^ (n + 1) + (1 - p⁻¹) * p ^ (n + 1)) := by
            rw [mul_add, hterm1, hterm2]
            ring
      _ = 0 := by rw [hzsum, mul_zero]
  rcases mul_eq_zero.mp hfactor with hpone | hroot
  · exact hpNe (sub_eq_zero.mp hpone).symm
  · apply hpow (2 * n + 1) (by omega)
    exact (sub_eq_zero.mp hroot).symm

lemma exists_vertical_integer_approx {v : ℂ} {c : ℝ} (hc : 0 < c) (hv : ‖v‖ = c) :
    ∃ k : ℤ, |k| = 1 ∧ |v.im - c * k| ≤ v.re ^ 2 / c := by
  have him : |v.im| ≤ c := by
    rw [← hv]
    simpa [Real.norm_eq_abs] using RCLike.norm_im_le_norm v
  have hcircle : v.re ^ 2 + v.im ^ 2 = c ^ 2 := by
    have hsq : Complex.normSq v = c ^ 2 := by
      rw [show Complex.normSq v = ‖v‖ ^ 2 from RCLike.normSq_eq_def' v, hv]
    simpa [Complex.normSq_apply, pow_two] using hsq
  by_cases hy : 0 ≤ v.im
  · refine ⟨1, by norm_num, ?_⟩
    have hyc : v.im ≤ c := by simpa [abs_of_nonneg hy] using him
    rw [Int.cast_one, mul_one, abs_of_nonpos (sub_nonpos.mpr hyc)]
    apply (le_div_iff₀ hc).2
    nlinarith [sq_nonneg (c - v.im)]
  · refine ⟨-1, by norm_num, ?_⟩
    have hyneg : v.im < 0 := lt_of_not_ge hy
    have hyc : -v.im ≤ c := by simpa [abs_of_neg hyneg] using him
    rw [Int.cast_neg, Int.cast_one, mul_neg, mul_one, abs_of_nonneg (by linarith)]
    apply (le_div_iff₀ hc).2
    nlinarith [sq_nonneg (c + v.im)]

lemma exists_vertical_integer_approx_height_one {p w : ℂ} {s : ℤ}
    (hp : ‖p‖ = 1) (hw : w ≠ 0) (hs : |s| ≤ 1) (i : ℕ) :
    ∃ k : ℤ, |((s : ℂ) * (w * p⁻¹ ^ i)).im - ‖w‖ * k| ≤
      (((s : ℂ) * (w * p⁻¹ ^ i)).re) ^ 2 / ‖w‖ := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rcases Int.abs_le_one_iff.mp hs with hs | hs | hs
  · subst s
    exact ⟨0, by simp⟩
  · subst s
    have hvnorm : ‖(1 : ℂ) * (w * p⁻¹ ^ i)‖ = ‖w‖ := by
      simp [norm_pow, norm_inv, hp]
    obtain ⟨k, -, hk⟩ := exists_vertical_integer_approx hwpos hvnorm
    exact ⟨k, by simpa using hk⟩
  · subst s
    have hvnorm : ‖(-1 : ℂ) * (w * p⁻¹ ^ i)‖ = ‖w‖ := by
      simp [norm_pow, norm_inv, hp]
    obtain ⟨k, -, hk⟩ := exists_vertical_integer_approx hwpos hvnorm
    exact ⟨k, by simpa using hk⟩

/-- Infinite pigeonhole extraction used in the unit-circle branch of the
corrected Erdős--Komornik conjugate argument. -/
lemma exists_tail_pair_same_norm_and_im_sign {S : ℕ → ℂ} {s : ℕ → ℤ}
    (hsupp : {i | s i ≠ 0}.Infinite)
    (hnorm : (Set.range fun n ↦ ‖S n‖).Finite) (N : ℕ) :
    ∃ r t : ℕ, N ≤ r ∧ r < t ∧ s r ≠ 0 ∧ s t ≠ 0 ∧
      ‖S r‖ = ‖S t‖ ∧ (0 ≤ (S r).im ↔ 0 ≤ (S t).im) := by
  let A : Set ℕ := {i | N ≤ i ∧ s i ≠ 0}
  have hA : A.Infinite := by
    have htail := hsupp.sdiff (Set.finite_Iio N)
    have heq : {i | s i ≠ 0} \ Set.Iio N = A := by
      ext i
      simp [A, and_comm, not_lt]
    simpa [heq] using htail
  let R : Set ℝ := Set.range fun n ↦ ‖S n‖
  let color : A → R × Bool := fun i ↦
    (⟨‖S i.1‖, Set.mem_range_self i.1⟩, decide (0 ≤ (S i.1).im))
  letI : Infinite A := hA.to_subtype
  letI : Finite R := hnorm
  obtain ⟨i, j, hij, hc⟩ := Finite.exists_ne_map_eq_of_infinite color
  have hij' : i.1 ≠ j.1 := by
    intro h
    apply hij
    exact Subtype.ext h
  have hnormij : ‖S i.1‖ = ‖S j.1‖ := by
    have h := congrArg (fun z : R × Bool ↦ z.1.1) hc
    simpa [color] using h
  have hsignij : (0 ≤ (S i.1).im ↔ 0 ≤ (S j.1).im) := by
    have h := congrArg (fun z : R × Bool ↦ z.2) hc
    change decide (0 ≤ (S i.1).im) = decide (0 ≤ (S j.1).im) at h
    exact decide_eq_decide.mp h
  rcases lt_or_gt_of_ne hij' with hijlt | hjilt
  · exact ⟨i.1, j.1, i.2.1, hijlt, i.2.2, j.2.2, hnormij, hsignij⟩
  · exact ⟨j.1, i.1, j.2.1, hjilt, j.2.2, i.2.2, hnormij.symm, hsignij.symm⟩

def unitWeightedPartialSum (p w : ℂ) (s : ℕ → ℤ) (n : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (n + 1), (s i : ℂ) * (w * p⁻¹ ^ i)

lemma unitWeightedPartialSum_succ (p w : ℂ) (s : ℕ → ℤ) (n : ℕ) :
    unitWeightedPartialSum p w s (n + 1) = unitWeightedPartialSum p w s n +
      (s (n + 1) : ℂ) * (w * p⁻¹ ^ (n + 1)) := by
  simp [unitWeightedPartialSum, Finset.sum_range_succ]

lemma unitWeightedPartialSum_re_converges {p w : ℂ} {s : ℕ → ℤ} {K : ℕ}
    (hfinite : (Set.range fun n ↦ ‖unitWeightedPartialSum p w s n‖).Finite)
    (hstep : ∀ i, K < i →
      ((s i : ℂ) * (w * p⁻¹ ^ i)).re ≤ 0) :
    ∃ L : ℝ, Tendsto (fun n ↦ (unitWeightedPartialSum p w s (K + n)).re)
      atTop (𝓝 L) := by
  let S : ℕ → ℂ := unitWeightedPartialSum p w s
  obtain ⟨C, hC⟩ := hfinite.bddAbove
  have hnorm : ∀ n, ‖S n‖ ≤ C := by
    intro n
    exact hC ⟨n, rfl⟩
  let x : ℕ → ℝ := fun n ↦ (S (K + n)).re
  have hxanti : Antitone x := antitone_nat_of_succ_le (fun n ↦ by
    have hrec := unitWeightedPartialSum_succ p w s (K + n)
    have hnonpos := hstep (K + n + 1) (by omega)
    dsimp only [x, S]
    rw [show K + (n + 1) = (K + n) + 1 by omega, hrec]
    simp only [map_add, Complex.add_re]
    linarith)
  have hxbdd : BddBelow (Set.range x) := by
    refine ⟨-C, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hre : |(S (K + n)).re| ≤ C := by
      exact (RCLike.norm_re_le_norm _).trans (hnorm (K + n))
    exact (abs_le.mp hre).1
  exact Real.tendsto_of_bddBelow_antitone hxbdd hxanti

lemma unitWeightedPartialSum_vertical_lattice_approx {p w : ℂ} {s : ℕ → ℤ}
    {r t : ℕ} {δ : ℝ} (hp : ‖p‖ = 1) (hw : w ≠ 0)
    (hs : ∀ i, |s i| ≤ 1) (hrt : r < t)
    (hnonpos : ∀ i, r < i → i ≤ t →
      ((s i : ℂ) * (w * p⁻¹ ^ i)).re ≤ 0)
    (hsmall : ∀ i, r < i → i ≤ t →
      |((s i : ℂ) * (w * p⁻¹ ^ i)).re| ≤ δ * ‖w‖) :
    ∃ k : ℤ,
      |(unitWeightedPartialSum p w s t - unitWeightedPartialSum p w s r).im -
          ‖w‖ * k| ≤
        δ * ((unitWeightedPartialSum p w s r).re -
          (unitWeightedPartialSum p w s t).re) := by
  classical
  let v : ℕ → ℂ := fun i ↦ (s i : ℂ) * (w * p⁻¹ ^ i)
  let I : Finset ℕ := Finset.Ico (r + 1) (t + 1)
  let k : ℕ → ℤ := fun i ↦ Classical.choose
    (exists_vertical_integer_approx_height_one hp hw (hs i) i)
  have hk (i : ℕ) :
      |(v i).im - ‖w‖ * k i| ≤ (v i).re ^ 2 / ‖w‖ := by
    simpa [v, k] using
      (Classical.choose_spec (exists_vertical_integer_approx_height_one hp hw (hs i) i))
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hterm (i : ℕ) (hi : i ∈ I) :
      |(v i).im - ‖w‖ * k i| ≤ δ * (-(v i).re) := by
    have hi' : i ∈ Finset.Ico (r + 1) (t + 1) := by simpa [I] using hi
    have hiBounds := Finset.mem_Ico.mp hi'
    have hir : r < i := by omega
    have hit : i ≤ t := by omega
    have hvnonpos := hnonpos i hir hit
    have hvsmall := hsmall i hir hit
    have hneg : -(v i).re ≤ δ * ‖w‖ := by
      rw [abs_of_nonpos hvnonpos] at hvsmall
      exact hvsmall
    apply (hk i).trans
    apply (div_le_iff₀ hwpos).2
    nlinarith [sq_nonneg ((v i).re)]
  have hsum : ∑ i ∈ I, v i =
      unitWeightedPartialSum p w s t - unitWeightedPartialSum p w s r := by
    simp only [I, unitWeightedPartialSum, v]
    exact Finset.sum_Ico_eq_sub _ (by omega)
  refine ⟨∑ i ∈ I, k i, ?_⟩
  have himag :
      (unitWeightedPartialSum p w s t - unitWeightedPartialSum p w s r).im -
          ‖w‖ * (∑ i ∈ I, k i : ℤ) =
        ∑ i ∈ I, ((v i).im - ‖w‖ * k i) := by
    have hreim : (∑ i ∈ I, v i).im = ∑ i ∈ I, (v i).im := by
      simpa only [Complex.imCLM_apply] using
        (map_sum (Complex.imCLM : ℂ →L[ℝ] ℝ) v I)
    rw [← hsum, hreim, Int.cast_sum]
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [himag]
  calc
    |∑ i ∈ I, ((v i).im - ‖w‖ * k i)| ≤
        ∑ i ∈ I, |(v i).im - ‖w‖ * k i| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ I, δ * (-(v i).re) := by
      exact Finset.sum_le_sum fun i hi ↦ hterm i hi
    _ = δ * ((unitWeightedPartialSum p w s r).re -
          (unitWeightedPartialSum p w s t).re) := by
      rw [← Finset.mul_sum]
      have hre : (∑ i ∈ I, v i).re = ∑ i ∈ I, (v i).re := by
        simpa only [Complex.reCLM_apply] using
          (map_sum (Complex.reCLM : ℂ →L[ℝ] ℝ) v I)
      rw [hsum] at hre
      simp only [map_sub, Complex.sub_re] at hre
      have hneg : ∑ i ∈ I, -(v i).re = -(∑ i ∈ I, (v i).re) := by
        rw [Finset.sum_neg_distrib]
      rw [hneg, ← hre]
      ring

lemma abs_sub_le_abs_add_of_same_sign {a b : ℝ} (h : 0 ≤ a ↔ 0 ≤ b) :
    |a - b| ≤ |a + b| := by
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := h.mp ha
    rw [abs_of_nonneg (add_nonneg ha hb)]
    rcases le_total a b with hab | hba
    · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
      linarith
  · have ha' : a < 0 := lt_of_not_ge ha
    have hb' : b < 0 := lt_of_not_ge (mt h.mpr ha)
    rw [abs_of_neg (add_neg ha' hb')]
    rcases le_total a b with hab | hba
    · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
      linarith

lemma equal_norm_chord_product {z u : ℂ} (h : ‖z‖ = ‖u‖) :
    |z.re - u.re| * |z.re + u.re| = |z.im - u.im| * |z.im + u.im| := by
  have hsq : z.re ^ 2 + z.im ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    have hn : Complex.normSq z = Complex.normSq u := by
      rw [show Complex.normSq z = ‖z‖ ^ 2 from RCLike.normSq_eq_def' z,
        show Complex.normSq u = ‖u‖ ^ 2 from RCLike.normSq_eq_def' u, h]
    simpa [Complex.normSq_apply, pow_two] using hn
  rw [← abs_mul, ← abs_mul]
  rw [show (z.re - u.re) * (z.re + u.re) =
      -((z.im - u.im) * (z.im + u.im)) by nlinarith, abs_neg]

lemma same_half_circle_chord_sq_le {z u : ℂ} (hnorm : ‖z‖ = ‖u‖)
    (hsign : 0 ≤ z.im ↔ 0 ≤ u.im) :
    |z.im - u.im| ^ 2 ≤ |z.re - u.re| * |z.re + u.re| := by
  calc
    |z.im - u.im| ^ 2 = |z.im - u.im| * |z.im - u.im| := by ring
    _ ≤ |z.im - u.im| * |z.im + u.im| :=
      mul_le_mul_of_nonneg_left (abs_sub_le_abs_add_of_same_sign hsign) (abs_nonneg _)
    _ = |z.re - u.re| * |z.re + u.re| := (equal_norm_chord_product hnorm).symm

lemma unitWeightedPartialSum_norm_range_infinite {p w : ℂ} {s : ℕ → ℤ} {K : ℕ}
    (hp : ‖p‖ = 1) (hw : w ≠ 0) (hs : ∀ i, |s i| ≤ 1)
    (hsupp : {i | s i ≠ 0}.Infinite)
    (hstep : ∀ i, K < i → ((s i : ℂ) * (w * p⁻¹ ^ i)).re ≤ 0)
    (hstrict : ∀ i, K < i → s i ≠ 0 →
      ((s i : ℂ) * (w * p⁻¹ ^ i)).re < 0)
    (hstart : (unitWeightedPartialSum p w s K).re < 0) :
    (Set.range fun n ↦ ‖unitWeightedPartialSum p w s n‖).Infinite := by
  classical
  intro hfinite
  let S : ℕ → ℂ := unitWeightedPartialSum p w s
  let c : ℝ := ‖w‖
  have hc : 0 < c := by exact norm_pos_iff.mpr hw
  obtain ⟨C, hC⟩ := hfinite.bddAbove
  let B : ℝ := max 1 C
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hSnorm : ∀ n, ‖S n‖ ≤ B := by
    intro n
    exact (hC ⟨n, rfl⟩).trans (le_max_right _ _)
  have hSre (n : ℕ) : |(S n).re| ≤ B :=
    (RCLike.norm_re_le_norm _).trans (hSnorm n)
  have hSim (n : ℕ) : |(S n).im| ≤ B :=
    (RCLike.norm_im_le_norm _).trans (hSnorm n)
  let c0 : ℝ := -(S K).re
  have hc0 : 0 < c0 := by dsimp [c0, S]; linarith
  let δ : ℝ := min (c / (16 * B)) (c0 / (4 * B))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (div_pos hc (by positivity)) (div_pos hc0 (by positivity))
  have hδc : δ ≤ c / (16 * B) := min_le_left _ _
  have hδc0 : δ ≤ c0 / (4 * B) := min_le_right _ _
  let E : ℝ := min (δ * c / 4) (c ^ 2 / (256 * B))
  have hE : 0 < E := by
    dsimp [E]
    exact lt_min (div_pos (mul_pos hδ hc) (by norm_num))
      (div_pos (sq_pos_of_pos hc) (by positivity))
  have hEδ : E ≤ δ * c / 4 := min_le_left _ _
  have hEc : E ≤ c ^ 2 / (256 * B) := min_le_right _ _
  obtain ⟨L, hconv⟩ := unitWeightedPartialSum_re_converges hfinite hstep
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv E hE
  have hnear {i : ℕ} (hi : K + N ≤ i) : |(S i).re - L| < E := by
    have hiK : K ≤ i := le_trans (Nat.le_add_right K N) hi
    have hiN : N ≤ i - K := by omega
    have h := hN (i - K) hiN
    have hidx : K + (i - K) = i := by omega
    simpa [S, Real.dist_eq, hidx] using h
  have hxanti : Antitone (fun n ↦ (S (K + n)).re) :=
    antitone_nat_of_succ_le (fun n ↦ by
      have hrec := unitWeightedPartialSum_succ p w s (K + n)
      have hn := hstep (K + n + 1) (by omega)
      dsimp only [S]
      rw [show K + (n + 1) = (K + n) + 1 by omega, hrec]
      simp only [Complex.add_re]
      linarith)
  obtain ⟨r, t, hrN, hrt, hsr, hst, hnormrt, hsignrt⟩ :=
    exists_tail_pair_same_norm_and_im_sign hsupp hfinite (K + N)
  have hrK : K ≤ r := le_trans (Nat.le_add_right K N) hrN
  have htK : K ≤ t := hrK.trans hrt.le
  have htailmono {a b : ℕ} (ha : K ≤ a) (hab : a ≤ b) : (S b).re ≤ (S a).re := by
    have := hxanti (Nat.sub_le_sub_right hab K)
    simpa [Nat.add_sub_of_le ha, Nat.add_sub_of_le (ha.trans hab)] using this
  have hrealrt : (S t).re < (S r).re := by
    have htpos : 0 < t := lt_of_le_of_lt (Nat.zero_le r) hrt
    have htstep := hstrict t (lt_of_le_of_lt hrK hrt) hst
    have hrec := unitWeightedPartialSum_succ p w s (t - 1)
    have htEq : t - 1 + 1 = t := by omega
    have hrprev : r ≤ t - 1 := by omega
    have hmono := htailmono hrK hrprev
    rw [htEq] at hrec
    dsimp only [S] at hrec hmono ⊢
    rw [hrec]
    simp only [Complex.add_re]
    linarith
  let H : ℝ := (S r).re - (S t).re
  have hH : 0 < H := by dsimp [H]; linarith
  have hHclose : H < 2 * E := by
    have hrnear := hnear hrN
    have htnear := hnear (hrN.trans hrt.le)
    dsimp only [H]
    have htri : |(S r).re - (S t).re| ≤
        |(S r).re - L| + |(S t).re - L| := by
      calc
        |(S r).re - (S t).re| ≤ |(S r).re - L| + |L - (S t).re| :=
          abs_sub_le _ _ _
        _ = _ := by rw [abs_sub_comm L]
    rw [abs_of_pos (by linarith)] at htri
    linarith
  have hHbound : H ≤ 2 * B := by
    have hrabs := hSre r
    have htabs := hSre t
    dsimp only [H]
    have hrle : (S r).re ≤ |(S r).re| := le_abs_self _
    have htle : -(S t).re ≤ |(S t).re| := neg_le_abs _
    linarith
  have hsmall : ∀ i, r < i → i ≤ t →
      |((s i : ℂ) * (w * p⁻¹ ^ i)).re| ≤ δ * ‖w‖ := by
    intro i hri hit
    have hiN : K + N ≤ i := hrN.trans hri.le
    have him1N : K + N ≤ i - 1 := by omega
    have hinear := hnear hiN
    have him1near := hnear him1N
    have hrec := unitWeightedPartialSum_succ p w s (i - 1)
    have hiEq : i - 1 + 1 = i := by omega
    rw [hiEq] at hrec
    have htermEq : ((s i : ℂ) * (w * p⁻¹ ^ i)).re =
        (S i).re - (S (i - 1)).re := by
      dsimp only [S]
      rw [hrec]
      simp
    rw [htermEq]
    apply le_of_lt
    calc
      |(S i).re - (S (i - 1)).re| ≤
          |(S i).re - L| + |L - (S (i - 1)).re| := abs_sub_le _ _ _
      _ = |(S i).re - L| + |(S (i - 1)).re - L| := by rw [abs_sub_comm L]
      _ < 2 * E := by linarith
      _ ≤ δ * c := by
        have : 2 * E ≤ δ * c / 2 := by linarith
        linarith
      _ = δ * ‖w‖ := rfl
  obtain ⟨k, hk⟩ := unitWeightedPartialSum_vertical_lattice_approx hp hw hs hrt
    (fun i hir hit ↦ hstep i (lt_of_le_of_lt hrK hir)) hsmall
  have himsq := same_half_circle_chord_sq_le hnormrt hsignrt
  have himsmall : |(S t).im - (S r).im| < c / 4 := by
    have hxsum : |(S r).re + (S t).re| ≤ 2 * B := by
      exact (abs_add_le _ _).trans (by linarith [hSre r, hSre t])
    have hdx : |(S r).re - (S t).re| = H := abs_of_pos hH
    have hprod : H * |(S r).re + (S t).re| < c ^ 2 / 16 := by
      rw [← hdx]
      calc
        |(S r).re - (S t).re| * |(S r).re + (S t).re| ≤ H * (2 * B) := by
          rw [hdx]
          exact mul_le_mul_of_nonneg_left hxsum hH.le
        _ < (2 * E) * (2 * B) := by nlinarith
        _ ≤ c ^ 2 / 16 := by
          have hEB : E * B ≤ (c ^ 2 / (256 * B)) * B :=
            mul_le_mul_of_nonneg_right hEc hB.le
          have hcancel : c ^ 2 / (256 * B) * B = c ^ 2 / 256 := by
            field_simp [ne_of_gt hB]
          have hEB' : E * B ≤ c ^ 2 / 256 := by
            calc E * B ≤ (c ^ 2 / (256 * B)) * B := hEB
              _ = c ^ 2 / 256 := hcancel
          nlinarith
    have hsq : |(S t).im - (S r).im| ^ 2 < c ^ 2 / 16 := by
      change |(S r).im - (S t).im| ^ 2 ≤
        |(S r).re - (S t).re| * |(S r).re + (S t).re| at himsq
      rw [abs_sub_comm]
      exact lt_of_le_of_lt himsq (by simpa [hdx] using hprod)
    nlinarith [sq_nonneg (|(S t).im - (S r).im|), sq_pos_of_pos hc]
  have hk' : |(S t).im - (S r).im - c * k| ≤ δ * H := by
    simpa [S, c, H, abs_sub_comm] using hk
  have hδH : δ * H ≤ c / 8 := by
    have hδB : δ * (2 * B) ≤ c / 8 := by
      calc
        δ * (2 * B) ≤ (c / (16 * B)) * (2 * B) :=
          mul_le_mul_of_nonneg_right hδc (by positivity)
        _ = c / 8 := by field_simp [ne_of_gt hB] <;> norm_num
    exact (mul_le_mul_of_nonneg_left hHbound hδ.le).trans hδB
  have hkabs : |c * (k : ℝ)| < c := by
    have htri : |c * (k : ℝ)| ≤ |(S t).im - (S r).im| +
        |(S t).im - (S r).im - c * k| := by
      calc
        |c * (k : ℝ)| = |((S t).im - (S r).im) -
            ((S t).im - (S r).im - c * k)| := by ring_nf
        _ = |((S t).im - (S r).im) +
            (-((S t).im - (S r).im - c * k))| := by ring
        _ ≤ |(S t).im - (S r).im| +
            |-((S t).im - (S r).im - c * k)| := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    linarith
  have hkzero : k = 0 := by
    by_contra hk0
    have hkoneZ : 1 ≤ |k| := Int.one_le_abs hk0
    have hkone : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast hkoneZ
    rw [abs_mul, abs_of_pos hc] at hkabs
    nlinarith
  have himfinal : |(S t).im - (S r).im| ≤ δ * H := by
    rw [hkzero] at hk'
    simpa using hk'
  have hrneg : (S r).re ≤ (S K).re := htailmono le_rfl hrK
  have htneg : (S t).re ≤ (S K).re := htailmono le_rfl htK
  have hxsumLower : 2 * c0 ≤ |(S r).re + (S t).re| := by
    rw [abs_of_neg (by dsimp [c0] at hc0; linarith)]
    dsimp [c0]
    linarith
  have hysumUpper : |(S r).im + (S t).im| ≤ 2 * B :=
    (abs_add_le _ _).trans (by linarith [hSim r, hSim t])
  have hchord := equal_norm_chord_product hnormrt
  have hdx : |(S r).re - (S t).re| = H := abs_of_pos hH
  rw [hdx] at hchord
  have hlower : H * (2 * c0) ≤
      H * |(S r).re + (S t).re| :=
    mul_le_mul_of_nonneg_left hxsumLower hH.le
  have hupper : |(S r).im - (S t).im| * |(S r).im + (S t).im| ≤
      (δ * H) * (2 * B) := by
    have hd : |(S r).im - (S t).im| ≤ δ * H := by
      simpa [abs_sub_comm] using himfinal
    exact mul_le_mul hd hysumUpper (abs_nonneg _) (by positivity)
  have hmain : H * (2 * c0) ≤ (δ * H) * (2 * B) := by
    calc
      H * (2 * c0) ≤ H * |(S r).re + (S t).re| := hlower
      _ = |(S r).im - (S t).im| * |(S r).im + (S t).im| := hchord
      _ ≤ (δ * H) * (2 * B) := hupper
  have hδsmall : δ * (4 * B) ≤ c0 := by
    calc
      δ * (4 * B) ≤ (c0 / (4 * B)) * (4 * B) :=
        mul_le_mul_of_nonneg_right hδc0 (by positivity)
      _ = c0 := by field_simp [ne_of_gt hB]
  nlinarith

lemma exists_unit_conjugate_expansion_with_infinite_radii {q : ℝ} {p : ℂ}
    (hq1 : 1 < q) (hq2 : q < 2) (hqint : IsIntegral ℤ q)
    (hpRoot : ((minpoly ℤ q).map (algebraMap ℤ ℂ)).eval p = 0)
    (hpNorm : ‖p‖ = 1) (hpNe : p ≠ 1)
    (hpPow : ∀ m : ℕ, 0 < m → p ^ m ≠ 1) :
    ∃ s : ℕ → ℤ, (∀ i, |s i| ≤ 1) ∧ SignedExpansion q s ∧
      (Set.range fun n ↦ ‖∑ i ∈ Finset.range (n + 1),
        (s i : ℂ) * p⁻¹ ^ i‖).Infinite := by
  classical
  let w : ℂ := 1 - p
  let a : ℕ → ℝ := fun n ↦ (w * p⁻¹ ^ (n + 1)).re
  have hsep := unit_separator_prefix hpNorm hpNe
  change 0 < w.re ∧ ∀ k : ℕ, ∑ i ∈ Finset.range k, a i < w.re at hsep
  obtain ⟨hwre, hprefix⟩ := hsep
  obtain ⟨K, s, hs, hs0, hsExp, hsP, hsPc, hcoeffOne⟩ :=
    exists_lazy_expansion_for_separator hq1 hq2 a
  have hw : w ≠ 0 := by
    intro h
    change 1 - p = 0 at h
    have hp1 : (1 : ℂ) = p := sub_eq_zero.mp h
    exact hpNe hp1.symm
  have htermRe (i : ℕ) :
      ((s i : ℂ) * (w * p⁻¹ ^ i)).re =
        (s i : ℝ) * (w * p⁻¹ ^ i).re := by
    norm_cast
    simp
  have hstep : ∀ i, K < i → ((s i : ℂ) * (w * p⁻¹ ^ i)).re ≤ 0 := by
    intro i hi
    have hi0 : 0 < i := lt_of_le_of_lt (Nat.zero_le K) hi
    let n := i - 1
    have hnK : K ≤ n := by dsimp [n]; omega
    have hin : n + 1 = i := by dsimp [n]; omega
    have haCases : a n ≤ 0 ∨ 0 < a n := le_or_gt (a n) 0
    rw [← hin, htermRe]
    change (s (n + 1) : ℝ) * a n ≤ 0
    rcases haCases with han | hap
    · exact mul_nonpos_of_nonneg_of_nonpos
        (by exact_mod_cast hsP n (Or.inr han)) han
    · have hsnonpos : s (n + 1) ≤ 0 := hsPc n (by
        simp only [not_or, not_lt]
        exact ⟨hnK, not_le.mpr hap⟩)
      exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hsnonpos) hap.le
  have hstrict : ∀ i, K < i → s i ≠ 0 →
      ((s i : ℂ) * (w * p⁻¹ ^ i)).re < 0 := by
    intro i hi hsi
    have hi0 : 0 < i := lt_of_le_of_lt (Nat.zero_le K) hi
    let n := i - 1
    have hnK : K ≤ n := by dsimp [n]; omega
    have hin : n + 1 = i := by dsimp [n]; omega
    have hane : a n ≠ 0 := by
      dsimp [a, w, n]
      simpa [hin] using unit_separator_term_ne_zero hpNorm hpNe hpPow (i - 1)
    rcases lt_or_gt_of_ne hane with han | hap
    · have hsnonneg : 0 ≤ s (n + 1) := hsP n (Or.inr han.le)
      have hspos : 0 < s (n + 1) := lt_of_le_of_ne hsnonneg (by simpa [hin] using hsi.symm)
      rw [← hin, htermRe]
      change (s (n + 1) : ℝ) * a n < 0
      exact mul_neg_of_pos_of_neg (by exact_mod_cast hspos) han
    · have hsnonpos : s (n + 1) ≤ 0 := hsPc n (by
        simp only [not_or, not_lt]
        exact ⟨hnK, not_le.mpr hap⟩)
      have hsneg : s (n + 1) < 0 := lt_of_le_of_ne hsnonpos (by simpa [hin] using hsi)
      rw [← hin, htermRe]
      change (s (n + 1) : ℝ) * a n < 0
      exact mul_neg_of_neg_of_pos (by exact_mod_cast hsneg) hap
  have hstart : (unitWeightedPartialSum p w s K).re < 0 := by
    have hcomplex : unitWeightedPartialSum p w s K =
        -w + ∑ n ∈ Finset.range K, (s (n + 1) : ℂ) * (w * p⁻¹ ^ (n + 1)) := by
      rw [unitWeightedPartialSum, Finset.sum_range_succ']
      simp [hs0, add_comm]
    have htailRe :
        (∑ n ∈ Finset.range K, (s (n + 1) : ℂ) * (w * p⁻¹ ^ (n + 1))).re =
          ∑ n ∈ Finset.range K, (s (n + 1) : ℝ) * a n := by
      have hmap := map_sum (Complex.reCLM : ℂ →L[ℝ] ℝ)
        (fun n ↦ (s (n + 1) : ℂ) * (w * p⁻¹ ^ (n + 1))) (Finset.range K)
      have hmap' :
          (∑ n ∈ Finset.range K,
            (s (n + 1) : ℂ) * (w * p⁻¹ ^ (n + 1))).re =
            ∑ n ∈ Finset.range K,
              ((s (n + 1) : ℂ) * (w * p⁻¹ ^ (n + 1))).re := by
        simpa only [Complex.reCLM_apply] using hmap
      rw [hmap']
      apply Finset.sum_congr rfl
      intro n hn
      rw [htermRe]
    have hsumRe : (unitWeightedPartialSum p w s K).re =
        -w.re + ∑ n ∈ Finset.range K, (s (n + 1) : ℝ) * a n := by
      rw [hcomplex]
      simp only [Complex.add_re, Complex.neg_re, htailRe]
    have htermle : ∀ n ∈ Finset.range K,
        (s (n + 1) : ℝ) * a n ≤ a n := by
      intro n hn
      have hnK : n < K := Finset.mem_range.mp hn
      by_cases han : 0 ≤ a n
      · have hsle : (s (n + 1) : ℝ) ≤ 1 := by
          exact_mod_cast (le_trans (le_abs_self _) (hs (n + 1)))
        nlinarith
      · have haneg : a n < 0 := lt_of_not_ge han
        rw [hcoeffOne n hnK haneg]
        norm_num
    have hsumle : (∑ n ∈ Finset.range K, (s (n + 1) : ℝ) * a n) ≤
        ∑ n ∈ Finset.range K, a n := Finset.sum_le_sum htermle
    rw [hsumRe]
    linarith [hprefix K]
  have hsupp : {i | s i ≠ 0}.Infinite := by
    by_contra hsuppInf
    have hsuppFin : {i | s i ≠ 0}.Finite := not_not.mp hsuppInf
    let F : Finset ℕ := hsuppFin.toFinset
    let N : ℕ := max K (F.sup id)
    have hKN : K ≤ N := le_max_left _ _
    have hzeroAfter : ∀ i, N < i → s i = 0 := by
      intro i hi
      by_contra hsi
      have hiF : i ∈ F := by simp [F, hsi]
      have hisup : i ≤ F.sup id := Finset.le_sup (f := id) hiF
      dsimp [N] at hi
      omega
    have hpartialQ :
        ∑ i ∈ Finset.range (N + 1), (s i : ℝ) * q⁻¹ ^ i = 0 := by
      calc
        ∑ i ∈ Finset.range (N + 1), (s i : ℝ) * q⁻¹ ^ i =
            ∑' i, (s i : ℝ) * q⁻¹ ^ i := by
          symm
          apply tsum_eq_sum
          intro i hi
          have hiN : N < i := by simpa using hi
          simp [hzeroAfter i hiN]
        _ = 0 := hsExp.tsum_eq
    have hrevQ : (reversedPolynomial s N).eval₂ (algebraMap ℤ ℝ) q = 0 := by
      have hformulaQR : q⁻¹ ^ N *
          (reversedPolynomial s N).eval₂ (algebraMap ℤ ℝ) q =
          ∑ i ∈ Finset.range (N + 1), (s i : ℝ) * q⁻¹ ^ i := by
        rw [eval₂_reversedPolynomial, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hiN : i ≤ N := by simpa using hi
        rw [pow_sub₀ q (by linarith) hiN]
        simp only [inv_pow]
        have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq1)
        calc
          (q ^ N)⁻¹ * ((s i : ℝ) * (q ^ N * (q ^ i)⁻¹)) =
              ((q ^ N)⁻¹ * q ^ N) * ((s i : ℝ) * (q ^ i)⁻¹) := by ring
          _ = (s i : ℝ) * (q ^ i)⁻¹ := by simp [pow_ne_zero N hq0]
      rw [hpartialQ] at hformulaQR
      exact (mul_eq_zero.mp hformulaQR).resolve_left (pow_ne_zero _ (inv_ne_zero (by linarith)))
    have hrevP : (reversedPolynomial s N).eval₂ (algebraMap ℤ ℂ) p = 0 := by
      have := eval₂_eq_at_conjugate_of_eval₂_eq hqint hpRoot
        (P := reversedPolynomial s N) (Q := 0) (by simpa using hrevQ)
      simpa using this
    have hp0 : p ≠ 0 := by
      intro hp0
      simp [hp0] at hpNorm
    have hformulaP := inv_pow_mul_eval₂_reversedPolynomial hp0 s N
    have hpartialP : ∑ i ∈ Finset.range (N + 1), (s i : ℂ) * p⁻¹ ^ i = 0 := by
      rw [hrevP, mul_zero] at hformulaP
      exact hformulaP.symm
    have hSNzero : unitWeightedPartialSum p w s N = 0 := by
      rw [unitWeightedPartialSum]
      calc
        ∑ i ∈ Finset.range (N + 1), (s i : ℂ) * (w * p⁻¹ ^ i) =
            w * ∑ i ∈ Finset.range (N + 1), (s i : ℂ) * p⁻¹ ^ i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = 0 := by rw [hpartialP, mul_zero]
    have hmono : (unitWeightedPartialSum p w s N).re ≤
        (unitWeightedPartialSum p w s K).re := by
      have hxanti : Antitone (fun n ↦
          (unitWeightedPartialSum p w s (K + n)).re) :=
        antitone_nat_of_succ_le (fun n ↦ by
          rw [show K + (n + 1) = (K + n) + 1 by omega,
            unitWeightedPartialSum_succ]
          simp only [Complex.add_re]
          exact add_le_of_nonpos_right (hstep (K + n + 1) (by omega)))
      have hm := hxanti (Nat.zero_le (N - K))
      simpa [Nat.add_sub_of_le hKN] using hm
    rw [hSNzero] at hmono
    simp only [Complex.zero_re] at hmono
    linarith
  have hweighted := unitWeightedPartialSum_norm_range_infinite hpNorm hw hs hsupp
    hstep hstrict hstart
  refine ⟨s, hs, hsExp, ?_⟩
  intro hfinitePartial
  apply hweighted
  let T : ℕ → ℂ := fun n ↦ ∑ i ∈ Finset.range (n + 1), (s i : ℂ) * p⁻¹ ^ i
  have hnormEq (n : ℕ) : ‖unitWeightedPartialSum p w s n‖ = ‖w‖ * ‖T n‖ := by
    have hsum : unitWeightedPartialSum p w s n = w * T n := by
      dsimp only [unitWeightedPartialSum, T]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum, norm_mul]
  exact hfinitePartial.image (fun x ↦ ‖w‖ * x) |>.subset (by
    rintro _ ⟨n, rfl⟩
    exact ⟨‖T n‖, ⟨n, rfl⟩, (hnormEq n).symm⟩)

lemma conjugate_not_root_of_unity {q : ℝ} {p : ℂ} (hqint : IsIntegral ℤ q)
    (hq1 : 1 < q)
    (hpRoot : ((minpoly ℤ q).map (algebraMap ℤ ℂ)).eval p = 0) :
    ∀ m : ℕ, 0 < m → p ^ m ≠ 1 := by
  have hqCint : IsIntegral ℤ (q : ℂ) :=
    hqint.map (IsScalarTower.toAlgHom ℤ ℝ ℂ)
  have hminZ : minpoly ℤ (q : ℂ) = minpoly ℤ q := by
    exact minpoly.algebraMap_eq Complex.ofRealHom.injective q
  have hminQ : minpoly ℚ (q : ℂ) =
      (minpoly ℤ q).map (algebraMap ℤ ℚ) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hqCint, hminZ]
  have hpRat : Polynomial.aeval p (minpoly ℚ (q : ℂ)) = 0 := by
    rw [hminQ, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_map]
    rw [← IsScalarTower.algebraMap_eq ℤ ℚ ℂ]
    exact hpRoot
  have hqCintQ : IsIntegral ℚ (q : ℂ) := hqCint.tower_top
  have hconj : IsConjRoot ℚ (q : ℂ) p :=
    isConjRoot_of_aeval_eq_zero hqCintQ hpRat
  intro m hm hpm
  let G : ℚ[X] := X ^ m - 1
  have hpG : Polynomial.aeval p G = 0 := by
    simp [G, hpm]
  have hdvdP : minpoly ℚ p ∣ G := minpoly.dvd ℚ p hpG
  have hdvdQ : minpoly ℚ (q : ℂ) ∣ G := by
    rw [hconj]
    exact hdvdP
  have hqG : Polynomial.aeval (q : ℂ) G = 0 :=
    Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdvdQ (minpoly.aeval ℚ (q : ℂ))
  have hqpowC : (q : ℂ) ^ m = 1 := sub_eq_zero.mp (by simpa [G] using hqG)
  have hqpowR : q ^ m = 1 := by exact_mod_cast hqpowC
  have : 1 < q ^ m := one_lt_pow₀ hq1 hm.ne'
  linarith

lemma conjugate_not_unit_of_no_accumulation {q : ℝ} {p : ℂ}
    (hq1 : 1 < q) (hq2 : q < 2)
    (hno : ¬ HasAccumulation (SignedSpectrum q))
    (hpRoot : ((minpoly ℤ q).map (algebraMap ℤ ℂ)).eval p = 0)
    (hpNorm : ‖p‖ = 1) : False := by
  have hqint := integral_of_no_signedSpectrum_accumulation hq1 hq2 hno
  have hpPow := conjugate_not_root_of_unity hqint hq1 hpRoot
  have hpNe : p ≠ 1 := by
    intro hp1
    apply hpPow 1 (by omega)
    simp [hp1]
  obtain ⟨s, hs, hsExp, hinfinite⟩ :=
    exists_unit_conjugate_expansion_with_infinite_radii hq1 hq2 hqint hpRoot
      hpNorm hpNe hpPow
  let f : ℕ → ℂ := fun n ↦
    (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) p
  let T : ℕ → ℂ := fun n ↦
    ∑ i ∈ Finset.range (n + 1), (s i : ℂ) * p⁻¹ ^ i
  have hfiniteF : (Set.range f).Finite :=
    finite_reversed_tail_range_at_conjugate hqint hno hpRoot hs
      (fun n ↦ reversed_tail_bound_of_signedExpansion hq1 hs hsExp n)
  have hp0 : p ≠ 0 := by
    intro hp0
    simp [hp0] at hpNorm
  have hnormEq (n : ℕ) : ‖T n‖ = ‖f n‖ := by
    have hformula := inv_pow_mul_eval₂_reversedPolynomial hp0 s n
    change p⁻¹ ^ n * f n = T n at hformula
    calc
      ‖T n‖ = ‖p⁻¹ ^ n * f n‖ := congrArg norm hformula.symm
      _ = ‖p⁻¹ ^ n‖ * ‖f n‖ := norm_mul _ _
      _ = ‖f n‖ := by rw [norm_pow, norm_inv, hpNorm]; simp
  apply hinfinite
  apply (hfiniteF.image norm).subset
  rintro _ ⟨n, rfl⟩
  exact ⟨f n, ⟨n, rfl⟩, (hnormEq n).symm⟩

/-- The corrected Erdős--Komornik conjugate argument: if the signed binary
spectrum has no finite accumulation point, then the base is Pisot. -/
lemma isPisot_of_no_signedSpectrum_accumulation {q : ℝ}
    (hq1 : 1 < q) (hq2 : q < 2)
    (hno : ¬ HasAccumulation (SignedSpectrum q)) :
    IsPisot1096 q := by
  have hqint : IsIntegral ℤ q :=
    integral_of_no_signedSpectrum_accumulation hq1 hq2 hno
  refine ⟨hq1, hqint, ?_⟩
  intro z hz hzq
  by_contra hnotlt
  have hge : 1 ≤ ‖z‖ := le_of_not_gt hnotlt
  rcases hge.eq_or_lt with hunit | hlarge
  · exact conjugate_not_unit_of_no_accumulation hq1 hq2 hno hz hunit.symm
  · by_cases him : z.im = 0
    · by_cases hre : 1 < z.re
      · apply conjugate_not_positive_real_of_no_accumulation hq1 hq2 hno hre
          (by
            intro heq
            apply hzq
            apply Complex.ext
            · simpa using heq
            · simpa using him)
        have hzReal : (z.re : ℂ) = z := by
          apply Complex.ext <;> simp [him]
        rw [hzReal]
        exact hz
      · have hzReal : (z.re : ℂ) = z := by
          apply Complex.ext <;> simp [him]
        have hreal : ‖z‖ = |z.re| := by
          calc
            ‖z‖ = ‖(z.re : ℂ)‖ := congrArg norm hzReal.symm
            _ = |z.re| := by simp [Real.norm_eq_abs]
        have hzre : z.re < 1 := by
          rw [hreal] at hlarge
          rcases abs_cases z.re with habs | habs <;> rw [habs.1] at hlarge
          · linarith
          · linarith
        obtain ⟨s, hs, hsExp, hnotSum⟩ :=
          exists_signed_expansion_separating_at_large_conjugate hq1 hq2 hlarge
            (Or.inl hzre)
        have hfinite : (Set.range fun n ↦
            (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z).Finite :=
          finite_reversed_tail_range_at_conjugate hqint hno hz hs
            (fun n ↦ reversed_tail_bound_of_signedExpansion hq1 hs hsExp n)
        exact hnotSum (hasSum_zero_of_finite_reversed_tail_range hlarge hs hfinite)
    · obtain ⟨s, hs, hsExp, hnotSum⟩ :=
        exists_signed_expansion_separating_at_large_conjugate hq1 hq2 hlarge
          (Or.inr him)
      have hfinite : (Set.range fun n ↦
          (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z).Finite :=
        finite_reversed_tail_range_at_conjugate hqint hno hz hs
          (fun n ↦ reversed_tail_bound_of_signedExpansion hq1 hs hsExp n)
      exact hnotSum (hasSum_zero_of_finite_reversed_tail_range hlarge hs hfinite)

/-- A concrete interval sufficient for the signed-spectrum accumulation
theorem.  The number-theoretic input is the formalized weak Smyth bound. -/
lemma signedSpectrum_hasAccumulation_below_eleven_tenths {q : ℝ}
    (hq1 : 1 < q) (hqsmall : q < 11 / 10) :
    HasAccumulation (SignedSpectrum q) := by
  by_contra hno
  exact no_pisot_below_eleven_tenths hqsmall
    (isPisot_of_no_signedSpectrum_accumulation hq1 (by linarith) hno)

end
end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos1096/Erdos1096Accumulation.lean` -/

section
open Filter Set Polynomial
open scoped BigOperators Pointwise Topology ComplexConjugate

noncomputable section



lemma signedSpectrum_mem_as_spectrum_difference {q y : ℝ}
    (hy : y ∈ SignedSpectrum q) :
    ∃ a ∈ Spectrum q, ∃ b ∈ Spectrum q, y = a - b := by
  rcases hy with ⟨p, hp, rfl⟩
  let A : Finset ℕ := p.support.filter fun i ↦ p.coeff i = 1
  let B : Finset ℕ := p.support.filter fun i ↦ p.coeff i = -1
  have hcases (i : ℕ) : p.coeff i = -1 ∨ p.coeff i = 0 ∨ p.coeff i = 1 := by
    have hi := abs_le.mp (hp i)
    omega
  have hpoly : p = (∑ i ∈ A, X ^ i) - ∑ i ∈ B, X ^ i := by
    ext i
    rcases hcases i with hi | hi | hi
    · simp [A, B, Polynomial.coeff_X_pow, hi]
    · have hisupp : i ∉ p.support := by simp [Polynomial.mem_support_iff, hi]
      simp [A, B, Polynomial.coeff_X_pow, hi, hisupp]
    · simp [A, B, Polynomial.coeff_X_pow, hi]
  refine ⟨∑ i ∈ A, q ^ i, ⟨A, rfl⟩,
    ∑ i ∈ B, q ^ i, ⟨B, rfl⟩, ?_⟩
  rw [hpoly, Polynomial.eval₂_sub, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_finsetSum]
  simp

private def residueZeroSupport3 (S : Finset ℕ) : Finset ℕ :=
  S.image (fun i ↦ 3 * i)

private def residueOneSupport3 (S : Finset ℕ) : Finset ℕ :=
  S.image (fun i ↦ 3 * i + 1)

private lemma residueZeroSupport3_disjoint_residueOneSupport3 (S T : Finset ℕ) :
    Disjoint (residueZeroSupport3 S) (residueOneSupport3 T) := by
  rw [Finset.disjoint_left]
  intro k hkS hkT
  rcases Finset.mem_image.mp hkS with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hkT with ⟨j, hj, h⟩
  omega

private lemma sum_residueZeroSupport3 (q : ℝ) (S : Finset ℕ) :
    (∑ k ∈ residueZeroSupport3 S, q ^ k) = ∑ i ∈ S, (q ^ 3) ^ i := by
  rw [residueZeroSupport3, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [pow_mul]
  · intro i hi j hj hij
    change 3 * i = 3 * j at hij
    omega

private lemma sum_residueOneSupport3 (q : ℝ) (S : Finset ℕ) :
    (∑ k ∈ residueOneSupport3 S, q ^ k) = q * ∑ i ∈ S, (q ^ 3) ^ i := by
  rw [residueOneSupport3, Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ, pow_mul]
    ring
  · intro i hi j hj hij
    change 3 * i + 1 = 3 * j + 1 at hij
    omega

lemma add_scaleSet_cube_subset_spectrum (q : ℝ) :
    ∀ u ∈ Spectrum (q ^ 3), ∀ v ∈ scaleSet q (Spectrum (q ^ 3)),
      u + v ∈ Spectrum q := by
  intro u hu v hv
  rcases hu with ⟨S, rfl⟩
  rcases hv with ⟨a, ⟨T, rfl⟩, rfl⟩
  refine ⟨residueZeroSupport3 S ∪ residueOneSupport3 T, ?_⟩
  rw [Finset.sum_union (residueZeroSupport3_disjoint_residueOneSupport3 S T)]
  rw [sum_residueZeroSupport3, sum_residueOneSupport3]

private lemma abs_sub_lt_of_floor_eq {x y L ε : ℝ} (hε : 0 < ε)
    (hx : 0 ≤ x - L) (hy : 0 ≤ y - L)
    (hfloor : ⌊(x - L) / ε⌋₊ = ⌊(y - L) / ε⌋₊) :
    |x - y| < ε := by
  let k : ℕ := ⌊(x - L) / ε⌋₊
  have hxlo : (k : ℝ) ≤ (x - L) / ε := by
    exact Nat.floor_le (div_nonneg hx hε.le)
  have hxhi : (x - L) / ε < (k : ℝ) + 1 := by
    exact Nat.lt_floor_add_one ((x - L) / ε)
  have hylo : (k : ℝ) ≤ (y - L) / ε := by
    rw [show k = ⌊(y - L) / ε⌋₊ by exact hfloor]
    exact Nat.floor_le (div_nonneg hy hε.le)
  have hyhi : (y - L) / ε < (k : ℝ) + 1 := by
    rw [show k = ⌊(y - L) / ε⌋₊ by exact hfloor]
    exact Nat.lt_floor_add_one ((y - L) / ε)
  rw [abs_lt]
  constructor
  · have haux : (y - L) / ε - (x - L) / ε < 1 := by linarith
    have hdiv : (y - x) / ε < 1 := by
      convert haux using 1 <;> ring
    have := (div_lt_iff₀ hε).mp hdiv
    linarith
  · have haux : (x - L) / ε - (y - L) / ε < 1 := by linarith
    have hdiv : (x - y) / ε < 1 := by
      convert haux using 1 <;> ring
    simpa using (div_lt_iff₀ hε).mp hdiv

/-- Akiyama--Komornik's finite sumset pigeonhole lemma in the special form
needed here.  An accumulation point of the signed spectrum in base `q³`
produces arbitrarily close distinct binary spectrum values in base `q`. -/
lemma smallSpectrumDifferences_of_cube_accumulation {q : ℝ}
    (hq1 : 1 < q) (hqcube2 : q ^ 3 ≤ 2)
    (hacc : HasAccumulation (SignedSpectrum (q ^ 3))) :
    SmallSpectrumDifferences q := by
  classical
  intro ε hε
  rcases hacc with ⟨c, hc⟩
  have hlocalAcc : AccPt c
      (Filter.principal (Metric.ball c 1 ∩ SignedSpectrum (q ^ 3))) :=
    hc.nhds_inter (Metric.ball_mem_nhds c zero_lt_one)
  have hlocalInf : (Metric.ball c 1 ∩ SignedSpectrum (q ^ 3)).Infinite :=
    Set.Infinite.of_accPt hlocalAcc
  have hq0 : 0 < q := by linarith
  have hcube1 : 1 < q ^ 3 := one_lt_pow₀ hq1 (by omega)
  obtain ⟨C, hC⟩ :=
    scaleSet_spectrum_eventuallyLeftDense hq0 hcube1 hqcube2
  let R : ℝ := q + |c| + 2
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 2 * R / ε < K := exists_nat_gt (2 * R / ε)
  have hKpos : 0 < K := by
    have hquot : 0 < 2 * R / ε := by positivity
    exact_mod_cast (lt_trans hquot hK)
  obtain ⟨Dset, hDsub, hDcard⟩ :=
    hlocalInf.exists_subset_card_eq (K * K + 1)
  let D := {d : ℝ // d ∈ Dset}
  have hrep (d : D) :
      ∃ ab : ℝ × ℝ, ab.1 ∈ Spectrum (q ^ 3) ∧
        ab.2 ∈ Spectrum (q ^ 3) ∧ (d : ℝ) = ab.1 - ab.2 := by
    obtain ⟨a, ha, b, hb, hd⟩ :=
      signedSpectrum_mem_as_spectrum_difference
        (show (d : ℝ) ∈ SignedSpectrum (q ^ 3) from (hDsub d.property).2)
    exact ⟨(a, b), ha, hb, hd⟩
  let rep : D → ℝ × ℝ := fun d ↦ Classical.choose (hrep d)
  have hrepSpec (d : D) :
      (rep d).1 ∈ Spectrum (q ^ 3) ∧
        (rep d).2 ∈ Spectrum (q ^ 3) ∧ (d : ℝ) = (rep d).1 - (rep d).2 :=
    Classical.choose_spec (hrep d)
  let a : D → ℝ := fun d ↦ (rep d).1
  let b : D → ℝ := fun d ↦ (rep d).2
  have ha (d : D) : a d ∈ Spectrum (q ^ 3) := (hrepSpec d).1
  have hb (d : D) : b d ∈ Spectrum (q ^ 3) := (hrepSpec d).2.1
  have hdab (d : D) : (d : ℝ) = a d - b d := (hrepSpec d).2.2
  let T : ℝ := C + ∑ d : D, |b d| + 1
  have htarget (d : D) : C ≤ T - b d := by
    have hbabs : b d ≤ |b d| := le_abs_self (b d)
    have habssum : |b d| ≤ ∑ e : D, |b e| := by
      exact Finset.single_le_sum (fun e _ ↦ abs_nonneg (b e)) (Finset.mem_univ d)
    dsimp [T]
    linarith
  have hvExists (d : D) : ∃ v ∈ scaleSet q (Spectrum (q ^ 3)),
      (T - b d) - q < v ∧ v ≤ T - b d :=
    hC (T - b d) (htarget d)
  let v : D → ℝ := fun d ↦ Classical.choose (hvExists d)
  have hvSpec (d : D) : v d ∈ scaleSet q (Spectrum (q ^ 3)) ∧
      (T - b d) - q < v d ∧ v d ≤ T - b d :=
    Classical.choose_spec (hvExists d)
  let A : D → ℝ := fun d ↦ a d + v d
  let B : D → ℝ := fun d ↦ b d + v d
  have hAZ (d : D) : A d ∈ Spectrum q :=
    add_scaleSet_cube_subset_spectrum q (a d) (ha d) (v d) (hvSpec d).1
  have hBZ (d : D) : B d ∈ Spectrum q :=
    add_scaleSet_cube_subset_spectrum q (b d) (hb d) (v d) (hvSpec d).1
  have hAdiffB (d : D) : A d - B d = (d : ℝ) := by
    dsimp [A, B]
    linarith [hdab d]
  have hdBound (d : D) : |(d : ℝ)| < |c| + 1 := by
    have hball : dist (d : ℝ) c < 1 := Metric.mem_ball.mp (hDsub d.property).1
    rw [Real.dist_eq] at hball
    calc
      |(d : ℝ)| = |((d : ℝ) - c) + c| := by ring_nf
      _ ≤ |(d : ℝ) - c| + |c| := abs_add_le _ _
      _ < |c| + 1 := by linarith
  have hBbounds (d : D) : T - R ≤ B d ∧ B d ≤ T + R := by
    have hlo := (hvSpec d).2.1
    have hhi := (hvSpec d).2.2
    dsimp [B, R]
    constructor <;> linarith [abs_nonneg c]
  have hAbounds (d : D) : T - R ≤ A d ∧ A d ≤ T + R := by
    have hBlo : T - q < B d := by
      have hlo := (hvSpec d).2.1
      dsimp [B]
      linarith
    have hBhi : B d ≤ T := by
      have hhi := (hvSpec d).2.2
      dsimp [B]
      linarith
    have hd := hdBound d
    rw [abs_lt] at hd
    have hrel := hAdiffB d
    dsimp [R]
    constructor <;> linarith
  let bin : ℝ → ℕ := fun x ↦ ⌊(x - (T - R)) / ε⌋₊
  have hbinRange {x : ℝ} (hx : T - R ≤ x ∧ x ≤ T + R) : bin x < K := by
    have hx0 : 0 ≤ x - (T - R) := by linarith
    apply (Nat.floor_lt (div_nonneg hx0 hε.le)).mpr
    calc
      (x - (T - R)) / ε ≤ (2 * R) / ε := by
        apply div_le_div_of_nonneg_right _ hε.le
        linarith
      _ < K := hK
  let code : D → Fin K × Fin K := fun d ↦
    (⟨bin (A d), hbinRange (hAbounds d)⟩,
      ⟨bin (B d), hbinRange (hBbounds d)⟩)
  have hcard : Fintype.card (Fin K × Fin K) < Fintype.card D := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    rw [show Fintype.card D = Dset.card by simp [D], hDcard]
    omega
  obtain ⟨d, e, hde, hcode⟩ := Fintype.exists_ne_map_eq_of_card_lt code hcard
  have hfloorA : bin (A d) = bin (A e) :=
    congrArg (fun z : Fin K × Fin K ↦ z.1.1) hcode
  have hfloorB : bin (B d) = bin (B e) :=
    congrArg (fun z : Fin K × Fin K ↦ z.2.1) hcode
  have hcloseA : |A d - A e| < ε :=
    abs_sub_lt_of_floor_eq hε (by linarith [hAbounds d])
      (by linarith [hAbounds e]) hfloorA
  have hcloseB : |B d - B e| < ε :=
    abs_sub_lt_of_floor_eq hε (by linarith [hBbounds d])
      (by linarith [hBbounds e]) hfloorB
  have hdistinct : A d ≠ A e ∨ B d ≠ B e := by
    by_contra hnot
    push_neg at hnot
    apply hde
    apply Subtype.ext
    have hdrel := hAdiffB d
    have herel := hAdiffB e
    linarith
  rcases hdistinct with hAne | hBne
  · rcases hAZ d with ⟨Sd, hSd⟩
    rcases hAZ e with ⟨Se, hSe⟩
    refine ⟨Se, Sd, ?_, ?_⟩
    · simpa [hSd, hSe] using abs_pos.mpr (sub_ne_zero.mpr hAne)
    · simpa [hSd, hSe] using hcloseA
  · rcases hBZ d with ⟨Sd, hSd⟩
    rcases hBZ e with ⟨Se, hSe⟩
    refine ⟨Se, Sd, ?_, ?_⟩
    · simpa [hSd, hSe] using abs_pos.mpr (sub_ne_zero.mpr hBne)
    · simpa [hSd, hSe] using hcloseB

/-- A rational interval on which the spectral small-difference input needed
by the even/odd bridge is now unconditional. -/
lemma smallSpectrumDifferences_below_one_hundred_one_hundredths {q : ℝ}
    (hq1 : 1 < q) (hqsmall : q < 101 / 100) :
    SmallSpectrumDifferences q := by
  have hq0 : 0 ≤ q := by linarith
  have hpow : q ^ 3 < (101 / 100 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hqsmall hq0 (by omega)
  have hcubeSmall : q ^ 3 < 11 / 10 := by
    calc
      q ^ 3 < (101 / 100 : ℝ) ^ 3 := hpow
      _ < 11 / 10 := by norm_num
  have hcubeTwo : q ^ 3 ≤ 2 := hcubeSmall.le.trans (by norm_num)
  exact smallSpectrumDifferences_of_cube_accumulation hq1 hcubeTwo
    (signedSpectrum_hasAccumulation_below_eleven_tenths
      (one_lt_pow₀ hq1 (by omega)) hcubeSmall)

end
end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos1096.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1096.
https://www.erdosproblems.com/forum/thread/1096

Informal authors:
- Paul Erdős
- Vilmos Komornik

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1096.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1096.lean
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Erdős Problem 1096

For every base sufficiently close to one, the successive gaps in the ordered
binary spectrum tend to zero.  The detailed mathematical proof and the
Leanization map are in `tex/1096.tex`.
-/

open Filter Set
open scoped BigOperators Pointwise Topology



noncomputable section

theorem erdos_1096 :
    ∃ ε > 0, ∀ q, 1 < q → q < 1 + ε →
    ∀ x : ℕ → ℝ, StrictMono x → Set.range x = { ∑ i ∈ S, q ^ i | S : Finset ℕ } →
    Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0) := by
  refine Iff.mp ?_ trivial
  constructor
  · intro htrue
    refine ⟨1 / 1000, by norm_num, fun q hq hqε x hx hrange ↦ ?_⟩
    have hqbound : q < 1001 / 1000 := by
      norm_num at hqε ⊢
      exact hqε
    have hsq1 : 1 < q ^ 2 := one_lt_pow₀ hq (by omega)
    have hsqbound : q ^ 2 < 101 / 100 := by
      calc
        q ^ 2 < (1001 / 1000 : ℝ) ^ 2 :=
          pow_lt_pow_left₀ hqbound (by linarith) (by omega)
        _ < 101 / 100 := by norm_num
    have hsq2 : q ^ 2 < 2 := hsqbound.trans (by norm_num)
    have hsmall : SmallDisjointDifferences (q ^ 2) :=
      smallDisjointDifferences_of_smallSpectrumDifferences
        (smallSpectrumDifferences_below_one_hundred_one_hundredths hsq1 hsqbound)
    have hdense : EventuallyRightDense (Spectrum q) :=
      spectrum_eventuallyRightDense_of_square_smallDifferences hq hsq2 hsmall
    have hrange' : Set.range x = Spectrum q := by
      rw [hrange]
      ext a
      simp only [Spectrum, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨S, rfl⟩
        exact ⟨S, rfl⟩
      · rintro ⟨S, rfl⟩
        exact ⟨S, rfl⟩
    exact gaps_tendsto_zero_of_eventuallyRightDense hx hrange'
      (strictMono_spectrum_tendsto_atTop hq hx hrange') hdense
  · intro h
    trivial


end

end

#print axioms erdos_1096
-- 'Erdos1096.erdos_1096' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1096
