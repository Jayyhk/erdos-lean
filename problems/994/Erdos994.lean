import Mathlib

namespace Erdos994

/-
# Erdős Problem 994

Let $E \subseteq (0,1)$ be a measurable subset with Lebesgue measure $\lambda(E)$. Is it true
that, for almost all $\alpha$,
$$\lim_{n \to \infty} \frac{1}{n} \sum_{1 \leq k \leq n} 1_{\{k\alpha\} \in E} = \lambda(E)$$
for all $E$?

The answer is **no**: this is a conjecture of Khintchine [Kh23], disproved by Marstrand [Ma70].
`erdos_994` refutes the historical reading, in which $E$ is fixed first and the exceptional null set
of $\alpha$ may depend on $E$. The reading with the quantifiers swapped (almost every $\alpha$ works
for all $E$ at once) is a stronger conjecture, so refuting it is easy. The stronger
`exists_counterexample_ae` gives a single Borel set $E \subseteq (0,1)$ with $\lambda(E) \leq 1/8$
whose visit averages have $\limsup \geq 1/2$ for almost every $\alpha$. The proof reconstructs
Marstrand's theorem via the transference argument of Quas--Wierdl, proving along the way the Rokhlin
lemma for commuting endomorphisms of Avila--Candela.

Formalised by Collin Yuanjie Ren in `CollinYuanjieRen/awards` (submission JSP-000827); the
eleven modules forming the closure of `erdos_994` are flattened here in dependency order, with
the final theorem renamed from upstream `not_khintchineFixedSet`. The definitions
`visitAverage`, `HasExpectedLimit` and `KhintchineFixedSet` are those of
`plby/lean-proofs` (`ErdosProblems/Erdos994.lean`).

Declarations that `erdos_994` does not depend on have been removed.
-/

/-! ### Upstream module `Jsp827/Statement.lean` -/

section
/-!
# Erdős Problem 994 (JSP-000827): frozen target statement

Source (erdosproblems.com/994, hashed in `ref/erdos994-statement.txt`; Khintchine 1923;
disproved by Marstrand, Proc. LMS 21 (1970) 540–556): "Let `E ⊆ (0,1)` be a measurable
subset with Lebesgue measure `λ(E)`. Is it true that, for almost all `α`,
`lim_{n→∞} (1/n) ∑_{1 ≤ k ≤ n} 1_{{kα} ∈ E} = λ(E)`?"  The historical (fixed-set) reading,
restored in upstream issue #72: `E` is fixed first and the exceptional null set of `α`
may depend on `E`.  Answer: no.

The definitions `visitAverage`, `HasExpectedLimit`, `KhintchineFixedSet` are reproduced
verbatim from plby/lean-proofs `ErdosProblems/Erdos994.lean` (commit 8822f7dd, Apache 2.0,
formal authors Codex / GPT-5.6 Sol; hashed copy in `ref/plby-Erdos994.lean`) so that the
two developments are directly comparable.  plby refutes only the quantifier-swapped
`∀ᵐ α, ∀ E` reading; the fixed-set statement below is what Marstrand disproved.
-/

open _root_.MeasureTheory _root_.Filter _root_.Set
open scoped _root_.Topology

attribute [local instance] Classical.propDecidable

/-- The normalized number of visits of the fractional parts
`fract (k * α)`, `1 ≤ k ≤ n`, to `E`.  At `n = 0` this is `0`. -/
noncomputable def visitAverage (E : Set ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n,
      if Int.fract ((k : ℝ) * α) ∈ E then (1 : ℝ) else 0) / (n : ℝ)

/-- The visit averages for `E` and `α` converge to the Lebesgue measure of `E`. -/
def HasExpectedLimit (E : Set ℝ) (α : ℝ) : Prop :=
  Tendsto (visitAverage E α) atTop (𝓝 (volume E).toReal)

/-- The conventional fixed-set quantifier order of Khintchine's historical conjecture.
Here the exceptional null set is allowed to depend on `E`. -/
def KhintchineFixedSet : Prop :=
  ∀ E : Set ℝ, MeasurableSet E → E ⊆ Ioo (0 : ℝ) 1 →
    ∀ᵐ α : ℝ, HasExpectedLimit E α

/-! The two roots `not_khintchineFixedSet` and `exists_counterexample_ae` are proved in
`Jsp827/Root.lean` from the development in `Marstrand/Main.lean`; this file only
fixes the definitions and the bridge below. -/

theorem not_khintchineFixedSet_of_exists
    (h : ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Ioo (0 : ℝ) 1 ∧
      ∀ᵐ α : ℝ, ¬ HasExpectedLimit E α) : ¬ KhintchineFixedSet := by
  intro hK
  obtain ⟨E, hE, hEI, hbad⟩ := h
  have hgood := hK E hE hEI
  have hfalse : ∀ᵐ α : ℝ, False := by
    filter_upwards [hgood, hbad] with α h1 h2
    exact h2 h1
  have hzero : (volume : Measure ℝ) univ = 0 := by simp [ae_iff] at hfalse
  simp at hzero

end

/-! ### Upstream module `Jsp827/Tower/Basic.lean` -/

section
/-!
# Towers for commuting endomorphisms: basic definitions

Avila–Candela, Ann. Inst. Fourier 66 (2016) 1529–1544, Section 1.  A measure-preserving
action of `ℕ^d` by commuting endomorphisms, boxes of multi-indices, admissible sets
(pairwise disjoint preimages over a box) and towers.
-/

open _root_.MeasureTheory _root_.Set
namespace RokhlinTower

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- A measure-preserving action of `ℕ^d` (as `Fin d → ℕ`) by commuting endomorphisms. -/
structure NatAction (d : ℕ) where
  /-- the endomorphism attached to a multi-index -/
  f : (Fin d → ℕ) → X → X
  f_zero : f 0 = id
  f_add : ∀ m n, f (m + n) = f m ∘ f n
  measurePreserving : ∀ n, MeasurePreserving (f n) μ μ

variable {μ}

namespace NatAction

variable {d : ℕ} (A : NatAction μ d)

lemma f_apply_add (m n : Fin d → ℕ) (x : X) : A.f (m + n) x = A.f m (A.f n x) :=
  congrFun (A.f_add m n) x

lemma f_comm (m n : Fin d → ℕ) (x : X) : A.f m (A.f n x) = A.f n (A.f m x) := by
  rw [← A.f_apply_add, ← A.f_apply_add, add_comm]

lemma measurable (n : Fin d → ℕ) : Measurable (A.f n) :=
  (A.measurePreserving n).measurable

/-- Preimages compose additively. -/
lemma preimage_preimage (m n : Fin d → ℕ) (B : Set X) :
    A.f m ⁻¹' (A.f n ⁻¹' B) = A.f (n + m) ⁻¹' B := by
  ext x
  simp only [Set.mem_preimage, A.f_apply_add]

lemma measure_preimage (n : Fin d → ℕ) {B : Set X} (hB : MeasurableSet B) :
    μ (A.f n ⁻¹' B) = μ B :=
  (A.measurePreserving n).measure_preimage hB.nullMeasurableSet

/-- Freeness: distinct multi-indices agree only on a null set. -/
def Free : Prop :=
  ∀ k l : Fin d → ℕ, k ≠ l → μ {x | A.f k x = A.f l x} = 0

end NatAction

/-- The box `[0, n)` of multi-indices. -/
def box {d : ℕ} (n : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i => Finset.range (n i)

lemma mem_box {d : ℕ} {n k : Fin d → ℕ} : k ∈ box n ↔ ∀ i, k i < n i := by
  simp [box, Fintype.mem_piFinset, Finset.mem_range]

lemma card_box {d : ℕ} (n : Fin d → ℕ) : (box n).card = ∏ i, n i := by
  simp [box, Fintype.card_piFinset, Finset.card_range]

namespace NatAction

variable {d : ℕ} (A : NatAction μ d)

/-- `B` is `n`-admissible: its preimages over the box are pairwise disjoint. -/
def Admissible (n : Fin d → ℕ) (B : Set X) : Prop :=
  MeasurableSet B ∧
    ∀ k ∈ box n, ∀ l ∈ box n, k ≠ l → Disjoint (A.f k ⁻¹' B) (A.f l ⁻¹' B)

/-- The tower over `B`. -/
def tower (n : Fin d → ℕ) (B : Set X) : Set X :=
  ⋃ k ∈ box n, A.f k ⁻¹' B

lemma measurableSet_tower {n : Fin d → ℕ} {B : Set X} (hB : MeasurableSet B) :
    MeasurableSet (A.tower n B) :=
  Finset.measurableSet_biUnion _ fun k _ ↦ A.measurable k hB

/-- The measure of an admissible tower is the number of levels times the base measure. -/
lemma measure_tower {n : Fin d → ℕ} {B : Set X} (hB : A.Admissible n B) :
    μ (A.tower n B) = (box n).card * μ B := by
  have hd : (↑(box n) : Set (Fin d → ℕ)).PairwiseDisjoint fun k ↦ A.f k ⁻¹' B :=
    fun k hk l hl hkl ↦ hB.2 k (by simpa using hk) l (by simpa using hl) hkl
  have hm : ∀ k ∈ box n, MeasurableSet (A.f k ⁻¹' B) := fun k _ ↦ A.measurable k hB.1
  rw [tower, measure_biUnion_finset hd hm]
  simp only [A.measure_preimage _ hB.1, Finset.sum_const, nsmul_eq_mul]

/-- Every level of an admissible tower has the measure of the base; in particular the
base measure is at most `μ univ / card (box n)`. -/
lemma card_mul_measure_le {n : Fin d → ℕ} {B : Set X} (hB : A.Admissible n B) :
    (box n).card * μ B ≤ μ univ := by
  rw [← A.measure_tower hB]
  exact measure_mono (subset_univ _)

/-- A preimage of an admissible set is admissible. -/
lemma Admissible.preimage {n : Fin d → ℕ} {B : Set X} (hB : A.Admissible n B)
    (m : Fin d → ℕ) : A.Admissible n (A.f m ⁻¹' B) := by
  have h : ∀ j : Fin d → ℕ,
      A.f j ⁻¹' (A.f m ⁻¹' B) = A.f m ⁻¹' (A.f j ⁻¹' B) := fun j ↦ by
    rw [A.preimage_preimage, A.preimage_preimage, add_comm]
  refine ⟨A.measurable m hB.1, fun k hk l hl hkl ↦ ?_⟩
  rw [h k, h l]
  exact Disjoint.preimage _ (hB.2 k hk l hl hkl)

end NatAction

end RokhlinTower

end

/-! ### Upstream module `Jsp827/Tower/Separation.lean` -/

section
/-!
# Separating a set from a translate (Avila–Candela Proposition 2.1)

Let `f, g` be measure-preserving endomorphisms of a probability space that agree only on a
null set.  Then inside `f ⁻¹' Y` there is a measurable `B` with `μ B ≥ (μ Y − ε)/4` and
`f ⁻¹' B` disjoint from `g ⁻¹' B`.

As in the paper, `f` and `g` are assumed to commute; this is part of the standing
hypotheses there (the endomorphisms come from an action of `ℕ^d`) and it is what makes the
final disjointness argument work.

Proof (AC Prop 2.1 / Lemma 2.2): choose a countable family of measurable sets separating
points (`HasCountableSeparatingOn X MeasurableSet univ`); the finite partitions `P_r`
generated by the first `r` sets refine each other and separate points, so
`Ω_r := ⋃_{A ∈ P_r} f⁻¹A ∩ g⁻¹A` decreases to `{f = g}` and `μ Ω_r → 0`.  The atoms of `P_r`
are the fibres of `signPattern S r`.  Colouring them randomly (each atom coloured `true`
independently with probability `1/2`) and writing `C` for the union of the `true` atoms, the
expected measure of `f⁻¹(Y ∩ C) \ g⁻¹C` is at least `(μ Y − μ Ω_r)/4`, so some colouring
works, and `B := f⁻¹(Y ∩ C) \ g⁻¹C` satisfies `f⁻¹B ∩ g⁻¹B = ∅` because `f` and `g` commute.
-/

open _root_.MeasureTheory _root_.Set

namespace RokhlinTower

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Counting the random subsets used in the averaging argument: for `σ ≠ τ` in a finite type
`K`, exactly a quarter of the Boolean colourings `c : K → Bool` satisfy `c σ = true` and
`c τ = false`. -/
lemma sum_ite_eq_card {K : Type*} [Fintype K] [DecidableEq K] {σ τ : K} (hστ : σ ≠ τ) :
    ∑ c : K → Bool, (if c σ = true ∧ c τ = false then (4 : ℝ) else 0)
      = (Fintype.card (K → Bool) : ℝ) := by
  classical
  set F : K → Bool → ℝ := fun i b ↦
    if i = σ then (if b then 2 else 0) else if i = τ then (if b then 0 else 2) else 1 with hF
  have hprod : ∀ c : K → Bool,
      ∏ i : K, F i (c i) = if c σ = true ∧ c τ = false then (4 : ℝ) else 0 := by
    intro c
    have h1 : F σ (c σ) = if c σ = true then (2 : ℝ) else 0 := by simp [hF]
    have h2 : F τ (c τ) = if c τ = true then (0 : ℝ) else 2 := by simp [hF, Ne.symm hστ]
    rw [← Finset.prod_subset (Finset.subset_univ ({σ, τ} : Finset K)) ?_]
    · rw [Finset.prod_pair hστ, h1, h2]
      by_cases hσ : c σ = true <;> by_cases hτ : c τ = true <;> simp_all
      norm_num
    · intro i _ hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      simp [hF, hi.1, hi.2]
  have hsum : ∀ i : K, ∑ b : Bool, F i b = 2 := by
    intro i
    rcases eq_or_ne i σ with h | h
    · simp [hF, h]
    · rcases eq_or_ne i τ with h' | h' <;> simp [hF, h, h']
  calc ∑ c : K → Bool, (if c σ = true ∧ c τ = false then (4 : ℝ) else 0)
      = ∑ c : K → Bool, ∏ i : K, F i (c i) := by simp [hprod]
    _ = ∏ i : K, ∑ b : Bool, F i b := (Fintype.prod_sum F).symm
    _ = (Fintype.card (K → Bool) : ℝ) := by
        rw [Finset.prod_congr rfl fun i _ ↦ hsum i, Finset.prod_const, Finset.card_univ,
          Fintype.card_fun, Fintype.card_bool]
        push_cast
        ring

/-- The measure of `W` intersected with the preimage of a finite set of values splits as a
sum over the fibres. -/
lemma toReal_measure_inter_fiber [IsFiniteMeasure μ] {ι : Type*} [DecidableEq ι] {w : X → ι}
    (hw : ∀ i : ι, MeasurableSet {x : X | w x = i}) {W : Set X} (hW : MeasurableSet W)
    (T : Finset ι) :
    (μ (W ∩ {x : X | w x ∈ T})).toReal = ∑ i ∈ T, (μ (W ∩ {x : X | w x = i})).toReal := by
  have hUnion : W ∩ {x : X | w x ∈ T} = ⋃ i ∈ T, W ∩ {x : X | w x = i} := by
    ext x
    refine ⟨fun h ↦ Set.mem_iUnion₂.2 ⟨w x, h.2, h.1, rfl⟩, fun h ↦ ?_⟩
    obtain ⟨i, hi, hxW, hxi⟩ := Set.mem_iUnion₂.1 h
    refine ⟨hxW, ?_⟩
    show w x ∈ T
    rw [show w x = i from hxi]
    exact hi
  have hd : (T : Set ι).PairwiseDisjoint fun i ↦ W ∩ {x : X | w x = i} := by
    intro i _ j _ hij
    refine Set.disjoint_left.2 fun x hx hx' ↦ hij ?_
    exact hx.2.symm.trans hx'.2
  rw [hUnion, measure_biUnion_finset hd fun i _ ↦ hW.inter (hw i),
    ENNReal.toReal_sum fun i _ ↦ measure_ne_top μ _]

/-- **Averaging step (Avila–Candela Lemma 2.2).**  If `u, v : X → ι` have measurable fibres in
a finite type `ι`, then some Boolean colouring `c` of `ι` separates `u` from `v` on at least a
quarter of `W`, up to the set where `u` and `v` agree. -/
lemma exists_colouring [IsFiniteMeasure μ] {ι : Type*} [Fintype ι] [DecidableEq ι] {u v : X → ι}
    (hu : ∀ i : ι, MeasurableSet {x : X | u x = i}) (hv : ∀ i : ι, MeasurableSet {x : X | v x = i})
    {W : Set X} (hW : MeasurableSet W) :
    ∃ c : ι → Bool, (μ W).toReal - (μ {x : X | u x = v x}).toReal
      ≤ 4 * (μ (W ∩ {x : X | c (u x) = true ∧ c (v x) = false})).toReal := by
  classical
  set w : X → ι × ι := fun x ↦ (u x, v x) with hw
  have hwfib : ∀ p : ι × ι, MeasurableSet {x : X | w x = p} := by
    intro p
    have : {x : X | w x = p} = {x : X | u x = p.1} ∩ {x : X | v x = p.2} := by
      ext x; simp [hw, Prod.ext_iff]
    rw [this]
    exact (hu p.1).inter (hv p.2)
  set m : ι × ι → ℝ := fun p ↦ (μ (W ∩ {x : X | w x = p})).toReal
  set N : ℝ := (Fintype.card (ι → Bool) : ℝ) with hN
  have hN0 : 0 ≤ N := by positivity
  have hdiag : ∑ p ∈ Finset.univ.filter fun p : ι × ι ↦ p.1 = p.2, m p
      = (μ (W ∩ {x : X | u x = v x})).toReal := by
    rw [← toReal_measure_inter_fiber hwfib hW _]
    congr 2
    ext x
    simp [hw]
  have htot : ∑ p : ι × ι, m p = (μ W).toReal := by
    rw [← toReal_measure_inter_fiber hwfib hW Finset.univ]
    congr 2
    simp
  have hcol : ∀ c : ι → Bool,
      (μ (W ∩ {x : X | c (u x) = true ∧ c (v x) = false})).toReal
        = ∑ p ∈ Finset.univ.filter fun p : ι × ι ↦ c p.1 = true ∧ c p.2 = false, m p := by
    intro c
    rw [← toReal_measure_inter_fiber hwfib hW _]
    congr 2
    ext x
    simp [hw]
  have hrw : ∑ c : ι → Bool, 4 * (μ (W ∩ {x : X | c (u x) = true ∧ c (v x) = false})).toReal
      = ∑ p : ι × ι, (∑ c : ι → Bool,
          (if c p.1 = true ∧ c p.2 = false then (4 : ℝ) else 0)) * m p := by
    simp only [hcol, Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ ↦ by split <;> ring
  have hlow : ∑ p : ι × ι, (if p.1 = p.2 then (0 : ℝ) else N * m p)
      ≤ ∑ p : ι × ι, (∑ c : ι → Bool,
          (if c p.1 = true ∧ c p.2 = false then (4 : ℝ) else 0)) * m p := by
    refine Finset.sum_le_sum fun p _ ↦ ?_
    rcases eq_or_ne p.1 p.2 with h | h
    · simp [h]
    · rw [sum_ite_eq_card h, ← hN]
      simp [h]
  have hsplit : ∑ p : ι × ι, (if p.1 = p.2 then (0 : ℝ) else N * m p)
      = N * ((μ W).toReal - (μ (W ∩ {x : X | u x = v x})).toReal) := by
    have h1 : ∑ p ∈ Finset.univ.filter fun p : ι × ι ↦ p.1 = p.2, m p
        + ∑ p ∈ Finset.univ.filter fun p : ι × ι ↦ ¬ p.1 = p.2, m p = ∑ p : ι × ι, m p :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have h2 : ∑ p : ι × ι, (if p.1 = p.2 then (0 : ℝ) else N * m p)
        = ∑ p ∈ Finset.univ.filter fun p : ι × ι ↦ ¬ p.1 = p.2, N * m p := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun p _ ↦ by split <;> simp_all
    rw [h2, ← Finset.mul_sum, ← htot, ← hdiag]
    congr 1
    linarith [h1]
  have hmono : (μ (W ∩ {x : X | u x = v x})).toReal ≤ (μ {x : X | u x = v x}).toReal :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono Set.inter_subset_right)
  have hkey : ∑ _c : ι → Bool, ((μ W).toReal - (μ {x : X | u x = v x}).toReal)
      ≤ ∑ c : ι → Bool, 4 * (μ (W ∩ {x : X | c (u x) = true ∧ c (v x) = false})).toReal := by
    calc ∑ _c : ι → Bool, ((μ W).toReal - (μ {x : X | u x = v x}).toReal)
        = N * ((μ W).toReal - (μ {x : X | u x = v x}).toReal) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
      _ ≤ N * ((μ W).toReal - (μ (W ∩ {x : X | u x = v x})).toReal) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hN0
      _ = ∑ p : ι × ι, (if p.1 = p.2 then (0 : ℝ) else N * m p) := hsplit.symm
      _ ≤ ∑ p : ι × ι, (∑ c : ι → Bool,
            (if c p.1 = true ∧ c p.2 = false then (4 : ℝ) else 0)) * m p := hlow
      _ = _ := hrw.symm
  obtain ⟨c, -, hc⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hkey
  exact ⟨c, hc⟩

/-- The `Bool`-valued pattern recording membership of `x` in the first `r` sets of the family
`S`; its fibres are the atoms of the finite partition generated by `S 0, …, S (r - 1)`. -/
noncomputable def signPattern (S : ℕ → Set X) (r : ℕ) (x : X) : Fin r → Bool :=
  fun i ↦ @decide (x ∈ S i) (Classical.propDecidable _)

omit [MeasurableSpace X] in
/-- Two points have the same level-`r` pattern iff they are not separated by any of the first
`r` sets. -/
lemma signPattern_eq_iff {S : ℕ → Set X} {r : ℕ} {x y : X} :
    signPattern S r x = signPattern S r y ↔ ∀ i : Fin r, (x ∈ S i ↔ y ∈ S i) := by
  simp [signPattern, funext_iff, decide_eq_decide]

/-- The atoms of the level-`r` partition are measurable. -/
lemma measurableSet_signPattern_eq {S : ℕ → Set X} (hS : ∀ n : ℕ, MeasurableSet (S n)) (r : ℕ)
    (σ : Fin r → Bool) : MeasurableSet {x : X | signPattern S r x = σ} := by
  have hEq : {x : X | signPattern S r x = σ} = ⋂ i : Fin r, (if σ i then S i else (S i)ᶜ) := by
    ext x
    rw [Set.mem_iInter]
    show signPattern S r x = σ ↔ ∀ i : Fin r, x ∈ if σ i then S i else (S i)ᶜ
    rw [funext_iff]
    exact forall_congr' fun i ↦ by
      rcases Bool.eq_false_or_eq_true (σ i) with h | h <;> rw [h] <;> simp [signPattern]
  rw [hEq]
  exact MeasurableSet.iInter fun i ↦ by cases σ i <;> simp [hS]

/-- A union of atoms of the level-`r` partition is measurable. -/
lemma measurableSet_signPattern_mem {S : ℕ → Set X} (hS : ∀ n : ℕ, MeasurableSet (S n)) {r : ℕ}
    (T : Set (Fin r → Bool)) : MeasurableSet {x : X | signPattern S r x ∈ T} := by
  have hEq : {x : X | signPattern S r x ∈ T} = ⋃ σ ∈ T, {x : X | signPattern S r x = σ} := by
    ext x
    refine ⟨fun h ↦ Set.mem_iUnion₂.2 ⟨_, h, rfl⟩, fun h ↦ ?_⟩
    obtain ⟨σ, hσ, hx⟩ := Set.mem_iUnion₂.1 h
    show signPattern S r x ∈ T
    rw [show signPattern S r x = σ from hx]
    exact hσ
  rw [hEq]
  exact MeasurableSet.biUnion T.to_countable fun σ _ ↦ measurableSet_signPattern_eq hS r σ

/-- **Avila–Candela Proposition 2.1.** -/
theorem exists_separated_subset [IsProbabilityMeasure μ]
    [HasCountableSeparatingOn X MeasurableSet univ]
    {f g : X → X} (hf : MeasurePreserving f μ μ) (hg : MeasurePreserving g μ μ)
    (hcomm : ∀ x : X, f (g x) = g (f x))
    (hfg : μ {x | f x = g x} = 0) {Y : Set X} (hY : MeasurableSet Y) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : Set X, MeasurableSet B ∧ B ⊆ f ⁻¹' Y ∧
      (μ Y).toReal - ε ≤ 4 * (μ B).toReal ∧ Disjoint (f ⁻¹' B) (g ⁻¹' B) := by
  classical
  obtain ⟨S, hSm, hSsep⟩ := exists_seq_separating X MeasurableSet.empty univ
  set Ω : ℕ → Set X := fun r ↦ {x : X | signPattern S r (f x) = signPattern S r (g x)}
  have hΩmeas : ∀ r : ℕ, MeasurableSet (Ω r) := by
    intro r
    have hEq : Ω r = ⋃ σ : Fin r → Bool,
        f ⁻¹' {y : X | signPattern S r y = σ} ∩ g ⁻¹' {y : X | signPattern S r y = σ} := by
      ext x
      refine ⟨fun hx ↦ Set.mem_iUnion.2 ⟨signPattern S r (f x), rfl, hx.symm⟩, fun hx ↦ ?_⟩
      obtain ⟨σ, h1, h2⟩ := Set.mem_iUnion.1 hx
      exact h1.trans h2.symm
    rw [hEq]
    exact MeasurableSet.iUnion fun σ ↦
      ((measurableSet_signPattern_eq hSm r σ).preimage hf.measurable).inter
        ((measurableSet_signPattern_eq hSm r σ).preimage hg.measurable)
  have hanti : Antitone Ω := by
    intro r r' hrr' x hx
    exact signPattern_eq_iff.2 fun i ↦ signPattern_eq_iff.1 hx ⟨i, i.2.trans_le hrr'⟩
  have hzero : μ (⋂ r, Ω r) = 0 := by
    refine measure_mono_null (fun x hx ↦ ?_) hfg
    refine hSsep (f x) (Set.mem_univ _) (g x) (Set.mem_univ _) fun n ↦ ?_
    exact signPattern_eq_iff.1 (Set.mem_iInter.1 hx (n + 1)) ⟨n, Nat.lt_succ_self n⟩
  have hlim : Filter.Tendsto (fun r ↦ μ (Ω r)) Filter.atTop (nhds 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) (fun r ↦ (hΩmeas r).nullMeasurableSet)
      hanti ⟨0, measure_ne_top μ _⟩
    rw [hzero] at h
    exact h
  obtain ⟨r, hr⟩ := (hlim.eventually_lt_const (ENNReal.ofReal_pos.2 hε)).exists
  have hrε : (μ {x : X | signPattern S r (f x) = signPattern S r (g x)}).toReal < ε :=
    ENNReal.toReal_lt_of_lt_ofReal hr
  have hufib : ∀ σ : Fin r → Bool, MeasurableSet {x : X | signPattern S r (f x) = σ} :=
    fun σ ↦ (measurableSet_signPattern_eq hSm r σ).preimage hf.measurable
  have hvfib : ∀ σ : Fin r → Bool, MeasurableSet {x : X | signPattern S r (g x) = σ} :=
    fun σ ↦ (measurableSet_signPattern_eq hSm r σ).preimage hg.measurable
  have hW : MeasurableSet (f ⁻¹' Y) := hY.preimage hf.measurable
  obtain ⟨c, hc⟩ := exists_colouring (μ := μ) (u := fun x ↦ signPattern S r (f x))
    (v := fun x ↦ signPattern S r (g x)) hufib hvfib hW
  refine ⟨f ⁻¹' Y ∩ {x : X | c (signPattern S r (f x)) = true ∧
    c (signPattern S r (g x)) = false}, ?_, Set.inter_subset_left, ?_, ?_⟩
  · exact hW.inter (((measurableSet_signPattern_mem hSm {σ | c σ = true}).preimage
      hf.measurable).inter ((measurableSet_signPattern_mem hSm {σ | c σ = false}).preimage
      hg.measurable))
  · have hpre : (μ (f ⁻¹' Y)).toReal = (μ Y).toReal := by
      rw [hf.measure_preimage hY.nullMeasurableSet]
    rw [hpre] at hc
    linarith
  · refine Set.disjoint_left.2 fun x hxf hxg ↦ ?_
    have h1 : c (signPattern S r (g (f x))) = false := hxf.2.2
    have h2 : c (signPattern S r (f (g x))) = true := hxg.2.1
    rw [hcomm x, h1] at h2
    exact Bool.false_ne_true h2

end RokhlinTower

end

/-! ### Upstream module `Jsp827/Tower/Iterate.lean` -/

section
/-!
# Iterating the separation step (Avila–Candela Lemma 2.3)

Applying Proposition 2.1 (`RokhlinTower.exists_separated_subset`) once for every ordered pair
of distinct box elements produces, inside some preimage of `Y`, an `n`-admissible set of
measure at least `c · μ Y` with `c = 5 ^ (-(number of pairs))`.

The induction is carried out over an arbitrary finite set `L` of ordered pairs of
multi-indices in `exists_subset_pairwise_disjoint`; Lemma 2.3 is the special case where `L`
is the set of pairs of distinct elements of the box.
-/

open _root_.MeasureTheory _root_.Set
namespace RokhlinTower

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

namespace NatAction

variable {d : ℕ} (A : NatAction μ d)

/-- Iterating Proposition 2.1 over a finite set `L` of ordered pairs of multi-indices: inside
some preimage of `Y` there is a measurable set `B` of measure at least `5 ^ (-L.card) · μ Y`
whose preimages under the two entries of every pair of distinct multi-indices in `L` are
disjoint. -/
lemma exists_subset_pairwise_disjoint [IsProbabilityMeasure μ]
    [HasCountableSeparatingOn X MeasurableSet univ] (hfree : A.Free)
    (L : Finset ((Fin d → ℕ) × (Fin d → ℕ))) {Y : Set X} (hY : MeasurableSet Y) :
    ∃ (N : Fin d → ℕ) (B : Set X), MeasurableSet B ∧ B ⊆ A.f N ⁻¹' Y ∧
      (∀ q ∈ L, q.1 ≠ q.2 → Disjoint (A.f q.1 ⁻¹' B) (A.f q.2 ⁻¹' B)) ∧
      (1 / 5 : ℝ) ^ L.card * (μ Y).toReal ≤ (μ B).toReal := by
  classical
  induction L using Finset.induction_on with
  | empty =>
    refine ⟨0, Y, hY, ?_, by simp, by simp⟩
    simp [A.f_zero]
  | insert a L ha ih =>
    obtain ⟨N₀, B₀, hB₀meas, hB₀sub, hB₀disj, hB₀le⟩ := ih
    obtain ⟨k, l⟩ := a
    have hcard : (insert (k, l) L).card = L.card + 1 := Finset.card_insert_of_notMem ha
    have hYpos : (0 : ℝ) ≤ (μ Y).toReal := ENNReal.toReal_nonneg
    by_cases hkl : k = l
    · refine ⟨N₀, B₀, hB₀meas, hB₀sub, ?_, ?_⟩
      · intro q hq hq2
        rcases Finset.mem_insert.1 hq with h | h
        · subst h
          exact absurd hkl hq2
        · exact hB₀disj q h hq2
      · have h2 : (1 / 5 : ℝ) ^ (L.card + 1) ≤ (1 / 5 : ℝ) ^ L.card := by
          rw [pow_succ]
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 5) L.card]
        rw [hcard]
        nlinarith [mul_le_mul_of_nonneg_right h2 hYpos]
    · by_cases hpos : 0 < (μ B₀).toReal
      · obtain ⟨B₁, hB₁meas, hB₁sub, hB₁ge, hB₁disj⟩ :=
          exists_separated_subset (μ := μ) (A.measurePreserving k) (A.measurePreserving l)
            (fun x ↦ A.f_comm k l x) (hfree k l hkl) hB₀meas
            (show (0 : ℝ) < (μ B₀).toReal / 5 by linarith)
        have hstep : ∀ m : Fin d → ℕ, A.f m ⁻¹' B₁ ⊆ A.f (m + k) ⁻¹' B₀ := by
          intro m
          have h := preimage_mono (f := A.f m) hB₁sub
          rwa [A.preimage_preimage, add_comm] at h
        refine ⟨N₀ + k, B₁, hB₁meas, ?_, ?_, ?_⟩
        · have h : A.f k ⁻¹' B₀ ⊆ A.f k ⁻¹' (A.f N₀ ⁻¹' Y) := preimage_mono hB₀sub
          rw [A.preimage_preimage] at h
          exact hB₁sub.trans h
        · intro q hq hq2
          rcases Finset.mem_insert.1 hq with h | h
          · subst h
            exact hB₁disj
          · have hd2 : Disjoint (A.f (q.1 + k) ⁻¹' B₀) (A.f (q.2 + k) ⁻¹' B₀) := by
              have h3 := (hB₀disj q h hq2).preimage (A.f k)
              rwa [A.preimage_preimage, A.preimage_preimage] at h3
            exact Disjoint.mono (hstep q.1) (hstep q.2) hd2
        · have hb : (μ B₀).toReal / 5 ≤ (μ B₁).toReal := by linarith
          have hsplit : (1 / 5 : ℝ) ^ (L.card + 1) * (μ Y).toReal
              = ((1 / 5 : ℝ) ^ L.card * (μ Y).toReal) / 5 := by
            rw [pow_succ]
            ring
          rw [hcard, hsplit]
          linarith
      · have hY0 : (μ Y).toReal = 0 := by
          have h2 : (μ B₀).toReal ≤ 0 := not_lt.1 hpos
          have h3 : (0 : ℝ) < (1 / 5 : ℝ) ^ L.card := pow_pos (by norm_num) _
          have h5 : (μ Y).toReal ≤ 0 := by
            by_contra h6
            have h7 : 0 < (1 / 5 : ℝ) ^ L.card * (μ Y).toReal := mul_pos h3 (not_le.1 h6)
            linarith
          linarith
        refine ⟨0, ∅, MeasurableSet.empty, empty_subset _, fun q _ _ ↦ by simp, ?_⟩
        rw [hcard, hY0]
        simp

/-- **AC Lemma 2.3.**  There is a constant `c > 0` (depending only on `n` and `d`) such that
inside some preimage of any measurable `Y` there is an `n`-admissible set of measure at least
`c · μ Y`. -/
theorem exists_admissible_subset [IsProbabilityMeasure μ]
    [HasCountableSeparatingOn X MeasurableSet univ] (hfree : A.Free) (n : Fin d → ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ Y : Set X, MeasurableSet Y →
      ∃ (N : Fin d → ℕ) (B : Set X), A.Admissible n B ∧ B ⊆ A.f N ⁻¹' Y ∧
        c * (μ Y).toReal ≤ (μ B).toReal := by
  classical
  set pairs : Finset ((Fin d → ℕ) × (Fin d → ℕ)) :=
    (box n ×ˢ box n).filter fun q ↦ q.1 ≠ q.2 with hpairs
  refine ⟨(1 / 5 : ℝ) ^ pairs.card, pow_pos (by norm_num) _, fun Y hY ↦ ?_⟩
  obtain ⟨N, B, hBmeas, hBsub, hBdisj, hBle⟩ := A.exists_subset_pairwise_disjoint hfree pairs hY
  refine ⟨N, B, ⟨hBmeas, fun k hk l hl hkl ↦ ?_⟩, hBsub, hBle⟩
  refine hBdisj (k, l) ?_ hkl
  simp only [hpairs, Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨hk, hl⟩, hkl⟩

end NatAction

end RokhlinTower

end

/-! ### Upstream module `Jsp827/Tower/Sup.lean` -/

section
/-!
# Towers of measure `> 2^{-d} μ Y − ε` (Avila–Candela Lemma 2.4)

A supremum argument: if the best admissible base inside preimages of `Y` had measure
`ρ < μ Y / (2^d ∏ n i)`, one could enlarge a near-optimal base by an admissible set found
(Lemma 2.3) inside `f_{N₀+n}⁻¹ Y` minus the `2n`-tower of the near-optimal base.
-/

open _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal

namespace RokhlinTower

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Doubling every side of a box multiplies its cardinality by `2 ^ d`. -/
lemma card_box_two_mul {d : ℕ} (n : Fin d → ℕ) :
    (box fun i ↦ 2 * n i).card = 2 ^ d * (box n).card := by
  simp [card_box, Finset.prod_mul_distrib]

/-- A box with positive sides contains its own corner inside its double. -/
lemma self_mem_box_two_mul {d : ℕ} {n : Fin d → ℕ} (hn : ∀ i, 0 < n i) :
    n ∈ box fun i ↦ 2 * n i :=
  mem_box.2 fun i ↦ by have := hn i; omega

namespace NatAction

variable {d : ℕ} (A : NatAction μ d)

/-- Each level of a tower is contained in the tower. -/
lemma preimage_subset_tower {m k : Fin d → ℕ} (hk : k ∈ box m) (B : Set X) :
    A.f k ⁻¹' B ⊆ A.tower m B := fun _ hx ↦ Set.mem_biUnion hk hx

/-- The union bound for a tower: no admissibility is needed. -/
lemma measure_tower_le (m : Fin d → ℕ) {B : Set X} (hB : MeasurableSet B) :
    μ (A.tower m B) ≤ (box m).card * μ B :=
  calc μ (A.tower m B) ≤ ∑ _k ∈ box m, μ B := by
        refine (measure_biUnion_finset_le _ _).trans ?_
        exact Finset.sum_le_sum fun k _ ↦ (A.measure_preimage k hB).le
    _ = (box m).card * μ B := by simp [mul_comm]

/-- Splicing an `n`-admissible set living outside the `2n`-tower of `D` onto a preimage of
`f n ⁻¹' D` preserves `n`-admissibility. -/
lemma Admissible.union_preimage {n : Fin d → ℕ} {D C : Set X}
    (hD : A.Admissible n D) (hC : A.Admissible n C) (N : Fin d → ℕ)
    (hCT : ∀ x ∈ C, A.f N x ∉ A.tower (fun i ↦ 2 * n i) D) :
    A.Admissible n (A.f N ⁻¹' (A.f n ⁻¹' D) ∪ C) := by
  have hP : A.Admissible n (A.f N ⁻¹' (A.f n ⁻¹' D)) := (hD.preimage A n).preimage A N
  have cross : ∀ k ∈ box n, ∀ l ∈ box n,
      Disjoint (A.f k ⁻¹' C) (A.f l ⁻¹' (A.f N ⁻¹' (A.f n ⁻¹' D))) := by
    intro k hk l hl
    rw [Set.disjoint_left]
    intro x hxk hxl
    obtain ⟨m, hm⟩ : ∃ m : Fin d → ℕ, ∀ i, m i = l i + n i - k i := ⟨_, fun _ ↦ rfl⟩
    have hmbox : m ∈ box fun i ↦ 2 * n i := mem_box.2 fun i ↦ by
      have h1 := mem_box.1 hk i
      have h2 := mem_box.1 hl i
      have h3 := hm i
      omega
    refine hCT _ hxk (A.preimage_subset_tower hmbox D ?_)
    show A.f m (A.f N (A.f k x)) ∈ D
    have key : A.f m (A.f N (A.f k x)) = A.f n (A.f N (A.f l x)) := by
      simp only [← A.f_apply_add]
      congr 1
      funext i
      have h1 := mem_box.1 hk i
      have h3 := hm i
      simp only [Pi.add_apply]
      omega
    rw [key]
    exact hxl
  refine ⟨(A.measurable N (A.measurable n hD.1)).union hC.1, fun k hk l hl hkl ↦ ?_⟩
  rw [Set.preimage_union, Set.preimage_union, Set.disjoint_union_left,
    Set.disjoint_union_right, Set.disjoint_union_right]
  exact ⟨⟨hP.2 k hk l hl hkl, (cross l hl k hk).symm⟩,
    ⟨cross k hk l hl, hC.2 k hk l hl hkl⟩⟩

/-- The set of measures of `n`-admissible sets sitting inside some preimage of `Y`. -/
def baseMeasures (n : Fin d → ℕ) (Y : Set X) : Set ℝ :=
  {r : ℝ | ∃ (N : Fin d → ℕ) (B : Set X), A.Admissible n B ∧ B ⊆ A.f N ⁻¹' Y ∧
    r = (μ B).toReal}

/-- The empty base shows that `0` belongs to `baseMeasures`. -/
lemma zero_mem_baseMeasures (n : Fin d → ℕ) (Y : Set X) : (0 : ℝ) ∈ A.baseMeasures n Y :=
  ⟨0, ∅, ⟨MeasurableSet.empty, fun k _ l _ _ ↦ by simp⟩, Set.empty_subset _, by simp⟩

/-- `baseMeasures` is nonempty. -/
lemma baseMeasures_nonempty (n : Fin d → ℕ) (Y : Set X) : (A.baseMeasures n Y).Nonempty :=
  ⟨0, A.zero_mem_baseMeasures n Y⟩

/-- `baseMeasures` is bounded above by `1`. -/
lemma baseMeasures_bddAbove [IsProbabilityMeasure μ] (n : Fin d → ℕ) (Y : Set X) :
    BddAbove (A.baseMeasures n Y) := by
  refine ⟨1, ?_⟩
  rintro r ⟨N, B, -, -, rfl⟩
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one

/-- The supremum of the base measures is at least `μ Y / (2 ^ d * card (box n))`. -/
lemma measure_le_sSup_baseMeasures [IsProbabilityMeasure μ]
    [HasCountableSeparatingOn X MeasurableSet univ] (hfree : A.Free) {n : Fin d → ℕ}
    (hn : ∀ i, 0 < n i) {Y : Set X} (hY : MeasurableSet Y) :
    (μ Y).toReal ≤ 2 ^ d * (box n).card * sSup (A.baseMeasures n Y) := by
  have hSne : (A.baseMeasures n Y).Nonempty := A.baseMeasures_nonempty n Y
  have hSbdd : BddAbove (A.baseMeasures n Y) := A.baseMeasures_bddAbove n Y
  set ρ : ℝ := sSup (A.baseMeasures n Y) with hρdef
  have hπnn : (0 : ℝ) ≤ 2 ^ d * (box n).card := by positivity
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨c, hc, hLem⟩ := A.exists_admissible_subset hfree n
  have hδpos : 0 < (μ Y).toReal - 2 ^ d * (box n).card * ρ := by linarith
  obtain ⟨-, ⟨N₀, D, hD, hDY, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hSne
    (show ρ - ((μ Y).toReal - 2 ^ d * (box n).card * ρ) * c < ρ from
      sub_lt_self _ (mul_pos hδpos hc))
  have hDρ : (μ D).toReal ≤ ρ := le_csSup hSbdd ⟨N₀, D, hD, hDY, rfl⟩
  have hTmeas : MeasurableSet (A.tower (fun i ↦ 2 * n i) D) :=
    A.measurableSet_tower hD.1
  have hTle : (μ (A.tower (fun i ↦ 2 * n i) D)).toReal ≤
      2 ^ d * (box n).card * (μ D).toReal := by
    calc (μ (A.tower (fun i ↦ 2 * n i) D)).toReal
        ≤ (((box fun i ↦ 2 * n i).card : ℝ≥0∞) * μ D).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
            (measure_ne_top μ D)) (A.measure_tower_le _ hD.1)
      _ = ((box fun i ↦ 2 * n i).card : ℝ) * (μ D).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
      _ = 2 ^ d * (box n).card * (μ D).toReal := by
          rw [card_box_two_mul]; push_cast; ring
  -- the set `Y' \ T` has measure at least `δ`
  have hY' : μ (A.f (N₀ + n) ⁻¹' Y) = μ Y := A.measure_preimage _ hY
  have hreal : (μ Y).toReal ≤
      (μ (A.f (N₀ + n) ⁻¹' Y \ A.tower (fun i ↦ 2 * n i) D)).toReal +
        (μ (A.tower (fun i ↦ 2 * n i) D)).toReal := by
    rw [← hY', ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) ?_
    refine (measure_mono (fun x hx ↦ ?_)).trans (measure_union_le _ _)
    by_cases hxT : x ∈ A.tower (fun i ↦ 2 * n i) D
    · exact Or.inr hxT
    · exact Or.inl ⟨hx, hxT⟩
  have hstep : 2 ^ d * (box n).card * (μ D).toReal ≤ 2 ^ d * (box n).card * ρ :=
    mul_le_mul_of_nonneg_left hDρ hπnn
  have hδle : (μ Y).toReal - 2 ^ d * (box n).card * ρ ≤
      (μ (A.f (N₀ + n) ⁻¹' Y \ A.tower (fun i ↦ 2 * n i) D)).toReal := by linarith
  obtain ⟨N₁, C, hC, hCsub, hCmeas⟩ :=
    hLem _ ((A.measurable _ hY).diff hTmeas)
  have hCδ : c * ((μ Y).toReal - 2 ^ d * (box n).card * ρ) ≤ (μ C).toReal :=
    le_trans (mul_le_mul_of_nonneg_left hδle hc.le) hCmeas
  -- the enlarged base
  have hCT : ∀ x ∈ C, A.f N₁ x ∉ A.tower (fun i ↦ 2 * n i) D := fun x hx ↦ (hCsub hx).2
  have hadm : A.Admissible n (A.f N₁ ⁻¹' (A.f n ⁻¹' D) ∪ C) :=
    Admissible.union_preimage A hD hC N₁ hCT
  have hnD : A.f n ⁻¹' (A.f N₀ ⁻¹' Y) = A.f (N₀ + n) ⁻¹' Y := A.preimage_preimage _ _ _
  have hN₁ : A.f N₁ ⁻¹' (A.f (N₀ + n) ⁻¹' Y) = A.f (N₀ + n + N₁) ⁻¹' Y :=
    A.preimage_preimage _ _ _
  have hsub : A.f N₁ ⁻¹' (A.f n ⁻¹' D) ∪ C ⊆ A.f (N₀ + n + N₁) ⁻¹' Y := by
    rw [← hN₁]
    refine Set.union_subset (Set.preimage_mono ?_) (fun x hx ↦ (hCsub hx).1)
    rw [← hnD]
    exact Set.preimage_mono hDY
  -- the measure of the enlarged base exceeds `ρ`
  have hdisj : Disjoint (A.f N₁ ⁻¹' (A.f n ⁻¹' D)) C := by
    rw [Set.disjoint_right]
    intro x hx hx'
    exact hCT x hx (A.preimage_subset_tower (self_mem_box_two_mul hn) D hx')
  have hmeas : μ (A.f N₁ ⁻¹' (A.f n ⁻¹' D) ∪ C) = μ D + μ C := by
    rw [measure_union hdisj hC.1, A.measure_preimage _ (A.measurable n hD.1),
      A.measure_preimage _ hD.1]
  have hBρ : (μ (A.f N₁ ⁻¹' (A.f n ⁻¹' D) ∪ C)).toReal ≤ ρ :=
    le_csSup hSbdd ⟨N₀ + n + N₁, _, hadm, hsub, rfl⟩
  rw [hmeas, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hBρ
  nlinarith [hr, hCδ, hBρ]

/-- **AC Lemma 2.4.**  Inside some preimage of `Y` there is an `n`-admissible set whose tower
has measure `> 2^{-d} μ Y − ε`. -/
theorem exists_admissible_tower_ge [IsProbabilityMeasure μ]
    [HasCountableSeparatingOn X MeasurableSet univ] (hfree : A.Free) (n : Fin d → ℕ)
    (hn : ∀ i, 0 < n i) {Y : Set X} (hY : MeasurableSet Y) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : Fin d → ℕ) (B : Set X), A.Admissible n B ∧ B ⊆ A.f N ⁻¹' Y ∧
      (μ Y).toReal / 2 ^ d - ε ≤ (μ (A.tower n B)).toReal := by
  have hcard : 0 < (box n).card := by
    rw [card_box]
    exact Finset.prod_pos fun i _ ↦ hn i
  have hcardR : (0 : ℝ) < (box n).card := by exact_mod_cast hcard
  have hSne : (A.baseMeasures n Y).Nonempty := A.baseMeasures_nonempty n Y
  have hkey := A.measure_le_sSup_baseMeasures hfree hn hY
  obtain ⟨-, ⟨N, B, hB, hBY, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hSne
    (show sSup (A.baseMeasures n Y) - ε / (box n).card < sSup (A.baseMeasures n Y) from
      sub_lt_self _ (by positivity))
  refine ⟨N, B, hB, hBY, ?_⟩
  rw [A.measure_tower hB, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hdiv : (μ Y).toReal / 2 ^ d ≤ (box n).card * sSup (A.baseMeasures n Y) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ d)]
    have h : 2 ^ d * ((box n).card : ℝ) * sSup (A.baseMeasures n Y)
        = (box n).card * sSup (A.baseMeasures n Y) * 2 ^ d := by ring
    linarith [hkey]
  have hmul : (box n).card * (sSup (A.baseMeasures n Y) - ε / (box n).card) ≤
      (box n).card * (μ B).toReal := mul_le_mul_of_nonneg_left hr.le hcardR.le
  have hexp : ((box n).card : ℝ) * (sSup (A.baseMeasures n Y) - ε / (box n).card) =
      (box n).card * sSup (A.baseMeasures n Y) - ε := by
    field_simp
  linarith

end NatAction

end RokhlinTower

end

/-! ### Upstream module `Jsp827/Tower/Main.lean` -/

section
/-!
# Rokhlin towers for commuting endomorphisms (Avila–Candela Theorem 1.2)

For a free measure-preserving `ℕ^d`-action on a probability space with a countable
separating family of measurable sets, every box `n` (all sides positive) admits an
`n`-tower of measure `≥ 1 − ε`: dyadic refinement `2^K n` and the sup argument of AC §2.
-/

open _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal

namespace RokhlinTower

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Doubling all sides `K` times multiplies the cardinality of a box by `(2 ^ K) ^ d`. -/
lemma card_box_pow_mul {d : ℕ} (K : ℕ) (N : Fin d → ℕ) :
    (box fun i ↦ 2 ^ K * N i).card = (2 ^ K) ^ d * (box N).card := by
  simp [card_box, Finset.prod_mul_distrib]

/-- The index set `fun i ↦ (t i + 1) * N i + j i`, for `t` in the box of side `2 ^ K - 1`.
It indexes the levels of the sub-tower `D` in the proof of Theorem 1.2: all coordinates of
the `N`-scaled part are at least `1`, which leaves room to subtract an index `j < N`. -/
def shiftBox {d : ℕ} (K : ℕ) (N j : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  (box fun _ ↦ 2 ^ K - 1).image fun t i ↦ (t i + 1) * N i + j i

/-- The shifted index set sits inside the box of side `2 ^ K * N`. -/
lemma shiftBox_subset {d : ℕ} (K : ℕ) {N j : Fin d → ℕ} (hj : ∀ i, j i < N i) :
    shiftBox K N j ⊆ box fun i ↦ 2 ^ K * N i := by
  intro u hu
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
  refine mem_box.2 fun i ↦ ?_
  have h1 : t i < 2 ^ K - 1 := mem_box.1 ht i
  have h3 : 1 ≤ 2 ^ K := Nat.one_le_pow _ _ (by norm_num)
  have h4 : t i + 2 ≤ 2 ^ K := by omega
  calc (t i + 1) * N i + j i < (t i + 1) * N i + N i := Nat.add_lt_add_left (hj i) _
    _ = (t i + 2) * N i := by ring
    _ ≤ 2 ^ K * N i := Nat.mul_le_mul h4 le_rfl

/-- The shifted index set has `(2 ^ K - 1) ^ d` elements. -/
lemma card_shiftBox {d : ℕ} (K : ℕ) {N : Fin d → ℕ} (hN : ∀ i, 0 < N i) (j : Fin d → ℕ) :
    (shiftBox K N j).card = (2 ^ K - 1) ^ d := by
  have hinj : Set.InjOn (fun (t : Fin d → ℕ) i ↦ (t i + 1) * N i + j i)
      ↑(box fun _ : Fin d ↦ 2 ^ K - 1) := by
    intro t _ t' _ h
    funext i
    have hi : (t i + 1) * N i + j i = (t' i + 1) * N i + j i := congrFun h i
    have h2 : (t i + 1) * N i = (t' i + 1) * N i := by omega
    have := Nat.eq_of_mul_eq_mul_right (hN i) h2
    omega
  rw [shiftBox, Finset.card_image_of_injOn hinj, card_box]
  simp

/-- Shifted index sets attached to distinct offsets `j < N` are disjoint. -/
lemma disjoint_shiftBox {d : ℕ} (K : ℕ) {N j j' : Fin d → ℕ} (hj : ∀ i, j i < N i)
    (hj' : ∀ i, j' i < N i) (h : j ≠ j') :
    Disjoint (shiftBox K N j) (shiftBox K N j') := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨t', -, ht'⟩ := Finset.mem_image.1 hu'
  refine h (funext fun i ↦ ?_)
  have hi : (t i + 1) * N i + j i = (t' i + 1) * N i + j' i := (congrFun ht' i).symm
  have hmod := congrArg (· % N i) hi
  simpa [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (hj i), Nat.mod_eq_of_lt (hj' i)]
    using hmod

/-- Translating the basic shifted index set by `j` gives the shifted index set at `j`. -/
lemma image_add_shiftBox {d : ℕ} (K : ℕ) (N j : Fin d → ℕ) :
    (shiftBox K N 0).image (fun k ↦ k + j) = shiftBox K N j := by
  have h : ((fun k ↦ k + j) ∘ fun (t : Fin d → ℕ) i ↦ (t i + 1) * N i + (0 : Fin d → ℕ) i)
      = fun (t : Fin d → ℕ) i ↦ (t i + 1) * N i + j i := by
    funext t i
    simp
  rw [shiftBox, shiftBox, Finset.image_image, h]

/-- Every element of a shifted index set stays in the box of side `2 ^ K * N` after
subtracting an index `j < N`. -/
lemma exists_add_eq_of_mem_shiftBox {d : ℕ} (K : ℕ) {N j' j u : Fin d → ℕ}
    (hj' : ∀ i, j' i < N i) (hj : ∀ i, j i < N i) (hu : u ∈ shiftBox K N j') :
    ∃ m ∈ box fun i ↦ 2 ^ K * N i, m + j = u := by
  have hub : ∀ i, u i < 2 ^ K * N i := fun i ↦ mem_box.1 (shiftBox_subset K hj' hu) i
  have hlb : ∀ i, N i ≤ u i := by
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hu
    intro i
    show N i ≤ (t i + 1) * N i + j' i
    have h1 : 1 * N i ≤ (t i + 1) * N i := Nat.mul_le_mul (by omega) le_rfl
    omega
  refine ⟨fun i ↦ u i - j i, mem_box.2 fun i ↦ ?_, funext fun i ↦ ?_⟩
  · have h1 := hub i
    have h2 := hlb i
    have h3 := hj i
    omega
  · have h2 := hlb i
    have h3 := hj i
    simp only [Pi.add_apply]
    omega

namespace NatAction

variable {d : ℕ} (A : NatAction μ d)

/-- The union of the levels of `B` indexed by a finite set of multi-indices. -/
def levels (s : Finset (Fin d → ℕ)) (B : Set X) : Set X :=
  ⋃ k ∈ s, A.f k ⁻¹' B

/-- A sub-union of levels of a measurable set is measurable. -/
lemma measurableSet_levels {s : Finset (Fin d → ℕ)} {B : Set X} (hB : MeasurableSet B) :
    MeasurableSet (A.levels s B) :=
  Finset.measurableSet_biUnion _ fun k _ ↦ A.measurable k hB

/-- The measure of a sub-union of the levels of an admissible tower. -/
lemma measure_levels {m : Fin d → ℕ} {B : Set X} (hB : A.Admissible m B)
    {s : Finset (Fin d → ℕ)} (hs : s ⊆ box m) : μ (A.levels s B) = s.card * μ B := by
  have hd : (↑s : Set (Fin d → ℕ)).PairwiseDisjoint fun k ↦ A.f k ⁻¹' B :=
    fun k hk l hl hkl ↦ hB.2 k (hs (by simpa using hk)) l (hs (by simpa using hl)) hkl
  have hm : ∀ k ∈ s, MeasurableSet (A.f k ⁻¹' B) := fun k _ ↦ A.measurable k hB.1
  rw [levels, measure_biUnion_finset hd hm]
  simp only [A.measure_preimage _ hB.1, Finset.sum_const, nsmul_eq_mul]

/-- Sub-unions of levels over disjoint index sets are disjoint. -/
lemma disjoint_levels {m : Fin d → ℕ} {B : Set X} (hB : A.Admissible m B)
    {s t : Finset (Fin d → ℕ)} (hs : s ⊆ box m) (ht : t ⊆ box m) (hst : Disjoint s t) :
    Disjoint (A.levels s B) (A.levels t B) := by
  rw [Set.disjoint_left]
  rintro x hx hx'
  simp only [levels, Set.mem_iUnion, Set.mem_preimage, exists_prop] at hx hx'
  obtain ⟨k, hk, hxk⟩ := hx
  obtain ⟨l, hl, hxl⟩ := hx'
  exact Set.disjoint_left.1
    (hB.2 k (hs hk) l (ht hl) fun h ↦ Finset.disjoint_left.1 hst hk (h ▸ hl)) hxk hxl

/-- Pulling a sub-union of levels back translates the index set. -/
lemma preimage_levels (j : Fin d → ℕ) (s : Finset (Fin d → ℕ)) (B : Set X) :
    A.f j ⁻¹' A.levels s B = A.levels (s.image fun k ↦ k + j) B := by
  simp only [levels, Set.preimage_iUnion, Finset.set_biUnion_finset_image,
    A.preimage_preimage]

/-- The union of two admissible sets whose levels do not meet is admissible. -/
lemma Admissible.union {n : Fin d → ℕ} {B C : Set X} (hB : A.Admissible n B)
    (hC : A.Admissible n C)
    (h : ∀ i ∈ box n, ∀ j ∈ box n, Disjoint (A.f i ⁻¹' C) (A.f j ⁻¹' B)) :
    A.Admissible n (B ∪ C) := by
  refine ⟨hB.1.union hC.1, fun k hk l hl hkl ↦ ?_⟩
  rw [Set.preimage_union, Set.preimage_union, Set.disjoint_union_left,
    Set.disjoint_union_right, Set.disjoint_union_right]
  exact ⟨⟨hB.2 k hk l hl hkl, (h l hl k hk).symm⟩, ⟨h k hk l hl, hC.2 k hk l hl hkl⟩⟩

/-- The set of measures of `N`-towers. -/
def towerMeasures (N : Fin d → ℕ) : Set ℝ :=
  {r : ℝ | ∃ B : Set X, A.Admissible N B ∧ r = (μ (A.tower N B)).toReal}

/-- The empty base shows that `0` is a tower measure. -/
lemma zero_mem_towerMeasures (N : Fin d → ℕ) : (0 : ℝ) ∈ A.towerMeasures N :=
  ⟨∅, ⟨MeasurableSet.empty, fun k _ l _ _ ↦ by simp⟩, by simp [tower]⟩

/-- The set of tower measures is nonempty. -/
lemma towerMeasures_nonempty (N : Fin d → ℕ) : (A.towerMeasures N).Nonempty :=
  ⟨0, A.zero_mem_towerMeasures N⟩

/-- The set of tower measures is bounded above by `1`. -/
lemma towerMeasures_bddAbove [IsProbabilityMeasure μ] (N : Fin d → ℕ) :
    BddAbove (A.towerMeasures N) := by
  refine ⟨1, ?_⟩
  rintro r ⟨B, -, rfl⟩
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one

/-- The supremum of the tower measures is nonnegative. -/
lemma sSup_towerMeasures_nonneg [IsProbabilityMeasure μ] (N : Fin d → ℕ) :
    0 ≤ sSup (A.towerMeasures N) :=
  le_csSup (A.towerMeasures_bddAbove N) (A.zero_mem_towerMeasures N)

/-- The supremum of the tower measures is at most `1`. -/
lemma sSup_towerMeasures_le_one [IsProbabilityMeasure μ] (N : Fin d → ℕ) :
    sSup (A.towerMeasures N) ≤ 1 :=
  csSup_le (A.towerMeasures_nonempty N) <| by
    rintro r ⟨B, -, rfl⟩
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one

/-- **The key step of Theorem 1.2.**  Fix a box `N` with positive sides and a refinement
factor `2 ^ K`.  Out of any `2 ^ K * N`-admissible set `B₀` one builds an `N`-admissible set
whose tower keeps all but a `d * 2 ^ (-K)` fraction of the tower of `B₀` (the sub-union `D`,
indexed by `shiftBox`) and, by Lemma 2.4 applied in the complement, gains a further
`2 ^ (-d)` fraction of what is left over. -/
lemma sSup_towerMeasures_ge [IsProbabilityMeasure μ]
    [HasCountableSeparatingOn X MeasurableSet univ] (hfree : A.Free) {N : Fin d → ℕ}
    (hN : ∀ i, 0 < N i) (K : ℕ) {B₀ : Set X} (hB₀ : A.Admissible (fun i ↦ 2 ^ K * N i) B₀)
    {δ : ℝ} (hδ : 0 < δ) :
    (1 - (μ (A.tower (fun i ↦ 2 ^ K * N i) B₀)).toReal) / 2 ^ d - δ
        + (1 - d / 2 ^ K) * (μ (A.tower (fun i ↦ 2 ^ K * N i) B₀)).toReal
      ≤ sSup (A.towerMeasures N) := by
  classical
  have hz : ∀ i, (0 : Fin d → ℕ) i < N i := fun i ↦ hN i
  have hTmeas : MeasurableSet (A.tower (fun i ↦ 2 ^ K * N i) B₀) := A.measurableSet_tower hB₀.1
  obtain ⟨N', B₁, hB₁, hB₁sub, hB₁ge⟩ :=
    A.exists_admissible_tower_ge hfree N hN hTmeas.compl hδ
  set D : Set X := A.f N' ⁻¹' A.levels (shiftBox K N 0) B₀ with hD
  have hDmeas : MeasurableSet D := A.measurable N' (A.measurableSet_levels hB₀.1)
  have hlev : ∀ j : Fin d → ℕ, A.f j ⁻¹' D = A.f N' ⁻¹' A.levels (shiftBox K N j) B₀ := by
    intro j
    calc A.f j ⁻¹' D = A.f (N' + j) ⁻¹' A.levels (shiftBox K N 0) B₀ := by
          rw [hD, A.preimage_preimage]
      _ = A.f N' ⁻¹' (A.f j ⁻¹' A.levels (shiftBox K N 0) B₀) := by
          rw [A.preimage_preimage, add_comm]
      _ = A.f N' ⁻¹' A.levels (shiftBox K N j) B₀ := by
          rw [A.preimage_levels, image_add_shiftBox]
  have hDadm : A.Admissible N D := by
    refine ⟨hDmeas, fun k hk l hl hkl ↦ ?_⟩
    rw [hlev k, hlev l]
    exact Disjoint.preimage _ (A.disjoint_levels hB₀ (shiftBox_subset K (mem_box.1 hk))
      (shiftBox_subset K (mem_box.1 hl))
      (disjoint_shiftBox K (mem_box.1 hk) (mem_box.1 hl) hkl))
  have hcross : ∀ i ∈ box N, ∀ j ∈ box N, Disjoint (A.f i ⁻¹' D) (A.f j ⁻¹' B₁) := by
    intro i hi j hj
    rw [hlev i, Set.disjoint_left]
    intro z hz₁ hz₂
    simp only [Set.mem_preimage, levels, Set.mem_iUnion, exists_prop] at hz₁
    obtain ⟨u, hu, hzu⟩ := hz₁
    obtain ⟨m, hm, hmu⟩ := exists_add_eq_of_mem_shiftBox K (mem_box.1 hi) (mem_box.1 hj) hu
    have hnot : A.f N' (A.f j z) ∉ A.tower (fun i ↦ 2 ^ K * N i) B₀ := hB₁sub hz₂
    refine hnot (A.preimage_subset_tower hm B₀ ?_)
    show A.f m (A.f N' (A.f j z)) ∈ B₀
    have e : m + (N' + j) = u + N' := by
      rw [← hmu]
      abel
    have h1 : A.f m (A.f N' (A.f j z)) = A.f u (A.f N' z) :=
      calc A.f m (A.f N' (A.f j z)) = A.f (m + (N' + j)) z := by
            rw [A.f_apply_add, A.f_apply_add]
        _ = A.f (u + N') z := by rw [e]
        _ = A.f u (A.f N' z) := A.f_apply_add _ _ _
    rw [h1]
    exact hzu
  have hadm : A.Admissible N (B₁ ∪ D) := Admissible.union A hB₁ hDadm hcross
  have hdisjBD : Disjoint B₁ D := by
    have h0 : (0 : Fin d → ℕ) ∈ box N := mem_box.2 hz
    have h := hcross 0 h0 0 h0
    rw [A.f_zero] at h
    simpa using h.symm
  have hmeasD : μ D = (((2 ^ K - 1) ^ d : ℕ) : ℝ≥0∞) * μ B₀ := by
    rw [hD, A.measure_preimage _ (A.measurableSet_levels hB₀.1),
      A.measure_levels hB₀ (shiftBox_subset K hz), card_shiftBox K hN 0]
  have hTreal : (μ (A.tower (fun i ↦ 2 ^ K * N i) B₀)).toReal
      = ((2 : ℝ) ^ K) ^ d * (((box N).card : ℝ) * (μ B₀).toReal) := by
    rw [A.measure_tower hB₀, card_box_pow_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    push_cast
    ring
  have hone : (1 : ℕ) ≤ 2 ^ K := Nat.one_le_pow _ _ (by norm_num)
  have hTDreal : (μ (A.tower N D)).toReal
      = ((box N).card : ℝ) * (((2 : ℝ) ^ K - 1) ^ d * (μ B₀).toReal) := by
    rw [A.measure_tower hDadm, hmeasD, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_mul, ENNReal.toReal_natCast]
    push_cast [Nat.cast_sub hone]
    ring
  have hber : 1 - (d : ℝ) / 2 ^ K ≤ (1 - 1 / 2 ^ K) ^ d := by
    have hx : (0 : ℝ) < 2 ^ K := by positivity
    have hle1 : (1 : ℝ) / 2 ^ K ≤ 1 := by
      rw [div_le_one hx]
      exact one_le_pow₀ (by norm_num)
    calc 1 - (d : ℝ) / 2 ^ K = 1 + (d : ℝ) * -(1 / 2 ^ K) := by ring
      _ ≤ (1 + -(1 / (2 : ℝ) ^ K)) ^ d := one_add_mul_le_pow (by linarith) d
      _ = (1 - 1 / 2 ^ K) ^ d := by ring_nf
  have hpow : (1 - (d : ℝ) / 2 ^ K) * ((2 : ℝ) ^ K) ^ d ≤ ((2 : ℝ) ^ K - 1) ^ d := by
    have hx : (0 : ℝ) < 2 ^ K := by positivity
    have h2 : ((2 : ℝ) ^ K - 1) ^ d = (1 - 1 / 2 ^ K) ^ d * ((2 : ℝ) ^ K) ^ d := by
      rw [← mul_pow]
      congr 1
      field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_right hber (by positivity)
  have hDlow : (1 - (d : ℝ) / 2 ^ K) * (μ (A.tower (fun i ↦ 2 ^ K * N i) B₀)).toReal
      ≤ (μ (A.tower N D)).toReal := by
    rw [hTreal, hTDreal]
    have hPb : (0 : ℝ) ≤ ((box N).card : ℝ) * (μ B₀).toReal := by positivity
    calc (1 - (d : ℝ) / 2 ^ K) * (((2 : ℝ) ^ K) ^ d * (((box N).card : ℝ) * (μ B₀).toReal))
        = ((1 - (d : ℝ) / 2 ^ K) * ((2 : ℝ) ^ K) ^ d)
            * (((box N).card : ℝ) * (μ B₀).toReal) := by ring
      _ ≤ ((2 : ℝ) ^ K - 1) ^ d * (((box N).card : ℝ) * (μ B₀).toReal) :=
          mul_le_mul_of_nonneg_right hpow hPb
      _ = ((box N).card : ℝ) * (((2 : ℝ) ^ K - 1) ^ d * (μ B₀).toReal) := by ring
  have hcompl : (μ (A.tower (fun i ↦ 2 ^ K * N i) B₀)ᶜ).toReal
      = 1 - (μ (A.tower (fun i ↦ 2 ^ K * N i) B₀)).toReal := by
    rw [prob_compl_eq_one_sub hTmeas,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  have hsum : μ (A.tower N (B₁ ∪ D)) = μ (A.tower N B₁) + μ (A.tower N D) := by
    rw [A.measure_tower hadm, A.measure_tower hB₁, A.measure_tower hDadm,
      measure_union hdisjBD hDmeas, mul_add]
  have hle : (μ (A.tower N (B₁ ∪ D))).toReal ≤ sSup (A.towerMeasures N) :=
    le_csSup (A.towerMeasures_bddAbove N) ⟨B₁ ∪ D, hadm, rfl⟩
  rw [hsum, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hle
  rw [hcompl] at hB₁ge
  linarith

/-- **AC Theorem 1.2.** -/
theorem exists_tower [IsProbabilityMeasure μ]
    [HasCountableSeparatingOn X MeasurableSet univ] (hfree : A.Free) (n : Fin d → ℕ)
    (hn : ∀ i, 0 < n i) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : Set X, A.Admissible n B ∧ 1 - ε ≤ (μ (A.tower n B)).toReal := by
  have hbdd : BddBelow (Set.range fun K : ℕ ↦ sSup (A.towerMeasures fun i ↦ 2 ^ K * n i)) :=
    ⟨0, by rintro _ ⟨K, rfl⟩; exact A.sSup_towerMeasures_nonneg _⟩
  set κ : ℝ := ⨅ K : ℕ, sSup (A.towerMeasures fun i ↦ 2 ^ K * n i) with hκdef
  have hκle : ∀ K : ℕ, κ ≤ sSup (A.towerMeasures fun i ↦ 2 ^ K * n i) :=
    fun K ↦ ciInf_le hbdd K
  have hκ0 : 0 ≤ κ := le_ciInf fun K ↦ A.sSup_towerMeasures_nonneg _
  have hκ1 : κ ≤ 1 := (hκle 0).trans (A.sSup_towerMeasures_le_one _)
  obtain ⟨v, hv0, hv1, hvd⟩ : ∃ v : ℝ, 0 < v ∧ v ≤ 1 ∧ ∀ x : ℝ, x / 2 ^ d = x * v := by
    refine ⟨((2 : ℝ) ^ d)⁻¹, by positivity, ?_, fun x ↦ by ring⟩
    rw [inv_le_one₀ (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hstep : ∀ δ : ℝ, 0 < δ → (1 - κ) * v ≤ 3 * δ := by
    intro δ hδ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (d : ℝ) / 2 ^ m ≤ δ := by
      obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((d : ℝ) / δ) (by norm_num : (1 : ℝ) < 2)
      refine ⟨m, ?_⟩
      rw [div_lt_iff₀ hδ] at hm
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ m)]
      linarith
    obtain ⟨θ, hθ0, hθδ, hθe⟩ : ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ δ ∧ (d : ℝ) / 2 ^ m = θ :=
      ⟨_, by positivity, hm, rfl⟩
    have hkey : ∀ k : ℕ, (1 - κ) * v + κ - 3 * δ ≤
        sSup (A.towerMeasures fun i ↦ 2 ^ k * n i) := by
      intro k
      have hNpos : ∀ i, 0 < 2 ^ k * n i := fun i ↦
        Nat.mul_pos (pow_pos (by norm_num) k) (hn i)
      have hMeq : (fun i ↦ 2 ^ m * (2 ^ k * n i)) = fun i ↦ 2 ^ (m + k) * n i := by
        funext i
        rw [pow_add, mul_assoc]
      have hsSup : κ ≤ sSup (A.towerMeasures fun i ↦ 2 ^ m * (2 ^ k * n i)) := by
        rw [hMeq]
        exact hκle (m + k)
      obtain ⟨r, ⟨B₀, hB₀, rfl⟩, hr⟩ := exists_lt_of_lt_csSup (A.towerMeasures_nonempty _)
        (show κ - δ < sSup (A.towerMeasures fun i ↦ 2 ^ m * (2 ^ k * n i)) by linarith)
      have hβ0 : (0 : ℝ) ≤ (μ (A.tower (fun i ↦ 2 ^ m * (2 ^ k * n i)) B₀)).toReal :=
        ENNReal.toReal_nonneg
      have hβ1 : (μ (A.tower (fun i ↦ 2 ^ m * (2 ^ k * n i)) B₀)).toReal ≤ 1 := by
        have h : μ (A.tower (fun i ↦ 2 ^ m * (2 ^ k * n i)) B₀) ≤ 1 := prob_le_one
        simpa using ENNReal.toReal_mono ENNReal.one_ne_top h
      have hkeylem := A.sSup_towerMeasures_ge hfree hNpos m hB₀ hδ
      rw [hvd, hθe] at hkeylem
      have h1 : (0 : ℝ) ≤ ((μ (A.tower (fun i ↦ 2 ^ m * (2 ^ k * n i)) B₀)).toReal - κ + δ)
          * (1 - v) := mul_nonneg (by linarith) (by linarith)
      have h2 : (0 : ℝ) ≤ (δ - θ)
          * (μ (A.tower (fun i ↦ 2 ^ m * (2 ^ k * n i)) B₀)).toReal :=
        mul_nonneg (by linarith) hβ0
      have h3 : (0 : ℝ) ≤ δ * (1 - (μ (A.tower (fun i ↦ 2 ^ m * (2 ^ k * n i)) B₀)).toReal) :=
        mul_nonneg hδ.le (by linarith)
      have h4 : (0 : ℝ) ≤ δ * v := mul_nonneg hδ.le hv0.le
      linarith
    have hinf : (1 - κ) * v + κ - 3 * δ ≤ κ := le_ciInf hkey
    linarith
  have hκ : (1 : ℝ) ≤ κ := by
    rcases le_or_gt 1 κ with h | hcon
    · exact h
    · exfalso
      have hpos : 0 < (1 - κ) * v := mul_pos (by linarith) hv0
      have h := hstep ((1 - κ) * v / 6) (by linarith)
      linarith
  have hfinal : (1 : ℝ) ≤ sSup (A.towerMeasures n) := by
    have h := hκle 0
    simp only [pow_zero, one_mul] at h
    linarith
  obtain ⟨r, ⟨B, hB, rfl⟩, hr⟩ := exists_lt_of_lt_csSup (A.towerMeasures_nonempty n)
    (show 1 - ε < sSup (A.towerMeasures n) by linarith)
  exact ⟨B, hB, hr.le⟩

end NatAction

end RokhlinTower

end

/-! ### Upstream module `Jsp827/Arith.lean` -/

/-!
# Arithmetic of smooth multi-indices

For a list of primes `p : Fin d → ℕ` and an exponent vector `e`, `gval p e = ∏ p i ^ e i`.
Facts needed for the Marstrand counterexample (discrete log-coordinate version):

* if the primes `p i` include every prime `≤ 2^J` and every exponent `e i ≥ J`, then every
  `n` with `1 ≤ n ≤ 2^J` divides `gval p e`, and `n = gval p a` for the exponent vector
  `a = fun i => (Nat.factorization n) (p i)` with `a ≤ e` componentwise;
* `gval p` is injective (unique factorization);
* the `Nat.log 2` sandwich: if `2^{j-1} < n ≤ 2^j`, `n ∣ g` and `L = Nat.log 2 g` then
  `Nat.log 2 (g / n) ∈ {L - j, L - j + 1}` (for `1 ≤ j ≤ L`).
-/

/-- The smooth number with exponent vector `e`. -/
def gval {d : ℕ} (p : Fin d → ℕ) (e : Fin d → ℕ) : ℕ := ∏ i, p i ^ e i

lemma gval_pos {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, 0 < p i) (e : Fin d → ℕ) : 0 < gval p e :=
  Finset.prod_pos fun i _ ↦ pow_pos (hp i) (e i)

/-- The exponent vector of `n` with respect to the primes `p`. -/
def expVec {d : ℕ} (p : Fin d → ℕ) (n : ℕ) : Fin d → ℕ := fun i => n.factorization (p i)

/-- The multiplicity of a prime `q` in `gval p e`, as a sum over the indices `i` with
`p i = q`. -/
private lemma factorization_gval {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, (p i).Prime)
    (e : Fin d → ℕ) (q : ℕ) :
    (gval p e).factorization q = ∑ i, if p i = q then e i else 0 := by
  rw [gval, Nat.factorization_prod fun i _ ↦ pow_ne_zero (e i) (hp i).ne_zero]
  rw [Finset.sum_apply']
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Nat.factorization_pow, Finsupp.smul_apply, (hp i).factorization,
    Finsupp.single_apply]
  by_cases h : p i = q <;> simp [h]

/-- The multiplicity of `p j` in `gval p e` is `e j`. -/
private lemma factorization_gval_self {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (e : Fin d → ℕ) (j : Fin d) :
    (gval p e).factorization (p j) = e j := by
  rw [factorization_gval hp e (p j)]
  simp [hinj.eq_iff]

/-- A prime outside the range of `p` does not divide `gval p e`. -/
private lemma factorization_gval_of_notMem {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, (p i).Prime)
    (e : Fin d → ℕ) {q : ℕ} (hq : ∀ i, p i ≠ q) : (gval p e).factorization q = 0 := by
  rw [factorization_gval hp e q]
  exact Finset.sum_eq_zero fun i _ ↦ by simp [hq i]

/-- If every prime factor of `n` is among the `p i` (which are distinct primes), then
`n = gval p (expVec p n)`. -/
lemma gval_expVec {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    {n : ℕ} (hn : 0 < n) (hcover : ∀ q, q.Prime → q ∣ n → ∃ i, p i = q) :
    gval p (expVec p n) = n := by
  have hg : gval p (expVec p n) ≠ 0 := (gval_pos (fun i ↦ (hp i).pos) _).ne'
  refine Nat.eq_of_factorization_eq hg hn.ne' fun q ↦ ?_
  by_cases hq : ∃ i, p i = q
  · obtain ⟨i, rfl⟩ := hq
    exact factorization_gval_self hp hinj _ i
  · simp only [not_exists] at hq
    rw [factorization_gval_of_notMem hp _ hq]
    rcases Nat.eq_zero_or_pos (n.factorization q) with h | h
    · exact h.symm
    have hqp : q.Prime := by
      by_contra hqp
      simp [Nat.factorization_eq_zero_of_not_prime n hqp] at h
    have hqd : q ∣ n := by
      by_contra hqd
      simp [Nat.factorization_eq_zero_of_not_dvd hqd] at h
    obtain ⟨i, hi⟩ := hcover q hqp hqd
    exact absurd hi (hq i)

/-- Every `n ≤ 2^J` is `p`-smooth with exponents `≤ J` when the `p i` cover all primes
`≤ 2^J`. -/
lemma expVec_le_of_le_pow {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, (p i).Prime)
    {J n : ℕ} (hn : n ≤ 2 ^ J) (i : Fin d) : expVec p n i ≤ J := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp [expVec]
  have hdvd : p i ^ n.factorization (p i) ∣ n := Nat.ordProj_dvd n (p i)
  have h1 : (2 : ℕ) ^ n.factorization (p i) ≤ p i ^ n.factorization (p i) :=
    Nat.pow_le_pow_left (hp i).two_le _
  have h2 : p i ^ n.factorization (p i) ≤ n := Nat.le_of_dvd hn0 hdvd
  have h3 : (2 : ℕ) ^ n.factorization (p i) ≤ 2 ^ J := le_trans h1 (le_trans h2 hn)
  exact (Nat.pow_le_pow_iff_right (le_refl 2)).mp h3

/-- The `Nat.log 2` sandwich for the quotient by a dyadic-range divisor. -/
lemma log_div_mem {g n j : ℕ} (hg : 0 < g) (hn : n ∣ g) (hj : 1 ≤ j)
    (hlo : 2 ^ (j - 1) < n) (hhi : n ≤ 2 ^ j) (hjL : j ≤ Nat.log 2 g) :
    Nat.log 2 (g / n) = Nat.log 2 g - j ∨ Nat.log 2 (g / n) = Nat.log 2 g - j + 1 := by
  set L := Nat.log 2 g with hL
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hlo
  have hgn : n * (g / n) = g := Nat.mul_div_cancel' hn
  have hm0 : 0 < g / n := Nat.div_pos (Nat.le_of_dvd hg hn) hn0
  have hlow : 2 ^ L ≤ g := Nat.pow_log_le_self 2 hg.ne'
  have hhigh : g < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) g
  have key1 : 2 ^ (L - j) ≤ g / n := by
    have h2 : (2 : ℕ) ^ j * 2 ^ (L - j) = 2 ^ L := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : n * 2 ^ (L - j) ≤ n * (g / n) := by
      rw [hgn]
      calc n * 2 ^ (L - j) ≤ 2 ^ j * 2 ^ (L - j) := Nat.mul_le_mul_right _ hhi
        _ = 2 ^ L := h2
        _ ≤ g := hlow
    exact Nat.le_of_mul_le_mul_left h3 hn0
  have key2 : g / n < 2 ^ (L - j + 2) := by
    have h2 : (2 : ℕ) ^ (j - 1) * 2 ^ (L - j + 2) = 2 ^ (L + 1) := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : 2 ^ (j - 1) * (g / n) < 2 ^ (j - 1) * 2 ^ (L - j + 2) := by
      rw [h2]
      calc 2 ^ (j - 1) * (g / n) < n * (g / n) := mul_lt_mul_of_pos_right hlo hm0
        _ = g := hgn
        _ < 2 ^ (L + 1) := hhigh
    exact Nat.lt_of_mul_lt_mul_left h3
  have hle1 : L - j ≤ Nat.log 2 (g / n) := Nat.le_log_of_pow_le (by norm_num) key1
  have hle2 : Nat.log 2 (g / n) < L - j + 2 := Nat.log_lt_of_lt_pow hm0.ne' key2
  omega

/-! ### Upstream module `Jsp827/Circle.lean` -/

section
/-!
# The multiplicative action on the unit circle

For primes `p : Fin d → ℕ`, the maps `x ↦ (∏ p i ^ e i) • x` on `UnitAddCircle` form a
free measure-preserving `ℕ^d`-action (`RokhlinTower.NatAction`).  The hypothesis
`HasCountableSeparatingOn UnitAddCircle MeasurableSet univ` needed by the tower theorem
is already available from Mathlib, since the circle is a second-countable T₀ Borel space.
-/

open _root_.MeasureTheory _root_.Set

/-- The smooth number with exponent vector `e` (duplicated here to keep this file
independent of `Arith.lean`; the two definitions are definitionally equal). -/
def gvalC {d : ℕ} (p : Fin d → ℕ) (e : Fin d → ℕ) : ℕ := ∏ i, p i ^ e i

/-- The multiplier attached to the zero exponent vector is `1`. -/
@[simp] lemma gvalC_zero {d : ℕ} (p : Fin d → ℕ) : gvalC p 0 = 1 := by
  simp [gvalC]

/-- The multipliers are multiplicative in the exponent vector. -/
lemma gvalC_add {d : ℕ} (p : Fin d → ℕ) (m n : Fin d → ℕ) :
    gvalC p (m + n) = gvalC p m * gvalC p n := by
  simp [gvalC, pow_add, Finset.prod_mul_distrib]

/-- Positive primes give positive multipliers. -/
lemma gvalC_pos {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, 0 < p i) (e : Fin d → ℕ) :
    0 < gvalC p e :=
  Finset.prod_pos fun i _ ↦ pow_pos (hp i) _

/-- For distinct primes the exponent vector is recovered from the multiplier, so the
multiplier map is injective. -/
lemma gvalC_injective {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) : Function.Injective (gvalC p) := by
  have key : ∀ e : Fin d → ℕ, ∀ j : Fin d, (gvalC p e).factorization (p j) = e j := by
    intro e j
    rw [gvalC, Nat.factorization_prod fun i _ ↦ (pow_ne_zero _ (hp i).ne_zero)]
    simp only [Nat.factorization_pow, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, (hp _).factorization, Finsupp.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hinj.ne hij]
    · simp
  intro k l h
  funext j
  rw [← key k j, ← key l j, h]

/-- Distinct multipliers agree only on a torsion set, which is null. -/
lemma measure_setOf_nsmul_eq_nsmul {a b : ℕ} (hab : a ≠ b) :
    volume {x : UnitAddCircle | a • x = b • x} = 0 := by
  have : NullSingletonClass (volume : Measure UnitAddCircle) :=
    ⟨fun x ↦ by rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]; simp⟩
  wlog h : b < a generalizing a b
  · simpa only [eq_comm] using this hab.symm (lt_of_le_of_ne (not_lt.mp h) hab)
  obtain ⟨c, hc, rfl⟩ : ∃ c, 0 < c ∧ a = b + c := ⟨a - b, by omega, by omega⟩
  have hset : {x : UnitAddCircle | (b + c) • x = b • x}
      = {x : UnitAddCircle | c • x = 0} := by
    ext x
    simp [add_nsmul, add_eq_left]
  rw [hset]
  exact (AddCircle.finite_torsion (1 : ℝ) hc).measure_zero _

/-- Multiplication by `gvalC p e` on the unit circle. -/
noncomputable def smoothAction {d : ℕ} (p : Fin d → ℕ) (hp : ∀ i, 0 < p i) :
    RokhlinTower.NatAction (volume : Measure UnitAddCircle) d where
  f e x := gvalC p e • x
  f_zero := by
    funext x
    simp
  f_add := by
    intro m n
    funext x
    simp [gvalC_add, mul_nsmul']
  measurePreserving := by
    intro n
    have h : ((gvalC p n : ℤ)) ≠ 0 := by
      exact_mod_cast (gvalC_pos hp n).ne'
    simpa only [natCast_zsmul] using
      MeasureTheory.Measure.measurePreserving_zsmul (volume : Measure UnitAddCircle) h

/-- Distinct exponent vectors give distinct multipliers, hence agree only on the finite
(torsion) set `{x | (g - g') • x = 0}`, which is null. -/
theorem smoothAction_free {d : ℕ} (p : Fin d → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) :
    (smoothAction p fun i => (hp i).pos).Free := by
  intro k l hkl
  exact measure_setOf_nsmul_eq_nsmul fun h ↦ hkl (gvalC_injective hp hinj h)

end

/-! ### Upstream module `Jsp827/Marstrand/Scale.lean` -/

section
/-!
# One scale of Marstrand's construction (discrete log-coordinate version)

Fix `J ≥ 3`, the list `p : Fin d → ℕ` of all primes `≤ 2^J` (distinct), a box side `N`
with `J ∣ N`, and a tower base `W` for the action `e ↦ gvalC p e • x` on the unit circle
with pairwise disjoint levels `level e = f e ⁻¹' W`, `e ∈ box (fun _ ↦ N)`.

* `L e := Nat.log 2 (gvalC p e)`; the *scale* of a level is `L e % J`.
* `badSet := ⋃ {level e : L e % J ∈ {0,1}}`  (this is `E` at this scale);
* `goodSet j₀ := ⋃ {level e : (∀ i, J ≤ e i) ∧ j₀ ≤ L e % J}`.

Counting claim: if `x ∈ level e` with `∀ i, J ≤ e i` and `j := L e % J ≥ 1`, then for every
`n ∈ (2^(j-1), 2^j]` we have `n • x ∈ badSet`, so at least half of the `n ≤ 2^j` visit
`badSet`.  Measure claims: `μ badSet ≤ 2 / J` and
`μ (goodSet j₀) ≥ (1 - ε) * (1 - J/N)^d * (1 - j₀/J)` when the tower has measure `≥ 1-ε`.
-/

open _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal

open RokhlinTower

attribute [local instance] Classical.propDecidable

variable {d : ℕ} (p : Fin d → ℕ) (hp : ∀ i, (p i).Prime)

/-- The action (abbreviation for readability). -/
noncomputable abbrev act : NatAction (volume : Measure UnitAddCircle) d :=
  smoothAction p fun i => (hp i).pos

/-- `Nat.log 2` of the multiplier of a level. -/
def L (e : Fin d → ℕ) : ℕ := Nat.log 2 (gvalC p e)

/-- The set of levels carrying the bad set at scale `J`. -/
def badIdx (J N : ℕ) : Finset (Fin d → ℕ) :=
  (box fun _ : Fin d => N).filter fun e => L p e % J = 0 ∨ L p e % J = 1

/-- The set of levels carrying the good set at scale `J` with threshold `j₀`. -/
def goodIdx (J N j₀ : ℕ) : Finset (Fin d → ℕ) :=
  (box fun _ : Fin d => N).filter fun e => (∀ i, J ≤ e i) ∧ j₀ ≤ L p e % J

/-- The bad set: union of the bad levels over the base `W`. -/
def badSet (J N : ℕ) (W : Set UnitAddCircle) : Set UnitAddCircle :=
  ⋃ e ∈ badIdx p J N, (act p hp).f e ⁻¹' W

/-- The good set. -/
def goodSet (J N j₀ : ℕ) (W : Set UnitAddCircle) : Set UnitAddCircle :=
  ⋃ e ∈ goodIdx p J N j₀, (act p hp).f e ⁻¹' W

/-- Hypothesis packaging the choice of primes: `p` enumerates exactly the primes `≤ 2^J`. -/
def PrimesUpTo (J : ℕ) : Prop :=
  Function.Injective p ∧ ∀ q : ℕ, q.Prime → q ≤ 2 ^ J → ∃ i, p i = q

/-- The action is multiplication by `gvalC p e`. -/
lemma act_apply (e : Fin d → ℕ) (x : UnitAddCircle) : (act p hp).f e x = gvalC p e • x := rfl

/-- `gvalC` agrees with `gval`. -/
lemma gvalC_eq_gval (e : Fin d → ℕ) : gvalC p e = gval p e := rfl

/-- **Counting claim (C′).**  For `x` in a good level, every `n` in the dyadic range
`(2^(j-1), 2^j]` (with `j = L e % J`) sends `x` into the bad set. -/
theorem nsmul_mem_badSet {J N j₀ : ℕ} (hJ : 3 ≤ J) (hprimes : PrimesUpTo p J)
    {W : Set UnitAddCircle} {e : Fin d → ℕ} (he : e ∈ goodIdx p J N j₀) (hj₀ : 1 ≤ j₀)
    {x : UnitAddCircle} (hx : x ∈ (act p hp).f e ⁻¹' W) {n : ℕ}
    (hlo : 2 ^ (L p e % J - 1) < n) (hhi : n ≤ 2 ^ (L p e % J)) :
    n • x ∈ badSet p hp J N W := by
  classical
  rw [goodIdx, Finset.mem_filter] at he
  obtain ⟨hbox, hge, hj₀le⟩ := he
  set j : ℕ := L p e % J with hjdef
  have hj1 : 1 ≤ j := le_trans hj₀ hj₀le
  have hjJ : j < J := Nat.mod_lt _ (by omega)
  have h1le : (1 : ℕ) ≤ 2 ^ (j - 1) := Nat.one_le_two_pow
  have hn0 : 0 < n := lt_of_lt_of_le (by omega) hlo.le
  have hnJ : n ≤ 2 ^ J := hhi.trans (Nat.pow_le_pow_right (by norm_num) hjJ.le)
  set a : Fin d → ℕ := expVec p n with hadef
  have hga : gvalC p a = n := by
    rw [gvalC_eq_gval]
    exact gval_expVec hp hprimes.1 hn0 fun q hq hqd ↦
      hprimes.2 q hq ((Nat.le_of_dvd hn0 hqd).trans hnJ)
  have hale : ∀ i, a i ≤ e i := fun i ↦ (expVec_le_of_le_pow hp hnJ i).trans (hge i)
  have hsub : (e - a) + a = e := by
    funext i
    have := hale i
    simp only [Pi.add_apply, Pi.sub_apply]
    omega
  have key : (act p hp).f (e - a) (n • x) = (act p hp).f e x := by
    rw [← hga, ← act_apply p hp a x, ← NatAction.f_apply_add, hsub]
  have hmemW : n • x ∈ (act p hp).f (e - a) ⁻¹' W := by
    simp only [Set.mem_preimage, key]
    exact hx
  have hsplit : gvalC p (e - a) * n = gvalC p e := by
    rw [← hga, ← gvalC_add, hsub]
  have hg0 : 0 < gvalC p e := gvalC_pos (fun i ↦ (hp i).pos) e
  have hdvd : n ∣ gvalC p e := ⟨gvalC p (e - a), by rw [← hsplit, Nat.mul_comm]⟩
  have hdiv : gvalC p e / n = gvalC p (e - a) := by
    rw [← hsplit, Nat.mul_div_cancel _ hn0]
  have hjL : j ≤ L p e := Nat.mod_le _ _
  have hlog : L p (e - a) = L p e - j ∨ L p (e - a) = L p e - j + 1 := by
    have := log_div_mem (g := gvalC p e) (n := n) (j := j) hg0 hdvd hj1 hlo hhi hjL
    rwa [hdiv] at this
  have hmod : L p e - j = J * (L p e / J) := by
    have := Nat.div_add_mod (L p e) J
    omega
  have hbad : e - a ∈ badIdx p J N := by
    refine Finset.mem_filter.mpr ⟨mem_box.mpr fun i ↦ ?_, ?_⟩
    · have := (mem_box.mp hbox) i
      simp only [Pi.sub_apply]
      omega
    · rcases hlog with h | h
      · left
        rw [h, hmod, Nat.mul_mod_right]
      · right
        rw [h, hmod, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  exact Set.mem_biUnion hbad hmemW

/-- At least half of the multiples `1 ≤ n ≤ 2^j` of a good point visit the bad set. -/
theorem half_visits {J N j₀ : ℕ} (hJ : 3 ≤ J) (hprimes : PrimesUpTo p J)
    {W : Set UnitAddCircle} {e : Fin d → ℕ} (he : e ∈ goodIdx p J N j₀) (hj₀ : 1 ≤ j₀)
    {x : UnitAddCircle} (hx : x ∈ (act p hp).f e ⁻¹' W) :
    2 ^ (L p e % J - 1) ≤
      ((Finset.Icc 1 (2 ^ (L p e % J))).filter fun n => n • x ∈ badSet p hp J N W).card := by
  classical
  have hj1 : 1 ≤ L p e % J :=
    hj₀.trans (Finset.mem_filter.mp he).2.2
  set j : ℕ := L p e % J with hjdef
  have hsub : Finset.Ioc (2 ^ (j - 1)) (2 ^ j) ⊆
      (Finset.Icc 1 (2 ^ j)).filter fun n ↦ n • x ∈ badSet p hp J N W := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, hn.2⟩, ?_⟩
    · have : (1 : ℕ) ≤ 2 ^ (j - 1) := Nat.one_le_two_pow
      omega
    · exact nsmul_mem_badSet p hp hJ hprimes he hj₀ hx hn.1 hn.2
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ioc] at hcard
  have hpow : (2 : ℕ) ^ j = 2 * 2 ^ (j - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, pow_succ]
    ring
  omega

/-- Every residue `r < J` is realised by `s ↦ (s + c) % J` for some `s < J`. -/
lemma exists_add_mod_eq {J c r : ℕ} (hJ : 0 < J) (hr : r < J) : ∃ s, s < J ∧ (s + c) % J = r := by
  have h1 : J * (c / J) + c % J = c := Nat.div_add_mod c J
  have h2 : c % J < J := Nat.mod_lt _ hJ
  refine ⟨(r + (J - c % J)) % J, Nat.mod_lt _ hJ, ?_⟩
  rw [Nat.mod_add_mod]
  have h3 : r + (J - c % J) + c = J * (c / J + 1) + r := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [h3, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-- In an interval `[A, B)` with endpoints divisible by `J`, every residue class of
`a ↦ (a + c) % J` has exactly `(B - A) / J` elements. -/
lemma card_filter_Ico_mod {J A B c r : ℕ} (hJ : 0 < J) (hAB : A ≤ B) (hA : J ∣ A) (hB : J ∣ B)
    (hr : r < J) :
    ((Finset.Ico A B).filter fun a ↦ (a + c) % J = r).card = (B - A) / J := by
  classical
  obtain ⟨s, hsJ, hs⟩ := exists_add_mod_eq hJ hr
  obtain ⟨u, hu⟩ := id hA
  obtain ⟨k, hk⟩ : ∃ k, B - A = J * k := Nat.dvd_sub hB hA
  have hkv : (B - A) / J = k := by rw [hk, Nat.mul_div_cancel_left _ hJ]
  rw [hkv, ← Finset.card_range k]
  refine Finset.card_nbij' (fun a ↦ (a - A) / J) (fun t ↦ A + J * t + s) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at ha ⊢
    exact Nat.div_lt_of_lt_mul (by omega)
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_range] at ht
    have hlt : J * t + s < J * k := by
      calc J * t + s < J * t + J := by omega
        _ = J * (t + 1) := by ring
        _ ≤ J * k := Nat.mul_le_mul_left _ (by omega)
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have hsplit : A + J * t + s + c = J * (u + t) + (s + c) := by rw [hu]; ring
    rw [hsplit, Nat.mul_add_mod, hs]
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at ha
    obtain ⟨⟨hAa, haB⟩, hmod⟩ := ha
    have hsa : a % J = s := by
      have h : a + c ≡ s + c [MOD J] := by rw [Nat.ModEq, hmod, hs]
      have h' := Nat.ModEq.add_right_cancel' c h
      rw [Nat.ModEq] at h'
      rw [h', Nat.mod_eq_of_lt hsJ]
    have haA : (a - A) % J = s := by
      have heq : J * u + (a - A) = a := by omega
      have hmm := Nat.mul_add_mod J u (a - A)
      rw [heq] at hmm
      rw [← hmm, hsa]
    have hd := Nat.div_add_mod (a - A) J
    simp only
    omega
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_range] at ht
    have hsimp : A + J * t + s - A = J * t + s := by omega
    simp only
    rw [hsimp, Nat.mul_add_div hJ, Nat.div_eq_of_lt hsJ, Nat.add_zero]

/-- Counting the elements of `[A, B)` whose residue satisfies `Q`. -/
lemma card_filter_Ico_residue {J A B c : ℕ} (hJ : 0 < J) (hAB : A ≤ B) (hA : J ∣ A) (hB : J ∣ B)
    (Q : ℕ → Prop) [DecidablePred Q] :
    ((Finset.Ico A B).filter fun a ↦ Q ((a + c) % J)).card
      = ((Finset.range J).filter Q).card * ((B - A) / J) := by
  classical
  have hmaps : ∀ a ∈ (Finset.Ico A B).filter fun a ↦ Q ((a + c) % J),
      (a + c) % J ∈ (Finset.range J).filter Q := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hJ), ha.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hterm : ∀ r ∈ (Finset.range J).filter Q,
      (((Finset.Ico A B).filter fun a ↦ Q ((a + c) % J)).filter
        fun a ↦ (a + c) % J = r).card = (B - A) / J := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    rw [Finset.filter_filter]
    have heq : ((Finset.Ico A B).filter fun a ↦ Q ((a + c) % J) ∧ (a + c) % J = r)
        = (Finset.Ico A B).filter fun a ↦ (a + c) % J = r := by
      ext a
      simp only [Finset.mem_filter]
      exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, h.2 ▸ hr.2, h.2⟩⟩
    rw [heq, card_filter_Ico_mod hJ hAB hA hB hr.1]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]

/-- `Nat.log 2` of `2 ^ a * m` splits off the power of two. -/
lemma log_two_pow_mul (a : ℕ) {m : ℕ} (hm : m ≠ 0) :
    Nat.log 2 (2 ^ a * m) = a + Nat.log 2 m := by
  induction a with
  | zero => simp
  | succ n ih =>
    have h : (2 : ℕ) ^ (n + 1) * m = 2 ^ n * m * 2 := by ring
    rw [h, Nat.log_mul_base (by norm_num) (Nat.mul_ne_zero (pow_ne_zero n two_ne_zero) hm), ih]
    omega

include hp in
/-- The scale splits as the exponent at the prime `2` plus the log of the remaining factor. -/
lemma L_eq_add {i₀ : Fin d} (hp2 : p i₀ = 2) (e : Fin d → ℕ) :
    L p e = e i₀ + Nat.log 2 (∏ i ∈ Finset.univ.erase i₀, p i ^ e i) := by
  have hpos : (0 : ℕ) < ∏ i ∈ Finset.univ.erase i₀, p i ^ e i :=
    Finset.prod_pos fun i _ ↦ pow_pos (hp i).pos _
  have hsplit : gvalC p e = 2 ^ e i₀ * ∏ i ∈ Finset.univ.erase i₀, p i ^ e i := by
    rw [gvalC, ← Finset.mul_prod_erase Finset.univ (fun i ↦ p i ^ e i) (Finset.mem_univ i₀), hp2]
  rw [L, hsplit, log_two_pow_mul _ hpos.ne']

include hp in
/-- Counting the exponent vectors in the cube `[A, B)^d` whose scale residue satisfies `Q`. -/
lemma card_filter_scale {i₀ : Fin d} (hp2 : p i₀ = 2) {J A B : ℕ} (hJ : 0 < J) (hAB : A ≤ B)
    (hA : J ∣ A) (hB : J ∣ B) (Q : ℕ → Prop) [DecidablePred Q] :
    ((Fintype.piFinset fun _ : Fin d ↦ Finset.Ico A B).filter fun e ↦ Q (L p e % J)).card
      = (∏ _i ∈ Finset.univ.erase i₀, (B - A)) *
          (((Finset.range J).filter Q).card * ((B - A) / J)) := by
  classical
  set S : Finset (Fin d → ℕ) :=
    (Fintype.piFinset fun _ : Fin d ↦ Finset.Ico A B).filter fun e ↦ Q (L p e % J) with hSdef
  set T : Finset (Fin d → ℕ) :=
    Fintype.piFinset (Function.update (fun _ : Fin d ↦ Finset.Ico A B) i₀ {0}) with hTdef
  have hmaps : ∀ e ∈ S, Function.update e i₀ 0 ∈ T := by
    intro e he
    rw [hSdef, Finset.mem_filter, Fintype.mem_piFinset] at he
    rw [hTdef, Fintype.mem_piFinset]
    intro i
    rcases eq_or_ne i i₀ with rfl | hi
    · simp
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
      exact he.1 i
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ b ∈ T, (S.filter fun e ↦ Function.update e i₀ 0 = b).card
      = ((Finset.range J).filter Q).card * ((B - A) / J) := by
    intro b hb
    rw [hTdef, Fintype.mem_piFinset] at hb
    have hb0 : b i₀ = 0 := by have := hb i₀; simpa using this
    have hbI : ∀ i, i ≠ i₀ → b i ∈ Finset.Ico A B := by
      intro i hi
      have := hb i
      rwa [Function.update_of_ne hi] at this
    set c : ℕ := Nat.log 2 (∏ i ∈ Finset.univ.erase i₀, p i ^ b i) with hcdef
    rw [← card_filter_Ico_residue (c := c) hJ hAB hA hB Q]
    refine Finset.card_nbij' (fun e ↦ e i₀) (fun a ↦ Function.update b i₀ a) ?_ ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_coe, Finset.mem_filter, hSdef, Fintype.mem_piFinset] at he
      obtain ⟨⟨hmem, hQ⟩, hupd⟩ := he
      have hrest : ∏ i ∈ Finset.univ.erase i₀, p i ^ e i
          = ∏ i ∈ Finset.univ.erase i₀, p i ^ b i :=
        Finset.prod_congr rfl fun i hi ↦ by
          rw [← hupd, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [L_eq_add p hp hp2 e, hrest, ← hcdef] at hQ
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hmem i₀, hQ⟩)
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at ha
      have hrest : ∏ i ∈ Finset.univ.erase i₀, p i ^ (Function.update b i₀ a) i
          = ∏ i ∈ Finset.univ.erase i₀, p i ^ b i :=
        Finset.prod_congr rfl fun i hi ↦ by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      have hmem : Function.update b i₀ a ∈ Fintype.piFinset fun _ : Fin d ↦ Finset.Ico A B := by
        rw [Fintype.mem_piFinset]
        intro i
        show Function.update b i₀ a i ∈ Finset.Ico A B
        rcases eq_or_ne i i₀ with rfl | hi
        · rw [Function.update_self]
          exact Finset.mem_Ico.mpr ha.1
        · rw [Function.update_of_ne hi]
          exact hbI i hi
      have hQa : Q (L p (Function.update b i₀ a) % J) := by
        rw [L_eq_add p hp hp2 (Function.update b i₀ a), hrest, Function.update_self, ← hcdef]
        exact ha.2
      have hback : Function.update (Function.update b i₀ a) i₀ 0 = b := by
        funext i
        rcases eq_or_ne i i₀ with rfl | hi
        · simp [hb0]
        · simp [Function.update_of_ne hi]
      exact Finset.mem_coe.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmem, hQa⟩, hback⟩)
    · intro e he
      simp only [Finset.mem_coe, Finset.mem_filter] at he
      funext i
      show Function.update b i₀ (e i₀) i = e i
      rcases eq_or_ne i i₀ with rfl | hi
      · rw [Function.update_self]
      · rw [Function.update_of_ne hi, ← he.2, Function.update_of_ne hi]
    · intro a _
      show Function.update b i₀ a i₀ = a
      rw [Function.update_self]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  congr 1
  have hcards : ∀ i : Fin d,
      (Function.update (fun _ : Fin d ↦ Finset.Ico A B) i₀ ({0} : Finset ℕ) i).card
        = Function.update (fun _ : Fin d ↦ B - A) i₀ 1 i := by
    intro i
    rcases eq_or_ne i i₀ with rfl | hi
    · simp
    · simp [Function.update_of_ne hi, Nat.card_Ico]
  rw [hTdef, Fintype.card_piFinset, Finset.prod_congr rfl fun i _ ↦ hcards i,
    Finset.prod_update_of_mem (Finset.mem_univ i₀), one_mul, ← Finset.erase_eq]

/-- The measure of a union of levels of an admissible tower. -/
lemma measure_levels {N : ℕ} {W : Set UnitAddCircle}
    (hW : (act p hp).Admissible (fun _ ↦ N) W) {S : Finset (Fin d → ℕ)}
    (hS : S ⊆ box fun _ : Fin d ↦ N) :
    volume (⋃ e ∈ S, (act p hp).f e ⁻¹' W) = S.card * volume W := by
  have hd : (↑S : Set (Fin d → ℕ)).PairwiseDisjoint fun k ↦ (act p hp).f k ⁻¹' W :=
    fun k hk l hl hkl ↦ hW.2 k (hS (by simpa using hk)) l (hS (by simpa using hl)) hkl
  have hm : ∀ k ∈ S, MeasurableSet ((act p hp).f k ⁻¹' W) :=
    fun k _ ↦ (act p hp).measurable k hW.1
  rw [measure_biUnion_finset hd hm]
  simp only [(act p hp).measure_preimage _ hW.1, Finset.sum_const, nsmul_eq_mul]

/-- Every set on the unit circle has finite measure. -/
lemma volume_ne_top (W : Set UnitAddCircle) : volume W ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (Set.subset_univ W))
  rw [UnitAddCircle.measure_univ]
  exact ENNReal.one_ne_top

/-- The number of levels in the box `[0, N)^d`. -/
lemma card_box_const (N : ℕ) : (box fun _ : Fin d ↦ N).card = N ^ d := by
  rw [card_box]
  simp

/-- **Measure claim for the bad set.** -/
theorem measure_badSet_le {J N : ℕ} (hJ : 0 < J) (hJN : J ∣ N) (hp2 : ∃ i, p i = 2)
    {W : Set UnitAddCircle} (hW : (act p hp).Admissible (fun _ => N) W) :
    (volume (badSet p hp J N W)).toReal ≤ 2 / J := by
  classical
  obtain ⟨i₀, hi₀⟩ := hp2
  have hbox : (box fun _ : Fin d ↦ N) = Fintype.piFinset fun _ : Fin d ↦ Finset.Ico 0 N := by
    simp only [box, Finset.range_eq_Ico]
  have hcardbad : (badIdx p J N).card
      = (∏ _i ∈ Finset.univ.erase i₀, (N - 0)) *
          (((Finset.range J).filter fun r ↦ r = 0 ∨ r = 1).card * ((N - 0) / J)) := by
    rw [badIdx, hbox]
    exact card_filter_scale p hp hi₀ hJ (Nat.zero_le N) (dvd_zero J) hJN
      (fun r ↦ r = 0 ∨ r = 1)
  simp only [Nat.sub_zero] at hcardbad
  have hcf : ((Finset.range J).filter fun r ↦ r = 0 ∨ r = 1).card ≤ 2 := by
    have hsub : (Finset.range J).filter (fun r ↦ r = 0 ∨ r = 1) ⊆ ({0, 1} : Finset ℕ) := by
      intro r hr
      have h := (Finset.mem_filter.mp hr).2
      simpa using h
    calc ((Finset.range J).filter fun r ↦ r = 0 ∨ r = 1).card
        ≤ ({0, 1} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 2 := by decide
  have hprodN : N ^ d = N * ∏ _i ∈ Finset.univ.erase i₀, N := by
    rw [Finset.mul_prod_erase Finset.univ (fun _ : Fin d ↦ N) (Finset.mem_univ i₀)]
    simp
  have hcount : J * (badIdx p J N).card ≤ 2 * N ^ d := by
    have hdvd : J * (N / J) = N := Nat.mul_div_cancel' hJN
    rw [hcardbad, hprodN]
    calc J * ((∏ _i ∈ Finset.univ.erase i₀, N) *
          (((Finset.range J).filter fun r ↦ r = 0 ∨ r = 1).card * (N / J)))
        = ((Finset.range J).filter fun r ↦ r = 0 ∨ r = 1).card *
            ((∏ _i ∈ Finset.univ.erase i₀, N) * (J * (N / J))) := by ring
      _ = ((Finset.range J).filter fun r ↦ r = 0 ∨ r = 1).card *
            (N * ∏ _i ∈ Finset.univ.erase i₀, N) := by rw [hdvd]; ring
      _ ≤ 2 * (N * ∏ _i ∈ Finset.univ.erase i₀, N) := Nat.mul_le_mul_right _ hcf
  have hmeas : volume (badSet p hp J N W) = ((badIdx p J N).card : ℝ≥0∞) * volume W := by
    rw [badSet]
    exact measure_levels p hp hW (by rw [badIdx]; exact Finset.filter_subset _ _)
  have hle1 : ((N : ℝ) ^ d) * (volume W).toReal ≤ 1 := by
    have h := (act p hp).card_mul_measure_le hW
    rw [card_box_const] at h
    have h2 := ENNReal.toReal_mono (volume_ne_top (Set.univ : Set UnitAddCircle)) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, UnitAddCircle.measure_univ,
      ENNReal.toReal_one, Nat.cast_pow] at h2
    exact h2
  rw [hmeas, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hw0 : (0 : ℝ) ≤ (volume W).toReal := ENNReal.toReal_nonneg
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  rw [le_div_iff₀ hJR]
  have hcountR : (J : ℝ) * ((badIdx p J N).card : ℝ) ≤ 2 * (N : ℝ) ^ d := by
    exact_mod_cast hcount
  nlinarith [mul_le_mul_of_nonneg_right hcountR hw0, hle1, hw0]

/-- **Measure claim for the good set.** -/
theorem measure_goodSet_ge {J N j₀ : ℕ} (hJ : 0 < J) (hJN : J ∣ N) (hJN' : J ≤ N)
    (hj₀ : j₀ ≤ J) (hp2 : ∃ i, p i = 2)
    {W : Set UnitAddCircle} (hW : (act p hp).Admissible (fun _ => N) W) {ε : ℝ}
    (htower : 1 - ε ≤ (volume ((act p hp).tower (fun _ => N) W)).toReal) :
    (1 - ε) * (1 - (J : ℝ) / N) ^ d * (1 - (j₀ : ℝ) / J) ≤
      (volume (goodSet p hp J N j₀ W)).toReal := by
  classical
  obtain ⟨i₀, hi₀⟩ := hp2
  have hN : 0 < N := lt_of_lt_of_le hJ hJN'
  have hgood : goodIdx p J N j₀
      = (Fintype.piFinset fun _ : Fin d ↦ Finset.Ico J N).filter fun e ↦ j₀ ≤ L p e % J := by
    ext e
    simp only [goodIdx, Finset.mem_filter, mem_box, Fintype.mem_piFinset, Finset.mem_Ico]
    exact ⟨fun h ↦ ⟨fun i ↦ ⟨h.2.1 i, h.1 i⟩, h.2.2⟩,
      fun h ↦ ⟨fun i ↦ (h.1 i).2, fun i ↦ (h.1 i).1, h.2⟩⟩
  have hcf : ((Finset.range J).filter fun r ↦ j₀ ≤ r).card = J - j₀ := by
    have hEq : (Finset.range J).filter (fun r ↦ j₀ ≤ r) = Finset.Ico j₀ J := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      exact ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩
    rw [hEq, Nat.card_Ico]
  have hcardgood : (goodIdx p J N j₀).card
      = (∏ _i ∈ Finset.univ.erase i₀, (N - J)) * ((J - j₀) * ((N - J) / J)) := by
    rw [hgood, card_filter_scale p hp hi₀ hJ hJN' dvd_rfl hJN (fun r ↦ j₀ ≤ r), hcf]
  have hprodNJ : (N - J) ^ d = (N - J) * ∏ _i ∈ Finset.univ.erase i₀, (N - J) := by
    rw [Finset.mul_prod_erase Finset.univ (fun _ : Fin d ↦ N - J) (Finset.mem_univ i₀)]
    simp
  have hcount : J * (goodIdx p J N j₀).card = (J - j₀) * (N - J) ^ d := by
    have hd : J * ((N - J) / J) = N - J := Nat.mul_div_cancel' (Nat.dvd_sub hJN dvd_rfl)
    rw [hcardgood, hprodNJ]
    calc J * ((∏ _i ∈ Finset.univ.erase i₀, (N - J)) * ((J - j₀) * ((N - J) / J)))
        = (J - j₀) * ((∏ _i ∈ Finset.univ.erase i₀, (N - J)) * (J * ((N - J) / J))) := by ring
      _ = (J - j₀) * ((N - J) * ∏ _i ∈ Finset.univ.erase i₀, (N - J)) := by rw [hd]; ring
  have hmeasg : volume (goodSet p hp J N j₀ W)
      = ((goodIdx p J N j₀).card : ℝ≥0∞) * volume W := by
    rw [goodSet]
    exact measure_levels p hp hW (by rw [goodIdx]; exact Finset.filter_subset _ _)
  have htowerR : 1 - ε ≤ (N : ℝ) ^ d * (volume W).toReal := by
    have h := (act p hp).measure_tower hW
    rw [card_box_const] at h
    rw [h, ENNReal.toReal_mul, ENNReal.toReal_natCast, Nat.cast_pow] at htower
    exact htower
  rw [hmeasg, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hw0 : (0 : ℝ) ≤ (volume W).toReal := ENNReal.toReal_nonneg
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hsub1 : (1 : ℝ) - (J : ℝ) / N = ((N - J : ℕ) : ℝ) / N := by
    rw [Nat.cast_sub hJN']
    field_simp
  have hsub2 : (1 : ℝ) - (j₀ : ℝ) / J = ((J - j₀ : ℕ) : ℝ) / J := by
    rw [Nat.cast_sub hj₀]
    field_simp
  have hcountR : (J : ℝ) * ((goodIdx p J N j₀).card : ℝ)
      = ((J - j₀ : ℕ) : ℝ) * ((N - J : ℕ) : ℝ) ^ d := by
    exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℝ)) hcount
  have hcardR : ((goodIdx p J N j₀).card : ℝ)
      = ((N - J : ℕ) : ℝ) ^ d * ((J - j₀ : ℕ) : ℝ) / J := by
    field_simp
    linarith [hcountR]
  rw [hsub1, hsub2, hcardR]
  have hbeta : (0 : ℝ) ≤ ((N - J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d * (((J - j₀ : ℕ) : ℝ) / J) := by
    positivity
  calc (1 - ε) * (((N - J : ℕ) : ℝ) / N) ^ d * (((J - j₀ : ℕ) : ℝ) / J)
      = (1 - ε) * (((N - J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d * (((J - j₀ : ℕ) : ℝ) / J)) := by
        rw [div_pow]
        ring
    _ ≤ ((N : ℝ) ^ d * (volume W).toReal) *
          (((N - J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d * (((J - j₀ : ℕ) : ℝ) / J)) :=
        mul_le_mul_of_nonneg_right htowerR hbeta
    _ = ((N - J : ℕ) : ℝ) ^ d * ((J - j₀ : ℕ) : ℝ) / J * (volume W).toReal := by
        field_simp

/-- The bad set is measurable. -/
lemma measurableSet_badSet {J N : ℕ} {W : Set UnitAddCircle} (hW : MeasurableSet W) :
    MeasurableSet (badSet p hp J N W) :=
  Finset.measurableSet_biUnion _ fun e _ ↦ (act p hp).measurable e hW

/-- The good set is measurable. -/
lemma measurableSet_goodSet {J N j₀ : ℕ} {W : Set UnitAddCircle} (hW : MeasurableSet W) :
    MeasurableSet (goodSet p hp J N j₀ W) :=
  Finset.measurableSet_biUnion _ fun e _ ↦ (act p hp).measurable e hW

end

/-! ### Upstream module `Jsp827/Marstrand/Main.lean` -/

section
/-!
# Assembly of Marstrand's counterexample

Scales `s = 0, 1, …`: `blockLen s := 2^(s+5)`, `primeList s` = all primes `≤ 2^(blockLen s)`,
threshold `j₀ := s + 1`, `towerErr s := 2^{-(s+1)}`, `boxSide s` a multiple of `blockLen s`
with `numPrimes s * blockLen s / boxSide s ≤ 2^{-s}`, and a tower base `base s` from
`RokhlinTower.NatAction.exists_tower`.  Put `bigE := ⋃ s, badScale s`, so
`volume bigE ≤ ∑ 2 / blockLen s = 1/8`.  The complements of `goodScale s` have summable
measure, so (Borel–Cantelli) almost every `x` lies in `goodScale s` for all large `s`; for
such `s` the scale `j_s(x) ≥ s + 1` satisfies `visitAverage bigE x (2^{j_s(x)}) ≥ 1/2`.
Hence `limsup ≥ 1/2 > 1/8 ≥ volume bigE`, so the averages do not converge to `volume bigE`.
Finally transfer from the circle to `ℝ` (`Int.fract (k * α)` is the class of `k • α`).
-/

open _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.ENNReal _root_.Topology

open RokhlinTower

attribute [local instance] Classical.propDecidable

/-- The block length at scale `s`. -/
def blockLen (s : ℕ) : ℕ := 2 ^ (s + 5)

/-- The primes up to `2 ^ blockLen s`, as a finset. -/
def primeFinset (s : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ blockLen s + 1)).filter Nat.Prime

/-- The number of primes up to `2 ^ blockLen s`. -/
def numPrimes (s : ℕ) : ℕ := (primeFinset s).card

/-- The increasing enumeration of the primes up to `2 ^ blockLen s`. -/
def primeList (s : ℕ) : Fin (numPrimes s) → ℕ := (primeFinset s).orderEmbOfFin rfl

/-- The box side at scale `s`. -/
def boxSide (s : ℕ) : ℕ := blockLen s * (numPrimes s * 2 ^ s + 1)

/-- The tower error at scale `s`. -/
noncomputable def towerErr (s : ℕ) : ℝ := (1 / 2) ^ (s + 1)

/-- The block length is at least `3`, as required by the counting lemmas. -/
lemma three_le_blockLen (s : ℕ) : 3 ≤ blockLen s := by
  have : (2:ℕ) ^ 5 ≤ 2 ^ (s + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simpa [blockLen] using le_trans (by norm_num) this

/-- Membership in `primeFinset s` means being a prime at most `2 ^ blockLen s`. -/
lemma mem_primeFinset {s q : ℕ} : q ∈ primeFinset s ↔ q.Prime ∧ q ≤ 2 ^ blockLen s := by
  simp [primeFinset, Finset.mem_filter, Finset.mem_range, and_comm]

/-- The enumeration takes values in `primeFinset s`. -/
lemma primeList_mem (s : ℕ) (i : Fin (numPrimes s)) : primeList s i ∈ primeFinset s :=
  (primeFinset s).orderEmbOfFin_mem rfl i

/-- Every entry of `primeList s` is prime. -/
lemma primeList_prime (s : ℕ) : ∀ i, (primeList s i).Prime :=
  fun i ↦ (mem_primeFinset.mp (primeList_mem s i)).1

/-- The enumeration `primeList s` is injective. -/
lemma primeList_injective (s : ℕ) : Function.Injective (primeList s) :=
  ((primeFinset s).orderEmbOfFin rfl).injective

/-- `primeList s` enumerates exactly the primes `≤ 2 ^ blockLen s`. -/
lemma primeList_primesUpTo (s : ℕ) : PrimesUpTo (primeList s) (blockLen s) := by
  refine ⟨primeList_injective s, fun q hq hle ↦ ?_⟩
  have hmem : q ∈ primeFinset s := mem_primeFinset.mpr ⟨hq, hle⟩
  have hr : Set.range (primeList s) = ↑(primeFinset s) :=
    Finset.range_orderEmbOfFin (primeFinset s) rfl
  have hq' : q ∈ Set.range (primeList s) := by
    rw [hr]
    exact_mod_cast hmem
  obtain ⟨i, hi⟩ := hq'
  exact ⟨i, hi⟩

/-- The prime `2` occurs in `primeList s`. -/
lemma primeList_two (s : ℕ) : ∃ i, primeList s i = 2 := by
  have hb : 0 < blockLen s := by have := three_le_blockLen s; omega
  have h2 : (2:ℕ) ≤ 2 ^ blockLen s := by
    calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ blockLen s := Nat.pow_le_pow_right (by norm_num) hb
  exact (primeList_primesUpTo s).2 2 Nat.prime_two h2

/-- There is at least one prime below `2 ^ blockLen s`. -/
lemma one_le_numPrimes (s : ℕ) : 1 ≤ numPrimes s := by
  obtain ⟨i, _⟩ := primeList_two s
  have : 0 < numPrimes s := i.pos
  omega

/-- The block length divides the box side. -/
lemma blockLen_dvd_boxSide (s : ℕ) : blockLen s ∣ boxSide s := ⟨_, rfl⟩

/-- The block length is at most the box side. -/
lemma blockLen_le_boxSide (s : ℕ) : blockLen s ≤ boxSide s := by
  have h : 1 ≤ numPrimes s * 2 ^ s + 1 := by omega
  simpa [boxSide] using Nat.le_mul_of_pos_right (blockLen s) (by omega)

/-- The box side is positive. -/
lemma boxSide_pos (s : ℕ) : 0 < boxSide s :=
  lt_of_lt_of_le (by have := three_le_blockLen s; omega) (blockLen_le_boxSide s)

/-- The tower error is positive. -/
lemma towerErr_pos (s : ℕ) : 0 < towerErr s := by
  unfold towerErr
  positivity

/-- The tower error is at most `1`. -/
lemma towerErr_le_one (s : ℕ) : towerErr s ≤ 1 := by
  unfold towerErr
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- The `ℕ^{numPrimes s}`-action at scale `s`. -/
noncomputable abbrev scaleAct (s : ℕ) :
    NatAction (volume : Measure UnitAddCircle) (numPrimes s) :=
  act (primeList s) (primeList_prime s)

/-- Existence of a tower base at scale `s`, from the Avila–Candela tower theorem. -/
lemma exists_base (s : ℕ) : ∃ W : Set UnitAddCircle,
    (scaleAct s).Admissible (fun _ ↦ boxSide s) W ∧
      1 - towerErr s ≤ (volume ((scaleAct s).tower (fun _ ↦ boxSide s) W)).toReal := by
  have : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  exact RokhlinTower.NatAction.exists_tower _
    (smoothAction_free (primeList s) (primeList_prime s) (primeList_injective s)) _
    (fun _ ↦ boxSide_pos s) (towerErr_pos s)

/-- The tower base at scale `s`. -/
noncomputable def base (s : ℕ) : Set UnitAddCircle := (exists_base s).choose

/-- The chosen base is admissible for the box of side `boxSide s`. -/
lemma base_admissible (s : ℕ) : (scaleAct s).Admissible (fun _ ↦ boxSide s) (base s) :=
  (exists_base s).choose_spec.1

/-- The chosen base is measurable. -/
lemma measurableSet_base (s : ℕ) : MeasurableSet (base s) := (base_admissible s).1

/-- The tower over the chosen base has measure at least `1 - towerErr s`. -/
lemma base_tower (s : ℕ) :
    1 - towerErr s ≤ (volume ((scaleAct s).tower (fun _ ↦ boxSide s) (base s))).toReal :=
  (exists_base s).choose_spec.2

/-- The bad set at scale `s`. -/
noncomputable def badScale (s : ℕ) : Set UnitAddCircle :=
  badSet (primeList s) (primeList_prime s) (blockLen s) (boxSide s) (base s)

/-- The good set at scale `s`. -/
noncomputable def goodScale (s : ℕ) : Set UnitAddCircle :=
  goodSet (primeList s) (primeList_prime s) (blockLen s) (boxSide s) (s + 1) (base s)

/-- The counterexample on the circle. -/
noncomputable def bigE : Set UnitAddCircle := ⋃ s, badScale s

/-- The bad set at scale `s` is measurable. -/
lemma measurableSet_badScale (s : ℕ) : MeasurableSet (badScale s) :=
  measurableSet_badSet _ _ (measurableSet_base s)

/-- The good set at scale `s` is measurable. -/
lemma measurableSet_goodScale (s : ℕ) : MeasurableSet (goodScale s) :=
  measurableSet_goodSet _ _ (measurableSet_base s)

/-- The circle counterexample is measurable. -/
lemma measurableSet_bigE : MeasurableSet bigE :=
  MeasurableSet.iUnion fun s ↦ measurableSet_badScale s

/-- The block length is positive. -/
lemma blockLen_pos (s : ℕ) : 0 < blockLen s := by
  have := three_le_blockLen s
  omega

/-- The unit circle has total volume one. -/
lemma isProbabilityMeasure_circle : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- The circle has finite volume. -/
lemma volume_circle_ne_top (A : Set UnitAddCircle) : volume A ≠ ∞ := by
  have := isProbabilityMeasure_circle
  exact measure_ne_top _ _

/-- The bad set at scale `s` has measure at most `2 / blockLen s`. -/
lemma measure_badScale_le (s : ℕ) :
    (volume (badScale s)).toReal ≤ 2 / (blockLen s : ℝ) :=
  measure_badSet_le (primeList s) (primeList_prime s) (blockLen_pos s)
    (blockLen_dvd_boxSide s) (primeList_two s) (base_admissible s)

/-- Explicit form of the scale-`s` measure bound as a geometric term. -/
lemma two_div_blockLen (s : ℕ) : 2 / (blockLen s : ℝ) = (1 / 16) * (1 / 2) ^ s := by
  have h : ((blockLen s : ℕ) : ℝ) = 2 ^ (s + 5) := by
    simp [blockLen]
  rw [h, pow_add]
  rw [div_pow, one_pow]
  field_simp
  ring

/-- Geometric bound for the measure of the bad set at scale `s`. -/
lemma volume_badScale_le (s : ℕ) :
    volume (badScale s) ≤ ENNReal.ofReal ((1 / 16) * (1 / 2) ^ s) := by
  rw [ENNReal.le_ofReal_iff_toReal_le (volume_circle_ne_top _) (by positivity)]
  rw [← two_div_blockLen]
  exact measure_badScale_le s

/-- The circle counterexample has volume at most `1/8`. -/
lemma volume_bigE_le : volume bigE ≤ ENNReal.ofReal (1 / 8) := by
  have hsum : ∑' s : ℕ, ((1 : ℝ) / 16) * (1 / 2) ^ s = 1 / 8 := by
    rw [tsum_mul_left, tsum_geometric_two]
    norm_num
  calc volume bigE ≤ ∑' s : ℕ, volume (badScale s) := measure_iUnion_le _
    _ ≤ ∑' s : ℕ, ENNReal.ofReal ((1 / 16) * (1 / 2) ^ s) :=
        ENNReal.tsum_le_tsum fun s ↦ volume_badScale_le s
    _ = ENNReal.ofReal (1 / 8) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun s ↦ by positivity)
          (summable_geometric_two.mul_left _), hsum]

/-- Real form of the volume bound for `bigE`. -/
lemma toReal_volume_bigE_le : (volume bigE).toReal ≤ 1 / 8 :=
  ENNReal.toReal_le_of_le_ofReal (by norm_num) volume_bigE_le

/-- The real value of the block length. -/
lemma blockLen_cast (s : ℕ) : ((blockLen s : ℕ) : ℝ) = 32 * 2 ^ s := by
  have : ((2:ℝ) ^ (s + 5)) = 2 ^ s * 32 := by
    rw [pow_add]
    norm_num
  simp [blockLen, this]
  ring

/-- The real value of the box side. -/
lemma boxSide_cast (s : ℕ) :
    ((boxSide s : ℕ) : ℝ) = (blockLen s : ℝ) * ((numPrimes s : ℝ) * 2 ^ s + 1) := by
  simp only [boxSide, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]

/-- The threshold `s + 1` is at most the block length. -/
lemma succ_le_blockLen (s : ℕ) : s + 1 ≤ blockLen s := by
  have h : s + 5 < 2 ^ (s + 5) := Nat.lt_two_pow_self
  simp only [blockLen]
  omega

/-- Bernoulli bound for the `(3/2)^s` growth used below. -/
lemma bernoulli_three_halves (s : ℕ) : 1 + (s : ℝ) / 2 ≤ (3 / 2) ^ s := by
  have h := one_add_mul_le_pow (a := (1/2 : ℝ)) (by norm_num) s
  have h2 : (1 : ℝ) + (1 / 2) = 3 / 2 := by norm_num
  rw [h2] at h
  calc 1 + (s : ℝ) / 2 = 1 + (s : ℝ) * (1 / 2) := by ring
    _ ≤ (3 / 2) ^ s := h

/-- Comparison of the two geometric rates used below. -/
lemma half_pow_le (s : ℕ) : ((1 : ℝ) / 2) ^ s ≤ (3 / 4) ^ s :=
  pow_le_pow_left₀ (by norm_num) (by norm_num) s

/-- The tower error is dominated by `(3/4)^s`. -/
lemma towerErr_le (s : ℕ) : towerErr s ≤ (3 / 4) ^ s := by
  have h : towerErr s ≤ (1 / 2 : ℝ) ^ s := by
    unfold towerErr
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) s]
  exact h.trans (half_pow_le s)

/-- The threshold term is dominated by `(3/4)^s`. -/
lemma thresholdTerm_le (s : ℕ) : ((s : ℝ) + 1) / (blockLen s : ℝ) ≤ (3 / 4) ^ s := by
  have hpos : (0 : ℝ) < 32 * 2 ^ s := by positivity
  rw [blockLen_cast, div_le_iff₀ hpos]
  have hb := bernoulli_three_halves s
  have h32 : (3 / 4 : ℝ) ^ s * (32 * 2 ^ s) = 32 * (3 / 2) ^ s := by
    rw [show (32:ℝ) * 2 ^ s = 2 ^ s * 32 by ring, ← mul_assoc, ← mul_pow]
    norm_num
    ring
  rw [h32]
  nlinarith [Nat.cast_nonneg (α := ℝ) s]

/-- The tower-shape term is dominated by `2^{-s}`. -/
lemma primeTerm_le (s : ℕ) :
    (numPrimes s : ℝ) * ((blockLen s : ℝ) / (boxSide s : ℝ)) ≤ (1 / 2 : ℝ) ^ s := by
  have hB : (0 : ℝ) < (blockLen s : ℝ) := by
    exact_mod_cast blockLen_pos s
  have hD : (1 : ℝ) ≤ (numPrimes s : ℝ) := by
    exact_mod_cast one_le_numPrimes s
  have hden : (0 : ℝ) < (numPrimes s : ℝ) * 2 ^ s + 1 := by positivity
  rw [boxSide_cast]
  have hrw : (numPrimes s : ℝ) * ((blockLen s : ℝ) /
      ((blockLen s : ℝ) * ((numPrimes s : ℝ) * 2 ^ s + 1)))
      = (numPrimes s : ℝ) / ((numPrimes s : ℝ) * 2 ^ s + 1) := by
    field_simp
  rw [hrw, div_le_iff₀ hden]
  have hp : ((1:ℝ) / 2) ^ s * 2 ^ s = 1 := by
    rw [← mul_pow]
    norm_num
  nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) s]

/-- `(1-x)(1-y)(1-z) ≥ 1-x-y-z` for `x, y ≥ 0` and `z ∈ [0,1]`. -/
lemma three_factor_bound {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    1 - x - y - z ≤ (1 - x) * (1 - y) * (1 - z) := by
  nlinarith [mul_nonneg (mul_nonneg hx hy) (sub_nonneg.mpr hz1), mul_nonneg hx hz,
    mul_nonneg hy hz]

/-- A linear lower bound for the measure of the good set at scale `s`. -/
lemma measure_goodScale_ge (s : ℕ) :
    1 - towerErr s - (numPrimes s : ℝ) * ((blockLen s : ℝ) / (boxSide s : ℝ))
        - ((s : ℝ) + 1) / (blockLen s : ℝ) ≤ (volume (goodScale s)).toReal := by
  have hmain := measure_goodSet_ge (primeList s) (primeList_prime s) (blockLen_pos s)
    (blockLen_dvd_boxSide s) (blockLen_le_boxSide s) (succ_le_blockLen s) (primeList_two s)
    (base_admissible s) (base_tower s)
  set a : ℝ := (blockLen s : ℝ) / (boxSide s : ℝ) with ha
  set x : ℝ := towerErr s with hxdef
  set y : ℝ := (numPrimes s : ℝ) * a with hy
  set z : ℝ := ((s : ℝ) + 1) / (blockLen s : ℝ) with hz
  have hcast : ((s + 1 : ℕ) : ℝ) / (blockLen s : ℝ) = z := by
    rw [hz]
    push_cast
    ring
  rw [hcast] at hmain
  have hx0 : 0 ≤ x := (towerErr_pos s).le
  have hx1 : x ≤ 1 := towerErr_le_one s
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one (by exact_mod_cast boxSide_pos s)]
    exact_mod_cast blockLen_le_boxSide s
  have hy0 : 0 ≤ y := by positivity
  have hz0 : 0 ≤ z := by positivity
  have hz1 : z ≤ 1 := by
    rw [hz, div_le_one (by exact_mod_cast blockLen_pos s)]
    have := succ_le_blockLen s
    have : ((s : ℝ) + 1) ≤ ((blockLen s : ℕ) : ℝ) := by exact_mod_cast this
    exact this
  have hber : 1 - y ≤ (1 - a) ^ (numPrimes s) := by
    have h := one_add_mul_le_pow (a := -a) (by linarith) (numPrimes s)
    calc 1 - y = 1 + (numPrimes s : ℝ) * (-a) := by rw [hy]; ring
      _ ≤ (1 + -a) ^ (numPrimes s) := h
      _ = (1 - a) ^ (numPrimes s) := by ring_nf
  have step1 : (1 - x) * (1 - y) ≤ (1 - x) * (1 - a) ^ (numPrimes s) :=
    mul_le_mul_of_nonneg_left hber (by linarith)
  have step2 : (1 - x) * (1 - y) * (1 - z) ≤ (1 - x) * (1 - a) ^ (numPrimes s) * (1 - z) :=
    mul_le_mul_of_nonneg_right step1 (by linarith)
  have step3 : 1 - x - y - z ≤ (1 - x) * (1 - y) * (1 - z) :=
    three_factor_bound hx0 hy0 hz0 hz1
  rw [goodScale]
  linarith [hmain]

/-- The complement of the good set at scale `s` is small. -/
lemma toReal_volume_compl_goodScale_le (s : ℕ) :
    (volume (goodScale s)ᶜ).toReal ≤ 3 * (3 / 4) ^ s := by
  have hle : volume (goodScale s) ≤ 1 := by
    calc volume (goodScale s) ≤ volume (univ : Set UnitAddCircle) := measure_mono (subset_univ _)
      _ = 1 := UnitAddCircle.measure_univ
  have hcompl : volume (goodScale s)ᶜ = 1 - volume (goodScale s) := by
    rw [measure_compl (measurableSet_goodScale s) (volume_circle_ne_top _),
      UnitAddCircle.measure_univ]
  have htoReal : (volume (goodScale s)ᶜ).toReal = 1 - (volume (goodScale s)).toReal := by
    rw [hcompl, ENNReal.toReal_sub_of_le hle (by simp)]
    simp
  rw [htoReal]
  have h1 := measure_goodScale_ge s
  have h2 := towerErr_le s
  have h3 := (primeTerm_le s).trans (half_pow_le s)
  have h4 := thresholdTerm_le s
  linarith

/-- Geometric bound for the measure of the complement of the good set. -/
lemma volume_compl_goodScale_le (s : ℕ) :
    volume (goodScale s)ᶜ ≤ ENNReal.ofReal (3 * (3 / 4) ^ s) := by
  rw [ENNReal.le_ofReal_iff_toReal_le (volume_circle_ne_top _) (by positivity)]
  exact toReal_volume_compl_goodScale_le s

/-- The complements of the good sets have summable measure. -/
lemma tsum_volume_compl_goodScale_ne_top : ∑' s : ℕ, volume (goodScale s)ᶜ ≠ ∞ := by
  have hsummable : Summable fun s : ℕ ↦ 3 * (3 / 4 : ℝ) ^ s :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 3
  have hle : ∑' s : ℕ, volume (goodScale s)ᶜ ≤ ∑' s : ℕ, ENNReal.ofReal (3 * (3 / 4 : ℝ) ^ s) :=
    ENNReal.tsum_le_tsum fun s ↦ volume_compl_goodScale_le s
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun s ↦ by positivity) hsummable] at hle
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- Borel–Cantelli: almost every point is eventually good. -/
lemma ae_eventually_mem_goodScale :
    ∀ᵐ x : UnitAddCircle, ∀ᶠ s in atTop, x ∈ goodScale s := by
  filter_upwards [MeasureTheory.ae_eventually_notMem tsum_volume_compl_goodScale_ne_top]
    with x hx
  filter_upwards [hx] with s hs
  simpa using hs

/-- A good point at scale `s` has a dyadic scale `j ≥ s + 1` at which at
least half of its multiples visit `bigE`. -/
lemma visits_of_mem_goodScale {x : UnitAddCircle} {s : ℕ} (hx : x ∈ goodScale s) :
    ∃ j : ℕ, s + 1 ≤ j ∧
      2 ^ (j - 1) ≤ ((Finset.Icc 1 (2 ^ j)).filter fun n ↦ n • x ∈ bigE).card := by
  rw [goodScale, goodSet] at hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨e, he, hxe⟩ := hx
  have he' := he
  rw [goodIdx, Finset.mem_filter] at he'
  refine ⟨L (primeList s) e % blockLen s, he'.2.2, ?_⟩
  have hhalf := half_visits (primeList s) (primeList_prime s) (three_le_blockLen s)
    (primeList_primesUpTo s) he (by omega) hxe
  refine le_trans hhalf (Finset.card_le_card ?_)
  refine Finset.monotone_filter_right _ fun n _ hn ↦ ?_
  simp only [bigE, Set.mem_iUnion]
  exact ⟨s, hn⟩

/-- Almost every point of the circle sees dyadic scales at which at least half of its
multiples land in `bigE`. -/
lemma ae_visits_bigE : ∀ᵐ x : UnitAddCircle, ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧
    2 ^ (j - 1) ≤ ((Finset.Icc 1 (2 ^ j)).filter fun n ↦ n • x ∈ bigE).card := by
  filter_upwards [ae_eventually_mem_goodScale] with x hx j₀
  obtain ⟨s, hs, hsj⟩ := (hx.and (eventually_ge_atTop j₀)).exists
  obtain ⟨j, hj, hcard⟩ := visits_of_mem_goodScale hs
  exact ⟨j, by omega, hcard⟩

/-- Integers vanish in the unit circle. -/
lemma intCast_circle_eq_zero (m : ℤ) : ((m : ℝ) : UnitAddCircle) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨m, by simp⟩

/-- The class of `Int.fract (k * α)` in the circle is `k • α`. -/
lemma coe_fract (α : ℝ) (k : ℕ) :
    ((Int.fract ((k : ℝ) * α) : ℝ) : UnitAddCircle) = k • ((α : ℝ) : UnitAddCircle) := by
  have h1 : Int.fract ((k : ℝ) * α) = (k : ℝ) * α + ((-⌊(k : ℝ) * α⌋ : ℤ) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [h1, show ((((k : ℝ) * α + ((-⌊(k : ℝ) * α⌋ : ℤ) : ℝ) : ℝ)) : UnitAddCircle)
      = (((k : ℝ) * α : ℝ) : UnitAddCircle) + ((((-⌊(k : ℝ) * α⌋ : ℤ)) : ℝ) : UnitAddCircle) from
      rfl, intCast_circle_eq_zero, add_zero, ← nsmul_eq_mul, AddCircle.coe_nsmul]

/-- The counterexample on the line. -/
noncomputable def bigE' : Set ℝ := Ioo (0 : ℝ) 1 ∩ ((↑) : ℝ → UnitAddCircle) ⁻¹' bigE

/-- The real counterexample is measurable. -/
lemma measurableSet_bigE' : MeasurableSet bigE' :=
  measurableSet_Ioo.inter ((AddCircle.measurable_mk' (a := (1 : ℝ))) measurableSet_bigE)

/-- The real counterexample has measure at most `1/8`. -/
lemma volume_bigE'_le : (volume bigE').toReal ≤ 1 / 8 := by
  have hproj := AddCircle.add_projection_respects_measure (T := 1) (t := 0) measurableSet_bigE
  have hsub : bigE' ⊆ (QuotientAddGroup.mk ⁻¹' bigE ∩ Ioc (0 : ℝ) (0 + 1)) := by
    intro y hy
    exact ⟨hy.2, ⟨hy.1.1, by simpa using hy.1.2.le⟩⟩
  have hle : volume bigE' ≤ volume bigE := by
    rw [hproj]
    exact measure_mono hsub
  exact le_trans (ENNReal.toReal_mono (volume_circle_ne_top _) hle) toReal_volume_bigE_le

/-- The preimage of a circle null set under the covering map is null. -/
lemma preimage_null {Z : Set UnitAddCircle} (hZ : MeasurableSet Z) (h0 : volume Z = 0) :
    volume ((QuotientAddGroup.mk : ℝ → UnitAddCircle) ⁻¹' Z) = 0 := by
  have hcover : (QuotientAddGroup.mk : ℝ → UnitAddCircle) ⁻¹' Z
      = ⋃ m : ℤ, ((QuotientAddGroup.mk : ℝ → UnitAddCircle) ⁻¹' Z ∩
        Ioc ((m : ℝ)) ((m : ℝ) + 1)) := by
    refine Set.eq_of_subset_of_subset (fun y hy ↦ ?_)
      (Set.iUnion_subset fun m ↦ Set.inter_subset_left)
    refine Set.mem_iUnion.mpr ⟨⌈y⌉ - 1, hy, ?_, ?_⟩
    · push_cast
      linarith [Int.ceil_lt_add_one y]
    · push_cast
      linarith [Int.le_ceil y]
  rw [hcover]
  refine measure_iUnion_null fun m ↦ ?_
  rw [← AddCircle.add_projection_respects_measure (T := 1) (t := (m : ℝ)) hZ]
  exact h0

/-- An almost-everywhere property on the circle pulls back to `ℝ`. -/
lemma ae_pullback {P : UnitAddCircle → Prop} (h : ∀ᵐ x : UnitAddCircle, P x) :
    ∀ᵐ α : ℝ, P ((α : ℝ) : UnitAddCircle) := by
  rw [ae_iff] at h ⊢
  obtain ⟨Z, hsub, hmeas, h0⟩ := exists_measurable_superset_of_null h
  exact measure_mono_null (fun α hα ↦ hsub hα) (preimage_null hmeas h0)

/-- Almost every real number is irrational. -/
lemma ae_irrational : ∀ᵐ α : ℝ, Irrational α := by
  rw [ae_iff]
  have hset : {α : ℝ | ¬ Irrational α} = Set.range ((↑) : ℚ → ℝ) := by
    ext α
    simp [Irrational]
  rw [hset]
  exact (Set.countable_range _).measure_zero _

/-- For irrational `α` and `k ≥ 1`, `Int.fract (k * α)` lies in `bigE'`
exactly when `k • α` lies in `bigE`. -/
lemma fract_mem_bigE'_iff {α : ℝ} (hα : Irrational α) {k : ℕ} (hk : 1 ≤ k) :
    Int.fract ((k : ℝ) * α) ∈ bigE' ↔ k • ((α : ℝ) : UnitAddCircle) ∈ bigE := by
  have hpos : 0 < Int.fract ((k : ℝ) * α) := by
    rcases (Int.fract_nonneg ((k : ℝ) * α)).lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have hirr : Irrational ((k : ℝ) * α) := hα.natCast_mul (by omega)
      have h2 : (k : ℝ) * α - (⌊(k : ℝ) * α⌋ : ℤ) = 0 := by
        rw [← Int.fract]
        exact h1.symm
      exact hirr.ne_int _ (sub_eq_zero.mp h2)
  constructor
  · intro h
    rw [← coe_fract]
    exact h.2
  · intro h
    refine ⟨⟨hpos, Int.fract_lt_one _⟩, ?_⟩
    show ((Int.fract ((k : ℝ) * α) : ℝ) : UnitAddCircle) ∈ bigE
    rw [coe_fract]
    exact h

/-- The visit averages of `bigE'` count the circle multiples landing in `bigE`. -/
lemma visitAverage_eq {α : ℝ} (hα : Irrational α) (n : ℕ) :
    visitAverage bigE' α n
      = (((Finset.Icc 1 n).filter fun k ↦ k • ((α : ℝ) : UnitAddCircle) ∈ bigE).card : ℝ) / n := by
  have hfilter : ((Finset.Icc 1 n).filter fun k : ℕ ↦ Int.fract ((k : ℝ) * α) ∈ bigE')
      = ((Finset.Icc 1 n).filter fun k : ℕ ↦ k • ((α : ℝ) : UnitAddCircle) ∈ bigE) :=
    Finset.filter_congr fun k hk ↦ fract_mem_bigE'_iff hα (Finset.mem_Icc.mp hk).1
  rw [visitAverage, Finset.sum_boole, hfilter]

/-- At a good dyadic scale the visit average is at least `1/2`. -/
lemma half_le_visitAverage {α : ℝ} (hα : Irrational α) {j : ℕ} (hj : 1 ≤ j)
    (hcard : 2 ^ (j - 1) ≤ ((Finset.Icc 1 (2 ^ j)).filter
      fun n ↦ n • ((α : ℝ) : UnitAddCircle) ∈ bigE).card) :
    1 / 2 ≤ visitAverage bigE' α (2 ^ j) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [visitAverage_eq hα, le_div_iff₀ (by positivity)]
  have h0 : (2 : ℕ) ^ m ≤ ((Finset.Icc 1 (2 ^ (m + 1))).filter
      fun n : ℕ ↦ n • ((α : ℝ) : UnitAddCircle) ∈ bigE).card := by simpa using hcard
  have h1 : ((2 : ℝ) ^ m) ≤
      (((Finset.Icc 1 (2 ^ (m + 1))).filter
        fun n : ℕ ↦ n • ((α : ℝ) : UnitAddCircle) ∈ bigE).card : ℝ) := by
    exact_mod_cast h0
  have h2 : (1 / 2 : ℝ) * (((2 ^ (m + 1) : ℕ) : ℝ)) = 2 ^ m := by
    push_cast
    rw [pow_succ]
    ring
  rw [h2]
  exact h1

/-- Transfer: the fractional parts `Int.fract (k * α)` are the representatives in `[0,1)` of
`k • (α : UnitAddCircle)`; the set `E' := {x ∈ Ioo 0 1 | (x : UnitAddCircle) ∈ E}` has the
same measure as `E` and, for irrational `α`, the same visit counts. -/
theorem exists_counterexample_ae' :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Ioo (0 : ℝ) 1 ∧
      ∀ᵐ α : ℝ, ¬ HasExpectedLimit E α := by
  refine ⟨bigE', measurableSet_bigE', Set.inter_subset_left, ?_⟩
  filter_upwards [ae_irrational, ae_pullback ae_visits_bigE] with α hα hvis
  intro hlim
  have hc : (volume bigE').toReal < 1 / 4 := lt_of_le_of_lt volume_bigE'_le (by norm_num)
  have hev : ∀ᶠ n in atTop, visitAverage bigE' α n < 1 / 4 :=
    Filter.Tendsto.eventually_lt_const hc hlim
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  obtain ⟨j, hj, hcard⟩ := hvis (max M 1)
  have hj1 : 1 ≤ j := le_trans (le_max_right M 1) hj
  have hjM : M ≤ j := le_trans (le_max_left M 1) hj
  have h2j : M ≤ 2 ^ j := le_trans hjM (le_of_lt Nat.lt_two_pow_self)
  have hlt := hM (2 ^ j) h2j
  have hge := half_le_visitAverage hα hj1 hcard
  linarith

end

/-! ### Upstream module `Jsp827/Root.lean` -/

section
/-!
# Roots of the JSP-000827 / Erdős #994 development

**Target (Marstrand 1970).**  Khintchine's conjecture is false: there is a measurable
`E ⊆ (0,1)` for which the visit averages `(1/n) ∑_{k ≤ n} 1_E({kα})` fail to converge to
`λ(E)` for almost every `α`.
-/

open _root_.MeasureTheory _root_.Set

/-- Explicit witness form: a measurable `E ⊆ (0,1)` with `∀ᵐ α, ¬ HasExpectedLimit E α`. -/
theorem exists_counterexample_ae :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Ioo (0 : ℝ) 1 ∧
      ∀ᵐ α : ℝ, ¬ HasExpectedLimit E α :=
  exists_counterexample_ae'

/-- **Marstrand's theorem:** the fixed-set Khintchine conjecture (`KhintchineFixedSet`,
the exact predicate of plby/lean-proofs `Erdos994`) is false. -/
theorem erdos_994 : ¬ KhintchineFixedSet :=
  not_khintchineFixedSet_of_exists exists_counterexample_ae

end

#print axioms erdos_994
-- 'Erdos994.erdos_994' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos994
