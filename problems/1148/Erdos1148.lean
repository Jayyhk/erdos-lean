import Mathlib

set_option linter.mathlibStandardSet false

namespace Erdos1148

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Lemma 2.1: Dictionary between ternary representations and discriminant points.
If b^2 - 4ac = 4n, b is even, and a, c have the same parity, then x=(a-c)/2,
y=b/2, z=(a+c)/2 are integers satisfying x^2+y^2-z^2=n.
-/
lemma lemma_dictionary (n : ℤ) (a b c : ℤ) (h_eq : b^2 - 4 * a * c = 4 * n)
    (hb : b % 2 = 0) (hac : a % 2 = c % 2) :
    ((a - c) / 2) ^ 2 + (b / 2) ^ 2 - ((a + c) / 2) ^ 2 = n := by
  have h4 : 4 * (((a - c) / 2) ^ 2 + (b / 2) ^ 2 - ((a + c) / 2) ^ 2) = 4 * n := by
    have hx : a - c = 2 * ((a - c) / 2) := by
      have : (a - c) % 2 = 0 := by omega
      omega
    have hy : b = 2 * (b / 2) := by omega
    have hz : a + c = 2 * ((a + c) / 2) := by
      have : (a + c) % 2 = 0 := by omega
      omega
    calc
      4 * (((a - c) / 2) ^ 2 + (b / 2) ^ 2 - ((a + c) / 2) ^ 2)
        = (2 * ((a - c) / 2)) ^ 2 + (2 * (b / 2)) ^ 2 - (2 * ((a + c) / 2)) ^ 2 := by ring
      _ = (a - c) ^ 2 + b ^ 2 - (a + c) ^ 2 := by rw [← hx, ← hy, ← hz]
      _ = b ^ 2 - 4 * a * c := by ring
      _ = 4 * n := h_eq
  exact mul_left_cancel₀ (by decide) h4

/-
Definition of R*_disc(d) from the paper.
-/
def R_star_disc (d : ℤ) : Set (ℤ × ℤ × ℤ) :=
  { t | t.2.1 ^ 2 - 4 * t.1 * t.2.2 = d ∧ Int.gcd t.1 (Int.gcd t.2.1 t.2.2) = 1 }

/-
Definition of V_disc,+1(R) from the paper.
-/
def V_disc_plus_1 : Set (ℝ × ℝ × ℝ) :=
  { t | t.2.1 ^ 2 - 4 * t.1 * t.2.2 = 1 }

/-- `V_disc,+1` is a closed subset of `ℝ³` (the level set of a polynomial). -/
lemma V_disc_plus_1_isClosed : IsClosed V_disc_plus_1 :=
  isClosed_eq (by fun_prop) continuous_const

/-- `V_disc,+1` is Borel-measurable. -/
lemma V_disc_plus_1_measurableSet : MeasurableSet V_disc_plus_1 :=
  V_disc_plus_1_isClosed.measurableSet

/-! ### Cone construction and the measure μ_disc,+1 (ELMV §1.1)

For `Ω ⊆ ℝ³`, ELMV define the cone `C(Ω) := { r·x : x ∈ Ω, r ∈ [0,1] }` and
the GL₂(ℝ)-invariant measure on the hyperboloid by
`μ_disc,+1(Ω) = vol_ℝ³(C(Ω ∩ V_disc,+1))`.

We realize `μ_disc,+1` as a Borel measure via the metric outer measure
construction `mkMetric'` applied to the cone-volume set function. -/

/-- The cone construction `C(Ω) = { r·x : x ∈ Ω, r ∈ [0,1] }` (ELMV §1.1). -/
def cone (Ω : Set (ℝ × ℝ × ℝ)) : Set (ℝ × ℝ × ℝ) :=
  { x | ∃ y ∈ Ω, ∃ r ∈ Set.Icc (0:ℝ) 1,
      x = (r * y.1, r * y.2.1, r * y.2.2) }

lemma cone_mono {Ω₁ Ω₂ : Set (ℝ × ℝ × ℝ)} (h : Ω₁ ⊆ Ω₂) : cone Ω₁ ⊆ cone Ω₂ := by
  rintro x ⟨y, hy, r, hr, rfl⟩
  exact ⟨y, h hy, r, hr, rfl⟩

@[simp] lemma cone_empty : cone (∅ : Set (ℝ × ℝ × ℝ)) = ∅ := by
  ext x
  simp [cone]

lemma cone_iUnion {ι : Sort*} (Ω : ι → Set (ℝ × ℝ × ℝ)) :
    cone (⋃ i, Ω i) = ⋃ i, cone (Ω i) := by
  ext x
  simp only [cone, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, ⟨i, hi⟩, r, hr, hx⟩
    exact ⟨i, y, hi, r, hr, hx⟩
  · rintro ⟨i, y, hi, r, hr, hx⟩
    exact ⟨y, ⟨i, hi⟩, r, hr, hx⟩

/-- **Ray uniqueness.** For distinct `x, y ∈ V_disc,+1`, the cone segments
`{r·x : r ∈ [0,1]}` and `{r·y : r ∈ [0,1]}` intersect only at the origin. -/
lemma cone_singleton_inter {x y : ℝ × ℝ × ℝ}
    (hx : x ∈ V_disc_plus_1) (hy : y ∈ V_disc_plus_1) (hxy : x ≠ y) :
    cone {x} ∩ cone {y} ⊆ ({0} : Set (ℝ × ℝ × ℝ)) := by
  rintro z ⟨hzx_mem, hzy_mem⟩
  obtain ⟨x', hx', r, hr, hzx⟩ := hzx_mem
  obtain ⟨y', hy', s, hs, hzy⟩ := hzy_mem
  rw [Set.mem_singleton_iff] at hx' hy'
  rw [hx'] at hzx
  rw [hy'] at hzy
  have hx_eq : x.2.1 ^ 2 - 4 * x.1 * x.2.2 = 1 := hx
  have hy_eq : y.2.1 ^ 2 - 4 * y.1 * y.2.2 = 1 := hy
  have heq : (r * x.1, r * x.2.1, r * x.2.2)
           = (s * y.1, s * y.2.1, s * y.2.2) := by rw [← hzx, hzy]
  rw [Prod.mk.injEq, Prod.mk.injEq] at heq
  obtain ⟨h1, h2, h3⟩ := heq
  have hr2_eq_s2 : r ^ 2 = s ^ 2 := by
    have lhs_calc : (r * x.2.1) ^ 2 - 4 * (r * x.1) * (r * x.2.2)
                 = r ^ 2 * (x.2.1 ^ 2 - 4 * x.1 * x.2.2) := by ring
    have rhs_calc : (s * y.2.1) ^ 2 - 4 * (s * y.1) * (s * y.2.2)
                 = s ^ 2 * (y.2.1 ^ 2 - 4 * y.1 * y.2.2) := by ring
    have : r ^ 2 * (x.2.1 ^ 2 - 4 * x.1 * x.2.2)
         = s ^ 2 * (y.2.1 ^ 2 - 4 * y.1 * y.2.2) := by
      rw [← lhs_calc, ← rhs_calc, h1, h2, h3]
    rw [hx_eq, hy_eq, mul_one, mul_one] at this
    exact this
  have hr_nn : 0 ≤ r := hr.1
  have hs_nn : 0 ≤ s := hs.1
  have hr_eq_s : r = s := by
    nlinarith [sq_nonneg (r - s), sq_nonneg (r + s)]
  subst hr_eq_s
  by_cases hr0 : r = 0
  · simp [hr0] at hzx
    rw [hzx]
    rfl
  · push_neg at hr0
    exfalso
    have hx_eq_y : x = y := by
      apply Prod.ext
      · exact mul_left_cancel₀ hr0 h1
      · apply Prod.ext
        · exact mul_left_cancel₀ hr0 h2
        · exact mul_left_cancel₀ hr0 h3
    exact hxy hx_eq_y

/-- For two disjoint subsets of `V_disc,+1`, their cones intersect only at `{0}`. -/
lemma cone_inter_subset_zero {A B : Set (ℝ × ℝ × ℝ)}
    (hA : A ⊆ V_disc_plus_1) (hB : B ⊆ V_disc_plus_1) (hdisj : Disjoint A B) :
    cone A ∩ cone B ⊆ ({0} : Set (ℝ × ℝ × ℝ)) := by
  rintro z ⟨⟨x, hxA, r, hr, hzx⟩, ⟨y, hyB, s, hs, hzy⟩⟩
  have hxV : x ∈ V_disc_plus_1 := hA hxA
  have hyV : y ∈ V_disc_plus_1 := hB hyB
  have hxy : x ≠ y := by
    intro heq
    rw [heq] at hxA
    exact Set.disjoint_iff.mp hdisj ⟨hxA, hyB⟩
  exact cone_singleton_inter hxV hyV hxy
    ⟨⟨x, rfl, r, hr, hzx⟩, ⟨y, rfl, s, hs, hzy⟩⟩

/-- `{0}` has Lebesgue volume zero in ℝ³. -/
lemma volume_singleton_zero :
    MeasureTheory.volume ({0} : Set (ℝ × ℝ × ℝ)) = 0 := by
  have h_eq : ({0} : Set (ℝ × ℝ × ℝ)) = ({0} : Set ℝ) ×ˢ (({0} : Set ℝ) ×ˢ ({0} : Set ℝ)) := by
    ext z
    simp [Prod.ext_iff]
  rw [h_eq, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
    MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
  simp [Real.volume_singleton]

/-- **Lusin-Souslin lemma applied**: for Borel `s ⊂ ℝ³`,
`cone(s ∩ V_disc,+1)` is Borel-measurable.

The map `ψ : ℝ × ℝ³ → ℝ³, ψ(r, x) = r·x` is continuous, and **injective** on
`(0, 1] × V_disc,+1` (since for `x ∈ V_disc,+1`, `disc(r·x) = r²` determines
`r > 0` uniquely, hence `x`). By the Lusin-Souslin theorem
(`MeasurableSet.image_of_continuousOn_injOn`), the image
`ψ((0, 1] × (s ∩ V_disc,+1))` is Borel. Adding `{0}` (Borel) yields
`cone(s ∩ V_disc,+1)`. -/
lemma cone_inter_V_measurableSet {s : Set (ℝ × ℝ × ℝ)} (hs : MeasurableSet s) :
    MeasurableSet (cone (s ∩ V_disc_plus_1)) := by
  by_cases h_ne : (s ∩ V_disc_plus_1).Nonempty
  · -- Define ψ(r, x) = r·x componentwise.
    set ψ : ℝ × (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ) :=
      fun p => (p.1 * p.2.1, p.1 * p.2.2.1, p.1 * p.2.2.2) with hψ_def
    have hψ_cont : Continuous ψ := by
      show Continuous (fun p : ℝ × (ℝ × ℝ × ℝ) =>
        (p.1 * p.2.1, p.1 * p.2.2.1, p.1 * p.2.2.2))
      fun_prop
    -- S = (0, 1] × (s ∩ V_disc_plus_1) measurable in ℝ × ℝ³.
    set S : Set (ℝ × (ℝ × ℝ × ℝ)) := Set.Ioc (0 : ℝ) 1 ×ˢ (s ∩ V_disc_plus_1) with hS_def
    have hS_meas : MeasurableSet S :=
      measurableSet_Ioc.prod (hs.inter V_disc_plus_1_measurableSet)
    -- ψ is injective on S (using discriminant computation).
    have hψ_inj : Set.InjOn ψ S := by
      intro p₁ hp₁ p₂ hp₂ h_eq
      obtain ⟨r₁, x₁⟩ := p₁
      obtain ⟨r₂, x₂⟩ := p₂
      simp only [hS_def, Set.mem_prod, Set.mem_Ioc] at hp₁ hp₂
      have hr₁ : 0 < r₁ := hp₁.1.1
      have hr₂ : 0 < r₂ := hp₂.1.1
      have hx₁ : x₁ ∈ V_disc_plus_1 := hp₁.2.2
      have hx₂ : x₂ ∈ V_disc_plus_1 := hp₂.2.2
      have hd₁ : x₁.2.1^2 - 4 * x₁.1 * x₁.2.2 = 1 := hx₁
      have hd₂ : x₂.2.1^2 - 4 * x₂.1 * x₂.2.2 = 1 := hx₂
      simp only [hψ_def, Prod.mk.injEq] at h_eq
      obtain ⟨h₁, h₂, h₃⟩ := h_eq
      -- (r₁·x₁.2.1)² - 4·(r₁·x₁.1)·(r₁·x₁.2.2) = r₁²·1 = r₁²
      have h_lhs : (r₁ * x₁.2.1)^2 - 4 * (r₁ * x₁.1) * (r₁ * x₁.2.2) = r₁^2 := by
        have : (r₁ * x₁.2.1)^2 - 4 * (r₁ * x₁.1) * (r₁ * x₁.2.2)
             = r₁^2 * (x₁.2.1^2 - 4 * x₁.1 * x₁.2.2) := by ring
        rw [this, hd₁]; ring
      have h_rhs : (r₂ * x₂.2.1)^2 - 4 * (r₂ * x₂.1) * (r₂ * x₂.2.2) = r₂^2 := by
        have : (r₂ * x₂.2.1)^2 - 4 * (r₂ * x₂.1) * (r₂ * x₂.2.2)
             = r₂^2 * (x₂.2.1^2 - 4 * x₂.1 * x₂.2.2) := by ring
        rw [this, hd₂]; ring
      have h_rsq : r₁^2 = r₂^2 := by
        rw [← h_lhs, ← h_rhs, h₁, h₂, h₃]
      have h_r_eq : r₁ = r₂ := by
        have h_factor : (r₁ - r₂) * (r₁ + r₂) = 0 := by nlinarith
        rcases mul_eq_zero.mp h_factor with h | h
        · linarith
        · linarith
      subst h_r_eq
      have h_r_ne : r₁ ≠ 0 := hr₁.ne'
      have hx_1 : x₁.1 = x₂.1 := mul_left_cancel₀ h_r_ne h₁
      have hx_2 : x₁.2.1 = x₂.2.1 := mul_left_cancel₀ h_r_ne h₂
      have hx_3 : x₁.2.2 = x₂.2.2 := mul_left_cancel₀ h_r_ne h₃
      obtain ⟨a₁, b₁, c₁⟩ := x₁
      obtain ⟨a₂, b₂, c₂⟩ := x₂
      simp_all
    -- Apply Lusin-Souslin.
    have h_image_meas : MeasurableSet (ψ '' S) :=
      hS_meas.image_of_continuousOn_injOn hψ_cont.continuousOn hψ_inj
    -- cone(s ∩ V_disc_plus_1) = ψ '' S ∪ {0}.
    have h_cone : cone (s ∩ V_disc_plus_1) = ψ '' S ∪ {0} := by
      ext y
      constructor
      · -- forward: y ∈ cone → y ∈ ψ '' S ∪ {0}.
        rintro ⟨x, hx, r, ⟨hr_nn, hr_le⟩, hy_eq⟩
        by_cases hr_pos : 0 < r
        · left
          refine ⟨(r, x), ?_, ?_⟩
          · show (r, x) ∈ S
            rw [hS_def]
            exact ⟨⟨hr_pos, hr_le⟩, hx⟩
          · -- ψ(r, x) = y
            show ψ (r, x) = y
            rw [hψ_def]
            rw [hy_eq]
        · right
          push_neg at hr_pos
          have hr_zero : r = 0 := le_antisymm hr_pos hr_nn
          subst hr_zero
          show y ∈ ({0} : Set (ℝ × ℝ × ℝ))
          rw [hy_eq]
          simp [Prod.mk.injEq]
      · -- backward: y ∈ ψ '' S ∪ {0} → y ∈ cone.
        rintro (⟨⟨r, x⟩, hp_mem, hy_eq⟩ | h_zero)
        · -- y = ψ(r, x) with (r, x) ∈ S.
          rw [hS_def] at hp_mem
          obtain ⟨⟨hr_pos, hr_le⟩, hx⟩ := hp_mem
          refine ⟨x, hx, r, ⟨hr_pos.le, hr_le⟩, ?_⟩
          rw [hψ_def] at hy_eq
          rw [← hy_eq]
        · -- y = 0. Use r = 0 and any x ∈ s ∩ V.
          obtain ⟨x₀, hx₀⟩ := h_ne
          have h_zero' : y = (0, 0, 0) := h_zero
          refine ⟨x₀, hx₀, 0, ⟨le_refl 0, by norm_num⟩, ?_⟩
          rw [h_zero']
          simp [Prod.mk.injEq]
    rw [h_cone]
    exact h_image_meas.union (MeasurableSet.singleton 0)
  · -- (s ∩ V).Nonempty fails: s ∩ V = ∅, cone = ∅.
    rw [show (s ∩ V_disc_plus_1) = ∅ from Set.not_nonempty_iff_eq_empty.mp h_ne, cone_empty]
    exact MeasurableSet.empty

/-- The cone-volume set function: `Ω ↦ vol_ℝ³(C(Ω ∩ V_disc,+1))`. -/
noncomputable def coneVolFn (Ω : Set (ℝ × ℝ × ℝ)) : ENNReal :=
  MeasureTheory.volume (cone (Ω ∩ V_disc_plus_1))

@[simp] lemma coneVolFn_empty : coneVolFn ∅ = 0 := by simp [coneVolFn, cone_empty]

/-- **σ-additivity of `coneVolFn` on disjoint Borel sets**. Uses
`cone_inter_V_measurableSet` (Lusin-Souslin) to make the cones measurable
and `cone_inter_subset_zero` to make them AEDisjoint. -/
lemma coneVolFn_iUnion_disjoint {A : ℕ → Set (ℝ × ℝ × ℝ)}
    (h_meas : ∀ i, MeasurableSet (A i)) (h_disj : Pairwise (Function.onFun Disjoint A)) :
    coneVolFn (⋃ i, A i) = ∑' i, coneVolFn (A i) := by
  unfold coneVolFn
  rw [Set.iUnion_inter, cone_iUnion]
  refine MeasureTheory.measure_iUnion₀ ?_ ?_
  · -- AEDisjoint: cones intersect ⊂ {0}, which has measure 0.
    intro i j hij
    have h_d : Disjoint (A i ∩ V_disc_plus_1) (A j ∩ V_disc_plus_1) :=
      (h_disj hij).mono Set.inter_subset_left Set.inter_subset_left
    have h_sub : cone (A i ∩ V_disc_plus_1) ∩ cone (A j ∩ V_disc_plus_1) ⊆ {0} :=
      cone_inter_subset_zero Set.inter_subset_right Set.inter_subset_right h_d
    exact MeasureTheory.measure_mono_null h_sub volume_singleton_zero
  · -- NullMeasurable: cones are Borel by Lusin-Souslin.
    intro i
    exact (cone_inter_V_measurableSet (h_meas i)).nullMeasurableSet

/-- The GL₂(ℝ)-invariant measure `μ_disc,+1` on `V_disc,+1(ℝ)` from ELMV §1.1,
defined directly on Borel sets via `Ω ↦ vol_ℝ³(C(Ω ∩ V_disc,+1))`. The
σ-additivity holds by `coneVolFn_iUnion_disjoint` (Lusin-Souslin makes the
cones Borel; their AEDisjointness comes from `cone_inter_subset_zero`). -/
noncomputable def μ_disc_plus_1 : MeasureTheory.Measure (ℝ × ℝ × ℝ) :=
  MeasureTheory.Measure.ofMeasurable
    (fun s _ => coneVolFn s)
    coneVolFn_empty
    (fun f hf_meas hf_disj => coneVolFn_iUnion_disjoint hf_meas hf_disj)

@[simp] lemma μ_disc_plus_1_apply {s : Set (ℝ × ℝ × ℝ)} (hs : MeasurableSet s) :
    μ_disc_plus_1 s = coneVolFn s :=
  MeasureTheory.Measure.ofMeasurable_apply _ hs

/-- **Local finiteness of `μ_disc_plus_1`**: every point has a neighborhood of
finite measure. The bound: `μ(B(x, 1)) ≤ vol(closedBall 0 (|x| + 1)) < ∞`
because `cone(B(x, 1) ∩ V) ⊆ closedBall 0 (|x| + 1)` (a cone of a bounded
set, with the radius factor in `[0, 1]`, can only shrink). -/
instance μ_disc_plus_1_isLocallyFiniteMeasure :
    MeasureTheory.IsLocallyFiniteMeasure μ_disc_plus_1 where
  finiteAtNhds x := by
    refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
    rw [μ_disc_plus_1_apply Metric.isOpen_ball.measurableSet]
    unfold coneVolFn
    -- cone(B(x, 1) ∩ V) ⊆ closedBall 0 (1 + dist x 0).
    have h_sub : cone (Metric.ball x 1 ∩ V_disc_plus_1)
        ⊆ Metric.closedBall (0 : ℝ × ℝ × ℝ) (1 + dist x 0) := by
      rintro z ⟨y, ⟨hy_ball, _⟩, r, ⟨hr_nn, hr_le⟩, hz_eq⟩
      -- dist(z, 0) = r · dist(y, 0) ≤ dist(y, 0) ≤ 1 + dist(x, 0).
      have hy_dist : dist y 0 < 1 + dist x 0 := by
        calc dist y 0 ≤ dist y x + dist x 0 := dist_triangle y x 0
          _ < 1 + dist x 0 := by linarith [Metric.mem_ball.mp hy_ball]
      -- z = (r·y.1, r·y.2.1, r·y.2.2). dist(z, 0) = max scaling.
      have h_z_dist : dist z 0 = r * dist y 0 := by
        rw [hz_eq]
        simp only [dist_zero_right]
        -- (r * y.1, r * y.2.1, r * y.2.2) = r • y
        have h_eq : ((r * y.1, r * y.2.1, r * y.2.2) : ℝ × ℝ × ℝ) = r • y := by
          obtain ⟨y1, y2, y3⟩ := y
          simp [Prod.smul_def]
        rw [h_eq, norm_smul]
        simp [abs_of_nonneg hr_nn]
      simp only [Metric.mem_closedBall]
      calc dist z 0 = r * dist y 0 := h_z_dist
        _ ≤ 1 * dist y 0 := mul_le_mul_of_nonneg_right hr_le dist_nonneg
        _ = dist y 0 := by ring
        _ ≤ 1 + dist x 0 := hy_dist.le
    calc MeasureTheory.volume (cone (Metric.ball x 1 ∩ V_disc_plus_1))
        ≤ MeasureTheory.volume (Metric.closedBall (0 : ℝ × ℝ × ℝ) (1 + dist x 0)) :=
          MeasureTheory.measure_mono h_sub
      _ < ⊤ := MeasureTheory.measure_closedBall_lt_top

/-- `coneVolFn` is monotone in its set argument: larger sets give larger
cone volumes. -/
lemma coneVolFn_mono {Ω₁ Ω₂ : Set (ℝ × ℝ × ℝ)} (h : Ω₁ ⊆ Ω₂) :
    coneVolFn Ω₁ ≤ coneVolFn Ω₂ := by
  unfold coneVolFn
  apply MeasureTheory.measure_mono
  exact cone_mono (Set.inter_subset_inter_left _ h)

/-- `coneVolFn` is countably subadditive: covering a set by countably many
pieces gives an upper bound on its cone volume by the sum of the pieces'
cone volumes. -/
lemma coneVolFn_iUnion_le (s : ℕ → Set (ℝ × ℝ × ℝ)) :
    coneVolFn (⋃ i, s i) ≤ ∑' i, coneVolFn (s i) := by
  unfold coneVolFn
  rw [show (⋃ i, s i) ∩ V_disc_plus_1 = ⋃ i, s i ∩ V_disc_plus_1 by
    rw [Set.iUnion_inter]]
  rw [cone_iUnion]
  exact MeasureTheory.measure_iUnion_le _

/-- For any cover `t : ℕ → Set ℝ³` of `s`, `coneVolFn(s) ≤ Σ coneVolFn(t i)`. -/
lemma coneVolFn_le_iUnion (s : Set (ℝ × ℝ × ℝ)) (t : ℕ → Set (ℝ × ℝ × ℝ))
    (h_cov : s ⊆ ⋃ i, t i) :
    coneVolFn s ≤ ∑' i, coneVolFn (t i) :=
  (coneVolFn_mono h_cov).trans (coneVolFn_iUnion_le t)

/-- **Key lower bound**: `coneVolFn` is everywhere bounded above by the
metric outer measure constructed from it. -/
lemma coneVolFn_le_mkMetric'_outer (s : Set (ℝ × ℝ × ℝ)) :
    coneVolFn s ≤ MeasureTheory.OuterMeasure.mkMetric' coneVolFn s := by
  rw [MeasureTheory.OuterMeasure.mkMetric'.eq_iSup_nat]
  simp only [MeasureTheory.OuterMeasure.iSup_apply]
  refine le_iSup_of_le 1 ?_
  -- Goal: coneVolFn s ≤ pre coneVolFn 1⁻¹ s.
  set r : ENNReal := ((1 : ℕ) : ENNReal)⁻¹
  show coneVolFn s ≤ MeasureTheory.OuterMeasure.mkMetric'.pre coneVolFn r s
  rw [MeasureTheory.OuterMeasure.mkMetric'.pre,
    MeasureTheory.OuterMeasure.boundedBy_apply]
  refine le_iInf fun t => le_iInf fun h_cov => ?_
  refine (coneVolFn_le_iUnion s t h_cov).trans ?_
  apply ENNReal.tsum_le_tsum
  intro n
  rcases (t n).eq_empty_or_nonempty with h_e | h_n
  · simp [h_e]
  · rw [iSup_pos h_n]
    by_cases h_diam : EMetric.diam (t n) ≤ r
    · -- ediam (t n) ≤ r: extend value = coneVolFn (t n).
      change coneVolFn (t n) ≤ ⨅ _ : EMetric.diam (t n) ≤ r, coneVolFn (t n)
      rw [iInf_pos h_diam]
    · -- ediam (t n) > r: extend value = ⊤.
      change coneVolFn (t n) ≤ ⨅ _ : EMetric.diam (t n) ≤ r, coneVolFn (t n)
      rw [iInf_neg h_diam]
      exact le_top

/-- The cone-volume `coneVolFn` equals the Borel measure `μ_disc_plus_1`
on Borel sets. -/
lemma coneVolFn_eq_μ_disc_plus_1 (s : Set (ℝ × ℝ × ℝ)) (hs : MeasurableSet s) :
    coneVolFn s = μ_disc_plus_1 s := (μ_disc_plus_1_apply hs).symm

/-- The cone-volume `coneVolFn` is dominated by the cone-volume Borel measure
`μ_disc_plus_1` on Borel sets (equality, in fact). -/
lemma coneVolFn_le_μ_disc_plus_1 (s : Set (ℝ × ℝ × ℝ)) (hs : MeasurableSet s) :
    coneVolFn s ≤ μ_disc_plus_1 s := (coneVolFn_eq_μ_disc_plus_1 s hs).le

/-- The discriminant function on triples. -/
def discFn : ℝ × ℝ × ℝ → ℝ := fun z => z.2.1^2 - 4 * z.1 * z.2.2

/-- The discriminant function is continuous. -/
lemma discFn_continuous : Continuous discFn := by
  unfold discFn; fun_prop

/-- The discriminant of `p/2` for `p ∈ V_disc,+1` equals `1/4`. -/
lemma discFn_half (p : ℝ × ℝ × ℝ) (hp : p ∈ V_disc_plus_1) :
    discFn (p.1 / 2, p.2.1 / 2, p.2.2 / 2) = 1/4 := by
  have : p.2.1^2 - 4 * p.1 * p.2.2 = 1 := hp
  unfold discFn
  show (p.2.1 / 2)^2 - 4 * (p.1 / 2) * (p.2.2 / 2) = 1/4
  field_simp
  linarith

/-- The "reconstruction" map: send a point `y ∈ ℝ³` with `discFn y > 0` to the
point `y / √(discFn y) ∈ V_disc,+1`. Combined with `√(discFn y)` as the scaling
factor, this gives the inverse to the cone map at non-conical points. -/
noncomputable def qFn : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun y =>
  let r := Real.sqrt (discFn y)
  (y.1 / r, y.2.1 / r, y.2.2 / r)

/-- For `p ∈ V_disc,+1`, `qFn (p/2) = p`. -/
lemma qFn_half (p : ℝ × ℝ × ℝ) (hp : p ∈ V_disc_plus_1) :
    qFn (p.1 / 2, p.2.1 / 2, p.2.2 / 2) = p := by
  unfold qFn
  show (p.1/2 / Real.sqrt (discFn (p.1/2, p.2.1/2, p.2.2/2)),
        p.2.1/2 / Real.sqrt (discFn (p.1/2, p.2.1/2, p.2.2/2)),
        p.2.2/2 / Real.sqrt (discFn (p.1/2, p.2.1/2, p.2.2/2))) = p
  rw [discFn_half p hp]
  rw [show (1:ℝ)/4 = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)]
  obtain ⟨a, b, c⟩ := p
  show (a/2 / (1/2), b/2 / (1/2), c/2 / (1/2)) = (a, b, c)
  have h1 : a/2 / (1/2 : ℝ) = a := by ring
  have h2 : b/2 / (1/2 : ℝ) = b := by ring
  have h3 : c/2 / (1/2 : ℝ) = c := by ring
  rw [h1, h2, h3]

/-- `qFn` is continuous at any point with `discFn > 0`. -/
lemma qFn_continuousAt {y : ℝ × ℝ × ℝ} (hy : 0 < discFn y) :
    ContinuousAt qFn y := by
  have h_sqrt_cont : ContinuousAt (fun z => Real.sqrt (discFn z)) y :=
    Real.continuous_sqrt.continuousAt.comp discFn_continuous.continuousAt
  have h_sqrt_ne : Real.sqrt (discFn y) ≠ 0 := by
    rw [Real.sqrt_ne_zero']
    exact hy
  unfold qFn
  refine ContinuousAt.prodMk ?_ ?_
  · exact (continuous_fst.continuousAt).div h_sqrt_cont h_sqrt_ne
  · refine ContinuousAt.prodMk ?_ ?_
    · exact (continuous_snd.fst.continuousAt).div h_sqrt_cont h_sqrt_ne
    · exact (continuous_snd.snd.continuousAt).div h_sqrt_cont h_sqrt_ne

/-- **Geometric lemma**: for `p ∈ V_disc,+1` and `ε > 0`, there's a small ball
`B(p/2, δ)` contained in `cone(B(p, ε) ∩ V_disc,+1)`. -/
lemma cone_contains_ball_around_half {p : ℝ × ℝ × ℝ} (hp : p ∈ V_disc_plus_1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ),
      Metric.ball ((p.1 / 2, p.2.1 / 2, p.2.2 / 2) : ℝ × ℝ × ℝ) δ
        ⊆ cone (Metric.ball p ε ∩ V_disc_plus_1) := by
  set y₀ : ℝ × ℝ × ℝ := (p.1 / 2, p.2.1 / 2, p.2.2 / 2)
  -- discFn y₀ = 1/4 > 0.
  have h_disc_y₀ : discFn y₀ = 1/4 := discFn_half p hp
  have h_disc_y₀_pos : 0 < discFn y₀ := by rw [h_disc_y₀]; norm_num
  -- discFn is continuous; get δ_A with discFn y > 1/8 on B(y₀, δ_A).
  have hA : ∃ δ_A > 0, ∀ y ∈ Metric.ball y₀ δ_A, (1:ℝ)/8 < discFn y := by
    have h_pos : (1:ℝ)/8 < discFn y₀ := by rw [h_disc_y₀]; norm_num
    have h_at : ContinuousAt discFn y₀ := discFn_continuous.continuousAt
    -- {z : 1/8 < discFn z} is open, contains y₀ ⟹ neighborhood ⟹ δ_A.
    have h_open : IsOpen {z | (1:ℝ)/8 < discFn z} :=
      (isOpen_lt continuous_const discFn_continuous)
    have h_mem : y₀ ∈ {z | (1:ℝ)/8 < discFn z} := h_pos
    obtain ⟨δ_A, hδ_A_pos, h_ball⟩ := Metric.isOpen_iff.mp h_open y₀ h_mem
    exact ⟨δ_A, hδ_A_pos, h_ball⟩
  -- discFn y < 3/8 on B(y₀, δ_B) (so r < 1).
  have hB : ∃ δ_B > 0, ∀ y ∈ Metric.ball y₀ δ_B, discFn y < (3:ℝ)/8 := by
    have h_lt : discFn y₀ < (3:ℝ)/8 := by rw [h_disc_y₀]; norm_num
    have h_open : IsOpen {z | discFn z < (3:ℝ)/8} :=
      (isOpen_lt discFn_continuous continuous_const)
    obtain ⟨δ_B, hδ_B_pos, h_ball⟩ := Metric.isOpen_iff.mp h_open y₀ h_lt
    exact ⟨δ_B, hδ_B_pos, h_ball⟩
  -- dist(qFn y, p) < ε on B(y₀, δ_C). (Use ContinuousAt qFn.)
  have hC : ∃ δ_C > 0, ∀ y ∈ Metric.ball y₀ δ_C, dist (qFn y) p < ε := by
    have h_q_at : ContinuousAt qFn y₀ := qFn_continuousAt h_disc_y₀_pos
    have h_q_eq : qFn y₀ = p := qFn_half p hp
    -- Use ContinuousAt to get a Metric.ball neighborhood.
    rw [Metric.continuousAt_iff] at h_q_at
    obtain ⟨δ_C, hδ_C_pos, h_ball⟩ := h_q_at ε hε
    refine ⟨δ_C, hδ_C_pos, fun y hy => ?_⟩
    have h_dy : dist y y₀ < δ_C := Metric.mem_ball.mp hy
    have := h_ball h_dy
    rw [h_q_eq] at this
    exact this
  obtain ⟨δ_A, hδ_A, hA⟩ := hA
  obtain ⟨δ_B, hδ_B, hB⟩ := hB
  obtain ⟨δ_C, hδ_C, hC⟩ := hC
  refine ⟨min δ_A (min δ_B δ_C), lt_min hδ_A (lt_min hδ_B hδ_C), ?_⟩
  intro y hy
  have hy_A : y ∈ Metric.ball y₀ δ_A :=
    Metric.ball_subset_ball (min_le_left _ _) hy
  have hy_B : y ∈ Metric.ball y₀ δ_B :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hy
  have hy_C : y ∈ Metric.ball y₀ δ_C :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hy
  have h_disc_pos : (1:ℝ)/8 < discFn y := hA y hy_A
  have h_disc_lt : discFn y < (3:ℝ)/8 := hB y hy_B
  have h_q_close : dist (qFn y) p < ε := hC y hy_C
  -- Show y ∈ cone(B(p, ε) ∩ V).
  -- y = √(discFn y) · qFn y, qFn y ∈ V, √(discFn y) ∈ (0, 1).
  refine ⟨qFn y, ?_, Real.sqrt (discFn y), ?_, ?_⟩
  · -- qFn y ∈ B(p, ε) ∩ V_disc_plus_1
    refine ⟨Metric.mem_ball.mpr h_q_close, ?_⟩
    -- qFn y ∈ V_disc_plus_1: discFn (qFn y) = 1
    show (qFn y).2.1^2 - 4 * (qFn y).1 * (qFn y).2.2 = 1
    show (y.2.1 / Real.sqrt (discFn y))^2 - 4 * (y.1 / Real.sqrt (discFn y))
          * (y.2.2 / Real.sqrt (discFn y)) = 1
    have h_pos' : 0 < discFn y := by linarith
    have hr_ne : Real.sqrt (discFn y) ≠ 0 := Real.sqrt_ne_zero'.mpr h_pos'
    have hr_sq : (Real.sqrt (discFn y))^2 = discFn y := Real.sq_sqrt h_pos'.le
    field_simp
    nlinarith [hr_sq, show y.2.1^2 - 4 * y.1 * y.2.2 = discFn y from rfl]
  · -- Real.sqrt (discFn y) ∈ Icc 0 1
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    have : discFn y < 1 := by linarith
    calc Real.sqrt (discFn y) ≤ Real.sqrt 1 :=
          Real.sqrt_le_sqrt this.le
      _ = 1 := Real.sqrt_one
  · -- y = (r * qFn y .1, r * qFn y .2.1, r * qFn y .2.2)
    have h_pos' : 0 < discFn y := by linarith
    have hr_ne : Real.sqrt (discFn y) ≠ 0 := Real.sqrt_ne_zero'.mpr h_pos'
    obtain ⟨y1, y2, y3⟩ := y
    show (y1, y2, y3) = (Real.sqrt _ * (y1 / Real.sqrt _),
                          Real.sqrt _ * (y2 / Real.sqrt _),
                          Real.sqrt _ * (y3 / Real.sqrt _))
    have h1 : Real.sqrt (discFn (y1, y2, y3)) * (y1 / Real.sqrt (discFn (y1, y2, y3))) = y1 := by
      field_simp
    have h2 : Real.sqrt (discFn (y1, y2, y3)) * (y2 / Real.sqrt (discFn (y1, y2, y3))) = y2 := by
      field_simp
    have h3 : Real.sqrt (discFn (y1, y2, y3)) * (y3 / Real.sqrt (discFn (y1, y2, y3))) = y3 := by
      field_simp
    rw [h1, h2, h3]

/-- **Positivity of cone volume on balls**: for `p ∈ V_disc,+1` and `ε > 0`,
`coneVolFn(B(p, ε)) > 0`. -/
lemma coneVolFn_pos_of_ball {p : ℝ × ℝ × ℝ} (hp : p ∈ V_disc_plus_1)
    {ε : ℝ} (hε : 0 < ε) :
    0 < coneVolFn (Metric.ball p ε) := by
  obtain ⟨δ, hδ, hsub⟩ := cone_contains_ball_around_half hp hε
  set y₀ : ℝ × ℝ × ℝ := (p.1 / 2, p.2.1 / 2, p.2.2 / 2)
  -- vol(B(y₀, δ)) > 0 since Lebesgue is IsOpenPosMeasure.
  have h_pos : 0 < MeasureTheory.volume (Metric.ball y₀ δ) := by
    exact Metric.isOpen_ball.measure_pos _ ⟨y₀, Metric.mem_ball_self hδ⟩
  -- coneVolFn(B(p, ε)) = vol(cone(B(p, ε) ∩ V)) ≥ vol(B(y₀, δ)) > 0.
  unfold coneVolFn
  exact lt_of_lt_of_le h_pos (MeasureTheory.measure_mono hsub)

/-- **Positivity of μ on balls** centered at `V_disc,+1` points. -/
lemma μ_disc_plus_1_pos_of_ball {p : ℝ × ℝ × ℝ} (hp : p ∈ V_disc_plus_1)
    {ε : ℝ} (hε : 0 < ε) :
    0 < μ_disc_plus_1 (Metric.ball p ε) :=
  lt_of_lt_of_le (coneVolFn_pos_of_ball hp hε)
    (coneVolFn_le_μ_disc_plus_1 _ Metric.isOpen_ball.measurableSet)

/-- **Urysohn bump function** centered at `p ∈ V_disc,+1`: there exists a
nonneg continuous compactly supported `f : ℝ³ → ℝ` with `f = 1` on
`closedBall p (ε/2)`, `f = 0` outside `ball p ε`, and `0 ≤ f ≤ 1`. -/
lemma exists_urysohn_bump {p : ℝ × ℝ × ℝ}
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : (ℝ × ℝ × ℝ) → ℝ,
      Continuous f ∧ HasCompactSupport f ∧ (∀ x, 0 ≤ f x) ∧
        (∀ x ∈ Metric.closedBall p (ε/2), f x = 1) ∧
        Function.support f ⊆ Metric.ball p ε := by
  have h_compact : IsCompact (Metric.closedBall p (ε/2)) := isCompact_closedBall p (ε/2)
  have h_closed : IsClosed (Metric.ball p ε)ᶜ := Metric.isOpen_ball.isClosed_compl
  have h_disjoint : Disjoint (Metric.closedBall p (ε/2)) (Metric.ball p ε)ᶜ := by
    rw [Set.disjoint_compl_right_iff_subset]
    intro x hx
    have : dist x p ≤ ε/2 := hx
    exact Metric.mem_ball.mpr (lt_of_le_of_lt this (by linarith))
  obtain ⟨f_cm, hf_one, hf_zero, hf_compact, hf_Icc⟩ :=
    exists_continuous_one_zero_of_isCompact h_compact h_closed h_disjoint
  refine ⟨f_cm, f_cm.continuous, hf_compact, fun x => (hf_Icc x).1, hf_one, ?_⟩
  intro x hx
  by_contra h_not
  have h_in : x ∈ (Metric.ball p ε)ᶜ := h_not
  exact hx (hf_zero h_in)

/-- **Urysohn bump function with positive integral** centered at
`p ∈ V_disc,+1`: there exists a nonneg continuous compactly supported
`f : ℝ³ → ℝ` with support in `ball p ε` and `∫ f dμ_disc_plus_1 > 0`. -/
lemma exists_bump_with_pos_integral {p : ℝ × ℝ × ℝ} (hp : p ∈ V_disc_plus_1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : (ℝ × ℝ × ℝ) → ℝ,
      Continuous f ∧ HasCompactSupport f ∧ (∀ x, 0 ≤ f x) ∧
        Function.support f ⊆ Metric.ball p ε ∧
        0 < ∫ x, f x ∂μ_disc_plus_1 := by
  obtain ⟨f, hf_cont, hf_supp, hf_nn, hf_one, hf_subset⟩ := exists_urysohn_bump (p := p) hε
  refine ⟨f, hf_cont, hf_supp, hf_nn, hf_subset, ?_⟩
  -- ∫ f dμ > 0 via integral_pos_iff_support_of_nonneg.
  have hf_integrable : MeasureTheory.Integrable f μ_disc_plus_1 :=
    hf_cont.integrable_of_hasCompactSupport hf_supp
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg hf_nn hf_integrable]
  -- μ(support f) > 0 since support f ⊇ ball p (ε/2) which has positive measure.
  have h_subset : Metric.ball p (ε/2) ⊆ Function.support f := by
    intro x hx
    have hx_closed : x ∈ Metric.closedBall p (ε/2) := Metric.ball_subset_closedBall hx
    have : f x = 1 := hf_one x hx_closed
    simp [Function.support, this]
  exact lt_of_lt_of_le (μ_disc_plus_1_pos_of_ball hp (by linarith))
    (MeasureTheory.measure_mono h_subset)

/-! #### Step 1: existence of a representation in any open patch of V_disc,+1

The next step is to derive an `existence-in-open` consequence of `theorem_2_3`.
The argument:

1. **Geometric lemma**: for `p ∈ V_disc,+1`, the cone `cone(B(p,ε) ∩ V_disc,+1)`
   contains a 3D ball `B(p/2, δ)` for some `δ > 0`. This is because for `z` near
   `p/2`, `r := √(disc(z))` is near `1/2 ∈ (0,1)`, `q := z/r` is in `V` (has
   `disc 1`) and near `p`, and `z = r · q`. Hence `B(p,ε) ∩ V` contains a
   neighborhood of `p`, and the cone contains a 3D ball.

2. **Positivity**: `coneVolFn(B(p,ε)) = vol_ℝ³(cone(...)) ≥ vol_ℝ³(B(p/2,δ)) > 0`
   by `IsOpen.measure_pos` (Lebesgue measure has `IsOpenPosMeasure`).

3. **Lifting to μ**: `μ_disc_plus_1(B(p,ε)) ≥ coneVolFn(B(p,ε)) > 0` via
   `coneVolFn_le_μ_disc_plus_1`.

4. **Bump function via Urysohn**: in any nonempty open `U ⊂ ℝ³` whose
   intersection with `V_disc,+1` is nonempty, there's a continuous
   compactly-supported `φ ≥ 0` with `supp(φ) ⊂ U` and `φ(p) > 0`.

5. **Integral positivity**: `∫ φ dμ_disc_plus_1 ≥ φ(p) · μ(small_ball(p)) > 0`.

6. **Tendsto extraction**: `theorem_2_3` gives `λ_d(φ) / vol_G(d) → ∫φ dμ > 0`.
   Eventually the sum `λ_d(φ)` is positive, hence at least one `t ∈ R_disc(4n)`
   has `φ(t/(2√n)) > 0`, i.e., `t/(2√n) ∈ supp(φ) ⊂ U`.

This chain provides `existence-in-open`. Combined with the Pell-matrix parity
correction (proved as `g/hAction_parity_matches` above), it derives
`duke_theorem`. -/

/-
Definition of Omega_strict and proof that it is non-empty.
-/
def Omega_strict : Set (ℝ × ℝ × ℝ) :=
  { t | t ∈ V_disc_plus_1 ∧ |t.1 - t.2.2| < 1 ∧ |t.2.1| < 1 ∧ |t.1 + t.2.2| < 1 }

theorem Omega_strict_nonempty : Omega_strict.Nonempty := by
  use (-3/8, 1/2, 1/2)
  dsimp [Omega_strict, V_disc_plus_1]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-
Projection to hyperboloid.
-/
noncomputable def project_to_hyperboloid (n : ℤ) (t : ℤ × ℤ × ℤ) : ℝ × ℝ × ℝ :=
  let s := Real.sqrt (4 * (n : ℝ))
  ((t.1 : ℝ) / s, (t.2.1 : ℝ) / s, (t.2.2 : ℝ) / s)

/-
Statement of Duke's Theorem adapted for Problem 1148, restricted to non-square
`n` (matching the non-square restriction in ELMV Theorem 2.3 from which it is
derived). The case `n = m²` is handled separately in `erdos_1148`.
-/
def DukeTheoremStatement : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, n ≥ N → ¬ IsSquare n →
  ∃ t ∈ R_star_disc (4 * n),
    project_to_hyperboloid n t ∈ Omega_strict ∧
    t.1 % 2 = t.2.2 % 2

/-! ### ELMV Theorem 2.3

The unconditional equidistribution result for non-square positive
discriminants due to Einsiedler-Lindenstrauss-Michel-Venkatesh
[ELMV12, Theorem 2.3], in the point-form consequence displayed
immediately after the theorem on page 15. -/

/-- **ELMV Theorem 2.3 in point form** — the displayed equation in ELMV [ELMV12]
immediately following the named Theorem 2.3 statement (page 15):

> `λ_d(ϕ_A) = ν_d(ϕ_Γ) = vol(G_d) µ_d(ϕ_Γ) = vol(G_d)(µ_{Γ\G}(ϕ_Γ) + o(1))`
> `= vol(G_d)(µ_{G/A}(ϕ_A) + o(1))`

Here:
* `λ_d(ϕ)` is the discrete measure `∑_{x ∈ R_disc(d)} ϕ(|d|^{-1/2}·x)` on
  `G/A ≃ V_disc,+1(ℝ)` (via §2.4 of the paper);
* `vol(G_d)` is the volume of the union of A-orbits, equal to
  `|Pic(O_d)|·Reg(O_d) = |d|^{1/2+o(1)}` (paper eq. 2.9);
* `µ_{G/A}` is the cone-volume measure `µ_disc,+1` under the identification.

Rewritten as `λ_d(ϕ) / vol(G_d) → µ_disc,+1(ϕ)` as `d = 4n → ∞`,
amongst **non-square** positive discriminants. -/
axiom theorem_2_3 :
    ∃ vol_G : ℤ → ℝ,
      (∀ n : ℤ, 0 < n → ¬ IsSquare n → 0 < vol_G (4 * n)) ∧
      (∀ f : (ℝ × ℝ × ℝ) → ℝ,
        Continuous f → HasCompactSupport f →
        Filter.Tendsto
          (fun n : ℤ =>
            (∑' t : R_star_disc (4 * n), f (project_to_hyperboloid n t.val))
              / vol_G (4 * n))
          (Filter.atTop ⊓ Filter.principal {n : ℤ | ¬ IsSquare n})
          (nhds (∫ x, f x ∂μ_disc_plus_1)))

/-! ### Deriving Duke's theorem (with parity) from Theorem 2.3

Chojecki's proof (see [erdosproblems.com/forum/thread/1148#post-4849] and
the linked note) splits as follows:

* From Theorem 2.3's equidistribution, taking `f` to be a nonnegative bump
  function on an open `Ω ⊂ V_disc,+1`, the existence of a representation
  `t ∈ R_disc(4n)` with `t/(2√n) ∈ Ω` follows for `n` sufficiently large.
* The parity condition `a ≡ c (mod 2)` is then enforced using Pell numbers
  `p_k, q_k, r_k` (from `v_k + u_k√2 = (21 + 15√2)(17 + 12√2)^k`) and
  matrices `g_k = (-p_k, q_k; q_k, -r_k)`, `h_k = (q_k, -r_k; p_k, -q_k)`
  acting on the discriminant form. Both matrices preserve the discriminant
  `b² − 4ac = 4n`, swap parity of `(a, c)`, and (for `k` large) keep the
  projection inside an open neighborhood. -/

/-! #### Pell-matrix data (Chojecki, k = 0 case)

The smallest Pell parameters from the recurrence
`v_k + u_k √2 = (21 + 15√2)(17 + 12√2)^k` at `k = 0`:
`v₀ = 21`, `u₀ = 15`, hence `q₀ = (v₀-1)/4 = 5`, `p₀ = (u₀+2q₀+1)/2 = 13`,
`r₀ = (u₀-2q₀-1)/2 = 2`. The corresponding GL₂(ℤ)-matrices are
`g₀ = (-p₀,  q₀;  q₀, -r₀) = (-13, 5; 5, -2)` and
`h₀ = ( q₀, -r₀;  p₀, -q₀) = (  5,-2; 13,-5)`.
Both have determinant `1`. They act on a discriminant form `(a, b, c)`
(satisfying `b² − 4ac = 4n`) by the standard formula
`(α, β; γ, δ) · (A, B, C) = (α²A + αγB + γ²C, 2αβA + (αδ+βγ)B + 2γδC,
β²A + βδB + δ²C)`. -/

/-- Action of `g₀ = (-13, 5; 5, -2)` on a triple `(a, b, c)`. -/
def gAction (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (169 * t.1 - 65 * t.2.1 + 25 * t.2.2,
   -130 * t.1 + 51 * t.2.1 - 20 * t.2.2,
   25 * t.1 - 10 * t.2.1 + 4 * t.2.2)

/-- Action of `h₀ = (5, -2; 13, -5)` on a triple `(a, b, c)`. -/
def hAction (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (25 * t.1 + 65 * t.2.1 + 169 * t.2.2,
   -20 * t.1 - 51 * t.2.1 - 130 * t.2.2,
   4 * t.1 + 10 * t.2.1 + 25 * t.2.2)

/-- `g₀` preserves the discriminant `b² − 4ac`. -/
lemma gAction_preserves_disc (t : ℤ × ℤ × ℤ) :
    (gAction t).2.1 ^ 2 - 4 * (gAction t).1 * (gAction t).2.2
      = t.2.1 ^ 2 - 4 * t.1 * t.2.2 := by
  unfold gAction
  ring

/-- `h₀` preserves the discriminant `b² − 4ac`. -/
lemma hAction_preserves_disc (t : ℤ × ℤ × ℤ) :
    (hAction t).2.1 ^ 2 - 4 * (hAction t).1 * (hAction t).2.2
      = t.2.1 ^ 2 - 4 * t.1 * t.2.2 := by
  unfold hAction
  ring

/-- After `gAction`, the new `(a', c')` always have the same parity (mod 2),
provided the input `b` is even and `(a, c) ≢ (0, 0) (mod 2)`. -/
lemma gAction_parity_matches (t : ℤ × ℤ × ℤ)
    (hb : t.2.1 % 2 = 0) (hac : t.2.2 % 2 = 0) :
    (gAction t).1 % 2 = (gAction t).2.2 % 2 := by
  unfold gAction
  simp only
  omega

/-- After `hAction`, the new `(a', c')` always have the same parity (mod 2),
provided the input `b` is even and the input `a` is even. -/
lemma hAction_parity_matches (t : ℤ × ℤ × ℤ)
    (hb : t.2.1 % 2 = 0) (ha : t.1 % 2 = 0) :
    (hAction t).1 % 2 = (hAction t).2.2 % 2 := by
  unfold hAction
  simp only
  omega

/-- **Existence in any open ball at a point of V_disc,+1** (consequence of
`theorem_2_3`): for any `p ∈ V_disc,+1` and `ε > 0`, eventually for `n` large
*and non-square*, some `t ∈ R_star_disc(4n)` has projection in `B(p, ε)`. -/
lemma exists_projection_in_ball {p : ℝ × ℝ × ℝ} (hp : p ∈ V_disc_plus_1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℤ, ∀ n : ℤ, n ≥ N → ¬ IsSquare n →
      ∃ t : R_star_disc (4 * n), project_to_hyperboloid n t.val ∈ Metric.ball p ε := by
  -- Build bump function with positive integral.
  obtain ⟨f, hf_cont, hf_supp, hf_nn, hf_subset, hf_int_pos⟩ :=
    exists_bump_with_pos_integral hp hε
  -- Apply theorem_2_3: sum / vol_G → ∫f, where ∫f > 0.
  obtain ⟨vol_G, h_vol_pos, h_lim⟩ := theorem_2_3
  have h_lim_f := h_lim f hf_cont hf_supp
  -- Eventually the ratio is > ½ · ∫f > 0.
  have h_evt := h_lim_f.eventually (eventually_gt_nhds
    (show (1:ℝ)/2 * (∫ x, f x ∂μ_disc_plus_1) < ∫ x, f x ∂μ_disc_plus_1 by linarith))
  rw [Filter.eventually_inf_principal] at h_evt
  rw [Filter.eventually_atTop] at h_evt
  obtain ⟨N, hN⟩ := h_evt
  refine ⟨max N 1, fun n hn hn_nsq => ?_⟩
  have hnN : n ≥ N := le_trans (le_max_left N 1) hn
  have hn1 : n ≥ 1 := le_trans (le_max_right N 1) hn
  have h_ratio_pos := hN n hnN hn_nsq
  have h_vol_pos_n : 0 < vol_G (4 * n) := h_vol_pos n (by linarith) hn_nsq
  -- Sum/vol > ½∫f > 0 and vol > 0 imply Sum > 0.
  have h_sum_pos : 0 <
      (∑' t : R_star_disc (4 * n), f (project_to_hyperboloid n t.val)) := by
    by_contra h_no
    push_neg at h_no
    have h_div_nonpos : (∑' t : R_star_disc (4 * n),
        f (project_to_hyperboloid n t.val)) / vol_G (4 * n) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg h_no h_vol_pos_n.le
    linarith
  -- Sum positive ⟹ at least one term positive ⟹ projection in supp(f) ⊂ ball.
  by_contra h_no_ball
  push_neg at h_no_ball
  have h_all_zero : ∀ t : R_star_disc (4 * n), f (project_to_hyperboloid n t.val) = 0 := by
    intro t
    by_contra h_ne
    have h_in_supp : project_to_hyperboloid n t.val ∈ Function.support f := h_ne
    exact h_no_ball t (hf_subset h_in_supp)
  have h_sum_zero : (∑' t : R_star_disc (4 * n), f (project_to_hyperboloid n t.val)) = 0 := by
    have : (fun t : R_star_disc (4 * n) => f (project_to_hyperboloid n t.val))
         = fun _ => 0 := funext h_all_zero
    rw [this, tsum_zero]
  linarith

/-! #### Pell-fixed point and continuity bound -/

/-- Chojecki's distinguished point `P_0 = (5/√221, 11/√221, -5/√221)`, fixed by
the Pell matrix `g₀` (and negated by `h₀`). It lies in `V_disc,+1` and
in `Ω_strict`. -/
noncomputable def P_0 : ℝ × ℝ × ℝ :=
  (5 / Real.sqrt 221, 11 / Real.sqrt 221, -5 / Real.sqrt 221)

/-- `P_0` lies on the hyperboloid `V_disc,+1`. -/
lemma P_0_mem_V : P_0 ∈ V_disc_plus_1 := by
  show (11 / Real.sqrt 221)^2 - 4 * (5 / Real.sqrt 221) * (-5 / Real.sqrt 221) = 1
  have h_sqrt_ne : Real.sqrt 221 ≠ 0 :=
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 221)).ne'
  have h_sq : (Real.sqrt 221)^2 = 221 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 221)
  field_simp
  nlinarith [h_sq, Real.sqrt_nonneg (221 : ℝ)]

/-- `P_0` lies in the open set `Ω_strict`. -/
lemma P_0_mem_Omega_strict : P_0 ∈ Omega_strict := by
  have h_sqrt_pos : 0 < Real.sqrt 221 := Real.sqrt_pos.mpr (by norm_num)
  -- √221 > 11 since 221 > 121 = 11²
  have h_sqrt_gt_11 : (11 : ℝ) < Real.sqrt 221 := by
    have : Real.sqrt 121 = 11 := by
      rw [show (121 : ℝ) = (11 : ℝ)^2 from by norm_num,
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 11)]
    rw [← this]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨P_0_mem_V, ?_, ?_, ?_⟩
  · -- |5/√221 - (-5/√221)| = 10/√221 < 1.
    show |(5 / Real.sqrt 221) - (-5 / Real.sqrt 221)| < 1
    have : (5 / Real.sqrt 221) - (-5 / Real.sqrt 221) = 10 / Real.sqrt 221 := by ring
    rw [this, abs_of_pos (by positivity)]
    rw [div_lt_one h_sqrt_pos]
    linarith
  · -- |11/√221| < 1.
    show |11 / Real.sqrt 221| < 1
    rw [abs_of_pos (by positivity)]
    rw [div_lt_one h_sqrt_pos]
    exact h_sqrt_gt_11
  · -- |5/√221 + (-5/√221)| = 0 < 1.
    show |(5 / Real.sqrt 221) + (-5 / Real.sqrt 221)| < 1
    have : (5 / Real.sqrt 221) + (-5 / Real.sqrt 221) = 0 := by ring
    rw [this, abs_zero]
    norm_num

/-! #### Real-valued Pell matrix actions -/

/-- Real-valued version of `gAction` (same linear map, lifted to `ℝ³`). -/
def gActionReal (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (169 * x.1 - 65 * x.2.1 + 25 * x.2.2,
   -130 * x.1 + 51 * x.2.1 - 20 * x.2.2,
   25 * x.1 - 10 * x.2.1 + 4 * x.2.2)

/-- Real-valued version of `hAction`. -/
def hActionReal (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (25 * x.1 + 65 * x.2.1 + 169 * x.2.2,
   -20 * x.1 - 51 * x.2.1 - 130 * x.2.2,
   4 * x.1 + 10 * x.2.1 + 25 * x.2.2)

lemma gActionReal_continuous : Continuous gActionReal := by
  unfold gActionReal; fun_prop

lemma hActionReal_continuous : Continuous hActionReal := by
  unfold hActionReal; fun_prop

/-- `gActionReal` fixes `P_0`. -/
lemma gActionReal_P_0 : gActionReal P_0 = P_0 := by
  have h_sqrt_ne : Real.sqrt 221 ≠ 0 :=
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 221)).ne'
  unfold gActionReal P_0
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩⟩
  all_goals field_simp; ring

/-- `hActionReal` sends `P_0` to `-P_0`. -/
lemma hActionReal_P_0 : hActionReal P_0 = (-P_0.1, -P_0.2.1, -P_0.2.2) := by
  have h_sqrt_ne : Real.sqrt 221 ≠ 0 :=
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 221)).ne'
  unfold hActionReal P_0
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩⟩
  all_goals field_simp; ring

/-- `gActionReal` preserves the discriminant `b² − 4ac`. -/
lemma gActionReal_preserves_disc (x : ℝ × ℝ × ℝ) :
    discFn (gActionReal x) = discFn x := by
  unfold discFn gActionReal
  ring

/-- `hActionReal` preserves the discriminant. -/
lemma hActionReal_preserves_disc (x : ℝ × ℝ × ℝ) :
    discFn (hActionReal x) = discFn x := by
  unfold discFn hActionReal
  ring

/-- Negation preserves `V_disc,+1` membership and `Ω_strict`. -/
lemma neg_mem_Omega_strict {x : ℝ × ℝ × ℝ} (hx : x ∈ Omega_strict) :
    (-x.1, -x.2.1, -x.2.2) ∈ Omega_strict := by
  obtain ⟨hV, h1, h2, h3⟩ := hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (-x.2.1)^2 - 4 * (-x.1) * (-x.2.2) = 1
    have : x.2.1^2 - 4 * x.1 * x.2.2 = 1 := hV
    nlinarith
  · show |(-x.1) - (-x.2.2)| < 1
    rw [show (-x.1) - (-x.2.2) = -(x.1 - x.2.2) by ring, abs_neg]
    exact h1
  · show |(-x.2.1)| < 1
    rw [abs_neg]
    exact h2
  · show |(-x.1) + (-x.2.2)| < 1
    rw [show (-x.1) + (-x.2.2) = -(x.1 + x.2.2) by ring, abs_neg]
    exact h3

/-- The "open inequalities" part of `Ω_strict`. -/
def Omega_strict_open : Set (ℝ × ℝ × ℝ) :=
  { x | |x.1 - x.2.2| < 1 ∧ |x.2.1| < 1 ∧ |x.1 + x.2.2| < 1 }

lemma Omega_strict_open_isOpen : IsOpen Omega_strict_open := by
  have h1 : IsOpen { x : ℝ × ℝ × ℝ | |x.1 - x.2.2| < 1 } :=
    isOpen_lt (by fun_prop) continuous_const
  have h2 : IsOpen { x : ℝ × ℝ × ℝ | |x.2.1| < 1 } :=
    isOpen_lt (by fun_prop) continuous_const
  have h3 : IsOpen { x : ℝ × ℝ × ℝ | |x.1 + x.2.2| < 1 } :=
    isOpen_lt (by fun_prop) continuous_const
  have h_eq : Omega_strict_open
      = ({x : ℝ × ℝ × ℝ | |x.1 - x.2.2| < 1}
          ∩ {x | |x.2.1| < 1} ∩ {x | |x.1 + x.2.2| < 1}) := by
    ext x; simp [Omega_strict_open, and_assoc]
  rw [h_eq]
  exact (h1.inter h2).inter h3

lemma P_0_mem_Omega_strict_open : P_0 ∈ Omega_strict_open := by
  obtain ⟨_, h1, h2, h3⟩ := P_0_mem_Omega_strict
  exact ⟨h1, h2, h3⟩

lemma neg_P_0_mem_Omega_strict_open : (-P_0.1, -P_0.2.1, -P_0.2.2) ∈ Omega_strict_open := by
  have := neg_mem_Omega_strict P_0_mem_Omega_strict
  exact ⟨this.2.1, this.2.2.1, this.2.2.2⟩

/-- For `x ∈ V_disc,+1`, `x ∈ Ω_strict ↔ x ∈ Ω_strict_open`. -/
lemma mem_Omega_strict_iff_open {x : ℝ × ℝ × ℝ} (hx : x ∈ V_disc_plus_1) :
    x ∈ Omega_strict ↔ x ∈ Omega_strict_open := by
  constructor
  · intro h; exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  · intro ⟨h1, h2, h3⟩; exact ⟨hx, h1, h2, h3⟩

/-- **The continuity ε**: there exists `ε > 0` such that the ball `B(P_0, ε)`
and its images under `gActionReal` and `hActionReal` all lie in
`Omega_strict_open`. -/
lemma exists_pell_continuity_radius :
    ∃ ε > (0 : ℝ),
      Metric.ball P_0 ε ⊆ Omega_strict_open ∧
      gActionReal '' Metric.ball P_0 ε ⊆ Omega_strict_open ∧
      hActionReal '' Metric.ball P_0 ε ⊆ Omega_strict_open := by
  -- Three nhd-of-P_0 conditions:
  obtain ⟨ε₀, hε₀_pos, hε₀_sub⟩ :=
    Metric.isOpen_iff.mp Omega_strict_open_isOpen P_0 P_0_mem_Omega_strict_open
  -- For gActionReal at P_0: preimage of Omega_strict_open is open, contains P_0.
  have h_g_at : ContinuousAt gActionReal P_0 := gActionReal_continuous.continuousAt
  have h_g_in : P_0 ∈ gActionReal ⁻¹' Omega_strict_open := by
    show gActionReal P_0 ∈ Omega_strict_open
    rw [gActionReal_P_0]; exact P_0_mem_Omega_strict_open
  have h_g_open : IsOpen (gActionReal ⁻¹' Omega_strict_open) :=
    Omega_strict_open_isOpen.preimage gActionReal_continuous
  obtain ⟨ε_g, hε_g_pos, hε_g_sub⟩ := Metric.isOpen_iff.mp h_g_open P_0 h_g_in
  -- Similarly for hActionReal.
  have h_h_in : P_0 ∈ hActionReal ⁻¹' Omega_strict_open := by
    show hActionReal P_0 ∈ Omega_strict_open
    rw [hActionReal_P_0]; exact neg_P_0_mem_Omega_strict_open
  have h_h_open : IsOpen (hActionReal ⁻¹' Omega_strict_open) :=
    Omega_strict_open_isOpen.preimage hActionReal_continuous
  obtain ⟨ε_h, hε_h_pos, hε_h_sub⟩ := Metric.isOpen_iff.mp h_h_open P_0 h_h_in
  -- Pick ε = min.
  refine ⟨min ε₀ (min ε_g ε_h), lt_min hε₀_pos (lt_min hε_g_pos hε_h_pos), ?_, ?_, ?_⟩
  · intro x hx
    exact hε₀_sub (Metric.ball_subset_ball (min_le_left _ _) hx)
  · rintro y ⟨x, hx, rfl⟩
    exact hε_g_sub
      (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hx)
  · rintro y ⟨x, hx, rfl⟩
    exact hε_h_sub
      (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hx)

/-- The integer action `gAction` on a triple, projected by `1/s`, agrees with
`gActionReal` applied to the original projection. -/
lemma gActionReal_project (n : ℤ) (t : ℤ × ℤ × ℤ) :
    project_to_hyperboloid n (gAction t) =
      gActionReal (project_to_hyperboloid n t) := by
  unfold project_to_hyperboloid gActionReal gAction
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩⟩
  · push_cast; ring
  · push_cast; ring
  · push_cast; ring

lemma hActionReal_project (n : ℤ) (t : ℤ × ℤ × ℤ) :
    project_to_hyperboloid n (hAction t) =
      hActionReal (project_to_hyperboloid n t) := by
  unfold project_to_hyperboloid hActionReal hAction
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩⟩
  · push_cast; ring
  · push_cast; ring
  · push_cast; ring

/-- Inverse of `gAction`'s binary-form-action matrix (the 3×3 matrix for
`g_0^{-1} = (-2, -5; -5, -13)` acting on quadratic-form coefficients). -/
def gAction_inv (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (4 * t.1 + 10 * t.2.1 + 25 * t.2.2,
   20 * t.1 + 51 * t.2.1 + 130 * t.2.2,
   25 * t.1 + 65 * t.2.1 + 169 * t.2.2)

/-- `hAction` is its own inverse: `h_0² = -I` in SL_2(ℤ), so the form-action
matrix `M(h_0)` satisfies `M(h_0)² = M(h_0²) = M(-I) = I`. -/
def hAction_inv : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := hAction

/-- Component-wise: first component of `gAction_inv (gAction t)` equals `t.1`. -/
lemma gAction_inv_gAction_fst (t : ℤ × ℤ × ℤ) :
    (gAction_inv (gAction t)).1 = t.1 := by
  show 4 * (gAction t).1 + 10 * (gAction t).2.1 + 25 * (gAction t).2.2 = t.1
  show 4 * (169 * t.1 - 65 * t.2.1 + 25 * t.2.2)
      + 10 * (-130 * t.1 + 51 * t.2.1 - 20 * t.2.2)
      + 25 * (25 * t.1 - 10 * t.2.1 + 4 * t.2.2) = t.1
  ring

/-- Second component. -/
lemma gAction_inv_gAction_snd_fst (t : ℤ × ℤ × ℤ) :
    (gAction_inv (gAction t)).2.1 = t.2.1 := by
  show 20 * (gAction t).1 + 51 * (gAction t).2.1 + 130 * (gAction t).2.2 = t.2.1
  show 20 * (169 * t.1 - 65 * t.2.1 + 25 * t.2.2)
      + 51 * (-130 * t.1 + 51 * t.2.1 - 20 * t.2.2)
      + 130 * (25 * t.1 - 10 * t.2.1 + 4 * t.2.2) = t.2.1
  ring

/-- Third component. -/
lemma gAction_inv_gAction_snd_snd (t : ℤ × ℤ × ℤ) :
    (gAction_inv (gAction t)).2.2 = t.2.2 := by
  show 25 * (gAction t).1 + 65 * (gAction t).2.1 + 169 * (gAction t).2.2 = t.2.2
  show 25 * (169 * t.1 - 65 * t.2.1 + 25 * t.2.2)
      + 65 * (-130 * t.1 + 51 * t.2.1 - 20 * t.2.2)
      + 169 * (25 * t.1 - 10 * t.2.1 + 4 * t.2.2) = t.2.2
  ring

/-- `gAction_inv ∘ gAction = id`. -/
lemma gAction_inv_gAction (t : ℤ × ℤ × ℤ) : gAction_inv (gAction t) = t := by
  apply Prod.ext
  · exact gAction_inv_gAction_fst t
  · apply Prod.ext
    · exact gAction_inv_gAction_snd_fst t
    · exact gAction_inv_gAction_snd_snd t

/-- `hAction ∘ hAction = id` (since `hAction_inv := hAction`). -/
lemma hAction_inv_hAction_fst (t : ℤ × ℤ × ℤ) :
    (hAction_inv (hAction t)).1 = t.1 := by
  show 25 * (hAction t).1 + 65 * (hAction t).2.1 + 169 * (hAction t).2.2 = t.1
  show 25 * (25 * t.1 + 65 * t.2.1 + 169 * t.2.2)
      + 65 * (-20 * t.1 - 51 * t.2.1 - 130 * t.2.2)
      + 169 * (4 * t.1 + 10 * t.2.1 + 25 * t.2.2) = t.1
  ring

lemma hAction_inv_hAction_snd_fst (t : ℤ × ℤ × ℤ) :
    (hAction_inv (hAction t)).2.1 = t.2.1 := by
  show -20 * (hAction t).1 - 51 * (hAction t).2.1 - 130 * (hAction t).2.2 = t.2.1
  show -20 * (25 * t.1 + 65 * t.2.1 + 169 * t.2.2)
      - 51 * (-20 * t.1 - 51 * t.2.1 - 130 * t.2.2)
      - 130 * (4 * t.1 + 10 * t.2.1 + 25 * t.2.2) = t.2.1
  ring

lemma hAction_inv_hAction_snd_snd (t : ℤ × ℤ × ℤ) :
    (hAction_inv (hAction t)).2.2 = t.2.2 := by
  show 4 * (hAction t).1 + 10 * (hAction t).2.1 + 25 * (hAction t).2.2 = t.2.2
  show 4 * (25 * t.1 + 65 * t.2.1 + 169 * t.2.2)
      + 10 * (-20 * t.1 - 51 * t.2.1 - 130 * t.2.2)
      + 25 * (4 * t.1 + 10 * t.2.1 + 25 * t.2.2) = t.2.2
  ring

/-- `hAction_inv ∘ hAction = id`. -/
lemma hAction_inv_hAction (t : ℤ × ℤ × ℤ) : hAction_inv (hAction t) = t := by
  apply Prod.ext
  · exact hAction_inv_hAction_fst t
  · apply Prod.ext
    · exact hAction_inv_hAction_snd_fst t
    · exact hAction_inv_hAction_snd_snd t

/-- `gAction` preserves membership in `R_star_disc(d)`. -/
lemma gAction_mem_R_star_disc {d : ℤ} {t : ℤ × ℤ × ℤ} (ht : t ∈ R_star_disc d) :
    gAction t ∈ R_star_disc d := by
  refine ⟨?_, ?_⟩
  · -- Discriminant preserved.
    rw [gAction_preserves_disc t]; exact ht.1
  · -- GCD: any common divisor of gAction t's components divides t's components
    -- (via gAction_inv = explicit linear combinations), hence divides 1.
    set g := Int.gcd (gAction t).1 (Int.gcd (gAction t).2.1 (gAction t).2.2) with hg_def
    have hg_dvd_a : (g : ℤ) ∣ (gAction t).1 := Int.gcd_dvd_left _ _
    have hg_dvd_bc : (g : ℤ) ∣ Int.gcd (gAction t).2.1 (gAction t).2.2 :=
      Int.gcd_dvd_right _ _
    have hg_dvd_b : (g : ℤ) ∣ (gAction t).2.1 := hg_dvd_bc.trans (Int.gcd_dvd_left _ _)
    have hg_dvd_c : (g : ℤ) ∣ (gAction t).2.2 := hg_dvd_bc.trans (Int.gcd_dvd_right _ _)
    -- g divides t.1, t.2.1, t.2.2 via gAction_inv linear combinations.
    have h_t : t = gAction_inv (gAction t) := (gAction_inv_gAction t).symm
    have h_t1 : (g : ℤ) ∣ t.1 := by
      rw [h_t]
      show (g : ℤ) ∣ 4 * (gAction t).1 + 10 * (gAction t).2.1 + 25 * (gAction t).2.2
      exact dvd_add (dvd_add (hg_dvd_a.mul_left 4) (hg_dvd_b.mul_left 10))
                    (hg_dvd_c.mul_left 25)
    have h_t2 : (g : ℤ) ∣ t.2.1 := by
      rw [h_t]
      show (g : ℤ) ∣ 20 * (gAction t).1 + 51 * (gAction t).2.1 + 130 * (gAction t).2.2
      exact dvd_add (dvd_add (hg_dvd_a.mul_left 20) (hg_dvd_b.mul_left 51))
                    (hg_dvd_c.mul_left 130)
    have h_t3 : (g : ℤ) ∣ t.2.2 := by
      rw [h_t]
      show (g : ℤ) ∣ 25 * (gAction t).1 + 65 * (gAction t).2.1 + 169 * (gAction t).2.2
      exact dvd_add (dvd_add (hg_dvd_a.mul_left 25) (hg_dvd_b.mul_left 65))
                    (hg_dvd_c.mul_left 169)
    have h_inner : (g : ℤ) ∣ ((Int.gcd t.2.1 t.2.2 : ℕ) : ℤ) :=
      Int.dvd_natAbs.mp (by
        rw [Int.natAbs_natCast]
        exact_mod_cast Nat.dvd_gcd (Int.natCast_dvd_natCast.mp (by simpa using Int.natAbs_dvd.mpr (by exact_mod_cast h_t2)))
          (Int.natCast_dvd_natCast.mp (by simpa using Int.natAbs_dvd.mpr (by exact_mod_cast h_t3))))
    have h_g_dvd_gcd_t : (g : ℤ) ∣ ((Int.gcd t.1 (Int.gcd t.2.1 t.2.2) : ℕ) : ℤ) :=
      Int.dvd_natAbs.mp (by
        rw [Int.natAbs_natCast]
        exact_mod_cast Nat.dvd_gcd (Int.natCast_dvd_natCast.mp (by simpa using Int.natAbs_dvd.mpr (by exact_mod_cast h_t1)))
          (Int.natCast_dvd_natCast.mp (by simpa using Int.natAbs_dvd.mpr (by exact_mod_cast h_inner))))
    rw [ht.2] at h_g_dvd_gcd_t
    -- g ∣ 1 ⟹ g = 1.
    have h_g_eq_one : g = 1 := by
      have h : (g : ℤ) ∣ (1 : ℤ) := by exact_mod_cast h_g_dvd_gcd_t
      have : g ∣ 1 := by exact_mod_cast h
      exact Nat.dvd_one.mp this
    exact h_g_eq_one

/-- `hAction` preserves membership in `R_star_disc(d)`. -/
lemma hAction_mem_R_star_disc {d : ℤ} {t : ℤ × ℤ × ℤ} (ht : t ∈ R_star_disc d) :
    hAction t ∈ R_star_disc d := by
  refine ⟨?_, ?_⟩
  · rw [hAction_preserves_disc t]; exact ht.1
  · set g := Int.gcd (hAction t).1 (Int.gcd (hAction t).2.1 (hAction t).2.2) with hg_def
    have hg_dvd_a : (g : ℤ) ∣ (hAction t).1 := Int.gcd_dvd_left _ _
    have hg_dvd_bc : (g : ℤ) ∣ Int.gcd (hAction t).2.1 (hAction t).2.2 :=
      Int.gcd_dvd_right _ _
    have hg_dvd_b : (g : ℤ) ∣ (hAction t).2.1 := hg_dvd_bc.trans (Int.gcd_dvd_left _ _)
    have hg_dvd_c : (g : ℤ) ∣ (hAction t).2.2 := hg_dvd_bc.trans (Int.gcd_dvd_right _ _)
    have h_t : t = hAction_inv (hAction t) := (hAction_inv_hAction t).symm
    have h_t1 : (g : ℤ) ∣ t.1 := by
      rw [h_t]
      show (g : ℤ) ∣ 25 * (hAction t).1 + 65 * (hAction t).2.1 + 169 * (hAction t).2.2
      exact dvd_add (dvd_add (hg_dvd_a.mul_left 25) (hg_dvd_b.mul_left 65))
                    (hg_dvd_c.mul_left 169)
    have h_t2 : (g : ℤ) ∣ t.2.1 := by
      rw [h_t]
      show (g : ℤ) ∣ -20 * (hAction t).1 - 51 * (hAction t).2.1 - 130 * (hAction t).2.2
      have h1 : (g : ℤ) ∣ -20 * (hAction t).1 := by
        have := hg_dvd_a.mul_left (-20); exact this
      have h2 : (g : ℤ) ∣ 51 * (hAction t).2.1 := hg_dvd_b.mul_left 51
      have h3 : (g : ℤ) ∣ 130 * (hAction t).2.2 := hg_dvd_c.mul_left 130
      have : -20 * (hAction t).1 - 51 * (hAction t).2.1 - 130 * (hAction t).2.2
           = -20 * (hAction t).1 + (-(51 * (hAction t).2.1)) + (-(130 * (hAction t).2.2)) := by ring
      rw [this]
      exact dvd_add (dvd_add h1 (dvd_neg.mpr h2)) (dvd_neg.mpr h3)
    have h_t3 : (g : ℤ) ∣ t.2.2 := by
      rw [h_t]
      show (g : ℤ) ∣ 4 * (hAction t).1 + 10 * (hAction t).2.1 + 25 * (hAction t).2.2
      exact dvd_add (dvd_add (hg_dvd_a.mul_left 4) (hg_dvd_b.mul_left 10))
                    (hg_dvd_c.mul_left 25)
    have h_inner : (g : ℤ) ∣ ((Int.gcd t.2.1 t.2.2 : ℕ) : ℤ) :=
      Int.dvd_natAbs.mp (by
        rw [Int.natAbs_natCast]
        exact_mod_cast Nat.dvd_gcd (Int.natCast_dvd_natCast.mp (by simpa using Int.natAbs_dvd.mpr (by exact_mod_cast h_t2)))
          (Int.natCast_dvd_natCast.mp (by simpa using Int.natAbs_dvd.mpr (by exact_mod_cast h_t3))))
    have h_g_dvd_gcd_t : (g : ℤ) ∣ ((Int.gcd t.1 (Int.gcd t.2.1 t.2.2) : ℕ) : ℤ) :=
      Int.dvd_natAbs.mp (by
        rw [Int.natAbs_natCast]
        exact_mod_cast Nat.dvd_gcd (Int.natCast_dvd_natCast.mp (by simpa using Int.natAbs_dvd.mpr (by exact_mod_cast h_t1)))
          (Int.natCast_dvd_natCast.mp (by simpa using Int.natAbs_dvd.mpr (by exact_mod_cast h_inner))))
    rw [ht.2] at h_g_dvd_gcd_t
    have h_g_eq_one : g = 1 := by
      have h : (g : ℤ) ∣ (1 : ℤ) := by exact_mod_cast h_g_dvd_gcd_t
      have : g ∣ 1 := by exact_mod_cast h
      exact Nat.dvd_one.mp this
    exact h_g_eq_one

/-- **Derived `duke_theorem`** from `theorem_2_3` plus the Pell-matrix
parity correction (Chojecki's forum proof). -/
theorem duke_theorem : DukeTheoremStatement := by
  obtain ⟨ε, hε_pos, hε_self, hε_g, hε_h⟩ := exists_pell_continuity_radius
  obtain ⟨N, hN⟩ := exists_projection_in_ball P_0_mem_V hε_pos
  refine ⟨max N 1, fun n hn hn_nsq => ?_⟩
  have hnN : n ≥ N := le_trans (le_max_left N 1) hn
  have hn1 : n ≥ 1 := le_trans (le_max_right N 1) hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hn1
  have h4n_pos : (0 : ℝ) < 4 * n := by linarith
  have h_sqrt_pos : 0 < Real.sqrt (4 * (n : ℝ)) := Real.sqrt_pos.mpr h4n_pos
  have h_sqrt_ne : Real.sqrt (4 * (n : ℝ)) ≠ 0 := h_sqrt_pos.ne'
  have h_sqrt_sq : (Real.sqrt (4 * (n : ℝ)))^2 = 4 * n := Real.sq_sqrt h4n_pos.le
  obtain ⟨t, h_ball⟩ := hN n hnN hn_nsq
  have ht_in_open : project_to_hyperboloid n t.val ∈ Omega_strict_open :=
    hε_self h_ball
  have ht_in_V : project_to_hyperboloid n t.val ∈ V_disc_plus_1 := by
    have h_disc : t.val.2.1^2 - 4 * t.val.1 * t.val.2.2 = 4 * n := t.property.1
    show (project_to_hyperboloid n t.val).2.1^2
         - 4 * (project_to_hyperboloid n t.val).1 * (project_to_hyperboloid n t.val).2.2 = 1
    show (t.val.2.1 / Real.sqrt (4 * (n : ℝ)))^2
         - 4 * ((t.val.1 : ℝ) / Real.sqrt (4 * (n : ℝ)))
             * ((t.val.2.2 : ℝ) / Real.sqrt (4 * (n : ℝ))) = 1
    have h_eq : ((t.val.2.1 : ℝ) / Real.sqrt (4 * (n : ℝ)))^2
              - 4 * ((t.val.1 : ℝ) / Real.sqrt (4 * (n : ℝ)))
                  * ((t.val.2.2 : ℝ) / Real.sqrt (4 * (n : ℝ)))
              = ((t.val.2.1 : ℝ)^2 - 4 * (t.val.1 : ℝ) * (t.val.2.2 : ℝ))
                  / (Real.sqrt (4 * (n : ℝ)))^2 := by field_simp
    rw [h_eq, h_sqrt_sq]
    have h_cast : ((t.val.2.1 : ℝ)^2 - 4 * (t.val.1 : ℝ) * (t.val.2.2 : ℝ))
                = ((t.val.2.1^2 - 4 * t.val.1 * t.val.2.2 : ℤ) : ℝ) := by push_cast; ring
    rw [h_cast, h_disc]
    push_cast
    field_simp
  have ht_in_strict : project_to_hyperboloid n t.val ∈ Omega_strict :=
    (mem_Omega_strict_iff_open ht_in_V).mpr ht_in_open
  -- Now handle parity dichotomy.
  -- We have t ∈ R_star_disc(4n), so gcd(a, b, c) = 1 and b² - 4ac = 4n.
  -- 4 | b² ⟹ 2 | b. So b is even.
  -- gcd(a, b, c) = 1 with b even: not both a, c even (else gcd ≥ 2).
  by_cases h_parity : t.val.1 % 2 = t.val.2.2 % 2
  · -- Case (a): parity matches, use t directly.
    exact ⟨t.val, t.property, ht_in_strict, h_parity⟩
  · -- Need to apply g- or h-action.
    -- Determine which case via the parity of c.
    by_cases h_c_even : t.val.2.2 % 2 = 0
    · -- Case (b): c even, a odd (since parity mismatch).
      -- Apply gAction.
      have h_b_even : t.val.2.1 % 2 = 0 := by
        have h_disc : t.val.2.1^2 - 4 * t.val.1 * t.val.2.2 = 4 * n := t.property.1
        have h_b_sq_eq : t.val.2.1^2 = 4 * n + 4 * (t.val.1 * t.val.2.2) := by linarith
        have h_b_sq_mod : t.val.2.1^2 % 4 = 0 := by
          set ac := t.val.1 * t.val.2.2
          omega
        by_contra h_no
        have h_odd : t.val.2.1 % 2 = 1 := by omega
        have h_b_eq : t.val.2.1 = 2 * (t.val.2.1 / 2) + 1 := by omega
        have h_sq_expand : t.val.2.1^2 = 4 * (t.val.2.1 / 2)^2 + 4 * (t.val.2.1 / 2) + 1 := by
          nlinarith [h_b_eq]
        set k := t.val.2.1 / 2
        omega
      have h_gA_in : gAction t.val ∈ R_star_disc (4 * n) :=
        gAction_mem_R_star_disc t.property
      refine ⟨gAction t.val, h_gA_in, ?_, ?_⟩
      · rw [gActionReal_project]
        have h_in : gActionReal (project_to_hyperboloid n t.val) ∈ Omega_strict_open :=
          hε_g (Set.mem_image_of_mem _ h_ball)
        have h_in_V : gActionReal (project_to_hyperboloid n t.val) ∈ V_disc_plus_1 := by
          have : discFn (gActionReal (project_to_hyperboloid n t.val))
              = discFn (project_to_hyperboloid n t.val) :=
            gActionReal_preserves_disc _
          show discFn (gActionReal (project_to_hyperboloid n t.val)) = 1
          rw [this]
          exact ht_in_V
        exact (mem_Omega_strict_iff_open h_in_V).mpr h_in
      · exact gAction_parity_matches t.val h_b_even h_c_even
    · -- Case (c): c odd, a even (since parity mismatch and c not even).
      have h_a_even : t.val.1 % 2 = 0 := by omega
      have h_b_even : t.val.2.1 % 2 = 0 := by
        have h_disc : t.val.2.1^2 - 4 * t.val.1 * t.val.2.2 = 4 * n := t.property.1
        have h_b_sq_eq : t.val.2.1^2 = 4 * n + 4 * (t.val.1 * t.val.2.2) := by linarith
        have h_b_sq_mod : t.val.2.1^2 % 4 = 0 := by
          set ac := t.val.1 * t.val.2.2
          omega
        by_contra h_no
        have h_odd : t.val.2.1 % 2 = 1 := by omega
        have h_b_eq : t.val.2.1 = 2 * (t.val.2.1 / 2) + 1 := by omega
        have h_sq_expand : t.val.2.1^2 = 4 * (t.val.2.1 / 2)^2 + 4 * (t.val.2.1 / 2) + 1 := by
          nlinarith [h_b_eq]
        set k := t.val.2.1 / 2
        omega
      have h_hA_in : hAction t.val ∈ R_star_disc (4 * n) :=
        hAction_mem_R_star_disc t.property
      refine ⟨hAction t.val, h_hA_in, ?_, ?_⟩
      · rw [hActionReal_project]
        have h_in : hActionReal (project_to_hyperboloid n t.val) ∈ Omega_strict_open :=
          hε_h (Set.mem_image_of_mem _ h_ball)
        have h_in_V : hActionReal (project_to_hyperboloid n t.val) ∈ V_disc_plus_1 := by
          have : discFn (hActionReal (project_to_hyperboloid n t.val))
              = discFn (project_to_hyperboloid n t.val) :=
            hActionReal_preserves_disc _
          show discFn (hActionReal (project_to_hyperboloid n t.val)) = 1
          rw [this]
          exact ht_in_V
        exact (mem_Omega_strict_iff_open h_in_V).mpr h_in
      · exact hAction_parity_matches t.val h_b_even h_a_even

theorem erdos_1148 :
  ∃ N : ℤ, ∀ n : ℤ, n ≥ N → ∃ x y z : ℤ, n = x^2 + y^2 - z^2 ∧ max (x^2) (max (y^2) (z^2)) ≤ n := by
  rcases duke_theorem with ⟨N, hN⟩
  use max N 1
  intro n hn
  have hnN : n ≥ N := le_trans (le_max_left N 1) hn
  have hn1 : n ≥ 1 := le_trans (le_max_right N 1) hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hn1
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos

  -- Case-split: square vs non-square n. ELMV Theorem 2.3 (hence DukeTheoremStatement)
  -- only applies to non-square n; the square case n = m² is trivial with (m, 0, 0).
  by_cases hn_sq : IsSquare n
  · -- Square case: n = m² for some m. Use (x, y, z) = (m, 0, 0).
    obtain ⟨m, hm⟩ := hn_sq
    refine ⟨m, 0, 0, ?_, ?_⟩
    · -- m² + 0² - 0² = m² = m * m = n
      rw [hm]; ring
    · -- max (m², 0, 0) = m² = n ≤ n
      have h_max : max (m^2) (max ((0:ℤ)^2) ((0:ℤ)^2)) = m^2 := by
        simp [sq_nonneg]
      rw [h_max, hm]; nlinarith [sq_nonneg m]

  rcases hN n hnN hn_sq with ⟨⟨a, b, c⟩, ht_disc, ht_omega, ht_parity⟩
  -- Reduce (a, b, c).1 → a, (a, b, c).2.2 → c, etc. so omega doesn't see extra division terms
  dsimp at ht_disc ht_parity

  let x := (a - c) / 2
  let y := b / 2
  let z := (a + c) / 2

  use x, y, z

  have h_eq : b ^ 2 - 4 * a * c = 4 * n := ht_disc.1

  have hb_even : b % 2 = 0 := by
    have h_parity : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases h_parity with h0 | h1
    · exact h0
    · exfalso
      have hk : ∃ k, b = 2 * k + 1 := ⟨b / 2, by omega⟩
      rcases hk with ⟨k, hk⟩
      have h_eq2 : 4 * (k ^ 2 + k - a * c - n) = -1 := by
        calc 4 * (k ^ 2 + k - a * c - n)
            = (2 * k + 1) ^ 2 - 4 * a * c - 4 * n - 1 := by ring
          _ = b ^ 2 - 4 * a * c - 4 * n - 1 := by rw [hk]
          _ = 4 * n - 4 * n - 1 := by rw [h_eq]
          _ = -1 := by ring
      generalize k ^ 2 + k - a * c - n = X at h_eq2
      omega

  -- KEY: Prove the 2*w relationships BEFORE h_n, so omega never sees x^2, y^2, z^2
  have hx_rel : a - c = 2 * x := by
    have : (a - c) % 2 = 0 := by omega
    change a - c = 2 * ((a - c) / 2)
    omega
  have hy_rel : b = 2 * y := by
    change b = 2 * (b / 2)
    omega
  have hz_rel : a + c = 2 * z := by
    have : (a + c) % 2 = 0 := by omega
    change a + c = 2 * ((a + c) / 2)
    omega

  have h_n : x ^ 2 + y ^ 2 - z ^ 2 = n := by
    exact lemma_dictionary n a b c h_eq hb_even ht_parity

  refine ⟨h_n.symm, ?_⟩

  have hs : Real.sqrt (4 * (n : ℝ)) = 2 * Real.sqrt (n : ℝ) := by
    calc Real.sqrt (4 * (n : ℝ))
        = Real.sqrt 4 * Real.sqrt (n : ℝ) := Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) (n : ℝ)
      _ = 2 * Real.sqrt (n : ℝ) := by norm_num

  dsimp [Omega_strict, project_to_hyperboloid] at ht_omega

  have h_omega1 : |(a : ℝ) / (2 * Real.sqrt (n : ℝ)) - (c : ℝ) / (2 * Real.sqrt (n : ℝ))| < 1 := by
    have h := ht_omega.2.1
    rwa [hs] at h

  have h_omega2 : |(b : ℝ) / (2 * Real.sqrt (n : ℝ))| < 1 := by
    have h := ht_omega.2.2.1
    rwa [hs] at h

  have h_omega3 : |(a : ℝ) / (2 * Real.sqrt (n : ℝ)) + (c : ℝ) / (2 * Real.sqrt (n : ℝ))| < 1 := by
    have h := ht_omega.2.2.2
    rwa [hs] at h

  have sqrt_pos : 0 < 2 * Real.sqrt (n : ℝ) := by positivity

  have h_bound1 : |((a - c : ℤ) : ℝ)| < 2 * Real.sqrt (n : ℝ) := by
    have h_sub : (a : ℝ) / (2 * Real.sqrt (n : ℝ)) - (c : ℝ) / (2 * Real.sqrt (n : ℝ))
        = ((a - c : ℤ) : ℝ) / (2 * Real.sqrt (n : ℝ)) := by push_cast; ring
    have h_omega1' : |((a - c : ℤ) : ℝ) / (2 * Real.sqrt (n : ℝ))| < 1 := by rwa [← h_sub]
    rw [abs_div, abs_of_pos sqrt_pos, div_lt_iff₀ sqrt_pos] at h_omega1'
    linarith

  have h_bound2 : |((b : ℤ) : ℝ)| < 2 * Real.sqrt (n : ℝ) := by
    have h_b : (b : ℝ) / (2 * Real.sqrt (n : ℝ))
        = ((b : ℤ) : ℝ) / (2 * Real.sqrt (n : ℝ)) := by push_cast; rfl
    have h_omega2' : |((b : ℤ) : ℝ) / (2 * Real.sqrt (n : ℝ))| < 1 := by rwa [← h_b]
    rw [abs_div, abs_of_pos sqrt_pos, div_lt_iff₀ sqrt_pos] at h_omega2'
    linarith

  have h_bound3 : |((a + c : ℤ) : ℝ)| < 2 * Real.sqrt (n : ℝ) := by
    have h_add : (a : ℝ) / (2 * Real.sqrt (n : ℝ)) + (c : ℝ) / (2 * Real.sqrt (n : ℝ))
        = ((a + c : ℤ) : ℝ) / (2 * Real.sqrt (n : ℝ)) := by push_cast; ring
    have h_omega3' : |((a + c : ℤ) : ℝ) / (2 * Real.sqrt (n : ℝ))| < 1 := by rwa [← h_add]
    rw [abs_div, abs_of_pos sqrt_pos, div_lt_iff₀ sqrt_pos] at h_omega3'
    linarith

  have bound_helper : ∀ (w : ℤ), |(2 * w : ℝ)| < 2 * Real.sqrt (n : ℝ) → (w ^ 2 : ℤ) ≤ n := by
    intro w hw
    have hw2 : 2 * |(w : ℝ)| < 2 * Real.sqrt (n : ℝ) := by
      calc 2 * |(w : ℝ)| = |(2 : ℝ)| * |(w : ℝ)| := by norm_num
           _ = |(2 * w : ℝ)| := by rw [← abs_mul]
           _ < 2 * Real.sqrt (n : ℝ) := hw
    have hw3 : |(w : ℝ)| < Real.sqrt (n : ℝ) := by linarith
    have hdiff : 0 < Real.sqrt (n : ℝ) - |(w : ℝ)| := sub_pos.mpr hw3
    have hsum_pos : 0 < Real.sqrt (n : ℝ) + |(w : ℝ)| := by
      have : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn_pos)
      positivity
    have hprod : 0 < (Real.sqrt (n : ℝ)) ^ 2 - |(w : ℝ)| ^ 2 := by
      calc 0
          < (Real.sqrt (n : ℝ) - |(w : ℝ)|) * (Real.sqrt (n : ℝ) + |(w : ℝ)|) := mul_pos hdiff hsum_pos
        _ = (Real.sqrt (n : ℝ)) ^ 2 - |(w : ℝ)| ^ 2 := by ring
    have h2 : |(w : ℝ)| ^ 2 < (Real.sqrt (n : ℝ)) ^ 2 := by linarith
    rw [sq_abs, Real.sq_sqrt hn_nonneg] at h2
    exact_mod_cast le_of_lt h2

  have hx_bound : (x ^ 2 : ℤ) ≤ n := by
    apply bound_helper
    have : ((a - c : ℤ) : ℝ) = 2 * (x : ℝ) := by rw [hx_rel]; push_cast; ring
    rwa [this] at h_bound1

  have hy_bound : (y ^ 2 : ℤ) ≤ n := by
    apply bound_helper
    have : ((b : ℤ) : ℝ) = 2 * (y : ℝ) := by rw [hy_rel]; push_cast; ring
    rwa [this] at h_bound2

  have hz_bound : (z ^ 2 : ℤ) ≤ n := by
    apply bound_helper
    have : ((a + c : ℤ) : ℝ) = 2 * (z : ℝ) := by rw [hz_rel]; push_cast; ring
    rwa [this] at h_bound3

  exact max_le hx_bound (max_le hy_bound hz_bound)

end

#print axioms erdos_1148
-- 'Erdos1148.erdos_1148' depends on axioms: [propext, Classical.choice, Erdos1148.theorem_2_3, Quot.sound]

end Erdos1148
