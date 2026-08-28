import Mathlib

namespace Erdos22

/-
# Problem Description

Erdős Problem 22. For `ε > 0` and `n` sufficiently large in terms of `ε`, is there a graph on
`n` vertices with at least `n²/8` edges, containing no `K₄`, whose largest independent set has
size at most `εn`? `erdos_22` proves that there is.

Equivalently, the Ramsey--Turán number satisfies `rt(n; 4, εn) ≥ n²/8` for large `n`. The
question was conjectured by Bollobás and Erdős [BoEr76], who constructed such a graph with
`(1/8 + o(1))n²` edges, and settled by Fox, Loh and Zhao [FLZ15], who obtained the clean
`≥ n²/8` for every `n ≥ 1`. The quantitative Bollobás--Erdős construction used here is the
same one that refutes problem 615, and the modules for that problem lie in the dependency
closure of this file; `not_erdos_615` therefore appears below as a by-product of the shared
construction.

The formalisation is by plby (github.com/plby/lean-proofs),
`src/latest/ErdosProblems/Erdos22.lean` together with `src/latest/ErdosProblems/Erdos615.lean`
and the two modules of `src/latest/ErdosProblems/Erdos615/`. The four files are concatenated
here in dependency order, with their project-internal imports removed so that `Mathlib` is the
only import, each module's contents kept in a `section` carrying its own `open` lines, and the
whole wrapped once in `namespace Erdos22` with the upstream trust-base print lines and
trailing `alias` removed. No mathematical content is changed.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos615/Erdos615BrunnMinkowski.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Prékopa--Leindler and Brunn--Minkowski in finite-dimensional real coordinate
spaces.  Mathlib v4.33.0 does not yet contain Brunn--Minkowski, so this file
supplies the localized analytic theorem used by the Erdős 615 construction.

The proof is by the standard tensorization of the one-dimensional
Prékopa--Leindler inequality.  It is adapted to current Mathlib APIs from the
complete Lean 3 development by Albert Chua.
-/


open Set Real MeasureTheory
open scoped ENNReal Pointwise Topology

namespace Erdos615.BrunnMinkowski

theorem ennreal_geomMean_le_arithMean2_weighted
    (w₁ w₂ : ℝ) (p₁ p₂ : ℝ≥0∞)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ ≤ ENNReal.ofReal w₁ * p₁ + ENNReal.ofReal w₂ * p₂ := by
  wlog hp : p₁ ≤ p₂ generalizing w₁ w₂ p₁ p₂
  · convert this w₂ w₁ p₂ p₁ hw₂ hw₁ (by linarith) (le_of_not_ge hp) using 1
    · rw [mul_comm]
    · rw [add_comm]
  rcases eq_or_ne p₂ ∞ with rfl | hp₂
  · rcases eq_or_lt_of_le hw₂ with rfl | hw₂pos
    · simp only [add_zero] at hw
      subst w₁
      simp
    · simp [hw₂pos]
  have hp₂lt : p₂ < ∞ := lt_top_iff_ne_top.mpr hp₂
  have hp₁lt : p₁ < ∞ := hp.trans_lt hp₂lt
  rw [← ENNReal.coe_toNNReal hp₁lt.ne, ← ENNReal.coe_toNNReal hp₂lt.ne,
    ← ENNReal.coe_rpow_of_nonneg _ hw₁, ← ENNReal.coe_rpow_of_nonneg _ hw₂,
    ← ENNReal.coe_mul, ENNReal.ofReal, ENNReal.ofReal,
    ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_add, ENNReal.coe_le_coe]
  have hnn : w₁.toNNReal + w₂.toNNReal = 1 := by
    apply NNReal.eq
    simpa [Real.toNNReal_of_nonneg hw₁, Real.toNNReal_of_nonneg hw₂] using hw
  convert NNReal.geom_mean_le_arith_mean2_weighted
    w₁.toNNReal w₂.toNNReal p₁.toNNReal p₂.toNNReal hnn using 1 <;>
      simp [Real.toNNReal_of_nonneg hw₁, Real.toNNReal_of_nonneg hw₂]

lemma brunnMinkowski_compact_one
    {A B : Set ℝ} (A_ne : A.Nonempty) (B_ne : B.Nonempty)
    (hA : IsCompact A) (hB : IsCompact B) :
    volume A + volume B ≤ volume (A + B) := by
  let A' := A + {sInf B}
  let B' := {sSup A} + B
  have hA' : volume A = volume A' := by
    simp [A', add_singleton, image_add_right]
  have hB' : volume B = volume B' := by
    simp [B', singleton_add, image_add_left]
  have hinter : volume (A' ∩ B') = 0 := by
    convert (volume_singleton : volume ({sSup A + sInf B} : Set ℝ) = 0)
    rw [eq_singleton_iff_unique_mem]
    refine ⟨?_, ?_⟩
    · exact ⟨by simpa [A'] using hA.sSup_mem A_ne,
        by simpa [B'] using hB.sInf_mem B_ne⟩
    · intro x hx
      rw [mem_inter_iff] at hx
      apply mem_singleton_iff.mpr
      apply le_antisymm
      · rcases hx.1 with ⟨a, ha, b, hb, rfl⟩
        rw [mem_singleton_iff.mp hb]
        exact add_le_add (le_csSup hA.bddAbove ha) le_rfl
      · rcases hx.2 with ⟨a, ha, b, hb, rfl⟩
        rw [mem_singleton_iff.mp ha]
        exact add_le_add le_rfl (csInf_le hB.bddBelow hb)
  have hA'meas : MeasurableSet A' := by
    have hc : IsCompact A' := by
      change IsCompact (A + {sInf B})
      rw [add_singleton]
      exact hA.image (continuous_id.add continuous_const)
    exact hc.measurableSet
  rw [hA', hB', ← measure_union_add_inter' hA'meas B', hinter, add_zero]
  apply measure_mono
  refine union_subset (add_subset_add_left ?_) (add_subset_add_right ?_)
  · exact singleton_subset_iff.mpr (hB.sInf_mem B_ne)
  · exact singleton_subset_iff.mpr (hA.sSup_mem A_ne)

abbrev CompactPiece (A : Set ℝ) :=
  {K : Set ℝ // K ⊆ A ∧ IsCompact K ∧ K.Nonempty}

lemma volume_eq_iSup_compactPiece
    {A : Set ℝ} (A_meas : MeasurableSet A) :
    volume A = ⨆ K : CompactPiece A, volume K.val := by
  rw [A_meas.measure_eq_iSup_isCompact volume]
  apply le_antisymm
  · refine iSup_le fun K ↦ iSup_le fun hKA ↦ iSup_le fun hKc ↦ ?_
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · simp
    · exact le_iSup_of_le ⟨K, hKA, hKc, hKne⟩ le_rfl
  · refine iSup_le fun K ↦ le_iSup_of_le K.val <|
      le_iSup_of_le K.property.1 <| le_iSup_of_le K.property.2.1 le_rfl

lemma brunnMinkowski_one
    {A B : Set ℝ} (A_meas : MeasurableSet A) (B_meas : MeasurableSet B)
    (A_ne : A.Nonempty) (B_ne : B.Nonempty) :
    volume A + volume B ≤ volume (A + B) := by
  obtain ⟨a, ha⟩ := A_ne
  obtain ⟨b, hb⟩ := B_ne
  letI : Nonempty (CompactPiece A) :=
    ⟨⟨{a}, singleton_subset_iff.mpr ha, isCompact_singleton, singleton_nonempty a⟩⟩
  letI : Nonempty (CompactPiece B) :=
    ⟨⟨{b}, singleton_subset_iff.mpr hb, isCompact_singleton, singleton_nonempty b⟩⟩
  rw [volume_eq_iSup_compactPiece A_meas, volume_eq_iSup_compactPiece B_meas]
  apply ENNReal.iSup_add_iSup_le
  intro K L
  exact (brunnMinkowski_compact_one K.property.2.2 L.property.2.2
    K.property.2.1 L.property.2.1).trans
      (measure_mono (add_subset_add K.property.1 L.property.1))

theorem lintegral_eq_lintegral_meas_lt_ennreal
    {α : Type*} [MeasurableSpace α] {f : α → ℝ≥0∞}
    (μ : Measure α) [SigmaFinite μ] (f_meas : Measurable f) :
    ∫⁻ ω, f ω ∂μ = ∫⁻ (t : ℝ) in Ioi 0, μ {a | ENNReal.ofReal t < f a} := by
  rcases eq_or_lt_of_le (show 0 ≤ μ {a | f a = ∞} from bot_le) with hzero | hpos
  · have hfinite : ∀ᵐ a ∂μ, f a < ∞ := by
      rw [ae_iff]
      simpa only [not_lt, top_le_iff] using hzero.symm
    convert lintegral_eq_lintegral_meas_lt μ
      (Filter.Eventually.of_forall fun x ↦ ENNReal.toReal_nonneg)
      (f_meas.ennreal_toReal.aemeasurable) using 1
    · exact lintegral_congr_ae
        (ofReal_toReal_ae_eq hfinite).symm
    · refine setLIntegral_congr_fun measurableSet_Ioi ?_
      intro t ht
      apply measure_congr
      filter_upwards [hfinite] with a ha
      exact propext <| ENNReal.ofReal_lt_iff_lt_toReal (mem_Ioi.mp ht).le ha.ne
  · have hne : μ {a | f a = ∞} ≠ 0 := hpos.ne'
    have hleft : ∫⁻ ω, f ω ∂μ = ∞ :=
      lintegral_eq_top_of_measure_eq_top_ne_zero f_meas.aemeasurable hne
    rw [hleft]
    apply le_antisymm ?_ le_top
    calc
      (∞ : ℝ≥0∞) = μ {a | f a = ∞} * volume (Ioi (0 : ℝ)) := by
        rw [volume_Ioi, ENNReal.mul_top hne]
      _ = ∫⁻ (_t : ℝ) in Ioi 0, μ {a | f a = ∞} := by
        rw [setLIntegral_const]
      _ ≤ ∫⁻ (t : ℝ) in Ioi 0, μ {a | ENNReal.ofReal t < f a} := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht
        apply measure_mono
        intro a ha
        rw [mem_setOf_eq, ha]
        exact ENNReal.ofReal_lt_top

lemma prekopa_slice_one
    (f g h : ℝ → ℝ≥0∞)
    (f_meas : Measurable f) (g_meas : Measurable g) (h_meas : Measurable h)
    (a b : ℝ) (hab : a + b = 1)
    (f_ineq : ∀ x y, f (a * x + b * y) ≥ g x ^ a * h y ^ b)
    (a_pos : 0 < a) (b_pos : 0 < b) {u v w : ℝ≥0∞}
    (hu : ∃ x, u < g x) (hv : ∃ y, v < h y)
    (hw : w ≤ u ^ a * v ^ b) :
    volume {x | w < f x} ≥
      ENNReal.ofReal a * volume {x | u < g x} +
        ENNReal.ofReal b * volume {y | v < h y} := by
  have hscale : ∀ {r : ℝ}, 0 ≤ r → ∀ s : Set ℝ,
      volume (r • s) = ENNReal.ofReal r * volume s := by
    intro r hr s
    simpa using volume.addHaar_smul_of_nonneg hr s
  rw [← hscale a_pos.le, ← hscale b_pos.le]
  rcases hu with ⟨x, hx⟩
  rcases hv with ⟨y, hy⟩
  calc
    volume (a • {x | u < g x}) + volume (b • {y | v < h y})
        ≤ volume (a • {x | u < g x} + b • {y | v < h y}) :=
      brunnMinkowski_one
      ((measurableSet_lt measurable_const g_meas).const_smul₀ a)
      ((measurableSet_lt measurable_const h_meas).const_smul₀ b)
      ⟨a * x, smul_mem_smul_set hx⟩
      ⟨b * y, smul_mem_smul_set hy⟩
    _ ≤ volume {x | w < f x} := by
      apply measure_mono
      rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      rw [mem_setOf_eq] at hx hy ⊢
      calc
        w ≤ u ^ a * v ^ b := hw
        _ < g x ^ a * h y ^ b :=
          ENNReal.mul_lt_mul (ENNReal.rpow_lt_rpow hx a_pos)
            (ENNReal.rpow_lt_rpow hy b_pos)
        _ ≤ f (a * x + b * y) := f_ineq x y

lemma prekopa_leindler_one_iSup_top
    (f g h : ℝ → ℝ≥0∞)
    (f_meas : Measurable f) (g_meas : Measurable g) (h_meas : Measurable h)
    (a b : ℝ) (hab : a + b = 1)
    (f_ineq : ∀ x y, f (a * x + b * y) ≥ g x ^ a * h y ^ b)
    (a_pos : 0 < a) (b_pos : 0 < b)
    (hg : 0 < ∫⁻ x, g x) (hh_top : ⨆ x, h x = ∞) :
    ∫⁻ x, f x ≥ (∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b := by
  suffices hfinf : ∞ ≤ ∫⁻ x, f x by
    exact (eq_top_iff.mpr hfinf).symm.le.trans' le_top
  obtain ⟨u, u_pos, hu⟩ :
      ∃ t : ℝ≥0∞, 0 < t ∧ 0 < volume {x | t < g x} := by
    rw [lintegral_eq_lintegral_meas_lt_ennreal volume g_meas] at hg
    by_contra hnot
    push_neg at hnot
    have hzero : ∀ t : ℝ, 0 < t →
        volume {x | ENNReal.ofReal t < g x} = 0 := by
      intro t ht
      exact le_antisymm (hnot (ENNReal.ofReal t) (ENNReal.ofReal_pos.mpr ht)) bot_le
    have : (∫⁻ (t : ℝ) in Ioi 0, volume {x | ENNReal.ofReal t < g x}) = 0 := by
      apply setLIntegral_eq_zero measurableSet_Ioi
      intro t ht
      exact hzero t (mem_Ioi.mp ht)
    exact (hg.ne' (by simpa [this] using this)).elim
  let c := volume {x | u < g x}
  have hc : 0 < c := hu
  suffices hnat : ∀ n : ℕ, (n : ℝ≥0∞) * (ENNReal.ofReal a * c) ≤ ∫⁻ x, f x by
    calc
      ∞ = (⨆ n : ℕ, (n : ℝ≥0∞)) * (ENNReal.ofReal a * c) := by
        rw [ENNReal.iSup_natCast, ENNReal.top_mul]
        exact (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr a_pos).ne' hc.ne').ne'
      _ ≤ ∫⁻ x, f x := by
        rw [ENNReal.iSup_mul]
        exact iSup_le hnat
  intro n
  rcases n.eq_zero_or_pos with rfl | n_pos
  · simp
  have hlevel : ENNReal.ofReal a * c ≤ volume {x | (n : ℝ≥0∞) ≤ f x} := by
    have hstrict : ENNReal.ofReal a * c ≤ volume {x | (n : ℝ≥0∞) < f x} := by
      have hu_exists : ∃ x, u < g x := nonempty_of_measure_ne_zero hu.ne'
      have u_fin : u < ∞ := by
        by_contra hutop
        have : u = ∞ := top_unique (not_lt.mp hutop)
        subst u
        simpa using hu
      obtain ⟨v, v_fin, huv⟩ :
          ∃ v : ℝ≥0∞, v < ∞ ∧ (n : ℝ≥0∞) ≤ u ^ a * v ^ b := by
        have hua_pos : 0 < u ^ a := ENNReal.rpow_pos_of_nonneg u_pos a_pos.le
        refine ⟨((n : ℝ≥0∞) / u ^ a) ^ b⁻¹, ?_, ?_⟩
        · exact ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.2 b_pos.le)
            (ENNReal.div_lt_top ENNReal.coe_ne_top hua_pos.ne').ne
        · have hua_fin : u ^ a ≠ ∞ :=
            (ENNReal.rpow_lt_top_of_nonneg a_pos.le u_fin.ne).ne
          rw [← ENNReal.rpow_mul, inv_mul_cancel₀ b_pos.ne', ENNReal.rpow_one,
            ENNReal.mul_div_cancel hua_pos.ne' hua_fin]
      obtain ⟨y, hy⟩ : ∃ y, v < h y :=
        (iSup_eq_top.mp hh_top) v v_fin
      exact (le_self_add.trans <| prekopa_slice_one f g h f_meas g_meas h_meas
        a b hab f_ineq a_pos b_pos hu_exists ⟨y, hy⟩ huv)
    exact hstrict.trans <| measure_mono fun z hz ↦ by
      change (n : ℝ≥0∞) < f z at hz
      change (n : ℝ≥0∞) ≤ f z
      exact hz.le
  calc
    (n : ℝ≥0∞) * (ENNReal.ofReal a * c)
        ≤ (n : ℝ≥0∞) * volume {x | (n : ℝ≥0∞) ≤ f x} :=
      by gcongr
    _ ≤ ∫⁻ x, f x := mul_meas_ge_le_lintegral f_meas n

lemma prekopa_leindler_one_iSup_one
    (f g h : ℝ → ℝ≥0∞)
    (f_meas : Measurable f) (g_meas : Measurable g) (h_meas : Measurable h)
    (a b : ℝ) (hab : a + b = 1)
    (f_ineq : ∀ x y, f (a * x + b * y) ≥ g x ^ a * h y ^ b)
    (a_pos : 0 < a) (b_pos : 0 < b)
    (hg : ⨆ x, g x = 1) (hh : ⨆ x, h x = 1) :
    ∫⁻ x, f x ≥ (∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b := by
  rw [lintegral_eq_lintegral_meas_lt_ennreal volume f_meas,
    lintegral_eq_lintegral_meas_lt_ennreal volume g_meas,
    lintegral_eq_lintegral_meas_lt_ennreal volume h_meas]
  refine (ennreal_geomMean_le_arithMean2_weighted a b
    (∫⁻ (t : ℝ) in Ioi 0, volume {x | ENNReal.ofReal t < g x})
    (∫⁻ (t : ℝ) in Ioi 0, volume {x | ENNReal.ofReal t < h x})
    a_pos.le b_pos.le hab).trans ?_
  rw [← lintegral_const_mul, ← lintegral_const_mul, ← lintegral_add_left]
  · apply setLIntegral_mono'
    · exact measurableSet_Ioi
    · intro t ht
      rcases lt_or_ge (ENNReal.ofReal t) 1 with ht1 | ht1
      · apply prekopa_slice_one f g h f_meas g_meas h_meas
          a b hab f_ineq a_pos b_pos
        · exact lt_iSup_iff.mp (hg ▸ ht1)
        · exact lt_iSup_iff.mp (hh ▸ ht1)
        · rcases eq_or_ne (ENNReal.ofReal t) 0 with ht0 | ht0
          · simpa [ht0]
          · rw [← ENNReal.rpow_add a b ht0 ENNReal.ofReal_ne_top,
              hab, ENNReal.rpow_one]
      · apply le_trans (le_of_eq ?_) bot_le
        change ENNReal.ofReal a * volume {x | ENNReal.ofReal t < g x} +
          ENNReal.ofReal b * volume {x | ENNReal.ofReal t < h x} = (0 : ℝ≥0∞)
        rw [add_eq_zero]
        constructor
        · apply mul_eq_zero_of_right
          rw [show {x | ENNReal.ofReal t < g x} = ∅ by
            ext x
            simp only [mem_setOf_eq, not_lt, mem_empty_iff_false, iff_false]
            exact ((le_iSup g x).trans_eq hg).trans ht1]
          exact measure_empty
        · apply mul_eq_zero_of_right
          rw [show {x | ENNReal.ofReal t < h x} = ∅ by
            ext x
            simp only [mem_setOf_eq, not_lt, mem_empty_iff_false, iff_false]
            exact ((le_iSup h x).trans_eq hh).trans ht1]
          exact measure_empty
  all_goals
    apply Antitone.measurable
    intro t₁ t₂ ht
    dsimp only
    gcongr

theorem prekopa_leindler_one
    (f g h : ℝ → ℝ≥0∞)
    (f_meas : Measurable f) (g_meas : Measurable g) (h_meas : Measurable h)
    (a b : ℝ) (a_nonneg : 0 ≤ a) (b_nonneg : 0 ≤ b) (hab : a + b = 1)
    (f_ineq : ∀ x y, f (a * x + b * y) ≥ g x ^ a * h y ^ b) :
    ∫⁻ x, f x ≥ (∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b := by
  rcases a_nonneg.eq_or_lt with rfl | a_pos
  · have hb : b = 1 := by linarith
    subst b
    convert lintegral_mono (fun y ↦ show h y ≤ f y by
      simpa using f_ineq 0 y) using 1 <;> simp
  rcases b_nonneg.eq_or_lt with rfl | b_pos
  · have ha : a = 1 := by linarith
    subst a
    convert lintegral_mono (fun x ↦ show g x ≤ f x by
      simpa using f_ineq x 0) using 1 <;> simp
  rcases eq_or_lt_of_le (show 0 ≤ ∫⁻ x, g x from bot_le) with hg_zero | hg_pos
  · rw [← hg_zero, ENNReal.zero_rpow_of_pos a_pos, zero_mul]
    exact bot_le
  rcases eq_or_lt_of_le (show 0 ≤ ∫⁻ x, h x from bot_le) with hh_zero | hh_pos
  · rw [← hh_zero, ENNReal.zero_rpow_of_pos b_pos, mul_zero]
    exact bot_le
  have cg_pos : 0 < ⨆ x, g x := by
    by_contra hcg
    have hcg0 : ⨆ x, g x = 0 := bot_unique (not_lt.mp hcg)
    have : g = 0 := funext fun x ↦ bot_unique ((le_iSup g x).trans_eq hcg0)
    subst g
    simpa using hg_pos
  have ch_pos : 0 < ⨆ x, h x := by
    by_contra hch
    have hch0 : ⨆ x, h x = 0 := bot_unique (not_lt.mp hch)
    have : h = 0 := funext fun x ↦ bot_unique ((le_iSup h x).trans_eq hch0)
    subst h
    simpa using hh_pos
  rcases eq_or_ne (⨆ x, h x) ∞ with ch_top | ch_fin
  · exact prekopa_leindler_one_iSup_top f g h f_meas g_meas h_meas
      a b hab f_ineq a_pos b_pos hg_pos ch_top
  rcases eq_or_ne (⨆ x, g x) ∞ with cg_top | cg_fin
  · rw [mul_comm]
    apply prekopa_leindler_one_iSup_top f h g f_meas h_meas g_meas
      b a (by linarith) _ b_pos a_pos hh_pos cg_top
    intro x y
    convert f_ineq y x using 1 <;> ring_nf
  have cg_lt_top : (⨆ x, g x) < ∞ := lt_top_iff_ne_top.mpr cg_fin
  have ch_lt_top : (⨆ x, h x) < ∞ := lt_top_iff_ne_top.mpr ch_fin
  let cgi := (⨆ x, g x)⁻¹
  let chi := (⨆ x, h x)⁻¹
  let c := cgi ^ a * chi ^ b
  have cgi_pos : 0 < cgi := ENNReal.inv_pos.mpr cg_fin
  have chi_pos : 0 < chi := ENNReal.inv_pos.mpr ch_fin
  have cgi_fin : cgi < ∞ := ENNReal.inv_lt_top.mpr cg_pos
  have chi_fin : chi < ∞ := ENNReal.inv_lt_top.mpr ch_pos
  have c_pos : 0 < c := ENNReal.mul_pos
    (ENNReal.rpow_pos cgi_pos cgi_fin.ne).ne'
    (ENNReal.rpow_pos chi_pos chi_fin.ne).ne'
  have c_fin : c < ∞ := ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg a_pos.le cgi_fin.ne)
    (ENNReal.rpow_lt_top_of_nonneg b_pos.le chi_fin.ne)
  let f' := fun x ↦ c * f x
  let g' := fun x ↦ cgi * g x
  let h' := fun x ↦ chi * h x
  have f'_meas : Measurable f' := f_meas.const_mul c
  have g'_meas : Measurable g' := g_meas.const_mul cgi
  have h'_meas : Measurable h' := h_meas.const_mul chi
  have f'_ineq : ∀ x y, f' (a * x + b * y) ≥ g' x ^ a * h' y ^ b := by
    intro x y
    dsimp only [f', g', h']
    rw [ENNReal.mul_rpow_of_nonneg _ _ a_pos.le,
      ENNReal.mul_rpow_of_nonneg _ _ b_pos.le]
    change cgi ^ a * g x ^ a * (chi ^ b * h y ^ b) ≤ c * f (a * x + b * y)
    calc
      _ = c * (g x ^ a * h y ^ b) := by simp only [c]; ac_rfl
      _ ≤ c * f (a * x + b * y) := by gcongr; exact f_ineq x y
  have hnorm := prekopa_leindler_one_iSup_one f' g' h'
    f'_meas g'_meas h'_meas a b hab f'_ineq a_pos b_pos
  have hg' : ⨆ x, g' x = 1 := by
    rw [show g' = fun x ↦ cgi * g x from rfl, ← ENNReal.mul_iSup]
    exact ENNReal.inv_mul_cancel cg_pos.ne' cg_fin
  have hh' : ⨆ x, h' x = 1 := by
    rw [show h' = fun x ↦ chi * h x from rfl, ← ENNReal.mul_iSup]
    exact ENNReal.inv_mul_cancel ch_pos.ne' ch_fin
  specialize hnorm hg' hh'
  dsimp only [f', g', h'] at hnorm
  rw [lintegral_const_mul' c f c_fin.ne,
    lintegral_const_mul' cgi g cgi_fin.ne,
    lintegral_const_mul' chi h chi_fin.ne] at hnorm
  rw [ENNReal.mul_rpow_of_nonneg _ _ a_pos.le,
    ENNReal.mul_rpow_of_nonneg _ _ b_pos.le] at hnorm
  have hnorm' : c * (∫⁻ x, f x) ≥
      c * ((∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b) := by
    calc
      _ ≥ cgi ^ a * (∫⁻ x, g x) ^ a *
          (chi ^ b * (∫⁻ x, h x) ^ b) := hnorm
      _ = _ := by simp only [c]; ac_rfl
  calc
    (∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b =
        c⁻¹ * (c * ((∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel c_pos.ne' c_fin.ne, one_mul]
    _ ≤ c⁻¹ * (c * ∫⁻ x, f x) := by
      simpa only [mul_comm] using mul_le_mul_left hnorm' c⁻¹
    _ = ∫⁻ x, f x := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel c_pos.ne' c_fin.ne, one_mul]

/-! ### Tensorization to finite real coordinate spaces -/

/-- The Prékopa--Leindler property for a real module with its specified volume. -/
def HasPrekopaLeindler (E : Type*) [AddCommMonoid E] [Module ℝ E]
    [MeasureSpace E] : Prop :=
  ∀ (f g h : E → ℝ≥0∞),
    Measurable f → Measurable g → Measurable h →
    ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
    (∀ x y, f (a • x + b • y) ≥ g x ^ a * h y ^ b) →
    ∫⁻ x, f x ≥ (∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b

theorem hasPrekopaLeindler_of_measurePreserving_linearEquiv
    {E F : Type*}
    [AddCommMonoid E] [Module ℝ E] [MeasureSpace E]
    [AddCommMonoid F] [Module ℝ F] [MeasureSpace F]
    (e : E ≃ₗ[ℝ] F)
    (he : MeasurePreserving e (volume : Measure E) (volume : Measure F))
    (hE : HasPrekopaLeindler E) : HasPrekopaLeindler F := by
  intro f g h hf hg hh a b ha hb hab hineq
  have hcomp : ∀ x y,
      (f ∘ e) (a • x + b • y) ≥ (g ∘ e) x ^ a * (h ∘ e) y ^ b := by
    intro x y
    simpa using hineq (e x) (e y)
  have H := hE (f ∘ e) (g ∘ e) (h ∘ e)
    (hf.comp he.measurable) (hg.comp he.measurable) (hh.comp he.measurable)
    a b ha hb hab hcomp
  change (∫⁻ x, f (e x)) ≥
    (∫⁻ x, g (e x)) ^ a * (∫⁻ x, h (e x)) ^ b at H
  rw [he.lintegral_comp hf, he.lintegral_comp hg, he.lintegral_comp hh] at H
  exact H

theorem hasPrekopaLeindler_prod
    {E F : Type*}
    [AddCommMonoid E] [Module ℝ E] [MeasureSpace E]
    [AddCommMonoid F] [Module ℝ F] [MeasureSpace F]
    [SigmaFinite (volume : Measure E)] [SigmaFinite (volume : Measure F)]
    (hE : HasPrekopaLeindler E) (hF : HasPrekopaLeindler F) :
    HasPrekopaLeindler (E × F) := by
  intro f g h hf hg hh a b ha hb hab hineq
  rw [Measure.volume_eq_prod, lintegral_prod _ hf.aemeasurable,
    lintegral_prod _ hg.aemeasurable, lintegral_prod _ hh.aemeasurable]
  apply hE
  · exact hf.lintegral_prod_right'
  · exact hg.lintegral_prod_right'
  · exact hh.lintegral_prod_right'
  · exact ha
  · exact hb
  · exact hab
  · intro x₁ y₁
    apply hF
    · exact hf.comp measurable_prodMk_left
    · exact hg.comp measurable_prodMk_left
    · exact hh.comp measurable_prodMk_left
    · exact ha
    · exact hb
    · exact hab
    · intro x₂ y₂
      simpa using hineq (x₁, x₂) (y₁, y₂)

theorem hasPrekopaLeindler_real : HasPrekopaLeindler ℝ := by
  intro f g h hf hg hh a b ha hb hab hineq
  simpa only [smul_eq_mul] using
    prekopa_leindler_one f g h hf hg hh a b ha hb hab hineq

theorem hasPrekopaLeindler_fin_zero : HasPrekopaLeindler (Fin 0 → ℝ) := by
  intro f g h hf hg hh a b ha hb hab hineq
  simp only [lintegral_unique, volume_pi, Measure.pi_univ, Finset.prod_fin_eq_prod_range,
    Finset.prod_range_zero, mul_one]
  convert hineq 0 0

theorem hasPrekopaLeindler_fin_one : HasPrekopaLeindler (Fin 1 → ℝ) := by
  let e : ℝ ≃ₗ[ℝ] (Fin 1 → ℝ) :=
    (LinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  have he : MeasurePreserving e := by
    exact (volume_preserving_piUnique (fun _ : Fin 1 ↦ ℝ)).symm
  exact hasPrekopaLeindler_of_measurePreserving_linearEquiv e he
    hasPrekopaLeindler_real

theorem hasPrekopaLeindler_sum
    {I J : Type*} [Fintype I] [Fintype J]
    (hI : HasPrekopaLeindler (I → ℝ))
    (hJ : HasPrekopaLeindler (J → ℝ)) :
    HasPrekopaLeindler (I ⊕ J → ℝ) := by
  let e : ((I → ℝ) × (J → ℝ)) ≃ₗ[ℝ] (I ⊕ J → ℝ) :=
    (LinearEquiv.sumPiEquivProdPi ℝ I J (fun _ ↦ ℝ)).symm
  have he : MeasurePreserving e := by
    exact (volume_measurePreserving_sumPiEquivProdPi (fun _ : I ⊕ J ↦ ℝ)).symm
  exact hasPrekopaLeindler_of_measurePreserving_linearEquiv e he
    (hasPrekopaLeindler_prod hI hJ)

theorem hasPrekopaLeindler_fin : ∀ n : ℕ, HasPrekopaLeindler (Fin n → ℝ)
  | 0 => hasPrekopaLeindler_fin_zero
  | n + 1 => by
      let ei : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
      let e : (Fin n ⊕ Fin 1 → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ) :=
        LinearEquiv.piCongrLeft ℝ (fun _ : Fin (n + 1) ↦ ℝ) ei
      have he : MeasurePreserving e := by
        exact volume_measurePreserving_piCongrLeft (fun _ : Fin (n + 1) ↦ ℝ) ei
      exact hasPrekopaLeindler_of_measurePreserving_linearEquiv e he
        (hasPrekopaLeindler_sum (hasPrekopaLeindler_fin n)
          hasPrekopaLeindler_fin_one)

theorem prekopa_leindler_fin {n : ℕ}
    (f g h : (Fin n → ℝ) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hineq : ∀ x y, f (a • x + b • y) ≥ g x ^ a * h y ^ b) :
    ∫⁻ x, f x ≥ (∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b :=
  hasPrekopaLeindler_fin n f g h hf hg hh a b ha hb hab hineq

theorem brunnMinkowski_multiplicative {n : ℕ}
    (A B : Set (Fin n → ℝ)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    volume (a • A + b • B) ≥ volume A ^ a * volume B ^ b := by
  rw [← measure_toMeasurable (a • A + b • B)]
  let C := toMeasurable volume (a • A + b • B)
  have hC : MeasurableSet C := measurableSet_toMeasurable _ _
  have H := prekopa_leindler_fin
    (C.indicator fun _ ↦ (1 : ℝ≥0∞))
    (A.indicator fun _ ↦ (1 : ℝ≥0∞))
    (B.indicator fun _ ↦ (1 : ℝ≥0∞))
    (measurable_const.indicator hC) (measurable_const.indicator hA)
    (measurable_const.indicator hB) a b ha.le hb.le hab ?_
  · simpa [C, measure_toMeasurable, lintegral_indicator_const hC,
      lintegral_indicator_const hA, lintegral_indicator_const hB] using H
  · intro x y
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ B
      · have hxy : a • x + b • y ∈ C := by
          apply subset_toMeasurable (volume : Measure (Fin n → ℝ))
          exact ⟨a • x, ⟨x, hx, rfl⟩, b • y, ⟨y, hy, rfl⟩, rfl⟩
        simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
          Set.indicator_of_mem hxy]
      · simp [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hb]
    · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos ha]

theorem brunnMinkowski_multiplicative_of_hasPrekopaLeindler
    {E : Type*} [AddCommMonoid E] [Module ℝ E] [MeasureSpace E]
    (hPL : HasPrekopaLeindler E)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    volume (a • A + b • B) ≥ volume A ^ a * volume B ^ b := by
  rw [← measure_toMeasurable (a • A + b • B)]
  let C := toMeasurable volume (a • A + b • B)
  have hC : MeasurableSet C := measurableSet_toMeasurable _ _
  have H := hPL
    (C.indicator fun _ ↦ (1 : ℝ≥0∞))
    (A.indicator fun _ ↦ (1 : ℝ≥0∞))
    (B.indicator fun _ ↦ (1 : ℝ≥0∞))
    (measurable_const.indicator hC) (measurable_const.indicator hA)
    (measurable_const.indicator hB) a b ha.le hb.le hab ?_
  · simpa [C, measure_toMeasurable, lintegral_indicator_const hC,
      lintegral_indicator_const hA, lintegral_indicator_const hB] using H
  · intro x y
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ B
      · have hxy : a • x + b • y ∈ C := by
          apply subset_toMeasurable (volume : Measure E)
          exact ⟨a • x, ⟨x, hx, rfl⟩, b • y, ⟨y, hy, rfl⟩, rfl⟩
        simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
          Set.indicator_of_mem hxy]
      · simp [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hb]
    · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos ha]

theorem hasPrekopaLeindler_euclidean (n : ℕ) :
    HasPrekopaLeindler (EuclideanSpace ℝ (Fin n)) := by
  let e : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  have he : MeasurePreserving e := by
    change MeasurePreserving (@WithLp.toLp 2 (Fin n → ℝ)) volume volume
    exact PiLp.volume_preserving_toLp (Fin n)
  exact hasPrekopaLeindler_of_measurePreserving_linearEquiv e he
    (hasPrekopaLeindler_fin n)

theorem brunnMinkowski_multiplicative_euclidean {n : ℕ}
    (A B : Set (EuclideanSpace ℝ (Fin n)))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    volume (a • A + b • B) ≥ volume A ^ a * volume B ^ b :=
  brunnMinkowski_multiplicative_of_hasPrekopaLeindler
    (hasPrekopaLeindler_euclidean n) A B hA hB a b ha hb hab

theorem euclidean_isodiametric {n : ℕ}
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) (d : ℝ) (hd : 0 ≤ d)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ d) :
    volume A ≤ volume (Metric.closedBall (0 : Fin n → ℝ) (d / 2)) := by
  let M : Set (Fin n → ℝ) := ((2 : ℝ)⁻¹ • A) + ((2 : ℝ)⁻¹ • (-A))
  have hnegA : MeasurableSet (-A) := hA.neg
  have hBM : volume M ≥
      volume A ^ (2 : ℝ)⁻¹ * volume (-A) ^ (2 : ℝ)⁻¹ := by
    exact brunnMinkowski_multiplicative A (-A) hA hnegA
      (2 : ℝ)⁻¹ (2 : ℝ)⁻¹ (by norm_num) (by norm_num) (by norm_num)
  have hmeasureNeg : volume (-A) = volume A := Measure.measure_neg volume A
  have hrpow : volume A ^ (2 : ℝ)⁻¹ * volume A ^ (2 : ℝ)⁻¹ = volume A := by
    rw [← ENNReal.rpow_add_of_nonneg (x := volume A)
      (2 : ℝ)⁻¹ (2 : ℝ)⁻¹ (by norm_num) (by norm_num)]
    norm_num
  have hvolAM : volume A ≤ volume M := by
    calc
      volume A = volume A ^ (2 : ℝ)⁻¹ * volume A ^ (2 : ℝ)⁻¹ := hrpow.symm
      _ = volume A ^ (2 : ℝ)⁻¹ * volume (-A) ^ (2 : ℝ)⁻¹ := by
        rw [hmeasureNeg]
      _ ≤ volume M := hBM
  refine hvolAM.trans (measure_mono ?_)
  intro z hz
  rcases hz with ⟨u, hu, v, hv, rfl⟩
  rcases hu with ⟨x, hx, rfl⟩
  rcases hv with ⟨ny, hny, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hhalf : (0 : ℝ) ≤ (2 : ℝ)⁻¹ := by norm_num
  calc
    ‖(2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • ny‖ =
        (2 : ℝ)⁻¹ * ‖x - (-ny)‖ := by
      rw [sub_neg_eq_add, ← smul_add, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hhalf]
    _ = (2 : ℝ)⁻¹ * dist x (-ny) := by rw [dist_eq_norm]
    _ ≤ (2 : ℝ)⁻¹ * d :=
      mul_le_mul_of_nonneg_left (hdiam x hx (-ny) hny) hhalf
    _ = d / 2 := by ring

theorem euclideanSpace_isodiametric {n : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin n))) (hA : MeasurableSet A)
    (d : ℝ) (hd : 0 ≤ d)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ d) :
    volume A ≤ volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (d / 2)) := by
  let M : Set (EuclideanSpace ℝ (Fin n)) :=
    ((2 : ℝ)⁻¹ • A) + ((2 : ℝ)⁻¹ • (-A))
  have hnegA : MeasurableSet (-A) := hA.neg
  have hBM : volume M ≥
      volume A ^ (2 : ℝ)⁻¹ * volume (-A) ^ (2 : ℝ)⁻¹ := by
    exact brunnMinkowski_multiplicative_euclidean A (-A) hA hnegA
      (2 : ℝ)⁻¹ (2 : ℝ)⁻¹ (by norm_num) (by norm_num) (by norm_num)
  have hmeasureNeg : volume (-A) = volume A := Measure.measure_neg volume A
  have hrpow : volume A ^ (2 : ℝ)⁻¹ * volume A ^ (2 : ℝ)⁻¹ = volume A := by
    rw [← ENNReal.rpow_add_of_nonneg (x := volume A)
      (2 : ℝ)⁻¹ (2 : ℝ)⁻¹ (by norm_num) (by norm_num)]
    norm_num
  have hvolAM : volume A ≤ volume M := by
    calc
      volume A = volume A ^ (2 : ℝ)⁻¹ * volume A ^ (2 : ℝ)⁻¹ := hrpow.symm
      _ = volume A ^ (2 : ℝ)⁻¹ * volume (-A) ^ (2 : ℝ)⁻¹ := by
        rw [hmeasureNeg]
      _ ≤ volume M := hBM
  refine hvolAM.trans (measure_mono ?_)
  intro z hz
  rcases hz with ⟨u, hu, v, hv, rfl⟩
  rcases hu with ⟨x, hx, rfl⟩
  rcases hv with ⟨ny, hny, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hhalf : (0 : ℝ) ≤ (2 : ℝ)⁻¹ := by norm_num
  calc
    ‖(2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • ny‖ =
        (2 : ℝ)⁻¹ * ‖x - (-ny)‖ := by
      rw [sub_neg_eq_add, ← smul_add, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hhalf]
    _ = (2 : ℝ)⁻¹ * dist x (-ny) := by rw [dist_eq_norm]
    _ ≤ (2 : ℝ)⁻¹ * d :=
      mul_le_mul_of_nonneg_left (hdiam x hx (-ny) hny) hhalf
    _ = d / 2 := by ring

theorem sphere_isodiametric {n : ℕ} (hn : 0 < n)
    (A : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hA : MeasurableSet A) (d : ℝ) (hd1 : 1 ≤ d)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ d) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere A ≤
      ENNReal.ofReal ((d / 2) ^ n) *
        (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ := by
  let C : Set (EuclideanSpace ℝ (Fin n)) :=
    Set.Ioo (0 : ℝ) 1 • ((↑) '' A)
  have hnorm (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
      ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.property
  have hcone : ∀ p ∈ C, ∀ q ∈ C, dist p q ≤ d := by
    intro p hp q hq
    rcases hp with ⟨r, hr, xr, hxr, rfl⟩
    rcases hxr with ⟨x, hx, rfl⟩
    rcases hq with ⟨s, hs, ys, hys, rfl⟩
    rcases hys with ⟨y, hy, rfl⟩
    have hxy : dist (x : EuclideanSpace ℝ (Fin n)) y ≤ d := by
      simpa only [Subtype.dist_eq] using hdiam x hx y hy
    have aux (hrs : r ≤ s) : dist
        (r • (x : EuclideanSpace ℝ (Fin n))) (s • (y : EuclideanSpace ℝ (Fin n))) ≤ d := by
      have hr0 : 0 ≤ r := hr.1.le
      have hrs0 : 0 ≤ s - r := sub_nonneg.mpr hrs
      calc
        dist (r • (x : EuclideanSpace ℝ (Fin n))) (s • (y : EuclideanSpace ℝ (Fin n))) =
            ‖r • ((x : EuclideanSpace ℝ (Fin n)) - y) + (r - s) • y‖ := by
          rw [dist_eq_norm]
          congr 1
          module
        _ ≤ ‖r • ((x : EuclideanSpace ℝ (Fin n)) - y)‖ + ‖(r - s) • (y : EuclideanSpace ℝ (Fin n))‖ :=
          norm_add_le _ _
        _ = r * dist (x : EuclideanSpace ℝ (Fin n)) y + (s - r) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hr0, abs_of_nonpos (sub_nonpos.mpr hrs), hnorm y,
            mul_one, dist_eq_norm]
          ring
        _ ≤ r * d + (s - r) := by gcongr
        _ ≤ d := by nlinarith [hr.2, hs.2]
    rcases le_total r s with hrs | hsr
    · exact aux hrs
    · rw [dist_comm]
      have hyx : dist (y : EuclideanSpace ℝ (Fin n)) x ≤ d := by
        simpa [dist_comm] using hxy
      have hs0 : 0 ≤ s := hs.1.le
      have hsr0 : 0 ≤ r - s := sub_nonneg.mpr hsr
      calc
        dist (s • (y : EuclideanSpace ℝ (Fin n))) (r • (x : EuclideanSpace ℝ (Fin n))) =
            ‖s • ((y : EuclideanSpace ℝ (Fin n)) - x) + (s - r) • x‖ := by
          rw [dist_eq_norm]
          congr 1
          module
        _ ≤ ‖s • ((y : EuclideanSpace ℝ (Fin n)) - x)‖ + ‖(s - r) • (x : EuclideanSpace ℝ (Fin n))‖ :=
          norm_add_le _ _
        _ = s * dist (y : EuclideanSpace ℝ (Fin n)) x + (r - s) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hs0, abs_of_nonpos (sub_nonpos.mpr hsr), hnorm x,
            mul_one, dist_eq_norm]
          ring
        _ ≤ s * d + (r - s) := by gcongr
        _ ≤ d := by nlinarith [hr.2, hs.2]
  have hCsubset : C ⊆ Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro p hp
    rcases hp with ⟨r, hr, xr, hxr, rfl⟩
    rcases hxr with ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr.1.le, hnorm x, mul_one]
    exact hr.2.le
  have hclosureSubset : closure C ⊆ Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    closure_minimal hCsubset Metric.isClosed_closedBall
  have hbounded : Bornology.IsBounded (closure C) :=
    Metric.isBounded_closedBall.subset hclosureSubset
  have hdiamC : Metric.diam C ≤ d :=
    Metric.diam_le_of_forall_dist_le (by linarith) hcone
  have hdiamClosure : ∀ p ∈ closure C, ∀ q ∈ closure C, dist p q ≤ d := by
    intro p hp q hq
    exact (Metric.dist_le_diam_of_mem hbounded hp hq).trans (by
      simpa only [Metric.diam_closure] using hdiamC)
  have hvolC : volume C ≤ volume
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (d / 2)) :=
    (measure_mono subset_closure).trans <|
      euclideanSpace_isodiametric (closure C) isClosed_closure.measurableSet d
        (by linarith) hdiamClosure
  rw [Measure.toSphere_apply' volume hA]
  simp only [finrank_euclideanSpace_fin]
  calc
    (n : ℝ≥0∞) * volume C ≤
        (n : ℝ≥0∞) * volume
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (d / 2)) := by gcongr
    _ = (n : ℝ≥0∞) *
        (ENNReal.ofReal ((d / 2) ^ n) * volume
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
      rw [Measure.addHaar_closedBall' volume (0 : EuclideanSpace ℝ (Fin n)) (by linarith),
        finrank_euclideanSpace_fin]
    _ = ENNReal.ofReal ((d / 2) ^ n) * volume.toSphere Set.univ := by
      rw [Measure.toSphere_apply_univ, finrank_euclideanSpace_fin,
        Measure.addHaar_unitClosedBall_eq_addHaar_unitBall]
      ac_rfl

lemma Gamma_half_step_sq_le {x : ℝ} (hx : 0 < x) :
    Real.Gamma (x + 1 / 2) ^ 2 ≤ x * Real.Gamma x ^ 2 := by
  have H := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
    hx (add_pos hx zero_lt_one) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hGx : 0 ≤ Real.Gamma x := (Real.Gamma_pos_of_pos hx).le
  have hGx1 : 0 ≤ Real.Gamma (x + 1) :=
    (Real.Gamma_pos_of_pos (add_pos hx zero_lt_one)).le
  have harg : (1 / 2 : ℝ) * x + 1 / 2 * (x + 1) = x + 1 / 2 := by ring
  rw [harg] at H
  have hsqrt : Real.Gamma x ^ (1 / 2 : ℝ) *
      Real.Gamma (x + 1) ^ (1 / 2 : ℝ) =
      Real.sqrt (Real.Gamma x * Real.Gamma (x + 1)) := by
    rw [Real.sqrt_eq_rpow, Real.mul_rpow hGx hGx1]
  rw [hsqrt, Real.Gamma_add_one hx.ne'] at H
  have hsquare := Real.sq_sqrt (mul_nonneg hGx (mul_nonneg hx.le hGx))
  have hGhalf : 0 ≤ Real.Gamma (x + 1 / 2) :=
    (Real.Gamma_pos_of_pos (by linarith)).le
  nlinarith [Real.sqrt_nonneg (Real.Gamma x * (x * Real.Gamma x))]

lemma unitBallConstant_le_sqrt_mul_succ (n : ℕ) :
    Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1) ≤
      Real.sqrt (n + 1 : ℝ) *
        (Real.sqrt Real.pi ^ (n + 1) /
          Real.Gamma (((n + 1 : ℕ) : ℝ) / 2 + 1)) := by
  let x : ℝ := (n : ℝ) / 2 + 1
  have hx : 0 < x := by positivity
  have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hGhalf : 0 < Real.Gamma (x + 1 / 2) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hsquare := Gamma_half_step_sq_le hx
  have hsqrtx : Real.Gamma (x + 1 / 2) ≤ Real.sqrt x * Real.Gamma x := by
    have hsqrt_sq : (Real.sqrt x * Real.Gamma x) ^ 2 = x * Real.Gamma x ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hx.le]
    have hsqrt_nonneg : 0 ≤ Real.sqrt x * Real.Gamma x :=
      mul_nonneg (Real.sqrt_nonneg _) hGx.le
    nlinarith
  have hxle : x ≤ (n + 1 : ℝ) := by
    dsimp only [x]
    norm_num
  have hsqrtle : Real.sqrt x ≤ Real.sqrt (n + 1 : ℝ) :=
    Real.sqrt_le_sqrt hxle
  have honepi : 1 ≤ Real.sqrt Real.pi := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    linarith [Real.pi_gt_three]
  have hGammaBound : Real.Gamma (x + 1 / 2) ≤
      Real.sqrt (n + 1 : ℝ) * Real.sqrt Real.pi * Real.Gamma x := by
    calc
      Real.Gamma (x + 1 / 2) ≤ Real.sqrt x * Real.Gamma x := hsqrtx
      _ ≤ Real.sqrt (n + 1 : ℝ) * Real.Gamma x := by gcongr
      _ ≤ Real.sqrt (n + 1 : ℝ) * Real.sqrt Real.pi * Real.Gamma x := by
        have hG : Real.Gamma x ≤ Real.sqrt Real.pi * Real.Gamma x := by
          nlinarith
        simpa [mul_assoc] using
          mul_le_mul_of_nonneg_left hG
            (Real.sqrt_nonneg (n + 1 : ℝ))
  have hpow : 0 ≤ Real.sqrt Real.pi ^ n := pow_nonneg (Real.sqrt_nonneg _) _
  have harg2 : (((n + 1 : ℕ) : ℝ) / 2 + 1) = x + 1 / 2 := by
    dsimp only [x]
    push_cast
    ring
  rw [harg2, ← mul_div_assoc, div_le_div_iff₀ hGx hGhalf]
  calc
    Real.sqrt Real.pi ^ n * Real.Gamma (x + 1 / 2) ≤ Real.sqrt Real.pi ^ n *
        (Real.sqrt (n + 1 : ℝ) * Real.sqrt Real.pi * Real.Gamma x) := by gcongr
    _ = _ := by rw [pow_succ]; ring

lemma exists_orthonormalBasis_zero_eq {n : ℕ}
    (x : EuclideanSpace ℝ (Fin (n + 1))) (hx : ‖x‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (n + 1)) ℝ
        (EuclideanSpace ℝ (Fin (n + 1))), b 0 = x := by
  let v : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) := fun _ ↦ x
  have hv : Orthonormal ℝ (({0} : Set (Fin (n + 1))).domRestrict v) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    simpa [v] using hx
  rcases Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n + 1)))
      (ι := Fin (n + 1)) (by simp) hv with ⟨b, hb⟩
  exact ⟨b, hb 0 (by simp)⟩

lemma euclidean_unitBall_slab_volume_bound {n : ℕ}
    (x : EuclideanSpace ℝ (Fin (n + 1))) (hx : ‖x‖ = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    volume {y : EuclideanSpace ℝ (Fin (n + 1)) |
        ‖y‖ ≤ 1 ∧ |inner ℝ x y| ≤ t} ≤
      ENNReal.ofReal (2 * t) *
        volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rcases exists_orthonormalBasis_zero_eq x hx with ⟨b, hb⟩
  let split := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) ↦ ℝ) 0
  let coord : EuclideanSpace ℝ (Fin (n + 1)) → ℝ × (Fin n → ℝ) :=
    fun y ↦ split (WithLp.ofLp (b.repr y))
  let tailBall : Set (Fin n → ℝ) :=
    (WithLp.toLp 2) ⁻¹'
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  let R : Set (ℝ × (Fin n → ℝ)) := Set.Icc (-t) t ×ˢ tailBall
  have hcoord : MeasurePreserving coord volume volume := by
    exact (volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) ↦ ℝ) 0).comp
        ((PiLp.volume_preserving_ofLp (Fin (n + 1))).comp
          b.measurePreserving_repr)
  have htailMeas : MeasurableSet tailBall := by
    exact measurableSet_closedBall.preimage
      (PiLp.volume_preserving_toLp (Fin n)).measurable
  have hRMeas : MeasurableSet R := measurableSet_Icc.prod htailMeas
  have htailVol : volume tailBall =
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    exact (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
      measurableSet_closedBall.nullMeasurableSet
  have hsubset : {y : EuclideanSpace ℝ (Fin (n + 1)) |
      ‖y‖ ≤ 1 ∧ |inner ℝ x y| ≤ t} ⊆ coord ⁻¹' R := by
    intro y hy
    have hfirst : (coord y).1 = inner ℝ x y := by
      simp [coord, split, hb, OrthonormalBasis.repr_apply_apply]
    have htail : ‖WithLp.toLp 2 (coord y).2‖ ≤ 1 := by
      let z := b.repr y
      have hnormz : ‖z‖ = ‖y‖ := b.repr.norm_map y
      have hsqTail : ‖WithLp.toLp 2 (coord y).2‖ ^ 2 ≤ ‖z‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
        rw [Fin.sum_univ_succAbove (fun i : Fin (n + 1) ↦
          ‖z.ofLp i‖ ^ 2) 0]
        simp only [coord, split, z, MeasurableEquiv.piFinSuccAbove_apply]
        exact le_add_of_nonneg_left (sq_nonneg _)
      have htailz : ‖WithLp.toLp 2 (coord y).2‖ ≤ ‖z‖ :=
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsqTail
      exact htailz.trans (by simpa [hnormz] using hy.1)
    constructor
    · constructor
      · rw [hfirst]
        exact neg_le_of_abs_le hy.2
      · rw [hfirst]
        exact (le_abs_self _).trans hy.2
    · simpa [tailBall, Metric.mem_closedBall, dist_zero_right] using htail
  calc
    volume {y : EuclideanSpace ℝ (Fin (n + 1)) |
        ‖y‖ ≤ 1 ∧ |inner ℝ x y| ≤ t} ≤ volume (coord ⁻¹' R) :=
      measure_mono hsubset
    _ = volume R := hcoord.measure_preimage hRMeas.nullMeasurableSet
    _ = volume (Set.Icc (-t) t) * volume tailBall := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]
    _ = ENNReal.ofReal (2 * t) *
        volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      rw [Real.volume_Icc, htailVol]
      congr 2
      ring

lemma euclidean_unitBall_volume_step {n : ℕ} (hn : 0 < n) :
    volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ≤
      ENNReal.ofReal (Real.sqrt (n + 1 : ℝ)) *
        volume (Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [EuclideanSpace.volume_closedBall, EuclideanSpace.volume_closedBall]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (unitBallConstant_le_sqrt_mul_succ n)

lemma spherical_equatorial_strip_bound {n : ℕ} (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (hx : ‖x‖ = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere
        {y | |inner ℝ x (y : EuclideanSpace ℝ (Fin (n + 1)))| ≤ t} ≤
      ENNReal.ofReal (2 * t * Real.sqrt (n + 1 : ℝ)) *
        (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere Set.univ := by
  let A : Set (Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    {y | |inner ℝ x (y : EuclideanSpace ℝ (Fin (n + 1)))| ≤ t}
  let C : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    Set.Ioo (0 : ℝ) 1 • ((↑) '' A)
  have hA : MeasurableSet A := by
    dsimp only [A]
    measurability
  have hnorm (y : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
      ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using y.property
  have hCsubset : C ⊆ {y : EuclideanSpace ℝ (Fin (n + 1)) |
      ‖y‖ ≤ 1 ∧ |inner ℝ x y| ≤ t} := by
    intro p hp
    rcases hp with ⟨r, hr, yr, hyr, rfl⟩
    rcases hyr with ⟨y, hy, rfl⟩
    constructor
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1.le, hnorm y,
        mul_one]
      exact hr.2.le
    · rw [inner_smul_right, abs_mul, abs_of_nonneg hr.1.le]
      calc
        r * |inner ℝ x (y : EuclideanSpace ℝ (Fin (n + 1)))| ≤
            1 * |inner ℝ x (y : EuclideanSpace ℝ (Fin (n + 1)))| := by
          exact mul_le_mul_of_nonneg_right hr.2.le (abs_nonneg _)
        _ ≤ t := by simpa [A] using hy
  have hCvol : volume C ≤ ENNReal.ofReal (2 * t) *
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    (measure_mono hCsubset).trans (euclidean_unitBall_slab_volume_bound x hx t ht)
  have hstep := euclidean_unitBall_volume_step hn
  rw [Measure.toSphere_apply' volume hA]
  simp only [finrank_euclideanSpace_fin]
  calc
    ((n + 1 : ℕ) : ℝ≥0∞) * volume C ≤
        ((n + 1 : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (2 * t) *
            volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
      gcongr
    _ ≤ ((n + 1 : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (2 * t) *
            (ENNReal.ofReal (Real.sqrt (n + 1 : ℝ)) *
              volume (Metric.closedBall
                (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) := by
      gcongr
    _ = ENNReal.ofReal (2 * t * Real.sqrt (n + 1 : ℝ)) *
        volume.toSphere Set.univ := by
      rw [Measure.toSphere_apply_univ, finrank_euclideanSpace_fin,
        Measure.addHaar_unitClosedBall_eq_addHaar_unitBall]
      calc
        ((n + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal (2 * t) *
              (ENNReal.ofReal (Real.sqrt (n + 1 : ℝ)) *
                volume (Metric.ball
                  (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) =
            ((n + 1 : ℕ) : ℝ≥0∞) *
              (ENNReal.ofReal (2 * t) *
                ENNReal.ofReal (Real.sqrt (n + 1 : ℝ))) *
              volume (Metric.ball
                (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by ac_rfl
        _ = ((n + 1 : ℕ) : ℝ≥0∞) *
              ENNReal.ofReal (2 * t * Real.sqrt (n + 1 : ℝ)) *
              volume (Metric.ball
                (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
          rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * t)]
        _ = ENNReal.ofReal (2 * t * Real.sqrt (n + 1 : ℝ)) *
            (((n + 1 : ℕ) : ℝ≥0∞) *
              volume (Metric.ball
                (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by ac_rfl

end Erdos615.BrunnMinkowski

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos615/Erdos615Construction.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/


open Set Real MeasureTheory
open scoped ENNReal NNReal Pointwise Topology BigOperators

namespace Erdos615.Construction

lemma packingNumber_ne_top_of_isCompact
    {X : Type*} [PseudoMetricSpace X] {A : Set X}
    {ε : ℝ≥0} (hε : ε ≠ 0) (hA : IsCompact A) :
    Metric.packingNumber ε A ≠ ⊤ := by
  rcases Metric.exists_finite_isCover_of_isCompact (s := A) (ε := ε / 2)
      (by positivity) hA with ⟨D, hDA, hDfin, hDcover⟩
  have hp : Metric.packingNumber ε A ≤ D.encard := by
    calc
      Metric.packingNumber ε A = Metric.packingNumber (2 * (ε / 2)) A := by
        congr 2
        field_simp
      _ ≤ Metric.externalCoveringNumber (ε / 2) A :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber (ε / 2) A
      _ ≤ D.encard := hDcover.externalCoveringNumber_le_encard
  exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hDfin) hp

section Partition

variable (h : ℕ) (ρ : ℝ)

abbrev Sphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin h)) 1

noncomputable def net : Set (Sphere h) :=
  Metric.maximalSeparatedSet (Real.toNNReal ρ) Set.univ

lemma net_finite (hρ : 0 < ρ) : (net h ρ).Finite := by
  rw [← Set.encard_ne_top_iff]
  change (Metric.maximalSeparatedSet (Real.toNNReal ρ)
    (Set.univ : Set (Sphere h))).encard ≠ ⊤
  have htop : Metric.packingNumber (Real.toNNReal ρ)
      (Set.univ : Set (Sphere h)) ≠ ⊤ :=
    packingNumber_ne_top_of_isCompact (X := Sphere h)
      (A := Set.univ) (ne_of_gt (Real.toNNReal_pos.mpr hρ)) isCompact_univ
  rw [Metric.encard_maximalSeparatedSet htop]
  exact htop

noncomputable def netFintype (hρ : 0 < ρ) : Fintype (net h ρ) :=
  (net_finite h ρ hρ).fintype

noncomputable def netCard (hρ : 0 < ρ) : ℕ :=
  @Fintype.card (net h ρ) (netFintype h ρ hρ)

noncomputable def center (hρ : 0 < ρ) : Fin (netCard h ρ hρ) → Sphere h :=
  fun i ↦ ((@Fintype.equivFin (net h ρ)
    (netFintype h ρ hρ)).symm i : net h ρ).1

lemma center_mem_net (hρ : 0 < ρ) (i : Fin (netCard h ρ hρ)) :
    center h ρ hρ i ∈ net h ρ :=
  ((@Fintype.equivFin (net h ρ) (netFintype h ρ hρ)).symm i : net h ρ).2

lemma center_injective (hρ : 0 < ρ) :
    Function.Injective (center h ρ hρ) := by
  intro i j hij
  apply (@Fintype.equivFin (net h ρ) (netFintype h ρ hρ)).symm.injective
  apply Subtype.ext
  exact hij

lemma netCard_pos (hh : 0 < h) (hρ : 0 < ρ) : 0 < netCard h ρ hρ := by
  have hsphere : (Set.univ : Set (Sphere h)).Nonempty := by
    let i : Fin h := ⟨0, hh⟩
    refine ⟨⟨EuclideanSpace.single i 1, ?_⟩, Set.mem_univ _⟩
    simp [Metric.mem_sphere, dist_zero_right]
  have hp : 0 < Metric.packingNumber (Real.toNNReal ρ)
      (Set.univ : Set (Sphere h)) := Metric.packingNumber_pos_iff.mpr hsphere
  have htop := packingNumber_ne_top_of_isCompact
    (A := (Set.univ : Set (Sphere h)))
    (ε := Real.toNNReal ρ) (ne_of_gt (Real.toNNReal_pos.mpr hρ)) isCompact_univ
  have henc : (net h ρ).encard = Metric.packingNumber (Real.toNNReal ρ)
      (Set.univ : Set (Sphere h)) := Metric.encard_maximalSeparatedSet htop
  have hnonempty : (net h ρ).Nonempty := Set.encard_pos.mp (henc.symm ▸ hp)
  exact (@Fintype.card_pos_iff (net h ρ) (netFintype h ρ hρ)).mpr
    (Set.nonempty_coe_sort.mpr hnonempty)

lemma net_isCover (hρ : 0 < ρ) :
    Metric.IsCover (Real.toNNReal ρ) (Set.univ : Set (Sphere h)) (net h ρ) := by
  have htop : Metric.packingNumber (Real.toNNReal ρ)
      (Set.univ : Set (Sphere h)) ≠ ⊤ :=
    packingNumber_ne_top_of_isCompact (X := Sphere h)
      (A := Set.univ) (ne_of_gt (Real.toNNReal_pos.mpr hρ)) isCompact_univ
  exact Metric.isCover_maximalSeparatedSet htop

lemma center_surjective (hρ : 0 < ρ) (z : Sphere h) (hz : z ∈ net h ρ) :
    ∃ i, center h ρ hρ i = z := by
  let z' : net h ρ := ⟨z, hz⟩
  let i := (@Fintype.equivFin (net h ρ) (netFintype h ρ hρ)) z'
  refine ⟨i, ?_⟩
  simp [center, i, z']

lemma center_cover (hρ : 0 < ρ) (y : Sphere h) :
    ∃ i : Fin (netCard h ρ hρ), dist y (center h ρ hρ i) ≤ ρ := by
  rcases net_isCover h ρ hρ (Set.mem_univ y) with ⟨z, hz, hyz⟩
  rcases center_surjective h ρ hρ z hz with ⟨i, rfl⟩
  refine ⟨i, ?_⟩
  have hd : dist y (center h ρ hρ i) ≤ (Real.toNNReal ρ : ℝ) := by
    exact_mod_cast (edist_le_coe.mp hyz)
  simpa [Real.coe_toNNReal ρ hρ.le] using hd

noncomputable def coveringBall (hρ : 0 < ρ) (n : ℕ) : Set (Sphere h) :=
  if hn : n < netCard h ρ hρ then
    Metric.closedBall (center h ρ hρ ⟨n, hn⟩) ρ
  else ∅

noncomputable def cell (hρ : 0 < ρ) (i : Fin (netCard h ρ hρ)) : Set (Sphere h) :=
  disjointed (coveringBall h ρ hρ) i

lemma coveringBall_measurable (hρ : 0 < ρ) (n : ℕ) :
    MeasurableSet (coveringBall h ρ hρ n) := by
  unfold coveringBall
  split_ifs
  · exact measurableSet_closedBall
  · exact MeasurableSet.empty

lemma cell_measurable (hρ : 0 < ρ) (i : Fin (netCard h ρ hρ)) :
    MeasurableSet (cell h ρ hρ i) := by
  exact MeasurableSet.disjointed (coveringBall_measurable h ρ hρ) i

lemma cell_subset_ball (hρ : 0 < ρ) (i : Fin (netCard h ρ hρ)) :
    cell h ρ hρ i ⊆ Metric.closedBall (center h ρ hρ i) ρ := by
  exact (disjointed_subset (coveringBall h ρ hρ) i).trans (by
    simp [coveringBall, i.isLt])

lemma cell_pairwiseDisjoint (hρ : 0 < ρ) :
    Pairwise (fun i j : Fin (netCard h ρ hρ) ↦
      Disjoint (cell h ρ hρ i) (cell h ρ hρ j)) := by
  intro i j hij
  exact disjoint_disjointed (coveringBall h ρ hρ)
    (fun hv ↦ hij (Fin.ext hv))

lemma iUnion_coveringBall (hρ : 0 < ρ) :
    ⋃ n : ℕ, coveringBall h ρ hρ n = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  rcases center_cover h ρ hρ y with ⟨i, hi⟩
  refine Set.mem_iUnion.mpr ⟨i.val, ?_⟩
  simp [coveringBall, i.isLt, Metric.mem_closedBall, hi]

lemma iUnion_cell (hρ : 0 < ρ) :
    ⋃ i : Fin (netCard h ρ hρ), cell h ρ hρ i = Set.univ := by
  have hall : ⋃ n : ℕ, disjointed (coveringBall h ρ hρ) n = Set.univ := by
    rw [iUnion_disjointed, iUnion_coveringBall h ρ hρ]
  apply Set.eq_univ_of_forall
  intro y
  have hy : y ∈ ⋃ n : ℕ, disjointed (coveringBall h ρ hρ) n := by
    rw [hall]
    trivial
  rcases Set.mem_iUnion.mp hy with ⟨n, hn⟩
  have hnlt : n < netCard h ρ hρ := by
    by_contra hnlt
    have hempty : coveringBall h ρ hρ n = ∅ := by
      simp [coveringBall, Nat.not_lt.mp hnlt]
    have : y ∈ coveringBall h ρ hρ n :=
      disjointed_subset (coveringBall h ρ hρ) n hn
    rw [hempty] at this
    exact this
  exact Set.mem_iUnion.mpr ⟨⟨n, hnlt⟩, hn⟩

lemma cell_dist_le_two_mul (hρ : 0 < ρ) (i : Fin (netCard h ρ hρ))
    {x y : Sphere h} (hx : x ∈ cell h ρ hρ i) (hy : y ∈ cell h ρ hρ i) :
    dist x y ≤ 2 * ρ := by
  have hxc := cell_subset_ball h ρ hρ i hx
  have hyc := cell_subset_ball h ρ hρ i hy
  rw [Metric.mem_closedBall] at hxc hyc
  calc
    dist x y ≤ dist x (center h ρ hρ i) + dist (center h ρ hρ i) y :=
      dist_triangle _ _ _
    _ ≤ ρ + ρ := add_le_add hxc (by simpa [dist_comm] using hyc)
    _ = 2 * ρ := by ring

lemma center_dist_gt (hρ : 0 < ρ)
    {i j : Fin (netCard h ρ hρ)} (hij : i ≠ j) :
    ρ < dist (center h ρ hρ i) (center h ρ hρ j) := by
  have hsep := Metric.isSeparated_maximalSeparatedSet
    (A := (Set.univ : Set (Sphere h))) (ε := Real.toNNReal ρ)
  have hed : (Real.toNNReal ρ : ℝ≥0∞) <
      edist (center h ρ hρ i) (center h ρ hρ j) :=
    hsep (center_mem_net h ρ hρ i) (center_mem_net h ρ hρ j)
      ((center_injective h ρ hρ).ne hij)
  rw [edist_dist] at hed
  apply (ENNReal.ofReal_lt_ofReal_iff
    (dist_pos.mpr ((center_injective h ρ hρ).ne hij))).mp
  simpa [ENNReal.ofReal, Real.coe_toNNReal ρ hρ.le] using hed

lemma netCard_mul_ballBound_le (hh : 0 < h) (hρ : 0 < ρ) :
    (netCard h ρ hρ : ℝ≥0∞) *
        (Measure.toSphereBallBound h (ρ / 2) : ℝ≥0∞) ≤ (h : ℝ≥0∞) := by
  let μ : Measure (Sphere h) :=
    (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere
  let q : ℝ≥0∞ := (Measure.toSphereBallBound h (ρ / 2) : ℝ≥0∞)
  let V : ℝ≥0∞ :=
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin h)) 1)
  let balls : Fin (netCard h ρ hρ) → Set (Sphere h) :=
    fun i ↦ Metric.ball (center h ρ hρ i) (ρ / 2)
  have hballs : (Set.univ : Set (Fin (netCard h ρ hρ))).PairwiseDisjoint balls := by
    intro i hi j hj hij
    apply Metric.ball_disjoint_ball
    have hd := center_dist_gt h ρ hρ hij
    linarith
  have hlower (i : Fin (netCard h ρ hρ)) : q * V ≤ μ (balls i) := by
    simpa [q, V, μ, balls, finrank_euclideanSpace_fin] using
      Measure.toSphereBallBound_mul_measure_unitBall_le_toSphere_ball
        (volume : Measure (EuclideanSpace ℝ (Fin h))) (by positivity : 0 < ρ / 2)
        (center h ρ hρ i)
  have hsum : (netCard h ρ hρ : ℝ≥0∞) * (q * V) ≤ μ Set.univ := by
    calc
      (netCard h ρ hρ : ℝ≥0∞) * (q * V) =
          ∑ i : Fin (netCard h ρ hρ), q * V := by simp
      _ ≤ ∑ i : Fin (netCard h ρ hρ), μ (balls i) := by
        exact Finset.sum_le_sum fun i _ ↦ hlower i
      _ = μ (⋃ i ∈ (Finset.univ : Finset (Fin (netCard h ρ hρ))), balls i) := by
        exact (measure_biUnion_finset (f := balls)
          (by simpa using hballs) (fun i _ ↦ measurableSet_ball)).symm
      _ = μ (⋃ i : Fin (netCard h ρ hρ), balls i) := by simp
      _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
  have hVpos : V ≠ 0 := by
    have hv : 0 < volume (Metric.ball
        (0 : EuclideanSpace ℝ (Fin h)) 1) :=
      Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin h)))
        (0 : EuclideanSpace ℝ (Fin h)) zero_lt_one
    exact ne_of_gt (by simpa [V] using hv)
  have hVtop : V ≠ ∞ := by
    exact ne_of_lt (by simpa [V] using
      (measure_ball_lt_top : volume
        (Metric.ball (0 : EuclideanSpace ℝ (Fin h)) 1) < ∞))
  have htotal : μ Set.univ = (h : ℝ≥0∞) * V := by
    simp [μ, V, Measure.toSphere_apply_univ, finrank_euclideanSpace_fin]
  rw [htotal] at hsum
  have : ((netCard h ρ hρ : ℝ≥0∞) * q) * V ≤ (h : ℝ≥0∞) * V := by
    simpa [mul_assoc] using hsum
  simpa [q] using (ENNReal.mul_le_mul_iff_left hVpos hVtop).mp this

lemma netCard_le_pow (hh : 0 < h) (hρ : 0 < ρ) (hρ4 : ρ ≤ 4) :
    (netCard h ρ hρ : ℝ) ≤ (8 / ρ) ^ h := by
  have hq : (Measure.toSphereBallBound h (ρ / 2) : ℝ) =
      (h : ℝ) * (ρ / 8) ^ h := by
    unfold Measure.toSphereBallBound
    rw [if_pos ⟨hh.ne', half_pos hρ⟩]
    norm_cast
    push_cast
    rw [min_eq_left]
    · congr 2
      · rw [Real.coe_toNNReal (ρ / 2) (half_pos hρ).le]
        ring
    · simp only [Real.coe_toNNReal (ρ / 2) (half_pos hρ).le,
        NNReal.coe_ofNat]
      linarith
  have hmain := netCard_mul_ballBound_le h ρ hh hρ
  have hmainReal : (netCard h ρ hρ : ℝ) *
      (Measure.toSphereBallBound h (ρ / 2) : ℝ) ≤ (h : ℝ) := by
    exact_mod_cast hmain
  rw [hq] at hmainReal
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hsmall : (netCard h ρ hρ : ℝ) * (ρ / 8) ^ h ≤ 1 := by
    nlinarith
  have hp : 0 < (ρ / 8) ^ h := pow_pos (by positivity) _
  have hinv : (ρ / 8) ^ h * (8 / ρ) ^ h = 1 := by
    rw [← mul_pow]
    have hρne : ρ ≠ 0 := hρ.ne'
    field_simp
    simp
  nlinarith

noncomputable def sphereNonempty (hh : 0 < h) : Nonempty (Sphere h) := by
  let i : Fin h := ⟨0, hh⟩
  exact ⟨⟨EuclideanSpace.single i 1, by simp⟩⟩

noncomputable def sphereFiniteMeasure : FiniteMeasure (Sphere h) :=
  ⟨(volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere, inferInstance⟩

noncomputable def sphereProbability (hh : 0 < h) : ProbabilityMeasure (Sphere h) :=
  letI : Nonempty (Sphere h) := sphereNonempty h hh
  (sphereFiniteMeasure h).normalize

lemma sphereProbability_le_of_toSphere_le (hh : 0 < h)
    (A : Set (Sphere h)) (c : ℝ) (hc : 0 ≤ c)
    (H : (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere A ≤
      ENNReal.ofReal c *
        (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere Set.univ) :
    (sphereProbability h hh A : ℝ) ≤ c := by
  letI : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
  letI : Nonempty (Sphere h) := sphereNonempty h hh
  let M := sphereFiniteMeasure h
  let P := sphereProbability h hh
  have Hnn : M A ≤ Real.toNNReal c * M Set.univ := by
    rw [← ENNReal.coe_le_coe]
    simp only [ENNReal.coe_mul, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    simpa [M, sphereFiniteMeasure, ENNReal.ofReal] using H
  have hMne : M ≠ 0 := by
    have hμ : (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere ≠ 0 :=
      Measure.toSphere_ne_zero (volume : Measure (EuclideanSpace ℝ (Fin h)))
    intro hzero
    have hcoe := congrArg (fun N : FiniteMeasure (Sphere h) ↦
      (N : Measure (Sphere h))) hzero
    exact hμ (by simpa [M, sphereFiniteMeasure] using hcoe)
  have hmass : 0 < M.mass := pos_iff_ne_zero.mpr (M.mass_nonzero_iff.mpr hMne)
  have hleft : M A = M.mass * M.normalize A := M.self_eq_mass_mul_normalize A
  have huniv : M Set.univ = M.mass := by simp
  rw [hleft, huniv, mul_comm (Real.toNNReal c) M.mass] at Hnn
  have HP : M.normalize A ≤ Real.toNNReal c :=
    (mul_le_mul_iff_right₀ hmass).mp Hnn
  have hP_eq : M.normalize = P := by rfl
  rw [hP_eq] at HP
  have HPReal : ((P A : ℝ≥0) : ℝ) ≤ (Real.toNNReal c : ℝ) := by
    exact_mod_cast HP
  simpa [P, Real.coe_toNNReal c hc] using HPReal

lemma sphereProbability_strip_bound (hh : 1 < h) (x : EuclideanSpace ℝ (Fin h))
    (hx : ‖x‖ = 1) (t : ℝ) (ht : 0 ≤ t) :
    (sphereProbability h (Nat.zero_lt_of_lt hh)
      {y | |inner ℝ x (y : EuclideanSpace ℝ (Fin h))| ≤ t} : ℝ) ≤
        2 * t * Real.sqrt h := by
  have hh0 : 0 < h := Nat.zero_lt_of_lt hh
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh0.ne'
  have hn : 0 < n := by omega
  have H' : (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere
        {y | |inner ℝ x (y : EuclideanSpace ℝ (Fin (n + 1)))| ≤ t} ≤
      ENNReal.ofReal (2 * t * Real.sqrt (n + 1)) *
        (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere Set.univ :=
    Erdos615.BrunnMinkowski.spherical_equatorial_strip_bound hn x hx t ht
  have HB := sphereProbability_le_of_toSphere_le (n + 1) hh0 _
    (2 * t * Real.sqrt ((n : ℝ) + 1))
    (mul_nonneg (mul_nonneg (by positivity) ht) (Real.sqrt_nonneg _)) H'
  simpa [Nat.cast_succ] using HB

lemma sphereProbability_neg_preimage (hh : 0 < h) (A : Set (Sphere h))
    (hA : MeasurableSet A) :
    sphereProbability h hh ((fun y : Sphere h ↦ -y) ⁻¹' A) =
      sphereProbability h hh A := by
  letI : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
  letI : Nonempty (Sphere h) := sphereNonempty h hh
  let M := sphereFiniteMeasure h
  let P := sphereProbability h hh
  let negS : Sphere h → Sphere h := fun y ↦ -y
  let negE : EuclideanSpace ℝ (Fin h) → EuclideanSpace ℝ (Fin h) := fun y ↦ -y
  have hpreMeas : MeasurableSet (negS ⁻¹' A) := hA.preimage measurable_neg
  have hcone : Set.Ioo (0 : ℝ) 1 • ((↑) '' (negS ⁻¹' A)) =
      negE ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' A)) := by
    ext z
    constructor
    · rintro ⟨r, hr, yr, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨r, hr, (-(w : EuclideanSpace ℝ (Fin h))), ⟨-w, hw, rfl⟩, ?_⟩
      simp [negE]
    · rintro ⟨r, hr, yr, ⟨w, hw, rfl⟩, hzw⟩
      refine ⟨r, hr, (-(w : EuclideanSpace ℝ (Fin h))),
        ⟨-w, ?_, rfl⟩, ?_⟩
      · simpa [negS] using hw
      · apply neg_injective
        simpa [negE] using hzw
  have Henn : (M : Measure (Sphere h)) (negS ⁻¹' A) =
      (M : Measure (Sphere h)) A := by
    rw [show (M : Measure (Sphere h)) =
      (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere by rfl]
    rw [Measure.toSphere_apply' volume hpreMeas, Measure.toSphere_apply' volume hA,
      hcone]
    congr 1
    have hvol : MeasurePreserving
        (⇑(MeasurableEquiv.neg (EuclideanSpace ℝ (Fin h)))) volume volume :=
      Measure.measurePreserving_neg _
    exact hvol.measure_preimage_equiv _
  have H : M (negS ⁻¹' A) = M A := by
    exact congrArg ENNReal.toNNReal Henn
  have hMne : M ≠ 0 := by
    have hμ : (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere ≠ 0 :=
      Measure.toSphere_ne_zero (volume : Measure (EuclideanSpace ℝ (Fin h)))
    intro hzero
    have hcoe := congrArg (fun N : FiniteMeasure (Sphere h) ↦
      (N : Measure (Sphere h))) hzero
    exact hμ (by simpa [M, sphereFiniteMeasure] using hcoe)
  have hmass : M.mass ≠ 0 := M.mass_nonzero_iff.mpr hMne
  apply (mul_left_cancel₀ hmass)
  calc
    M.mass * P ((fun y : Sphere h ↦ -y) ⁻¹' A) =
        M ((fun y : Sphere h ↦ -y) ⁻¹' A) :=
      (M.self_eq_mass_mul_normalize _).symm
    _ = M A := H
    _ = M.mass * P A := M.self_eq_mass_mul_normalize A

lemma sphereProbability_positive_inner_bound (hh : 1 < h)
    (x : EuclideanSpace ℝ (Fin h)) (hx : ‖x‖ = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    1 / 2 - 2 * t * Real.sqrt h ≤
      (sphereProbability h (Nat.zero_lt_of_lt hh)
        {y | t < inner ℝ x (y : EuclideanSpace ℝ (Fin h))} : ℝ) := by
  let P := sphereProbability h (Nat.zero_lt_of_lt hh)
  let Pos : Set (Sphere h) :=
    {y | t < inner ℝ x (y : EuclideanSpace ℝ (Fin h))}
  let Neg : Set (Sphere h) :=
    {y | inner ℝ x (y : EuclideanSpace ℝ (Fin h)) < -t}
  let Strip : Set (Sphere h) :=
    {y | |inner ℝ x (y : EuclideanSpace ℝ (Fin h))| ≤ t}
  have hPos : MeasurableSet Pos := by
    dsimp only [Pos]
    measurability
  have hNeg : MeasurableSet Neg := by
    dsimp only [Neg]
    measurability
  have hStrip : MeasurableSet Strip := by
    dsimp only [Strip]
    measurability
  have hpre : (fun y : Sphere h ↦ -y) ⁻¹' Pos = Neg := by
    ext y
    change (t < inner ℝ x (-(y : EuclideanSpace ℝ (Fin h)))) ↔
      inner ℝ x (y : EuclideanSpace ℝ (Fin h)) < -t
    rw [inner_neg_right]
    constructor
    · intro H
      linarith
    · intro H
      linarith
  have hsymm : P Pos = P Neg := by
    rw [← hpre, sphereProbability_neg_preimage h (Nat.zero_lt_of_lt hh) Pos hPos]
  have hcover : (Set.univ : Set (Sphere h)) ⊆ Pos ∪ Neg ∪ Strip := by
    intro y hy
    simp only [Set.mem_union, Set.mem_setOf_eq, Pos, Neg, Strip]
    by_cases hp : t < inner ℝ x (y : EuclideanSpace ℝ (Fin h))
    · exact Or.inl (Or.inl hp)
    by_cases hn : inner ℝ x (y : EuclideanSpace ℝ (Fin h)) < -t
    · exact Or.inl (Or.inr hn)
    · right
      rw [abs_le]
      exact ⟨le_of_not_gt hn, le_of_not_gt hp⟩
  have hprobNN : (1 : ℝ≥0) ≤ P Pos + P Neg + P Strip := by
    calc
      (1 : ℝ≥0) = P Set.univ := by simp
      _ ≤ P (Pos ∪ Neg ∪ Strip) := P.apply_mono hcover
      _ ≤ P (Pos ∪ Neg) + P Strip := P.apply_union_le
      _ ≤ P Pos + P Neg + P Strip := by
        gcongr
        exact P.apply_union_le
  have hprob : (1 : ℝ) ≤ (P Pos : ℝ) + (P Neg : ℝ) + (P Strip : ℝ) := by
    exact_mod_cast hprobNN
  have hstrip : (P Strip : ℝ) ≤ 2 * t * Real.sqrt h := by
    simpa [P, Strip] using sphereProbability_strip_bound h hh x hx t ht
  have hsymmR : (P Pos : ℝ) = (P Neg : ℝ) := by exact_mod_cast hsymm
  simpa [P, Pos] using (by nlinarith : 1 / 2 - 2 * t * Real.sqrt h ≤ (P Pos : ℝ))

lemma dist_lt_sqrt_two_sub_of_inner_gt
    {u v : EuclideanSpace ℝ (Fin h)} {β : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (huv : 2 * β < inner ℝ u v) :
    dist u v < Real.sqrt 2 - β := by
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt1 : 1 ≤ Real.sqrt 2 := by nlinarith
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by nlinarith
  have hprod : Real.sqrt 2 * β ≤ 2 * β :=
    mul_le_mul_of_nonneg_right hsqrt2 hβ0
  have hd : 0 ≤ Real.sqrt 2 - β := by linarith
  have hsq : ‖u - v‖ ^ 2 < (Real.sqrt 2 - β) ^ 2 := by
    rw [norm_sub_sq_real, hu, hv]
    calc
      1 ^ 2 - 2 * inner ℝ u v + 1 ^ 2 < 2 - 4 * β := by nlinarith
      _ ≤ (Real.sqrt 2 - β) ^ 2 := by nlinarith
  have hnorm : ‖u - v‖ < Real.sqrt 2 - β :=
    (sq_lt_sq₀ (norm_nonneg _) hd).mp hsq
  simpa [dist_eq_norm] using hnorm

lemma sphereProbability_near_fixed_bound (hh : 1 < h)
    (x : Sphere h) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    1 / 2 - 4 * β * Real.sqrt h ≤
      (sphereProbability h (Nat.zero_lt_of_lt hh)
        {y : Sphere h | dist x y < Real.sqrt 2 - β} : ℝ) := by
  let P := sphereProbability h (Nat.zero_lt_of_lt hh)
  let Pos : Set (Sphere h) :=
    {y | 2 * β < inner ℝ (x : EuclideanSpace ℝ (Fin h))
      (y : EuclideanSpace ℝ (Fin h))}
  let Near : Set (Sphere h) := {y | dist x y < Real.sqrt 2 - β}
  have hx : ‖(x : EuclideanSpace ℝ (Fin h))‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.property
  have hsub : Pos ⊆ Near := by
    intro y hy
    have hyNorm : ‖(y : EuclideanSpace ℝ (Fin h))‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using y.property
    exact dist_lt_sqrt_two_sub_of_inner_gt (h := h) hx hyNorm hβ0 hβ1 hy
  have hcap := sphereProbability_positive_inner_bound h hh
    (x : EuclideanSpace ℝ (Fin h)) hx (2 * β) (mul_nonneg (by positivity) hβ0)
  have hmonoNN : P Pos ≤ P Near := P.apply_mono hsub
  have hmono : (P Pos : ℝ) ≤ (P Near : ℝ) := by exact_mod_cast hmonoNN
  have H := hcap.trans hmono
  simpa [P, Pos, Near] using (by nlinarith [H] :
    1 / 2 - 4 * β * Real.sqrt h ≤ (P Near : ℝ))

noncomputable def nearPairSet (β : ℝ) : Set (Sphere h × Sphere h) :=
  {z | dist z.1 z.2 < Real.sqrt 2 - β}

lemma nearPairSet_measurable (β : ℝ) : MeasurableSet (nearPairSet h β) := by
  unfold nearPairSet
  measurability

lemma sphereProbability_near_pair_bound (hh : 1 < h)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hsmall : 4 * β * Real.sqrt h ≤ 1 / 2) :
    1 / 2 - 4 * β * Real.sqrt h ≤
      ((sphereProbability h (Nat.zero_lt_of_lt hh)).prod
        (sphereProbability h (Nat.zero_lt_of_lt hh)) (nearPairSet h β) : ℝ) := by
  let P := sphereProbability h (Nat.zero_lt_of_lt hh)
  let q : ℝ := 1 / 2 - 4 * β * Real.sqrt h
  have hq : 0 ≤ q := sub_nonneg.mpr hsmall
  have hcond (x : Sphere h) : ENNReal.ofReal q ≤
      (P : Measure (Sphere h)) ((Prod.mk x) ⁻¹' nearPairSet h β) := by
    have hx := sphereProbability_near_fixed_bound h hh x β hβ0 hβ1
    have Hof := ENNReal.ofReal_le_ofReal hx
    simpa [q, P, nearPairSet, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      using Hof
  have Hprod : ENNReal.ofReal q ≤
      ((P : Measure (Sphere h)).prod (P : Measure (Sphere h))) (nearPairSet h β) := by
    rw [Measure.prod_apply (nearPairSet_measurable h β)]
    calc
      ENNReal.ofReal q = ∫⁻ _ : Sphere h, ENNReal.ofReal q ∂(P : Measure (Sphere h)) := by
        simp
      _ ≤ ∫⁻ x : Sphere h,
          (P : Measure (Sphere h)) ((Prod.mk x) ⁻¹' nearPairSet h β)
          ∂(P : Measure (Sphere h)) := lintegral_mono hcond
  have Hcoe : ENNReal.ofReal q ≤ ((P.prod P (nearPairSet h β) : ℝ≥0) : ℝ≥0∞) := by
    simpa [ProbabilityMeasure.toMeasure_prod,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using Hprod
  exact (ENNReal.ofReal_le_coe.mp Hcoe)

noncomputable def weight (hh : 0 < h) (hρ : 0 < ρ)
    (i : Fin (netCard h ρ hρ)) : ℝ :=
  (sphereProbability h hh (cell h ρ hρ i) : ℝ≥0)

lemma weight_nonneg (hh : 0 < h) (hρ : 0 < ρ)
    (i : Fin (netCard h ρ hρ)) : 0 ≤ weight h ρ hh hρ i := by
  exact NNReal.zero_le_coe

lemma sum_weight (hh : 0 < h) (hρ : 0 < ρ) :
    ∑ i : Fin (netCard h ρ hρ), weight h ρ hh hρ i = 1 := by
  let P := sphereProbability h hh
  have hdis : (Set.univ : Set (Fin (netCard h ρ hρ))).PairwiseDisjoint
      (cell h ρ hρ) := by
    intro i hi j hj hij
    exact cell_pairwiseDisjoint h ρ hρ hij
  have hdis' : (↑(Finset.univ : Finset (Fin (netCard h ρ hρ))) :
      Set (Fin (netCard h ρ hρ))).PairwiseDisjoint (cell h ρ hρ) := by
    intro i hi j hj hij
    exact cell_pairwiseDisjoint h ρ hρ hij
  have heq : (P : Measure (Sphere h)) Set.univ =
      ∑ i : Fin (netCard h ρ hρ), (P : Measure (Sphere h)) (cell h ρ hρ i) := by
    calc
      (P : Measure (Sphere h)) Set.univ =
          (P : Measure (Sphere h))
            (⋃ i : Fin (netCard h ρ hρ), cell h ρ hρ i) := by
        rw [iUnion_cell h ρ hρ]
      _ = ∑ i : Fin (netCard h ρ hρ),
            (P : Measure (Sphere h)) (cell h ρ hρ i) := by
        simpa using (measure_biUnion_finset (s := Finset.univ)
          (f := cell h ρ hρ) hdis'
          (fun i _ ↦ cell_measurable h ρ hρ i))
  have heq' : (1 : ℝ≥0∞) =
      ∑ i : Fin (netCard h ρ hρ),
        ((P (cell h ρ hρ i) : ℝ≥0) : ℝ≥0∞) := by
    simpa [P, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using heq
  have heqNN : (1 : ℝ≥0) =
      ∑ i : Fin (netCard h ρ hρ), P (cell h ρ hρ i) := by
    exact_mod_cast heq'
  have heqReal := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) heqNN.symm
  simpa [weight, P] using heqReal

abbrev GoodIndexPair (hρ : 0 < ρ) (a : ℝ) :=
  {p : Fin (netCard h ρ hρ) × Fin (netCard h ρ hρ) //
    dist (center h ρ hρ p.1) (center h ρ hρ p.2) < Real.sqrt 2 - a}

noncomputable def goodRegion (hρ : 0 < ρ) (a : ℝ) : Set (Sphere h × Sphere h) :=
  ⋃ p : GoodIndexPair h ρ hρ a,
    cell h ρ hρ p.1.1 ×ˢ cell h ρ hρ p.1.2

lemma goodRegion_measurable (hρ : 0 < ρ) (a : ℝ) :
    MeasurableSet (goodRegion h ρ hρ a) := by
  unfold goodRegion
  exact MeasurableSet.iUnion fun p ↦
    (cell_measurable h ρ hρ p.1.1).prod (cell_measurable h ρ hρ p.1.2)

lemma goodRectangles_pairwiseDisjoint (hρ : 0 < ρ) (a : ℝ) :
    Pairwise fun p q : GoodIndexPair h ρ hρ a ↦
      Disjoint (cell h ρ hρ p.1.1 ×ˢ cell h ρ hρ p.1.2)
        (cell h ρ hρ q.1.1 ×ˢ cell h ρ hρ q.1.2) := by
  intro p q hpq
  rw [Set.disjoint_left]
  intro z hzp hzq
  by_cases hi : p.1.1 = q.1.1
  · have hj : p.1.2 ≠ q.1.2 := by
      intro hj
      apply hpq
      apply Subtype.ext
      exact Prod.ext hi hj
    exact (Set.disjoint_left.mp (cell_pairwiseDisjoint h ρ hρ hj)) hzp.2 hzq.2
  · exact (Set.disjoint_left.mp (cell_pairwiseDisjoint h ρ hρ hi)) hzp.1 hzq.1

lemma sum_good_weight_eq_probability (hh : 0 < h) (hρ : 0 < ρ) (a : ℝ) :
    ∑ p : GoodIndexPair h ρ hρ a,
        weight h ρ hh hρ p.1.1 * weight h ρ hh hρ p.1.2 =
      ((sphereProbability h hh).prod (sphereProbability h hh)
        (goodRegion h ρ hρ a) : ℝ) := by
  let P := sphereProbability h hh
  let R : GoodIndexPair h ρ hρ a → Set (Sphere h × Sphere h) :=
    fun p ↦ cell h ρ hρ p.1.1 ×ˢ cell h ρ hρ p.1.2
  have hdis : (↑(Finset.univ : Finset (GoodIndexPair h ρ hρ a)) :
      Set (GoodIndexPair h ρ hρ a)).PairwiseDisjoint R := by
    intro p hp q hq hpq
    exact goodRectangles_pairwiseDisjoint h ρ hρ a hpq
  have heqM : (P.prod P : Measure (Sphere h × Sphere h))
        (goodRegion h ρ hρ a) =
      ∑ p : GoodIndexPair h ρ hρ a,
        (P.prod P : Measure (Sphere h × Sphere h)) (R p) := by
    change (P.prod P : Measure (Sphere h × Sphere h)) (⋃ p, R p) = _
    simpa using (measure_biUnion_finset (μ := (P.prod P : Measure (Sphere h × Sphere h)))
      (s := Finset.univ) (f := R) hdis
      (fun p _ ↦ (cell_measurable h ρ hρ p.1.1).prod
        (cell_measurable h ρ hρ p.1.2)))
  have heqNN : P.prod P (goodRegion h ρ hρ a) =
      ∑ p : GoodIndexPair h ρ hρ a,
        P (cell h ρ hρ p.1.1) * P (cell h ρ hρ p.1.2) := by
    apply ENNReal.coe_injective
    simpa [R, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ProbabilityMeasure.toMeasure_prod, Measure.prod_prod] using heqM
  have heqReal := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) heqNN.symm
  simpa [weight, P] using heqReal

lemma nearPairSet_subset_goodRegion (hρ : 0 < ρ) (a : ℝ) :
    nearPairSet h (a + 2 * ρ) ⊆ goodRegion h ρ hρ a := by
  intro z hz
  have hxall : z.1 ∈ ⋃ i : Fin (netCard h ρ hρ), cell h ρ hρ i := by
    rw [iUnion_cell h ρ hρ]
    trivial
  have hyall : z.2 ∈ ⋃ i : Fin (netCard h ρ hρ), cell h ρ hρ i := by
    rw [iUnion_cell h ρ hρ]
    trivial
  rcases Set.mem_iUnion.mp hxall with ⟨i, hxi⟩
  rcases Set.mem_iUnion.mp hyall with ⟨j, hyj⟩
  have hxic := cell_subset_ball h ρ hρ i hxi
  have hyjc := cell_subset_ball h ρ hρ j hyj
  rw [Metric.mem_closedBall] at hxic hyjc
  have hgood : dist (center h ρ hρ i) (center h ρ hρ j) < Real.sqrt 2 - a := by
    have htri := dist_triangle4 (center h ρ hρ i) z.1 z.2 (center h ρ hρ j)
    have hnear : dist z.1 z.2 < Real.sqrt 2 - (a + 2 * ρ) := hz
    have hix : dist (center h ρ hρ i) z.1 ≤ ρ := by
      simpa [dist_comm] using hxic
    have hyj' : dist z.2 (center h ρ hρ j) ≤ ρ := by
      simpa [dist_comm] using hyjc
    linarith
  let p : GoodIndexPair h ρ hρ a := ⟨(i, j), hgood⟩
  exact Set.mem_iUnion.mpr ⟨p, ⟨hxi, hyj⟩⟩

lemma sum_good_weight_lower (hh : 1 < h) (hρ : 0 < ρ) (a : ℝ)
    (hβ0 : 0 ≤ a + 2 * ρ) (hβ1 : a + 2 * ρ ≤ 1)
    (hsmall : 4 * (a + 2 * ρ) * Real.sqrt h ≤ 1 / 2) :
    1 / 2 - 4 * (a + 2 * ρ) * Real.sqrt h ≤
      ∑ p : GoodIndexPair h ρ hρ a,
        weight h ρ (Nat.zero_lt_of_lt hh) hρ p.1.1 *
          weight h ρ (Nat.zero_lt_of_lt hh) hρ p.1.2 := by
  let P := sphereProbability h (Nat.zero_lt_of_lt hh)
  have hnear := sphereProbability_near_pair_bound h hh (a + 2 * ρ)
    hβ0 hβ1 hsmall
  have hmonoNN : P.prod P (nearPairSet h (a + 2 * ρ)) ≤
      P.prod P (goodRegion h ρ hρ a) :=
    (P.prod P).apply_mono (nearPairSet_subset_goodRegion h ρ hρ a)
  have hmono : (P.prod P (nearPairSet h (a + 2 * ρ)) : ℝ) ≤
      (P.prod P (goodRegion h ρ hρ a) : ℝ) := by exact_mod_cast hmonoNN
  calc
    1 / 2 - 4 * (a + 2 * ρ) * Real.sqrt h ≤
        (P.prod P (goodRegion h ρ hρ a) : ℝ) := hnear.trans hmono
    _ = ∑ p : GoodIndexPair h ρ hρ a,
        weight h ρ (Nat.zero_lt_of_lt hh) hρ p.1.1 *
          weight h ρ (Nat.zero_lt_of_lt hh) hρ p.1.2 := by
      simpa [P] using
        (sum_good_weight_eq_probability h ρ (Nat.zero_lt_of_lt hh) hρ a).symm

noncomputable def multiplicity (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ)
    (i : Fin (netCard h ρ hρ)) : ℕ :=
  ⌊(L : ℝ) * weight h ρ hh hρ i⌋₊ + 1

abbrev CopyVertex (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) :=
  Σ i : Fin (netCard h ρ hρ), Fin (multiplicity h ρ hh hρ L i)

abbrev WeightedGoodCopyPair (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ) :=
  Σ p : GoodIndexPair h ρ hρ a,
    Fin (multiplicity h ρ hh hρ L p.1.1) ×
      Fin (multiplicity h ρ hh hρ L p.1.2)

noncomputable def copyCard (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) : ℕ :=
  Fintype.card (CopyVertex h ρ hh hρ L)

lemma multiplicity_lower (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ)
    (i : Fin (netCard h ρ hρ)) :
    (L : ℝ) * weight h ρ hh hρ i ≤ multiplicity h ρ hh hρ L i := by
  unfold multiplicity
  simpa using (Nat.lt_floor_add_one
    ((L : ℝ) * weight h ρ hh hρ i)).le

lemma multiplicity_upper (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ)
    (i : Fin (netCard h ρ hρ)) :
    (multiplicity h ρ hh hρ L i : ℝ) ≤
      (L : ℝ) * weight h ρ hh hρ i + 1 := by
  unfold multiplicity
  have hf := Nat.floor_le (mul_nonneg (Nat.cast_nonneg L)
    (weight_nonneg h ρ hh hρ i))
  simpa using add_le_add_right hf 1

lemma copyCard_eq_sum (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) :
    copyCard h ρ hh hρ L =
      ∑ i : Fin (netCard h ρ hρ), multiplicity h ρ hh hρ L i := by
  change Fintype.card (Σ i : Fin (netCard h ρ hρ),
    Fin (multiplicity h ρ hh hρ L i)) = _
  rw [Fintype.card_sigma]
  simp

lemma scale_le_copyCard (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) :
    L ≤ copyCard h ρ hh hρ L := by
  have hsum : (L : ℝ) ≤
      ∑ i : Fin (netCard h ρ hρ),
        (multiplicity h ρ hh hρ L i : ℝ) := by
    calc
      (L : ℝ) = ∑ i : Fin (netCard h ρ hρ),
          (L : ℝ) * weight h ρ hh hρ i := by
        rw [← Finset.mul_sum, sum_weight h ρ hh hρ, mul_one]
      _ ≤ ∑ i : Fin (netCard h ρ hρ),
          (multiplicity h ρ hh hρ L i : ℝ) := by
        exact Finset.sum_le_sum fun i _ ↦ multiplicity_lower h ρ hh hρ L i
  rw [copyCard_eq_sum h ρ hh hρ L]
  exact_mod_cast hsum

lemma copyCard_le_scale_add (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) :
    copyCard h ρ hh hρ L ≤ L + netCard h ρ hρ := by
  rw [copyCard_eq_sum h ρ hh hρ L]
  have hsum : (∑ i : Fin (netCard h ρ hρ),
      multiplicity h ρ hh hρ L i : ℝ) ≤
      (L : ℝ) + netCard h ρ hρ := by
    calc
      (∑ i : Fin (netCard h ρ hρ),
          multiplicity h ρ hh hρ L i : ℝ) ≤
          ∑ i : Fin (netCard h ρ hρ),
            ((L : ℝ) * weight h ρ hh hρ i + 1) := by
        exact Finset.sum_le_sum fun i _ ↦ multiplicity_upper h ρ hh hρ L i
      _ = (L : ℝ) + netCard h ρ hρ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          sum_weight h ρ hh hρ, mul_one]
        simp
  exact_mod_cast hsum

lemma weightedGoodCopyPair_card_eq_sum (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) :
    Fintype.card (WeightedGoodCopyPair h ρ hh hρ L a) =
      ∑ p : GoodIndexPair h ρ hρ a,
        multiplicity h ρ hh hρ L p.1.1 * multiplicity h ρ hh hρ L p.1.2 := by
  change Fintype.card (Σ p : GoodIndexPair h ρ hρ a,
    Fin (multiplicity h ρ hh hρ L p.1.1) ×
      Fin (multiplicity h ρ hh hρ L p.1.2)) = _
  rw [Fintype.card_sigma]
  simp

lemma scale_sq_mul_sum_good_weight_le_weightedGoodCopyPair_card
    (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ) :
    (L : ℝ) ^ 2 * (∑ p : GoodIndexPair h ρ hρ a,
      weight h ρ hh hρ p.1.1 * weight h ρ hh hρ p.1.2) ≤
        Fintype.card (WeightedGoodCopyPair h ρ hh hρ L a) := by
  rw [weightedGoodCopyPair_card_eq_sum h ρ hh hρ L a]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hi := multiplicity_lower h ρ hh hρ L p.1.1
  have hj := multiplicity_lower h ρ hh hρ L p.1.2
  calc
    (L : ℝ) ^ 2 *
        (weight h ρ hh hρ p.1.1 * weight h ρ hh hρ p.1.2) =
      ((L : ℝ) * weight h ρ hh hρ p.1.1) *
        ((L : ℝ) * weight h ρ hh hρ p.1.2) := by ring
    _ ≤ (multiplicity h ρ hh hρ L p.1.1 : ℝ) *
        multiplicity h ρ hh hρ L p.1.2 := by
      exact mul_le_mul hi hj
        (mul_nonneg (Nat.cast_nonneg L) (weight_nonneg h ρ hh hρ p.1.2))
        (Nat.cast_nonneg _)

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_lt_one_sub_half_sq_of_unit_of_dist_gt
    {u v : E} {d : ℝ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hd : 0 ≤ d) (huv : d < dist u v) :
    inner ℝ u v < 1 - d ^ 2 / 2 := by
  have hsquare : d ^ 2 < ‖u - v‖ ^ 2 := by
    rw [sq_lt_sq₀ hd (norm_nonneg _)]
    simpa [dist_eq_norm] using huv
  rw [norm_sub_sq_real, hu, hv] at hsquare
  nlinarith

lemma one_sub_half_sq_lt_inner_of_unit_of_dist_lt
    {u v : E} {d : ℝ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hd : 0 ≤ d) (huv : dist u v < d) :
    1 - d ^ 2 / 2 < inner ℝ u v := by
  have hsquare : ‖u - v‖ ^ 2 < d ^ 2 := by
    rw [sq_lt_sq₀ (norm_nonneg _) hd]
    simpa [dist_eq_norm] using huv
  rw [norm_sub_sq_real, hu, hv] at hsquare
  nlinarith

lemma no_unit_far_triangle {u v w : E} {a : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (ha0 : 0 ≤ a) (ha4 : a < 1 / 4)
    (huv : 2 - a < dist u v) (huw : 2 - a < dist u w)
    (hvw : 2 - a < dist v w) : False := by
  have hd : 0 ≤ 2 - a := by linarith
  have huv' := inner_lt_one_sub_half_sq_of_unit_of_dist_gt hu hv hd huv
  have huw' := inner_lt_one_sub_half_sq_of_unit_of_dist_gt hu hw hd huw
  have hvw' := inner_lt_one_sub_half_sq_of_unit_of_dist_gt hv hw hd hvw
  have hnonneg : 0 ≤ inner ℝ (u + v + w) (u + v + w) := real_inner_self_nonneg
  simp only [inner_add_left, inner_add_right, real_inner_comm u v,
    real_inner_comm u w, real_inner_comm v w,
    real_inner_self_eq_norm_sq, hu, hv, hw, one_pow] at hnonneg
  nlinarith

lemma no_unit_far_pair_near_cross {x x' y y' : E} {a : ℝ}
    (hx : ‖x‖ = 1) (hx' : ‖x'‖ = 1) (hy : ‖y‖ = 1) (hy' : ‖y'‖ = 1)
    (ha0 : 0 ≤ a) (ha : a < 2 * (Real.sqrt 2 - 1))
    (hxx : 2 - a < dist x x') (hyy : 2 - a < dist y y')
    (hxy : dist x y < Real.sqrt 2 - a)
    (hxy' : dist x y' < Real.sqrt 2 - a)
    (hx'y : dist x' y < Real.sqrt 2 - a)
    (hx'y' : dist x' y' < Real.sqrt 2 - a) : False := by
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hdFar : 0 ≤ 2 - a := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hdNear : 0 ≤ Real.sqrt 2 - a := by linarith
  have hxx' := inner_lt_one_sub_half_sq_of_unit_of_dist_gt hx hx' hdFar hxx
  have hyy' := inner_lt_one_sub_half_sq_of_unit_of_dist_gt hy hy' hdFar hyy
  have hxyI := one_sub_half_sq_lt_inner_of_unit_of_dist_lt hx hy hdNear hxy
  have hxy'I := one_sub_half_sq_lt_inner_of_unit_of_dist_lt hx hy' hdNear hxy'
  have hx'yI := one_sub_half_sq_lt_inner_of_unit_of_dist_lt hx' hy hdNear hx'y
  have hx'y'I := one_sub_half_sq_lt_inner_of_unit_of_dist_lt hx' hy' hdNear hx'y'
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnonneg : 0 ≤ inner ℝ (x + x' - y - y') (x + x' - y - y') :=
    real_inner_self_nonneg
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_comm x x', real_inner_comm x y, real_inner_comm x y',
    real_inner_comm x' y, real_inner_comm x' y', real_inner_comm y y',
    real_inner_self_eq_norm_sq, hx, hx', hy, hy', one_pow] at hnonneg
  nlinarith

end Geometry

section Graph

lemma four_bool_cases (p₀ p₁ p₂ p₃ : Bool) :
    (p₀ = p₁ ∧ p₀ = p₂) ∨
    (p₀ = p₁ ∧ p₀ = p₃) ∨
    (p₀ = p₂ ∧ p₀ = p₃) ∨
    (p₁ = p₂ ∧ p₁ = p₃) ∨
    (p₀ = p₁ ∧ p₂ = p₃ ∧ p₀ ≠ p₂) ∨
    (p₀ = p₂ ∧ p₁ = p₃ ∧ p₀ ≠ p₁) ∨
    (p₀ = p₃ ∧ p₁ = p₂ ∧ p₀ ≠ p₁) := by
  rcases Bool.eq_false_or_eq_true p₀ with h₀ | h₀ <;>
    rcases Bool.eq_false_or_eq_true p₁ with h₁ | h₁ <;>
    rcases Bool.eq_false_or_eq_true p₂ with h₂ | h₂ <;>
    rcases Bool.eq_false_or_eq_true p₃ with h₃ | h₃ <;> simp_all

noncomputable def position (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ)
    (v : CopyVertex h ρ hh hρ L) : Sphere h :=
  center h ρ hρ v.1

def edgeRel (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ)
    (u v : Bool × CopyVertex h ρ hh hρ L) : Prop :=
  if u.1 = v.1 then
    2 - a < dist (position h ρ hh hρ L u.2) (position h ρ hh hρ L v.2)
  else
    dist (position h ρ hh hρ L u.2) (position h ρ hh hρ L v.2) <
      Real.sqrt 2 - a

lemma edgeRel_comm (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ)
    (u v : Bool × CopyVertex h ρ hh hρ L) :
    edgeRel h ρ hh hρ L a u v ↔ edgeRel h ρ hh hρ L a v u := by
  unfold edgeRel
  rw [dist_comm]
  by_cases huv : u.1 = v.1
  · rw [if_pos huv, if_pos huv.symm]
  · have hvu : v.1 ≠ u.1 := Ne.symm huv
    rw [if_neg huv, if_neg hvu]

noncomputable def BEGraph (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ) :
    SimpleGraph (Bool × CopyVertex h ρ hh hρ L) :=
  SimpleGraph.fromRel (edgeRel h ρ hh hρ L a)

lemma BEGraph_adj_iff (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ)
    (u v : Bool × CopyVertex h ρ hh hρ L) :
    (BEGraph h ρ hh hρ L a).Adj u v ↔
      u ≠ v ∧ edgeRel h ρ hh hρ L a u v := by
  rw [BEGraph, SimpleGraph.fromRel_adj]
  simp only [edgeRel_comm h ρ hh hρ L a v u, or_self]

noncomputable def weightedGoodLeftVertex (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) (q : WeightedGoodCopyPair h ρ hh hρ L a) :
    Bool × CopyVertex h ρ hh hρ L :=
  (false, ⟨q.1.1.1, q.2.1⟩)

noncomputable def weightedGoodRightVertex (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) (q : WeightedGoodCopyPair h ρ hh hρ L a) :
    Bool × CopyVertex h ρ hh hρ L :=
  (true, ⟨q.1.1.2, q.2.2⟩)

lemma weightedGoodEndpoints_injective (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) :
    Function.Injective fun q : WeightedGoodCopyPair h ρ hh hρ L a ↦
      (weightedGoodLeftVertex h ρ hh hρ L a q,
        weightedGoodRightVertex h ρ hh hρ L a q) := by
  intro q r hqr
  grind [weightedGoodLeftVertex, weightedGoodRightVertex]

noncomputable def weightedGoodCopyPairToEdge (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) (q : WeightedGoodCopyPair h ρ hh hρ L a) :
    (BEGraph h ρ hh hρ L a).edgeSet := by
  let u := weightedGoodLeftVertex h ρ hh hρ L a q
  let v := weightedGoodRightVertex h ρ hh hρ L a q
  refine ⟨s(u, v), ?_⟩
  change (BEGraph h ρ hh hρ L a).Adj u v
  rw [BEGraph_adj_iff]
  refine ⟨?_, ?_⟩
  · intro huv
    have := congrArg Prod.fst huv
    simp [u, v, weightedGoodLeftVertex, weightedGoodRightVertex] at this
  · simpa [edgeRel, u, v, weightedGoodLeftVertex, weightedGoodRightVertex,
      position] using q.1.property

lemma weightedGoodCopyPairToEdge_injective (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) :
    Function.Injective (weightedGoodCopyPairToEdge h ρ hh hρ L a) := by
  intro q r hqr
  have hs := congrArg Subtype.val hqr
  change s(weightedGoodLeftVertex h ρ hh hρ L a q,
      weightedGoodRightVertex h ρ hh hρ L a q) =
    s(weightedGoodLeftVertex h ρ hh hρ L a r,
      weightedGoodRightVertex h ρ hh hρ L a r) at hs
  rw [Sym2.eq_iff] at hs
  apply weightedGoodEndpoints_injective h ρ hh hρ L a
  rcases hs with hdir | hswap
  · exact Prod.ext hdir.1 hdir.2
  · exfalso
    have hbool := congrArg Prod.fst hswap.1
    simp [weightedGoodLeftVertex, weightedGoodRightVertex] at hbool

lemma weightedGoodCopyPair_card_le_edges (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) :
    Nat.card (WeightedGoodCopyPair h ρ hh hρ L a) ≤
      Nat.card (BEGraph h ρ hh hρ L a).edgeSet := by
  exact Nat.card_le_card_of_injective
    (weightedGoodCopyPairToEdge h ρ hh hρ L a)
    (weightedGoodCopyPairToEdge_injective h ρ hh hρ L a)

lemma BEGraph_edgeCard_lower (hh : 1 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ)
    (hβ0 : 0 ≤ a + 2 * ρ) (hβ1 : a + 2 * ρ ≤ 1)
    (hsmall : 4 * (a + 2 * ρ) * Real.sqrt h ≤ 1 / 2) :
    (L : ℝ) ^ 2 * (1 / 2 - 4 * (a + 2 * ρ) * Real.sqrt h) ≤
      Nat.card (BEGraph h ρ (Nat.zero_lt_of_lt hh) hρ L a).edgeSet := by
  have hsum := sum_good_weight_lower h ρ hh hρ a hβ0 hβ1 hsmall
  have hround := scale_sq_mul_sum_good_weight_le_weightedGoodCopyPair_card
    h ρ (Nat.zero_lt_of_lt hh) hρ L a
  have hcardNat := weightedGoodCopyPair_card_le_edges
    h ρ (Nat.zero_lt_of_lt hh) hρ L a
  have hcard : (Fintype.card (WeightedGoodCopyPair h ρ
      (Nat.zero_lt_of_lt hh) hρ L a) : ℝ) ≤
      Nat.card (BEGraph h ρ (Nat.zero_lt_of_lt hh) hρ L a).edgeSet := by
    rw [Nat.card_eq_fintype_card] at hcardNat
    exact_mod_cast hcardNat
  calc
    (L : ℝ) ^ 2 * (1 / 2 - 4 * (a + 2 * ρ) * Real.sqrt h) ≤
        (L : ℝ) ^ 2 * (∑ p : GoodIndexPair h ρ hρ a,
          weight h ρ (Nat.zero_lt_of_lt hh) hρ p.1.1 *
            weight h ρ (Nat.zero_lt_of_lt hh) hρ p.1.2) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ ≤ Fintype.card (WeightedGoodCopyPair h ρ
        (Nat.zero_lt_of_lt hh) hρ L a) := hround
    _ ≤ Nat.card (BEGraph h ρ (Nat.zero_lt_of_lt hh) hρ L a).edgeSet := hcard

lemma position_norm (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ)
    (v : CopyVertex h ρ hh hρ L) :
    ‖(position h ρ hh hρ L v : EuclideanSpace ℝ (Fin h))‖ = 1 := by
  simpa [position, Metric.mem_sphere, dist_zero_right] using
    (position h ρ hh hρ L v).property

lemma BEGraph_cliqueFree_four (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ)
    (ha0 : 0 ≤ a) (ha4 : a < 1 / 4)
    (haMix : a < 2 * (Real.sqrt 2 - 1)) :
    (BEGraph h ρ hh hρ L a).CliqueFree 4 := by
  by_contra hfree
  rcases (SimpleGraph.not_cliqueFree_iff_top_isContained 4).mp hfree with ⟨f⟩
  have hadj (i j : Fin 4) (hij : i ≠ j) :
      (BEGraph h ρ hh hρ L a).Adj (f i) (f j) := by
    exact f.topEmbedding.map_adj_iff.mpr ((SimpleGraph.top_adj i j).mpr hij)
  have hvertex_ne (i j : Fin 4) (hij : i ≠ j) : f i ≠ f j :=
    f.injective.ne hij
  have hfar (i j : Fin 4) (hij : i ≠ j) (hpart : (f i).1 = (f j).1) :
      2 - a < dist (position h ρ hh hρ L (f i).2)
        (position h ρ hh hρ L (f j).2) := by
    have H := (BEGraph_adj_iff h ρ hh hρ L a (f i) (f j)).mp (hadj i j hij)
    simpa [edgeRel, hpart] using H.2
  have hnear (i j : Fin 4) (hij : i ≠ j) (hpart : (f i).1 ≠ (f j).1) :
      dist (position h ρ hh hρ L (f i).2)
          (position h ρ hh hρ L (f j).2) < Real.sqrt 2 - a := by
    have H := (BEGraph_adj_iff h ρ hh hρ L a (f i) (f j)).mp (hadj i j hij)
    simpa [edgeRel, hpart] using H.2
  have htri (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hpij : (f i).1 = (f j).1) (hpik : (f i).1 = (f k).1) : False := by
    apply no_unit_far_triangle
      (position_norm h ρ hh hρ L (f i).2)
      (position_norm h ρ hh hρ L (f j).2)
      (position_norm h ρ hh hρ L (f k).2) ha0 ha4
    · exact hfar i j hij hpij
    · exact hfar i k hik hpik
    · exact hfar j k hjk (hpij.symm.trans hpik)
  have hmix (i i' j j' : Fin 4)
      (hii' : i ≠ i') (hjj' : j ≠ j')
      (hij : i ≠ j) (hij' : i ≠ j') (hi'j : i' ≠ j) (hi'j' : i' ≠ j')
      (hpi : (f i).1 = (f i').1) (hpj : (f j).1 = (f j').1)
      (hpij : (f i).1 ≠ (f j).1) : False := by
    apply no_unit_far_pair_near_cross
      (position_norm h ρ hh hρ L (f i).2)
      (position_norm h ρ hh hρ L (f i').2)
      (position_norm h ρ hh hρ L (f j).2)
      (position_norm h ρ hh hρ L (f j').2) ha0 haMix
    · exact hfar i i' hii' hpi
    · exact hfar j j' hjj' hpj
    · exact hnear i j hij hpij
    · exact hnear i j' hij' (fun H ↦ hpij (H.trans hpj.symm))
    · exact hnear i' j hi'j (fun H ↦ hpij (hpi.trans H))
    · exact hnear i' j' hi'j' (fun H ↦ hpij (hpi.trans (H.trans hpj.symm)))
  rcases four_bool_cases (f 0).1 (f 1).1 (f 2).1 (f 3).1 with
    h012 | h013 | h023 | h123 | h01_23 | h02_13 | h03_12
  · exact htri 0 1 2 (by decide) (by decide) (by decide) h012.1 h012.2
  · exact htri 0 1 3 (by decide) (by decide) (by decide) h013.1 h013.2
  · exact htri 0 2 3 (by decide) (by decide) (by decide) h023.1 h023.2
  · exact htri 1 2 3 (by decide) (by decide) (by decide) h123.1 h123.2
  · exact hmix 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) h01_23.1 h01_23.2.1 h01_23.2.2
  · exact hmix 0 2 1 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) h02_13.1 h02_13.2.1 h02_13.2.2
  · exact hmix 0 3 1 2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) h03_12.1 h03_12.2.1 h03_12.2.2

noncomputable def cellUnion (hρ : 0 < ρ)
    (J : Finset (Fin (netCard h ρ hρ))) : Set (Sphere h) :=
  ⋃ i ∈ J, cell h ρ hρ i

lemma cellUnion_measurable (hρ : 0 < ρ)
    (J : Finset (Fin (netCard h ρ hρ))) :
    MeasurableSet (cellUnion h ρ hρ J) := by
  exact Finset.measurableSet_biUnion J fun i _ ↦ cell_measurable h ρ hρ i

lemma sum_weight_finset_eq_probability (hh : 0 < h) (hρ : 0 < ρ)
    (J : Finset (Fin (netCard h ρ hρ))) :
    ∑ i ∈ J, weight h ρ hh hρ i =
      (sphereProbability h hh (cellUnion h ρ hρ J) : ℝ≥0) := by
  let P := sphereProbability h hh
  have hdis : (↑J : Set (Fin (netCard h ρ hρ))).PairwiseDisjoint
      (cell h ρ hρ) := by
    intro i hi j hj hij
    exact cell_pairwiseDisjoint h ρ hρ hij
  have heq : (P : Measure (Sphere h)) (cellUnion h ρ hρ J) =
      ∑ i ∈ J, (P : Measure (Sphere h)) (cell h ρ hρ i) := by
    exact measure_biUnion_finset hdis
      (fun i _ ↦ cell_measurable h ρ hρ i)
  have heq' : ((P (cellUnion h ρ hρ J) : ℝ≥0) : ℝ≥0∞) =
      ∑ i ∈ J, ((P (cell h ρ hρ i) : ℝ≥0) : ℝ≥0∞) := by
    simpa [P, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using heq
  have heqNN : P (cellUnion h ρ hρ J) =
      ∑ i ∈ J, P (cell h ρ hρ i) := by
    exact_mod_cast heq'
  have heqReal := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) heqNN.symm
  simpa [weight, P] using heqReal

lemma sphereProbability_le_isodiametric (hh : 0 < h)
    (A : Set (Sphere h)) (hA : MeasurableSet A) (d : ℝ) (hd1 : 1 ≤ d)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ d) :
    (sphereProbability h hh A : ℝ) ≤ (d / 2) ^ h := by
  letI : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
  letI : Nonempty (Sphere h) := sphereNonempty h hh
  let M := sphereFiniteMeasure h
  let P := sphereProbability h hh
  have hc : 0 ≤ (d / 2) ^ h := pow_nonneg (by linarith) _
  have H := Erdos615.BrunnMinkowski.sphere_isodiametric hh A hA d hd1 hdiam
  have Hnn : M A ≤ Real.toNNReal ((d / 2) ^ h) * M Set.univ := by
    rw [← ENNReal.coe_le_coe]
    simp only [ENNReal.coe_mul, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    simpa [M, sphereFiniteMeasure, ENNReal.ofReal] using H
  have hMne : M ≠ 0 := by
    have hμ : (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere ≠ 0 :=
      Measure.toSphere_ne_zero (volume : Measure (EuclideanSpace ℝ (Fin h)))
    intro hzero
    have hcoe := congrArg (fun N : FiniteMeasure (Sphere h) ↦ (N : Measure (Sphere h))) hzero
    exact hμ (by simpa [M, sphereFiniteMeasure] using hcoe)
  have hmass : 0 < M.mass := pos_iff_ne_zero.mpr (M.mass_nonzero_iff.mpr hMne)
  have hleft : M A = M.mass * M.normalize A := M.self_eq_mass_mul_normalize A
  have huniv : M Set.univ = M.mass := by simp
  rw [hleft, huniv, mul_comm (Real.toNNReal ((d / 2) ^ h)) M.mass] at Hnn
  have HP : M.normalize A ≤ Real.toNNReal ((d / 2) ^ h) :=
    (mul_le_mul_iff_right₀ hmass).mp Hnn
  have hP_eq : M.normalize = P := by
    rfl
  rw [hP_eq] at HP
  have HPReal : ((P A : ℝ≥0) : ℝ) ≤
      (Real.toNNReal ((d / 2) ^ h) : ℝ) := by exact_mod_cast HP
  simpa [P, Real.coe_toNNReal ((d / 2) ^ h) hc] using HPReal

lemma cellUnion_weight_isodiametric (hh : 0 < h) (hρ : 0 < ρ)
    (J : Finset (Fin (netCard h ρ hρ))) (a : ℝ)
    (hd1 : 1 ≤ 2 - a + 2 * ρ)
    (hcenters : ∀ i ∈ J, ∀ j ∈ J,
      dist (center h ρ hρ i) (center h ρ hρ j) ≤ 2 - a) :
    ∑ i ∈ J, weight h ρ hh hρ i ≤ ((2 - a + 2 * ρ) / 2) ^ h := by
  rw [sum_weight_finset_eq_probability h ρ hh hρ J]
  apply sphereProbability_le_isodiametric h hh
    (cellUnion h ρ hρ J) (cellUnion_measurable h ρ hρ J)
    (2 - a + 2 * ρ) hd1
  intro x hx y hy
  simp only [cellUnion, Set.mem_iUnion] at hx hy
  rcases hx with ⟨i, hiJ, hxi⟩
  rcases hy with ⟨j, hjJ, hyj⟩
  have hxc := cell_subset_ball h ρ hρ i hxi
  have hyc := cell_subset_ball h ρ hρ j hyj
  rw [Metric.mem_closedBall] at hxc hyc
  calc
    dist x y ≤ dist x (center h ρ hρ i) +
        dist (center h ρ hρ i) (center h ρ hρ j) +
        dist (center h ρ hρ j) y := by
      linarith [dist_triangle x (center h ρ hρ i) y,
        dist_triangle (center h ρ hρ i) (center h ρ hρ j) y]
    _ ≤ ρ + (2 - a) + ρ := by
      gcongr
      · exact hcenters i hiJ j hjJ
      · simpa [dist_comm] using hyc
    _ = 2 - a + 2 * ρ := by ring

noncomputable def partSet (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ)
    (s : Finset (Bool × CopyVertex h ρ hh hρ L)) (b : Bool) :=
  s.filter fun v ↦ v.1 = b

noncomputable def representedCells (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ)
    (s : Finset (Bool × CopyVertex h ρ hh hρ L)) (b : Bool) :
    Finset (Fin (netCard h ρ hρ)) :=
  (partSet h ρ hh hρ L s b).image fun v ↦ v.2.1

lemma partSet_card_le_sum_multiplicity (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ)
    (s : Finset (Bool × CopyVertex h ρ hh hρ L)) (b : Bool) :
    (partSet h ρ hh hρ L s b).card ≤
      ∑ i ∈ representedCells h ρ hh hρ L s b,
        multiplicity h ρ hh hρ L i := by
  classical
  let S := partSet h ρ hh hρ L s b
  let J := representedCells h ρ hh hρ L s b
  let U := Σ i : {i // i ∈ J}, Fin (multiplicity h ρ hh hρ L i.1)
  let F : S → U := fun v ↦
    ⟨⟨v.1.2.1, by
      apply Finset.mem_image.mpr
      exact ⟨v.1, v.2, rfl⟩⟩, v.1.2.2⟩
  have hF : Function.Injective F := by
    intro u v huv
    apply Subtype.ext
    apply Prod.ext
    · have huPart : u.1.1 = b := (Finset.mem_filter.mp u.2).2
      have hvPart : v.1.1 = b := (Finset.mem_filter.mp v.2).2
      exact huPart.trans hvPart.symm
    · let back : U → CopyVertex h ρ hh hρ L := fun z ↦ ⟨z.1.1, z.2⟩
      exact congrArg back huv
  have hcard := Fintype.card_le_of_injective F hF
  calc
    S.card = Fintype.card S := (Fintype.card_coe S).symm
    _ ≤ Fintype.card U := hcard
    _ = ∑ i : {i // i ∈ J}, multiplicity h ρ hh hρ L i.1 := by
      change Fintype.card (Σ i : {i // i ∈ J},
        Fin (multiplicity h ρ hh hρ L i.1)) = _
      rw [Fintype.card_sigma]
      simp
    _ = ∑ i ∈ J, multiplicity h ρ hh hρ L i := by
      exact (Finset.sum_subtype J (fun _ ↦ Iff.rfl)
        (multiplicity h ρ hh hρ L)).symm

lemma independent_represented_center_dist (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) (ha2 : a ≤ 2)
    (s : Finset (Bool × CopyVertex h ρ hh hρ L))
    (hs : (BEGraph h ρ hh hρ L a).IsIndepSet s) (b : Bool)
    (i : Fin (netCard h ρ hρ)) (hi : i ∈ representedCells h ρ hh hρ L s b)
    (j : Fin (netCard h ρ hρ)) (hj : j ∈ representedCells h ρ hh hρ L s b) :
    dist (center h ρ hρ i) (center h ρ hρ j) ≤ 2 - a := by
  classical
  rcases Finset.mem_image.mp hi with ⟨u, huPart, hui⟩
  rcases Finset.mem_image.mp hj with ⟨v, hvPart, hvj⟩
  have huS : u ∈ s := (Finset.mem_filter.mp huPart).1
  have hvS : v ∈ s := (Finset.mem_filter.mp hvPart).1
  have hub : u.1 = b := (Finset.mem_filter.mp huPart).2
  have hvb : v.1 = b := (Finset.mem_filter.mp hvPart).2
  subst i
  subst j
  by_contra hdist
  have huv : u ≠ v := by
    intro huv
    subst v
    exact hdist (by simp [sub_nonneg.mpr ha2])
  have hadj : (BEGraph h ρ hh hρ L a).Adj u v := by
    rw [BEGraph_adj_iff]
    refine ⟨huv, ?_⟩
    rw [edgeRel, if_pos (hub.trans hvb.symm)]
    simpa [position] using lt_of_not_ge hdist
  exact hs huS hvS huv hadj

lemma partSet_card_bound (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ)
    (ha2 : a ≤ 2) (hd1 : 1 ≤ 2 - a + 2 * ρ)
    (s : Finset (Bool × CopyVertex h ρ hh hρ L))
    (hs : (BEGraph h ρ hh hρ L a).IsIndepSet s) (b : Bool) :
    ((partSet h ρ hh hρ L s b).card : ℝ) ≤
      (L : ℝ) * ((2 - a + 2 * ρ) / 2) ^ h + netCard h ρ hρ := by
  classical
  let J := representedCells h ρ hh hρ L s b
  have hcard := partSet_card_le_sum_multiplicity h ρ hh hρ L s b
  have hmult : (∑ i ∈ J, multiplicity h ρ hh hρ L i : ℝ) ≤
      (L : ℝ) * (∑ i ∈ J, weight h ρ hh hρ i) + J.card := by
    calc
      (∑ i ∈ J, multiplicity h ρ hh hρ L i : ℝ) ≤
          ∑ i ∈ J, ((L : ℝ) * weight h ρ hh hρ i + 1) := by
        exact Finset.sum_le_sum fun i _ ↦ multiplicity_upper h ρ hh hρ L i
      _ = (L : ℝ) * (∑ i ∈ J, weight h ρ hh hρ i) + J.card := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        simp
  have hweight : ∑ i ∈ J, weight h ρ hh hρ i ≤
      ((2 - a + 2 * ρ) / 2) ^ h :=
    cellUnion_weight_isodiametric h ρ hh hρ J a hd1
      (independent_represented_center_dist h ρ hh hρ L a ha2 s hs b)
  have hJcard : J.card ≤ netCard h ρ hρ := by
    simpa using Finset.card_le_univ J
  calc
    ((partSet h ρ hh hρ L s b).card : ℝ) ≤
        (∑ i ∈ J, multiplicity h ρ hh hρ L i : ℕ) := by exact_mod_cast hcard
    _ = ∑ i ∈ J, (multiplicity h ρ hh hρ L i : ℝ) := by norm_cast
    _ ≤ (L : ℝ) * (∑ i ∈ J, weight h ρ hh hρ i) + J.card := hmult
    _ ≤ (L : ℝ) * ((2 - a + 2 * ρ) / 2) ^ h + netCard h ρ hρ := by
      gcongr

lemma independent_finset_card_bound (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ)
    (ha2 : a ≤ 2) (hd1 : 1 ≤ 2 - a + 2 * ρ)
    (s : Finset (Bool × CopyVertex h ρ hh hρ L))
    (hs : (BEGraph h ρ hh hρ L a).IsIndepSet s) :
    (s.card : ℝ) ≤ 2 *
      ((L : ℝ) * ((2 - a + 2 * ρ) / 2) ^ h + netCard h ρ hρ) := by
  have hf := partSet_card_bound h ρ hh hρ L a ha2 hd1 s hs false
  have ht := partSet_card_bound h ρ hh hρ L a ha2 hd1 s hs true
  have hsplit : (partSet h ρ hh hρ L s false).card +
      (partSet h ρ hh hρ L s true).card = s.card := by
    simpa [partSet] using
      (Finset.card_filter_add_card_filter_not (s := s) (fun v ↦ v.1 = false))
  have hsplitR : ((partSet h ρ hh hρ L s false).card : ℝ) +
      (partSet h ρ hh hρ L s true).card = s.card := by exact_mod_cast hsplit
  nlinarith

lemma BEGraph_indepNum_bound (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ)
    (ha2 : a ≤ 2) (hd1 : 1 ≤ 2 - a + 2 * ρ) :
    ((BEGraph h ρ hh hρ L a).indepNum : ℝ) ≤ 2 *
      ((L : ℝ) * ((2 - a + 2 * ρ) / 2) ^ h + netCard h ρ hρ) := by
  rcases (BEGraph h ρ hh hρ L a).exists_isNIndepSet_indepNum with ⟨s, hs⟩
  rw [← hs.card_eq]
  exact independent_finset_card_bound h ρ hh hρ L a ha2 hd1 s hs.isIndepSet

end Graph

end Partition

end Erdos615.Construction

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos615.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 615.
https://www.erdosproblems.com/forum/thread/615

Informal authors:
- Jacob Fox
- Po-Shen Loh
- Yufei Zhao

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos615.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/615.lean
-/

open Filter SimpleGraph Set Real
open scoped Topology BigOperators ENNReal NNReal

namespace Erdos615

attribute [local instance] Classical.propDecidable

open Construction

lemma eventually_asymptotic_numeric_bound :
    ∀ᶠ K : ℕ in atTop,
      200 * (K : ℝ) ^ 19 * Real.exp (-(K : ℝ)) + 200 / (K : ℝ) ^ 3 < 1 := by
  have hExp : Tendsto
      (fun K : ℕ ↦ 200 * (K : ℝ) ^ 19 * Real.exp (-(K : ℝ)))
      atTop (𝓝 0) := by
    have H := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 19).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def, mul_assoc] using H.const_mul 200
  have hInv : Tendsto (fun K : ℕ ↦ 200 / (K : ℝ) ^ 3) atTop (𝓝 0) := by
    have H : Tendsto (fun K : ℕ ↦ ((K : ℝ)⁻¹) ^ 3) atTop (𝓝 0) :=
      by simpa [Function.comp_def] using
        (tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop (R := ℝ))).pow 3
    simpa [div_eq_mul_inv, inv_pow] using H.const_mul 200
  have H := hExp.add hInv
  exact (tendsto_order.1 H).2 1 (by norm_num)

lemma isIndepSet_map_equiv {α β : Type*} (G : SimpleGraph α) (e : α ≃ β)
    {s : Finset α} (hs : G.IsIndepSet s) :
    (G.map e.toEmbedding).IsIndepSet (s.map e.toEmbedding) := by
  rw [SimpleGraph.isIndepSet_iff] at hs ⊢
  intro x hx y hy hxy
  rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
  rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
  have hxy' : x' ≠ y' := fun H ↦ hxy (congrArg e H)
  intro hadj
  exact hs hx' hy' hxy'
    ((SimpleGraph.Embedding.map e.toEmbedding G).map_adj_iff.mp hadj)

lemma indepNum_map_equiv {α β : Type*} [Finite α] [Finite β]
    (G : SimpleGraph α) (e : α ≃ β) :
    (G.map e.toEmbedding).indepNum = G.indepNum := by
  apply le_antisymm
  · rcases (G.map e.toEmbedding).exists_isNIndepSet_indepNum with ⟨s, hs⟩
    have ht := isIndepSet_map_equiv (G.map e.toEmbedding) e.symm hs.isIndepSet
    have hgraph : (G.map e.toEmbedding).map e.symm.toEmbedding = G := by
      ext x y
      simp
    rw [hgraph] at ht
    have hcard := ht.card_le_indepNum
    simpa [hs.card_eq] using hcard
  · rcases G.exists_isNIndepSet_indepNum with ⟨s, hs⟩
    have ht := isIndepSet_map_equiv G e hs.isIndepSet
    have hcard := ht.card_le_indepNum
    simpa [hs.card_eq] using hcard

structure RawCounterexample (c : ℝ) (N : ℕ) where
  Vertex : Type
  fintypeVertex : Fintype Vertex
  graph : SimpleGraph Vertex
  card_pos : 0 < @Fintype.card Vertex fintypeVertex
  card_gt_one : 1 < @Fintype.card Vertex fintypeVertex
  card_lower : N ≤ @Fintype.card Vertex fintypeVertex
  edge_density : (1 / 8 - c) *
    ((@Fintype.card Vertex fintypeVertex : ℕ) : ℝ) ^ 2 ≤ Nat.card graph.edgeSet
  cliqueFree : graph.CliqueFree 4
  indep_log_lt : (graph.indepNum : ℝ) *
    Real.log ((@Fintype.card Vertex fintypeVertex : ℕ) : ℝ) <
      (@Fintype.card Vertex fintypeVertex : ℕ)

lemma exists_raw_counterexample (c : ℝ) (hc : 0 < c) (N : ℕ) :
    Nonempty (RawCounterexample c N) := by
  have hInv : Tendsto (fun K : ℕ ↦ 10 / (K : ℝ)) atTop (𝓝 0) := by
    have H := (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 10
    simpa [Function.comp_def, div_eq_mul_inv] using H
  have hDensity : ∀ᶠ K : ℕ in atTop, 10 / (K : ℝ) < c :=
    (tendsto_order.1 hInv).2 c (by simpa using hc)
  have hLarge : ∀ᶠ K : ℕ in atTop, 10 ≤ K ∧ N ≤ K :=
    (eventually_ge_atTop 10).and (eventually_ge_atTop N)
  obtain ⟨K, ⟨hK10, hNK⟩, hKc, hKasym⟩ :=
    (hLarge.and (hDensity.and eventually_asymptotic_numeric_bound)).exists
  have hKpos : 0 < K := by omega
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hKone : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  let h : ℕ := K ^ 12
  have hh : 1 < h := by
    have Hpow : 2 ^ 12 ≤ K ^ 12 := Nat.pow_le_pow_left (by omega) 12
    norm_num [h] at Hpow ⊢
    omega
  have hh0 : 0 < h := Nat.zero_lt_of_lt hh
  let a : ℝ := 1 / (K : ℝ) ^ 7
  let ρ : ℝ := a / 16
  have ha : 0 < a := by dsimp [a]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hsqrt : Real.sqrt (h : ℝ) = (K : ℝ) ^ 6 := by
    rw [show (h : ℝ) = ((K : ℝ) ^ 6) ^ 2 by
      norm_num [h]
      ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hβ : a + 2 * ρ = 9 / (8 * (K : ℝ) ^ 7) := by
    dsimp [a, ρ]
    field_simp
    ring
  have herror : 4 * (a + 2 * ρ) * Real.sqrt h = 9 / (2 * (K : ℝ)) := by
    rw [hβ, hsqrt]
    field_simp
    ring
  have hβ0 : 0 ≤ a + 2 * ρ := by positivity
  have hβ1 : a + 2 * ρ ≤ 1 := by
    rw [hβ]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * K ^ 7)).2
    have hpowK : (K : ℝ) ≤ K ^ 7 := by
      calc
        (K : ℝ) = K * 1 := by ring
        _ ≤ K * K ^ 6 := mul_le_mul_of_nonneg_left
          (one_le_pow₀ hKone) hKR.le
        _ = K ^ 7 := by ring
    have hK9 : (9 : ℝ) ≤ K := by exact_mod_cast (show 9 ≤ K by omega)
    nlinarith
  have hsmall : 4 * (a + 2 * ρ) * Real.sqrt h ≤ 1 / 2 := by
    rw [herror]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)).2
    nlinarith [show (9 : ℝ) ≤ K by exact_mod_cast (show 9 ≤ K by omega)]
  have ha0 : 0 ≤ a := ha.le
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact (div_le_one (by positivity)).2 (one_le_pow₀ hKone)
  have ha2 : a ≤ 2 := ha1.trans (by norm_num)
  have ha4 : a < 1 / 4 := by
    have hpow : (4 : ℝ) < K ^ 7 := by
      have hK4 : (4 : ℝ) < K := by exact_mod_cast (show 4 < K by omega)
      calc
        (4 : ℝ) < K := hK4
        _ ≤ K ^ 7 := by
          calc
            (K : ℝ) = K * 1 := by ring
            _ ≤ K * K ^ 6 := mul_le_mul_of_nonneg_left
              (one_le_pow₀ hKone) hKR.le
            _ = K ^ 7 := by ring
    dsimp [a]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < K ^ 7)]
    nlinarith
  have haMix : a < 2 * (Real.sqrt 2 - 1) := by
    have hsqrt0 := Real.sqrt_nonneg 2
    have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsqrt54 : (5 : ℝ) / 4 < Real.sqrt 2 := by nlinarith
    have haQuarter := ha4
    nlinarith
  have hd1 : 1 ≤ 2 - a + 2 * ρ := by
    nlinarith [hρ.le]
  have hρ4 : ρ ≤ 4 := by
    have : ρ < 1 := by
      dsimp [ρ]
      nlinarith [ha4]
    linarith
  let B : ℕ := netCard h ρ hρ
  have hBpos : 0 < B := netCard_pos h ρ hh0 hρ
  let L : ℕ := (B + 1) * K ^ 22
  have hLpos : 0 < L := by dsimp [L]; positivity
  let M : ℕ := copyCard h ρ hh0 hρ L
  let V := Bool × CopyVertex h ρ hh0 hρ L
  let G : SimpleGraph V := BEGraph h ρ hh0 hρ L a
  have hMlower : L ≤ M := scale_le_copyCard h ρ hh0 hρ L
  have hMupper : M ≤ L + B := copyCard_le_scale_add h ρ hh0 hρ L
  have hedgeRaw : (L : ℝ) ^ 2 *
      (1 / 2 - 4 * (a + 2 * ρ) * Real.sqrt h) ≤ Nat.card G.edgeSet := by
    simpa [G] using BEGraph_edgeCard_lower h ρ hh hρ L a hβ0 hβ1 hsmall
  have hfreeRaw : G.CliqueFree 4 := by
    simpa [G] using BEGraph_cliqueFree_four h ρ hh0 hρ L a ha0 ha4 haMix
  have hindRaw : (G.indepNum : ℝ) ≤ 2 *
      ((L : ℝ) * ((2 - a + 2 * ρ) / 2) ^ h + B) := by
    simpa [G] using BEGraph_indepNum_bound h ρ hh0 hρ L a ha2 hd1
  have hBbound : (B : ℝ) ≤ (128 * (K : ℝ) ^ 7) ^ h := by
    have H := netCard_le_pow h ρ hh0 hρ hρ4
    have hbase : 8 / ρ = 128 * (K : ℝ) ^ 7 := by
      dsimp [ρ, a]
      field_simp
      ring
    simpa [B, hbase] using H
  have hK22 : (K : ℝ) ≤ K ^ 22 := by
    calc
      (K : ℝ) = K * 1 := by ring
      _ ≤ K * K ^ 21 := mul_le_mul_of_nonneg_left
        (one_le_pow₀ hKone) hKR.le
      _ = K ^ 22 := by ring
  have hBKleL : (B : ℝ) * K ≤ L := by
    calc
      (B : ℝ) * K ≤ B * K ^ 22 :=
        mul_le_mul_of_nonneg_left hK22 (Nat.cast_nonneg B)
      _ ≤ (B + 1) * K ^ 22 := by
        gcongr
        norm_num
      _ = (L : ℕ) := by norm_cast
  have hBdiv : (B : ℝ) ≤ L / K := (le_div_iff₀ hKR).2 hBKleL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hMR : (0 : ℝ) < M := by
    exact_mod_cast (hLpos.trans_le hMlower)
  have hMbound : (M : ℝ) ≤ L * (1 + 1 / K) := by
    have HM : (M : ℝ) ≤ L + B := by exact_mod_cast hMupper
    calc
      (M : ℝ) ≤ L + B := HM
      _ ≤ L + L / K := by gcongr
      _ = L * (1 + 1 / K) := by ring
  have ht0 : (0 : ℝ) ≤ 1 / K := by positivity
  have ht1 : (1 : ℝ) / K ≤ 1 := (div_le_one hKR).2 hKone
  have honePlusSq : (1 + (1 : ℝ) / K) ^ 2 ≤ 1 + 3 / K := by
    have hsq : ((1 : ℝ) / K) ^ 2 ≤ 1 / K := by
      nlinarith only [ht0, ht1]
    calc
      (1 + (1 : ℝ) / K) ^ 2 =
          1 + 2 * ((1 : ℝ) / K) + ((1 : ℝ) / K) ^ 2 := by ring
      _ ≤ 1 + 2 * ((1 : ℝ) / K) + 1 / K := by gcongr
      _ = 1 + 3 / K := by ring
  have hvertexSq : ((2 * M : ℕ) : ℝ) ^ 2 ≤
      4 * (L : ℝ) ^ 2 * (1 + 3 / K) := by
    have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (M : ℝ)) hMbound 2
    calc
      ((2 * M : ℕ) : ℝ) ^ 2 = 4 * (M : ℝ) ^ 2 := by push_cast; ring
      _ ≤ 4 * ((L : ℝ) * (1 + 1 / K)) ^ 2 := by gcongr
      _ = 4 * (L : ℝ) ^ 2 * (1 + 1 / K) ^ 2 := by ring
      _ ≤ 4 * (L : ℝ) ^ 2 * (1 + 3 / K) := by gcongr
  have hedgeRaw' : (L : ℝ) ^ 2 * (1 / 2 - 9 / (2 * K)) ≤
      Nat.card G.edgeSet := by
    simpa [herror] using hedgeRaw
  have hdensityRaw : (1 / 8 - c) * (((2 * M : ℕ) : ℝ) ^ 2) ≤
      Nat.card G.edgeSet := by
    by_cases hc8 : 1 / 8 - c ≤ 0
    · exact (mul_nonpos_of_nonpos_of_nonneg hc8 (sq_nonneg _)).trans
        (Nat.cast_nonneg _)
    · have hc8nonneg : 0 ≤ 1 / 8 - c := le_of_not_ge hc8
      have hct : 10 * ((1 : ℝ) / K) < c := by
        simpa [div_eq_mul_inv, mul_assoc] using hKc
      have hcoeff : 4 * (1 / 8 - c) * (1 + 3 / K) ≤
          1 / 2 - 9 / (2 * K) := by
        have hctnonneg : 0 ≤ c * ((1 : ℝ) / K) := mul_nonneg hc.le ht0
        calc
          4 * (1 / 8 - c) * (1 + 3 / K) =
              1 / 2 + (3 / 2) * (1 / K) - 4 * c -
                12 * (c * (1 / K)) := by ring
          _ ≤ 1 / 2 + (3 / 2) * (1 / K) - 4 * c := by
            nlinarith only [hctnonneg]
          _ ≤ 1 / 2 - (9 / 2) * (1 / K) := by
            nlinarith only [hct, ht0]
          _ = 1 / 2 - 9 / (2 * K) := by field_simp
      calc
        (1 / 8 - c) * (((2 * M : ℕ) : ℝ) ^ 2) ≤
            (1 / 8 - c) * (4 * (L : ℝ) ^ 2 * (1 + 3 / K)) :=
          mul_le_mul_of_nonneg_left hvertexSq hc8nonneg
        _ = (L : ℝ) ^ 2 * (4 * (1 / 8 - c) * (1 + 3 / K)) := by ring
        _ ≤ (L : ℝ) ^ 2 * (1 / 2 - 9 / (2 * K)) :=
          mul_le_mul_of_nonneg_left hcoeff (sq_nonneg _)
        _ ≤ Nat.card G.edgeSet := hedgeRaw'
  let A : ℝ := (128 * (K : ℝ) ^ 7) ^ h
  have hQone : (1 : ℝ) ≤ 128 * K ^ 7 := by
    have : (1 : ℝ) ≤ K ^ 7 := one_le_pow₀ hKone
    nlinarith only [this]
  have hAone : (1 : ℝ) ≤ A := by
    dsimp [A]
    exact one_le_pow₀ hQone
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hAone
  have hB_A : (B : ℝ) ≤ A := hBbound
  have hLupper : (L : ℝ) ≤ 2 * A * K ^ 22 := by
    change (((B + 1) * K ^ 22 : ℕ) : ℝ) ≤ _
    push_cast
    have hB1 : (B : ℝ) + 1 ≤ 2 * A := by
      nlinarith only [hB_A, hAone]
    exact mul_le_mul_of_nonneg_right hB1 (by positivity)
  have hBleL : (B : ℝ) ≤ L := by
    calc
      (B : ℝ) ≤ L / K := hBdiv
      _ ≤ L := div_le_self hLR.le hKone
  have hMtwice : (M : ℝ) ≤ 2 * L := by
    have HM : (M : ℝ) ≤ L + B := by exact_mod_cast hMupper
    nlinarith only [HM, hBleL]
  have hnUpper : (((2 * M : ℕ) : ℝ)) ≤ 8 * A * K ^ 22 := by
    push_cast
    nlinarith only [hMtwice, hLupper]
  have hnPos : (0 : ℝ) < ((2 * M : ℕ) : ℝ) := by
    push_cast
    nlinarith only [hMR]
  have hRhsPos : (0 : ℝ) < 8 * A * K ^ 22 := by positivity
  have hlogMono : Real.log ((2 * M : ℕ) : ℝ) ≤
      Real.log (8 * A * K ^ 22) := Real.log_le_log hnPos hnUpper
  have hlogEq : Real.log (8 * A * K ^ 22) =
      Real.log 8 + (h : ℝ) * Real.log (128 * K ^ 7) +
        22 * Real.log K := by
    rw [Real.log_mul (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) hApos.ne')
      (pow_ne_zero _ hKR.ne'),
      Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hApos.ne',
      show A = (128 * (K : ℝ) ^ 7) ^ h by rfl,
      Real.log_pow, Real.log_pow]
    ring
  have hlog8 : Real.log 8 ≤ 7 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)).trans_eq (by norm_num)
  have hlogQ : Real.log (128 * (K : ℝ) ^ 7) ≤ 128 * K ^ 7 := by
    have H := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 128 * K ^ 7)
    linarith only [H]
  have hlogK : Real.log (K : ℝ) ≤ K := by
    have H := Real.log_le_sub_one_of_pos hKR
    linarith only [H]
  have hhcast : (h : ℝ) = (K : ℝ) ^ 12 := by norm_num [h]
  have htermQ : (h : ℝ) * Real.log (128 * K ^ 7) ≤ 128 * K ^ 19 := by
    calc
      (h : ℝ) * Real.log (128 * K ^ 7) ≤ h * (128 * K ^ 7) :=
        mul_le_mul_of_nonneg_left hlogQ (Nat.cast_nonneg h)
      _ = 128 * K ^ 19 := by rw [hhcast]; ring
  have htermK : 22 * Real.log (K : ℝ) ≤ 22 * K := by
    nlinarith only [hlogK]
  have hK19one : (1 : ℝ) ≤ K ^ 19 := one_le_pow₀ hKone
  have hKleK19 : (K : ℝ) ≤ K ^ 19 := by
    calc
      (K : ℝ) = K * 1 := by ring
      _ ≤ K * K ^ 18 := mul_le_mul_of_nonneg_left
        (one_le_pow₀ hKone) hKR.le
      _ = K ^ 19 := by ring
  have hlogBound : Real.log ((2 * M : ℕ) : ℝ) ≤ 200 * K ^ 19 := by
    rw [hlogEq] at hlogMono
    nlinarith only [hlogMono, hlog8, htermQ, htermK, hK19one, hKleK19]
  have hradiusBase : (2 - a + 2 * ρ) / 2 =
      1 - 7 / (16 * (K : ℝ) ^ 7) := by
    dsimp [a, ρ]
    field_simp
    ring
  let x : ℝ := 7 / (16 * (K : ℝ) ^ 7)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * K ^ 7)).2
    have : (1 : ℝ) ≤ K ^ 7 := one_le_pow₀ hKone
    nlinarith only [this]
  have honeSub : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hbaseExp : 1 - x ≤ Real.exp (-x) := by
    simpa [add_comm] using Real.add_one_le_exp (-x)
  have hpowExp : (1 - x) ^ h ≤ Real.exp (-x) ^ h :=
    pow_le_pow_left₀ honeSub hbaseExp h
  have hexponent : Real.exp (-x) ^ h = Real.exp (-(7 * (K : ℝ) ^ 5 / 16)) := by
    rw [← Real.exp_nat_mul]
    apply congrArg Real.exp
    dsimp [x]
    rw [hhcast]
    field_simp
  have hKexp : (K : ℝ) ≤ 7 * K ^ 5 / 16 := by
    have hK4 : (16 : ℝ) ≤ 7 * K ^ 4 := by
      have hK4ten : (10 : ℝ) ^ 4 ≤ K ^ 4 :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hK10) 4
      norm_num at hK4ten ⊢
      nlinarith only [hK4ten]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2
    have Hmul := mul_le_mul_of_nonneg_left hK4 hKR.le
    nlinarith only [Hmul]
  have halphaExp : ((2 - a + 2 * ρ) / 2) ^ h ≤ Real.exp (-(K : ℝ)) := by
    rw [hradiusBase]
    change (1 - x) ^ h ≤ _
    calc
      (1 - x) ^ h ≤ Real.exp (-x) ^ h := hpowExp
      _ = Real.exp (-(7 * (K : ℝ) ^ 5 / 16)) := hexponent
      _ ≤ Real.exp (-(K : ℝ)) := Real.exp_le_exp.mpr (by linarith only [hKexp])
  have hBK22leL : (B : ℝ) * K ^ 22 ≤ L := by
    change (B : ℝ) * K ^ 22 ≤ (((B + 1) * K ^ 22 : ℕ) : ℝ)
    push_cast
    gcongr
    norm_num
  have hRound : (B : ℝ) / L ≤ 1 / K ^ 22 := by
    rw [div_le_div_iff₀ hLR (by positivity : (0 : ℝ) < K ^ 22)]
    simpa using hBK22leL
  have hlogNonneg : 0 ≤ Real.log ((2 * M : ℕ) : ℝ) :=
    Real.log_natCast_nonneg _
  have hAlphaLog :
      (((2 - a + 2 * ρ) / 2) ^ h + (B : ℝ) / L) *
          Real.log ((2 * M : ℕ) : ℝ) < 1 := by
    have hsumAlpha : ((2 - a + 2 * ρ) / 2) ^ h + (B : ℝ) / L ≤
        Real.exp (-(K : ℝ)) + 1 / K ^ 22 := add_le_add halphaExp hRound
    calc
      (((2 - a + 2 * ρ) / 2) ^ h + (B : ℝ) / L) *
          Real.log ((2 * M : ℕ) : ℝ) ≤
        (Real.exp (-(K : ℝ)) + 1 / K ^ 22) *
          Real.log ((2 * M : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hsumAlpha hlogNonneg
      _ ≤ (Real.exp (-(K : ℝ)) + 1 / K ^ 22) * (200 * K ^ 19) := by
        gcongr
      _ = 200 * K ^ 19 * Real.exp (-(K : ℝ)) + 200 / K ^ 3 := by
        field_simp
      _ < 1 := hKasym
  have hIndLog : (G.indepNum : ℝ) * Real.log ((2 * M : ℕ) : ℝ) < 2 * M := by
    calc
      (G.indepNum : ℝ) * Real.log ((2 * M : ℕ) : ℝ) ≤
          (2 * ((L : ℝ) * ((2 - a + 2 * ρ) / 2) ^ h + B)) *
            Real.log ((2 * M : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hindRaw hlogNonneg
      _ = 2 * L * ((((2 - a + 2 * ρ) / 2) ^ h + (B : ℝ) / L) *
          Real.log ((2 * M : ℕ) : ℝ)) := by
        field_simp
      _ < 2 * L := by
        simpa [mul_assoc] using
          (mul_lt_mul_of_pos_left hAlphaLog
            (mul_pos (by norm_num : (0 : ℝ) < 2) hLR))
      _ ≤ 2 * M := by exact_mod_cast (Nat.mul_le_mul_left 2 hMlower)
  let instV : Fintype V := inferInstance
  have hcard : @Fintype.card V instV = 2 * M := by
    simp [instV, V, M, copyCard]
  have hcardPos : 0 < @Fintype.card V instV := by
    rw [hcard]
    exact Nat.mul_pos (by norm_num) (by exact_mod_cast hMR)
  have hcardOne : 1 < @Fintype.card V instV := by
    rw [hcard]
    have hMpos : 0 < M := by exact_mod_cast hMR
    omega
  have hK22leL : (K : ℝ) ^ 22 ≤ L := by
    change (K : ℝ) ^ 22 ≤ (((B + 1) * K ^ 22 : ℕ) : ℝ)
    push_cast
    have hB1 : (1 : ℝ) ≤ (B : ℝ) + 1 := by norm_num
    calc
      (K : ℝ) ^ 22 = 1 * K ^ 22 := by ring
      _ ≤ ((B : ℝ) + 1) * K ^ 22 :=
        mul_le_mul_of_nonneg_right hB1 (by positivity)
  have hKleLNat : K ≤ L := by exact_mod_cast hK22.trans hK22leL
  have hcardLower : N ≤ @Fintype.card V instV := by
    rw [hcard]
    exact hNK.trans
      (hKleLNat.trans (hMlower.trans (Nat.le_mul_of_pos_left _ (by omega))))
  have hEdge : (1 / 8 - c) * ((@Fintype.card V instV : ℕ) : ℝ) ^ 2 ≤
      Nat.card G.edgeSet := by
    rw [hcard]
    exact hdensityRaw
  have hInd : (G.indepNum : ℝ) *
      Real.log ((@Fintype.card V instV : ℕ) : ℝ) <
        (@Fintype.card V instV : ℕ) := by
    rw [hcard]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hIndLog
  exact ⟨⟨V, instV, G, hcardPos, hcardOne, hcardLower, hEdge, hfreeRaw, hInd⟩⟩

lemma exists_counterexample (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∃ G : SimpleGraph (Fin n),
      (1 / 8 - c) * n ^ 2 ≤ G.edgeFinset.card ∧
      G.CliqueFree 4 ∧ G.indepNum < (n : ℝ) / Real.log n := by
  rcases exists_raw_counterexample c hc N with ⟨W⟩
  letI : Fintype W.Vertex := W.fintypeVertex
  let n : ℕ := Fintype.card W.Vertex
  let e : W.Vertex ≃ Fin n := Fintype.equivFin W.Vertex
  let Gfin : SimpleGraph (Fin n) := W.graph.map e.toEmbedding
  letI : DecidableRel Gfin.Adj := fun _ _ ↦ Classical.propDecidable _
  letI : Nonempty W.Vertex := Fintype.card_pos_iff.mp W.card_pos
  have hedgeEq : Gfin.edgeFinset.card = Nat.card W.graph.edgeSet := by
    calc
      Gfin.edgeFinset.card = W.graph.edgeFinset.card := by
        simpa [Gfin] using
          (SimpleGraph.Iso.map e W.graph).card_edgeFinset_eq.symm
      _ = Fintype.card W.graph.edgeSet := W.graph.edgeFinset_card
      _ = Nat.card W.graph.edgeSet := Nat.card_eq_fintype_card.symm
  have hfreeFin : Gfin.CliqueFree 4 := by
    simpa [Gfin] using
      (SimpleGraph.cliqueFree_map_iff (G := W.graph) (f := e.toEmbedding)).2 W.cliqueFree
  have hindEq : Gfin.indepNum = W.graph.indepNum := by
    simpa [Gfin] using indepNum_map_equiv W.graph e
  have hdensityFin : (1 / 8 - c) * (n : ℝ) ^ 2 ≤ Gfin.edgeFinset.card := by
    rw [hedgeEq]
    exact W.edge_density
  have hnOne : (1 : ℝ) < n := by
    exact_mod_cast (show 1 < n by simpa [n] using W.card_gt_one)
  have hlogPos : 0 < Real.log (n : ℝ) := Real.log_pos hnOne
  have hindFin : (Gfin.indepNum : ℝ) < (n : ℝ) / Real.log n := by
    rw [hindEq]
    exact (lt_div_iff₀ hlogPos).2 W.indep_log_lt
  exact ⟨n, W.card_lower, Gfin, hdensityFin, hfreeFin, hindFin⟩

/-- Erdős Problem 615 has a negative answer, by the quantitative
Bollobás--Erdős construction. -/
theorem not_erdos_615 :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ᶠ (n : ℕ) in atTop,
      ∀ G : SimpleGraph (Fin n), (1 / 8 - c) * n ^ 2 ≤ G.edgeFinset.card →
        ¬ G.CliqueFree 4 ∨ (n : ℝ) / Real.log n ≤ G.indepNum := by
  rintro ⟨c, hc, hlarge⟩
  rcases eventually_atTop.1 hlarge with ⟨N, hN⟩
  obtain ⟨n, hn, G, hedges, hfree, hind⟩ := exists_counterexample c hc N
  rcases hN n hn G hedges with hnotfree | hlargeindep
  · exact hnotfree hfree
  · exact (not_le_of_gt hind) hlargeindep


end Erdos615

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos22.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 22.
https://www.erdosproblems.com/forum/thread/22

Informal authors:
- Jacob Fox
- Po-Shen Loh
- Yufei Zhao

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos22.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/22.lean
-/

open Filter SimpleGraph Set Real
open scoped Topology BigOperators ENNReal NNReal



attribute [local instance] Classical.propDecidable

open Erdos615.Construction

/-! ## Two finite graph operations -/

/-- Add an independent set of `t` vertices and join it completely to the
`true` Boolean part of `G`. -/
def oneSidedExtension {W : Type*} (G : SimpleGraph (Bool × W)) (t : ℕ) :
    SimpleGraph ((Bool × W) ⊕ Fin t) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inl u, .inr _ => u.1 = true
    | .inr _, .inl v => v.1 = true
    | .inr _, .inr _ => False
  symm.symm
    | .inl _, .inl _ => G.adj_symm
    | .inl _, .inr _ | .inr _, .inl _ => id
    | .inr _, .inr _ => id
  loopless.irrefl
    | .inl u => G.loopless.irrefl u
    | .inr _ => id

@[simp] lemma oneSidedExtension_adj_inl_inl {W : Type*}
    (G : SimpleGraph (Bool × W)) (t : ℕ) (u v : Bool × W) :
    (oneSidedExtension G t).Adj (.inl u) (.inl v) ↔ G.Adj u v := Iff.rfl

@[simp] lemma oneSidedExtension_adj_inl_inr {W : Type*}
    (G : SimpleGraph (Bool × W)) (t : ℕ) (u : Bool × W) (v : Fin t) :
    (oneSidedExtension G t).Adj (.inl u) (.inr v) ↔ u.1 = true := Iff.rfl

@[simp] lemma oneSidedExtension_adj_inr_inl {W : Type*}
    (G : SimpleGraph (Bool × W)) (t : ℕ) (u : Fin t) (v : Bool × W) :
    (oneSidedExtension G t).Adj (.inr u) (.inl v) ↔ v.1 = true := Iff.rfl

@[simp] lemma oneSidedExtension_not_adj_inr_inr {W : Type*}
    (G : SimpleGraph (Bool × W)) (t : ℕ) (u v : Fin t) :
    ¬(oneSidedExtension G t).Adj (.inr u) (.inr v) := id

/-- A uniform independent-fibre blowup. -/
def uniformBlowup {V : Type*} (G : SimpleGraph V) (q : ℕ) :
    SimpleGraph (V × Fin q) where
  Adj u v := G.Adj u.1 v.1
  symm.symm _ _ := G.adj_symm
  loopless.irrefl u := G.loopless.irrefl u.1

@[simp] lemma uniformBlowup_adj {V : Type*} (G : SimpleGraph V) (q : ℕ)
    (u v : V × Fin q) :
    (uniformBlowup G q).Adj u v ↔ G.Adj u.1 v.1 := Iff.rfl

/-- Add `r` isolated vertices to a uniform blowup. -/
abbrev paddedBlowup {V : Type*} (G : SimpleGraph V) (q r : ℕ) :
    SimpleGraph ((V × Fin q) ⊕ Fin r) := uniformBlowup G q ⊕g ⊥

/-! ## Clique-freeness of the one-sided extension -/

lemma BEGraph_no_samePart_triangle {h : ℕ} {ρ : ℝ} (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) (ha0 : 0 ≤ a) (ha4 : a < 1 / 4) (b : Bool)
    (u v w : CopyVertex h ρ hh hρ L)
    (huv : (BEGraph h ρ hh hρ L a).Adj (b, u) (b, v))
    (huw : (BEGraph h ρ hh hρ L a).Adj (b, u) (b, w))
    (hvw : (BEGraph h ρ hh hρ L a).Adj (b, v) (b, w)) : False := by
  have hfar (x y : CopyVertex h ρ hh hρ L)
      (hxy : (BEGraph h ρ hh hρ L a).Adj (b, x) (b, y)) :
      2 - a < dist (position h ρ hh hρ L x) (position h ρ hh hρ L y) := by
    have H := (BEGraph_adj_iff h ρ hh hρ L a (b, x) (b, y)).mp hxy
    simpa [edgeRel] using H.2
  exact no_unit_far_triangle
    (position_norm h ρ hh hρ L u)
    (position_norm h ρ hh hρ L v)
    (position_norm h ρ hh hρ L w) ha0 ha4
    (hfar u v huv) (hfar u w huw) (hfar v w hvw)

lemma oneSidedExtension_cliqueFree_four {W : Type*} [Nonempty W]
    (G : SimpleGraph (Bool × W)) (t : ℕ)
    (hG : G.CliqueFree 4)
    (htri : ∀ u v w : W,
      G.Adj (true, u) (true, v) →
      G.Adj (true, u) (true, w) →
      G.Adj (true, v) (true, w) → False) :
    (oneSidedExtension G t).CliqueFree 4 := by
  by_contra hfree
  rcases (SimpleGraph.not_cliqueFree_iff_top_isContained 4).mp hfree with ⟨f⟩
  have hadj (i j : Fin 4) (hij : i ≠ j) :
      (oneSidedExtension G t).Adj (f i) (f j) :=
    f.topEmbedding.map_adj_iff.mpr ((SimpleGraph.top_adj i j).mpr hij)
  by_cases hnew : ∃ i u, f i = .inr u
  · rcases hnew with ⟨i, u, hi⟩
    have hold (j : Fin 4) (hji : j ≠ i) : ∃ w : W, f j = .inl (true, w) := by
      cases hj : f j with
      | inl x =>
          have hx : x.1 = true := by
            have H := hadj j i hji
            simpa [hj, hi] using H
          rcases x with ⟨b, w⟩
          cases b <;> simp_all
      | inr v =>
          exfalso
          have H := hadj j i hji
          simpa [hj, hi] using H
    fin_cases i
    · rcases hold 1 (by decide) with ⟨v, hv⟩
      rcases hold 2 (by decide) with ⟨w, hw⟩
      rcases hold 3 (by decide) with ⟨x, hx⟩
      exact htri v w x
        (by simpa [hv, hw] using hadj 1 2 (by decide))
        (by simpa [hv, hx] using hadj 1 3 (by decide))
        (by simpa [hw, hx] using hadj 2 3 (by decide))
    · rcases hold 0 (by decide) with ⟨v, hv⟩
      rcases hold 2 (by decide) with ⟨w, hw⟩
      rcases hold 3 (by decide) with ⟨x, hx⟩
      exact htri v w x
        (by simpa [hv, hw] using hadj 0 2 (by decide))
        (by simpa [hv, hx] using hadj 0 3 (by decide))
        (by simpa [hw, hx] using hadj 2 3 (by decide))
    · rcases hold 0 (by decide) with ⟨v, hv⟩
      rcases hold 1 (by decide) with ⟨w, hw⟩
      rcases hold 3 (by decide) with ⟨x, hx⟩
      exact htri v w x
        (by simpa [hv, hw] using hadj 0 1 (by decide))
        (by simpa [hv, hx] using hadj 0 3 (by decide))
        (by simpa [hw, hx] using hadj 1 3 (by decide))
    · rcases hold 0 (by decide) with ⟨v, hv⟩
      rcases hold 1 (by decide) with ⟨w, hw⟩
      rcases hold 2 (by decide) with ⟨x, hx⟩
      exact htri v w x
        (by simpa [hv, hw] using hadj 0 1 (by decide))
        (by simpa [hv, hx] using hadj 0 2 (by decide))
        (by simpa [hw, hx] using hadj 1 2 (by decide))
  · have hold (i : Fin 4) : ∃ x : Bool × W, f i = .inl x := by
      cases hi : f i with
      | inl x => exact ⟨x, rfl⟩
      | inr u => exact False.elim (hnew ⟨i, u, hi⟩)
    choose g hg using hold
    have hginj : Function.Injective g := by
      intro i j hij
      apply f.injective
      simpa [hg i, hg j, hij]
    let e : (⊤ : SimpleGraph (Fin 4)) ↪g G :=
      { toFun := g
        inj' := hginj
        map_rel_iff' := by
          intro i j
          constructor
          · intro H
            exact (SimpleGraph.top_adj i j).mpr
              (fun hij ↦ G.loopless.irrefl (g i) (hij ▸ H))
          · intro hij
            have H := hadj i j ((SimpleGraph.top_adj i j).mp hij)
            simpa [hg i, hg j] using H }
    exact e.isContained.not_cliqueFree hG

/-! ## Independence-number bounds -/

private noncomputable def leftPart {A B : Type*} [Fintype A]
    (s : Finset (A ⊕ B)) : Finset A :=
  Finset.univ.filter fun a ↦ Sum.inl a ∈ s

private lemma card_le_leftPart_add {A B : Type*} [Fintype A] [Fintype B]
    (s : Finset (A ⊕ B)) :
    s.card ≤ (leftPart s).card + Fintype.card B := by
  classical
  let f : s → (leftPart s) ⊕ B
    | ⟨.inl a, ha⟩ => .inl ⟨a, by simp [leftPart, ha]⟩
    | ⟨.inr b, _⟩ => .inr b
  have hf : Function.Injective f := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    rcases x with a | b <;> rcases y with a' | b' <;>
      simp [f] at hxy ⊢
    · exact congrArg Subtype.val hxy
    · exact hxy
  have H := Fintype.card_le_of_injective f hf
  simpa using H

private lemma leftPart_independent {A B : Type*} [Fintype A]
    (H : SimpleGraph (A ⊕ B)) (G : SimpleGraph A)
    (hleft : ∀ a b, H.Adj (.inl a) (.inl b) ↔ G.Adj a b)
    (s : Finset (A ⊕ B)) (hs : H.IsIndepSet s) :
    G.IsIndepSet (leftPart s) := by
  classical
  rw [SimpleGraph.isIndepSet_iff] at hs ⊢
  intro a ha b hb hab hadj
  have ha' : Sum.inl a ∈ s := (Finset.mem_filter.mp ha).2
  have hb' : Sum.inl b ∈ s := (Finset.mem_filter.mp hb).2
  exact hs ha' hb' (by simpa using hab) ((hleft a b).mpr hadj)

lemma indepNum_le_left_add {A B : Type*} [Fintype A] [Fintype B]
    (H : SimpleGraph (A ⊕ B)) (G : SimpleGraph A)
    (hleft : ∀ a b, H.Adj (.inl a) (.inl b) ↔ G.Adj a b) :
    H.indepNum ≤ G.indepNum + Fintype.card B := by
  classical
  rcases H.exists_isNIndepSet_indepNum with ⟨s, hs⟩
  rw [← hs.card_eq]
  calc
    s.card ≤ (leftPart s).card + Fintype.card B := card_le_leftPart_add s
    _ ≤ G.indepNum + Fintype.card B :=
      Nat.add_le_add_right (leftPart_independent H G hleft s hs.isIndepSet).card_le_indepNum _

lemma oneSidedExtension_indepNum_le {W : Type*} [Fintype W]
    (G : SimpleGraph (Bool × W)) (t : ℕ) :
    (oneSidedExtension G t).indepNum ≤ G.indepNum + t := by
  simpa using indepNum_le_left_add (oneSidedExtension G t) G
    (fun _ _ ↦ oneSidedExtension_adj_inl_inl G t _ _)

lemma uniformBlowup_indepNum_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (q : ℕ) :
    (uniformBlowup G q).indepNum ≤ q * G.indepNum := by
  classical
  rcases (uniformBlowup G q).exists_isNIndepSet_indepNum with ⟨s, hs⟩
  have himage : G.IsIndepSet (s.image Prod.fst) := by
    have hs' := hs.isIndepSet
    rw [SimpleGraph.isIndepSet_iff] at hs' ⊢
    intro a ha b hb hab hadj
    rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨y, hy, hfy⟩
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hab hfy
    exact hs' hx hy hxy (by simpa [hfy] using hadj)
  have hfiber (b : V) (hb : b ∈ s.image Prod.fst) :
      {a ∈ s | a.1 = b}.card ≤ q := by
    have H := Finset.card_le_card_of_injOn (fun a : V × Fin q ↦ a.2)
      (s := {a ∈ s | a.1 = b}) (t := Finset.univ)
      (fun _ _ ↦ Finset.mem_univ _)
      (by
        intro x hx y hy hsecond
        have hxfirst := (Finset.mem_filter.mp hx).2
        have hyfirst := (Finset.mem_filter.mp hy).2
        exact Prod.ext (hxfirst.trans hyfirst.symm) hsecond)
    simpa using H
  rw [← hs.card_eq]
  calc
    s.card ≤ q * (s.image Prod.fst).card :=
      Finset.card_le_mul_card_image s q hfiber
    _ ≤ q * G.indepNum := Nat.mul_le_mul_left q himage.card_le_indepNum

lemma paddedBlowup_indepNum_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (q r : ℕ) :
    (paddedBlowup G q r).indepNum ≤ q * G.indepNum + r := by
  calc
    (paddedBlowup G q r).indepNum ≤ (uniformBlowup G q).indepNum + r := by
      simpa [paddedBlowup] using indepNum_le_left_add
        (uniformBlowup G q ⊕g (⊥ : SimpleGraph (Fin r))) (uniformBlowup G q)
        (fun _ _ ↦ SimpleGraph.sum_adj_inl)
    _ ≤ q * G.indepNum + r :=
      Nat.add_le_add_right (uniformBlowup_indepNum_le G q) r

/-! ## Clique-freeness and edge counts of blowups -/

lemma uniformBlowup_cliqueFree_four {V : Type*} (G : SimpleGraph V) (q : ℕ)
    (hG : G.CliqueFree 4) : (uniformBlowup G q).CliqueFree 4 := by
  by_contra hfree
  rcases (SimpleGraph.not_cliqueFree_iff_top_isContained 4).mp hfree with ⟨f⟩
  have hadj (i j : Fin 4) (hij : i ≠ j) :
      (uniformBlowup G q).Adj (f i) (f j) :=
    f.topEmbedding.map_adj_iff.mpr ((SimpleGraph.top_adj i j).mpr hij)
  have hproj : Function.Injective (fun i : Fin 4 ↦ (f i).1) := by
    intro i j hij
    by_contra hne
    have H := hadj i j hne
    exact G.loopless.irrefl (f i).1 (by simpa [hij] using H)
  let e : (⊤ : SimpleGraph (Fin 4)) ↪g G :=
    { toFun := fun i ↦ (f i).1
      inj' := hproj
      map_rel_iff' := by
        intro i j
        constructor
        · intro H
          exact (SimpleGraph.top_adj i j).mpr
            (fun hij ↦ G.loopless.irrefl (f i).1 (hij ▸ H))
        · intro hij
          exact hadj i j ((SimpleGraph.top_adj i j).mp hij) }
  exact e.isContained.not_cliqueFree hG

lemma sum_cliqueFree_four {A B : Type*} (G : SimpleGraph A) (H : SimpleGraph B)
    (hG : G.CliqueFree 4) (hH : H.CliqueFree 4) : (G ⊕g H).CliqueFree 4 := by
  by_contra hfree
  rcases (SimpleGraph.not_cliqueFree_iff_top_isContained 4).mp hfree with ⟨f⟩
  have hadj (i j : Fin 4) (hij : i ≠ j) : (G ⊕g H).Adj (f i) (f j) :=
    f.topEmbedding.map_adj_iff.mpr ((SimpleGraph.top_adj i j).mpr hij)
  rcases h0 : f 0 with a | b
  · have hall (i : Fin 4) : ∃ a : A, f i = .inl a := by
      by_cases hi : i = 0
      · subst i; exact ⟨a, h0⟩
      · cases hfi : f i with
        | inl x => exact ⟨x, rfl⟩
        | inr y => exfalso; simpa [h0, hfi] using hadj 0 i (Ne.symm hi)
    choose g hg using hall
    have hginj : Function.Injective g := by
      intro i j hij
      apply f.injective
      simpa [hg i, hg j, hij]
    let e : (⊤ : SimpleGraph (Fin 4)) ↪g G :=
      { toFun := g
        inj' := hginj
        map_rel_iff' := by
          intro i j
          constructor
          · intro had
            exact (SimpleGraph.top_adj i j).mpr
              (fun hij ↦ G.loopless.irrefl (g i) (hij ▸ had))
          · intro hij
            simpa [hg i, hg j] using hadj i j ((SimpleGraph.top_adj i j).mp hij) }
    exact e.isContained.not_cliqueFree hG
  · have hall (i : Fin 4) : ∃ b : B, f i = .inr b := by
      by_cases hi : i = 0
      · subst i; exact ⟨b, h0⟩
      · cases hfi : f i with
        | inl x => exfalso; simpa [h0, hfi] using hadj 0 i (Ne.symm hi)
        | inr y => exact ⟨y, rfl⟩
    choose g hg using hall
    have hginj : Function.Injective g := by
      intro i j hij
      apply f.injective
      simpa [hg i, hg j, hij]
    let e : (⊤ : SimpleGraph (Fin 4)) ↪g H :=
      { toFun := g
        inj' := hginj
        map_rel_iff' := by
          intro i j
          constructor
          · intro had
            exact (SimpleGraph.top_adj i j).mpr
              (fun hij ↦ H.loopless.irrefl (g i) (hij ▸ had))
          · intro hij
            simpa [hg i, hg j] using hadj i j ((SimpleGraph.top_adj i j).mp hij) }
    exact e.isContained.not_cliqueFree hH

lemma bot_cliqueFree_four {V : Type*} : (⊥ : SimpleGraph V).CliqueFree 4 := by
  intro s hs
  have hcard := hs.card_eq
  have hle : s.card ≤ 1 := by
    by_contra h
    have htwo : 2 ≤ s.card := by omega
    rcases Finset.one_lt_card.mp (by omega : 1 < s.card) with ⟨x, hx, y, hy, hxy⟩
    simpa using hs.isClique hx hy hxy
  omega

lemma paddedBlowup_cliqueFree_four {V : Type*} (G : SimpleGraph V) (q r : ℕ)
    (hG : G.CliqueFree 4) : (paddedBlowup G q r).CliqueFree 4 :=
  sum_cliqueFree_four _ _ (uniformBlowup_cliqueFree_four G q hG) bot_cliqueFree_four

private def uniformBlowupDartEquiv {V : Type*} (G : SimpleGraph V) (q : ℕ) :
    (uniformBlowup G q).Dart ≃ G.Dart × (Fin q × Fin q) where
  toFun d := (⟨(d.fst.1, d.snd.1), d.adj⟩, (d.fst.2, d.snd.2))
  invFun d := ⟨((d.1.fst, d.2.1), (d.1.snd, d.2.2)), d.1.adj⟩
  left_inv := by rintro ⟨⟨⟨v, i⟩, ⟨w, j⟩⟩, h⟩; rfl
  right_inv := by rintro ⟨⟨⟨v, w⟩, h⟩, ⟨i, j⟩⟩; rfl

lemma uniformBlowup_edgeCard {V : Type*} [Fintype V]
    (G : SimpleGraph V) (q : ℕ) :
    Nat.card (uniformBlowup G q).edgeSet = q ^ 2 * Nat.card G.edgeSet := by
  classical
  have hc := Fintype.card_congr (uniformBlowupDartEquiv G q)
  have hblow := (uniformBlowup G q).dart_card_eq_twice_card_edges
  have hbase := G.dart_card_eq_twice_card_edges
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  rw [hblow, hbase, (uniformBlowup G q).edgeFinset_card, G.edgeFinset_card,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hc
  apply Nat.mul_left_cancel (n := 2)
  · norm_num
  · calc
      2 * Nat.card (uniformBlowup G q).edgeSet =
          2 * Nat.card G.edgeSet * (q * q) := hc
      _ = 2 * (q ^ 2 * Nat.card G.edgeSet) := by rw [pow_two]; ac_rfl

lemma paddedBlowup_edgeCard {V : Type*} [Fintype V]
    (G : SimpleGraph V) (q r : ℕ) :
    Nat.card (paddedBlowup G q r).edgeSet = q ^ 2 * Nat.card G.edgeSet := by
  classical
  calc
    Nat.card (paddedBlowup G q r).edgeSet =
        Nat.card (uniformBlowup G q).edgeSet +
          Nat.card (⊥ : SimpleGraph (Fin r)).edgeSet := by
      rw [Nat.card_congr (SimpleGraph.edgeSetSumEquiv
        (G := uniformBlowup G q) (H := (⊥ : SimpleGraph (Fin r)))), Nat.card_sum]
    _ = Nat.card (uniformBlowup G q).edgeSet := by simp
    _ = q ^ 2 * Nat.card G.edgeSet := uniformBlowup_edgeCard G q

private lemma sym2_map_inl_ne_cross {A B : Type*} (e : Sym2 A) (a : A) (b : B) :
    Sym2.map Sum.inl e ≠ s(Sum.inr b, Sum.inl a) := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [Sym2.map_pair_eq]
      intro H
      rw [Sym2.eq_iff] at H
      simp at H

lemma oneSidedExtension_edgeCard_lower {W : Type*} [Fintype W]
    (G : SimpleGraph (Bool × W)) (t : ℕ) :
    Nat.card G.edgeSet + t * Fintype.card W ≤
      Nat.card (oneSidedExtension G t).edgeSet := by
  classical
  let eOld : G ↪g oneSidedExtension G t :=
    { toFun := Sum.inl
      inj' := Sum.inl_injective
      map_rel_iff' := by simp }
  let F : G.edgeSet ⊕ (Fin t × W) → (oneSidedExtension G t).edgeSet
    | .inl e => eOld.mapEdgeSet e
    | .inr p => ⟨s(.inr p.1, .inl (true, p.2)), by simp⟩
  have hF : Function.Injective F := by
    rintro (e | p) (e' | p') heq
    · change eOld.mapEdgeSet e = eOld.mapEdgeSet e' at heq
      congr 1
      exact eOld.mapEdgeSet.injective heq
    · exfalso
      have H := congrArg Subtype.val heq
      simp only [F, SimpleGraph.Embedding.mapEdgeSet_apply] at H
      dsimp [SimpleGraph.Hom.mapEdgeSet, eOld] at H
      exact sym2_map_inl_ne_cross e.1 (true, p'.2) p'.1 H
    · exfalso
      have H := congrArg Subtype.val heq
      simp only [F, SimpleGraph.Embedding.mapEdgeSet_apply] at H
      dsimp [SimpleGraph.Hom.mapEdgeSet, eOld] at H
      exact sym2_map_inl_ne_cross e'.1 (true, p.2) p.1 H.symm
    · congr 1
      have H := congrArg Subtype.val heq
      change s(Sum.inr p.1, Sum.inl (true, p.2)) =
        s(Sum.inr p'.1, Sum.inl (true, p'.2)) at H
      rw [Sym2.eq_iff] at H
      simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq,
        Sum.inr.injEq, Sum.inr_ne_inl, false_and, Sum.inl_ne_inr, or_false] at H
      exact Prod.ext H.1 H.2.2
  have H := Nat.card_le_card_of_injective F hF
  simpa [Nat.card_sum, Nat.card_prod, Nat.card_fin] using H

/-! ## A strict-density seed from the finite Bollobás--Erdős graph -/

structure StrictSeed (ε : ℝ) where
  Vertex : Type
  fintypeVertex : Fintype Vertex
  graph : SimpleGraph Vertex
  card_pos : 0 < @Fintype.card Vertex fintypeVertex
  cliqueFree : graph.CliqueFree 4
  indep_small : 4 * (graph.indepNum : ℝ) <
    ε * (@Fintype.card Vertex fintypeVertex : ℕ)
  edge_strict : (@Fintype.card Vertex fintypeVertex) ^ 2 <
    8 * Nat.card graph.edgeSet

lemma eventually_seed_error_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop,
      Real.exp (-(K : ℝ)) + 1 / (K : ℝ) ^ 22 + 50 / (K : ℝ) < ε / 4 := by
  have hExp : Tendsto (fun K : ℕ ↦ Real.exp (-(K : ℝ))) atTop (𝓝 0) := by
    have H := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def] using H
  have hInv22 : Tendsto (fun K : ℕ ↦ 1 / (K : ℝ) ^ 22) atTop (𝓝 0) := by
    have H : Tendsto (fun K : ℕ ↦ ((K : ℝ)⁻¹) ^ 22) atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        (tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop (R := ℝ))).pow 22
    simpa [div_eq_mul_inv, inv_pow] using H
  have hInv : Tendsto (fun K : ℕ ↦ 50 / (K : ℝ)) atTop (𝓝 0) := by
    have H := (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 50
    simpa [Function.comp_def, div_eq_mul_inv] using H
  have H := (hExp.add hInv22).add hInv
  exact (tendsto_order.1 H).2 (ε / 4) (by nlinarith)

lemma exists_strictSeed (ε : ℝ) (hε : 0 < ε) : Nonempty (StrictSeed ε) := by
  obtain ⟨K, hK30, hKerr⟩ :=
    ((eventually_ge_atTop 30).and (eventually_seed_error_small ε hε)).exists
  have hKpos : 0 < K := by omega
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hKone : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  let h : ℕ := K ^ 12
  have hh : 1 < h := by
    have Hpow : 2 ^ 12 ≤ K ^ 12 := Nat.pow_le_pow_left (by omega) 12
    norm_num [h] at Hpow ⊢
    omega
  have hh0 : 0 < h := Nat.zero_lt_of_lt hh
  let a : ℝ := 1 / (K : ℝ) ^ 7
  let ρ : ℝ := a / 16
  have ha : 0 < a := by dsimp [a]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hsqrt : Real.sqrt (h : ℝ) = (K : ℝ) ^ 6 := by
    rw [show (h : ℝ) = ((K : ℝ) ^ 6) ^ 2 by
      norm_num [h]
      ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hβ : a + 2 * ρ = 9 / (8 * (K : ℝ) ^ 7) := by
    dsimp [a, ρ]
    field_simp
    ring
  have herror : 4 * (a + 2 * ρ) * Real.sqrt h = 9 / (2 * (K : ℝ)) := by
    rw [hβ, hsqrt]
    field_simp
    ring
  have hβ0 : 0 ≤ a + 2 * ρ := by positivity
  have hβ1 : a + 2 * ρ ≤ 1 := by
    rw [hβ]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * K ^ 7)).2
    have hpowK : (K : ℝ) ≤ K ^ 7 := by
      calc
        (K : ℝ) = K * 1 := by ring
        _ ≤ K * K ^ 6 := mul_le_mul_of_nonneg_left (one_le_pow₀ hKone) hKR.le
        _ = K ^ 7 := by ring
    have hK9 : (9 : ℝ) ≤ K := by exact_mod_cast (show 9 ≤ K by omega)
    nlinarith
  have hsmall : 4 * (a + 2 * ρ) * Real.sqrt h ≤ 1 / 2 := by
    rw [herror]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)).2
    nlinarith [show (9 : ℝ) ≤ K by exact_mod_cast (show 9 ≤ K by omega)]
  have ha0 : 0 ≤ a := ha.le
  have ha2 : a ≤ 2 := by
    have ha1 : a ≤ 1 := by
      dsimp [a]
      exact (div_le_one (by positivity)).2 (one_le_pow₀ hKone)
    linarith
  have ha4 : a < 1 / 4 := by
    have hpow : (4 : ℝ) < K ^ 7 := by
      have hK4 : (4 : ℝ) < K := by exact_mod_cast (show 4 < K by omega)
      calc
        (4 : ℝ) < K := hK4
        _ ≤ K ^ 7 := by
          calc
            (K : ℝ) = K * 1 := by ring
            _ ≤ K * K ^ 6 := mul_le_mul_of_nonneg_left (one_le_pow₀ hKone) hKR.le
            _ = K ^ 7 := by ring
    dsimp [a]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < K ^ 7)]
    nlinarith
  have haMix : a < 2 * (Real.sqrt 2 - 1) := by
    have hsqrt0 := Real.sqrt_nonneg 2
    have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsqrt54 : (5 : ℝ) / 4 < Real.sqrt 2 := by nlinarith
    nlinarith [ha4]
  have hd1 : 1 ≤ 2 - a + 2 * ρ := by nlinarith [hρ.le]
  let B : ℕ := netCard h ρ hρ
  have hBpos : 0 < B := netCard_pos h ρ hh0 hρ
  let L : ℕ := (B + 1) * K ^ 22
  have hLpos : 0 < L := by dsimp [L]; positivity
  let M : ℕ := copyCard h ρ hh0 hρ L
  let W := CopyVertex h ρ hh0 hρ L
  let G : SimpleGraph (Bool × W) := BEGraph h ρ hh0 hρ L a
  have hMlower : L ≤ M := scale_le_copyCard h ρ hh0 hρ L
  have hMupper : M ≤ L + B := copyCard_le_scale_add h ρ hh0 hρ L
  have hedgeRaw : (L : ℝ) ^ 2 *
      (1 / 2 - 4 * (a + 2 * ρ) * Real.sqrt h) ≤ Nat.card G.edgeSet := by
    simpa [G] using BEGraph_edgeCard_lower h ρ hh hρ L a hβ0 hβ1 hsmall
  have hfreeRaw : G.CliqueFree 4 := by
    simpa [G] using BEGraph_cliqueFree_four h ρ hh0 hρ L a ha0 ha4 haMix
  have hindRaw : (G.indepNum : ℝ) ≤ 2 *
      ((L : ℝ) * ((2 - a + 2 * ρ) / 2) ^ h + B) := by
    simpa [G] using BEGraph_indepNum_bound h ρ hh0 hρ L a ha2 hd1
  have hK22 : (K : ℝ) ≤ K ^ 22 := by
    calc
      (K : ℝ) = K * 1 := by ring
      _ ≤ K * K ^ 21 := mul_le_mul_of_nonneg_left (one_le_pow₀ hKone) hKR.le
      _ = K ^ 22 := by ring
  have hBKleL : (B : ℝ) * K ≤ L := by
    calc
      (B : ℝ) * K ≤ B * K ^ 22 :=
        mul_le_mul_of_nonneg_left hK22 (Nat.cast_nonneg B)
      _ ≤ (B + 1) * K ^ 22 := by gcongr; norm_num
      _ = (L : ℕ) := by norm_cast
  have hBdiv : (B : ℝ) ≤ L / K := (le_div_iff₀ hKR).2 hBKleL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hMbound : (M : ℝ) ≤ L * (1 + 1 / K) := by
    have HM : (M : ℝ) ≤ L + B := by exact_mod_cast hMupper
    calc
      (M : ℝ) ≤ L + B := HM
      _ ≤ L + L / K := by gcongr
      _ = L * (1 + 1 / K) := by ring
  have hradiusBase : (2 - a + 2 * ρ) / 2 =
      1 - 7 / (16 * (K : ℝ) ^ 7) := by
    dsimp [a, ρ]
    field_simp
    ring
  let x : ℝ := 7 / (16 * (K : ℝ) ^ 7)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * K ^ 7)).2
    have : (1 : ℝ) ≤ K ^ 7 := one_le_pow₀ hKone
    nlinarith only [this]
  have honeSub : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hbaseExp : 1 - x ≤ Real.exp (-x) := by
    simpa [add_comm] using Real.add_one_le_exp (-x)
  have hpowExp : (1 - x) ^ h ≤ Real.exp (-x) ^ h :=
    pow_le_pow_left₀ honeSub hbaseExp h
  have hhcast : (h : ℝ) = (K : ℝ) ^ 12 := by norm_num [h]
  have hexponent : Real.exp (-x) ^ h = Real.exp (-(7 * (K : ℝ) ^ 5 / 16)) := by
    rw [← Real.exp_nat_mul]
    apply congrArg Real.exp
    dsimp [x]
    rw [hhcast]
    field_simp
  have hKexp : (K : ℝ) ≤ 7 * K ^ 5 / 16 := by
    have hK4 : (16 : ℝ) ≤ 7 * K ^ 4 := by
      have hK4thirty : (30 : ℝ) ^ 4 ≤ K ^ 4 :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hK30) 4
      norm_num at hK4thirty ⊢
      nlinarith only [hK4thirty]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2
    have Hmul := mul_le_mul_of_nonneg_left hK4 hKR.le
    nlinarith only [Hmul]
  have halphaExp : ((2 - a + 2 * ρ) / 2) ^ h ≤ Real.exp (-(K : ℝ)) := by
    rw [hradiusBase]
    change (1 - x) ^ h ≤ _
    calc
      (1 - x) ^ h ≤ Real.exp (-x) ^ h := hpowExp
      _ = Real.exp (-(7 * (K : ℝ) ^ 5 / 16)) := hexponent
      _ ≤ Real.exp (-(K : ℝ)) := Real.exp_le_exp.mpr (by linarith only [hKexp])
  have hBK22leL : (B : ℝ) * K ^ 22 ≤ L := by
    change (B : ℝ) * K ^ 22 ≤ (((B + 1) * K ^ 22 : ℕ) : ℝ)
    push_cast
    gcongr
    norm_num
  have hRound : (B : ℝ) / L ≤ 1 / K ^ 22 := by
    rw [div_le_div_iff₀ hLR (by positivity : (0 : ℝ) < K ^ 22)]
    simpa using hBK22leL
  let t : ℕ := 100 * (B + 1) * K ^ 21
  let H : SimpleGraph ((Bool × W) ⊕ Fin t) := oneSidedExtension G t
  let instW : Fintype W := inferInstance
  have hWcard : @Fintype.card W instW = M := by simp [instW, W, M, copyCard]
  have hMpos : 0 < M := hLpos.trans_le hMlower
  letI : Nonempty W := Fintype.card_pos_iff.mp (by simpa [hWcard] using hMpos)
  have hfreeH : H.CliqueFree 4 := by
    apply oneSidedExtension_cliqueFree_four G t hfreeRaw
    intro u v w
    exact BEGraph_no_samePart_triangle hh0 hρ L a ha0 ha4 true u v w
  have htEq : (t : ℝ) = 100 * (L : ℝ) / K := by
    dsimp [t, L]
    push_cast
    field_simp
  have hedgeRaw' : (L : ℝ) ^ 2 * (1 / 2 - 9 / (2 * K)) ≤
      Nat.card G.edgeSet := by simpa [herror] using hedgeRaw
  have hedgeExtNat := oneSidedExtension_edgeCard_lower G t
  rw [hWcard] at hedgeExtNat
  have hedgeExt : (Nat.card G.edgeSet : ℝ) + (t : ℝ) * M ≤
      Nat.card H.edgeSet := by
    exact_mod_cast hedgeExtNat
  have hMlowerR : (L : ℝ) ≤ M := by exact_mod_cast hMlower
  have hedgeH : (L : ℝ) ^ 2 * (1 / 2 + 191 / (2 * K)) ≤
      Nat.card H.edgeSet := by
    have htpos : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have htmul : (100 * (L : ℝ) / K) * L ≤ (t : ℝ) * M := by
      rw [← htEq]
      exact mul_le_mul_of_nonneg_left hMlowerR htpos
    have hident : (100 * (L : ℝ) / K) * L = 100 * (L : ℝ) ^ 2 / K := by ring
    rw [hident] at htmul
    calc
      (L : ℝ) ^ 2 * (1 / 2 + 191 / (2 * K)) =
          (L : ℝ) ^ 2 * (1 / 2 - 9 / (2 * K)) + 100 * (L : ℝ) ^ 2 / K := by
            field_simp
            ring
      _ ≤ (Nat.card G.edgeSet : ℝ) + (t : ℝ) * M := add_le_add hedgeRaw' htmul
      _ ≤ Nat.card H.edgeSet := hedgeExt
  let instH : Fintype ((Bool × W) ⊕ Fin t) := inferInstance
  have hcardH : @Fintype.card ((Bool × W) ⊕ Fin t) instH = 2 * M + t := by
    simp [instH, hWcard]
  have hcardHpos : 0 < @Fintype.card ((Bool × W) ⊕ Fin t) instH := by
    rw [hcardH]
    omega
  have hcardBound : ((@Fintype.card ((Bool × W) ⊕ Fin t) instH : ℕ) : ℝ) ≤
      2 * (L : ℝ) * (1 + 51 / K) := by
    rw [hcardH]
    push_cast
    rw [htEq]
    calc
      2 * (M : ℝ) + 100 * (L : ℝ) / K ≤
          2 * ((L : ℝ) * (1 + 1 / K)) + 100 * (L : ℝ) / K := by
            gcongr
      _ = 2 * (L : ℝ) * (1 + 51 / K) := by ring
  have hcardSq : (((@Fintype.card ((Bool × W) ⊕ Fin t) instH : ℕ) : ℝ) ^ 2) / 8 ≤
      (L : ℝ) ^ 2 * (1 / 2 + 51 / K + 2601 / (2 * K ^ 2)) := by
    have hcardNonneg : (0 : ℝ) ≤ (@Fintype.card ((Bool × W) ⊕ Fin t) instH : ℕ) :=
      Nat.cast_nonneg _
    have hrightNonneg : (0 : ℝ) ≤ 2 * (L : ℝ) * (1 + 51 / K) := by positivity
    have hsq := pow_le_pow_left₀ hcardNonneg hcardBound 2
    calc
      (((@Fintype.card ((Bool × W) ⊕ Fin t) instH : ℕ) : ℝ) ^ 2) / 8 ≤
          (2 * (L : ℝ) * (1 + 51 / K)) ^ 2 / 8 := by gcongr
      _ = (L : ℝ) ^ 2 * (1 / 2 + 51 / K + 2601 / (2 * K ^ 2)) := by ring
  have hcoeff : (1 : ℝ) / 2 + 51 / K + 2601 / (2 * K ^ 2) <
      1 / 2 + 191 / (2 * K) := by
    field_simp [hKR.ne']
    nlinarith only [show (30 : ℝ) ≤ K by exact_mod_cast hK30]
  have hedgeStrictR :
      (((@Fintype.card ((Bool × W) ⊕ Fin t) instH : ℕ) : ℝ) ^ 2) / 8 <
        Nat.card H.edgeSet := by
    have hLsqPos : 0 < (L : ℝ) ^ 2 := sq_pos_of_pos hLR
    exact lt_of_le_of_lt hcardSq <|
      lt_of_lt_of_le (mul_lt_mul_of_pos_left hcoeff hLsqPos) hedgeH
  have hedgeStrictNat : (@Fintype.card ((Bool × W) ⊕ Fin t) instH) ^ 2 <
      8 * Nat.card H.edgeSet := by
    let m : ℕ := @Fintype.card ((Bool × W) ⊕ Fin t) instH
    let E : ℕ := Nat.card H.edgeSet
    have hreal : (m : ℝ) ^ 2 < 8 * (E : ℝ) := by
      have hbase : (m : ℝ) ^ 2 / 8 < (E : ℝ) := by
        simpa [m, E] using hedgeStrictR
      calc
        (m : ℝ) ^ 2 = 8 * ((m : ℝ) ^ 2 / 8) := by ring
        _ < 8 * (E : ℝ) := mul_lt_mul_of_pos_left hbase (by norm_num)
    have hnat : m ^ 2 < 8 * E := by exact_mod_cast hreal
    simpa [m, E] using hnat
  have hindHNat := oneSidedExtension_indepNum_le G t
  have hindH : (H.indepNum : ℝ) ≤ 2 *
      ((L : ℝ) * Real.exp (-(K : ℝ)) + B) + t := by
    have hindH' : (H.indepNum : ℝ) ≤ (G.indepNum : ℝ) + t := by
      exact_mod_cast hindHNat
    nlinarith only [hindH', hindRaw, halphaExp, hLR.le,
      mul_le_mul_of_nonneg_left halphaExp hLR.le]
  have hBbound : (B : ℝ) ≤ (L : ℝ) / K ^ 22 := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < K ^ 22)).2
    simpa [mul_comm] using hBK22leL
  have hindError : (H.indepNum : ℝ) ≤ 2 * (L : ℝ) *
      (Real.exp (-(K : ℝ)) + 1 / K ^ 22 + 50 / K) := by
    calc
      (H.indepNum : ℝ) ≤ 2 * ((L : ℝ) * Real.exp (-(K : ℝ)) + B) + t := hindH
      _ ≤ 2 * ((L : ℝ) * Real.exp (-(K : ℝ)) + L / K ^ 22) +
          100 * L / K := by
            rw [htEq]
            gcongr
      _ = 2 * (L : ℝ) *
          (Real.exp (-(K : ℝ)) + 1 / K ^ 22 + 50 / K) := by ring
  have hcardLowerR : 2 * (L : ℝ) ≤
      (@Fintype.card ((Bool × W) ⊕ Fin t) instH : ℕ) := by
    rw [hcardH]
    push_cast
    have htR : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    nlinarith only [hMlowerR, htR]
  have hindSmall : 4 * (H.indepNum : ℝ) <
      ε * (@Fintype.card ((Bool × W) ⊕ Fin t) instH : ℕ) := by
    have hεnonneg := hε.le
    have herrorLt : 2 * (L : ℝ) *
        (Real.exp (-(K : ℝ)) + 1 / K ^ 22 + 50 / K) < ε * (L : ℝ) / 2 := by
      have hscale : (0 : ℝ) < 2 * (L : ℝ) := by positivity
      have H := mul_lt_mul_of_pos_left hKerr hscale
      nlinarith only [H]
    have hright := mul_le_mul_of_nonneg_left hcardLowerR hεnonneg
    nlinarith only [hindError, herrorLt, hright]
  exact ⟨⟨_, instH, H, hcardHpos, hfreeH, hindSmall, hedgeStrictNat⟩⟩

/-! ## Strict seed implies witnesses at every sufficiently large order -/

lemma strict_surplus_absorbs_padding {m E q r : ℕ} (hm : 0 < m)
    (hseed : m ^ 2 < 8 * E) (hr : r < m) (hq : 3 * m ^ 2 ≤ q) :
    (q * m + r) ^ 2 ≤ 8 * (q ^ 2 * E) := by
  have hseed' : m ^ 2 + 1 ≤ 8 * E := by omega
  have hq1 : 1 ≤ q := by nlinarith [sq_pos_of_pos (show (0 : ℝ) < m by exact_mod_cast hm)]
  have hrle : r ≤ m := Nat.le_of_lt hr
  have htwo : 2 * q * m * r ≤ 2 * q * m * m := by gcongr
  have hrsq : r ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hrle 2
  have hmtoq : m ^ 2 ≤ q * m ^ 2 := by
    calc
      m ^ 2 = 1 * m ^ 2 := by simp
      _ ≤ q * m ^ 2 := Nat.mul_le_mul_right _ hq1
  have hqbig : 3 * q * m ^ 2 ≤ q ^ 2 := by
    have H := Nat.mul_le_mul_left q hq
    nlinarith only [H]
  have hroom : 2 * q * m * r + r ^ 2 ≤ q ^ 2 := by
    nlinarith only [htwo, hrsq, hmtoq, hqbig]
  have hscaled := Nat.mul_le_mul_left (q ^ 2) hseed'
  nlinarith only [hroom, hscaled]

lemma eventual_graphs (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ (n : ℕ) in atTop,
      ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
        (G.indepNum : ℝ) ≤ ε * n ∧ (n : ℝ) ^ 2 / 8 ≤ G.edgeFinset.card := by
  rcases exists_strictSeed ε hε with ⟨S⟩
  letI : Fintype S.Vertex := S.fintypeVertex
  let m : ℕ := Fintype.card S.Vertex
  have hm : 0 < m := S.card_pos
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (m : ℝ) / ε)
  refine Filter.eventually_atTop.2 ⟨max (3 * m ^ 3) N, ?_⟩
  intro n hn
  have hnCube : 3 * m ^ 3 ≤ n := (le_max_left _ _).trans hn
  have hNn : N ≤ n := (le_max_right _ _).trans hn
  let q : ℕ := n / m
  let r : ℕ := n % m
  have hr : r < m := Nat.mod_lt n hm
  have hq : 3 * m ^ 2 ≤ q := by
    apply (Nat.le_div_iff_mul_le hm).2
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hnCube
  have hqpos : 0 < q := by
    have hleft : 0 < 3 * m ^ 2 := by positivity
    omega
  have hdecomp : q * m + r = n := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using Nat.div_add_mod n m
  let A := (S.Vertex × Fin q) ⊕ Fin r
  let P : SimpleGraph A := paddedBlowup S.graph q r
  let instA : Fintype A := inferInstance
  have hcardA : @Fintype.card A instA = n := by
    simp only [A, instA, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    change m * q + r = n
    simpa [Nat.mul_comm] using hdecomp
  let e : A ≃ Fin n := Fintype.equivFinOfCardEq hcardA
  let Gfin : SimpleGraph (Fin n) := P.map e.toEmbedding
  letI : DecidableRel Gfin.Adj := fun _ _ ↦ Classical.propDecidable _
  have hnpos : 0 < n := by
    rw [← hdecomp]
    positivity
  letI : Nonempty A := Fintype.card_pos_iff.mp (by simpa [hcardA] using hnpos)
  have hfreeP : P.CliqueFree 4 := paddedBlowup_cliqueFree_four S.graph q r S.cliqueFree
  have hfreeFin : Gfin.CliqueFree 4 := by
    simpa [Gfin] using
      (SimpleGraph.cliqueFree_map_iff (G := P) (f := e.toEmbedding)).2 hfreeP
  have hIndEq : Gfin.indepNum = P.indepNum := by
    simpa [Gfin] using Erdos615.indepNum_map_equiv P e
  have hIndNat : P.indepNum ≤ q * S.graph.indepNum + r :=
    paddedBlowup_indepNum_le S.graph q r
  have hIndCast : (P.indepNum : ℝ) ≤
      (q : ℝ) * S.graph.indepNum + r := by exact_mod_cast hIndNat
  have hseedScaled : 4 * (q : ℝ) * S.graph.indepNum <
      (q : ℝ) * ε * m := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
    have H := mul_lt_mul_of_pos_left S.indep_small hqR
    nlinarith only [H]
  have hmSmall : (m : ℝ) ≤ ε * n / 2 := by
    have hNcast : (N : ℝ) ≤ n := by exact_mod_cast hNn
    have hmul : 2 * (m : ℝ) < (N : ℝ) * ε := by
      exact (div_lt_iff₀ hε).mp hN
    nlinarith only [hmul, hNcast, hε]
  have hrSmall : (r : ℝ) ≤ ε * n / 2 := by
    have hrR : (r : ℝ) ≤ m := by exact_mod_cast (Nat.le_of_lt hr)
    exact hrR.trans hmSmall
  have hdecompR : (q : ℝ) * m + r = n := by exact_mod_cast hdecomp
  have hIndFin : (Gfin.indepNum : ℝ) ≤ ε * n := by
    rw [hIndEq]
    nlinarith only [hIndCast, hseedScaled, hrSmall, hdecompR, hε]
  have hEdgeP : Nat.card P.edgeSet = q ^ 2 * Nat.card S.graph.edgeSet :=
    paddedBlowup_edgeCard S.graph q r
  have hEdgeNat : n ^ 2 ≤ 8 * Nat.card P.edgeSet := by
    rw [hEdgeP, ← hdecomp]
    exact strict_surplus_absorbs_padding hm S.edge_strict hr hq
  have hEdgeEq : Gfin.edgeFinset.card = Nat.card P.edgeSet := by
    calc
      Gfin.edgeFinset.card = P.edgeFinset.card := by
        simpa [Gfin] using (SimpleGraph.Iso.map e P).card_edgeFinset_eq.symm
      _ = Fintype.card P.edgeSet := P.edgeFinset_card
      _ = Nat.card P.edgeSet := Nat.card_eq_fintype_card.symm
  have hEdgeFin : (n : ℝ) ^ 2 / 8 ≤ Gfin.edgeFinset.card := by
    rw [hEdgeEq]
    have H : (n : ℝ) ^ 2 ≤ 8 * (Nat.card P.edgeSet : ℝ) := by exact_mod_cast hEdgeNat
    nlinarith only [H]
  exact ⟨Gfin, hfreeFin, hIndFin, hEdgeFin⟩

theorem erdos_22 :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop,
      ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
        (G.indepNum : ℝ) ≤ ε * n ∧ (n : ℝ) ^ 2 / 8 ≤ G.edgeFinset.card := by
  intro ε hε
  exact eventual_graphs ε hε

end

#print axioms erdos_22
-- 'Erdos22.erdos_22' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos22
