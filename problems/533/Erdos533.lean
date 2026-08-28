import Mathlib

namespace Erdos533

/-
# Problem Description

Erdős Problem 533. Let `δ > 0`. If `n` is sufficiently large and `G` is a graph on `n`
vertices with no `K₅` and at least `δn²` edges, must `G` contain a set of `≫_δ n` vertices
spanning no triangle? `erdos_533` disproves this.

The counterexample family formalised below has fixed edge density `1/32`, is `K₅`-free, and
has triangle-independence number `o(n)`, so no linear-in-`n` triangle-free vertex set exists.
In the statement, "`≫_δ n` vertices" is rendered as a constant `c > 0` depending only on `δ`
with `c * n ≤ S.card`, and "containing no triangle" as `G.CliqueFreeOn S 3`.

The formalisation is by plby (github.com/plby/lean-proofs),
`src/latest/ErdosProblems/Erdos533.lean` together with the modules of
`src/latest/ErdosProblems/Erdos533/`. Those files are concatenated here in dependency order,
with their project-internal imports removed so that `Mathlib` is the only import, each
module's contents kept in a `section` carrying its own `open` lines, the whole wrapped once in
`namespace Erdos533`, the upstream trust-base print line and trailing `alias` removed, and the
final theorem renamed from `not_erdos_533` to `erdos_533`. No mathematical content is changed.
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


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos533.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 533.
https://www.erdosproblems.com/forum/thread/533

Informal authors:
- József Balogh
- John Lenz
- Hong Liu
- Christian Reiher
- Maryam Sharifzadeh
- Katherine Staden

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos533.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/533.lean
-/
/-
Formalization of the negative answer to Erdős Problem 533.

The mathematical construction is the `p = 3`, `ℓ = 1` specialization of
the complex Bollobás--Erdős graph of Liu, Reiher, Sharifzadeh, and Staden.
-/


open Filter SimpleGraph
open Set MeasureTheory
open scoped Classical ENNReal NNReal Pointwise Topology BigOperators



/-! ## The complex sphere used by the LRSS construction -/

/-- The unit sphere in a nonzero finite-dimensional complex Euclidean space.
The parameter is shifted by one so that the sphere is nonempty also at `k = 0`. -/
abbrev ComplexSphere (k : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1

instance complexSphereNonempty (k : ℕ) : Nonempty (ComplexSphere k) :=
  ⟨⟨EuclideanSpace.single 0 1, by simp [ComplexSphere, Metric.mem_sphere]⟩⟩

/-- Surface measure on `ComplexSphere k`, regarded as a bundled finite measure. -/
noncomputable def complexSphereFiniteMeasure (k : ℕ) :
    MeasureTheory.FiniteMeasure (ComplexSphere k) :=
  ⟨MeasureTheory.Measure.toSphere MeasureTheory.volume, inferInstance⟩

/-- Normalized surface measure on the complex unit sphere. -/
noncomputable def complexSphereProbability (k : ℕ) :
    MeasureTheory.ProbabilityMeasure (ComplexSphere k) :=
  (complexSphereFiniteMeasure k).normalize

@[simp] theorem complexSphereProbability_univ (k : ℕ) :
    (complexSphereProbability k : MeasureTheory.Measure (ComplexSphere k)) Set.univ = 1 := by
  exact MeasureTheory.measure_univ

/-! ## A two-set concentration lemma on a real sphere -/

/-- Brunn--Minkowski applied to the two truncated cones over `A` and `-B`.
If both sets have more than `(d / 2)^h` of the spherical surface measure,
then some pair has distance greater than `d`.  This two-set form is the
concentration input used to find the three approximate rotations. -/
theorem realSphere_two_set_far (h : ℕ) (hh : 0 < h)
    (A B : Set (Erdos615.Construction.Sphere h))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (d : ℝ) (hd : 1 ≤ d) (q : ℝ≥0∞)
    (hq : ENNReal.ofReal ((d / 2) ^ h) < q)
    (hAq : q * volume.toSphere
      (Set.univ : Set (Erdos615.Construction.Sphere h)) < volume.toSphere A)
    (hBq : q * volume.toSphere
      (Set.univ : Set (Erdos615.Construction.Sphere h)) < volume.toSphere B) :
    ∃ a ∈ A, ∃ b ∈ B, d < dist a b := by
  let E := EuclideanSpace ℝ (Fin h)
  let V : ℝ≥0∞ := volume (Metric.ball (0 : E) 1)
  obtain ⟨KA, hKAA, hKA, hKAq⟩ := hA.exists_lt_isCompact hAq
  obtain ⟨KB, hKBB, hKB, hKBq⟩ := hB.exists_lt_isCompact hBq
  let OA : Set E := Set.Ioo (0 : ℝ) 1 • ((↑) '' KA)
  let OB : Set E := Set.Ioo (0 : ℝ) 1 • ((↑) '' KB)
  let CA : Set E := Set.Icc (0 : ℝ) 1 • ((↑) '' KA)
  let CB : Set E := Set.Icc (0 : ℝ) 1 • ((↑) '' KB)
  have hCA : IsCompact CA :=
    isCompact_Icc.smul_set (hKA.image continuous_subtype_val)
  have hCB : IsCompact CB :=
    isCompact_Icc.smul_set (hKB.image continuous_subtype_val)
  have hh0 : (h : ℝ≥0∞) ≠ 0 := by simp [hh.ne']
  have hhtop : (h : ℝ≥0∞) ≠ ∞ := by simp
  have htotal : volume.toSphere
      (Set.univ : Set (Metric.sphere (0 : E) 1)) = (h : ℝ≥0∞) * V := by
    simp [E, V, Measure.toSphere_apply_univ, finrank_euclideanSpace_fin]
  have hOAK : volume.toSphere KA = (h : ℝ≥0∞) * volume OA := by
    rw [Measure.toSphere_apply' volume hKA.measurableSet]
    simp only [OA, E, finrank_euclideanSpace_fin]
  have hOBK : volume.toSphere KB = (h : ℝ≥0∞) * volume OB := by
    rw [Measure.toSphere_apply' volume hKB.measurableSet]
    simp only [OB, E, finrank_euclideanSpace_fin]
  have hOA_lower : q * V < volume OA := by
    by_contra hn
    have hle : volume OA ≤ q * V := not_lt.mp hn
    have hmul := mul_le_mul_right hle (h : ℝ≥0∞)
    apply not_lt_of_ge hmul
    simpa [htotal, hOAK, mul_assoc, mul_left_comm, mul_comm] using hKAq
  have hOB_lower : q * V < volume OB := by
    by_contra hn
    have hle : volume OB ≤ q * V := not_lt.mp hn
    have hmul := mul_le_mul_right hle (h : ℝ≥0∞)
    apply not_lt_of_ge hmul
    simpa [htotal, hOBK, mul_assoc, mul_left_comm, mul_comm] using hKBq
  have hOA_CA : OA ⊆ CA := by
    rintro x ⟨r, hr, y, hy, rfl⟩
    exact ⟨r, Set.mem_Icc.mpr ⟨hr.1.le, hr.2.le⟩, y, hy, rfl⟩
  have hOB_CB : OB ⊆ CB := by
    rintro x ⟨r, hr, y, hy, rfl⟩
    exact ⟨r, Set.mem_Icc.mpr ⟨hr.1.le, hr.2.le⟩, y, hy, rfl⟩
  have hCA_lower : q * V < volume CA :=
    hOA_lower.trans_le (measure_mono hOA_CA)
  have hCB_lower : q * V < volume CB :=
    hOB_lower.trans_le (measure_mono hOB_CB)
  by_contra hfar
  push Not at hfar
  let M : Set E := ((2 : ℝ)⁻¹ • CA) + ((2 : ℝ)⁻¹ • (-CB))
  have hBM : volume M ≥
      volume CA ^ (2 : ℝ)⁻¹ * volume (-CB) ^ (2 : ℝ)⁻¹ := by
    exact Erdos615.BrunnMinkowski.brunnMinkowski_multiplicative_of_hasPrekopaLeindler
      (Erdos615.BrunnMinkowski.hasPrekopaLeindler_euclidean h)
      CA (-CB) hCA.measurableSet hCB.neg.measurableSet
      (2 : ℝ)⁻¹ (2 : ℝ)⁻¹ (by norm_num) (by norm_num) (by norm_num)
  have hneg : volume (-CB) = volume CB := Measure.measure_neg volume CB
  have hM_lower : q * V < volume M := by
    have hca := ENNReal.rpow_lt_rpow hCA_lower
      (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
    have hcb := ENNReal.rpow_lt_rpow hCB_lower
      (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
    have hCApos : 0 < volume CA := bot_le.trans_lt hCA_lower
    have hCArpow0 : volume CA ^ (2 : ℝ)⁻¹ ≠ 0 :=
      (ENNReal.rpow_pos hCApos hCA.measure_lt_top.ne).ne'
    have hCArpowTop : volume CA ^ (2 : ℝ)⁻¹ ≠ ∞ :=
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hCA.measure_lt_top.ne).ne
    calc
      q * V = (q * V) ^ (2 : ℝ)⁻¹ * (q * V) ^ (2 : ℝ)⁻¹ := by
        rw [← ENNReal.rpow_add_of_nonneg] <;> norm_num
      _ ≤ volume CA ^ (2 : ℝ)⁻¹ * (q * V) ^ (2 : ℝ)⁻¹ :=
        mul_le_mul_left hca.le _
      _ < volume CA ^ (2 : ℝ)⁻¹ * volume CB ^ (2 : ℝ)⁻¹ := by
        simpa [mul_comm] using
          ENNReal.mul_lt_mul_left hCArpow0 hCArpowTop hcb
      _ = volume CA ^ (2 : ℝ)⁻¹ * volume (-CB) ^ (2 : ℝ)⁻¹ := by rw [hneg]
      _ ≤ volume M := hBM
  have hnorm (x : Metric.sphere (0 : E) 1) : ‖(x : E)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.property
  have hMball : M ⊆ Metric.closedBall (0 : E) (d / 2) := by
    intro z hz
    rcases hz with ⟨u, hu, v, hv, rfl⟩
    rcases hu with ⟨a, ha, rfl⟩
    rcases hv with ⟨nb, hnb, rfl⟩
    have hnb' : -nb ∈ CB := Set.mem_neg.mp hnb
    rcases ha with ⟨r, hr, ar, har, rfl⟩
    rcases har with ⟨a, haK, rfl⟩
    rcases hnb' with ⟨s, hs, br, hbr, hsbr⟩
    rcases hbr with ⟨b, hbK, rfl⟩
    have hnb_eq : nb = -(s • (b : E)) := by
      have hn := congrArg Neg.neg hsbr
      exact (neg_neg nb).symm.trans hn.symm
    subst nb
    rw [Metric.mem_closedBall, dist_zero_right]
    have hab : dist (a : E) b ≤ d := hfar a (hKAA haK) b (hKBB hbK)
    have aux (hrs : r ≤ s) : ‖r • (a : E) - s • (b : E)‖ ≤ d := by
      calc
        ‖r • (a : E) - s • (b : E)‖ =
            ‖r • ((a : E) - b) + (r - s) • (b : E)‖ := by
          congr 1
          simp only [smul_sub, sub_smul]
          abel
        _ ≤ ‖r • ((a : E) - b)‖ + ‖(r - s) • (b : E)‖ := norm_add_le _ _
        _ = r * dist (a : E) b + (s - r) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hr.1, abs_of_nonpos (sub_nonpos.mpr hrs), hnorm b,
            mul_one, dist_eq_norm]
          ring
        _ ≤ r * d + (s - r) := by
          simpa [add_comm] using
            add_le_add_right (mul_le_mul_of_nonneg_left hab hr.1) (s - r)
        _ ≤ d := by nlinarith [hr.2, hs.2]
    have hrsnorm : ‖r • (a : E) - s • (b : E)‖ ≤ d := by
      rcases le_total r s with hrs | hsr
      · exact aux hrs
      · rw [norm_sub_rev]
        have hba : dist (b : E) (a : E) ≤ d := by
          calc
            dist (b : E) (a : E) = dist (a : E) (b : E) := dist_comm _ _
            _ ≤ d := hab
        calc
          ‖s • (b : E) - r • (a : E)‖ =
              ‖s • ((b : E) - a) + (s - r) • (a : E)‖ := by
            congr 1
            simp only [smul_sub, sub_smul]
            abel
          _ ≤ ‖s • ((b : E) - a)‖ + ‖(s - r) • (a : E)‖ := norm_add_le _ _
          _ = s * dist (b : E) a + (r - s) := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg hs.1, abs_of_nonpos (sub_nonpos.mpr hsr), hnorm a,
              mul_one, dist_eq_norm]
            ring
          _ ≤ s * d + (r - s) := by
            simpa [add_comm] using
              add_le_add_right (mul_le_mul_of_nonneg_left hba hs.1) (r - s)
          _ ≤ d := by nlinarith [hr.2, hs.2]
    exact (show
      ‖(2 : ℝ)⁻¹ • (r • (a : E)) + (2 : ℝ)⁻¹ • (-(s • (b : E)))‖ ≤ d / 2 from
      calc
        ‖(2 : ℝ)⁻¹ • (r • (a : E)) + (2 : ℝ)⁻¹ • (-(s • (b : E)))‖ =
            ‖(2 : ℝ)⁻¹ • (r • (a : E) - s • (b : E))‖ := by
          congr 1
          simp only [smul_neg, smul_sub, smul_smul]
          abel
        _ = (2 : ℝ)⁻¹ * ‖r • (a : E) - s • (b : E)‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          norm_num
        _ ≤ (2 : ℝ)⁻¹ * d := mul_le_mul_of_nonneg_left hrsnorm (by norm_num)
        _ = d / 2 := inv_mul_eq_div 2 d)
  have hball : volume (Metric.closedBall (0 : E) (d / 2)) =
      ENNReal.ofReal ((d / 2) ^ h) * V := by
    rw [Measure.addHaar_closedBall' volume (0 : E) (by linarith)]
    simp [E, V, finrank_euclideanSpace_fin,
      Measure.addHaar_unitClosedBall_eq_addHaar_unitBall]
  have hV0 : V ≠ 0 := by
    exact ne_of_gt (by simpa [V] using
      Metric.measure_ball_pos (volume : Measure E) (0 : E) zero_lt_one)
  have hVtop : V ≠ ∞ := by
    exact ne_of_lt (by simpa [V] using
      (measure_ball_lt_top : volume (Metric.ball (0 : E) 1) < ∞))
  have hpqV : ENNReal.ofReal ((d / 2) ^ h) * V < q * V :=
    ENNReal.mul_lt_mul_left hV0 hVtop hq
  exact (not_lt_of_ge ((measure_mono hMball).trans_eq hball))
    (hpqV.trans hM_lower)

/-- Probability-normalized version of `realSphere_two_set_far`, phrased in
the normalization used by the finite partition from Problem 615. -/
theorem sphereProbability_two_set_far (h : ℕ) (hh : 0 < h)
    (A B : Set (Erdos615.Construction.Sphere h))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (d q : ℝ) (hd : 1 ≤ d) (hq0 : 0 ≤ q)
    (hpow : (d / 2) ^ h < q)
    (hAq : q < (Erdos615.Construction.sphereProbability h hh A : ℝ))
    (hBq : q < (Erdos615.Construction.sphereProbability h hh B : ℝ)) :
    ∃ a ∈ A, ∃ b ∈ B, d < dist a b := by
  have hAun : ENNReal.ofReal q * volume.toSphere
      (Set.univ : Set (Erdos615.Construction.Sphere h)) < volume.toSphere A := by
    apply lt_of_not_ge
    intro hle
    have hp := Erdos615.Construction.sphereProbability_le_of_toSphere_le
      h hh A q hq0 hle
    linarith
  have hBun : ENNReal.ofReal q * volume.toSphere
      (Set.univ : Set (Erdos615.Construction.Sphere h)) < volume.toSphere B := by
    apply lt_of_not_ge
    intro hle
    have hp := Erdos615.Construction.sphereProbability_le_of_toSphere_le
      h hh B q hq0 hle
    linarith
  apply realSphere_two_set_far h hh A B hA hB d hd (ENNReal.ofReal q)
  · have hqpos : 0 < q :=
      (pow_nonneg (by linarith : 0 ≤ d / 2) h).trans_lt hpow
    exact (ENNReal.ofReal_lt_ofReal_iff hqpos).mpr hpow
  · exact hAun
  · exact hBun

/-! ## The order-three complex rotation -/

/-- The primitive cube root of unity used by the `p = 3` construction. -/
noncomputable def rho : ℂ :=
  (-1 / 2 : ℂ) + (Real.sqrt 3 / 2 : ℝ) * Complex.I

private lemma sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := by
  norm_num

@[simp] theorem rho_re : rho.re = -1 / 2 := by
  simp [rho]

@[simp] theorem rho_im : rho.im = Real.sqrt 3 / 2 := by
  simp [rho]

theorem rho_sq : rho ^ 2 =
    (-1 / 2 : ℂ) - (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  apply Complex.ext <;> simp [rho, pow_two]
  · nlinarith [sqrt_three_sq]
  · ring

@[simp] theorem rho_cube : rho ^ 3 = 1 := by
  rw [show rho ^ 3 = rho ^ 2 * rho by ring, rho_sq]
  apply Complex.ext <;> simp [rho]
  · nlinarith [sqrt_three_sq]
  · ring

theorem one_add_rho_add_sq : 1 + rho + rho ^ 2 = 0 := by
  rw [rho_sq]
  apply Complex.ext <;> simp [rho]
  <;> ring

@[simp] theorem norm_rho : ‖rho‖ = 1 := by
  rw [Complex.norm_def]
  rw [show Complex.normSq rho = 1 by
    simp [rho, Complex.normSq_apply]
    nlinarith [sqrt_three_sq]]
  norm_num

/-- A real orthonormal basis identifying `ℂ^(k+1)` with `ℝ^(2(k+1))`. -/
noncomputable def complexRealBasis (k : ℕ) :
    OrthonormalBasis (Fin ((k + 1) * 2)) ℝ
      (EuclideanSpace ℂ (Fin (k + 1))) :=
  (Pi.orthonormalBasis fun _ : Fin (k + 1) =>
    Complex.orthonormalBasisOneI).reindex
      ((Equiv.sigmaEquivProd (Fin (k + 1)) (Fin 2)).trans finProdFinEquiv)

/-- Coordinatewise multiplication by a unit complex number, as a real
linear isometry of complex Euclidean space. -/
noncomputable def complexScalarIsometry (k : ℕ) (u : ℂ) (hu : ‖u‖ = 1) :
    EuclideanSpace ℂ (Fin (k + 1)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℂ (Fin (k + 1)) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun _ : Fin (k + 1) => rotation
      ⟨u, by
        simpa [Submonoid.unitSphere, Metric.mem_sphere, dist_zero_right] using hu⟩)

@[simp] theorem complexScalarIsometry_apply (k : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    (x : EuclideanSpace ℂ (Fin (k + 1))) :
    complexScalarIsometry k u hu x = u • x := by
  ext i
  rfl

/-- The same complex rotation transported to the real coordinate sphere. -/
noncomputable def realCoordinateRotation (k : ℕ) (u : ℂ) (hu : ‖u‖ = 1) :
    EuclideanSpace ℝ (Fin ((k + 1) * 2)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin ((k + 1) * 2)) :=
  (complexRealBasis k).repr.symm.trans
    ((complexScalarIsometry k u hu).trans (complexRealBasis k).repr)

@[simp] theorem realCoordinateRotation_apply (k : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    (x : EuclideanSpace ℝ (Fin ((k + 1) * 2))) :
    (complexRealBasis k).repr.symm (realCoordinateRotation k u hu x) =
      u • (complexRealBasis k).repr.symm x := by
  simp [realCoordinateRotation]

/-- A real linear isometry restricts to an equivalence of the unit sphere. -/
noncomputable def realSphereEquiv {h : ℕ}
    (e : EuclideanSpace ℝ (Fin h) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h)) :
    Erdos615.Construction.Sphere h ≃ Erdos615.Construction.Sphere h where
  toFun x := ⟨e x, by
    simpa [Erdos615.Construction.Sphere, Metric.mem_sphere, dist_zero_right]
      using x.property⟩
  invFun x := ⟨e.symm x, by
    simpa [Erdos615.Construction.Sphere, Metric.mem_sphere, dist_zero_right]
      using x.property⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

@[simp] theorem realSphereEquiv_coe {h : ℕ}
    (e : EuclideanSpace ℝ (Fin h) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h))
    (x : Erdos615.Construction.Sphere h) :
    ((realSphereEquiv e x : Erdos615.Construction.Sphere h) :
      EuclideanSpace ℝ (Fin h)) = e x := rfl

/-- Normalized spherical measure is invariant under every ambient real linear
isometry.  The proof compares the truncated cones in the definition of
`Measure.toSphere`. -/
theorem sphereProbability_preimage_linearIsometry (h : ℕ) (hh : 0 < h)
    (e : EuclideanSpace ℝ (Fin h) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h))
    (A : Set (Erdos615.Construction.Sphere h)) (hA : MeasurableSet A) :
    Erdos615.Construction.sphereProbability h hh
        ((realSphereEquiv e) ⁻¹' A) =
      Erdos615.Construction.sphereProbability h hh A := by
  letI : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
  letI : Nonempty (Erdos615.Construction.Sphere h) :=
    Erdos615.Construction.sphereNonempty h hh
  let M := Erdos615.Construction.sphereFiniteMeasure h
  let P := Erdos615.Construction.sphereProbability h hh
  let eS := realSphereEquiv e
  have hpreMeas : MeasurableSet (eS ⁻¹' A) := by
    apply hA.preimage
    exact ((e.continuous.comp continuous_subtype_val).subtype_mk _).measurable
  have hcone : Set.Ioo (0 : ℝ) 1 • ((↑) '' (eS ⁻¹' A)) =
      e ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' A)) := by
    ext z
    constructor
    · rintro ⟨r, hr, yr, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨r, hr, e (w : EuclideanSpace ℝ (Fin h)),
        ⟨eS w, hw, rfl⟩, ?_⟩
      simp [eS, realSphereEquiv]
    · rintro ⟨r, hr, yr, ⟨w, hw, rfl⟩, hzw⟩
      let w' : Erdos615.Construction.Sphere h :=
        ⟨e.symm w, by
          simpa [Erdos615.Construction.Sphere, Metric.mem_sphere, dist_zero_right]
            using w.property⟩
      refine ⟨r, hr, (w' : EuclideanSpace ℝ (Fin h)), ⟨w', ?_, rfl⟩, ?_⟩
      · change eS w' ∈ A
        simpa [eS, w', realSphereEquiv] using hw
      · apply e.injective
        simpa [w'] using hzw
  have Henn : (M : Measure (Erdos615.Construction.Sphere h)) (eS ⁻¹' A) =
      (M : Measure (Erdos615.Construction.Sphere h)) A := by
    rw [show (M : Measure (Erdos615.Construction.Sphere h)) =
      (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere by rfl]
    rw [Measure.toSphere_apply' volume hpreMeas,
      Measure.toSphere_apply' volume hA, hcone]
    congr 1
    have hvol : MeasurePreserving
        (⇑e.toHomeomorph.toMeasurableEquiv) volume volume := by
      simpa using e.measurePreserving
    exact hvol.measure_preimage_equiv _
  have H : M (eS ⁻¹' A) = M A := by
    exact congrArg ENNReal.toNNReal Henn
  have hMne : M ≠ 0 := by
    have hμ : (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere ≠ 0 :=
      Measure.toSphere_ne_zero (volume : Measure (EuclideanSpace ℝ (Fin h)))
    intro hzero
    have hcoe := congrArg
      (fun N : FiniteMeasure (Erdos615.Construction.Sphere h) =>
        (N : Measure (Erdos615.Construction.Sphere h))) hzero
    exact hμ (by simpa [M, Erdos615.Construction.sphereFiniteMeasure] using hcoe)
  have hmass : M.mass ≠ 0 := M.mass_nonzero_iff.mpr hMne
  apply mul_left_cancel₀ hmass
  calc
    M.mass * P (eS ⁻¹' A) = M (eS ⁻¹' A) :=
      (M.self_eq_mass_mul_normalize _).symm
    _ = M A := H
    _ = M.mass * P A := M.self_eq_mass_mul_normalize A

/-- If a measurable set has probability greater than twice the two-set
concentration threshold, one point of the set is far from one transformed
copy in each of two prescribed orthogonal directions. -/
theorem three_far_transforms (h : ℕ) (hh : 0 < h)
    (A : Set (Erdos615.Construction.Sphere h)) (hA : MeasurableSet A)
    (q D : ℝ) (hq0 : 0 ≤ q) (hD : 1 ≤ D)
    (hpow : (D / 2) ^ h < q)
    (hlarge : 2 * q <
      (Erdos615.Construction.sphereProbability h hh A : ℝ))
    (e₁ e₂ : EuclideanSpace ℝ (Fin h) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin h)) :
    ∃ a₀ ∈ A, ∃ a₁ ∈ A, ∃ a₂ ∈ A,
      D < dist a₀ (realSphereEquiv e₁ a₁) ∧
      D < dist a₀ (realSphereEquiv e₂ a₂) := by
  let P := Erdos615.Construction.sphereProbability h hh
  let B₁ : Set (Erdos615.Construction.Sphere h) :=
    (realSphereEquiv e₁.symm) ⁻¹' A
  let B₂ : Set (Erdos615.Construction.Sphere h) :=
    (realSphereEquiv e₂.symm) ⁻¹' A
  have hB₁ : MeasurableSet B₁ := by
    apply hA.preimage
    exact ((e₁.symm.continuous.comp continuous_subtype_val).subtype_mk _).measurable
  have hB₂ : MeasurableSet B₂ := by
    apply hA.preimage
    exact ((e₂.symm.continuous.comp continuous_subtype_val).subtype_mk _).measurable
  have hPB₁ : P B₁ = P A := by
    exact sphereProbability_preimage_linearIsometry h hh e₁.symm A hA
  have hPB₂ : P B₂ = P A := by
    exact sphereProbability_preimage_linearIsometry h hh e₂.symm A hA
  let Bad₁ : Set (Erdos615.Construction.Sphere h) :=
    A ∩ ⋂ b : B₁, Metric.closedBall (b : Erdos615.Construction.Sphere h) D
  let Bad₂ : Set (Erdos615.Construction.Sphere h) :=
    A ∩ ⋂ b : B₂, Metric.closedBall (b : Erdos615.Construction.Sphere h) D
  have hBad₁ : MeasurableSet Bad₁ := by
    exact hA.inter (isClosed_iInter fun _ => Metric.isClosed_closedBall).measurableSet
  have hBad₂ : MeasurableSet Bad₂ := by
    exact hA.inter (isClosed_iInter fun _ => Metric.isClosed_closedBall).measurableSet
  have hqA : q < (P A : ℝ) := by linarith
  have hBad₁q : (P Bad₁ : ℝ) ≤ q := by
    by_contra hn
    have hqBad : q < (P Bad₁ : ℝ) := lt_of_not_ge hn
    have hqB₁ : q < (P B₁ : ℝ) := by
      rw [hPB₁]
      exact hqA
    obtain ⟨a, haBad, b, hbB, hab⟩ := sphereProbability_two_set_far
      h hh Bad₁ B₁ hBad₁ hB₁ D q hD hq0 hpow hqBad hqB₁
    have hle : dist a b ≤ D := by
      exact Metric.mem_closedBall.mp
        (Set.mem_iInter.mp haBad.2 ⟨b, hbB⟩)
    exact (not_lt_of_ge hle) hab
  have hBad₂q : (P Bad₂ : ℝ) ≤ q := by
    by_contra hn
    have hqBad : q < (P Bad₂ : ℝ) := lt_of_not_ge hn
    have hqB₂ : q < (P B₂ : ℝ) := by
      rw [hPB₂]
      exact hqA
    obtain ⟨a, haBad, b, hbB, hab⟩ := sphereProbability_two_set_far
      h hh Bad₂ B₂ hBad₂ hB₂ D q hD hq0 hpow hqBad hqB₂
    have hle : dist a b ≤ D := by
      exact Metric.mem_closedBall.mp
        (Set.mem_iInter.mp haBad.2 ⟨b, hbB⟩)
    exact (not_lt_of_ge hle) hab
  have hnot : ¬A ⊆ Bad₁ ∪ Bad₂ := by
    intro hsub
    have hmono : P A ≤ P (Bad₁ ∪ Bad₂) := P.apply_mono hsub
    have hunion : P (Bad₁ ∪ Bad₂) ≤ P Bad₁ + P Bad₂ := P.apply_union_le
    have hmonoR : (P A : ℝ) ≤ (P (Bad₁ ∪ Bad₂) : ℝ) := by exact_mod_cast hmono
    have hunionR : (P (Bad₁ ∪ Bad₂) : ℝ) ≤
        (P Bad₁ : ℝ) + (P Bad₂ : ℝ) := by exact_mod_cast hunion
    linarith
  obtain ⟨a₀, ha₀A, ha₀bad⟩ := Set.not_subset.mp hnot
  have ha₀bad₁ : a₀ ∉ Bad₁ := by
    intro ha
    exact ha₀bad (Or.inl ha)
  have ha₀bad₂ : a₀ ∉ Bad₂ := by
    intro ha
    exact ha₀bad (Or.inr ha)
  have hex₁ : ∃ b : B₁, D < dist a₀ (b : Erdos615.Construction.Sphere h) := by
    by_contra hn
    push Not at hn
    apply ha₀bad₁
    refine ⟨ha₀A, Set.mem_iInter.mpr ?_⟩
    intro b
    exact Metric.mem_closedBall.mpr (hn b)
  have hex₂ : ∃ b : B₂, D < dist a₀ (b : Erdos615.Construction.Sphere h) := by
    by_contra hn
    push Not at hn
    apply ha₀bad₂
    refine ⟨ha₀A, Set.mem_iInter.mpr ?_⟩
    intro b
    exact Metric.mem_closedBall.mpr (hn b)
  obtain ⟨b₁, hb₁⟩ := hex₁
  obtain ⟨b₂, hb₂⟩ := hex₂
  let a₁ : Erdos615.Construction.Sphere h := realSphereEquiv e₁.symm b₁
  let a₂ : Erdos615.Construction.Sphere h := realSphereEquiv e₂.symm b₂
  have ha₁A : a₁ ∈ A := b₁.property
  have ha₂A : a₂ ∈ A := b₂.property
  refine ⟨a₀, ha₀A, a₁, ha₁A, a₂, ha₂A, ?_, ?_⟩
  · have heq : realSphereEquiv e₁ a₁ = b₁ := by
      simp [a₁, realSphereEquiv]
    simpa [heq] using hb₁
  · have heq : realSphereEquiv e₂ a₂ = b₂ := by
      simp [a₂, realSphereEquiv]
    simpa [heq] using hb₂

/-! ## Transporting the concentration output back to the complex sphere -/

/-- The real coordinate sphere associated with `complexRealBasis` is
isometric to the complex sphere used by the graph construction. -/
noncomputable def complexOfRealSphere (k : ℕ)
    (x : Erdos615.Construction.Sphere ((k + 1) * 2)) : ComplexSphere k :=
  ⟨(complexRealBasis k).repr.symm x, by
    simpa [ComplexSphere, Erdos615.Construction.Sphere, Metric.mem_sphere,
      dist_zero_right] using x.property⟩

@[simp] theorem complexOfRealSphere_coe (k : ℕ)
    (x : Erdos615.Construction.Sphere ((k + 1) * 2)) :
    ((complexOfRealSphere k x : ComplexSphere k) :
      EuclideanSpace ℂ (Fin (k + 1))) = (complexRealBasis k).repr.symm x := rfl

theorem dist_complexOfRealSphere (k : ℕ)
    (x y : Erdos615.Construction.Sphere ((k + 1) * 2)) :
    dist (complexOfRealSphere k x) (complexOfRealSphere k y) = dist x y := by
  change dist ((complexRealBasis k).repr.symm (x :
      EuclideanSpace ℝ (Fin ((k + 1) * 2))))
    ((complexRealBasis k).repr.symm (y :
      EuclideanSpace ℝ (Fin ((k + 1) * 2)))) = dist x y
  simp [dist_eq_norm, Subtype.dist_eq, ← map_sub]

/-- On a unit sphere, being very close to the antipode of `y` forces being
close to `y` itself after the sign is removed. -/
theorem close_of_far_neg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y : E} {D e : ℝ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hD : 0 ≤ D) (he : 0 ≤ e) (hgap : 4 - D ^ 2 < e ^ 2)
    (hfar : D < dist x (-y)) : dist x y < e := by
  have hfar' : D < ‖x + y‖ := by
    simpa [dist_eq_norm] using hfar
  have hfarSq : D ^ 2 < ‖x + y‖ ^ 2 :=
    (sq_lt_sq₀ hD (norm_nonneg _)).2 hfar'
  have hpar : ‖x - y‖ ^ 2 + ‖x + y‖ ^ 2 = 4 := by
    rw [norm_sub_sq_real, norm_add_sq_real, hx, hy]
    ring
  have hcloseSq : ‖x - y‖ ^ 2 < e ^ 2 := by
    nlinarith
  have hclose : ‖x - y‖ < e :=
    (sq_lt_sq₀ (norm_nonneg _) he).1 hcloseSq
  simpa [dist_eq_norm] using hclose

@[simp] theorem norm_neg_rho : ‖-rho‖ = 1 := by simp

@[simp] theorem norm_neg_rho_sq : ‖-(rho ^ 2)‖ = 1 := by simp [norm_rho]

/-- The two negative order-three rotations used by the antipodal
concentration argument. -/
noncomputable def negRhoRotation (k : ℕ) :
    EuclideanSpace ℝ (Fin ((k + 1) * 2)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin ((k + 1) * 2)) :=
  realCoordinateRotation k (-rho) norm_neg_rho

noncomputable def negRhoSqRotation (k : ℕ) :
    EuclideanSpace ℝ (Fin ((k + 1) * 2)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin ((k + 1) * 2)) :=
  realCoordinateRotation k (-(rho ^ 2)) norm_neg_rho_sq

@[simp] theorem complexOfRealSphere_negRhoRotation (k : ℕ)
    (x : Erdos615.Construction.Sphere ((k + 1) * 2)) :
    ((complexOfRealSphere k
        (realSphereEquiv (negRhoRotation k) x) : ComplexSphere k) :
      EuclideanSpace ℂ (Fin (k + 1))) =
      -(rho • ((complexOfRealSphere k x : ComplexSphere k) :
        EuclideanSpace ℂ (Fin (k + 1)))) := by
  simp [negRhoRotation, complexOfRealSphere]

@[simp] theorem complexOfRealSphere_negRhoSqRotation (k : ℕ)
    (x : Erdos615.Construction.Sphere ((k + 1) * 2)) :
    ((complexOfRealSphere k
        (realSphereEquiv (negRhoSqRotation k) x) : ComplexSphere k) :
      EuclideanSpace ℂ (Fin (k + 1))) =
      -(rho ^ 2 • ((complexOfRealSphere k x : ComplexSphere k) :
        EuclideanSpace ℂ (Fin (k + 1)))) := by
  simp [negRhoSqRotation, complexOfRealSphere]

theorem norm_one_sub_rho : ‖(1 : ℂ) - rho‖ = Real.sqrt 3 := by
  rw [Complex.norm_def]
  congr 1
  simp [rho, Complex.normSq_apply]
  nlinarith [sqrt_three_sq]

theorem norm_one_sub_rho_sq : ‖(1 : ℂ) - rho ^ 2‖ = Real.sqrt 3 := by
  rw [rho_sq, Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply]
  nlinarith [sqrt_three_sq]

/-! ## Geometric graph definitions -/

/-- Two sphere points are inner-adjacent in the oriented relation when one
is close to one of the two nontrivial order-three rotations of the other. -/
def approxRotation {k : ℕ} (d : ℝ) (h : Fin 2)
    (x y : ComplexSphere k) : Prop :=
  ‖(x : EuclideanSpace ℂ (Fin (k + 1))) -
      rho ^ (h.1 + 1) • (y : EuclideanSpace ℂ (Fin (k + 1)))‖ ≤ d

def rotationClose {k : ℕ} (d : ℝ) (x y : ComplexSphere k) : Prop :=
  ∃ h : Fin 2, approxRotation d h x y

/-- The real partition centers, transported to the complex sphere. -/
noncomputable def complexCenter (k : ℕ) (r : ℝ) (hr : 0 < r)
    (i : Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr)) :
    ComplexSphere k :=
  complexOfRealSphere k
    (Erdos615.Construction.center ((k + 1) * 2) r hr i)

/-- A unit real normal vector representing one of the three imaginary-part
functionals `Im (rho^j ⟨x,y⟩)`. -/
noncomputable def complexStripNormal (k : ℕ) (j : Fin 3)
    (x : ComplexSphere k) : EuclideanSpace ℝ (Fin ((k + 1) * 2)) :=
  (complexRealBasis k).repr
    ((Complex.I * star (rho ^ j.1)) •
      (x : EuclideanSpace ℂ (Fin (k + 1))))

theorem complexStripNormal_norm (k : ℕ) (j : Fin 3)
    (x : ComplexSphere k) : ‖complexStripNormal k j x‖ = 1 := by
  have hx : ‖(x : EuclideanSpace ℂ (Fin (k + 1)))‖ = 1 := by
    simpa [ComplexSphere, Metric.mem_sphere, dist_zero_right] using x.property
  simp [complexStripNormal, norm_smul, norm_mul, norm_rho, hx]

theorem complexStripFunctional (k : ℕ) (j : Fin 3)
    (x : ComplexSphere k)
    (y : Erdos615.Construction.Sphere ((k + 1) * 2)) :
    inner ℝ (complexStripNormal k j x)
        (y : EuclideanSpace ℝ (Fin ((k + 1) * 2))) =
      (rho ^ j.1 * inner ℂ
        (x : EuclideanSpace ℂ (Fin (k + 1)))
        ((complexOfRealSphere k y : ComplexSphere k) :
          EuclideanSpace ℂ (Fin (k + 1)))).im := by
  calc
    inner ℝ (complexStripNormal k j x)
        (y : EuclideanSpace ℝ (Fin ((k + 1) * 2))) =
      inner ℝ
        ((Complex.I * star (rho ^ j.1)) •
          (x : EuclideanSpace ℂ (Fin (k + 1))))
        ((complexRealBasis k).repr.symm y) := by
          exact (complexRealBasis k).repr.inner_map_eq_flip _ _
    _ = (inner ℂ
        ((Complex.I * star (rho ^ j.1)) •
          (x : EuclideanSpace ℂ (Fin (k + 1))))
        ((complexRealBasis k).repr.symm y)).re :=
      by
        simp only [PiLp.inner_apply, Complex.inner, RCLike.inner_apply]
        exact (map_sum Complex.reCLM (fun i : Fin (k + 1) =>
          ((complexRealBasis k).repr.symm y) i *
            star (((Complex.I * star (rho ^ j.1)) •
              (x : EuclideanSpace ℂ (Fin (k + 1)))) i)) Finset.univ).symm
    _ = _ := by
      rw [inner_smul_left]
      simp [Complex.mul_re, Complex.mul_im]

/-- Each complex strip has the same elementary spherical-measure bound as a
real equatorial strip. -/
theorem sphereProbability_complex_strip (k : ℕ) (j : Fin 3)
    (x : ComplexSphere k) (s : ℝ) (hs : 0 ≤ s) :
    (Erdos615.Construction.sphereProbability ((k + 1) * 2) (by omega)
      {y | |(rho ^ j.1 * inner ℂ
        (x : EuclideanSpace ℂ (Fin (k + 1)))
        ((complexOfRealSphere k y : ComplexSphere k) :
          EuclideanSpace ℂ (Fin (k + 1)))).im| ≤ s} : ℝ) ≤
      2 * s * Real.sqrt ((((k + 1) * 2 : ℕ) : ℝ)) := by
  simpa only [complexStripFunctional] using
    Erdos615.Construction.sphereProbability_strip_bound ((k + 1) * 2)
      (by omega) (complexStripNormal k j x)
      (complexStripNormal_norm k j x) s hs

/-! The cross-edge sector predicates are declared here because the strip
estimate and the subsequent finite averaging use them. -/

/-- The closed angular sector from angle `0` to angle `2π/3`, represented
as the intersection of two half-planes. -/
def inMainSector (a : ℂ) : Prop :=
  0 ≤ a.im ∧ 0 ≤ (-rho ^ 2 * a).im

/-- The inner product stays away from the three boundary lines of the
rotated sectors. -/
def awayFromStrips (t : ℝ) (a : ℂ) : Prop :=
  ∀ h : Fin 3, t ≤ |(rho ^ h.1 * a).im|

/-- Cross adjacency between one point in each tagged part. -/
def crossClose {k : ℕ} (t : ℝ) (x y : ComplexSphere k) : Prop :=
  inMainSector
      (inner ℂ (x : EuclideanSpace ℂ (Fin (k + 1)))
        (y : EuclideanSpace ℂ (Fin (k + 1)))) ∧
    awayFromStrips t
      (inner ℂ (x : EuclideanSpace ℂ (Fin (k + 1)))
        (y : EuclideanSpace ℂ (Fin (k + 1))))

/-- Cells whose centers avoid all three strips relative to a fixed first
center. -/
noncomputable def robustSecondCells (k : ℕ) (r : ℝ) (hr : 0 < r)
    (t : ℝ) (i : Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr)) :
    Finset (Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr)) :=
  Finset.univ.filter fun j ↦ awayFromStrips t
    (inner ℂ
      ((complexCenter k r hr i : ComplexSphere k) :
        EuclideanSpace ℂ (Fin (k + 1)))
      ((complexCenter k r hr j : ComplexSphere k) :
        EuclideanSpace ℂ (Fin (k + 1))))

/-- For a fixed first center, almost all of the second-sphere weight avoids
the three strips.  The loss is the sum of the three real strip bounds. -/
theorem sum_robustSecondCells_weight_lower (k : ℕ) (r t : ℝ)
    (hr : 0 < r) (hrt : r < t)
    (i : Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr)) :
    1 - 12 * t * Real.sqrt ((((k + 1) * 2 : ℕ) : ℝ)) ≤
      ∑ j ∈ robustSecondCells k r hr t i,
        Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr j := by
  let h : ℕ := (k + 1) * 2
  have hh : 0 < h := by simp [h]
  let P := Erdos615.Construction.sphereProbability h hh
  let x : ComplexSphere k := complexCenter k r hr i
  let Strip (q : Fin 3) : Set (Erdos615.Construction.Sphere h) :=
    {y | |(rho ^ q.1 * inner ℂ
      (x : EuclideanSpace ℂ (Fin (k + 1)))
      ((complexOfRealSphere k y : ComplexSphere k) :
        EuclideanSpace ℂ (Fin (k + 1)))).im| ≤ 2 * t}
  let Bad : Set (Erdos615.Construction.Sphere h) :=
    Strip 0 ∪ Strip 1 ∪ Strip 2
  have ht : 0 < t := hr.trans hrt
  have hStrip (q : Fin 3) : MeasurableSet (Strip q) := by
    dsimp only [Strip]
    measurability
  have hBad : MeasurableSet Bad :=
    ((hStrip 0).union (hStrip 1)).union (hStrip 2)
  have hstripBound (q : Fin 3) :
      (P (Strip q) : ℝ) ≤ 4 * t * Real.sqrt h := by
    convert sphereProbability_complex_strip k q x (2 * t) (by positivity) using 1 <;>
      simp only [P, Strip, h, x] <;> ring
  have hBadNN : P Bad ≤ P (Strip 0) + P (Strip 1) + P (Strip 2) := by
    calc
      P Bad ≤ P (Strip 0 ∪ Strip 1) + P (Strip 2) := by
        simpa [Bad] using P.apply_union_le (s₁ := Strip 0 ∪ Strip 1)
          (s₂ := Strip 2)
      _ ≤ (P (Strip 0) + P (Strip 1)) + P (Strip 2) := by
        gcongr
        exact P.apply_union_le
      _ = P (Strip 0) + P (Strip 1) + P (Strip 2) := by ring
  have hBadReal : (P Bad : ℝ) ≤ 12 * t * Real.sqrt h := by
    have H : (P Bad : ℝ) ≤
        (P (Strip 0) : ℝ) + (P (Strip 1) : ℝ) + (P (Strip 2) : ℝ) := by
      exact_mod_cast hBadNN
    linarith [hstripBound 0, hstripBound 1, hstripBound 2]
  have hcompENN : (P : Measure (Erdos615.Construction.Sphere h)) Bad +
      (P : Measure (Erdos615.Construction.Sphere h)) Badᶜ = 1 := by
    simpa using
      (measure_add_measure_compl (μ := (P : Measure (Erdos615.Construction.Sphere h))) hBad)
  have hcompNN : P Bad + P Badᶜ = 1 := by
    apply ENNReal.coe_injective
    simpa [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hcompENN
  have hcompReal : (P Bad : ℝ) + (P Badᶜ : ℝ) = 1 := by
    exact_mod_cast hcompNN
  have hgoodProb : 1 - 12 * t * Real.sqrt h ≤ (P Badᶜ : ℝ) := by
    linarith
  have hsubset : Badᶜ ⊆ Erdos615.Construction.cellUnion h r hr
      (robustSecondCells k r hr t i) := by
    intro y hy
    have hyBad : y ∉ Bad := hy
    have hyall : y ∈ ⋃ j : Fin (Erdos615.Construction.netCard h r hr),
        Erdos615.Construction.cell h r hr j := by
      rw [Erdos615.Construction.iUnion_cell h r hr]
      trivial
    rcases Set.mem_iUnion.mp hyall with ⟨j, hycell⟩
    have hycenter := Erdos615.Construction.cell_subset_ball h r hr j hycell
    rw [Metric.mem_closedBall] at hycenter
    have haway : awayFromStrips t
        (inner ℂ
          ((complexCenter k r hr i : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))
          ((complexCenter k r hr j : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))) := by
      intro q
      have hyNot : ¬|(rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexOfRealSphere k y : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im| ≤ 2 * t := by
        intro H
        apply hyBad
        fin_cases q
        · exact Or.inl (Or.inl H)
        · exact Or.inl (Or.inr H)
        · exact Or.inr H
      have hyLarge : 2 * t < |(rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexOfRealSphere k y : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im| := lt_of_not_ge hyNot
      have hproj : |(rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexCenter k r hr j : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im -
          (rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexOfRealSphere k y : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im| ≤ r := by
        have hc := complexStripFunctional k q x
          (Erdos615.Construction.center h r hr j)
        have hyf := complexStripFunctional k q x y
        change inner ℝ (complexStripNormal k q x)
            (Erdos615.Construction.center h r hr j :
              EuclideanSpace ℝ (Fin h)) = _ at hc
        change |(rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexOfRealSphere k (Erdos615.Construction.center h r hr j) :
            ComplexSphere k) : EuclideanSpace ℂ (Fin (k + 1)))).im -
          (rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexOfRealSphere k y : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im| ≤ r
        rw [← hc, ← hyf]
        have H := abs_real_inner_le_norm (complexStripNormal k q x)
          ((Erdos615.Construction.center h r hr j :
              EuclideanSpace ℝ (Fin h)) - (y : EuclideanSpace ℝ (Fin h)))
        rw [inner_sub_right, complexStripNormal_norm, one_mul] at H
        exact H.trans (by
          simpa only [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using hycenter)
      have habs := abs_sub_abs_le_abs_sub
        ((rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexOfRealSphere k y : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im)
        ((rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexCenter k r hr j : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im)
      have hdiff : |(rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexOfRealSphere k y : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im| -
          |(rho ^ q.1 * inner ℂ
          (x : EuclideanSpace ℂ (Fin (k + 1)))
          ((complexCenter k r hr j : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))).im| ≤ r :=
        habs.trans (by simpa [abs_sub_comm] using hproj)
      dsimp only [x] at hyLarge hdiff ⊢
      linarith
    have hj : j ∈ robustSecondCells k r hr t i := by
      simp [robustSecondCells, haway]
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hycell⟩⟩
  have hmonoNN : P Badᶜ ≤
      P (Erdos615.Construction.cellUnion h r hr
        (robustSecondCells k r hr t i)) := P.apply_mono hsubset
  have hmonoReal : (P Badᶜ : ℝ) ≤
      (P (Erdos615.Construction.cellUnion h r hr
        (robustSecondCells k r hr t i)) : ℝ) := by
    exact_mod_cast hmonoNN
  have hw := Erdos615.Construction.sum_weight_finset_eq_probability
    h r hh hr (robustSecondCells k r hr t i)
  calc
    1 - 12 * t * Real.sqrt ((((k + 1) * 2 : ℕ) : ℝ)) =
        1 - 12 * t * Real.sqrt h := by simp [h]
    _ ≤ (P Badᶜ : ℝ) := hgoodProb
    _ ≤ (P (Erdos615.Construction.cellUnion h r hr
        (robustSecondCells k r hr t i)) : ℝ) := hmonoReal
    _ = ∑ j ∈ robustSecondCells k r hr t i,
        Erdos615.Construction.weight h r hh hr j := hw.symm

/-- Coordinatewise multiplication by `rho^q` on the complex sphere. -/
noncomputable def rhoRotateSphere (k : ℕ) (q : Fin 3) (x : ComplexSphere k) :
    ComplexSphere k :=
  ⟨rho ^ q.1 • (x : EuclideanSpace ℂ (Fin (k + 1))), by
    have hx : ‖(x : EuclideanSpace ℂ (Fin (k + 1)))‖ = 1 := by
      simpa [ComplexSphere, Metric.mem_sphere, dist_zero_right] using x.property
    simpa [ComplexSphere, Metric.mem_sphere, dist_zero_right, norm_smul,
      norm_rho, hx]⟩

@[simp] theorem rhoRotateSphere_coe (k : ℕ) (q : Fin 3)
    (x : ComplexSphere k) :
    ((rhoRotateSphere k q x : ComplexSphere k) :
      EuclideanSpace ℂ (Fin (k + 1))) =
      rho ^ q.1 • (x : EuclideanSpace ℂ (Fin (k + 1))) := rfl

theorem rotationClose_rhoRotate {k : ℕ} {d : ℝ} (q : Fin 3)
    {x y : ComplexSphere k} (hxy : rotationClose d x y) :
    rotationClose d (rhoRotateSphere k q x) (rhoRotateSphere k q y) := by
  obtain ⟨j, hj⟩ := hxy
  refine ⟨j, ?_⟩
  change ‖rho ^ q.1 • (x : EuclideanSpace ℂ (Fin (k + 1))) -
      rho ^ (j.1 + 1) •
        (rho ^ q.1 • (y : EuclideanSpace ℂ (Fin (k + 1))))‖ ≤ d
  rw [show rho ^ q.1 • (x : EuclideanSpace ℂ (Fin (k + 1))) -
      rho ^ (j.1 + 1) •
        (rho ^ q.1 • (y : EuclideanSpace ℂ (Fin (k + 1)))) =
      rho ^ q.1 • ((x : EuclideanSpace ℂ (Fin (k + 1))) -
        rho ^ (j.1 + 1) • (y : EuclideanSpace ℂ (Fin (k + 1)))) by
          rw [smul_sub, smul_smul, smul_smul]
          congr 2
          ring,
    norm_smul, norm_pow, norm_rho, one_pow, one_mul]
  exact hj

/-- The three closed sectors of angle `2π/3` cover the complex plane. -/
theorem three_main_sectors_cover (a : ℂ) :
    inMainSector a ∨ inMainSector (rho * a) ∨
      inMainSector (rho ^ 2 * a) := by
  have hsum : a.im + (rho * a).im + (rho ^ 2 * a).im = 0 := by
    have H := congrArg Complex.im
      (show (1 + rho + rho ^ 2) * a = 0 by rw [one_add_rho_add_sq, zero_mul])
    simpa [add_mul] using H
  have hsec₀ : (-rho ^ 2 * a).im = a.im + (rho * a).im := by
    have hc : -rho ^ 2 = 1 + rho := by
      linear_combination -one_add_rho_add_sq
    rw [hc, add_mul]
    simp
  have hsec₁ : (-rho ^ 2 * (rho * a)).im = -a.im := by
    have hc : (-rho ^ 2) * rho = -1 := by
      rw [neg_mul, show rho ^ 2 * rho = rho ^ 3 by ring, rho_cube]
    rw [← mul_assoc, hc]
    simp
  have hsec₂ : (-rho ^ 2 * (rho ^ 2 * a)).im = -(rho * a).im := by
    have hc : (-rho ^ 2) * rho ^ 2 = -rho := by
      rw [neg_mul, show rho ^ 2 * rho ^ 2 = rho ^ 3 * rho by ring, rho_cube,
        one_mul]
    rw [← mul_assoc, hc]
    simp
  by_cases ha : 0 ≤ a.im
  · by_cases hs : 0 ≤ (-rho ^ 2 * a).im
    · exact Or.inl ⟨ha, hs⟩
    · right
      right
      rw [inMainSector, hsec₂]
      rw [hsec₀] at hs
      constructor <;> linarith
  · have ha' : a.im < 0 := lt_of_not_ge ha
    by_cases hr : 0 ≤ (rho * a).im
    · right
      left
      rw [inMainSector, hsec₁]
      exact ⟨hr, by linarith⟩
    · right
      right
      have hr' : (rho * a).im < 0 := lt_of_not_ge hr
      rw [inMainSector, hsec₂]
      constructor <;> linarith

/-- Avoiding the three boundary strips is invariant under the three rotations. -/
theorem awayFromStrips_rho_pow {t : ℝ} {a : ℂ} (q : Fin 3)
    (ha : awayFromStrips t a) : awayFromStrips t (rho ^ q.1 * a) := by
  intro j
  fin_cases q <;> fin_cases j
  · simpa using ha 0
  · simpa using ha 1
  · simpa using ha 2
  · simpa [mul_assoc] using ha 1
  · norm_num only [pow_one] at ⊢
    change t ≤ |(rho * (rho * a)).im|
    rw [show rho * (rho * a) = rho ^ 2 * a by ring]
    exact ha 2
  · norm_num only [pow_one] at ⊢
    change t ≤ |(rho ^ 2 * (rho * a)).im|
    rw [show rho ^ 2 * (rho * a) = a by
      calc
        rho ^ 2 * (rho * a) = rho ^ 3 * a := by ring
        _ = a := by rw [rho_cube, one_mul]]
    simpa only [Fin.val_zero 3, pow_zero, one_mul] using ha 0
  · simpa [mul_assoc] using ha 2
  · norm_num only [pow_one] at ⊢
    change t ≤ |(rho * (rho ^ 2 * a)).im|
    rw [show rho * (rho ^ 2 * a) = a by
      calc
        rho * (rho ^ 2 * a) = rho ^ 3 * a := by ring
        _ = a := by rw [rho_cube, one_mul]]
    simpa only [Fin.val_zero 3, pow_zero, one_mul] using ha 0
  · change t ≤ |(rho ^ 2 * (rho ^ 2 * a)).im|
    rw [show rho ^ 2 * (rho ^ 2 * a) = rho * a by
      calc
        rho ^ 2 * (rho ^ 2 * a) = rho ^ 3 * (rho * a) := by ring
        _ = rho * a := by rw [rho_cube, one_mul]]
    simpa only [Fin.val_one 1, pow_one] using ha 1

/-- The weighted fraction of cross pairs selected by a fixed global rotation
of the second part. -/
noncomputable def crossWeight (k : ℕ) (r : ℝ) (hr : 0 < r)
    (t : ℝ) (q : Fin 3) : ℝ :=
  ∑ i : Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr),
    Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr i *
      ∑ j : Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr),
        if crossClose t (complexCenter k r hr i)
            (rhoRotateSphere k q (complexCenter k r hr j)) then
          Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr j
        else 0

/-- One of the three global rotations supplies at least one quarter of all
weighted cross pairs, provided the three strip losses total at most `1/4`. -/
theorem exists_crossWeight_ge_quarter (k : ℕ) (r t : ℝ)
    (hr : 0 < r) (hrt : r < t)
    (hstrip : 12 * t * Real.sqrt ((((k + 1) * 2 : ℕ) : ℝ)) ≤ 1 / 4) :
    ∃ q : Fin 3, 1 / 4 ≤ crossWeight k r hr t q := by
  let I := Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr)
  let wt : I → ℝ := fun i ↦
    Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr i
  have hwt (i : I) : 0 ≤ wt i :=
    Erdos615.Construction.weight_nonneg ((k + 1) * 2) r (by omega) hr i
  have hwtsum : ∑ i : I, wt i = 1 :=
    Erdos615.Construction.sum_weight ((k + 1) * 2) r (by omega) hr
  let robust : ℝ := ∑ i : I, wt i *
    ∑ j ∈ robustSecondCells k r hr t i, wt j
  have hrobust : 3 / 4 ≤ robust := by
    have H : 1 - 12 * t * Real.sqrt ((((k + 1) * 2 : ℕ) : ℝ)) ≤ robust := by
      calc
        1 - 12 * t * Real.sqrt ((((k + 1) * 2 : ℕ) : ℝ)) =
            ∑ i : I, wt i *
              (1 - 12 * t * Real.sqrt ((((k + 1) * 2 : ℕ) : ℝ))) := by
                rw [← Finset.sum_mul, hwtsum, one_mul]
        _ ≤ ∑ i : I, wt i *
            ∑ j ∈ robustSecondCells k r hr t i, wt j := by
              exact Finset.sum_le_sum fun i _ ↦
                mul_le_mul_of_nonneg_left
                  (sum_robustSecondCells_weight_lower k r t hr hrt i) (hwt i)
        _ = robust := rfl
    linarith
  have hpair (i j : I)
      (hj : j ∈ robustSecondCells k r hr t i) :
      wt i * wt j ≤ ∑ q : Fin 3,
        if crossClose t (complexCenter k r hr i)
            (rhoRotateSphere k q (complexCenter k r hr j)) then
          wt i * wt j else 0 := by
    have haway : awayFromStrips t
        (inner ℂ
          ((complexCenter k r hr i : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))
          ((complexCenter k r hr j : ComplexSphere k) :
            EuclideanSpace ℂ (Fin (k + 1)))) := by
      simpa [robustSecondCells] using (Finset.mem_filter.mp hj).2
    let a : ℂ := inner ℂ
      ((complexCenter k r hr i : ComplexSphere k) :
        EuclideanSpace ℂ (Fin (k + 1)))
      ((complexCenter k r hr j : ComplexSphere k) :
        EuclideanSpace ℂ (Fin (k + 1)))
    obtain hsector | hsector | hsector := three_main_sectors_cover a
    · have hc : crossClose t (complexCenter k r hr i)
          (rhoRotateSphere k 0 (complexCenter k r hr j)) := by
        refine ⟨?_, ?_⟩
        · simpa [a, inner_smul_right]
        · simpa [a, inner_smul_right] using awayFromStrips_rho_pow 0 haway
      have hnonneg : 0 ≤ wt i * wt j := mul_nonneg (hwt i) (hwt j)
      calc
        wt i * wt j = if crossClose t (complexCenter k r hr i)
            (rhoRotateSphere k 0 (complexCenter k r hr j)) then
          wt i * wt j else 0 := (if_pos hc).symm
        _ ≤ ∑ q : Fin 3, if crossClose t (complexCenter k r hr i)
              (rhoRotateSphere k q (complexCenter k r hr j)) then
            wt i * wt j else 0 := Finset.single_le_sum
              (s := Finset.univ) (a := (0 : Fin 3))
              (f := fun q : Fin 3 ↦ if crossClose t (complexCenter k r hr i)
                (rhoRotateSphere k q (complexCenter k r hr j)) then
                  wt i * wt j else 0)
              (fun q _ ↦ by
                by_cases hq : crossClose t (complexCenter k r hr i)
                  (rhoRotateSphere k q (complexCenter k r hr j))
                · rw [if_pos hq]
                  exact hnonneg
                · rw [if_neg hq]) (Finset.mem_univ 0)
    · have hc : crossClose t (complexCenter k r hr i)
          (rhoRotateSphere k 1 (complexCenter k r hr j)) := by
        refine ⟨?_, ?_⟩
        · simpa [a, inner_smul_right]
        · simpa [a, inner_smul_right] using awayFromStrips_rho_pow 1 haway
      have hnonneg : 0 ≤ wt i * wt j := mul_nonneg (hwt i) (hwt j)
      calc
        wt i * wt j = if crossClose t (complexCenter k r hr i)
            (rhoRotateSphere k 1 (complexCenter k r hr j)) then
          wt i * wt j else 0 := (if_pos hc).symm
        _ ≤ ∑ q : Fin 3, if crossClose t (complexCenter k r hr i)
              (rhoRotateSphere k q (complexCenter k r hr j)) then
            wt i * wt j else 0 := Finset.single_le_sum
              (s := Finset.univ) (a := (1 : Fin 3))
              (f := fun q : Fin 3 ↦ if crossClose t (complexCenter k r hr i)
                (rhoRotateSphere k q (complexCenter k r hr j)) then
                  wt i * wt j else 0)
              (fun q _ ↦ by
                by_cases hq : crossClose t (complexCenter k r hr i)
                  (rhoRotateSphere k q (complexCenter k r hr j))
                · rw [if_pos hq]
                  exact hnonneg
                · rw [if_neg hq]) (Finset.mem_univ 1)
    · have hc : crossClose t (complexCenter k r hr i)
          (rhoRotateSphere k 2 (complexCenter k r hr j)) := by
        refine ⟨?_, ?_⟩
        · simpa [a, inner_smul_right]
        · simpa [a, inner_smul_right] using awayFromStrips_rho_pow 2 haway
      have hnonneg : 0 ≤ wt i * wt j := mul_nonneg (hwt i) (hwt j)
      calc
        wt i * wt j = if crossClose t (complexCenter k r hr i)
            (rhoRotateSphere k 2 (complexCenter k r hr j)) then
          wt i * wt j else 0 := (if_pos hc).symm
        _ ≤ ∑ q : Fin 3, if crossClose t (complexCenter k r hr i)
              (rhoRotateSphere k q (complexCenter k r hr j)) then
            wt i * wt j else 0 := Finset.single_le_sum
              (s := Finset.univ) (a := (2 : Fin 3))
              (f := fun q : Fin 3 ↦ if crossClose t (complexCenter k r hr i)
                (rhoRotateSphere k q (complexCenter k r hr j)) then
                  wt i * wt j else 0)
              (fun q _ ↦ by
                by_cases hq : crossClose t (complexCenter k r hr i)
                  (rhoRotateSphere k q (complexCenter k r hr j))
                · rw [if_pos hq]
                  exact hnonneg
                · rw [if_neg hq]) (Finset.mem_univ 2)
  have hrobustCross : robust ≤ ∑ q : Fin 3, crossWeight k r hr t q := by
    calc
      robust = ∑ i : I, ∑ j ∈ robustSecondCells k r hr t i,
          wt i * wt j := by
            simp only [robust, Finset.mul_sum]
      _ ≤ ∑ i : I, ∑ j ∈ robustSecondCells k r hr t i,
          ∑ q : Fin 3, if crossClose t (complexCenter k r hr i)
              (rhoRotateSphere k q (complexCenter k r hr j)) then
            wt i * wt j else 0 := by
              exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j hj ↦ hpair i j hj
      _ ≤ ∑ i : I, ∑ j : I,
          ∑ q : Fin 3, if crossClose t (complexCenter k r hr i)
              (rhoRotateSphere k q (complexCenter k r hr j)) then
            wt i * wt j else 0 := by
              apply Finset.sum_le_sum
              intro i hi
              apply Finset.sum_le_univ_sum_of_nonneg
              intro j
              exact Finset.sum_nonneg fun q _ ↦ by
                split_ifs <;> simp_all [mul_nonneg (hwt i) (hwt j)]
      _ = ∑ q : Fin 3, crossWeight k r hr t q := by
              simp only [crossWeight, wt, I]
              rw [show (∑ i : I, ∑ j : I,
                  ∑ q : Fin 3, if crossClose t (complexCenter k r hr i)
                      (rhoRotateSphere k q (complexCenter k r hr j)) then
                    wt i * wt j else 0) =
                  ∑ q : Fin 3, ∑ i : I, ∑ j : I,
                    if crossClose t (complexCenter k r hr i)
                        (rhoRotateSphere k q (complexCenter k r hr j)) then
                      wt i * wt j else 0 by
                calc
                  _ = ∑ i : I, ∑ q : Fin 3, ∑ j : I,
                      if crossClose t (complexCenter k r hr i)
                          (rhoRotateSphere k q (complexCenter k r hr j)) then
                        wt i * wt j else 0 := by
                          apply Finset.sum_congr rfl
                          intro i hi
                          rw [Finset.sum_comm]
                  _ = _ := by rw [Finset.sum_comm]]
              apply Finset.sum_congr rfl
              intro q hq
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              split_ifs <;> ring
  by_contra hn
  push Not at hn
  have hsumlt : (∑ q : Fin 3, crossWeight k r hr t q) < 3 / 4 := by
    rw [Fin.sum_univ_succ]
    norm_num [Fin.sum_univ_succ]
    linarith [hn 0, hn 1, hn 2]
  linarith

theorem rotationClose_irrefl {k : ℕ} {d : ℝ} (hd : d < Real.sqrt 3)
    (x : ComplexSphere k) : ¬rotationClose d x x := by
  rintro ⟨j, hj⟩
  have hxnorm : ‖(x : EuclideanSpace ℂ (Fin (k + 1)))‖ = 1 := by
    simpa [ComplexSphere, Metric.mem_sphere, dist_zero_right] using x.property
  have hnorm :
      ‖(x : EuclideanSpace ℂ (Fin (k + 1))) -
          rho ^ (j.1 + 1) • (x : EuclideanSpace ℂ (Fin (k + 1)))‖ =
        Real.sqrt 3 := by
    rw [show
      (x : EuclideanSpace ℂ (Fin (k + 1))) -
          rho ^ (j.1 + 1) • (x : EuclideanSpace ℂ (Fin (k + 1))) =
        ((1 : ℂ) - rho ^ (j.1 + 1)) •
          (x : EuclideanSpace ℂ (Fin (k + 1))) by module,
      norm_smul, hxnorm, mul_one]
    fin_cases j
    · norm_num
      exact norm_one_sub_rho
    · norm_num
      exact norm_one_sub_rho_sq
  change ‖(x : EuclideanSpace ℂ (Fin (k + 1))) -
      rho ^ (j.1 + 1) • (x : EuclideanSpace ℂ (Fin (k + 1)))‖ ≤ d at hj
  rw [hnorm] at hj
  linarith

theorem rotationClose_symm {k : ℕ} {d : ℝ} {x y : ComplexSphere k} :
    rotationClose d x y → rotationClose d y x := by
  rintro ⟨h, hh⟩
  fin_cases h
  · refine ⟨1, ?_⟩
    norm_num [approxRotation] at hh ⊢
    rw [show
      (y : EuclideanSpace ℂ (Fin (k + 1))) - rho ^ 2 •
          (x : EuclideanSpace ℂ (Fin (k + 1))) =
        (-rho ^ 2) •
          ((x : EuclideanSpace ℂ (Fin (k + 1))) - rho •
            (y : EuclideanSpace ℂ (Fin (k + 1)))) by
      have hcoef : (-rho ^ 2) * rho = -1 := by
        rw [neg_mul, show rho ^ 2 * rho = rho ^ 3 by ring, rho_cube]
      rw [smul_sub, smul_smul, hcoef]
      simp [sub_eq_add_neg, add_comm]]
    simpa [norm_smul, norm_rho] using hh

  · refine ⟨0, ?_⟩
    norm_num [approxRotation] at hh ⊢
    rw [show
      (y : EuclideanSpace ℂ (Fin (k + 1))) - rho •
          (x : EuclideanSpace ℂ (Fin (k + 1))) =
        (-rho) •
          ((x : EuclideanSpace ℂ (Fin (k + 1))) - rho ^ 2 •
            (y : EuclideanSpace ℂ (Fin (k + 1)))) by
      have hcoef : (-rho) * rho ^ 2 = -1 := by
        rw [neg_mul, show rho * rho ^ 2 = rho ^ 3 by ring, rho_cube]
      rw [smul_sub, smul_smul, hcoef]
      simp [sub_eq_add_neg, add_comm]]
    simpa [norm_smul, norm_rho] using hh

theorem approxRotation_zero_flip_one {k : ℕ} {d : ℝ}
    {x y : ComplexSphere k} (h : approxRotation d 0 x y) :
    approxRotation d 1 y x := by
  norm_num [approxRotation] at h ⊢
  rw [show
    (y : EuclideanSpace ℂ (Fin (k + 1))) - rho ^ 2 •
        (x : EuclideanSpace ℂ (Fin (k + 1))) =
      (-rho ^ 2) •
        ((x : EuclideanSpace ℂ (Fin (k + 1))) - rho •
          (y : EuclideanSpace ℂ (Fin (k + 1)))) by
    have hcoef : (-rho ^ 2) * rho = -1 := by
      rw [neg_mul, show rho ^ 2 * rho = rho ^ 3 by ring, rho_cube]
    rw [smul_sub, smul_smul, hcoef]
    simp [sub_eq_add_neg, add_comm]]
  simpa [norm_smul, norm_rho] using h

theorem approxRotation_one_flip_zero {k : ℕ} {d : ℝ}
    {x y : ComplexSphere k} (h : approxRotation d 1 x y) :
    approxRotation d 0 y x := by
  norm_num [approxRotation] at h ⊢
  rw [show
    (y : EuclideanSpace ℂ (Fin (k + 1))) - rho •
        (x : EuclideanSpace ℂ (Fin (k + 1))) =
      (-rho) •
        ((x : EuclideanSpace ℂ (Fin (k + 1))) - rho ^ 2 •
          (y : EuclideanSpace ℂ (Fin (k + 1)))) by
    have hcoef : (-rho) * rho ^ 2 = -1 := by
      rw [neg_mul, show rho * rho ^ 2 = rho ^ 3 by ring, rho_cube]
    rw [smul_sub, smul_smul, hcoef]
    simp [sub_eq_add_neg, add_comm]]
  simpa [norm_smul, norm_rho] using h

/-- If a union of partition cells has more than four times the spherical
concentration threshold, three of its cells have centers spanning an inner
triangle.  This is the analytic heart of the bound on triangle-free sets. -/
theorem large_cells_give_inner_triangle (k : ℕ) (r d e D : ℝ)
    (hr : 0 < r) (he : 0 ≤ e) (hD : 1 ≤ D)
    (hgap : 4 - D ^ 2 < e ^ 2) (hclose : 2 * r + 2 * e < d)
    (hdroot : d < Real.sqrt 3)
    (J : Finset (Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr)))
    (hlarge :
      4 * (D / 2) ^ ((k + 1) * 2) <
        ∑ i ∈ J, Erdos615.Construction.weight ((k + 1) * 2) r
          (by omega) hr i) :
    ∃ i₀ ∈ J, ∃ i₁ ∈ J, ∃ i₂ ∈ J,
      i₀ ≠ i₁ ∧ i₀ ≠ i₂ ∧ i₁ ≠ i₂ ∧
      rotationClose d (complexCenter k r hr i₀) (complexCenter k r hr i₁) ∧
      rotationClose d (complexCenter k r hr i₀) (complexCenter k r hr i₂) ∧
      rotationClose d (complexCenter k r hr i₁) (complexCenter k r hr i₂) := by
  let h : ℕ := (k + 1) * 2
  have hh : 0 < h := by simp [h]
  let P := Erdos615.Construction.sphereProbability h hh
  let A : Set (Erdos615.Construction.Sphere h) :=
    Erdos615.Construction.cellUnion h r hr J
  have hA : MeasurableSet A :=
    Erdos615.Construction.cellUnion_measurable h r hr J
  let b : ℝ := (D / 2) ^ h
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hbpos : 0 < b := pow_pos (by positivity) _
  have hPA : 4 * b < (P A : ℝ) := by
    have hw := Erdos615.Construction.sum_weight_finset_eq_probability
      h r hh hr J
    simpa [h, b, P, A] using hlarge.trans_eq hw
  obtain ⟨a₀, ha₀A, a₁, ha₁A, a₂, ha₂A, hfar₁, hfar₂⟩ :=
    three_far_transforms h hh A hA (2 * b) D (by positivity) hD
      (by simpa [b] using (show b < 2 * b by linarith))
      (by simpa [P] using (show 2 * (2 * b) < (P A : ℝ) by nlinarith [hPA]))
      (negRhoRotation k) (negRhoSqRotation k)
  have ha₀mem := ha₀A
  have ha₁mem := ha₁A
  have ha₂mem := ha₂A
  simp only [A, Erdos615.Construction.cellUnion, Set.mem_iUnion] at ha₀mem ha₁mem ha₂mem
  rcases ha₀mem with ⟨i₀, hi₀J, ha₀cell⟩
  rcases ha₁mem with ⟨i₁, hi₁J, ha₁cell⟩
  rcases ha₂mem with ⟨i₂, hi₂J, ha₂cell⟩
  let E := EuclideanSpace ℂ (Fin (k + 1))
  let x₀ : ComplexSphere k := complexOfRealSphere k a₀
  let x₁ : ComplexSphere k := complexOfRealSphere k a₁
  let x₂ : ComplexSphere k := complexOfRealSphere k a₂
  let c₀ : ComplexSphere k := complexCenter k r hr i₀
  let c₁ : ComplexSphere k := complexCenter k r hr i₁
  let c₂ : ComplexSphere k := complexCenter k r hr i₂
  have sphereNorm (x : ComplexSphere k) : ‖(x : E)‖ = 1 := by
    simpa [E, ComplexSphere, Metric.mem_sphere, dist_zero_right] using x.property
  have hfar₁' : D < dist (x₀ : E) (-(rho • (x₁ : E))) := by
    have H : D < dist (complexOfRealSphere k a₀)
        (complexOfRealSphere k (realSphereEquiv (negRhoRotation k) a₁)) := by
      rw [dist_complexOfRealSphere]
      exact hfar₁
    change D < dist
      (((complexOfRealSphere k a₀ : ComplexSphere k) : E))
      (((complexOfRealSphere k (realSphereEquiv (negRhoRotation k) a₁) :
        ComplexSphere k) : E)) at H
    simpa only [x₀, x₁, complexOfRealSphere_negRhoRotation] using H
  have hfar₂' : D < dist (x₀ : E) (-(rho ^ 2 • (x₂ : E))) := by
    have H : D < dist (complexOfRealSphere k a₀)
        (complexOfRealSphere k (realSphereEquiv (negRhoSqRotation k) a₂)) := by
      rw [dist_complexOfRealSphere]
      exact hfar₂
    change D < dist
      (((complexOfRealSphere k a₀ : ComplexSphere k) : E))
      (((complexOfRealSphere k (realSphereEquiv (negRhoSqRotation k) a₂) :
        ComplexSphere k) : E)) at H
    simpa only [x₀, x₂, complexOfRealSphere_negRhoSqRotation] using H
  have hrotNorm₁ : ‖rho • (x₁ : E)‖ = 1 := by
    rw [norm_smul, norm_rho, sphereNorm x₁]
    norm_num
  have hrotNorm₂ : ‖rho ^ 2 • (x₂ : E)‖ = 1 := by
    rw [norm_smul, norm_pow, norm_rho, sphereNorm x₂]
    norm_num
  have hx₀₁ : dist (x₀ : E) (rho • (x₁ : E)) < e :=
    close_of_far_neg (sphereNorm x₀) hrotNorm₁ (by linarith) he hgap hfar₁'
  have hx₀₂ : dist (x₀ : E) (rho ^ 2 • (x₂ : E)) < e :=
    close_of_far_neg (sphereNorm x₀) hrotNorm₂ (by linarith) he hgap hfar₂'
  have hc₀x₀ : dist (c₀ : E) (x₀ : E) ≤ r := by
    have H := Erdos615.Construction.cell_subset_ball h r hr i₀ ha₀cell
    rw [Metric.mem_closedBall] at H
    have H' : dist (complexOfRealSphere k a₀)
        (complexOfRealSphere k (Erdos615.Construction.center h r hr i₀)) ≤ r := by
      rw [dist_complexOfRealSphere]
      exact H
    rw [_root_.dist_comm] at H'
    change dist (c₀ : E) (x₀ : E) ≤ r at H'
    exact H'
  have hc₁x₁ : dist (c₁ : E) (x₁ : E) ≤ r := by
    have H := Erdos615.Construction.cell_subset_ball h r hr i₁ ha₁cell
    rw [Metric.mem_closedBall] at H
    have H' : dist (complexOfRealSphere k a₁)
        (complexOfRealSphere k (Erdos615.Construction.center h r hr i₁)) ≤ r := by
      rw [dist_complexOfRealSphere]
      exact H
    rw [_root_.dist_comm] at H'
    change dist (c₁ : E) (x₁ : E) ≤ r at H'
    exact H'
  have hc₂x₂ : dist (c₂ : E) (x₂ : E) ≤ r := by
    have H := Erdos615.Construction.cell_subset_ball h r hr i₂ ha₂cell
    rw [Metric.mem_closedBall] at H
    have H' : dist (complexOfRealSphere k a₂)
        (complexOfRealSphere k (Erdos615.Construction.center h r hr i₂)) ≤ r := by
      rw [dist_complexOfRealSphere]
      exact H
    rw [_root_.dist_comm] at H'
    change dist (c₂ : E) (x₂ : E) ≤ r at H'
    exact H'
  have rhoDist (u v : E) : dist (rho • u) (rho • v) = dist u v := by
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, norm_rho, one_mul]
  have rhoSqDist (u v : E) : dist (rho ^ 2 • u) (rho ^ 2 • v) = dist u v := by
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, norm_pow, norm_rho,
      one_pow, one_mul]
  have hc₀₁ : dist (c₀ : E) (rho • (c₁ : E)) < d := by
    calc
      dist (c₀ : E) (rho • (c₁ : E)) ≤
          dist (c₀ : E) (x₀ : E) +
            dist (x₀ : E) (rho • (x₁ : E)) +
            dist (rho • (x₁ : E)) (rho • (c₁ : E)) :=
        dist_triangle4 _ _ _ _
      _ < r + e + r := by
        have hlast : dist (rho • (x₁ : E)) (rho • (c₁ : E)) ≤ r := by
          rw [rhoDist]
          rw [_root_.dist_comm]
          exact hc₁x₁
        linarith
      _ < d := by linarith
  have hc₀₂ : dist (c₀ : E) (rho ^ 2 • (c₂ : E)) < d := by
    calc
      dist (c₀ : E) (rho ^ 2 • (c₂ : E)) ≤
          dist (c₀ : E) (x₀ : E) +
            dist (x₀ : E) (rho ^ 2 • (x₂ : E)) +
            dist (rho ^ 2 • (x₂ : E)) (rho ^ 2 • (c₂ : E)) :=
        dist_triangle4 _ _ _ _
      _ < r + e + r := by
        have hlast : dist (rho ^ 2 • (x₂ : E)) (rho ^ 2 • (c₂ : E)) ≤ r := by
          rw [rhoSqDist]
          rw [_root_.dist_comm]
          exact hc₂x₂
        linarith
      _ < d := by linarith
  have hrho21 : rho ^ 2 * rho = 1 := by
    rw [show rho ^ 2 * rho = rho ^ 3 by ring, rho_cube]
  have hrho22 : rho ^ 2 * rho ^ 2 = rho := by
    calc
      rho ^ 2 * rho ^ 2 = rho ^ 3 * rho := by ring
      _ = rho := by rw [rho_cube, one_mul]
  have hx₁₂ : dist (x₁ : E) (rho • (x₂ : E)) < 2 * e := by
    have H : dist (rho • (x₁ : E)) (rho ^ 2 • (x₂ : E)) < 2 * e := by
      calc
        dist (rho • (x₁ : E)) (rho ^ 2 • (x₂ : E)) ≤
            dist (rho • (x₁ : E)) (x₀ : E) +
              dist (x₀ : E) (rho ^ 2 • (x₂ : E)) := dist_triangle _ _ _
        _ < e + e := add_lt_add (by simpa only [_root_.dist_comm] using hx₀₁) hx₀₂
        _ = 2 * e := by ring
    rw [dist_eq_norm, show
      (x₁ : E) - rho • (x₂ : E) =
        rho ^ 2 • (rho • (x₁ : E) - rho ^ 2 • (x₂ : E)) by
          rw [smul_sub, smul_smul, smul_smul, hrho21, hrho22, one_smul],
      norm_smul, norm_pow, norm_rho]
    simpa [dist_eq_norm] using H
  have hc₁₂ : dist (c₁ : E) (rho • (c₂ : E)) < d := by
    calc
      dist (c₁ : E) (rho • (c₂ : E)) ≤
          dist (c₁ : E) (x₁ : E) +
            dist (x₁ : E) (rho • (x₂ : E)) +
            dist (rho • (x₂ : E)) (rho • (c₂ : E)) :=
        dist_triangle4 _ _ _ _
      _ < r + 2 * e + r := by
        have hlast : dist (rho • (x₂ : E)) (rho • (c₂ : E)) ≤ r := by
          rw [rhoDist]
          rw [_root_.dist_comm]
          exact hc₂x₂
        linarith
      _ < d := by linarith
  have hrot₀₁ : rotationClose d c₀ c₁ := by
    refine ⟨0, ?_⟩
    norm_num [approxRotation]
    simpa [dist_eq_norm] using hc₀₁.le
  have hrot₀₂ : rotationClose d c₀ c₂ := by
    refine ⟨1, ?_⟩
    norm_num [approxRotation]
    simpa [dist_eq_norm] using hc₀₂.le
  have hrot₁₂ : rotationClose d c₁ c₂ := by
    refine ⟨0, ?_⟩
    norm_num [approxRotation]
    simpa [dist_eq_norm] using hc₁₂.le
  have hi₀₁ : i₀ ≠ i₁ := by
    intro hij
    subst i₁
    exact rotationClose_irrefl hdroot c₀ hrot₀₁
  have hi₀₂ : i₀ ≠ i₂ := by
    intro hij
    subst i₂
    exact rotationClose_irrefl hdroot c₀ hrot₀₂
  have hi₁₂ : i₁ ≠ i₂ := by
    intro hij
    subst i₂
    exact rotationClose_irrefl hdroot c₁ hrot₁₂
  exact ⟨i₀, hi₀J, i₁, hi₁J, i₂, hi₂J, hi₀₁, hi₀₂, hi₁₂,
    hrot₀₁, hrot₀₂, hrot₁₂⟩

/-- In an inner triangle, two vertices cannot use the same rotation label
relative to the third vertex once the approximation radius is small. -/
theorem same_rotation_not_adjacent {k : ℕ} {d : ℝ} {u v x : ComplexSphere k}
    {h : Fin 2} (hd : 3 * d < Real.sqrt 3)
    (hu : approxRotation d h u x) (hv : approxRotation d h v x) :
    ¬ rotationClose d u v := by
  intro huv
  obtain ⟨j, huv⟩ := huv
  let E := EuclideanSpace ℂ (Fin (k + 1))
  let a : E := rho ^ (h.1 + 1) • (x : E)
  change ‖(u : E) - a‖ ≤ d at hu
  change ‖(v : E) - a‖ ≤ d at hv
  change ‖(u : E) - rho ^ (j.1 + 1) • (v : E)‖ ≤ d at huv
  have huv_dist : ‖(u : E) - (v : E)‖ ≤ 2 * d := by
    calc
      ‖(u : E) - (v : E)‖ = ‖((u : E) - a) - ((v : E) - a)‖ := by
        congr 1
        module
      _ ≤ ‖(u : E) - a‖ + ‖(v : E) - a‖ := norm_sub_le _ _
      _ ≤ d + d := add_le_add hu hv
      _ = 2 * d := by ring
  have hfar :
      ‖(v : E) - rho ^ (j.1 + 1) • (v : E)‖ ≤ 3 * d := by
    calc
      ‖(v : E) - rho ^ (j.1 + 1) • (v : E)‖ =
          ‖((v : E) - (u : E)) +
            ((u : E) - rho ^ (j.1 + 1) • (v : E))‖ := by
        congr 1
        module
      _ ≤ ‖(v : E) - (u : E)‖ +
          ‖(u : E) - rho ^ (j.1 + 1) • (v : E)‖ := norm_add_le _ _
      _ ≤ 2 * d + d := add_le_add (by simpa [norm_sub_rev] using huv_dist) huv
      _ = 3 * d := by ring
  have hvnorm : ‖(v : E)‖ = 1 := by
    simpa [ComplexSphere] using v.property
  have hnorm :
      ‖(v : E) - rho ^ (j.1 + 1) • (v : E)‖ = Real.sqrt 3 := by
    rw [show
      (v : E) - rho ^ (j.1 + 1) • (v : E) =
        ((1 : ℂ) - rho ^ (j.1 + 1)) • (v : E) by module, norm_smul, hvnorm, mul_one]
    fin_cases j
    · norm_num
      exact norm_one_sub_rho
    · norm_num
      exact norm_one_sub_rho_sq
  rw [hnorm] at hfar
  linarith

/-- The graph induced by the inner-edge rule on one tagged part. -/
def innerGraph {k m : ℕ} (d : ℝ) (w : Fin m → ComplexSphere k) :
    SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun i j ↦ rotationClose d (w i) (w j)

theorem innerGraph_adj_iff {k m : ℕ} (d : ℝ)
    (w : Fin m → ComplexSphere k) (i j : Fin m) :
    (innerGraph d w).Adj i j ↔ i ≠ j ∧ rotationClose d (w i) (w j) := by
  rw [innerGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hij, h | h⟩
    · exact ⟨hij, h⟩
    · exact ⟨hij, rotationClose_symm h⟩
  · rintro ⟨hij, h⟩
    exact ⟨hij, Or.inl h⟩

/-- The inner graph is `K₄`-free.  This is the label-pigeonhole part of
the LRSS construction and uses no measure theory. -/
theorem innerGraph_cliqueFree_four {k m : ℕ} {d : ℝ}
    (w : Fin m → ComplexSphere k) (hd : 3 * d < Real.sqrt 3) :
    (innerGraph d w).CliqueFree 4 := by
  intro s hs
  obtain ⟨a, b, c, x, hab, hac, hax, hbc, hbx, hcx, rfl⟩ :=
    Finset.card_eq_four.mp hs.card_eq
  have hcl := hs.isClique
  have hab_adj : rotationClose d (w a) (w b) :=
    ((innerGraph_adj_iff d w a b).mp (hcl (by solve | simp) (by solve | simp) hab)).2
  have hac_adj : rotationClose d (w a) (w c) :=
    ((innerGraph_adj_iff d w a c).mp (hcl (by solve | simp) (by solve | simp) hac)).2
  have hbc_adj : rotationClose d (w b) (w c) :=
    ((innerGraph_adj_iff d w b c).mp (hcl (by solve | simp) (by solve | simp) hbc)).2
  obtain ⟨ha, ha_rot⟩ : rotationClose d (w a) (w x) :=
    (innerGraph_adj_iff d w a x).mp (hcl (by solve | simp) (by solve | simp) hax) |>.2
  obtain ⟨hb, hb_rot⟩ : rotationClose d (w b) (w x) :=
    (innerGraph_adj_iff d w b x).mp (hcl (by solve | simp) (by solve | simp) hbx) |>.2
  obtain ⟨hc, hc_rot⟩ : rotationClose d (w c) (w x) :=
    (innerGraph_adj_iff d w c x).mp (hcl (by solve | simp) (by solve | simp) hcx) |>.2
  have hpigeon : ha = hb ∨ ha = hc ∨ hb = hc := by
    fin_cases ha <;> fin_cases hb <;> fin_cases hc <;> simp
  rcases hpigeon with hab_label | hac_label | hbc_label
  · subst hb
    exact same_rotation_not_adjacent hd ha_rot hb_rot hab_adj
  · subst hc
    exact same_rotation_not_adjacent hd ha_rot hc_rot hac_adj
  · subst hc
    exact same_rotation_not_adjacent hd hb_rot hc_rot hbc_adj

/-- The centroid of three sphere points, regarded as a vector in the ambient
complex Euclidean space. -/
noncomputable def triangleAverage {k : ℕ} (x₀ x₁ x₂ : ComplexSphere k) :
    EuclideanSpace ℂ (Fin (k + 1)) :=
  (3 : ℝ)⁻¹ •
    ((x₀ : EuclideanSpace ℂ (Fin (k + 1))) +
      (x₁ : EuclideanSpace ℂ (Fin (k + 1))) +
      (x₂ : EuclideanSpace ℂ (Fin (k + 1))))

private theorem triangleAverage_norm_le_aux {k : ℕ} {d : ℝ}
    {x₀ x₁ x₂ : ComplexSphere k}
    (h₁ : approxRotation d 0 x₁ x₀) (h₂ : approxRotation d 1 x₂ x₀) :
    ‖triangleAverage x₀ x₁ x₂‖ ≤ 2 * d / 3 := by
  let E := EuclideanSpace ℂ (Fin (k + 1))
  norm_num [approxRotation] at h₁ h₂
  have hrho : -(rho + rho ^ 2) = 1 := by
    linear_combination -one_add_rho_add_sq
  have hsum :
      (x₀ : E) + (x₁ : E) + (x₂ : E) =
        ((x₁ : E) - rho • (x₀ : E)) +
          ((x₂ : E) - rho ^ 2 • (x₀ : E)) := by
    calc
      _ = (x₁ : E) + (x₂ : E) + (x₀ : E) := by module
      _ = (x₁ : E) + (x₂ : E) + (-(rho + rho ^ 2)) • (x₀ : E) := by
        rw [hrho, one_smul]
      _ = _ := by module
  calc
    ‖triangleAverage x₀ x₁ x₂‖ =
        (1 / 3 : ℝ) * ‖(x₀ : E) + (x₁ : E) + (x₂ : E)‖ := by
      rw [triangleAverage, norm_smul]
      norm_num
    _ = (1 / 3 : ℝ) *
        ‖((x₁ : E) - rho • (x₀ : E)) +
          ((x₂ : E) - rho ^ 2 • (x₀ : E))‖ := by rw [hsum]
    _ ≤ (1 / 3 : ℝ) *
        (‖(x₁ : E) - rho • (x₀ : E)‖ +
          ‖(x₂ : E) - rho ^ 2 • (x₀ : E)‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (1 / 3 : ℝ) * (d + d) := by gcongr
    _ = 2 * d / 3 := by ring

/-- The centroid of an inner triangle is small. -/
theorem inner_triangle_average_norm_le {k : ℕ} {d : ℝ}
    {x₀ x₁ x₂ : ComplexSphere k} (hd : 3 * d < Real.sqrt 3)
    (h₁₀ : rotationClose d x₁ x₀) (h₂₀ : rotationClose d x₂ x₀)
    (h₁₂ : rotationClose d x₁ x₂) :
    ‖triangleAverage x₀ x₁ x₂‖ ≤ 2 * d / 3 := by
  obtain ⟨a, ha⟩ := h₁₀
  obtain ⟨b, hb⟩ := h₂₀
  have hab : a ≠ b := by
    intro heq
    subst b
    exact same_rotation_not_adjacent hd ha hb h₁₂
  fin_cases a <;> fin_cases b
  · simp at hab
  · exact triangleAverage_norm_le_aux ha hb
  · simpa [triangleAverage, add_left_comm, add_comm] using
      (triangleAverage_norm_le_aux (x₁ := x₂) (x₂ := x₁) hb ha)
  · simp at hab

/-- The sector and strip conditions force a uniform positive imaginary part
after subtracting a `rho²`-rotate of a second cross neighbor. -/
theorem crossClose_im_inner_sub_rhoSq {k : ℕ} {t : ℝ}
    {x y y' : ComplexSphere k} (hxy : crossClose t x y)
    (hxy' : crossClose t x y') :
    2 * t ≤
      (inner ℂ (x : EuclideanSpace ℂ (Fin (k + 1)))
        ((y : EuclideanSpace ℂ (Fin (k + 1))) -
          rho ^ 2 • (y' : EuclideanSpace ℂ (Fin (k + 1))))).im := by
  let E := EuclideanSpace ℂ (Fin (k + 1))
  let a : ℂ := inner ℂ (x : E) (y : E)
  let b : ℂ := inner ℂ (x : E) (y' : E)
  have ha_nonneg : 0 ≤ a.im := hxy.1.1
  have hb_nonneg : 0 ≤ (-rho ^ 2 * b).im := hxy'.1.2
  have ha_strip := hxy.2 (0 : Fin 3)
  have hb_strip := hxy'.2 (2 : Fin 3)
  norm_num at ha_strip hb_strip
  change t ≤ |a.im| at ha_strip
  change t ≤ |(rho ^ 2 * b).im| at hb_strip
  have ha_lower : t ≤ a.im := by
    rwa [abs_of_nonneg ha_nonneg] at ha_strip
  have hb_abs : |(-rho ^ 2 * b).im| = |(rho ^ 2 * b).im| := by
    rw [neg_mul, Complex.neg_im, abs_neg]
  have hb_mag : t ≤ |(-rho ^ 2 * b).im| := by
    rwa [hb_abs]
  have hb_lower : t ≤ (-rho ^ 2 * b).im := by
    rwa [abs_of_nonneg hb_nonneg] at hb_mag
  rw [inner_sub_right, inner_smul_right]
  change 2 * t ≤ (a - rho ^ 2 * b).im
  calc
    2 * t = t + t := by ring
    _ ≤ a.im + (-rho ^ 2 * b).im := add_le_add ha_lower hb_lower
    _ = (a - rho ^ 2 * b).im := by simp [sub_eq_add_neg]

/-- The local `3 + 2` obstruction.  An inner triangle in the left part and
an inner edge in the right part cannot have all six cross edges. -/
theorem no_oriented_three_two_configuration {k : ℕ} {d t : ℝ}
    (hd0 : 0 ≤ d) (ht : 0 < t) (hdsmall : 3 * d < Real.sqrt 3)
    (hdt : d ^ 2 < 3 * t)
    {x₀ x₁ x₂ y y' : ComplexSphere k}
    (hx₁₀ : rotationClose d x₁ x₀) (hx₂₀ : rotationClose d x₂ x₀)
    (hx₁₂ : rotationClose d x₁ x₂)
    (hyy' : approxRotation d 1 y y')
    (hx₀y : crossClose t x₀ y) (hx₀y' : crossClose t x₀ y')
    (hx₁y : crossClose t x₁ y) (hx₁y' : crossClose t x₁ y')
    (hx₂y : crossClose t x₂ y) (hx₂y' : crossClose t x₂ y') : False := by
  let E := EuclideanSpace ℂ (Fin (k + 1))
  let e : E := (y : E) - rho ^ 2 • (y' : E)
  have he : ‖e‖ ≤ d := by
    norm_num [approxRotation] at hyy'
    exact hyy'
  have havg : ‖triangleAverage x₀ x₁ x₂‖ ≤ 2 * d / 3 :=
    inner_triangle_average_norm_le hdsmall hx₁₀ hx₂₀ hx₁₂
  have h₀ : 2 * t ≤ (inner ℂ (x₀ : E) e).im :=
    crossClose_im_inner_sub_rhoSq hx₀y hx₀y'
  have h₁ : 2 * t ≤ (inner ℂ (x₁ : E) e).im :=
    crossClose_im_inner_sub_rhoSq hx₁y hx₁y'
  have h₂ : 2 * t ≤ (inner ℂ (x₂ : E) e).im :=
    crossClose_im_inner_sub_rhoSq hx₂y hx₂y'
  have hlower : 2 * t ≤ (inner ℂ (triangleAverage x₀ x₁ x₂) e).im := by
    have hsum : 6 * t ≤
        (inner ℂ (x₀ : E) e).im + (inner ℂ (x₁ : E) e).im +
          (inner ℂ (x₂ : E) e).im := by linarith
    simp only [triangleAverage, inner_smul_real_left, inner_add_left]
    norm_num
    linarith
  have him_le_norm :
      (inner ℂ (triangleAverage x₀ x₁ x₂) e).im ≤
        ‖inner ℂ (triangleAverage x₀ x₁ x₂) e‖ :=
    le_trans (le_abs_self _) (Complex.abs_im_le_norm _)
  have hinner :
      ‖inner ℂ (triangleAverage x₀ x₁ x₂) e‖ ≤
        ‖triangleAverage x₀ x₁ x₂‖ * ‖e‖ :=
    norm_inner_le_norm _ _
  have hproduct :
      ‖triangleAverage x₀ x₁ x₂‖ * ‖e‖ ≤ (2 * d / 3) * d := by
    exact mul_le_mul havg he (norm_nonneg _) (by positivity)
  have hupper :
      (inner ℂ (triangleAverage x₀ x₁ x₂) e).im ≤ 2 * d ^ 2 / 3 := by
    calc
      _ ≤ ‖inner ℂ (triangleAverage x₀ x₁ x₂) e‖ := him_le_norm
      _ ≤ ‖triangleAverage x₀ x₁ x₂‖ * ‖e‖ := hinner
      _ ≤ (2 * d / 3) * d := hproduct
      _ = 2 * d ^ 2 / 3 := by ring
  nlinarith

/-- Companion cross-edge inequality with the approximate edge in the first
argument of the inner product. -/
theorem crossClose_im_inner_sub_left_rho {k : ℕ} {t : ℝ}
    {x x' y : ComplexSphere k} (hxy : crossClose t x y)
    (hx'y : crossClose t x' y) :
    2 * t ≤
      (inner ℂ
        ((x : EuclideanSpace ℂ (Fin (k + 1))) -
          rho • (x' : EuclideanSpace ℂ (Fin (k + 1))))
        (y : EuclideanSpace ℂ (Fin (k + 1)))).im := by
  let E := EuclideanSpace ℂ (Fin (k + 1))
  let a : ℂ := inner ℂ (x : E) (y : E)
  let b : ℂ := inner ℂ (x' : E) (y : E)
  have ha_nonneg : 0 ≤ a.im := hxy.1.1
  have hb_nonneg : 0 ≤ (-rho ^ 2 * b).im := hx'y.1.2
  have ha_strip := hxy.2 (0 : Fin 3)
  have hb_strip := hx'y.2 (2 : Fin 3)
  norm_num at ha_strip hb_strip
  change t ≤ |a.im| at ha_strip
  change t ≤ |(rho ^ 2 * b).im| at hb_strip
  have ha_lower : t ≤ a.im := by
    rwa [abs_of_nonneg ha_nonneg] at ha_strip
  have hb_abs : |(-rho ^ 2 * b).im| = |(rho ^ 2 * b).im| := by
    rw [neg_mul, Complex.neg_im, abs_neg]
  have hb_mag : t ≤ |(-rho ^ 2 * b).im| := by rwa [hb_abs]
  have hb_lower : t ≤ (-rho ^ 2 * b).im := by
    rwa [abs_of_nonneg hb_nonneg] at hb_mag
  rw [inner_sub_left, inner_smul_left]
  change 2 * t ≤ (a - starRingEnd ℂ rho * b).im
  have hrho_star : starRingEnd ℂ rho = rho ^ 2 := by
    change star rho = rho ^ 2
    rw [Complex.star_def]
    have hrho_ne : rho ≠ 0 := by
      intro h
      have := norm_rho
      rw [h, norm_zero] at this
      norm_num at this
    apply mul_right_cancel₀ hrho_ne
    rw [← Complex.normSq_eq_conj_mul_self,
      show rho ^ 2 * rho = rho ^ 3 by ring, rho_cube,
      Complex.normSq_eq_norm_sq, norm_rho]
    norm_num
  rw [hrho_star]
  calc
    2 * t = t + t := by ring
    _ ≤ a.im + (-rho ^ 2 * b).im := add_le_add ha_lower hb_lower
    _ = (a - rho ^ 2 * b).im := by simp [sub_eq_add_neg]

/-- The local `2 + 3` obstruction, obtained by putting the inner triangle in
the second part. -/
theorem no_oriented_two_three_configuration {k : ℕ} {d t : ℝ}
    (hd0 : 0 ≤ d) (ht : 0 < t) (hdsmall : 3 * d < Real.sqrt 3)
    (hdt : d ^ 2 < 3 * t)
    {x x' y₀ y₁ y₂ : ComplexSphere k}
    (hxx' : approxRotation d 0 x x')
    (hy₁₀ : rotationClose d y₁ y₀) (hy₂₀ : rotationClose d y₂ y₀)
    (hy₁₂ : rotationClose d y₁ y₂)
    (hxy₀ : crossClose t x y₀) (hx'y₀ : crossClose t x' y₀)
    (hxy₁ : crossClose t x y₁) (hx'y₁ : crossClose t x' y₁)
    (hxy₂ : crossClose t x y₂) (hx'y₂ : crossClose t x' y₂) : False := by
  let E := EuclideanSpace ℂ (Fin (k + 1))
  let e : E := (x : E) - rho • (x' : E)
  have he : ‖e‖ ≤ d := by
    norm_num [approxRotation] at hxx'
    exact hxx'
  have havg : ‖triangleAverage y₀ y₁ y₂‖ ≤ 2 * d / 3 :=
    inner_triangle_average_norm_le hdsmall hy₁₀ hy₂₀ hy₁₂
  have h₀ : 2 * t ≤ (inner ℂ e (y₀ : E)).im :=
    crossClose_im_inner_sub_left_rho hxy₀ hx'y₀
  have h₁ : 2 * t ≤ (inner ℂ e (y₁ : E)).im :=
    crossClose_im_inner_sub_left_rho hxy₁ hx'y₁
  have h₂ : 2 * t ≤ (inner ℂ e (y₂ : E)).im :=
    crossClose_im_inner_sub_left_rho hxy₂ hx'y₂
  have hlower : 2 * t ≤ (inner ℂ e (triangleAverage y₀ y₁ y₂)).im := by
    have hsum : 6 * t ≤
        (inner ℂ e (y₀ : E)).im + (inner ℂ e (y₁ : E)).im +
          (inner ℂ e (y₂ : E)).im := by linarith
    simp only [triangleAverage, inner_smul_real_right, inner_add_right]
    norm_num
    linarith
  have him_le_norm :
      (inner ℂ e (triangleAverage y₀ y₁ y₂)).im ≤
        ‖inner ℂ e (triangleAverage y₀ y₁ y₂)‖ :=
    le_trans (le_abs_self _) (Complex.abs_im_le_norm _)
  have hinner :
      ‖inner ℂ e (triangleAverage y₀ y₁ y₂)‖ ≤
        ‖e‖ * ‖triangleAverage y₀ y₁ y₂‖ :=
    norm_inner_le_norm _ _
  have hproduct :
      ‖e‖ * ‖triangleAverage y₀ y₁ y₂‖ ≤ d * (2 * d / 3) := by
    exact mul_le_mul he havg (norm_nonneg _) hd0
  have hupper :
      (inner ℂ e (triangleAverage y₀ y₁ y₂)).im ≤ 2 * d ^ 2 / 3 := by
    calc
      _ ≤ ‖inner ℂ e (triangleAverage y₀ y₁ y₂)‖ := him_le_norm
      _ ≤ ‖e‖ * ‖triangleAverage y₀ y₁ y₂‖ := hinner
      _ ≤ d * (2 * d / 3) := hproduct
      _ = 2 * d ^ 2 / 3 := by ring
  nlinarith

/-- The oriented relation whose symmetric, irreflexive closure is the finite
two-part complex Bollobás--Erdős graph. -/
def geometricRel {k m : ℕ} (d t : ℝ)
    (w z : Fin m → ComplexSphere k) :
    (Fin m ⊕ Fin m) → (Fin m ⊕ Fin m) → Prop
  | .inl i, .inl j => rotationClose d (w i) (w j)
  | .inr i, .inr j => rotationClose d (z i) (z j)
  | .inl i, .inr j => crossClose t (w i) (z j)
  | _, _ => False

/-- The finite graph before transport from `Fin m ⊕ Fin m` to `Fin (2*m)`. -/
def geometricGraph {k m : ℕ} (d t : ℝ)
    (w z : Fin m → ComplexSphere k) : SimpleGraph (Fin m ⊕ Fin m) :=
  SimpleGraph.fromRel (geometricRel d t w z)

theorem geometricGraph_left_adj {k m : ℕ} (d t : ℝ)
    (w z : Fin m → ComplexSphere k) (i j : Fin m) :
    (geometricGraph d t w z).Adj (.inl i) (.inl j) ↔
      i ≠ j ∧
        (rotationClose d (w i) (w j) ∨ rotationClose d (w j) (w i)) := by
  simp [geometricGraph, geometricRel]

theorem geometricGraph_left_adj_iff {k m : ℕ} (d t : ℝ)
    (w z : Fin m → ComplexSphere k) (i j : Fin m) :
    (geometricGraph d t w z).Adj (.inl i) (.inl j) ↔
      i ≠ j ∧ rotationClose d (w i) (w j) := by
  rw [geometricGraph_left_adj]
  constructor
  · rintro ⟨hij, h | h⟩
    · exact ⟨hij, h⟩
    · exact ⟨hij, rotationClose_symm h⟩
  · rintro ⟨hij, h⟩
    exact ⟨hij, Or.inl h⟩

theorem geometricGraph_right_adj {k m : ℕ} (d t : ℝ)
    (w z : Fin m → ComplexSphere k) (i j : Fin m) :
    (geometricGraph d t w z).Adj (.inr i) (.inr j) ↔
      i ≠ j ∧
        (rotationClose d (z i) (z j) ∨ rotationClose d (z j) (z i)) := by
  simp [geometricGraph, geometricRel]

theorem geometricGraph_right_adj_iff {k m : ℕ} (d t : ℝ)
    (w z : Fin m → ComplexSphere k) (i j : Fin m) :
    (geometricGraph d t w z).Adj (.inr i) (.inr j) ↔
      i ≠ j ∧ rotationClose d (z i) (z j) := by
  rw [geometricGraph_right_adj]
  constructor
  · rintro ⟨hij, h | h⟩
    · exact ⟨hij, h⟩
    · exact ⟨hij, rotationClose_symm h⟩
  · rintro ⟨hij, h⟩
    exact ⟨hij, Or.inl h⟩

theorem geometricGraph_cross_adj {k m : ℕ} (d t : ℝ)
    (w z : Fin m → ComplexSphere k) (i j : Fin m) :
    (geometricGraph d t w z).Adj (.inl i) (.inr j) ↔
      crossClose t (w i) (z j) := by
  simp [geometricGraph, geometricRel]

private theorem no_four_left_of_clique {k m : ℕ} {d t : ℝ}
    (w z : Fin m → ComplexSphere k) (hdsmall : 3 * d < Real.sqrt 3)
    {s : Set (Fin m ⊕ Fin m)}
    (hs : (geometricGraph d t w z).IsClique s)
    {a b c e : Fin m}
    (ha : Sum.inl a ∈ s) (hb : Sum.inl b ∈ s)
    (hc : Sum.inl c ∈ s) (he : Sum.inl e ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) : False := by
  apply (innerGraph_cliqueFree_four w hdsmall) {a, b, c, e}
  refine ⟨?_, ?_⟩
  · intro u hu v hv huv
    have hus : Sum.inl u ∈ s := by
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
      · exact he
    have hvs : Sum.inl v ∈ s := by
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
      · exact he
    exact (innerGraph_adj_iff d w u v).2
      ⟨huv, (geometricGraph_left_adj_iff d t w z u v).1
        (hs hus hvs (by simpa using huv)) |>.2⟩
  · simp [hab, hac, hae, hbc, hbe, hce]

private theorem no_four_right_of_clique {k m : ℕ} {d t : ℝ}
    (w z : Fin m → ComplexSphere k) (hdsmall : 3 * d < Real.sqrt 3)
    {s : Set (Fin m ⊕ Fin m)}
    (hs : (geometricGraph d t w z).IsClique s)
    {a b c e : Fin m}
    (ha : Sum.inr a ∈ s) (hb : Sum.inr b ∈ s)
    (hc : Sum.inr c ∈ s) (he : Sum.inr e ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) : False := by
  apply (innerGraph_cliqueFree_four z hdsmall) {a, b, c, e}
  refine ⟨?_, ?_⟩
  · intro u hu v hv huv
    have hus : Sum.inr u ∈ s := by
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
      · exact he
    have hvs : Sum.inr v ∈ s := by
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
      · exact he
    exact (innerGraph_adj_iff d z u v).2
      ⟨huv, (geometricGraph_right_adj_iff d t w z u v).1
        (hs hus hvs (by simpa using huv)) |>.2⟩
  · simp [hab, hac, hae, hbc, hbe, hce]

private theorem no_three_left_two_right_of_clique {k m : ℕ} {d t : ℝ}
    (w z : Fin m → ComplexSphere k)
    (hd0 : 0 ≤ d) (ht : 0 < t) (hdsmall : 3 * d < Real.sqrt 3)
    (hdt : d ^ 2 < 3 * t) {s : Set (Fin m ⊕ Fin m)}
    (hs : (geometricGraph d t w z).IsClique s)
    {a b c p q : Fin m}
    (ha : Sum.inl a ∈ s) (hb : Sum.inl b ∈ s) (hc : Sum.inl c ∈ s)
    (hp : Sum.inr p ∈ s) (hq : Sum.inr q ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hpq : p ≠ q) : False := by
  have hx₁₀ : rotationClose d (w b) (w a) :=
    (geometricGraph_left_adj_iff d t w z b a).1
      (hs hb ha (by simpa using hab.symm)) |>.2
  have hx₂₀ : rotationClose d (w c) (w a) :=
    (geometricGraph_left_adj_iff d t w z c a).1
      (hs hc ha (by simpa using hac.symm)) |>.2
  have hx₁₂ : rotationClose d (w b) (w c) :=
    (geometricGraph_left_adj_iff d t w z b c).1
      (hs hb hc (by simpa using hbc)) |>.2
  have hpqrot : rotationClose d (z p) (z q) :=
    (geometricGraph_right_adj_iff d t w z p q).1
      (hs hp hq (by simpa using hpq)) |>.2
  have cross (i : Fin m) (hi : Sum.inl i ∈ s) (j : Fin m)
      (hj : Sum.inr j ∈ s) : crossClose t (w i) (z j) :=
    (geometricGraph_cross_adj d t w z i j).1 (hs hi hj (by solve | simp))
  obtain ⟨r, hr⟩ := hpqrot
  fin_cases r
  · exact no_oriented_three_two_configuration hd0 ht hdsmall hdt hx₁₀ hx₂₀ hx₁₂
      (approxRotation_zero_flip_one hr)
      (cross a ha q hq) (cross a ha p hp)
      (cross b hb q hq) (cross b hb p hp)
      (cross c hc q hq) (cross c hc p hp)
  · exact no_oriented_three_two_configuration hd0 ht hdsmall hdt hx₁₀ hx₂₀ hx₁₂ hr
      (cross a ha p hp) (cross a ha q hq)
      (cross b hb p hp) (cross b hb q hq)
      (cross c hc p hp) (cross c hc q hq)

private theorem no_two_left_three_right_of_clique {k m : ℕ} {d t : ℝ}
    (w z : Fin m → ComplexSphere k)
    (hd0 : 0 ≤ d) (ht : 0 < t) (hdsmall : 3 * d < Real.sqrt 3)
    (hdt : d ^ 2 < 3 * t) {s : Set (Fin m ⊕ Fin m)}
    (hs : (geometricGraph d t w z).IsClique s)
    {p q a b c : Fin m}
    (hp : Sum.inl p ∈ s) (hq : Sum.inl q ∈ s)
    (ha : Sum.inr a ∈ s) (hb : Sum.inr b ∈ s) (hc : Sum.inr c ∈ s)
    (hpq : p ≠ q) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  have hpqrot : rotationClose d (w p) (w q) :=
    (geometricGraph_left_adj_iff d t w z p q).1
      (hs hp hq (by simpa using hpq)) |>.2
  have hy₁₀ : rotationClose d (z b) (z a) :=
    (geometricGraph_right_adj_iff d t w z b a).1
      (hs hb ha (by simpa using hab.symm)) |>.2
  have hy₂₀ : rotationClose d (z c) (z a) :=
    (geometricGraph_right_adj_iff d t w z c a).1
      (hs hc ha (by simpa using hac.symm)) |>.2
  have hy₁₂ : rotationClose d (z b) (z c) :=
    (geometricGraph_right_adj_iff d t w z b c).1
      (hs hb hc (by simpa using hbc)) |>.2
  have cross (i : Fin m) (hi : Sum.inl i ∈ s) (j : Fin m)
      (hj : Sum.inr j ∈ s) : crossClose t (w i) (z j) :=
    (geometricGraph_cross_adj d t w z i j).1 (hs hi hj (by solve | simp))
  obtain ⟨r, hr⟩ := hpqrot
  fin_cases r
  · exact no_oriented_two_three_configuration hd0 ht hdsmall hdt hr hy₁₀ hy₂₀ hy₁₂
      (cross p hp a ha) (cross q hq a ha)
      (cross p hp b hb) (cross q hq b hb)
      (cross p hp c hc) (cross q hq c hc)
  · exact no_oriented_two_three_configuration hd0 ht hdsmall hdt
      (approxRotation_one_flip_zero hr) hy₁₀ hy₂₀ hy₁₂
      (cross q hq a ha) (cross p hp a ha)
      (cross q hq b hb) (cross p hp b hb)
      (cross q hq c hc) (cross p hp c hc)

/-- The complete geometric graph is `K₅`-free whenever the two numerical
separation inequalities used above hold. -/
theorem geometricGraph_cliqueFree_five {k m : ℕ} {d t : ℝ}
    (w z : Fin m → ComplexSphere k)
    (hd0 : 0 ≤ d) (ht : 0 < t) (hdsmall : 3 * d < Real.sqrt 3)
    (hdt : d ^ 2 < 3 * t) : (geometricGraph d t w z).CliqueFree 5 := by
  intro s hs
  have hcard : s.card = 4 + 1 := by simpa using hs.card_eq
  obtain ⟨v₀, u, hv₀u, hus, hu_card⟩ := Finset.card_eq_succ.mp hcard
  obtain ⟨v₁, v₂, v₃, v₄, h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄, rfl⟩ :=
    Finset.card_eq_four.mp hu_card
  have h₀₁ : v₀ ≠ v₁ := by
    intro h
    apply hv₀u
    simp [h]
  have h₀₂ : v₀ ≠ v₂ := by
    intro h
    apply hv₀u
    simp [h]
  have h₀₃ : v₀ ≠ v₃ := by
    intro h
    apply hv₀u
    simp [h]
  have h₀₄ : v₀ ≠ v₄ := by
    intro h
    apply hv₀u
    simp [h]
  subst s
  rcases v₀ with v₀ | v₀ <;> rcases v₁ with v₁ | v₁ <;>
    rcases v₂ with v₂ | v₂ <;> rcases v₃ with v₃ | v₃ <;>
    rcases v₄ with v₄ | v₄
  all_goals simp at h₀₁ h₀₂ h₀₃ h₀₄ h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄
  · apply no_four_left_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₁) (c := v₂) (e := v₃) <;> simp <;> assumption
  · apply no_four_left_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₁) (c := v₂) (e := v₃) <;> simp <;> assumption
  · apply no_four_left_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₁) (c := v₂) (e := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₀) (b := v₁) (c := v₂) (p := v₃) (q := v₄) <;> simp <;> assumption
  · apply no_four_left_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₁) (c := v₃) (e := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₀) (b := v₁) (c := v₃) (p := v₂) (q := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₀) (b := v₁) (c := v₄) (p := v₂) (q := v₃) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₀) (q := v₁) (a := v₂) (b := v₃) (c := v₄) <;> simp <;> assumption
  · apply no_four_left_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₂) (c := v₃) (e := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₀) (b := v₂) (c := v₃) (p := v₁) (q := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₀) (b := v₂) (c := v₄) (p := v₁) (q := v₃) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₀) (q := v₂) (a := v₁) (b := v₃) (c := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₀) (b := v₃) (c := v₄) (p := v₁) (q := v₂) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₀) (q := v₃) (a := v₁) (b := v₂) (c := v₄) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₀) (q := v₄) (a := v₁) (b := v₂) (c := v₃) <;> simp <;> assumption
  · apply no_four_right_of_clique w z hdsmall hs.isClique
      (a := v₁) (b := v₂) (c := v₃) (e := v₄) <;> simp <;> assumption
  · apply no_four_left_of_clique w z hdsmall hs.isClique
      (a := v₁) (b := v₂) (c := v₃) (e := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₁) (b := v₂) (c := v₃) (p := v₀) (q := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₁) (b := v₂) (c := v₄) (p := v₀) (q := v₃) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₁) (q := v₂) (a := v₀) (b := v₃) (c := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₁) (b := v₃) (c := v₄) (p := v₀) (q := v₂) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₁) (q := v₃) (a := v₀) (b := v₂) (c := v₄) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₁) (q := v₄) (a := v₀) (b := v₂) (c := v₃) <;> simp <;> assumption
  · apply no_four_right_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₂) (c := v₃) (e := v₄) <;> simp <;> assumption
  · apply no_three_left_two_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (a := v₂) (b := v₃) (c := v₄) (p := v₀) (q := v₁) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₂) (q := v₃) (a := v₀) (b := v₁) (c := v₄) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₂) (q := v₄) (a := v₀) (b := v₁) (c := v₃) <;> simp <;> assumption
  · apply no_four_right_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₁) (c := v₃) (e := v₄) <;> simp <;> assumption
  · apply no_two_left_three_right_of_clique w z hd0 ht hdsmall hdt hs.isClique
      (p := v₃) (q := v₄) (a := v₀) (b := v₁) (c := v₂) <;> simp <;> assumption
  · apply no_four_right_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₁) (c := v₂) (e := v₄) <;> simp <;> assumption
  · apply no_four_right_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₁) (c := v₂) (e := v₃) <;> simp <;> assumption
  · apply no_four_right_of_clique w z hdsmall hs.isClique
      (a := v₀) (b := v₁) (c := v₂) (e := v₃) <;> simp <;> assumption

/-! ## The finite construction interface -/

/-- Transport the two tagged parts of the geometric construction to the
standard vertex type `Fin (m + m)` used by the statement of the problem. -/
def finiteGeometricGraph {k m : ℕ} (d t : ℝ)
    (w z : Fin m → ComplexSphere k) : SimpleGraph (Fin (m + m)) :=
  (geometricGraph d t w z).map finSumFinEquiv.toEmbedding

/-! ### Rounding the spherical weights -/

noncomputable def copyVertexEquivFin (h : ℕ) (r : ℝ)
    (hh : 0 < h) (hr : 0 < r) (L : ℕ) :
    Erdos615.Construction.CopyVertex h r hh hr L ≃
      Fin (Erdos615.Construction.copyCard h r hh hr L) :=
  Fintype.equivFin _

noncomputable def roundedLeftPosition (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (v : Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L)) : ComplexSphere k :=
  complexCenter k r hr
    ((copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L).symm v).1

noncomputable def roundedRightPosition (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (q : Fin 3)
    (v : Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L)) : ComplexSphere k :=
  rhoRotateSphere k q (roundedLeftPosition k r hr L v)

/-- The standard finite vertex type, decoded as a Boolean part tag and a
rounded copy of a partition cell. -/
noncomputable def roundedVertexEquiv (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) :
    Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r (by omega) hr L +
      Erdos615.Construction.copyCard ((k + 1) * 2) r (by omega) hr L) ≃
      Bool × Erdos615.Construction.CopyVertex ((k + 1) * 2) r (by omega) hr L :=
  finSumFinEquiv.symm |>.trans
    ((Equiv.sumCongr
      (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L).symm
      (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L).symm).trans
      (Equiv.boolProdEquivSum _).symm)

theorem rounded_adj_of_same_part {k L : ℕ} {r d t : ℝ} (hr : 0 < r)
    (q : Fin 3)
    (u v : Bool × Erdos615.Construction.CopyVertex ((k + 1) * 2) r
      (by omega) hr L) (huv : u ≠ v) (hpart : u.1 = v.1)
    (hrot : rotationClose d (complexCenter k r hr u.2.1)
      (complexCenter k r hr v.2.1)) :
    (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
      (roundedRightPosition k r hr L q)).Adj
        ((roundedVertexEquiv k r hr L).symm u)
        ((roundedVertexEquiv k r hr L).symm v) := by
  rcases u with ⟨bu, u⟩
  rcases v with ⟨bv, v⟩
  simp only at hpart
  subst bv
  cases bu
  · rw [finiteGeometricGraph, SimpleGraph.map_adj]
    refine ⟨Sum.inl (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L u),
      Sum.inl (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L v), ?_, by
        rfl, by rfl⟩
    rw [geometricGraph_left_adj_iff]
    refine ⟨?_, ?_⟩
    · intro huvFin
      apply huv
      simp only [Prod.mk.injEq, true_and]
      exact (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L).injective huvFin
    · simpa [roundedLeftPosition] using hrot
  · rw [finiteGeometricGraph, SimpleGraph.map_adj]
    refine ⟨Sum.inr (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L u),
      Sum.inr (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L v), ?_, by
        rfl, by rfl⟩
    rw [geometricGraph_right_adj_iff]
    refine ⟨?_, ?_⟩
    · intro huvFin
      apply huv
      simp only [Prod.mk.injEq, true_and]
      exact (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L).injective huvFin
    · simpa [roundedRightPosition, roundedLeftPosition] using
        rotationClose_rhoRotate q hrot

abbrev CrossIndexPair (k : ℕ) (r : ℝ) (hr : 0 < r)
    (t : ℝ) (q : Fin 3) :=
  {p : Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr) ×
      Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr) //
    crossClose t (complexCenter k r hr p.1)
      (rhoRotateSphere k q (complexCenter k r hr p.2))}

abbrev WeightedCrossCopyPair (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (t : ℝ) (q : Fin 3) :=
  Σ p : CrossIndexPair k r hr t q,
    Fin (Erdos615.Construction.multiplicity ((k + 1) * 2) r (by omega) hr L p.1.1) ×
      Fin (Erdos615.Construction.multiplicity ((k + 1) * 2) r (by omega) hr L p.1.2)

theorem crossWeight_eq_sum (k : ℕ) (r : ℝ) (hr : 0 < r)
    (t : ℝ) (q : Fin 3) :
    crossWeight k r hr t q =
      ∑ p : CrossIndexPair k r hr t q,
        Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr p.1.1 *
          Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr p.1.2 := by
  classical
  rw [crossWeight]
  let I := Fin (Erdos615.Construction.netCard ((k + 1) * 2) r hr)
  let good : I × I → Prop := fun p ↦
    crossClose t (complexCenter k r hr p.1)
      (rhoRotateSphere k q (complexCenter k r hr p.2))
  let f : I × I → ℝ := fun p ↦
    Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr p.1 *
      Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr p.2
  rw [show (∑ i : I, Erdos615.Construction.weight ((k + 1) * 2) r
      (by omega) hr i * ∑ j : I, if good (i, j) then
        Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr j else 0) =
      ∑ p : I × I, if good p then f p else 0 by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs <;> simp_all [f]]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter good) (by simp [good]) f

theorem weightedCrossCopyPair_card_lower (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (t : ℝ) (q : Fin 3) :
    (L : ℝ) ^ 2 * crossWeight k r hr t q ≤
      Fintype.card (WeightedCrossCopyPair k r hr L t q) := by
  rw [crossWeight_eq_sum]
  change (L : ℝ) ^ 2 * (∑ p : CrossIndexPair k r hr t q,
      Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr p.1.1 *
        Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr p.1.2) ≤ _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hi := Erdos615.Construction.multiplicity_lower ((k + 1) * 2) r
    (by omega) hr L p.1.1
  have hj := Erdos615.Construction.multiplicity_lower ((k + 1) * 2) r
    (by omega) hr L p.1.2
  calc
    (L : ℝ) ^ 2 *
        (Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr p.1.1 *
          Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr p.1.2) =
      ((L : ℝ) * Erdos615.Construction.weight ((k + 1) * 2) r
        (by omega) hr p.1.1) *
      ((L : ℝ) * Erdos615.Construction.weight ((k + 1) * 2) r
        (by omega) hr p.1.2) := by ring
    _ ≤ Erdos615.Construction.multiplicity ((k + 1) * 2) r
        (by omega) hr L p.1.1 *
      Erdos615.Construction.multiplicity ((k + 1) * 2) r
        (by omega) hr L p.1.2 := by
      exact mul_le_mul hi hj
        (mul_nonneg (Nat.cast_nonneg L)
          (Erdos615.Construction.weight_nonneg _ _ _ _ _)) (Nat.cast_nonneg _)

noncomputable def weightedCrossLeftFin (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (t : ℝ) (q : Fin 3)
    (p : WeightedCrossCopyPair k r hr L t q) :
    Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r (by omega) hr L) :=
  copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L ⟨p.1.1.1, p.2.1⟩

noncomputable def weightedCrossRightFin (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (t : ℝ) (q : Fin 3)
    (p : WeightedCrossCopyPair k r hr L t q) :
    Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r (by omega) hr L) :=
  copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L ⟨p.1.1.2, p.2.2⟩

noncomputable def weightedCrossPairToEdge (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (d t : ℝ) (q : Fin 3)
    (p : WeightedCrossCopyPair k r hr L t q) :
    (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
      (roundedRightPosition k r hr L q)).edgeFinset := by
  let m := Erdos615.Construction.copyCard ((k + 1) * 2) r (by omega) hr L
  let u : Fin (m + m) := finSumFinEquiv
    (Sum.inl (weightedCrossLeftFin k r hr L t q p) : Fin m ⊕ Fin m)
  let v : Fin (m + m) := finSumFinEquiv
    (Sum.inr (weightedCrossRightFin k r hr L t q p) : Fin m ⊕ Fin m)
  refine ⟨s(u, v), ?_⟩
  rw [SimpleGraph.mem_edgeFinset]
  change (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
    (roundedRightPosition k r hr L q)).Adj u v
  rw [finiteGeometricGraph, SimpleGraph.map_adj]
  refine ⟨Sum.inl (weightedCrossLeftFin k r hr L t q p),
    Sum.inr (weightedCrossRightFin k r hr L t q p), ?_, rfl, rfl⟩
  rw [geometricGraph_cross_adj]
  simpa [roundedLeftPosition, roundedRightPosition, weightedCrossLeftFin,
    weightedCrossRightFin] using p.1.property

theorem weightedCrossPairToEdge_injective (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (d t : ℝ) (q : Fin 3) :
    Function.Injective (weightedCrossPairToEdge k r hr L d t q) := by
  intro p p' hpp'
  have hs := congrArg Subtype.val hpp'
  dsimp only [weightedCrossPairToEdge] at hs
  change s(finSumFinEquiv (Sum.inl (weightedCrossLeftFin k r hr L t q p)),
      finSumFinEquiv (Sum.inr (weightedCrossRightFin k r hr L t q p))) =
    s(finSumFinEquiv (Sum.inl (weightedCrossLeftFin k r hr L t q p')),
      finSumFinEquiv (Sum.inr (weightedCrossRightFin k r hr L t q p'))) at hs
  rw [Sym2.eq_iff] at hs
  have hends :
      weightedCrossLeftFin k r hr L t q p = weightedCrossLeftFin k r hr L t q p' ∧
      weightedCrossRightFin k r hr L t q p = weightedCrossRightFin k r hr L t q p' := by
    rcases hs with hs | hs
    · exact ⟨Sum.inl.inj (finSumFinEquiv.injective hs.1),
        Sum.inr.inj (finSumFinEquiv.injective hs.2)⟩
    · exfalso
      have := finSumFinEquiv.injective hs.1
      simp at this
  have hleft :=
    (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L).injective hends.1
  have hright :=
    (copyVertexEquivFin ((k + 1) * 2) r (by omega) hr L).injective hends.2
  rcases p with ⟨⟨⟨i, j⟩, hij⟩, a, b⟩
  rcases p' with ⟨⟨⟨i', j'⟩, hij'⟩, a', b'⟩
  dsimp only [weightedCrossLeftFin, weightedCrossRightFin] at hleft hright
  cases hleft
  cases hright
  rfl

/-- The rounded finite graph retains the weighted cross density. -/
theorem finiteGeometricGraph_edge_lower (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ) (d t : ℝ) (q : Fin 3) :
    (L : ℝ) ^ 2 * crossWeight k r hr t q ≤
      ((finiteGeometricGraph d t (roundedLeftPosition k r hr L)
        (roundedRightPosition k r hr L q)).edgeFinset.card : ℝ) := by
  have hcard : Fintype.card (WeightedCrossCopyPair k r hr L t q) ≤
      Fintype.card
        (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
          (roundedRightPosition k r hr L q)).edgeFinset :=
    Fintype.card_le_of_injective _
      (weightedCrossPairToEdge_injective k r hr L d t q)
  have hcard' : (Fintype.card (WeightedCrossCopyPair k r hr L t q) : ℝ) ≤
      ((finiteGeometricGraph d t (roundedLeftPosition k r hr L)
        (roundedRightPosition k r hr L q)).edgeFinset.card : ℝ) := by
    exact_mod_cast (by simpa only [Fintype.card_coe] using hcard)
  exact (weightedCrossCopyPair_card_lower k r hr L t q).trans hcard'

noncomputable def roundedDecodedSet (k : ℕ) (r : ℝ) (hr : 0 < r)
    (L : ℕ)
    (S : Finset (Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L + Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L))) :
    Finset (Bool × Erdos615.Construction.CopyVertex ((k + 1) * 2) r
      (by omega) hr L) :=
  S.map (roundedVertexEquiv k r hr L).toEmbedding

/-- A triangle-free set cannot represent partition cells of total weight
above the three-point concentration threshold in either part. -/
theorem rounded_part_weight_bound (k L : ℕ) (r d e D t : ℝ)
    (hr : 0 < r) (he : 0 ≤ e) (hD : 1 ≤ D)
    (hgap : 4 - D ^ 2 < e ^ 2) (hclose : 2 * r + 2 * e < d)
    (hdroot : d < Real.sqrt 3) (q : Fin 3)
    (S : Finset (Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L + Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L)))
    (hS : (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
      (roundedRightPosition k r hr L q)).CliqueFreeOn S 3) (bpart : Bool) :
    ∑ i ∈ Erdos615.Construction.representedCells ((k + 1) * 2) r
        (by omega) hr L (roundedDecodedSet k r hr L S) bpart,
      Erdos615.Construction.weight ((k + 1) * 2) r (by omega) hr i ≤
        4 * (D / 2) ^ ((k + 1) * 2) := by
  let s := roundedDecodedSet k r hr L S
  let J := Erdos615.Construction.representedCells ((k + 1) * 2) r
    (by omega) hr L s bpart
  by_contra hn
  have hlarge : 4 * (D / 2) ^ ((k + 1) * 2) <
      ∑ i ∈ J, Erdos615.Construction.weight ((k + 1) * 2) r
        (by omega) hr i := lt_of_not_ge hn
  obtain ⟨i₀, hi₀J, i₁, hi₁J, i₂, hi₂J,
      hi₀₁, hi₀₂, hi₁₂, hrot₀₁, hrot₀₂, hrot₁₂⟩ :=
    large_cells_give_inner_triangle k r d e D hr he hD hgap hclose hdroot J hlarge
  rcases Finset.mem_image.mp hi₀J with ⟨u₀, hu₀part, hu₀cell⟩
  rcases Finset.mem_image.mp hi₁J with ⟨u₁, hu₁part, hu₁cell⟩
  rcases Finset.mem_image.mp hi₂J with ⟨u₂, hu₂part, hu₂cell⟩
  have hu₀s : u₀ ∈ s := (Finset.mem_filter.mp hu₀part).1
  have hu₁s : u₁ ∈ s := (Finset.mem_filter.mp hu₁part).1
  have hu₂s : u₂ ∈ s := (Finset.mem_filter.mp hu₂part).1
  have hu₀b : u₀.1 = bpart := (Finset.mem_filter.mp hu₀part).2
  have hu₁b : u₁.1 = bpart := (Finset.mem_filter.mp hu₁part).2
  have hu₂b : u₂.1 = bpart := (Finset.mem_filter.mp hu₂part).2
  have hcell₀ : u₀.2.1 = i₀ := hu₀cell
  have hcell₁ : u₁.2.1 = i₁ := hu₁cell
  have hcell₂ : u₂.2.1 = i₂ := hu₂cell
  have hu₀₁ : u₀ ≠ u₁ := by
    intro H
    apply hi₀₁
    rw [← hcell₀, ← hcell₁, H]
  have hu₀₂ : u₀ ≠ u₂ := by
    intro H
    apply hi₀₂
    rw [← hcell₀, ← hcell₂, H]
  have hu₁₂ : u₁ ≠ u₂ := by
    intro H
    apply hi₁₂
    rw [← hcell₁, ← hcell₂, H]
  let v₀ := (roundedVertexEquiv k r hr L).symm u₀
  let v₁ := (roundedVertexEquiv k r hr L).symm u₁
  let v₂ := (roundedVertexEquiv k r hr L).symm u₂
  have hv₀S : v₀ ∈ S := by
    simpa [s, roundedDecodedSet, v₀] using hu₀s
  have hv₁S : v₁ ∈ S := by
    simpa [s, roundedDecodedSet, v₁] using hu₁s
  have hv₂S : v₂ ∈ S := by
    simpa [s, roundedDecodedSet, v₂] using hu₂s
  have hv₀₁ : v₀ ≠ v₁ := (roundedVertexEquiv k r hr L).symm.injective.ne hu₀₁
  have hv₀₂ : v₀ ≠ v₂ := (roundedVertexEquiv k r hr L).symm.injective.ne hu₀₂
  have hv₁₂ : v₁ ≠ v₂ := (roundedVertexEquiv k r hr L).symm.injective.ne hu₁₂
  have hadj₀₁ : (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
      (roundedRightPosition k r hr L q)).Adj v₀ v₁ := by
    apply rounded_adj_of_same_part hr q u₀ u₁ hu₀₁
      (hu₀b.trans hu₁b.symm)
    simpa [hcell₀, hcell₁] using hrot₀₁
  have hadj₀₂ : (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
      (roundedRightPosition k r hr L q)).Adj v₀ v₂ := by
    apply rounded_adj_of_same_part hr q u₀ u₂ hu₀₂
      (hu₀b.trans hu₂b.symm)
    simpa [hcell₀, hcell₂] using hrot₀₂
  have hadj₁₂ : (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
      (roundedRightPosition k r hr L q)).Adj v₁ v₂ := by
    apply rounded_adj_of_same_part hr q u₁ u₂ hu₁₂
      (hu₁b.trans hu₂b.symm)
    simpa [hcell₁, hcell₂] using hrot₁₂
  apply hS (t := {v₀, v₁, v₂})
  · intro v hv
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · exact hv₀S
    · exact hv₁S
    · exact hv₂S
  · refine ⟨?_, ?_⟩
    · intro v hv w hw hvw
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv hw
      rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
      all_goals simp_all only [ne_eq, not_true_eq_false]
      all_goals first | exact hadj₀₁ | exact hadj₀₂ | exact hadj₁₂ |
        exact hadj₀₁.symm | exact hadj₀₂.symm | exact hadj₁₂.symm
    · simp [hv₀₁, hv₀₂, hv₁₂]

theorem rounded_part_card_bound (k L : ℕ) (r d e D t : ℝ)
    (hr : 0 < r) (he : 0 ≤ e) (hD : 1 ≤ D)
    (hgap : 4 - D ^ 2 < e ^ 2) (hclose : 2 * r + 2 * e < d)
    (hdroot : d < Real.sqrt 3) (q : Fin 3)
    (S : Finset (Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L + Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L)))
    (hS : (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
      (roundedRightPosition k r hr L q)).CliqueFreeOn S 3) (bpart : Bool) :
    ((Erdos615.Construction.partSet ((k + 1) * 2) r (by omega) hr L
      (roundedDecodedSet k r hr L S) bpart).card : ℝ) ≤
      (L : ℝ) * (4 * (D / 2) ^ ((k + 1) * 2)) +
        Erdos615.Construction.netCard ((k + 1) * 2) r hr := by
  let s := roundedDecodedSet k r hr L S
  let J := Erdos615.Construction.representedCells ((k + 1) * 2) r
    (by omega) hr L s bpart
  have hcard := Erdos615.Construction.partSet_card_le_sum_multiplicity
    ((k + 1) * 2) r (by omega) hr L s bpart
  have hweight := rounded_part_weight_bound k L r d e D t hr he hD hgap hclose
    hdroot q S hS bpart
  have hmult : (∑ i ∈ J, Erdos615.Construction.multiplicity
      ((k + 1) * 2) r (by omega) hr L i : ℝ) ≤
      (L : ℝ) * (∑ i ∈ J, Erdos615.Construction.weight
        ((k + 1) * 2) r (by omega) hr i) + J.card := by
    calc
      (∑ i ∈ J, Erdos615.Construction.multiplicity
          ((k + 1) * 2) r (by omega) hr L i : ℝ) ≤
        ∑ i ∈ J, ((L : ℝ) * Erdos615.Construction.weight
          ((k + 1) * 2) r (by omega) hr i + 1) := by
            exact Finset.sum_le_sum fun i _ ↦
              Erdos615.Construction.multiplicity_upper _ _ _ _ _ _
      _ = (L : ℝ) * (∑ i ∈ J, Erdos615.Construction.weight
          ((k + 1) * 2) r (by omega) hr i) + J.card := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
            simp
  have hJ : (J.card : ℝ) ≤
      Erdos615.Construction.netCard ((k + 1) * 2) r hr := by
    exact_mod_cast (by simpa using Finset.card_le_univ J)
  calc
    ((Erdos615.Construction.partSet ((k + 1) * 2) r (by omega) hr L
        s bpart).card : ℝ) ≤
      (∑ i ∈ J, Erdos615.Construction.multiplicity
        ((k + 1) * 2) r (by omega) hr L i : ℕ) := by exact_mod_cast hcard
    _ = ∑ i ∈ J, (Erdos615.Construction.multiplicity
        ((k + 1) * 2) r (by omega) hr L i : ℝ) := by norm_cast
    _ ≤ (L : ℝ) * (∑ i ∈ J, Erdos615.Construction.weight
        ((k + 1) * 2) r (by omega) hr i) + J.card := hmult
    _ ≤ (L : ℝ) * (4 * (D / 2) ^ ((k + 1) * 2)) +
        Erdos615.Construction.netCard ((k + 1) * 2) r hr := by
      gcongr

theorem rounded_triangleFree_card_bound (k L : ℕ) (r d e D t : ℝ)
    (hr : 0 < r) (he : 0 ≤ e) (hD : 1 ≤ D)
    (hgap : 4 - D ^ 2 < e ^ 2) (hclose : 2 * r + 2 * e < d)
    (hdroot : d < Real.sqrt 3) (q : Fin 3)
    (S : Finset (Fin (Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L + Erdos615.Construction.copyCard ((k + 1) * 2) r
      (by omega) hr L)))
    (hS : (finiteGeometricGraph d t (roundedLeftPosition k r hr L)
      (roundedRightPosition k r hr L q)).CliqueFreeOn S 3) :
    (S.card : ℝ) ≤ 8 * (L : ℝ) * (D / 2) ^ ((k + 1) * 2) +
      2 * Erdos615.Construction.netCard ((k + 1) * 2) r hr := by
  let s := roundedDecodedSet k r hr L S
  have hfalse := rounded_part_card_bound k L r d e D t hr he hD hgap hclose
    hdroot q S hS false
  have htrue := rounded_part_card_bound k L r d e D t hr he hD hgap hclose
    hdroot q S hS true
  have hparts :
      (Erdos615.Construction.partSet ((k + 1) * 2) r (by omega) hr L s false).card +
      (Erdos615.Construction.partSet ((k + 1) * 2) r (by omega) hr L s true).card =
        s.card := by
    simpa [Erdos615.Construction.partSet] using
      (Finset.card_filter_add_card_filter_not (s := s) (fun v ↦ v.1 = false))
  have hScard : S.card = s.card := by simp [s, roundedDecodedSet]
  rw [hScard, ← hparts]
  push_cast
  nlinarith

/-! ### Choosing the dimension and the rounding scale -/

/-- An elementary Bernoulli bound, used instead of an asymptotic exponential
limit when selecting the sphere dimension. -/
theorem one_sub_pow_le_reciprocal (x : ℝ) (n : ℕ)
    (hx0 : 0 < x) (hx1 : x < 1) :
    (1 - x) ^ n ≤ 1 / (1 + (n : ℝ) * x) := by
  let p : ℝ := 1 - x
  have hp0 : 0 < p := by simp [p, hx1]
  have hp1 : p ≤ 1 := by simp [p, hx0.le]
  let a : ℝ := 1 / p - 1
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact sub_nonneg.mpr ((one_le_div hp0).2 hp1)
  have hbern : 1 + (n : ℝ) * a ≤ (1 + a) ^ n :=
    one_add_mul_le_pow (by linarith : -2 ≤ a) n
  have hax : x ≤ a := by
    dsimp [a, p]
    rw [le_sub_iff_add_le, le_div_iff₀ hp0]
    nlinarith
  have hrecip : 1 + (n : ℝ) * x ≤ (1 / p) ^ n := by
    calc
      1 + (n : ℝ) * x ≤ 1 + (n : ℝ) * a := by
        gcongr
      _ ≤ (1 + a) ^ n := hbern
      _ = (1 / p) ^ n := by simp [a]
  have hpPow : 0 < p ^ n := pow_pos hp0 _
  have hprod : p ^ n * (1 + (n : ℝ) * x) ≤ 1 := by
    calc
      p ^ n * (1 + (n : ℝ) * x) ≤ p ^ n * (1 / p) ^ n :=
        mul_le_mul_of_nonneg_left hrecip hpPow.le
      _ = 1 := by
        rw [← mul_pow]
        field_simp
        simp
  have hden : 0 < 1 + (n : ℝ) * x := by positivity
  rw [show (1 - x) ^ n = p ^ n by rfl, div_eq_mul_inv,
    le_mul_inv_iff₀ hden]
  simpa [mul_comm] using hprod

/-- There are dimensions of the special form `16 R⁴` for which the
three-point concentration threshold is arbitrarily small. -/
theorem exists_dimension_parameter (eta : ℝ) (heta : 0 < eta) :
    ∃ R : ℕ, 0 < R ∧
      8 * (1 - 1 / (102400 * (R : ℝ) ^ 2)) ^ (16 * R ^ 4) < eta := by
  obtain ⟨R, hR⟩ := exists_nat_gt (max 1 (51200 / eta))
  have hR1 : 1 < (R : ℝ) := lt_of_le_of_lt (le_max_left _ _) hR
  have hR0 : 0 < R := by exact_mod_cast (by linarith : (0 : ℝ) < R)
  have hReta : 51200 / eta < (R : ℝ) :=
    (le_max_right _ _).trans_lt hR
  let x : ℝ := 1 / (102400 * (R : ℝ) ^ 2)
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by
    dsimp [x]
    rw [div_lt_one (by positivity)]
    nlinarith [sq_nonneg (R : ℝ)]
  have hpow := one_sub_pow_le_reciprocal x (16 * R ^ 4) hx0 hx1
  have hnx : ((16 * R ^ 4 : ℕ) : ℝ) * x = (R : ℝ) ^ 2 / 6400 := by
    dsimp [x]
    push_cast
    field_simp
    ring
  rw [hnx] at hpow
  have hfrac : 8 / eta < (R : ℝ) ^ 2 / 6400 := by
    rw [div_lt_div_iff₀ heta (by norm_num : (0 : ℝ) < 6400)]
    have hmul := mul_lt_mul_of_pos_left hReta heta
    field_simp at hmul ⊢
    nlinarith [hR1, sq_nonneg ((R : ℝ) - 1)]
  have hsmall : 8 * (1 / (1 + (R : ℝ) ^ 2 / 6400)) < eta := by
    rw [show 8 * (1 / (1 + (R : ℝ) ^ 2 / 6400)) =
      8 / (1 + (R : ℝ) ^ 2 / 6400) by ring,
      div_lt_iff₀ (by positivity)]
    have H : 8 < ((R : ℝ) ^ 2 / 6400) * eta :=
      (div_lt_iff₀ heta).mp hfrac
    nlinarith
  refine ⟨R, hR0, ?_⟩
  calc
    8 * (1 - 1 / (102400 * (R : ℝ) ^ 2)) ^ (16 * R ^ 4) =
        8 * (1 - x) ^ (16 * R ^ 4) := by rfl
    _ ≤ 8 * (1 / (1 + (R : ℝ) ^ 2 / 6400)) := by gcongr
    _ < eta := hsmall

/-- A finite counterexample at density `1 / 32`: every triangle-free vertex
set has fewer than `η n` vertices. -/
def IsCounterexample (η : ℝ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  G.CliqueFree 5 ∧
    (1 / 32 : ℝ) * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ) ∧
    ∀ S : Finset (Fin n), G.CliqueFreeOn (S : Set (Fin n)) 3 →
      (S.card : ℝ) < η * n

/-- The precise finite output required from the analytic part of the LRSS
construction.  The numerical assumptions are kept in the package so that
`K₅`-freeness is obtained from `geometricGraph_cliqueFree_five`, rather than
being assumed as part of the analytic input. -/
def GeometricWitness (η : ℝ) (N : ℕ) : Prop :=
  ∃ (k m : ℕ) (d t : ℝ) (w z : Fin m → ComplexSphere k),
    0 < m ∧ N ≤ m + m ∧
    0 ≤ d ∧ 0 < t ∧ 3 * d < Real.sqrt 3 ∧ d ^ 2 < 3 * t ∧
    (1 / 32 : ℝ) * ((m + m : ℕ) : ℝ) ^ 2 ≤
      ((finiteGeometricGraph d t w z).edgeFinset.card : ℝ) ∧
    ∀ S : Finset (Fin (m + m)),
      (finiteGeometricGraph d t w z).CliqueFreeOn
          (S : Set (Fin (m + m))) 3 →
        (S.card : ℝ) < η * (m + m : ℕ)

/-- The complete finite complex Bollobás--Erdős construction.  All
parameters are explicit; only the final integer scale `L` is chosen large
enough to absorb rounding errors and the requested lower bound on the order. -/
theorem geometricWitness_exists (η : ℝ) (hη : 0 < η) (N : ℕ) :
    GeometricWitness η N := by
  obtain ⟨R, hR, hRsmall⟩ := exists_dimension_parameter η hη
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hRone : 1 ≤ (R : ℝ) := by exact_mod_cast hR
  let k : ℕ := 8 * R ^ 4 - 1
  have hEight : 0 < 8 * R ^ 4 := by positivity
  have hdim : (k + 1) * 2 = 16 * R ^ 4 := by
    dsimp [k]
    omega
  let d : ℝ := 1 / (20 * R)
  let t : ℝ := 1 / (400 * (R : ℝ) ^ 2)
  let e : ℝ := 1 / (80 * R)
  let D : ℝ := 2 - 1 / (51200 * (R : ℝ) ^ 2)
  let r : ℝ := 1 / (40000 * (R : ℝ) ^ 2)
  have hd : 0 < d := by positivity
  have ht : 0 < t := by positivity
  have he : 0 ≤ e := by positivity
  have hr : 0 < r := by positivity
  have hrt : r < t := by
    dsimp [r, t]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_pos_of_pos hRreal]
  have hD : 1 ≤ D := by
    have H : 1 / (51200 * (R : ℝ) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [sq_nonneg ((R : ℝ) - 1)]
    dsimp [D]
    linarith
  have hgap : 4 - D ^ 2 < e ^ 2 := by
    dsimp [D, e]
    field_simp
    nlinarith [sq_pos_of_pos hRreal, sq_nonneg ((R : ℝ) ^ 2)]
  have hclose : 2 * r + 2 * e < d := by
    dsimp [r, e, d]
    field_simp
    nlinarith [hRone, sq_pos_of_pos hRreal]
  have hdroot : d < Real.sqrt 3 := by
    have hsqrt : 1 < Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
    have hd1 : d ≤ 1 / 20 := by
      dsimp [d]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hdsmall : 3 * d < Real.sqrt 3 := by
    have hsqrt : 1 < Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
    have hd1 : d ≤ 1 / 20 := by
      dsimp [d]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have hdt : d ^ 2 < 3 * t := by
    dsimp [d, t]
    field_simp
    nlinarith [sq_pos_of_pos hRreal]
  have hstrip : 12 * t * Real.sqrt ((((k + 1) * 2 : ℕ) : ℝ)) ≤ 1 / 4 := by
    have hsqrt : Real.sqrt (((k + 1) * 2 : ℕ) : ℝ) = 4 * (R : ℝ) ^ 2 := by
      rw [hdim]
      push_cast
      rw [show (16 : ℝ) * (R : ℝ) ^ 4 = (4 * (R : ℝ) ^ 2) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    rw [hsqrt]
    dsimp [t]
    field_simp
    nlinarith [sq_pos_of_pos hRreal]
  have hthreshold : 8 * (D / 2) ^ ((k + 1) * 2) < η := by
    rw [hdim]
    convert hRsmall using 1
    congr 2
    dsimp [D]
    field_simp
    ring
  obtain ⟨q, hq⟩ := exists_crossWeight_ge_quarter k r t hr hrt hstrip
  let K : ℕ := Erdos615.Construction.netCard ((k + 1) * 2) r hr
  have hK : 0 < K := Erdos615.Construction.netCard_pos ((k + 1) * 2) r
    (by omega) hr
  obtain ⟨L, hL⟩ := exists_nat_gt
    (max ((3 * K : ℕ) : ℝ) (max (N : ℝ) (2 * (K : ℝ) / η)))
  have hLKreal : (3 * K : ℕ) < (L : ℝ) :=
    (le_max_left _ _).trans_lt hL
  have hNLreal : (N : ℝ) < (L : ℝ) :=
    (le_max_left _ _).trans (le_max_right _ _) |>.trans_lt hL
  have hKηreal : 2 * (K : ℝ) / η < (L : ℝ) :=
    (le_max_right _ _).trans (le_max_right _ _) |>.trans_lt hL
  have hLpos : 0 < L := by
    have : (0 : ℝ) < L := by nlinarith [hK]
    exact_mod_cast this
  have hLK : 3 * K ≤ L := by exact_mod_cast hLKreal.le
  have hNL : N ≤ L := by exact_mod_cast hNLreal.le
  have hKη : 2 * (K : ℝ) < η * L := by
    rw [div_lt_iff₀ hη] at hKηreal
    simpa [mul_comm] using hKηreal
  let m : ℕ := Erdos615.Construction.copyCard ((k + 1) * 2) r
    (by omega) hr L
  let w : Fin m → ComplexSphere k := roundedLeftPosition k r hr L
  let z : Fin m → ComplexSphere k := roundedRightPosition k r hr L q
  have hLm : L ≤ m :=
    Erdos615.Construction.scale_le_copyCard ((k + 1) * 2) r (by omega) hr L
  have hmpos : 0 < m := hLpos.trans_le hLm
  have hmupper : m ≤ L + K :=
    Erdos615.Construction.copyCard_le_scale_add ((k + 1) * 2) r
      (by omega) hr L
  have hNorder : N ≤ m + m := by omega
  have hedgeL : (L : ℝ) ^ 2 / 4 ≤
      ((finiteGeometricGraph d t w z).edgeFinset.card : ℝ) := by
    calc
      (L : ℝ) ^ 2 / 4 = (L : ℝ) ^ 2 * (1 / 4) := by ring
      _ ≤ (L : ℝ) ^ 2 * crossWeight k r hr t q := by
        gcongr
      _ ≤ ((finiteGeometricGraph d t w z).edgeFinset.card : ℝ) := by
        simpa [w, z] using finiteGeometricGraph_edge_lower k r hr L d t q
  have hmupperReal : (m : ℝ) ≤ (L : ℝ) + K := by exact_mod_cast hmupper
  have hLKReal : 3 * (K : ℝ) ≤ L := by exact_mod_cast hLK
  have hedge : (1 / 32 : ℝ) * ((m + m : ℕ) : ℝ) ^ 2 ≤
      ((finiteGeometricGraph d t w z).edgeFinset.card : ℝ) := by
    calc
      (1 / 32 : ℝ) * ((m + m : ℕ) : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 / 4 := by
        push_cast
        nlinarith [sq_nonneg ((m : ℝ) - (L : ℝ)), sq_nonneg (L : ℝ)]
      _ ≤ ((finiteGeometricGraph d t w z).edgeFinset.card : ℝ) := hedgeL
  refine ⟨k, m, d, t, w, z, hmpos, hNorder, hd.le, ht, hdsmall, hdt, hedge, ?_⟩
  intro S hS
  have hcard := rounded_triangleFree_card_bound k L r d e D t hr he hD hgap
    hclose hdroot q S (by simpa [w, z] using hS)
  have hLmReal : (L : ℝ) ≤ m := by exact_mod_cast hLm
  have hstrict : 8 * (L : ℝ) * (D / 2) ^ ((k + 1) * 2) +
      2 * (K : ℝ) < η * (m + m : ℕ) := by
    push_cast
    have hfirst := mul_lt_mul_of_pos_right hthreshold (show (0 : ℝ) < L by exact_mod_cast hLpos)
    have hfirst' : 8 * (L : ℝ) * (D / 2) ^ ((k + 1) * 2) < η * L := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hfirst
    calc
      8 * (L : ℝ) * (D / 2) ^ ((k + 1) * 2) + 2 * (K : ℝ) <
          η * L + η * L := add_lt_add hfirst' hKη
      _ = η * (L + L) := by ring
      _ ≤ η * (m + m) := by
        gcongr
  exact hcard.trans_lt (by simpa [K] using hstrict)

/-- The deterministic geometric argument converts an analytic witness into
an ordinary finite counterexample. -/
theorem isCounterexample_finiteGeometricGraph {η : ℝ} {N k m : ℕ}
    {d t : ℝ} {w z : Fin m → ComplexSphere k}
    (hm : 0 < m) (hN : N ≤ m + m)
    (hd0 : 0 ≤ d) (ht : 0 < t) (hdsmall : 3 * d < Real.sqrt 3)
    (hdt : d ^ 2 < 3 * t)
    (hedge : (1 / 32 : ℝ) * ((m + m : ℕ) : ℝ) ^ 2 ≤
      ((finiteGeometricGraph d t w z).edgeFinset.card : ℝ))
    (hsmall : ∀ S : Finset (Fin (m + m)),
      (finiteGeometricGraph d t w z).CliqueFreeOn
          (S : Set (Fin (m + m))) 3 →
        (S.card : ℝ) < η * (m + m : ℕ)) :
    N ≤ m + m ∧ IsCounterexample η (finiteGeometricGraph d t w z) := by
  refine ⟨hN, ?_, hedge, hsmall⟩
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [finiteGeometricGraph, cliqueFree_map_iff]
  exact geometricGraph_cliqueFree_five w z hd0 ht hdsmall hdt

/-- The finite construction package needed to negate the eventual statement. -/
def CounterexamplePackage : Prop :=
  ∀ η : ℝ, 0 < η → ∀ N : ℕ,
    ∃ n : ℕ, N ≤ n ∧ ∃ G : SimpleGraph (Fin n), IsCounterexample η G

/-- The finite geometric witnesses, for arbitrary accuracy and lower bound on
the order, provide the counterexample package used by the quantifier layer. -/
theorem counterexamplePackage_of_geometricWitness
    (hgeom : ∀ η : ℝ, 0 < η → ∀ N : ℕ, GeometricWitness η N) :
    CounterexamplePackage := by
  intro η hη N
  obtain ⟨k, m, d, t, w, z, hm, hN, hd0, ht, hdsmall, hdt, hedge, hsmall⟩ :=
    hgeom η hη N
  refine ⟨m + m, hN, finiteGeometricGraph d t w z, ?_⟩
  exact (isCounterexample_finiteGeometricGraph hm hN hd0 ht hdsmall hdt hedge hsmall).2

/-- Pure quantifier conversion: arbitrarily large finite counterexamples at one
fixed positive density imply the exact negative answer in Problem 533. -/
theorem erdos_533_of_counterexamplePackage (hcounter : CounterexamplePackage) :
    ¬ ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), G.CliqueFree 5 →
        δ * (n : ℝ) ^ 2 ≤ G.edgeFinset.card →
          ∃ S : Finset (Fin n), c * n ≤ (S.card : ℝ) ∧
            G.CliqueFreeOn (S : Set (Fin n)) 3 := by
  intro h
  obtain ⟨c, hc, h_eventual⟩ := h (1 / 32) (by norm_num)
  rw [eventually_atTop] at h_eventual
  obtain ⟨N, hN⟩ := h_eventual
  obtain ⟨n, hn, G, hG5, hGedge, hGsmall⟩ := hcounter (c / 2) (by positivity) N
  obtain ⟨S, hScard, hSfree⟩ := hN n hn G hG5 (by simpa using hGedge)
  have hsmall := hGsmall S hSfree
  have hn_pos : 0 < (n : ℝ) := by
    by_contra hn0
    have hn_eq : n = 0 := by
      exact Nat.eq_zero_of_not_pos fun hn_nat => hn0 (by exact_mod_cast hn_nat)
    subst n
    exact (not_lt_of_ge (Nat.cast_nonneg S.card)) (by simpa using hsmall)
  nlinarith

/-- Erdős Problem 533 has a negative answer.  The graph family above has
fixed edge density `1/32`, is `K₅`-free, and has triangle-independence
number `o(n)`. -/
theorem erdos_533 :
    ¬ ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), G.CliqueFree 5 →
        δ * (n : ℝ) ^ 2 ≤ G.edgeFinset.card →
          ∃ S : Finset (Fin n), c * n ≤ (S.card : ℝ) ∧
            G.CliqueFreeOn (S : Set (Fin n)) 3 :=
  erdos_533_of_counterexamplePackage
    (counterexamplePackage_of_geometricWitness geometricWitness_exists)

end

#print axioms erdos_533
-- 'Erdos533.erdos_533' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos533
