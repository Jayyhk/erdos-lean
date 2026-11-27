import Mathlib

namespace Erdos184

/-
# Erdős Problem 184

Any graph on $n$ vertices can be decomposed into $O(n)$ many edge-disjoint cycles and edges.

The answer is **yes**: `erdos_184` gives an absolute constant $C > 0$ such that the edges of
every simple graph on $n$ vertices can be partitioned into at most $Cn$ parts, each the edge set
of a cycle or a single edge (`EdgeDecomposition`). Erdős and Gallai, who conjectured this, proved
that $O(n \log n)$ parts suffice.

Formalised by OpenAI in `openai/math` (`lean/OAI/Combinatorics/CycleDecomposition`), with the
preprint *A linear cycle-and-edge decomposition of every graph*; the 34 modules forming the closure
of `ErdosGallai.erdos_gallai` are flattened here in dependency order, with the upstream `OAI`
namespace merged into this file's `Erdos184`. `erdos_184` is added here: it restates upstream's
`erdos_gallai : MainStatement`, and adds no mathematical content.

Note that erdosproblems.com still lists this problem as open, pending human review of the
argument; what is recorded here is the machine-checked Lean development.

Declarations that `erdos_184` does not depend on have been removed.
-/

universe cycleUniverse1 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse2 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse3 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37 cycleUniverse38 cycleUniverse39 cycleUniverse4 cycleUniverse40 cycleUniverse41 cycleUniverse42 cycleUniverse43 cycleUniverse44 cycleUniverse45 cycleUniverse46 cycleUniverse47 cycleUniverse48 cycleUniverse49 cycleUniverse5 cycleUniverse50 cycleUniverse51 cycleUniverse52 cycleUniverse53 cycleUniverse54 cycleUniverse55 cycleUniverse56 cycleUniverse57 cycleUniverse58 cycleUniverse59 cycleUniverse6 cycleUniverse60 cycleUniverse61 cycleUniverse62 cycleUniverse63 cycleUniverse64 cycleUniverse65 cycleUniverse66 cycleUniverse67 cycleUniverse68 cycleUniverse69 cycleUniverse7 cycleUniverse70 cycleUniverse71 cycleUniverse72 cycleUniverse73 cycleUniverse74 cycleUniverse75 cycleUniverse76 cycleUniverse77 cycleUniverse78 cycleUniverse79 cycleUniverse8 cycleUniverse80 cycleUniverse81 cycleUniverse82 cycleUniverse83 cycleUniverse84 cycleUniverse85 cycleUniverse9 u

/-! ### Upstream module `Combinatorics/CycleDecomposition/Sampling.lean` -/

namespace ErdosGallai.Sampling
open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Finset _root_.Real

section BernoulliBounds
variable {Ω : Type cycleUniverse1} {I : Type cycleUniverse2} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma indicator_mem_Icc {Ω : Type cycleUniverse3} [_contextInstance1 : MeasurableSpace Ω] {X : Ω → ℝ} (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (ω : Ω) :
    X ω ∈ Set.Icc (0 : ℝ) 1 := by rcases hX ω with h | h <;> simp [h]

lemma mgf_indicator {X : Ω → ℝ} (hm : Measurable X)
    (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (p t : ℝ) (hp : ∫ ω, X ω ∂μ = p) :
    mgf X μ t = 1 + p * (exp t - 1) := by
  have hXi : Integrable X μ := Integrable.of_mem_Icc 0 1 hm.aemeasurable
    (ae_of_all _ (indicator_mem_Icc hX))
  have heq : (fun ω => exp (t * X ω)) = fun ω => (1 : ℝ) + (exp t - 1) * X ω := by
    funext ω
    rcases hX ω with h | h <;> simp [h]
  rw [mgf, heq, integral_add (integrable_const _) (hXi.const_mul _), integral_const_mul,
    hp, integral_const]
  simp [mul_comm]

lemma mgf_indicator_sum_bound {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p t : ℝ) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    mgf (∑ i ∈ s, X i) μ t ≤ exp ((s.card : ℝ) * p * (exp t - 1)) := by
  by_cases hs : s.Nonempty
  swap
  · have he := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]
  rw [hi.mgf_sum hm]
  have heq : (∏ i ∈ s, mgf (X i) μ t) = (1 + p * (exp t - 1)) ^ s.card := by
    simp_rw [mgf_indicator (hm _) (hX _) p t (hp _)]
    simp
  rw [heq]
  have hn : 0 ≤ 1 + p * (exp t - 1) := by
    obtain ⟨i, _⟩ := hs
    rw [← mgf_indicator (hm i) (hX i) p t (hp i)]
    exact mgf_nonneg
  calc
    (1 + p * (exp t - 1)) ^ s.card ≤ exp (p * (exp t - 1)) ^ s.card :=
      pow_le_pow_left₀ hn (by linarith [add_one_le_exp (p * (exp t - 1))]) _
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

lemma exp_neg_half_bound : exp (-(1 / 2 : ℝ)) ≤ 5 / 8 := by
  have he : exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) = exp 1 := by
    rw [← exp_add]; norm_num
  have hlow : (8 / 5 : ℝ) ≤ exp (1 / 2 : ℝ) := by
    nlinarith [exp_one_gt_d9, exp_pos (1 / 2 : ℝ)]
  rw [exp_neg]
  exact (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by norm_num at *; exact hlow)

lemma exp_half_bound : exp (1 / 2 : ℝ) ≤ 5 / 3 := by
  have he : exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) = exp 1 := by
    rw [← exp_add]; norm_num
  nlinarith [exp_one_lt_d9, exp_pos (1 / 2 : ℝ)]

theorem bernoulli_sum_lower_tail {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | (∑ i ∈ s, X i ω) ≤ p * s.card / 2} ≤ exp (-p * s.card / 8) := by
  have hInt : Integrable (fun ω => exp (-(1 / 2 : ℝ) * (∑ i ∈ s, X i) ω)) μ :=
    hi.integrable_exp_mul_sum hm (fun i _ => integrable_exp_mul_of_mem_Icc
      (hm i).aemeasurable (ae_of_all _ (indicator_mem_Icc (hX i))))
  have hb := measure_le_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (p * s.card / 2)
    (by norm_num : -(1 / 2 : ℝ) ≤ 0) hInt
  simp only [Finset.sum_apply] at hb
  apply hb.trans
  calc
    _ ≤ exp (-(-(1 / 2 : ℝ)) * (p * s.card / 2)) *
        exp ((s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      exact mul_le_mul_of_nonneg_left (mgf_indicator_sum_bound s hm hi hX p _ hp) (exp_pos _).le
    _ = exp (p * s.card / 4 + (s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_neg_half_bound
        (mul_nonneg (Nat.cast_nonneg s.card) hp0)]

theorem bernoulli_sum_upper_tail {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | 2 * p * s.card ≤ ∑ i ∈ s, X i ω} ≤ exp (-p * s.card / 3) := by
  have hInt : Integrable (fun ω => exp ((1 / 2 : ℝ) * (∑ i ∈ s, X i) ω)) μ :=
    hi.integrable_exp_mul_sum hm (fun i _ => integrable_exp_mul_of_mem_Icc
      (hm i).aemeasurable (ae_of_all _ (indicator_mem_Icc (hX i))))
  have hb := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (2 * p * s.card)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hInt
  simp only [Finset.sum_apply] at hb
  apply hb.trans
  calc
    _ ≤ exp (-(1 / 2 : ℝ) * (2 * p * s.card)) *
        exp ((s.card : ℝ) * p * (exp (1 / 2 : ℝ) - 1)) := by
      exact mul_le_mul_of_nonneg_left (mgf_indicator_sum_bound s hm hi hX p _ hp) (exp_pos _).le
    _ = exp (-p * s.card + (s.card : ℝ) * p * (exp (1 / 2 : ℝ) - 1)) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_half_bound
        (mul_nonneg (Nat.cast_nonneg s.card) hp0)]

end BernoulliBounds

section ProductSamples
variable {V : Type cycleUniverse4} [Fintype V] [DecidableEq V]

noncomputable def sampleMeasure (V : Type cycleUniverse5) [Fintype V] (p : unitInterval) : Measure (V → Bool) :=
  Measure.pi (fun _ : V => bernoulliMeasure true false p)

instance sampleMeasure_probability (p : unitInterval) : IsProbabilityMeasure (sampleMeasure V p) := by
  unfold sampleMeasure
  infer_instance

def sampleVertices (ω : V → Bool) : Finset V := Finset.univ.filter (fun v => ω v = true)

def sampleIndicator (v : V) (ω : V → Bool) : ℝ := if ω v then 1 else 0

lemma sampleIndicator_measurable {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (v : V) : Measurable (sampleIndicator v) :=
  measurable_of_finite _

lemma sampleIndicator_values {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (v : V) (ω : V → Bool) :
    sampleIndicator v ω = 0 ∨ sampleIndicator v ω = 1 := by
  simp only [sampleIndicator]; split <;> simp

lemma sampleIndicator_indep {V : Type cycleUniverse8} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (p : unitInterval) :
    iIndepFun (sampleIndicator (V := V)) (sampleMeasure V p) := by
  exact iIndepFun_pi (X := fun _ : V => fun b : Bool => if b then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)

lemma sampleIndicator_integral {V : Type cycleUniverse9} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (p : unitInterval) (v : V) :
    ∫ ω, sampleIndicator v ω ∂sampleMeasure V p = (p : ℝ) := by
  have hl := (measurePreserving_eval (fun _ : V => bernoulliMeasure true false p) v).hasLaw
  have hi := hl.integral_comp (f := fun b : Bool => if b then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable
  simpa [sampleMeasure, sampleIndicator, integral_bernoulliMeasure] using hi

lemma sampleIndicator_sum (S : Finset V) (ω : V → Bool) :
    (∑ v ∈ S, sampleIndicator v ω) = ((S ∩ sampleVertices ω).card : ℝ) := by
  simp only [sampleIndicator,  Finset.sum_boole]
  congr 2
  ext v
  simp [sampleVertices]

lemma sample_card_lower_tail (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | ((S ∩ sampleVertices ω).card : ℝ) ≤ (p : ℝ) * S.card / 2} ≤
      exp (-(p : ℝ) * S.card / 8) := by
  simpa only [sampleIndicator_sum] using bernoulli_sum_lower_tail S
    sampleIndicator_measurable (sampleIndicator_indep p) sampleIndicator_values
    (p : ℝ) p.property.1 (sampleIndicator_integral p)

lemma sample_card_upper_tail (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | 2 * (p : ℝ) * S.card ≤ ((S ∩ sampleVertices ω).card : ℝ)} ≤
      exp (-(p : ℝ) * S.card / 3) := by
  simpa only [sampleIndicator_sum] using bernoulli_sum_upper_tail S
    sampleIndicator_measurable (sampleIndicator_indep p) sampleIndicator_values
    (p : ℝ) p.property.1 (sampleIndicator_integral p)

lemma sample_miss_probability (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | Disjoint S (sampleVertices ω)} = (1 - (p : ℝ)) ^ S.card := by
  have heq : {ω | Disjoint S (sampleVertices ω)} =
      Set.univ.pi (fun v : V => if v ∈ S then {false} else Set.univ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    simp only [Finset.disjoint_left, sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h v
      by_cases hv : v ∈ S
      · simp only [hv, ↓reduceIte, Set.mem_singleton_iff]
        cases hi : ω v <;> simp_all
      · simp [hv]
    · intro h v hv ht
      have := h v
      simp_all
  rw [heq, Measure.real, sampleMeasure, Measure.pi_pi, ENNReal.toReal_prod]
  have hpv (v : V) :
      ((bernoulliMeasure true false p) (if v ∈ S then {false} else Set.univ)).toReal =
        if v ∈ S then 1 - (p : ℝ) else 1 := by
    by_cases hv : v ∈ S
    · simp only [hv, ↓reduceIte]
      change (bernoulliMeasure true false p).real {false} = _
      exact bernoulliMeasure_real_apply_of_notMem_of_mem p (by simp) (by simp) (by simp)
    · simp [hv]
  simp_rw [hpv]
  simp

lemma sample_miss_bound (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | Disjoint S (sampleVertices ω)} ≤ exp (-(p : ℝ) * S.card) := by
  rw [sample_miss_probability]
  calc
    (1 - (p : ℝ)) ^ S.card ≤ exp (-(p : ℝ)) ^ S.card := by
      apply pow_le_pow_left₀ (sub_nonneg.mpr p.property.2)
      linarith [add_one_le_exp (-(p : ℝ))]
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

lemma sample_contains_probability (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p) {ω | S ⊆ sampleVertices ω} = ENNReal.ofReal (p : ℝ) ^ S.card := by
  have heq : {ω | S ⊆ sampleVertices ω} =
      Set.univ.pi (fun v : V => if v ∈ S then {true} else Set.univ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    simp only [Finset.subset_iff, sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h v
      by_cases hv : v ∈ S <;> simp_all
    · intro h v hv
      simpa [hv] using h v
  rw [heq, sampleMeasure, Measure.pi_pi]
  have hpv (v : V) :
      bernoulliMeasure true false p (if v ∈ S then {true} else Set.univ) =
        if v ∈ S then ENNReal.ofReal (p : ℝ) else 1 := by
    by_cases hv : v ∈ S
    · simp only [hv, ↓reduceIte]
      rw [bernoulliMeasure_apply_of_mem_of_notMem p (by simp) (by simp) (by simp)]
      exact ENNReal.ofReal_coe_nnreal.symm
    · simp [hv]
  simp_rw [hpv]
  simp

lemma sample_contains_real_probability (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | S ⊆ sampleVertices ω} = (p : ℝ) ^ S.card := by
  rw [Measure.real, sample_contains_probability, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal p.property.1]

lemma sample_blocks_independent {I : Type cycleUniverse10} (p : unitInterval) (S : I → Finset V)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    iIndepSet (fun i => {ω | S i ⊆ sampleVertices ω}) (sampleMeasure V p) := by
  classical
  rw [iIndepSet_iff_meas_biInter (fun _ => MeasurableSet.of_discrete)]
  intro t
  have heq : (⋂ i ∈ t, {ω | S i ⊆ sampleVertices ω}) =
      {ω | t.biUnion S ⊆ sampleVertices ω} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Finset.biUnion_subset]
  rw [heq, sample_contains_probability, Finset.card_biUnion]
  · simp_rw [sample_contains_probability]
    exact (Finset.prod_pow_eq_pow_sum t (fun i => (S i).card) _).symm
  · intro i _ j _ hij
    exact hS hij

noncomputable def blockIndicator (S : Finset V) : (V → Bool) → ℝ :=
  {ω | S ⊆ sampleVertices ω}.indicator (fun _ => 1)

lemma blockIndicator_values (S : Finset V) (ω : V → Bool) :
    blockIndicator S ω = 0 ∨ blockIndicator S ω = 1 := by
  classical
  by_cases h : S ⊆ sampleVertices ω <;> simp [blockIndicator, h]

lemma blockIndicator_integral (p : unitInterval) (S : Finset V) :
    ∫ ω, blockIndicator S ω ∂sampleMeasure V p = (p : ℝ) ^ S.card := by
  rw [blockIndicator, integral_indicator_const _ MeasurableSet.of_discrete,
    sample_contains_real_probability]
  simp

lemma sample_blocks_lower_tail {I : Type cycleUniverse11} (p : unitInterval) (S : I → Finset V)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) (d : ℕ)
    (hd : ∀ i, (S i).card = d) (t : Finset I) :
    (sampleMeasure V p).real {ω | (∑ i ∈ t, blockIndicator (S i) ω) ≤
      (p : ℝ) ^ d * t.card / 2} ≤ exp (-(p : ℝ) ^ d * t.card / 8) := by
  apply bernoulli_sum_lower_tail t (fun _ => measurable_of_finite _)
    (sample_blocks_independent p S hS).iIndepFun_indicator
    (fun i => blockIndicator_values (S i)) ((p : ℝ) ^ d) (pow_nonneg p.property.1 _)
  intro i
  change (∫ ω, blockIndicator (S i) ω ∂sampleMeasure V p) = _
  rw [blockIndicator_integral, hd]

lemma sample_weight_sum (A : Finset V) (w : V → ℝ) (ω : V → Bool) :
    (∑ v ∈ A ∩ sampleVertices ω, w v) = ∑ v ∈ A, w v * sampleIndicator v ω := by
  rw [← Finset.sum_ite_mem]
  apply Finset.sum_congr rfl
  intro v _
  simp only [sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and, sampleIndicator]
  split <;> simp_all

lemma sample_weight_integral (p : unitInterval) (A : Finset V) (w : V → ℝ) :
    ∫ ω, (∑ v ∈ A ∩ sampleVertices ω, w v) ∂sampleMeasure V p =
      (p : ℝ) * ∑ v ∈ A, w v := by
  simp_rw [sample_weight_sum]
  rw [integral_finsetSum A (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_const_mul, sampleIndicator_integral]
  rw [← Finset.sum_mul, mul_comm]

lemma nonnegative_markov_quarter {Ω : Type cycleUniverse12} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hi : Integrable X μ) (hn : ∀ ω, 0 ≤ X ω) {B : ℝ} (hB : 0 < B)
    (he : ∫ ω, X ω ∂μ ≤ B) : μ.real {ω | 4 * B < X ω} ≤ 1 / 4 := by
  have hb := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hn) hi (4 * B)
  have hm : μ.real {ω | 4 * B < X ω} ≤ μ.real {ω | 4 * B ≤ X ω} :=
    measureReal_mono (fun ω (h : 4 * B < X ω) => h.le)
  nlinarith [mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 4 * B)]

lemma sample_weight_markov (p : unitInterval) (hp : 0 < (p : ℝ))
    (A : Finset V) (w : V → ℝ) (hw : ∀ v ∈ A, 0 ≤ w v)
    {B : ℝ} (hB : 0 < B) (hs : ∑ v ∈ A, w v ≤ B) :
    (sampleMeasure V p).real {ω | 4 * (p : ℝ) * B < ∑ v ∈ A ∩ sampleVertices ω, w v} ≤
      1 / 4 := by
  have ht := nonnegative_markov_quarter (μ := sampleMeasure V p)
    (X := fun ω => ∑ v ∈ A ∩ sampleVertices ω, w v) Integrable.of_finite
    (fun ω => Finset.sum_nonneg (fun v hv => hw v (Finset.mem_inter.mp hv).1))
    (mul_pos hp hB) (by rw [sample_weight_integral]; exact mul_le_mul_of_nonneg_left hs hp.le)
  simpa only [mul_assoc] using ht

theorem exists_small_weighted_hitting_set {I : Type cycleUniverse13} (A : Finset V) (hA : A.Nonempty)
    (good : Finset I) (K : I → Finset V) (hKA : ∀ i ∈ good, K i ⊆ A)
    (w : V → ℝ) (hw : ∀ v ∈ A, 0 ≤ w v) {B d : ℝ}
    (hB : 0 < B) (hs : ∑ v ∈ A, w v ≤ B)
    (hd : ∀ i ∈ good, d ≤ (K i).card)
    (q : unitInterval) (hq : 0 < (q : ℝ))
    (hmiss : (good.card : ℝ) * exp (-(q : ℝ) * d) < 1 / 2) :
    ∃ S : Finset V, S ⊆ A ∧ (S.card : ℝ) ≤ 4 * (q : ℝ) * A.card ∧
      (∑ v ∈ S, w v) ≤ 4 * (q : ℝ) * B ∧ ∀ i ∈ good, ¬Disjoint (K i) S := by
  classical
  let μ := sampleMeasure V q
  let E₁ : Set (V → Bool) := {ω | 4 * (q : ℝ) * A.card < ((A ∩ sampleVertices ω).card : ℝ)}
  let E₂ : Set (V → Bool) := {ω | 4 * (q : ℝ) * B < ∑ v ∈ A ∩ sampleVertices ω, w v}
  let E₃ : Set (V → Bool) := ⋃ i ∈ good, {ω | Disjoint (K i) (sampleVertices ω)}
  have h₁ : μ.real E₁ ≤ 1 / 4 := by
    have ht := sample_weight_markov q hq A (fun _ => (1 : ℝ)) (by simp)
      (show (0 : ℝ) < A.card by exact_mod_cast hA.card_pos) (by simp)
    simpa [μ, E₁] using ht
  have h₂ : μ.real E₂ ≤ 1 / 4 := sample_weight_markov q hq A w hw hB hs
  have h₃ : μ.real E₃ < 1 / 2 := by
    calc
      μ.real E₃ ≤ ∑ i ∈ good, μ.real {ω | Disjoint (K i) (sampleVertices ω)} :=
        measureReal_biUnion_finset_le good _
      _ ≤ ∑ i ∈ good, exp (-(q : ℝ) * d) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (sample_miss_bound q (K i)).trans (exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left (hd i hi) (neg_nonpos.mpr hq.le)))
      _ = (good.card : ℝ) * exp (-(q : ℝ) * d) := by simp
      _ < _ := hmiss
  have hf : μ.real (E₁ ∪ E₂ ∪ E₃) < 1 := by
    have ha := measureReal_union_le (μ := μ) (E₁ ∪ E₂) E₃
    have hb := measureReal_union_le (μ := μ) E₁ E₂
    linarith
  have hne : E₁ ∪ E₂ ∪ E₃ ≠ Set.univ := by
    intro h
    rw [h] at hf
    have hu : μ.real Set.univ = 1 := by simp [μ, Measure.real]
    linarith
  obtain ⟨ω, hω⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  have hn := hω
  simp only [Set.mem_union, not_or] at hn
  refine ⟨A ∩ sampleVertices ω, Finset.inter_subset_left, le_of_not_gt hn.1.1,
    le_of_not_gt hn.1.2, ?_⟩
  intro i hi hdj
  apply hn.2
  simp only [E₃, Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨i, hi, ?_⟩
  apply Finset.disjoint_left.mpr
  intro v hv hvs
  exact Finset.disjoint_left.mp hdj hv (Finset.mem_inter.mpr ⟨hKA i hi hv, hvs⟩)

end ProductSamples

section FiniteUnion
variable {Ω : Type cycleUniverse14} {I : Type cycleUniverse15} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma exists_avoiding_finite_events (s : Finset I) (E : I → Set Ω)
    (h : ∑ i ∈ s, μ.real (E i) < 1) : ∃ ω, ∀ i ∈ s, ω ∉ E i := by
  by_contra hn
  push Not at hn
  have cover : (⋃ i ∈ s, E i) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, hi, he⟩ := hn ω
    exact ⟨i, hi, he⟩
  have hu := measureReal_biUnion_finset_le (μ := μ) s E
  rw [cover] at hu
  have : μ.real Set.univ = 1 := by simp [Measure.real]
  rw [this] at hu
  linarith

end FiniteUnion
end ErdosGallai.Sampling
/-! ### Upstream module `Combinatorics/CycleDecomposition/SamplingCuts.lean` -/

namespace ErdosGallai.Sampling
open _root_.Finset _root_.MeasureTheory _root_.ProbabilityTheory _root_.Real
open scoped symmDiff
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

noncomputable def cutColor (e : V × V) : ℕ :=
  (Fintype.equivFin V e.1).val + (Fintype.equivFin V e.2).val

lemma cutColor_lt {V : Type cycleUniverse2} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (e : V × V) : cutColor e < 2 * Fintype.card V := by
  have h₁ := (Fintype.equivFin V e.1).isLt
  have h₂ := (Fintype.equivFin V e.2).isLt
  dsimp [cutColor]
  omega

lemma same_cutColor_blocks_disjoint (A B : Finset V) (hAB : Disjoint A B)
    {e f : V × V} (he₁ : e.1 ∈ A) (he₂ : e.2 ∈ B)
    (hf₁ : f.1 ∈ A) (hf₂ : f.2 ∈ B) (hc : cutColor e = cutColor f) (hef : e ≠ f) :
    Disjoint ({e.1, e.2} : Finset V) {f.1, f.2} := by
  have h₁ : e.1 ≠ f.1 := by
    intro h
    have ht : e.2 = f.2 := (Fintype.equivFin V).injective (Fin.ext (by
      dsimp [cutColor] at hc
      rw [h] at hc
      omega))
    exact hef (Prod.ext h ht)
  have h₂ : e.2 ≠ f.2 := by
    intro h
    have ht : e.1 = f.1 := (Fintype.equivFin V).injective (Fin.ext (by
      dsimp [cutColor] at hc
      rw [h] at hc
      omega))
    exact hef (Prod.ext ht h)
  have h₃ : e.1 ≠ f.2 := fun h => Finset.disjoint_left.mp hAB he₁ (h ▸ hf₂)
  have h₄ : e.2 ≠ f.1 := fun h => Finset.disjoint_left.mp hAB hf₁ (h ▸ he₂)
  simp [Finset.disjoint_left, h₁, h₂, h₃, h₄]

lemma blockIndicator_sum_card (E : Finset (V × V)) (ω : V → Bool) :
    (∑ e ∈ E, blockIndicator ({e.1, e.2} : Finset V) ω) =
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) := by
  classical
  simp only [blockIndicator, Set.indicator_apply, Set.mem_ofPred_eq,
    Finset.insert_subset_iff, Finset.singleton_subset_iff]
  exact Finset.sum_boole _ _

lemma sampled_matching_lower_tail (p : unitInterval) (A B : Finset V) (hAB : Disjoint A B)
    (E : Finset (V × V)) (hE : ∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ B)
    (c : ℕ) (hc : ∀ e ∈ E, cutColor e = c) :
    (sampleMeasure V p).real {ω |
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) ≤
        (p : ℝ) ^ 2 * E.card / 2} ≤ exp (-(p : ℝ) ^ 2 * E.card / 8) := by
  classical
  let S : E → Finset V := fun e => {e.val.1, e.val.2}
  have hS : Pairwise fun e f : E => Disjoint (S e) (S f) := by
    intro e f hef
    exact same_cutColor_blocks_disjoint A B hAB (hE e e.property).1 (hE e e.property).2
      (hE f f.property).1 (hE f f.property).2 ((hc e e.property).trans (hc f f.property).symm)
      (fun h => hef (Subtype.ext h))
  have hd : ∀ e : E, (S e).card = 2 := by
    intro e
    apply Finset.card_pair
    intro h
    exact Finset.disjoint_left.mp hAB (hE e e.property).1 (h ▸ (hE e e.property).2)
  have ht := sample_blocks_lower_tail p S hS 2 hd Finset.univ
  have heq (ω : V → Bool) : (∑ e : E, blockIndicator (S e) ω) =
      (∑ e ∈ E, blockIndicator ({e.1, e.2} : Finset V) ω) := by
    exact Finset.sum_attach E (fun e => blockIndicator ({e.1, e.2} : Finset V) ω)
  simp_rw [heq, blockIndicator_sum_card] at ht
  simpa using ht

lemma sum_cutColor_class_card (E : Finset (V × V)) :
    (∑ i ∈ Finset.range (2 * Fintype.card V), (E.filter (fun e => cutColor e = i)).card) =
      E.card := by
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  apply Finset.filter_true_of_mem
  intro e _
  exact Finset.mem_range.mpr (cutColor_lt e)

theorem sampled_bipartite_cut_lower_tail (p : unitInterval)
    (hr : 0 < Fintype.card V) (A B : Finset V) (hAB : Disjoint A B)
    (E : Finset (V × V)) (hE : ∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ B) :
    (sampleMeasure V p).real {ω |
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) <
        (p : ℝ) ^ 2 * E.card / 4} ≤
      2 * (Fintype.card V : ℝ) * exp (-(p : ℝ) ^ 2 * E.card / (32 * Fintype.card V)) := by
  classical
  let r : ℝ := Fintype.card V
  have hrR : 0 < r := by
    change 0 < (Fintype.card V : ℝ)
    exact_mod_cast hr
  let colors := Finset.range (2 * Fintype.card V)
  let C (i : ℕ) := E.filter (fun e => cutColor e = i)
  let m (i : ℕ) : ℝ := (C i).card
  let L := colors.filter (fun i => (E.card : ℝ) / (4 * r) ≤ m i)
  let retained (i : ℕ) (ω : V → Bool) : ℝ :=
    ((C i |>.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ)
  have hsum : ∑ i ∈ colors, m i = (E.card : ℝ) := by
    dsimp [colors, m, C]
    exact_mod_cast sum_cutColor_class_card E
  have hretain (ω : V → Bool) : ∑ i ∈ colors, retained i ω =
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) := by
    have ht := sum_cutColor_class_card
      (E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω))
    simpa only [retained, C, colors, Finset.filter_filter, and_comm, Nat.cast_sum] using
      (show (∑ i ∈ Finset.range (2 * Fintype.card V),
        (((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).filter
          (fun e => cutColor e = i)).card : ℝ)) = _ by exact_mod_cast ht)
  have hlarge : (E.card : ℝ) / 2 ≤ ∑ i ∈ L, m i := by
    have hb : ∑ i ∈ colors, m i ≤
        ∑ i ∈ colors, ((if i ∈ L then m i else 0) + (E.card : ℝ) / (4 * r)) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hiL : i ∈ L
      · simp only [hiL, ↓reduceIte]
        have : 0 ≤ (E.card : ℝ) / (4 * r) := by positivity
        linarith
      · have hiM : m i < (E.card : ℝ) / (4 * r) := by
          simpa only [L, Finset.mem_filter, hi, true_and, not_le] using hiL
        simp only [hiL, ↓reduceIte, zero_add]
        exact hiM.le
    rw [hsum, Finset.sum_add_distrib, Finset.sum_ite_mem] at hb
    have hsub : colors ∩ L = L := Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
    rw [hsub] at hb
    have hconst : ∑ _i ∈ colors, (E.card : ℝ) / (4 * r) = (E.card : ℝ) / 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, colors, Finset.card_range, Nat.cast_mul,
        Nat.cast_ofNat]
      dsimp [r] at *
      field_simp
      ; ring
    rw [hconst] at hb
    linarith
  let Bad (i : ℕ) : Set (V → Bool) :=
    {ω | retained i ω ≤ (p : ℝ) ^ 2 * m i / 2}
  have hcover : {ω |
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) <
        (p : ℝ) ^ 2 * E.card / 4} ⊆ ⋃ i ∈ L, Bad i := by
    intro ω hfail
    by_contra hnot
    have hiok : ∀ i ∈ L, (p : ℝ) ^ 2 * m i / 2 ≤ retained i ω := by
      intro i hi
      have hn : ω ∉ Bad i := fun h => hnot (Set.mem_iUnion.mpr ⟨i,
        Set.mem_iUnion.mpr ⟨hi, h⟩⟩)
      exact (lt_of_not_ge hn).le
    have hs₁ : (p : ℝ) ^ 2 / 2 * (∑ i ∈ L, m i) ≤ ∑ i ∈ L, retained i ω := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ = (p : ℝ) ^ 2 * m i / 2 := by ring
        _ ≤ retained i ω := hiok i hi
    have hs₂ : (∑ i ∈ L, retained i ω) ≤ ∑ i ∈ colors, retained i ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => Nat.cast_nonneg _)
    rw [hretain] at hs₂
    have hs₃ := mul_le_mul_of_nonneg_left hlarge (by positivity : 0 ≤ (p : ℝ) ^ 2 / 2)
    change ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) <
      (p : ℝ) ^ 2 * E.card / 4 at hfail
    nlinarith
  have hbad (i : ℕ) (hi : i ∈ L) : (sampleMeasure V p).real (Bad i) ≤
      exp (-(p : ℝ) ^ 2 * E.card / (32 * r)) := by
    have ht := sampled_matching_lower_tail p A B hAB (C i)
      (fun e he => hE e (Finset.mem_filter.mp he).1) i
      (fun e he => (Finset.mem_filter.mp he).2)
    have hm : (E.card : ℝ) / (4 * r) ≤ m i := (Finset.mem_filter.mp hi).2
    have he : -(p : ℝ) ^ 2 * m i / 8 ≤ -(p : ℝ) ^ 2 * E.card / (32 * r) := by
      have ht := mul_le_mul_of_nonpos_left hm (neg_nonpos.mpr (sq_nonneg (p : ℝ)))
      calc
        _ ≤ (-(p : ℝ) ^ 2 * ((E.card : ℝ) / (4 * r))) / 8 := by linarith
        _ = _ := by ring
    exact ht.trans (exp_le_exp.mpr he)
  calc
    _ ≤ (sampleMeasure V p).real (⋃ i ∈ L, Bad i) := measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ i ∈ L, (sampleMeasure V p).real (Bad i) := measureReal_biUnion_finset_le L Bad
    _ ≤ ∑ i ∈ L, exp (-(p : ℝ) ^ 2 * E.card / (32 * r)) := Finset.sum_le_sum hbad
    _ = (L.card : ℝ) * exp (-(p : ℝ) ^ 2 * E.card / (32 * r)) := by simp
    _ ≤ 2 * r * exp (-(p : ℝ) ^ 2 * E.card / (32 * r)) := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      have ht := Finset.card_le_card (Finset.filter_subset (fun i => (E.card : ℝ) / (4 * r) ≤ m i) colors)
      have ht' : L.card ≤ 2 * Fintype.card V := by
        simpa only [colors, Finset.card_range] using ht
      change (L.card : ℝ) ≤ 2 * (Fintype.card V : ℝ)
      exact_mod_cast ht'

def neighborsIn (P : SimpleGraph V) [DecidableRel P.Adj] (v : V) (A : Finset V) :=
  A.filter (P.Adj v)

lemma card_interedges_eq_sum_neighborsIn {V : Type cycleUniverse3} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    (A B : Finset V) : (P.interedges A B).card = ∑ v ∈ A, (neighborsIn P v B).card := by
  simp only [SimpleGraph.interedges, Rel.interedges, neighborsIn, Finset.card_filter]
  rw [Finset.sum_product]

lemma neighborsIn_partition_card {V : Type cycleUniverse4} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    (v : V) (A W : Finset V) (hAW : A ⊆ W) :
    (neighborsIn P v W).card = (neighborsIn P v A).card + (neighborsIn P v (W \ A)).card := by
  have hu : neighborsIn P v W = neighborsIn P v A ∪ neighborsIn P v (W \ A) := by
    ext x; simp only [neighborsIn, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · intro ⟨hx, ha⟩
      by_cases hxA : x ∈ A
      · exact Or.inl ⟨hxA, ha⟩
      · exact Or.inr ⟨⟨hx, hxA⟩, ha⟩
    · rintro (⟨hx, ha⟩ | ⟨⟨hx, _⟩, ha⟩)
      · exact ⟨hAW hx, ha⟩
      · exact ⟨hx, ha⟩
  rw [hu, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2 (Finset.mem_filter.mp hx).1

lemma interedges_sym2_injective {V : Type cycleUniverse5} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    (A B : Finset V) (hAB : Disjoint A B) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges A B : Set (V × V)) := by
  intro e he f hf hef
  rcases Sym2.mk_eq_mk_iff.mp hef with h | h
  · exact h
  · exact False.elim <| Finset.disjoint_left.mp hAB (P.mem_interedges_iff.mp he).1
      ((congrArg Prod.fst h).symm ▸ (P.mem_interedges_iff.mp hf).2.1)

lemma cut_perturbation_card (P : SimpleGraph V) [DecidableRel P.Adj]
    (W A T : Finset V) (_hAW : A ⊆ W) (_hTW : T ⊆ W) :
    (P.interedges T (W \ T)).card ≤ (P.interedges A (W \ A)).card +
      Fintype.card V * (A ∆ T).card := by
  classical
  let f := fun e : V × V => s(e.1, e.2)
  let E := (P.interedges A (W \ A)).image f
  let D := (((A ∆ T) ×ˢ (Finset.univ : Finset V)).image f)
  have hinj := interedges_sym2_injective P T (W \ T) (Finset.disjoint_left.mpr (by
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 hx))
  have hsub : (P.interedges T (W \ T)).image f ⊆ E ∪ D := by
    intro e he
    obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_image.mp he
    rcases P.mem_interedges_iff.mp hxy with ⟨hxT, hyWT, hxy⟩
    obtain ⟨hyW, hyT⟩ := Finset.mem_sdiff.mp hyWT
    by_cases hxA : x ∈ A
    · by_cases hyA : y ∈ A
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨(y,x), Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
        · exact Finset.mem_symmDiff.mpr (Or.inl ⟨hyA, hyT⟩)
        · exact Sym2.eq_swap
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨(x,y), P.mem_interedges_iff.mpr
          ⟨hxA, Finset.mem_sdiff.mpr ⟨hyW, hyA⟩, hxy⟩, rfl⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(x,y), Finset.mem_product.mpr
        ⟨Finset.mem_symmDiff.mpr (Or.inr ⟨hxT, hxA⟩), Finset.mem_univ _⟩, rfl⟩
  calc
    _ = ((P.interedges T (W \ T)).image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (E ∪ D).card := Finset.card_le_card hsub
    _ ≤ E.card + D.card := Finset.card_union_le _ _
    _ ≤ (P.interedges A (W \ A)).card + (((A ∆ T) ×ˢ (Finset.univ : Finset V))).card :=
      Nat.add_le_add (Finset.card_image_le) Finset.card_image_le
    _ = _ := by simp [mul_comm]

lemma card_le_add_symmDiff {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (A T : Finset V) : A.card ≤ T.card + (A ∆ T).card := by
  have hs : A ⊆ T ∪ (A ∆ T) := by
    intro x hx
    by_cases hxT : x ∈ T
    · exact Finset.mem_union_left _ hxT
    · exact Finset.mem_union_right _ (Finset.mem_symmDiff.mpr (Or.inl ⟨hx,hxT⟩))
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

lemma sdiff_card_le_add_symmDiff {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (W A T : Finset V) :
    (W \ A).card ≤ (W \ T).card + (A ∆ T).card := by
  have hs : W \ A ⊆ (W \ T) ∪ (A ∆ T) := by
    intro x hx
    obtain ⟨hxW,hxA⟩ := Finset.mem_sdiff.mp hx
    by_cases hxT : x ∈ T
    · exact Finset.mem_union_right _ (Finset.mem_symmDiff.mpr (Or.inr ⟨hxT,hxA⟩))
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxW,hxT⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

lemma cut_card_lower_of_neighbors (P : SimpleGraph V) [DecidableRel P.Adj]
    (A B Q : Finset V) (hQA : Q ⊆ A) (c : ℝ)
    (hc : ∀ v ∈ Q, c ≤ (neighborsIn P v B).card) :
    c * Q.card ≤ ((P.interedges A B).card : ℝ) := by
  rw [card_interedges_eq_sum_neighborsIn, Nat.cast_sum]
  calc
    _ = ∑ v ∈ Q, c := by simp [mul_comm]
    _ ≤ ∑ v ∈ Q, ((neighborsIn P v B).card : ℝ) := Finset.sum_le_sum hc
    _ ≤ ∑ v ∈ A, ((neighborsIn P v B).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hQA (fun _ _ _ => Nat.cast_nonneg _)

lemma bad_sampled_cut_size_and_exceptional (P : SimpleGraph V) [DecidableRel P.Adj]
    (W A : Finset V) (hAW : A ⊆ W) (_ha : 0 < (A.card : ℝ))
    {p h τ : ℝ} (hp : 0 < p) (hh : 0 < h) (hτ : τ < p*h/4)
    (hdeg : ∀ v, p*h/2 ≤ ((neighborsIn P v W).card : ℝ))
    (hbad : ((P.interedges A (W \ A)).card : ℝ) < τ * A.card) :
    p*h/4 < (A.card : ℝ) ∧
      ((A \ A.filter (fun v => p*h/4 ≤ ((neighborsIn P v A).card : ℝ))).card : ℝ) ≤
        4*τ*A.card/(p*h) := by
  have hpart (v : V) : ((neighborsIn P v W).card : ℝ) =
      ((neighborsIn P v A).card : ℝ) + ((neighborsIn P v (W \ A)).card : ℝ) := by
    exact_mod_cast neighborsIn_partition_card P v A W hAW
  constructor
  · by_contra hn
    have ha' : (A.card : ℝ) ≤ p*h/4 := le_of_not_gt hn
    have hlo : p*h/4 * A.card ≤ ((P.interedges A (W \ A)).card : ℝ) := by
      apply cut_card_lower_of_neighbors P A (W \ A) A (Finset.Subset.refl _) (p*h/4)
      intro v _
      have hc : ((neighborsIn P v A).card : ℝ) ≤ A.card := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset (P.Adj v) A)
      have hd := hdeg v
      have he := hpart v
      linarith
    nlinarith
  · let Q := A \ A.filter (fun v => p*h/4 ≤ ((neighborsIn P v A).card : ℝ))
    have hl : p*h/4 * Q.card ≤ ((P.interedges A (W \ A)).card : ℝ) := by
      apply cut_card_lower_of_neighbors P A (W \ A) Q Finset.sdiff_subset (p*h/4)
      intro v hv
      obtain ⟨hvA,hvG⟩ := Finset.mem_sdiff.mp hv
      have hn : ((neighborsIn P v A).card : ℝ) < p*h/4 := by
        simpa only [Finset.mem_filter, hvA, true_and, not_le] using hvG
      have hd := hdeg v
      have he := hpart v
      linarith
    change (Q.card : ℝ) ≤ _
    apply (le_div_iff₀ (mul_pos hp hh)).mpr
    nlinarith

def neighborhoodUnion (P : SimpleGraph V) [DecidableRel P.Adj] (S : Finset V) : Finset V :=
  S.biUnion (fun v => neighborsIn P v Finset.univ)

lemma neighborhoodUnion_leakage (P : SimpleGraph V) [DecidableRel P.Adj]
    (S W A : Finset V) :
    (((neighborhoodUnion P S ∩ W) \ A).card : ℝ) ≤
      ∑ v ∈ S, ((neighborsIn P v (W \ A)).card : ℝ) := by
  have heq : (neighborhoodUnion P S ∩ W) \ A =
      S.biUnion (fun v => neighborsIn P v (W \ A)) := by
    ext x
    simp only [neighborhoodUnion, neighborsIn, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    aesop
  rw [heq]
  exact_mod_cast Finset.card_biUnion_le

lemma hitting_neighborhoodUnion (P : SimpleGraph V) [DecidableRel P.Adj]
    (good S A : Finset V) (hhit : ∀ v ∈ good, ¬Disjoint (neighborsIn P v A) S) :
    good ⊆ neighborhoodUnion P S := by
  intro v hv
  obtain ⟨x,hxK,hxS⟩ := Finset.not_disjoint_iff.mp (hhit v hv)
  apply Finset.mem_biUnion.mpr
  refine ⟨x,hxS,?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, P.adj_symm (Finset.mem_filter.mp hxK).2⟩

theorem exists_approximating_witness (P : SimpleGraph V) [DecidableRel P.Adj]
    (W A : Finset V) (hAW : A ⊆ W) (ha : 0 < (A.card : ℝ))
    {p h τ M : ℝ} (hp : 0 < p) (hh : 0 < h) (hτ0 : 0 < τ)
    (hτ : τ < p*h/4) (hM : 0 < M) (hMh : M ≤ h)
    (hmiss : (Fintype.card V : ℝ) * exp (-p*M/4) < 1/2)
    (hdeg : ∀ v, p*h/2 ≤ ((neighborsIn P v W).card : ℝ))
    (hbad : ((P.interedges A (W \ A)).card : ℝ) < τ * A.card) :
    p*h/4 < (A.card : ℝ) ∧ ∃ S : Finset V, S ⊆ A ∧
      (S.card : ℝ) ≤ 4 * A.card * M / h ∧
      ((A ∆ (neighborhoodUnion P S ∩ W)).card : ℝ) ≤
        (4*τ/(p*h) + 4*τ*M/h) * A.card := by
  classical
  obtain ⟨hlarge, hexc⟩ := bad_sampled_cut_size_and_exceptional P W A hAW ha hp hh hτ hdeg hbad
  refine ⟨hlarge, ?_⟩
  let good := A.filter (fun v => p*h/4 ≤ ((neighborsIn P v A).card : ℝ))
  let w : V → ℝ := fun v => ((neighborsIn P v (W \ A)).card : ℝ)
  let q : unitInterval := ⟨M/h, div_nonneg hM.le hh.le, (div_le_one hh).mpr hMh⟩
  have hq : 0 < (q : ℝ) := div_pos hM hh
  have hm : (good.card : ℝ) * exp (-(q : ℝ) * (p*h/4)) < 1/2 := by
    have heq : -(q : ℝ) * (p*h/4) = -p*M/4 := by
      dsimp [q]
      field_simp [hh.ne']
    rw [heq]
    have hg : (good.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ good
    exact (mul_le_mul_of_nonneg_right hg (exp_pos _).le).trans_lt hmiss
  have hsum : ∑ v ∈ A, w v ≤ τ * A.card := by
    dsimp [w]
    rw [← Nat.cast_sum, ← card_interedges_eq_sum_neighborsIn]
    exact hbad.le
  obtain ⟨S,hSA,hSc,hSw,hSh⟩ := exists_small_weighted_hitting_set A
    (Finset.card_pos.mp (by exact_mod_cast ha)) good (fun v => neighborsIn P v A)
    (fun v _ => Finset.filter_subset _ _) w (fun _ _ => Nat.cast_nonneg _)
    (mul_pos hτ0 ha) hsum
    (fun v hv => (Finset.mem_filter.mp hv).2) q hq hm
  refine ⟨S,hSA,?_,?_⟩
  · convert hSc using 1 ; dsimp [q] ; ring
  · let T := neighborhoodUnion P S ∩ W
    have hgood : good ⊆ neighborhoodUnion P S := hitting_neighborhoodUnion P good S A hSh
    have hsub : A ∆ T ⊆ (A \ good) ∪ (T \ A) := by
      intro v hv
      rcases Finset.mem_symmDiff.mp hv with ⟨hvA,hvT⟩ | ⟨hvT,hvA⟩
      · apply Finset.mem_union_left
        apply Finset.mem_sdiff.mpr
        refine ⟨hvA,?_⟩
        intro hvG
        exact hvT (Finset.mem_inter.mpr ⟨hgood hvG, hAW hvA⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvT,hvA⟩)
    have hδ : ((A ∆ T).card : ℝ) ≤ ((A \ good).card : ℝ) + ((T \ A).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hleak : ((T \ A).card : ℝ) ≤ 4*(q : ℝ)*(τ*A.card) :=
      (neighborhoodUnion_leakage P S W A).trans hSw
    change ((A ∆ T).card : ℝ) ≤ _
    change ((A \ good).card : ℝ) ≤ _ at hexc
    calc
      _ ≤ 4*τ*A.card/(p*h) + 4*(q : ℝ)*(τ*A.card) := add_le_add hexc hleak |>.trans' hδ
      _ = _ := by dsimp [q]; ring

def CutExpansion (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ) : Prop :=
  ∀ U : Finset V, h * min (U.card : ℝ) (Uᶜ.card : ℝ) ≤
    ((P.interedges U Uᶜ).card : ℝ)

def CutExpansionOn (P : SimpleGraph V) [DecidableRel P.Adj] (W : Finset V) (h : ℝ) : Prop :=
  ∀ A : Finset V, A ⊆ W → h * min (A.card : ℝ) ((W \ A).card : ℝ) ≤
    ((P.interedges A (W \ A)).card : ℝ)

theorem cutExpansionOn_of_witnesses (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) {p h τ M : ℝ} (hp : 0 < p) (hh : 0 < h) (hτ0 : 0 < τ)
    (hτ : τ < p*h/4) (hM : 0 < M) (hMh : M ≤ h)
    (hmiss : (Fintype.card V : ℝ) * exp (-p*M/4) < 1/2)
    (hε : 4*τ/(p*h) + 4*τ*M/h ≤ 1/2)
    (hperturb : τ + Fintype.card V * (4*τ/(p*h) + 4*τ*M/h) ≤ p^2*h/8)
    (hexp : CutExpansion P h)
    (hdeg : ∀ v, p*h/2 ≤ ((neighborsIn P v W).card : ℝ))
    (hwitness : ∀ S : Finset V, (S.card : ℝ) ≤ 4*Fintype.card V*M/h →
      let U := neighborhoodUnion P S
      p*h/8 ≤ min (U.card : ℝ) (Uᶜ.card : ℝ) →
      (p^2/4) * ((P.interedges U Uᶜ).card : ℝ) ≤
        ((P.interedges (U ∩ W) (W \ (U ∩ W))).card : ℝ)) :
    CutExpansionOn P W τ := by
  classical
  have hsmall (A : Finset V) (hAW : A ⊆ W)
      (hsize : (A.card : ℝ) ≤ (W \ A).card) :
      τ * A.card ≤ ((P.interedges A (W \ A)).card : ℝ) := by
    by_contra hn
    have hbad := lt_of_not_ge hn
    have ha : 0 < (A.card : ℝ) := by
      by_contra hn
      have hz : (A.card : ℝ) = 0 := (le_of_not_gt hn).antisymm (Nat.cast_nonneg _)
      rw [hz, mul_zero] at hbad
      exact (Nat.cast_nonneg _).not_gt hbad
    obtain ⟨hlarge,S,hSA,hSc,hδ⟩ := exists_approximating_witness P W A hAW ha
      hp hh hτ0 hτ hM hMh hmiss hdeg hbad
    let U := neighborhoodUnion P S
    let T := U ∩ W
    let δ : ℝ := (A ∆ T).card
    have hδ' : δ ≤ (A.card : ℝ)/2 := by
      have ht := mul_le_mul_of_nonneg_right hε ha.le
      dsimp [δ,T,U]
      linarith
    have hmin : (A.card : ℝ)/2 ≤ min (U.card : ℝ) (Uᶜ.card : ℝ) := by
      apply le_min
      · have ht : (A.card : ℝ) ≤ (T.card : ℝ) + δ := by
          dsimp [δ]
          exact_mod_cast card_le_add_symmDiff A T
        have hTU : (T.card : ℝ) ≤ U.card := by
          exact_mod_cast Finset.card_le_card (Finset.inter_subset_left : T ⊆ U)
        linarith
      · have ht : ((W \ A).card : ℝ) ≤ ((W \ T).card : ℝ) + δ := by
          dsimp [δ]
          exact_mod_cast sdiff_card_le_add_symmDiff W A T
        have hs : W \ T ⊆ Uᶜ := by
          intro v hv
          obtain ⟨hvW,hvT⟩ := Finset.mem_sdiff.mp hv
          apply Finset.mem_compl.mpr
          intro hvU
          exact hvT (Finset.mem_inter.mpr ⟨hvU,hvW⟩)
        have hh' : ((W \ T).card : ℝ) ≤ Uᶜ.card := by exact_mod_cast Finset.card_le_card hs
        linarith
    have hsbound : (S.card : ℝ) ≤ 4*Fintype.card V*M/h := by
      apply hSc.trans
      have hac : (A.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ A
      gcongr
    have hw := hwitness S hsbound (by dsimp [U] at hmin; linarith)
    have he := hexp U
    have hlo : p^2*h*A.card/8 ≤ ((P.interedges T (W \ T)).card : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hmin hh.le
      have ht := mul_le_mul_of_nonneg_left (hm.trans he) (by positivity : 0 ≤ p^2/4)
      change p^2/4 * ((P.interedges U Uᶜ).card : ℝ) ≤ _ at hw
      nlinarith
    have hupper : ((P.interedges T (W \ T)).card : ℝ) ≤
        ((P.interedges A (W \ A)).card : ℝ) + Fintype.card V * δ := by
      dsimp [δ]
      exact_mod_cast cut_perturbation_card P W A T hAW Finset.inter_subset_right
    have hd := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ (Fintype.card V : ℝ))
    have hp' := mul_le_mul_of_nonneg_right hperturb ha.le
    change (Fintype.card V : ℝ) * δ ≤ _ at hd
    nlinarith
  intro A hAW
  by_cases hs : (A.card : ℝ) ≤ (W \ A).card
  · rw [min_eq_left hs]
    exact hsmall A hAW hs
  · have hs' : ((W \ A).card : ℝ) ≤ A.card := (lt_of_not_ge hs).le
    rw [min_eq_right hs']
    have heq : W \ (W \ A) = A := Finset.sdiff_sdiff_eq_self hAW
    have ht := hsmall (W \ A) Finset.sdiff_subset (by simpa only [heq] using hs')
    rw [heq] at ht
    let : Std.Symm P.Adj := P.symm
    have hcomm : (P.interedges (W \ A) A).card = (P.interedges A (W \ A)).card :=
      Rel.card_interedges_comm (W \ A) A
    rwa [hcomm] at ht

lemma cutExpansion_minDegree (P : SimpleGraph V) [DecidableRel P.Adj]
    {h : ℝ} (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V) (v : V) :
    h ≤ ((neighborsIn P v Finset.univ).card : ℝ) := by
  have ht := hexp {v}
  have hc : (1 : ℝ) ≤ ((({v} : Finset V)ᶜ).card : ℝ) := by
    have : 1 ≤ (({v} : Finset V)ᶜ).card := by
      rw [Finset.card_compl, Finset.card_singleton]
      omega
    exact_mod_cast this
  simp only [Finset.card_singleton, Nat.cast_one, min_eq_left hc, mul_one] at ht
  rw [card_interedges_eq_sum_neighborsIn, Finset.sum_singleton] at ht
  have heq : neighborsIn P v ({v} : Finset V)ᶜ = neighborsIn P v Finset.univ := by
    ext x
    simp only [neighborsIn, Finset.mem_filter, Finset.mem_compl, Finset.mem_singleton,
      Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨fun he => P.irrefl (he ▸ h), h⟩⟩
  rwa [heq] at ht

lemma sample_neighbors_lower_tail (P : SimpleGraph V) [DecidableRel P.Adj]
    (p : unitInterval) {h : ℝ} (hdeg : ∀ v, h ≤ ((neighborsIn P v Finset.univ).card : ℝ))
    (v : V) :
    (sampleMeasure V p).real {ω | ((neighborsIn P v (sampleVertices ω)).card : ℝ) < (p : ℝ)*h/2} ≤
      exp (-(p : ℝ)*h/8) := by
  have heq (ω : V → Bool) : neighborsIn P v (sampleVertices ω) =
      neighborsIn P v Finset.univ ∩ sampleVertices ω := by
    ext x; simp [neighborsIn, and_comm]
  simp_rw [heq]
  have hs : {ω | (((neighborsIn P v Finset.univ) ∩ sampleVertices ω).card : ℝ) < (p : ℝ)*h/2} ⊆
      {ω | (((neighborsIn P v Finset.univ) ∩ sampleVertices ω).card : ℝ) ≤
        (p : ℝ)*(neighborsIn P v Finset.univ).card/2} := by
    intro ω hω
    change (((neighborsIn P v Finset.univ) ∩ sampleVertices ω).card : ℝ) < (p : ℝ)*h/2 at hω
    exact hω.le.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hdeg v) p.property.1) (by norm_num))
  have he : -(p : ℝ)*(neighborsIn P v Finset.univ).card/8 ≤ -(p : ℝ)*h/8 := by
    have ht := mul_le_mul_of_nonneg_left (hdeg v) p.property.1
    linarith
  exact (measureReal_mono hs (measure_ne_top _ _)).trans
    ((sample_card_lower_tail p _).trans (exp_le_exp.mpr he))

lemma card_small_subsets_le (s : ℕ) (hr : 0 < Fintype.card V) :
    (((Finset.univ : Finset V).powerset).filter (fun S => S.card ≤ s)).card ≤
      (s+1) * Fintype.card V ^ s := by
  classical
  have heq : (((Finset.univ : Finset V).powerset).filter (fun S => S.card ≤ s)) =
      (Finset.range (s+1)).biUnion (fun t => (Finset.univ : Finset V).powersetCard t) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
      Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
    exact ⟨fun h => ⟨S.card, by omega, rfl⟩,
      fun ⟨t,ht,he⟩ => by omega⟩
  rw [heq]
  calc
    _ ≤ ∑ t ∈ Finset.range (s+1), ((Finset.univ : Finset V).powersetCard t).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ t ∈ Finset.range (s+1), Fintype.card V ^ s := by
      apply Finset.sum_le_sum
      intro t ht
      rw [Finset.card_powersetCard, Finset.card_univ]
      exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right hr (by simpa using ht))
    _ = _ := by simp [mul_comm]

def witnessFamily (P : SimpleGraph V) [DecidableRel P.Adj] (s : ℕ) : Finset (Finset V) :=
  ((((Finset.univ : Finset V).powerset).filter (fun S => S.card ≤ s))).image (neighborhoodUnion P)

lemma card_witnessFamily_le (P : SimpleGraph V) [DecidableRel P.Adj]
    (s : ℕ) (hr : 0 < Fintype.card V) :
    (witnessFamily P s).card ≤ (s+1) * Fintype.card V ^ s :=
  Finset.card_image_le.trans (card_small_subsets_le s hr)

lemma sampled_witness_cut_lower_tail (P : SimpleGraph V) [DecidableRel P.Adj]
    (p : unitInterval) {h : ℝ} (hh : 0 ≤ h) (hexp : CutExpansion P h)
    (hr : 0 < Fintype.card V) (U : Finset V)
    (hU : (p : ℝ)*h/8 ≤ min (U.card : ℝ) (Uᶜ.card : ℝ)) :
    (sampleMeasure V p).real {ω |
      ((P.interedges (U ∩ sampleVertices ω) (sampleVertices ω \ (U ∩ sampleVertices ω))).card : ℝ) <
        (p : ℝ)^2/4 * (P.interedges U Uᶜ).card} ≤
      2 * (Fintype.card V : ℝ) * exp (-(p : ℝ)^3*h^2/(256*Fintype.card V)) := by
  have hAB : Disjoint U Uᶜ := Finset.disjoint_left.mpr (fun _ hx hy => (Finset.mem_compl.mp hy) hx)
  have heq (ω : V → Bool) :
      P.interedges (U ∩ sampleVertices ω) (sampleVertices ω \ (U ∩ sampleVertices ω)) =
        (P.interedges U Uᶜ).filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω) := by
    ext ⟨x,y⟩
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_compl]
    aesop
  have ht := sampled_bipartite_cut_lower_tail p hr U Uᶜ hAB (P.interedges U Uᶜ)
    (fun e he => ⟨(P.mem_interedges_iff.mp he).1, (P.mem_interedges_iff.mp he).2.1⟩)
  have hl : (p : ℝ)*h^2/8 ≤ ((P.interedges U Uᶜ).card : ℝ) := by
    have ht := mul_le_mul_of_nonneg_left hU hh
    have hu := hexp U
    nlinarith
  have he : -(p : ℝ)^2 * (P.interedges U Uᶜ).card/(32*Fintype.card V) ≤
      -(p : ℝ)^3*h^2/(256*Fintype.card V) := by
    have hrR : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hr
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hs := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (p : ℝ)^2)
    nlinarith
  simp_rw [heq]
  have hc : (p : ℝ)^2/4 * (P.interedges U Uᶜ).card = (p : ℝ)^2 * (P.interedges U Uᶜ).card/4 := by ring
  rw [hc]
  exact ht.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) (by positivity))

def SampleGood (P : SimpleGraph V) [DecidableRel P.Adj] (p h τ : ℝ) (ω : V → Bool) : Prop :=
  ((sampleVertices ω).card : ℝ) ≤ 2*p*Fintype.card V ∧
    (∀ v, p*h/2 ≤ ((neighborsIn P v (sampleVertices ω)).card : ℝ)) ∧
    CutExpansionOn P (sampleVertices ω) τ

theorem vertex_sampling_failure_bound (P : SimpleGraph V) [DecidableRel P.Adj]
    (p : unitInterval) {h τ M : ℝ} (hp : 0 < (p : ℝ)) (hh : 0 < h) (hτ0 : 0 < τ)
    (hτ : τ < (p : ℝ)*h/4) (hM : 0 < M) (hMh : M ≤ h)
    (hr : 2 ≤ Fintype.card V)
    (hmiss : (Fintype.card V : ℝ) * exp (-(p : ℝ)*M/4) < 1/2)
    (hε : 4*τ/((p : ℝ)*h) + 4*τ*M/h ≤ 1/2)
    (hperturb : τ + Fintype.card V * (4*τ/((p : ℝ)*h) + 4*τ*M/h) ≤ (p : ℝ)^2*h/8)
    (hexp : CutExpansion P h) :
    (sampleMeasure V p).real {ω | ¬SampleGood P (p : ℝ) h τ ω} ≤
      exp (-(p : ℝ)*Fintype.card V/3) +
      Fintype.card V * exp (-(p : ℝ)*h/8) +
      2*Fintype.card V * ((⌈4*Fintype.card V*M/h⌉₊+1 : ℕ) : ℝ) *
        (Fintype.card V : ℝ)^⌈4*Fintype.card V*M/h⌉₊ *
        exp (-(p : ℝ)^3*h^2/(256*Fintype.card V)) := by
  classical
  let μ := sampleMeasure V p
  let s := ⌈4*(Fintype.card V : ℝ)*M/h⌉₊
  let large := (witnessFamily P s).filter
    (fun U => (p : ℝ)*h/8 ≤ min (U.card : ℝ) (Uᶜ.card : ℝ))
  let B₀ : Set (V → Bool) := {ω | 2*(p : ℝ)*Fintype.card V < ((sampleVertices ω).card : ℝ)}
  let B₁ (v : V) : Set (V → Bool) :=
    {ω | ((neighborsIn P v (sampleVertices ω)).card : ℝ) < (p : ℝ)*h/2}
  let B₂ (U : Finset V) : Set (V → Bool) := {ω |
    ((P.interedges (U ∩ sampleVertices ω) (sampleVertices ω \ (U ∩ sampleVertices ω))).card : ℝ) <
      (p : ℝ)^2/4 * (P.interedges U Uᶜ).card}
  have h₀ : μ.real B₀ ≤ exp (-(p : ℝ)*Fintype.card V/3) := by
    have hs : B₀ ⊆ {ω | 2*(p : ℝ)*Fintype.card V ≤ ((sampleVertices ω).card : ℝ)} := by
      intro ω hω
      change 2*(p : ℝ)*Fintype.card V < ((sampleVertices ω).card : ℝ) at hω
      exact hω.le
    have ht := sample_card_upper_tail p (Finset.univ : Finset V)
    simp only [Finset.card_univ, Finset.univ_inter] at ht
    exact (measureReal_mono hs (measure_ne_top _ _)).trans ht
  have h₁ : μ.real (⋃ v ∈ (Finset.univ : Finset V), B₁ v) ≤
      Fintype.card V * exp (-(p : ℝ)*h/8) := by
    calc
      _ ≤ ∑ v : V, μ.real (B₁ v) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _v : V, exp (-(p : ℝ)*h/8) := Finset.sum_le_sum (fun v _ =>
        sample_neighbors_lower_tail P p (cutExpansion_minDegree P hexp hr) v)
      _ = _ := by simp
  have h₂ : μ.real (⋃ U ∈ large, B₂ U) ≤
      2*Fintype.card V * ((s+1 : ℕ) : ℝ) * (Fintype.card V : ℝ)^s *
        exp (-(p : ℝ)^3*h^2/(256*Fintype.card V)) := by
    calc
      _ ≤ ∑ U ∈ large, μ.real (B₂ U) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _U ∈ large, 2*(Fintype.card V : ℝ)*exp (-(p : ℝ)^3*h^2/(256*Fintype.card V)) := by
        apply Finset.sum_le_sum
        intro U hU
        exact sampled_witness_cut_lower_tail P p hh.le hexp (by omega) U (Finset.mem_filter.mp hU).2
      _ = (large.card : ℝ) * (2*Fintype.card V * exp (-(p : ℝ)^3*h^2/(256*Fintype.card V))) := by simp
      _ ≤ (((s+1 : ℕ) : ℝ) * (Fintype.card V : ℝ)^s) *
          (2*Fintype.card V * exp (-(p : ℝ)^3*h^2/(256*Fintype.card V))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have ht : large.card ≤ (s+1)*Fintype.card V^s :=
          (Finset.card_le_card (Finset.filter_subset _ _)).trans
            (card_witnessFamily_le P s (by omega))
        exact_mod_cast ht
      _ = _ := by ring
  have hcover : {ω | ¬SampleGood P (p : ℝ) h τ ω} ⊆
      (B₀ ∪ (⋃ v ∈ (Finset.univ : Finset V), B₁ v)) ∪ (⋃ U ∈ large, B₂ U) := by
    intro ω hω
    by_contra hn
    have hn₀ : ω ∉ B₀ := fun h => hn (Or.inl (Or.inl h))
    have hn₁ (v : V) : ω ∉ B₁ v := fun h => hn (Or.inl (Or.inr
      (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, h⟩⟩)))
    have hn₂ (U : Finset V) (hU : U ∈ large) : ω ∉ B₂ U := fun h => hn (Or.inr
      (Set.mem_iUnion.mpr ⟨U, Set.mem_iUnion.mpr ⟨hU,h⟩⟩))
    apply hω
    have hd (v : V) : (p : ℝ)*h/2 ≤ ((neighborsIn P v (sampleVertices ω)).card : ℝ) :=
      le_of_not_gt (hn₁ v)
    refine ⟨le_of_not_gt hn₀, hd, ?_⟩
    apply cutExpansionOn_of_witnesses P (sampleVertices ω) hp hh hτ0 hτ hM hMh
      hmiss hε hperturb hexp hd
    intro S hS
    dsimp only
    intro hU
    let U := neighborhoodUnion P S
    have hSc : S.card ≤ s := by
      have ht := hS.trans (Nat.le_ceil (4*(Fintype.card V : ℝ)*M/h))
      dsimp [s]
      exact_mod_cast ht
    have hmem : U ∈ large := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, hU⟩
      apply Finset.mem_image.mpr
      exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hSc⟩, rfl⟩
    exact le_of_not_gt (hn₂ U hmem)
  calc
    _ ≤ μ.real ((B₀ ∪ (⋃ v ∈ (Finset.univ : Finset V), B₁ v)) ∪ (⋃ U ∈ large, B₂ U)) :=
      measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ μ.real (B₀ ∪ (⋃ v ∈ (Finset.univ : Finset V), B₁ v)) + μ.real (⋃ U ∈ large, B₂ U) :=
      measureReal_union_le _ _
    _ ≤ μ.real B₀ + μ.real (⋃ v ∈ (Finset.univ : Finset V), B₁ v) + μ.real (⋃ U ∈ large, B₂ U) :=
      add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add h₀ h₁) h₂

end ErdosGallai.Sampling

/-! ### Upstream module `Combinatorics/CycleDecomposition/ReservoirSampling.lean` -/

section
open _root_.Filter _root_.Asymptotics _root_.Real
open scoped _root_.Topology
noncomputable section
namespace ErdosGallai.Sampling

lemma eventually_monomial_lt (K c a b : ℝ) (hc : 0 < c) (hab : a < b) :
    ∀ᶠ D : ℝ in atTop, K * D^a < c * D^b := by
  have ht : Tendsto (fun D : ℝ => K * D^(a-b)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).const_mul K
    simpa only [neg_sub, mul_zero] using hh
  filter_upwards [eventually_gt_atTop (0 : ℝ), ht.eventually_lt_const hc] with D hD htD
  have hb : 0 < D^b := Real.rpow_pos_of_pos hD b
  have heq : D^a = D^(a-b) * D^b := by rw [← Real.rpow_add hD]; congr 1; ring
  rw [heq, ← mul_assoc]
  exact mul_lt_mul_of_pos_right htD hb

lemma tendsto_monomial_exp_neg_power (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun D : ℝ => D^a * exp (-c * D^b)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a/b) c hc).comp
    (tendsto_rpow_atTop hb)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul hD.le, mul_div_cancel₀ _ hb.ne']

lemma eventually_log_le_small_power : ∀ᶠ D : ℝ in atTop, log D ≤ D^(1/10 : ℝ) := by
  filter_upwards [(isLittleO_log_rpow_atTop (show (0 : ℝ) < 1/10 by norm_num)).eventuallyLE,
    eventually_ge_atTop (1 : ℝ)] with D hD h1
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg h1),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] using hD

def samplingScaleError (c p D : ℝ) : ℝ :=
  exp (-p/3 * D^(9/10 : ℝ)) +
    D^(51/50 : ℝ) * exp (-(p*c/8) * D^(9/10 : ℝ)) +
    (2*(4/c+2)) * (D^(23/20 : ℝ) * exp (-(p^3*c^2/512) * D^(39/50 : ℝ)))

lemma samplingScaleError_tendsto (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    Tendsto (samplingScaleError c p) atTop (𝓝 0) := by
  have h0 := tendsto_monomial_exp_neg_power 0 (9/10) (p/3) (by norm_num) (by positivity)
  have h1 := tendsto_monomial_exp_neg_power (51/50) (9/10) (p*c/8) (by norm_num) (by positivity)
  have h2 := (tendsto_monomial_exp_neg_power (23/20) (39/50) (p^3*c^2/512)
    (by norm_num) (by positivity)).const_mul (2*(4/c+2))
  unfold samplingScaleError
  simpa [neg_div, Real.rpow_zero] using (h0.add h1).add h2

def SamplingScaleReady (c p D : ℝ) (r : ℕ) : Prop :=
  let h := c*D^(9/10 : ℝ)
  let τ := D^(37/50 : ℝ)
  let M := D^(1/100 : ℝ)
  2 ≤ r ∧ τ < p*h/4 ∧ M ≤ h ∧ (r : ℝ)*exp (-p*M/4) < 1/2 ∧
    4*τ/(p*h)+4*τ*M/h ≤ 1/2 ∧
    τ+r*(4*τ/(p*h)+4*τ*M/h) ≤ p^2*h/8 ∧
    exp (-p*r/3) + r*exp (-p*h/8) +
      2*r*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ) * (r : ℝ)^⌈4*r*M/h⌉₊ *
        exp (-p^3*h^2/(256*r)) ≤ samplingScaleError c p D

lemma sampling_witness_error_le (c p D : ℝ) (r : ℕ) (hc : 0 < c) (hp : 0 < p)
    (hD : 1 ≤ D) (hrpos : 0 < (r : ℝ)) (hrhi : (r : ℝ) ≤ D^(51/50 : ℝ))
    (hlog : log D ≤ D^(1/10 : ℝ))
    (hcost : ((51/50)*(4/c+2))*D^(23/100 : ℝ) ≤
      (p^3*c^2/512)*D^(39/50 : ℝ)) :
    let h := c*D^(9/10 : ℝ)
    let M := D^(1/100 : ℝ)
    2*r*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ)*(r : ℝ)^⌈4*r*M/h⌉₊*
        exp (-p^3*h^2/(256*r)) ≤
      (2*(4/c+2))*(D^(23/20 : ℝ)*exp (-(p^3*c^2/512)*D^(39/50 : ℝ))) := by
  let h := c*D^(9/10 : ℝ)
  let M := D^(1/100 : ℝ)
  let K := 4/c+2
  have hK : 0 < K := by dsimp [K]; positivity
  have hDpos : 0 < D := by linarith
  have hh : 0 < h := by dsimp [h]; positivity
  have hMpos : 0 < M := Real.rpow_pos_of_pos hDpos _
  have hrNat : 0 < r := by exact_mod_cast hrpos
  have hs : ((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ) ≤ K*D^(13/100 : ℝ) := by
    have hnorm : 4*D^(51/50 : ℝ)*M/h = (4/c)*D^(13/100 : ℝ) := by
      dsimp [M,h]
      rw [show (13/100 : ℝ) = (51/50+1/100)-9/10 by norm_num,
        Real.rpow_sub hDpos, Real.rpow_add hDpos]
      field_simp
    calc
      _ ≤ 4*r*M/h+2 := by
        have hs := (Nat.ceil_lt_add_one (show 0 ≤ 4*(r : ℝ)*M/h by positivity)).le
        push_cast
        linarith
      _ ≤ 4*D^(51/50 : ℝ)*M/h+2 := by gcongr
      _ = (4/c)*D^(13/100 : ℝ)+2 := by rw [hnorm]
      _ ≤ K*D^(13/100 : ℝ) := by
        have hd := Real.one_le_rpow hD (show (0 : ℝ) ≤ 13/100 by norm_num)
        dsimp [K]
        nlinarith
  have hln : log (r : ℝ) ≤ (51/50)*log D := by
    simpa only [Real.log_rpow hDpos] using Real.log_le_log hrpos hrhi
  have hecost : (⌈4*r*M/h⌉₊ : ℝ)*log (r : ℝ) ≤
      (p^3*c^2/512)*D^(39/50 : ℝ) := by
    have hs' : (⌈4*r*M/h⌉₊ : ℝ) ≤ K*D^(13/100 : ℝ) := by push_cast at hs; linarith
    calc
      _ ≤ K*D^(13/100 : ℝ)*((51/50)*log D) := by
        apply mul_le_mul hs' hln
        · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega))
        · positivity
      _ ≤ K*D^(13/100 : ℝ)*((51/50)*D^(1/10 : ℝ)) := by gcongr
      _ = ((51/50)*K)*D^(23/100 : ℝ) := by
        have he := Real.rpow_add hDpos (13/100 : ℝ) (1/10)
        norm_num at he
        rw [he]
        ring
      _ ≤ _ := hcost
  have hratio : c^2*D^(39/50 : ℝ) ≤ h^2/(r : ℝ) := by
    have he : c^2*D^(39/50 : ℝ) = h^2/D^(51/50 : ℝ) := by
      dsimp [h]
      rw [show (39/50 : ℝ) = (9/10)*2-51/50 by norm_num,
        Real.rpow_sub hDpos]
      have he2 := Real.rpow_mul_natCast hDpos.le (9/10 : ℝ) 2
      norm_num only [Nat.cast_ofNat] at he2
      rw [show (9/10 : ℝ)*2=9/5 by norm_num, he2]
      ring
    rw [he]
    exact div_le_div_of_nonneg_left (sq_nonneg h) hrpos hrhi
  have hexpcost : exp ((⌈4*r*M/h⌉₊ : ℝ)*log (r : ℝ) - p^3*h^2/(256*r)) ≤
      exp (-(p^3*c^2/512)*D^(39/50 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hn := mul_le_mul_of_nonneg_left hratio (show 0 ≤ p^3/256 by positivity)
    have hid : (p^3/256)*(h^2/(r : ℝ)) =p^3*h^2/(256*r) := by ring
    rw [hid] at hn
    nlinarith
  have hpoly : 2*(r : ℝ)*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ) ≤
      2*K*D^(23/20 : ℝ) := by
    calc
      _ ≤ 2*D^(51/50 : ℝ)*(K*D^(13/100 : ℝ)) := by gcongr
      _ = _ := by
        have he := Real.rpow_add hDpos (51/50 : ℝ) (13/100)
        norm_num at he
        rw [he]
        ring
  have hwitness : 2*r*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ)*(r : ℝ)^⌈4*r*M/h⌉₊*
      exp (-p^3*h^2/(256*r)) ≤
      (2*K)*(D^(23/20 : ℝ)*exp (-(p^3*c^2/512)*D^(39/50 : ℝ))) := by
    have heq : (r : ℝ)^⌈4*r*M/h⌉₊*exp (-p^3*h^2/(256*r)) =
        exp ((⌈4*r*M/h⌉₊ : ℝ)*log (r : ℝ)-p^3*h^2/(256*r)) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hrpos]
      simp only [neg_mul,  Real.exp_neg, div_eq_mul_inv]
    rw [mul_assoc (2*(r : ℝ)*_) _ _, heq]
    exact (mul_le_mul hpoly hexpcost (exp_pos _).le (by positivity)).trans_eq (by ring)
  exact hwitness

lemma eventually_samplingScaleReady (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∀ᶠ D : ℝ in atTop, ∀ r : ℕ,
      D^(9/10 : ℝ) ≤ r → (r : ℝ) ≤ D^(51/50 : ℝ) → SamplingScaleReady c p D r := by
  let K := 4/c+2
  have hK : 0 < K := by dsimp [K]; positivity
  have hmiss : Tendsto (fun D : ℝ => D^(51/50 : ℝ) * exp (-p/4*D^(1/100 : ℝ)))
      atTop (𝓝 0) := by
    convert tendsto_monomial_exp_neg_power (51/50) (1/100) (p/4)
      (by norm_num) (by positivity) using 1 ; simp [neg_div]
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show (0 : ℝ) < 9/10 by norm_num)).eventually_ge_atTop 2,
    eventually_monomial_lt 1 (p*c/4) (37/50) (9/10) (by positivity) (by norm_num),
    eventually_monomial_lt 1 c (1/100) (9/10) hc (by norm_num),
    hmiss.eventually_lt_const (show (0 : ℝ) < 1/2 by norm_num),
    eventually_monomial_lt (4/(p*c)) (1/4) (-4/25) 0 (by norm_num) (by norm_num),
    eventually_monomial_lt (4/c) (1/4) (-3/20) 0 (by norm_num) (by norm_num),
    eventually_monomial_lt 1 (p^2*c/24) (37/50) (9/10) (by positivity) (by norm_num),
    eventually_monomial_lt (4/(p*c)) (p^2*c/24) (43/50) (9/10) (by positivity) (by norm_num),
    eventually_monomial_lt (4/c) (p^2*c/24) (87/100) (9/10) (by positivity) (by norm_num),
    eventually_log_le_small_power,
    eventually_monomial_lt ((51/50)*K) (p^3*c^2/512) (23/100) (39/50)
      (by positivity) (by norm_num)] with D hD h2 hτ hM hm hε₁ hε₂ ht₀ ht₁ ht₂ hlog hcost
  intro r hrlo hrhi
  have hDpos : 0 < D := by linarith
  have hr2 : 2 ≤ r := by exact_mod_cast h2.trans hrlo
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  let h := c*D^(9/10 : ℝ)
  let τ := D^(37/50 : ℝ)
  let M := D^(1/100 : ℝ)
  have hh : 0 < h := by dsimp [h]; positivity
  have hτpos : 0 < τ := Real.rpow_pos_of_pos hDpos _
  have hMpos : 0 < M := Real.rpow_pos_of_pos hDpos _
  have he₁ : 4*τ/(p*h) = (4/(p*c))*D^(-4/25 : ℝ) := by
    dsimp [τ,h]
    rw [show (-4/25 : ℝ) =37/50-9/10 by norm_num, Real.rpow_sub hDpos]
    field_simp
  have he₂ : 4*τ*M/h = (4/c)*D^(-3/20 : ℝ) := by
    dsimp [τ,M,h]
    rw [show (-3/20 : ℝ) =(37/50+1/100)-9/10 by norm_num,
      Real.rpow_sub hDpos, Real.rpow_add hDpos]
    field_simp
  have hm₁ : D^(51/50 : ℝ)*((4/(p*c))*D^(-4/25 : ℝ)) =
      (4/(p*c))*D^(43/50 : ℝ) := by
    rw [mul_left_comm, ← Real.rpow_add hDpos]
    norm_num
  have hm₂ : D^(51/50 : ℝ)*((4/c)*D^(-3/20 : ℝ)) =
      (4/c)*D^(87/100 : ℝ) := by
    rw [mul_left_comm, ← Real.rpow_add hDpos]
    norm_num
  refine ⟨hr2, ?_, (by simpa only [one_mul] using hM.le), ?_, ?_, ?_, ?_⟩
  · change τ < p*h/4
    dsimp [τ,h]
    simpa only [one_mul, div_mul_eq_mul_div, mul_assoc] using hτ
  · change (r : ℝ)*exp (-p*M/4) < 1/2
    calc
      _ ≤ D^(51/50 : ℝ)*exp (-p*M/4) := mul_le_mul_of_nonneg_right hrhi (exp_pos _).le
      _ < _ := by simpa [M, div_mul_eq_mul_div] using hm
  · change 4*τ/(p*h)+4*τ*M/h ≤ 1/2
    rw [he₁, he₂]
    simp only [Real.rpow_zero, mul_one] at hε₁ hε₂
    linarith
  · change τ+(r : ℝ)*(4*τ/(p*h)+4*τ*M/h) ≤ p^2*h/8
    rw [he₁,he₂]
    have ht : (r : ℝ)*((4/(p*c))*D^(-4/25 : ℝ)+(4/c)*D^(-3/20 : ℝ)) ≤
        (4/(p*c))*D^(43/50 : ℝ)+(4/c)*D^(87/100 : ℝ) := by
      calc
        _ ≤ D^(51/50 : ℝ)*((4/(p*c))*D^(-4/25 : ℝ)+(4/c)*D^(-3/20 : ℝ)) := by
          apply mul_le_mul_of_nonneg_right hrhi; positivity
        _ = _ := by rw [mul_add, hm₁, hm₂]
    dsimp [τ,h]
    nlinarith
  · change exp (-p*r/3)+r*exp (-p*h/8)+
      2*r*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ)*(r : ℝ)^⌈4*r*M/h⌉₊*
        exp (-p^3*h^2/(256*r)) ≤ samplingScaleError c p D
    have hwitness := sampling_witness_error_le c p D r hc hp hD hrpos hrhi hlog hcost.le
    have hsize : exp (-p*r/3) ≤ exp (-p/3*D^(9/10 : ℝ)) := by
      apply exp_le_exp.mpr
      have ht := mul_le_mul_of_nonneg_left hrlo hp.le
      nlinarith
    have hdegree : (r : ℝ)*exp (-p*h/8) ≤
        D^(51/50 : ℝ)*exp (-(p*c/8)*D^(9/10 : ℝ)) := by
      have heq : -p*h/8=-(p*c/8)*D^(9/10 : ℝ) := by dsimp [h]; ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hrhi (exp_pos _).le
    exact add_le_add (add_le_add hsize hdegree) hwitness

end ErdosGallai.Sampling

namespace ErdosGallai.Sampling
open _root_.Filter _root_.MeasureTheory _root_.Real

theorem vertex_sampling_uniform (c : ℝ) (hc : 0 < c) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (_hp1 : (p : ℝ) < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (P : SimpleGraph V) [DecidableRel P.Adj],
      D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) →
      CutExpansion P (c*D^(9/10 : ℝ)) →
      (sampleMeasure V p).real {ω | ¬SampleGood P (p : ℝ) (c*D^(9/10 : ℝ))
        (D^(37/50 : ℝ)) ω} ≤ ε := by
  have hevent : ∀ᶠ D : ℝ in atTop,
      1 ≤ D ∧
      (∀ r : ℕ, D^(9/10 : ℝ) ≤ r → (r : ℝ) ≤ D^(51/50 : ℝ) →
        SamplingScaleReady c (p : ℝ) D r) ∧
      samplingScaleError c (p : ℝ) D ≤ ε := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_samplingScaleReady c (p : ℝ) hc hp,
      (samplingScaleError_tendsto c (p : ℝ) hc hp).eventually_le_const hε] with D h1 h2 h3
    exact ⟨h1,h2,h3⟩
  obtain ⟨D₀,hD₀⟩ := hevent.exists_forall_of_atTop
  refine ⟨D₀, ?_⟩
  intro D hD V _ _ P _ hrlo hrhi hexp
  obtain ⟨h1, hready, herr⟩ := hD₀ D hD
  have hDpos : 0 < D := by linarith
  obtain ⟨hr,hτ,hM,hmiss,he,hperturb,hbound⟩ := hready (Fintype.card V) hrlo hrhi
  exact (vertex_sampling_failure_bound P p hp (by positivity) (by positivity)
    hτ (by positivity) hM hr hmiss he hperturb hexp).trans (hbound.trans herr)

end ErdosGallai.Sampling

open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Finset
noncomputable section
namespace ErdosGallai.Sampling

def reservoirLabelPMF (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) : PMF (Fin 4) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (if i = 3 then 1-3*(p : ℝ) else (p : ℝ))) (by
    rw [Fin.sum_univ_four]
    simp only [show (0 : Fin 4) ≠ 3 by decide, show (1 : Fin 4) ≠ 3 by decide,
      show (2 : Fin 4) ≠ 3 by decide, ↓reduceIte,  ]
    rw [← ENNReal.ofReal_add p.property.1 p.property.1,
      ← ENNReal.ofReal_add (by linarith [p.property.1]) p.property.1,
      ← ENNReal.ofReal_add (by linarith [p.property.1]) (by linarith)]
    norm_num [show (p : ℝ)+(p : ℝ)+(p : ℝ)+(1-3*(p : ℝ)) = 1 by ring])

def labelIs (i : Fin 3) (j : Fin 4) : Bool := decide (j = i.castSucc)

lemma ofReal_unitInterval (p : unitInterval) :
    ENNReal.ofReal (p : ℝ) = (unitInterval.toNNReal p : ENNReal) := by
  unfold ENNReal.ofReal
  apply congrArg (fun x : NNReal => (x : ENNReal))
  apply Subtype.ext
  exact Real.coe_toNNReal _ p.property.1

lemma labelIs_preserving (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) (i : Fin 3) :
    MeasurePreserving (labelIs i) (reservoirLabelPMF p hp).toMeasure
      (bernoulliMeasure true false p) := by
  have hnon : 0 ≤ (p : ℝ) := p.property.1
  have hnon' : 0 ≤ 1-3*(p : ℝ) := by linarith
  refine ⟨measurable_of_finite _, ?_⟩
  apply Measure.ext_iff_singleton.mpr
  intro b
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  rw [PMF.toMeasure_apply_fintype]
  simp only [reservoirLabelPMF]
  cases b <;> fin_cases i <;>
    simp [labelIs, Fin.sum_univ_four,  PMF.ofFintype_apply]
  all_goals
    first
    | exact ofReal_unitInterval p
    | rw [← ENNReal.ofReal_add hnon hnon,
        ← ENNReal.ofReal_add (by linarith : 0 ≤ (p : ℝ)+(p : ℝ)) hnon']
      convert ofReal_unitInterval (unitInterval.symm p) using 1
      congr 1
      change (p : ℝ)+(p : ℝ)+(1-3*(p : ℝ)) = 1-(p : ℝ)
      ring

end ErdosGallai.Sampling

namespace ErdosGallai.Sampling
noncomputable section
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

def reservoirSample (i : Fin 3) (ω : V → Fin 4) : V → Bool := fun v => labelIs i (ω v)

def reservoirMeasure (V : Type cycleUniverse2) [Fintype V] (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) :
    Measure (V → Fin 4) := Measure.pi (fun _ : V => (reservoirLabelPMF p hp).toMeasure)

instance reservoirMeasure_probability (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) :
    IsProbabilityMeasure (reservoirMeasure V p hp) := by unfold reservoirMeasure; infer_instance

lemma reservoirSample_preserving {V : Type cycleUniverse3} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) (i : Fin 3) :
    MeasurePreserving (reservoirSample i) (reservoirMeasure V p hp) (sampleMeasure V p) := by
  exact measurePreserving_pi _ _ (fun _ => labelIs_preserving p hp i)

lemma reservoirSamples_disjoint {V : Type cycleUniverse4} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (ω : V → Fin 4) (i j : Fin 3) (hij : i ≠ j) :
    Disjoint (sampleVertices (reservoirSample i ω)) (sampleVertices (reservoirSample j ω)) := by
  apply Finset.disjoint_left.mpr
  intro v hi hj
  simp only [sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    reservoirSample, labelIs, decide_eq_true_eq] at hi hj
  exact hij (Fin.castSucc_injective 3 (hi.symm.trans hj))

theorem three_reservoirs_uniform (c : ℝ) (hc : 0 < c) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hp3 : 3*(p : ℝ) ≤ 1) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (P : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (P i).Adj],
      D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) →
      (∀ i, CutExpansion (P i) (c*D^(9/10 : ℝ))) →
      ∃ W : Fin 3 → Finset V,
        (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧
        (∀ i, ((W i).card : ℝ) ≤ 2*(p : ℝ)*Fintype.card V) ∧
        (∀ i v, (p : ℝ)*(c*D^(9/10 : ℝ))/2 ≤ ((neighborsIn (P i) v (W i)).card : ℝ)) ∧
        (∀ i, CutExpansionOn (P i) (W i) (D^(37/50 : ℝ))) := by
  have hp1 : (p : ℝ) < 1 := by linarith
  obtain ⟨D₀,hD₀⟩ := vertex_sampling_uniform.{u} c hc p hp hp1 (1/4) (by norm_num)
  refine ⟨D₀, ?_⟩
  intro D hD V _ _ P _ hlo hhi hcut
  let μ := reservoirMeasure V p hp3
  let B : Fin 3 → Set (V → Fin 4) := fun i =>
    {ω | ¬SampleGood (P i) (p : ℝ) (c*D^(9/10 : ℝ)) (D^(37/50 : ℝ)) (reservoirSample i ω)}
  have hB : ∀ i, μ.real (B i) ≤ 1/4 := by
    intro i
    have hm := (reservoirSample_preserving (V := V) p hp3 i).measure_preimage
      ((Set.Finite.measurableSet (Set.toFinite {ω | ¬SampleGood (P i) (p : ℝ) (c*D^(9/10 : ℝ))
        (D^(37/50 : ℝ)) ω})).nullMeasurableSet)
    change (μ (B i)).toReal ≤ 1/4
    rw [show μ (B i) = (sampleMeasure V p) {ω | ¬SampleGood (P i) (p : ℝ)
      (c*D^(9/10 : ℝ)) (D^(37/50 : ℝ)) ω} from hm]
    exact hD₀ D hD V (P i) hlo hhi (hcut i)
  have hi : ∑ i ∈ (Finset.univ : Finset (Fin 3)), μ.real (B i) < 1 := by
    calc
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin 3)), (1/4 : ℝ) := by
        exact Finset.sum_le_sum (fun i _ => hB i)
      _ < 1 := by norm_num
  obtain ⟨ω,hω⟩ := exists_avoiding_finite_events (μ := μ) Finset.univ B hi
  have hgood : ∀ i, SampleGood (P i) (p : ℝ) (c*D^(9/10 : ℝ)) (D^(37/50 : ℝ))
      (reservoirSample i ω) := by
    intro i
    exact not_not.mp (hω i (Finset.mem_univ i))
  refine ⟨fun i => sampleVertices (reservoirSample i ω), reservoirSamples_disjoint ω,
    fun i => (hgood i).1, fun i => (hgood i).2.1, fun i => (hgood i).2.2⟩

end
end ErdosGallai.Sampling

end
end
end

/-! ### Upstream module `Combinatorics/CycleDecomposition/EdgeSplitting.lean` -/

section
open _root_.Filter _root_.Asymptotics _root_.Real
open scoped _root_.Topology
noncomputable section
open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Finset
noncomputable section
namespace ErdosGallai.Splitting
section BernoulliBounds
variable {Ω : Type cycleUniverse1} {I : Type cycleUniverse2} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma indicator_mem_Icc {Ω : Type cycleUniverse3} [_contextInstance1 : MeasurableSpace Ω] {X : Ω → ℝ} (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (ω : Ω) :
    X ω ∈ Set.Icc (0 : ℝ) 1 := by rcases hX ω with h | h <;> simp [h]

lemma mgf_indicator {X : Ω → ℝ} (hm : Measurable X)
    (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (p t : ℝ) (hp : ∫ ω, X ω ∂μ = p) :
    mgf X μ t = 1 + p * (exp t - 1) := by
  have hXi : Integrable X μ := Integrable.of_mem_Icc 0 1 hm.aemeasurable
    (ae_of_all _ (indicator_mem_Icc hX))
  have heq : (fun ω => exp (t * X ω)) = fun ω => (1 : ℝ) + (exp t - 1) * X ω := by
    funext ω
    rcases hX ω with h | h <;> simp [h]
  rw [mgf, heq, integral_add (integrable_const _) (hXi.const_mul _), integral_const_mul,
    hp, integral_const]
  simp [mul_comm]

lemma mgf_indicator_sum_bound {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p t : ℝ) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    mgf (∑ i ∈ s, X i) μ t ≤ exp ((s.card : ℝ) * p * (exp t - 1)) := by
  by_cases hs : s.Nonempty
  swap
  · have he := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]
  rw [hi.mgf_sum hm]
  have heq : (∏ i ∈ s, mgf (X i) μ t) = (1 + p * (exp t - 1)) ^ s.card := by
    simp_rw [mgf_indicator (hm _) (hX _) p t (hp _)]
    simp
  rw [heq]
  have hn : 0 ≤ 1 + p * (exp t - 1) := by
    obtain ⟨i, _⟩ := hs
    rw [← mgf_indicator (hm i) (hX i) p t (hp i)]
    exact mgf_nonneg
  calc
    (1 + p * (exp t - 1)) ^ s.card ≤ exp (p * (exp t - 1)) ^ s.card :=
      pow_le_pow_left₀ hn (by linarith [add_one_le_exp (p * (exp t - 1))]) _
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

lemma exp_neg_half_bound : exp (-(1 / 2 : ℝ)) ≤ 5 / 8 := by
  have he : exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) = exp 1 := by
    rw [← exp_add]; norm_num
  have hlow : (8 / 5 : ℝ) ≤ exp (1 / 2 : ℝ) := by
    nlinarith [exp_one_gt_d9, exp_pos (1 / 2 : ℝ)]
  rw [exp_neg]
  exact (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by norm_num at *; exact hlow)

theorem bernoulli_sum_lower_tail {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | (∑ i ∈ s, X i ω) ≤ p * s.card / 2} ≤ exp (-p * s.card / 8) := by
  have hInt : Integrable (fun ω => exp (-(1 / 2 : ℝ) * (∑ i ∈ s, X i) ω)) μ :=
    hi.integrable_exp_mul_sum hm (fun i _ => integrable_exp_mul_of_mem_Icc
      (hm i).aemeasurable (ae_of_all _ (indicator_mem_Icc (hX i))))
  have hb := measure_le_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (p * s.card / 2)
    (by norm_num : -(1 / 2 : ℝ) ≤ 0) hInt
  simp only [Finset.sum_apply] at hb
  apply hb.trans
  calc
    _ ≤ exp (-(-(1 / 2 : ℝ)) * (p * s.card / 2)) *
        exp ((s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      exact mul_le_mul_of_nonneg_left (mgf_indicator_sum_bound s hm hi hX p _ hp) (exp_pos _).le
    _ = exp (p * s.card / 4 + (s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_neg_half_bound
        (mul_nonneg (Nat.cast_nonneg s.card) hp0)]

end BernoulliBounds

noncomputable section
variable {V : Type cycleUniverse4} [Fintype V] [DecidableEq V]

def CutExpansion (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ) : Prop :=
  ∀ U : Finset V, h * min (U.card : ℝ) (Uᶜ.card : ℝ) ≤
    ((P.interedges U Uᶜ).card : ℝ)

lemma boundary_sym2_injective (P : SimpleGraph V) [DecidableRel P.Adj]
    (U : Finset V) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges U Uᶜ : Set (V × V)) := by
  intro e he f hf hef
  rcases (Sym2.mk_eq_mk_iff.mp hef) with h | h
  · exact h
  · have he1 := (P.mem_interedges_iff.mp he).1
    have hf2 := (P.mem_interedges_iff.mp hf).2.1
    have hfirst : e.1 = f.2 := congrArg Prod.fst h
    exact False.elim ((Finset.mem_compl.mp hf2) (hfirst ▸ he1))

def edgeColorMeasure (V : Type cycleUniverse5) [Fintype V] (l : ℕ) [NeZero l] :
    Measure (Sym2 V → Fin l) :=
  Measure.pi (fun _ : Sym2 V => (PMF.uniformOfFintype (Fin l)).toMeasure)

instance edgeColorMeasure_probability (l : ℕ) [NeZero l] :
    IsProbabilityMeasure (edgeColorMeasure V l) := by
  unfold edgeColorMeasure
  infer_instance

def colorIndicator {l : ℕ} (i : Fin l) (e : Sym2 V) (ω : Sym2 V → Fin l) : ℝ :=
  if ω e = i then 1 else 0

lemma colorIndicator_indep {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {l : ℕ} [NeZero l] (i : Fin l) :
    iIndepFun (colorIndicator (V := V) i) (edgeColorMeasure V l) := by
  exact iIndepFun_pi (X := fun _ : Sym2 V => fun j : Fin l => if j = i then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)

lemma colorIndicator_integral {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {l : ℕ} [NeZero l] (i : Fin l) (e : Sym2 V) :
    ∫ ω, colorIndicator i e ω ∂edgeColorMeasure V l = 1/(l : ℝ) := by
  have hl := (measurePreserving_eval
    (fun _ : Sym2 V => (PMF.uniformOfFintype (Fin l)).toMeasure) e).hasLaw
  have hi := hl.integral_comp (f := fun j : Fin l => if j = i then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable
  rw [PMF.integral_eq_sum] at hi
  simpa [edgeColorMeasure, colorIndicator, PMF.uniformOfFintype_apply] using hi

def colorGraph (P : SimpleGraph V) {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) :
    SimpleGraph V where
  Adj x y := P.Adj x y ∧ ω s(x,y) = i
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro x h; exact P.irrefl h.1⟩

instance colorGraph_decidable (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) :
    DecidableRel (colorGraph P ω i).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

lemma colorGraph_interedges {V : Type cycleUniverse8} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) (S T : Finset V) :
    (colorGraph P ω i).interedges S T =
      (P.interedges S T).filter (fun e => ω s(e.1,e.2) = i) := by
  ext ⟨x,y⟩
  simp only [SimpleGraph.mem_interedges_iff, Finset.mem_filter]
  change (x ∈ S ∧ y ∈ T ∧ (P.Adj x y ∧ ω s(x,y) = i)) ↔ _
  tauto

lemma color_cut_sum (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) (S : Finset V) :
    (∑ e ∈ (P.interedges S Sᶜ).image (fun e => s(e.1,e.2)), colorIndicator i e ω) =
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) := by
  rw [Finset.sum_image (boundary_sym2_injective P S)]
  simp only [colorIndicator, Finset.sum_boole, colorGraph_interedges]

lemma color_cut_lower_tail (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] (i : Fin l) (S : Finset V) {h : ℝ}
    (hexp : CutExpansion P h) (hS : S.card ≤ Sᶜ.card) :
    (edgeColorMeasure V l).real {ω |
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} ≤
        exp (-h*S.card/(8*l)) := by
  let E := (P.interedges S Sᶜ).image (fun e => s(e.1,e.2))
  have hcard : E.card = (P.interedges S Sᶜ).card :=
    Finset.card_image_of_injOn (boundary_sym2_injective P S)
  have hl : 0 < (l : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne l)
  have hcut : h * S.card ≤ (E.card : ℝ) := by
    rw [hcard]
    have he := hexp S
    rwa [min_eq_left (by exact_mod_cast hS)] at he
  have hb := bernoulli_sum_lower_tail (μ := edgeColorMeasure V l) E
    (fun e => measurable_of_finite (colorIndicator i e)) (colorIndicator_indep i)
    (fun e ω => by simp only [colorIndicator]; split <;> simp)
    (1/(l : ℝ)) (by positivity) (colorIndicator_integral i)
  apply (measureReal_mono (show {ω |
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} ⊆
      {ω | (∑ e ∈ E, colorIndicator i e ω) ≤ (1/(l : ℝ))*E.card/2} from ?_)).trans
      (hb.trans ?_)
  · intro ω hω
    change (∑ e ∈ E, colorIndicator i e ω) ≤ (1/(l : ℝ))*E.card/2
    rw [show (∑ e ∈ E, colorIndicator i e ω) =
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) from color_cut_sum P ω i S]
    calc
      _ ≤ h*S.card/(2*l) := le_of_lt hω
      _ ≤ (E.card : ℝ)/(2*l) := div_le_div_of_nonneg_right hcut (by positivity)
      _ = _ := by ring
  · apply exp_le_exp.mpr
    have he := div_le_div_of_nonneg_right hcut (show 0 ≤ 8*(l : ℝ) by positivity)
    calc
      _ = -((E.card : ℝ)/(8*l)) := by ring
      _ ≤ -(h*S.card/(8*l)) := neg_le_neg he
      _ = _ := by ring

lemma cutExpansion_of_small_cuts (P : SimpleGraph V) [DecidableRel P.Adj] {h : ℝ}
    (hcut : ∀ S : Finset V, S.Nonempty → S.card ≤ Sᶜ.card →
      h*S.card ≤ ((P.interedges S Sᶜ).card : ℝ)) : CutExpansion P h := by
  intro S
  by_cases he : S = ∅
  · simp [he]
  by_cases hc : Sᶜ = ∅
  · simp [hc]
  by_cases hs : S.card ≤ Sᶜ.card
  · rw [min_eq_left (by exact_mod_cast hs)]
    exact hcut S (Finset.nonempty_iff_ne_empty.mpr he) hs
  · rw [min_eq_right (by exact_mod_cast le_of_not_ge hs)]
    have hi := hcut Sᶜ (Finset.nonempty_iff_ne_empty.mpr hc) (by simpa using le_of_not_ge hs)
    have hcomm : (P.interedges Sᶜ S).card = (P.interedges S Sᶜ).card := by
      have := P.symm
      exact Rel.card_interedges_comm Sᶜ S
    simpa only [compl_compl, hcomm] using hi

lemma sum_nonempty_subsets_power (q : ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Finset V)).erase ∅, q^S.card) =
      (1+q)^(Fintype.card V)-1 := by
  have hs := Finset.sum_erase_add (s := Finset.univ) (fun S : Finset V => q^S.card)
    (Finset.mem_univ (∅ : Finset V))
  have hp := Finset.prod_one_add (s := (Finset.univ : Finset V)) (f := fun _ => q)
  simp only [Finset.prod_const, Finset.card_univ, Finset.powerset_univ] at hp
  simp only [Finset.card_empty, pow_zero] at hs
  linarith

theorem edge_splitting_failure_bound (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] {h : ℝ} (hexp : CutExpansion P h) :
    (edgeColorMeasure V l).real {ω | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} ≤
      l * (exp ((Fintype.card V : ℝ)*exp (-h/(8*l)))-1) := by
  let cuts : Finset (Finset V) := Finset.univ.erase ∅
  let B (i : Fin l) (S : Finset V) : Set (Sym2 V → Fin l) :=
    {ω | S.card ≤ Sᶜ.card ∧
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)}
  let q : ℝ := exp (-h/(8*l))
  have cover : {ω | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin l)), ⋃ S ∈ cuts, B i S := by
    intro ω hω
    rcases hω with ⟨i, hi⟩
    by_contra hn
    apply hi
    apply cutExpansion_of_small_cuts
    intro S hS hs
    have hb : ω ∉ B i S := by
      intro hm
      apply hn
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ _,
        Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr
          ⟨Finset.mem_erase.mpr ⟨hS.ne_empty, Finset.mem_univ _⟩, hm⟩⟩⟩⟩
    have hc : h*S.card/(2*l) ≤ (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) := by
      exact le_of_not_gt (fun hf => hb ⟨hs, hf⟩)
    convert hc using 1 ; ring
  have hbound (i : Fin l) (S : Finset V) :
      (edgeColorMeasure V l).real (B i S) ≤ q^S.card := by
    by_cases hs : S.card ≤ Sᶜ.card
    · calc
        _ ≤ (edgeColorMeasure V l).real {ω |
            (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} :=
          measureReal_mono (fun _ hw => hw.2)
        _ ≤ exp (-h*S.card/(8*l)) := color_cut_lower_tail P i S hexp hs
        _ = q^S.card := by dsimp [q]; rw [← exp_nat_mul]; congr 1; ring
    · have he : B i S = ∅ := by ext ω; simp [B,hs]
      rw [he, measureReal_empty]
      exact pow_nonneg (exp_pos _).le _
  calc
    _ ≤ (edgeColorMeasure V l).real
        (⋃ i ∈ (Finset.univ : Finset (Fin l)), ⋃ S ∈ cuts, B i S) :=
      measureReal_mono cover (measure_ne_top _ _)
    _ ≤ ∑ i : Fin l, (edgeColorMeasure V l).real (⋃ S ∈ cuts, B i S) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ i : Fin l, ∑ S ∈ cuts, (edgeColorMeasure V l).real (B i S) :=
      Finset.sum_le_sum (fun _ _ => measureReal_biUnion_finset_le _ _)
    _ ≤ ∑ _i : Fin l, ∑ S ∈ cuts, q^S.card := by
      apply Finset.sum_le_sum; intro i _; exact Finset.sum_le_sum (fun S _ => hbound i S)
    _ = (l : ℝ)*((1+q)^(Fintype.card V)-1) := by
      simp only [cuts, sum_nonempty_subsets_power, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    _ ≤ l*(exp ((Fintype.card V : ℝ)*q)-1) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg l)
      apply sub_le_sub_right
      calc
        _ ≤ (exp q)^(Fintype.card V) :=
          pow_le_pow_left₀ (by dsimp [q]; positivity) (by linarith [add_one_le_exp q]) _
        _ = _ := (exp_nat_mul _ _).symm

theorem edge_splitting_of_error_lt_one (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] {h : ℝ} (hexp : CutExpansion P h)
    (herror : (l : ℝ)*(exp ((Fintype.card V : ℝ)*exp (-h/(8*l)))-1) < 1) :
    ∃ ω : Sym2 V → Fin l,
      (∀ i, CutExpansion (colorGraph P ω i) (h/(2*l))) ∧
      (∀ x y, P.Adj x y ↔ ∃ i, (colorGraph P ω i).Adj x y) ∧
      (∀ i j, i ≠ j → Disjoint (colorGraph P ω i).edgeSet (colorGraph P ω j).edgeSet) := by
  have he := (edge_splitting_failure_bound P hexp).trans_lt herror
  have hh : ∃ ω : Sym2 V → Fin l, ∀ i, CutExpansion (colorGraph P ω i) (h/(2*l)) := by
    by_contra hn
    push Not at hn
    have hall : {ω : Sym2 V → Fin l | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} =
        Set.univ := Set.eq_univ_of_forall hn
    simp only [hall, Measure.real, measure_univ, ENNReal.toReal_one] at he
    exact (lt_irrefl _ he)
  obtain ⟨ω, hω⟩ := hh
  refine ⟨ω, hω, ?_, ?_⟩
  · intro x y
    exact ⟨fun hxy => ⟨ω s(x,y), hxy, rfl⟩, fun ⟨_, hxy, _⟩ => hxy⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro e hei hej
    induction e using Sym2.ind with | _ x y =>
      have hi : (colorGraph P ω i).Adj x y := by simpa using hei
      have hj : (colorGraph P ω j).Adj x y := by simpa using hej
      exact hij (hi.2.symm.trans hj.2)

end

lemma tendsto_monomial_exp_neg_power (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun D : ℝ => D^a * exp (-c * D^b)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a/b) c hc).comp
    (tendsto_rpow_atTop hb)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul hD.le, mul_div_cancel₀ _ hb.ne']

noncomputable def edgeSplittingScaleError (c : ℝ) (l : ℕ) (D : ℝ) : ℝ :=
  (l : ℝ) * (Real.exp (D^(51/50 : ℝ) * Real.exp ((-(c / (8*l))) * D^(9/10 : ℝ))) - 1)

lemma edgeSplittingScaleError_tendsto (c : ℝ) (hc : 0 < c) (l : ℕ) (hl : 0 < l) :
    Tendsto (edgeSplittingScaleError c l) atTop (𝓝 0) := by
  have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
  have ht := tendsto_monomial_exp_neg_power (51/50) (9/10) (c/(8*l))
    (by norm_num) (by positivity)
  have hh := ((Real.continuous_exp.tendsto 0).comp ht).sub_const 1 |>.const_mul (l : ℝ)
  unfold edgeSplittingScaleError
  convert hh using 1 <;> norm_num

theorem edge_splitting_uniform (c : ℝ) (hc : 0 < c) (l : ℕ) (hl : 0 < l) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ),
      c*D^(9/10 : ℝ) ≤ h → D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) → CutExpansion P h →
      ∃ ω : Sym2 V → Fin l,
        (∀ i, CutExpansion (colorGraph P ω i) (h/(2*l))) ∧
        (∀ x y, P.Adj x y ↔ ∃ i, (colorGraph P ω i).Adj x y) ∧
        (∀ i j, i ≠ j → Disjoint (colorGraph P ω i).edgeSet (colorGraph P ω j).edgeSet) := by
  have : NeZero l := ⟨hl.ne'⟩
  have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
  have hevent := (edgeSplittingScaleError_tendsto c hc l hl).eventually_lt_const
    (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨D₀,hD₀⟩ := hevent.exists_forall_of_atTop
  refine ⟨D₀, ?_⟩
  intro D hD V _ _ P _ h hh _hrlo hrhi hexp
  apply edge_splitting_of_error_lt_one P hexp
  apply lt_of_le_of_lt _ (hD₀ D hD)
  unfold edgeSplittingScaleError
  apply mul_le_mul_of_nonneg_left _ hlR.le
  apply sub_le_sub_right
  apply exp_le_exp.mpr
  apply mul_le_mul hrhi _ (exp_pos _).le ((Nat.cast_nonneg (Fintype.card V)).trans hrhi)
  apply exp_le_exp.mpr
  have he := div_le_div_of_nonneg_right hh (show 0 ≤ 8*(l : ℝ) by positivity)
  calc
    -h/(8*l) = -(h/(8*l)) := by ring
    _ ≤ -(c*D^(9/10 : ℝ)/(8*l)) := neg_le_neg he
    _ = -(c/(8*l))*D^(9/10 : ℝ) := by ring

end ErdosGallai.Splitting

end
end
end

/-! ### Upstream module `Combinatorics/CycleDecomposition/Representatives.lean` -/

section
open _root_.Filter _root_.Asymptotics _root_.Real
noncomputable section
open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Finset
noncomputable section
namespace ErdosGallai.Representatives
noncomputable section
variable {I : Type cycleUniverse1} {V : Type cycleUniverse2} [DecidableEq I] [DecidableEq V] [Nonempty V]

lemma choose_with_mates (A : Finset I) (mate : I → I)
    (hmate : Function.Involutive mate) (hfix : ∀ i, mate i ≠ i)
    (N : I → Finset V) (k : ℕ)
    (hroom : ∀ i ∈ A, A.card ≤ ((N i).card - 1) * k) :
    ∃ f : I → V, (∀ i ∈ A, f i ∈ N i) ∧
      (∀ i ∈ A, mate i ∈ A → f i ≠ f (mate i)) ∧
      (∀ v, (A.filter (fun i => f i = v)).card ≤ k) := by
  induction A using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.choice inferInstance, by simp⟩
  | @insert i A hi ih =>
    obtain ⟨f,hf,hsep,hcap⟩ := ih (by
      intro j hj
      exact (Finset.card_le_card (Finset.subset_insert i A)).trans (hroom j (by simp [hj])))
    have hlt : A.card < ((N i).erase (f (mate i))).card * k := by
      have h := hroom i (by simp)
      have hcard := Finset.pred_card_le_card_erase (s := N i) (a := f (mate i))
      have hmul := Nat.mul_le_mul_right k hcard
      rw [Finset.card_insert_of_notMem hi] at h
      omega
    obtain ⟨v,hv,hload⟩ := Finset.exists_card_fiber_lt_of_card_lt_mul (f := f) hlt
    have hvN := (Finset.mem_erase.mp hv).2
    have hvne := (Finset.mem_erase.mp hv).1
    let g := Function.update f i v
    have gi : g i = v := by simp [g]
    have gold : ∀ j, j ≠ i → g j = f j := by
      intro j hj
      simp [g, hj]
    refine ⟨g, ?_, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa only [gi] using hvN
      · rw [gold j (ne_of_mem_of_not_mem hj hi)]
        exact hf j hj
    · intro j hj hmj
      by_cases hji : j = i
      · subst j
        rw [gi, gold (mate i) (hfix i)]
        exact hvne
      · rw [gold j hji]
        by_cases hmi : mate j = i
        · rw [hmi, gi]
          have hjm : j = mate i := by rw [← hmi, hmate]
          simpa [hjm] using hvne.symm
        · rw [gold (mate j) hmi]
          exact hsep j (Finset.mem_of_mem_insert_of_ne hj hji)
            (Finset.mem_of_mem_insert_of_ne hmj hmi)
    · intro w
      have hold : A.filter (fun j => g j = w) = A.filter (fun j => f j = w) := by
        apply Finset.filter_congr
        intro j hj
        rw [gold j (ne_of_mem_of_not_mem hj hi)]
      rw [Finset.filter_insert, hold]
      by_cases hvw : v = w
      · simp only [gi, hvw, ite_eq_left]
        rw [Finset.card_insert_of_notMem (fun h => hi (Finset.mem_filter.mp h).1)]
        simpa only [hvw] using Nat.succ_le_of_lt hload
      · simp only [gi, hvw, ite_false]
        exact hcap w

theorem two_distinct_representatives (S : Finset I) (N : I → Finset V) (k : ℕ)
    (hroom : ∀ i ∈ S, 2*S.card ≤ ((N i).card-1)*k) :
    ∃ f : I × Fin 2 → V,
      (∀ i ∈ S, ∀ t, f (i,t) ∈ N i) ∧
      (∀ i ∈ S, f (i,0) ≠ f (i,1)) ∧
      (∀ v, ((S ×ˢ Finset.univ).filter (fun i => f i = v)).card ≤ k) := by
  let mate : I × Fin 2 → I × Fin 2 := fun i => (i.1, 1-i.2)
  have hm : Function.Involutive mate := by
    rintro ⟨i,t⟩
    fin_cases t <;> rfl
  have hfix : ∀ i, mate i ≠ i := by
    rintro ⟨i,t⟩
    fin_cases t <;> (intro h; have hh := congrArg Prod.snd h; norm_num [mate] at hh)
  obtain ⟨f,hf,hsep,hcap⟩ := choose_with_mates (S ×ˢ Finset.univ) mate hm hfix
    (fun i => N i.1) k (by
      intro i hi
      simpa [Finset.card_product, mul_comm] using hroom i.1 (Finset.mem_product.mp hi).1)
  refine ⟨f, ?_, ?_, hcap⟩
  · intro i hi t
    exact hf (i,t) (by simp [hi])
  · intro i hi
    exact hsep (i,0) (by simp [hi]) (by simp [mate, hi])

theorem reservoir_representatives (S : Finset I) (N : I → Finset V)
    (r d : ℝ) (hr : (S.card : ℝ) ≤ r) (hd : 4 ≤ d)
    (hN : ∀ i ∈ S, d/2 ≤ ((N i).card : ℝ)) :
    ∃ f : I × Fin 2 → V,
      (∀ i ∈ S, ∀ t, f (i,t) ∈ N i) ∧
      (∀ i ∈ S, f (i,0) ≠ f (i,1)) ∧
      (∀ v, ((S ×ˢ Finset.univ).filter (fun i => f i = v)).card ≤ ⌈8*r/d⌉₊) := by
  apply two_distinct_representatives
  intro i hi
  have hd0 : 0 < d := by linarith
  have hr0 : 0 ≤ r := le_trans (Nat.cast_nonneg _) hr
  have hNi := hN i hi
  have hNi1 : 1 ≤ (N i).card := by exact_mod_cast (by linarith : (1 : ℝ) ≤ (N i).card)
  have hn : d/4 ≤ (((N i).card - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hNi1]
    push_cast
    linarith
  have hk : 8*r/d ≤ (⌈8*r/d⌉₊ : ℝ) := Nat.le_ceil _
  have hk0 : 0 ≤ (⌈8*r/d⌉₊ : ℝ) := Nat.cast_nonneg _
  have hprod : 2*(S.card : ℝ) ≤ (((N i).card - 1 : ℕ) : ℝ)*(⌈8*r/d⌉₊ : ℝ) := by
    calc
      _ ≤ 2*r := by linarith
      _ = (d/4)*(8*r/d) := by field_simp; ring
      _ ≤ (d/4)*(⌈8*r/d⌉₊ : ℝ) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hn hk0
  exact_mod_cast hprod

end
end ErdosGallai.Representatives

namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable

noncomputable def reservoirProbability (η : ℝ) : ℝ := min (η/12) (1/12)
noncomputable def reservoirExpansionCoefficient (c : ℝ) : ℝ := min c 1 / 6

theorem reservoir_preparation (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G P : SimpleGraph V) [DecidableRel P.Adj], P ≤ G →
      D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) →
      Splitting.CutExpansion P (c*D^(9/10 : ℝ)) →
      ∃ (ω : Sym2 V → Fin 3) (W : Fin 3 → Finset V) (f : Fin 3 → V × Fin 2 → V),
        (∀ i, Splitting.colorGraph P ω i ≤ G) ∧
        (∀ i j, i ≠ j → Disjoint (Splitting.colorGraph P ω i).edgeSet
            (Splitting.colorGraph P ω j).edgeSet) ∧
        (∀ i, Splitting.CutExpansion (Splitting.colorGraph P ω i)
          (reservoirExpansionCoefficient c * D^(9/10 : ℝ))) ∧
        (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧
        (∀ i, 2 ≤ (W i).card) ∧
        (∀ i, ((W i).card : ℝ) ≤ 2*reservoirProbability η*Fintype.card V) ∧
        (∀ i, (W i).card < Fintype.card V) ∧
        ((∑ i, (W i).card : ℕ) : ℝ) ≤ η * Fintype.card V ∧
        (∀ i, Sampling.CutExpansionOn (Splitting.colorGraph P ω i) (W i)
          (D^(37/50 : ℝ))) ∧
        (∀ i v, v ∉ W i → ∀ t, f i (v,t) ∈ W i ∧
          (Splitting.colorGraph P ω i).Adj v (f i (v,t))) ∧
        (∀ i v, v ∉ W i → f i (v,0) ≠ f i (v,1)) ∧
        (∀ i w, (((W i)ᶜ ×ˢ Finset.univ).filter (fun x => f i x = w)).card ≤
          ⌈8*(Fintype.card V : ℝ) /
            (reservoirProbability η * (reservoirExpansionCoefficient c * D^(9/10 : ℝ)))⌉₊) := by
  let c₀ := min c 1
  let a := reservoirExpansionCoefficient c
  let q := reservoirProbability η
  have hc₀ : 0 < c₀ := lt_min hc (by norm_num)
  have ha : 0 < a := by dsimp [a, reservoirExpansionCoefficient]; positivity
  have hq : 0 < q := by dsimp [q, reservoirProbability]; positivity
  have hq12 : q ≤ 1/12 := min_le_right _ _
  have hqη : q ≤ η/12 := min_le_left _ _
  have hq3 : 3*q ≤ 1 := by linarith
  have hq6 : 6*q ≤ η := by linarith
  have hq2 : 2*q < 1 := by linarith
  let p : unitInterval := ⟨q, hq.le, by linarith⟩
  obtain ⟨D₁,hD₁⟩ := Splitting.edge_splitting_uniform.{u} c₀ hc₀ 3 (by norm_num)
  obtain ⟨D₂,hD₂⟩ := Sampling.three_reservoirs_uniform.{u} a ha p hq hq3
  have ht : ∀ᶠ D : ℝ in atTop, 4/(q*a) ≤ D^(9/10 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9/10)).eventually
      (eventually_ge_atTop _)
  obtain ⟨D₃,hD₃⟩ := ht.exists_forall_of_atTop
  refine ⟨max 1 (max D₁ (max D₂ D₃)), ?_⟩
  intro D hD V _ _ G P _ hPG hlo hhi hexp
  have hD1 : 1 ≤ D := (le_max_left _ _).trans hD
  have hDsplit : D₁ ≤ D := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hD
  have hDsample : D₂ ≤ D :=
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hD
  have hDpower : D₃ ≤ D :=
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hD
  have hpow : 0 < D^(9/10 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hd : 4 ≤ q*(a*D^(9/10 : ℝ)) := by
    have hh := (div_le_iff₀ (mul_pos hq ha)).mp (hD₃ D hDpower)
    nlinarith
  have hr : 0 < (Fintype.card V : ℝ) := hpow.trans_le hlo
  have : Nonempty V := Fintype.card_pos_iff.mp (by exact_mod_cast hr)
  have hexp₀ : Splitting.CutExpansion P (c₀*D^(9/10 : ℝ)) := by
    intro U
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left c 1) hpow.le)
      (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans (hexp U)
  obtain ⟨ω,hcut,hcover,hdisj⟩ := hD₁ D hDsplit V P
    (c₀*D^(9/10 : ℝ)) le_rfl hlo hhi hexp₀
  have hcut' : ∀ i, Sampling.CutExpansion (Splitting.colorGraph P ω i)
      (a*D^(9/10 : ℝ)) := by
    intro i
    have heq : a*D^(9/10 : ℝ) = c₀*D^(9/10 : ℝ)/(2*(3 : ℝ)) := by
      dsimp [a, reservoirExpansionCoefficient, c₀]
      ring
    rw [heq]
    exact hcut i
  obtain ⟨W,hWdisj,hWsize,hWneigh,hWcut⟩ := hD₂ D hDsample V
    (fun i => Splitting.colorGraph P ω i) hlo hhi hcut'
  have hWtwo : ∀ i, 2 ≤ (W i).card := by
    intro i
    let v : V := Classical.choice inferInstance
    have hn := hWneigh i v
    have hsub : Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i) ⊆ W i :=
      Finset.filter_subset _ _
    have hh := Finset.card_le_card hsub
    have hn' : (2 : ℝ) ≤ (Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i)).card := by
      change q*(a*D^(9/10 : ℝ))/2 ≤ _ at hn
      linarith
    have hn'' : 2 ≤ (Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i)).card := by
      exact_mod_cast hn'
    omega
  have hWlt : ∀ i, (W i).card < Fintype.card V := by
    intro i
    have hh := (hWsize i).trans_lt (mul_lt_of_lt_one_left hr hq2)
    exact_mod_cast hh
  have hWsum : ((∑ i, (W i).card : ℕ) : ℝ) ≤ η * Fintype.card V := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hWsize i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    rw [Nat.cast_sum]
    exact hh.trans (by dsimp [p]; nlinarith [mul_le_mul_of_nonneg_right hq6 hr.le])
  have hrep : ∀ i, ∃ f : V × Fin 2 → V,
      (∀ v ∈ (W i)ᶜ, ∀ t, f (v,t) ∈ Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i)) ∧
      (∀ v ∈ (W i)ᶜ, f (v,0) ≠ f (v,1)) ∧
      (∀ w, (((W i)ᶜ ×ˢ Finset.univ).filter (fun x => f x = w)).card ≤
        ⌈8*(Fintype.card V : ℝ)/(q*(a*D^(9/10 : ℝ)))⌉₊) := by
    intro i
    exact Representatives.reservoir_representatives (W i)ᶜ
      (fun v => Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i))
      (Fintype.card V) (q*(a*D^(9/10 : ℝ)))
      (by exact_mod_cast (Finset.card_le_univ ((W i)ᶜ))) hd
      (fun v _ => hWneigh i v)
  choose f hf hsep hcap using hrep
  refine ⟨ω,W,f,?_,hdisj,?_,hWdisj,hWtwo,hWsize,hWlt,hWsum,hWcut,?_,?_,hcap⟩
  · intro i x y hxy
    exact hPG hxy.1
  · exact hcut'
  · intro i v hv t
    exact Finset.mem_filter.mp (hf i v (Finset.mem_compl.mpr hv) t)
  · intro i v hv
    exact hsep i v (Finset.mem_compl.mpr hv)

end
end ErdosGallai

end
end
end

/-! ### Upstream module `Combinatorics/CycleDecomposition/Routing.lean` -/

section
open _root_.Filter _root_.Asymptotics _root_.Real
noncomputable section
noncomputable section
namespace ErdosGallai

variable {V : Type} [Fintype V] [DecidableEq V]

def CutExpansion (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ) : Prop :=
  ∀ U : Finset V, h * min (U.card : ℝ) (Uᶜ.card : ℝ) ≤
    ((P.interedges U Uᶜ).card : ℝ)

lemma boundary_sym2_injective (P : SimpleGraph V) [DecidableRel P.Adj]
    (U : Finset V) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges U Uᶜ : Set (V × V)) := by
  intro e he f hf hef
  rcases (Sym2.mk_eq_mk_iff.mp hef) with h | h
  · exact h
  · have he1 := (P.mem_interedges_iff.mp he).1
    have hf2 := (P.mem_interedges_iff.mp hf).2.1
    have hfirst : e.1 = f.2 := congrArg Prod.fst h
    exact False.elim ((Finset.mem_compl.mp hf2) (hfirst ▸ he1))

theorem routing_union_growth_step_of_boundary
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h)
    (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (B Bnext : Finset V)
    (W : V → Finset V)
    (hmono : B ⊆ Bnext)
    (hsmall : (B.card : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hF : (((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card : ℝ) ≤
      h * (B.card : ℝ) / 4)
    (hW : ∀ v ∈ B, ((W v).card : ℝ) ≤ h / 4)
    (hextend : ∀ v ∈ B, ∀ w ∉ B, P.Adj v w → s(v, w) ∉ F →
      w ∉ W v → w ∈ Bnext) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (B.card : ℝ) ≤
      (Bnext.card : ℝ) := by
  let E := P.interedges B Bᶜ
  let Ebad := E.filter (fun e => s(e.1, e.2) ∈ F)
  let Vbad := B.biUnion (fun v => ({v} : Finset V) ×ˢ (W v))
  let Enew := (Finset.univ : Finset V) ×ˢ (Bnext \ B)
  have hcover : E ⊆ Ebad ∪ Vbad ∪ Enew := by
    intro e he
    rcases P.mem_interedges_iff.mp he with ⟨hv, hw, hadj⟩
    have hnw : e.2 ∉ B := Finset.mem_compl.mp hw
    by_cases hdel : s(e.1, e.2) ∈ F
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨he, hdel⟩))
    by_cases hforbid : e.2 ∈ W e.1
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨e.1, hv, Finset.mem_product.mpr ⟨by simp, hforbid⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_sdiff.mpr
        ⟨hextend e.1 hv e.2 hnw hadj hdel hforbid, hnw⟩⟩
  have hcount : E.card ≤ Ebad.card + Vbad.card + Enew.card :=
    (Finset.card_le_card hcover).trans <|
      (Finset.card_union_le _ _).trans <|
        Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hforbidden : Vbad.card ≤ ∑ v ∈ B, (W v).card := by
    simpa [Vbad, Finset.card_product] using
      (Finset.card_biUnion_le (s := B) (t := fun v => ({v} : Finset V) ×ˢ W v))
  have hnew : Enew.card = Fintype.card V * (Bnext \ B).card := by
    simp [Enew]
  have hraw : E.card ≤ Ebad.card + (∑ v ∈ B, (W v).card) +
      Fintype.card V * (Bnext \ B).card := by omega
  have hsum : (∑ v ∈ B, ((W v).card : ℝ)) ≤ (h / 4) * B.card := by
    calc
      _ ≤ ∑ _v ∈ B, h / 4 := Finset.sum_le_sum hW
      _ = _ := by simp [mul_comm]
  have hcomplN : B.card + Bᶜ.card = Fintype.card V := by
    rw [Finset.card_compl]
    exact Nat.add_sub_of_le (Finset.card_le_univ B)
  have hcompl : (B.card : ℝ) + (Bᶜ.card : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast hcomplN
  have hlecompl : (B.card : ℝ) ≤ (Bᶜ.card : ℝ) := by linarith
  have hcut : h * (B.card : ℝ) ≤ (E.card : ℝ) := by
    simpa [min_eq_left hlecompl, E] using hexp B
  have hdiffN : (Bnext \ B).card + B.card = Bnext.card := by
    rw [Finset.card_sdiff_of_subset hmono]
    exact Nat.sub_add_cancel (Finset.card_le_card hmono)
  have hdiff : ((Bnext \ B).card : ℝ) + (B.card : ℝ) = (Bnext.card : ℝ) := by
    exact_mod_cast hdiffN
  have hrawR : (E.card : ℝ) ≤ (Ebad.card : ℝ) +
      (∑ v ∈ B, ((W v).card : ℝ)) +
      (Fintype.card V : ℝ) * ((Bnext \ B).card : ℝ) := by
    exact_mod_cast hraw
  have hreach : h * (B.card : ℝ) / 2 ≤
      (Fintype.card V : ℝ) * ((Bnext \ B).card : ℝ) := by
    nlinarith [hcut, hrawR, hF, hsum]
  have hdiv : h * (B.card : ℝ) / (2 * (Fintype.card V : ℝ)) ≤
      ((Bnext \ B).card : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (Fintype.card V : ℝ))).mpr
    nlinarith [hreach]
  calc
    (1 + h / (2 * (Fintype.card V : ℝ))) * (B.card : ℝ)
        = (B.card : ℝ) + h * (B.card : ℝ) / (2 * (Fintype.card V : ℝ)) := by ring
    _ ≤ (B.card : ℝ) + ((Bnext \ B).card : ℝ) := add_le_add (le_refl _) hdiv
    _ = (Bnext.card : ℝ) := by linarith

def avoidGraph (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V) :
    SimpleGraph V where
  Adj v w := P.Adj v w ∧ s(v, w) ∉ F ∧ v ∉ W ∧ w ∉ W
  symm := ⟨by
    intro v w h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2.1, h.2.2.2, h.2.2.1⟩⟩
  loopless := ⟨by intro v h; exact P.irrefl h.1⟩

noncomputable def walkBall (G : SimpleGraph V) (s : V) (t : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ p : G.Walk s v, p.length ≤ t)

@[simp] lemma mem_walkBall {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (s v : V) (t : ℕ) :
    v ∈ walkBall G s t ↔ ∃ p : G.Walk s v, p.length ≤ t := by
  classical
  simp [walkBall]

lemma root_mem_walkBall (G : SimpleGraph V) (s : V) (t : ℕ) :
    s ∈ walkBall G s t := by
  exact (mem_walkBall G s s t).mpr ⟨.nil, by simp⟩

lemma walkBall_mono (G : SimpleGraph V) (s : V) {t u : ℕ} (htu : t ≤ u) :
    walkBall G s t ⊆ walkBall G s u := by
  intro v hv
  obtain ⟨p, hp⟩ := (mem_walkBall G s v t).mp hv
  exact (mem_walkBall G s v u).mpr ⟨p, hp.trans htu⟩

lemma walk_avoids_end {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s v : V} (p : (avoidGraph P F W).Walk s v) (hs : s ∉ W) : v ∉ W := by
  induction p with
  | nil => exact hs
  | cons hadj p ih => exact ih hadj.2.2.2

lemma ball_avoids (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    (s : V) (hs : s ∉ W) (t : ℕ) : Disjoint (walkBall (avoidGraph P F W) s t) W := by
  apply Finset.disjoint_left.mpr
  intro v hv
  obtain ⟨p, _⟩ := (mem_walkBall _ _ _ _).mp hv
  exact walk_avoids_end P F W p hs

lemma walkBall_step (G : SimpleGraph V) (s v w : V) (t : ℕ)
    (hv : v ∈ walkBall G s t) (hadj : G.Adj v w) :
    w ∈ walkBall G s (t + 1) := by
  obtain ⟨p, hp⟩ := (mem_walkBall _ _ _ _).mp hv
  apply (mem_walkBall _ _ _ _).mpr
  exact ⟨p.concat hadj, by simpa using Nat.add_le_add_right hp 1⟩

lemma CutExpansion.le_order (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V) :
    h ≤ (Fintype.card V : ℝ) := by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  have hcomplN : 1 ≤ ({v} : Finset V)ᶜ.card := by
    simp only [Finset.card_compl, Finset.card_singleton]
    omega
  have hcompl : (1 : ℝ) ≤ (({v} : Finset V)ᶜ.card : ℝ) := by exact_mod_cast hcomplN
  have hc := hexp {v}
  simp only [Finset.card_singleton, Nat.cast_one, min_eq_left hcompl, mul_one] at hc
  have hupper := P.card_interedges_le_mul ({v} : Finset V) ({v} : Finset V)ᶜ
  simp only [Finset.card_singleton, one_mul] at hupper
  have hle := (Finset.card_le_univ (({v} : Finset V)ᶜ))
  exact hc.trans (by exact_mod_cast hupper.trans hle)

noncomputable def routingG (r h : ℝ) : ℕ := ⌈8 * (r / h) * Real.logb 2 (2 * r)⌉₊

noncomputable def routingDepth (r : ℝ) : ℕ := ⌈Real.logb 2 r⌉₊

noncomputable def routingLength (r h : ℝ) : ℕ := 2 * routingG r h * (1 + routingDepth r)

lemma routingG_growth (r h : ℝ) (hr : 1 ≤ r) (hh : 0 < h) (hhr : h ≤ r) :
    r / 2 < (1 + h / (2 * r)) ^ routingG r h := by
  have hr0 : 0 < r := by linarith
  let x := h / (2 * r)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxle : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : 0 < 2 * r)).mpr
    linarith
  have hlog : h / (4 * r) ≤ Real.log (1 + h / (2 * r)) := by
    have heq : h / (4 * r) = x / 2 := by dsimp [x]; ring
    rw [heq]
    calc
      x / 2 ≤ 2 * x / (x + 2) := by
        apply (le_div_iff₀ (by linarith : 0 < x + 2)).mpr
        nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hxle)]
      _ ≤ Real.log (1 + x) := Real.le_log_one_add_of_nonneg hx0
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2le : Real.log 2 ≤ 1 := by
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at htwo ⊢
    exact htwo
  have hlogpos : 0 < Real.log (2 * r) := Real.log_pos (by linarith)
  have hbase : Real.log (2 * r) ≤ Real.logb 2 (2 * r) := by
    rw [Real.logb]
    apply (le_div_iff₀ hl2pos).mpr
    nlinarith
  have hg : 8 * (r / h) * Real.logb 2 (2 * r) ≤ (routingG r h : ℝ) :=
    Nat.le_ceil _
  have hlogpow : 2 * Real.log (2 * r) ≤
      Real.log ((1 + h / (2 * r)) ^ routingG r h) := by
    rw [Real.log_pow]
    calc
      2 * Real.log (2 * r) ≤ 2 * Real.logb 2 (2 * r) := by linarith
      _ = (8 * (r / h) * Real.logb 2 (2 * r)) * (h / (4 * r)) := by
        field_simp
        ; ring
      _ ≤ (routingG r h : ℝ) * (h / (4 * r)) :=
        mul_le_mul_of_nonneg_right hg (by positivity)
      _ ≤ (routingG r h : ℝ) * Real.log (1 + h / (2 * r)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
  have hsmall : Real.log (r / 2) < 2 * Real.log (2 * r) := by
    have := Real.log_le_log (by positivity : 0 < r / 2) (by linarith : r / 2 ≤ 2 * r)
    linarith
  apply (Real.log_lt_log_iff (by positivity : 0 < r / 2) (by positivity)).mp
  exact hsmall.trans_le hlogpow

def incidentEdges (F : Finset (Sym2 V)) (v : V) : Finset (Sym2 V) :=
  F.filter (fun e => v ∈ e)

lemma incidentEdges_union {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (F E : Finset (Sym2 V)) (v : V) :
    incidentEdges (F ∪ E) v = incidentEdges F v ∪ incidentEdges E v := by
  simp [incidentEdges, Finset.filter_union]

lemma incidentEdges_union_card_le (F E : Finset (Sym2 V)) (v : V) :
    (incidentEdges (F ∪ E) v).card ≤ (incidentEdges F v).card + (incidentEdges E v).card := by
  rw [incidentEdges_union]
  exact Finset.card_union_le _ _

lemma incidentEdges_sum_le (F : Finset (Sym2 V)) :
    ∑ v : V, (incidentEdges F v).card ≤ 2 * F.card := by
  have heq : ∑ v : V, (incidentEdges F v).card = ∑ e ∈ F, e.toFinset.card := by
    simp only [incidentEdges, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    simp [← Sym2.mem_toFinset]
  rw [heq]
  calc
    _ ≤ ∑ _e ∈ F, 2 := Finset.sum_le_sum (fun e _ => by
      rw [Sym2.card_toFinset]
      split <;> norm_num)
    _ = 2 * F.card := by simp [mul_comm]

lemma incidentEdges_path_start_le_one {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) :
    (incidentEdges p.edges.toFinset s).card ≤ 1 := by
  have hsub : incidentEdges p.edges.toFinset s ⊆ {s(s, p.snd)} := by
    intro e he
    obtain ⟨heP, hs⟩ := Finset.mem_filter.mp he
    obtain ⟨v, hev⟩ := Sym2.mem_iff_exists.mp hs
    subst e
    have hv := hp.eq_snd_of_mem_edges (List.mem_toFinset.mp heP)
    simp [hv]
  exact (Finset.card_le_card hsub).trans (by simp)

lemma incidentEdges_path_end_le_one (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) :
    (incidentEdges p.edges.toFinset t).card ≤ 1 := by
  simpa using incidentEdges_path_start_le_one G p.reverse hp.reverse

lemma incidentEdges_walk_eq_empty_of_not_mem {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) {s t v : V}
    (p : G.Walk s t) (hv : v ∉ p.support) : incidentEdges p.edges.toFinset v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heP, hve⟩ := Finset.mem_filter.mp he
  have hm := p.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, List.mem_toFinset.mp heP, hve⟩)
  exact hv hm

lemma incidentEdges_path_le_two (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) (v : V) :
    (incidentEdges p.edges.toFinset v).card ≤ 2 := by
  by_cases hv : v ∈ p.support
  · have htake := incidentEdges_path_end_le_one G (p.takeUntil v hv) (hp.takeUntil hv)
    have hdrop := incidentEdges_path_start_le_one G (p.dropUntil v hv) (hp.dropUntil hv)
    have heq : p.edges.toFinset = (p.takeUntil v hv).edges.toFinset ∪ (p.dropUntil v hv).edges.toFinset := by
      have he := congrArg (fun q : G.Walk s t => q.edges.toFinset) (p.take_spec hv)
      simpa only [SimpleGraph.Walk.edges_append, List.toFinset_append] using he.symm
    rw [heq]
    exact (incidentEdges_union_card_le _ _ v).trans (by omega)
  · rw [incidentEdges_walk_eq_empty_of_not_mem G p hv]
    simp

lemma deleted_boundary_card_le_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (B : Finset V) (F : Finset (Sym2 V)) :
    ((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card ≤
      ∑ v ∈ B, (incidentEdges F v).card := by
  let T := B.biUnion (fun v => ({v} : Finset V) ×ˢ incidentEdges F v)
  have hc : ((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun e : V × V => (e.1, s(e.1, e.2)))
    · intro e he
      obtain ⟨heP, heF⟩ := Finset.mem_filter.mp he
      apply Finset.mem_biUnion.mpr
      refine ⟨e.1, (P.mem_interedges_iff.mp heP).1, Finset.mem_product.mpr ⟨by simp, ?_⟩⟩
      exact Finset.mem_filter.mpr ⟨heF, by simp⟩
    · intro e he f hf heq
      have hsym := congrArg Prod.snd heq
      exact boundary_sym2_injective P B (Finset.mem_filter.mp he).1
        (Finset.mem_filter.mp hf).1 hsym
  have hT : T.card ≤ ∑ v ∈ B, (incidentEdges F v).card := by
    simpa [T] using Finset.card_biUnion_le (s := B)
      (t := fun v => ({v} : Finset V) ×ˢ incidentEdges F v)
  exact hc.trans hT

lemma walkBall_growth_of_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h) (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (W : Finset V) (s : V) (hs : s ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) (t : ℕ)
    (hsmall : ((walkBall (avoidGraph P F W) s t).card : ℝ) ≤ (Fintype.card V : ℝ) / 2) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (walkBall (avoidGraph P F W) s t).card ≤
      ((walkBall (avoidGraph P F W) s (t + 1)).card : ℝ) := by
  classical
  apply routing_union_growth_step_of_boundary P h hexp hr F _ _ (fun _ => W)
      (walkBall_mono _ s (Nat.le_succ t)) hsmall
  · calc
      _ ≤ ∑ v ∈ walkBall (avoidGraph P F W) s t, ((incidentEdges F v).card : ℝ) := by
        exact_mod_cast deleted_boundary_card_le_incidents P (walkBall (avoidGraph P F W) s t) F
      _ ≤ ∑ _v ∈ walkBall (avoidGraph P F W) s t, h / 4 := Finset.sum_le_sum (fun v _ => hF v)
      _ = _ := by simp; ring
  · exact fun _ _ => hW
  · intro v hv w _ hadj hdel hw
    have hnv := Finset.disjoint_left.mp (ball_avoids P F W s hs t) hv
    exact walkBall_step _ s v w t hv ⟨hadj, hdel, hnv, hw⟩

lemma walkBall_large_of_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s : V) (hs : s ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    (Fintype.card V : ℝ) / 2 <
      (walkBall (avoidGraph P F W) s (routingG (Fintype.card V) h)).card := by
  have hrR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < Fintype.card V := by linarith
  let g := routingG (Fintype.card V) h
  let c : ℝ := 1 + h / (2 * (Fintype.card V : ℝ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  by_contra hnot
  have hend := le_of_not_gt hnot
  have hpow : ∀ j ≤ g, c ^ j ≤ (walkBall (avoidGraph P F W) s j).card := by
    intro j
    induction j with
    | zero =>
      intro _
      have H := Finset.card_pos.mpr ⟨s, root_mem_walkBall (avoidGraph P F W) s 0⟩
      have H' : 1 ≤ (walkBall (avoidGraph P F W) s 0).card := H
      simpa using (Nat.cast_le (α := ℝ)).mpr H'
    | succ j ih =>
      intro hj
      have hmono : ((walkBall (avoidGraph P F W) s j).card : ℝ) ≤
          (walkBall (avoidGraph P F W) s g).card := by
        exact_mod_cast Finset.card_le_card (walkBall_mono (avoidGraph P F W) s (by omega : j ≤ g))
      have hsmall := hmono.trans hend
      calc
        c ^ (j + 1) = c * c ^ j := by rw [pow_succ]; ring
        _ ≤ c * (walkBall (avoidGraph P F W) s j).card := mul_le_mul_of_nonneg_left (ih (by omega)) hc
        _ ≤ (walkBall (avoidGraph P F W) s (j + 1)).card :=
          walkBall_growth_of_incidents P h hexp hr0 F W s hs hF hW j hsmall
  have hg := routingG_growth (Fintype.card V) h (by linarith) hh (hexp.le_order P h hr)
  exact (not_lt_of_ge ((hpow g le_rfl).trans hend)) hg

lemma exists_short_avoiding_path (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s t : V) (hs : s ∉ W) (ht : t ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    ∃ q : (avoidGraph P F W).Walk s t, q.IsPath ∧
      q.length ≤ 2 * routingG (Fintype.card V) h := by
  classical
  let g := routingG (Fintype.card V) h
  let B₁ := walkBall (avoidGraph P F W) s g
  let B₂ := walkBall (avoidGraph P F W) t g
  have h₁ := walkBall_large_of_incidents P h hh hexp hr F W s hs hF hW
  have h₂ := walkBall_large_of_incidents P h hh hexp hr F W t ht hF hW
  have hmeet : (B₁ ∩ B₂).Nonempty := by
    apply Finset.card_pos.mp
    have hc := Finset.card_union_add_card_inter B₁ B₂
    have hu := Finset.card_le_univ (B₁ ∪ B₂)
    have hsum : (Fintype.card V : ℝ) < (B₁.card : ℝ) + (B₂.card : ℝ) := by
      dsimp [B₁, B₂, g]; linarith
    have hsumN : Fintype.card V < B₁.card + B₂.card := by exact_mod_cast hsum
    omega
  obtain ⟨v, hv⟩ := hmeet
  obtain ⟨p₁, hp₁⟩ := (mem_walkBall _ s v g).mp (Finset.mem_inter.mp hv).1
  obtain ⟨p₂, hp₂⟩ := (mem_walkBall _ t v g).mp (Finset.mem_inter.mp hv).2
  let w := p₁.append p₂.reverse
  refine ⟨w.bypass, w.bypass_isPath, w.length_bypass_le_length.trans ?_⟩
  dsimp [w]
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

lemma two_routingG_le_length (r h : ℝ) : 2 * routingG r h ≤ routingLength r h := by
  dsimp [routingLength]
  exact Nat.le_mul_of_pos_right _ (by omega)

lemma routingLength_bounds (r h : ℝ) (hr : 1 ≤ r) (hh : 0 < h) :
    1 ≤ routingLength r h ∧ r ≤ (routingLength r h : ℝ) * h := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 1 ≤ Real.logb 2 (2 * r) := by
    rw [Real.logb]
    apply (le_div_iff₀ hl2).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 * r)
  have hg : 8 * (r / h) * Real.logb 2 (2 * r) ≤ (routingG r h : ℝ) := Nat.le_ceil _
  have hgh : 8 * r ≤ (routingG r h : ℝ) * h := by
    calc
      8 * r = (8 * (r / h)) * h := by field_simp
      _ ≤ (8 * (r / h) * Real.logb 2 (2 * r)) * h := by
        apply mul_le_mul_of_nonneg_right _ hh.le
        simpa using mul_le_mul_of_nonneg_left hlog (show 0 ≤ 8 * (r / h) by positivity)
      _ ≤ (routingG r h : ℝ) * h := mul_le_mul_of_nonneg_right hg hh.le
  have hgpos : 0 < routingG r h := by
    have hgR : (0 : ℝ) < routingG r h := by nlinarith
    exact_mod_cast hgR
  have hgle : routingG r h ≤ routingLength r h := (by omega : routingG r h ≤ 2 * routingG r h).trans (two_routingG_le_length r h)
  refine ⟨by omega, ?_⟩
  have hgleR : (routingG r h : ℝ) ≤ routingLength r h := by exact_mod_cast hgle
  nlinarith

lemma routing_budget (L k b z h r : ℝ) (hL : 1 ≤ L) (hk : 1 ≤ k)
    (hb : 1 ≤ b) (hz : 0 ≤ z) (hh : 0 < h) (_hr : 0 ≤ r)
    (hreach : r ≤ L * h) (hbudget : 64 * (L ^ 2 * (k + b) + z) ≤ h) :
    h / 8 + 2 + k ≤ h / 4 ∧ z + b * L ≤ h / 8 ∧ 64 * L * k * r ≤ h ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hLs : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hLLs : L ≤ L ^ 2 := by nlinarith
  have hbig : 64 * (k + b) ≤ h := by
    calc
      _ ≤ 64 * (L ^ 2 * (k + b) + z) := by nlinarith [mul_le_mul_of_nonneg_right hLs (by linarith : 0 ≤ k + b)]
      _ ≤ _ := hbudget
  have hbL : 64 * (b * L + z) ≤ h := by
    calc
      _ ≤ 64 * (L ^ 2 * (k + b) + z) := by nlinarith [mul_le_mul_of_nonneg_left hLLs hb0, mul_nonneg (sq_nonneg L) hk0]
      _ ≤ _ := hbudget
  have hkL : 64 * L ^ 2 * k ≤ h := by nlinarith [mul_nonneg (sq_nonneg L) hb0]
  refine ⟨by linarith, by linarith, ?_⟩
  calc
    64 * L * k * r ≤ 64 * L * k * (L * h) := mul_le_mul_of_nonneg_left hreach (by positivity)
    _ = (64 * L ^ 2 * k) * h := by ring
    _ ≤ h * h := mul_le_mul_of_nonneg_right hkL hh.le
    _ = h ^ 2 := by ring

noncomputable def saturated (F : Finset (Sym2 V)) (h : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => h / 8 ≤ ((incidentEdges F v).card : ℝ))

lemma saturated_card_le (F : Finset (Sym2 V)) (h : ℝ) (hh : 0 < h)
    (hF : 128 * (F.card : ℝ) ≤ h ^ 2) : (saturated F h).card ≤ h / 8 := by
  classical
  have hs : h / 8 * (saturated F h).card ≤ ∑ v : V, ((incidentEdges F v).card : ℝ) := by
    calc
      _ = ∑ _v ∈ saturated F h, h / 8 := by simp [mul_comm]
      _ ≤ ∑ v ∈ saturated F h, ((incidentEdges F v).card : ℝ) := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  have hsum : (∑ v : V, ((incidentEdges F v).card : ℝ)) ≤ 2 * (F.card : ℝ) := by
    exact_mod_cast incidentEdges_sum_le F
  nlinarith

def pathInterior {P : SimpleGraph V} {s t : V} (q : P.Walk s t) : Finset V :=
  q.support.toFinset \ {s, t}

lemma pathInterior_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : SimpleGraph V} {s t : V} (q : P.Walk s t) :
    (pathInterior q).card ≤ q.length := by
  have hp := List.toFinset_card_le q.support
  rw [q.length_support] at hp
  have hstart : s ∈ q.support.toFinset ∩ ({s, t} : Finset V) := by simp
  have hint := Finset.card_pos.mpr ⟨s, hstart⟩
  have hd := Finset.card_sdiff_add_card_inter q.support.toFinset ({s, t} : Finset V)
  dsimp [pathInterior]
  omega

lemma avoidGraph_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V) :
    avoidGraph P F W ≤ P := fun _ _ h => h.1

lemma walk_avoids_support (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s t : V} (q : (avoidGraph P F W).Walk s t) (hs : s ∉ W) :
    Disjoint q.support.toFinset W := by
  apply Finset.disjoint_left.mpr
  intro v hv
  exact walk_avoids_end P F W (q.takeUntil v (List.mem_toFinset.mp hv)) hs

lemma walk_avoids_edges {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s t : V} (q : (avoidGraph P F W).Walk s t) :
    Disjoint q.edges.toFinset F := by
  apply Finset.disjoint_left.mpr
  intro e he
  induction e using Sym2.inductionOn with
  | hf v w => exact (q.adj_of_mem_edges (List.mem_toFinset.mp he)).2.1

lemma exists_short_path_with_avoidance (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s t : V) (hs : s ∉ W) (ht : t ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    ∃ q : P.Walk s t, q.IsPath ∧ q.length ≤ routingLength (Fintype.card V) h ∧
      Disjoint q.edges.toFinset F ∧ Disjoint q.support.toFinset W := by
  obtain ⟨q, hp, hl⟩ := exists_short_avoiding_path P h hh hexp hr F W s t hs ht hF hW
  refine ⟨q.mapLe (avoidGraph_le P F W), hp.mapLe _, ?_, ?_, ?_⟩
  · simpa using hl.trans (two_routingG_le_length (Fintype.card V) h)
  · simpa using walk_avoids_edges P F W q
  · simpa using walk_avoids_support P F W q hs

lemma route_degree_update {P : SimpleGraph V} {s t : V} (q : P.Walk s t)
    (hp : q.IsPath) (F : Finset (Sym2 V)) (h : ℝ) (load : V → ℕ)
    (hdegree : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 8 + 2 + load v)
    (havoid : Disjoint q.support.toFinset (saturated F h \ {s, t})) (v : V) :
    ((incidentEdges (F ∪ q.edges.toFinset) v).card : ℝ) ≤
      h / 8 + 2 + load v + (if v = s ∨ v = t then 1 else 0) := by
  classical
  have hadd : ((incidentEdges (F ∪ q.edges.toFinset) v).card : ℝ) ≤
      (incidentEdges F v).card + (incidentEdges q.edges.toFinset v).card := by
    exact_mod_cast incidentEdges_union_card_le F q.edges.toFinset v
  by_cases hv : v = s ∨ v = t
  · rw [ite_eq_left hv]
    have hqN : (incidentEdges q.edges.toFinset v).card ≤ 1 := by
      rcases hv with rfl | rfl
      · exact incidentEdges_path_start_le_one P q hp
      · exact incidentEdges_path_end_le_one P q hp
    have hq : ((incidentEdges q.edges.toFinset v).card : ℝ) ≤ 1 := by exact_mod_cast hqN
    linarith [hdegree v]
  · rw [ite_eq_right hv]
    by_cases hmem : v ∈ q.support
    · have hns : v ∉ saturated F h := by
        intro hsat
        apply Finset.disjoint_left.mp havoid (List.mem_toFinset.mpr hmem)
        exact Finset.mem_sdiff.mpr ⟨hsat, by simpa using hv⟩
      have hsmall : ((incidentEdges F v).card : ℝ) < h / 8 := by
        simpa [saturated] using hns
      have hq : ((incidentEdges q.edges.toFinset v).card : ℝ) ≤ 2 := by
        exact_mod_cast incidentEdges_path_le_two P q hp v
      have : (0 : ℝ) ≤ load v := by positivity
      linarith
    · rw [incidentEdges_walk_eq_empty_of_not_mem P q hmem] at hadd
      simp only [Finset.card_empty, Nat.cast_zero, add_zero] at hadd
      linarith [hdegree v]

section Families
variable {I T : Type} [Fintype I] [DecidableEq I] [DecidableEq T]
variable {P : SimpleGraph V} {x y : I → V}

def endpointLoad (A : Finset I) (x y : I → V) (v : V) : ℕ :=
  (A.filter (fun i => x i = v ∨ y i = v)).card

lemma endpointLoad_mono {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {A B : Finset I} (hAB : A ⊆ B) (x y : I → V) (v : V) :
    endpointLoad A x y v ≤ endpointLoad B x y v :=
  Finset.card_le_card (Finset.filter_subset_filter _ hAB)

lemma endpointLoad_insert {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] (A : Finset I) (i : I) (hi : i ∉ A) (x y : I → V) (v : V) :
    endpointLoad (insert i A) x y v = endpointLoad A x y v +
      (if v = x i ∨ v = y i then 1 else 0) := by
  classical
  by_cases hv : v = x i ∨ v = y i
  · have hv' : x i = v ∨ y i = v := by simpa [eq_comm] using hv
    simp [endpointLoad, Finset.filter_insert, hv, hv', hi]
  · have hv' : ¬ (x i = v ∨ y i = v) := by simpa [eq_comm] using hv
    simp [endpointLoad, Finset.filter_insert, hv, hv']

lemma endpointLoad_sum {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] (A : Finset I) (x y : I → V) (hxy : ∀ i ∈ A, x i ≠ y i) :
    ∑ v : V, endpointLoad A x y v = 2 * A.card := by
  classical
  simp only [endpointLoad, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have heq : ∀ i ∈ A, (∑ v : V, if x i = v ∨ y i = v then 1 else 0) = 2 := by
    intro i hi
    have hf : (Finset.univ.filter fun v => x i = v ∨ y i = v) = ({x i, y i} : Finset V) := by
      ext v
      simp [eq_comm]
    have hc : ({x i, y i} : Finset V).card = 2 := by simp [hxy i hi]
    rw [← hc, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    _ = ∑ _i ∈ A, 2 := Finset.sum_congr rfl heq
    _ = _ := by simp [mul_comm]

noncomputable def usedEdges (A : Finset I) (q : ∀ i, P.Walk (x i) (y i)) : Finset (Sym2 V) :=
  A.biUnion (fun i => (q i).edges.toFinset)

lemma usedEdges_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (q : ∀ i, P.Walk (x i) (y i)) (L : ℕ)
    (hq : ∀ i ∈ A, (q i).length ≤ L) : (usedEdges A q).card ≤ L * A.card := by
  calc
    _ ≤ ∑ i ∈ A, (q i).edges.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A, L := Finset.sum_le_sum (fun i hi => by
      have hc := List.toFinset_card_le (q i).edges
      simpa using hc.trans (by simpa using hq i hi))
    _ = _ := by simp [mul_comm]

lemma usedEdges_update_insert {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (i : I) (hi : i ∉ A)
    (q : ∀ j, P.Walk (x j) (y j)) (p : P.Walk (x i) (y i)) :
    usedEdges (insert i A) (Function.update q i p) = usedEdges A q ∪ p.edges.toFinset := by
  classical
  rw [usedEdges, Finset.biUnion_insert]
  simp only [Function.update_self]
  rw [Finset.union_comm]
  congr 1
  apply Finset.biUnion_congr rfl
  intro j hj
  have hji : j ≠ i := by intro h; exact hi (h ▸ hj)
  rw [Function.update_of_ne hji]

noncomputable def teamInterior (A : Finset I) (q : ∀ j, P.Walk (x j) (y j))
    (team : I → T) (i : I) : Finset V :=
  (A.filter (fun j => team j = team i)).biUnion (fun j => pathInterior (q j))

lemma teamInterior_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} {T : Type} [_contextInstance5 : Fintype I] [_contextInstance6 : DecidableEq I] [_contextInstance7 : DecidableEq T] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (q : ∀ j, P.Walk (x j) (y j))
    (team : I → T) (i : I) (L : ℕ) (b : ℝ)
    (hq : ∀ j ∈ A, (q j).length ≤ L)
    (hb : ((Finset.univ.filter (fun j => team j = team i)).card : ℝ) ≤ b) :
    ((teamInterior A q team i).card : ℝ) ≤ b * L := by
  have hc : (teamInterior A q team i).card ≤ L * (A.filter (fun j => team j = team i)).card := by
    calc
      _ ≤ ∑ j ∈ A.filter (fun j => team j = team i), (pathInterior (q j)).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ A.filter (fun j => team j = team i), L := Finset.sum_le_sum (fun j hj =>
        (pathInterior_card_le (q j)).trans (hq j (Finset.mem_filter.mp hj).1))
      _ = _ := by simp [mul_comm]
  have hcard : ((A.filter (fun j => team j = team i)).card : ℝ) ≤ b := by
    apply le_trans _ hb
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ A))
  have hcR : ((teamInterior A q team i).card : ℝ) ≤ (L : ℝ) * (A.filter (fun j => team j = team i)).card := by exact_mod_cast hc
  calc
    _ ≤ (L : ℝ) * b := hcR.trans (mul_le_mul_of_nonneg_left hcard (by positivity))
    _ = _ := mul_comm _ _

structure PartialRoutes (P : SimpleGraph V) (x y : I → V) (team : I → T)
    (Z : I → Finset V) (L : ℕ) (h : ℝ) (A : Finset I)
    (q : ∀ i, P.Walk (x i) (y i)) : Prop where
  simple : ∀ i ∈ A, (q i).IsPath
  short : ∀ i ∈ A, (q i).length ≤ L
  avoids : ∀ i ∈ A, Disjoint (pathInterior (q i)) (Z i)
  edge_disjoint : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (q i).edges.toFinset (q j).edges.toFinset
  team_disjoint : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))
  degree : ∀ v, ((incidentEdges (usedEdges A q) v).card : ℝ) ≤ h / 8 + 2 + endpointLoad A x y v

theorem routing (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (x y : I → V) (hxy : ∀ i, x i ≠ y i) (team : I → T) (Z : I → Finset V)
    (k b z : ℝ) (hk : 1 ≤ k) (hb : 1 ≤ b) (hz : 0 ≤ z)
    (hload : ∀ v, (endpointLoad Finset.univ x y v : ℝ) ≤ k)
    (hteam : ∀ i, ((Finset.univ.filter (fun j => team j = team i)).card : ℝ) ≤ b)
    (hZ : ∀ i, ((Z i).card : ℝ) ≤ z)
    (hbudget : 64 * ((routingLength (Fintype.card V) h : ℝ) ^ 2 * (k + b) + z) ≤ h) :
    ∃ q : ∀ i, P.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength (Fintype.card V) h ∧
        Disjoint (pathInterior (q i)) (Z i)) ∧
      (∀ i j, i ≠ j → Disjoint (q i).edges.toFinset (q j).edges.toFinset) ∧
      (∀ i j, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
  classical
  let L := routingLength (Fintype.card V) h
  have hrR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hr
  obtain ⟨hL, hreach⟩ := routingLength_bounds (Fintype.card V) h (by linarith) hh
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨hdegBudget, hforbidBudget, hnumBudget⟩ := routing_budget L k b z h (Fintype.card V)
    hLR hk hb hz hh (by positivity) hreach hbudget
  have hloadA : ∀ (A : Finset I) v, (endpointLoad A x y v : ℝ) ≤ k := by
    intro A v
    have hm : (endpointLoad A x y v : ℝ) ≤ endpointLoad Finset.univ x y v := by
      exact_mod_cast endpointLoad_mono (Finset.subset_univ A) x y v
    exact hm.trans (hload v)
  have htotal : 2 * (Fintype.card I : ℝ) ≤ k * Fintype.card V := by
    have heq := endpointLoad_sum Finset.univ x y (fun i _ => hxy i)
    have heqR : (∑ v : V, (endpointLoad Finset.univ x y v : ℝ)) = 2 * Fintype.card I := by
      exact_mod_cast heq
    rw [← heqR]
    calc
      _ ≤ ∑ _v : V, k := Finset.sum_le_sum (fun v _ => hload v)
      _ = _ := by simp [mul_comm]
  have hdefault : ∀ i, ∃ p : P.Walk (x i) (y i), p.IsPath := by
    intro i
    obtain ⟨p, hp, _⟩ := exists_short_path_with_avoidance P h hh hexp hr ∅ ∅ (x i) (y i)
      (by simp) (by simp) (by intro v; simp [incidentEdges]; positivity) (by simp; positivity)
    exact ⟨p, hp⟩
  choose defaultPath hdefaultPath using hdefault
  have hpartial : ∀ A : Finset I, ∃ q : ∀ i, P.Walk (x i) (y i), PartialRoutes P x y team Z L h A q := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      refine ⟨defaultPath, ?_⟩
      constructor
      · simp
      · simp
      · simp
      · simp
      · simp
      · intro v
        simp only [usedEdges, Finset.biUnion_empty, incidentEdges, Finset.filter_empty,
          Finset.card_empty, Nat.cast_zero, endpointLoad, add_zero]
        linarith
    | @insert i A hi ih =>
      obtain ⟨q, hq⟩ := ih
      let F := usedEdges A q
      let S := saturated F h
      let B := teamInterior A q team i
      let W := (S ∪ Z i ∪ B) \ {x i, y i}
      have hFcard : 128 * (F.card : ℝ) ≤ h ^ 2 := by
        have hc : (F.card : ℝ) ≤ (L : ℝ) * A.card := by
          exact_mod_cast usedEdges_card_le A q L hq.short
        have ha : (A.card : ℝ) ≤ Fintype.card I := by exact_mod_cast Finset.card_le_univ A
        have hsize : 2 * (A.card : ℝ) ≤ k * Fintype.card V := by linarith
        have hmult := mul_le_mul_of_nonneg_left hsize (show 0 ≤ (L : ℝ) by positivity)
        nlinarith [hnumBudget]
      have hS : (S.card : ℝ) ≤ h / 8 := saturated_card_le F h hh hFcard
      have hB : (B.card : ℝ) ≤ b * L := teamInterior_card_le A q team i L b hq.short (hteam i)
      have hW : (W.card : ℝ) ≤ h / 4 := by
        have hc : W.card ≤ S.card + (Z i).card + B.card :=
          (Finset.card_le_card Finset.sdiff_subset).trans ((Finset.card_union_le _ _).trans
            (Nat.add_le_add_right (Finset.card_union_le _ _) _))
        have hcR : (W.card : ℝ) ≤ (S.card : ℝ) + (Z i).card + B.card := by exact_mod_cast hc
        linarith [hZ i]
      have hFdegree : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4 := by
        intro v
        have hd := hq.degree v
        have hl := hloadA A v
        dsimp [F]
        linarith
      obtain ⟨p, hp, hpL, hpF, hpW⟩ := exists_short_path_with_avoidance P h hh hexp hr F W (x i) (y i)
        (by simp [W]) (by simp [W]) hFdegree hW
      have hpZ : Disjoint (pathInterior p) (Z i) := by
        apply Finset.disjoint_left.mpr
        intro v hv hvZ
        obtain ⟨hvp, hvends⟩ := Finset.mem_sdiff.mp hv
        apply Finset.disjoint_left.mp hpW hvp
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hvZ), hvends⟩
      have hpS : Disjoint p.support.toFinset (saturated F h \ {x i, y i}) := by
        apply Finset.disjoint_left.mpr
        intro v hv hvS
        obtain ⟨hs, he⟩ := Finset.mem_sdiff.mp hvS
        apply Finset.disjoint_left.mp hpW hv
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hs), he⟩
      have hpEdge : ∀ j ∈ A, Disjoint p.edges.toFinset (q j).edges.toFinset := by
        intro j hj
        apply Finset.disjoint_left.mpr
        intro e hep heq
        exact Finset.disjoint_left.mp hpF hep (Finset.mem_biUnion.mpr ⟨j, hj, heq⟩)
      have hpTeam : ∀ j ∈ A, team i = team j → Disjoint (pathInterior p) (pathInterior (q j)) := by
        intro j hj htm
        apply Finset.disjoint_left.mpr
        intro v hvp hvq
        obtain ⟨hvp', hvends⟩ := Finset.mem_sdiff.mp hvp
        apply Finset.disjoint_left.mp hpW hvp'
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_union_right _ ?_, hvends⟩
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, htm.symm⟩, hvq⟩
      let q' := Function.update q i p
      have hsame : q' i = p := Function.update_self i p q
      have hother : ∀ j ∈ A, q' j = q j := by
        intro j hj
        apply Function.update_of_ne
        intro hji
        exact hi (hji ▸ hj)
      refine ⟨q', ?_⟩
      constructor
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hp
        · simpa only [hother j hj] using hq.simple j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hpL
        · simpa only [hother j hj] using hq.short j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hpZ
        · simpa only [hother j hj] using hq.avoids j hj
      · intro j hj k hk hjk
        rcases Finset.mem_insert.mp hj with rfl | hjA
        · have hkA : k ∈ A := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
          simpa only [hsame, hother k hkA] using hpEdge k hkA
        · rcases Finset.mem_insert.mp hk with rfl | hkA
          · simpa only [hsame, hother j hjA] using (hpEdge j hjA).symm
          · simpa only [hother j hjA, hother k hkA] using hq.edge_disjoint j hjA k hkA hjk
      · intro j hj k hk hjk htm
        rcases Finset.mem_insert.mp hj with rfl | hjA
        · have hkA : k ∈ A := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
          simpa only [hsame, hother k hkA] using hpTeam k hkA htm
        · rcases Finset.mem_insert.mp hk with rfl | hkA
          · simpa only [hsame, hother j hjA] using (hpTeam j hjA htm.symm).symm
          · simpa only [hother j hjA, hother k hkA] using hq.team_disjoint j hjA k hkA hjk htm
      · intro v
        have heq : usedEdges (insert i A) q' = F ∪ p.edges.toFinset := usedEdges_update_insert A i hi q p
        rw [heq]
        have hu := route_degree_update p hp F h (endpointLoad A x y) hq.degree hpS v
        have hloadEq : (endpointLoad (insert i A) x y v : ℝ) =
            endpointLoad A x y v + (if v = x i ∨ v = y i then (1 : ℝ) else 0) := by
          rw [endpointLoad_insert A i hi]
          split_ifs <;> simp
        rw [hloadEq]
        simpa only [add_assoc] using hu
  obtain ⟨q, hq⟩ := hpartial Finset.univ
  exact ⟨q, fun i => ⟨hq.simple i (by simp), hq.short i (by simp), hq.avoids i (by simp)⟩,
    fun i j hij => hq.edge_disjoint i (by simp) j (by simp) hij,
    fun i j hij htm => hq.team_disjoint i (by simp) j (by simp) hij htm⟩

end Families
end ErdosGallai

end
end
end

/-! ### Upstream module `Combinatorics/CycleDecomposition/ReservoirCycles.lean` -/

section
open _root_.Filter _root_.Asymptotics _root_.Real
noncomputable section
open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Finset
noncomputable section
namespace ErdosGallai
noncomputable section
lemma routing_length_upper (r h : ℝ) (hr : 2 ≤ r) (hh : 0 < h) (hhr : h ≤ r) :
    (routingLength r h : ℝ) ≤ 108*(r/h)*(logb 2 r)^2 := by
  have hr0 : 0 < r := by linarith
  have hl : 1 ≤ logb 2 r := by
    simpa using Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
      (by norm_num : (0:ℝ) < 2) hr
  have hR : 1 ≤ r/h := (le_div_iff₀ hh).mpr (by simpa using hhr)
  have hlog : logb 2 (2*r) = 1 + logb 2 r := by
    rw [Real.logb_mul (by norm_num) hr0.ne']
    norm_num
  have hg := Nat.ceil_lt_add_one (show 0 ≤ 8*(r/h)*logb 2 (2*r) by rw [hlog]; positivity)
  have hd := Nat.ceil_lt_add_one (show 0 ≤ logb 2 r by linarith)
  change (routingG r h : ℝ) < 8*(r/h)*logb 2 (2*r)+1 at hg
  change (routingDepth r : ℝ) < logb 2 r + 1 at hd
  rw [hlog] at hg
  have hprod : 1 ≤ (r/h)*logb 2 r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hl)]
  have hg' : (routingG r h : ℝ) ≤ 18*(r/h)*logb 2 r := by nlinarith
  have hd' : (1 + routingDepth r : ℝ) ≤ 3*logb 2 r := by linarith
  have hm := mul_le_mul hg' hd' (by positivity) (by positivity)
  dsimp [routingLength]
  push_cast
  nlinarith

lemma eventually_logb_le_power (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, logb 2 D ≤ D^ε := by
  have ho := (isLittleO_log_rpow_atTop hε).const_mul_left (1 / log 2)
  filter_upwards [ho.eventuallyLE, eventually_ge_atTop (1:ℝ)] with D hD h1
  simpa [Real.logb, div_eq_mul_inv, mul_comm, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg h1), abs_of_nonneg (Real.rpow_nonneg (by linarith) ε),
    abs_of_pos (show 0 < (log 2)⁻¹ by positivity),
    abs_of_pos (Real.log_pos (by norm_num : (1:ℝ) < 2))] using hD

lemma eventually_constant_le_power (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, C ≤ D^ε :=
  (tendsto_rpow_atTop hε).eventually (eventually_ge_atTop C)

lemma eventually_const_mul_power_le (C α β : ℝ) (hab : α < β) :
    ∀ᶠ D : ℝ in atTop, C*D^α ≤ D^β := by
  filter_upwards [eventually_constant_le_power C (β-α) (by linarith),
    eventually_gt_atTop (0:ℝ)] with D hc hD
  calc
    C*D^α ≤ D^(β-α)*D^α := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hD.le _)
    _ = D^β := by rw [← Real.rpow_add hD]; congr 1; ring

theorem eventually_routing_length (c β γ δ : ℝ) (hc : 0 < c) (hβ : 0 < β)
    (hδ : 0 < δ) :
    ∀ᶠ D : ℝ in atTop, ∀ r : ℝ, 2 ≤ r → r ≤ D^β → c*D^γ ≤ r →
      (routingLength r (c*D^γ) : ℝ) ≤ D^(β-γ+δ) := by
  filter_upwards [eventually_logb_le_power (δ/4) (by positivity),
    eventually_constant_le_power (108*β^2/c) (δ/2) (by positivity),
    eventually_gt_atTop (1:ℝ)] with D hlog hconst hD r hr hrD hhr
  have hD0 : 0 < D := by linarith
  have hpowγ : 0 < D^γ := Real.rpow_pos_of_pos hD0 _
  have hden : 0 < c*D^γ := mul_pos hc hpowγ
  have hlog0 : 0 ≤ logb 2 r := (Real.logb_pos (by norm_num) (by linarith)).le
  have hlogR : logb 2 r ≤ β*D^(δ/4) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
      (by linarith : 0 < r) hrD
    rw [Real.logb_rpow_eq_mul_logb_of_pos hD0] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlog hβ.le)
  have hratio : r/(c*D^γ) ≤ D^(β-γ)/c := by
    calc
      _ ≤ D^β/(c*D^γ) := div_le_div_of_nonneg_right hrD hden.le
      _ = _ := by rw [Real.rpow_sub hD0]; ring
  have hsq : (logb 2 r)^2 ≤ β^2*D^(δ/2) := by
    calc
      _ ≤ (β*D^(δ/4))^2 := pow_le_pow_left₀ hlog0 hlogR 2
      _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hD0.le]; congr 2; ring
  calc
    (routingLength r (c*D^γ) : ℝ) ≤ 108*(r/(c*D^γ))*(logb 2 r)^2 :=
      routing_length_upper r (c*D^γ) hr hden hhr
    _ ≤ 108*(D^(β-γ)/c)*(β^2*D^(δ/2)) := by gcongr
    _ = (108*β^2/c)*D^(β-γ+δ/2) := by rw [Real.rpow_add hD0]; ring
    _ ≤ D^(δ/2)*D^(β-γ+δ/2) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hD0.le _)
    _ = D^(β-γ+δ) := by rw [← Real.rpow_add hD0]; congr 1; ring

lemma eventually_reservoir_capacity (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∀ᶠ D : ℝ in atTop, ∀ r : ℝ, 0 ≤ r → r ≤ D^(51/50:ℝ) →
      (⌈8*r/(p*(c*D^(9/10:ℝ)))⌉₊ : ℝ) ≤ D^(13/100:ℝ) := by
  filter_upwards [eventually_const_mul_power_le (8/(p*c)+1) (3/25) (13/100) (by norm_num),
    eventually_gt_atTop (1:ℝ)] with D hbound hD r hr hrD
  have hD0 : 0 < D := by linarith
  have hden : 0 < p*(c*D^(9/10:ℝ)) := by positivity
  have hone : 1 ≤ D^(3/25:ℝ) := Real.one_le_rpow hD.le (by norm_num)
  have hx : 8*r/(p*(c*D^(9/10:ℝ))) ≤ (8/(p*c))*D^(3/25:ℝ) := by
    calc
      _ ≤ 8*D^(51/50:ℝ)/(p*(c*D^(9/10:ℝ))) := by gcongr
      _ = _ := by
        have heq : D^(3/25:ℝ) = D^(51/50:ℝ)/D^(9/10:ℝ) := by
          rw [← Real.rpow_sub hD0]; norm_num
        rw [heq]; ring
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 8*r/(p*(c*D^(9/10:ℝ))) by positivity)
  nlinarith only [hx, hceil, hone, hbound]

theorem residue_routing_margin (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, ∀ r rᵢ : ℝ,
      0 ≤ r → r ≤ D^(51/50:ℝ) → 2 ≤ rᵢ → rᵢ ≤ r → D^(37/50:ℝ) ≤ rᵢ →
      64*((routingLength rᵢ (D^(37/50:ℝ)) : ℝ)^2*
        ((⌈8*r/(p*(c*D^(9/10:ℝ)))⌉₊ : ℝ)+1)) ≤ D^(37/50:ℝ) := by
  have hev : ∀ᶠ D : ℝ in atTop, ∀ r rᵢ : ℝ,
      0 ≤ r → r ≤ D^(51/50:ℝ) → 2 ≤ rᵢ → rᵢ ≤ r → D^(37/50:ℝ) ≤ rᵢ →
      64*((routingLength rᵢ (D^(37/50:ℝ)) : ℝ)^2*
        ((⌈8*r/(p*(c*D^(9/10:ℝ)))⌉₊ : ℝ)+1)) ≤ D^(37/50:ℝ) := by
    filter_upwards [eventually_routing_length 1 (51/50) (37/50) (1/100)
      (by norm_num) (by norm_num) (by norm_num),
      eventually_reservoir_capacity c p hc hp,
      eventually_const_mul_power_le 128 (71/100) (37/50) (by norm_num),
      eventually_gt_atTop (1:ℝ)] with D hlen hcap hcost hD r rᵢ hr hrD hri2 hrir htau
    have hD0 : 0 < D := by linarith
    have hL := hlen rᵢ hri2 (hrir.trans hrD) (by simpa using htau)
    norm_num at hL
    have hk := hcap r hr hrD
    have hone : 1 ≤ D^(13/100:ℝ) := Real.one_le_rpow hD.le (by norm_num)
    have hprod : (routingLength rᵢ (D^(37/50:ℝ)) : ℝ)^2*
        ((⌈8*r/(p*(c*D^(9/10:ℝ)))⌉₊ : ℝ)+1) ≤ 2*D^(71/100:ℝ) := by
      calc
        _ ≤ (D^(29/100:ℝ))^2 * (2*D^(13/100:ℝ)) := by gcongr; linarith
        _ = _ := by
          rw [← Real.rpow_mul_natCast hD0.le]
          norm_num
          rw [mul_left_comm, ← Real.rpow_add hD0]
          norm_num
    nlinarith only [hprod, hcost]
  obtain ⟨A,hA⟩ := eventually_atTop.mp hev
  refine ⟨max A 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro D hD
  exact hA D ((le_max_left _ _).trans hD)

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

def CutExpansionOn (P : SimpleGraph V) [DecidableRel P.Adj] (W : Finset V) (h : ℝ) : Prop :=
  ∀ A : Finset V, A ⊆ W → h * min (A.card : ℝ) ((W \ A).card : ℝ) ≤
    ((P.interedges A (W \ A)).card : ℝ)

lemma subtype_image_compl {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (W : Finset V) (U : Finset (W : Set V)) :
    Uᶜ.image Subtype.val = W \ U.image Subtype.val := by
  ext v
  simp only [Finset.mem_image, Finset.mem_compl, Finset.mem_sdiff]
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.property,?_⟩
    rintro ⟨y,hy,he⟩
    exact hx (Subtype.ext he ▸ hy)
  · rintro ⟨hv,hvU⟩
    refine ⟨⟨v,hv⟩,?_,rfl⟩
    intro hx
    exact hvU ⟨⟨v,hv⟩,hx,rfl⟩

lemma induced_interedges_card (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) (U : Finset (W : Set V)) :
    (((P.induce (W : Set V)).interedges U Uᶜ).card : ℝ) =
      ((P.interedges (U.image Subtype.val) (W \ U.image Subtype.val)).card : ℝ) := by
  classical
  let f : ↥(W : Set V) × ↥(W : Set V) → V × V := fun e => (e.1.val,e.2.val)
  have hf : Function.Injective f := by
    intro a b h
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have heq : ((P.induce (W : Set V)).interedges U Uᶜ).image f =
      P.interedges (U.image Subtype.val) (W \ U.image Subtype.val) := by
    rw [← subtype_image_compl W U]
    ext e
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_image]
    constructor
    · rintro ⟨a,⟨ha,hb,hab⟩,rfl⟩
      exact ⟨⟨a.1,ha,rfl⟩,⟨a.2,hb,rfl⟩,hab⟩
    · rintro ⟨⟨x,hx,hxe⟩,⟨y,hy,hye⟩,he⟩
      refine ⟨(x,y),⟨hx,hy,?_⟩,Prod.ext hxe hye⟩
      change P.Adj x.val y.val
      simpa only [hxe,hye] using he
  rw [← heq, Finset.card_image_of_injective _ hf]

lemma cutExpansion_induce (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) (h : ℝ) (hexp : CutExpansionOn P W h) :
    CutExpansion (P.induce (W : Set V)) h := by
  classical
  intro U
  have hsub : U.image Subtype.val ⊆ W := by
    rintro v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    exact a.property
  have h := hexp (U.image Subtype.val) hsub
  have he : W \ U.image Subtype.val = Uᶜ.image Subtype.val :=
    (subtype_image_compl W U).symm
  rw [he] at h
  simp only [Finset.card_image_of_injective _ Subtype.val_injective] at h
  rw [induced_interedges_card,he]
  exact h

theorem routing_allow_equal {I : Type} [Fintype I]
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (x y : I → V) (k : ℝ) (hk : 1 ≤ k)
    (hload : ∀ v, (endpointLoad Finset.univ x y v : ℝ) ≤ k)
    (hbudget : 64 * ((routingLength (Fintype.card V) h : ℝ)^2 * (k+1)) ≤ h) :
    ∃ q : ∀ i, P.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength (Fintype.card V) h) ∧
      (∀ i j, i ≠ j → Disjoint (q i).edges.toFinset (q j).edges.toFinset) := by
  classical
  let J := {i : I // x i ≠ y i}
  have hjload (v : V) :
      (endpointLoad Finset.univ (fun i : J => x i.val) (fun i : J => y i.val) v : ℝ) ≤ k := by
    apply le_trans _ (hload v)
    exact_mod_cast (show endpointLoad Finset.univ (fun i : J => x i.val)
        (fun i : J => y i.val) v ≤ endpointLoad Finset.univ x y v from by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro a ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩
      · intro a _ b _ hab
        exact Subtype.ext hab)
  obtain ⟨q,hq,hd,_⟩ := routing P h hh hexp hr
    (fun i : J => x i.val) (fun i : J => y i.val) (fun i => i.property)
    (fun i : J => i) (fun _ => ∅) k 1 0 hk (by norm_num) (by norm_num) hjload
    (by
      intro i
      have he : (univ.filter (fun j : J => j = i)) = {i} := by ext j; simp
      rw [he]; simp) (by intro i; simp) (by simpa only [add_zero] using hbudget)
  let Q : ∀ i, P.Walk (x i) (y i) := fun i =>
    if hi : x i = y i then (SimpleGraph.Walk.nil : P.Walk (x i) (x i)).copy rfl hi
    else q ⟨i,hi⟩
  refine ⟨Q,?_,?_⟩
  · intro i
    by_cases hi : x i = y i
    · simp [Q,hi]
    · simpa only [Q,dite_eq_right hi] using ⟨(hq ⟨i,hi⟩).1,(hq ⟨i,hi⟩).2.1⟩
  · intro i j hij
    by_cases hi : x i = y i
    · simp [Q,hi]
    by_cases hj : x j = y j
    · simp [Q,hj]
    simp only [Q,dite_eq_right hi,dite_eq_right hj]
    exact hd ⟨i,hi⟩ ⟨j,hj⟩ (fun he => hij (congrArg Subtype.val he))

theorem routing_in_reservoir {I : Type} [Fintype I]
    (G P : SimpleGraph V) [DecidableRel P.Adj] (hPG : P ≤ G)
    (W : Finset V) (h : ℝ) (hh : 0 < h)
    (hexp : CutExpansionOn P W h) (hr : 2 ≤ W.card)
    (x y : I → V) (hx : ∀ i, x i ∈ W) (hy : ∀ i, y i ∈ W)
    (k : ℝ) (hk : 1 ≤ k)
    (hload : ∀ v, (endpointLoad Finset.univ x y v : ℝ) ≤ k)
    (hbudget : 64 * ((routingLength W.card h : ℝ)^2 * (k+1)) ≤ h) :
    ∃ q : ∀ i, G.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card h ∧
        ∀ v ∈ (q i).support, v ∈ W) ∧
      Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) := by
  classical
  let X : I → (W : Set V) := fun i => ⟨x i,hx i⟩
  let Y : I → (W : Set V) := fun i => ⟨y i,hy i⟩
  have hl (v : (W : Set V)) : (endpointLoad univ X Y v : ℝ) ≤ k := by
    simpa only [endpointLoad,X,Y,Subtype.ext_iff] using hload v.val
  obtain ⟨q,hq,hd⟩ := routing_allow_equal (P.induce (W : Set V)) h hh
    (cutExpansion_induce P W h hexp) (by simpa using hr) X Y k hk hl
    (by simpa using hbudget)
  let f : (P.induce (W : Set V)) →g G :=
    { toFun := Subtype.val, map_rel' := fun ha => hPG ha }
  have hf : Function.Injective f := Subtype.val_injective
  have hcard : Fintype.card ↥(W : Set V) = W.card := Fintype.card_coe W
  let Q : ∀ i, G.Walk (x i) (y i) := fun i => (q i).map f
  refine ⟨Q,?_,?_⟩
  · intro i
    refine ⟨(hq i).1.map hf,?_,?_⟩
    · simpa only [Q,SimpleGraph.Walk.length_map, hcard] using (hq i).2
    · intro v hv
      have hv' : v ∈ (q i).support.map f := by simpa only [Q,SimpleGraph.Walk.support_map] using hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv'
      exact a.property
  · intro i j hij
    change Disjoint ((q i).map f).edgeSet ((q j).map f).edgeSet
    rw [SimpleGraph.Walk.edgeSet_map,SimpleGraph.Walk.edgeSet_map]
    rw [Set.disjoint_image_iff (Sym2.map.injective hf)]
    apply Set.disjoint_left.mpr
    intro e he he'
    exact Finset.disjoint_left.mp (hd i j hij)
      (by simpa using he) (by simpa using he')

theorem uniform_reservoir_routing (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G P : SimpleGraph V) [DecidableRel P.Adj], P ≤ G →
      ∀ W : Finset V, CutExpansionOn P W (D^(37/50:ℝ)) → 2 ≤ W.card →
      (Fintype.card V : ℝ) ≤ D^(51/50:ℝ) →
      ∀ (I : Type) [Fintype I] (x y : I → V),
      (∀ i, x i ∈ W) → (∀ i, y i ∈ W) →
      (∀ v, endpointLoad univ x y v ≤
        ⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊) →
      ∃ q : ∀ i, G.Walk (x i) (y i),
        (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card (D^(37/50:ℝ)) ∧
          ∀ v ∈ (q i).support, v ∈ W) ∧
        Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) := by
  obtain ⟨D₀,hD₀,hmargin⟩ := residue_routing_margin c p hc hp
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V _ _ G P _ hPG W hexp hW hr I _ x y hx hy hl
  have hDpos : 0 < D := lt_trans (by norm_num) (hD₀.trans_le hD)
  have horder : (D^(37/50:ℝ)) ≤ (W.card : ℝ) := by
    simpa using (cutExpansion_induce P W _ hexp).le_order (P.induce (W:Set V)) _
      (by simpa using hW)
  have hWupper : (W.card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast W.card_le_univ
  have hrpos : 0 < (Fintype.card V : ℝ) := by
    have hWreal : (2:ℝ) ≤ W.card := by exact_mod_cast hW
    linarith
  have hk : 1 ≤ (⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊ : ℝ) := by
    have hceil : 0 < ⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊ :=
      Nat.ceil_pos.mpr (by positivity)
    exact_mod_cast hceil
  apply routing_in_reservoir G P hPG W (D^(37/50:ℝ)) (by positivity) hexp hW
    x y hx hy _ hk (by intro v; exact_mod_cast hl v)
  exact hmargin D hD _ _ hrpos.le hr (by exact_mod_cast hW) hWupper horder

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable

theorem occurrence_slots {A : Type cycleUniverse1} {V : Type cycleUniverse2} [Fintype A] (f : A → V) (k : ℕ)
    (h : ∀ v, Fintype.card {a // f a = v} ≤ k) :
    ∃ slot : A → Fin k, Function.Injective (fun a => (f a, slot a)) := by
  classical
  have he : ∀ v, Nonempty ({a // f a = v} ↪ Fin k) := by
    intro v
    exact Function.Embedding.nonempty_of_card_le (by simpa using h v)
  let e := fun v => Classical.choice (he v)
  refine ⟨fun a => e (f a) ⟨a,rfl⟩, ?_⟩
  intro a b hab
  have hf : f a = f b := congrArg Prod.fst hab
  have hs : e (f a) ⟨a,rfl⟩ = e (f b) ⟨b,rfl⟩ := congrArg Prod.snd hab
  have hσ : (⟨f a, e (f a) ⟨a,rfl⟩⟩ : Σ _ : V, Fin k) =
      ⟨f b, e (f b) ⟨b,rfl⟩⟩ := Sigma.ext hf (heq_of_eq hs)
  let E : (Σ v, {a // f a = v}) ↪ (Σ _ : V, Fin k) :=
    Function.Embedding.sigmaMap (Function.Embedding.refl V) e
  have heq : (⟨f a, ⟨a,rfl⟩⟩ : Σ v, {a // f a = v}) = ⟨f b, ⟨b,rfl⟩⟩ :=
    E.injective hσ
  exact congrArg (fun z : Σ v, {a // f a = v} => z.2.val) heq

def endpointOccurrence {I : Type cycleUniverse3} {V : Type cycleUniverse4} (x y : I → V) (a : I × Fin 2) : V :=
  if a.2 = 0 then x a.1 else y a.1

theorem endpoint_occurrence_slots {I : Type cycleUniverse5} {V : Type cycleUniverse6} [Fintype I]
    (x y : I → V) (hne : ∀ i, x i ≠ y i)
    (hload : ∀ v, (univ.filter (fun i => x i = v ∨ y i = v)).card ≤ 2) :
    ∃ slot : I × Fin 2 → Fin 2,
      Function.Injective (fun a => (endpointOccurrence x y a, slot a)) := by
  classical
  apply occurrence_slots
  intro v
  let f : {a : I × Fin 2 // endpointOccurrence x y a = v} →
      {i : I // x i = v ∨ y i = v} := fun a =>
    ⟨a.val.1, by
      by_cases h0 : a.val.2 = 0
      · exact Or.inl (by simpa [endpointOccurrence,h0] using a.property)
      · exact Or.inr (by simpa [endpointOccurrence,h0] using a.property)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hi : a.val.1 = b.val.1 := congrArg Subtype.val hab
    apply Prod.ext hi
    by_contra ht
    have hcases : (a.val.2 = 0 ∧ b.val.2 ≠ 0) ∨ (a.val.2 ≠ 0 ∧ b.val.2 = 0) := by
      have ha := (a.val.2).isLt
      have hb := (b.val.2).isLt
      have hne : (a.val.2).val ≠ (b.val.2).val := fun h => ht (Fin.ext h)
      simp only [Fin.ext_iff, Fin.val_zero]
      omega
    rcases hcases with h | h
    · have ha : x a.val.1 = v := by simpa [endpointOccurrence,h.1] using a.property
      have hb : y b.val.1 = v := by simpa [endpointOccurrence,h.2] using b.property
      exact hne _ (ha.trans (hi ▸ hb).symm)
    · have ha : y a.val.1 = v := by simpa [endpointOccurrence,h.1] using a.property
      have hb : x b.val.1 = v := by simpa [endpointOccurrence,h.2] using b.property
      exact hne _ ((hi ▸ hb).trans ha.symm)
  exact (Fintype.card_le_of_injective f hf).trans (by simpa only [Fintype.card_subtype] using hload v)

theorem reserved_edges_injective {A : Type cycleUniverse7} {V : Type cycleUniverse8} (S W : Set V)
    (f : A → V) (slot : A → Fin 2) (r : V × Fin 2 → V)
    (hslots : Function.Injective (fun a => (f a,slot a)))
    (hout : ∀ a, f a ∈ S) (hin : ∀ v ∈ S, ∀ t, r (v,t) ∈ W)
    (hdisj : Disjoint S W) (hr : ∀ v ∈ S, r (v,0) ≠ r (v,1)) :
    Function.Injective (fun a => s(f a,r (f a,slot a))) := by
  intro a b hab
  rcases Sym2.eq_iff.mp hab with he | he
  · have hf : f a = f b := he.1
    have hh : r (f a,slot a) = r (f b,slot b) := he.2
    apply hslots
    apply Prod.ext hf
    have hrinj : Function.Injective (fun t : Fin 2 => r (f a,t)) := by
      intro i j hij
      have h0 := hr (f a) (hout a)
      fin_cases i <;> fin_cases j
      · rfl
      · exact (h0 hij).elim
      · exact (h0 hij.symm).elim
      · rfl
    exact hrinj (by simpa only [hf] using hh)
  · have hf : f a = r (f b,slot b) := he.1
    exact False.elim (Set.disjoint_left.mp hdisj (hout a)
      (hf.symm ▸ hin (f b) (hout b) (slot b)))

theorem assigned_representative_load {A : Type cycleUniverse9} {V : Type cycleUniverse10} [Fintype A] [DecidableEq V]
    (S : Finset V) (f : A → V) (slot : A → Fin 2) (r : V × Fin 2 → V)
    (hslots : Function.Injective (fun a => (f a,slot a)))
    (hout : ∀ a, f a ∈ S) (k : ℕ)
    (hcap : ∀ v, ((S ×ˢ univ).filter (fun a => r a = v)).card ≤ k) :
    ∀ v, (univ.filter (fun a => r (f a,slot a) = v)).card ≤ k := by
  classical
  intro v
  apply le_trans (Finset.card_le_card_of_injOn (fun a => (f a,slot a)) ?_ ?_) (hcap v)
  · intro a ha
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hout a,mem_univ _⟩, (mem_filter.mp ha).2⟩
  · intro a _ b _ hab
    exact hslots hab

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable

theorem choose_reservoir_endpoints {V I : Type} [Fintype V] [Fintype I]
    [DecidableEq V] (P : SimpleGraph V) (W : Finset V)
    (x y : I → V) (hne : ∀ i, x i ≠ y i)
    (houtx : ∀ i, x i ∉ W) (houty : ∀ i, y i ∉ W)
    (hload : ∀ v, endpointLoad univ x y v ≤ 2)
    (r : V × Fin 2 → V)
    (hr : ∀ v, v ∉ W → ∀ t, r (v,t) ∈ W ∧ P.Adj v (r (v,t)))
    (hrne : ∀ v, v ∉ W → r (v,0) ≠ r (v,1))
    (k : ℕ) (hcap : ∀ v, ((Wᶜ ×ˢ univ).filter (fun z => r z = v)).card ≤ k) :
    ∃ a b : I → V,
      (∀ i, a i ∈ W ∧ P.Adj (x i) (a i)) ∧
      (∀ i, b i ∈ W ∧ P.Adj (y i) (b i)) ∧
      Function.Injective (fun z : I × Fin 2 =>
        if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)) ∧
      (∀ v, endpointLoad univ a b v ≤ k) ∧
      (∀ i, ∃ t, a i = r (x i,t)) ∧ (∀ i, ∃ t, b i = r (y i,t)) := by
  classical
  obtain ⟨slot,hslot⟩ := endpoint_occurrence_slots x y hne (fun v => by
    convert hload v using 1
    congr 1
    ext i
    simp only [ Finset.mem_filter, Finset.mem_univ, true_and])
  let occ := endpointOccurrence x y
  have ho : ∀ z : I × Fin 2, occ z ∉ W := by
    rintro ⟨i,t⟩
    by_cases h : t = 0
    · simpa [occ,endpointOccurrence,h] using houtx i
    · simpa [occ,endpointOccurrence,h] using houty i
  let a := fun i => r (x i,slot (i,0))
  let b := fun i => r (y i,slot (i,1))
  have hsp := reserved_edges_injective (Wᶜ : Finset V) W occ slot r hslot
    (fun z => Finset.mem_compl.mpr (ho z))
    (fun v hv t => (hr v (Finset.mem_compl.mp hv) t).1)
    (Set.disjoint_left.mpr (fun _ hv hw => (Finset.mem_compl.mp hv) hw))
    (fun v hv => hrne v (Finset.mem_compl.mp hv))
  have hcap' := assigned_representative_load Wᶜ occ slot r hslot
    (fun z => Finset.mem_compl.mpr (ho z)) k hcap
  refine ⟨a,b,(fun i => hr _ (houtx i) _),(fun i => hr _ (houty i) _),?_,?_,?_,?_⟩
  · have heq : (fun z : I × Fin 2 =>
        if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)) =
        (fun z => s(occ z,r (occ z,slot z))) := by
      funext z
      rcases z with ⟨i,t⟩
      fin_cases t <;> simp [occ,endpointOccurrence,a,b]
    rw [heq]
    exact hsp
  · intro v
    apply le_trans (Finset.card_le_card_of_injOn
      (fun i => (i,if a i = v then (0 : Fin 2) else 1)) ?_ ?_) (hcap' v)
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      by_cases hi0 : a i = v
      · simp [hi0,occ,endpointOccurrence,a]
      · have hi1 : b i = v := hi'.resolve_left hi0
        simpa [hi0,occ,endpointOccurrence,b] using hi1
    · intro i hi j hj he
      exact congrArg Prod.fst he
  · intro i; exact ⟨slot (i,0),rfl⟩
  · intro i; exact ⟨slot (i,1),rfl⟩

theorem uniform_assigned_reservoir_routing (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G P : SimpleGraph V) [DecidableRel P.Adj], P ≤ G →
      ∀ W : Finset V, CutExpansionOn P W (D^(37/50:ℝ)) → 2 ≤ W.card →
      (Fintype.card V : ℝ) ≤ D^(51/50:ℝ) →
      ∀ (I : Type) [Fintype I] (x y : I → V),
      (∀ i, x i ≠ y i) → (∀ i, x i ∉ W) → (∀ i, y i ∉ W) →
      (∀ v, endpointLoad univ x y v ≤ 2) →
      ∀ r : V × Fin 2 → V,
      (∀ v, v ∉ W → ∀ t, r (v,t) ∈ W ∧ P.Adj v (r (v,t))) →
      (∀ v, v ∉ W → r (v,0) ≠ r (v,1)) →
      (∀ v, ((Wᶜ ×ˢ univ).filter (fun z => r z = v)).card ≤
        ⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊) →
      ∃ (a b : I → V) (q : ∀ i, G.Walk (a i) (b i)),
        (∀ i, G.Adj (x i) (a i) ∧ G.Adj (y i) (b i)) ∧
        Function.Injective (fun z : I × Fin 2 =>
          if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)) ∧
        (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card (D^(37/50:ℝ)) ∧
          ∀ v ∈ (q i).support, v ∈ W) ∧
        Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
        (∀ i, ∃ t, a i = r (x i,t)) ∧ (∀ i, ∃ t, b i = r (y i,t)) ∧
        (∀ i, (q i).edgeSet ⊆ P.edgeSet) := by
  obtain ⟨D₀,hD₀,hroute⟩ := uniform_reservoir_routing c p hc hp
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V _ _ G P _ hPG W hexp hW hr I _ x y hne hx hy hl r hrep hrepne hcap
  obtain ⟨a,b,ha,hb,hs,hl',ha',hb'⟩ :=
    choose_reservoir_endpoints P W x y hne hx hy hl r hrep hrepne _ hcap
  obtain ⟨q,hq,hd⟩ := hroute D hD V P P le_rfl W hexp hW hr I a b
    (fun i => (ha i).1) (fun i => (hb i).1) hl'
  let Q : ∀ i, G.Walk (a i) (b i) := fun i => (q i).mapLe hPG
  refine ⟨a,b,Q,(fun i => ⟨hPG (ha i).2,hPG (hb i).2⟩),hs,?_,?_,ha',hb',?_⟩
  · intro i
    refine ⟨(hq i).1.mapLe hPG,?_,?_⟩
    · simpa only [Q, SimpleGraph.Walk.length_mapLe] using (hq i).2.1
    · simpa only [Q, SimpleGraph.Walk.support_mapLe_eq_support] using (hq i).2.2
  · intro i j hij
    simpa only [Q, SimpleGraph.Walk.edgeSet_mapLe_eq_edgeSet] using hd hij
  · intro i
    rw [show (Q i).edgeSet = (q i).edgeSet from (q i).edgeSet_mapLe_eq_edgeSet hPG]
    intro e he
    exact (q i).edges_subset_edgeSet he

end
end ErdosGallai

namespace ErdosGallai
open _root_.SimpleGraph

variable {V : Type cycleUniverse11} {G : SimpleGraph V} {x y a b : V}

def reservoirReturn (P : G.Walk a b) (hx : G.Adj x a) (hy : G.Adj y b) :
    G.Walk y x := .cons hy (P.reverse.concat hx.symm)

lemma reservoirReturn_isPath (Q : G.Walk x y) (P : G.Walk a b)
    (hQ : Q.IsPath) (hQpos : 0 < Q.length) (hP : P.IsPath)
    (hdisj : Q.support.Disjoint P.support) (hx : G.Adj x a) (hy : G.Adj y b) :
    (reservoirReturn P hx hy).IsPath := by
  have hxy : x ≠ y := by
    intro h
    subst y
    have := hQ.nil_iff_eq.mpr rfl
    have hz : Q.length = 0 := this.length_eq_zero
    omega
  have hxP : x ∉ P.reverse.support := by
    simpa using hdisj Q.start_mem_support
  have hyP : y ∉ P.reverse.support := by
    simpa using hdisj Q.end_mem_support
  exact (hP.reverse.concat hxP hx.symm).cons (by simpa using And.intro hyP hxy.symm)

theorem reservoir_path_closure (Q : G.Walk x y) (P : G.Walk a b)
    (hQ : Q.IsPath) (hQpos : 0 < Q.length) (hP : P.IsPath)
    (hdisj : Q.support.Disjoint P.support) (hx : G.Adj x a) (hy : G.Adj y b) :
    (Q.append (reservoirReturn P hx hy)).IsCycle ∧
    (Q.append (reservoirReturn P hx hy)).edgeSet =
      Q.edgeSet ∪ P.edgeSet ∪ {s(x,a), s(y,b)} ∧
    3 ≤ (Q.append (reservoirReturn P hx hy)).length := by
  have hreturn := reservoirReturn_isPath Q P hQ hQpos hP hdisj hx hy
  have htail : Q.support.tail.Disjoint (reservoirReturn P hx hy).support.tail := by
    rw [List.disjoint_left]
    intro v hv
    have hvQ := List.mem_of_mem_tail hv
    have hvP : v ∉ P.support := hdisj hvQ
    have hvx : v ≠ x := by
      have hn := hQ.support_nodup
      rw [← Q.cons_tail_support, List.nodup_cons] at hn
      exact fun heq => hn.1 (heq ▸ hv)
    simpa [reservoirReturn] using And.intro hvP hvx
  have hcycle := hQ.isCycle_append hreturn htail (Or.inr (by simp [reservoirReturn]))
  refine ⟨hcycle, ?_, ?_⟩
  · ext e
    simp only [Walk.edgeSet_append, reservoirReturn, Walk.edgeSet_cons,
      Walk.edgeSet_concat, Walk.edgeSet_reverse, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rw [Sym2.eq_swap (a := x) (b := a)]
    tauto
  · simpa [reservoirReturn] using (by omega : 3 ≤ Q.length + (P.length + 1 + 1))

end ErdosGallai

namespace ErdosGallai
noncomputable section
open _root_.SimpleGraph
attribute [local instance] Classical.propDecidable

lemma spoke_sets_pairwise {I : Type cycleUniverse12} {E : Type cycleUniverse13} (e : I × Fin 2 → E)
    (he : Function.Injective e) :
    Pairwise (fun i j => Disjoint ({e (i,0), e (i,1)} : Set E) {e (j,0), e (j,1)}) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro a hai haj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hai haj
  rcases hai with hai | hai <;> rcases haj with haj | haj
  all_goals exact hij (congrArg Prod.fst (he (hai.symm.trans haj)))

lemma pairwise_union_three {I : Type cycleUniverse14} {E : Type cycleUniverse15} (A B S : I → Set E)
    (hA : Pairwise fun i j => Disjoint (A i) (A j))
    (hB : Pairwise fun i j => Disjoint (B i) (B j))
    (hS : Pairwise fun i j => Disjoint (S i) (S j))
    (hAB : ∀ i j, Disjoint (A i) (B j))
    (hAS : ∀ i j, Disjoint (A i) (S j))
    (hBS : ∀ i j, Disjoint (B i) (S j)) :
    Pairwise (fun i j => Disjoint (A i ∪ B i ∪ S i) (A j ∪ B j ∪ S j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro e ((ha | hb) | hs) ((ha' | hb') | hs')
  all_goals first
    | exact Set.disjoint_left.mp (hA hij) ha ha'
    | exact Set.disjoint_left.mp (hB hij) hb hb'
    | exact Set.disjoint_left.mp (hS hij) hs hs'
    | exact Set.disjoint_left.mp (hAB i j) ha hb'
    | exact Set.disjoint_left.mp (hAS i j) ha hs'
    | exact Set.disjoint_left.mp (hBS i j) hb hs'
    | exact Set.disjoint_left.mp (hAB j i) ha' hb
    | exact Set.disjoint_left.mp (hAS j i) ha' hs
    | exact Set.disjoint_left.mp (hBS j i) hb' hs

theorem reservoir_cycle_family {V : Type cycleUniverse16} {I : Type cycleUniverse17} {G : SimpleGraph V}
    {x y a b : I → V} (Q : ∀ i, G.Walk (x i) (y i))
    (P : ∀ i, G.Walk (a i) (b i))
    (hx : ∀ i, G.Adj (x i) (a i)) (hy : ∀ i, G.Adj (y i) (b i))
    (hQ : ∀ i, (Q i).IsPath) (hQpos : ∀ i, 0 < (Q i).length)
    (hP : ∀ i, (P i).IsPath)
    (hsep : ∀ i, (Q i).support.Disjoint (P i).support)
    (hQQ : Pairwise fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet)
    (hPP : Pairwise fun i j => Disjoint (P i).edgeSet (P j).edgeSet)
    (hspoke : Function.Injective (fun z : I × Fin 2 =>
      if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)))
    (hQP : ∀ i j, Disjoint (Q i).edgeSet (P j).edgeSet)
    (hQS : ∀ i j, Disjoint (Q i).edgeSet {s(x j,a j),s(y j,b j)})
    (hPS : ∀ i j, Disjoint (P i).edgeSet {s(x j,a j),s(y j,b j)}) :
    let C := fun i => (Q i).append (reservoirReturn (P i) (hx i) (hy i))
    (∀ i, (C i).IsCycle) ∧
    Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
    (⋃ i, (C i).edgeSet) =
      (⋃ i, (Q i).edgeSet) ∪ (⋃ i, (P i).edgeSet) ∪
        (⋃ i, ({s(x i,a i),s(y i,b i)} : Set (Sym2 V))) := by
  dsimp only
  have hC := fun i => reservoir_path_closure (Q i) (P i) (hQ i) (hQpos i)
    (hP i) (hsep i) (hx i) (hy i)
  refine ⟨fun i => (hC i).1, ?_, ?_⟩
  · have hSS : Pairwise (fun i j => Disjoint
        ({s(x i,a i),s(y i,b i)} : Set (Sym2 V)) {s(x j,a j),s(y j,b j)}) := by
      simpa using spoke_sets_pairwise _ hspoke
    simpa only [fun i => (hC i).2.1] using
      pairwise_union_three (fun i => (Q i).edgeSet) (fun i => (P i).edgeSet)
        (fun i => ({s(x i,a i),s(y i,b i)} : Set (Sym2 V)))
        hQQ hPP hSS hQP hQS hPS
  · simp only [fun i => (hC i).2.1, Set.iUnion_union_distrib]

end
end ErdosGallai

end
end
end

/-! ### Upstream module `Combinatorics/CycleDecomposition/ReservoirRemainder.lean` -/

noncomputable section
open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Finset
noncomputable section
namespace ErdosGallai
noncomputable section
open _root_.Finset _root_.SimpleGraph
attribute [local instance] Classical.propDecidable

lemma walks_edges_disjoint_of_support {V : Type cycleUniverse1} {G H : SimpleGraph V}
    {x y a b : V} (p : G.Walk x y) (q : H.Walk a b)
    (h : p.support.Disjoint q.support) : Disjoint p.edgeSet q.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he he'
  induction e using Sym2.ind with
  | _ u v =>
    exact h (p.fst_mem_support_of_mem_edges he) (q.fst_mem_support_of_mem_edges he')

lemma walk_edges_disjoint_spokes_of_outside {V : Type cycleUniverse2} {I : Type cycleUniverse3} {G : SimpleGraph V}
    {u v : V} (Q : G.Walk u v) (W : Set V) (x y a b : I → V)
    (hQ : ∀ z ∈ Q.support, z ∉ W) (ha : ∀ i, a i ∈ W) (hb : ∀ i, b i ∈ W) :
    ∀ i, Disjoint Q.edgeSet ({s(x i,a i), s(y i,b i)} : Set (Sym2 V)) := by
  intro i
  apply Set.disjoint_left.mpr
  intro e he he'
  rcases he' with rfl | he'
  · exact hQ _ (Q.snd_mem_support_of_mem_edges he) (ha i)
  · have heq : e = s(y i,b i) := he'
    subst e
    exact hQ _ (Q.snd_mem_support_of_mem_edges he) (hb i)

lemma walk_edges_disjoint_spokes_of_inside {V : Type cycleUniverse4} {I : Type cycleUniverse5} {G : SimpleGraph V}
    {u v : V} (Q : G.Walk u v) (W : Set V) (x y a b : I → V)
    (hQ : ∀ z ∈ Q.support, z ∈ W) (hx : ∀ i, x i ∉ W) (hy : ∀ i, y i ∉ W) :
    ∀ i, Disjoint Q.edgeSet ({s(x i,a i), s(y i,b i)} : Set (Sym2 V)) := by
  intro i
  apply Set.disjoint_left.mpr
  intro e he he'
  rcases he' with rfl | he'
  · exact hx i (hQ _ (Q.fst_mem_support_of_mem_edges he))
  · have heq : e = s(y i,b i) := he'
    subst e
    exact hy i (hQ _ (Q.fst_mem_support_of_mem_edges he))

theorem uniform_reservoir_completion (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G P : SimpleGraph V) [DecidableRel P.Adj], P ≤ G →
      ∀ W : Finset V, CutExpansionOn P W (D^(37/50:ℝ)) → 2 ≤ W.card →
      (Fintype.card V : ℝ) ≤ D^(51/50:ℝ) →
      ∀ (I : Type) [Fintype I] (x y : I → V) (Q : ∀ i, G.Walk (x i) (y i)),
      (∀ i, (Q i).IsPath) → (∀ i, 0 < (Q i).length) →
      (∀ i v, v ∈ (Q i).support → v ∉ W) →
      Pairwise (fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet) →
      (∀ v, endpointLoad univ x y v ≤ 2) →
      ∀ r : V × Fin 2 → V,
      (∀ v, v ∉ W → ∀ t, r (v,t) ∈ W ∧ P.Adj v (r (v,t))) →
      (∀ v, v ∉ W → r (v,0) ≠ r (v,1)) →
      (∀ v, ((Wᶜ ×ˢ univ).filter (fun z => r z = v)).card ≤
        ⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊) →
      ∃ (a b : I → V) (q : ∀ i, G.Walk (a i) (b i))
        (C : ∀ i, G.Walk (x i) (x i)),
        (∀ i, (C i).IsCycle) ∧
        Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
        (∀ i, (C i).edgeSet = (Q i).edgeSet ∪ (q i).edgeSet ∪
          {s(x i,a i),s(y i,b i)}) ∧
        (∀ i, (q i).edgeSet ⊆ P.edgeSet ∧ ∀ v ∈ (q i).support, v ∈ W) ∧
        Function.Injective (fun z : I × Fin 2 =>
          if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)) ∧
        (∀ i, ∃ t, a i = r (x i,t)) ∧ (∀ i, ∃ t, b i = r (y i,t)) := by
  obtain ⟨D₀,hD₀,hrouting⟩ := uniform_assigned_reservoir_routing c p hc hp
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V _ _ G P _ hPG W hexp hW hr I _ x y Q hQ hpos hout hQQ hl r hrep hrepne hcap
  have hne : ∀ i, x i ≠ y i := by
    intro i hi
    have hz := ((hQ i).nil_iff_eq.mpr hi).length_eq_zero
    have := hpos i
    omega
  have hx : ∀ i, x i ∉ W := fun i => hout i _ (Q i).start_mem_support
  have hy : ∀ i, y i ∉ W := fun i => hout i _ (Q i).end_mem_support
  obtain ⟨a,b,q,hab,hsp,hq,hdd,ha',hb',hPedge⟩ :=
    hrouting D hD V G P hPG W hexp hW hr I x y hne hx hy hl r hrep hrepne hcap
  have ha : ∀ i, a i ∈ W := fun i => (hq i).2.2 _ (q i).start_mem_support
  have hb : ∀ i, b i ∈ W := fun i => (hq i).2.2 _ (q i).end_mem_support
  have hdisj : ∀ i j, (Q i).support.Disjoint (q j).support := by
    intro i j
    exact List.disjoint_left.mpr (fun v hv hv' => hout i v hv ((hq j).2.2 v hv'))
  let C := fun i => (Q i).append (reservoirReturn (q i) (hab i).1 (hab i).2)
  have hfamily := reservoir_cycle_family Q q (fun i => (hab i).1) (fun i => (hab i).2)
    hQ hpos (fun i => (hq i).1) (fun i => hdisj i i) hQQ hdd hsp
    (fun i j => walks_edges_disjoint_of_support _ _ (hdisj i j))
    (fun i => walk_edges_disjoint_spokes_of_outside (Q i) W x y a b (hout i) ha hb)
    (fun i => walk_edges_disjoint_spokes_of_inside (q i) W x y a b (hq i).2.2 hx hy)
  refine ⟨a,b,q,C,hfamily.1,hfamily.2.1,?_,?_,hsp,ha',hb'⟩
  · intro i
    exact (reservoir_path_closure (Q i) (q i) (hQ i) (hpos i) (hq i).1
      (hdisj i i) (hab i).1 (hab i).2).2.1
  · intro i
    exact ⟨hPedge i,(hq i).2.2⟩

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open _root_.SimpleGraph
attribute [local instance] Classical.propDecidable

lemma exists_reservoir_avoided {V : Type cycleUniverse6} (W : Fin 3 → Set V)
    (hW : Pairwise fun i j => Disjoint (W i) (W j)) (x y : V) :
    ∃ i, x ∉ W i ∧ y ∉ W i := by
  by_contra hno
  have h : ∀ i, x ∈ W i ∨ y ∈ W i := by
    intro i
    by_contra! hi
    exact hno ⟨i,hi⟩
  have h01 := Set.disjoint_left.mp (hW (show (0 : Fin 3) ≠ 1 by decide))
  have h02 := Set.disjoint_left.mp (hW (show (0 : Fin 3) ≠ 2 by decide))
  have h12 := Set.disjoint_left.mp (hW (show (1 : Fin 3) ≠ 2 by decide))
  rcases h 0 with hx0 | hy0 <;>
    rcases h 1 with hx1 | hy1 <;>
    rcases h 2 with hx2 | hy2
  all_goals first
    | exact h01 hx0 hx1
    | exact h02 hx0 hx2
    | exact h12 hx1 hx2
    | exact h01 hy0 hy1
    | exact h02 hy0 hy2
    | exact h12 hy1 hy2

lemma exists_edge_reservoir_avoided {V : Type cycleUniverse7} (W : Fin 3 → Set V)
    (hW : Pairwise fun i j => Disjoint (W i) (W j)) (e : Sym2 V) :
    ∃ i, ∀ v ∈ e, v ∉ W i := by
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨i,hx,hy⟩ := exists_reservoir_avoided W hW x y
    refine ⟨i,?_⟩
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact hx
    · exact hy

noncomputable def reservoirColor {V : Type cycleUniverse8} (W : Fin 3 → Set V)
    (hW : Pairwise fun i j => Disjoint (W i) (W j)) (e : Sym2 V) : Fin 3 :=
  (exists_edge_reservoir_avoided W hW e).choose

lemma reservoirColor_avoids {V : Type cycleUniverse9} (W : Fin 3 → Set V)
    (hW : Pairwise fun i j => Disjoint (W i) (W j)) (e : Sym2 V) :
    ∀ v ∈ e, v ∉ W (reservoirColor W hW e) :=
  (exists_edge_reservoir_avoided W hW e).choose_spec

def complementaryReservoirGraph {V : Type cycleUniverse10} (G : SimpleGraph V)
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (i : Fin 3) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ reservoirColor W hW s(x,y) = i
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro x h; exact G.loopless.irrefl x h.1⟩

lemma complementaryReservoirGraph_edges {V : Type cycleUniverse11} (G : SimpleGraph V)
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (i : Fin 3) :
    (complementaryReservoirGraph G W hW i).edgeSet =
      {e | e ∈ G.edgeSet ∧ reservoirColor W hW e = i} := by
  ext e
  induction e using Sym2.ind with
  | _ x y => rfl

theorem complementary_reservoir_graphs {V : Type cycleUniverse12} (G : SimpleGraph V)
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j)) :
    (∀ i, complementaryReservoirGraph G W hW i ≤ G) ∧
    (∀ i x y, (complementaryReservoirGraph G W hW i).Adj x y →
      x ∉ W i ∧ y ∉ W i) ∧
    Pairwise (fun i j => Disjoint (complementaryReservoirGraph G W hW i).edgeSet
      (complementaryReservoirGraph G W hW j).edgeSet) ∧
    (⋃ i, (complementaryReservoirGraph G W hW i).edgeSet) = G.edgeSet := by
  refine ⟨fun _ _ _ h => h.1, ?_, ?_, ?_⟩
  · intro i x y h
    have hx := reservoirColor_avoids W hW s(x,y) x (Sym2.mem_mk_left x y)
    have hy := reservoirColor_avoids W hW s(x,y) y (Sym2.mem_mk_right x y)
    rw [h.2] at hx hy
    exact ⟨hx,hy⟩
  · intro i j hij
    rw [complementaryReservoirGraph_edges, complementaryReservoirGraph_edges]
    exact Set.disjoint_left.mpr fun _ he hj => hij (he.2.symm.trans hj.2)
  · ext e
    simp only [Set.mem_iUnion, complementaryReservoirGraph_edges, Set.mem_ofPred]
    constructor
    · rintro ⟨i,he,_⟩; exact he
    · intro he; exact ⟨reservoirColor W hW e, he, rfl⟩

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open _root_.Finset _root_.SimpleGraph
attribute [local instance] Classical.propDecidable

def reservoirInternal {V : Type cycleUniverse13} (P : SimpleGraph V) (W : Set V) : Set (Sym2 V) :=
  {e | e ∈ P.edgeSet ∧ ∀ v ∈ e, v ∈ W}

noncomputable def reservoirSpokes {V : Type cycleUniverse14} [Fintype V] [DecidableEq V]
    (W : Finset V) (r : V × Fin 2 → V) : Finset (Sym2 V) :=
  (Wᶜ ×ˢ univ).image (fun z => s(z.1,r z))

lemma mem_reservoirSpokes {V : Type cycleUniverse15} [Fintype V] [DecidableEq V]
    (W : Finset V) (r : V × Fin 2 → V) (e : Sym2 V) :
    e ∈ reservoirSpokes W r ↔ ∃ v ∉ W, ∃ t : Fin 2, e = s(v,r (v,t)) := by
  simp only [reservoirSpokes, Finset.mem_image, Finset.mem_product,
    Finset.mem_compl, Finset.mem_univ, and_true, Prod.exists]
  constructor
  · rintro ⟨v,t,hv,he⟩
    exact ⟨v,hv,t,he.symm⟩
  · rintro ⟨v,hv,t,he⟩
    exact ⟨v,t,hv,he.symm⟩

lemma reservoirSpokes_card_le {V : Type cycleUniverse16} [Fintype V] [DecidableEq V]
    (W : Finset V) (r : V × Fin 2 → V) :
    (reservoirSpokes W r).card ≤ 2 * Fintype.card V := by
  apply (Finset.card_image_le).trans
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have := Finset.card_le_univ Wᶜ
  omega

lemma reservoirSpokes_subset {V : Type cycleUniverse17} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (W : Finset V) (r : V × Fin 2 → V)
    (hr : ∀ v, v ∉ W → ∀ t, P.Adj v (r (v,t))) :
    (reservoirSpokes W r : Set (Sym2 V)) ⊆ P.edgeSet := by
  intro e he
  obtain ⟨v,hv,t,rfl⟩ := (mem_reservoirSpokes W r e).mp he
  exact hr v hv t

lemma reservoirInternal_spokes_disjoint {V : Type cycleUniverse18} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (W : Finset V) (r : V × Fin 2 → V) :
    Disjoint (reservoirInternal P W) (reservoirSpokes W r : Set (Sym2 V)) := by
  apply Set.disjoint_left.mpr
  intro e he he'
  obtain ⟨v,hv,t,rfl⟩ := (mem_reservoirSpokes W r e).mp he'
  exact hv (he.2 _ (Sym2.mem_mk_left _ _))

theorem reservoir_reservations {V : Type cycleUniverse19} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Fin 3 → SimpleGraph V) (W : Fin 3 → Finset V)
    (r : Fin 3 → V × Fin 2 → V)
    (hPG : ∀ i, P i ≤ G)
    (hPP : Pairwise fun i j => Disjoint (P i).edgeSet (P j).edgeSet)
    (hr : ∀ i v, v ∉ W i → ∀ t, (P i).Adj v (r i (v,t))) :
    let R := fun i => reservoirInternal (P i) (W i)
    let O := fun i => (reservoirSpokes (W i) (r i) : Set (Sym2 V))
    (∀ i, R i ⊆ G.edgeSet ∧ O i ⊆ G.edgeSet) ∧
    Pairwise (fun i j => Disjoint (R i ∪ O i) (R j ∪ O j)) ∧
    (∀ i, Disjoint (R i) (O i)) ∧
    Disjoint (⋃ i, R i) (⋃ i, O i) ∧
    (∑ i, (reservoirSpokes (W i) (r i)).card) ≤ 6 * Fintype.card V := by
  dsimp only
  have hR : ∀ i, reservoirInternal (P i) (W i) ⊆ (P i).edgeSet := fun _ _ he => he.1
  have hO := fun i => reservoirSpokes_subset (P i) (W i) (r i) (hr i)
  have hU : ∀ i, reservoirInternal (P i) (W i) ∪
      (reservoirSpokes (W i) (r i) : Set (Sym2 V)) ⊆ (P i).edgeSet :=
    fun i => Set.union_subset (hR i) (hO i)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    exact ⟨(hR i).trans (SimpleGraph.edgeSet_mono (hPG i)),
      (hO i).trans (SimpleGraph.edgeSet_mono (hPG i))⟩
  · intro i j hij
    exact (hPP hij).mono (hU i) (hU j)
  · exact fun i => reservoirInternal_spokes_disjoint (P i) (W i) (r i)
  · rw [Set.disjoint_iUnion_left]
    intro i
    rw [Set.disjoint_iUnion_right]
    intro j
    by_cases hij : i = j
    · subst j
      exact reservoirInternal_spokes_disjoint (P i) (W i) (r i)
    · exact (hPP hij).mono (hR i) (hO j)
  · calc
      _ ≤ ∑ _i : Fin 3, 2 * Fintype.card V :=
        Finset.sum_le_sum (fun i _ => reservoirSpokes_card_le (W i) (r i))
      _ = _ := by simp; omega

lemma complementary_walk_outside {V : Type cycleUniverse20} {G : SimpleGraph V}
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (i : Fin 3) {x y : V} (q : (complementaryReservoirGraph G W hW i).Walk x y)
    (hq : 0 < q.length) : ∀ v ∈ q.support, v ∉ W i := by
  have hn : ¬ q.Nil := by
    intro h
    have hz := h.length_eq_zero
    omega
  intro v hv
  obtain ⟨e,he,hve⟩ := SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hn |>.mp hv
  have heG := q.edges_subset_edgeSet he
  have hecol : reservoirColor W hW e = i := by
    rw [complementaryReservoirGraph_edges] at heG
    exact heG.2
  exact hecol ▸ reservoirColor_avoids W hW e v hve

theorem complementary_reservation_ledger {V : Type cycleUniverse21} (G : SimpleGraph V)
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (E : Set (Sym2 V)) (hE : E ⊆ G.edgeSet) :
    let H := G.deleteEdges E
    let K := fun i => complementaryReservoirGraph H W hW i
    Pairwise (fun i j => Disjoint (K i).edgeSet (K j).edgeSet) ∧
    (∀ i, Disjoint (K i).edgeSet E) ∧
    ((⋃ i, (K i).edgeSet) ∪ E = G.edgeSet) := by
  dsimp only
  have hh := complementary_reservoir_graphs (G.deleteEdges E) W hW
  refine ⟨hh.2.2.1,?_,?_⟩
  · intro i
    apply Set.disjoint_left.mpr
    intro e he he'
    have h := SimpleGraph.edgeSet_mono (hh.1 i) he
    rw [SimpleGraph.edgeSet_deleteEdges] at h
    exact h.2 he'
  · rw [hh.2.2.2, SimpleGraph.edgeSet_deleteEdges]
    exact Set.sdiff_union_of_subset hE

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open _root_.Finset _root_.SimpleGraph
attribute [local instance] Classical.propDecidable

def edgeRestriction {V : Type cycleUniverse22} (G : SimpleGraph V) (E : Set (Sym2 V)) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ s(x,y) ∈ E
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro x h; exact G.loopless.irrefl x h.1⟩

lemma edgeRestriction_le {V : Type cycleUniverse23} (G : SimpleGraph V) (E : Set (Sym2 V)) :
    edgeRestriction G E ≤ G := fun _ _ h => h.1

lemma edgeRestriction_edges {V : Type cycleUniverse24} (G : SimpleGraph V) (E : Set (Sym2 V)) :
    (edgeRestriction G E).edgeSet = G.edgeSet ∩ E := by
  ext e
  induction e using Sym2.ind with | _ x y => rfl

lemma edgeRestriction_edges_of_subset {V : Type cycleUniverse25} (G : SimpleGraph V) (E : Set (Sym2 V))
    (hE : E ⊆ G.edgeSet) : (edgeRestriction G E).edgeSet = E := by
  rw [edgeRestriction_edges, Set.inter_eq_right.mpr hE]

def completedEdges {V : Type cycleUniverse26} {I : Type cycleUniverse27} (C : I → Set (Sym2 V)) : Set (Sym2 V) := ⋃ i, C i

def residualInternalGraph {V : Type cycleUniverse28} {B : Type cycleUniverse29} {I : Type cycleUniverse30} (G : SimpleGraph V)
    (R : B → Set (Sym2 V)) (C : I → Set (Sym2 V)) (b : B) : SimpleGraph V :=
  edgeRestriction G (R b \ completedEdges C)

def unusedSpokes {V : Type cycleUniverse31} {I : Type cycleUniverse32} [Fintype V] (S : Set (Sym2 V))
    (C : I → Set (Sym2 V)) : Finset (Sym2 V) := (S \ completedEdges C).toFinset

lemma unusedSpokes_card_le {V : Type cycleUniverse33} {I : Type cycleUniverse34} [Fintype V] (S : Finset (Sym2 V))
    (C : I → Set (Sym2 V)) : (unusedSpokes (↑S) C).card ≤ S.card := by
  apply Finset.card_le_card
  intro e he
  simp only [unusedSpokes, Set.mem_toFinset, Finset.mem_coe, Set.mem_sdiff] at he
  exact he.1

theorem residue_edge_ledger {V : Type cycleUniverse35} {B : Type cycleUniverse36} {I : Type cycleUniverse37} [Fintype V]
    (G : SimpleGraph V) (R : B → Set (Sym2 V)) (S : Set (Sym2 V))
    (C : I → Set (Sym2 V))
    (hR : ∀ b, R b ⊆ G.edgeSet) (hS : S ⊆ G.edgeSet)
    (hRR : Pairwise fun b c => Disjoint (R b) (R c))
    (hRS : ∀ b, Disjoint (R b) S)
    (hC : ∀ i, C i ⊆ G.edgeSet)
    (_hCC : Pairwise fun i j => Disjoint (C i) (C j))
    (hcover : G.edgeSet \ ((⋃ b, R b) ∪ S) ⊆ completedEdges C) :
    (∀ b, (residualInternalGraph G R C b).edgeSet = R b \ completedEdges C) ∧
    Pairwise (fun b c => Disjoint (residualInternalGraph G R C b).edgeSet
      (residualInternalGraph G R C c).edgeSet) ∧
    (∀ b i, Disjoint (residualInternalGraph G R C b).edgeSet (C i)) ∧
    (∀ b, Disjoint (residualInternalGraph G R C b).edgeSet (↑(unusedSpokes S C) : Set _)) ∧
    (∀ i, Disjoint (C i) (↑(unusedSpokes S C) : Set _)) ∧
    (completedEdges C ∪ (↑(unusedSpokes S C) : Set _) ∪
      (⋃ b, (residualInternalGraph G R C b).edgeSet)) = G.edgeSet := by
  classical
  have hrem (b : B) : (residualInternalGraph G R C b).edgeSet = R b \ completedEdges C := by
    apply edgeRestriction_edges_of_subset
    exact fun e he => hR b he.1
  have hsingle : (↑(unusedSpokes S C) : Set _) = S \ completedEdges C := by
    simp only [unusedSpokes, Set.coe_toFinset]
  have hsub : completedEdges C ⊆ G.edgeSet := by
    rintro e he
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
    exact hC i hi
  refine ⟨hrem,?_,?_,?_,?_,?_⟩
  · intro b c hbc
    rw [hrem b,hrem c]
    exact (hRR hbc).mono Set.sdiff_subset Set.sdiff_subset
  · intro b i
    rw [hrem b]
    apply Set.disjoint_left.mpr
    intro e he hi
    exact he.2 (Set.mem_iUnion.mpr ⟨i,hi⟩)
  · intro b
    rw [hrem b,hsingle]
    exact (hRS b).mono Set.sdiff_subset Set.sdiff_subset
  · intro i
    rw [hsingle]
    apply Set.disjoint_left.mpr
    intro e hi he
    exact he.2 (Set.mem_iUnion.mpr ⟨i,hi⟩)
  · rw [hsingle]
    ext e
    constructor
    · rintro ((he | he) | he)
      · exact hsub he
      · exact hS he.1
      · obtain ⟨b,hb⟩ := Set.mem_iUnion.mp he
        rw [hrem b] at hb
        exact hR b hb.1
    · intro he
      by_cases hc : e ∈ completedEdges C
      · exact Or.inl (Or.inl hc)
      by_cases hs : e ∈ S
      · exact Or.inl (Or.inr ⟨hs,hc⟩)
      have hr : e ∈ ⋃ b, R b := by
        by_contra hr
        exact hc (hcover ⟨he,by intro hu; exact hu.elim hr hs⟩)
      obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hr
      exact Or.inr (Set.mem_iUnion.mpr ⟨b,by rw [hrem b]; exact ⟨hb,hc⟩⟩)

theorem residue_part_count {V : Type cycleUniverse38} {I : Type cycleUniverse39} [Fintype V] [Fintype I]
    (S : Finset (Sym2 V)) (C : I → Set (Sym2 V))
    (hI : Fintype.card I ≤ 3 * Fintype.card V)
    (hS : S.card ≤ 6 * Fintype.card V) :
    Fintype.card I + (unusedSpokes (↑S) C).card ≤ 9 * Fintype.card V := by
  have := unusedSpokes_card_le S C
  omega

lemma induce_edge_image_of_support_subset {V : Type cycleUniverse40} (H : SimpleGraph V)
    (W : Set V) (hW : H.support ⊆ W) :
    Sym2.map Subtype.val '' (H.induce W).edgeSet = H.edgeSet := by
  ext e
  constructor
  · rintro ⟨d,hd,rfl⟩
    induction d using Sym2.ind with
    | _ x y => exact hd
  · intro he
    induction e using Sym2.ind with
    | _ x y =>
      have hx : x ∈ W := hW ⟨y,he⟩
      have hy : y ∈ W := hW ⟨x,he.symm⟩
      exact ⟨s(⟨x,hx⟩,⟨y,hy⟩),he,rfl⟩

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open _root_.Finset _root_.SimpleGraph
attribute [local instance] Classical.propDecidable

lemma walk_edges_internal {V : Type cycleUniverse44} {G P : SimpleGraph V} {a b : V}
    (W : Set V) (q : G.Walk a b) (he : q.edgeSet ⊆ P.edgeSet)
    (hv : ∀ v ∈ q.support, v ∈ W) :
    q.edgeSet ⊆ reservoirInternal P W := by
  intro e h
  refine ⟨he h,?_⟩
  induction e using Sym2.ind with
  | _ x y =>
    intro v hmem
    rcases (Sym2.mem_iff.mp hmem) with rfl | rfl
    · exact hv _ (q.fst_mem_support_of_mem_edges h)
    · exact hv _ (q.snd_mem_support_of_mem_edges h)

lemma completion_edges_subset {V : Type cycleUniverse45} [Fintype V] [DecidableEq V]
    {G P : SimpleGraph V} (W : Finset V) (r : V × Fin 2 → V)
    {x y a b : V} (Q : G.Walk x y) (q : G.Walk a b) (C : G.Walk x x)
    (K : Set (Sym2 V)) (hQ : Q.edgeSet ⊆ K)
    (hC : C.edgeSet = Q.edgeSet ∪ q.edgeSet ∪ {s(x,a),s(y,b)})
    (hq : q.edgeSet ⊆ P.edgeSet ∧ ∀ v ∈ q.support, v ∈ W)
    (hx : x ∉ W) (hy : y ∉ W)
    (ha : ∃ t, a = r (x,t)) (hb : ∃ t, b = r (y,t)) :
    C.edgeSet ⊆ K ∪ (reservoirInternal P W ∪ (reservoirSpokes W r : Set _)) := by
  rw [hC]
  have hqi := walk_edges_internal (W : Set V) q hq.1 hq.2
  intro e he
  rcases he with (he | he) | he
  · exact Or.inl (hQ he)
  · exact Or.inr (Or.inl (hqi he))
  · apply Or.inr ∘ Or.inr
    rcases (show e = s(x,a) ∨ e = s(y,b) by simpa using he) with rfl | rfl
    · obtain ⟨t,rfl⟩ := ha
      exact (mem_reservoirSpokes W r _).mpr ⟨x,hx,t,rfl⟩
    · obtain ⟨t,rfl⟩ := hb
      exact (mem_reservoirSpokes W r _).mpr ⟨y,hy,t,rfl⟩

lemma completed_subfamilies_disjoint {E : Type cycleUniverse46} {B : Type cycleUniverse47} {I : B → Type cycleUniverse55}
    (K R : B → Set E) (C : ∀ b, I b → Set E)
    (hKK : Pairwise fun b c => Disjoint (K b) (K c))
    (hRR : Pairwise fun b c => Disjoint (R b) (R c))
    (hKR : ∀ b c, Disjoint (K b) (R c))
    (hC : ∀ b i, C b i ⊆ K b ∪ R b)
    (hCC : ∀ b, Pairwise fun i j => Disjoint (C b i) (C b j)) :
    Pairwise (fun s t : Sigma I => Disjoint (C s.1 s.2) (C t.1 t.2)) := by
  rintro ⟨b,i⟩ ⟨c,j⟩ hne
  by_cases hbc : b = c
  · subst c
    apply hCC b
    intro hij
    exact hne (by cases hij; rfl)
  · apply Disjoint.mono (hC b i) (hC c j)
    rw [Set.disjoint_union_left,Set.disjoint_union_right,Set.disjoint_union_right]
    exact ⟨⟨hKK hbc,hKR b c⟩,⟨(hKR c b).symm,hRR hbc⟩⟩

lemma completed_subfamilies_cover {E : Type cycleUniverse48} {B : Type cycleUniverse49} {I : B → Type cycleUniverse56}
    (K : B → Set E) (Q C : ∀ b, I b → Set E)
    (hQ : ∀ b, (⋃ i, Q b i) = K b)
    (hQC : ∀ b i, Q b i ⊆ C b i) :
    (⋃ b, K b) ⊆ ⋃ s : Sigma I, C s.1 s.2 := by
  intro e he
  obtain ⟨b,hb⟩ := Set.mem_iUnion.mp he
  rw [← hQ b] at hb
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hb
  exact Set.mem_iUnion.mpr ⟨⟨b,i⟩,hQC b i hi⟩

lemma endpointLoad_family_card {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]
    (x y : I → V) (hne : ∀ i, x i ≠ y i)
    (hload : ∀ v, endpointLoad univ x y v ≤ 2) :
    Fintype.card I ≤ Fintype.card V := by
  classical
  have hs := endpointLoad_sum (univ : Finset I) x y (fun i _ => hne i)
  have hb := Finset.sum_le_sum (fun v (_ : v ∈ (univ : Finset V)) => hload v)
  simp only [Finset.card_univ] at hs
  rw [hs] at hb
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hb
  omega

lemma sigma_three_card_le {V : Type} [Fintype V]
    (I : Fin 3 → Type) [∀ b, Fintype (I b)]
    (hI : ∀ b, Fintype.card (I b) ≤ Fintype.card V) :
    Fintype.card (Sigma I) ≤ 3 * Fintype.card V := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _b : Fin 3, Fintype.card V := Finset.sum_le_sum (fun b _ => hI b)
    _ = _ := by simp [mul_comm]

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open _root_.Finset _root_.SimpleGraph
attribute [local instance] Classical.propDecidable

theorem uniform_three_reservoir_completion (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G : SimpleGraph V) (P K : Fin 3 → SimpleGraph V)
        [∀ b, DecidableRel (P b).Adj],
      (∀ b, P b ≤ G) →
      Pairwise (fun b d => Disjoint (P b).edgeSet (P d).edgeSet) →
      ∀ (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V),
      (∀ b, CutExpansionOn (P b) (W b) (D^(37/50:ℝ))) →
      (∀ b, 2 ≤ (W b).card) → (Fintype.card V : ℝ) ≤ D^(51/50:ℝ) →
      (∀ b v, v ∉ W b → ∀ t, r b (v,t) ∈ W b ∧ (P b).Adj v (r b (v,t))) →
      (∀ b v, v ∉ W b → r b (v,0) ≠ r b (v,1)) →
      (∀ b v, (((W b)ᶜ ×ˢ univ).filter (fun z => r b z = v)).card ≤
        ⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊) →
      let T := fun b => reservoirInternal (P b) (W b) ∪
        (reservoirSpokes (W b) (r b) : Set (Sym2 V))
      Pairwise (fun b d => Disjoint (K b).edgeSet (K d).edgeSet) →
      (∀ b d, Disjoint (K b).edgeSet (T d)) →
      ∀ (I : Fin 3 → Type) [∀ b, Fintype (I b)]
        (x y : ∀ b, I b → V) (Q : ∀ b i, G.Walk (x b i) (y b i)),
      (∀ b i, (Q b i).IsPath) → (∀ b i, 0 < (Q b i).length) →
      (∀ b i v, v ∈ (Q b i).support → v ∉ W b) →
      (∀ b, Pairwise fun i j => Disjoint (Q b i).edgeSet (Q b j).edgeSet) →
      (∀ b, (⋃ i, (Q b i).edgeSet) = (K b).edgeSet) →
      (∀ b v, endpointLoad univ (x b) (y b) v ≤ 2) →
      ∃ C : ∀ b i, G.Walk (x b i) (x b i),
        (∀ b i, (C b i).IsCycle) ∧
        Pairwise (fun s t : Sigma I =>
          Disjoint (C s.1 s.2).edgeSet (C t.1 t.2).edgeSet) ∧
        (∀ b i, (C b i).edgeSet ⊆ (K b).edgeSet ∪ T b) ∧
        (⋃ b, (K b).edgeSet) ⊆ (⋃ s : Sigma I, (C s.1 s.2).edgeSet) ∧
        Fintype.card (Sigma I) ≤ 3 * Fintype.card V := by
  classical
  obtain ⟨D₀,hD₀,hclose⟩ := uniform_reservoir_completion c p hc hp
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V _ _ G P K _ hPG hPP W r hexp hW hn hr hrne hcap
  dsimp only
  intro hKK hKT I _ x y Q hQ hpos hout hQQ hcover hl
  have hex : ∀ b : Fin 3,
      ∃ (a z : I b → V) (q : ∀ i, G.Walk (a i) (z i))
        (C : ∀ i, G.Walk (x b i) (x b i)),
        (∀ i, (C i).IsCycle) ∧
        Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
        (∀ i, (C i).edgeSet = (Q b i).edgeSet ∪ (q i).edgeSet ∪
          {s(x b i,a i),s(y b i,z i)}) ∧
        (∀ i, (q i).edgeSet ⊆ (P b).edgeSet ∧ ∀ v ∈ (q i).support, v ∈ W b) ∧
        Function.Injective (fun z' : I b × Fin 2 =>
          if z'.2 = 0 then s(x b z'.1,a z'.1) else s(y b z'.1,z z'.1)) ∧
        (∀ i, ∃ t, a i = r b (x b i,t)) ∧
        (∀ i, ∃ t, z i = r b (y b i,t)) := by
    intro b
    exact hclose D hD V G (P b) (hPG b) (W b) (hexp b) (hW b) hn
      (I b) (x b) (y b) (Q b) (hQ b) (hpos b) (hout b) (hQQ b) (hl b)
      (r b) (hr b) (hrne b) (hcap b)
  choose a z q C hCy hCC hCe hqe _hsp ha hz using hex
  have hsub : ∀ b i, (C b i).edgeSet ⊆ (K b).edgeSet ∪
      (reservoirInternal (P b) (W b) ∪ (reservoirSpokes (W b) (r b) : Set _)) := by
    intro b i
    apply completion_edges_subset (W b) (r b) (Q b i) (q b i) (C b i)
      (K b).edgeSet _ (hCe b i) (hqe b i)
      (hout b i _ (Q b i).start_mem_support)
      (hout b i _ (Q b i).end_mem_support) (ha b i) (hz b i)
    intro e he
    rw [← hcover b]
    exact Set.mem_iUnion.mpr ⟨i,he⟩
  have hreserv := reservoir_reservations G P W r hPG hPP
    (fun b v hv t => (hr b v hv t).2)
  refine ⟨C,hCy,?_,hsub,?_,?_⟩
  · exact completed_subfamilies_disjoint (fun b => (K b).edgeSet)
      (fun b => reservoirInternal (P b) (W b) ∪
        (reservoirSpokes (W b) (r b) : Set _))
      (fun b i => (C b i).edgeSet) hKK hreserv.2.1 hKT hsub hCC
  · apply completed_subfamilies_cover (fun b => (K b).edgeSet)
      (fun b i => (Q b i).edgeSet) (fun b i => (C b i).edgeSet) hcover
    intro b i e he
    rw [hCe b i]
    exact Or.inl (Or.inl he)
  · apply sigma_three_card_le I
    intro b
    apply endpointLoad_family_card (x b) (y b) _ (hl b)
    intro i hi
    have hz := ((hQ b i).nil_iff_eq.mpr hi).length_eq_zero
    have hp := hpos b i
    omega

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable

noncomputable def allReservoirSpokes {V : Type cycleUniverse50} [Fintype V] [DecidableEq V]
    (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V) : Finset (Sym2 V) :=
  univ.biUnion (fun b => reservoirSpokes (W b) (r b))

lemma coe_allReservoirSpokes {V : Type cycleUniverse51} [Fintype V] [DecidableEq V]
    (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V) :
    (allReservoirSpokes W r : Set (Sym2 V)) =
      ⋃ b, (reservoirSpokes (W b) (r b) : Set (Sym2 V)) := by
  ext e
  simp [allReservoirSpokes]

lemma allReservoirSpokes_card_le {V : Type cycleUniverse52} [Fintype V] [DecidableEq V]
    (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V) :
    (allReservoirSpokes W r).card ≤ 6 * Fintype.card V := by
  apply (Finset.card_biUnion_le).trans
  calc
    (∑ b : Fin 3, (reservoirSpokes (W b) (r b)).card) ≤
      ∑ _b : Fin 3, 2 * Fintype.card V :=
        Finset.sum_le_sum (fun b _ => reservoirSpokes_card_le (W b) (r b))
    _ = _ := by simp; omega

theorem three_reservoir_remainder {V : Type cycleUniverse53} {I : Type cycleUniverse54} [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) (P : Fin 3 → SimpleGraph V)
    (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V)
    (hPG : ∀ b, P b ≤ G)
    (hPP : Pairwise fun b d => Disjoint (P b).edgeSet (P d).edgeSet)
    (hr : ∀ b v, v ∉ W b → ∀ t, (P b).Adj v (r b (v,t)))
    (C : I → Set (Sym2 V)) (hC : ∀ i, C i ⊆ G.edgeSet)
    (hCC : Pairwise fun i j => Disjoint (C i) (C j))
    (hI : Fintype.card I ≤ 3 * Fintype.card V)
    (hcover : G.edgeSet \ ((⋃ b, reservoirInternal (P b) (W b)) ∪
      (allReservoirSpokes W r : Set _)) ⊆ completedEdges C) :
    let R := fun b => reservoirInternal (P b) (W b)
    let H := residualInternalGraph G R C
    let S := unusedSpokes (↑(allReservoirSpokes W r)) C
    (∀ b, (H b).support ⊆ (W b : Set V)) ∧
    (∀ b, Sym2.map Subtype.val '' ((H b).induce (W b : Set V)).edgeSet = (H b).edgeSet) ∧
    (∀ b, (H b).edgeSet = R b \ completedEdges C) ∧
    Pairwise (fun b d => Disjoint (H b).edgeSet (H d).edgeSet) ∧
    (∀ b i, Disjoint (H b).edgeSet (C i)) ∧
    (∀ b, Disjoint (H b).edgeSet (S : Set _)) ∧
    (∀ i, Disjoint (C i) (S : Set _)) ∧
    (completedEdges C ∪ (S : Set _) ∪ (⋃ b, (H b).edgeSet)) = G.edgeSet ∧
    Fintype.card I + S.card ≤ 9 * Fintype.card V := by
  classical
  dsimp only
  obtain ⟨hsub,hTT,_hown,hRS,_hcount⟩ := reservoir_reservations G P W r hPG hPP hr
  have hS : (allReservoirSpokes W r : Set (Sym2 V)) ⊆ G.edgeSet := by
    rw [coe_allReservoirSpokes]
    exact Set.iUnion_subset (fun b => (hsub b).2)
  have hRR : Pairwise fun b d =>
      Disjoint (reservoirInternal (P b) (W b)) (reservoirInternal (P d) (W d)) := by
    intro b d hbd
    exact (hTT hbd).mono Set.subset_union_left Set.subset_union_left
  have hRO : ∀ b, Disjoint (reservoirInternal (P b) (W b))
      (allReservoirSpokes W r : Set (Sym2 V)) := by
    intro b
    rw [coe_allReservoirSpokes]
    exact hRS.mono_left (Set.subset_iUnion (fun d => reservoirInternal (P d) (W d)) b)
  let R := fun b => reservoirInternal (P b) (W b)
  let H := residualInternalGraph G R C
  have hledger := residue_edge_ledger G R (↑(allReservoirSpokes W r)) C
    (fun b => (hsub b).1) hS hRR hRO hC hCC hcover
  have hsupp : ∀ b, (H b).support ⊆ (W b : Set V) := by
    intro b v hv
    obtain ⟨w,hw⟩ := (H b).mem_support.mp hv
    have he : s(v,w) ∈ (H b).edgeSet := hw
    rw [hledger.1 b] at he
    exact he.1.2 _ (Sym2.mem_mk_left _ _)
  refine ⟨hsupp,?_,hledger.1,hledger.2.1,hledger.2.2.1,
    hledger.2.2.2.1,hledger.2.2.2.2.1,hledger.2.2.2.2.2,?_⟩
  · intro b
    exact induce_edge_image_of_support_subset (H b) (W b) (hsupp b)
  · exact residue_part_count (allReservoirSpokes W r) C hI (allReservoirSpokes_card_le W r)

end
end ErdosGallai

end
end
/-! ### Upstream module `Combinatorics/CycleDecomposition/Lovasz.lean` -/

noncomputable section
noncomputable section
namespace ErdosGallai.Lovasz
noncomputable section
open _root_.SimpleGraph
attribute [local instance] Classical.propDecidable

def StarActive {V : Type cycleUniverse1} (S : Set V) (R : V → V → Prop) (v : V) : Prop :=
  ∃ a ∈ S, Relation.ReflTransGen R a v

lemma starActive_source {V : Type cycleUniverse2} {S : Set V} {R : V → V → Prop}
    {v : V} (hv : v ∈ S) : StarActive S R v :=
  ⟨v, hv, .refl⟩

lemma starActive_step {V : Type cycleUniverse3} {S : Set V} {R : V → V → Prop}
    {v w : V} (hv : StarActive S R v) (h : R v w) : StarActive S R w := by
  obtain ⟨a, ha, hr⟩ := hv
  exact ⟨a, ha, hr.tail h⟩

lemma starActive_iff {V : Type cycleUniverse4} {S : Set V} {R : V → V → Prop} {v : V} :
    StarActive S R v ↔ v ∈ S ∨ ∃ w, StarActive S R w ∧ R w v := by
  constructor
  · rintro ⟨a, ha, hr⟩
    rcases hr.cases_tail with rfl | ⟨w, hw, h⟩
    · exact Or.inl ha
    · exact Or.inr ⟨w, ⟨a, ha, hw⟩, h⟩
  · rintro (h | ⟨w, hw, h⟩)
    · exact starActive_source h
    · exact starActive_step hw h

lemma starActive_subset {V : Type cycleUniverse6} {S T : Set V} {R : V → V → Prop}
    (hS : S ⊆ T) (hR : ∀ a b, R a b → b ∈ T) :
    {v | StarActive S R v} ⊆ T := by
  rintro v ⟨a, ha, hr⟩
  rcases hr.cases_tail with rfl | ⟨w, _, h⟩
  · exact hS ha
  · exact hR w v h

lemma star_inj {V : Type cycleUniverse8} {x a b : V} : s(x,a) = s(x,b) ↔ a = b := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, h'⟩)
    · exact h
    · exact h'.trans h
  · intro h; exact Or.inl ⟨rfl, h⟩

structure PathPiece {V : Type cycleUniverse9} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  positive : 0 < walk.length

lemma PathPiece.ends_ne {V : Type cycleUniverse10} {G : SimpleGraph V} (P : PathPiece G) :
    P.start ≠ P.finish := by
  intro h
  have hz := (P.isPath.nil_iff_eq.mpr h).length_eq_zero
  have := P.positive
  omega

structure Piece {V : Type cycleUniverse11} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  simple : (walk.IsPath ∧ 0 < walk.length) ∨
    ∃ h : finish = start, (walk.copy rfl h).IsCycle

namespace Piece
variable {V : Type cycleUniverse12} {G : SimpleGraph V}

def ofPath (p : PathPiece G) : Piece G :=
  ⟨p.start, p.finish, p.walk, Or.inl ⟨p.isPath, p.positive⟩⟩

def ofCycle {v : V} (p : G.Walk v v) (h : p.IsCycle) : Piece G :=
  ⟨v, v, p, Or.inr ⟨rfl, h⟩⟩

end Piece

structure Arm {V : Type cycleUniverse13} (G : SimpleGraph V) (x : V) where
  near : V
  far : V
  adj : G.Adj x near
  walk : G.Walk near far
  isPath : walk.IsPath
  avoids : x ∉ walk.support

namespace Arm
variable {V : Type cycleUniverse14} {G : SimpleGraph V} {x : V}

def tip (A : Arm G x) : PathPiece G where
  start := x
  finish := A.far
  walk := .cons A.adj A.walk
  isPath := A.isPath.cons A.avoids
  positive := by simp

def flip (A : Arm G x) (h : G.Adj x A.far) : Arm G x where
  near := A.far
  far := A.near
  adj := h
  walk := A.walk.reverse
  isPath := A.isPath.reverse
  avoids := by simpa using A.avoids

@[simp] lemma flip_edges (A : Arm G x) (h : G.Adj x A.far) :
    (A.flip h).walk.edgeSet = A.walk.edgeSet := by simp [flip]

@[simp] lemma mem_flip_support (A : Arm G x) (h : G.Adj x A.far) (v : V) :
    v ∈ (A.flip h).walk.support ↔ v ∈ A.walk.support := by simp [flip]

lemma two_arms_isPath (A B : Arm G x)
    (hd : A.walk.support.Disjoint B.walk.support) :
    ((Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)).IsPath := by
  apply Walk.IsPath.mk'
  simp only [Walk.support_append, Walk.support_reverse, Walk.support_cons,
    List.tail_cons, List.reverse_cons, List.append_assoc]
  apply List.nodup_append'.mpr
  refine ⟨List.nodup_reverse.mpr A.isPath.support_nodup, ?_, ?_⟩
  · exact List.nodup_cons.mpr ⟨B.avoids, B.isPath.support_nodup⟩
  · rw [List.disjoint_left]
    intro v hv hq
    have hav : v ∈ A.walk.support := List.mem_reverse.mp hv
    rcases List.mem_cons.mp hq with rfl | hq
    · exact A.avoids hav
    · exact List.disjoint_left.mp hd hav hq

def join (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support) : PathPiece G where
  start := A.far
  finish := B.far
  walk := (Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)
  isPath := two_arms_isPath A B hd
  positive := by simp only [Walk.length_append, Walk.length_reverse, Walk.length_cons]; omega

lemma join_edges (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support) :
    (A.join B hd).walk.edgeSet =
      A.walk.edgeSet ∪ B.walk.edgeSet ∪ {s(x,A.near), s(x,B.near)} := by
  simp only [join, Walk.edgeSet_append, Walk.edgeSet_reverse, Walk.edgeSet_cons]
  ext e
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

lemma near_ne (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support) :
    A.near ≠ B.near := by
  intro h
  exact List.disjoint_left.mp hd A.walk.start_mem_support (by simpa only [h] using B.walk.start_mem_support)

lemma far_ne_center (A : Arm G x) : A.far ≠ x := by
  intro h
  apply A.avoids
  simpa only [h] using A.walk.end_mem_support

lemma star_not_mem (A : Arm G x) (v : V) : s(x,v) ∉ A.walk.edgeSet := by
  intro he
  exact A.avoids (Walk.mem_support_iff_exists_mem_edges.mpr
    (Or.inr ⟨s(x,v), he, by simp⟩))

def orient (A : Arm G x) (active : Prop) (h : active → G.Adj x A.far) : Arm G x :=
  if ha : active then A.flip (h ha) else A

@[simp] lemma orient_edges (A : Arm G x) (active : Prop) (h : active → G.Adj x A.far) :
    (A.orient active h).walk.edgeSet = A.walk.edgeSet := by
  by_cases ha : active
  · exact (congrArg (fun B : Arm G x => B.walk.edgeSet)
      (show A.orient active h = A.flip (h ha) from dite_eq_left ha)).trans (A.flip_edges _)
  · exact congrArg (fun B : Arm G x => B.walk.edgeSet)
      (show A.orient active h = A from dite_eq_right ha)

@[simp] lemma orient_near (A : Arm G x) (active : Prop) (h : active → G.Adj x A.far) :
    (A.orient active h).near = if active then A.far else A.near := by
  by_cases ha : active <;> simp [orient, flip, ha]

@[simp] lemma mem_orient_support (A : Arm G x) (active : Prop)
    (h : active → G.Adj x A.far) (v : V) :
    v ∈ (A.orient active h).walk.support ↔ v ∈ A.walk.support := by
  by_cases ha : active
  · exact (congrArg (fun B : Arm G x => v ∈ B.walk.support)
      (show A.orient active h = A.flip (h ha) from dite_eq_left ha)).to_iff.trans
        (A.mem_flip_support _ v)
  · exact (congrArg (fun B : Arm G x => v ∈ B.walk.support)
      (show A.orient active h = A from dite_eq_right ha)).to_iff

lemma orient_disjoint (A B : Arm G x) (p q : Prop)
    (ha : p → G.Adj x A.far) (hb : q → G.Adj x B.far)
    (hd : A.walk.support.Disjoint B.walk.support) :
    (A.orient p ha).walk.support.Disjoint (B.orient q hb).walk.support := by
  rw [List.disjoint_left]
  intro v hv hw
  exact List.disjoint_left.mp hd ((A.mem_orient_support p ha v).mp hv)
    ((B.mem_orient_support q hb v).mp hw)

end Arm

inductive Frame {V : Type cycleUniverse15} (G : SimpleGraph V) (x : V) where
  | away (p : PathPiece G) (avoid : x ∉ p.walk.support)
  | tip (A : Arm G x)
  | through (A B : Arm G x) (disjoint : A.walk.support.Disjoint B.walk.support)

namespace Frame
variable {V : Type cycleUniverse16} {G : SimpleGraph V} {x : V}

def path : Frame G x → PathPiece G
  | .away p _ => p
  | .tip A => A.tip
  | .through A B hd => A.join B hd

def Port : Frame G x → Type
  | .away _ _ => Bool
  | .tip _ => Unit
  | .through _ _ _ => Bool

def endpoint : (F : Frame G x) → F.Port → V
  | .away p _, false => p.start
  | .away p _, true => p.finish
  | .tip A, _ => A.far
  | .through A _ _, false => A.far
  | .through _ B _, true => B.far

def exit : (F : Frame G x) → F.Port → Option V
  | .away _ _, _ => none
  | .tip _, _ => none
  | .through A _ _, false => some A.near
  | .through _ B _, true => some B.near

def inserted (F : Frame G x) (active : F.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ e = s(x, F.endpoint p)}

def removed (F : Frame G x) (active : F.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ ∃ v, F.exit p = some v ∧ e = s(x,v)}

lemma endpoint_ne_center (F : Frame G x) (p : F.Port) : F.endpoint p ≠ x := by
  cases F with
  | away P hx =>
    cases p
    · change P.start ≠ x
      intro h; apply hx; simpa only [← h] using P.walk.start_mem_support
    · change P.finish ≠ x
      intro h; apply hx; simpa only [← h] using P.walk.end_mem_support
  | tip A => exact A.far_ne_center
  | through A B hd => cases p <;> exact Arm.far_ne_center _

lemma port_iff_endpoint (F : Frame G x) (v : V) :
    (∃ p : F.Port, F.endpoint p = v) ↔
      (F.path.start = v ∨ F.path.finish = v) ∧ v ≠ x := by
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨?_, (F.endpoint_ne_center p)⟩
    cases F with
    | away P hx => cases p <;> simp [endpoint, path]
    | tip A => exact Or.inr rfl
    | through A B hd => cases p <;> simp [endpoint, path, Arm.join]
  · rintro ⟨he, hx⟩
    cases F with
    | away P hp =>
      rcases he with he | he
      · exact ⟨false, he⟩
      · exact ⟨true, he⟩
    | tip A =>
      rcases he with he | he
      · exact (hx he.symm).elim
      · exact ⟨(), he⟩
    | through A B hd =>
      rcases he with he | he
      · exact ⟨false, he⟩
      · exact ⟨true, he⟩

lemma exit_edge (F : Frame G x) (p : F.Port) (v : V) (h : F.exit p = some v) :
    s(x,v) ∈ F.path.walk.edgeSet := by
  cases F with
  | away P hx => cases h
  | tip A => cases h
  | through A B hd =>
    cases p
    · cases h
      rw [path, Arm.join_edges]
      exact Or.inr (by simp)
    · cases h
      rw [path, Arm.join_edges]
      exact Or.inr (by simp)

@[simp] lemma removed_away (P : PathPiece G) (hx : x ∉ P.walk.support)
    (active : (Frame.away P hx).Port → Prop) :
    (Frame.away P hx).removed active = ∅ := by
  ext e; simp [removed, exit]

@[simp] lemma removed_tip (A : Arm G x) (active : (Frame.tip A).Port → Prop) :
    (Frame.tip A).removed active = ∅ := by
  ext e; simp [removed, exit]

lemma inserted_away (P : PathPiece G) (hx : x ∉ P.walk.support)
    (active : (Frame.away P hx).Port → Prop) :
    (Frame.away P hx).inserted active =
      (if active false then {s(x,P.start)} else ∅) ∪
      (if active true then {s(x,P.finish)} else ∅) := by
  ext e
  by_cases h0 : active false <;> by_cases h1 : active true <;>
    simp [inserted, endpoint, Port, Bool.exists_bool, h0, h1, or_comm]

lemma inserted_tip (A : Arm G x) (active : (Frame.tip A).Port → Prop) :
    (Frame.tip A).inserted active = if active () then {s(x,A.far)} else ∅ := by
  ext e
  by_cases h : active () <;> simp [inserted, endpoint, Port, h]

lemma inserted_through (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support)
    (active : (Frame.through A B hd).Port → Prop) :
    (Frame.through A B hd).inserted active =
      (if active false then {s(x,A.far)} else ∅) ∪
      (if active true then {s(x,B.far)} else ∅) := by
  ext e
  by_cases h0 : active false <;> by_cases h1 : active true <;>
    simp [inserted, endpoint, Port, Bool.exists_bool, h0, h1, or_comm]

lemma removed_through (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support)
    (active : (Frame.through A B hd).Port → Prop) :
    (Frame.through A B hd).removed active =
      (if active false then {s(x,A.near)} else ∅) ∪
      (if active true then {s(x,B.near)} else ∅) := by
  ext e
  by_cases h0 : active false <;> by_cases h1 : active true <;>
    simp [removed, exit, Port, Bool.exists_bool, h0, h1, or_comm]

end Frame

lemma replace_two_attachments {E : Type cycleUniverse17} (B : Set E) (e f a b : E)
    (he : e ∉ B) (hf : f ∉ B) (hne : e ≠ f) (p q : Prop) [Decidable p] [Decidable q] :
    ((B ∪ {e,f}) \ ((if p then {e} else ∅) ∪ (if q then {f} else ∅))) ∪
      ((if p then {a} else ∅) ∪ (if q then {b} else ∅)) =
      B ∪ {if p then a else e, if q then b else f} := by
  classical
  ext z
  by_cases hp : p <;> by_cases hq : q <;>
    simp only [hp, hq, ↓reduceIte, Set.mem_union, Set.mem_sdiff, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_empty_iff_false] <;> aesop

namespace Frame
variable {V : Type cycleUniverse18} {G : SimpleGraph V} {x : V}

lemma modify_through (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support)
    (active : (Frame.through A B hd).Port → Prop)
    (hadj : ∀ p, active p → G.Adj x ((Frame.through A B hd).endpoint p)) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      ((Frame.through A B hd).path.walk.edgeSet \ (Frame.through A B hd).removed active) ∪
        (Frame.through A B hd).inserted active := by
  have ha : active false → G.Adj x A.far := hadj false
  have hb : active true → G.Adj x B.far := hadj true
  let A' := A.orient (active false) ha
  let B' := B.orient (active true) hb
  have hd' : A'.walk.support.Disjoint B'.walk.support :=
    A.orient_disjoint B _ _ _ _ hd
  refine ⟨Piece.ofPath (A'.join B' hd'), ?_⟩
  have he : s(x,A.near) ∉ A.walk.edgeSet ∪ B.walk.edgeSet := by
    rintro (he | he)
    · exact A.star_not_mem _ he
    · exact B.star_not_mem _ he
  have hf : s(x,B.near) ∉ A.walk.edgeSet ∪ B.walk.edgeSet := by
    rintro (he | he)
    · exact A.star_not_mem _ he
    · exact B.star_not_mem _ he
  have hne : s(x,A.near) ≠ s(x,B.near) := fun h => A.near_ne B hd (star_inj.mp h)
  change (A'.join B' hd').walk.edgeSet = _
  rw [inserted_through, removed_through]
  change (A'.join B' hd').walk.edgeSet = ((A.join B hd).walk.edgeSet \ _) ∪ _
  rw [Arm.join_edges, Arm.join_edges]
  dsimp only [A', B']
  simp only [Arm.orient_edges, Arm.orient_near]
  have hh := (replace_two_attachments _ _ _ s(x,A.far) s(x,B.far) he hf hne
    (active false) (active true)).symm
  by_cases h0 : active false <;> by_cases h1 : active true
  · simpa [h0, h1] using hh
  · simpa [h0, h1] using hh
  · simpa [h0, h1] using hh
  · simp [h0, h1]

lemma modify_tip (A : Arm G x) (active : (Frame.tip A).Port → Prop)
    (hadj : ∀ p, active p → G.Adj x ((Frame.tip A).endpoint p))
    (hnew : ∀ p, active p → s(x,(Frame.tip A).endpoint p) ∉
      (Frame.tip A).path.walk.edgeSet) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      ((Frame.tip A).path.walk.edgeSet \ (Frame.tip A).removed active) ∪
        (Frame.tip A).inserted active := by
  rw [removed_tip, inserted_tip, Set.sdiff_empty]
  by_cases ha : active ()
  · have haG : G.Adj x A.far := hadj () ha
    have he : s(A.far,x) ∉ A.tip.walk.edges := by
      intro he
      exact hnew () ha (Sym2.eq_swap ▸ he)
    let c : G.Walk A.far A.far := Walk.cons haG.symm A.tip.walk
    have hc : c.IsCycle := Path.cons_isCycle ⟨A.tip.walk,A.tip.isPath⟩ _ he
    refine ⟨Piece.ofCycle c hc, ?_⟩
    change c.edgeSet = _
    dsimp only [c, Arm.tip, path]
    simp only [Walk.edgeSet_cons, ha, ↓reduceIte]
    rw [Sym2.eq_swap]
    ext e
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
    tauto
  · refine ⟨Piece.ofPath A.tip, ?_⟩
    simp [Piece.ofPath, path, ha]

lemma modify_away (P : PathPiece G) (hx : x ∉ P.walk.support)
    (active : (Frame.away P hx).Port → Prop)
    (hadj : ∀ p, active p → G.Adj x ((Frame.away P hx).endpoint p)) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      ((Frame.away P hx).path.walk.edgeSet \ (Frame.away P hx).removed active) ∪
        (Frame.away P hx).inserted active := by
  rw [removed_away, inserted_away, Set.sdiff_empty]
  change ∃ Q : Piece G, Q.walk.edgeSet = P.walk.edgeSet ∪ _
  by_cases h0 : active false
  · have h0G : G.Adj x P.start := hadj false h0
    let q : G.Walk x P.finish := Walk.cons h0G P.walk
    have hq : q.IsPath := P.isPath.cons hx
    by_cases h1 : active true
    · have he : s(P.finish,x) ∉ q.edges := by
        intro he
        have hh := hq.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
        have hp := P.positive
        simp only [q, Walk.length_cons] at hh
        omega
      have h1G : G.Adj x P.finish := hadj true h1
      let c : G.Walk P.finish P.finish := Walk.cons h1G.symm q
      have hc : c.IsCycle := Path.cons_isCycle ⟨q,hq⟩ _ he
      refine ⟨Piece.ofCycle c hc, ?_⟩
      change c.edgeSet = _
      simp only [c, q, Walk.edgeSet_cons, h0, h1, ↓reduceIte]
      rw [Sym2.eq_swap]
      ext e
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
    · let Q : PathPiece G := ⟨x, P.finish, q, hq, by simp [q]⟩
      refine ⟨Piece.ofPath Q, ?_⟩
      change q.edgeSet = _
      simp only [q, Walk.edgeSet_cons, h0, h1, ↓reduceIte, Set.union_empty]
      ext e
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
  · by_cases h1 : active true
    · have h1G : G.Adj x P.finish := hadj true h1
      let q : G.Walk x P.start := Walk.cons h1G P.walk.reverse
      have hq : q.IsPath := P.isPath.reverse.cons (by simpa using hx)
      let Q : PathPiece G := ⟨x, P.start, q, hq, by simp [q]⟩
      refine ⟨Piece.ofPath Q, ?_⟩
      change q.edgeSet = _
      simp only [q, Walk.edgeSet_cons, Walk.edgeSet_reverse, h0, h1, ↓reduceIte,
        Set.empty_union]
      ext e
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
    · refine ⟨Piece.ofPath P, ?_⟩
      simp [Piece.ofPath, h0, h1]

theorem modify (F : Frame G x) (active : F.Port → Prop)
    (hadj : ∀ p, active p → G.Adj x (F.endpoint p))
    (hnew : ∀ p, active p → F.exit p = none → s(x,F.endpoint p) ∉ F.path.walk.edgeSet) :
    ∃ Q : Piece G, Q.walk.edgeSet = (F.path.walk.edgeSet \ F.removed active) ∪
      F.inserted active := by
  cases F with
  | away P hx => exact modify_away P hx active hadj
  | through A B hd => exact modify_through A B hd active hadj
  | tip A => exact modify_tip A active hadj (fun p hp => hnew p hp rfl)

end Frame

theorem rewire_partition {E : Type cycleUniverse19} {I : Type cycleUniverse20} (old remove add : I → Set E) (fresh : Set E)
    (hsub : ∀ i, remove i ⊆ old i)
    (hold : Pairwise fun i j => Disjoint (old i) (old j))
    (hadd : Pairwise fun i j => Disjoint (add i) (add j))
    (hfresh : Disjoint fresh (⋃ i, old i))
    (hbalance : (⋃ i, add i) = (⋃ i, remove i) ∪ fresh) :
    Pairwise (fun i j => Disjoint ((old i \ remove i) ∪ add i)
      ((old j \ remove j) ∪ add j)) ∧
    (⋃ i, ((old i \ remove i) ∪ add i)) = (⋃ i, old i) ∪ fresh := by
  have hcross : ∀ i j, Disjoint (old i \ remove i) (add j) := by
    intro i j
    apply Set.disjoint_left.mpr
    rintro e ⟨hei, hnot⟩ hej
    have hh : e ∈ (⋃ l, remove l) ∪ fresh := by
      rw [← hbalance]
      exact Set.mem_iUnion.mpr ⟨j, hej⟩
    rcases hh with hh | hh
    · obtain ⟨l, hel⟩ := Set.mem_iUnion.mp hh
      by_cases hil : i = l
      · subst l; exact hnot hel
      · exact Set.disjoint_left.mp (hold hil) hei (hsub l hel)
    · exact Set.disjoint_left.mp hfresh hh (Set.mem_iUnion.mpr ⟨i, hei⟩)
  constructor
  · intro i j hij
    exact Disjoint.union_left
      (Disjoint.union_right ((hold hij).mono Set.sdiff_subset Set.sdiff_subset) (hcross i j))
      (Disjoint.union_right (hcross j i).symm (hadd hij))
  · ext e
    constructor
    · intro he
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
      rcases hi with hi | hi
      · exact Or.inl (Set.mem_iUnion.mpr ⟨i, hi.1⟩)
      · have hh : e ∈ (⋃ l, remove l) ∪ fresh := by
          rw [← hbalance]
          exact Set.mem_iUnion.mpr ⟨i, hi⟩
        rcases hh with hh | hh
        · obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hh
          exact Or.inl (Set.mem_iUnion.mpr ⟨l, hsub l hl⟩)
        · exact Or.inr hh
    · rintro (he | he)
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
        by_cases hr : e ∈ remove i
        · have hh : e ∈ ⋃ l, add l := by
            rw [hbalance]
            exact Or.inl (Set.mem_iUnion.mpr ⟨i, hr⟩)
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hh
          exact Set.mem_iUnion.mpr ⟨j, Or.inr hj⟩
        · exact Set.mem_iUnion.mpr ⟨i, Or.inl ⟨hi, hr⟩⟩
      · have hh : e ∈ ⋃ l, add l := by rw [hbalance]; exact Or.inr he
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hh
        exact Set.mem_iUnion.mpr ⟨i, Or.inr hi⟩

inductive Centered {V : Type cycleUniverse21} (G : SimpleGraph V) (x : V) where
  | path (F : Frame G x)
  | cycle {v : V} (c : G.Walk v v) (hc : c.IsCycle)

namespace Centered
variable {V : Type cycleUniverse22} {G : SimpleGraph V} {x : V}

def piece : Centered G x → Piece G
  | .path F => .ofPath F.path
  | .cycle c hc => .ofCycle c hc

def Port : Centered G x → Type
  | .path F => F.Port
  | .cycle _ _ => Empty

def endpoint : (K : Centered G x) → K.Port → V
  | .path F, p => F.endpoint p
  | .cycle _ _, p => nomatch p

def exit : (K : Centered G x) → K.Port → Option V
  | .path F, p => F.exit p
  | .cycle _ _, p => nomatch p

def inserted (K : Centered G x) (active : K.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ e = s(x,K.endpoint p)}

def removed (K : Centered G x) (active : K.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ ∃ v, K.exit p = some v ∧ e = s(x,v)}

lemma exit_edge (K : Centered G x) (p : K.Port) (v : V) (h : K.exit p = some v) :
    s(x,v) ∈ K.piece.walk.edgeSet := by
  cases K with
  | path F => exact F.exit_edge p v h
  | cycle c hc => exact p.elim

lemma exit_adj (K : Centered G x) (p : K.Port) (v : V) (h : K.exit p = some v) :
    G.Adj x v := by
  exact G.mem_edgeSet.mp (K.piece.walk.edges_subset_edgeSet (K.exit_edge p v h))

lemma exit_none_all (K : Centered G x) (p : K.Port) (h : K.exit p = none) :
    ∀ q, K.exit q = none := by
  cases K with
  | cycle c hc => exact p.elim
  | path F =>
    cases F with
    | away P hx => exact fun _ => rfl
    | tip A => exact fun _ => rfl
    | through A B hd => cases p <;> cases h

lemma removed_subset (K : Centered G x) (active : K.Port → Prop) :
    K.removed active ⊆ K.piece.walk.edgeSet := by
  rintro e ⟨p, hp, v, hv, rfl⟩
  exact K.exit_edge p v hv

lemma modify (K : Centered G x) (active : K.Port → Prop)
    (hadj : ∀ p, active p → G.Adj x (K.endpoint p))
    (hnew : ∀ p, active p → K.exit p = none →
      s(x,K.endpoint p) ∉ K.piece.walk.edgeSet) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      (K.piece.walk.edgeSet \ K.removed active) ∪ K.inserted active := by
  cases K with
  | path F => exact F.modify active hadj hnew
  | cycle c hc =>
    refine ⟨.ofCycle c hc, ?_⟩
    have hr : (Centered.cycle c hc).removed active = ∅ := by
      ext e; simp only [removed, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      exact ⟨fun ⟨p, _⟩ => p.elim, False.elim⟩
    have hi : (Centered.cycle c hc).inserted active = ∅ := by
      ext e; simp only [inserted, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      exact ⟨fun ⟨p, _⟩ => p.elim, False.elim⟩
    simp only [hr, hi, Set.sdiff_empty, Set.union_empty]
    rfl

end Centered

theorem restore_selected {V : Type cycleUniverse23} {I : Type cycleUniverse24} (G : SimpleGraph V) (x : V)
    (K : I → Centered G x) (S : Set V)
    (hS : ∀ v ∈ S, G.Adj x v)
    (hold : Pairwise fun i j => Disjoint (K i).piece.walk.edgeSet (K j).piece.walk.edgeSet)
    (hfresh : Disjoint {e | ∃ v ∈ S, e = s(x,v)} (⋃ i, (K i).piece.walk.edgeSet))
    (selected : Set (Σ i, (K i).Port))
    (hinj : Set.InjOn (fun z : Σ i, (K i).Port => (K z.1).endpoint z.2) selected)
    (hcov : ∀ v, G.Adj x v → ∃ z ∈ selected, (K z.1).endpoint z.2 = v) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) =
        (⋃ i, (K i).piece.walk.edgeSet) ∪ {e | ∃ v ∈ S, e = s(x,v)} := by
  let R : V → V → Prop := fun a b => ∃ z ∈ selected,
    (K z.1).endpoint z.2 = a ∧ (K z.1).exit z.2 = some b
  let active : (i : I) → (K i).Port → Prop := fun i p =>
    (⟨i,p⟩ : Σ j, (K j).Port) ∈ selected ∧ StarActive S R ((K i).endpoint p)
  have hactive_adj : ∀ v, StarActive S R v → G.Adj x v := by
    intro v hv
    exact starActive_subset (T := {v | G.Adj x v}) hS
      (by rintro a b ⟨z, _, _, hz⟩; exact (K z.1).exit_adj z.2 b hz) hv
  have hbalance : (⋃ i, (K i).inserted (active i)) =
      (⋃ i, (K i).removed (active i)) ∪ {e | ∃ v ∈ S, e = s(x,v)} := by
    ext e
    constructor
    · intro he
      obtain ⟨i, p, hp, rfl⟩ := Set.mem_iUnion.mp he
      rcases (starActive_iff.mp hp.2) with hs | ⟨w, hw, z, hz, hzw, hzv⟩
      · exact Or.inr ⟨_, hs, rfl⟩
      · exact Or.inl (Set.mem_iUnion.mpr ⟨z.1, z.2, ⟨hz, hzw.symm ▸ hw⟩,
          _, hzv, rfl⟩)
    · rintro (he | ⟨v, hv, rfl⟩)
      · obtain ⟨i, p, hp, v, hpv, rfl⟩ := Set.mem_iUnion.mp he
        have hv : StarActive S R v := starActive_step hp.2 ⟨⟨i,p⟩, hp.1, rfl, hpv⟩
        obtain ⟨z, hz, hzv⟩ := hcov v (hactive_adj v hv)
        exact Set.mem_iUnion.mpr ⟨z.1, z.2, ⟨hz, hzv.symm ▸ hv⟩, congrArg (s(x,·)) hzv.symm⟩
      · obtain ⟨z, hz, hzv⟩ := hcov v (hS v hv)
        exact Set.mem_iUnion.mpr ⟨z.1, z.2, ⟨hz, hzv.symm ▸ starActive_source hv⟩,
          congrArg (s(x,·)) hzv.symm⟩
  have hadd : Pairwise fun i j =>
      Disjoint ((K i).inserted (active i)) ((K j).inserted (active j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro e ⟨p, hp, he⟩ ⟨q, hq, hf⟩
    have h : (⟨i,p⟩ : Σ l, (K l).Port) = ⟨j,q⟩ :=
      hinj hp.1 hq.1 (star_inj.mp (he.symm.trans hf))
    exact hij (congrArg Sigma.fst h)
  have hnew : ∀ i p, active i p → (K i).exit p = none →
      s(x,(K i).endpoint p) ∉ (K i).piece.walk.edgeSet := by
    intro i p hp hn he
    have ha : s(x,(K i).endpoint p) ∈ ⋃ j, (K j).inserted (active j) :=
      Set.mem_iUnion.mpr ⟨i, p, hp, rfl⟩
    rw [hbalance] at ha
    rcases ha with ha | ha
    · obtain ⟨j, q, hq, v, hqv, hev⟩ := Set.mem_iUnion.mp ha
      have hej : s(x,(K i).endpoint p) ∈ (K j).piece.walk.edgeSet :=
        hev ▸ (K j).exit_edge q v hqv
      have hij : i = j := by
        by_contra h; exact Set.disjoint_left.mp (hold h) he hej
      subst j
      rw [(K i).exit_none_all p hn q] at hqv
      cases hqv
    · exact Set.disjoint_left.mp hfresh ha (Set.mem_iUnion.mpr ⟨i, he⟩)
  choose Q hQ using fun i => (K i).modify (active i)
    (fun p hp => hactive_adj _ hp.2) (hnew i)
  have hh := rewire_partition (fun i => (K i).piece.walk.edgeSet)
    (fun i => (K i).removed (active i)) (fun i => (K i).inserted (active i))
    {e | ∃ v ∈ S, e = s(x,v)} (fun i => (K i).removed_subset _) hold hadd hfresh hbalance
  refine ⟨Q, ?_, ?_⟩
  · simpa only [hQ] using hh.1
  · simpa only [hQ] using hh.2

theorem restore_star {V : Type cycleUniverse25} {I : Type cycleUniverse26} (G : SimpleGraph V) (x : V)
    (K : I → Centered G x) (S : Set V)
    (hS : ∀ v ∈ S, G.Adj x v)
    (hold : Pairwise fun i j => Disjoint (K i).piece.walk.edgeSet (K j).piece.walk.edgeSet)
    (hfresh : Disjoint {e | ∃ v ∈ S, e = s(x,v)} (⋃ i, (K i).piece.walk.edgeSet))
    (hcov : ∀ v, G.Adj x v → ∃ i p, (K i).endpoint p = v) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) =
        (⋃ i, (K i).piece.walk.edgeSet) ∪ {e | ∃ v ∈ S, e = s(x,v)} := by
  let T := {v // G.Adj x v}
  have hh : ∀ v : T, ∃ z : Σ i, (K i).Port, (K z.1).endpoint z.2 = v.val := by
    intro v
    obtain ⟨i,p,h⟩ := hcov v.val v.property
    exact ⟨⟨i,p⟩,h⟩
  choose f hf using hh
  apply restore_selected G x K S hS hold hfresh (Set.range f)
  · rintro z ⟨v,rfl⟩ w ⟨u,rfl⟩ he
    have hvu : v = u := Subtype.ext ((hf v).symm.trans (he.trans (hf u)))
    exact congrArg f hvu
  · intro v hv
    exact ⟨f ⟨v,hv⟩, ⟨⟨v,hv⟩, rfl⟩, hf ⟨v,hv⟩⟩

namespace Arm
variable {V : Type cycleUniverse27} {G : SimpleGraph V} {x b : V}

def fromWalk (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) : Arm G x :=
  match w with
  | .nil => False.elim (hn .nil)
  | @Walk.cons _ _ _ y _ h q =>
    ⟨y, b, h, q, (Walk.cons_isPath_iff h q).mp hp |>.1,
      (Walk.cons_isPath_iff h q).mp hp |>.2⟩

@[simp] lemma fromWalk_far (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) :
    (fromWalk w hp hn).far = b := by
  cases w with
  | nil => exact (hn .nil).elim
  | cons h q => rfl

@[simp] lemma fromWalk_support (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) :
    (fromWalk w hp hn).walk.support = w.support.tail := by
  cases w with
  | nil => exact (hn .nil).elim
  | cons h q => rfl

@[simp] lemma fromWalk_tip_edges (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) :
    (fromWalk w hp hn).tip.walk.edgeSet = w.edgeSet := by
  cases w with
  | nil => exact (hn .nil).elim
  | cons h q => rfl
end Arm

lemma PathPiece.exists_frame {V : Type cycleUniverse28} {G : SimpleGraph V} (P : PathPiece G) (x : V) :
    ∃ F : Frame G x, F.path.walk.edgeSet = P.walk.edgeSet ∧
      ∀ v, (F.path.start = v ∨ F.path.finish = v) ↔ (P.start = v ∨ P.finish = v) := by
  classical
  by_cases hx : x ∈ P.walk.support
  · obtain ⟨q,r,hq,hr,hqr⟩ := P.isPath.mem_support_iff_exists_append.mp hx
    have hp : (q.append r).IsPath := hqr ▸ P.isPath
    by_cases hqn : q.Nil
    · have hx : P.start = x := hqn.eq
      have hrn : ¬r.Nil := by
        intro hn; exact P.ends_ne (hx.trans hn.eq)
      let A := Arm.fromWalk r hr hrn
      refine ⟨.tip A, ?_, ?_⟩
      · change A.tip.walk.edgeSet = P.walk.edgeSet
        rw [Arm.fromWalk_tip_edges]
        rw [hqr, Walk.edgeSet_append]
        simp [Walk.edgeSet, Walk.edges_eq_nil.mpr hqn]
      · intro v
        change (x = v ∨ A.far = v) ↔ _
        simp only [A, Arm.fromWalk_far, hx]
    · by_cases hrn : r.Nil
      · have hx : x = P.finish := hrn.eq
        have hqnr : ¬q.reverse.Nil := by simpa using hqn
        let A := Arm.fromWalk q.reverse hq.reverse hqnr
        refine ⟨.tip A, ?_, ?_⟩
        · change A.tip.walk.edgeSet = P.walk.edgeSet
          rw [Arm.fromWalk_tip_edges, Walk.edgeSet_reverse]
          rw [hqr, Walk.edgeSet_append]
          simp [Walk.edgeSet, Walk.edges_eq_nil.mpr hrn]
        · intro v
          change (x = v ∨ A.far = v) ↔ _
          simp only [A, Arm.fromWalk_far, hx, or_comm]
      · have hqnr : ¬q.reverse.Nil := by simpa using hqn
        let A := Arm.fromWalk q.reverse hq.reverse hqnr
        let B := Arm.fromWalk r hr hrn
        have hd : A.walk.support.Disjoint B.walk.support := by
          rw [Arm.fromWalk_support, Arm.fromWalk_support]
          have hd := hp.disjoint_support_of_append hrn
          rw [Walk.support_tail_of_not_nil r hrn] at hd
          apply List.disjoint_left.mpr
          intro v hv hw
          exact List.disjoint_left.mp hd
            (by simpa using (List.mem_of_mem_tail hv : v ∈ q.reverse.support)) hw
        refine ⟨.through A B hd, ?_, ?_⟩
        · change ((Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)).edgeSet = _
          rw [Walk.edgeSet_append, Walk.edgeSet_reverse]
          change A.tip.walk.edgeSet ∪ B.tip.walk.edgeSet = _
          rw [Arm.fromWalk_tip_edges, Arm.fromWalk_tip_edges, Walk.edgeSet_reverse,
            hqr, Walk.edgeSet_append]
        · intro v
          change (A.far = v ∨ B.far = v) ↔ _
          simp only [A, B, Arm.fromWalk_far]
  · exact ⟨.away P hx, rfl, fun _ => Iff.rfl⟩

namespace Piece
variable {V : Type cycleUniverse29} {G H : SimpleGraph V}

lemma isTrail (P : Piece G) : P.walk.IsTrail := by
  rcases P.simple with hp | ⟨h,hc⟩
  · exact hp.1.isTrail
  · exact (P.walk.isTrail_copy rfl h).mp hc.isTrail

def mapLe (h : H ≤ G) (P : Piece H) : Piece G := by
  rcases P with ⟨a,b,w,hs⟩
  refine ⟨a,b,w.mapLe h, ?_⟩
  rcases hs with hp | ⟨hb,hc⟩
  · exact Or.inl ⟨hp.1.mapLe h, by simpa using hp.2⟩
  · subst b
    exact Or.inr ⟨rfl, by simpa using hc.mapLe h⟩

@[simp] lemma mapLe_edges (h : H ≤ G) (P : Piece H) :
    (P.mapLe h).walk.edgeSet = P.walk.edgeSet := by
  cases P
  exact Walk.edgeSet_mapLe_eq_edgeSet _ _

@[simp] lemma mapLe_start (h : H ≤ G) (P : Piece H) : (P.mapLe h).start = P.start := by
  cases P; rfl
@[simp] lemma mapLe_finish (h : H ≤ G) (P : Piece H) : (P.mapLe h).finish = P.finish := by
  cases P; rfl

lemma exists_centered (P : Piece G) (x : V) :
    ∃ K : Centered G x, K.piece.walk.edgeSet = P.walk.edgeSet ∧
      ∀ v, P.start ≠ P.finish → (P.start = v ∨ P.finish = v) → v ≠ x →
        ∃ p, K.endpoint p = v := by
  rcases P with ⟨a,b,w,hs⟩
  rcases hs with hp | ⟨hb,hc⟩
  · let Q : PathPiece G := ⟨a,b,w,hp.1,hp.2⟩
    obtain ⟨F,he,hv⟩ := Q.exists_frame x
    refine ⟨.path F, he, ?_⟩
    intro v _ he hx
    exact (F.port_iff_endpoint v).mpr ⟨(hv v).mpr he, hx⟩
  · subst b
    refine ⟨.cycle w (by simpa using hc), rfl, ?_⟩
    exact fun _ hn => (hn rfl).elim
end Piece

theorem trail_partition_degree_sum {V : Type cycleUniverse30} {I : Type cycleUniverse31} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    G.degree v = ∑ i, (p i).edges.countP (fun e => decide (v ∈ e)) := by
  classical
  have he : G.edgeFinset = Finset.univ.biUnion (fun i => (p i).edges.toFinset) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, ← hc, Set.mem_iUnion,
      Finset.mem_biUnion, Finset.mem_univ, List.mem_toFinset, true_and,
      SimpleGraph.Walk.mem_edgeSet]
  rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter, he,
    Finset.filter_biUnion]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    have hfilter : ((p i).edges.filter (fun e => decide (v ∈ e))).toFinset =
        ((p i).edges.toFinset.filter (fun e => v ∈ e)) := by
      simp [List.toFinset_filter]
    rw [← hfilter, List.toFinset_card_of_nodup ((ht i).edges_nodup.filter _),
      List.countP_eq_length_filter]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact Set.disjoint_left.mp (hd hij)
      (by simpa using (Finset.mem_filter.mp hei).1)
      (by simpa using (Finset.mem_filter.mp hej).1)

theorem trail_partition_even_degree_iff {V : Type cycleUniverse32} {I : Type cycleUniverse33} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    Even (G.degree v) ↔ Even (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card := by
  classical
  rw [trail_partition_degree_sum G p ht hd hc v, Finset.even_sum_iff_even_card_odd]
  have he : (Finset.univ.filter (fun i => Odd ((p i).edges.countP
      (fun e => decide (v ∈ e))))) = (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ← Nat.not_even_iff_odd, (ht i).even_countP_edges_iff]
    tauto
  rw [he]

lemma endpoint_of_odd {V : Type cycleUniverse34} {I : Type cycleUniverse35} [Fintype V] [Fintype I]
    (H : SimpleGraph V) (P : I → Piece H)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = H.edgeSet)
    (v : V) (hv : Odd (H.degree v)) :
    ∃ i, (P i).start ≠ (P i).finish ∧ ((P i).start = v ∨ (P i).finish = v) := by
  classical
  have ho := (trail_partition_even_degree_iff H (fun i => (P i).walk)
    (fun i => (P i).isTrail) hd hc v).not.mp (Nat.not_even_iff_odd.mpr hv)
  have hp : 0 < (Finset.univ.filter
      (fun i => (P i).start ≠ (P i).finish ∧ (v = (P i).start ∨ v = (P i).finish))).card := by
    by_contra hn
    have hz : (Finset.univ.filter
      (fun i => (P i).start ≠ (P i).finish ∧ (v = (P i).start ∨ v = (P i).finish))).card = 0 := by omega
    exact ho (hz ▸ ⟨0, rfl⟩)
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hp
  exact ⟨i, (Finset.mem_filter.mp hi).2.1, by
    simpa only [eq_comm] using (Finset.mem_filter.mp hi).2.2⟩

theorem restore_partition {V : Type cycleUniverse36} {I : Type cycleUniverse37} [Fintype V] [Fintype I]
    (G H : SimpleGraph V) (hHG : H ≤ G) (x : V) (S : Set V)
    (hS : ∀ v ∈ S, G.Adj x v)
    (hedges : G.edgeSet = H.edgeSet ∪ {e | ∃ v ∈ S, e = s(x,v)})
    (hfresh : Disjoint {e | ∃ v ∈ S, e = s(x,v)} H.edgeSet)
    (hodd : ∀ v, G.Adj x v → Odd (H.degree v))
    (P : I → Piece H)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = H.edgeSet) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) = G.edgeSet := by
  choose K hk hv using fun i => ((P i).mapLe hHG).exists_centered x
  have he : ∀ i, (K i).piece.walk.edgeSet = (P i).walk.edgeSet := by
    intro i; exact (hk i).trans ((P i).mapLe_edges hHG)
  have hKC : (⋃ i, (K i).piece.walk.edgeSet) = H.edgeSet := by simpa only [he] using hc
  obtain ⟨Q,hQ,hQC⟩ := restore_star G x K S hS
    (by simpa only [he] using hd) (by rwa [hKC]) (by
      intro v hxv
      obtain ⟨i, hi, hiv⟩ := endpoint_of_odd H P hd hc v (hodd v hxv)
      obtain ⟨p,hp⟩ := hv i v (by simpa using hi) (by simpa using hiv) hxv.ne.symm
      exact ⟨i,p,hp⟩)
  exact ⟨Q,hQ,by simpa only [hKC, ← hedges] using hQC⟩

def activeOrder {V : Type cycleUniverse38} [Fintype V] (G : SimpleGraph V) : ℕ :=
  G.support.toFinset.card

lemma activeOrder_mono {V : Type cycleUniverse39} [Fintype V] {G H : SimpleGraph V} (h : H ≤ G) :
    activeOrder H ≤ activeOrder G := by
  apply Finset.card_le_card
  intro v hv
  exact Set.mem_toFinset.mpr (SimpleGraph.support_mono h (Set.mem_toFinset.mp hv))

def HasPartition {V : Type cycleUniverse40} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (P : Fin k → Piece G),
    (Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
    (⋃ i, (P i).walk.edgeSet) = G.edgeSet ∧ 2 * k ≤ activeOrder G

def evenStarVertices {V : Type cycleUniverse41} [Fintype V] (G : SimpleGraph V) (x : V) : Set V :=
  {y | G.Adj x y ∧ Even (G.degree y)}

def evenStarEdges {V : Type cycleUniverse42} [Fintype V] (G : SimpleGraph V) (x : V) : Set (Sym2 V) :=
  {e | ∃ y ∈ evenStarVertices G x, e = s(x,y)}

def deleteEvenStar {V : Type cycleUniverse43} [Fintype V] (G : SimpleGraph V) (x : V) : SimpleGraph V :=
  G.deleteEdges (evenStarEdges G x)

lemma evenStar_subset {V : Type cycleUniverse44} [Fintype V] (G : SimpleGraph V) (x : V) :
    evenStarEdges G x ⊆ G.edgeSet := by
  rintro e ⟨y,hy,rfl⟩; exact hy.1

lemma deleteEvenStar_neighbor_even {V : Type cycleUniverse45} [Fintype V] (G : SimpleGraph V)
    (x v : V) (hxv : G.Adj x v) (he : Even (G.degree v)) :
    (deleteEvenStar G x).neighborFinset v = (G.neighborFinset v).erase x := by
  classical
  ext w
  rw [Finset.mem_erase, (deleteEvenStar G x).mem_neighborFinset, G.mem_neighborFinset]
  rw [deleteEvenStar, SimpleGraph.deleteEdges_adj]
  simp only [evenStarEdges, Set.mem_ofPred_eq, evenStarVertices, Sym2.eq_iff]
  constructor
  · rintro ⟨hvw, hn⟩
    refine ⟨?_,hvw⟩
    intro hw; subst w
    exact hn ⟨v,⟨hxv,he⟩, Or.inr ⟨rfl,rfl⟩⟩
  · rintro ⟨hw,hvw⟩
    refine ⟨hvw, ?_⟩
    rintro ⟨y,_,h⟩
    rcases h with ⟨h,_⟩ | ⟨_,h⟩
    · exact hxv.ne h.symm
    · exact hw h

lemma deleteEvenStar_neighbor_odd {V : Type cycleUniverse46} [Fintype V] (G : SimpleGraph V)
    (x v : V) (hxv : G.Adj x v) (he : ¬Even (G.degree v)) :
    (deleteEvenStar G x).neighborFinset v = G.neighborFinset v := by
  classical
  ext w
  rw [(deleteEvenStar G x).mem_neighborFinset, G.mem_neighborFinset]
  rw [deleteEvenStar, SimpleGraph.deleteEdges_adj]
  simp only [evenStarEdges, Set.mem_ofPred_eq, evenStarVertices, Sym2.eq_iff]
  refine ⟨fun h => h.1, fun hw => ⟨hw, ?_⟩⟩
  rintro ⟨y,hy,h⟩
  rcases h with ⟨h,_⟩ | ⟨h,_⟩
  · exact hxv.ne h.symm
  · subst y; exact he hy.2

lemma deleteEvenStar_neighbor_degree {V : Type cycleUniverse47} [Fintype V] (G : SimpleGraph V)
    (x v : V) (hxv : G.Adj x v) : Odd ((deleteEvenStar G x).degree v) := by
  classical
  by_cases he : Even (G.degree v)
  · have hcard := Finset.card_erase_add_one (s := G.neighborFinset v)
      (a := x) (by simpa using hxv.symm)
    rw [← deleteEvenStar_neighbor_even G x v hxv he,
      G.card_neighborFinset_eq_degree, (deleteEvenStar G x).card_neighborFinset_eq_degree] at hcard
    obtain ⟨k,hk⟩ := he
    exact ⟨k-1, by omega⟩
  · rw [← (deleteEvenStar G x).card_neighborFinset_eq_degree v,
      deleteEvenStar_neighbor_odd G x v hxv he, G.card_neighborFinset_eq_degree]
    exact Nat.not_even_iff_odd.mp he

lemma deleteEvenStar_edges {V : Type cycleUniverse48} [Fintype V] (G : SimpleGraph V) (x : V) :
    G.edgeSet = (deleteEvenStar G x).edgeSet ∪ evenStarEdges G x := by
  rw [deleteEvenStar, SimpleGraph.edgeSet_deleteEdges,
    Set.sdiff_union_of_subset (evenStar_subset G x)]

lemma deleteEvenStar_fresh {V : Type cycleUniverse49} [Fintype V] (G : SimpleGraph V) (x : V) :
    Disjoint (evenStarEdges G x) (deleteEvenStar G x).edgeSet := by
  rw [deleteEvenStar, SimpleGraph.edgeSet_deleteEdges]
  exact Set.disjoint_sdiff_right

lemma deleteEvenStar_lt {V : Type cycleUniverse50} [Fintype V] (G : SimpleGraph V) (x y : V)
    (hxy : G.Adj x y) (he : Even (G.degree y)) :
    (deleteEvenStar G x).edgeFinset.card < G.edgeFinset.card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro e he
    exact G.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono
      (show deleteEvenStar G x ≤ G from G.deleteEdges_le _)
      ((deleteEvenStar G x).mem_edgeFinset.mp he))
  · intro h
    have hh : s(x,y) ∈ (deleteEvenStar G x).edgeFinset := h.symm ▸ G.mem_edgeFinset.mpr hxy
    have hf : s(x,y) ∈ evenStarEdges G x := ⟨y,⟨hxy,he⟩,rfl⟩
    exact Set.disjoint_left.mp (deleteEvenStar_fresh G x) hf (SimpleGraph.mem_edgeFinset.mp hh)

theorem even_vertex_step {V : Type cycleUniverse51} [Fintype V] (G : SimpleGraph V)
    (hIH : ∀ H : SimpleGraph V, H.edgeFinset.card < G.edgeFinset.card → HasPartition H)
    (hpos : ∃ y, 0 < G.degree y ∧ Even (G.degree y)) : HasPartition G := by
  classical
  obtain ⟨y,hy,he⟩ := hpos
  obtain ⟨x,hxy⟩ := (G.degree_pos_iff_exists_adj y).mp hy
  let H := deleteEvenStar G x
  obtain ⟨k,P,hd,hc,hk⟩ := hIH H (deleteEvenStar_lt G x y hxy.symm he)
  obtain ⟨Q,hQ,hQC⟩ := restore_partition G H (G.deleteEdges_le _) x
    (evenStarVertices G x) (fun _ h => h.1) (deleteEvenStar_edges G x)
    (deleteEvenStar_fresh G x) (deleteEvenStar_neighbor_degree G x) P hd hc
  exact ⟨k,Q,hQ,hQC,hk.trans (activeOrder_mono (G.deleteEdges_le _))⟩

lemma single_edge_piece {V : Type cycleUniverse52} (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ∃ P : Piece G, P.walk.edgeSet = {e} := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := he
    let P : PathPiece G := ⟨a,b,Walk.cons hab Walk.nil,
      (Walk.IsPath.nil).cons (by simpa using hab.ne), by simp⟩
    exact ⟨.ofPath P, by simp [Piece.ofPath, P]⟩

lemma partition_single_edges {V : Type cycleUniverse53} [Fintype V] (G : SimpleGraph V) :
    ∃ P : Fin G.edgeFinset.card → Piece G,
      (Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
      (⋃ i, (P i).walk.edgeSet) = G.edgeSet := by
  classical
  choose P hP using fun e : G.edgeSet => single_edge_piece G e.val e.property
  let e : G.edgeSet ≃ Fin G.edgeFinset.card := (Fintype.equivFin G.edgeSet).trans
    (finCongr (G.card_edgeSet))
  refine ⟨fun i => P (e.symm i), ?_, ?_⟩
  · intro i j hij
    rw [hP, hP]
    exact Set.disjoint_singleton.mpr (fun h => hij (e.symm.injective (Subtype.ext h)))
  · ext z
    simp only [Set.mem_iUnion,hP,Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩; exact (e.symm i).property
    · intro hz
      exact ⟨e ⟨z,hz⟩, by simp⟩

lemma matching_partition {V : Type cycleUniverse54} [Fintype V] (G : SimpleGraph V)
    (hdeg : ∀ v, G.degree v ≤ 1) : HasPartition G := by
  classical
  obtain ⟨P,hd,hc⟩ := partition_single_edges G
  refine ⟨_,P,hd,hc,?_⟩
  rw [← G.sum_degrees_support_eq_twice_card_edges]
  simpa [activeOrder] using Finset.sum_le_sum (s := G.support.toFinset)
    (f := fun v => G.degree v) (g := fun _ => 1) (fun v _ => hdeg v)

def subdivision {V : Type cycleUniverse55} (G : SimpleGraph V) (x y : V) : SimpleGraph (Option V) where
  Adj a b := match a,b with
    | some a, some b => G.Adj a b ∧ s(a,b) ≠ s(x,y)
    | none, some b => b = x ∨ b = y
    | some a, none => a = x ∨ a = y
    | none, none => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by
    intro a h
    cases a
    · exact h
    · exact G.irrefl h.1⟩

@[simp] lemma subdivision_some {V : Type cycleUniverse56} (G : SimpleGraph V) (x y a b : V) :
    (subdivision G x y).Adj (some a) (some b) ↔ G.Adj a b ∧ s(a,b) ≠ s(x,y) := Iff.rfl
@[simp] lemma subdivision_none_some {V : Type cycleUniverse57} (G : SimpleGraph V) (x y a : V) :
    (subdivision G x y).Adj none (some a) ↔ a = x ∨ a = y := Iff.rfl
@[simp] lemma subdivision_some_none {V : Type cycleUniverse58} (G : SimpleGraph V) (x y a : V) :
    (subdivision G x y).Adj (some a) none ↔ a = x ∨ a = y := Iff.rfl
def halfSubdivision {V : Type cycleUniverse60} (G : SimpleGraph V) (x y : V) : SimpleGraph (Option V) :=
  (subdivision G x y).deleteEdges {s(none,some x)}

@[simp] lemma half_some {V : Type cycleUniverse61} (G : SimpleGraph V) (x y a b : V) :
    (halfSubdivision G x y).Adj (some a) (some b) ↔ G.Adj a b ∧ s(a,b) ≠ s(x,y) := by
  rw [halfSubdivision, SimpleGraph.deleteEdges_adj]
  simp []

@[simp] lemma half_none_some {V : Type cycleUniverse62} (G : SimpleGraph V) (x y a : V) (hxy : x ≠ y) :
    (halfSubdivision G x y).Adj none (some a) ↔ a = y := by
  rw [halfSubdivision, SimpleGraph.deleteEdges_adj]
  simp only [subdivision_none_some, Set.mem_singleton_iff, star_inj, Option.some.injEq]
  aesop

@[simp] lemma half_some_none {V : Type cycleUniverse63} (G : SimpleGraph V) (x y a : V) (hxy : x ≠ y) :
    (halfSubdivision G x y).Adj (some a) none ↔ a = y := by
  rw [(halfSubdivision G x y).adj_comm, half_none_some G x y a hxy]

lemma option_degree_some {V : Type cycleUniverse64} [Fintype V] (K : SimpleGraph (Option V)) (v : V) :
    K.degree (some v) = (Finset.univ.filter (fun u : V => K.Adj (some v) (some u))).card +
      if K.Adj (some v) none then 1 else 0 := by
  classical
  rw [← K.card_neighborFinset_eq_degree, K.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  omega

lemma option_degree_none {V : Type cycleUniverse65} [Fintype V] (K : SimpleGraph (Option V)) :
    K.degree none = (Finset.univ.filter (fun u : V => K.Adj none (some u))).card := by
  classical
  rw [← K.card_neighborFinset_eq_degree, K.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp

lemma subdivision_old_neighbors {V : Type cycleUniverse66} [Fintype V] (G : SimpleGraph V)
    (x y v : V) :
    (Finset.univ.filter fun u : V => (subdivision G x y).Adj (some v) (some u)) =
      if v = x then (G.neighborFinset v).erase y else
      if v = y then (G.neighborFinset v).erase x else G.neighborFinset v := by
  classical
  ext u
  by_cases hx : v = x
  · subst v
    simp [eq_comm, and_comm]
    aesop
  · by_cases hy : v = y
    · subst v
      simp [hx,  eq_comm, and_comm]
      tauto
    · simp [hx, hy]

lemma subdivision_degree {V : Type cycleUniverse67} [Fintype V] (G : SimpleGraph V)
    (x y v : V) (hxy : G.Adj x y) :
    (subdivision G x y).degree (some v) = G.degree v := by
  classical
  rw [option_degree_some, subdivision_old_neighbors]
  by_cases hx : v = x
  · subst v
    simpa using Finset.card_erase_add_one (s := G.neighborFinset x) (a := y)
      (by simpa using hxy)
  · by_cases hy : v = y
    · subst v
      simpa [hx] using Finset.card_erase_add_one (s := G.neighborFinset y) (a := x)
        (by simpa using hxy.symm)
    · simp [hx,hy]

lemma subdivision_degree_none {V : Type cycleUniverse68} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) : (subdivision G x y).degree none = 2 := by
  classical
  rw [option_degree_none]
  have he : (Finset.univ.filter fun u : V => (subdivision G x y).Adj none (some u)) =
      {x,y} := by ext u; simp
  rw [he]
  simp [hxy.ne]

lemma half_degree {V : Type cycleUniverse69} [Fintype V] (G : SimpleGraph V)
    (x y v : V) (hxy : G.Adj x y) :
    (halfSubdivision G x y).degree (some v) + (if v = x then 1 else 0) = G.degree v := by
  classical
  rw [option_degree_some]
  have he : (Finset.univ.filter fun u : V => (halfSubdivision G x y).Adj (some v) (some u)) =
      (Finset.univ.filter fun u : V => (subdivision G x y).Adj (some v) (some u)) := by
    ext u; simp
  rw [he, subdivision_old_neighbors]
  by_cases hx : v = x
  · subst v
    simpa [hxy.ne] using Finset.card_erase_add_one (s := G.neighborFinset x) (a := y)
      (by simpa using hxy)
  · by_cases hy : v = y
    · subst v
      simpa [hx, hxy.ne] using Finset.card_erase_add_one (s := G.neighborFinset y) (a := x)
        (by simpa using hxy.symm)
    · simp [hx,hy,half_some_none G x y v hxy.ne]

lemma half_degree_none {V : Type cycleUniverse70} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) : (halfSubdivision G x y).degree none = 1 := by
  classical
  rw [option_degree_none]
  have he : (Finset.univ.filter fun u : V => (halfSubdivision G x y).Adj none (some u)) =
      {y} := by ext u; simp [half_none_some G x y u hxy.ne]
  rw [he]
  simp

lemma subdivision_edge_count {V : Type cycleUniverse71} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) :
    (subdivision G x y).edgeFinset.card = G.edgeFinset.card + 1 := by
  classical
  have hd := (subdivision G x y).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_option, subdivision_degree_none G x y hxy] at hd
  simp_rw [subdivision_degree G x y _ hxy] at hd
  rw [G.sum_degrees_eq_twice_card_edges] at hd
  omega

lemma half_edge_count {V : Type cycleUniverse72} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) :
    (halfSubdivision G x y).edgeFinset.card = G.edgeFinset.card := by
  classical
  have he : (halfSubdivision G x y).edgeFinset =
      (subdivision G x y).edgeFinset.erase s(none,some x) := by
    ext e
    rw [(halfSubdivision G x y).mem_edgeFinset, Finset.mem_erase,
      (subdivision G x y).mem_edgeFinset]
    simp [halfSubdivision, SimpleGraph.edgeSet_deleteEdges, and_comm]
  rw [he, Finset.card_erase_of_mem, subdivision_edge_count G x y hxy]
  · omega
  · exact (subdivision G x y).mem_edgeFinset.mpr (Or.inl rfl)

lemma subdivision_activeOrder {V : Type cycleUniverse73} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) :
    activeOrder (subdivision G x y) = activeOrder G + 1 := by
  classical
  have he : (subdivision G x y).support.toFinset =
      insert none (G.support.toFinset.image Option.some) := by
    ext v
    cases v with
    | none => simp [← SimpleGraph.degree_pos_iff_mem_support, subdivision_degree_none G x y hxy]
    | some v =>
      simp only [Set.mem_toFinset, Finset.mem_insert, Option.some_ne_none, Finset.mem_image,
        Option.some.injEq, false_or, exists_eq_right]
      rw [← (subdivision G x y).degree_pos_iff_mem_support,
        subdivision_degree G x y v hxy, G.degree_pos_iff_mem_support]
  dsimp [activeOrder]
  rw [he, Finset.card_insert_of_notMem, Finset.card_image_of_injective]
  · exact Option.some_injective V
  · simp

lemma suppress_path {V : Type cycleUniverse74} (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    {a b : V} (p : (subdivision G x y).Walk (some a) (some b)) (hp : p.IsPath) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.support = p.support.filterMap id ∧
      ∀ e : Sym2 V, e ∈ q.edgeSet ↔
        e.map Option.some ∈ p.edgeSet ∨ (e = s(x,y) ∧ s(none,some x) ∈ p.edgeSet) := by
  classical
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    cases p with
    | nil =>
      refine ⟨.nil, by simp, by simp, ?_⟩
      intro e
      simp
    | @cons _ v _ h p =>
      have ht : p.IsPath := hp.of_cons
      have ha : some a ∉ p.support := (Walk.cons_isPath_iff _ _ |>.mp hp).2
      cases v with
      | some c =>
        obtain ⟨q,hq,hqs,hqe⟩ := ih p.length (by simp only [Walk.length_cons] at hn; omega) p ht rfl
        have hac : G.Adj a c := (subdivision_some G x y a c).mp h |>.1
        refine ⟨.cons hac q, hq.cons ?_, ?_, ?_⟩
        · intro ha'
          apply ha
          rw [hqs] at ha'
          simpa using ha'
        · simp [hqs]
        · intro e
          have hinj : Function.Injective (Sym2.map (Option.some : V → Option V)) :=
            Sym2.map.injective (Option.some_injective V)
          have he : e.map Option.some = s(some a,some c) ↔ e = s(a,c) :=
            by simpa only [Sym2.map_mk] using (hinj.eq_iff (a := e) (b := s(a,c)))
          have hnedge : s(none,some x) ≠ s(some a,some c) := by simp []
          simp only [Walk.edgeSet_cons, Set.mem_insert_iff, he, hnedge, false_or, hqe]
          tauto
      | none =>
        cases p with
        | @cons _ v _ h' p =>
          cases v with
          | none => exact (h'.ne rfl).elim
          | some c =>
            have hac : a ≠ c := by
              intro he
              apply ha
              simp [he]
            have hae : a = x ∨ a = y := (subdivision_some_none G x y a).mp h
            have hce : c = x ∨ c = y := (subdivision_none_some G x y c).mp h'
            have hexy : s(a,c) = s(x,y) := by
              rcases hae with rfl | rfl <;> rcases hce with rfl | rfl
              · exact (hac rfl).elim
              · rfl
              · exact Sym2.eq_swap
              · exact (hac rfl).elim
            have hacG : G.Adj a c := G.mem_edgeSet.mp (hexy.symm ▸ hxy)
            obtain ⟨q,hq,hqs,hqe⟩ := ih p.length (by simp only [Walk.length_cons] at hn; omega) p ht.of_cons rfl
            refine ⟨.cons hacG q, hq.cons ?_, ?_, ?_⟩
            · intro ha'
              apply ha
              have hh : some a ∈ p.support := by rw [hqs] at ha'; simpa using ha'
              simp [hh]
            · simp [hqs]
            · intro e
              have he1 : e.map Option.some ≠ s(some a,none) := by
                induction e using Sym2.inductionOn with | _ u v => simp []
              have he2 : e.map Option.some ≠ s(none,some c) := by
                induction e using Sym2.inductionOn with | _ u v => simp []
              have hn : s(none,some x) = s(some a,none) ∨
                  s(none,some x) = s(none,some c) := by
                rcases hae with rfl | hay
                · exact Or.inl Sym2.eq_swap
                · rcases hce with rfl | hcy
                  · exact Or.inr rfl
                  · exact (hac (hay.trans hcy.symm)).elim
              simp only [Walk.edgeSet_cons, Set.mem_insert_iff, he1, he2, false_or,
                hexy, hqe]
              tauto

lemma tight_partition_endpoints {V : Type cycleUniverse75} {I : Type cycleUniverse76} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (P : I → Piece G) (S : Finset V)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = G.edgeSet)
    (ho : ∀ v ∈ S, Odd (G.degree v)) (hk : 2 * Fintype.card I ≤ S.card) :
    ∀ i, (P i).start ≠ (P i).finish ∧ (P i).start ∈ S ∧ (P i).finish ∈ S := by
  classical
  let endpoint : I × Bool → V := fun z => if z.2 then (P z.1).start else (P z.1).finish
  have he : ∀ v : S, ∃ z : I × Bool, endpoint z = v := by
    intro v
    obtain ⟨i,_, h | h⟩ := endpoint_of_odd G P hd hc v (ho v v.property)
    · exact ⟨(i,true),h⟩
    · exact ⟨(i,false),h⟩
  choose pick hpick using he
  have hinj : Function.Injective pick := by
    intro v w hvw
    apply Subtype.ext
    exact (hpick v).symm.trans ((congrArg endpoint hvw).trans (hpick w))
  have hsurj : Function.Surjective pick := by
    by_contra hn
    have hh := Fintype.card_lt_of_injective_not_surjective pick hinj hn
    simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_bool] at hh
    omega
  have hendinj : Function.Injective endpoint := by
    intro z t heq
    obtain ⟨v,rfl⟩ := hsurj z
    obtain ⟨w,rfl⟩ := hsurj t
    have hvw : v = w := Subtype.ext (by simpa only [hpick] using heq)
    exact congrArg pick hvw
  have hmem : ∀ z, endpoint z ∈ S := by
    intro z
    obtain ⟨v,rfl⟩ := hsurj z
    rw [hpick]
    exact v.property
  intro i
  refine ⟨?_, hmem (i,true), hmem (i,false)⟩
  intro heq
  have hh := hendinj (show endpoint (i,true) = endpoint (i,false) from heq)
  have := congrArg Prod.snd hh
  contradiction

def subdivisionRepresentative {V : Type cycleUniverse77} (x y : V) (e : Sym2 V) : Sym2 (Option V) :=
  if e = s(x,y) then s(none,some x) else e.map Option.some

lemma representative_mem {V : Type cycleUniverse78} (G : SimpleGraph V) (x y : V) (_hxy : G.Adj x y)
    (e : Sym2 V) (he : e ∈ G.edgeSet) :
    subdivisionRepresentative x y e ∈ (subdivision G x y).edgeSet := by
  classical
  by_cases h : e = s(x,y)
  · simp [subdivisionRepresentative, h]
  · rw [subdivisionRepresentative, ite_eq_right h]
    induction e using Sym2.ind with
    | _ a b => exact ⟨he,h⟩

lemma suppress_piece {V : Type cycleUniverse79} (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (P : Piece (subdivision G x y)) (hne : P.start ≠ P.finish)
    (ha : P.start ≠ none) (hb : P.finish ≠ none) :
    ∃ Q : Piece G, ∀ e, e ∈ Q.walk.edgeSet ↔ subdivisionRepresentative x y e ∈ P.walk.edgeSet := by
  classical
  rcases P with ⟨a,b,p,hp⟩
  cases a with
  | none => exact (ha rfl).elim
  | some a =>
    cases b with
    | none => exact (hb rfl).elim
    | some b =>
      have hab : a ≠ b := fun h => hne (congrArg some h)
      have hpath : p.IsPath := by
        rcases hp with h | ⟨h,_⟩
        · exact h.1
        · exact (hne h.symm).elim
      obtain ⟨q,hq,_,hqe⟩ := suppress_path G x y hxy p hpath
      have hpos : 0 < q.length := by
        by_contra hn
        exact hab (Walk.eq_of_length_eq_zero (by omega : q.length = 0))
      refine ⟨.ofPath ⟨a,b,q,hq,hpos⟩, ?_⟩
      intro e
      change e ∈ q.edgeSet ↔ _
      rw [hqe]
      by_cases he : e = s(x,y)
      · subst e
        have hn : (s(x,y) : Sym2 V).map some ∉ p.edgeSet := by
          intro h
          have hh := p.edges_subset_edgeSet h
          exact hh.2 rfl
        simp only [subdivisionRepresentative, ite_true, hn, false_or, true_and]
      · simp [subdivisionRepresentative, he]

lemma suppress_partition {V : Type cycleUniverse80} {I : Type cycleUniverse81} [Fintype I]
    (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (P : I → Piece (subdivision G x y))
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = (subdivision G x y).edgeSet)
    (hp : ∀ i, (P i).start ≠ (P i).finish ∧ (P i).start ≠ none ∧ (P i).finish ≠ none) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) = G.edgeSet := by
  classical
  choose Q hQ using fun i => suppress_piece G x y hxy (P i) (hp i).1 (hp i).2.1 (hp i).2.2
  refine ⟨Q, ?_, ?_⟩
  · intro i j hij
    exact Set.disjoint_left.mpr fun e hei hej =>
      Set.disjoint_left.mp (hd hij) ((hQ i e).mp hei) ((hQ j e).mp hej)
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun i => (Q i).walk.edges_subset_edgeSet
    · intro e he
      have hrep := representative_mem G x y hxy e he
      rw [← hc] at hrep
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hrep
      exact Set.mem_iUnion.mpr ⟨i,(hQ i e).mpr hi⟩

lemma even_activeOrder {V : Type cycleUniverse82} [Fintype V] (G : SimpleGraph V)
    (ho : ∀ v, 0 < G.degree v → Odd (G.degree v)) : Even (activeOrder G) := by
  classical
  have he : G.support.toFinset = Finset.univ.filter (fun v => Odd (G.degree v)) := by
    ext v
    simp only [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      ← G.degree_pos_iff_mem_support]
    refine ⟨ho v, ?_⟩
    rintro ⟨k,hk⟩
    omega
  simpa only [activeOrder, he] using G.even_card_odd_degree_vertices

lemma half_restore {V : Type cycleUniverse83} {I : Type cycleUniverse84} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (ho : ∀ v, 0 < G.degree v → Odd (G.degree v))
    (P : I → Piece (halfSubdivision G x y))
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = (halfSubdivision G x y).edgeSet) :
    ∃ Q : I → Piece (subdivision G x y),
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) = (subdivision G x y).edgeSet := by
  classical
  have he : {e : Sym2 (Option V) | ∃ v ∈ ({none} : Set (Option V)), e = s(some x,v)} =
      {s(none,some x)} := by
    ext e
    simp [Sym2.eq_swap]
  apply restore_partition (subdivision G x y) (halfSubdivision G x y)
    ((subdivision G x y).deleteEdges_le _) (some x) {none}
    (by intro v hv; rcases hv with rfl; exact Or.inl rfl) ?_ ?_ ?_ P hd hc
  · rw [he, halfSubdivision, SimpleGraph.edgeSet_deleteEdges]
    symm
    apply Set.sdiff_union_of_subset
    intro e he
    rcases he with rfl
    exact Or.inl rfl
  · rw [he, halfSubdivision, SimpleGraph.edgeSet_deleteEdges]
    exact Set.disjoint_sdiff_right
  · intro v hv
    cases v with
    | none => rw [half_degree_none G x y hxy]; exact ⟨0,rfl⟩
    | some v =>
      have hxv : G.Adj x v := hv.1
      have hh := half_degree G x y v hxy
      rw [ite_eq_right hxv.ne.symm, add_zero] at hh
      rw [hh]
      exact ho v ((G.degree_pos_iff_exists_adj v).mpr ⟨x,hxv.symm⟩)

theorem odd_vertex_step {V : Type cycleUniverse85} [Fintype V] (G : SimpleGraph V)
    (hIH : ∀ H : SimpleGraph (Option V), H.edgeFinset.card < G.edgeFinset.card → HasPartition H)
    (ho : ∀ v, 0 < G.degree v → Odd (G.degree v)) (x : V) (hx : 3 ≤ G.degree x) :
    HasPartition G := by
  classical
  obtain ⟨y,hxy⟩ := (G.degree_pos_iff_exists_adj x).mp (by omega)
  have hp : ∃ v, 0 < (halfSubdivision G x y).degree v ∧
      Even ((halfSubdivision G x y).degree v) := by
    refine ⟨some x, ?_, ?_⟩
    · have hd := half_degree G x y x hxy
      simp only [ite_true] at hd
      omega
    · have hd := half_degree G x y x hxy
      simp only [ite_true] at hd
      obtain ⟨k,hk⟩ := ho x (by omega)
      exact ⟨k,by omega⟩
  obtain ⟨k,P,hd,hc,hk⟩ := even_vertex_step (halfSubdivision G x y)
    (fun H hh => hIH H (by rwa [half_edge_count G x y hxy] at hh)) hp
  have hbound : 2 * k ≤ activeOrder G + 1 := by
    have hm := activeOrder_mono ((subdivision G x y).deleteEdges_le {s(none,some x)})
    rw [subdivision_activeOrder G x y hxy] at hm
    exact hk.trans hm
  have hk' : 2 * k ≤ activeOrder G := by
    obtain ⟨a,ha⟩ := even_activeOrder G ho
    omega
  obtain ⟨Q,hQ,hQC⟩ := half_restore G x y hxy ho P hd hc
  let S := G.support.toFinset.image Option.some
  have hScard : S.card = activeOrder G := by
    exact Finset.card_image_of_injective _ (Option.some_injective V)
  have hSodd : ∀ v ∈ S, Odd ((subdivision G x y).degree v) := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    rw [subdivision_degree G x y w hxy]
    exact ho w ((G.degree_pos_iff_mem_support w).mpr (Set.mem_toFinset.mp hw))
  have hends := tight_partition_endpoints (subdivision G x y) Q S hQ hQC hSodd
    (by simpa only [Fintype.card_fin, hScard] using hk')
  have hnon : ∀ i, (Q i).start ≠ (Q i).finish ∧
      (Q i).start ≠ none ∧ (Q i).finish ≠ none := by
    intro i
    refine ⟨(hends i).1, ?_, ?_⟩
    · intro h
      have hh := (hends i).2.1
      simp only [h, S, Finset.mem_image, Option.some_ne_none, and_false, exists_false] at hh
    · intro h
      have hh := (hends i).2.2
      simp only [h, S, Finset.mem_image, Option.some_ne_none, and_false, exists_false] at hh
  obtain ⟨R,hR,hRC⟩ := suppress_partition G x y hxy Q hQ hQC hnon
  exact ⟨k,R,hR,hRC,hk'⟩

theorem path_cycle_partition {V : Type u} [Fintype V] (G : SimpleGraph V) : HasPartition G := by
  classical
  suffices ∀ (n : ℕ) (W : Type u) [Fintype W] (H : SimpleGraph W),
      H.edgeFinset.card = n → HasPartition H by
    exact this G.edgeFinset.card V G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ H hcount
    by_cases he : ∃ v, 0 < H.degree v ∧ Even (H.degree v)
    · exact even_vertex_step H (fun K hk => ih K.edgeFinset.card (by omega) W K rfl) he
    · have ho : ∀ v, 0 < H.degree v → Odd (H.degree v) := by
        intro v hv
        exact Nat.not_even_iff_odd.mp (fun hev => he ⟨v,hv,hev⟩)
      by_cases hm : ∀ v, H.degree v ≤ 1
      · exact matching_partition H hm
      · push Not at hm
        obtain ⟨x,hx⟩ := hm
        have hx3 : 3 ≤ H.degree x := by
          obtain ⟨k,hk⟩ := ho x (by omega)
          omega
        exact odd_vertex_step H
          (fun K hk => ih K.edgeFinset.card (by omega) (Option W) K rfl) ho x hx3

end
end ErdosGallai.Lovasz

end
end
/-! ### Upstream module `Combinatorics/CycleDecomposition/PathDeletion.lean` -/

noncomputable section
noncomputable section
namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable

structure PositiveSimplePath {V : Type cycleUniverse1} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  positive : 0 < walk.length

lemma PositiveSimplePath.endpoints_ne {V : Type cycleUniverse2} {G : SimpleGraph V}
    (P : PositiveSimplePath G) : P.start ≠ P.finish := by
  intro he
  have hz := P.isPath.nil_iff_eq.mpr he
  have := hz.length_eq_zero
  have := P.positive
  omega

theorem endpoint_path_count {V : Type cycleUniverse3} {I : Type cycleUniverse4} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G)
    (hload : ∀ v : V, (Finset.univ.filter
      (fun i => (P i).start = v ∨ (P i).finish = v)).card ≤ 2) :
    Fintype.card I ≤ Fintype.card V := by
  classical
  have hsum : (∑ v : V, (Finset.univ.filter
      (fun i => (P i).start = v ∨ (P i).finish = v)).card) =
      2 * Fintype.card I := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    have heq : ∀ i : I,
        (∑ v : V, if (P i).start = v ∨ (P i).finish = v then 1 else 0) = 2 := by
      intro i
      have hf : (Finset.univ.filter fun v =>
          (P i).start = v ∨ (P i).finish = v) = {(P i).start, (P i).finish} := by
        ext v; simp [eq_comm]
      have hc : ({(P i).start, (P i).finish} : Finset V).card = 2 := by
        simp [(P i).endpoints_ne]
      rw [← hc, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    omega
  have hbound := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hload v)
  rw [hsum] at hbound
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hbound
  omega

def EndpointPathPartition {V : Type cycleUniverse5} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (P : Fin k → PositiveSimplePath G),
    Pairwise (fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
    (⋃ i, (P i).walk.edgeSet) = G.edgeSet ∧
    (∀ v : V, (Finset.univ.filter (fun i => (P i).start = v ∨ (P i).finish = v)).card ≤ 2) ∧
    k ≤ Fintype.card V

def PathOrCycleEdgeSet {V : Type cycleUniverse6} (G : SimpleGraph V)
    (s : Set (Sym2 V)) : Prop :=
  (∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ 0 < p.length ∧ s = p.edgeSet) ∨
  (∃ (a : V) (p : G.Walk a a), p.IsCycle ∧ s = p.edgeSet)

def LovaszPathCyclePartition {V : Type cycleUniverse7} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (parts : Fin k → Set (Sym2 V)),
    (∀ i, PathOrCycleEdgeSet G (parts i)) ∧
    Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
    (⋃ i, parts i) = G.edgeSet ∧ 2 * k ≤ Fintype.card V

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
def evenAugmentation {V : Type cycleUniverse8} [Fintype V] (G : SimpleGraph V) :
    SimpleGraph (Option V) where
  Adj x y := match x, y with
    | some u, some v => G.Adj u v
    | none, some v => Even (G.degree v)
    | some u, none => Even (G.degree u)
    | none, none => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact G.adj_symm h⟩
  loopless := ⟨by
    intro x h
    cases x
    · exact h
    · exact G.irrefl h⟩

@[simp] theorem evenAugmentation_some_adj {V : Type cycleUniverse9} [Fintype V]
    (G : SimpleGraph V) (u v : V) :
    (evenAugmentation G).Adj (some u) (some v) ↔ G.Adj u v := Iff.rfl

@[simp] theorem evenAugmentation_some_none {V : Type cycleUniverse11} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (evenAugmentation G).Adj (some v) none ↔ Even (G.degree v) := Iff.rfl

theorem evenAugmentation_degree {V : Type cycleUniverse12} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (evenAugmentation G).degree (some v) =
      G.degree v + if Even (G.degree v) then 1 else 0 := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  simp only [evenAugmentation_some_adj, evenAugmentation_some_none]
  have he : (∑ u : V, if G.Adj v u then 1 else 0) = G.degree v := by
    rw [← G.card_neighborFinset_eq_degree v, G.neighborFinset_eq_filter,
      Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [he]
  omega

theorem evenAugmentation_old_odd {V : Type cycleUniverse13} [Fintype V]
    (G : SimpleGraph V) (v : V) : Odd ((evenAugmentation G).degree (some v)) := by
  rw [evenAugmentation_degree]
  by_cases h : Even (G.degree v)
  · simp only [h, ↓reduceIte]
    rcases h with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · simpa [h] using Nat.not_even_iff_odd.mp h

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable

theorem trail_partition_degree_sum {V : Type cycleUniverse14} {I : Type cycleUniverse15} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    G.degree v = ∑ i, (p i).edges.countP (fun e => decide (v ∈ e)) := by
  classical
  have he : G.edgeFinset = Finset.univ.biUnion (fun i => (p i).edges.toFinset) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, ← hc, Set.mem_iUnion,
      Finset.mem_biUnion, Finset.mem_univ, List.mem_toFinset, true_and,
      SimpleGraph.Walk.mem_edgeSet]
  rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter, he,
    Finset.filter_biUnion]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    have hfilter : ((p i).edges.filter (fun e => decide (v ∈ e))).toFinset =
        ((p i).edges.toFinset.filter (fun e => v ∈ e)) := by
      simp [List.toFinset_filter]
    rw [← hfilter, List.toFinset_card_of_nodup ((ht i).edges_nodup.filter _),
      List.countP_eq_length_filter]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact Set.disjoint_left.mp (hd hij)
      (by simpa using (Finset.mem_filter.mp hei).1)
      (by simpa using (Finset.mem_filter.mp hej).1)

theorem trail_partition_even_degree_iff {V : Type cycleUniverse16} {I : Type cycleUniverse17} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    Even (G.degree v) ↔ Even (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card := by
  classical
  rw [trail_partition_degree_sum G p ht hd hc v, Finset.even_sum_iff_even_card_odd]
  have he : (Finset.univ.filter (fun i => Odd ((p i).edges.countP
      (fun e => decide (v ∈ e))))) = (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ← Nat.not_even_iff_odd, (ht i).even_countP_edges_iff]
    tauto
  rw [he]

private theorem odd_load_one {V : Type cycleUniverse18} [DecidableEq V]
    (S : Finset V) (f : V → ℕ) (ho : ∀ v ∈ S, Odd (f v))
    (hs : ∑ v ∈ S, f v ≤ S.card + 1) : ∀ v ∈ S, f v = 1 := by
  intro v hv
  by_contra hn
  have hv3 : 3 ≤ f v := by rcases ho v hv with ⟨k, hk⟩; omega
  have hlow : ∑ x ∈ S, (1 + if x = v then 2 else 0) ≤ ∑ x ∈ S, f x := by
    apply Finset.sum_le_sum
    intro x hx
    by_cases he : x = v
    · subst x; simpa using hv3
    · simp only [he, ↓reduceIte, add_zero]
      rcases ho x hx with ⟨k, hk⟩
      omega
  have heq : (∑ x ∈ S, (1 + if x = v then 2 else 0)) = S.card + 2 := by
    simp [Finset.sum_add_distrib, hv]
  omega

theorem tight_odd_trail_partition {V : Type cycleUniverse19} {I : Type cycleUniverse20} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (S : Finset V) {a b : I → V}
    (p : ∀ i, G.Walk (a i) (b i)) (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet)
    (ho : ∀ v ∈ S, Odd (G.degree v))
    (hsize : 2 * Fintype.card I ≤ S.card + 1) :
    (∀ i, a i ≠ b i) ∧ (∀ v ∈ S,
      (Finset.univ.filter (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card = 1) := by
  classical
  let load := fun v : V => (Finset.univ.filter
    (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card
  let openParts := Finset.univ.filter (fun i => a i ≠ b i)
  have hlodd : ∀ v ∈ S, Odd (load v) := by
    intro v hv
    rw [← Nat.not_even_iff_odd, ← trail_partition_even_degree_iff G p ht hd hc v]
    exact (Nat.not_even_iff_odd.mpr (ho v hv))
  have htotal : (∑ v : V, load v) = 2 * openParts.card := by
    dsimp [load]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    have he : ∀ i : I, (∑ v : V, if a i ≠ b i ∧ (v = a i ∨ v = b i) then 1 else 0) =
        if a i ≠ b i then 2 else 0 := by
      intro i
      by_cases h : a i = b i
      · simp [h]
      · have hf : (Finset.univ.filter (fun v => a i ≠ b i ∧ (v = a i ∨ v = b i))) =
            {a i, b i} := by ext v; simp [h]
        have hcard : ({a i, b i} : Finset V).card = 2 := by simp [h]
        rw [ite_eq_left h, ← hcard, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp_rw [he]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    change openParts.card * 2 = 2 * openParts.card
    omega
  have hsub : (∑ v ∈ S, load v) ≤ ∑ v : V, load v :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  have hlow : S.card ≤ ∑ v ∈ S, load v := by
    simpa using Finset.sum_le_sum (s := S) (f := fun _ => 1) (g := load)
      (fun v hv => by rcases hlodd v hv with ⟨k, hk⟩; omega)
  have hcount : openParts.card ≤ Fintype.card I := Finset.card_le_univ _
  have hpoint := odd_load_one S load hlodd (by omega)
  refine ⟨?_, hpoint⟩
  intro i hi
  have hproper : openParts ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have hh : i ∈ openParts := heq.symm ▸ Finset.mem_univ i
    simp [openParts, hi] at hh
  have hlt := Finset.card_lt_card hproper
  simp only [Finset.card_univ] at hlt
  omega

end
end ErdosGallai

namespace ErdosGallai
noncomputable section

private theorem path_tail_delete_start {V : Type cycleUniverse21} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.tail.edgeSet = {e | e ∈ p.edgeSet ∧ a ∉ e} := by
  cases p with
  | nil => ext e; simp
  | @cons a c b h q =>
    have ha : a ∉ q.support := (List.nodup_cons.mp hp.support_nodup).1
    have hnot : ∀ e ∈ q.edgeSet, a ∉ e := by
      intro e he hae
      exact ha (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
        (Or.inr ⟨e, he, hae⟩))
    ext e
    simp only [Set.mem_ofPred_eq, SimpleGraph.Walk.mem_edgeSet,
      SimpleGraph.Walk.edges_tail, SimpleGraph.Walk.edges_cons, List.tail_cons, List.mem_cons]
    constructor
    · intro he
      exact ⟨Or.inr he, hnot e he⟩
    · rintro ⟨he | he, hn⟩
      · subst e; exact (hn (by simp)).elim
      · exact he

private theorem path_dropLast_delete_end {V : Type cycleUniverse22} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.dropLast.edgeSet = {e | e ∈ p.edgeSet ∧ b ∉ e} := by
  have he : p.dropLast.edgeSet = p.reverse.tail.edgeSet := by
    calc
      _ = p.dropLast.reverse.edgeSet := (SimpleGraph.Walk.edgeSet_reverse _).symm
      _ = _ := by rw [SimpleGraph.Walk.reverse_dropLast, SimpleGraph.Walk.edgeSet_copy]
  rw [he, path_tail_delete_start p.reverse hp.reverse, SimpleGraph.Walk.edgeSet_reverse]

private theorem positive_avoids_of_no_incidence {V : Type cycleUniverse23} {G : SimpleGraph V}
    {a b v : V} (p : G.Walk a b) (hpos : 0 < p.length)
    (he : ∀ e ∈ p.edgeSet, v ∉ e) : v ∉ p.support := by
  have hn : ¬p.Nil := by intro hz; have := hz.length_eq_zero; omega
  intro hv
  obtain ⟨e, he', hve⟩ := SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hn |>.mp hv
  exact he e he' hve

theorem delete_vertex_from_path {V : Type cycleUniverse24} [DecidableEq V] {G : SimpleGraph V}
    {a b v : V} (p : G.Walk a b) (hp : p.IsPath) (hv : v ∈ p.support) :
    let q := (p.takeUntil v hv).dropLast
    let r := (p.dropUntil v hv).tail
    q.IsPath ∧ r.IsPath ∧ Disjoint q.edgeSet r.edgeSet ∧
    q.edgeSet ∪ r.edgeSet = {e | e ∈ p.edgeSet ∧ v ∉ e} ∧
    (0 < q.length → v ∉ q.support) ∧
    (0 < r.length → v ∉ r.support) ∧
    (0 < q.length → G.Adj (p.takeUntil v hv).penultimate v) ∧
    (0 < r.length → G.Adj v (p.dropUntil v hv).snd) := by
  dsimp only
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have ht : t.IsPath := hp.takeUntil hv
  have hd : d.IsPath := hp.dropUntil hv
  have heq : t.append d = p := p.take_spec hv
  have hqe : t.dropLast.edgeSet = {e | e ∈ t.edgeSet ∧ v ∉ e} :=
    path_dropLast_delete_end t ht
  have hre : d.tail.edgeSet = {e | e ∈ d.edgeSet ∧ v ∉ e} :=
    path_tail_delete_start d hd
  have hdis : Disjoint t.edgeSet d.edgeSet := by
    have hn := hp.isTrail.edges_nodup
    rw [← heq, SimpleGraph.Walk.edges_append] at hn
    have hn' := (List.nodup_append.mp hn).2.2
    apply Set.disjoint_left.mpr
    intro e het hed
    exact hn' e het e hed rfl
  refine ⟨ht.dropLast, hd.tail, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hqe, hre]
    exact hdis.mono (fun _ h => h.1) (fun _ h => h.1)
  · have he : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    rw [hqe, hre]
    ext e
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    rw [← he]
    simp only [Set.mem_union]
    tauto
  · intro hpos
    apply positive_avoids_of_no_incidence _ hpos
    intro e he
    exact (hqe ▸ he).2
  · intro hpos
    apply positive_avoids_of_no_incidence _ hpos
    intro e he
    exact (hre ▸ he).2
  · intro hpos
    apply t.adj_penultimate
    intro hn
    have hz := hn.length_eq_zero
    change 0 < t.dropLast.length at hpos
    rw [SimpleGraph.Walk.length_dropLast, hz] at hpos
    omega
  · intro hpos
    apply d.adj_snd
    intro hn
    have hz := hn.length_eq_zero
    change 0 < d.tail.length at hpos
    rw [SimpleGraph.Walk.length_tail, hz] at hpos
    omega

theorem delete_vertex_boundary_edges {V : Type cycleUniverse25} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V} (p : G.Walk a b) (hv : v ∈ p.support) :
    (0 < (p.takeUntil v hv).dropLast.length →
      s((p.takeUntil v hv).penultimate, v) ∈ p.edgeSet) ∧
    (0 < (p.dropUntil v hv).tail.length →
      s(v, (p.dropUntil v hv).snd) ∈ p.edgeSet) := by
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have heq : t.append d = p := p.take_spec hv
  constructor
  · intro hpos
    have hn : ¬ t.Nil := by
      intro hz
      change 0 < t.dropLast.length at hpos
      rw [SimpleGraph.Walk.length_dropLast, hz.length_eq_zero] at hpos
      omega
    have hm := t.mk_penultimate_end_mem_edges hn
    have hed : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    exact hed ▸ Or.inl hm
  · intro hpos
    have hn : ¬ d.Nil := by
      intro hz
      change 0 < d.tail.length at hpos
      rw [SimpleGraph.Walk.length_tail, hz.length_eq_zero] at hpos
      omega
    have hm := d.mk_start_snd_mem_edges hn
    have hed : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    exact hed ▸ Or.inr hm

theorem delete_vertex_new_ends_ne {V : Type cycleUniverse26} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V} (p : G.Walk a b) (hp : p.IsPath)
    (hv : v ∈ p.support)
    (hl : 0 < (p.takeUntil v hv).dropLast.length)
    (hr : 0 < (p.dropUntil v hv).tail.length) :
    (p.takeUntil v hv).penultimate ≠ (p.dropUntil v hv).snd := by
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have heq : t.append d = p := p.take_spec hv
  have htn : ¬t.Nil := by
    intro hz
    change 0 < t.dropLast.length at hl
    rw [SimpleGraph.Walk.length_dropLast, hz.length_eq_zero] at hl
    omega
  have hdn : ¬d.Nil := by
    intro hz
    change 0 < d.tail.length at hr
    rw [SimpleGraph.Walk.length_tail, hz.length_eq_zero] at hr
    omega
  have hdj := hp.isTrail.edges_nodup
  rw [← heq, SimpleGraph.Walk.edges_append] at hdj
  have hdis := (List.nodup_append.mp hdj).2.2
  intro hsame
  have ha := t.mk_penultimate_end_mem_edges htn
  have hb := d.mk_start_snd_mem_edges hdn
  apply hdis _ ha _ hb

  rw [show t.penultimate = d.snd from hsame, Sym2.eq_swap]

theorem delete_vertex_new_endpoint_load {V : Type cycleUniverse27} {I : Type cycleUniverse28} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} {a b : I → V} {v : V}
    (p : ∀ i, G.Walk (a i) (b i)) (hp : ∀ i, (p i).IsPath)
    (hv : ∀ i, v ∈ (p i).support)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet) (x : V) :
    let live := fun z : I × Bool => if z.2 then
      0 < ((p z.1).takeUntil v (hv z.1)).dropLast.length else
      0 < ((p z.1).dropUntil v (hv z.1)).tail.length
    let newEnd := fun z : I × Bool => if z.2 then
      ((p z.1).takeUntil v (hv z.1)).penultimate else
      ((p z.1).dropUntil v (hv z.1)).snd
    (Finset.univ.filter fun z => live z ∧ newEnd z = x).card ≤ 1 := by
  classical
  dsimp only
  apply Finset.card_le_one.mpr
  intro z hz w hw
  obtain ⟨i, bi⟩ := z
  obtain ⟨j, bj⟩ := w
  have hi := (Finset.mem_filter.mp hz).2
  have hj := (Finset.mem_filter.mp hw).2
  have hei : s(v,x) ∈ (p i).edgeSet := by
    cases bi
    · have hx : ((p i).dropUntil v (hv i)).snd = x := hi.2
      simpa only [hx] using (delete_vertex_boundary_edges (p i) (hv i)).2 hi.1
    · have hx : ((p i).takeUntil v (hv i)).penultimate = x := hi.2
      have he := (delete_vertex_boundary_edges (p i) (hv i)).1 hi.1
      simpa only [hx, Sym2.eq_swap] using he
  have hej : s(v,x) ∈ (p j).edgeSet := by
    cases bj
    · have hx : ((p j).dropUntil v (hv j)).snd = x := hj.2
      simpa only [hx] using (delete_vertex_boundary_edges (p j) (hv j)).2 hj.1
    · have hx : ((p j).takeUntil v (hv j)).penultimate = x := hj.2
      have he := (delete_vertex_boundary_edges (p j) (hv j)).1 hj.1
      simpa only [hx, Sym2.eq_swap] using he
  have hij : i = j := by
    by_contra hn
    exact Set.disjoint_left.mp (hd hn) hei hej
  subst j
  congr 1
  cases bi <;> cases bj
  · rfl
  · have he := delete_vertex_new_ends_ne (p i) (hp i) (hv i) hj.1 hi.1
    exact (he (hj.2.trans hi.2.symm)).elim
  · have he := delete_vertex_new_ends_ne (p i) (hp i) (hv i) hi.1 hj.1
    exact (he (hi.2.trans hj.2.symm)).elim
  · rfl

structure SimplePathPiece {V : Type cycleUniverse29} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath

namespace SimplePathPiece
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse30} {I : Type cycleUniverse31} [Fintype I] [DecidableEq V] {G : SimpleGraph V}

def Avoiding (p : I → SimplePathPiece G) (v : V) := {i : I // v ∉ (p i).walk.support}
def Meeting (p : I → SimplePathPiece G) (v : V) := {i : I // v ∈ (p i).walk.support}
def DeleteIndex (p : I → SimplePathPiece G) (v : V) :=
  Avoiding p v ⊕ (Meeting p v × Bool)

instance (p : I → SimplePathPiece G) (v : V) : Fintype (Avoiding p v) := by
  classical
  exact inferInstanceAs (Fintype {i : I // v ∉ (p i).walk.support})
instance (p : I → SimplePathPiece G) (v : V) : Fintype (Meeting p v) := by
  classical
  exact inferInstanceAs (Fintype {i : I // v ∈ (p i).walk.support})
instance (p : I → SimplePathPiece G) (v : V) : Fintype (DeleteIndex p v) :=
  inferInstanceAs (Fintype (Avoiding p v ⊕ (Meeting p v × Bool)))

def deleted (p : I → SimplePathPiece G) (v : V) : DeleteIndex p v → SimplePathPiece G
  | .inl i => p i.val
  | .inr (i,true) => ⟨_,_,((p i.val).walk.takeUntil v i.property).dropLast,
      ((p i.val).isPath.takeUntil i.property).dropLast⟩
  | .inr (i,false) => ⟨_,_,((p i.val).walk.dropUntil v i.property).tail,
      ((p i.val).isPath.dropUntil i.property).tail⟩

def parent (p : I → SimplePathPiece G) (v : V) : DeleteIndex p v → I
  | .inl i => i.val
  | .inr (i,_) => i.val

def oldEnd (p : I → SimplePathPiece G) (v x : V) : DeleteIndex p v → Prop
  | .inl i => (p i.val).start = x ∨ (p i.val).finish = x
  | .inr (i,true) => (p i.val).start = x
  | .inr (i,false) => (p i.val).finish = x

def newEnd (p : I → SimplePathPiece G) (v x : V) : DeleteIndex p v → Prop
  | .inl _ => False
  | .inr (i,true) => ((p i.val).walk.takeUntil v i.property).penultimate = x
  | .inr (i,false) => ((p i.val).walk.dropUntil v i.property).snd = x

lemma deleted_ends {V : Type cycleUniverse32} {I : Type cycleUniverse33} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v x : V) (j : DeleteIndex p v) :
    (deleted p v j).start = x ∨ (deleted p v j).finish = x ↔
      oldEnd p v x j ∨ newEnd p v x j := by
  rcases j with i | ⟨i,b⟩
  · simp [deleted, oldEnd, newEnd]
  · cases b <;> simp [deleted, oldEnd, newEnd, or_comm]

lemma deleted_edges_subset {V : Type cycleUniverse34} {I : Type cycleUniverse35} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V) (j : DeleteIndex p v) :
    (deleted p v j).walk.edgeSet ⊆ (p (parent p v j)).walk.edgeSet := by
  rcases j with i | ⟨i,b⟩
  · exact Set.Subset.rfl
  · have h := (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.2.1
    cases b
    · intro e he
      exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
        h ▸ Or.inr he).1
    · intro e he
      exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
        h ▸ Or.inl he).1

lemma deleted_positive_avoids {V : Type cycleUniverse36} {I : Type cycleUniverse37} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V) (j : DeleteIndex p v)
    (hpos : 0 < (deleted p v j).walk.length) : v ∉ (deleted p v j).walk.support := by
  rcases j with i | ⟨i,b⟩
  · exact i.property
  · have h := delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property
    cases b
    · exact h.2.2.2.2.2.1 hpos
    · exact h.2.2.2.2.1 hpos

lemma deleted_disjoint (p : I → SimplePathPiece G) (v : V)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet) :
    Pairwise fun j k => Disjoint (deleted p v j).walk.edgeSet (deleted p v k).walk.edgeSet := by
  intro j k hjk
  by_cases he : parent p v j = parent p v k
  · rcases j with i | ⟨i,b⟩ <;> rcases k with l | ⟨l,c⟩
    · exact (hjk (congrArg Sum.inl (Subtype.ext he))).elim
    · exact (i.property (show v ∈ (p i.val).walk.support from (show i.val = l.val from he).symm ▸ l.property)).elim
    · exact (l.property (show v ∈ (p l.val).walk.support from (show i.val = l.val from he) ▸ i.property)).elim
    · have hil : i = l := Subtype.ext he
      subst l
      cases b <;> cases c
      · exact (hjk rfl).elim
      · exact (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.1.symm
      · exact (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.1
      · exact (hjk rfl).elim
  · exact (hd he).mono (deleted_edges_subset p v j) (deleted_edges_subset p v k)

lemma deleted_old_load (p : I → SimplePathPiece G) (v x : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hload : (Finset.univ.filter fun i => (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    (Finset.univ.filter fun j : DeleteIndex p v => oldEnd p v x j).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hjp : (p (parent p v j)).start = x ∨ (p (parent p v j)).finish = x := by
    have h := (Finset.mem_filter.mp hj).2
    rcases j with i | ⟨i,b⟩
    · exact h
    · cases b
      · exact Or.inr h
      · exact Or.inl h
  have hkp : (p (parent p v k)).start = x ∨ (p (parent p v k)).finish = x := by
    have h := (Finset.mem_filter.mp hk).2
    rcases k with i | ⟨i,b⟩
    · exact h
    · cases b
      · exact Or.inr h
      · exact Or.inl h
  have he := Finset.card_le_one.mp hload (parent p v j)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hjp⟩) (parent p v k)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkp⟩)
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  rcases j with i | ⟨i,b⟩ <;> rcases k with l | ⟨l,c⟩
  · exact congrArg Sum.inl (Subtype.ext he)
  · exact (i.property (show v ∈ (p i.val).walk.support from (show i.val = l.val from he).symm ▸ l.property)).elim
  · exact (l.property (show v ∈ (p l.val).walk.support from (show i.val = l.val from he) ▸ i.property)).elim
  · have hil : i = l := Subtype.ext he
    subst l
    cases b <;> cases c
    · rfl
    · exact (hne _ (hk'.trans hj'.symm)).elim
    · exact (hne _ (hj'.trans hk'.symm)).elim
    · rfl

lemma deleted_new_load (p : I → SimplePathPiece G) (v x : V)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet) :
    (Finset.univ.filter fun j : DeleteIndex p v =>
      0 < (deleted p v j).walk.length ∧ newEnd p v x j).card ≤ 1 := by
  classical
  have h := delete_vertex_new_endpoint_load
    (fun i : Meeting p v => (p i.val).walk) (fun i => (p i.val).isPath)
    (fun i => i.property)
    (fun i j hij => hd (fun he => hij (Subtype.ext he))) x
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  rcases j with i | ⟨i,b⟩
  · exact False.elim hj'.2
  rcases k with l | ⟨l,c⟩
  · exact False.elim hk'.2
  apply congrArg Sum.inr
  apply Finset.card_le_one.mp h
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases b <;> exact hj'
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases c <;> exact hk'

theorem deleted_endpoint_load (p : I → SimplePathPiece G) (v x : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet)
    (hload : (Finset.univ.filter fun i => (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    (Finset.univ.filter fun j : DeleteIndex p v => 0 < (deleted p v j).walk.length ∧
      ((deleted p v j).start = x ∨ (deleted p v j).finish = x)).card ≤ 2 := by
  classical
  let A := Finset.univ.filter (fun j : DeleteIndex p v => oldEnd p v x j)
  let B := Finset.univ.filter (fun j : DeleteIndex p v =>
    0 < (deleted p v j).walk.length ∧ newEnd p v x j)
  have hsub : (Finset.univ.filter fun j : DeleteIndex p v =>
      0 < (deleted p v j).walk.length ∧
      ((deleted p v j).start = x ∨ (deleted p v j).finish = x)) ⊆ A ∪ B := by
    intro j hj
    obtain ⟨hpos,hend⟩ := (Finset.mem_filter.mp hj).2
    rcases (deleted_ends p v x j).mp hend with ho | hn
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpos,hn⟩)
  have ha := deleted_old_load p v x hne hload
  have hb := deleted_new_load p v x hd
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
  dsimp [A,B] at hc
  omega

theorem deleted_union (p : I → SimplePathPiece G) (v : V) :
    (⋃ j : DeleteIndex p v, (deleted p v j).walk.edgeSet) =
      {e | (∃ i, e ∈ (p i).walk.edgeSet) ∧ v ∉ e} := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    refine ⟨⟨parent p v j, deleted_edges_subset p v j hj⟩,?_⟩
    rcases j with i | ⟨i,b⟩
    · intro hv
      exact i.property (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
        (Or.inr ⟨e,hj,hv⟩))
    · have h := (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.2.1
      cases b
      · exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
          h ▸ Or.inr hj).2
      · exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
          h ▸ Or.inl hj).2
  · rintro ⟨⟨i,hi⟩,hv⟩
    by_cases hs : v ∈ (p i).walk.support
    · have h := (delete_vertex_from_path (p i).walk (p i).isPath hs).2.2.2.1
      have he : e ∈ ((p i).walk.takeUntil v hs).dropLast.edgeSet ∪
          ((p i).walk.dropUntil v hs).tail.edgeSet := h.symm ▸ ⟨hi,hv⟩
      rcases he with hl | hr
      · exact Set.mem_iUnion.mpr ⟨Sum.inr (⟨i,hs⟩,true),hl⟩
      · exact Set.mem_iUnion.mpr ⟨Sum.inr (⟨i,hs⟩,false),hr⟩
    · exact Set.mem_iUnion.mpr ⟨Sum.inl ⟨i,hs⟩,hi⟩

theorem deleted_positive_union (p : I → SimplePathPiece G) (v : V) :
    (⋃ j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length},
      (deleted p v j.val).walk.edgeSet) =
      {e | (∃ i, e ∈ (p i).walk.edgeSet) ∧ v ∉ e} := by
  rw [← deleted_union p v]
  ext e
  constructor
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    exact Set.mem_iUnion.mpr ⟨j.val,hj⟩
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    have hp : 0 < (deleted p v j).walk.length := by
      by_contra hn
      have hz : (deleted p v j).walk.length = 0 := by omega
      have hn' := SimpleGraph.Walk.length_eq_zero_iff.mp hz
      have he' := SimpleGraph.Walk.edges_eq_nil.mpr hn'
      have hmem : e ∈ (deleted p v j).walk.edges := hj
      exact List.not_mem_nil (he' ▸ hmem)
    exact Set.mem_iUnion.mpr ⟨⟨j,hp⟩,hj⟩

def deletedInduced (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    SimplePathPiece (G.induce {x | x ≠ v}) := by
  let q := deleted p v j.val
  have havo : ∀ x ∈ q.walk.support, x ∈ ({x | x ≠ v} : Set V) := by
    intro x hx he
    subst x
    exact deleted_positive_avoids p v j.val j.property hx
  exact ⟨_,_, q.walk.induce _ havo, by
    apply SimpleGraph.Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce _).toHom)
    simpa using q.isPath⟩

end SimplePathPiece

end
end ErdosGallai
end
end
/-! ### Upstream module `Combinatorics/CycleDecomposition/EndpointPartition.lean` -/

noncomputable section
noncomputable section
namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
theorem endpoint_partition_of_family {V : Type cycleUniverse1} {I : Type cycleUniverse2} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = G.edgeSet)
    (hl : ∀ x : V, (Finset.univ.filter fun i =>
      (P i).start = x ∨ (P i).finish = x).card ≤ 2) : EndpointPathPartition G := by
  classical
  let e := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I,fun j => P (e j),?_,?_,?_,endpoint_path_count P hl⟩
  · intro i j hij
    exact hd (fun he => hij (e.injective he))
  · rw [← hc]
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e i,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,by rw [e.apply_symm_apply]; exact hi⟩
  · intro x
    have heq : (Finset.univ.filter fun j => (P (e j)).start = x ∨ (P (e j)).finish = x).card =
        (Finset.univ.filter fun i => (P i).start = x ∨ (P i).finish = x).card := by
      apply Finset.card_bij (fun j _ => e j)
      · intro i hi; simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
      · intro i hi j hj he; exact e.injective he
      · intro i hi; exact ⟨e.symm i,by simpa using hi, by simp⟩
    rw [heq]
    exact hl x

def PositiveSimplePath.mapIso {V : Type cycleUniverse3} {W : Type cycleUniverse4} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (P : PositiveSimplePath G) : PositiveSimplePath H :=
  ⟨f P.start,f P.finish,P.walk.map f.toHom,P.isPath.map f.injective,by simpa using P.positive⟩

theorem endpoint_partition_mapIso {V : Type cycleUniverse5} {W : Type cycleUniverse6} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H)
    (hp : EndpointPathPartition G) : EndpointPathPartition H := by
  classical
  obtain ⟨k,P,hd,hc,hl,hk⟩ := hp
  apply endpoint_partition_of_family (fun i => (P i).mapIso f)
  · intro i j hij
    change Disjoint ((P i).walk.map f.toHom).edgeSet ((P j).walk.map f.toHom).edgeSet
    simp only [SimpleGraph.Walk.edgeSet_map]
    exact (Set.disjoint_image_iff (Sym2.map.injective f.injective)).mpr (hd hij)
  · have hmap : Sym2.map f.toHom '' G.edgeSet = H.edgeSet := by
      ext e
      induction e using Sym2.inductionOn with | _ u v =>
        constructor
        · rintro ⟨e,he,heq⟩
          induction e using Sym2.inductionOn with | _ a b =>
            have ha : H.Adj (f a) (f b) := f.toHom.map_adj he
            exact heq ▸ ha
        · intro huv
          refine ⟨s(f.symm u, f.symm v), f.symm.toHom.map_adj huv,?_⟩
          simp
    change (⋃ i, ((P i).walk.map f.toHom).edgeSet) = H.edgeSet
    simp_rw [SimpleGraph.Walk.edgeSet_map]
    rw [← Set.image_iUnion,hc,hmap]
  · intro x
    have heq : (Finset.univ.filter fun i => ((P i).mapIso f).start = x ∨
        ((P i).mapIso f).finish = x) =
        (Finset.univ.filter fun i => (P i).start = f.symm x ∨ (P i).finish = f.symm x) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      change (f (P i).start = x ∨ f (P i).finish = x) ↔ _
      exact or_congr (f.toEquiv.eq_symm_apply.symm) (f.toEquiv.eq_symm_apply.symm)
    rw [heq]
    exact hl _

namespace SimplePathPiece
variable {V : Type cycleUniverse7} {I : Type cycleUniverse8} [Fintype V] [Fintype I] [DecidableEq V] {G : SimpleGraph V}

lemma deletedInduced_map {V : Type cycleUniverse9} {I : Type cycleUniverse10} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] [_contextInstance4 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    (deletedInduced p v j).walk.map (SimpleGraph.Embedding.induce _).toHom =
      (deleted p v j.val).walk := by
  exact SimpleGraph.Walk.map_induce _ _

lemma deletedInduced_edges (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    Sym2.map (SimpleGraph.Embedding.induce (G := G) {x | x ≠ v}).toHom ''
      (deletedInduced p v j).walk.edgeSet = (deleted p v j.val).walk.edgeSet := by
  calc
    _ = ((deletedInduced p v j).walk.map
        (SimpleGraph.Embedding.induce {x | x ≠ v}).toHom).edgeSet :=
      (SimpleGraph.Walk.edgeSet_map _ _).symm
    _ = _ := congrArg (fun q : G.Walk (deleted p v j.val).start
        (deleted p v j.val).finish => q.edgeSet) (deletedInduced_map p v j)

def deletedPositive (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    PositiveSimplePath (G.induce {x | x ≠ v}) :=
  { deletedInduced p v j with
    positive := by
      have h := congrArg SimpleGraph.Walk.length (deletedInduced_map p v j)
      rw [SimpleGraph.Walk.length_map] at h
      rw [h]
      exact j.property }

theorem endpoint_partition_after_deletion (p : I → SimplePathPiece G) (v : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet)
    (hc : (⋃ i, (p i).walk.edgeSet) = G.edgeSet)
    (hl : ∀ x : V, x ≠ v → (Finset.univ.filter fun i =>
      (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    EndpointPathPartition (G.induce {x | x ≠ v}) := by
  classical
  let A := {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}
  let f : G.induce {x | x ≠ v} →g G := (SimpleGraph.Embedding.induce _).toHom
  have hf : Function.Injective f := Subtype.val_injective
  apply endpoint_partition_of_family (fun j : A => deletedPositive p v j)
  · intro j k hjk
    have hdis := deleted_disjoint p v hd (fun he => hjk (Subtype.ext he))
    apply Set.disjoint_left.mpr
    intro e hej hek
    have he1 : Sym2.map f e ∈ (deleted p v j.val).walk.edgeSet := by
      rw [← deletedInduced_edges p v j]
      exact ⟨e,hej,rfl⟩
    have he2 : Sym2.map f e ∈ (deleted p v k.val).walk.edgeSet := by
      rw [← deletedInduced_edges p v k]
      exact ⟨e,hek,rfl⟩
    exact Set.disjoint_left.mp hdis he1 he2
  · apply Set.Subset.antisymm
    · intro e he
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
      exact (deletedPositive p v j).walk.edges_subset_edgeSet hj
    · intro e he
      have he' : Sym2.map f e ∈ G.edgeSet ∧ v ∉ Sym2.map f e := by
        induction e using Sym2.inductionOn with | _ a b =>
          refine ⟨he,?_⟩
          change v ∉ s(a.val,b.val)
          simpa only [Sym2.map_mk,Sym2.mem_iff,eq_comm] using not_or.mpr ⟨a.property,b.property⟩
      have hmem : Sym2.map f e ∈ ⋃ j : A, (deleted p v j.val).walk.edgeSet := by
        rw [deleted_positive_union]
        refine ⟨?_,he'.2⟩
        exact Set.mem_iUnion.mp (hc.symm ▸ he'.1)
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hmem
      rw [← deletedInduced_edges p v j] at hj
      obtain ⟨e',he',heq⟩ := hj
      have heq' : e' = e := Sym2.map.injective hf heq
      subst e'
      exact Set.mem_iUnion.mpr ⟨j,he'⟩
  · intro x
    have hb := deleted_endpoint_load p v x.val hne hd (hl x.val x.property)
    have hc' : (Finset.univ.filter fun j : A =>
        (deletedPositive p v j).start = x ∨ (deletedPositive p v j).finish = x).card ≤
        (Finset.univ.filter fun j : DeleteIndex p v => 0 < (deleted p v j).walk.length ∧
          ((deleted p v j).start = x.val ∨ (deleted p v j).finish = x.val)).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro j hj
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,j.property,?_⟩
        rcases (Finset.mem_filter.mp hj).2 with hs | ht
        · exact Or.inl (congrArg Subtype.val hs)
        · exact Or.inr (congrArg Subtype.val ht)
      · exact fun _ _ _ _ he => Subtype.ext he
    convert hc'.trans hb using 1

    congr 1
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]

end SimplePathPiece

def evenAugmentationOldIso {V : Type cycleUniverse11} [Fintype V] (G : SimpleGraph V) :
    G ≃g (evenAugmentation G).induce {x | x ≠ none} where
  toEquiv := Equiv.optionSubtype none ⟨Equiv.refl (Option V),rfl⟩
  map_rel_iff' := Iff.rfl

theorem endpoint_partition_of_augmented_parts {V : Type cycleUniverse12} [Fintype V]
    (G : SimpleGraph V) (hL : LovaszPathCyclePartition (evenAugmentation G)) :
    EndpointPathPartition G := by
  classical
  obtain ⟨k,parts,hparts,hd,hc,hk⟩ := hL
  have hw : ∀ i : Fin k, ∃ (a b : Option V) (p : (evenAugmentation G).Walk a b),
      p.IsTrail ∧ (a ≠ b → p.IsPath) ∧ parts i = p.edgeSet := by
    intro i
    rcases hparts i with ⟨a,b,p,hp,_,he⟩ | ⟨a,p,hp,he⟩
    · exact ⟨a,b,p,hp.isTrail,fun _ => hp,he⟩
    · exact ⟨a,a,p,hp.isTrail,fun h => False.elim (h rfl),he⟩
  choose a b p ht hp he using hw
  have hd' : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet := by
    simpa only [he] using hd
  have hc' : (⋃ i, (p i).edgeSet) = (evenAugmentation G).edgeSet := by
    simpa only [he] using hc
  let S : Finset (Option V) := Finset.univ.image some
  have hS : S.card = Fintype.card V := by
    simp only [S,Finset.card_image_of_injective _ (Option.some_injective V),Finset.card_univ]
  have ho : ∀ x ∈ S, Odd ((evenAugmentation G).degree x) := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact evenAugmentation_old_odd G y
  have hk' : 2 * Fintype.card (Fin k) ≤ S.card + 1 := by
    simpa only [Fintype.card_fin,Fintype.card_option,hS] using hk
  obtain ⟨hopen,hload⟩ := tight_odd_trail_partition (evenAugmentation G) S p ht hd' hc' ho hk'
  let P : Fin k → SimplePathPiece (evenAugmentation G) := fun i =>
    ⟨a i,b i,p i,hp i (hopen i)⟩
  have hload' : ∀ x : Option V, x ≠ none → (Finset.univ.filter fun i =>
      (P i).start = x ∨ (P i).finish = x).card ≤ 1 := by
    intro x hx
    cases x with
    | none => exact False.elim (hx rfl)
    | some x =>
      have h := hload (some x) (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)
      have hpred : (Finset.univ.filter fun i => a i ≠ b i ∧
          (some x = a i ∨ some x = b i)) =
          (Finset.univ.filter fun i => (P i).start = some x ∨ (P i).finish = some x) := by
        ext i
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,P]
        constructor
        · rintro ⟨_,hi⟩
          exact hi.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
        · intro hi
          exact ⟨hopen i,hi.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
      apply le_of_eq
      calc
        _ = _ := congrArg Finset.card hpred.symm
        _ = 1 := by
          convert h using 1
          congr 1
          ext i
          simp only [Finset.mem_filter,Finset.mem_univ,true_and]

  have hdel := SimplePathPiece.endpoint_partition_after_deletion P none hopen hd' hc' hload'
  exact endpoint_partition_mapIso (evenAugmentationOldIso G).symm hdel

end
end ErdosGallai

namespace ErdosGallai
noncomputable section

theorem lovasz_path_cycle_partition {V : Type cycleUniverse13} [Fintype V] (G : SimpleGraph V) :
    LovaszPathCyclePartition G := by
  classical
  obtain ⟨k,P,hd,hc,hk⟩ := Lovasz.path_cycle_partition G
  refine ⟨k,fun i => (P i).walk.edgeSet,?_,hd,hc,?_⟩
  · intro i
    rcases (P i).simple with hp | ⟨h,hcy⟩
    · exact Or.inl ⟨(P i).start,(P i).finish,(P i).walk,hp.1,hp.2,rfl⟩
    · exact Or.inr ⟨(P i).start,(P i).walk.copy rfl h,hcy,by simp⟩
  · exact hk.trans (Finset.card_le_univ _)

theorem endpoint_path_partition {V : Type cycleUniverse14} [Fintype V] (G : SimpleGraph V) :
    EndpointPathPartition G :=
  endpoint_partition_of_augmented_parts G (lovasz_path_cycle_partition (evenAugmentation G))

end
end ErdosGallai

end
end
/-! ### Upstream module `Combinatorics/CycleDecomposition/Decomposition.lean` -/

noncomputable section
noncomputable section
namespace ErdosGallai

def CycleOrSingleEdge {V : Type} (G : SimpleGraph V)
    (s : Set (Sym2 V)) : Prop :=
  (∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ s = p.edgeSet) ∨
  ∃ e ∈ G.edgeSet, s = {e}

def EdgeDecomposition {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ parts : Fin k → Set (Sym2 V),
    (∀ i, CycleOrSingleEdge G (parts i)) ∧
    Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
    (⋃ i, parts i) = G.edgeSet

noncomputable section
open _root_.SimpleGraph

lemma cycleOrSingleEdge_subset {V : Type} {G : SimpleGraph V}
    {s : Set (Sym2 V)} (hs : CycleOrSingleEdge G s) : s ⊆ G.edgeSet := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact p.edges_subset_edgeSet
  · simpa using he

lemma cycleOrSingleEdge_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) {s : Set (Sym2 V)}
    (hs : CycleOrSingleEdge G s) : CycleOrSingleEdge H (Sym2.map f '' s) := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact Or.inl ⟨f v,p.map f,hp.map hf,(p.edgeSet_map f).symm⟩
  · refine Or.inr ⟨Sym2.map f e, ?_, by simp⟩
    induction e using Sym2.ind with | _ x y =>
      exact f.map_adj he

lemma edgeDecomposition_of_indexed {V I : Type} [Fintype I] (G : SimpleGraph V)
    (parts : I → Set (Sym2 V)) (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hu : (⋃ i, parts i) = G.edgeSet) : EdgeDecomposition G (Fintype.card I) := by
  let e := Fintype.equivFin I
  refine ⟨fun j => parts (e.symm j), fun j => hp _, ?_, ?_⟩
  · intro i j hij
    exact hd (fun he => hij (e.symm.injective he))
  · ext x
    simp only [Set.mem_iUnion]
    rw [← hu]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨e i, by simpa using hi⟩

theorem edgeDecomposition_singleEdges {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (Nat.card G.edgeSet) := by
  classical
  let : Fintype G.edgeSet := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  apply edgeDecomposition_of_indexed G (fun e : G.edgeSet => {e.1})
  · intro e; exact Or.inr ⟨e.1,e.2,rfl⟩
  · intro e d hed
    exact Set.disjoint_singleton.mpr (fun h => hed (Subtype.ext h))
  · ext e; simp

theorem edgeDecomposition_assemble {V I : Type} [Fintype I] (G : SimpleGraph V)
    (W : I → Type) (H : ∀ i, SimpleGraph (W i))
    (f : ∀ i, H i →g G) (hf : ∀ i, Function.Injective (f i))
    (hdisj : Pairwise (fun i j =>
      Disjoint (Sym2.map (f i) '' (H i).edgeSet) (Sym2.map (f j) '' (H j).edgeSet)))
    (hcover : (⋃ i, Sym2.map (f i) '' (H i).edgeSet) = G.edgeSet)
    (k : I → ℕ) (hparts : ∀ i, EdgeDecomposition (H i) (k i)) :
    EdgeDecomposition G (∑ i, k i) := by
  classical
  choose parts hp hd hu using hparts
  let J := Σ i, Fin (k i)
  let P : J → Set (Sym2 V) := fun j => Sym2.map (f j.1) '' parts j.1 j.2
  have hpart : ∀ j, CycleOrSingleEdge G (P j) := by
    intro j; exact cycleOrSingleEdge_map (f j.1) (hf j.1) (hp j.1 j.2)
  have hsub : ∀ i a, parts i a ⊆ (H i).edgeSet := by
    intro i a; exact cycleOrSingleEdge_subset (hp i a)
  have hdisjP : Pairwise (fun i j => Disjoint (P i) (P j)) := by
    rintro ⟨i,a⟩ ⟨j,b⟩ hij
    by_cases h : i = j
    · subst j
      have hab : a ≠ b := fun he => hij (by cases he; rfl)
      apply Set.disjoint_left.mpr
      rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩
      have hxy : x = y := Sym2.map.injective (hf i) (he.trans he'.symm)
      subst y
      exact Set.disjoint_left.mp (hd i hab) hx hy
    · exact (hdisj h).mono (Set.image_mono (hsub i a)) (Set.image_mono (hsub j b))
  have hcoverP : (⋃ j, P j) = G.edgeSet := by
    rw [← hcover]
    ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨⟨i,a⟩,x,hx,he⟩
      exact ⟨i,x,hsub i a hx,he⟩
    · rintro ⟨i,x,hx,he⟩
      rw [← hu i] at hx
      obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hx
      exact ⟨⟨i,a⟩,x,ha,he⟩
  have hc : Fintype.card J = ∑ i, k i := by simp [J, Fintype.card_sigma]
  rw [← hc]
  exact edgeDecomposition_of_indexed G P hpart hdisjP hcoverP

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open _root_.Finset _root_.SimpleGraph
attribute [local instance] Classical.propDecidable

theorem small_residue (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G P : SimpleGraph V)
        [DecidableRel P.Adj], P ≤ G →
      D^(9/10:ℝ) ≤ (Fintype.card V:ℝ) →
      (Fintype.card V:ℝ) ≤ D^(51/50:ℝ) →
      Splitting.CutExpansion P (c*D^(9/10:ℝ)) →
      ∃ (k : ℕ) (parts : Fin k → Set (Sym2 V))
        (W : Fin 3 → Finset V) (H : Fin 3 → SimpleGraph V),
        (∀ i, CycleOrSingleEdge G (parts i)) ∧
        Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
        (∀ b, H b ≤ G ∧ (H b).support ⊆ (W b : Set V)) ∧
        (∀ b, (W b).card < Fintype.card V) ∧
        ((∑ b, (W b).card : ℕ):ℝ) ≤ η * Fintype.card V ∧
        Pairwise (fun b d => Disjoint (H b).edgeSet (H d).edgeSet) ∧
        (∀ b i, Disjoint (H b).edgeSet (parts i)) ∧
        ((⋃ i, parts i) ∪ (⋃ b, (H b).edgeSet)) = G.edgeSet ∧
        k ≤ 9 * Fintype.card V := by
  classical
  have ha : 0 < reservoirExpansionCoefficient c := by
    unfold reservoirExpansionCoefficient
    exact div_pos (lt_min hc (by norm_num)) (by norm_num)
  have hp : 0 < reservoirProbability η := by
    unfold reservoirProbability
    exact lt_min (div_pos hη (by norm_num)) (by norm_num)
  obtain ⟨D₁,hprep⟩ := reservoir_preparation c η hc hη
  obtain ⟨D₂,hD₂,hclose⟩ := uniform_three_reservoir_completion
    (reservoirExpansionCoefficient c) (reservoirProbability η) ha hp
  refine ⟨max D₁ D₂, hD₂.trans_le (le_max_right _ _), ?_⟩
  intro D hD V _ _ G P _ hPG hlo hhi hexp
  obtain ⟨ω,W,r,hPG',hPP,hPexp,hWW,hW2,hWsize,hWlt,hWsum,hWexp,hr,hrne,hcap⟩ :=
    hprep D ((le_max_left _ _).trans hD) V G P hPG hlo hhi hexp
  let P' := fun b => Splitting.colorGraph P ω b
  have hWW' : Pairwise fun b d => Disjoint (W b : Set V) (W d : Set V) := by
    intro b d hbd
    exact Finset.disjoint_coe.mpr (hWW b d hbd)
  let R := fun b => reservoirInternal (P' b) (W b)
  let T := fun b => R b ∪ (reservoirSpokes (W b) (r b) : Set (Sym2 V))
  let E : Set (Sym2 V) := ⋃ b, T b
  have hres := reservoir_reservations G P' W r hPG' hPP
    (fun b v hv t => (hr b v hv t).2)
  have hE : E ⊆ G.edgeSet := Set.iUnion_subset fun b =>
    Set.union_subset (hres.1 b).1 (hres.1 b).2
  let K := fun b => complementaryReservoirGraph (G.deleteEdges E)
    (fun b => (W b : Set V)) hWW' b
  have hK := complementary_reservoir_graphs (G.deleteEdges E)
    (fun b => (W b : Set V)) hWW'
  have hKG : ∀ b, K b ≤ G := fun b => (hK.1 b).trans (G.deleteEdges_le E)
  have hledger := complementary_reservation_ledger G (fun b => (W b : Set V)) hWW' E hE
  have hKT : ∀ b d, Disjoint (K b).edgeSet (T d) := fun b d =>
    (hledger.2.1 b).mono_right (Set.subset_iUnion T d)
  have hx : ∀ b : Fin 3, EndpointPathPartition (K b) := fun b => endpoint_path_partition (K b)
  choose k Q hQQ hQc hQl hQn using hx
  let x := fun b i => (Q b i).start
  let y := fun b i => (Q b i).finish
  let q : ∀ b i, G.Walk (x b i) (y b i) := fun b i => (Q b i).walk.mapLe (hKG b)
  have hqp : ∀ b i, (q b i).IsPath := fun b i => (Q b i).isPath.mapLe _
  have hql : ∀ b i, 0 < (q b i).length := by
    intro b i
    simpa [q] using (Q b i).positive
  have hqo : ∀ b i v, v ∈ (q b i).support → v ∉ W b := by
    intro b i v hv
    apply complementary_walk_outside (fun b => (W b : Set V)) hWW' b
      (Q b i).walk (Q b i).positive v
    simpa [q] using hv
  have hqd : ∀ b, Pairwise fun i j => Disjoint (q b i).edgeSet (q b j).edgeSet := by
    intro b i j hij
    simpa [q] using hQQ b hij
  have hqc : ∀ b, (⋃ i, (q b i).edgeSet) = (K b).edgeSet := by
    intro b
    simpa [q] using hQc b
  obtain ⟨C,hCy,hCC,hCsub,hcover,hcount⟩ := hclose D ((le_max_right _ _).trans hD)
    V G P' K hPG' hPP W r hWexp hW2 hhi hr hrne hcap
    hledger.1 hKT (fun b => Fin (k b)) x y q hqp hql hqo hqd hqc
      (by
        intro b v
        dsimp only [endpointLoad,x,y]
        convert hQl b v using 2
        ext i
        simp)
  let I := Σ b, Fin (k b)
  let CE : I → Set (Sym2 V) := fun z => (C z.1 z.2).edgeSet
  have hCE : ∀ i, CE i ⊆ G.edgeSet := fun i => (C i.1 i.2).edges_subset_edgeSet
  have hEeq : E = (⋃ b, R b) ∪ (allReservoirSpokes W r : Set _) := by
    simp only [E,T,coe_allReservoirSpokes,Set.iUnion_union_distrib]
  have hcov : G.edgeSet \ ((⋃ b, R b) ∪ (allReservoirSpokes W r : Set _)) ⊆
      completedEdges CE := by
    rw [← hEeq, ← SimpleGraph.edgeSet_deleteEdges, ← hK.2.2.2]
    exact hcover
  obtain ⟨hsupp,hind,hHe,hHH,hHC,hHS,hCS,hu,hnum⟩ :=
    three_reservoir_remainder G P' W r hPG' hPP
      (fun b v hv t => (hr b v hv t).2) CE hCE hCC hcount hcov
  let H := residualInternalGraph G R CE
  let S := unusedSpokes (↑(allReservoirSpokes W r)) CE
  let J := I ⊕ S
  let parts : J → Set (Sym2 V) := Sum.elim CE (fun e => {e.val})
  have hSsub : (S : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he
    have hh : e ∈ (allReservoirSpokes W r : Set _) := by
      have hh := he
      simp only [Finset.mem_coe,S,unusedSpokes,Set.mem_toFinset,Set.mem_sdiff] at hh
      exact hh.1
    exact hE (by rw [hEeq]; exact Or.inr hh)
  have hpart : ∀ j, CycleOrSingleEdge G (parts j) := by
    intro j
    rcases j with i | e
    · exact Or.inl ⟨x i.1 i.2,C i.1 i.2,hCy i.1 i.2,rfl⟩
    · exact Or.inr ⟨e.val,hSsub e.property,rfl⟩
  have hpd : Pairwise fun i j => Disjoint (parts i) (parts j) := by
    intro i j hij
    rcases i with i | e <;> rcases j with j | f
    · exact hCC (fun h => hij (congrArg Sum.inl h))
    · exact (hCS i).mono_right (Set.singleton_subset_iff.mpr f.property)
    · exact (hCS j).symm.mono_left (Set.singleton_subset_iff.mpr e.property)
    · exact Set.disjoint_singleton.mpr (fun h => hij (congrArg Sum.inr (Subtype.ext h)))
  have hpartU : (⋃ j, parts j) = completedEdges CE ∪ (S : Set (Sym2 V)) := by
    ext e
    simp only [Set.mem_iUnion, Set.mem_union, completedEdges, parts]
    constructor
    · rintro ⟨i,hi⟩
      rcases i with i | f
      · exact Or.inl ⟨i,hi⟩
      · exact Or.inr ((Set.mem_singleton_iff.mp hi) ▸ f.property)
    · rintro (⟨i,hi⟩ | he)
      · exact ⟨Sum.inl i,hi⟩
      · exact ⟨Sum.inr ⟨e,he⟩,rfl⟩
  let equiv := Fintype.equivFin J
  refine ⟨Fintype.card J,fun i => parts (equiv.symm i),W,H,?_,?_,?_,hWlt,hWsum,
    hHH,?_,?_,?_⟩
  · exact fun i => hpart _
  · intro i j hij
    exact hpd (fun h => hij (equiv.symm.injective h))
  · intro b
    refine ⟨?_,hsupp b⟩
    exact edgeRestriction_le G _
  · intro b i
    rcases hji : equiv.symm i with j | e
    all_goals simp only [hji, parts, Sum.elim_inl, Sum.elim_inr]
    · exact hHC b j
    · exact (hHS b).mono_right (Set.singleton_subset_iff.mpr e.property)
  · have he : (⋃ i, parts (equiv.symm i)) = ⋃ j, parts j := by
      ext e
      simp only [Set.mem_iUnion]
      exact ⟨fun ⟨i,hi⟩ => ⟨equiv.symm i,hi⟩,
        fun ⟨j,hj⟩ => ⟨equiv j,by simpa using hj⟩⟩
    rw [he,hpartU]
    exact hu
  · simpa only [J,Fintype.card_sum,Fintype.card_coe] using hnum

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open _root_.SimpleGraph _root_.Finset
attribute [local instance] Classical.propDecidable

def decompositionCost {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.find (show ∃ k, EdgeDecomposition G k from ⟨_,edgeDecomposition_singleEdges G⟩)

lemma decompositionCost_spec {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (decompositionCost G) := Nat.find_spec _

lemma decompositionCost_le {V : Type} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : EdgeDecomposition G k) : decompositionCost G ≤ k := Nat.find_min' _ h

theorem edgeDecomposition_adjoin {V I J : Type} [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) (H : ∀ j, SimpleGraph (W j)) (f : ∀ j, H j →g G)
    (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet)
    (k : J → ℕ) (hD : ∀ j, EdgeDecomposition (H j) (k j)) :
    EdgeDecomposition G (Fintype.card I + ∑ j, k j) := by
  classical
  choose P hP hPd hPc using hD
  let R : (I ⊕ Σ j, Fin (k j)) → Set (Sym2 V) :=
    Sum.elim parts (fun z => Sym2.map (f z.1) '' P z.1 z.2)
  have hsub : ∀ j i, P j i ⊆ (H j).edgeSet := fun j i => cycleOrSingleEdge_subset (hP j i)
  have hRp : ∀ z, CycleOrSingleEdge G (R z) := by
    intro z
    rcases z with z | ⟨j,i⟩
    · exact hp z
    · exact cycleOrSingleEdge_map (f j) (hf j) (hP j i)
  have hRd : Pairwise fun z t => Disjoint (R z) (R t) := by
    intro z t hzt
    rcases z with z | ⟨j,i⟩ <;> rcases t with t | ⟨l,a⟩
    · exact hd (fun h => hzt (congrArg Sum.inl h))
    · exact ((hHP l z).mono_left (Set.image_mono (hsub l a))).symm
    · exact (hHP j t).mono_left (Set.image_mono (hsub j i))
    · by_cases hjl : j = l
      · subst l
        have hia : i ≠ a := fun h => hzt (by cases h; rfl)
        apply Set.disjoint_left.mpr
        rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩
        have hxy := Sym2.map.injective (hf j) (he.trans he'.symm)
        subst y
        exact Set.disjoint_left.mp (hPd j hia) hx hy
      · exact (hHH hjl).mono (Set.image_mono (hsub j i)) (Set.image_mono (hsub l a))
  have hRu : (⋃ z, R z) = G.edgeSet := by
    rw [← hu]
    ext e
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨z,hz⟩
      rcases z with z | ⟨j,i⟩
      · exact Or.inl ⟨z,hz⟩
      · obtain ⟨x,hx,he⟩ := hz
        exact Or.inr ⟨j,x,hsub j i hx,he⟩
    · rintro (⟨i,hi⟩ | ⟨j,x,hx,he⟩)
      · exact ⟨Sum.inl i,hi⟩
      · rw [← hPc j] at hx
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
        exact ⟨Sum.inr ⟨j,i⟩,x,hi,he⟩
  simpa only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin] using
    edgeDecomposition_of_indexed G R hRp hRd hRu

lemma decompositionCost_adjoin {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) [∀ j, Fintype (W j)] (H : ∀ j, SimpleGraph (W j))
    (f : ∀ j, H j →g G) (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) :=
  decompositionCost_le (edgeDecomposition_adjoin G parts hp hd W H f hf hHH hHP hu _
    (fun j => decompositionCost_spec (H j)))

end
end ErdosGallai
namespace ErdosGallai
noncomputable section
open _root_.SimpleGraph _root_.Finset
attribute [local instance] Classical.propDecidable

lemma edgeDecomposition_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : H →g G) (hf : Function.Injective f)
    (hu : Sym2.map f '' H.edgeSet = G.edgeSet) {k : ℕ} (hk : EdgeDecomposition H k) :
    EdgeDecomposition G k := by
  have := edgeDecomposition_assemble (I := Unit) G (fun _ : Unit => W) (fun _ => H) (fun _ => f)
    (fun _ => hf) (by intro i j hij; exact False.elim (hij (Subsingleton.elim _ _)))
    (by rw [Set.iUnion_const]; exact hu) (fun _ => k) (fun _ => hk)
  simpa using this

lemma decompositionCost_on {V : Type} [Fintype V] (G : SimpleGraph V)
    (A : Finset V) (hA : ∀ ⦃x y⦄, G.Adj x y → x ∈ A ∧ y ∈ A) :
    decompositionCost G ≤ decompositionCost (G.induce (A:Set V)) := by
  classical
  let f : G.induce (A:Set V) →g G := ⟨Subtype.val,fun h => h⟩
  have hu : Sym2.map f '' (G.induce (A:Set V)).edgeSet = G.edgeSet := by
    ext e
    constructor
    · rintro ⟨e,he,rfl⟩
      induction e using Sym2.ind with | _ x y => exact he
    · intro he
      induction e using Sym2.ind with
      | _ x y =>
        exact ⟨s(⟨x,(hA he).1⟩,⟨y,(hA he).2⟩),he,rfl⟩
  exact decompositionCost_le (edgeDecomposition_map f Subtype.val_injective hu (decompositionCost_spec _))

end
end ErdosGallai
namespace ErdosGallai
noncomputable section
open _root_.SimpleGraph _root_.Finset
attribute [local instance] Classical.propDecidable

lemma decompositionCost_adjoin_same {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (H : J → SimpleGraph V) (hHG : ∀ j, H j ≤ G)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hHP : ∀ j i, Disjoint (H j).edgeSet (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) := by
  let f : ∀ j, H j →g G := fun j => ⟨id,fun h => hHG j h⟩
  have he (j) : Sym2.map (f j) '' (H j).edgeSet = (H j).edgeSet := by
    have hf : (f j : V → V) = id := rfl
    rw [hf, Sym2.map_id, Set.image_id]
  apply decompositionCost_adjoin G parts hp hd (fun _ => V) H f (fun _ => Function.injective_id)
  · simpa only [he] using hHH
  · simpa only [he] using hHP
  · simpa only [he] using hu

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open _root_.SimpleGraph _root_.Finset
attribute [local instance] Classical.propDecidable

theorem uniform_piece_cost (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, ∀ (n : ℕ) (C : ℝ), 0 ≤ C →
      (∀ (W : Type) [Fintype W] (H : SimpleGraph W), Fintype.card W < n →
        (decompositionCost H:ℝ) ≤ C * Fintype.card W) →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G P : SimpleGraph V)
        [DecidableRel P.Adj], P ≤ G → Fintype.card V ≤ n →
      D^(9/10:ℝ) ≤ (Fintype.card V:ℝ) →
      (Fintype.card V:ℝ) ≤ D^(51/50:ℝ) →
      Splitting.CutExpansion P (c*D^(9/10:ℝ)) →
      (decompositionCost G:ℝ) ≤ (9+C*η)*Fintype.card V := by
  obtain ⟨D₀,hD₀,hres⟩ := small_residue c η hc hη
  refine ⟨D₀,hD₀,?_⟩
  intro D hD n C hC ih V _ _ G P _ hPG hn hlo hhi he
  obtain ⟨k,parts,W,H,hp,hd,hHG,hWlt,hWsum,hHH,hHP,hu,hk⟩ :=
    hres D hD V G P hPG hlo hhi he
  have hcost (b : Fin 3) : (decompositionCost (H b):ℝ) ≤ C * (W b).card := by
    have hA : ∀ ⦃x y⦄, (H b).Adj x y → x ∈ W b ∧ y ∈ W b := by
      intro x y hxy
      exact ⟨(hHG b).2 ⟨y,hxy⟩,(hHG b).2 ⟨x,hxy.symm⟩⟩
    calc
      _ ≤ (decompositionCost ((H b).induce (W b:Set V)):ℝ) :=
        Nat.cast_le.mpr (decompositionCost_on _ _ hA)
      _ ≤ C * Fintype.card (W b:Set V) := ih _ _ (by simpa using (hWlt b).trans_le hn)
      _ = _ := by simp
  have htot := decompositionCost_adjoin_same G parts hp hd H (fun b => (hHG b).1) hHH hHP hu
  have hsum : (∑ b, (decompositionCost (H b):ℝ)) ≤ C * ∑ b, ((W b).card:ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun b _ => hcost b)
  have hsum' := mul_le_mul_of_nonneg_left hWsum hC
  have hk' : (k:ℝ) ≤ 9 * Fintype.card V := by exact_mod_cast hk
  have htot' : (decompositionCost G:ℝ) ≤ k + ∑ b, (decompositionCost (H b):ℝ) := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_sum] using (Nat.cast_le.mpr htot : (decompositionCost G:ℝ) ≤ _)
  push_cast at hsum'
  nlinarith

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable

theorem uniform_piece_cost_on (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, ∀ (n : ℕ) (C : ℝ), 0 ≤ C →
      (∀ (W : Type) [Fintype W] (H : SimpleGraph W), Fintype.card W < n →
        (decompositionCost H:ℝ) ≤ C * Fintype.card W) →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G P : SimpleGraph V)
        [DecidableRel P.Adj] (A : Finset V), P ≤ G → A.card ≤ n →
      (∀ ⦃x y⦄, G.Adj x y → x ∈ A ∧ y ∈ A) →
      D^(9/10:ℝ) ≤ (A.card:ℝ) → (A.card:ℝ) ≤ D^(51/50:ℝ) →
      CutExpansionOn P A (c*D^(9/10:ℝ)) →
      (decompositionCost G:ℝ) ≤ (9+C*η)*A.card := by
  obtain ⟨D₀,hD₀,hcost⟩ := uniform_piece_cost c η hc hη
  refine ⟨D₀,hD₀,?_⟩
  intro D hD n C hC ih V _ _ G P _ A hPG hn hA hlo hhi he
  have hcost' := hcost D hD n C hC ih (A:Set V) (G.induce (A:Set V))
    (P.induce (A:Set V)) (fun _ _ h => hPG h) (by simpa using hn)
    (by simpa using hlo) (by simpa using hhi) (cutExpansion_induce P A _ he)
  calc
    _ ≤ (decompositionCost (G.induce (A:Set V)):ℝ) := Nat.cast_le.mpr (decompositionCost_on G A hA)
    _ ≤ _ := by simpa using hcost'

end
end ErdosGallai

end
end
/-! ### Upstream module `Combinatorics/CycleDecomposition/BatchLovasz.lean` -/

noncomputable section
namespace ErdosGallai.Batch.Lovasz
noncomputable section
open _root_.SimpleGraph
attribute [local instance] Classical.propDecidable

def StarActive {V : Type cycleUniverse1} (S : Set V) (R : V → V → Prop) (v : V) : Prop :=
  ∃ a ∈ S, Relation.ReflTransGen R a v

lemma starActive_source {V : Type cycleUniverse2} {S : Set V} {R : V → V → Prop}
    {v : V} (hv : v ∈ S) : StarActive S R v :=
  ⟨v, hv, .refl⟩

lemma starActive_step {V : Type cycleUniverse3} {S : Set V} {R : V → V → Prop}
    {v w : V} (hv : StarActive S R v) (h : R v w) : StarActive S R w := by
  obtain ⟨a, ha, hr⟩ := hv
  exact ⟨a, ha, hr.tail h⟩

lemma starActive_iff {V : Type cycleUniverse4} {S : Set V} {R : V → V → Prop} {v : V} :
    StarActive S R v ↔ v ∈ S ∨ ∃ w, StarActive S R w ∧ R w v := by
  constructor
  · rintro ⟨a, ha, hr⟩
    rcases hr.cases_tail with rfl | ⟨w, hw, h⟩
    · exact Or.inl ha
    · exact Or.inr ⟨w, ⟨a, ha, hw⟩, h⟩
  · rintro (h | ⟨w, hw, h⟩)
    · exact starActive_source h
    · exact starActive_step hw h

lemma starActive_subset {V : Type cycleUniverse6} {S T : Set V} {R : V → V → Prop}
    (hS : S ⊆ T) (hR : ∀ a b, R a b → b ∈ T) :
    {v | StarActive S R v} ⊆ T := by
  rintro v ⟨a, ha, hr⟩
  rcases hr.cases_tail with rfl | ⟨w, _, h⟩
  · exact hS ha
  · exact hR w v h

lemma star_inj {V : Type cycleUniverse8} {x a b : V} : s(x,a) = s(x,b) ↔ a = b := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, h'⟩)
    · exact h
    · exact h'.trans h
  · intro h; exact Or.inl ⟨rfl, h⟩

structure PathPiece {V : Type cycleUniverse9} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  positive : 0 < walk.length

lemma PathPiece.ends_ne {V : Type cycleUniverse10} {G : SimpleGraph V} (P : PathPiece G) :
    P.start ≠ P.finish := by
  intro h
  have hz := (P.isPath.nil_iff_eq.mpr h).length_eq_zero
  have := P.positive
  omega

structure Piece {V : Type cycleUniverse11} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  simple : (walk.IsPath ∧ 0 < walk.length) ∨
    ∃ h : finish = start, (walk.copy rfl h).IsCycle

namespace Piece
variable {V : Type cycleUniverse12} {G : SimpleGraph V}

def ofPath (p : PathPiece G) : Piece G :=
  ⟨p.start, p.finish, p.walk, Or.inl ⟨p.isPath, p.positive⟩⟩

def ofCycle {v : V} (p : G.Walk v v) (h : p.IsCycle) : Piece G :=
  ⟨v, v, p, Or.inr ⟨rfl, h⟩⟩

end Piece

structure Arm {V : Type cycleUniverse13} (G : SimpleGraph V) (x : V) where
  near : V
  far : V
  adj : G.Adj x near
  walk : G.Walk near far
  isPath : walk.IsPath
  avoids : x ∉ walk.support

namespace Arm
variable {V : Type cycleUniverse14} {G : SimpleGraph V} {x : V}

def tip (A : Arm G x) : PathPiece G where
  start := x
  finish := A.far
  walk := .cons A.adj A.walk
  isPath := A.isPath.cons A.avoids
  positive := by simp

def flip (A : Arm G x) (h : G.Adj x A.far) : Arm G x where
  near := A.far
  far := A.near
  adj := h
  walk := A.walk.reverse
  isPath := A.isPath.reverse
  avoids := by simpa using A.avoids

@[simp] lemma flip_edges (A : Arm G x) (h : G.Adj x A.far) :
    (A.flip h).walk.edgeSet = A.walk.edgeSet := by simp [flip]

@[simp] lemma mem_flip_support (A : Arm G x) (h : G.Adj x A.far) (v : V) :
    v ∈ (A.flip h).walk.support ↔ v ∈ A.walk.support := by simp [flip]

lemma two_arms_isPath (A B : Arm G x)
    (hd : A.walk.support.Disjoint B.walk.support) :
    ((Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)).IsPath := by
  apply Walk.IsPath.mk'
  simp only [Walk.support_append, Walk.support_reverse, Walk.support_cons,
    List.tail_cons, List.reverse_cons, List.append_assoc]
  apply List.nodup_append'.mpr
  refine ⟨List.nodup_reverse.mpr A.isPath.support_nodup, ?_, ?_⟩
  · exact List.nodup_cons.mpr ⟨B.avoids, B.isPath.support_nodup⟩
  · rw [List.disjoint_left]
    intro v hv hq
    have hav : v ∈ A.walk.support := List.mem_reverse.mp hv
    rcases List.mem_cons.mp hq with rfl | hq
    · exact A.avoids hav
    · exact List.disjoint_left.mp hd hav hq

def join (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support) : PathPiece G where
  start := A.far
  finish := B.far
  walk := (Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)
  isPath := two_arms_isPath A B hd
  positive := by simp only [Walk.length_append, Walk.length_reverse, Walk.length_cons]; omega

lemma join_edges (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support) :
    (A.join B hd).walk.edgeSet =
      A.walk.edgeSet ∪ B.walk.edgeSet ∪ {s(x,A.near), s(x,B.near)} := by
  simp only [join, Walk.edgeSet_append, Walk.edgeSet_reverse, Walk.edgeSet_cons]
  ext e
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

lemma near_ne (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support) :
    A.near ≠ B.near := by
  intro h
  exact List.disjoint_left.mp hd A.walk.start_mem_support (by simpa only [h] using B.walk.start_mem_support)

lemma far_ne_center (A : Arm G x) : A.far ≠ x := by
  intro h
  apply A.avoids
  simpa only [h] using A.walk.end_mem_support

lemma star_not_mem (A : Arm G x) (v : V) : s(x,v) ∉ A.walk.edgeSet := by
  intro he
  exact A.avoids (Walk.mem_support_iff_exists_mem_edges.mpr
    (Or.inr ⟨s(x,v), he, by simp⟩))

def orient (A : Arm G x) (active : Prop) (h : active → G.Adj x A.far) : Arm G x :=
  if ha : active then A.flip (h ha) else A

@[simp] lemma orient_edges (A : Arm G x) (active : Prop) (h : active → G.Adj x A.far) :
    (A.orient active h).walk.edgeSet = A.walk.edgeSet := by
  by_cases ha : active
  · exact (congrArg (fun B : Arm G x => B.walk.edgeSet)
      (show A.orient active h = A.flip (h ha) from dite_eq_left ha)).trans (A.flip_edges _)
  · exact congrArg (fun B : Arm G x => B.walk.edgeSet)
      (show A.orient active h = A from dite_eq_right ha)

@[simp] lemma orient_near (A : Arm G x) (active : Prop) (h : active → G.Adj x A.far) :
    (A.orient active h).near = if active then A.far else A.near := by
  by_cases ha : active <;> simp [orient, flip, ha]

@[simp] lemma mem_orient_support (A : Arm G x) (active : Prop)
    (h : active → G.Adj x A.far) (v : V) :
    v ∈ (A.orient active h).walk.support ↔ v ∈ A.walk.support := by
  by_cases ha : active
  · exact (congrArg (fun B : Arm G x => v ∈ B.walk.support)
      (show A.orient active h = A.flip (h ha) from dite_eq_left ha)).to_iff.trans
        (A.mem_flip_support _ v)
  · exact (congrArg (fun B : Arm G x => v ∈ B.walk.support)
      (show A.orient active h = A from dite_eq_right ha)).to_iff

lemma orient_disjoint (A B : Arm G x) (p q : Prop)
    (ha : p → G.Adj x A.far) (hb : q → G.Adj x B.far)
    (hd : A.walk.support.Disjoint B.walk.support) :
    (A.orient p ha).walk.support.Disjoint (B.orient q hb).walk.support := by
  rw [List.disjoint_left]
  intro v hv hw
  exact List.disjoint_left.mp hd ((A.mem_orient_support p ha v).mp hv)
    ((B.mem_orient_support q hb v).mp hw)

end Arm

inductive Frame {V : Type cycleUniverse15} (G : SimpleGraph V) (x : V) where
  | away (p : PathPiece G) (avoid : x ∉ p.walk.support)
  | tip (A : Arm G x)
  | through (A B : Arm G x) (disjoint : A.walk.support.Disjoint B.walk.support)

namespace Frame
variable {V : Type cycleUniverse16} {G : SimpleGraph V} {x : V}

def path : Frame G x → PathPiece G
  | .away p _ => p
  | .tip A => A.tip
  | .through A B hd => A.join B hd

def Port : Frame G x → Type
  | .away _ _ => Bool
  | .tip _ => Unit
  | .through _ _ _ => Bool

def endpoint : (F : Frame G x) → F.Port → V
  | .away p _, false => p.start
  | .away p _, true => p.finish
  | .tip A, _ => A.far
  | .through A _ _, false => A.far
  | .through _ B _, true => B.far

def exit : (F : Frame G x) → F.Port → Option V
  | .away _ _, _ => none
  | .tip _, _ => none
  | .through A _ _, false => some A.near
  | .through _ B _, true => some B.near

def inserted (F : Frame G x) (active : F.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ e = s(x, F.endpoint p)}

def removed (F : Frame G x) (active : F.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ ∃ v, F.exit p = some v ∧ e = s(x,v)}

lemma endpoint_ne_center (F : Frame G x) (p : F.Port) : F.endpoint p ≠ x := by
  cases F with
  | away P hx =>
    cases p
    · change P.start ≠ x
      intro h; apply hx; simpa only [← h] using P.walk.start_mem_support
    · change P.finish ≠ x
      intro h; apply hx; simpa only [← h] using P.walk.end_mem_support
  | tip A => exact A.far_ne_center
  | through A B hd => cases p <;> exact Arm.far_ne_center _

lemma port_iff_endpoint (F : Frame G x) (v : V) :
    (∃ p : F.Port, F.endpoint p = v) ↔
      (F.path.start = v ∨ F.path.finish = v) ∧ v ≠ x := by
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨?_, (F.endpoint_ne_center p)⟩
    cases F with
    | away P hx => cases p <;> simp [endpoint, path]
    | tip A => exact Or.inr rfl
    | through A B hd => cases p <;> simp [endpoint, path, Arm.join]
  · rintro ⟨he, hx⟩
    cases F with
    | away P hp =>
      rcases he with he | he
      · exact ⟨false, he⟩
      · exact ⟨true, he⟩
    | tip A =>
      rcases he with he | he
      · exact (hx he.symm).elim
      · exact ⟨(), he⟩
    | through A B hd =>
      rcases he with he | he
      · exact ⟨false, he⟩
      · exact ⟨true, he⟩

lemma exit_edge (F : Frame G x) (p : F.Port) (v : V) (h : F.exit p = some v) :
    s(x,v) ∈ F.path.walk.edgeSet := by
  cases F with
  | away P hx => cases h
  | tip A => cases h
  | through A B hd =>
    cases p
    · cases h
      rw [path, Arm.join_edges]
      exact Or.inr (by simp)
    · cases h
      rw [path, Arm.join_edges]
      exact Or.inr (by simp)

@[simp] lemma removed_away (P : PathPiece G) (hx : x ∉ P.walk.support)
    (active : (Frame.away P hx).Port → Prop) :
    (Frame.away P hx).removed active = ∅ := by
  ext e; simp [removed, exit]

@[simp] lemma removed_tip (A : Arm G x) (active : (Frame.tip A).Port → Prop) :
    (Frame.tip A).removed active = ∅ := by
  ext e; simp [removed, exit]

lemma inserted_away (P : PathPiece G) (hx : x ∉ P.walk.support)
    (active : (Frame.away P hx).Port → Prop) :
    (Frame.away P hx).inserted active =
      (if active false then {s(x,P.start)} else ∅) ∪
      (if active true then {s(x,P.finish)} else ∅) := by
  ext e
  by_cases h0 : active false <;> by_cases h1 : active true <;>
    simp [inserted, endpoint, Port, Bool.exists_bool, h0, h1, or_comm]

lemma inserted_tip (A : Arm G x) (active : (Frame.tip A).Port → Prop) :
    (Frame.tip A).inserted active = if active () then {s(x,A.far)} else ∅ := by
  ext e
  by_cases h : active () <;> simp [inserted, endpoint, Port, h]

lemma inserted_through (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support)
    (active : (Frame.through A B hd).Port → Prop) :
    (Frame.through A B hd).inserted active =
      (if active false then {s(x,A.far)} else ∅) ∪
      (if active true then {s(x,B.far)} else ∅) := by
  ext e
  by_cases h0 : active false <;> by_cases h1 : active true <;>
    simp [inserted, endpoint, Port, Bool.exists_bool, h0, h1, or_comm]

lemma removed_through (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support)
    (active : (Frame.through A B hd).Port → Prop) :
    (Frame.through A B hd).removed active =
      (if active false then {s(x,A.near)} else ∅) ∪
      (if active true then {s(x,B.near)} else ∅) := by
  ext e
  by_cases h0 : active false <;> by_cases h1 : active true <;>
    simp [removed, exit, Port, Bool.exists_bool, h0, h1, or_comm]

end Frame

lemma replace_two_attachments {E : Type cycleUniverse17} (B : Set E) (e f a b : E)
    (he : e ∉ B) (hf : f ∉ B) (hne : e ≠ f) (p q : Prop) [Decidable p] [Decidable q] :
    ((B ∪ {e,f}) \ ((if p then {e} else ∅) ∪ (if q then {f} else ∅))) ∪
      ((if p then {a} else ∅) ∪ (if q then {b} else ∅)) =
      B ∪ {if p then a else e, if q then b else f} := by
  classical
  ext z
  by_cases hp : p <;> by_cases hq : q <;>
    simp only [hp, hq, ↓reduceIte, Set.mem_union, Set.mem_sdiff, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_empty_iff_false] <;> aesop

namespace Frame
variable {V : Type cycleUniverse18} {G : SimpleGraph V} {x : V}

lemma modify_through (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support)
    (active : (Frame.through A B hd).Port → Prop)
    (hadj : ∀ p, active p → G.Adj x ((Frame.through A B hd).endpoint p)) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      ((Frame.through A B hd).path.walk.edgeSet \ (Frame.through A B hd).removed active) ∪
        (Frame.through A B hd).inserted active := by
  have ha : active false → G.Adj x A.far := hadj false
  have hb : active true → G.Adj x B.far := hadj true
  let A' := A.orient (active false) ha
  let B' := B.orient (active true) hb
  have hd' : A'.walk.support.Disjoint B'.walk.support :=
    A.orient_disjoint B _ _ _ _ hd
  refine ⟨Piece.ofPath (A'.join B' hd'), ?_⟩
  have he : s(x,A.near) ∉ A.walk.edgeSet ∪ B.walk.edgeSet := by
    rintro (he | he)
    · exact A.star_not_mem _ he
    · exact B.star_not_mem _ he
  have hf : s(x,B.near) ∉ A.walk.edgeSet ∪ B.walk.edgeSet := by
    rintro (he | he)
    · exact A.star_not_mem _ he
    · exact B.star_not_mem _ he
  have hne : s(x,A.near) ≠ s(x,B.near) := fun h => A.near_ne B hd (star_inj.mp h)
  change (A'.join B' hd').walk.edgeSet = _
  rw [inserted_through, removed_through]
  change (A'.join B' hd').walk.edgeSet = ((A.join B hd).walk.edgeSet \ _) ∪ _
  rw [Arm.join_edges, Arm.join_edges]
  dsimp only [A', B']
  simp only [Arm.orient_edges, Arm.orient_near]
  have hh := (replace_two_attachments _ _ _ s(x,A.far) s(x,B.far) he hf hne
    (active false) (active true)).symm
  by_cases h0 : active false <;> by_cases h1 : active true
  · simpa [h0, h1] using hh
  · simpa [h0, h1] using hh
  · simpa [h0, h1] using hh
  · simp [h0, h1]

lemma modify_tip (A : Arm G x) (active : (Frame.tip A).Port → Prop)
    (hadj : ∀ p, active p → G.Adj x ((Frame.tip A).endpoint p))
    (hnew : ∀ p, active p → s(x,(Frame.tip A).endpoint p) ∉
      (Frame.tip A).path.walk.edgeSet) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      ((Frame.tip A).path.walk.edgeSet \ (Frame.tip A).removed active) ∪
        (Frame.tip A).inserted active := by
  rw [removed_tip, inserted_tip, Set.sdiff_empty]
  by_cases ha : active ()
  · have haG : G.Adj x A.far := hadj () ha
    have he : s(A.far,x) ∉ A.tip.walk.edges := by
      intro he
      exact hnew () ha (Sym2.eq_swap ▸ he)
    let c : G.Walk A.far A.far := Walk.cons haG.symm A.tip.walk
    have hc : c.IsCycle := Path.cons_isCycle ⟨A.tip.walk,A.tip.isPath⟩ _ he
    refine ⟨Piece.ofCycle c hc, ?_⟩
    change c.edgeSet = _
    dsimp only [c, Arm.tip, path]
    simp only [Walk.edgeSet_cons, ha, ↓reduceIte]
    rw [Sym2.eq_swap]
    ext e
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
    tauto
  · refine ⟨Piece.ofPath A.tip, ?_⟩
    simp [Piece.ofPath, path, ha]

lemma modify_away (P : PathPiece G) (hx : x ∉ P.walk.support)
    (active : (Frame.away P hx).Port → Prop)
    (hadj : ∀ p, active p → G.Adj x ((Frame.away P hx).endpoint p)) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      ((Frame.away P hx).path.walk.edgeSet \ (Frame.away P hx).removed active) ∪
        (Frame.away P hx).inserted active := by
  rw [removed_away, inserted_away, Set.sdiff_empty]
  change ∃ Q : Piece G, Q.walk.edgeSet = P.walk.edgeSet ∪ _
  by_cases h0 : active false
  · have h0G : G.Adj x P.start := hadj false h0
    let q : G.Walk x P.finish := Walk.cons h0G P.walk
    have hq : q.IsPath := P.isPath.cons hx
    by_cases h1 : active true
    · have he : s(P.finish,x) ∉ q.edges := by
        intro he
        have hh := hq.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
        have hp := P.positive
        simp only [q, Walk.length_cons] at hh
        omega
      have h1G : G.Adj x P.finish := hadj true h1
      let c : G.Walk P.finish P.finish := Walk.cons h1G.symm q
      have hc : c.IsCycle := Path.cons_isCycle ⟨q,hq⟩ _ he
      refine ⟨Piece.ofCycle c hc, ?_⟩
      change c.edgeSet = _
      simp only [c, q, Walk.edgeSet_cons, h0, h1, ↓reduceIte]
      rw [Sym2.eq_swap]
      ext e
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
    · let Q : PathPiece G := ⟨x, P.finish, q, hq, by simp [q]⟩
      refine ⟨Piece.ofPath Q, ?_⟩
      change q.edgeSet = _
      simp only [q, Walk.edgeSet_cons, h0, h1, ↓reduceIte, Set.union_empty]
      ext e
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
  · by_cases h1 : active true
    · have h1G : G.Adj x P.finish := hadj true h1
      let q : G.Walk x P.start := Walk.cons h1G P.walk.reverse
      have hq : q.IsPath := P.isPath.reverse.cons (by simpa using hx)
      let Q : PathPiece G := ⟨x, P.start, q, hq, by simp [q]⟩
      refine ⟨Piece.ofPath Q, ?_⟩
      change q.edgeSet = _
      simp only [q, Walk.edgeSet_cons, Walk.edgeSet_reverse, h0, h1, ↓reduceIte,
        Set.empty_union]
      ext e
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
    · refine ⟨Piece.ofPath P, ?_⟩
      simp [Piece.ofPath, h0, h1]

theorem modify (F : Frame G x) (active : F.Port → Prop)
    (hadj : ∀ p, active p → G.Adj x (F.endpoint p))
    (hnew : ∀ p, active p → F.exit p = none → s(x,F.endpoint p) ∉ F.path.walk.edgeSet) :
    ∃ Q : Piece G, Q.walk.edgeSet = (F.path.walk.edgeSet \ F.removed active) ∪
      F.inserted active := by
  cases F with
  | away P hx => exact modify_away P hx active hadj
  | through A B hd => exact modify_through A B hd active hadj
  | tip A => exact modify_tip A active hadj (fun p hp => hnew p hp rfl)

end Frame

theorem rewire_partition {E : Type cycleUniverse19} {I : Type cycleUniverse20} (old remove add : I → Set E) (fresh : Set E)
    (hsub : ∀ i, remove i ⊆ old i)
    (hold : Pairwise fun i j => Disjoint (old i) (old j))
    (hadd : Pairwise fun i j => Disjoint (add i) (add j))
    (hfresh : Disjoint fresh (⋃ i, old i))
    (hbalance : (⋃ i, add i) = (⋃ i, remove i) ∪ fresh) :
    Pairwise (fun i j => Disjoint ((old i \ remove i) ∪ add i)
      ((old j \ remove j) ∪ add j)) ∧
    (⋃ i, ((old i \ remove i) ∪ add i)) = (⋃ i, old i) ∪ fresh := by
  have hcross : ∀ i j, Disjoint (old i \ remove i) (add j) := by
    intro i j
    apply Set.disjoint_left.mpr
    rintro e ⟨hei, hnot⟩ hej
    have hh : e ∈ (⋃ l, remove l) ∪ fresh := by
      rw [← hbalance]
      exact Set.mem_iUnion.mpr ⟨j, hej⟩
    rcases hh with hh | hh
    · obtain ⟨l, hel⟩ := Set.mem_iUnion.mp hh
      by_cases hil : i = l
      · subst l; exact hnot hel
      · exact Set.disjoint_left.mp (hold hil) hei (hsub l hel)
    · exact Set.disjoint_left.mp hfresh hh (Set.mem_iUnion.mpr ⟨i, hei⟩)
  constructor
  · intro i j hij
    exact Disjoint.union_left
      (Disjoint.union_right ((hold hij).mono Set.sdiff_subset Set.sdiff_subset) (hcross i j))
      (Disjoint.union_right (hcross j i).symm (hadd hij))
  · ext e
    constructor
    · intro he
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
      rcases hi with hi | hi
      · exact Or.inl (Set.mem_iUnion.mpr ⟨i, hi.1⟩)
      · have hh : e ∈ (⋃ l, remove l) ∪ fresh := by
          rw [← hbalance]
          exact Set.mem_iUnion.mpr ⟨i, hi⟩
        rcases hh with hh | hh
        · obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hh
          exact Or.inl (Set.mem_iUnion.mpr ⟨l, hsub l hl⟩)
        · exact Or.inr hh
    · rintro (he | he)
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
        by_cases hr : e ∈ remove i
        · have hh : e ∈ ⋃ l, add l := by
            rw [hbalance]
            exact Or.inl (Set.mem_iUnion.mpr ⟨i, hr⟩)
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hh
          exact Set.mem_iUnion.mpr ⟨j, Or.inr hj⟩
        · exact Set.mem_iUnion.mpr ⟨i, Or.inl ⟨hi, hr⟩⟩
      · have hh : e ∈ ⋃ l, add l := by rw [hbalance]; exact Or.inr he
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hh
        exact Set.mem_iUnion.mpr ⟨i, Or.inr hi⟩

inductive Centered {V : Type cycleUniverse21} (G : SimpleGraph V) (x : V) where
  | path (F : Frame G x)
  | cycle {v : V} (c : G.Walk v v) (hc : c.IsCycle)

namespace Centered
variable {V : Type cycleUniverse22} {G : SimpleGraph V} {x : V}

def piece : Centered G x → Piece G
  | .path F => .ofPath F.path
  | .cycle c hc => .ofCycle c hc

def Port : Centered G x → Type
  | .path F => F.Port
  | .cycle _ _ => Empty

def endpoint : (K : Centered G x) → K.Port → V
  | .path F, p => F.endpoint p
  | .cycle _ _, p => nomatch p

def exit : (K : Centered G x) → K.Port → Option V
  | .path F, p => F.exit p
  | .cycle _ _, p => nomatch p

def inserted (K : Centered G x) (active : K.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ e = s(x,K.endpoint p)}

def removed (K : Centered G x) (active : K.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ ∃ v, K.exit p = some v ∧ e = s(x,v)}

lemma exit_edge (K : Centered G x) (p : K.Port) (v : V) (h : K.exit p = some v) :
    s(x,v) ∈ K.piece.walk.edgeSet := by
  cases K with
  | path F => exact F.exit_edge p v h
  | cycle c hc => exact p.elim

lemma exit_adj (K : Centered G x) (p : K.Port) (v : V) (h : K.exit p = some v) :
    G.Adj x v := by
  exact G.mem_edgeSet.mp (K.piece.walk.edges_subset_edgeSet (K.exit_edge p v h))

lemma exit_none_all (K : Centered G x) (p : K.Port) (h : K.exit p = none) :
    ∀ q, K.exit q = none := by
  cases K with
  | cycle c hc => exact p.elim
  | path F =>
    cases F with
    | away P hx => exact fun _ => rfl
    | tip A => exact fun _ => rfl
    | through A B hd => cases p <;> cases h

lemma removed_subset (K : Centered G x) (active : K.Port → Prop) :
    K.removed active ⊆ K.piece.walk.edgeSet := by
  rintro e ⟨p, hp, v, hv, rfl⟩
  exact K.exit_edge p v hv

lemma modify (K : Centered G x) (active : K.Port → Prop)
    (hadj : ∀ p, active p → G.Adj x (K.endpoint p))
    (hnew : ∀ p, active p → K.exit p = none →
      s(x,K.endpoint p) ∉ K.piece.walk.edgeSet) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      (K.piece.walk.edgeSet \ K.removed active) ∪ K.inserted active := by
  cases K with
  | path F => exact F.modify active hadj hnew
  | cycle c hc =>
    refine ⟨.ofCycle c hc, ?_⟩
    have hr : (Centered.cycle c hc).removed active = ∅ := by
      ext e; simp only [removed, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      exact ⟨fun ⟨p, _⟩ => p.elim, False.elim⟩
    have hi : (Centered.cycle c hc).inserted active = ∅ := by
      ext e; simp only [inserted, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      exact ⟨fun ⟨p, _⟩ => p.elim, False.elim⟩
    simp only [hr, hi, Set.sdiff_empty, Set.union_empty]
    rfl

end Centered

theorem restore_selected {V : Type cycleUniverse23} {I : Type cycleUniverse24} (G : SimpleGraph V) (x : V)
    (K : I → Centered G x) (S : Set V)
    (hS : ∀ v ∈ S, G.Adj x v)
    (hold : Pairwise fun i j => Disjoint (K i).piece.walk.edgeSet (K j).piece.walk.edgeSet)
    (hfresh : Disjoint {e | ∃ v ∈ S, e = s(x,v)} (⋃ i, (K i).piece.walk.edgeSet))
    (selected : Set (Σ i, (K i).Port))
    (hinj : Set.InjOn (fun z : Σ i, (K i).Port => (K z.1).endpoint z.2) selected)
    (hcov : ∀ v, G.Adj x v → ∃ z ∈ selected, (K z.1).endpoint z.2 = v) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) =
        (⋃ i, (K i).piece.walk.edgeSet) ∪ {e | ∃ v ∈ S, e = s(x,v)} := by
  let R : V → V → Prop := fun a b => ∃ z ∈ selected,
    (K z.1).endpoint z.2 = a ∧ (K z.1).exit z.2 = some b
  let active : (i : I) → (K i).Port → Prop := fun i p =>
    (⟨i,p⟩ : Σ j, (K j).Port) ∈ selected ∧ StarActive S R ((K i).endpoint p)
  have hactive_adj : ∀ v, StarActive S R v → G.Adj x v := by
    intro v hv
    exact starActive_subset (T := {v | G.Adj x v}) hS
      (by rintro a b ⟨z, _, _, hz⟩; exact (K z.1).exit_adj z.2 b hz) hv
  have hbalance : (⋃ i, (K i).inserted (active i)) =
      (⋃ i, (K i).removed (active i)) ∪ {e | ∃ v ∈ S, e = s(x,v)} := by
    ext e
    constructor
    · intro he
      obtain ⟨i, p, hp, rfl⟩ := Set.mem_iUnion.mp he
      rcases (starActive_iff.mp hp.2) with hs | ⟨w, hw, z, hz, hzw, hzv⟩
      · exact Or.inr ⟨_, hs, rfl⟩
      · exact Or.inl (Set.mem_iUnion.mpr ⟨z.1, z.2, ⟨hz, hzw.symm ▸ hw⟩,
          _, hzv, rfl⟩)
    · rintro (he | ⟨v, hv, rfl⟩)
      · obtain ⟨i, p, hp, v, hpv, rfl⟩ := Set.mem_iUnion.mp he
        have hv : StarActive S R v := starActive_step hp.2 ⟨⟨i,p⟩, hp.1, rfl, hpv⟩
        obtain ⟨z, hz, hzv⟩ := hcov v (hactive_adj v hv)
        exact Set.mem_iUnion.mpr ⟨z.1, z.2, ⟨hz, hzv.symm ▸ hv⟩, congrArg (s(x,·)) hzv.symm⟩
      · obtain ⟨z, hz, hzv⟩ := hcov v (hS v hv)
        exact Set.mem_iUnion.mpr ⟨z.1, z.2, ⟨hz, hzv.symm ▸ starActive_source hv⟩,
          congrArg (s(x,·)) hzv.symm⟩
  have hadd : Pairwise fun i j =>
      Disjoint ((K i).inserted (active i)) ((K j).inserted (active j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro e ⟨p, hp, he⟩ ⟨q, hq, hf⟩
    have h : (⟨i,p⟩ : Σ l, (K l).Port) = ⟨j,q⟩ :=
      hinj hp.1 hq.1 (star_inj.mp (he.symm.trans hf))
    exact hij (congrArg Sigma.fst h)
  have hnew : ∀ i p, active i p → (K i).exit p = none →
      s(x,(K i).endpoint p) ∉ (K i).piece.walk.edgeSet := by
    intro i p hp hn he
    have ha : s(x,(K i).endpoint p) ∈ ⋃ j, (K j).inserted (active j) :=
      Set.mem_iUnion.mpr ⟨i, p, hp, rfl⟩
    rw [hbalance] at ha
    rcases ha with ha | ha
    · obtain ⟨j, q, hq, v, hqv, hev⟩ := Set.mem_iUnion.mp ha
      have hej : s(x,(K i).endpoint p) ∈ (K j).piece.walk.edgeSet :=
        hev ▸ (K j).exit_edge q v hqv
      have hij : i = j := by
        by_contra h; exact Set.disjoint_left.mp (hold h) he hej
      subst j
      rw [(K i).exit_none_all p hn q] at hqv
      cases hqv
    · exact Set.disjoint_left.mp hfresh ha (Set.mem_iUnion.mpr ⟨i, he⟩)
  choose Q hQ using fun i => (K i).modify (active i)
    (fun p hp => hactive_adj _ hp.2) (hnew i)
  have hh := rewire_partition (fun i => (K i).piece.walk.edgeSet)
    (fun i => (K i).removed (active i)) (fun i => (K i).inserted (active i))
    {e | ∃ v ∈ S, e = s(x,v)} (fun i => (K i).removed_subset _) hold hadd hfresh hbalance
  refine ⟨Q, ?_, ?_⟩
  · simpa only [hQ] using hh.1
  · simpa only [hQ] using hh.2

theorem restore_star {V : Type cycleUniverse25} {I : Type cycleUniverse26} (G : SimpleGraph V) (x : V)
    (K : I → Centered G x) (S : Set V)
    (hS : ∀ v ∈ S, G.Adj x v)
    (hold : Pairwise fun i j => Disjoint (K i).piece.walk.edgeSet (K j).piece.walk.edgeSet)
    (hfresh : Disjoint {e | ∃ v ∈ S, e = s(x,v)} (⋃ i, (K i).piece.walk.edgeSet))
    (hcov : ∀ v, G.Adj x v → ∃ i p, (K i).endpoint p = v) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) =
        (⋃ i, (K i).piece.walk.edgeSet) ∪ {e | ∃ v ∈ S, e = s(x,v)} := by
  let T := {v // G.Adj x v}
  have hh : ∀ v : T, ∃ z : Σ i, (K i).Port, (K z.1).endpoint z.2 = v.val := by
    intro v
    obtain ⟨i,p,h⟩ := hcov v.val v.property
    exact ⟨⟨i,p⟩,h⟩
  choose f hf using hh
  apply restore_selected G x K S hS hold hfresh (Set.range f)
  · rintro z ⟨v,rfl⟩ w ⟨u,rfl⟩ he
    have hvu : v = u := Subtype.ext ((hf v).symm.trans (he.trans (hf u)))
    exact congrArg f hvu
  · intro v hv
    exact ⟨f ⟨v,hv⟩, ⟨⟨v,hv⟩, rfl⟩, hf ⟨v,hv⟩⟩

namespace Arm
variable {V : Type cycleUniverse27} {G : SimpleGraph V} {x b : V}

def fromWalk (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) : Arm G x :=
  match w with
  | .nil => False.elim (hn .nil)
  | @Walk.cons _ _ _ y _ h q =>
    ⟨y, b, h, q, (Walk.cons_isPath_iff h q).mp hp |>.1,
      (Walk.cons_isPath_iff h q).mp hp |>.2⟩

@[simp] lemma fromWalk_far (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) :
    (fromWalk w hp hn).far = b := by
  cases w with
  | nil => exact (hn .nil).elim
  | cons h q => rfl

@[simp] lemma fromWalk_support (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) :
    (fromWalk w hp hn).walk.support = w.support.tail := by
  cases w with
  | nil => exact (hn .nil).elim
  | cons h q => rfl

@[simp] lemma fromWalk_tip_edges (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) :
    (fromWalk w hp hn).tip.walk.edgeSet = w.edgeSet := by
  cases w with
  | nil => exact (hn .nil).elim
  | cons h q => rfl
end Arm

lemma PathPiece.exists_frame {V : Type cycleUniverse28} {G : SimpleGraph V} (P : PathPiece G) (x : V) :
    ∃ F : Frame G x, F.path.walk.edgeSet = P.walk.edgeSet ∧
      ∀ v, (F.path.start = v ∨ F.path.finish = v) ↔ (P.start = v ∨ P.finish = v) := by
  classical
  by_cases hx : x ∈ P.walk.support
  · obtain ⟨q,r,hq,hr,hqr⟩ := P.isPath.mem_support_iff_exists_append.mp hx
    have hp : (q.append r).IsPath := hqr ▸ P.isPath
    by_cases hqn : q.Nil
    · have hx : P.start = x := hqn.eq
      have hrn : ¬r.Nil := by
        intro hn; exact P.ends_ne (hx.trans hn.eq)
      let A := Arm.fromWalk r hr hrn
      refine ⟨.tip A, ?_, ?_⟩
      · change A.tip.walk.edgeSet = P.walk.edgeSet
        rw [Arm.fromWalk_tip_edges]
        rw [hqr, Walk.edgeSet_append]
        simp [Walk.edgeSet, Walk.edges_eq_nil.mpr hqn]
      · intro v
        change (x = v ∨ A.far = v) ↔ _
        simp only [A, Arm.fromWalk_far, hx]
    · by_cases hrn : r.Nil
      · have hx : x = P.finish := hrn.eq
        have hqnr : ¬q.reverse.Nil := by simpa using hqn
        let A := Arm.fromWalk q.reverse hq.reverse hqnr
        refine ⟨.tip A, ?_, ?_⟩
        · change A.tip.walk.edgeSet = P.walk.edgeSet
          rw [Arm.fromWalk_tip_edges, Walk.edgeSet_reverse]
          rw [hqr, Walk.edgeSet_append]
          simp [Walk.edgeSet, Walk.edges_eq_nil.mpr hrn]
        · intro v
          change (x = v ∨ A.far = v) ↔ _
          simp only [A, Arm.fromWalk_far, hx, or_comm]
      · have hqnr : ¬q.reverse.Nil := by simpa using hqn
        let A := Arm.fromWalk q.reverse hq.reverse hqnr
        let B := Arm.fromWalk r hr hrn
        have hd : A.walk.support.Disjoint B.walk.support := by
          rw [Arm.fromWalk_support, Arm.fromWalk_support]
          have hd := hp.disjoint_support_of_append hrn
          rw [Walk.support_tail_of_not_nil r hrn] at hd
          apply List.disjoint_left.mpr
          intro v hv hw
          exact List.disjoint_left.mp hd
            (by simpa using (List.mem_of_mem_tail hv : v ∈ q.reverse.support)) hw
        refine ⟨.through A B hd, ?_, ?_⟩
        · change ((Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)).edgeSet = _
          rw [Walk.edgeSet_append, Walk.edgeSet_reverse]
          change A.tip.walk.edgeSet ∪ B.tip.walk.edgeSet = _
          rw [Arm.fromWalk_tip_edges, Arm.fromWalk_tip_edges, Walk.edgeSet_reverse,
            hqr, Walk.edgeSet_append]
        · intro v
          change (A.far = v ∨ B.far = v) ↔ _
          simp only [A, B, Arm.fromWalk_far]
  · exact ⟨.away P hx, rfl, fun _ => Iff.rfl⟩

namespace Piece
variable {V : Type cycleUniverse29} {G H : SimpleGraph V}

lemma isTrail (P : Piece G) : P.walk.IsTrail := by
  rcases P.simple with hp | ⟨h,hc⟩
  · exact hp.1.isTrail
  · exact (P.walk.isTrail_copy rfl h).mp hc.isTrail

def mapLe (h : H ≤ G) (P : Piece H) : Piece G := by
  rcases P with ⟨a,b,w,hs⟩
  refine ⟨a,b,w.mapLe h, ?_⟩
  rcases hs with hp | ⟨hb,hc⟩
  · exact Or.inl ⟨hp.1.mapLe h, by simpa using hp.2⟩
  · subst b
    exact Or.inr ⟨rfl, by simpa using hc.mapLe h⟩

@[simp] lemma mapLe_edges (h : H ≤ G) (P : Piece H) :
    (P.mapLe h).walk.edgeSet = P.walk.edgeSet := by
  cases P
  exact Walk.edgeSet_mapLe_eq_edgeSet _ _

@[simp] lemma mapLe_start (h : H ≤ G) (P : Piece H) : (P.mapLe h).start = P.start := by
  cases P; rfl
@[simp] lemma mapLe_finish (h : H ≤ G) (P : Piece H) : (P.mapLe h).finish = P.finish := by
  cases P; rfl

lemma exists_centered (P : Piece G) (x : V) :
    ∃ K : Centered G x, K.piece.walk.edgeSet = P.walk.edgeSet ∧
      ∀ v, P.start ≠ P.finish → (P.start = v ∨ P.finish = v) → v ≠ x →
        ∃ p, K.endpoint p = v := by
  rcases P with ⟨a,b,w,hs⟩
  rcases hs with hp | ⟨hb,hc⟩
  · let Q : PathPiece G := ⟨a,b,w,hp.1,hp.2⟩
    obtain ⟨F,he,hv⟩ := Q.exists_frame x
    refine ⟨.path F, he, ?_⟩
    intro v _ he hx
    exact (F.port_iff_endpoint v).mpr ⟨(hv v).mpr he, hx⟩
  · subst b
    refine ⟨.cycle w (by simpa using hc), rfl, ?_⟩
    exact fun _ hn => (hn rfl).elim
end Piece

theorem trail_partition_degree_sum {V : Type cycleUniverse30} {I : Type cycleUniverse31} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    G.degree v = ∑ i, (p i).edges.countP (fun e => decide (v ∈ e)) := by
  classical
  have he : G.edgeFinset = Finset.univ.biUnion (fun i => (p i).edges.toFinset) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, ← hc, Set.mem_iUnion,
      Finset.mem_biUnion, Finset.mem_univ, List.mem_toFinset, true_and,
      SimpleGraph.Walk.mem_edgeSet]
  rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter, he,
    Finset.filter_biUnion]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    have hfilter : ((p i).edges.filter (fun e => decide (v ∈ e))).toFinset =
        ((p i).edges.toFinset.filter (fun e => v ∈ e)) := by
      simp [List.toFinset_filter]
    rw [← hfilter, List.toFinset_card_of_nodup ((ht i).edges_nodup.filter _),
      List.countP_eq_length_filter]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact Set.disjoint_left.mp (hd hij)
      (by simpa using (Finset.mem_filter.mp hei).1)
      (by simpa using (Finset.mem_filter.mp hej).1)

theorem trail_partition_even_degree_iff {V : Type cycleUniverse32} {I : Type cycleUniverse33} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    Even (G.degree v) ↔ Even (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card := by
  classical
  rw [trail_partition_degree_sum G p ht hd hc v, Finset.even_sum_iff_even_card_odd]
  have he : (Finset.univ.filter (fun i => Odd ((p i).edges.countP
      (fun e => decide (v ∈ e))))) = (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ← Nat.not_even_iff_odd, (ht i).even_countP_edges_iff]
    tauto
  rw [he]

lemma endpoint_of_odd {V : Type cycleUniverse34} {I : Type cycleUniverse35} [Fintype V] [Fintype I]
    (H : SimpleGraph V) (P : I → Piece H)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = H.edgeSet)
    (v : V) (hv : Odd (H.degree v)) :
    ∃ i, (P i).start ≠ (P i).finish ∧ ((P i).start = v ∨ (P i).finish = v) := by
  classical
  have ho := (trail_partition_even_degree_iff H (fun i => (P i).walk)
    (fun i => (P i).isTrail) hd hc v).not.mp (Nat.not_even_iff_odd.mpr hv)
  have hp : 0 < (Finset.univ.filter
      (fun i => (P i).start ≠ (P i).finish ∧ (v = (P i).start ∨ v = (P i).finish))).card := by
    by_contra hn
    have hz : (Finset.univ.filter
      (fun i => (P i).start ≠ (P i).finish ∧ (v = (P i).start ∨ v = (P i).finish))).card = 0 := by omega
    exact ho (hz ▸ ⟨0, rfl⟩)
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hp
  exact ⟨i, (Finset.mem_filter.mp hi).2.1, by
    simpa only [eq_comm] using (Finset.mem_filter.mp hi).2.2⟩

theorem restore_partition {V : Type cycleUniverse36} {I : Type cycleUniverse37} [Fintype V] [Fintype I]
    (G H : SimpleGraph V) (hHG : H ≤ G) (x : V) (S : Set V)
    (hS : ∀ v ∈ S, G.Adj x v)
    (hedges : G.edgeSet = H.edgeSet ∪ {e | ∃ v ∈ S, e = s(x,v)})
    (hfresh : Disjoint {e | ∃ v ∈ S, e = s(x,v)} H.edgeSet)
    (hodd : ∀ v, G.Adj x v → Odd (H.degree v))
    (P : I → Piece H)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = H.edgeSet) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) = G.edgeSet := by
  choose K hk hv using fun i => ((P i).mapLe hHG).exists_centered x
  have he : ∀ i, (K i).piece.walk.edgeSet = (P i).walk.edgeSet := by
    intro i; exact (hk i).trans ((P i).mapLe_edges hHG)
  have hKC : (⋃ i, (K i).piece.walk.edgeSet) = H.edgeSet := by simpa only [he] using hc
  obtain ⟨Q,hQ,hQC⟩ := restore_star G x K S hS
    (by simpa only [he] using hd) (by rwa [hKC]) (by
      intro v hxv
      obtain ⟨i, hi, hiv⟩ := endpoint_of_odd H P hd hc v (hodd v hxv)
      obtain ⟨p,hp⟩ := hv i v (by simpa using hi) (by simpa using hiv) hxv.ne.symm
      exact ⟨i,p,hp⟩)
  exact ⟨Q,hQ,by simpa only [hKC, ← hedges] using hQC⟩

def activeOrder {V : Type cycleUniverse38} [Fintype V] (G : SimpleGraph V) : ℕ :=
  G.support.toFinset.card

lemma activeOrder_mono {V : Type cycleUniverse39} [Fintype V] {G H : SimpleGraph V} (h : H ≤ G) :
    activeOrder H ≤ activeOrder G := by
  apply Finset.card_le_card
  intro v hv
  exact Set.mem_toFinset.mpr (SimpleGraph.support_mono h (Set.mem_toFinset.mp hv))

def HasPartition {V : Type cycleUniverse40} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (P : Fin k → Piece G),
    (Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
    (⋃ i, (P i).walk.edgeSet) = G.edgeSet ∧ 2 * k ≤ activeOrder G

def evenStarVertices {V : Type cycleUniverse41} [Fintype V] (G : SimpleGraph V) (x : V) : Set V :=
  {y | G.Adj x y ∧ Even (G.degree y)}

def evenStarEdges {V : Type cycleUniverse42} [Fintype V] (G : SimpleGraph V) (x : V) : Set (Sym2 V) :=
  {e | ∃ y ∈ evenStarVertices G x, e = s(x,y)}

def deleteEvenStar {V : Type cycleUniverse43} [Fintype V] (G : SimpleGraph V) (x : V) : SimpleGraph V :=
  G.deleteEdges (evenStarEdges G x)

lemma evenStar_subset {V : Type cycleUniverse44} [Fintype V] (G : SimpleGraph V) (x : V) :
    evenStarEdges G x ⊆ G.edgeSet := by
  rintro e ⟨y,hy,rfl⟩; exact hy.1

lemma deleteEvenStar_neighbor_even {V : Type cycleUniverse45} [Fintype V] (G : SimpleGraph V)
    (x v : V) (hxv : G.Adj x v) (he : Even (G.degree v)) :
    (deleteEvenStar G x).neighborFinset v = (G.neighborFinset v).erase x := by
  classical
  ext w
  rw [Finset.mem_erase, (deleteEvenStar G x).mem_neighborFinset, G.mem_neighborFinset]
  rw [deleteEvenStar, SimpleGraph.deleteEdges_adj]
  simp only [evenStarEdges, Set.mem_ofPred_eq, evenStarVertices, Sym2.eq_iff]
  constructor
  · rintro ⟨hvw, hn⟩
    refine ⟨?_,hvw⟩
    intro hw; subst w
    exact hn ⟨v,⟨hxv,he⟩, Or.inr ⟨rfl,rfl⟩⟩
  · rintro ⟨hw,hvw⟩
    refine ⟨hvw, ?_⟩
    rintro ⟨y,_,h⟩
    rcases h with ⟨h,_⟩ | ⟨_,h⟩
    · exact hxv.ne h.symm
    · exact hw h

lemma deleteEvenStar_neighbor_odd {V : Type cycleUniverse46} [Fintype V] (G : SimpleGraph V)
    (x v : V) (hxv : G.Adj x v) (he : ¬Even (G.degree v)) :
    (deleteEvenStar G x).neighborFinset v = G.neighborFinset v := by
  classical
  ext w
  rw [(deleteEvenStar G x).mem_neighborFinset, G.mem_neighborFinset]
  rw [deleteEvenStar, SimpleGraph.deleteEdges_adj]
  simp only [evenStarEdges, Set.mem_ofPred_eq, evenStarVertices, Sym2.eq_iff]
  refine ⟨fun h => h.1, fun hw => ⟨hw, ?_⟩⟩
  rintro ⟨y,hy,h⟩
  rcases h with ⟨h,_⟩ | ⟨h,_⟩
  · exact hxv.ne h.symm
  · subst y; exact he hy.2

lemma deleteEvenStar_neighbor_degree {V : Type cycleUniverse47} [Fintype V] (G : SimpleGraph V)
    (x v : V) (hxv : G.Adj x v) : Odd ((deleteEvenStar G x).degree v) := by
  classical
  by_cases he : Even (G.degree v)
  · have hcard := Finset.card_erase_add_one (s := G.neighborFinset v)
      (a := x) (by simpa using hxv.symm)
    rw [← deleteEvenStar_neighbor_even G x v hxv he,
      G.card_neighborFinset_eq_degree, (deleteEvenStar G x).card_neighborFinset_eq_degree] at hcard
    obtain ⟨k,hk⟩ := he
    exact ⟨k-1, by omega⟩
  · rw [← (deleteEvenStar G x).card_neighborFinset_eq_degree v,
      deleteEvenStar_neighbor_odd G x v hxv he, G.card_neighborFinset_eq_degree]
    exact Nat.not_even_iff_odd.mp he

lemma deleteEvenStar_edges {V : Type cycleUniverse48} [Fintype V] (G : SimpleGraph V) (x : V) :
    G.edgeSet = (deleteEvenStar G x).edgeSet ∪ evenStarEdges G x := by
  rw [deleteEvenStar, SimpleGraph.edgeSet_deleteEdges,
    Set.sdiff_union_of_subset (evenStar_subset G x)]

lemma deleteEvenStar_fresh {V : Type cycleUniverse49} [Fintype V] (G : SimpleGraph V) (x : V) :
    Disjoint (evenStarEdges G x) (deleteEvenStar G x).edgeSet := by
  rw [deleteEvenStar, SimpleGraph.edgeSet_deleteEdges]
  exact Set.disjoint_sdiff_right

lemma deleteEvenStar_lt {V : Type cycleUniverse50} [Fintype V] (G : SimpleGraph V) (x y : V)
    (hxy : G.Adj x y) (he : Even (G.degree y)) :
    (deleteEvenStar G x).edgeFinset.card < G.edgeFinset.card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro e he
    exact G.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono
      (show deleteEvenStar G x ≤ G from G.deleteEdges_le _)
      ((deleteEvenStar G x).mem_edgeFinset.mp he))
  · intro h
    have hh : s(x,y) ∈ (deleteEvenStar G x).edgeFinset := h.symm ▸ G.mem_edgeFinset.mpr hxy
    have hf : s(x,y) ∈ evenStarEdges G x := ⟨y,⟨hxy,he⟩,rfl⟩
    exact Set.disjoint_left.mp (deleteEvenStar_fresh G x) hf (SimpleGraph.mem_edgeFinset.mp hh)

theorem even_vertex_step {V : Type cycleUniverse51} [Fintype V] (G : SimpleGraph V)
    (hIH : ∀ H : SimpleGraph V, H.edgeFinset.card < G.edgeFinset.card → HasPartition H)
    (hpos : ∃ y, 0 < G.degree y ∧ Even (G.degree y)) : HasPartition G := by
  classical
  obtain ⟨y,hy,he⟩ := hpos
  obtain ⟨x,hxy⟩ := (G.degree_pos_iff_exists_adj y).mp hy
  let H := deleteEvenStar G x
  obtain ⟨k,P,hd,hc,hk⟩ := hIH H (deleteEvenStar_lt G x y hxy.symm he)
  obtain ⟨Q,hQ,hQC⟩ := restore_partition G H (G.deleteEdges_le _) x
    (evenStarVertices G x) (fun _ h => h.1) (deleteEvenStar_edges G x)
    (deleteEvenStar_fresh G x) (deleteEvenStar_neighbor_degree G x) P hd hc
  exact ⟨k,Q,hQ,hQC,hk.trans (activeOrder_mono (G.deleteEdges_le _))⟩

lemma single_edge_piece {V : Type cycleUniverse52} (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ∃ P : Piece G, P.walk.edgeSet = {e} := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := he
    let P : PathPiece G := ⟨a,b,Walk.cons hab Walk.nil,
      (Walk.IsPath.nil).cons (by simpa using hab.ne), by simp⟩
    exact ⟨.ofPath P, by simp [Piece.ofPath, P]⟩

lemma partition_single_edges {V : Type cycleUniverse53} [Fintype V] (G : SimpleGraph V) :
    ∃ P : Fin G.edgeFinset.card → Piece G,
      (Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
      (⋃ i, (P i).walk.edgeSet) = G.edgeSet := by
  classical
  choose P hP using fun e : G.edgeSet => single_edge_piece G e.val e.property
  let e : G.edgeSet ≃ Fin G.edgeFinset.card := (Fintype.equivFin G.edgeSet).trans
    (finCongr (G.card_edgeSet))
  refine ⟨fun i => P (e.symm i), ?_, ?_⟩
  · intro i j hij
    rw [hP, hP]
    exact Set.disjoint_singleton.mpr (fun h => hij (e.symm.injective (Subtype.ext h)))
  · ext z
    simp only [Set.mem_iUnion,hP,Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩; exact (e.symm i).property
    · intro hz
      exact ⟨e ⟨z,hz⟩, by simp⟩

lemma matching_partition {V : Type cycleUniverse54} [Fintype V] (G : SimpleGraph V)
    (hdeg : ∀ v, G.degree v ≤ 1) : HasPartition G := by
  classical
  obtain ⟨P,hd,hc⟩ := partition_single_edges G
  refine ⟨_,P,hd,hc,?_⟩
  rw [← G.sum_degrees_support_eq_twice_card_edges]
  simpa [activeOrder] using Finset.sum_le_sum (s := G.support.toFinset)
    (f := fun v => G.degree v) (g := fun _ => 1) (fun v _ => hdeg v)

def subdivision {V : Type cycleUniverse55} (G : SimpleGraph V) (x y : V) : SimpleGraph (Option V) where
  Adj a b := match a,b with
    | some a, some b => G.Adj a b ∧ s(a,b) ≠ s(x,y)
    | none, some b => b = x ∨ b = y
    | some a, none => a = x ∨ a = y
    | none, none => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by
    intro a h
    cases a
    · exact h
    · exact G.irrefl h.1⟩

@[simp] lemma subdivision_some {V : Type cycleUniverse56} (G : SimpleGraph V) (x y a b : V) :
    (subdivision G x y).Adj (some a) (some b) ↔ G.Adj a b ∧ s(a,b) ≠ s(x,y) := Iff.rfl
@[simp] lemma subdivision_none_some {V : Type cycleUniverse57} (G : SimpleGraph V) (x y a : V) :
    (subdivision G x y).Adj none (some a) ↔ a = x ∨ a = y := Iff.rfl
@[simp] lemma subdivision_some_none {V : Type cycleUniverse58} (G : SimpleGraph V) (x y a : V) :
    (subdivision G x y).Adj (some a) none ↔ a = x ∨ a = y := Iff.rfl
def halfSubdivision {V : Type cycleUniverse60} (G : SimpleGraph V) (x y : V) : SimpleGraph (Option V) :=
  (subdivision G x y).deleteEdges {s(none,some x)}

@[simp] lemma half_some {V : Type cycleUniverse61} (G : SimpleGraph V) (x y a b : V) :
    (halfSubdivision G x y).Adj (some a) (some b) ↔ G.Adj a b ∧ s(a,b) ≠ s(x,y) := by
  rw [halfSubdivision, SimpleGraph.deleteEdges_adj]
  simp []

@[simp] lemma half_none_some {V : Type cycleUniverse62} (G : SimpleGraph V) (x y a : V) (hxy : x ≠ y) :
    (halfSubdivision G x y).Adj none (some a) ↔ a = y := by
  rw [halfSubdivision, SimpleGraph.deleteEdges_adj]
  simp only [subdivision_none_some, Set.mem_singleton_iff, star_inj, Option.some.injEq]
  aesop

@[simp] lemma half_some_none {V : Type cycleUniverse63} (G : SimpleGraph V) (x y a : V) (hxy : x ≠ y) :
    (halfSubdivision G x y).Adj (some a) none ↔ a = y := by
  rw [(halfSubdivision G x y).adj_comm, half_none_some G x y a hxy]

lemma option_degree_some {V : Type cycleUniverse64} [Fintype V] (K : SimpleGraph (Option V)) (v : V) :
    K.degree (some v) = (Finset.univ.filter (fun u : V => K.Adj (some v) (some u))).card +
      if K.Adj (some v) none then 1 else 0 := by
  classical
  rw [← K.card_neighborFinset_eq_degree, K.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  omega

lemma option_degree_none {V : Type cycleUniverse65} [Fintype V] (K : SimpleGraph (Option V)) :
    K.degree none = (Finset.univ.filter (fun u : V => K.Adj none (some u))).card := by
  classical
  rw [← K.card_neighborFinset_eq_degree, K.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp

lemma subdivision_old_neighbors {V : Type cycleUniverse66} [Fintype V] (G : SimpleGraph V)
    (x y v : V) :
    (Finset.univ.filter fun u : V => (subdivision G x y).Adj (some v) (some u)) =
      if v = x then (G.neighborFinset v).erase y else
      if v = y then (G.neighborFinset v).erase x else G.neighborFinset v := by
  classical
  ext u
  by_cases hx : v = x
  · subst v
    simp [eq_comm, and_comm]
    aesop
  · by_cases hy : v = y
    · subst v
      simp [hx,  eq_comm, and_comm]
      tauto
    · simp [hx, hy]

lemma subdivision_degree {V : Type cycleUniverse67} [Fintype V] (G : SimpleGraph V)
    (x y v : V) (hxy : G.Adj x y) :
    (subdivision G x y).degree (some v) = G.degree v := by
  classical
  rw [option_degree_some, subdivision_old_neighbors]
  by_cases hx : v = x
  · subst v
    simpa using Finset.card_erase_add_one (s := G.neighborFinset x) (a := y)
      (by simpa using hxy)
  · by_cases hy : v = y
    · subst v
      simpa [hx] using Finset.card_erase_add_one (s := G.neighborFinset y) (a := x)
        (by simpa using hxy.symm)
    · simp [hx,hy]

lemma subdivision_degree_none {V : Type cycleUniverse68} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) : (subdivision G x y).degree none = 2 := by
  classical
  rw [option_degree_none]
  have he : (Finset.univ.filter fun u : V => (subdivision G x y).Adj none (some u)) =
      {x,y} := by ext u; simp
  rw [he]
  simp [hxy.ne]

lemma half_degree {V : Type cycleUniverse69} [Fintype V] (G : SimpleGraph V)
    (x y v : V) (hxy : G.Adj x y) :
    (halfSubdivision G x y).degree (some v) + (if v = x then 1 else 0) = G.degree v := by
  classical
  rw [option_degree_some]
  have he : (Finset.univ.filter fun u : V => (halfSubdivision G x y).Adj (some v) (some u)) =
      (Finset.univ.filter fun u : V => (subdivision G x y).Adj (some v) (some u)) := by
    ext u; simp
  rw [he, subdivision_old_neighbors]
  by_cases hx : v = x
  · subst v
    simpa [hxy.ne] using Finset.card_erase_add_one (s := G.neighborFinset x) (a := y)
      (by simpa using hxy)
  · by_cases hy : v = y
    · subst v
      simpa [hx, hxy.ne] using Finset.card_erase_add_one (s := G.neighborFinset y) (a := x)
        (by simpa using hxy.symm)
    · simp [hx,hy,half_some_none G x y v hxy.ne]

lemma half_degree_none {V : Type cycleUniverse70} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) : (halfSubdivision G x y).degree none = 1 := by
  classical
  rw [option_degree_none]
  have he : (Finset.univ.filter fun u : V => (halfSubdivision G x y).Adj none (some u)) =
      {y} := by ext u; simp [half_none_some G x y u hxy.ne]
  rw [he]
  simp

lemma subdivision_edge_count {V : Type cycleUniverse71} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) :
    (subdivision G x y).edgeFinset.card = G.edgeFinset.card + 1 := by
  classical
  have hd := (subdivision G x y).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_option, subdivision_degree_none G x y hxy] at hd
  simp_rw [subdivision_degree G x y _ hxy] at hd
  rw [G.sum_degrees_eq_twice_card_edges] at hd
  omega

lemma half_edge_count {V : Type cycleUniverse72} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) :
    (halfSubdivision G x y).edgeFinset.card = G.edgeFinset.card := by
  classical
  have he : (halfSubdivision G x y).edgeFinset =
      (subdivision G x y).edgeFinset.erase s(none,some x) := by
    ext e
    rw [(halfSubdivision G x y).mem_edgeFinset, Finset.mem_erase,
      (subdivision G x y).mem_edgeFinset]
    simp [halfSubdivision, SimpleGraph.edgeSet_deleteEdges, and_comm]
  rw [he, Finset.card_erase_of_mem, subdivision_edge_count G x y hxy]
  · omega
  · exact (subdivision G x y).mem_edgeFinset.mpr (Or.inl rfl)

lemma subdivision_activeOrder {V : Type cycleUniverse73} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) :
    activeOrder (subdivision G x y) = activeOrder G + 1 := by
  classical
  have he : (subdivision G x y).support.toFinset =
      insert none (G.support.toFinset.image Option.some) := by
    ext v
    cases v with
    | none => simp [← SimpleGraph.degree_pos_iff_mem_support, subdivision_degree_none G x y hxy]
    | some v =>
      simp only [Set.mem_toFinset, Finset.mem_insert, Option.some_ne_none, Finset.mem_image,
        Option.some.injEq, false_or, exists_eq_right]
      rw [← (subdivision G x y).degree_pos_iff_mem_support,
        subdivision_degree G x y v hxy, G.degree_pos_iff_mem_support]
  dsimp [activeOrder]
  rw [he, Finset.card_insert_of_notMem, Finset.card_image_of_injective]
  · exact Option.some_injective V
  · simp

lemma suppress_path {V : Type cycleUniverse74} (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    {a b : V} (p : (subdivision G x y).Walk (some a) (some b)) (hp : p.IsPath) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.support = p.support.filterMap id ∧
      ∀ e : Sym2 V, e ∈ q.edgeSet ↔
        e.map Option.some ∈ p.edgeSet ∨ (e = s(x,y) ∧ s(none,some x) ∈ p.edgeSet) := by
  classical
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    cases p with
    | nil =>
      refine ⟨.nil, by simp, by simp, ?_⟩
      intro e
      simp
    | @cons _ v _ h p =>
      have ht : p.IsPath := hp.of_cons
      have ha : some a ∉ p.support := (Walk.cons_isPath_iff _ _ |>.mp hp).2
      cases v with
      | some c =>
        obtain ⟨q,hq,hqs,hqe⟩ := ih p.length (by simp only [Walk.length_cons] at hn; omega) p ht rfl
        have hac : G.Adj a c := (subdivision_some G x y a c).mp h |>.1
        refine ⟨.cons hac q, hq.cons ?_, ?_, ?_⟩
        · intro ha'
          apply ha
          rw [hqs] at ha'
          simpa using ha'
        · simp [hqs]
        · intro e
          have hinj : Function.Injective (Sym2.map (Option.some : V → Option V)) :=
            Sym2.map.injective (Option.some_injective V)
          have he : e.map Option.some = s(some a,some c) ↔ e = s(a,c) :=
            by simpa only [Sym2.map_mk] using (hinj.eq_iff (a := e) (b := s(a,c)))
          have hnedge : s(none,some x) ≠ s(some a,some c) := by simp []
          simp only [Walk.edgeSet_cons, Set.mem_insert_iff, he, hnedge, false_or, hqe]
          tauto
      | none =>
        cases p with
        | @cons _ v _ h' p =>
          cases v with
          | none => exact (h'.ne rfl).elim
          | some c =>
            have hac : a ≠ c := by
              intro he
              apply ha
              simp [he]
            have hae : a = x ∨ a = y := (subdivision_some_none G x y a).mp h
            have hce : c = x ∨ c = y := (subdivision_none_some G x y c).mp h'
            have hexy : s(a,c) = s(x,y) := by
              rcases hae with rfl | rfl <;> rcases hce with rfl | rfl
              · exact (hac rfl).elim
              · rfl
              · exact Sym2.eq_swap
              · exact (hac rfl).elim
            have hacG : G.Adj a c := G.mem_edgeSet.mp (hexy.symm ▸ hxy)
            obtain ⟨q,hq,hqs,hqe⟩ := ih p.length (by simp only [Walk.length_cons] at hn; omega) p ht.of_cons rfl
            refine ⟨.cons hacG q, hq.cons ?_, ?_, ?_⟩
            · intro ha'
              apply ha
              have hh : some a ∈ p.support := by rw [hqs] at ha'; simpa using ha'
              simp [hh]
            · simp [hqs]
            · intro e
              have he1 : e.map Option.some ≠ s(some a,none) := by
                induction e using Sym2.inductionOn with | _ u v => simp []
              have he2 : e.map Option.some ≠ s(none,some c) := by
                induction e using Sym2.inductionOn with | _ u v => simp []
              have hn : s(none,some x) = s(some a,none) ∨
                  s(none,some x) = s(none,some c) := by
                rcases hae with rfl | hay
                · exact Or.inl Sym2.eq_swap
                · rcases hce with rfl | hcy
                  · exact Or.inr rfl
                  · exact (hac (hay.trans hcy.symm)).elim
              simp only [Walk.edgeSet_cons, Set.mem_insert_iff, he1, he2, false_or,
                hexy, hqe]
              tauto

lemma tight_partition_endpoints {V : Type cycleUniverse75} {I : Type cycleUniverse76} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (P : I → Piece G) (S : Finset V)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = G.edgeSet)
    (ho : ∀ v ∈ S, Odd (G.degree v)) (hk : 2 * Fintype.card I ≤ S.card) :
    ∀ i, (P i).start ≠ (P i).finish ∧ (P i).start ∈ S ∧ (P i).finish ∈ S := by
  classical
  let endpoint : I × Bool → V := fun z => if z.2 then (P z.1).start else (P z.1).finish
  have he : ∀ v : S, ∃ z : I × Bool, endpoint z = v := by
    intro v
    obtain ⟨i,_, h | h⟩ := endpoint_of_odd G P hd hc v (ho v v.property)
    · exact ⟨(i,true),h⟩
    · exact ⟨(i,false),h⟩
  choose pick hpick using he
  have hinj : Function.Injective pick := by
    intro v w hvw
    apply Subtype.ext
    exact (hpick v).symm.trans ((congrArg endpoint hvw).trans (hpick w))
  have hsurj : Function.Surjective pick := by
    by_contra hn
    have hh := Fintype.card_lt_of_injective_not_surjective pick hinj hn
    simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_bool] at hh
    omega
  have hendinj : Function.Injective endpoint := by
    intro z t heq
    obtain ⟨v,rfl⟩ := hsurj z
    obtain ⟨w,rfl⟩ := hsurj t
    have hvw : v = w := Subtype.ext (by simpa only [hpick] using heq)
    exact congrArg pick hvw
  have hmem : ∀ z, endpoint z ∈ S := by
    intro z
    obtain ⟨v,rfl⟩ := hsurj z
    rw [hpick]
    exact v.property
  intro i
  refine ⟨?_, hmem (i,true), hmem (i,false)⟩
  intro heq
  have hh := hendinj (show endpoint (i,true) = endpoint (i,false) from heq)
  have := congrArg Prod.snd hh
  contradiction

def subdivisionRepresentative {V : Type cycleUniverse77} (x y : V) (e : Sym2 V) : Sym2 (Option V) :=
  if e = s(x,y) then s(none,some x) else e.map Option.some

lemma representative_mem {V : Type cycleUniverse78} (G : SimpleGraph V) (x y : V) (_hxy : G.Adj x y)
    (e : Sym2 V) (he : e ∈ G.edgeSet) :
    subdivisionRepresentative x y e ∈ (subdivision G x y).edgeSet := by
  classical
  by_cases h : e = s(x,y)
  · simp [subdivisionRepresentative, h]
  · rw [subdivisionRepresentative, ite_eq_right h]
    induction e using Sym2.ind with
    | _ a b => exact ⟨he,h⟩

lemma suppress_piece {V : Type cycleUniverse79} (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (P : Piece (subdivision G x y)) (hne : P.start ≠ P.finish)
    (ha : P.start ≠ none) (hb : P.finish ≠ none) :
    ∃ Q : Piece G, ∀ e, e ∈ Q.walk.edgeSet ↔ subdivisionRepresentative x y e ∈ P.walk.edgeSet := by
  classical
  rcases P with ⟨a,b,p,hp⟩
  cases a with
  | none => exact (ha rfl).elim
  | some a =>
    cases b with
    | none => exact (hb rfl).elim
    | some b =>
      have hab : a ≠ b := fun h => hne (congrArg some h)
      have hpath : p.IsPath := by
        rcases hp with h | ⟨h,_⟩
        · exact h.1
        · exact (hne h.symm).elim
      obtain ⟨q,hq,_,hqe⟩ := suppress_path G x y hxy p hpath
      have hpos : 0 < q.length := by
        by_contra hn
        exact hab (Walk.eq_of_length_eq_zero (by omega : q.length = 0))
      refine ⟨.ofPath ⟨a,b,q,hq,hpos⟩, ?_⟩
      intro e
      change e ∈ q.edgeSet ↔ _
      rw [hqe]
      by_cases he : e = s(x,y)
      · subst e
        have hn : (s(x,y) : Sym2 V).map some ∉ p.edgeSet := by
          intro h
          have hh := p.edges_subset_edgeSet h
          exact hh.2 rfl
        simp only [subdivisionRepresentative, ite_true, hn, false_or, true_and]
      · simp [subdivisionRepresentative, he]

lemma suppress_partition {V : Type cycleUniverse80} {I : Type cycleUniverse81} [Fintype I]
    (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (P : I → Piece (subdivision G x y))
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = (subdivision G x y).edgeSet)
    (hp : ∀ i, (P i).start ≠ (P i).finish ∧ (P i).start ≠ none ∧ (P i).finish ≠ none) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) = G.edgeSet := by
  classical
  choose Q hQ using fun i => suppress_piece G x y hxy (P i) (hp i).1 (hp i).2.1 (hp i).2.2
  refine ⟨Q, ?_, ?_⟩
  · intro i j hij
    exact Set.disjoint_left.mpr fun e hei hej =>
      Set.disjoint_left.mp (hd hij) ((hQ i e).mp hei) ((hQ j e).mp hej)
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun i => (Q i).walk.edges_subset_edgeSet
    · intro e he
      have hrep := representative_mem G x y hxy e he
      rw [← hc] at hrep
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hrep
      exact Set.mem_iUnion.mpr ⟨i,(hQ i e).mpr hi⟩

lemma even_activeOrder {V : Type cycleUniverse82} [Fintype V] (G : SimpleGraph V)
    (ho : ∀ v, 0 < G.degree v → Odd (G.degree v)) : Even (activeOrder G) := by
  classical
  have he : G.support.toFinset = Finset.univ.filter (fun v => Odd (G.degree v)) := by
    ext v
    simp only [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      ← G.degree_pos_iff_mem_support]
    refine ⟨ho v, ?_⟩
    rintro ⟨k,hk⟩
    omega
  simpa only [activeOrder, he] using G.even_card_odd_degree_vertices

lemma half_restore {V : Type cycleUniverse83} {I : Type cycleUniverse84} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (ho : ∀ v, 0 < G.degree v → Odd (G.degree v))
    (P : I → Piece (halfSubdivision G x y))
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = (halfSubdivision G x y).edgeSet) :
    ∃ Q : I → Piece (subdivision G x y),
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) = (subdivision G x y).edgeSet := by
  classical
  have he : {e : Sym2 (Option V) | ∃ v ∈ ({none} : Set (Option V)), e = s(some x,v)} =
      {s(none,some x)} := by
    ext e
    simp [Sym2.eq_swap]
  apply restore_partition (subdivision G x y) (halfSubdivision G x y)
    ((subdivision G x y).deleteEdges_le _) (some x) {none}
    (by intro v hv; rcases hv with rfl; exact Or.inl rfl) ?_ ?_ ?_ P hd hc
  · rw [he, halfSubdivision, SimpleGraph.edgeSet_deleteEdges]
    symm
    apply Set.sdiff_union_of_subset
    intro e he
    rcases he with rfl
    exact Or.inl rfl
  · rw [he, halfSubdivision, SimpleGraph.edgeSet_deleteEdges]
    exact Set.disjoint_sdiff_right
  · intro v hv
    cases v with
    | none => rw [half_degree_none G x y hxy]; exact ⟨0,rfl⟩
    | some v =>
      have hxv : G.Adj x v := hv.1
      have hh := half_degree G x y v hxy
      rw [ite_eq_right hxv.ne.symm, add_zero] at hh
      rw [hh]
      exact ho v ((G.degree_pos_iff_exists_adj v).mpr ⟨x,hxv.symm⟩)

theorem odd_vertex_step {V : Type cycleUniverse85} [Fintype V] (G : SimpleGraph V)
    (hIH : ∀ H : SimpleGraph (Option V), H.edgeFinset.card < G.edgeFinset.card → HasPartition H)
    (ho : ∀ v, 0 < G.degree v → Odd (G.degree v)) (x : V) (hx : 3 ≤ G.degree x) :
    HasPartition G := by
  classical
  obtain ⟨y,hxy⟩ := (G.degree_pos_iff_exists_adj x).mp (by omega)
  have hp : ∃ v, 0 < (halfSubdivision G x y).degree v ∧
      Even ((halfSubdivision G x y).degree v) := by
    refine ⟨some x, ?_, ?_⟩
    · have hd := half_degree G x y x hxy
      simp only [ite_true] at hd
      omega
    · have hd := half_degree G x y x hxy
      simp only [ite_true] at hd
      obtain ⟨k,hk⟩ := ho x (by omega)
      exact ⟨k,by omega⟩
  obtain ⟨k,P,hd,hc,hk⟩ := even_vertex_step (halfSubdivision G x y)
    (fun H hh => hIH H (by rwa [half_edge_count G x y hxy] at hh)) hp
  have hbound : 2 * k ≤ activeOrder G + 1 := by
    have hm := activeOrder_mono ((subdivision G x y).deleteEdges_le {s(none,some x)})
    rw [subdivision_activeOrder G x y hxy] at hm
    exact hk.trans hm
  have hk' : 2 * k ≤ activeOrder G := by
    obtain ⟨a,ha⟩ := even_activeOrder G ho
    omega
  obtain ⟨Q,hQ,hQC⟩ := half_restore G x y hxy ho P hd hc
  let S := G.support.toFinset.image Option.some
  have hScard : S.card = activeOrder G := by
    exact Finset.card_image_of_injective _ (Option.some_injective V)
  have hSodd : ∀ v ∈ S, Odd ((subdivision G x y).degree v) := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    rw [subdivision_degree G x y w hxy]
    exact ho w ((G.degree_pos_iff_mem_support w).mpr (Set.mem_toFinset.mp hw))
  have hends := tight_partition_endpoints (subdivision G x y) Q S hQ hQC hSodd
    (by simpa only [Fintype.card_fin, hScard] using hk')
  have hnon : ∀ i, (Q i).start ≠ (Q i).finish ∧
      (Q i).start ≠ none ∧ (Q i).finish ≠ none := by
    intro i
    refine ⟨(hends i).1, ?_, ?_⟩
    · intro h
      have hh := (hends i).2.1
      simp only [h, S, Finset.mem_image, Option.some_ne_none, and_false, exists_false] at hh
    · intro h
      have hh := (hends i).2.2
      simp only [h, S, Finset.mem_image, Option.some_ne_none, and_false, exists_false] at hh
  obtain ⟨R,hR,hRC⟩ := suppress_partition G x y hxy Q hQ hQC hnon
  exact ⟨k,R,hR,hRC,hk'⟩

theorem path_cycle_partition {V : Type u} [Fintype V] (G : SimpleGraph V) : HasPartition G := by
  classical
  suffices ∀ (n : ℕ) (W : Type u) [Fintype W] (H : SimpleGraph W),
      H.edgeFinset.card = n → HasPartition H by
    exact this G.edgeFinset.card V G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ H hcount
    by_cases he : ∃ v, 0 < H.degree v ∧ Even (H.degree v)
    · exact even_vertex_step H (fun K hk => ih K.edgeFinset.card (by omega) W K rfl) he
    · have ho : ∀ v, 0 < H.degree v → Odd (H.degree v) := by
        intro v hv
        exact Nat.not_even_iff_odd.mp (fun hev => he ⟨v,hv,hev⟩)
      by_cases hm : ∀ v, H.degree v ≤ 1
      · exact matching_partition H hm
      · push Not at hm
        obtain ⟨x,hx⟩ := hm
        have hx3 : 3 ≤ H.degree x := by
          obtain ⟨k,hk⟩ := ho x (by omega)
          omega
        exact odd_vertex_step H
          (fun K hk => ih K.edgeFinset.card (by omega) (Option W) K rfl) ho x hx3

end
end ErdosGallai.Batch.Lovasz

end
/-! ### Upstream module `Combinatorics/CycleDecomposition/BatchPathDeletion.lean` -/

noncomputable section
namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable

structure PositiveSimplePath {V : Type cycleUniverse1} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  positive : 0 < walk.length

lemma PositiveSimplePath.endpoints_ne {V : Type cycleUniverse2} {G : SimpleGraph V}
    (P : PositiveSimplePath G) : P.start ≠ P.finish := by
  intro he
  have hz := P.isPath.nil_iff_eq.mpr he
  have := hz.length_eq_zero
  have := P.positive
  omega

theorem endpoint_path_count {V : Type cycleUniverse3} {I : Type cycleUniverse4} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G)
    (hload : ∀ v : V, (Finset.univ.filter
      (fun i => (P i).start = v ∨ (P i).finish = v)).card ≤ 2) :
    Fintype.card I ≤ Fintype.card V := by
  classical
  have hsum : (∑ v : V, (Finset.univ.filter
      (fun i => (P i).start = v ∨ (P i).finish = v)).card) =
      2 * Fintype.card I := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    have heq : ∀ i : I,
        (∑ v : V, if (P i).start = v ∨ (P i).finish = v then 1 else 0) = 2 := by
      intro i
      have hf : (Finset.univ.filter fun v =>
          (P i).start = v ∨ (P i).finish = v) = {(P i).start, (P i).finish} := by
        ext v; simp [eq_comm]
      have hc : ({(P i).start, (P i).finish} : Finset V).card = 2 := by
        simp [(P i).endpoints_ne]
      rw [← hc, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    omega
  have hbound := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hload v)
  rw [hsum] at hbound
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hbound
  omega

def EndpointPathPartition {V : Type cycleUniverse5} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (P : Fin k → PositiveSimplePath G),
    Pairwise (fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
    (⋃ i, (P i).walk.edgeSet) = G.edgeSet ∧
    (∀ v : V, (Finset.univ.filter (fun i => (P i).start = v ∨ (P i).finish = v)).card ≤ 2) ∧
    k ≤ Fintype.card V

def PathOrCycleEdgeSet {V : Type cycleUniverse6} (G : SimpleGraph V)
    (s : Set (Sym2 V)) : Prop :=
  (∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ 0 < p.length ∧ s = p.edgeSet) ∨
  (∃ (a : V) (p : G.Walk a a), p.IsCycle ∧ s = p.edgeSet)

def LovaszPathCyclePartition {V : Type cycleUniverse7} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (parts : Fin k → Set (Sym2 V)),
    (∀ i, PathOrCycleEdgeSet G (parts i)) ∧
    Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
    (⋃ i, parts i) = G.edgeSet ∧ 2 * k ≤ Fintype.card V

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
def evenAugmentation {V : Type cycleUniverse8} [Fintype V] (G : SimpleGraph V) :
    SimpleGraph (Option V) where
  Adj x y := match x, y with
    | some u, some v => G.Adj u v
    | none, some v => Even (G.degree v)
    | some u, none => Even (G.degree u)
    | none, none => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact G.adj_symm h⟩
  loopless := ⟨by
    intro x h
    cases x
    · exact h
    · exact G.irrefl h⟩

@[simp] theorem evenAugmentation_some_adj {V : Type cycleUniverse9} [Fintype V]
    (G : SimpleGraph V) (u v : V) :
    (evenAugmentation G).Adj (some u) (some v) ↔ G.Adj u v := Iff.rfl

@[simp] theorem evenAugmentation_some_none {V : Type cycleUniverse11} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (evenAugmentation G).Adj (some v) none ↔ Even (G.degree v) := Iff.rfl

theorem evenAugmentation_degree {V : Type cycleUniverse12} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (evenAugmentation G).degree (some v) =
      G.degree v + if Even (G.degree v) then 1 else 0 := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  simp only [evenAugmentation_some_adj, evenAugmentation_some_none]
  have he : (∑ u : V, if G.Adj v u then 1 else 0) = G.degree v := by
    rw [← G.card_neighborFinset_eq_degree v, G.neighborFinset_eq_filter,
      Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [he]
  omega

theorem evenAugmentation_old_odd {V : Type cycleUniverse13} [Fintype V]
    (G : SimpleGraph V) (v : V) : Odd ((evenAugmentation G).degree (some v)) := by
  rw [evenAugmentation_degree]
  by_cases h : Even (G.degree v)
  · simp only [h, ↓reduceIte]
    rcases h with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · simpa [h] using Nat.not_even_iff_odd.mp h

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable

theorem trail_partition_degree_sum {V : Type cycleUniverse14} {I : Type cycleUniverse15} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    G.degree v = ∑ i, (p i).edges.countP (fun e => decide (v ∈ e)) := by
  classical
  have he : G.edgeFinset = Finset.univ.biUnion (fun i => (p i).edges.toFinset) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, ← hc, Set.mem_iUnion,
      Finset.mem_biUnion, Finset.mem_univ, List.mem_toFinset, true_and,
      SimpleGraph.Walk.mem_edgeSet]
  rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter, he,
    Finset.filter_biUnion]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    have hfilter : ((p i).edges.filter (fun e => decide (v ∈ e))).toFinset =
        ((p i).edges.toFinset.filter (fun e => v ∈ e)) := by
      simp [List.toFinset_filter]
    rw [← hfilter, List.toFinset_card_of_nodup ((ht i).edges_nodup.filter _),
      List.countP_eq_length_filter]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact Set.disjoint_left.mp (hd hij)
      (by simpa using (Finset.mem_filter.mp hei).1)
      (by simpa using (Finset.mem_filter.mp hej).1)

theorem trail_partition_even_degree_iff {V : Type cycleUniverse16} {I : Type cycleUniverse17} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    Even (G.degree v) ↔ Even (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card := by
  classical
  rw [trail_partition_degree_sum G p ht hd hc v, Finset.even_sum_iff_even_card_odd]
  have he : (Finset.univ.filter (fun i => Odd ((p i).edges.countP
      (fun e => decide (v ∈ e))))) = (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ← Nat.not_even_iff_odd, (ht i).even_countP_edges_iff]
    tauto
  rw [he]

private theorem odd_load_one {V : Type cycleUniverse18} [DecidableEq V]
    (S : Finset V) (f : V → ℕ) (ho : ∀ v ∈ S, Odd (f v))
    (hs : ∑ v ∈ S, f v ≤ S.card + 1) : ∀ v ∈ S, f v = 1 := by
  intro v hv
  by_contra hn
  have hv3 : 3 ≤ f v := by rcases ho v hv with ⟨k, hk⟩; omega
  have hlow : ∑ x ∈ S, (1 + if x = v then 2 else 0) ≤ ∑ x ∈ S, f x := by
    apply Finset.sum_le_sum
    intro x hx
    by_cases he : x = v
    · subst x; simpa using hv3
    · simp only [he, ↓reduceIte, add_zero]
      rcases ho x hx with ⟨k, hk⟩
      omega
  have heq : (∑ x ∈ S, (1 + if x = v then 2 else 0)) = S.card + 2 := by
    simp [Finset.sum_add_distrib, hv]
  omega

theorem tight_odd_trail_partition {V : Type cycleUniverse19} {I : Type cycleUniverse20} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (S : Finset V) {a b : I → V}
    (p : ∀ i, G.Walk (a i) (b i)) (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet)
    (ho : ∀ v ∈ S, Odd (G.degree v))
    (hsize : 2 * Fintype.card I ≤ S.card + 1) :
    (∀ i, a i ≠ b i) ∧ (∀ v ∈ S,
      (Finset.univ.filter (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card = 1) := by
  classical
  let load := fun v : V => (Finset.univ.filter
    (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card
  let openParts := Finset.univ.filter (fun i => a i ≠ b i)
  have hlodd : ∀ v ∈ S, Odd (load v) := by
    intro v hv
    rw [← Nat.not_even_iff_odd, ← trail_partition_even_degree_iff G p ht hd hc v]
    exact (Nat.not_even_iff_odd.mpr (ho v hv))
  have htotal : (∑ v : V, load v) = 2 * openParts.card := by
    dsimp [load]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    have he : ∀ i : I, (∑ v : V, if a i ≠ b i ∧ (v = a i ∨ v = b i) then 1 else 0) =
        if a i ≠ b i then 2 else 0 := by
      intro i
      by_cases h : a i = b i
      · simp [h]
      · have hf : (Finset.univ.filter (fun v => a i ≠ b i ∧ (v = a i ∨ v = b i))) =
            {a i, b i} := by ext v; simp [h]
        have hcard : ({a i, b i} : Finset V).card = 2 := by simp [h]
        rw [ite_eq_left h, ← hcard, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp_rw [he]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    change openParts.card * 2 = 2 * openParts.card
    omega
  have hsub : (∑ v ∈ S, load v) ≤ ∑ v : V, load v :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  have hlow : S.card ≤ ∑ v ∈ S, load v := by
    simpa using Finset.sum_le_sum (s := S) (f := fun _ => 1) (g := load)
      (fun v hv => by rcases hlodd v hv with ⟨k, hk⟩; omega)
  have hcount : openParts.card ≤ Fintype.card I := Finset.card_le_univ _
  have hpoint := odd_load_one S load hlodd (by omega)
  refine ⟨?_, hpoint⟩
  intro i hi
  have hproper : openParts ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have hh : i ∈ openParts := heq.symm ▸ Finset.mem_univ i
    simp [openParts, hi] at hh
  have hlt := Finset.card_lt_card hproper
  simp only [Finset.card_univ] at hlt
  omega

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section

private theorem path_tail_delete_start {V : Type cycleUniverse21} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.tail.edgeSet = {e | e ∈ p.edgeSet ∧ a ∉ e} := by
  cases p with
  | nil => ext e; simp
  | @cons a c b h q =>
    have ha : a ∉ q.support := (List.nodup_cons.mp hp.support_nodup).1
    have hnot : ∀ e ∈ q.edgeSet, a ∉ e := by
      intro e he hae
      exact ha (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
        (Or.inr ⟨e, he, hae⟩))
    ext e
    simp only [Set.mem_ofPred_eq, SimpleGraph.Walk.mem_edgeSet,
      SimpleGraph.Walk.edges_tail, SimpleGraph.Walk.edges_cons, List.tail_cons, List.mem_cons]
    constructor
    · intro he
      exact ⟨Or.inr he, hnot e he⟩
    · rintro ⟨he | he, hn⟩
      · subst e; exact (hn (by simp)).elim
      · exact he

private theorem path_dropLast_delete_end {V : Type cycleUniverse22} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.dropLast.edgeSet = {e | e ∈ p.edgeSet ∧ b ∉ e} := by
  have he : p.dropLast.edgeSet = p.reverse.tail.edgeSet := by
    calc
      _ = p.dropLast.reverse.edgeSet := (SimpleGraph.Walk.edgeSet_reverse _).symm
      _ = _ := by rw [SimpleGraph.Walk.reverse_dropLast, SimpleGraph.Walk.edgeSet_copy]
  rw [he, path_tail_delete_start p.reverse hp.reverse, SimpleGraph.Walk.edgeSet_reverse]

private theorem positive_avoids_of_no_incidence {V : Type cycleUniverse23} {G : SimpleGraph V}
    {a b v : V} (p : G.Walk a b) (hpos : 0 < p.length)
    (he : ∀ e ∈ p.edgeSet, v ∉ e) : v ∉ p.support := by
  have hn : ¬p.Nil := by intro hz; have := hz.length_eq_zero; omega
  intro hv
  obtain ⟨e, he', hve⟩ := SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hn |>.mp hv
  exact he e he' hve

theorem delete_vertex_from_path {V : Type cycleUniverse24} [DecidableEq V] {G : SimpleGraph V}
    {a b v : V} (p : G.Walk a b) (hp : p.IsPath) (hv : v ∈ p.support) :
    let q := (p.takeUntil v hv).dropLast
    let r := (p.dropUntil v hv).tail
    q.IsPath ∧ r.IsPath ∧ Disjoint q.edgeSet r.edgeSet ∧
    q.edgeSet ∪ r.edgeSet = {e | e ∈ p.edgeSet ∧ v ∉ e} ∧
    (0 < q.length → v ∉ q.support) ∧
    (0 < r.length → v ∉ r.support) ∧
    (0 < q.length → G.Adj (p.takeUntil v hv).penultimate v) ∧
    (0 < r.length → G.Adj v (p.dropUntil v hv).snd) := by
  dsimp only
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have ht : t.IsPath := hp.takeUntil hv
  have hd : d.IsPath := hp.dropUntil hv
  have heq : t.append d = p := p.take_spec hv
  have hqe : t.dropLast.edgeSet = {e | e ∈ t.edgeSet ∧ v ∉ e} :=
    path_dropLast_delete_end t ht
  have hre : d.tail.edgeSet = {e | e ∈ d.edgeSet ∧ v ∉ e} :=
    path_tail_delete_start d hd
  have hdis : Disjoint t.edgeSet d.edgeSet := by
    have hn := hp.isTrail.edges_nodup
    rw [← heq, SimpleGraph.Walk.edges_append] at hn
    have hn' := (List.nodup_append.mp hn).2.2
    apply Set.disjoint_left.mpr
    intro e het hed
    exact hn' e het e hed rfl
  refine ⟨ht.dropLast, hd.tail, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hqe, hre]
    exact hdis.mono (fun _ h => h.1) (fun _ h => h.1)
  · have he : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    rw [hqe, hre]
    ext e
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    rw [← he]
    simp only [Set.mem_union]
    tauto
  · intro hpos
    apply positive_avoids_of_no_incidence _ hpos
    intro e he
    exact (hqe ▸ he).2
  · intro hpos
    apply positive_avoids_of_no_incidence _ hpos
    intro e he
    exact (hre ▸ he).2
  · intro hpos
    apply t.adj_penultimate
    intro hn
    have hz := hn.length_eq_zero
    change 0 < t.dropLast.length at hpos
    rw [SimpleGraph.Walk.length_dropLast, hz] at hpos
    omega
  · intro hpos
    apply d.adj_snd
    intro hn
    have hz := hn.length_eq_zero
    change 0 < d.tail.length at hpos
    rw [SimpleGraph.Walk.length_tail, hz] at hpos
    omega

theorem delete_vertex_boundary_edges {V : Type cycleUniverse25} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V} (p : G.Walk a b) (hv : v ∈ p.support) :
    (0 < (p.takeUntil v hv).dropLast.length →
      s((p.takeUntil v hv).penultimate, v) ∈ p.edgeSet) ∧
    (0 < (p.dropUntil v hv).tail.length →
      s(v, (p.dropUntil v hv).snd) ∈ p.edgeSet) := by
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have heq : t.append d = p := p.take_spec hv
  constructor
  · intro hpos
    have hn : ¬ t.Nil := by
      intro hz
      change 0 < t.dropLast.length at hpos
      rw [SimpleGraph.Walk.length_dropLast, hz.length_eq_zero] at hpos
      omega
    have hm := t.mk_penultimate_end_mem_edges hn
    have hed : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    exact hed ▸ Or.inl hm
  · intro hpos
    have hn : ¬ d.Nil := by
      intro hz
      change 0 < d.tail.length at hpos
      rw [SimpleGraph.Walk.length_tail, hz.length_eq_zero] at hpos
      omega
    have hm := d.mk_start_snd_mem_edges hn
    have hed : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    exact hed ▸ Or.inr hm

theorem delete_vertex_new_ends_ne {V : Type cycleUniverse26} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V} (p : G.Walk a b) (hp : p.IsPath)
    (hv : v ∈ p.support)
    (hl : 0 < (p.takeUntil v hv).dropLast.length)
    (hr : 0 < (p.dropUntil v hv).tail.length) :
    (p.takeUntil v hv).penultimate ≠ (p.dropUntil v hv).snd := by
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have heq : t.append d = p := p.take_spec hv
  have htn : ¬t.Nil := by
    intro hz
    change 0 < t.dropLast.length at hl
    rw [SimpleGraph.Walk.length_dropLast, hz.length_eq_zero] at hl
    omega
  have hdn : ¬d.Nil := by
    intro hz
    change 0 < d.tail.length at hr
    rw [SimpleGraph.Walk.length_tail, hz.length_eq_zero] at hr
    omega
  have hdj := hp.isTrail.edges_nodup
  rw [← heq, SimpleGraph.Walk.edges_append] at hdj
  have hdis := (List.nodup_append.mp hdj).2.2
  intro hsame
  have ha := t.mk_penultimate_end_mem_edges htn
  have hb := d.mk_start_snd_mem_edges hdn
  apply hdis _ ha _ hb

  rw [show t.penultimate = d.snd from hsame, Sym2.eq_swap]

theorem delete_vertex_new_endpoint_load {V : Type cycleUniverse27} {I : Type cycleUniverse28} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} {a b : I → V} {v : V}
    (p : ∀ i, G.Walk (a i) (b i)) (hp : ∀ i, (p i).IsPath)
    (hv : ∀ i, v ∈ (p i).support)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet) (x : V) :
    let live := fun z : I × Bool => if z.2 then
      0 < ((p z.1).takeUntil v (hv z.1)).dropLast.length else
      0 < ((p z.1).dropUntil v (hv z.1)).tail.length
    let newEnd := fun z : I × Bool => if z.2 then
      ((p z.1).takeUntil v (hv z.1)).penultimate else
      ((p z.1).dropUntil v (hv z.1)).snd
    (Finset.univ.filter fun z => live z ∧ newEnd z = x).card ≤ 1 := by
  classical
  dsimp only
  apply Finset.card_le_one.mpr
  intro z hz w hw
  obtain ⟨i, bi⟩ := z
  obtain ⟨j, bj⟩ := w
  have hi := (Finset.mem_filter.mp hz).2
  have hj := (Finset.mem_filter.mp hw).2
  have hei : s(v,x) ∈ (p i).edgeSet := by
    cases bi
    · have hx : ((p i).dropUntil v (hv i)).snd = x := hi.2
      simpa only [hx] using (delete_vertex_boundary_edges (p i) (hv i)).2 hi.1
    · have hx : ((p i).takeUntil v (hv i)).penultimate = x := hi.2
      have he := (delete_vertex_boundary_edges (p i) (hv i)).1 hi.1
      simpa only [hx, Sym2.eq_swap] using he
  have hej : s(v,x) ∈ (p j).edgeSet := by
    cases bj
    · have hx : ((p j).dropUntil v (hv j)).snd = x := hj.2
      simpa only [hx] using (delete_vertex_boundary_edges (p j) (hv j)).2 hj.1
    · have hx : ((p j).takeUntil v (hv j)).penultimate = x := hj.2
      have he := (delete_vertex_boundary_edges (p j) (hv j)).1 hj.1
      simpa only [hx, Sym2.eq_swap] using he
  have hij : i = j := by
    by_contra hn
    exact Set.disjoint_left.mp (hd hn) hei hej
  subst j
  congr 1
  cases bi <;> cases bj
  · rfl
  · have he := delete_vertex_new_ends_ne (p i) (hp i) (hv i) hj.1 hi.1
    exact (he (hj.2.trans hi.2.symm)).elim
  · have he := delete_vertex_new_ends_ne (p i) (hp i) (hv i) hi.1 hj.1
    exact (he (hi.2.trans hj.2.symm)).elim
  · rfl

structure SimplePathPiece {V : Type cycleUniverse29} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath

namespace SimplePathPiece
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse30} {I : Type cycleUniverse31} [Fintype I] [DecidableEq V] {G : SimpleGraph V}

def Avoiding (p : I → SimplePathPiece G) (v : V) := {i : I // v ∉ (p i).walk.support}
def Meeting (p : I → SimplePathPiece G) (v : V) := {i : I // v ∈ (p i).walk.support}
def DeleteIndex (p : I → SimplePathPiece G) (v : V) :=
  Avoiding p v ⊕ (Meeting p v × Bool)

instance (p : I → SimplePathPiece G) (v : V) : Fintype (Avoiding p v) := by
  classical
  exact inferInstanceAs (Fintype {i : I // v ∉ (p i).walk.support})
instance (p : I → SimplePathPiece G) (v : V) : Fintype (Meeting p v) := by
  classical
  exact inferInstanceAs (Fintype {i : I // v ∈ (p i).walk.support})
instance (p : I → SimplePathPiece G) (v : V) : Fintype (DeleteIndex p v) :=
  inferInstanceAs (Fintype (Avoiding p v ⊕ (Meeting p v × Bool)))

def deleted (p : I → SimplePathPiece G) (v : V) : DeleteIndex p v → SimplePathPiece G
  | .inl i => p i.val
  | .inr (i,true) => ⟨_,_,((p i.val).walk.takeUntil v i.property).dropLast,
      ((p i.val).isPath.takeUntil i.property).dropLast⟩
  | .inr (i,false) => ⟨_,_,((p i.val).walk.dropUntil v i.property).tail,
      ((p i.val).isPath.dropUntil i.property).tail⟩

def parent (p : I → SimplePathPiece G) (v : V) : DeleteIndex p v → I
  | .inl i => i.val
  | .inr (i,_) => i.val

def oldEnd (p : I → SimplePathPiece G) (v x : V) : DeleteIndex p v → Prop
  | .inl i => (p i.val).start = x ∨ (p i.val).finish = x
  | .inr (i,true) => (p i.val).start = x
  | .inr (i,false) => (p i.val).finish = x

def newEnd (p : I → SimplePathPiece G) (v x : V) : DeleteIndex p v → Prop
  | .inl _ => False
  | .inr (i,true) => ((p i.val).walk.takeUntil v i.property).penultimate = x
  | .inr (i,false) => ((p i.val).walk.dropUntil v i.property).snd = x

lemma deleted_ends {V : Type cycleUniverse32} {I : Type cycleUniverse33} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v x : V) (j : DeleteIndex p v) :
    (deleted p v j).start = x ∨ (deleted p v j).finish = x ↔
      oldEnd p v x j ∨ newEnd p v x j := by
  rcases j with i | ⟨i,b⟩
  · simp [deleted, oldEnd, newEnd]
  · cases b <;> simp [deleted, oldEnd, newEnd, or_comm]

lemma deleted_edges_subset {V : Type cycleUniverse34} {I : Type cycleUniverse35} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V) (j : DeleteIndex p v) :
    (deleted p v j).walk.edgeSet ⊆ (p (parent p v j)).walk.edgeSet := by
  rcases j with i | ⟨i,b⟩
  · exact Set.Subset.rfl
  · have h := (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.2.1
    cases b
    · intro e he
      exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
        h ▸ Or.inr he).1
    · intro e he
      exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
        h ▸ Or.inl he).1

lemma deleted_positive_avoids {V : Type cycleUniverse36} {I : Type cycleUniverse37} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V) (j : DeleteIndex p v)
    (hpos : 0 < (deleted p v j).walk.length) : v ∉ (deleted p v j).walk.support := by
  rcases j with i | ⟨i,b⟩
  · exact i.property
  · have h := delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property
    cases b
    · exact h.2.2.2.2.2.1 hpos
    · exact h.2.2.2.2.1 hpos

lemma deleted_disjoint (p : I → SimplePathPiece G) (v : V)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet) :
    Pairwise fun j k => Disjoint (deleted p v j).walk.edgeSet (deleted p v k).walk.edgeSet := by
  intro j k hjk
  by_cases he : parent p v j = parent p v k
  · rcases j with i | ⟨i,b⟩ <;> rcases k with l | ⟨l,c⟩
    · exact (hjk (congrArg Sum.inl (Subtype.ext he))).elim
    · exact (i.property (show v ∈ (p i.val).walk.support from (show i.val = l.val from he).symm ▸ l.property)).elim
    · exact (l.property (show v ∈ (p l.val).walk.support from (show i.val = l.val from he) ▸ i.property)).elim
    · have hil : i = l := Subtype.ext he
      subst l
      cases b <;> cases c
      · exact (hjk rfl).elim
      · exact (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.1.symm
      · exact (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.1
      · exact (hjk rfl).elim
  · exact (hd he).mono (deleted_edges_subset p v j) (deleted_edges_subset p v k)

lemma deleted_old_load (p : I → SimplePathPiece G) (v x : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hload : (Finset.univ.filter fun i => (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    (Finset.univ.filter fun j : DeleteIndex p v => oldEnd p v x j).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hjp : (p (parent p v j)).start = x ∨ (p (parent p v j)).finish = x := by
    have h := (Finset.mem_filter.mp hj).2
    rcases j with i | ⟨i,b⟩
    · exact h
    · cases b
      · exact Or.inr h
      · exact Or.inl h
  have hkp : (p (parent p v k)).start = x ∨ (p (parent p v k)).finish = x := by
    have h := (Finset.mem_filter.mp hk).2
    rcases k with i | ⟨i,b⟩
    · exact h
    · cases b
      · exact Or.inr h
      · exact Or.inl h
  have he := Finset.card_le_one.mp hload (parent p v j)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hjp⟩) (parent p v k)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkp⟩)
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  rcases j with i | ⟨i,b⟩ <;> rcases k with l | ⟨l,c⟩
  · exact congrArg Sum.inl (Subtype.ext he)
  · exact (i.property (show v ∈ (p i.val).walk.support from (show i.val = l.val from he).symm ▸ l.property)).elim
  · exact (l.property (show v ∈ (p l.val).walk.support from (show i.val = l.val from he) ▸ i.property)).elim
  · have hil : i = l := Subtype.ext he
    subst l
    cases b <;> cases c
    · rfl
    · exact (hne _ (hk'.trans hj'.symm)).elim
    · exact (hne _ (hj'.trans hk'.symm)).elim
    · rfl

lemma deleted_new_load (p : I → SimplePathPiece G) (v x : V)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet) :
    (Finset.univ.filter fun j : DeleteIndex p v =>
      0 < (deleted p v j).walk.length ∧ newEnd p v x j).card ≤ 1 := by
  classical
  have h := delete_vertex_new_endpoint_load
    (fun i : Meeting p v => (p i.val).walk) (fun i => (p i.val).isPath)
    (fun i => i.property)
    (fun i j hij => hd (fun he => hij (Subtype.ext he))) x
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  rcases j with i | ⟨i,b⟩
  · exact False.elim hj'.2
  rcases k with l | ⟨l,c⟩
  · exact False.elim hk'.2
  apply congrArg Sum.inr
  apply Finset.card_le_one.mp h
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases b <;> exact hj'
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases c <;> exact hk'

theorem deleted_endpoint_load (p : I → SimplePathPiece G) (v x : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet)
    (hload : (Finset.univ.filter fun i => (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    (Finset.univ.filter fun j : DeleteIndex p v => 0 < (deleted p v j).walk.length ∧
      ((deleted p v j).start = x ∨ (deleted p v j).finish = x)).card ≤ 2 := by
  classical
  let A := Finset.univ.filter (fun j : DeleteIndex p v => oldEnd p v x j)
  let B := Finset.univ.filter (fun j : DeleteIndex p v =>
    0 < (deleted p v j).walk.length ∧ newEnd p v x j)
  have hsub : (Finset.univ.filter fun j : DeleteIndex p v =>
      0 < (deleted p v j).walk.length ∧
      ((deleted p v j).start = x ∨ (deleted p v j).finish = x)) ⊆ A ∪ B := by
    intro j hj
    obtain ⟨hpos,hend⟩ := (Finset.mem_filter.mp hj).2
    rcases (deleted_ends p v x j).mp hend with ho | hn
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpos,hn⟩)
  have ha := deleted_old_load p v x hne hload
  have hb := deleted_new_load p v x hd
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
  dsimp [A,B] at hc
  omega

theorem deleted_union (p : I → SimplePathPiece G) (v : V) :
    (⋃ j : DeleteIndex p v, (deleted p v j).walk.edgeSet) =
      {e | (∃ i, e ∈ (p i).walk.edgeSet) ∧ v ∉ e} := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    refine ⟨⟨parent p v j, deleted_edges_subset p v j hj⟩,?_⟩
    rcases j with i | ⟨i,b⟩
    · intro hv
      exact i.property (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
        (Or.inr ⟨e,hj,hv⟩))
    · have h := (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.2.1
      cases b
      · exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
          h ▸ Or.inr hj).2
      · exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
          h ▸ Or.inl hj).2
  · rintro ⟨⟨i,hi⟩,hv⟩
    by_cases hs : v ∈ (p i).walk.support
    · have h := (delete_vertex_from_path (p i).walk (p i).isPath hs).2.2.2.1
      have he : e ∈ ((p i).walk.takeUntil v hs).dropLast.edgeSet ∪
          ((p i).walk.dropUntil v hs).tail.edgeSet := h.symm ▸ ⟨hi,hv⟩
      rcases he with hl | hr
      · exact Set.mem_iUnion.mpr ⟨Sum.inr (⟨i,hs⟩,true),hl⟩
      · exact Set.mem_iUnion.mpr ⟨Sum.inr (⟨i,hs⟩,false),hr⟩
    · exact Set.mem_iUnion.mpr ⟨Sum.inl ⟨i,hs⟩,hi⟩

theorem deleted_positive_union (p : I → SimplePathPiece G) (v : V) :
    (⋃ j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length},
      (deleted p v j.val).walk.edgeSet) =
      {e | (∃ i, e ∈ (p i).walk.edgeSet) ∧ v ∉ e} := by
  rw [← deleted_union p v]
  ext e
  constructor
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    exact Set.mem_iUnion.mpr ⟨j.val,hj⟩
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    have hp : 0 < (deleted p v j).walk.length := by
      by_contra hn
      have hz : (deleted p v j).walk.length = 0 := by omega
      have hn' := SimpleGraph.Walk.length_eq_zero_iff.mp hz
      have he' := SimpleGraph.Walk.edges_eq_nil.mpr hn'
      have hmem : e ∈ (deleted p v j).walk.edges := hj
      exact List.not_mem_nil (he' ▸ hmem)
    exact Set.mem_iUnion.mpr ⟨⟨j,hp⟩,hj⟩

def deletedInduced (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    SimplePathPiece (G.induce {x | x ≠ v}) := by
  let q := deleted p v j.val
  have havo : ∀ x ∈ q.walk.support, x ∈ ({x | x ≠ v} : Set V) := by
    intro x hx he
    subst x
    exact deleted_positive_avoids p v j.val j.property hx
  exact ⟨_,_, q.walk.induce _ havo, by
    apply SimpleGraph.Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce _).toHom)
    simpa using q.isPath⟩

end SimplePathPiece

end
end ErdosGallai.Batch
end
/-! ### Upstream module `Combinatorics/CycleDecomposition/BatchEndpoints.lean` -/

noncomputable section
namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
theorem endpoint_partition_of_family {V : Type cycleUniverse1} {I : Type cycleUniverse2} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = G.edgeSet)
    (hl : ∀ x : V, (Finset.univ.filter fun i =>
      (P i).start = x ∨ (P i).finish = x).card ≤ 2) : EndpointPathPartition G := by
  classical
  let e := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I,fun j => P (e j),?_,?_,?_,endpoint_path_count P hl⟩
  · intro i j hij
    exact hd (fun he => hij (e.injective he))
  · rw [← hc]
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e i,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,by rw [e.apply_symm_apply]; exact hi⟩
  · intro x
    have heq : (Finset.univ.filter fun j => (P (e j)).start = x ∨ (P (e j)).finish = x).card =
        (Finset.univ.filter fun i => (P i).start = x ∨ (P i).finish = x).card := by
      apply Finset.card_bij (fun j _ => e j)
      · intro i hi; simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
      · intro i hi j hj he; exact e.injective he
      · intro i hi; exact ⟨e.symm i,by simpa using hi, by simp⟩
    rw [heq]
    exact hl x

def PositiveSimplePath.mapIso {V : Type cycleUniverse3} {W : Type cycleUniverse4} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (P : PositiveSimplePath G) : PositiveSimplePath H :=
  ⟨f P.start,f P.finish,P.walk.map f.toHom,P.isPath.map f.injective,by simpa using P.positive⟩

theorem endpoint_partition_mapIso {V : Type cycleUniverse5} {W : Type cycleUniverse6} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H)
    (hp : EndpointPathPartition G) : EndpointPathPartition H := by
  classical
  obtain ⟨k,P,hd,hc,hl,hk⟩ := hp
  apply endpoint_partition_of_family (fun i => (P i).mapIso f)
  · intro i j hij
    change Disjoint ((P i).walk.map f.toHom).edgeSet ((P j).walk.map f.toHom).edgeSet
    simp only [SimpleGraph.Walk.edgeSet_map]
    exact (Set.disjoint_image_iff (Sym2.map.injective f.injective)).mpr (hd hij)
  · have hmap : Sym2.map f.toHom '' G.edgeSet = H.edgeSet := by
      ext e
      induction e using Sym2.inductionOn with | _ u v =>
        constructor
        · rintro ⟨e,he,heq⟩
          induction e using Sym2.inductionOn with | _ a b =>
            have ha : H.Adj (f a) (f b) := f.toHom.map_adj he
            exact heq ▸ ha
        · intro huv
          refine ⟨s(f.symm u, f.symm v), f.symm.toHom.map_adj huv,?_⟩
          simp
    change (⋃ i, ((P i).walk.map f.toHom).edgeSet) = H.edgeSet
    simp_rw [SimpleGraph.Walk.edgeSet_map]
    rw [← Set.image_iUnion,hc,hmap]
  · intro x
    have heq : (Finset.univ.filter fun i => ((P i).mapIso f).start = x ∨
        ((P i).mapIso f).finish = x) =
        (Finset.univ.filter fun i => (P i).start = f.symm x ∨ (P i).finish = f.symm x) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      change (f (P i).start = x ∨ f (P i).finish = x) ↔ _
      exact or_congr (f.toEquiv.eq_symm_apply.symm) (f.toEquiv.eq_symm_apply.symm)
    rw [heq]
    exact hl _

namespace SimplePathPiece
variable {V : Type cycleUniverse7} {I : Type cycleUniverse8} [Fintype V] [Fintype I] [DecidableEq V] {G : SimpleGraph V}

lemma deletedInduced_map {V : Type cycleUniverse9} {I : Type cycleUniverse10} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] [_contextInstance4 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    (deletedInduced p v j).walk.map (SimpleGraph.Embedding.induce _).toHom =
      (deleted p v j.val).walk := by
  exact SimpleGraph.Walk.map_induce _ _

lemma deletedInduced_edges (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    Sym2.map (SimpleGraph.Embedding.induce (G := G) {x | x ≠ v}).toHom ''
      (deletedInduced p v j).walk.edgeSet = (deleted p v j.val).walk.edgeSet := by
  calc
    _ = ((deletedInduced p v j).walk.map
        (SimpleGraph.Embedding.induce {x | x ≠ v}).toHom).edgeSet :=
      (SimpleGraph.Walk.edgeSet_map _ _).symm
    _ = _ := congrArg (fun q : G.Walk (deleted p v j.val).start
        (deleted p v j.val).finish => q.edgeSet) (deletedInduced_map p v j)

def deletedPositive (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    PositiveSimplePath (G.induce {x | x ≠ v}) :=
  { deletedInduced p v j with
    positive := by
      have h := congrArg SimpleGraph.Walk.length (deletedInduced_map p v j)
      rw [SimpleGraph.Walk.length_map] at h
      rw [h]
      exact j.property }

theorem endpoint_partition_after_deletion (p : I → SimplePathPiece G) (v : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet)
    (hc : (⋃ i, (p i).walk.edgeSet) = G.edgeSet)
    (hl : ∀ x : V, x ≠ v → (Finset.univ.filter fun i =>
      (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    EndpointPathPartition (G.induce {x | x ≠ v}) := by
  classical
  let A := {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}
  let f : G.induce {x | x ≠ v} →g G := (SimpleGraph.Embedding.induce _).toHom
  have hf : Function.Injective f := Subtype.val_injective
  apply endpoint_partition_of_family (fun j : A => deletedPositive p v j)
  · intro j k hjk
    have hdis := deleted_disjoint p v hd (fun he => hjk (Subtype.ext he))
    apply Set.disjoint_left.mpr
    intro e hej hek
    have he1 : Sym2.map f e ∈ (deleted p v j.val).walk.edgeSet := by
      rw [← deletedInduced_edges p v j]
      exact ⟨e,hej,rfl⟩
    have he2 : Sym2.map f e ∈ (deleted p v k.val).walk.edgeSet := by
      rw [← deletedInduced_edges p v k]
      exact ⟨e,hek,rfl⟩
    exact Set.disjoint_left.mp hdis he1 he2
  · apply Set.Subset.antisymm
    · intro e he
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
      exact (deletedPositive p v j).walk.edges_subset_edgeSet hj
    · intro e he
      have he' : Sym2.map f e ∈ G.edgeSet ∧ v ∉ Sym2.map f e := by
        induction e using Sym2.inductionOn with | _ a b =>
          refine ⟨he,?_⟩
          change v ∉ s(a.val,b.val)
          simpa only [Sym2.map_mk,Sym2.mem_iff,eq_comm] using not_or.mpr ⟨a.property,b.property⟩
      have hmem : Sym2.map f e ∈ ⋃ j : A, (deleted p v j.val).walk.edgeSet := by
        rw [deleted_positive_union]
        refine ⟨?_,he'.2⟩
        exact Set.mem_iUnion.mp (hc.symm ▸ he'.1)
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hmem
      rw [← deletedInduced_edges p v j] at hj
      obtain ⟨e',he',heq⟩ := hj
      have heq' : e' = e := Sym2.map.injective hf heq
      subst e'
      exact Set.mem_iUnion.mpr ⟨j,he'⟩
  · intro x
    have hb := deleted_endpoint_load p v x.val hne hd (hl x.val x.property)
    have hc' : (Finset.univ.filter fun j : A =>
        (deletedPositive p v j).start = x ∨ (deletedPositive p v j).finish = x).card ≤
        (Finset.univ.filter fun j : DeleteIndex p v => 0 < (deleted p v j).walk.length ∧
          ((deleted p v j).start = x.val ∨ (deleted p v j).finish = x.val)).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro j hj
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,j.property,?_⟩
        rcases (Finset.mem_filter.mp hj).2 with hs | ht
        · exact Or.inl (congrArg Subtype.val hs)
        · exact Or.inr (congrArg Subtype.val ht)
      · exact fun _ _ _ _ he => Subtype.ext he
    convert hc'.trans hb using 1

    congr 1
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]

end SimplePathPiece

def evenAugmentationOldIso {V : Type cycleUniverse11} [Fintype V] (G : SimpleGraph V) :
    G ≃g (evenAugmentation G).induce {x | x ≠ none} where
  toEquiv := Equiv.optionSubtype none ⟨Equiv.refl (Option V),rfl⟩
  map_rel_iff' := Iff.rfl

theorem endpoint_partition_of_augmented_parts {V : Type cycleUniverse12} [Fintype V]
    (G : SimpleGraph V) (hL : LovaszPathCyclePartition (evenAugmentation G)) :
    EndpointPathPartition G := by
  classical
  obtain ⟨k,parts,hparts,hd,hc,hk⟩ := hL
  have hw : ∀ i : Fin k, ∃ (a b : Option V) (p : (evenAugmentation G).Walk a b),
      p.IsTrail ∧ (a ≠ b → p.IsPath) ∧ parts i = p.edgeSet := by
    intro i
    rcases hparts i with ⟨a,b,p,hp,_,he⟩ | ⟨a,p,hp,he⟩
    · exact ⟨a,b,p,hp.isTrail,fun _ => hp,he⟩
    · exact ⟨a,a,p,hp.isTrail,fun h => False.elim (h rfl),he⟩
  choose a b p ht hp he using hw
  have hd' : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet := by
    simpa only [he] using hd
  have hc' : (⋃ i, (p i).edgeSet) = (evenAugmentation G).edgeSet := by
    simpa only [he] using hc
  let S : Finset (Option V) := Finset.univ.image some
  have hS : S.card = Fintype.card V := by
    simp only [S,Finset.card_image_of_injective _ (Option.some_injective V),Finset.card_univ]
  have ho : ∀ x ∈ S, Odd ((evenAugmentation G).degree x) := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact evenAugmentation_old_odd G y
  have hk' : 2 * Fintype.card (Fin k) ≤ S.card + 1 := by
    simpa only [Fintype.card_fin,Fintype.card_option,hS] using hk
  obtain ⟨hopen,hload⟩ := tight_odd_trail_partition (evenAugmentation G) S p ht hd' hc' ho hk'
  let P : Fin k → SimplePathPiece (evenAugmentation G) := fun i =>
    ⟨a i,b i,p i,hp i (hopen i)⟩
  have hload' : ∀ x : Option V, x ≠ none → (Finset.univ.filter fun i =>
      (P i).start = x ∨ (P i).finish = x).card ≤ 1 := by
    intro x hx
    cases x with
    | none => exact False.elim (hx rfl)
    | some x =>
      have h := hload (some x) (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)
      have hpred : (Finset.univ.filter fun i => a i ≠ b i ∧
          (some x = a i ∨ some x = b i)) =
          (Finset.univ.filter fun i => (P i).start = some x ∨ (P i).finish = some x) := by
        ext i
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,P]
        constructor
        · rintro ⟨_,hi⟩
          exact hi.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
        · intro hi
          exact ⟨hopen i,hi.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
      apply le_of_eq
      calc
        _ = _ := congrArg Finset.card hpred.symm
        _ = 1 := by
          convert h using 1
          congr 1
          ext i
          simp only [Finset.mem_filter,Finset.mem_univ,true_and]

  have hdel := SimplePathPiece.endpoint_partition_after_deletion P none hopen hd' hc' hload'
  exact endpoint_partition_mapIso (evenAugmentationOldIso G).symm hdel

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section

theorem lovasz_path_cycle_partition {V : Type cycleUniverse13} [Fintype V] (G : SimpleGraph V) :
    LovaszPathCyclePartition G := by
  classical
  obtain ⟨k,P,hd,hc,hk⟩ := Lovasz.path_cycle_partition G
  refine ⟨k,fun i => (P i).walk.edgeSet,?_,hd,hc,?_⟩
  · intro i
    rcases (P i).simple with hp | ⟨h,hcy⟩
    · exact Or.inl ⟨(P i).start,(P i).finish,(P i).walk,hp.1,hp.2,rfl⟩
    · exact Or.inr ⟨(P i).start,(P i).walk.copy rfl h,hcy,by simp⟩
  · exact hk.trans (Finset.card_le_univ _)

theorem endpoint_path_partition {V : Type cycleUniverse14} [Fintype V] (G : SimpleGraph V) :
    EndpointPathPartition G :=
  endpoint_partition_of_augmented_parts G (lovasz_path_cycle_partition (evenAugmentation G))

end
end ErdosGallai.Batch

end
/-! ### Upstream module `Combinatorics/CycleDecomposition/Pairing.lean` -/

noncomputable section
open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Finset
namespace ErdosGallai.Batch
noncomputable section

def Pairing (V : Type cycleUniverse1) := {f : V → V // Function.Involutive f ∧ ∀ x, f x ≠ x}

namespace Pairing
variable {V : Type cycleUniverse2} {W : Type cycleUniverse3}
instance : CoeFun (Pairing V) (fun _ => V → V) := ⟨Subtype.val⟩
instance [Fintype V] : Fintype (Pairing V) := by
  classical
  unfold Pairing
  infer_instance
@[simp] theorem apply_apply (p : Pairing V) (v : V) : p (p v) = v := p.property.1 v
@[simp] theorem apply_ne (p : Pairing V) (v : V) : p v ≠ v := p.property.2 v

def transport (e : V ≃ W) : Pairing V ≃ Pairing W where
  toFun p := ⟨fun x => e (p (e.symm x)),
    (by intro x; simp), (by intro x h; have := congrArg e.symm h; simp at this)⟩
  invFun p := ⟨fun x => e.symm (p (e x)),
    (by intro x; simp), (by intro x h; have := congrArg e h; simp at this)⟩
  left_inv p := by apply Subtype.ext; funext x; simp
  right_inv p := by apply Subtype.ext; funext x; simp

@[simp] theorem transport_apply (e : V ≃ W) (p : Pairing V) (x : W) :
    transport e p x = e (p (e.symm x)) := rfl

theorem nonempty_of_even [Fintype V] (h : Even (Fintype.card V)) : Nonempty (Pairing V) := by
  classical
  obtain ⟨k,hk⟩ := h
  let q : Pairing (Fin k ⊕ Fin k) := ⟨fun x => x.swap,
    (by intro x; cases x <;> rfl), (by intro x h; cases x <;> nomatch h)⟩
  let e : (Fin k ⊕ Fin k) ≃ V := Fintype.equivOfCardEq (by simpa using hk.symm)
  exact ⟨transport e q⟩

variable [Fintype V]

def oneCount (a b : V) : ℕ := by
  classical
  exact Fintype.card {p : Pairing V // p a = b}
def twoCount (a b c d : V) : ℕ := by
  classical
  exact Fintype.card {p : Pairing V // p a = b ∧ p c = d}

@[simp] theorem oneCount_self (a : V) : oneCount a a = 0 := by
  classical
  unfold oneCount
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun p => p.val.apply_ne a p.property⟩

theorem oneCount_transport (e : V ≃ V) (a b : V) :
    oneCount (e a) (e b) = oneCount a b := by
  classical
  symm
  exact Fintype.card_congr ((transport e).subtypeEquiv (by intro p; simp))

theorem oneCount_eq (a b c : V) (hab : a ≠ b) (hac : a ≠ c) :
    oneCount a b = oneCount a c := by
  classical
  have h := oneCount_transport (Equiv.swap b c) a b
  simpa [Equiv.swap_apply_of_ne_of_ne hab hac] using h.symm

theorem oneCount_balance (a b : V) (hab : a ≠ b) :
    (Fintype.card V - 1) * oneCount a b = Fintype.card (Pairing V) := by
  classical
  have hsum : (∑ c : V, oneCount a c) = Fintype.card (Pairing V) := by
    unfold oneCount
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv (fun p : Pairing V => p a))
  have heq : (∑ c : V, oneCount a c) = ∑ c ∈ (univ.erase a), oneCount a b := by
    rw [← Finset.sum_erase_add _ _ (mem_univ a),oneCount_self,add_zero]
    apply Finset.sum_congr rfl
    intro c hc
    exact oneCount_eq a c b (Finset.mem_erase.mp hc).1.symm hab
  rw [heq,Finset.sum_const,Finset.card_erase_of_mem (mem_univ a)] at hsum
  simpa using hsum

theorem twoCount_transport (e : V ≃ V) (a b c d : V) :
    twoCount (e a) (e b) (e c) (e d) = twoCount a b c d := by
  classical
  symm
  exact Fintype.card_congr ((transport e).subtypeEquiv (by intro p; simp))

theorem twoCount_eq (a b c d e : V)
    (had : a ≠ d) (hae : a ≠ e) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) : twoCount a b c d = twoCount a b c e := by
  classical
  have h := twoCount_transport (Equiv.swap d e) a b c d
  simpa [Equiv.swap_apply_of_ne_of_ne had hae,
    Equiv.swap_apply_of_ne_of_ne hbd hbe,Equiv.swap_apply_of_ne_of_ne hcd hce] using h.symm

theorem twoCount_forbidden (a b c d : V) (hac : a ≠ c) (hbc : b ≠ c)
    (hd : d = a ∨ d = b ∨ d = c) : twoCount a b c d = 0 := by
  classical
  unfold twoCount
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun p => ?_⟩
  rcases p.property with ⟨hab,hcd⟩
  rcases hd with rfl | rfl | rfl
  · have h := congrArg p.val hcd
    simp only [apply_apply,hab] at h
    exact hbc h.symm
  · have h := congrArg p.val hab
    have h' := congrArg p.val hcd
    simp only [apply_apply] at h h'
    exact hac (h.trans h'.symm)
  · exact p.val.apply_ne _ hcd

theorem twoCount_balance (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (Fintype.card V - 3) * twoCount a b c d = oneCount a b := by
  classical
  let Q := {p : Pairing V // p a = b}
  have hsum : (∑ e : V, twoCount a b c e) = oneCount a b := by
    have hcard : ∀ e : V, Fintype.card {p : Q // p.val c = e} = twoCount a b c e := by
      intro e
      apply Fintype.card_congr
      exact ⟨fun p => ⟨p.val.val,p.val.property,p.property⟩,
        fun p => ⟨⟨p.val,p.property.1⟩,p.property.2⟩,fun _ => rfl,fun _ => rfl⟩
    calc
      (∑ e : V, twoCount a b c e) = ∑ e : V, Fintype.card {p : Q // p.val c = e} := by simp_rw [hcard]
      _ = Fintype.card Q := by
        rw [← Fintype.card_sigma]
        exact Fintype.card_congr (Equiv.sigmaFiberEquiv (fun p : Q => p.val c))
      _ = oneCount a b := rfl
  let S : Finset V := {a,b,c}
  have hScard : S.card = 3 := by simp [S,hab,hac,hbc]
  have hsum' : (∑ e : V, twoCount a b c e) = ∑ e ∈ univ \ S, twoCount a b c d := by
    rw [← Finset.sum_sdiff (s₁:=S) (s₂:=univ) (by simp)]
    have hz : ∑ e ∈ S, twoCount a b c e = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      exact twoCount_forbidden a b c e hac hbc (by simpa [S] using he)
    rw [hz,add_zero]
    apply Finset.sum_congr rfl
    intro e he
    have he' : e ≠ a ∧ e ≠ b ∧ e ≠ c := by simpa [S] using (Finset.mem_sdiff.mp he).2
    exact twoCount_eq a b c e d he'.1.symm had he'.2.1.symm hbd he'.2.2.symm hcd
  rw [hsum',Finset.sum_const,Finset.card_sdiff,Finset.inter_univ,hScard] at hsum
  simpa using hsum

theorem one_fraction (hV : Even (Fintype.card V)) (a b : V) (hab : a ≠ b) :
    (oneCount a b : ℝ) / Fintype.card (Pairing V) = 1 / (Fintype.card V - 1 : ℝ) := by
  classical
  have hn : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff_nontrivial.mpr ⟨a,b,hab⟩
  have hbal := oneCount_balance a b hab
  have hbal' : ((Fintype.card V:ℝ)-1)*(oneCount a b:ℝ) = Fintype.card (Pairing V) := by
    have h := congrArg (fun n : ℕ => (n:ℝ)) hbal
    simpa only [Nat.cast_mul,Nat.cast_sub (show 1 ≤ Fintype.card V by omega),Nat.cast_one] using h
  have : Nonempty (Pairing V) := nonempty_of_even hV
  have hp : (0:ℝ) < Fintype.card (Pairing V) := by exact_mod_cast Fintype.card_pos
  have hn' : (0:ℝ) < Fintype.card V-1 := by
    have hnR : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    linarith
  apply (div_eq_div_iff hp.ne' hn'.ne').mpr
  nlinarith

theorem two_fraction (hV : Even (Fintype.card V)) (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (twoCount a b c d : ℝ) / Fintype.card (Pairing V) =
      1 / ((Fintype.card V - 1 : ℝ)*(Fintype.card V - 3 : ℝ)) := by
  classical
  have hn : 4 ≤ Fintype.card V := by
    have : ({a,b,c,d}:Finset V).card = 4 := by simp [hab,hac,had,hbc,hbd,hcd]
    exact this.symm ▸ Finset.card_le_univ _
  have hone := oneCount_balance a b hab
  have htwo := twoCount_balance a b c d hab hac had hbc hbd hcd
  have hb : ((Fintype.card V:ℝ)-1)*((Fintype.card V:ℝ)-3)*(twoCount a b c d:ℝ) =
      Fintype.card (Pairing V) := by
    have h1 : ((Fintype.card V:ℝ)-1)*(oneCount a b:ℝ) = Fintype.card (Pairing V) := by
      have h := congrArg (fun n : ℕ => (n:ℝ)) hone
      simpa only [Nat.cast_mul,Nat.cast_sub (show 1 ≤ Fintype.card V by omega),Nat.cast_one] using h
    have h2 : ((Fintype.card V:ℝ)-3)*(twoCount a b c d:ℝ) = oneCount a b := by
      have h := congrArg (fun n : ℕ => (n:ℝ)) htwo
      simpa only [Nat.cast_mul,Nat.cast_sub (show 3 ≤ Fintype.card V by omega),Nat.cast_ofNat] using h
    nlinarith
  have : Nonempty (Pairing V) := nonempty_of_even hV
  have hp : (0:ℝ) < Fintype.card (Pairing V) := by exact_mod_cast Fintype.card_pos
  have hn' : (0:ℝ) < Fintype.card V-3 := by
    have hnR : (4:ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    linarith
  have hn'' : (0:ℝ) < Fintype.card V-1 := by linarith
  apply (div_eq_div_iff hp.ne' (mul_pos hn'' hn').ne').mpr
  nlinarith

end Pairing
end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section

def finiteAverage {α : Type cycleUniverse4} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

lemma finiteAverage_equiv {α : Type cycleUniverse5} {β : Type cycleUniverse6} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : finiteAverage (fun x => f (e x)) = finiteAverage f := by
  unfold finiteAverage
  rw [e.sum_comp,Fintype.card_congr e]

lemma finiteAverage_add {α : Type cycleUniverse7} [Fintype α] (f g : α → ℝ) :
    finiteAverage (fun x => f x+g x) = finiteAverage f+finiteAverage g := by
  simp [finiteAverage,Finset.sum_add_distrib,add_div]

lemma finiteAverage_sum {α : Type cycleUniverse8} {ι : Type cycleUniverse9} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    finiteAverage (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, finiteAverage (f i) := by
  unfold finiteAverage
  rw [Finset.sum_comm,Finset.sum_div]

lemma finiteAverage_const {α : Type cycleUniverse11} [Fintype α] [Nonempty α] (r : ℝ) :
    finiteAverage (fun _ : α => r) = r := by
  have h : (Fintype.card α:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [finiteAverage,h]

lemma finiteAverage_mono {α : Type cycleUniverse12} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : finiteAverage f ≤ finiteAverage g := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun a _ => h a)

lemma finiteAverage_prod {α : Type cycleUniverse13} {β : Type cycleUniverse14} [Fintype α] [Fintype β]
    (f : α → ℝ) (g : β → ℝ) :
    finiteAverage (fun x : α × β => f x.1*g x.2) = finiteAverage f*finiteAverage g := by
  unfold finiteAverage
  rw [Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

lemma exists_le_finiteAverage {α : Type cycleUniverse15} [Fintype α] [Nonempty α] (f : α → ℝ) :
    ∃ a, f a ≤ finiteAverage f := by
  have hp : (0:ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have h : ∑ a, f a ≤ ∑ _a : α, finiteAverage f := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,finiteAverage]
    field_simp
    rfl
  obtain ⟨a,ha,h⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty) h
  exact ⟨a,h⟩

lemma finiteAverage_indicator {α : Type cycleUniverse16} [Fintype α] (P : α → Prop) [DecidablePred P] :
    finiteAverage (fun a => if P a then 1 else 0) = (Fintype.card {a // P a} : ℝ)/Fintype.card α := by
  unfold finiteAverage
  congr 1
  simp [Fintype.card_subtype]

lemma finiteAverage_pi_eval {ι : Type cycleUniverse17} [Fintype ι] [DecidableEq ι] {Ω : ι → Type cycleUniverse60}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] (i : ι) (f : Ω i → ℝ) :
    finiteAverage (fun ω : ∀ j, Ω j => f (ω i)) = finiteAverage f := by
  classical
  let e := Equiv.piSplitAt i Ω
  have he := finiteAverage_equiv e.symm (fun ω : ∀ j, Ω j => f (ω i))
  have he' : finiteAverage (fun x : Ω i × (∀ j : {j // j ≠ i}, Ω j.val) => f x.1) =
      finiteAverage f := by
    have h := finiteAverage_prod f (fun _ : (∀ j : {j // j ≠ i}, Ω j.val) => (1:ℝ))
    simpa only [mul_one,finiteAverage_const] using h
  rw [← he]
  simpa [e,Equiv.piSplitAt_symm_apply] using he'

lemma finiteAverage_pi_pair {ι : Type cycleUniverse18} [Fintype ι] [DecidableEq ι] {Ω : ι → Type cycleUniverse61}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] (i j : ι) (hij : i ≠ j)
    (f : Ω i → ℝ) (g : Ω j → ℝ) :
    finiteAverage (fun ω : ∀ k, Ω k => f (ω i)*g (ω j)) = finiteAverage f*finiteAverage g := by
  classical
  let e := Equiv.piSplitAt i Ω
  rw [← finiteAverage_equiv e.symm (fun ω : ∀ k, Ω k => f (ω i)*g (ω j))]
  have hfun : (fun x => f (e.symm x i)*g (e.symm x j)) =
      (fun x : Ω i × (∀ k : {k // k ≠ i}, Ω k.val) => f x.1*g (x.2 ⟨j,hij.symm⟩)) := by
    funext x
    simp [e,Equiv.piSplitAt_symm_apply,hij.symm]
  rw [hfun,finiteAverage_prod f (fun x : (∀ k : {k // k ≠ i}, Ω k.val) => g (x ⟨j,hij.symm⟩)),
    finiteAverage_pi_eval]

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
noncomputable section

abbrev PairingSpace (V : Type cycleUniverse19) [Fintype V] := Pairing (V ⊕ Fin (Fintype.card V % 2))

lemma pairingSpace_even (V : Type cycleUniverse20) [Fintype V] :
    Even (Fintype.card (V ⊕ Fin (Fintype.card V % 2))) := by
  simp only [Fintype.card_sum,Fintype.card_fin,Nat.even_iff]
  omega

instance pairingSpace_nonempty (V : Type cycleUniverse21) [Fintype V] : Nonempty (PairingSpace V) :=
  Pairing.nonempty_of_even (pairingSpace_even V)

def paired {V : Type cycleUniverse22} [Fintype V] (p : PairingSpace V) (u v : V) : Prop :=
  p (Sum.inl u) = Sum.inl v

instance paired_decidable {V : Type cycleUniverse23} [Fintype V] (p : PairingSpace V) (u v : V) :
    Decidable (paired p u v) := Classical.propDecidable _

lemma paired_symm {V : Type cycleUniverse25} [Fintype V] (p : PairingSpace V) {u v : V}
    (h : paired p u v) : paired p v u := by
  have hh := congrArg p h
  simpa only [paired,Pairing.apply_apply] using hh.symm

lemma paired_first_moment {V : Type cycleUniverse30} [Fintype V] (u v : V) (huv : u ≠ v) :
    finiteAverage (fun p : PairingSpace V => if paired p u v then 1 else 0) =
      1 / ((Fintype.card V:ℝ) + (Fintype.card V % 2 : ℕ) - 1) := by
  classical
  rw [finiteAverage_indicator]
  have h := Pairing.one_fraction (pairingSpace_even V) (Sum.inl u) (Sum.inl v)
    (by simpa using huv)
  simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add] at h
  dsimp only [Pairing.oneCount,paired] at h ⊢
  convert h using 1
  congr 2

lemma paired_two_moment {V : Type cycleUniverse31} [Fintype V] (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    finiteAverage (fun p : PairingSpace V => if paired p a b ∧ paired p c d then 1 else 0) =
      1 / (((Fintype.card V:ℝ)+(Fintype.card V%2:ℕ)-1)*
        ((Fintype.card V:ℝ)+(Fintype.card V%2:ℕ)-3)) := by
  classical
  rw [finiteAverage_indicator]
  have h := Pairing.two_fraction (pairingSpace_even V)
    (Sum.inl a) (Sum.inl b) (Sum.inl c) (Sum.inl d)
    (by simpa using hab) (by simpa using hac) (by simpa using had)
    (by simpa using hbc) (by simpa using hbd) (by simpa using hcd)
  simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add] at h
  dsimp only [Pairing.twoCount,paired] at h ⊢
  convert h using 1
  congr 2

lemma paired_first_bound {V : Type cycleUniverse32} [Fintype V] (hV : 2 ≤ Fintype.card V)
    (u v : V) (huv : u ≠ v) :
    finiteAverage (fun p : PairingSpace V => if paired p u v then 1 else 0) ≤
      1 / ((Fintype.card V:ℝ)-1) := by
  classical
  rw [paired_first_moment u v huv]
  have hn : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  have hm : (0:ℝ) ≤ (Fintype.card V%2:ℕ) := Nat.cast_nonneg _
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

lemma paired_two_bound {V : Type cycleUniverse33} [Fintype V] (hV : 4 ≤ Fintype.card V)
    (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    finiteAverage (fun p : PairingSpace V => if paired p a b ∧ paired p c d then 1 else 0) ≤
      1 / (((Fintype.card V:ℝ)-1)*((Fintype.card V:ℝ)-3)) := by
  classical
  rw [paired_two_moment a b c d hab hac had hbc hbd hcd]
  have hn : (4:ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  have hm : (0:ℝ) ≤ (Fintype.card V%2:ℕ) := Nat.cast_nonneg _
  apply one_div_le_one_div_of_le (mul_pos (by linarith) (by linarith))
  exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable

lemma finiteAverage_or_le {Ω : Type cycleUniverse34} [Fintype Ω] (P Q : Ω → Prop) :
    finiteAverage (fun ω => if P ω ∨ Q ω then 1 else 0) ≤
      finiteAverage (fun ω => if P ω then 1 else 0) +
      finiteAverage (fun ω => if Q ω then 1 else 0) := by
  rw [← finiteAverage_add]
  apply finiteAverage_mono
  intro ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp,hq]

lemma pairing_patterns_internal {V : Type cycleUniverse36} [Fintype V] (hV : 4 ≤ Fintype.card V)
    (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    finiteAverage (fun p : PairingSpace V =>
      if (paired p a c ∧ paired p b d) ∨ (paired p a d ∧ paired p b c) then 1 else 0) ≤
      2 / (((Fintype.card V:ℝ)-1)*((Fintype.card V:ℝ)-3)) := by
  have h₁ := paired_two_bound hV a c b d hac hab had hbc.symm hcd hbd
  have h₂ := paired_two_bound hV a d b c had hab hac hbd.symm hcd.symm hbc
  have h := finiteAverage_or_le
    (fun p : PairingSpace V => paired p a c ∧ paired p b d)
    (fun p : PairingSpace V => paired p a d ∧ paired p b c)
  calc
    _ ≤ finiteAverage (fun p : PairingSpace V => if paired p a c ∧ paired p b d then 1 else 0) +
        finiteAverage (fun p : PairingSpace V => if paired p a d ∧ paired p b c then 1 else 0) := by
      convert h using 1 <;> congr 3 <;> funext p <;> split_ifs <;> rfl
    _ ≤ 1 / (((Fintype.card V:ℝ)-1)*((Fintype.card V:ℝ)-3)) +
      1 / (((Fintype.card V:ℝ)-1)*((Fintype.card V:ℝ)-3)) := add_le_add h₁ h₂
    _ = _ := by ring

lemma pairing_patterns_cross {I : Type cycleUniverse37} [Fintype I] [DecidableEq I]
    {V : I → Type cycleUniverse63} [∀ i, Fintype (V i)] (i j : I) (hij : i ≠ j)
    (a c : V i) (hac : a ≠ c) (b d : V j) (hbd : b ≠ d) :
    finiteAverage (fun p : ∀ k, PairingSpace (V k) =>
      if paired (p i) a c ∧ paired (p j) b d then 1 else 0) =
      (1 / ((Fintype.card (V i):ℝ)+(Fintype.card (V i)%2:ℕ)-1)) *
      (1 / ((Fintype.card (V j):ℝ)+(Fintype.card (V j)%2:ℕ)-1)) := by
  have hind : (fun p : ∀ k, PairingSpace (V k) =>
      if paired (p i) a c ∧ paired (p j) b d then (1:ℝ) else 0) =
      (fun p => (if paired (p i) a c then 1 else 0)*(if paired (p j) b d then 1 else 0)) := by
    funext p
    split_ifs <;> simp_all
  rw [hind,finiteAverage_pi_pair (Ω:=fun k => PairingSpace (V k)) i j hij
    (fun p => if paired p a c then 1 else 0) (fun p => if paired p b d then 1 else 0),paired_first_moment a c hac,paired_first_moment b d hbd]

lemma pairing_patterns_cross_bound {I : Type cycleUniverse38} [Fintype I] [DecidableEq I]
    {V : I → Type cycleUniverse64} [∀ i, Fintype (V i)] (i j : I) (hij : i ≠ j)
    (hi : 2 ≤ Fintype.card (V i)) (hj : 2 ≤ Fintype.card (V j))
    (a c : V i) (hac : a ≠ c) (b d : V j) (hbd : b ≠ d) :
    finiteAverage (fun p : ∀ k, PairingSpace (V k) =>
      if paired (p i) a c ∧ paired (p j) b d then 1 else 0) ≤
      1 / (((Fintype.card (V i):ℝ)-1)*((Fintype.card (V j):ℝ)-1)) := by
  rw [pairing_patterns_cross i j hij a c hac b d hbd,one_div_mul_one_div]
  have hi' : (2:ℝ) ≤ Fintype.card (V i) := by exact_mod_cast hi
  have hj' : (2:ℝ) ≤ Fintype.card (V j) := by exact_mod_cast hj
  have hmi : (0:ℝ) ≤ (Fintype.card (V i)%2:ℕ) := Nat.cast_nonneg _
  have hmj : (0:ℝ) ≤ (Fintype.card (V j)%2:ℕ) := Nat.cast_nonneg _
  apply one_div_le_one_div_of_le (mul_pos (by linarith) (by linarith))
  exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
noncomputable section
namespace Pairing
variable {V : Type cycleUniverse39}

def pairSetoid (p : Pairing V) : Setoid V where
  r u v := u = v ∨ p u = v
  iseqv := ⟨fun _ => Or.inl rfl, (by
    intro u v h
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (by have hh := congrArg p h; simpa using hh.symm)), (by
    intro u v w h1 h2
    rcases h1 with rfl | h1
    · exact h2
    rcases h2 with rfl | h2
    · exact Or.inr h1
    · left
      have hh := congrArg p h1
      simpa only [apply_apply,h2] using hh)⟩

def PairQuotient (p : Pairing V) := Quotient (pairSetoid p)

instance [Fintype V] (p : Pairing V) : Fintype (PairQuotient p) := by
  classical
  unfold PairQuotient
  infer_instance

instance (p : Pairing V) : DecidableEq (PairQuotient p) := Classical.decEq _

def project (p : Pairing V) (v : V) : PairQuotient p := Quotient.mk (pairSetoid p) v

lemma project_eq_iff (p : Pairing V) (u v : V) :
    project p u = project p v ↔ u = v ∨ p u = v := Quotient.eq

lemma project_surjective (p : Pairing V) : Function.Surjective (project p) := by
  intro q
  exact Quotient.exists_rep q

@[simp] lemma project_apply (p : Pairing V) (v : V) : project p (p v) = project p v :=
  (project_eq_iff p _ _).mpr (Or.inr (apply_apply p v))

lemma fiber_card [Fintype V] (p : Pairing V) (q : PairQuotient p) :
    Fintype.card {v // project p v = q} = 2 := by
  classical
  obtain ⟨x,rfl⟩ := project_surjective p q
  rw [Fintype.card_subtype]
  have heq : (univ.filter (fun v => project p v = project p x)) = {x,p x} := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    rw [project_eq_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · right
        have hh := congrArg p h
        simpa only [apply_apply] using hh
    · rintro (h | h)
      · exact Or.inl h
      · right
        subst v
        simp
  rw [heq]
  simp [Ne.symm (apply_ne p x)]

lemma card_pairQuotient [Fintype V] (p : Pairing V) :
    2 * Fintype.card (PairQuotient p) = Fintype.card V := by
  classical
  have h : (∑ q : PairQuotient p, Fintype.card {v // project p v = q}) = Fintype.card V := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv (project p))
  simpa only [fiber_card,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_comm] using h
end Pairing

def oldProject {V : Type cycleUniverse40} [Fintype V] (p : PairingSpace V) (v : V) : Pairing.PairQuotient p :=
  p.project (Sum.inl v)

lemma oldProject_eq_iff {V : Type cycleUniverse41} [Fintype V] (p : PairingSpace V) (u v : V) :
    oldProject p u = oldProject p v ↔ u = v ∨ paired p u v := by
  simp only [oldProject,Pairing.project_eq_iff,Sum.inl.injEq,paired]

lemma dummy_partner_is_old {V : Type cycleUniverse42} [Fintype V] (p : PairingSpace V)
    (d : Fin (Fintype.card V % 2)) : ∃ v : V, p (Sum.inr d) = Sum.inl v := by
  cases h : p (Sum.inr d) with
  | inl v => exact ⟨v,rfl⟩
  | inr e =>
    have he : e = d := by
      apply Fin.ext
      have hd := d.isLt
      have he := e.isLt
      have hh := Nat.mod_lt (Fintype.card V) (by omega : 0 < 2)
      omega
    subst e
    exact False.elim (p.apply_ne _ h)

lemma oldProject_surjective {V : Type cycleUniverse43} [Fintype V] (p : PairingSpace V) :
    Function.Surjective (oldProject p) := by
  intro q
  obtain ⟨x,rfl⟩ := p.project_surjective q
  cases x with
  | inl v => exact ⟨v,rfl⟩
  | inr d =>
    obtain ⟨v,hv⟩ := dummy_partner_is_old p d
    refine ⟨v,?_⟩
    change p.project (Sum.inl v) = p.project (Sum.inr d)
    rw [← hv,p.project_apply]

lemma old_quotient_order {V : Type cycleUniverse44} [Fintype V] (p : PairingSpace V) :
    Fintype.card (Pairing.PairQuotient p) = Fintype.card V - Fintype.card V / 2 := by
  have h := p.card_pairQuotient
  simp only [Fintype.card_sum,Fintype.card_fin] at h
  omega

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
noncomputable section

variable {V : Type cycleUniverse46} {I : Type cycleUniverse47} [Fintype V] [Fintype I] (X : I → Finset V)

abbrev Outside := {v : V // ∀ i, v ∉ X i}
abbrev FoldDomain := Outside X ⊕ (Σ i, X i)

def unfoldVertex : FoldDomain X → V
  | Sum.inl v => v.val
  | Sum.inr v => v.2.val

lemma unfoldVertex_bijective {V : Type cycleUniverse48} {I : Type cycleUniverse49} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (hd : Pairwise (fun i j => Disjoint (X i) (X j))) :
    Function.Bijective (unfoldVertex X) := by
  classical
  constructor
  · rintro (u | ⟨i,u⟩) (v | ⟨j,v⟩) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · change u.val = v.val at h
      exact False.elim (u.property j (h.symm ▸ v.property))
    · change u.val = v.val at h
      exact False.elim (v.property i (h ▸ u.property))
    · change u.val = v.val at h
      have hij : i = j := by
        by_contra hij
        exact Finset.disjoint_left.mp (hd hij) u.property (h.symm ▸ v.property)
      subst j
      exact congrArg Sum.inr (Sigma.ext rfl (heq_of_eq (Subtype.ext h)))
  · intro v
    by_cases h : ∃ i, v ∈ X i
    · obtain ⟨i,hi⟩ := h
      exact ⟨Sum.inr ⟨i,⟨v,hi⟩⟩,rfl⟩
    · exact ⟨Sum.inl ⟨v,by simpa only [not_exists] using h⟩,rfl⟩

def splitEquiv (hd : Pairwise (fun i j => Disjoint (X i) (X j))) : FoldDomain X ≃ V :=
  Equiv.ofBijective (unfoldVertex X) (unfoldVertex_bijective X hd)

abbrev FamilyQuotient (p : ∀ i, PairingSpace (X i)) :=
  Outside X ⊕ (Σ i, Pairing.PairQuotient (p i))

instance (p : ∀ i, PairingSpace (X i)) : Fintype (FamilyQuotient X p) := by
  classical
  unfold FamilyQuotient
  infer_instance

instance (p : ∀ i, PairingSpace (X i)) : DecidableEq (FamilyQuotient X p) := Classical.decEq _

def foldOnDomain (p : ∀ i, PairingSpace (X i)) : FoldDomain X → FamilyQuotient X p
  | Sum.inl v => Sum.inl v
  | Sum.inr ⟨i,v⟩ => Sum.inr ⟨i,oldProject (p i) v⟩

def familyProject (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) : V → FamilyQuotient X p :=
  foldOnDomain X p ∘ (splitEquiv X hd).symm

lemma familyProject_surjective (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) : Function.Surjective (familyProject X hd p) := by
  have h : Function.Surjective (foldOnDomain X p) := by
    rintro (v | ⟨i,q⟩)
    · exact ⟨Sum.inl v,rfl⟩
    · obtain ⟨v,hv⟩ := oldProject_surjective (p i) q
      exact ⟨Sum.inr ⟨i,v⟩,by simp only [foldOnDomain,hv]⟩
  exact h.comp (splitEquiv X hd).symm.surjective

lemma family_quotient_order_add (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) :
    Fintype.card (FamilyQuotient X p) + ∑ i, (X i).card / 2 = Fintype.card V := by
  classical
  have hV := Fintype.card_congr (splitEquiv X hd)
  have hV' : Fintype.card (Outside X) + ∑ i, (X i).card = Fintype.card V := by
    simpa only [FoldDomain,Fintype.card_sum,Fintype.card_sigma,Fintype.card_coe] using hV
  rw [Fintype.card_sum,Fintype.card_sigma,add_assoc,← Finset.sum_add_distrib]
  simp_rw [old_quotient_order,Fintype.card_coe,Nat.sub_add_cancel (Nat.div_le_self _ _)]
  exact hV'

theorem family_quotient_order (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) :
    Fintype.card (FamilyQuotient X p) = Fintype.card V - ∑ i, (X i).card / 2 := by
  have h := family_quotient_order_add X hd p
  omega

lemma familyProject_eq_on_inside (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) (i : I) (v : X i) :
    familyProject X hd p v.val = Sum.inr ⟨i,oldProject (p i) v⟩ := by
  have hv : (splitEquiv X hd) (Sum.inr ⟨i,v⟩) = v.val := rfl
  rw [familyProject,Function.comp_apply,← hv,Equiv.symm_apply_apply]
  rfl

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse50} {I : Type cycleUniverse51} [Fintype V] [Fintype I] (X : I → Finset V)

def familyPaired (p : ∀ i, PairingSpace (X i)) (u v : V) : Prop :=
  ∃ (i : I) (hu : u ∈ X i) (hv : v ∈ X i), paired (p i) ⟨u,hu⟩ ⟨v,hv⟩

lemma familyProject_apply_split (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) (x : FoldDomain X) :
    familyProject X hd p ((splitEquiv X hd) x) = foldOnDomain X p x := by
  simp only [familyProject,Function.comp_apply,Equiv.symm_apply_apply]

lemma familyProject_eq_iff (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) (u v : V) :
    familyProject X hd p u = familyProject X hd p v ↔ u = v ∨ familyPaired X p u v := by
  constructor
  · intro h
    obtain ⟨a,rfl⟩ := (splitEquiv X hd).surjective u
    obtain ⟨b,rfl⟩ := (splitEquiv X hd).surjective v
    rw [familyProject_apply_split,familyProject_apply_split] at h
    rcases a with a | ⟨i,a⟩ <;> rcases b with b | ⟨j,b⟩
    · exact Or.inl (congrArg (splitEquiv X hd) (congrArg Sum.inl (Sum.inl.inj h)))
    · simp only [foldOnDomain,Sum.inl_ne_inr] at h
    · simp only [foldOnDomain,Sum.inr_ne_inl] at h
    · have hh := Sum.inr.inj h
      have hij := congrArg Sigma.fst hh
      change i = j at hij
      subst j
      have hval : oldProject (p i) a = oldProject (p i) b := by
        simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hh
      obtain hab | hab := (oldProject_eq_iff (p i) a b).mp hval
      · subst b
        exact Or.inl rfl
      · exact Or.inr ⟨i,a.property,b.property,hab⟩
  · rintro (rfl | ⟨i,hu,hv,hp⟩)
    · rfl
    · rw [familyProject_eq_on_inside X hd p i ⟨u,hu⟩,
        familyProject_eq_on_inside X hd p i ⟨v,hv⟩]
      congr 2
      exact (oldProject_eq_iff (p i) ⟨u,hu⟩ ⟨v,hv⟩).mpr (Or.inr hp)

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse56} {I : Type cycleUniverse57} [Fintype V] [Fintype I] (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (p : ∀ i, PairingSpace (X i))

lemma loop_iff_familyPaired {u v : V} (huv : u ≠ v) :
    (Sym2.map (familyProject X hd p) s(u,v)).IsDiag ↔ familyPaired X p u v := by
  simp only [Sym2.map_mk,Sym2.mk_isDiag_iff,
    familyProject_eq_iff,huv,false_or]

lemma shared_endpoint_collision {v u w : V} (huw : u ≠ w)
    (h : Sym2.map (familyProject X hd p) s(v,u) =
      Sym2.map (familyProject X hd p) s(v,w)) : familyPaired X p u w := by
  have h := (Sym2.mk_eq_mk_iff (p := (familyProject X hd p v, familyProject X hd p u))
    (q := (familyProject X hd p v, familyProject X hd p w))).mp h
  simp only [Prod.mk.injEq,Prod.swap_prod_mk] at h
  have he : familyProject X hd p u = familyProject X hd p w := by
    rcases h with h | h
    · exact h.2
    · exact h.2.trans h.1
  exact ((familyProject_eq_iff X hd p u w).mp he).resolve_left huw

lemma four_endpoint_collision {u v x y : V}
    (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) (hvy : v ≠ y)
    (h : Sym2.map (familyProject X hd p) s(u,v) =
      Sym2.map (familyProject X hd p) s(x,y)) :
    (familyPaired X p u x ∧ familyPaired X p v y) ∨
    (familyPaired X p u y ∧ familyPaired X p v x) := by
  have h := (Sym2.mk_eq_mk_iff (p := (familyProject X hd p u, familyProject X hd p v))
    (q := (familyProject X hd p x, familyProject X hd p y))).mp h
  simp only [Prod.mk.injEq,Prod.swap_prod_mk] at h
  rcases h with h | h
  · exact Or.inl ⟨((familyProject_eq_iff X hd p u x).mp h.1).resolve_left hux,
      ((familyProject_eq_iff X hd p v y).mp h.2).resolve_left hvy⟩
  · exact Or.inr ⟨((familyProject_eq_iff X hd p u y).mp h.1).resolve_left huy,
      ((familyProject_eq_iff X hd p v x).mp h.2).resolve_left hvx⟩

lemma paired_fibers_placement {V : Type cycleUniverse58} {I : Type cycleUniverse59} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (p : (i : I) → ErdosGallai.Batch.PairingSpace (Subtype fun x => x ∈ X i)) {u v x y : V}
    (hux : familyPaired X p u x) (hvy : familyPaired X p v y) :
    (∃ i, u ∈ X i ∧ v ∈ X i ∧ x ∈ X i ∧ y ∈ X i) ∨
    (∃ i j, i ≠ j ∧ u ∈ X i ∧ x ∈ X i ∧ v ∈ X j ∧ y ∈ X j) := by
  obtain ⟨i,hu,hx,_⟩ := hux
  obtain ⟨j,hv,hy,_⟩ := hvy
  by_cases hij : i = j
  · subst j
    exact Or.inl ⟨i,hu,hv,hx,hy⟩
  · exact Or.inr ⟨i,j,hij,hu,hx,hv,hy⟩

end
end ErdosGallai.Batch

end
/-! ### Upstream module `Combinatorics/CycleDecomposition/CollisionEstimates.lean` -/

noncomputable section
open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Finset
namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse1} [Fintype V] (G : SimpleGraph V)

def neighborsIn (X : Finset V) (v : V) : ℕ :=
  (X.filter (G.Adj v)).card

def internalGraph (X : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ X ∧ v ∈ X
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

lemma neighborsIn_le_degree (X : Finset V) (v : V) :
    neighborsIn G X v ≤ G.degree v := by
  classical
  rw [← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro x hx
  exact (G.mem_neighborFinset v x).mpr (Finset.mem_filter.mp hx).2

lemma neighborsIn_eq_sum {V : Type cycleUniverse2} [_contextInstance1 : Fintype V] (G : SimpleGraph V) (X : Finset V) (v : V) :
    neighborsIn G X v = ∑ x ∈ X, if G.Adj v x then 1 else 0 := by
  classical
  simp only [neighborsIn,Finset.card_eq_sum_ones,Finset.sum_filter]

lemma sum_incidence_to_set (X : Finset V) :
    ∑ v, neighborsIn G X v = ∑ x ∈ X, G.degree x := by
  classical
  simp_rw [neighborsIn_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp_rw [G.adj_comm (v:=x)]
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (G.Adj x) = G.neighborFinset x := by
    ext y
    simp
  simp [he]

lemma internalGraph_degree (X : Finset V) (v : V) :
    (internalGraph G X).degree v = if v ∈ X then neighborsIn G X v else 0 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  by_cases hv : v ∈ X
  · simp only [hv,ite_true]
    congr 1
    ext x
    rw [SimpleGraph.mem_neighborFinset,Finset.mem_filter]
    change (G.Adj v x ∧ v ∈ X ∧ x ∈ X) ↔ _
    tauto
  · have he : (internalGraph G X).neighborFinset v = ∅ := by
      ext x
      simp only [SimpleGraph.mem_neighborFinset,Finset.notMem_empty]
      change (G.Adj v x ∧ v ∈ X ∧ x ∈ X) ↔ False
      tauto
    simp [he,hv]

lemma internalGraph_degree_sum (X : Finset V) :
    2 * (internalGraph G X).edgeFinset.card = ∑ x ∈ X, neighborsIn G X x := by
  classical
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp_rw [internalGraph_degree]
  simp

lemma internal_edge_bound (X : Finset V) (a : ℝ)
    (ha : ∀ x ∈ X, (G.degree x : ℝ) ≤ a) :
    2 * ((internalGraph G X).edgeFinset.card : ℝ) ≤ a * X.card := by
  have hid := congrArg (fun n : ℕ => (n:ℝ)) (internalGraph_degree_sum G X)
  push_cast at hid
  rw [hid]
  calc
    _ ≤ ∑ x ∈ X, a := Finset.sum_le_sum fun x hx =>
      (Nat.cast_le.mpr (neighborsIn_le_degree G X x)).trans (ha x hx)
    _ = _ := by simp [mul_comm]

lemma incidence_bound (X : Finset V) (a : ℝ)
    (ha : ∀ x ∈ X, (G.degree x : ℝ) ≤ a) :
    (∑ v, neighborsIn G X v : ℝ) ≤ a * X.card := by
  have hid := congrArg (fun n : ℕ => (n:ℝ)) (sum_incidence_to_set G X)
  push_cast at hid
  rw [hid]
  simpa [mul_comm] using Finset.sum_le_sum (s:=X) (fun x hx => ha x hx)

lemma wedge_count_bound (X : Finset V) (a : ℝ) (ha : 1 ≤ a)
    (hdegree : ∀ x ∈ X, (G.degree x : ℝ) ≤ a)
    (hneighbor : ∀ v, (neighborsIn G X v : ℝ) ≤ a) :
    ((∑ v, (neighborsIn G X v).choose 2 : ℕ) : ℝ) ≤
      a*(a-1)*X.card/2 := by
  have hb (v : V) : ((neighborsIn G X v).choose 2 : ℝ) ≤
      (a-1)*(neighborsIn G X v)/2 := by
    rw [Nat.cast_choose_two]
    have hn : (0:ℝ) ≤ neighborsIn G X v := Nat.cast_nonneg _
    have hn' := hneighbor v
    nlinarith
  calc
    _ = ∑ v, ((neighborsIn G X v).choose 2 : ℝ) := by push_cast; rfl
    _ ≤ ∑ v, (a-1)*(neighborsIn G X v)/2 := Finset.sum_le_sum fun v _ => hb v
    _ = (a-1)/2 * ∑ v, (neighborsIn G X v : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ ≤ (a-1)/2 * (a*X.card) := mul_le_mul_of_nonneg_left
        (incidence_bound G X a hdegree) (by positivity)
    _ = _ := by ring

def betweenCount (X Y : Finset V) : ℕ := ∑ x ∈ X, neighborsIn G Y x

lemma betweenCount_comm (X Y : Finset V) :
    betweenCount G X Y = betweenCount G Y X := by
  classical
  simp only [betweenCount,neighborsIn_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  simp only [G.adj_comm]

lemma betweenCount_bound (X Y : Finset V) (a : ℝ)
    (hdegree : ∀ y ∈ Y, (G.degree y : ℝ) ≤ a) :
    (betweenCount G X Y : ℝ) ≤ a*Y.card := by
  rw [betweenCount_comm]
  simp only [betweenCount,Nat.cast_sum]
  calc
    _ ≤ ∑ y ∈ Y, a := Finset.sum_le_sum fun y hy =>
      (Nat.cast_le.mpr (neighborsIn_le_degree G X y)).trans (hdegree y hy)
    _ = _ := by simp [mul_comm]

lemma disjoint_neighbor_sum_le {I : Type cycleUniverse3} [Fintype I] (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (v : V) :
    ∑ i, neighborsIn G (X i) v ≤ G.degree v := by
  classical
  have hb : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => (X i).filter (G.Adj v)) := by
    intro i hi j hj hij
    exact (hd hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  simp only [neighborsIn]
  rw [← Finset.card_biUnion hb,← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
  exact (G.mem_neighborFinset v x).mpr (Finset.mem_filter.mp hx).2

lemma betweenCount_row_bound {I : Type cycleUniverse4} [Fintype I] (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (i : I) (a : ℝ)
    (hdegree : ∀ x ∈ X i, (G.degree x : ℝ) ≤ a) :
    (∑ j, betweenCount G (X i) (X j) : ℝ) ≤ a*(X i).card := by
  simp only [betweenCount,Nat.cast_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ x ∈ X i, a := by
      apply Finset.sum_le_sum
      intro x hx
      have hn := disjoint_neighbor_sum_le G X hd x
      have hn' : (∑ j, (neighborsIn G (X j) x : ℝ)) ≤ G.degree x := by
        exact_mod_cast hn
      exact hn'.trans (hdegree x hx)
    _ = _ := by simp [mul_comm]

lemma cross_error_row {I : Type cycleUniverse5} [Fintype I] (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (a : ℝ) (ha : 0 ≤ a)
    (hsize : ∀ i, 0 < (X i).card)
    (hdegree : ∀ i x, x ∈ X i → (G.degree x : ℝ) ≤ a) (i : I) :
    (∑ j, ((betweenCount G (X i) (X j) : ℝ)^2 /
      ((X i).card*(X j).card))) ≤ a^2 := by
  have hmi : (0:ℝ) < (X i).card := by exact_mod_cast hsize i
  calc
    _ ≤ ∑ j, a/(X i).card * (betweenCount G (X i) (X j) : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hmj : (0:ℝ) < (X j).card := by exact_mod_cast hsize j
      have he := betweenCount_bound G (X i) (X j) a (hdegree j)
      have hn : (0:ℝ) ≤ betweenCount G (X i) (X j) := Nat.cast_nonneg _
      apply (div_le_iff₀ (mul_pos hmi hmj)).mpr
      field_simp
      nlinarith
    _ = a/(X i).card * ∑ j, (betweenCount G (X i) (X j) : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ a/(X i).card * (a*(X i).card) := mul_le_mul_of_nonneg_left
      (betweenCount_row_bound G X hd i a (hdegree i)) (by positivity)
    _ = a^2 := by field_simp

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section

def CollisionPairs {α : Type cycleUniverse6} {β : Type cycleUniverse7} [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α) : Finset (Finset α) := by
  classical
  exact (s.powersetCard 2).filter (fun p => (p.image f).card = 1)

lemma mem_collisionPairs {α : Type cycleUniverse8} {β : Type cycleUniverse9} [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α) (p : Finset α) :
    p ∈ CollisionPairs f s ↔ p ⊆ s ∧ p.card = 2 ∧ (p.image f).card = 1 := by
  classical
  simp [CollisionPairs,and_assoc]

lemma collisionPairs_mono {α : Type cycleUniverse10} {β : Type cycleUniverse11} [DecidableEq α] [DecidableEq β] (f : α → β) {s t : Finset α} (h : s ⊆ t) :
    CollisionPairs f s ⊆ CollisionPairs f t := by
  classical
  intro p hp
  rw [mem_collisionPairs] at hp ⊢
  exact ⟨hp.1.trans h,hp.2⟩

lemma pair_mem_collisionPairs {α : Type cycleUniverse12} {β : Type cycleUniverse13} [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b) (heq : f a = f b) :
    {a,b} ∈ CollisionPairs f s := by
  classical
  rw [mem_collisionPairs]
  refine ⟨?_,by simp [hne],by simp [heq]⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact ha
  · exact Finset.mem_singleton.mp hx ▸ hb

theorem prune_collisions {α : Type cycleUniverse14} {β : Type cycleUniverse15} [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α) :
    ∃ t ⊆ s, Set.InjOn f (t : Set α) ∧ t.image f = s.image f ∧
      s.card - t.card ≤ (CollisionPairs f s).card := by
  classical
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases hinj : Set.InjOn f (s : Set α)
  · exact ⟨s,Subset.rfl,hinj,rfl,by simp⟩
  simp only [Set.InjOn,Finset.mem_coe,not_forall] at hinj
  obtain ⟨a,ha,b,hb,heq,hne⟩ := hinj
  have hsub : s.erase a ⊂ s := Finset.erase_ssubset ha
  obtain ⟨t,ht,hinj,himage,hcost⟩ := ih (s.erase a) hsub
  have hpair := pair_mem_collisionPairs f s ha hb hne heq
  have hnot : ({a,b}:Finset α) ∉ CollisionPairs f (s.erase a) := by
    intro hp
    have hh := (mem_collisionPairs f _ _).mp hp
    have := hh.1 (show a ∈ ({a,b}:Finset α) by simp)
    simp at this
  have hlt : (CollisionPairs f (s.erase a)).card < (CollisionPairs f s).card := by
    apply Finset.card_lt_card
    exact Finset.ssubset_iff_subset_ne.mpr ⟨collisionPairs_mono f (Finset.erase_subset _ _),
      fun he => hnot (he ▸ hpair)⟩
  have himage' : (s.erase a).image f = s.image f := by
    apply le_antisymm
    · exact Finset.image_subset_image (Finset.erase_subset _ _)
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      by_cases hxa : x = a
      · subst x
        exact Finset.mem_image.mpr ⟨b,by simp [hb,Ne.symm hne],heq.symm⟩
      · exact Finset.mem_image.mpr ⟨x,by simp [hx,hxa],rfl⟩
  refine ⟨t,ht.trans (Finset.erase_subset _ _),hinj,himage.trans himage',?_⟩
  have hcard := Finset.card_erase_of_mem ha
  have htt := Finset.card_le_card ht
  omega

theorem prune_bad_images {α : Type cycleUniverse16} {β : Type cycleUniverse17} [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α) (bad : β → Prop) [DecidablePred bad] :
    ∃ t ⊆ s, (∀ x ∈ t, ¬ bad (f x)) ∧ Set.InjOn f (t : Set α) ∧
      t.image f = (s.filter (fun x => ¬bad (f x))).image f ∧
      s.card-t.card ≤ (s.filter (fun x => bad (f x))).card +
        (CollisionPairs f (s.filter (fun x => ¬bad (f x)))).card := by
  classical
  obtain ⟨t,ht,hinj,himage,hcost⟩ := prune_collisions f (s.filter (fun x => ¬bad (f x)))
  refine ⟨t,ht.trans (Finset.filter_subset _ _),?_,hinj,himage,?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp (ht hx)).2
  · have hpart := Finset.card_filter_add_card_filter_not (s:=s) (p:=fun x => bad (f x))
    have hle := Finset.card_le_card ht
    omega

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable

def quotientDefect {V : Type cycleUniverse18} {W : Type cycleUniverse19} [Fintype V] (G : SimpleGraph V) (projMap : V → W) : ℕ := by
  classical
  let s := G.edgeFinset
  exact (s.filter (fun e => (Sym2.map projMap e).IsDiag)).card +
    (CollisionPairs (Sym2.map projMap) (s.filter (fun e => ¬(Sym2.map projMap e).IsDiag))).card

theorem simple_quotient_representatives {V : Type cycleUniverse20} {W : Type cycleUniverse21} [Fintype V]
    (G : SimpleGraph V) (projMap : V → W) :
    ∃ (retained : Finset (Sym2 V)) (Q : SimpleGraph W),
      retained ⊆ G.edgeFinset ∧
      (G.edgeFinset \ retained).card ≤ quotientDefect G projMap ∧
      Q.edgeSet = ((retained.image (Sym2.map projMap) : Finset (Sym2 W)) : Set (Sym2 W)) ∧
      (∀ e ∈ Q.edgeSet, ∃! f, f ∈ retained ∧ Sym2.map projMap f = e) := by
  classical
  obtain ⟨t,ht,hgood,hinj,himage,hcost⟩ :=
    prune_bad_images (Sym2.map projMap) G.edgeFinset Sym2.IsDiag
  let Q : SimpleGraph W := SimpleGraph.fromEdgeSet (t.image (Sym2.map projMap) : Set (Sym2 W))
  have hQ : Q.edgeSet = (t.image (Sym2.map projMap) : Set (Sym2 W)) := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    constructor
    · exact fun h => h.1
    · intro he
      refine ⟨he,?_⟩
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
      exact hgood f hf
  refine ⟨t,Q,ht,?_,hQ,?_⟩
  · rw [Finset.card_sdiff_of_subset ht]
    exact hcost
  · intro e he
    rw [hQ] at he
    obtain ⟨f,hf,hfe⟩ := Finset.mem_image.mp he
    refine ⟨f,⟨hf,hfe⟩,?_⟩
    intro g hg
    exact hinj hg.1 hf (hg.2.trans hfe.symm)

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse22} {I : Type cycleUniverse23} [Fintype V] [Fintype I] (X : I → Finset V)
  (hd : Pairwise (fun i j => Disjoint (X i) (X j)))

lemma familyPaired_symm {V : Type cycleUniverse24} {I : Type cycleUniverse25} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (p : ∀ i, PairingSpace (X i)) {u v : V}
    (h : familyPaired X p u v) : familyPaired X p v u := by
  obtain ⟨i,hu,hv,hp⟩ := h
  exact ⟨i,hv,hu,paired_symm (p i) hp⟩

lemma familyPaired_local {V : Type cycleUniverse26} {I : Type cycleUniverse27} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (hd : Pairwise fun i j => Disjoint (X i) (X j)) (p : ∀ i, PairingSpace (X i)) (i : I)
    (u v : X i) : familyPaired X p u v ↔ paired (p i) u v := by
  constructor
  · rintro ⟨j,hu,hv,hp⟩
    have hij : i = j := by
      by_contra hij
      exact Finset.disjoint_left.mp (hd hij) u.property hu
    subst j
    exact hp
  · intro hp
    exact ⟨i,u.property,v.property,hp⟩

lemma familyPaired_same_set {V : Type cycleUniverse28} {I : Type cycleUniverse29} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (hd : Pairwise fun i j => Disjoint (X i) (X j)) (p : ∀ i, PairingSpace (X i)) (i : I)
    {u v : V} (hu : u ∈ X i) (hp : familyPaired X p u v) : v ∈ X i := by
  obtain ⟨j,hu',hv,hp⟩ := hp
  have hij : i = j := by
    by_contra hij
    exact Finset.disjoint_left.mp (hd hij) hu hu'
  exact hij.symm ▸ hv

def vertexPairEvent (p : ∀ i, PairingSpace (X i)) (s : Finset V) : Prop :=
  ∃ u ∈ s, ∃ v ∈ s, u ≠ v ∧ familyPaired X p u v

lemma vertexPairEvent_pair (p : ∀ i, PairingSpace (X i)) (u v : V) (huv : u ≠ v) :
    vertexPairEvent X p {u,v} ↔ familyPaired X p u v := by
  constructor
  · rintro ⟨a,ha,b,hb,hab,hp⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (hab rfl)
    · exact hp
    · exact familyPaired_symm X p hp
    · exact False.elim (hab rfl)
  · intro hp
    exact ⟨u,by simp,v,by simp,huv,hp⟩

lemma finiteAverage_filter_card {Ω : Type cycleUniverse30} {A : Type cycleUniverse31} [Fintype Ω]
    (s : Finset A) (P : Ω → A → Prop) :
    finiteAverage (fun ω => ((s.filter (P ω)).card : ℝ)) =
      ∑ a ∈ s, finiteAverage (fun ω => if P ω a then 1 else 0) := by
  have hf (ω : Ω) : ((s.filter (P ω)).card : ℝ) =
      ∑ a ∈ s, if P ω a then 1 else 0 := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one,Finset.sum_filter]
  simp_rw [hf]
  exact finiteAverage_sum s _

include hd in
lemma vertexPairEvent_average (i : I) (s : Finset V)
    (hs : s ⊆ X i) (hc : s.card = 2) (hm : 2 ≤ (X i).card) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      if vertexPairEvent X p s then 1 else 0) ≤ 1 / ((X i).card-1:ℝ) := by
  classical
  obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp hc
  have hu := hs (show u ∈ ({u,v}:Finset V) by simp)
  have hv := hs (show v ∈ ({u,v}:Finset V) by simp)
  have he (p : ∀ j, PairingSpace (X j)) :
      vertexPairEvent X p {u,v} ↔ paired (p i) ⟨u,hu⟩ ⟨v,hv⟩ :=
    (vertexPairEvent_pair X p u v huv).trans (familyPaired_local X hd p i ⟨u,hu⟩ ⟨v,hv⟩)
  simp_rw [he]
  rw [finiteAverage_pi_eval (Ω:=fun j => PairingSpace (X j)) i
    (fun p => if paired p ⟨u,hu⟩ ⟨v,hv⟩ then 1 else 0)]
  convert paired_first_bound (V:=(X i)) (by simpa using hm) ⟨u,hu⟩ ⟨v,hv⟩
    (fun h => huv (congrArg Subtype.val h)) using 1 ; simp

def wedgeErrors (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) (i : I) (v : V) :=
  (((X i).filter (G.Adj v)).powersetCard 2).filter (vertexPairEvent X p)

include hd in
lemma wedgeErrors_average (G : SimpleGraph V) (i : I) (v : V)
    (hm : 2 ≤ (X i).card) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) => ((wedgeErrors X G p i v).card : ℝ)) ≤
      ((neighborsIn G (X i) v).choose 2 : ℝ) / ((X i).card-1:ℝ) := by
  classical
  change finiteAverage (fun p => (((((X i).filter (G.Adj v)).powersetCard 2).filter
    (vertexPairEvent X p)).card : ℝ)) ≤ _
  rw [finiteAverage_filter_card]
  calc
    _ ≤ ∑ _s ∈ ((X i).filter (G.Adj v)).powersetCard 2,
        1 / ((X i).card-1:ℝ) := by
      apply Finset.sum_le_sum
      intro s hs
      obtain ⟨hs,hc⟩ := Finset.mem_powersetCard.mp hs
      exact vertexPairEvent_average X hd i s (hs.trans (Finset.filter_subset _ _)) hc hm
    _ = _ := by simp [Finset.card_powersetCard,neighborsIn,div_eq_mul_inv]

lemma mem_internalGraph {G : SimpleGraph V} {S : Finset V} {u v : V} :
    s(u,v) ∈ (internalGraph G S).edgeFinset ↔ G.Adj u v ∧ u ∈ S ∧ v ∈ S := by
  simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
  rfl

def crossGraph (G : SimpleGraph V) (S T : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ((u ∈ S ∧ v ∈ T) ∨ (u ∈ T ∧ v ∈ S))
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.elim (fun h => Or.inr ⟨h.2,h.1⟩)
    (fun h => Or.inl ⟨h.2,h.1⟩)⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

lemma distinct_edge_cases (G : SimpleGraph V) {e f : Sym2 V}
    (he : e ∈ G.edgeFinset) (hf : f ∈ G.edgeFinset) (hef : e ≠ f) :
    (∃ v u w, v ≠ u ∧ v ≠ w ∧ u ≠ w ∧ e = s(v,u) ∧ f = s(v,w)) ∨
    (∃ u v x y, u ≠ v ∧ x ≠ y ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧
      e = s(u,v) ∧ f = s(x,y)) := by
  obtain ⟨a,b⟩ := e
  obtain ⟨c,d⟩ := f
  have hab : a ≠ b := (SimpleGraph.mem_edgeFinset.mp he).ne
  have hcd : c ≠ d := (SimpleGraph.mem_edgeFinset.mp hf).ne
  by_cases hac : a = c
  · subst c
    refine Or.inl ⟨a,b,d,hab,hcd,?_,rfl,rfl⟩
    intro hbd
    exact hef (hbd ▸ rfl)
  by_cases had : a = d
  · subst d
    refine Or.inl ⟨a,b,c,hab,hcd.symm,?_,rfl,Sym2.eq_swap⟩
    intro hbc
    subst c
    exact hef Sym2.eq_swap
  by_cases hbc : b = c
  · subst c
    refine Or.inl ⟨b,a,d,hab.symm,hcd,?_,Sym2.eq_swap,rfl⟩
    intro had
    subst d
    exact hef Sym2.eq_swap
  by_cases hbd : b = d
  · subst d
    refine Or.inl ⟨b,a,c,hab.symm,hcd.symm,?_,Sym2.eq_swap,Sym2.eq_swap⟩
    intro hac
    subst c
    exact hef rfl
  exact Or.inr ⟨a,b,c,d,hab,hcd,hac,had,hbc,hbd,rfl,rfl⟩

lemma internal_collision_average (i : I) (hm : 4 ≤ (X i).card)
    (u v x y : X i) (huv : u ≠ v) (hux : u ≠ x) (huy : u ≠ y)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      if Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V)) then 1 else 0) ≤
      2 / (((X i).card-1:ℝ)*((X i).card-3:ℝ)) := by
  classical
  have hmono : finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      if Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V)) then 1 else 0) ≤
      finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      if (paired (p i) u x ∧ paired (p i) v y) ∨
        (paired (p i) u y ∧ paired (p i) v x) then 1 else 0) := by
    apply finiteAverage_mono
    intro p
    by_cases hc : Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V))
    · have hh := four_endpoint_collision X hd p (fun h => hux (Subtype.ext h))
        (fun h => huy (Subtype.ext h)) (fun h => hvx (Subtype.ext h))
        (fun h => hvy (Subtype.ext h)) hc
      have he : (paired (p i) u x ∧ paired (p i) v y) ∨
          (paired (p i) u y ∧ paired (p i) v x) := by
        simpa only [familyPaired_local X hd p i] using hh
      simp only [ite_eq_left hc,ite_eq_left he,le_refl]
    · rw [ite_eq_right hc]
      split_ifs <;> norm_num
  apply hmono.trans
  rw [finiteAverage_pi_eval (Ω:=fun j => PairingSpace (X j)) i
    (fun p => if (paired p u x ∧ paired p v y) ∨ (paired p u y ∧ paired p v x)
      then 1 else 0)]
  simpa only [Fintype.card_coe] using pairing_patterns_internal
    (V:=(X i)) (by simpa using hm) u v x y huv hux huy hvx hvy hxy

lemma cross_collision_average (i j : I) (hij : i ≠ j)
    (hi : 2 ≤ (X i).card) (hj : 2 ≤ (X j).card)
    (u x : X i) (v y : X j) (hux : u ≠ x) (hvy : v ≠ y) :
    finiteAverage (fun p : ∀ k, PairingSpace (X k) =>
      if Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V)) then 1 else 0) ≤
      1 / (((X i).card-1:ℝ)*((X j).card-1:ℝ)) := by
  classical
  have huy : (u:V) ≠ y := by
    intro h
    exact Finset.disjoint_left.mp (hd hij) u.property (h ▸ y.property)
  have hvx : (v:V) ≠ x := by
    intro h
    exact Finset.disjoint_left.mp (hd hij) (h ▸ x.property) v.property
  have hmono : finiteAverage (fun p : ∀ k, PairingSpace (X k) =>
      if Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V)) then 1 else 0) ≤
      finiteAverage (fun p : ∀ k, PairingSpace (X k) =>
      if paired (p i) u x ∧ paired (p j) v y then 1 else 0) := by
    apply finiteAverage_mono
    intro p
    by_cases hc : Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V))
    · have hh := four_endpoint_collision X hd p (fun h => hux (Subtype.ext h))
        huy hvx (fun h => hvy (Subtype.ext h)) hc
      have he : paired (p i) u x ∧ paired (p j) v y := by
        rcases hh with hh | hh
        · exact ⟨(familyPaired_local X hd p i u x).mp hh.1,
            (familyPaired_local X hd p j v y).mp hh.2⟩
        · have hy := familyPaired_same_set X hd p i u.property hh.1
          exact False.elim (Finset.disjoint_left.mp (hd hij) hy y.property)
      simp only [ite_eq_left hc,ite_eq_left he,le_refl]
    · rw [ite_eq_right hc]
      split_ifs <;> norm_num
  apply hmono.trans
  simpa only [Fintype.card_coe] using pairing_patterns_cross_bound
    (V:=fun k => X k) i j hij (by simpa using hi) (by simpa using hj) u x hux v y hvy

end
end ErdosGallai.Batch
end
/-! ### Upstream module `Combinatorics/CycleDecomposition/BatchPreparation.lean` -/

noncomputable section
namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse1} {I : Type cycleUniverse2} [Fintype V] [Fintype I] (X : I → Finset V)
  (hd : Pairwise (fun i j => Disjoint (X i) (X j)))

lemma crossGraph_card (G : SimpleGraph V) (S T : Finset V) (hst : Disjoint S T) :
    (crossGraph G S T).edgeFinset.card = betweenCount G S T := by
  classical
  have hdeg (v : V) : (crossGraph G S T).degree v =
      (if v ∈ S then neighborsIn G T v else 0) +
      (if v ∈ T then neighborsIn G S v else 0) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hfin : (crossGraph G S T).neighborFinset v =
      (if v ∈ S then T.filter (G.Adj v) else ∅) ∪
      (if v ∈ T then S.filter (G.Adj v) else ∅) := by
      ext x
      simp only [SimpleGraph.mem_neighborFinset,Finset.mem_union]
      change (G.Adj v x ∧ ((v ∈ S ∧ x ∈ T) ∨ (v ∈ T ∧ x ∈ S))) ↔ _
      split_ifs <;> simp_all only [Finset.mem_filter,Finset.notMem_empty] <;> tauto
    rw [hfin,Finset.card_union_of_disjoint]
    · split_ifs <;> simp [neighborsIn]
    · split_ifs with hs ht ht
      · exact False.elim (Finset.disjoint_left.mp hst hs ht)
      all_goals simp
  have hh := (crossGraph G S T).sum_degrees_eq_twice_card_edges
  simp_rw [hdeg] at hh
  rw [Finset.sum_add_distrib] at hh
  have hS : (∑ v, if v ∈ S then neighborsIn G T v else 0) = betweenCount G S T := by
    simp [betweenCount]
  have hT : (∑ v, if v ∈ T then neighborsIn G S v else 0) = betweenCount G T S := by
    simp [betweenCount]
  rw [hS,hT,betweenCount_comm G T S] at hh
  omega

def edgePairEvent (p : ∀ i, PairingSpace (X i)) (q : Finset (Sym2 V)) : Prop :=
  (q.image (Sym2.map (familyProject X hd p))).card = 1

lemma edgePairEvent_pair (p : ∀ i, PairingSpace (X i)) (e f : Sym2 V) :
    edgePairEvent X hd p {e,f} ↔
      Sym2.map (familyProject X hd p) e = Sym2.map (familyProject X hd p) f := by
  classical
  by_cases h : Sym2.map (familyProject X hd p) e = Sym2.map (familyProject X hd p) f
  · simp [edgePairEvent,h]
  · simp [edgePairEvent,h,Finset.card_pair h]

def DisjointEdgePair (q : Finset (Sym2 V)) : Prop :=
  ∃ u v x y : V, u ≠ v ∧ x ≠ y ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧
    q = {s(u,v),s(x,y)}

def pairErrors (H : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) :=
  ((H.edgeFinset.powersetCard 2).filter DisjointEdgePair).filter (edgePairEvent X hd p)

def loopErrors (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) (i : I) :=
  (internalGraph G (X i)).edgeFinset.filter
    (fun e => (Sym2.map (familyProject X hd p) e).IsDiag)

lemma loopErrors_average (G : SimpleGraph V) (i : I) (hm : 2 ≤ (X i).card) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) => ((loopErrors X hd G p i).card : ℝ)) ≤
      ((internalGraph G (X i)).edgeFinset.card : ℝ) / ((X i).card-1:ℝ) := by
  classical
  change finiteAverage (fun p => (((internalGraph G (X i)).edgeFinset.filter _).card:ℝ)) ≤ _
  have hav := finiteAverage_filter_card (s:=(internalGraph G (X i)).edgeFinset)
    (P:=fun (p : ∀ j, PairingSpace (X j)) e => (Sym2.map (familyProject X hd p) e).IsDiag)
  calc
    _ = ∑ e ∈ (internalGraph G (X i)).edgeFinset,
        finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
          if (Sym2.map (familyProject X hd p) e).IsDiag then 1 else 0) := by
      convert hav using 1 <;> congr 4
      · funext p
        congr 2
        ext e
        simp only [Finset.mem_filter]
      · funext e
        congr 1
        funext p
        split_ifs <;> rfl
    _ ≤ _ := by
      calc
        _ ≤ ∑ _e ∈ (internalGraph G (X i)).edgeFinset, 1 / ((X i).card-1:ℝ) := by
          apply Finset.sum_le_sum
          intro e he
          obtain ⟨u,v⟩ := e
          obtain ⟨huv,hu,hv⟩ := mem_internalGraph.mp he
          have heq (p : ∀ j, PairingSpace (X j)) :
              (Sym2.map (familyProject X hd p) s(u,v)).IsDiag ↔ vertexPairEvent X p {u,v} :=
            (loop_iff_familyPaired X hd p huv.ne).trans (vertexPairEvent_pair X p u v huv.ne).symm
          simp_rw [heq]
          exact vertexPairEvent_average X hd i {u,v} (by intro z hz; rcases Finset.mem_insert.mp hz with rfl | hz; exact hu; exact Finset.mem_singleton.mp hz ▸ hv)
            (by simp [huv.ne]) hm
        _ = _ := by simp [div_eq_mul_inv]

lemma internal_pairErrors_average (G : SimpleGraph V) (i : I) (hm : 4 ≤ (X i).card) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      ((pairErrors X hd (internalGraph G (X i)) p).card : ℝ)) ≤
      ((internalGraph G (X i)).edgeFinset.card.choose 2 : ℝ) *
        (2 / (((X i).card-1:ℝ)*((X i).card-3:ℝ))) := by
  classical
  change finiteAverage (fun p => (((((internalGraph G (X i)).edgeFinset.powersetCard 2).filter DisjointEdgePair).filter _).card:ℝ)) ≤ _
  rw [finiteAverage_filter_card]
  calc
    _ ≤ ∑ _q ∈ ((internalGraph G (X i)).edgeFinset.powersetCard 2).filter DisjointEdgePair,
        2 / (((X i).card-1:ℝ)*((X i).card-3:ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hq,hdis⟩ := Finset.mem_filter.mp hq
      obtain ⟨u,v,x,y,huv,hxy,hux,huy,hvx,hvy,rfl⟩ := hdis
      have hsub := (Finset.mem_powersetCard.mp hq).1
      obtain ⟨he,hu,hv⟩ := mem_internalGraph.mp (hsub (by simp : s(u,v) ∈ ({s(u,v),s(x,y)}:Finset (Sym2 V))))
      obtain ⟨hf,hx,hy⟩ := mem_internalGraph.mp (hsub (by simp : s(x,y) ∈ ({s(u,v),s(x,y)}:Finset (Sym2 V))))
      simp_rw [edgePairEvent_pair]
      exact internal_collision_average X hd i hm ⟨u,hu⟩ ⟨v,hv⟩ ⟨x,hx⟩ ⟨y,hy⟩
        (fun h => huv (congrArg Subtype.val h)) (fun h => hux (congrArg Subtype.val h))
        (fun h => huy (congrArg Subtype.val h)) (fun h => hvx (congrArg Subtype.val h))
        (fun h => hvy (congrArg Subtype.val h)) (fun h => hxy (congrArg Subtype.val h))
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_powersetCard _ _)
      · have : (4:ℝ) ≤ (X i).card := by exact_mod_cast hm
        exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))

lemma cross_pair_orientation {V : Type cycleUniverse3} {I : Type cycleUniverse4} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (G : SimpleGraph V) (i j : I)
    (q : Finset (Sym2 V)) (hq : q ⊆ (crossGraph G (X i) (X j)).edgeFinset)
    (hdis : DisjointEdgePair q) :
    ∃ (u x : X i) (v y : X j), u ≠ x ∧ v ≠ y ∧ q = {s((u:V),(v:V)),s((x:V),(y:V))} := by
  classical
  obtain ⟨u,v,x,y,huv,hxy,hux,huy,hvx,hvy,rfl⟩ := hdis
  have he := SimpleGraph.mem_edgeFinset.mp (hq (by simp : s(u,v) ∈ ({s(u,v),s(x,y)}:Finset (Sym2 V))))
  have hf := SimpleGraph.mem_edgeFinset.mp (hq (by simp : s(x,y) ∈ ({s(u,v),s(x,y)}:Finset (Sym2 V))))
  rcases he.2 with ⟨hui,hvj⟩ | ⟨huj,hvi⟩ <;> rcases hf.2 with ⟨hxi,hyj⟩ | ⟨hxj,hyi⟩
  · exact ⟨⟨u,hui⟩,⟨x,hxi⟩,⟨v,hvj⟩,⟨y,hyj⟩,
      (fun h => hux (congrArg Subtype.val h)),(fun h => hvy (congrArg Subtype.val h)),rfl⟩
  · refine ⟨⟨u,hui⟩,⟨y,hyi⟩,⟨v,hvj⟩,⟨x,hxj⟩,
      (fun h => huy (congrArg Subtype.val h)),(fun h => hvx (congrArg Subtype.val h)),?_⟩
    rw [Sym2.eq_swap (a:=y) (b:=x)]
  · refine ⟨⟨v,hvi⟩,⟨x,hxi⟩,⟨u,huj⟩,⟨y,hyj⟩,
      (fun h => hvx (congrArg Subtype.val h)),(fun h => huy (congrArg Subtype.val h)),?_⟩
    rw [Sym2.eq_swap (a:=v) (b:=u)]
  · refine ⟨⟨v,hvi⟩,⟨y,hyi⟩,⟨u,huj⟩,⟨x,hxj⟩,
      (fun h => hvy (congrArg Subtype.val h)),(fun h => hux (congrArg Subtype.val h)),?_⟩
    rw [Sym2.eq_swap (a:=v) (b:=u),Sym2.eq_swap (a:=y) (b:=x)]

lemma cross_pairErrors_average (G : SimpleGraph V) (i j : I) (hij : i ≠ j)
    (hi : 2 ≤ (X i).card) (hj : 2 ≤ (X j).card) :
    finiteAverage (fun p : ∀ k, PairingSpace (X k) =>
      ((pairErrors X hd (crossGraph G (X i) (X j)) p).card : ℝ)) ≤
      ((betweenCount G (X i) (X j)).choose 2 : ℝ) *
        (1 / (((X i).card-1:ℝ)*((X j).card-1:ℝ))) := by
  classical
  change finiteAverage (fun p => (((((crossGraph G (X i) (X j)).edgeFinset.powersetCard 2).filter DisjointEdgePair).filter _).card:ℝ)) ≤ _
  rw [finiteAverage_filter_card]
  calc
    _ ≤ ∑ _q ∈ ((crossGraph G (X i) (X j)).edgeFinset.powersetCard 2).filter DisjointEdgePair,
        1 / (((X i).card-1:ℝ)*((X j).card-1:ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hq,hdis⟩ := Finset.mem_filter.mp hq
      obtain ⟨u,x,v,y,hux,hvy,rfl⟩ := cross_pair_orientation X G i j q
        (Finset.mem_powersetCard.mp hq).1 hdis
      simp_rw [edgePairEvent_pair]
      exact cross_collision_average X hd i j hij hi hj u x v y hux hvy
    _ ≤ _ := by
      rw [← crossGraph_card G (X i) (X j) (hd hij)]
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_powersetCard _ _)
      · have : (2:ℝ) ≤ (X i).card := by exact_mod_cast hi
        have : (2:ℝ) ≤ (X j).card := by exact_mod_cast hj
        exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse5} {I : Type cycleUniverse6} [Fintype V] [Fintype I] (X : I → Finset V)
  (hd : Pairwise (fun i j => Disjoint (X i) (X j)))

lemma mem_pairErrors (H : SimpleGraph V) (p : ∀ i, PairingSpace (X i))
    (q : Finset (Sym2 V)) :
    q ∈ pairErrors X hd H p ↔ q ⊆ H.edgeFinset ∧ q.card = 2 ∧
      DisjointEdgePair q ∧ edgePairEvent X hd p q := by
  classical
  simp [pairErrors,and_assoc]

lemma mem_crossGraph {G : SimpleGraph V} {S T : Finset V} {u v : V} :
    s(u,v) ∈ (crossGraph G S T).edgeFinset ↔
      G.Adj u v ∧ ((u ∈ S ∧ v ∈ T) ∨ (u ∈ T ∧ v ∈ S)) := by
  rw [SimpleGraph.mem_edgeFinset]
  rfl

lemma two_paired_edges_placement (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i))
    {u v x y : V} (he : G.Adj u v) (hf : G.Adj x y)
    (hux : familyPaired X p u x) (hvy : familyPaired X p v y) :
    (∃ i, {s(u,v),s(x,y)} ⊆ (internalGraph G (X i)).edgeFinset) ∨
    (∃ i j, i ≠ j ∧ {s(u,v),s(x,y)} ⊆ (crossGraph G (X i) (X j)).edgeFinset) := by
  classical
  rcases paired_fibers_placement X p hux hvy with ⟨i,hu,hv,hx,hy⟩ | ⟨i,j,hij,hu,hx,hv,hy⟩
  · left
    refine ⟨i,?_⟩
    intro e he'
    rcases Finset.mem_insert.mp he' with rfl | he'
    · exact mem_internalGraph.mpr ⟨he,hu,hv⟩
    · exact Finset.mem_singleton.mp he' ▸ mem_internalGraph.mpr ⟨hf,hx,hy⟩
  · right
    refine ⟨i,j,hij,?_⟩
    intro e he'
    rcases Finset.mem_insert.mp he' with rfl | he'
    · exact mem_crossGraph.mpr ⟨he,Or.inl ⟨hu,hv⟩⟩
    · exact Finset.mem_singleton.mp he' ▸ mem_crossGraph.mpr ⟨hf,Or.inl ⟨hx,hy⟩⟩

def wedgeCover (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) : Finset (Finset (Sym2 V)) :=
  Finset.univ.biUnion fun i => Finset.univ.biUnion fun v =>
    (wedgeErrors X G p i v).image (fun q => q.image (fun u => s(v,u)))

def internalCover (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) : Finset (Finset (Sym2 V)) :=
  Finset.univ.biUnion fun i => pairErrors X hd (internalGraph G (X i)) p

def crossCover (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) : Finset (Finset (Sym2 V)) :=
  Finset.univ.biUnion fun i => (Finset.univ.erase i).biUnion fun j =>
    pairErrors X hd (crossGraph G (X i) (X j)) p

lemma all_collisions_covered (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) :
    CollisionPairs (Sym2.map (familyProject X hd p)) G.edgeFinset ⊆
      wedgeCover X G p ∪ internalCover X hd G p ∪ crossCover X hd G p := by
  classical
  intro q hq
  obtain ⟨hsub,hcard,himage⟩ := (mem_collisionPairs _ _ _).mp hq
  obtain ⟨e,f,hef,rfl⟩ := Finset.card_eq_two.mp hcard
  have he := hsub (by simp : e ∈ ({e,f}:Finset (Sym2 V)))
  have hf := hsub (by simp : f ∈ ({e,f}:Finset (Sym2 V)))
  have hev : edgePairEvent X hd p {e,f} := himage
  have heq := (edgePairEvent_pair X hd p e f).mp hev
  rcases distinct_edge_cases G he hf hef with hshared | hdis
  · obtain ⟨v,u,w,hvu,hvw,huw,rfl,rfl⟩ := hshared
    have hpair := shared_endpoint_collision X hd p huw heq
    obtain ⟨i,hu,hw,hpair'⟩ := hpair
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _,?_⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨{u,w},?_,by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_,by simp [huw]⟩,?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Finset.mem_filter.mpr ⟨hu,SimpleGraph.mem_edgeFinset.mp he⟩
      · exact Finset.mem_singleton.mp hz ▸ Finset.mem_filter.mpr ⟨hw,SimpleGraph.mem_edgeFinset.mp hf⟩
    · exact (vertexPairEvent_pair X p u w huw).mpr ⟨i,hu,hw,hpair'⟩
  · obtain ⟨u,v,x,y,huv,hxy,hux,huy,hvx,hvy,rfl,rfl⟩ := hdis
    have hdis : DisjointEdgePair ({s(u,v),s(x,y)}:Finset (Sym2 V)) :=
      ⟨u,v,x,y,huv,hxy,hux,huy,hvx,hvy,rfl⟩
    have hplace : (∃ i, {s(u,v),s(x,y)} ⊆ (internalGraph G (X i)).edgeFinset) ∨
        (∃ i j, i ≠ j ∧ {s(u,v),s(x,y)} ⊆ (crossGraph G (X i) (X j)).edgeFinset) := by
      rcases four_endpoint_collision X hd p hux huy hvx hvy heq with hh | hh
      · exact two_paired_edges_placement X G p (SimpleGraph.mem_edgeFinset.mp he)
          (SimpleGraph.mem_edgeFinset.mp hf) hh.1 hh.2
      · have hh' := two_paired_edges_placement X G p (SimpleGraph.mem_edgeFinset.mp he)
          (SimpleGraph.mem_edgeFinset.mp hf).symm hh.1 hh.2
        simpa only [Sym2.eq_swap (a:=y) (b:=x)] using hh'
    rcases hplace with ⟨i,hi⟩ | ⟨i,j,hij,hij'⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
        (mem_pairErrors X hd _ p _).mpr ⟨hi,by simp [hef],hdis,hev⟩⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨j,by simp [hij.symm],?_⟩⟩
      exact (mem_pairErrors X hd _ p _).mpr ⟨hij',by simp [hef],hdis,hev⟩

lemma all_loops_covered (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) :
    G.edgeFinset.filter (fun e => (Sym2.map (familyProject X hd p) e).IsDiag) ⊆
      Finset.univ.biUnion (fun i => loopErrors X hd G p i) := by
  classical
  intro e he
  obtain ⟨he,hloop⟩ := Finset.mem_filter.mp he
  obtain ⟨u,v⟩ := e
  have huv := SimpleGraph.mem_edgeFinset.mp he
  obtain ⟨i,hu,hv,hp⟩ := (loop_iff_familyPaired X hd p huv.ne).mp hloop
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
    Finset.mem_filter.mpr ⟨mem_internalGraph.mpr ⟨huv,hu,hv⟩,hloop⟩⟩

def foldErrorBudget (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) : ℕ :=
  ∑ i, ((loopErrors X hd G p i).card +
    (∑ v, (wedgeErrors X G p i v).card) +
    (pairErrors X hd (internalGraph G (X i)) p).card +
    ∑ j ∈ Finset.univ.erase i, (pairErrors X hd (crossGraph G (X i) (X j)) p).card)

lemma quotientDefect_le_budget (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) :
    quotientDefect G (familyProject X hd p) ≤ foldErrorBudget X hd G p := by
  classical
  have hl := (Finset.card_le_card (all_loops_covered X hd G p)).trans
    (Finset.card_biUnion_le)
  have hc := (Finset.card_le_card (all_collisions_covered X hd G p)).trans
    (Finset.card_union_le _ _)
  have hw : (wedgeCover X G p).card ≤ ∑ i, ∑ v, (wedgeErrors X G p i v).card := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum fun v hv => Finset.card_image_le
  have hi : (internalCover X hd G p).card ≤
      ∑ i, (pairErrors X hd (internalGraph G (X i)) p).card := Finset.card_biUnion_le
  have hx : (crossCover X hd G p).card ≤ ∑ i, ∑ j ∈ Finset.univ.erase i,
      (pairErrors X hd (crossGraph G (X i) (X j)) p).card := by
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum fun i hi => Finset.card_biUnion_le
  have hc' := Finset.card_le_card (collisionPairs_mono (Sym2.map (familyProject X hd p))
    (Finset.filter_subset (fun e => ¬(Sym2.map (familyProject X hd p) e).IsDiag) G.edgeFinset))
  have hunion := Finset.card_union_le (wedgeCover X G p) (internalCover X hd G p)
  unfold quotientDefect foldErrorBudget
  simp only [Finset.sum_add_distrib]
  omega

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse7} {I : Type cycleUniverse8} [Fintype V] [Fintype I] (X : I → Finset V)
  (hd : Pairwise (fun i j => Disjoint (X i) (X j)))

lemma fold_ratio_one (m : ℝ) (hm : 8 ≤ m) : m/(m-1) ≤ 8/7 := by
  apply (div_le_iff₀ (show 0 < m-1 by linarith)).mpr
  linarith
lemma fold_ratio_three (m : ℝ) (hm : 8 ≤ m) : m/(m-3) ≤ 8/5 := by
  apply (div_le_iff₀ (show 0 < m-3 by linarith)).mpr
  linarith
lemma choose_two_real_bound (n : ℕ) : (n.choose 2 : ℝ) ≤ (n:ℝ)^2/2 := by
  rw [Nat.cast_choose_two]
  have := Nat.cast_nonneg (α:=ℝ) n
  nlinarith

lemma first_error_numeric (m a e : ℝ) (hm : 8 ≤ m) (he : 2*e ≤ a*m) :
    e/(m-1) + (a*(a-1)*m/2)/(m-1) ≤ (4/7)*a^2 := by
  have hp : 0 < m-1 := by linarith
  calc
    _ = (e+a*(a-1)*m/2)/(m-1) := by ring
    _ ≤ (a^2*m/2)/(m-1) := (div_le_div_iff_of_pos_right hp).mpr (by nlinarith)
    _ = (a^2/2)*(m/(m-1)) := by ring
    _ ≤ (a^2/2)*(8/7) := mul_le_mul_of_nonneg_left (fold_ratio_one m hm) (by positivity)
    _ = _ := by ring

lemma internal_error_numeric (m a : ℝ) (e : ℕ) (hm : 8 ≤ m) (ha : 0 ≤ a)
    (he : 2*(e:ℝ) ≤ a*m) :
    (e.choose 2 : ℝ)*(2/((m-1)*(m-3))) ≤ (16/35)*a^2 := by
  have hp : 0 < m-1 := by linarith
  have hp' : 0 < m-3 := by linarith
  have he2 : (e:ℝ)^2 ≤ (a*m/2)^2 := by
    apply sq_le_sq₀ (Nat.cast_nonneg _) (by positivity) |>.mpr
    linarith
  calc
    _ ≤ ((e:ℝ)^2/2)*(2/((m-1)*(m-3))) := mul_le_mul_of_nonneg_right
      (choose_two_real_bound e) (by positivity)
    _ = (e:ℝ)^2/((m-1)*(m-3)) := by ring
    _ ≤ (a*m/2)^2/((m-1)*(m-3)) := div_le_div_of_nonneg_right he2 (by positivity)
    _ = (a^2/4)*((m/(m-1))*(m/(m-3))) := by field_simp ; ring
    _ ≤ (a^2/4)*((8/7)*(8/5)) := mul_le_mul_of_nonneg_left
      (mul_le_mul (fold_ratio_one m hm) (fold_ratio_three m hm)
        (by positivity) (by norm_num)) (by positivity)
    _ = _ := by ring

lemma cross_error_numeric (m n : ℝ) (e : ℕ) (hm : 8 ≤ m) (hn : 8 ≤ n) :
    (e.choose 2 : ℝ)*(1/((m-1)*(n-1))) ≤ (32/49)*((e:ℝ)^2/(m*n)) := by
  have hp : 0 < m-1 := by linarith
  have hq : 0 < n-1 := by linarith
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < n := by linarith
  calc
    _ ≤ ((e:ℝ)^2/2)*(1/((m-1)*(n-1))) := mul_le_mul_of_nonneg_right
      (choose_two_real_bound e) (by positivity)
    _ = ((e:ℝ)^2/(2*m*n))*((m/(m-1))*(n/(n-1))) := by field_simp
    _ ≤ ((e:ℝ)^2/(2*m*n))*((8/7)*(8/7)) := mul_le_mul_of_nonneg_left
      (mul_le_mul (fold_ratio_one m hm) (fold_ratio_one n hn)
        (by positivity) (by norm_num)) (by positivity)
    _ = _ := by ring

lemma first_errors_average (G : SimpleGraph V) (i : I) (a : ℝ) (ha : 1 ≤ a)
    (hm : 8 ≤ (X i).card)
    (hdegree : ∀ x ∈ X i, (G.degree x : ℝ) ≤ a)
    (hneighbor : ∀ v, (neighborsIn G (X i) v : ℝ) ≤ a) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      ((loopErrors X hd G p i).card : ℝ) + ∑ v, ((wedgeErrors X G p i v).card:ℝ)) ≤
      (4/7)*a^2 := by
  classical
  rw [finiteAverage_add,finiteAverage_sum]
  have hp : 0 < ((X i).card:ℝ)-1 := by
    have : (8:ℝ) ≤ (X i).card := by exact_mod_cast hm
    linarith
  calc
    _ ≤ ((internalGraph G (X i)).edgeFinset.card:ℝ)/((X i).card-1:ℝ) +
        ∑ v, ((neighborsIn G (X i) v).choose 2 : ℝ)/((X i).card-1:ℝ) :=
      add_le_add (loopErrors_average X hd G i (by omega))
        (Finset.sum_le_sum fun v _ => wedgeErrors_average X hd G i v (by omega))
    _ = ((internalGraph G (X i)).edgeFinset.card:ℝ)/((X i).card-1:ℝ) +
        (∑ v, ((neighborsIn G (X i) v).choose 2 : ℝ))/((X i).card-1:ℝ) := by rw [Finset.sum_div]
    _ ≤ ((internalGraph G (X i)).edgeFinset.card:ℝ)/((X i).card-1:ℝ) +
        (a*(a-1)*(X i).card/2)/((X i).card-1:ℝ) := by
      apply add_le_add_right
      exact div_le_div_of_nonneg_right (by exact_mod_cast wedge_count_bound G (X i) a ha hdegree hneighbor) hp.le
    _ ≤ _ := first_error_numeric _ _ _ (by exact_mod_cast hm) (internal_edge_bound G (X i) a hdegree)

lemma internal_errors_average (G : SimpleGraph V) (i : I) (a : ℝ) (ha : 0 ≤ a)
    (hm : 8 ≤ (X i).card) (hdegree : ∀ x ∈ X i, (G.degree x : ℝ) ≤ a) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      ((pairErrors X hd (internalGraph G (X i)) p).card : ℝ)) ≤ (16/35)*a^2 :=
  (internal_pairErrors_average X hd G i (by omega)).trans
    (internal_error_numeric _ _ _ (by exact_mod_cast hm) ha (internal_edge_bound G (X i) a hdegree))

lemma cross_errors_average (G : SimpleGraph V) (i : I) (a : ℝ) (ha : 0 ≤ a)
    (hm : ∀ i, 8 ≤ (X i).card)
    (hdegree : ∀ i x, x ∈ X i → (G.degree x : ℝ) ≤ a) :
    finiteAverage (fun p : ∀ k, PairingSpace (X k) =>
      ∑ j ∈ Finset.univ.erase i, ((pairErrors X hd (crossGraph G (X i) (X j)) p).card : ℝ)) ≤
      (32/49)*a^2 := by
  classical
  rw [finiteAverage_sum]
  calc
    _ ≤ ∑ j ∈ Finset.univ.erase i, (32/49)*((betweenCount G (X i) (X j):ℝ)^2 /
        ((X i).card*(X j).card)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hij := (Finset.mem_erase.mp hj).1.symm
      exact (cross_pairErrors_average X hd G i j hij (by have := hm i; omega) (by have := hm j; omega)).trans
        (cross_error_numeric _ _ _ (by exact_mod_cast hm i) (by exact_mod_cast hm j))
    _ ≤ ∑ j, (32/49)*((betweenCount G (X i) (X j):ℝ)^2 /
        ((X i).card*(X j).card)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro j hj hj'
      positivity
    _ = (32/49)*∑ j, ((betweenCount G (X i) (X j):ℝ)^2 /
        ((X i).card*(X j).card)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (cross_error_row G X hd a ha (by intro i; have := hm i; omega) hdegree i) (by norm_num)

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse9} {I : Type cycleUniverse10} [Fintype V] [Fintype I]

theorem folding_average_bound (G : SimpleGraph V) (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (a : ℝ) (ha : 1 ≤ a)
    (hm : ∀ i, 8 ≤ (X i).card) (hma : ∀ i, a^2 ≤ (X i).card)
    (hdegree : ∀ i x, x ∈ X i → (G.degree x : ℝ) ≤ a)
    (hneighbor : ∀ i v, (neighborsIn G (X i) v : ℝ) ≤ a) :
    finiteAverage (fun p : ∀ i, PairingSpace (X i) =>
      (foldErrorBudget X hd G p : ℝ)) ≤ 2 * ∑ i, ((X i).card : ℝ) := by
  classical
  simp only [foldErrorBudget,Nat.cast_sum,Nat.cast_add]
  rw [finiteAverage_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [finiteAverage_add,finiteAverage_add]
  have hfirst := first_errors_average X hd G i a ha (hm i) (hdegree i) (hneighbor i)
  have hint := internal_errors_average X hd G i a (by linarith) (hm i) (hdegree i)
  have hcross := cross_errors_average X hd G i a (by linarith) hm hdegree
  calc
    _ ≤ (4/7)*a^2 + (16/35)*a^2 + (32/49)*a^2 :=
      add_le_add (add_le_add hfirst hint) hcross
    _ ≤ 2 * ((X i).card : ℝ) := by nlinarith [hma i,sq_nonneg a]

theorem pair_folding (G : SimpleGraph V) (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (a : ℝ) (ha : 1 ≤ a)
    (hm : ∀ i, 8 ≤ (X i).card) (hma : ∀ i, a^2 ≤ (X i).card)
    (hdegree : ∀ i x, x ∈ X i → (G.degree x : ℝ) ≤ a)
    (hneighbor : ∀ i v, (neighborsIn G (X i) v : ℝ) ≤ a) :
    ∃ (p : ∀ i, PairingSpace (X i)) (retained : Finset (Sym2 V))
      (Q : SimpleGraph (FamilyQuotient X p)),
      retained ⊆ G.edgeFinset ∧
      (G.edgeFinset \ retained).card ≤ 2 * ∑ i, (X i).card ∧
      Q.edgeSet = ((retained.image (Sym2.map (familyProject X hd p)) :
         Finset (Sym2 (FamilyQuotient X p))) : Set (Sym2 (FamilyQuotient X p))) ∧
      (∀ e ∈ Q.edgeSet, ∃! f, f ∈ retained ∧ Sym2.map (familyProject X hd p) f = e) ∧
      Fintype.card (FamilyQuotient X p) = Fintype.card V - ∑ i, (X i).card / 2 := by
  classical
  obtain ⟨p,hp⟩ := exists_le_finiteAverage (fun p : ∀ i, PairingSpace (X i) =>
      (foldErrorBudget X hd G p : ℝ))
  have hcostR := hp.trans (folding_average_bound G X hd a ha hm hma hdegree hneighbor)
  have hcost : foldErrorBudget X hd G p ≤ 2 * ∑ i, (X i).card := by exact_mod_cast hcostR
  obtain ⟨retained,Q,hsub,herr,hQ,hrep⟩ := simple_quotient_representatives G (familyProject X hd p)
  exact ⟨p,retained,Q,hsub,herr.trans ((quotientDefect_le_budget X hd G p).trans hcost),
    hQ,hrep,family_quotient_order X hd p⟩

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse11} [Fintype V] (G : SimpleGraph V)

def heavyNeighbors (X : Finset V) (a : ℝ) : Finset V :=
  Finset.univ.filter (fun v => a < (neighborsIn G X v : ℝ))

lemma mem_heavyNeighbors (X : Finset V) (a : ℝ) (v : V) :
    v ∈ heavyNeighbors G X a ↔ a < (neighborsIn G X v : ℝ) := by simp [heavyNeighbors]

lemma heavyNeighbors_disjoint_active (X Y : Finset V) (a : ℝ)
    (hY : ∀ v ∈ Y, (G.degree v : ℝ) ≤ a) :
    Disjoint (heavyNeighbors G X a) Y := by
  apply Finset.disjoint_left.mpr
  intro v hv hy
  have h₁ := (mem_heavyNeighbors G X a v).mp hv
  have h₂ : (neighborsIn G X v : ℝ) ≤ G.degree v := by
    exact_mod_cast neighborsIn_le_degree G X v
  exact (not_lt_of_ge (h₂.trans (hY v hy))) h₁

lemma heavyNeighbors_card_le (X : Finset V) (a : ℝ) (ha : 0 < a)
    (hX : ∀ v ∈ X, (G.degree v : ℝ) ≤ a) :
    (heavyNeighbors G X a).card ≤ X.card := by
  have hsum : a * (heavyNeighbors G X a).card ≤
      ∑ v ∈ heavyNeighbors G X a, (neighborsIn G X v : ℝ) := by
    calc
      _ = ∑ _v ∈ heavyNeighbors G X a, a := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun v hv =>
        ((mem_heavyNeighbors G X a v).mp hv).le
  have hsub : (∑ v ∈ heavyNeighbors G X a, (neighborsIn G X v : ℝ)) ≤
      ∑ v, (neighborsIn G X v : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  have htotal : (∑ v, (neighborsIn G X v : ℝ)) ≤ a * X.card := by
    rw [← Nat.cast_sum, sum_incidence_to_set G X, Nat.cast_sum]
    simpa [mul_comm] using Finset.sum_le_sum (s := X) (fun v hv => hX v hv)
  have hh := hsum.trans (hsub.trans htotal)
  have := (mul_le_mul_iff_right₀ ha).mp hh
  exact_mod_cast this

variable {I : Type cycleUniverse12} [Fintype I] (X : I → Finset V)

def heavyDesignated (a : ℝ) (i : I) : SimpleGraph V :=
  crossGraph G (X i) (heavyNeighbors G (X i) a)

lemma heavyDesignated_le {V : Type cycleUniverse13} [_contextInstance1 : Fintype V] (G : SimpleGraph V) {I : Type cycleUniverse14} [_contextInstance4 : Fintype I] (X : I → Finset V) (a : ℝ) (i : I) : heavyDesignated G X a i ≤ G :=
  fun _ _ h => h.1

theorem heavyDesignated_pairwise {V : Type cycleUniverse15} [_contextInstance1 : Fintype V] (G : SimpleGraph V) {I : Type cycleUniverse16} [_contextInstance4 : Fintype I] (X : I → Finset V) (a : ℝ)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hdegree : ∀ i v, v ∈ X i → (G.degree v : ℝ) ≤ a) :
    Pairwise (fun i j => Disjoint (heavyDesignated G X a i).edgeSet
      (heavyDesignated G X a j).edgeSet) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro e hei hej
  induction e using Sym2.ind with
  | _ u v =>
    change G.Adj u v ∧ ((u ∈ X i ∧ v ∈ heavyNeighbors G (X i) a) ∨
      (u ∈ heavyNeighbors G (X i) a ∧ v ∈ X i)) at hei
    change G.Adj u v ∧ ((u ∈ X j ∧ v ∈ heavyNeighbors G (X j) a) ∨
      (u ∈ heavyNeighbors G (X j) a ∧ v ∈ X j)) at hej
    rcases hei.2 with hi | hi <;> rcases hej.2 with hj | hj
    · exact Finset.disjoint_left.mp (hd hij) hi.1 hj.1
    · exact Finset.disjoint_left.mp
        (heavyNeighbors_disjoint_active G (X j) (X i) a (hdegree i)) hj.1 hi.1
    · exact Finset.disjoint_left.mp
        (heavyNeighbors_disjoint_active G (X i) (X j) a (hdegree j)) hi.1 hj.1
    · exact Finset.disjoint_left.mp (hd hij) hi.2 hj.2

def trimHeavyGraph (a : ℝ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ∀ i, ¬ (heavyDesignated G X a i).Adj u v
  symm := ⟨fun _ _ h => ⟨h.1.symm,fun i hi => h.2 i hi.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

lemma trimHeavyGraph_le {V : Type cycleUniverse17} [_contextInstance1 : Fintype V] (G : SimpleGraph V) {I : Type cycleUniverse18} [_contextInstance4 : Fintype I] (X : I → Finset V) (a : ℝ) : trimHeavyGraph G X a ≤ G := fun _ _ h => h.1

theorem trimHeavyGraph_neighbors {V : Type cycleUniverse19} [_contextInstance1 : Fintype V] (G : SimpleGraph V) {I : Type cycleUniverse20} [_contextInstance4 : Fintype I] (X : I → Finset V) (a : ℝ) (ha : 0 ≤ a) (i : I) (v : V) :
    (neighborsIn (trimHeavyGraph G X a) (X i) v : ℝ) ≤ a := by
  by_cases hv : v ∈ heavyNeighbors G (X i) a
  · have he : (X i).filter ((trimHeavyGraph G X a).Adj v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨hui,hvu⟩ := Finset.mem_filter.mp hu
      exact hvu.2 i ⟨hvu.1,Or.inr ⟨hv,hui⟩⟩
    simpa [neighborsIn, he] using ha
  · have hnon : (neighborsIn G (X i) v : ℝ) ≤ a :=
      le_of_not_gt (fun hh => hv ((mem_heavyNeighbors G (X i) a v).mpr hh))
    apply le_trans _ hnon
    exact_mod_cast Finset.card_le_card (show
      (X i).filter ((trimHeavyGraph G X a).Adj v) ⊆ (X i).filter (G.Adj v) from
      fun u hu => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,
        (Finset.mem_filter.mp hu).2.1⟩)

theorem trimHeavyGraph_degree (a : ℝ) (v : V) :
    (trimHeavyGraph G X a).degree v ≤ G.degree v := by
  classical
  exact SimpleGraph.degree_le_of_le (trimHeavyGraph_le G X a)

theorem trimHeavyGraph_ledger (a : ℝ) :
    (trimHeavyGraph G X a).edgeSet ∪
      (⋃ i, (heavyDesignated G X a i).edgeSet) = G.edgeSet ∧
    Disjoint (trimHeavyGraph G X a).edgeSet
      (⋃ i, (heavyDesignated G X a i).edgeSet) := by
  constructor
  · ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Set.mem_union, Set.mem_iUnion, SimpleGraph.mem_edgeSet]
      change (G.Adj u v ∧ ∀ i, ¬ (heavyDesignated G X a i).Adj u v) ∨
        (∃ i, (heavyDesignated G X a i).Adj u v) ↔ G.Adj u v
      constructor
      · rintro (h | ⟨i,hi⟩)
        · exact h.1
        · exact hi.1
      · intro h
        by_cases he : ∃ i, (heavyDesignated G X a i).Adj u v
        · exact Or.inr he
        · exact Or.inl ⟨h,fun i hi => he ⟨i,hi⟩⟩
  · apply Set.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hf
      exact he.2 i hi

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open _root_.SimpleGraph
attribute [local instance] Classical.propDecidable

structure TrimmedPath {V : Type cycleUniverse21} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  simple : walk.IsPath

lemma alternating_endpoint_mem {V : Type cycleUniverse22} {G : SimpleGraph V} (X H : Set V)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hp : 0 < p.length) :
    (a ∈ X ∨ a ∈ H) ∧ (b ∈ X ∨ b ∈ H) := by
  have hn : ¬p.Nil := by intro h; have := h.length_eq_zero; omega
  constructor
  · exact (hbi (p.adj_snd hn)).elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  · exact (hbi (p.adj_penultimate hn)).elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)

lemma alternating_snd_mem {V : Type cycleUniverse23} {G : SimpleGraph V} (X H : Set V)
    (hd : Disjoint X H)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hp : 0 < p.length) (ha : a ∈ H) : p.snd ∈ X := by
  have hn : ¬p.Nil := by intro h; have := h.length_eq_zero; omega
  rcases hbi (p.adj_snd hn) with h | h
  · exact False.elim (Set.disjoint_left.mp hd h.1 ha)
  · exact h.2

lemma alternating_penultimate_mem {V : Type cycleUniverse24} {G : SimpleGraph V} (X H : Set V)
    (hd : Disjoint X H)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hp : 0 < p.length) (hb : b ∈ H) :
    p.penultimate ∈ X := by
  have hn : ¬p.Nil := by intro h; have := h.length_eq_zero; omega
  rcases hbi (p.adj_penultimate hn) with h | h
  · exact h.1
  · exact False.elim (Set.disjoint_left.mp hd h.2 hb)

theorem trim_bipartite_path {V : Type cycleUniverse25} {G : SimpleGraph V} (X H : Set V)
    (hd : Disjoint X H)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hs : p.IsPath) (hp : 0 < p.length) :
    ∃ q : TrimmedPath G,
      q.walk.edgeSet ⊆ p.edgeSet ∧ p.length ≤ q.walk.length + 2 ∧
      (0 < q.walk.length → q.start ∈ X ∧ q.finish ∈ X) := by
  have hends := alternating_endpoint_mem X H hbi p hp
  by_cases ha : a ∈ H
  · have hsa := alternating_snd_mem X H hd hbi p hp ha
    by_cases hb : b ∈ H
    · refine ⟨⟨p.snd,p.tail.penultimate,p.tail.dropLast,hs.tail.dropLast⟩,?_,?_,?_⟩
      · intro e he
        simp only [Walk.mem_edgeSet, Walk.edges_dropLast, Walk.edges_tail] at he ⊢
        exact List.mem_of_mem_tail (List.mem_of_mem_dropLast he)
      · simp only [Walk.length_dropLast,Walk.length_tail]
        omega
      · intro hpos
        have ht : 0 < p.tail.length := by
          change 0 < p.tail.dropLast.length at hpos
          rw [Walk.length_dropLast] at hpos
          omega
        exact ⟨hsa,alternating_penultimate_mem X H hd hbi p.tail ht hb⟩
    · refine ⟨⟨p.snd,b,p.tail,hs.tail⟩,?_,?_,?_⟩
      · intro e he
        simp only [Walk.mem_edgeSet, Walk.edges_tail] at he ⊢
        exact List.mem_of_mem_tail he
      · simp only [Walk.length_tail]; omega
      · intro _
        exact ⟨hsa,hends.2.resolve_right hb⟩
  · by_cases hb : b ∈ H
    · refine ⟨⟨a,p.penultimate,p.dropLast,hs.dropLast⟩,?_,?_,?_⟩
      · intro e he
        simp only [Walk.mem_edgeSet, Walk.edges_dropLast] at he ⊢
        exact List.mem_of_mem_dropLast he
      · simp only [Walk.length_dropLast]; omega
      · intro _
        exact ⟨hends.1.resolve_right ha,alternating_penultimate_mem X H hd hbi p hp hb⟩
    · exact ⟨⟨a,b,p,hs⟩,Set.Subset.rfl,by change p.length ≤ p.length + 2; omega,fun _ =>
        ⟨hends.1.resolve_right ha,hends.2.resolve_right hb⟩⟩

lemma bipartite_path_length {V : Type cycleUniverse26} {G : SimpleGraph V} (X H : Set V)
    (hd : Disjoint X H)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hp : 0 < p.length) (ha : a ∈ X) (hb : b ∈ X) :
    2 ≤ p.length := by
  by_contra h
  have hlen : p.length = 1 := by omega
  rcases hbi (Walk.adj_of_length_eq_one hlen) with he | he
  · exact Set.disjoint_left.mp hd hb he.2
  · exact Set.disjoint_left.mp hd ha he.1

lemma path_edgeFinset_card {V : Type cycleUniverse27} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) : p.edges.toFinset.card = p.length := by
  classical
  rw [List.toFinset_card_of_nodup hp.isTrail.edges_nodup, Walk.length_edges]

theorem trim_bipartite_path_ledger {V : Type cycleUniverse28} {G : SimpleGraph V} (X H : Set V)
    (hd : Disjoint X H)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hs : p.IsPath) (hp : 0 < p.length) :
    ∃ (q : TrimmedPath G) (discarded : Finset (Sym2 V)),
      discarded.card ≤ 2 ∧ Disjoint (discarded : Set (Sym2 V)) q.walk.edgeSet ∧
      (discarded : Set (Sym2 V)) ∪ q.walk.edgeSet = p.edgeSet ∧
      (0 < q.walk.length → q.start ∈ X ∧ q.finish ∈ X ∧ 2 ≤ q.walk.length) := by
  classical
  obtain ⟨q,hsub,hlen,hends⟩ := trim_bipartite_path X H hd hbi p hs hp
  have hfs : q.walk.edges.toFinset ⊆ p.edges.toFinset := by
    intro e he
    exact List.mem_toFinset.mpr (hsub (List.mem_toFinset.mp he))
  refine ⟨q,p.edges.toFinset \ q.walk.edges.toFinset,?_,?_,?_,?_⟩
  · rw [Finset.card_sdiff_of_subset hfs, path_edgeFinset_card p hs,
      path_edgeFinset_card q.walk q.simple]
    omega
  · rw [Set.disjoint_left]
    intro e he hq
    exact (Finset.mem_sdiff.mp he).2 (List.mem_toFinset.mpr hq)
  · ext e
    simp only [Set.mem_union, Finset.mem_coe, Finset.mem_sdiff, List.mem_toFinset,
      Walk.mem_edgeSet]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact hsub h
    · intro h
      by_cases he : e ∈ q.walk.edges
      · exact Or.inr he
      · exact Or.inl ⟨h,he⟩
  · intro hpos
    obtain ⟨ha,hb⟩ := hends hpos
    exact ⟨ha,hb,bipartite_path_length X H hd hbi q.walk hpos ha hb⟩

theorem close_trimmed_path {V : Type cycleUniverse29} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (q : G.Walk b a) (hp : p.IsPath) (hq : q.IsPath)
    (hlen : 2 ≤ p.length)
    (havoid : ∀ v ∈ q.support, v ≠ a → v ≠ b → v ∉ p.support) :
    (p.append q).IsCycle ∧ (p.append q).edgeSet = p.edgeSet ∪ q.edgeSet := by
  refine ⟨hp.isCycle_append hq ?_ (Or.inl (by omega)), Walk.edgeSet_append p q⟩
  rw [List.disjoint_left]
  intro v hvp hvq
  have hva : v ≠ a := by
    intro h; subst v
    have hn := hp.support_nodup
    rw [← p.cons_tail_support] at hn
    exact hn.notMem hvp
  have hvb : v ≠ b := by
    intro h; subst v
    have hn := hq.support_nodup
    rw [← q.cons_tail_support] at hn
    exact hn.notMem hvq
  exact havoid v (List.mem_of_mem_tail hvq) hva hvb (List.mem_of_mem_tail hvp)

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open _root_.Finset _root_.SimpleGraph
attribute [local instance] Classical.propDecidable

lemma endpoint_path_count_on {V : Type cycleUniverse30} {I : Type cycleUniverse31} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G) (S : Finset V)
    (hends : ∀ i, (P i).start ∈ S ∧ (P i).finish ∈ S)
    (hload : ∀ v, (univ.filter (fun i => (P i).start = v ∨ (P i).finish = v)).card ≤ 2) :
    Fintype.card I ≤ S.card := by
  classical
  have heq : ∑ v ∈ S, (univ.filter (fun i => (P i).start = v ∨ (P i).finish = v)).card =
      2 * Fintype.card I := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
    have hc : ∀ i : I, (∑ v ∈ S, if (P i).start = v ∨ (P i).finish = v then 1 else 0) = 2 := by
      intro i
      have hf : S.filter (fun v => (P i).start = v ∨ (P i).finish = v) =
          {(P i).start,(P i).finish} := by
        ext v
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
        constructor
        · intro h; simpa only [eq_comm] using h.2
        · intro h
          rcases h with rfl | rfl
          · exact ⟨(hends i).1,Or.inl rfl⟩
          · exact ⟨(hends i).2,Or.inr rfl⟩
      rw [← Finset.sum_filter,hf]
      simp [(P i).endpoints_ne]
    simp_rw [hc]
    simp [mul_comm]
  have hb := Finset.sum_le_sum (fun v (_ : v ∈ S) => hload v)
  rw [heq] at hb
  simp only [Finset.sum_const, smul_eq_mul] at hb
  omega

lemma heavy_paths {V : Type cycleUniverse32} [Fintype V] (G : SimpleGraph V)
    (X : Finset V) (a : ℝ) (ha : 0 < a)
    (hdeg : ∀ v ∈ X, (G.degree v:ℝ) ≤ a) :
    let H := heavyNeighbors G X a
    let B := crossGraph G X H
    ∃ (k : ℕ) (P : Fin k → PositiveSimplePath B),
      Pairwise (fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
      (⋃ i, (P i).walk.edgeSet) = B.edgeSet ∧ k ≤ 2 * X.card := by
  classical
  dsimp only
  obtain ⟨k,P,hd,hu,hl,_⟩ := endpoint_path_partition (crossGraph G X (heavyNeighbors G X a))
  refine ⟨k,P,hd,hu,?_⟩
  have hend : ∀ i, (P i).start ∈ X ∪ heavyNeighbors G X a ∧
      (P i).finish ∈ X ∪ heavyNeighbors G X a := by
    intro i
    have h := alternating_endpoint_mem (X:Set V) (heavyNeighbors G X a : Set V)
      (fun {_ _} (h : (crossGraph G X (heavyNeighbors G X a)).Adj _ _) => h.2) (P i).walk (P i).positive
    exact ⟨Finset.mem_union.mpr h.1,Finset.mem_union.mpr h.2⟩
  have hk := endpoint_path_count_on P (X ∪ heavyNeighbors G X a) hend hl
  rw [Fintype.card_fin] at hk
  have hh := heavyNeighbors_card_le G X a ha hdeg
  exact hk.trans ((Finset.card_union_le _ _).trans (by omega))

structure PreparedBatch {V I : Type} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (X : I → Finset V)
    (hd : Pairwise fun i j => Disjoint (X i) (X j)) where
  pairing : ∀ i, PairingSpace (X i)
  quotient : SimpleGraph (FamilyQuotient X pairing)
  retained : Finset (Sym2 V)
  bad : Finset (Sym2 V)
  count : I → ℕ
  path : ∀ i, Fin (count i) → TrimmedPath G
  count_le : ∀ i, count i ≤ 2 * (X i).card
  bad_le : bad.card ≤ 6 * ∑ i, (X i).card
  ends : ∀ i j, 0 < (path i j).walk.length →
    (path i j).start ∈ X i ∧ (path i j).finish ∈ X i ∧ 2 ≤ (path i j).walk.length
  paths_disjoint : Pairwise fun z w : Σ i, Fin (count i) =>
    Disjoint (path z.1 z.2).walk.edgeSet (path w.1 w.2).walk.edgeSet
  bad_paths : ∀ i j, Disjoint (bad : Set (Sym2 V)) (path i j).walk.edgeSet
  retained_paths : ∀ i j, Disjoint (retained : Set (Sym2 V)) (path i j).walk.edgeSet
  bad_retained : Disjoint (bad : Set (Sym2 V)) (retained : Set (Sym2 V))
  cover : (bad : Set (Sym2 V)) ∪ (retained : Set (Sym2 V)) ∪
    (⋃ (i) (j), (path i j).walk.edgeSet) = G.edgeSet
  quotient_edges : quotient.edgeSet =
    (Sym2.map (familyProject X hd pairing)) '' (retained : Set (Sym2 V))
  representatives : ∀ e ∈ quotient.edgeSet, ∃! f,
    f ∈ retained ∧ Sym2.map (familyProject X hd pairing) f = e
  order : Fintype.card (FamilyQuotient X pairing) =
    Fintype.card V - ∑ i, (X i).card / 2

lemma PreparedBatch.bad_subset {V I : Type} [Fintype V] [Fintype I]
    {G : SimpleGraph V} {X : I → Finset V} {hd}
    (b : PreparedBatch G X hd) : (b.bad : Set (Sym2 V)) ⊆ G.edgeSet := by
  rw [← b.cover]; exact Set.subset_union_of_subset_left (Set.subset_union_left) _

lemma PreparedBatch.retained_subset {V I : Type} [Fintype V] [Fintype I]
    {G : SimpleGraph V} {X : I → Finset V} {hd}
    (b : PreparedBatch G X hd) : (b.retained : Set (Sym2 V)) ⊆ G.edgeSet := by
  rw [← b.cover]; exact Set.subset_union_of_subset_left (Set.subset_union_right) _

theorem prepare_batch {V I : Type} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (X : I → Finset V)
    (hd : Pairwise fun i j => Disjoint (X i) (X j))
    (a : ℝ) (ha : 1 ≤ a) (hm : ∀ i, 8 ≤ (X i).card)
    (hma : ∀ i, a^2 ≤ (X i).card)
    (hdeg : ∀ i v, v ∈ X i → (G.degree v:ℝ) ≤ a) :
    Nonempty (PreparedBatch G X hd) := by
  classical
  let H := heavyDesignated G X a
  let T := trimHeavyGraph G X a
  have hHpair := heavyDesignated_pairwise G X a hd hdeg
  have hT := trimHeavyGraph_ledger G X a
  have hpaths : ∀ i, ∃ (k : ℕ) (P : Fin k → PositiveSimplePath (H i)),
      Pairwise (fun j l => Disjoint (P j).walk.edgeSet (P l).walk.edgeSet) ∧
      (⋃ j, (P j).walk.edgeSet) = (H i).edgeSet ∧ k ≤ 2*(X i).card :=
    fun i => heavy_paths G (X i) a (by linarith) (hdeg i)
  choose k P hPd hPu hk using hpaths
  have htrim : ∀ i j, ∃ (q : TrimmedPath (H i)) (S : Finset (Sym2 V)),
      S.card ≤ 2 ∧ Disjoint (S:Set _) q.walk.edgeSet ∧
      (S:Set _) ∪ q.walk.edgeSet = (P i j).walk.edgeSet ∧
      (0 < q.walk.length → q.start ∈ X i ∧ q.finish ∈ X i ∧ 2 ≤ q.walk.length) := by
    intro i j
    exact trim_bipartite_path_ledger (X i:Set V) (heavyNeighbors G (X i) a:Set V)
      (by simpa only [Finset.disjoint_coe] using
        (heavyNeighbors_disjoint_active G (X i) (X i) a (hdeg i)).symm)
      (fun {_ _} (h : (H i).Adj _ _) => h.2) (P i j).walk (P i j).isPath (P i j).positive
  choose q S hSnum hSq hScover hEnds using htrim
  let Qpath : ∀ i, Fin (k i) → TrimmedPath G := fun i j =>
    ⟨(q i j).start,(q i j).finish,(q i j).walk.map (SimpleGraph.Hom.ofLE (heavyDesignated_le G X a i)),
      (q i j).simple.map (Function.injective_id)⟩
  have hQedges : ∀ i j, (Qpath i j).walk.edgeSet = (q i j).walk.edgeSet := by
    intro i j; simp [Qpath,Walk.edgeSet_map,SimpleGraph.Hom.ofLE]
  have hQlen : ∀ i j, (Qpath i j).walk.length = (q i j).walk.length :=
    fun i j => Walk.length_map _ _
  have hSsub : ∀ i j, (S i j:Set _) ⊆ (P i j).walk.edgeSet := by
    intro i j; rw [← hScover i j]; exact Set.subset_union_left
  have hqsub : ∀ i j, (Qpath i j).walk.edgeSet ⊆ (P i j).walk.edgeSet := by
    intro i j; rw [hQedges,← hScover i j]; exact Set.subset_union_right
  have hPsub : ∀ i j, (P i j).walk.edgeSet ⊆ (H i).edgeSet :=
    fun i j => (P i j).walk.edges_subset_edgeSet
  have hPdall : Pairwise fun z w : Σ i, Fin (k i) =>
      Disjoint (P z.1 z.2).walk.edgeSet (P w.1 w.2).walk.edgeSet := by
    rintro ⟨i,j⟩ ⟨l,m⟩ hne
    by_cases hi : i = l
    · subst l
      exact hPd i (fun he => hne (by cases he; rfl))
    · exact (hHpair hi).mono (hPsub _ _) (hPsub _ _)
  let B := Finset.univ.biUnion fun z : Σ i, Fin (k i) => S z.1 z.2
  have hB : (B:Set (Sym2 V)) = ⋃ i, ⋃ j, (S i j : Set (Sym2 V)) := by
    ext e; simp [B]
  have hBnum : B.card ≤ 4 * ∑ i, (X i).card := by
    have hc : B.card ≤ ∑ z : Σ i, Fin (k i), (S z.1 z.2).card :=
      Finset.card_biUnion_le
    have hj : (∑ z : Σ i, Fin (k i), (S z.1 z.2).card) ≤ 2 * ∑ i, k i := by
      calc
        _ ≤ ∑ z : Σ i, Fin (k i), 2 := Finset.sum_le_sum (fun z _ => hSnum z.1 z.2)
        _ = _ := by simp [Fintype.card_sigma,mul_comm]
    have hk' := Finset.sum_le_sum (fun i (_:i∈(univ:Finset I)) => hk i)
    rw [← Finset.mul_sum] at hk'
    omega
  have hBheavy : (B:Set (Sym2 V)) ⊆ ⋃ i, (H i).edgeSet := by
    rw [hB]; exact Set.iUnion_subset (fun i => Set.iUnion_subset (fun j =>
      Set.subset_iUnion_of_subset i ((hSsub i j).trans (hPsub i j))))
  have hBhq : ∀ i j, Disjoint (B:Set (Sym2 V)) (Qpath i j).walk.edgeSet := by
    intro i j
    rw [hB,Set.disjoint_iUnion_left]
    intro l
    rw [Set.disjoint_iUnion_left]
    intro m
    by_cases he : (⟨l,m⟩ : Σ i, Fin (k i)) = ⟨i,j⟩
    · cases he
      rw [hQedges]; exact hSq i j
    · exact (hPdall he).mono (hSsub l m) (hqsub i j)
  have hdegT : ∀ i v, v ∈ X i → (T.degree v:ℝ) ≤ a := by
    intro i v hv
    exact (show (T.degree v:ℝ) ≤ G.degree v by exact_mod_cast trimHeavyGraph_degree G X a v).trans (hdeg i v hv)
  obtain ⟨p,R,Q,hR,hBad,hQ,hrep,horder⟩ := pair_folding T X hd a ha hm hma hdegT
    (trimHeavyGraph_neighbors G X a (by linarith))
  let A := T.edgeFinset \ R
  have hA : (A:Set (Sym2 V)) = T.edgeSet \ (R:Set (Sym2 V)) := by
    simp [A,SimpleGraph.coe_edgeFinset]
  have hR' : (R:Set (Sym2 V)) ⊆ T.edgeSet := by
    intro e he; exact SimpleGraph.mem_edgeFinset.mp (hR he)
  refine ⟨⟨p,Q,R,A ∪ B,k,Qpath,hk,?_,?_,?_,?_,?_,?_,?_,?_,hrep,horder⟩⟩
  · exact (Finset.card_union_le _ _).trans (by
      have hn : A.card ≤ 2 * ∑ i, (X i).card := hBad
      omega)
  · intro i j hp
    simpa only [Qpath,Walk.length_map] using hEnds i j (by rwa [hQlen] at hp)
  · intro z w hzw
    exact (hPdall hzw).mono (hqsub _ _) (hqsub _ _)
  · intro i j
    rw [Finset.coe_union,Set.disjoint_union_left]
    refine ⟨?_,hBhq i j⟩
    apply hT.2.mono
    · rw [hA]; exact Set.sdiff_subset
    · exact (hqsub i j).trans ((hPsub i j).trans (Set.subset_iUnion (fun i => (H i).edgeSet) i))
  · intro i j
    exact hT.2.mono hR' ((hqsub i j).trans ((hPsub i j).trans (Set.subset_iUnion (fun i => (H i).edgeSet) i)))
  · rw [Finset.coe_union,Set.disjoint_union_left]
    refine ⟨?_,hT.2.symm.mono hBheavy hR'⟩
    rw [hA]; exact Set.disjoint_sdiff_left
  · have hheavy : (B:Set (Sym2 V)) ∪ (⋃ i, ⋃ j, (Qpath i j).walk.edgeSet) =
        ⋃ i, (H i).edgeSet := by
      rw [hB,← Set.iUnion_union_distrib]
      congr 1
      funext i
      rw [← Set.iUnion_union_distrib]
      simp_rw [hQedges,hScover]
      exact hPu i
    rw [Finset.coe_union]
    have hAR : (A:Set (Sym2 V)) ∪ (R:Set (Sym2 V)) = T.edgeSet := by
      rw [hA]; exact Set.sdiff_union_of_subset hR'
    calc
      _ = ((A:Set _) ∪ (R:Set _)) ∪ ((B:Set _) ∪ ⋃ i, ⋃ j, (Qpath i j).walk.edgeSet) := by
        ext e; simp only [Set.mem_union]; tauto
      _ = T.edgeSet ∪ ⋃ i, (H i).edgeSet := by rw [hAR,hheavy]
      _ = G.edgeSet := hT.1
  · simpa only [Finset.coe_image] using hQ

end
end ErdosGallai.Batch
end
/-! ### Upstream module `Combinatorics/CycleDecomposition/BatchRouting.lean` -/

section
open _root_.Filter _root_.Asymptotics _root_.Real
noncomputable section
open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Finset
namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable

lemma family_quotient_image_order {V I : Type} [Fintype V] [Fintype I]
    (X : I → Finset V) (hd : Pairwise fun i j => Disjoint (X i) (X j))
    (p : ∀ i, PairingSpace (X i)) (W : Finset V) (hX : ∀ i, X i ⊆ W) :
    (W.image (familyProject X hd p)).card + ∑ i, (X i).card / 2 = W.card := by
  classical
  let projMap := familyProject X hd p
  have hi : Set.InjOn projMap (↑Wᶜ : Set V) := by
    intro x hx y hy h
    rcases (familyProject_eq_iff X hd p x y).mp h with he | ⟨i,hx',hy',_⟩
    · exact he
    · exact False.elim (Finset.mem_compl.mp hx (hX i hx'))
  have hd' : Disjoint (W.image projMap) (Wᶜ.image projMap) := by
    apply Finset.disjoint_left.mpr
    rintro z hz hz'
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hz'
    rcases (familyProject_eq_iff X hd p y x).mp he with he | ⟨i,hy',hx',_⟩
    · subst y; exact Finset.mem_compl.mp hy hx
    · exact Finset.mem_compl.mp hy (hX i hy')
  have hu : W.image projMap ∪ Wᶜ.image projMap = univ := by
    rw [← Finset.image_union,Finset.union_compl]
    exact Finset.image_univ_of_surjective (familyProject_surjective X hd p)
  have hc := Finset.card_union_of_disjoint hd'
  rw [hu,Finset.card_univ,Finset.card_image_of_injOn hi] at hc
  have hc' := Finset.card_compl W
  have h := family_quotient_order_add X hd p
  dsimp only [projMap] at hc
  have hWcard := Finset.card_le_univ W
  omega

lemma PreparedBatch.quotient_supported {V I : Type} [Fintype V] [Fintype I]
    {G : SimpleGraph V} {X : I → Finset V} {hd}
    (b : PreparedBatch G X hd) (W : Finset V)
    (hW : ∀ ⦃x y⦄, G.Adj x y → x ∈ W ∧ y ∈ W) :
    ∀ ⦃x y⦄, b.quotient.Adj x y →
      x ∈ W.image (familyProject X hd b.pairing) ∧
      y ∈ W.image (familyProject X hd b.pairing) := by
  classical
  intro x y hxy
  have he : s(x,y) ∈ b.quotient.edgeSet := hxy
  rw [b.quotient_edges] at he
  obtain ⟨e,he,heq⟩ := he
  induction e using Sym2.ind with
  | _ u v =>
    have huv : G.Adj u v := b.retained_subset he
    have hu := Finset.mem_image_of_mem (familyProject X hd b.pairing) (hW huv).1
    have hv := Finset.mem_image_of_mem (familyProject X hd b.pairing) (hW huv).2
    change s(familyProject X hd b.pairing u,familyProject X hd b.pairing v) = s(x,y) at heq
    rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hu,hv⟩
    · exact ⟨hv,hu⟩

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch

variable {V : Type} [Fintype V] [DecidableEq V]

def CutExpansion (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ) : Prop :=
  ∀ U : Finset V, h * min (U.card : ℝ) (Uᶜ.card : ℝ) ≤
    ((P.interedges U Uᶜ).card : ℝ)

lemma boundary_sym2_injective (P : SimpleGraph V) [DecidableRel P.Adj]
    (U : Finset V) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges U Uᶜ : Set (V × V)) := by
  intro e he f hf hef
  rcases (Sym2.mk_eq_mk_iff.mp hef) with h | h
  · exact h
  · have he1 := (P.mem_interedges_iff.mp he).1
    have hf2 := (P.mem_interedges_iff.mp hf).2.1
    have hfirst : e.1 = f.2 := congrArg Prod.fst h
    exact False.elim ((Finset.mem_compl.mp hf2) (hfirst ▸ he1))

theorem routing_union_growth_step_of_boundary
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h)
    (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (B Bnext : Finset V)
    (W : V → Finset V)
    (hmono : B ⊆ Bnext)
    (hsmall : (B.card : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hF : (((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card : ℝ) ≤
      h * (B.card : ℝ) / 4)
    (hW : ∀ v ∈ B, ((W v).card : ℝ) ≤ h / 4)
    (hextend : ∀ v ∈ B, ∀ w ∉ B, P.Adj v w → s(v, w) ∉ F →
      w ∉ W v → w ∈ Bnext) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (B.card : ℝ) ≤
      (Bnext.card : ℝ) := by
  let E := P.interedges B Bᶜ
  let Ebad := E.filter (fun e => s(e.1, e.2) ∈ F)
  let Vbad := B.biUnion (fun v => ({v} : Finset V) ×ˢ (W v))
  let Enew := (Finset.univ : Finset V) ×ˢ (Bnext \ B)
  have hcover : E ⊆ Ebad ∪ Vbad ∪ Enew := by
    intro e he
    rcases P.mem_interedges_iff.mp he with ⟨hv, hw, hadj⟩
    have hnw : e.2 ∉ B := Finset.mem_compl.mp hw
    by_cases hdel : s(e.1, e.2) ∈ F
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨he, hdel⟩))
    by_cases hforbid : e.2 ∈ W e.1
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨e.1, hv, Finset.mem_product.mpr ⟨by simp, hforbid⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_sdiff.mpr
        ⟨hextend e.1 hv e.2 hnw hadj hdel hforbid, hnw⟩⟩
  have hcount : E.card ≤ Ebad.card + Vbad.card + Enew.card :=
    (Finset.card_le_card hcover).trans <|
      (Finset.card_union_le _ _).trans <|
        Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hforbidden : Vbad.card ≤ ∑ v ∈ B, (W v).card := by
    simpa [Vbad, Finset.card_product] using
      (Finset.card_biUnion_le (s := B) (t := fun v => ({v} : Finset V) ×ˢ W v))
  have hnew : Enew.card = Fintype.card V * (Bnext \ B).card := by
    simp [Enew]
  have hraw : E.card ≤ Ebad.card + (∑ v ∈ B, (W v).card) +
      Fintype.card V * (Bnext \ B).card := by omega
  have hsum : (∑ v ∈ B, ((W v).card : ℝ)) ≤ (h / 4) * B.card := by
    calc
      _ ≤ ∑ _v ∈ B, h / 4 := Finset.sum_le_sum hW
      _ = _ := by simp [mul_comm]
  have hcomplN : B.card + Bᶜ.card = Fintype.card V := by
    rw [Finset.card_compl]
    exact Nat.add_sub_of_le (Finset.card_le_univ B)
  have hcompl : (B.card : ℝ) + (Bᶜ.card : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast hcomplN
  have hlecompl : (B.card : ℝ) ≤ (Bᶜ.card : ℝ) := by linarith
  have hcut : h * (B.card : ℝ) ≤ (E.card : ℝ) := by
    simpa [min_eq_left hlecompl, E] using hexp B
  have hdiffN : (Bnext \ B).card + B.card = Bnext.card := by
    rw [Finset.card_sdiff_of_subset hmono]
    exact Nat.sub_add_cancel (Finset.card_le_card hmono)
  have hdiff : ((Bnext \ B).card : ℝ) + (B.card : ℝ) = (Bnext.card : ℝ) := by
    exact_mod_cast hdiffN
  have hrawR : (E.card : ℝ) ≤ (Ebad.card : ℝ) +
      (∑ v ∈ B, ((W v).card : ℝ)) +
      (Fintype.card V : ℝ) * ((Bnext \ B).card : ℝ) := by
    exact_mod_cast hraw
  have hreach : h * (B.card : ℝ) / 2 ≤
      (Fintype.card V : ℝ) * ((Bnext \ B).card : ℝ) := by
    nlinarith [hcut, hrawR, hF, hsum]
  have hdiv : h * (B.card : ℝ) / (2 * (Fintype.card V : ℝ)) ≤
      ((Bnext \ B).card : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (Fintype.card V : ℝ))).mpr
    nlinarith [hreach]
  calc
    (1 + h / (2 * (Fintype.card V : ℝ))) * (B.card : ℝ)
        = (B.card : ℝ) + h * (B.card : ℝ) / (2 * (Fintype.card V : ℝ)) := by ring
    _ ≤ (B.card : ℝ) + ((Bnext \ B).card : ℝ) := add_le_add (le_refl _) hdiv
    _ = (Bnext.card : ℝ) := by linarith

def avoidGraph (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V) :
    SimpleGraph V where
  Adj v w := P.Adj v w ∧ s(v, w) ∉ F ∧ v ∉ W ∧ w ∉ W
  symm := ⟨by
    intro v w h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2.1, h.2.2.2, h.2.2.1⟩⟩
  loopless := ⟨by intro v h; exact P.irrefl h.1⟩

noncomputable def walkBall (G : SimpleGraph V) (s : V) (t : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ p : G.Walk s v, p.length ≤ t)

@[simp] lemma mem_walkBall {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (s v : V) (t : ℕ) :
    v ∈ walkBall G s t ↔ ∃ p : G.Walk s v, p.length ≤ t := by
  classical
  simp [walkBall]

lemma root_mem_walkBall (G : SimpleGraph V) (s : V) (t : ℕ) :
    s ∈ walkBall G s t := by
  exact (mem_walkBall G s s t).mpr ⟨.nil, by simp⟩

lemma walkBall_mono (G : SimpleGraph V) (s : V) {t u : ℕ} (htu : t ≤ u) :
    walkBall G s t ⊆ walkBall G s u := by
  intro v hv
  obtain ⟨p, hp⟩ := (mem_walkBall G s v t).mp hv
  exact (mem_walkBall G s v u).mpr ⟨p, hp.trans htu⟩

lemma walk_avoids_end {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s v : V} (p : (avoidGraph P F W).Walk s v) (hs : s ∉ W) : v ∉ W := by
  induction p with
  | nil => exact hs
  | cons hadj p ih => exact ih hadj.2.2.2

lemma ball_avoids (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    (s : V) (hs : s ∉ W) (t : ℕ) : Disjoint (walkBall (avoidGraph P F W) s t) W := by
  apply Finset.disjoint_left.mpr
  intro v hv
  obtain ⟨p, _⟩ := (mem_walkBall _ _ _ _).mp hv
  exact walk_avoids_end P F W p hs

lemma walkBall_step (G : SimpleGraph V) (s v w : V) (t : ℕ)
    (hv : v ∈ walkBall G s t) (hadj : G.Adj v w) :
    w ∈ walkBall G s (t + 1) := by
  obtain ⟨p, hp⟩ := (mem_walkBall _ _ _ _).mp hv
  apply (mem_walkBall _ _ _ _).mpr
  exact ⟨p.concat hadj, by simpa using Nat.add_le_add_right hp 1⟩

lemma CutExpansion.le_order (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V) :
    h ≤ (Fintype.card V : ℝ) := by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  have hcomplN : 1 ≤ ({v} : Finset V)ᶜ.card := by
    simp only [Finset.card_compl, Finset.card_singleton]
    omega
  have hcompl : (1 : ℝ) ≤ (({v} : Finset V)ᶜ.card : ℝ) := by exact_mod_cast hcomplN
  have hc := hexp {v}
  simp only [Finset.card_singleton, Nat.cast_one, min_eq_left hcompl, mul_one] at hc
  have hupper := P.card_interedges_le_mul ({v} : Finset V) ({v} : Finset V)ᶜ
  simp only [Finset.card_singleton, one_mul] at hupper
  have hle := (Finset.card_le_univ (({v} : Finset V)ᶜ))
  exact hc.trans (by exact_mod_cast hupper.trans hle)

noncomputable def routingG (r h : ℝ) : ℕ := ⌈8 * (r / h) * Real.logb 2 (2 * r)⌉₊

noncomputable def routingDepth (r : ℝ) : ℕ := ⌈Real.logb 2 r⌉₊

noncomputable def routingLength (r h : ℝ) : ℕ := 2 * routingG r h * (1 + routingDepth r)

lemma routingG_growth (r h : ℝ) (hr : 1 ≤ r) (hh : 0 < h) (hhr : h ≤ r) :
    r / 2 < (1 + h / (2 * r)) ^ routingG r h := by
  have hr0 : 0 < r := by linarith
  let x := h / (2 * r)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxle : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : 0 < 2 * r)).mpr
    linarith
  have hlog : h / (4 * r) ≤ Real.log (1 + h / (2 * r)) := by
    have heq : h / (4 * r) = x / 2 := by dsimp [x]; ring
    rw [heq]
    calc
      x / 2 ≤ 2 * x / (x + 2) := by
        apply (le_div_iff₀ (by linarith : 0 < x + 2)).mpr
        nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hxle)]
      _ ≤ Real.log (1 + x) := Real.le_log_one_add_of_nonneg hx0
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2le : Real.log 2 ≤ 1 := by
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at htwo ⊢
    exact htwo
  have hlogpos : 0 < Real.log (2 * r) := Real.log_pos (by linarith)
  have hbase : Real.log (2 * r) ≤ Real.logb 2 (2 * r) := by
    rw [Real.logb]
    apply (le_div_iff₀ hl2pos).mpr
    nlinarith
  have hg : 8 * (r / h) * Real.logb 2 (2 * r) ≤ (routingG r h : ℝ) :=
    Nat.le_ceil _
  have hlogpow : 2 * Real.log (2 * r) ≤
      Real.log ((1 + h / (2 * r)) ^ routingG r h) := by
    rw [Real.log_pow]
    calc
      2 * Real.log (2 * r) ≤ 2 * Real.logb 2 (2 * r) := by linarith
      _ = (8 * (r / h) * Real.logb 2 (2 * r)) * (h / (4 * r)) := by
        field_simp
        ; ring
      _ ≤ (routingG r h : ℝ) * (h / (4 * r)) :=
        mul_le_mul_of_nonneg_right hg (by positivity)
      _ ≤ (routingG r h : ℝ) * Real.log (1 + h / (2 * r)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
  have hsmall : Real.log (r / 2) < 2 * Real.log (2 * r) := by
    have := Real.log_le_log (by positivity : 0 < r / 2) (by linarith : r / 2 ≤ 2 * r)
    linarith
  apply (Real.log_lt_log_iff (by positivity : 0 < r / 2) (by positivity)).mp
  exact hsmall.trans_le hlogpow

def incidentEdges (F : Finset (Sym2 V)) (v : V) : Finset (Sym2 V) :=
  F.filter (fun e => v ∈ e)

lemma incidentEdges_union {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (F E : Finset (Sym2 V)) (v : V) :
    incidentEdges (F ∪ E) v = incidentEdges F v ∪ incidentEdges E v := by
  simp [incidentEdges, Finset.filter_union]

lemma incidentEdges_union_card_le (F E : Finset (Sym2 V)) (v : V) :
    (incidentEdges (F ∪ E) v).card ≤ (incidentEdges F v).card + (incidentEdges E v).card := by
  rw [incidentEdges_union]
  exact Finset.card_union_le _ _

lemma incidentEdges_sum_le (F : Finset (Sym2 V)) :
    ∑ v : V, (incidentEdges F v).card ≤ 2 * F.card := by
  have heq : ∑ v : V, (incidentEdges F v).card = ∑ e ∈ F, e.toFinset.card := by
    simp only [incidentEdges, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    simp [← Sym2.mem_toFinset]
  rw [heq]
  calc
    _ ≤ ∑ _e ∈ F, 2 := Finset.sum_le_sum (fun e _ => by
      rw [Sym2.card_toFinset]
      split <;> norm_num)
    _ = 2 * F.card := by simp [mul_comm]

lemma incidentEdges_path_start_le_one {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) :
    (incidentEdges p.edges.toFinset s).card ≤ 1 := by
  have hsub : incidentEdges p.edges.toFinset s ⊆ {s(s, p.snd)} := by
    intro e he
    obtain ⟨heP, hs⟩ := Finset.mem_filter.mp he
    obtain ⟨v, hev⟩ := Sym2.mem_iff_exists.mp hs
    subst e
    have hv := hp.eq_snd_of_mem_edges (List.mem_toFinset.mp heP)
    simp [hv]
  exact (Finset.card_le_card hsub).trans (by simp)

lemma incidentEdges_path_end_le_one (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) :
    (incidentEdges p.edges.toFinset t).card ≤ 1 := by
  simpa using incidentEdges_path_start_le_one G p.reverse hp.reverse

lemma incidentEdges_walk_eq_empty_of_not_mem {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) {s t v : V}
    (p : G.Walk s t) (hv : v ∉ p.support) : incidentEdges p.edges.toFinset v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heP, hve⟩ := Finset.mem_filter.mp he
  have hm := p.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, List.mem_toFinset.mp heP, hve⟩)
  exact hv hm

lemma incidentEdges_path_le_two (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) (v : V) :
    (incidentEdges p.edges.toFinset v).card ≤ 2 := by
  by_cases hv : v ∈ p.support
  · have htake := incidentEdges_path_end_le_one G (p.takeUntil v hv) (hp.takeUntil hv)
    have hdrop := incidentEdges_path_start_le_one G (p.dropUntil v hv) (hp.dropUntil hv)
    have heq : p.edges.toFinset = (p.takeUntil v hv).edges.toFinset ∪ (p.dropUntil v hv).edges.toFinset := by
      have he := congrArg (fun q : G.Walk s t => q.edges.toFinset) (p.take_spec hv)
      simpa only [SimpleGraph.Walk.edges_append, List.toFinset_append] using he.symm
    rw [heq]
    exact (incidentEdges_union_card_le _ _ v).trans (by omega)
  · rw [incidentEdges_walk_eq_empty_of_not_mem G p hv]
    simp

lemma deleted_boundary_card_le_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (B : Finset V) (F : Finset (Sym2 V)) :
    ((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card ≤
      ∑ v ∈ B, (incidentEdges F v).card := by
  let T := B.biUnion (fun v => ({v} : Finset V) ×ˢ incidentEdges F v)
  have hc : ((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun e : V × V => (e.1, s(e.1, e.2)))
    · intro e he
      obtain ⟨heP, heF⟩ := Finset.mem_filter.mp he
      apply Finset.mem_biUnion.mpr
      refine ⟨e.1, (P.mem_interedges_iff.mp heP).1, Finset.mem_product.mpr ⟨by simp, ?_⟩⟩
      exact Finset.mem_filter.mpr ⟨heF, by simp⟩
    · intro e he f hf heq
      have hsym := congrArg Prod.snd heq
      exact boundary_sym2_injective P B (Finset.mem_filter.mp he).1
        (Finset.mem_filter.mp hf).1 hsym
  have hT : T.card ≤ ∑ v ∈ B, (incidentEdges F v).card := by
    simpa [T] using Finset.card_biUnion_le (s := B)
      (t := fun v => ({v} : Finset V) ×ˢ incidentEdges F v)
  exact hc.trans hT

lemma walkBall_growth_of_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h) (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (W : Finset V) (s : V) (hs : s ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) (t : ℕ)
    (hsmall : ((walkBall (avoidGraph P F W) s t).card : ℝ) ≤ (Fintype.card V : ℝ) / 2) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (walkBall (avoidGraph P F W) s t).card ≤
      ((walkBall (avoidGraph P F W) s (t + 1)).card : ℝ) := by
  classical
  apply routing_union_growth_step_of_boundary P h hexp hr F _ _ (fun _ => W)
      (walkBall_mono _ s (Nat.le_succ t)) hsmall
  · calc
      _ ≤ ∑ v ∈ walkBall (avoidGraph P F W) s t, ((incidentEdges F v).card : ℝ) := by
        exact_mod_cast deleted_boundary_card_le_incidents P (walkBall (avoidGraph P F W) s t) F
      _ ≤ ∑ _v ∈ walkBall (avoidGraph P F W) s t, h / 4 := Finset.sum_le_sum (fun v _ => hF v)
      _ = _ := by simp; ring
  · exact fun _ _ => hW
  · intro v hv w _ hadj hdel hw
    have hnv := Finset.disjoint_left.mp (ball_avoids P F W s hs t) hv
    exact walkBall_step _ s v w t hv ⟨hadj, hdel, hnv, hw⟩

lemma walkBall_large_of_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s : V) (hs : s ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    (Fintype.card V : ℝ) / 2 <
      (walkBall (avoidGraph P F W) s (routingG (Fintype.card V) h)).card := by
  have hrR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < Fintype.card V := by linarith
  let g := routingG (Fintype.card V) h
  let c : ℝ := 1 + h / (2 * (Fintype.card V : ℝ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  by_contra hnot
  have hend := le_of_not_gt hnot
  have hpow : ∀ j ≤ g, c ^ j ≤ (walkBall (avoidGraph P F W) s j).card := by
    intro j
    induction j with
    | zero =>
      intro _
      have H := Finset.card_pos.mpr ⟨s, root_mem_walkBall (avoidGraph P F W) s 0⟩
      have H' : 1 ≤ (walkBall (avoidGraph P F W) s 0).card := H
      simpa using (Nat.cast_le (α := ℝ)).mpr H'
    | succ j ih =>
      intro hj
      have hmono : ((walkBall (avoidGraph P F W) s j).card : ℝ) ≤
          (walkBall (avoidGraph P F W) s g).card := by
        exact_mod_cast Finset.card_le_card (walkBall_mono (avoidGraph P F W) s (by omega : j ≤ g))
      have hsmall := hmono.trans hend
      calc
        c ^ (j + 1) = c * c ^ j := by rw [pow_succ]; ring
        _ ≤ c * (walkBall (avoidGraph P F W) s j).card := mul_le_mul_of_nonneg_left (ih (by omega)) hc
        _ ≤ (walkBall (avoidGraph P F W) s (j + 1)).card :=
          walkBall_growth_of_incidents P h hexp hr0 F W s hs hF hW j hsmall
  have hg := routingG_growth (Fintype.card V) h (by linarith) hh (hexp.le_order P h hr)
  exact (not_lt_of_ge ((hpow g le_rfl).trans hend)) hg

lemma exists_short_avoiding_path (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s t : V) (hs : s ∉ W) (ht : t ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    ∃ q : (avoidGraph P F W).Walk s t, q.IsPath ∧
      q.length ≤ 2 * routingG (Fintype.card V) h := by
  classical
  let g := routingG (Fintype.card V) h
  let B₁ := walkBall (avoidGraph P F W) s g
  let B₂ := walkBall (avoidGraph P F W) t g
  have h₁ := walkBall_large_of_incidents P h hh hexp hr F W s hs hF hW
  have h₂ := walkBall_large_of_incidents P h hh hexp hr F W t ht hF hW
  have hmeet : (B₁ ∩ B₂).Nonempty := by
    apply Finset.card_pos.mp
    have hc := Finset.card_union_add_card_inter B₁ B₂
    have hu := Finset.card_le_univ (B₁ ∪ B₂)
    have hsum : (Fintype.card V : ℝ) < (B₁.card : ℝ) + (B₂.card : ℝ) := by
      dsimp [B₁, B₂, g]; linarith
    have hsumN : Fintype.card V < B₁.card + B₂.card := by exact_mod_cast hsum
    omega
  obtain ⟨v, hv⟩ := hmeet
  obtain ⟨p₁, hp₁⟩ := (mem_walkBall _ s v g).mp (Finset.mem_inter.mp hv).1
  obtain ⟨p₂, hp₂⟩ := (mem_walkBall _ t v g).mp (Finset.mem_inter.mp hv).2
  let w := p₁.append p₂.reverse
  refine ⟨w.bypass, w.bypass_isPath, w.length_bypass_le_length.trans ?_⟩
  dsimp [w]
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

lemma two_routingG_le_length (r h : ℝ) : 2 * routingG r h ≤ routingLength r h := by
  dsimp [routingLength]
  exact Nat.le_mul_of_pos_right _ (by omega)

lemma routingLength_bounds (r h : ℝ) (hr : 1 ≤ r) (hh : 0 < h) :
    1 ≤ routingLength r h ∧ r ≤ (routingLength r h : ℝ) * h := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 1 ≤ Real.logb 2 (2 * r) := by
    rw [Real.logb]
    apply (le_div_iff₀ hl2).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 * r)
  have hg : 8 * (r / h) * Real.logb 2 (2 * r) ≤ (routingG r h : ℝ) := Nat.le_ceil _
  have hgh : 8 * r ≤ (routingG r h : ℝ) * h := by
    calc
      8 * r = (8 * (r / h)) * h := by field_simp
      _ ≤ (8 * (r / h) * Real.logb 2 (2 * r)) * h := by
        apply mul_le_mul_of_nonneg_right _ hh.le
        simpa using mul_le_mul_of_nonneg_left hlog (show 0 ≤ 8 * (r / h) by positivity)
      _ ≤ (routingG r h : ℝ) * h := mul_le_mul_of_nonneg_right hg hh.le
  have hgpos : 0 < routingG r h := by
    have hgR : (0 : ℝ) < routingG r h := by nlinarith
    exact_mod_cast hgR
  have hgle : routingG r h ≤ routingLength r h := (by omega : routingG r h ≤ 2 * routingG r h).trans (two_routingG_le_length r h)
  refine ⟨by omega, ?_⟩
  have hgleR : (routingG r h : ℝ) ≤ routingLength r h := by exact_mod_cast hgle
  nlinarith

lemma routing_budget (L k b z h r : ℝ) (hL : 1 ≤ L) (hk : 1 ≤ k)
    (hb : 1 ≤ b) (hz : 0 ≤ z) (hh : 0 < h) (_hr : 0 ≤ r)
    (hreach : r ≤ L * h) (hbudget : 64 * (L ^ 2 * (k + b) + z) ≤ h) :
    h / 8 + 2 + k ≤ h / 4 ∧ z + b * L ≤ h / 8 ∧ 64 * L * k * r ≤ h ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hLs : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hLLs : L ≤ L ^ 2 := by nlinarith
  have hbig : 64 * (k + b) ≤ h := by
    calc
      _ ≤ 64 * (L ^ 2 * (k + b) + z) := by nlinarith [mul_le_mul_of_nonneg_right hLs (by linarith : 0 ≤ k + b)]
      _ ≤ _ := hbudget
  have hbL : 64 * (b * L + z) ≤ h := by
    calc
      _ ≤ 64 * (L ^ 2 * (k + b) + z) := by nlinarith [mul_le_mul_of_nonneg_left hLLs hb0, mul_nonneg (sq_nonneg L) hk0]
      _ ≤ _ := hbudget
  have hkL : 64 * L ^ 2 * k ≤ h := by nlinarith [mul_nonneg (sq_nonneg L) hb0]
  refine ⟨by linarith, by linarith, ?_⟩
  calc
    64 * L * k * r ≤ 64 * L * k * (L * h) := mul_le_mul_of_nonneg_left hreach (by positivity)
    _ = (64 * L ^ 2 * k) * h := by ring
    _ ≤ h * h := mul_le_mul_of_nonneg_right hkL hh.le
    _ = h ^ 2 := by ring

noncomputable def saturated (F : Finset (Sym2 V)) (h : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => h / 8 ≤ ((incidentEdges F v).card : ℝ))

lemma saturated_card_le (F : Finset (Sym2 V)) (h : ℝ) (hh : 0 < h)
    (hF : 128 * (F.card : ℝ) ≤ h ^ 2) : (saturated F h).card ≤ h / 8 := by
  classical
  have hs : h / 8 * (saturated F h).card ≤ ∑ v : V, ((incidentEdges F v).card : ℝ) := by
    calc
      _ = ∑ _v ∈ saturated F h, h / 8 := by simp [mul_comm]
      _ ≤ ∑ v ∈ saturated F h, ((incidentEdges F v).card : ℝ) := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  have hsum : (∑ v : V, ((incidentEdges F v).card : ℝ)) ≤ 2 * (F.card : ℝ) := by
    exact_mod_cast incidentEdges_sum_le F
  nlinarith

def pathInterior {P : SimpleGraph V} {s t : V} (q : P.Walk s t) : Finset V :=
  q.support.toFinset \ {s, t}

lemma pathInterior_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : SimpleGraph V} {s t : V} (q : P.Walk s t) :
    (pathInterior q).card ≤ q.length := by
  have hp := List.toFinset_card_le q.support
  rw [q.length_support] at hp
  have hstart : s ∈ q.support.toFinset ∩ ({s, t} : Finset V) := by simp
  have hint := Finset.card_pos.mpr ⟨s, hstart⟩
  have hd := Finset.card_sdiff_add_card_inter q.support.toFinset ({s, t} : Finset V)
  dsimp [pathInterior]
  omega

lemma avoidGraph_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V) :
    avoidGraph P F W ≤ P := fun _ _ h => h.1

lemma walk_avoids_support (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s t : V} (q : (avoidGraph P F W).Walk s t) (hs : s ∉ W) :
    Disjoint q.support.toFinset W := by
  apply Finset.disjoint_left.mpr
  intro v hv
  exact walk_avoids_end P F W (q.takeUntil v (List.mem_toFinset.mp hv)) hs

lemma walk_avoids_edges {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s t : V} (q : (avoidGraph P F W).Walk s t) :
    Disjoint q.edges.toFinset F := by
  apply Finset.disjoint_left.mpr
  intro e he
  induction e using Sym2.inductionOn with
  | hf v w => exact (q.adj_of_mem_edges (List.mem_toFinset.mp he)).2.1

lemma exists_short_path_with_avoidance (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s t : V) (hs : s ∉ W) (ht : t ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    ∃ q : P.Walk s t, q.IsPath ∧ q.length ≤ routingLength (Fintype.card V) h ∧
      Disjoint q.edges.toFinset F ∧ Disjoint q.support.toFinset W := by
  obtain ⟨q, hp, hl⟩ := exists_short_avoiding_path P h hh hexp hr F W s t hs ht hF hW
  refine ⟨q.mapLe (avoidGraph_le P F W), hp.mapLe _, ?_, ?_, ?_⟩
  · simpa using hl.trans (two_routingG_le_length (Fintype.card V) h)
  · simpa using walk_avoids_edges P F W q
  · simpa using walk_avoids_support P F W q hs

lemma route_degree_update {P : SimpleGraph V} {s t : V} (q : P.Walk s t)
    (hp : q.IsPath) (F : Finset (Sym2 V)) (h : ℝ) (load : V → ℕ)
    (hdegree : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 8 + 2 + load v)
    (havoid : Disjoint q.support.toFinset (saturated F h \ {s, t})) (v : V) :
    ((incidentEdges (F ∪ q.edges.toFinset) v).card : ℝ) ≤
      h / 8 + 2 + load v + (if v = s ∨ v = t then 1 else 0) := by
  classical
  have hadd : ((incidentEdges (F ∪ q.edges.toFinset) v).card : ℝ) ≤
      (incidentEdges F v).card + (incidentEdges q.edges.toFinset v).card := by
    exact_mod_cast incidentEdges_union_card_le F q.edges.toFinset v
  by_cases hv : v = s ∨ v = t
  · rw [ite_eq_left hv]
    have hqN : (incidentEdges q.edges.toFinset v).card ≤ 1 := by
      rcases hv with rfl | rfl
      · exact incidentEdges_path_start_le_one P q hp
      · exact incidentEdges_path_end_le_one P q hp
    have hq : ((incidentEdges q.edges.toFinset v).card : ℝ) ≤ 1 := by exact_mod_cast hqN
    linarith [hdegree v]
  · rw [ite_eq_right hv]
    by_cases hmem : v ∈ q.support
    · have hns : v ∉ saturated F h := by
        intro hsat
        apply Finset.disjoint_left.mp havoid (List.mem_toFinset.mpr hmem)
        exact Finset.mem_sdiff.mpr ⟨hsat, by simpa using hv⟩
      have hsmall : ((incidentEdges F v).card : ℝ) < h / 8 := by
        simpa [saturated] using hns
      have hq : ((incidentEdges q.edges.toFinset v).card : ℝ) ≤ 2 := by
        exact_mod_cast incidentEdges_path_le_two P q hp v
      have : (0 : ℝ) ≤ load v := by positivity
      linarith
    · rw [incidentEdges_walk_eq_empty_of_not_mem P q hmem] at hadd
      simp only [Finset.card_empty, Nat.cast_zero, add_zero] at hadd
      linarith [hdegree v]

section Families
variable {I T : Type} [Fintype I] [DecidableEq I] [DecidableEq T]
variable {P : SimpleGraph V} {x y : I → V}

def endpointLoad (A : Finset I) (x y : I → V) (v : V) : ℕ :=
  (A.filter (fun i => x i = v ∨ y i = v)).card

lemma endpointLoad_mono {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {A B : Finset I} (hAB : A ⊆ B) (x y : I → V) (v : V) :
    endpointLoad A x y v ≤ endpointLoad B x y v :=
  Finset.card_le_card (Finset.filter_subset_filter _ hAB)

lemma endpointLoad_insert {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] (A : Finset I) (i : I) (hi : i ∉ A) (x y : I → V) (v : V) :
    endpointLoad (insert i A) x y v = endpointLoad A x y v +
      (if v = x i ∨ v = y i then 1 else 0) := by
  classical
  by_cases hv : v = x i ∨ v = y i
  · have hv' : x i = v ∨ y i = v := by simpa [eq_comm] using hv
    simp [endpointLoad, Finset.filter_insert, hv, hv', hi]
  · have hv' : ¬ (x i = v ∨ y i = v) := by simpa [eq_comm] using hv
    simp [endpointLoad, Finset.filter_insert, hv, hv']

lemma endpointLoad_sum {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] (A : Finset I) (x y : I → V) (hxy : ∀ i ∈ A, x i ≠ y i) :
    ∑ v : V, endpointLoad A x y v = 2 * A.card := by
  classical
  simp only [endpointLoad, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have heq : ∀ i ∈ A, (∑ v : V, if x i = v ∨ y i = v then 1 else 0) = 2 := by
    intro i hi
    have hf : (Finset.univ.filter fun v => x i = v ∨ y i = v) = ({x i, y i} : Finset V) := by
      ext v
      simp [eq_comm]
    have hc : ({x i, y i} : Finset V).card = 2 := by simp [hxy i hi]
    rw [← hc, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    _ = ∑ _i ∈ A, 2 := Finset.sum_congr rfl heq
    _ = _ := by simp [mul_comm]

noncomputable def usedEdges (A : Finset I) (q : ∀ i, P.Walk (x i) (y i)) : Finset (Sym2 V) :=
  A.biUnion (fun i => (q i).edges.toFinset)

lemma usedEdges_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (q : ∀ i, P.Walk (x i) (y i)) (L : ℕ)
    (hq : ∀ i ∈ A, (q i).length ≤ L) : (usedEdges A q).card ≤ L * A.card := by
  calc
    _ ≤ ∑ i ∈ A, (q i).edges.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A, L := Finset.sum_le_sum (fun i hi => by
      have hc := List.toFinset_card_le (q i).edges
      simpa using hc.trans (by simpa using hq i hi))
    _ = _ := by simp [mul_comm]

lemma usedEdges_update_insert {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (i : I) (hi : i ∉ A)
    (q : ∀ j, P.Walk (x j) (y j)) (p : P.Walk (x i) (y i)) :
    usedEdges (insert i A) (Function.update q i p) = usedEdges A q ∪ p.edges.toFinset := by
  classical
  rw [usedEdges, Finset.biUnion_insert]
  simp only [Function.update_self]
  rw [Finset.union_comm]
  congr 1
  apply Finset.biUnion_congr rfl
  intro j hj
  have hji : j ≠ i := by intro h; exact hi (h ▸ hj)
  rw [Function.update_of_ne hji]

noncomputable def teamInterior (A : Finset I) (q : ∀ j, P.Walk (x j) (y j))
    (team : I → T) (i : I) : Finset V :=
  (A.filter (fun j => team j = team i)).biUnion (fun j => pathInterior (q j))

lemma teamInterior_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} {T : Type} [_contextInstance5 : Fintype I] [_contextInstance6 : DecidableEq I] [_contextInstance7 : DecidableEq T] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (q : ∀ j, P.Walk (x j) (y j))
    (team : I → T) (i : I) (L : ℕ) (b : ℝ)
    (hq : ∀ j ∈ A, (q j).length ≤ L)
    (hb : ((Finset.univ.filter (fun j => team j = team i)).card : ℝ) ≤ b) :
    ((teamInterior A q team i).card : ℝ) ≤ b * L := by
  have hc : (teamInterior A q team i).card ≤ L * (A.filter (fun j => team j = team i)).card := by
    calc
      _ ≤ ∑ j ∈ A.filter (fun j => team j = team i), (pathInterior (q j)).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ A.filter (fun j => team j = team i), L := Finset.sum_le_sum (fun j hj =>
        (pathInterior_card_le (q j)).trans (hq j (Finset.mem_filter.mp hj).1))
      _ = _ := by simp [mul_comm]
  have hcard : ((A.filter (fun j => team j = team i)).card : ℝ) ≤ b := by
    apply le_trans _ hb
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ A))
  have hcR : ((teamInterior A q team i).card : ℝ) ≤ (L : ℝ) * (A.filter (fun j => team j = team i)).card := by exact_mod_cast hc
  calc
    _ ≤ (L : ℝ) * b := hcR.trans (mul_le_mul_of_nonneg_left hcard (by positivity))
    _ = _ := mul_comm _ _

structure PartialRoutes (P : SimpleGraph V) (x y : I → V) (team : I → T)
    (Z : I → Finset V) (L : ℕ) (h : ℝ) (A : Finset I)
    (q : ∀ i, P.Walk (x i) (y i)) : Prop where
  simple : ∀ i ∈ A, (q i).IsPath
  short : ∀ i ∈ A, (q i).length ≤ L
  avoids : ∀ i ∈ A, Disjoint (pathInterior (q i)) (Z i)
  edge_disjoint : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (q i).edges.toFinset (q j).edges.toFinset
  team_disjoint : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))
  degree : ∀ v, ((incidentEdges (usedEdges A q) v).card : ℝ) ≤ h / 8 + 2 + endpointLoad A x y v

theorem routing (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (x y : I → V) (hxy : ∀ i, x i ≠ y i) (team : I → T) (Z : I → Finset V)
    (k b z : ℝ) (hk : 1 ≤ k) (hb : 1 ≤ b) (hz : 0 ≤ z)
    (hload : ∀ v, (endpointLoad Finset.univ x y v : ℝ) ≤ k)
    (hteam : ∀ i, ((Finset.univ.filter (fun j => team j = team i)).card : ℝ) ≤ b)
    (hZ : ∀ i, ((Z i).card : ℝ) ≤ z)
    (hbudget : 64 * ((routingLength (Fintype.card V) h : ℝ) ^ 2 * (k + b) + z) ≤ h) :
    ∃ q : ∀ i, P.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength (Fintype.card V) h ∧
        Disjoint (pathInterior (q i)) (Z i)) ∧
      (∀ i j, i ≠ j → Disjoint (q i).edges.toFinset (q j).edges.toFinset) ∧
      (∀ i j, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
  classical
  let L := routingLength (Fintype.card V) h
  have hrR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hr
  obtain ⟨hL, hreach⟩ := routingLength_bounds (Fintype.card V) h (by linarith) hh
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨hdegBudget, hforbidBudget, hnumBudget⟩ := routing_budget L k b z h (Fintype.card V)
    hLR hk hb hz hh (by positivity) hreach hbudget
  have hloadA : ∀ (A : Finset I) v, (endpointLoad A x y v : ℝ) ≤ k := by
    intro A v
    have hm : (endpointLoad A x y v : ℝ) ≤ endpointLoad Finset.univ x y v := by
      exact_mod_cast endpointLoad_mono (Finset.subset_univ A) x y v
    exact hm.trans (hload v)
  have htotal : 2 * (Fintype.card I : ℝ) ≤ k * Fintype.card V := by
    have heq := endpointLoad_sum Finset.univ x y (fun i _ => hxy i)
    have heqR : (∑ v : V, (endpointLoad Finset.univ x y v : ℝ)) = 2 * Fintype.card I := by
      exact_mod_cast heq
    rw [← heqR]
    calc
      _ ≤ ∑ _v : V, k := Finset.sum_le_sum (fun v _ => hload v)
      _ = _ := by simp [mul_comm]
  have hdefault : ∀ i, ∃ p : P.Walk (x i) (y i), p.IsPath := by
    intro i
    obtain ⟨p, hp, _⟩ := exists_short_path_with_avoidance P h hh hexp hr ∅ ∅ (x i) (y i)
      (by simp) (by simp) (by intro v; simp [incidentEdges]; positivity) (by simp; positivity)
    exact ⟨p, hp⟩
  choose defaultPath hdefaultPath using hdefault
  have hpartial : ∀ A : Finset I, ∃ q : ∀ i, P.Walk (x i) (y i), PartialRoutes P x y team Z L h A q := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      refine ⟨defaultPath, ?_⟩
      constructor
      · simp
      · simp
      · simp
      · simp
      · simp
      · intro v
        simp only [usedEdges, Finset.biUnion_empty, incidentEdges, Finset.filter_empty,
          Finset.card_empty, Nat.cast_zero, endpointLoad, add_zero]
        linarith
    | @insert i A hi ih =>
      obtain ⟨q, hq⟩ := ih
      let F := usedEdges A q
      let S := saturated F h
      let B := teamInterior A q team i
      let W := (S ∪ Z i ∪ B) \ {x i, y i}
      have hFcard : 128 * (F.card : ℝ) ≤ h ^ 2 := by
        have hc : (F.card : ℝ) ≤ (L : ℝ) * A.card := by
          exact_mod_cast usedEdges_card_le A q L hq.short
        have ha : (A.card : ℝ) ≤ Fintype.card I := by exact_mod_cast Finset.card_le_univ A
        have hsize : 2 * (A.card : ℝ) ≤ k * Fintype.card V := by linarith
        have hmult := mul_le_mul_of_nonneg_left hsize (show 0 ≤ (L : ℝ) by positivity)
        nlinarith [hnumBudget]
      have hS : (S.card : ℝ) ≤ h / 8 := saturated_card_le F h hh hFcard
      have hB : (B.card : ℝ) ≤ b * L := teamInterior_card_le A q team i L b hq.short (hteam i)
      have hW : (W.card : ℝ) ≤ h / 4 := by
        have hc : W.card ≤ S.card + (Z i).card + B.card :=
          (Finset.card_le_card Finset.sdiff_subset).trans ((Finset.card_union_le _ _).trans
            (Nat.add_le_add_right (Finset.card_union_le _ _) _))
        have hcR : (W.card : ℝ) ≤ (S.card : ℝ) + (Z i).card + B.card := by exact_mod_cast hc
        linarith [hZ i]
      have hFdegree : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4 := by
        intro v
        have hd := hq.degree v
        have hl := hloadA A v
        dsimp [F]
        linarith
      obtain ⟨p, hp, hpL, hpF, hpW⟩ := exists_short_path_with_avoidance P h hh hexp hr F W (x i) (y i)
        (by simp [W]) (by simp [W]) hFdegree hW
      have hpZ : Disjoint (pathInterior p) (Z i) := by
        apply Finset.disjoint_left.mpr
        intro v hv hvZ
        obtain ⟨hvp, hvends⟩ := Finset.mem_sdiff.mp hv
        apply Finset.disjoint_left.mp hpW hvp
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hvZ), hvends⟩
      have hpS : Disjoint p.support.toFinset (saturated F h \ {x i, y i}) := by
        apply Finset.disjoint_left.mpr
        intro v hv hvS
        obtain ⟨hs, he⟩ := Finset.mem_sdiff.mp hvS
        apply Finset.disjoint_left.mp hpW hv
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hs), he⟩
      have hpEdge : ∀ j ∈ A, Disjoint p.edges.toFinset (q j).edges.toFinset := by
        intro j hj
        apply Finset.disjoint_left.mpr
        intro e hep heq
        exact Finset.disjoint_left.mp hpF hep (Finset.mem_biUnion.mpr ⟨j, hj, heq⟩)
      have hpTeam : ∀ j ∈ A, team i = team j → Disjoint (pathInterior p) (pathInterior (q j)) := by
        intro j hj htm
        apply Finset.disjoint_left.mpr
        intro v hvp hvq
        obtain ⟨hvp', hvends⟩ := Finset.mem_sdiff.mp hvp
        apply Finset.disjoint_left.mp hpW hvp'
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_union_right _ ?_, hvends⟩
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, htm.symm⟩, hvq⟩
      let q' := Function.update q i p
      have hsame : q' i = p := Function.update_self i p q
      have hother : ∀ j ∈ A, q' j = q j := by
        intro j hj
        apply Function.update_of_ne
        intro hji
        exact hi (hji ▸ hj)
      refine ⟨q', ?_⟩
      constructor
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hp
        · simpa only [hother j hj] using hq.simple j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hpL
        · simpa only [hother j hj] using hq.short j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hpZ
        · simpa only [hother j hj] using hq.avoids j hj
      · intro j hj k hk hjk
        rcases Finset.mem_insert.mp hj with rfl | hjA
        · have hkA : k ∈ A := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
          simpa only [hsame, hother k hkA] using hpEdge k hkA
        · rcases Finset.mem_insert.mp hk with rfl | hkA
          · simpa only [hsame, hother j hjA] using (hpEdge j hjA).symm
          · simpa only [hother j hjA, hother k hkA] using hq.edge_disjoint j hjA k hkA hjk
      · intro j hj k hk hjk htm
        rcases Finset.mem_insert.mp hj with rfl | hjA
        · have hkA : k ∈ A := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
          simpa only [hsame, hother k hkA] using hpTeam k hkA htm
        · rcases Finset.mem_insert.mp hk with rfl | hkA
          · simpa only [hsame, hother j hjA] using (hpTeam j hjA htm.symm).symm
          · simpa only [hother j hjA, hother k hkA] using hq.team_disjoint j hjA k hkA hjk htm
      · intro v
        have heq : usedEdges (insert i A) q' = F ∪ p.edges.toFinset := usedEdges_update_insert A i hi q p
        rw [heq]
        have hu := route_degree_update p hp F h (endpointLoad A x y) hq.degree hpS v
        have hloadEq : (endpointLoad (insert i A) x y v : ℝ) =
            endpointLoad A x y v + (if v = x i ∨ v = y i then (1 : ℝ) else 0) := by
          rw [endpointLoad_insert A i hi]
          split_ifs <;> simp
        rw [hloadEq]
        simpa only [add_assoc] using hu
  obtain ⟨q, hq⟩ := hpartial Finset.univ
  exact ⟨q, fun i => ⟨hq.simple i (by simp), hq.short i (by simp), hq.avoids i (by simp)⟩,
    fun i j hij => hq.edge_disjoint i (by simp) j (by simp) hij,
    fun i j hij htm => hq.team_disjoint i (by simp) j (by simp) hij htm⟩

end Families
end ErdosGallai.Batch

end
end

/-! ### Upstream module `Combinatorics/CycleDecomposition/CycleLifting.lean` -/

section
open _root_.Filter _root_.Asymptotics _root_.Real
noncomputable section
open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Finset
namespace ErdosGallai.Batch
noncomputable section
lemma routing_length_upper (r h : ℝ) (hr : 2 ≤ r) (hh : 0 < h) (hhr : h ≤ r) :
    (routingLength r h : ℝ) ≤ 108*(r/h)*(logb 2 r)^2 := by
  have hr0 : 0 < r := by linarith
  have hl : 1 ≤ logb 2 r := by
    simpa using Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
      (by norm_num : (0:ℝ) < 2) hr
  have hR : 1 ≤ r/h := (le_div_iff₀ hh).mpr (by simpa using hhr)
  have hlog : logb 2 (2*r) = 1 + logb 2 r := by
    rw [Real.logb_mul (by norm_num) hr0.ne']
    norm_num
  have hg := Nat.ceil_lt_add_one (show 0 ≤ 8*(r/h)*logb 2 (2*r) by rw [hlog]; positivity)
  have hd := Nat.ceil_lt_add_one (show 0 ≤ logb 2 r by linarith)
  change (routingG r h : ℝ) < 8*(r/h)*logb 2 (2*r)+1 at hg
  change (routingDepth r : ℝ) < logb 2 r + 1 at hd
  rw [hlog] at hg
  have hprod : 1 ≤ (r/h)*logb 2 r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hl)]
  have hg' : (routingG r h : ℝ) ≤ 18*(r/h)*logb 2 r := by nlinarith
  have hd' : (1 + routingDepth r : ℝ) ≤ 3*logb 2 r := by linarith
  have hm := mul_le_mul hg' hd' (by positivity) (by positivity)
  dsimp [routingLength]
  push_cast
  nlinarith

lemma eventually_logb_le_power (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, logb 2 D ≤ D^ε := by
  have ho := (isLittleO_log_rpow_atTop hε).const_mul_left (1 / log 2)
  filter_upwards [ho.eventuallyLE, eventually_ge_atTop (1:ℝ)] with D hD h1
  simpa [Real.logb, div_eq_mul_inv, mul_comm, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg h1), abs_of_nonneg (Real.rpow_nonneg (by linarith) ε),
    abs_of_pos (show 0 < (log 2)⁻¹ by positivity),
    abs_of_pos (Real.log_pos (by norm_num : (1:ℝ) < 2))] using hD

lemma eventually_constant_le_power (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, C ≤ D^ε :=
  (tendsto_rpow_atTop hε).eventually (eventually_ge_atTop C)

lemma eventually_const_mul_power_le (C α β : ℝ) (hab : α < β) :
    ∀ᶠ D : ℝ in atTop, C*D^α ≤ D^β := by
  filter_upwards [eventually_constant_le_power C (β-α) (by linarith),
    eventually_gt_atTop (0:ℝ)] with D hc hD
  calc
    C*D^α ≤ D^(β-α)*D^α := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hD.le _)
    _ = D^β := by rw [← Real.rpow_add hD]; congr 1; ring

theorem eventually_routing_length (c β γ δ : ℝ) (hc : 0 < c) (hβ : 0 < β)
    (hδ : 0 < δ) :
    ∀ᶠ D : ℝ in atTop, ∀ r : ℝ, 2 ≤ r → r ≤ D^β → c*D^γ ≤ r →
      (routingLength r (c*D^γ) : ℝ) ≤ D^(β-γ+δ) := by
  filter_upwards [eventually_logb_le_power (δ/4) (by positivity),
    eventually_constant_le_power (108*β^2/c) (δ/2) (by positivity),
    eventually_gt_atTop (1:ℝ)] with D hlog hconst hD r hr hrD hhr
  have hD0 : 0 < D := by linarith
  have hpowγ : 0 < D^γ := Real.rpow_pos_of_pos hD0 _
  have hden : 0 < c*D^γ := mul_pos hc hpowγ
  have hlog0 : 0 ≤ logb 2 r := (Real.logb_pos (by norm_num) (by linarith)).le
  have hlogR : logb 2 r ≤ β*D^(δ/4) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
      (by linarith : 0 < r) hrD
    rw [Real.logb_rpow_eq_mul_logb_of_pos hD0] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlog hβ.le)
  have hratio : r/(c*D^γ) ≤ D^(β-γ)/c := by
    calc
      _ ≤ D^β/(c*D^γ) := div_le_div_of_nonneg_right hrD hden.le
      _ = _ := by rw [Real.rpow_sub hD0]; ring
  have hsq : (logb 2 r)^2 ≤ β^2*D^(δ/2) := by
    calc
      _ ≤ (β*D^(δ/4))^2 := pow_le_pow_left₀ hlog0 hlogR 2
      _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hD0.le]; congr 2; ring
  calc
    (routingLength r (c*D^γ) : ℝ) ≤ 108*(r/(c*D^γ))*(logb 2 r)^2 :=
      routing_length_upper r (c*D^γ) hr hden hhr
    _ ≤ 108*(D^(β-γ)/c)*(β^2*D^(δ/2)) := by gcongr
    _ = (108*β^2/c)*D^(β-γ+δ/2) := by rw [Real.rpow_add hD0]; ring
    _ ≤ D^(δ/2)*D^(β-γ+δ/2) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hD0.le _)
    _ = D^(β-γ+δ) := by rw [← Real.rpow_add hD0]; congr 1; ring

theorem batch_routing_margin : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
    ∀ r : ℝ, D^(9/10:ℝ) ≤ r → r ≤ D^(51/50:ℝ) →
    2 ≤ r ∧ 64*((routingLength r (D^(9/10:ℝ)/4) : ℝ)^2*
      (D^(1/100:ℝ)+D^(3/10:ℝ))+2*D^(3/10:ℝ)) ≤ D^(9/10:ℝ)/4 := by
  have hev : ∀ᶠ D : ℝ in atTop, ∀ r : ℝ, D^(9/10:ℝ) ≤ r → r ≤ D^(51/50:ℝ) →
      2 ≤ r ∧ 64*((routingLength r (D^(9/10:ℝ)/4) : ℝ)^2*
        (D^(1/100:ℝ)+D^(3/10:ℝ))+2*D^(3/10:ℝ)) ≤ D^(9/10:ℝ)/4 := by
    filter_upwards [eventually_routing_length (1/4) (51/50) (9/10) (2/25)
      (by norm_num) (by norm_num) (by norm_num),
      eventually_const_mul_power_le 1024 (7/10) (9/10) (by norm_num),
      eventually_constant_le_power 2 (9/10) (by norm_num),
      eventually_gt_atTop (1:ℝ)] with D hlen hcost htwo hD r hr hrD
    have hD0 : 0 < D := by linarith
    have hr2 : 2 ≤ r := htwo.trans hr
    have hh : (1/4)*D^(9/10:ℝ) ≤ r := by
      have hh0 := Real.rpow_nonneg hD0.le (9/10:ℝ)
      linarith
    have hL := hlen r hr2 hrD hh
    norm_num at hL
    have hL' : (routingLength r (D^(9/10:ℝ)/4) : ℝ) ≤ D^(1/5:ℝ) := by
      convert hL using 1 ; ring_nf
    have hsmall : D^(1/100:ℝ) ≤ D^(3/10:ℝ) := Real.rpow_le_rpow_of_exponent_le hD.le (by norm_num)
    have h37 : D^(3/10:ℝ) ≤ D^(7/10:ℝ) := Real.rpow_le_rpow_of_exponent_le hD.le (by norm_num)
    have hprod : (routingLength r (D^(9/10:ℝ)/4) : ℝ)^2*
        (D^(1/100:ℝ)+D^(3/10:ℝ)) ≤ 2*D^(7/10:ℝ) := by
      calc
        _ ≤ (D^(1/5:ℝ))^2 * (2*D^(3/10:ℝ)) := by gcongr; linarith
        _ = _ := by
          rw [← Real.rpow_mul_natCast hD0.le]
          norm_num
          rw [mul_left_comm, ← Real.rpow_add hD0]
          norm_num
    refine ⟨hr2, ?_⟩
    nlinarith only [hprod, h37, hcost]
  obtain ⟨A,hA⟩ := eventually_atTop.mp hev
  refine ⟨max A 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro D hD
  exact hA D ((le_max_left _ _).trans hD)

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

def CutExpansionOn (P : SimpleGraph V) [DecidableRel P.Adj] (W : Finset V) (h : ℝ) : Prop :=
  ∀ A : Finset V, A ⊆ W → h * min (A.card : ℝ) ((W \ A).card : ℝ) ≤
    ((P.interedges A (W \ A)).card : ℝ)

lemma subtype_image_compl {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (W : Finset V) (U : Finset (W : Set V)) :
    Uᶜ.image Subtype.val = W \ U.image Subtype.val := by
  ext v
  simp only [Finset.mem_image, Finset.mem_compl, Finset.mem_sdiff]
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.property,?_⟩
    rintro ⟨y,hy,he⟩
    exact hx (Subtype.ext he ▸ hy)
  · rintro ⟨hv,hvU⟩
    refine ⟨⟨v,hv⟩,?_,rfl⟩
    intro hx
    exact hvU ⟨⟨v,hv⟩,hx,rfl⟩

lemma induced_interedges_card (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) (U : Finset (W : Set V)) :
    (((P.induce (W : Set V)).interedges U Uᶜ).card : ℝ) =
      ((P.interedges (U.image Subtype.val) (W \ U.image Subtype.val)).card : ℝ) := by
  classical
  let f : ↥(W : Set V) × ↥(W : Set V) → V × V := fun e => (e.1.val,e.2.val)
  have hf : Function.Injective f := by
    intro a b h
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have heq : ((P.induce (W : Set V)).interedges U Uᶜ).image f =
      P.interedges (U.image Subtype.val) (W \ U.image Subtype.val) := by
    rw [← subtype_image_compl W U]
    ext e
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_image]
    constructor
    · rintro ⟨a,⟨ha,hb,hab⟩,rfl⟩
      exact ⟨⟨a.1,ha,rfl⟩,⟨a.2,hb,rfl⟩,hab⟩
    · rintro ⟨⟨x,hx,hxe⟩,⟨y,hy,hye⟩,he⟩
      refine ⟨(x,y),⟨hx,hy,?_⟩,Prod.ext hxe hye⟩
      change P.Adj x.val y.val
      simpa only [hxe,hye] using he
  rw [← heq, Finset.card_image_of_injective _ hf]

lemma cutExpansion_induce (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) (h : ℝ) (hexp : CutExpansionOn P W h) :
    CutExpansion (P.induce (W : Set V)) h := by
  classical
  intro U
  have hsub : U.image Subtype.val ⊆ W := by
    rintro v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    exact a.property
  have h := hexp (U.image Subtype.val) hsub
  have he : W \ U.image Subtype.val = Uᶜ.image Subtype.val :=
    (subtype_image_compl W U).symm
  rw [he] at h
  simp only [Finset.card_image_of_injective _ Subtype.val_injective] at h
  rw [induced_interedges_card,he]
  exact h

lemma pathInterior_map {A B : Type} [DecidableEq A] [DecidableEq B]
    {H : SimpleGraph A} {J : SimpleGraph B} (f : H →g J)
    (hf : Function.Injective f) {a b : A} (p : H.Walk a b) :
    pathInterior (p.map f) = (pathInterior p).image f := by
  classical
  simp only [pathInterior, SimpleGraph.Walk.support_map]
  rw [Finset.image_sdiff _ _ hf]
  have hm : (p.support.map f).toFinset = p.support.toFinset.image f := by
    ext v; simp
  rw [hm]
  simp

theorem team_routing_on_set {I T : Type} [Fintype I]
    (G P : SimpleGraph V) [DecidableRel P.Adj] (hPG : P ≤ G)
    (W : Finset V) (h : ℝ) (hh : 0 < h)
    (hexp : CutExpansionOn P W h) (hr : 2 ≤ W.card)
    (x y : I → V) (hx : ∀ i, x i ∈ W) (hy : ∀ i, y i ∈ W)
    (hxy : ∀ i, x i ≠ y i) (team : I → T) (Z : I → Finset V)
    (k b z : ℝ) (hk : 1 ≤ k) (hb : 1 ≤ b) (hz : 0 ≤ z)
    (hload : ∀ v, (endpointLoad univ x y v : ℝ) ≤ k)
    (hteam : ∀ i, ((univ.filter (fun j => team j = team i)).card : ℝ) ≤ b)
    (hZ : ∀ i, ((Z i).card : ℝ) ≤ z)
    (hbudget : 64 * ((routingLength W.card h : ℝ)^2 * (k+b) + z) ≤ h) :
    ∃ q : ∀ i, G.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card h ∧
        (∀ v ∈ (q i).support, v ∈ W) ∧ (q i).edgeSet ⊆ P.edgeSet ∧
        Disjoint (pathInterior (q i)) (Z i)) ∧
      Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
      (∀ i j, i ≠ j → team i = team j →
        Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
  classical
  let X : I → (W : Set V) := fun i => ⟨x i,hx i⟩
  let Y : I → (W : Set V) := fun i => ⟨y i,hy i⟩
  let Z' : I → Finset (W : Set V) := fun i => univ.filter (fun v => v.val ∈ Z i)
  have hl (v : (W : Set V)) : (endpointLoad univ X Y v : ℝ) ≤ k := by
    simpa only [endpointLoad,X,Y,Subtype.ext_iff] using hload v.val
  have hz' : ∀ i, ((Z' i).card : ℝ) ≤ z := by
    intro i
    apply le_trans _ (hZ i)
    have hc : (Z' i).card ≤ (Z i).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro v hv; exact (Finset.mem_filter.mp hv).2
      · exact Subtype.val_injective.injOn
    exact_mod_cast hc
  obtain ⟨q,hq,hd,ht⟩ := routing (P.induce (W : Set V)) h hh
    (cutExpansion_induce P W h hexp) (by simpa using hr) X Y
    (fun i he => hxy i (congrArg Subtype.val he)) team Z' k b z hk hb hz hl hteam hz'
    (by simpa using hbudget)
  let f : (P.induce (W : Set V)) →g G :=
    { toFun := Subtype.val, map_rel' := fun ha => hPG ha }
  have hf : Function.Injective f := Subtype.val_injective
  have hcard : Fintype.card ↥(W : Set V) = W.card := Fintype.card_coe W
  let Q : ∀ i, G.Walk (x i) (y i) := fun i => (q i).map f
  refine ⟨Q,?_,?_,?_⟩
  · intro i
    refine ⟨(hq i).1.map hf,?_,?_,?_,?_⟩
    · simpa only [Q,SimpleGraph.Walk.length_map,hcard] using (hq i).2.1
    · intro v hv
      have hv' : v ∈ (q i).support.map f := by simpa only [Q,SimpleGraph.Walk.support_map] using hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv'
      exact a.property
    · intro e he
      rw [SimpleGraph.Walk.edgeSet_map] at he
      obtain ⟨d,hd,rfl⟩ := he
      induction d using Sym2.ind with
      | _ a b => exact (q i).adj_of_mem_edges hd
    · rw [show Q i = (q i).map f from rfl, pathInterior_map f hf]
      apply Finset.disjoint_left.mpr
      intro v hv hzv
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.disjoint_left.mp (hq i).2.2 ha (by simpa [Z',f] using hzv)
  · intro i j hij
    change Disjoint ((q i).map f).edgeSet ((q j).map f).edgeSet
    rw [SimpleGraph.Walk.edgeSet_map,SimpleGraph.Walk.edgeSet_map,
      Set.disjoint_image_iff (Sym2.map.injective hf)]
    apply Set.disjoint_left.mpr
    intro e he he'
    exact Finset.disjoint_left.mp (hd i j hij) (by simpa using he) (by simpa using he')
  · intro i j hij hteam'
    change Disjoint (pathInterior ((q i).map f)) (pathInterior ((q j).map f))
    rw [pathInterior_map f hf,pathInterior_map f hf,Finset.disjoint_image hf]
    exact ht i j hij hteam'

theorem uniform_batch_routing :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (A : Type) [Fintype A] [DecidableEq A],
      ∀ (G P : SimpleGraph A) [DecidableRel P.Adj], P ≤ G →
      ∀ W : Finset A, CutExpansionOn P W (D^(9/10:ℝ)/4) →
      D^(9/10:ℝ) ≤ (W.card : ℝ) → (W.card : ℝ) ≤ D^(51/50:ℝ) →
      ∀ (I T : Type) [Fintype I] (x y : I → A),
      (∀ i, x i ∈ W) → (∀ i, y i ∈ W) → (∀ i, x i ≠ y i) →
      ∀ (team : I → T) (Z : I → Finset A),
      (∀ v, (endpointLoad univ x y v : ℝ) ≤ D^(1/100:ℝ)) →
      (∀ i, ((univ.filter (fun j => team j = team i)).card : ℝ) ≤ D^(3/10:ℝ)) →
      (∀ i, ((Z i).card : ℝ) ≤ 2*D^(3/10:ℝ)) →
      ∃ q : ∀ i, G.Walk (x i) (y i),
        (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card (D^(9/10:ℝ)/4) ∧
          (∀ v ∈ (q i).support, v ∈ W) ∧ (q i).edgeSet ⊆ P.edgeSet ∧
          Disjoint (pathInterior (q i)) (Z i)) ∧
        Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
        (∀ i j, i ≠ j → team i = team j →
          Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
  obtain ⟨D₀,hD₀,hm⟩ := batch_routing_margin
  refine ⟨D₀,hD₀,?_⟩
  intro D hD A _ _ G P _ hPG W hexp hr₁ hr₂ I T _ x y hx hy hxy team Z hl ht hZ
  have hD1 : 1 < D := hD₀.trans_le hD
  have hD0 : 0 < D := lt_trans zero_lt_one hD1
  obtain ⟨hr,hbudget⟩ := hm D hD W.card hr₁ hr₂
  apply team_routing_on_set G P hPG W _ (by positivity) hexp (by exact_mod_cast hr)
    x y hx hy hxy team Z _ _ _ _ _ (by positivity) hl ht hZ hbudget
  · exact Real.one_le_rpow hD1.le (by norm_num)
  · exact Real.one_le_rpow hD1.le (by norm_num)

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open _root_.SimpleGraph

variable {V : Type cycleUniverse1} {G : SimpleGraph V}

structure CycleVisit (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish

inductive VisitChain (G : SimpleGraph V) : V → V → Type _
  | single {u v : V} (p : G.Walk u v) : VisitChain G u v
  | cons {u v w z : V} (p : G.Walk u v) (h : G.Adj v w)
      (q : VisitChain G w z) : VisitChain G u z

namespace VisitChain

variable {u v : V}

def walk : {u v : V} → VisitChain G u v → G.Walk u v
  | _, _, .single p => p
  | _, _, .cons p h q => p.append (.cons h q.walk)

def visits : {u v : V} → VisitChain G u v → List (CycleVisit G)
  | u, v, .single p => [⟨u,v,p⟩]
  | u, _, .cons (v := v) p _ q => ⟨u,v,p⟩ :: q.visits

def links : {u v : V} → VisitChain G u v → Set (Sym2 V)
  | _, _, .single _ => ∅
  | _, _, .cons (v := v) (w := w) _ _ q => {s(v,w)} ∪ q.links

def switchEdges (q : VisitChain G u v) : Set (Sym2 V) :=
  ⋃ p ∈ q.visits, p.walk.edgeSet

lemma mem_support_iff (q : VisitChain G u v) (x : V) :
    x ∈ q.walk.support ↔ ∃ p ∈ q.visits, x ∈ p.walk.support := by
  induction q with
  | single p => simp [walk, visits]
  | cons p h q ih =>
    simp only [walk, Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons,
      ih, visits, List.mem_cons]
    constructor
    · rintro (hp | rfl | ⟨r,hr,hx⟩)
      · exact ⟨_, Or.inl rfl, hp⟩
      · exact ⟨_, Or.inl rfl, p.end_mem_support⟩
      · exact ⟨r, Or.inr hr, hx⟩
    · rintro ⟨r, rfl | hr, hx⟩
      · exact Or.inl hx
      · exact Or.inr (Or.inr ⟨r,hr,hx⟩)

lemma isPath_of_separated (q : VisitChain G u v)
    (hp : ∀ p ∈ q.visits, p.walk.IsPath)
    (hd : q.visits.Pairwise (fun p r => p.walk.support.Disjoint r.walk.support)) :
    q.walk.IsPath := by
  induction q with
  | single p => exact hp ⟨_,_,p⟩ (by simp [visits])
  | cons p h q ih =>
    have hpd := (List.pairwise_cons.mp hd).1
    have hqt := ih (fun r hr => hp r (by simp [visits, hr]))
      (List.pairwise_cons.mp hd).2
    have hpt := hp ⟨_,_,p⟩ (by simp [visits])
    have hdisj : p.support.Disjoint q.walk.support := by
      rw [List.disjoint_left]
      intro x hx hqx
      obtain ⟨r,hr,hxr⟩ := q.mem_support_iff x |>.mp hqx
      exact hpd r hr hx hxr
    apply Walk.IsPath.mk'
    simpa only [walk, Walk.support_append, Walk.support_cons, List.tail_cons]
      using (List.nodup_append').mpr ⟨hpt.support_nodup, hqt.support_nodup, hdisj⟩

lemma length_visits_le (q : VisitChain G u v) : q.visits.length ≤ q.walk.length + 1 := by
  induction q with
  | single p => simp [visits, walk]
  | cons p h q ih => simp only [visits, List.length_cons, walk, Walk.length_append,
      Walk.length_cons]; omega

lemma edgeSet_eq (q : VisitChain G u v) :
    q.walk.edgeSet = q.links ∪ q.switchEdges := by
  induction q with
  | single p => simp [walk, links, switchEdges, visits]
  | cons p h q ih =>
    simp only [walk, Walk.edgeSet_append, Walk.edgeSet_cons, ih, links,
      switchEdges, visits]
    ext e
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff,
      Set.mem_iUnion, List.mem_cons, exists_prop, or_and_right, exists_or, exists_eq_left]
    tauto

theorem close_cycle (q : VisitChain G u v) (hc : G.Adj v u)
    (hp : ∀ p ∈ q.visits, p.walk.IsPath)
    (hd : q.visits.Pairwise (fun p r => p.walk.support.Disjoint r.walk.support))
    (hn : 3 ≤ q.visits.length) :
    (Walk.cons hc q.walk).IsCycle ∧
    (Walk.cons hc q.walk).edgeSet = {s(v,u)} ∪ q.links ∪ q.switchEdges ∧
    3 ≤ (Walk.cons hc q.walk).length := by
  have hpath := q.isPath_of_separated hp hd
  have hlength := q.length_visits_le
  have he : s(v,u) ∉ q.walk.edges := by
    intro he
    have hh := hpath.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
    omega
  refine ⟨Path.cons_isCycle ⟨q.walk,hpath⟩ hc he, ?_, ?_⟩
  · rw [Walk.edgeSet_cons, q.edgeSet_eq]
    ext e
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · simp only [Walk.length_cons]
    omega

end VisitChain

namespace VisitChain
variable {W : Type cycleUniverse2} {Q : SimpleGraph W}

def of_walk (s t : W → V) (q : ∀ z, G.Walk (s z) (t z)) :
    {a b : W} → (p : Q.Walk a b) →
    (∀ d ∈ p.darts, G.Adj (t d.fst) (s d.snd)) → VisitChain G (s a) (t b)
  | _, _, .nil, _ => .single (q _)
  | a, b, .cons (v := c) h p, hr => .cons (q a)
      (hr ⟨(a,c),h⟩ (by simp))
      (of_walk s t q p (by intro d hd; exact hr d (by simp [hd])))

lemma of_walk_visits (s t : W → V) (q : ∀ z, G.Walk (s z) (t z))
    {a b : W} (p : Q.Walk a b)
    (hr : ∀ d ∈ p.darts, G.Adj (t d.fst) (s d.snd)) :
    (of_walk s t q p hr).visits = p.support.map (fun z => (⟨s z,t z,q z⟩ : CycleVisit G)) := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [of_walk, visits, ih]

lemma of_walk_links (s t : W → V) (q : ∀ z, G.Walk (s z) (t z))
    {a b : W} (p : Q.Walk a b)
    (hr : ∀ d ∈ p.darts, G.Adj (t d.fst) (s d.snd)) :
    (of_walk s t q p hr).links = {e | ∃ d ∈ p.darts, e = s(t d.fst,s d.snd)} := by
  induction p with
  | nil => ext e; simp [of_walk, links]
  | cons h p ih =>
    ext e
    simp [of_walk, links, ih,  ]

lemma of_walk_switchEdges (s t : W → V) (q : ∀ z, G.Walk (s z) (t z))
    {a b : W} (p : Q.Walk a b)
    (hr : ∀ d ∈ p.darts, G.Adj (t d.fst) (s d.snd)) :
    (of_walk s t q p hr).switchEdges = ⋃ z ∈ p.support, (q z).edgeSet := by
  rw [switchEdges, of_walk_visits]
  ext e
  simp only [Set.mem_iUnion, List.mem_map, exists_prop]
  constructor
  · rintro ⟨r,⟨z,hz,rfl⟩,he⟩
    exact ⟨z,hz,he⟩
  · rintro ⟨z,hz,he⟩
    exact ⟨⟨s z,t z,q z⟩,⟨z,hz,rfl⟩,he⟩

end VisitChain

theorem lift_quotient_cycle {W : Type cycleUniverse3} {Q : SimpleGraph W}
    (s t : W → V) (q : ∀ z, G.Walk (s z) (t z))
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle)
    (hr : ∀ d ∈ p.dropLast.darts, G.Adj (t d.fst) (s d.snd))
    (hc : G.Adj (t p.penultimate) (s a))
    (hq : ∀ z ∈ p.dropLast.support, (q z).IsPath)
    (hsep : ∀ z ∈ p.dropLast.support, ∀ w ∈ p.dropLast.support,
      z ≠ w → (q z).support.Disjoint (q w).support) :
    ∃ c : G.Walk (t p.penultimate) (t p.penultimate), c.IsCycle ∧
      c.edgeSet = {s(t p.penultimate,s a)} ∪
        {e | ∃ d ∈ p.dropLast.darts, e = s(t d.fst,s d.snd)} ∪
        (⋃ z ∈ p.dropLast.support, (q z).edgeSet) := by
  let chain := VisitChain.of_walk s t q p.dropLast hr
  have hv : chain.visits = p.dropLast.support.map (fun z => (⟨s z,t z,q z⟩ : CycleVisit G)) :=
    VisitChain.of_walk_visits s t q p.dropLast hr
  have hpaths : ∀ v ∈ chain.visits, v.walk.IsPath := by
    intro v hvv
    rw [hv] at hvv
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hvv
    exact hq z hz
  have hpair : chain.visits.Pairwise (fun v w => v.walk.support.Disjoint w.walk.support) := by
    rw [hv, List.pairwise_map]
    apply (List.pairwise_iff_getElem).mpr
    intro i j hi hj hij
    have hne : p.dropLast.support[i] ≠ p.dropLast.support[j] := by
      intro he
      have hij' := hp.isPath_dropLast.support_nodup.getElem_inj_iff.mp he
      omega
    exact hsep _ (List.getElem_mem _) _ (List.getElem_mem _) hne
  have hn : 3 ≤ chain.visits.length := by
    rw [hv, List.length_map, Walk.length_support, Walk.length_dropLast]
    have := hp.three_le_length
    omega
  obtain ⟨hcycle,hedges,_⟩ := chain.close_cycle hc hpaths hpair hn
  refine ⟨Walk.cons hc chain.walk,hcycle,?_⟩
  rw [hedges, VisitChain.of_walk_links, VisitChain.of_walk_switchEdges]

noncomputable section
attribute [local instance] Classical.propDecidable

theorem orient_edge_representatives {W : Type cycleUniverse4} {Q : SimpleGraph W}
    (projMap : V → W) (S : Set (Sym2 V)) (hSG : S ⊆ G.edgeSet)
    (hrep : ∀ e ∈ Q.edgeSet, ∃ f ∈ S, Sym2.map projMap f = e) :
    ∃ R : Q.Dart → G.Dart, ∀ d,
      (R d).edge ∈ S ∧ projMap (R d).fst = d.fst ∧ projMap (R d).snd = d.snd := by
  have hex : ∀ d : Q.Dart, ∃ r : G.Dart,
      r.edge ∈ S ∧ projMap r.fst = d.fst ∧ projMap r.snd = d.snd := by
    intro d
    obtain ⟨f,hf,hmap⟩ := hrep d.edge d.edge_mem
    induction f using Sym2.ind with
    | _ x y =>
      have hadj : G.Adj x y := hSG hf
      change s(projMap x,projMap y) = s(d.fst,d.snd) at hmap
      rcases Sym2.eq_iff.mp hmap with he | he
      · exact ⟨⟨(x,y),hadj⟩,hf,he.1,he.2⟩
      · refine ⟨⟨(y,x),hadj.symm⟩,?_,he.2,he.1⟩
        change s(y,x) ∈ S
        simpa only [Sym2.eq_swap] using hf
  exact Classical.axiomOfChoice hex

def portFrom {A : Type cycleUniverse5} {W : Type cycleUniverse6} (L : List A) (f : A → W) (g : A → V)
    (v₀ : V) (z : W) : V :=
  if h : ∃ d ∈ L, f d = z then g h.choose else v₀

lemma portFrom_on {A : Type cycleUniverse7} {W : Type cycleUniverse8} (L : List A) (f : A → W) (g : A → V)
    (v₀ : V) (hn : (L.map f).Nodup) {d : A} (hd : d ∈ L) :
    portFrom L f g v₀ (f d) = g d := by
  have hex : ∃ e ∈ L, f e = f d := ⟨d,hd,rfl⟩
  rw [portFrom, dite_eq_left hex]
  congr 1
  exact List.inj_on_of_nodup_map hn hex.choose_spec.1 hd hex.choose_spec.2

theorem choose_cycle_ports {W : Type cycleUniverse9} {Q : SimpleGraph W}
    (projMap : V → W) (R : Q.Dart → G.Dart)
    (hprojMap : ∀ d, projMap (R d).fst = d.fst ∧ projMap (R d).snd = d.snd)
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle) (v₀ : V) :
    ∃ s t : W → V,
      (∀ d ∈ p.darts, t d.fst = (R d).fst ∧ s d.snd = (R d).snd) ∧
      (∀ z ∈ p.dropLast.support, projMap (s z) = z ∧ projMap (t z) = z) := by
  let s := portFrom p.darts (fun d => d.snd) (fun d => (R d).snd) v₀
  let t := portFrom p.darts (fun d => d.fst) (fun d => (R d).fst) v₀
  have hnf : (p.darts.map (fun d => d.fst)).Nodup := by
    rw [Walk.map_fst_darts]
    exact hp.nodup_dropLast_support
  have hns : (p.darts.map (fun d => d.snd)).Nodup := by
    rw [Walk.map_snd_darts]
    exact hp.support_nodup
  have ht : ∀ d ∈ p.darts, t d.fst = (R d).fst := fun d hd =>
    portFrom_on _ _ _ _ hnf hd
  have hs : ∀ d ∈ p.darts, s d.snd = (R d).snd := fun d hd =>
    portFrom_on _ _ _ _ hns hd
  refine ⟨s,t,fun d hd => ⟨ht d hd,hs d hd⟩,?_⟩
  intro z hz
  have hz' : z ∈ p.support.dropLast := by
    rw [← p.support_dropLast hp.not_nil]
    exact hz
  have hzt : z ∈ p.support.tail :=
    p.tail_support_perm_dropLast_support.mem_iff.mpr hz'
  have hzf : z ∈ p.darts.map (fun d => d.fst) := by rwa [Walk.map_fst_darts]
  have hzs : z ∈ p.darts.map (fun d => d.snd) := by rwa [Walk.map_snd_darts]
  obtain ⟨d,hd,he⟩ := List.mem_map.mp hzf
  obtain ⟨e,he',hee⟩ := List.mem_map.mp hzs
  exact ⟨by rw [← hee,hs e he']; exact (hprojMap e).2,
    by rw [← he,ht d hd]; exact (hprojMap d).1⟩

lemma last_dart_mem {W : Type cycleUniverse10} {Q : SimpleGraph W} {a b : W}
    (p : Q.Walk a b) (hp : ¬p.Nil) :
    (⟨(p.penultimate,b),p.adj_penultimate hp⟩ : Q.Dart) ∈ p.darts := by
  have he := congrArg Walk.darts (p.concat_dropLast (p.adj_penultimate hp))
  rw [Walk.darts_concat] at he
  rw [← he]
  simp

lemma cycle_darts_split {W : Type cycleUniverse11} {Q : SimpleGraph W} {a b : W}
    (p : Q.Walk a b) (hp : ¬p.Nil) :
    p.darts = p.dropLast.darts ++ [⟨(p.penultimate,b),p.adj_penultimate hp⟩] := by
  have he := congrArg Walk.darts (p.concat_dropLast (p.adj_penultimate hp))
  simpa only [Walk.darts_concat, List.concat_eq_append] using he.symm

theorem inflate_represented_cycle {W : Type cycleUniverse12} {Q : SimpleGraph W}
    (R : Q.Dart → G.Dart) (s t : W → V)
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle)
    (hports : ∀ d ∈ p.darts, t d.fst = (R d).fst ∧ s d.snd = (R d).snd)
    (q : ∀ z, G.Walk (s z) (t z))
    (hq : ∀ z ∈ p.dropLast.support, (q z).IsPath)
    (hsep : ∀ z ∈ p.dropLast.support, ∀ w ∈ p.dropLast.support,
      z ≠ w → (q z).support.Disjoint (q w).support) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      c.edgeSet = {e | ∃ d ∈ p.darts, e = (R d).edge} ∪
        (⋃ z ∈ p.dropLast.support, (q z).edgeSet) := by
  let last : Q.Dart := ⟨(p.penultimate,a),p.adj_penultimate hp.not_nil⟩
  have hlast : last ∈ p.darts := last_dart_mem p hp.not_nil
  have hsub : p.dropLast.darts ⊆ p.darts := by
    rw [Walk.darts_dropLast]; exact List.dropLast_subset _
  have hed : ∀ d ∈ p.darts, s(t d.fst,s d.snd) = (R d).edge := by
    intro d hd
    rw [(hports d hd).1,(hports d hd).2]
    rfl
  have hadj : ∀ d ∈ p.darts, G.Adj (t d.fst) (s d.snd) := by
    intro d hd
    rw [(hports d hd).1,(hports d hd).2]
    exact (R d).adj
  obtain ⟨c,hc,he⟩ := lift_quotient_cycle s t q p hp
    (fun d hd => hadj d (hsub hd)) (hadj last hlast) hq hsep
  refine ⟨_,c,hc,?_⟩
  rw [he]
  have hlinks : {s(t p.penultimate,s a)} ∪
      {e | ∃ d ∈ p.dropLast.darts, e = s(t d.fst,s d.snd)} =
      {e | ∃ d ∈ p.darts, e = (R d).edge} := by
    ext e
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (rfl | ⟨d,hd,rfl⟩)
      · exact ⟨last,hlast,hed last hlast⟩
      · exact ⟨d,hsub hd,hed d (hsub hd)⟩
    · rintro ⟨d,hd,rfl⟩
      rw [cycle_darts_split p hp.not_nil] at hd
      simp only [List.mem_append,List.mem_singleton] at hd
      rcases hd with hd | rfl
      · exact Or.inr ⟨d,hd,(hed d (hsub hd)).symm⟩
      · exact Or.inl (hed last hlast).symm
  rw [hlinks]

def cyclePortSet {W : Type cycleUniverse15} (S : Set W) (s t : W → V) : Set V :=
  {v | ∃ z ∈ S, v = s z ∨ v = t z}

def visitInterior {W : Type cycleUniverse16} (s t : W → V) (q : ∀ z, G.Walk (s z) (t z))
    (z : W) : Set V := {x | x ∈ (q z).support ∧ x ≠ s z ∧ x ≠ t z}

theorem switch_supports_separated {W : Type cycleUniverse17}
    (S : Set W) (projMap : V → W) (s t : W → V)
    (q : ∀ z, G.Walk (s z) (t z))
    (hproj : ∀ z ∈ S, projMap (s z) = z ∧ projMap (t z) = z)
    (havoid : ∀ z ∈ S, Disjoint (visitInterior s t q z) (cyclePortSet S s t))
    (hinter : ∀ z ∈ S, ∀ w ∈ S, z ≠ w →
      Disjoint (visitInterior s t q z) (visitInterior s t q w)) :
    ∀ z ∈ S, ∀ w ∈ S, z ≠ w → (q z).support.Disjoint (q w).support := by
  intro z hz w hw hzw
  rw [List.disjoint_left]
  intro x hx hy
  by_cases hxend : x = s z ∨ x = t z
  · have hxZ : x ∈ cyclePortSet S s t := ⟨z,hz,hxend⟩
    by_cases hyend : x = s w ∨ x = t w
    · have hxprojMap : projMap x = z := by rcases hxend with rfl | rfl <;> simp_all
      have hyprojMap : projMap x = w := by rcases hyend with rfl | rfl <;> simp_all
      exact hzw (hxprojMap.symm.trans hyprojMap)
    · exact Set.disjoint_left.mp (havoid w hw)
        ⟨hy,fun he => hyend (Or.inl he),fun he => hyend (Or.inr he)⟩ hxZ
  · have hxI : x ∈ visitInterior s t q z :=
      ⟨hx,fun he => hxend (Or.inl he),fun he => hxend (Or.inr he)⟩
    by_cases hyend : x = s w ∨ x = t w
    · exact Set.disjoint_left.mp (havoid z hz) hxI ⟨w,hw,hyend⟩
    · exact Set.disjoint_left.mp (hinter z hz w hw hzw) hxI
        ⟨hy,fun he => hyend (Or.inl he),fun he => hyend (Or.inr he)⟩

theorem cyclePortSet_eq_representative_vertices {W : Type cycleUniverse18} {Q : SimpleGraph W}
    (R : Q.Dart → G.Dart) (s t : W → V)
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle)
    (hports : ∀ d ∈ p.darts, t d.fst = (R d).fst ∧ s d.snd = (R d).snd) :
    cyclePortSet {z | z ∈ p.dropLast.support} s t =
      {v | ∃ d ∈ p.darts, v = (R d).fst ∨ v = (R d).snd} := by
  have hmF : p.darts.map (fun d => d.fst) = p.dropLast.support := by
    rw [Walk.map_fst_darts, p.support_dropLast hp.not_nil]
  have hmS : ∀ z, z ∈ p.darts.map (fun d => d.snd) ↔ z ∈ p.dropLast.support := by
    intro z
    rw [Walk.map_snd_darts, p.support_dropLast hp.not_nil]
    exact p.tail_support_perm_dropLast_support.mem_iff
  ext v
  constructor
  · rintro ⟨z,hz,hv | hv⟩
    · obtain ⟨d,hd,hds⟩ := List.mem_map.mp ((hmS z).mpr hz)
      exact ⟨d,hd,Or.inr (hv.trans (by rw [← hds]; exact (hports d hd).2))⟩
    · have hz' : z ∈ p.darts.map (fun d => d.fst) := by rwa [hmF]
      obtain ⟨d,hd,hdf⟩ := List.mem_map.mp hz'
      exact ⟨d,hd,Or.inl (hv.trans (by rw [← hdf]; exact (hports d hd).1))⟩
  · rintro ⟨d,hd,hv | hv⟩
    · refine ⟨d.fst,?_,Or.inr (hv.trans (hports d hd).1.symm)⟩
      rw [← hmF]
      exact List.mem_map.mpr ⟨d,hd,rfl⟩
    · exact ⟨d.snd,(hmS _).mp (List.mem_map.mpr ⟨d,hd,rfl⟩),
        Or.inl (hv.trans (hports d hd).2.symm)⟩

end
end ErdosGallai.Batch

end
end

/-! ### Upstream module `Combinatorics/CycleDecomposition/Templates.lean` -/

noncomputable section
namespace ErdosGallai.Batch
noncomputable section
open _root_.Finset _root_.SimpleGraph
attribute [local instance] Classical.propDecidable

def demandLoad {I : Type cycleUniverse1} {V : Type cycleUniverse2} [Fintype I] (x y : I → V) (v : V) : ℕ :=
  (univ.filter fun i => x i = v ∨ y i = v).card

theorem demand_load_le_degree {V : Type cycleUniverse3} {I : Type cycleUniverse4} {B : Type cycleUniverse5} [Fintype V] [Fintype I]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : B → Set (Sym2 V))
    (hE : Pairwise fun b c => Disjoint (E b) (E c))
    (owner : I → B) (x y : I → V)
    (hunique : ∀ i j v, owner i = owner j →
      (x i = v ∨ y i = v) → (x j = v ∨ y j = v) → i = j)
    (hedge : ∀ i v, x i = v ∨ y i = v →
      ∃ w, G.Adj v w ∧ s(v,w) ∈ E (owner i)) (v : V) :
    demandLoad x y v ≤ G.degree v := by
  classical
  let S := {i : I // x i = v ∨ y i = v}
  have hs (i : S) := hedge i.val v i.property
  let f : S → G.neighborFinset v := fun i =>
    ⟨(hs i).choose, by simpa using (hs i).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro i j hij
    have he : (hs i).choose = (hs j).choose := congrArg Subtype.val hij
    apply Subtype.ext
    by_cases ho : owner i.val = owner j.val
    · exact hunique i.val j.val v ho i.property j.property
    · exact False.elim (Set.disjoint_left.mp (hE ho)
        (hs i).choose_spec.2 (by rw [he]; exact (hs j).choose_spec.2))
  have hc := Fintype.card_le_of_injective f hf
  have hn : Fintype.card (G.neighborFinset v) = G.degree v := by
    rw [Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree]
  rw [hn] at hc
  have hcS : Fintype.card S = demandLoad x y v := by
    simp only [S, Fintype.card_subtype, demandLoad]
    congr 1
    ext i
    simp
  rw [hcS] at hc
  exact hc

lemma start_has_incident_edge {V : Type cycleUniverse6} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : ¬p.Nil) :
    ∃ w, G.Adj a w ∧ s(a,w) ∈ p.edgeSet := by
  exact ⟨p.snd,p.adj_snd hp,p.mk_start_snd_mem_edges hp⟩

lemma finish_has_incident_edge {V : Type cycleUniverse7} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : ¬p.Nil) :
    ∃ w, G.Adj b w ∧ s(b,w) ∈ p.edgeSet := by
  refine ⟨p.penultimate,(p.adj_penultimate hp).symm,?_⟩
  change s(b,p.penultimate) ∈ p.edges
  simpa only [Sym2.eq_swap] using p.mk_penultimate_end_mem_edges hp

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch

def CycleOrSingleEdge {V : Type} (G : SimpleGraph V)
    (s : Set (Sym2 V)) : Prop :=
  (∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ s = p.edgeSet) ∨
  ∃ e ∈ G.edgeSet, s = {e}

def EdgeDecomposition {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ parts : Fin k → Set (Sym2 V),
    (∀ i, CycleOrSingleEdge G (parts i)) ∧
    Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
    (⋃ i, parts i) = G.edgeSet

noncomputable section
open _root_.SimpleGraph

lemma cycleOrSingleEdge_subset {V : Type} {G : SimpleGraph V}
    {s : Set (Sym2 V)} (hs : CycleOrSingleEdge G s) : s ⊆ G.edgeSet := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact p.edges_subset_edgeSet
  · simpa using he

lemma cycleOrSingleEdge_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) {s : Set (Sym2 V)}
    (hs : CycleOrSingleEdge G s) : CycleOrSingleEdge H (Sym2.map f '' s) := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact Or.inl ⟨f v,p.map f,hp.map hf,(p.edgeSet_map f).symm⟩
  · refine Or.inr ⟨Sym2.map f e, ?_, by simp⟩
    induction e using Sym2.ind with | _ x y =>
      exact f.map_adj he

lemma edgeDecomposition_of_indexed {V I : Type} [Fintype I] (G : SimpleGraph V)
    (parts : I → Set (Sym2 V)) (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hu : (⋃ i, parts i) = G.edgeSet) : EdgeDecomposition G (Fintype.card I) := by
  let e := Fintype.equivFin I
  refine ⟨fun j => parts (e.symm j), fun j => hp _, ?_, ?_⟩
  · intro i j hij
    exact hd (fun he => hij (e.symm.injective he))
  · ext x
    simp only [Set.mem_iUnion]
    rw [← hu]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨e i, by simpa using hi⟩

theorem edgeDecomposition_singleEdges {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (Nat.card G.edgeSet) := by
  classical
  let : Fintype G.edgeSet := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  apply edgeDecomposition_of_indexed G (fun e : G.edgeSet => {e.1})
  · intro e; exact Or.inr ⟨e.1,e.2,rfl⟩
  · intro e d hed
    exact Set.disjoint_singleton.mpr (fun h => hed (Subtype.ext h))
  · ext e; simp

theorem edgeDecomposition_assemble {V I : Type} [Fintype I] (G : SimpleGraph V)
    (W : I → Type) (H : ∀ i, SimpleGraph (W i))
    (f : ∀ i, H i →g G) (hf : ∀ i, Function.Injective (f i))
    (hdisj : Pairwise (fun i j =>
      Disjoint (Sym2.map (f i) '' (H i).edgeSet) (Sym2.map (f j) '' (H j).edgeSet)))
    (hcover : (⋃ i, Sym2.map (f i) '' (H i).edgeSet) = G.edgeSet)
    (k : I → ℕ) (hparts : ∀ i, EdgeDecomposition (H i) (k i)) :
    EdgeDecomposition G (∑ i, k i) := by
  classical
  choose parts hp hd hu using hparts
  let J := Σ i, Fin (k i)
  let P : J → Set (Sym2 V) := fun j => Sym2.map (f j.1) '' parts j.1 j.2
  have hpart : ∀ j, CycleOrSingleEdge G (P j) := by
    intro j; exact cycleOrSingleEdge_map (f j.1) (hf j.1) (hp j.1 j.2)
  have hsub : ∀ i a, parts i a ⊆ (H i).edgeSet := by
    intro i a; exact cycleOrSingleEdge_subset (hp i a)
  have hdisjP : Pairwise (fun i j => Disjoint (P i) (P j)) := by
    rintro ⟨i,a⟩ ⟨j,b⟩ hij
    by_cases h : i = j
    · subst j
      have hab : a ≠ b := fun he => hij (by cases he; rfl)
      apply Set.disjoint_left.mpr
      rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩
      have hxy : x = y := Sym2.map.injective (hf i) (he.trans he'.symm)
      subst y
      exact Set.disjoint_left.mp (hd i hab) hx hy
    · exact (hdisj h).mono (Set.image_mono (hsub i a)) (Set.image_mono (hsub j b))
  have hcoverP : (⋃ j, P j) = G.edgeSet := by
    rw [← hcover]
    ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨⟨i,a⟩,x,hx,he⟩
      exact ⟨i,x,hsub i a hx,he⟩
    · rintro ⟨i,x,hx,he⟩
      rw [← hu i] at hx
      obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hx
      exact ⟨⟨i,a⟩,x,ha,he⟩
  have hc : Fintype.card J = ∑ i, k i := by simp [J, Fintype.card_sigma]
  rw [← hc]
  exact edgeDecomposition_of_indexed G P hpart hdisjP hcoverP

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open _root_.SimpleGraph _root_.Finset
attribute [local instance] Classical.propDecidable

def decompositionCost {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.find (show ∃ k, EdgeDecomposition G k from ⟨_,edgeDecomposition_singleEdges G⟩)

lemma decompositionCost_spec {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (decompositionCost G) := Nat.find_spec _

lemma decompositionCost_le {V : Type} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : EdgeDecomposition G k) : decompositionCost G ≤ k := Nat.find_min' _ h

theorem edgeDecomposition_adjoin {V I J : Type} [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) (H : ∀ j, SimpleGraph (W j)) (f : ∀ j, H j →g G)
    (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet)
    (k : J → ℕ) (hD : ∀ j, EdgeDecomposition (H j) (k j)) :
    EdgeDecomposition G (Fintype.card I + ∑ j, k j) := by
  classical
  choose P hP hPd hPc using hD
  let R : (I ⊕ Σ j, Fin (k j)) → Set (Sym2 V) :=
    Sum.elim parts (fun z => Sym2.map (f z.1) '' P z.1 z.2)
  have hsub : ∀ j i, P j i ⊆ (H j).edgeSet := fun j i => cycleOrSingleEdge_subset (hP j i)
  have hRp : ∀ z, CycleOrSingleEdge G (R z) := by
    intro z
    rcases z with z | ⟨j,i⟩
    · exact hp z
    · exact cycleOrSingleEdge_map (f j) (hf j) (hP j i)
  have hRd : Pairwise fun z t => Disjoint (R z) (R t) := by
    intro z t hzt
    rcases z with z | ⟨j,i⟩ <;> rcases t with t | ⟨l,a⟩
    · exact hd (fun h => hzt (congrArg Sum.inl h))
    · exact ((hHP l z).mono_left (Set.image_mono (hsub l a))).symm
    · exact (hHP j t).mono_left (Set.image_mono (hsub j i))
    · by_cases hjl : j = l
      · subst l
        have hia : i ≠ a := fun h => hzt (by cases h; rfl)
        apply Set.disjoint_left.mpr
        rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩
        have hxy := Sym2.map.injective (hf j) (he.trans he'.symm)
        subst y
        exact Set.disjoint_left.mp (hPd j hia) hx hy
      · exact (hHH hjl).mono (Set.image_mono (hsub j i)) (Set.image_mono (hsub l a))
  have hRu : (⋃ z, R z) = G.edgeSet := by
    rw [← hu]
    ext e
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨z,hz⟩
      rcases z with z | ⟨j,i⟩
      · exact Or.inl ⟨z,hz⟩
      · obtain ⟨x,hx,he⟩ := hz
        exact Or.inr ⟨j,x,hsub j i hx,he⟩
    · rintro (⟨i,hi⟩ | ⟨j,x,hx,he⟩)
      · exact ⟨Sum.inl i,hi⟩
      · rw [← hPc j] at hx
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
        exact ⟨Sum.inr ⟨j,i⟩,x,hi,he⟩
  simpa only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin] using
    edgeDecomposition_of_indexed G R hRp hRd hRu

lemma decompositionCost_adjoin {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) [∀ j, Fintype (W j)] (H : ∀ j, SimpleGraph (W j))
    (f : ∀ j, H j →g G) (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) :=
  decompositionCost_le (edgeDecomposition_adjoin G parts hp hd W H f hf hHH hHP hu _
    (fun j => decompositionCost_spec (H j)))

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
noncomputable section
open _root_.SimpleGraph _root_.Finset
attribute [local instance] Classical.propDecidable

lemma edgeDecomposition_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : H →g G) (hf : Function.Injective f)
    (hu : Sym2.map f '' H.edgeSet = G.edgeSet) {k : ℕ} (hk : EdgeDecomposition H k) :
    EdgeDecomposition G k := by
  have := edgeDecomposition_assemble (I := Unit) G (fun _ : Unit => W) (fun _ => H) (fun _ => f)
    (fun _ => hf) (by intro i j hij; exact False.elim (hij (Subsingleton.elim _ _)))
    (by rw [Set.iUnion_const]; exact hu) (fun _ => k) (fun _ => hk)
  simpa using this

lemma edgeDecomposition_on {V : Type} (G : SimpleGraph V)
    (A : Finset V) (hA : ∀ ⦃x y⦄, G.Adj x y → x ∈ A ∧ y ∈ A)
    {k : ℕ} (hk : EdgeDecomposition (G.induce (A:Set V)) k) : EdgeDecomposition G k := by
  classical
  let f : G.induce (A:Set V) →g G := ⟨Subtype.val,fun h => h⟩
  apply edgeDecomposition_map f Subtype.val_injective _ hk
  ext e
  constructor
  · rintro ⟨e,he,rfl⟩
    induction e using Sym2.ind with | _ x y => exact he
  · intro he
    induction e using Sym2.ind with
    | _ x y => exact ⟨s(⟨x,(hA he).1⟩,⟨y,(hA he).2⟩),he,rfl⟩

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open _root_.Finset _root_.SimpleGraph
attribute [local instance] Classical.propDecidable

lemma endpointLoad_subtype_le {V I : Type} [Fintype I]
    (x y : I → V) (s : I → Prop) (v : V) :
    endpointLoad univ (fun i : {i // s i} => x i) (fun i => y i) v ≤ endpointLoad univ x y v := by
  classical
  simp only [endpointLoad]
  apply Finset.card_le_card_of_injOn (fun i : {i // s i} => i.val)
  · intro i hi; simpa using hi
  · intro i _ j _ h; exact Subtype.ext h

theorem uniform_multi_batch_routing :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V R I T : Type) [Fintype V] [Fintype R] [Fintype I],
      ∀ (G : SimpleGraph V) (P : R → SimpleGraph V) (U : R → Finset V),
      (∀ r, P r ≤ G) → Pairwise (fun r s => Disjoint (P r).edgeSet (P s).edgeSet) →
      Pairwise (fun r s => Disjoint (U r) (U s)) →
      (∀ r, CutExpansionOn (P r) (U r) (D^(9/10:ℝ)/4)) →
      (∀ r, D^(9/10:ℝ) ≤ ((U r).card:ℝ) ∧ ((U r).card:ℝ) ≤ D^(51/50:ℝ)) →
      ∀ (owner : I → R) (x y : I → V),
      (∀ i, x i ∈ U (owner i) ∧ y i ∈ U (owner i) ∧ x i ≠ y i) →
      ∀ (team : I → T) (Z : I → Finset V),
      (∀ v, (endpointLoad univ x y v:ℝ) ≤ D^(1/100:ℝ)) →
      (∀ i, ((univ.filter (fun j => team j = team i)).card:ℝ) ≤ D^(3/10:ℝ)) →
      (∀ i, ((Z i).card:ℝ) ≤ 2*D^(3/10:ℝ)) →
      ∃ q : ∀ i, G.Walk (x i) (y i),
        (∀ i, (q i).IsPath ∧ (∀ v ∈ (q i).support, v ∈ U (owner i)) ∧
          (q i).edgeSet ⊆ (P (owner i)).edgeSet ∧ Disjoint (pathInterior (q i)) (Z i)) ∧
        Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
        (∀ i j, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
  classical
  obtain ⟨D₀,hD₀,hroute⟩ := uniform_batch_routing
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V R I T _ _ _ G P U hPG hPP hUU he hr owner x y hxy team Z hl ht hZ
  let J := fun r => {i // owner i = r}
  have hex : ∀ r, ∃ q : ∀ i : J r, G.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (∀ v ∈ (q i).support, v ∈ U r) ∧
        (q i).edgeSet ⊆ (P r).edgeSet ∧ Disjoint (pathInterior (q i)) (Z i)) ∧
      Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
      (∀ i j : J r, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
    intro r
    obtain ⟨q,hq,hd,hi⟩ := hroute D hD V G (P r) (hPG r) (U r) (he r) (hr r).1 (hr r).2
      (J r) T (fun i => x i) (fun i => y i)
      (fun i => by simpa only [← i.property] using (hxy i).1)
      (fun i => by simpa only [← i.property] using (hxy i).2.1)
      (fun i => (hxy i).2.2) (fun i => team i) (fun i => Z i)
      (fun v => (show (endpointLoad univ (fun i : J r => x i) (fun i => y i) v:ℝ) ≤
        endpointLoad univ x y v by exact_mod_cast endpointLoad_subtype_le x y (fun i => owner i = r) v).trans (hl v))
      (fun i => le_trans (by
        apply Nat.cast_le.mpr
        apply Finset.card_le_card_of_injOn (fun i : J r => i.val)
        · intro j hj; simpa using hj
        · intro j _ l _ h; exact Subtype.ext h) (ht i)) (fun i => hZ i)
    exact ⟨q,fun i => ⟨(hq i).1,(hq i).2.2⟩,hd,hi⟩
  choose q hq hd hi using hex
  let f : ∀ i, G.Walk (x i) (y i) := fun i => q (owner i) ⟨i,rfl⟩
  have hf (i : I) (r : R) (h : owner i = r) : f i = q r ⟨i,h⟩ := by
    subst r; rfl
  refine ⟨f,fun i => hq _ _,?_,?_⟩
  · intro i j hij
    by_cases hh : owner i = owner j
    · have h := hd (owner i) (show (⟨i,rfl⟩:J (owner i)) ≠ ⟨j,hh.symm⟩ from
        fun h => hij (congrArg Subtype.val h))
      rw [hf j (owner i) hh.symm]
      exact h
    · exact (hPP hh).mono (hq _ _).2.2.1 (hq _ _).2.2.1
  · intro i j hij hteam
    by_cases hh : owner i = owner j
    · have h := hi (owner i) ⟨i,rfl⟩ ⟨j,hh.symm⟩
        (fun h => hij (congrArg Subtype.val h)) hteam
      rw [hf j (owner i) hh.symm]
      exact h
    · apply (hUU hh).mono
      · intro v hv; exact (hq (owner i) ⟨i,rfl⟩).2.1 v (List.mem_toFinset.mp (Finset.mem_sdiff.mp hv).1)
      · intro v hv; exact (hq (owner j) ⟨j,rfl⟩).2.1 v (List.mem_toFinset.mp (Finset.mem_sdiff.mp hv).1)

structure CycleOutline {V : Type} (G : SimpleGraph V) where
  W : Type
  finiteW : Fintype W
  Q : SimpleGraph W
  base : W
  cycle : Q.Walk base base
  isCycle : cycle.IsCycle
  rep : Q.Dart → G.Dart
  start : W → V
  finish : W → V
  project : V → W
  ports : ∀ d ∈ cycle.darts, finish d.fst = (rep d).fst ∧ start d.snd = (rep d).snd
  projects : ∀ z ∈ cycle.dropLast.support, project (start z) = z ∧ project (finish z) = z
  outside : ∀ z, z ∉ cycle.dropLast.support → start z = finish z
attribute [instance] CycleOutline.finiteW

namespace CycleOutline
variable {V : Type} {G : SimpleGraph V} (c : CycleOutline G)

def edges : Set (Sym2 V) := {e | ∃ d ∈ c.cycle.darts, e = (c.rep d).edge}
def vertices : Finset V := c.cycle.darts.toFinset.biUnion fun d => {(c.rep d).fst,(c.rep d).snd}
abbrev Switch := {z : c.W // z ∈ c.cycle.dropLast.support ∧ c.start z ≠ c.finish z}
instance : Fintype c.Switch := inferInstanceAs (Fintype {_z : c.W // _})

lemma edges_subset : c.edges ⊆ G.edgeSet := by
  rintro e ⟨d,hd,rfl⟩; exact (c.rep d).edge_mem

lemma outgoing (z : c.W) (hz : z ∈ c.cycle.dropLast.support) :
    ∃ d ∈ c.cycle.darts, d.fst = z := by
  have h : z ∈ c.cycle.darts.map (fun d => d.fst) := by
    rw [Walk.map_fst_darts,← c.cycle.support_dropLast c.isCycle.not_nil]; exact hz
  exact List.mem_map.mp h

lemma incoming (z : c.W) (hz : z ∈ c.cycle.dropLast.support) :
    ∃ d ∈ c.cycle.darts, d.snd = z := by
  have h : z ∈ c.cycle.darts.map (fun d => d.snd) := by
    rw [Walk.map_snd_darts]
    apply c.cycle.tail_support_perm_dropLast_support.mem_iff.mpr
    rw [← c.cycle.support_dropLast c.isCycle.not_nil]; exact hz
  exact List.mem_map.mp h

lemma endpoint_incident (z : c.Switch) (v : V) (hv : c.start z = v ∨ c.finish z = v) :
    ∃ w, G.Adj v w ∧ s(v,w) ∈ c.edges := by
  rcases hv with rfl | rfl
  · obtain ⟨d,hd,he⟩ := c.incoming z z.property.1
    have hh := (c.ports d hd).2
    rw [he] at hh
    refine ⟨(c.rep d).fst,?_,?_⟩
    · rw [hh]; exact (c.rep d).adj.symm
    · refine ⟨d,hd,?_⟩
      rw [hh]; exact Sym2.eq_swap
  · obtain ⟨d,hd,he⟩ := c.outgoing z z.property.1
    have hh := (c.ports d hd).1
    rw [he] at hh
    refine ⟨(c.rep d).snd,?_,?_⟩
    · rw [hh]; exact (c.rep d).adj
    · refine ⟨d,hd,?_⟩; rw [hh]; rfl

lemma endpoint_unique (z w : c.Switch) (v : V)
    (hz : c.start z = v ∨ c.finish z = v) (hw : c.start w = v ∨ c.finish w = v) : z = w := by
  apply Subtype.ext
  have hf : ∀ (z : c.Switch), c.start z = v ∨ c.finish z = v → c.project v = z := by
    intro z hz
    rcases hz with h | h
    · rw [← h]; exact (c.projects z z.property.1).1
    · rw [← h]; exact (c.projects z z.property.1).2
  exact (hf z hz).symm.trans (hf w hw)

lemma vertices_card_support : c.vertices.card ≤ 2 * c.cycle.dropLast.support.toFinset.card := by
  have hfirst : c.vertices.card ≤ 2*c.cycle.darts.toFinset.card := by
    calc
      _ ≤ ∑ d ∈ c.cycle.darts.toFinset, ({(c.rep d).fst,(c.rep d).snd}:Finset V).card := Finset.card_biUnion_le
      _ ≤ ∑ d ∈ c.cycle.darts.toFinset, 2 := Finset.sum_le_sum (fun d _ => Finset.card_le_two)
      _ = _ := by simp [mul_comm]
  have hd : c.cycle.darts.toFinset.card ≤ c.cycle.dropLast.support.toFinset.card := by
    calc
      _ ≤ c.cycle.darts.length := List.toFinset_card_le _
      _ = c.cycle.dropLast.support.length := by
        rw [Walk.length_darts,Walk.length_support,Walk.length_dropLast]
        have := c.isCycle.three_le_length; omega
      _ = c.cycle.dropLast.support.toFinset.card := (List.toFinset_card_of_nodup c.isCycle.isPath_dropLast.support_nodup).symm
  omega

lemma mem_vertices (v : V) : v ∈ c.vertices ↔ ∃ d ∈ c.cycle.darts, v = (c.rep d).fst ∨ v = (c.rep d).snd := by
  simp [vertices]

theorem complete [DecidableEq V]
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z))
    (hs : ∀ z, (route z).IsPath)
    (ha : ∀ z, Disjoint (pathInterior (route z)) c.vertices)
    (hd : Pairwise fun z w => Disjoint (pathInterior (route z)) (pathInterior (route w))) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧
      p.edgeSet = c.edges ∪ ⋃ z, (route z).edgeSet := by
  classical
  let visits : ∀ z, G.Walk (c.start z) (c.finish z) := fun z =>
    if h : z ∈ c.cycle.dropLast.support ∧ c.start z ≠ c.finish z then route ⟨z,h⟩
    else (Walk.nil : G.Walk (c.start z) (c.start z)).copy rfl (by
      by_cases hz : z ∈ c.cycle.dropLast.support
      · exact not_not.mp (fun hn => h ⟨hz,hn⟩)
      · exact c.outside z hz)
  have hv (z : c.Switch) : visits z = route z := by simp only [visits,dite_eq_left z.property]
  have hnil (z : c.W) (hz : ¬(z ∈ c.cycle.dropLast.support ∧ c.start z ≠ c.finish z)) :
      (visits z).Nil := by simp only [visits,dite_eq_right hz,Walk.nil_copy,Walk.nil_nil]
  have hpath : ∀ z, (visits z).IsPath := by
    intro z
    by_cases hz : z ∈ c.cycle.dropLast.support ∧ c.start z ≠ c.finish z
    · simpa only [visits,dite_eq_left hz] using hs ⟨z,hz⟩
    · simp [visits,dite_eq_right hz]
  have hinter (z : c.W) : visitInterior c.start c.finish visits z = (pathInterior (visits z):Set V) := by
    ext v; simp [visitInterior,pathInterior]
  have h_avoid : ∀ z ∈ c.cycle.dropLast.support, Disjoint
      (visitInterior c.start c.finish visits z) {v | ∃ d ∈ c.cycle.darts, v = (c.rep d).fst ∨ v = (c.rep d).snd} := by
    intro z hz
    rw [hinter]
    have he : {v | ∃ d ∈ c.cycle.darts, v = (c.rep d).fst ∨ v = (c.rep d).snd} = (c.vertices:Set V) := by
      ext v; exact (c.mem_vertices v).symm
    rw [he,Finset.disjoint_coe]
    by_cases hne : c.start z ≠ c.finish z
    · rw [hv ⟨z,hz,hne⟩]; exact ha _
    · have hn := hnil z (by tauto)
      simp [Finset.disjoint_left,pathInterior,Walk.nil_iff_support_eq.mp hn]
  have h_dis : Pairwise fun z w : {z // z ∈ c.cycle.dropLast.support} =>
      Disjoint (visitInterior c.start c.finish visits z) (visitInterior c.start c.finish visits w) := by
    intro z w hzw
    rw [hinter,hinter,Finset.disjoint_coe]
    by_cases hz : c.start z ≠ c.finish z
    · by_cases hw : c.start w ≠ c.finish w
      · rw [hv ⟨z,z.property,hz⟩,hv ⟨w,w.property,hw⟩]
        exact hd (fun h => hzw (Subtype.ext (congrArg (fun t : c.Switch => (t:c.W)) h)))
      · have hn := hnil w (by tauto); simp [Finset.disjoint_left,pathInterior,Walk.nil_iff_support_eq.mp hn] ; tauto
    · have hn := hnil z (by tauto); simp [Finset.disjoint_left,pathInterior,Walk.nil_iff_support_eq.mp hn]
  obtain ⟨v,p,hp,hedge⟩ := inflate_represented_cycle c.rep c.start c.finish c.cycle c.isCycle c.ports visits
    (fun z _ => hpath z) (switch_supports_separated {z | z ∈ c.cycle.dropLast.support}
      c.project c.start c.finish visits c.projects
      (by
        intro z hz
        rw [cyclePortSet_eq_representative_vertices c.rep c.start c.finish c.cycle c.isCycle c.ports]
        exact h_avoid z hz)
      (fun z hz w hw hzw => h_dis (show (⟨z,hz⟩:{z // z ∈ c.cycle.dropLast.support}) ≠ ⟨w,hw⟩ from
        fun h => hzw (congrArg Subtype.val h))))
  refine ⟨v,p,hp,hedge.trans ?_⟩
  congr 1
  ext e
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨z,hz,he⟩
    by_cases hne : c.start z ≠ c.finish z
    · exact ⟨⟨z,hz,hne⟩,by rwa [hv ⟨z,hz,hne⟩] at he⟩
    · have hn := hnil z (by tauto)
      have hh := he
      simp [Walk.edgeSet,Walk.edges_eq_nil.mpr hn] at hh
  · rintro ⟨z,he⟩; exact ⟨z,z.property.1,by rwa [hv]⟩

end CycleOutline
end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open _root_.Finset _root_.SimpleGraph
attribute [local instance] Classical.propDecidable

structure RoutingTemplate {V : Type} (G : SimpleGraph V) where
  Arity : Type
  finiteArity : Fintype Arity
  x : Arity → V
  y : Arity → V
  ne : ∀ i, x i ≠ y i
  edges : Set (Sym2 V)
  subset : edges ⊆ G.edgeSet
  vertices : Finset V
  incident : ∀ i v, x i = v ∨ y i = v → ∃ w, s(v,w) ∈ edges
  unique : ∀ i j v, (x i = v ∨ y i = v) → (x j = v ∨ y j = v) → i = j
  complete : ∀ q : ∀ i, G.Walk (x i) (y i),
    (∀ i, (q i).IsPath) →
    (∀ i, Disjoint (pathInterior (q i)) vertices) →
    Pairwise (fun i j => Disjoint (pathInterior (q i)) (pathInterior (q j))) →
    CycleOrSingleEdge G (edges ∪ ⋃ i, (q i).edgeSet)
attribute [instance] RoutingTemplate.finiteArity

namespace RoutingTemplate
variable {V : Type} {G : SimpleGraph V}

def ofCycle (c : CycleOutline G) : RoutingTemplate G where
  Arity := c.Switch
  finiteArity := inferInstance
  x := fun i => c.start i
  y := fun i => c.finish i
  ne := fun i => i.property.2
  edges := c.edges
  subset := c.edges_subset
  vertices := c.vertices
  incident := fun i v h => by obtain ⟨w,_,he⟩ := c.endpoint_incident i v h; exact ⟨w,he⟩
  unique := c.endpoint_unique
  complete := by
    intro q hs ha hd
    obtain ⟨v,p,hp,he⟩ := c.complete q hs ha hd
    exact Or.inl ⟨v,p,hp,he.symm⟩

def ofSingle (e : Sym2 V) (he : e ∈ G.edgeSet) : RoutingTemplate G where
  Arity := Empty
  finiteArity := inferInstance
  x := Empty.elim
  y := Empty.elim
  ne := fun i => i.elim
  edges := {e}
  subset := Set.singleton_subset_iff.mpr he
  vertices := ∅
  incident := fun i => i.elim
  unique := fun i => i.elim
  complete := by intro q _ _ _; exact Or.inr ⟨e,he,by simp⟩

def ofPath {x y : V} (p : G.Walk x y) (hp : p.IsPath) (hl : 2 ≤ p.length) : RoutingTemplate G where
  Arity := Unit
  finiteArity := inferInstance
  x := fun _ => y
  y := fun _ => x
  ne := fun _ he => by
    have hn : p.Nil := hp.nil_iff_eq.mpr he.symm
    have := Walk.length_eq_zero_iff.mpr hn
    omega
  edges := p.edgeSet
  subset := p.edges_subset_edgeSet
  vertices := p.support.toFinset
  incident := by
    intro i v hv
    have hn : ¬p.Nil := fun h => by have := Walk.length_eq_zero_iff.mpr h; omega
    rcases hv with rfl | rfl
    · obtain ⟨w,_,he⟩ := finish_has_incident_edge p hn; exact ⟨w,he⟩
    · obtain ⟨w,_,he⟩ := start_has_incident_edge p hn; exact ⟨w,he⟩
  unique := fun _ _ _ _ _ => Subsingleton.elim _ _
  complete := by
    intro q hs ha hd
    obtain ⟨hc,he⟩ := close_trimmed_path p (q ()) hp (hs ()) hl (by
      intro v hv hxa hxb hpv
      exact Finset.disjoint_left.mp (ha ())
        (by simp [pathInterior,hv,hxa,hxb]) (List.mem_toFinset.mpr hpv))
    refine Or.inl ⟨x,p.append (q ()),hc,?_⟩
    have hh : ∀ i : Unit, q i = q () := fun i => by cases i; rfl
    simp_rw [hh,Set.iUnion_const]
    exact he.symm

end RoutingTemplate

theorem uniform_resolve_templates :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V R B : Type) [Fintype V] [Fintype R] [Fintype B],
      ∀ (G F : SimpleGraph V) (P : R → SimpleGraph V) (U : R → Finset V),
      F ≤ G → (∀ r, P r ≤ G) →
      Pairwise (fun r s => Disjoint (P r).edgeSet (P s).edgeSet) →
      Pairwise (fun r s => Disjoint (U r) (U s)) →
      (∀ r, Disjoint F.edgeSet (P r).edgeSet) →
      (∀ r, CutExpansionOn (P r) (U r) (D^(9/10:ℝ)/4)) →
      (∀ r, D^(9/10:ℝ) ≤ ((U r).card:ℝ) ∧ ((U r).card:ℝ) ≤ D^(51/50:ℝ)) →
      ∀ (b : B → RoutingTemplate G),
      (∀ j, (b j).edges ⊆ F.edgeSet) →
      Pairwise (fun j k => Disjoint (b j).edges (b k).edges) →
      ∀ owner : (j : B) → (b j).Arity → R,
      (∀ j i, (b j).x i ∈ U (owner j i) ∧ (b j).y i ∈ U (owner j i)) →
      (∀ j i, (F.degree ((b j).x i):ℝ) ≤ D^(1/100:ℝ) ∧
        (F.degree ((b j).y i):ℝ) ≤ D^(1/100:ℝ)) →
      (∀ j, (Fintype.card (b j).Arity:ℝ) ≤ D^(3/10:ℝ)) →
      (∀ j, ((b j).vertices.card:ℝ) ≤ 2*D^(3/10:ℝ)) →
      ∃ (parts : B → Set (Sym2 V)) (used : Set (Sym2 V)),
        (∀ j, CycleOrSingleEdge G (parts j)) ∧
        Pairwise (fun j k => Disjoint (parts j) (parts k)) ∧
        used ⊆ ⋃ r, (P r).edgeSet ∧ Disjoint F.edgeSet used ∧
        (⋃ j, parts j) = (⋃ j, (b j).edges) ∪ used := by
  classical
  obtain ⟨D₀,hD₀,hr⟩ := uniform_multi_batch_routing
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V R B _ _ _ G F P U hFG hPG hPP hUU hFP he hsize b hsub hdis owner hends hdeg hnum hvertices
  let I := Σ j, (b j).Arity
  let x : I → V := fun i => (b i.1).x i.2
  let y : I → V := fun i => (b i.1).y i.2
  have hl (v : V) : (endpointLoad univ x y v:ℝ) ≤ D^(1/100:ℝ) := by
    have hload : endpointLoad univ x y v ≤ F.degree v := by
      have hh := demand_load_le_degree F (fun j => (b j).edges) hdis
        Sigma.fst x y (by
          rintro ⟨j,i⟩ ⟨k,l⟩ v h h₁ h₂
          dsimp only at h; subst k
          congr 1; exact (b j).unique i l v h₁ h₂) (by
          rintro ⟨j,i⟩ v h
          obtain ⟨w,hw⟩ := (b j).incident i v h
          exact ⟨w,hsub j hw,hw⟩) v
      simpa [demandLoad,endpointLoad] using hh
    by_cases hz : endpointLoad univ x y v = 0
    · rw [hz,Nat.cast_zero]; exact Real.rpow_nonneg (by linarith) _
    · have hp : 0 < (univ.filter fun i => x i = v ∨ y i = v).card := by
        change 0 < endpointLoad univ x y v; omega
      obtain ⟨⟨j,i⟩,hi⟩ := Finset.card_pos.mp hp
      have hv : (b j).x i = v ∨ (b j).y i = v := (Finset.mem_filter.mp hi).2
      have hh : (F.degree v:ℝ) ≤ D^(1/100:ℝ) := by
        rcases hv with rfl | rfl
        · exact (hdeg j i).1
        · exact (hdeg j i).2
      exact (Nat.cast_le.mpr hload).trans hh
  have hteam (i : I) : ((univ.filter fun j : I => j.1 = i.1).card:ℝ) ≤ D^(3/10:ℝ) := by
    have hc : (univ.filter fun j : I => j.1 = i.1).card = Fintype.card (b i.1).Arity := by
      rw [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_sigma]
      calc
        _ = ∑ j : B, if j = i.1 then Fintype.card (b j).Arity else 0 := by
          apply Finset.sum_congr rfl; intro j _
          by_cases hh : j = i.1 <;> simp [hh]
        _ = _ := by simp
    rw [hc]; exact hnum i.1
  obtain ⟨q,hq,hqd,hqi⟩ := hr D hD V R I B G P U hPG hPP hUU he hsize
    (fun i => owner i.1 i.2) x y (fun i => ⟨(hends i.1 i.2).1,(hends i.1 i.2).2,(b i.1).ne i.2⟩)
    Sigma.fst (fun i => (b i.1).vertices) hl hteam (fun i => hvertices i.1)
  let used := ⋃ i, (q i).edgeSet
  let parts := fun j => (b j).edges ∪ ⋃ i, (q ⟨j,i⟩).edgeSet
  have hu : used ⊆ ⋃ r, (P r).edgeSet := by
    apply Set.iUnion_subset; intro i
    exact Set.subset_iUnion_of_subset (owner i.1 i.2) (hq i).2.2.1
  have hFu : Disjoint F.edgeSet used := by
    refine Set.disjoint_iUnion_right.mpr (fun i => ?_)
    exact (hFP _).mono_right (hq i).2.2.1
  have hbu : ∀ j, Disjoint (b j).edges used := fun j => hFu.mono_left (hsub j)
  refine ⟨parts,used,?_,?_,hu,hFu,?_⟩
  · intro j
    exact (b j).complete (fun i => q ⟨j,i⟩) (fun i => (hq _).1) (fun i => (hq _).2.2.2)
      (fun i l hil => hqi _ _ (fun h => hil (eq_of_heq (Sigma.mk.inj_iff.mp h).2)) rfl)
  · intro j k hjk
    apply Set.disjoint_union_left.mpr; constructor
    · apply Set.disjoint_union_right.mpr; constructor
      · exact hdis hjk
      · exact (hbu j).mono_right (Set.iUnion_subset (fun i => Set.subset_iUnion (fun z : I => (q z).edgeSet) ⟨k,i⟩))
    · apply Set.disjoint_union_right.mpr; constructor
      · exact ((hbu k).mono_right (Set.iUnion_subset (fun i => Set.subset_iUnion (fun z : I => (q z).edgeSet) ⟨j,i⟩))).symm
      · apply Set.disjoint_iUnion_left.mpr; intro i
        apply Set.disjoint_iUnion_right.mpr; intro l
        exact hqd (fun h => hjk (congrArg Sigma.fst h))
  · ext e
    simp only [parts,used,Set.mem_iUnion,Set.mem_union]
    constructor
    · rintro ⟨j,he|⟨i,hi⟩⟩
      · exact Or.inl ⟨j,he⟩
      · exact Or.inr ⟨⟨j,i⟩,hi⟩
    · rintro (⟨j,he⟩|⟨⟨j,i⟩,he⟩)
      · exact ⟨j,Or.inl he⟩
      · exact ⟨j,Or.inr ⟨i,he⟩⟩

end
end ErdosGallai.Batch
end
/-! ### Upstream module `Combinatorics/CycleDecomposition/BatchResolution.lean` -/

noncomputable section
namespace ErdosGallai.Batch
noncomputable section
open _root_.Finset _root_.SimpleGraph
attribute [local instance] Classical.propDecidable

theorem cycle_template_of_representatives_bounded {V W : Type} [Fintype W]
    {G : SimpleGraph V} {Q : SimpleGraph W} (projMap : V → W)
    (S : Set (Sym2 V)) (hSG : S ⊆ G.edgeSet)
    (hrep : ∀ e ∈ Q.edgeSet, ∃! f, f ∈ S ∧ Sym2.map projMap f = e)
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle)
    (M : ℕ) (hM : p.dropLast.support.toFinset.card ≤ M) :
    ∃ b : RoutingTemplate G,
      b.edges = {e | e ∈ S ∧ Sym2.map projMap e ∈ p.edgeSet} ∧
      Fintype.card b.Arity ≤ M ∧
      b.vertices.card ≤ 2*M ∧
      ∀ i, projMap (b.x i) = projMap (b.y i) := by
  classical
  obtain ⟨R,hR⟩ := orient_edge_representatives projMap S hSG (fun e he =>
    (hrep e he).exists)
  let v₀ := (R ⟨(a,p.snd),p.adj_snd hp.not_nil⟩).fst
  obtain ⟨s,t,hports,hproj⟩ := choose_cycle_ports projMap R (fun d => (hR d).2) p hp v₀
  have hfst (d : Q.Dart) (hd : d ∈ p.darts) : d.fst ∈ p.dropLast.support := by
    rw [p.support_dropLast hp.not_nil,← Walk.map_fst_darts]
    exact List.mem_map.mpr ⟨d,hd,rfl⟩
  have hsnd (d : Q.Dart) (hd : d ∈ p.darts) : d.snd ∈ p.dropLast.support := by
    rw [p.support_dropLast hp.not_nil]
    apply p.tail_support_perm_dropLast_support.mem_iff.mp
    rw [← Walk.map_snd_darts]
    exact List.mem_map.mpr ⟨d,hd,rfl⟩
  let c : CycleOutline G := {
    W := W, finiteW := inferInstance, Q := Q, base := a, cycle := p, isCycle := hp,
    rep := R, start := fun z => if z ∈ p.dropLast.support then s z else v₀,
    finish := fun z => if z ∈ p.dropLast.support then t z else v₀,
    project := projMap,
    ports := by intro d hd; simpa only [ite_eq_left (hfst d hd),ite_eq_left (hsnd d hd)] using hports d hd,
    projects := by intro z hz; simpa only [ite_eq_left hz] using hproj z hz,
    outside := by intro z hz; simp only [ite_eq_right hz]
  }
  have hmap (d : Q.Dart) : Sym2.map projMap (R d).edge = d.edge := by
    change s(projMap (R d).fst,projMap (R d).snd) = s(d.fst,d.snd)
    rw [(hR d).2.1,(hR d).2.2]
  have he : c.edges = {e | e ∈ S ∧ Sym2.map projMap e ∈ p.edgeSet} := by
    ext e
    constructor
    · rintro ⟨d,hd,rfl⟩
      refine ⟨(hR d).1,?_⟩
      rw [hmap]
      change d.edge ∈ p.edges
      rw [Walk.edges_eq_map_darts]
      exact List.mem_map.mpr ⟨d,hd,rfl⟩
    · rintro ⟨hS,he⟩
      change Sym2.map projMap e ∈ p.edges at he
      rw [Walk.edges_eq_map_darts] at he
      obtain ⟨d,hd,hde⟩ := List.mem_map.mp he
      refine ⟨d,hd,?_⟩
      exact (hrep d.edge d.edge_mem).unique ⟨hS,hde.symm⟩ ⟨(hR d).1,hmap d⟩
  refine ⟨RoutingTemplate.ofCycle c,he,?_,?_,?_⟩
  · change Fintype.card c.Switch ≤ M
    apply le_trans _ hM
    apply Finset.card_le_card_of_injOn (fun i : c.Switch => i.val)
    · intro z hz; exact List.mem_toFinset.mpr z.property.1
    · intro z _ w _ h; exact Subtype.ext h
  · exact c.vertices_card_support.trans (Nat.mul_le_mul_left _ hM)
  · intro i
    change c.Switch at i
    exact (c.projects i i.property.1).1.trans (c.projects i i.property.1).2.symm

theorem quotient_part_template_on {V W : Type} [Fintype W]
    {G : SimpleGraph V} {Q : SimpleGraph W} (projMap : V → W)
    (S : Set (Sym2 V)) (hSG : S ⊆ G.edgeSet)
    (A : Finset W) (hA : ∀ ⦃x y⦄, Q.Adj x y → x ∈ A ∧ y ∈ A)
    (hrep : ∀ e ∈ Q.edgeSet, ∃! f, f ∈ S ∧ Sym2.map projMap f = e)
    (s : Set (Sym2 W)) (hs : CycleOrSingleEdge Q s) :
    ∃ b : RoutingTemplate G,
      b.edges = {e | e ∈ S ∧ Sym2.map projMap e ∈ s} ∧
      Fintype.card b.Arity ≤ A.card ∧
      b.vertices.card ≤ 2*A.card ∧
      ∀ i, projMap (b.x i) = projMap (b.y i) := by
  rcases hs with ⟨a,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact cycle_template_of_representatives_bounded projMap S hSG hrep p hp A.card (by
      apply Finset.card_le_card
      intro z hz
      rw [List.mem_toFinset,p.support_dropLast hp.not_nil,← Walk.map_fst_darts] at hz
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hz
      exact (hA d.adj).1)
  · obtain ⟨f,hf,huniq⟩ := hrep e he
    refine ⟨RoutingTemplate.ofSingle f (hSG hf.1),?_,by change Fintype.card Empty ≤ _; simp,by simp [RoutingTemplate.ofSingle],fun i => i.elim⟩
    ext g
    change g = f ↔ g ∈ S ∧ Sym2.map projMap g ∈ ({e} : Set (Sym2 W))
    constructor
    · intro h; subst g; exact ⟨hf.1,hf.2⟩
    · rintro ⟨hg,hge⟩; exact huniq g ⟨hg,hge⟩

theorem quotient_partition_templates_on {V W : Type} [Fintype W]
    {G : SimpleGraph V} {Q : SimpleGraph W} (projMap : V → W)
    (S : Set (Sym2 V)) (hSG : S ⊆ G.edgeSet)
    (A : Finset W) (hA : ∀ ⦃x y⦄, Q.Adj x y → x ∈ A ∧ y ∈ A)
    (himage : Sym2.map projMap '' S = Q.edgeSet)
    (hrep : ∀ e ∈ Q.edgeSet, ∃! f, f ∈ S ∧ Sym2.map projMap f = e)
    {k : ℕ} (hQ : EdgeDecomposition Q k) :
    ∃ b : Fin k → RoutingTemplate G,
      Pairwise (fun i j => Disjoint (b i).edges (b j).edges) ∧
      (⋃ i, (b i).edges) = S ∧
      (∀ i, Fintype.card (b i).Arity ≤ A.card ∧
        (b i).vertices.card ≤ 2*A.card ∧
        ∀ j, projMap ((b i).x j) = projMap ((b i).y j)) := by
  classical
  obtain ⟨parts,hp,hd,hcover⟩ := hQ
  choose b hb hnum hv hprojMap using fun i => quotient_part_template_on projMap S hSG A hA hrep (parts i) (hp i)
  refine ⟨b,?_,?_,fun i => ⟨hnum i,hv i,hprojMap i⟩⟩
  · intro i j hij
    rw [hb i,hb j]
    exact Set.disjoint_left.mpr (fun _ hi hj => Set.disjoint_left.mp (hd hij) hi.2 hj.2)
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; rw [hb i] at hi; exact hi.1
    · intro he
      have hq : Sym2.map projMap e ∈ Q.edgeSet := by rw [← himage]; exact Set.mem_image_of_mem _ he
      rw [← hcover] at hq
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hq
      exact ⟨i,by rw [hb i]; exact ⟨he,hi⟩⟩

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open _root_.Finset _root_.SimpleGraph
attribute [local instance] Classical.propDecidable

lemma walk_support_on {V : Type} {G : SimpleGraph V} (W : Finset V)
    (hW : ∀ ⦃x y⦄, G.Adj x y → x ∈ W ∧ y ∈ W)
    {x y : V} (p : G.Walk x y) (hp : 0 < p.length) : p.support.toFinset ⊆ W := by
  classical
  intro v hv
  obtain ⟨e,he,hv⟩ := Walk.mem_support_iff_exists_mem_edges_of_not_nil
    (p := p) (by simpa only [Walk.length_eq_zero_iff.symm] using (Nat.ne_of_gt hp)) |>.mp (List.mem_toFinset.mp hv)
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := p.edges_subset_edgeSet he
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact (hW hab).1
    · exact (hW hab).2

structure BatchTemplateFamily {V I : Type} [Fintype I]
    (G J : SimpleGraph V) (X : I → Finset V) (W : Finset V) (bad : Finset (Sym2 V)) (k : ℕ) where
  Index : Type
  finiteIndex : Fintype Index
  block : Index → RoutingTemplate G
  count : Fintype.card Index ≤ k + 2 * ∑ i, (X i).card
  disjoint : Pairwise fun i j => Disjoint (block i).edges (block j).edges
  bad_disjoint : ∀ i, Disjoint (bad : Set (Sym2 V)) (block i).edges
  cover : (bad : Set (Sym2 V)) ∪ (⋃ i, (block i).edges) = J.edgeSet
  arity : ∀ i, Fintype.card (block i).Arity ≤ W.card
  vertices : ∀ i, (block i).vertices.card ≤ 2*W.card
  owner : (i : Index) → (block i).Arity → I
  ends : ∀ i j, (block i).x j ∈ X (owner i j) ∧ (block i).y j ∈ X (owner i j)
attribute [instance] BatchTemplateFamily.finiteIndex

lemma BatchTemplateFamily.subset {V I : Type} [Fintype I]
    {G J : SimpleGraph V} {X : I → Finset V} {W bad k}
    (b : BatchTemplateFamily G J X W bad k) (i : b.Index) : (b.block i).edges ⊆ J.edgeSet := by
  rw [← b.cover]
  intro e he; exact Or.inr (Set.mem_iUnion.mpr ⟨i,he⟩)

theorem prepare_templates {V I : Type} [Fintype V] [Fintype I]
    (G J : SimpleGraph V) (hJG : J ≤ G) (W : Finset V)
    (hW : ∀ ⦃x y⦄, J.Adj x y → x ∈ W ∧ y ∈ W)
    (X : I → Finset V) (hd : Pairwise fun i j => Disjoint (X i) (X j))
    (hX : ∀ i, X i ⊆ W) (b : PreparedBatch J X hd)
    {k : ℕ} (hk : EdgeDecomposition b.quotient k) :
    Nonempty (BatchTemplateFamily G J X W b.bad k) := by
  classical
  let projMap := familyProject X hd b.pairing
  let A := W.image projMap
  have hAW : A.card ≤ W.card := Finset.card_image_le
  obtain ⟨q,hqd,hqu,hqn⟩ := quotient_partition_templates_on projMap (b.retained:Set (Sym2 V))
    (b.retained_subset.trans (SimpleGraph.edgeSet_mono hJG)) A (b.quotient_supported W hW)
    b.quotient_edges.symm (by simpa only [Finset.mem_coe] using b.representatives) hk
  have hqsub (j) : (q j).edges ⊆ (b.retained : Set (Sym2 V)) := by
    rw [← hqu]; intro e he; exact Set.mem_iUnion.mpr ⟨j,he⟩
  have hex (j) (i : (q j).Arity) : ∃ r, (q j).x i ∈ X r ∧ (q j).y i ∈ X r := by
    obtain he | ⟨r,hx,hy,_⟩ := (familyProject_eq_iff X hd b.pairing _ _).mp ((hqn j).2.2 i)
    · exact False.elim ((q j).ne i he)
    · exact ⟨r,hx,hy⟩
  choose own hown using hex
  let P := {z : Σ i, Fin (b.count i) // 0 < (b.path z.1 z.2).walk.length}
  let path : ∀ z : P, G.Walk (b.path z.1.1 z.1.2).start (b.path z.1.1 z.1.2).finish :=
    fun z => (b.path z.1.1 z.1.2).walk.map (SimpleGraph.Hom.ofLE hJG)
  have hpe (z : P) : (path z).edgeSet = (b.path z.1.1 z.1.2).walk.edgeSet := by
    simp [path,Walk.edgeSet_map,SimpleGraph.Hom.ofLE]
  have hps (z : P) : (path z).IsPath := (b.path z.1.1 z.1.2).simple.map Function.injective_id
  have hpl (z : P) : 2 ≤ (path z).length := by
    simpa only [path,Walk.length_map] using (b.ends z.1.1 z.1.2 z.property).2.2
  let t : P → RoutingTemplate G := fun z => RoutingTemplate.ofPath (path z) (hps z) (hpl z)
  have hte (z : P) : (t z).edges = (b.path z.1.1 z.1.2).walk.edgeSet := hpe z
  have htv (z : P) : (t z).vertices.card ≤ W.card := by
    apply Finset.card_le_card
    change (path z).support.toFinset ⊆ W
    simpa [path,Walk.support_map,SimpleGraph.Hom.ofLE] using
      walk_support_on W hW (b.path z.1.1 z.1.2).walk z.property
  have hta (z : P) : Fintype.card (t z).Arity ≤ W.card := by
    change Fintype.card Unit ≤ W.card
    simpa using Finset.card_pos.mpr ⟨(b.path z.1.1 z.1.2).start,
      hX z.1.1 (b.ends z.1.1 z.1.2 z.property).1⟩
  have htu : (⋃ z, (t z).edges) = ⋃ i, ⋃ j, (b.path i j).walk.edgeSet := by
    ext e; simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨z,hz⟩; exact ⟨z.1.1,z.1.2,(hte z) ▸ hz⟩
    · rintro ⟨i,j,hj⟩
      have hp : 0 < (b.path i j).walk.length := by
        by_contra h
        have hn := Walk.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h)
        have he := Walk.edges_eq_nil.mpr hn
        change e ∈ (b.path i j).walk.edges at hj
        rw [he] at hj; contradiction
      exact ⟨⟨⟨i,j⟩,hp⟩,by rw [hte]; exact hj⟩
  refine ⟨{
    Index := Fin k ⊕ P,
    finiteIndex := inferInstance,
    block := Sum.elim q t,
    count := ?_,
    disjoint := ?_,
    bad_disjoint := ?_,
    cover := ?_,
    arity := ?_,
    vertices := ?_,
    owner := fun j => match j with | Sum.inl j => own j | Sum.inr z => fun _ => z.1.1,
    ends := ?_
  }⟩
  · have hp : Fintype.card P ≤ 2 * ∑ i, (X i).card := by
      calc
        _ ≤ Fintype.card (Σ i, Fin (b.count i)) := Fintype.card_subtype_le _
        _ = ∑ i, b.count i := by simp
        _ ≤ ∑ i, 2*(X i).card := Finset.sum_le_sum (fun i _ => b.count_le i)
        _ = _ := by rw [← Finset.mul_sum]
    simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_left hp k
  · intro j l hne
    rcases j with j | j <;> rcases l with l | l <;> dsimp only [Sum.elim_inl,Sum.elim_inr]
    · exact hqd (fun h => hne (congrArg Sum.inl h))
    · exact (b.retained_paths l.1.1 l.1.2).mono (hqsub j) (by rw [hte])
    · exact ((b.retained_paths j.1.1 j.1.2).mono (hqsub l) (by rw [hte])).symm
    · rw [hte,hte]
      exact b.paths_disjoint (fun h => hne (congrArg Sum.inr (Subtype.ext h)))
  · rintro (j | z) <;> dsimp only [Sum.elim_inl,Sum.elim_inr]
    · exact b.bad_retained.mono_right (hqsub j)
    · rw [hte]; exact b.bad_paths _ _
  ·
    simp only [Set.iUnion_sum,Sum.elim_inl,Sum.elim_inr]
    rw [hqu,htu,← Set.union_assoc]
    exact b.cover
  · rintro (j | z)
    · exact (hqn j).1.trans hAW
    · exact hta z
  · rintro (j | z)
    · exact (hqn j).2.1.trans (Nat.mul_le_mul_left _ hAW)
    · exact (htv z).trans (by omega)
  · rintro (j | z) i
    · exact hown j i
    · exact ⟨(b.ends z.1.1 z.1.2 z.property).2.1,(b.ends z.1.1 z.1.2 z.property).1⟩

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable

theorem uniform_batch_resolution :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V R B : Type) [Fintype V] [Fintype R] [Fintype B],
      ∀ (G F : SimpleGraph V) (P : R → SimpleGraph V) (U : R → Finset V),
      F ≤ G → (∀ r, P r ≤ G) →
      Pairwise (fun r s => Disjoint (P r).edgeSet (P s).edgeSet) →
      Pairwise (fun r s => Disjoint (U r) (U s)) →
      (∀ r, Disjoint F.edgeSet (P r).edgeSet) →
      (∀ r, CutExpansionOn (P r) (U r) (D^(9/10:ℝ)/4)) →
      (∀ r, D^(9/10:ℝ) ≤ ((U r).card:ℝ) ∧ ((U r).card:ℝ) ≤ D^(51/50:ℝ)) →
      ∀ (J : B → SimpleGraph V) (W : B → Finset V),
      (∀ b, J b ≤ F) → Pairwise (fun b c => Disjoint (J b).edgeSet (J c).edgeSet) →
      (⋃ b, (J b).edgeSet) = F.edgeSet →
      (∀ b, ∀ ⦃x y⦄, (J b).Adj x y → x ∈ W b ∧ y ∈ W b) →
      (∀ b, ((W b).card:ℝ) ≤ D^(3/10:ℝ)) →
      ∀ (I : B → Type) [∀ b, Fintype (I b)] (X : ∀ b, I b → Finset V)
        (hXd : ∀ b, Pairwise fun i j => Disjoint (X b i) (X b j)),
      (∀ b i, X b i ⊆ W b) →
      ∀ rX : ∀ b, I b → R,
      (∀ b i, X b i ⊆ U (rX b i)) →
      (∀ b i v, v ∈ X b i → (F.degree v:ℝ) ≤ D^(1/100:ℝ)) →
      ∀ (prep : ∀ b, PreparedBatch (J b) (X b) (hXd b)) (k : B → ℕ),
      (∀ b, EdgeDecomposition (prep b).quotient (k b)) →
      ∃ (K : Type) (_ : Fintype K) (parts : K → Set (Sym2 V)) (used : Set (Sym2 V)),
        Fintype.card K ≤ (∑ b, k b) + 8 * ∑ b, ∑ i, (X b i).card ∧
        (∀ j, CycleOrSingleEdge G (parts j)) ∧
        Pairwise (fun j l => Disjoint (parts j) (parts l)) ∧
        used ⊆ ⋃ r, (P r).edgeSet ∧ Disjoint F.edgeSet used ∧
        (⋃ j, parts j) = F.edgeSet ∪ used := by
  classical
  obtain ⟨D₀,hD₀,hresolve⟩ := uniform_resolve_templates
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V R B _ _ _ G F P U hFG hPG hPP hUU hFP he hr J W hJF hJJ hJu hW hWnum I _ X hXd hXW rX hXU hdeg prep k hk
  have hT (b : B) := prepare_templates G (J b) ((hJF b).trans hFG) (W b) (hW b)
    (X b) (hXd b) (hXW b) (prep b) (hk b)
  let T : ∀ b, BatchTemplateFamily G (J b) (X b) (W b) (prep b).bad (k b) :=
    fun b => Classical.choice (hT b)
  let Q := Σ b, (T b).Index
  let q : Q → RoutingTemplate G := fun z => (T z.1).block z.2
  have hqsub (z : Q) : (q z).edges ⊆ F.edgeSet :=
    ((T z.1).subset z.2).trans (SimpleGraph.edgeSet_mono (hJF z.1))
  have hqd : Pairwise fun z w : Q => Disjoint (q z).edges (q w).edges := by
    rintro ⟨b,i⟩ ⟨c,j⟩ hne
    by_cases hh : b = c
    · subst c; exact (T b).disjoint (fun h => hne (by cases h; rfl))
    · exact (hJJ hh).mono ((T b).subset i) ((T c).subset j)
  let owner : (z : Q) → (q z).Arity → R := fun z i => rX z.1 ((T z.1).owner z.2 i)
  obtain ⟨parts,used,hparts,hpartsd,hused,hFu,hcover⟩ :=
    hresolve D hD V R Q G F P U hFG hPG hPP hUU hFP he hr q hqsub hqd owner
      (fun z i => ⟨hXU _ _ ((T z.1).ends z.2 i).1,hXU _ _ ((T z.1).ends z.2 i).2⟩)
      (fun z i => ⟨hdeg _ _ _ ((T z.1).ends z.2 i).1,hdeg _ _ _ ((T z.1).ends z.2 i).2⟩)
      (fun z => (Nat.cast_le.mpr ((T z.1).arity z.2)).trans (hWnum z.1))
      (fun z => (Nat.cast_le.mpr ((T z.1).vertices z.2)).trans (by
        push_cast; exact mul_le_mul_of_nonneg_left (hWnum z.1) (by norm_num)))
  let S := Σ b, (prep b).bad
  let e : S → Sym2 V := fun z => z.2.val
  have hSsub (z : S) : e z ∈ (J z.1).edgeSet := (prep z.1).bad_subset z.2.property
  have hSF (z : S) : e z ∈ F.edgeSet := SimpleGraph.edgeSet_mono (hJF z.1) (hSsub z)
  have hinj : Function.Injective e := by
    rintro ⟨b,i⟩ ⟨c,j⟩ h
    by_cases hh : b = c
    · subst c; exact Sigma.ext rfl (heq_of_eq (Subtype.ext h))
    · exact False.elim (Set.disjoint_left.mp (hJJ hh) (hSsub ⟨b,i⟩) (h ▸ hSsub ⟨c,j⟩))
  have hbadq (z : S) (w : Q) : e z ∉ (q w).edges := by
    intro hw
    by_cases hh : z.1 = w.1
    · rcases z with ⟨b,z⟩; rcases w with ⟨c,w⟩
      dsimp only at hh; subst c
      exact Set.disjoint_left.mp ((T b).bad_disjoint w) z.property hw
    · exact Set.disjoint_left.mp (hJJ hh) (hSsub z) ((T w.1).subset w.2 hw)
  have hbadpart (z : S) (w : Q) : e z ∉ parts w := by
    intro hw
    have hu : e z ∈ ⋃ w, parts w := Set.mem_iUnion.mpr ⟨w,hw⟩
    rw [hcover] at hu
    rcases hu with hu | hu
    · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hu; exact hbadq z w hw
    · exact Set.disjoint_left.mp hFu (hSF z) hu
  have horiginal : (⋃ z : S, {e z}) ∪ (⋃ w : Q, (q w).edges) = F.edgeSet := by
    rw [← hJu]
    ext f
    simp only [Set.mem_union,Set.mem_iUnion,Set.mem_singleton_iff]
    constructor
    · rintro (⟨z,hz⟩ | ⟨w,hw⟩)
      · exact ⟨z.1,hz ▸ hSsub z⟩
      · exact ⟨w.1,(T w.1).subset w.2 hw⟩
    · rintro ⟨b,hb⟩
      rw [← (T b).cover] at hb
      rcases hb with hb | hb
      · exact Or.inl ⟨⟨b,⟨f,hb⟩⟩,rfl⟩
      · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hb
        exact Or.inr ⟨⟨b,j⟩,hj⟩
  refine ⟨Q ⊕ S,inferInstance,Sum.elim parts (fun z => {e z}),used,?_,?_,?_,hused,hFu,?_⟩
  · have hq : Fintype.card Q ≤ (∑ b, k b) + 2*∑ b, ∑ i, (X b i).card := by
      calc
        _ = ∑ b, Fintype.card (T b).Index := Fintype.card_sigma
        _ ≤ ∑ b, (k b + 2 * ∑ i, (X b i).card) := Finset.sum_le_sum (fun b _ => (T b).count)
        _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum]
    have hs : Fintype.card S ≤ 6*∑ b, ∑ i, (X b i).card := by
      calc
        _ = ∑ b, (prep b).bad.card := by simp [S,Fintype.card_sigma]
        _ ≤ ∑ b, 6*∑ i, (X b i).card := Finset.sum_le_sum (fun b _ => (prep b).bad_le)
        _ = _ := by rw [← Finset.mul_sum]
    rw [Fintype.card_sum]; omega
  · rintro (j | z)
    · exact hparts j
    · exact Or.inr ⟨e z,SimpleGraph.edgeSet_mono hFG (hSF z),rfl⟩
  · rintro (i | i) (j | j) hij <;> dsimp only [Sum.elim_inl,Sum.elim_inr]
    · exact hpartsd (fun h => hij (congrArg Sum.inl h))
    · exact (Set.disjoint_singleton_right).mpr (hbadpart j i)
    · exact (Set.disjoint_singleton_left).mpr (hbadpart i j)
    · exact Set.disjoint_singleton.mpr (fun h => hij (congrArg Sum.inr (hinj h)))
  · simp only [Set.iUnion_sum,Sum.elim_inl,Sum.elim_inr]
    rw [hcover]
    calc
      _ = ((⋃ z : S, {e z}) ∪ (⋃ w : Q, (q w).edges)) ∪ used := by
        rw [Set.union_comm ((⋃ w : Q, (q w).edges) ∪ used), Set.union_assoc]
      _ = _ := by rw [horiginal]

end
end ErdosGallai.Batch

end
/-! ### Upstream module `Combinatorics/CycleDecomposition/CoupledResolution.lean` -/

section
open _root_.Filter _root_.Asymptotics _root_.Real
open scoped _root_.Topology
noncomputable section
open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Finset
namespace ErdosGallai.Batch.Splitting
section BernoulliBounds
variable {Ω : Type cycleUniverse1} {I : Type cycleUniverse2} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma indicator_mem_Icc {Ω : Type cycleUniverse3} [_contextInstance1 : MeasurableSpace Ω] {X : Ω → ℝ} (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (ω : Ω) :
    X ω ∈ Set.Icc (0 : ℝ) 1 := by rcases hX ω with h | h <;> simp [h]

lemma mgf_indicator {X : Ω → ℝ} (hm : Measurable X)
    (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (p t : ℝ) (hp : ∫ ω, X ω ∂μ = p) :
    mgf X μ t = 1 + p * (exp t - 1) := by
  have hXi : Integrable X μ := Integrable.of_mem_Icc 0 1 hm.aemeasurable
    (ae_of_all _ (indicator_mem_Icc hX))
  have heq : (fun ω => exp (t * X ω)) = fun ω => (1 : ℝ) + (exp t - 1) * X ω := by
    funext ω
    rcases hX ω with h | h <;> simp [h]
  rw [mgf, heq, integral_add (integrable_const _) (hXi.const_mul _), integral_const_mul,
    hp, integral_const]
  simp [mul_comm]

lemma mgf_indicator_sum_bound {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p t : ℝ) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    mgf (∑ i ∈ s, X i) μ t ≤ exp ((s.card : ℝ) * p * (exp t - 1)) := by
  by_cases hs : s.Nonempty
  swap
  · have he := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]
  rw [hi.mgf_sum hm]
  have heq : (∏ i ∈ s, mgf (X i) μ t) = (1 + p * (exp t - 1)) ^ s.card := by
    simp_rw [mgf_indicator (hm _) (hX _) p t (hp _)]
    simp
  rw [heq]
  have hn : 0 ≤ 1 + p * (exp t - 1) := by
    obtain ⟨i, _⟩ := hs
    rw [← mgf_indicator (hm i) (hX i) p t (hp i)]
    exact mgf_nonneg
  calc
    (1 + p * (exp t - 1)) ^ s.card ≤ exp (p * (exp t - 1)) ^ s.card :=
      pow_le_pow_left₀ hn (by linarith [add_one_le_exp (p * (exp t - 1))]) _
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

lemma exp_neg_half_bound : exp (-(1 / 2 : ℝ)) ≤ 5 / 8 := by
  have he : exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) = exp 1 := by
    rw [← exp_add]; norm_num
  have hlow : (8 / 5 : ℝ) ≤ exp (1 / 2 : ℝ) := by
    nlinarith [exp_one_gt_d9, exp_pos (1 / 2 : ℝ)]
  rw [exp_neg]
  exact (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by norm_num at *; exact hlow)

theorem bernoulli_sum_lower_tail {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | (∑ i ∈ s, X i ω) ≤ p * s.card / 2} ≤ exp (-p * s.card / 8) := by
  have hInt : Integrable (fun ω => exp (-(1 / 2 : ℝ) * (∑ i ∈ s, X i) ω)) μ :=
    hi.integrable_exp_mul_sum hm (fun i _ => integrable_exp_mul_of_mem_Icc
      (hm i).aemeasurable (ae_of_all _ (indicator_mem_Icc (hX i))))
  have hb := measure_le_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (p * s.card / 2)
    (by norm_num : -(1 / 2 : ℝ) ≤ 0) hInt
  simp only [Finset.sum_apply] at hb
  apply hb.trans
  calc
    _ ≤ exp (-(-(1 / 2 : ℝ)) * (p * s.card / 2)) *
        exp ((s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      exact mul_le_mul_of_nonneg_left (mgf_indicator_sum_bound s hm hi hX p _ hp) (exp_pos _).le
    _ = exp (p * s.card / 4 + (s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_neg_half_bound
        (mul_nonneg (Nat.cast_nonneg s.card) hp0)]

end BernoulliBounds

noncomputable section
variable {V : Type cycleUniverse4} [Fintype V] [DecidableEq V]

def CutExpansion (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ) : Prop :=
  ∀ U : Finset V, h * min (U.card : ℝ) (Uᶜ.card : ℝ) ≤
    ((P.interedges U Uᶜ).card : ℝ)

lemma boundary_sym2_injective (P : SimpleGraph V) [DecidableRel P.Adj]
    (U : Finset V) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges U Uᶜ : Set (V × V)) := by
  intro e he f hf hef
  rcases (Sym2.mk_eq_mk_iff.mp hef) with h | h
  · exact h
  · have he1 := (P.mem_interedges_iff.mp he).1
    have hf2 := (P.mem_interedges_iff.mp hf).2.1
    have hfirst : e.1 = f.2 := congrArg Prod.fst h
    exact False.elim ((Finset.mem_compl.mp hf2) (hfirst ▸ he1))

def edgeColorMeasure (V : Type cycleUniverse5) [Fintype V] (l : ℕ) [NeZero l] :
    Measure (Sym2 V → Fin l) :=
  Measure.pi (fun _ : Sym2 V => (PMF.uniformOfFintype (Fin l)).toMeasure)

instance edgeColorMeasure_probability (l : ℕ) [NeZero l] :
    IsProbabilityMeasure (edgeColorMeasure V l) := by
  unfold edgeColorMeasure
  infer_instance

def colorIndicator {l : ℕ} (i : Fin l) (e : Sym2 V) (ω : Sym2 V → Fin l) : ℝ :=
  if ω e = i then 1 else 0

lemma colorIndicator_indep {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {l : ℕ} [NeZero l] (i : Fin l) :
    iIndepFun (colorIndicator (V := V) i) (edgeColorMeasure V l) := by
  exact iIndepFun_pi (X := fun _ : Sym2 V => fun j : Fin l => if j = i then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)

lemma colorIndicator_integral {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {l : ℕ} [NeZero l] (i : Fin l) (e : Sym2 V) :
    ∫ ω, colorIndicator i e ω ∂edgeColorMeasure V l = 1/(l : ℝ) := by
  have hl := (measurePreserving_eval
    (fun _ : Sym2 V => (PMF.uniformOfFintype (Fin l)).toMeasure) e).hasLaw
  have hi := hl.integral_comp (f := fun j : Fin l => if j = i then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable
  rw [PMF.integral_eq_sum] at hi
  simpa [edgeColorMeasure, colorIndicator, PMF.uniformOfFintype_apply] using hi

def colorGraph (P : SimpleGraph V) {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) :
    SimpleGraph V where
  Adj x y := P.Adj x y ∧ ω s(x,y) = i
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro x h; exact P.irrefl h.1⟩

instance colorGraph_decidable (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) :
    DecidableRel (colorGraph P ω i).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

lemma colorGraph_interedges {V : Type cycleUniverse8} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) (S T : Finset V) :
    (colorGraph P ω i).interedges S T =
      (P.interedges S T).filter (fun e => ω s(e.1,e.2) = i) := by
  ext ⟨x,y⟩
  simp only [SimpleGraph.mem_interedges_iff, Finset.mem_filter]
  change (x ∈ S ∧ y ∈ T ∧ (P.Adj x y ∧ ω s(x,y) = i)) ↔ _
  tauto

lemma color_cut_sum (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) (S : Finset V) :
    (∑ e ∈ (P.interedges S Sᶜ).image (fun e => s(e.1,e.2)), colorIndicator i e ω) =
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) := by
  rw [Finset.sum_image (boundary_sym2_injective P S)]
  simp only [colorIndicator, Finset.sum_boole, colorGraph_interedges]

lemma color_cut_lower_tail (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] (i : Fin l) (S : Finset V) {h : ℝ}
    (hexp : CutExpansion P h) (hS : S.card ≤ Sᶜ.card) :
    (edgeColorMeasure V l).real {ω |
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} ≤
        exp (-h*S.card/(8*l)) := by
  let E := (P.interedges S Sᶜ).image (fun e => s(e.1,e.2))
  have hcard : E.card = (P.interedges S Sᶜ).card :=
    Finset.card_image_of_injOn (boundary_sym2_injective P S)
  have hl : 0 < (l : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne l)
  have hcut : h * S.card ≤ (E.card : ℝ) := by
    rw [hcard]
    have he := hexp S
    rwa [min_eq_left (by exact_mod_cast hS)] at he
  have hb := bernoulli_sum_lower_tail (μ := edgeColorMeasure V l) E
    (fun e => measurable_of_finite (colorIndicator i e)) (colorIndicator_indep i)
    (fun e ω => by simp only [colorIndicator]; split <;> simp)
    (1/(l : ℝ)) (by positivity) (colorIndicator_integral i)
  apply (measureReal_mono (show {ω |
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} ⊆
      {ω | (∑ e ∈ E, colorIndicator i e ω) ≤ (1/(l : ℝ))*E.card/2} from ?_)).trans
      (hb.trans ?_)
  · intro ω hω
    change (∑ e ∈ E, colorIndicator i e ω) ≤ (1/(l : ℝ))*E.card/2
    rw [show (∑ e ∈ E, colorIndicator i e ω) =
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) from color_cut_sum P ω i S]
    calc
      _ ≤ h*S.card/(2*l) := le_of_lt hω
      _ ≤ (E.card : ℝ)/(2*l) := div_le_div_of_nonneg_right hcut (by positivity)
      _ = _ := by ring
  · apply exp_le_exp.mpr
    have he := div_le_div_of_nonneg_right hcut (show 0 ≤ 8*(l : ℝ) by positivity)
    calc
      _ = -((E.card : ℝ)/(8*l)) := by ring
      _ ≤ -(h*S.card/(8*l)) := neg_le_neg he
      _ = _ := by ring

lemma cutExpansion_of_small_cuts (P : SimpleGraph V) [DecidableRel P.Adj] {h : ℝ}
    (hcut : ∀ S : Finset V, S.Nonempty → S.card ≤ Sᶜ.card →
      h*S.card ≤ ((P.interedges S Sᶜ).card : ℝ)) : CutExpansion P h := by
  intro S
  by_cases he : S = ∅
  · simp [he]
  by_cases hc : Sᶜ = ∅
  · simp [hc]
  by_cases hs : S.card ≤ Sᶜ.card
  · rw [min_eq_left (by exact_mod_cast hs)]
    exact hcut S (Finset.nonempty_iff_ne_empty.mpr he) hs
  · rw [min_eq_right (by exact_mod_cast le_of_not_ge hs)]
    have hi := hcut Sᶜ (Finset.nonempty_iff_ne_empty.mpr hc) (by simpa using le_of_not_ge hs)
    have hcomm : (P.interedges Sᶜ S).card = (P.interedges S Sᶜ).card := by
      have := P.symm
      exact Rel.card_interedges_comm Sᶜ S
    simpa only [compl_compl, hcomm] using hi

lemma sum_nonempty_subsets_power (q : ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Finset V)).erase ∅, q^S.card) =
      (1+q)^(Fintype.card V)-1 := by
  have hs := Finset.sum_erase_add (s := Finset.univ) (fun S : Finset V => q^S.card)
    (Finset.mem_univ (∅ : Finset V))
  have hp := Finset.prod_one_add (s := (Finset.univ : Finset V)) (f := fun _ => q)
  simp only [Finset.prod_const, Finset.card_univ, Finset.powerset_univ] at hp
  simp only [Finset.card_empty, pow_zero] at hs
  linarith

theorem edge_splitting_failure_bound (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] {h : ℝ} (hexp : CutExpansion P h) :
    (edgeColorMeasure V l).real {ω | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} ≤
      l * (exp ((Fintype.card V : ℝ)*exp (-h/(8*l)))-1) := by
  let cuts : Finset (Finset V) := Finset.univ.erase ∅
  let B (i : Fin l) (S : Finset V) : Set (Sym2 V → Fin l) :=
    {ω | S.card ≤ Sᶜ.card ∧
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)}
  let q : ℝ := exp (-h/(8*l))
  have cover : {ω | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin l)), ⋃ S ∈ cuts, B i S := by
    intro ω hω
    rcases hω with ⟨i, hi⟩
    by_contra hn
    apply hi
    apply cutExpansion_of_small_cuts
    intro S hS hs
    have hb : ω ∉ B i S := by
      intro hm
      apply hn
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ _,
        Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr
          ⟨Finset.mem_erase.mpr ⟨hS.ne_empty, Finset.mem_univ _⟩, hm⟩⟩⟩⟩
    have hc : h*S.card/(2*l) ≤ (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) := by
      exact le_of_not_gt (fun hf => hb ⟨hs, hf⟩)
    convert hc using 1 ; ring
  have hbound (i : Fin l) (S : Finset V) :
      (edgeColorMeasure V l).real (B i S) ≤ q^S.card := by
    by_cases hs : S.card ≤ Sᶜ.card
    · calc
        _ ≤ (edgeColorMeasure V l).real {ω |
            (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} :=
          measureReal_mono (fun _ hw => hw.2)
        _ ≤ exp (-h*S.card/(8*l)) := color_cut_lower_tail P i S hexp hs
        _ = q^S.card := by dsimp [q]; rw [← exp_nat_mul]; congr 1; ring
    · have he : B i S = ∅ := by ext ω; simp [B,hs]
      rw [he, measureReal_empty]
      exact pow_nonneg (exp_pos _).le _
  calc
    _ ≤ (edgeColorMeasure V l).real
        (⋃ i ∈ (Finset.univ : Finset (Fin l)), ⋃ S ∈ cuts, B i S) :=
      measureReal_mono cover (measure_ne_top _ _)
    _ ≤ ∑ i : Fin l, (edgeColorMeasure V l).real (⋃ S ∈ cuts, B i S) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ i : Fin l, ∑ S ∈ cuts, (edgeColorMeasure V l).real (B i S) :=
      Finset.sum_le_sum (fun _ _ => measureReal_biUnion_finset_le _ _)
    _ ≤ ∑ _i : Fin l, ∑ S ∈ cuts, q^S.card := by
      apply Finset.sum_le_sum; intro i _; exact Finset.sum_le_sum (fun S _ => hbound i S)
    _ = (l : ℝ)*((1+q)^(Fintype.card V)-1) := by
      simp only [cuts, sum_nonempty_subsets_power, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    _ ≤ l*(exp ((Fintype.card V : ℝ)*q)-1) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg l)
      apply sub_le_sub_right
      calc
        _ ≤ (exp q)^(Fintype.card V) :=
          pow_le_pow_left₀ (by dsimp [q]; positivity) (by linarith [add_one_le_exp q]) _
        _ = _ := (exp_nat_mul _ _).symm

theorem edge_splitting_of_error_lt_one (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] {h : ℝ} (hexp : CutExpansion P h)
    (herror : (l : ℝ)*(exp ((Fintype.card V : ℝ)*exp (-h/(8*l)))-1) < 1) :
    ∃ ω : Sym2 V → Fin l,
      (∀ i, CutExpansion (colorGraph P ω i) (h/(2*l))) ∧
      (∀ x y, P.Adj x y ↔ ∃ i, (colorGraph P ω i).Adj x y) ∧
      (∀ i j, i ≠ j → Disjoint (colorGraph P ω i).edgeSet (colorGraph P ω j).edgeSet) := by
  have he := (edge_splitting_failure_bound P hexp).trans_lt herror
  have hh : ∃ ω : Sym2 V → Fin l, ∀ i, CutExpansion (colorGraph P ω i) (h/(2*l)) := by
    by_contra hn
    push Not at hn
    have hall : {ω : Sym2 V → Fin l | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} =
        Set.univ := Set.eq_univ_of_forall hn
    simp only [hall, Measure.real, measure_univ, ENNReal.toReal_one] at he
    exact (lt_irrefl _ he)
  obtain ⟨ω, hω⟩ := hh
  refine ⟨ω, hω, ?_, ?_⟩
  · intro x y
    exact ⟨fun hxy => ⟨ω s(x,y), hxy, rfl⟩, fun ⟨_, hxy, _⟩ => hxy⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro e hei hej
    induction e using Sym2.ind with | _ x y =>
      have hi : (colorGraph P ω i).Adj x y := by simpa using hei
      have hj : (colorGraph P ω j).Adj x y := by simpa using hej
      exact hij (hi.2.symm.trans hj.2)

end

lemma tendsto_monomial_exp_neg_power (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun D : ℝ => D^a * exp (-c * D^b)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a/b) c hc).comp
    (tendsto_rpow_atTop hb)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul hD.le, mul_div_cancel₀ _ hb.ne']

noncomputable def edgeSplittingScaleError (c : ℝ) (l : ℕ) (D : ℝ) : ℝ :=
  (l : ℝ) * (Real.exp (D^(51/50 : ℝ) * Real.exp ((-(c / (8*l))) * D^(9/10 : ℝ))) - 1)

lemma edgeSplittingScaleError_tendsto (c : ℝ) (hc : 0 < c) (l : ℕ) (hl : 0 < l) :
    Tendsto (edgeSplittingScaleError c l) atTop (𝓝 0) := by
  have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
  have ht := tendsto_monomial_exp_neg_power (51/50) (9/10) (c/(8*l))
    (by norm_num) (by positivity)
  have hh := ((Real.continuous_exp.tendsto 0).comp ht).sub_const 1 |>.const_mul (l : ℝ)
  unfold edgeSplittingScaleError
  convert hh using 1 <;> norm_num

theorem edge_splitting_uniform (c : ℝ) (hc : 0 < c) (l : ℕ) (hl : 0 < l) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ),
      c*D^(9/10 : ℝ) ≤ h → D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) → CutExpansion P h →
      ∃ ω : Sym2 V → Fin l,
        (∀ i, CutExpansion (colorGraph P ω i) (h/(2*l))) ∧
        (∀ x y, P.Adj x y ↔ ∃ i, (colorGraph P ω i).Adj x y) ∧
        (∀ i j, i ≠ j → Disjoint (colorGraph P ω i).edgeSet (colorGraph P ω j).edgeSet) := by
  have : NeZero l := ⟨hl.ne'⟩
  have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
  have hevent := (edgeSplittingScaleError_tendsto c hc l hl).eventually_lt_const
    (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨D₀,hD₀⟩ := hevent.exists_forall_of_atTop
  refine ⟨D₀, ?_⟩
  intro D hD V _ _ P _ h hh _hrlo hrhi hexp
  apply edge_splitting_of_error_lt_one P hexp
  apply lt_of_le_of_lt _ (hD₀ D hD)
  unfold edgeSplittingScaleError
  apply mul_le_mul_of_nonneg_left _ hlR.le
  apply sub_le_sub_right
  apply exp_le_exp.mpr
  apply mul_le_mul hrhi _ (exp_pos _).le ((Nat.cast_nonneg (Fintype.card V)).trans hrhi)
  apply exp_le_exp.mpr
  have he := div_le_div_of_nonneg_right hh (show 0 ≤ 8*(l : ℝ) by positivity)
  calc
    -h/(8*l) = -(h/(8*l)) := by ring
    _ ≤ -(c*D^(9/10 : ℝ)/(8*l)) := neg_le_neg he
    _ = -(c/(8*l))*D^(9/10 : ℝ) := by ring

end ErdosGallai.Batch.Splitting

namespace ErdosGallai.Batch
noncomputable section
def inductionPhi (x : ℝ) : ℝ :=
  if x = 1 then 1/2 else max (1/2) (1 - 1 / sqrt (logb 2 x))

lemma inductionPhi_one : inductionPhi 1 = 1/2 := by simp [inductionPhi]

lemma inductionPhi_bounds (x : ℝ) : 1/2 ≤ inductionPhi x ∧ inductionPhi x ≤ 1 := by
  by_cases hx : x = 1
  · norm_num [inductionPhi, hx]
  · simp only [inductionPhi, hx, ite_false]
    exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith [one_div_nonneg.mpr (Real.sqrt_nonneg (logb 2 x))])⟩

lemma inductionPhi_monotone : MonotoneOn inductionPhi (Set.Ici 1) := by
  intro x hx y hy hxy
  by_cases hx1 : x = 1
  · simpa [hx1, inductionPhi_one] using (inductionPhi_bounds y).1
  have hxgt : 1 < x := lt_of_le_of_ne hx (Ne.symm hx1)
  have hygt : 1 < y := hxgt.trans_le hxy
  have hlog : logb 2 x ≤ logb 2 y := Real.logb_le_logb_of_le (by norm_num)
    (by linarith) hxy
  have hxlog : 0 < logb 2 x := Real.logb_pos (by norm_num) hxgt
  have hinv := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hxlog) (Real.sqrt_le_sqrt hlog)
  simp only [inductionPhi, hx1, ne_of_gt hygt, ite_false]
  exact max_le_max le_rfl (by linarith)

lemma inductionPhi_nonconstant (x : ℝ) (hlog : 4 ≤ logb 2 x) :
    inductionPhi x = 1 - 1 / sqrt (logb 2 x) := by
  have hx : x ≠ 1 := by intro hx; subst x; norm_num at hlog
  have hsqrt : 2 ≤ sqrt (logb 2 x) := by
    convert Real.sqrt_le_sqrt hlog using 1 ; norm_num
  have hinv : 1 / sqrt (logb 2 x) ≤ 1/2 :=
    one_div_le_one_div_of_le (by norm_num) hsqrt
  simp only [inductionPhi, hx, ite_false]
  exact max_eq_right (by linarith)

def inductionDelta : ℝ := 1 / sqrt (3/10) - 1

lemma inductionDelta_pos : 0 < inductionDelta := by
  have hs : 0 < sqrt (3/10 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : sqrt (3/10 : ℝ) < 1 := by
    exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  dsimp [inductionDelta]
  have hh := (one_lt_div hs).mpr hs1
  linarith

theorem induction_potential_gain (D n : ℝ) (hD : 1 < D) (hn : D ≤ n)
    (hw : 40/3 ≤ logb 2 D) :
    inductionDelta / sqrt (logb 2 D) ≤ inductionPhi n - inductionPhi (D^(3/10:ℝ)) := by
  have hD0 : 0 < D := by linarith
  have hw0 : 0 < logb 2 D := by linarith
  have hnlog : logb 2 D ≤ logb 2 n :=
    Real.logb_le_logb_of_le (by norm_num) hD0 hn
  have hblog : logb 2 (D^(3/10:ℝ)) = (3/10)*logb 2 D := by
    exact Real.logb_rpow_eq_mul_logb_of_pos hD0
  rw [inductionPhi_nonconstant n (by linarith),
    inductionPhi_nonconstant (D^(3/10:ℝ)) (by rw [hblog]; linarith), hblog]
  have hinv := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hw0)
    (Real.sqrt_le_sqrt hnlog)
  have hid : 1 / sqrt ((3/10)*logb 2 D) - 1 / sqrt (logb 2 D) =
    inductionDelta / sqrt (logb 2 D) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3/10)]
    dsimp [inductionDelta]
    field_simp
  rw [← hid]
  linarith

lemma induction_cutoff_absorption (A w : ℝ) (hA : 0 ≤ A) (hw0 : 0 < w)
    (hw : ((A+1)/inductionDelta)^2 ≤ w) :
    (A+1)/w ≤ inductionDelta / sqrt w := by
  have hd := inductionDelta_pos
  have hratio : 0 ≤ (A+1)/inductionDelta := by positivity
  have hs : (A+1)/inductionDelta ≤ sqrt w := by
    have hh := Real.sqrt_le_sqrt hw
    simpa [Real.sqrt_sq hratio] using hh
  have hm : A+1 ≤ inductionDelta * sqrt w := by
    have := (div_le_iff₀ hd).mp hs
    simpa [mul_comm] using this
  apply (div_le_div_iff₀ hw0 (Real.sqrt_pos.mpr hw0)).mpr
  have hmul := mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg w)
  simpa [mul_assoc, Real.mul_self_sqrt hw0.le] using hmul

theorem induction_cost_absorbed (D n S C A₁ A₂ : ℝ)
    (hD : 1 < D) (hn : D ≤ n) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hA₁ : 0 ≤ A₁) (_hA₂ : 0 ≤ A₂) (hCA : 7*A₂ ≤ C)
    (hw : 40/3 ≤ logb 2 D)
    (hcut : ((A₁+1)/inductionDelta)^2 ≤ logb 2 D) :
    A₂*(S+n/logb 2 D) + (C/100)*S +
      C*inductionPhi (D^(3/10:ℝ))*(n-S/3+A₁*n/logb 2 D) ≤ C*inductionPhi n*n := by
  let f := inductionPhi (D^(3/10:ℝ))
  obtain ⟨hflo,hfhi⟩ := inductionPhi_bounds (D^(3/10:ℝ))
  have hw0 : 0 < logb 2 D := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hnw : 0 ≤ n/logb 2 D := div_nonneg hn0 hw0.le
  have hcoeff : A₂+C/100-C*f/3 ≤ 0 := by
    dsimp [f]
    nlinarith [mul_le_mul_of_nonneg_left hflo hC]
  have hScost := mul_nonpos_of_nonpos_of_nonneg hcoeff hS
  have hA₂C : A₂ ≤ C := by linarith
  have hAprod : C*f*A₁ ≤ C*A₁ := by
    exact mul_le_mul_of_nonneg_right (by
      simpa [f] using mul_le_mul_of_nonneg_left hfhi hC) hA₁
  have how := mul_le_mul_of_nonneg_right (add_le_add hA₂C hAprod) hnw
  have habs := induction_cutoff_absorption A₁ (logb 2 D) hA₁ hw0 hcut
  have hgain := induction_potential_gain D n hD hn hw
  have hpay := mul_le_mul_of_nonneg_left (habs.trans hgain) (mul_nonneg hC hn0)
  change A₂*(S+n/logb 2 D) + (C/100)*S + C*f*(n-S/3+A₁*n/logb 2 D) ≤ _
  change C*n*((A₁+1)/logb 2 D) ≤ C*n*(inductionPhi n - f) at hpay
  simp only [div_eq_mul_inv] at hScost how hpay ⊢
  nlinarith only [hScost, how, hpay]

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma cutExpansionOn_of_induce (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) (h : ℝ) (he : CutExpansion (P.induce (W:Set V)) h) : CutExpansionOn P W h := by
  intro A hA
  let B : Finset (W:Set V) := univ.filter (fun x => x.val ∈ A)
  have him : B.image Subtype.val = A := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y,hy,rfl⟩; exact (Finset.mem_filter.mp hy).2
    · intro hx; exact ⟨⟨x,hA hx⟩,by simp [B,hx],rfl⟩
  have hcomp := subtype_image_compl W B
  rw [him] at hcomp
  have hh := he B
  rw [induced_interedges_card,him] at hh
  have hc : B.card = A.card := by rw [← him,Finset.card_image_of_injective _ Subtype.val_injective]
  have hcc : Bᶜ.card = (W \ A).card := by rw [← hcomp,Finset.card_image_of_injective _ Subtype.val_injective]
  simpa only [hc,hcc] using hh

lemma cutExpansionOn_mono {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P Q : SimpleGraph V} [DecidableRel P.Adj] [DecidableRel Q.Adj]
    {W : Finset V} {h : ℝ} (he : CutExpansionOn P W h) (hPQ : P ≤ Q) : CutExpansionOn Q W h := by
  intro A hA
  exact (he A hA).trans (Nat.cast_le.mpr (Finset.card_le_card (by
    intro e he
    simp only [SimpleGraph.mem_interedges_iff] at he ⊢
    exact ⟨he.1,he.2.1,hPQ he.2.2⟩)))

theorem uniform_two_routers_on : ∃ D₀ : ℝ, ∀ D ≥ D₀,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (R : SimpleGraph V) (W : Finset V),
    (∀ ⦃x y⦄, R.Adj x y → x ∈ W ∧ y ∈ W) →
    D^(9/10:ℝ) ≤ (W.card:ℝ) → (W.card:ℝ) ≤ D^(51/50:ℝ) →
    CutExpansionOn R W (D^(9/10:ℝ)) →
    ∃ P T : SimpleGraph V, P ≤ R ∧ T ≤ R ∧ Disjoint P.edgeSet T.edgeSet ∧
      P.edgeSet ∪ T.edgeSet = R.edgeSet ∧
      CutExpansionOn P W (D^(9/10:ℝ)/4) ∧ CutExpansionOn T W (D^(9/10:ℝ)/4) := by
  obtain ⟨D₀,hsplit⟩ := Splitting.edge_splitting_uniform 1 (by norm_num) 2 (by norm_num)
  refine ⟨D₀,?_⟩
  intro D hD V _ _ R W hW hlo hhi he
  let R' := R.induce (W:Set V)
  have he' : Splitting.CutExpansion R' (D^(9/10:ℝ)) := cutExpansion_induce R W _ he
  obtain ⟨ω,hω,hcover,hdis⟩ := hsplit D hD (W:Set V) R' (D^(9/10:ℝ))
    (by simp) (by simpa using hlo) (by simpa using hhi) he'
  let f : (W:Set V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let Q (i : Fin 2) := (Splitting.colorGraph R' ω i).map f
  have hQR (i : Fin 2) : Q i ≤ R := by
    apply SimpleGraph.map_le_iff_le_comap.mpr
    exact fun _ _ h => h.1
  have hind (i) : (Q i).induce (W:Set V) = Splitting.colorGraph R' ω i :=
    SimpleGraph.comap_map_eq f _
  have hexp (i) : @CutExpansionOn V _ (Q i) (fun _ _ => Classical.propDecidable _) W (D^(9/10:ℝ)/4) := by
    apply @cutExpansionOn_of_induce V _ _ (Q i) (fun _ _ => Classical.propDecidable _) W
    have hcol : CutExpansion (Splitting.colorGraph R' ω i) (D^(9/10:ℝ)/4) := by simpa only [CutExpansion, Splitting.CutExpansion, Nat.cast_ofNat, show (2:ℝ)*2=4 by norm_num] using hω i
    convert hcol using 1 ; simp only [hind]
  have hQedge (i) : (Q i).edgeSet = Sym2.map (Subtype.val : ↥(W:Set V) → V) ''
      (Splitting.colorGraph R' ω i).edgeSet := SimpleGraph.edgeSet_map f _
  refine ⟨Q 0,Q 1,hQR 0,hQR 1,?_,?_,hexp 0,hexp 1⟩
  · rw [hQedge,hQedge]
    apply Set.disjoint_left.mpr
    rintro e ⟨a,ha,hae⟩ ⟨b,hb,hbe⟩
    have hab := Sym2.map.injective Subtype.val_injective (hae.trans hbe.symm)
    subst b
    exact Set.disjoint_left.mp (hdis 0 1 (by decide)) ha hb
  · apply Set.Subset.antisymm
    · exact Set.union_subset (SimpleGraph.edgeSet_mono (hQR 0)) (SimpleGraph.edgeSet_mono (hQR 1))
    · intro e heR
      induction e using Sym2.ind with
      | _ x y =>
        have hxy : R.Adj x y := heR
        obtain ⟨i,hi⟩ := (hcover ⟨x,(hW hxy).1⟩ ⟨y,(hW hxy).2⟩).mp hxy
        have hm : s(x,y) ∈ (Q i).edgeSet := by
          rw [hQedge]
          exact ⟨s(⟨x,(hW hxy).1⟩,⟨y,(hW hxy).2⟩),hi,rfl⟩
        fin_cases i
        · exact Or.inl hm
        · exact Or.inr hm

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open _root_.SimpleGraph _root_.Finset
attribute [local instance] Classical.propDecidable

lemma decompositionCost_adjoin_same {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (H : J → SimpleGraph V) (hHG : ∀ j, H j ≤ G)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hHP : ∀ j i, Disjoint (H j).edgeSet (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) := by
  let f : ∀ j, H j →g G := fun j => ⟨id,fun h => hHG j h⟩
  have he (j) : Sym2.map (f j) '' (H j).edgeSet = (H j).edgeSet := by
    have hf : (f j : V → V) = id := rfl
    rw [hf, Sym2.map_id, Set.image_id]
  apply decompositionCost_adjoin G parts hp hd (fun _ => V) H f (fun _ => Function.injective_id)
  · simpa only [he] using hHH
  · simpa only [he] using hHP
  · simpa only [he] using hu

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable

def routerRemainder {V : Type} (R : SimpleGraph V) (used : Set (Sym2 V)) : SimpleGraph V :=
  R \ SimpleGraph.fromEdgeSet used

lemma routerRemainder_edges {V : Type} (R : SimpleGraph V) (used : Set (Sym2 V)) :
    (routerRemainder R used).edgeSet = R.edgeSet \ used := by
  simp [routerRemainder,SimpleGraph.edgeSet_sdiff]

lemma routerRemainder_le {V : Type} (R : SimpleGraph V) (used : Set (Sym2 V)) :
    routerRemainder R used ≤ R := fun _ _ h => h.1

lemma protected_le_remainder {V : Type} {R T : SimpleGraph V} {used : Set (Sym2 V)}
    (hTR : T ≤ R) (htu : Disjoint T.edgeSet used) : T ≤ routerRemainder R used := by
  apply SimpleGraph.edgeSet_subset_edgeSet.mp
  rw [routerRemainder_edges]
  exact fun _ he => ⟨SimpleGraph.edgeSet_mono hTR he,fun hu => Set.disjoint_left.mp htu he hu⟩

lemma protected_avoids_used {V A : Type} (R P T : A → SimpleGraph V)
    (hRR : Pairwise fun i j => Disjoint (R i).edgeSet (R j).edgeSet)
    (hPR : ∀ i, P i ≤ R i) (hTR : ∀ i, T i ≤ R i)
    (hTP : ∀ i, Disjoint (T i).edgeSet (P i).edgeSet)
    (used : Set (Sym2 V)) (hu : used ⊆ ⋃ i, (P i).edgeSet) :
    ∀ i, Disjoint (T i).edgeSet used := by
  intro i
  apply Set.disjoint_left.mpr
  intro e he heu
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hu heu)
  by_cases hij : i = j
  · subst j; exact Set.disjoint_left.mp (hTP i) he hj
  · exact Set.disjoint_left.mp (hRR hij) (SimpleGraph.edgeSet_mono (hTR i) he)
      (SimpleGraph.edgeSet_mono (hPR j) hj)

lemma batch_remainder_ledger {V A K : Type} [Fintype V] [Fintype A] [Fintype K]
    (G F : SimpleGraph V) (R : A → SimpleGraph V)
    (hRG : ∀ i, R i ≤ G)
    (hRR : Pairwise fun i j => Disjoint (R i).edgeSet (R j).edgeSet)
    (hFR : ∀ i, Disjoint F.edgeSet (R i).edgeSet)
    (hcover : F.edgeSet ∪ (⋃ i, (R i).edgeSet) = G.edgeSet)
    (parts : K → Set (Sym2 V)) (hp : ∀ k, CycleOrSingleEdge G (parts k))
    (hd : Pairwise fun j k => Disjoint (parts j) (parts k))
    (used : Set (Sym2 V)) (hu : used ⊆ ⋃ i, (R i).edgeSet)
    (hparts : (⋃ k, parts k) = F.edgeSet ∪ used) :
    decompositionCost G ≤ Fintype.card K + ∑ i, decompositionCost (routerRemainder (R i) used) := by
  apply decompositionCost_adjoin_same G parts hp hd (fun i => routerRemainder (R i) used)
    (fun i => (routerRemainder_le _ _).trans (hRG i))
  · intro i j hij
    exact (hRR hij).mono (SimpleGraph.edgeSet_mono (routerRemainder_le _ _))
      (SimpleGraph.edgeSet_mono (routerRemainder_le _ _))
  · intro i k
    rw [routerRemainder_edges]
    apply Set.disjoint_left.mpr
    intro e he hp
    have hpe : e ∈ F.edgeSet ∪ used := hparts ▸ Set.mem_iUnion.mpr ⟨k,hp⟩
    rcases hpe with hpe | hpe
    · exact Set.disjoint_left.mp (hFR i) hpe he.1
    · exact he.2 hpe
  · rw [hparts,← hcover]
    simp_rw [routerRemainder_edges]
    ext e
    simp only [Set.mem_union,Set.mem_iUnion,Set.mem_sdiff]
    constructor
    · rintro ((hf | hu') | ⟨i,hi,_⟩)
      · exact Or.inl hf
      · exact Or.inr (Set.mem_iUnion.mp (hu hu'))
      · exact Or.inr ⟨i,hi⟩
    · rintro (hf | ⟨i,hi⟩)
      · exact Or.inl (Or.inl hf)
      · by_cases he : e ∈ used
        · exact Or.inl (Or.inr he)
        · exact Or.inr ⟨i,hi,he⟩

lemma prepared_quotient_cost {V I : Type} [Fintype V] [Fintype I]
    (J : SimpleGraph V) (X : I → Finset V) (hd : Pairwise fun i j => Disjoint (X i) (X j))
    (p : PreparedBatch J X hd) (W : Finset V)
    (hW : ∀ ⦃x y⦄, J.Adj x y → x ∈ W ∧ y ∈ W)
    (hX : ∀ i, X i ⊆ W) (n : ℕ) (M t : ℝ) (_ht : 0 ≤ t) (hn : W.card < n) (hM : (W.card:ℝ) ≤ M)
    (ih : ∀ (A : Type) [Fintype A] (H : SimpleGraph A), Fintype.card A < n → (Fintype.card A:ℝ) ≤ M →
      (decompositionCost H:ℝ) ≤ t * Fintype.card A) :
    ∃ k, EdgeDecomposition p.quotient k ∧
      (k:ℝ) ≤ t * ((W.card:ℝ) - ∑ i, ((X i).card / 2:ℕ)) := by
  classical
  let A := W.image (familyProject X hd p.pairing)
  let H := p.quotient.induce (A:Set (FamilyQuotient X p.pairing))
  have ho : A.card + ∑ i, (X i).card / 2 = W.card := family_quotient_image_order X hd p.pairing W hX
  have hn' : Fintype.card (A:Set (FamilyQuotient X p.pairing)) < n := by simp only [Finset.coe_sort_coe,Fintype.card_coe]; omega
  refine ⟨decompositionCost H,edgeDecomposition_on _ A (p.quotient_supported W hW) (decompositionCost_spec H),?_⟩
  have hc := ih (A:Set (FamilyQuotient X p.pairing)) H hn' (by simp only [Finset.coe_sort_coe,Fintype.card_coe]; exact (Nat.cast_le.mpr (by omega : A.card ≤ W.card)).trans hM)
  simp only [Finset.coe_sort_coe,Fintype.card_coe] at hc
  have heq : (A.card:ℝ) = (W.card:ℝ) - ∑ i, ((X i).card / 2:ℕ) := by
    have hh : (A.card:ℝ) + ∑ i, ((X i).card / 2:ℕ) = W.card := by exact_mod_cast ho
    linarith
  rwa [heq] at hc

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable

theorem uniform_coupled_resolution_cost : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
    ∀ (V A B : Type) [Fintype V] [Fintype A] [Fintype B],
    ∀ (G F : SimpleGraph V) (R : A → SimpleGraph V) (U : A → Finset V),
    F ≤ G → (∀ r, R r ≤ G) →
    Pairwise (fun r s => Disjoint (R r).edgeSet (R s).edgeSet) →
    Pairwise (fun r s => Disjoint (U r) (U s)) →
    (∀ r, ∀ ⦃x y⦄, (R r).Adj x y → x ∈ U r ∧ y ∈ U r) →
    (∀ r, Disjoint F.edgeSet (R r).edgeSet) →
    F.edgeSet ∪ (⋃ r, (R r).edgeSet) = G.edgeSet →
    (∀ r, CutExpansionOn (R r) (U r) (D^(9/10:ℝ))) →
    (∀ r, D^(9/10:ℝ) ≤ ((U r).card:ℝ) ∧ ((U r).card:ℝ) ≤ D^(51/50:ℝ)) →
    ∀ (J : B → SimpleGraph V) (W : B → Finset V),
    (∀ b, J b ≤ F) → Pairwise (fun b c => Disjoint (J b).edgeSet (J c).edgeSet) →
    (⋃ b, (J b).edgeSet) = F.edgeSet →
    (∀ b, ∀ ⦃x y⦄, (J b).Adj x y → x ∈ W b ∧ y ∈ W b) →
    (∀ b, ((W b).card:ℝ) ≤ D^(3/10:ℝ)) →
    ∀ (I : B → Type) [∀ b, Fintype (I b)] (X : ∀ b, I b → Finset V)
      (_hXd : ∀ b, Pairwise fun i j => Disjoint (X b i) (X b j)),
    (∀ b i, X b i ⊆ W b) →
    ∀ rX : ∀ b, I b → A,
    (∀ b i, X b i ⊆ U (rX b i)) →
    (∀ b i v, v ∈ X b i → (F.degree v:ℝ) ≤ D^(1/100:ℝ)) →
    1 ≤ D^(1/100:ℝ) → (∀ b i, 8 ≤ (X b i).card) →
    (∀ b i, (D^(1/100:ℝ))^2 ≤ (X b i).card) →
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → (∀ b, (W b).card < n) →
    (∀ (Q : Type) [Fintype Q] (H : SimpleGraph Q), Fintype.card Q < n →
      (Fintype.card Q:ℝ) ≤ D^(3/10:ℝ) → (decompositionCost H:ℝ) ≤ t * Fintype.card Q) →
    ∃ H : A → SimpleGraph V,
      (∀ r, H r ≤ R r) ∧
      (∀ r, CutExpansionOn (H r) (U r) (D^(9/10:ℝ)/4)) ∧
      (decompositionCost G:ℝ) ≤
        t * ((∑ b, ((W b).card:ℝ)) - ∑ b, ∑ i, ((X b i).card / 2:ℕ)) +
        8 * (∑ b, ∑ i, ((X b i).card:ℝ)) + ∑ r, (decompositionCost (H r):ℝ) := by
  obtain ⟨D₁,hsplit⟩ := uniform_two_routers_on
  obtain ⟨D₂,hD₂,hresolve⟩ := uniform_batch_resolution
  refine ⟨max D₁ D₂,lt_of_lt_of_le hD₂ (le_max_right _ _),?_⟩
  intro D hD V A B _ _ _ G F R U hFG hRG hRR hUU hRU hFR hcover he hr
    J W hJF hJJ hJu hW hWnum I _ X hXd hXW rX hXU hdeg ha hm hma n t ht hn ih
  have hs (r : A) := hsplit D ((le_max_left _ _).trans hD) V (R r) (U r)
    (hRU r) (hr r).1 (hr r).2 (he r)
  choose P T hPR hTR hPT hPu hPe hTe using hs
  have hPP : Pairwise fun r s => Disjoint (P r).edgeSet (P s).edgeSet :=
    fun _ _ h => (hRR h).mono (SimpleGraph.edgeSet_mono (hPR _)) (SimpleGraph.edgeSet_mono (hPR _))
  have hp (b : B) : Nonempty (PreparedBatch (J b) (X b) (hXd b)) :=
    prepare_batch (J b) (X b) (hXd b) (D^(1/100:ℝ)) ha (hm b) (hma b)
      (fun i v hv => (Nat.cast_le.mpr (SimpleGraph.degree_le_of_le (hJF b))).trans (hdeg b i v hv))
  let prep (b : B) := Classical.choice (hp b)
  have hq (b : B) := prepared_quotient_cost (J b) (X b) (hXd b) (prep b) (W b)
    (hW b) (hXW b) n (D^(3/10:ℝ)) t ht (hn b) (hWnum b) ih
  choose k hk hkc using hq
  obtain ⟨K,hK,parts,used,hcount,hparts,hdis,hused,hFu,hpartscover⟩ :=
    hresolve D ((le_max_right _ _).trans hD) V A B G F P U hFG
      (fun r => (hPR r).trans (hRG r)) hPP hUU
      (fun r => (hFR r).mono_right (SimpleGraph.edgeSet_mono (hPR r))) hPe hr
      J W hJF hJJ hJu hW hWnum I X hXd hXW rX hXU hdeg prep k hk
  let : Fintype K := hK
  have husedR : used ⊆ ⋃ r, (R r).edgeSet := hused.trans (Set.iUnion_mono fun r => SimpleGraph.edgeSet_mono (hPR r))
  have hTu := protected_avoids_used R P T hRR hPR hTR (fun r => (hPT r).symm) used hused
  let H (r : A) := routerRemainder (R r) used
  have hcost := batch_remainder_ledger G F R hRG hRR hFR hcover parts hparts hdis used husedR hpartscover
  refine ⟨H,fun r => routerRemainder_le _ _,fun r => ?_,?_⟩
  · exact cutExpansionOn_mono (hTe r) (protected_le_remainder (hTR r) (hTu r))
  · have hkreal : (Fintype.card K:ℝ) ≤ (∑ b, (k b:ℝ)) + 8 * (∑ b, ∑ i, ((X b i).card:ℝ)) := by
      exact_mod_cast hcount
    have hqsum := Finset.sum_le_sum (s := univ) (fun b _ => hkc b)
    have hqsum' : (∑ b, (k b:ℝ)) ≤
        t * ((∑ b, ((W b).card:ℝ)) - ∑ b, ∑ i, ((X b i).card / 2:ℕ)) := by
      simpa only [Finset.mul_sum,Finset.sum_sub_distrib,mul_sub,Nat.cast_sum] using hqsum
    have hc : (decompositionCost G:ℝ) ≤ (Fintype.card K:ℝ) + ∑ r, (decompositionCost (H r):ℝ) := by
      exact_mod_cast hcost
    linarith

end
end ErdosGallai.Batch

end
end

/-! ### Upstream module `Combinatorics/CycleDecomposition/DepthFirstSearch.lean` -/

noncomputable section
namespace ErdosGallai.Scale
open _root_.Finset _root_.SimpleGraph
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

structure DFSState (G : SimpleGraph V) where
  stack : List V
  finished : Finset V
  unexplored : Finset V
  nodup : stack.Nodup
  chain : stack.IsChain G.Adj
  f_s : Disjoint finished stack.toFinset
  f_u : Disjoint finished unexplored
  s_u : Disjoint stack.toFinset unexplored
  cover : finished ∪ stack.toFinset ∪ unexplored = univ
  separation : ∀ x ∈ finished, ∀ y ∈ unexplored, ¬ G.Adj x y

namespace DFSState
variable {G : SimpleGraph V}

lemma card_eq (s : DFSState G) :
    Fintype.card V = s.finished.card + s.stack.length + s.unexplored.card := by
  have hdis : Disjoint (s.finished ∪ s.stack.toFinset) s.unexplored :=
    Finset.disjoint_union_left.mpr ⟨s.f_u, s.s_u⟩
  have hc := congrArg Finset.card s.cover
  rw [Finset.card_union_of_disjoint hdis, Finset.card_union_of_disjoint s.f_s,
    List.toFinset_card_of_nodup s.nodup, Finset.card_univ] at hc
  exact hc.symm

lemma restart (s : DFSState G) (hs : s.stack = []) (v : V) (hv : v ∈ s.unexplored) :
    ∃ t : DFSState G, t.finished = s.finished ∧
      t.unexplored.card + 1 = s.unexplored.card := by
  have hvf : v ∉ s.finished := fun hf => Finset.disjoint_left.mp s.f_u hf hv
  refine ⟨⟨[v], s.finished, s.unexplored.erase v, by simp, by simp,
    ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · simpa using hvf
  · exact s.f_u.mono_right (Finset.erase_subset _ _)
  · simp
  · change s.finished ∪ {v} ∪ s.unexplored.erase v = univ
    rw [Finset.union_assoc, Finset.singleton_union, Finset.insert_erase hv]
    simpa only [hs, List.toFinset_nil, Finset.union_empty] using s.cover
  · intro x hx y hy
    exact s.separation x hx y (Finset.mem_of_mem_erase hy)
  · exact Finset.card_erase_add_one hv

lemma push (s : DFSState G) (v w : V) (L : List V) (hs : s.stack = v::L)
    (hw : w ∈ s.unexplored) (hadj : G.Adj w v) :
    ∃ t : DFSState G, t.finished = s.finished ∧
      t.unexplored.card + 1 = s.unexplored.card := by
  have hws : w ∉ s.stack := fun h => Finset.disjoint_left.mp s.s_u
    (List.mem_toFinset.mpr h) hw
  have hwf : w ∉ s.finished := fun h => Finset.disjoint_left.mp s.f_u h hw
  refine ⟨⟨w::s.stack, s.finished, s.unexplored.erase w, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    rfl, ?_⟩
  · exact List.nodup_cons.mpr ⟨hws,s.nodup⟩
  · rw [hs]
    exact List.IsChain.cons_cons hadj (hs ▸ s.chain)
  · simpa using And.intro hwf s.f_s
  · exact s.f_u.mono_right (Finset.erase_subset _ _)
  · rw [List.toFinset_cons, Finset.disjoint_insert_left]
    exact ⟨(by simp), s.s_u.mono_right (Finset.erase_subset _ _)⟩
  · ext x
    have hx : x ∈ s.finished ∪ s.stack.toFinset ∪ s.unexplored := by rw [s.cover]; simp
    simp only [Finset.mem_union] at hx
    simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert,
      Finset.mem_erase, Finset.mem_univ, iff_true]
    by_cases hxw : x = w
    · exact Or.inl (Or.inr (Or.inl hxw))
    · rcases hx with (h|h)|h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr ⟨hxw,h⟩
  · intro x hx y hy
    exact s.separation x hx y (Finset.mem_of_mem_erase hy)
  · exact Finset.card_erase_add_one hw

lemma pop (s : DFSState G) (v : V) (L : List V) (hs : s.stack = v::L)
    (hn : ∀ w ∈ s.unexplored, ¬G.Adj v w) :
    ∃ t : DFSState G, t.finished.card = s.finished.card + 1 ∧
      t.unexplored = s.unexplored := by
  have hvf : v ∉ s.finished := fun hv => Finset.disjoint_left.mp s.f_s hv (by simp [hs])
  have hvu : v ∉ s.unexplored := fun hv => Finset.disjoint_left.mp s.s_u (by simp [hs]) hv
  have hL : L.toFinset ⊆ s.stack.toFinset := by rw [hs]; simp
  have hnd : v ∉ L ∧ L.Nodup := by simpa only [hs, List.nodup_cons] using s.nodup
  have hvL : v ∉ L := hnd.1
  refine ⟨⟨L, insert v s.finished, s.unexplored, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, rfl⟩
  · exact hnd.2
  · exact (hs ▸ s.chain).of_cons
  · exact Finset.disjoint_insert_left.mpr ⟨by simpa using hvL, s.f_s.mono_right hL⟩
  · exact Finset.disjoint_insert_left.mpr ⟨hvu,s.f_u⟩
  · exact s.s_u.mono_left hL
  · simpa [hs, Finset.insert_union] using s.cover
  · intro x hx y hy
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hn y hy
    · exact s.separation x hx y hy
  · exact Finset.card_insert_of_notMem hvf

lemma reaches_balance (s : DFSState G) (hs : s.finished.card ≤ s.unexplored.card) :
    ∃ t : DFSState G, t.finished.card = t.unexplored.card := by
  generalize hd : s.unexplored.card - s.finished.card = d
  induction d using Nat.strong_induction_on generalizing s with
  | h d ih =>
    by_cases heq : s.finished.card = s.unexplored.card
    · exact ⟨s,heq⟩
    have hlt : s.finished.card < s.unexplored.card := lt_of_le_of_ne hs heq
    have hdpos : 0 < d := by omega
    cases hstack : s.stack with
    | nil =>
      obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < s.unexplored.card by omega)
      obtain ⟨t,htf,htu⟩ := s.restart hstack v hv
      apply ih (t.unexplored.card-t.finished.card) (by rw [htf]; omega) t (by rw [htf]; omega) rfl
    | cons v L =>
      by_cases hn : ∃ w ∈ s.unexplored, G.Adj v w
      · obtain ⟨w,hw,hadj⟩ := hn
        obtain ⟨t,htf,htu⟩ := s.push v w L hstack hw hadj.symm
        apply ih (t.unexplored.card-t.finished.card) (by rw [htf]; omega) t (by rw [htf]; omega) rfl
      · push Not at hn
        obtain ⟨t,htf,htu⟩ := s.pop v L hstack hn
        apply ih (t.unexplored.card-t.finished.card) (by rw [htf,htu]; omega) t (by rw [htf,htu]; omega) rfl

end DFSState

theorem exists_balanced_dfs_state (G : SimpleGraph V) :
    ∃ s : DFSState G, s.finished.card = s.unexplored.card := by
  let s : DFSState G := ⟨[], ∅, univ, by simp, by simp, by simp, by simp, by simp,
    by simp, by simp⟩
  exact s.reaches_balance (by simp [s])

end ErdosGallai.Scale

namespace ErdosGallai.Scale
open _root_.Finset _root_.SimpleGraph
variable {V : Type cycleUniverse2} [Fintype V] [DecidableEq V]

def externalNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) : Finset V :=
  univ.filter (fun v => v ∉ U ∧ ∃ u ∈ U, G.Adj u v)

def VertexExpansion (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) : Prop :=
  ∀ U : Finset V, U.Nonempty → 2 * U.card ≤ Fintype.card V →
    α * U.card ≤ ((externalNeighbors G U).card : ℝ)

lemma DFSState.external_subset (G : SimpleGraph V) [DecidableRel G.Adj] (s : DFSState G) :
    externalNeighbors G s.unexplored ⊆ s.stack.toFinset := by
  intro v hv
  obtain ⟨_,hvu,u,hu,hadj⟩ := Finset.mem_filter.mp hv
  have hc : v ∈ s.finished ∪ s.stack.toFinset ∪ s.unexplored := by rw [s.cover]; simp
  rcases Finset.mem_union.mp hc with h|h
  · rcases Finset.mem_union.mp h with h|h
    · exact (s.separation v h u hu hadj.symm).elim
    · exact h
  · exact (hvu h).elim

theorem exists_long_stack (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (hα : α ≤ 1) (hexp : VertexExpansion G α) :
    ∃ L : List V, L.Nodup ∧ L.IsChain G.Adj ∧ α * Fintype.card V / 3 ≤ (L.length : ℝ) := by
  obtain ⟨s,heq⟩ := exists_balanced_dfs_state G
  refine ⟨s.stack,s.nodup,s.chain,?_⟩
  have hc := s.card_eq
  rw [heq] at hc
  have hcR : (Fintype.card V : ℝ) = 2*(s.unexplored.card : ℝ)+(s.stack.length : ℝ) := by
    exact_mod_cast (show Fintype.card V = 2*s.unexplored.card+s.stack.length by omega)
  have hN : ((externalNeighbors G s.unexplored).card : ℝ) ≤ (s.stack.length : ℝ) := by
    have ht := Finset.card_le_card (s.external_subset G)
    rw [List.toFinset_card_of_nodup s.nodup] at ht
    exact_mod_cast ht
  by_cases hU : s.unexplored.Nonempty
  · have hsmall : 2*s.unexplored.card ≤ Fintype.card V := by omega
    have he := (hexp s.unexplored hU hsmall).trans hN
    have ht : (0 : ℝ) ≤ s.stack.length := Nat.cast_nonneg _
    have ha := mul_le_mul_of_nonneg_right hα ht
    nlinarith
  · have hu : s.unexplored.card = 0 := by simp [Finset.not_nonempty_iff_eq_empty.mp hU]
    rw [hu, Nat.cast_zero, mul_zero, zero_add] at hcR

    nlinarith [show (0 : ℝ) ≤ s.stack.length from Nat.cast_nonneg _,
      mul_le_mul_of_nonneg_right hα (show (0 : ℝ) ≤ s.stack.length from Nat.cast_nonneg _)]

end ErdosGallai.Scale
end
/-! ### Upstream module `Combinatorics/CycleDecomposition/ExpansionBoxes.lean` -/

section
open _root_.Filter _root_.Asymptotics _root_.Real
noncomputable section
namespace ErdosGallai.Scale
open _root_.Finset _root_.SimpleGraph
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]
def avoidGraph (G : SimpleGraph V) (J : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∉ J ∧ y ∉ J
  symm := ⟨fun _x _y h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _x h => G.irrefl h.1⟩

lemma chain_reachable {V : Type cycleUniverse2} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {H : SimpleGraph V} {L : List V} (hL : L.IsChain H.Adj)
    {x y : V} (hx : x ∈ L) (hy : y ∈ L) : H.Reachable x y := by
  let : Trans H.Reachable H.Reachable H.Reachable := ⟨fun h₁ h₂ => h₁.trans h₂⟩
  cases L with
  | nil => simp at hx
  | cons a L =>
    have hC : (a::L).IsChain H.Reachable := hL.imp (fun _ _ h => h.reachable)
    have ha : ∀ b ∈ a::L, H.Reachable a b := by
      intro b hb
      rcases List.mem_cons.mp hb with rfl|hb
      · exact .refl _
      · exact hC.rel_cons hb
    exact (ha x hx).symm.trans (ha y hy)

theorem connector_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (α m : ℝ) (hα : 0 ≤ α) (hexp : VertexExpansion G α)
    (X Z J : Finset V) (hX : X.Nonempty) (hZ : Z.Nonempty)
    (hXJ : Disjoint X J) (hZJ : Disjoint Z J)
    (hconnX : ∀ x ∈ X, ∀ y ∈ X, (avoidGraph G J).Reachable x y)
    (_hconnZ : ∀ x ∈ Z, ∀ y ∈ Z, (avoidGraph G J).Reachable x y)
    (hmX : m ≤ (X.card : ℝ)) (hmZ : m ≤ (Z.card : ℝ))
    (hJ : (J.card : ℝ) < α*m) :
    ∃ x ∈ X, ∃ z ∈ Z, (avoidGraph G J).Reachable x z := by
  classical
  by_contra hn
  obtain ⟨x,hx⟩ := hX
  obtain ⟨z,hz⟩ := hZ
  let H := avoidGraph G J
  let A : Finset V := univ.filter (fun v => v ∉ J ∧ H.Reachable x v)
  let B : Finset V := univ \ (J ∪ A)
  have hXA : X ⊆ A := by
    intro y hy
    exact mem_filter.mpr ⟨mem_univ _,
      (Finset.disjoint_left.mp hXJ hy), hconnX x hx y hy⟩
  have hZA : ∀ y ∈ Z, ¬ H.Reachable x y := by
    intro y hy hr
    exact hn ⟨x,hx,y,hy,hr⟩
  have hZB : Z ⊆ B := by
    intro y hy
    simp only [B, Finset.mem_sdiff, mem_univ, true_and, mem_union, not_or]
    refine ⟨Finset.disjoint_left.mp hZJ hy, ?_⟩
    intro ha
    exact hZA y hy (mem_filter.mp ha).2.2
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro y ha hb
    exact (mem_sdiff.mp hb).2 (mem_union_right J ha)
  have hc : A.card + B.card ≤ Fintype.card V := by
    rw [← card_union_of_disjoint hAB]
    exact card_le_univ _
  have hboundaryA : externalNeighbors G A ⊆ J := by
    intro v hv
    obtain ⟨_,hva,u,hu,hadj⟩ := mem_filter.mp hv
    by_contra hvj
    obtain ⟨_,huj,hru⟩ := mem_filter.mp hu
    have hadjH : H.Adj u v := ⟨hadj,huj,hvj⟩
    exact hva (mem_filter.mpr ⟨mem_univ _,hvj,hru.trans hadjH.reachable⟩)
  have hboundaryB : externalNeighbors G B ⊆ J := by
    intro v hv
    obtain ⟨_,hvb,u,hu,hadj⟩ := mem_filter.mp hv
    by_contra hvj
    have hva : v ∈ A := by
      by_contra hna
      exact hvb (mem_sdiff.mpr ⟨mem_univ _, by simpa using And.intro hvj hna⟩)
    obtain ⟨_,_,hrv⟩ := mem_filter.mp hva
    have huj : u ∉ J := fun h => (mem_sdiff.mp hu).2 (mem_union_left A h)
    have hadjH : H.Adj v u := ⟨hadj.symm,hvj,huj⟩
    have hua : u ∈ A := mem_filter.mpr ⟨mem_univ _,huj,hrv.trans hadjH.reachable⟩
    exact (mem_sdiff.mp hu).2 (mem_union_right J hua)
  have hcontr (Q : Finset V) (hne : Q.Nonempty) (hsmall : 2*Q.card ≤ Fintype.card V)
      (hm : m ≤ (Q.card : ℝ)) (hb : externalNeighbors G Q ⊆ J) : False := by
    have he := hexp Q hne hsmall
    have hc : ((externalNeighbors G Q).card : ℝ) ≤ J.card := by
      exact_mod_cast card_le_card hb
    have hh := mul_le_mul_of_nonneg_left hm hα
    linarith
  by_cases hsmall : 2*A.card ≤ Fintype.card V
  · exact hcontr A ⟨x,hXA hx⟩ hsmall
      (hmX.trans (by exact_mod_cast card_le_card hXA)) hboundaryA
  · exact hcontr B ⟨z,hZB hz⟩ (by omega)
      (hmZ.trans (by exact_mod_cast card_le_card hZB)) hboundaryB

lemma avoid_support {V : Type cycleUniverse3} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (J : Finset V) {x z : V}
    (p : (avoidGraph G J).Walk x z) (hx : x ∉ J) :
    ∀ w ∈ p.support, w ∉ J := by
  induction p with
  | nil => simpa using hx
  | @cons u v z hadj p ih =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl|hw
    · exact hx
    · exact ih hadj.2.2 w hw

theorem shortest_set_connector (G : SimpleGraph V) (X Z J : Finset V)
    (hXJ : Disjoint X J)
    (hr : ∃ x ∈ X, ∃ z ∈ Z, (avoidGraph G J).Reachable x z) :
    ∃ x ∈ X, ∃ z ∈ Z, ∃ p : G.Walk x z,
      p.IsPath ∧ ∀ w ∈ p.support, w ∉ J ∧ (w ∈ X → w = x) ∧ (w ∈ Z → w = z) := by
  classical
  let H := avoidGraph G J
  let P : ℕ → Prop := fun k => ∃ x ∈ X, ∃ z ∈ Z, ∃ p : H.Walk x z,
    p.IsPath ∧ p.length = k
  have hP : ∃ k, P k := by
    obtain ⟨x,hx,z,hz,hr⟩ := hr
    obtain ⟨p,hp⟩ := hr.exists_isPath
    exact ⟨p.length,x,hx,z,hz,p,hp,rfl⟩
  obtain ⟨x,hx,z,hz,p,hp,hplen⟩ := Nat.find_spec hP
  have hmin : ∀ a ∈ X, ∀ b ∈ Z, ∀ q : H.Walk a b, q.IsPath → p.length ≤ q.length := by
    intro a ha b hb q hq
    rw [hplen]
    exact Nat.find_min' hP ⟨a,ha,b,hb,q,hq,rfl⟩
  have hsub : H ≤ G := fun _ _ h => h.1
  refine ⟨x,hx,z,hz,p.mapLe hsub,(hp.mapLe hsub),?_⟩
  intro w hw
  rw [Walk.support_mapLe_eq_support] at hw
  refine ⟨avoid_support G J p (Finset.disjoint_left.mp hXJ hx) w hw,?_,?_⟩
  · intro hwX
    by_contra hne
    have hlt := Walk.length_dropUntil_lt_length hw hne
    have hle := hmin w hwX z hz (p.dropUntil w hw) (hp.dropUntil hw)
    omega
  · intro hwZ
    by_contra hne
    have hlt := Walk.length_takeUntil_lt_length hw hne
    have hle := hmin x hx w hwZ (p.takeUntil w hw) (hp.takeUntil hw)
    omega

lemma path_cons_append {V : Type cycleUniverse4} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (x z : V) (B : List V)
    (hC : (x :: (B ++ [z])).IsChain G.Adj) :
    ∃ p : G.Walk x z, p.support = x :: (B ++ [z]) := by
  let L := x :: (B ++ [z])
  have hn : L ≠ [] := by simp [L]
  let p := Walk.ofSupport L hn hC
  have hx : L.head hn = x := rfl
  have hz : L.getLast hn = z := by simp [L]
  exact ⟨p.copy hx hz, by
    change ((Walk.ofSupport L hn hC).copy hx hz).support = L
    rw [Walk.support_copy, Walk.support_ofSupport]⟩

theorem cycle_across_middle (G : SimpleGraph V) (X J Z : List V)
    (hnd : (X ++ J ++ Z).Nodup) (hC : (X ++ J ++ Z).IsChain G.Adj)
    (hj : 1 ≤ J.length)
    (hc : ∃ x ∈ X, ∃ z ∈ Z, ∃ q : G.Walk x z,
      q.IsPath ∧ ∀ w ∈ q.support, w ∉ J ∧ (w ∈ X → w = x) ∧ (w ∈ Z → w = z)) :
    ∃ a : V, ∃ c : G.Walk a a, c.IsCycle ∧ J.length + 2 ≤ c.length := by
  obtain ⟨x,hx,z,hz,q,hq,havoid⟩ := hc
  obtain ⟨A,B,hX⟩ := List.mem_iff_append.mp hx
  obtain ⟨C,D,hZ⟩ := List.mem_iff_append.mp hz
  let M := x :: ((B ++ J ++ C) ++ [z])
  have heq : X ++ J ++ Z = A ++ (M ++ D) := by
    simp [hX,hZ,M,List.append_assoc]
  have hMC : M.IsChain G.Adj := by
    rw [heq] at hC
    exact hC.right_of_append.left_of_append
  have hMN : M.Nodup := by
    rw [heq] at hnd
    exact (List.nodup_append.mp (List.nodup_append.mp hnd).2.1).1
  obtain ⟨p,hpS⟩ := path_cons_append G x z (B ++ J ++ C) hMC
  have hp : p.IsPath := by
    rw [Walk.isPath_def,hpS]
    exact hMN
  have hlen : J.length + 1 ≤ p.length := by
    have ht := p.length_support
    rw [hpS] at ht
    simp only [List.length_cons,List.length_append] at ht
    omega
  have hxs : x ∉ p.support.tail := by
    have hn := hp.support_nodup
    rw [← p.cons_tail_support] at hn
    exact (List.nodup_cons.mp hn).1
  have hzs : z ∉ q.reverse.support.tail := by
    have hn := hq.reverse.support_nodup
    rw [← q.reverse.cons_tail_support] at hn
    exact (List.nodup_cons.mp hn).1
  have hdis : p.support.tail.Disjoint q.reverse.support.tail := by
    apply List.disjoint_left.mpr
    intro w hwP hwQ
    have hwq : w ∈ q.support := by
      simpa using List.mem_of_mem_tail hwQ
    obtain ⟨hwJ,hwX,hwZ⟩ := havoid w hwq
    have hwp : w ∈ X ++ J ++ Z := by
      rw [heq]
      have : w ∈ M := by
        change w ∈ x :: ((B ++ J ++ C) ++ [z])
        rw [← hpS]
        exact List.mem_of_mem_tail hwP
      simp only [List.mem_append]
      exact Or.inr (Or.inl this)
    simp only [List.mem_append] at hwp
    rcases hwp with (hw|hw)|hw
    · exact hxs (hwX hw ▸ hwP)
    · exact hwJ hw
    · exact hzs (hwZ hw ▸ hwQ)
  have hxz : x ≠ z := by
    intro he
    have hz : z ∈ p.support.tail := by simp [hpS]
    exact hxs (he ▸ hz)
  have hqlen : 1 ≤ q.length := by
    by_contra hh
    have : q.length = 0 := by omega
    exact hxz (Walk.eq_of_length_eq_zero this)
  refine ⟨x,p.append q.reverse,hp.isCycle_append hq.reverse hdis (Or.inl (by omega)),?_⟩
  simp only [Walk.length_append,Walk.length_reverse]
  omega

theorem long_cycle_of_vertex_expansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hexp : VertexExpansion G α)
    (hq : 1 ≤ α^2 * Fintype.card V / 100) :
    ∃ a : V, ∃ c : G.Walk a a, c.IsCycle ∧
      α^2 * Fintype.card V / 100 < (c.length : ℝ) := by
  classical
  obtain ⟨L,hnd,hchain,hL⟩ := exists_long_stack G α hα1 hexp
  let q := α^2 * Fintype.card V / 100
  let j := ⌊q⌋₊
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hjle : (j : ℝ) ≤ q := Nat.floor_le hq0
  have hjlt : q < (j : ℝ)+1 := Nat.lt_floor_add_one q
  have hj1 : 1 ≤ j := by exact (Nat.le_floor_iff hq0).mpr (by simpa [q] using hq)
  have hL0 : (0 : ℝ) ≤ L.length := Nat.cast_nonneg _
  have hu0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have haa : α^2 ≤ α := by nlinarith
  have hqq : 2*q ≤ α * Fintype.card V / 6 := by
    have hh := mul_le_mul_of_nonneg_right haa hu0
    dsimp [q]
    nlinarith [mul_nonneg (le_of_lt hα) hu0]
  have hround : 2*(j+1) ≤ L.length := by
    have hroundR : 2*((j:ℝ)+1) ≤ (L.length:ℝ) := by
      have hq1 : 1 ≤ q := hq
      linarith
    exact_mod_cast hroundR
  let k := (L.length-j)/2
  let X := L.take k
  let J := (L.drop k).take j
  let Z := (L.drop k).drop j
  have heq : L = X ++ J ++ Z := by
    dsimp [X,J,Z]
    rw [List.append_assoc,List.take_append_drop,List.take_append_drop]
  have hk : k ≤ L.length := by dsimp [k]; omega
  have hjdrop : j ≤ (L.drop k).length := by simp only [List.length_drop]; dsimp [k]; omega
  have hXlen : X.length = k := by simp [X,List.length_take, min_eq_left hk]
  have hJlen : J.length = j := by dsimp [J]; rw [List.length_take, min_eq_left hjdrop]
  have hZlen : Z.length = L.length-k-j := by simp only [Z,List.length_drop]
  have houterX : L.length ≤ 4*X.length := by rw [hXlen]; dsimp [k]; omega
  have houterZ : L.length ≤ 4*Z.length := by rw [hZlen]; dsimp [k]; omega
  rw [heq] at hnd hchain
  have hnX : X.Nodup := (List.nodup_append.mp (List.nodup_append.mp hnd).1).1
  have hnJ : J.Nodup := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1
  have hnZ : Z.Nodup := (List.nodup_append.mp hnd).2.1
  have hXJ : X.Disjoint J := (List.nodup_append.mp hnd).1.disjoint
  have hZJ : Z.Disjoint J := by
    have hd := hnd.disjoint
    exact List.disjoint_left.mpr (fun w hwz hwj =>
      List.disjoint_left.mp hd (List.mem_append_right X hwj) hwz)
  have hXJf : Disjoint X.toFinset J.toFinset := by
    apply Finset.disjoint_left.mpr
    intro w hw hJw
    exact List.disjoint_left.mp hXJ (List.mem_toFinset.mp hw) (List.mem_toFinset.mp hJw)
  have hZJf : Disjoint Z.toFinset J.toFinset := by
    apply Finset.disjoint_left.mpr
    intro w hw hJw
    exact List.disjoint_left.mp hZJ (List.mem_toFinset.mp hw) (List.mem_toFinset.mp hJw)
  have hconnX : ∀ x ∈ X.toFinset, ∀ y ∈ X.toFinset,
      (avoidGraph G J.toFinset).Reachable x y := by
    intro x hx y hy
    apply chain_reachable (L := X) _ (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy)
    apply hchain.left_of_append.left_of_append.imp_of_mem_imp
    intro a b ha hb hab
    exact ⟨hab,fun hj => List.disjoint_left.mp hXJ ha (List.mem_toFinset.mp hj),
      fun hj => List.disjoint_left.mp hXJ hb (List.mem_toFinset.mp hj)⟩
  have hconnZ : ∀ x ∈ Z.toFinset, ∀ y ∈ Z.toFinset,
      (avoidGraph G J.toFinset).Reachable x y := by
    intro x hx y hy
    apply chain_reachable (L := Z) _ (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy)
    apply hchain.right_of_append.imp_of_mem_imp
    intro a b ha hb hab
    exact ⟨hab,fun hj => List.disjoint_left.mp hZJ ha (List.mem_toFinset.mp hj),
      fun hj => List.disjoint_left.mp hZJ hb (List.mem_toFinset.mp hj)⟩
  have hXne : X.toFinset.Nonempty := by
    rw [← Finset.card_pos,List.toFinset_card_of_nodup hnX]
    omega
  have hZne : Z.toFinset.Nonempty := by
    rw [← Finset.card_pos,List.toFinset_card_of_nodup hnZ]
    omega
  have hmX : (L.length : ℝ)/4 ≤ X.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnX]
    have : (L.length : ℝ) ≤ 4*(X.length:ℝ) := by exact_mod_cast houterX
    linarith
  have hmZ : (L.length : ℝ)/4 ≤ Z.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnZ]
    have : (L.length : ℝ) ≤ 4*(Z.length:ℝ) := by exact_mod_cast houterZ
    linarith
  have hsmallJ : (J.toFinset.card : ℝ) < α*((L.length:ℝ)/4) := by
    rw [List.toFinset_card_of_nodup hnJ,hJlen]
    have hmul := mul_le_mul_of_nonneg_left hL (le_of_lt hα)
    dsimp [q] at hjle
    nlinarith
  obtain ⟨x,hx,z,hz,p,hp,hpavoid⟩ := shortest_set_connector G X.toFinset Z.toFinset J.toFinset hXJf
    (connector_exists G α ((L.length:ℝ)/4) (le_of_lt hα) hexp
      X.toFinset Z.toFinset J.toFinset hXne hZne hXJf hZJf hconnX hconnZ hmX hmZ hsmallJ)
  obtain ⟨a,c,hc,hlen⟩ := cycle_across_middle G X J Z hnd hchain (by omega)
    ⟨x,List.mem_toFinset.mp hx,z,List.mem_toFinset.mp hz,p,hp,by simpa using hpavoid⟩
  refine ⟨a,c,hc,?_⟩
  rw [hJlen] at hlen
  have hlR : (j:ℝ)+2 ≤ c.length := by exact_mod_cast hlen
  change q < (c.length:ℝ)
  linarith

end ErdosGallai.Scale

namespace ErdosGallai.Scale
open _root_.Finset _root_.SimpleGraph Classical
variable {V : Type cycleUniverse5} [Fintype V] [DecidableEq V]

def SupportedOn (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ ⦃x y⦄, G.Adj x y → x ∈ A ∧ y ∈ A

structure AssignedPiece (V : Type cycleUniverse6) [DecidableEq V] where
  vertices : Finset V
  graph : SimpleGraph V
  supported : SupportedOn graph vertices

noncomputable def restrictGraph (G : SimpleGraph V) (A : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ A ∧ y ∈ A
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

noncomputable def crossingGraph (G : SimpleGraph V) (A B : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ((x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim (fun h => Or.inr ⟨h.2,h.1⟩)
    (fun h => Or.inl ⟨h.2,h.1⟩)⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

noncomputable def edgeOccurrences (L : List (SimpleGraph V)) (x y : V) : ℕ := by
  classical
  exact L.countP (fun H => H.Adj x y)

def GraphPartition (G : SimpleGraph V) (L : List (SimpleGraph V)) : Prop :=
  ∀ x y, edgeOccurrences L x y = if G.Adj x y then 1 else 0

noncomputable def edgeCount (G : SimpleGraph V) : ℕ := by
  classical
  exact G.edgeFinset.card

noncomputable def cutCount (G : SimpleGraph V) (A B : Finset V) : ℕ := by
  classical
  exact (G.interedges A B).card

def CutExpansionOn (G : SimpleGraph V) (A : Finset V) (h : ℝ) : Prop :=
  ∀ U ⊆ A, h * min (U.card : ℝ) ((A \ U).card : ℝ) ≤ cutCount G U (A \ U)

@[simp] lemma edgeOccurrences_nil {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (x y : V) : edgeOccurrences [] x y = 0 := by
  classical
  simp [edgeOccurrences]
@[simp] lemma edgeOccurrences_cons {V : Type cycleUniverse8} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (H : SimpleGraph V) (L) (x y : V) :
    edgeOccurrences (H::L) x y = (if H.Adj x y then 1 else 0) + edgeOccurrences L x y := by
  classical
  simp [edgeOccurrences, List.countP_cons, Nat.add_comm]
@[simp] lemma edgeOccurrences_append {V : Type cycleUniverse9} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L M : List (SimpleGraph V)) (x y : V) :
    edgeOccurrences (L++M) x y = edgeOccurrences L x y + edgeOccurrences M x y := by
  classical
  simp [edgeOccurrences]

lemma restrictGraph_le {V : Type cycleUniverse10} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (A : Finset V) : restrictGraph G A ≤ G :=
  fun _ _ h => h.1
lemma restrictGraph_supported {V : Type cycleUniverse11} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (A : Finset V) :
    SupportedOn (restrictGraph G A) A := fun _ _ h => h.2

lemma partition_member_le {V : Type cycleUniverse12} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {G : SimpleGraph V} {L : List (SimpleGraph V)}
    (h : GraphPartition G L) {H : SimpleGraph V} (hH : H ∈ L) : H ≤ G := by
  classical
  intro x y hxy
  by_contra hn
  have hc := h x y
  simp only [hn, ite_false] at hc
  have hp : 0 < edgeOccurrences L x y := by
    simpa [edgeOccurrences, List.countP_pos_iff] using (show ∃ K ∈ L, K.Adj x y from ⟨H,hH,hxy⟩)
  omega

@[simp] lemma edgeCount_bot {V : Type cycleUniverse13} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] : edgeCount (⊥ : SimpleGraph V) = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false] at he

noncomputable def splitPotential (T x : ℝ) : ℝ :=
  1 + 1 / logb 2 (T/2) - 1 / logb 2 (max x (T/2))

lemma logb_four_thirds : (1/4:ℝ) ≤ logb 2 (4/3) := by
  have h := Real.logb_le_logb_of_le (b:=2) (x:=2) (y:=(4/3:ℝ)^4)
    (by norm_num) (by norm_num) (by norm_num)
  rw [Real.logb_pow] at h
  norm_num only [Real.logb_self_eq_one, Nat.cast_ofNat] at h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

lemma splitPotential_bounds (T x : ℝ) (hT : 4 ≤ T) :
    1 ≤ splitPotential T x ∧ splitPotential T x ≤ 2 := by
  have hbase : 1 ≤ logb 2 (T/2) := by
    have hh := Real.logb_le_logb_of_le (b:=2) (x:=2) (y:=T/2)
      (by norm_num) (by norm_num) (by linarith)
    norm_num [Real.logb] at hh
    exact hh
  have hlog := Real.logb_le_logb_of_le (b:=2) (x:=T/2) (y:=max x (T/2))
    (by norm_num) (by linarith) (le_max_right _ _)
  have hsmall : 0 < logb 2 (T/2) := by linarith
  have hbig : 0 < logb 2 (max x (T/2)) := by linarith
  have hrecip : 1 / logb 2 (max x (T/2)) ≤ 1 / logb 2 (T/2) :=
    one_div_le_one_div_of_le hsmall hlog
  have hrecipone : 1/logb 2 (T/2) ≤ 1 := (div_le_one hsmall).mpr hbase
  dsimp [splitPotential]
  constructor
  · linarith
  · linarith [one_div_pos.mpr hbig]

lemma splitPotential_monotone (T : ℝ) (hT : 4 ≤ T) : Monotone (splitPotential T) := by
  intro x y hxy
  have hpos : 0 < T/2 := by linarith
  have hlogx : 0 < logb 2 (max x (T/2)) :=
    Real.logb_pos (by norm_num) (lt_of_lt_of_le (by linarith : 1 < T/2) (le_max_right _ _))
  have hlog := Real.logb_le_logb_of_le (b:=2) (by norm_num)
    (lt_of_lt_of_le hpos (le_max_right x (T/2))) (max_le_max hxy le_rfl)
  have hi := one_div_le_one_div_of_le hlogx hlog
  dsimp [splitPotential]
  linarith

lemma split_potential_decrement (T u u₁ : ℝ) (hT : 4 ≤ T) (hu : T < u)
    (h₁ : u₁ ≤ 3*u/4) :
    (1/4:ℝ)/(logb 2 u)^2 ≤ splitPotential T u - splitPotential T u₁ := by
  let M := max u₁ (T/2)
  have hu0 : 0 < u := by linarith
  have hM0 : 0 < M := lt_of_lt_of_le (by linarith : 0 < T/2) (le_max_right _ _)
  have hMu : M ≤ 3*u/4 := max_le h₁ (by linarith)
  have hMlt : M ≤ u := by linarith
  have hLu : 0 < logb 2 u := Real.logb_pos (by norm_num) (by linarith)
  have hLM : 0 < logb 2 M := Real.logb_pos (by norm_num)
    (lt_of_lt_of_le (by linarith : 1 < T/2) (le_max_right _ _))
  have hlle : logb 2 M ≤ logb 2 u :=
    Real.logb_le_logb_of_le (by norm_num) hM0 hMlt
  have hquot : (4/3:ℝ) ≤ u/M := (le_div_iff₀ hM0).mpr (by linarith)
  have hlogq := Real.logb_le_logb_of_le (b:=2) (x:=4/3) (y:=u/M)
    (by norm_num) (by norm_num) hquot
  rw [Real.logb_div hu0.ne' hM0.ne'] at hlogq
  have hgap : (1/4:ℝ) ≤ logb 2 u - logb 2 M := logb_four_thirds.trans hlogq
  have hmax : max u (T/2) = u := max_eq_left (by linarith)
  dsimp [splitPotential]
  rw [hmax]
  change (1/4:ℝ)/(logb 2 u)^2 ≤
    (1+1/logb 2 (T/2)-1/logb 2 u) - (1+1/logb 2 (T/2)-1/logb 2 M)
  have hid : (1+1/logb 2 (T/2)-1/logb 2 u) - (1+1/logb 2 (T/2)-1/logb 2 M) =
      (logb 2 u-logb 2 M)/(logb 2 M*logb 2 u) := by field_simp; ring
  rw [hid]
  apply (div_le_div_iff₀ (sq_pos_of_pos hLu) (mul_pos hLM hLu)).mpr
  have hm := mul_le_mul_of_nonneg_right hlle hLu.le
  nlinarith [sq_nonneg (logb 2 u)]

lemma split_potential_subadditive (T u u₁ u₂ : ℝ) (hT : 4 ≤ T) (hu : T < u)
    (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂) (h₁ : u₁ ≤ 3*u/4) (h₂ : u₂ ≤ u)
    (hsum : u₁+u₂ ≤ u+(1/32:ℝ)*u₁/(logb 2 u)^2) :
    u₁*splitPotential T u₁ + u₂*splitPotential T u₂ ≤ u*splitPotential T u := by
  have hdec := split_potential_decrement T u u₁ hT hu h₁
  have hmono := splitPotential_monotone T hT h₂
  obtain ⟨hfpos,hfhi⟩ := splitPotential_bounds T u hT
  have h₁cost := mul_le_mul_of_nonneg_left hdec hu₁
  have h₂cost := mul_le_mul_of_nonneg_left hmono hu₂
  have hLu : 0 < logb 2 u := Real.logb_pos (by norm_num) (by linarith)
  have hden : 0 < (logb 2 u)^2 := sq_pos_of_pos hLu
  have hsumcost := mul_le_mul_of_nonneg_right hsum (by linarith : 0 ≤ splitPotential T u)
  have hwt : 0 ≤ u₁/(logb 2 u)^2 := div_nonneg hu₁ hden.le
  have hratio : u₁*((1/4:ℝ)/(logb 2 u)^2) = (1/4:ℝ)*(u₁/(logb 2 u)^2) := by ring
  have hratio2 : ((1/32:ℝ)*u₁/(logb 2 u)^2)*splitPotential T u =
      (1/32:ℝ)*(u₁/(logb 2 u)^2)*splitPotential T u := by ring
  simp only [add_mul] at hsumcost
  rw [hratio2] at hsumcost
  rw [hratio] at h₁cost
  nlinarith

noncomputable def externalOn (G : SimpleGraph V) (U : Finset V) : Finset V :=
  univ.filter (fun v => v ∉ U ∧ ∃ u ∈ U, G.Adj u v)

lemma externalOn_subset {G : SimpleGraph V} {A U : Finset V} (hG : SupportedOn G A) :
    externalOn G U ⊆ A := by
  intro x hx
  obtain ⟨u,hu,hadj⟩ := (Finset.mem_filter.mp hx).2.2
  exact (hG hadj).2

lemma externalOn_disjoint (G : SimpleGraph V) (U : Finset V) :
    Disjoint U (externalOn G U) := by
  apply Finset.disjoint_left.mpr
  intro x hx hn
  exact (Finset.mem_filter.mp hn).2.1 hx

lemma overlap_child_supported {G : SimpleGraph V} {A U : Finset V}
    (hG : SupportedOn G A) (_hU : U ⊆ A) :
    SupportedOn (G \ restrictGraph G (U ∪ externalOn G U)) (A\U) := by
  intro x y hxy
  obtain ⟨hx,hy⟩ := hG hxy.1
  have hb (x y : V) (hxy : G.Adj x y) (hx : x ∈ U) : y ∈ U ∪ externalOn G U := by
    by_cases hy : y ∈ U
    · exact Finset.mem_union_left _ hy
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy,x,hx,hxy⟩)
  constructor
  · refine Finset.mem_sdiff.mpr ⟨hx,fun hxU => ?_⟩
    exact hxy.2 ⟨hxy.1,Finset.mem_union_left _ hxU,hb x y hxy.1 hxU⟩
  · refine Finset.mem_sdiff.mpr ⟨hy,fun hyU => ?_⟩
    exact hxy.2 ⟨hxy.1,hb y x hxy.1.symm hyU,Finset.mem_union_left _ hyU⟩

lemma overlap_child_sizes {G : SimpleGraph V} {A U : Finset V} {T : ℝ}
    (hT : 4 ≤ T) (hlarge : T < (A.card : ℝ)) (hU : U ⊆ A)
    (hne : U.Nonempty) (hhalf : 2*U.card ≤ A.card)
    (hsparse : ((externalOn G U).card : ℝ) < (1/32:ℝ)*U.card/(logb 2 A.card)^2) :
    (U ∪ externalOn G U).Nonempty ∧ (A\U).Nonempty ∧
    ((U ∪ externalOn G U).card : ℝ) ≤ 3*A.card/4 ∧
    (A\U).card < A.card ∧
    ((U ∪ externalOn G U).card : ℝ) + (A\U).card ≤
      A.card+(1/32:ℝ)*(U ∪ externalOn G U).card/(logb 2 A.card)^2 := by
  have hu : 0 < U.card := hne.card_pos
  have hlog : 1 ≤ logb 2 (A.card : ℝ) := by
    have h := Real.logb_le_logb_of_le (b:=2) (x:=2) (y:=A.card)
      (by norm_num) (by norm_num) (by linarith)
    norm_num [Real.logb] at h
    exact h
  have hd : 0 < (logb 2 (A.card : ℝ))^2 := by positivity
  have hquot : (1/32:ℝ)/(logb 2 (A.card : ℝ))^2 ≤ 1/2 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg (logb 2 (A.card : ℝ)-1)]
  have hsmall : ((externalOn G U).card : ℝ) < (U.card : ℝ)/2 := by
    have hm := mul_le_mul_of_nonneg_right hquot (Nat.cast_nonneg U.card)
    have hid : (1/32:ℝ)/(logb 2 (A.card : ℝ))^2 * U.card =
        (1/32:ℝ)*U.card/(logb 2 (A.card : ℝ))^2 := by ring
    rw [hid] at hm
    linarith
  have hcard₁ := Finset.card_union_of_disjoint (externalOn_disjoint G U)
  have hcard₂ := Finset.card_sdiff_add_card_eq_card hU
  have hcard₁R : ((U ∪ externalOn G U).card : ℝ) = U.card+(externalOn G U).card := by
    exact_mod_cast hcard₁
  have hcard₂R : ((A\U).card : ℝ) + U.card = A.card := by exact_mod_cast hcard₂
  have hhalfR : 2*(U.card : ℝ) ≤ A.card := by exact_mod_cast hhalf
  have hmon : (1/32:ℝ)*U.card/(logb 2 A.card)^2 ≤
      (1/32:ℝ)*(U ∪ externalOn G U).card/(logb 2 A.card)^2 := by
    gcongr
    exact Finset.subset_union_left
  refine ⟨hne.mono Finset.subset_union_left,?_,?_,?_,?_⟩
  · exact Finset.card_pos.mp (by omega)
  · linarith
  · omega
  · linarith

lemma partition_split_append {G K : SimpleGraph V} {L M : List (SimpleGraph V)}
    (hle : K ≤ G) (hL : GraphPartition K L) (hM : GraphPartition (G\K) M) :
    GraphPartition G (L++M) := by
  intro x y
  have h₁ := hL x y
  have h₂ := hM x y
  have hk := @hle x y
  simp only [edgeOccurrences_append,SimpleGraph.sdiff_adj] at h₂ ⊢
  by_cases hK : K.Adj x y <;> by_cases hG : G.Adj x y <;> simp_all

theorem box_recursion (G : SimpleGraph V) (A : Finset V) (T : ℝ)
    (hT : 4 ≤ T) (hA : A.Nonempty) (hG : SupportedOn G A)
    (hsplit : ∀ B ⊆ A, ∀ H : SimpleGraph V, H ≤ G → SupportedOn H B → T < (B.card : ℝ) →
      ∃ U ⊆ B, U.Nonempty ∧ 2*U.card ≤ B.card ∧
        ((externalOn H U).card : ℝ) < (1/32:ℝ)*U.card/(logb 2 B.card)^2) :
    ∃ L : List (AssignedPiece V),
      (∀ P ∈ L, P.vertices ⊆ A ∧ P.vertices.Nonempty ∧ (P.vertices.card : ℝ) ≤ T) ∧
      (∀ x ∈ A, ∃ P ∈ L, x ∈ P.vertices) ∧
      GraphPartition G (L.map AssignedPiece.graph) ∧
      (L.map (fun P => (P.vertices.card : ℝ)*splitPotential T P.vertices.card)).sum ≤
        (A.card : ℝ)*splitPotential T A.card := by
  classical
  induction hn : A.card using Nat.strong_induction_on generalizing A G with
  | h n ih =>
    by_cases hsmall : (A.card : ℝ) ≤ T
    · let P : AssignedPiece V := ⟨A,G,hG⟩
      refine ⟨[P],?_,?_,?_,?_⟩
      · intro Q hQ; simp only [List.mem_singleton] at hQ; subst Q
        exact ⟨Finset.Subset.refl _,hA,hsmall⟩
      · intro x hx; exact ⟨P,by simp,hx⟩
      · intro x y; simp [P]
      · simp [P,← hn]
    · have hlarge : T < (A.card : ℝ) := lt_of_not_ge hsmall
      obtain ⟨U,hU,hne,hhalf,hsparse⟩ := hsplit A (Finset.Subset.refl _) G le_rfl hG hlarge
      let B := externalOn G U
      let A₁ := U ∪ B
      let A₂ := A\U
      let G₁ := restrictGraph G A₁
      let G₂ := G\G₁
      have hA₁ : A₁ ⊆ A := Finset.union_subset hU (externalOn_subset hG)
      have hA₂ : A₂ ⊆ A := Finset.sdiff_subset
      have hG₁ : G₁ ≤ G := restrictGraph_le G A₁
      have hG₂ : G₂ ≤ G := sdiff_le
      have hs₁ : SupportedOn G₁ A₁ := restrictGraph_supported G A₁
      have hs₂ : SupportedOn G₂ A₂ := overlap_child_supported hG hU
      obtain ⟨hn₁,hn₂,hsize₁,hsize₂,hsum⟩ := overlap_child_sizes hT hlarge hU hne hhalf hsparse
      have hlt₁ : A₁.card < n := by
        have hn0 : (0 : ℝ) < A.card := by linarith
        have hlt : (A₁.card : ℝ) < A.card := lt_of_le_of_lt hsize₁ (by linarith)
        exact hn ▸ (Nat.cast_lt.mp hlt)
      have hlt₂ : A₂.card < n := hn ▸ hsize₂
      have subprem (D : Finset V) (hD : D ⊆ A) (K : SimpleGraph V) (hK : K ≤ G) :
          ∀ C ⊆ D, ∀ H : SimpleGraph V, H ≤ K → SupportedOn H C → T < (C.card : ℝ) →
            ∃ U ⊆ C, U.Nonempty ∧ 2*U.card ≤ C.card ∧
              ((externalOn H U).card : ℝ) < (1/32:ℝ)*U.card/(logb 2 C.card)^2 := by
        intro C hC H hH hs hlarge
        exact hsplit C (hC.trans hD) H (hH.trans hK) hs hlarge
      obtain ⟨L,hL,hcovL,hpartL,hcostL⟩ := ih _ hlt₁ G₁ A₁ hn₁ hs₁
        (subprem A₁ hA₁ G₁ hG₁) rfl
      obtain ⟨M,hM,hcovM,hpartM,hcostM⟩ := ih _ hlt₂ G₂ A₂ hn₂ hs₂
        (subprem A₂ hA₂ G₂ hG₂) rfl
      refine ⟨L++M,?_,?_,?_,?_⟩
      · intro P hP
        rcases List.mem_append.mp hP with hP | hP
        · obtain ⟨hsub,hne,hbound⟩ := hL P hP; exact ⟨hsub.trans hA₁,hne,hbound⟩
        · obtain ⟨hsub,hne,hbound⟩ := hM P hP; exact ⟨hsub.trans hA₂,hne,hbound⟩
      · intro x hx
        by_cases hxU : x ∈ U
        · obtain ⟨P,hP,hxP⟩ := hcovL x (Finset.mem_union_left _ hxU)
          exact ⟨P,List.mem_append_left _ hP,hxP⟩
        · obtain ⟨P,hP,hxP⟩ := hcovM x (Finset.mem_sdiff.mpr ⟨hx,hxU⟩)
          exact ⟨P,List.mem_append_right _ hP,hxP⟩
      · simpa only [List.map_append] using partition_split_append hG₁ hpartL hpartM
      · simp only [List.map_append,List.sum_append]
        have hsub := split_potential_subadditive T A.card A₁.card A₂.card hT hlarge
          (Nat.cast_nonneg _) (Nat.cast_nonneg _) hsize₁ (by exact_mod_cast hsize₂.le) hsum
        rw [← hn]
        linarith

end ErdosGallai.Scale
end
end

/-! ### Upstream module `Combinatorics/CycleDecomposition/ScaleExtraction.lean` -/

section
open _root_.Filter _root_.Asymptotics _root_.Real
noncomputable section
namespace ErdosGallai.Scale
open _root_.Finset _root_.SimpleGraph Classical
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]
lemma edgeCount_eq_card {V : Type cycleUniverse2} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (S : Finset (Sym2 V))
    (hS : ∀ e, e ∈ S ↔ e ∈ G.edgeSet) : edgeCount G = S.card := by
  unfold edgeCount
  congr 1
  ext e
  simp only [SimpleGraph.mem_edgeFinset]
  exact (hS e).symm

def IsCycleGraph (K : SimpleGraph V) : Prop :=
  ∃ a : V, ∃ p : K.Walk a a, p.IsCycle ∧ K.edgeSet = p.edgeSet

def NoLongCycle (G : SimpleGraph V) (ℓ : ℝ) : Prop :=
  ∀ a : V, ∀ p : G.Walk a a, p.IsCycle → (p.length : ℝ) < ℓ

lemma NoLongCycle.mono {V : Type cycleUniverse3} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {G H : SimpleGraph V} {ℓ : ℝ}
    (h : NoLongCycle G ℓ) (hle : H ≤ G) : NoLongCycle H ℓ := by
  intro a p hp
  simpa using h a (p.mapLe hle) (hp.mapLe hle)

lemma cycle_graph_of_walk (G : SimpleGraph V) {a : V} (p : G.Walk a a) (hp : p.IsCycle) :
    ∃ K : SimpleGraph V, K ≤ G ∧ IsCycleGraph K ∧ edgeCount K = p.length := by
  classical
  let K := SimpleGraph.fromEdgeSet p.edgeSet
  have he : K.edgeSet = p.edgeSet := by
    rw [SimpleGraph.edgeSet_fromEdgeSet,sdiff_eq_left]
    exact Set.disjoint_left.mpr (fun e he hd =>
      G.not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet he) hd)
  have hle : K ≤ G := SimpleGraph.edgeSet_subset_edgeSet.mp (he ▸ p.edges_subset_edgeSet)
  have htransfer : ∀ e ∈ p.edges, e ∈ K.edgeSet := by
    intro e he'; rw [he]; exact he'
  refine ⟨K,hle,⟨a,p.transfer K htransfer,hp.transfer htransfer,?_⟩,?_⟩
  · simpa using he
  · rw [edgeCount_eq_card K p.edges.toFinset (by
      intro e; simp only [List.mem_toFinset,he]; rfl)]
    exact (List.toFinset_card_of_nodup hp.isTrail.edges_nodup).trans p.length_edges

lemma edgeCount_sdiff_add {G K : SimpleGraph V} (hle : K ≤ G) :
    edgeCount (G \ K) + edgeCount K = edgeCount G := by
  classical
  rw [edgeCount_eq_card (G \ K) (G.edgeFinset \ K.edgeFinset) (by
    intro e; simp only [Finset.mem_sdiff,SimpleGraph.mem_edgeFinset,SimpleGraph.edgeSet_sdiff,
      Set.mem_sdiff]),
    edgeCount_eq_card K K.edgeFinset (by intro e; simp),
    edgeCount_eq_card G G.edgeFinset (by intro e; simp)]
  exact Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hle)

lemma edgeCount_cycle_pos {K : SimpleGraph V} (h : IsCycleGraph K) : 0 < edgeCount K := by
  classical
  obtain ⟨a,p,hp,he⟩ := h
  have hf : K.edgeFinset = p.edges.toFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset,he,List.mem_toFinset]
    rfl
  simp only [edgeCount,hf,List.toFinset_card_of_nodup hp.isTrail.edges_nodup,
    SimpleGraph.Walk.length_edges]
  exact hp.three_le_length.trans_lt' (by omega)

theorem remove_long_cycles (G : SimpleGraph V) (ℓ : ℝ) :
    ∃ (H : SimpleGraph V) (L : List (SimpleGraph V)),
      H ≤ G ∧ NoLongCycle H ℓ ∧
      (∀ K ∈ L, IsCycleGraph K ∧ ℓ ≤ (edgeCount K : ℝ)) ∧
      GraphPartition G (H::L) ∧
      (L.length : ℝ)*ℓ + edgeCount H ≤ edgeCount G := by
  classical
  induction hn : edgeCount G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hstop : NoLongCycle G ℓ
    · refine ⟨G,[],le_rfl,hstop,by simp,?_,?_⟩
      · intro x y; simp
      · simp [← hn]
    · obtain ⟨a,p,hp,hplen⟩ : ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ ℓ ≤ (p.length : ℝ) := by
        by_contra hh
        apply hstop
        intro a p hp
        by_contra hlen
        exact hh ⟨a,p,hp,le_of_not_gt hlen⟩
      obtain ⟨K,hle,hK,hKlen⟩ := cycle_graph_of_walk G p hp
      have heq := edgeCount_sdiff_add hle
      have hpos := edgeCount_cycle_pos hK
      have hlt : edgeCount (G \ K) < n := by omega
      obtain ⟨H,L,hH,hNL,hL,hpart,hbudget⟩ := ih _ hlt (G \ K) rfl
      refine ⟨H,K::L,hH.trans sdiff_le,hNL,?_,?_,?_⟩
      · intro J hJ
        rcases List.mem_cons.mp hJ with rfl | hJ
        · exact ⟨hK,by simpa [hKlen] using hplen⟩
        · exact hL J hJ
      · intro x y
        have hh := @hH x y
        have hk := @hle x y
        have he := hpart x y
        simp only [edgeOccurrences_cons,SimpleGraph.sdiff_adj] at he ⊢
        by_cases hG : G.Adj x y <;> by_cases hK : K.Adj x y <;>
          by_cases hH : H.Adj x y <;> simp_all
      · have heqR : (edgeCount (G \ K) : ℝ) + edgeCount K = edgeCount G := by exact_mod_cast heq
        have hKbound : ℓ ≤ (edgeCount K : ℝ) := by simpa [hKlen] using hplen
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
        rw [← hn]
        nlinarith

lemma longCycle_power_margin : ∀ᶠ u : ℝ in atTop,
    4 ≤ u ∧ u^(199/200:ℝ) ≤ ((1/32:ℝ)/(logb 2 u)^2)^2*u/100 := by
  have hlog := (isLittleO_log_rpow_rpow_atTop (4:ℝ)
    (s:=1/200) (by norm_num)).const_mul_left ((102400:ℝ)/(log 2)^4)
  filter_upwards [eventually_ge_atTop (4:ℝ),hlog.eventuallyLE] with u hu hh
  have hu0 : 0 < u := by linarith
  have hln : 0 ≤ log u := log_nonneg (by linarith)
  have hln2 : 0 < log 2 := log_pos (by norm_num)
  have hLu : 0 < logb 2 u := logb_pos (by norm_num) (by linarith)
  have hr0 : 0 ≤ u^(1/200:ℝ) := rpow_nonneg hu0.le _
  have hnum0 : 0 ≤ (102400:ℝ)/(log 2)^4 * (log u)^(4:ℝ) := by positivity
  simp only [Real.norm_eq_abs,abs_of_nonneg hnum0,abs_of_nonneg hr0] at hh
  have hden : (102400:ℝ)*(logb 2 u)^4 ≤ u^(1/200:ℝ) := by
    calc
      (102400:ℝ)*(logb 2 u)^4 = (102400:ℝ)/(log 2)^(4:ℕ) * (log u)^(4:ℕ) := by
        simp only [Real.logb,div_pow]; ring
      _ ≤ u^(1/200:ℝ) := by simpa only [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast] using hh
  have hm := mul_le_mul_of_nonneg_left hden (rpow_nonneg hu0.le (199/200:ℝ))
  have he : u^(199/200:ℝ)*u^(1/200:ℝ) = u := by
    rw [← Real.rpow_add hu0]; norm_num
  rw [he] at hm
  refine ⟨hu,?_⟩
  have hid : ((1/32:ℝ)/(logb 2 u)^2)^2*u/100 = u/(102400*(logb 2 u)^4) := by
    field_simp
    ; ring
  rw [hid]
  exact (le_div_iff₀ (by positivity : (0:ℝ) < 102400*(logb 2 u)^4)).mpr (by nlinarith)

lemma longCycle_scale_ready : ∃ Dsp : ℝ, ∀ D ≥ Dsp,
    4 ≤ D ∧ 4 ≤ D^(51/50:ℝ) ∧
    ∀ u : ℝ, D^(51/50:ℝ) < u →
      0 < (1/32:ℝ)/(logb 2 u)^2 ∧ (1/32:ℝ)/(logb 2 u)^2 ≤ 1 ∧
      1 ≤ ((1/32:ℝ)/(logb 2 u)^2)^2*u/100 ∧
      D^(101/100:ℝ) < ((1/32:ℝ)/(logb 2 u)^2)^2*u/100 := by
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp longCycle_power_margin
  refine ⟨max 4 Q,?_⟩
  intro D hD
  have hD4 : 4 ≤ D := (le_max_left _ _).trans hD
  have hD1 : 1 ≤ D := by linarith
  have hDp : 0 < D := by linarith
  have hTD : D ≤ D^(51/50:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hD1
      (by norm_num : (1:ℝ) ≤ 51/50)
  refine ⟨hD4,hD4.trans hTD,?_⟩
  intro u hu
  have huQ : Q ≤ u := (le_max_right 4 Q).trans (hD.trans (hTD.trans hu.le))
  obtain ⟨hu4,hq⟩ := hQ u huQ
  have hlog : 1 ≤ logb 2 u := by
    have h := Real.logb_le_logb_of_le (b:=2) (x:=2) (y:=u)
      (by norm_num) (by norm_num) (by linarith)
    norm_num [Real.logb] at h
    exact h
  have hd : 0 < (logb 2 u)^2 := by positivity
  have hα : 0 < (1/32:ℝ)/(logb 2 u)^2 := by positivity
  have hα1 : (1/32:ℝ)/(logb 2 u)^2 ≤ 1 := by
    apply (div_le_one hd).mpr
    nlinarith [sq_nonneg (logb 2 u-1)]
  have hmargin : D^(101/100:ℝ) < u^(199/200:ℝ) := by
    have hstrict := Real.rpow_lt_rpow (Real.rpow_nonneg hDp.le (51/50:ℝ)) hu
      (by norm_num : (0:ℝ) < 199/200)
    rw [← Real.rpow_mul hDp.le] at hstrict
    have hle := Real.rpow_le_rpow_of_exponent_le hD1
      (by norm_num : (101/100:ℝ) ≤ (51/50)*(199/200))
    exact hle.trans_lt hstrict
  have hpow1 : 1 ≤ D^(101/100:ℝ) := Real.one_le_rpow hD1 (by norm_num)
  exact ⟨hα,hα1,hpow1.trans (hmargin.le.trans hq),hmargin.trans_le hq⟩

lemma external_induce_image (G : SimpleGraph V) (A : Finset V) (hG : SupportedOn G A)
    (U : Finset {x // x ∈ A}) :
    externalOn G (U.image Subtype.val) =
      (externalOn (G.induce (A : Set V)) U).image Subtype.val := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨_,hyU,x,hx,hxy⟩ := Finset.mem_filter.mp hy
    have hyA := (hG hxy).2
    obtain ⟨x',hx',heq⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨⟨y,hyA⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩,rfl⟩
    · intro hy'
      exact hyU (Finset.mem_image.mpr ⟨⟨y,hyA⟩,hy',rfl⟩)
    · exact ⟨x',hx',by simpa only [SimpleGraph.induce_adj,heq] using hxy⟩
  · intro hy
    obtain ⟨y',hy',rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨_,hyU,x,hx,hxy⟩ := Finset.mem_filter.mp hy'
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩
    · intro hy
      obtain ⟨z,hz,heq⟩ := Finset.mem_image.mp hy
      have heq' : z = y' := Subtype.ext heq
      exact hyU (heq' ▸ hz)
    · exact ⟨x,Finset.mem_image.mpr ⟨x,hx,rfl⟩,hxy⟩

lemma sparse_neighborhood_from_cycle_exclusion (G : SimpleGraph V) (A : Finset V)
    (hG : SupportedOn G A) (ℓ : ℝ) (hNL : NoLongCycle G ℓ)
    (hα : 0 < (1/32:ℝ)/(logb 2 A.card)^2)
    (hα1 : (1/32:ℝ)/(logb 2 A.card)^2 ≤ 1)
    (hq : 1 ≤ ((1/32:ℝ)/(logb 2 A.card)^2)^2*A.card/100)
    (hmargin : ℓ < ((1/32:ℝ)/(logb 2 A.card)^2)^2*A.card/100) :
    ∃ U ⊆ A, U.Nonempty ∧ 2*U.card ≤ A.card ∧
      ((externalOn G U).card : ℝ) < (1/32:ℝ)*U.card/(logb 2 A.card)^2 := by
  classical
  by_contra hno
  let H := G.induce (A : Set V)
  let α := (1/32:ℝ)/(logb 2 A.card)^2
  have hexp : VertexExpansion H α := by
    intro U hU hhalf
    let W := U.image Subtype.val
    have hW : W ⊆ A := by
      intro x hx
      obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hx
      exact x'.property
    have hcard : W.card = U.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hWne : W.Nonempty := hU.image _
    have hWhalf : 2*W.card ≤ A.card := by simpa [hcard] using hhalf
    have hs : ¬ ((externalOn G W).card : ℝ) < (1/32:ℝ)*W.card/(logb 2 A.card)^2 :=
      fun hs => hno ⟨W,hW,hWne,hWhalf,hs⟩
    have hbound := le_of_not_gt hs
    have heq := external_induce_image G A hG U
    have hcardext := congrArg Finset.card heq
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcardext
    have hext : externalNeighbors H U = externalOn H U := by rfl
    rw [hext]
    change α*(U.card:ℝ) ≤ (externalOn H U).card
    rw [← hcardext]
    dsimp [α]
    rw [← hcard]
    calc
      (1/32:ℝ)/(logb 2 A.card)^2 * (W.card:ℝ) = (1/32:ℝ)*(W.card:ℝ)/(logb 2 A.card)^2 := by ring
      _ ≤ ((externalOn G W).card:ℝ) := hbound
  have hq' : 1 ≤ α^2*(Fintype.card {x // x ∈ A})/100 := by simpa [α] using hq
  obtain ⟨a,p,hp,hplen⟩ := long_cycle_of_vertex_expansion H α hα hα1 hexp hq'
  let f : H →g G := ⟨Subtype.val,fun h => h⟩
  have hc := hp.map (f:=f) (by exact Subtype.val_injective)
  have hlen := hNL a.val (p.map f) hc
  simp only [SimpleGraph.Walk.length_map] at hlen
  have hplen' : α^2*(A.card:ℝ)/100 < (p.length:ℝ) := by simpa using hplen
  dsimp [α] at hplen'
  linarith

lemma splitPotential_scale_bound (D x : ℝ) (hD : 4 ≤ D) :
    splitPotential (D^(51/50:ℝ)) x ≤ 1+2/logb 2 D := by
  have hD1 : 1 ≤ D := by linarith
  have hDp : 0 < D := by linarith
  have hLD : 2 ≤ logb 2 D := by
    have h := Real.logb_le_logb_of_le (b:=2) (x:=4) (y:=D)
      (by norm_num) (by norm_num) hD
    have h4 : logb 2 (4:ℝ) = 2 := by
      rw [show (4:ℝ) = 2^(2:ℕ) by norm_num,Real.logb_pow]
      norm_num
    rw [h4] at h
    exact h
  have hLD0 : 0 < logb 2 D := by linarith
  have hlogT : logb 2 (D^(51/50:ℝ)/2) = (51/50:ℝ)*logb 2 D-1 := by
    rw [Real.logb_div (Real.rpow_pos_of_pos hDp _).ne' (by norm_num),
      Real.logb_rpow_eq_mul_logb_of_pos hDp]
    norm_num
  have hT0 : 0 < logb 2 (D^(51/50:ℝ)/2) := by rw [hlogT]; linarith
  have hrecip : 1/logb 2 (D^(51/50:ℝ)/2) ≤ 2/logb 2 D := by
    apply (div_le_div_iff₀ hT0 hLD0).mpr
    rw [hlogT]
    linarith
  have hbasepos : 0 < D^(51/50:ℝ)/2 := by positivity
  have hmaxlog := Real.logb_le_logb_of_le (b:=2) (by norm_num) hbasepos
    (le_max_right x (D^(51/50:ℝ)/2))
  have hmax0 : 0 < logb 2 (max x (D^(51/50:ℝ)/2)) := lt_of_lt_of_le hT0 hmaxlog
  have hinv := one_div_pos.mpr hmax0
  dsimp [splitPotential]
  linarith

lemma partition_replace_head {G H : SimpleGraph V} {C L : List (SimpleGraph V)}
    (hG : GraphPartition G (H::C)) (hH : GraphPartition H L) :
    GraphPartition G (C++L) := by
  intro x y
  have h := hG x y
  simp only [edgeOccurrences_cons] at h
  rw [edgeOccurrences_append,hH x y]
  omega

theorem scale_boxes : ∃ Dsp : ℝ, ∀ D ≥ Dsp,
    ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (A : Finset V), A.Nonempty → SupportedOn G A →
      2*(edgeCount G : ℝ)/A.card ≤ D →
    ∃ (C : List (SimpleGraph V)) (L : List (AssignedPiece V)),
      (∀ K ∈ C, IsCycleGraph K ∧ D^(101/100:ℝ) ≤ (edgeCount K : ℝ)) ∧
      (C.length : ℝ) ≤ A.card/(2*D^(1/100:ℝ)) ∧
      (∀ P ∈ L, P.vertices ⊆ A ∧ P.vertices.Nonempty ∧ (P.vertices.card : ℝ) ≤ D^(51/50:ℝ)) ∧
      (∀ x ∈ A, ∃ P ∈ L, x ∈ P.vertices) ∧
      GraphPartition G (C++L.map AssignedPiece.graph) ∧
      (L.map (fun P => (P.vertices.card : ℝ))).sum ≤ (1+2/logb 2 D)*A.card := by
  classical
  obtain ⟨Dsp,hsp⟩ := longCycle_scale_ready
  refine ⟨Dsp,?_⟩
  intro D hD V _ _ G A hA hG hdeg
  obtain ⟨hD4,hT4,hnum⟩ := hsp D hD
  have hDp : 0 < D := by linarith
  have hA0 : (0:ℝ) < A.card := by exact_mod_cast hA.card_pos
  obtain ⟨H,C,hHG,hNL,hC,hpartC,hbudget⟩ := remove_long_cycles G (D^(101/100:ℝ))
  have hHA : SupportedOn H A := fun _ _ h => hG (hHG h)
  have hsplit : ∀ B ⊆ A, ∀ K : SimpleGraph V, K ≤ H → SupportedOn K B → D^(51/50:ℝ) < (B.card:ℝ) →
      ∃ U ⊆ B, U.Nonempty ∧ 2*U.card ≤ B.card ∧
        ((externalOn K U).card : ℝ) < (1/32:ℝ)*U.card/(logb 2 B.card)^2 := by
    intro B hB K hK hs hlarge
    obtain ⟨ha,ha1,hq,hm⟩ := hnum B.card hlarge
    exact sparse_neighborhood_from_cycle_exclusion K B hs _ (hNL.mono hK) ha ha1 hq hm
  obtain ⟨L,hL,hcov,hpartL,hcost⟩ := box_recursion H A (D^(51/50:ℝ)) hT4 hA hHA hsplit
  refine ⟨C,L,hC,?_,hL,hcov,partition_replace_head hpartC hpartL,?_⟩
  · have hdeg' := (div_le_iff₀ hA0).mp hdeg
    have he : D^(101/100:ℝ) = D*D^(1/100:ℝ) := by
      rw [show (101/100:ℝ) = 1+1/100 by norm_num,Real.rpow_add hDp,Real.rpow_one]
    rw [he] at hbudget
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 2*D^(1/100:ℝ))).mpr
    have hnonneg : (0:ℝ) ≤ edgeCount H := Nat.cast_nonneg _
    nlinarith
  · have hfbound := splitPotential_scale_bound D A.card hD4
    have hplain : (L.map (fun P => (P.vertices.card:ℝ))).sum ≤
        (L.map (fun P => (P.vertices.card:ℝ)*splitPotential (D^(51/50:ℝ)) P.vertices.card)).sum := by
      apply List.sum_le_sum
      intro P hP
      have hb := (splitPotential_bounds (D^(51/50:ℝ)) P.vertices.card hT4).1
      have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg P.vertices.card)
      simpa using hm
    have hmul := mul_le_mul_of_nonneg_left hfbound hA0.le
    nlinarith

end ErdosGallai.Scale

namespace ErdosGallai.Scale
open _root_.Finset _root_.SimpleGraph Classical _root_.Real
variable {V : Type cycleUniverse4} [Fintype V] [DecidableEq V]

lemma edgeCount_sup_le (G H : SimpleGraph V) : edgeCount (G ⊔ H) ≤ edgeCount G + edgeCount H := by
  classical
  simpa [edgeCount, SimpleGraph.edgeFinset_sup] using Finset.card_union_le G.edgeFinset H.edgeFinset

lemma crossing_count (G : SimpleGraph V) (A B : Finset V) (hd : Disjoint A B) :
    edgeCount (crossingGraph G A B) = cutCount G A B := by
  classical
  have hinj : Set.InjOn (fun e : V × V => s(e.1,e.2)) (G.interedges A B : Set (V×V)) := by
    intro e he f hf hh
    rcases Sym2.mk_eq_mk_iff.mp hh with hh | hh
    · exact hh
    · have heA := (G.mem_interedges_iff.mp he).1
      have hfB := (G.mem_interedges_iff.mp hf).2.1
      have heq : e.1 = f.2 := congrArg Prod.fst hh
      exact False.elim (Finset.disjoint_left.mp hd heA (heq.symm ▸ hfB))
  have heq : (crossingGraph G A B).edgeFinset =
      (G.interedges A B).image (fun e : V×V => s(e.1,e.2)) := by
    ext e
    induction e using Sym2.inductionOn with | _ x y =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨hxy,(⟨hx,hy⟩|⟨hx,hy⟩)⟩
        · exact Finset.mem_image.mpr ⟨(x,y),G.mem_interedges_iff.mpr ⟨hx,hy,hxy⟩,rfl⟩
        · exact Finset.mem_image.mpr ⟨(y,x),G.mem_interedges_iff.mpr ⟨hy,hx,hxy.symm⟩,
            Sym2.eq_swap⟩
      · rintro h
        obtain ⟨⟨a,b⟩,hab,he⟩ := Finset.mem_image.mp h
        obtain ⟨ha,hb,hg⟩ := G.mem_interedges_iff.mp hab
        rcases (Sym2.mk_eq_mk_iff (p := (a,b)) (q := (x,y))).mp he with he | he
        · cases he; exact ⟨hg,Or.inl ⟨ha,hb⟩⟩
        · cases he; exact ⟨hg.symm,Or.inr ⟨hb,ha⟩⟩
  simp only [edgeCount,heq,Finset.card_image_of_injOn hinj,cutCount]

lemma log2_split_budget {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    min a b + a*a.log2 + b*b.log2 ≤ (a+b)*(a+b).log2 := by
  have hm : Monotone Nat.log2 := by
    intro m n h
    simpa only [Nat.log2_eq_log_two] using (Nat.log_mono_right (b:=2) h)
  have hla := hm (show a ≤ a+b by omega)
  have hlb := hm (show b ≤ a+b by omega)
  rcases le_total a b with hab | hba
  · have hhalf := hm (show 2*a ≤ a+b by omega)
    rw [Nat.log2_two_mul (by omega)] at hhalf
    rw [min_eq_left hab]
    nlinarith
  · have hhalf := hm (show 2*b ≤ a+b by omega)
    rw [Nat.log2_two_mul (by omega)] at hhalf
    rw [min_eq_right hba]
    nlinarith

lemma partition_combine {G K G₁ G₂ H₁ H₂ : SimpleGraph V}
    {L₁ L₂ : List (SimpleGraph V)}
    (hp₁ : GraphPartition G₁ (H₁::L₁)) (hp₂ : GraphPartition G₂ (H₂::L₂))
    (hcover : ∀ x y, G.Adj x y ↔ K.Adj x y ∨ G₁.Adj x y ∨ G₂.Adj x y)
    (hd₁ : Disjoint K G₁) (hd₂ : Disjoint K G₂) (hd₃ : Disjoint G₁ G₂) :
    GraphPartition G ((K ⊔ H₁ ⊔ H₂)::(L₁++L₂)) := by
  classical
  have hle₁ : H₁ ≤ G₁ := partition_member_le hp₁ (by simp)
  have hle₂ : H₂ ≤ G₂ := partition_member_le hp₂ (by simp)
  intro x y
  have h₁ := hp₁ x y
  have h₂ := hp₂ x y
  have hd₁ := SimpleGraph.disjoint_left.mp hd₁ x y
  have hd₂ := SimpleGraph.disjoint_left.mp hd₂ x y
  have hd₃ := SimpleGraph.disjoint_left.mp hd₃ x y
  have hh₁ := @hle₁ x y
  have hh₂ := @hle₂ x y
  have hc := hcover x y
  simp only [edgeOccurrences_cons,edgeOccurrences_append,SimpleGraph.sup_adj] at *
  by_cases hK : K.Adj x y <;> by_cases hG₁ : G₁.Adj x y <;>
    by_cases hG₂ : G₂.Adj x y <;> by_cases hH₁ : H₁.Adj x y <;>
    by_cases hH₂ : H₂.Adj x y <;> simp_all

lemma cut_split_properties {V : Type cycleUniverse5} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (A U : Finset V)
    (hG : SupportedOn G A) (_hU : U ⊆ A) :
    (∀ x y, G.Adj x y ↔ (crossingGraph G U (A\U)).Adj x y ∨
        (restrictGraph G U).Adj x y ∨ (restrictGraph G (A\U)).Adj x y) ∧
    Disjoint (crossingGraph G U (A\U)) (restrictGraph G U) ∧
    Disjoint (crossingGraph G U (A\U)) (restrictGraph G (A\U)) ∧
    Disjoint (restrictGraph G U) (restrictGraph G (A\U)) := by
  constructor
  · intro x y
    change G.Adj x y ↔ (G.Adj x y ∧ _) ∨ (G.Adj x y ∧ _) ∨ (G.Adj x y ∧ _)
    have hs := @hG x y
    simp only [Finset.mem_sdiff]
    tauto
  · simp only [SimpleGraph.disjoint_left, crossingGraph, restrictGraph,Finset.mem_sdiff]
    tauto

lemma empty_supported_graph {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {G : SimpleGraph V} {A : Finset V}
    (hG : SupportedOn G A) (hA : A.card ≤ 1) : G = ⊥ := by
  ext x y
  constructor
  · intro h
    obtain ⟨hx,hy⟩ := hG h
    have hxy := Finset.card_le_one.mp hA x hx y hy
    exact False.elim (G.ne_of_adj h hxy)
  · simp

theorem cut_extraction (G : SimpleGraph V) (A : Finset V)
    (hG : SupportedOn G A) (σ : ℝ) (hσ : 0 ≤ σ) :
    ∃ (R : List (AssignedPiece V)) (H : SimpleGraph V),
      (∀ P ∈ R, P.vertices ⊆ A ∧ 2 ≤ P.vertices.card ∧
        CutExpansionOn P.graph P.vertices σ) ∧
      R.Pairwise (fun P Q => Disjoint P.vertices Q.vertices) ∧
      GraphPartition G (H :: R.map AssignedPiece.graph) ∧
      SupportedOn H A ∧
      (edgeCount H : ℝ) ≤ σ * A.card * A.card.log2 := by
  classical
  induction hcard : A.card using Nat.strong_induction_on generalizing A G with
  | h n ih =>
    by_cases hsmall : A.card ≤ 1
    · have he := empty_supported_graph hG hsmall
      refine ⟨[],⊥,by simp,by simp,?_,?_,?_⟩
      · subst G
        intro x y
        simp
      · intro x y h; exact False.elim h
      · simp only [edgeCount_bot,Nat.cast_zero]
        positivity
    by_cases hexp : CutExpansionOn G A σ
    · refine ⟨[⟨A,G,hG⟩],⊥,?_,by simp,?_,?_,?_⟩
      · intro P hP
        have he := List.mem_singleton.mp hP
        subst P
        exact ⟨fun _ h => h,by change 2 ≤ A.card; omega,hexp⟩
      · intro x y; simp
      · intro x y h; exact False.elim h
      · simp only [edgeCount_bot,Nat.cast_zero]
        positivity
    unfold CutExpansionOn at hexp
    push Not at hexp
    obtain ⟨U,hU,hcut⟩ := hexp
    have hdisUB : Disjoint U (A\U) := Finset.disjoint_left.mpr
      (fun _ hu hb => (Finset.mem_sdiff.mp hb).2 hu)
    have hcnt : (0 : ℝ) ≤ cutCount G U (A\U) := Nat.cast_nonneg _
    have hσpos : 0 < σ := by
      by_contra h
      have : σ = 0 := le_antisymm (le_of_not_gt h) hσ
      rw [this,zero_mul] at hcut
      linarith
    have hUpos : 0 < U.card := by
      by_contra h
      have hz : U.card = 0 := by omega
      simp [hz] at hcut
      linarith [min_le_left (0:ℝ) ((A\U).card:ℝ)]
    have hBpos : 0 < (A\U).card := by
      by_contra h
      have hz : (A\U).card = 0 := by omega
      simp [hz] at hcut
      linarith [min_le_right (U.card:ℝ) (0:ℝ)]
    have hcardSum := Finset.card_sdiff_add_card_eq_card hU
    have hUlt : U.card < n := by omega
    have hBlt : (A\U).card < n := by omega
    obtain ⟨R₁,H₁,hR₁,hd₁,hp₁,hs₁,hc₁⟩ := ih U.card hUlt (restrictGraph G U) U
      (restrictGraph_supported G U) rfl
    obtain ⟨R₂,H₂,hR₂,hd₂,hp₂,hs₂,hc₂⟩ := ih (A\U).card hBlt (restrictGraph G (A\U)) (A\U)
      (restrictGraph_supported G (A\U)) rfl
    let K := crossingGraph G U (A\U)
    obtain ⟨hcover,hdis₁,hdis₂,hdis₃⟩ := cut_split_properties G A U hG hU
    refine ⟨R₁++R₂,K ⊔ H₁ ⊔ H₂,?_,?_,?_,?_,?_⟩
    · intro P hP
      rcases List.mem_append.mp hP with hP | hP
      · obtain ⟨hPA,hPc,hPe⟩ := hR₁ P hP
        exact ⟨hPA.trans hU,hPc,hPe⟩
      · obtain ⟨hPA,hPc,hPe⟩ := hR₂ P hP
        exact ⟨hPA.trans Finset.sdiff_subset,hPc,hPe⟩
    · apply List.pairwise_append.mpr
      refine ⟨hd₁,hd₂,?_⟩
      intro P hP Q hQ
      exact hdisUB.mono
        (hR₁ P hP).1 (hR₂ Q hQ).1
    · simpa only [List.map_append] using partition_combine hp₁ hp₂ hcover hdis₁ hdis₂ hdis₃
    · intro x y h
      rcases h with (h|h)|h
      · exact hG h.1
      · exact ⟨hU (hs₁ h).1,hU (hs₁ h).2⟩
      · exact ⟨(Finset.mem_sdiff.mp (hs₂ h).1).1,(Finset.mem_sdiff.mp (hs₂ h).2).1⟩
    · have hcardK : edgeCount K = cutCount G U (A\U) :=
        crossing_count G U (A\U) hdisUB
      have hcost : (edgeCount (K⊔H₁⊔H₂) : ℝ) ≤
          edgeCount K + edgeCount H₁ + edgeCount H₂ := by
        exact_mod_cast (edgeCount_sup_le (K⊔H₁) H₂).trans
          (Nat.add_le_add_right (edgeCount_sup_le K H₁) _)
      have hpot := log2_split_budget hUpos hBpos
      have hpotR : min (U.card:ℝ) ((A\U).card:ℝ) + U.card*U.card.log2 +
          (A\U).card*(A\U).card.log2 ≤ (A.card:ℝ) * A.card.log2 := by
        have he : U.card+(A\U).card = A.card := by omega
        rw [he] at hpot
        exact_mod_cast hpot
      have hpay := mul_le_mul_of_nonneg_left hpotR hσ
      rw [hcardK] at hcost
      rw [← hcard]
      nlinarith

lemma cast_log2_le_logb {n : ℕ} (hn : 0 < n) : (n.log2 : ℝ) ≤ Real.logb 2 n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) (by exact_mod_cast hn)).mpr
  rw [Real.rpow_natCast, Nat.log2_eq_log_two]
  exact_mod_cast Nat.pow_log_le_self 2 hn.ne'

lemma expansion_order_lower {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {G : SimpleGraph V} {A : Finset V} {σ : ℝ}
    (hA : 2 ≤ A.card) (he : CutExpansionOn G A σ) : σ+1 ≤ A.card := by
  classical
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  have hsub : {x} ⊆ A := Finset.singleton_subset_iff.mpr hx
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  simp only [Finset.card_singleton] at hcard
  have hB : (1:ℝ) ≤ (A\{x}).card := by exact_mod_cast (show 1 ≤ (A\{x}).card by omega)
  have hc := he {x} hsub
  simp only [Finset.card_singleton,Nat.cast_one,min_eq_left hB,mul_one] at hc
  have hbound : cutCount G {x} (A\{x}) ≤ (A\{x}).card := by
    simpa only [cutCount,Finset.card_singleton,one_mul] using G.card_interedges_le_mul {x} (A\{x})
  have hboundR : (cutCount G {x} (A\{x}) : ℝ) ≤ (A\{x}).card := by exact_mod_cast hbound
  have heqR : ((A\{x}).card:ℝ)+1 = A.card := by exact_mod_cast hcard
  linarith

open _root_.Filter _root_.Asymptotics _root_.Real in
lemma cut_scale_ready : ∀ᶠ D : ℝ in atTop,
    1 ≤ D ∧ 2*D^(9/10:ℝ)*logb 2 (D^(51/50:ℝ)) ≤ D^(19/20:ℝ) := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have he := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/20)).const_mul_left
    ((51/25:ℝ)/log 2)).eventuallyLE
  filter_upwards [eventually_ge_atTop (1:ℝ),he] with D hD h
  have hDp : 0 < D := by linarith
  have hn : 0 ≤ (51/25:ℝ)/log 2 * log D := mul_nonneg (by positivity) (Real.log_nonneg hD)
  have hh : (51/25:ℝ)/log 2 * log D ≤ D^(1/20:ℝ) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_nonneg (Real.rpow_nonneg hDp.le _)] using h
  refine ⟨hD,?_⟩
  calc
    2*D^(9/10:ℝ)*logb 2 (D^(51/50:ℝ)) = D^(9/10:ℝ)*((51/25:ℝ)/log 2*log D) := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos hDp]
      simp only [Real.logb]
      ring
    _ ≤ D^(9/10:ℝ)*D^(1/20:ℝ) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = D^(19/20:ℝ) := by rw [← Real.rpow_add hDp]; norm_num

theorem scale_cut_extraction : ∃ Dcut : ℝ, ∀ D ≥ Dcut,
    ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (A : Finset V), A.Nonempty → SupportedOn G A →
      (A.card : ℝ) ≤ D^(51/50:ℝ) →
    ∃ (R : List (AssignedPiece V)) (H : SimpleGraph V),
      (∀ P ∈ R, P.vertices ⊆ A ∧ D^(9/10:ℝ) ≤ P.vertices.card ∧
        (P.vertices.card:ℝ) ≤ D^(51/50:ℝ) ∧ CutExpansionOn P.graph P.vertices (D^(9/10:ℝ))) ∧
      R.Pairwise (fun P Q => Disjoint P.vertices Q.vertices) ∧
      GraphPartition G (H :: R.map AssignedPiece.graph) ∧ SupportedOn H A ∧
      2*(edgeCount H : ℝ)/A.card ≤ D^(19/20:ℝ) := by
  classical
  obtain ⟨Dcut,hready⟩ := Filter.eventually_atTop.mp cut_scale_ready
  refine ⟨Dcut,?_⟩
  intro D hD V _ _ G A hA hG hhi
  obtain ⟨hD₁,hscale⟩ := hready D hD
  have hDp : 0 < D := by linarith
  have hAp : 0 < A.card := Finset.card_pos.mpr hA
  have hAr : (0:ℝ) < A.card := by exact_mod_cast hAp
  obtain ⟨R,H,hR,hd,hp,hs,hcost⟩ := cut_extraction G A hG (D^(9/10:ℝ)) (by positivity)
  refine ⟨R,H,?_,hd,hp,hs,?_⟩
  · intro P hP
    obtain ⟨hsub,hsize,hexp⟩ := hR P hP
    have hlo := expansion_order_lower hsize hexp
    have hle : (P.vertices.card:ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hsub
    exact ⟨hsub,by linarith,hle.trans hhi,hexp⟩
  · have hlog := (cast_log2_le_logb hAp).trans
      (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hAr hhi)
    have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ D^(9/10:ℝ)*(A.card:ℝ) by positivity)
    have hscaleA := mul_le_mul_of_nonneg_right hscale hAr.le
    apply (div_le_iff₀ hAr).mpr
    nlinarith

end ErdosGallai.Scale
end
end

/-! ### Upstream module `Combinatorics/CycleDecomposition/ScaleHierarchy.lean` -/

section
open _root_.Filter _root_.Asymptotics _root_.Real
open scoped _root_.Topology
noncomputable section
open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Finset
namespace ErdosGallai.Scale
open _root_.Finset _root_.SimpleGraph Classical _root_.Real
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

lemma edgeOccurrences_refine {I : Type cycleUniverse2} (L : List I)
    (g : I → SimpleGraph V) (f : I → List (SimpleGraph V))
    (h : ∀ i ∈ L, GraphPartition (g i) (f i)) (x y : V) :
    edgeOccurrences (L.flatMap f) x y = edgeOccurrences (L.map g) x y := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.flatMap_cons, edgeOccurrences_append, List.map_cons,
      edgeOccurrences_cons]
    rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]

lemma graphPartition_refine {I : Type cycleUniverse3} {G : SimpleGraph V}
    {C : List (SimpleGraph V)} {L : List I}
    {g : I → SimpleGraph V} {f : I → List (SimpleGraph V)}
    (hp : GraphPartition G (C ++ L.map g))
    (h : ∀ i ∈ L, GraphPartition (g i) (f i)) :
    GraphPartition G (C ++ L.flatMap f) := by
  intro x y
  simpa only [edgeOccurrences_append, edgeOccurrences_refine L g f h] using hp x y

theorem scale_split : ∃ Dsp : ℝ, ∀ D ≥ Dsp,
    ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (A : Finset V), A.Nonempty → SupportedOn G A →
      2*(edgeCount G : ℝ)/A.card ≤ D →
    ∃ (C : List (SimpleGraph V)) (L : List (AssignedPiece V))
      (R : AssignedPiece V → List (AssignedPiece V))
      (H : AssignedPiece V → SimpleGraph V),
      (∀ K ∈ C, IsCycleGraph K ∧ D^(101/100:ℝ) ≤ (edgeCount K : ℝ)) ∧
      (C.length : ℝ) ≤ A.card/(2*D^(1/100:ℝ)) ∧
      (∀ P ∈ L, P.vertices ⊆ A ∧ P.vertices.Nonempty ∧
        (P.vertices.card : ℝ) ≤ D^(51/50:ℝ)) ∧
      (∀ x ∈ A, ∃ P ∈ L, x ∈ P.vertices) ∧
      (L.map (fun P => (P.vertices.card : ℝ))).sum ≤ (1+2/logb 2 D)*A.card ∧
      (∀ P ∈ L,
        (∀ Q ∈ R P, Q.vertices ⊆ P.vertices ∧
          D^(9/10:ℝ) ≤ Q.vertices.card ∧
          (Q.vertices.card:ℝ) ≤ D^(51/50:ℝ) ∧
          CutExpansionOn Q.graph Q.vertices (D^(9/10:ℝ))) ∧
        (R P).Pairwise (fun Q T => Disjoint Q.vertices T.vertices) ∧
        GraphPartition P.graph (H P :: (R P).map AssignedPiece.graph) ∧
        SupportedOn (H P) P.vertices ∧
        2*(edgeCount (H P) : ℝ)/P.vertices.card ≤ D^(19/20:ℝ)) ∧
      GraphPartition G (C ++ L.flatMap (fun P => H P :: (R P).map AssignedPiece.graph)) := by
  classical
  obtain ⟨D₁,h₁⟩ := scale_boxes.{u}
  obtain ⟨D₂,h₂⟩ := scale_cut_extraction.{u}
  refine ⟨max D₁ D₂, ?_⟩
  intro D hD V _ _ G A hA hs hd
  obtain ⟨C,L,hC,hCN,hL,hcover,hp,hcost⟩ :=
    h₁ D ((le_max_left _ _).trans hD) V G A hA hs hd
  have hres : ∀ P : AssignedPiece V,
      ∃ (R : List (AssignedPiece V)) (H : SimpleGraph V), P ∈ L →
        (∀ Q ∈ R, Q.vertices ⊆ P.vertices ∧
          D^(9/10:ℝ) ≤ Q.vertices.card ∧
          (Q.vertices.card:ℝ) ≤ D^(51/50:ℝ) ∧
          CutExpansionOn Q.graph Q.vertices (D^(9/10:ℝ))) ∧
        R.Pairwise (fun Q T => Disjoint Q.vertices T.vertices) ∧
        GraphPartition P.graph (H :: R.map AssignedPiece.graph) ∧
        SupportedOn H P.vertices ∧
        2*(edgeCount H : ℝ)/P.vertices.card ≤ D^(19/20:ℝ) := by
    intro P
    by_cases hP : P ∈ L
    · obtain ⟨R,H,hgood⟩ := h₂ D ((le_max_right _ _).trans hD) V
        P.graph P.vertices (hL P hP).2.1 P.supported (hL P hP).2.2
      exact ⟨R,H,fun _ => hgood⟩
    · exact ⟨[],⊥,fun hp => False.elim (hP hp)⟩
  choose R H hR using hres
  refine ⟨C,L,R,H,hC,hCN,hL,hcover,hcost,hR,?_⟩
  exact graphPartition_refine hp (fun P hP => (hR P hP).2.2.1)

end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
def scaleTheta : ℝ := 19/20
def inductionScale (n : ℝ) (j : ℕ) : ℝ := n ^ (scaleTheta ^ j)

lemma scaleTheta_pos : 0 < scaleTheta := by norm_num [scaleTheta]
lemma scaleTheta_lt_one : scaleTheta < 1 := by norm_num [scaleTheta]

lemma inductionScale_zero (n : ℝ) : inductionScale n 0 = n := by
  simp [inductionScale]

lemma inductionScale_pos (n : ℝ) (hn : 0 < n) (j : ℕ) :
    0 < inductionScale n j := Real.rpow_pos_of_pos hn _

lemma inductionScale_succ (n : ℝ) (hn : 0 ≤ n) (j : ℕ) :
    inductionScale n (j+1) = (inductionScale n j) ^ scaleTheta := by
  simp only [inductionScale, pow_succ, Real.rpow_mul hn]

lemma inductionScale_gt_one (n : ℝ) (hn : 1 < n) (j : ℕ) :
    1 < inductionScale n j := by
  simpa [inductionScale] using Real.rpow_lt_rpow_of_exponent_lt hn
    (pow_pos scaleTheta_pos j)

lemma inductionScale_le (n : ℝ) (hn : 1 ≤ n) (j : ℕ) :
    inductionScale n j ≤ n := by
  have hp : scaleTheta ^ j ≤ 1 := pow_le_one₀ scaleTheta_pos.le scaleTheta_lt_one.le
  simpa [inductionScale] using Real.rpow_le_rpow_of_exponent_le hn hp

lemma inductionScale_log (n : ℝ) (hn : 0 < n) (j : ℕ) :
    logb 2 (inductionScale n j) = scaleTheta ^ j * logb 2 n := by
  exact Real.logb_rpow_eq_mul_logb_of_pos hn

lemma inductionScale_log_pos (n : ℝ) (hn : 1 < n) (j : ℕ) :
    0 < logb 2 (inductionScale n j) := by
  exact Real.logb_pos (by norm_num) (inductionScale_gt_one n hn j)

lemma inductionScale_log_succ (n : ℝ) (hn : 0 < n) (j : ℕ) :
    logb 2 (inductionScale n (j+1)) = scaleTheta * logb 2 (inductionScale n j) := by
  rw [inductionScale_log n hn, inductionScale_log n hn, pow_succ]
  ring

lemma inductionScale_add (n : ℝ) (hn : 0 ≤ n) (i K : ℕ) :
    inductionScale n (i+K) = (inductionScale n i) ^ (scaleTheta ^ K) := by
  simp only [inductionScale, pow_add, Real.rpow_mul hn]

lemma inductionScale_window : (51/50 : ℝ) * scaleTheta ^ 200 < 1/1000 ∧
    scaleTheta ^ 201 < 1/1000 := by
  norm_num [scaleTheta]

lemma inductionScale_tendsto (n : ℝ) (hn : 0 < n) :
    Tendsto (inductionScale n) atTop (𝓝 1) := by
  have ht := (Real.continuous_const_rpow (ne_of_gt hn)).tendsto 0
  change Tendsto (fun j : ℕ => n ^ (scaleTheta ^ j)) atTop (𝓝 1)
  simpa only [Function.comp_def, Real.rpow_zero] using
    ht.comp (tendsto_pow_atTop_nhds_zero_of_lt_one scaleTheta_pos.le scaleTheta_lt_one)

theorem inductionScale_first_cutoff (n Dstar : ℝ) (hD : 1 < Dstar) (hn : Dstar ≤ n) :
    ∃ m : ℕ, 0 < m ∧ inductionScale n m < Dstar ∧
      ∀ j < m, Dstar ≤ inductionScale n j := by
  have hn0 : 0 < n := lt_trans (by norm_num) (hD.trans_le hn)
  have he : ∀ᶠ j in atTop, inductionScale n j < Dstar :=
    (inductionScale_tendsto n hn0).eventually (gt_mem_nhds hD)
  have hex : ∃ j, inductionScale n j < Dstar := he.exists
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · by_contra hm
    have hz : Nat.find hex = 0 := by omega
    have := Nat.find_spec hex
    rw [hz, inductionScale_zero] at this
    linarith
  · intro j hj
    exact le_of_not_gt (Nat.find_min hex hj)

theorem scale_reciprocal_log_sum (n : ℝ) (hn : 1 < n) (j : ℕ) :
    (∑ l ∈ Finset.range (j+1), 1 / logb 2 (inductionScale n l)) ≤
      20 / logb 2 (inductionScale n j) := by
  induction j with
  | zero =>
    simp only [zero_add, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    exact div_le_div_of_nonneg_right (by norm_num) (inductionScale_log_pos n hn 0).le
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have hb : (∑ x ∈ range (j + 1), 1 / logb 2 (inductionScale n x)) +
        1 / logb 2 (inductionScale n (j+1)) ≤
        20 / logb 2 (inductionScale n j) + 1 / logb 2 (inductionScale n (j+1)) := by
      linarith [ih]
    apply hb.trans_eq
    rw [inductionScale_log_succ n (by linarith)]
    have hz : logb 2 (inductionScale n j) ≠ 0 := ne_of_gt (inductionScale_log_pos n hn j)
    dsimp [scaleTheta]
    field_simp
    ; ring

lemma exp_le_one_add_twice {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1/2) :
    exp x ≤ 1+2*x := by
  apply (Real.exp_bound_div_one_sub_of_interval hx (by linarith)).trans
  apply (div_le_iff₀ (by linarith : 0 < 1-x)).mpr
  nlinarith

theorem scale_overlap_product (n C₀ : ℝ) (hn : 1 < n) (hC : 0 ≤ C₀) (j : ℕ)
    (hcut : 40*C₀ ≤ logb 2 (inductionScale n j)) :
    (∏ l ∈ Finset.range (j+1), (1 + C₀ / logb 2 (inductionScale n l))) ≤
      1 + 40*C₀ / logb 2 (inductionScale n j) := by
  have hL := inductionScale_log_pos n hn j
  have hsum : (∑ l ∈ Finset.range (j+1), C₀ / logb 2 (inductionScale n l)) ≤
      20*C₀ / logb 2 (inductionScale n j) := by
    have hh := mul_le_mul_of_nonneg_left (scale_reciprocal_log_sum n hn j) hC
    calc
      _ ≤ C₀ * (20 / logb 2 (inductionScale n j)) := by
        simpa only [Finset.mul_sum, mul_one_div] using hh
      _ = _ := by ring
  calc
    _ ≤ ∏ l ∈ Finset.range (j+1), exp (C₀ / logb 2 (inductionScale n l)) := by
      apply Finset.prod_le_prod₀
      · intro l hl
        have := div_nonneg hC (inductionScale_log_pos n hn l).le
        linarith
      · intro l hl
        simpa [add_comm] using Real.add_one_le_exp (C₀ / logb 2 (inductionScale n l))
    _ = exp (∑ l ∈ Finset.range (j+1), C₀ / logb 2 (inductionScale n l)) :=
      (Real.exp_sum _ _).symm
    _ ≤ exp (20*C₀ / logb 2 (inductionScale n j)) := Real.exp_le_exp.mpr hsum
    _ ≤ 1 + 2*(20*C₀ / logb 2 (inductionScale n j)) := by
      apply exp_le_one_add_twice (div_nonneg (by positivity) hL.le)
      apply (div_le_iff₀ hL).mpr
      linarith
    _ = _ := by ring

theorem scale_prefix_cycle_cost (n : ℝ) (hn : 1 < n) (j : ℕ) (A : ℕ → ℝ)
    (hA : ∀ l ∈ Finset.range (j+1), A l ≤ 2*n)
    (hscale : ∀ l ∈ Finset.range (j+1),
      1 / (inductionScale n l) ^ (1/100 : ℝ) ≤ 1 / logb 2 (inductionScale n l)) :
    (∑ l ∈ Finset.range (j+1), A l / (2*(inductionScale n l) ^ (1/100 : ℝ))) ≤
      20*n / logb 2 (inductionScale n j) := by
  have hn0 : 0 < n := by linarith
  calc
    _ ≤ ∑ l ∈ Finset.range (j+1), n * (1 / logb 2 (inductionScale n l)) := by
      apply Finset.sum_le_sum
      intro l hl
      have hp : 0 < (inductionScale n l) ^ (1/100 : ℝ) :=
        Real.rpow_pos_of_pos (inductionScale_pos n hn0 l) _
      calc
        _ ≤ 2*n / (2*(inductionScale n l) ^ (1/100 : ℝ)) :=
          div_le_div_of_nonneg_right (hA l hl) (by positivity)
        _ = n * (1 / (inductionScale n l) ^ (1/100 : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hscale l hl) hn0.le
    _ = n * (∑ l ∈ Finset.range (j+1), 1 / logb 2 (inductionScale n l)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ n * (20 / logb 2 (inductionScale n j)) :=
      mul_le_mul_of_nonneg_left (scale_reciprocal_log_sum n hn j) hn0.le
    _ = _ := by ring

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

structure StageSplit (P : AssignedPiece V) where
  cycles : List (SimpleGraph V)
  boxes : List (AssignedPiece V)
  pieces : AssignedPiece V → List (AssignedPiece V)
  remainder : AssignedPiece V → SimpleGraph V
  cycles_good : ∀ K ∈ cycles, IsCycleGraph K
  box_subset : ∀ B ∈ boxes, B.vertices ⊆ P.vertices
  box_nonempty : P.vertices.Nonempty → ∀ B ∈ boxes, B.vertices.Nonempty
  box_cover : ∀ v ∈ P.vertices, ∃ B ∈ boxes, v ∈ B.vertices
  piece_subset : ∀ B ∈ boxes, ∀ R ∈ pieces B, R.vertices ⊆ B.vertices
  piece_disjoint : ∀ B ∈ boxes, (pieces B).Pairwise fun R S => Disjoint R.vertices S.vertices
  remainder_supported : ∀ B ∈ boxes, SupportedOn (remainder B) B.vertices
  box_partition : ∀ B ∈ boxes, GraphPartition B.graph (remainder B :: (pieces B).map AssignedPiece.graph)
  partition : GraphPartition P.graph (cycles ++ boxes.map AssignedPiece.graph)

def StageSplit.Bounded {P : AssignedPiece V} (s : StageSplit P) (D : ℝ) : Prop :=
  (s.cycles.length:ℝ) ≤ P.vertices.card / (2*D^(1/100:ℝ)) ∧
  (s.boxes.map (fun B => (B.vertices.card:ℝ))).sum ≤ (1+2/logb 2 D)*P.vertices.card ∧
  (∀ B ∈ s.boxes, (B.vertices.card:ℝ) ≤ D^(51/50:ℝ)) ∧
  (∀ B ∈ s.boxes, ∀ R ∈ s.pieces B,
    D^(9/10:ℝ) ≤ (R.vertices.card:ℝ) ∧ (R.vertices.card:ℝ) ≤ D^(51/50:ℝ) ∧
    CutExpansionOn R.graph R.vertices (D^(9/10:ℝ))) ∧
  (∀ B ∈ s.boxes, 2*(edgeCount (s.remainder B):ℝ)/B.vertices.card ≤ D^(19/20:ℝ))

def StageSplit.trivial (P : AssignedPiece V) : StageSplit P where
  cycles := []
  boxes := [P]
  pieces := fun _ => []
  remainder := AssignedPiece.graph
  cycles_good := by simp
  box_subset := by simp
  box_nonempty := by simp
  box_cover := by intro v hv; exact ⟨P,by simp,hv⟩
  piece_subset := by simp
  piece_disjoint := by simp
  remainder_supported := fun B _ => B.supported
  box_partition := by intro B _ x y; simp
  partition := by intro x y; simp

theorem scale_splitter : ∃ Dsp : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V],
    ∃ split : ∀ (_D : ℝ) (P : AssignedPiece V), StageSplit P,
      ∀ D ≥ Dsp, ∀ P, P.vertices.Nonempty →
        2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ D → (split D P).Bounded D := by
  obtain ⟨Dsp,hsp⟩ := scale_split
  refine ⟨Dsp,?_⟩
  intro V _ _
  have hex (D : ℝ) (P : AssignedPiece V) : ∃ s : StageSplit P,
      Dsp ≤ D → P.vertices.Nonempty → 2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ D → s.Bounded D := by
    by_cases h : Dsp ≤ D ∧ P.vertices.Nonempty ∧ 2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ D
    · obtain ⟨C,L,R,H,hC,hCl,hL,hcover,horder,hR,hpart⟩ :=
        hsp D h.1 V P.graph P.vertices h.2.1 P.supported h.2.2
      have hpart' : GraphPartition P.graph (C ++ L.map AssignedPiece.graph) := by
        intro x y
        rw [edgeOccurrences_append, ← edgeOccurrences_refine L AssignedPiece.graph
          (fun B => H B :: (R B).map AssignedPiece.graph) (fun B hB => (hR B hB).2.2.1)]
        simpa only [edgeOccurrences_append] using hpart x y
      let s : StageSplit P := {
        cycles := C, boxes := L, pieces := R, remainder := H
        cycles_good := fun K hK => (hC K hK).1
        box_subset := fun B hB => (hL B hB).1
        box_nonempty := fun _ B hB => (hL B hB).2.1
        box_cover := hcover
        piece_subset := fun B hB Q hQ => (hR B hB).1 Q hQ |>.1
        piece_disjoint := fun B hB => (hR B hB).2.1
        remainder_supported := fun B hB => (hR B hB).2.2.2.1
        box_partition := fun B hB => (hR B hB).2.2.1
        partition := hpart' }
      refine ⟨s,fun _ _ _ => ⟨hCl,horder,fun B hB => (hL B hB).2.2,?_,?_⟩⟩
      · exact fun B hB Q hQ => (hR B hB).1 Q hQ |>.2
      · exact fun B hB => (hR B hB).2.2.2.2
    · exact ⟨StageSplit.trivial P,fun hD hP hdeg => False.elim (h ⟨hD,hP,hdeg⟩)⟩
  choose s hs using hex
  exact ⟨s,fun D hD P hP hdeg => hs D P hD hP hdeg⟩

def StageSplit.children {P : AssignedPiece V} (s : StageSplit P) : List (AssignedPiece V) :=
  s.boxes.pmap (fun B hB => ⟨B.vertices,s.remainder B,s.remainder_supported B hB⟩) (fun _ h => h)

lemma StageSplit.mem_children {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : AssignedPiece V} (s : StageSplit P) (Q : AssignedPiece V) :
    Q ∈ s.children ↔ ∃ B ∈ s.boxes, Q.vertices = B.vertices ∧ Q.graph = s.remainder B := by
  simp only [StageSplit.children, List.mem_pmap]
  constructor
  · rintro ⟨B,hB,rfl⟩; exact ⟨B,hB,rfl,rfl⟩
  · rintro ⟨B,hB,hv,hg⟩
    refine ⟨B,hB,?_⟩
    cases Q; cases B; simp_all

lemma StageSplit.children_map {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : AssignedPiece V} (s : StageSplit P)
    {α : Type cycleUniverse4} (f : Finset V → SimpleGraph V → α) :
    s.children.map (fun Q => f Q.vertices Q.graph) =
      s.boxes.map (fun B => f B.vertices (s.remainder B)) := by
  unfold StageSplit.children
  rw [List.map_pmap]
  change List.pmap (fun B (_ : B ∈ s.boxes) => f B.vertices (s.remainder B)) s.boxes _ = _
  exact List.pmap_eq_map (fun B (h : B ∈ s.boxes) => h)

lemma list_disjoint_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L : List (Finset V)) (A : Finset V)
    (hd : L.Pairwise Disjoint) (hA : ∀ B ∈ L, B ⊆ A) :
    (L.map Finset.card).sum ≤ A.card := by
  induction L generalizing A with
  | nil => simp
  | cons B L ih =>
    obtain ⟨hBL,hd⟩ := List.pairwise_cons.mp hd
    have hBA := hA B (by simp)
    have hLA : ∀ C ∈ L, C ⊆ A \ B := by
      intro C hC v hv
      exact Finset.mem_sdiff.mpr ⟨hA C (by simp [hC]) hv,
        fun hb => Finset.disjoint_left.mp (hBL C hC) hb hv⟩
    have hh := ih (A \ B) hd hLA
    have hc := Finset.card_sdiff_of_subset hBA
    have hBAcard := Finset.card_le_card hBA
    simp only [List.map_cons,List.sum_cons]
    omega

def vertexMass (L : List (AssignedPiece V)) : ℝ :=
  (L.map (fun P => (P.vertices.card:ℝ))).sum

lemma vertexMass_nonneg {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L : List (AssignedPiece V)) : 0 ≤ vertexMass L :=
  List.sum_nonneg (fun x hx => by obtain ⟨P,_,rfl⟩ := List.mem_map.mp hx; positivity)

@[simp] lemma vertexMass_nil {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] : vertexMass ([] : List (AssignedPiece V)) = 0 := rfl
@[simp] lemma vertexMass_cons {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : AssignedPiece V) (L) :
    vertexMass (P::L) = P.vertices.card + vertexMass L := rfl
@[simp] lemma vertexMass_append {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L M : List (AssignedPiece V)) :
    vertexMass (L++M) = vertexMass L + vertexMass M := by simp [vertexMass]
lemma vertexMass_flatMap {I : Type cycleUniverse5} (L : List I) (f : I → List (AssignedPiece V)) :
    vertexMass (L.flatMap f) = (L.map (fun i => vertexMass (f i))).sum := by
  induction L with
  | nil => simp
  | cons i L ih => simp [ih]

lemma StageSplit.children_mass {P : AssignedPiece V} (s : StageSplit P) :
    vertexMass s.children = vertexMass s.boxes := by
  unfold vertexMass
  rw [s.children_map (fun A _ => (A.card:ℝ))]

lemma StageSplit.pieces_mass {P : AssignedPiece V} (s : StageSplit P) {B : AssignedPiece V}
    (hB : B ∈ s.boxes) : vertexMass (s.pieces B) ≤ B.vertices.card := by
  have hh := list_disjoint_card_le ((s.pieces B).map AssignedPiece.vertices) B.vertices
    (List.pairwise_map.mpr (s.piece_disjoint B hB)) (by
      intro A hA; obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hA
      exact s.piece_subset B hB Q hQ)
  simpa [vertexMass,List.map_map,Function.comp_def] using (Nat.cast_le.mpr hh : (_:ℝ) ≤ _)

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

abbrev SplitSystem (V : Type) [Fintype V] [DecidableEq V] :=
  ℕ → (P : AssignedPiece V) → StageSplit P

def nextLayer (s : SplitSystem V) (j : ℕ) (L : List (AssignedPiece V)) : List (AssignedPiece V) :=
  L.flatMap fun P => (s j P).children

def advance (s : SplitSystem V) (j : ℕ) : ℕ → List (AssignedPiece V) → List (AssignedPiece V)
  | 0,L => L
  | k+1,L => nextLayer s (j+k) (advance s j k L)

@[simp] lemma advance_zero (s : SplitSystem V) (j) (L) : advance s j 0 L = L := rfl
@[simp] lemma advance_succ (s : SplitSystem V) (j k) (L) :
    advance s j (k+1) L = nextLayer s (j+k) (advance s j k L) := rfl

lemma advance_add (s : SplitSystem V) (j k l) (L) :
    advance s j (k+l) L = advance s (j+k) l (advance s j k L) := by
  induction l with
  | zero => simp
  | succ l ih => simp only [Nat.add_succ,advance_succ,ih,Nat.add_assoc]

lemma advance_flatMap (s : SplitSystem V) (j k) {I : Type cycleUniverse6}
    (L : List I) (f : I → List (AssignedPiece V)) :
    advance s j k (L.flatMap f) = L.flatMap (fun i => advance s j k (f i)) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [advance_succ,nextLayer,ih,List.flatMap_assoc]

lemma nextLayer_mem (s : SplitSystem V) (j) (L) (Q : AssignedPiece V) :
    Q ∈ nextLayer s j L ↔ ∃ P ∈ L, ∃ B ∈ (s j P).boxes,
      Q.vertices = B.vertices ∧ Q.graph = (s j P).remainder B := by
  simp only [nextLayer,List.mem_flatMap,StageSplit.mem_children]

lemma advance_subset (s : SplitSystem V) (j k) (L) (A : Finset V)
    (hA : ∀ P ∈ L, P.vertices ⊆ A) :
    ∀ Q ∈ advance s j k L, Q.vertices ⊆ A := by
  induction k with
  | zero => exact hA
  | succ k ih =>
    intro Q hQ
    obtain ⟨P,hP,B,hB,hv,_⟩ := (nextLayer_mem s (j+k) _ Q).mp hQ
    rw [hv]
    exact ((s (j+k) P).box_subset B hB).trans (ih P hP)

lemma advance_nonempty (s : SplitSystem V) (j k) (L)
    (hL : ∀ P ∈ L, P.vertices.Nonempty) :
    ∀ Q ∈ advance s j k L, Q.vertices.Nonempty := by
  induction k with
  | zero => exact hL
  | succ k ih =>
    intro Q hQ
    obtain ⟨P,hP,B,hB,hv,_⟩ := (nextLayer_mem s (j+k) _ Q).mp hQ
    rw [hv]
    exact (s (j+k) P).box_nonempty (ih P hP) B hB

lemma advance_cover (s : SplitSystem V) (j k) (L) (P : AssignedPiece V) (hP : P ∈ L)
    (v : V) (hv : v ∈ P.vertices) : ∃ Q ∈ advance s j k L, v ∈ Q.vertices := by
  induction k with
  | zero => exact ⟨P,hP,hv⟩
  | succ k ih =>
    obtain ⟨Q,hQ,hvQ⟩ := ih
    obtain ⟨B,hB,hvB⟩ := (s (j+k) Q).box_cover v hvQ
    let T : AssignedPiece V := ⟨B.vertices,(s (j+k) Q).remainder B,
      (s (j+k) Q).remainder_supported B hB⟩
    exact ⟨T,(nextLayer_mem s (j+k) _ T).mpr ⟨Q,hQ,B,hB,rfl,rfl⟩,hvB⟩

lemma list_union_mem {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L : List (AssignedPiece V)) (v : V) :
    v ∈ L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅ ↔ ∃ P ∈ L, v ∈ P.vertices := by
  induction L with
  | nil => simp
  | cons P L ih =>
    simp only [List.foldr_cons,Finset.mem_union,ih,List.mem_cons]
    aesop

lemma list_union_card {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L : List (AssignedPiece V)) :
    ((L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅).card:ℝ) ≤ vertexMass L := by
  induction L with
  | nil => simp
  | cons P L ih =>
    simp only [List.foldr_cons,vertexMass_cons]
    have hc := Finset.card_union_le P.vertices (L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅)
    have hc' : ((P.vertices ∪ L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅).card:ℝ) ≤
        P.vertices.card + (L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅).card := by exact_mod_cast hc
    linarith

lemma list_cover_card_le (L : List (AssignedPiece V)) (A : Finset V)
    (hcover : ∀ v ∈ A, ∃ P ∈ L, v ∈ P.vertices) : (A.card:ℝ) ≤ vertexMass L := by
  have hsub : A ⊆ L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅ :=
    fun v hv => (list_union_mem L v).mpr (hcover v hv)
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (list_union_card L)

lemma advance_mass_lower (s : SplitSystem V) (j k) (P : AssignedPiece V) :
    (P.vertices.card:ℝ) ≤ vertexMass (advance s j k [P]) :=
  list_cover_card_le _ _ (fun v hv => advance_cover s j k [P] P (by simp) v hv)

lemma nextLayer_mass_bound (s : SplitSystem V) (j) (L : List (AssignedPiece V)) (D : ℝ)
    (hb : ∀ P ∈ L, (s j P).Bounded D) :
    vertexMass (nextLayer s j L) ≤ (1+2/logb 2 D)*vertexMass L := by
  induction L with
  | nil => simp [nextLayer]
  | cons P L ih =>
    have hP := (hb P (by simp)).2.1
    have hL := ih (fun Q hQ => hb Q (by simp [hQ]))
    simp only [nextLayer,List.flatMap_cons,vertexMass_append,StageSplit.children_mass,
      vertexMass_cons] at hL ⊢
    change vertexMass (s j P).boxes ≤ _ at hP
    nlinarith

lemma advance_valid (s : SplitSystem V) (n Dstar : ℝ) (hn : 0 ≤ n)
    (hs : ∀ l P, Dstar ≤ inductionScale n l → P.vertices.Nonempty →
      2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ inductionScale n l →
      (s l P).Bounded (inductionScale n l))
    (j k : ℕ) (L : List (AssignedPiece V))
    (hL : ∀ P ∈ L, P.vertices.Nonempty)
    (hdeg : ∀ P ∈ L, 2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ inductionScale n j)
    (hcut : ∀ l, j ≤ l → l < j+k → Dstar ≤ inductionScale n l) :
    ∀ P ∈ advance s j k L,
      2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ inductionScale n (j+k) := by
  induction k with
  | zero => simpa using hdeg
  | succ k ih =>
    intro Q hQ
    obtain ⟨P,hP,B,hB,hv,hg⟩ := (nextLayer_mem s (j+k) _ Q).mp hQ
    have hPdeg := ih (fun l hlj hl => hcut l hlj (by omega)) P hP
    have hb := hs (j+k) P (hcut (j+k) (by omega) (by omega))
      (advance_nonempty s j k L hL P hP) hPdeg
    rw [hv,hg,show j+(k+1) = (j+k)+1 by omega,inductionScale_succ n hn]
    exact hb.2.2.2.2 B hB

lemma advance_bounded (s : SplitSystem V) (n Dstar : ℝ) (hn : 0 ≤ n)
    (hs : ∀ l P, Dstar ≤ inductionScale n l → P.vertices.Nonempty →
      2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ inductionScale n l →
      (s l P).Bounded (inductionScale n l))
    (j k : ℕ) (L : List (AssignedPiece V))
    (hL : ∀ P ∈ L, P.vertices.Nonempty)
    (hdeg : ∀ P ∈ L, 2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ inductionScale n j)
    (hcut : ∀ l, j ≤ l → l ≤ j+k → Dstar ≤ inductionScale n l) :
    ∀ P ∈ advance s j k L, (s (j+k) P).Bounded (inductionScale n (j+k)) := by
  intro P hP
  exact hs (j+k) P (hcut _ (by omega) (by omega)) (advance_nonempty s j k L hL P hP)
    (advance_valid s n Dstar hn hs j k L hL hdeg (fun l hlj hl => hcut l hlj (by omega)) P hP)

lemma advance_mass_global_product (s : SplitSystem V) (n : ℝ) (hn : 1 < n)
    (j k : ℕ) (L : List (AssignedPiece V))
    (hb : ∀ l < k, ∀ P ∈ advance s j l L, (s (j+l) P).Bounded (inductionScale n (j+l))) :
    vertexMass (advance s j k L) ≤ vertexMass L *
      ∏ l ∈ Finset.range (j+k), (1+2/logb 2 (inductionScale n l)) := by
  have hfac (l) : 1 ≤ 1+2/logb 2 (inductionScale n l) := by
    have := div_nonneg (by norm_num : (0:ℝ) ≤ 2) (inductionScale_log_pos n hn l).le
    linarith
  induction k with
  | zero =>
    simp only [advance_zero,Nat.add_zero]
    exact le_mul_of_one_le_right (vertexMass_nonneg L) (Finset.one_le_prod₀ (fun l _ => hfac l))
  | succ k ih =>
    have hm := nextLayer_mass_bound s (j+k) (advance s j k L) (inductionScale n (j+k))
      (hb k (by omega))
    have hi := mul_le_mul_of_nonneg_left (ih (fun l hl => hb l (by omega))) ((hfac (j+k)).trans' (by norm_num : (0:ℝ) ≤ 1))
    rw [advance_succ,show j+(k+1) = (j+k)+1 by omega,Finset.prod_range_succ]
    calc
      _ ≤ (1+2/logb 2 (inductionScale n (j+k))) * vertexMass (advance s j k L) := hm
      _ ≤ _ := by nlinarith only [hi]

end
end ErdosGallai.Scale
end
end

/-! ### Upstream module `Combinatorics/CycleDecomposition/ScaleDecomposition.lean` -/

noncomputable section
namespace ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def graphUnion (L : List (SimpleGraph V)) : SimpleGraph V := L.foldr (· ⊔ ·) ⊥

@[simp] lemma graphUnion_nil {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] : graphUnion ([] : List (SimpleGraph V)) = ⊥ := rfl
@[simp] lemma graphUnion_cons {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (L) : graphUnion (G::L) = G ⊔ graphUnion L := rfl
lemma graphUnion_adj {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L : List (SimpleGraph V)) (x y : V) :
    (graphUnion L).Adj x y ↔ ∃ G ∈ L, G.Adj x y := by
  induction L with
  | nil => simp
  | cons G L ih => simp only [graphUnion_cons,SimpleGraph.sup_adj,ih,List.mem_cons]; aesop

lemma edgeOccurrences_pos (L : List (SimpleGraph V)) (x y : V) :
    0 < edgeOccurrences L x y ↔ (graphUnion L).Adj x y := by
  simp [edgeOccurrences,List.countP_pos_iff,graphUnion_adj]

lemma graphPartition_union {G : SimpleGraph V} {L : List (SimpleGraph V)}
    (h : GraphPartition G L) : graphUnion L = G := by
  ext x y
  rw [← edgeOccurrences_pos,h x y]
  split_ifs <;> simp_all

lemma graphPartition_of_le_one (L : List (SimpleGraph V))
    (h : ∀ x y, edgeOccurrences L x y ≤ 1) : GraphPartition (graphUnion L) L := by
  intro x y
  have hh := h x y
  rw [← edgeOccurrences_pos]
  split_ifs <;> omega

lemma edgeOccurrences_sublist {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {L M : List (SimpleGraph V)} (h : L.Sublist M) (x y : V) :
    edgeOccurrences L x y ≤ edgeOccurrences M x y := by
  exact List.Sublist.countP_le h

lemma graphPartition_sublist {G : SimpleGraph V} {L M : List (SimpleGraph V)}
    (hp : GraphPartition G M) (h : L.Sublist M) : GraphPartition (graphUnion L) L := by
  apply graphPartition_of_le_one
  intro x y
  have hh := edgeOccurrences_sublist h x y
  rw [hp x y] at hh
  split_ifs at hh <;> omega

lemma graphUnion_sublist {L M : List (SimpleGraph V)} (h : L.Sublist M) : graphUnion L ≤ graphUnion M := by
  intro x y hxy
  obtain ⟨G,hG,hxy⟩ := (graphUnion_adj _ _ _).mp hxy
  exact (graphUnion_adj _ _ _).mpr ⟨G,h.subset hG,hxy⟩

lemma graphUnion_append (L M : List (SimpleGraph V)) : graphUnion (L++M) = graphUnion L ⊔ graphUnion M := by
  ext x y
  simp only [graphUnion_adj,List.mem_append,SimpleGraph.sup_adj]
  aesop

lemma edgeCount_union_le (L : List (SimpleGraph V)) :
    edgeCount (graphUnion L) ≤ (L.map edgeCount).sum := by
  induction L with
  | nil => simp
  | cons G L ih =>
    simp only [graphUnion_cons,List.map_cons,List.sum_cons]
    exact (edgeCount_sup_le G (graphUnion L)).trans (Nat.add_le_add_left ih _)

def levelCycles (s : SplitSystem V) (j : ℕ) (L : List (AssignedPiece V)) : List (SimpleGraph V) :=
  L.flatMap fun P => (s j P).cycles

def levelPieces (s : SplitSystem V) (j : ℕ) (L : List (AssignedPiece V)) : List (AssignedPiece V) :=
  L.flatMap fun P => (s j P).boxes.flatMap (s j P).pieces

lemma StageSplit.ledger {P : AssignedPiece V} (s : StageSplit P) (x y : V) :
    edgeOccurrences (s.cycles ++ (s.boxes.flatMap s.pieces).map AssignedPiece.graph ++
      s.children.map AssignedPiece.graph) x y = if P.graph.Adj x y then 1 else 0 := by
  have h := s.partition x y
  rw [edgeOccurrences_append] at h
  rw [← edgeOccurrences_refine s.boxes AssignedPiece.graph
    (fun B => s.remainder B :: (s.pieces B).map AssignedPiece.graph) s.box_partition] at h
  have he : edgeOccurrences (s.boxes.flatMap (fun B => s.remainder B ::
      (s.pieces B).map AssignedPiece.graph)) x y =
      edgeOccurrences ((s.boxes.flatMap s.pieces).map AssignedPiece.graph) x y +
      edgeOccurrences (s.children.map AssignedPiece.graph) x y := by
    rw [s.children_map (fun _ G => G)]
    induction s.boxes with
    | nil => simp
    | cons B L ih =>
      simp only [List.flatMap_cons,List.map_append,List.map_cons,edgeOccurrences_append,
        edgeOccurrences_cons] at *
      omega
  rw [he] at h
  simpa only [edgeOccurrences_append,Nat.add_assoc] using h

lemma level_ledger (s : SplitSystem V) (j) (L : List (AssignedPiece V)) (x y : V) :
    edgeOccurrences (levelCycles s j L ++ (levelPieces s j L).map AssignedPiece.graph ++
      (nextLayer s j L).map AssignedPiece.graph) x y = edgeOccurrences (L.map AssignedPiece.graph) x y := by
  induction L with
  | nil => simp [levelCycles,levelPieces,nextLayer]
  | cons P L ih =>
    have hp := (s j P).ledger x y
    simp only [levelCycles,levelPieces,nextLayer,List.flatMap_cons,List.map_append,
      List.map_cons,edgeOccurrences_append,edgeOccurrences_cons] at ih hp ⊢
    omega

def pastCycles (s : SplitSystem V) (j : ℕ) : ℕ → List (AssignedPiece V) → List (SimpleGraph V)
  | 0,_ => []
  | k+1,L => pastCycles s j k L ++ levelCycles s (j+k) (advance s j k L)

def pastPieces (s : SplitSystem V) (j : ℕ) : ℕ → List (AssignedPiece V) → List (AssignedPiece V)
  | 0,_ => []
  | k+1,L => pastPieces s j k L ++ levelPieces s (j+k) (advance s j k L)

lemma past_ledger (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) (x y : V) :
    edgeOccurrences (pastCycles s j k L ++ (pastPieces s j k L).map AssignedPiece.graph ++
      (advance s j k L).map AssignedPiece.graph) x y = edgeOccurrences (L.map AssignedPiece.graph) x y := by
  induction k with
  | zero => simp [pastCycles,pastPieces]
  | succ k ih =>
    have h := level_ledger s (j+k) (advance s j k L) x y
    simp only [pastCycles,pastPieces,advance_succ,List.map_append,edgeOccurrences_append] at ih h ⊢
    omega

lemma past_partition (s : SplitSystem V) (j k) (P : AssignedPiece V) :
    GraphPartition P.graph (pastCycles s j k [P] ++ (pastPieces s j k [P]).map AssignedPiece.graph ++
      (advance s j k [P]).map AssignedPiece.graph) := by
  intro x y
  rw [past_ledger]
  simp

lemma levelCycles_good (s : SplitSystem V) (j) (L : List (AssignedPiece V)) :
    ∀ G ∈ levelCycles s j L, IsCycleGraph G := by
  intro G hG
  obtain ⟨P,_,hG⟩ := List.mem_flatMap.mp hG
  exact (s j P).cycles_good G hG

lemma pastCycles_good (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    ∀ G ∈ pastCycles s j k L, IsCycleGraph G := by
  induction k with
  | zero => simp [pastCycles]
  | succ k ih =>
    intro G hG
    rcases List.mem_append.mp hG with h | h
    · exact ih G h
    · exact levelCycles_good s (j+k) _ G h

lemma levelPieces_mass (s : SplitSystem V) (j) (L : List (AssignedPiece V)) :
    vertexMass (levelPieces s j L) ≤ vertexMass (nextLayer s j L) := by
  induction L with
  | nil => simp [levelPieces,nextLayer]
  | cons P L ih =>
    have hs : vertexMass ((s j P).boxes.flatMap (s j P).pieces) ≤ vertexMass (s j P).boxes := by
      rw [vertexMass_flatMap]
      unfold vertexMass
      exact List.sum_le_sum (fun B hB => (s j P).pieces_mass hB)
    simp only [levelPieces,nextLayer,List.flatMap_cons,vertexMass_append,
      StageSplit.children_mass] at ih ⊢
    linarith

lemma levelCycles_length (s : SplitSystem V) (j) (L : List (AssignedPiece V)) (D : ℝ)
    (hb : ∀ P ∈ L, (s j P).Bounded D) :
    ((levelCycles s j L).length:ℝ) ≤ vertexMass L / (2*D^(1/100:ℝ)) := by
  induction L with
  | nil => simp [levelCycles]
  | cons P L ih =>
    have hp := (hb P (by simp)).1
    have hl := ih (fun Q hQ => hb Q (by simp [hQ]))
    simp only [levelCycles,List.flatMap_cons,List.length_append,Nat.cast_add,vertexMass_cons]
    rw [add_div]
    exact add_le_add hp hl

lemma pastPieces_mass (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    vertexMass (pastPieces s j k L) = ∑ l ∈ Finset.range k,
      vertexMass (levelPieces s (j+l) (advance s j l L)) := by
  induction k with
  | zero => simp [pastPieces]
  | succ k ih => simp [pastPieces,ih,Finset.sum_range_succ]

lemma pastCycles_length (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    ((pastCycles s j k L).length:ℝ) = ∑ l ∈ Finset.range k,
      ((levelCycles s (j+l) (advance s j l L)).length:ℝ) := by
  induction k with
  | zero => simp [pastCycles]
  | succ k ih => simp [pastCycles,ih,Finset.sum_range_succ]

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale

def CycleOrSingleEdge {V : Type} (G : SimpleGraph V)
    (s : Set (Sym2 V)) : Prop :=
  (∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ s = p.edgeSet) ∨
  ∃ e ∈ G.edgeSet, s = {e}

def EdgeDecomposition {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ parts : Fin k → Set (Sym2 V),
    (∀ i, CycleOrSingleEdge G (parts i)) ∧
    Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
    (⋃ i, parts i) = G.edgeSet

noncomputable section
open _root_.SimpleGraph

lemma cycleOrSingleEdge_subset {V : Type} {G : SimpleGraph V}
    {s : Set (Sym2 V)} (hs : CycleOrSingleEdge G s) : s ⊆ G.edgeSet := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact p.edges_subset_edgeSet
  · simpa using he

lemma cycleOrSingleEdge_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) {s : Set (Sym2 V)}
    (hs : CycleOrSingleEdge G s) : CycleOrSingleEdge H (Sym2.map f '' s) := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact Or.inl ⟨f v,p.map f,hp.map hf,(p.edgeSet_map f).symm⟩
  · refine Or.inr ⟨Sym2.map f e, ?_, by simp⟩
    induction e using Sym2.ind with | _ x y =>
      exact f.map_adj he

lemma edgeDecomposition_of_indexed {V I : Type} [Fintype I] (G : SimpleGraph V)
    (parts : I → Set (Sym2 V)) (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hu : (⋃ i, parts i) = G.edgeSet) : EdgeDecomposition G (Fintype.card I) := by
  let e := Fintype.equivFin I
  refine ⟨fun j => parts (e.symm j), fun j => hp _, ?_, ?_⟩
  · intro i j hij
    exact hd (fun he => hij (e.symm.injective he))
  · ext x
    simp only [Set.mem_iUnion]
    rw [← hu]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨e i, by simpa using hi⟩

theorem edgeDecomposition_singleEdges {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (Nat.card G.edgeSet) := by
  classical
  let : Fintype G.edgeSet := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  apply edgeDecomposition_of_indexed G (fun e : G.edgeSet => {e.1})
  · intro e; exact Or.inr ⟨e.1,e.2,rfl⟩
  · intro e d hed
    exact Set.disjoint_singleton.mpr (fun h => hed (Subtype.ext h))
  · ext e; simp

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
open _root_.SimpleGraph _root_.Finset
attribute [local instance] Classical.propDecidable

def decompositionCost {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.find (show ∃ k, EdgeDecomposition G k from ⟨_,edgeDecomposition_singleEdges G⟩)

lemma decompositionCost_spec {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (decompositionCost G) := Nat.find_spec _

lemma decompositionCost_le {V : Type} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : EdgeDecomposition G k) : decompositionCost G ≤ k := Nat.find_min' _ h

lemma decompositionCost_singleEdges {V : Type} [Fintype V] (G : SimpleGraph V) :
    decompositionCost G ≤ Nat.card G.edgeSet := decompositionCost_le (edgeDecomposition_singleEdges G)

theorem edgeDecomposition_adjoin {V I J : Type} [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) (H : ∀ j, SimpleGraph (W j)) (f : ∀ j, H j →g G)
    (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet)
    (k : J → ℕ) (hD : ∀ j, EdgeDecomposition (H j) (k j)) :
    EdgeDecomposition G (Fintype.card I + ∑ j, k j) := by
  classical
  choose P hP hPd hPc using hD
  let R : (I ⊕ Σ j, Fin (k j)) → Set (Sym2 V) :=
    Sum.elim parts (fun z => Sym2.map (f z.1) '' P z.1 z.2)
  have hsub : ∀ j i, P j i ⊆ (H j).edgeSet := fun j i => cycleOrSingleEdge_subset (hP j i)
  have hRp : ∀ z, CycleOrSingleEdge G (R z) := by
    intro z
    rcases z with z | ⟨j,i⟩
    · exact hp z
    · exact cycleOrSingleEdge_map (f j) (hf j) (hP j i)
  have hRd : Pairwise fun z t => Disjoint (R z) (R t) := by
    intro z t hzt
    rcases z with z | ⟨j,i⟩ <;> rcases t with t | ⟨l,a⟩
    · exact hd (fun h => hzt (congrArg Sum.inl h))
    · exact ((hHP l z).mono_left (Set.image_mono (hsub l a))).symm
    · exact (hHP j t).mono_left (Set.image_mono (hsub j i))
    · by_cases hjl : j = l
      · subst l
        have hia : i ≠ a := fun h => hzt (by cases h; rfl)
        apply Set.disjoint_left.mpr
        rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩
        have hxy := Sym2.map.injective (hf j) (he.trans he'.symm)
        subst y
        exact Set.disjoint_left.mp (hPd j hia) hx hy
      · exact (hHH hjl).mono (Set.image_mono (hsub j i)) (Set.image_mono (hsub l a))
  have hRu : (⋃ z, R z) = G.edgeSet := by
    rw [← hu]
    ext e
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨z,hz⟩
      rcases z with z | ⟨j,i⟩
      · exact Or.inl ⟨z,hz⟩
      · obtain ⟨x,hx,he⟩ := hz
        exact Or.inr ⟨j,x,hsub j i hx,he⟩
    · rintro (⟨i,hi⟩ | ⟨j,x,hx,he⟩)
      · exact ⟨Sum.inl i,hi⟩
      · rw [← hPc j] at hx
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
        exact ⟨Sum.inr ⟨j,i⟩,x,hi,he⟩
  simpa only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin] using
    edgeDecomposition_of_indexed G R hRp hRd hRu

lemma decompositionCost_adjoin {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) [∀ j, Fintype (W j)] (H : ∀ j, SimpleGraph (W j))
    (f : ∀ j, H j →g G) (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) :=
  decompositionCost_le (edgeDecomposition_adjoin G parts hp hd W H f hf hHH hHP hu _
    (fun j => decompositionCost_spec (H j)))

end
end ErdosGallai.Scale
namespace ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable

end
end ErdosGallai.Scale
namespace ErdosGallai.Scale
noncomputable section
open _root_.SimpleGraph _root_.Finset
attribute [local instance] Classical.propDecidable

lemma decompositionCost_adjoin_same {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (H : J → SimpleGraph V) (hHG : ∀ j, H j ≤ G)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hHP : ∀ j i, Disjoint (H j).edgeSet (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) := by
  let f : ∀ j, H j →g G := fun j => ⟨id,fun h => hHG j h⟩
  have he (j) : Sym2.map (f j) '' (H j).edgeSet = (H j).edgeSet := by
    have hf : (f j : V → V) = id := rfl
    rw [hf, Sym2.map_id, Set.image_id]
  apply decompositionCost_adjoin G parts hp hd (fun _ => V) H f (fun _ => Function.injective_id)
  · simpa only [he] using hHH
  · simpa only [he] using hHP
  · simpa only [he] using hu

lemma decompositionCost_assemble_same {V J : Type} [Fintype V] [Fintype J]
    (G : SimpleGraph V) (H : J → SimpleGraph V) (hHG : ∀ j, H j ≤ G)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hu : (⋃ j, (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ ∑ j, decompositionCost (H j) := by
  simpa using decompositionCost_adjoin_same (I := Empty) G Empty.elim (fun i => nomatch i)
    (by intro i; exact i.elim) H hHG hHH (fun _ i => nomatch i) (by simpa using hu)

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma list_pairwise_get {A : Type cycleUniverse1} {R : A → A → Prop} {L : List A}
    (h : L.Pairwise R) (hs : (∀ ⦃left right⦄, R left right → R right left)) : Pairwise fun i j : Fin L.length => R (L.get i) (L.get j) := by
  intro i j hij
  rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun he => hij (Fin.ext he)) with hlt | hgt
  · exact List.pairwise_iff_getElem.mp h i.val j.val i.isLt j.isLt hlt
  · exact hs (List.pairwise_iff_getElem.mp h j.val i.val j.isLt i.isLt hgt)

lemma list_sum_get {A : Type cycleUniverse2} {M : Type cycleUniverse3} [AddCommMonoid M] (L : List A) (f : A → M) :
    (∑ i : Fin L.length, f (L.get i)) = (L.map f).sum := by
  rw [← List.sum_ofFn]
  calc
    _ = (List.map f (List.ofFn L.get)).sum := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [List.ofFn_get]

lemma graphPartition_pairwise {G : SimpleGraph V} {L : List (SimpleGraph V)}
    (h : GraphPartition G L) : L.Pairwise fun H K => Disjoint H.edgeSet K.edgeSet := by
  induction L generalizing G with
  | nil => simp
  | cons H L ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih (graphPartition_sublist h (List.sublist_cons_self _ _))⟩
    intro K hK
    apply Set.disjoint_left.mpr
    intro e he he'
    induction e using Sym2.ind with
    | _ x y =>
      have hc := h x y
      have hp : 0 < edgeOccurrences L x y := by
        rw [edgeOccurrences_pos,graphUnion_adj]
        exact ⟨K,hK,he'⟩
      have hxy : H.Adj x y := he
      simp only [edgeOccurrences_cons,hxy,ite_true] at hc
      split_ifs at hc <;> omega

lemma graphUnion_edges (L : List (SimpleGraph V)) :
    (⋃ i : Fin L.length, (L.get i).edgeSet) = (graphUnion L).edgeSet := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Set.mem_iUnion,SimpleGraph.mem_edgeSet]

    rw [graphUnion_adj]
    constructor
    · rintro ⟨i,h⟩; exact ⟨_,L.get_mem i,h⟩
    · rintro ⟨H,hH,h⟩
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
      exact ⟨i,h⟩

lemma decompositionCost_partition {G : SimpleGraph V} {L : List (SimpleGraph V)}
    (h : GraphPartition G L) : decompositionCost G ≤ (L.map decompositionCost).sum := by
  rw [← list_sum_get L decompositionCost]
  apply decompositionCost_assemble_same G (fun i : Fin L.length => L.get i)
  · intro i; exact partition_member_le h (L.get_mem i)
  · exact list_pairwise_get (graphPartition_pairwise h) (fun _ _ h => h.symm)
  · rw [graphUnion_edges,graphPartition_union h]

lemma decompositionCost_cycle {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {G : SimpleGraph V} (h : IsCycleGraph G) :
    decompositionCost G ≤ 1 := by
  apply decompositionCost_le
  have hp : CycleOrSingleEdge G G.edgeSet := by
    obtain ⟨a,p,hp,he⟩ := h
    exact Or.inl ⟨a,p,hp,he⟩
  refine ⟨fun _ => G.edgeSet,fun _ => hp,?_,?_⟩
  · intro i j hij; exact False.elim (hij (Subsingleton.elim i j))
  · ext e
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨(0 : Fin 1),h⟩⟩

lemma decompositionCost_edgeCount {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) : decompositionCost G ≤ edgeCount G := by
  have h := decompositionCost_singleEdges G
  rw [Nat.card_eq_fintype_card,SimpleGraph.card_edgeSet] at h
  exact h

lemma decompositionCost_partition_real {G : SimpleGraph V} {L : List (SimpleGraph V)}
    (h : GraphPartition G L) : (decompositionCost G:ℝ) ≤
      (L.map (fun H => (decompositionCost H:ℝ))).sum := by
  have hh : (decompositionCost G:ℝ) ≤ ((L.map decompositionCost).sum:ℕ) :=
    Nat.cast_le.mpr (decompositionCost_partition h)
  simpa [List.map_map,Function.comp_def] using hh

lemma decompositionCost_cycles (L : List (SimpleGraph V))
    (h : ∀ G ∈ L, IsCycleGraph G) :
    (L.map (fun H => (decompositionCost H:ℝ))).sum ≤ L.length := by
  calc
    _ ≤ (L.map (fun _ => (1:ℝ))).sum := List.sum_le_sum (fun G hG => by exact_mod_cast decompositionCost_cycle (h G hG))
    _ = _ := by simp

end
end ErdosGallai.Scale

end
/-! ### Upstream module `Combinatorics/CycleDecomposition/BatchIndexing.lean` -/

noncomputable section
open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Finset
namespace ErdosGallai.Indexing
noncomputable section
variable {I : Type cycleUniverse1} [DecidableEq I]

def batchWeight (w : I → ℕ) (b : Finset I) : ℝ := ∑ i ∈ b, (w i : ℝ)

lemma batchWeight_nonneg {I : Type cycleUniverse2} [_contextInstance1 : DecidableEq I] (w : I → ℕ) (b : Finset I) : 0 ≤ batchWeight w b := by
  exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

lemma indexed_batch_construction (w : I → ℕ) (A : Finset I) (B : ℝ) (hB : 0 < B)
    (hw : ∀ i ∈ A, (w i : ℝ) ≤ B/2) :
    ∃ P : List (Finset I),
      P.Pairwise Disjoint ∧
      (∀ i, i ∈ A ↔ ∃ b ∈ P, i ∈ b) ∧
      (∀ b ∈ P, b.Nonempty ∧ batchWeight w b ≤ B) ∧
      (∀ b ∈ P.tail, B/2 < batchWeight w b) ∧
      (P.map (batchWeight w)).sum = batchWeight w A := by
  induction A using Finset.induction_on with
  | empty =>
    refine ⟨[], by simp, ?_, by simp, by simp, ?_⟩
    · simp
    · simp [batchWeight]
  | @insert a A ha ih =>
    obtain ⟨P, hdisj, hcover, hbins, hheavy, hmass⟩ := ih (fun i hi => hw i (by simp [hi]))
    have hwa := hw a (by simp)
    have haP : ∀ b ∈ P, a ∉ b := by
      intro b hb hab
      exact ha ((hcover a).mpr ⟨b,hb,hab⟩)
    cases P with
    | nil =>
      have hAz : A = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        simpa using (hcover i).mp hi
      subst A
      refine ⟨[{a}], by simp, ?_, ?_, by simp, ?_⟩
      · intro i; simp
      · intro b hb
        simp only [List.mem_singleton] at hb
        subst b
        exact ⟨by simp, by simp [batchWeight]; linarith⟩
      · simp
    | cons b bs =>
      have hab : a ∉ b := haP b (by simp)
      obtain ⟨hbne,hbB⟩ := hbins b (by simp)
      by_cases hlight : batchWeight w b ≤ B/2
      · refine ⟨insert a b :: bs, ?_, ?_, ?_, ?_, ?_⟩
        · rw [List.pairwise_cons]
          refine ⟨?_, (List.pairwise_cons.mp hdisj).2⟩
          intro d hd
          exact Finset.disjoint_insert_left.mpr ⟨haP d (by simp [hd]),
            (List.pairwise_cons.mp hdisj).1 d hd⟩
        · intro i
          constructor
          · intro hia
            rcases Finset.mem_insert.mp hia with hia | hi
            · exact ⟨insert a b, by simp, by simp [hia]⟩
            · obtain ⟨d,hd,hid⟩ := (hcover i).mp hi
              rcases List.mem_cons.mp hd with hd | hd
              · subst d
                exact ⟨insert a b, by simp, Finset.mem_insert_of_mem hid⟩
              · exact ⟨d, by simp [hd], hid⟩
          · rintro ⟨d,hd,hid⟩
            rcases List.mem_cons.mp hd with rfl | hd
            · rcases Finset.mem_insert.mp hid with rfl | hib
              · simp
              · exact Finset.mem_insert_of_mem ((hcover i).mpr ⟨b, by simp, hib⟩)
            · exact Finset.mem_insert_of_mem ((hcover i).mpr ⟨d, by simp [hd], hid⟩)
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · refine ⟨by simp, ?_⟩
            simp only [batchWeight, Finset.sum_insert hab]
            change (w a : ℝ) + batchWeight w b ≤ B
            linarith
          · exact hbins d (by simp [hd])
        · simpa using hheavy
        · simp only [List.map_cons, List.sum_cons] at hmass ⊢
          rw [show batchWeight w (insert a b) = (w a:ℝ)+batchWeight w b by
            simp [batchWeight, hab], show batchWeight w (insert a A) = (w a:ℝ)+batchWeight w A by
            simp [batchWeight, ha]]
          linarith
      · refine ⟨{a} :: b :: bs, ?_, ?_, ?_, ?_, ?_⟩
        · rw [List.pairwise_cons]
          exact ⟨fun d hd => Finset.disjoint_singleton_left.mpr (haP d hd), hdisj⟩
        · intro i
          constructor
          · intro hi
            rcases Finset.mem_insert.mp hi with hia | hi
            · exact ⟨{a}, by simp, by simp [hia]⟩
            · obtain ⟨d,hd,hid⟩ := (hcover i).mp hi
              exact ⟨d, List.mem_cons_of_mem _ hd, hid⟩
          · rintro ⟨d,hd,hid⟩
            rcases List.mem_cons.mp hd with rfl | hd
            · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hid))
            · exact Finset.mem_insert_of_mem ((hcover i).mpr ⟨d,hd,hid⟩)
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact ⟨by simp, by simp [batchWeight]; linarith⟩
          · exact hbins d hd
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact lt_of_not_ge hlight
          · exact hheavy d hd
        · simp only [List.map_cons, List.sum_cons] at hmass ⊢
          simp only [batchWeight, Finset.sum_singleton, Finset.sum_insert ha] at hmass ⊢
          linarith

lemma batch_tail_mass {I : Type cycleUniverse3} [_contextInstance1 : DecidableEq I] (w : I → ℕ) (P : List (Finset I)) (t : ℝ)
    (ht : ∀ b ∈ P, t ≤ batchWeight w b) :
    (P.length : ℝ)*t ≤ (P.map (batchWeight w)).sum := by
  induction P with
  | nil => simp
  | cons b bs ih =>
    have hb := ht b (by simp)
    have hbs := ih (fun d hd => ht d (by simp [hd]))
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons, List.sum_cons]
    nlinarith

theorem indexed_batch_partition (w : I → ℕ) (A : Finset I) (B : ℝ) (hB : 0 < B)
    (hw : ∀ i ∈ A, (w i : ℝ) ≤ B/2) :
    ∃ P : List (Finset I),
      P.Pairwise Disjoint ∧
      (∀ i, i ∈ A ↔ ∃ b ∈ P, i ∈ b) ∧
      (∀ b ∈ P, b.Nonempty ∧ batchWeight w b ≤ B) ∧
      (P.map (batchWeight w)).sum = batchWeight w A ∧
      (P.length : ℝ) ≤ 1 + 2*batchWeight w A/B := by
  obtain ⟨P,hd,hc,hb,ht,hm⟩ := indexed_batch_construction w A B hB hw
  refine ⟨P,hd,hc,hb,hm,?_⟩
  have htail := batch_tail_mass w P.tail (B/2) (fun b hb => (ht b hb).le)
  cases P with
  | nil =>
    simp only [List.length_nil, Nat.cast_zero]
    have hh := div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (batchWeight_nonneg w A)) hB.le
    linarith
  | cons b bs =>
    simp only [List.tail_cons, List.length_cons, Nat.cast_add, Nat.cast_one] at htail ⊢
    simp only [List.map_cons, List.sum_cons] at hm
    have hb0 := batchWeight_nonneg w b
    have hdv : (bs.length : ℝ) ≤ 2*batchWeight w A/B := by
      apply (le_div_iff₀ hB).mpr
      linarith
    linarith

end
end ErdosGallai.Indexing

namespace ErdosGallai.Indexing
noncomputable section
private theorem cover_card_le {V : Type cycleUniverse4} {I : Type cycleUniverse5} [DecidableEq V] [Fintype I]
    (S : Finset V) (W : I → Finset V)
    (h : S ⊆ Finset.univ.biUnion W) :
    S.card ≤ ∑ i, (W i).card :=
  (Finset.card_le_card h).trans Finset.card_biUnion_le

private theorem disjoint_piece_inter {V : Type cycleUniverse6} {J : Type cycleUniverse7} [DecidableEq V] [Fintype J]
    (R : J → Finset V) (hR : Pairwise fun i j => Disjoint (R i) (R j))
    (S : Finset V) :
    (S ∩ Finset.univ.biUnion R).card = ∑ j, (S ∩ R j).card := by
  rw [Finset.inter_biUnion]
  apply Finset.card_biUnion
  intro i _ j _ hij
  exact (hR hij).mono Finset.inter_subset_right Finset.inter_subset_right

theorem active_occurrences {V : Type cycleUniverse8} {I : Type cycleUniverse9} {J : Type cycleUniverse10} [DecidableEq V]
    [Fintype I] [Fintype J]
    (Y good : Finset V) (W : I → Finset V) (R : J → Finset V)
    (_hW : ∀ i, W i ⊆ Y) (hRsub : ∀ j, R j ⊆ Y)
    (hcover : Y ⊆ Finset.univ.biUnion W)
    (hR : Pairwise fun i j => Disjoint (R i) (R j))
    (keep : I → J → Prop) [∀ i j, Decidable (keep i j)] :
    let active := ∑ i, ∑ j, if keep i j then (W i ∩ R j ∩ good).card else 0
    let skipped := ∑ i, ∑ j, if keep i j then 0 else (W i ∩ R j ∩ good).card
    (∑ j, (R j).card) ≤ active + skipped + (Y \ good).card ∧
    active + Y.card ≤ (∑ j, (R j).card) + ∑ i, (W i).card := by
  classical
  dsimp only
  let U := Finset.univ.biUnion R
  have hU : U ⊆ Y := by
    intro v hv
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hv
    exact hRsub j hj
  have hcard : U.card = ∑ j, (R j).card := by
    apply Finset.card_biUnion
    intro i _ j _ hij
    exact hR hij
  let mass := ∑ i, ∑ j, (W i ∩ R j ∩ good).card
  let whole := ∑ i, (W i ∩ U).card
  have hsplit :
      (∑ i, ∑ j, if keep i j then (W i ∩ R j ∩ good).card else 0) +
      (∑ i, ∑ j, if keep i j then 0 else (W i ∩ R j ∩ good).card) = mass := by
    dsimp [mass]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> omega
  have hgood : (U ∩ good).card ≤ mass := by
    have hc : U ∩ good ⊆ Finset.univ.biUnion (fun i => W i ∩ U ∩ good) := by
      intro v hv
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp (hcover (hU (Finset.mem_inter.mp hv).1))
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr
        ⟨Finset.mem_inter.mpr ⟨hvi, (Finset.mem_inter.mp hv).1⟩,
          (Finset.mem_inter.mp hv).2⟩⟩
    apply (cover_card_le (U ∩ good) _ hc).trans
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro i _
    have heq : W i ∩ U ∩ good = (W i ∩ good) ∩ U := by ext v; simp only [Finset.mem_inter]; tauto
    rw [heq, disjoint_piece_inter R hR]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ext v
    simp only [Finset.mem_inter]
    tauto
  have hbad : (U \ good).card ≤ (Y \ good).card := by
    apply Finset.card_le_card
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨hU (Finset.mem_sdiff.mp hv).1, (Finset.mem_sdiff.mp hv).2⟩
  have hmass : mass ≤ whole := by
    apply Finset.sum_le_sum
    intro i _
    rw [disjoint_piece_inter R hR]
    exact Finset.sum_le_sum fun j _ => Finset.card_le_card Finset.inter_subset_left
  have houtside : (Y \ U).card ≤ ∑ i, (W i \ U).card := by
    apply cover_card_le
    intro v hv
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp (hcover (Finset.mem_sdiff.mp hv).1)
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_sdiff.mpr ⟨hvi, (Finset.mem_sdiff.mp hv).2⟩⟩
  have hY : U.card + (Y \ U).card = Y.card := by
    simpa only [Finset.inter_eq_right.mpr hU] using Finset.card_inter_add_card_sdiff Y U
  have hWsum : whole + (∑ i, (W i \ U).card) = ∑ i, (W i).card := by
    dsimp [whole]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.card_inter_add_card_sdiff (W i) U
  have hUgood := Finset.card_inter_add_card_sdiff U good
  constructor <;> omega

end
end ErdosGallai.Indexing

namespace ErdosGallai.Indexing
noncomputable section
attribute [local instance] Classical.propDecidable

lemma list_pairwise_get {A : Type cycleUniverse14} {R : A → A → Prop} {L : List A}
    (h : L.Pairwise R) (hs : (∀ ⦃left right⦄, R left right → R right left)) : Pairwise fun i j : Fin L.length => R (L.get i) (L.get j) := by
  intro i j hij
  rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun he => hij (Fin.ext he)) with hlt | hgt
  · exact List.pairwise_iff_getElem.mp h i.val j.val i.isLt j.isLt hlt
  · exact hs (List.pairwise_iff_getElem.mp h j.val i.val j.isLt i.isLt hgt)

lemma list_sum_get {A : Type cycleUniverse15} {M : Type cycleUniverse16} [AddCommMonoid M] (L : List A) (f : A → M) :
    (∑ i : Fin L.length, f (L.get i)) = (L.map f).sum := by
  rw [← List.sum_ofFn]
  calc
    _ = (List.map f (List.ofFn L.get)).sum := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [List.ofFn_get]

structure GraphBatches {V : Type} (F : SimpleGraph V) (Y : Finset V) (B T : ℝ) where
  Index : Type
  finite : Fintype Index
  graph : Index → SimpleGraph V
  vertices : Index → Finset V
  graph_le : ∀ i, graph i ≤ F
  disjoint : Pairwise fun i j => Disjoint (graph i).edgeSet (graph j).edgeSet
  edge_cover : (⋃ i, (graph i).edgeSet) = F.edgeSet
  supported : ∀ i, ∀ ⦃x y⦄, (graph i).Adj x y → x ∈ vertices i ∧ y ∈ vertices i
  subset : ∀ i, vertices i ⊆ Y
  vertex_cover : Y ⊆ univ.biUnion vertices
  order_le : ∀ i, ((vertices i).card:ℝ) ≤ B
  mass_le : (∑ i, ((vertices i).card:ℝ)) ≤ T
  count_le : (Fintype.card Index:ℝ) ≤ 1+2*T/B
attribute [instance] GraphBatches.finite

theorem materialize_batches {V I : Type} [Fintype I]
    (F : SimpleGraph V) (Y : Finset V) (H : I → SimpleGraph V) (U : I → Finset V)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hu : (⋃ i, (H i).edgeSet) = F.edgeSet)
    (hU : ∀ i, ∀ ⦃x y⦄, (H i).Adj x y → x ∈ U i ∧ y ∈ U i)
    (hUY : ∀ i, U i ⊆ Y) (hY : Y ⊆ univ.biUnion U)
    (B : ℝ) (hB : 0 < B) (hsmall : ∀ i, ((U i).card:ℝ) ≤ B/2) :
    Nonempty (GraphBatches F Y B (∑ i, ((U i).card:ℝ))) := by
  classical
  obtain ⟨L,hLd,hLc,hLn,hLm,hLnum⟩ := indexed_batch_partition (fun i => (U i).card) univ B hB (fun i _ => hsmall i)
  let A := Fin L.length
  let bag (a : A) : Finset I := L.get a
  let W (a : A) := (bag a).biUnion U
  let J (a : A) : SimpleGraph V := ⨆ i ∈ bag a, H i
  have hbagd : Pairwise fun a b => Disjoint (bag a) (bag b) := list_pairwise_get hLd (fun _ _ h => h.symm)
  have hbagcov (i : I) : ∃ a : A, i ∈ bag a := by
    obtain ⟨b,hb,hi⟩ := (hLc i).mp (mem_univ _)
    obtain ⟨k,hk⟩ := List.mem_iff_get.mp hb
    exact ⟨k,by change i ∈ L.get k; rwa [hk]⟩
  have hJedge (a : A) : (J a).edgeSet = ⋃ i ∈ bag a, (H i).edgeSet := by
    ext e
    induction e using Sym2.ind with
    | _ x y => simp [J,SimpleGraph.mem_edgeSet,SimpleGraph.iSup_adj]
  have hJsub (a : A) : (J a).edgeSet ⊆ F.edgeSet := by
    rw [hJedge,← hu]
    exact Set.iUnion₂_subset fun i _ => Set.subset_iUnion (fun j : I => (H j).edgeSet) i
  have hWweight (a : A) : ((W a).card:ℝ) ≤ batchWeight (fun i => (U i).card) (bag a) := by
    have hh := Finset.card_biUnion_le (s := bag a) (t := U)
    dsimp only [W,batchWeight]
    exact_mod_cast hh
  have hJd : Pairwise fun a b => Disjoint (J a).edgeSet (J b).edgeSet := by
    intro a b hab
    rw [hJedge,hJedge]
    apply Set.disjoint_left.mpr
    rintro e he he'
    obtain ⟨i,hi,he⟩ := Set.mem_iUnion₂.mp he
    obtain ⟨j,hj,he'⟩ := Set.mem_iUnion₂.mp he'
    have hij : i ≠ j := by rintro rfl; exact Finset.disjoint_left.mp (hbagd hab) hi hj
    exact Set.disjoint_left.mp (hHH hij) he he'
  refine ⟨{
    Index := A
    finite := inferInstance
    graph := J
    vertices := W
    graph_le := fun a => SimpleGraph.edgeSet_subset_edgeSet.mp (hJsub a)
    disjoint := hJd
    edge_cover := ?_
    supported := ?_
    subset := ?_
    vertex_cover := ?_
    order_le := ?_
    mass_le := ?_
    count_le := ?_ }⟩
  · apply Set.Subset.antisymm (Set.iUnion_subset hJsub)
    intro e he
    rw [← hu] at he
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
    obtain ⟨a,hia⟩ := hbagcov i
    exact Set.mem_iUnion.mpr ⟨a,by rw [hJedge]; exact Set.mem_iUnion₂.mpr ⟨i,hia,hi⟩⟩
  · intro a x y hxy
    have he : s(x,y) ∈ (J a).edgeSet := hxy
    rw [hJedge] at he
    obtain ⟨i,hi,he⟩ := Set.mem_iUnion₂.mp he
    exact ⟨Finset.mem_biUnion.mpr ⟨i,hi,(hU i he).1⟩,Finset.mem_biUnion.mpr ⟨i,hi,(hU i he).2⟩⟩
  · intro a v hv
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hv
    exact hUY i hi
  · intro v hv
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp (hY hv)
    obtain ⟨a,ha⟩ := hbagcov i
    exact Finset.mem_biUnion.mpr ⟨a,mem_univ _,Finset.mem_biUnion.mpr ⟨i,ha,hi⟩⟩
  · intro a
    exact (hWweight a).trans ((hLn (bag a) (L.get_mem a)).2)
  · calc
      _ ≤ ∑ a, batchWeight (fun i => (U i).card) (bag a) := Finset.sum_le_sum (fun a _ => hWweight a)
      _ = _ := by rw [list_sum_get,hLm]; rfl
  · simpa only [A,Fintype.card_fin,batchWeight] using hLnum

end
end ErdosGallai.Indexing

namespace ErdosGallai.Indexing
noncomputable section
attribute [local instance] Classical.propDecidable

def goodVertices {V : Type} [Fintype V] (F : SimpleGraph V) (Y : Finset V) (a : ℝ) : Finset V :=
  Y.filter fun v => (F.degree v:ℝ) ≤ a

lemma bad_vertices_degree_bound {V : Type} [Fintype V] (F : SimpleGraph V) (Y : Finset V) (a : ℝ) :
    a * ((Y \ goodVertices F Y a).card:ℝ) ≤ 2 * (F.edgeFinset.card:ℝ) := by
  classical
  let bad := Y \ goodVertices F Y a
  have hbad (v) (hv : v ∈ bad) : a ≤ (F.degree v:ℝ) := by
    have hn := (Finset.mem_sdiff.mp hv).2
    exact le_of_lt (lt_of_not_ge (fun h => hn (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv).1,h⟩)))
  calc
    _ = ∑ v ∈ bad, a := by simp [bad,mul_comm]
    _ ≤ ∑ v ∈ bad, (F.degree v:ℝ) := Finset.sum_le_sum hbad
    _ ≤ ∑ v, (F.degree v:ℝ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
    _ = _ := by exact_mod_cast F.sum_degrees_eq_twice_card_edges

structure ActiveFamily {V R B : Type} [Fintype V] [Fintype R] [Fintype B]
    (F : SimpleGraph V) (Y : Finset V) (W : B → Finset V) (U : R → Finset V) (a L : ℝ) where
  Index : B → Type
  finite : ∀ b, Fintype (Index b)
  vertices : ∀ b, Index b → Finset V
  router : ∀ b, Index b → R
  subset_batch : ∀ b i, vertices b i ⊆ W b
  subset_router : ∀ b i, vertices b i ⊆ U (router b i)
  disjoint : ∀ b, Pairwise fun i j => Disjoint (vertices b i) (vertices b j)
  degree_le : ∀ b i v, v ∈ vertices b i → (F.degree v:ℝ) ≤ a
  large : ∀ b i, L ≤ ((vertices b i).card:ℝ)
  lower : (∑ r, ((U r).card:ℝ)) - ((Y \ goodVertices F Y a).card:ℝ) -
    L * Fintype.card B * Fintype.card R ≤ ∑ b, ∑ i, ((vertices b i).card:ℝ)
  upper : (∑ b, ∑ i, ((vertices b i).card:ℝ)) + Y.card ≤
    (∑ r, ((U r).card:ℝ)) + ∑ b, ((W b).card:ℝ)
attribute [instance] ActiveFamily.finite

theorem choose_active_family {V R B : Type} [Fintype V] [Fintype R] [Fintype B]
    (F : SimpleGraph V) (Y : Finset V) (W : B → Finset V) (U : R → Finset V) (a L : ℝ)
    (hL : 0 ≤ L) (hW : ∀ b, W b ⊆ Y) (hU : ∀ r, U r ⊆ Y)
    (hcov : Y ⊆ univ.biUnion W) (hUd : Pairwise fun r s => Disjoint (U r) (U s)) :
    Nonempty (ActiveFamily F Y W U a L) := by
  classical
  let good := goodVertices F Y a
  let S (b : B) (r : R) := W b ∩ U r ∩ good
  let keep (b : B) (r : R) := L ≤ ((S b r).card:ℝ)
  let I (b : B) := {r : R // keep b r}
  let X (b : B) (i : I b) := S b i.val
  have hsum (b : B) : (∑ i : I b, ((X b i).card:ℝ)) =
      ∑ r, if keep b r then ((S b r).card:ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simpa only [Finset.subtype_univ] using (Finset.sum_subtype_eq_sum_filter (s := univ) (p := keep b) (fun r => ((S b r).card:ℝ)))
  have hadd := active_occurrences Y good W U hW hU hcov hUd keep
  dsimp only at hadd
  have hlow : (∑ r, ((U r).card:ℝ)) ≤
      (∑ b, ∑ r, if keep b r then ((S b r).card:ℝ) else 0) +
      (∑ b, ∑ r, if keep b r then 0 else ((S b r).card:ℝ)) + ((Y \ good).card:ℝ) := by
    exact_mod_cast hadd.1
  have hhigh : (∑ b, ∑ r, if keep b r then ((S b r).card:ℝ) else 0) + Y.card ≤
      (∑ r, ((U r).card:ℝ)) + ∑ b, ((W b).card:ℝ) := by exact_mod_cast hadd.2
  have hskip : (∑ b, ∑ r, if keep b r then 0 else ((S b r).card:ℝ)) ≤
      L * Fintype.card B * Fintype.card R := by
    calc
      _ ≤ ∑ _b : B, ∑ _r : R, L := by
        apply Finset.sum_le_sum; intro b _
        apply Finset.sum_le_sum; intro r _
        split_ifs with hk
        · exact hL
        · exact le_of_lt (lt_of_not_ge hk)
      _ = _ := by simp; ring
  refine ⟨{
    Index := I
    finite := fun _ => inferInstance
    vertices := X
    router := fun _ i => i.val
    subset_batch := fun _ _ => Finset.inter_subset_left.trans Finset.inter_subset_left
    subset_router := fun _ _ => Finset.inter_subset_left.trans Finset.inter_subset_right
    disjoint := ?_
    degree_le := ?_
    large := fun _ i => i.property
    lower := ?_
    upper := ?_ }⟩
  · intro b i j hij
    exact (hUd (fun h => hij (Subtype.ext h))).mono
      (Finset.inter_subset_left.trans Finset.inter_subset_right)
      (Finset.inter_subset_left.trans Finset.inter_subset_right)
  · intro b i v hv
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
  · simp_rw [hsum]
    dsimp only [good] at hlow hskip
    linarith
  · simpa only [hsum] using hhigh

lemma thirds_le_halves {k : ℕ} (hk : 8 ≤ k) : (k:ℝ)/3 ≤ (k/2:ℕ) := by
  have h : k ≤ 3*(k/2) := by omega
  have h' : (k:ℝ) ≤ 3*(k/2:ℕ) := by exact_mod_cast h
  linarith

end
end ErdosGallai.Indexing

end
/-! ### Upstream module `Combinatorics/CycleDecomposition/PrefixSelection.lean` -/

noncomputable section
open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Finset
namespace ErdosGallai
noncomputable section
theorem prefix_selection (S : ℕ → ℝ) (hS : ∀ j, 0 ≤ S j) (K N : ℕ)
    (hsupp : ∀ j, N ≤ j → S j = 0) (hne : ∃ j, 0 < S j) :
    ∃ i, 0 < S i ∧ ∑ j ∈ range (i+K+1), S j ≤ 4*(K+1:ℝ)*S i := by
  let A := (range N).filter (fun j => 0 < S j)
  have hA : A.Nonempty := by
    obtain ⟨j,hj⟩ := hne
    exact ⟨j, by
      simp only [A, mem_filter, mem_range]
      exact ⟨by by_contra hn; rw [hsupp j (by omega)] at hj; linarith, hj⟩⟩
  let i₀ := A.min' hA
  have hi₀A : i₀ ∈ A := A.min'_mem hA
  have hi₀pos : 0 < S i₀ := (mem_filter.mp hi₀A).2
  have hstart : (∑ j ∈ range (i₀+1), S j) = S i₀ := by
    apply sum_eq_single i₀
    · intro j hj hji
      by_contra hjzero
      have hjpos : 0 < S j := lt_of_le_of_ne (hS j) (Ne.symm hjzero)
      have hjA : j ∈ A := by
        simp only [A, mem_filter, mem_range]
        refine ⟨?_, hjpos⟩
        have hiN := (mem_range.mp (mem_filter.mp hi₀A).1)
        have hjle := mem_range.mp hj
        omega
      have hmin : i₀ ≤ j := A.min'_le j hjA
      have hjle := mem_range.mp hj
      omega
    · intro hi
      exact (hi (by simp)).elim
  let B := A.filter (fun i => (∑ j ∈ range (i+1), S j) ≤ 2*(K+1:ℝ)*S i)
  have hB : B.Nonempty := by
    refine ⟨i₀, mem_filter.mpr ⟨hi₀A, ?_⟩⟩
    rw [hstart]
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  let i := B.max' hB
  have hiB : i ∈ B := B.max'_mem hB
  have hiA : i ∈ A := (mem_filter.mp hiB).1
  have hipos : 0 < S i := (mem_filter.mp hiA).2
  have hinv : (∑ j ∈ range (i+1), S j) ≤ 2*(K+1:ℝ)*S i := (mem_filter.mp hiB).2
  refine ⟨i, hipos, ?_⟩
  by_contra hfail
  have hfail' : 4*(K+1:ℝ)*S i < ∑ j ∈ range (i+K+1), S j := lt_of_not_ge hfail
  have hwindow : 2*(K+1:ℝ)*S i < ∑ j ∈ Ico (i+1) (i+K+1), S j := by
    have hsplit := Finset.sum_range_add_sum_Ico S (by omega : i+1 ≤ i+K+1)
    linarith
  have hwindow_nonempty : (Ico (i+1) (i+K+1)).Nonempty := by
    by_contra hh
    rw [Finset.not_nonempty_iff_eq_empty.mp hh] at hwindow
    simp only [sum_empty] at hwindow
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  obtain ⟨j,hjw,hmax⟩ := Finset.exists_max_image (Ico (i+1) (i+K+1)) S hwindow_nonempty
  have hsum : (∑ l ∈ Ico (i+1) (i+K+1), S l) ≤ (K:ℝ)*S j := by
    calc
      _ ≤ ∑ _l ∈ Ico (i+1) (i+K+1), S j := sum_le_sum hmax
      _ = _ := by simp []
  have hdouble : 2*S i < S j := by
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  have hjpos : 0 < S j := by linarith
  have hjA : j ∈ A := by
    simp only [A, mem_filter, mem_range]
    exact ⟨by by_contra hjN; rw [hsupp j (by omega)] at hjpos; linarith, hjpos⟩
  have hjbounds := Finset.mem_Ico.mp hjw
  have hpartial : (∑ l ∈ Ico (i+1) (j+1), S l) ≤ (K:ℝ)*S j := by
    calc
      _ ≤ ∑ l ∈ Ico (i+1) (i+K+1), S l := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro l hl
          simp only [mem_Ico] at hl ⊢
          omega
        · intro l _ _; exact hS l
      _ ≤ _ := hsum
  have hjinv : (∑ l ∈ range (j+1), S l) ≤ 2*(K+1:ℝ)*S j := by
    have hsplit := Finset.sum_range_add_sum_Ico S (by omega : i+1 ≤ j+1)
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  have hjB : j ∈ B := mem_filter.mpr ⟨hjA,hjinv⟩
  have hji : j ≤ i := B.le_max' j hjB
  omega

end
end ErdosGallai

namespace ErdosGallai

def MainStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ∃ k : ℕ, EdgeDecomposition G k ∧ (k : ℝ) ≤ C * n
end ErdosGallai
end
/-! ### Upstream module `Combinatorics/CycleDecomposition/CostRegrouping.lean` -/

section
open _root_.Filter _root_.Asymptotics _root_.Real
noncomputable section
namespace ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def StageSplit.rest {P : AssignedPiece V} (s : StageSplit P) (B : AssignedPiece V) : AssignedPiece V :=
  if h : B ∈ s.boxes then ⟨B.vertices,s.remainder B,s.remainder_supported B h⟩ else B

@[simp] lemma StageSplit.rest_vertices {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : AssignedPiece V} (s : StageSplit P) (B) :
    (s.rest B).vertices = B.vertices := by unfold StageSplit.rest; split_ifs <;> rfl
lemma StageSplit.rest_graph {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : AssignedPiece V} (s : StageSplit P) {B} (hB : B ∈ s.boxes) :
    (s.rest B).graph = s.remainder B := by simp [StageSplit.rest,hB]
lemma StageSplit.children_eq_map_rest {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : AssignedPiece V} (s : StageSplit P) :
    s.children = s.boxes.map s.rest := by
  unfold StageSplit.children
  rw [← List.pmap_eq_map (f := s.rest) (fun B (hB : B ∈ s.boxes) => hB)]
  apply List.pmap_congr_left
  intro B hB
  simp [StageSplit.rest,hB]

lemma pastPieces_flatMap (s : SplitSystem V) (j k) {I : Type cycleUniverse1}
    (L : List I) (f : I → List (AssignedPiece V)) :
    (pastPieces s j k (L.flatMap f)).Perm (L.flatMap (fun i => pastPieces s j k (f i))) := by
  induction k with
  | zero => simp [pastPieces]
  | succ k ih =>
    simp only [pastPieces,advance_flatMap,levelPieces,List.flatMap_assoc]
    apply (ih.append_right _).trans
    exact List.flatMap_append_perm _ _ _
lemma pastCycles_flatMap (s : SplitSystem V) (j k) {I : Type cycleUniverse2}
    (L : List I) (f : I → List (AssignedPiece V)) :
    (pastCycles s j k (L.flatMap f)).Perm (L.flatMap (fun i => pastCycles s j k (f i))) := by
  induction k with
  | zero => simp [pastCycles]
  | succ k ih =>
    simp only [pastCycles,advance_flatMap,levelCycles,List.flatMap_assoc]
    apply (ih.append_right _).trans
    exact List.flatMap_append_perm _ _ _

lemma pastPieces_add (s : SplitSystem V) (j k l) (L : List (AssignedPiece V)) :
    pastPieces s j (k+l) L = pastPieces s j k L ++ pastPieces s (j+k) l (advance s j k L) := by
  induction l with
  | zero => simp [pastPieces]
  | succ l ih => simp [pastPieces,ih,advance_add,Nat.add_assoc,List.append_assoc]
lemma pastCycles_add (s : SplitSystem V) (j k l) (L : List (AssignedPiece V)) :
    pastCycles s j (k+l) L = pastCycles s j k L ++ pastCycles s (j+k) l (advance s j k L) := by
  induction l with
  | zero => simp [pastCycles]
  | succ l ih => simp [pastCycles,ih,advance_add,Nat.add_assoc,List.append_assoc]

lemma advance_mem_mono (s : SplitSystem V) (j k) {L M : List (AssignedPiece V)}
    (h : ∀ P ∈ L, P ∈ M) : ∀ Q ∈ advance s j k L, Q ∈ advance s j k M := by
  induction k with
  | zero => exact h
  | succ k ih =>
    intro Q hQ
    obtain ⟨P,hP,B,hB,hv,hg⟩ := (nextLayer_mem s (j+k) _ Q).mp hQ
    exact (nextLayer_mem s (j+k) _ Q).mpr ⟨P,ih P hP,B,hB,hv,hg⟩

lemma advance_local_mem (s : SplitSystem V) (i k) (L : List (AssignedPiece V))
    {P B : AssignedPiece V} (hP : P ∈ advance s 0 i L) (hB : B ∈ (s i P).boxes) :
    ∀ Q ∈ advance s (i+1) k [(s i P).rest B], Q ∈ advance s 0 (i+1+k) L := by
  rw [advance_add, Nat.zero_add]
  apply advance_mem_mono
  intro Q hQ
  simp only [List.mem_singleton] at hQ
  subst Q
  simp only [advance_succ,Nat.zero_add]

  apply (nextLayer_mem s i _ _).mpr
  exact ⟨P,hP,B,hB,(s i P).rest_vertices B,(s i P).rest_graph hB⟩

lemma box_regroup {B R : AssignedPiece V} (A : List (AssignedPiece V))
    (hBR : GraphPartition B.graph (R.graph :: A.map AssignedPiece.graph))
    (s : SplitSystem V) (j k : ℕ) :
    GraphPartition B.graph
      (pastCycles s j k [R] ++ (pastPieces s j k [R]).map AssignedPiece.graph ++
        [graphUnion ((advance s j k [R]).map AssignedPiece.graph ++ A.map AssignedPiece.graph)]) := by
  let L := (advance s j k [R]).map AssignedPiece.graph ++ A.map AssignedPiece.graph
  have hL : GraphPartition (graphUnion L) L := by
    apply graphPartition_of_le_one
    intro x y
    have hb := hBR x y
    have hr := past_partition s j k R x y
    simp only [edgeOccurrences_cons,edgeOccurrences_append] at hb hr ⊢
    dsimp only [L]
    rw [edgeOccurrences_append]
    split_ifs at hb hr <;> omega
  intro x y
  have hb := hBR x y
  have hr := past_partition s j k R x y
  have hl := hL x y
  simp only [edgeOccurrences_cons,edgeOccurrences_append,edgeOccurrences_nil,Nat.add_zero] at hb hr hl ⊢
  dsimp only [L] at hl
  rw [edgeOccurrences_append] at hl
  omega

lemma piece_list_cost (L : List (AssignedPiece V)) (c : ℝ)
    (h : ∀ P ∈ L, (decompositionCost P.graph:ℝ) ≤ c*P.vertices.card) :
    (L.map (fun P => (decompositionCost P.graph:ℝ))).sum ≤ c*vertexMass L := by
  induction L with
  | nil => simp
  | cons P L ih =>
    have hp := h P (by simp)
    have hl := ih (fun Q hQ => h Q (by simp [hQ]))
    simp only [List.map_cons,List.sum_cons,vertexMass_cons]
    nlinarith

lemma box_cost_regroup {B R : AssignedPiece V} (A : List (AssignedPiece V))
    (hBR : GraphPartition B.graph (R.graph :: A.map AssignedPiece.graph))
    (s : SplitSystem V) (j k : ℕ) (c q : ℝ)
    (hp : ∀ P ∈ pastPieces s j k [R], (decompositionCost P.graph:ℝ) ≤ c*P.vertices.card)
    (hq : (decompositionCost (graphUnion ((advance s j k [R]).map AssignedPiece.graph ++
      A.map AssignedPiece.graph)):ℝ) ≤ q) :
    (decompositionCost B.graph:ℝ) ≤ (pastCycles s j k [R]).length +
      c*vertexMass (pastPieces s j k [R]) + q := by
  have hh := decompositionCost_partition_real (box_regroup A hBR s j k)
  have hc := decompositionCost_cycles (pastCycles s j k [R]) (pastCycles_good s j k [R])
  have hm := piece_list_cost (pastPieces s j k [R]) c hp
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,List.map_map,Function.comp_def] at hh
  linarith

end
end ErdosGallai.Scale

namespace ErdosGallai
noncomputable section
def mainP : ℝ := 804
def mainEta : ℝ := 1/(100*mainP)
def mainH : ℝ := 80/(Scale.scaleTheta^200)
def mainA₁ : ℝ := mainH + 4/3
def mainA₂ : ℝ := max (9*mainP+8) (9*mainH)
lemma mainP_pos : 0 < mainP := by norm_num [mainP]
lemma mainEta_pos : 0 < mainEta := by norm_num [mainEta,mainP]
lemma mainH_pos : 0 < mainH := by unfold mainH; exact div_pos (by norm_num) (pow_pos Scale.scaleTheta_pos _)
lemma mainA₁_nonneg : 0 ≤ mainA₁ := by unfold mainA₁; linarith [mainH_pos]
lemma mainA₂_nonneg : 0 ≤ mainA₂ := by unfold mainA₂; exact (by norm_num [mainP] : (0:ℝ) ≤ 9*mainP+8).trans (le_max_left _ _)
structure MainScaleReady (wmin D : ℝ) : Prop where
  gt_one : 1 < D
  log_large : wmin ≤ logb 2 D
  cycle_power : 1/(D^(1/100:ℝ)) ≤ 1/logb 2 D
  batch_power : D^(1/1000:ℝ) ≤ D^(3/10:ℝ)/2
  bad_power : 2*D^(-9/1000:ℝ) ≤ 1/logb 2 D
  skip_power : D^(-87/100:ℝ)+4*D^(-3/20:ℝ) ≤ 1/logb 2 D
  active_eight : 8 ≤ D^(3/100:ℝ)

lemma eventually_inverse_power_log (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, C*D^(-ε) ≤ 1/logb 2 D := by
  filter_upwards [Batch.eventually_logb_le_power (ε/2) (by positivity),
    Batch.eventually_const_mul_power_le C (ε/2) ε (by linarith),
    eventually_gt_atTop (1:ℝ)] with D hl hc hD
  have hd : 0 < D := by linarith
  have hw : 0 < logb 2 D := Real.logb_pos (by norm_num) hD
  have hp : 0 < D^ε := Real.rpow_pos_of_pos hd _
  apply (le_div_iff₀ hw).mpr
  calc
    _ = (C*logb 2 D)/D^ε := by rw [Real.rpow_neg hd.le]; ring
    _ ≤ 1 := (div_le_one hp).mpr ((mul_le_mul_of_nonneg_left hl hC).trans hc)

lemma main_scale_ready_cutoff (wmin : ℝ) : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, MainScaleReady wmin D := by
  have hev : ∀ᶠ D : ℝ in atTop, MainScaleReady wmin D := by
    filter_upwards [eventually_gt_atTop (1:ℝ),
      (Real.tendsto_logb_atTop (by norm_num : (1:ℝ) < 2)).eventually (eventually_ge_atTop wmin),
      eventually_inverse_power_log 1 (1/100) (by norm_num) (by norm_num),
      Batch.eventually_const_mul_power_le 2 (1/1000) (3/10) (by norm_num),
      eventually_inverse_power_log 2 (9/1000) (by norm_num) (by norm_num),
      eventually_inverse_power_log 2 (87/100) (by norm_num) (by norm_num),
      eventually_inverse_power_log 8 (3/20) (by norm_num) (by norm_num),
      Batch.eventually_constant_le_power 8 (3/100) (by norm_num)] with D hD hw hc hb hbad hs₁ hs₂ h8
    refine ⟨hD,hw,?_,by linarith,by simpa only [neg_div] using hbad,?_,h8⟩
    · simpa only [one_mul,Real.rpow_neg (by linarith : 0 ≤ D),one_div] using hc
    · simp only [neg_div]
      linarith
  obtain ⟨A,hA⟩ := eventually_atTop.mp hev
  refine ⟨max A 2,lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) (le_max_right _ _),?_⟩
  intro D hD
  exact hA D ((le_max_left _ _).trans hD)

lemma MainScaleReady.active_square {w D : ℝ} (h : MainScaleReady w D) :
    (D^(1/100:ℝ))^2 ≤ D^(3/100:ℝ) := by
  rw [← Real.rpow_mul_natCast (by linarith [h.gt_one] : 0 ≤ D)]
  apply Real.rpow_le_rpow_of_exponent_le h.gt_one.le
  norm_num

lemma MainScaleReady.bad_count {w D y b : ℝ} (h : MainScaleReady w D) (hy : 0 ≤ y)
    (hb : D^(1/100:ℝ)*b ≤ 2*y*D^(1/1000:ℝ)) : b ≤ y/logb 2 D := by
  have hd : 0 < D := by linarith [h.gt_one]
  have hp : 0 < D^(1/100:ℝ) := Real.rpow_pos_of_pos hd _
  calc
    b ≤ 2*y*D^(1/1000:ℝ)/D^(1/100:ℝ) := (le_div_iff₀ hp).mpr (by simpa [mul_comm] using hb)
    _ = y*(2*D^(-9/1000:ℝ)) := by
      have he : D^(1/1000:ℝ)/D^(1/100:ℝ) = D^(-9/1000:ℝ) := by
        rw [← Real.rpow_sub hd]; norm_num
      rw [show 2*y*D^(1/1000:ℝ)/D^(1/100:ℝ) = (2*y)*(D^(1/1000:ℝ)/D^(1/100:ℝ)) by ring,he]
      ring
    _ ≤ y*(1/logb 2 D) := mul_le_mul_of_nonneg_left h.bad_power hy
    _ = _ := by ring

lemma MainScaleReady.skip_count {w D y T b r : ℝ} (h : MainScaleReady w D)
    (hy : 0 ≤ y) (_hb : 0 ≤ b) (hr : 0 ≤ r)
    (hyD : y ≤ D^(51/50:ℝ)) (hT : T ≤ 2*y)
    (hbT : b ≤ 1+2*T/D^(3/10:ℝ)) (hrY : D^(9/10:ℝ)*r ≤ y) :
    D^(3/100:ℝ)*b*r ≤ y/logb 2 D := by
  have hd : 0 < D := by linarith [h.gt_one]
  have hB : 0 < D^(3/10:ℝ) := Real.rpow_pos_of_pos hd _
  have hS : 0 < D^(9/10:ℝ) := Real.rpow_pos_of_pos hd _
  have hL : 0 ≤ D^(3/100:ℝ) := Real.rpow_nonneg hd.le _
  have hb' : b ≤ 1+4*y/D^(3/10:ℝ) := by
    have ht := div_le_div_of_nonneg_right (by linarith : 2*T ≤ 4*y) hB.le
    linarith
  have hr' : r ≤ y/D^(9/10:ℝ) := (le_div_iff₀ hS).mpr (by simpa [mul_comm] using hrY)
  have he₁ : D^(3/100:ℝ)/D^(9/10:ℝ) = D^(-87/100:ℝ) := by
    rw [← Real.rpow_sub hd]; norm_num
  have he₂ : D^(51/50:ℝ)*D^(3/100:ℝ)/(D^(3/10:ℝ)*D^(9/10:ℝ)) = D^(-3/20:ℝ) := by
    rw [← Real.rpow_add hd,← Real.rpow_add hd,← Real.rpow_sub hd]; norm_num
  calc
    _ ≤ D^(3/100:ℝ)*(1+4*y/D^(3/10:ℝ))*(y/D^(9/10:ℝ)) := by gcongr
    _ = y*(D^(3/100:ℝ)/D^(9/10:ℝ)+4*y*(D^(3/100:ℝ)/(D^(3/10:ℝ)*D^(9/10:ℝ)))) := by ring
    _ ≤ y*(D^(3/100:ℝ)/D^(9/10:ℝ)+4*D^(51/50:ℝ)*(D^(3/100:ℝ)/(D^(3/10:ℝ)*D^(9/10:ℝ)))) := by gcongr
    _ = y*(D^(-87/100:ℝ)+4*D^(-3/20:ℝ)) := by rw [he₁,← he₂]; ring
    _ ≤ y*(1/logb 2 D) := mul_le_mul_of_nonneg_left h.skip_power hy
    _ = _ := by ring

end
end ErdosGallai

namespace ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def costMass (L : List (AssignedPiece V)) : ℝ := (L.map (fun Q => (decompositionCost Q.graph:ℝ))).sum

lemma costMass_bound (L : List (AssignedPiece V)) (f : AssignedPiece V → ℝ)
    (h : ∀ P ∈ L, (decompositionCost P.graph:ℝ) ≤ f P) : costMass L ≤ (L.map f).sum :=
  List.sum_le_sum h

lemma past_cost (s : SplitSystem V) (j k) (P : AssignedPiece V) (c : ℝ)
    (hp : ∀ Q ∈ pastPieces s j k [P], (decompositionCost Q.graph:ℝ) ≤ c*Q.vertices.card) :
    (decompositionCost P.graph:ℝ) ≤ ((pastCycles s j k [P]).length:ℝ) +
      c*vertexMass (pastPieces s j k [P]) + costMass (advance s j k [P]) := by
  have hh := decompositionCost_partition_real (past_partition s j k P)
  have hc := decompositionCost_cycles _ (pastCycles_good s j k [P])
  have hm := piece_list_cost _ c hp
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def] at hh
  dsimp only [costMass]
  linarith

lemma stage_cost (s : SplitSystem V) (j) (P : AssignedPiece V) :
    (decompositionCost P.graph:ℝ) ≤ ((s j P).cycles.length:ℝ) + costMass (s j P).boxes := by
  have hh := decompositionCost_partition_real (s j P).partition
  have hc := decompositionCost_cycles _ (s j P).cycles_good
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def] at hh
  dsimp only [costMass]
  linarith

lemma vertexMass_perm {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {L M : List (AssignedPiece V)} (h : L.Perm M) : vertexMass L = vertexMass M :=
  (h.map _).sum_eq

lemma pastCycles_sum (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    (L.map (fun P => ((pastCycles s j k [P]).length:ℝ))).sum = ((pastCycles s j k L).length:ℝ) := by
  have h := (pastCycles_flatMap s j k L (fun P => [P])).length_eq
  simp only [List.flatMap_singleton'] at h
  rw [h,List.length_flatMap]
  simp [Function.comp_def]

lemma pastPieces_sum (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    (L.map (fun P => vertexMass (pastPieces s j k [P]))).sum = vertexMass (pastPieces s j k L) := by
  have h := vertexMass_perm (pastPieces_flatMap s j k L (fun P => [P]))
  simpa only [List.flatMap_singleton',vertexMass_flatMap] using h.symm

lemma advance_sum (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    (L.map (fun P => vertexMass (advance s j k [P]))).sum = vertexMass (advance s j k L) := by
  have h := congrArg vertexMass (advance_flatMap s j k L (fun P => [P]))
  simpa only [List.flatMap_singleton',vertexMass_flatMap] using h.symm

lemma pastCycles_after_first (s : SplitSystem V) (j k) (P : AssignedPiece V) :
    (pastCycles s j (k+1) [P]).Perm ((s j P).cycles ++
      (s j P).boxes.flatMap (fun B => pastCycles s (j+1) k [(s j P).rest B])) := by
  rw [show k+1=1+k by omega,pastCycles_add]
  simp only [pastCycles,advance_zero,List.nil_append,levelCycles,List.flatMap_singleton,
    Nat.add_zero,advance_succ,nextLayer,Nat.add_zero,List.flatMap_singleton,StageSplit.children_eq_map_rest]
  have hh := pastCycles_flatMap s (j+1) k (s j P).boxes (fun B => [(s j P).rest B])
  simp only [← List.map_eq_flatMap] at hh
  exact hh.append_left _

lemma pastPieces_after_first (s : SplitSystem V) (j k) (P : AssignedPiece V) :
    (pastPieces s j (k+1) [P]).Perm ((s j P).boxes.flatMap (s j P).pieces ++
      (s j P).boxes.flatMap (fun B => pastPieces s (j+1) k [(s j P).rest B])) := by
  rw [show k+1=1+k by omega,pastPieces_add]
  simp only [pastPieces,advance_zero,List.nil_append,levelPieces,List.flatMap_singleton,
    Nat.add_zero,advance_succ,nextLayer,Nat.add_zero,List.flatMap_singleton,StageSplit.children_eq_map_rest]
  have hh := pastPieces_flatMap s (j+1) k (s j P).boxes (fun B => [(s j P).rest B])
  simp only [← List.map_eq_flatMap] at hh
  exact hh.append_left _

lemma advance_after_first (s : SplitSystem V) (j k) (P : AssignedPiece V) :
    advance s j (k+1) [P] = (s j P).boxes.flatMap (fun B => advance s (j+1) k [(s j P).rest B]) := by
  rw [show k+1=1+k by omega,advance_add]
  simp only [advance_succ,advance_zero,Nat.add_zero,nextLayer,List.flatMap_singleton,
    StageSplit.children_eq_map_rest]
  simpa only [← List.map_eq_flatMap] using advance_flatMap s (j+1) k (s j P).boxes (fun B => [(s j P).rest B])

lemma selected_input_cost (s : SplitSystem V) (j k) (P : AssignedPiece V) (c α β γ : ℝ)
    (hp : ∀ B ∈ (s j P).boxes, ∀ Q ∈ pastPieces s (j+1) k [(s j P).rest B],
      (decompositionCost Q.graph:ℝ) ≤ c*Q.vertices.card)
    (hq : ∀ B ∈ (s j P).boxes,
      (decompositionCost (graphUnion ((advance s (j+1) k [(s j P).rest B]).map AssignedPiece.graph ++
        ((s j P).pieces B).map AssignedPiece.graph)):ℝ) ≤
      c*vertexMass ((s j P).pieces B) + α*vertexMass (advance s (j+1) k [(s j P).rest B]) +
      β*vertexMass ((s j P).pieces B) + γ*B.vertices.card) :
    (decompositionCost P.graph:ℝ) ≤ ((pastCycles s j (k+1) [P]).length:ℝ) +
      c*vertexMass (pastPieces s j (k+1) [P]) + α*vertexMass (advance s j (k+1) [P]) +
      β*vertexMass (levelPieces s j [P]) + γ*vertexMass (nextLayer s j [P]) := by
  have hb (B) (hB : B ∈ (s j P).boxes) := box_cost_regroup ((s j P).pieces B)
    (R := (s j P).rest B) (by simpa only [StageSplit.rest_graph _ hB] using (s j P).box_partition B hB)
    s (j+1) k c _ (hp B hB) (hq B hB)
  have hh := (stage_cost s j P).trans (add_le_add (le_refl _) (costMass_bound _ _ hb))
  have hc := (pastCycles_after_first s j k P).length_eq
  have hm := vertexMass_perm (pastPieces_after_first s j k P)
  rw [hc,List.length_append,Nat.cast_add,List.length_flatMap,hm,vertexMass_append,
    vertexMass_flatMap,vertexMass_flatMap,advance_after_first,vertexMass_flatMap]
  simp only [levelPieces,nextLayer,List.flatMap_singleton,StageSplit.children_mass,vertexMass_flatMap]
  simp only [List.sum_map_add,List.sum_map_mul_left] at hh
  simp only [Nat.cast_list_sum,List.map_map,Function.comp_def,vertexMass] at hh ⊢
  linarith

lemma selected_prefix_cost (s : SplitSystem V) (i k) (P : AssignedPiece V) (c α β γ : ℝ)
    (hp : ∀ Q ∈ pastPieces s 0 (i+(k+1)) [P], (decompositionCost Q.graph:ℝ) ≤ c*Q.vertices.card)
    (hq : ∀ Q ∈ advance s 0 i [P], ∀ B ∈ (s i Q).boxes,
      (decompositionCost (graphUnion ((advance s (i+1) k [(s i Q).rest B]).map AssignedPiece.graph ++
        ((s i Q).pieces B).map AssignedPiece.graph)):ℝ) ≤
      c*vertexMass ((s i Q).pieces B) + α*vertexMass (advance s (i+1) k [(s i Q).rest B]) +
      β*vertexMass ((s i Q).pieces B) + γ*B.vertices.card) :
    (decompositionCost P.graph:ℝ) ≤ ((pastCycles s 0 (i+(k+1)) [P]).length:ℝ) +
      c*vertexMass (pastPieces s 0 (i+(k+1)) [P]) + α*vertexMass (advance s 0 (i+(k+1)) [P]) +
      β*vertexMass (levelPieces s i (advance s 0 i [P])) + γ*vertexMass (advance s 0 (i+1) [P]) := by
  have he : pastPieces s 0 (i+(k+1)) [P] = pastPieces s 0 i [P] ++
      pastPieces s i (k+1) (advance s 0 i [P]) := by rw [pastPieces_add,Nat.zero_add]
  have hp₀ : ∀ Q ∈ pastPieces s 0 i [P], (decompositionCost Q.graph:ℝ) ≤ c*Q.vertices.card := by
    intro Q hQ; apply hp; rw [he]; exact List.mem_append_left _ hQ
  have hpp (Q) (hQ : Q ∈ advance s 0 i [P]) (B) (hB : B ∈ (s i Q).boxes)
      (R) (hR : R ∈ pastPieces s (i+1) k [(s i Q).rest B]) :
      (decompositionCost R.graph:ℝ) ≤ c*R.vertices.card := by
    apply hp R
    rw [he,List.mem_append]
    right
    have h₁ := pastPieces_flatMap s i (k+1) (advance s 0 i [P]) (fun Q => [Q])
    simp only [List.flatMap_singleton'] at h₁
    rw [h₁.mem_iff]
    apply List.mem_flatMap.mpr
    refine ⟨Q,hQ,?_⟩
    rw [(pastPieces_after_first s i k Q).mem_iff,List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨B,hB,hR⟩)
  have hh := (past_cost s 0 i P c hp₀).trans (add_le_add (le_refl _)
    (costMass_bound _ _ (fun Q hQ => selected_input_cost s i k Q c α β γ (hpp Q hQ) (hq Q hQ))))
  rw [pastCycles_add,pastPieces_add,advance_add,Nat.zero_add,List.length_append,Nat.cast_add,vertexMass_append]
  simp only [List.sum_map_add,List.sum_map_mul_left,pastCycles_sum,pastPieces_sum,advance_sum] at hh
  have hS : ((advance s 0 i [P]).map (fun Q => vertexMass (levelPieces s i [Q]))).sum =
      vertexMass (levelPieces s i (advance s 0 i [P])) := by
    simp only [levelPieces,List.flatMap_singleton,vertexMass_flatMap]
  have hN : ((advance s 0 i [P]).map (fun Q => vertexMass (nextLayer s i [Q]))).sum =
      vertexMass (advance s 0 (i+1) [P]) := by
    simp only [nextLayer,List.flatMap_singleton,advance_succ,Nat.zero_add,vertexMass_flatMap]
  rw [hS,hN] at hh
  linarith

end
end ErdosGallai.Scale

end
end

/-! ### Upstream module `Combinatorics/CycleDecomposition/UniformLayers.lean` -/

section
open _root_.Filter _root_.Asymptotics _root_.Real
noncomputable section
open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Finset
namespace ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

structure Layers (P : AssignedPiece V) (Dstar : ℝ) where
  system : SplitSystem V
  count : ℕ
  positive : 0 < count
  cutoff : ∀ j < count, Dstar ≤ inductionScale P.vertices.card j
  last_lt : inductionScale P.vertices.card count < Dstar
  bounded : ∀ j < count, ∀ Q ∈ advance system 0 j [P],
    (system j Q).Bounded (inductionScale P.vertices.card j)
  degree : ∀ j ≤ count, ∀ Q ∈ advance system 0 j [P],
    2*(edgeCount Q.graph:ℝ)/Q.vertices.card ≤ inductionScale P.vertices.card j

theorem uniform_layers : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ Dstar ≥ D₀,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (P : AssignedPiece V),
    Dstar ≤ (P.vertices.card:ℝ) → 2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ P.vertices.card →
    Nonempty (Layers P Dstar) := by
  obtain ⟨Dsp,hsp⟩ := scale_splitter
  refine ⟨max Dsp 2,lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) (le_max_right _ _),?_⟩
  intro Dstar hD V _ _ P hn hdeg
  have hD1 : 1 < Dstar := lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) ((le_max_right _ _).trans hD)
  have hn1 : 1 < (P.vertices.card:ℝ) := hD1.trans_le hn
  have hne : P.vertices.Nonempty := Finset.card_pos.mp (by exact_mod_cast (by linarith : (0:ℝ) < P.vertices.card))
  obtain ⟨split,hsplit⟩ := hsp V
  let s : SplitSystem V := fun j Q => split (inductionScale P.vertices.card j) Q
  have hs : ∀ j Q, Dstar ≤ inductionScale P.vertices.card j → Q.vertices.Nonempty →
      2*(edgeCount Q.graph:ℝ)/Q.vertices.card ≤ inductionScale P.vertices.card j →
      (s j Q).Bounded (inductionScale P.vertices.card j) := by
    intro j Q hj hQ hd
    exact hsplit _ ((le_max_left _ _).trans (hD.trans hj)) Q hQ hd
  obtain ⟨m,hm,hlast,hcut⟩ := inductionScale_first_cutoff P.vertices.card Dstar hD1 hn
  have hL : ∀ Q ∈ [P], Q.vertices.Nonempty := by simpa using hne
  have hLd : ∀ Q ∈ [P], 2*(edgeCount Q.graph:ℝ)/Q.vertices.card ≤ inductionScale P.vertices.card 0 := by
    simpa only [List.mem_singleton,forall_eq,inductionScale_zero] using hdeg
  refine ⟨{ system := s, count := m, positive := hm, cutoff := hcut, last_lt := hlast, bounded := ?_, degree := ?_ }⟩
  · intro j hj
    simpa only [Nat.zero_add] using advance_bounded s P.vertices.card Dstar (Nat.cast_nonneg _) hs
      0 j [P] hL hLd (fun l _ hl => hcut l (by omega))
  · intro j hj
    simpa only [Nat.zero_add] using advance_valid s P.vertices.card Dstar (Nat.cast_nonneg _) hs
      0 j [P] hL hLd (fun l _ hl => hcut l (by omega))

variable {P : AssignedPiece V} {Dstar : ℝ}

abbrev Layers.frontier (H : Layers P Dstar) (j : ℕ) := advance H.system 0 j [P]
abbrev Layers.scale (_H : Layers P Dstar) (j : ℕ) := inductionScale (P.vertices.card:ℝ) j
abbrev Layers.mass (H : Layers P Dstar) (j : ℕ) := vertexMass (H.frontier j)
abbrev Layers.pieceMass (H : Layers P Dstar) (j : ℕ) := vertexMass (levelPieces H.system j (H.frontier j))

lemma Layers.mass_lower (H : Layers P Dstar) (j) : (P.vertices.card:ℝ) ≤ H.mass j :=
  advance_mass_lower H.system 0 j P

lemma Layers.mass_upper (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hlog : ∀ j < H.count, 80 ≤ logb 2 (H.scale j)) (j) (hj : j < H.count) :
    H.mass (j+1) ≤ (1+80/logb 2 (H.scale j))*P.vertices.card := by
  have hh := advance_mass_global_product H.system P.vertices.card hn 0 (j+1) [P]
    (fun l hl => by simpa only [Nat.zero_add] using H.bounded l (by omega))
  have hx := scale_overlap_product P.vertices.card 2 hn (by norm_num) j (by norm_num; exact hlog j hj)
  simp only [Nat.zero_add,vertexMass_cons,vertexMass_nil,add_zero] at hh
  have hx' := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg P.vertices.card : (0:ℝ) ≤ _)
  norm_num only [show (40:ℝ)*2=80 by norm_num] at hx'
  dsimp only [Layers.mass,Layers.frontier,Layers.scale] at *
  nlinarith

lemma Layers.mass_two (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hlog : ∀ j < H.count, 80 ≤ logb 2 (H.scale j)) (k) (hk : k ≤ H.count) :
    H.mass k ≤ 2*P.vertices.card := by
  cases k with
  | zero => simp only [Layers.mass,Layers.frontier,advance_zero,vertexMass_cons,vertexMass_nil,add_zero]; nlinarith [(Nat.cast_nonneg P.vertices.card : (0:ℝ) ≤ _)]
  | succ j =>
    have hj : j < H.count := by omega
    have hh := H.mass_upper hn hlog j hj
    have hl := hlog j hj
    have hd : 80/logb 2 (H.scale j) ≤ 1 := (div_le_one (by linarith)).mpr hl
    have hc : (0:ℝ) ≤ P.vertices.card := Nat.cast_nonneg _
    nlinarith

lemma Layers.pieceMass_two (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hlog : ∀ j < H.count, 80 ≤ logb 2 (H.scale j)) (j) (hj : j < H.count) :
    H.pieceMass j ≤ 2*P.vertices.card :=
  (levelPieces_mass H.system j (H.frontier j)).trans (by
    simpa only [Layers.mass,Layers.frontier,advance_succ,Nat.zero_add] using H.mass_two hn hlog (j+1) (by omega))

lemma Layers.cycles_bound (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hready : ∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) (j) (hj : j < H.count) :
    ((pastCycles H.system 0 (j+1) [P]).length:ℝ) ≤ 20*P.vertices.card/logb 2 (H.scale j) := by
  rw [pastCycles_length]
  apply (Finset.sum_le_sum (fun l hl => ?_)).trans
    (scale_prefix_cycle_cost P.vertices.card hn j (fun l => H.mass l)
      (fun l hl => H.mass_two hn (fun a ha => (hready a ha).log_large) l (by have := Finset.mem_range.mp hl; omega))
      (fun l hl => (hready l (by have := Finset.mem_range.mp hl; omega)).cycle_power))
  simpa only [Nat.zero_add] using levelCycles_length H.system l (H.frontier l) (H.scale l)
    (H.bounded l (by have := Finset.mem_range.mp hl; omega))

lemma Layers.subset (H : Layers P Dstar) (j) : ∀ Q ∈ H.frontier j, Q.vertices ⊆ P.vertices :=
  advance_subset H.system 0 j [P] P.vertices (by simp)

lemma Layers.box_subset (H : Layers P Dstar) (j) {Q B : AssignedPiece V}
    (hQ : Q ∈ H.frontier j) (hB : B ∈ (H.system j Q).boxes) : B.vertices ⊆ P.vertices :=
  ((H.system j Q).box_subset B hB).trans (H.subset j Q hQ)

lemma Layers.boundary_order (H : Layers P Dstar) (j) (hj : j < H.count)
    {Q : AssignedPiece V} (hQ : Q ∈ H.frontier (j+1)) :
    (Q.vertices.card:ℝ) ≤ (H.scale j)^(51/50:ℝ) := by
  simp only [Layers.frontier,advance_succ,Nat.zero_add] at hQ
  obtain ⟨T,hT,B,hB,hv,_⟩ := (nextLayer_mem H.system j _ Q).mp hQ
  rw [hv]
  exact (H.bounded j hj T hT).2.2.1 B hB

lemma Layers.local_mass (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hlog : ∀ j < H.count, 80 ≤ logb 2 (H.scale j)) (i k)
    (hik : i+k < H.count) {Q B : AssignedPiece V}
    (hQ : Q ∈ H.frontier i) (hB : B ∈ (H.system i Q).boxes) :
    vertexMass (advance H.system (i+1) k [(H.system i Q).rest B]) ≤
      (1+80/logb 2 (H.scale (i+k)))*B.vertices.card := by
  have hh := advance_mass_global_product H.system P.vertices.card hn (i+1) k [(H.system i Q).rest B]
    (fun l hl R hR => by
      have hr := advance_local_mem H.system i l [P] hQ hB R hR
      have he : i+1+l = (i+l)+1 := by omega
      exact H.bounded (i+1+l) (by omega) R hr)
  have hx := scale_overlap_product P.vertices.card 2 hn (by norm_num) (i+k)
    (by norm_num; exact hlog (i+k) hik)
  simp only [vertexMass_cons,vertexMass_nil,add_zero,StageSplit.rest_vertices] at hh
  rw [show i+1+k=(i+k)+1 by omega] at hh
  have hx' := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg B.vertices.card : (0:ℝ) ≤ _)
  norm_num only [show (40:ℝ)*2=80 by norm_num] at hx'
  dsimp only [Layers.scale] at *
  nlinarith

lemma Layers.local_mass_two (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hlog : ∀ j < H.count, 80 ≤ logb 2 (H.scale j)) (i k)
    (hik : i+k < H.count) {Q B : AssignedPiece V}
    (hQ : Q ∈ H.frontier i) (hB : B ∈ (H.system i Q).boxes) :
    vertexMass (advance H.system (i+1) k [(H.system i Q).rest B]) ≤ 2*B.vertices.card := by
  have hh := H.local_mass hn hlog i k hik hQ hB
  have hl := hlog (i+k) hik
  have hd : 80/logb 2 (H.scale (i+k)) ≤ 1 := (div_le_one (by linarith)).mpr hl
  have hc : (0:ℝ) ≤ B.vertices.card := Nat.cast_nonneg _
  nlinarith

lemma Layers.gap_order (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ)) (i)
    (hik : i+200 < H.count) {Q B R : AssignedPiece V}
    (hQ : Q ∈ H.frontier i) (hB : B ∈ (H.system i Q).boxes)
    (hR : R ∈ advance H.system (i+1) 200 [(H.system i Q).rest B]) :
    (R.vertices.card:ℝ) ≤ (H.scale i)^(1/1000:ℝ) ∧
      2*(edgeCount R.graph:ℝ)/R.vertices.card ≤ (H.scale i)^(1/1000:ℝ) := by
  have hr := advance_local_mem H.system i 200 [P] hQ hB R hR
  have hr' : R ∈ H.frontier ((i+200)+1) := by convert hr using 1
  have hd : 1 < H.scale i := inductionScale_gt_one P.vertices.card hn i
  constructor
  · have hh := H.boundary_order (i+200) hik hr'
    apply hh.trans
    dsimp only [Layers.scale]
    rw [inductionScale_add _ (by positivity),← Real.rpow_mul (by linarith : 0 ≤ inductionScale P.vertices.card i)]
    apply Real.rpow_le_rpow_of_exponent_le hd.le
    nlinarith [inductionScale_window.1]
  · have hh := H.degree ((i+200)+1) (by omega) R hr'
    apply hh.trans
    rw [show i+200+1=i+201 by omega]
    dsimp only [Layers.scale]
    rw [inductionScale_add _ (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hd.le inductionScale_window.2.le

end
end ErdosGallai.Scale

namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable

lemma disjoint_subset_mass {V A : Type} [Fintype A] [DecidableEq V]
    (U : A → Finset V) (Y : Finset V) (hd : Pairwise fun r s => Disjoint (U r) (U s))
    (hu : ∀ r, U r ⊆ Y) : (∑ r, ((U r).card:ℝ)) ≤ Y.card := by
  have hc : (univ.biUnion U).card = ∑ r, (U r).card := Finset.card_biUnion (fun i _ j _ hij => hd hij)
  have hs : univ.biUnion U ⊆ Y := by
    intro v hv
    obtain ⟨r,_,hv⟩ := Finset.mem_biUnion.mp hv
    exact hu r hv
  have hh := Finset.card_le_card hs
  rw [hc] at hh
  exact_mod_cast hh

theorem uniform_box_cost : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, ∀ wmin : ℝ,
    MainScaleReady wmin D →
    ∀ (V A : Type) [Fintype V] [Fintype A],
    ∀ (G F : SimpleGraph V) (R : A → SimpleGraph V) (U : A → Finset V) (Y : Finset V),
    F ≤ G → (∀ r, R r ≤ G) →
    Pairwise (fun r s => Disjoint (R r).edgeSet (R s).edgeSet) →
    Pairwise (fun r s => Disjoint (U r) (U s)) →
    (∀ r, U r ⊆ Y) →
    (∀ r, ∀ ⦃x y⦄, (R r).Adj x y → x ∈ U r ∧ y ∈ U r) →
    (∀ r, Disjoint F.edgeSet (R r).edgeSet) →
    F.edgeSet ∪ (⋃ r, (R r).edgeSet) = G.edgeSet →
    (∀ r, Batch.CutExpansionOn (R r) (U r) (D^(9/10:ℝ))) →
    (∀ r, D^(9/10:ℝ) ≤ ((U r).card:ℝ) ∧ ((U r).card:ℝ) ≤ D^(51/50:ℝ)) →
    ((Y.card:ℝ) ≤ D^(51/50:ℝ)) →
    2*(F.edgeFinset.card:ℝ) ≤ 2*Y.card*D^(1/1000:ℝ) →
    ∀ T : ℝ, T ≤ 2*Y.card →
    ∀ _b : Indexing.GraphBatches F Y (D^(3/10:ℝ)) T,
    ∀ (n : ℕ) (C t : ℝ), 0 ≤ C → 0 ≤ t → Y.card ≤ n → D^(3/10:ℝ) < n →
    (∀ (Q : Type) [Fintype Q] (H : SimpleGraph Q), Fintype.card Q < n →
      (decompositionCost H:ℝ) ≤ C*Fintype.card Q) →
    (∀ (Q : Type) [Fintype Q] (H : SimpleGraph Q), Fintype.card Q < n →
      (Fintype.card Q:ℝ) ≤ D^(3/10:ℝ) → (Batch.decompositionCost H:ℝ) ≤ t*Fintype.card Q) →
    (Batch.decompositionCost G:ℝ) ≤
      t*(T-(∑ r, ((U r).card:ℝ))/3+(2/3)*Y.card/logb 2 D) +
      8*((∑ r, ((U r).card:ℝ))+T-Y.card) + (9+C*mainEta)*(∑ r, ((U r).card:ℝ)) := by
  obtain ⟨D₁,hD₁,hresolve⟩ := Batch.uniform_coupled_resolution_cost
  obtain ⟨D₂,hD₂,hpiece⟩ := uniform_piece_cost_on (1/4) mainEta (by norm_num) mainEta_pos
  refine ⟨max D₁ D₂,lt_of_lt_of_le hD₁ (le_max_left _ _),?_⟩
  intro D hD wmin hready V A _ _ G F R U Y hFG hRG hRR hUU hUY hRU hFR hcov hexp horder
    hY hF T hT b n C t hC ht hYn hsmall ih ihq
  have hD0 : 0 < D := by linarith [hready.gt_one]
  have ha : 1 ≤ D^(1/100:ℝ) := Real.one_le_rpow hready.gt_one.le (by norm_num)
  obtain ⟨a⟩ := Indexing.choose_active_family F Y b.vertices U (D^(1/100:ℝ)) (D^(3/100:ℝ))
    (Real.rpow_nonneg hD0.le _) b.subset hUY b.vertex_cover hUU
  let := a.finite
  have h8 (j) (i : a.Index j) : 8 ≤ (a.vertices j i).card := by
    have hh := hready.active_eight.trans (a.large j i)
    exact_mod_cast hh
  have hsquare (j) (i : a.Index j) : (D^(1/100:ℝ))^2 ≤ (a.vertices j i).card :=
    hready.active_square.trans (a.large j i)
  have hn (j) : (b.vertices j).card < n := by
    exact_mod_cast (b.order_le j).trans_lt hsmall
  obtain ⟨H,hHR,hHexp,hcost⟩ := hresolve D ((le_max_left _ _).trans hD) V A b.Index G F R U
    hFG hRG hRR hUU hRU hFR hcov hexp horder b.graph b.vertices b.graph_le b.disjoint b.edge_cover
    b.supported b.order_le a.Index a.vertices a.disjoint a.subset_batch a.router a.subset_router
    a.degree_le ha h8 hsquare n t ht hn ihq
  have hp (r : A) : (Batch.decompositionCost (H r):ℝ) ≤ (9+C*mainEta)*(U r).card := by
    have hh := hpiece D ((le_max_right _ _).trans hD) n C hC ih V (H r) (H r) (U r) le_rfl
      ((Finset.card_le_card (hUY r)).trans hYn) (fun x y h => hRU r (hHR r h)) (horder r).1 (horder r).2
      (by

        simpa only [CutExpansionOn,Batch.CutExpansionOn,show (1/4:ℝ)*D^(9/10:ℝ) = D^(9/10:ℝ)/4 by ring] using hHexp r)
    exact hh
  have hpsum : (∑ r, (Batch.decompositionCost (H r):ℝ)) ≤ (9+C*mainEta)*(∑ r, ((U r).card:ℝ)) := by
    simpa only [Finset.mul_sum] using Finset.sum_le_sum (s := univ) (fun r _ => hp r)
  have hbad : ((Y \ Indexing.goodVertices F Y (D^(1/100:ℝ))).card:ℝ) ≤ Y.card/logb 2 D :=
    hready.bad_count (Nat.cast_nonneg _) ((Indexing.bad_vertices_degree_bound F Y (D^(1/100:ℝ))).trans hF)
  have hrcount : D^(9/10:ℝ)*(Fintype.card A:ℝ) ≤ Y.card := by
    calc
      _ = ∑ _r : A, D^(9/10:ℝ) := by simp [mul_comm]
      _ ≤ ∑ r, ((U r).card:ℝ) := Finset.sum_le_sum (fun r _ => (horder r).1)
      _ ≤ _ := disjoint_subset_mass U Y hUU hUY
  have hskip := hready.skip_count (Nat.cast_nonneg Y.card) (Nat.cast_nonneg (Fintype.card b.Index))
    (Nat.cast_nonneg (Fintype.card A)) hY hT b.count_le hrcount
  have hlow : (∑ r, ((U r).card:ℝ))-2*Y.card/logb 2 D ≤ ∑ j, ∑ i, ((a.vertices j i).card:ℝ) := by
    have hh := a.lower
    simp only [div_eq_mul_inv] at hbad hskip hh ⊢
    linarith only [hh,hbad,hskip]
  have hhigh : (∑ j, ∑ i, ((a.vertices j i).card:ℝ)) ≤ (∑ r, ((U r).card:ℝ))+T-Y.card := by
    have hh := a.upper
    have hm := b.mass_le
    linarith
  have hhalf : (∑ j, ∑ i, ((a.vertices j i).card:ℝ))/3 ≤
      ∑ j, ∑ i, (((a.vertices j i).card / 2:ℕ):ℝ) := by
    simp only [Finset.sum_div]
    apply Finset.sum_le_sum; intro j _
    apply Finset.sum_le_sum; intro i _
    exact Indexing.thirds_le_halves (h8 j i)
  have hq : (∑ j, ((b.vertices j).card:ℝ)) - ∑ j, ∑ i, (((a.vertices j i).card / 2:ℕ):ℝ) ≤
      T-(∑ r, ((U r).card:ℝ))/3+(2/3)*Y.card/logb 2 D := by
    have hm := b.mass_le
    simp only [div_eq_mul_inv] at hm hlow hhalf ⊢
    linarith only [hm,hlow,hhalf]
  have hqm := mul_le_mul_of_nonneg_left hq ht
  push_cast at hcost
  linarith

end
end ErdosGallai

end
end

/-! ### Upstream module `Combinatorics/CycleDecomposition/LayerCosts.lean` -/

section
open _root_.Filter _root_.Asymptotics _root_.Real
noncomputable section
open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Finset
namespace ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma assigned_union_edges (L : List (AssignedPiece V)) :
    (⋃ i : Fin L.length, (L.get i).graph.edgeSet) = (graphUnion (L.map AssignedPiece.graph)).edgeSet := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Set.mem_iUnion,SimpleGraph.mem_edgeSet]

    rw [graphUnion_adj]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨_,List.mem_map.mpr ⟨_,L.get_mem i,rfl⟩,hi⟩
    · rintro ⟨G,hG,hxy⟩
      obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hG
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hQ
      exact ⟨i,hxy⟩

lemma box_coupled_partition {B R : AssignedPiece V} (A : List (AssignedPiece V))
    (hBR : GraphPartition B.graph (R.graph :: A.map AssignedPiece.graph))
    (s : SplitSystem V) (j k : ℕ) :
    GraphPartition (graphUnion ((advance s j k [R]).map AssignedPiece.graph ++ A.map AssignedPiece.graph))
      ((advance s j k [R]).map AssignedPiece.graph ++ A.map AssignedPiece.graph) := by
  apply graphPartition_of_le_one
  intro x y
  have hb := hBR x y
  have hr := past_partition s j k R x y
  simp only [edgeOccurrences_cons,edgeOccurrences_append] at hb hr ⊢
  split_ifs at hb hr <;> omega

theorem uniform_local_box_cost : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, ∀ wmin : ℝ,
    ErdosGallai.MainScaleReady wmin D →
    ∀ (V : Type) [Fintype V] (L A : List (AssignedPiece V)) (Y : Finset V),
    GraphPartition (graphUnion (L.map AssignedPiece.graph ++ A.map AssignedPiece.graph))
      (L.map AssignedPiece.graph ++ A.map AssignedPiece.graph) →
    A.Pairwise (fun R S => Disjoint R.vertices S.vertices) →
    (∀ R ∈ A, R.vertices ⊆ Y) →
    (∀ Q ∈ L, Q.vertices ⊆ Y) →
    (∀ v ∈ Y, ∃ Q ∈ L, v ∈ Q.vertices) →
    (∀ Q ∈ L, Q.vertices.Nonempty ∧ (Q.vertices.card:ℝ) ≤ D^(1/1000:ℝ) ∧
      2*(edgeCount Q.graph:ℝ)/Q.vertices.card ≤ D^(1/1000:ℝ)) →
    (∀ R ∈ A, D^(9/10:ℝ) ≤ (R.vertices.card:ℝ) ∧ (R.vertices.card:ℝ) ≤ D^(51/50:ℝ) ∧
      CutExpansionOn R.graph R.vertices (D^(9/10:ℝ))) →
    (Y.card:ℝ) ≤ D^(51/50:ℝ) → vertexMass L ≤ 2*Y.card →
    ∀ (n : ℕ) (C t : ℝ), 0 ≤ C → 0 ≤ t → Y.card ≤ n → D^(3/10:ℝ) < n →
    (∀ (Q : Type) [Fintype Q] (H : SimpleGraph Q), Fintype.card Q < n →
      (ErdosGallai.decompositionCost H:ℝ) ≤ C*Fintype.card Q) →
    (∀ (Q : Type) [Fintype Q] (H : SimpleGraph Q), Fintype.card Q < n →
      (Fintype.card Q:ℝ) ≤ D^(3/10:ℝ) → (Batch.decompositionCost H:ℝ) ≤ t*Fintype.card Q) →
    (decompositionCost (graphUnion (L.map AssignedPiece.graph ++ A.map AssignedPiece.graph)):ℝ) ≤
      (9+C*ErdosGallai.mainEta)*vertexMass A + (t+8)*vertexMass L +
      (8-t/3)*vertexMass A + ((2/3)*t/logb 2 D-8)*Y.card := by
  obtain ⟨D₀,hD₀,hbox⟩ := ErdosGallai.uniform_box_cost
  refine ⟨D₀,hD₀,?_⟩
  intro D hD wmin hready V _ L A Y hpart hAd hAY hLY hcover hL hA hY hmass
    n C t hC ht hYn hsmall ih ihq
  let F := graphUnion (L.map AssignedPiece.graph)
  let G := graphUnion (L.map AssignedPiece.graph ++ A.map AssignedPiece.graph)
  let R (r : Fin A.length) := (A.get r).graph
  let U (r : Fin A.length) := (A.get r).vertices
  have hp := List.pairwise_append.mp (graphPartition_pairwise hpart)
  have hLL := list_pairwise_get (List.pairwise_map.mp hp.1) (fun _ _ h => h.symm)
  have hRR : Pairwise (fun r s => Disjoint (R r).edgeSet (R s).edgeSet) :=
    list_pairwise_get (List.pairwise_map.mp hp.2.1) (fun _ _ h => h.symm)
  have hUU : Pairwise (fun r s => Disjoint (U r) (U s)) :=
    list_pairwise_get hAd (fun _ _ h => h.symm)
  have hFR (r) : Disjoint F.edgeSet (R r).edgeSet := by
    rw [← assigned_union_edges]
    exact Set.disjoint_iUnion_left.mpr (fun i => hp.2.2 _ (List.mem_map.mpr ⟨_,L.get_mem i,rfl⟩)
      _ (List.mem_map.mpr ⟨_,A.get_mem r,rfl⟩))
  have hFG : F ≤ G := graphUnion_sublist (List.sublist_append_left _ _)
  have hRG (r) : R r ≤ G := by
    intro x y hxy
    exact (graphUnion_adj _ _ _).mpr ⟨_,List.mem_append_right _ (List.mem_map.mpr ⟨_,A.get_mem r,rfl⟩),hxy⟩
  have hcov : F.edgeSet ∪ (⋃ r, (R r).edgeSet) = G.edgeSet := by
    change F.edgeSet ∪ (⋃ r : Fin A.length, (A.get r).graph.edgeSet) = _
    rw [assigned_union_edges]
    ext e
    induction e using Sym2.ind with
    | _ x y => simp only [Set.mem_union,SimpleGraph.mem_edgeSet,G,graphUnion_append,SimpleGraph.sup_adj,F]
  have hB : 0 < D^(3/10:ℝ) := Real.rpow_pos_of_pos (by linarith [hready.gt_one]) _
  obtain ⟨b⟩ := Indexing.materialize_batches F Y (fun i : Fin L.length => (L.get i).graph)
    (fun i => (L.get i).vertices) hLL (assigned_union_edges L)
    (fun i x y hxy => (L.get i).supported hxy) (fun i => hLY _ (L.get_mem i))
    (by
      intro v hv
      obtain ⟨Q,hQ,hvQ⟩ := hcover v hv
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hQ
      exact Finset.mem_biUnion.mpr ⟨i,mem_univ _,hvQ⟩)
    (D^(3/10:ℝ)) hB (fun i => ((hL _ (L.get_mem i)).2.1).trans hready.batch_power)
  have hsum : (∑ i : Fin L.length, ((L.get i).vertices.card:ℝ)) = vertexMass L := list_sum_get L (fun Q => (Q.vertices.card:ℝ))
  have hAsum : (∑ i : Fin A.length, ((U i).card:ℝ)) = vertexMass A := list_sum_get A (fun Q => (Q.vertices.card:ℝ))
  have hF : 2*(F.edgeFinset.card:ℝ) ≤ 2*Y.card*D^(1/1000:ℝ) := by
    have hh := (Nat.cast_le.mpr (edgeCount_union_le (L.map AssignedPiece.graph)) : (_:ℝ) ≤ _)
    have hdeg : (L.map (fun Q => 2*(edgeCount Q.graph:ℝ))).sum ≤ vertexMass L * D^(1/1000:ℝ) := by
      unfold vertexMass
      rw [← List.sum_map_mul_right]
      apply List.sum_le_sum
      intro Q hQ
      have hc : (0:ℝ) < Q.vertices.card := by exact_mod_cast Finset.card_pos.mpr (hL Q hQ).1
      simpa only [mul_comm] using (div_le_iff₀ hc).mp (hL Q hQ).2.2
    simp only [Nat.cast_list_sum,List.map_map,Function.comp_def] at hh
    rw [List.sum_map_mul_left] at hdeg
    have hx := mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg (show (0:ℝ) ≤ D by linarith [hready.gt_one]) (1/1000:ℝ))
    change 2*(edgeCount F:ℝ) ≤ _
    linarith
  have hcost := hbox D hD wmin hready V (Fin A.length) G F R U Y hFG hRG hRR hUU
    (fun r => hAY _ (A.get_mem r)) (fun r x y hxy => (A.get r).supported hxy) hFR hcov
    (fun r => (hA _ (A.get_mem r)).2.2)
    (fun r => ⟨(hA _ (A.get_mem r)).1,(hA _ (A.get_mem r)).2.1⟩)
    hY hF (∑ i : Fin L.length, ((L.get i).vertices.card:ℝ)) (by simpa only [hsum] using hmass)
    b n C t hC ht hYn hsmall ih ihq
  rw [hsum,hAsum] at hcost
  change (decompositionCost G:ℝ) ≤ _
  convert hcost using 1 <;> first | rfl | ring

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma pastPieces_mem (s : SplitSystem V) (j k : ℕ) (L : List (AssignedPiece V))
    {R : AssignedPiece V} (hR : R ∈ pastPieces s j k L) :
    ∃ l < k, R ∈ levelPieces s (j+l) (advance s j l L) := by
  induction k with
  | zero => simp [pastPieces] at hR
  | succ k ih =>
    rcases List.mem_append.mp hR with h | h
    · obtain ⟨l,hl,hR⟩ := ih h
      exact ⟨l,by omega,hR⟩
    · exact ⟨k,by omega,h⟩

theorem uniform_committed_piece_cost : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ Dstar ≥ D₀,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (P : AssignedPiece V) (H : Layers P Dstar),
    ∀ (C : ℝ), 0 ≤ C →
    (∀ (Q : Type) [Fintype Q] (G : SimpleGraph Q), Fintype.card Q < P.vertices.card →
      (ErdosGallai.decompositionCost G:ℝ) ≤ C*Fintype.card Q) →
    ∀ k ≤ H.count, ∀ R ∈ pastPieces H.system 0 k [P],
      (decompositionCost R.graph:ℝ) ≤ (9+C*ErdosGallai.mainEta)*R.vertices.card := by
  obtain ⟨D₀,hD₀,hpc⟩ := ErdosGallai.uniform_piece_cost_on 1 ErdosGallai.mainEta (by norm_num) ErdosGallai.mainEta_pos
  refine ⟨D₀,hD₀,?_⟩
  intro Dstar hD V _ _ P H C hC ih k hk R hR
  obtain ⟨j,hjk,hR⟩ := pastPieces_mem H.system 0 k [P] hR
  simp only [Nat.zero_add] at hR
  obtain ⟨Q,hQ,B,hB,hR⟩ := (by simpa [levelPieces,List.mem_flatMap] using hR :
    ∃ Q ∈ H.frontier j, ∃ B ∈ (H.system j Q).boxes, R ∈ (H.system j Q).pieces B)
  have hj : j < H.count := by omega
  have hb := (H.bounded j hj Q hQ).2.2.2.1 B hB R hR
  have hsub := ((H.system j Q).piece_subset B hB R hR).trans (H.box_subset j hQ hB)
  exact hpc (H.scale j) (hD.trans (H.cutoff j hj)) P.vertices.card C hC ih V R.graph R.graph R.vertices
    le_rfl (Finset.card_le_card hsub) R.supported hb.1 hb.2.1 (by
      simpa only [one_mul,ErdosGallai.CutExpansionOn,CutExpansionOn,cutCount,Layers.scale] using hb.2.2)

theorem uniform_gap_prefix_cost : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ Dstar ≥ D₀,
    ∀ (V : Type) [Fintype V] (P : AssignedPiece V) (H : Layers P Dstar),
    1 < (P.vertices.card:ℝ) →
    (∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) →
    ∀ i, i+200 < H.count → ∀ C t : ℝ, 0 ≤ C → 0 ≤ t →
    (∀ (Q : Type) [Fintype Q] (G : SimpleGraph Q), Fintype.card Q < P.vertices.card →
      (ErdosGallai.decompositionCost G:ℝ) ≤ C*Fintype.card Q) →
    (∀ (Q : Type) [Fintype Q] (G : SimpleGraph Q), Fintype.card Q < P.vertices.card →
      (Fintype.card Q:ℝ) ≤ (H.scale i)^(3/10:ℝ) →
      (Batch.decompositionCost G:ℝ) ≤ t*Fintype.card Q) →
    (∀ R ∈ pastPieces H.system 0 (i+201) [P],
      (decompositionCost R.graph:ℝ) ≤ (9+C*ErdosGallai.mainEta)*R.vertices.card) →
    (decompositionCost P.graph:ℝ) ≤ ((pastCycles H.system 0 (i+201) [P]).length:ℝ) +
      (9+C*ErdosGallai.mainEta)*vertexMass (pastPieces H.system 0 (i+201) [P]) +
      (t+8)*H.mass (i+201) + (8-t/3)*H.pieceMass i +
      ((2/3)*t/logb 2 (H.scale i)-8)*H.mass (i+1) := by
  obtain ⟨D₀,hD₀,hlocal⟩ := uniform_local_box_cost
  refine ⟨D₀,hD₀,?_⟩
  intro Dstar hD V _ P H hn hready i hik C t hC ht ih ihq hp
  have hi : i < H.count := by omega
  have hne : P.vertices.Nonempty := Finset.card_pos.mp (by exact_mod_cast (by linarith : (0:ℝ) < P.vertices.card))
  have hsmall : (H.scale i)^(3/10:ℝ) < (P.vertices.card:ℝ) := by
    apply lt_of_lt_of_le _ (inductionScale_le P.vertices.card hn.le i)
    have hd := inductionScale_gt_one P.vertices.card hn i
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hd (by norm_num : (3/10:ℝ) < 1)
  apply selected_prefix_cost H.system i 200 P (9+C*ErdosGallai.mainEta)
    (t+8) (8-t/3) ((2/3)*t/logb 2 (H.scale i)-8) hp
  intro Q hQ B hB
  have hQne := advance_nonempty H.system 0 i [P] (by simpa using hne) Q hQ
  have hBne := (H.system i Q).box_nonempty hQne B hB
  have hrest : ((H.system i Q).rest B).vertices.Nonempty := by simpa only [StageSplit.rest_vertices] using hBne
  exact hlocal (H.scale i) (hD.trans (H.cutoff i hi)) 80 (hready i hi) V
    (advance H.system (i+1) 200 [(H.system i Q).rest B]) ((H.system i Q).pieces B) B.vertices
    (box_coupled_partition _ (by simpa only [StageSplit.rest_graph _ hB] using (H.system i Q).box_partition B hB) _ _ _)
    ((H.system i Q).piece_disjoint B hB) ((H.system i Q).piece_subset B hB)
    (advance_subset H.system (i+1) 200 [(H.system i Q).rest B] B.vertices (by simp))
    (fun v hv => advance_cover H.system (i+1) 200 [(H.system i Q).rest B] ((H.system i Q).rest B) (by simp) v (by simpa only [StageSplit.rest_vertices] using hv))
    (fun R hR => ⟨advance_nonempty H.system (i+1) 200 [(H.system i Q).rest B] (by simpa using hrest) R hR,
      H.gap_order hn i hik hQ hB hR⟩)
    ((H.bounded i hi Q hQ).2.2.2.1 B hB) ((H.bounded i hi Q hQ).2.2.1 B hB)
    (H.local_mass_two hn (fun j hj => (hready j hj).log_large) i 200 hik hQ hB)
    P.vertices.card C t hC ht (Finset.card_le_card (H.box_subset i hQ hB)) hsmall ih ihq

end
end ErdosGallai.Scale

namespace ErdosGallai
noncomputable section
lemma main_gap_scalar (q n S M L Nt Ni C t w : ℝ)
    (hn : 0 ≤ n) (hS : 0 ≤ S) (hC : 0 ≤ C) (ht : 0 ≤ t) (hw : 0 < w)
    (hM : M ≤ mainP*S) (hL : L ≤ mainH*n/w)
    (hNt : Nt ≤ n+mainH*n/w) (hNilo : n ≤ Ni) (hNihi : Ni ≤ 2*n)
    (hq : q ≤ L+(9+C*mainEta)*M+(t+8)*Nt+(8-t/3)*S+((2/3)*t/w-8)*Ni) :
    q ≤ mainA₂*(S+n/w)+(C/100)*S+t*(n-S/3+mainA₁*n/w) := by
  have hη := mainEta_pos
  have hc := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 9+C*mainEta)
  have hT := mul_le_mul_of_nonneg_left hNt (by linarith : 0 ≤ t+8)
  have hI := mul_le_mul_of_nonneg_left hNihi (by positivity : 0 ≤ (2/3)*t/w)
  have hI' : -8*Ni ≤ -8*n := by linarith
  have hA := mul_le_mul_of_nonneg_right (le_max_left (9*mainP+8) (9*mainH)) hS
  have hB := mul_le_mul_of_nonneg_right (le_max_right (9*mainP+8) (9*mainH)) (div_nonneg hn hw.le)
  change (9*mainP+8)*S ≤ mainA₂*S at hA
  change 9*mainH*(n/w) ≤ mainA₂*(n/w) at hB
  simp only [mainEta,mainP,mainA₁,div_eq_mul_inv] at hc hT hI hI' hA hB hq hL ⊢
  nlinarith only [hc,hT,hI,hI',hA,hB,hq,hL]

lemma main_terminal_scalar (q n M C Dstar : ℝ) (hn : 0 ≤ n) (hC : 0 ≤ C)
    (hCbig : 4*(20+Dstar+18*mainP) ≤ C) (hM : M ≤ 2*mainP*n)
    (hq : q ≤ (20+Dstar)*n+(9+C*mainEta)*M) :
    q ≤ C*Batch.inductionPhi n*n := by
  have hη := mainEta_pos
  have hc := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 9+C*mainEta)
  have hbig := mul_le_mul_of_nonneg_right hCbig hn
  have hphi := mul_le_mul_of_nonneg_left (Batch.inductionPhi_bounds n).1 (mul_nonneg hC hn)
  have hCn : 0 ≤ C*n := mul_nonneg hC hn
  simp only [mainEta,mainP] at hc hbig hq
  nlinarith only [hq,hc,hbig,hphi,hCn]

end
end ErdosGallai

namespace ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {P : AssignedPiece V} {Dstar : ℝ}

lemma Layers.gap_log (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ)) (i) :
    logb 2 (H.scale (i+200)) = scaleTheta^200 * logb 2 (H.scale i) := by
  dsimp only [Layers.scale]
  rw [inductionScale_add _ (by positivity)]
  exact Real.logb_rpow_eq_mul_logb_of_pos (inductionScale_pos _ (by linarith) _)

lemma Layers.gap_mass (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hready : ∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) (i)
    (hik : i+200 < H.count) :
    H.mass (i+201) ≤ (P.vertices.card:ℝ) + ErdosGallai.mainH*P.vertices.card/logb 2 (H.scale i) := by
  have hh := H.mass_upper hn (fun j hj => (hready j hj).log_large) (i+200) hik
  rw [H.gap_log hn] at hh
  convert hh using 1 ; try omega
  unfold ErdosGallai.mainH
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma Layers.gap_cycles (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hready : ∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) (i)
    (hik : i+200 < H.count) :
    ((pastCycles H.system 0 (i+201) [P]).length:ℝ) ≤
      ErdosGallai.mainH*P.vertices.card/logb 2 (H.scale i) := by
  have hh := H.cycles_bound hn hready (i+200) hik
  rw [H.gap_log hn] at hh
  have hw : 0 < logb 2 (H.scale i) := inductionScale_log_pos _ hn i
  calc
    _ ≤ 20*P.vertices.card/(scaleTheta^200*logb 2 (H.scale i)) := hh
    _ ≤ 80*P.vertices.card/(scaleTheta^200*logb 2 (H.scale i)) :=
      div_le_div_of_nonneg_right (by nlinarith [(Nat.cast_nonneg P.vertices.card : (0:ℝ) ≤ _)]) (by positivity)
    _ = _ := by unfold ErdosGallai.mainH; simp only [div_eq_mul_inv,mul_inv_rev]; ring

lemma Layers.boundary_cost (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hready : ∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) :
    costMass (H.frontier H.count) ≤ Dstar*P.vertices.card := by
  have hne : P.vertices.Nonempty := Finset.card_pos.mp (by exact_mod_cast (by linarith : (0:ℝ) < P.vertices.card))
  have hD : 0 ≤ Dstar := by
    have hh := H.last_lt
    have hd := inductionScale_pos P.vertices.card (by linarith) H.count
    linarith
  have hcost : ∀ Q ∈ H.frontier H.count, (decompositionCost Q.graph:ℝ) ≤ (Dstar/2)*Q.vertices.card := by
    intro Q hQ
    have hQne := advance_nonempty H.system 0 H.count [P] (by simpa using hne) Q hQ
    have hc : (0:ℝ) < Q.vertices.card := by exact_mod_cast Finset.card_pos.mpr hQne
    have hg := (div_le_iff₀ hc).mp (H.degree H.count le_rfl Q hQ)
    have hh := mul_le_mul_of_nonneg_right H.last_lt.le hc.le
    have he := (Nat.cast_le.mpr (decompositionCost_edgeCount Q.graph) : (_:ℝ) ≤ _)
    nlinarith only [hg,hh,he]
  have hh := piece_list_cost (H.frontier H.count) (Dstar/2) hcost
  have hm := mul_le_mul_of_nonneg_left (H.mass_two hn (fun j hj => (hready j hj).log_large) H.count le_rfl)
    (div_nonneg hD (by norm_num : (0:ℝ) ≤ 2))
  change costMass (H.frontier H.count) ≤ (Dstar/2)*H.mass H.count at hh
  nlinarith only [hh,hm]

lemma Layers.terminal_cost (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hready : ∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) (c : ℝ)
    (hp : ∀ R ∈ pastPieces H.system 0 H.count [P], (decompositionCost R.graph:ℝ) ≤ c*R.vertices.card) :
    (decompositionCost P.graph:ℝ) ≤ (20+Dstar)*P.vertices.card + c*vertexMass (pastPieces H.system 0 H.count [P]) := by
  have hcost := past_cost H.system 0 H.count P c hp
  have he := H.boundary_cost hn hready
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt H.positive)
  have hcy := H.cycles_bound hn hready j (by omega)
  have hw := (hready j (by omega)).log_large
  have hdiv : 20*(P.vertices.card:ℝ)/logb 2 (H.scale j) ≤ 20*P.vertices.card :=
    div_le_self (by positivity) (by linarith)
  rw [hj] at hcost he ⊢
  nlinarith only [hcost,he,hcy,hdiv]

end
end ErdosGallai.Scale

end
end

/-! ### Upstream module `Combinatorics/CycleDecomposition/Main.lean` -/

section
open _root_.Filter _root_.Asymptotics _root_.Real
noncomputable section
open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Finset
namespace ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {P : AssignedPiece V} {Dstar : ℝ}

def Layers.pieceSequence (H : Layers P Dstar) (j : ℕ) : ℝ :=
  if j < H.count then H.pieceMass j else 0

lemma Layers.pieceSequence_nonneg (H : Layers P Dstar) (j) : 0 ≤ H.pieceSequence j := by
  unfold Layers.pieceSequence
  split_ifs
  · exact vertexMass_nonneg _
  · rfl

lemma Layers.pieceSequence_zero (H : Layers P Dstar) (j) (hj : H.count ≤ j) :
    H.pieceSequence j = 0 := by simp only [Layers.pieceSequence,ite_eq_right (by omega : ¬ j < H.count)]

lemma Layers.past_mass_eq_sequence (H : Layers P Dstar) (k) (hk : k ≤ H.count) :
    vertexMass (pastPieces H.system 0 k [P]) = ∑ j ∈ range k, H.pieceSequence j := by
  rw [pastPieces_mass]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.zero_add,Layers.pieceSequence,ite_eq_left (by have := Finset.mem_range.mp hj; omega : j < H.count)]

lemma Layers.prefix_choice (H : Layers P Dstar) :
    vertexMass (pastPieces H.system 0 H.count [P]) = 0 ∨
    ∃ i < H.count, 0 < H.pieceMass i ∧
      ∀ k ≤ H.count, k ≤ i+201 →
        vertexMass (pastPieces H.system 0 k [P]) ≤ ErdosGallai.mainP*H.pieceMass i := by
  by_cases he : ∃ j, 0 < H.pieceSequence j
  · right
    obtain ⟨i,hi,hpref⟩ := ErdosGallai.prefix_selection H.pieceSequence H.pieceSequence_nonneg
      200 H.count H.pieceSequence_zero he
    have hic : i < H.count := by
      by_contra hi'
      rw [H.pieceSequence_zero i (by omega)] at hi
      linarith
    simp only [Layers.pieceSequence,ite_eq_left hic] at hi
    refine ⟨i,hic,hi,?_⟩
    intro k hk hki
    rw [H.past_mass_eq_sequence k hk]
    have hh : (∑ j ∈ range k, H.pieceSequence j) ≤ ∑ j ∈ range (i+200+1), H.pieceSequence j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun j _ _ => H.pieceSequence_nonneg j)
    apply hh.trans
    norm_num only [Layers.pieceSequence,ite_eq_left hic,ErdosGallai.mainP,Nat.cast_ofNat] at hpref ⊢
    exact hpref
  · left
    rw [H.past_mass_eq_sequence H.count le_rfl]
    apply Finset.sum_eq_zero
    intro j _
    exact le_antisymm (le_of_not_gt (fun h => he ⟨j,h⟩)) (H.pieceSequence_nonneg j)

end
end ErdosGallai.Scale

namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable

lemma main_edge_bound {V : Type} [Fintype V] (G : SimpleGraph V) :
    2*(Scale.edgeCount G:ℝ) ≤ (Fintype.card V:ℝ)^2 := by
  classical
  have h : (G.edgeFinset.card:ℝ) ≤ ((Fintype.card V).choose 2:ℝ) :=
    Nat.cast_le.mpr G.card_edgeFinset_le_card_choose_two
  rw [Nat.cast_choose_two] at h
  change 2*(G.edgeFinset.card:ℝ) ≤ _
  nlinarith [(Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)]

lemma main_cost_eq_scale {V : Type} [Fintype V] (G : SimpleGraph V) :
    decompositionCost G = Scale.decompositionCost G := by rfl
lemma main_cost_eq_batch {V : Type} [Fintype V] (G : SimpleGraph V) :
    decompositionCost G = Batch.decompositionCost G := by rfl

theorem main_cost_bound : ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    (decompositionCost G:ℝ) ≤ C*Batch.inductionPhi (Fintype.card V)*Fintype.card V := by
  classical
  let wmin : ℝ := max 80 (((mainA₁+1)/Batch.inductionDelta)^2)
  obtain ⟨Da,ha,hLayers⟩ := Scale.uniform_layers
  obtain ⟨Db,hb,hPiece⟩ := Scale.uniform_committed_piece_cost
  obtain ⟨Dc,hc,hGap⟩ := Scale.uniform_gap_prefix_cost
  obtain ⟨Dr,hr,hReady⟩ := main_scale_ready_cutoff wmin
  let Dstar : ℝ := max (max Da Db) (max Dc Dr)
  have hDa : Da ≤ Dstar := (le_max_left Da Db).trans (le_max_left _ _)
  have hDb : Db ≤ Dstar := (le_max_right Da Db).trans (le_max_left _ _)
  have hDc : Dc ≤ Dstar := (le_max_left Dc Dr).trans (le_max_right _ _)
  have hDr : Dr ≤ Dstar := (le_max_right Dc Dr).trans (le_max_right _ _)
  have hDstar : 1 < Dstar := ha.trans_le hDa
  let C : ℝ := max (4*(20+Dstar+18*mainP)) (7*mainA₂)
  have hCbig : 4*(20+Dstar+18*mainP) ≤ C := le_max_left _ _
  have hCA : 7*mainA₂ ≤ C := le_max_right _ _
  have hCpos : 0 < C := lt_of_lt_of_le (by linarith [mainP_pos]) hCbig
  have hC : 0 ≤ C := hCpos.le
  refine ⟨C,hCpos,?_⟩
  have hmain : ∀ n : ℕ, ∀ (V : Type) [Fintype V], Fintype.card V = n → ∀ (G : SimpleGraph V),
      (decompositionCost G:ℝ) ≤ C*Batch.inductionPhi (Fintype.card V)*Fintype.card V := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ hn G
      subst n
      have hn0 : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
      by_cases hsmall : (Fintype.card V:ℝ) < Dstar
      · have he := main_edge_bound G
        have hq : (decompositionCost G:ℝ) ≤ Scale.edgeCount G :=
          Nat.cast_le.mpr (Scale.decompositionCost_edgeCount G)
        have hnD := mul_le_mul_of_nonneg_right hsmall.le hn0
        have hphi := mul_le_mul_of_nonneg_left (Batch.inductionPhi_bounds (Fintype.card V)).1
          (mul_nonneg hC hn0)
        have hbig := mul_le_mul_of_nonneg_right hCbig hn0
        have hP := mul_nonneg mainP_pos.le hn0
        nlinarith only [he,hq,hnD,hphi,hbig,hP]
      · have hnD : Dstar ≤ (Fintype.card V:ℝ) := le_of_not_gt hsmall
        have hn1 : 1 < (Fintype.card V:ℝ) := hDstar.trans_le hnD
        let P : Scale.AssignedPiece V := ⟨univ,G,fun _ _ _ => ⟨mem_univ _,mem_univ _⟩⟩
        have hpc : P.vertices.card = Fintype.card V := Finset.card_univ
        have hp1 : 1 < (P.vertices.card:ℝ) := by simpa only [hpc] using hn1
        have hdeg : 2*(Scale.edgeCount P.graph:ℝ)/P.vertices.card ≤ P.vertices.card := by
          apply (div_le_iff₀ (by linarith : (0:ℝ) < P.vertices.card)).mpr
          simpa only [hpc,P,pow_two] using main_edge_bound G
        obtain ⟨H⟩ := hLayers Dstar hDa V P (by simpa only [hpc] using hnD) hdeg
        have hready' : ∀ j < H.count, MainScaleReady wmin (H.scale j) := by
          intro j hj
          exact hReady _ (hDr.trans (H.cutoff j hj))
        have hready : ∀ j < H.count, MainScaleReady 80 (H.scale j) := by
          intro j hj
          have hh := hready' j hj
          exact ⟨hh.gt_one,(le_max_left _ _).trans hh.log_large,hh.cycle_power,hh.batch_power,
            hh.bad_power,hh.skip_power,hh.active_eight⟩
        have ihw : ∀ (Q : Type) [Fintype Q] (F : SimpleGraph Q), Fintype.card Q < P.vertices.card →
            (decompositionCost F:ℝ) ≤ C*Fintype.card Q := by
          intro Q _ F hQ
          have hh := ih (Fintype.card Q) (by simpa only [hpc] using hQ) Q rfl F
          have hp := mul_le_mul_of_nonneg_left (Batch.inductionPhi_bounds (Fintype.card Q)).2
            (mul_nonneg hC (Nat.cast_nonneg (Fintype.card Q) : (0:ℝ) ≤ _))
          nlinarith only [hh,hp]
        have hpieces := hPiece Dstar hDb V P H C hC ihw
        have terminal (hm : Scale.vertexMass (Scale.pastPieces H.system 0 H.count [P]) ≤
            2*mainP*P.vertices.card) :
            (decompositionCost G:ℝ) ≤ C*Batch.inductionPhi (Fintype.card V)*Fintype.card V := by
          have hh := H.terminal_cost hp1 hready (9+C*mainEta) (hpieces H.count le_rfl)
          have ht := main_terminal_scalar _ P.vertices.card _ C Dstar (Nat.cast_nonneg _) hC hCbig hm hh
          simpa only [hpc,P,← main_cost_eq_scale] using ht
        rcases H.prefix_choice with hz | ⟨i,hic,hi,hprefix⟩
        · apply terminal
          rw [hz]
          exact mul_nonneg (mul_nonneg (by norm_num) mainP_pos.le) (Nat.cast_nonneg _)
        · by_cases hgap : i+200 < H.count
          · let t := C*Batch.inductionPhi ((H.scale i)^(3/10:ℝ))
            have ht : 0 ≤ t := mul_nonneg hC (by linarith [(Batch.inductionPhi_bounds ((H.scale i)^(3/10:ℝ))).1])
            have ihq : ∀ (Q : Type) [Fintype Q] (F : SimpleGraph Q), Fintype.card Q < P.vertices.card →
                (Fintype.card Q:ℝ) ≤ (H.scale i)^(3/10:ℝ) →
                (Batch.decompositionCost F:ℝ) ≤ t*Fintype.card Q := by
              intro Q _ F hQ hQD
              have hh := ih (Fintype.card Q) (by simpa only [hpc] using hQ) Q rfl F
              by_cases h0 : Fintype.card Q = 0
              · simpa only [h0,Nat.cast_zero,mul_zero,← main_cost_eq_batch] using hh
              · have h1 : (1:ℝ) ≤ Fintype.card Q := by exact_mod_cast (by omega : 1 ≤ Fintype.card Q)
                have hp := Batch.inductionPhi_monotone h1 (h1.trans hQD) hQD
                have hp' := mul_le_mul_of_nonneg_left hp
                  (mul_nonneg hC (Nat.cast_nonneg (Fintype.card Q) : (0:ℝ) ≤ _))
                change (decompositionCost F:ℝ) ≤ C*Batch.inductionPhi ((H.scale i)^(3/10:ℝ))*Fintype.card Q
                nlinarith only [hh,hp']
            have hlocal := hGap Dstar hDc V P H hp1 hready i hgap C t hC ht ihw ihq
              (hpieces (i+201) (by omega))
            have hscalar := main_gap_scalar _ P.vertices.card (H.pieceMass i)
              (Scale.vertexMass (Scale.pastPieces H.system 0 (i+201) [P]))
              ((Scale.pastCycles H.system 0 (i+201) [P]).length:ℝ)
              (H.mass (i+201)) (H.mass (i+1)) C t (logb 2 (H.scale i))
              (Nat.cast_nonneg _) (Scale.vertexMass_nonneg _) hC ht
              (by linarith [(hready i hic).log_large])
              (hprefix (i+201) (by omega) le_rfl) (H.gap_cycles hp1 hready i hgap)
              (H.gap_mass hp1 hready i hgap) (H.mass_lower (i+1))
              (H.mass_two hp1 (fun j hj => (hready j hj).log_large) (i+1) (by omega)) hlocal
            have habs := Batch.induction_cost_absorbed (H.scale i) P.vertices.card (H.pieceMass i)
              C mainA₁ mainA₂ (hready i hic).gt_one (Scale.inductionScale_le _ hp1.le i)
              (Scale.vertexMass_nonneg _) hC mainA₁_nonneg mainA₂_nonneg hCA
              (by linarith [(hready i hic).log_large])
              ((le_max_right _ _).trans (hready' i hic).log_large)
            have hfinal := hscalar.trans habs
            simpa only [hpc,P,← main_cost_eq_scale] using hfinal
          · apply terminal
            calc
              _ ≤ mainP*H.pieceMass i := hprefix H.count le_rfl (by omega)
              _ ≤ mainP*(2*P.vertices.card) := mul_le_mul_of_nonneg_left
                (H.pieceMass_two hp1 (fun j hj => (hready j hj).log_large) i hic) mainP_pos.le
              _ = _ := by ring
  intro V _ G
  exact hmain (Fintype.card V) V rfl G

theorem erdos_gallai : MainStatement := by
  obtain ⟨C,hC,hcost⟩ := main_cost_bound
  refine ⟨C,hC,?_⟩
  intro n G
  refine ⟨decompositionCost G,decompositionCost_spec G,?_⟩
  have hh := hcost (Fin n) G
  simp only [Fintype.card_fin] at hh
  have hp := mul_le_mul_of_nonneg_left (Batch.inductionPhi_bounds n).2
    (mul_nonneg hC.le (Nat.cast_nonneg n : (0:ℝ) ≤ _))
  nlinarith only [hh,hp]

end
end ErdosGallai

end
end

/-- Erdős Problem 184: every simple graph on `n` vertices is the edge-disjoint union of at most
`C * n` cycles and single edges, for an absolute constant `C`. -/
theorem erdos_184 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ∃ k : ℕ, ErdosGallai.EdgeDecomposition G k ∧ (k : ℝ) ≤ C * n :=
  ErdosGallai.erdos_gallai

#print axioms erdos_184
-- 'Erdos184.erdos_184' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos184
