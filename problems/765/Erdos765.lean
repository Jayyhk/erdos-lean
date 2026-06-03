import Mathlib

namespace Erdos765


open Finset Fintype SimpleGraph

/-- The 4-cycle over `Fin 4`, where vertices differing by 1 are adjacent. -/
def C4 : SimpleGraph (Fin 4) where
  Adj i j := j = i + 1 ∨ i = j + 1

section LowerBound

variable {F : Type*} [Field F]

section PointCounting

open Polynomial in
lemma exists_sq_add_sq [Finite F] (c : F) : ∃ a b, a ^ 2 + b ^ 2 = c := by
  let _ : Fintype F := ofFinite _
  obtain ⟨⟨k, hk⟩, pr, cF⟩ := FiniteField.card F _
  by_cases hc : ringChar F = 2
  · obtain ⟨r, rfl⟩ := FiniteField.isSquare_of_char_two hc c
    exact ⟨r, 0, by simp [sq]⟩
  let f : F[X] := X ^ 2
  let g : F[X] := X ^ 2 - C c
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (degree_X_pow 2) (degree_X_pow_sub_C (by decide) c) (FiniteField.odd_card_of_char_ne_two hc)
  refine ⟨a, b, ?_⟩
  rw [← sub_eq_zero]
  simpa only [f, g, eval_C, eval_X, eval_pow, eval_sub, ← add_sub_assoc] using hab

lemma card_sum_sq_eq [Finite F] {c d : F} (hc : c ≠ 0) (hd : d ≠ 0) :
    {p : F × F | p.1 ^ 2 + p.2 ^ 2 = c}.ncard = {p : F × F | p.1 ^ 2 + p.2 ^ 2 = d}.ncard := by
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq (d / c)
  let f (p : F × F) := (a * p.1 - b * p.2, b * p.1 + a * p.2)
  have injf : f.Injective := fun p q h ↦ by grind
  set S := {p : F × F | p.1 ^ 2 + p.2 ^ 2 = c}
  set T := {p : F × F | p.1 ^ 2 + p.2 ^ 2 = d}
  suffices S.BijOn f T by exact Set.ncard_congr' this.equiv
  refine ⟨fun p hp ↦ by grind, injf.injOn, fun p hp ↦ ?_⟩
  obtain ⟨q, hq⟩ : ∃ q, f q = p := Finite.injective_iff_surjective.mp injf p
  grind

theorem card_quadric [Fintype F] [DecidableEq F] : #{v : Fin 3 → F | v ⬝ᵥ v = 0} = card F ^ 2 := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ c, c ≠ 0 → #{p : F × F | p.1 ^ 2 + p.2 ^ 2 = c} = N :=
    ⟨#{p : F × F | p.1 ^ 2 + p.2 ^ 2 = 1}, fun c hc ↦ by
      simp_rw [← Set.ncard_coe_finset, coe_filter_univ]
      exact card_sum_sq_eq hc one_ne_zero⟩
  calc
    _ = ∑ z, #{p : F × F | p.1 ^ 2 + p.2 ^ 2 = -z ^ 2} := by
      simp_rw [dotProduct, Fin.sum_univ_three, card_filter, ← sq, ← sum_product']
      apply sum_bij fun x _ ↦ (x 2, (x 0, x 1))
      · simp
      · simp_rw [mem_univ, forall_const, Prod.mk.injEq, and_imp]
        exact fun _ _ _ _ _ ↦ by ext i; fin_cases i <;> assumption
      · simp_rw [univ_product_univ, mem_univ, forall_const, exists_const, Prod.forall,
          Prod.mk.injEq]
        exact fun a b c ↦ ⟨fun i ↦ if i = 2 then a else if i = 0 then b else c, rfl, rfl, rfl⟩
      · simp [add_eq_zero_iff_eq_neg]
    _ = ∑ c, #{p : F × F | p.1 ^ 2 + p.2 ^ 2 = c} := by
      rw [sum_eq_add_sum_compl 0, zero_pow two_ne_zero, neg_zero, sum_eq_add_sum_compl 0]
      congr! 2 with c hc
      rw [mem_compl, mem_singleton] at hc
      rw [hN _ hc, hN _ (by simpa)]
    _ = _ := by
      simp_rw [Finset.card_eq_sum_ones, sum_filter]
      rw [sum_comm]
      simp [sq]

end PointCounting

variable (F) in
/-- An abbreviation for the projective plane over `F`. -/
abbrev P2 := Projectivization F (Fin 3 → F)

variable (F) in
/-- The projective plane graph. Two distinct vertices are adjacent if their dot product is 0. -/
def P2Graph : SimpleGraph (P2 F) where
  Adj v w := v ≠ w ∧ v.orthogonal w
  symm v w h := ⟨h.1.symm, Projectivization.orthogonal_comm.mp h.2⟩

lemma p2Graph_adj {v w : P2 F} : (P2Graph F).Adj v w ↔ v ≠ w ∧ v.orthogonal w := Iff.rfl

lemma subsingleton_commonNeighbors_p2Graph {v w : P2 F} (h : v ≠ w) :
    ((P2Graph F).commonNeighbors v w).Subsingleton := fun _ ma _ mb ↦
  (Configuration.ofField.eq_or_eq_of_orthogonal ma.1.2 ma.2.2 mb.1.2 mb.2.2).resolve_left h

theorem p2Graph_C4_free : C4.Free (P2Graph F) := by
  by_contra! h
  obtain ⟨⟨f, adjf⟩, injf⟩ := h
  apply absurd (subsingleton_commonNeighbors_p2Graph (injf.ne (show 0 ≠ 2 by lia)))
  rw [Set.not_subsingleton_iff]
  refine ⟨f 1, ⟨adjf ?_, adjf ?_⟩, f 3, ⟨adjf ?_, adjf ?_⟩, injf.ne (by lia)⟩ <;> simp [C4]

variable [Fintype F]

theorem card_P2 :
    let _ : Fintype (P2 F) := ofFinite _
    card (P2 F) = card F ^ 2 + card F + 1 := by
  simp_rw [card_eq_nat_card, Projectivization.card_of_finrank _ _ (Module.finrank_fin_fun F),
    sum_range_succ, sum_range_zero]
  lia

open scoped Classical in
lemma card_self_orthogonal :
    let _ : Fintype (P2 F) := ofFinite _;
    #{v : P2 F | v.orthogonal v} = card F + 1 := by
  have work : #{v ∈ univ.erase (0 : Fin 3 → F) | v ⬝ᵥ v = 0} = card F ^ 2 - 1 := by
    simp [filter_erase, card_quadric (F := F)]
  let M : Finset Fˣ := univ
  rw [← Nat.mul_left_inj (show #M ≠ 0 by rw [card_ne_zero]; exact univ_nonempty), ← card_product,
    show #M = card F - 1 by exact card_units F, ← Nat.sq_sub_sq, one_pow, ← work]
  let f (p : P2 F × Fˣ) : Fin 3 → F := p.2 • p.1.rep
  have injf : f.Injective := fun ⟨p, c⟩ ⟨q, d⟩ e ↦ by
    simp only [f] at e
    have pq : p = q := by
      rw [← p.mk_rep, ← q.mk_rep, Projectivization.mk_eq_mk_iff]
      refine ⟨c⁻¹ * d, ?_⟩
      rw [mul_smul, ← e, ← mul_smul, inv_mul_cancel, one_smul]
    simp_rw [Prod.mk.injEq, pq, true_and]
    rw [pq] at e
    rw [← Units.val_inj]
    exact smul_left_injective _ q.rep_nonzero e
  rw [← card_map ⟨_, injf⟩]
  congr
  ext v
  simp_rw [mem_map, mem_product, Function.Embedding.coeFn_mk, f, M, mem_filter, mem_erase, mem_univ,
    true_and, and_true, Prod.exists]
  refine ⟨fun ⟨p, c, op, dv⟩ ↦ ?_, fun ⟨nv, ov⟩ ↦ ?_⟩
  · rw [← p.mk_rep, Projectivization.orthogonal_mk] at op
    rw [← dv, dotProduct_smul, smul_dotProduct, op, smul_ne_zero_iff_ne c]
    simp [p.rep_nonzero]
  · obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep F v nv
    refine ⟨Projectivization.mk F v nv, c⁻¹, ?_⟩
    rw [Projectivization.orthogonal_mk, ← hc]
    simp [ov]

open Configuration.ProjectivePlane in
open scoped Classical in
lemma degree_p2Graph (v : P2 F) :
    let _ : Fintype (P2 F) := ofFinite _
    (P2Graph F).degree v = if v.orthogonal v then card F else card F + 1 := by
  extract_lets
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  conv_lhs =>
    enter [1, 1, w]
    rw [p2Graph_adj, and_comm]
  rw [← filter_filter, filter_ne]
  have oec : order (P2 F) (P2 F) = card F := by
    have cl := card_lines (P2 F) (P2 F)
    rw [card_P2] at cl
    suffices StrictMono fun n ↦ n ^ 2 + n + 1 by exact this.injective cl.symm
    exact strictMono_nat_of_lt_succ fun n ↦ by lia
  have lc := lineCount_eq (P2 F) v
  rw [oec, Configuration.lineCount, Nat.card_eq_fintype_card, Fintype.card_subtype] at lc
  change #{w | v.orthogonal w} = _ at lc
  split_ifs with hv
  · rw [card_erase_of_mem (by simp [hv]), lc, Nat.add_sub_cancel]
  · rw [erase_eq_of_notMem (by simp [hv]), lc]

open scoped Classical in
lemma sum_degree_p2Graph :
    let _ : Fintype (P2 F) := ofFinite _
    ∑ v, (P2Graph F).degree v = card F * (card F + 1) ^ 2 := by
  simp_rw [degree_p2Graph, sum_ite, sum_const, ← compl_filter, card_compl, card_P2,
    card_self_orthogonal, smul_eq_mul, add_assoc, Nat.add_sub_cancel_right]
  lia

theorem card_edgeFinset_p2Graph :
    #(P2Graph F).edgeFinset = card F * (card F + 1) ^ 2 / 2 := by
  rw [← sum_degree_p2Graph, sum_degrees_eq_twice_card_edges, Nat.mul_div_cancel_left _ zero_lt_two]
  congr!

end LowerBound

theorem extremalNumber_C4_ge_of_isPrimePow {q : ℕ} (hq : IsPrimePow q) :
    q * (q + 1) ^ 2 / 2 ≤ extremalNumber (q ^ 2 + q + 1) C4 := by
  rw [← Fintype.card_fin q, ← nonempty_field_iff] at hq
  obtain ⟨Fq⟩ := hq
  conv_lhs => rw [← Fintype.card_fin q, ← card_edgeFinset_p2Graph]
  let _ : Fintype (P2 (Fin q)) := ofFinite _
  have ceq : card (P2 (Fin q)) = q ^ 2 + q + 1 := by rw [card_P2, Fintype.card_fin q]
  rw [extremalNumber_of_fintypeCard_eq ceq]
  classical
  have : P2Graph (Fin q) ∈ ({G | C4.Free G} : Finset _) := by
    rw [mem_filter_univ]
    exact p2Graph_C4_free
  convert le_sup (f := fun G : SimpleGraph _ ↦ #G.edgeFinset) this

section UpperBound

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

open Function.Embedding in
lemma card_clackers_eq [DecidableEq V] :
    #{p : V × Sym2 V | ¬p.2.IsDiag ∧ ∀ w ∈ p.2, G.Adj p.1 w} = ∑ v, (G.degree v).choose 2 := by
  rw [card_filter, sum_prod_type]
  congr! with v
  rw [← card_neighborFinset_eq_degree, ← card_coe, ← Sym2.card_subtype_not_diag, subtype_card,
    ← card_filter, ← card_map (sym2Map (subtype _))]
  congr
  ext e
  induction e using Sym2.inductionOn with | _ a b
  simp_rw [mem_map, mem_filter_univ, Sym2.exists, Sym2.isDiag_iff_proj_eq, Sym2.mem_iff,
    forall_eq_or_imp, forall_eq, sym2Map_apply, subtype_apply, Sym2.map_pair_eq, Subtype.exists,
    Subtype.mk.injEq, mem_neighborFinset, exists_prop, Sym2.eq_iff]
  simp only [and_or_left, exists_or, ↓existsAndEq, and_true]
  tauto

variable (G) in
/-- Construct a graph homomorphism from the 4-cycle to `G` given necessary adjacencies. -/
def _root_.SimpleGraph.C4Hom {v₀ v₁ v₂ v₃ : V} (a₀₁ : G.Adj v₀ v₁) (a₁₂ : G.Adj v₁ v₂)
    (a₂₃ : G.Adj v₂ v₃) (a₃₀ : G.Adj v₃ v₀) : C4 →g G where
  toFun := ![v₀, v₁, v₂, v₃]
  map_rel' {i j} a := by
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by lia
    · obtain rfl | rfl : j = 1 ∨ j = 3 := by grind [C4]
      all_goals simp only [Matrix.cons_val]
      · exact a₀₁
      · exact a₃₀.symm
    · obtain rfl | rfl : j = 0 ∨ j = 2 := by grind [C4]
      all_goals simp only [Matrix.cons_val]
      · exact a₀₁.symm
      · exact a₁₂
    · obtain rfl | rfl : j = 1 ∨ j = 3 := by grind [C4]
      all_goals simp only [Matrix.cons_val]
      · exact a₁₂.symm
      · exact a₂₃
    · obtain rfl | rfl : j = 0 ∨ j = 2 := by grind [C4]
      all_goals simp only [Matrix.cons_val]
      · exact a₃₀
      · exact a₂₃.symm

omit [Fintype V] in
lemma four_vector_inj {v₀ v₁ v₂ v₃ : V} (n₀₁ : v₀ ≠ v₁) (n₀₂ : v₀ ≠ v₂) (n₀₃ : v₀ ≠ v₃)
    (n₁₂ : v₁ ≠ v₂) (n₁₃ : v₁ ≠ v₃) (n₂₃ : v₂ ≠ v₃) : ![v₀, v₁, v₂, v₃].Injective := by
  rw [← List.nodup_ofFn]
  simp_rw [List.ofFn_succ, Fin.reduceSucc, Matrix.cons_val, List.ofFn_zero]
  grind

lemma card_clackers_le [DecidableEq V] (fG : C4.Free G) :
    #{p : V × Sym2 V | ¬p.2.IsDiag ∧ ∀ w ∈ p.2, G.Adj p.1 w} ≤ (card V).choose 2 := by
  rw [card_filter, sum_prod_type, sum_comm]
  simp_rw [ite_and]
  conv_lhs =>
    enter [2, e]
    rw [← ite_sum_zero ¬e.IsDiag]
  simp_rw [← card_filter, sum_ite, sum_const_zero, add_zero]
  calc
    _ ≤ ∑ e : Sym2 V with ¬e.IsDiag, 1 := by
      refine sum_le_sum fun e hn ↦ ?_
      induction e using Sym2.inductionOn with | _ v₀ v₂
      simp_rw [mem_filter_univ, Sym2.isDiag_iff_proj_eq] at hn
      rw [card_le_one]
      intro v₁ a₁ v₃ a₃
      simp_rw [mem_filter_univ, Sym2.mem_iff, forall_eq_or_imp, forall_eq] at a₁ a₃
      contrapose! fG
      exact ⟨⟨G.C4Hom a₁.1.symm a₁.2 a₃.2.symm a₃.1,
        four_vector_inj a₁.1.ne' hn a₃.1.ne' a₁.2.ne fG a₃.2.ne'⟩⟩
    _ = _ := by rw [← card_eq_sum_ones, ← Fintype.card_subtype, Sym2.card_subtype_not_diag]

theorem reiman_inequality (fG : C4.Free G) :
    #G.edgeFinset ≤ card V / 4 * (√(4 * card V - 3) + 1) := by
  obtain cV | cV := (card V).eq_zero_or_pos
  · rw [cV, Nat.cast_zero, zero_div, zero_mul, Nat.cast_nonpos, card_eq_zero, edgeFinset_eq_empty]
    rw [card_eq_zero_iff] at cV
    let u : Subsingleton (SimpleGraph V) := inferInstance
    exact u.elim ..
  rw [div_mul_eq_mul_div, le_div_iff₀' zero_lt_four, mul_add_one, ← sub_le_iff_le_add]
  refine le_of_sq_le_sq ?_ (by positivity)
  have nn : (0 : ℝ) ≤ 4 * card V - 3 := by
    rw [sub_nonneg]
    norm_cast
    lia
  rw [mul_pow, Real.sq_sqrt nn]
  suffices (2 * #G.edgeFinset : ℝ) ^ 2 ≤
    card V * (2 * #G.edgeFinset + card V * (card V - 1)) by linarith
  rw [← Nat.cast_two, ← Nat.cast_mul, ← sum_degrees_eq_twice_card_edges, Nat.cast_sum]
  apply sq_sum_le_card_mul_sum_sq.trans
  rw [card_univ]
  refine mul_le_mul_of_nonneg_left ?_ (by simp)
  rw [← sub_le_iff_le_add', ← sum_sub_distrib, ← div_le_div_iff_of_pos_right zero_lt_two,
    ← Nat.cast_choose_two, sum_div]
  conv_lhs =>
    enter [2, v]
    rw [sq, ← mul_sub_one, ← Nat.cast_choose_two]
  classical
  rw [← Nat.cast_sum, Nat.cast_le, ← card_clackers_eq]
  exact card_clackers_le fG

end UpperBound

theorem extremalNumber_C4_le {n : ℕ} : extremalNumber n C4 ≤ ⌊n / 4 * (√(4 * n - 3) + 1)⌋₊ := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ fG
  rw [Nat.le_floor_iff (by positivity)]
  exact reiman_inequality fG

lemma extremalNumber_C4_le_real {n : ℕ} : extremalNumber n C4 ≤ n / 4 * (√(4 * n - 3) + 1) := by
  rw [← Nat.le_floor_iff (by positivity)]
  exact extremalNumber_C4_le

open Filter Asymptotics Real

section PNT

/-- A result from [PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/main/PrimeNumberTheoremAnd/Consequences.lean#L1555). -/
axiom prime_between {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x < p ∧ p < (1 + ε) * x

lemma prime_between' {ε : ℝ} (εpos : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ (1 - ε) * x < p ∧ p < x := by
  obtain lε | lε := le_or_gt 1 ε
  · refine (eventually_gt_atTop 2).mono fun x hx ↦ ⟨2, Nat.prime_two, ⟨?_, mod_cast hx⟩⟩
    apply (show (0 : ℝ) < (2 : ℕ) by simp).trans_le'
    apply mul_nonpos_of_nonpos_of_nonneg <;> linarith
  replace lε : 0 < 1 - ε := by linarith
  have tt : Tendsto ((1 - ε) * ·) atTop atTop := (tendsto_const_mul_atTop_of_pos lε).mpr tendsto_id
  convert tt.eventually (prime_between (div_pos εpos lε)) with x
  field

lemma exists_prime_near_sqrt' {ε : ℝ} (εpos : 0 < ε) :
    ∀ᶠ n in atTop, ∃ q : ℕ,
      q.Prime ∧ q ^ 2 + q + 1 ≤ n ∧ (1 - ε) * ((√(4 * n - 3) - 1) / 2) ≤ q := by
  obtain lε | lε := le_or_gt 1 ε
  · refine (eventually_gt_atTop 7).mono fun x hx ↦ ⟨2, Nat.prime_two, ⟨by lia, ?_⟩⟩
    apply (show (0 : ℝ) ≤ (2 : ℕ) by simp).trans'
    apply mul_nonpos_of_nonpos_of_nonneg (by linarith) (div_nonneg ?_ zero_le_two)
    rw [sub_nonneg, one_le_sqrt, le_sub_iff_add_le]
    norm_cast
    lia
  have tt : Tendsto (fun n : ℕ ↦ (√(4 * n - 3) - 1) / 2) atTop atTop := by
    conv =>
      enter [1, n]
      rw [div_eq_inv_mul]
    rw [tendsto_const_mul_atTop_of_pos (by norm_num)]
    refine tendsto_atTop_add_const_right _ _ (tendsto_sqrt_atTop.comp ?_)
    apply tendsto_atTop_add_const_right
    rw [tendsto_const_mul_atTop_of_pos (by norm_num)]
    exact tendsto_natCast_atTop_atTop
  filter_upwards [tt.eventually (prime_between' εpos)] with n ⟨q, pq, lbq, ubq⟩
  refine ⟨q, pq, ?_, lbq.le⟩
  rw [lt_div_iff₀' zero_lt_two, lt_sub_iff_add_lt, lt_sqrt (by positivity),
    lt_sub_iff_add_lt, show (2 * q + 1 : ℝ) ^ 2 + 3 = 4 * (q ^ 2 + q + 1) by ring,
    mul_lt_mul_iff_right₀ zero_lt_four] at ubq
  exact_mod_cast ubq.le

open Topology in
lemma sqrt_approx_eventually {ε : ℝ} (εpos : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (1 - ε) * √n ≤ (√(4 * n - 3) - 1) / 2 := by
  obtain hε | hε := lt_or_ge ε 2
  · have tt : Tendsto (fun n : ℕ ↦ (4 * (1 - ε) / √n + 4 / n) / (4 * ε * (2 - ε))) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat.sqrt).add
        (tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat)).div_const _
    replace tt :
        Tendsto (fun n : ℕ ↦ (4 * (1 - ε) * √n + 4) / (4 * ε * (2 - ε) * n)) atTop (𝓝 0) := by
      grind
    replace tt : ∀ᶠ n : ℕ in atTop, 4 * (1 - ε) * √n + 4 ≤ 4 * ε * (2 - ε) * n := by
      filter_upwards [tt.eventually (gt_mem_nhds zero_lt_one), eventually_gt_atTop 0] with n hn hn'
      rw [div_lt_iff₀ (mul_pos (mul_pos (by linarith) (by linarith)) (by simp [hn']))] at hn
      linarith
    replace tt : ∀ᶠ n : ℕ in atTop, (2 * (1 - ε) * √n + 1) ^ 2 ≤ 4 * n - 3 := by grind
    filter_upwards [tt, eventually_ge_atTop 1] with n hn hn'
    replace hn' : (0 : ℝ) ≤ 4 * n - 3 := by norm_cast; lia
    nlinarith [sqrt_nonneg (4 * n - 3), mul_self_sqrt hn']
  · filter_upwards [eventually_gt_atTop 0] with n hn
    apply (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sqrt_nonneg _)).trans
    refine div_nonneg ?_ zero_le_two
    rw [sub_nonneg, one_le_sqrt, le_sub_iff_add_le]
    norm_cast
    lia

lemma exists_prime_near_sqrt {ε : ℝ} (εpos : 0 < ε) :
    ∀ᶠ n in atTop, ∃ q : ℕ, q.Prime ∧ q ^ 2 + q + 1 ≤ n ∧ (1 - ε) * √n ≤ q := by
  obtain hε | hε := le_or_gt 2 ε
  · filter_upwards [exists_prime_near_sqrt' εpos] with n ⟨q, hprime, hle, _⟩
    exact ⟨q, hprime, hle,
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sqrt_nonneg _)).trans q.cast_nonneg⟩
  · have hε2 : 0 < ε / 2 := by linarith
    have h1mε2 : 0 ≤ 1 - ε / 2 := by linarith
    filter_upwards [exists_prime_near_sqrt' hε2, sqrt_approx_eventually hε2]
      with n ⟨q, hprime, hle, hq_bound⟩ hsqrt
    refine ⟨q, hprime, hle, ?_⟩
    calc
      _ ≤ (1 - ε / 2) * ((1 - ε / 2) * √n) := by nlinarith [sq_nonneg (ε / 2), sqrt_nonneg n]
      _ ≤ (1 - ε / 2) * ((√(4 * n - 3) - 1) / 2) := mul_le_mul_of_nonneg_left hsqrt h1mε2
      _ ≤ _ := hq_bound

end PNT

/-- If `H` has no isolated vertices, then `H.Free` is preserved under `SimpleGraph.map`. -/
lemma _root_.SimpleGraph.Free.map {V W X : Type*} {G : SimpleGraph V} {H : SimpleGraph X}
    (hfree : H.Free G) (f : V ↪ W) (hH : ∀ x, ∃ y, H.Adj x y) : H.Free (G.map f) := by
  contrapose hfree
  obtain ⟨g, hg⟩ := hfree
  have hg2 {x y} (hxy : H.Adj x y) : (G.map f).Adj (g x) (g y) := g.map_rel' hxy
  have h_preimage (x) : g x ∈ Set.range f := by
    obtain ⟨y, hy⟩ := hH x
    obtain ⟨u, v, huv⟩ := hg2 hy
    grind
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ∀ x, f (ψ x) = g x :=
    ⟨fun x ↦ (h_preimage x).choose, fun x ↦ (h_preimage x).choose_spec⟩
  refine ⟨⟨ψ, ?_⟩, ?_⟩
  · grind [map_adj]
  · rw [RelHom.coeFn_mk]
    exact fun x y hxy ↦ hg (by rw [← hψ x, ← hψ y, hxy])

/-- Monotonicity of `extremalNumber` for graphs without isolated vertices. -/
lemma _root_.SimpleGraph.extremalNumber_mono_left_of_no_iso {W : Type*} {H : SimpleGraph W}
    {m n : ℕ} (hmn : m ≤ n) (hH : ∀ w, ∃ w', H.Adj w w') :
    extremalNumber m H ≤ extremalNumber n H := by
  rw [← Fintype.card_fin m, ← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ hG
  set G' : SimpleGraph (Fin n) := G.map (Fin.castLEEmb hmn)
  have hG'_free : H.Free G' := hG.map (Fin.castLEEmb hmn) hH
  have hG'_edgeFinset : #G'.edgeFinset = #G.edgeFinset := by
    convert card_edgeFinset_map (Fin.castLEEmb hmn) G
  exact hG'_edgeFinset ▸ card_edgeFinset_le_extremalNumber hG'_free

lemma C4_no_isolated_vertices : ∀ v, ∃ w, C4.Adj v w := by simp [C4]

lemma extremalNumber_C4_mono {m n : ℕ} (hmn : m ≤ n) :
    extremalNumber m C4 ≤ extremalNumber n C4 :=
  SimpleGraph.extremalNumber_mono_left_of_no_iso hmn C4_no_isolated_vertices

lemma extremalNumber_C4_ge_of_isPrimePow_le {q n : ℕ} (hq : IsPrimePow q)
    (hle : q ^ 2 + q + 1 ≤ n) : q * (q + 1) ^ 2 / 2 ≤ extremalNumber n C4 :=
  (extremalNumber_C4_ge_of_isPrimePow hq).trans (extremalNumber_C4_mono hle)

lemma pow_three_div_two_eq {n : ℕ} : n ^ (3 / 2 : ℝ) = n * √n := by
  rw [sqrt_eq_rpow, ← rpow_one_add' (by simp) (by positivity)]
  norm_num

lemma upper_bound_le_rpow_add {n : ℕ} :
    n / 4 * (√(4 * n - 3) + 1) ≤ n ^ (3 / 2 : ℝ) / 2 + n / 4 := by
  suffices h_sqrt : √(4 * n - 3) ≤ 2 * √n by
    rw [pow_three_div_two_eq]
    nlinarith [sqrt_nonneg n, sq_sqrt n.cast_nonneg]
  exact sqrt_le_iff.mpr ⟨by positivity, by nlinarith [mul_self_sqrt n.cast_nonneg]⟩

lemma eventually_rpow_pos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < n ^ (3 / 2 : ℝ) / 2 :=
  eventually_atTop.mpr ⟨1, fun n hn ↦ by positivity⟩

lemma lower_bound_from_prime {n q : ℕ} {ε : ℝ} (hε1 : ε < 1) (hq : (1 - ε) * √n ≤ q) :
    (1 - ε) ^ 3 * (n ^ (3 / 2 : ℝ) / 2) ≤ q * (q + 1) ^ 2 / 2 := by
  have h_subst : (1 - ε) ^ 3 * (n ^ (3 / 2 : ℝ) / 2) ≤
      ((1 - ε) * √n) * ((1 - ε) * √n + 1) ^ 2 / 2 := by
    nth_rw 1 [pow_three_div_two_eq, ← mul_self_sqrt n.cast_nonneg,
      show (1 - ε) ^ 3 * (√n * √n * √n / 2) = (1 - ε) * √n * ((1 - ε) * √n + 0) ^ 2 / 2 by ring]
    replace hε1 : 0 < 1 - ε := by linarith
    gcongr
    positivity
  apply h_subst.trans
  gcongr
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hε1.le) (sqrt_nonneg _)) zero_le_one

lemma nat_div_two_cast (q : ℕ) : (q * (q + 1) ^ 2 / 2 : ℝ) = (q * (q + 1) ^ 2 / 2 : ℕ) := by
  have h : 2 ∣ q * (q + 1) ^ 2 := by
    obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := q.even_or_odd <;> lia
  norm_cast

lemma eventually_n_le_c_rpow {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, n / 4 ≤ c * (n ^ (3 / 2 : ℝ) / 2) := by
  have h_bound : ∀ᶠ n : ℕ in atTop, √n ≥ 1 / (2 * c) :=
    eventually_atTop.mpr ⟨⌈(1 / (2 * c)) ^ 2⌉₊, fun n hn ↦ le_sqrt_of_sq_le (by simpa using hn)⟩
  filter_upwards [h_bound] with n hn
  rw [pow_three_div_two_eq]
  nlinarith [sqrt_nonneg n, sq_sqrt n.cast_nonneg,
    mul_div_cancel₀ (1 : ℝ) <| show (2 * c) ≠ 0 by positivity, show 0 ≤ n * c by positivity]

theorem erdos_765 : (fun n ↦ (extremalNumber n C4 : ℝ)) ~[atTop] fun n ↦ n ^ (3 / 2 : ℝ) / 2 := by
  rw [IsEquivalent, isLittleO_iff]
  intro c hc
  set ε : ℝ := min (c / 4) (1 / 2) with hε_def
  have hε : 0 < ε := by positivity
  have hε1 : ε < 1 := (min_le_right ..).trans_lt (by norm_num)
  have hεc : 1 - c ≤ (1 - ε) ^ 3 := by
    have : ε ≤ c / 4 := min_le_left ..
    nlinarith [sq_nonneg ε]
  filter_upwards [exists_prime_near_sqrt hε, eventually_rpow_pos,
    eventually_n_le_c_rpow hc] with n ⟨q, hq_prime, hq_le, hq_lower⟩ hn_pos hn_ub
  simp only [Pi.sub_apply, norm_eq_abs, abs_of_pos hn_pos]
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le', ← sub_eq_add_neg, ← one_sub_mul]
    calc
      _ ≤ (1 - ε) ^ 3 * (n ^ (3 / 2 : ℝ) / 2) := by nlinarith
      _ ≤ _ := lower_bound_from_prime hε1 hq_lower
      _ ≤ _ := by
        rw [nat_div_two_cast, Nat.cast_le]
        exact extremalNumber_C4_ge_of_isPrimePow_le hq_prime.isPrimePow hq_le
  · rw [sub_le_iff_le_add']
    exact extremalNumber_C4_le_real.trans <| upper_bound_le_rpow_add.trans <|
      add_le_add_right hn_ub _

#print axioms erdos_765
-- 'erdos_765' depends on axioms: [propext, Classical.choice, Erdos765.prime_between, Quot.sound]

end Erdos765
