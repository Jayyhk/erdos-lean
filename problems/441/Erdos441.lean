import Mathlib

namespace Erdos441

/-
# Erdős Problem 441

Let $N\geq 1$. What is the size of the largest $A\subset \{1,\ldots,N\}$ such that
$[a,b]\leq N$ for all $a,b\in A$, where $[a,b]$ is the least common multiple of $a$ and $b$? Is
it attained by choosing all integers in $[1,(N/2)^{1/2}]$ together with all even integers in
$[(N/2)^{1/2},(2N)^{1/2}]$?

Writing $g(N)$ for the size of the largest such $A$, Chen [Ch98] proved
$g(N) \sim \left(\tfrac{9}{8}N\right)^{1/2}$, and Chen and Dai [ChDa07] proved that the
construction is **not** always optimal: for infinitely many $N$ it is strictly smaller than
$g(N)$. `erdos_441` states both. `erdosConstruction N` is the proposed set, written without
square roots as $2a^2 \leq N$, or $a$ even with $a^2 \leq 2N$.

Formalised by Collin Yuanjie Ren in `CollinYuanjieRen/awards` (submission JSP-000360), proving
Chen's asymptotic and reusing the definitions and the non-optimality theorem of
`plby/lean-proofs` (`ErdosProblems/Erdos441.lean`). The 94 modules forming the closure of
`erdos_441` are flattened here in dependency order, with the final theorem renamed from
upstream `erdos_441_complete`.

Declarations that `erdos_441` does not depend on have been removed.
-/

/-! ### Upstream module `MerLeanExperiment/PrefixDot.lean` -/

theorem dot_le_of_prefix_le {n : ℕ} (u v w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hanti : Antitone w)
    (hp : ∀ t : Fin n, ∑ i ∈ Finset.Iic t, u i ≤ ∑ i ∈ Finset.Iic t, v i) :
    ∑ i, u i * w i ≤ ∑ i, v i * w i := by
  induction n with
  | zero => simp
  | succ n ih =>
      let last : Fin (n + 1) := Fin.last n
      let u' : Fin n → ℝ := fun i ↦ u i.castSucc
      let v' : Fin n → ℝ := fun i ↦ v i.castSucc
      let w' : Fin n → ℝ := fun i ↦ w i.castSucc - w last
      have hw' : ∀ i, 0 ≤ w' i := by
        intro i
        exact sub_nonneg.mpr (hanti (Fin.le_last i.castSucc))
      have hanti' : Antitone w' := by
        intro i j hij
        exact sub_le_sub_right (hanti (Fin.castSucc_le_castSucc_iff.mpr hij)) _
      have hp' : ∀ t : Fin n,
          ∑ i ∈ Finset.Iic t, u' i ≤ ∑ i ∈ Finset.Iic t, v' i := by
        intro t
        have h := hp t.castSucc
        have hiic : Finset.Iic t.castSucc = (Finset.Iic t).map Fin.castSuccEmb := by
          ext i
          simp only [Finset.mem_Iic, Finset.mem_map, Fin.castSuccEmb_apply]
          constructor
          · intro hi
            have hv : i.val ≤ t.val := hi
            exact ⟨⟨i, lt_of_le_of_lt hv t.isLt⟩, Fin.mk_le_mk.mpr hv, rfl⟩
          · rintro ⟨j, hj, rfl⟩
            exact Fin.castSucc_le_castSucc_iff.mpr hj
        rw [hiic] at h
        simpa only [Finset.sum_map, Fin.castSuccEmb_apply, u', v'] using h
      have hind := ih u' v' w' hw' hanti' hp'
      have htotal : (∑ i, u i) ≤ ∑ i, v i := by
        have h := hp last
        have hiic : Finset.Iic last = Finset.univ := by
          ext i
          simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
          exact Fin.le_last i
        simpa [hiic] using h
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      change (∑ i : Fin n, u' i * w i.castSucc) + u last * w last ≤
        (∑ i : Fin n, v' i * w i.castSucc) + v last * w last
      have hwdecomp : ∀ i : Fin n, w i.castSucc = w' i + w last := by
        intro i
        dsimp [w']
        ring
      simp_rw [hwdecomp]
      simp_rw [mul_add, Finset.sum_add_distrib]
      have hlast : 0 ≤ w last := hw last
      have htotal' :
          (∑ i : Fin n, u' i) + u last ≤ (∑ i : Fin n, v' i) + v last := by
        simpa [u', v', last, Fin.sum_univ_castSucc] using htotal
      have huMul : (∑ i : Fin n, u' i * w last) = (∑ i : Fin n, u' i) * w last :=
        (Finset.sum_mul Finset.univ u' (w last)).symm
      have hvMul : (∑ i : Fin n, v' i * w last) = (∑ i : Fin n, v' i) * w last :=
        (Finset.sum_mul Finset.univ v' (w last)).symm
      rw [huMul, hvMul]
      nlinarith [mul_le_mul_of_nonneg_right htotal' hlast]

/-! ### Upstream module `MerLeanExperiment/SuffixMax.lean` -/

/-- The largest value of `a` at an index no earlier than `i`. -/
noncomputable def suffixMax {n : ℕ} (a : Fin n → ℝ) (i : Fin n) : ℝ :=
  (Finset.univ.filter (i ≤ ·)).sup' ⟨i, by simp⟩ a

theorem suffix_max_spec {n : ℕ} (a : Fin n → ℝ) :
    (∀ i, a i ≤ suffixMax a i) ∧ Antitone (suffixMax a) ∧
      ∀ i, ∃ j, i ≤ j ∧ a j = suffixMax a i := by
  constructor
  · intro i
    unfold suffixMax
    exact Finset.le_sup' a (by simp)
  constructor
  · intro i j hij
    unfold suffixMax
    apply Finset.sup'_le
    intro k hk
    apply Finset.le_sup' a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact le_trans hij hk
  · intro i
    obtain ⟨j, hj, hmax⟩ :=
      Finset.exists_mem_eq_sup' (s := Finset.univ.filter (i ≤ ·)) ⟨i, by simp⟩ a
    exact ⟨j, (Finset.mem_filter.mp hj).2, hmax.symm⟩

/-! ### Upstream module `MerLeanExperiment/WeightedTransfer.lean` -/

theorem weighted_prefix_transfer_of_forward_moves {n r : ℕ} (α β : Fin n → ℝ)
    (k : Fin r → Fin n → ℕ) (δ : Fin r → ℝ) (B : ℝ)
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i) (hδ : ∀ j, 0 ≤ δ j)
    (hprefix : ∀ t : Fin n,
      ∑ i ∈ Finset.Iic t, β i ≤ ∑ i ∈ Finset.Iic t, ∑ j, δ j * k j i)
    (hmoves : ∀ j (φ : Fin n → Fin n), (∀ i, i ≤ φ i) →
      ∑ i, (k j i : ℝ) * α (φ i) ≤ B) :
    ∑ i, β i * α i ≤ B * ∑ j, δ j := by
  classical
  obtain ⟨hmajor, hanti, hattain⟩ := suffix_max_spec α
  choose φ hφ hφval using hattain
  let M : Fin n → ℝ := suffixMax α
  let c : Fin n → ℝ := fun i ↦ ∑ j, δ j * (k j i : ℝ)
  have hMnonneg : ∀ i, 0 ≤ M i := fun i ↦ (hα i).trans (hmajor i)
  have hβα : (∑ i, β i * α i) ≤ ∑ i, β i * M i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hmajor i) (hβ i)
  have hβc : (∑ i, β i * M i) ≤ ∑ i, c i * M i := by
    apply dot_le_of_prefix_le β c M hMnonneg hanti
    intro t
    simpa [c] using hprefix t
  have hmoveM : ∀ j, (∑ i, (k j i : ℝ) * M i) ≤ B := by
    intro j
    have hj := hmoves j φ hφ
    simpa [M, hφval] using hj
  have hexchange :
      (∑ i, c i * M i) = ∑ j, δ j * ∑ i, (k j i : ℝ) * M i := by
    simp only [c, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr with j
    rw [Finset.mul_sum]
    congr with i
    ring
  calc
    (∑ i, β i * α i) ≤ ∑ i, β i * M i := hβα
    _ ≤ ∑ i, c i * M i := hβc
    _ = ∑ j, δ j * ∑ i, (k j i : ℝ) * M i := hexchange
    _ ≤ ∑ j, δ j * B := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hmoveM j) (hδ j)
    _ = B * ∑ j, δ j := by rw [Finset.mul_sum]; simp [mul_comm]

/-! ### Upstream module `MerLeanExperiment/FiniteOrderTransfer.lean` -/

theorem sum_prefix_order_iso {I : Type*} [Fintype I] [LinearOrder I] {n : ℕ}
    (e : Fin n ≃o I) (f : I → ℝ) (t : Fin n) :
    (∑ i ∈ Finset.Iic t, f (e i)) = ∑ i : I, if i ≤ e t then f i else 0 := by
  classical
  calc
    _ = ∑ i : Fin n, if i ≤ t then f (e i) else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp
    _ = _ := Fintype.sum_equiv e.toEquiv _ _ (fun i => by simp)

theorem weighted_finite_order_transfer {I J : Type*} [Fintype I] [LinearOrder I]
    [Fintype J] (alpha beta : I → ℝ) (k : J → I → ℕ) (delta : J → ℝ) (B : ℝ)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i) (hdelta : ∀ j, 0 ≤ delta j)
    (hprefix : ∀ t : I, (∑ i : I, if i ≤ t then beta i else 0) ≤
      ∑ i : I, if i ≤ t then ∑ j : J, delta j * k j i else 0)
    (hmoves : ∀ j (phi : I → I), (∀ i, i ≤ phi i) →
      (∑ i : I, (k j i : ℝ) * alpha (phi i)) ≤ B) :
    (∑ i : I, beta i * alpha i) ≤ B * ∑ j : J, delta j := by
  classical
  let e : Fin (Fintype.card I) ≃o I := monoEquivOfFin I rfl
  let d : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have hsumI (f : I → ℝ) : (∑ i, f (e i)) = ∑ i : I, f i :=
    Fintype.sum_equiv e.toEquiv _ _ (fun _ => rfl)
  have hsumJ (f : J → ℝ) : (∑ j, f (d j)) = ∑ j : J, f j :=
    Fintype.sum_equiv d _ _ (fun _ => rfl)
  have hpre (t : Fin (Fintype.card I)) :
      (∑ i ∈ Finset.Iic t, beta (e i)) ≤
        ∑ i ∈ Finset.Iic t, ∑ j : Fin (Fintype.card J), delta (d j) * k (d j) (e i) := by
    have heq : (∑ i ∈ Finset.Iic t,
        ∑ j : Fin (Fintype.card J), delta (d j) * k (d j) (e i)) =
        ∑ i ∈ Finset.Iic t, ∑ j : J, delta j * k j (e i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hsumJ (fun j => delta j * k j (e i))
    rw [heq, sum_prefix_order_iso e beta t,
      sum_prefix_order_iso e (fun i => ∑ j : J, delta j * k j i) t]
    exact hprefix (e t)
  have hmove (j : Fin (Fintype.card J))
      (phi : Fin (Fintype.card I) → Fin (Fintype.card I)) (hphi : ∀ i, i ≤ phi i) :
      (∑ i, (k (d j) (e i) : ℝ) * alpha (e (phi i))) ≤ B := by
    let psi : I → I := fun i => e (phi (e.symm i))
    have hpsi (i : I) : i ≤ psi i := by
      have hh := e.monotone (hphi (e.symm i))
      simpa [psi] using hh
    have hh := hmoves (d j) psi hpsi
    have heq : (∑ i, (k (d j) (e i) : ℝ) * alpha (e (phi i))) =
        ∑ i : I, (k (d j) i : ℝ) * alpha (psi i) := by
      exact Fintype.sum_equiv e.toEquiv _ _ (fun i => by simp [psi])
    rw [heq]
    exact hh
  have hh := weighted_prefix_transfer_of_forward_moves
    (fun i => alpha (e i)) (fun i => beta (e i)) (fun j i => k (d j) (e i))
    (fun j => delta (d j)) B (fun i => halpha (e i)) (fun i => hbeta (e i))
    (fun j => hdelta (d j)) hpre hmove
  rw [hsumI (fun i => beta i * alpha i), hsumJ delta] at hh
  exact hh

/-! ### Upstream module `MerLeanExperiment/GridPoints.lean` -/

/-- The explicit integer sets B(alpha,beta) from Chen, Section 3. -/
noncomputable def gridPoints (α β : ℝ) : Finset ℤ :=
  Finset.Icc 1 ⌊α * β⌋ ∪ Finset.Icc ⌈-min (α * β) (β / α - 1)⌉ 0

theorem mem_gridPoints (α β : ℝ) (z : ℤ) : z ∈ gridPoints α β ↔
    (1 ≤ (z : ℝ) ∧ (z : ℝ) ≤ α * β) ∨
      (-min (α * β) (β / α - 1) ≤ (z : ℝ) ∧ (z : ℝ) ≤ 0) := by
  simp only [gridPoints, Finset.mem_union, Finset.mem_Icc,
    Int.le_floor, Int.ceil_le]
  norm_cast

theorem grid_points_separation (α β γ : ℝ) (hα : 0 < α)
    (hαβ : α ≤ β) (hαγ : α ≤ γ) (a b : ℤ)
    (ha : a ∈ gridPoints α β) (hb : b ∈ gridPoints α γ) :
    |((a - b : ℤ) : ℝ)| ≤ β * γ := by
  have hβ : 0 ≤ β := le_trans (le_of_lt hα) hαβ
  have hγ : 0 ≤ γ := le_trans (le_of_lt hα) hαγ
  have hbg : α * β ≤ β * γ := by nlinarith [mul_nonneg hβ (sub_nonneg.mpr hαγ)]
  have hgb : α * γ ≤ β * γ := mul_le_mul_of_nonneg_right hαβ hγ
  have hmix (u v x y : ℝ) (hv : α ≤ v)
      (hx1 : 1 ≤ x) (hxu : x ≤ α * u)
      (hy : -min (α * v) (v / α - 1) ≤ y) : x - y ≤ u * v := by
    have huv : 0 ≤ (α * u - 1) * (v - α) :=
      mul_nonneg (by linarith) (sub_nonneg.mpr hv)
    have hbound : x - y ≤ α * u + v / α - 1 := by
      have hm := min_le_right (α * v) (v / α - 1)
      linarith
    have hd : v / α * α = v := div_mul_cancel₀ v (ne_of_gt hα)
    have ht : α * u + v / α - 1 ≤ u * v := by
      nlinarith
    exact le_trans hbound ht
  rw [mem_gridPoints] at ha hb
  push_cast
  rw [abs_le]
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · constructor <;> linarith
  · have hab := hmix β γ a b hαγ ha.1 ha.2 hb.1
    have hnonpos := hb.2
    constructor <;> linarith [mul_nonneg hβ hγ]
  · have hba := hmix γ β b a hαβ hb.1 hb.2 ha.1
    constructor <;> nlinarith [mul_nonneg hβ hγ]
  · have ham := min_le_left (α * β) (β / α - 1)
    have hbm := min_le_left (α * γ) (γ / α - 1)
    constructor <;> linarith

/-! ### Upstream module `MerLeanExperiment/GridPointCount.lean` -/

theorem grid_points_card (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    ((gridPoints α β).card : ℤ) =
      ⌊α * β⌋ + ⌊min (α * β) (β / α - 1)⌋ + 1 := by
  let A : ℤ := ⌊α * β⌋
  let C : ℤ := ⌊min (α * β) (β / α - 1)⌋
  have hβ : 0 ≤ β := le_trans (le_of_lt hα) hαβ
  have hprod : 0 ≤ α * β := mul_nonneg (le_of_lt hα) hβ
  have hdiv : 1 ≤ β / α := (le_div_iff₀ hα).mpr (by simpa using hαβ)
  have hmin : 0 ≤ min (α * β) (β / α - 1) := by
    exact le_min hprod (by linarith)
  have hA : 0 ≤ A := by exact Int.floor_nonneg.mpr hprod
  have hC : 0 ≤ C := by exact Int.floor_nonneg.mpr hmin
  have hceil : ⌈-min (α * β) (β / α - 1)⌉ = -C := by
    simp [C, Int.ceil_neg]
  have hdis : Disjoint (Finset.Icc (1 : ℤ) A) (Finset.Icc (-C) 0) := by
    rw [Finset.disjoint_left]
    intro z hzpos hzneg
    simp only [Finset.mem_Icc] at hzpos hzneg
    omega
  have hcardA : ((Finset.Icc (1 : ℤ) A).card : ℤ) = A + 1 - 1 :=
    Int.card_Icc_of_le 1 A (by omega)
  have hcardC : ((Finset.Icc (-C) 0).card : ℤ) = 0 + 1 - (-C) :=
    Int.card_Icc_of_le (-C) 0 (by omega)
  rw [gridPoints, hceil, Finset.card_union_of_disjoint hdis]
  rw [Nat.cast_add, hcardA, hcardC]
  dsimp [A, C]
  omega

theorem grid_points_mono (α β γ : ℝ) (hα : 0 < α) (hβγ : β ≤ γ) :
    gridPoints α β ⊆ gridPoints α γ := by
  intro z hz
  rw [mem_gridPoints] at hz ⊢
  have hmul : α * β ≤ α * γ := mul_le_mul_of_nonneg_left hβγ (le_of_lt hα)
  have hdiv : β / α ≤ γ / α := div_le_div_of_nonneg_right hβγ (le_of_lt hα)
  have hmin : min (α * β) (β / α - 1) ≤ min (α * γ) (γ / α - 1) :=
    min_le_min hmul (by linarith)
  rcases hz with hz | hz
  · exact Or.inl ⟨hz.1, hz.2.trans hmul⟩
  · exact Or.inr ⟨by linarith, hz.2⟩

/-! ### Upstream module `MerLeanExperiment/GridDefinitions.lean` -/

/-- Chen's geometric ratio; the proof uses only positive L. -/
noncomputable def gridQ (L : ℕ) : ℝ := (2 : ℝ) ^ (1 / (2 * (L : ℝ)))

noncomputable def gridEta : ℝ := (10 - 7 * Real.sqrt 2) / 32

/-- Actual nested integer sets, with integer exponents throughout. -/
noncomputable def gridA (q : ℝ) (i j : ℤ) : Finset ℤ :=
  if j ≤ i then gridPoints (q ^ j) (q ^ i) else ∅

/-- Column L is the exceptional singleton column from Chen, not a set difference. -/
noncomputable def gridCount (q : ℝ) (L : ℕ) (i j : ℤ) : ℕ :=
  if j = (L : ℤ) then (if i = 0 then 1 else 0)
  else if j < (L : ℤ) then (gridA q i j \ gridA q (i - 1) j).card else 0

noncomputable def gridBeta (q : ℝ) (L : ℕ) (i : ℤ) : ℝ :=
  if i < (L : ℤ) then q ^ i * (q - 1)
  else (1 + gridEta) * q ^ i * (q - 1)

noncomputable def gridDelta (q : ℝ) (L : ℕ) (j : ℤ) : ℝ :=
  if j < 0 then q ^ j * (q - 1)
  else if j < (L : ℤ) then (q - 1) / 2 * (q ^ j - q ^ (-j - 1))
  else if j = (L : ℤ) then 1 - q ^ (-1 : ℤ) else 0

noncomputable def gridBetaPrefix (q : ℝ) (L : ℕ) (T t : ℤ) : ℝ :=
  ∑ i ∈ Finset.Icc (-T) t, gridBeta q L i

noncomputable def gridCapacityPrefix (q : ℝ) (L : ℕ) (T t : ℤ) : ℝ :=
  ∑ i ∈ Finset.Icc (-T) t,
    ∑ j ∈ Finset.Icc (-T) (L : ℤ), gridDelta q L j * (gridCount q L i j : ℝ)

/-! ### Upstream module `MerLeanExperiment/GridFiberDefinitions.lean` -/

noncomputable def gridFiber (q : ℝ) (L : ℕ) (i j : ℤ) : Finset ℤ :=
  if j = (L : ℤ) then (if i = 0 then {1} else ∅)
  else if j < (L : ℤ) then gridA q i j \ gridA q (i - 1) j else ∅

/-! ### Upstream module `MerLeanExperiment/GridColumns.lean` -/

theorem grid_column_mono (q : ℝ) (hq : 1 < q) (i i' j : ℤ) (hii : i ≤ i') :
    gridA q i j ⊆ gridA q i' j := by
  intro z hz
  by_cases hji : j ≤ i
  · have hji' : j ≤ i' := hji.trans hii
    have hz' : z ∈ gridPoints (q ^ j) (q ^ i) := by simpa [gridA, hji] using hz
    simpa [gridA, hji'] using
      grid_points_mono (q ^ j) (q ^ i) (q ^ i') (zpow_pos (by linarith) _)
        (zpow_le_zpow_right₀ (le_of_lt hq) hii) hz'
  · simp [gridA, hji] at hz

theorem zero_mem_grid_column (q : ℝ) (hq : 1 < q) (i j : ℤ) (hji : j ≤ i) :
    (0 : ℤ) ∈ gridA q i j := by
  simp only [gridA, hji, ↓reduceIte, mem_gridPoints]
  right
  have hqpos : 0 < q := by linarith
  have hqjpos : 0 < q ^ j := zpow_pos hqpos _
  have hpowle : q ^ j ≤ q ^ i := zpow_le_zpow_right₀ (le_of_lt hq) hji
  have hratio : 1 ≤ q ^ i / q ^ j := (le_div_iff₀ hqjpos).mpr (by simpa using hpowle)
  have hprod : 0 ≤ q ^ j * q ^ i := mul_nonneg (zpow_nonneg hqpos.le _) (zpow_nonneg hqpos.le _)
  constructor
  · have : 0 ≤ min (q ^ j * q ^ i) (q ^ i / q ^ j - 1) :=
      le_min hprod (by linarith)
    linarith
  · norm_num

theorem zero_one_subset_grid_column (q : ℝ) (hq : 1 < q) (i j : ℤ)
    (hji : j ≤ i) (hsum : 0 ≤ i + j) :
    ({0, 1} : Finset ℤ) ⊆ gridA q i j := by
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact zero_mem_grid_column q hq i j hji
  · simp only [gridA, hji, ↓reduceIte, mem_gridPoints]
    left
    constructor
    · norm_num
    · have hqpos : 0 < q := by linarith
      have hone : 1 ≤ q ^ (j + i) := one_le_zpow₀ (le_of_lt hq) (by omega)
      rw [zpow_add₀ hqpos.ne'] at hone
      exact_mod_cast hone

/-! ### Upstream module `MerLeanExperiment/GridFibers.lean` -/

theorem grid_fiber_card (q : ℝ) (L : ℕ) (i j : ℤ) :
    (gridFiber q L i j).card = gridCount q L i j := by
  simp only [gridFiber, gridCount]
  split_ifs <;> rfl

theorem grid_fibers_disjoint (q : ℝ) (hq : 1 < q) (L : ℕ) (i k j : ℤ)
    (hik : i ≠ k) : Disjoint (gridFiber q L i j) (gridFiber q L k j) := by
  by_cases hjL : j = (L : ℤ)
  · subst j
    simp only [gridFiber, ↓reduceIte]
    by_cases hi : i = 0
    · subst i
      have hk : k ≠ 0 := by
        intro hk
        apply hik
        omega
      simp [hk]
    · simp [hi]
  · by_cases hj : j < (L : ℤ)
    · simp only [gridFiber, hjL, hj, ↓reduceIte]
      apply Finset.disjoint_left.mpr
      intro z hzi hzk
      have hziA := (Finset.mem_sdiff.mp hzi).1
      have hzkA := (Finset.mem_sdiff.mp hzk).1
      have hziN := (Finset.mem_sdiff.mp hzi).2
      have hzkN := (Finset.mem_sdiff.mp hzk).2
      rcases lt_or_gt_of_ne hik with hik' | hki'
      · exact hzkN (grid_column_mono q hq i (k - 1) j (by omega) hziA)
      · exact hziN (grid_column_mono q hq k (i - 1) j (by omega) hzkA)
    · simp [gridFiber, hjL, hj]

theorem grid_fiber_separation (q : ℝ) (hq : 1 < q) (L : ℕ)
    (i k j z w : ℤ) (hz : z ∈ gridFiber q L i j)
    (hw : w ∈ gridFiber q L k j) :
    ((z - w).natAbs : ℝ) ≤ q ^ i * q ^ k := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  by_cases hjL : j = (L : ℤ)
  · subst j
    simp only [gridFiber, ↓reduceIte] at hz hw
    split at hz <;> split at hw <;> simp_all
  · have hj : j < (L : ℤ) := by
      by_contra hn
      have : (L : ℤ) < j := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hjL)
      simp [gridFiber, hjL, not_lt.mpr this.le] at hz
    have hz' : z ∈ gridA q i j \ gridA q (i - 1) j := by
      simpa only [gridFiber, hjL, hj, ↓reduceIte] using hz
    have hw' : w ∈ gridA q k j \ gridA q (k - 1) j := by
      simpa only [gridFiber, hjL, hj, ↓reduceIte] using hw
    have hzA : z ∈ gridA q i j := (Finset.mem_sdiff.mp hz').1
    have hwA : w ∈ gridA q k j := (Finset.mem_sdiff.mp hw').1
    have hji : j ≤ i := by
      by_contra hn
      rw [gridA, if_neg hn] at hzA
      simp at hzA
    have hjk : j ≤ k := by
      by_contra hn
      rw [gridA, if_neg hn] at hwA
      simp at hwA
    have hzP : z ∈ gridPoints (q ^ j) (q ^ i) := by
      simpa [gridA, hji] using hzA
    have hwP : w ∈ gridPoints (q ^ j) (q ^ k) := by
      simpa [gridA, hjk] using hwA
    have hsep := grid_points_separation (q ^ j) (q ^ i) (q ^ k)
      (zpow_pos hq0 j)
      (zpow_le_zpow_right₀ hq.le hji)
      (zpow_le_zpow_right₀ hq.le hjk) z w hzP hwP
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact hsep

theorem grid_fiber_sum {I : Type*} [Fintype I] (q : ℝ) (L : ℕ) (j : ℤ)
    (row : I → ℤ) (f : I → ℝ) :
    (∑ e : Σ i : I, {z : ℤ // z ∈ gridFiber q L (row i) j}, f e.1) =
      ∑ i : I, (gridCount q L (row i) j : ℝ) * f i := by
  classical
  rw [Fintype.sum_sigma]
  apply Fintype.sum_congr
  intro i
  simp [grid_fiber_card, mul_comm]

theorem grid_fiber_label_injective {I : Type*} (q : ℝ) (hq : 1 < q) (L : ℕ)
    (j : ℤ) (row : I → ℤ) (hrow : Function.Injective row) :
    Function.Injective
      (fun e : Σ i : I, {z : ℤ // z ∈ gridFiber q L (row i) j} => e.2.val) := by
  rintro ⟨i, z⟩ ⟨k, w⟩ heq
  change z.val = w.val at heq
  have hr : row i = row k := by
    by_contra hne
    have hd := grid_fibers_disjoint q hq L (row i) (row k) j hne
    exact (Finset.disjoint_left.mp hd z.property (by
      rw [heq]
      exact w.property))
  have hik : i = k := hrow hr
  subst k
  congr 1
  exact Subtype.ext heq

/-! ### Upstream module `MerLeanExperiment/CyclicAverage.lean` -/

theorem exists_cyclic_average (m k : ℕ) (hm : 0 < m) (hk : k ≤ m)
    (f : Fin m → ℝ) :
    ∃ offset : Fin m,
      Function.Injective (fun h : Fin k => offset + Fin.castLE hk h) ∧
      (k : ℝ) / m * (∑ s : Fin m, f s) ≤
        ∑ h : Fin k, f (offset + Fin.castLE hk h) := by
  classical
  let : NeZero m := ⟨by omega⟩
  have hshift (h : Fin k) :
      (∑ offset : Fin m, f (offset + Fin.castLE hk h)) = ∑ s : Fin m, f s := by
    exact Fintype.sum_equiv (Equiv.addRight (Fin.castLE hk h)) _ _ (fun _ => rfl)
  have htotal : (∑ offset : Fin m, ∑ h : Fin k, f (offset + Fin.castLE hk h)) =
      (k : ℝ) * ∑ s : Fin m, f s := by
    rw [Finset.sum_comm]
    simp_rw [hshift]
    simp
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have havg :
      (∑ _offset : Fin m, (k : ℝ) / m * (∑ s : Fin m, f s)) ≤
        ∑ offset : Fin m, ∑ h : Fin k, f (offset + Fin.castLE hk h) := by
    rw [htotal]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hmR]
    ring_nf
    exact le_rfl
  obtain ⟨offset, _, hoff⟩ := Finset.exists_le_of_sum_le
    (show (Finset.univ : Finset (Fin m)).Nonempty from ⟨⟨0, hm⟩, Finset.mem_univ _⟩) havg
  refine ⟨offset, ?_, hoff⟩
  intro i j hij
  exact Fin.castLE_injective hk (add_left_cancel hij)

/-! ### Upstream module `MerLeanExperiment/FiberAverage.lean` -/

theorem exists_injective_average {I : Type*} [Fintype I] (m : ℕ) (hm : 0 < m)
    (hk : Fintype.card I ≤ m) (f : Fin m → ℝ) :
    ∃ s : I → Fin m, Function.Injective s ∧
      (Fintype.card I : ℝ) / m * (∑ j : Fin m, f j) ≤ ∑ i : I, f (s i) := by
  classical
  obtain ⟨offset, hinj, hbound⟩ := exists_cyclic_average m (Fintype.card I) hm hk f
  let e := Fintype.equivFin I
  let s : I → Fin m := fun i => offset + Fin.castLE hk (e i)
  refine ⟨s, hinj.comp e.injective, ?_⟩
  have heq : (∑ i : I, f (s i)) =
      ∑ h : Fin (Fintype.card I), f (offset + Fin.castLE hk h) := by
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [heq]
  exact hbound

/-! ### Upstream module `MerLeanExperiment/FactorialQuotient.lean` -/

/-- Every prime at most `M` divides the quotient `M! / d` when both `d` and
`2d` occur as distinct factors of the factorial. -/
theorem factorial_quotient_small_prime (M d p : ℕ) (hd : 0 < d)
    (hsize : 2 * d ≤ M) (hp : p.Prime) (hpM : p ≤ M) :
    p ∣ M.factorial / d := by
  have hdM : d ≤ M := by omega
  have hdFact : d ∣ M.factorial := Nat.dvd_factorial hd hdM
  by_cases hpd : p ∣ d
  · have hidx : d - 1 ≠ 2 * d - 1 := by omega
    have hsubset : ({d - 1, 2 * d - 1} : Finset ℕ) ⊆ Finset.range M := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> simp <;> omega
    have hpair := Finset.prod_dvd_prod_of_subset
      ({d - 1, 2 * d - 1} : Finset ℕ) (Finset.range M) (fun i => i + 1) hsubset
    have hpairValue :
        (∏ i ∈ ({d - 1, 2 * d - 1} : Finset ℕ), (i + 1)) = d * (2 * d) := by
      simp [hidx, Nat.sub_add_cancel (by omega : 1 ≤ d),
        Nat.sub_add_cancel (by omega : 1 ≤ 2 * d)]
    rw [hpairValue, ← Nat.factorial_eq_prod_range_add_one] at hpair
    have hpdPair : p * d ∣ d * (2 * d) := by
      obtain ⟨k, hk⟩ := hpd
      refine ⟨2 * k, ?_⟩
      rw [hk]
      ring
    have hpdFact : p * d ∣ M.factorial := hpdPair.trans hpair
    apply (Nat.dvd_div_iff_mul_dvd hdFact).2
    simpa [Nat.mul_comm] using hpdFact
  · have hpFact : p ∣ M.factorial := hp.dvd_factorial.mpr hpM
    have hcop : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hpd).symm
    apply (Nat.dvd_div_iff_mul_dvd hdFact).2
    exact hcop.mul_dvd_of_dvd_of_dvd hdFact hpFact

/-- Integer form of `factorial_quotient_small_prime`, including negative
denominators with their actual Euclidean-division semantics. -/
theorem factorial_int_quotient_small_prime (M p : ℕ) (d : ℤ) (hd : d ≠ 0)
    (hsize : 2 * d.natAbs ≤ M) (hp : p.Prime) (hpM : p ≤ M) :
    (p : ℤ) ∣ (M.factorial : ℤ) / d := by
  have hdAbs : 0 < d.natAbs := Int.natAbs_pos.mpr hd
  have hnat := factorial_quotient_small_prime M d.natAbs p hdAbs hsize hp hpM
  have hdM : d.natAbs ≤ M := by omega
  have hdFact : d.natAbs ∣ M.factorial := Nat.dvd_factorial hdAbs hdM
  have hmulNat : d.natAbs * p ∣ M.factorial :=
    (Nat.dvd_div_iff_mul_dvd hdFact).1 hnat
  have hmulInt : (d.natAbs : ℤ) * (p : ℤ) ∣ (M.factorial : ℤ) := by
    exact_mod_cast hmulNat
  have hdMul : d * (p : ℤ) ∣ (M.factorial : ℤ) := by
    rcases le_total 0 d with hdNonneg | hdNonpos
    · simpa [Int.natAbs_of_nonneg hdNonneg] using hmulInt
    · simpa [Int.natCast_natAbs, abs_of_nonpos hdNonpos] using hmulInt
  exact Int.dvd_div_of_mul_dvd hdMul

/-! ### Upstream module `MerLeanExperiment/FactorialLinear.lean` -/

theorem factorial_linear_spec (M : ℕ) (d : ℤ) (hd : d ≠ 0)
    (hsize : 2 * d.natAbs ≤ M) (ell : ℤ) :
    let A : ℤ := (M.factorial : ℤ) / d
    d * A = (M.factorial : ℤ) ∧ IsCoprime A (1 - A * ell) ∧
      ∀ p : ℕ, p.Prime → p ≤ M → ∀ n : ℤ,
        ¬ (p : ℤ) ∣ A * n + (1 - A * ell) := by
  dsimp only
  have hdNat : d.natAbs ∣ M.factorial :=
    Nat.dvd_factorial (Int.natAbs_pos.mpr hd) (by omega)
  have hdInt : d ∣ (M.factorial : ℤ) := by
    have hcast : (d.natAbs : ℤ) ∣ (M.factorial : ℤ) := by exact_mod_cast hdNat
    rcases le_total 0 d with hdpos | hdneg
    · simpa [Int.natAbs_of_nonneg hdpos] using hcast
    · simpa [Int.natCast_natAbs, abs_of_nonpos hdneg] using hcast
  constructor
  · exact Int.mul_ediv_cancel' hdInt
  constructor
  · exact ⟨ell, 1, by ring⟩
  · intro p hp hpM n hdiv
    have hA := factorial_int_quotient_small_prime M p d hd hsize hp hpM
    have hAn : (p : ℤ) ∣ ((M.factorial : ℤ) / d) * (n - ell) :=
      dvd_mul_of_dvd_left hA _
    have hid : ((M.factorial : ℤ) / d) * n + (1 - ((M.factorial : ℤ) / d) * ell) =
        ((M.factorial : ℤ) / d) * (n - ell) + 1 := by ring
    rw [hid] at hdiv
    have hpone : (p : ℤ) ∣ 1 := (dvd_add_right hAn).mp hdiv
    exact hp.not_dvd_one (by exact_mod_cast hpone)

/-! ### Upstream module `MerLeanExperiment/ShiftDefinitions.lean` -/

def shiftedPoint {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ) (i : Fin K) : ℤ :=
  (M.factorial : ℤ) * ell i + r i

def shiftFactor {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ) (i j : Fin K) : ℤ :=
  ((M.factorial : ℤ) / (r j - r i)) * (ell j - ell i) + 1

def shiftPairs (K : ℕ) : Finset (Fin K × Fin K) :=
  Finset.univ.filter fun ij => ij.1 < ij.2

def shiftProduct {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ) : ℤ :=
  ∏ ij ∈ shiftPairs K, shiftFactor M r ell ij.1 ij.2

def shiftProductNat {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ) : ℕ :=
  (shiftProduct M r ell).natAbs

/-! ### Upstream module `MerLeanExperiment/CollisionDefinitions.lean` -/

def shiftParityWeight (r s : ℤ) : ℕ :=
  if Odd r ∧ Odd s then 2 else 1

/-! ### Upstream module `MerLeanExperiment/TranslationDefinitions.lean` -/

noncomputable def goodTranslateUnion {K : ℕ} (A : Finset ℕ) (D : ℕ)
    (y : Fin K → ℤ) (H : ℤ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 H).biUnion fun h =>
    (Finset.univ.filter fun i => (y i + 2 * h).natAbs ∈ A ∧
      Nat.Coprime (y i + 2 * h).natAbs D).image fun i => (y i + 2 * h).natAbs

/-! ### Upstream module `MerLeanExperiment/CellDefinitions.lean` -/

noncomputable def realIntIoc (a b : ℝ) : Finset ℤ :=
  Finset.Ioc ⌊a⌋ ⌊b⌋

/-! ### Upstream module `MerLeanExperiment/PackingCellDefinitions.lean` -/

noncomputable def packingCell {K : ℕ} (A : Finset ℕ) (r : Fin K → ℤ)
    (c : Fin K → ℝ) (delta R : ℝ) (i : Fin K) : Finset ℕ := by
  classical
  exact A.filter fun n => c i * R < (n : ℝ) ∧ (n : ℝ) ≤ (c i + delta) * R ∧
    Even ((n : ℤ) - r i)

noncomputable def packingCellUnion {K : ℕ} (A : Finset ℕ) (r : Fin K → ℤ)
    (c : Fin K → ℝ) (delta R : ℝ) : Finset ℕ := by
  classical
  exact Finset.univ.biUnion (packingCell A r c delta R)

noncomputable def packingBadPoints (A : Finset ℕ) (D : ℕ) (B R : ℝ) : Finset ℕ := by
  classical
  exact A.filter fun n => (n : ℝ) ≤ B * R ∧ ¬ Nat.Coprime n D

/-! ### Upstream module `MerLeanExperiment/DensityDefinitions.lean` -/

noncomputable def parityDensity (A : Finset ℕ) (a b R : ℝ) (r : ℤ) : ℝ := by
  classical
  exact ((A.filter fun n : ℕ => a * R < (n : ℝ) ∧ (n : ℝ) ≤ b * R ∧
    Even ((n : ℤ) - r)).card : ℝ) / ((b - a) * R)

noncomputable def intervalDensity (A : Finset ℕ) (a b R : ℝ) : ℝ := by
  classical
  exact ((A.filter fun n : ℕ => a * R < (n : ℝ) ∧ (n : ℝ) ≤ b * R).card : ℝ) /
    ((b - a) * R)

/-! ### Upstream module `MerLeanExperiment/ParityRegionDefinitions.lean` -/

noncomputable def parityRegion (A : Finset ℕ) (a b R : ℝ) (r : ℤ) : Finset ℕ := by
  classical
  exact A.filter fun n : ℕ => a * R < (n : ℝ) ∧ (n : ℝ) ≤ b * R ∧
    Even ((n : ℤ) - r)

noncomputable def consecutiveCell (A : Finset ℕ) (a delta R : ℝ) (r : ℤ)
    (s : ℕ) : Finset ℕ :=
  parityRegion A (a + s * delta) (a + (s + 1) * delta) R r

/-! ### Upstream module `MerLeanExperiment/ParityGroupDefinitions.lean` -/

def parityRep (v : Bool) : ℤ := if v then 0 else 1

def ownerParity {K l : ℕ} (o : Fin K → Fin l) (r : Fin K → ℤ)
    (i : Fin K) : Fin l × Bool := (o i, decide (Even (r i)))

/-! ### Upstream module `MerLeanExperiment/SelectedMeshCells.lean` -/

theorem selected_mesh_bounds {K l : ℕ} (a b : Fin l → ℝ)
    (o : Fin K → Fin l) (m : Fin l → ℕ) (s : ∀ i : Fin K, Fin (m (o i)))
    (delta : ℝ) (hd : 0 ≤ delta)
    (hmesh : ∀ j, (m j : ℝ) * delta ≤ b j - a j) :
    ∀ i, a (o i) ≤ a (o i) + (s i).val * delta ∧
      a (o i) + (s i).val * delta + delta ≤ b (o i) := by
  intro i
  have hn : (0 : ℝ) ≤ (s i).val := by positivity
  have hi : ((s i).val : ℝ) + 1 ≤ m (o i) := by exact_mod_cast (s i).isLt
  have hh := mul_le_mul_of_nonneg_right hi hd
  constructor
  · nlinarith [mul_nonneg hn hd]
  · nlinarith [hmesh (o i)]

theorem selected_mesh_cells_card {K l : ℕ} (A : Finset ℕ)
    (a b : Fin l → ℝ) (o : Fin K → Fin l) (r : Fin K → ℤ)
    (m : Fin l → ℕ) (s : ∀ i : Fin K, Fin (m (o i))) (delta R : ℝ)
    (hd : 0 < delta) (hR : 0 < R)
    (hmesh : ∀ j, (m j : ℝ) * delta ≤ b j - a j)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j)))
    (hs : ∀ i j, ownerParity o r i = ownerParity o r j →
      (s i).val = (s j).val → i = j) :
    (packingCellUnion A r (fun i => a (o i) + (s i).val * delta) delta R).card =
      ∑ i : Fin K,
        (packingCell A r (fun i => a (o i) + (s i).val * delta) delta R i).card := by
  classical
  let c := fun i => a (o i) + (s i).val * delta
  have hb := selected_mesh_bounds a b o m s delta hd.le hmesh
  have hpw : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint
      (packingCell A r c delta R) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have hi := (Finset.mem_filter.mp hn).2
    have hj := (Finset.mem_filter.mp hn').2
    have hoi : (n : ℝ) / R ∈ Set.Ioc (a (o i)) (b (o i)) := by
      constructor
      · apply (lt_div_iff₀ hR).mpr
        exact (mul_le_mul_of_nonneg_right (hb i).1 hR.le).trans_lt hi.1
      · apply (div_le_iff₀ hR).mpr
        exact hi.2.1.trans (mul_le_mul_of_nonneg_right (hb i).2 hR.le)
    have hoj : (n : ℝ) / R ∈ Set.Ioc (a (o j)) (b (o j)) := by
      constructor
      · apply (lt_div_iff₀ hR).mpr
        exact (mul_le_mul_of_nonneg_right (hb j).1 hR.le).trans_lt hj.1
      · apply (div_le_iff₀ hR).mpr
        exact hj.2.1.trans (mul_le_mul_of_nonneg_right (hb j).2 hR.le)
    have ho : o i = o j := by
      by_contra h
      exact Set.disjoint_left.mp (hdisj (o i) (o j) h) hoi hoj
    have hpar : Even (r i) ↔ Even (r j) :=
      (Int.even_sub.mp hi.2.2).symm.trans (Int.even_sub.mp hj.2.2)
    have hg : ownerParity o r i = ownerParity o r j := by
      simp only [ownerParity, Prod.mk.injEq]
      exact ⟨ho, by simp only [hpar]⟩
    have hindex : (s i).val = (s j).val := by
      by_contra hnij
      rcases lt_or_gt_of_ne hnij with hlt | hgt
      · have hsle : ((s i).val : ℝ) + 1 ≤ (s j).val := by exact_mod_cast hlt
        have hcle : c i + delta ≤ c j := by
          dsimp [c]
          rw [congrArg a ho]
          nlinarith [mul_le_mul_of_nonneg_right hsle hd.le]
        have hscale := mul_le_mul_of_nonneg_right hcle hR.le
        linarith [hi.2.1, hj.1]
      · have hsle : ((s j).val : ℝ) + 1 ≤ (s i).val := by exact_mod_cast hgt
        have hcle : c j + delta ≤ c i := by
          dsimp [c]
          rw [congrArg a ho]
          nlinarith [mul_le_mul_of_nonneg_right hsle hd.le]
        have hscale := mul_le_mul_of_nonneg_right hcle hR.le
        linarith [hj.2.1, hi.1]
    exact hij (hs i j hg hindex)
  exact Finset.card_biUnion hpw

/-! ### Upstream module `MerLeanExperiment/ParityGroups.lean` -/

theorem even_sub_parity_rep (n r : ℤ) :
    Even (n - r) ↔ Even (n - parityRep (decide (Even r))) := by
  by_cases hr : Even r <;> simp [Int.even_sub, parityRep, hr]

theorem parity_region_rep (A : Finset ℕ) (a b R : ℝ) (r : ℤ) :
    parityRegion A a b R r =
      parityRegion A a b R (parityRep (decide (Even r))) := by
  classical
  ext n
  simp only [parityRegion, Finset.mem_filter, even_sub_parity_rep (n : ℤ) r]

theorem density_parity_partition (A : Finset ℕ) (a b R : ℝ) (r : ℤ) :
    parityDensity A a b R r + parityDensity A a b R (r + 1) =
      intervalDensity A a b R := by
  classical
  let F := A.filter fun n : ℕ => a * R < (n : ℝ) ∧ (n : ℝ) ≤ b * R
  have hfilter (s : ℤ) :
      (A.filter fun n : ℕ => a * R < (n : ℝ) ∧ (n : ℝ) ≤ b * R ∧
        Even ((n : ℤ) - s)) = F.filter (fun n : ℕ => Even ((n : ℤ) - s)) := by
    ext n
    simp [F, and_assoc]
  have hnext (n : ℕ) : Even ((n : ℤ) - (r + 1)) ↔ ¬Even ((n : ℤ) - r) := by
    rw [sub_add_eq_sub_sub, Int.even_sub_one]
  unfold parityDensity intervalDensity
  rw [hfilter r, hfilter (r + 1), ← add_div]
  congr 1
  simp only [hnext]
  exact_mod_cast (Finset.card_filter_add_card_filter_not (s := F)
    (fun n : ℕ => Even ((n : ℤ) - r)))

theorem sum_owner_parity_fibers {K l : ℕ} (o : Fin K → Fin l)
    (r : Fin K → ℤ) (f : Fin K → ℝ) :
    (∑ g : Fin l × Bool, ∑ i : {i : Fin K // ownerParity o r i = g}, f i.val) =
      ∑ i : Fin K, f i := by
  classical
  have hh := Fintype.sum_sigma
    (fun x : Σ g, {i : Fin K // ownerParity o r i = g} => f x.2.val)
  rw [← hh]
  exact Fintype.sum_equiv (Equiv.sigmaFiberEquiv (ownerParity o r)) _ _ (fun _ => rfl)

/-! ### Upstream module `MerLeanExperiment/AveragedMesh.lean` -/

/-- Choose one distinct mesh cell for every label inside each owner/parity
fiber.  Fiberwise averaging then bounds the actual union of the selected
packing cells. -/
theorem exists_averaged_mesh {K l : ℕ} (A : Finset ℕ) (a b : Fin l → ℝ)
    (o : Fin K → Fin l) (r : Fin K → ℤ) (m : Fin l → ℕ) (delta R : ℝ)
    (hd : 0 < delta) (hR : 0 < R) (hm : ∀ j, 0 < m j)
    (hKm : ∀ j, K ≤ m j)
    (hmesh : ∀ j, (m j : ℝ) * delta ≤ b j - a j)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j))) :
    ∃ c : Fin K → ℝ,
      (∀ i, a (o i) ≤ c i ∧ c i + delta ≤ b (o i)) ∧
      (∑ g : Fin l × Bool,
          (Fintype.card {i : Fin K // ownerParity o r i = g} : ℝ) / m g.1 *
            (∑ s : Fin (m g.1),
              ((consecutiveCell A (a g.1) delta R (parityRep g.2) s.val).card : ℝ))) ≤
        (packingCellUnion A r c delta R).card := by
  classical
  let Fiber := fun g : Fin l × Bool ↦ {i : Fin K // ownerParity o r i = g}
  have hfiberK (g : Fin l × Bool) : Fintype.card (Fiber g) ≤ K := by
    simpa [Fiber] using
      Fintype.card_le_of_injective (fun i : Fiber g ↦ i.val) Subtype.val_injective
  have havg (g : Fin l × Bool) :
      ∃ sg : Fiber g → Fin (m g.1), Function.Injective sg ∧
        (Fintype.card (Fiber g) : ℝ) / m g.1 *
            (∑ s : Fin (m g.1),
              ((consecutiveCell A (a g.1) delta R (parityRep g.2) s.val).card : ℝ)) ≤
          ∑ i : Fiber g,
            ((consecutiveCell A (a g.1) delta R (parityRep g.2)
              (sg i).val).card : ℝ) := by
    exact exists_injective_average (I := Fiber g) (m g.1) (hm g.1)
      ((hfiberK g).trans (hKm g.1))
      (fun s : Fin (m g.1) ↦
        ((consecutiveCell A (a g.1) delta R (parityRep g.2) s.val).card : ℝ))
  choose sg hsg_inj hsg_avg using havg
  have hsg_transport (g h : Fin l × Bool) (e : g = h) (i : Fiber g) :
      (sg g i).val = (sg h ⟨i.val, i.property.trans e⟩).val := by
    subst h
    rfl
  let sigma : ∀ i : Fin K, Fin (m (o i)) := fun i ↦
    sg (ownerParity o r i) ⟨i, rfl⟩
  let c : Fin K → ℝ := fun i ↦ a (o i) + (sigma i).val * delta
  refine ⟨c, ?_, ?_⟩
  · simpa [c] using selected_mesh_bounds a b o m sigma delta hd.le hmesh
  · have hsigma_inj : ∀ i j, ownerParity o r i = ownerParity o r j →
        (sigma i).val = (sigma j).val → i = j := by
      intro i j hg hsval
      let ii : Fiber (ownerParity o r i) := ⟨i, rfl⟩
      let jj : Fiber (ownerParity o r j) := ⟨j, rfl⟩
      let jj' : Fiber (ownerParity o r i) := ⟨j, hg.symm⟩
      have hsval' : (sg (ownerParity o r i) ii).val =
          (sg (ownerParity o r j) jj).val := by
        exact hsval
      have htrans : (sg (ownerParity o r j) jj).val =
          (sg (ownerParity o r i) jj').val := by
        simpa [jj, jj'] using
          hsg_transport (ownerParity o r j) (ownerParity o r i) hg.symm jj
      have hsfin : sg (ownerParity o r i) ii =
          sg (ownerParity o r i) jj' := by
        apply Fin.ext
        exact hsval'.trans htrans
      exact congrArg Subtype.val (hsg_inj (ownerParity o r i) hsfin)
    have hcardN := selected_mesh_cells_card A a b o r m sigma delta R hd hR
      hmesh hdisj hsigma_inj
    have hcardR : ((packingCellUnion A r c delta R).card : ℝ) =
        ∑ i : Fin K, ((packingCell A r c delta R i).card : ℝ) := by
      dsimp [c]
      exact_mod_cast hcardN
    have hcell (i : Fin K) :
        packingCell A r c delta R i =
          consecutiveCell A (a (o i)) delta R
            (parityRep (ownerParity o r i).2) (sigma i).val := by
      ext n
      simp only [packingCell, consecutiveCell, parityRegion, Finset.mem_filter]
      rw [even_sub_parity_rep (n : ℤ) (r i)]
      simp only [ownerParity]
      dsimp [c]
      constructor
      · rintro ⟨hnA, hnlo, hnhi, hnpar⟩
        refine ⟨hnA, hnlo, ?_, hnpar⟩
        convert hnhi using 1 <;> ring
      · rintro ⟨hnA, hnlo, hnhi, hnpar⟩
        refine ⟨hnA, hnlo, ?_, hnpar⟩
        convert hnhi using 1 <;> ring
    have hfiber_eq (g : Fin l × Bool) :
        (∑ i : Fiber g,
            ((consecutiveCell A (a g.1) delta R (parityRep g.2)
              (sg g i).val).card : ℝ)) =
          ∑ i : Fiber g, ((packingCell A r c delta R i.val).card : ℝ) := by
      apply Fintype.sum_congr
      intro i
      rw [hcell i.val]
      have ho : o i.val = g.1 := congrArg Prod.fst i.property
      have hv : (ownerParity o r i.val).2 = g.2 := congrArg Prod.snd i.property
      have hs : (sigma i.val).val = (sg g i).val := by
        dsimp [sigma]
        simpa using hsg_transport (ownerParity o r i.val) g i.property
          (⟨i.val, rfl⟩ : Fiber (ownerParity o r i.val))
      have ha : a (o i.val) = a g.1 := congrArg a ho
      have hr : parityRep (ownerParity o r i.val).2 = parityRep g.2 :=
        congrArg parityRep hv
      rw [ha, hr, hs]
    calc
      (∑ g : Fin l × Bool,
          (Fintype.card {i : Fin K // ownerParity o r i = g} : ℝ) / m g.1 *
            (∑ s : Fin (m g.1),
              ((consecutiveCell A (a g.1) delta R (parityRep g.2) s.val).card : ℝ))) ≤
          ∑ g : Fin l × Bool, ∑ i : Fiber g,
            ((consecutiveCell A (a g.1) delta R (parityRep g.2)
              (sg g i).val).card : ℝ) := by
        apply Finset.sum_le_sum
        intro g _
        simpa [Fiber] using hsg_avg g
      _ = ∑ g : Fin l × Bool, ∑ i : Fiber g,
          ((packingCell A r c delta R i.val).card : ℝ) := by
        apply Fintype.sum_congr
        exact hfiber_eq
      _ = ∑ i : Fin K, ((packingCell A r c delta R i).card : ℝ) := by
        simpa [Fiber] using sum_owner_parity_fibers o r
          (fun i : Fin K ↦ ((packingCell A r c delta R i).card : ℝ))
      _ = ((packingCellUnion A r c delta R).card : ℝ) := hcardR.symm

/-! ### Upstream module `MerLeanExperiment/CellCover.lean` -/

theorem mem_realIntIoc (a b : ℝ) (n : ℤ) :
    n ∈ realIntIoc a b ↔ a < (n : ℝ) ∧ (n : ℝ) ≤ b := by
  simp only [realIntIoc, Finset.mem_Ioc, Int.floor_lt, Int.le_floor]

theorem card_realIntIoc_le (a b : ℝ) (hab : a ≤ b) :
    ((realIntIoc a b).card : ℝ) ≤ b - a + 1 := by
  have hc : ((realIntIoc a b).card : ℤ) = ⌊b⌋ - ⌊a⌋ :=
    Int.card_Ioc_of_le _ _ (Int.floor_mono hab)
  have hcR : ((realIntIoc a b).card : ℝ) = (⌊b⌋ : ℝ) - (⌊a⌋ : ℝ) := by
    exact_mod_cast hc
  rw [hcR]
  have hb := Int.floor_le b
  have ha := Int.lt_floor_add_one a
  linarith

theorem cell_point_cover (c delta R E : ℝ) (y n : ℤ)
    (hylo : c * R < (y : ℝ)) (hyhi : (y : ℝ) ≤ c * R + E)
    (hnlo : c * R < (n : ℝ)) (hnhi : (n : ℝ) ≤ (c + delta) * R)
    (hparity : Even (n - y)) :
    n ∈ realIntIoc (c * R) (c * R + E) ∨
      ∃ h ∈ Finset.Icc (1 : ℤ) ⌊delta * R / 2⌋, n = y + 2 * h := by
  by_cases hny : n ≤ y
  · left
    exact (mem_realIntIoc _ _ _).mpr ⟨hnlo, (Int.cast_le.mpr hny).trans hyhi⟩
  · right
    obtain ⟨h, he⟩ := hparity
    have hn : n = y + 2 * h := by omega
    have hh : 1 ≤ h := by omega
    refine ⟨h, Finset.mem_Icc.mpr ⟨hh, ?_⟩, hn⟩
    apply Int.le_floor.mpr
    have hnR : (n : ℝ) = (y : ℝ) + 2 * (h : ℝ) := by exact_mod_cast hn
    nlinarith

/-! ### Upstream module `MerLeanExperiment/ParityRegions.lean` -/

/-- Splitting a half-open parity region at an intermediate endpoint. -/
theorem parity_region_split (A : Finset ℕ) (a b c R : ℝ) (r : ℤ)
    (hab : a ≤ b) (hbc : b ≤ c) (hR : 0 ≤ R) :
    parityRegion A a c R r =
      parityRegion A a b R r ∪ parityRegion A b c R r := by
  ext n
  simp only [parityRegion, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hnA, han, hnc, hnpar⟩
    by_cases hnb : (n : ℝ) ≤ b * R
    · exact Or.inl ⟨hnA, han, hnb, hnpar⟩
    · exact Or.inr ⟨hnA, lt_of_not_ge hnb, hnc, hnpar⟩
  · rintro (hn | hn)
    · exact ⟨hn.1, hn.2.1, hn.2.2.1.trans
        (mul_le_mul_of_nonneg_right hbc hR), hn.2.2.2⟩
    · exact ⟨hn.1, (mul_le_mul_of_nonneg_right hab hR).trans_lt hn.2.1,
        hn.2.2.1, hn.2.2.2⟩

/-- Regions whose underlying real intervals are ordered and disjoint are
disjoint, independently of their parity labels. -/
theorem parity_regions_disjoint (A : Finset ℕ) (a b c d R : ℝ) (r s : ℤ)
    (hbc : b ≤ c) (hR : 0 ≤ R) :
    Disjoint (parityRegion A a b R r) (parityRegion A c d R s) := by
  rw [Finset.disjoint_left]
  intro n hn₁ hn₂
  simp only [parityRegion, Finset.mem_filter] at hn₁ hn₂
  have hscaled : b * R ≤ c * R := mul_le_mul_of_nonneg_right hbc hR
  linarith [hn₁.2.2.1, hn₂.2.1]

/-- The actual parity-filtered natural-number region has at most the usual
integer interval count. -/
theorem parity_region_card_le (A : Finset ℕ) (a b R : ℝ) (r : ℤ)
    (hab : a ≤ b) (hR : 0 ≤ R) :
    ((parityRegion A a b R r).card : ℝ) ≤ (b - a) * R + 1 := by
  let S : Finset ℤ := (parityRegion A a b R r).image (fun n : ℕ ↦ (n : ℤ))
  have hcardS : S.card = (parityRegion A a b R r).card := by
    dsimp [S]
    exact Finset.card_image_of_injective _ (fun x y hxy ↦ by exact_mod_cast hxy)
  have hsub : S ⊆ realIntIoc (a * R) (b * R) := by
    intro z hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    have hnr := (Finset.mem_filter.mp hn).2
    exact (mem_realIntIoc _ _ _).mpr ⟨hnr.1, hnr.2.1⟩
  have hcardN : S.card ≤ (realIntIoc (a * R) (b * R)).card :=
    Finset.card_le_card hsub
  have hcardR : (S.card : ℝ) ≤ ((realIntIoc (a * R) (b * R)).card : ℝ) := by
    exact_mod_cast hcardN
  have habR : a * R ≤ b * R := mul_le_mul_of_nonneg_right hab hR
  have hinterval := card_realIntIoc_le (a * R) (b * R) habR
  rw [hcardS] at hcardR
  calc
    ((parityRegion A a b R r).card : ℝ) ≤
        ((realIntIoc (a * R) (b * R)).card : ℝ) := hcardR
    _ ≤ b * R - a * R + 1 := hinterval
    _ = (b - a) * R + 1 := by ring

/-- A finite union of consecutive actual cells is exactly the longer parity
region with the same left endpoint. -/
theorem consecutive_cells_union (A : Finset ℕ) (a delta R : ℝ) (r : ℤ)
    (m : ℕ) (hd : 0 ≤ delta) (hR : 0 ≤ R) :
    (Finset.range m).biUnion (consecutiveCell A a delta R r) =
      parityRegion A a (a + m * delta) R r := by
  induction m with
  | zero =>
      simp only [Finset.range_zero, Finset.biUnion_empty]
      ext n
      simp only [Finset.notMem_empty, parityRegion, Finset.mem_filter, false_iff]
      rintro ⟨_, hnlo, hnhi, _⟩
      norm_num at hnhi
      linarith
  | succ m ih =>
      have hm : (0 : ℝ) ≤ m := by positivity
      have ham : a ≤ a + (m : ℝ) * delta := by
        nlinarith [mul_nonneg hm hd]
      have hmm : a + (m : ℝ) * delta ≤ a + ((m : ℝ) + 1) * delta := by
        nlinarith
      rw [Finset.range_add_one, Finset.biUnion_insert, ih]
      rw [show consecutiveCell A a delta R r m =
          parityRegion A (a + (m : ℝ) * delta)
            (a + ((m : ℝ) + 1) * delta) R r by
        simp [consecutiveCell]]
      rw [show (↑(m + 1) : ℝ) = (m : ℝ) + 1 by norm_num]
      rw [Finset.union_comm]
      exact (parity_region_split A a (a + (m : ℝ) * delta)
        (a + ((m : ℝ) + 1) * delta) R r ham hmm hR).symm

/-- Consecutive actual cells are pairwise disjoint, so their cardinalities
sum to the cardinality of their union. -/
theorem consecutive_cells_card (A : Finset ℕ) (a delta R : ℝ) (r : ℤ)
    (m : ℕ) (hd : 0 ≤ delta) (hR : 0 ≤ R) :
    (∑ s ∈ Finset.range m, (consecutiveCell A a delta R r s).card) =
      (parityRegion A a (a + m * delta) R r).card := by
  have hpw : ((Finset.range m : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (consecutiveCell A a delta R r) := by
    intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_range] at hi hj
    rcases lt_or_gt_of_ne hij with hij | hji
    · apply parity_regions_disjoint
      · have hs : ((i : ℝ) + 1) * delta ≤ (j : ℝ) * delta := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show i + 1 ≤ j by omega)) hd
        linarith
      · exact hR
    · exact (parity_regions_disjoint A
        (a + (j : ℝ) * delta) (a + ((j : ℝ) + 1) * delta)
        (a + (i : ℝ) * delta) (a + ((i : ℝ) + 1) * delta) R r r
        (by
          have hs : ((j : ℝ) + 1) * delta ≤ (i : ℝ) * delta := by
            exact mul_le_mul_of_nonneg_right
              (by exact_mod_cast (show j + 1 ≤ i by omega)) hd
          linarith) hR).symm
  rw [← consecutive_cells_union A a delta R r m hd hR]
  symm
  rw [Finset.card_biUnion hpw]

/-- The uncovered tail after the consecutive mesh costs at most one interval
length plus the unavoidable integer endpoint error. -/
theorem parity_region_le_cells_add (A : Finset ℕ) (a b delta R : ℝ) (r : ℤ)
    (m : ℕ) (hd : 0 < delta) (hR : 0 < R)
    (hlo : (m : ℝ) * delta ≤ b - a)
    (hhi : b - a < ((m : ℝ) + 1) * delta) :
    ((parityRegion A a b R r).card : ℝ) ≤
      (∑ s ∈ Finset.range m,
        ((consecutiveCell A a delta R r s).card : ℝ)) + delta * R + 1 := by
  let c : ℝ := a + (m : ℝ) * delta
  have hm : (0 : ℝ) ≤ m := by positivity
  have hac : a ≤ c := by
    dsimp [c]
    nlinarith [mul_nonneg hm hd.le]
  have hcb : c ≤ b := by dsimp [c]; linarith
  have hsplit := parity_region_split A a c b R r hac hcb hR.le
  have hdis := parity_regions_disjoint A a c c b R r r le_rfl hR.le
  have hcardN : (parityRegion A a b R r).card =
      (parityRegion A a c R r).card + (parityRegion A c b R r).card := by
    rw [hsplit, Finset.card_union_of_disjoint hdis]
  have htail := parity_region_card_le A c b R r hcb hR.le
  have hlen : b - c < delta := by
    dsimp [c]
    nlinarith
  have htail' : ((parityRegion A c b R r).card : ℝ) ≤ delta * R + 1 := by
    calc
      ((parityRegion A c b R r).card : ℝ) ≤ (b - c) * R + 1 := htail
      _ ≤ delta * R + 1 := by nlinarith
  have hcovered := consecutive_cells_card A a delta R r m hd.le hR.le
  have hcoveredR : ((parityRegion A a c R r).card : ℝ) =
      ∑ s ∈ Finset.range m,
        ((consecutiveCell A a delta R r s).card : ℝ) := by
    rw [show c = a + (m : ℝ) * delta by rfl]
    exact_mod_cast hcovered.symm
  rw [hcardN, Nat.cast_add, hcoveredR]
  linarith

/-! ### Upstream module `MerLeanExperiment/ParityDensityMesh.lean` -/

theorem parity_density_mesh_bound (A : Finset ℕ) (a b delta R : ℝ)
    (r : ℤ) (m : ℕ) (hm : 0 < m) (hd : 0 < delta) (hR : 0 < R)
    (hlo : (m : ℝ) * delta ≤ b - a)
    (hhi : b - a < ((m : ℝ) + 1) * delta) :
    delta * R * parityDensity A a b R r ≤
      (∑ s : Fin m, ((consecutiveCell A a delta R r s.val).card : ℝ)) / m +
        delta * (delta * R + 1) / (b - a) := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hw : 0 < b - a := (mul_pos hmR hd).trans_le hlo
  let C : ℝ := ∑ s : Fin m, ((consecutiveCell A a delta R r s.val).card : ℝ)
  let F : ℝ := (parityRegion A a b R r).card
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hfull : F ≤ C + delta * R + 1 := by
    have h := parity_region_le_cells_add A a b delta R r m hd hR hlo hhi
    have heq := Fin.sum_univ_eq_sum_range
      (fun s : ℕ => ((consecutiveCell A a delta R r s).card : ℝ)) m
    change F ≤ C + delta * R + 1
    dsimp only [C]
    rw [heq]
    exact h
  have hratio : delta / (b - a) ≤ 1 / (m : ℝ) := by
    apply (div_le_div_iff₀ hw hmR).mpr
    nlinarith
  have heq : delta * R * parityDensity A a b R r = delta / (b - a) * F := by
    unfold parityDensity
    change delta * R * (F / ((b - a) * R)) = _
    field_simp
  calc
    delta * R * parityDensity A a b R r = delta / (b - a) * F := heq
    _ ≤ delta / (b - a) * (C + delta * R + 1) :=
      mul_le_mul_of_nonneg_left hfull (div_nonneg hd.le hw.le)
    _ ≤ C / m + delta * (delta * R + 1) / (b - a) := by
      have hh := mul_le_mul_of_nonneg_right hratio hC
      calc
        _ = delta / (b - a) * C + delta * (delta * R + 1) / (b - a) := by ring
        _ ≤ 1 / (m : ℝ) * C + delta * (delta * R + 1) / (b - a) := add_le_add hh le_rfl
        _ = _ := by ring

/-! ### Upstream module `MerLeanExperiment/FiberMultiplicity.lean` -/

theorem sum_owner_parity_multiplicity {K l : ℕ} (o : Fin K → Fin l)
    (r : Fin K → ℤ) (F : Fin l × Bool → ℝ) :
    (∑ g : Fin l × Bool,
      (Fintype.card {i : Fin K // ownerParity o r i = g} : ℝ) * F g) =
      ∑ i : Fin K, F (ownerParity o r i) := by
  classical
  rw [← sum_owner_parity_fibers o r (fun i => F (ownerParity o r i))]
  apply Finset.sum_congr rfl
  intro g _
  have h (i : {i : Fin K // ownerParity o r i = g}) :
      F (ownerParity o r i.val) = F g := by rw [i.property]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ### Upstream module `MerLeanExperiment/FiniteParityDensity.lean` -/

theorem exists_finite_parity_density_mesh {K l : ℕ} (A : Finset ℕ)
    (a b : Fin l → ℝ) (o : Fin K → Fin l) (r : Fin K → ℤ)
    (m : Fin l → ℕ) (delta R : ℝ) (hd : 0 < delta) (hR : 0 < R)
    (hm : ∀ j, 0 < m j) (hKm : ∀ j, K ≤ m j)
    (hlo : ∀ j, (m j : ℝ) * delta ≤ b j - a j)
    (hhi : ∀ j, b j - a j < ((m j : ℝ) + 1) * delta)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j))) :
    ∃ c : Fin K → ℝ, (∀ i, a (o i) ≤ c i ∧ c i + delta ≤ b (o i)) ∧
      delta * R * (∑ i : Fin K, parityDensity A (a (o i)) (b (o i)) R (r i)) ≤
        (packingCellUnion A r c delta R).card +
          delta * (delta * R + 1) * (∑ i : Fin K, 1 / (b (o i) - a (o i))) := by
  classical
  obtain ⟨c, hcb, havg⟩ := exists_averaged_mesh A a b o r m delta R hd hR hm hKm hlo hdisj
  refine ⟨c, hcb, ?_⟩
  let C : Fin l × Bool → ℝ := fun g =>
    ∑ s : Fin (m g.1), ((consecutiveCell A (a g.1) delta R (parityRep g.2) s.val).card : ℝ)
  have hsum : (∑ i : Fin K, C (ownerParity o r i) / m (o i)) ≤
      (packingCellUnion A r c delta R).card := by
    calc
      _ = ∑ g : Fin l × Bool,
          (Fintype.card {i : Fin K // ownerParity o r i = g} : ℝ) * (C g / m g.1) :=
        (sum_owner_parity_multiplicity o r (fun g => C g / m g.1)).symm
      _ = ∑ g : Fin l × Bool,
          (Fintype.card {i : Fin K // ownerParity o r i = g} : ℝ) / m g.1 * C g := by
        apply Finset.sum_congr rfl
        intro g _
        ring
      _ ≤ _ := havg
  have hper (i : Fin K) :
      delta * R * parityDensity A (a (o i)) (b (o i)) R (r i) ≤
        C (ownerParity o r i) / m (o i) +
          delta * (delta * R + 1) / (b (o i) - a (o i)) := by
    have hdens : parityDensity A (a (o i)) (b (o i)) R (r i) =
        parityDensity A (a (o i)) (b (o i)) R (parityRep (decide (Even (r i)))) := by
      change ((parityRegion A (a (o i)) (b (o i)) R (r i)).card : ℝ) / _ =
        ((parityRegion A (a (o i)) (b (o i)) R (parityRep (decide (Even (r i))))).card : ℝ) / _
      rw [parity_region_rep]
    rw [hdens]
    exact parity_density_mesh_bound A (a (o i)) (b (o i)) delta R
      (parityRep (decide (Even (r i)))) (m (o i)) (hm (o i)) hd hR (hlo (o i)) (hhi (o i))
  have hall := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin K))) => hper i)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hall
  have herr : (∑ i : Fin K, delta * (delta * R + 1) / (b (o i) - a (o i))) =
      delta * (delta * R + 1) * (∑ i : Fin K, 1 / (b (o i) - a (o i))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [herr] at hall
  linarith

/-! ### Upstream module `MerLeanExperiment/PackingParameters.lean` -/

theorem exists_finite_positive_bounds {I : Type*} [Fintype I]
    (f : I → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧ (∀ i, c ≤ f i) ∧ (∀ i, f i ≤ B) := by
  classical
  let D : ℝ := 1 + ∑ i, 1 / f i
  let B : ℝ := 1 + ∑ i, f i
  have hD : 0 < D := by
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
      (one_div_pos.mpr (hf i)).le)
    dsimp [D]
    linarith
  have hB : 0 < B := by
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset I)) => (hf i).le)
    dsimp [B]
    linarith
  refine ⟨1 / D, B, one_div_pos.mpr hD, hB, ?_, ?_⟩
  · intro i
    have hi : 1 / f i ≤ D := by
      have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
        (one_div_pos.mpr (hf j)).le) (Finset.mem_univ i)
      dsimp [D]
      linarith
    have hh := one_div_le_one_div_of_le (one_div_pos.mpr (hf i)) hi
    simpa only [one_div_one_div] using hh
  · intro i
    have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
      (hf j).le) (Finset.mem_univ i)
    dsimp [B]
    linarith

theorem exists_packing_mesh {l : ℕ} (K : ℕ) (a b : Fin l → ℝ)
    (hab : ∀ j, a j < b j) (S epsilon : ℝ) (hS : 0 ≤ S)
    (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, ∃ m : Fin l → ℕ, 0 < delta ∧ (∀ j, 0 < m j) ∧
      (∀ j, K ≤ m j) ∧ (∀ j, (m j : ℝ) * delta ≤ b j - a j) ∧
      (∀ j, b j - a j < ((m j : ℝ) + 1) * delta) ∧ delta * S ≤ epsilon / 4 := by
  classical
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  obtain ⟨c, _, hc, _, hcw, _⟩ := exists_finite_positive_bounds
    (fun j => (b j - a j) / ((K : ℝ) + 1))
    (fun j => div_pos (sub_pos.mpr (hab j)) hK)
  let delta : ℝ := min c (epsilon / (4 * (S + 1)))
  have hd : 0 < delta := lt_min hc (div_pos hepsilon (by positivity))
  have hdw (j : Fin l) : delta ≤ (b j - a j) / ((K : ℝ) + 1) :=
    (min_le_left _ _).trans (hcw j)
  let m : Fin l → ℕ := fun j => ⌊(b j - a j) / delta⌋₊
  have hm (j : Fin l) : K + 1 ≤ m j := by
    apply Nat.le_floor
    rw [Nat.cast_add, Nat.cast_one]
    apply (le_div_iff₀ hd).mpr
    have hh := (le_div_iff₀ hK).mp (hdw j)
    nlinarith
  refine ⟨delta, m, hd, (fun j => by have := hm j; omega),
    (fun j => by have := hm j; omega), ?_, ?_, ?_⟩
  · intro j
    exact (le_div_iff₀ hd).mp (Nat.floor_le (div_nonneg (sub_pos.mpr (hab j)).le hd.le))
  · intro j
    exact (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one ((b j - a j) / delta))
  · have hh : delta ≤ epsilon / (4 * (S + 1)) := min_le_right _ _
    have hc := (le_div_iff₀ (show 0 < 4 * (S + 1) by positivity)).mp hh
    nlinarith

theorem exists_packing_residue_budget {K : ℕ} (r : Fin K → ℤ) :
    ∃ M : ℕ, 3 ≤ M ∧ 2 * K ≤ M ∧ ∀ i j, 2 * (r j - r i).natAbs ≤ M := by
  classical
  let S : ℕ := ∑ i : Fin K, ∑ j : Fin K, 2 * (r j - r i).natAbs
  refine ⟨3 + 2 * K + S, by omega, by omega, ?_⟩
  intro i j
  have hj : 2 * (r j - r i).natAbs ≤ ∑ j : Fin K, 2 * (r j - r i).natAbs :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (2 * (r j - r i).natAbs)) (Finset.mem_univ j)
  have hi : (∑ j : Fin K, 2 * (r j - r i).natAbs) ≤ S :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (∑ j : Fin K, 2 * (r j - r i).natAbs))
      (Finset.mem_univ i)
  omega

/-! ### Upstream module `MerLeanExperiment/GcdCancellation.lean` -/

theorem gcd_dvd_difference_factor (U V d F : ℤ) (D : ℕ)
    (hdiff : V - U = d * F) (hFD : F.natAbs ∣ D)
    (hcop : Nat.Coprime U.natAbs D) :
    Nat.gcd U.natAbs V.natAbs ∣ d.natAbs := by
  let g := Nat.gcd U.natAbs V.natAbs
  have hgU : g ∣ U.natAbs := Nat.gcd_dvd_left _ _
  have hgV : g ∣ V.natAbs := Nat.gcd_dvd_right _ _
  have hU : (g : ℤ) ∣ U := Int.natCast_dvd.mpr hgU
  have hV : (g : ℤ) ∣ V := Int.natCast_dvd.mpr hgV
  have hprod : (g : ℤ) ∣ d * F := hdiff ▸ dvd_sub hV hU
  have hprodNat : g ∣ d.natAbs * F.natAbs := by
    simpa only [Int.natAbs_mul] using Int.natCast_dvd.mp hprod
  have hcopg : Nat.Coprime g F.natAbs := hcop.of_dvd hgU hFD
  exact hcopg.dvd_mul_right.mp hprodNat

theorem two_mul_le_of_odd_dvd_even (g d : ℕ) (hd : 0 < d)
    (hgodd : Odd g) (hdeven : Even d) (hgd : g ∣ d) : 2 * g ≤ d := by
  exact Nat.le_of_dvd hd
    (hgodd.coprime_two_left.mul_dvd_of_dvd_of_dvd hdeven.two_dvd hgd)

/-! ### Upstream module `MerLeanExperiment/ShiftAlgebra.lean` -/

theorem shift_factor_mul_difference {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ)
    (i j : Fin K) (hd : r j - r i ≠ 0) (hsize : 2 * (r j - r i).natAbs ≤ M) :
    (r j - r i) * shiftFactor M r ell i j =
      shiftedPoint M r ell j - shiftedPoint M r ell i := by
  have heq := (factorial_linear_spec M (r j - r i) hd hsize (ell i)).1
  unfold shiftFactor shiftedPoint
  calc
    _ = ((r j - r i) * ((M.factorial : ℤ) / (r j - r i))) *
        (ell j - ell i) + (r j - r i) := by ring
    _ = _ := by rw [heq]; ring

theorem shift_points_injective {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ)
    (hr : Function.Injective r)
    (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M) :
    Function.Injective (shiftedPoint M r ell) := by
  intro i j hpoint
  by_contra hij
  have hd : r j - r i ≠ 0 := sub_ne_zero.mpr (fun h => hij (hr h).symm)
  have hdpos : 0 < (r j - r i).natAbs := Int.natAbs_pos.mpr hd
  have hsmall : (r j - r i).natAbs < M := by
    have hs := hsize i j hij
    omega
  have hdiv : (M.factorial : ℤ) ∣ r j - r i := by
    refine ⟨ell i - ell j, ?_⟩
    unfold shiftedPoint at hpoint
    nlinarith
  have hle : M.factorial ≤ (r j - r i).natAbs :=
    Nat.le_of_dvd hdpos (Int.natCast_dvd.mp hdiv)
  have hMF := Nat.self_le_factorial M
  omega

theorem shift_factor_ne_zero {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ)
    (hr : Function.Injective r)
    (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M)
    (i j : Fin K) (hij : i ≠ j) : shiftFactor M r ell i j ≠ 0 := by
  intro hz
  have hd : r j - r i ≠ 0 := sub_ne_zero.mpr (fun h => hij (hr h).symm)
  have heq := shift_factor_mul_difference M r ell i j hd (hsize i j hij)
  rw [hz, mul_zero] at heq
  have hp : shiftedPoint M r ell j = shiftedPoint M r ell i := sub_eq_zero.mp heq.symm
  exact hij ((shift_points_injective M r ell hr hsize) hp).symm

/-! ### Upstream module `MerLeanExperiment/TranslatedGcd.lean` -/

theorem translated_shift_gcd_bound {K : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (r ell : Fin K → ℤ) (hr : Function.Injective r)
    (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M)
    (i j : Fin K) (hij : i < j) (h : ℤ)
    (hcop : Nat.Coprime (shiftedPoint M r ell i + 2 * h).natAbs
      (shiftProductNat M r ell)) :
    shiftParityWeight (r i) (r j) *
      Nat.gcd (shiftedPoint M r ell i + 2 * h).natAbs
        (shiftedPoint M r ell j + 2 * h).natAbs ≤ (r j - r i).natAbs := by
  have hd : r j - r i ≠ 0 := sub_ne_zero.mpr (fun he => (ne_of_lt hij) (hr he).symm)
  have hdpos : 0 < (r j - r i).natAbs := Int.natAbs_pos.mpr hd
  have hfactor : shiftFactor M r ell i j ∣ shiftProduct M r ell := by
    unfold shiftProduct
    apply Finset.dvd_prod_of_mem (fun ij : Fin K × Fin K => shiftFactor M r ell ij.1 ij.2)
      (a := (i, j))
    simp [shiftPairs, hij]
  have hfactorNat : (shiftFactor M r ell i j).natAbs ∣ shiftProductNat M r ell := by
    obtain ⟨k, hk⟩ := hfactor
    refine ⟨k.natAbs, ?_⟩
    simp only [shiftProductNat, hk, Int.natAbs_mul]
  have hdiff : (shiftedPoint M r ell j + 2 * h) -
      (shiftedPoint M r ell i + 2 * h) =
      (r j - r i) * shiftFactor M r ell i j := by
    rw [shift_factor_mul_difference M r ell i j hd (hsize i j (ne_of_lt hij))]
    ring
  have hgd := gcd_dvd_difference_factor _ _ _ _ _ hdiff hfactorNat hcop
  by_cases hodd : Odd (r i) ∧ Odd (r j)
  · rw [shiftParityWeight, ite_eq_left hodd]
    have htwo : (2 : ℤ) ∣ (M.factorial : ℤ) := by
      exact_mod_cast Nat.dvd_factorial (by omega : 0 < 2) hM
    have hfact : Even (M.factorial : ℤ) := even_iff_two_dvd.mpr htwo
    have hpoint : Odd (shiftedPoint M r ell i + 2 * h) := by
      exact ((hfact.mul_right (ell i)).add_odd hodd.1).add_even (even_two.mul_right h)
    have hgodd : Odd (Nat.gcd (shiftedPoint M r ell i + 2 * h).natAbs
        (shiftedPoint M r ell j + 2 * h).natAbs) := by
      exact Nat.coprime_two_left.mp
        (hpoint.natAbs.coprime_two_left.of_dvd_right (Nat.gcd_dvd_left _ _))
    exact two_mul_le_of_odd_dvd_even _ _ hdpos hgodd (hodd.2.sub_odd hodd.1).natAbs hgd
  · rw [shiftParityWeight, ite_eq_right hodd, one_mul]
    exact Nat.le_of_dvd hdpos hgd

/-! ### Upstream module `MerLeanExperiment/LcmCollision.lean` -/

theorem lcm_gt_of_separated_lower_bounds (X a b d : ℝ) (u v gamma : ℕ)
    (hX : 0 < X) (ha : 0 < a) (hb : 0 < b) (hgamma : 0 < gamma)
    (hu : a * Real.sqrt X < (u : ℝ)) (hv : b * Real.sqrt X < (v : ℝ))
    (hg : (gamma : ℝ) * (Nat.gcd u v : ℝ) ≤ d)
    (hd : d ≤ (gamma : ℝ) * a * b) : X < (Nat.lcm u v : ℝ) := by
  have hs : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hgp : (0 : ℝ) < gamma := Nat.cast_pos.mpr hgamma
  have hu0 : (0 : ℝ) < u := (mul_pos ha hs).trans hu
  have hp : a * b * X < (u : ℝ) * v := by
    calc
      _ = (a * Real.sqrt X) * (b * Real.sqrt X) := by
        rw [mul_mul_mul_comm, Real.mul_self_sqrt hX.le]
      _ < (u : ℝ) * v := mul_lt_mul hu hv.le (mul_pos hb hs) hu0.le
  have hid : (Nat.gcd u v : ℝ) * (Nat.lcm u v : ℝ) = (u : ℝ) * v := by
    exact_mod_cast Nat.gcd_mul_lcm u v
  by_contra hnot
  have hl : (Nat.lcm u v : ℝ) ≤ X := le_of_not_gt hnot
  have hupper : (gamma : ℝ) * ((u : ℝ) * v) ≤ (gamma : ℝ) * (a * b * X) := by
    calc
      _ = ((gamma : ℝ) * (Nat.gcd u v : ℝ)) * (Nat.lcm u v : ℝ) := by rw [mul_assoc, hid]
      _ ≤ ((gamma : ℝ) * (Nat.gcd u v : ℝ)) * X :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      _ ≤ d * X := mul_le_mul_of_nonneg_right hg hX.le
      _ ≤ ((gamma : ℝ) * a * b) * X := mul_le_mul_of_nonneg_right hd hX.le
      _ = _ := by ring
  exact (not_lt_of_ge hupper) (mul_lt_mul_of_pos_left hp hgp)

/-! ### Upstream module `MerLeanExperiment/External/Erdos441.lean` -/

/-!
# Erdős Problem 441

For `N : ℕ`, let `g N` be the largest cardinality of a finite subset of
`{1, ..., N}` whose pairwise least common multiples do not exceed `N`.

Erdős proposed the union of the integers at most `sqrt (N / 2)` and the even
integers at most `sqrt (2 * N)`.  We use the equivalent square-only definition
`erdosConstruction` below.  The construction is always admissible, but it is not
eventually extremal: at every `N = 2 * (6*t + 4)^2`, the new element
`2 * (6*t + 6)` may be adjoined.

The latter is an elementary infinite-family strengthening of a single
counterexample and gives the exact negative answer to Erdős's proposed extremal
description.  Chen's separate sharp asymptotic theorem is discussed, together
with its sieve-theoretic dependency chain, in `tex/441.tex`.
-/

/-- A finite set of positive integers at most `N`, every two of whose least
common multiples are at most `N`. -/
def LcmBounded (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    ∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N

instance (N : ℕ) (A : Finset ℕ) : Decidable (LcmBounded N A) := by
  unfold LcmBounded
  infer_instance

/-- The finite collection of all admissible subsets of `{1, ..., N}`. -/
def candidates (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter (LcmBounded N)

/-- The exact extremal function in Erdős Problem 441. -/
def g (N : ℕ) : ℕ :=
  (candidates N).sup Finset.card

@[simp] lemma mem_candidates {N : ℕ} {A : Finset ℕ} :
    A ∈ candidates N ↔ LcmBounded N A := by
  constructor
  · intro hA
    exact (Finset.mem_filter.mp hA).2
  · intro hA
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA.1, hA⟩

@[simp] lemma empty_lcmBounded (N : ℕ) : LcmBounded N ∅ := by
  simp [LcmBounded]

lemma card_le_g {N : ℕ} {A : Finset ℕ} (hA : LcmBounded N A) :
    A.card ≤ g N := by
  exact Finset.le_sup (f := Finset.card) (mem_candidates.mpr hA)

/-- The supremum defining `g` is attained by an admissible finite set. -/
theorem exists_extremal (N : ℕ) :
    ∃ A : Finset ℕ, LcmBounded N A ∧ A.card = g N := by
  have hne : (candidates N).Nonempty :=
    ⟨∅, mem_candidates.mpr (empty_lcmBounded N)⟩
  obtain ⟨A, hA, hcard⟩ :=
    Finset.exists_mem_eq_sup (candidates N) hne Finset.card
  exact ⟨A, mem_candidates.mp hA, hcard.symm⟩

/-- Erdős's proposed construction, written without real square roots. -/
def erdosConstruction (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun a ↦
    2 * a ^ 2 ≤ N ∨ (2 ∣ a ∧ a ^ 2 ≤ 2 * N)

@[simp] lemma mem_erdosConstruction {N a : ℕ} :
    a ∈ erdosConstruction N ↔
      1 ≤ a ∧ a ≤ N ∧
        (2 * a ^ 2 ≤ N ∨ (2 ∣ a ∧ a ^ 2 ≤ 2 * N)) := by
  simp [erdosConstruction, and_assoc]

lemma lcm_le_mul {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nat.lcm a b ≤ a * b := by
  exact Nat.le_of_dvd (Nat.mul_pos ha hb) (Nat.lcm_dvd_mul a b)

private lemma mul_le_of_two_mul_sq_le_sq_le {N x y : ℕ}
    (hx : 2 * x ^ 2 ≤ N) (hy : y ^ 2 ≤ 2 * N) :
    x * y ≤ N := by
  nlinarith [sq_nonneg (2 * (x : ℤ) - y)]

private lemma two_mul_le_of_two_mul_sq_le {N u v : ℕ}
    (hu : 2 * u ^ 2 ≤ N) (hv : 2 * v ^ 2 ≤ N) :
    2 * (u * v) ≤ N := by
  nlinarith [sq_nonneg ((u : ℤ) - v)]

/-- Erdős's proposed set is admissible for every `N`. -/
theorem erdosConstruction_lcmBounded (N : ℕ) :
    LcmBounded N (erdosConstruction N) := by
  constructor
  · intro a ha
    exact Finset.mem_Icc.mpr ⟨(mem_erdosConstruction.mp ha).1,
      (mem_erdosConstruction.mp ha).2.1⟩
  · intro a ha b hb
    have ha' := mem_erdosConstruction.mp ha
    have hb' := mem_erdosConstruction.mp hb
    rcases ha'.2.2 with haLow | ⟨haEven, haHigh⟩
    · rcases hb'.2.2 with hbLow | ⟨_hbEven, hbHigh⟩
      · have hbHigh : b ^ 2 ≤ 2 * N := by omega
        exact (lcm_le_mul ha'.1 hb'.1).trans
          (mul_le_of_two_mul_sq_le_sq_le haLow hbHigh)
      · exact (lcm_le_mul ha'.1 hb'.1).trans
          (mul_le_of_two_mul_sq_le_sq_le haLow hbHigh)
    · rcases hb'.2.2 with hbLow | ⟨hbEven, hbHigh⟩
      · rw [Nat.lcm_comm]
        exact (lcm_le_mul hb'.1 ha'.1).trans
          (mul_le_of_two_mul_sq_le_sq_le hbLow haHigh)
      · rcases haEven with ⟨u, rfl⟩
        rcases hbEven with ⟨v, rfl⟩
        have hu : 2 * u ^ 2 ≤ N := by nlinarith
        have hv : 2 * v ^ 2 ≤ N := by nlinarith
        have huPos : 1 ≤ u := by omega
        have hvPos : 1 ≤ v := by omega
        have hdvd : Nat.lcm (2 * u) (2 * v) ∣ 2 * (u * v) := by
          apply Nat.lcm_dvd
          · exact ⟨v, by ring⟩
          · exact ⟨u, by ring⟩
        calc
          Nat.lcm (2 * u) (2 * v) ≤ 2 * (u * v) :=
            Nat.le_of_dvd (by positivity) hdvd
          _ ≤ N := two_mul_le_of_two_mul_sq_le hu hv

/-! ## An infinite family on which Erdős's construction is not maximal -/

/-- The square-root parameter in the elementary counterexample family. -/
def familyK (t : ℕ) : ℕ := 6 * t + 4

/-- The ambient bound `N = 2 k²` in the elementary counterexample family. -/
def familyN (t : ℕ) : ℕ := 2 * familyK t ^ 2

/-- The element which can be adjoined to Erdős's construction. -/
def extra (t : ℕ) : ℕ := 2 * (familyK t + 2)

/-- A disjoint enumeration of the odd part below `k` and the even part below
`2k` at `N = 2k²`. -/
def familyListing (t : ℕ) : Finset ℕ :=
  (Finset.range (3 * t + 2)).image (fun i ↦ 2 * i + 1) ∪
    (Finset.range (familyK t)).image (fun i ↦ 2 * (i + 1))

private lemma lcm_le_commonMultiple {a b m : ℕ} (hm : 0 < m)
    (ha : a ∣ m) (hb : b ∣ m) :
    Nat.lcm a b ≤ m := by
  exact Nat.le_of_dvd hm (Nat.lcm_dvd ha hb)

private lemma low_member_le_familyK {t b : ℕ}
    (hb : 2 * b ^ 2 ≤ familyN t) : b ≤ familyK t := by
  simp only [familyN] at hb
  nlinarith [sq_nonneg ((b : ℤ) - familyK t)]

private lemma high_half_le_familyK {t h : ℕ}
    (hh : (2 * h) ^ 2 ≤ 2 * familyN t) : h ≤ familyK t := by
  simp only [familyN] at hh
  nlinarith [sq_nonneg ((h : ℤ) - familyK t)]

/-- At the counterexample parameters, Erdős's construction is precisely the
odd integers at most `k` together with the even integers at most `2k`. -/
lemma familyListing_eq_erdosConstruction (t : ℕ) :
    familyListing t = erdosConstruction (familyN t) := by
  ext a
  simp only [familyListing, Finset.mem_union, Finset.mem_image,
    Finset.mem_range, mem_erdosConstruction]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · constructor
      · omega
      constructor
      · simp [familyN, familyK]
        nlinarith
      · left
        simp [familyN, familyK]
        nlinarith
    · constructor
      · omega
      constructor
      · have hi1 : i + 1 ≤ familyK t := by omega
        calc
          2 * (i + 1) ≤ 2 * familyK t := Nat.mul_le_mul_left 2 hi1
          _ ≤ familyN t := by
            simp [familyN, familyK]
            nlinarith
      · right
        constructor
        · exact ⟨i + 1, by ring⟩
        · have hi1 : i + 1 ≤ familyK t := by omega
          have hsquare := Nat.pow_le_pow_left hi1 2
          simp only [familyN]
          nlinarith
  · rintro ⟨hapos, _haN, haLow | ⟨haEven, haHigh⟩⟩
    · have hak : a ≤ familyK t := low_member_le_familyK haLow
      obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' a
      · right
        have hipos : 1 ≤ i := by omega
        refine ⟨i - 1, ?_, ?_⟩
        · omega
        · omega
      · left
        refine ⟨i, ?_, hi.symm⟩
        simp [familyK] at hak
        omega
    · rcases haEven with ⟨h, rfl⟩
      have hh : h ≤ familyK t := high_half_le_familyK haHigh
      have hhpos : 1 ≤ h := by omega
      right
      refine ⟨h - 1, ?_, ?_⟩
      · omega
      · omega

lemma familyListing_disjoint (t : ℕ) :
    Disjoint
      ((Finset.range (3 * t + 2)).image (fun i ↦ 2 * i + 1))
      ((Finset.range (familyK t)).image (fun i ↦ 2 * (i + 1))) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_image, Finset.mem_range] at ha hb
  obtain ⟨i, _hi, rfl⟩ := ha
  obtain ⟨j, _hj, hij⟩ := hb
  omega

/-- The proposed construction has its expected exact size on the family
`N = 2 * (6t+4)²`. -/
lemma card_erdosConstruction_familyN (t : ℕ) :
    (erdosConstruction (familyN t)).card = 9 * t + 6 := by
  rw [← familyListing_eq_erdosConstruction, familyListing,
    Finset.card_union_of_disjoint (familyListing_disjoint t),
    Finset.card_image_of_injective _ (by intro i j h; dsimp at h; omega),
    Finset.card_image_of_injective _ (by intro i j h; dsimp at h; omega)]
  simp [familyK]
  omega

private lemma extra_lcm_low_le (t b : ℕ) (hbpos : 1 ≤ b)
    (hb : b ≤ familyK t) :
    Nat.lcm (extra t) b ≤ familyN t := by
  by_cases hinterior : b ≤ familyK t - 2
  · have hb2 : b + 2 ≤ familyK t := by
      have hk : 2 ≤ familyK t := by simp [familyK]
      omega
    exact (lcm_le_mul (by simp [extra, familyK]; omega) hbpos).trans (by
      simp only [extra, familyN, familyK] at *
      nlinarith)
  · have hcases : b = familyK t - 1 ∨ b = familyK t := by omega
    rcases hcases with hprev | htop
    · subst b
      let m := 12 * (t + 1) * (2 * t + 1)
      have hm : 0 < m := by positivity
      have he : extra t ∣ m := by
        refine ⟨2 * t + 1, ?_⟩
        simp [extra, familyK, m]
        ring
      have hb : familyK t - 1 ∣ m := by
        refine ⟨4 * (t + 1), ?_⟩
        simp [familyK, m]
        ring
      exact (lcm_le_commonMultiple hm he hb).trans (by
        simp [familyN, familyK, m]
        nlinarith)
    · subst b
      let m := familyK t * (familyK t + 2)
      have hm : 0 < m := by positivity
      have he : extra t ∣ m := by
        refine ⟨3 * t + 2, ?_⟩
        simp [extra, familyK, m]
        ring
      have hb : familyK t ∣ m := dvd_mul_right _ _
      exact (lcm_le_commonMultiple hm he hb).trans (by
        simp [familyN, familyK, m]
        nlinarith)

private lemma extra_lcm_even_le (t h : ℕ) (hhpos : 1 ≤ h)
    (hh : h ≤ familyK t) :
    Nat.lcm (extra t) (2 * h) ≤ familyN t := by
  by_cases hinterior : h ≤ familyK t - 2
  · have hdvd : Nat.lcm (extra t) (2 * h) ∣
        2 * (familyK t + 2) * h := by
      apply Nat.lcm_dvd
      · exact dvd_mul_right _ _
      · refine ⟨familyK t + 2, ?_⟩
        ring
    have hh2 : h + 2 ≤ familyK t := by
      have hk : 2 ≤ familyK t := by simp [familyK]
      omega
    exact (Nat.le_of_dvd (by positivity) hdvd).trans (by
      simp only [familyN, familyK] at *
      nlinarith)
  · have hcases : h = familyK t - 1 ∨ h = familyK t := by omega
    rcases hcases with hprev | htop
    · subst h
      let m := 12 * (t + 1) * (2 * t + 1)
      have hm : 0 < m := by positivity
      have he : extra t ∣ m := by
        refine ⟨2 * t + 1, ?_⟩
        simp [extra, familyK, m]
        ring
      have hb : 2 * (familyK t - 1) ∣ m := by
        refine ⟨2 * (t + 1), ?_⟩
        simp [familyK, m]
        ring
      exact (lcm_le_commonMultiple hm he hb).trans (by
        simp [familyN, familyK, m]
        nlinarith)
    · subst h
      let m := familyK t * (familyK t + 2)
      have hm : 0 < m := by positivity
      have he : extra t ∣ m := by
        refine ⟨3 * t + 2, ?_⟩
        simp [extra, familyK, m]
        ring
      have hb : 2 * familyK t ∣ m := by
        refine ⟨3 * t + 3, ?_⟩
        simp [familyK, m]
        ring
      exact (lcm_le_commonMultiple hm he hb).trans (by
        simp [familyN, familyK, m]
        nlinarith)

/-- Every member of Erdős's construction at `familyN t` has small LCM with
the extra element. -/
lemma extra_lcm_construction_le (t : ℕ) {b : ℕ}
    (hb : b ∈ erdosConstruction (familyN t)) :
    Nat.lcm (extra t) b ≤ familyN t := by
  have hb' := mem_erdosConstruction.mp hb
  rcases hb'.2.2 with hbLow | ⟨hbEven, hbHigh⟩
  · exact extra_lcm_low_le t b hb'.1 (low_member_le_familyK hbLow)
  · rcases hbEven with ⟨h, rfl⟩
    have hhpos : 1 ≤ h := by omega
    exact extra_lcm_even_le t h hhpos (high_half_le_familyK hbHigh)

lemma extra_le_familyN (t : ℕ) : extra t ≤ familyN t := by
  simp [extra, familyN, familyK]
  nlinarith

/-- The added element lies strictly beyond the upper endpoint `2k` of the
even part of Erdős's construction. -/
lemma extra_not_mem_erdosConstruction (t : ℕ) :
    extra t ∉ erdosConstruction (familyN t) := by
  intro he
  have he' := mem_erdosConstruction.mp he
  rcases he'.2.2 with heLow | ⟨_, heHigh⟩
  · simp [extra, familyN, familyK] at heLow
    norm_num [pow_two] at heLow
    nlinarith
  · simp [extra, familyN, familyK] at heHigh
    norm_num [pow_two] at heHigh
    nlinarith

/-- The enlarged construction is admissible for every member of the infinite
counterexample family. -/
theorem augmentedConstruction_lcmBounded (t : ℕ) :
    LcmBounded (familyN t)
      (insert (extra t) (erdosConstruction (familyN t))) := by
  have hB := erdosConstruction_lcmBounded (familyN t)
  constructor
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_Icc.mpr ⟨by simp [extra, familyK]; omega, extra_le_familyN t⟩
    · exact hB.1 ha
  · intro a ha b hb
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · simpa using extra_le_familyN t
      · exact extra_lcm_construction_le t hb
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · simpa [Nat.lcm_comm] using extra_lcm_construction_le t ha
      · exact hB.2 a ha b hb

/-- At every parameter in the family, the exact extremal size is strictly
larger than the size of Erdős's proposed construction. -/
theorem erdosConstruction_card_lt_g (t : ℕ) :
    (erdosConstruction (familyN t)).card < g (familyN t) := by
  have hle := card_le_g (augmentedConstruction_lcmBounded t)
  rw [Finset.card_insert_of_notMem (extra_not_mem_erdosConstruction t)] at hle
  omega

/-- The strict improvement has the explicit cardinality from the mathematical
writeup: `|B| = 9t+6`, so `g ≥ 9t+7`. -/
theorem nine_mul_add_seven_le_g_familyN (t : ℕ) :
    9 * t + 7 ≤ g (familyN t) := by
  have hle := card_le_g (augmentedConstruction_lcmBounded t)
  rw [Finset.card_insert_of_notMem (extra_not_mem_erdosConstruction t),
    card_erdosConstruction_familyN] at hle
  omega

/-- There are arbitrarily large `N` for which Erdős's proposed construction is
not extremal. -/
theorem erdosConstruction_not_eventually_extremal :
    ∀ M : ℕ, ∃ N ≥ M,
      (erdosConstruction N).card < g N := by
  intro M
  refine ⟨familyN M, ?_, erdosConstruction_card_lt_g M⟩
  simp [familyN, familyK]
  nlinarith

/-! ### Upstream module `MerLeanExperiment/TranslationCollision.lean` -/

theorem at_most_one_translated_shift {K : ℕ} (M N : ℕ) (hM : 2 ≤ M)
    (hN : 0 < N) (r ell : Fin K → ℤ) (hr : Function.Injective r)
    (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M)
    (a : Fin K → ℝ) (ha : ∀ i, 0 < a i)
    (hleft : ∀ i, a i * Real.sqrt (N : ℝ) < (shiftedPoint M r ell i : ℝ))
    (hsep : ∀ i j, i < j → ((r j - r i).natAbs : ℝ) ≤
      (shiftParityWeight (r i) (r j) : ℝ) * a i * a j)
    (A : Finset ℕ) (hA : LcmBounded N A) (h : ℤ) (hh : 0 ≤ h) :
    (Finset.univ.filter fun i => (shiftedPoint M r ell i + 2 * h).natAbs ∈ A ∧
      Nat.Coprime (shiftedPoint M r ell i + 2 * h).natAbs
        (shiftProductNat M r ell)).card ≤ 1 := by
  classical
  have hlow (i : Fin K) : a i * Real.sqrt (N : ℝ) <
      ((shiftedPoint M r ell i + 2 * h).natAbs : ℝ) := by
    have hhR : (0 : ℝ) ≤ h := by exact_mod_cast hh
    calc
      _ < (shiftedPoint M r ell i : ℝ) := hleft i
      _ ≤ (shiftedPoint M r ell i + 2 * h : ℤ) := by push_cast; linarith
      _ ≤ ((shiftedPoint M r ell i + 2 * h).natAbs : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        exact le_abs_self _
  have hcollision (i j : Fin K) (hij : i < j)
      (hiA : (shiftedPoint M r ell i + 2 * h).natAbs ∈ A)
      (hjA : (shiftedPoint M r ell j + 2 * h).natAbs ∈ A)
      (hicop : Nat.Coprime (shiftedPoint M r ell i + 2 * h).natAbs
        (shiftProductNat M r ell)) : False := by
    have hg := translated_shift_gcd_bound M hM r ell hr hsize i j hij h hicop
    have hgamma : 0 < shiftParityWeight (r i) (r j) := by
      unfold shiftParityWeight
      split_ifs <;> norm_num
    have hgt := lcm_gt_of_separated_lower_bounds (N : ℝ) (a i) (a j)
      ((r j - r i).natAbs : ℝ) (shiftedPoint M r ell i + 2 * h).natAbs
      (shiftedPoint M r ell j + 2 * h).natAbs (shiftParityWeight (r i) (r j))
      (Nat.cast_pos.mpr hN) (ha i) (ha j) hgamma (hlow i) (hlow j)
      (by exact_mod_cast hg) (hsep i j hij)
    have hle := hA.2 _ hiA _ hjA
    exact (not_lt_of_ge (Nat.cast_le.mpr hle)) hgt
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (hcollision i j hij hi'.1 hj'.1 hi'.2).elim
  · exact hij
  · exact (hcollision j i hij hj'.1 hi'.1 hj'.2).elim

/-! ### Upstream module `MerLeanExperiment/TranslationUnion.lean` -/

theorem translated_good_union_card {K : ℕ} (M N : ℕ) (hM : 2 ≤ M) (hN : 0 < N) (r ell : Fin K → ℤ) (hr : Function.Injective r) (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M) (a : Fin K → ℝ) (ha : ∀ i, 0 < a i) (hleft : ∀ i, a i * Real.sqrt (N : ℝ) < (shiftedPoint M r ell i : ℝ)) (hsep : ∀ i j, i < j → ((r j - r i).natAbs : ℝ) ≤ (shiftParityWeight (r i) (r j) : ℝ) * a i * a j) (A : Finset ℕ) (hA : LcmBounded N A) (H : ℤ) : (goodTranslateUnion A (shiftProductNat M r ell) (shiftedPoint M r ell) H).card ≤ H.toNat := by
  classical
  unfold goodTranslateUnion
  calc
    _ ≤ ∑ h ∈ Finset.Icc 1 H,
        ((Finset.univ.filter fun i => (shiftedPoint M r ell i + 2 * h).natAbs ∈ A ∧
          Nat.Coprime (shiftedPoint M r ell i + 2 * h).natAbs
            (shiftProductNat M r ell)).image fun i =>
              (shiftedPoint M r ell i + 2 * h).natAbs).card := Finset.card_biUnion_le
    _ ≤ ∑ _h ∈ Finset.Icc 1 H, 1 := by
      apply Finset.sum_le_sum
      intro h hh
      exact Finset.card_image_le.trans
        (at_most_one_translated_shift M N hM hN r ell hr hsize a ha hleft hsep A hA h
          (by have := (Finset.mem_Icc.mp hh).1; omega))
    _ = H.toNat := by simp

/-! ### Upstream module `MerLeanExperiment/PackingCellUnion.lean` -/

theorem packing_cell_union_bound {K : ℕ} (M N : ℕ) (hM : 2 ≤ M)
    (hN : 0 < N) (r ell : Fin K → ℤ) (hr : Function.Injective r)
    (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M)
    (c E : Fin K → ℝ) (hc : ∀ i, 0 < c i) (hE : ∀ i, 0 ≤ E i)
    (delta B : ℝ) (hdelta : 0 ≤ delta) (hB : ∀ i, c i + delta ≤ B)
    (hpoint : ∀ i, c i * Real.sqrt (N : ℝ) < (shiftedPoint M r ell i : ℝ) ∧
      (shiftedPoint M r ell i : ℝ) ≤ c i * Real.sqrt (N : ℝ) + E i)
    (hsep : ∀ i j, i < j → ((r j - r i).natAbs : ℝ) ≤
      (shiftParityWeight (r i) (r j) : ℝ) * c i * c j)
    (A : Finset ℕ) (hA : LcmBounded N A) :
    ((packingCellUnion A r c delta (Real.sqrt (N : ℝ))).card : ℝ) ≤
      delta * Real.sqrt (N : ℝ) / 2 + (∑ i, (E i + 1)) +
        ((packingBadPoints A (shiftProductNat M r ell) B (Real.sqrt (N : ℝ))).card : ℝ) := by
  classical
  let R : ℝ := Real.sqrt (N : ℝ)
  let D := shiftProductNat M r ell
  let H : ℤ := ⌊delta * R / 2⌋
  let S : Fin K → Finset ℕ := fun i =>
    (realIntIoc (c i * R) (c i * R + E i)).image Int.natAbs
  let U := Finset.univ.biUnion S
  let G := goodTranslateUnion A D (shiftedPoint M r ell) H
  let Bad := packingBadPoints A D B R
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hfact : Even (M.factorial : ℤ) := by
    apply even_iff_two_dvd.mpr
    exact_mod_cast Nat.dvd_factorial (by omega : 0 < 2) hM
  have hcover : packingCellUnion A r c delta R ⊆ (G ∪ U) ∪ Bad := by
    intro n hn
    obtain ⟨i, _, hni⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨hnA, hnlo, hnhi, hnpar⟩ := Finset.mem_filter.mp hni
    by_cases hcop : Nat.Coprime n D
    · have hpar : Even ((n : ℤ) - shiftedPoint M r ell i) := by
        have heq : (n : ℤ) - shiftedPoint M r ell i =
            ((n : ℤ) - r i) - (M.factorial : ℤ) * ell i := by
          unfold shiftedPoint
          ring
        rw [heq]
        exact hnpar.sub (hfact.mul_right (ell i))
      have hnloR : c i * R < ((n : ℤ) : ℝ) := by exact_mod_cast hnlo
      have hnhiR : ((n : ℤ) : ℝ) ≤ (c i + delta) * R := by exact_mod_cast hnhi
      rcases cell_point_cover (c i) delta R (E i) (shiftedPoint M r ell i) (n : ℤ)
          (hpoint i).1 (hpoint i).2 hnloR hnhiR hpar with hshort | ⟨h, hh, heq⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_univ _, ?_⟩
        exact Finset.mem_image.mpr ⟨(n : ℤ), hshort, by simp⟩
      · have hnabs : (shiftedPoint M r ell i + 2 * h).natAbs = n := by rw [← heq]; simp
        apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨h, hh, ?_⟩
        apply Finset.mem_image.mpr
        refine ⟨i, ?_, hnabs⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnabs]
        exact ⟨hnA, hcop⟩
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨hnA, hnhi.trans (mul_le_mul_of_nonneg_right (hB i) hR), hcop⟩
  have hGnat : G.card ≤ H.toNat :=
    translated_good_union_card M N hM hN r ell hr hsize c hc
      (fun i => (hpoint i).1) hsep A hA H
  have hHnonneg : 0 ≤ H := Int.floor_nonneg.mpr (by positivity)
  have hH : (H.toNat : ℝ) ≤ delta * R / 2 := by
    have he : (H.toNat : ℝ) = (H : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hHnonneg
    rw [he]
    exact Int.floor_le _
  have hG : (G.card : ℝ) ≤ delta * R / 2 := (Nat.cast_le.mpr hGnat).trans hH
  have hU : (U.card : ℝ) ≤ ∑ i, (E i + 1) := by
    have hUnat : U.card ≤ ∑ i, (S i).card := Finset.card_biUnion_le
    calc
      _ ≤ ∑ i, ((S i).card : ℝ) := by exact_mod_cast hUnat
      _ ≤ ∑ i, (E i + 1) := by
        apply Finset.sum_le_sum
        intro i _
        have himg : (S i).card ≤ (realIntIoc (c i * R) (c i * R + E i)).card :=
          Finset.card_image_le
        have hcount := card_realIntIoc_le (c i * R) (c i * R + E i) (by linarith [hE i])
        exact (Nat.cast_le.mpr himg).trans (by linarith)
  have hcardNat : (packingCellUnion A r c delta R).card ≤ G.card + U.card + Bad.card :=
    (Finset.card_le_card hcover).trans
      ((Finset.card_union_le (G ∪ U) Bad).trans
        (Nat.add_le_add_right (Finset.card_union_le G U) _))
  have hcard : ((packingCellUnion A r c delta R).card : ℝ) ≤
      (G.card : ℝ) + U.card + Bad.card := by exact_mod_cast hcardNat
  change ((packingCellUnion A r c delta R).card : ℝ) ≤
    delta * R / 2 + (∑ i, (E i + 1)) + (Bad.card : ℝ)
  linarith

/-! ### Upstream module `MerLeanExperiment/PackingBadBridge.lean` -/

theorem packing_bad_points_le_exceptions (N : ℕ) (A : Finset ℕ) (hA : LcmBounded N A) (D : ℕ) (B R : ℝ) : (packingBadPoints A D B R).card ≤ ((realIntIoc 0 (B * R)).filter fun n => ¬ Nat.Coprime n.natAbs D).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun n : ℕ => (n : ℤ))
  · intro n hn
    obtain ⟨hnA, hupper, hbad⟩ := Finset.mem_filter.mp hn
    have hnpos : 0 < n := by
      have := (Finset.mem_Icc.mp (hA.1 hnA)).1
      omega
    apply Finset.mem_filter.mpr
    refine ⟨(mem_realIntIoc _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
    · change (0 : ℝ) < (n : ℝ)
      exact_mod_cast hnpos
    · change (n : ℝ) ≤ B * R
      exact hupper
    · simpa using hbad
  · intro n _ m _ he
    change (n : ℤ) = (m : ℤ) at he
    exact_mod_cast he

/-! ### Upstream module `MerLeanExperiment/CRTResidues.lean` -/

/-- Pull a finite product of residue sets back along the actual Chinese remainder equivalence. -/
noncomputable def jointResidues {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (R : ∀ i, Finset (ZMod (m i))) : Finset (ZMod (∏ i, m i)) := by
  classical
  exact (Fintype.piFinset R).map (ZMod.prodEquivPi m hc).symm.toEquiv.toEmbedding

/-- The CRT residue set has its expected cardinality and exactly its intended membership test. -/
theorem joint_residue_spec {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (R : ∀ i, Finset (ZMod (m i))) :
    (jointResidues m hc R).card = ∏ i, (R i).card ∧
      ∀ x : ℤ, (x : ZMod (∏ i, m i)) ∈ jointResidues m hc R ↔
        ∀ i, (x : ZMod (m i)) ∈ R i := by
  classical
  constructor
  · simp [jointResidues]
  · intro x
    have hcoords : ZMod.prodEquivPi m hc (x : ZMod (∏ i, m i)) =
        fun i => (x : ZMod (m i)) := by
      ext i
      simp
    constructor
    · rintro hx
      obtain ⟨y, hy, heq⟩ := Finset.mem_map.mp hx
      have hyx : y = fun i => (x : ZMod (m i)) := by
        rw [← hcoords, ← heq]
        exact ((ZMod.prodEquivPi m hc).apply_symm_apply y).symm
      simpa only [hyx] using Fintype.mem_piFinset.mp hy
    · intro hx
      apply Finset.mem_map.mpr
      refine ⟨ZMod.prodEquivPi m hc (x : ZMod (∏ i, m i)), ?_, ?_⟩
      · rw [hcoords]
        exact Fintype.mem_piFinset.mpr hx
      · exact (ZMod.prodEquivPi m hc).symm_apply_apply _

/-! ### Upstream module `MerLeanExperiment/ResidueCount.lean` -/

/-- A residue class has discrepancy at most one in an integer interval. -/
theorem residue_count_discrepancy (a b v : ℤ) (r : ℕ)
    (hr : 0 < r) (hab : a ≤ b) :
    |(({x ∈ Finset.Ioc a b | Int.ModEq (r : ℤ) x v}).card : ℚ) -
      ((b - a : ℤ) : ℚ) / r| ≤ 1 := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hrZ : (0 : ℤ) < r := by exact_mod_cast hr
  have habQ : (a : ℚ) ≤ b := by exact_mod_cast hab
  have hmono : ⌊(a - v : ℚ) / r⌋ ≤ ⌊(b - v : ℚ) / r⌋ :=
    Int.floor_mono (div_le_div_of_nonneg_right (sub_le_sub_right habQ _) hrQ.le)
  have hc := Int.Ioc_filter_modEq_card a b hrZ v
  simp only [Int.cast_natCast] at hc
  rw [max_eq_left (sub_nonneg.mpr hmono)] at hc
  have hcQ : (({x ∈ Finset.Ioc a b | Int.ModEq (r : ℤ) x v}).card : ℚ) =
      (⌊(b - v : ℚ) / r⌋ : ℚ) - (⌊(a - v : ℚ) / r⌋ : ℚ) := by
    exact_mod_cast hc
  rw [hcQ]
  have haL := Int.floor_le ((a - v : ℚ) / r)
  have haU := Int.lt_floor_add_one ((a - v : ℚ) / r)
  have hbL := Int.floor_le ((b - v : ℚ) / r)
  have hbU := Int.lt_floor_add_one ((b - v : ℚ) / r)
  have hdiff : ((b - a : ℤ) : ℚ) / r =
      (b - v : ℚ) / r - (a - v : ℚ) / r := by
    push_cast
    ring
  rw [hdiff, abs_le]
  constructor <;> linarith

/-! ### Upstream module `MerLeanExperiment/ResidueSetCount.lean` -/

/-- A finite set of residue classes has discrepancy at most its cardinality
in an integer interval. -/
theorem residue_set_discrepancy (a b : ℤ) (r : ℕ) (hr : 0 < r) (hab : a ≤ b)
    (R : Finset (ZMod r)) :
    |(({x ∈ (Finset.Ioc a b : Finset ℤ) | ((x : ℤ) : ZMod r) ∈ R}).card : ℚ) -
      ((b - a : ℤ) : ℚ) / r * R.card| ≤ R.card := by
  have hresidue (x : ℤ) (v : ZMod r) :
      (((x : ℤ) : ZMod r) = v) ↔ Int.ModEq (r : ℤ) x (v.val : ℤ) := by
    have hv : (v.val : ZMod r) = v :=
      @ZMod.natCast_zmod_val r ⟨Nat.ne_of_gt hr⟩ v
    calc
      (((x : ℤ) : ZMod r) = v) ↔
          (((x : ℤ) : ZMod r) = (v.val : ZMod r)) := by rw [hv]
      _ ↔ Int.ModEq (r : ℤ) x (v.val : ℤ) := by
        simpa only [Int.cast_natCast] using
          (ZMod.intCast_eq_intCast_iff x (v.val : ℤ) r)
  have hsingle (v : ZMod r) :
      |((({x ∈ (Finset.Ioc a b : Finset ℤ) | ((x : ℤ) : ZMod r) = v}).card : ℚ) -
          ((b - a : ℤ) : ℚ) / r)| ≤ 1 := by
    simpa only [hresidue] using
      residue_count_discrepancy a b (v.val : ℤ) r hr hab
  have hcard :
      (∑ v ∈ R, ({x ∈ (Finset.Ioc a b : Finset ℤ) | ((x : ℤ) : ZMod r) = v}).card) =
        ({x ∈ (Finset.Ioc a b : Finset ℤ) | ((x : ℤ) : ZMod r) ∈ R}).card :=
    Finset.sum_card_fiberwise_eq_card_filter
      ((Finset.Ioc a b : Finset ℤ)) R (fun x : ℤ => ((x : ℤ) : ZMod r))
  have hdecomp :
      (({x ∈ (Finset.Ioc a b : Finset ℤ) | ((x : ℤ) : ZMod r) ∈ R}).card : ℚ) -
          ((b - a : ℤ) : ℚ) / r * R.card =
        ∑ v ∈ R,
          ((({x ∈ (Finset.Ioc a b : Finset ℤ) | ((x : ℤ) : ZMod r) = v}).card : ℚ) -
            ((b - a : ℤ) : ℚ) / r) := by
    rw [← hcard]
    push_cast
    rw [Finset.sum_sub_distrib]
    simp
    ring
  rw [hdecomp]
  calc
    |∑ v ∈ R,
        ((({x ∈ (Finset.Ioc a b : Finset ℤ) | ((x : ℤ) : ZMod r) = v}).card : ℚ) -
          ((b - a : ℤ) : ℚ) / r)|
        ≤ ∑ v ∈ R,
            |((({x ∈ (Finset.Ioc a b : Finset ℤ) | ((x : ℤ) : ZMod r) = v}).card : ℚ) -
              ((b - a : ℤ) : ℚ) / r)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ R, (1 : ℚ) := by
      exact Finset.sum_le_sum fun v hv => hsingle v
    _ = R.card := by simp

/-! ### Upstream module `MerLeanExperiment/JointResidueCount.lean` -/

/-- Uniform intersection-count error, obtained from the actual CRT equivalence. -/
theorem joint_residue_discrepancy {ι : Type*} [Fintype ι]
    (a b : ℤ) (hab : a ≤ b) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (R : ∀ i, Finset (ZMod (m i))) :
    |(({x ∈ Finset.Ioc a b | ∀ i, ((x : ℤ) : ZMod (m i)) ∈ R i}).card : ℚ) -
      ((b - a : ℤ) : ℚ) * ∏ i, ((R i).card : ℚ) / m i| ≤
      ∏ i, ((R i).card : ℚ) := by
  classical
  have hpos : 0 < ∏ i, m i := Finset.prod_pos fun i _ => hm i
  have hspec := joint_residue_spec m hc R
  have hcount := residue_set_discrepancy a b (∏ i, m i) hpos hab
    (jointResidues m hc R)
  simp only [hspec.2, hspec.1, Nat.cast_prod] at hcount
  rw [Finset.prod_div_distrib]
  convert hcount using 2
  ring

/-! ### Upstream module `MerLeanExperiment/SieveError.lean` -/

/-- The elementary finite sieve error bound, with explicit intersection estimates. -/
theorem sieve_discrepancy_bound {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (bad : ι → Finset α) (L : ℚ) (rho err : ι → ℚ)
    (herr : ∀ T : Finset ι,
      |((T.inf bad).card : ℚ) - L * ∏ i ∈ T, rho i| ≤ ∏ i ∈ T, err i) :
    |(((Finset.univ : Finset ι).inf fun i => (bad i)ᶜ).card : ℚ) -
      L * ∏ i, (1 - rho i)| ≤ ∏ i, (1 + err i) := by
  classical
  have hIE : (((Finset.univ : Finset ι).inf fun i => (bad i)ᶜ).card : ℚ) =
      ∑ T ∈ (Finset.univ : Finset ι).powerset,
        (-1 : ℚ) ^ T.card * (T.inf bad).card := by
    exact_mod_cast Finset.inclusion_exclusion_card_inf_compl
      (Finset.univ : Finset ι) bad
  have hprod : (∏ i, (1 - rho i)) =
      ∑ T ∈ (Finset.univ : Finset ι).powerset,
        (-1 : ℚ) ^ T.card * ∏ i ∈ T, rho i := by
    simpa using Finset.prod_sub (fun _ : ι => (1 : ℚ)) rho Finset.univ
  have heq : (((Finset.univ : Finset ι).inf fun i => (bad i)ᶜ).card : ℚ) -
      L * ∏ i, (1 - rho i) =
      ∑ T ∈ (Finset.univ : Finset ι).powerset,
        (-1 : ℚ) ^ T.card * ((T.inf bad).card - L * ∏ i ∈ T, rho i) := by
    rw [hIE, hprod, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro T _
    ring
  rw [heq, Finset.prod_one_add]
  calc
    _ ≤ ∑ T ∈ (Finset.univ : Finset ι).powerset,
        |(-1 : ℚ) ^ T.card * ((T.inf bad).card - L * ∏ i ∈ T, rho i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro T _
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using herr T

/-! ### Upstream module `MerLeanExperiment/IntervalSieve.lean` -/

/-- Elementary sieve on an actual integer interval, with all CRT estimates discharged. -/
theorem interval_sieve_discrepancy {ι : Type*} [Fintype ι]
    (a b : ℤ) (hab : a ≤ b) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (R : ∀ i, Finset (ZMod (m i))) :
    |(({x ∈ Finset.Ioc a b | ∀ i, ((x : ℤ) : ZMod (m i)) ∉ R i}).card : ℚ) -
      ((b - a : ℤ) : ℚ) * ∏ i, (1 - ((R i).card : ℚ) / m i)| ≤
      ∏ i, (1 + ((R i).card : ℚ)) := by
  classical
  let U := Finset.Ioc a b
  let bad : ι → Finset U := fun i =>
    Finset.univ.filter fun x => ((x.val : ℤ) : ZMod (m i)) ∈ R i
  have hmem (T : Finset ι) (f : ι → Finset U) (x : U) :
      x ∈ T.inf f ↔ ∀ i ∈ T, x ∈ f i := by
    induction T using Finset.induction_on with
    | empty => simp [Finset.inf_empty]
    | @insert i T hi ih => simp [Finset.inf_insert, ih]
  have hcard (p : ℤ → Prop) [DecidablePred p] :
      (Finset.univ.filter fun x : U => p x.val).card = (U.filter p).card := by
    apply Finset.card_bij (fun x _ => x.val)
    · intro x hx
      exact Finset.mem_filter.mpr ⟨x.property, (Finset.mem_filter.mp hx).2⟩
    · intro x _ y _ hxy
      exact Subtype.ext hxy
    · intro x hx
      exact ⟨⟨x, (Finset.mem_filter.mp hx).1⟩,
        by simpa using (Finset.mem_filter.mp hx).2, rfl⟩
  have herr (T : Finset ι) :
      |((T.inf bad).card : ℚ) - ((b - a : ℤ) : ℚ) *
        ∏ i ∈ T, ((R i).card : ℚ) / m i| ≤ ∏ i ∈ T, ((R i).card : ℚ) := by
    have hcT : Pairwise (fun i j : T => (m i.val).Coprime (m j.val)) := by
      intro i j hij
      exact hc (fun h => hij (Subtype.ext h))
    have h := joint_residue_discrepancy a b hab (fun i : T => m i.val)
      (fun i => hm i.val) hcT (fun i => R i.val)
    have heq : T.inf bad = Finset.univ.filter
        (fun x : U => ∀ i ∈ T, ((x.val : ℤ) : ZMod (m i)) ∈ R i) := by
      ext x
      simpa [bad] using hmem T bad x
    rw [heq, hcard (fun x : ℤ =>
      ∀ i ∈ T, ((x : ℤ) : ZMod (m i)) ∈ R i)]
    have hforall :
        {x ∈ Finset.Ioc a b |
            ∀ i : T, ((x : ℤ) : ZMod (m i.val)) ∈ R i.val} =
          U.filter (fun x : ℤ =>
            ∀ i ∈ T, ((x : ℤ) : ZMod (m i)) ∈ R i) := by
      ext x
      simp only [U, Finset.mem_filter, Subtype.forall]
    have hrho :
        (∏ i : T, ((R i.val).card : ℚ) / m i.val) =
          ∏ i ∈ T, ((R i).card : ℚ) / m i :=
      Finset.prod_coe_sort T (fun i : ι => ((R i).card : ℚ) / m i)
    have herrprod :
        (∏ i : T, ((R i.val).card : ℚ)) =
          ∏ i ∈ T, ((R i).card : ℚ) :=
      Finset.prod_coe_sort T (fun i : ι => ((R i).card : ℚ))
    rw [← hforall, ← hrho, ← herrprod]
    exact h
  have h := sieve_discrepancy_bound bad ((b - a : ℤ) : ℚ)
    (fun i => ((R i).card : ℚ) / m i) (fun i => ((R i).card : ℚ)) herr
  have heq : (Finset.univ.inf fun i => (bad i)ᶜ) = Finset.univ.filter
      (fun x : U => ∀ i, ((x.val : ℤ) : ZMod (m i)) ∉ R i) := by
    ext x
    simpa [bad] using hmem (Finset.univ : Finset ι) (fun i => (bad i)ᶜ) x
  rw [heq, hcard (fun x : ℤ =>
    ∀ i, ((x : ℤ) : ZMod (m i)) ∉ R i)] at h
  exact h

/-! ### Upstream module `MerLeanExperiment/FiniteAvoidance.lean` -/

/-- The finite set of primes at most `Z`. -/
def sievePrimes (Z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Z).filter Nat.Prime

/-- A prime index in the finite sieve up to `Z`. -/
abbrev SievePrime (Z : ℕ) := ↥(sievePrimes Z)

/-- A sufficiently long integer interval contains a point avoiding all the
prescribed residue sets at primes up to `Z`. -/
theorem exists_interval_avoiding
    (M Z : ℕ) (hM : 3 ≤ M) (a b : ℤ) (hab : a ≤ b)
    (R : (p : SievePrime Z) → Finset (ZMod p.val))
    (hsmall : ∀ p, p.val ≤ M → R p = ∅)
    (hcard : ∀ p, 2 * (R p).card ≤ M)
    (hlength : (((2 * M) ^ Z : ℕ) : ℤ) < b - a) :
    ∃ k ∈ Finset.Ioc a b, ∀ p, (k : ZMod p.val) ∉ R p := by
  classical
  have hprime (p : SievePrime Z) : p.val.Prime :=
    (Finset.mem_filter.mp p.property).2
  have hm (p : SievePrime Z) : 0 < p.val := (hprime p).pos
  have hc : Pairwise (fun p q : SievePrime Z => p.val.Coprime q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (hprime p) (hprime q)).2
      (fun h => hpq (Subtype.ext h))
  have hsieve := interval_sieve_discrepancy a b hab (fun p : SievePrime Z => p.val)
    hm hc R
  let W : ℚ := ∏ p : SievePrime Z,
    (1 - ((R p).card : ℚ) / p.val)
  let E : ℚ := ∏ p : SievePrime Z, (1 + ((R p).card : ℚ))
  let n := Fintype.card (SievePrime Z)
  have hn : n ≤ Z := by
    dsimp [n]
    rw [Fintype.card_coe]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  have htwo_card_le (p : SievePrime Z) : 2 * (R p).card ≤ p.val := by
    by_cases hpM : p.val ≤ M
    · rw [hsmall p hpM]
      simp
    · exact (hcard p).trans (Nat.le_of_lt (lt_of_not_ge hpM))
  have hfactor (p : SievePrime Z) :
      (1 / 2 : ℚ) ≤ 1 - ((R p).card : ℚ) / p.val := by
    have hpQ : (0 : ℚ) < p.val := by exact_mod_cast hm p
    have htwoQ : (2 : ℚ) * (R p).card ≤ p.val := by
      exact_mod_cast htwo_card_le p
    have hfrac : ((R p).card : ℚ) / p.val ≤ 1 / 2 := by
      rw [div_le_iff₀ hpQ]
      nlinarith
    linarith
  have hWn : (1 / 2 : ℚ) ^ n ≤ W := by
    have hprod := Finset.prod_le_prod
      (s := (Finset.univ : Finset (SievePrime Z)))
      (f := fun _ => (1 / 2 : ℚ))
      (g := fun p => 1 - ((R p).card : ℚ) / p.val)
      (by intro p hp; norm_num)
      (by intro p hp; exact hfactor p)
    simpa [W, n] using hprod
  have hWZ : (1 / 2 : ℚ) ^ Z ≤ W :=
    (pow_le_pow_of_le_one (a := (1 / 2 : ℚ)) (by norm_num) (by norm_num) hn).trans hWn
  have herrfactor (p : SievePrime Z) :
      (1 + ((R p).card : ℚ)) ≤ M := by
    have hpCard := hcard p
    exact_mod_cast (show 1 + (R p).card ≤ M by omega)
  have hEn : E ≤ (M : ℚ) ^ n := by
    have hprod := Finset.prod_le_prod
      (s := (Finset.univ : Finset (SievePrime Z)))
      (f := fun p => (1 + ((R p).card : ℚ)))
      (g := fun _ => (M : ℚ))
      (by intro p hp; positivity)
      (by intro p hp; exact herrfactor p)
    simpa [E, n] using hprod
  have hEZ : E ≤ (M : ℚ) ^ Z :=
    hEn.trans (pow_le_pow_right₀ (a := (M : ℚ)) (by exact_mod_cast hM.trans' (by decide)) hn)
  have hlengthQ : (((2 * M) ^ Z : ℕ) : ℚ) < ((b - a : ℤ) : ℚ) := by
    exact_mod_cast hlength
  have hhalf_pos : (0 : ℚ) < (1 / 2 : ℚ) ^ Z := pow_pos (by norm_num) Z
  have hidentity :
      (((2 * M) ^ Z : ℕ) : ℚ) * (1 / 2 : ℚ) ^ Z = (M : ℚ) ^ Z := by
    push_cast
    rw [← mul_pow]
    congr 1
    ring
  have hL0 : (0 : ℚ) ≤ ((b - a : ℤ) : ℚ) := by
    exact_mod_cast sub_nonneg.mpr hab
  have hstrict : E < ((b - a : ℤ) : ℚ) * W := by
    calc
      E ≤ (M : ℚ) ^ Z := hEZ
      _ = (((2 * M) ^ Z : ℕ) : ℚ) * (1 / 2 : ℚ) ^ Z := hidentity.symm
      _ < ((b - a : ℤ) : ℚ) * (1 / 2 : ℚ) ^ Z :=
        mul_lt_mul_of_pos_right hlengthQ hhalf_pos
      _ ≤ ((b - a : ℤ) : ℚ) * W := mul_le_mul_of_nonneg_left hWZ hL0
  let good := {k ∈ Finset.Ioc a b |
    ∀ p : SievePrime Z, (k : ZMod p.val) ∉ R p}
  have hgood_pos : 0 < good.card := by
    by_contra hnot
    have hzero : good.card = 0 := Nat.eq_zero_of_not_pos hnot
    have hsieve' :
        |(good.card : ℚ) - ((b - a : ℤ) : ℚ) * W| ≤ E := by
      simpa [good, W, E] using hsieve
    rw [hzero, Nat.cast_zero, zero_sub, abs_neg] at hsieve'
    exact (not_lt_of_ge ((le_abs_self _).trans hsieve')) hstrict
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hgood_pos
  have hk' := Finset.mem_filter.mp hk
  exact ⟨k, hk'.1, hk'.2⟩

/-! ### Upstream module `MerLeanExperiment/LinearResidues.lean` -/

/-- The actual union of roots of the integer linear forms modulo a prime. -/
noncomputable def linearBadResidues (p : ℕ) [Fact p.Prime]
    {ι : Type*} [Fintype ι] (A B : ι → ℤ) : Finset (ZMod p) := by
  classical
  exact Finset.univ.biUnion fun i =>
    Finset.univ.filter fun z => (A i : ZMod p) * z + B i = 0

theorem linear_bad_residue_spec (p : ℕ) [Fact p.Prime]
    {ι : Type*} [Fintype ι] (A B : ι → ℤ)
    (hprim : ∀ i, IsCoprime (A i) (B i)) :
    (linearBadResidues p A B).card ≤ Fintype.card ι ∧
      ∀ k : ℤ, (k : ZMod p) ∈ linearBadResidues p A B ↔
        (p : ℤ) ∣ ∏ i, (A i * k + B i) := by
  classical
  have hsingle (i : ι) :
      (Finset.univ.filter fun z : ZMod p => (A i : ZMod p) * z + B i = 0).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro z hz w hw
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    have hcop := (hprim i).map (Int.castRingHom (ZMod p))
    obtain ⟨u, v, huv⟩ := hcop
    by_cases ha : (A i : ZMod p) = 0
    · have hb : (B i : ZMod p) = 0 := by simpa [ha] using hz'
      change u * (A i : ZMod p) + v * (B i : ZMod p) = 1 at huv
      simp only [ha, hb, mul_zero, add_zero] at huv
      exact False.elim (zero_ne_one huv)
    · apply mul_left_cancel₀ ha
      exact add_right_cancel (hz'.trans hw'.symm)
  constructor
  · calc
      (linearBadResidues p A B).card ≤
          ∑ i : ι, (Finset.univ.filter fun z : ZMod p =>
            (A i : ZMod p) * z + B i = 0).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : ι, 1 := Finset.sum_le_sum fun i _ => hsingle i
      _ = Fintype.card ι := by simp
  · intro k
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [linearBadResidues, Finset.prod_eq_zero_iff]

theorem linear_bad_residues_empty (p : ℕ) [Fact p.Prime]
    {ι : Type*} [Fintype ι] (A B : ι → ℤ)
    (hprim : ∀ i, IsCoprime (A i) (B i))
    (hno : ∀ k : ℤ, ¬ (p : ℤ) ∣ ∏ i, (A i * k + B i)) :
    linearBadResidues p A B = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hzcast : (((z.val : ℕ) : ℤ) : ZMod p) = z := by simp
  rw [← hzcast] at hz
  exact hno z.val ((linear_bad_residue_spec p A B hprim).2 z.val |>.mp hz)

/-! ### Upstream module `MerLeanExperiment/SieveLength.lean` -/

theorem sieve_cutoff_power_bound (M : ℕ) (hM : 3 ≤ M) (x : ℝ) (hx : 1 ≤ x) :
    (((2 * M)^⌊Real.log x / (8 * Real.log M)⌋₊ : ℕ) : ℝ) ≤
      x ^ (5 / 24 : ℝ) := by
  let z : ℕ := ⌊Real.log x / (8 * Real.log M)⌋₊
  have hMr : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos hMr
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have h8M : (8 : ℝ) ≤ (M : ℝ) ^ 2 := by
    have hMr3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith [sq_nonneg ((M : ℝ) - 3)]
  have hlog8M := Real.strictMonoOn_log.monotoneOn
    (by norm_num : (0 : ℝ) < 8) (by positivity : (0 : ℝ) < (M : ℝ) ^ 2) h8M
  have hlog2M : 3 * Real.log 2 ≤ 2 * Real.log (M : ℝ) := by
    calc
      3 * Real.log 2 = Real.log (8 : ℝ) := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      _ ≤ Real.log ((M : ℝ) ^ 2) := hlog8M
      _ = 2 * Real.log (M : ℝ) := by rw [Real.log_pow]; norm_num
  have hlogBase : Real.log ((2 * M : ℕ) : ℝ) ≤ (5 / 3 : ℝ) * Real.log M := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by positivity : (M : ℝ) ≠ 0)]
    nlinarith
  have hz : (z : ℝ) ≤ Real.log x / (8 * Real.log M) := by
    exact Nat.floor_le (div_nonneg hlogx (by positivity))
  have hlogpow : Real.log (((2 * M : ℕ) : ℝ)) * z ≤ Real.log x * (5 / 24 : ℝ) := by
    have hbaseNonneg : 0 ≤ Real.log (((2 * M : ℕ) : ℝ)) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 2 * M by omega)
    calc
      Real.log (((2 * M : ℕ) : ℝ)) * z ≤
          Real.log (((2 * M : ℕ) : ℝ)) * (Real.log x / (8 * Real.log M)) :=
        mul_le_mul_of_nonneg_left hz hbaseNonneg
      _ ≤ ((5 / 3 : ℝ) * Real.log M) * (Real.log x / (8 * Real.log M)) :=
        mul_le_mul_of_nonneg_right hlogBase (div_nonneg hlogx (by positivity))
      _ = Real.log x * (5 / 24 : ℝ) := by field_simp; ring
  rw [show (((2 * M) ^ z : ℕ) : ℝ) = (((2 * M : ℕ) : ℝ) ^ z) by norm_cast]
  rw [← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by linarith)]
  exact Real.exp_le_exp.mpr hlogpow

theorem eventually_sieve_length (M : ℕ) (hM : 3 ≤ M) (c0 : ℝ) (hc0 : 0 < c0) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (((2 * M)^⌊Real.log x / (8 * Real.log M)⌋₊ : ℕ) : ℝ) <
        c0 * x ^ (1 / 4 : ℝ) - 1 := by
  have ht24 := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 24)
  have ht4 := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  have he24 : ∀ᶠ x : ℝ in Filter.atTop, 2 / c0 < x ^ (1 / 24 : ℝ) :=
    ht24.eventually (Filter.eventually_gt_atTop (2 / c0))
  have he4 : ∀ᶠ x : ℝ in Filter.atTop, 2 / c0 < x ^ (1 / 4 : ℝ) :=
    ht4.eventually (Filter.eventually_gt_atTop (2 / c0))
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), he24, he4] with x hx hx24 hx4
  have hbound := sieve_cutoff_power_bound M hM x hx
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hadd : x ^ (1 / 4 : ℝ) = x ^ (5 / 24 : ℝ) * x ^ (1 / 24 : ℝ) := by
    rw [← Real.rpow_add hxp]
    congr 1
    norm_num
  have hx5 : 0 < x ^ (5 / 24 : ℝ) := Real.rpow_pos_of_pos hxp _
  have hx24' : 2 < c0 * x ^ (1 / 24 : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hc0).mp hx24
  have hcprod : 2 * x ^ (5 / 24 : ℝ) < c0 * x ^ (1 / 4 : ℝ) := by
    rw [hadd]
    nlinarith [mul_lt_mul_of_pos_right hx24' hx5]
  have hc4 : 2 < c0 * x ^ (1 / 4 : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hc0).mp hx4
  nlinarith

/-! ### Upstream module `MerLeanExperiment/UniformAvoidance.lean` -/

theorem chen_uniform_linear_avoidance (M : ℕ) (hM : 3 ≤ M) (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ X0 : ℝ, 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x → ∀ c1 c2 : ℝ, c0 ≤ c1 →
      ∀ t : ℕ, 2 * t ≤ M → ∀ A B : Fin t → ℤ,
      (∀ i, IsCoprime (A i) (B i)) →
      (∀ p : ℕ, p.Prime → p ≤ M → ∀ n : ℤ,
        ¬ (p : ℤ) ∣ ∏ i, (A i * n + B i)) →
      ∃ k : ℤ, c1 * x ^ (1 / 2 : ℝ) + c2 < (k : ℝ) ∧
        (k : ℝ) < c1 * (x ^ (1 / 2 : ℝ) + x ^ (1 / 4 : ℝ)) + c2 ∧
        ∀ p : ℕ, p.Prime → (p : ℤ) ∣ ∏ i, (A i * k + B i) →
          Real.log x / (8 * Real.log M) < (p : ℝ) := by
  classical
  obtain ⟨X, hX⟩ := (Filter.eventually_atTop.1 (eventually_sieve_length M hM c0 hc0))
  refine ⟨max 1 X, le_max_left _ _, ?_⟩
  intro x hx c1 c2 hc1 t ht A B hprim hsmall
  have hx1 : 1 ≤ x := le_trans (le_max_left 1 X) hx
  have hxX : X ≤ x := le_trans (le_max_right 1 X) hx
  have hlen0 := hX x hxX
  let q : ℝ := Real.log x / (8 * Real.log M)
  let Z : ℕ := ⌊q⌋₊
  let L : ℝ := c1 * x ^ (1 / 2 : ℝ) + c2
  let U : ℝ := c1 * (x ^ (1 / 2 : ℝ) + x ^ (1 / 4 : ℝ)) + c2
  let a : ℤ := ⌊L⌋
  let b : ℤ := ⌈U⌉ - 1
  have hc1pos : 0 < c1 := lt_of_lt_of_le hc0 hc1
  have hLU : U - L = c1 * x ^ (1 / 4 : ℝ) := by
    dsimp [L, U]
    ring
  have hpowlen : (((2 * M) ^ Z : ℕ) : ℝ) < U - L - 1 := by
    dsimp [Z, q]
    rw [hLU]
    exact hlen0.trans_le (by gcongr)
  have hbaReal : U - L - 1 ≤ ((b - a : ℤ) : ℝ) := by
    have hfl : (a : ℝ) ≤ L := by exact Int.floor_le L
    have hce : U - 1 ≤ (b : ℝ) := by
      dsimp [b]
      push_cast
      have := Int.le_ceil U
      linarith
    push_cast
    linarith
  have hab : a ≤ b := by
    have : (0 : ℝ) < ((b - a : ℤ) : ℝ) := lt_of_lt_of_le
      (lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ (((2 * M) ^ Z : ℕ) : ℝ)) hpowlen) hbaReal
    exact sub_nonneg.mp (by exact_mod_cast this.le)
  have hlength : (((2 * M) ^ Z : ℕ) : ℤ) < b - a := by
    exact_mod_cast hpowlen.trans_le hbaReal
  have hprime (p : SievePrime Z) : p.val.Prime := (Finset.mem_filter.mp p.property).2
  let R : (p : SievePrime Z) → Finset (ZMod p.val) := fun p =>
    @linearBadResidues p.val ⟨hprime p⟩ (Fin t) inferInstance A B
  have hRsmall : ∀ p, p.val ≤ M → R p = ∅ := by
    intro p hpM
    exact @linear_bad_residues_empty p.val ⟨hprime p⟩ (Fin t) inferInstance A B
      hprim (hsmall p.val (hprime p) hpM)
  have hRcard : ∀ p, 2 * (R p).card ≤ M := by
    intro p
    exact (Nat.mul_le_mul_left 2
      (@linear_bad_residue_spec p.val ⟨hprime p⟩ (Fin t) inferInstance A B hprim).1).trans
      (by simpa using ht)
  obtain ⟨k, hkIoc, hkavoid⟩ := exists_interval_avoiding M Z hM a b hab R hRsmall hRcard hlength
  have hkLower : L < (k : ℝ) := by
    have hLfloor : L < (a : ℝ) + 1 := by exact Int.lt_floor_add_one L
    have hak : a < k := (Finset.mem_Ioc.mp hkIoc).1
    exact hLfloor.trans_le (by exact_mod_cast hak)
  have hkUpper : (k : ℝ) < U := by
    have hkb : k ≤ b := (Finset.mem_Ioc.mp hkIoc).2
    have hbU : (b : ℝ) < U := by
      dsimp [b]
      push_cast
      have := Int.ceil_lt_add_one U
      linarith
    have hkb' : (k : ℝ) ≤ (b : ℝ) := by exact_mod_cast hkb
    exact hkb'.trans_lt hbU
  refine ⟨k, ?_, ?_, ?_⟩
  · exact hkLower
  · exact hkUpper
  intro p hp hdiv
  by_contra hpq
  have hpqle : (p : ℝ) ≤ q := le_of_not_gt hpq
  have hqnonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (Real.log_nonneg hx1) (by
      have : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
      positivity)
  have hpZ : p ≤ Z := by
    dsimp [Z]
    exact Nat.le_floor hpqle
  have hp1 : 1 ≤ p := hp.one_le
  let sp : SievePrime Z := ⟨p, by simp [sievePrimes, hp1, hpZ, hp]⟩
  have hmem : (k : ZMod p) ∈ R sp := by
    exact ((@linear_bad_residue_spec p ⟨hp⟩ (Fin t) inferInstance A B hprim).2 k).mpr hdiv
  exact hkavoid sp hmem

/-! ### Upstream module `MerLeanExperiment/ShiftSelection.lean` -/

/-- Uniform selection of shifted points whose pair factors have no small prime
divisors.  The threshold is fixed before the finite family and its translations. -/
theorem exists_rough_shifted_points (M : ℕ) (hM : 3 ≤ M) (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ X0 : ℝ, 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x → ∀ K : ℕ, 2 * K ≤ M →
      ∀ r : Fin K → ℤ, Function.Injective r →
      (∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M) →
      ∀ c : Fin K → ℝ, (∀ i, c0 ≤ c i) → ∃ ell : Fin K → ℤ,
        (∀ i, c i * Real.sqrt x < (shiftedPoint M r ell i : ℝ) ∧
          (shiftedPoint M r ell i : ℝ) <
            c i * (Real.sqrt x + x ^ (1 / 4 : ℝ))) ∧
        ∀ i j, i < j → ∀ p : ℕ, p.Prime →
          (p : ℤ) ∣ shiftFactor M r ell i j →
            Real.log x / (8 * Real.log M) < (p : ℝ) := by
  classical
  let FR : ℝ := M.factorial
  have hFR : 0 < FR := by
    dsimp [FR]
    exact_mod_cast Nat.factorial_pos M
  have hcScaled : 0 < c0 / FR := div_pos hc0 hFR
  obtain ⟨X0, hX0, havoid⟩ :=
    chen_uniform_linear_avoidance M hM (c0 / FR) hcScaled
  refine ⟨X0, hX0, ?_⟩
  intro x hx K
  induction K with
  | zero =>
      intro hKM r hrInj hrDist c hc
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ K ih =>
      intro hKM r hrInj hrDist c hc
      let rOld : Fin K → ℤ := fun i ↦ r i.castSucc
      let cOld : Fin K → ℝ := fun i ↦ c i.castSucc
      have hKold : 2 * K ≤ M := by omega
      have hrOldInj : Function.Injective rOld := by
        intro i j hij
        apply Fin.castSucc_injective
        apply hrInj
        simpa [rOld] using hij
      have hrOldDist : ∀ i j, i ≠ j → 2 * (rOld j - rOld i).natAbs ≤ M := by
        intro i j hij
        apply hrDist i.castSucc j.castSucc
        exact fun h ↦ hij (Fin.castSucc_injective K h)
      have hcOld : ∀ i, c0 ≤ cOld i := fun i ↦ hc i.castSucc
      obtain ⟨ellOld, hpointOld, hroughOld⟩ :=
        ih hKold rOld hrOldInj hrOldDist cOld hcOld
      let last : Fin (K + 1) := Fin.last K
      let d : Fin K → ℤ := fun i ↦ r last - r i.castSucc
      let A : Fin K → ℤ := fun i ↦ (M.factorial : ℤ) / d i
      let B : Fin K → ℤ := fun i ↦ 1 - A i * ellOld i
      have hd (i : Fin K) : d i ≠ 0 := by
        dsimp [d, last]
        exact sub_ne_zero.mpr (Ne.symm (hrInj.ne (Fin.castSucc_ne_last i)))
      have hdSize (i : Fin K) : 2 * (d i).natAbs ≤ M := by
        exact hrDist i.castSucc last (Fin.castSucc_ne_last i)
      have hspec (i : Fin K) :
          d i * A i = (M.factorial : ℤ) ∧ IsCoprime (A i) (B i) ∧
            ∀ p : ℕ, p.Prime → p ≤ M → ∀ n : ℤ, ¬ (p : ℤ) ∣ A i * n + B i := by
        simpa [A, B] using factorial_linear_spec M (d i) (hd i) (hdSize i) (ellOld i)
      have hprim : ∀ i, IsCoprime (A i) (B i) := fun i ↦ (hspec i).2.1
      have hsmall : ∀ p : ℕ, p.Prime → p ≤ M → ∀ n : ℤ,
          ¬ (p : ℤ) ∣ ∏ i, (A i * n + B i) := by
        intro p hp hpM n
        exact (Nat.prime_iff_prime_int.mp hp).not_dvd_finsetProd
          (fun i _ ↦ (hspec i).2.2 p hp hpM n)
      have hcLast : c0 / FR ≤ c last / FR := by
        exact (div_le_div_iff_of_pos_right hFR).2 (hc last)
      obtain ⟨k, hkLower, hkUpper, hkRough⟩ :=
        havoid x hx (c last / FR) (-((r last : ℤ) : ℝ) / FR) hcLast K hKold
          A B hprim hsmall
      let ell : Fin (K + 1) → ℤ := Fin.lastCases k ellOld
      refine ⟨ell, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun q ↦ ?_) i
        · have hkL := hkLower
          have hkU := hkUpper
          rw [← Real.sqrt_eq_rpow] at hkL hkU
          have hlowRewrite :
              c last / FR * Real.sqrt x + -((r last : ℤ) : ℝ) / FR =
                (c last * Real.sqrt x - (r last : ℝ)) / FR := by
            field_simp [hFR.ne']; ring
          have huppRewrite :
              c last / FR * (Real.sqrt x + x ^ (1 / 4 : ℝ)) +
                  -((r last : ℤ) : ℝ) / FR =
                (c last * (Real.sqrt x + x ^ (1 / 4 : ℝ)) - (r last : ℝ)) / FR := by
            field_simp [hFR.ne']; ring
          rw [hlowRewrite] at hkL
          rw [huppRewrite] at hkU
          have hkL' := (div_lt_iff₀ hFR).mp hkL
          have hkU' := (lt_div_iff₀ hFR).mp hkU
          constructor
          · change c last * Real.sqrt x <
              (((M.factorial : ℤ) * ell last + r last : ℤ) : ℝ)
            simp [ell, last]
            nlinarith
          · change (((M.factorial : ℤ) * ell last + r last : ℤ) : ℝ) <
              c last * (Real.sqrt x + x ^ (1 / 4 : ℝ))
            simp [ell, last]
            nlinarith
        · simpa [ell, shiftedPoint, rOld, cOld] using hpointOld q
      · intro i j hij p hp hpDiv
        cases j using Fin.lastCases with
        | last =>
            cases i using Fin.lastCases with
            | last => exact (lt_irrefl _ hij).elim
            | cast iOld =>
                have hfactor :
                    shiftFactor M r ell iOld.castSucc (Fin.last K) =
                      A iOld * k + B iOld := by
                  simp [shiftFactor, ell, A, B, d, last]
                  ring
                have hpForm : (p : ℤ) ∣ A iOld * k + B iOld := by
                  rwa [hfactor] at hpDiv
                have hformProd : A iOld * k + B iOld ∣ ∏ u, (A u * k + B u) :=
                  Finset.dvd_prod_of_mem (fun u ↦ A u * k + B u)
                    (Finset.mem_univ iOld)
                exact hkRough p hp (hpForm.trans hformProd)
        | cast jOld =>
            cases i using Fin.lastCases with
            | last => exact (not_lt_of_ge (Fin.le_last jOld.castSucc) hij).elim
            | cast iOld =>
                have hqq : iOld < jOld := by simpa using hij
                apply hroughOld iOld jOld hqq p hp
                simpa [shiftFactor, ell, rOld] using hpDiv

/-! ### Upstream module `MerLeanExperiment/ShiftProduct.lean` -/

theorem shift_product_pos {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ)
    (hr : Function.Injective r)
    (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M) :
    0 < shiftProductNat M r ell := by
  apply Int.natAbs_pos.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro ij hij
  have hlt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
  exact shift_factor_ne_zero M r ell hr hsize ij.1 ij.2 (ne_of_lt hlt)

theorem shift_product_rough {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ) (z : ℝ)
    (hrough : ∀ i j, i < j → ∀ p : ℕ, p.Prime →
      (p : ℤ) ∣ shiftFactor M r ell i j → z < (p : ℝ)) :
    ∀ p ∈ (shiftProductNat M r ell).primeFactors, z < (p : ℝ) := by
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  let : Fact p.Prime := ⟨hprime⟩
  have hn : p ∣ (shiftProduct M r ell).natAbs := Nat.dvd_of_mem_primeFactors hp
  have hdiv : (p : ℤ) ∣ shiftProduct M r ell := Int.natCast_dvd.mpr hn
  have hz : ∏ ij ∈ shiftPairs K, (shiftFactor M r ell ij.1 ij.2 : ZMod p) = 0 := by
    simpa [shiftProduct] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (shiftProduct M r ell) p).mpr hdiv
  obtain ⟨ij, hij, hf⟩ := Finset.prod_eq_zero_iff.mp hz
  have hlt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
  exact hrough ij.1 ij.2 hlt p hprime
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hf)

theorem shift_product_bound {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ)
    (hr : Function.Injective r)
    (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M)
    (Y : ℝ) (_hY : 0 ≤ Y)
    (hpoints : ∀ i, 0 ≤ (shiftedPoint M r ell i : ℝ) ∧
      (shiftedPoint M r ell i : ℝ) ≤ Y) :
    (shiftProductNat M r ell : ℝ) ≤ Y ^ (shiftPairs K).card := by
  have hfactor (ij : Fin K × Fin K) (hij : ij ∈ shiftPairs K) :
      ((shiftFactor M r ell ij.1 ij.2).natAbs : ℝ) ≤ Y := by
    have hlt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
    have hd : r ij.2 - r ij.1 ≠ 0 :=
      sub_ne_zero.mpr (fun h => (ne_of_lt hlt) (hr h).symm)
    have hdp : 0 < (r ij.2 - r ij.1).natAbs := Int.natAbs_pos.mpr hd
    have heq := shift_factor_mul_difference M r ell ij.1 ij.2 hd
      (hsize ij.1 ij.2 (ne_of_lt hlt))
    have hnat : (shiftFactor M r ell ij.1 ij.2).natAbs ≤
        (shiftedPoint M r ell ij.2 - shiftedPoint M r ell ij.1).natAbs := by
      calc
        _ ≤ (r ij.2 - r ij.1).natAbs * (shiftFactor M r ell ij.1 ij.2).natAbs := by
          exact Nat.le_mul_of_pos_left _ hdp
        _ = _ := by rw [← Int.natAbs_mul, heq]
    have hdiff : ((shiftedPoint M r ell ij.2 - shiftedPoint M r ell ij.1).natAbs : ℝ) ≤ Y := by
      rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, abs_le]
      have hi := hpoints ij.1
      have hj := hpoints ij.2
      constructor <;> linarith
    exact (Nat.cast_le.mpr hnat).trans hdiff
  calc
    (shiftProductNat M r ell : ℝ) =
        ∏ ij ∈ shiftPairs K, ((shiftFactor M r ell ij.1 ij.2).natAbs : ℝ) := by
      simp [shiftProductNat, shiftProduct, Finset.abs_prod]
    _ ≤ ∏ _ij ∈ shiftPairs K, Y :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) hfactor
    _ = Y ^ (shiftPairs K).card := by simp

/-! ### Upstream module `MerLeanExperiment/CoprimeExceptions.lean` -/

/-- Integers in a signed interval that are not coprime to `D` are covered by
the residue-zero classes of the prime factors of `D`. -/
theorem coprime_exception_bound (D : ℕ) (hD : D ≠ 0) (a b : ℤ) (hab : a ≤ b) :
    (({x ∈ Finset.Ioc a b | ¬ Nat.Coprime (x : ℤ).natAbs D}).card : ℚ) ≤
      ∑ p ∈ D.primeFactors, (((b - a : ℤ) : ℚ) / p + 1) := by
  let bad : Finset ℤ := {x ∈ Finset.Ioc a b | ¬ Nat.Coprime x.natAbs D}
  let multiples (p : ℕ) : Finset ℤ :=
    {x ∈ Finset.Ioc a b | Int.ModEq (p : ℤ) x 0}
  have hcover : bad ⊆ D.primeFactors.biUnion multiples := by
    intro x hx
    have hx' : x ∈ Finset.Ioc a b ∧ ¬ Nat.Coprime x.natAbs D := by
      simpa [bad] using hx
    obtain ⟨p, hp, hpx, hpD⟩ := Nat.Prime.not_coprime_iff_dvd.mp hx'.2
    have hpMem : p ∈ D.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpD, hD⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hpMem, ?_⟩
    have hpInt : (p : ℤ) ∣ x := Int.natCast_dvd.mpr hpx
    simpa [multiples, hx'.1, Int.modEq_zero_iff_dvd] using hpInt
  have hcardNat : bad.card ≤ ∑ p ∈ D.primeFactors, (multiples p).card := by
    exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hcardQ : (bad.card : ℚ) ≤
      ∑ p ∈ D.primeFactors, ((multiples p).card : ℚ) := by
    exact_mod_cast hcardNat
  have hclass (p : ℕ) (hpMem : p ∈ D.primeFactors) :
      ((multiples p).card : ℚ) ≤ ((b - a : ℤ) : ℚ) / p + 1 := by
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    have hres := residue_count_discrepancy a b 0 p hp.pos hab
    change |((multiples p).card : ℚ) - ((b - a : ℤ) : ℚ) / p| ≤ 1 at hres
    rw [abs_le] at hres
    linarith
  change (bad.card : ℚ) ≤ ∑ p ∈ D.primeFactors, (((b - a : ℤ) : ℚ) / p + 1)
  exact hcardQ.trans (Finset.sum_le_sum fun p hpMem ↦ hclass p hpMem)

/-! ### Upstream module `MerLeanExperiment/PrimeFactorLog.lean` -/

theorem prime_factor_log_bound (D : ℕ) (hD : 0 < D) (z : ℝ) (hz : 1 < z)
    (hrough : ∀ p ∈ D.primeFactors, z ≤ (p : ℝ)) :
    (D.primeFactors.card : ℝ) * Real.log z ≤ Real.log D := by
  have hprod : (∏ p ∈ D.primeFactors, (p : ℝ)) ≤ (D : ℝ) := by
    have hn := Nat.le_of_dvd hD (Nat.prod_primeFactors_dvd D)
    have hc : ((∏ p ∈ D.primeFactors, p : ℕ) : ℝ) ≤ (D : ℝ) := Nat.cast_le.mpr hn
    simpa only [Nat.cast_prod] using hc
  have hpos (p : ℕ) (hp : p ∈ D.primeFactors) : (0 : ℝ) < p := by
    exact_mod_cast Nat.pos_of_mem_primeFactors hp
  have hprodpos : (0 : ℝ) < ∏ p ∈ D.primeFactors, (p : ℝ) :=
    Finset.prod_pos hpos
  calc
    (D.primeFactors.card : ℝ) * Real.log z =
        ∑ _p ∈ D.primeFactors, Real.log z := by simp
    _ ≤ ∑ p ∈ D.primeFactors, Real.log p := by
      exact Finset.sum_le_sum fun p hp => Real.log_le_log (by linarith) (hrough p hp)
    _ = Real.log (∏ p ∈ D.primeFactors, (p : ℝ)) :=
      (Real.log_prod fun p hp => ne_of_gt (hpos p hp)).symm
    _ ≤ Real.log D := Real.log_le_log hprodpos hprod

/-! ### Upstream module `MerLeanExperiment/CoprimeExceptionLog.lean` -/

/-- A logarithmic bound for the actual integers in a signed interval that are
not coprime to a positive integer all of whose prime factors are at least `z`. -/
theorem coprime_exception_log_bound (D : ℕ) (hD : 0 < D) (a b : ℤ) (hab : a ≤ b)
    (z : ℝ) (hz : 1 < z) (hrough : ∀ p ∈ D.primeFactors, z ≤ (p : ℝ)) :
    (({x ∈ Finset.Ioc a b | ¬ Nat.Coprime (x : ℤ).natAbs D}).card : ℝ) * Real.log z ≤
      Real.log D * (((b - a : ℤ) : ℝ) / z + 1) := by
  let bad : Finset ℤ := {x ∈ Finset.Ioc a b | ¬ Nat.Coprime x.natAbs D}
  let B : ℝ := ((b - a : ℤ) : ℝ) / z + 1
  have hcountQ := coprime_exception_bound D hD.ne' a b hab
  have hcountR : (bad.card : ℝ) ≤
      ∑ p ∈ D.primeFactors, (((b - a : ℤ) : ℝ) / (p : ℝ) + 1) := by
    exact_mod_cast hcountQ
  have hlength : (0 : ℝ) ≤ ((b - a : ℤ) : ℝ) := by
    exact_mod_cast sub_nonneg.mpr hab
  have hzpos : (0 : ℝ) < z := by linarith
  have hterm (p : ℕ) (hp : p ∈ D.primeFactors) :
      (((b - a : ℤ) : ℝ) / (p : ℝ) + 1) ≤ B := by
    have hpz : z ≤ (p : ℝ) := hrough p hp
    dsimp [B]
    gcongr
  have hbad : (bad.card : ℝ) ≤ (D.primeFactors.card : ℝ) * B := by
    calc
      (bad.card : ℝ) ≤
          ∑ p ∈ D.primeFactors, (((b - a : ℤ) : ℝ) / (p : ℝ) + 1) := hcountR
      _ ≤ ∑ _p ∈ D.primeFactors, B :=
        Finset.sum_le_sum fun p hp ↦ hterm p hp
      _ = (D.primeFactors.card : ℝ) * B := by simp
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hlog : 0 ≤ Real.log z := Real.log_nonneg hz.le
  have hfactor := prime_factor_log_bound D hD z hz hrough
  change (bad.card : ℝ) * Real.log z ≤ Real.log D * B
  calc
    (bad.card : ℝ) * Real.log z ≤
        ((D.primeFactors.card : ℝ) * B) * Real.log z :=
      mul_le_mul_of_nonneg_right hbad hlog
    _ = ((D.primeFactors.card : ℝ) * Real.log z) * B := by ring
    _ ≤ Real.log D * B := mul_le_mul_of_nonneg_right hfactor hB

/-! ### Upstream module `MerLeanExperiment/UniformExceptions.lean` -/

/-- Uniformly, rough positive integers of polynomial size have vanishingly few
non-coprime integers in any translated interval of square-root length. -/
theorem eventually_rough_coprime_exceptions (K C : ℝ) (hK : 0 < K) (hC : 0 < C)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ x : ℝ in Filter.atTop, ∀ D : ℕ, 0 < D →
    (D : ℝ) ≤ x ^ C → (∀ p ∈ D.primeFactors, Real.log x / K ≤ (p : ℝ)) →
    ∀ a b : ℤ, a ≤ b → ((b - a : ℤ) : ℝ) ≤ C * Real.sqrt x →
    (({n ∈ Finset.Ioc a b | ¬ Nat.Coprime (n : ℤ).natAbs D}).card : ℝ) ≤
      ε * Real.sqrt x := by
  let A : ℝ := C * (C * K + 2)
  let X : ℝ := Real.exp (K * Real.exp (A / ε + 1))
  filter_upwards [Filter.eventually_ge_atTop X] with x hx
  intro D hD hDsize hrough a b hab hlength
  let z : ℝ := Real.log x / K
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hinner : 0 < K * Real.exp (A / ε + 1) := by positivity
  have hXone : 1 < X := by
    dsimp [X]
    exact Real.one_lt_exp_iff.mpr hinner
  have hxone : 1 < x := hXone.trans_le hx
  have hxpos : 0 < x := zero_lt_one.trans hxone
  have hlogxpos : 0 < Real.log x := Real.log_pos hxone
  have hlogxLower : K * Real.exp (A / ε + 1) ≤ Real.log x := by
    calc
      K * Real.exp (A / ε + 1) = Real.log X := by simp [X]
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hx
  have hzLower : Real.exp (A / ε + 1) ≤ z := by
    dsimp [z]
    apply (le_div_iff₀ hK).2
    simpa [mul_comm] using hlogxLower
  have hExpOne : 1 < Real.exp (A / ε + 1) := by
    rw [Real.one_lt_exp_iff]
    positivity
  have hzOne : 1 < z := hExpOne.trans_le hzLower
  have hlogzLower : A / ε + 1 ≤ Real.log z := by
    calc
      A / ε + 1 = Real.log (Real.exp (A / ε + 1)) := by simp
      _ ≤ Real.log z := Real.log_le_log (Real.exp_pos _) hzLower
  have hAthresh : A ≤ ε * Real.log z := by
    have hmul := mul_le_mul_of_nonneg_left hlogzLower hε.le
    have hcancel : ε * (A / ε) = A := by field_simp
    nlinarith
  have hfinite := coprime_exception_log_bound D hD a b hab z hzOne hrough
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hlogD : Real.log D ≤ C * Real.log x := by
    calc
      Real.log D ≤ Real.log (x ^ C) := Real.log_le_log hDreal hDsize
      _ = C * Real.log x := Real.log_rpow hxpos C
  have hzpos : 0 < z := zero_lt_one.trans hzOne
  have hlenNonneg : (0 : ℝ) ≤ ((b - a : ℤ) : ℝ) := by
    exact_mod_cast sub_nonneg.mpr hab
  have hsqrtNonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hBnonneg : 0 ≤ ((b - a : ℤ) : ℝ) / z + 1 := by positivity
  have hBbound : ((b - a : ℤ) : ℝ) / z + 1 ≤
      C * Real.sqrt x / z + 1 := by
    gcongr
  have hClogNonneg : 0 ≤ C * Real.log x :=
    mul_nonneg hC.le hlogxpos.le
  have hweighted :
      (({n ∈ Finset.Ioc a b | ¬ Nat.Coprime (n : ℤ).natAbs D}).card : ℝ) *
          Real.log z ≤ (C * Real.log x) * (C * Real.sqrt x / z + 1) := by
    calc
      (({n ∈ Finset.Ioc a b | ¬ Nat.Coprime (n : ℤ).natAbs D}).card : ℝ) *
          Real.log z ≤ Real.log D * (((b - a : ℤ) : ℝ) / z + 1) := hfinite
      _ ≤ (C * Real.log x) * (((b - a : ℤ) : ℝ) / z + 1) :=
        mul_le_mul_of_nonneg_right hlogD hBnonneg
      _ ≤ (C * Real.log x) * (C * Real.sqrt x / z + 1) :=
        mul_le_mul_of_nonneg_left hBbound hClogNonneg
  have halgebra : (C * Real.log x) * (C * Real.sqrt x / z + 1) =
      C * (C * K * Real.sqrt x + Real.log x) := by
    dsimp [z]
    field_simp [hK.ne', hlogxpos.ne']
  have hlogsqrt := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hxpos)
  rw [Real.log_sqrt hxpos.le] at hlogsqrt
  have hlogSqrt : Real.log x ≤ 2 * Real.sqrt x := by linarith
  have hconstant : C * (C * K * Real.sqrt x + Real.log x) ≤
      A * Real.sqrt x := by
    have hi : C * K * Real.sqrt x + Real.log x ≤
        (C * K + 2) * Real.sqrt x := by
      nlinarith
    have := mul_le_mul_of_nonneg_left hi hC.le
    calc
      C * (C * K * Real.sqrt x + Real.log x) ≤
          C * ((C * K + 2) * Real.sqrt x) := this
      _ = A * Real.sqrt x := by simp [A]; ring
  have hweightedA :
      (({n ∈ Finset.Ioc a b | ¬ Nat.Coprime (n : ℤ).natAbs D}).card : ℝ) *
          Real.log z ≤ A * Real.sqrt x := by
    calc
      _ ≤ (C * Real.log x) * (C * Real.sqrt x / z + 1) := hweighted
      _ = C * (C * K * Real.sqrt x + Real.log x) := halgebra
      _ ≤ A * Real.sqrt x := hconstant
  have hproduct :
      (({n ∈ Finset.Ioc a b | ¬ Nat.Coprime (n : ℤ).natAbs D}).card : ℝ) *
          Real.log z ≤ (ε * Real.sqrt x) * Real.log z := by
    calc
      _ ≤ A * Real.sqrt x := hweightedA
      _ ≤ (ε * Real.log z) * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hAthresh hsqrtNonneg
      _ = (ε * Real.sqrt x) * Real.log z := by ring
  exact le_of_mul_le_mul_right hproduct (Real.log_pos hzOne)

/-! ### Upstream module `MerLeanExperiment/ShortError.lean` -/

theorem eventually_short_interval_error (K : ℕ) (B : ℝ) (_hB : 0 ≤ B)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ x : ℝ in Filter.atTop,
    (K : ℝ) * B * x ^ (1 / 4 : ℝ) + K ≤ ε * Real.sqrt x := by
  have ht := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  have he : ∀ᶠ x : ℝ in Filter.atTop,
      (K : ℝ) * (B + 1) / ε ≤ x ^ (1 / 4 : ℝ) :=
    ht.eventually (Filter.eventually_ge_atTop _)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), he] with x hx he
  have hx0 : 0 ≤ x := by linarith
  have hQ : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hcoef : (K : ℝ) * (B + 1) ≤ ε * x ^ (1 / 4 : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ hε).mp he
  have hsq : (x ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0, Real.sqrt_eq_rpow]
    norm_num
  calc
    _ ≤ ((K : ℝ) * (B + 1)) * x ^ (1 / 4 : ℝ) := by
      have hkQ := mul_le_mul_of_nonneg_left hQ (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
      nlinarith
    _ ≤ (ε * x ^ (1 / 4 : ℝ)) * x ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = ε * Real.sqrt x := by rw [mul_assoc, ← sq, hsq]

/-! ### Upstream module `MerLeanExperiment/UniformCellUnion.lean` -/

theorem eventually_packing_cell_union {K : ℕ} (M : ℕ) (hM : 3 ≤ M) (hK : 2 * K ≤ M) (r : Fin K → ℤ) (hr : Function.Injective r) (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M) (c0 B delta : ℝ) (hc0 : 0 < c0) (hB : 0 < B) (hdelta : 0 ≤ delta) (ε : ℝ) (hε : 0 < ε) : ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N ≥ N0, ∀ c : Fin K → ℝ, (∀ i, c0 ≤ c i) → (∀ i, c i + delta ≤ B) → (∀ i j, i < j → ((r j - r i).natAbs : ℝ) ≤ (shiftParityWeight (r i) (r j) : ℝ) * c i * c j) → ∀ A : Finset ℕ, LcmBounded N A → ((packingCellUnion A r c delta (Real.sqrt (N : ℝ))).card : ℝ) ≤ (delta / 2 + ε) * Real.sqrt (N : ℝ) := by
  classical
  let C : ℝ := B + (shiftPairs K).card + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hBC : B ≤ C := by
    dsimp [C]
    have : (0 : ℝ) ≤ (shiftPairs K).card := Nat.cast_nonneg _
    linarith
  have hcut : 0 < 8 * Real.log (M : ℝ) := by
    have hMr : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
    exact mul_pos (by norm_num) (Real.log_pos hMr)
  obtain ⟨Xsel, _, hsel⟩ := exists_rough_shifted_points M hM c0 hc0
  obtain ⟨Xexc, hexc⟩ := Filter.eventually_atTop.mp
    (eventually_rough_coprime_exceptions (8 * Real.log M) C hcut hC
      (ε / 2) (by positivity))
  obtain ⟨Xerr, herr⟩ := Filter.eventually_atTop.mp
    (eventually_short_interval_error K B hB.le (ε / 2) (by positivity))
  let N0 : ℕ := max 1 (max ⌈Xsel⌉₊ (max ⌈Xexc⌉₊ (max ⌈Xerr⌉₊ ⌈(2 * B) ^ 2⌉₊)))
  refine ⟨N0, le_max_left _ _, ?_⟩
  intro N hN c hc0c hcB hsep A hA
  have hN1 : 1 ≤ N := by dsimp [N0] at hN; omega
  have hNpos : 0 < N := by omega
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hx0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hNsel : Xsel ≤ (N : ℝ) := (Nat.le_ceil Xsel).trans
    (Nat.cast_le.mpr (by dsimp [N0] at hN; omega))
  have hNexc : Xexc ≤ (N : ℝ) := (Nat.le_ceil Xexc).trans
    (Nat.cast_le.mpr (by dsimp [N0] at hN; omega))
  have hNerr : Xerr ≤ (N : ℝ) := (Nat.le_ceil Xerr).trans
    (Nat.cast_le.mpr (by dsimp [N0] at hN; omega))
  have hNB : (2 * B) ^ 2 ≤ (N : ℝ) := (Nat.le_ceil _).trans
    (Nat.cast_le.mpr (by dsimp [N0] at hN; omega))
  let R := Real.sqrt (N : ℝ)
  let Q := (N : ℝ) ^ (1 / 4 : ℝ)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hRpos : 0 < R := Real.sqrt_pos.mpr (by exact_mod_cast hNpos)
  have hR2 : R ^ 2 = (N : ℝ) := Real.sq_sqrt hx0
  have hBR : 2 * B ≤ R := by nlinarith
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg hx0 _
  have hQR : Q ≤ R := by
    dsimp only [R]
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hcpos (i : Fin K) : 0 < c i := hc0.trans_le (hc0c i)
  have hcB' (i : Fin K) : c i ≤ B := by have := hcB i; linarith
  obtain ⟨ell, hpoints, hrough⟩ := hsel (N : ℝ) hNsel K hK r hr hsize c hc0c
  let D := shiftProductNat M r ell
  have hDpos : 0 < D := shift_product_pos M r ell hr hsize
  have hpointsN (i : Fin K) : 0 ≤ (shiftedPoint M r ell i : ℝ) ∧
      (shiftedPoint M r ell i : ℝ) ≤ N := by
    refine ⟨(mul_pos (hcpos i) hRpos).le.trans (hpoints i).1.le, ?_⟩
    calc
      _ ≤ c i * (R + Q) := (hpoints i).2.le
      _ ≤ B * (R + Q) := mul_le_mul_of_nonneg_right (hcB' i) (by positivity)
      _ ≤ 2 * B * R := by nlinarith [mul_le_mul_of_nonneg_left hQR hB.le]
      _ ≤ (N : ℝ) := by nlinarith [mul_le_mul_of_nonneg_right hBR hR0]
  have hDsize : (D : ℝ) ≤ (N : ℝ) ^ C := by
    calc
      _ ≤ (N : ℝ) ^ (shiftPairs K).card :=
        shift_product_bound M r ell hr hsize (N : ℝ) hx0 hpointsN
      _ ≤ (N : ℝ) ^ C := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le hx1
        dsimp [C]
        linarith
  have hDrough : ∀ p ∈ D.primeFactors,
      Real.log (N : ℝ) / (8 * Real.log M) ≤ (p : ℝ) := by
    intro p hp
    exact (shift_product_rough M r ell _ hrough p hp).le
  have hfloor : (0 : ℤ) ≤ ⌊B * R⌋ := Int.floor_nonneg.mpr (by positivity)
  have hlength : ((⌊B * R⌋ - 0 : ℤ) : ℝ) ≤ C * R := by
    push_cast
    simpa only [sub_zero] using
      (Int.floor_le _).trans (mul_le_mul_of_nonneg_right hBC hR0)
  have hbadInt := hexc (N : ℝ) hNexc D hDpos hDsize hDrough 0 ⌊B * R⌋ hfloor hlength
  have hbad : ((packingBadPoints A D B R).card : ℝ) ≤ ε / 2 * R := by
    have hb := packing_bad_points_le_exceptions N A hA D B R
    have hbR : ((packingBadPoints A D B R).card : ℝ) ≤
        (((realIntIoc 0 (B * R)).filter fun n => ¬ Nat.Coprime n.natAbs D).card : ℝ) :=
      Nat.cast_le.mpr hb
    exact hbR.trans (by simpa [realIntIoc] using hbadInt)
  have hshort : (∑ i : Fin K, (c i * Q + 1)) ≤ (K : ℝ) * B * Q + K := by
    calc
      _ ≤ ∑ _i : Fin K, (B * Q + 1) := by
        apply Finset.sum_le_sum
        intro i _
        linarith [mul_le_mul_of_nonneg_right (hcB' i) hQ0]
      _ = _ := by simp; ring
  have hcount := packing_cell_union_bound M N (by omega) hNpos r ell hr hsize
    c (fun i => c i * Q) hcpos (fun i => mul_nonneg (hcpos i).le hQ0)
    delta B hdelta hcB
    (fun i => ⟨(hpoints i).1, by
      change (shiftedPoint M r ell i : ℝ) ≤
        c i * Real.sqrt (N : ℝ) + c i * (N : ℝ) ^ (1 / 4 : ℝ)
      nlinarith [(hpoints i).2]⟩)
    hsep A hA
  have herror := herr (N : ℝ) hNerr
  change ((packingCellUnion A r c delta R).card : ℝ) ≤ (delta / 2 + ε) * R
  change ((packingCellUnion A r c delta R).card : ℝ) ≤
    delta * R / 2 + (∑ i, (c i * Q + 1)) + (packingBadPoints A D B R).card at hcount
  change (K : ℝ) * B * Q + K ≤ ε / 2 * R at herror
  linarith

/-! ### Upstream module `MerLeanExperiment/ParityPacking.lean` -/

theorem eventually_parity_packing {K l : ℕ} (a b : Fin l → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j)))
    (o : Fin K → Fin l) (r : Fin K → ℤ) (hr : Function.Injective r)
    (hsep : ∀ i j, i < j → ((r j - r i).natAbs : ℝ) ≤
      (shiftParityWeight (r i) (r j) : ℝ) * a (o i) * a (o j))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ A : Finset ℕ, LcmBounded N A →
      (∑ i, parityDensity A (a (o i)) (b (o i)) (Real.sqrt (N : ℝ)) (r i)) ≤
        1 / 2 + ε := by
  classical
  obtain ⟨c0, _, hc0, _, hca, _⟩ := exists_finite_positive_bounds a ha
  obtain ⟨_, B, _, hB, _, hBb⟩ := exists_finite_positive_bounds b (fun j => (ha j).trans (hab j))
  obtain ⟨M, hM, hMK, hsize⟩ := exists_packing_residue_budget r
  let S : ℝ := ∑ i : Fin K, 1 / (b (o i) - a (o i))
  have hS : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro i _
    exact (one_div_pos.mpr (sub_pos.mpr (hab (o i)))).le
  obtain ⟨delta, m, hd, hm, hKm, hlo, hhi, hdS⟩ := exists_packing_mesh K a b hab S ε hS hε
  obtain ⟨NU, hNU, hU⟩ := eventually_packing_cell_union M hM hMK r hr
    (fun i j _ => hsize i j) c0 B delta hc0 hB hd.le (ε * delta / 4) (by positivity)
  let N0 : ℕ := max NU (max 1 ⌈(4 * S / ε) ^ 2⌉₊)
  refine ⟨N0, ?_⟩
  intro N hN A hA
  have hNN : NU ≤ N := by dsimp [N0] at hN; omega
  have hN1 : 1 ≤ N := by dsimp [N0] at hN; omega
  let R : ℝ := Real.sqrt (N : ℝ)
  have hR : 0 < R := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))
  have hR2 : R ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hNsq : (4 * S / ε) ^ 2 ≤ (N : ℝ) := (Nat.le_ceil _).trans
    (Nat.cast_le.mpr (by dsimp [N0] at hN; omega))
  have hSR : S ≤ ε / 4 * R := by
    have hbase : 0 ≤ 4 * S / ε := by positivity
    have hlarge : 4 * S / ε ≤ R := by nlinarith
    have hh := (div_le_iff₀ hε).mp hlarge
    nlinarith
  obtain ⟨c, hcb, hfinite⟩ := exists_finite_parity_density_mesh A a b o r m
    delta R hd hR hm hKm hlo hhi hdisj
  have hc (i : Fin K) : 0 < c i := (ha (o i)).trans_le (hcb i).1
  have hsepc (i j : Fin K) (hij : i < j) :
      ((r j - r i).natAbs : ℝ) ≤
        (shiftParityWeight (r i) (r j) : ℝ) * c i * c j := by
    have hw : (0 : ℝ) ≤ shiftParityWeight (r i) (r j) := Nat.cast_nonneg _
    exact (hsep i j hij).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (hcb i).1 hw) (hcb j).1 (ha (o j)).le
      (mul_nonneg hw (hc i).le))
  have hbound := hU N hNN c (fun i => (hca (o i)).trans (hcb i).1)
    (fun i => (hcb i).2.trans (hBb (o i))) hsepc A hA
  have herr : delta * (delta * R + 1) * S ≤ delta * R * (ε / 2) := by
    have hh1 := mul_le_mul_of_nonneg_left hdS (mul_pos hd hR).le
    have hh2 := mul_le_mul_of_nonneg_left hSR hd.le
    nlinarith only [hh1, hh2]
  apply (mul_le_mul_iff_right₀ (mul_pos hd hR)).mp
  change delta * R * (∑ i, parityDensity A (a (o i)) (b (o i)) R (r i)) ≤ _
  change delta * R * (∑ i, parityDensity A (a (o i)) (b (o i)) R (r i)) ≤
    (packingCellUnion A r c delta R).card + delta * (delta * R + 1) * S at hfinite
  change ((packingCellUnion A r c delta R).card : ℝ) ≤ (delta / 2 + ε * delta / 4) * R at hbound
  nlinarith [mul_pos (mul_pos hd hR) hε]

/-! ### Upstream module `MerLeanExperiment/IntervalPacking.lean` -/

theorem eventually_interval_packing {K l : ℕ} (a b : Fin l → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j)))
    (o : Fin K → Fin l) (r : Fin K → ℤ) (hr : Function.Injective r)
    (hsep : ∀ i j, i < j → ((r j - r i).natAbs : ℝ) ≤ a (o i) * a (o j))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ A : Finset ℕ, LcmBounded N A →
      (∑ i, intervalDensity A (a (o i)) (b (o i)) (Real.sqrt (N : ℝ))) ≤ 1 + ε := by
  classical
  have hw (x y : ℤ) : (1 : ℝ) ≤ shiftParityWeight x y := by
    unfold shiftParityWeight
    split_ifs <;> norm_num
  have hscale (i j : Fin K) (x y : ℤ) :
      a (o i) * a (o j) ≤ (shiftParityWeight x y : ℝ) * a (o i) * a (o j) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hw x y) (ha (o i)).le) (ha (o j)).le
  have hsep1 (i j : Fin K) (hij : i < j) :
      ((r j - r i).natAbs : ℝ) ≤
        (shiftParityWeight (r i) (r j) : ℝ) * a (o i) * a (o j) :=
    (hsep i j hij).trans (hscale i j (r i) (r j))
  let r' : Fin K → ℤ := fun i => r i + 1
  have hr' : Function.Injective r' := by
    intro i j h
    apply hr
    dsimp [r'] at h
    omega
  have hsep2 (i j : Fin K) (hij : i < j) :
      ((r' j - r' i).natAbs : ℝ) ≤
        (shiftParityWeight (r' i) (r' j) : ℝ) * a (o i) * a (o j) := by
    have heq : r' j - r' i = r j - r i := by dsimp [r']; ring
    rw [heq]
    exact (hsep i j hij).trans (hscale i j (r' i) (r' j))
  obtain ⟨N1, hN1⟩ := eventually_parity_packing a b ha hab hdisj o r hr hsep1
    (ε / 2) (by positivity)
  obtain ⟨N2, hN2⟩ := eventually_parity_packing a b ha hab hdisj o r' hr' hsep2
    (ε / 2) (by positivity)
  refine ⟨max N1 N2, ?_⟩
  intro N hN A hA
  have h1 := hN1 N ((le_max_left _ _).trans hN) A hA
  have h2 := hN2 N ((le_max_right _ _).trans hN) A hA
  have heq : (∑ i : Fin K, intervalDensity A (a (o i)) (b (o i)) (Real.sqrt (N : ℝ))) =
      (∑ i : Fin K, parityDensity A (a (o i)) (b (o i)) (Real.sqrt (N : ℝ)) (r i)) +
      (∑ i : Fin K, parityDensity A (a (o i)) (b (o i)) (Real.sqrt (N : ℝ)) (r' i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (density_parity_partition A (a (o i)) (b (o i)) (Real.sqrt (N : ℝ)) (r i)).symm
  rw [heq]
  linarith

/-! ### Upstream module `MerLeanExperiment/FiniteIntervalPacking.lean` -/

theorem eventually_finite_interval_packing {I E : Type*} [Fintype I] [Fintype E]
    (a b : I → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j)))
    (o : E → I) (r : E → ℤ) (hr : Function.Injective r)
    (hsep : ∀ i j, i ≠ j → ((r j - r i).natAbs : ℝ) ≤ a (o i) * a (o j))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ A : Finset ℕ, LcmBounded N A →
      (∑ i : E, intervalDensity A (a (o i)) (b (o i)) (Real.sqrt (N : ℝ))) ≤
        1 + epsilon := by
  classical
  let ie : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let ee : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
  let owner : Fin (Fintype.card E) → Fin (Fintype.card I) := fun i => ie.symm (o (ee i))
  have hdis (i j : Fin (Fintype.card I)) (hij : i ≠ j) :
      Disjoint (Set.Ioc (a (ie i)) (b (ie i))) (Set.Ioc (a (ie j)) (b (ie j))) :=
    hdisj _ _ (fun h => hij (ie.injective h))
  have hs (i j : Fin (Fintype.card E)) (hij : i < j) :
      ((r (ee j) - r (ee i)).natAbs : ℝ) ≤ a (ie (owner i)) * a (ie (owner j)) := by
    have hh := hsep (ee i) (ee j) (fun h => (ne_of_lt hij) (ee.injective h))
    simpa [owner] using hh
  obtain ⟨N0, hN0⟩ := eventually_interval_packing (fun i => a (ie i)) (fun i => b (ie i))
    (fun i => ha (ie i)) (fun i => hab (ie i)) hdis owner (fun i => r (ee i))
    (hr.comp ee.injective) hs epsilon hepsilon
  refine ⟨N0, ?_⟩
  intro N hN A hA
  have hh := hN0 N hN A hA
  have heq : (∑ i : Fin (Fintype.card E),
      intervalDensity A (a (ie (owner i))) (b (ie (owner i))) (Real.sqrt (N : ℝ))) =
      ∑ i : E, intervalDensity A (a (o i)) (b (o i)) (Real.sqrt (N : ℝ)) := by
    exact Fintype.sum_equiv ee _ _ (fun i => by simp [owner])
  rw [heq] at hh
  exact hh

/-! ### Upstream module `MerLeanExperiment/GridForwardPacking.lean` -/

theorem grid_intervals_disjoint (q : ℝ) (hq : 1 < q) (i j : ℤ) (hij : i ≠ j) :
    Disjoint (Set.Ioc (q ^ i) (q ^ (i + 1))) (Set.Ioc (q ^ j) (q ^ (j + 1))) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hij with hij | hji
  · have h := zpow_le_zpow_right₀ hq.le (show i + 1 ≤ j by omega)
    exact (h.trans_lt hy.1).not_ge hx.2
  · have h := zpow_le_zpow_right₀ hq.le (show j + 1 ≤ i by omega)
    exact (h.trans_lt hx.1).not_ge hy.2

theorem eventually_grid_forward_packing {I : Type*} [Fintype I]
    (q : ℝ) (hq : 1 < q) (L : ℕ) (j : ℤ) (row : I → ℤ)
    (hrow : Function.Injective row) (phi : I → I) (hphi : ∀ i, row i ≤ row (phi i))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ A : Finset ℕ, LcmBounded N A →
      (∑ i : I, (gridCount q L (row i) j : ℝ) *
        intervalDensity A (q ^ (row (phi i))) (q ^ (row (phi i) + 1))
          (Real.sqrt (N : ℝ))) ≤ 1 + epsilon := by
  classical
  let E : Type _ := Σ i : I, {z : ℤ // z ∈ gridFiber q L (row i) j}
  let label : E → ℤ := fun e => e.2.val
  let owner : E → I := fun e => phi e.1
  have hqp : 0 < q := by linarith
  have ha (i : I) : 0 < q ^ row i := zpow_pos hqp _
  have hab (i : I) : q ^ row i < q ^ (row i + 1) := by
    rw [zpow_add₀ hqp.ne', zpow_one]
    nlinarith [ha i]
  have hdis (i k : I) (hik : i ≠ k) :
      Disjoint (Set.Ioc (q ^ row i) (q ^ (row i + 1)))
        (Set.Ioc (q ^ row k) (q ^ (row k + 1))) :=
    grid_intervals_disjoint q hq (row i) (row k) (fun h => hik (hrow h))
  have hr : Function.Injective label := grid_fiber_label_injective q hq L j row hrow
  have hsep (e f : E) (_hef : e ≠ f) :
      ((label f - label e).natAbs : ℝ) ≤ q ^ row (owner e) * q ^ row (owner f) := by
    calc
      _ ≤ q ^ row f.1 * q ^ row e.1 := grid_fiber_separation q hq L
        (row f.1) (row e.1) j f.2.val e.2.val f.2.property e.2.property
      _ = q ^ row e.1 * q ^ row f.1 := mul_comm _ _
      _ ≤ _ := mul_le_mul (zpow_le_zpow_right₀ hq.le (hphi e.1))
        (zpow_le_zpow_right₀ hq.le (hphi f.1)) (ha f.1).le (ha (owner e)).le
  obtain ⟨N0, hN0⟩ := eventually_finite_interval_packing
    (fun i => q ^ row i) (fun i => q ^ (row i + 1)) ha hab hdis owner label hr hsep
    epsilon hepsilon
  refine ⟨N0, ?_⟩
  intro N hN A hA
  have hh := hN0 N hN A hA
  have heq := grid_fiber_sum q L j row
    (fun i => intervalDensity A (q ^ row (phi i)) (q ^ (row (phi i) + 1)) (Real.sqrt (N : ℝ)))
  change (∑ e : E, intervalDensity A (q ^ row (phi e.1))
    (q ^ (row (phi e.1) + 1)) (Real.sqrt (N : ℝ))) ≤ _ at hh
  rw [heq] at hh
  exact hh

theorem eventually_uniform_grid_forward_packing {I J : Type*} [Fintype I] [Fintype J]
    (q : ℝ) (hq : 1 < q) (L : ℕ) (col : J → ℤ) (row : I → ℤ)
    (hrow : Function.Injective row) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ A : Finset ℕ, LcmBounded N A →
      ∀ j : J, ∀ phi : I → I, (∀ i, row i ≤ row (phi i)) →
        (∑ i : I, (gridCount q L (row i) (col j) : ℝ) *
          intervalDensity A (q ^ (row (phi i))) (q ^ (row (phi i) + 1))
            (Real.sqrt (N : ℝ))) ≤ 1 + epsilon := by
  classical
  have hex (j : J) (phi : I → I) : ∃ N0 : ℕ, ∀ N ≥ N0, ∀ A : Finset ℕ,
      LcmBounded N A → (∀ i, row i ≤ row (phi i)) →
        (∑ i : I, (gridCount q L (row i) (col j) : ℝ) *
          intervalDensity A (q ^ (row (phi i))) (q ^ (row (phi i) + 1))
            (Real.sqrt (N : ℝ))) ≤ 1 + epsilon := by
    by_cases hphi : ∀ i, row i ≤ row (phi i)
    · obtain ⟨N0, hh⟩ := eventually_grid_forward_packing q hq L (col j) row hrow phi hphi
        epsilon hepsilon
      exact ⟨N0, fun N hN A hA _ => hh N hN A hA⟩
    · exact ⟨0, fun _ _ _ _ h => False.elim (hphi h)⟩
  choose bound hbound using hex
  refine ⟨∑ j : J, ∑ phi : I → I, bound j phi, ?_⟩
  intro N hN A hA j phi hphi
  have h1 : bound j phi ≤ ∑ psi : I → I, bound j psi :=
    Finset.single_le_sum (fun psi _ => Nat.zero_le (bound j psi)) (Finset.mem_univ phi)
  have h2 : (∑ psi : I → I, bound j psi) ≤ ∑ k : J, ∑ psi : I → I, bound k psi :=
    Finset.single_le_sum (fun k _ => Nat.zero_le (∑ psi : I → I, bound k psi))
      (Finset.mem_univ j)
  exact hbound j phi N (h1.trans (h2.trans hN)) A hA hphi

/-! ### Upstream module `MerLeanExperiment/IntTelescoping.lean` -/

/-- Integer telescoping, including the adjacent empty interval. -/
theorem sum_Icc_backward_sub (f : ℤ → ℝ) (a b : ℤ) (hab : a ≤ b + 1) :
    ∑ i ∈ Finset.Icc a b, (f i - f (i - 1)) = f b - f (a - 1) := by
  have haux (n : ℕ) :
      ∑ i ∈ Finset.Icc a (a + n - 1), (f i - f (i - 1)) =
        f (a + n - 1) - f (a - 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have htop : a + ((n + 1 : ℕ) : ℤ) - 1 = a + n := by omega
      have hset : Finset.Icc a (a + n) =
          insert (a + n) (Finset.Icc a (a + n - 1)) := by
        ext z
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [htop, hset, Finset.sum_insert (by simp), ih]
      ring
  let n := (b + 1 - a).toNat
  have he : a + (n : ℤ) - 1 = b := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
    ring
  simpa only [he] using haux n

theorem sum_card_sdiff_Icc (F : ℤ → Finset ℤ) (a b : ℤ) (hab : a ≤ b + 1)
    (hmono : ∀ i ∈ Finset.Icc a b, F (i - 1) ⊆ F i) :
    ∑ i ∈ Finset.Icc a b, ((F i \ F (i - 1)).card : ℝ) =
      (F b).card - (F (a - 1)).card := by
  calc
    _ = ∑ i ∈ Finset.Icc a b, ((F i).card - (F (i - 1)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h : ((F i \ F (i - 1)).card : ℝ) + (F (i - 1)).card = (F i).card := by
        exact_mod_cast Finset.card_sdiff_add_card_eq_card (hmono i hi)
      linarith
    _ = _ := sum_Icc_backward_sub (fun i => ((F i).card : ℝ)) a b hab

theorem sum_Icc_zpow_mul_sub_one (q : ℝ) (hq : q ≠ 0) (a b : ℤ)
    (hab : a ≤ b + 1) :
    ∑ i ∈ Finset.Icc a b, q ^ i * (q - 1) = q ^ (b + 1) - q ^ a := by
  have h := sum_Icc_backward_sub (fun i => q ^ (i + 1)) a b hab
  simp only [sub_add_cancel] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  rw [zpow_add_one₀ hq]
  ring

/-! ### Upstream module `MerLeanExperiment/GridPrefixIdentity.lean` -/

theorem sum_gridCount_column (q : ℝ) (hq : 1 < q) (L : ℕ) (T t j : ℤ)
    (ht : -T ≤ t) (hj : -T ≤ j) (hjL : j < (L : ℤ)) :
    ∑ i ∈ Finset.Icc (-T) t, (gridCount q L i j : ℝ) = (gridA q t j).card := by
  have hzero : gridA q (-T - 1) j = ∅ := by
    simp [gridA, show ¬ j ≤ -T - 1 by omega]
  calc
    _ = ∑ i ∈ Finset.Icc (-T) t,
        ((gridA q i j \ gridA q (i - 1) j).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [gridCount, ne_of_lt hjL, hjL]
    _ = (gridA q t j).card - (gridA q (-T - 1) j).card :=
      sum_card_sdiff_Icc (fun i => gridA q i j) (-T) t (by omega)
        (fun i _ => grid_column_mono q hq (i - 1) i j (by omega))
    _ = _ := by rw [hzero]; simp

theorem grid_capacity_prefix_eq (q : ℝ) (hq : 1 < q) (L : ℕ) (hL : 1 ≤ L)
    (T t : ℤ) (hT : 0 ≤ T) (ht : -T ≤ t) :
    gridCapacityPrefix q L T t =
      (∑ j ∈ Finset.Icc (-T) (-1), (gridA q t j).card * q ^ j * (q - 1)) +
      (1 / 2 : ℝ) * (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
        (gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1))) +
      (if 0 ≤ t then 1 - q ^ (-1 : ℤ) else 0) := by
  classical
  let f : ℤ → ℝ := fun j => gridDelta q L j *
    ∑ i ∈ Finset.Icc (-T) t, (gridCount q L i j : ℝ)
  have hsum : gridCapacityPrefix q L T t = ∑ j ∈ Finset.Icc (-T) (L : ℤ), f j := by
    unfold gridCapacityPrefix
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact (Finset.mul_sum _ _ _).symm
  have hsplit : Finset.Icc (-T) (L : ℤ) =
      (Finset.Icc (-T) (-1) ∪ Finset.Icc 0 ((L : ℤ) - 1)) ∪ {(L : ℤ)} := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdis1 : Disjoint (Finset.Icc (-T) (-1)) (Finset.Icc 0 ((L : ℤ) - 1)) := by
    rw [Finset.disjoint_left]
    intro j hj hk
    simp only [Finset.mem_Icc] at hj hk
    omega
  have hdis2 : Disjoint (Finset.Icc (-T) (-1) ∪ Finset.Icc 0 ((L : ℤ) - 1))
      {(L : ℤ)} := by
    rw [Finset.disjoint_left]
    intro j hj hk
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton] at hj hk
    omega
  rw [hsum, hsplit, Finset.sum_union hdis2, Finset.sum_union hdis1, Finset.sum_singleton]
  have hneg : (∑ j ∈ Finset.Icc (-T) (-1), f j) =
      ∑ j ∈ Finset.Icc (-T) (-1), (gridA q t j).card * q ^ j * (q - 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hjlo, hjhi⟩ := Finset.mem_Icc.mp hj
    dsimp [f]
    rw [sum_gridCount_column q hq L T t j ht hjlo (by omega)]
    simp [gridDelta, show j < 0 by omega]
    ring
  have hpos : (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1), f j) =
      (1 / 2 : ℝ) * ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
        (gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hjlo, hjhi⟩ := Finset.mem_Icc.mp hj
    dsimp [f]
    rw [sum_gridCount_column q hq L T t j ht (by omega) (by omega)]
    simp [gridDelta, not_lt.mpr hjlo, show j < (L : ℤ) by omega]
    ring
  have hlast : f (L : ℤ) = if 0 ≤ t then 1 - q ^ (-1 : ℤ) else 0 := by
    dsimp [f]
    have hd : gridDelta q L (L : ℤ) = 1 - q ^ (-1 : ℤ) := by
      simp [gridDelta]
    rw [hd]
    have hnegT : -T ≤ 0 := by omega
    by_cases ht0 : 0 ≤ t
    · simp [gridCount, Finset.sum_ite_eq', hnegT, ht0]
    · simp [gridCount, Finset.sum_ite_eq', hnegT, ht0]
  rw [hneg, hpos, hlast]

/-! ### Upstream module `MerLeanExperiment/GridPrefixSmall.lean` -/

private lemma grid_weight_nonneg (q : ℝ) (hq : 1 < q) (j : ℤ) :
    0 ≤ q ^ j * (q - 1) := mul_nonneg (zpow_nonneg (by linarith) _) (by linarith)

theorem grid_prefix_case_neg (q : ℝ) (hq : 1 < q) (L : ℕ) (hL : 1 ≤ L)
    (T t : ℤ) (hT : 0 ≤ T) (htlo : -T ≤ t) (htneg : t < 0) :
    gridBetaPrefix q L T t ≤ gridCapacityPrefix q L T t := by
  rw [grid_capacity_prefix_eq q hq L hL T t hT htlo]
  have hbeta : gridBetaPrefix q L T t =
      ∑ i ∈ Finset.Icc (-T) t, q ^ i * (q - 1) := by
    unfold gridBetaPrefix
    apply Finset.sum_congr rfl
    intro i hi
    have hit : i ≤ t := (Finset.mem_Icc.mp hi).2
    simp [gridBeta, show i < (L : ℤ) by omega]
  rw [hbeta]
  have hsubset : Finset.Icc (-T) t ⊆ Finset.Icc (-T) (-1) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  have hcard :
      (∑ j ∈ Finset.Icc (-T) t, q ^ j * (q - 1)) ≤
        ∑ j ∈ Finset.Icc (-T) t,
          (gridA q t j).card * q ^ j * (q - 1) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjt : j ≤ t := (Finset.mem_Icc.mp hj).2
    have hmem := zero_mem_grid_column q hq t j hjt
    have hc : (1 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast Finset.one_le_card.mpr ⟨0, hmem⟩
    have hw := grid_weight_nonneg q hq j
    calc
      q ^ j * (q - 1) ≤ ((gridA q t j).card : ℝ) * (q ^ j * (q - 1)) :=
        by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hw
      _ = _ := by ring_nf
  have hcardFull :
      (∑ j ∈ Finset.Icc (-T) t,
          (gridA q t j).card * q ^ j * (q - 1)) ≤
        ∑ j ∈ Finset.Icc (-T) (-1),
          (gridA q t j).card * q ^ j * (q - 1) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun j _ _ => by positivity)
  have hposzero :
      (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
        (gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj0 : 0 ≤ j := (Finset.mem_Icc.mp hj).1
    simp [gridA, show ¬ j ≤ t by omega]
  rw [hposzero]
  simp only [mul_zero, add_zero]
  simp [show ¬ 0 ≤ t by omega]
  exact hcard.trans hcardFull

theorem grid_prefix_case_small (q : ℝ) (hq : 1 < q) (L : ℕ) (hL : 1 ≤ L)
    (T t : ℤ) (hT : 0 ≤ T) (hcover : (L : ℤ) - 1 ≤ T)
    (ht0 : 0 ≤ t) (htL : t < (L : ℤ)) :
    gridBetaPrefix q L T t ≤ gridCapacityPrefix q L T t := by
  have htT : t ≤ T := by omega
  rw [grid_capacity_prefix_eq q hq L hL T t hT (by omega)]
  have hbeta : gridBetaPrefix q L T t = q ^ (t + 1) - q ^ (-T) := by
    unfold gridBetaPrefix
    calc
      _ = ∑ i ∈ Finset.Icc (-T) t, q ^ i * (q - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiL : i < (L : ℤ) := (Finset.mem_Icc.mp hi).2.trans_lt htL
        simp [gridBeta, hiL]
      _ = _ := sum_Icc_zpow_mul_sub_one q (by linarith) (-T) t (by omega)
  rw [hbeta]
  simp [ht0]
  let wn : ℤ → ℝ := fun j => q ^ j * (q - 1)
  have hneg :
      (∑ j ∈ Finset.Icc (-T) (-1), wn j) +
          (∑ j ∈ Finset.Icc (-t) (-1), wn j) ≤
        ∑ j ∈ Finset.Icc (-T) (-1),
          (gridA q t j).card * q ^ j * (q - 1) := by
    have hsub : Finset.Icc (-t) (-1) ⊆ Finset.Icc (-T) (-1) := by
      intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    have heq :
        (∑ j ∈ Finset.Icc (-T) (-1), wn j) + (∑ j ∈ Finset.Icc (-t) (-1), wn j) =
          ∑ j ∈ Finset.Icc (-T) (-1), (wn j + if -t ≤ j then wn j else 0) := by
      rw [Finset.sum_add_distrib]
      congr 1
      have hfilter : (Finset.Icc (-T) (-1)).filter (fun j => -t ≤ j) = Finset.Icc (-t) (-1) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [← hfilter, Finset.sum_filter]
    rw [heq]
    apply Finset.sum_le_sum
    intro j hj
    have hjr := Finset.mem_Icc.mp hj
    have hjt : j ≤ t := by omega
    have hw := grid_weight_nonneg q hq j
    by_cases hextra : -t ≤ j
    · have hs : 0 ≤ t + j := by omega
      have htwoN : 2 ≤ (gridA q t j).card :=
        Finset.card_le_card (zero_one_subset_grid_column q hq t j hjt hs)
      have htwo : (2 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast htwoN
      simp [hextra, wn]
      nlinarith
    · have honeN : 1 ≤ (gridA q t j).card :=
        Finset.one_le_card.mpr ⟨0, zero_mem_grid_column q hq t j hjt⟩
      have hone : (1 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast honeN
      simp [hextra, wn]
      nlinarith
  have hpos :
      (∑ j ∈ Finset.Icc 0 t, (q - 1) * (q ^ j - q ^ (-j - 1))) ≤
        (1 / 2 : ℝ) * ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1)) := by
    rw [Finset.mul_sum]
    have hsub : Finset.Icc 0 t ⊆ Finset.Icc 0 ((L : ℤ) - 1) := by
      intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    have hrestrict :
        (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (1 / 2 : ℝ) * ((gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1)))) =
        ∑ j ∈ Finset.Icc 0 t,
          (1 / 2 : ℝ) * ((gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1))) := by
      symm
      apply Finset.sum_subset hsub
      intro j hjbig hjnot
      have hj := Finset.mem_Icc.mp hjbig
      have hjt : ¬ j ≤ t := by
        intro h
        exact hjnot (by simp [hj.1, h])
      simp [gridA, hjt]
    rw [hrestrict]
    apply Finset.sum_le_sum
    intro j hj
    have hjr := Finset.mem_Icc.mp hj
    have htwoN : 2 ≤ (gridA q t j).card := by
      have hs := zero_one_subset_grid_column q hq t j hjr.2 (by omega)
      have := Finset.card_le_card hs
      simpa using this
    have htwo : (2 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast htwoN
    have hzpow : q ^ (-j - 1) ≤ q ^ j :=
      zpow_le_zpow_right₀ (le_of_lt hq) (by omega)
    have hw : 0 ≤ (q - 1) * (q ^ j - q ^ (-j - 1)) := mul_nonneg (by linarith) (sub_nonneg.mpr hzpow)
    nlinarith
  have hs1 := sum_Icc_zpow_mul_sub_one q (by linarith) (-T) (-1) (by omega)
  have hs2 := sum_Icc_zpow_mul_sub_one q (by linarith) (-t) (-1) (by omega)
  have hs3 :
      (∑ j ∈ Finset.Icc 0 t, (q - 1) * (q ^ j - q ^ (-j - 1))) =
        q ^ (t + 1) - 2 + q ^ (-t - 1) := by
    have hf := sum_Icc_zpow_mul_sub_one q (by linarith) 0 t (by omega)
    have hb := sum_Icc_backward_sub (fun j => q ^ (-j - 1)) 0 t (by omega)
    calc
      _ = (∑ j ∈ Finset.Icc 0 t, q ^ j * (q - 1)) -
          ∑ j ∈ Finset.Icc 0 t, (q ^ (-j) - q ^ (-j - 1)) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            rw [zpow_sub_one₀ (by linarith : q ≠ 0)]
            field_simp
      _ = _ := by
        rw [hf]
        have hb' : (∑ j ∈ Finset.Icc 0 t, (q ^ (-j) - q ^ (-j - 1))) =
            1 - q ^ (-t - 1) := by
          rw [← neg_inj]
          rw [← Finset.sum_neg_distrib]
          convert hb using 1
          · apply Finset.sum_congr rfl
            intro j _
            ring_nf
          · norm_num
        rw [hb']
        norm_num
        ring_nf
  have hlower := add_le_add (add_le_add hneg hpos) (le_refl (1 - q ^ (-1 : ℤ)))
  rw [hs1, hs2, hs3] at hlower
  norm_num only [Int.reduceNeg, add_neg_cancel, zpow_zero] at hlower
  have hrem : 0 ≤ (1 - q ^ (-1 : ℤ)) * (1 - q ^ (-t : ℤ)) := by
    have hqinv : q ^ (-1 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ (le_of_lt hq) (by omega)
    have hqt : q ^ (-t : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ (le_of_lt hq) (by omega)
    exact mul_nonneg (sub_nonneg.mpr hqinv) (sub_nonneg.mpr hqt)
  have hid :
      (1 - q ^ (-T)) + (1 - q ^ (-t)) +
          (q ^ (t + 1) - 2 + q ^ (-t - 1)) + (1 - q ^ (-1 : ℤ)) =
        (q ^ (t + 1) - q ^ (-T)) +
          (1 - q ^ (-1 : ℤ)) * (1 - q ^ (-t)) := by
    have hz : q ^ (-t - 1) = q ^ (-t) * q ^ (-1 : ℤ) := by
      rw [← zpow_add₀ (by linarith : q ≠ 0)]
      congr 1
    rw [hz]
    ring_nf
  rw [hid] at hlower
  have hlower' :
      (q ^ (t + 1) + (1 - q ^ (-1 : ℤ)) * (1 - q ^ (-t))) - q ^ (-T) ≤
        (∑ j ∈ Finset.Icc (-T) (-1), (gridA q t j).card * q ^ j * (q - 1)) +
        (1 / 2 : ℝ) * (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1))) +
        (1 - q ^ (-1 : ℤ)) := by
    linarith
  have hshift := (sub_le_iff_le_add).mp hlower'
  exact (le_add_of_nonneg_right hrem).trans (by simpa [zpow_neg] using hshift)

/-! ### Upstream module `MerLeanExperiment/GridSums.lean` -/

theorem sum_Icc_zpow_difference (q : ℝ) (hq : q ≠ 0) (a b : ℤ)
    (hab : a ≤ b + 1) :
    ∑ j ∈ Finset.Icc a b, (q - 1) * (q ^ j - q ^ (-j - 1)) =
      q ^ (b + 1) - q ^ a - q ^ (-a) + q ^ (-b - 1) := by
  have hneg : (∑ j ∈ Finset.Icc a b, (q - 1) * q ^ (-j - 1)) =
      q ^ (-a) - q ^ (-b - 1) := by
    calc
      _ = ∑ j ∈ Finset.Icc a b, (-q ^ (-j - 1) - (-q ^ (-(j - 1) - 1))) := by
        apply Finset.sum_congr rfl
        intro j _
        have hi : -(j - 1) - 1 = -j := by omega
        rw [hi, zpow_sub_one₀ hq]
        field_simp
        ring
      _ = -q ^ (-b - 1) - (-q ^ (-(a - 1) - 1)) :=
        sum_Icc_backward_sub (fun j => -q ^ (-j - 1)) a b hab
      _ = _ := by
        have hi : -(a - 1) - 1 = -a := by omega
        rw [hi]
        ring
  calc
    _ = (∑ j ∈ Finset.Icc a b, q ^ j * (q - 1)) -
        ∑ j ∈ Finset.Icc a b, (q - 1) * q ^ (-j - 1) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [sum_Icc_zpow_mul_sub_one q hq a b hab, hneg]; ring

theorem grid_beta_prefix_eq (q : ℝ) (hq : q ≠ 0) (L : ℕ) (T t : ℤ)
    (hT : 0 ≤ T) (hLt : (L : ℤ) ≤ t) :
    gridBetaPrefix q L T t = q ^ (t + 1) - q ^ (-T) +
      gridEta * (q ^ (t + 1) - q ^ (L : ℤ)) := by
  have hid (i : ℤ) : gridBeta q L i = q ^ i * (q - 1) +
      if (L : ℤ) ≤ i then gridEta * (q ^ i * (q - 1)) else 0 := by
    by_cases hi : i < (L : ℤ)
    · simp [gridBeta, hi, not_le.mpr hi]
    · simp only [gridBeta, ite_eq_right hi, ite_eq_left (not_lt.mp hi)]
      ring
  have hfilter : (Finset.Icc (-T) t).filter (fun i => (L : ℤ) ≤ i) =
      Finset.Icc (L : ℤ) t := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hextra :
      (∑ i ∈ Finset.Icc (-T) t,
        if (L : ℤ) ≤ i then gridEta * (q ^ i * (q - 1)) else 0) =
      gridEta * ∑ i ∈ Finset.Icc (L : ℤ) t, q ^ i * (q - 1) := by
    rw [← Finset.sum_filter, hfilter, Finset.mul_sum]
  unfold gridBetaPrefix
  simp_rw [hid]
  rw [Finset.sum_add_distrib, hextra,
    sum_Icc_zpow_mul_sub_one q hq (-T) t (by omega),
    sum_Icc_zpow_mul_sub_one q hq (L : ℤ) t (by omega)]

/-! ### Upstream module `MerLeanExperiment/GridScalarDefinitions.lean` -/

/-- The exact capacity-minus-beta residual in Chen's third grid case. -/
noncomputable def gridResidual3 (q u : ℝ) : ℝ :=
  9 * Real.sqrt 2 / 4 + Real.sqrt 2 * gridEta + 1 - 1 / q +
    u * (-q / 2 - 1 / 4 - gridEta * q) - 3 / u

/-- The coefficient and common endpoint remainder in Chen's fourth grid case. -/
noncomputable def gridSlope4 (q : ℝ) : ℝ :=
  2 - 2 * q + (1 - q / 2) / (2 * (1 + q)) - gridEta * q

noncomputable def gridResidual4 (q : ℝ) : ℝ :=
  2 * gridSlope4 q + 2 - 3 * Real.sqrt 2 / 2 + gridEta * Real.sqrt 2 - q / 8

/-! ### Upstream module `MerLeanExperiment/GridCapacity3.lean` -/

private lemma grid_neg_one_mem_case3 (q : ℝ) (hq : 1 < q) (L : ℕ)
    (hq2L : q ^ (2 * (L : ℤ)) = 2) (t j : ℤ)
    (hjlo : -t ≤ j) (hjhi : j ≤ t - 2 * (L : ℤ)) :
    (-1 : ℤ) ∈ gridA q t j := by
  have hqpos : 0 < q := by linarith
  have hjt : j ≤ t := by omega
  simp only [gridA, hjt, ↓reduceIte, mem_gridPoints]
  right
  have hprod : 1 ≤ q ^ j * q ^ t := by
    rw [← zpow_add₀ hqpos.ne']
    exact one_le_zpow₀ hq.le (by omega)
  have hratio : 2 ≤ q ^ t / q ^ j := by
    rw [← zpow_sub₀ hqpos.ne']
    rw [← hq2L]
    exact zpow_le_zpow_right₀ hq.le (by omega)
  have hmin : 1 ≤ min (q ^ j * q ^ t) (q ^ t / q ^ j - 1) :=
    le_min hprod (by linarith)
  constructor
  · norm_num
    exact ⟨hprod, by linarith⟩
  · norm_num

private lemma grid_two_mem_case3 (q : ℝ) (hq : 1 < q) (L : ℕ)
    (hq2L : q ^ (2 * (L : ℤ)) = 2) (t j : ℤ)
    (hjt : j ≤ t) (hsum : 2 * (L : ℤ) ≤ j + t) :
    (2 : ℤ) ∈ gridA q t j := by
  have hqpos : 0 < q := by linarith
  simp only [gridA, hjt, ↓reduceIte, mem_gridPoints]
  left
  constructor
  · norm_num
  · have hp : (2 : ℝ) ≤ q ^ (j + t) := by
      rw [← hq2L]
      exact zpow_le_zpow_right₀ hq.le hsum
    rw [zpow_add₀ hqpos.ne'] at hp
    exact_mod_cast hp

private lemma grid_neg_weight_nonneg (q : ℝ) (hq : 1 < q) (j : ℤ) :
    0 ≤ q ^ j * (q - 1) := by positivity

private lemma grid_pos_weight_nonneg (q : ℝ) (hq : 1 < q) (j : ℤ) (hj : 0 ≤ j) :
    0 ≤ (q - 1) * (q ^ j - q ^ (-j - 1)) := by
  have hp := zpow_le_zpow_right₀ hq.le (show -j - 1 ≤ j by omega)
  exact mul_nonneg (by linarith) (sub_nonneg.mpr hp)

/-- The five actual grid-column blocks in Case 3 give precisely the source
residual lower bound; all cardinality estimates come from concrete members. -/
theorem grid_case3_capacity (q : ℝ) (hq : 1 < q) (L : ℕ) (hL : 1 ≤ L)
    (hqL : q ^ (L : ℤ) = Real.sqrt 2) (hq2L : q ^ (2 * (L : ℤ)) = 2)
    (T t : ℤ) (hT : 0 ≤ T) (htT : t ≤ T) (hLt : (L : ℤ) ≤ t)
    (ht2L : t < 2 * (L : ℤ)) :
    gridBetaPrefix q L T t + gridResidual3 q (q ^ t) ≤
      gridCapacityPrefix q L T t := by
  have hqpos : 0 < q := by linarith
  have hqne : q ≠ 0 := hqpos.ne'
  have ht0 : 0 ≤ t := by omega
  have htlo : -T ≤ t := by omega
  rw [grid_capacity_prefix_eq q hq L hL T t hT htlo]
  rw [ite_eq_left ht0]
  let wn : ℤ → ℝ := fun j ↦ q ^ j * (q - 1)
  let wp : ℤ → ℝ := fun j ↦ (q - 1) * (q ^ j - q ^ (-j - 1))
  let h : ℤ := 2 * (L : ℤ) - t
  have hh1 : 1 ≤ h := by omega
  have hhL : h ≤ (L : ℤ) := by omega
  have hneg :
      ( (∑ j ∈ Finset.Icc (-T) (-1), wn j) +
          ∑ j ∈ Finset.Icc (-t) (-1), wn j) +
          ∑ j ∈ Finset.Icc (-t) (t - 2 * (L : ℤ)), wn j ≤
        ∑ j ∈ Finset.Icc (-T) (-1),
          (gridA q t j).card * q ^ j * (q - 1) := by
    have hsumA :
        (∑ j ∈ Finset.Icc (-T) (-1), if -t ≤ j then wn j else 0) =
          ∑ j ∈ Finset.Icc (-t) (-1), wn j := by
      have hf : (Finset.Icc (-T) (-1)).filter (fun j ↦ -t ≤ j) =
          Finset.Icc (-t) (-1) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [← hf, Finset.sum_filter]
    have hsumB :
        (∑ j ∈ Finset.Icc (-T) (-1),
          if -t ≤ j ∧ j ≤ t - 2 * (L : ℤ) then wn j else 0) =
          ∑ j ∈ Finset.Icc (-t) (t - 2 * (L : ℤ)), wn j := by
      have hf : (Finset.Icc (-T) (-1)).filter
          (fun j ↦ -t ≤ j ∧ j ≤ t - 2 * (L : ℤ)) =
          Finset.Icc (-t) (t - 2 * (L : ℤ)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [← hf, Finset.sum_filter]
    have heq :
        ((∑ j ∈ Finset.Icc (-T) (-1), wn j) +
            ∑ j ∈ Finset.Icc (-t) (-1), wn j) +
            ∑ j ∈ Finset.Icc (-t) (t - 2 * (L : ℤ)), wn j =
          ∑ j ∈ Finset.Icc (-T) (-1),
            ((wn j + if -t ≤ j then wn j else 0) +
              if -t ≤ j ∧ j ≤ t - 2 * (L : ℤ) then wn j else 0) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumA, hsumB]
    rw [heq]
    apply Finset.sum_le_sum
    intro j hjmem
    have hjr := Finset.mem_Icc.mp hjmem
    have hjt : j ≤ t := by omega
    have hw := grid_neg_weight_nonneg q hq j
    by_cases ha : -t ≤ j
    · by_cases hb : j ≤ t - 2 * (L : ℤ)
      · have hsub : ({-1, 0, 1} : Finset ℤ) ⊆ gridA q t j := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl
          · exact grid_neg_one_mem_case3 q hq L hq2L t j ha hb
          · exact zero_mem_grid_column q hq t j hjt
          · exact (zero_one_subset_grid_column q hq t j hjt (by omega)) (by simp)
        have hcN : 3 ≤ (gridA q t j).card := by
          have hc := Finset.card_le_card hsub
          norm_num at hc ⊢
          exact hc
        have hc : (3 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast hcN
        simp [ha, hb, wn]
        nlinarith
      · have hcN : 2 ≤ (gridA q t j).card :=
          Finset.card_le_card (zero_one_subset_grid_column q hq t j hjt (by omega))
        have hc : (2 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast hcN
        simp [ha, hb, wn]
        nlinarith
    · have hcN : 1 ≤ (gridA q t j).card :=
        Finset.one_le_card.mpr ⟨0, zero_mem_grid_column q hq t j hjt⟩
      have hc : (1 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast hcN
      simp [ha, wn]
      nlinarith
  have hpos :
      (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1), wp j) +
          (1 / 2 : ℝ) * (∑ j ∈ Finset.Icc h ((L : ℤ) - 1), wp j) ≤
        (1 / 2 : ℝ) * ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1)) := by
    have hsumH :
        (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1), if h ≤ j then wp j else 0) =
          ∑ j ∈ Finset.Icc h ((L : ℤ) - 1), wp j := by
      have hf : (Finset.Icc 0 ((L : ℤ) - 1)).filter (fun j ↦ h ≤ j) =
          Finset.Icc h ((L : ℤ) - 1) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [← hf, Finset.sum_filter]
    have heq :
        (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1), wp j) +
            (1 / 2 : ℝ) * (∑ j ∈ Finset.Icc h ((L : ℤ) - 1), wp j) =
          ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
            ((1 / 2 : ℝ) * (2 * wp j + if h ≤ j then wp j else 0)) := by
      rw [← hsumH, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      split <;> ring
    rw [heq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hjmem
    have hjr := Finset.mem_Icc.mp hjmem
    have hjt : j ≤ t := by omega
    have hw := grid_pos_weight_nonneg q hq j hjr.1
    by_cases hjh : h ≤ j
    · have hsub : ({0, 1, 2} : Finset ℤ) ⊆ gridA q t j := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact zero_mem_grid_column q hq t j hjt
        · exact (zero_one_subset_grid_column q hq t j hjt (by omega)) (by simp)
        · exact grid_two_mem_case3 q hq L hq2L t j hjt (by dsimp [h] at hjh; omega)
      have hcN : 3 ≤ (gridA q t j).card := by
        have hc := Finset.card_le_card hsub
        norm_num at hc ⊢
        exact hc
      have hc : (3 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast hcN
      simp [hjh, wp]
      nlinarith
    · have hcN : 2 ≤ (gridA q t j).card :=
        Finset.card_le_card (zero_one_subset_grid_column q hq t j hjt (by omega))
      have hc : (2 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast hcN
      simp [hjh, wp]
      nlinarith
  have hs1 := sum_Icc_zpow_mul_sub_one q hqne (-T) (-1) (by omega)
  have hs2 := sum_Icc_zpow_mul_sub_one q hqne (-t) (-1) (by omega)
  have hs3 := sum_Icc_zpow_mul_sub_one q hqne (-t) (t - 2 * (L : ℤ)) (by omega)
  have hp1 := sum_Icc_zpow_difference q hqne 0 ((L : ℤ) - 1) (by omega)
  have hp2 := sum_Icc_zpow_difference q hqne h ((L : ℤ) - 1) (by omega)
  have hlower := add_le_add (add_le_add hneg hpos) (le_refl (1 - q ^ (-1 : ℤ)))
  have hqtpos : 0 < q ^ t := zpow_pos hqpos t
  have ht1 : q ^ (t + 1) = q ^ t * q := by rw [zpow_add_one₀ hqne]
  have hnt : q ^ (-t) = 1 / q ^ t := by simp [zpow_neg, one_div]
  have hnL : q ^ (-(L : ℤ)) = 1 / q ^ (L : ℤ) := by
    simp [zpow_neg, one_div]
  have hhpow : q ^ h = 2 / q ^ t := by
    dsimp [h]
    rw [zpow_sub₀ hqne, hq2L]
  have hhneg : q ^ (-h) = q ^ t / 2 := by
    rw [zpow_neg, hhpow]
    field_simp [hqtpos.ne']
  have hthird : q ^ (t - 2 * (L : ℤ) + 1) = q ^ t * q / 2 := by
    have he : t - 2 * (L : ℤ) + 1 = (t + 1) - 2 * (L : ℤ) := by omega
    rw [he, zpow_sub₀ hqne, hq2L, ht1]
  have hLp : (L : ℤ) - 1 + 1 = (L : ℤ) := by omega
  have hLm : -((L : ℤ) - 1) - 1 = -(L : ℤ) := by omega
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsInv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp [hspos.ne']
    nlinarith [hsSq]
  have hnegone : q ^ (-1 : ℤ) = 1 / q := by
    rw [zpow_neg]
    norm_num [one_div]
  have htarget :
      gridBetaPrefix q L T t + gridResidual3 q (q ^ t) =
        (((∑ j ∈ Finset.Icc (-T) (-1), wn j) +
            ∑ j ∈ Finset.Icc (-t) (-1), wn j) +
            ∑ j ∈ Finset.Icc (-t) (t - 2 * (L : ℤ)), wn j) +
          ((∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1), wp j) +
            (1 / 2 : ℝ) * (∑ j ∈ Finset.Icc h ((L : ℤ) - 1), wp j)) +
          (1 - q ^ (-1 : ℤ)) := by
    rw [grid_beta_prefix_eq q hqne L T t hT hLt]
    dsimp [wn, wp]
    rw [hs1, hs2, hs3, hp1, hp2]
    norm_num only [Int.reduceNeg, add_neg_cancel, zpow_zero]
    rw [hLp, hLm, ht1, hnt, hnL, hhpow, hhneg, hthird, hqL, hnegone, hsInv]
    dsimp [gridResidual3, gridEta]
    field_simp [hqne, hqtpos.ne', hspos.ne']
    ring_nf
  rw [htarget]
  exact hlower

/-! ### Upstream module `MerLeanExperiment/GridRatio.lean` -/

theorem grid_ratio_spec (L : ℕ) (hL : 1 ≤ L) :
    1 < gridQ L ∧ gridQ L ^ (L : ℤ) = Real.sqrt 2 ∧
      gridQ L ^ (2 * (L : ℤ)) = 2 ∧ 0 < gridEta := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hq : 1 < gridQ L := Real.one_lt_rpow (by norm_num) (by positivity)
  have hqL : gridQ L ^ (L : ℤ) = Real.sqrt 2 := by
    rw [gridQ, ← Real.rpow_intCast, ← Real.rpow_mul (by norm_num), Real.sqrt_eq_rpow]
    congr 1
    push_cast
    field_simp
  have hq2L : gridQ L ^ (2 * (L : ℤ)) = 2 := by
    rw [mul_comm (2 : ℤ), zpow_mul, hqL]
    norm_num [Real.sq_sqrt]
  have heta : 0 < gridEta := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hs0 := Real.sqrt_nonneg (2 : ℝ)
    dsimp [gridEta]
    nlinarith
  exact ⟨hq, hqL, hq2L, heta⟩

theorem gridQ_tendsto_one : Filter.Tendsto gridQ Filter.atTop (nhds 1) := by
  have h := tendsto_const_div_atTop_nhds_zero_nat (Real.log 2 / 2)
  have he := Real.continuous_exp.continuousAt.tendsto.comp h
  have hid : gridQ = fun L : ℕ => Real.exp ((Real.log 2 / 2) / (L : ℝ)) := by
    funext L
    rw [gridQ, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hid]
  simpa only [Real.exp_zero, Function.comp_def] using he

/-! ### Upstream module `MerLeanExperiment/QuadraticChord.lean` -/

theorem quadratic_nonneg_between (a b u A B C : ℝ) (ha : a ≤ u) (hb : u ≤ b)
    (hA : A ≤ 0) (hleft : 0 ≤ A * a ^ 2 + B * a + C)
    (hright : 0 ≤ A * b ^ 2 + B * b + C) :
    0 ≤ A * u ^ 2 + B * u + C := by
  by_cases heq : a = b
  · have hu : u = a := by linarith
    simpa only [hu] using hleft
  have hgap : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne (ha.trans hb) heq)
  have hid : (b - a) * (A * u ^ 2 + B * u + C) =
      (b - u) * (A * a ^ 2 + B * a + C) +
      (u - a) * (A * b ^ 2 + B * b + C) +
      (-A) * (u - a) * (b - u) * (b - a) := by ring
  have hmul : 0 ≤ (b - a) * (A * u ^ 2 + B * u + C) := by
    rw [hid]
    have hua := sub_nonneg.mpr ha
    have hbu := sub_nonneg.mpr hb
    have hnA := neg_nonneg.mpr hA
    positivity
  by_contra hn
  exact (not_lt_of_ge hmul) (mul_neg_of_pos_of_neg hgap (lt_of_not_ge hn))

/-! ### Upstream module `MerLeanExperiment/GridScalar3.lean` -/

/-- For all sufficiently fine source grids, the exact third-case residual is
nonnegative throughout its full real endpoint interval. -/
theorem grid_case3_scalar : ∃ L0 : ℕ, 1 ≤ L0 ∧ ∀ L ≥ L0, ∀ u : ℝ,
    Real.sqrt 2 ≤ u → u ≤ 2 / gridQ L → 0 ≤ gridResidual3 (gridQ L) u := by
  let F : ℝ → ℝ := fun q ↦ 1 / q - Real.sqrt 2 * (1 / 2 + gridEta)
  let G : ℝ → ℝ := fun q ↦
    9 * Real.sqrt 2 / 4 + Real.sqrt 2 * gridEta - 2 * gridEta -
      3 / (2 * q) - 3 * q / 2
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsmall : 13 * Real.sqrt 2 < 23 := by
    nlinarith [sq_nonneg (13 * Real.sqrt 2 + 23)]
  have hlarge : 65 < 48 * Real.sqrt 2 := by
    nlinarith [sq_nonneg (48 * Real.sqrt 2 + 65)]
  have hFone : 0 < F 1 := by
    dsimp [F, gridEta]
    nlinarith
  have hGone : 0 < G 1 := by
    dsimp [G, gridEta]
    nlinarith
  have hFcont : ContinuousAt F 1 := by
    dsimp [F]
    fun_prop (disch := norm_num)
  have hGcont : ContinuousAt G 1 := by
    dsimp [G]
    fun_prop (disch := norm_num)
  have hFevent : ∀ᶠ L : ℕ in Filter.atTop, 0 < F (gridQ L) :=
    (hFcont.tendsto.comp gridQ_tendsto_one).eventually (lt_mem_nhds hFone)
  have hGevent : ∀ᶠ L : ℕ in Filter.atTop, 0 < G (gridQ L) :=
    (hGcont.tendsto.comp gridQ_tendsto_one).eventually (lt_mem_nhds hGone)
  obtain ⟨Lbase, hLbase⟩ := Filter.eventually_atTop.1 (hFevent.and hGevent)
  refine ⟨max 1 Lbase, le_max_left _ _, ?_⟩
  intro L hL u huLower huUpper
  have hLone : 1 ≤ L := le_trans (le_max_left 1 Lbase) hL
  have hLbase' : Lbase ≤ L := le_trans (le_max_right 1 Lbase) hL
  have hFG := hLbase L hLbase'
  have hspec := grid_ratio_spec L hLone
  have hq : 1 < gridQ L := hspec.1
  have hqpos : 0 < gridQ L := zero_lt_one.trans hq
  have heta : 0 < gridEta := hspec.2.2.2
  let q : ℝ := gridQ L
  have hq' : 1 < q := hq
  have hqpos' : 0 < q := hqpos
  have hFq : 0 < F q := hFG.1
  have hGq : 0 < G q := hFG.2
  have hleftEq : gridResidual3 q (Real.sqrt 2) = (q - 1) * F q := by
    dsimp [gridResidual3, F]
    field_simp [hqpos'.ne', hspos.ne']
    nlinarith
  have hrightEq : gridResidual3 q (2 / q) = G q := by
    dsimp [gridResidual3, G]
    field_simp [hqpos'.ne']
    ring
  have hleft : 0 ≤ gridResidual3 q (Real.sqrt 2) := by
    rw [hleftEq]
    exact mul_nonneg (sub_nonneg.mpr hq'.le) hFq.le
  have hright : 0 ≤ gridResidual3 q (2 / q) := by
    rw [hrightEq]
    exact hGq.le
  let A : ℝ := -q / 2 - 1 / 4 - gridEta * q
  let B : ℝ := 9 * Real.sqrt 2 / 4 + Real.sqrt 2 * gridEta + 1 - 1 / q
  have hA : A ≤ 0 := by
    dsimp [A]
    have : 0 ≤ gridEta * q := mul_nonneg heta.le hqpos'.le
    nlinarith
  have hmulEq (v : ℝ) (hv : v ≠ 0) :
      v * gridResidual3 q v = A * v ^ 2 + B * v - 3 := by
    dsimp [gridResidual3, A, B]
    field_simp [hqpos'.ne', hv]
    ring
  have hquadLeft : 0 ≤ A * (Real.sqrt 2) ^ 2 + B * Real.sqrt 2 - 3 := by
    rw [← hmulEq (Real.sqrt 2) hspos.ne']
    exact mul_nonneg hs0 hleft
  have hbpos : 0 < 2 / q := div_pos (by norm_num) hqpos'
  have hquadRight : 0 ≤ A * (2 / q) ^ 2 + B * (2 / q) - 3 := by
    rw [← hmulEq (2 / q) hbpos.ne']
    exact mul_nonneg hbpos.le hright
  have huLower' : Real.sqrt 2 ≤ u := huLower
  have huUpper' : u ≤ 2 / q := huUpper
  have hquad := quadratic_nonneg_between (Real.sqrt 2) (2 / q) u A B (-3)
    huLower' huUpper' hA (by simpa using hquadLeft) (by simpa using hquadRight)
  have hupos : 0 < u := hspos.trans_le huLower
  have hquad' : 0 ≤ A * u ^ 2 + B * u - 3 := by
    simpa only [sub_eq_add_neg] using hquad
  rw [← hmulEq u hupos.ne'] at hquad'
  change 0 ≤ gridResidual3 q u
  exact nonneg_of_mul_nonneg_right hquad' hupos

/-! ### Upstream module `MerLeanExperiment/GridPrefixCase3.lean` -/

theorem grid_prefix_case3 : ∃ L0 : ℕ, 1 ≤ L0 ∧ ∀ L ≥ L0, ∀ T t : ℤ,
    0 ≤ T → t ≤ T → (L : ℤ) ≤ t → t < 2 * (L : ℤ) →
    gridBetaPrefix (gridQ L) L T t ≤ gridCapacityPrefix (gridQ L) L T t := by
  obtain ⟨L0, hL0, hscalar⟩ := grid_case3_scalar
  refine ⟨L0, hL0, ?_⟩
  intro L hL T t hT htT hLt ht2L
  have hLone : 1 ≤ L := hL0.trans hL
  obtain ⟨hq, hqL, hq2L, _⟩ := grid_ratio_spec L hLone
  have hqne : gridQ L ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  have hlu : Real.sqrt 2 ≤ gridQ L ^ t := by
    rw [← hqL]
    exact zpow_le_zpow_right₀ hq.le hLt
  have huu : gridQ L ^ t ≤ 2 / gridQ L := by
    calc
      _ ≤ gridQ L ^ (2 * (L : ℤ) - 1) :=
        zpow_le_zpow_right₀ hq.le (by omega)
      _ = 2 / gridQ L := by rw [zpow_sub_one₀ hqne, hq2L, div_eq_mul_inv]
  have hnonneg := hscalar L hL (gridQ L ^ t) hlu huu
  exact (le_add_of_nonneg_right hnonneg).trans
    (grid_case3_capacity (gridQ L) hq L hLone hqL hq2L T t hT htT hLt ht2L)

/-! ### Upstream module `MerLeanExperiment/GridExtraDefinitions.lean` -/

/-- Actual reflected extra-point incidence sum in the fourth grid case. -/
noncomputable def gridExtra4 (q : ℝ) (T t : ℤ) : ℝ := by
  classical
  exact ∑ a ∈ Finset.Icc (⌊q ^ t⌋₊ + 1) ⌊q ^ t + 1 / 2⌋₊,
    ∑ j ∈ Finset.Icc (-T) (-1),
      if (a : ℝ) ≤ min (q ^ t * q ^ j + 1) (q ^ t / q ^ j)
      then q ^ j * (q - 1) else 0

/-! ### Upstream module `MerLeanExperiment/GeometricThresholds.lean` -/

theorem geom_tail_lower (q : ℝ) (hq : 1 < q) (T : ℤ) (hT : 0 ≤ T) (s : ℝ)
    (hs : q ^ (-T) ≤ s) :
    1 - q * s ≤ ∑ j ∈ (Finset.Icc (-T) (-1)).filter (fun j => s ≤ q ^ j),
      q ^ j * (q - 1) := by
  let A := (Finset.Icc (-T) (-1)).filter (fun j => s ≤ q ^ j)
  have hq0 : 0 < q := zero_lt_one.trans hq
  by_cases hA : A.Nonempty
  · let j0 := A.min' hA
    have hj0A : j0 ∈ A := Finset.min'_mem A hA
    have hj0 : j0 ∈ Finset.Icc (-T) (-1) := (Finset.mem_filter.1 hj0A).1
    have hsj0 : s ≤ q ^ j0 := (Finset.mem_filter.1 hj0A).2
    have hset : A = Finset.Icc j0 (-1) := by
      ext j
      constructor
      · intro hjA
        have hj := Finset.mem_filter.1 hjA
        exact Finset.mem_Icc.2 ⟨Finset.min'_le A j hjA, (Finset.mem_Icc.1 hj.1).2⟩
      · intro hjI
        have hjbounds := Finset.mem_Icc.1 hjI
        have hj0bounds := Finset.mem_Icc.1 hj0
        refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hj0bounds.1.trans hjbounds.1,
          hjbounds.2⟩, hsj0.trans ?_⟩
        exact zpow_le_zpow_right₀ hq.le hjbounds.1
    have hj0bound : q ^ j0 ≤ q * s := by
      by_cases heq : j0 = -T
      · rw [heq]
        have hs0 : 0 ≤ s := (zpow_pos hq0 _).le.trans hs
        nlinarith
      · have hj0bounds := Finset.mem_Icc.1 hj0
        have hjgt : -T < j0 := lt_of_le_of_ne hj0bounds.1 (Ne.symm heq)
        have hjpred : j0 - 1 ∈ Finset.Icc (-T) (-1) := by
          simp only [Finset.mem_Icc]
          omega
        have hfail : ¬s ≤ q ^ (j0 - 1) := by
          intro hp
          have hm : j0 - 1 ∈ A := Finset.mem_filter.2 ⟨hjpred, hp⟩
          have := Finset.min'_le A (j0 - 1) hm
          omega
        have hp_lt : q ^ (j0 - 1) < s := lt_of_not_ge hfail
        rw [show j0 = (j0 - 1) + 1 by ring, zpow_add_one₀ hq0.ne']
        simpa [mul_comm] using (mul_lt_mul_of_pos_right hp_lt hq0).le
    change 1 - q * s ≤ ∑ j ∈ A, q ^ j * (q - 1)
    rw [hset, sum_Icc_zpow_mul_sub_one q hq0.ne' j0 (-1) (by
      have hj0bounds := Finset.mem_Icc.1 hj0
      omega)]
    norm_num
    linarith
  · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change 1 - q * s ≤ ∑ j ∈ A, q ^ j * (q - 1)
    rw [hAempty]
    simp only [Finset.sum_empty]
    by_cases hT0 : T = 0
    · subst T
      norm_num at hs
      nlinarith
    · have hm1base : (-1 : ℤ) ∈ Finset.Icc (-T) (-1) := by
        simp only [Finset.mem_Icc]
        omega
      have hnot : ¬s ≤ q ^ (-1 : ℤ) := by
        intro hp
        have : (-1 : ℤ) ∈ A := Finset.mem_filter.2 ⟨hm1base, hp⟩
        rw [hAempty] at this
        simp at this
      have hinv : q ^ (-1 : ℤ) = q⁻¹ := by simp
      rw [hinv] at hnot
      have hmul : 1 < q * s := by
        have := lt_of_not_ge hnot
        calc
          1 = q * q⁻¹ := by field_simp
          _ < q * s := mul_lt_mul_of_pos_left this hq0
      linarith

theorem geom_tail_upper (q : ℝ) (hq : 1 < q) (T : ℤ) (_hT : 0 ≤ T) (h : ℝ)
    (_hh0 : 0 < h) (hh1 : h < 1) :
    (∑ j ∈ (Finset.Icc (-T) (-1)).filter (fun j => h < q ^ j),
      q ^ j * (q - 1)) ≤ 1 - h := by
  let A := (Finset.Icc (-T) (-1)).filter (fun j => h < q ^ j)
  have hq0 : 0 < q := zero_lt_one.trans hq
  by_cases hA : A.Nonempty
  · let j0 := A.min' hA
    have hj0A : j0 ∈ A := Finset.min'_mem A hA
    have hj0 : j0 ∈ Finset.Icc (-T) (-1) := (Finset.mem_filter.1 hj0A).1
    have hhj0 : h < q ^ j0 := (Finset.mem_filter.1 hj0A).2
    have hset : A = Finset.Icc j0 (-1) := by
      ext j
      constructor
      · intro hjA
        have hj := Finset.mem_filter.1 hjA
        exact Finset.mem_Icc.2 ⟨Finset.min'_le A j hjA, (Finset.mem_Icc.1 hj.1).2⟩
      · intro hjI
        have hjbounds := Finset.mem_Icc.1 hjI
        have hj0bounds := Finset.mem_Icc.1 hj0
        refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hj0bounds.1.trans hjbounds.1,
          hjbounds.2⟩, hhj0.trans_le ?_⟩
        exact zpow_le_zpow_right₀ hq.le hjbounds.1
    change (∑ j ∈ A, q ^ j * (q - 1)) ≤ 1 - h
    rw [hset, sum_Icc_zpow_mul_sub_one q hq0.ne' j0 (-1) (by
      have hj0bounds := Finset.mem_Icc.1 hj0
      omega)]
    norm_num
    linarith
  · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change (∑ j ∈ A, q ^ j * (q - 1)) ≤ 1 - h
    rw [hAempty]
    simp only [Finset.sum_empty]
    linarith

theorem geom_band_lower (q : ℝ) (hq : 1 < q) (T : ℤ) (hT : 0 ≤ T)
    (s h : ℝ) (hs : q ^ (-T) ≤ s) (hh0 : 0 < h) (hh1 : h < 1) :
    h - q * s ≤ ∑ j ∈ (Finset.Icc (-T) (-1)).filter
      (fun j => s ≤ q ^ j ∧ q ^ j ≤ h), q ^ j * (q - 1) := by
  have hw (j : ℤ) : 0 ≤ q ^ j * (q - 1) :=
    mul_nonneg (zpow_nonneg (by linarith) _) (by linarith)
  by_cases hsh : s ≤ h
  · let J := Finset.Icc (-T) (-1)
    let L := J.filter (fun j => s ≤ q ^ j)
    let U := J.filter (fun j => h < q ^ j)
    let B := J.filter (fun j => s ≤ q ^ j ∧ q ^ j ≤ h)
    have hpart : L = B ∪ U := by
      ext j
      simp only [L, B, U, J, Finset.mem_filter, Finset.mem_Icc, Finset.mem_union]
      constructor
      · rintro ⟨hj, hsj⟩
        by_cases hjh : q ^ j ≤ h
        · exact Or.inl ⟨hj, hsj, hjh⟩
        · exact Or.inr ⟨hj, lt_of_not_ge hjh⟩
      · rintro (hj | hj)
        · exact ⟨hj.1, hj.2.1⟩
        · exact ⟨hj.1, hsh.trans hj.2.le⟩
    have hdisj : Disjoint B U := by
      refine Finset.disjoint_left.2 ?_
      intro j hjB hjU
      have hb := (Finset.mem_filter.1 hjB).2.2
      have hu := (Finset.mem_filter.1 hjU).2
      linarith
    have hsum : (∑ j ∈ L, q ^ j * (q - 1)) =
        (∑ j ∈ B, q ^ j * (q - 1)) + (∑ j ∈ U, q ^ j * (q - 1)) := by
      rw [hpart, Finset.sum_union hdisj]
    have hl := geom_tail_lower q hq T hT s hs
    have hu := geom_tail_upper q hq T hT h hh0 hh1
    change 1 - q * s ≤ ∑ j ∈ L, q ^ j * (q - 1) at hl
    change (∑ j ∈ U, q ^ j * (q - 1)) ≤ 1 - h at hu
    change h - q * s ≤ ∑ j ∈ B, q ^ j * (q - 1)
    linarith
  · have hneg : h - q * s ≤ 0 := by
      have hspos : 0 < s := hh0.trans (lt_of_not_ge hsh)
      nlinarith
    exact hneg.trans (Finset.sum_nonneg fun j _ => hw j)

/-! ### Upstream module `MerLeanExperiment/WeightedIncidence.lean` -/

/-! ### Upstream module `MerLeanExperiment/TwoFamilyIncidence.lean` -/

theorem weighted_two_family_incidence (A B : Finset ℕ) (J : Finset ℤ)
    (f g : ℕ → ℤ) (G : ℤ → Finset ℤ) (P Q : ℕ → ℤ → Prop)
    [∀ a j, Decidable (P a j)] [∀ b j, Decidable (Q b j)]
    (w : ℤ → ℝ) (hw : ∀ j ∈ J, 0 ≤ w j)
    (hf : Set.InjOn f (A : Set ℕ)) (hg : Set.InjOn g (B : Set ℕ))
    (hcross : ∀ a ∈ A, ∀ b ∈ B, f a ≠ g b)
    (hP : ∀ a ∈ A, ∀ j ∈ J, P a j → f a ∈ G j)
    (hQ : ∀ b ∈ B, ∀ j ∈ J, Q b j → g b ∈ G j) :
    (∑ a ∈ A, ∑ j ∈ J, if P a j then w j else 0) +
      (∑ b ∈ B, ∑ j ∈ J, if Q b j then w j else 0) ≤
        ∑ j ∈ J, ((G j).card : ℝ) * w j := by
  classical
  rw [Finset.sum_comm (s := A), Finset.sum_comm (s := B), ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  let Ap := A.filter fun a => P a j
  let Bq := B.filter fun b => Q b j
  have hdis : Disjoint (Ap.image f) (Bq.image g) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp hz
    obtain ⟨b, hb, hgb⟩ := Finset.mem_image.mp hz'
    exact hcross a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      (hfa.trans hgb.symm)
  have hsub : Ap.image f ∪ Bq.image g ⊆ G j := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      exact hP a (Finset.mem_filter.mp ha).1 j hj (Finset.mem_filter.mp ha).2
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
      exact hQ b (Finset.mem_filter.mp hb).1 j hj (Finset.mem_filter.mp hb).2
  have hAf : (Ap.image f).card = Ap.card :=
    Finset.card_image_of_injOn (hf.mono (Finset.filter_subset _ _))
  have hBg : (Bq.image g).card = Bq.card :=
    Finset.card_image_of_injOn (hg.mono (Finset.filter_subset _ _))
  have hcards : Ap.card + Bq.card ≤ (G j).card := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis, hAf, hBg] at hh
    exact hh
  have heqA : (∑ a ∈ A, if P a j then w j else 0) = (Ap.card : ℝ) * w j := by
    rw [← Finset.sum_filter]
    simp [Ap]
  have heqB : (∑ b ∈ B, if Q b j then w j else 0) = (Bq.card : ℝ) * w j := by
    rw [← Finset.sum_filter]
    simp [Bq]
  rw [heqA, heqB, ← add_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcards) (hw j hj)

/-! ### Upstream module `MerLeanExperiment/GridNegativeFour.lean` -/

private lemma sum_Icc_one_cast (n : ℕ) :
    ∑ a ∈ Finset.Icc 1 n, (a : ℝ) = (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hset : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext a
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hset, Finset.sum_insert (by simp), ih]
      push_cast
      ring

private lemma sum_Icc_two_sub_one_cast (n : ℕ) :
    ∑ a ∈ Finset.Icc 2 n, ((a : ℝ) - 1) = (n : ℝ) * (n - 1) / 2 := by
  by_cases hn : n = 0
  · subst n; simp
  by_cases hn1 : n = 1
  · subst n; simp
  have h2 : 2 ≤ n := by omega
  calc
    _ = (∑ a ∈ Finset.Icc 1 n, (a : ℝ)) - 1 - ((Finset.Icc 2 n).card : ℝ) := by
      rw [Finset.sum_sub_distrib]
      have hsplit : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
        ext a
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hsplit, Finset.sum_insert (by simp)]
      simp
    _ = _ := by
      have hcard : (Finset.Icc 2 n).card = n - 1 := by
        simp
      rw [sum_Icc_one_cast]
      rw [hcard]
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        norm_num
      rw [hcast]
      ring

theorem grid_extra4_nonneg (q : ℝ) (hq : 1 < q) (T t : ℤ) :
    0 ≤ gridExtra4 q T t := by
  classical
  simp only [gridExtra4]
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  · exact mul_nonneg (zpow_nonneg (by linarith) _) (by linarith)
  · exact le_rfl

theorem grid_extra4_lower (q : ℝ) (hq : 1 < q) (T t : ℤ) (hT : 0 ≤ T)
    (_ht0 : 0 ≤ t) (htT : t ≤ T) (hu : 2 ≤ q ^ t)
    (hn : (⌊q ^ t⌋₊ : ℝ) < q ^ t - 1 / 2) :
    q ^ t / ((⌊q ^ t⌋₊ : ℝ) + 1) - q * (⌊q ^ t⌋₊ : ℝ) / q ^ t ≤
      gridExtra4 q T t := by
  classical
  let u : ℝ := q ^ t
  let n : ℕ := ⌊u⌋₊
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hu0 : 0 < u := zpow_pos hq0 t
  have hun : (n : ℝ) ≤ u := Nat.floor_le hu0.le
  have hult : u < (n : ℝ) + 1 := Nat.lt_floor_add_one u
  have hn' : (n : ℝ) < u - 1 / 2 := by simpa [n, u] using hn
  have hfloor : ⌊u + 1 / 2⌋₊ = n + 1 := by
    apply le_antisymm
    · have hm : ⌊u + 1 / 2⌋₊ < n + 2 := by
        rw [Nat.floor_lt (by positivity)]
        norm_num at hult ⊢
        linarith
      omega
    · apply Nat.le_floor
      norm_num at hn' ⊢
      linarith
  have hn2 : 2 ≤ n := by
    rw [show n = ⌊u⌋₊ by rfl]
    exact Nat.le_floor hu
  have hs : q ^ (-T) ≤ (n : ℝ) / u := by
    have hp : q ^ (-T) ≤ q ^ (-t) := zpow_le_zpow_right₀ hq.le (by omega)
    have hinv : q ^ (-t) = 1 / u := by
      simp [u, one_div]
    rw [hinv] at hp
    have : 1 / u ≤ (n : ℝ) / u := by
      apply div_le_div_of_nonneg_right _ hu0.le
      exact_mod_cast (show 1 ≤ n by omega)
    exact hp.trans this
  have hh0 : 0 < u / ((n : ℝ) + 1) := div_pos hu0 (by positivity)
  have hh1 : u / ((n : ℝ) + 1) < 1 := (div_lt_one (by positivity)).2 hult
  have hband := geom_band_lower q hq T hT ((n : ℝ) / u)
    (u / ((n : ℝ) + 1)) hs hh0 hh1
  have hcond (j : ℤ) :
      ((n + 1 : ℕ) : ℝ) ≤ min (u * q ^ j + 1) (u / q ^ j) ↔
        (n : ℝ) / u ≤ q ^ j ∧ q ^ j ≤ u / ((n : ℝ) + 1) := by
    have hp : 0 < q ^ j := zpow_pos hq0 j
    constructor
    · intro h
      have h1 := le_trans h (min_le_left _ _)
      have h2 := le_trans h (min_le_right _ _)
      constructor
      · apply (div_le_iff₀ hu0).2
        norm_num at h1 ⊢
        linarith
      · apply (le_div_iff₀ (by positivity)).2
        have hx := (le_div_iff₀ hp).1 h2
        simpa [Nat.cast_add, Nat.cast_one, mul_comm] using hx
    · rintro ⟨h1, h2⟩
      apply le_min
      · have := (div_le_iff₀ hu0).1 h1
        norm_num at this ⊢
        linarith
      · apply (le_div_iff₀ hp).2
        have hx := (le_div_iff₀ (show 0 < (n : ℝ) + 1 by positivity)).1 h2
        simpa [Nat.cast_add, Nat.cast_one, mul_comm] using hx
  change u / ((n : ℝ) + 1) - q * (n : ℝ) / u ≤ gridExtra4 q T t
  rw [gridExtra4]
  change _ ≤ ∑ a ∈ Finset.Icc (n + 1) ⌊u + 1 / 2⌋₊,
    ∑ j ∈ Finset.Icc (-T) (-1),
      if (a : ℝ) ≤ min (u * q ^ j + 1) (u / q ^ j)
      then q ^ j * (q - 1) else 0
  rw [hfloor]
  simp only [Finset.Icc_self, Finset.sum_singleton]
  simp_rw [hcond]
  have hband' : u / ((n : ℝ) + 1) - q * (n : ℝ) / u ≤
      ∑ j ∈ (Finset.Icc (-T) (-1)).filter
        (fun j => (n : ℝ) / u ≤ q ^ j ∧ q ^ j ≤ u / ((n : ℝ) + 1)),
        q ^ j * (q - 1) := by
    calc
      _ = u / ((n : ℝ) + 1) - q * ((n : ℝ) / u) := by ring
      _ ≤ _ := hband
  simpa only [Finset.sum_filter] using hband'

theorem grid_case4_negative_columns (q : ℝ) (hq : 1 < q) (T t : ℤ)
    (hT : 0 ≤ T) (ht0 : 0 ≤ t) (htT : t ≤ T) (hu : 2 ≤ q ^ t) :
    2 * (⌊q ^ t⌋₊ : ℝ) - q * (⌊q ^ t⌋₊ : ℝ) ^ 2 / q ^ t - q ^ (-T) +
        gridExtra4 q T t ≤
      ∑ j ∈ Finset.Icc (-T) (-1), (gridA q t j).card * q ^ j * (q - 1) := by
  classical
  let u : ℝ := q ^ t
  let n : ℕ := ⌊u⌋₊
  let m : ℕ := ⌊u + 1 / 2⌋₊
  let J : Finset ℤ := Finset.Icc (-T) (-1)
  let w : ℤ → ℝ := fun j => q ^ j * (q - 1)
  let P : ℕ → ℤ → Prop := fun a j => (a : ℝ) / u ≤ q ^ j
  let Q : ℕ → ℤ → Prop := fun a j =>
    (a : ℝ) ≤ min (u * q ^ j + 1) (u / q ^ j)
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hu0 : 0 < u := by simpa [u] using zpow_pos hq0 t
  have hun : (n : ℝ) ≤ u := by
    dsimp [n]
    exact Nat.floor_le hu0.le
  have hn2 : 2 ≤ n := by
    dsimp [n]
    exact Nat.le_floor (by simpa [u] using hu)
  have hnm : n ≤ m := by
    apply Nat.floor_mono
    dsimp [u]
    linarith
  have hw : ∀ j ∈ J, 0 ≤ w j := by
    intro j hj
    exact mul_nonneg (zpow_nonneg hq0.le _) (by linarith)
  have hPmem : ∀ a ∈ Finset.Icc 1 n, ∀ j ∈ J, P a j →
      (a : ℤ) ∈ gridA q t j := by
    intro a ha j hj hpa
    have hjle : j ≤ t := by
      have := (Finset.mem_Icc.1 hj).2
      omega
    simp only [gridA, hjle, ↓reduceIte, mem_gridPoints]
    left
    have ha1 : 1 ≤ (a : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 ha).1
    refine ⟨ha1, ?_⟩
    have := (div_le_iff₀ hu0).1 hpa
    simpa [u, mul_comm] using this
  have hQmem : ∀ a ∈ Finset.Icc 1 m, ∀ j ∈ J, Q a j →
      (1 - (a : ℤ)) ∈ gridA q t j := by
    intro a ha j hj hqa
    have hjle : j ≤ t := by
      have := (Finset.mem_Icc.1 hj).2
      omega
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.1 ha).1
    simp only [gridA, hjle, ↓reduceIte, mem_gridPoints]
    right
    constructor
    · have h1 := le_trans hqa (min_le_left _ _)
      have h2 := le_trans hqa (min_le_right _ _)
      have hm : (a : ℝ) - 1 ≤
          min (q ^ j * q ^ t) (q ^ t / q ^ j - 1) := by
        apply le_min
        · dsimp [u] at h1
          nlinarith
        · dsimp [u] at h2
          linarith
      push_cast
      linarith
    · push_cast
      linarith
  have hinc := weighted_two_family_incidence
    (Finset.Icc 1 n) (Finset.Icc 1 m) J
    (fun a => (a : ℤ)) (fun a => 1 - (a : ℤ)) (fun j => gridA q t j)
    P Q w hw
    (by
      intro a ha b hb hab
      exact Int.ofNat_inj.mp hab)
    (by
      intro a ha b hb hab
      exact Int.ofNat_inj.mp (sub_right_inj.mp hab))
    (by
      intro a ha b hb hab
      have ha1 := (Finset.mem_Icc.1 ha).1
      have hb1 := (Finset.mem_Icc.1 hb).1
      omega)
    hPmem hQmem
  have hPA (a : ℕ) (ha : a ∈ Finset.Icc 1 n) :
      1 - q * ((a : ℝ) / u) ≤ ∑ j ∈ J, if P a j then w j else 0 := by
    have hs : q ^ (-T) ≤ (a : ℝ) / u := by
      have hp : q ^ (-T) ≤ q ^ (-t) := zpow_le_zpow_right₀ hq.le (by omega)
      have hinv : q ^ (-t) = 1 / u := by simp [u, one_div]
      rw [hinv] at hp
      have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.1 ha).1
      exact hp.trans (by
        apply div_le_div_of_nonneg_right ha1 hu0.le)
    have htail := geom_tail_lower q hq T hT ((a : ℝ) / u) hs
    simpa only [J, P, w, Finset.sum_filter] using htail
  have hQB (a : ℕ) (ha : a ∈ Finset.Icc 2 n) :
      1 - q * (((a : ℝ) - 1) / u) ≤ ∑ j ∈ J, if Q a j then w j else 0 := by
    have hs : q ^ (-T) ≤ ((a : ℝ) - 1) / u := by
      have hp : q ^ (-T) ≤ q ^ (-t) := zpow_le_zpow_right₀ hq.le (by omega)
      have hinv : q ^ (-t) = 1 / u := by simp [u, one_div]
      rw [hinv] at hp
      have ha2 : (2 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.1 ha).1
      exact hp.trans (by
        apply div_le_div_of_nonneg_right (by linarith) hu0.le)
    have htail := geom_tail_lower q hq T hT (((a : ℝ) - 1) / u) hs
    calc
      _ ≤ ∑ j ∈ J, if ((a : ℝ) - 1) / u ≤ q ^ j then w j else 0 := by
        simpa only [J, w, Finset.sum_filter] using htail
      _ ≤ ∑ j ∈ J, if Q a j then w j else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        split_ifs with hth hqa
        · exact le_rfl
        · exfalso
          apply hqa
          have hjm1 : j ≤ -1 := (Finset.mem_Icc.1 hj).2
          have hqj0 : 0 < q ^ j := zpow_pos hq0 j
          have hqj1 : q ^ j ≤ 1 := by
            simpa using zpow_le_zpow_right₀ hq.le (by omega : j ≤ 0)
          have han : (a : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 ha).2
          apply le_min
          · have hx := (div_le_iff₀ hu0).1 hth
            nlinarith
          · have hau : (a : ℝ) ≤ u := han.trans hun
            apply (le_div_iff₀ hqj0).2
            nlinarith
        · exact (hw j hj)
        · exact le_rfl
  have hQone : ∑ j ∈ J, w j ≤ ∑ j ∈ J, if Q 1 j then w j else 0 := by
    apply Finset.sum_le_sum
    intro j hj
    have hjm1 : j ≤ -1 := (Finset.mem_Icc.1 hj).2
    have hqj0 : 0 < q ^ j := zpow_pos hq0 j
    have hqj1 : q ^ j ≤ 1 := by
      simpa using zpow_le_zpow_right₀ hq.le (by omega : j ≤ 0)
    have huq : (1 : ℝ) ≤ u / q ^ j := by
      apply (le_div_iff₀ hqj0).2
      nlinarith
    have hQ : Q 1 j := by
      simpa only [Q, Nat.cast_one] using
        (le_min (by nlinarith [mul_pos hu0 hqj0]) huq)
    simp [hQ]
  have hJsum : ∑ j ∈ J, w j = 1 - q ^ (-T) := by
    dsimp [J, w]
    rw [sum_Icc_zpow_mul_sub_one q hq0.ne' (-T) (-1) (by omega)]
    norm_num
  have hbase :
      (n : ℝ) - q * (n : ℝ) * ((n : ℝ) + 1) / (2 * u) +
        ((n : ℝ) - q * (n : ℝ) * ((n : ℝ) - 1) / (2 * u) - q ^ (-T)) +
        gridExtra4 q T t ≤
      (∑ a ∈ Finset.Icc 1 n, ∑ j ∈ J, if P a j then w j else 0) +
        ∑ a ∈ Finset.Icc 1 m, ∑ j ∈ J, if Q a j then w j else 0 := by
    have hA : (n : ℝ) - q * (n : ℝ) * ((n : ℝ) + 1) / (2 * u) ≤
        ∑ a ∈ Finset.Icc 1 n, ∑ j ∈ J, if P a j then w j else 0 := by
      calc
        _ = ∑ a ∈ Finset.Icc 1 n, (1 - q * ((a : ℝ) / u)) := by
          rw [Finset.sum_sub_distrib]
          have hcard : (Finset.Icc 1 n).card = n := by simp
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
          have hsumq : (∑ x ∈ Finset.Icc 1 n, q * ((x : ℝ) / u)) =
              q / u * ∑ x ∈ Finset.Icc 1 n, (x : ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
          rw [hsumq]
          rw [sum_Icc_one_cast]
          ring
        _ ≤ _ := Finset.sum_le_sum fun a ha => hPA a ha
    have hsetn : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
      ext a
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hone_not : 1 ∉ Finset.Icc 2 n := by simp
    have hsetm : Finset.Icc 1 m = Finset.Icc 1 n ∪ Finset.Icc (n + 1) m := by
      ext a
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    have hdis : Disjoint (Finset.Icc 1 n) (Finset.Icc (n + 1) m) := by
      exact Finset.disjoint_left.mpr (by
        intro a ha hb
        have ha' := (Finset.mem_Icc.1 ha).2
        have hb' := (Finset.mem_Icc.1 hb).1
        omega)
    have hB0 :
        (n : ℝ) - q * (n : ℝ) * ((n : ℝ) - 1) / (2 * u) - q ^ (-T) ≤
          ∑ a ∈ Finset.Icc 1 n, ∑ j ∈ J, if Q a j then w j else 0 := by
      rw [hsetn, Finset.sum_insert hone_not]
      have hrest : (n : ℝ) - 1 - q * (n : ℝ) * ((n : ℝ) - 1) / (2 * u) ≤
          ∑ a ∈ Finset.Icc 2 n, ∑ j ∈ J, if Q a j then w j else 0 := by
        calc
          _ = ∑ a ∈ Finset.Icc 2 n,
              (1 - q * (((a : ℝ) - 1) / u)) := by
            rw [Finset.sum_sub_distrib]
            have hcard : (Finset.Icc 2 n).card = n - 1 := by simp
            rw [Finset.sum_const, hcard, nsmul_eq_mul]
            have hsumq : (∑ x ∈ Finset.Icc 2 n, q * (((x : ℝ) - 1) / u)) =
                q / u * ∑ x ∈ Finset.Icc 2 n, ((x : ℝ) - 1) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x hx
              ring
            rw [hsumq]
            rw [sum_Icc_two_sub_one_cast]
            have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
              rw [Nat.cast_sub (by omega : 1 ≤ n)]
              norm_num
            rw [hcast]
            ring
          _ ≤ _ := Finset.sum_le_sum fun a ha => hQB a ha
      rw [hJsum] at hQone
      linarith
    have hextra : gridExtra4 q T t =
        ∑ a ∈ Finset.Icc (n + 1) m, ∑ j ∈ J, if Q a j then w j else 0 := by
      simp only [gridExtra4]
      change (∑ a ∈ Finset.Icc (n + 1) m,
        ∑ j ∈ J, if Q a j then w j else 0) = _
      rfl
    have hB :
        ((n : ℝ) - q * (n : ℝ) * ((n : ℝ) - 1) / (2 * u) - q ^ (-T)) +
            gridExtra4 q T t ≤
          ∑ a ∈ Finset.Icc 1 m, ∑ j ∈ J, if Q a j then w j else 0 := by
      rw [hsetm, Finset.sum_union hdis, hextra]
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_right hB0
          (∑ a ∈ Finset.Icc (n + 1) m, ∑ j ∈ J, if Q a j then w j else 0))
    linarith [add_le_add hA hB]
  have := hbase.trans hinc
  dsimp [J, w] at this ⊢
  dsimp [u, n] at this ⊢
  calc
    _ = (⌊q ^ t⌋₊ : ℝ) - q * (⌊q ^ t⌋₊ : ℝ) * ((⌊q ^ t⌋₊ : ℝ) + 1) /
          (2 * q ^ t) +
        ((⌊q ^ t⌋₊ : ℝ) - q * (⌊q ^ t⌋₊ : ℝ) * ((⌊q ^ t⌋₊ : ℝ) - 1) /
          (2 * q ^ t) - q ^ (-T)) + gridExtra4 q T t := by ring
    _ ≤ ∑ j ∈ Finset.Icc (-T) (-1),
        ((gridA q t j).card : ℝ) * (q ^ j * (q - 1)) := this
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-! ### Upstream module `MerLeanExperiment/GridPositiveFour.lean` -/

private lemma grid_case4_column_card_lower (q : ℝ) (hq : 1 < q) (L : ℕ)
    (hq2L : q ^ (2 * (L : ℤ)) = 2) (t j : ℤ)
    (ht : 2 * (L : ℤ) ≤ t) (hj0 : 0 ≤ j) (hjL : j ≤ (L : ℤ) - 1) :
    q ^ t * (q ^ j + q ^ (-j)) - 2 ≤ ((gridA q t j).card : ℝ) := by
  have hqpos : 0 < q := by linarith
  have hqne : q ≠ 0 := hqpos.ne'
  have hjt : j ≤ t := by omega
  have hαpos : 0 < q ^ j := zpow_pos hqpos j
  have hαβ : q ^ j ≤ q ^ t := zpow_le_zpow_right₀ hq.le hjt
  have hqtpos : 0 < q ^ t := zpow_pos hqpos t
  have hqj_one : 1 ≤ q ^ j := one_le_zpow₀ hq.le hj0
  have hqt_two : (2 : ℝ) ≤ q ^ t := by
    rw [← hq2L]
    exact zpow_le_zpow_right₀ hq.le ht
  have hdiv_le : q ^ t / q ^ j ≤ q ^ t := by
    exact (div_le_iff₀ hαpos).2 (by nlinarith)
  have hmin_le : q ^ t / q ^ j - 1 ≤ q ^ j * q ^ t := by
    nlinarith [mul_le_mul_of_nonneg_right hqj_one hqtpos.le]
  have hmin : min (q ^ j * q ^ t) (q ^ t / q ^ j - 1) = q ^ t / q ^ j - 1 :=
    min_eq_right hmin_le
  have hcZ := grid_points_card (q ^ j) (q ^ t) hαpos hαβ
  have hcR : ((gridPoints (q ^ j) (q ^ t)).card : ℝ) =
      (⌊q ^ j * q ^ t⌋ : ℝ) +
        (⌊min (q ^ j * q ^ t) (q ^ t / q ^ j - 1)⌋ : ℝ) + 1 := by
    exact_mod_cast hcZ
  have hf₁ : q ^ j * q ^ t - 1 ≤ (⌊q ^ j * q ^ t⌋ : ℝ) := by
    have h := Int.lt_floor_add_one (q ^ j * q ^ t)
    linarith
  have hf₂ : q ^ t / q ^ j - 2 ≤ (⌊q ^ t / q ^ j - 1⌋ : ℝ) := by
    have h := Int.lt_floor_add_one (q ^ t / q ^ j - 1)
    linarith
  have hneg : q ^ t / q ^ j = q ^ t * q ^ (-j) := by
    rw [zpow_neg]
    field_simp
  simp only [gridA, hjt, ↓reduceIte]
  rw [hmin] at hcR
  calc
    q ^ t * (q ^ j + q ^ (-j)) - 2 =
        q ^ j * q ^ t + q ^ t / q ^ j - 2 := by rw [hneg]; ring
    _ ≤ ((gridPoints (q ^ j) (q ^ t)).card : ℝ) := by
      rw [hcR]
      linarith

private lemma grid_case4_square_sum (q : ℝ) (hq : 1 < q) (L : ℕ) (hL : 1 ≤ L)
    (hq2L : q ^ (2 * (L : ℤ)) = 2) :
    ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
        (q - 1) * (q ^ (2 * j) - q ^ (-2 * j - 1)) =
      (1 - q / 2) / (1 + q) := by
  have hqne : q ≠ 0 := by linarith
  have hden : q ^ 2 - 1 ≠ 0 := by nlinarith
  have htel₁ := sum_Icc_backward_sub
    (fun j : ℤ ↦ q ^ (2 * j + 2)) 0 ((L : ℤ) - 1) (by omega)
  have hs₁ :
      ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (q ^ 2 - 1) * q ^ (2 * j) = 1 := by
    calc
      _ = ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (q ^ (2 * j + 2) - q ^ (2 * (j - 1) + 2)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show 2 * (j - 1) + 2 = 2 * j by omega]
        rw [show q ^ (2 * j + 2) = q ^ (2 * j) * q ^ 2 by
          rw [show 2 * j + 2 = 2 * j + (2 : ℤ) by omega, zpow_add₀ hqne]
          norm_num]
        ring
      _ = q ^ (2 * ((L : ℤ) - 1) + 2) - q ^ (2 * (0 - 1) + 2) := htel₁
      _ = 1 := by
        rw [show 2 * ((L : ℤ) - 1) + 2 = 2 * (L : ℤ) by omega,
          show 2 * ((0 : ℤ) - 1) + 2 = 0 by omega, hq2L]
        norm_num
  have htel₂ := sum_Icc_backward_sub
    (fun j : ℤ ↦ -q ^ (-2 * j - 1)) 0 ((L : ℤ) - 1) (by omega)
  have hs₂ :
      ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (q ^ 2 - 1) * q ^ (-2 * j - 1) = q / 2 := by
    calc
      _ = ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (-q ^ (-2 * j - 1) - (-q ^ (-2 * (j - 1) - 1))) := by
        apply Finset.sum_congr rfl
        intro j _
        have he : -2 * (j - 1) - 1 = -2 * j + 1 := by omega
        rw [he]
        have hp : q ^ (-2 * j + 1) = q ^ (-2 * j - 1) * q ^ 2 := by
          rw [show -2 * j + 1 = (-2 * j - 1) + 2 by omega, zpow_add₀ hqne]
          norm_num
        rw [hp]
        ring
      _ = -q ^ (-2 * ((L : ℤ) - 1) - 1) -
          (-q ^ (-2 * (0 - 1) - 1)) := htel₂
      _ = q / 2 := by
        rw [show -2 * ((L : ℤ) - 1) - 1 = -2 * (L : ℤ) + 1 by omega,
          show -2 * ((0 : ℤ) - 1) - 1 = 1 by omega]
        have hp : q ^ (-2 * (L : ℤ) + 1) = q / 2 := by
          rw [show -2 * (L : ℤ) + 1 = 1 - 2 * (L : ℤ) by omega,
            zpow_sub₀ hqne, hq2L]
          norm_num
        rw [hp, zpow_one]
        ring
  have hsum₁ :
      ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1), q ^ (2 * j) = 1 / (q ^ 2 - 1) := by
    apply (eq_div_iff hden).2
    rw [Finset.sum_mul]
    simpa [mul_comm] using hs₁
  have hsum₂ :
      ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1), q ^ (-2 * j - 1) =
        (q / 2) / (q ^ 2 - 1) := by
    apply (eq_div_iff hden).2
    rw [Finset.sum_mul]
    simpa [mul_comm] using hs₂
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum₁, hsum₂]
  field_simp
  ring

private lemma grid_case4_summand_expand (q : ℝ) (hq : 1 < q) (t j : ℤ) :
    (q ^ t * (q ^ j + q ^ (-j)) - 2) *
        ((q - 1) * (q ^ j - q ^ (-j - 1))) =
      q ^ t * ((q - 1) * (q ^ (2 * j) - q ^ (-2 * j - 1))) +
        (q - 1) * q ^ t * (1 - 1 / q) -
        2 * ((q - 1) * (q ^ j - q ^ (-j - 1))) := by
  have hqne : q ≠ 0 := by linarith
  have hsq : q ^ j * q ^ j = q ^ (2 * j) := by
    rw [← zpow_add₀ hqne]
    congr 1
    omega
  have hone : q ^ j * q ^ (-j) = 1 := by
    rw [← zpow_add₀ hqne]
    norm_num
  have hinv : q ^ j * q ^ (-j - 1) = 1 / q := by
    rw [← zpow_add₀ hqne]
    rw [show j + (-j - 1) = (-1 : ℤ) by omega]
    simp [one_div]
  have href : q ^ (-j - 1) * q ^ (-j) = q ^ (-2 * j - 1) := by
    rw [← zpow_add₀ hqne]
    congr 1
    omega
  calc
    _ = q ^ t * (q - 1) *
          (q ^ j * q ^ j + q ^ j * q ^ (-j) -
            q ^ j * q ^ (-j - 1) - q ^ (-j - 1) * q ^ (-j)) -
        2 * ((q - 1) * (q ^ j - q ^ (-j - 1))) := by ring
    _ = _ := by rw [hsq, hone, hinv, href]; ring

/-- The nonnegative grid columns in Case 4 supply the source's positive-column
lower bound, derived directly from the concrete grid-point cardinalities. -/
theorem grid_case4_positive_columns (q : ℝ) (hq : 1 < q) (L : ℕ) (hL : 1 ≤ L)
    (hqL : q ^ (L : ℤ) = Real.sqrt 2)
    (hq2L : q ^ (2 * (L : ℤ)) = 2)
    (t : ℤ) (ht : 2 * (L : ℤ) ≤ t) :
    q ^ t / (2 * (1 + q)) * (1 - q / 2) + 2 - 3 * Real.sqrt 2 / 2 ≤
      (1 / 2 : ℝ) * ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
        (gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1)) := by
  have hqpos : 0 < q := by linarith
  have hqne : q ≠ 0 := hqpos.ne'
  let I : Finset ℤ := Finset.Icc 0 ((L : ℤ) - 1)
  let W : ℤ → ℝ := fun j ↦ (q - 1) * (q ^ j - q ^ (-j - 1))
  have hW (j : ℤ) (hj : j ∈ I) : 0 ≤ W j := by
    have hjr := Finset.mem_Icc.mp hj
    dsimp [W]
    exact mul_nonneg (by linarith)
      (sub_nonneg.mpr (zpow_le_zpow_right₀ hq.le (by omega)))
  have hcolumns :
      (∑ j ∈ I, (q ^ t * (q ^ j + q ^ (-j)) - 2) * W j) ≤
        ∑ j ∈ I, ((gridA q t j).card : ℝ) * W j := by
    apply Finset.sum_le_sum
    intro j hj
    have hjr := Finset.mem_Icc.mp hj
    exact mul_le_mul_of_nonneg_right
      (grid_case4_column_card_lower q hq L hq2L t j ht hjr.1 hjr.2) (hW j hj)
  have hIcardZ : (I.card : ℤ) = (L : ℤ) := by
    dsimp [I]
    rw [Int.card_Icc_of_le 0 ((L : ℤ) - 1) (by omega)]
    omega
  have hIcard : (I.card : ℝ) = L := by exact_mod_cast hIcardZ
  have hsquare := grid_case4_square_sum q hq L hL hq2L
  have hweight := sum_Icc_zpow_difference q hqne 0 ((L : ℤ) - 1) (by omega)
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsInv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp [hspos.ne']
    nlinarith [hsSq]
  have hnL : q ^ (-(L : ℤ)) = Real.sqrt 2 / 2 := by
    rw [zpow_neg, hqL]
    simpa [one_div] using hsInv
  have hweight' : ∑ j ∈ I, W j = 3 * Real.sqrt 2 / 2 - 2 := by
    dsimp [I, W]
    rw [hweight]
    rw [show (L : ℤ) - 1 + 1 = (L : ℤ) by omega,
      show -((L : ℤ) - 1) - 1 = -(L : ℤ) by omega, hqL, hnL]
    norm_num
    ring
  have hsquare' :
      ∑ j ∈ I, (q - 1) * (q ^ (2 * j) - q ^ (-2 * j - 1)) =
        (1 - q / 2) / (1 + q) := by
    simpa [I] using hsquare
  have hexpand :
      (∑ j ∈ I, (q ^ t * (q ^ j + q ^ (-j)) - 2) * W j) =
        q ^ t / (1 + q) * (1 - q / 2) +
          (L : ℝ) * ((q - 1) * q ^ t * (1 - 1 / q)) +
          4 - 3 * Real.sqrt 2 := by
    have hsumA :
        (∑ j ∈ I, q ^ t *
          ((q - 1) * (q ^ (2 * j) - q ^ (-2 * j - 1)))) =
        q ^ t * (∑ j ∈ I,
          (q - 1) * (q ^ (2 * j) - q ^ (-2 * j - 1))) := by
      rw [Finset.mul_sum]
    have hsumC : (∑ j ∈ I, 2 * W j) = 2 * (∑ j ∈ I, W j) := by
      rw [Finset.mul_sum]
    calc
      _ = ∑ j ∈ I,
          (q ^ t * ((q - 1) * (q ^ (2 * j) - q ^ (-2 * j - 1))) +
            (q - 1) * q ^ t * (1 - 1 / q) - 2 * W j) := by
        apply Finset.sum_congr rfl
        intro j _
        exact grid_case4_summand_expand q hq t j
      _ = q ^ t * (∑ j ∈ I,
            (q - 1) * (q ^ (2 * j) - q ^ (-2 * j - 1))) +
          (I.card : ℝ) * ((q - 1) * q ^ t * (1 - 1 / q)) -
          2 * (∑ j ∈ I, W j) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          hsumA, Finset.sum_const, nsmul_eq_mul, hsumC]
      _ = _ := by
        rw [hsquare', hIcard, hweight']
        ring
  have hmiddle :
      0 ≤ (L : ℝ) * ((q - 1) * q ^ t * (1 - 1 / q)) := by
    have hqinv : 1 / q ≤ 1 := (div_le_one hqpos).2 hq.le
    positivity
  have hlower :
      q ^ t / (2 * (1 + q)) * (1 - q / 2) + 2 - 3 * Real.sqrt 2 / 2 ≤
        (1 / 2 : ℝ) *
          ∑ j ∈ I, (q ^ t * (q ^ j + q ^ (-j)) - 2) * W j := by
    have hqadd : 1 + q ≠ 0 := by linarith
    have hid :
        q ^ t / (2 * (1 + q)) * (1 - q / 2) + 2 - 3 * Real.sqrt 2 / 2 =
          (1 / 2 : ℝ) *
            (q ^ t / (1 + q) * (1 - q / 2) + 4 - 3 * Real.sqrt 2) := by
      field_simp [hqadd]
      ring
    rw [hid, hexpand]
    exact mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
  have hhalf := mul_le_mul_of_nonneg_left hcolumns (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact hlower.trans (by simpa [I, W, mul_assoc] using hhalf)

/-! ### Upstream module `MerLeanExperiment/FloorBranches.lean` -/

/-- The first floor branch is a concave quadratic on the closed half-unit
interval; both endpoint values dominate the common source bound. -/
theorem floor_branch_one (q u n : ℝ) (hq : 1 ≤ q) (hu : 2 ≤ u)
    (hnlo : u - 1 / 2 ≤ n) (hnhi : n ≤ u) :
    (2 - q) * u - q / (4 * u) ≤ 2 * n - q * n ^ 2 / u := by
  have hupos : 0 < u := by linarith
  let A : ℝ := -q / u
  let B : ℝ := 2
  let C : ℝ := -((2 - q) * u - q / (4 * u))
  have hA : A ≤ 0 := by
    dsimp [A]
    have hq0 : 0 ≤ q := le_trans (by norm_num) hq
    have hd : 0 ≤ q / u := div_nonneg hq0 hupos.le
    have heq : -q / u = -(q / u) := by ring
    rw [heq]
    exact neg_nonpos.mpr hd
  have hleft : 0 ≤ A * (u - 1 / 2) ^ 2 + B * (u - 1 / 2) + C := by
    dsimp [A, B, C]
    field_simp [hupos.ne']
    ring_nf
    nlinarith
  have hright : 0 ≤ A * u ^ 2 + B * u + C := by
    dsimp [A, B, C]
    field_simp [hupos.ne']
    ring_nf
    nlinarith
  have hquad := quadratic_nonneg_between (u - 1 / 2) u n A B C
    hnlo hnhi hA hleft hright
  calc
    (2 - q) * u - q / (4 * u) ≤
        (2 - q) * u - q / (4 * u) + (A * n ^ 2 + B * n + C) := by linarith
    _ = 2 * n - q * n ^ 2 / u := by
      dsimp [A, B, C]
      field_simp [hupos.ne']
      ring_nf

/-- The second floor branch lies above its rational endpoint chord on the
closed half-unit interval, by the explicit nonnegative chord-gap identity. -/
theorem floor_branch_two (q u n : ℝ) (hq : 1 ≤ q) (hu : 2 ≤ u)
    (hnlo : u - 1 ≤ n) (hnhi : n ≤ u - 1 / 2) :
    (2 - q) * u - q / (4 * u) ≤
      2 * n - q * n * (n + 1) / u + u / (n + 1) := by
  let a : ℝ := u - 1
  let b : ℝ := u - 1 / 2
  let F : ℝ → ℝ := fun x ↦ 2 * x - q * x * (x + 1) / u + u / (x + 1)
  let target : ℝ := (2 - q) * u - q / (4 * u)
  have hupos : 0 < u := by linarith
  have ha1 : a + 1 = u := by dsimp [a]; ring
  have hb1 : b + 1 = u + 1 / 2 := by dsimp [b]; ring
  have ha1pos : 0 < a + 1 := by rw [ha1]; exact hupos
  have hb1pos : 0 < b + 1 := by rw [hb1]; linarith
  have hn1pos : 0 < n + 1 := by
    linarith
  have hgapPos : 0 < b - a := by
    dsimp [a, b]
    norm_num
  have hFa : target ≤ F a := by
    have heq : F a = (2 - q) * u + (q - 1) := by
      dsimp [F, a]
      field_simp [hupos.ne']
      ring
    rw [heq]
    dsimp [target]
    have : 0 ≤ q / (4 * u) := by positivity
    linarith
  have hFb : target ≤ F b := by
    have hrecip : 1 / (2 * u + 1) ≤ q / (2 * u) := by
      have h2u : 0 < 2 * u := by positivity
      have h2u1 : 0 < 2 * u + 1 := by positivity
      apply (div_le_div_iff₀ h2u1 h2u).2
      nlinarith
    have heq : F b = (2 - q) * u + q / (4 * u) - 1 / (2 * u + 1) := by
      dsimp [F]
      rw [hb1]
      dsimp [b]
      field_simp [hupos.ne', show u + 1 / 2 ≠ 0 by positivity,
        show 2 * u + 1 ≠ 0 by positivity]
      ring
    rw [heq]
    dsimp [target]
    have htwice : q / (4 * u) + q / (4 * u) = q / (2 * u) := by
      field_simp [hupos.ne']
      ring
    linarith
  have habNonneg : 0 ≤ b - n := sub_nonneg.mpr hnhi
  have hnaNonneg : 0 ≤ n - a := sub_nonneg.mpr hnlo
  have hprodPos : 0 < (a + 1) * (b + 1) * (n + 1) := by positivity
  have hsecond : u / ((a + 1) * (b + 1) * (n + 1)) ≤ 1 / u := by
    apply (div_le_div_iff₀ hprodPos hupos).2
    rw [ha1]
    have hbn : u ≤ (b + 1) * (n + 1) := by
      have hbge : u ≤ b + 1 := by rw [hb1]; linarith
      have hnge : 1 ≤ n + 1 := by linarith
      calc
        u = u * 1 := by ring
        _ ≤ (b + 1) * (n + 1) :=
          mul_le_mul hbge hnge (by linarith) (by linarith)
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hbn hupos.le
  have hfirst : 1 / u ≤ q / u := by
    exact (div_le_div_iff_of_pos_right hupos).2 hq
  have hbracket : 0 ≤ q / u - u / ((a + 1) * (b + 1) * (n + 1)) := by
    linarith
  have hgapNonneg : 0 ≤
      (n - a) * (b - n) *
        (q / u - u / ((a + 1) * (b + 1) * (n + 1))) := by
    positivity
  let chord : ℝ := ((b - n) * F a + (n - a) * F b) / (b - a)
  have hchord : target ≤ chord := by
    have hweighted : (b - a) * target ≤ (b - n) * F a + (n - a) * F b := by
      have h1 := mul_le_mul_of_nonneg_left hFa habNonneg
      have h2 := mul_le_mul_of_nonneg_left hFb hnaNonneg
      have hweights : (b - n) * target + (n - a) * target = (b - a) * target := by ring
      rw [← hweights]
      exact add_le_add h1 h2
    dsimp [chord]
    exact (le_div_iff₀ hgapPos).2 (by simpa [mul_comm] using hweighted)
  have hgapEq : F n - chord =
      (n - a) * (b - n) *
        (q / u - u / ((a + 1) * (b + 1) * (n + 1))) := by
    dsimp [F, chord]
    field_simp [hupos.ne', ha1pos.ne', hb1pos.ne', hn1pos.ne', hgapPos.ne']
    ring
  have hFn : chord ≤ F n := by
    rw [← sub_nonneg]
    rw [hgapEq]
    exact hgapNonneg
  exact hchord.trans hFn

/-! ### Upstream module `MerLeanExperiment/GridCapacity4.lean` -/

theorem grid_case4_capacity (q : ℝ) (hq : 1 < q) (L : ℕ) (hL : 1 ≤ L)
    (hqL : q ^ (L : ℤ) = Real.sqrt 2) (hq2L : q ^ (2 * (L : ℤ)) = 2)
    (T t : ℤ) (hT : 0 ≤ T) (htT : t ≤ T) (ht2L : 2 * (L : ℤ) ≤ t) :
    gridBetaPrefix q L T t +
      (q ^ t * gridSlope4 q + 2 - 3 * Real.sqrt 2 / 2 + gridEta * Real.sqrt 2 -
        q / (4 * q ^ t)) ≤ gridCapacityPrefix q L T t := by
  have hqpos : 0 < q := by linarith
  have ht0 : 0 ≤ t := by omega
  have hu : 2 ≤ q ^ t := by
    rw [← hq2L]
    exact zpow_le_zpow_right₀ hq.le ht2L
  have hup : 0 < q ^ t := zpow_pos hqpos _
  let n : ℝ := ⌊q ^ t⌋₊
  have hnhi : n ≤ q ^ t := Nat.floor_le hup.le
  have hnlo : q ^ t - 1 ≤ n := by
    have hh := Nat.lt_floor_add_one (q ^ t)
    dsimp [n]
    linarith
  have hscalar : (2 - q) * q ^ t - q / (4 * q ^ t) ≤
      2 * n - q * n ^ 2 / q ^ t + gridExtra4 q T t := by
    by_cases hn : q ^ t - 1 / 2 ≤ n
    · have h := floor_branch_one q (q ^ t) n hq.le hu hn hnhi
      have he := grid_extra4_nonneg q hq T t
      linarith
    · have hn' : n < q ^ t - 1 / 2 := lt_of_not_ge hn
      have h := floor_branch_two q (q ^ t) n hq.le hu hnlo hn'.le
      have he := grid_extra4_lower q hq T t hT ht0 htT hu hn'
      have heq : 2 * n - q * n * (n + 1) / q ^ t + q ^ t / (n + 1) =
          2 * n - q * n ^ 2 / q ^ t + (q ^ t / (n + 1) - q * n / q ^ t) := by ring
      rw [heq] at h
      change q ^ t / (n + 1) - q * n / q ^ t ≤ gridExtra4 q T t at he
      linarith
  have hneg := grid_case4_negative_columns q hq T t hT ht0 htT hu
  have hpos := grid_case4_positive_columns q hq L hL hqL hq2L t ht2L
  have hcap := grid_capacity_prefix_eq q hq L hL T t hT (by omega)
  simp only [ht0, ↓reduceIte] at hcap
  have hex : 0 ≤ 1 - q ^ (-1 : ℤ) := by
    have hh : q ^ (-1 : ℤ) ≤ q ^ (0 : ℤ) := zpow_le_zpow_right₀ hq.le (by norm_num)
    exact sub_nonneg.mpr (by simpa only [zpow_zero] using hh)
  have hbeta := grid_beta_prefix_eq q hqpos.ne' L T t hT (by omega)
  rw [hqL, zpow_add₀ hqpos.ne', zpow_one] at hbeta
  rw [hcap, hbeta]
  unfold gridSlope4
  change 2 * n - q * n ^ 2 / q ^ t - q ^ (-T) + gridExtra4 q T t ≤ _ at hneg
  have halg : (q ^ t * q - q ^ (-T) + gridEta * (q ^ t * q - Real.sqrt 2)) +
      (q ^ t * (2 - 2 * q + (1 - q / 2) / (2 * (1 + q)) - gridEta * q) +
        2 - 3 * Real.sqrt 2 / 2 + gridEta * Real.sqrt 2 - q / (4 * q ^ t)) =
      ((2 - q) * q ^ t - q / (4 * q ^ t)) - q ^ (-T) +
        (q ^ t / (2 * (1 + q)) * (1 - q / 2) + 2 - 3 * Real.sqrt 2 / 2) := by ring
  rw [halg]
  linarith

/-! ### Upstream module `MerLeanExperiment/GridScalar4.lean` -/

/-- For every sufficiently fine source grid, the fourth-case scalar residual is
nonnegative uniformly for all admissible values of `u`. -/
theorem grid_case4_scalar : ∃ L0 : ℕ, 1 ≤ L0 ∧ ∀ L ≥ L0, ∀ u : ℝ,
    2 ≤ u → 0 ≤ u * gridSlope4 (gridQ L) + 2 - 3 * Real.sqrt 2 / 2 +
      gridEta * Real.sqrt 2 - gridQ L / (4 * u) := by
  let D : ℝ → ℝ := fun q ↦ gridSlope4 q
  let E : ℝ → ℝ := fun q ↦ gridResidual4 q
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsmall : 12 * Real.sqrt 2 < 17 := by
    nlinarith [sq_nonneg (12 * Real.sqrt 2 + 17)]
  have hDone : 0 < D 1 := by
    dsimp [D, gridSlope4, gridEta]
    nlinarith
  have hEone : 0 < E 1 := by
    dsimp [E, gridResidual4, gridSlope4, gridEta]
    nlinarith
  have hDcont : ContinuousAt D 1 := by
    dsimp [D, gridSlope4]
    fun_prop (disch := norm_num)
  have hEcont : ContinuousAt E 1 := by
    dsimp [E, gridResidual4, gridSlope4]
    fun_prop (disch := norm_num)
  have hDevent : ∀ᶠ L : ℕ in Filter.atTop, 0 < D (gridQ L) :=
    (hDcont.tendsto.comp gridQ_tendsto_one).eventually (lt_mem_nhds hDone)
  have hEevent : ∀ᶠ L : ℕ in Filter.atTop, 0 < E (gridQ L) :=
    (hEcont.tendsto.comp gridQ_tendsto_one).eventually (lt_mem_nhds hEone)
  obtain ⟨Lbase, hLbase⟩ := Filter.eventually_atTop.1 (hDevent.and hEevent)
  refine ⟨max 1 Lbase, le_max_left _ _, ?_⟩
  intro L hL u hu
  have hLone : 1 ≤ L := le_trans (le_max_left 1 Lbase) hL
  have hLbase' : Lbase ≤ L := le_trans (le_max_right 1 Lbase) hL
  have hDE := hLbase L hLbase'
  have hqpos : 0 < gridQ L := (grid_ratio_spec L hLone).1.trans' zero_lt_one
  have huPos : 0 < u := by linarith
  have hDu : 2 * D (gridQ L) ≤ u * D (gridQ L) := by
    exact mul_le_mul_of_nonneg_right hu hDE.1.le
  have hfrac : gridQ L / (4 * u) ≤ gridQ L / 8 := by
    apply (div_le_div_iff_of_pos_left hqpos (by positivity) (by norm_num)).2
    nlinarith
  have hE : 0 ≤ E (gridQ L) := hDE.2.le
  dsimp [E, gridResidual4] at hE
  dsimp [D] at hDu
  nlinarith

/-! ### Upstream module `MerLeanExperiment/GridPrefixCase4.lean` -/

theorem grid_prefix_case4 : ∃ L0 : ℕ, 1 ≤ L0 ∧ ∀ L ≥ L0, ∀ T t : ℤ,
    0 ≤ T → t ≤ T → 2 * (L : ℤ) ≤ t →
    gridBetaPrefix (gridQ L) L T t ≤ gridCapacityPrefix (gridQ L) L T t := by
  obtain ⟨L0, hL0, hscalar⟩ := grid_case4_scalar
  refine ⟨L0, hL0, ?_⟩
  intro L hL T t hT htT ht2L
  have hLone : 1 ≤ L := hL0.trans hL
  obtain ⟨hq, hqL, hq2L, _⟩ := grid_ratio_spec L hLone
  have hu : 2 ≤ gridQ L ^ t := by
    rw [← hq2L]
    exact zpow_le_zpow_right₀ hq.le ht2L
  exact (le_add_of_nonneg_right (hscalar L hL (gridQ L ^ t) hu)).trans
    (grid_case4_capacity (gridQ L) hq L hLone hqL hq2L T t hT htT ht2L)

/-! ### Upstream module `MerLeanExperiment/GridPrefixAll.lean` -/

theorem grid_prefix_all : ∃ L0 : ℕ, 1 ≤ L0 ∧ ∀ L ≥ L0, ∀ T : ℤ,
    (L : ℤ) - 1 ≤ T → ∀ t : ℤ, -T ≤ t → t ≤ T →
    gridBetaPrefix (gridQ L) L T t ≤ gridCapacityPrefix (gridQ L) L T t := by
  obtain ⟨L3, hL3, h3⟩ := grid_prefix_case3
  obtain ⟨L4, hL4, h4⟩ := grid_prefix_case4
  refine ⟨max L3 L4, hL3.trans (le_max_left _ _), ?_⟩
  intro L hL T hT t htlo hthi
  have hLone : 1 ≤ L := hL3.trans ((le_max_left _ _).trans hL)
  have hT0 : 0 ≤ T := by omega
  obtain ⟨hq, _, _, _⟩ := grid_ratio_spec L hLone
  by_cases ht0 : t < 0
  · exact grid_prefix_case_neg (gridQ L) hq L hLone T t hT0 htlo ht0
  by_cases htL : t < (L : ℤ)
  · exact grid_prefix_case_small (gridQ L) hq L hLone T t hT0 hT (by omega) htL
  by_cases ht2L : t < 2 * (L : ℤ)
  · exact h3 L ((le_max_left _ _).trans hL) T t hT0 hthi (by omega) ht2L
  · exact h4 L ((le_max_right _ _).trans hL) T t hT0 hthi (by omega)

/-! ### Upstream module `MerLeanExperiment/GridWeightSums.lean` -/

theorem grid_weights_nonneg (q : ℝ) (hq : 1 < q) (L : ℕ) :
    (∀ i : ℤ, 0 ≤ gridBeta q L i) ∧ ∀ j : ℤ, 0 ≤ gridDelta q L j := by
  have hqp : 0 < q := by linarith
  have hqm : 0 ≤ q - 1 := by linarith
  have heta : 0 < gridEta := (grid_ratio_spec 1 le_rfl).2.2.2
  constructor
  · intro i
    unfold gridBeta
    split_ifs <;> positivity
  · intro j
    unfold gridDelta
    split_ifs with hj0 hjL hjLeq
    · exact mul_nonneg (zpow_pos hqp _).le hqm
    · exact mul_nonneg (div_nonneg hqm (by norm_num))
        (sub_nonneg.mpr (zpow_le_zpow_right₀ hq.le (by omega)))
    · have hh : q ^ (-1 : ℤ) ≤ q ^ (0 : ℤ) :=
        zpow_le_zpow_right₀ hq.le (by norm_num)
      exact sub_nonneg.mpr (by simpa only [zpow_zero] using hh)
    · rfl

theorem grid_delta_sum (q : ℝ) (hq : 1 < q) (L : ℕ) (hL : 1 ≤ L)
    (hqL : q ^ (L : ℤ) = Real.sqrt 2) (T : ℤ) (hT : 0 ≤ T) :
    (∑ j ∈ Finset.Icc (-T) (L : ℤ), gridDelta q L j) =
      3 * Real.sqrt 2 / 4 - q ^ (-T) + 1 - q ^ (-1 : ℤ) := by
  classical
  have hqp : 0 < q := by linarith
  have hqne : q ≠ 0 := hqp.ne'
  have hsplit : Finset.Icc (-T) (L : ℤ) =
      (Finset.Icc (-T) (-1) ∪ Finset.Icc 0 ((L : ℤ) - 1)) ∪ {(L : ℤ)} := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdis1 : Disjoint (Finset.Icc (-T) (-1)) (Finset.Icc 0 ((L : ℤ) - 1)) := by
    rw [Finset.disjoint_left]
    intro j hj hk
    simp only [Finset.mem_Icc] at hj hk
    omega
  have hdis2 : Disjoint (Finset.Icc (-T) (-1) ∪ Finset.Icc 0 ((L : ℤ) - 1))
      {(L : ℤ)} := by
    rw [Finset.disjoint_left]
    intro j hj hk
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton] at hj hk
    omega
  have hneg : (∑ j ∈ Finset.Icc (-T) (-1), gridDelta q L j) = 1 - q ^ (-T) := by
    calc
      _ = ∑ j ∈ Finset.Icc (-T) (-1), q ^ j * (q - 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [gridDelta, show j < 0 by have := (Finset.mem_Icc.mp hj).2; omega,
          ↓reduceIte]
      _ = _ := by
        rw [sum_Icc_zpow_mul_sub_one q hqne (-T) (-1) (by omega)]
        norm_num
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hinv : q ^ (-(L : ℤ)) = Real.sqrt 2 / 2 := by
    rw [zpow_neg, hqL]
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).mpr
    have hh : (Real.sqrt 2)⁻¹ * Real.sqrt 2 = 1 := inv_mul_cancel₀ hspos.ne'
    nlinarith
  have hpos : (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1), gridDelta q L j) =
      3 * Real.sqrt 2 / 4 - 1 := by
    calc
      _ = (1 / 2 : ℝ) * ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (q - 1) * (q ^ j - q ^ (-j - 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hj0 := (Finset.mem_Icc.mp hj).1
        have hjL := (Finset.mem_Icc.mp hj).2
        simp only [gridDelta, not_lt.mpr hj0, show j < (L : ℤ) by omega, ↓reduceIte]
        ring
      _ = _ := by
        rw [sum_Icc_zpow_difference q hqne 0 ((L : ℤ) - 1) (by omega)]
        rw [show (L : ℤ) - 1 + 1 = (L : ℤ) by omega,
          show -((L : ℤ) - 1) - 1 = -(L : ℤ) by omega, hqL, hinv]
        norm_num
        ring
  have hlast : gridDelta q L (L : ℤ) = 1 - q ^ (-1 : ℤ) := by
    simp [gridDelta]
  rw [hsplit, Finset.sum_union hdis2, Finset.sum_union hdis1, Finset.sum_singleton,
    hneg, hpos, hlast]
  ring

/-! ### Upstream module `MerLeanExperiment/WeightedGridPacking.lean` -/

theorem sum_int_interval_subtype (a b : ℤ) (f : ℤ → ℝ) :
    (∑ i : {i : ℤ // i ∈ Finset.Icc a b}, f i.val) =
      ∑ i ∈ Finset.Icc a b, f i := by
  classical
  change (∑ i ∈ (Finset.Icc a b).attach, f i.val) = _
  exact Finset.sum_attach (Finset.Icc a b) f

theorem sum_int_interval_prefix (a b t : ℤ) (hat : a ≤ t) (htb : t ≤ b)
    (f : ℤ → ℝ) :
    (∑ i : {i : ℤ // i ∈ Finset.Icc a b}, if i.val ≤ t then f i.val else 0) =
      ∑ i ∈ Finset.Icc a t, f i := by
  classical
  change (∑ i : {i : ℤ // i ∈ Finset.Icc a b},
    if i.val ≤ t then f i.val else 0) = _
  calc
    _ = ∑ i ∈ Finset.Icc a b, if i ≤ t then f i else 0 :=
      sum_int_interval_subtype a b (fun i => if i ≤ t then f i else 0)
    _ = _ := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      · intro i hi
        rfl

theorem eventually_weighted_grid_packing :
    ∃ L0 : ℕ, 1 ≤ L0 ∧ ∀ L ≥ L0, ∀ T : ℤ, (L : ℤ) - 1 ≤ T →
      ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N ≥ N0, ∀ A : Finset ℕ,
        LcmBounded N A →
        (∑ i ∈ Finset.Icc (-T) T, gridBeta (gridQ L) L i *
          intervalDensity A (gridQ L ^ i) (gridQ L ^ (i + 1))
            (Real.sqrt (N : ℝ))) ≤
          (1 + epsilon) * ∑ j ∈ Finset.Icc (-T) (L : ℤ),
            gridDelta (gridQ L) L j := by
  classical
  obtain ⟨L0, hL0, hprefix⟩ := grid_prefix_all
  refine ⟨L0, hL0, ?_⟩
  intro L hL T hT epsilon hepsilon
  have hLone : 1 ≤ L := hL0.trans hL
  obtain ⟨hq, _, _, _⟩ := grid_ratio_spec L hLone
  let I := {i : ℤ // i ∈ Finset.Icc (-T) T}
  let J := {j : ℤ // j ∈ Finset.Icc (-T) (L : ℤ)}
  let row : I → ℤ := fun i => i.val
  let col : J → ℤ := fun j => j.val
  have hrow : Function.Injective row := fun _ _ h => Subtype.ext h
  obtain ⟨N0, hpack⟩ := eventually_uniform_grid_forward_packing
    (I := I) (J := J) (gridQ L) hq L col row hrow epsilon hepsilon
  refine ⟨N0, ?_⟩
  intro N hN A hA
  let alpha : I → ℝ := fun i => intervalDensity A (gridQ L ^ i.val)
    (gridQ L ^ (i.val + 1)) (Real.sqrt (N : ℝ))
  let beta : I → ℝ := fun i => gridBeta (gridQ L) L i.val
  let k : J → I → ℕ := fun j i => gridCount (gridQ L) L i.val j.val
  let delta : J → ℝ := fun j => gridDelta (gridQ L) L j.val
  have halpha : ∀ i, 0 ≤ alpha i := by
    intro i
    unfold alpha intervalDensity
    apply div_nonneg
    · positivity
    · apply mul_nonneg
      · have hp : 0 < gridQ L ^ i.val := zpow_pos (by linarith) _
        have hadd : gridQ L ^ (i.val + 1) = gridQ L ^ i.val * gridQ L := by
          rw [zpow_add₀ (by linarith : gridQ L ≠ 0), zpow_one]
        rw [hadd]
        nlinarith
      · exact Real.sqrt_nonneg _
  obtain ⟨hbeta0, hdelta0⟩ := grid_weights_nonneg (gridQ L) hq L
  have hbeta : ∀ i, 0 ≤ beta i := fun i => hbeta0 i.val
  have hdelta : ∀ j, 0 ≤ delta j := fun j => hdelta0 j.val
  have hpref : ∀ t : I,
      (∑ i : I, if i ≤ t then beta i else 0) ≤
        ∑ i : I, if i ≤ t then ∑ j : J, delta j * k j i else 0 := by
    intro t
    have htlo : -T ≤ t.val := (Finset.mem_Icc.mp t.property).1
    have hthi : t.val ≤ T := (Finset.mem_Icc.mp t.property).2
    have hh := hprefix L hL T hT t.val htlo hthi
    unfold gridBetaPrefix gridCapacityPrefix at hh
    change
      (∑ i : I, if i.val ≤ t.val then gridBeta (gridQ L) L i.val else 0) ≤
        ∑ i : I, if i.val ≤ t.val then
          ∑ j : J, gridDelta (gridQ L) L j.val *
            gridCount (gridQ L) L i.val j.val else 0
    have hinner (i : I) :
        (∑ j : J, gridDelta (gridQ L) L j.val *
          gridCount (gridQ L) L i.val j.val) =
        ∑ j ∈ Finset.Icc (-T) (L : ℤ), gridDelta (gridQ L) L j *
          gridCount (gridQ L) L i.val j := by
      simpa only [J] using sum_int_interval_subtype (-T) (L : ℤ)
        (fun j => gridDelta (gridQ L) L j *
          gridCount (gridQ L) L i.val j)
    simp_rw [hinner]
    rw [sum_int_interval_prefix (-T) T t.val htlo hthi
      (fun i => gridBeta (gridQ L) L i)]
    rw [sum_int_interval_prefix (-T) T t.val htlo hthi
      (fun i => ∑ j ∈ Finset.Icc (-T) (L : ℤ),
        gridDelta (gridQ L) L j * gridCount (gridQ L) L i j)]
    exact hh
  have hmoves : ∀ j (phi : I → I), (∀ i, i ≤ phi i) →
      (∑ i : I, (k j i : ℝ) * alpha (phi i)) ≤ 1 + epsilon := by
    intro j phi hphi
    exact hpack N hN A hA j phi (fun i => hphi i)
  have hh := weighted_finite_order_transfer alpha beta k delta (1 + epsilon)
    halpha hbeta hdelta hpref hmoves
  change (∑ i : I, gridBeta (gridQ L) L i.val *
      intervalDensity A (gridQ L ^ i.val) (gridQ L ^ (i.val + 1))
        (Real.sqrt (N : ℝ))) ≤
      (1 + epsilon) * ∑ j : J, gridDelta (gridQ L) L j.val at hh
  calc
    (∑ i ∈ Finset.Icc (-T) T, gridBeta (gridQ L) L i *
        intervalDensity A (gridQ L ^ i) (gridQ L ^ (i + 1))
          (Real.sqrt (N : ℝ))) =
      ∑ i : I, gridBeta (gridQ L) L i.val *
        intervalDensity A (gridQ L ^ i.val) (gridQ L ^ (i.val + 1))
          (Real.sqrt (N : ℝ)) := by
        symm
        simpa only [I] using sum_int_interval_subtype (-T) T
          (fun i => gridBeta (gridQ L) L i *
            intervalDensity A (gridQ L ^ i) (gridQ L ^ (i + 1))
              (Real.sqrt (N : ℝ)))
    _ ≤ (1 + epsilon) * ∑ j : J, gridDelta (gridQ L) L j.val := hh
    _ = (1 + epsilon) * ∑ j ∈ Finset.Icc (-T) (L : ℤ),
        gridDelta (gridQ L) L j := by
      rw [sum_int_interval_subtype]

/-! ### Upstream module `MerLeanExperiment/IntervalRegionDefinitions.lean` -/

noncomputable def intervalRegion (A : Finset ℕ) (a b R : ℝ) : Finset ℕ := by
  classical
  exact A.filter fun n : ℕ => a * R < (n : ℝ) ∧ (n : ℝ) ≤ b * R

/-! ### Upstream module `MerLeanExperiment/IntervalCounts.lean` -/

/-- A positive-natural prefix has no extra endpoint error: its size is at
most the real upper endpoint itself. -/
theorem positive_prefix_card_le (A : Finset ℕ) (hA : ∀ n ∈ A, 0 < n)
    (H : ℝ) (hH : 0 ≤ H) :
    ((A.filter fun n : ℕ => (n : ℝ) ≤ H).card : ℝ) ≤ H := by
  let S := A.filter fun n : ℕ => (n : ℝ) ≤ H
  have hsub : S ⊆ Finset.Icc 1 ⌊H⌋₊ := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨hA n hn'.1, Nat.le_floor hn'.2⟩
  have hc : S.card ≤ (Finset.Icc 1 ⌊H⌋₊).card := Finset.card_le_card hsub
  have hfloor : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le hH
  have hIcc : (Finset.Icc 1 ⌊H⌋₊).card ≤ ⌊H⌋₊ := by
    rw [Nat.card_Icc]
    omega
  have hcard : (S.card : ℝ) ≤ (⌊H⌋₊ : ℝ) := by
    exact_mod_cast hc.trans hIcc
  exact hcard.trans hfloor

/-- Counts of the actual contiguous geometric regions telescope exactly. -/
theorem grid_middle_card_sum (A : Finset ℕ) (q : ℝ) (hq : 1 < q)
    (T : ℤ) (hT : 0 ≤ T) (R : ℝ) (hR : 0 ≤ R) :
    (∑ i ∈ Finset.Icc (-T) T,
      ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ)) =
        (intervalRegion A (q ^ (-T)) (q ^ (T + 1)) R).card := by
  let F : ℤ → Finset ℕ := fun i ↦ A.filter fun n : ℕ =>
    (n : ℝ) ≤ q ^ (i + 1) * R
  have hqpos : 0 < q := by linarith
  have hmono (i : ℤ) : F (i - 1) ⊆ F i := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨hn'.1, hn'.2.trans ?_⟩
    have hp : q ^ i ≤ q ^ (i + 1) := zpow_le_zpow_right₀ hq.le (by omega)
    rw [show i - 1 + 1 = i by omega]
    exact mul_le_mul_of_nonneg_right hp hR
  have hdiff (i : ℤ) : F i \ F (i - 1) =
      intervalRegion A (q ^ i) (q ^ (i + 1)) R := by
    ext n
    simp only [F, Finset.mem_sdiff, Finset.mem_filter, intervalRegion]
    have he : i - 1 + 1 = i := by omega
    rw [he]
    constructor
    · rintro ⟨⟨hnA, hnhi⟩, hnnot⟩
      exact ⟨hnA, lt_of_not_ge (fun hnle ↦ hnnot ⟨hnA, hnle⟩), hnhi⟩
    · rintro ⟨hnA, hnlo, hnhi⟩
      exact ⟨⟨hnA, hnhi⟩, fun hnprev ↦ (not_le_of_gt hnlo) hnprev.2⟩
  have htel := sum_Icc_backward_sub
    (fun i : ℤ ↦ ((F i).card : ℝ)) (-T) T (by omega)
  have hterms :
      (∑ i ∈ Finset.Icc (-T) T, ((F i \ F (i - 1)).card : ℝ)) =
        ∑ i ∈ Finset.Icc (-T) T,
          (((F i).card : ℝ) - ((F (i - 1)).card : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    have hc := Finset.card_sdiff_add_card_eq_card (hmono i)
    have hcR : (((F i \ F (i - 1)).card : ℝ) + ((F (i - 1)).card : ℝ)) =
        ((F i).card : ℝ) := by exact_mod_cast hc
    linarith
  have houterMono : F (-T - 1) ⊆ F T := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨hn'.1, hn'.2.trans ?_⟩
    have hp : q ^ (-T) ≤ q ^ (T + 1) :=
      zpow_le_zpow_right₀ hq.le (by omega)
    rw [show -T - 1 + 1 = -T by omega]
    exact mul_le_mul_of_nonneg_right hp hR
  have houter : F T \ F (-T - 1) =
      intervalRegion A (q ^ (-T)) (q ^ (T + 1)) R := by
    ext n
    simp only [F, Finset.mem_sdiff, Finset.mem_filter, intervalRegion]
    rw [show -T - 1 + 1 = -T by omega]
    constructor
    · rintro ⟨⟨hnA, hnhi⟩, hnnot⟩
      exact ⟨hnA, lt_of_not_ge (fun hnle ↦ hnnot ⟨hnA, hnle⟩), hnhi⟩
    · rintro ⟨hnA, hnlo, hnhi⟩
      exact ⟨⟨hnA, hnhi⟩, fun hnprev ↦ (not_le_of_gt hnlo) hnprev.2⟩
  have houterCard :
      (((F T).card : ℝ) - ((F (-T - 1)).card : ℝ)) =
        ((F T \ F (-T - 1)).card : ℝ) := by
    have hc := Finset.card_sdiff_add_card_eq_card houterMono
    have hcR : (((F T \ F (-T - 1)).card : ℝ) + ((F (-T - 1)).card : ℝ)) =
        ((F T).card : ℝ) := by exact_mod_cast hc
    linarith
  calc
    (∑ i ∈ Finset.Icc (-T) T,
        ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ)) =
      ∑ i ∈ Finset.Icc (-T) T, ((F i \ F (i - 1)).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hdiff]
    _ = ∑ i ∈ Finset.Icc (-T) T,
        (((F i).card : ℝ) - ((F (i - 1)).card : ℝ)) := hterms
    _ = ((F T).card : ℝ) - ((F (-T - 1)).card : ℝ) := by
      simpa using htel
    _ = ((F T \ F (-T - 1)).card : ℝ) := houterCard
    _ = ((intervalRegion A (q ^ (-T)) (q ^ (T + 1)) R).card : ℝ) := by
      rw [houter]

/-- The small prefix, middle interval, and strict tail form an exact
partition of the original finite set. -/
theorem three_region_card_partition (A : Finset ℕ) (H J : ℝ) (hHJ : H ≤ J) :
    A.card = (A.filter fun n : ℕ => (n : ℝ) ≤ H).card +
      (A.filter fun n : ℕ => H < (n : ℝ) ∧ (n : ℝ) ≤ J).card +
      (A.filter fun n : ℕ => J < (n : ℝ)).card := by
  let S := A.filter fun n : ℕ => (n : ℝ) ≤ H
  let M := A.filter fun n : ℕ => H < (n : ℝ) ∧ (n : ℝ) ≤ J
  let U := A.filter fun n : ℕ => J < (n : ℝ)
  have hunion : A = (S ∪ M) ∪ U := by
    ext n
    simp only [S, M, U, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hnA
      by_cases hnH : (n : ℝ) ≤ H
      · exact Or.inl (Or.inl ⟨hnA, hnH⟩)
      · by_cases hnJ : (n : ℝ) ≤ J
        · exact Or.inl (Or.inr ⟨hnA, lt_of_not_ge hnH, hnJ⟩)
        · exact Or.inr ⟨hnA, lt_of_not_ge hnJ⟩
    · rintro (hnSM | hnU)
      · rcases hnSM with hnS | hnM
        · exact hnS.1
        · exact hnM.1
      · exact hnU.1
  have hSM : Disjoint S M := by
    rw [Finset.disjoint_left]
    intro n hnS hnM
    simp only [S, M, Finset.mem_filter] at hnS hnM
    linarith
  have hSU : Disjoint S U := by
    rw [Finset.disjoint_left]
    intro n hnS hnU
    simp only [S, U, Finset.mem_filter] at hnS hnU
    linarith [hHJ]
  have hMU : Disjoint M U := by
    rw [Finset.disjoint_left]
    intro n hnM hnU
    simp only [M, U, Finset.mem_filter] at hnM hnU
    linarith
  have hSMU : Disjoint (S ∪ M) U := Finset.disjoint_union_left.mpr ⟨hSU, hMU⟩
  change A.card = S.card + M.card + U.card
  rw [hunion, Finset.card_union_of_disjoint hSMU,
    Finset.card_union_of_disjoint hSM]

/-! ### Upstream module `MerLeanExperiment/GridNormalization.lean` -/

/-- The unweighted count of the middle geometric range is bounded by its
weighted density sum. -/
theorem grid_middle_le_weighted_density (A : Finset ℕ) (q : ℝ) (hq : 1 < q)
    (L : ℕ) (T : ℤ) (hT : 0 ≤ T) (R : ℝ) (hR : 0 < R) :
    ((intervalRegion A (q ^ (-T)) (q ^ (T + 1)) R).card : ℝ) / R ≤
      ∑ i ∈ Finset.Icc (-T) T,
        gridBeta q L i * intervalDensity A (q ^ i) (q ^ (i + 1)) R := by
  classical
  have hq0 : 0 < q := by linarith
  have heta : 0 ≤ gridEta := (grid_ratio_spec 1 le_rfl).2.2.2.le
  have hwidth (i : ℤ) : q ^ (i + 1) - q ^ i = q ^ i * (q - 1) := by
    rw [zpow_add_one₀ hq0.ne']
    ring
  have hwidth_pos (i : ℤ) : 0 < q ^ i * (q - 1) :=
    mul_pos (zpow_pos hq0 i) (sub_pos.mpr hq)
  have hdensity (i : ℤ) :
      intervalDensity A (q ^ i) (q ^ (i + 1)) R =
        ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ) /
          ((q ^ i * (q - 1)) * R) := by
    unfold intervalDensity intervalRegion
    rw [hwidth]
  have hcancel (i : ℤ) :
      (q ^ i * (q - 1)) * intervalDensity A (q ^ i) (q ^ (i + 1)) R =
        ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ) / R := by
    rw [hdensity]
    field_simp [hq0.ne', (sub_pos.mpr hq).ne', hR.ne']
  have hrow (i : ℤ) :
      ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ) / R ≤
        gridBeta q L i * intervalDensity A (q ^ i) (q ^ (i + 1)) R := by
    by_cases hi : i < (L : ℤ)
    · rw [gridBeta, if_pos hi, hcancel]
    · rw [gridBeta, if_neg hi]
      have hc : 0 ≤ ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ) / R :=
        div_nonneg (Nat.cast_nonneg _) hR.le
      calc
        ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ) / R ≤
            (1 + gridEta) *
              (((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ) / R) := by
                nlinarith [mul_nonneg heta hc]
        _ = (1 + gridEta) * q ^ i * (q - 1) *
              intervalDensity A (q ^ i) (q ^ (i + 1)) R := by
                rw [← hcancel i]
                ring
  calc
    ((intervalRegion A (q ^ (-T)) (q ^ (T + 1)) R).card : ℝ) / R =
        (∑ i ∈ Finset.Icc (-T) T,
          ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ)) / R := by
            rw [grid_middle_card_sum A q hq T hT R hR.le]
    _ = ∑ i ∈ Finset.Icc (-T) T,
          ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ) / R := by
            rw [Finset.sum_div]
    _ ≤ ∑ i ∈ Finset.Icc (-T) T,
          gridBeta q L i * intervalDensity A (q ^ i) (q ^ (i + 1)) R := by
            exact Finset.sum_le_sum fun i _ ↦ hrow i

/-- The geometric scale identity iterates over a natural block count. -/
theorem grid_scale_power (q : ℝ) (L S : ℕ)
    (hq2L : q ^ (2 * (L : ℤ)) = 2) :
    q ^ (2 * (L : ℤ) * (S : ℤ)) = (2 : ℝ) ^ S := by
  rw [zpow_mul, hq2L, zpow_natCast]

/-- The square-root constant used at the endpoint of the grid estimate. -/
theorem sqrt_nine_eighth :
    Real.sqrt (9 / 8 : ℝ) = 3 * Real.sqrt 2 / 4 := by
  have hleft : 0 ≤ Real.sqrt (9 / 8 : ℝ) := Real.sqrt_nonneg _
  have hright : 0 ≤ 3 * Real.sqrt 2 / 4 := by positivity
  have hleft_sq : (Real.sqrt (9 / 8 : ℝ)) ^ 2 = 9 / 8 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

/-! ### Upstream module `MerLeanExperiment/TailBound.lean` -/

/-- The integer reciprocal quotients distinguish all members of an admissible set. -/
theorem lcm_quotient_injective (N : ℕ) (A : Finset ℕ) (hA : LcmBounded N A) :
    Set.InjOn (fun a => N / a) (A : Set ℕ) := by
  have hneq (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) (hab : a < b) :
      N / a ≠ N / b := by
    intro heq
    have ha0 : 0 < a := (Finset.mem_Icc.mp (hA.1 ha)).1
    have hb0 : 0 < b := lt_trans ha0 hab
    have hg : Nat.gcd a b ≤ b - a := Nat.le_of_dvd (Nat.sub_pos_of_lt hab)
      (Nat.dvd_sub (Nat.gcd_dvd_right a b) (Nat.gcd_dvd_left a b))
    have hprod : a * b ≤ N * (b - a) := by
      calc
        a * b = Nat.gcd a b * Nat.lcm a b := (Nat.gcd_mul_lcm a b).symm
        _ ≤ (b - a) * N := Nat.mul_le_mul hg (hA.2 a ha b hb)
        _ = N * (b - a) := Nat.mul_comm _ _
    have hlow : (N / a) * b ≤ N := by
      rw [heq]
      exact Nat.div_mul_le_self N b
    have hhigh : N < a * (N / a + 1) := Nat.lt_mul_div_succ N ha0
    have hlow' := Nat.mul_le_mul_right a hlow
    have hhigh' := Nat.mul_lt_mul_of_pos_right hhigh hb0
    have hsub : b - a + a = b := Nat.sub_add_cancel (le_of_lt hab)
    nlinarith
  intro a ha b hb heq
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim (hneq a b ha hb hab heq)
  · exact hab
  · exact False.elim (hneq b a hb ha hab heq.symm)

/-- A positive integral cutoff gives a finite reciprocal-quotient count. -/
theorem lcm_tail_nat_bound (N K : ℕ) (A : Finset ℕ) (hA : LcmBounded N A)
    (hK : 0 < K) : (A.filter fun a => K ≤ a).card ≤ N / K := by
  let B := A.filter fun a => K ≤ a
  have hinj : Set.InjOn (fun a => N / a) (B : Set ℕ) :=
    (lcm_quotient_injective N A hA).mono (Finset.filter_subset _ _)
  have hsub : B.image (fun a => N / a) ⊆ Finset.Icc 1 (N / K) := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    have haA := (Finset.mem_filter.mp ha).1
    have hKa := (Finset.mem_filter.mp ha).2
    have haN := (Finset.mem_Icc.mp (hA.1 haA)).2
    have ha0 : 0 < a := lt_of_lt_of_le hK hKa
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.div_pos haN ha0
    · exact Nat.div_le_div_left hKa hK
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hcard
  simpa using hcard

/-- A uniform tail bound, with no dyadic decomposition or rounding error. -/
theorem lcm_tail_bound (N : ℕ) (A : Finset ℕ) (hA : LcmBounded N A)
    (H : ℝ) (hH : 0 < H) :
    ((A.filter fun a : ℕ => H < (a : ℝ)).card : ℝ) ≤ (N : ℝ) / H := by
  let K := ⌊H⌋₊ + 1
  have hK : 0 < K := Nat.zero_lt_succ _
  have hHK : H < (K : ℝ) := by simpa [K] using Nat.lt_floor_add_one H
  have heq : (A.filter fun a : ℕ => H < (a : ℝ)) = A.filter fun a => K ≤ a := by
    ext a
    simp only [Finset.mem_filter, K, Nat.add_one_le_iff,
      Nat.floor_lt (le_of_lt hH)]
  rw [heq]
  have hcount := lcm_tail_nat_bound N K A hA hK
  have hdiv := Nat.div_mul_le_self N K
  have hcast : ((N / K : ℕ) : ℝ) * (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdiv
  have hc : ((A.filter fun a => K ≤ a).card : ℝ) ≤ ((N / K : ℕ) : ℝ) := by
    exact_mod_cast hcount
  apply (le_div_iff₀ hH).mpr
  have hc0 : (0 : ℝ) ≤ (A.filter fun a => K ≤ a).card := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hc hK0,
    mul_le_mul_of_nonneg_left (le_of_lt hHK) hc0]

/-! ### Upstream module `MerLeanExperiment/ConcreteUpper.lean` -/

theorem eventually_concrete_upper : ∃ L0 : ℕ, 1 ≤ L0 ∧ ∀ L ≥ L0, ∀ S : ℕ,
    1 ≤ S → ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ N ≥ N0, ∀ A : Finset ℕ, LcmBounded N A →
        (A.card : ℝ) ≤ (Real.sqrt (9 / 8 : ℝ) + (1 - gridQ L ^ (-1 : ℤ)) +
          (1 / 2 : ℝ) ^ S + epsilon * (Real.sqrt (9 / 8 : ℝ) + 1)) *
            Real.sqrt (N : ℝ) := by
  classical
  obtain ⟨L0, hL0, hweighted⟩ := eventually_weighted_grid_packing
  refine ⟨L0, hL0, ?_⟩
  intro L hL S hS epsilon hepsilon
  have hLone : 1 ≤ L := hL0.trans hL
  obtain ⟨hq, hqL, hq2L, _⟩ := grid_ratio_spec L hLone
  let q := gridQ L
  have hqp : 0 < q := by dsimp [q]; linarith
  let T : ℤ := 2 * (L : ℤ) * (S : ℤ) - 1
  have hLI : (1 : ℤ) ≤ L := by exact_mod_cast hLone
  have hSI : (1 : ℤ) ≤ S := by exact_mod_cast hS
  have hT : (L : ℤ) - 1 ≤ T := by
    dsimp [T]
    nlinarith
  have hT0 : 0 ≤ T := by omega
  have hscale : q ^ (T + 1) = (2 : ℝ) ^ S := by
    dsimp only [T]
    rw [sub_add_cancel]
    exact grid_scale_power q L S hq2L
  obtain ⟨NW, hW⟩ := hweighted L hL T hT epsilon hepsilon
  refine ⟨max 1 NW, le_max_left _ _, ?_⟩
  intro N hN A hA
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNW : NW ≤ N := (le_max_right _ _).trans hN
  let R := Real.sqrt (N : ℝ)
  have hR : 0 < R := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))
  have hR2 : R ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  let c : ℝ := Real.sqrt (9 / 8 : ℝ)
  let D : ℝ := ∑ j ∈ Finset.Icc (-T) (L : ℤ), gridDelta q L j
  have hD : D = c - q ^ (-T) + 1 - q ^ (-1 : ℤ) := by
    dsimp [D, c]
    rw [grid_delta_sum q hq L hLone hqL T hT0, sqrt_nine_eighth]
  have hDle : D ≤ c + 1 := by
    rw [hD]
    have h1 := zpow_pos hqp (-T)
    have h2 := zpow_pos hqp (-1)
    linarith
  have hsmall := positive_prefix_card_le A
    (fun n hn => by have := (Finset.mem_Icc.mp (hA.1 hn)).1; omega)
    (q ^ (-T) * R) (mul_pos (zpow_pos hqp _) hR).le
  have hmiddle : ((intervalRegion A (q ^ (-T)) (q ^ (T + 1)) R).card : ℝ) ≤
      ((1 + epsilon) * D) * R := by
    apply (div_le_iff₀ hR).mp
    exact (grid_middle_le_weighted_density A q hq L T hT0 R hR).trans (hW N hNW A hA)
  have htail := lcm_tail_bound N A hA (q ^ (T + 1) * R)
    (mul_pos (zpow_pos hqp _) hR)
  have htailval : (N : ℝ) / (q ^ (T + 1) * R) = (1 / 2 : ℝ) ^ S * R := by
    rw [hscale, ← hR2]
    calc
      _ = (1 / (2 : ℝ) ^ S) * R := by field_simp
      _ = _ := by rw [div_pow, one_pow]
  rw [htailval] at htail
  have hHJ : q ^ (-T) * R ≤ q ^ (T + 1) * R :=
    mul_le_mul_of_nonneg_right (zpow_le_zpow_right₀ hq.le (by omega)) hR.le
  have hpart : (A.card : ℝ) =
      ((A.filter fun n : ℕ => (n : ℝ) ≤ q ^ (-T) * R).card : ℝ) +
      ((intervalRegion A (q ^ (-T)) (q ^ (T + 1)) R).card : ℝ) +
      ((A.filter fun n : ℕ => q ^ (T + 1) * R < (n : ℝ)).card : ℝ) := by
    exact_mod_cast three_region_card_partition A (q ^ (-T) * R) (q ^ (T + 1) * R) hHJ
  have heD := mul_le_mul_of_nonneg_left hDle hepsilon.le
  calc
    (A.card : ℝ) ≤ q ^ (-T) * R + ((1 + epsilon) * D) * R + (1 / 2 : ℝ) ^ S * R := by
      rw [hpart]
      exact add_le_add (add_le_add hsmall hmiddle) htail
    _ = (q ^ (-T) + D + (1 / 2 : ℝ) ^ S + epsilon * D) * R := by ring
    _ ≤ (q ^ (-T) + D + (1 / 2 : ℝ) ^ S + epsilon * (c + 1)) * R := by
      apply mul_le_mul_of_nonneg_right _ hR.le
      linarith
    _ = _ := by rw [hD]; dsimp only [q, c, R]; ring

/-! ### Upstream module `MerLeanExperiment/UpperBound.lean` -/

theorem chen_uniform_upper : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ A : Finset ℕ, LcmBounded N A →
      (A.card : ℝ) ≤ (Real.sqrt (9 / 8 : ℝ) + ε) * Real.sqrt N := by
  intro epsilon hepsilon
  obtain ⟨L0, hL0, hconcrete⟩ := eventually_concrete_upper
  have hgap : Filter.Tendsto (fun L : ℕ => 1 - gridQ L ^ (-1 : ℤ))
      Filter.atTop (nhds (0 : ℝ)) := by
    have hh := (gridQ_tendsto_one.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).const_sub 1
    simpa only [inv_one, sub_self, zpow_neg_one] using hh
  have hpower : Filter.Tendsto (fun S : ℕ => (1 / 2 : ℝ) ^ S)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨NL, hNL⟩ := Filter.eventually_atTop.mp
    (hgap.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < epsilon / 3)))
  obtain ⟨NS, hNS⟩ := Filter.eventually_atTop.mp
    (hpower.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < epsilon / 3)))
  let L := max L0 NL
  let S := max 1 NS
  let c : ℝ := Real.sqrt (9 / 8 : ℝ)
  have hc : 0 < c + 1 := by dsimp [c]; positivity
  let rho : ℝ := epsilon / (3 * (c + 1))
  have hrho : 0 < rho := div_pos hepsilon (by positivity)
  have hrhoc : rho * (c + 1) = epsilon / 3 := by
    dsimp [rho]
    field_simp
  obtain ⟨N0, _, hN0⟩ := hconcrete L (le_max_left _ _) S (le_max_left _ _) rho hrho
  refine ⟨N0, ?_⟩
  intro N hN A hA
  have hbound := hN0 N hN A hA
  have hgl := hNL L (le_max_right _ _)
  have hps := hNS S (le_max_right _ _)
  have hcoef : c + (1 - gridQ L ^ (-1 : ℤ)) + (1 / 2 : ℝ) ^ S + rho * (c + 1) ≤
      c + epsilon := by
    rw [hrhoc]
    change 1 - gridQ L ^ (-1 : ℤ) < epsilon / 3 at hgl
    change (1 / 2 : ℝ) ^ S < epsilon / 3 at hps
    linarith
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _))

/-! ### Upstream module `MerLeanExperiment/LowerBound.lean` -/

private theorem g_mono {m n : ℕ} (hmn : m ≤ n) : g m ≤ g n := by
  obtain ⟨A, hA, hcard⟩ := exists_extremal m
  rw [← hcard]
  apply card_le_g
  constructor
  · intro x hx
    have hx' := Finset.mem_Icc.mp (hA.1 hx)
    exact Finset.mem_Icc.mpr ⟨hx'.1, hx'.2.trans hmn⟩
  · intro x hx y hy
    exact (hA.2 x hx y hy).trans hmn

/-- A uniform squared lower bound for the Erdős extremal function. -/
theorem lower_squared_bound (N : ℕ) :
    9 * N ≤ 8 * (g N + 11) ^ 2 := by
  let s := Nat.sqrt (N / 72)
  have hs_upper : N / 72 < (s + 1) ^ 2 := by
    simpa [s] using Nat.lt_succ_sqrt' (N / 72)
  have hmod : N % 72 < 72 := Nat.mod_lt N (by norm_num)
  have hdivmod := Nat.div_add_mod N 72
  have hN_upper : N < 72 * (s + 1) ^ 2 := by omega
  by_cases hs0 : s = 0
  · simp [hs0] at hN_upper
    have hg11 : 11 ≤ g N + 11 := by omega
    have hsq := Nat.pow_le_pow_left hg11 2
    calc
      9 * N ≤ 9 * 71 := by omega
      _ ≤ 8 * 11 ^ 2 := by norm_num
      _ ≤ 8 * (g N + 11) ^ 2 := Nat.mul_le_mul_left 8 hsq
  · have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0
    let t := s - 1
    have hs_lower : s ^ 2 ≤ N / 72 := by
      simpa [s] using Nat.sqrt_le' (N / 72)
    have h72 : 72 * s ^ 2 ≤ N := by
      calc
        72 * s ^ 2 ≤ 72 * (N / 72) := Nat.mul_le_mul_left 72 hs_lower
        _ = (N / 72) * 72 := by ring
        _ ≤ N := Nat.div_mul_le_self N 72
    have hfamily : familyN t ≤ N := by
      have hform : familyN t = 2 * (6 * s - 2) ^ 2 := by
        simp [familyN, familyK, t]
        omega
      rw [hform]
      calc
        2 * (6 * s - 2) ^ 2 ≤ 2 * (6 * s) ^ 2 :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.sub_le _ _) 2)
        _ = 72 * s ^ 2 := by ring
        _ ≤ N := h72
    have hfamily_g : g (familyN t) ≤ g N := g_mono hfamily
    have hsource := nine_mul_add_seven_le_g_familyN t
    have hlow : 9 * t + 7 ≤ g N := hsource.trans hfamily_g
    have hg : 9 * (s + 1) ≤ g N + 11 := by
      dsimp [t] at hlow
      omega
    have hsq := Nat.pow_le_pow_left hg 2
    have hscaled : 9 * N < 8 * (9 * (s + 1)) ^ 2 := by
      calc
        9 * N < 9 * (72 * (s + 1) ^ 2) :=
          Nat.mul_lt_mul_of_pos_left hN_upper (by norm_num)
        _ = 8 * (9 * (s + 1)) ^ 2 := by ring
    exact (Nat.le_of_lt hscaled).trans (Nat.mul_le_mul_left 8 hsq)

/-! ### Upstream module `MerLeanExperiment/Asymptotic.lean` -/

/-- Chen's sharp asymptotic for the Erdős 441 extremal function. -/
theorem chen_asymptotic :
    Filter.Tendsto (fun N : ℕ => (g N : ℝ) / Real.sqrt ((9 / 8 : ℝ) * N))
      Filter.atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  let c : ℝ := Real.sqrt (9 / 8 : ℝ)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hc2 : c ^ 2 = 9 / 8 := by
    dsimp [c]
    exact Real.sq_sqrt (by norm_num)
  obtain ⟨NU, hNU⟩ := chen_uniform_upper (epsilon * c / 2) (by positivity)
  let B : ℝ := 22 / (epsilon * c)
  let N0 : ℕ := max NU (max 1 ⌈B ^ 2⌉₊)
  refine ⟨N0, ?_⟩
  intro N hN
  have hNU_N : NU ≤ N := by
    dsimp [N0] at hN
    omega
  have hN1 : 1 ≤ N := by
    dsimp [N0] at hN
    omega
  have hNpos : 0 < N := by omega
  let R : ℝ := Real.sqrt (N : ℝ)
  have hR : 0 < R := by
    dsimp [R]
    exact Real.sqrt_pos.mpr (by exact_mod_cast hNpos)
  have hR2 : R ^ 2 = (N : ℝ) := by
    dsimp [R]
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hBsq : B ^ 2 ≤ (N : ℝ) :=
    (Nat.le_ceil (B ^ 2)).trans
      (Nat.cast_le.mpr (by dsimp [N0] at hN; omega))
  have hBR : B ≤ R := by nlinarith
  have hlarge : 22 ≤ epsilon * c * R := by
    calc
      (22 : ℝ) = epsilon * c * B := by
        dsimp [B]
        field_simp [hepsilon.ne', hc.ne']
      _ ≤ epsilon * c * R :=
        mul_le_mul_of_nonneg_left hBR (mul_pos hepsilon hc).le
  obtain ⟨A, hA, hcard⟩ := exists_extremal N
  have hu := hNU N hNU_N A hA
  rw [hcard] at hu
  have hupper : (g N : ℝ) ≤ (c + epsilon * c / 2) * R := by
    simpa only [c, R] using hu
  have hlNat := lower_squared_bound N
  have hl : (9 : ℝ) * N ≤ 8 * ((g N : ℝ) + 11) ^ 2 := by
    exact_mod_cast hlNat
  have hcR2 : (c * R) ^ 2 = (9 / 8 : ℝ) * N := by
    rw [mul_pow, hc2, hR2]
  have hsquares : (c * R) ^ 2 ≤ ((g N : ℝ) + 11) ^ 2 := by
    nlinarith
  have hlower : c * R ≤ (g N : ℝ) + 11 := by
    have hg0 : 0 ≤ (g N : ℝ) + 11 := by positivity
    have hcR0 : 0 ≤ c * R := (mul_pos hc hR).le
    nlinarith
  have hden : 0 < c * R := mul_pos hc hR
  have hratioLower : 1 - epsilon / 2 ≤ (g N : ℝ) / (c * R) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have hratioUpper : (g N : ℝ) / (c * R) ≤ 1 + epsilon / 2 := by
    apply (div_le_iff₀ hden).2
    calc
      (g N : ℝ) ≤ (c + epsilon * c / 2) * R := hupper
      _ = (1 + epsilon / 2) * (c * R) := by ring
  have hsqrt : Real.sqrt ((9 / 8 : ℝ) * N) = c * R := by
    dsimp [c, R]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9 / 8)]
  rw [hsqrt, Real.dist_eq]
  rw [abs_lt]
  constructor <;> linarith

/-! ### Upstream module `MerLeanExperiment/Target.lean` -/

/-- The complete two-part statement of Erdős problem 441. -/
theorem erdos_441 :
    Filter.Tendsto (fun N : ℕ => (g N : ℝ) / Real.sqrt ((9 / 8 : ℝ) * N))
      Filter.atTop (nhds 1) ∧
    ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ (erdosConstruction N).card < g N := by
  exact ⟨chen_asymptotic, erdosConstruction_not_eventually_extremal⟩

#print axioms erdos_441
-- 'Erdos441.erdos_441' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos441
