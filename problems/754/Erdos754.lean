import Mathlib

namespace Erdos754

/-
# Erdős Problem 754

Let $f(n)$ be maximal such that there exists a set $A$ of $n$ points in $\mathbb{R}^4$ in which
every $x\in A$ has at least $f(n)$ points in $A$ equidistant from $x$. Is it true that
$f(n)\leq \frac{n}{2}+O(1)$?

The answer is **yes**, proved by Swanepoel [Sw13] (`erdos_754_upper`, with the explicit constant
$202$). Together with the lower bounds of Avis, Erdős and Pach [AEP88], $\lfloor n/2 \rfloor
\leq f(n)$ for every $n$ and $n/2 + 2 \leq f(n)$ whenever $8 \mid n$, this gives
$f(n) = n/2 + O(1)$; `erdos_754` states all three bounds. Points live in
`EuclideanSpace ℝ (Fin 4)`, and the common distance at each point is allowed to depend on that
point.

Formalised by Collin Yuanjie Ren in `CollinYuanjieRen/awards` (submission JSP-000620), which
proves the lower bounds and vendors the upper bound from `plby/lean-proofs`
(`ErdosProblems/Erdos754.lean` and `Erdos755.lean`). The five modules forming the closure are
flattened here in dependency order. plby's final theorem is renamed `erdos_754_upper`.
`erdos_754` is added here: it restates upstream's `erdos_754_two_sided`, and adds no
mathematical content.

Declarations that `erdos_754` does not depend on have been removed.
-/

universe u

/-! ### Upstream module `JSP620/External/Erdos755.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 755.
https://www.erdosproblems.com/forum/thread/755

Informal authors:
- Frank Clemen
- Adrian Dumitrescu
- Ding Liu

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos755.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/755.lean
-/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-!
# Erdős Problem 755

The mathematical proof and the correspondence between its lemmas and the
formal development are documented in `tex/755.tex`.
-/

open scoped BigOperators EuclideanGeometry _root_.Asymptotics RealInnerProductSpace _root_.SimpleGraph

namespace Erdos755

/-! ## The unit-distance graph and the finite maximum -/

/-! ## Euclidean core lemmas -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Three distinct points at a common distance from one center are affinely independent. -/
theorem affineIndependent_fin3_of_equidistant
    (f : Fin 3 → E) (hf : Function.Injective f) (center : E) (radius : ℝ)
    (h : ∀ i, dist (f i) center = radius) :
    AffineIndependent ℝ f := by
  apply EuclideanGeometry.Cospherical.affineIndependent (s := Set.range f)
  · exact ⟨center, radius, by rintro _ ⟨i, rfl⟩; exact h i⟩
  · exact Set.Subset.rfl
  · exact hf

/-- The affine direction space of three distinct cospherical points has dimension two. -/
theorem finrank_vectorSpan_fin3_of_equidistant
    (f : Fin 3 → E) (hf : Function.Injective f) (center : E) (radius : ℝ)
    (h : ∀ i, dist (f i) center = radius) :
    Module.finrank ℝ (vectorSpan ℝ (Set.range f)) = 2 := by
  exact (affineIndependent_fin3_of_equidistant f hf center radius h).finrank_vectorSpan
    (by norm_num)

/-- Constant cross-distance makes the two affine direction spaces orthogonal. -/
theorem vectorSpan_range_isOrtho_of_cross_dist_eq
    {ι κ : Type*} [Nonempty ι] [Nonempty κ]
    (f : ι → E) (g : κ → E) (radius : ℝ)
    (h : ∀ i j, dist (f i) (g j) = radius) :
    vectorSpan ℝ (Set.range f) ⟂ vectorSpan ℝ (Set.range g) := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  let j₀ : κ := Classical.choice inferInstance
  rw [vectorSpan_range_eq_span_range_vsub_right ℝ f i₀,
    vectorSpan_range_eq_span_range_vsub_right ℝ g j₀, Submodule.isOrtho_span]
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  apply EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq
  · simpa [dist_comm] using (h i₀ j₀).trans (h i₀ j).symm
  · simpa [dist_comm] using (h i j₀).trans (h i j).symm

/-! ## The global geometric obstruction -/

/-! ## The geometric obstruction in every link -/

lemma inner_eq_zero_of_mem_orthogonal_spans
    {I J : Type*} {u : I → E} {v : J → E}
    (horth : ∀ i j, ⟪u i, v j⟫ = 0) {x y : E}
    (hx : x ∈ Submodule.span ℝ (Set.range u))
    (hy : y ∈ Submodule.span ℝ (Set.range v)) : ⟪x, y⟫ = 0 := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb => obtain ⟨j, rfl⟩ := hb; exact horth i j
    | zero => simp
    | add y z _ _ hy hz => simp [inner_add_right, hy, hz]
    | smul c y _ hy => simp only [inner_smul_right, hy, mul_zero]
  | zero => simp
  | add x z _ _ hx hz => simp [inner_add_left, hx, hz]
  | smul c x _ hx => simp only [inner_smul_left, hx, mul_zero]

/-! ## Edge Erdős--Stone in the two forms used below -/

/-! ## Choosing an extremal configuration for each order -/

/-! ## The numerical local-to-global deduction -/

/-! ## Graph double counting -/

/-! ## Combining geometry, extremal graph theory, and double counting -/

end Erdos755

end

/-! ### Upstream module `JSP620/External/Erdos754.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 754.
https://www.erdosproblems.com/forum/thread/754

Informal authors:
- Konrad J. Swanepoel

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos754.md
-/
/- JSP-000620 submission note: this file is a verbatim copy of plby/lean-proofs commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e, src/latest/ErdosProblems/Erdos754.lean (Apache-2.0,
header above retained). The only change is the module name in the next import line. -/

open scoped BigOperators EuclideanGeometry RealInnerProductSpace
open _root_.Finset

variable {V : Type u}

/-! ## Finite averages used by dependent random choice -/

noncomputable def indicator (P : Prop) : ℝ :=
  @ite ℝ P (Classical.propDecidable P) 1 0

@[simp] lemma indicator_true {P : Prop} (h : P) : indicator P = 1 := by
  simp [indicator, h]

@[simp] lemma indicator_false {P : Prop} (h : ¬ P) : indicator P = 0 := by
  simp [indicator, h]

lemma indicator_nonneg (P : Prop) : 0 ≤ indicator P := by
  unfold indicator
  split_ifs <;> norm_num

lemma sum_indicator_eq_card_filter (s : Finset V) (p : V → Prop) [DecidablePred p] :
    ∑ x ∈ s, indicator (p x) = ((s.filter p).card : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [sum_insert ha, ih, filter_insert]
      by_cases hp : p a
      · rw [indicator_true hp]
        simp [ha, hp]
        ring
      · rw [indicator_false hp]
        simp [hp]

noncomputable def samples (t : ℕ) (A : Finset V) : Finset (Fin t → V) :=
  Fintype.piFinset fun _ => A

lemma card_samples (t : ℕ) (A : Finset V) : (samples t A).card = A.card ^ t := by
  simp [samples]

noncomputable def commonNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (q : ι → V) (B : Finset V) : Finset V :=
  B.filter fun y => ∀ i, G.Adj (q i) y

lemma mem_commonNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (q : ι → V) (B : Finset V) (y : V) :
    y ∈ commonNeighbors G q B ↔ y ∈ B ∧ ∀ i, G.Adj (q i) y := by
  simp [commonNeighbors]

lemma commonNeighbors_subset_target (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (q : ι → V) (B : Finset V) :
    commonNeighbors G q B ⊆ B := by
  intro y hy
  exact (mem_commonNeighbors G q B y).mp hy |>.1

lemma card_commonNeighbors_eq_sum_indicator
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (q : ι → V) (B : Finset V) :
    ((commonNeighbors G q B).card : ℝ) =
      ∑ y ∈ B, indicator (∀ i, G.Adj (q i) y) := by
  classical
  rw [sum_indicator_eq_card_filter]
  rfl

lemma expect_all_adjacent
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (t : ℕ) (y : V) :
    𝔼 x ∈ samples t A, indicator (∀ i, G.Adj (x i) y) =
      (((A.filter fun z => G.Adj z y).card : ℝ) / A.card) ^ t := by
  classical
  have hsingle :
      𝔼 z ∈ A, indicator (G.Adj z y) =
        ((A.filter fun z => G.Adj z y).card : ℝ) / A.card := by
    rw [Finset.expect_eq_sum_div_card]
    rw [sum_indicator_eq_card_filter]
  calc
    𝔼 x ∈ samples t A, indicator (∀ i, G.Adj (x i) y) =
        𝔼 x ∈ samples t A, ∏ i, indicator (G.Adj (x i) y) := by
          apply Finset.expect_congr rfl
          intro x hx
          by_cases h : ∀ i, G.Adj (x i) y
          · rw [indicator_true h]
            exact (Finset.prod_eq_one fun i _ => indicator_true (h i)).symm
          · rw [indicator_false h]
            push Not at h
            obtain ⟨i, hi⟩ := h
            exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_false hi)).symm
    _ = (𝔼 z ∈ A, indicator (G.Adj z y)) ^ t := by
      symm
      simpa [samples] using (Finset.expect_pow A (fun z => indicator (G.Adj z y)) t)
    _ = (((A.filter fun z => G.Adj z y).card : ℝ) / A.card) ^ t := by rw [hsingle]

lemma expect_card_commonNeighbors
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (t : ℕ) :
    𝔼 x ∈ samples t A, ((commonNeighbors G x B).card : ℝ) =
      ∑ y ∈ B, (((A.filter fun z => G.Adj z y).card : ℝ) / A.card) ^ t := by
  classical
  simp_rw [card_commonNeighbors_eq_sum_indicator]
  rw [Finset.expect_sum_comm]
  congr 1
  funext y
  exact expect_all_adjacent G A t y

def edgeMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : ℕ :=
  ∑ y ∈ B, (A.filter fun z => G.Adj z y).card

lemma sum_degree_ratios
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    ∑ y ∈ B, ((A.filter fun z => G.Adj z y).card : ℝ) / A.card =
      edgeMass G A B / A.card := by
  classical
  simp only [edgeMass, Nat.cast_sum]
  rw [Finset.sum_div]

lemma pow_expect_le_expect_pow {ι : Type*} (S : Finset ι)
    (hS : S.Nonempty) (g : ι → ℝ) (hg : ∀ x ∈ S, 0 ≤ g x) (t : ℕ) :
    (𝔼 x ∈ S, g x) ^ t ≤ 𝔼 x ∈ S, (g x) ^ t := by
  classical
  let w : ι → ℝ := fun _ => (S.card : ℝ)⁻¹
  have hw : ∀ x ∈ S, 0 ≤ w x := fun _ _ => by positivity
  have hw_sum : ∑ x ∈ S, w x = 1 := by simp [w, hS.card_ne_zero]
  have hJ := Real.pow_arith_mean_le_arith_mean_pow S w g hw hw_sum hg t
  simpa [Finset.expect, NNRat.smul_def, w, div_eq_inv_mul, ← Finset.mul_sum] using hJ

lemma samples_nonempty (t : ℕ) {A : Finset V} (hA : A.Nonempty) :
    (samples t A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  refine ⟨fun _ => a, ?_⟩
  simp [samples, ha]

lemma expect_card_commonNeighbors_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdensity : ρ * A.card * B.card ≤ edgeMass G A B)
    (t : ℕ) :
    (ρ ^ t) * B.card ≤
      𝔼 x ∈ samples t A, ((commonNeighbors G x B).card : ℝ) := by
  classical
  let g : V → ℝ := fun y => ((A.filter fun z => G.Adj z y).card : ℝ) / A.card
  have hg : ∀ y ∈ B, 0 ≤ g y := fun _ _ => by positivity
  have hmean : ρ ≤ 𝔼 y ∈ B, g y := by
    rw [Finset.expect_eq_sum_div_card,
      show (∑ y ∈ B, g y) = edgeMass G A B / A.card by exact sum_degree_ratios G A B]
    have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    have hBpos : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
    rw [div_div]
    apply (le_div_iff₀ (mul_pos hApos hBpos)).2
    simpa [mul_assoc] using hdensity
  have hjensen := pow_expect_le_expect_pow B hB g hg t
  have hpow : ρ ^ t ≤ 𝔼 y ∈ B, (g y) ^ t :=
    (pow_le_pow_left₀ hρ hmean t).trans hjensen
  rw [expect_card_commonNeighbors G A B t]
  rw [Finset.expect_eq_sum_div_card] at hpow
  apply (le_div_iff₀ (by exact_mod_cast hB.card_pos)).mp at hpow
  simpa [g, mul_comm] using hpow

/- Compatibility abbreviations keep the finite-average proof below readable while
the file remains independent of the unrelated Erdős 163 development. -/
namespace DRC
noncomputable abbrev indicator (P : Prop) : ℝ := Erdos754.indicator P

@[simp] lemma indicator_true {P : Prop} (h : P) : indicator P = 1 := by
  simp [indicator, Erdos754.indicator, h]

lemma indicator_nonneg (P : Prop) : 0 ≤ indicator P := by
  simpa [indicator] using Erdos754.indicator_nonneg P

lemma sum_indicator_eq_card_filter (s : Finset V) (p : V → Prop) [DecidablePred p] :
    ∑ x ∈ s, indicator (p x) = ((s.filter p).card : ℝ) := by
  simpa [indicator] using Erdos754.sum_indicator_eq_card_filter s p

abbrev edgeMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : ℕ := Erdos754.edgeMass G A B

abbrev expect_card_commonNeighbors_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdensity : ρ * A.card * B.card ≤ Erdos754.edgeMass G A B)
    (t : ℕ) :
    (ρ ^ t) * B.card ≤
      𝔼 x ∈ Erdos754.samples t A,
        ((Erdos754.commonNeighbors G x B).card : ℝ) :=
  Erdos754.expect_card_commonNeighbors_lower G hA hB hρ hdensity t

abbrev samples_nonempty (t : ℕ) {A : Finset V} (hA : A.Nonempty) :
    (Erdos754.samples t A).Nonempty := Erdos754.samples_nonempty t hA
end DRC

namespace FiniteDefect
noncomputable abbrev samples (t : ℕ) (A : Finset V) : Finset (Fin t → V) :=
  Erdos754.samples t A

noncomputable abbrev commonNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (q : ι → V) (B : Finset V) : Finset V :=
  Erdos754.commonNeighbors G q B
end FiniteDefect

variable [Fintype V]

lemma expect_eq01 (hV : Nonempty V) :
    (𝔼 q ∈ FiniteDefect.samples 3 (Finset.univ : Finset V),
      indicator (q 0 = q 1)) = 1 / (Fintype.card V : ℝ) := by
  classical
  rw [Finset.expect_eq_sum_div_card, sum_indicator_eq_card_filter,
    card_samples]
  simp only [Finset.card_univ]
  have hn : Fintype.card V ≠ 0 := Fintype.card_ne_zero
  have hsamples : (samples 3 (Finset.univ : Finset V)).filter
      (fun q => q 0 = q 1) = Finset.univ.filter (fun q : Fin 3 → V => q 0 = q 1) := by
    ext q; simp [samples]
  have hfilter : (Finset.univ.filter (fun q : Fin 3 → V => q 0 = q 1)).card =
      Fintype.card V ^ 2 := by
    rw [← Fintype.card_coe]
    let e : {q : Fin 3 → V // q 0 = q 1} ≃ V × V := {
      toFun q := (q.1 0, q.1 2)
      invFun z := ⟨![z.1, z.1, z.2], by simp⟩
      left_inv q := by apply Subtype.ext; funext i; fin_cases i <;> simp [q.property]
      right_inv z := by simp }
    simpa [pow_two] using Fintype.card_congr e
  rw [hsamples, hfilter]
  have hnR : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  norm_cast

lemma expect_eq02 (hV : Nonempty V) :
    (𝔼 q ∈ FiniteDefect.samples 3 (Finset.univ : Finset V),
      indicator (q 0 = q 2)) = 1 / (Fintype.card V : ℝ) := by
  classical
  rw [Finset.expect_eq_sum_div_card, sum_indicator_eq_card_filter,
    card_samples]
  simp only [Finset.card_univ]
  have hn : Fintype.card V ≠ 0 := Fintype.card_ne_zero
  have hsamples : (samples 3 (Finset.univ : Finset V)).filter
      (fun q => q 0 = q 2) = Finset.univ.filter (fun q : Fin 3 → V => q 0 = q 2) := by
    ext q; simp [samples]
  have hfilter : (Finset.univ.filter (fun q : Fin 3 → V => q 0 = q 2)).card =
      Fintype.card V ^ 2 := by
    rw [← Fintype.card_coe]
    let e : {q : Fin 3 → V // q 0 = q 2} ≃ V × V := {
      toFun q := (q.1 0, q.1 1)
      invFun z := ⟨![z.1, z.2, z.1], by simp⟩
      left_inv q := by apply Subtype.ext; funext i; fin_cases i <;> simp [q.property]
      right_inv z := by simp }
    simpa [pow_two] using Fintype.card_congr e
  rw [hsamples, hfilter]
  have hnR : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  norm_cast

lemma expect_eq12 (hV : Nonempty V) :
    (𝔼 q ∈ FiniteDefect.samples 3 (Finset.univ : Finset V),
      indicator (q 1 = q 2)) = 1 / (Fintype.card V : ℝ) := by
  classical
  rw [Finset.expect_eq_sum_div_card, sum_indicator_eq_card_filter,
    card_samples]
  simp only [Finset.card_univ]
  have hn : Fintype.card V ≠ 0 := Fintype.card_ne_zero
  have hsamples : (samples 3 (Finset.univ : Finset V)).filter
      (fun q => q 1 = q 2) = Finset.univ.filter (fun q : Fin 3 → V => q 1 = q 2) := by
    ext q; simp [samples]
  have hfilter : (Finset.univ.filter (fun q : Fin 3 → V => q 1 = q 2)).card =
      Fintype.card V ^ 2 := by
    rw [← Fintype.card_coe]
    let e : {q : Fin 3 → V // q 1 = q 2} ≃ V × V := {
      toFun q := (q.1 0, q.1 1)
      invFun z := ⟨![z.1, z.2, z.2], by simp⟩
      left_inv q := by apply Subtype.ext; funext i; fin_cases i <;> simp [q.property]
      right_inv z := by simp }
    simpa [pow_two] using Fintype.card_congr e
  rw [hsamples, hfilter]
  have hnR : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  norm_cast

lemma edgeMass_univ_eq_sum_degree (G : SimpleGraph V) [DecidableRel G.Adj] :
    DRC.edgeMass G (Finset.univ : Finset V) Finset.univ = ∑ v, G.degree v := by
  classical
  unfold DRC.edgeMass
  apply Finset.sum_congr rfl
  intro v hv
  rw [← G.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simpa [G.mem_neighborFinset] using G.adj_comm w v

lemma exists_injective_commonNeighbors
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 48 ≤ Fintype.card V)
    (hdeg : ∀ v, (Fintype.card V : ℝ) / 2 + 100 ≤ G.degree v) :
    ∃ q : Fin 3 → V, Function.Injective q ∧
      (Fintype.card V : ℝ) / 16 ≤
        (FiniteDefect.commonNeighbors G q (Finset.univ : Finset V)).card := by
  classical
  let n : ℝ := Fintype.card V
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hU : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
  have hmass : (1 / 2 : ℝ) * (Finset.univ : Finset V).card *
      (Finset.univ : Finset V).card ≤
      DRC.edgeMass G (Finset.univ : Finset V) Finset.univ := by
    have hEM : (DRC.edgeMass G (Finset.univ : Finset V) Finset.univ : ℝ) =
        ∑ v : V, (G.degree v : ℝ) := by
      rw [edgeMass_univ_eq_sum_degree]
      norm_cast
    rw [hEM]
    calc
      (1 / 2 : ℝ) * (Finset.univ : Finset V).card *
          (Finset.univ : Finset V).card =
          ∑ _v : V, ((Fintype.card V : ℝ) / 2) := by
            simp [Finset.card_univ]
            ring
      _ ≤ ∑ v : V, (G.degree v : ℝ) := by
            apply Finset.sum_le_sum
            intro v hv
            exact le_trans (by linarith : (Fintype.card V : ℝ) / 2 ≤
              (Fintype.card V : ℝ) / 2 + 100) (hdeg v)
      _ = ∑ v : V, (G.degree v : ℝ) := rfl
  have hX := DRC.expect_card_commonNeighbors_lower G hU hU
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) hmass 3
  let Ω := FiniteDefect.samples 3 (Finset.univ : Finset V)
  let X : (Fin 3 → V) → ℝ := fun q =>
    (FiniteDefect.commonNeighbors G q (Finset.univ : Finset V)).card
  let P : (Fin 3 → V) → ℝ := fun q =>
    (Fintype.card V : ℝ) *
      (DRC.indicator (q 0 = q 1) + DRC.indicator (q 0 = q 2) + DRC.indicator (q 1 = q 2))
  have hΩ : Ω.Nonempty := DRC.samples_nonempty 3 hU
  have hX' : (n / 8) ≤ 𝔼 q ∈ Ω, X q := by
    norm_num at hX
    simpa [n, Ω, X, div_eq_mul_inv, mul_comm] using hX
  have hP : (𝔼 q ∈ Ω, P q) = 3 := by
    dsimp [Ω, P]
    simp_rw [mul_add]
    rw [Finset.expect_add_distrib, Finset.expect_add_distrib]
    simp_rw [mul_comm (Fintype.card V : ℝ)]
    rw [← Finset.expect_mul, ← Finset.expect_mul, ← Finset.expect_mul,
      expect_eq01 hV, expect_eq02 hV, expect_eq12 hV]
    have hnR : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
    ring
  have hobj : n / 16 ≤ 𝔼 q ∈ Ω, (X q - P q) := by
    rw [Finset.expect_sub_distrib, hP]
    have hn : (48 : ℝ) ≤ n := by
      dsimp [n]
      exact_mod_cast hcard
    linarith
  obtain ⟨q, hqΩ, hq⟩ := Finset.exists_le_of_le_expect hΩ hobj
  have hXle : X q ≤ n := by
    dsimp [X, n]
    exact_mod_cast Finset.card_le_card
      (commonNeighbors_subset_target G q (Finset.univ : Finset V))
  have hpos : 0 < n / 16 := by
    have hn : (0 : ℝ) < n := by
      dsimp [n]
      exact_mod_cast Fintype.card_pos
    positivity
  have h01 : q 0 ≠ q 1 := by
    intro h
    have hPge : n ≤ P q := by
      dsimp [P]
      rw [DRC.indicator_true h]
      have hnonneg : 0 ≤ DRC.indicator (q 0 = q 2) + DRC.indicator (q 1 = q 2) :=
        add_nonneg (DRC.indicator_nonneg _) (DRC.indicator_nonneg _)
      nlinarith
    linarith
  have h02 : q 0 ≠ q 2 := by
    intro h
    have hPge : n ≤ P q := by
      dsimp [P]
      rw [DRC.indicator_true h]
      have hnonneg : 0 ≤ DRC.indicator (q 0 = q 1) + DRC.indicator (q 1 = q 2) :=
        add_nonneg (DRC.indicator_nonneg _) (DRC.indicator_nonneg _)
      nlinarith
    linarith
  have h12 : q 1 ≠ q 2 := by
    intro h
    have hPge : n ≤ P q := by
      dsimp [P]
      rw [DRC.indicator_true h]
      have hnonneg : 0 ≤ DRC.indicator (q 0 = q 1) + DRC.indicator (q 0 = q 2) :=
        add_nonneg (DRC.indicator_nonneg _) (DRC.indicator_nonneg _)
      nlinarith
    linarith
  have hinj : Function.Injective q := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hPnonneg : 0 ≤ P q := by
    dsimp [P]
    have hn : (0 : ℝ) ≤ Fintype.card V := by positivity
    exact mul_nonneg hn (add_nonneg
      (add_nonneg (DRC.indicator_nonneg _) (DRC.indicator_nonneg _))
      (DRC.indicator_nonneg _))
  have hqX : n / 16 ≤ X q := by linarith
  exact ⟨q, hinj, by simpa [n, X] using hqX⟩

def neighborsIn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : Finset V :=
  S.filter fun w => G.Adj v w

omit [Fintype V] in
lemma exists_injective_fin3_of_card_ge_three (S : Finset V) (hS : 3 ≤ S.card) :
    ∃ f : Fin 3 → V, Function.Injective f ∧ ∀ i, f i ∈ S := by
  classical
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hS
  let f : Fin 3 → V := fun i =>
    ((T.equivFin).symm (Fin.cast hTcard.symm i) : T)
  refine ⟨f, ?_, ?_⟩
  · intro i j hij
    dsimp [f] at hij
    have hcast : Fin.cast hTcard.symm i = Fin.cast hTcard.symm j := by
      apply T.equivFin.symm.injective
      exact Subtype.ext hij
    exact (Fin.cast_injective hTcard.symm) hcast
  · intro i
    exact hTS ((T.equivFin).symm (Fin.cast hTcard.symm i)).property

lemma sum_card_neighborsIn_eq_sum_degree_on
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ∑ v : V, (neighborsIn G S v).card = ∑ w ∈ S, G.degree w := by
  classical
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := fun v w : V => G.Adj v w) (s := (Finset.univ : Finset V)) (t := S)
  calc
    ∑ v : V, (neighborsIn G S v).card =
        ∑ v ∈ (Finset.univ : Finset V),
          (Finset.bipartiteAbove (fun v w : V => G.Adj v w) S v).card := by
            apply Finset.sum_congr rfl
            intro v hv
            congr 1
    _ = ∑ w ∈ S,
          (Finset.bipartiteBelow (fun v w : V => G.Adj v w)
            (Finset.univ : Finset V) w).card := hdc
    _ = ∑ w ∈ S, G.degree w := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [← G.card_neighborFinset_eq_degree]
            congr 1
            ext v
            simpa [Finset.bipartiteBelow, G.mem_neighborFinset] using G.adj_comm v w

def Saturated33 (G : SimpleGraph V) : Prop :=
  ∀ (f g : Fin 3 → V), Function.Injective f → Function.Injective g →
    (∀ i j, G.Adj (f i) (g j)) →
    ∀ x y, (∀ j, G.Adj x (g j)) → (∀ i, G.Adj y (f i)) → G.Adj x y

omit [Fintype V] in
lemma card_neighborsIn_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : (neighborsIn G S v).card ≤ S.card :=
  Finset.card_filter_le _ _

omit [Fintype V] in
lemma card_neighborsIn_le_two_of_not_three
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V)
    (h : ¬ 3 ≤ (neighborsIn G S v).card) :
    (neighborsIn G S v).card ≤ 2 := by omega

lemma sum_neighborsIn_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (A : Finset V) (hA : ∀ v, v ∈ A ↔ 3 ≤ (neighborsIn G S v).card) :
    (∑ v : V, (neighborsIn G S v).card : ℕ) ≤ A.card * S.card + 2 * Fintype.card V := by
  classical
  calc
    (∑ v : V, (neighborsIn G S v).card : ℕ) ≤
        ∑ v : V, if v ∈ A then S.card else 2 := by
          apply Finset.sum_le_sum
          intro v hv
          by_cases hvA : v ∈ A
          · simp [hvA, card_neighborsIn_le_card]
          · simp only [hvA, ↓reduceIte]
            exact card_neighborsIn_le_two_of_not_three G S v (by simpa [hA v] using hvA)
    _ = A.card * S.card + ((Finset.univ.filter fun v : V => v ∉ A).card) * 2 := by
          rw [Finset.sum_ite]
          simp [mul_comm]
    _ ≤ A.card * S.card + 2 * Fintype.card V := by
          have hle : (Finset.univ.filter fun v : V => v ∉ A).card ≤ Fintype.card V := by
            simpa using Finset.card_filter_le (Finset.univ : Finset V) (fun v => v ∉ A)
          omega

lemma low_degree_of_saturated33
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] (hSat : Saturated33 G) :
    ∃ v : V, (G.degree v : ℝ) ≤ (Fintype.card V : ℝ) / 2 + 100 := by
  classical
  by_cases hsmall : Fintype.card V < 48
  · obtain ⟨v⟩ := (inferInstance : Nonempty V)
    refine ⟨v, ?_⟩
    have hdeg : G.degree v ≤ Fintype.card V := by
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card (by simp)
    have hdegR : (G.degree v : ℝ) ≤ Fintype.card V := by exact_mod_cast hdeg
    have hn : (Fintype.card V : ℝ) < 48 := by exact_mod_cast hsmall
    nlinarith
  · have hcard : 48 ≤ Fintype.card V := by omega
    by_contra hnone
    push Not at hnone
    have hdeg : ∀ v, (Fintype.card V : ℝ) / 2 + 100 ≤ G.degree v := by
      intro v
      exact (le_of_lt (hnone v))
    obtain ⟨q, hqinj, hqB⟩ := exists_injective_commonNeighbors G hcard hdeg
    let B := FiniteDefect.commonNeighbors G q (Finset.univ : Finset V)
    have hBcard : 3 ≤ B.card := by
      have hBreal : (3 : ℝ) ≤ B.card := by
        have h48R : (48 : ℝ) ≤ Fintype.card V := by exact_mod_cast hcard
        calc
          (3 : ℝ) ≤ (Fintype.card V : ℝ) / 16 := by nlinarith
          _ ≤ B.card := hqB
      exact_mod_cast hBreal
    let A := (Finset.univ : Finset V).filter fun v => 3 ≤ (neighborsIn G B v).card
    have hAiff (v : V) : v ∈ A ↔ 3 ≤ (neighborsIn G B v).card := by simp [A]
    have hAB : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b := by
      intro a ha b hb
      obtain ⟨g, hginj, hgmem⟩ := exists_injective_fin3_of_card_ge_three
        (neighborsIn G B a) ((hAiff a).mp ha)
      have hcross : ∀ i j, G.Adj (q i) (g j) := by
        intro i j
        have hgjB : g j ∈ B := (Finset.mem_filter.mp (hgmem j)).1
        exact (mem_commonNeighbors G q (Finset.univ : Finset V) (g j)).mp hgjB |>.2 i
      apply hSat q g hqinj hginj hcross a b
      · intro j
        exact (Finset.mem_filter.mp (hgmem j)).2
      · intro i
        have hb' := (mem_commonNeighbors G q (Finset.univ : Finset V) b).mp hb |>.2 i
        exact (G.adj_comm _ _).mp hb'
    have hsumB : ∑ v : V, (neighborsIn G B v).card = ∑ b ∈ B, G.degree b :=
      sum_card_neighborsIn_eq_sum_degree_on G B
    have hlowB : (B.card : ℝ) * ((Fintype.card V : ℝ) / 2 + 100) ≤
        (∑ v : V, (neighborsIn G B v).card : ℕ) := by
      rw [hsumB, Nat.cast_sum]
      calc
        (B.card : ℝ) * ((Fintype.card V : ℝ) / 2 + 100) =
            ∑ _b ∈ B, ((Fintype.card V : ℝ) / 2 + 100) := by
              simp [mul_add]
        _ ≤ ∑ b ∈ B, (G.degree b : ℝ) := by
          exact Finset.sum_le_sum fun b hb => hdeg b
    have huppB : ((∑ v : V, (neighborsIn G B v).card : ℕ) : ℝ) ≤
        (A.card : ℝ) * B.card + 2 * Fintype.card V := by
      exact_mod_cast sum_neighborsIn_le G B A hAiff
    have hBpos : (0 : ℝ) < B.card := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hBcard)
    have hn : (0 : ℝ) ≤ Fintype.card V := by positivity
    have hAreal : (Fintype.card V : ℝ) / 2 + 68 ≤ A.card := by
      have hdiv : 2 * (Fintype.card V : ℝ) / B.card ≤ 32 := by
        apply (div_le_iff₀ hBpos).2
        have hb16 : (Fintype.card V : ℝ) / 16 ≤ B.card := hqB
        nlinarith
      have hmain := hlowB.trans huppB
      apply (le_of_sub_nonneg ?_)
      nlinarith
    have hAcard : 3 ≤ A.card := by
      have h : (3 : ℝ) ≤ A.card := by
        calc
          (3 : ℝ) ≤ (Fintype.card V : ℝ) / 2 + 68 := by nlinarith
          _ ≤ A.card := hAreal
      exact_mod_cast h
    let B' := (Finset.univ : Finset V).filter fun v => 3 ≤ (neighborsIn G A v).card
    have hB'iff (v : V) : v ∈ B' ↔ 3 ≤ (neighborsIn G A v).card := by simp [B']
    have hAB' : ∀ a ∈ A, ∀ b ∈ B', G.Adj a b := by
      intro a ha b hb
      obtain ⟨f, hfinj, hfmem⟩ := exists_injective_fin3_of_card_ge_three
        (neighborsIn G A b) ((hB'iff b).mp hb)
      obtain ⟨g, hginj, hgmem⟩ := exists_injective_fin3_of_card_ge_three B hBcard
      have hcross : ∀ i j, G.Adj (g i) (f j) := by
        intro i j
        exact (G.adj_comm _ _).mp
          (hAB (f j) ((Finset.mem_filter.mp (hfmem j)).1) (g i) (hgmem i))
      have hb' : G.Adj b a := by
        apply hSat g f hginj hfinj hcross b a
        · intro j; exact (Finset.mem_filter.mp (hfmem j)).2
        · intro i; exact hAB a ha (g i) (hgmem i)
      exact (G.adj_comm _ _).mp hb'
    have hsumA : ∑ v : V, (neighborsIn G A v).card = ∑ a ∈ A, G.degree a :=
      sum_card_neighborsIn_eq_sum_degree_on G A
    have hlowA : (A.card : ℝ) * ((Fintype.card V : ℝ) / 2 + 100) ≤
        (∑ v : V, (neighborsIn G A v).card : ℕ) := by
      rw [hsumA, Nat.cast_sum]
      calc
        (A.card : ℝ) * ((Fintype.card V : ℝ) / 2 + 100) =
            ∑ _a ∈ A, ((Fintype.card V : ℝ) / 2 + 100) := by
              simp [mul_add]
        _ ≤ ∑ a ∈ A, (G.degree a : ℝ) := by
          exact Finset.sum_le_sum fun a ha => hdeg a
    have huppA : ((∑ v : V, (neighborsIn G A v).card : ℕ) : ℝ) ≤
        (B'.card : ℝ) * A.card + 2 * Fintype.card V := by
      exact_mod_cast sum_neighborsIn_le G A B' hB'iff
    have hApos : (0 : ℝ) < A.card := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hAcard)
    have hB'real : (Fintype.card V : ℝ) / 2 + 96 ≤ B'.card := by
      have hdiv : 2 * (Fintype.card V : ℝ) / A.card ≤ 4 := by
        apply (div_le_iff₀ hApos).2
        have ha2 : (Fintype.card V : ℝ) / 2 ≤ A.card := by linarith
        nlinarith
      have hmain := hlowA.trans huppA
      apply (le_of_sub_nonneg ?_)
      nlinarith
    have hdisj : Disjoint A B' := by
      apply Finset.disjoint_left.2
      intro z hzA hzB'
      exact G.irrefl (hAB' z hzA z hzB')
    have hcardunion : A.card + B'.card ≤ Fintype.card V := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card (by simp)
    have hcontr : (Fintype.card V : ℝ) + 164 ≤ A.card + B'.card := by
      linarith
    have hcardunionR : (A.card + B'.card : ℝ) ≤ Fintype.card V := by
      exact_mod_cast hcardunion
    linarith

omit [Fintype V] in
lemma saturated33_induce
    (G : SimpleGraph V) (S : Set V) (hSat : Saturated33 G) :
    Saturated33 (G.induce S) := by
  intro f g hf hg hcross x y hx hy
  let f' : Fin 3 → V := fun i => (f i : V)
  let g' : Fin 3 → V := fun j => (g j : V)
  have hf' : Function.Injective f' := by
    intro i j h
    apply hf
    exact Subtype.ext h
  have hg' : Function.Injective g' := by
    intro i j h
    apply hg
    exact Subtype.ext h
  have hcross' : ∀ i j, G.Adj (f' i) (g' j) := hcross
  exact hSat f' g' hf' hg' hcross' x y hx hy

theorem card_edgeFinset_le_quarter_add_linear_of_saturated33 :
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Saturated33 G →
      (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 4 + 101 * Fintype.card V := by
  intro V instV G instAdj hSat
  classical
  generalize hn : Fintype.card V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      by_cases hV : Nonempty V
      · let := hV
        obtain ⟨v, hvdeg⟩ := low_degree_of_saturated33 G hSat
        let S : Set V := {v}ᶜ
        let J := G.induce S
        have hcardS : Fintype.card S = n - 1 := by
          change Fintype.card {x : V // x ≠ v} = n - 1
          have hone : Fintype.card {x : V // x = v} = 1 := by simp
          calc
            Fintype.card {x : V // x ≠ v} =
                Fintype.card V - Fintype.card {x : V // x = v} := by
                  exact Fintype.card_subtype_compl (fun x : V => x = v)
            _ = n - 1 := by rw [hone, hn]
        have hnpos : 0 < n := by
          rw [← hn]
          exact Fintype.card_pos
        have hJ : (J.edgeFinset.card : ℝ) ≤
            (Fintype.card S : ℝ) ^ 2 / 4 + 101 * Fintype.card S := by
          have hJ' := ih (n - 1) (by omega) J (saturated33_induce G S hSat) hcardS
          simpa [hcardS] using hJ'
        have hdegNat : G.degree v ≤ G.edgeFinset.card := G.degree_le_card_edgeFinset v
        have hsplit : G.edgeFinset.card = J.edgeFinset.card + G.degree v := by
          rw [← Nat.sub_add_cancel hdegNat,
            ← G.card_edgeFinset_deleteIncidenceSet v,
            ← G.card_edgeFinset_induce_compl_singleton v]
        rw [hsplit, Nat.cast_add]
        rw [hcardS] at hJ
        have hnsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]
          norm_num
        rw [hnsub] at hJ
        have hdeg' : (G.degree v : ℝ) ≤ (n : ℝ) / 2 + 100 := by
          rw [← hn]
          exact hvdeg
        have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
        nlinarith
      · have : IsEmpty V := not_nonempty_iff.mp hV
        have hn0 : n = 0 := by
          rw [← hn]
          exact Fintype.card_eq_zero
        subst n
        have he := G.card_edgeFinset_le_card_choose_two
        rw [hn0] at he
        norm_num at he
        subst G
        simp

/-! ## Euclidean rectangle completion -/

abbrev E4 := EuclideanSpace ℝ (Fin 4)

lemma pair_vsub_mem_vectorSpan (a b : E4) :
    b - a ∈ vectorSpan ℝ (Set.range ![a, b]) := by
  exact vsub_mem_vectorSpan ℝ ⟨1, rfl⟩ ⟨0, rfl⟩

lemma finrank_E4 : Module.finrank ℝ E4 = 4 := by simp [E4]

lemma vectorSpan_eq_orthogonal_of_cross
    (f g : Fin 3 → E4) (hf : Function.Injective f) (hg : Function.Injective g)
    (r : ℝ) (hcross : ∀ i j, dist (f i) (g j) = r) :
    vectorSpan ℝ (Set.range f) = (vectorSpan ℝ (Set.range g))ᗮ := by
  let U := vectorSpan ℝ (Set.range f)
  let W := vectorSpan ℝ (Set.range g)
  have hUW : U ⟂ W := Erdos755.vectorSpan_range_isOrtho_of_cross_dist_eq f g r hcross
  have hle : U ≤ Wᗮ := Submodule.isOrtho_iff_le.mp hUW
  have hU : Module.finrank ℝ U = 2 :=
    Erdos755.finrank_vectorSpan_fin3_of_equidistant f hf (g 0) r (fun i => hcross i 0)
  have hW : Module.finrank ℝ W = 2 :=
    Erdos755.finrank_vectorSpan_fin3_of_equidistant g hg (f 0) r
      (fun j => by simpa [dist_comm] using hcross 0 j)
  have hsum := Submodule.finrank_add_finrank_orthogonal W
  have hWperp : Module.finrank ℝ Wᗮ = 2 := by
    rw [hW, finrank_E4] at hsum
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hU, hWperp])

lemma orthogonal_quadrilateral
    {x a y b : E4} (horth : inner ℝ (x - a) (y - b) = 0) :
    ‖x - y‖ ^ 2 + ‖a - b‖ ^ 2 = ‖x - b‖ ^ 2 + ‖a - y‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real]
  simp only [inner_sub_left, inner_sub_right] at horth
  nlinarith

/-- In four dimensions, two transverse triples at one common distance have the
rectangle-completion property used in Swanepoel's argument. -/
lemma dist_eq_of_cross_completion
    (f g : Fin 3 → E4) (hf : Function.Injective f) (hg : Function.Injective g)
    (r : ℝ) (hr : 0 < r) (hcross : ∀ i j, dist (f i) (g j) = r)
    (x y : E4) (hx : ∀ j, dist x (g j) = r) (hy : ∀ i, dist y (f i) = r) :
    dist x y = r := by
  let U := vectorSpan ℝ (Set.range f)
  let W := vectorSpan ℝ (Set.range g)
  have hUW : U ⟂ W := Erdos755.vectorSpan_range_isOrtho_of_cross_dist_eq f g r hcross
  have hUeq : U = Wᗮ := vectorSpan_eq_orthogonal_of_cross f g hf hg r hcross
  have hWeq : W = Uᗮ := by
    have hWU : W ⟂ U := hUW.symm
    have hle : W ≤ Uᗮ := Submodule.isOrtho_iff_le.mp hWU
    have hW : Module.finrank ℝ W = 2 :=
      Erdos755.finrank_vectorSpan_fin3_of_equidistant g hg (f 0) r
        (fun j => by simpa [dist_comm] using hcross 0 j)
    have hU : Module.finrank ℝ U = 2 :=
      Erdos755.finrank_vectorSpan_fin3_of_equidistant f hf (g 0) r (fun i => hcross i 0)
    have hsum := Submodule.finrank_add_finrank_orthogonal U
    have hUperp : Module.finrank ℝ Uᗮ = 2 := by
      rw [hU, finrank_E4] at hsum
      omega
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hW, hUperp])
  have hxspan : x - f 0 ∈ U := by
    have hp : vectorSpan ℝ (Set.range ![f 0, x]) ⟂ W :=
      Erdos755.vectorSpan_range_isOrtho_of_cross_dist_eq ![f 0, x] g r (by
        intro i j
        fin_cases i
        · exact hcross 0 j
        · exact hx j)
    have hxperp : x - f 0 ∈ Wᗮ :=
      (Submodule.isOrtho_iff_le.mp hp) (pair_vsub_mem_vectorSpan (f 0) x)
    rwa [hUeq]
  have hyspan : y - g 0 ∈ W := by
    have hp : vectorSpan ℝ (Set.range ![g 0, y]) ⟂ U :=
      Erdos755.vectorSpan_range_isOrtho_of_cross_dist_eq ![g 0, y] f r (by
        intro j i
        fin_cases j
        · simpa [dist_comm] using hcross i 0
        · simpa [dist_comm] using hy i)
    have hyperp : y - g 0 ∈ Uᗮ :=
      (Submodule.isOrtho_iff_le.mp hp) (pair_vsub_mem_vectorSpan (g 0) y)
    rwa [hWeq]
  have hxspan' : x - f 0 ∈ Submodule.span ℝ (Set.range (fun i => f i - f 0)) := by
    have hxspanv : x - f 0 ∈ Submodule.span ℝ (Set.range (fun i => f i -ᵥ f 0)) := by
      rw [← vectorSpan_range_eq_span_range_vsub_right ℝ f 0]
      exact hxspan
    simpa only [vsub_eq_sub] using hxspanv
  have hyspan' : y - g 0 ∈ Submodule.span ℝ (Set.range (fun j => g j - g 0)) := by
    have hyspanv : y - g 0 ∈ Submodule.span ℝ (Set.range (fun j => g j -ᵥ g 0)) := by
      rw [← vectorSpan_range_eq_span_range_vsub_right ℝ g 0]
      exact hyspan
    simpa only [vsub_eq_sub] using hyspanv
  have horth : inner ℝ (x - f 0) (y - g 0) = 0 :=
    Erdos755.inner_eq_zero_of_mem_orthogonal_spans
      (u := fun i => f i - f 0) (v := fun j => g j - g 0)
      (fun i j => by
        have hmemi : f i - f 0 ∈ U := vsub_mem_vectorSpan ℝ ⟨i, rfl⟩ ⟨0, rfl⟩
        have hmemj : g j - g 0 ∈ W := vsub_mem_vectorSpan ℝ ⟨j, rfl⟩ ⟨0, rfl⟩
        exact hUW.inner_eq hmemi hmemj)
      hxspan' hyspan'
  have hquad := orthogonal_quadrilateral horth
  have hy0 : dist (f 0) y = r := by simpa [dist_comm] using hy 0
  rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm,
    hx 0, hcross 0 0, hy0] at hquad
  have hsquare : dist x y ^ 2 = r ^ 2 := by nlinarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsquare) with h | h
  · exact h
  · have : 0 ≤ dist x y := dist_nonneg
    nlinarith

/-! ## Fixed-distance graphs -/

noncomputable def distanceGraph {W : Type*} (p : W → E4)
    (_hp : Function.Injective p) (r : ℝ) (hr : 0 < r) : SimpleGraph W where
  Adj x y := dist (p x) (p y) = r
  symm.symm := by intro x y h; simpa [dist_comm] using h
  loopless.irrefl := by
    intro x h
    have : (0 : ℝ) = r := by simpa using h
    linarith

noncomputable instance distanceGraph.instDecidableRelAdj {W : Type*} (p : W → E4)
    (hp : Function.Injective p) (r : ℝ) (hr : 0 < r) :
    DecidableRel (distanceGraph p hp r hr).Adj := Classical.decRel _

lemma distanceGraph_saturated33 {W : Type*} (p : W → E4)
    (hp : Function.Injective p) (r : ℝ) (hr : 0 < r) :
    Saturated33 (distanceGraph p hp r hr) := by
  intro f g hf hg hcross x y hx hy
  let f' : Fin 3 → E4 := fun i => p (f i)
  let g' : Fin 3 → E4 := fun j => p (g j)
  have hf' : Function.Injective f' := hp.comp hf
  have hg' : Function.Injective g' := hp.comp hg
  exact dist_eq_of_cross_completion f' g' hf' hg' r hr hcross (p x) (p y) hx hy

lemma directed_indicator_eq_twice_edges {W : Type*} [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    (∑ x : W, ∑ y : W, DRC.indicator (G.Adj x y)) =
      2 * (G.edgeFinset.card : ℝ) := by
  classical
  calc
    (∑ x : W, ∑ y : W, DRC.indicator (G.Adj x y)) =
        ∑ x : W, (G.degree x : ℝ) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [DRC.sum_indicator_eq_card_filter]
          rw [← G.card_neighborFinset_eq_degree]
          have hfilter : (Finset.univ.filter fun y : W => G.Adj x y) =
              G.neighborFinset x := by
            ext y
            simp [G.mem_neighborFinset]
          rw [hfilter]
    _ = 2 * (G.edgeFinset.card : ℝ) := by
          rw [← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges]
          norm_cast

/-! ## Fiberwise counting -/

noncomputable def fiber {W : Type*} [Fintype W] (c : W → ℝ) (t : ℝ) : Finset W :=
  Finset.univ.filter fun x => c x = t

lemma sum_eq_eq_fibers {W : Type*} [Fintype W]
    (c : W → ℝ) (w : W → W → ℝ) :
    ∑ x : W, ∑ y : W, (if c x = c y then w x y else 0) =
      ∑ t ∈ (Finset.univ.image c), ∑ x ∈ fiber c t, ∑ y ∈ fiber c t, w x y := by
  classical
  symm
  calc
    ∑ t ∈ (Finset.univ.image c), ∑ x ∈ fiber c t, ∑ y ∈ fiber c t, w x y =
        ∑ t ∈ (Finset.univ.image c),
          ∑ x ∈ (Finset.univ : Finset W) with c x = t,
            ∑ y ∈ (Finset.univ : Finset W) with c y = t, w x y := by rfl
    _ = ∑ t ∈ (Finset.univ.image c),
          ∑ x ∈ (Finset.univ : Finset W) with c x = t,
            ∑ y ∈ (Finset.univ : Finset W) with c y = c x, w x y := by
          apply Finset.sum_congr rfl
          intro t ht
          apply Finset.sum_congr rfl
          intro x hx
          have hxt : c x = t := (Finset.mem_filter.mp hx).2
          rw [hxt]
    _ = ∑ x ∈ (Finset.univ : Finset W),
          ∑ y ∈ (Finset.univ : Finset W) with c y = c x, w x y := by
          rw [Finset.sum_fiberwise_of_maps_to (g := c)
            (s := (Finset.univ : Finset W)) (t := Finset.univ.image c)]
          intro x hx
          exact Finset.mem_image_of_mem c hx
    _ = ∑ x : W, ∑ y : W, (if c x = c y then w x y else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_filter]
          congr 1
          funext y
          by_cases h : c x = c y <;> simp [h, eq_comm]

lemma sum_fiber_card {W : Type*} [Fintype W] (c : W → ℝ) :
    ∑ t ∈ (Finset.univ.image c), (fiber c t).card = Fintype.card W := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := c)
    (s := (Finset.univ : Finset W)) (t := Finset.univ.image c)
    (fun x hx => Finset.mem_image_of_mem c hx)
  simpa [fiber] using h.symm

lemma sum_eq_indicator_eq_sum_fiber_sq {W : Type*} [Fintype W] (c : W → ℝ) :
    ∑ x : W, ∑ y : W, DRC.indicator (c x = c y) =
      ∑ t ∈ (Finset.univ.image c), ((fiber c t).card : ℝ) ^ 2 := by
  classical
  rw [show (∑ x : W, ∑ y : W, DRC.indicator (c x = c y)) =
      ∑ x : W, ∑ y : W, (if c x = c y then (1 : ℝ) else 0) by
        simp [DRC.indicator, Erdos754.indicator]]
  rw [sum_eq_eq_fibers]
  apply Finset.sum_congr rfl
  intro t ht
  simp [pow_two]

lemma total_le_of_same_le {W : Type*} [Fintype W]
    (c : W → ℝ) (fav : W → W → Prop)
    (hboth : ∀ x y, c x ≠ c y → fav x y → fav y x → False)
    (hSame :
      ∑ x : W, ∑ y : W,
          (if c x = c y then DRC.indicator (fav x y) else 0) ≤
        (∑ x : W, ∑ y : W, DRC.indicator (c x = c y)) / 2 +
          202 * Fintype.card W) :
    ∑ x : W, ∑ y : W, DRC.indicator (fav x y) ≤
      (Fintype.card W : ℝ) ^ 2 / 2 + 202 * Fintype.card W := by
  classical
  let S : ℝ := ∑ x : W, ∑ y : W, DRC.indicator (fav x y)
  let I : ℝ := ∑ x : W, ∑ y : W,
    (if c x = c y then DRC.indicator (fav x y) else 0)
  let E : ℝ := ∑ x : W, ∑ y : W, DRC.indicator (c x = c y)
  let R : ℝ := ∑ x : W, ∑ y : W,
    (if c x = c y then DRC.indicator (fav x y) + DRC.indicator (fav y x) else 1)
  have hpair : ∀ x y,
      DRC.indicator (fav x y) + DRC.indicator (fav y x) ≤
        (if c x = c y then DRC.indicator (fav x y) + DRC.indicator (fav y x) else 1) := by
    intro x y
    by_cases hxy : c x = c y
    · simp [hxy]
    · by_cases h1 : fav x y
      · by_cases h2 : fav y x
        · exact False.elim (hboth x y hxy h1 h2)
        · simp [hxy, h1, h2, DRC.indicator]
      · by_cases h2 : fav y x <;> simp [hxy, h1, h2, DRC.indicator]
  have htwice : 2 * S =
      ∑ x : W, ∑ y : W,
        (DRC.indicator (fav x y) + DRC.indicator (fav y x)) := by
    dsimp [S]
    have hsplit :
        (∑ x : W, ∑ y : W,
          (DRC.indicator (fav x y) + DRC.indicator (fav y x))) =
        (∑ x : W, ∑ y : W, DRC.indicator (fav x y)) +
          (∑ x : W, ∑ y : W, DRC.indicator (fav y x)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_add_distrib]
    have hswap : (∑ x : W, ∑ y : W, DRC.indicator (fav y x)) =
        ∑ x : W, ∑ y : W, DRC.indicator (fav x y) := by rw [Finset.sum_comm]
    rw [hsplit, hswap]
    ring
  have hRbound : 2 * S ≤ R := by
    rw [htwice]
    exact Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hpair x y
  have hR : R = 2 * I + ((Fintype.card W : ℝ) ^ 2 - E) := by
    dsimp [R, I, E]
    have hsplit :
        (∑ x : W, ∑ y : W,
          (if c x = c y then DRC.indicator (fav x y) + DRC.indicator (fav y x) else 1)) =
        (∑ x : W, ∑ y : W, (if c x = c y then DRC.indicator (fav x y) else 0)) +
        (∑ x : W, ∑ y : W, (if c x = c y then DRC.indicator (fav y x) else 0)) +
        (∑ x : W, ∑ y : W, (if c x = c y then (0 : ℝ) else 1)) := by
      calc
        (∑ x : W, ∑ y : W,
          (if c x = c y then DRC.indicator (fav x y) + DRC.indicator (fav y x) else 1)) =
          ∑ x : W, ∑ y : W,
            ((if c x = c y then DRC.indicator (fav x y) else 0) +
              (if c x = c y then DRC.indicator (fav y x) else 0) +
              (if c x = c y then (0 : ℝ) else 1)) := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            by_cases h : c x = c y <;> simp [h]
        _ = _ := by simp_rw [Finset.sum_add_distrib]
    rw [hsplit]
    have hswap :
        (∑ x : W, ∑ y : W, (if c x = c y then DRC.indicator (fav y x) else 0)) =
        ∑ x : W, ∑ y : W, (if c x = c y then DRC.indicator (fav x y) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      by_cases h : c x = c y
      · rw [if_pos h.symm, if_pos h]
      · have h' : c y ≠ c x := Ne.symm h
        rw [if_neg h', if_neg h]
    rw [hswap]
    have hpartition :
        (∑ x : W, ∑ y : W, (if c x = c y then (0 : ℝ) else 1)) +
        (∑ x : W, ∑ y : W, DRC.indicator (c x = c y)) =
          (Fintype.card W : ℝ) ^ 2 := by
      have hpoint :
          (∑ x : W, ∑ y : W,
            ((if c x = c y then (0 : ℝ) else 1) + DRC.indicator (c x = c y))) =
            (Fintype.card W : ℝ) ^ 2 := by
        calc
          (∑ x : W, ∑ y : W,
            ((if c x = c y then (0 : ℝ) else 1) + DRC.indicator (c x = c y))) =
              ∑ x : W, ∑ y : W, (1 : ℝ) := by
                apply Finset.sum_congr rfl
                intro x hx
                apply Finset.sum_congr rfl
                intro y hy
                by_cases h : c x = c y <;> simp [h, DRC.indicator]
          _ = (Fintype.card W : ℝ) ^ 2 := by simp [pow_two]
      rw [← hpoint]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_add_distrib]
    linarith
  have hSame' : I ≤ E / 2 + 202 * Fintype.card W := by simpa [I, E] using hSame
  rw [hR] at hRbound
  linarith

lemma same_le_of_fiber_bounds {W : Type*} [Fintype W]
    (c : W → ℝ) (fav : W → W → Prop)
    (hFiber : ∀ t ∈ Finset.univ.image c,
      ∑ x ∈ fiber c t, ∑ y ∈ fiber c t, DRC.indicator (fav x y) ≤
        ((fiber c t).card : ℝ) ^ 2 / 2 + 202 * (fiber c t).card) :
    ∑ x : W, ∑ y : W,
        (if c x = c y then DRC.indicator (fav x y) else 0) ≤
      (∑ x : W, ∑ y : W, DRC.indicator (c x = c y)) / 2 +
        202 * Fintype.card W := by
  classical
  rw [sum_eq_eq_fibers]
  calc
    ∑ t ∈ Finset.univ.image c,
        ∑ x ∈ fiber c t, ∑ y ∈ fiber c t, DRC.indicator (fav x y) ≤
      ∑ t ∈ Finset.univ.image c,
        (((fiber c t).card : ℝ) ^ 2 / 2 + 202 * (fiber c t).card) := by
          exact Finset.sum_le_sum hFiber
    _ = (∑ x : W, ∑ y : W, DRC.indicator (c x = c y)) / 2 +
        202 * Fintype.card W := by
          have hcardR : (∑ t ∈ Finset.univ.image c, ((fiber c t).card : ℝ)) =
              Fintype.card W := by
            exact_mod_cast sum_fiber_card c
          rw [sum_eq_indicator_eq_sum_fiber_sq]
          simp_rw [Finset.sum_add_distrib]
          rw [Finset.sum_div, ← Finset.mul_sum, hcardR]

/-- A favorite-distance relation; the strict positivity is kept separately. -/
def IsFavorite {W : Type*} (p : W → E4) (c : W → ℝ) (x y : W) : Prop :=
  x ≠ y ∧ dist (p x) (p y) = c x

lemma fiber_directed_bound {W : Type*}
    (p : W → E4) (hp : Function.Injective p) (c : W → ℝ) (hc : ∀ x, 0 < c x)
    (F : Finset W) (t : ℝ) (hFt : ∀ x ∈ F, c x = t) :
    ∑ x ∈ F, ∑ y ∈ F, DRC.indicator (IsFavorite p c x y) ≤
      ((F.card : ℝ) ^ 2 / 2 + 202 * F.card) := by
  classical
  by_cases hF : F.Nonempty
  · obtain ⟨x0, hx0⟩ := hF
    have ht : 0 < t := by rw [← hFt x0 hx0]; exact hc x0
    let q : F → E4 := fun x => p x
    have hq : Function.Injective q := by
      intro x y h
      apply Subtype.ext
      exact hp h
    let G := distanceGraph q hq t ht
    have hG := card_edgeFinset_le_quarter_add_linear_of_saturated33 G
      (distanceGraph_saturated33 q hq t ht)
    have hdir := directed_indicator_eq_twice_edges G
    have hsum :
        (∑ x ∈ F, ∑ y ∈ F, DRC.indicator (IsFavorite p c x y)) =
          ∑ x : F, ∑ y : F, DRC.indicator (G.Adj x y) := by
      rw [← Finset.sum_coe_sort F
        (fun x => ∑ y ∈ F, DRC.indicator (IsFavorite p c x y))]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.sum_coe_sort F
        (fun y => DRC.indicator (IsFavorite p c (x : W) y))]
      apply Finset.sum_congr rfl
      intro y hy
      have hcx : c x = t := hFt x x.property
      by_cases hxy : x = y
      · subst y
        simp [G, distanceGraph, IsFavorite]
      · simp [G, distanceGraph, q, IsFavorite, hxy, hcx]
    rw [hsum, hdir]
    have hcard : Fintype.card F = F.card := Fintype.card_coe F
    rw [hcard] at hG
    nlinarith
  · have hF0 : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [hF0]

/-- The Swanepoel-type favorite-distance bound, with an explicit absolute constant. -/
theorem favorite_distance_sum_le {W : Type*} [Fintype W]
    (p : W → E4) (hp : Function.Injective p) (c : W → ℝ) (hc : ∀ x, 0 < c x) :
    ∑ x : W, ∑ y : W, DRC.indicator (IsFavorite p c x y) ≤
      (Fintype.card W : ℝ) ^ 2 / 2 + 202 * Fintype.card W := by
  classical
  apply total_le_of_same_le c (IsFavorite p c)
  · intro x y hxy h1 h2
    have hdist : c x = c y := by
      calc
        c x = dist (p x) (p y) := h1.2.symm
        _ = dist (p y) (p x) := dist_comm _ _
        _ = c y := h2.2
    exact hxy hdist
  · apply same_le_of_fiber_bounds c (IsFavorite p c)
    intro t ht
    apply fiber_directed_bound p hp c hc (fiber c t) t
    intro x hx
    exact (Finset.mem_filter.mp hx).2

/-! ## The extremal function in Problem 754 -/

/-- The number of other points at the prescribed positive distance from `x`. -/
noncomputable def favoriteDegree (P : Finset E4) (c : P → ℝ) (x : P) : ℕ :=
  open scoped Classical in
  (Finset.univ.filter fun y : P => IsFavorite (fun z : P => (z : E4)) c x y).card

/-- A value `k` is attainable for a set of `n` points when every point has at least
`k` other points at its own prescribed positive distance. -/
def Attainable (n k : ℕ) : Prop :=
  ∃ P : Finset E4, P.card = n ∧
    ∃ c : P → ℝ, (∀ x, 0 < c x) ∧ ∀ x, k ≤ favoriteDegree P c x

/-- The maximal minimum favorite-distance degree for `n` points.  The empty case is
set to zero, as the problem concerns positive numbers of points. -/
noncomputable def f (n : ℕ) : ℕ :=
  if n = 0 then 0 else sSup {k : ℕ | Attainable n k}

lemma sum_favoriteDegree_eq (P : Finset E4) (c : P → ℝ) :
    ∑ x : P, (favoriteDegree P c x : ℝ) =
      ∑ x : P, ∑ y : P,
        DRC.indicator (IsFavorite (fun z : P => (z : E4)) c x y) := by
  classical
  apply Finset.sum_congr rfl
  intro x hx
  unfold favoriteDegree
  rw [DRC.sum_indicator_eq_card_filter]

lemma attainable_bddAbove (n : ℕ) (hn : n ≠ 0) : BddAbove {k : ℕ | Attainable n k} := by
  classical
  refine ⟨n, ?_⟩
  intro k hk
  rcases hk with ⟨P, hP, c, hc, hk⟩
  have hPempty : P.Nonempty := by
    apply Finset.card_pos.mp
    rw [hP]
    omega
  obtain ⟨x, hx⟩ := hPempty
  let xP : P := ⟨x, hx⟩
  have hdeg : favoriteDegree P c xP ≤ Fintype.card P := by
    unfold favoriteDegree
    simpa using Finset.card_filter_le (Finset.univ : Finset P)
      (fun y : P => IsFavorite (fun z : P => (z : E4)) c xP y)
  simpa [hP] using (hk xP).trans hdeg

lemma attainable_nonempty (n : ℕ) : {k : ℕ | Attainable n k}.Nonempty := by
  obtain ⟨P, hP⟩ := Finset.exists_card_eq (α := E4) n
  refine ⟨0, P, hP, (fun _ => 1), ?_, ?_⟩
  · intro x
    norm_num
  · intro x
    omega

lemma attainable_cast_le (n k : ℕ) (hn : n ≠ 0) (hk : Attainable n k) :
    (k : ℝ) ≤ (n : ℝ) / 2 + 202 := by
  rcases hk with ⟨P, hP, c, hc, hk⟩
  have hPne : P.Nonempty := by
    apply Finset.card_pos.mp
    rw [hP]
    omega
  have hsumlow : (n : ℝ) * k ≤ ∑ x : P, (favoriteDegree P c x : ℝ) := by
    rw [← hP]
    calc
      (P.card : ℝ) * k = ∑ _x : P, (k : ℝ) := by simp
      _ ≤ ∑ x : P, (favoriteDegree P c x : ℝ) := by
        exact Finset.sum_le_sum fun x hx => by exact_mod_cast hk x
  have hsumup : ∑ x : P, (favoriteDegree P c x : ℝ) ≤
      (n : ℝ) ^ 2 / 2 + 202 * n := by
    rw [sum_favoriteDegree_eq]
    have h := favorite_distance_sum_le (fun z : P => (z : E4))
      (fun _ _ hxy => Subtype.ext hxy) c hc
    simpa [hP] using h
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  nlinarith

/-- Erdős Problem 754: the maximal favorite-distance degree is at most `n / 2`
plus an absolute constant. -/
theorem erdos_754_upper : ∃ C : ℝ, ∀ n : ℕ, (f n : ℝ) ≤ (n : ℝ) / 2 + C := by
  refine ⟨202, fun n => ?_⟩
  by_cases hn : n = 0
  · subst n
    simp [f]
  · have hmem : f n ∈ {k : ℕ | Attainable n k} := by
      rw [f, if_neg hn]
      exact Nat.sSup_mem (attainable_nonempty n) (attainable_bddAbove n hn)
    exact attainable_cast_le n (f n) hn hmem

end

/-! ### Upstream module `JSP620/Circles.lean` -/

section
/-!
# Two orthogonal circles in `ℝ⁴` (the Lenz construction)

Supporting geometry for the lower bound in Erdős Problem 754 / JSP-000620.

Points of the two circles are encoded by complex numbers `w` with `normSq w = 1 / 2`:
`e1 w = (w.re, w.im, 0, 0)` lies on the circle in the first coordinate plane and
`e2 w = (0, 0, w.re, w.im)` on the circle in the second coordinate plane.  Any point of
the first circle is at distance one from every point of the second circle, and the
rotation by a right angle (`w ↦ w * I`) moves a point of a circle to a point at
distance one on the same circle.
-/

open _root_.Complex _root_.Finset

namespace Erdos754Lower

/-- The common radius `1 / √2` of the two circles. -/
noncomputable def ρ : ℝ := (Real.sqrt 2)⁻¹

lemma ρ_pos : 0 < ρ := by
  unfold ρ
  positivity

lemma ρ_ne_zero : ρ ≠ 0 := ρ_pos.ne'

lemma ρ_mul_self : ρ * ρ = 1 / 2 := by
  unfold ρ
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- A point of the first circle, placed in the first coordinate plane of `ℝ⁴`. -/
noncomputable def e1 (w : ℂ) : E4 := !₂[w.re, w.im, 0, 0]

/-- A point of the second circle, placed in the second coordinate plane of `ℝ⁴`. -/
noncomputable def e2 (w : ℂ) : E4 := !₂[0, 0, w.re, w.im]

@[simp] lemma e1_zero (w : ℂ) : e1 w 0 = w.re := rfl
@[simp] lemma e1_one (w : ℂ) : e1 w 1 = w.im := rfl
@[simp] lemma e1_two (w : ℂ) : e1 w 2 = 0 := rfl
@[simp] lemma e1_three (w : ℂ) : e1 w 3 = 0 := rfl
@[simp] lemma e2_zero (w : ℂ) : e2 w 0 = 0 := rfl
@[simp] lemma e2_one (w : ℂ) : e2 w 1 = 0 := rfl
@[simp] lemma e2_two (w : ℂ) : e2 w 2 = w.re := rfl
@[simp] lemma e2_three (w : ℂ) : e2 w 3 = w.im := rfl

lemma e1_injective : Function.Injective e1 := by
  intro w v h
  have h0 := congrArg (fun x : E4 => x 0) h
  have h1 := congrArg (fun x : E4 => x 1) h
  simp only [e1_zero, e1_one] at h0 h1
  exact Complex.ext h0 h1

lemma e2_injective : Function.Injective e2 := by
  intro w v h
  have h0 := congrArg (fun x : E4 => x 2) h
  have h1 := congrArg (fun x : E4 => x 3) h
  simp only [e2_two, e2_three] at h0 h1
  exact Complex.ext h0 h1

lemma e1_ne_e2 {w v : ℂ} (hw : w ≠ 0) : e1 w ≠ e2 v := by
  intro h
  have h0 := congrArg (fun x : E4 => x 0) h
  have h1 := congrArg (fun x : E4 => x 1) h
  simp only [e1_zero, e1_one, e2_zero, e2_one] at h0 h1
  exact hw (Complex.ext h0 h1)

lemma dist_sq_e1_e1 (w v : ℂ) : dist (e1 w) (e1 v) ^ 2 = normSq (w - v) := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_four]
  simp only [e1_zero, e1_one, e1_two, e1_three, Real.dist_eq, sq_abs, normSq_apply,
    Complex.sub_re, Complex.sub_im]
  ring

lemma dist_sq_e2_e2 (w v : ℂ) : dist (e2 w) (e2 v) ^ 2 = normSq (w - v) := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_four]
  simp only [e2_zero, e2_one, e2_two, e2_three, Real.dist_eq, sq_abs, normSq_apply,
    Complex.sub_re, Complex.sub_im]
  ring

lemma dist_sq_e1_e2 (w v : ℂ) : dist (e1 w) (e2 v) ^ 2 = normSq w + normSq v := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_four]
  simp only [e1_zero, e1_one, e1_two, e1_three, e2_zero, e2_one, e2_two, e2_three,
    Real.dist_eq, sq_abs, normSq_apply]
  ring

lemma dist_eq_one_of_sq {x y : E4} (h : dist x y ^ 2 = 1) : dist x y = 1 := by
  have := (pow_left_inj₀ dist_nonneg zero_le_one two_ne_zero).mp (by rw [h]; norm_num)
  exact this

lemma dist_e1_e2 {w v : ℂ} (hw : normSq w = 1 / 2) (hv : normSq v = 1 / 2) :
    dist (e1 w) (e2 v) = 1 := by
  apply dist_eq_one_of_sq
  rw [dist_sq_e1_e2, hw, hv]
  norm_num

lemma dist_e2_e1 {w v : ℂ} (hw : normSq w = 1 / 2) (hv : normSq v = 1 / 2) :
    dist (e2 w) (e1 v) = 1 := by
  rw [dist_comm]
  exact dist_e1_e2 hv hw

lemma normSq_sub_mul_I (w : ℂ) : normSq (w - w * I) = 2 * normSq w := by
  have : w - w * I = w * (1 - I) := by ring
  rw [this, normSq_mul]
  simp [normSq_apply]
  ring

lemma normSq_sub_mul_neg_I (w : ℂ) : normSq (w - w * (-I)) = 2 * normSq w := by
  have : w - w * (-I) = w * (1 + I) := by ring
  rw [this, normSq_mul]
  simp [normSq_apply]
  ring

lemma dist_e1_rot {w : ℂ} (hw : normSq w = 1 / 2) : dist (e1 w) (e1 (w * I)) = 1 := by
  apply dist_eq_one_of_sq
  rw [dist_sq_e1_e1, normSq_sub_mul_I, hw]
  norm_num

lemma dist_e1_rot' {w : ℂ} (hw : normSq w = 1 / 2) : dist (e1 w) (e1 (w * (-I))) = 1 := by
  apply dist_eq_one_of_sq
  rw [dist_sq_e1_e1, normSq_sub_mul_neg_I, hw]
  norm_num

lemma dist_e2_rot {w : ℂ} (hw : normSq w = 1 / 2) : dist (e2 w) (e2 (w * I)) = 1 := by
  apply dist_eq_one_of_sq
  rw [dist_sq_e2_e2, normSq_sub_mul_I, hw]
  norm_num

lemma dist_e2_rot' {w : ℂ} (hw : normSq w = 1 / 2) : dist (e2 w) (e2 (w * (-I))) = 1 := by
  apply dist_eq_one_of_sq
  rw [dist_sq_e2_e2, normSq_sub_mul_neg_I, hw]
  norm_num

lemma ne_zero_of_normSq {w : ℂ} (hw : normSq w = 1 / 2) : w ≠ 0 := by
  intro h
  rw [h, normSq_zero] at hw
  norm_num at hw

lemma mul_I_ne_self {w : ℂ} (hw : w ≠ 0) : w * I ≠ w := by
  intro h
  have : w * (I - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h0 | h0
  · exact hw h0
  · have := congrArg Complex.re h0
    simp at this

lemma mul_neg_I_ne_self {w : ℂ} (hw : w ≠ 0) : w * (-I) ≠ w := by
  intro h
  have : w * (-I - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h0 | h0
  · exact hw h0
  · have := congrArg Complex.re h0
    simp at this

lemma mul_I_ne_mul_neg_I {w : ℂ} (hw : w ≠ 0) : w * I ≠ w * (-I) := by
  intro h
  have : w * (2 * I) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h0 | h0
  · exact hw h0
  · have := congrArg Complex.im h0
    simp at this

end Erdos754Lower

end

/-! ### Upstream module `JSP620/Construction.lean` -/

section
/-!
# The Avis–Erdős–Pach lower bound for Erdős Problem 754 (JSP-000620)

Let `f n` be the largest `k` such that some set of `n` points in `ℝ⁴` has, at every
point `x`, at least `k` other points at one common distance depending on `x`
(`Erdos754.f`, the definition used by the existing upper-bound formalization).

We formalize the classical lower-bound construction: two orthogonal circles of radius
`1 / √2` in `ℝ⁴`, each carrying finitely many points.  Every point of one circle is at
distance one from every point of the other circle.  Taking `⌈n/2⌉` and `⌊n/2⌋` points
gives `⌊n/2⌋ ≤ f n` for all `n`.  Taking the vertices of `k` inscribed squares on each
circle (all `4k`-th roots of unity, rescaled) additionally gives every point two
neighbours at distance one on its own circle, hence `n/2 + 2 ≤ f n` whenever `8 ∣ n`.
Combined with the existing upper bound `f n ≤ n/2 + 202` this settles
`f n = n/2 + O(1)`.
-/

open _root_.Complex _root_.Finset

namespace Erdos754Lower

open Erdos754

/-! ## Rescaled roots of unity on a circle -/

/-- A primitive `N`-th root of unity. -/
noncomputable def ζ (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / N)

lemma ζ_isPrimitiveRoot (N : ℕ) (hN : N ≠ 0) : IsPrimitiveRoot (ζ N) N :=
  Complex.isPrimitiveRoot_exp N hN

lemma normSq_ζ_pow (N : ℕ) (hN : N ≠ 0) (m : ℕ) : normSq (ζ N ^ m) = 1 := by
  rw [normSq_eq_norm_sq, norm_pow, (ζ_isPrimitiveRoot N hN).norm'_eq_one hN, one_pow, one_pow]

/-- The `m`-th of `N` equally spaced points on the circle of radius `1 / √2`. -/
noncomputable def pt (N m : ℕ) : ℂ := (ρ : ℂ) * ζ N ^ m

lemma normSq_pt (N : ℕ) (hN : N ≠ 0) (m : ℕ) : normSq (pt N m) = 1 / 2 := by
  rw [pt, normSq_mul, normSq_ofReal, ρ_mul_self, normSq_ζ_pow N hN m, mul_one]

lemma pt_injOn (N : ℕ) (hN : N ≠ 0) : Set.InjOn (pt N) (range N) := by
  intro i hi j hj h
  have hρ : (ρ : ℂ) ≠ 0 := by exact_mod_cast ρ_ne_zero
  have h' : ζ N ^ i = ζ N ^ j := mul_left_cancel₀ hρ h
  exact (ζ_isPrimitiveRoot N hN).pow_inj (mem_range.mp hi) (mem_range.mp hj) h'

/-- `N` distinct points on the circle of radius `1 / √2`. -/
noncomputable def circ (N : ℕ) : Finset ℂ := (range N).image (pt N)

lemma card_circ (N : ℕ) (hN : N ≠ 0) : (circ N).card = N := by
  rw [circ, card_image_of_injOn (pt_injOn N hN), card_range]

lemma normSq_of_mem_circ {N : ℕ} (hN : N ≠ 0) {w : ℂ} (hw : w ∈ circ N) :
    normSq w = 1 / 2 := by
  obtain ⟨m, -, rfl⟩ := mem_image.mp hw
  exact normSq_pt N hN m

/-! ## Rotation by a right angle on `4k` points -/

lemma ζ_pow_quarter (k : ℕ) (hk : k ≠ 0) : ζ (4 * k) ^ k = I := by
  unfold ζ
  rw [← Complex.exp_nat_mul]
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have : (k : ℂ) * (2 * Real.pi * I / ((4 * k : ℕ) : ℂ)) = ((Real.pi / 2 : ℝ) : ℂ) * I := by
    push_cast
    field_simp
    ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

lemma ζ_pow_three_quarter (k : ℕ) (hk : k ≠ 0) : ζ (4 * k) ^ (3 * k) = -I := by
  rw [pow_mul', ζ_pow_quarter k hk, pow_succ, I_sq]
  ring

lemma ζ_pow_full (k : ℕ) (hk : k ≠ 0) : ζ (4 * k) ^ (4 * k) = 1 :=
  (ζ_isPrimitiveRoot (4 * k) (by omega)).pow_eq_one

lemma pt_mul_I (k : ℕ) (hk : k ≠ 0) (m : ℕ) :
    pt (4 * k) m * I = pt (4 * k) ((m + k) % (4 * k)) := by
  rw [pt, pt, mul_assoc, ← ζ_pow_quarter k hk, ← pow_add,
    pow_eq_pow_mod (m + k) (ζ_pow_full k hk)]

lemma pt_mul_neg_I (k : ℕ) (hk : k ≠ 0) (m : ℕ) :
    pt (4 * k) m * (-I) = pt (4 * k) ((m + 3 * k) % (4 * k)) := by
  rw [pt, pt, mul_assoc, ← ζ_pow_three_quarter k hk, ← pow_add,
    pow_eq_pow_mod (m + 3 * k) (ζ_pow_full k hk)]

lemma mul_I_mem_circ {k : ℕ} (hk : k ≠ 0) {w : ℂ} (hw : w ∈ circ (4 * k)) :
    w * I ∈ circ (4 * k) := by
  obtain ⟨m, -, rfl⟩ := mem_image.mp hw
  rw [pt_mul_I k hk m]
  exact mem_image.mpr ⟨_, mem_range.mpr (Nat.mod_lt _ (by omega)), rfl⟩

lemma mul_neg_I_mem_circ {k : ℕ} (hk : k ≠ 0) {w : ℂ} (hw : w ∈ circ (4 * k)) :
    w * (-I) ∈ circ (4 * k) := by
  obtain ⟨m, -, rfl⟩ := mem_image.mp hw
  rw [pt_mul_neg_I k hk m]
  exact mem_image.mpr ⟨_, mem_range.mpr (Nat.mod_lt _ (by omega)), rfl⟩

/-! ## The point set and its favorite-distance degrees -/

/-- The two-circle point set determined by parameter sets `X` (first circle) and
`Y` (second circle). -/
noncomputable def pts (X Y : Finset ℂ) : Finset E4 := X.image e1 ∪ Y.image e2

/-- A parameter set lies on the circle of radius `1 / √2`. -/
def OnCircle (X : Finset ℂ) : Prop := ∀ w ∈ X, normSq w = 1 / 2

lemma onCircle_circ (N : ℕ) (hN : N ≠ 0) : OnCircle (circ N) :=
  fun _ hw => normSq_of_mem_circ hN hw

lemma disjoint_images {X Y : Finset ℂ} (hX : OnCircle X) :
    Disjoint (X.image e1) (Y.image e2) := by
  rw [disjoint_left]
  intro x hx hy
  obtain ⟨w, hw, rfl⟩ := mem_image.mp hx
  obtain ⟨v, -, hvx⟩ := mem_image.mp hy
  exact e1_ne_e2 (ne_zero_of_normSq (hX w hw)) hvx.symm

lemma card_pts {X Y : Finset ℂ} (hX : OnCircle X) : (pts X Y).card = X.card + Y.card := by
  rw [pts, card_union_of_disjoint (disjoint_images hX),
    card_image_of_injective _ e1_injective, card_image_of_injective _ e2_injective]

/-- The number of points of `P` other than `x` at distance one from `x`. -/
noncomputable def unitDeg (P : Finset E4) (x : E4) : ℕ :=
  open scoped Classical in
  (P.filter fun y => y ≠ x ∧ dist x y = 1).card

/-- With the constant favorite distance one, `Erdos754.favoriteDegree` is `unitDeg`. -/
lemma favoriteDegree_const_one (P : Finset E4) (x : P) :
    favoriteDegree P (fun _ => (1 : ℝ)) x = unitDeg P x := by
  classical
  unfold favoriteDegree unitDeg
  refine Finset.card_bij (fun y _ => (y : E4)) ?_ ?_ ?_
  · intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    refine Finset.mem_filter.mpr ⟨y.property, ?_, hy'.2⟩
    intro h
    exact hy'.1 (Subtype.ext h.symm)
  · intro y₁ _ y₂ _ h
    exact Subtype.ext h
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    refine ⟨⟨y, hy'.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hy'.2.2⟩, rfl⟩
    intro h
    exact hy'.2.1 (congrArg Subtype.val h).symm

lemma card_le_unitDeg {P T : Finset E4} {x : E4} (hT : T ⊆ P)
    (hne : ∀ y ∈ T, y ≠ x) (hd : ∀ y ∈ T, dist x y = 1) : T.card ≤ unitDeg P x := by
  classical
  unfold unitDeg
  apply Finset.card_le_card
  intro y hy
  exact Finset.mem_filter.mpr ⟨hT hy, hne y hy, hd y hy⟩

lemma unitDeg_e1_ge {X Y : Finset ℂ} (hX : OnCircle X) (hY : OnCircle Y) {w : ℂ}
    (hw : w ∈ X) : Y.card ≤ unitDeg (pts X Y) (e1 w) := by
  have h := card_le_unitDeg (P := pts X Y) (T := Y.image e2) (x := e1 w)
    (fun y hy => Finset.mem_union_right _ hy)
    (by
      intro y hy
      obtain ⟨v, -, rfl⟩ := mem_image.mp hy
      exact (e1_ne_e2 (ne_zero_of_normSq (hX w hw))).symm)
    (by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
      exact dist_e1_e2 (hX w hw) (hY v hv))
  rwa [card_image_of_injective _ e2_injective] at h

lemma unitDeg_e2_ge {X Y : Finset ℂ} (hX : OnCircle X) (hY : OnCircle Y) {v : ℂ}
    (hv : v ∈ Y) : X.card ≤ unitDeg (pts X Y) (e2 v) := by
  have h := card_le_unitDeg (P := pts X Y) (T := X.image e1) (x := e2 v)
    (fun y hy => Finset.mem_union_left _ hy)
    (by
      intro y hy
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hy
      exact e1_ne_e2 (ne_zero_of_normSq (hX w hw)))
    (by
      intro y hy
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hy
      exact dist_e2_e1 (hY v hv) (hX w hw))
  rwa [card_image_of_injective _ e1_injective] at h

/-- A parameter set closed under rotation by a right angle. -/
def RotClosed (X : Finset ℂ) : Prop := ∀ w ∈ X, w * I ∈ X ∧ w * (-I) ∈ X

lemma rotClosed_circ (k : ℕ) (hk : k ≠ 0) : RotClosed (circ (4 * k)) :=
  fun _ hw => ⟨mul_I_mem_circ hk hw, mul_neg_I_mem_circ hk hw⟩

lemma unitDeg_e1_ge_rot {X Y : Finset ℂ} (hX : OnCircle X) (hY : OnCircle Y)
    (hXr : RotClosed X) {w : ℂ} (hw : w ∈ X) :
    Y.card + 2 ≤ unitDeg (pts X Y) (e1 w) := by
  classical
  have hw0 : w ≠ 0 := ne_zero_of_normSq (hX w hw)
  have hwI := (hXr w hw).1
  have hwI' := (hXr w hw).2
  have hnot1 : e1 (w * I) ∉ Y.image e2 := by
    intro h
    obtain ⟨v, -, hv⟩ := mem_image.mp h
    exact e1_ne_e2 (ne_zero_of_normSq (hX _ hwI)) hv.symm
  have hnot2 : e1 (w * (-I)) ∉ insert (e1 (w * I)) (Y.image e2) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact mul_I_ne_mul_neg_I hw0 (e1_injective h).symm
    · obtain ⟨v, -, hv⟩ := mem_image.mp h
      exact e1_ne_e2 (ne_zero_of_normSq (hX _ hwI')) hv.symm
  have h := card_le_unitDeg (P := pts X Y)
    (T := insert (e1 (w * (-I))) (insert (e1 (w * I)) (Y.image e2))) (x := e1 w)
    (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_union_left _ (mem_image.mpr ⟨_, hwI', rfl⟩)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_union_left _ (mem_image.mpr ⟨_, hwI, rfl⟩)
      · exact Finset.mem_union_right _ hy)
    (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · intro h
        exact mul_neg_I_ne_self hw0 (e1_injective h)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · intro h
        exact mul_I_ne_self hw0 (e1_injective h)
      · obtain ⟨v, -, rfl⟩ := mem_image.mp hy
        exact (e1_ne_e2 hw0).symm)
    (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact dist_e1_rot' (hX w hw)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact dist_e1_rot (hX w hw)
      · obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
        exact dist_e1_e2 (hX w hw) (hY v hv))
  rwa [card_insert_of_notMem hnot2, card_insert_of_notMem hnot1,
    card_image_of_injective _ e2_injective] at h

lemma unitDeg_e2_ge_rot {X Y : Finset ℂ} (hX : OnCircle X) (hY : OnCircle Y)
    (hYr : RotClosed Y) {v : ℂ} (hv : v ∈ Y) :
    X.card + 2 ≤ unitDeg (pts X Y) (e2 v) := by
  classical
  have hv0 : v ≠ 0 := ne_zero_of_normSq (hY v hv)
  have hvI := (hYr v hv).1
  have hvI' := (hYr v hv).2
  have hnot1 : e2 (v * I) ∉ X.image e1 := by
    intro h
    obtain ⟨w, hw, hw'⟩ := mem_image.mp h
    exact e1_ne_e2 (ne_zero_of_normSq (hX w hw)) hw'
  have hnot2 : e2 (v * (-I)) ∉ insert (e2 (v * I)) (X.image e1) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact mul_I_ne_mul_neg_I hv0 (e2_injective h).symm
    · obtain ⟨w, hw, hw'⟩ := mem_image.mp h
      exact e1_ne_e2 (ne_zero_of_normSq (hX w hw)) hw'
  have h := card_le_unitDeg (P := pts X Y)
    (T := insert (e2 (v * (-I))) (insert (e2 (v * I)) (X.image e1))) (x := e2 v)
    (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_union_right _ (mem_image.mpr ⟨_, hvI', rfl⟩)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_union_right _ (mem_image.mpr ⟨_, hvI, rfl⟩)
      · exact Finset.mem_union_left _ hy)
    (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · intro h
        exact mul_neg_I_ne_self hv0 (e2_injective h)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · intro h
        exact mul_I_ne_self hv0 (e2_injective h)
      · obtain ⟨w, hw, rfl⟩ := mem_image.mp hy
        exact e1_ne_e2 (ne_zero_of_normSq (hX w hw)))
    (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact dist_e2_rot' (hY v hv)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact dist_e2_rot (hY v hv)
      · obtain ⟨w, hw, rfl⟩ := mem_image.mp hy
        exact dist_e2_e1 (hY v hv) (hX w hw))
  rwa [card_insert_of_notMem hnot2, card_insert_of_notMem hnot1,
    card_image_of_injective _ e1_injective] at h

/-! ## Attainable values -/

lemma attainable_of_forall_unitDeg {P : Finset E4} {k : ℕ}
    (h : ∀ x ∈ P, k ≤ unitDeg P x) : Attainable P.card k := by
  refine ⟨P, rfl, fun _ => 1, fun _ => one_pos, fun x => ?_⟩
  rw [favoriteDegree_const_one]
  exact h x x.property

lemma forall_mem_pts {X Y : Finset ℂ} {p : E4 → Prop}
    (h1 : ∀ w ∈ X, p (e1 w)) (h2 : ∀ v ∈ Y, p (e2 v)) : ∀ x ∈ pts X Y, p x := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨w, hw, rfl⟩ := mem_image.mp hx
    exact h1 w hw
  · obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
    exact h2 v hv

/-- Two circles carrying `a` and `b` points: every point has at least `min a b` others
at distance one. -/
lemma attainable_two_circles (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Attainable (a + b) (min a b) := by
  have hX := onCircle_circ a ha
  have hY := onCircle_circ b hb
  have hcard : (pts (circ a) (circ b)).card = a + b := by
    rw [card_pts hX, card_circ a ha, card_circ b hb]
  rw [← hcard]
  apply attainable_of_forall_unitDeg
  apply forall_mem_pts
  · intro w hw
    exact le_trans (by rw [card_circ b hb]; exact min_le_right a b) (unitDeg_e1_ge hX hY hw)
  · intro v hv
    exact le_trans (by rw [card_circ a ha]; exact min_le_left a b) (unitDeg_e2_ge hX hY hv)

/-- Two circles each carrying the vertices of `k` inscribed squares: every point has at
least `4k + 2` others at distance one. -/
lemma attainable_squares (k : ℕ) (hk : k ≠ 0) : Attainable (8 * k) (4 * k + 2) := by
  have h4 : 4 * k ≠ 0 := by omega
  have hX := onCircle_circ (4 * k) h4
  have hXr := rotClosed_circ k hk
  have hcard : (pts (circ (4 * k)) (circ (4 * k))).card = 8 * k := by
    rw [card_pts hX, card_circ _ h4]
    ring
  rw [← hcard]
  apply attainable_of_forall_unitDeg
  apply forall_mem_pts
  · intro w hw
    have := unitDeg_e1_ge_rot hX hX hXr hw
    rwa [card_circ _ h4] at this
  · intro v hv
    have := unitDeg_e2_ge_rot hX hX hXr hv
    rwa [card_circ _ h4] at this

lemma le_f_of_attainable {n k : ℕ} (hn : n ≠ 0) (h : Attainable n k) : k ≤ f n := by
  have hf : f n = sSup {k : ℕ | Attainable n k} := by simp [f, hn]
  rw [hf]
  exact le_csSup (attainable_bddAbove n hn) h

/-! ## The lower bounds -/

/-- For every `n`, some `n`-point set in `ℝ⁴` has every point at distance one from at
least `⌊n/2⌋` other points. -/
theorem half_le_f (n : ℕ) : n / 2 ≤ f n := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · have hb : n / 2 ≠ 0 := by omega
    have ha : n - n / 2 ≠ 0 := by omega
    have h := attainable_two_circles (n - n / 2) (n / 2) ha hb
    have hsum : n - n / 2 + n / 2 = n := by omega
    have hmin : min (n - n / 2) (n / 2) = n / 2 := by
      apply min_eq_right
      omega
    rw [hsum, hmin] at h
    exact le_f_of_attainable (by omega) h

/-- For `n = 8k` with `k ≥ 1`, some `n`-point set in `ℝ⁴` has every point at distance
one from at least `n/2 + 2` other points (Avis–Erdős–Pach). -/
theorem f_eight_mul (k : ℕ) (hk : k ≠ 0) : 4 * k + 2 ≤ f (8 * k) :=
  le_f_of_attainable (by omega) (attainable_squares k hk)

theorem half_add_two_le_f_of_eight_dvd (n : ℕ) (hn : n ≠ 0) (h8 : 8 ∣ n) :
    n / 2 + 2 ≤ f n := by
  obtain ⟨k, rfl⟩ := h8
  have hk : k ≠ 0 := by omega
  have := f_eight_mul k hk
  have h2 : 8 * k / 2 = 4 * k := by omega
  rw [h2]
  exact this

end Erdos754Lower

end

/-! ### Upstream module `JSP620/Target.lean` -/

/-!
# Erdős Problem 754 (JSP-000620): the two-sided answer `f(n) = n/2 + O(1)`

`Erdos754.f n` is the largest `k` such that some `n`-point set in `ℝ⁴` has, at every
point, at least `k` other points at one distance chosen for that point.

* Lower bounds (this development, following Avis–Erdős–Pach 1988): `⌊n/2⌋ ≤ f n` for every
  `n`, and `n/2 + 2 ≤ f n` whenever `8 ∣ n`.
* Upper bound (existing formalization `Erdos754.erdos_754_upper` of Swanepoel's theorem, by
  Codex / GPT-5.6 Sol in plby/lean-proofs): `f n ≤ n/2 + 202`.

Together: `f n = n/2 + O(1)`, which is the answer to the catalog question.
-/

namespace Erdos754Lower

/-- The two-sided resolution of Erdős Problem 754: the lower bounds of Avis, Erdős and
Pach and the upper bound `f n ≤ n/2 + O(1)`. -/
theorem erdos_754_two_sided :
    (∀ n : ℕ, n / 2 ≤ f n) ∧
    (∀ n : ℕ, n ≠ 0 → 8 ∣ n → n / 2 + 2 ≤ f n) ∧
    (∃ C : ℝ, ∀ n : ℕ, (f n : ℝ) ≤ (n : ℝ) / 2 + C) :=
  ⟨half_le_f, half_add_two_le_f_of_eight_dvd, erdos_754_upper⟩

end Erdos754Lower

/-- Erdős Problem 754: `f n = n / 2 + O(1)`, with the Avis--Erdős--Pach lower bounds and
Swanepoel's upper bound. -/
theorem erdos_754 :
    (∀ n : ℕ, n / 2 ≤ f n) ∧
    (∀ n : ℕ, n ≠ 0 → 8 ∣ n → n / 2 + 2 ≤ f n) ∧
    (∃ C : ℝ, ∀ n : ℕ, (f n : ℝ) ≤ (n : ℝ) / 2 + C) :=
  Erdos754Lower.erdos_754_two_sided

#print axioms erdos_754
-- 'Erdos754.erdos_754' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos754
