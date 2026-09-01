import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos185

/-
# Problem Description

Erdős Problem 185, originally considered by Moser. Let `f₃(n)` be the maximal size of a
subset of `{0,1,2}ⁿ` containing no three points on a line. Is it true that `f₃(n) = o(3ⁿ)`?
`erdos_185` proves that it is.

The answer is yes, as a corollary of the density Hales--Jewett theorem of Furstenberg and
Katznelson. Moser had shown the lower bound `f₃(n) ≫ 3ⁿ / √n`, so the `o(3ⁿ)` is not far
from best possible.

"No three points on a line" is taken in the ordinary Euclidean sense: `IsMoserSet A` asks
that no three *distinct* points of `A` be `Collinear ℝ` after embedding the cube in
`Fin n → ℝ`, using Mathlib's own `Collinear`. `f3 n` is the `Finset.sup` of cardinalities
over the line-free subsets; that family contains `∅`, so the supremum is a real maximum
rather than a default `0`, and `card_le_f3` together with `exists_isMoserSet_card_eq_f3`
record that it both dominates and is attained.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos185/Definitions.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

/-!
# Erdős Problem 185: definitions and the finite extremal problem

This file gives the literal geometric formulation of the Moser problem in the
ternary cube.  In particular, `IsMoserSet` uses Euclidean collinearity after
embedding the entries `0`, `1`, and `2` in `ℝ`; it is not the weaker
condition of containing no Hales--Jewett combinatorial line.
-/

open Finset

noncomputable section

/-- A word of length `n` in the alphabet `{0, 1, 2}`. -/
abbrev Word (n : ℕ) := Fin n → Fin 3

/-- The literal coordinatewise embedding of the ternary cube in `ℝ^n`. -/
def toRealPoint {n : ℕ} (x : Word n) : Fin n → ℝ :=
  fun i ↦ ((x i : ℕ) : ℝ)

/--
A subset of the ternary cube is a Moser set if it contains no three distinct
points which are collinear in the ordinary real affine space.
-/
def IsMoserSet {n : ℕ} (A : Finset (Word n)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
    x ≠ y → x ≠ z → y ≠ z →
      ¬ Collinear ℝ
        ({toRealPoint x, toRealPoint y, toRealPoint z} : Set (Fin n → ℝ))

/-- The empty subset of a ternary cube is a Moser set. -/
@[simp] theorem isMoserSet_empty (n : ℕ) :
    IsMoserSet (∅ : Finset (Word n)) := by
  simp [IsMoserSet]

/-- The Moser property is inherited by subsets. -/
theorem IsMoserSet.mono {n : ℕ} {A B : Finset (Word n)}
    (hA : IsMoserSet A) (hBA : B ⊆ A) : IsMoserSet B := by
  intro x hx y hy z hz hxy hxz hyz
  exact hA x (hBA hx) y (hBA hy) z (hBA hz) hxy hxz hyz

/-- The ternary cube has exactly `3 ^ n` words. -/
@[simp] theorem cube_card (n : ℕ) :
    (Finset.univ : Finset (Word n)).card = 3 ^ n := by
  simp [Word]

/-- All admissible subsets of the `n`-dimensional ternary cube. -/
noncomputable def candidates (n : ℕ) : Finset (Finset (Word n)) := by
  classical
  exact (Finset.univ : Finset (Word n)).powerset.filter IsMoserSet

/-- Membership in `candidates` is exactly the geometric Moser property. -/
@[simp] theorem mem_candidates_iff {n : ℕ} {A : Finset (Word n)} :
    A ∈ candidates n ↔ IsMoserSet A := by
  simp [candidates]

/-- The candidate family is nonempty. -/
theorem candidates_nonempty (n : ℕ) : (candidates n).Nonempty := by
  exact ⟨∅, mem_candidates_iff.mpr (isMoserSet_empty n)⟩

/--
`f3 n` is the maximum cardinality of a subset of `{0,1,2}^n` containing no
three distinct geometrically collinear points.
-/
noncomputable def f3 (n : ℕ) : ℕ :=
  (candidates n).sup Finset.card

/-- Every geometrically line-free set has cardinality at most `f3 n`. -/
theorem card_le_f3 {n : ℕ} {A : Finset (Word n)}
    (hA : IsMoserSet A) : A.card ≤ f3 n := by
  exact Finset.le_sup (f := Finset.card) (mem_candidates_iff.mpr hA)

/-- There is a geometrically line-free set whose cardinality is `f3 n`. -/
theorem exists_isMoserSet_card_eq_f3 (n : ℕ) :
    ∃ A : Finset (Word n), IsMoserSet A ∧ A.card = f3 n := by
  obtain ⟨A, hA, hmax⟩ :=
    (candidates n).exists_max_image Finset.card (candidates_nonempty n)
  refine ⟨A, mem_candidates_iff.mp hA, le_antisymm ?_ ?_⟩
  · exact card_le_f3 (mem_candidates_iff.mp hA)
  · exact Finset.sup_le fun B hB ↦ hmax B hB

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos185/Geometry.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

/-!
# Combinatorial lines in the ternary cube are geometric lines

This file supplies the elementary bridge from Mathlib's Hales--Jewett
`Combinatorics.Line` to the literal Euclidean collinearity used in the
definition of a Moser set.  The wildcard coordinate required by a proper
combinatorial line also shows that its three ternary words are distinct.
-/

section
open Combinatorics.Line

/-- A proper combinatorial line over a nontrivial alphabet is injective. -/
private theorem _root_.Combinatorics.Line.injective {α ι : Type*} [Nontrivial α]
    (l : Combinatorics.Line α ι) : Function.Injective l := by
  intro x y hxy
  obtain ⟨i, hi⟩ := l.proper
  have hcoord := congrFun hxy i
  simpa only [apply_none l x i hi, apply_none l y i hi] using hcoord

end

open Finset

noncomputable section

/-- The words at parameters `0` and `1` of a ternary combinatorial line are distinct. -/
theorem combinatorialLine_zero_ne_one {n : ℕ}
    (l : Combinatorics.Line (Fin 3) (Fin n)) : l 0 ≠ l 1 :=
  l.injective.ne (by decide)

/-- The words at parameters `0` and `2` of a ternary combinatorial line are distinct. -/
theorem combinatorialLine_zero_ne_two {n : ℕ}
    (l : Combinatorics.Line (Fin 3) (Fin n)) : l 0 ≠ l 2 :=
  l.injective.ne (by decide)

/-- The words at parameters `1` and `2` of a ternary combinatorial line are distinct. -/
theorem combinatorialLine_one_ne_two {n : ℕ}
    (l : Combinatorics.Line (Fin 3) (Fin n)) : l 1 ≠ l 2 :=
  l.injective.ne (by decide)

/-- After the coordinatewise embedding into real space, the entire range of
a ternary combinatorial line is collinear. -/
theorem combinatorialLine_realRange_collinear {n : ℕ}
    (l : Combinatorics.Line (Fin 3) (Fin n)) :
    Collinear ℝ (Set.range fun t : Fin 3 ↦ toRealPoint (l t)) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨toRealPoint (l 0),
    toRealPoint (l 1) - toRealPoint (l 0), ?_⟩
  rintro _ ⟨t, rfl⟩
  refine ⟨((t : ℕ) : ℝ), ?_⟩
  ext i
  cases h : l.idxFun i <;>
    simp [toRealPoint, Combinatorics.Line.coe_apply, h]

/-- In particular, the three real points obtained at parameters `0`, `1`,
and `2` form a geometrically collinear triple. -/
theorem combinatorialLine_realPoints_collinear {n : ℕ}
    (l : Combinatorics.Line (Fin 3) (Fin n)) :
    Collinear ℝ
      ({toRealPoint (l 0), toRealPoint (l 1), toRealPoint (l 2)} :
        Set (Fin n → ℝ)) := by
  apply Collinear.subset _ (combinatorialLine_realRange_collinear l)
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

/-- A finite set contains a combinatorial line if it contains the full range
of some proper Mathlib combinatorial line. -/
def ContainsCombinatorialLine {n : ℕ} (A : Finset (Word n)) : Prop :=
  ∃ l : Combinatorics.Line (Fin 3) (Fin n),
    Set.range l ⊆ (A : Set (Word n))

/-- A geometric Moser set cannot contain a Hales--Jewett combinatorial line. -/
theorem IsMoserSet.not_containsCombinatorialLine {n : ℕ}
    {A : Finset (Word n)} (hA : IsMoserSet A) :
    ¬ ContainsCombinatorialLine A := by
  rintro ⟨l, hl⟩
  have h0 : l 0 ∈ A := hl ⟨0, rfl⟩
  have h1 : l 1 ∈ A := hl ⟨1, rfl⟩
  have h2 : l 2 ∈ A := hl ⟨2, rfl⟩
  exact hA (l 0) h0 (l 1) h1 (l 2) h2
    (combinatorialLine_zero_ne_one l)
    (combinatorialLine_zero_ne_two l)
    (combinatorialLine_one_ne_two l)
    (combinatorialLine_realPoints_collinear l)

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos185/Corollary.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

/-!
# The density-Hales--Jewett corollary for Erdős Problem 185

This file isolates the short final deduction from the density Hales--Jewett
theorem for the ternary alphabet.  `DensityHalesJewettThree` is a proposition;
the theorem below takes a proof of it as an ordinary local hypothesis.  A
later file can therefore supply the unconditional proof without putting any
unproved declaration in the environment.
-/

open Filter
open scoped Topology

noncomputable section

/-- The exact specialization of density Hales--Jewett needed for Problem 185:
every sufficiently high-dimensional subset of the ternary cube of density at
least `δ` contains a proper combinatorial line. -/
def DensityHalesJewettThree : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ A : Finset (Word n),
        δ * (3 : ℝ) ^ n ≤ (A.card : ℝ) →
          ContainsCombinatorialLine A

/-- Density Hales--Jewett for the three-letter alphabet implies that the
maximum size of a geometric-line-free subset of the ternary cube is little-o
of the size of the cube. -/
theorem f3_isLittleO_three_pow_of_densityHalesJewettThree
    (hDHJ : DensityHalesJewettThree) :
    Asymptotics.IsLittleO Filter.atTop
      (fun n : ℕ ↦ (f3 n : ℝ))
      (fun n : ℕ ↦ (3 : ℝ) ^ n) := by
  rw [Asymptotics.isLittleO_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := hDHJ δ hδ
  filter_upwards [eventually_ge_atTop N] with n hn
  obtain ⟨A, hA, hcard⟩ := exists_isMoserSet_card_eq_f3 n
  have hnotDense : ¬ δ * (3 : ℝ) ^ n ≤ (A.card : ℝ) := by
    intro hDense
    exact hA.not_containsCombinatorialLine (hN n hn A hDense)
  have hbound : (f3 n : ℝ) ≤ δ * (3 : ℝ) ^ n := by
    rw [← hcard]
    exact le_of_not_ge hnotDense
  have hf : |(f3 n : ℝ)| = (f3 n : ℝ) :=
    abs_of_nonneg (show (0 : ℝ) ≤ (f3 n : ℝ) from Nat.cast_nonneg _)
  have hg : |(3 : ℝ) ^ n| = (3 : ℝ) ^ n :=
    abs_of_nonneg (pow_nonneg (by norm_num) n)
  simpa only [Real.norm_eq_abs, hf, hg] using hbound

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/Basic.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Basic finite-word and combinatorial-line infrastructure for Erdős 171

This file fixes the concrete convention used in the formalization: a word in
`[t]^n` is a function `Fin n → Fin t`, and a combinatorial line is Mathlib's
proper `Combinatorics.Line (Fin t) (Fin n)`.  It also records the elementary
injectivity and composition facts used throughout the density argument.
-/

namespace Erdos171

open Set

/-- The discrete cube `[t]^n`, represented as words of length `n` over `Fin t`. -/
abbrev Word (t n : ℕ) := Fin n → Fin t

/-- A set of words contains a (proper) combinatorial line. -/
def ContainsLine {t n : ℕ} (A : Set (Word t n)) : Prop :=
  ∃ l : Combinatorics.Line (Fin t) (Fin n), Set.range l ⊆ A

theorem containsLine_iff {t n : ℕ} {A : Set (Word t n)} :
    ContainsLine A ↔
      ∃ l : Combinatorics.Line (Fin t) (Fin n), ∀ a : Fin t, l a ∈ A := by
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l, fun a ↦ hl ⟨a, rfl⟩⟩
  · rintro ⟨l, hl⟩
    refine ⟨l, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact hl a

theorem ContainsLine.mono {t n : ℕ} {A B : Set (Word t n)}
    (hA : ContainsLine A) (hAB : A ⊆ B) : ContainsLine B := by
  obtain ⟨l, hl⟩ := hA
  exact ⟨l, hl.trans hAB⟩

theorem containsLine_coe_finset_iff {t n : ℕ} {A : Finset (Word t n)} :
    ContainsLine (A : Set (Word t n)) ↔
      ∃ l : Combinatorics.Line (Fin t) (Fin n), ∀ a : Fin t, l a ∈ A := by
  simpa only [Finset.mem_coe] using (containsLine_iff (A := (A : Set (Word t n))))

@[simp] theorem card_word (t n : ℕ) : Fintype.card (Word t n) = t ^ n := by
  simp [Word]

end Erdos171

section
open Combinatorics

section
open Combinatorics.Line

/-- The collection of lines in a finite cube is finite. -/
private noncomputable instance _root_.Combinatorics.Line.instFintype {α ι : Type*} [Fintype α] [Fintype ι] :
    Fintype (Line α ι) := by
  classical
  exact Fintype.ofInjective Line.idxFun fun _ _ h ↦ Line.ext h

/-- A line template without any wildcard coordinates. -/
private def _root_.Combinatorics.Line.NoWildcard {α ι : Type*} (f : ι → Option α) : Prop :=
  ∀ i, f i ≠ none

/-- A line is exactly a template which is not wildcard-free. -/
private noncomputable def _root_.Combinatorics.Line.templateEquiv {α ι : Type*} :
    Line α ι ≃ {f : ι → Option α // ¬ NoWildcard f} where
  toFun l := ⟨l.idxFun, by
    intro h
    obtain ⟨i, hi⟩ := l.proper
    exact h i hi⟩
  invFun f :=
    { idxFun := f
      proper := by
        classical
        simpa only [NoWildcard, not_forall, not_ne_iff] using f.property }
  left_inv l := by
    apply Line.ext
    rfl
  right_inv f := by
    apply Subtype.ext
    rfl

/-- Wildcard-free templates are exactly ordinary words. -/
private noncomputable def _root_.Combinatorics.Line.fixedTemplateEquiv {α ι : Type*} :
    (ι → α) ≃ {f : ι → Option α // NoWildcard f} where
  toFun x := ⟨fun i ↦ some (x i), fun _ ↦ Option.some_ne_none _⟩
  invFun f i := (f.1 i).get (Option.ne_none_iff_isSome.mp (f.2 i))
  left_inv x := by
    funext i
    rfl
  right_inv f := by
    apply Subtype.ext
    funext i
    exact Option.some_get _

/-- The number of proper line templates is the number of all templates minus
the number of wildcard-free templates. -/
private theorem _root_.Combinatorics.Line.card_eq_templates_sub_words {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι] :
    Fintype.card (Line α ι) =
      (Fintype.card α + 1) ^ Fintype.card ι -
        Fintype.card α ^ Fintype.card ι := by
  classical
  rw [Fintype.card_congr (templateEquiv (α := α) (ι := ι))]
  rw [Fintype.card_subtype_compl (NoWildcard (α := α) (ι := ι))]
  rw [← Fintype.card_congr (fixedTemplateEquiv (α := α) (ι := ι))]
  simp

/-- In `[k]^m` there are `(k+1)^m-k^m` proper combinatorial lines. -/
@[simp] private theorem _root_.Combinatorics.Line.card_fin (k m : ℕ) :
    Fintype.card (Line (Fin k) (Fin m)) = (k + 1) ^ m - k ^ m := by
  simpa using
    (card_eq_templates_sub_words (α := Fin k) (ι := Fin m))

/-- A proper combinatorial line is injective in its alphabet parameter. -/
private theorem _root_.Combinatorics.Line.parameter_injective {α ι : Type*} (l : Line α ι) : Function.Injective l := by
  intro a b hab
  obtain ⟨i, hi⟩ := l.proper
  have hiab := congrFun hab i
  simpa only [l.apply_none a i hi, l.apply_none b i hi] using hiab

end

section
open Combinatorics.Subspace

/-- The collection of subspaces between finite cubes is finite. -/
private noncomputable instance _root_.Combinatorics.Subspace.instFintype {η α ι : Type*} [Fintype η] [Fintype α]
    [Fintype ι] : Fintype (Subspace η α ι) := by
  classical
  exact Fintype.ofInjective Subspace.idxFun fun _ _ h ↦ Subspace.ext h

/-- Evaluation on a proper subspace is injective in the parameter word. -/
private theorem _root_.Combinatorics.Subspace.parameter_injective {η α ι : Type*} (U : Subspace η α ι) :
    Function.Injective U := by
  intro x y hxy
  funext e
  obtain ⟨i, hi⟩ := U.proper e
  have hcoord := congrFun hxy i
  simpa only [U.apply_inr (x := x) hi, U.apply_inr (x := y) hi] using hcoord

/-- Compose a line in the parameter cube with a combinatorial subspace. -/
private def _root_.Combinatorics.Subspace.lineMap {η α ι : Type*} (U : Subspace η α ι) (l : Line α η) : Line α ι where
  idxFun i := (U.idxFun i).elim some l.idxFun
  proper := by
    obtain ⟨e, he⟩ := l.proper
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨i, by simp [hi, he]⟩

@[simp] private theorem _root_.Combinatorics.Subspace.lineMap_idxFun_inl {η α ι : Type*} (U : Subspace η α ι)
    (l : Line α η) {i : ι} {a : α} (hi : U.idxFun i = Sum.inl a) :
    (U.lineMap l).idxFun i = some a := by
  simp [lineMap, hi]

@[simp] private theorem _root_.Combinatorics.Subspace.lineMap_idxFun_inr {η α ι : Type*} (U : Subspace η α ι)
    (l : Line α η) {i : ι} {e : η} (hi : U.idxFun i = Sum.inr e) :
    (U.lineMap l).idxFun i = l.idxFun e := by
  simp [lineMap, hi]

@[simp] private theorem _root_.Combinatorics.Subspace.lineMap_apply {η α ι : Type*} (U : Subspace η α ι)
    (l : Line α η) (a : α) : U.lineMap l a = U (l a) := by
  funext i
  cases hi : U.idxFun i with
  | inl b => simp [lineMap, Line.coe_apply, Subspace.coe_apply, hi]
  | inr e =>
      cases he : l.idxFun e <;>
        simp [lineMap, Line.coe_apply, Subspace.coe_apply, hi, he]

end

end

namespace Erdos171

/-- Embed a word over `Fin k` into the same-length cube over `Fin (k+1)`. -/
def restrictWord {k m : ℕ} (w : Word k m) : Word (k + 1) m :=
  fun i ↦ Fin.castSucc (w i)

theorem restrictWord_injective {k m : ℕ} : Function.Injective (restrictWord (k := k) (m := m)) := by
  intro x y h
  funext i
  exact Fin.castSucc_inj.mp (by simpa only [restrictWord] using congrFun h i)

/-- A word over `Fin (k+1)` lies entirely in its initial `Fin k` alphabet. -/
def IsRestrictedWord {k m : ℕ} (w : Word (k + 1) m) : Prop :=
  ∀ i, w i ≠ Fin.last k

/-- Ordinary `Fin k` words are equivalent to `Fin (k+1)` words which avoid the
new last letter. -/
noncomputable def restrictedWordEquiv (k m : ℕ) :
    Word k m ≃ {w : Word (k + 1) m // IsRestrictedWord w} where
  toFun w := ⟨restrictWord w, fun i ↦ Fin.castSucc_ne_last (w i)⟩
  invFun w := fun i ↦ (w.1 i).castPred (w.2 i)
  left_inv w := by
    funext i
    exact Fin.castPred_castSucc
  right_inv w := by
    apply Subtype.ext
    funext i
    exact Fin.castSucc_castPred (w.1 i) (w.2 i)

theorem range_restrictWord {k m : ℕ} :
    Set.range (restrictWord (k := k) (m := m)) =
      {w : Word (k + 1) m | IsRestrictedWord w} := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    exact fun i ↦ Fin.castSucc_ne_last (v i)
  · intro hw
    let w' : {w : Word (k + 1) m // IsRestrictedWord w} := ⟨w, hw⟩
    refine ⟨(restrictedWordEquiv k m).symm w', ?_⟩
    exact congrArg Subtype.val ((restrictedWordEquiv k m).apply_symm_apply w')

/-- Replace every wildcard in a line template by the new last letter.  This is
the endpoint at the additional letter in the density-Hales--Jewett argument. -/
def templateEndpoint {k m : ℕ} (l : Combinatorics.Line (Fin k) (Fin m)) :
    Word (k + 1) m :=
  fun i ↦ finSuccEquivLast.symm (l.idxFun i)

/-- Regard an internal `Fin k` line template as a line over `Fin (k+1)` by
embedding all of its fixed letters. -/
def templateExtension {k m : ℕ} (l : Combinatorics.Line (Fin k) (Fin m)) :
    Combinatorics.Line (Fin (k + 1)) (Fin m) :=
  l.map Fin.castSucc

@[simp] theorem templateExtension_castSucc {k m : ℕ}
    (l : Combinatorics.Line (Fin k) (Fin m)) (a : Fin k) :
    templateExtension l (Fin.castSucc a) = restrictWord (l a) := by
  funext i
  cases hi : l.idxFun i with
  | none =>
      simp [templateExtension, restrictWord, Combinatorics.Line.map,
        Combinatorics.Line.coe_apply, hi]
  | some b =>
      simp [templateExtension, restrictWord, Combinatorics.Line.map,
        Combinatorics.Line.coe_apply, hi]

@[simp] theorem templateExtension_last {k m : ℕ}
    (l : Combinatorics.Line (Fin k) (Fin m)) :
    templateExtension l (Fin.last k) = templateEndpoint l := by
  funext i
  cases hi : l.idxFun i with
  | none =>
      simp [templateExtension, templateEndpoint, Combinatorics.Line.map,
        Combinatorics.Line.coe_apply, hi]
  | some a =>
      simp [templateExtension, templateEndpoint, Combinatorics.Line.map,
        Combinatorics.Line.coe_apply, hi]

@[simp] theorem templateEndpoint_of_none {k m : ℕ}
    (l : Combinatorics.Line (Fin k) (Fin m)) {i : Fin m}
    (hi : l.idxFun i = none) :
    templateEndpoint l i = Fin.last k := by
  simp [templateEndpoint, hi]

@[simp] theorem templateEndpoint_of_some {k m : ℕ}
    (l : Combinatorics.Line (Fin k) (Fin m)) {i : Fin m} {a : Fin k}
    (hi : l.idxFun i = some a) :
    templateEndpoint l i = Fin.castSucc a := by
  simp [templateEndpoint, hi]

theorem templateEndpoint_not_restricted {k m : ℕ}
    (l : Combinatorics.Line (Fin k) (Fin m)) :
    ¬ IsRestrictedWord (templateEndpoint l) := by
  intro h
  obtain ⟨i, hi⟩ := l.proper
  exact h i (templateEndpoint_of_none l hi)

/-- Proper internal line templates are in bijection with the words which use
the new last letter in at least one coordinate. -/
noncomputable def templateEndpointEquiv (k m : ℕ) :
    Combinatorics.Line (Fin k) (Fin m) ≃
      {w : Word (k + 1) m // ¬ IsRestrictedWord w} where
  toFun l := ⟨templateEndpoint l, templateEndpoint_not_restricted l⟩
  invFun w :=
    { idxFun := fun i ↦ finSuccEquivLast (w.1 i)
      proper := by
        classical
        have hw : ∃ i, w.1 i = Fin.last k := by
          simpa only [IsRestrictedWord, not_forall, not_ne_iff] using w.2
        obtain ⟨i, hi⟩ := hw
        exact ⟨i, by simp [hi]⟩ }
  left_inv l := by
    apply Combinatorics.Line.ext
    funext i
    simp [templateEndpoint]
  right_inv w := by
    apply Subtype.ext
    funext i
    simp [templateEndpoint]

theorem templateEndpoint_injective {k m : ℕ} :
    Function.Injective (templateEndpoint (k := k) (m := m)) := by
  intro l₁ l₂ h
  apply (templateEndpointEquiv k m).injective
  apply Subtype.ext
  exact h

@[simp] theorem ncard_range_templateEndpoint (k m : ℕ) :
    Set.ncard (Set.range (templateEndpoint (k := k) (m := m))) =
      (k + 1) ^ m - k ^ m := by
  rw [Set.ncard_range_of_injective templateEndpoint_injective]
  simp only [Nat.card_eq_fintype_card, Combinatorics.Line.card_fin]

end Erdos171

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/Insensitive.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Insensitive subsets of a finite word cube

This file formalizes the elementary ``insensitive-set'' constructions used in
the density-increment proof of density Hales--Jewett.  The distinguished symbol
in `Fin (k + 1)` is `Fin.last k`.  Replacing every occurrence of that symbol by
`i.castSucc` gives a canonical representative for the equivalence relation
which permits independent changes between these two symbols.
-/

namespace Erdos171

open Set

section Replacement

variable {k n : ℕ}

/-- Replace the distinguished last letter of `Fin (k + 1)` by `i`. -/
def replaceLastLetter (i : Fin k) (a : Fin (k + 1)) : Fin (k + 1) :=
  if a = Fin.last k then i.castSucc else a

@[simp] theorem replaceLastLetter_last (i : Fin k) :
    replaceLastLetter i (Fin.last k) = i.castSucc := by
  simp [replaceLastLetter]

@[simp] theorem replaceLastLetter_castSucc (i a : Fin k) :
    replaceLastLetter i a.castSucc = a.castSucc := by
  simp [replaceLastLetter, Fin.castSucc_ne_last]

theorem replaceLastLetter_ne_last (i : Fin k) (a : Fin (k + 1)) :
    replaceLastLetter i a ≠ Fin.last k := by
  by_cases h : a = Fin.last k
  · simp [h]
  · simpa [replaceLastLetter, h] using h

@[simp] theorem replaceLastLetter_idem (i : Fin k) (a : Fin (k + 1)) :
    replaceLastLetter i (replaceLastLetter i a) = replaceLastLetter i a := by
  change (if replaceLastLetter i a = Fin.last k then i.castSucc else replaceLastLetter i a) = _
  rw [if_neg (replaceLastLetter_ne_last i a)]

/-- Replace every occurrence of the distinguished last letter in a word by `i`. -/
def replaceLast (i : Fin k) (x : Word (k + 1) n) : Word (k + 1) n :=
  fun r ↦ replaceLastLetter i (x r)

@[simp] theorem replaceLast_apply (i : Fin k) (x : Word (k + 1) n) (r : Fin n) :
    replaceLast i x r = replaceLastLetter i (x r) := rfl

@[simp] theorem replaceLast_idem (i : Fin k) (x : Word (k + 1) n) :
    replaceLast i (replaceLast i x) = replaceLast i x := by
  funext r
  exact replaceLastLetter_idem i (x r)

theorem replaceLast_ne_last (i : Fin k) (x : Word (k + 1) n) (r : Fin n) :
    replaceLast i x r ≠ Fin.last k :=
  replaceLastLetter_ne_last i (x r)

/-- The word in the smaller alphabet obtained by treating every last letter as `i`. -/
def endpoint (i : Fin k) (x : Word (k + 1) n) : Word k n :=
  fun r ↦ (replaceLast i x r).castPred (replaceLast_ne_last i x r)

@[simp] theorem endpoint_last (i : Fin k) (r : Fin n) :
    endpoint i (fun _ : Fin n ↦ Fin.last k) r = i := by
  apply Fin.castSucc_injective
  simp [endpoint]

@[simp] theorem endpoint_castSucc (i : Fin k) (x : Word k n) :
    endpoint i (fun r ↦ (x r).castSucc) = x := by
  funext r
  apply Fin.castSucc_injective
  simp [endpoint]

@[simp] theorem castSucc_endpoint (i : Fin k) (x : Word (k + 1) n) (r : Fin n) :
    (endpoint i x r).castSucc = replaceLast i x r := by
  simp [endpoint]

theorem endpoint_eq_iff_replaceLast_eq (i : Fin k) (x y : Word (k + 1) n) :
    endpoint i x = endpoint i y ↔ replaceLast i x = replaceLast i y := by
  constructor
  · intro h
    funext r
    rw [← castSucc_endpoint i x r, ← castSucc_endpoint i y r, h]
  · intro h
    funext r
    apply Fin.castSucc_injective
    simpa only [castSucc_endpoint] using congrFun h r

/-- Two words are `(i,last)`-equivalent if changing `i` and the last letter independently
at any coordinates cannot distinguish them. -/
def LastEquivalent (i : Fin k) (x y : Word (k + 1) n) : Prop :=
  replaceLast i x = replaceLast i y

@[refl] theorem LastEquivalent.refl (i : Fin k) (x : Word (k + 1) n) :
    LastEquivalent i x x := rfl

@[symm] theorem LastEquivalent.symm (i : Fin k) {x y : Word (k + 1) n}
    (h : LastEquivalent i x y) : LastEquivalent i y x := Eq.symm h

@[trans] theorem LastEquivalent.trans (i : Fin k) {x y z : Word (k + 1) n}
    (hxy : LastEquivalent i x y) (hyz : LastEquivalent i y z) :
    LastEquivalent i x z := Eq.trans hxy hyz

theorem lastEquivalent_iff_endpoint_eq (i : Fin k) (x y : Word (k + 1) n) :
    LastEquivalent i x y ↔ endpoint i x = endpoint i y := by
  rw [endpoint_eq_iff_replaceLast_eq]
  rfl

end Replacement

section Insensitive

variable {k n : ℕ}

/-- A set is `(i,last)`-insensitive when it is constant on `LastEquivalent` classes. -/
def IsLastInsensitive (i : Fin k) (C : Set (Word (k + 1) n)) : Prop :=
  ∀ x y, LastEquivalent i x y → (x ∈ C ↔ y ∈ C)

theorem IsLastInsensitive.compl {i : Fin k} {C : Set (Word (k + 1) n)}
    (hC : IsLastInsensitive i C) : IsLastInsensitive i Cᶜ := by
  intro x y hxy
  simpa only [Set.mem_compl_iff] using not_congr (hC x y hxy)

theorem IsLastInsensitive.union {i : Fin k} {C D : Set (Word (k + 1) n)}
    (hC : IsLastInsensitive i C) (hD : IsLastInsensitive i D) :
    IsLastInsensitive i (C ∪ D) := by
  intro x y hxy
  simpa only [Set.mem_union] using or_congr (hC x y hxy) (hD x y hxy)

end Insensitive

section EndpointConstruction

variable {k n : ℕ}

/-- The `(i,last)`-insensitive cylinder generated by a set in the restricted cube `[k]^n`. -/
def endpointCylinder (i : Fin k) (A : Set (Word k n)) : Set (Word (k + 1) n) :=
  endpoint i ⁻¹' A

@[simp] theorem mem_endpointCylinder (i : Fin k) (A : Set (Word k n))
    (x : Word (k + 1) n) : x ∈ endpointCylinder i A ↔ endpoint i x ∈ A :=
  Iff.rfl

theorem endpointCylinder_isLastInsensitive (i : Fin k) (A : Set (Word k n)) :
    IsLastInsensitive i (endpointCylinder i A) := by
  intro x y hxy
  simpa only [mem_endpointCylinder, (lastEquivalent_iff_endpoint_eq i x y).mp hxy]

@[simp] theorem mem_iInter_endpointCylinder (A : Set (Word k n))
    (x : Word (k + 1) n) :
    x ∈ ⋂ i : Fin k, endpointCylinder i A ↔ ∀ i : Fin k, endpoint i x ∈ A := by
  simp

/-- Taking the `i`-endpoint of the wildcard word attached to a line recovers
the `i`-point of that line. -/
@[simp] theorem endpoint_templateEndpoint (i : Fin k)
    (l : Combinatorics.Line (Fin k) (Fin n)) :
    endpoint i (templateEndpoint l) = l i := by
  funext r
  cases hr : l.idxFun r with
  | none =>
      simp [endpoint, replaceLast, replaceLastLetter, Combinatorics.Line.coe_apply, hr]
  | some a =>
      simp [endpoint, replaceLast, replaceLastLetter, Combinatorics.Line.coe_apply, hr]

@[simp] theorem endpoint_templateExtension_last (i : Fin k)
    (l : Combinatorics.Line (Fin k) (Fin n)) :
    endpoint i (templateExtension l (Fin.last k)) = l i := by
  simp

@[simp] theorem endpoint_templateExtension_castSucc (i a : Fin k)
    (l : Combinatorics.Line (Fin k) (Fin n)) :
    endpoint i (templateExtension l a.castSucc) = l a := by
  rw [templateExtension_castSucc]
  change endpoint i (fun r ↦ (l a r).castSucc) = l a
  exact endpoint_castSucc i (l a)

/-- The wildcard endpoint of a line belongs to all of the insensitive cylinders
generated by `A` exactly when every point of the original line belongs to `A`. -/
@[simp] theorem templateEndpoint_mem_iInter_endpointCylinder_iff
    (A : Set (Word k n)) (l : Combinatorics.Line (Fin k) (Fin n)) :
    templateEndpoint l ∈ ⋂ i : Fin k, endpointCylinder i A ↔
      Set.range l ⊆ A := by
  rw [mem_iInter_endpointCylinder]
  simp only [endpoint_templateEndpoint]
  constructor
  · intro h _ hx
    obtain ⟨i, rfl⟩ := hx
    exact h i
  · intro h i
    exact h ⟨i, rfl⟩

/-- A word containing the last letter encodes a proper line in the restricted cube: last-letter
coordinates are wildcard coordinates, and every other coordinate is held constant. -/
def endpointLine (x : Word (k + 1) n)
    (hx : ∃ r, x r = Fin.last k) : Combinatorics.Line (Fin k) (Fin n) where
  idxFun r := if h : x r = Fin.last k then none else some ((x r).castPred h)
  proper := by
    obtain ⟨r, hr⟩ := hx
    exact ⟨r, by simp [hr]⟩

@[simp] theorem endpointLine_apply (x : Word (k + 1) n)
    (hx : ∃ r, x r = Fin.last k) (i : Fin k) :
    endpointLine x hx i = endpoint i x := by
  funext r
  by_cases h : x r = Fin.last k
  · simp [endpointLine, Combinatorics.Line.coe_apply, endpoint, replaceLast,
      replaceLastLetter, h]
  · simp [endpointLine, Combinatorics.Line.coe_apply, endpoint, replaceLast,
      replaceLastLetter, h]

end EndpointConstruction

end Erdos171

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/SubspaceOps.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Operations on combinatorial subspaces for Erdős 171

This file supplies the algebra of subspaces used by the density argument.  In
particular, it contains composition, independent products and coordinate
concatenation.  The final section records carefully the two distinct operations
involving the inclusion `Fin k → Fin (k + 1)`:

* restrict the *parameters* of a large-alphabet subspace to the old alphabet;
* lift a small-alphabet subspace by mapping all of its fixed letters into the
  large alphabet.

A large-alphabet subspace can be turned back into a small-alphabet subspace
exactly when none of its fixed letters is the new last letter.
-/

section
open Combinatorics

section
open Combinatorics.Subspace

variable {η ζ ξ α ι κ υ : Type*}

/-- Composition of combinatorial subspaces.  The convention is functional:
`U.comp V` first evaluates `V` and then evaluates `U`. -/
private def _root_.Combinatorics.Subspace.comp (U : Subspace η α ι) (V : Subspace ζ α η) : Subspace ζ α ι where
  idxFun i := (U.idxFun i).elim Sum.inl V.idxFun
  proper z := by
    obtain ⟨e, he⟩ := V.proper z
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨i, by simp [hi, he]⟩

@[simp] private theorem _root_.Combinatorics.Subspace.comp_idxFun (U : Subspace η α ι) (V : Subspace ζ α η) (i : ι) :
    (U.comp V).idxFun i = (U.idxFun i).elim Sum.inl V.idxFun := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.comp_apply (U : Subspace η α ι) (V : Subspace ζ α η)
    (x : ζ → α) : U.comp V x = U (V x) := by
  funext i
  cases hi : U.idxFun i <;> simp [comp, coe_apply, hi]

@[simp] private theorem _root_.Combinatorics.Subspace.lineMap_comp (U : Subspace η α ι) (V : Subspace ζ α η)
    (l : Line α ζ) :
    (U.comp V).lineMap l = U.lineMap (V.lineMap l) := by
  ext i
  cases hU : U.idxFun i with
  | inl a => simp [comp, lineMap, hU]
  | inr e =>
      cases hV : V.idxFun e <;> simp [comp, lineMap, hU, hV]

/-- Independent product of two subspaces.  Its parameter directions and its
ambient coordinates are both disjoint sums. -/
private def _root_.Combinatorics.Subspace.sum (U : Subspace η α ι) (V : Subspace ζ α κ) :
    Subspace (η ⊕ ζ) α (ι ⊕ κ) where
  idxFun
    | Sum.inl i => (U.idxFun i).map id Sum.inl
    | Sum.inr j => (V.idxFun j).map id Sum.inr
  proper
    | Sum.inl e => by
        obtain ⟨i, hi⟩ := U.proper e
        exact ⟨Sum.inl i, by simp [hi]⟩
    | Sum.inr f => by
        obtain ⟨j, hj⟩ := V.proper f
        exact ⟨Sum.inr j, by simp [hj]⟩

@[simp] private theorem _root_.Combinatorics.Subspace.sum_idxFun_inl (U : Subspace η α ι) (V : Subspace ζ α κ)
    (i : ι) :
    (U.sum V).idxFun (Sum.inl i) = (U.idxFun i).map id Sum.inl := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.sum_idxFun_inr (U : Subspace η α ι) (V : Subspace ζ α κ)
    (j : κ) :
    (U.sum V).idxFun (Sum.inr j) = (V.idxFun j).map id Sum.inr := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.sum_apply_inl (U : Subspace η α ι) (V : Subspace ζ α κ)
    (x : η ⊕ ζ → α) (i : ι) :
    U.sum V x (Sum.inl i) = U (x ∘ Sum.inl) i := by
  cases hi : U.idxFun i <;> simp [sum, coe_apply, hi]

@[simp] private theorem _root_.Combinatorics.Subspace.sum_apply_inr (U : Subspace η α ι) (V : Subspace ζ α κ)
    (x : η ⊕ ζ → α) (j : κ) :
    U.sum V x (Sum.inr j) = V (x ∘ Sum.inr) j := by
  cases hj : V.idxFun j <;> simp [sum, coe_apply, hj]

/-- Join two words on disjoint coordinate sets. -/
private def _root_.Combinatorics.Subspace.sumWord (x : η → α) (y : ζ → α) : η ⊕ ζ → α :=
  Sum.elim x y

@[simp] private theorem _root_.Combinatorics.Subspace.sumWord_inl (x : η → α) (y : ζ → α) (e : η) :
    sumWord x y (Sum.inl e) = x e := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.sumWord_inr (x : η → α) (y : ζ → α) (f : ζ) :
    sumWord x y (Sum.inr f) = y f := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.sum_apply_sumWord (U : Subspace η α ι) (V : Subspace ζ α κ)
    (x : η → α) (y : ζ → α) :
    U.sum V (sumWord x y) = sumWord (U x) (V y) := by
  have hx : sumWord x y ∘ Sum.inl = x := by funext e; rfl
  have hy : sumWord x y ∘ Sum.inr = y := by funext f; rfl
  funext q
  cases q with
  | inl i => simpa [hx] using sum_apply_inl U V (sumWord x y) i
  | inr j => simpa [hy] using sum_apply_inr U V (sumWord x y) j

/-- Concatenate two ambient coordinate blocks while sharing the same parameter
directions. -/
private def _root_.Combinatorics.Subspace.concat (U : Subspace η α ι) (V : Subspace η α κ) :
    Subspace η α (ι ⊕ κ) where
  idxFun
    | Sum.inl i => U.idxFun i
    | Sum.inr j => V.idxFun j
  proper e := by
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨Sum.inl i, hi⟩

@[simp] private theorem _root_.Combinatorics.Subspace.concat_idxFun_inl (U : Subspace η α ι) (V : Subspace η α κ)
    (i : ι) : (U.concat V).idxFun (Sum.inl i) = U.idxFun i := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.concat_idxFun_inr (U : Subspace η α ι) (V : Subspace η α κ)
    (j : κ) : (U.concat V).idxFun (Sum.inr j) = V.idxFun j := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.concat_apply (U : Subspace η α ι) (V : Subspace η α κ)
    (x : η → α) :
    U.concat V x = sumWord (U x) (V x) := by
  funext q
  cases q with
  | inl i => simp [concat, coe_apply, sumWord]
  | inr j => simp [concat, coe_apply, sumWord]

/-- Extend a subspace by a block of fixed suffix coordinates. -/
private def _root_.Combinatorics.Subspace.extendRightWord (U : Subspace η α ι) (y : κ → α) :
    Subspace η α (ι ⊕ κ) where
  idxFun
    | Sum.inl i => U.idxFun i
    | Sum.inr j => Sum.inl (y j)
  proper e := by
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨Sum.inl i, hi⟩

@[simp] private theorem _root_.Combinatorics.Subspace.extendRightWord_idxFun_inl (U : Subspace η α ι) (y : κ → α)
    (i : ι) : (U.extendRightWord y).idxFun (Sum.inl i) = U.idxFun i := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.extendRightWord_idxFun_inr (U : Subspace η α ι) (y : κ → α)
    (j : κ) : (U.extendRightWord y).idxFun (Sum.inr j) = Sum.inl (y j) := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.extendRightWord_apply (U : Subspace η α ι) (y : κ → α)
    (x : η → α) :
    U.extendRightWord y x = sumWord (U x) y := by
  funext q
  cases q with
  | inl i => simp [extendRightWord, coe_apply, sumWord]
  | inr j => simp [extendRightWord, coe_apply, sumWord]

/-- The canonical coordinate face on the first `m₀` coordinates.  All later
coordinates are fixed at `default`. -/
private def _root_.Combinatorics.Subspace.coordinateFace {m₀ m : ℕ} [Inhabited α] (h : m₀ ≤ m) :
    Subspace (Fin m₀) α (Fin m) where
  idxFun i := if hi : i.val < m₀ then Sum.inr ⟨i.val, hi⟩ else Sum.inl default
  proper e := by
    refine ⟨Fin.castLE h e, ?_⟩
    simp [e.isLt]

@[simp] private theorem _root_.Combinatorics.Subspace.coordinateFace_idxFun_castLE {m₀ m : ℕ} [Inhabited α]
    (h : m₀ ≤ m) (e : Fin m₀) :
    (coordinateFace (α := α) h).idxFun (Fin.castLE h e) = Sum.inr e := by
  simp [coordinateFace, e.isLt]

@[simp] private theorem _root_.Combinatorics.Subspace.coordinateFace_apply_castLE {m₀ m : ℕ} [Inhabited α]
    (h : m₀ ≤ m) (x : Fin m₀ → α) (e : Fin m₀) :
    coordinateFace (α := α) h x (Fin.castLE h e) = x e := by
  rw [apply_inr (coordinateFace_idxFun_castLE h e)]

@[simp] private theorem _root_.Combinatorics.Subspace.coordinateFace_comp {m₀ m₁ m₂ : ℕ} [Inhabited α]
    (h₀₁ : m₀ ≤ m₁) (h₁₂ : m₁ ≤ m₂) :
    (coordinateFace (α := α) h₁₂).comp (coordinateFace (α := α) h₀₁) =
      coordinateFace (α := α) (h₀₁.trans h₁₂) := by
  ext i
  by_cases h₀ : i.val < m₀
  · have h₁ : i.val < m₁ := lt_of_lt_of_le h₀ h₀₁
    simp [comp, coordinateFace, h₀, h₁]
  · by_cases h₁ : i.val < m₁ <;> simp [comp, coordinateFace, h₀, h₁]

/-- Map all fixed letters of a subspace through a function.  Variable
coordinates are unchanged. -/
private def _root_.Combinatorics.Subspace.mapAlphabet (U : Subspace η α ι) (f : α → υ) : Subspace η υ ι where
  idxFun i := (U.idxFun i).map f id
  proper e := by
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨i, by simp [hi]⟩

@[simp] private theorem _root_.Combinatorics.Subspace.mapAlphabet_idxFun (U : Subspace η α ι) (f : α → υ) (i : ι) :
    (U.mapAlphabet f).idxFun i = (U.idxFun i).map f id := rfl

@[simp] private theorem _root_.Combinatorics.Subspace.mapAlphabet_apply (U : Subspace η α ι) (f : α → υ)
    (x : η → α) :
    U.mapAlphabet f (f ∘ x) = f ∘ U x := by
  funext i
  cases hi : U.idxFun i <;> simp [mapAlphabet, coe_apply, hi]

@[simp] private theorem _root_.Combinatorics.Subspace.mapAlphabet_id (U : Subspace η α ι) :
    U.mapAlphabet id = U := by
  ext i
  cases hi : U.idxFun i <;> simp [mapAlphabet, hi]

end

end

namespace Erdos171

open Set

variable {η ζ α ι κ : Type*}

/-- The product set of two families of words on disjoint coordinate types. -/
def sumSet (A : Set (η → α)) (B : Set (ζ → α)) : Set (η ⊕ ζ → α) :=
  {x | (x ∘ Sum.inl) ∈ A ∧ (x ∘ Sum.inr) ∈ B}

@[simp] theorem mem_sumSet {A : Set (η → α)} {B : Set (ζ → α)}
    {x : η ⊕ ζ → α} :
    x ∈ sumSet A B ↔ (x ∘ Sum.inl) ∈ A ∧ (x ∘ Sum.inr) ∈ B :=
  Iff.rfl

@[simp] theorem sumWord_mem_sumSet {A : Set (η → α)} {B : Set (ζ → α)}
    {x : η → α} {y : ζ → α} :
    Combinatorics.Subspace.sumWord x y ∈ sumSet A B ↔ x ∈ A ∧ y ∈ B := by
  rfl

section FinAlphabet

variable {k : ℕ}

/-- Include an old-alphabet word into the alphabet with one new last letter. -/
def liftWord (x : η → Fin k) : η → Fin (k + 1) :=
  fun e ↦ (x e).castSucc

@[simp] theorem liftWord_apply (x : η → Fin k) (e : η) :
    liftWord x e = (x e).castSucc := rfl

theorem liftWord_injective : Function.Injective (liftWord : (η → Fin k) → η → Fin (k + 1)) := by
  intro x y h
  funext e
  exact Fin.castSucc_injective k (congrFun h e)

/-- Image of a set of words under inclusion of the old alphabet. -/
def liftSet (A : Set (η → Fin k)) : Set (η → Fin (k + 1)) :=
  liftWord '' A

/-- Pull a set over the enlarged alphabet back to words using only old letters. -/
def restrictSet (B : Set (η → Fin (k + 1))) : Set (η → Fin k) :=
  liftWord ⁻¹' B

@[simp] theorem mem_restrictSet {B : Set (η → Fin (k + 1))} {x : η → Fin k} :
    x ∈ restrictSet B ↔ liftWord x ∈ B :=
  Iff.rfl

@[simp] theorem liftWord_mem_liftSet {A : Set (η → Fin k)} {x : η → Fin k} :
    liftWord x ∈ liftSet A ↔ x ∈ A := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (liftWord_injective hxy).symm ▸ hy
  · exact fun hx ↦ ⟨x, hx, rfl⟩

@[simp] theorem restrictSet_liftSet (A : Set (η → Fin k)) :
    restrictSet (liftSet A) = A := by
  ext x
  simp

/-- Finset version of `liftSet`. -/
def liftFinset [DecidableEq (η → Fin (k + 1))] (A : Finset (η → Fin k)) :
    Finset (η → Fin (k + 1)) :=
  A.map ⟨liftWord, liftWord_injective⟩

@[simp] theorem mem_liftFinset [DecidableEq (η → Fin (k + 1))]
    {A : Finset (η → Fin k)} {x : η → Fin k} :
    liftWord x ∈ liftFinset A ↔ x ∈ A := by
  simp [liftFinset, liftWord_injective.eq_iff]

@[simp] theorem card_liftFinset [DecidableEq (η → Fin (k + 1))]
    (A : Finset (η → Fin k)) :
    (liftFinset A).card = A.card := by
  simp [liftFinset]

end FinAlphabet

end Erdos171

section
open Combinatorics

section
open Combinatorics.Subspace

open Erdos171

variable {η ι : Type*} {k : ℕ}

/-- Lift a small-alphabet subspace into the alphabet with one new last letter. -/
private def _root_.Combinatorics.Subspace.finLift (U : Subspace η (Fin k) ι) : Subspace η (Fin (k + 1)) ι :=
  U.mapAlphabet Fin.castSucc

@[simp] private theorem _root_.Combinatorics.Subspace.finLift_apply (U : Subspace η (Fin k) ι) (x : η → Fin k) :
    U.finLift (liftWord x) = liftWord (U x) := by
  exact U.mapAlphabet_apply Fin.castSucc x

/-- A large-alphabet subspace has only old fixed letters. -/
private def _root_.Combinatorics.Subspace.FixedLettersOld (U : Subspace η (Fin (k + 1)) ι) : Prop :=
  ∀ i a, U.idxFun i = Sum.inl a → a ≠ Fin.last k

private theorem _root_.Combinatorics.Subspace.FixedLettersOld.ne_last {U : Subspace η (Fin (k + 1)) ι}
    (hU : U.FixedLettersOld) {i : ι} {a : Fin (k + 1)}
    (hi : U.idxFun i = Sum.inl a) : a ≠ Fin.last k :=
  hU i a hi

/-- A total retraction from `Fin (k + 1)` to the old alphabet.  Its value on the
new last letter is irrelevant; on every old letter it is inverse to
`Fin.castSucc`. -/
private def _root_.Combinatorics.Subspace.dropLast [Inhabited (Fin k)] (a : Fin (k + 1)) : Fin k :=
  if h : a = Fin.last k then default else a.castPred h

@[simp] private theorem _root_.Combinatorics.Subspace.dropLast_castSucc [Inhabited (Fin k)] (a : Fin k) :
    dropLast a.castSucc = a := by
  simp [dropLast, Fin.castSucc_ne_last, Fin.castPred_castSucc]

private theorem _root_.Combinatorics.Subspace.castSucc_dropLast [Inhabited (Fin k)] {a : Fin (k + 1)}
    (ha : a ≠ Fin.last k) :
    (dropLast a).castSucc = a := by
  simp [dropLast, ha, Fin.castSucc_castPred]

/-- Restrict the fixed letters of a large-alphabet subspace through `dropLast`.
When all fixed letters are old, `finLift` recovers the original subspace. -/
private def _root_.Combinatorics.Subspace.finRestrict [Inhabited (Fin k)] (U : Subspace η (Fin (k + 1)) ι) :
    Subspace η (Fin k) ι :=
  U.mapAlphabet dropLast

@[simp] private theorem _root_.Combinatorics.Subspace.finRestrict_apply
    [Inhabited (Fin k)]
    (U : Subspace η (Fin (k + 1)) ι)
    (hU : U.FixedLettersOld) (x : η → Fin k) :
    liftWord (U.finRestrict x) = U (liftWord x) := by
  funext i
  cases hi : U.idxFun i with
  | inl a =>
      simp [finRestrict, mapAlphabet, coe_apply, hi,
        castSucc_dropLast (hU.ne_last hi)]
  | inr e =>
      simp [finRestrict, mapAlphabet, coe_apply, hi]

@[simp] private theorem _root_.Combinatorics.Subspace.finRestrict_finLift [Inhabited (Fin k)]
    (U : Subspace η (Fin k) ι) :
    U.finLift.finRestrict = U := by
  ext i
  cases hi : U.idxFun i with
  | inl a =>
      simp [finRestrict, finLift, mapAlphabet, hi]
  | inr e =>
      simp [finRestrict, finLift, mapAlphabet, hi]

@[simp] private theorem _root_.Combinatorics.Subspace.finLift_finRestrict
    [Inhabited (Fin k)]
    (U : Subspace η (Fin (k + 1)) ι)
    (hU : U.FixedLettersOld) :
    U.finRestrict.finLift = U := by
  ext i
  cases hi : U.idxFun i with
  | inl a =>
      simp [finRestrict, finLift, mapAlphabet, hi,
        castSucc_dropLast (hU.ne_last hi)]
  | inr e =>
      simp [finRestrict, finLift, mapAlphabet, hi]

end

end

namespace Erdos171

open Set

variable {η ι : Type*} {k : ℕ}

section FinAlphabet

/-- Pull back an ambient set along a subspace while restricting its parameters
to old-alphabet words. -/
def restrictedPreimage (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Set (ι → Fin (k + 1))) : Set (η → Fin k) :=
  {x | U (liftWord x) ∈ A}

@[simp] theorem mem_restrictedPreimage
    {U : Combinatorics.Subspace η (Fin (k + 1)) ι}
    {A : Set (ι → Fin (k + 1))} {x : η → Fin k} :
    x ∈ restrictedPreimage U A ↔ U (liftWord x) ∈ A :=
  Iff.rfl

end FinAlphabet

end Erdos171

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos185/DHJ/Cube.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Finite cubes and pullbacks for Erdős problem 185

This file contains the elementary algebra needed to work inside a
combinatorial subspace without importing the larger Erdős 171 development.
The central operation is `pullbackFinset`: it records, as a finset in the
parameter cube, the points of a finset lying in a given subspace.
-/

section
open Combinatorics

section
open Combinatorics.Subspace

variable {α : Type*}

/-- Product of finite-dimensional subspaces, with both disjoint sums reindexed
by the standard equivalence `Fin r ⊕ Fin s ≃ Fin (r+s)`. -/
private def _root_.Combinatorics.Subspace.finSum {p q m n : ℕ} (U : Subspace (Fin m) α (Fin p))
    (V : Subspace (Fin n) α (Fin q)) :
    Subspace (Fin (m + n)) α (Fin (p + q)) :=
  (U.sum V).reindex finSumFinEquiv (Equiv.refl α) finSumFinEquiv

@[simp] private theorem _root_.Combinatorics.Subspace.finSum_apply_castAdd {p q m n : ℕ}
    (U : Subspace (Fin m) α (Fin p)) (V : Subspace (Fin n) α (Fin q))
    (x : Fin (m + n) → α) (i : Fin p) :
    U.finSum V x (Fin.castAdd q i) = U (x ∘ Fin.castAdd n) i := by
  simp [finSum, Function.comp_def]

@[simp] private theorem _root_.Combinatorics.Subspace.finSum_apply_natAdd {p q m n : ℕ}
    (U : Subspace (Fin m) α (Fin p)) (V : Subspace (Fin n) α (Fin q))
    (x : Fin (m + n) → α) (j : Fin q) :
    U.finSum V x (Fin.natAdd p j) = V (x ∘ Fin.natAdd m) j := by
  simp [finSum, Function.comp_def]

end

end

namespace DHJ

open Set

/-- Words use the same concrete representation as the Erdős 171 library. -/
abbrev Word := Erdos171.Word

section Lines

variable {α ι η : Type*}

/-- A finite family of words contains a proper combinatorial line. -/
def HasLine [DecidableEq (ι → α)] (A : Finset (ι → α)) : Prop :=
  ∃ l : Combinatorics.Line α ι, ∀ a : α, l a ∈ A

/-- A line in a parameter cube, lifted through a subspace. -/
abbrev liftLine (U : Combinatorics.Subspace η α ι)
    (l : Combinatorics.Line α η) : Combinatorics.Line α ι :=
  U.lineMap l

@[simp] theorem liftLine_apply (U : Combinatorics.Subspace η α ι)
    (l : Combinatorics.Line α η) (a : α) :
    liftLine U l a = U (l a) :=
  Combinatorics.Subspace.lineMap_apply U l a

end Lines

section Pullback

variable {α ι η ζ : Type*}

/-- The points of `A` seen in the parameter cube of `U`. -/
noncomputable def pullbackFinset [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    Finset (η → α) := by
  classical
  exact Finset.univ.filter fun x ↦ U x ∈ A

@[simp] theorem mem_pullbackFinset [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) (x : η → α) :
    x ∈ pullbackFinset U A ↔ U x ∈ A := by
  classical
  simp [pullbackFinset]

@[simp] theorem coe_pullbackFinset [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    (pullbackFinset U A : Set (η → α)) = U ⁻¹' (A : Set (ι → α)) := by
  ext x
  simp

@[simp] theorem pullbackFinset_univ [Fintype η] [Fintype α]
    [Fintype ι] [DecidableEq η] [DecidableEq ι]
    (U : Combinatorics.Subspace η α ι) :
    pullbackFinset U (Finset.univ : Finset (ι → α)) = Finset.univ := by
  classical
  ext x
  simp

@[simp] theorem pullbackFinset_empty [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) :
    pullbackFinset U (∅ : Finset (ι → α)) = ∅ := by
  classical
  ext x
  simp

@[simp] theorem pullbackFinset_inter [Fintype η] [Fintype α]
    [DecidableEq (η → α)] [DecidableEq (ι → α)]
    (U : Combinatorics.Subspace η α ι) (A B : Finset (ι → α)) :
    pullbackFinset U (A ∩ B) = pullbackFinset U A ∩ pullbackFinset U B := by
  classical
  ext x
  simp

@[simp] theorem pullbackFinset_union [Fintype η] [Fintype α]
    [DecidableEq (η → α)] [DecidableEq (ι → α)]
    (U : Combinatorics.Subspace η α ι) (A B : Finset (ι → α)) :
    pullbackFinset U (A ∪ B) = pullbackFinset U A ∪ pullbackFinset U B := by
  classical
  ext x
  simp

@[simp] theorem pullbackFinset_sdiff [Fintype η] [Fintype α]
    [DecidableEq (η → α)] [DecidableEq (ι → α)]
    (U : Combinatorics.Subspace η α ι) (A B : Finset (ι → α)) :
    pullbackFinset U (A \ B) = pullbackFinset U A \ pullbackFinset U B := by
  classical
  ext x
  simp

@[simp] theorem pullback_comp [Fintype ζ] [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι)
    (V : Combinatorics.Subspace ζ α η) (A : Finset (ι → α)) :
    pullbackFinset (U.comp V) A = pullbackFinset V (pullbackFinset U A) := by
  classical
  ext x
  simp

/-- Density of `A` inside `U`, measured in the uniform parameter cube. -/
noncomputable def densityIn [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : ℝ :=
  ((pullbackFinset U A).card : ℝ) / Nat.card (η → α)

@[simp] theorem densityIn_eq_card_div [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    densityIn U A = ((pullbackFinset U A).card : ℝ) / Nat.card (η → α) :=
  rfl

theorem densityIn_le_one [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    densityIn U A ≤ 1 := by
  classical
  rw [densityIn, Nat.card_eq_fintype_card]
  cases isEmpty_or_nonempty (η → α) with
  | inl h =>
      letI := h
      have hp : pullbackFinset U A = ∅ := by
        ext x
        exact isEmptyElim x
      simp [hp]
  | inr h =>
      letI := h
      have hc : (0 : ℝ) < Fintype.card (η → α) := by
        exact_mod_cast Fintype.card_pos
      rw [div_le_one hc]
      exact_mod_cast Finset.card_le_univ (pullbackFinset U A)

@[simp] theorem densityIn_comp [Fintype ζ] [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι)
    (V : Combinatorics.Subspace ζ α η) (A : Finset (ι → α)) :
    densityIn (U.comp V) A = densityIn V (pullbackFinset U A) := by
  simp [densityIn]

theorem HasLine.of_pullback [Fintype η] [Fintype α]
    [DecidableEq (η → α)] [DecidableEq (ι → α)]
    (U : Combinatorics.Subspace η α ι)
    {A : Finset (ι → α)} (h : HasLine (pullbackFinset U A)) : HasLine A := by
  obtain ⟨l, hl⟩ := h
  refine ⟨U.lineMap l, ?_⟩
  intro a
  rw [Combinatorics.Subspace.lineMap_apply]
  exact (mem_pullbackFinset U A (l a)).1 (hl a)

end Pullback

section RestrictedPart

/-- The part of an enlarged-alphabet finset using only the old letters. -/
noncomputable def restrictedPart {k m : ℕ}
    (A : Finset (Word (k + 1) m)) : Finset (Word k m) := by
  classical
  exact Finset.univ.filter fun x ↦ Erdos171.restrictWord x ∈ A

@[simp] theorem mem_restrictedPart {k m : ℕ}
    (A : Finset (Word (k + 1) m)) (x : Word k m) :
    x ∈ restrictedPart A ↔ Erdos171.restrictWord x ∈ A := by
  classical
  simp [restrictedPart]

/-- The binary part of a ternary finset. -/
noncomputable def binaryPart {m : ℕ} (A : Finset (Word 3 m)) : Finset (Word 2 m) :=
  restrictedPart A

/-- Every old-alphabet parameter word of `U` is carried into `A`. -/
def RestrictedPartContained {k m n : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (A : Finset (Word (k + 1) n)) : Prop :=
  ∀ x : Word k m, U (Erdos171.restrictWord x) ∈ A

end RestrictedPart

section Insensitive

variable {k m n : ℕ}

end Insensitive

section Conversion

theorem hasLine_iff_containsLine {t n : ℕ} (A : Finset (Word t n)) :
    HasLine A ↔ Erdos171.ContainsLine (A : Set (Word t n)) := by
  simpa only [HasLine] using
    (Erdos171.containsLine_coe_finset_iff (A := A)).symm

end Conversion

end DHJ

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos185/DHJ/Density.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Uniform density and sections of finite cubes

This file contains the elementary finite-probability layer used by the
density-increment proof of density Hales--Jewett for three letters.  It is
deliberately independent of the unfinished Erdős 171 density framework.
All densities and averages take values in `ℝ`, and every identity below is
an exact identity between finite sums.
-/

open scoped BigOperators

namespace DHJ

section FiniteProbability

variable {X Y : Type*}

/-- Uniform average of a real-valued function on a finite type. -/
noncomputable def average [Fintype X] (f : X → ℝ) : ℝ :=
  𝔼 x, f x

/-- Uniform density of a finset in its ambient finite type. -/
noncomputable def density [Fintype X] (A : Finset X) : ℝ :=
  (A.card : ℝ) / Fintype.card X

@[simp] theorem average_eq_sum_div_card [Fintype X] (f : X → ℝ) :
    average f = (∑ x, f x) / Fintype.card X := by
  simp [average, Fintype.expect_eq_sum_div_card]

@[simp] theorem density_eq_card_div_card [Fintype X] (A : Finset X) :
    density A = (A.card : ℝ) / Fintype.card X :=
  rfl

@[simp] theorem density_empty [Fintype X] : density (∅ : Finset X) = 0 := by
  simp [density]

@[simp] theorem density_univ [Fintype X] [Nonempty X] :
    density (Finset.univ : Finset X) = 1 := by
  simp [density]

theorem density_nonneg [Fintype X] (A : Finset X) : 0 ≤ density A := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem density_le_one [Fintype X] (A : Finset X) : density A ≤ 1 := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
      letI := hX
      have hA : A = ∅ := by
        ext x
        exact isEmptyElim x
      simp [hA]
  | inr hX =>
      letI := hX
      rw [density, div_le_one (by positivity)]
      exact_mod_cast Finset.card_le_univ A

theorem density_mono [Fintype X] {A B : Finset X} (hAB : A ⊆ B) :
    density A ≤ density B := by
  unfold density
  gcongr

/-- Density is preserved by an equivalence of finite ambient types. -/
theorem density_map_equiv [Fintype X] [Fintype Y]
    (e : X ≃ Y) (A : Finset X) :
    density (A.map e.toEmbedding) = density A := by
  simp [density, Fintype.card_congr e]

theorem average_const [Fintype X] [Nonempty X] (c : ℝ) :
    average (fun _ : X ↦ c) = c := by
  simp [average, Fintype.expect_const]

theorem average_add [Fintype X] (f g : X → ℝ) :
    average (fun x ↦ f x + g x) = average f + average g := by
  simp [average, Finset.expect_add_distrib]

theorem average_sub [Fintype X] (f g : X → ℝ) :
    average (fun x ↦ f x - g x) = average f - average g := by
  simp [average, Finset.expect_sub_distrib]

theorem average_mul_const [Fintype X] (f : X → ℝ) (c : ℝ) :
    average (fun x ↦ f x * c) = average f * c := by
  simp [average, Finset.expect_mul]

theorem average_mono [Fintype X] {f g : X → ℝ}
    (hfg : ∀ x, f x ≤ g x) : average f ≤ average g := by
  simp only [average_eq_sum_div_card]
  gcongr with x
  exact hfg x

theorem average_le_const [Fintype X] [Nonempty X] {f : X → ℝ} {c : ℝ}
    (hf : ∀ x, f x ≤ c) : average f ≤ c := by
  simpa [average_const] using
    average_mono (f := f) (g := fun _ ↦ c) hf

theorem const_le_average [Fintype X] [Nonempty X] {f : X → ℝ} {c : ℝ}
    (hf : ∀ x, c ≤ f x) : c ≤ average f := by
  simpa [average_const] using
    average_mono (f := fun _ ↦ c) (g := f) hf

/-- Some value of a function is at least its uniform average. -/
theorem exists_average_le [Fintype X] [Nonempty X] (f : X → ℝ) :
    ∃ x, average f ≤ f x := by
  by_contra! h
  have hsum : (∑ x, f x) < ∑ _x : X, average f :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun x _ ↦ h x)
  have hcard : (Fintype.card X : ℝ) ≠ 0 := by positivity
  rw [average_eq_sum_div_card, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hcancel : (Fintype.card X : ℝ) *
      ((∑ x, f x) / Fintype.card X) = ∑ x, f x := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hcard
  rw [hcancel] at hsum
  exact hsum.false

/-- The fibre of a finset in a product after fixing its first coordinate. -/
noncomputable def fiber [Fintype Y] (A : Finset (X × Y)) (x : X) : Finset Y := by
  classical
  exact Finset.univ.filter fun y ↦ (x, y) ∈ A

@[simp] theorem mem_fiber [Fintype Y] (A : Finset (X × Y)) (x : X) (y : Y) :
    y ∈ fiber A x ↔ (x, y) ∈ A := by
  classical
  simp [fiber]

/-- Exact fibrewise counting for a subset of a finite product. -/
theorem card_eq_sum_card_fiber [Fintype X] [Fintype Y]
    (A : Finset (X × Y)) : A.card = ∑ x, (fiber A x).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (s := A) (t := Finset.univ) (f := Prod.fst) (by simp)]
  apply Finset.sum_congr rfl
  intro x _
  refine Finset.card_bij (fun p _ ↦ p.2) ?_ ?_ ?_
  · intro p hp
    have hp' := Finset.mem_filter.1 hp
    apply (mem_fiber A x p.2).2
    rw [← hp'.2]
    simpa using hp'.1
  · intro p hp q hq hpq
    apply Prod.ext
    · have hp' := (Finset.mem_filter.1 hp).2
      have hq' := (Finset.mem_filter.1 hq).2
      simpa [hp', hq']
    · exact hpq
  · intro y hy
    refine ⟨(x, y), ?_, rfl⟩
    have hy' : (x, y) ∈ A := (mem_fiber A x y).1 hy
    simp [hy']

/-- Density in a product is the average of the densities of its fibres. -/
theorem density_eq_average_fiber [Fintype X] [Fintype Y]
    (A : Finset (X × Y)) :
    density A = average fun x ↦ density (fiber A x) := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
      letI := hX
      simp [density_eq_card_div_card, average_eq_sum_div_card]
  | inr hX =>
      letI := hX
      cases isEmpty_or_nonempty Y with
      | inl hY =>
          letI := hY
          simp [density_eq_card_div_card, average_eq_sum_div_card]
      | inr hY =>
          letI := hY
          rw [density_eq_card_div_card, average_eq_sum_div_card]
          rw [card_eq_sum_card_fiber]
          simp only [density_eq_card_div_card]
          rw [Fintype.card_prod]
          push_cast
          rw [← Finset.sum_div]
          have hXcard : (Fintype.card X : ℝ) ≠ 0 := by positivity
          have hYcard : (Fintype.card Y : ℝ) ≠ 0 := by positivity
          field_simp

/-- A product set has a fibre at least as dense as the whole set. -/
theorem exists_fiber_density_ge [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (A : Finset (X × Y)) :
    ∃ x, density A ≤ density (fiber A x) := by
  rw [density_eq_average_fiber]
  exact exists_average_le _

/-- The indicator of a finset has average equal to its density. -/
theorem average_indicator [Fintype X] [DecidableEq X] (A : Finset X) :
    average (fun x ↦ if x ∈ A then (1 : ℝ) else 0) = density A := by
  classical
  simp [average_eq_sum_div_card, density_eq_card_div_card, Finset.sum_boole]

/-- The exact average of a function which is constant on a finset and its complement. -/
theorem average_piecewise_const [Fintype X] [Nonempty X] [DecidableEq X]
    (A : Finset X) (a b : ℝ) :
    average (fun x ↦ if x ∈ A then a else b) =
      density A * a + (1 - density A) * b := by
  let ι : X → ℝ := fun x ↦ if x ∈ A then 1 else 0
  have hpoint : (fun x ↦ if x ∈ A then a else b) =
      fun x ↦ ι x * a + (1 - ι x) * b := by
    funext x
    simp only [ι]
    split <;> ring
  rw [hpoint, average_add, average_mul_const, average_mul_const,
    average_sub, average_const, average_indicator]

/-- The set where a real-valued function is at least a prescribed threshold. -/
noncomputable def superlevel [Fintype X] (f : X → ℝ) (c : ℝ) : Finset X := by
  classical
  exact Finset.univ.filter fun x ↦ c ≤ f x

@[simp] theorem mem_superlevel [Fintype X] (f : X → ℝ) (c : ℝ) (x : X) :
    x ∈ superlevel f c ↔ c ≤ f x := by
  classical
  simp [superlevel]

/-- Quantitative averaging.  If `f ≤ B` and `μ ≤ average f`, the set on
which `f ≥ c` has density at least `(μ-c)/(B-c)`. -/
theorem density_superlevel_ge [Fintype X] [Nonempty X] [DecidableEq X]
    (f : X → ℝ) {mu c B : ℝ} (havg : mu ≤ average f)
    (hub : ∀ x, f x ≤ B) (hcB : c < B) :
    (mu - c) / (B - c) ≤ density (superlevel f c) := by
  have hpoint : ∀ x, f x ≤
      (if x ∈ superlevel f c then B else c) := by
    intro x
    by_cases hx : x ∈ superlevel f c
    · simpa [hx] using hub x
    · simp only [hx, if_false]
      exact le_of_lt (not_le.1 (by simpa using hx))
  have havg' : average f ≤ density (superlevel f c) * B +
      (1 - density (superlevel f c)) * c := by
    calc
      average f ≤ average (fun x ↦ if x ∈ superlevel f c then B else c) :=
        average_mono hpoint
      _ = density (superlevel f c) * B +
          (1 - density (superlevel f c)) * c :=
        average_piecewise_const (superlevel f c) B c
  rw [div_le_iff₀ (sub_pos.2 hcB)]
  nlinarith

/-- Prefixes whose corresponding fibre has density at least `c`. -/
noncomputable def largeFibers [Fintype X] [Fintype Y]
    (A : Finset (X × Y)) (c : ℝ) : Finset X :=
  superlevel (fun x ↦ density (fiber A x)) c

@[simp] theorem mem_largeFibers [Fintype X] [Fintype Y]
    (A : Finset (X × Y)) (c : ℝ) (x : X) :
    x ∈ largeFibers A c ↔ c ≤ density (fiber A x) := by
  simp [largeFibers]

/-- Half-threshold version: a `[0,1]`-valued function of average at least
`δ` is at least `δ/2` on a set of density at least `δ/2`. -/
theorem half_le_density_superlevel [Fintype X] [Nonempty X] [DecidableEq X]
    (f : X → ℝ) {delta : ℝ} (hdelta : 0 ≤ delta)
    (havg : delta ≤ average f) (hub : ∀ x, f x ≤ 1) :
    delta / 2 ≤ density (superlevel f (delta / 2)) := by
  have hmain := density_superlevel_ge f havg hub
    (show delta / 2 < 1 by
      have hdelta1 : delta ≤ 1 := havg.trans (average_le_const hub)
      linarith)
  have hdens0 := density_nonneg (superlevel f (delta / 2))
  have hdens1 := density_le_one (superlevel f (delta / 2))
  rw [div_le_iff₀ (show 0 < (1 : ℝ) - delta / 2 by
    have hdelta1 : delta ≤ 1 := havg.trans (average_le_const hub)
    linarith)] at hmain
  nlinarith

end FiniteProbability

section CubeSections

/-- A generic finite word, kept separate from the ternary `Erdos185.Word`. -/
abbrev Cube (k n : ℕ) := Erdos171.Word k n

/-- Split a word into an initial block and a final block. -/
def wordSplitEquiv (k m r : ℕ) : Cube k (m + r) ≃ Cube k m × Cube k r :=
  (Equiv.piCongrLeft (fun _ : Fin (m + r) ↦ Fin k) finSumFinEquiv).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin r) (Fin k))

@[simp] theorem wordSplitEquiv_apply_fst (k m r : ℕ) (w : Cube k (m + r))
    (i : Fin m) : (wordSplitEquiv k m r w).1 i = w (Fin.castAdd r i) := by
  simp [wordSplitEquiv]

@[simp] theorem wordSplitEquiv_apply_snd (k m r : ℕ) (w : Cube k (m + r))
    (i : Fin r) : (wordSplitEquiv k m r w).2 i = w (Fin.natAdd m i) := by
  simp [wordSplitEquiv]

/-- The product-coordinate form of a set in a cube split after `m` coordinates. -/
noncomputable def splitFinset {k m r : ℕ} (A : Finset (Cube k (m + r))) :
    Finset (Cube k m × Cube k r) :=
  A.map (wordSplitEquiv k m r).toEmbedding

@[simp] theorem mem_splitFinset {k m r : ℕ} (A : Finset (Cube k (m + r)))
    (x : Cube k m) (y : Cube k r) :
    (x, y) ∈ splitFinset A ↔ (wordSplitEquiv k m r).symm (x, y) ∈ A := by
  classical
  simp [splitFinset]

/-- The section `A_x` obtained by fixing the first `m` coordinates to `x`. -/
noncomputable def prefixSection {k m r : ℕ} (A : Finset (Cube k (m + r)))
    (x : Cube k m) : Finset (Cube k r) :=
  fiber (splitFinset A) x

@[simp] theorem mem_prefixSection {k m r : ℕ}
    (A : Finset (Cube k (m + r))) (x : Cube k m) (y : Cube k r) :
    y ∈ prefixSection A x ↔ (wordSplitEquiv k m r).symm (x, y) ∈ A := by
  simp [prefixSection]

@[simp] theorem card_splitFinset {k m r : ℕ} (A : Finset (Cube k (m + r))) :
    (splitFinset A).card = A.card := by
  simp [splitFinset]

/-- Density of a cube set is the average of the densities of all its prefix sections. -/
theorem density_eq_average_prefixSection {k m r : ℕ}
    (A : Finset (Cube k (m + r))) :
    density A = average fun x : Cube k m ↦ density (prefixSection A x) := by
  have hmap : density (splitFinset A) = density A :=
    density_map_equiv (wordSplitEquiv k m r) A
  rw [← hmap, density_eq_average_fiber]
  rfl

/-- Prefixes supporting a section of density at least `c`. -/
noncomputable def largePrefixSections {k m r : ℕ}
    (A : Finset (Cube k (m + r))) (c : ℝ) : Finset (Cube k m) :=
  superlevel (fun x ↦ density (prefixSection A x)) c

@[simp] theorem mem_largePrefixSections {k m r : ℕ}
    (A : Finset (Cube k (m + r))) (c : ℝ) (x : Cube k m) :
    x ∈ largePrefixSections A c ↔ c ≤ density (prefixSection A x) := by
  simp [largePrefixSections]

/-- Half-threshold form for prefix sections. -/
theorem half_le_density_largePrefixSections {k m r : ℕ} (hk : 0 < k)
    (A : Finset (Cube k (m + r))) {delta : ℝ}
    (hdelta : 0 ≤ delta) (hA : delta ≤ density A) :
    delta / 2 ≤ density (largePrefixSections A (delta / 2)) := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [density_eq_average_prefixSection] at hA
  simpa only [largePrefixSections] using
    half_le_density_superlevel (fun x ↦ density (prefixSection A x)) hdelta hA
      (fun x ↦ density_le_one _)

end CubeSections

end DHJ

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/Binary.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The binary density Hales--Jewett theorem

For the alphabet `Fin 2`, a combinatorial-line-free family is an antichain in
the Boolean lattice.  Sperner's theorem therefore bounds it by the middle
binomial coefficient.  An elementary squared central-binomial estimate then
shows that this bound has density tending to zero.
-/

namespace Erdos171

open Finset Set Function

/-- The support of a binary word: the coordinates carrying the letter `1`. -/
def binarySupport {n : ℕ} (x : Word 2 n) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ x i = 1)

@[simp] theorem mem_binarySupport {n : ℕ} {x : Word 2 n} {i : Fin n} :
    i ∈ binarySupport x ↔ x i = 1 := by
  simp [binarySupport]

theorem binarySupport_injective (n : ℕ) :
    Function.Injective (@binarySupport n) := by
  intro x y h
  funext i
  have hi : (x i = 1) ↔ (y i = 1) := by
    simpa only [mem_binarySupport] using Finset.ext_iff.mp h i
  apply Fin.ext
  omega

theorem binarySupport_subset_iff {n : ℕ} {x y : Word 2 n} :
    binarySupport x ⊆ binarySupport y ↔ ∀ i, x i ≤ y i := by
  constructor
  · intro h i
    have hi : x i = 1 → y i = 1 := by
      simpa only [mem_binarySupport] using @h i
    exact Fin.le_iff_val_le_val.mpr (by omega)
  · intro h i hi
    rw [mem_binarySupport] at hi ⊢
    have := h i
    apply Fin.ext
    omega

/-- Two binary words form an oriented combinatorial line when they are
distinct and coordinatewise ordered. -/
def BinaryLine {n : ℕ} (x y : Word 2 n) : Prop :=
  x ≠ y ∧ ∀ i, x i ≤ y i

theorem binaryLine_iff_support_ssubset {n : ℕ} {x y : Word 2 n} :
    BinaryLine x y ↔ binarySupport x ⊂ binarySupport y := by
  rw [BinaryLine, Finset.ssubset_iff_subset_ne, binarySupport_subset_iff]
  constructor
  · rintro ⟨hne, hle⟩
    exact ⟨hle, fun h ↦ hne ((binarySupport_injective n) h)⟩
  · rintro ⟨hle, hne⟩
    exact ⟨fun h ↦ hne (congrArg binarySupport h), hle⟩

/-- The proper Mathlib combinatorial line determined by an oriented pair of
binary words.  A coordinate is a wildcard exactly where the endpoints differ. -/
def lineOfBinaryLine {n : ℕ} (x y : Word 2 n) (h : BinaryLine x y) :
    Combinatorics.Line (Fin 2) (Fin n) where
  idxFun i := if x i = y i then some (x i) else none
  proper := by
    by_contra! hall
    apply h.1
    funext i
    simpa using hall i

@[simp] theorem lineOfBinaryLine_zero {n : ℕ} (x y : Word 2 n)
    (h : BinaryLine x y) : lineOfBinaryLine x y h 0 = x := by
  funext i
  by_cases hi : x i = y i
  · simp [lineOfBinaryLine, Combinatorics.Line.coe_apply, hi]
  · have hle := h.2 i
    apply Fin.ext
    simp [lineOfBinaryLine, Combinatorics.Line.coe_apply, hi]
    omega

@[simp] theorem lineOfBinaryLine_one {n : ℕ} (x y : Word 2 n)
    (h : BinaryLine x y) : lineOfBinaryLine x y h 1 = y := by
  funext i
  by_cases hi : x i = y i
  · simp [lineOfBinaryLine, Combinatorics.Line.coe_apply, hi]
  · have hle := h.2 i
    apply Fin.ext
    simp [lineOfBinaryLine, Combinatorics.Line.coe_apply, hi]
    omega

/-- An oriented binary pair in a set supplies a proper `Combinatorics.Line`. -/
theorem containsLine_of_binaryLine {n : ℕ} {A : Set (Word 2 n)}
    {x y : Word 2 n} (hx : x ∈ A) (hy : y ∈ A) (hxy : BinaryLine x y) :
    ContainsLine A := by
  refine ⟨lineOfBinaryLine x y hxy, ?_⟩
  rintro _ ⟨a, rfl⟩
  fin_cases a
  · simpa using hx
  · simpa using hy

theorem antichain_image_binarySupport {n : ℕ} (A : Finset (Word 2 n))
    (hA : ∀ x ∈ A, ∀ y ∈ A, ¬ BinaryLine x y) :
    IsAntichain (· ⊆ ·)
      ((A.image binarySupport : Finset (Finset (Fin n))) : Set (Finset (Fin n))) := by
  intro s hs t ht hne hst
  simp only [Finset.mem_coe, Finset.mem_image] at hs ht
  obtain ⟨x, hxA, rfl⟩ := hs
  obtain ⟨y, hyA, hy⟩ := ht
  subst hy
  apply hA x hxA y hyA
  rw [binaryLine_iff_support_ssubset, Finset.ssubset_iff_subset_ne]
  exact ⟨hst, hne⟩

/-- Sperner's sharp upper bound for a binary line-free family. -/
theorem binary_line_free_card_le_choose {n : ℕ} (A : Finset (Word 2 n))
    (hA : ¬ ContainsLine (A : Set (Word 2 n))) :
    A.card ≤ n.choose (n / 2) := by
  have hpair : ∀ x ∈ A, ∀ y ∈ A, ¬ BinaryLine x y := by
    intro x hx y hy hxy
    exact hA (containsLine_of_binaryLine hx hy hxy)
  have hanti := antichain_image_binarySupport A hpair
  have hs := hanti.sperner
  rw [Finset.card_image_of_injective A (binarySupport_injective n)] at hs
  simpa using hs

/-- A convenient squared estimate for the central binomial coefficient. -/
theorem centralBinom_sq_bound : ∀ m : ℕ,
    (m + 1) * (Nat.centralBinom m) ^ 2 ≤ 16 ^ m := by
  intro m
  induction m with
  | zero => norm_num [Nat.centralBinom]
  | succ m ih =>
      have hrec := Nat.succ_mul_centralBinom_succ m
      have hpoly : (m + 2) * (2 * (2 * m + 1)) ^ 2 ≤ 16 * (m + 1) ^ 3 := by
        nlinarith
      have hmul :
          (m + 2) * (m + 1) ^ 2 * (Nat.centralBinom (m + 1)) ^ 2 ≤
            16 * (m + 1) ^ 2 * 16 ^ m := by
        calc
          (m + 2) * (m + 1) ^ 2 * (Nat.centralBinom (m + 1)) ^ 2
              = (m + 2) * (2 * (2 * m + 1)) ^ 2 * (Nat.centralBinom m) ^ 2 := by
                  have hrec_sq := congrArg (fun z : ℕ ↦ z ^ 2) hrec
                  nlinarith
          _ ≤ 16 * (m + 1) ^ 3 * (Nat.centralBinom m) ^ 2 := by gcongr
          _ = 16 * (m + 1) ^ 2 * ((m + 1) * (Nat.centralBinom m) ^ 2) := by ring
          _ ≤ 16 * (m + 1) ^ 2 * 16 ^ m := by gcongr
      have hpos : 0 < (m + 1) ^ 2 := by positivity
      refine Nat.le_of_mul_le_mul_left ?_ hpos
      rw [pow_succ]
      convert hmul using 1 <;> ring

/-- Uniform (even and odd dimension) squared upper bound for the middle
binomial coefficient. -/
theorem choose_middle_sq_bound (n : ℕ) :
    (n / 2 + 1) * (n.choose (n / 2)) ^ 2 ≤ 2 ^ (2 * n) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · simpa [Nat.centralBinom, pow_mul] using centralBinom_sq_bound m
  · have hchoose : (2 * m + 1).choose m ≤ 2 * Nat.centralBinom m := by
      cases m with
      | zero => norm_num [Nat.centralBinom]
      | succ k =>
          rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 by omega,
            Nat.choose_succ_succ' (2 * (k + 1)) k]
          rw [two_mul]
          simpa [two_mul] using
            Nat.add_le_add (Nat.choose_le_centralBinom k (k + 1))
              (Nat.choose_le_centralBinom (k + 1) (k + 1))
    calc
      ((2 * m + 1) / 2 + 1) * ((2 * m + 1).choose ((2 * m + 1) / 2)) ^ 2
          ≤ (m + 1) * (2 * Nat.centralBinom m) ^ 2 := by
              rw [show (2 * m + 1) / 2 = m by omega]
              exact Nat.mul_le_mul_left (m + 1) (Nat.pow_le_pow_left hchoose 2)
      _ = 4 * ((m + 1) * (Nat.centralBinom m) ^ 2) := by ring
      _ ≤ 4 * 16 ^ m := by gcongr; exact centralBinom_sq_bound m
      _ = 2 ^ (2 * (2 * m + 1)) := by
        rw [show 4 = 2 ^ 2 by norm_num, show 16 = 2 ^ 4 by norm_num,
          ← pow_mul, ← pow_add]
        congr 1
        omega

/-- The density Hales--Jewett theorem for the binary alphabet, for finite
families.  The proof gives the explicit threshold `2 * M` for any natural
`M > (ε²)⁻¹`. -/
theorem exists_containsLine_of_dense_binary_finset (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset (Word 2 n),
      eps * (2 : ℝ) ^ n ≤ A.card → ContainsLine (A : Set (Word 2 n)) := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (eps ^ 2)⁻¹ < M := exists_nat_gt ((eps ^ 2)⁻¹)
  refine ⟨2 * M, ?_⟩
  intro n hn A hdense
  by_contra hfree
  have hcard := binary_line_free_card_le_choose A hfree
  have hcardR : (A.card : ℝ) ≤ n.choose (n / 2) := by exact_mod_cast hcard
  have hdense' : eps * (2 : ℝ) ^ n ≤ n.choose (n / 2) := hdense.trans hcardR
  have hsq : (eps * (2 : ℝ) ^ n) ^ 2 ≤ ((n.choose (n / 2) : ℕ) : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hdense'
  have hbound :
      (((n / 2 + 1 : ℕ) : ℝ) * ((n.choose (n / 2) : ℕ) : ℝ) ^ 2) ≤
        ((2 : ℝ) ^ n) ^ 2 := by
    have hb := choose_middle_sq_bound n
    have hbR :
        (((n / 2 + 1 : ℕ) : ℝ) * ((n.choose (n / 2) : ℕ) : ℝ) ^ 2) ≤
          (2 : ℝ) ^ (2 * n) := by
      exact_mod_cast hb
    simpa [pow_two, ← pow_add, two_mul] using hbR
  have hcombined :
      (((n / 2 + 1 : ℕ) : ℝ) * eps ^ 2) * ((2 : ℝ) ^ n) ^ 2 ≤
        ((2 : ℝ) ^ n) ^ 2 := by
    calc
      (((n / 2 + 1 : ℕ) : ℝ) * eps ^ 2) * ((2 : ℝ) ^ n) ^ 2 =
          ((n / 2 + 1 : ℕ) : ℝ) * (eps * (2 : ℝ) ^ n) ^ 2 := by ring
      _ ≤ ((n / 2 + 1 : ℕ) : ℝ) * ((n.choose (n / 2) : ℕ) : ℝ) ^ 2 := by
        gcongr
      _ ≤ ((2 : ℝ) ^ n) ^ 2 := hbound
  have hcoef : ((n / 2 + 1 : ℕ) : ℝ) * eps ^ 2 ≤ 1 := by
    have hq : 0 < ((2 : ℝ) ^ n) ^ 2 := by positivity
    exact le_of_mul_le_mul_right (by simpa using hcombined) hq
  have hMdiv : M ≤ n / 2 := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hMcast : (M : ℝ) ≤ ((n / 2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast (hMdiv.trans (by omega))
  have hepssq : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hMinv : (eps ^ 2)⁻¹ * eps ^ 2 = 1 := by
    field_simp
  have hlarge : 1 < ((n / 2 + 1 : ℕ) : ℝ) * eps ^ 2 := by
    have := mul_lt_mul_of_pos_right (hM.trans_le hMcast) hepssq
    nlinarith
  exact (not_lt_of_ge hcoef) hlarge

end Erdos171

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos185/DHJ/BinaryMulti.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Multidimensional density Hales--Jewett for the binary alphabet

This is the finite, exact-dimension version of the elementary implication
`DHJ(2) -> MDHJ(2)`.  The successor step splits the cube into two blocks.
On a positive-density set of prefixes the final-block section contains a
line.  Pigeonholing the finitely many possible lines, and applying the
induction hypothesis to one colour class, supplies a common line over an
`m`-dimensional subspace of prefixes.  Its independent product with that
line is the required `(m+1)`-subspace.
-/

namespace DHJ

open scoped BigOperators

private noncomputable def colorGraph {X C : Type*}
    (D : Finset X) (color : X -> C) : Finset (C × X) := by
  classical
  exact D.map
    ⟨fun x => (color x, x), fun _ _ h => congrArg Prod.snd h⟩

private theorem mem_colorGraph {X C : Type*}
    (D : Finset X) (color : X -> C) (c : C) (x : X) :
    (c, x) ∈ colorGraph D color ↔ x ∈ D ∧ color x = c := by
  classical
  constructor
  · rw [colorGraph, Finset.mem_map]
    rintro ⟨y, hy, hpair⟩
    have hyx : y = x := congrArg Prod.snd hpair
    subst y
    exact ⟨hy, congrArg Prod.fst hpair⟩
  · rintro ⟨hx, hcolor⟩
    rw [colorGraph, Finset.mem_map]
    exact ⟨x, hx, Prod.ext hcolor rfl⟩

private theorem density_colorGraph {X C : Type*} [Fintype X] [Fintype C]
    (D : Finset X) (color : X -> C) :
    density (colorGraph D color) = density D / Fintype.card C := by
  classical
  simp only [density_eq_card_div_card, colorGraph, Finset.card_map,
    Fintype.card_prod]
  push_cast
  ring

private noncomputable def colorClass {X C : Type*} [Fintype X]
    (D : Finset X) (color : X -> C) (c : C) : Finset X := by
  classical
  exact Finset.univ.filter fun x => x ∈ D ∧ color x = c

@[simp] private theorem mem_colorClass {X C : Type*} [Fintype X]
    (D : Finset X) (color : X -> C) (c : C) (x : X) :
    x ∈ colorClass D color c ↔ x ∈ D ∧ color x = c := by
  classical
  simp [colorClass]

private theorem exists_dense_colorClass {X C : Type*} [Fintype X] [Fintype C]
    [Nonempty X] [Nonempty C] (D : Finset X) (color : X -> C) :
    ∃ c : C, density D / Fintype.card C ≤
      density (colorClass D color c) := by
  classical
  obtain ⟨c, hc⟩ := exists_fiber_density_ge (colorGraph D color)
  have hfiber : fiber (colorGraph D color) c = colorClass D color c := by
    ext x
    simp [mem_colorGraph]
  refine ⟨c, ?_⟩
  rw [density_colorGraph] at hc
  simpa only [hfiber] using hc

/-- Regard a line as a one-dimensional subspace. -/
private def lineSubspace {α ι : Type*} (l : Combinatorics.Line α ι) :
    Combinatorics.Subspace (Fin 1) α ι where
  idxFun i := (l.idxFun i).elim (Sum.inr 0) Sum.inl
  proper e := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i, by simp [hi, Fin.eq_zero e]⟩

@[simp] private theorem lineSubspace_apply {α ι : Type*}
    (l : Combinatorics.Line α ι) (x : Fin 1 -> α) :
    lineSubspace l x = l (x 0) := by
  funext i
  cases hi : l.idxFun i <;>
    simp [lineSubspace, Combinatorics.Line.coe_apply,
      Combinatorics.Subspace.coe_apply, hi]

private theorem wordSplitEquiv_finSum_line_apply {m q p : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin 2) (Fin q))
    (l : Combinatorics.Line (Fin 2) (Fin p)) (x : Word 2 (m + 1)) :
    wordSplitEquiv 2 q p (U.finSum (lineSubspace l) x) =
      (U (fun i => x (Fin.castAdd 1 i)), l (x (Fin.last m))) := by
  apply Prod.ext
  · funext i
    simp [wordSplitEquiv_apply_fst, Function.comp_def]
  · funext i
    simp only [wordSplitEquiv_apply_snd,
      Combinatorics.Subspace.finSum_apply_natAdd, lineSubspace_apply]
    have hzero : Fin.natAdd m (0 : Fin 1) = Fin.last m := by
      ext
      simp
    rw [Function.comp_apply, hzero]

/-- A density lower bound, in the local normalized-density convention,
supplies a binary line using the Sperner proof in `Erdos171.Binary`. -/
private theorem exists_binary_line_of_density (delta : ℝ) (hdelta : 0 < delta) :
    ∃ p : ℕ, 0 < p ∧ ∀ A : Finset (Word 2 p), delta ≤ density A ->
      ∃ l : Combinatorics.Line (Fin 2) (Fin p), ∀ a, l a ∈ A := by
  obtain ⟨N, hN⟩ :=
    Erdos171.exists_containsLine_of_dense_binary_finset delta hdelta
  refine ⟨N + 1, by omega, ?_⟩
  intro A hA
  have hcard : delta * (2 : ℝ) ^ (N + 1) ≤ A.card := by
    have hden : delta ≤ (A.card : ℝ) / (2 : ℝ) ^ (N + 1) := by
      simpa [density, Word] using hA
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (N + 1))).mp hden
  have hline := hN (N + 1) (by omega) A hcard
  exact Erdos171.containsLine_coe_finset_iff.mp hline

/-- Every positive-density subset of a suitably chosen binary cube contains
an `m`-dimensional combinatorial subspace.  The dimension `N` is an exact
witness; no monotonicity in the ambient dimension is needed here. -/
theorem binary_multidimensional (m : ℕ) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ N : ℕ, ∀ A : Finset (Word 2 N), delta ≤ density A ->
      ∃ U : Combinatorics.Subspace (Fin m) (Fin 2) (Fin N),
        ∀ x : Word 2 m, U x ∈ A := by
  classical
  induction m generalizing delta with
  | zero =>
      refine ⟨0, ?_⟩
      intro A hA
      have hpos : 0 < density A := hdelta.trans_le hA
      have hne : A.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hAempty
        subst A
        simpa using hpos
      obtain ⟨a, ha⟩ := hne
      let U : Combinatorics.Subspace (Fin 0) (Fin 2) (Fin 0) :=
        { idxFun := Fin.elim0
          proper := fun e => Fin.elim0 e }
      refine ⟨U, ?_⟩
      intro x
      convert ha using 1
  | succ m ih =>
      obtain ⟨p, hp0, hp⟩ :=
        exists_binary_line_of_density (delta / 2) (by positivity)
      let LineType := Combinatorics.Line (Fin 2) (Fin p)
      let K := Fintype.card LineType
      haveI : Nonempty LineType := by
        let i : Fin p := ⟨0, hp0⟩
        exact ⟨{ idxFun := fun _ => none, proper := ⟨i, rfl⟩ }⟩
      have hK : 0 < K := Fintype.card_pos
      have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
      let delta' : ℝ := delta / (2 * (K : ℝ))
      have hdelta' : 0 < delta' := by
        dsimp [delta']
        exact div_pos hdelta (mul_pos (by norm_num) hKreal)
      obtain ⟨q, hq⟩ := ih delta' hdelta'
      refine ⟨q + p, ?_⟩
      intro A hA
      let G : Finset (Word 2 q) := largePrefixSections A (delta / 2)
      have hG : delta / 2 ≤ density G := by
        exact half_le_density_largePrefixSections (k := 2) (m := q) (r := p)
          (by omega) A hdelta.le hA
      have hline : ∀ x ∈ G,
          ∃ l : LineType, ∀ a : Fin 2, l a ∈ prefixSection A x := by
        intro x hx
        apply hp
        simpa only [G, mem_largePrefixSections] using hx
      let chosenLine : Word 2 q -> LineType := fun x =>
        if hx : x ∈ G then Classical.choose (hline x hx)
        else Classical.choice inferInstance
      have chosenLine_spec (x : Word 2 q) (hx : x ∈ G) :
          ∀ a : Fin 2, chosenLine x a ∈ prefixSection A x := by
        dsimp only [chosenLine]
        rw [dif_pos hx]
        exact Classical.choose_spec (hline x hx)
      obtain ⟨l, hl⟩ := exists_dense_colorClass G chosenLine
      have hclass : delta' ≤ density (colorClass G chosenLine l) := by
        calc
          delta' = (delta / 2) / (K : ℝ) := by
            dsimp [delta', K]
            ring
          _ ≤ density G / (K : ℝ) := by
            gcongr
          _ ≤ density (colorClass G chosenLine l) := by
            simpa only [K, LineType] using hl
      obtain ⟨U, hU⟩ := hq (colorClass G chosenLine l) hclass
      refine ⟨U.finSum (lineSubspace l), ?_⟩
      intro z
      let x : Word 2 m := fun i => z (Fin.castAdd 1 i)
      let a : Fin 2 := z (Fin.last m)
      have hUx : U x ∈ G ∧ chosenLine (U x) = l := by
        simpa only [mem_colorClass] using hU x
      have hsection : l a ∈ prefixSection A (U x) := by
        rw [← hUx.2]
        exact chosenLine_spec (U x) hUx.1 a
      rw [mem_prefixSection] at hsection
      have hsplit : wordSplitEquiv 2 q p (U.finSum (lineSubspace l) z) =
          (U x, l a) := by
        simpa only [x, a] using wordSplitEquiv_finSum_line_apply U l z
      have hjoin : (wordSplitEquiv 2 q p).symm (U x, l a) =
          U.finSum (lineSubspace l) z := by
        apply (wordSplitEquiv 2 q p).injective
        simp [hsplit]
      simpa only [hjoin] using hsection

end DHJ

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos185/DHJ/Uniformity.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Uniform sections for the ternary density Hales--Jewett argument

This file formalizes the elementary stopping argument of Dodos--Kanellopoulos--
Tyros.  A cube is exposed one block at a time.  If one section is too small,
averaging supplies another section whose density has increased by a fixed
amount.  Since density is at most one, after finitely many blocks one exposed
block has all of its sections close to the original density.

The recursive `Tower` representation below keeps the stopping argument free of
coordinate arithmetic.  At the public interface the tower is reindexed by a
finite equivalence, so the resulting subspace has the usual `Fin N` ambient
coordinates.
-/

open scoped BigOperators

namespace DHJ

open Combinatorics

universe u

/-! ## Towers of equal finite blocks -/

/-- `Tower X Y b` consists of `b` successive `X`-blocks followed by a tail
of type `Y`. -/
def Tower (X Y : Type u) : ℕ → Type u
  | 0 => Y
  | b + 1 => X × Tower X Y b

attribute [reducible] Tower

noncomputable instance towerFintype (X Y : Type u) [Fintype X] [Fintype Y] :
    (b : ℕ) → Fintype (Tower X Y b)
  | 0 => inferInstanceAs (Fintype Y)
  | b + 1 => by
      letI := towerFintype X Y b
      exact inferInstanceAs (Fintype (X × Tower X Y b))

instance towerNonempty (X Y : Type u) [Nonempty X] [Nonempty Y] :
    (b : ℕ) → Nonempty (Tower X Y b)
  | 0 => inferInstanceAs (Nonempty Y)
  | b + 1 => by
      letI := towerNonempty X Y b
      exact inferInstanceAs (Nonempty (X × Tower X Y b))

/-- A hole records one distinguished block in a tower and the values frozen
in all blocks preceding it. -/
inductive BlockHole (X Y : Type u) : ℕ → Type u
  | here (b : ℕ) : BlockHole X Y (b + 1)
  | later {b : ℕ} (x : X) (h : BlockHole X Y b) : BlockHole X Y (b + 1)

namespace BlockHole

/-- The still-unfrozen tail following the distinguished block. -/
def Tail {X Y : Type u} : {b : ℕ} → BlockHole X Y b → Type u
  | _, .here b => Tower X Y b
  | _, .later _ h => h.Tail

attribute [reducible] Tail

noncomputable def tailFintype {X Y : Type u} [Fintype X] [Fintype Y] :
    {b : ℕ} → (h : BlockHole X Y b) → Fintype h.Tail
  | _, .here b => towerFintype X Y b
  | _, .later _ h => h.tailFintype

def tailNonempty {X Y : Type u} [Nonempty X] [Nonempty Y] :
    {b : ℕ} → (h : BlockHole X Y b) → Nonempty h.Tail
  | _, .here b => towerNonempty X Y b
  | _, .later _ h => h.tailNonempty

noncomputable instance instTailFintype {X Y : Type u} [Fintype X] [Fintype Y]
    {b : ℕ} (h : BlockHole X Y b) : Fintype h.Tail :=
  h.tailFintype

instance instTailNonempty {X Y : Type u} [Nonempty X] [Nonempty Y]
    {b : ℕ} (h : BlockHole X Y b) : Nonempty h.Tail :=
  h.tailNonempty

/-- Fill the distinguished block and the remaining tail of a hole. -/
def fill {X Y : Type u} : {b : ℕ} → (h : BlockHole X Y b) →
    X → h.Tail → Tower X Y b
  | _, .here _, x, z => (x, z)
  | _, .later p h, x, z => (p, h.fill x z)

/-- The section obtained by filling a hole's distinguished block with `x`. -/
noncomputable def holeSection {X Y : Type u} [Fintype X] [Fintype Y]
    {b : ℕ} (A : Finset (Tower X Y b)) (h : BlockHole X Y b) (x : X) :
    Finset h.Tail := by
  classical
  letI := h.tailFintype
  exact Finset.univ.filter fun z ↦ h.fill x z ∈ A

@[simp] theorem mem_section {X Y : Type u} [Fintype X] [Fintype Y]
    {b : ℕ} (A : Finset (Tower X Y b)) (h : BlockHole X Y b)
    (x : X) (z : h.Tail) :
    z ∈ h.holeSection A x ↔ h.fill x z ∈ A := by
  classical
  letI := h.tailFintype
  simp [holeSection]

@[simp] theorem section_here {X Y : Type u} [Fintype X] [Fintype Y]
    {b : ℕ} (A : Finset (Tower X Y (b + 1))) (x : X) :
    (BlockHole.here b).holeSection A x = fiber A x := by
  classical
  ext z
  rw [mem_section, mem_fiber]
  rfl

@[simp] theorem section_later {X Y : Type u} [Fintype X] [Fintype Y]
    {b : ℕ} (A : Finset (Tower X Y (b + 1))) (p x : X)
    (h : BlockHole X Y b) :
    (BlockHole.later p h).holeSection A x = h.holeSection (fiber A p) x := by
  classical
  letI := h.tailFintype
  ext z
  rw [mem_section, mem_section, mem_fiber]
  rfl

end BlockHole

/-! ## The finite stopping argument -/

/-- If one value lies `eps` below a finite average, another value lies more
than `rho` above it, provided `(card X - 1) * rho ≤ eps`. -/
theorem exists_gt_average_add_of_exists_lt_average_sub
    {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ)
    {eps rho : ℝ} (hrho : 0 < rho)
    (hspread : ((Fintype.card X : ℝ) - 1) * rho ≤ eps)
    (x₀ : X) (hx₀ : f x₀ < average f - eps) :
    ∃ x : X, average f + rho < f x := by
  classical
  by_contra! hub
  have hcard : 0 < (Fintype.card X : ℝ) := by positivity
  have hsum_average :
      (∑ x : X, f x) = (Fintype.card X : ℝ) * average f := by
    rw [average_eq_sum_div_card]
    field_simp
  have herase_card :
      ((Finset.univ.erase x₀).card : ℝ) = (Fintype.card X : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (by simp), Finset.card_univ]
    have hcNat : Fintype.card X - 1 + 1 = Fintype.card X :=
      Nat.sub_add_cancel (Fintype.card_pos_iff.mpr inferInstance)
    have hcReal : ((Fintype.card X - 1 : ℕ) : ℝ) + 1 = Fintype.card X := by
      exact_mod_cast hcNat
    linarith
  have herase :
      (∑ x ∈ Finset.univ.erase x₀, f x) ≤
        ∑ _x ∈ Finset.univ.erase x₀, (average f + rho) := by
    exact Finset.sum_le_sum fun x _ ↦ hub x
  have hlt :
      (∑ x : X, f x) < (Fintype.card X : ℝ) * average f := by
    calc
      (∑ x : X, f x) =
          (∑ x ∈ Finset.univ.erase x₀, f x) + f x₀ := by
            exact (Finset.sum_erase_add _ _
              (by simp : x₀ ∈ (Finset.univ : Finset X))).symm
      _ = f x₀ + ∑ x ∈ Finset.univ.erase x₀, f x := by
            ac_rfl
      _
          < (average f - eps) +
              ∑ _x ∈ Finset.univ.erase x₀, (average f + rho) :=
            add_lt_add_of_lt_of_le hx₀ herase
      _ = (average f - eps) +
            ((Fintype.card X : ℝ) - 1) * (average f + rho) := by
              rw [Finset.sum_const, nsmul_eq_mul, herase_card]
      _ ≤ (Fintype.card X : ℝ) * average f := by
            nlinarith
  linarith

/-- Stopping lemma with an explicit density budget.  The hypothesis says that
there are enough unexposed blocks for repeated increments of size `rho` to
cross the a priori upper bound one. -/
theorem tower_uniform_sections_aux
    {X Y : Type u} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    {eps rho : ℝ} (hrho : 0 < rho)
    (hspread : ((Fintype.card X : ℝ) - 1) * rho ≤ eps) :
    ∀ (b : ℕ) (A : Finset (Tower X Y b)),
      1 < density A + (b : ℝ) * rho →
      ∃ h : BlockHole X Y b, ∀ x : X,
        density A - eps ≤ density (h.holeSection A x) := by
  intro b
  induction b with
  | zero =>
      intro A hbudget
      have hle := density_le_one A
      norm_num only [Nat.cast_zero, zero_mul, add_zero] at hbudget
      exact (not_lt_of_ge hle hbudget).elim
  | succ b ih =>
      intro A hbudget
      by_cases huniform : ∀ x : X,
          density A - eps ≤ density (fiber A x)
      · refine ⟨BlockHole.here b, ?_⟩
        intro x
        rw [BlockHole.section_here]
        exact huniform x
      · push_neg at huniform
        obtain ⟨x₀, hx₀⟩ := huniform
        have havg : density A = average fun x : X ↦ density (fiber A x) :=
          density_eq_average_fiber A
        obtain ⟨p, hp⟩ :=
          exists_gt_average_add_of_exists_lt_average_sub
            (fun x : X ↦ density (fiber A x)) hrho hspread x₀ (by
              rw [← havg]
              exact hx₀)
        have hnext : 1 < density (fiber A p) + (b : ℝ) * rho := by
          rw [← havg] at hp
          norm_num only [Nat.cast_add, Nat.cast_one] at hbudget
          linarith
        obtain ⟨h, hh⟩ := ih (fiber A p) hnext
        refine ⟨BlockHole.later p h, ?_⟩
        intro x
        have hbase : density A - eps ≤ density (fiber A p) - eps := by
          linarith
        rw [BlockHole.section_later]
        exact hbase.trans (hh x)

/-- Uniform sections, in a dimension chosen solely from the block type and
the error. -/
theorem exists_tower_uniform_sections
    {X Y : Type u} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (hX : 1 < Fintype.card X) (eps : ℝ) (heps : 0 < eps) :
    ∃ b : ℕ, ∀ A : Finset (Tower X Y b),
      ∃ h : BlockHole X Y b, ∀ x : X,
        density A - eps ≤ density (h.holeSection A x) := by
  let rho : ℝ := eps / ((Fintype.card X : ℝ) - 1)
  have hden : 0 < (Fintype.card X : ℝ) - 1 := by
    have : (1 : ℝ) < Fintype.card X := by exact_mod_cast hX
    linarith
  have hrho : 0 < rho := div_pos heps hden
  obtain ⟨b, hb⟩ : ∃ b : ℕ, rho⁻¹ < b := exists_nat_gt rho⁻¹
  refine ⟨b, ?_⟩
  intro A
  apply tower_uniform_sections_aux hrho
  · dsimp [rho]
    field_simp
    norm_num
  · have hbrho : 1 < (b : ℝ) * rho := by
      have := mul_lt_mul_of_pos_right hb hrho
      have hinv : rho⁻¹ * rho = 1 := inv_mul_cancel₀ hrho.ne'
      linarith
    have hnonneg := density_nonneg A
    linarith

/-! ## Turning a tower hole into an ordinary combinatorial subspace -/

/-- The coordinate type of `b` successive blocks of length `m`. -/
def BlockIndex (m : ℕ) : ℕ → Type
  | 0 => Fin 0
  | b + 1 => Fin m ⊕ BlockIndex m b

noncomputable instance blockIndexFintype (m : ℕ) :
    (b : ℕ) → Fintype (BlockIndex m b)
  | 0 => inferInstanceAs (Fintype (Fin 0))
  | b + 1 => by
      letI := blockIndexFintype m b
      exact inferInstanceAs (Fintype (Fin m ⊕ BlockIndex m b))

/-- Flatten a tower of word-blocks to a word on `BlockIndex`. -/
def towerWord {q m : ℕ} :
    (b : ℕ) → Tower (Word q m) PUnit b → BlockIndex m b → Fin q
  | 0, _, i => Fin.elim0 i
  | _ + 1, (x, _), Sum.inl i => x i
  | b + 1, (_, z), Sum.inr i => towerWord b z i

/-- Unflatten a word on `BlockIndex` into a tower of word-blocks. -/
def wordTower {q m : ℕ} :
    (b : ℕ) → (BlockIndex m b → Fin q) → Tower (Word q m) PUnit b
  | 0, _ => PUnit.unit
  | b + 1, x => (fun i ↦ x (Sum.inl i), wordTower b fun i ↦ x (Sum.inr i))

@[simp] theorem wordTower_towerWord {q m : ℕ} :
    ∀ (b : ℕ) (z : Tower (Word q m) PUnit b),
      wordTower b (towerWord b z) = z := by
  intro b
  induction b with
  | zero => intro z; cases z; rfl
  | succ b ih =>
      rintro ⟨x, z⟩
      change (x, wordTower b (towerWord b z)) = (x, z)
      rw [ih]

@[simp] theorem towerWord_wordTower {q m : ℕ} :
    ∀ (b : ℕ) (x : BlockIndex m b → Fin q),
      towerWord b (wordTower b x) = x := by
  intro b
  induction b with
  | zero =>
      intro x
      funext i
      exact Fin.elim0 i
  | succ b ih =>
      intro x
      funext i
      cases i with
      | inl j =>
          change (fun i ↦ x (Sum.inl i)) j = x (Sum.inl j)
          rfl
      | inr j =>
          change towerWord b (wordTower b (fun i ↦ x (Sum.inr i))) j = x (Sum.inr j)
          rw [ih]

/-- Towers of `m`-letter blocks are equivalent to words on their flattened
coordinate type. -/
def towerWordEquiv (q m b : ℕ) :
    Tower (Word q m) PUnit b ≃ (BlockIndex m b → Fin q) where
  toFun := towerWord b
  invFun := wordTower b
  left_inv := wordTower_towerWord b
  right_inv := towerWord_wordTower b

/-- Reindex the flattened coordinate type by `Fin`. -/
noncomputable def towerFinEquiv (q m b : ℕ) :
    Tower (Word q m) PUnit b ≃ Word q (Fintype.card (BlockIndex m b)) :=
  (towerWordEquiv q m b).trans
    ((Fintype.equivFin (BlockIndex m b)).arrowCongr (Equiv.refl (Fin q)))

namespace BlockHole

/-- The subspace obtained by fixing a hole's frozen prefix and remaining tail,
while retaining the distinguished word-block as its parameter cube. -/
def subspace {q m : ℕ} :
    {b : ℕ} → (h : BlockHole (Word q m) PUnit b) → h.Tail →
      Subspace (Fin m) (Fin q) (BlockIndex m b)
  | _, .here b, z =>
      { idxFun := fun
          | Sum.inl i => Sum.inr i
          | Sum.inr j => Sum.inl (towerWord b z j)
        proper := fun e ↦ ⟨Sum.inl e, rfl⟩ }
  | _, .later p h, z =>
      { idxFun := fun
          | Sum.inl i => Sum.inl (p i)
          | Sum.inr j => (h.subspace z).idxFun j
        proper := by
          intro e
          obtain ⟨j, hj⟩ := (h.subspace z).proper e
          exact ⟨Sum.inr j, hj⟩ }

@[simp] theorem subspace_apply {q m : ℕ} :
    ∀ {b : ℕ} (h : BlockHole (Word q m) PUnit b) (z : h.Tail)
      (x : Word q m),
      h.subspace z x = towerWord b (h.fill x z) := by
  intro b h
  induction h with
  | here b =>
      intro z x
      funext i
      cases i <;> rfl
  | later p h ih =>
      intro z x
      funext i
      cases i with
      | inl j => rfl
      | inr j =>
          change h.subspace z x j = towerWord _ (h.fill x z) j
          exact congrFun (ih z x) j

end BlockHole

/-- Extend the fixed letters of a binary subspace to the ternary alphabet.
Its variable blocks remain variable, now over all three letters. -/
def extendBinarySubspace {d m : ℕ}
    (U : Subspace (Fin d) (Fin 2) (Fin m)) :
    Subspace (Fin d) (Fin 3) (Fin m) where
  idxFun i := (U.idxFun i).map Fin.castSucc id
  proper e := by
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨i, by simp [hi]⟩

@[simp] theorem extendBinarySubspace_apply_restrictWord {d m : ℕ}
    (U : Subspace (Fin d) (Fin 2) (Fin m)) (x : Word 2 d) :
    extendBinarySubspace U (Erdos171.restrictWord x) =
      Erdos171.restrictWord (U x) := by
  funext i
  cases hi : U.idxFun i with
  | inl a =>
      simp [extendBinarySubspace, Erdos171.restrictWord,
        Subspace.coe_apply, hi]
  | inr e =>
      simp [extendBinarySubspace, Erdos171.restrictWord,
        Subspace.coe_apply, hi]

/-- Append a fixed coordinate block to a subspace. -/
def appendFixedTailSubspace {q d M r : ℕ}
    (U : Subspace (Fin d) (Fin q) (Fin M)) (y : Word q r) :
    Subspace (Fin d) (Fin q) (Fin (M + r)) where
  idxFun i := match finSumFinEquiv.symm i with
    | Sum.inl j => U.idxFun j
    | Sum.inr j => Sum.inl (y j)
  proper e := by
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨Fin.castAdd r i, by simp [hi]⟩

@[simp] theorem wordSplitEquiv_appendFixedTailSubspace_apply
    {q d M r : ℕ} (U : Subspace (Fin d) (Fin q) (Fin M))
    (y : Word q r) (x : Word q d) :
    wordSplitEquiv q M r (appendFixedTailSubspace U y x) = (U x, y) := by
  apply Prod.ext
  · funext i
    simp [appendFixedTailSubspace, wordSplitEquiv,
      Subspace.coe_apply]
  · funext i
    simp [appendFixedTailSubspace, wordSplitEquiv,
      Subspace.coe_apply]

/-! ## The restricted-subspace corollary -/

/-- Incidences between embedded binary points in the distinguished block and
the common tails of their sections. -/
noncomputable def binaryHoleIncidence {M b : ℕ}
    (A : Finset (Tower (Word 3 M) PUnit b))
    (h : BlockHole (Word 3 M) PUnit b) :
    Finset (Word 2 M × h.Tail) := by
  classical
  letI := h.tailFintype
  exact Finset.univ.filter fun p ↦
    h.fill (Erdos171.restrictWord p.1) p.2 ∈ A

@[simp] theorem mem_binaryHoleIncidence {M b : ℕ}
    (A : Finset (Tower (Word 3 M) PUnit b))
    (h : BlockHole (Word 3 M) PUnit b) (x : Word 2 M) (z : h.Tail) :
    (x, z) ∈ binaryHoleIncidence A h ↔
      h.fill (Erdos171.restrictWord x) z ∈ A := by
  classical
  letI := h.tailFintype
  simp [binaryHoleIncidence]

@[simp] theorem fiber_binaryHoleIncidence {M b : ℕ}
    (A : Finset (Tower (Word 3 M) PUnit b))
    (h : BlockHole (Word 3 M) PUnit b) (x : Word 2 M) :
    fiber (binaryHoleIncidence A h) x =
      h.holeSection A (Erdos171.restrictWord x) := by
  classical
  letI := h.tailFintype
  ext z
  simp

/-- Transpose a finite binary relation. -/
noncomputable def transposeFinset {X Y : Type*}
    (A : Finset (X × Y)) : Finset (Y × X) := by
  classical
  exact A.map (Equiv.prodComm X Y).toEmbedding

@[simp] theorem mem_transposeFinset {X Y : Type*}
    (A : Finset (X × Y)) (y : Y) (x : X) :
    (y, x) ∈ transposeFinset A ↔ (x, y) ∈ A := by
  classical
  simp [transposeFinset]

@[simp] theorem density_transposeFinset {X Y : Type*}
    [Fintype X] [Fintype Y] (A : Finset (X × Y)) :
    density (transposeFinset A) = density A := by
  simpa [transposeFinset] using density_map_equiv (Equiv.prodComm X Y) A

/-- Evaluation of a reindexed hole subspace agrees with the tower-to-`Fin`
equivalence. -/
theorem reindex_hole_comp_apply {q m d b : ℕ}
    (h : BlockHole (Word q m) PUnit b) (z : h.Tail)
    (V : Subspace (Fin d) (Fin q) (Fin m)) (x : Word q d) :
    ((h.subspace z).comp V).reindex (Equiv.refl _) (Equiv.refl _)
        (Fintype.equivFin (BlockIndex m b)) x =
      towerFinEquiv q m b (h.fill (V x) z) := by
  funext i
  simp only [Subspace.reindex_apply, Equiv.refl_apply, Equiv.refl_symm,
    Function.comp_apply, Subspace.comp_apply, BlockHole.subspace_apply]
  rfl

/-- A dense ternary cube contains a ternary subspace all of whose binary
parameter points lie in the dense set.  This is Corollary 5 of the specialized
DKT argument. -/
theorem restricted_binary_subspace (m : ℕ) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ N : ℕ, ∀ A : Finset (Word 3 N), delta ≤ density A →
      ∃ U : Subspace (Fin m) (Fin 3) (Fin N), RestrictedPartContained U A := by
  obtain ⟨M, hM⟩ := binary_multidimensional m (delta / 2) (by linarith)
  let K := M + 1
  have hKpos : 0 < K := by simp [K]
  have hblock : 1 < Fintype.card (Word 3 K) := by
    rw [Erdos171.card_word]
    exact Nat.one_lt_pow hKpos.ne' (by norm_num)
  obtain ⟨b, hb⟩ := exists_tower_uniform_sections
    (X := Word 3 K) (Y := PUnit) hblock (delta / 2) (by linarith)
  let N := Fintype.card (BlockIndex K b)
  let e : Tower (Word 3 K) PUnit b ≃ Word 3 N := towerFinEquiv 3 K b
  refine ⟨N, ?_⟩
  intro A hA
  classical
  let AT : Finset (Tower (Word 3 K) PUnit b) := A.map e.symm.toEmbedding
  have hAT : density AT = density A := by
    simpa [AT] using density_map_equiv e.symm A
  obtain ⟨h, hh⟩ := hb AT
  letI := h.tailFintype
  letI := h.tailNonempty
  let R := binaryHoleIncidence AT h
  have hsections : ∀ x : Word 2 K,
      delta / 2 ≤ density (fiber R x) := by
    intro x
    rw [show fiber R x = h.holeSection AT (Erdos171.restrictWord x) by
      simp [R]]
    have := hh (Erdos171.restrictWord x)
    rw [hAT] at this
    linarith
  have hR : delta / 2 ≤ density R := by
    rw [density_eq_average_fiber]
    exact const_le_average hsections
  let RT := transposeFinset R
  have hRT : delta / 2 ≤ density RT :=
    hR.trans_eq (density_transposeFinset R).symm
  obtain ⟨z, hz⟩ := exists_fiber_density_ge RT
  let Cfull : Finset (Word 2 K) := fiber RT z
  have hCfull : delta / 2 ≤ density Cfull := hRT.trans hz
  have hKeq : K = M + 1 := rfl
  let Csplit : Finset (Word 2 M × Word 2 1) := by
    rw [hKeq] at Cfull
    exact splitFinset Cfull
  have hCsplit : density Csplit = density Cfull := by
    simpa [Csplit, K] using
      (density_map_equiv (wordSplitEquiv 2 M 1) Cfull)
  let Cswap := transposeFinset Csplit
  have hCswap : delta / 2 ≤ density Cswap := by
    rw [density_transposeFinset, hCsplit]
    exact hCfull
  obtain ⟨y, hy⟩ := exists_fiber_density_ge Cswap
  let C : Finset (Word 2 M) := fiber Cswap y
  have hC : delta / 2 ≤ density C := hCswap.trans hy
  obtain ⟨U₂, hU₂⟩ := hM C hC
  let UK : Subspace (Fin m) (Fin 2) (Fin K) :=
    appendFixedTailSubspace U₂ y
  let V : Subspace (Fin m) (Fin 3) (Fin K) := extendBinarySubspace UK
  let W : Subspace (Fin m) (Fin 3) (Fin N) :=
    ((h.subspace z).comp V).reindex (Equiv.refl _) (Equiv.refl _)
      (Fintype.equivFin (BlockIndex K b))
  refine ⟨W, ?_⟩
  intro x
  have hxC : U₂ x ∈ C := hU₂ x
  have hxCswap : (y, U₂ x) ∈ Cswap := (mem_fiber Cswap y (U₂ x)).1 hxC
  have hxCsplit : (U₂ x, y) ∈ Csplit := by
    simpa [Cswap] using hxCswap
  have hxCfull : UK x ∈ Cfull := by
    have hmem : (wordSplitEquiv 2 M 1).symm (U₂ x, y) ∈ Cfull := by
      simpa [Csplit] using hxCsplit
    have hUKsplit : wordSplitEquiv 2 M 1 (UK x) = (U₂ x, y) := by
      simpa only [UK] using
        wordSplitEquiv_appendFixedTailSubspace_apply U₂ y x
    rw [← hUKsplit] at hmem
    simpa using hmem
  have hxR : (UK x, z) ∈ R := by
    have hxRT : (z, UK x) ∈ RT := (mem_fiber RT z (UK x)).1 hxCfull
    simpa [RT] using hxRT
  have hxAT : h.fill (Erdos171.restrictWord (UK x)) z ∈ AT := by
    simpa [R] using hxR
  have hxe : e (h.fill (Erdos171.restrictWord (UK x)) z) ∈ A := by
    simpa [AT] using hxAT
  have hW : W (Erdos171.restrictWord x) =
      e (h.fill (Erdos171.restrictWord (UK x)) z) := by
    rw [show W (Erdos171.restrictWord x) =
        towerFinEquiv 3 K b (h.fill (V (Erdos171.restrictWord x)) z) by
      exact reindex_hole_comp_apply h z V (Erdos171.restrictWord x)]
    simp [V]
    rfl
  rw [hW]
  exact hxe

end DHJ

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/Density.lean` -/

section
/-!
# Uniform density on finite types

This file collects the elementary finite-probability identities used in the
formalization of the density Hales--Jewett theorem.  The definitions take values in
`ℝ`; this is convenient for the density-increment estimates, while the proofs reduce
to exact finite sums.
-/

open scoped BigOperators

namespace Erdos171

section Density

variable {α β : Type*}

/-- The uniform average of a real-valued function on a finite type. -/
noncomputable def average [Fintype α] (f : α → ℝ) : ℝ :=
  𝔼 x, f x

/-- The density of a finset in its ambient finite type, as a real number. -/
noncomputable def density [Fintype α] (A : Finset α) : ℝ :=
  (A.card : ℝ) / Fintype.card α

@[simp]
theorem average_eq_sum_div_card [Fintype α] (f : α → ℝ) :
    average f = (∑ x, f x) / Fintype.card α := by
  simp [average, Fintype.expect_eq_sum_div_card]

@[simp]
theorem density_eq_card_div_card [Fintype α] (A : Finset α) :
    density A = (A.card : ℝ) / Fintype.card α := by
  rfl

theorem density_eq_coe_dens [Fintype α] (A : Finset α) :
    density A = (A.dens : ℝ) := by
  rw [density_eq_card_div_card, Finset.nnratCast_dens]

@[simp]
theorem density_empty [Fintype α] : density (∅ : Finset α) = 0 := by
  simp [density]

@[simp]
theorem density_univ [Fintype α] [Nonempty α] :
    density (Finset.univ : Finset α) = 1 := by
  simp [density]

theorem density_nonneg [Fintype α] (A : Finset α) : 0 ≤ density A := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem density_le_one [Fintype α] (A : Finset α) : density A ≤ 1 := by
  cases isEmpty_or_nonempty α with
  | inl h =>
      letI := h
      have hA : A = ∅ := by
        ext x
        exact isEmptyElim x
      simp [hA]
  | inr h =>
      letI := h
      rw [density, div_le_one (by positivity)]
      exact_mod_cast Finset.card_le_univ A

theorem density_mono [Fintype α] {A B : Finset α} (h : A ⊆ B) :
    density A ≤ density B := by
  unfold density
  gcongr

@[simp]
theorem density_eq_zero [Fintype α] (A : Finset α) :
    density A = 0 ↔ A = ∅ := by
  cases isEmpty_or_nonempty α with
  | inl h =>
      letI := h
      have hA : A = ∅ := by
        ext x
        exact isEmptyElim x
      simp [hA]
  | inr h =>
      letI := h
      simp [density]

@[simp]
theorem density_pos [Fintype α] (A : Finset α) :
    0 < density A ↔ A.Nonempty := by
  constructor
  · intro h
    rw [Finset.nonempty_iff_ne_empty]
    intro hA
    simpa [hA] using h
  · intro h
    rw [lt_iff_le_and_ne]
    refine ⟨density_nonneg A, ?_⟩
    intro hd
    exact h.ne_empty ((density_eq_zero A).1 hd.symm)

theorem average_const [Fintype α] [Nonempty α] (c : ℝ) :
    average (fun _ : α ↦ c) = c := by
  simp [average, Fintype.expect_const]

theorem average_add [Fintype α] (f g : α → ℝ) :
    average (fun x ↦ f x + g x) = average f + average g := by
  simp [average, Finset.expect_add_distrib]

theorem average_sub [Fintype α] (f g : α → ℝ) :
    average (fun x ↦ f x - g x) = average f - average g := by
  simp [average, Finset.expect_sub_distrib]

theorem average_mul_const [Fintype α] (f : α → ℝ) (c : ℝ) :
    average (fun x ↦ f x * c) = average f * c := by
  simp [average, Finset.expect_mul]

/-- The average of a function over a specified finite subset. -/
noncomputable def averageOn (A : Finset α) (f : α → ℝ) : ℝ :=
  𝔼 x ∈ A, f x

@[simp]
theorem averageOn_eq_sum_div_card (A : Finset α) (f : α → ℝ) :
    averageOn A f = (∑ x ∈ A, f x) / A.card := by
  simp [averageOn, Finset.expect_eq_sum_div_card]

theorem average_mono [Fintype α] {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    average f ≤ average g := by
  simp only [average_eq_sum_div_card]
  gcongr with x
  exact h x

theorem average_le_const [Fintype α] [Nonempty α] {f : α → ℝ} {c : ℝ}
    (h : ∀ x, f x ≤ c) : average f ≤ c := by
  simpa [average_const] using average_mono (f := f) (g := fun _ ↦ c) h

theorem const_le_average [Fintype α] [Nonempty α] {f : α → ℝ} {c : ℝ}
    (h : ∀ x, c ≤ f x) : c ≤ average f := by
  simpa [average_const] using average_mono (f := fun _ ↦ c) (g := f) h

/-- Some value of a function is at least its uniform average. -/
theorem exists_average_le [Fintype α] [Nonempty α] (f : α → ℝ) :
    ∃ x, average f ≤ f x := by
  by_contra! h
  have hsum : (∑ x, f x) < ∑ _x : α, average f :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun x _ ↦ h x)
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by positivity
  rw [average_eq_sum_div_card, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hcancel : (Fintype.card α : ℝ) *
      ((∑ x, f x) / Fintype.card α) = ∑ x, f x := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hcard
  rw [hcancel] at hsum
  exact hsum.false

/-- A fibre of a subset of a product, with the first coordinate fixed. -/
noncomputable def fiber [Fintype β] (A : Finset (α × β)) (a : α) : Finset β :=
  by
    classical
    exact Finset.univ.filter fun b ↦ (a, b) ∈ A

@[simp]
theorem mem_fiber [Fintype β] (A : Finset (α × β)) (a : α) (b : β) :
    b ∈ fiber A a ↔ (a, b) ∈ A := by
  classical
  simp [fiber]

/-- Exact fibrewise counting for a subset of a product. -/
theorem card_eq_sum_card_fiber [Fintype α] [Fintype β] (A : Finset (α × β)) :
    A.card = ∑ a, (fiber A a).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (s := A) (t := Finset.univ) (f := Prod.fst) (by simp)]
  apply Finset.sum_congr rfl
  intro a _
  refine Finset.card_bij (fun p _ ↦ p.2) ?_ ?_ ?_
  · intro p hp
    have hp' := Finset.mem_filter.1 hp
    apply (mem_fiber A a p.2).2
    rw [← hp'.2]
    simpa using hp'.1
  · intro p hp q hq hpq
    apply Prod.ext
    · have hp' := (Finset.mem_filter.1 hp).2
      have hq' := (Finset.mem_filter.1 hq).2
      simpa [hp', hq']
    · exact hpq
  · intro b hb
    refine ⟨(a, b), ?_, rfl⟩
    have hb' : (a, b) ∈ A := (mem_fiber A a b).1 hb
    simp [hb']

/-- Uniform density on a product is the average of the densities of its fibres. -/
theorem density_eq_average_fiber [Fintype α] [Fintype β]
    (A : Finset (α × β)) :
    density A = average fun a ↦ density (fiber A a) := by
  cases isEmpty_or_nonempty α with
  | inl hα =>
      letI := hα
      simp [density_eq_card_div_card, average_eq_sum_div_card]
  | inr hα =>
      letI := hα
      cases isEmpty_or_nonempty β with
      | inl hβ =>
          letI := hβ
          simp [density_eq_card_div_card, average_eq_sum_div_card]
      | inr hβ =>
          letI := hβ
          rw [density_eq_card_div_card, average_eq_sum_div_card]
          rw [card_eq_sum_card_fiber]
          simp only [density_eq_card_div_card]
          rw [Fintype.card_prod]
          push_cast
          rw [← Finset.sum_div]
          have ha : (Fintype.card α : ℝ) ≠ 0 := by positivity
          have hb : (Fintype.card β : ℝ) ≠ 0 := by positivity
          field_simp

/-- The indicator of a finset has average equal to its density. -/
theorem average_indicator [Fintype α] [DecidableEq α] (A : Finset α) :
    average (fun x ↦ if x ∈ A then (1 : ℝ) else 0) = density A := by
  classical
  simp [average_eq_sum_div_card, density_eq_card_div_card,
    Finset.sum_boole]

/-- The exact uniform average of a two-valued function. -/
theorem average_piecewise_const [Fintype α] [Nonempty α] [DecidableEq α]
    (A : Finset α) (a b : ℝ) :
    average (fun x ↦ if x ∈ A then a else b) =
      density A * a + (1 - density A) * b := by
  let ι : α → ℝ := fun x ↦ if x ∈ A then 1 else 0
  have hpoint : (fun x ↦ if x ∈ A then a else b) =
      fun x ↦ ι x * a + (1 - ι x) * b := by
    funext x
    simp only [ι]
    split <;> ring
  rw [hpoint, average_add, average_mul_const, average_mul_const,
    average_sub, average_const, average_indicator]

/-- A pointwise upper bound on and off a set gives the corresponding upper bound
for the uniform average. -/
theorem average_le_density_mul_add [Fintype α] [Nonempty α] [DecidableEq α]
    (A : Finset α) (f : α → ℝ) (a b : ℝ)
    (hA : ∀ x ∈ A, f x ≤ a) (hAc : ∀ x ∉ A, f x ≤ b) :
    average f ≤ density A * a + (1 - density A) * b := by
  rw [← average_piecewise_const A a b]
  apply average_mono
  intro x
  by_cases hx : x ∈ A
  · simpa [hx] using hA x hx
  · simpa [hx] using hAc x hx

/-- The set on which a real-valued function is at least a given threshold. -/
noncomputable def superlevel [Fintype α] (f : α → ℝ) (c : ℝ) : Finset α := by
  classical
  exact Finset.univ.filter fun x ↦ c ≤ f x

@[simp]
theorem mem_superlevel [Fintype α] (f : α → ℝ) (c : ℝ) (x : α) :
    x ∈ superlevel f c ↔ c ≤ f x := by
  classical
  simp [superlevel]

/-- Quantitative averaging: if `f ≤ B` and its average is at least `μ`, then
the density of the set where `f ≥ c` is at least `(μ-c)/(B-c)`. -/
theorem density_superlevel_ge [Fintype α] [Nonempty α] [DecidableEq α]
    (f : α → ℝ) {μ c B : ℝ} (havg : μ ≤ average f)
    (hub : ∀ x, f x ≤ B) (hcB : c < B) :
    (μ - c) / (B - c) ≤ density (superlevel f c) := by
  have havg' : average f ≤ density (superlevel f c) * B +
      (1 - density (superlevel f c)) * c := by
    apply average_le_density_mul_add
    · intro x _
      exact hub x
    · intro x hx
      exact le_of_lt (not_le.1 (by simpa using hx))
  rw [div_le_iff₀ (sub_pos.2 hcB)]
  nlinarith

/-- The particularly useful half-threshold form of quantitative averaging. -/
theorem half_le_density_superlevel [Fintype α] [Nonempty α] [DecidableEq α]
    (f : α → ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ) (havg : δ ≤ average f)
    (hub : ∀ x, f x ≤ 1) :
    δ / 2 ≤ density (superlevel f (δ / 2)) := by
  have havg' : average f ≤ density (superlevel f (δ / 2)) +
      (1 - density (superlevel f (δ / 2))) * (δ / 2) := by
    convert average_le_density_mul_add (superlevel f (δ / 2)) f 1 (δ / 2)
      (fun x _ ↦ hub x) (fun x hx ↦ le_of_lt (not_le.1 (by simpa using hx))) using 1 <;> ring
  have hdle : density (superlevel f (δ / 2)) ≤ 1 := density_le_one _
  have hd0 : 0 ≤ density (superlevel f (δ / 2)) := density_nonneg _
  have hδle : δ ≤ 1 := havg.trans (average_le_const hub)
  nlinarith

/-- Turn a set into the finset of all its elements in a finite ambient type. -/
noncomputable def setFinset [Fintype α] (A : Set α) : Finset α := by
  classical
  exact Finset.univ.filter fun x ↦ x ∈ A

@[simp]
theorem mem_setFinset [Fintype α] (A : Set α) (x : α) :
    x ∈ setFinset A ↔ x ∈ A := by
  classical
  simp [setFinset]

/-- Uniform density of a set in a finite ambient type. -/
noncomputable def setDensity [Fintype α] (A : Set α) : ℝ :=
  density (setFinset A)

@[simp]
theorem setDensity_empty [Fintype α] : setDensity (∅ : Set α) = 0 := by
  classical
  simp [setDensity, setFinset]

@[simp]
theorem setDensity_univ [Fintype α] [Nonempty α] :
    setDensity (Set.univ : Set α) = 1 := by
  classical
  simp [setDensity, setFinset]

/-- A fibre of a set in a product. -/
def setFiber (A : Set (α × β)) (a : α) : Set β :=
  {b | (a, b) ∈ A}

@[simp]
theorem mem_setFiber (A : Set (α × β)) (a : α) (b : β) :
    b ∈ setFiber A a ↔ (a, b) ∈ A := Iff.rfl

/-- Density is preserved by equivalences of finite ambient types. -/
theorem density_map_equiv [Fintype α] [Fintype β] (e : α ≃ β) (A : Finset α) :
    density (A.map e.toEmbedding) = density A := by
  simp [density, Fintype.card_congr e]

/-- The density of a Cartesian product is the product of the two densities. -/
theorem density_product [Fintype α] [Fintype β] (A : Finset α) (B : Finset β) :
    density (A ×ˢ B) = density A * density B := by
  simp [density_eq_card_div_card, Finset.card_product, Fintype.card_prod]
  ring

/-! ## Incidence Fubini identities -/

/-- The column of a finset of pairs at a fixed second coordinate. -/
noncomputable def columnFiber [Fintype α] (A : Finset (α × β)) (b : β) : Finset α := by
  classical
  exact Finset.univ.filter fun a ↦ (a, b) ∈ A

@[simp]
theorem mem_columnFiber [Fintype α] (A : Finset (α × β)) (a : α) (b : β) :
    a ∈ columnFiber A b ↔ (a, b) ∈ A := by
  classical
  simp [columnFiber]

/-- The row set of a binary relation. -/
def relationRow (R : α → β → Prop) (a : α) : Set β :=
  {b | R a b}

/-- The column set of a binary relation. -/
def relationColumn (R : α → β → Prop) (b : β) : Set α :=
  {a | R a b}

@[simp]
theorem mem_relationRow (R : α → β → Prop) (a : α) (b : β) :
    b ∈ relationRow R a ↔ R a b := Iff.rfl

@[simp]
theorem mem_relationColumn (R : α → β → Prop) (a : α) (b : β) :
    a ∈ relationColumn R b ↔ R a b := Iff.rfl

section Lattice

variable [Fintype α] [DecidableEq α]

theorem density_union_add_density_inter (A B : Finset α) :
    density (A ∪ B) + density (A ∩ B) = density A + density B := by
  simp only [density_eq_coe_dens]
  exact_mod_cast Finset.dens_union_add_dens_inter A B

theorem density_sdiff_add_density_inter (A B : Finset α) :
    density (A \ B) + density (A ∩ B) = density A := by
  simp only [density_eq_coe_dens]
  exact_mod_cast Finset.dens_sdiff_add_dens_inter A B

theorem density_union_le_add (A B : Finset α) :
    density (A ∪ B) ≤ density A + density B := by
  have h := density_union_add_density_inter A B
  have hi := density_nonneg (A ∩ B)
  linarith

end Lattice

end Density

end Erdos171

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/Tiling.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Finite tilings by combinatorial subspaces

This file contains the bookkeeping common to the insensitive-set tiling
argument.  A tile is represented by the finite range of a proper Mathlib
`Combinatorics.Subspace`; a tiling is a finite, pairwise-disjoint family of
such ranges.  The density lemmas below are deliberately stated for arbitrary
finite families, so that the final intersection argument can sum a relative
error estimate over all of its large tiles.
-/

open scoped BigOperators

namespace Erdos171

open Combinatorics

@[simp] theorem mem_finsetMap_equiv {A B : Type*} [DecidableEq A]
    [DecidableEq B] (e : A ≃ B) (D : Finset A) (x : B) :
    x ∈ D.map e.toEmbedding ↔ e.symm x ∈ D := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    simpa using hy
  · intro hx
    exact Finset.mem_map.mpr ⟨e.symm x, hx, by simp⟩

section SubspacePoints

variable {eta alpha iota : Type*}

/-- The finite set of points parametrized by a combinatorial subspace. -/
noncomputable def subspacePoints [Fintype (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota) :
    Finset (iota → alpha) :=
  Finset.univ.image U

@[simp] theorem mem_subspacePoints [Fintype (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (x : iota → alpha) :
    x ∈ subspacePoints U ↔ x ∈ Set.range U := by
  simp [subspacePoints]

@[simp] theorem card_subspacePoints [Fintype (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota) :
    (subspacePoints U).card = Fintype.card (eta → alpha) := by
  rw [subspacePoints, Finset.card_image_of_injective _ U.parameter_injective,
    Finset.card_univ]

@[simp] theorem card_subspacePoints_fin {m q : ℕ}
    [DecidableEq (iota → Fin q)] (U : Subspace (Fin m) (Fin q) iota) :
    (subspacePoints U).card = q ^ m := by
  rw [card_subspacePoints, Fintype.card_fun]
  simp

end SubspacePoints

section Pullback

variable {eta zeta alpha iota : Type*}

/-- Pull a finite set in the ambient cube back to the parameter cube of a
subspace.  Its density is the usual relative density inside that subspace. -/
noncomputable def subspacePullback [Fintype (eta → alpha)]
    (U : Subspace eta alpha iota) (D : Finset (iota → alpha)) :
    Finset (eta → alpha) := by
  classical
  exact Finset.univ.filter fun x ↦ U x ∈ D

@[simp] theorem mem_subspacePullback [Fintype (eta → alpha)]
    (U : Subspace eta alpha iota) (D : Finset (iota → alpha))
    (x : eta → alpha) :
    x ∈ subspacePullback U D ↔ U x ∈ D := by
  classical
  simp [subspacePullback]

theorem image_subspacePullback [Fintype (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (D : Finset (iota → alpha)) :
    (subspacePullback U D).image U = subspacePoints U ∩ D := by
  classical
  ext x
  constructor
  · simp only [Finset.mem_image, mem_subspacePullback, Finset.mem_inter,
      mem_subspacePoints]
    rintro ⟨y, hyD, rfl⟩
    exact ⟨⟨y, rfl⟩, hyD⟩
  · simp only [Finset.mem_inter, mem_subspacePoints, Finset.mem_image,
      mem_subspacePullback]
    rintro ⟨⟨y, rfl⟩, hyD⟩
    exact ⟨y, hyD, rfl⟩

theorem card_inter_subspacePoints [Fintype (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (D : Finset (iota → alpha)) :
    (subspacePoints U ∩ D).card = (subspacePullback U D).card := by
  rw [← image_subspacePullback U D,
    Finset.card_image_of_injective _ U.parameter_injective]

/-- Ambient density factors as the density of the large tile times relative
density in its parameter cube. -/
theorem density_inter_subspacePoints [Fintype (eta → alpha)]
    [Nonempty (eta → alpha)] [Fintype (iota → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (D : Finset (iota → alpha)) :
    density (subspacePoints U ∩ D) =
      density (subspacePoints U) * density (subspacePullback U D) := by
  simp only [density_eq_card_div_card, card_inter_subspacePoints]
  rw [card_subspacePoints]
  have heta : (Fintype.card (eta → alpha) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Density scaling for an arbitrary finite subset of a subspace's parameter
cube. -/
theorem density_image_subspace [Fintype (eta → alpha)]
    [Nonempty (eta → alpha)] [Fintype (iota → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (B : Finset (eta → alpha)) :
    density (B.image U) = density (subspacePoints U) * density B := by
  simp only [density_eq_card_div_card,
    Finset.card_image_of_injective _ U.parameter_injective, card_subspacePoints]
  have heta : (Fintype.card (eta → alpha) : ℝ) ≠ 0 := by positivity
  field_simp

theorem subspacePoints_comp [Fintype (zeta → alpha)]
    [Fintype (eta → alpha)] [DecidableEq (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (V : Subspace zeta alpha eta) :
    subspacePoints (U.comp V) = (subspacePoints V).image U := by
  classical
  ext x
  simp only [mem_subspacePoints, Finset.mem_image, Set.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨V z, ⟨z, rfl⟩, (Subspace.comp_apply U V z).symm⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, Subspace.comp_apply U V z⟩

theorem subspacePoints_comp_subset_iff [Fintype (zeta → alpha)]
    [Fintype (eta → alpha)] [DecidableEq (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (V : Subspace zeta alpha eta) (D : Finset (iota → alpha)) :
    subspacePoints (U.comp V) ⊆ D ↔
      subspacePoints V ⊆ subspacePullback U D := by
  constructor
  · intro h x hx
    rw [mem_subspacePullback]
    rw [mem_subspacePoints] at hx
    obtain ⟨z, rfl⟩ := hx
    apply h
    rw [mem_subspacePoints]
    exact ⟨z, Subspace.comp_apply U V z⟩
  · intro h x hx
    rw [mem_subspacePoints] at hx
    obtain ⟨z, rfl⟩ := hx
    have hz : U (V z) ∈ D := by
      rw [← mem_subspacePullback]
      apply h
      rw [mem_subspacePoints]
      exact ⟨z, rfl⟩
    simpa only [Subspace.comp_apply] using hz

end Pullback

section InsensitivePullback

variable {k m n : ℕ}

/-- Subspaces preserve `(i,last)`-equivalence of parameter words. -/
theorem lastEquivalent_subspace (i : Fin k)
    (U : Subspace (Fin m) (Fin (k + 1)) (Fin n))
    {x y : Word (k + 1) m} (hxy : LastEquivalent i x y) :
    LastEquivalent i (U x) (U y) := by
  rw [LastEquivalent] at hxy ⊢
  funext r
  cases hr : U.idxFun r with
  | inl a => simp [replaceLast, Subspace.coe_apply, hr]
  | inr e =>
      simpa [replaceLast, Subspace.coe_apply, hr] using congrFun hxy e

/-- Pulling an insensitive set back through a combinatorial subspace again
gives an insensitive set in the parameter cube. -/
theorem IsLastInsensitive.subspacePullback (i : Fin k)
    (U : Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (D : Finset (Word (k + 1) n))
    (hD : IsLastInsensitive i (D : Set (Word (k + 1) n))) :
    IsLastInsensitive i (subspacePullback U D : Set (Word (k + 1) m)) := by
  intro x y hxy
  simp only [Finset.mem_coe, mem_subspacePullback]
  exact hD (U x) (U y) (lastEquivalent_subspace i U hxy)

end InsensitivePullback

section Families

variable {eta alpha iota : Type*} [Fintype (eta → alpha)]
  [DecidableEq (iota → alpha)]

/-- A finite pairwise-disjoint family of equal-dimensional combinatorial
subspaces.  Containment in a target set is kept separate, since the same
family is used with several successive remainders in the greedy argument. -/
structure SubspaceTiling (eta alpha iota : Type*)
    [Fintype (eta → alpha)] [DecidableEq (iota → alpha)] where
  tiles : Finset (Subspace eta alpha iota)
  pairwiseDisjoint : (tiles : Set (Subspace eta alpha iota)).PairwiseDisjoint
    subspacePoints

namespace SubspaceTiling

variable {zeta : Type*} [Fintype (zeta → alpha)]
  [DecidableEq (eta → alpha)]

/-- The empty tiling. -/
noncomputable def empty : SubspaceTiling eta alpha iota := by
  classical
  exact ⟨∅, by simp⟩

@[simp] theorem tiles_empty : (empty : SubspaceTiling eta alpha iota).tiles = ∅ := rfl

/-- The union of all points in all tiles. -/
noncomputable def covered (T : SubspaceTiling eta alpha iota) :
    Finset (iota → alpha) :=
  T.tiles.biUnion subspacePoints

@[simp] theorem covered_empty : (empty : SubspaceTiling eta alpha iota).covered = ∅ := by
  classical
  simp [covered, empty]

/-- Join two tilings whose covered point sets are disjoint. -/
noncomputable def disjointUnion (T S : SubspaceTiling eta alpha iota)
    (h : Disjoint T.covered S.covered) :
    SubspaceTiling eta alpha iota := by
  classical
  exact
    { tiles := T.tiles ∪ S.tiles
      pairwiseDisjoint := by
        intro U hU V hV hUV
        change U ∈ T.tiles ∪ S.tiles at hU
        change V ∈ T.tiles ∪ S.tiles at hV
        rw [Finset.mem_union] at hU hV
        rcases hU with hUT | hUS <;> rcases hV with hVT | hVS
        · exact T.pairwiseDisjoint hUT hVT hUV
        · exact h.mono
            (fun x hx ↦ Finset.mem_biUnion.mpr ⟨U, hUT, hx⟩)
            (fun x hx ↦ Finset.mem_biUnion.mpr ⟨V, hVS, hx⟩)
        · exact h.symm.mono
            (fun x hx ↦ Finset.mem_biUnion.mpr ⟨U, hUS, hx⟩)
            (fun x hx ↦ Finset.mem_biUnion.mpr ⟨V, hVT, hx⟩)
        · exact S.pairwiseDisjoint hUS hVS hUV }

theorem covered_disjointUnion (T S : SubspaceTiling eta alpha iota)
    (h : Disjoint T.covered S.covered) :
    (T.disjointUnion S h).covered = T.covered ∪ S.covered := by
  classical
  exact Finset.union_biUnion

@[simp] theorem mem_covered (T : SubspaceTiling eta alpha iota)
    (x : iota → alpha) :
    x ∈ T.covered ↔ ∃ U ∈ T.tiles, x ∈ subspacePoints U := by
  classical
  simp [covered]

theorem tile_subset_covered (T : SubspaceTiling eta alpha iota)
    {U : Subspace eta alpha iota} (hU : U ∈ T.tiles) :
    subspacePoints U ⊆ T.covered := by
  classical
  intro x hx
  exact (T.mem_covered x).2 ⟨U, hU, hx⟩

section AmbientReindex

variable {kappa : Type*} [DecidableEq (kappa → alpha)]

/-- The word equivalence induced by reindexing ambient coordinates. -/
def ambientWordEquiv (e : iota ≃ kappa) :
    (iota → alpha) ≃ (kappa → alpha) :=
  e.arrowCongr (Equiv.refl alpha)

@[simp] theorem mem_map_ambientWordEquiv (e : iota ≃ kappa)
    (D : Finset (iota → alpha)) (x : kappa → alpha) :
    x ∈ D.map (ambientWordEquiv e).toEmbedding ↔
      (ambientWordEquiv e).symm x ∈ D := by
  exact mem_finsetMap_equiv (ambientWordEquiv e) D x

theorem ambientReindex_injective (e : iota ≃ kappa) :
    Function.Injective (fun U : Subspace eta alpha iota ↦
      U.reindex (Equiv.refl eta) (Equiv.refl alpha) e) := by
  intro U V hUV
  apply Subspace.ext
  funext i
  have hi := congrArg
    (fun W : Subspace eta alpha kappa ↦ W.idxFun (e i)) hUV
  simpa [Subspace.reindex] using hi

noncomputable def ambientReindexEmbedding (e : iota ≃ kappa) :
    Subspace eta alpha iota ↪ Subspace eta alpha kappa :=
  ⟨fun U ↦ U.reindex (Equiv.refl eta) (Equiv.refl alpha) e,
    ambientReindex_injective e⟩

theorem subspacePoints_ambientReindex (e : iota ≃ kappa)
    (U : Subspace eta alpha iota) :
    subspacePoints (U.reindex (Equiv.refl eta) (Equiv.refl alpha) e) =
      (subspacePoints U).map (ambientWordEquiv e).toEmbedding := by
  classical
  ext x
  constructor
  · intro hx
    rw [mem_subspacePoints] at hx
    obtain ⟨a, rfl⟩ := hx
    apply Finset.mem_map.mpr
    refine ⟨U a, by simp, ?_⟩
    funext j
    simp [ambientWordEquiv, Function.comp_def]
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    rw [mem_subspacePoints] at hy ⊢
    obtain ⟨a, rfl⟩ := hy
    refine ⟨a, ?_⟩
    funext j
    simp [ambientWordEquiv, Function.comp_def]

/-- Transport every tile through an equivalence of ambient coordinate types. -/
noncomputable def ambientReindex (T : SubspaceTiling eta alpha iota)
    (e : iota ≃ kappa) : SubspaceTiling eta alpha kappa := by
  classical
  exact
    { tiles := T.tiles.map (ambientReindexEmbedding e)
      pairwiseDisjoint := by
        intro U hU V hV hUV
        obtain ⟨U₀, hU₀, rfl⟩ := Finset.mem_map.mp hU
        obtain ⟨V₀, hV₀, rfl⟩ := Finset.mem_map.mp hV
        have hUV₀ : U₀ ≠ V₀ := fun h ↦
          hUV (congrArg (fun W ↦
            W.reindex (Equiv.refl eta) (Equiv.refl alpha) e) h)
        change Disjoint
          (subspacePoints
            (U₀.reindex (Equiv.refl eta) (Equiv.refl alpha) e))
          (subspacePoints
            (V₀.reindex (Equiv.refl eta) (Equiv.refl alpha) e))
        rw [subspacePoints_ambientReindex, subspacePoints_ambientReindex,
          Finset.disjoint_map]
        exact T.pairwiseDisjoint hU₀ hV₀ hUV₀ }

theorem covered_ambientReindex (T : SubspaceTiling eta alpha iota)
    (e : iota ≃ kappa) :
    (T.ambientReindex e).covered =
      T.covered.map (ambientWordEquiv e).toEmbedding := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨U, hU, hxU⟩ := ((T.ambientReindex e).mem_covered x).mp hx
    change U ∈ T.tiles.map (ambientReindexEmbedding e) at hU
    obtain ⟨U₀, hU₀, rfl⟩ := Finset.mem_map.mp hU
    change x ∈ subspacePoints
      (U₀.reindex (Equiv.refl eta) (Equiv.refl alpha) e) at hxU
    rw [subspacePoints_ambientReindex] at hxU
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hxU
    exact Finset.mem_map.mpr ⟨y, T.tile_subset_covered hU₀ hy, rfl⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨U, hU, hyU⟩ := (T.mem_covered y).mp hy
    apply ((T.ambientReindex e).mem_covered _).mpr
    refine ⟨U.reindex (Equiv.refl eta) (Equiv.refl alpha) e, ?_, ?_⟩
    · change U.reindex (Equiv.refl eta) (Equiv.refl alpha) e ∈
        T.tiles.map (ambientReindexEmbedding e)
      exact Finset.mem_map.mpr ⟨U, hU, rfl⟩
    · rw [subspacePoints_ambientReindex]
      exact Finset.mem_map.mpr ⟨y, hyU, rfl⟩

end AmbientReindex

/-- Every tile in `T` is contained in `D`. -/
def IsContainedIn (T : SubspaceTiling eta alpha iota)
    (D : Finset (iota → alpha)) : Prop :=
  ∀ U ∈ T.tiles, subspacePoints U ⊆ D

theorem covered_subset_iff (T : SubspaceTiling eta alpha iota)
    (D : Finset (iota → alpha)) :
    T.covered ⊆ D ↔ T.IsContainedIn D := by
  classical
  constructor
  · intro h U hU
    exact (T.tile_subset_covered hU).trans h
  · intro h x hx
    obtain ⟨U, hU, hxU⟩ := (T.mem_covered x).1 hx
    exact h U hU hxU

section AmbientReindexContainment

variable {kappa : Type*} [DecidableEq (kappa → alpha)]

/-- Containment after an ambient reindex is equivalent to containment in the
pullback of the target finset. -/
theorem ambientReindex_isContainedIn_iff
    (T : SubspaceTiling eta alpha iota) (e : iota ≃ kappa)
    (D : Finset (kappa → alpha)) :
    (T.ambientReindex e).IsContainedIn D ↔
      T.IsContainedIn
        (D.map (ambientWordEquiv e).symm.toEmbedding) := by
  rw [← (T.ambientReindex e).covered_subset_iff D,
    ← T.covered_subset_iff, covered_ambientReindex]
  constructor
  · intro h x hx
    apply Finset.mem_map.mpr
    refine ⟨ambientWordEquiv e x, h ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    · simp
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    have hy' := h hy
    obtain ⟨z, hz, hzy⟩ := Finset.mem_map.mp hy'
    simpa [← hzy] using hz

/-- Exact residual-set transport under an ambient coordinate equivalence. -/
theorem sdiff_covered_ambientReindex
    (T : SubspaceTiling eta alpha iota) (e : iota ≃ kappa)
    (D : Finset (kappa → alpha)) :
    D \ (T.ambientReindex e).covered =
      ((D.map (ambientWordEquiv e).symm.toEmbedding) \ T.covered).map
        (ambientWordEquiv e).toEmbedding := by
  classical
  rw [covered_ambientReindex]
  ext x
  constructor
  · intro hx
    have hx' := Finset.mem_sdiff.mp hx
    apply Finset.mem_map.mpr
    refine ⟨(ambientWordEquiv e).symm x, Finset.mem_sdiff.mpr ⟨?_, ?_⟩, by simp⟩
    · exact Finset.mem_map.mpr ⟨x, hx'.1, by simp⟩
    · intro hcover
      apply hx'.2
      exact Finset.mem_map.mpr
        ⟨(ambientWordEquiv e).symm x, hcover, by simp⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
    have hy' := Finset.mem_sdiff.mp hy
    obtain ⟨z, hzD, hzy⟩ := Finset.mem_map.mp hy'.1
    apply Finset.mem_sdiff.mpr
    constructor
    · have hzx : z = x := by
        rw [← hyx, ← hzy]
        simp
      simpa [hzx] using hzD
    · intro hxcover
      obtain ⟨w, hwcover, hwx⟩ := Finset.mem_map.mp hxcover
      apply hy'.2
      have hwy : w = y := by
        apply (ambientWordEquiv e).injective
        exact hwx.trans hyx.symm
      simpa [hwy] using hwcover

theorem density_sdiff_covered_ambientReindex
    [Fintype (iota → alpha)] [Fintype (kappa → alpha)]
    (T : SubspaceTiling eta alpha iota) (e : iota ≃ kappa)
    (D : Finset (kappa → alpha)) :
    density (D \ (T.ambientReindex e).covered) =
      density (D.map (ambientWordEquiv e).symm.toEmbedding \ T.covered) := by
  rw [sdiff_covered_ambientReindex,
    density_map_equiv (ambientWordEquiv e)]

end AmbientReindexContainment

theorem card_covered (T : SubspaceTiling eta alpha iota) :
    T.covered.card = ∑ U ∈ T.tiles, (subspacePoints U).card := by
  classical
  exact Finset.card_biUnion T.pairwiseDisjoint

theorem comp_left_injective (U : Subspace eta alpha iota) :
    Function.Injective (U.comp : Subspace zeta alpha eta → Subspace zeta alpha iota) := by
  intro V W hVW
  apply Subspace.ext
  funext e
  obtain ⟨i, hi⟩ := U.proper e
  have hcoord := congrArg (fun X : Subspace zeta alpha iota ↦ X.idxFun i) hVW
  simpa [Subspace.comp, hi] using hcoord

noncomputable def compEmbedding (U : Subspace eta alpha iota) :
    Subspace zeta alpha eta ↪ Subspace zeta alpha iota :=
  ⟨U.comp, comp_left_injective U⟩

/-- Map every tile in a parameter cube into an outer combinatorial subspace. -/
noncomputable def comp (T : SubspaceTiling zeta alpha eta)
    (U : Subspace eta alpha iota) : SubspaceTiling zeta alpha iota := by
  classical
  exact
    { tiles := T.tiles.map (compEmbedding U)
      pairwiseDisjoint := by
        intro V hV W hW hne
        obtain ⟨V₀, hV₀, hVeq⟩ := Finset.mem_map.1 hV
        obtain ⟨W₀, hW₀, hWeq⟩ := Finset.mem_map.1 hW
        subst V
        subst W
        have hne₀ : V₀ ≠ W₀ := fun h ↦ hne (congrArg U.comp h)
        change Disjoint (subspacePoints (U.comp V₀)) (subspacePoints (U.comp W₀))
        rw [subspacePoints_comp, subspacePoints_comp,
          Finset.disjoint_image U.parameter_injective]
        exact T.pairwiseDisjoint hV₀ hW₀ hne₀ }

theorem covered_comp (T : SubspaceTiling zeta alpha eta)
    (U : Subspace eta alpha iota) :
    (T.comp U).covered = T.covered.image U := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨V, hV, hxV⟩ := ((T.comp U).mem_covered x).1 hx
    change V ∈ T.tiles.map (compEmbedding U) at hV
    obtain ⟨V₀, hV₀, hVeq⟩ := Finset.mem_map.1 hV
    subst V
    change x ∈ subspacePoints (U.comp V₀) at hxV
    rw [subspacePoints_comp] at hxV
    simp only [Finset.mem_image] at hxV ⊢
    obtain ⟨y, hy, rfl⟩ := hxV
    exact ⟨y, T.tile_subset_covered hV₀ hy, rfl⟩
  · intro hx
    simp only [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨V, hV, hyV⟩ := (T.mem_covered y).1 hy
    apply ((T.comp U).mem_covered (U y)).2
    refine ⟨U.comp V, ?_, ?_⟩
    · change U.comp V ∈ T.tiles.map (compEmbedding U)
      exact Finset.mem_map.2 ⟨V, hV, rfl⟩
    · rw [subspacePoints_comp]
      exact Finset.mem_image_of_mem U hyV

theorem covered_comp_subset_subspacePoints
    (T : SubspaceTiling zeta alpha eta) (U : Subspace eta alpha iota) :
    (T.comp U).covered ⊆ subspacePoints U := by
  rw [covered_comp]
  intro x hx
  simp only [Finset.mem_image] at hx
  obtain ⟨y, _hy, rfl⟩ := hx
  simp

theorem comp_isContainedIn_iff (T : SubspaceTiling zeta alpha eta)
    (U : Subspace eta alpha iota) (D : Finset (iota → alpha)) :
    (T.comp U).IsContainedIn D ↔ T.IsContainedIn (subspacePullback U D) := by
  classical
  constructor
  · intro h V hV
    rw [← subspacePoints_comp_subset_iff U V D]
    apply h (U.comp V)
    change U.comp V ∈ T.tiles.map (compEmbedding U)
    exact Finset.mem_map.2 ⟨V, hV, rfl⟩
  · intro h V hV
    change V ∈ T.tiles.map (compEmbedding U) at hV
    obtain ⟨V₀, hV₀, hVeq⟩ := Finset.mem_map.1 hV
    subst V
    change subspacePoints (U.comp V₀) ⊆ D
    rw [subspacePoints_comp_subset_iff]
    exact h V₀ hV₀

/-- Refine every tile of `T` by an inner tiling in its parameter cube and
flatten all the resulting composed subspaces into one tiling. -/
noncomputable def bind (T : SubspaceTiling eta alpha iota)
    (R : Subspace eta alpha iota → SubspaceTiling zeta alpha eta) :
    SubspaceTiling zeta alpha iota := by
  classical
  exact
    { tiles := T.tiles.biUnion fun U ↦ (R U).comp U |>.tiles
      pairwiseDisjoint := by
        intro A hA B hB hAB
        change A ∈ T.tiles.biUnion (fun U ↦ ((R U).comp U).tiles) at hA
        change B ∈ T.tiles.biUnion (fun U ↦ ((R U).comp U).tiles) at hB
        obtain ⟨U, hU, hAU⟩ := Finset.mem_biUnion.mp hA
        obtain ⟨V, hV, hBV⟩ := Finset.mem_biUnion.mp hB
        by_cases hUV : U = V
        · subst V
          exact ((R U).comp U).pairwiseDisjoint hAU hBV hAB
        · exact (T.pairwiseDisjoint hU hV hUV).mono
            (((R U).comp U).tile_subset_covered hAU |>.trans
              ((R U).covered_comp_subset_subspacePoints U))
            (((R V).comp V).tile_subset_covered hBV |>.trans
              ((R V).covered_comp_subset_subspacePoints V)) }

theorem covered_bind (T : SubspaceTiling eta alpha iota)
    (R : Subspace eta alpha iota → SubspaceTiling zeta alpha eta) :
    (T.bind R).covered =
      T.tiles.biUnion fun U ↦ ((R U).comp U).covered := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨A, hA, hxA⟩ := ((T.bind R).mem_covered x).1 hx
    change A ∈ T.tiles.biUnion (fun U ↦ ((R U).comp U).tiles) at hA
    obtain ⟨U, hU, hAU⟩ := Finset.mem_biUnion.mp hA
    apply Finset.mem_biUnion.mpr
    exact ⟨U, hU, (((R U).comp U).mem_covered x).2 ⟨A, hAU, hxA⟩⟩
  · intro hx
    obtain ⟨U, hU, hxU⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨A, hAU, hxA⟩ := (((R U).comp U).mem_covered x).1 hxU
    apply ((T.bind R).mem_covered x).2
    refine ⟨A, ?_, hxA⟩
    change A ∈ T.tiles.biUnion (fun V ↦ ((R V).comp V).tiles)
    exact Finset.mem_biUnion.mpr ⟨U, hU, hAU⟩

theorem density_covered [Fintype (iota → alpha)]
    (T : SubspaceTiling eta alpha iota) :
    density T.covered = ∑ U ∈ T.tiles, density (subspacePoints U) := by
  classical
  simp only [density]
  rw [T.card_covered]
  push_cast
  rw [Finset.sum_div]

end SubspaceTiling

end Families

section DensityOfDisjointUnions

variable {A I : Type*} [Fintype A] [DecidableEq A]

/-- Density is additive on a finite pairwise-disjoint union. -/
theorem density_biUnion {s : Finset I} {f : I → Finset A}
    (h : (s : Set I).PairwiseDisjoint f) :
    density (s.biUnion f) = ∑ i ∈ s, density (f i) := by
  classical
  simp only [density]
  rw [Finset.card_biUnion h]
  push_cast
  rw [Finset.sum_div]

/-- Sum a uniform relative-density bound over pairwise-disjoint ambient
pieces.  This is the quantitative bookkeeping used in the induction from one
insensitive factor to an intersection of insensitive factors. -/
theorem density_biUnion_le_mul_density_biUnion
    {s : Finset I} {p q : I → Finset A}
    (hp : (s : Set I).PairwiseDisjoint p)
    (hq : ∀ i ∈ s, q i ⊆ p i) {c : ℝ}
    (hlocal : ∀ i ∈ s, density (q i) ≤ c * density (p i)) :
    density (s.biUnion q) ≤ c * density (s.biUnion p) := by
  classical
  have hqdisj : (s : Set I).PairwiseDisjoint q := by
    intro i hi j hj hij
    exact (hp hi hj hij).mono (hq i hi) (hq j hj)
  rw [density_biUnion hqdisj, density_biUnion hp, Finset.mul_sum]
  gcongr with i hi
  exact hlocal i hi

end DensityOfDisjointUnions

section TilingStatements

/-- Intersection of a finite family of finsets, taken inside the full finite
ambient type. -/
noncomputable def familyInter {X : Type*} [Fintype X] {r : ℕ}
    (D : Fin r → Finset X) : Finset X := by
  classical
  exact Finset.univ.filter fun x ↦ ∀ j, x ∈ D j

@[simp] theorem mem_familyInter {X : Type*} [Fintype X] {r : ℕ}
    (D : Fin r → Finset X) (x : X) :
    x ∈ familyInter D ↔ ∀ j, x ∈ D j := by
  classical
  simp [familyInter]

@[simp] theorem familyInter_one {X : Type*} [Fintype X]
    (D : Fin 1 → Finset X) : familyInter D = D 0 := by
  ext x
  simp only [mem_familyInter]
  constructor
  · exact fun h ↦ h 0
  · intro hx j
    simpa only [Subsingleton.elim j 0] using hx

theorem familyInter_succ {X : Type*} [Fintype X] [DecidableEq X] {r : ℕ}
    (D : Fin (r + 1) → Finset X) :
    familyInter D =
      familyInter (fun j : Fin r ↦ D j.castSucc) ∩ D (Fin.last r) := by
  ext x
  simp only [mem_familyInter, Finset.mem_inter]
  constructor
  · intro h
    exact ⟨fun j ↦ h j.castSucc, h (Fin.last r)⟩
  · rintro ⟨hinit, hlast⟩ j
    exact Fin.lastCases hlast hinit j

/-- Exact-dimension form of DKT Lemma 12. -/
def OneInsensitiveTilingAt (k m n : ℕ) (beta : ℝ) : Prop :=
  ∀ (i : Fin k) (D : Finset (Word (k + 1) n)),
    IsLastInsensitive i (D : Set (Word (k + 1) n)) →
    2 * beta < density D →
    ∃ T : SubspaceTiling (Fin m) (Fin (k + 1)) (Fin n),
      T.IsContainedIn D ∧ density (D \ T.covered) < 2 * beta

/-- Exact-dimension form of DKT Corollary 13.  `label` records which old
letter each insensitive factor is paired with; the proof does not require
these labels to be distinct. -/
def InsensitiveIntersectionTilingAt (k r m n : ℕ) (beta : ℝ) : Prop :=
  ∀ (label : Fin r → Fin k) (D : Fin r → Finset (Word (k + 1) n)),
    (∀ j, IsLastInsensitive (label j) (D j : Set (Word (k + 1) n))) →
    2 * (r : ℝ) * beta < density (familyInter D) →
    ∃ T : SubspaceTiling (Fin m) (Fin (k + 1)) (Fin n),
      T.IsContainedIn (familyInter D) ∧
        density (familyInter D \ T.covered) < 2 * (r : ℝ) * beta

/-- Inductive step in DKT Corollary 13: first tile the intersection of the
first `r` factors by `F`-dimensional subspaces, then use the one-factor tiling
inside every retained large tile. -/
theorem InsensitiveIntersectionTilingAt.succ {k r F m n : ℕ} {beta : ℝ}
    (hbeta : 0 < beta) (hrpos : 0 < r)
    (hprev : InsensitiveIntersectionTilingAt k r F n beta)
    (hone : OneInsensitiveTilingAt k m F beta) :
    InsensitiveIntersectionTilingAt k (r + 1) m n beta := by
  classical
  intro label D hD hden
  let Dpre : Fin r → Finset (Word (k + 1) n) := fun j ↦ D j.castSucc
  let labelPre : Fin r → Fin k := fun j ↦ label j.castSucc
  let jlast : Fin (r + 1) := Fin.last r
  let Dlast : Finset (Word (k + 1) n) := D jlast
  have hsplit : familyInter D = familyInter Dpre ∩ Dlast := by
    simpa [Dpre, Dlast, jlast] using familyInter_succ D
  have hall_sub_pre : familyInter D ⊆ familyInter Dpre := by
    rw [hsplit]
    exact Finset.inter_subset_left
  have hmono : density (familyInter D) ≤ density (familyInter Dpre) :=
    density_mono hall_sub_pre
  have hrposR : (0 : ℝ) < r := by exact_mod_cast hrpos
  have hpreDen : 2 * (r : ℝ) * beta < density (familyInter Dpre) := by
    have hden' : 2 * ((r : ℝ) + 1) * beta < density (familyInter D) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hden
    nlinarith
  obtain ⟨T, hTsub, hTloss⟩ :=
    hprev labelPre Dpre (fun j ↦ hD j.castSucc) hpreDen
  have hlastInsensitive :
      IsLastInsensitive (label jlast) (Dlast : Set (Word (k + 1) n)) := by
    simpa [Dlast] using hD jlast
  have hinner : ∀ U : Combinatorics.Subspace (Fin F) (Fin (k + 1)) (Fin n),
      ∃ R : SubspaceTiling (Fin m) (Fin (k + 1)) (Fin F),
        R.IsContainedIn (subspacePullback U Dlast) ∧
          density (subspacePullback U Dlast \ R.covered) ≤ 2 * beta := by
    intro U
    have hins := hlastInsensitive.subspacePullback (label jlast) U Dlast
    by_cases hdense : 2 * beta < density (subspacePullback U Dlast)
    · obtain ⟨R, hRsub, hRloss⟩ :=
        hone (label jlast) (subspacePullback U Dlast) hins hdense
      exact ⟨R, hRsub, hRloss.le⟩
    · refine ⟨SubspaceTiling.empty, ?_, ?_⟩
      · intro V hV
        simp at hV
      · simpa using le_of_not_gt hdense
  choose R hRsub hRloss using hinner
  let S : SubspaceTiling (Fin m) (Fin (k + 1)) (Fin n) := T.bind R
  have hSpre : S.covered ⊆ familyInter Dpre := by
    intro x hx
    rw [show S.covered = T.tiles.biUnion (fun U ↦ ((R U).comp U).covered) by
      exact T.covered_bind R] at hx
    obtain ⟨U, hU, hxU⟩ := Finset.mem_biUnion.mp hx
    exact hTsub U hU (((R U).covered_comp_subset_subspacePoints U) hxU)
  have hSlast : S.covered ⊆ Dlast := by
    intro x hx
    rw [show S.covered = T.tiles.biUnion (fun U ↦ ((R U).comp U).covered) by
      exact T.covered_bind R] at hx
    obtain ⟨U, _hU, hxU⟩ := Finset.mem_biUnion.mp hx
    have hcomp : ((R U).comp U).IsContainedIn Dlast :=
      (((R U).comp_isContainedIn_iff U Dlast)).2 (hRsub U)
    exact (((R U).comp U).covered_subset_iff Dlast).2 hcomp hxU
  have hSsub : S.IsContainedIn (familyInter D) := by
    rw [← S.covered_subset_iff]
    rw [hsplit]
    exact fun _ hx ↦ Finset.mem_inter.mpr ⟨hSpre hx, hSlast hx⟩
  let q := fun U : Combinatorics.Subspace (Fin F) (Fin (k + 1)) (Fin n) ↦
    (subspacePullback U Dlast \ (R U).covered).image U
  have hqsub : ∀ U ∈ T.tiles, q U ⊆ subspacePoints U := by
    intro U _hU x hx
    simp only [q, Finset.mem_image] at hx
    obtain ⟨y, _hy, rfl⟩ := hx
    simp
  have hqlocal : ∀ U ∈ T.tiles,
      density (q U) ≤ (2 * beta) * density (subspacePoints U) := by
    intro U _hU
    rw [show density (q U) = density (subspacePoints U) *
        density (subspacePullback U Dlast \ (R U).covered) by
      exact density_image_subspace U _]
    have hpnonneg := density_nonneg (subspacePoints U)
    have := mul_le_mul_of_nonneg_left (hRloss U) hpnonneg
    nlinarith
  have hqUnion :
      density (T.tiles.biUnion q) ≤ 2 * beta := by
    have hsum := density_biUnion_le_mul_density_biUnion
      T.pairwiseDisjoint hqsub hqlocal
    have hcover : T.tiles.biUnion subspacePoints = T.covered := rfl
    rw [hcover] at hsum
    have hTle := density_le_one T.covered
    have hbnonneg : 0 ≤ 2 * beta := by positivity
    nlinarith
  have hresSub : familyInter D \ S.covered ⊆
      (familyInter Dpre \ T.covered) ∪ T.tiles.biUnion q := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    have hxall := hx'.1
    have hxnotS := hx'.2
    have hxpre : x ∈ familyInter Dpre := hall_sub_pre hxall
    have hxlast : x ∈ Dlast := by
      rw [hsplit] at hxall
      exact (Finset.mem_inter.mp hxall).2
    by_cases hxT : x ∈ T.covered
    · apply Finset.mem_union.mpr
      apply Or.inr
      obtain ⟨U, hU, hxU⟩ := (T.mem_covered x).1 hxT
      apply Finset.mem_biUnion.mpr
      refine ⟨U, hU, ?_⟩
      rw [show q U =
          (subspacePullback U Dlast \ (R U).covered).image U by rfl]
      rw [mem_subspacePoints] at hxU
      obtain ⟨y, hy⟩ := hxU
      subst x
      apply Finset.mem_image.mpr
      refine ⟨y, Finset.mem_sdiff.mpr ⟨?_, ?_⟩, rfl⟩
      · exact (mem_subspacePullback U Dlast y).2 hxlast
      · intro hycover
        apply hxnotS
        rw [show S.covered = T.tiles.biUnion
            (fun V ↦ ((R V).comp V).covered) by exact T.covered_bind R]
        apply Finset.mem_biUnion.mpr
        refine ⟨U, hU, ?_⟩
        rw [(R U).covered_comp U]
        exact Finset.mem_image_of_mem U hycover
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hxpre, hxT⟩))
  refine ⟨S, hSsub, ?_⟩
  have hresDen := density_mono hresSub
  have hunion := density_union_le_add
    (familyInter Dpre \ T.covered) (T.tiles.biUnion q)
  have htarget' :
      density (familyInter D \ S.covered) < 2 * (r : ℝ) * beta + 2 * beta := by
    linarith
  have hcast : (r + 1 : ℕ) = r + 1 := rfl
  push_cast
  nlinarith

/-- Lower-bound-preserving form of the qualitative intersection tiling
theorem.  Only the outermost recursive tiling needs to meet the requested
ambient-dimension bound; dimensions used for the inner tilings may be chosen
freely. -/
theorem exists_insensitiveIntersectionTilingAt_ge {k : ℕ} {beta : ℝ}
    (hbeta : 0 < beta)
    (hone : ∀ m N, ∃ n, N ≤ n ∧ OneInsensitiveTilingAt k m n beta) :
    ∀ r m N, ∃ n, N ≤ n ∧
      InsensitiveIntersectionTilingAt k (r + 1) m n beta := by
  intro r
  induction r with
  | zero =>
      intro m N
      obtain ⟨n, hNn, hn⟩ := hone m N
      refine ⟨n, hNn, ?_⟩
      intro label D hD hden
      have hden₀ : 2 * beta < density (D 0) := by
        simpa [familyInter_one] using hden
      obtain ⟨T, hTsub, hTloss⟩ := hn (label 0) (D 0) (hD 0) hden₀
      refine ⟨T, ?_, ?_⟩
      · simpa [familyInter_one] using hTsub
      · simpa [familyInter_one] using hTloss
  | succ r ihr =>
      intro m N
      obtain ⟨F, _hzeroF, hF⟩ := hone m 0
      obtain ⟨n, hNn, hn⟩ := ihr F N
      exact ⟨n, hNn, hn.succ hbeta (Nat.succ_pos r) hF⟩

end TilingStatements

end Erdos171

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/Framework.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Finitary density-Hales--Jewett frameworks

The density of a finset in Mathlib is an exact nonnegative rational number.
This file records two equivalent quantifier arrangements for density
Hales--Jewett: it is enough to obtain one dimension for each positive density,
because a dense fibre in every larger cube contains the same line.  We also
state the corresponding finite-dimensional-subspace property.
-/

namespace Erdos171

open scoped BigOperators

/-- A set of words contains an `m`-dimensional combinatorial subspace. -/
def ContainsSubspace (m : ℕ) {t n : ℕ} (A : Set (Word t n)) : Prop :=
  ∃ U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n), Set.range U ⊆ A

/-- One-witness formulation of density Hales--Jewett. -/
def FiniteDensityHJ (t : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n : ℕ, ∀ A : Finset (Word t n),
      δ ≤ density A → ContainsLine (A : Set (Word t n))

/-- Eventual formulation of density Hales--Jewett. -/
def EventualDensityHJ (t : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ A : Finset (Word t n),
      δ ≤ density A → ContainsLine (A : Set (Word t n))

/-- The one-witness formulation for an `m`-dimensional subspace. -/
def FiniteDensityMDHJ (t m : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n : ℕ, ∀ A : Finset (Word t n),
      δ ≤ density A → ContainsSubspace m (A : Set (Word t n))

/-- The eventual formulation for an `m`-dimensional subspace. -/
def EventualDensityMDHJ (t m : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ A : Finset (Word t n),
      δ ≤ density A → ContainsSubspace m (A : Set (Word t n))

/-- Split a word into an initial and a final block. -/
def wordAddEquiv (t m r : ℕ) : Word t (m + r) ≃ Word t m × Word t r :=
  (Equiv.piCongrLeft (fun _ : Fin (m + r) ↦ Fin t) finSumFinEquiv).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin r) (Fin t))

@[simp] theorem wordAddEquiv_apply_fst (t m r : ℕ) (w : Word t (m + r))
    (i : Fin m) : (wordAddEquiv t m r w).1 i = w (Fin.castAdd r i) := by
  simp [wordAddEquiv]

@[simp] theorem wordAddEquiv_apply_snd (t m r : ℕ) (w : Word t (m + r))
    (i : Fin r) : (wordAddEquiv t m r w).2 i = w (Fin.natAdd m i) := by
  simp [wordAddEquiv]

/-- Split a word, with the final block placed first for fibrewise counting. -/
def wordFiberEquiv (t m r : ℕ) : Word t (m + r) ≃ Word t r × Word t m :=
  (wordAddEquiv t m r).trans (Equiv.prodComm _ _)

/-- A line on an initial block, extended by a fixed final block. -/
def extendLineRight {t m r : ℕ}
    (l : Combinatorics.Line (Fin t) (Fin m)) (z : Word t r) :
    Combinatorics.Line (Fin t) (Fin (m + r)) where
  idxFun i := match finSumFinEquiv.symm i with
    | Sum.inl j => l.idxFun j
    | Sum.inr j => some (z j)
  proper := by
    obtain ⟨j, hj⟩ := l.proper
    exact ⟨Fin.castAdd r j, by simp [hj]⟩

@[simp] theorem extendLineRight_apply {t m r : ℕ}
    (l : Combinatorics.Line (Fin t) (Fin m)) (z : Word t r) (a : Fin t) :
    wordFiberEquiv t m r (extendLineRight l z a) = (z, l a) := by
  apply Prod.ext
  · funext i
    change extendLineRight l z a (Fin.natAdd m i) = z i
    simp [extendLineRight, Combinatorics.Line.coe_apply]
  · funext i
    change extendLineRight l z a (Fin.castAdd r i) = l a i
    simp [extendLineRight, Combinatorics.Line.coe_apply]

/-- Regard a combinatorial line as a one-dimensional subspace. -/
def lineSubspace {α ι : Type*} (l : Combinatorics.Line α ι) :
    Combinatorics.Subspace (Fin 1) α ι where
  idxFun i := (l.idxFun i).elim (Sum.inr 0) Sum.inl
  proper e := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i, by simp [hi, Fin.eq_zero e]⟩

@[simp] theorem lineSubspace_apply {α ι : Type*} (l : Combinatorics.Line α ι)
    (x : Fin 1 → α) : lineSubspace l x = l (x 0) := by
  funext i
  cases hi : l.idxFun i <;>
    simp [lineSubspace, Combinatorics.Line.coe_apply,
      Combinatorics.Subspace.coe_apply, hi]

/-- Independently join an `m`-subspace on an initial coordinate block and a
line on a final coordinate block. -/
def appendSubspaceLine {t m n r : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n))
    (l : Combinatorics.Line (Fin t) (Fin r)) :
    Combinatorics.Subspace (Fin (m + 1)) (Fin t) (Fin (n + r)) :=
  (U.sum (lineSubspace l)).reindex finSumFinEquiv (Equiv.refl _) finSumFinEquiv

@[simp] theorem wordAddEquiv_appendSubspaceLine_apply {t m n r : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n))
    (l : Combinatorics.Line (Fin t) (Fin r))
    (x : Word t (m + 1)) :
    wordAddEquiv t n r (appendSubspaceLine U l x) =
      (U (fun i ↦ x (Fin.castAdd 1 i)), l (x (Fin.last m))) := by
  apply Prod.ext
  · funext i
    simp only [wordAddEquiv_apply_fst, appendSubspaceLine,
      Combinatorics.Subspace.reindex_apply, Equiv.refl_apply,
      Equiv.refl_symm, finSumFinEquiv_symm_apply_castAdd,
      Combinatorics.Subspace.sum_apply_inl, Function.comp_apply,
      finSumFinEquiv_apply_left]
    have hf :
        ((⇑(Equiv.refl (Fin t)) ∘ x ∘ ⇑finSumFinEquiv) ∘ Sum.inl) =
          (fun j : Fin m ↦ x (Fin.castAdd 1 j)) := by
      funext j
      simp
    rw [hf]
  · funext i
    simp only [wordAddEquiv_apply_snd, appendSubspaceLine,
      Combinatorics.Subspace.reindex_apply, Equiv.refl_apply,
      Equiv.refl_symm, finSumFinEquiv_symm_apply_natAdd,
      Combinatorics.Subspace.sum_apply_inr, Function.comp_apply,
      lineSubspace_apply]
    have hz : Fin.natAdd m (0 : Fin 1) = Fin.last m := by ext; simp
    rw [finSumFinEquiv_apply_right, hz]

/-- Extend a subspace on an initial coordinate block by a fixed final word. -/
def extendSubspaceRight {t m n r : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n)) (z : Word t r) :
    Combinatorics.Subspace (Fin m) (Fin t) (Fin (n + r)) :=
  (U.extendRightWord z).reindex (Equiv.refl _) (Equiv.refl _) finSumFinEquiv

@[simp] theorem extendSubspaceRight_apply {t m n r : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n)) (z : Word t r)
    (x : Word t m) :
    wordFiberEquiv t n r (extendSubspaceRight U z x) = (z, U x) := by
  apply Prod.ext
  · funext i
    change extendSubspaceRight U z x (Fin.natAdd n i) = z i
    simp [extendSubspaceRight, Combinatorics.Subspace.reindex_apply]
  · funext i
    change extendSubspaceRight U z x (Fin.castAdd r i) = U x i
    simp [extendSubspaceRight, Combinatorics.Subspace.reindex_apply]

/-- Some fibre of a nonempty finite product has density at least the density of
the whole set.  This is the exact finite averaging principle needed for
cylinder lifting. -/
theorem exists_fiber_density_ge {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (A : Finset (X × Y)) :
    ∃ x : X, density A ≤ density (fiber A x) := by
  rw [density_eq_average_fiber]
  exact exists_average_le _

/-- The graph of a finite colouring, restricted to a finset. -/
noncomputable def colorGraph {X C : Type*} (D : Finset X) (color : X → C) :
    Finset (C × X) := by
  classical
  exact D.map
    ⟨fun x ↦ (color x, x), fun _ _ h ↦ congrArg Prod.snd h⟩

@[simp] theorem mem_colorGraph {X C : Type*} (D : Finset X) (color : X → C)
    (c : C) (x : X) :
    (c, x) ∈ colorGraph D color ↔ x ∈ D ∧ color x = c := by
  classical
  constructor
  · rw [colorGraph, Finset.mem_map]
    rintro ⟨y, hy, hpair⟩
    have hyx : y = x := congrArg Prod.snd hpair
    subst y
    exact ⟨hy, congrArg Prod.fst hpair⟩
  · rintro ⟨hx, hcolor⟩
    rw [colorGraph, Finset.mem_map]
    exact ⟨x, hx, Prod.ext hcolor rfl⟩

theorem density_colorGraph {X C : Type*} [Fintype X] [Fintype C]
    (D : Finset X) (color : X → C) :
    density (colorGraph D color) = density D / Fintype.card C := by
  classical
  simp only [density_eq_card_div_card, colorGraph, Finset.card_map, Fintype.card_prod]
  push_cast
  ring

/-- One colour class, regarded as a finset in the original ambient type. -/
noncomputable def colorClass {X C : Type*} [Fintype X]
    (D : Finset X) (color : X → C) (c : C) : Finset X := by
  classical
  exact Finset.univ.filter fun x ↦ x ∈ D ∧ color x = c

@[simp] theorem mem_colorClass {X C : Type*} [Fintype X]
    (D : Finset X) (color : X → C) (c : C) (x : X) :
    x ∈ colorClass D color c ↔ x ∈ D ∧ color x = c := by
  classical
  simp [colorClass]

/-- A finite colouring has a colour class whose ambient density is at least
the density of the coloured set divided by the number of colours. -/
theorem exists_dense_colorClass {X C : Type*} [Fintype X] [Fintype C]
    [Nonempty X] [Nonempty C] (D : Finset X) (color : X → C) :
    ∃ c : C, density D / Fintype.card C ≤
      density (colorClass D color c) := by
  classical
  obtain ⟨c, hc⟩ := exists_fiber_density_ge (colorGraph D color)
  have hfiber : fiber (colorGraph D color) c = colorClass D color c := by
    ext x
    simp
  refine ⟨c, ?_⟩
  rw [density_colorGraph] at hc
  simpa only [hfiber] using hc

/-- A single witnessing dimension for every positive density automatically
works in every larger dimension. -/
theorem FiniteDensityHJ.eventual {t : ℕ} (h : FiniteDensityHJ t) (ht : 0 < t) :
    EventualDensityHJ t := by
  intro δ hδ
  obtain ⟨m, hm⟩ := h δ hδ
  refine ⟨m, ?_⟩
  intro n hmn A hA
  letI : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hmn
  classical
  let e := wordFiberEquiv t m r
  let B : Finset (Word t r × Word t m) := A.map e.toEmbedding
  have hB : δ ≤ density B := by
    change δ ≤ density (A.map e.toEmbedding)
    rw [density_map_equiv]
    exact hA
  obtain ⟨z, hz⟩ := exists_fiber_density_ge B
  obtain ⟨l, hl⟩ := hm (fiber B z) (hB.trans hz)
  refine ⟨extendLineRight l z, ?_⟩
  rintro _ ⟨a, rfl⟩
  have hmemB : (z, l a) ∈ B := (mem_fiber B z (l a)).1 (hl ⟨a, rfl⟩)
  have hmemA : e.symm (z, l a) ∈ A := by simpa [B] using hmemB
  have heq : e.symm (z, l a) = extendLineRight l z a := by
    apply e.injective
    simp [e]
  simpa [heq] using hmemA

/-- As for lines, a single witnessing dimension for an `m`-subspace works in
every larger dimension by fixing a dense fibre. -/
theorem FiniteDensityMDHJ.eventual {t m : ℕ} (h : FiniteDensityMDHJ t m)
    (ht : 0 < t) : EventualDensityMDHJ t m := by
  intro δ hδ
  obtain ⟨n₀, hn₀⟩ := h δ hδ
  refine ⟨n₀, ?_⟩
  intro n hn A hA
  letI : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  classical
  let e := wordFiberEquiv t n₀ r
  let B : Finset (Word t r × Word t n₀) := A.map e.toEmbedding
  have hB : δ ≤ density B := by
    change δ ≤ density (A.map e.toEmbedding)
    rw [density_map_equiv]
    exact hA
  obtain ⟨z, hz⟩ := exists_fiber_density_ge B
  obtain ⟨U, hU⟩ := hn₀ (fiber B z) (hB.trans hz)
  refine ⟨extendSubspaceRight U z, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hmemB : (z, U x) ∈ B := (mem_fiber B z (U x)).1 (hU ⟨x, rfl⟩)
  have hmemA : e.symm (z, U x) ∈ A := by simpa [B] using hmemB
  have heq : e.symm (z, U x) = extendSubspaceRight U z x := by
    apply e.injective
    simp [e]
  simpa [heq] using hmemA

end Erdos171

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/UniformFibres.lean` -/

section
/-!
# Uniform fibres by a finite energy-increment argument

This file proves the elementary uniform-fibres lemma used in the Dodos--
Kanellopoulos--Tyros proof of density Hales--Jewett.  The exact argument is
carried out with Mathlib's rational `Finset.dens`; a wrapper supplies real
inequalities for the rest of the development.
-/

namespace Erdos171

open scoped BigOperators

abbrev BlockTower.{u} (X Y : Type u) : Nat → Type u
  | 0 => Y
  | n + 1 => X × BlockTower X Y n

namespace BlockTower

variable {X Y : Type u} [Fintype X] [Fintype Y]

noncomputable instance instFintype : ∀ r, Fintype (BlockTower X Y r)
  | 0 => inferInstanceAs (Fintype Y)
  | n + 1 => @instFintypeProd X (BlockTower X Y n) inferInstance (instFintype n)

noncomputable def fibre {r : ℕ} (A : Finset (BlockTower X Y (r + 1))) (x : X) :
    Finset (BlockTower X Y r) := by
  classical exact Finset.univ.filter (fun z ↦ (x, z) ∈ A)

@[simp] theorem mem_fibre {r : ℕ} (A : Finset (BlockTower X Y (r + 1)))
    (x : X) (z : BlockTower X Y r) : z ∈ fibre A x ↔ (x, z) ∈ A := by
  classical simp [fibre]

/-- Split a word at a block boundary. -/
def wordAddEquiv (t m n : ℕ) :
    Word t (m + n) ≃ Word t m × Word t n :=
  (Equiv.piCongrLeft (fun _ : Fin (m + n) ↦ Fin t) finSumFinEquiv).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) (Fin t))

/-- Flatten an iterated tower of `m`-letter blocks followed by an `s`-letter
suffix into an ordinary word. -/
def wordEquiv (t m s : ℕ) : ∀ r : ℕ,
    BlockTower (Word t m) (Word t s) r ≃ Word t (r * m + s)
  | 0 => by simpa using Equiv.refl (Word t s)
  | r + 1 =>
      ((Equiv.refl (Word t m)).prodCongr (wordEquiv t m s r)).trans <|
        (wordAddEquiv t m (r * m + s)).symm.trans <|
          Equiv.piCongrLeft (fun _ : Fin ((r + 1) * m + s) ↦ Fin t) <|
            finCongr (by simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm])

@[simp] theorem dens_map_wordEquiv (t m s r : ℕ)
    (A : Finset (BlockTower (Word t m) (Word t s) r)) :
    (A.map (wordEquiv t m s r).toEmbedding).dens = A.dens := by
  exact Finset.dens_map_equiv _

end BlockTower

namespace UniformFibres

open BlockTower

variable {X : Type u} [Fintype X]

variable {Y : Type u} [Fintype Y]

/-- A record of the initial blocks frozen before the uniform block.  The two
indices are the original and remaining tower heights. -/
inductive FrozenPrefix (X : Type u) : ℕ → ℕ → Type u
  | nil (r : ℕ) : FrozenPrefix X r r
  | cons {r q : ℕ} (x : X) (p : FrozenPrefix X r q) : FrozenPrefix X (r + 1) q

namespace FrozenPrefix

/-- Insert the frozen blocks in front of a remaining tower word. -/
def prepend {X Y : Type u} : {r q : ℕ} → FrozenPrefix X r q →
    BlockTower X Y q → BlockTower X Y r
  | _, _, .nil _, z => z
  | _, _, .cons x p, z => (x, prepend p z)

noncomputable def iterFibre {X Y : Type u} [Fintype X] [Fintype Y] :
    {r q : ℕ} → FrozenPrefix X r q → Finset (BlockTower X Y r) →
      Finset (BlockTower X Y q)
  | _, _, .nil _, A => A
  | _, _, .cons x p, A => iterFibre p (BlockTower.fibre A x)

@[simp] theorem iterFibre_nil {X Y : Type u} [Fintype X] [Fintype Y]
    (r : ℕ) (A : Finset (BlockTower X Y r)) :
    iterFibre (.nil r : FrozenPrefix X r r) A = A := rfl

@[simp] theorem iterFibre_cons {X Y : Type u} [Fintype X] [Fintype Y]
    {r q : ℕ} (x : X) (p : FrozenPrefix X r q)
    (A : Finset (BlockTower X Y (r + 1))) :
    iterFibre (.cons x p) A = iterFibre p (BlockTower.fibre A x) := rfl

@[simp] theorem mem_iterFibre {X Y : Type u} [Fintype X] [Fintype Y] :
    ∀ {r q : ℕ} (p : FrozenPrefix X r q)
      (A : Finset (BlockTower X Y r)) (z : BlockTower X Y q),
      z ∈ p.iterFibre A ↔ prepend p z ∈ A
  | _, _, .nil _, A, z => Iff.rfl
  | _, _, .cons x p, A, z => by
      rw [iterFibre_cons, mem_iterFibre, mem_fibre]
      rfl

end FrozenPrefix

end UniformFibres

end Erdos171

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/RestrictedMDHJ.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Restricted multidimensional density Hales--Jewett

This file formalizes Corollary 5 of Dodos--Kanellopoulos--Tyros.  Assuming
density Hales--Jewett for the alphabet `Fin k`, every dense subset of a large
cube over `Fin (k + 1)` contains the old-alphabet face of an arbitrarily
high-dimensional combinatorial subspace.
-/

namespace Erdos171

/-- The nested coordinate type corresponding to a tower of word blocks. -/
abbrev BlockCoord (M s : ℕ) : ℕ → Type
  | 0 => Fin s
  | r + 1 => Fin M ⊕ BlockCoord M s r

namespace BlockCoord

/-- Flatten the nested coordinate type of a block tower. -/
def equivFin (M s : ℕ) : ∀ r : ℕ, BlockCoord M s r ≃ Fin (r * M + s)
  | 0 => finCongr (by simp)
  | r + 1 =>
      ((Equiv.refl (Fin M)).sumCongr (equivFin M s r)).trans <|
        finSumFinEquiv.trans <| finCongr (by
          simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm])

end BlockCoord

namespace BlockTower

universe u

theorem nonempty {X Y : Type u} [Nonempty X] [Nonempty Y] :
    ∀ r : ℕ, Nonempty (BlockTower X Y r)
  | 0 => inferInstance
  | r + 1 => by
      letI : Nonempty (BlockTower X Y r) :=
        nonempty (X := X) (Y := Y) r
      infer_instance

/-- View a tower of word blocks as a word on the corresponding nested
coordinate type. -/
def functionEquiv (t M s : ℕ) : ∀ r : ℕ,
    BlockTower (Word t M) (Word t s) r ≃ (BlockCoord M s r → Fin t)
  | 0 => Equiv.refl _
  | r + 1 =>
      ((Equiv.refl (Word t M)).prodCongr (functionEquiv t M s r)).trans
        (Equiv.sumArrowEquivProdArrow (Fin M) (BlockCoord M s r) (Fin t)).symm

@[simp] theorem functionEquiv_zero_apply (t M s : ℕ) (z : Word t s) :
    functionEquiv t M s 0 z = z := rfl

@[simp] theorem functionEquiv_succ_apply (t M s r : ℕ)
    (z : Word t M) (y : BlockTower (Word t M) (Word t s) r) :
    functionEquiv t M s (r + 1) (z, y) =
      Sum.elim z (functionEquiv t M s r y) := by
  rfl

/-- A block-tower/ordinary-word equivalence factored through its explicit
coordinate equivalence. -/
def coordinateWordEquiv (t M s r : ℕ) :
    BlockTower (Word t M) (Word t s) r ≃ Word t (r * M + s) :=
  (functionEquiv t M s r).trans <|
    Equiv.piCongrLeft (fun _ : Fin (r * M + s) ↦ Fin t) (BlockCoord.equivFin M s r)

@[simp] theorem coordinateWordEquiv_apply (t M s r : ℕ)
    (z : BlockTower (Word t M) (Word t s) r) (i : Fin (r * M + s)) :
    coordinateWordEquiv t M s r z i =
      functionEquiv t M s r z ((BlockCoord.equivFin M s r).symm i) := by
  simp only [coordinateWordEquiv, Equiv.trans_apply]
  rw [Equiv.piCongrLeft_apply]
  simp

end BlockTower

/-- Prepend a fixed coordinate block without changing the parameter
directions of a subspace. -/
def fixedLeft {eta alpha iota kappa : Type*} (z : kappa → alpha)
    (U : Combinatorics.Subspace eta alpha iota) :
    Combinatorics.Subspace eta alpha (kappa ⊕ iota) where
  idxFun
    | Sum.inl i => Sum.inl (z i)
    | Sum.inr j => U.idxFun j
  proper e := by
    obtain ⟨j, hj⟩ := U.proper e
    exact ⟨Sum.inr j, hj⟩

@[simp] theorem fixedLeft_apply {eta alpha iota kappa : Type*}
    (z : kappa → alpha) (U : Combinatorics.Subspace eta alpha iota)
    (x : eta → alpha) :
    fixedLeft z U x = Sum.elim z (U x) := by
  funext i
  cases i <;> simp [fixedLeft, Combinatorics.Subspace.coe_apply]

namespace UniformFibres.FrozenPrefix

open BlockTower

/-- Realize a frozen prefix, a subspace in the next block, and a fixed
remaining suffix as a subspace in the original flattened word cube. -/
def realizeNested {t M s m q : ℕ} : ∀ {r : ℕ},
    FrozenPrefix (Word t M) r (q + 1) →
      Combinatorics.Subspace (Fin m) (Fin t) (Fin M) →
      BlockTower (Word t M) (Word t s) q →
      Combinatorics.Subspace (Fin m) (Fin t) (BlockCoord M s r)
  | _, .nil _, V, y =>
      V.extendRightWord (BlockTower.functionEquiv t M s q y)
  | _, .cons z p, V, y =>
      fixedLeft z (realizeNested p V y)

@[simp] theorem realizeNested_apply {t M s m : ℕ} : ∀ {q r : ℕ}
    (p : FrozenPrefix (Word t M) r (q + 1))
    (V : Combinatorics.Subspace (Fin m) (Fin t) (Fin M))
    (y : BlockTower (Word t M) (Word t s) q) (x : Word t m),
    realizeNested p V y x =
      BlockTower.functionEquiv t M s r (p.prepend (V x, y))
  | q, _, .nil _, V, y, x => by
      rw [show realizeNested (.nil (q + 1)) V y x =
          Sum.elim (V x) (BlockTower.functionEquiv t M s q y) by
        simp [realizeNested, Combinatorics.Subspace.extendRightWord_apply,
          Combinatorics.Subspace.sumWord]]
      exact (BlockTower.functionEquiv_succ_apply t M s q (V x) y).symm
  | q, _, .cons z p, V, y, x => by
      rw [show realizeNested (.cons z p) V y x =
          Sum.elim z (realizeNested p V y x) by
        simp [realizeNested]]
      rw [realizeNested_apply p V y x]
      exact (BlockTower.functionEquiv_succ_apply t M s _ z
        (p.prepend (V x, y))).symm

/-- Flatten `realizeNested` to an ordinary `Fin`-indexed word cube. -/
def realize {t M s m q r : ℕ}
    (p : FrozenPrefix (Word t M) r (q + 1))
    (V : Combinatorics.Subspace (Fin m) (Fin t) (Fin M))
    (y : BlockTower (Word t M) (Word t s) q) :
    Combinatorics.Subspace (Fin m) (Fin t) (Fin (r * M + s)) :=
  (realizeNested p V y).reindex (Equiv.refl _) (Equiv.refl _)
    (BlockCoord.equivFin M s r)

@[simp] theorem realize_apply {t M s m q r : ℕ}
    (p : FrozenPrefix (Word t M) r (q + 1))
    (V : Combinatorics.Subspace (Fin m) (Fin t) (Fin M))
    (y : BlockTower (Word t M) (Word t s) q) (x : Word t m) :
    realize p V y x =
      BlockTower.coordinateWordEquiv t M s r (p.prepend (V x, y)) := by
  funext i
  simp [realize,
    Combinatorics.Subspace.reindex_apply]

end UniformFibres.FrozenPrefix

/-- A set in a cube over `Fin (k + 1)` contains the restriction to the old
alphabet `Fin k` of an `m`-dimensional combinatorial subspace. -/
def ContainsRestrictedSubspace (m : ℕ) {k n : ℕ}
    (A : Set (Word (k + 1) n)) : Prop :=
  ∃ U : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
    Set.range (fun x : Word k m ↦ U (liftWord x)) ⊆ A

theorem containsRestrictedSubspace_iff (m : ℕ) {k n : ℕ}
    {A : Set (Word (k + 1) n)} :
    ContainsRestrictedSubspace m A ↔
      ∃ U : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
        ∀ x : Word k m, U (liftWord x) ∈ A := by
  constructor
  · rintro ⟨U, hU⟩
    exact ⟨U, fun x ↦ hU ⟨x, rfl⟩⟩
  · rintro ⟨U, hU⟩
    refine ⟨U, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hU x

theorem ContainsRestrictedSubspace.mono {m k n : ℕ}
    {A B : Set (Word (k + 1) n)}
    (hA : ContainsRestrictedSubspace m A) (hAB : A ⊆ B) :
    ContainsRestrictedSubspace m B := by
  obtain ⟨U, hU⟩ := hA
  exact ⟨U, hU.trans hAB⟩

/-- One-witness form of the restricted multidimensional density theorem. -/
def FiniteRestrictedMDHJ (k m : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n : ℕ, ∀ A : Finset (Word (k + 1) n),
      δ ≤ density A → ContainsRestrictedSubspace m (A : Set (Word (k + 1) n))

/-- Eventual form of the restricted multidimensional density theorem. -/
def EventualRestrictedMDHJ (k m : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ A : Finset (Word (k + 1) n),
      δ ≤ density A → ContainsRestrictedSubspace m (A : Set (Word (k + 1) n))

/-- A witnessing dimension for the restricted theorem works in every larger
ambient dimension, by restricting to a dense fibre and fixing the added
coordinates. -/
theorem FiniteRestrictedMDHJ.eventual {k m : ℕ} (h : FiniteRestrictedMDHJ k m) :
    EventualRestrictedMDHJ k m := by
  intro δ hδ
  obtain ⟨n₀, hn₀⟩ := h δ hδ
  refine ⟨n₀, ?_⟩
  intro n hn A hA
  letI : Nonempty (Fin (k + 1)) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  classical
  let e := wordFiberEquiv (k + 1) n₀ r
  let B : Finset (Word (k + 1) r × Word (k + 1) n₀) := A.map e.toEmbedding
  have hB : δ ≤ density B := by
    change δ ≤ density (A.map e.toEmbedding)
    rw [density_map_equiv]
    exact hA
  obtain ⟨z, hz⟩ := exists_fiber_density_ge B
  obtain ⟨U, hU⟩ := hn₀ (fiber B z) (hB.trans hz)
  refine ⟨extendSubspaceRight U z, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hmemB : (z, U (liftWord x)) ∈ B :=
    (mem_fiber B z (U (liftWord x))).1 (hU ⟨x, rfl⟩)
  have hmemA : e.symm (z, U (liftWord x)) ∈ A := by
    simpa [B] using hmemB
  have heq : e.symm (z, U (liftWord x)) =
      extendSubspaceRight U z (liftWord x) := by
    apply e.injective
    simp [e]
  simpa [heq] using hmemA

/-- Positive-dimension witness form, convenient when the ambient cube will
later be repeated in blocks. -/
theorem FiniteRestrictedMDHJ.positiveWitness {k m : ℕ}
    (h : FiniteRestrictedMDHJ k m) (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ ∀ A : Finset (Word (k + 1) n),
      δ ≤ density A → ContainsRestrictedSubspace m (A : Set (Word (k + 1) n)) := by
  obtain ⟨n₀, hn₀⟩ := h.eventual δ hδ
  refine ⟨max n₀ 1, lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _), ?_⟩
  exact hn₀ _ (Nat.le_max_left _ _)

end Erdos171

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/InsensitiveTiling.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Tiling an insensitive set

This file contains the tiling step in the Dodos--Kanellopoulos--Tyros proof.
The first lemma is its elementary geometric core: on an `(i,last)`-insensitive
set, containment of the old-alphabet restriction of a subspace upgrades to
containment of the whole subspace.
-/

namespace Erdos171

open Combinatorics

/-- Membership in the image of a finite set under an equivalence. -/
@[simp] theorem mem_map_equiv_toEmbedding {A B : Type*}
    [DecidableEq A] [DecidableEq B] (e : A ≃ B) (S : Finset A) (b : B) :
    b ∈ S.map e.toEmbedding ↔ e.symm b ∈ S := by
  constructor
  · intro hb
    obtain ⟨a, ha, hab⟩ := Finset.mem_map.mp hb
    simpa [← hab] using ha
  · intro hb
    exact Finset.mem_map.mpr ⟨e.symm b, hb, e.apply_symm_apply b⟩

/-- The family of all translates of a common block template over its
support.  It is defined early because both the geometric tiling construction
and the fresh-block invariant use the same finite set. -/
noncomputable def commonBlockLayer {X B Y : Type*}
    [Fintype X] [Fintype B] [Fintype Y]
    (S : Finset (X × Y)) (V : Finset B) : Finset ((X × B) × Y) := by
  classical
  exact Finset.univ.filter fun z ↦ (z.1.1, z.2) ∈ S ∧ z.1.2 ∈ V

@[simp] theorem mem_commonBlockLayer {X B Y : Type*}
    [Fintype X] [Fintype B] [Fintype Y]
    (S : Finset (X × Y)) (V : Finset B) (z : (X × B) × Y) :
    z ∈ commonBlockLayer S V ↔ (z.1.1, z.2) ∈ S ∧ z.1.2 ∈ V := by
  classical
  simp [commonBlockLayer]

section MiddleSubspaces

variable {eta alpha xi mu upsilon : Type*}

/-- Insert a subspace in a middle coordinate block, fixing the coordinates
on both sides. -/
def middleSubspace (x : xi → alpha) (U : Subspace eta alpha mu)
    (y : upsilon → alpha) : Subspace eta alpha ((xi ⊕ mu) ⊕ upsilon) where
  idxFun
    | Sum.inl (Sum.inl a) => Sum.inl (x a)
    | Sum.inl (Sum.inr b) => U.idxFun b
    | Sum.inr c => Sum.inl (y c)
  proper e := by
    obtain ⟨b, hb⟩ := U.proper e
    exact ⟨Sum.inl (Sum.inr b), hb⟩

@[simp] theorem middleSubspace_apply (x : xi → alpha)
    (U : Subspace eta alpha mu) (y : upsilon → alpha) (a : eta → alpha) :
    middleSubspace x U y a = Sum.elim (Sum.elim x (U a)) y := by
  funext c
  rcases c with (c | c) | c <;> simp [middleSubspace, Subspace.coe_apply]

/-- Split a word into the unused coordinates, current block, and used
suffix. -/
def splitMiddleWord : (((xi ⊕ mu) ⊕ upsilon) → alpha) ≃
    (((xi → alpha) × (mu → alpha)) × (upsilon → alpha)) :=
  (Equiv.sumArrowEquivProdArrow (xi ⊕ mu) upsilon alpha).trans
    ((Equiv.sumArrowEquivProdArrow xi mu alpha).prodCongr (Equiv.refl _))

@[simp] theorem splitMiddleWord_middleSubspace_apply
    (x : xi → alpha) (U : Subspace eta alpha mu)
    (y : upsilon → alpha) (a : eta → alpha) :
    splitMiddleWord (middleSubspace x U y a) = ((x, U a), y) := by
  rfl

variable [Fintype (eta → alpha)] [Fintype (xi → alpha)]
  [Fintype (mu → alpha)] [Fintype (upsilon → alpha)]
  [DecidableEq (mu → alpha)]
  [DecidableEq (((xi ⊕ mu) ⊕ upsilon) → alpha)]

/-- The translates of one common middle-block template form a disjoint
subspace tiling. -/
noncomputable def commonBlockTiling
    (S : Finset ((xi → alpha) × (upsilon → alpha)))
    (U : Subspace eta alpha mu) :
    SubspaceTiling eta alpha ((xi ⊕ mu) ⊕ upsilon) := by
  classical
  exact
    { tiles := S.image fun p ↦ middleSubspace p.1 U p.2
      pairwiseDisjoint := by
        intro A hA B hB hAB
        obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨q, hqS, rfl⟩ := Finset.mem_image.mp hB
        change Disjoint (subspacePoints (middleSubspace p.1 U p.2))
          (subspacePoints (middleSubspace q.1 U q.2))
        rw [Finset.disjoint_left]
        intro z hzP hzQ
        rw [mem_subspacePoints] at hzP hzQ
        obtain ⟨a, ha⟩ := hzP
        obtain ⟨b, hb⟩ := hzQ
        have heq : ((p.1, U a), p.2) = ((q.1, U b), q.2) := by
          rw [← splitMiddleWord_middleSubspace_apply p.1 U p.2 a,
            ← splitMiddleWord_middleSubspace_apply q.1 U q.2 b,
            ha, hb]
        have hpq : p = q := by
          apply Prod.ext
          · exact congrArg (fun w ↦ w.1.1) heq
          · exact congrArg
              (fun w : (((xi → alpha) × (mu → alpha)) × (upsilon → alpha)) ↦ w.2) heq
        exact hAB (congrArg (fun r ↦ middleSubspace r.1 U r.2) hpq) }

/-- The covered set of the common-block tiling is exactly the layer obtained
by taking its support times the point set of the template. -/
theorem image_covered_commonBlockTiling
    (S : Finset ((xi → alpha) × (upsilon → alpha)))
    (U : Subspace eta alpha mu) :
    (commonBlockTiling S U).covered.map splitMiddleWord.toEmbedding =
      commonBlockLayer S (subspacePoints U) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_map.mp hz
    obtain ⟨V, hV, hwV⟩ := ((commonBlockTiling S U).mem_covered w).mp hw
    obtain ⟨p, hpS, hpV⟩ := Finset.mem_image.mp hV
    subst V
    rw [mem_subspacePoints] at hwV
    obtain ⟨a, rfl⟩ := hwV
    have hz : z = ((p.1, U a), p.2) := hwz.symm
    subst z
    change ((p.1, U a), p.2) ∈ commonBlockLayer S (subspacePoints U)
    exact (mem_commonBlockLayer S (subspacePoints U) _).mpr
      ⟨hpS, by simp⟩
  · intro hz
    have hz' := (mem_commonBlockLayer S (subspacePoints U) z).mp hz
    rw [mem_subspacePoints] at hz'
    obtain ⟨b, hb⟩ := hz'.2
    apply Finset.mem_map.mpr
    refine ⟨middleSubspace z.1.1 U z.2 b, ?_, ?_⟩
    swap
    · change splitMiddleWord (middleSubspace z.1.1 U z.2 b) = z
      rw [splitMiddleWord_middleSubspace_apply]
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · exact hb
      · rfl
    apply ((commonBlockTiling S U).mem_covered _).2
    refine ⟨middleSubspace z.1.1 U z.2, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(z.1.1, z.2), hz'.1, rfl⟩
    · simp

end MiddleSubspaces

/-- If the old-alphabet restriction of a subspace lies in an insensitive set,
then its entire parameter cube lies in that set. -/
theorem subspacePoints_subset_of_restricted_of_isLastInsensitive
    {k m n : ℕ} (i : Fin k) (D : Finset (Word (k + 1) n))
    (hD : IsLastInsensitive i (D : Set (Word (k + 1) n)))
    (U : Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (hU : ∀ x : Word k m, U (liftWord x) ∈ D) :
    subspacePoints U ⊆ D := by
  intro z hz
  rw [mem_subspacePoints] at hz
  obtain ⟨y, rfl⟩ := hz
  have heq : LastEquivalent i (U (liftWord (endpoint i y))) (U y) := by
    rw [LastEquivalent]
    funext r
    cases hr : U.idxFun r with
    | inl a =>
        simp [replaceLast, Subspace.coe_apply, hr]
    | inr e =>
        simp [replaceLast, Subspace.coe_apply, hr, liftWord,
          castSucc_endpoint]
  exact (hD _ _ heq).mp (hU (endpoint i y))

section CommonBlock

variable {P : Type*} [Fintype P] [Nonempty P]

/-- The one-step extraction in the greedy tiling algorithm.  If a set in a
product cube has insensitive block fibres and density greater than `2 * beta`,
then a positive-density set of outside coordinates admits one and the same
block subspace.  Pigeonholing the common template is what makes the union of
the resulting translates insensitive in the still-unused coordinates. -/
theorem exists_common_block_subspace
    {k d M : ℕ} (i : Fin k) (beta : ℝ) (hbeta : 0 < beta)
    (hblock : ∀ A : Finset (Word (k + 1) M),
      beta ≤ density A → ContainsRestrictedSubspace d
        (A : Set (Word (k + 1) M)))
    (D : Finset (P × Word (k + 1) M))
    (hD : ∀ p : P, IsLastInsensitive i
      (fiber D p : Set (Word (k + 1) M)))
    (hden : 2 * beta ≤ density D) :
    ∃ (U : Subspace (Fin d) (Fin (k + 1)) (Fin M)) (S : Finset P),
      beta / Fintype.card (Subspace (Fin d) (Fin (k + 1)) (Fin M)) ≤
        density S ∧
      ∀ p ∈ S, subspacePoints U ⊆ fiber D p := by
  classical
  let f : P → ℝ := fun p ↦ density (fiber D p)
  let T : Finset P := superlevel f beta
  have havg : 2 * beta ≤ average f := by
    rw [show average f = density D by
      simpa only [f] using (density_eq_average_fiber D).symm]
    exact hden
  have hTden : beta ≤ density T := by
    have hhalf := half_le_density_superlevel f (δ := 2 * beta)
      (by positivity) havg (fun p ↦ density_le_one (fiber D p))
    simpa only [T, show (2 * beta) / 2 = beta by ring] using hhalf
  have hTpos : 0 < density T := hbeta.trans_le hTden
  have hTne : T.Nonempty := (density_pos T).mp hTpos
  obtain ⟨p₀, hp₀⟩ := hTne
  have hex (p : P) (hp : p ∈ T) :
      ∃ U : Subspace (Fin d) (Fin (k + 1)) (Fin M),
        subspacePoints U ⊆ fiber D p := by
    have hpden : beta ≤ density (fiber D p) := by
      exact (mem_superlevel f beta p).mp hp
    obtain ⟨U, hU⟩ := (containsRestrictedSubspace_iff d).mp
      (hblock (fiber D p) hpden)
    exact ⟨U, subspacePoints_subset_of_restricted_of_isLastInsensitive
      i (fiber D p) (hD p) U hU⟩
  obtain ⟨U₀, hU₀⟩ := hex p₀ hp₀
  letI : Nonempty (Subspace (Fin d) (Fin (k + 1)) (Fin M)) := ⟨U₀⟩
  have hall : ∀ p : P, ∃ U : Subspace (Fin d) (Fin (k + 1)) (Fin M),
      p ∈ T → subspacePoints U ⊆ fiber D p := by
    intro p
    by_cases hp : p ∈ T
    · obtain ⟨U, hU⟩ := hex p hp
      exact ⟨U, fun _ ↦ hU⟩
    · exact ⟨U₀, fun hp' ↦ (hp hp').elim⟩
  choose selected hselected using hall
  obtain ⟨U, hUden⟩ := exists_dense_colorClass T selected
  let S : Finset P := colorClass T selected U
  refine ⟨U, S, ?_, ?_⟩
  · exact (div_le_div_of_nonneg_right hTden (by positivity)).trans hUden
  · intro p hp
    have hp' := (mem_colorClass T selected U p).mp hp
    rw [← hp'.2]
    exact hselected p hp'.1

end CommonBlock

section FreshBlockInvariant

variable {X B Y : Type*} [Fintype X] [Fintype B] [Fintype Y]
  [DecidableEq X] [DecidableEq B] [DecidableEq Y]

/-- Coordinate-type-polymorphic version of `LastEquivalent`. -/
def LastEquivalentOn {k : ℕ} (i : Fin k) {I : Type*}
    (x y : I → Fin (k + 1)) : Prop :=
  (fun r ↦ replaceLastLetter i (x r)) =
    (fun r ↦ replaceLastLetter i (y r))

@[refl] theorem LastEquivalentOn.refl {k : ℕ} (i : Fin k)
    {I : Type*} (x : I → Fin (k + 1)) : LastEquivalentOn i x x := rfl

theorem lastEquivalentOn_fin_iff {k n : ℕ} (i : Fin k)
    (x y : Word (k + 1) n) :
    LastEquivalentOn i x y ↔ LastEquivalent i x y := Iff.rfl

/-- A finite set is constant on the classes of a relation.  The fresh-block
argument uses this with `(i,last)`-equivalence, first on a product of unused
coordinates and then on the unused coordinates alone. -/
def IsRelationInsensitive (r : X → X → Prop) (C : Finset X) : Prop :=
  ∀ x x', r x x' → (x ∈ C ↔ x' ∈ C)

/-- Product of two equivalence relations, used for an unused prefix followed
by the current fresh block. -/
def ProductRelation (rX : X → X → Prop) (rB : B → B → Prop) :
    X × B → X × B → Prop :=
  fun z z' ↦ rX z.1 z'.1 ∧ rB z.2 z'.2

/-- Splitting a word across a sum of coordinate types identifies generic
last-equivalence with the product of the two last-equivalences. -/
theorem lastEquivalentOn_sum_iff {k : ℕ} (i : Fin k)
    {I J : Type*} (x y : (I ⊕ J) → Fin (k + 1)) :
    LastEquivalentOn i x y ↔
      ProductRelation (LastEquivalentOn (I := I) i)
        (LastEquivalentOn (I := J) i)
        (Equiv.sumArrowEquivProdArrow I J (Fin (k + 1)) x)
        (Equiv.sumArrowEquivProdArrow I J (Fin (k + 1)) y) := by
  constructor
  · intro h
    constructor <;> funext r
    · exact congrFun h (Sum.inl r)
    · exact congrFun h (Sum.inr r)
  · rintro ⟨hI, hJ⟩
    funext r
    cases r with
    | inl r => exact congrFun hI r
    | inr r => exact congrFun hJ r

/-- Freeze the already used suffix of a three-part word. -/
noncomputable def prefixSection (R : Finset ((X × B) × Y)) (y : Y) :
    Finset (X × B) := by
  classical
  exact Finset.univ.filter fun z ↦ (z, y) ∈ R

/-- Freeze the unused prefix and used suffix, leaving the current block. -/
noncomputable def middleFiber (R : Finset ((X × B) × Y))
    (x : X) (y : Y) : Finset B := by
  classical
  exact Finset.univ.filter fun b ↦ ((x, b), y) ∈ R

/-- Outside coordinates on which every point of the common block template
is still present in the remainder. -/
noncomputable def commonBlockSupport (R : Finset ((X × B) × Y))
    (V : Finset B) : Finset (X × Y) := by
  classical
  exact Finset.univ.filter fun p ↦ ∀ b ∈ V, ((p.1, b), p.2) ∈ R

/-- A support fibre in the coordinates which remain unused. -/
noncomputable def supportFiber (S : Finset (X × Y)) (y : Y) : Finset X := by
  classical
  exact Finset.univ.filter fun x ↦ (x, y) ∈ S

/-- A fibre of the remainder after both the current block and the used suffix
have been frozen. -/
noncomputable def futureFiber (R : Finset ((X × B) × Y))
    (b : B) (y : Y) : Finset X := by
  classical
  exact Finset.univ.filter fun x ↦ ((x, b), y) ∈ R

@[simp] theorem mem_prefixSection (R : Finset ((X × B) × Y))
    (y : Y) (z : X × B) : z ∈ prefixSection R y ↔ (z, y) ∈ R := by
  classical
  simp [prefixSection]

@[simp] theorem mem_middleFiber (R : Finset ((X × B) × Y))
    (x : X) (y : Y) (b : B) : b ∈ middleFiber R x y ↔ ((x, b), y) ∈ R := by
  classical
  simp [middleFiber]

@[simp] theorem mem_commonBlockSupport (R : Finset ((X × B) × Y))
    (V : Finset B) (p : X × Y) :
    p ∈ commonBlockSupport R V ↔ ∀ b ∈ V, ((p.1, b), p.2) ∈ R := by
  classical
  simp [commonBlockSupport]

@[simp] theorem mem_supportFiber (S : Finset (X × Y))
    (y : Y) (x : X) : x ∈ supportFiber S y ↔ (x, y) ∈ S := by
  classical
  simp [supportFiber]

@[simp] theorem mem_futureFiber (R : Finset ((X × B) × Y))
    (b : B) (y : Y) (x : X) : x ∈ futureFiber R b y ↔ ((x, b), y) ∈ R := by
  classical
  simp [futureFiber]

theorem commonBlockLayer_subset (R : Finset ((X × B) × Y))
    (V : Finset B) :
    commonBlockLayer (commonBlockSupport R V) V ⊆ R := by
  intro z hz
  have hz' := (mem_commonBlockLayer _ _ _).mp hz
  exact (mem_commonBlockSupport R V (z.1.1, z.2)).mp hz'.1 z.1.2 hz'.2

/-- Joint insensitivity on unused coordinates and the current block implies
insensitivity of every current-block fibre. -/
theorem IsRelationInsensitive.middleFiber
    (rX : X → X → Prop) (rB : B → B → Prop)
    (hreflX : Reflexive rX) (R : Finset ((X × B) × Y))
    (hR : ∀ y, IsRelationInsensitive (ProductRelation rX rB)
      (prefixSection R y)) (x : X) (y : Y) :
    IsRelationInsensitive rB (middleFiber R x y) := by
  intro b b' hbb'
  simpa only [mem_middleFiber, ← mem_prefixSection] using
    hR y (x, b) (x, b') ⟨hreflX x, hbb'⟩

/-- The set of unused prefixes supporting a fixed common block template is
insensitive. -/
theorem IsRelationInsensitive.supportFiber
    (rX : X → X → Prop) (rB : B → B → Prop)
    (hreflB : Reflexive rB) (R : Finset ((X × B) × Y))
    (hR : ∀ y, IsRelationInsensitive (ProductRelation rX rB)
      (prefixSection R y)) (V : Finset B) (y : Y) :
    IsRelationInsensitive rX (supportFiber (commonBlockSupport R V) y) := by
  intro x x' hxx'
  simp only [mem_supportFiber, mem_commonBlockSupport]
  constructor
  · intro hx b hb
    have hmem : (x, b) ∈ prefixSection R y := by simpa using hx b hb
    have := (hR y (x, b) (x', b) ⟨hxx', hreflB b⟩).mp hmem
    simpa using this
  · intro hx b hb
    have hmem : (x', b) ∈ prefixSection R y := by simpa using hx b hb
    have := (hR y (x, b) (x', b) ⟨hxx', hreflB b⟩).mpr hmem
    simpa using this

/-- Before subtraction, every future fibre is insensitive. -/
theorem IsRelationInsensitive.futureFiber
    (rX : X → X → Prop) (rB : B → B → Prop)
    (hreflB : Reflexive rB) (R : Finset ((X × B) × Y))
    (hR : ∀ y, IsRelationInsensitive (ProductRelation rX rB)
      (prefixSection R y)) (b : B) (y : Y) :
    IsRelationInsensitive rX (futureFiber R b y) := by
  intro x x' hxx'
  simpa only [mem_futureFiber, ← mem_prefixSection] using
    hR y (x, b) (x', b) ⟨hxx', hreflB b⟩

/-- Fresh-block preservation: after all translates of the common template
are removed, every fibre over the enlarged used suffix is still insensitive
in all coordinates which remain unused.  This is the precise invariant used
at the next greedy stage. -/
theorem IsRelationInsensitive.residual_futureFiber
    (rX : X → X → Prop) (rB : B → B → Prop)
    (hreflB : Reflexive rB) (R : Finset ((X × B) × Y))
    (hR : ∀ y, IsRelationInsensitive (ProductRelation rX rB)
      (prefixSection R y)) (V : Finset B) (b : B) (y : Y) :
    IsRelationInsensitive rX
      (Erdos171.futureFiber
        (R \ commonBlockLayer (commonBlockSupport R V) V) b y) := by
  have hold := IsRelationInsensitive.futureFiber rX rB hreflB R hR b y
  have hsupp := IsRelationInsensitive.supportFiber rX rB hreflB R hR V y
  intro x x' hxx'
  simp only [mem_futureFiber, Finset.mem_sdiff, mem_commonBlockLayer,
    mem_commonBlockSupport]
  have hold' : (((x, b), y) ∈ R ↔ ((x', b), y) ∈ R) := by
    simpa only [mem_futureFiber] using hold x x' hxx'
  have hsupp' :
      ((∀ c ∈ V, ((x, c), y) ∈ R) ↔
        ∀ c ∈ V, ((x', c), y) ∈ R) := by
    simpa only [mem_supportFiber, mem_commonBlockSupport] using
      hsupp x x' hxx'
  exact and_congr hold' (not_congr (and_congr hsupp' Iff.rfl))

end FreshBlockInvariant

section CommonFreshBlock

variable {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
  [DecidableEq X] [DecidableEq Y]

/-- Reassociate the three blocks so that the current block is the fibre
coordinate used by `exists_common_block_subspace`. -/
def outsideMiddleEquiv (B : Type*) : ((X × B) × Y) ≃ ((X × Y) × B) where
  toFun z := ((z.1.1, z.2), z.1.2)
  invFun z := ((z.1.1, z.2), z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The complete one-step form used in DKT Lemma 12.  It selects a common
subspace template in the current coordinate block, takes its full support,
and removes all corresponding translates.  The removed layer has a uniform
positive density, lies in the old remainder, and the new remainder satisfies
the fresh-block invariant. -/
theorem exists_common_block_layer
    {k d M : ℕ} (i : Fin k) (beta : ℝ) (hbeta : 0 < beta)
    (rX : X → X → Prop) (hreflX : Reflexive rX)
    (hblock : ∀ A : Finset (Word (k + 1) M),
      beta ≤ density A → ContainsRestrictedSubspace d
        (A : Set (Word (k + 1) M)))
    (R : Finset ((X × Word (k + 1) M) × Y))
    (hR : ∀ y, IsRelationInsensitive
      (ProductRelation rX (LastEquivalent i)) (prefixSection R y))
    (hden : 2 * beta ≤ density R) :
    ∃ U : Subspace (Fin d) (Fin (k + 1)) (Fin M),
      let S := commonBlockSupport R (subspacePoints U)
      let L := commonBlockLayer S (subspacePoints U)
      beta / Fintype.card (Subspace (Fin d) (Fin (k + 1)) (Fin M)) ≤
          density S ∧
        L ⊆ R ∧
        beta / Fintype.card (Subspace (Fin d) (Fin (k + 1)) (Fin M)) *
            density (subspacePoints U) ≤ density L ∧
        ∀ b y, IsRelationInsensitive rX (futureFiber (R \ L) b y) := by
  classical
  let e := outsideMiddleEquiv (X := X) (Y := Y) (Word (k + 1) M)
  let D : Finset ((X × Y) × Word (k + 1) M) := R.map e.toEmbedding
  have hDden : density D = density R := by
    simpa [D, e] using density_map_equiv e R
  have hfiber (p : X × Y) : fiber D p = middleFiber R p.1 p.2 := by
    ext b
    simp [D, e, outsideMiddleEquiv]
  have hDins : ∀ p : X × Y,
      IsLastInsensitive i (fiber D p : Set (Word (k + 1) M)) := by
    intro p
    rw [hfiber]
    exact IsRelationInsensitive.middleFiber rX (LastEquivalent i) hreflX R hR p.1 p.2
  obtain ⟨U, S₀, hS₀den, hS₀⟩ := exists_common_block_subspace
    i beta hbeta hblock D hDins (by simpa only [hDden] using hden)
  let V : Finset (Word (k + 1) M) := subspacePoints U
  let S : Finset (X × Y) := commonBlockSupport R V
  let L : Finset ((X × Word (k + 1) M) × Y) := commonBlockLayer S V
  have hS₀S : S₀ ⊆ S := by
    intro p hp
    rw [show S = commonBlockSupport R V by rfl, mem_commonBlockSupport]
    intro b hb
    have hb' : b ∈ fiber D p := hS₀ p hp (by simpa [V] using hb)
    simpa [hfiber p] using hb'
  have hSden :
      beta / Fintype.card (Subspace (Fin d) (Fin (k + 1)) (Fin M)) ≤
        density S := hS₀den.trans (density_mono hS₀S)
  have hLsub : L ⊆ R := by
    simpa [L, S] using commonBlockLayer_subset R V
  have hLprod :
      L = (S.product V).map e.symm.toEmbedding := by
    ext z
    simp [L, commonBlockLayer, e, outsideMiddleEquiv]
  have hLden : density L = density S * density V := by
    rw [hLprod, density_map_equiv]
    exact density_product S V
  refine ⟨U, ?_⟩
  dsimp only
  refine ⟨hSden, hLsub, ?_, ?_⟩
  · rw [hLden]
    exact mul_le_mul_of_nonneg_right hSden (density_nonneg V)
  · intro b y
    exact IsRelationInsensitive.residual_futureFiber rX (LastEquivalent i)
      (LastEquivalent.refl i) R hR V b y

end CommonFreshBlock

section GeometricFreshBlockStep

variable {xi upsilon : Type*}

/-- Geometric one-step producer: the common layer returned by
`exists_common_block_layer` is realized as an actual `SubspaceTiling` in the
three-block word cube. -/
theorem exists_common_block_tiling_step
    {k d M : ℕ}
    [Fintype (xi → Fin (k + 1))] [Nonempty (xi → Fin (k + 1))]
    [Fintype (upsilon → Fin (k + 1))] [Nonempty (upsilon → Fin (k + 1))]
    [DecidableEq (xi → Fin (k + 1))]
    [DecidableEq (upsilon → Fin (k + 1))]
    [Fintype (((xi ⊕ Fin M) ⊕ upsilon) → Fin (k + 1))]
    [DecidableEq (((xi ⊕ Fin M) ⊕ upsilon) → Fin (k + 1))]
    (i : Fin k) (beta : ℝ) (hbeta : 0 < beta)
    (rX : (xi → Fin (k + 1)) → (xi → Fin (k + 1)) → Prop)
    (hreflX : Reflexive rX)
    (hblock : ∀ A : Finset (Word (k + 1) M),
      beta ≤ density A → ContainsRestrictedSubspace d
        (A : Set (Word (k + 1) M)))
    (R : Finset (((xi ⊕ Fin M) ⊕ upsilon) → Fin (k + 1)))
    (hR : ∀ y, IsRelationInsensitive
      (ProductRelation rX (LastEquivalent i))
      (prefixSection (R.map splitMiddleWord.toEmbedding) y))
    (hden : 2 * beta ≤ density R) :
    ∃ (U : Subspace (Fin d) (Fin (k + 1)) (Fin M))
      (T : SubspaceTiling (Fin d) (Fin (k + 1)) ((xi ⊕ Fin M) ⊕ upsilon)),
      T.IsContainedIn R ∧
      beta / Fintype.card
          (Subspace (Fin d) (Fin (k + 1)) (Fin M)) *
          density (subspacePoints U) ≤
        density T.covered ∧
      ∀ b y, IsRelationInsensitive rX
        (futureFiber
          (R.map splitMiddleWord.toEmbedding \ T.covered.map splitMiddleWord.toEmbedding)
          b y) := by
  classical
  let D := R.map splitMiddleWord.toEmbedding
  have hDden : density D = density R := by
    simpa [D] using density_map_equiv
      (splitMiddleWord (xi := xi) (mu := Fin M) (upsilon := upsilon)
        (alpha := Fin (k + 1))) R
  obtain ⟨U, hSden, hLsub, hLden, hres⟩ := exists_common_block_layer
    i beta hbeta rX hreflX hblock D hR (by simpa only [hDden] using hden)
  let S := commonBlockSupport D (subspacePoints U)
  let T : SubspaceTiling (Fin d) (Fin (k + 1)) ((xi ⊕ Fin M) ⊕ upsilon) :=
    commonBlockTiling S U
  have hcoverImage :
      T.covered.map splitMiddleWord.toEmbedding =
        commonBlockLayer S (subspacePoints U) := by
    exact image_covered_commonBlockTiling S U
  have hTsub : T.IsContainedIn R := by
    rw [← T.covered_subset_iff]
    intro x hx
    have hxL : splitMiddleWord x ∈ commonBlockLayer S (subspacePoints U) := by
      rw [← hcoverImage]
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    have hxD : splitMiddleWord x ∈ D := hLsub hxL
    simpa [D] using hxD
  have hTden :
      beta / Fintype.card
          (Subspace (Fin d) (Fin (k + 1)) (Fin M)) *
          density (subspacePoints U) ≤ density T.covered := by
    calc
      _ ≤ density (commonBlockLayer S (subspacePoints U)) := hLden
      _ = density (T.covered.map splitMiddleWord.toEmbedding) := by rw [hcoverImage]
      _ = density T.covered := density_map_equiv splitMiddleWord T.covered
  refine ⟨U, T, hTsub, hTden, ?_⟩
  intro b y
  simpa only [D, T, hcoverImage] using hres b y

end GeometricFreshBlockStep

section BlockRecursionCoordinates

/-- Coordinates in the blocks which have not yet been processed. -/
abbrev UnusedBlockCoord (M : ℕ) : ℕ → Type
  | 0 => Fin 0
  | r + 1 => UnusedBlockCoord M r ⊕ Fin M

/-- The recursive unused-block coordinate type is finite. -/
@[instance_reducible] noncomputable def unusedBlockCoordFintype (M : ℕ) :
    ∀ r, Fintype (UnusedBlockCoord M r)
  | 0 => inferInstanceAs (Fintype (Fin 0))
  | r + 1 => by
      letI := unusedBlockCoordFintype M r
      exact inferInstanceAs (Fintype (UnusedBlockCoord M r ⊕ Fin M))

/-- Decidable equality on the recursive unused-block coordinate type. -/
@[instance_reducible] def unusedBlockCoordDecidableEq (M : ℕ) :
    ∀ r, DecidableEq (UnusedBlockCoord M r)
  | 0 => inferInstanceAs (DecidableEq (Fin 0))
  | r + 1 => by
      letI := unusedBlockCoordDecidableEq M r
      exact inferInstanceAs (DecidableEq (UnusedBlockCoord M r ⊕ Fin M))

attribute [local instance] unusedBlockCoordFintype unusedBlockCoordDecidableEq

@[simp] theorem card_unusedBlockCoord (M s : ℕ) :
    Fintype.card (UnusedBlockCoord M s) = s * M := by
  induction s with
  | zero => simp [UnusedBlockCoord]
  | succ s ih => simp [UnusedBlockCoord, ih, Nat.succ_mul]

/-- Coordinates in the blocks already processed by the greedy algorithm. -/
abbrev UsedBlockCoord (M : ℕ) : ℕ → Type
  | 0 => Fin 0
  | s + 1 => Fin M ⊕ UsedBlockCoord M s

/-- Reassociate one newly processed block from the unused side to the used
side. -/
def blockAssocEquiv (M r s : ℕ) :
    ((UnusedBlockCoord M r ⊕ Fin M) ⊕ UsedBlockCoord M s) ≃
      (UnusedBlockCoord M r ⊕ (Fin M ⊕ UsedBlockCoord M s)) where
  toFun
    | Sum.inl (Sum.inl x) => Sum.inl x
    | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
    | Sum.inr y => Sum.inr (Sum.inr y)
  invFun
    | Sum.inl x => Sum.inl (Sum.inl x)
    | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
    | Sum.inr (Sum.inr y) => Sum.inr y
  left_inv
    | Sum.inl (Sum.inl x) => rfl
    | Sum.inl (Sum.inr b) => rfl
    | Sum.inr y => rfl
  right_inv
    | Sum.inl x => rfl
    | Sum.inr (Sum.inl b) => rfl
    | Sum.inr (Sum.inr y) => rfl

/-- Freeze the used coordinate suffix of a word set. -/
noncomputable def sumSection {A C alpha : Type*}
    [Fintype (A → alpha)] (R : Finset ((A ⊕ C) → alpha))
    (y : C → alpha) : Finset (A → alpha) := by
  classical
  exact Finset.univ.filter fun x ↦ Sum.elim x y ∈ R

@[simp] theorem mem_sumSection {A C alpha : Type*}
    [Fintype (A → alpha)] (R : Finset ((A ⊕ C) → alpha))
    (y : C → alpha) (x : A → alpha) :
    x ∈ sumSection R y ↔ Sum.elim x y ∈ R := by
  classical
  simp [sumSection]

/-- The invariant at a greedy stage: after the used suffix is frozen, the
entire remaining prefix is `(i,last)`-insensitive. -/
def HasFreshBlockInvariant {k : ℕ} (i : Fin k)
    {A C : Type*} [Fintype (A → Fin (k + 1))]
    (R : Finset ((A ⊕ C) → Fin (k + 1))) : Prop :=
  ∀ y, IsRelationInsensitive (LastEquivalentOn (I := A) i) (sumSection R y)

end BlockRecursionCoordinates

section GreedyBlockRun

attribute [local instance] unusedBlockCoordFintype unusedBlockCoordDecidableEq

/-- The uniform density gained at every unsuccessful fresh-block stage. -/
noncomputable def insensitiveBlockGain (k d M : ℕ) (beta : ℝ) : ℝ :=
  beta / Fintype.card (Subspace (Fin d) (Fin (k + 1)) (Fin M)) *
    ((k + 1 : ℝ) ^ d / (k + 1 : ℝ) ^ M)

theorem density_subspacePoints_block {k d M : ℕ}
    (U : Subspace (Fin d) (Fin (k + 1)) (Fin M)) :
    density (subspacePoints U) =
      (k + 1 : ℝ) ^ d / (k + 1 : ℝ) ^ M := by
  simp [density_eq_card_div_card, card_subspacePoints_fin, Word]

/-- The finite fresh-block recursion.  Either it already leaves a remainder
of density below `2 * beta`, or its disjoint tiles occupy at least one copy of
the uniform gain for every available block. -/
theorem exists_tiling_or_density_gain
    {k d M : ℕ} (i : Fin k) (beta : ℝ) (hbeta : 0 < beta)
    (hblock : ∀ A : Finset (Word (k + 1) M),
      beta ≤ density A → ContainsRestrictedSubspace d
        (A : Set (Word (k + 1) M))) :
    ∀ (s : ℕ) {C : Type*} [Fintype C] [DecidableEq C]
      (Q : Finset ((UnusedBlockCoord M s ⊕ C) → Fin (k + 1))),
      HasFreshBlockInvariant i Q →
      ∃ T : SubspaceTiling (Fin d) (Fin (k + 1))
          (UnusedBlockCoord M s ⊕ C),
        T.IsContainedIn Q ∧
          (density (Q \ T.covered) < 2 * beta ∨
            (s : ℝ) * insensitiveBlockGain k d M beta ≤ density T.covered) := by
  intro s
  induction s with
  | zero =>
      intro C _inst _dec Q hQ
      refine ⟨SubspaceTiling.empty, ?_, Or.inr ?_⟩
      · intro U hU
        simp at hU
      · simp [insensitiveBlockGain]
  | succ s ih =>
      intro C _inst _dec Q hQ
      by_cases hsmall : density Q < 2 * beta
      · refine ⟨SubspaceTiling.empty, ?_, Or.inl ?_⟩
        · intro U hU
          simp at hU
        · simpa only [SubspaceTiling.covered_empty, Finset.sdiff_empty] using hsmall
      let D := Q.map splitMiddleWord.toEmbedding
      have hstepInv : ∀ y, IsRelationInsensitive
          (ProductRelation
            (LastEquivalentOn (I := UnusedBlockCoord M s) i)
            (LastEquivalent i)) (prefixSection D y) := by
        intro y p p' hpp'
        let x : (UnusedBlockCoord M s ⊕ Fin M) → Fin (k + 1) :=
          Sum.elim p.1 p.2
        let x' : (UnusedBlockCoord M s ⊕ Fin M) → Fin (k + 1) :=
          Sum.elim p'.1 p'.2
        have hxx' : LastEquivalentOn i x x' := by
          apply (lastEquivalentOn_sum_iff i x x').mpr
          exact ⟨hpp'.1, (lastEquivalentOn_fin_iff i p.2 p'.2).mpr hpp'.2⟩
        have hxmem := hQ y x x' hxx'
        have hxmem' : Sum.elim x y ∈ Q ↔ Sum.elim x' y ∈ Q := by
          simpa only [mem_sumSection] using hxmem
        rw [mem_prefixSection, mem_prefixSection]
        have hp : (p, y) ∈ D ↔ Sum.elim x y ∈ Q := by
          simp only [D, mem_map_equiv_toEmbedding]
          rfl
        have hp' : (p', y) ∈ D ↔ Sum.elim x' y ∈ Q := by
          simp only [D, mem_map_equiv_toEmbedding]
          rfl
        exact hp.trans (hxmem'.trans hp'.symm)
      obtain ⟨U, L, hLsub, hLgain, hres⟩ := exists_common_block_tiling_step
        i beta hbeta (LastEquivalentOn (I := UnusedBlockCoord M s) i)
          (LastEquivalentOn.refl i) hblock Q hstepInv (not_lt.mp hsmall)
      let Q₀ := Q \ L.covered
      let e := blockAssocEquiv M s 0
      -- The suffix type is arbitrary; use the same associator with `C`.
      let eC :
          ((UnusedBlockCoord M s ⊕ Fin M) ⊕ C) ≃
            (UnusedBlockCoord M s ⊕ (Fin M ⊕ C)) :=
        { toFun
            | Sum.inl (Sum.inl x) => Sum.inl x
            | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
            | Sum.inr y => Sum.inr (Sum.inr y)
          invFun
            | Sum.inl x => Sum.inl (Sum.inl x)
            | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
            | Sum.inr (Sum.inr y) => Sum.inr y
          left_inv
            | Sum.inl (Sum.inl x) => rfl
            | Sum.inl (Sum.inr b) => rfl
            | Sum.inr y => rfl
          right_inv
            | Sum.inl x => rfl
            | Sum.inr (Sum.inl b) => rfl
            | Sum.inr (Sum.inr y) => rfl }
      let Q' := Q₀.map (SubspaceTiling.ambientWordEquiv eC).toEmbedding
      have hQ'inv : HasFreshBlockInvariant i Q' := by
        intro y' x x' hxx'
        let b : Word (k + 1) M := fun r ↦ y' (Sum.inl r)
        let y : C → Fin (k + 1) := fun r ↦ y' (Sum.inr r)
        have hh := hres b y x x' hxx'
        let ew := SubspaceTiling.ambientWordEquiv
          (alpha := Fin (k + 1)) eC
        have hamb (z : UnusedBlockCoord M s → Fin (k + 1)) :
            ew.symm (Sum.elim z y') = Sum.elim (Sum.elim z b) y := by
          funext q
          rcases q with (q | q)
          · rcases q with q | q <;> rfl
          · rfl
        have hmem (z : UnusedBlockCoord M s → Fin (k + 1)) :
            Sum.elim z y' ∈ Q' ↔
              z ∈ futureFiber
                (D \ L.covered.map splitMiddleWord.toEmbedding) b y := by
          dsimp only [Q']
          rw [mem_map_equiv_toEmbedding, hamb]
          simp only [Q₀, mem_futureFiber, Finset.mem_sdiff, D,
            mem_map_equiv_toEmbedding]
          rfl
        rw [mem_sumSection, mem_sumSection]
        exact (hmem x).trans (hh.trans (hmem x').symm)
      obtain ⟨T', hT'sub, hT'out⟩ := ih (C := Fin M ⊕ C) Q' hQ'inv
      let T₀ := T'.ambientReindex eC.symm
      have hT₀contained : T₀.IsContainedIn Q₀ := by
        change (T'.ambientReindex eC.symm).IsContainedIn Q₀
        rw [SubspaceTiling.ambientReindex_isContainedIn_iff]
        simpa [Q', SubspaceTiling.ambientWordEquiv, Function.comp_def] using hT'sub
      have hT₀sub : T₀.covered ⊆ Q₀ :=
        (T₀.covered_subset_iff Q₀).mpr hT₀contained
      have hdisj : Disjoint L.covered T₀.covered := by
        rw [Finset.disjoint_left]
        intro x hxL hxT
        exact (Finset.mem_sdiff.mp (hT₀sub hxT)).2 hxL
      let T := L.disjointUnion T₀ hdisj
      have hTsub : T.IsContainedIn Q := by
        rw [← T.covered_subset_iff]
        rw [SubspaceTiling.covered_disjointUnion]
        intro x hx
        rcases Finset.mem_union.mp hx with hxL | hxT
        · exact ((L.covered_subset_iff Q).mpr hLsub) hxL
        · exact (Finset.mem_sdiff.mp (hT₀sub hxT)).1
      refine ⟨T, hTsub, ?_⟩
      rcases hT'out with hT'small | hT'gain
      · left
        have heq : density (Q₀ \ T₀.covered) =
            density (Q' \ T'.covered) := by
          have h := SubspaceTiling.density_sdiff_covered_ambientReindex
            T' eC.symm Q₀
          simpa [T₀, Q', SubspaceTiling.ambientWordEquiv,
            Function.comp_def] using h
        have hresEq : Q \ T.covered = Q₀ \ T₀.covered := by
          have hcover : T.covered = L.covered ∪ T₀.covered :=
            SubspaceTiling.covered_disjointUnion L T₀ hdisj
          rw [hcover]
          ext x
          simp only [Q₀, Finset.mem_sdiff, Finset.mem_union]
          tauto
        rw [hresEq, heq]
        exact hT'small
      · right
        have hT₀den : density T₀.covered = density T'.covered := by
          change density (T'.ambientReindex eC.symm).covered = density T'.covered
          rw [SubspaceTiling.covered_ambientReindex]
          exact density_map_equiv
            (SubspaceTiling.ambientWordEquiv eC.symm) T'.covered
        have hinter : L.covered ∩ T₀.covered = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdisj
        have hadd : density T.covered = density L.covered + density T₀.covered := by
          rw [show T.covered = L.covered ∪ T₀.covered by
            exact SubspaceTiling.covered_disjointUnion L T₀ hdisj]
          have hu := density_union_add_density_inter L.covered T₀.covered
          rw [hinter, density_empty] at hu
          linarith
        have hgain' : insensitiveBlockGain k d M beta ≤ density L.covered := by
          simpa [insensitiveBlockGain, density_subspacePoints_block U] using hLgain
        rw [hadd, hT₀den]
        push_cast
        nlinarith

end GreedyBlockRun

section OneInsensitiveTiling

attribute [local instance] unusedBlockCoordFintype unusedBlockCoordDecidableEq

/-- Dodos--Kanellopoulos--Tyros, Lemma 12, with an arbitrary lower bound on
the ambient dimension. -/
theorem FiniteRestrictedMDHJ.exists_oneInsensitiveTilingAt_ge
    {k d : ℕ} (hMDHJ : FiniteRestrictedMDHJ k d)
    {beta : ℝ} (hbeta : 0 < beta) (N : ℕ) :
    ∃ n, N ≤ n ∧ OneInsensitiveTilingAt k d n beta := by
  by_cases htriv : 1 ≤ 2 * beta
  · refine ⟨N, le_rfl, ?_⟩
    intro i D hD hden
    exact (not_lt_of_ge ((density_le_one D).trans htriv) hden).elim
  obtain ⟨M, hMpos, hblock⟩ := hMDHJ.positiveWitness beta hbeta
  have hbeta1 : beta ≤ 1 := by linarith
  obtain ⟨U, hU⟩ := hblock (Finset.univ : Finset (Word (k + 1) M))
    (by rw [density_univ]; exact hbeta1)
  letI : Nonempty (Subspace (Fin d) (Fin (k + 1)) (Fin M)) := ⟨U⟩
  let theta := insensitiveBlockGain k d M beta
  have htheta : 0 < theta := by
    dsimp only [theta, insensitiveBlockGain]
    positivity
  obtain ⟨R₀, hR₀⟩ := exists_nat_gt (1 / theta)
  let R := max R₀ N
  have hR₀R : (R₀ : ℝ) ≤ R := by
    exact_mod_cast Nat.le_max_left R₀ N
  have hRgain₀ : 1 < (R₀ : ℝ) * theta :=
    (div_lt_iff₀ htheta).mp hR₀
  have hRgain : 1 < (R : ℝ) * theta := by
    nlinarith
  have hNRM : N ≤ R * M := by
    have hNR : N ≤ R := Nat.le_max_right R₀ N
    have hRM : R ≤ R * M := by
      nlinarith [hMpos]
    exact hNR.trans hRM
  let I := UnusedBlockCoord M R ⊕ Fin 0
  have hIcard : Fintype.card I = R * M := by
    simp [I]
  let e : I ≃ Fin (R * M) := Fintype.equivFinOfCardEq hIcard
  refine ⟨R * M, hNRM, ?_⟩
  intro i D hD hDden
  let ew := SubspaceTiling.ambientWordEquiv
    (alpha := Fin (k + 1)) e
  let Q : Finset (I → Fin (k + 1)) := D.map ew.symm.toEmbedding
  have hQinv : HasFreshBlockInvariant i Q := by
    intro y x x' hxx'
    rw [mem_sumSection, mem_sumSection]
    have hsum : LastEquivalentOn i (Sum.elim x y) (Sum.elim x' y) :=
      (lastEquivalentOn_sum_iff i _ _).mpr
        ⟨hxx', LastEquivalentOn.refl i y⟩
    have hew : LastEquivalentOn i (ew (Sum.elim x y))
        (ew (Sum.elim x' y)) := by
      funext r
      exact congrFun hsum (e.symm r)
    have hmem := hD (ew (Sum.elim x y)) (ew (Sum.elim x' y))
      ((lastEquivalentOn_fin_iff i _ _).mp hew)
    simpa only [Q, mem_map_equiv_toEmbedding, Equiv.symm_symm,
      Finset.mem_coe] using hmem
  obtain ⟨T, hTsub, hout⟩ := exists_tiling_or_density_gain
    i beta hbeta hblock R (C := Fin 0) Q hQinv
  rcases hout with hsmall | hgain
  · let Tout := T.ambientReindex e
    refine ⟨Tout, ?_, ?_⟩
    · change (T.ambientReindex e).IsContainedIn D
      apply (SubspaceTiling.ambientReindex_isContainedIn_iff T e D).mpr
      simpa only [Q] using hTsub
    · change density (D \ (T.ambientReindex e).covered) < 2 * beta
      rw [SubspaceTiling.density_sdiff_covered_ambientReindex]
      simpa only [Q] using hsmall
  · have hcap := density_le_one T.covered
    exact (not_lt_of_ge hcap (hRgain.trans_le hgain)).elim

end OneInsensitiveTiling

section FiniteGreedyIteration

variable {Omega : Type*} [Fintype Omega]

end FiniteGreedyIteration

end Erdos171

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos185/DHJ/Tiling.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Almost tilings of insensitive subsets of the ternary cube

This file specializes the Dodos--Kanellopoulos--Tyros greedy tiling theorem
to the ternary cube.  The input needed by the generic tiling development is
the restricted multidimensional density theorem for the binary subalphabet;
`restricted_binary_subspace` supplies exactly that input.  The generic
finite recursion then tiles one insensitive set by subspaces, and its
intersection recursion applies this successively to two insensitive factors.

The public result preserves an arbitrary lower bound on the ambient
dimension.  It is the two-factor form used by the density-increment argument.
-/

namespace DHJ

open Combinatorics
open Erdos171

/-- The specialized restricted-subspace theorem is precisely the restricted
multidimensional density hypothesis over the binary subalphabet. -/
theorem finiteRestrictedMDHJ_binary (d : ℕ) :
    Erdos171.FiniteRestrictedMDHJ 2 d := by
  intro delta hdelta
  obtain ⟨N, hN⟩ := restricted_binary_subspace d delta hdelta
  refine ⟨N, ?_⟩
  intro A hA
  obtain ⟨U, hU⟩ := hN A hA
  rw [Erdos171.containsRestrictedSubspace_iff]
  refine ⟨U, ?_⟩
  intro x
  exact hU x

/-- DKT Corollary 13 for the intersection of one `(0,2)`-insensitive set and
one `(1,2)`-insensitive set.  The tiling dimension is exactly `d`, its ambient
dimension may be required to exceed `lower`, and the uncovered density is
strictly below `4 * beta`.

We invoke the generic two-factor theorem at the smaller error parameter
`beta / 2`.  Thus its strict density premise is implied even when the input
density is exactly `4 * beta`, and its stronger uncovered bound (`2 * beta`)
implies the stated one. -/
theorem exists_two_insensitive_tiling_dimension
    (d lower : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    ∃ N : ℕ, lower ≤ N ∧ ∀ D0 D1 : Finset (Word 3 N),
      Erdos171.IsLastInsensitive (0 : Fin 2) (D0 : Set (Word 3 N)) →
      Erdos171.IsLastInsensitive (1 : Fin 2) (D1 : Set (Word 3 N)) →
      4 * beta ≤ density (D0 ∩ D1) →
      ∃ T : Erdos171.SubspaceTiling (Fin d) (Fin 3) (Fin N),
        T.IsContainedIn (D0 ∩ D1) ∧
          density ((D0 ∩ D1) \ T.covered) < 4 * beta := by
  have hhalf : 0 < beta / 2 := by linarith
  have hone : ∀ m lower', ∃ n, lower' ≤ n ∧
      Erdos171.OneInsensitiveTilingAt 2 m n (beta / 2) := by
    intro m lower'
    exact (finiteRestrictedMDHJ_binary m).exists_oneInsensitiveTilingAt_ge
      hhalf lower'
  obtain ⟨N, hN, hinter⟩ :=
    Erdos171.exists_insensitiveIntersectionTilingAt_ge
      hhalf hone 1 d lower
  refine ⟨N, hN, ?_⟩
  intro D0 D1 hD0 hD1 hmass
  let D : Fin 2 → Finset (Word 3 N) := ![D0, D1]
  let label : Fin 2 → Fin 2 := ![0, 1]
  have hD : ∀ j, Erdos171.IsLastInsensitive (label j)
      (D j : Set (Word 3 N)) := by
    intro j
    fin_cases j
    · simpa [D, label] using hD0
    · simpa [D, label] using hD1
  have hfamily : Erdos171.familyInter D = D0 ∩ D1 := by
    ext x
    simp only [Erdos171.mem_familyInter, Finset.mem_inter]
    constructor
    · intro hx
      exact ⟨by simpa [D] using hx 0, by simpa [D] using hx 1⟩
    · rintro ⟨hx0, hx1⟩ j
      fin_cases j
      · simpa [D] using hx0
      · simpa [D] using hx1
  have hdense : 2 * (2 : ℝ) * (beta / 2) <
      density (Erdos171.familyInter D) := by
    rw [hfamily]
    linarith
  obtain ⟨T, hT, herr⟩ := hinter label D hD hdense
  refine ⟨T, ?_, ?_⟩
  · simpa only [hfamily] using hT
  · rw [hfamily] at herr
    norm_num at herr
    have herr' : density ((D0 ∩ D1) \ T.covered) < 2 * beta := by
      rw [density_eq_card_div_card, Erdos171.card_word]
      norm_num
      nlinarith [herr]
    linarith

end DHJ

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/GrahamRothschild.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The line case of the finite Graham--Rothschild theorem

This file proves the precise finite Ramsey theorem for combinatorial lines used
by Dodos--Kanellopoulos--Tyros in their proof of density Hales--Jewett.  The
proof is the standard repeated-Hales--Jewett fusion (Shelah's ``first moving
block'' proof): after passing to a block subspace, the color of a line depends
only on its first moving block.  A final pigeonhole argument makes those block
colors equal.

Only the line case is stated.  A superficially stronger statement obtained by
coloring Mathlib's *labelled* higher-dimensional `Subspace`s is false without
an ordering convention: in dimension two one may color a parameter word by
which labelled variable occurs first.  Lines have only one variable, so this
obstruction is absent here.
-/

namespace Erdos171

open Function
open Combinatorics

namespace GrahamRothschild

universe u v w x

variable {α : Type u} {P : Type v} {B : Type w} {I : Type x}

/-- A line already moves in the old (prefix) coordinates. -/
def PrefixMoving (q : Line α (P ⊕ Fin m)) : Prop :=
  ∃ p : P, q.idxFun (Sum.inl p) = none

/-- Two lines have the same first moving coordinate among their `Fin m` tail
coordinates.  This definition remains useful when either line also moves in
the prefix. -/
def SameFirstTail (q r : Line α (P ⊕ Fin m)) : Prop :=
  ∃ i : Fin m,
    q.idxFun (Sum.inr i) = none ∧
      r.idxFun (Sum.inr i) = none ∧
      ∀ j : Fin m, j < i →
        q.idxFun (Sum.inr j) ≠ none ∧ r.idxFun (Sum.inr j) ≠ none

/-- The fusion invariant.  Lines agreeing on the prefix have equal colors if
the prefix already moves, or if their first moving tail block is the same. -/
def IsFirstBlockCanonical (C : Line α I → Bool)
    (U : Subspace (P ⊕ Fin m) α I) : Prop :=
  ∀ q r : Line α (P ⊕ Fin m),
    (∀ p : P, q.idxFun (Sum.inl p) = r.idxFun (Sum.inl p)) →
    (PrefixMoving q ∨ SameFirstTail q r) →
    C (U.lineMap q) = C (U.lineMap r)

/-- Replace the current block by a word over letters and pointers into the
prefix.  The current block is the `0` coordinate of `Fin (m+1)`; all later
blocks are shifted down by one. -/
def specializeIdx (x : B → α ⊕ P) (q : Line α (P ⊕ Fin (m + 1))) :
    ((P ⊕ B) ⊕ Fin m) → Option α
  | Sum.inl (Sum.inl p) => q.idxFun (Sum.inl p)
  | Sum.inl (Sum.inr b) => (x b).elim some (fun p => q.idxFun (Sum.inl p))
  | Sum.inr j => q.idxFun (Sum.inr j.succ)

/-- The patterns for which specializing the current block still leaves a
proper line.  The only excluded case is when the current block is the unique
source of a wildcard before all later blocks. -/
def Specializable (q : Line α (P ⊕ Fin (m + 1))) : Prop :=
  PrefixMoving q ∨ q.idxFun (Sum.inr 0) ≠ none

theorem specializeIdx_proper (x : B → α ⊕ P)
    (q : Line α (P ⊕ Fin (m + 1))) (hq : Specializable q) :
    ∃ i, specializeIdx x q i = none := by
  rcases hq with hp | h0
  · obtain ⟨p, hp⟩ := hp
    exact ⟨Sum.inl (Sum.inl p), hp⟩
  · obtain ⟨i, hi⟩ := q.proper
    cases i with
    | inl p => exact ⟨Sum.inl (Sum.inl p), hi⟩
    | inr i =>
      cases i using Fin.cases with
      | zero => exact (h0 hi).elim
      | succ j => exact ⟨Sum.inr j, hi⟩

/-- Specialization as a proper line. -/
def specializeLine (x : B → α ⊕ P) (q : Line α (P ⊕ Fin (m + 1)))
    (hq : Specializable q) : Line α ((P ⊕ B) ⊕ Fin m) where
  idxFun := specializeIdx x q
  proper := specializeIdx_proper x q hq

/-- Compress a Hales--Jewett line in the current block to one new parameter
coordinate. -/
def compressSubspace (h : Line (α ⊕ P) B) :
    Subspace (P ⊕ Fin (m + 1)) α ((P ⊕ B) ⊕ Fin m) where
  idxFun
    | Sum.inl (Sum.inl p) => Sum.inr (Sum.inl p)
    | Sum.inl (Sum.inr b) =>
        (h.idxFun b).elim (Sum.inr (Sum.inr 0)) (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl))
    | Sum.inr j => Sum.inr (Sum.inr j.succ)
  proper
    | Sum.inl p => ⟨Sum.inl (Sum.inl p), rfl⟩
    | Sum.inr i => by
        cases i using Fin.cases with
        | zero =>
            obtain ⟨b, hb⟩ := h.proper
            exact ⟨Sum.inl (Sum.inr b), by simp [hb]⟩
        | succ j => exact ⟨Sum.inr j, rfl⟩

theorem compress_lineMap_eq_specialize_inl
    (h : Line (α ⊕ P) B) (q : Line α (P ⊕ Fin (m + 1)))
    (hq : Specializable q) (a : α)
    (h0 : q.idxFun (Sum.inr 0) = some a) :
    (compressSubspace (m := m) h).lineMap q =
      specializeLine (h (Sum.inl a)) q hq := by
  ext i
  cases i with
  | inl i =>
    cases i with
    | inl p => rfl
    | inr b =>
      cases hb : h.idxFun b with
      | none => simp [compressSubspace, Subspace.lineMap, specializeLine, specializeIdx, hb, h0]
      | some z =>
        cases z <;>
          simp [compressSubspace, Subspace.lineMap, specializeLine, specializeIdx, hb,
            Line.coe_apply]
  | inr j => rfl

theorem compress_lineMap_eq_specialize_inr
    (h : Line (α ⊕ P) B) (q : Line α (P ⊕ Fin (m + 1)))
    (hq : Specializable q) (p : P)
    (h0 : q.idxFun (Sum.inr 0) = q.idxFun (Sum.inl p)) :
    (compressSubspace (m := m) h).lineMap q = specializeLine (h (Sum.inr p)) q hq := by
  ext i
  cases i with
  | inl i =>
    cases i with
    | inl p' => rfl
    | inr b =>
      cases hb : h.idxFun b with
      | none => simp [compressSubspace, Subspace.lineMap, specializeLine, specializeIdx, hb, h0]
      | some z =>
        cases z <;>
          simp [compressSubspace, Subspace.lineMap, specializeLine, specializeIdx, hb,
            Line.coe_apply]
  | inr j => rfl

theorem specialize_prefix_eq (x : B → α ⊕ P)
    (q r : Line α (P ⊕ Fin (m + 1)))
    (hq : Specializable q) (hr : Specializable r)
    (hpre : ∀ p : P, q.idxFun (Sum.inl p) = r.idxFun (Sum.inl p)) :
    ∀ s : P ⊕ B,
      (specializeLine x q hq).idxFun (Sum.inl s) =
        (specializeLine x r hr).idxFun (Sum.inl s) := by
  intro s
  cases s with
  | inl p => exact hpre p
  | inr b =>
      cases hx : x b with
      | inl a => simp [specializeLine, specializeIdx, hx]
      | inr p => simpa [specializeLine, specializeIdx, hx] using hpre p

theorem specialize_prefixMoving (x : B → α ⊕ P)
    (q : Line α (P ⊕ Fin (m + 1))) (hq : Specializable q)
    (hp : PrefixMoving q) :
    PrefixMoving (P := P ⊕ B) (m := m) (specializeLine x q hq) := by
  obtain ⟨p, hp⟩ := hp
  exact ⟨Sum.inl p, hp⟩

theorem specialize_sameFirstTail_succ (x : B → α ⊕ P)
    (q r : Line α (P ⊕ Fin (m + 1)))
    (hq : Specializable q) (hr : Specializable r) (i : Fin m)
    (hqi : q.idxFun (Sum.inr i.succ) = none)
    (hri : r.idxFun (Sum.inr i.succ) = none)
    (hmin : ∀ j : Fin (m + 1), j < i.succ →
      q.idxFun (Sum.inr j) ≠ none ∧ r.idxFun (Sum.inr j) ≠ none) :
    SameFirstTail (P := P ⊕ B) (specializeLine x q hq) (specializeLine x r hr) := by
  refine ⟨i, hqi, hri, ?_⟩
  intro j hj
  exact hmin j.succ (by simpa using hj)

theorem compress_prefix_eq_of_current_none
    (h : Line (α ⊕ P) B) (q r : Line α (P ⊕ Fin (m + 1)))
    (hpre : ∀ p : P, q.idxFun (Sum.inl p) = r.idxFun (Sum.inl p))
    (hq0 : q.idxFun (Sum.inr 0) = none)
    (hr0 : r.idxFun (Sum.inr 0) = none) :
    ∀ s : P ⊕ B,
      ((compressSubspace (m := m) h).lineMap q).idxFun (Sum.inl s) =
        ((compressSubspace (m := m) h).lineMap r).idxFun (Sum.inl s) := by
  intro s
  cases s with
  | inl p => exact hpre p
  | inr b =>
      cases hb : h.idxFun b with
      | none => simp [compressSubspace, Subspace.lineMap, hb, hq0, hr0]
      | some z =>
          cases z with
          | inl a => simp [compressSubspace, Subspace.lineMap, hb]
          | inr p => simpa [compressSubspace, Subspace.lineMap, hb] using hpre p

theorem compress_prefixMoving_of_current_none
    (h : Line (α ⊕ P) B) (q : Line α (P ⊕ Fin (m + 1)))
    (hq0 : q.idxFun (Sum.inr 0) = none) :
    PrefixMoving (P := P ⊕ B) (m := m) ((compressSubspace (m := m) h).lineMap q) := by
  obtain ⟨b, hb⟩ := h.proper
  refine ⟨Sum.inr b, ?_⟩
  simp [compressSubspace, Subspace.lineMap, hb, hq0]

/-- Repeated Hales--Jewett fusion.  The returned subspace is canonical for the
first moving tail block, relative to an arbitrary finite prefix type `P`. -/
theorem exists_firstBlockCanonical (α : Type) [Finite α] (P : Type) [Finite P] :
    ∀ m : ℕ, ∃ (I : Type) (_ : Fintype I),
      ∀ C : Line α I → Bool,
        ∃ U : Subspace (P ⊕ Fin m) α I, IsFirstBlockCanonical C U := by
  classical
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite P
  intro m
  induction m generalizing P with
  | zero =>
      refine ⟨P ⊕ Fin 0, inferInstance, fun C => ⟨default, ?_⟩⟩
      intro q r hpre _
      have hqr : q = r := by
        apply Line.ext
        funext i
        cases i with
        | inl p => exact hpre p
        | inr i => exact Fin.elim0 i
      subst r
      rfl
  | succ m ih =>
      let pattern := {q : Line α (P ⊕ Fin (m + 1)) // Specializable q}
      obtain ⟨B, instB, hB⟩ :=
        Line.exists_mono_in_high_dimension (α ⊕ P) (pattern → Bool)
      letI : Fintype B := instB
      obtain ⟨I, instI, hI⟩ := ih (P := P ⊕ B)
      letI : Fintype I := instI
      refine ⟨I, instI, fun C => ?_⟩
      obtain ⟨V, hV⟩ := hI C
      let D : (B → α ⊕ P) → pattern → Bool := fun x q =>
        C (V.lineMap (specializeLine x q.1 q.2))
      obtain ⟨h, c, hc⟩ := hB D
      let Q : Subspace (P ⊕ Fin (m + 1)) α ((P ⊕ B) ⊕ Fin m) :=
        compressSubspace h
      refine ⟨V.comp Q, ?_⟩
      intro q r hpre hkey
      have hcolors (z z' : α ⊕ P) : D (h z) = D (h z') :=
        (hc z).trans (hc z').symm
      rcases hkey with hp | htail
      · obtain ⟨p, hp⟩ := hp
        have hrp : r.idxFun (Sum.inl p) = none := by rw [← hpre p]; exact hp
        have hsq : Specializable q := Or.inl ⟨p, hp⟩
        have hsr : Specializable r := Or.inl ⟨p, hrp⟩
        cases hq0 : q.idxFun (Sum.inr 0) with
        | none =>
          cases hr0 : r.idxFun (Sum.inr 0) with
          | none =>
            have hqcomp := compress_lineMap_eq_specialize_inr
              (m := m) h q hsq p (by rw [hq0, hp])
            have hrcomp := compress_lineMap_eq_specialize_inr
              (m := m) h r hsr p (by rw [hr0, hrp])
            calc
              C ((V.comp Q).lineMap q) =
                  C (V.lineMap (specializeLine (h (Sum.inr p)) q hsq)) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hqcomp]
              _ = C (V.lineMap (specializeLine (h (Sum.inr p)) r hsr)) := by
                    apply hV
                    · exact specialize_prefix_eq _ q r hsq hsr hpre
                    · exact Or.inl (specialize_prefixMoving _ q hsq ⟨p, hp⟩)
              _ = C ((V.comp Q).lineMap r) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hrcomp]
          | some b =>
            have hqcomp := compress_lineMap_eq_specialize_inr
              (m := m) h q hsq p (by rw [hq0, hp])
            have hrcomp := compress_lineMap_eq_specialize_inl
              (m := m) h r hsr b hr0
            have hmono := congrFun (hcolors (Sum.inr p) (Sum.inl b)) ⟨q, hsq⟩
            calc
              C ((V.comp Q).lineMap q) =
                  C (V.lineMap (specializeLine (h (Sum.inr p)) q hsq)) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hqcomp]
              _ = C (V.lineMap (specializeLine (h (Sum.inl b)) q hsq)) := hmono
              _ = C (V.lineMap (specializeLine (h (Sum.inl b)) r hsr)) := by
                    apply hV
                    · exact specialize_prefix_eq _ q r hsq hsr hpre
                    · exact Or.inl (specialize_prefixMoving _ q hsq ⟨p, hp⟩)
              _ = C ((V.comp Q).lineMap r) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hrcomp]
        | some a =>
          cases hr0 : r.idxFun (Sum.inr 0) with
          | none =>
            have hqcomp := compress_lineMap_eq_specialize_inl
              (m := m) h q hsq a hq0
            have hrcomp := compress_lineMap_eq_specialize_inr
              (m := m) h r hsr p (by rw [hr0, hrp])
            have hmono := congrFun (hcolors (Sum.inl a) (Sum.inr p)) ⟨q, hsq⟩
            calc
              C ((V.comp Q).lineMap q) =
                  C (V.lineMap (specializeLine (h (Sum.inl a)) q hsq)) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hqcomp]
              _ = C (V.lineMap (specializeLine (h (Sum.inr p)) q hsq)) := hmono
              _ = C (V.lineMap (specializeLine (h (Sum.inr p)) r hsr)) := by
                    apply hV
                    · exact specialize_prefix_eq _ q r hsq hsr hpre
                    · exact Or.inl (specialize_prefixMoving _ q hsq ⟨p, hp⟩)
              _ = C ((V.comp Q).lineMap r) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hrcomp]
          | some b =>
            have hqcomp := compress_lineMap_eq_specialize_inl
              (m := m) h q hsq a hq0
            have hrcomp := compress_lineMap_eq_specialize_inl
              (m := m) h r hsr b hr0
            have hmono := congrFun (hcolors (Sum.inl a) (Sum.inl b)) ⟨q, hsq⟩
            calc
              C ((V.comp Q).lineMap q) =
                  C (V.lineMap (specializeLine (h (Sum.inl a)) q hsq)) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hqcomp]
              _ = C (V.lineMap (specializeLine (h (Sum.inl b)) q hsq)) := hmono
              _ = C (V.lineMap (specializeLine (h (Sum.inl b)) r hsr)) := by
                    apply hV
                    · exact specialize_prefix_eq _ q r hsq hsr hpre
                    · exact Or.inl (specialize_prefixMoving _ q hsq ⟨p, hp⟩)
              _ = C ((V.comp Q).lineMap r) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hrcomp]
      · obtain ⟨i, hqi, hri, hmin⟩ := htail
        cases i using Fin.cases with
        | zero =>
          have hpref := compress_prefix_eq_of_current_none h q r hpre hqi hri
          have hmov := compress_prefixMoving_of_current_none h q hqi
          rw [Subspace.lineMap_comp, Subspace.lineMap_comp]
          exact hV _ _ hpref (Or.inl hmov)
        | succ i =>
          have hq0ne := (hmin 0 (by simp)).1
          have hr0ne := (hmin 0 (by simp)).2
          cases hq0 : q.idxFun (Sum.inr 0) with
          | none => exact (hq0ne hq0).elim
          | some a =>
            cases hr0 : r.idxFun (Sum.inr 0) with
            | none => exact (hr0ne hr0).elim
            | some b =>
              have hsq : Specializable q := Or.inr (by simp [hq0])
              have hsr : Specializable r := Or.inr (by simp [hr0])
              have hqcomp := compress_lineMap_eq_specialize_inl
                (m := m) h q hsq a hq0
              have hrcomp := compress_lineMap_eq_specialize_inl
                (m := m) h r hsr b hr0
              have hmono := congrFun (hcolors (Sum.inl a) (Sum.inl b)) ⟨q, hsq⟩
              calc
                C ((V.comp Q).lineMap q) =
                    C (V.lineMap (specializeLine (h (Sum.inl a)) q hsq)) := by
                      rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hqcomp]
                _ = C (V.lineMap (specializeLine (h (Sum.inl b)) q hsq)) := hmono
                _ = C (V.lineMap (specializeLine (h (Sum.inl b)) r hsr)) := by
                      apply hV
                      · exact specialize_prefix_eq _ q r hsq hsr hpre
                      · exact Or.inr (specialize_sameFirstTail_succ _ q r hsq hsr i hqi hri hmin)
                _ = C ((V.comp Q).lineMap r) := by
                      rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hrcomp]

/-- A line moving in exactly one tail coordinate. -/
def singletonTailLine (a₀ : α) (i : Fin m) : Line α (Empty ⊕ Fin m) where
  idxFun
    | Sum.inl e => nomatch e
    | Sum.inr j => if j = i then none else some a₀
  proper := ⟨Sum.inr i, by simp⟩

/-- Moving tail coordinates of a line with empty prefix. -/
def tailMoving (q : Line α (Empty ⊕ Fin m)) : Finset (Fin m) :=
  Finset.univ.filter fun i => q.idxFun (Sum.inr i) = none

theorem tailMoving_nonempty (q : Line α (Empty ⊕ Fin m)) :
    (tailMoving q).Nonempty := by
  obtain ⟨i, hi⟩ := q.proper
  cases i with
  | inl e => exact Empty.elim e
  | inr i => exact ⟨i, by simpa [tailMoving] using hi⟩

noncomputable def firstTailMoving (q : Line α (Empty ⊕ Fin m)) : Fin m :=
  (tailMoving q).min' (tailMoving_nonempty q)

theorem firstTailMoving_mem (q : Line α (Empty ⊕ Fin m)) :
    firstTailMoving q ∈ tailMoving q :=
  Finset.min'_mem _ _

theorem firstTailMoving_idxFun (q : Line α (Empty ⊕ Fin m)) :
    q.idxFun (Sum.inr (firstTailMoving q)) = none := by
  simpa [tailMoving] using firstTailMoving_mem q

theorem firstTailMoving_min (q : Line α (Empty ⊕ Fin m)) (j : Fin m)
    (hj : j < firstTailMoving q) : q.idxFun (Sum.inr j) ≠ none := by
  intro hnone
  have hjmem : j ∈ tailMoving q := by simpa [tailMoving, hnone]
  exact (not_le_of_gt hj) (Finset.min'_le _ _ hjmem)

theorem sameFirstTail_singleton (a₀ : α) (q : Line α (Empty ⊕ Fin m)) :
    SameFirstTail q (singletonTailLine a₀ (firstTailMoving q)) := by
  refine ⟨firstTailMoving q, firstTailMoving_idxFun q, by simp [singletonTailLine], ?_⟩
  intro j hj
  exact ⟨firstTailMoving_min q j hj, by simp [singletonTailLine, ne_of_lt hj]⟩

/-- Restrict a finite parameter cube to the coordinates in `s`, using the
increasing enumeration of `s` as the new parameter order. -/
noncomputable def restrictToFinset (a₀ : α) (s : Finset (Fin M))
    {d : ℕ} (hs : s.card = d) : Subspace (Fin d) α (Empty ⊕ Fin M) where
  idxFun
    | Sum.inl e => nomatch e
    | Sum.inr i => if hi : i ∈ s then
        Sum.inr ((s.orderIsoOfFin hs).symm ⟨i, hi⟩)
      else Sum.inl a₀
  proper j := by
    let i : Fin M := s.orderEmbOfFin hs j
    have hi : i ∈ s := s.orderEmbOfFin_mem hs j
    refine ⟨Sum.inr i, ?_⟩
    change (if hi' : i ∈ s then
      Sum.inr ((s.orderIsoOfFin hs).symm ⟨i, hi'⟩) else Sum.inl a₀) = Sum.inr j
    rw [dif_pos hi]
    have hsub : (⟨i, hi⟩ : s) = s.orderIsoOfFin hs j := by
      apply Subtype.ext
      rfl
    rw [hsub, (s.orderIsoOfFin hs).symm_apply_apply]

theorem restrictToFinset_moving_mem (a₀ : α) (s : Finset (Fin M))
    {d : ℕ} (hs : s.card = d) (q : Line α (Fin d)) (i : Fin M)
    (hi : ((restrictToFinset a₀ s hs).lineMap q).idxFun (Sum.inr i) = none) :
    i ∈ s := by
  by_contra his
  simp [restrictToFinset, Subspace.lineMap, his] at hi

/-- Boolean pigeonhole in the exact form used after fusion. -/
theorem exists_bool_homogeneous_finset (d : ℕ) (f : Fin (2 * d) → Bool) :
    ∃ (s : Finset (Fin (2 * d))) (c : Bool),
      s.card = d ∧ ∀ i ∈ s, f i = c := by
  classical
  let st : Finset (Fin (2 * d)) := Finset.univ.filter fun i => f i = true
  let sf : Finset (Fin (2 * d)) := Finset.univ.filter fun i => f i ≠ true
  have hsum : st.card + sf.card = 2 * d := by
    simpa [st, sf] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * d))))
        (fun i => f i = true))
  by_cases ht : d ≤ st.card
  · obtain ⟨s, hsst, hcard⟩ := Finset.exists_subset_card_eq ht
    exact ⟨s, true, hcard, fun i hi => (Finset.mem_filter.mp (hsst hi)).2⟩
  · have hf : d ≤ sf.card := by omega
    obtain ⟨s, hssf, hcard⟩ := Finset.exists_subset_card_eq hf
    refine ⟨s, false, hcard, ?_⟩
    intro i hi
    have hne : f i ≠ true := (Finset.mem_filter.mp (hssf hi)).2
    cases h : f i <;> simp_all

/-- The finite line-color Graham--Rothschild theorem, with an arbitrary finite
ambient coordinate type. -/
theorem exists_mono_lines_fintype (α : Type) [Finite α] [Nonempty α] (d : ℕ) :
    ∃ (I : Type) (_ : Fintype I), ∀ C : Line α I → Bool,
      ∃ U : Subspace (Fin d) α I, ∃ c : Bool,
        ∀ q : Line α (Fin d), C (U.lineMap q) = c := by
  classical
  obtain ⟨I, instI, hI⟩ := exists_firstBlockCanonical α Empty (2 * d)
  refine ⟨I, instI, fun C => ?_⟩
  letI : Fintype I := instI
  obtain ⟨V, hV⟩ := hI C
  let a₀ : α := Classical.arbitrary α
  let blockColor : Fin (2 * d) → Bool := fun i =>
    C (V.lineMap (singletonTailLine a₀ i))
  obtain ⟨s, c, hs, hsc⟩ := exists_bool_homogeneous_finset d blockColor
  let Q : Subspace (Fin d) α (Empty ⊕ Fin (2 * d)) := restrictToFinset a₀ s hs
  refine ⟨V.comp Q, c, ?_⟩
  intro q
  let r : Line α (Empty ⊕ Fin (2 * d)) := Q.lineMap q
  let i : Fin (2 * d) := firstTailMoving r
  have hi0 : r.idxFun (Sum.inr i) = none := firstTailMoving_idxFun r
  have his : i ∈ s := restrictToFinset_moving_mem a₀ s hs q i hi0
  have hcanon : C (V.lineMap r) = C (V.lineMap (singletonTailLine a₀ i)) := by
    apply hV
    · intro e
      exact Empty.elim e
    · exact Or.inr (sameFirstTail_singleton a₀ r)
  calc
    C ((V.comp Q).lineMap q) = C (V.lineMap r) := by
      rw [Subspace.lineMap_comp]
    _ = C (V.lineMap (singletonTailLine a₀ i)) := hcanon
    _ = blockColor i := rfl
    _ = c := hsc i his

/-- Reindex the coordinates of a line. -/
def lineReindex (e : I ≃ J) (q : Line α I) : Line α J where
  idxFun j := q.idxFun (e.symm j)
  proper := by
    obtain ⟨i, hi⟩ := q.proper
    exact ⟨e i, by simpa⟩

@[simp] theorem reindex_lineMap {η α I J : Type*}
    (e : I ≃ J) (U : Subspace η α I) (q : Line α η) :
    (U.reindex (Equiv.refl _) (Equiv.refl _) e).lineMap q =
      lineReindex e (U.lineMap q) := by
  apply Line.ext
  funext j
  cases h : U.idxFun (e.symm j) <;>
    simp [Subspace.reindex, Subspace.lineMap, lineReindex, h]

/-- Fin-indexed form of finite Graham--Rothschild for line colorings. -/
theorem exists_mono_lines_fin (α : Type) [Finite α] [Nonempty α] (d : ℕ) :
    ∃ n : ℕ, ∀ C : Line α (Fin n) → Bool,
      ∃ U : Subspace (Fin d) α (Fin n), ∃ c : Bool,
        ∀ q : Line α (Fin d), C (U.lineMap q) = c := by
  classical
  obtain ⟨I, instI, hI⟩ := exists_mono_lines_fintype α d
  letI : Fintype I := instI
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, fun C => ?_⟩
  let D : Line α I → Bool := fun q => C (lineReindex e q)
  obtain ⟨U, c, hU⟩ := hI D
  refine ⟨U.reindex (Equiv.refl _) (Equiv.refl _) e, c, ?_⟩
  intro q
  rw [reindex_lineMap]
  exact hU q

end GrahamRothschild

end Erdos171

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos185/DHJ/GrahamRothschildTwo.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Graham--Rothschild for binary combinatorial lines

This is the binary specialization of the finite line-color
Graham--Rothschild theorem.  It is the Ramsey input used in the
density-increment proof of ternary density Hales--Jewett.
-/

namespace DHJ

open Combinatorics

/-- For every target dimension, some binary cube contains a subspace on
which every internal combinatorial line has the same Boolean color. -/
theorem binary_line_homogeneous (m : ℕ) :
    ∃ N : ℕ, ∀ c : Line (Fin 2) (Fin N) → Bool,
      ∃ U : Subspace (Fin m) (Fin 2) (Fin N), ∃ b : Bool,
        ∀ l : Line (Fin 2) (Fin m), c (U.lineMap l) = b :=
  Erdos171.GrahamRothschild.exists_mono_lines_fin (Fin 2) m

end DHJ

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/IncrementArithmetic.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Arithmetic for the density-increment step in Erdős 171

This file isolates the real-number bookkeeping in the Dodos--Kanellopoulos--Tyros
proof of density Hales--Jewett.  It contains no combinatorial definitions.  The
constants are

* `theta δ q = δ / (4q)`, where `q` is the number of lines in a fixed cube;
* `eta δ θ = δθ / 48`;
* `gamma δ η k = δη² / k`.

The remaining lemmas are the numerical estimates used in Lemmas 8 and 10,
Corollary 11, and the last tiling/averaging step of that proof.
-/

namespace Erdos171.IncrementArithmetic

open scoped BigOperators

/-- The line-correlation threshold, with `q` possible line templates. -/
noncomputable def theta (δ q : ℝ) : ℝ := δ / (4 * q)

/-- The error parameter in the DKT density-increment argument. -/
noncomputable def eta (δ θ : ℝ) : ℝ := δ * θ / 48

/-- The density increment supplied by a structured set. -/
noncomputable def gamma (δ η k : ℝ) : ℝ := δ * η ^ 2 / k

theorem theta_pos {δ q : ℝ} (hδ : 0 < δ) (hq : 0 < q) :
    0 < theta δ q := by
  unfold theta
  positivity

theorem eta_pos {δ θ : ℝ} (hδ : 0 < δ) (hθ : 0 < θ) :
    0 < eta δ θ := by
  unfold eta
  positivity

theorem gamma_pos {δ η k : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hk : 0 < k) :
    0 < gamma δ η k := by
  unfold gamma
  positivity

/-- In the paper `δ ≤ 1`; this very coarse estimate is enough to make the
two large sets in Lemma 8 intersect. -/
theorem eta_lt_theta_div_two {δ θ : ℝ}
    (hδ_one : δ ≤ 1) (hθ : 0 < θ) :
    eta δ θ < θ / 2 := by
  have hmul : δ * θ ≤ θ := by
    simpa using mul_le_mul_of_nonneg_right hδ_one hθ.le
  unfold eta
  nlinarith

/-- The first branch of Corollary 11 has an increment at least `γ`. -/
theorem gamma_le_eta_sq_div_two {δ η k : ℝ}
    (_hδ_nonneg : 0 ≤ δ) (hδ_one : δ ≤ 1) (hk : 2 ≤ k) :
    gamma δ η k ≤ η ^ 2 / 2 := by
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hηsq : 0 ≤ η ^ 2 := sq_nonneg η
  have hleft : δ * η ^ 2 ≤ η ^ 2 := by
    simpa using mul_le_mul_of_nonneg_right hδ_one hηsq
  have hright : η ^ 2 ≤ (η ^ 2 / 2) * k := by
    nlinarith [mul_le_mul_of_nonneg_left hk hηsq]
  unfold gamma
  rw [div_le_iff₀ hkpos]
  exact hleft.trans hright

end Erdos171.IncrementArithmetic

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/SubspaceDensity.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Density inside combinatorial subspaces

This file connects the combinatorial `Subspace` API with the uniform-density
API used in the density Hales--Jewett argument.  Pullback density is the density
of the parameter words whose images belong to the ambient family.  Since every
proper subspace is injective in its parameter word, this is exactly relative
density inside the image of the subspace.

The second half gives two exact counting identities used repeatedly later:

* averaging the pullback densities of all fixed-suffix extensions is the
  pullback density on the corresponding sum-coordinate subspace;
* the fraction of internal lines contained in a family is both a finite
  density and the average of the corresponding containment indicator.
-/

open scoped BigOperators

namespace Erdos171

open Set

attribute [local instance 1] Classical.dec

variable {η ζ α ι κ : Type*}

/-! ## Pullback and relative density -/

/-- Pull an ambient finset back to the parameter cube of a subspace. -/
noncomputable def pullbackFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    Finset (η → α) := by
  classical
  exact Finset.univ.filter fun x ↦ U x ∈ A

@[simp] theorem mem_pullbackFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) (x : η → α) :
    x ∈ pullbackFinset U A ↔ U x ∈ A := by
  classical
  simp [pullbackFinset]

/-- Pull an ambient set back to the parameter cube, represented as a finset. -/
noncomputable def pullbackSetFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Set (ι → α)) :
    Finset (η → α) := by
  classical
  exact Finset.univ.filter fun x ↦ U x ∈ A

@[simp] theorem mem_pullbackSetFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Set (ι → α)) (x : η → α) :
    x ∈ pullbackSetFinset U A ↔ U x ∈ A := by
  classical
  simp [pullbackSetFinset]

@[simp] theorem pullback_setFinset [Fintype (η → α)] [Fintype (ι → α)]
    (U : Combinatorics.Subspace η α ι) (A : Set (ι → α)) :
    pullbackFinset U (setFinset A) = pullbackSetFinset U A := by
  classical
  ext x
  simp

/-- Density of an ambient finset when viewed in the coordinates of a subspace. -/
noncomputable def subspaceDensityFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : ℝ :=
  density (pullbackFinset U A)

/-- Density of an ambient set when viewed in the coordinates of a subspace. -/
noncomputable def subspaceDensity [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Set (ι → α)) : ℝ :=
  density (pullbackSetFinset U A)

@[simp] theorem subspaceDensity_setFinset [Fintype (η → α)] [Fintype (ι → α)]
    (U : Combinatorics.Subspace η α ι) (A : Set (ι → α)) :
    subspaceDensityFinset U (setFinset A) = subspaceDensity U A := by
  rw [subspaceDensityFinset, subspaceDensity, pullback_setFinset]

/-- The finite image of a subspace. -/
noncomputable def subspaceImageFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) : Finset (ι → α) := by
  classical
  exact Finset.univ.image U

@[simp] theorem mem_subspaceImageFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (y : ι → α) :
    y ∈ subspaceImageFinset U ↔ y ∈ Set.range U := by
  classical
  simp [subspaceImageFinset]

@[simp] theorem pullbackFinset_comp [Fintype (η → α)] [Fintype (ζ → α)]
    (U : Combinatorics.Subspace η α ι) (V : Combinatorics.Subspace ζ α η)
    (A : Finset (ι → α)) :
    pullbackFinset (U.comp V) A = pullbackFinset V (pullbackFinset U A) := by
  classical
  ext x
  simp [Combinatorics.Subspace.comp_apply]

@[simp] theorem pullbackSetFinset_comp [Fintype (η → α)] [Fintype (ζ → α)]
    (U : Combinatorics.Subspace η α ι) (V : Combinatorics.Subspace ζ α η)
    (A : Set (ι → α)) :
    pullbackSetFinset (U.comp V) A = pullbackSetFinset V (U ⁻¹' A) := by
  classical
  ext x
  simp [Combinatorics.Subspace.comp_apply]

@[simp] theorem subspaceDensityFinset_comp [Fintype (η → α)] [Fintype (ζ → α)]
    (U : Combinatorics.Subspace η α ι) (V : Combinatorics.Subspace ζ α η)
    (A : Finset (ι → α)) :
    subspaceDensityFinset (U.comp V) A =
      subspaceDensityFinset V (pullbackFinset U A) := by
  simp [subspaceDensityFinset]

@[simp] theorem subspaceDensity_comp [Fintype (η → α)] [Fintype (ζ → α)]
    (U : Combinatorics.Subspace η α ι) (V : Combinatorics.Subspace ζ α η)
    (A : Set (ι → α)) :
    subspaceDensity (U.comp V) A = subspaceDensity V (U ⁻¹' A) := by
  simp [subspaceDensity]

/-! ## Exact average over fixed-suffix extensions -/

end Erdos171

section
open Combinatorics

section
open Combinatorics.Subspace

/-- The identity combinatorial subspace. -/
private def _root_.Combinatorics.Subspace.coordinateIdentity (α η : Type*) : Subspace η α η where
  idxFun := Sum.inr
  proper e := ⟨e, rfl⟩

@[simp] private theorem _root_.Combinatorics.Subspace.coordinateIdentity_apply (x : η → α) :
    coordinateIdentity α η x = x := by
  funext e
  rfl

end

end

namespace Erdos171

open Set

attribute [local instance 1] Classical.dec

variable {η ζ α ι κ : Type*}

/-- The set of pairs `(suffix, parameter)` whose extended word lies in `A`. -/
noncomputable def extensionPullback [Fintype (κ → α)] [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α)) :
    Finset ((κ → α) × (η → α)) := by
  classical
  exact Finset.univ.filter fun p ↦
    Combinatorics.Subspace.sumWord (U p.2) p.1 ∈ A

@[simp] theorem mem_extensionPullback [Fintype (κ → α)] [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α))
    (p : (κ → α) × (η → α)) :
    p ∈ extensionPullback U A ↔
      Combinatorics.Subspace.sumWord (U p.2) p.1 ∈ A := by
  classical
  simp [extensionPullback]

/-! ## Counting internal lines -/

/-- Internal parameter lines all of whose points map into `A`. -/
noncomputable def internalLines [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    Finset (Combinatorics.Line α η) := by
  classical
  exact Finset.univ.filter fun l ↦ ∀ a, U (l a) ∈ A

@[simp] theorem mem_internalLines [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α))
    (l : Combinatorics.Line α η) :
    l ∈ internalLines U A ↔ ∀ a, U (l a) ∈ A := by
  classical
  simp [internalLines]

end Erdos171

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/Correlation.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Correlated sections and many restricted lines

This file formalizes Lemmas 7 and 8 in the Dodos--Kanellopoulos--Tyros
density-increment proof.  The key convention is that the constants are chosen
at a fixed density floor `δ₀`, while `ρ` denotes the actual density of the set
under consideration and may be larger than `δ₀`.

The first part is a purely finite averaging argument.  It says that if the
average density of a family of fibres is close to `ρ`, no fibre has a density
increment, and the average fraction of restricted internal lines is at least
`θ`, then one fibre is simultaneously dense and line-rich.  The second part
connects this statement with combinatorial subspaces and correlated tail
sections.
-/

open scoped BigOperators

namespace Erdos171

/-! ## Pure finite averaging (DKT Lemma 8) -/

/-- The strict superlevel set of a real-valued function on a finite type. -/
noncomputable def strictSuperlevel {X : Type*} [Fintype X]
    (f : X → ℝ) (c : ℝ) : Finset X :=
  Finset.univ.filter fun x ↦ c < f x

@[simp] theorem mem_strictSuperlevel {X : Type*} [Fintype X]
    (f : X → ℝ) (c : ℝ) (x : X) :
    x ∈ strictSuperlevel f c ↔ c < f x := by
  simp [strictSuperlevel]

/-! ## Restricted internal lines and tail sections -/

/-- Restricted parameter lines all of whose old-alphabet points map into
`A`.  The ambient subspace uses the enlarged alphabet `Fin (k+1)`, while the
line itself and its parameters use only `Fin k`. -/
noncomputable def restrictedInternalLines {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1))) :
    Finset (Combinatorics.Line (Fin k) η) := by
  classical
  exact Finset.univ.filter fun l ↦
    ∀ a : Fin k, U (liftWord (l a)) ∈ A

@[simp] theorem mem_restrictedInternalLines {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1)))
    (l : Combinatorics.Line (Fin k) η) :
    l ∈ restrictedInternalLines U A ↔
      ∀ a : Fin k, U (liftWord (l a)) ∈ A := by
  simp [restrictedInternalLines]

/-- Tails for which the section at a fixed parameter word belongs to `A`. -/
noncomputable def sectionTails {η ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (x : η → Fin (k + 1)) : Finset (κ → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun y ↦
    Combinatorics.Subspace.sumWord (U x) y ∈ A

@[simp] theorem mem_sectionTails {η ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (x : η → Fin (k + 1)) (y : κ → Fin (k + 1)) :
    y ∈ sectionTails U A x ↔
      Combinatorics.Subspace.sumWord (U x) y ∈ A := by
  simp [sectionTails]

@[simp] theorem sectionTails_comp {η ζ ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (V : Combinatorics.Subspace ζ (Fin (k + 1)) η)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (x : ζ → Fin (k + 1)) :
    sectionTails (U.comp V) A x = sectionTails U A (V x) := by
  ext y
  simp [Combinatorics.Subspace.comp_apply]

/-- Tails on which all old-alphabet points of a fixed restricted parameter
line belong to `A`.  This is the finite section intersection appearing in
DKT Lemma 7. -/
noncomputable def restrictedLineTails {η ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (l : Combinatorics.Line (Fin k) η) :
    Finset (κ → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun y ↦
    ∀ a : Fin k,
      Combinatorics.Subspace.sumWord (U (liftWord (l a))) y ∈ A

@[simp] theorem mem_restrictedLineTails {η ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (l : Combinatorics.Line (Fin k) η)
    (y : κ → Fin (k + 1)) :
    y ∈ restrictedLineTails U A l ↔
      ∀ a : Fin k,
        Combinatorics.Subspace.sumWord (U (liftWord (l a))) y ∈ A := by
  simp [restrictedLineTails]

/-- Old-alphabet parameter words whose images under a large-alphabet
subspace belong to `A`. -/
noncomputable def restrictedPullbackFinset {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1))) : Finset (η → Fin k) := by
  classical
  exact Finset.univ.filter fun x ↦ U (liftWord x) ∈ A

@[simp] theorem mem_restrictedPullbackFinset {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1))) (x : η → Fin k) :
    x ∈ restrictedPullbackFinset U A ↔ U (liftWord x) ∈ A := by
  simp [restrictedPullbackFinset]

/-- Restricted correlated-tail sets are natural under composition with the
lift of an old-alphabet subspace. -/
@[simp] theorem restrictedLineTails_comp_finLift
    {η ζ ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (V : Combinatorics.Subspace ζ (Fin k) η)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (l : Combinatorics.Line (Fin k) ζ) :
    restrictedLineTails (U.comp V.finLift) A l =
      restrictedLineTails U A (V.lineMap l) := by
  ext y
  simp [Combinatorics.Subspace.comp_apply,
    Combinatorics.Subspace.lineMap_apply]

/-! ## Correlated restricted lines (DKT Lemma 7) -/

/-! ## Many restricted lines from correlated sections -/

end Erdos171

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/FaceDensity.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Density of the old-alphabet face

Inside `[k+1]^m`, the words using only the first `k` letters form the image
of `[k]^m` under `liftWord`.  This file records their exact density and the
fact that this density tends to zero with the dimension.
-/

namespace Erdos171

open Filter Finset

end Erdos171

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos171/StructuredCorrelation.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The structured correlation alternative

This file formalizes Dodos--Kanellopoulos--Tyros Lemma 10 and Corollary 11.
The numerical parameters `eta` and `gamma` are frozen at an initial density
floor `delta0`, while `rho` is the density at the current stage of the
iteration.
-/

open scoped BigOperators

namespace Erdos171

attribute [local instance] Classical.dec

/-! ## Endpoint cylinders -/

/-- The old-alphabet part of a set in the enlarged cube. -/
noncomputable def oldPart {k m : ℕ} (A : Finset (Word (k + 1) m)) :
    Finset (Word k m) :=
  Finset.univ.filter fun x ↦ liftWord x ∈ A

@[simp] theorem mem_oldPart {k m : ℕ} (A : Finset (Word (k + 1) m))
    (x : Word k m) : x ∈ oldPart A ↔ liftWord x ∈ A := by
  simp [oldPart]

/-- The `(i,last)`-insensitive cylinder generated by the old part of `A`. -/
noncomputable def endpointCell {k m : ℕ} (i : Fin k)
    (A : Finset (Word (k + 1) m)) : Finset (Word (k + 1) m) :=
  setFinset (endpointCylinder i (oldPart A : Set (Word k m)))

@[simp] theorem mem_endpointCell {k m : ℕ} (i : Fin k)
    (A : Finset (Word (k + 1) m)) (x : Word (k + 1) m) :
    x ∈ endpointCell i A ↔ liftWord (endpoint i x) ∈ A := by
  simp [endpointCell]

/-- The structured endpoint set: all old-letter endpoints must lie in `A`. -/
noncomputable def endpointCore {k m : ℕ} (A : Finset (Word (k + 1) m)) :
    Finset (Word (k + 1) m) :=
  familyInter fun i : Fin k ↦ endpointCell i A

@[simp] theorem mem_endpointCore {k m : ℕ} (A : Finset (Word (k + 1) m))
    (x : Word (k + 1) m) :
    x ∈ endpointCore A ↔ ∀ i : Fin k, liftWord (endpoint i x) ∈ A := by
  simp [endpointCore]

/-- Wildcard words associated to restricted internal lines contained in `A`. -/
noncomputable def cubeRestrictedLines {k m : ℕ}
    (A : Finset (Word (k + 1) m)) :
    Finset (Combinatorics.Line (Fin k) (Fin m)) :=
  Finset.univ.filter fun l ↦ ∀ a : Fin k, liftWord (l a) ∈ A

@[simp] theorem mem_cubeRestrictedLines {k m : ℕ}
    (A : Finset (Word (k + 1) m))
    (l : Combinatorics.Line (Fin k) (Fin m)) :
    l ∈ cubeRestrictedLines A ↔ ∀ a : Fin k, liftWord (l a) ∈ A := by
  simp [cubeRestrictedLines]

noncomputable def restrictedEndpointSet {k m : ℕ}
    (A : Finset (Word (k + 1) m)) : Finset (Word (k + 1) m) :=
  (cubeRestrictedLines A).image templateEndpoint

@[simp] theorem mem_restrictedEndpointSet {k m : ℕ}
    (A : Finset (Word (k + 1) m)) (x : Word (k + 1) m) :
    x ∈ restrictedEndpointSet A ↔
      ∃ l : Combinatorics.Line (Fin k) (Fin m),
        (∀ a : Fin k, liftWord (l a) ∈ A) ∧ templateEndpoint l = x := by
  simp [restrictedEndpointSet]

/-! ## The line-free restriction -/

theorem templateEndpoint_endpointLine {k m : ℕ} (x : Word (k + 1) m)
    (hx : ∃ r, x r = Fin.last k) :
    templateEndpoint (endpointLine x hx) = x := by
  funext r
  by_cases hr : x r = Fin.last k
  · simp [endpointLine, templateEndpoint, hr]
  · simp [endpointLine, templateEndpoint, hr]

/-! ## First-failed-cell partition -/

/-- Words for which `i` is the first endpoint condition that fails. -/
noncomputable def firstFailedPiece {k m : ℕ} (A : Finset (Word (k + 1) m))
    (i : Fin k) : Finset (Word (k + 1) m) :=
  Finset.univ.filter fun x ↦
    (∀ j : Fin k, j < i → x ∈ endpointCell j A) ∧ x ∉ endpointCell i A

@[simp] theorem mem_firstFailedPiece {k m : ℕ}
    (A : Finset (Word (k + 1) m)) (i : Fin k) (x : Word (k + 1) m) :
    x ∈ firstFailedPiece A i ↔
      (∀ j : Fin k, j < i → x ∈ endpointCell j A) ∧ x ∉ endpointCell i A := by
  simp [firstFailedPiece]

/-! ## DKT Lemma 10 and Corollary 11 on a coordinate cube -/

/-! ## Transport to an arbitrary subspace and the Lemma 8 alternative -/

end Erdos171

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos185/DHJ/Correlation.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The correlation step for ternary density Hales--Jewett

This file contains the finite, quantitative part of the Dodos--Kanellopoulos--Tyros
argument which turns many binary lines into correlation with the intersection of
two insensitive sets.  The density `alpha` of the set being studied is always
kept separate from the fixed lower density floor in `CorrelationConstants`.
-/

open scoped BigOperators

namespace DHJ

open Combinatorics

/-! ## Constants -/

/-- Constants used throughout one ternary correlation argument.  In the DKT
proof `delta` is a fixed lower bound for the current density, while `theta`
comes from binary density Hales--Jewett and line counting. -/
structure CorrelationConstants where
  delta : ℝ
  theta : ℝ
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  theta_pos : 0 < theta
  theta_le_one : theta ≤ 1

namespace CorrelationConstants

/-- The uniformity error used in the correlated-section argument. -/
noncomputable def eta (p : CorrelationConstants) : ℝ := p.delta * p.theta / 48

/-- The additive correlation increment. -/
noncomputable def gamma (p : CorrelationConstants) : ℝ := p.delta * p.eta ^ 2 / 2

theorem delta_nonneg (p : CorrelationConstants) : 0 ≤ p.delta := p.delta_pos.le

theorem theta_nonneg (p : CorrelationConstants) : 0 ≤ p.theta := p.theta_pos.le

theorem eta_pos (p : CorrelationConstants) : 0 < p.eta := by
  unfold eta
  exact div_pos (mul_pos p.delta_pos p.theta_pos) (by norm_num)

theorem eta_nonneg (p : CorrelationConstants) : 0 ≤ p.eta := p.eta_pos.le

theorem eta_le_one (p : CorrelationConstants) : p.eta ≤ 1 := by
  unfold eta
  nlinarith [p.delta_pos, p.delta_le_one, p.theta_pos, p.theta_le_one]

theorem eta_lt_theta_div_two (p : CorrelationConstants) : p.eta < p.theta / 2 := by
  unfold eta
  nlinarith [p.delta_pos, p.delta_le_one, p.theta_pos]

theorem gamma_pos (p : CorrelationConstants) : 0 < p.gamma := by
  unfold gamma
  exact div_pos (mul_pos p.delta_pos (pow_pos p.eta_pos 2)) (by norm_num)

theorem gamma_nonneg (p : CorrelationConstants) : 0 ≤ p.gamma := p.gamma_pos.le

theorem gamma_le_eta_div_two (p : CorrelationConstants) : p.gamma ≤ p.eta / 2 := by
  unfold gamma
  have he0 := p.eta_nonneg
  have he1 := p.eta_le_one
  nlinarith [p.delta_nonneg, p.delta_le_one]

theorem gamma_le_eta_sq_div_two (p : CorrelationConstants) :
    p.gamma ≤ p.eta ^ 2 / 2 := by
  unfold gamma
  nlinarith [sq_nonneg p.eta, p.delta_nonneg, p.delta_le_one]

theorem eta_le_delta (p : CorrelationConstants) : p.eta ≤ p.delta := by
  unfold eta
  nlinarith [p.delta_nonneg, p.theta_nonneg, p.theta_le_one]

theorem eta_sq_div_two_le_delta_div_two (p : CorrelationConstants) :
    p.eta ^ 2 / 2 ≤ p.delta / 2 := by
  have he0 := p.eta_nonneg
  have he1 := p.eta_le_one
  have hed := p.eta_le_delta
  nlinarith

theorem twelve_eta (p : CorrelationConstants) :
    12 * p.eta = p.delta * p.theta / 4 := by
  unfold eta
  ring

end CorrelationConstants

/-- The fixed binary-DHJ witness used to choose `theta`.  A
`CorrelationSystem` is chosen once from the density floor, before any target
dimension is requested; consequently its `eta` and `gamma` are uniform over
the whole density-increment iteration. -/
structure CorrelationSystem where
  constants : CorrelationConstants
  m0 : ℕ
  m0_pos : 0 < m0
  binary_dhj : ∀ B : Finset (Word 2 m0),
    constants.delta / 4 ≤ density B → HasLine B
  theta_mul_lineCount :
    constants.theta * (Fintype.card (Line (Fin 2) (Fin m0)) : ℝ) =
      constants.delta / 4

namespace CorrelationSystem

/-- Binary density Hales--Jewett supplies one correlation system for every
positive density floor at most one. -/
theorem exists_of_delta (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∃ s : CorrelationSystem, s.constants.delta = delta := by
  obtain ⟨N, hN⟩ :=
    Erdos171.exists_containsLine_of_dense_binary_finset (delta / 4) (by positivity)
  let m0 := N + 1
  let L : ℝ := Fintype.card (Line (Fin 2) (Fin m0))
  have hm0 : 0 < m0 := by simp [m0]
  letI : Nonempty (Line (Fin 2) (Fin m0)) := by
    let l : Line (Fin 2) (Fin m0) :=
      { idxFun := fun _ ↦ none
        proper := ⟨⟨0, hm0⟩, rfl⟩ }
    exact ⟨l⟩
  have hLpos : 0 < L := by
    dsimp only [L]
    positivity
  have hLone : 1 ≤ L := by
    have hnat : 1 ≤ Fintype.card (Line (Fin 2) (Fin m0)) :=
      Fintype.card_pos_iff.mpr inferInstance
    dsimp only [L]
    exact_mod_cast hnat
  let theta := (delta / 4) / L
  have htheta : 0 < theta := by
    dsimp only [theta]
    positivity
  have htheta1 : theta ≤ 1 := by
    have hdelta4 : delta / 4 ≤ 1 := by linarith
    dsimp only [theta]
    calc
      delta / 4 / L ≤ delta / 4 / 1 := by
        exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hLone
      _ ≤ 1 := by simpa using hdelta4
  let p : CorrelationConstants :=
    { delta := delta
      theta := theta
      delta_pos := hdelta
      delta_le_one := hdelta1
      theta_pos := htheta
      theta_le_one := htheta1 }
  refine ⟨{
    constants := p
    m0 := m0
    m0_pos := hm0
    binary_dhj := ?_
    theta_mul_lineCount := ?_ }, rfl⟩
  · intro B hB
    apply (hasLine_iff_containsLine B).2
    apply hN m0 (by simp [m0]) B
    have hden : delta / 4 ≤ (B.card : ℝ) / (2 : ℝ) ^ m0 := by
      simpa [density, Word] using hB
    exact (le_div_iff₀ (by positivity)).mp hden
  · dsimp only [p]
    change theta * L = delta / 4
    dsimp only [theta]
    exact div_mul_cancel₀ _ hLpos.ne'

end CorrelationSystem

/-! ## Elementary density identities -/

section DensityLattice

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem density_sdiff_add_density_inter' (A B : Finset X) :
    density (A \ B) + density (A ∩ B) = density A := by
  simp only [density_eq_card_div_card]
  rw [← add_div, ← Nat.cast_add, Finset.card_sdiff_add_card_inter]

theorem density_union_add_density_inter' (A B : Finset X) :
    density (A ∪ B) + density (A ∩ B) = density A + density B := by
  simp only [density_eq_card_div_card]
  rw [← add_div, ← add_div, ← Nat.cast_add, ← Nat.cast_add,
    Finset.card_union_add_card_inter]

theorem density_inter_le_right' (A B : Finset X) : density (A ∩ B) ≤ density B :=
  density_mono Finset.inter_subset_right

theorem density_compl' [Nonempty X] (A : Finset X) :
    density (Finset.univ \ A) = 1 - density A := by
  have h := density_sdiff_add_density_inter' (Finset.univ : Finset X) A
  simp only [Finset.univ_inter, density_univ] at h
  linarith

end DensityLattice

/-! ## Binary lines and their ternary completion -/

section Completion

/-- Binary lines whose two binary points belong to a ternary set. -/
noncomputable def goodBinaryLines {m : ℕ} (A : Finset (Word 3 m)) :
    Finset (Line (Fin 2) (Fin m)) := by
  classical
  exact Finset.univ.filter fun l ↦
    ∀ i : Fin 2, Erdos171.restrictWord (l i) ∈ A

@[simp] theorem mem_goodBinaryLines {m : ℕ} (A : Finset (Word 3 m))
    (l : Line (Fin 2) (Fin m)) :
    l ∈ goodBinaryLines A ↔
      ∀ i : Fin 2, Erdos171.restrictWord (l i) ∈ A := by
  classical
  simp [goodBinaryLines]

/-- The canonical completion map from binary lines to ternary words is
injective: the ternary word remembers the entire line template. -/
theorem templateEndpoint_injective (m : ℕ) :
    Function.Injective
      (Erdos171.templateEndpoint : Line (Fin 2) (Fin m) → Word 3 m) := by
  intro l r hlr
  apply Line.ext
  funext i
  apply finSuccEquivLast.symm.injective
  exact congrFun hlr i

/-- The ternary words which use only the first two letters. -/
noncomputable def binaryImage (m : ℕ) : Finset (Word 3 m) := by
  classical
  exact Finset.univ.image Erdos171.restrictWord

@[simp] theorem mem_binaryImage {m : ℕ} (x : Word 3 m) :
    x ∈ binaryImage m ↔ Erdos171.IsRestrictedWord x := by
  classical
  rw [binaryImage, Finset.mem_image]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact fun i ↦ Fin.castSucc_ne_last (y i)
  · intro hx
    obtain ⟨y, rfl⟩ :=
      (Set.ext_iff.1 Erdos171.range_restrictWord x).2 hx
    exact ⟨y, Finset.mem_univ _, rfl⟩

@[simp] theorem card_binaryImage (m : ℕ) : (binaryImage m).card = 2 ^ m := by
  classical
  rw [binaryImage, Finset.card_image_of_injective _ Erdos171.restrictWord_injective]
  simp [Erdos171.card_word]

theorem density_binaryImage (m : ℕ) :
    density (binaryImage m) = (2 : ℝ) ^ m / (3 : ℝ) ^ m := by
  rw [density_eq_card_div_card, card_binaryImage]
  simp [Erdos171.card_word]

/-- Finset version of the insensitive cylinder generated by a binary set. -/
noncomputable def endpointCylinderFinset {m : ℕ} (i : Fin 2)
    (B : Finset (Word 2 m)) : Finset (Word 3 m) := by
  classical
  exact Finset.univ.filter fun x ↦ Erdos171.endpoint i x ∈ B

@[simp] theorem mem_endpointCylinderFinset {m : ℕ} (i : Fin 2)
    (B : Finset (Word 2 m)) (x : Word 3 m) :
    x ∈ endpointCylinderFinset i B ↔ Erdos171.endpoint i x ∈ B := by
  classical
  simp [endpointCylinderFinset]

theorem endpointCylinderFinset_isLastInsensitive {m : ℕ} (i : Fin 2)
    (B : Finset (Word 2 m)) :
    Erdos171.IsLastInsensitive i
      (endpointCylinderFinset i B : Set (Word 3 m)) := by
  intro x y hxy
  change (x ∈ endpointCylinderFinset i B ↔ y ∈ endpointCylinderFinset i B)
  rw [mem_endpointCylinderFinset, mem_endpointCylinderFinset]
  exact Erdos171.endpointCylinder_isLastInsensitive i
    (B : Set (Word 2 m)) x y hxy

/-- The intersection of the two endpoint cylinders attached to the binary
part of `A`. -/
noncomputable def completionCore {m : ℕ} (A : Finset (Word 3 m)) :
    Finset (Word 3 m) :=
  endpointCylinderFinset 0 (binaryPart A) ∩
    endpointCylinderFinset 1 (binaryPart A)

@[simp] theorem mem_completionCore {m : ℕ} (A : Finset (Word 3 m))
    (x : Word 3 m) :
    x ∈ completionCore A ↔
      Erdos171.restrictWord (Erdos171.endpoint 0 x) ∈ A ∧
      Erdos171.restrictWord (Erdos171.endpoint 1 x) ∈ A := by
  simp [completionCore, binaryPart]

theorem templateEndpoint_mem_completionCore_iff {m : ℕ}
    (A : Finset (Word 3 m)) (l : Line (Fin 2) (Fin m)) :
    Erdos171.templateEndpoint l ∈ completionCore A ↔ l ∈ goodBinaryLines A := by
  simp only [mem_completionCore, Erdos171.endpoint_templateEndpoint,
    mem_goodBinaryLines]
  constructor
  · intro h i
    refine Fin.cases h.1 (fun j ↦ ?_) i
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact h.2
  · intro h
    exact ⟨h 0, h 1⟩

/-- Completing good binary lines injects them into the completion core. -/
theorem card_goodBinaryLines_le_completionCore {m : ℕ}
    (A : Finset (Word 3 m)) :
    (goodBinaryLines A).card ≤ (completionCore A).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (f := Erdos171.templateEndpoint) ?_ ?_
  · intro l hl
    exact (templateEndpoint_mem_completionCore_iff A l).2 hl
  · exact (templateEndpoint_injective m).injOn

/-- Replacing the wildcards in `endpointLine x hx` by the new last letter
recovers `x`. -/
theorem templateEndpoint_endpointLine {m : ℕ} (x : Word 3 m)
    (hx : ∃ r, x r = Fin.last 2) :
    Erdos171.templateEndpoint (Erdos171.endpointLine x hx) = x :=
  Erdos171.templateEndpoint_endpointLine x hx

/-- In a line-free set, a point of the completion core that also lies in the
set must be a binary point. -/
theorem inter_completionCore_subset_binaryImage {m : ℕ}
    {A : Finset (Word 3 m)} (hline : ¬ HasLine A) :
    A ∩ completionCore A ⊆ binaryImage m := by
  intro x hx
  obtain ⟨hxA, hxCore⟩ := Finset.mem_inter.mp hx
  rw [mem_binaryImage]
  by_contra hrestricted
  simp only [Erdos171.IsRestrictedWord, not_forall, not_not] at hrestricted
  obtain ⟨r, hr⟩ := hrestricted
  have hxcore := (mem_completionCore A x).1 hxCore
  let l : Line (Fin 2) (Fin m) := Erdos171.endpointLine x ⟨r, hr⟩
  apply hline
  refine ⟨Erdos171.templateExtension l, ?_⟩
  intro a
  refine Fin.lastCases ?_ (fun i ↦ ?_) a
  · rw [Erdos171.templateExtension_last]
    simpa only [l, templateEndpoint_endpointLine x ⟨r, hr⟩] using hxA
  · rw [Erdos171.templateExtension_castSucc]
    cases i using Fin.cases with
    | zero =>
        simpa [l, Erdos171.endpointLine_apply] using hxcore.1
    | succ i =>
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simpa [l, Erdos171.endpointLine_apply] using hxcore.2

/-- Line-freeness bounds the mass of `A` in its completion core by the mass
of the binary slice. -/
theorem density_inter_completionCore_le {m : ℕ}
    {A : Finset (Word 3 m)} (hline : ¬ HasLine A) :
    density (A ∩ completionCore A) ≤ (2 : ℝ) ^ m / (3 : ℝ) ^ m := by
  calc
    density (A ∩ completionCore A) ≤ density (binaryImage m) :=
      density_mono (inter_completionCore_subset_binaryImage hline)
    _ = _ := density_binaryImage m

end Completion

/-! ## Correlated sections and the many-lines dichotomy -/

section CorrelatedSections

variable {Y : Type*} [Fintype Y] [Nonempty Y]

/-- Swap the factors of a finite subset of a product.  This local name avoids
coupling the correlation argument to the suffix-section endgame. -/
noncomputable def transposeProductFinset {X Z : Type*}
    (A : Finset (X × Z)) : Finset (Z × X) :=
  A.map (Equiv.prodComm X Z).toEmbedding

@[simp] theorem mem_transposeProductFinset {X Z : Type*}
    [DecidableEq X] [DecidableEq Z] (A : Finset (X × Z)) (z : Z) (x : X) :
    (z, x) ∈ transposeProductFinset A ↔ (x, z) ∈ A := by
  classical
  rw [transposeProductFinset, Finset.mem_map]
  constructor
  · rintro ⟨⟨x', z'⟩, hxz, heq⟩
    simp only [Equiv.coe_toEmbedding, Equiv.prodComm_apply] at heq
    cases heq
    exact hxz
  · intro hxz
    exact ⟨(x, z), hxz, rfl⟩

@[simp] theorem card_transposeProductFinset {X Z : Type*}
    [DecidableEq X] [DecidableEq Z] (A : Finset (X × Z)) :
    (transposeProductFinset A).card = A.card := by
  simp [transposeProductFinset]

/-- Section of a product set obtained by fixing its second coordinate. -/
noncomputable def tailSlice {X Z : Type*} [Fintype X]
    (A : Finset (X × Z)) (z : Z) : Finset X :=
  fiber (transposeProductFinset A) z

@[simp] theorem mem_tailSlice {X Z : Type*} [Fintype X]
    [DecidableEq Z] (A : Finset (X × Z)) (z : Z) (x : X) :
    x ∈ tailSlice A z ↔ (x, z) ∈ A := by
  classical
  rw [tailSlice, mem_fiber, mem_transposeProductFinset]

/-- Density is also the average of the sections obtained by fixing the
second product coordinate. -/
theorem density_eq_average_tailSlice {X Z : Type*}
    [Fintype X] [Nonempty X] [Fintype Z] [Nonempty Z]
    (A : Finset (X × Z)) :
    density A = average fun z : Z ↦ density (tailSlice A z) := by
  classical
  let B : Finset (Z × X) := transposeProductFinset A
  have hB : density B = density A := by
    simp [B, density, Fintype.card_prod, mul_comm]
  rw [← hB, density_eq_average_fiber]
  rfl

/-- Pull a product set back in its first coordinate through a subspace. -/
noncomputable def prefixPullbackProduct {d n : ℕ} {α Z : Type*}
    [Fintype α] [Fintype Z]
    (U : Subspace (Fin d) α (Fin n)) (A : Finset ((Fin n → α) × Z)) :
    Finset ((Fin d → α) × Z) := by
  classical
  exact Finset.univ.filter fun p ↦ (U p.1, p.2) ∈ A

@[simp] theorem mem_prefixPullbackProduct {d n : ℕ} {α Z : Type*}
    [Fintype α] [Fintype Z]
    (U : Subspace (Fin d) α (Fin n)) (A : Finset ((Fin n → α) × Z))
    (x : Fin d → α) (z : Z) :
    (x, z) ∈ prefixPullbackProduct U A ↔ (U x, z) ∈ A := by
  classical
  simp [prefixPullbackProduct]

@[simp] theorem fiber_prefixPullbackProduct {d n : ℕ} {α Z : Type*}
    [Fintype α] [Fintype Z]
    (U : Subspace (Fin d) α (Fin n)) (A : Finset ((Fin n → α) × Z))
    (x : Fin d → α) :
    fiber (prefixPullbackProduct U A) x = fiber A (U x) := by
  classical
  ext z
  simp

@[simp] theorem tailSlice_prefixPullbackProduct {d n : ℕ} {α Z : Type*}
    [Fintype α] [Fintype Z] [DecidableEq Z]
    (U : Subspace (Fin d) α (Fin n)) (A : Finset ((Fin n → α) × Z)) (z : Z) :
    tailSlice (prefixPullbackProduct U A) z =
      pullbackFinset U (tailSlice A z) := by
  classical
  ext x
  simp

@[simp] theorem finLift_apply_restrictWord {d n : ℕ}
    (U : Subspace (Fin d) (Fin 2) (Fin n)) (x : Word 2 d) :
    U.finLift (Erdos171.restrictWord x) = Erdos171.restrictWord (U x) := by
  calc
    U.finLift (Erdos171.restrictWord x) =
        U.finLift (Erdos171.liftWord x) := by rfl
    _ = Erdos171.liftWord (U x) := U.finLift_apply x
    _ = Erdos171.restrictWord (U x) := by rfl

/-- Restrict both the parameter and fixed alphabets of a binary subspace to
the binary part of a ternary product set. -/
noncomputable def binaryPrefixPullbackProduct {d n : ℕ} {Z : Type*}
    [Fintype Z]
    (U : Subspace (Fin d) (Fin 2) (Fin n)) (A : Finset (Word 3 n × Z)) :
    Finset (Word 2 d × Z) := by
  classical
  exact Finset.univ.filter fun p ↦
    (Erdos171.restrictWord (U p.1), p.2) ∈ A

@[simp] theorem mem_binaryPrefixPullbackProduct {d n : ℕ} {Z : Type*}
    [Fintype Z]
    (U : Subspace (Fin d) (Fin 2) (Fin n)) (A : Finset (Word 3 n × Z))
    (x : Word 2 d) (z : Z) :
    (x, z) ∈ binaryPrefixPullbackProduct U A ↔
      (Erdos171.restrictWord (U x), z) ∈ A := by
  classical
  simp [binaryPrefixPullbackProduct]

@[simp] theorem fiber_binaryPrefixPullbackProduct {d n : ℕ} {Z : Type*}
    [Fintype Z]
    (U : Subspace (Fin d) (Fin 2) (Fin n)) (A : Finset (Word 3 n × Z))
    (x : Word 2 d) :
    fiber (binaryPrefixPullbackProduct U A) x =
      fiber A (Erdos171.restrictWord (U x)) := by
  classical
  ext z
  simp

@[simp] theorem tailSlice_binaryPrefixPullbackProduct {d n : ℕ} {Z : Type*}
    [Fintype Z] [DecidableEq Z]
    (U : Subspace (Fin d) (Fin 2) (Fin n)) (A : Finset (Word 3 n × Z)) (z : Z) :
    tailSlice (binaryPrefixPullbackProduct U A) z =
      binaryPart (tailSlice (prefixPullbackProduct U.finLift A) z) := by
  classical
  ext x
  rw [mem_tailSlice, mem_binaryPrefixPullbackProduct]
  rw [show x ∈ binaryPart (tailSlice (prefixPullbackProduct U.finLift A) z) ↔
      Erdos171.restrictWord x ∈ tailSlice (prefixPullbackProduct U.finLift A) z by
    exact mem_restrictedPart _ _]
  rw [mem_tailSlice, mem_prefixPullbackProduct, finLift_apply_restrictWord]

/-- Tails common to the two binary endpoints of a line. -/
noncomputable def lineSectionIntersection {m : ℕ}
    (A : Finset (Word 3 m × Y)) (l : Line (Fin 2) (Fin m)) : Finset Y := by
  classical
  exact fiber A (Erdos171.restrictWord (l 0)) ∩
    fiber A (Erdos171.restrictWord (l 1))

@[simp] theorem mem_lineSectionIntersection {m : ℕ}
    (A : Finset (Word 3 m × Y)) (l : Line (Fin 2) (Fin m)) (y : Y) :
    y ∈ lineSectionIntersection A l ↔
      (Erdos171.restrictWord (l 0), y) ∈ A ∧
      (Erdos171.restrictWord (l 1), y) ∈ A := by
  simp [lineSectionIntersection]

@[simp] theorem lineSectionIntersection_prefixFinLift {m r : ℕ}
    (A : Finset (Word 3 r × Y))
    (V : Subspace (Fin m) (Fin 2) (Fin r))
    (l : Line (Fin 2) (Fin m)) :
    lineSectionIntersection (prefixPullbackProduct V.finLift A) l =
      lineSectionIntersection A (V.lineMap l) := by
  classical
  ext y
  simp only [mem_lineSectionIntersection, mem_prefixPullbackProduct,
    finLift_apply_restrictWord, Subspace.lineMap_apply]

/-- The incidence set between binary lines and tails on which both endpoints
belong to the corresponding slice. -/
noncomputable def binaryLineIncidences {m : ℕ}
    (A : Finset (Word 3 m × Y)) :
    Finset (Line (Fin 2) (Fin m) × Y) := by
  classical
  exact Finset.univ.filter fun p ↦
    p.2 ∈ lineSectionIntersection A p.1

@[simp] theorem mem_binaryLineIncidences {m : ℕ}
    (A : Finset (Word 3 m × Y)) (l : Line (Fin 2) (Fin m)) (y : Y) :
    (l, y) ∈ binaryLineIncidences A ↔
      y ∈ lineSectionIntersection A l := by
  classical
  simp [binaryLineIncidences]

@[simp] theorem fiber_binaryLineIncidences {m : ℕ}
    (A : Finset (Word 3 m × Y)) (l : Line (Fin 2) (Fin m)) :
    fiber (binaryLineIncidences A) l = lineSectionIntersection A l := by
  classical
  ext y
  simp

@[simp] theorem tailSlice_binaryLineIncidences {m : ℕ}
    (A : Finset (Word 3 m × Y)) (y : Y) :
    tailSlice (binaryLineIncidences A) y = goodBinaryLines (tailSlice A y) := by
  classical
  ext l
  rw [mem_tailSlice, mem_binaryLineIncidences, mem_goodBinaryLines]
  simp only [mem_lineSectionIntersection, mem_tailSlice]
  constructor
  · rintro ⟨h0, h1⟩ i
    refine Fin.cases h0 (fun j ↦ ?_) i
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact h1
  · intro h
    exact ⟨h 0, h 1⟩

/-- Exact double-counting identity for binary-line/tail incidences. -/
theorem average_density_lineSectionIntersection_eq {m : ℕ} (hm : 0 < m)
    (A : Finset (Word 3 m × Y)) :
    average (fun l : Line (Fin 2) (Fin m) ↦
      density (lineSectionIntersection A l)) =
    average (fun y : Y ↦ density (goodBinaryLines (tailSlice A y))) := by
  letI : Nonempty (Line (Fin 2) (Fin m)) := by
    let l : Line (Fin 2) (Fin m) :=
      { idxFun := fun _ ↦ none
        proper := ⟨⟨0, hm⟩, rfl⟩ }
    exact ⟨l⟩
  have hleft := density_eq_average_fiber (binaryLineIncidences A)
  have hright := density_eq_average_tailSlice (binaryLineIncidences A)
  simp only [fiber_binaryLineIncidences] at hleft
  simp only [tailSlice_binaryLineIncidences] at hright
  linarith

/-- Abstract product form of the correlated-sections conclusion.  This is the
form consumed by the many-lines averaging argument and produced by the tower
uniformization/Ramsey construction. -/
structure CorrelatedSectionData (p : CorrelationConstants) (alpha : ℝ)
    (m : ℕ) (Y : Type*) [Fintype Y] where
  points : Finset (Word 3 m × Y)
  section_dense : ∀ u : Word 3 m,
    alpha - p.eta ^ 2 / 2 ≤ density (fiber points u)
  line_dense : ∀ l : Line (Fin 2) (Fin m),
    p.theta ≤ density (lineSectionIntersection points l)

/-- Graham--Rothschild homogenization plus the fixed binary-DHJ witness turn
uniform point sections into correlated line sections.  The returned binary
subspace records the prefix embedding, which is needed later to transport a
selected tail slice back into the ambient cube. -/
theorem exists_correlatedSectionData_of_uniform
    (s : CorrelationSystem) {alpha : ℝ} {m r : ℕ} (hm : s.m0 ≤ m)
    (A : Finset (Word 3 r × Y))
    (hfloor : s.constants.delta ≤ alpha)
    (huniform : ∀ x : Word 3 r,
      alpha - s.constants.eta ^ 2 / 2 ≤ density (fiber A x))
    (hGR : ∀ c : Line (Fin 2) (Fin r) → Bool,
      ∃ V : Subspace (Fin m) (Fin 2) (Fin r), ∃ b : Bool,
        ∀ l : Line (Fin 2) (Fin m), c (V.lineMap l) = b) :
    ∃ V : Subspace (Fin m) (Fin 2) (Fin r),
      ∃ S : CorrelatedSectionData s.constants alpha m Y,
        S.points = prefixPullbackProduct V.finLift A := by
  classical
  let p := s.constants
  let color : Line (Fin 2) (Fin r) → Bool := fun l ↦
    decide (p.theta ≤ density (lineSectionIntersection A l))
  obtain ⟨V, b, hV⟩ := hGR color
  have hb : b = true := by
    cases b with
    | true => rfl
    | false =>
      exfalso
      let F : Subspace (Fin s.m0) (Fin 2) (Fin m) :=
        Subspace.coordinateFace hm
      let Z : Subspace (Fin s.m0) (Fin 2) (Fin r) := V.comp F
      let Q : Finset (Word 2 s.m0 × Y) := binaryPrefixPullbackProduct Z A
      have hQ : p.delta / 2 ≤ density Q := by
        rw [density_eq_average_fiber]
        apply const_le_average
        intro x
        rw [fiber_binaryPrefixPullbackProduct]
        have hx := huniform (Erdos171.restrictWord (Z x))
        have herror := p.eta_sq_div_two_le_delta_div_two
        dsimp only [p] at hx herror ⊢
        nlinarith
      have hQavg : p.delta / 2 ≤
          average fun y : Y ↦ density (tailSlice Q y) := by
        rwa [← density_eq_average_tailSlice]
      let H : Finset Y := superlevel
        (fun y : Y ↦ density (tailSlice Q y)) (p.delta / 4)
      have hH : p.delta / 4 ≤ density H := by
        have hh := half_le_density_superlevel
          (fun y : Y ↦ density (tailSlice Q y))
          (show 0 ≤ p.delta / 2 from
            div_nonneg p.delta_nonneg (by norm_num)) hQavg
          (fun y ↦ density_le_one (tailSlice Q y))
        simpa only [H, show p.delta / 2 / 2 = p.delta / 4 by ring] using hh
      let PZ : Finset (Word 3 s.m0 × Y) := prefixPullbackProduct Z.finLift A
      let L : ℝ := Fintype.card (Line (Fin 2) (Fin s.m0))
      letI : Nonempty (Line (Fin 2) (Fin s.m0)) := by
        let l : Line (Fin 2) (Fin s.m0) :=
          { idxFun := fun _ ↦ none
            proper := ⟨⟨0, s.m0_pos⟩, rfl⟩ }
        exact ⟨l⟩
      have hLpos : 0 < L := by
        have hnat : 0 < Fintype.card (Line (Fin 2) (Fin s.m0)) := Fintype.card_pos
        dsimp only [L]
        exact_mod_cast hnat
      have hpointGood (y : Y) :
          (if y ∈ H then 1 / L else 0) ≤
            density (goodBinaryLines (tailSlice PZ y)) := by
        by_cases hy : y ∈ H
        · rw [if_pos hy]
          have hQy : p.delta / 4 ≤ density (tailSlice Q y) := by
            exact (mem_superlevel _ _ y).1 hy
          have hlineQ : HasLine (tailSlice Q y) := by
            apply s.binary_dhj
            simpa only [p] using hQy
          rw [tailSlice_binaryPrefixPullbackProduct Z A y] at hlineQ
          obtain ⟨l, hl⟩ := hlineQ
          have hlGood : l ∈ goodBinaryLines (tailSlice PZ y) := by
            apply (mem_goodBinaryLines _ l).2
            intro i
            exact (mem_restrictedPart _ (l i)).1 (hl i)
          have hcard : 1 ≤ (goodBinaryLines (tailSlice PZ y)).card :=
            Finset.one_le_card.mpr ⟨l, hlGood⟩
          rw [density_eq_card_div_card]
          change 1 / L ≤ ((goodBinaryLines (tailSlice PZ y)).card : ℝ) / L
          exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hLpos.le
        · rw [if_neg hy]
          exact density_nonneg _
      have havgGoodLower : density H / L ≤
          average fun y : Y ↦ density (goodBinaryLines (tailSlice PZ y)) := by
        calc
          density H / L =
              average (fun y : Y ↦ if y ∈ H then 1 / L else 0) := by
            rw [average_piecewise_const]
            ring
          _ ≤ _ := average_mono hpointGood
      have hthetaH : p.theta ≤ density H / L := by
        rw [le_div_iff₀ hLpos]
        have hcount := s.theta_mul_lineCount
        change p.theta * L = p.delta / 4 at hcount
        linarith
      have havgGood : p.theta ≤
          average fun y : Y ↦ density (goodBinaryLines (tailSlice PZ y)) :=
        hthetaH.trans havgGoodLower
      have havgInter : p.theta ≤
          average fun l : Line (Fin 2) (Fin s.m0) ↦
            density (lineSectionIntersection PZ l) := by
        rw [average_density_lineSectionIntersection_eq s.m0_pos PZ]
        exact havgGood
      obtain ⟨l, hl⟩ := exists_average_le
        (fun l : Line (Fin 2) (Fin s.m0) ↦
          density (lineSectionIntersection PZ l))
      have hgoodZ : p.theta ≤
          density (lineSectionIntersection A (Z.lineMap l)) := by
        have := havgInter.trans hl
        simpa only [PZ, lineSectionIntersection_prefixFinLift] using this
      have hhom := hV (F.lineMap l)
      have hfalse :
          decide (p.theta ≤
            density (lineSectionIntersection A (V.lineMap (F.lineMap l)))) = false := by
        simpa only [color] using hhom
      have hbad : ¬p.theta ≤
          density (lineSectionIntersection A (V.lineMap (F.lineMap l))) :=
        of_decide_eq_false hfalse
      apply hbad
      simpa only [Z, Subspace.lineMap_comp] using hgoodZ
  let P : Finset (Word 3 m × Y) := prefixPullbackProduct V.finLift A
  let S : CorrelatedSectionData p alpha m Y :=
    { points := P
      section_dense := by
        intro x
        dsimp only [P]
        rw [fiber_prefixPullbackProduct]
        exact huniform (V.finLift x)
      line_dense := by
        intro l
        dsimp only [P]
        rw [lineSectionIntersection_prefixFinLift]
        have hc := hV l
        rw [hb] at hc
        exact of_decide_eq_true (by simpa only [color] using hc) }
  exact ⟨V, S, rfl⟩

/-- The DKT many-lines dichotomy in a product cube.  Either one tail slice
already has the desired `eta²/2` increment over the actual density `alpha`,
or one tail simultaneously has density at least `alpha-2 eta` and contains a
`theta/2` fraction of all binary lines. -/
theorem manyBinaryLines_of_correlatedSections (p : CorrelationConstants)
    {alpha : ℝ} {m : ℕ} (hm : 0 < m)
    (S : CorrelatedSectionData p alpha m Y) :
    (∃ y : Y, alpha + p.eta ^ 2 / 2 ≤ density (tailSlice S.points y)) ∨
      ∃ y : Y,
        alpha - 2 * p.eta ≤ density (tailSlice S.points y) ∧
        p.theta / 2 ≤ density (goodBinaryLines (tailSlice S.points y)) := by
  classical
  letI : Nonempty (Word 3 m) := inferInstance
  letI : Nonempty (Line (Fin 2) (Fin m)) := by
    let l : Line (Fin 2) (Fin m) :=
      { idxFun := fun _ ↦ none
        proper := ⟨⟨0, hm⟩, rfl⟩ }
    exact ⟨l⟩
  by_cases hinc : ∃ y : Y,
      alpha + p.eta ^ 2 / 2 ≤ density (tailSlice S.points y)
  · exact Or.inl hinc
  · right
    push_neg at hinc
    have hdensePoints : alpha - p.eta ^ 2 / 2 ≤ density S.points := by
      rw [density_eq_average_fiber]
      exact const_le_average S.section_dense
    have havgSlices : alpha - p.eta ^ 2 / 2 ≤
        average fun y : Y ↦ density (tailSlice S.points y) := by
      rwa [← density_eq_average_tailSlice]
    let H1 : Finset Y := superlevel
      (fun y : Y ↦ density (tailSlice S.points y)) (alpha - 2 * p.eta)
    have hH1raw :
        ((alpha - p.eta ^ 2 / 2) - (alpha - 2 * p.eta)) /
            ((alpha + p.eta ^ 2 / 2) - (alpha - 2 * p.eta)) ≤
          density H1 := by
      apply density_superlevel_ge
      · exact havgSlices
      · intro y
        exact (hinc y).le
      · have := p.eta_pos
        nlinarith
    have hratio :
        1 - p.eta ≤
          ((alpha - p.eta ^ 2 / 2) - (alpha - 2 * p.eta)) /
            ((alpha + p.eta ^ 2 / 2) - (alpha - 2 * p.eta)) := by
      rw [le_div_iff₀]
      · have he0 := p.eta_pos
        have he1 := p.eta_le_one
        nlinarith [sq_nonneg p.eta]
      · have := p.eta_pos
        nlinarith
    have hH1 : 1 - p.eta ≤ density H1 := hratio.trans hH1raw
    have havgLines : p.theta ≤
        average fun y : Y ↦ density (goodBinaryLines (tailSlice S.points y)) := by
      rw [← average_density_lineSectionIntersection_eq hm S.points]
      exact const_le_average S.line_dense
    let H2 : Finset Y := superlevel
      (fun y : Y ↦ density (goodBinaryLines (tailSlice S.points y)))
        (p.theta / 2)
    have hH2 : p.theta / 2 ≤ density H2 := by
      exact half_le_density_superlevel
        (fun y : Y ↦ density (goodBinaryLines (tailSlice S.points y)))
        p.theta_nonneg havgLines (fun y ↦ density_le_one _)
    have hinterLower : density H1 + density H2 - 1 ≤ density (H1 ∩ H2) := by
      have hu := density_union_add_density_inter' H1 H2
      have hule := density_le_one (H1 ∪ H2)
      linarith
    have hinterPos : 0 < density (H1 ∩ H2) := by
      have heta := p.eta_lt_theta_div_two
      linarith
    have hinterNonempty : (H1 ∩ H2).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty, density_empty] at hinterPos
      exact lt_irrefl 0 hinterPos
    obtain ⟨y, hy⟩ := hinterNonempty
    obtain ⟨hy1, hy2⟩ := Finset.mem_inter.mp hy
    refine ⟨y, ?_, ?_⟩
    · exact (mem_superlevel _ _ y).1 hy1
    · exact (mem_superlevel _ _ y).1 hy2

end CorrelatedSections

/-! ## The excess decomposition -/

section Excess

variable {m : ℕ}

/-- The output of the correlation step in a standard ternary parameter cube. -/
structure InsensitiveCorrelation (p : CorrelationConstants)
    (alpha : ℝ) (A : Finset (Word 3 m)) where
  first : Finset (Word 3 m)
  second : Finset (Word 3 m)
  first_insensitive :
    Erdos171.IsLastInsensitive 0 (first : Set (Word 3 m))
  second_insensitive :
    Erdos171.IsLastInsensitive 1 (second : Set (Word 3 m))
  mass : p.gamma ≤ density (first ∩ second)
  correlated :
    (alpha + p.gamma) * density (first ∩ second) ≤
      density (A ∩ (first ∩ second))

theorem isLastInsensitive_univ (i : Fin 2) :
    Erdos171.IsLastInsensitive i (Set.univ : Set (Word 3 m)) := by
  intro x y _
  simp

theorem isLastInsensitive_finset_compl (i : Fin 2)
    (C : Finset (Word 3 m))
    (hC : Erdos171.IsLastInsensitive i (C : Set (Word 3 m))) :
    Erdos171.IsLastInsensitive i
      ((Finset.univ \ C : Finset (Word 3 m)) : Set (Word 3 m)) := by
  have hcoe :
      (((Finset.univ \ C : Finset (Word 3 m)) : Set (Word 3 m))) =
        (C : Set (Word 3 m))ᶜ := by
    ext x
    simp
  rw [hcoe]
  exact hC.compl

/-- An increment on the whole parameter cube is already an insensitive
correlation, using the whole cube for both insensitive factors. -/
theorem insensitiveCorrelation_of_increment (p : CorrelationConstants)
    {alpha : ℝ} {A : Finset (Word 3 m)}
    (hinc : alpha + p.gamma ≤ density A) :
    Nonempty (InsensitiveCorrelation p alpha A) := by
  refine ⟨
    { first := Finset.univ
      second := Finset.univ
      first_insensitive := by simpa using (isLastInsensitive_univ 0)
      second_insensitive := by simpa using (isLastInsensitive_univ 1)
      mass := ?_
      correlated := ?_ }⟩
  · have hhalf : p.gamma ≤ p.eta / 2 := p.gamma_le_eta_div_two
    have heta : p.eta / 2 ≤ 1 := by linarith [p.eta_le_one]
    simpa using hhalf.trans heta
  · simpa using hinc

/-- The direct-increment alternative in the DKT dichotomy implies the
correlation conclusion because `gamma ≤ eta²/2`. -/
theorem insensitiveCorrelation_of_eta_increment (p : CorrelationConstants)
    {alpha : ℝ} {A : Finset (Word 3 m)}
    (hinc : alpha + p.eta ^ 2 / 2 ≤ density A) :
    Nonempty (InsensitiveCorrelation p alpha A) := by
  apply insensitiveCorrelation_of_increment p
  nlinarith [p.gamma_le_eta_sq_div_two]

/-- A quantitative lower bound for the completion core obtained from many
good binary lines.  The power hypothesis is the only dimension estimate used
here; later modules arrange it by choosing the parameter dimension large. -/
theorem density_completionCore_ge_of_many_lines (p : CorrelationConstants)
    {A : Finset (Word 3 m)}
    (hmany : p.theta / 2 * ((3 : ℝ) ^ m - (2 : ℝ) ^ m) ≤
      ((goodBinaryLines A).card : ℝ))
    (hpow : 2 * (2 : ℝ) ^ m ≤ (3 : ℝ) ^ m) :
    p.theta / 4 ≤ density (completionCore A) := by
  have hcardNat := card_goodBinaryLines_le_completionCore A
  have hcard : ((goodBinaryLines A).card : ℝ) ≤
      ((completionCore A).card : ℝ) := by exact_mod_cast hcardNat
  have hthree : 0 < (3 : ℝ) ^ m := by positivity
  rw [density_eq_card_div_card]
  simp only [Erdos171.card_word, Nat.cast_pow, Nat.cast_ofNat]
  rw [le_div_iff₀ hthree]
  have htheta := p.theta_nonneg
  nlinarith

/-- Pure finite-probability heart of the correlation argument.  The sets
`C0,C1` are the two insensitive endpoint cylinders.  If their intersection
has noticeable mass but contains little of `A`, then one of the two disjoint
pieces of its complement has positive excess over density `alpha + gamma`. -/
theorem insensitiveCorrelation_of_core (p : CorrelationConstants)
    {alpha : ℝ} {A C0 C1 : Finset (Word 3 m)}
    (hfloor : p.delta ≤ alpha)
    (hA : alpha - 2 * p.eta ≤ density A)
    (hC0 : Erdos171.IsLastInsensitive 0 (C0 : Set (Word 3 m)))
    (hC1 : Erdos171.IsLastInsensitive 1 (C1 : Set (Word 3 m)))
    (hC : p.theta / 4 ≤ density (C0 ∩ C1))
    (hAC : density (A ∩ (C0 ∩ C1)) ≤ p.eta) :
    Nonempty (InsensitiveCorrelation p alpha A) := by
  classical
  let P0 : Finset (Word 3 m) := Finset.univ \ C0
  let P1 : Finset (Word 3 m) := C0 \ C1
  let C : Finset (Word 3 m) := C0 ∩ C1
  have hPdisj : Disjoint P0 P1 := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    simp only [P0, P1, Finset.mem_sdiff, Finset.mem_univ, true_and] at hx0 hx1
    exact hx0 hx1.1
  have hPunion : P0 ∪ P1 = Finset.univ \ C := by
    ext x
    simp only [P0, P1, C, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_inter]
    tauto
  have hAPdisj : Disjoint (A ∩ P0) (A ∩ P1) := by
    exact hPdisj.mono Finset.inter_subset_right Finset.inter_subset_right
  have hAPunion : (A ∩ P0) ∪ (A ∩ P1) = A \ C := by
    ext x
    simp only [P0, P1, C, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    tauto
  have hsumP : density P0 + density P1 = density (Finset.univ \ C) := by
    have hu := density_union_add_density_inter' P0 P1
    have hi : P0 ∩ P1 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hPdisj
    rw [hi, density_empty, add_zero, hPunion] at hu
    linarith
  have hsumAP : density (A ∩ P0) + density (A ∩ P1) = density (A \ C) := by
    have hu := density_union_add_density_inter' (A ∩ P0) (A ∩ P1)
    have hi : (A ∩ P0) ∩ (A ∩ P1) = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hAPdisj
    rw [hi, density_empty, add_zero, hAPunion] at hu
    linarith
  have hsdiffA := density_sdiff_add_density_inter' A C
  have hsdiffU := density_compl' C
  have hAC' : density (A ∩ C) ≤ p.eta := by simpa [C] using hAC
  have hC' : p.theta / 4 ≤ density C := by simpa [C] using hC
  have hcoeff : 0 ≤ alpha + p.gamma := by
    linarith [p.delta_pos, p.gamma_pos]
  have hprodC :
      (alpha + p.gamma) * (p.theta / 4) ≤
        (alpha + p.gamma) * density C :=
    mul_le_mul_of_nonneg_left hC' hcoeff
  have hfloorProd :
      (p.delta + p.gamma) * (p.theta / 4) ≤
        (alpha + p.gamma) * (p.theta / 4) := by
    have hsum : p.delta + p.gamma ≤ alpha + p.gamma := by linarith
    exact mul_le_mul_of_nonneg_right hsum
      (div_nonneg p.theta_nonneg (by norm_num))
  let e0 : ℝ := density (A ∩ P0) - (alpha + p.gamma) * density P0
  let e1 : ℝ := density (A ∩ P1) - (alpha + p.gamma) * density P1
  have hexcess : 2 * p.gamma ≤ e0 + e1 := by
    have hgammaEta := p.gamma_le_eta_div_two
    have htwelve := p.twelve_eta
    have hdiff : alpha - 3 * p.eta ≤ density (A \ C) := by
      linarith
    have hprodDelta :
        p.delta * p.theta / 4 ≤ (alpha + p.gamma) * density C := by
      calc
        p.delta * p.theta / 4 ≤
            (p.delta + p.gamma) * (p.theta / 4) := by
              have hnonneg : 0 ≤ p.gamma * (p.theta / 4) :=
                mul_nonneg p.gamma_nonneg
                  (div_nonneg p.theta_nonneg (by norm_num))
              nlinarith
        _ ≤ (alpha + p.gamma) * (p.theta / 4) := hfloorProd
        _ ≤ (alpha + p.gamma) * density C := hprodC
    have hprodEta :
        12 * p.eta ≤ (alpha + p.gamma) * density C := by
      linarith
    have hdiff' : -3 * p.eta ≤ density (A \ C) - alpha := by
      linarith
    have hgamma3 : 3 * p.gamma ≤ 9 * p.eta := by
      linarith [p.eta_pos]
    dsimp only [e0, e1]
    rw [sub_add_sub_comm, hsumAP, ← mul_add, hsumP, hsdiffU]
    rw [show density (A \ C) - (alpha + p.gamma) * (1 - density C) =
        density (A \ C) - alpha - p.gamma +
          (alpha + p.gamma) * density C by ring]
    linarith
  have hchoice : p.gamma ≤ e0 ∨ p.gamma ≤ e1 := by
    by_cases h0 : p.gamma ≤ e0
    · exact Or.inl h0
    · right
      exact le_of_lt (by linarith)
  rcases hchoice with he0 | he1
  · have hP0mass : p.gamma ≤ density P0 := by
      have hinter := density_inter_le_right' A P0
      have hsubnonneg : 0 ≤ (alpha + p.gamma) * density P0 :=
        mul_nonneg hcoeff (density_nonneg P0)
      dsimp only [e0] at he0
      linarith
    refine ⟨
      { first := P0
        second := Finset.univ
        first_insensitive := ?_
        second_insensitive := by simpa using (isLastInsensitive_univ 1)
        mass := ?_
        correlated := ?_ }⟩
    · exact isLastInsensitive_finset_compl 0 C0 hC0
    · simpa using hP0mass
    · dsimp only [e0] at he0
      have hcorr : (alpha + p.gamma) * density P0 ≤ density (A ∩ P0) := by
        linarith [p.gamma_nonneg]
      simpa only [Finset.inter_univ] using hcorr
  · have hP1mass : p.gamma ≤ density P1 := by
      have hinter := density_inter_le_right' A P1
      have hsubnonneg : 0 ≤ (alpha + p.gamma) * density P1 :=
        mul_nonneg hcoeff (density_nonneg P1)
      dsimp only [e1] at he1
      linarith
    refine ⟨
      { first := C0
        second := Finset.univ \ C1
        first_insensitive := hC0
        second_insensitive := isLastInsensitive_finset_compl 1 C1 hC1
        mass := ?_
        correlated := ?_ }⟩
    · have hP1eq : C0 ∩ (Finset.univ \ C1) = P1 := by
        ext x
        simp [P1]
      rw [hP1eq]
      exact hP1mass
    · dsimp only [e1] at he1
      have hcorr : (alpha + p.gamma) * density P1 ≤ density (A ∩ P1) := by
        linarith [p.gamma_nonneg]
      have hP1eq : C0 ∩ (Finset.univ \ C1) = P1 := by
        ext x
        simp [P1]
      rw [hP1eq]
      exact hcorr

/-- The many-binary-lines alternative yields correlation with two insensitive
sets.  The current density `alpha` is independent of the fixed floor
`p.delta`; only `p.delta ≤ alpha` is used. -/
theorem insensitiveCorrelation_of_manyBinaryLines (p : CorrelationConstants)
    {alpha : ℝ} {A : Finset (Word 3 m)}
    (hfloor : p.delta ≤ alpha)
    (hA : alpha - 2 * p.eta ≤ density A)
    (hline : ¬ HasLine A)
    (hmany : p.theta / 2 * ((3 : ℝ) ^ m - (2 : ℝ) ^ m) ≤
      ((goodBinaryLines A).card : ℝ))
    (hhalf : 2 * (2 : ℝ) ^ m ≤ (3 : ℝ) ^ m)
    (hsmall : (2 : ℝ) ^ m / (3 : ℝ) ^ m ≤ p.eta) :
    Nonempty (InsensitiveCorrelation p alpha A) := by
  let C0 := endpointCylinderFinset 0 (binaryPart A)
  let C1 := endpointCylinderFinset 1 (binaryPart A)
  have hcore : completionCore A = C0 ∩ C1 := rfl
  apply insensitiveCorrelation_of_core p hfloor hA
  · exact endpointCylinderFinset_isLastInsensitive 0 (binaryPart A)
  · exact endpointCylinderFinset_isLastInsensitive 1 (binaryPart A)
  · rw [← hcore]
    exact density_completionCore_ge_of_many_lines p hmany hhalf
  · rw [← hcore]
    exact (density_inter_completionCore_le hline).trans hsmall

/-- Density-form wrapper for `insensitiveCorrelation_of_manyBinaryLines`.
This is the form returned directly by the many-lines averaging lemma. -/
theorem insensitiveCorrelation_of_manyBinaryLineDensity
    (p : CorrelationConstants) {alpha : ℝ} {A : Finset (Word 3 m)}
    (hm : 0 < m)
    (hfloor : p.delta ≤ alpha)
    (hA : alpha - 2 * p.eta ≤ density A)
    (hline : ¬ HasLine A)
    (hmany : p.theta / 2 ≤ density (goodBinaryLines A))
    (hhalf : 2 * (2 : ℝ) ^ m ≤ (3 : ℝ) ^ m)
    (hsmall : (2 : ℝ) ^ m / (3 : ℝ) ^ m ≤ p.eta) :
    Nonempty (InsensitiveCorrelation p alpha A) := by
  haveI : Nonempty (Line (Fin 2) (Fin m)) := by
    let l : Line (Fin 2) (Fin m) :=
      { idxFun := fun _ ↦ none
        proper := ⟨⟨0, hm⟩, rfl⟩ }
    exact ⟨l⟩
  have hcardpos : 0 < (Fintype.card (Line (Fin 2) (Fin m)) : ℝ) := by
    positivity
  have hcount :
      p.theta / 2 * (Fintype.card (Line (Fin 2) (Fin m)) : ℝ) ≤
        ((goodBinaryLines A).card : ℝ) := by
    rw [density_eq_card_div_card, le_div_iff₀ hcardpos] at hmany
    exact hmany
  have hlineCount :
      (Fintype.card (Line (Fin 2) (Fin m)) : ℝ) =
        (3 : ℝ) ^ m - (2 : ℝ) ^ m := by
    rw [Line.card_fin]
    norm_num only [Nat.cast_sub (Nat.pow_le_pow_left (by omega : 2 ≤ 3) m),
      Nat.cast_pow, Nat.cast_ofNat, Nat.reduceAdd]
  apply insensitiveCorrelation_of_manyBinaryLines p hfloor hA hline
  · simpa only [hlineCount] using hcount
  · exact hhalf
  · exact hsmall

/-- Combine the correlated-sections and many-lines lemmas with the
insensitive excess calculation.  This isolates precisely what remains for
the Ramsey/uniformization construction: produce `CorrelatedSectionData` and
transport its selected tail slice back to a subspace of the original cube. -/
theorem insensitiveCorrelation_of_correlatedSections
    (p : CorrelationConstants) {alpha : ℝ} {m : ℕ} {Y : Type*}
    [Fintype Y] [Nonempty Y]
    (hm : 0 < m)
    (S : CorrelatedSectionData p alpha m Y)
    (hfloor : p.delta ≤ alpha)
    (hline : ∀ y : Y, ¬ HasLine (tailSlice S.points y))
    (hhalf : 2 * (2 : ℝ) ^ m ≤ (3 : ℝ) ^ m)
    (hsmall : (2 : ℝ) ^ m / (3 : ℝ) ^ m ≤ p.eta) :
    ∃ y : Y, Nonempty (InsensitiveCorrelation p alpha (tailSlice S.points y)) := by
  rcases manyBinaryLines_of_correlatedSections p hm S with hinc | hmany
  · obtain ⟨y, hy⟩ := hinc
    exact ⟨y, insensitiveCorrelation_of_eta_increment p hy⟩
  · obtain ⟨y, hyA, hyLines⟩ := hmany
    exact ⟨y, insensitiveCorrelation_of_manyBinaryLineDensity p hm hfloor hyA
      (hline y) hyLines hhalf hsmall⟩

end Excess

/-! ## Concrete tower construction and ambient transport -/

section TowerBridge

/-- Product presentation of all fillings of a uniformized tower hole. -/
noncomputable def holeProduct {r b : ℕ}
    (A : Finset (Tower (Word 3 r) PUnit b))
    (h : BlockHole (Word 3 r) PUnit b) :
    Finset (Word 3 r × h.Tail) := by
  classical
  letI := h.tailFintype
  exact Finset.univ.filter fun p ↦ h.fill p.1 p.2 ∈ A

@[simp] theorem mem_holeProduct {r b : ℕ}
    (A : Finset (Tower (Word 3 r) PUnit b))
    (h : BlockHole (Word 3 r) PUnit b) (x : Word 3 r) (z : h.Tail) :
    (x, z) ∈ holeProduct A h ↔ h.fill x z ∈ A := by
  classical
  letI := h.tailFintype
  simp [holeProduct]

@[simp] theorem fiber_holeProduct {r b : ℕ}
    (A : Finset (Tower (Word 3 r) PUnit b))
    (h : BlockHole (Word 3 r) PUnit b) (x : Word 3 r) :
    fiber (holeProduct A h) x = h.holeSection A x := by
  classical
  letI := h.tailFintype
  ext z
  simp

/-- Fixed-dimension concrete correlation theorem.  Uniformization is applied
after the Graham--Rothschild source dimension has been chosen.  The selected
tail and homogeneous binary subspace are composed with the hole subspace and
reindexed back to a genuine `Fin N` cube. -/
theorem exists_insensitiveCorrelation_fixedDimension
    (s : CorrelationSystem) (m : ℕ)
    (hm0 : s.m0 ≤ m)
    (hhalf : 2 * (2 : ℝ) ^ m ≤ (3 : ℝ) ^ m)
    (hsmall : (2 : ℝ) ^ m / (3 : ℝ) ^ m ≤ s.constants.eta) :
    ∃ N : ℕ, ∀ A : Finset (Word 3 N),
      s.constants.delta ≤ density A →
      HasLine A ∨
        ∃ W : Subspace (Fin m) (Fin 3) (Fin N),
          Nonempty (InsensitiveCorrelation s.constants (density A)
            (pullbackFinset W A)) := by
  have hmpos : 0 < m := s.m0_pos.trans_le hm0
  obtain ⟨r, hGR⟩ := binary_line_homogeneous m
  have hrpos : 0 < r := by
    let c : Line (Fin 2) (Fin r) → Bool := fun _ ↦ false
    obtain ⟨V, _b, _hV⟩ := hGR c
    obtain ⟨i, _hi⟩ := V.proper (⟨0, hmpos⟩ : Fin m)
    exact Fin.pos_iff_nonempty.mpr ⟨i⟩
  have hblock : 1 < Fintype.card (Word 3 r) := by
    rw [Erdos171.card_word]
    exact Nat.one_lt_pow hrpos.ne' (by norm_num)
  obtain ⟨b, hb⟩ := exists_tower_uniform_sections
    (X := Word 3 r) (Y := PUnit) hblock
    (s.constants.eta ^ 2 / 2)
    (div_pos (pow_pos s.constants.eta_pos 2) (by norm_num))
  let N := Fintype.card (BlockIndex r b)
  let e : Tower (Word 3 r) PUnit b ≃ Word 3 N := towerFinEquiv 3 r b
  refine ⟨N, ?_⟩
  intro A hA
  classical
  by_cases hlineA : HasLine A
  · exact Or.inl hlineA
  · right
    let AT : Finset (Tower (Word 3 r) PUnit b) := A.map e.symm.toEmbedding
    have hAT : density AT = density A := by
      simpa [AT] using density_map_equiv e.symm A
    obtain ⟨h, hh⟩ := hb AT
    letI := h.tailFintype
    letI := h.tailNonempty
    let T : Finset (Word 3 r × h.Tail) := holeProduct AT h
    have huniform : ∀ x : Word 3 r,
        density A - s.constants.eta ^ 2 / 2 ≤ density (fiber T x) := by
      intro x
      dsimp only [T]
      rw [fiber_holeProduct]
      have hx := hh x
      rwa [hAT] at hx
    obtain ⟨V, S, hS⟩ := exists_correlatedSectionData_of_uniform
      s hm0 T hA huniform hGR
    have hPull (z : h.Tail) :
        pullbackFinset
            (((h.subspace z).comp V.finLift).reindex
              (Equiv.refl _) (Equiv.refl _)
              (Fintype.equivFin (BlockIndex r b))) A =
          tailSlice S.points z := by
      ext x
      rw [mem_pullbackFinset, mem_tailSlice, hS,
        mem_prefixPullbackProduct]
      dsimp only [T]
      rw [mem_holeProduct]
      have happly := reindex_hole_comp_apply h z V.finLift x
      rw [happly]
      simpa [AT, e]
    have hlineSlices : ∀ z : h.Tail, ¬HasLine (tailSlice S.points z) := by
      intro z hz
      apply hlineA
      let W : Subspace (Fin m) (Fin 3) (Fin N) :=
        ((h.subspace z).comp V.finLift).reindex
          (Equiv.refl _) (Equiv.refl _)
          (Fintype.equivFin (BlockIndex r b))
      apply HasLine.of_pullback W
      rw [hPull z]
      exact hz
    obtain ⟨z, hz⟩ := insensitiveCorrelation_of_correlatedSections
      s.constants hmpos S hA hlineSlices hhalf hsmall
    let W : Subspace (Fin m) (Fin 3) (Fin N) :=
      ((h.subspace z).comp V.finLift).reindex
        (Equiv.refl _) (Equiv.refl _)
        (Fintype.equivFin (BlockIndex r b))
    refine ⟨W, ?_⟩
    simpa only [W, hPull z] using hz

/-- Above one fixed dimension, both elementary power estimates needed in the
completion-core count hold. -/
theorem exists_correlation_dimension_threshold (s : CorrelationSystem) :
    ∃ M : ℕ, s.m0 ≤ M ∧ ∀ m ≥ M,
      2 * (2 : ℝ) ^ m ≤ (3 : ℝ) ^ m ∧
      (2 : ℝ) ^ m / (3 : ℝ) ^ m ≤ s.constants.eta := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one s.constants.eta_pos
    (by norm_num : (2 / 3 : ℝ) < 1)
  let M := max s.m0 (max 2 k)
  refine ⟨M, le_max_left _ _, ?_⟩
  intro m hm
  have hmM : max 2 k ≤ m := (le_max_right s.m0 (max 2 k)).trans hm
  have hm2 : 2 ≤ m := (le_max_left 2 k).trans hmM
  have hmk : k ≤ m := (le_max_right 2 k).trans hmM
  constructor
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm2
    have hp : 2 ^ t ≤ 3 ^ t := Nat.pow_le_pow_left (by omega) t
    have hpR : (2 : ℝ) ^ t ≤ (3 : ℝ) ^ t := by exact_mod_cast hp
    norm_num only [pow_add, pow_two]
    have hnonneg : 0 ≤ (3 : ℝ) ^ t := by positivity
    nlinarith
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hmk
    rw [← div_pow]
    rw [pow_add]
    have htail : (2 / 3 : ℝ) ^ t ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have hbase : 0 ≤ (2 / 3 : ℝ) ^ k := by positivity
    calc
      (2 / 3 : ℝ) ^ k * (2 / 3 : ℝ) ^ t ≤
          (2 / 3 : ℝ) ^ k * 1 := mul_le_mul_of_nonneg_left htail hbase
      _ = (2 / 3 : ℝ) ^ k := mul_one _
      _ ≤ s.constants.eta := hk.le

/-- Uniform-in-dimension correlation theorem for one fixed correlation
system.  In particular, `s.constants.gamma` is chosen before `m`. -/
theorem exists_insensitiveCorrelation (s : CorrelationSystem) :
    ∃ M : ℕ, ∀ m ≥ M, ∃ N : ℕ, ∀ A : Finset (Word 3 N),
      s.constants.delta ≤ density A →
      HasLine A ∨
        ∃ W : Subspace (Fin m) (Fin 3) (Fin N),
          Nonempty (InsensitiveCorrelation s.constants (density A)
            (pullbackFinset W A)) := by
  obtain ⟨M, hm0, hM⟩ := exists_correlation_dimension_threshold s
  refine ⟨M, ?_⟩
  intro m hm
  obtain ⟨hhalf, hsmall⟩ := hM m hm
  exact exists_insensitiveCorrelation_fixedDimension s m (hm0.trans hm) hhalf hsmall

/-- Choose all correlation constants once from a prescribed density floor.
This is the quantifier order required by the subsequent density-increment
iteration. -/
theorem exists_uniform_insensitiveCorrelation (delta : ℝ)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∃ s : CorrelationSystem, s.constants.delta = delta ∧
      ∃ M : ℕ, ∀ m ≥ M, ∃ N : ℕ, ∀ A : Finset (Word 3 N),
        delta ≤ density A →
        HasLine A ∨
          ∃ W : Subspace (Fin m) (Fin 3) (Fin N),
            Nonempty (InsensitiveCorrelation s.constants (density A)
              (pullbackFinset W A)) := by
  obtain ⟨s, hs⟩ := CorrelationSystem.exists_of_delta delta hdelta hdelta1
  refine ⟨s, hs, ?_⟩
  obtain ⟨M, hM⟩ := exists_insensitiveCorrelation s
  refine ⟨M, ?_⟩
  intro m hm
  obtain ⟨N, hN⟩ := hM m hm
  exact ⟨N, fun A hA ↦ hN A (by simpa only [hs] using hA)⟩

end TowerBridge

end DHJ

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos185/DHJ/Iteration.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The density-increment endgame for ternary density Hales--Jewett

This file isolates the formal iteration argument from the combinatorial work
which produces one density increment.  The increment is required to be
uniform over all sets whose current density is at least a fixed positive base
density.  Iterating inside pullbacks then either finds a line, or raises the
density by the same positive amount at every step.  The latter alternative is
eventually incompatible with the elementary upper bound `densityIn <= 1`.

The exact-dimension conclusion is promoted to all larger dimensions by fixing
a suffix whose section is at least as dense as the original set.  This final
fibre argument is recorded explicitly because the proposition used by Erdős
Problem 185 has an eventual-dimension formulation.
-/

namespace DHJ

open scoped BigOperators

noncomputable section

/-- The abstract combinatorial input needed by the density-increment
endgame.  For a fixed positive base density `delta`, the gain `gamma` is
independent of both the requested target dimension and the current set.

The lower bound on the current set is always the original `delta`, while the
conclusion increases its *actual* density.  This is the uniformity which makes
the principle legitimately iterable. -/
def TernaryIncrementPrinciple : Prop :=
  forall delta : Real, 0 < delta ->
    exists gamma : Real, 0 < gamma /\
      forall d : Nat, exists n : Nat,
        forall A : Finset (Word 3 n), delta <= density A ->
          HasLine A \/
            exists U : Combinatorics.Subspace (Fin d) (Fin 3) (Fin n),
              density A + gamma <= densityIn U A

/-- `densityIn` is the ordinary density of the pullback to the parameter
cube. -/
theorem densityIn_eq_density_pullback {eta alpha iota : Type*}
    [Fintype eta] [Fintype alpha] [DecidableEq eta]
    (U : Combinatorics.Subspace eta alpha iota)
    (A : Finset (iota -> alpha)) :
    densityIn U A = density (pullbackFinset U A) := by
  simp [densityIn, density, Nat.card_eq_fintype_card]

/-- Starting from one uniform increment step, build dimensions backwards so
that `r + 1` nested applications either find a line or produce a prescribed
`d`-dimensional subspace on which the density has risen by
`(r + 1) * gamma`.

The backwards choice of dimensions is important: an outer application first
produces a parameter cube whose dimension is exactly the source dimension
chosen for the remaining recursive applications. -/
theorem iterated_increment
    {delta gamma : Real} (hgamma : 0 < gamma)
    (hstep : forall d : Nat, exists n : Nat,
      forall A : Finset (Word 3 n), delta <= density A ->
        HasLine A \/
          exists U : Combinatorics.Subspace (Fin d) (Fin 3) (Fin n),
            density A + gamma <= densityIn U A)
    (d r : Nat) :
    exists n : Nat, forall A : Finset (Word 3 n), delta <= density A ->
      HasLine A \/
        exists U : Combinatorics.Subspace (Fin d) (Fin 3) (Fin n),
          density A + ((r + 1 : Nat) : Real) * gamma <= densityIn U A := by
  induction r with
  | zero =>
      obtain ⟨n, hn⟩ := hstep d
      refine ⟨n, fun A hA => ?_⟩
      simpa using hn A hA
  | succ r ihr =>
      obtain ⟨m, hm⟩ := ihr
      obtain ⟨n, hn⟩ := hstep m
      refine ⟨n, fun A hA => ?_⟩
      rcases hn A hA with hline | ⟨U, hU⟩
      . exact Or.inl hline
      . have hU' : density A + gamma <= density (pullbackFinset U A) := by
          simpa only [densityIn_eq_density_pullback] using hU
        have hpull : delta <= density (pullbackFinset U A) := by
          exact hA.trans ((le_add_of_nonneg_right hgamma.le).trans hU')
        rcases hm (pullbackFinset U A) hpull with hline | ⟨V, hV⟩
        . exact Or.inl (HasLine.of_pullback U hline)
        . refine Or.inr ⟨U.comp V, ?_⟩
          rw [densityIn_comp]
          have hchain :
              density A + gamma + ((r + 1 : Nat) : Real) * gamma <=
                densityIn V (pullbackFinset U A) := by
            nlinarith
          push_cast at hchain ⊢
          nlinarith

/-- A positive uniform increment principle already gives a line in one exact
dimension for every positive density. -/
theorem exists_exact_dimension_hasLine_of_increment
    (hinc : TernaryIncrementPrinciple) (delta : Real) (hdelta : 0 < delta) :
    exists N : Nat, forall A : Finset (Word 3 N),
      delta <= density A -> HasLine A := by
  obtain ⟨gamma, hgamma, hstep⟩ := hinc delta hdelta
  obtain ⟨r, hr⟩ := exists_nat_gt ((1 - delta) / gamma)
  have hr' : (1 - delta) / gamma < ((r + 1 : Nat) : Real) := by
    exact hr.trans_le (by exact_mod_cast Nat.le_succ r)
  have hover : 1 < delta + ((r + 1 : Nat) : Real) * gamma := by
    have := (div_lt_iff₀ hgamma).mp hr'
    nlinarith
  obtain ⟨N, hN⟩ := iterated_increment hgamma hstep 1 r
  refine ⟨N, fun A hA => ?_⟩
  rcases hN A hA with hline | ⟨U, hU⟩
  . exact hline
  . exfalso
    have hupper := densityIn_le_one U A
    have hlower :
        delta + ((r + 1 : Nat) : Real) * gamma <= densityIn U A := by
      nlinarith
    linarith

section SuffixSections

/-- Reindex the ambient coordinates of a combinatorial line by an
equivalence. -/
def reindexLine {alpha iota kappa : Type*}
    (l : Combinatorics.Line alpha iota) (e : iota ≃ kappa) :
    Combinatorics.Line alpha kappa where
  idxFun j := l.idxFun (e.symm j)
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨e i, by simp [hi]⟩

@[simp] theorem reindexLine_apply {alpha iota kappa : Type*}
    (l : Combinatorics.Line alpha iota) (e : iota ≃ kappa)
    (a : alpha) (j : kappa) :
    reindexLine l e a j = l a (e.symm j) := by
  rfl

/-- Swap the two coordinates of a finset in a product. -/
noncomputable def swapFinset {X Y : Type*} (A : Finset (X × Y)) :
    Finset (Y × X) :=
  A.map (Equiv.prodComm X Y).toEmbedding

@[simp] theorem mem_swapFinset {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (A : Finset (X × Y)) (y : Y) (x : X) :
    (y, x) ∈ swapFinset A <-> (x, y) ∈ A := by
  simp [swapFinset]

@[simp] theorem card_swapFinset {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (A : Finset (X × Y)) : (swapFinset A).card = A.card := by
  simp [swapFinset]

/-- The section obtained by fixing the final `r` coordinates of a word. -/
noncomputable def suffixSection {k m r : Nat}
    (A : Finset (Word k (m + r))) (y : Word k r) : Finset (Word k m) :=
  fiber (swapFinset (splitFinset A)) y

@[simp] theorem mem_suffixSection {k m r : Nat}
    (A : Finset (Word k (m + r))) (y : Word k r) (x : Word k m) :
    x ∈ suffixSection A y <-> (wordSplitEquiv k m r).symm (x, y) ∈ A := by
  simp [suffixSection]

/-- Density is the average of the densities of the sections obtained by
fixing the final block. -/
theorem density_eq_average_suffixSection {k m r : Nat}
    (A : Finset (Word k (m + r))) :
    density A = average fun y : Word k r => density (suffixSection A y) := by
  let B : Finset (Word k r × Word k m) := swapFinset (splitFinset A)
  have hB : density B = density A := by
    dsimp [B]
    rw [card_swapFinset, card_splitFinset, Fintype.card_prod]
    simp [Word, pow_add, mul_comm]
  rw [← hB, density_eq_average_fiber]
  rfl

/-- Some suffix section is at least as dense as the whole set. -/
theorem exists_suffixSection_density_ge {k m r : Nat} (hk : 0 < k)
    (A : Finset (Word k (m + r))) :
    exists y : Word k r, density A <= density (suffixSection A y) := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [density_eq_average_suffixSection]
  exact exists_average_le _

/-- Append a fixed suffix to every point of a line, then identify the sum of
the two coordinate blocks with `Fin (m + r)`. -/
def lineWithFixedSuffix {k m r : Nat}
    (l : Combinatorics.Line (Fin k) (Fin m)) (y : Word k r) :
    Combinatorics.Line (Fin k) (Fin (m + r)) :=
  reindexLine (l.horizontal y) finSumFinEquiv

@[simp] theorem lineWithFixedSuffix_apply {k m r : Nat}
    (l : Combinatorics.Line (Fin k) (Fin m)) (y : Word k r) (a : Fin k) :
    lineWithFixedSuffix l y a =
      (wordSplitEquiv k m r).symm (l a, y) := by
  apply (wordSplitEquiv k m r).injective
  apply Prod.ext
  . funext i
    simp [lineWithFixedSuffix, reindexLine, Combinatorics.Line.apply_def]
    cases h : finSumFinEquiv.symm (Fin.castAdd r i) <;> rfl
  . funext i
    simp [lineWithFixedSuffix, reindexLine, Combinatorics.Line.apply_def]
    cases h : finSumFinEquiv.symm (Fin.natAdd m i) <;> rfl

end SuffixSections

/-- A line theorem in one exact dimension extends to every larger dimension
by taking a dense suffix section and appending that fixed suffix to the line
found in the section. -/
theorem hasLine_in_larger_dimensions
    (delta : Real) {N : Nat}
    (hN : forall A : Finset (Word 3 N), delta <= density A -> HasLine A) :
    forall n : Nat, N <= n -> forall A : Finset (Word 3 n),
      delta <= density A -> HasLine A := by
  intro n hn
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro A hA
  obtain ⟨y, hy⟩ := exists_suffixSection_density_ge (k := 3) (m := N)
    (r := r) (by norm_num) A
  obtain ⟨l, hl⟩ := hN (suffixSection A y) (hA.trans hy)
  refine ⟨lineWithFixedSuffix l y, fun a => ?_⟩
  rw [lineWithFixedSuffix_apply]
  exact (mem_suffixSection A y (l a)).1 (hl a)

/-- The abstract increment principle implies the exact eventual-dimension
ternary density Hales--Jewett proposition used by the geometric corollary. -/
theorem densityHalesJewettThree_of_increment
    (hinc : TernaryIncrementPrinciple) : Erdos185.DensityHalesJewettThree := by
  intro delta hdelta
  obtain ⟨N, hN⟩ := exists_exact_dimension_hasLine_of_increment hinc delta hdelta
  refine ⟨N, fun n hn A hcard => ?_⟩
  have hdensity : delta <= density A := by
    rw [density, le_div_iff₀ (by positivity)]
    simpa [Word] using hcard
  obtain ⟨l, hl⟩ := hasLine_in_larger_dimensions delta hN n hn A hdensity
  exact ⟨l, by rintro _ ⟨a, rfl⟩; exact hl a⟩

end

end DHJ

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos185/DHJ/Increment.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The ternary density increment

This file combines the correlation and insensitive-set tiling statements.
The first theorem is the finite averaging calculation which turns an almost
tiling of the structured set into a dense tile.  The final theorem packages
the result with constants which depend only on the fixed density floor, not
on the current density.  That uniformity is what permits finite iteration.
-/

open scoped BigOperators

namespace DHJ

open Combinatorics

private theorem density_eq_erdos171_density {X : Type*} [Fintype X]
    (A : Finset X) : density A = Erdos171.density A :=
  rfl

private theorem pullback_eq_subspacePullback
    {eta alpha iota : Type*} [Fintype eta] [Fintype alpha]
    [Fintype (eta → alpha)]
    (U : Subspace eta alpha iota) (A : Finset (iota → alpha)) :
    pullbackFinset U A = Erdos171.subspacePullback U A := by
  classical
  ext x
  simp [Erdos171.mem_subspacePullback]

private theorem densityIn_eq_erdos171
    {eta alpha iota : Type*} [Fintype eta] [Fintype alpha]
    [Fintype (eta → alpha)] [DecidableEq eta]
    (U : Subspace eta alpha iota) (A : Finset (iota → alpha)) :
    densityIn U A = Erdos171.density (Erdos171.subspacePullback U A) := by
  rw [densityIn, pullback_eq_subspacePullback]
  rw [Erdos171.density, Nat.card_eq_fintype_card]

/-! The strictly positive common ambient density of the tiles lets one pass
from an inequality on their disjoint union to one of the tiles. -/

private theorem exists_dense_tile {m d : ℕ}
    (A : Finset (Word 3 m))
    (T : Erdos171.SubspaceTiling (Fin d) (Fin 3) (Fin m))
    {c : ℝ}
    (hglobal : c * density T.covered < density (A ∩ T.covered)) :
    ∃ U ∈ T.tiles, c < densityIn U A := by
  classical
  let p : Subspace (Fin d) (Fin 3) (Fin m) → Finset (Word 3 m) :=
    fun U ↦ Erdos171.subspacePoints U
  let q : Subspace (Fin d) (Fin 3) (Fin m) → Finset (Word 3 m) :=
    fun U ↦ Erdos171.subspacePoints U ∩ A
  have hqdisj : (T.tiles : Set (Subspace (Fin d) (Fin 3) (Fin m))).PairwiseDisjoint q := by
    intro U hU V hV hne
    exact (T.pairwiseDisjoint hU hV hne).mono (Finset.inter_subset_left)
      (Finset.inter_subset_left)
  have hinter : T.tiles.biUnion q = A ∩ T.covered := by
    ext x
    simp only [Finset.mem_biUnion, q, p, Erdos171.SubspaceTiling.mem_covered,
      Finset.mem_inter]
    aesop
  have hsum_global :
      c * (∑ U ∈ T.tiles, Erdos171.density (p U)) <
        ∑ U ∈ T.tiles, Erdos171.density (q U) := by
    rw [← Erdos171.SubspaceTiling.density_covered,
      ← Erdos171.density_biUnion hqdisj, hinter]
    simpa only [density_eq_erdos171_density] using hglobal
  have hex : ∃ U ∈ T.tiles,
      c * Erdos171.density (p U) < Erdos171.density (q U) := by
    by_contra! h
    have hsum :
        ∑ U ∈ T.tiles, Erdos171.density (q U) ≤
          ∑ U ∈ T.tiles, c * Erdos171.density (p U) := by
      gcongr with U hU
      exact h U hU
    rw [← Finset.mul_sum] at hsum
    exact (not_lt_of_ge hsum) hsum_global
  obtain ⟨U, hUT, hU⟩ := hex
  refine ⟨U, hUT, ?_⟩
  have hfactor := Erdos171.density_inter_subspacePoints U A
  have htilepos : 0 < Erdos171.density (Erdos171.subspacePoints U) := by
    rw [Erdos171.density_eq_card_div_card,
      Erdos171.card_subspacePoints_fin, Erdos171.card_word]
    positivity
  have hpU : p U = Erdos171.subspacePoints U := rfl
  have hqU : q U = Erdos171.subspacePoints U ∩ A := rfl
  rw [hpU, hqU, hfactor] at hU
  have hlocal : c < Erdos171.density (Erdos171.subspacePullback U A) := by
    apply lt_of_mul_lt_mul_left _ htilepos.le
    simpa only [mul_comm] using hU
  simpa only [densityIn_eq_erdos171] using hlocal

/-! The scalar part of Proposition 6 in Dodos--Kanellopoulos--Tyros. -/

theorem exists_density_increment_of_correlation_tiling {m d : ℕ}
    (A D : Finset (Word 3 m)) (alpha γ : ℝ)
    (halpha : 0 ≤ alpha) (hγ : 0 < γ)
    (hD : γ ≤ density D)
    (hcorr : (alpha + γ) * density D ≤ density (A ∩ D))
    (T : Erdos171.SubspaceTiling (Fin d) (Fin 3) (Fin m))
    (hcontained : T.IsContainedIn D)
    (huncovered : density (D \ T.covered) < γ ^ 2 / 2) :
    ∃ U ∈ T.tiles, alpha + γ / 2 < densityIn U A := by
  classical
  have hcovD : T.covered ⊆ D :=
    (Erdos171.SubspaceTiling.covered_subset_iff T D).2 hcontained
  have hu : density T.covered ≤ density D := density_mono hcovD
  have hsplitD : density (D \ T.covered) + density T.covered = density D := by
    rw [density_eq_erdos171_density, density_eq_erdos171_density,
      density_eq_erdos171_density]
    have hs := Erdos171.density_sdiff_add_density_inter D T.covered
    rw [Finset.inter_eq_right.mpr hcovD] at hs
    exact hs
  have hsplitA :
      density ((A ∩ D) \ T.covered) + density (A ∩ T.covered) =
        density (A ∩ D) := by
    rw [density_eq_erdos171_density, density_eq_erdos171_density,
      density_eq_erdos171_density]
    have hs := Erdos171.density_sdiff_add_density_inter (A ∩ D) T.covered
    have hi : (A ∩ D) ∩ T.covered = A ∩ T.covered := by
      ext x
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨⟨hxA, _⟩, hxT⟩
        exact ⟨hxA, hxT⟩
      · rintro ⟨hxA, hxT⟩
        exact ⟨⟨hxA, hcovD hxT⟩, hxT⟩
    simpa only [hi] using hs
  have hrem_le : density ((A ∩ D) \ T.covered) ≤ density (D \ T.covered) := by
    apply density_mono
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hx ⊢
    exact ⟨hx.1.2, hx.2⟩
  have hc :
      (alpha + γ) * density D - density (D \ T.covered) ≤
        density (A ∩ T.covered) := by
    linarith
  have hcoefficient : 0 ≤ alpha + γ / 2 := by
    positivity
  have hutarget :
      (alpha + γ / 2) * density T.covered ≤
        (alpha + γ / 2) * density D :=
    mul_le_mul_of_nonneg_left hu hcoefficient
  have hgap : density (D \ T.covered) < (γ / 2) * density D := by
    nlinarith [sq_pos_of_pos hγ]
  have hmass :
      (alpha + γ / 2) * density T.covered <
        density (A ∩ T.covered) := by
    nlinarith
  apply exists_dense_tile A T
  exact hmass

/-! ## Quantifier-compatible assembly

The two propositions below record the exact output contracts of the
correlation and tiling modules.  In particular, the correlation constants
are chosen before the target dimension, so the eventual additive gain is
uniform throughout the iteration. -/

/-- The concrete uniform ternary increment, obtained from the correlation
theorem and the two-insensitive-factor almost-tiling theorem. -/
theorem ternaryIncrementPrinciple : TernaryIncrementPrinciple := by
  intro delta hdelta
  by_cases hdeltaOne : delta ≤ 1
  · obtain ⟨s, _hsdelta, lower, hcorr⟩ :=
      exists_uniform_insensitiveCorrelation delta hdelta hdeltaOne
    let p : CorrelationConstants := s.constants
    refine ⟨p.gamma / 2, half_pos p.gamma_pos, ?_⟩
    intro d
    let beta : ℝ := p.gamma ^ 2 / 8
    have hbeta : 0 < beta := by
      dsimp only [beta]
      exact div_pos (sq_pos_of_pos p.gamma_pos) (by norm_num)
    obtain ⟨m, hm, htile⟩ :=
      exists_two_insensitive_tiling_dimension d lower beta hbeta
    obtain ⟨n, hn⟩ := hcorr m hm
    refine ⟨n, ?_⟩
    intro A hA
    rcases hn A hA with hline | ⟨W, hS⟩
    · exact Or.inl hline
    · obtain ⟨S⟩ := hS
      have hgammaOne : p.gamma ≤ 1 := by
        calc
          p.gamma ≤ p.eta / 2 := p.gamma_le_eta_div_two
          _ ≤ 1 := by nlinarith [p.eta_le_one]
      have hfourBeta : 4 * beta ≤ p.gamma := by
        have hsquare : p.gamma ^ 2 ≤ p.gamma := by
          nlinarith [mul_nonneg p.gamma_nonneg (sub_nonneg.mpr hgammaOne)]
        dsimp only [beta]
        nlinarith
      obtain ⟨T, hcontained, herror⟩ :=
        htile S.first S.second S.first_insensitive S.second_insensitive
          (hfourBeta.trans S.mass)
      have herror' :
          density ((S.first ∩ S.second) \ T.covered) < p.gamma ^ 2 / 2 := by
        have hfour : 4 * beta = p.gamma ^ 2 / 2 := by
          dsimp only [beta]
          ring
        simpa only [hfour] using herror
      obtain ⟨U, _hUT, hU⟩ :=
        exists_density_increment_of_correlation_tiling
          (pullbackFinset W A) (S.first ∩ S.second) (density A) p.gamma
          (density_nonneg A) p.gamma_pos S.mass S.correlated T hcontained herror'
      refine Or.inr ⟨W.comp U, ?_⟩
      rw [densityIn_comp]
      exact le_of_lt hU
  · refine ⟨1, zero_lt_one, ?_⟩
    intro d
    refine ⟨0, ?_⟩
    intro A hA
    exfalso
    have hupper := density_le_one A
    exact hdeltaOne (hA.trans hupper)

end DHJ

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos185.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 185.
https://www.erdosproblems.com/forum/thread/185

Informal authors:
- Pandelis Dodos
- Vassilis Kanellopoulos
- Konstantinos Tyros

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos185.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Erdős Problem 185

The maximum size of a subset of the ternary cube containing no three
distinct Euclidean-collinear points is little-oh of the size of the cube.

The substantive combinatorial input is the specialized density
Hales--Jewett theorem proved in the `Erdos185.DHJ` modules by the finite
density-increment argument of Dodos--Kanellopoulos--Tyros.  A combinatorial
line is a Euclidean line, so the density theorem applies to every Moser set.
-/

/-- Density Hales--Jewett for the ternary alphabet, in the exact cardinality
form needed for Erdős Problem 185. -/
theorem density_hales_jewett_three : DensityHalesJewettThree :=
  DHJ.densityHalesJewettThree_of_increment DHJ.ternaryIncrementPrinciple

/-- **Erdős Problem 185.** If `f3 n` is the largest cardinality of a subset
of `{0,1,2}^n` containing no three distinct Euclidean-collinear points, then
`f3 n = o(3^n)`. -/
theorem erdos_185 :
    Asymptotics.IsLittleO Filter.atTop
      (fun n : ℕ ↦ (f3 n : ℝ))
      (fun n : ℕ ↦ (3 : ℝ) ^ n) :=
  f3_isLittleO_three_pow_of_densityHalesJewettThree density_hales_jewett_three

end

#print axioms erdos_185
-- 'Erdos185.erdos_185' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos185
