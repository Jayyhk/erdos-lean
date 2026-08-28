import Mathlib

namespace Erdos847

/-
# Problem Description

Erdős Problem 847. Let `A ⊂ ℕ` be infinite and suppose there is some `ε > 0` such that every
subset of `A` of size `n` contains a subset of size at least `εn` with no three-term
arithmetic progression. Must `A` be a union of finitely many sets containing no three-term
arithmetic progression? `erdos_847` disproves this.

A problem of Erdős, Nešetřil and Rödl [Er92b]; the negative answer is due to Reiher, Rödl and
Sales [RRS24]. In the statement, `HasFew3APs A` is the hypothesis
`∃ ε > 0, ∀ finite B ⊆ A, ∃ C ⊆ B with C.ncard ≥ ε * B.ncard and ThreeAPFree C`, and the
conclusion being refuted is that `A` is a finite union `⋃ i : Fin n, S i` with every `S i`
three-term-progression-free.

The formalisation is by plby (github.com/plby/lean-proofs),
`src/latest/ErdosProblems/Erdos847.lean` together with the modules of
`src/latest/ErdosProblems/Erdos847/`. Those files are concatenated here in dependency order,
with their project-internal imports removed so that `Mathlib` is the only import, each
module's contents kept in a `section` carrying its own `open` lines, the whole wrapped once in
`namespace Erdos847`, the upstream trust-base print line and trailing `alias` removed, and the
final theorem renamed from `not_erdos_847` to `erdos_847`. No mathematical content is changed.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/LineCounting.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Counting combinatorial lines in finite Hales--Jewett cubes

This module supplies the exact finite counts used in the sparse-line selection
argument of Reiher--Rödl--Sales.  It deliberately separates raw line words
from proper combinatorial lines: a raw word is a function to `Option A`, and a
proper line is one whose `none` (moving-coordinate) set is nonempty.
-/

namespace Erdos847LineCounting

open Function Set
open Combinatorics

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {A : Type u} [Fintype A]

/-- Evaluation on a combinatorial line is injective when the alphabet has at least two letters. -/
lemma line_apply_injective [Nontrivial A] {n : ℕ} (l : Line A (Fin n)) :
    Function.Injective l := by
  intro a b hab
  obtain ⟨j, hj⟩ := l.proper
  have h := congrFun hab j
  simpa [Line.coe_apply, hj] using h

/-- Two values of a nontrivial alphabet determine a line as a function. -/
lemma line_eq_of_apply_eq_apply [Nontrivial A] {n : ℕ} {l m : Line A (Fin n)} {a b : A}
    (hab : a ≠ b) (ha : l a = m a) (hb : l b = m b) : l = m := by
  ext j
  have haj := congrFun ha j
  have hbj := congrFun hb j
  cases hl : l.idxFun j <;> cases hm : m.idxFun j <;>
    simp_all [Line.coe_apply]

/-- Two distinct cube points lie on at most one combinatorial line. -/
lemma line_eq_of_two_points [Nontrivial A] {n : ℕ} {l m : Line A (Fin n)}
    {a b c d : A} (hpts : l a ≠ l b) (ha : l a = m c) (hb : l b = m d) : l = m := by
  have hab : a ≠ b := fun h ↦ hpts (by simp [h])
  obtain ⟨j, hj⟩ := l.proper
  have hc : c = a := by
    have hca := congrFun ha j
    cases hm : m.idxFun j with
    | none => simpa [Line.coe_apply, hj, hm] using hca.symm
    | some z =>
        have hdb := congrFun hb j
        simp only [Line.coe_apply, hj, hm, Option.getD_none, Option.getD_some] at hca hdb
        exact (hab (hca.trans hdb.symm)).elim
  have hd : d = b := by
    have hdb := congrFun hb j
    cases hm : m.idxFun j with
    | none => simpa [Line.coe_apply, hj, hm] using hdb.symm
    | some z =>
        have hca := congrFun ha j
        simp only [Line.coe_apply, hj, hm, Option.getD_none, Option.getD_some] at hca hdb
        exact (hab (hca.trans hdb.symm)).elim
  apply line_eq_of_apply_eq_apply hab
  · simpa [hc] using ha
  · simpa [hd] using hb

/-- The cube vertices lying on a combinatorial line. -/
def linePoints {n : ℕ} (l : Line A (Fin n)) : Set (Fin n → A) := Set.range l

@[simp] lemma mem_linePoints {n : ℕ} (l : Line A (Fin n)) (x : Fin n → A) :
    x ∈ linePoints l ↔ ∃ a, l a = x := Iff.rfl

/-- Set-theoretic form: two distinct common vertices determine the line uniquely. -/
lemma line_eq_of_two_mem_points [Nontrivial A] {n : ℕ} {l m : Line A (Fin n)}
    {x y : Fin n → A} (hxy : x ≠ y)
    (hxl : x ∈ linePoints l) (hxm : x ∈ linePoints m)
    (hyl : y ∈ linePoints l) (hym : y ∈ linePoints m) : l = m := by
  rcases hxl with ⟨a, rfl⟩
  rcases hyl with ⟨b, hby⟩
  rcases hxm with ⟨c, hca⟩
  rcases hym with ⟨d, hdy⟩
  apply line_eq_of_two_points (l := l) (m := m) (a := a) (b := b) (c := c) (d := d)
  · intro hab
    exact hxy (hab.trans hby)
  · exact hca.symm
  · exact hby.trans hdy.symm

/-- Moving coordinates of a proper Mathlib combinatorial line. -/
def movingSet {I : Type*} [Fintype I] (l : Line A I) : Finset I :=
  Finset.univ.filter fun j ↦ l.idxFun j = none

@[simp] lemma mem_movingSet {I : Type*} [Fintype I] (l : Line A I) (j : I) :
    j ∈ movingSet l ↔ l.idxFun j = none := by
  simp [movingSet]

/-- A raw line word. `none` means a moving coordinate and `some a` a fixed letter. -/
abbrev RawLine (A : Type u) (n : ℕ) := Fin n → Option A

/-- Moving coordinates of a raw line word. -/
def rawMovingSet {n : ℕ} (f : RawLine A n) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ f j = none

@[simp] lemma mem_rawMovingSet {n : ℕ} (f : RawLine A n) (j : Fin n) :
    j ∈ rawMovingSet f ↔ f j = none := by
  simp [rawMovingSet]

/-- All proper combinatorial lines, stratified by moving-support cardinality. -/
noncomputable def lineStratum (n i : ℕ) : Finset (Line A (Fin n)) := by
  letI : Fintype (Line A (Fin n)) :=
    Fintype.ofInjective Line.idxFun (by
      intro l m h
      cases l
      cases m
      simp_all)
  exact Finset.univ.filter fun l ↦ (movingSet l).card = i

@[simp] lemma mem_lineStratum {n i : ℕ} {l : Line A (Fin n)} :
    l ∈ lineStratum (A := A) n i ↔ (movingSet l).card = i := by
  simp [lineStratum]

/-- An `i`-element coordinate support, represented as an element of a finite powerset slice. -/
abbrev Support (n i : ℕ) := ↥((Finset.univ : Finset (Fin n)).powersetCard i)

/-- The fixed letters on the complement of a support. -/
abbrev FixedWord (S : Finset (Fin n)) := ({j : Fin n // j ∉ S} → A)

/-- A support together with all fixed letters is the canonical code for a line. -/
abbrev LineCode (A : Type u) [Fintype A] (n i : ℕ) :=
  Σ S : Support n i, FixedWord (A := A) S.1

lemma support_card (S : Support n i) : S.1.card = i :=
  (Finset.mem_powersetCard.mp S.2).2

/-- Decode a canonical support/fixed-word code into a proper combinatorial line. -/
def lineOfCode {n i : ℕ} (hi : 0 < i) (c : LineCode A n i) : Line A (Fin n) where
  idxFun j := if h : j ∈ c.1.1 then none else some (c.2 ⟨j, h⟩)
  proper := by
    have hcard : c.1.1.card = i := support_card c.1
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (hcard.symm ▸ hi)
    exact ⟨j, dif_pos hj⟩

@[simp] lemma lineOfCode_idxFun_none_iff {n i : ℕ} (hi : 0 < i) (c : LineCode A n i)
    (j : Fin n) : (lineOfCode hi c).idxFun j = none ↔ j ∈ c.1.1 := by
  simp [lineOfCode]

/-- A coordinate outside the moving support carries a fixed letter. -/
lemma idxFun_isSome_of_not_mem_movingSet {n : ℕ} (l : Line A (Fin n))
    (j : {j : Fin n // j ∉ movingSet l}) : (l.idxFun j.1).isSome := by
  cases h : l.idxFun j.1 with
  | none => exact (j.2 ((mem_movingSet l j.1).2 h)).elim
  | some a => simp

/-- The fixed letter of a line at a coordinate outside its moving support. -/
def fixedLetter {n : ℕ} (l : Line A (Fin n)) (j : {j : Fin n // j ∉ movingSet l}) : A :=
  (l.idxFun j.1).get (idxFun_isSome_of_not_mem_movingSet l j)

@[simp] lemma fixedLetter_spec {n : ℕ} (l : Line A (Fin n))
    (j : {j : Fin n // j ∉ movingSet l}) : l.idxFun j.1 = some (fixedLetter l j) := by
  exact (Option.coe_get (idxFun_isSome_of_not_mem_movingSet l j)).symm

/-- Lines in a support stratum which contain a specified cube point. -/
noncomputable def linesThrough {n : ℕ} (x : Fin n → A) (i : ℕ) :
    Finset (Line A (Fin n)) :=
  (lineStratum (A := A) n i).filter fun l ↦ ∃ a, l a = x

@[simp] lemma mem_linesThrough {n i : ℕ} {x : Fin n → A} {l : Line A (Fin n)} :
    l ∈ linesThrough x i ↔ (movingSet l).card = i ∧ ∃ a, l a = x := by
  simp [linesThrough]

/-! ## Subcube and extension multiplicities

An `m`-dimensional coordinate subcube is canonically encoded by its `m` moving coordinates and
one fixed letter on every complementary coordinate.  This representation avoids the `|A|^m`
overcount caused by representing a subcube by an arbitrary ambient point.
-/

/-- Canonical codes for `m`-dimensional coordinate subcubes of `A^(Fin n)`. -/
abbrev SubcubeCode (A : Type u) [Fintype A] (n m : ℕ) := LineCode A n m

/-- The candidate `m`-coordinate supports which extend the moving support of `l`. -/
noncomputable def extensionSupports {n : ℕ} (l : Line A (Fin n)) (m : ℕ) :
    Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard m).filter (movingSet l ⊆ ·)

@[simp] lemma mem_extensionSupports {n m : ℕ} {l : Line A (Fin n)}
    {M : Finset (Fin n)} :
    M ∈ extensionSupports l m ↔ M ⊆ Finset.univ ∧ M.card = m ∧ movingSet l ⊆ M := by
  simp [extensionSupports, and_assoc]

/-- A canonical subcube contains a line when it moves on every moving coordinate of the line and
agrees with the line's fixed letters outside the subcube support. -/
def SubcubeContainsLine {n m : ℕ} (Q : SubcubeCode A n m) (l : Line A (Fin n)) : Prop :=
  movingSet l ⊆ Q.1.1 ∧
    ∀ j : {j : Fin n // j ∉ Q.1.1}, l.idxFun j.1 = some (Q.2 j)

/-- All canonical `m`-subcubes containing a given line. -/
noncomputable def subcubesContaining {n : ℕ} (l : Line A (Fin n)) (m : ℕ) :
    Finset (SubcubeCode A n m) :=
  Finset.univ.filter fun Q ↦ SubcubeContainsLine Q l

@[simp] lemma mem_subcubesContaining {n m : ℕ} {l : Line A (Fin n)}
    {Q : SubcubeCode A n m} :
    Q ∈ subcubesContaining l m ↔ SubcubeContainsLine Q l := by
  simp [subcubesContaining]

end Erdos847LineCounting

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/BlockCandidates.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Disjoint-block Hales--Jewett candidates

This file packages a useful amplification of the finite Hales--Jewett theorem.
The coordinate type `Fin t × J` is split into `t` disjoint copies of `J`.  A
candidate line moves inside one copy, is a prescribed Hales--Jewett line there,
and is fixed arbitrarily on all other copies.

The encoding is injective.  Consequently the candidate family has an exact
product count.  Every colouring makes many candidates monochromatic, while a
fixed cube point belongs to at most `t * 2 ^ card J` candidates.
-/

namespace Erdos847BlockCandidates

open Function Set
open Combinatorics
open Erdos847LineCounting

attribute [local instance] Classical.propDecidable Classical.decEq

universe u v w

variable {A : Type u} {J : Type v} {K : Type w}
variable [Fintype A] [Fintype J]

/-- The fixed coordinates outside the selected block. -/
abbrev OutsideIndex (t : ℕ) (j : Fin t) := {k : Fin t // k ≠ j}

/-- A fixed word on every block other than `j`. -/
abbrev OutsideWord (A : Type u) (J : Type v) (t : ℕ) (j : Fin t) :=
  OutsideIndex t j → J → A

/-- A frame consists of an active block and the fixed word outside it. -/
abbrev FrameCode (A : Type u) (J : Type v) (t : ℕ) :=
  Σ j : Fin t, OutsideWord A J t j

/-- Candidate-line codes relative to a prescribed finite internal line family `S`. -/
abbrev CandidateCode (A : Type u) (J : Type v) (t : ℕ)
    (S : Finset (Line A J)) :=
  Σ j : Fin t, OutsideWord A J t j × ↑S

/-- Fill the active block of a frame by a word on `J`. -/
def framePoint {t : ℕ} (f : FrameCode A J t) (x : J → A) : Fin t × J → A :=
  fun iq ↦ if h : iq.1 = f.1 then x iq.2 else f.2 ⟨iq.1, h⟩ iq.2

@[simp] lemma framePoint_active {t : ℕ} (f : FrameCode A J t) (x : J → A)
    (q : J) : framePoint f x (f.1, q) = x q := by
  simp [framePoint]

@[simp] lemma framePoint_outside {t : ℕ} (f : FrameCode A J t) (x : J → A)
    (k : Fin t) (q : J) (hk : k ≠ f.1) :
    framePoint f x (k, q) = f.2 ⟨k, hk⟩ q := by
  simp [framePoint, hk]

/-- Decode a candidate into an ambient combinatorial line. -/
def encodedLine {t : ℕ} {S : Finset (Line A J)}
    (c : CandidateCode A J t S) : Line A (Fin t × J) where
  idxFun iq := if h : iq.1 = c.1 then c.2.2.1.idxFun iq.2
    else some (c.2.1 ⟨iq.1, h⟩ iq.2)
  proper := by
    obtain ⟨q, hq⟩ := c.2.2.1.proper
    exact ⟨(c.1, q), by simp [hq]⟩

@[simp] lemma encodedLine_idxFun_active {t : ℕ} {S : Finset (Line A J)}
    (c : CandidateCode A J t S) (q : J) :
    (encodedLine c).idxFun (c.1, q) = c.2.2.1.idxFun q := by
  simp [encodedLine]

@[simp] lemma encodedLine_idxFun_outside {t : ℕ} {S : Finset (Line A J)}
    (c : CandidateCode A J t S) (k : Fin t) (q : J) (hk : k ≠ c.1) :
    (encodedLine c).idxFun (k, q) = some (c.2.1 ⟨k, hk⟩ q) := by
  simp [encodedLine, hk]

@[simp] lemma encodedLine_apply {t : ℕ} {S : Finset (Line A J)}
    (c : CandidateCode A J t S) (a : A) :
    encodedLine c a = framePoint ⟨c.1, c.2.1⟩ (c.2.2.1 a) := by
  funext iq
  by_cases h : iq.1 = c.1
  · simp [Line.coe_apply, encodedLine, framePoint, h]
  · simp [Line.coe_apply, encodedLine, framePoint, h]

/-- The block/outside-word/internal-line encoding loses no information. -/
theorem encodedLine_injective {t : ℕ} {S : Finset (Line A J)} :
    Function.Injective (encodedLine : CandidateCode A J t S → Line A (Fin t × J)) := by
  rintro ⟨j, w, l⟩ ⟨k, v, m⟩ hline
  have hjk : j = k := by
    obtain ⟨q, hq⟩ := l.1.proper
    have hidx := congrArg (fun L : Line A (Fin t × J) ↦ L.idxFun (j, q)) hline
    by_contra hne
    simp [encodedLine, hq, hne] at hidx
  subst k
  have hlm : l = m := by
    apply Subtype.ext
    apply Line.ext
    funext q
    have hidx := congrArg (fun L : Line A (Fin t × J) ↦ L.idxFun (j, q)) hline
    simpa [encodedLine] using hidx
  subst m
  have hwv : w = v := by
    funext k' q
    have hidx := congrArg
      (fun L : Line A (Fin t × J) ↦ L.idxFun (k'.1, q)) hline
    have hsome : some (w k' q) = some (v k' q) := by
      simpa [encodedLine, k'.2] using hidx
    exact Option.some.inj hsome
  subst v
  rfl

/-- The finite family of all encoded candidates. -/
noncomputable def candidateLines (t : ℕ) (S : Finset (Line A J)) :
    Finset (Line A (Fin t × J)) :=
  Finset.univ.image (encodedLine (S := S))

@[simp] lemma mem_candidateLines {t : ℕ} {S : Finset (Line A J)}
    {l : Line A (Fin t × J)} :
    l ∈ candidateLines t S ↔ ∃ c : CandidateCode A J t S, encodedLine c = l := by
  simp [candidateLines]

/-- There are `t - 1` blocks outside a selected block. -/
lemma card_outsideIndex {t : ℕ} (j : Fin t) :
    Fintype.card (OutsideIndex t j) = t - 1 := by
  have h := Fintype.card_subtype_compl (fun k : Fin t ↦ k = j)
  simp only [Fintype.card_fin] at h
  have heq : Fintype.card {k : Fin t // k = j} = 1 := by simp
  rw [heq] at h
  simpa [OutsideIndex] using h

/-- Exact number of outside words. -/
lemma card_outsideWord {t : ℕ} (j : Fin t) :
    Fintype.card (OutsideWord A J t j) =
      Fintype.card A ^ (Fintype.card J * (t - 1)) := by
  simp only [OutsideWord, Fintype.card_fun, card_outsideIndex]
  rw [pow_mul]

/-- Exact number of frames. -/
lemma card_frameCode (t : ℕ) :
    Fintype.card (FrameCode A J t) =
      t * Fintype.card A ^ (Fintype.card J * (t - 1)) := by
  rw [Fintype.card_sigma]
  simp_rw [card_outsideWord]
  simp

/-- Exact number of candidate codes. -/
lemma card_candidateCode (t : ℕ) (S : Finset (Line A J)) :
    Fintype.card (CandidateCode A J t S) =
      t * Fintype.card A ^ (Fintype.card J * (t - 1)) * S.card := by
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_prod, card_outsideWord, Fintype.card_coe]
  simp
  ring

/-- Exact candidate-family cardinality. -/
theorem card_candidateLines (t : ℕ) (S : Finset (Line A J)) :
    (candidateLines t S).card =
      t * Fintype.card A ^ (Fintype.card J * (t - 1)) * S.card := by
  rw [candidateLines, Finset.card_image_of_injective _ encodedLine_injective,
    Finset.card_univ, card_candidateCode]

/-- A finite internal family contains at most as many lines as raw `Option A` words. -/
lemma card_lineFamily_le (S : Finset (Line A J)) :
    S.card ≤ (Fintype.card A + 1) ^ Fintype.card J := by
  have hinj : Set.InjOn Line.idxFun (S : Set (Line A J)) := by
    intro l _ m _ h
    cases l
    cases m
    simp_all
  calc
    S.card = (S.image Line.idxFun).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (J → Option A)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = (Fintype.card A + 1) ^ Fintype.card J := by simp [Fintype.card_fun]

/-- Nonempty internal families give the basic lower bound on candidates. -/
theorem candidateLines_card_lower {t : ℕ} {S : Finset (Line A J)}
    (hS : S.Nonempty) :
    t * Fintype.card A ^ (Fintype.card J * (t - 1)) ≤
      (candidateLines t S).card := by
  rw [card_candidateLines]
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr hS
  simpa using Nat.mul_le_mul_left
    (t * Fintype.card A ^ (Fintype.card J * (t - 1))) hcard

/-- Crude raw-word upper bound on the candidate family. -/
theorem candidateLines_card_upper (t : ℕ) (S : Finset (Line A J)) :
    (candidateLines t S).card ≤
      t * Fintype.card A ^ (Fintype.card J * (t - 1)) *
        (Fintype.card A + 1) ^ Fintype.card J := by
  rw [card_candidateLines]
  exact Nat.mul_le_mul_left _ (card_lineFamily_le S)

/-! ## Monochromatic candidates -/

/-- Candidates which are monochromatic for a given colouring. -/
noncomputable def monoCandidateLines {t : ℕ} (S : Finset (Line A J))
    (color : (Fin t × J → A) → K) : Finset (Line A (Fin t × J)) :=
  (candidateLines t S).filter fun l ↦ l.IsMono color

@[simp] lemma mem_monoCandidateLines {t : ℕ} {S : Finset (Line A J)}
    {color : (Fin t × J → A) → K} {l : Line A (Fin t × J)} :
    l ∈ monoCandidateLines S color ↔ l ∈ candidateLines t S ∧ l.IsMono color := by
  simp [monoCandidateLines]

/-- Choose a monochromatic internal line for the colouring induced by a frame. -/
noncomputable def chosenInternal {t : ℕ} {S : Finset (Line A J)}
    (hHJ : ∀ color : (J → A) → K, ∃ l ∈ S, l.IsMono color)
    (color : (Fin t × J → A) → K) (f : FrameCode A J t) : ↑S :=
  ⟨Classical.choose (hHJ (fun x ↦ color (framePoint f x))),
    (Classical.choose_spec (hHJ (fun x ↦ color (framePoint f x)))).1⟩

lemma chosenInternal_mono {t : ℕ} {S : Finset (Line A J)}
    (hHJ : ∀ color : (J → A) → K, ∃ l ∈ S, l.IsMono color)
    (color : (Fin t × J → A) → K) (f : FrameCode A J t) :
    (chosenInternal hHJ color f).1.IsMono (fun x ↦ color (framePoint f x)) :=
  (Classical.choose_spec (hHJ (fun x ↦ color (framePoint f x)))).2

/-- Candidate selected from a frame by internal Hales--Jewett. -/
noncomputable def chosenCandidate {t : ℕ} {S : Finset (Line A J)}
    (hHJ : ∀ color : (J → A) → K, ∃ l ∈ S, l.IsMono color)
    (color : (Fin t × J → A) → K) (f : FrameCode A J t) :
    CandidateCode A J t S := ⟨f.1, f.2, chosenInternal hHJ color f⟩

lemma chosenCandidate_mono {t : ℕ} {S : Finset (Line A J)}
    (hHJ : ∀ color : (J → A) → K, ∃ l ∈ S, l.IsMono color)
    (color : (Fin t × J → A) → K) (f : FrameCode A J t) :
    (encodedLine (chosenCandidate hHJ color f)).IsMono color := by
  rcases chosenInternal_mono hHJ color f with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro a
  simpa [chosenCandidate, encodedLine_apply] using hk a

lemma chosenCandidate_injective {t : ℕ} {S : Finset (Line A J)}
    (hHJ : ∀ color : (J → A) → K, ∃ l ∈ S, l.IsMono color)
    (color : (Fin t × J → A) → K) :
    Function.Injective (fun f : FrameCode A J t ↦
      encodedLine (chosenCandidate hHJ color f)) := by
  rintro ⟨j, w⟩ ⟨k, v⟩ h
  have hcode := encodedLine_injective h
  have hjk : j = k := congrArg Sigma.fst hcode
  subst k
  have hwv : w = v := by
    funext k' q
    have hidx := congrArg
      (fun L : Line A (Fin t × J) ↦ L.idxFun (k'.1, q)) h
    have hsome : some (w k' q) = some (v k' q) := by
      simpa [chosenCandidate, encodedLine, k'.2] using hidx
    exact Option.some.inj hsome
  subst v
  rfl

/-- Every colouring has at least one monochromatic candidate per frame. -/
theorem monoCandidateLines_card_lower {t : ℕ} {S : Finset (Line A J)}
    (hHJ : ∀ color : (J → A) → K, ∃ l ∈ S, l.IsMono color)
    (color : (Fin t × J → A) → K) :
    t * Fintype.card A ^ (Fintype.card J * (t - 1)) ≤
      (monoCandidateLines S color).card := by
  let f : FrameCode A J t → Line A (Fin t × J) :=
    fun frame ↦ encodedLine (chosenCandidate hHJ color frame)
  have himage : (Finset.univ : Finset (FrameCode A J t)).image f ⊆
      monoCandidateLines S color := by
    intro l hl
    rcases Finset.mem_image.mp hl with ⟨frame, -, rfl⟩
    exact mem_monoCandidateLines.mpr ⟨mem_candidateLines.mpr
      ⟨chosenCandidate hHJ color frame, rfl⟩, chosenCandidate_mono hHJ color frame⟩
  calc
    t * Fintype.card A ^ (Fintype.card J * (t - 1)) =
        (Finset.univ : Finset (FrameCode A J t)).card := by
          rw [Finset.card_univ, card_frameCode]
    _ = ((Finset.univ : Finset (FrameCode A J t)).image f).card :=
      (Finset.card_image_of_injective _ (chosenCandidate_injective hHJ color)).symm
    _ ≤ (monoCandidateLines S color).card := Finset.card_le_card himage

/-! ## Point degrees -/

end Erdos847BlockCandidates

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/LineExclusions.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Geometric exclusion counts for the sparse Hales--Jewett selection

This standalone scratch module formalizes the three estimates in the proof of
Reiher--Rödl--Sales Claim 3.9.  It uses the same exact tripod and triangle
predicates as `Erdos847SparseLines.lean`, but repeats the small incidence API so
that the file can be checked independently of precompiled scratch modules.
-/

namespace Erdos847LineExclusions

open Function Set
open Combinatorics
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {A : Type u} {I : Type*}

/-- The cube vertices on a combinatorial line. -/
def linePoints (l : Line A I) : Set (I → A) := Set.range l

@[simp] lemma mem_linePoints (l : Line A I) (x : I → A) :
    x ∈ linePoints l ↔ ∃ a, l a = x := Iff.rfl

/-- Moving coordinates of a combinatorial line. -/
def movingSet [Fintype I] (l : Line A I) : Finset I :=
  Finset.univ.filter fun i ↦ l.idxFun i = none

@[simp] lemma mem_movingSet [Fintype I] (l : Line A I) (i : I) :
    i ∈ movingSet l ↔ l.idxFun i = none := by
  simp [movingSet]

lemma line_idxFun_injective :
    Function.Injective (Line.idxFun : Line A I → I → Option A) := by
  intro l m h
  cases l with
  | mk lf lp =>
      cases m with
      | mk mf mp =>
          simp only at h
          subst mf
          rfl

/-- Through a fixed cube point, a line is determined by its moving support. -/
lemma line_eq_of_movingSet_eq_of_mem [Fintype I] {l m : Line A I}
    (hmove : movingSet l = movingSet m) {x : I → A}
    (hxl : x ∈ linePoints l) (hxm : x ∈ linePoints m) : l = m := by
  rcases hxl with ⟨a, ha⟩
  rcases hxm with ⟨b, hb⟩
  apply line_idxFun_injective
  funext i
  by_cases hi : i ∈ movingSet l
  · have hil : l.idxFun i = none := (mem_movingSet l i).mp hi
    have him : m.idxFun i = none := (mem_movingSet m i).mp (hmove ▸ hi)
    simp [hil, him]
  · have hil : l.idxFun i ≠ none := fun h ↦ hi ((mem_movingSet l i).mpr h)
    have him : m.idxFun i ≠ none := by
      intro h
      exact hi (hmove.symm ▸ (mem_movingSet m i).mpr h)
    cases hl : l.idxFun i with
    | none => exact (hil hl).elim
    | some c =>
        cases hm : m.idxFun i with
        | none => exact (him hm).elim
        | some d =>
            have h := congrFun (ha.trans hb.symm) i
            simp only [Line.coe_apply, hl, hm, Option.getD_some] at h
            exact congrArg some h

lemma line_apply_injective [Nontrivial A] (l : Line A I) : Function.Injective l := by
  intro a b hab
  obtain ⟨i, hi⟩ := l.proper
  have h := congrFun hab i
  simpa [Line.coe_apply, hi] using h

/-- Two distinct common cube vertices determine a combinatorial line. -/
lemma line_eq_of_two_mem_points [Nontrivial A] {l m : Line A I} {x y : I → A}
    (hxy : x ≠ y) (hxl : x ∈ linePoints l) (hxm : x ∈ linePoints m)
    (hyl : y ∈ linePoints l) (hym : y ∈ linePoints m) : l = m := by
  rcases hxl with ⟨a, rfl⟩
  rcases hyl with ⟨b, hby⟩
  rcases hxm with ⟨c, hca⟩
  rcases hym with ⟨d, hdy⟩
  have hab : a ≠ b := by
    intro hab
    apply hxy
    simpa [hab] using hby
  obtain ⟨i, hi⟩ := l.proper
  have hc : c = a := by
    have h := congrFun hca i
    cases hm : m.idxFun i with
    | none => simpa [Line.coe_apply, hi, hm] using h
    | some z =>
        have h' := congrFun (hdy.trans hby.symm) i
        simp only [Line.coe_apply, hi, hm, Option.getD_none, Option.getD_some] at h h'
        exact (hab (h.symm.trans h')).elim
  have hd : d = b := by
    have h := congrFun (hdy.trans hby.symm) i
    cases hm : m.idxFun i with
    | none => simpa [Line.coe_apply, hi, hm] using h
    | some z =>
        have h' := congrFun hca i
        simp only [Line.coe_apply, hi, hm, Option.getD_none, Option.getD_some] at h h'
        exact (hab (h'.symm.trans h)).elim
  apply line_idxFun_injective
  funext j
  have haj := congrFun hca j
  have hbj := congrFun (hdy.trans hby.symm) j
  cases hl : l.idxFun j <;> cases hm : m.idxFun j <;>
    simp_all [Line.coe_apply]

/-- Finite set of vertices of a line. -/
noncomputable def linePointFinset [Fintype A] (l : Line A I) : Finset (I → A) :=
  Finset.univ.image l

@[simp] lemma mem_linePointFinset [Fintype A] {l : Line A I} {x : I → A} :
    x ∈ linePointFinset l ↔ x ∈ linePoints l := by
  simp [linePointFinset, linePoints]

lemma card_linePointFinset [Fintype A] [Nontrivial A] (l : Line A I) :
    (linePointFinset l).card = Fintype.card A := by
  rw [linePointFinset, Finset.card_image_of_injective _ (line_apply_injective l)]
  exact Finset.card_univ

/-- Selected lines through a point and their degree. -/
noncomputable def incidentLines (S : Finset (Line A I)) (x : I → A) : Finset (Line A I) :=
  S.filter fun l ↦ x ∈ linePoints l

@[simp] lemma mem_incidentLines {S : Finset (Line A I)} {x : I → A} {l : Line A I} :
    l ∈ incidentLines S x ↔ l ∈ S ∧ x ∈ linePoints l := by
  simp [incidentLines]

noncomputable def lineDegree (S : Finset (Line A I)) (x : I → A) : ℕ :=
  (incidentLines S x).card

lemma sum_lineDegree [Fintype A] [Fintype I] [Nontrivial A]
    (S : Finset (Line A I)) :
    ∑ x : I → A, lineDegree S x = Fintype.card A * S.card := by
  let r : Line A I → (I → A) → Prop := fun l x ↦ x ∈ linePoints l
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := S) (t := (Finset.univ : Finset (I → A))) r
  have habove : ∀ l : Line A I,
      Finset.bipartiteAbove r Finset.univ l = linePointFinset l := by
    intro l
    ext x
    simp [r]
  have hbelow : ∀ x : I → A,
      Finset.bipartiteBelow r S x = incidentLines S x := by
    intro x
    ext l
    simp [r]
  simpa only [habove, hbelow, lineDegree, card_linePointFinset, Finset.sum_const_nat,
    Finset.card_univ, Nat.nsmul_eq_mul, Nat.mul_comm] using hdouble.symm

/-- The exact RRS tripod predicate. -/
def HasTripod [Fintype I] (S : Finset (Line A I)) : Prop :=
  ∃ l₁ ∈ S, ∃ l₂ ∈ S, ∃ l₃ ∈ S,
    l₁ ≠ l₂ ∧ l₂ ≠ l₃ ∧ l₃ ≠ l₁ ∧
      (∃ x, x ∈ linePoints l₁ ∧ x ∈ linePoints l₂ ∧ x ∈ linePoints l₃) ∧
      movingSet l₁ = movingSet l₂ ∪ movingSet l₃ ∧
      Disjoint (movingSet l₂) (movingSet l₃)

/-- The exact RRS triangle predicate. -/
def HasTriangle (S : Finset (Line A I)) : Prop :=
  ∃ l₁ ∈ S, ∃ l₂ ∈ S, ∃ l₃ ∈ S,
    l₁ ≠ l₂ ∧ l₂ ≠ l₃ ∧ l₃ ≠ l₁ ∧
      (linePoints l₁ ∩ linePoints l₂).Nonempty ∧
      (linePoints l₂ ∩ linePoints l₃).Nonempty ∧
      (linePoints l₃ ∩ linePoints l₁).Nonempty ∧
      linePoints l₁ ∩ linePoints l₂ ∩ linePoints l₃ = ∅

/-- Point-degree cap used in suitability. -/
def DegreeBound [Fintype A] [Fintype I] (S : Finset (Line A I)) (d : ℕ) : Prop :=
  ∀ x, lineDegree S x ≤ d

/-- Exact suitability condition of the sparse selection. -/
def Suitable [Fintype A] [Fintype I] (S : Finset (Line A I)) (d : ℕ) : Prop :=
  DegreeBound S d ∧ ¬ HasTripod S ∧ ¬ HasTriangle S

/-! ## Candidate lines supported in disjoint Hales--Jewett blocks -/

/-- Every candidate line moves inside one of the displayed coordinate blocks. -/
def SupportedInBlocks [Fintype I] {t : ℕ} (T : Finset (Line A I))
    (blocks : Fin t → Finset I) : Prop :=
  ∀ l ∈ T, ∃ j, movingSet l ⊆ blocks j

/-- Candidate lines through `x` whose moving support is contained in `B`. -/
noncomputable def blockLinesThrough [Fintype I] (T : Finset (Line A I))
    (x : I → A) (B : Finset I) : Finset (Line A I) :=
  T.filter fun l ↦ x ∈ linePoints l ∧ movingSet l ⊆ B

@[simp] lemma mem_blockLinesThrough [Fintype I] {T : Finset (Line A I)}
    {x : I → A} {B : Finset I} {l : Line A I} :
    l ∈ blockLinesThrough T x B ↔
      l ∈ T ∧ x ∈ linePoints l ∧ movingSet l ⊆ B := by
  simp [blockLinesThrough]

/-- A fixed point is on at most `2^|B|` candidate lines moving inside `B`. -/
lemma card_blockLinesThrough_le [Fintype I] (T : Finset (Line A I))
    (x : I → A) (B : Finset I) :
    (blockLinesThrough T x B).card ≤ 2 ^ B.card := by
  let source := blockLinesThrough T x B
  let target := B.powerset
  have hmap : Set.MapsTo movingSet (source : Set (Line A I))
      (target : Set (Finset I)) := by
    intro l hl
    exact Finset.mem_powerset.mpr (mem_blockLinesThrough.mp hl).2.2
  have hinj : (source : Set (Line A I)).InjOn movingSet := by
    intro l hl m hm heq
    exact line_eq_of_movingSet_eq_of_mem heq
      (mem_blockLinesThrough.mp hl).2.1 (mem_blockLinesThrough.mp hm).2.1
  have hcard := Finset.card_le_card_of_injOn movingSet hmap hinj
  simpa [source, target] using hcard

/-- The block-supported candidate lines through one point, written as a union
over the blocks. -/
noncomputable def blockUnionThrough [Fintype I] {t : ℕ}
    (T : Finset (Line A I)) (blocks : Fin t → Finset I) (x : I → A) :
    Finset (Line A I) :=
  Finset.univ.biUnion fun j ↦ blockLinesThrough T x (blocks j)

lemma incidentLines_subset_blockUnionThrough [Fintype I] {t : ℕ}
    {T : Finset (Line A I)} {blocks : Fin t → Finset I}
    (hT : SupportedInBlocks T blocks) (x : I → A) :
    incidentLines T x ⊆ blockUnionThrough T blocks x := by
  intro l hl
  obtain ⟨j, hj⟩ := hT l (mem_incidentLines.mp hl).1
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j,
    mem_blockLinesThrough.mpr ⟨(mem_incidentLines.mp hl).1,
      (mem_incidentLines.mp hl).2, hj⟩⟩

/-- In `t` blocks of size `m`, a cube point belongs to at most `t 2^m`
candidate lines.  Disjointness is not needed for this upper bound. -/
lemma lineDegree_le_blocks [Fintype I] {t m : ℕ}
    (T : Finset (Line A I)) (blocks : Fin t → Finset I)
    (hT : SupportedInBlocks T blocks) (hcard : ∀ j, (blocks j).card = m)
    (x : I → A) :
    lineDegree T x ≤ t * 2 ^ m := by
  calc
    lineDegree T x ≤ (blockUnionThrough T blocks x).card :=
      Finset.card_le_card (incidentLines_subset_blockUnionThrough hT x)
    _ ≤ ∑ j : Fin t, (blockLinesThrough T x (blocks j)).card := by
      simpa [blockUnionThrough] using
        (Finset.card_biUnion_le
          (s := (Finset.univ : Finset (Fin t)))
          (t := fun j ↦ blockLinesThrough T x (blocks j)))
    _ ≤ ∑ _j : Fin t, 2 ^ m := by
      exact Finset.sum_le_sum fun j _ ↦
        (card_blockLinesThrough_le T x (blocks j)).trans_eq (by rw [hcard j])
    _ = t * 2 ^ m := by simp

/-! ## Saturated-point exclusions -/

/-- Points at which the selected family has reached degree `d`. -/
noncomputable def saturatedPoints [Fintype A] [Fintype I]
    (S : Finset (Line A I)) (d : ℕ) : Finset (I → A) :=
  Finset.univ.filter fun x ↦ d ≤ lineDegree S x

@[simp] lemma mem_saturatedPoints [Fintype A] [Fintype I]
    {S : Finset (Line A I)} {d : ℕ} {x : I → A} :
    x ∈ saturatedPoints S d ↔ d ≤ lineDegree S x := by
  simp [saturatedPoints]

lemma card_saturatedPoints_mul_le [Fintype A] [Fintype I] [Nontrivial A]
    (S : Finset (Line A I)) (d : ℕ) :
    (saturatedPoints S d).card * d ≤ Fintype.card A * S.card := by
  calc
    (saturatedPoints S d).card * d ≤
        ∑ x ∈ saturatedPoints S d, lineDegree S x := by
      simpa [Nat.nsmul_eq_mul] using
        Finset.card_nsmul_le_sum (saturatedPoints S d) (lineDegree S) d
          (fun x hx ↦ mem_saturatedPoints.mp hx)
    _ ≤ ∑ x : I → A, lineDegree S x :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = Fintype.card A * S.card := sum_lineDegree S

/-- Lines from `T` meeting at least one point of `P`. -/
noncomputable def linesMeetingPoints (T : Finset (Line A I)) (P : Finset (I → A)) :
    Finset (Line A I) :=
  P.biUnion (incidentLines T)

@[simp] lemma mem_linesMeetingPoints {T : Finset (Line A I)} {P : Finset (I → A)}
    {l : Line A I} :
    l ∈ linesMeetingPoints T P ↔
      ∃ x ∈ P, l ∈ T ∧ x ∈ linePoints l := by
  simp [linesMeetingPoints]

lemma card_linesMeetingPoints_le (T : Finset (Line A I)) (P : Finset (I → A)) (M : ℕ)
    (hM : ∀ x ∈ P, lineDegree T x ≤ M) :
    (linesMeetingPoints T P).card ≤ P.card * M := by
  calc
    (linesMeetingPoints T P).card ≤ ∑ x ∈ P, lineDegree T x := by
      simpa [linesMeetingPoints, lineDegree] using
        (Finset.card_biUnion_le (s := P) (t := incidentLines T))
    _ ≤ P.card * M := by
      simpa [Nat.nsmul_eq_mul] using Finset.sum_le_card_nsmul P (lineDegree T) M hM

/-- Candidate additions which violate the point-degree cap. -/
noncomputable def degreeExcluded [Fintype A] [Fintype I]
    (T S : Finset (Line A I)) (d : ℕ) : Finset (Line A I) :=
  T.filter fun l ↦ ¬ DegreeBound (insert l S) d

lemma lineDegree_insert_le [Fintype A] [Fintype I]
    (S : Finset (Line A I)) (l : Line A I) (x : I → A) :
    lineDegree (insert l S) x ≤ lineDegree S x + 1 := by
  by_cases hx : x ∈ linePoints l
  · have heq : incidentLines (insert l S) x = insert l (incidentLines S x) := by
      ext q
      simp only [mem_incidentLines, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hqS, hqx⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hqS, hqx⟩
      · rintro (rfl | ⟨hqS, hqx⟩)
        · exact ⟨Or.inl rfl, hx⟩
        · exact ⟨Or.inr hqS, hqx⟩
    rw [lineDegree, heq, lineDegree]
    exact Finset.card_insert_le _ _
  · have heq : incidentLines (insert l S) x = incidentLines S x := by
      ext q
      simp only [mem_incidentLines, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hqS, hqx⟩
        · exact (hx hqx).elim
        · exact ⟨hqS, hqx⟩
      · rintro ⟨hqS, hqx⟩
        exact ⟨Or.inr hqS, hqx⟩
    rw [lineDegree, heq, lineDegree]
    omega

lemma lineDegree_insert_eq_of_not_mem [Fintype A] [Fintype I]
    (S : Finset (Line A I)) (l : Line A I) (x : I → A)
    (hx : x ∉ linePoints l) :
    lineDegree (insert l S) x = lineDegree S x := by
  unfold lineDegree incidentLines
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | hqS, hqx⟩
    · exact (hx hqx).elim
    · exact ⟨hqS, hqx⟩
  · rintro ⟨hqS, hqx⟩
    exact ⟨Or.inr hqS, hqx⟩

/-- Any actual degree-violating addition meets a point saturated in the old
family. -/
lemma degreeExcluded_subset_saturated [Fintype A] [Fintype I]
    {T S : Finset (Line A I)} {d : ℕ} (hS : DegreeBound S d) :
    degreeExcluded T S d ⊆ linesMeetingPoints T (saturatedPoints S d) := by
  intro l hl
  have hlT := (Finset.mem_filter.mp hl).1
  have hbad := (Finset.mem_filter.mp hl).2
  simp only [DegreeBound, not_forall, not_le] at hbad
  obtain ⟨x, hxbad⟩ := hbad
  have hxl : x ∈ linePoints l := by
    by_contra hnot
    rw [lineDegree_insert_eq_of_not_mem S l x hnot] at hxbad
    exact (not_lt_of_ge (hS x)) hxbad
  have hsle := hS x
  have hins := lineDegree_insert_le S l x
  have hsat : d ≤ lineDegree S x := by omega
  exact mem_linesMeetingPoints.mpr
    ⟨x, mem_saturatedPoints.mpr hsat, hlT, hxl⟩

/-- RRS (5.5), with division cleared: for block-supported candidates, the
number excluded by saturation satisfies
`excluded * d ≤ a * |S| * (t * 2^m)`. -/
theorem degreeExcluded_mul_le [Fintype A] [Fintype I] [Nontrivial A]
    {t m d : ℕ} (T S : Finset (Line A I)) (blocks : Fin t → Finset I)
    (hT : SupportedInBlocks T blocks) (hblocks : ∀ j, (blocks j).card = m)
    (hS : DegreeBound S d) :
    (degreeExcluded T S d).card * d ≤
      (Fintype.card A * S.card) * (t * 2 ^ m) := by
  have hsub := degreeExcluded_subset_saturated (T := T) hS
  have hmeet : (linesMeetingPoints T (saturatedPoints S d)).card ≤
      (saturatedPoints S d).card * (t * 2 ^ m) :=
    card_linesMeetingPoints_le T (saturatedPoints S d) (t * 2 ^ m)
      (fun x _ ↦ lineDegree_le_blocks T blocks hT hblocks x)
  have hcard : (degreeExcluded T S d).card ≤
      (saturatedPoints S d).card * (t * 2 ^ m) :=
    (Finset.card_le_card hsub).trans hmeet
  calc
    (degreeExcluded T S d).card * d
        ≤ ((saturatedPoints S d).card * (t * 2 ^ m)) * d :=
      Nat.mul_le_mul_right d hcard
    _ = ((saturatedPoints S d).card * d) * (t * 2 ^ m) := by ring
    _ ≤ (Fintype.card A * S.card) * (t * 2 ^ m) :=
      Nat.mul_le_mul_right _ (card_saturatedPoints_mul_le S d)

/-! ## Tripod exclusions -/

/-- Symmetric moving-support form of the tripod relation, with the first
argument reserved for the candidate line. -/
def TripodSupports (X U V : Finset I) : Prop :=
  (X = U ∪ V ∧ Disjoint U V) ∨
  (U = X ∪ V ∧ Disjoint X V) ∨
  (V = X ∪ U ∧ Disjoint X U)

/-- For fixed supports `U,V`, there is at most one possible third support in
a tripod. -/
lemma tripodSupports_left_unique {X Y U V : Finset I}
    (hX : TripodSupports X U V) (hY : TripodSupports Y U V) : X = Y := by
  have canonical (Z : Finset I) (hZ : TripodSupports Z U V) :
      Z = (U \ V) ∪ (V \ U) := by
    rcases hZ with ⟨rfl, hUV⟩ | ⟨hU, hZV⟩ | ⟨hV, hZU⟩
    · ext i
      have hd := Finset.disjoint_left.mp hUV
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hiU | hiV)
        · exact Or.inl ⟨hiU, hd hiU⟩
        · exact Or.inr ⟨hiV, fun hiU ↦ hd hiU hiV⟩
      · rintro (⟨hiU, -⟩ | ⟨hiV, -⟩)
        · exact Or.inl hiU
        · exact Or.inr hiV
    · ext i
      have hUi : i ∈ U ↔ i ∈ Z ∨ i ∈ V := by
        simpa only [Finset.mem_union] using Finset.ext_iff.mp hU i
      have hd := Finset.disjoint_left.mp hZV
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hiZ
        exact Or.inl ⟨hUi.mpr (Or.inl hiZ), hd hiZ⟩
      · rintro (⟨hiU, hiV⟩ | ⟨hiV, hiU⟩)
        · rcases hUi.mp hiU with hiZ | hiV'
          · exact hiZ
          · exact (hiV hiV').elim
        · exact (hiU (hUi.mpr (Or.inr hiV))).elim
    · ext i
      have hVi : i ∈ V ↔ i ∈ Z ∨ i ∈ U := by
        simpa only [Finset.mem_union] using Finset.ext_iff.mp hV i
      have hd := Finset.disjoint_left.mp hZU
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hiZ
        exact Or.inr ⟨hVi.mpr (Or.inl hiZ), hd hiZ⟩
      · rintro (⟨hiU, hiV⟩ | ⟨hiV, hiU⟩)
        · exact (hiV (hVi.mpr (Or.inr hiU))).elim
        · rcases hVi.mp hiV with hiZ | hiU'
          · exact hiZ
          · exact (hiU hiU').elim
  exact (canonical X hX).trans (canonical Y hY).symm

/-- Candidates completing a tripod with a fixed common point and fixed two
selected lines. -/
noncomputable def tripodPairCandidates [Fintype I]
    (T : Finset (Line A I)) (x : I → A) (u v : Line A I) : Finset (Line A I) :=
  T.filter fun l ↦ x ∈ linePoints l ∧
    TripodSupports (movingSet l) (movingSet u) (movingSet v)

lemma card_tripodPairCandidates_le [Fintype I]
    (T : Finset (Line A I)) (x : I → A) (u v : Line A I) :
    (tripodPairCandidates T x u v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro l hl q hq
  have hl' := Finset.mem_filter.mp hl
  have hq' := Finset.mem_filter.mp hq
  exact line_eq_of_movingSet_eq_of_mem
    (tripodSupports_left_unique hl'.2.2 hq'.2.2)
    hl'.2.1 hq'.2.1

/-- All candidates carrying a tripod certificate `(x,u,v)`. -/
noncomputable def tripodCertificateCandidates [Fintype A] [Fintype I]
    (T S : Finset (Line A I)) : Finset (Line A I) :=
  Finset.univ.biUnion fun x ↦
    (incidentLines S x).biUnion fun u ↦
      (incidentLines S x).biUnion fun v ↦ tripodPairCandidates T x u v

lemma card_tripodCertificateCandidates_le [Fintype A] [Fintype I]
    (T S : Finset (Line A I)) {d : ℕ} (hdeg : DegreeBound S d) :
    (tripodCertificateCandidates T S).card ≤
      d ^ 2 * Fintype.card (I → A) := by
  calc
    (tripodCertificateCandidates T S).card ≤
        ∑ x : I → A, ∑ u ∈ incidentLines S x,
          ∑ v ∈ incidentLines S x, (tripodPairCandidates T x u v).card := by
      simp only [tripodCertificateCandidates]
      refine (Finset.card_biUnion_le (s := (Finset.univ : Finset (I → A)))
        (t := fun x ↦ (incidentLines S x).biUnion fun u ↦
          (incidentLines S x).biUnion fun v ↦ tripodPairCandidates T x u v)).trans ?_
      exact Finset.sum_le_sum fun x _ ↦
        (Finset.card_biUnion_le (s := incidentLines S x)
          (t := fun u ↦ (incidentLines S x).biUnion fun v ↦
            tripodPairCandidates T x u v)).trans
          (Finset.sum_le_sum fun u _ ↦ Finset.card_biUnion_le)
    _ ≤ ∑ _x : I → A, ∑ _u ∈ incidentLines S _x,
          ∑ _v ∈ incidentLines S _x, 1 := by
      exact Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun u _ ↦
        Finset.sum_le_sum fun v _ ↦ card_tripodPairCandidates_le T x u v
    _ = ∑ x : I → A, (lineDegree S x) ^ 2 := by
      simp [lineDegree, pow_two]
    _ ≤ ∑ _x : I → A, d ^ 2 := by
      exact Finset.sum_le_sum fun x _ ↦ Nat.pow_le_pow_left (hdeg x) 2
    _ = d ^ 2 * Fintype.card (I → A) := by
      simp [Nat.mul_comm]

/-- Actual additions which create a tripod. -/
noncomputable def tripodExcluded [Fintype I]
    (T S : Finset (Line A I)) : Finset (Line A I) :=
  T.filter fun l ↦ HasTripod (insert l S)

lemma tripodExcluded_subset_certificates [Fintype A] [Fintype I]
    {T S : Finset (Line A I)} (hS : ¬ HasTripod S) :
    tripodExcluded T S ⊆ tripodCertificateCandidates T S := by
  intro l hl
  have hlT := (Finset.mem_filter.mp hl).1
  rcases (Finset.mem_filter.mp hl).2 with
    ⟨l₁, h₁, l₂, h₂, l₃, h₃, h₁₂, h₂₃, h₃₁,
      ⟨x, hx₁, hx₂, hx₃⟩, hsupport, hdisj⟩
  have hcert (u v : Line A I) (hu : u ∈ S) (hv : v ∈ S)
      (hxu : x ∈ linePoints u) (hxv : x ∈ linePoints v)
      (hxl : x ∈ linePoints l)
      (hsup : TripodSupports (movingSet l) (movingSet u) (movingSet v)) :
      l ∈ tripodCertificateCandidates T S := by
    exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨u, mem_incidentLines.mpr ⟨hu, hxu⟩,
        Finset.mem_biUnion.mpr ⟨v, mem_incidentLines.mpr ⟨hv, hxv⟩,
          Finset.mem_filter.mpr ⟨hlT, hxl, hsup⟩⟩⟩⟩
  simp only [Finset.mem_insert] at h₁ h₂ h₃
  rcases h₁ with rfl | h₁S
  · rcases h₂ with rfl | h₂S
    · exact (h₁₂ rfl).elim
    · rcases h₃ with rfl | h₃S
      · exact (h₃₁ rfl).elim
      · exact hcert l₂ l₃ h₂S h₃S hx₂ hx₃ hx₁
          (Or.inl ⟨hsupport, hdisj⟩)
  · rcases h₂ with rfl | h₂S
    · rcases h₃ with rfl | h₃S
      · exact (h₂₃ rfl).elim
      · exact hcert l₁ l₃ h₁S h₃S hx₁ hx₃ hx₂
          (Or.inr (Or.inl ⟨hsupport, hdisj⟩))
    · rcases h₃ with rfl | h₃S
      · exact hcert l₁ l₂ h₁S h₂S hx₁ hx₂ hx₃
          (Or.inr (Or.inl ⟨by simpa [Finset.union_comm] using hsupport,
            hdisj.symm⟩))
      · exact (hS ⟨l₁, h₁S, l₂, h₂S, l₃, h₃S,
          h₁₂, h₂₃, h₃₁, ⟨x, hx₁, hx₂, hx₃⟩,
          hsupport, hdisj⟩).elim

/-- RRS (5.6): at most `d² |A|^n` additions complete a tripod. -/
theorem card_tripodExcluded_le [Fintype A] [Fintype I]
    (T S : Finset (Line A I)) {d : ℕ}
    (hdeg : DegreeBound S d) (htripod : ¬ HasTripod S) :
    (tripodExcluded T S).card ≤ d ^ 2 * Fintype.card (I → A) :=
  (Finset.card_le_card (tripodExcluded_subset_certificates htripod)).trans
    (card_tripodCertificateCandidates_le T S hdeg)

/-! ## Triangle exclusions -/

/-- Candidate lines through two prescribed distinct points. -/
noncomputable def twoPointCandidates (T : Finset (Line A I))
    (x y : I → A) : Finset (Line A I) :=
  T.filter fun l ↦ x ≠ y ∧ x ∈ linePoints l ∧ y ∈ linePoints l

@[simp] lemma mem_twoPointCandidates {T : Finset (Line A I)}
    {x y : I → A} {l : Line A I} :
    l ∈ twoPointCandidates T x y ↔
      l ∈ T ∧ x ≠ y ∧ x ∈ linePoints l ∧ y ∈ linePoints l := by
  simp [twoPointCandidates]

lemma card_twoPointCandidates_le [Nontrivial A]
    (T : Finset (Line A I)) (x y : I → A) :
    (twoPointCandidates T x y).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro l hl q hq
  have hl' := Finset.mem_filter.mp hl
  have hq' := Finset.mem_filter.mp hq
  exact line_eq_of_two_mem_points hl'.2.1 hl'.2.2.1 hq'.2.2.1
    hl'.2.2.2 hq'.2.2.2

/-- The certificate count for a triangle follows the chain
`x --u-- z --v-- y`; the candidate line is the unique line through `x,y`. -/
noncomputable def triangleCertificateCandidates [Fintype A] [Fintype I]
    (T S : Finset (Line A I)) : Finset (Line A I) :=
  Finset.univ.biUnion fun x ↦
    (incidentLines S x).biUnion fun u ↦
      (linePointFinset u).biUnion fun z ↦
        (incidentLines S z).biUnion fun v ↦
          (linePointFinset v).biUnion fun y ↦ twoPointCandidates T x y

lemma card_triangleCertificateCandidates_le [Fintype A] [Fintype I] [Nontrivial A]
    (T S : Finset (Line A I)) {d : ℕ} (hdeg : DegreeBound S d) :
    (triangleCertificateCandidates T S).card ≤
      (Fintype.card A * d) ^ 2 * Fintype.card (I → A) := by
  have hunion : (triangleCertificateCandidates T S).card ≤
      ∑ x : I → A, ∑ u ∈ incidentLines S x, ∑ z ∈ linePointFinset u,
        ∑ v ∈ incidentLines S z, ∑ y ∈ linePointFinset v,
          (twoPointCandidates T x y).card := by
    simp only [triangleCertificateCandidates]
    refine (Finset.card_biUnion_le
      (s := (Finset.univ : Finset (I → A)))
      (t := fun x ↦ (incidentLines S x).biUnion fun u ↦
        (linePointFinset u).biUnion fun z ↦
          (incidentLines S z).biUnion fun v ↦
            (linePointFinset v).biUnion fun y ↦ twoPointCandidates T x y)).trans ?_
    exact Finset.sum_le_sum fun x _ ↦
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun u _ ↦
        (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun z _ ↦
          (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun v _ ↦
            Finset.card_biUnion_le))))))
  have hpairs :
      (∑ x : I → A, ∑ u ∈ incidentLines S x, ∑ z ∈ linePointFinset u,
        ∑ v ∈ incidentLines S z, ∑ y ∈ linePointFinset v,
          (twoPointCandidates T x y).card) ≤
      ∑ x : I → A, ∑ u ∈ incidentLines S x, ∑ z ∈ linePointFinset u,
        ∑ v ∈ incidentLines S z, ∑ _y ∈ linePointFinset v, 1 := by
    exact Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun u _ ↦
      Finset.sum_le_sum fun z _ ↦ Finset.sum_le_sum fun v _ ↦
        Finset.sum_le_sum fun y _ ↦ card_twoPointCandidates_le T x y
  have hv (z : I → A) :
      ∑ v ∈ incidentLines S z, ∑ _y ∈ linePointFinset v, 1 ≤
        d * Fintype.card A := by
    calc
      ∑ v ∈ incidentLines S z, ∑ _y ∈ linePointFinset v, 1 =
          lineDegree S z * Fintype.card A := by
        simp [lineDegree, card_linePointFinset]
      _ ≤ d * Fintype.card A := Nat.mul_le_mul_right _ (hdeg z)
  have hz (u : Line A I) :
      ∑ z ∈ linePointFinset u,
          ∑ v ∈ incidentLines S z, ∑ _y ∈ linePointFinset v, 1 ≤
        Fintype.card A * (d * Fintype.card A) := by
    calc
      ∑ z ∈ linePointFinset u,
          ∑ v ∈ incidentLines S z, ∑ _y ∈ linePointFinset v, 1 ≤
          ∑ _z ∈ linePointFinset u, d * Fintype.card A :=
        Finset.sum_le_sum fun z _ ↦ hv z
      _ = Fintype.card A * (d * Fintype.card A) := by
        simp [card_linePointFinset]
  have hu (x : I → A) :
      ∑ u ∈ incidentLines S x, ∑ z ∈ linePointFinset u,
          ∑ v ∈ incidentLines S z, ∑ _y ∈ linePointFinset v, 1 ≤
        d * (Fintype.card A * (d * Fintype.card A)) := by
    calc
      ∑ u ∈ incidentLines S x, ∑ z ∈ linePointFinset u,
          ∑ v ∈ incidentLines S z, ∑ _y ∈ linePointFinset v, 1 ≤
          ∑ _u ∈ incidentLines S x,
            Fintype.card A * (d * Fintype.card A) :=
        Finset.sum_le_sum fun u _ ↦ hz u
      _ = lineDegree S x * (Fintype.card A * (d * Fintype.card A)) := by
        simp [lineDegree]
      _ ≤ d * (Fintype.card A * (d * Fintype.card A)) :=
        Nat.mul_le_mul_right _ (hdeg x)
  calc
    (triangleCertificateCandidates T S).card ≤
        ∑ x : I → A, ∑ u ∈ incidentLines S x, ∑ z ∈ linePointFinset u,
          ∑ v ∈ incidentLines S z, ∑ y ∈ linePointFinset v,
            (twoPointCandidates T x y).card := hunion
    _ ≤ ∑ x : I → A, ∑ u ∈ incidentLines S x, ∑ z ∈ linePointFinset u,
          ∑ v ∈ incidentLines S z, ∑ _y ∈ linePointFinset v, 1 := hpairs
    _ ≤ ∑ _x : I → A,
          d * (Fintype.card A * (d * Fintype.card A)) :=
      Finset.sum_le_sum fun x _ ↦ hu x
    _ = (Fintype.card A * d) ^ 2 * Fintype.card (I → A) := by
      simp [pow_two]
      ring

/-- Actual additions which create a triangle. -/
noncomputable def triangleExcluded
    (T S : Finset (Line A I)) : Finset (Line A I) :=
  T.filter fun l ↦ HasTriangle (insert l S)

lemma triangleExcluded_subset_certificates [Fintype A] [Fintype I] [Nontrivial A]
    {T S : Finset (Line A I)} (hS : ¬ HasTriangle S) :
    triangleExcluded T S ⊆ triangleCertificateCandidates T S := by
  intro l hl
  have hlT := (Finset.mem_filter.mp hl).1
  rcases (Finset.mem_filter.mp hl).2 with
    ⟨l₁, h₁, l₂, h₂, l₃, h₃, h₁₂, h₂₃, h₃₁,
      ⟨x₁₂, hx₁, hx₂⟩, ⟨x₂₃, hx₂', hx₃⟩,
      ⟨x₃₁, hx₃', hx₁'⟩, hempty⟩
  have hpairs (p q : I → A)
      (hp₁ : p ∈ linePoints l₁) (hp₂ : p ∈ linePoints l₂)
      (hq₃ : q ∈ linePoints l₃) (hq₁ : q ∈ linePoints l₁) : p ≠ q := by
    intro hpq
    subst q
    have : p ∈ linePoints l₁ ∩ linePoints l₂ ∩ linePoints l₃ :=
      ⟨⟨hp₁, hp₂⟩, hq₃⟩
    simpa [hempty] using this
  have hne₂₃₁₂ : x₂₃ ≠ x₁₂ := by
    intro h
    subst x₂₃
    have : x₁₂ ∈ linePoints l₁ ∩ linePoints l₂ ∩ linePoints l₃ :=
      ⟨⟨hx₁, hx₂'⟩, hx₃⟩
    simpa [hempty] using this
  have hne₃₁₂₃ : x₃₁ ≠ x₂₃ := by
    intro h
    subst x₃₁
    have : x₂₃ ∈ linePoints l₁ ∩ linePoints l₂ ∩ linePoints l₃ :=
      ⟨⟨hx₁', hx₂'⟩, hx₃⟩
    simpa [hempty] using this
  have hcert (p z q : I → A) (u v : Line A I)
      (hu : u ∈ S) (hv : v ∈ S)
      (hpl : p ∈ linePoints l) (hpu : p ∈ linePoints u)
      (hzu : z ∈ linePoints u) (hzv : z ∈ linePoints v)
      (hqv : q ∈ linePoints v) (hql : q ∈ linePoints l)
      (hpq : p ≠ q) : l ∈ triangleCertificateCandidates T S := by
    have hlpair : l ∈ twoPointCandidates T p q := by
      exact mem_twoPointCandidates.mpr ⟨hlT, hpq, hpl, hql⟩
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨u, mem_incidentLines.mpr ⟨hu, hpu⟩,
        Finset.mem_biUnion.mpr ⟨z, mem_linePointFinset.mpr hzu,
          Finset.mem_biUnion.mpr ⟨v, mem_incidentLines.mpr ⟨hv, hzv⟩,
            Finset.mem_biUnion.mpr ⟨q, mem_linePointFinset.mpr hqv,
              hlpair⟩⟩⟩⟩⟩
  simp only [Finset.mem_insert] at h₁ h₂ h₃
  rcases h₁ with rfl | h₁S
  · rcases h₂ with rfl | h₂S
    · exact (h₁₂ rfl).elim
    · rcases h₃ with rfl | h₃S
      · exact (h₃₁ rfl).elim
      · exact hcert x₁₂ x₂₃ x₃₁ l₂ l₃ h₂S h₃S
          hx₁ hx₂ hx₂' hx₃ hx₃' hx₁'
          (hpairs x₁₂ x₃₁ hx₁ hx₂ hx₃' hx₁')
  · rcases h₂ with rfl | h₂S
    · rcases h₃ with rfl | h₃S
      · exact (h₂₃ rfl).elim
      · exact hcert x₂₃ x₃₁ x₁₂ l₃ l₁ h₃S h₁S
          hx₂' hx₃ hx₃' hx₁' hx₁ hx₂
          hne₂₃₁₂
    · rcases h₃ with rfl | h₃S
      · exact hcert x₃₁ x₁₂ x₂₃ l₁ l₂ h₁S h₂S
          hx₃' hx₁' hx₁ hx₂ hx₂' hx₃
          hne₃₁₂₃
      · exact (hS ⟨l₁, h₁S, l₂, h₂S, l₃, h₃S,
          h₁₂, h₂₃, h₃₁, ⟨x₁₂, hx₁, hx₂⟩,
          ⟨x₂₃, hx₂', hx₃⟩, ⟨x₃₁, hx₃', hx₁'⟩,
          hempty⟩).elim

/-- RRS (5.7): at most `(a d)² a^n` additions complete a triangle. -/
theorem card_triangleExcluded_le [Fintype A] [Fintype I] [Nontrivial A]
    (T S : Finset (Line A I)) {d : ℕ}
    (hdeg : DegreeBound S d) (htriangle : ¬ HasTriangle S) :
    (triangleExcluded T S).card ≤
      (Fintype.card A * d) ^ 2 * Fintype.card (I → A) :=
  (Finset.card_le_card (triangleExcluded_subset_certificates htriangle)).trans
    (card_triangleCertificateCandidates_le T S hdeg)

/-! ## Combined non-addable bound -/

/-- The exact set of candidate lines whose insertion destroys suitability. -/
noncomputable def nonaddable [Fintype A] [Fintype I]
    (T S : Finset (Line A I)) (d : ℕ) : Finset (Line A I) :=
  T.filter fun l ↦ ¬ Suitable (insert l S) d

/-- Every non-addable candidate is excluded by saturation, a new tripod, or
a new triangle. -/
lemma nonaddable_subset_three_exclusions [Fintype A] [Fintype I]
    {T S : Finset (Line A I)} {d : ℕ} :
    nonaddable T S d ⊆
      degreeExcluded T S d ∪ tripodExcluded T S ∪ triangleExcluded T S := by
  intro l hl
  have hl' := Finset.mem_filter.mp hl
  by_cases hdeg : DegreeBound (insert l S) d
  · by_cases htripod : HasTripod (insert l S)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hl'.1, htripod⟩))
    · have htriangle : HasTriangle (insert l S) := by
        exact Classical.byContradiction fun hn ↦
          hl'.2 ⟨hdeg, htripod, hn⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hl'.1, htriangle⟩)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hl'.1, hdeg⟩))

lemma card_nonaddable_le_three [Fintype A] [Fintype I]
    (T S : Finset (Line A I)) (d : ℕ) :
    (nonaddable T S d).card ≤
      (degreeExcluded T S d).card + (tripodExcluded T S).card +
        (triangleExcluded T S).card := by
  calc
    (nonaddable T S d).card ≤
        (degreeExcluded T S d ∪ tripodExcluded T S ∪ triangleExcluded T S).card :=
      Finset.card_le_card nonaddable_subset_three_exclusions
    _ ≤ (degreeExcluded T S d ∪ tripodExcluded T S).card +
        (triangleExcluded T S).card :=
      Finset.card_union_le (degreeExcluded T S d ∪ tripodExcluded T S)
        (triangleExcluded T S)
    _ ≤ ((degreeExcluded T S d).card + (tripodExcluded T S).card) +
        (triangleExcluded T S).card :=
      Nat.add_le_add_right
        (Finset.card_union_le (degreeExcluded T S d) (tripodExcluded T S)) _

/-- Combined cleared-denominator estimate for block-supported candidates.

The three summands are respectively the saturated-point, tripod, and triangle
certificate bounds. -/
theorem nonaddable_mul_le [Fintype A] [Fintype I] [Nontrivial A]
    {t m d : ℕ} (T S : Finset (Line A I)) (blocks : Fin t → Finset I)
    (hT : SupportedInBlocks T blocks) (hblocks : ∀ j, (blocks j).card = m)
    (hS : Suitable S d) :
    (nonaddable T S d).card * d ≤
      (Fintype.card A * S.card) * (t * 2 ^ m) +
        (d ^ 2 * Fintype.card (I → A) +
          (Fintype.card A * d) ^ 2 * Fintype.card (I → A)) * d := by
  have hcard := card_nonaddable_le_three T S d
  have hdegree := degreeExcluded_mul_le T S blocks hT hblocks hS.1
  have htripod := card_tripodExcluded_le T S hS.1 hS.2.1
  have htriangle := card_triangleExcluded_le T S hS.1 hS.2.2
  calc
    (nonaddable T S d).card * d ≤
        ((degreeExcluded T S d).card + (tripodExcluded T S).card +
          (triangleExcluded T S).card) * d := Nat.mul_le_mul_right d hcard
    _ = (degreeExcluded T S d).card * d +
        ((tripodExcluded T S).card + (triangleExcluded T S).card) * d := by ring
    _ ≤ (Fintype.card A * S.card) * (t * 2 ^ m) +
        (d ^ 2 * Fintype.card (I → A) +
          (Fintype.card A * d) ^ 2 * Fintype.card (I → A)) * d := by
      exact Nat.add_le_add hdegree (Nat.mul_le_mul_right d (Nat.add_le_add htripod htriangle))

/-- The explicit parameter inequality used by the greedy sparse-selection
lemma.  Its conclusion says that fewer than a `1/(2 A₀)` fraction of all
candidates are non-addable. -/
theorem nonaddable_fraction [Fintype A] [Fintype I] [Nontrivial A]
    {t m d A₀ : ℕ} (T S : Finset (Line A I)) (blocks : Fin t → Finset I)
    (hT : SupportedInBlocks T blocks) (hblocks : ∀ j, (blocks j).card = m)
    (hS : Suitable S d)
    (hparam : (2 * A₀) *
      ((Fintype.card A * S.card) * (t * 2 ^ m) +
        (d ^ 2 * Fintype.card (I → A) +
          (Fintype.card A * d) ^ 2 * Fintype.card (I → A)) * d) <
      d * T.card) :
    (2 * A₀) * (nonaddable T S d).card < T.card := by
  have hb := nonaddable_mul_le T S blocks hT hblocks hS
  have hmul := Nat.mul_le_mul_left (2 * A₀) hb
  have hchain : ((2 * A₀) * (nonaddable T S d).card) * d < T.card * d := by
    calc
      ((2 * A₀) * (nonaddable T S d).card) * d
          = (2 * A₀) * ((nonaddable T S d).card * d) := by ring
      _ ≤ (2 * A₀) *
          ((Fintype.card A * S.card) * (t * 2 ^ m) +
            (d ^ 2 * Fintype.card (I → A) +
              (Fintype.card A * d) ^ 2 * Fintype.card (I → A)) * d) := hmul
      _ < d * T.card := hparam
      _ = T.card * d := by ring
  exact Nat.lt_of_mul_lt_mul_right hchain

end Erdos847LineExclusions

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/SparseSelection.lean` -/

section
/-!
# A finite greedy sparse-selection lemma

This file isolates the counting argument used to choose a sparse family while successively
destroying all bad colourings.  It deliberately uses only natural-number cross multiplication.

`X j` is the `j`th stratum of candidates, `Hit x c` says that candidate `x` destroys colouring
`c`, and `Suitable S` is the sparsity condition imposed on a chosen family.  All strata have the
same cardinality `L`.  The two substantive hypotheses are:

* every colouring is hit by at least a `1 / A` fraction of one stratum;
* while fewer than `q` candidates have been selected, the non-addable candidates in every
  stratum form less than a `1 / (2A)` fraction.

Thus, among all `m` strata, averaging supplies an addable candidate hitting at least a
`1 / (2Am)` fraction of the currently bad colourings.
-/

namespace Erdos847SparseSelection

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

section Definitions

variable {Candidate Colour : Type*}

/-- The colourings not hit by any member of `S`. -/
def badColourings (colours : Finset Colour) (Hit : Candidate → Colour → Prop)
    (S : Finset Candidate) : Finset Colour := by
  classical
  exact colours.filter fun c ↦ ∀ x ∈ S, ¬ Hit x c

@[simp] lemma mem_badColourings {colours : Finset Colour} {Hit : Candidate → Colour → Prop}
    {S : Finset Candidate} {c : Colour} :
    c ∈ badColourings colours Hit S ↔ c ∈ colours ∧ ∀ x ∈ S, ¬ Hit x c := by
  classical
  simp [badColourings]

@[simp] lemma badColourings_empty (colours : Finset Colour) (Hit : Candidate → Colour → Prop) :
    badColourings colours Hit ∅ = colours := by
  classical
  ext c
  simp

lemma badColourings_insert (colours : Finset Colour) (Hit : Candidate → Colour → Prop)
    (x : Candidate) (S : Finset Candidate) :
    badColourings colours Hit (insert x S) =
      (badColourings colours Hit S).filter fun c ↦ ¬ Hit x c := by
  classical
  ext c
  simp [badColourings, and_assoc, and_left_comm, and_comm]

end Definitions

section Equalize

variable {Candidate : Type*}

end Equalize

section Iteration

variable {Candidate Colour : Type*}

/-- Multiplicative decay propagates through any prescribed number of greedy steps. -/
theorem iterate_decay
    (colours : Finset Colour) (Hit : Candidate → Colour → Prop)
    (Suitable : Finset Candidate → Prop) {D q : ℕ} (hD : 0 < D)
    (hempty : Suitable ∅)
    (hstep : ∀ (S : Finset Candidate), Suitable S → S.card < q →
      (badColourings colours Hit S).Nonempty →
      ∃ x, Suitable (insert x S) ∧
        D * (badColourings colours Hit (insert x S)).card ≤
          (D - 1) * (badColourings colours Hit S).card)
    (t : ℕ) (ht : t ≤ q) :
    ∃ S : Finset Candidate, Suitable S ∧ S.card ≤ t ∧
      D ^ t * (badColourings colours Hit S).card ≤ (D - 1) ^ t * colours.card := by
  induction t with
  | zero =>
      refine ⟨∅, hempty, by simp, ?_⟩
      simp
  | succ t ih =>
      have htq : t ≤ q := t.le_succ.trans ht
      obtain ⟨S, hS, hSt, hdec⟩ := ih htq
      by_cases hbad : (badColourings colours Hit S).Nonempty
      · have hSq : S.card < q := hSt.trans_lt (Nat.lt_of_succ_le ht)
        obtain ⟨x, hxSuit, hxdec⟩ := hstep S hS hSq hbad
        refine ⟨insert x S, hxSuit, ?_, ?_⟩
        · exact (Finset.card_insert_le x S).trans (Nat.succ_le_succ hSt)
        · calc
            D ^ (t + 1) * (badColourings colours Hit (insert x S)).card =
                D ^ t * (D * (badColourings colours Hit (insert x S)).card) := by
                  rw [pow_succ]
                  ring
            _ ≤ D ^ t * ((D - 1) * (badColourings colours Hit S).card) :=
              Nat.mul_le_mul_left _ hxdec
            _ = (D - 1) * (D ^ t * (badColourings colours Hit S).card) := by ring
            _ ≤ (D - 1) * ((D - 1) ^ t * colours.card) :=
              Nat.mul_le_mul_left _ hdec
            _ = (D - 1) ^ (t + 1) * colours.card := by
              rw [pow_succ]
              ring
      · refine ⟨S, hS, hSt.trans (Nat.le_succ t), ?_⟩
        have hz : (badColourings colours Hit S).card = 0 := Finset.not_nonempty_iff_eq_empty.mp hbad ▸ rfl
        simp [hz]

end Iteration

section NumericalDecay

/-- The first two terms of the binomial expansion, in a form requiring no division. -/
lemma pow_add_one_lower (a n : ℕ) :
    a ^ (n + 1) + (n + 1) * a ^ n ≤ (a + 1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        a ^ (n + 1 + 1) + (n + 1 + 1) * a ^ (n + 1) ≤
            a ^ (n + 1 + 1) + (n + 1 + 1) * a ^ (n + 1) +
              (n + 1) * a ^ n := Nat.le_add_right _ _
        _ = (a ^ (n + 1) + (n + 1) * a ^ n) * (a + 1) := by
          rw [pow_succ, pow_succ]
          ring
        _ ≤ (a + 1) ^ (n + 1) * (a + 1) := Nat.mul_le_mul_right _ ih
        _ = (a + 1) ^ (n + 1 + 1) := by
          simp only [pow_succ]

/-- In a block of `D` steps, multiplying by `(D-1)/D` at each step loses at least a factor two. -/
lemma two_mul_pred_pow_le_pow {D : ℕ} (hD : 2 ≤ D) :
    2 * (D - 1) ^ D ≤ D ^ D := by
  have hDpos : 1 ≤ D := le_trans (by decide) hD
  have hdecomp : D - 1 + 1 = D := Nat.sub_add_cancel hDpos
  have hpow : (D - 1) ^ D ≤ D * (D - 1) ^ (D - 1) := by
    calc
      (D - 1) ^ D = (D - 1) ^ ((D - 1) + 1) :=
        congrArg (fun n : ℕ ↦ (D - 1) ^ n) hdecomp.symm
      _ = (D - 1) ^ (D - 1) * (D - 1) := by rw [pow_succ]
      _ ≤ (D - 1) ^ (D - 1) * D :=
        Nat.mul_le_mul_left _ (Nat.sub_le D 1)
      _ = D * (D - 1) ^ (D - 1) := Nat.mul_comm _ _
  calc
    2 * (D - 1) ^ D = (D - 1) ^ D + (D - 1) ^ D := by omega
    _ ≤ (D - 1) ^ D + D * (D - 1) ^ (D - 1) := Nat.add_le_add_left hpow _
    _ ≤ ((D - 1) + 1) ^ ((D - 1) + 1) := by
      simpa only [hdecomp] using pow_add_one_lower (D - 1) (D - 1)
    _ = D ^ D := by rw [hdecomp]

end NumericalDecay

section OneStep

variable {Candidate Colour : Type*}
variable (X : Fin m → Finset Candidate) (colours : Finset Colour)
  (Hit : Candidate → Colour → Prop) (Suitable : Finset Candidate → Prop)

/-- The finite averaging step.  `weight` represents harmless replication of a stratum; the
identity `weight j * #(X j) = L` says that all replicated strata have the same size.  Thus this
statement applies directly when the unreplicated strata have different positive sizes.

`D = 2 * A * m` is kept explicit in the conclusion. -/
theorem exists_addable_hits_many
    (weight : Fin m → ℕ) {A L q : ℕ} (hA : 0 < A) (hL : 0 < L)
    (hcard : ∀ j, weight j * (X j).card = L)
    (hdense : ∀ c ∈ colours, ∃ j,
      (X j).card ≤ A * ((X j).filter fun x ↦ Hit x c).card)
    (hnonadd : ∀ (S : Finset Candidate), Suitable S → S.card < q → ∀ j,
      2 * A * ((X j).filter fun x ↦ ¬ Suitable (insert x S)).card < (X j).card)
    {S : Finset Candidate} (hS : Suitable S) (hSq : S.card < q)
    (hbad : (badColourings colours Hit S).Nonempty) :
    ∃ j x, x ∈ X j ∧ Suitable (insert x S) ∧
      (badColourings colours Hit S).card ≤
        (2 * A * m) * ((badColourings colours Hit S).filter fun c ↦ Hit x c).card := by
  classical
  let B := badColourings colours Hit S
  let goodCount : Fin m → Colour → ℕ := fun j c ↦
    weight j * ((X j).filter fun x ↦ Hit x c ∧ Suitable (insert x S)).card
  have hgood (c : Colour) (hc : c ∈ B) :
      L ≤ 2 * A * ∑ j, goodCount j c := by
    obtain ⟨j, hj⟩ := hdense c (mem_badColourings.mp hc).1
    let H := ((X j).filter fun x ↦ Hit x c).card
    let G := ((X j).filter fun x ↦ Hit x c ∧ Suitable (insert x S)).card
    let N := ((X j).filter fun x ↦ ¬ Suitable (insert x S)).card
    have hsplit : H ≤ G + N := by
      let Y := (X j).filter fun x ↦ Hit x c
      have hpart := Finset.card_filter_add_card_filter_not
        (s := Y) (fun x ↦ Suitable (insert x S))
      have hfirst : (Y.filter fun x ↦ Suitable (insert x S)).card = G := by
        congr 1
        ext x
        simp [Y, G, and_assoc, and_left_comm, and_comm]
      have hsecond : (Y.filter fun x ↦ ¬ Suitable (insert x S)).card ≤ N := by
        apply Finset.card_le_card
        intro x hx
        have hx' := Finset.mem_filter.mp hx
        have hxY := Finset.mem_filter.mp hx'.1
        exact Finset.mem_filter.mpr ⟨hxY.1, hx'.2⟩
      dsimp [H]
      rw [← hpart, hfirst]
      exact Nat.add_le_add_left hsecond G
    have hd : (X j).card ≤ A * H := hj
    have hn : 2 * A * N < (X j).card := hnonadd S hS hSq j
    have hAG : (X j).card ≤ 2 * A * G := by
      let AG := A * G
      let AN := A * N
      have hAH : A * H ≤ AG + AN := by
        dsimp [AG, AN]
        rw [← Nat.mul_add]
        exact Nat.mul_le_mul_left A hsplit
      have hn' : 2 * AN < (X j).card := by
        simpa [AN, Nat.mul_assoc] using hn
      have hd' : (X j).card ≤ AG + AN := hd.trans hAH
      have hAG' : (X j).card ≤ 2 * AG := by omega
      simpa [AG, Nat.mul_assoc] using hAG'
    have hweighted : L ≤ 2 * A * goodCount j c := by
      calc
        L = weight j * (X j).card := (hcard j).symm
        _ ≤ weight j * (2 * A * G) := Nat.mul_le_mul_left (weight j) hAG
        _ = 2 * A * goodCount j c := by
          simp [goodCount, G]
          ring
    calc
      L ≤ 2 * A * goodCount j c := hweighted
      _ ≤ 2 * A * ∑ k, goodCount k c := by
        exact Nat.mul_le_mul_left (2 * A)
          (Finset.single_le_sum (f := fun k : Fin m ↦ goodCount k c)
            (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j))
  let incidence : Fin m → Candidate → ℕ := fun j x ↦
    weight j * (if Suitable (insert x S) then (B.filter fun c ↦ Hit x c).card else 0)
  have hincidence :
      (∑ c ∈ B, ∑ j, goodCount j c) = ∑ j, ∑ x ∈ X j, incidence j x := by
    rw [Finset.sum_comm]
    congr 1
    funext j
    simp_rw [goodCount, incidence]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    congr 1
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hsx : Suitable (insert x S)
    · simp [hsx, B]
    · simp [hsx]
  have hlower : L * B.card ≤ 2 * A * ∑ j, ∑ x ∈ X j, incidence j x := by
    calc
      L * B.card = ∑ c ∈ B, L := by simp [Nat.mul_comm]
      _ ≤ ∑ c ∈ B, 2 * A * ∑ j, goodCount j c := by
        exact Finset.sum_le_sum fun c hc ↦ hgood c hc
      _ = 2 * A * ∑ j, ∑ x ∈ X j, incidence j x := by
        rw [← hincidence]
        simp only [Finset.mul_sum]
  by_contra! hno
  have hpoint (j : Fin m) (x : Candidate) (hx : x ∈ X j) :
      (2 * A * m) * incidence j x < weight j * B.card := by
    by_cases hsx : Suitable (insert x S)
    · have hw : 0 < weight j := by
        have hp : 0 < weight j * (X j).card := by rw [hcard j]; exact hL
        exact Nat.pos_of_mul_pos_right hp
      have := (Nat.mul_lt_mul_left hw).mpr (hno j x hx hsx)
      calc
        (2 * A * m) * incidence j x =
            weight j * ((2 * A * m) * (B.filter fun c ↦ Hit x c).card) := by
              simp [incidence, hsx]
              ring
        _ < weight j * B.card := by simpa [B] using this
    · have hw : 0 < weight j := by
        have hp : 0 < weight j * (X j).card := by rw [hcard j]; exact hL
        exact Nat.pos_of_mul_pos_right hp
      simp [incidence, hsx, B, hw, hbad.card_pos]
  have hm : 0 < m := by
    obtain ⟨c, hc⟩ := hbad
    obtain ⟨j, -⟩ := hdense c (mem_badColourings.mp hc).1
    exact Fin.pos_iff_nonempty.mpr ⟨j⟩
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hupper :
      (2 * A * m) * (∑ j, ∑ x ∈ X j, incidence j x) < m * (L * B.card) := by
    rw [Finset.mul_sum]
    calc
      ∑ j, (2 * A * m) * ∑ x ∈ X j, incidence j x =
          ∑ j, ∑ x ∈ X j, (2 * A * m) * incidence j x := by
            congr 1
            funext j
            rw [Finset.mul_sum]
      _ < ∑ j, ∑ _x ∈ X j, weight j * B.card := by
        apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        intro j _
        apply Finset.sum_lt_sum_of_nonempty
        · have : 0 < (X j).card := by
            have hp : 0 < weight j * (X j).card := by rw [hcard j]; exact hL
            exact Nat.pos_of_mul_pos_left hp
          exact Finset.card_pos.mp this
        · exact fun x hx ↦ hpoint j x hx
      _ = m * (L * B.card) := by
        calc
          ∑ j, ∑ _x ∈ X j, weight j * B.card = ∑ _j : Fin m, L * B.card := by
            apply Finset.sum_congr rfl
            intro j _
            simp only [Finset.sum_const, nsmul_eq_mul]
            calc
              (X j).card * (weight j * B.card) =
                  (weight j * (X j).card) * B.card := by ring
              _ = L * B.card := by rw [hcard j]
          _ = m * (L * B.card) := by simp
  have hlower' : m * (L * B.card) ≤ (2 * A * m) * (∑ j, ∑ x ∈ X j, incidence j x) := by
    calc
      m * (L * B.card) ≤ m * (2 * A * ∑ j, ∑ x ∈ X j, incidence j x) :=
        Nat.mul_le_mul_left m hlower
      _ = (2 * A * m) * (∑ j, ∑ x ∈ X j, incidence j x) := by ring
  exact (not_lt_of_ge hlower') hupper

end OneStep

section Compose

variable {Candidate Colour : Type*}

end Compose

end
end Erdos847SparseSelection

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/SparseLines.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Sparse Hales--Jewett line systems for Erdős Problem 847

This scratch module isolates the finite line-system input in the
Reiher--Rödl--Sales construction.  It provides:

* precise finitary definitions of the Ramsey, tripod, and triangle properties;
* rigidity of combinatorial lines (two distinct common points determine a line);
* the ordinary Hales--Jewett theorem packaged as a finite Ramsey line family;
* support-size strata for the later sparse-selection counting argument.

The final sparse-selection argument is stated only after all its constituent
predicates have been made explicit.  Every declaration in this file is proved;
there are no proof placeholders.
-/

namespace Erdos847SparseLines

open Function Set
open Combinatorics

attribute [local instance] Classical.propDecidable

universe u v w

variable {A : Type u} {I : Type v} {K : Type w}

/-- The set of cube vertices lying on a combinatorial line. -/
def linePoints (l : Line A I) : Set (I → A) := Set.range l

@[simp]
lemma mem_linePoints (l : Line A I) (x : I → A) :
    x ∈ linePoints l ↔ ∃ a, l a = x := Iff.rfl

/-- Evaluation on a combinatorial line is injective as soon as the alphabet is nontrivial. -/
lemma line_apply_injective [Nontrivial A] (l : Line A I) : Function.Injective l := by
  intro a b hab
  obtain ⟨i, hi⟩ := l.proper
  have h := congrFun hab i
  simpa [Line.coe_apply, hi] using h

/-- Two parameter values determine the line as a function. -/
lemma line_eq_of_apply_eq_apply [Nontrivial A] {l m : Line A I} {a b : A}
    (hab : a ≠ b) (ha : l a = m a) (hb : l b = m b) : l = m := by
  ext i
  have hai := congrFun ha i
  have hbi := congrFun hb i
  cases hl : l.idxFun i <;> cases hm : m.idxFun i <;>
    simp_all [Line.coe_apply]

/-- Two distinct common cube vertices determine a combinatorial line uniquely. -/
lemma line_eq_of_two_mem_points [Nontrivial A] {l m : Line A I} {x y : I → A}
    (hxy : x ≠ y) (hxl : x ∈ linePoints l) (hxm : x ∈ linePoints m)
    (hyl : y ∈ linePoints l) (hym : y ∈ linePoints m) : l = m := by
  rcases hxl with ⟨a, rfl⟩
  rcases hyl with ⟨b, hby⟩
  rcases hxm with ⟨c, hca⟩
  rcases hym with ⟨d, hdy⟩
  have hab : a ≠ b := by
    intro hab
    apply hxy
    simpa [hab] using hby
  obtain ⟨i, hi⟩ := l.proper
  have hc : c = a := by
    have h := congrFun hca i
    cases hm : m.idxFun i with
    | none => simpa [Line.coe_apply, hi, hm] using h
    | some z =>
        have h' := congrFun (hdy.trans hby.symm) i
        simp only [Line.coe_apply, hi, hm, Option.getD_none, Option.getD_some] at h h'
        exact (hab (h.symm.trans h')).elim
  have hd : d = b := by
    have h := congrFun (hdy.trans hby.symm) i
    cases hm : m.idxFun i with
    | none => simpa [Line.coe_apply, hi, hm] using h
    | some z =>
        have h' := congrFun hca i
        simp only [Line.coe_apply, hi, hm, Option.getD_none, Option.getD_some] at h h'
        exact (hab (h'.symm.trans h)).elim
  apply line_eq_of_apply_eq_apply hab
  · simpa [hc] using hca.symm
  · simpa [hd] using (hdy.trans hby.symm).symm

/-- Injectivity of the data field of a combinatorial line. -/
lemma line_idxFun_injective :
    Function.Injective (Line.idxFun : Line A I → I → Option A) := by
  intro l m h
  cases l with
  | mk lf lp =>
      cases m with
      | mk mf mp =>
          simp only at h
          subst mf
          rfl

/-- The moving-coordinate support of a line. -/
def movingSet [Fintype I] (l : Line A I) : Finset I :=
  Finset.univ.filter fun i ↦ l.idxFun i = none

@[simp]
lemma mem_movingSet [Fintype I] (l : Line A I) (i : I) :
    i ∈ movingSet l ↔ l.idxFun i = none := by
  simp [movingSet]

/-- A line through a fixed vertex is determined already by its moving support. -/
lemma line_eq_of_movingSet_eq_of_mem [Fintype I] {l m : Line A I}
    (hmove : movingSet l = movingSet m) {x : I → A}
    (hxl : x ∈ linePoints l) (hxm : x ∈ linePoints m) : l = m := by
  rcases hxl with ⟨a, ha⟩
  rcases hxm with ⟨b, hb⟩
  apply line_idxFun_injective
  funext i
  by_cases hi : i ∈ movingSet l
  · have hil : l.idxFun i = none := (mem_movingSet l i).mp hi
    have him : m.idxFun i = none := (mem_movingSet m i).mp (hmove ▸ hi)
    simp [hil, him]
  · have hil : l.idxFun i ≠ none := fun h ↦ hi ((mem_movingSet l i).mpr h)
    have him : m.idxFun i ≠ none := by
      intro h
      exact hi (hmove.symm ▸ (mem_movingSet m i).mpr h)
    cases hl : l.idxFun i with
    | none => exact (hil hl).elim
    | some c =>
        cases hm : m.idxFun i with
        | none => exact (him hm).elim
        | some d =>
            have h := congrFun (ha.trans hb.symm) i
            simp only [Line.coe_apply, hl, hm, Option.getD_some] at h
            exact congrArg some h

/-- The vertices of a line, as a finset for incidence counting. -/
noncomputable def linePointFinset [Fintype A] (l : Line A I) : Finset (I → A) :=
  Finset.univ.image l

@[simp]
lemma mem_linePointFinset [Fintype A] {l : Line A I} {x : I → A} :
    x ∈ linePointFinset l ↔ x ∈ linePoints l := by
  simp [linePointFinset, linePoints]

lemma card_linePointFinset [Fintype A] [Nontrivial A] (l : Line A I) :
    (linePointFinset l).card = Fintype.card A := by
  rw [linePointFinset, Finset.card_image_of_injective _ (line_apply_injective l)]
  exact Finset.card_univ

/-- A concrete `Fintype` structure on combinatorial lines. -/
noncomputable def lineFintype [Fintype A] [Fintype I] : Fintype (Line A I) :=
  Fintype.ofInjective Line.idxFun line_idxFun_injective

/-- The full finite line family in a finite cube. -/
noncomputable def allLines [Fintype A] [Fintype I] : Finset (Line A I) := by
  letI := lineFintype (A := A) (I := I)
  exact Finset.univ

@[simp]
lemma mem_allLines [Fintype A] [Fintype I] (l : Line A I) : l ∈ allLines := by
  classical
  letI := lineFintype (A := A) (I := I)
  simp [allLines]

/-- A line in `S` is monochromatic for every coloring of its cube vertices. -/
def IsRamseyFamily (S : Finset (Line A I)) (K : Type w) : Prop :=
  ∀ color : (I → A) → K, ∃ l ∈ S, l.IsMono color

/-- Lines of `S` incident with a fixed cube vertex. -/
noncomputable def incidentLines (S : Finset (Line A I)) (x : I → A) : Finset (Line A I) :=
  S.filter fun l ↦ x ∈ linePoints l

@[simp]
lemma mem_incidentLines {S : Finset (Line A I)} {x : I → A} {l : Line A I} :
    l ∈ incidentLines S x ↔ l ∈ S ∧ x ∈ linePoints l := by
  simp [incidentLines]

/-- The degree of a cube vertex in a selected line family. -/
noncomputable def lineDegree (S : Finset (Line A I)) (x : I → A) : ℕ :=
  (incidentLines S x).card

/-- Double-counting incidences: every selected line contains exactly `|A|` vertices. -/
lemma sum_lineDegree [Fintype A] [Fintype I] [Nontrivial A]
    (S : Finset (Line A I)) :
    ∑ x : I → A, lineDegree S x = Fintype.card A * S.card := by
  classical
  let r : Line A I → (I → A) → Prop := fun l x ↦ x ∈ linePoints l
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := S) (t := (Finset.univ : Finset (I → A))) r
  have habove : ∀ l : Line A I,
      Finset.bipartiteAbove r Finset.univ l = linePointFinset l := by
    intro l
    ext x
    simp [r]
  have hbelow : ∀ x : I → A,
      Finset.bipartiteBelow r S x = incidentLines S x := by
    intro x
    ext l
    simp [r]
  simpa only [habove, hbelow, lineDegree, card_linePointFinset, Finset.sum_const_nat,
    Finset.card_univ, Nat.nsmul_eq_mul, Nat.mul_comm] using hdouble.symm

/-- Vertices whose selected-line degree has reached the cap `d`. -/
noncomputable def saturatedPoints [Fintype A] [Fintype I]
    (S : Finset (Line A I)) (d : ℕ) : Finset (I → A) :=
  Finset.univ.filter fun x ↦ d ≤ lineDegree S x

@[simp]
lemma mem_saturatedPoints [Fintype A] [Fintype I]
    {S : Finset (Line A I)} {d : ℕ} {x : I → A} :
    x ∈ saturatedPoints S d ↔ d ≤ lineDegree S x := by
  simp [saturatedPoints]

/-- First RRS exclusion estimate in abstract incidence form: the number of saturated vertices,
times the degree cap, is at most the total number of line--vertex incidences. -/
lemma card_saturatedPoints_mul_le [Fintype A] [Fintype I] [Nontrivial A]
    (S : Finset (Line A I)) (d : ℕ) :
    (saturatedPoints S d).card * d ≤ Fintype.card A * S.card := by
  classical
  calc
    (saturatedPoints S d).card * d ≤
        ∑ x ∈ saturatedPoints S d, lineDegree S x := by
      simpa [Nat.nsmul_eq_mul] using
        Finset.card_nsmul_le_sum (saturatedPoints S d) (lineDegree S) d
          (fun x hx ↦ mem_saturatedPoints.mp hx)
    _ ≤ ∑ x : I → A, lineDegree S x := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = Fintype.card A * S.card := sum_lineDegree S

/-- Lines from `T` that meet at least one vertex of `P`. -/
noncomputable def linesMeetingPoints (T : Finset (Line A I)) (P : Finset (I → A)) :
    Finset (Line A I) :=
  P.biUnion (incidentLines T)

@[simp]
lemma mem_linesMeetingPoints {T : Finset (Line A I)} {P : Finset (I → A)}
    {l : Line A I} :
    l ∈ linesMeetingPoints T P ↔
      ∃ x ∈ P, l ∈ T ∧ x ∈ linePoints l := by
  simp [linesMeetingPoints]

/-- Union bound for lines excluded because they meet a forbidden set of vertices. -/
lemma card_linesMeetingPoints_le_sum_degree (T : Finset (Line A I)) (P : Finset (I → A)) :
    (linesMeetingPoints T P).card ≤ ∑ x ∈ P, lineDegree T x := by
  classical
  simpa [linesMeetingPoints, lineDegree] using
    (Finset.card_biUnion_le (s := P) (t := incidentLines T))

/-- If every forbidden vertex belongs to at most `M` candidate lines, at most `|P| M`
candidates are excluded by the degree condition. -/
lemma card_linesMeetingPoints_le (T : Finset (Line A I)) (P : Finset (I → A)) (M : ℕ)
    (hM : ∀ x ∈ P, lineDegree T x ≤ M) :
    (linesMeetingPoints T P).card ≤ P.card * M := by
  calc
    (linesMeetingPoints T P).card ≤ ∑ x ∈ P, lineDegree T x :=
      card_linesMeetingPoints_le_sum_degree T P
    _ ≤ P.card * M := by
      simpa [Nat.nsmul_eq_mul] using Finset.sum_le_card_nsmul P (lineDegree T) M hM

/-- The exact RRS tripod pattern: three pairwise distinct selected lines pass through one
cube vertex and, after the existential relabeling displayed here, the moving support of the first
line is the disjoint union of the moving supports of the other two. -/
def HasTripod [Fintype I] (S : Finset (Line A I)) : Prop :=
  ∃ l₁ ∈ S, ∃ l₂ ∈ S, ∃ l₃ ∈ S,
    l₁ ≠ l₂ ∧ l₂ ≠ l₃ ∧ l₃ ≠ l₁ ∧
      (∃ x, x ∈ linePoints l₁ ∧ x ∈ linePoints l₂ ∧ x ∈ linePoints l₃) ∧
      movingSet l₁ = movingSet l₂ ∪ movingSet l₃ ∧
      Disjoint (movingSet l₂) (movingSet l₃)

/-- Three pairwise distinct selected lines meet pairwise, but have no common point. -/
def HasTriangle (S : Finset (Line A I)) : Prop :=
  ∃ l₁ ∈ S, ∃ l₂ ∈ S, ∃ l₃ ∈ S,
    l₁ ≠ l₂ ∧ l₂ ≠ l₃ ∧ l₃ ≠ l₁ ∧
      (linePoints l₁ ∩ linePoints l₂).Nonempty ∧
      (linePoints l₂ ∩ linePoints l₃).Nonempty ∧
      (linePoints l₃ ∩ linePoints l₁).Nonempty ∧
      linePoints l₁ ∩ linePoints l₂ ∩ linePoints l₃ = ∅

/-- The two forbidden intersection patterns required by the RRS partite construction. -/
def IsSparse [Fintype I] (S : Finset (Line A I)) : Prop :=
  ¬ HasTripod S ∧ ¬ HasTriangle S

lemma IsSparse.subset [Fintype I] {S T : Finset (Line A I)} (hS : IsSparse S) (hTS : T ⊆ S) :
    IsSparse T := by
  constructor
  · intro hT
    apply hS.1
    rcases hT with ⟨l₁, h₁, l₂, h₂, l₃, h₃, hrest⟩
    exact ⟨l₁, hTS h₁, l₂, hTS h₂, l₃, hTS h₃, hrest⟩
  · intro hT
    apply hS.2
    rcases hT with ⟨l₁, h₁, l₂, h₂, l₃, h₃, hrest⟩
    exact ⟨l₁, hTS h₁, l₂, hTS h₂, l₃, hTS h₃, hrest⟩

lemma isSparse_empty [Fintype I] : IsSparse (∅ : Finset (Line A I)) := by
  constructor <;> simp [HasTripod, HasTriangle]

/-- A support-size stratum of an explicitly finite family of lines. -/
def supportStratum [Fintype I] (S : Finset (Line A I)) (s : ℕ) : Finset (Line A I) :=
  S.filter fun l ↦ (movingSet l).card = s

@[simp]
lemma mem_supportStratum [Fintype I] {S : Finset (Line A I)} {s : ℕ} {l : Line A I} :
    l ∈ supportStratum S s ↔ l ∈ S ∧ (movingSet l).card = s := by
  simp [supportStratum]

/-- The ordinary Hales--Jewett theorem, packaged as a finite Ramsey family.

The family here is the full finite family of lines.  The sparse-selection
argument starts from support-size strata of this family and deletes lines.
-/
theorem exists_finite_ramsey_family (A : Type u) [Finite A] [Nontrivial A]
    (K : Type w) [Finite K] :
    ∃ (I : Type) (_ : Fintype I) (S : Finset (Line A I)), IsRamseyFamily S K := by
  rcases Line.exists_mono_in_high_dimension A K with ⟨I, hI, hHJ⟩
  letI : Fintype I := hI
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype (Line A I) :=
    Fintype.ofInjective Line.idxFun (by
      intro l m h
      cases l with
      | mk lf lp =>
          cases m with
          | mk mf mp =>
              simp only at h
              subst mf
              rfl)
  refine ⟨I, inferInstance, Finset.univ, ?_⟩
  intro color
  rcases hHJ color with ⟨l, hl⟩
  exact ⟨l, Finset.mem_univ l, hl⟩

/-! ## Generic one-stratum greedy selection -/

open Erdos847SparseSelection in
/-- One-stratum specialization of the finite averaging lemma. -/
theorem exists_addable_hits_many_one {Candidate Colour : Type*}
    (X : Finset Candidate) (colours : Finset Colour)
    (Hit : Candidate → Colour → Prop) (Suitable : Finset Candidate → Prop)
    {A q : ℕ} (hA : 0 < A) (hX : 0 < X.card)
    (hdense : ∀ c ∈ colours, X.card ≤ A * (X.filter fun x ↦ Hit x c).card)
    (hnonadd : ∀ (S : Finset Candidate), Suitable S → S.card < q →
      2 * A * (X.filter fun x ↦ ¬ Suitable (insert x S)).card < X.card)
    {S : Finset Candidate} (hS : Suitable S) (hSq : S.card < q)
    (hbad : (badColourings colours Hit S).Nonempty) :
    ∃ x ∈ X, Suitable (insert x S) ∧
      (badColourings colours Hit S).card ≤
        (2 * A) * ((badColourings colours Hit S).filter fun c ↦ Hit x c).card := by
  classical
  let strata : Fin 1 → Finset Candidate := fun _ ↦ X
  have hcard : ∀ j : Fin 1, 1 * (strata j).card = X.card := by simp [strata]
  have hdense' : ∀ c ∈ colours, ∃ j : Fin 1,
      (strata j).card ≤ A * ((strata j).filter fun x ↦ Hit x c).card := by
    intro c hc
    exact ⟨0, by simpa [strata] using hdense c hc⟩
  have hnonadd' : ∀ (S : Finset Candidate), Suitable S → S.card < q → ∀ j : Fin 1,
      2 * A * ((strata j).filter fun x ↦ ¬ Suitable (insert x S)).card <
        (strata j).card := by
    intro S hS hSq j
    simpa [strata] using hnonadd S hS hSq
  obtain ⟨j, x, hx, hsx, hhit⟩ :=
    exists_addable_hits_many strata colours Hit Suitable (fun _ ↦ 1)
      hA hX hcard hdense' hnonadd' hS hSq hbad
  exact ⟨x, by simpa [strata] using hx, hsx, by simpa using hhit⟩

/-- The first two binomial terms, in a form sufficient for the integer decay estimate. -/
lemma pow_add_one_linear_lower (x n : ℕ) :
    x ^ (n + 1) + (n + 1) * x ^ n ≤ (x + 1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hmul := Nat.mul_le_mul_right (x + 1) ih
      calc
        x ^ (n + 2) + (n + 2) * x ^ (n + 1)
            ≤ x ^ (n + 2) + (n + 2) * x ^ (n + 1) + (n + 1) * x ^ n :=
              Nat.le_add_right _ _
        _ = (x ^ (n + 1) + (n + 1) * x ^ n) * (x + 1) := by
              simp only [pow_succ]
              ring
        _ ≤ (x + 1) ^ (n + 1) * (x + 1) := hmul
        _ = (x + 1) ^ (n + 2) := by
          exact (pow_succ (x + 1) (n + 1)).symm

/-- `D` successive losses by the ratio `(D-1)/D` reduce an integer count by at least half. -/
lemma two_mul_pred_pow_le_pow {D : ℕ} (hD : 2 ≤ D) :
    2 * (D - 1) ^ D ≤ D ^ D := by
  have hlin := pow_add_one_linear_lower (D - 1) (D - 1)
  have hD1 : D - 1 + 1 = D := Nat.sub_add_cancel (by omega : 1 ≤ D)
  have hlin' : (D - 1) ^ D + D * (D - 1) ^ (D - 1) ≤ D ^ D := by
    simpa [hD1] using hlin
  have hterm : (D - 1) ^ D ≤ D * (D - 1) ^ (D - 1) := by
    calc
      (D - 1) ^ D = (D - 1) ^ ((D - 1) + 1) := by rw [hD1]
      _ = (D - 1) ^ (D - 1) * (D - 1) := pow_succ _ _
      _ ≤ (D - 1) ^ (D - 1) * D :=
        Nat.mul_le_mul_left _ (Nat.sub_le D 1)
      _ = D * (D - 1) ^ (D - 1) := Nat.mul_comm _ _
  omega

lemma decay_power_blocks {D s : ℕ} (hD : 2 ≤ D) :
    2 ^ s * (D - 1) ^ (D * s) ≤ D ^ (D * s) := by
  have h := Nat.pow_le_pow_left (two_mul_pred_pow_le_pow hD) s
  simpa [mul_pow, pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

open Erdos847SparseSelection in
/-- Complete one-stratum greedy selection, with the iteration and vanishing estimate kept over
natural numbers. -/
theorem exists_suitable_hitting_family {Candidate Colour : Type*}
    (X : Finset Candidate) (colours : Finset Colour)
    (Hit : Candidate → Colour → Prop) (Suitable : Finset Candidate → Prop)
    {A s : ℕ} (hA : 0 < A) (hempty : Suitable ∅)
    (hdense : ∀ c ∈ colours, X.card ≤ A * (X.filter fun x ↦ Hit x c).card)
    (hnonadd : ∀ (S : Finset Candidate), Suitable S → S.card < (2 * A) * s →
      2 * A * (X.filter fun x ↦ ¬ Suitable (insert x S)).card < X.card)
    (hcolours : colours.card < 2 ^ s) :
    ∃ S : Finset Candidate, Suitable S ∧
      badColourings colours Hit S = ∅ := by
  classical
  by_cases hcol : colours = ∅
  · exact ⟨∅, hempty, by simp [hcol]⟩
  have hcolne : colours.Nonempty := Finset.nonempty_iff_ne_empty.mpr hcol
  have hcpos : 0 < colours.card := Finset.card_pos.mpr hcolne
  obtain ⟨c, hc⟩ := hcolne
  have hX : 0 < X.card := by
    have hd := hdense c hc
    by_contra hzero
    have hX0 : X.card = 0 := Nat.eq_zero_of_not_pos hzero
    have hfilter0 : (X.filter fun x ↦ Hit x c).card = 0 := by
      have : X = ∅ := Finset.card_eq_zero.mp hX0
      simp [this]
    have hspos : 0 < s := by
      by_contra hs
      have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
      subst s
      have hlt : colours.card < 1 := by simpa using hcolours
      exact (Nat.not_lt_of_ge hcpos) hlt
    have hqpos : 0 < (2 * A) * s := by positivity
    have := hnonadd ∅ hempty (by simpa using hqpos)
    simp [hX0] at this
  let D := 2 * A
  let q := D * s
  have hD : 2 ≤ D := by
    dsimp [D]
    omega
  have hstep : ∀ (S : Finset Candidate), Suitable S → S.card < q →
      (badColourings colours Hit S).Nonempty →
      ∃ x, Suitable (insert x S) ∧
        D * (badColourings colours Hit (insert x S)).card ≤
          (D - 1) * (badColourings colours Hit S).card := by
    intro S hS hSq hbad
    obtain ⟨x, hxX, hxSuit, hxhit⟩ :=
      exists_addable_hits_many_one X colours Hit Suitable hA hX hdense
        (by simpa [q, D] using hnonadd) hS (by simpa [q, D] using hSq) hbad
    refine ⟨x, hxSuit, ?_⟩
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := badColourings colours Hit S) (fun c ↦ Hit x c)
    have hnext : badColourings colours Hit (insert x S) =
        (badColourings colours Hit S).filter fun c ↦ ¬ Hit x c :=
      badColourings_insert colours Hit x S
    rw [hnext]
    let B := (badColourings colours Hit S).card
    let H := ((badColourings colours Hit S).filter fun c ↦ Hit x c).card
    let R := ((badColourings colours Hit S).filter fun c ↦ ¬ Hit x c).card
    have hBH : B = H + R := by
      dsimp [B, H, R]
      omega
    have hxhit' : B ≤ D * H := by simpa [B, H, D] using hxhit
    have hDRB : D * R + B ≤ D * B := by
      calc
        D * R + B ≤ D * R + D * H := Nat.add_le_add_left hxhit' _
        _ = D * (H + R) := by ring
        _ = D * B := by rw [← hBH]
    have hDB : D * B = (D - 1) * B + B := by
      calc
        D * B = ((D - 1) + 1) * B := by congr 1 <;> omega
        _ = (D - 1) * B + B := by rw [Nat.add_mul, one_mul]
    have hcancel : D * R + B ≤ (D - 1) * B + B := hDRB.trans_eq hDB
    exact Nat.le_of_add_le_add_right hcancel
  obtain ⟨S, hS, hScard, hdec⟩ :=
    iterate_decay colours Hit Suitable (D := D) (q := q)
      (by omega : 0 < D) hempty hstep q (le_rfl)
  have hblock : 2 ^ s * (D - 1) ^ q ≤ D ^ q := by
    simpa [q] using decay_power_blocks hD (s := s)
  have hsmall : (D - 1) ^ q * colours.card < D ^ q := by
    have hpred : 0 < D - 1 := by omega
    have hpredpos : 0 < (D - 1) ^ q := pow_pos hpred q
    calc
      (D - 1) ^ q * colours.card < (D - 1) ^ q * 2 ^ s :=
        (Nat.mul_lt_mul_left hpredpos).2 hcolours
      _ = 2 ^ s * (D - 1) ^ q := Nat.mul_comm _ _
      _ ≤ D ^ q := hblock
  have hzero : (badColourings colours Hit S).card = 0 := by
    by_contra hb
    have hbone : 1 ≤ (badColourings colours Hit S).card := Nat.one_le_iff_ne_zero.mpr hb
    have hlower : D ^ q ≤ D ^ q * (badColourings colours Hit S).card := by
      simpa using Nat.mul_le_mul_left (D ^ q) hbone
    exact (not_lt_of_ge (hlower.trans hdec)) hsmall
  exact ⟨S, hS, Finset.card_eq_zero.mp hzero⟩

/-! ## Disjoint-block candidates and geometric suitability -/

/-- Coordinates in one block of `Fin t × J`. -/
def coordinateBlock {J : Type*} [Fintype J] (t : ℕ) (j : Fin t) :
    Finset (Fin t × J) :=
  Finset.univ.filter fun iq ↦ iq.1 = j

lemma card_coordinateBlock {J : Type*} [Fintype J] (t : ℕ) (j : Fin t) :
    (coordinateBlock (J := J) t j).card = Fintype.card J := by
  classical
  let f : J → Fin t × J := fun q ↦ (j, q)
  have himage : Finset.univ.image f = coordinateBlock (J := J) t j := by
    ext iq
    simp [coordinateBlock, f, Prod.ext_iff, eq_comm]
  rw [← himage, Finset.card_image_of_injective]
  · simp
  · intro q r h
    exact congrArg Prod.snd h

lemma candidateLines_supported {A J : Type*} [Fintype A] [Fintype J]
    (t : ℕ) (S : Finset (Line A J)) :
    Erdos847LineExclusions.SupportedInBlocks
      (Erdos847BlockCandidates.candidateLines t S)
      (coordinateBlock (J := J) t) := by
  classical
  intro l hl
  rcases Erdos847BlockCandidates.mem_candidateLines.mp hl with ⟨c, rfl⟩
  refine ⟨c.1, ?_⟩
  intro iq hi
  have hnone :=
    (Erdos847LineExclusions.mem_movingSet
      (Erdos847BlockCandidates.encodedLine c) iq).mp hi
  have hblock : iq.1 = c.1 := by
    by_contra hne
    simp [Erdos847BlockCandidates.encodedLine, hne] at hnone
  simp [coordinateBlock, hblock]

lemma pow_lt_two_pow_mul_add_one (r N : ℕ) :
    r ^ N < 2 ^ (r * N + 1) := by
  have hr : r ≤ 2 ^ r := r.lt_two_pow_self.le
  have hp : r ^ N ≤ (2 ^ r) ^ N := Nat.pow_le_pow_left hr N
  have heq : (2 ^ r) ^ N = 2 ^ (r * N) := by rw [pow_mul]
  have hlt : 2 ^ (r * N) < 2 ^ (r * N + 1) :=
    Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _)
  exact hp.trans_eq heq |>.trans_lt hlt

/-! ## Natural-number parameter hierarchy for sparse selection

The paper writes `n ≫ d ≫ α⁻¹ ≫ m`.  The following explicit integer parameters implement
the denominator-cleared scheme used by the finite greedy proof.  Keeping these quantities in `ℕ`
avoids logarithms and real-valued probability estimates.
-/

/-! The following denominator-cleared calculation is the numerical core of the
disjoint-block construction.  It is deliberately stated independently of the
geometry: the first summand is the saturated-point exclusion and the second is
the combined tripod/triangle certificate bound. -/

lemma block_parameter_bound
    {a m r A₀ C d t V P F s N M : ℕ}
    (ha : 0 < a) (hA₀ : 0 < A₀) (hP : 0 < P)
    (hC : C = 2 * A₀ * (r + 1))
    (hd : d = 4 * A₀ * a * C * a ^ m * 2 ^ m + 1)
    (ht : t = 8 * A₀ * a ^ 2 * d ^ 2 * a ^ m + 1)
    (hV : V = P * a ^ m) (hF : F = t * P) (hs : s = r * V + 1)
    (hN : N < 2 * A₀ * s) (hFM : F ≤ M) :
    (2 * A₀) *
        ((a * N) * (t * 2 ^ m) +
          (d ^ 2 * V + (a * d) ^ 2 * V) * d) < d * M := by
  have hVpos : 0 < V := by rw [hV]; positivity
  have hVone : 1 ≤ V := by omega
  have hCpos : 0 < C := by rw [hC]; positivity
  have hdpos : 0 < d := by rw [hd]; positivity
  have htpos : 0 < t := by rw [ht]; positivity
  have hFpos : 0 < F := by rw [hF]; positivity
  have hNs : N < C * V := by
    calc
      N < 2 * A₀ * s := hN
      _ ≤ 2 * A₀ * ((r + 1) * V) := by
        apply Nat.mul_le_mul_left
        rw [hs]
        calc
          r * V + 1 ≤ r * V + V := Nat.add_le_add_left hVone _
          _ = (r + 1) * V := by ring
      _ = C * V := by rw [hC]; ring
  let U₁ := (a * N) * (t * 2 ^ m)
  let U₂ := (d ^ 2 * V + (a * d) ^ 2 * V) * d
  have hU₁raw : U₁ < (a * (C * V)) * (t * 2 ^ m) := by
    dsimp [U₁]
    exact Nat.mul_lt_mul_of_pos_right
      (Nat.mul_lt_mul_of_pos_left hNs ha) (by positivity)
  have hU₁ : (4 * A₀) * U₁ < d * F := by
    calc
      (4 * A₀) * U₁ < (4 * A₀) * ((a * (C * V)) * (t * 2 ^ m)) :=
        Nat.mul_lt_mul_of_pos_left hU₁raw (by positivity)
      _ = (4 * A₀ * a * C * a ^ m * 2 ^ m) * F := by
        rw [hV, hF]
        ring
      _ < d * F := by
        apply Nat.mul_lt_mul_of_pos_right _ hFpos
        rw [hd]
        omega
  have had : d ≤ a * d := by
    calc
      d = 1 * d := by simp
      _ ≤ a * d := Nat.mul_le_mul_right d (by omega)
  have hU₂raw : U₂ ≤ 2 * a ^ 2 * d ^ 3 * V := by
    dsimp [U₂]
    calc
      (d ^ 2 * V + (a * d) ^ 2 * V) * d
          ≤ ((a * d) ^ 2 * V + (a * d) ^ 2 * V) * d := by
            apply Nat.mul_le_mul_right
            exact Nat.add_le_add_right
              (Nat.mul_le_mul_right V (Nat.pow_le_pow_left had 2)) _
      _ = 2 * a ^ 2 * d ^ 3 * V := by ring
  have hU₂ : (4 * A₀) * U₂ < d * F := by
    calc
      (4 * A₀) * U₂ ≤ (4 * A₀) * (2 * a ^ 2 * d ^ 3 * V) :=
        Nat.mul_le_mul_left _ hU₂raw
      _ = (8 * A₀ * a ^ 2 * d ^ 2 * a ^ m) * (d * P) := by
        rw [hV]
        ring
      _ < t * (d * P) := by
        apply Nat.mul_lt_mul_of_pos_right _ (by positivity)
        rw [ht]
        omega
      _ = d * F := by rw [hF]; ring
  have hsum : (4 * A₀) * (U₁ + U₂) < d * F + d * F := by
    rw [Nat.mul_add]
    exact Nat.add_lt_add hU₁ hU₂
  have hdouble : 2 * ((2 * A₀) * (U₁ + U₂)) < 2 * (d * F) := by
    convert hsum using 1 <;> ring
  have hhalf : (2 * A₀) * (U₁ + U₂) < d * F :=
    (Nat.mul_lt_mul_left (by omega : 0 < 2)).mp hdouble
  exact hhalf.trans_le (Nat.mul_le_mul_left d hFM)

/-- The numerical estimate above, combined with the geometric exclusion
lemmas, says that fewer than a `1/(2A₀)` fraction of the disjoint-block
candidates are forbidden at every greedy stage.  Factoring this out keeps the
final Ramsey construction inexpensive to elaborate. -/
theorem block_candidates_nonaddable
    (A : Type u) [Fintype A] [Nontrivial A]
    {J : Type v} [Fintype J] (S : Finset (Line A J)) (hSne : S.Nonempty)
    {a m r A₀ C d t P V F s : ℕ}
    (ha : 0 < a) (hA₀ : 0 < A₀) (hP : 0 < P)
    (haeq : a = Fintype.card A) (hmeq : m = Fintype.card J)
    (hC : C = 2 * A₀ * (r + 1))
    (hd : d = 4 * A₀ * a * C * a ^ m * 2 ^ m + 1)
    (ht : t = 8 * A₀ * a ^ 2 * d ^ 2 * a ^ m + 1)
    (hPdef : P = a ^ (m * (t - 1)))
    (hV : V = P * a ^ m) (hF : F = t * P) (hs : s = r * V + 1)
    (R : Finset (Line A (Fin t × J)))
    (hR : Erdos847LineExclusions.Suitable R d)
    (hRcard : R.card < (2 * A₀) * s) :
    (2 * A₀) *
        (Erdos847LineExclusions.nonaddable
          (Erdos847BlockCandidates.candidateLines t S) R d).card <
      (Erdos847BlockCandidates.candidateLines t S).card := by
  letI : DecidableEq (Fin t × J) := Classical.decEq _
  have htpos : 0 < t := by rw [ht]; positivity
  have htone : 1 ≤ t := by omega
  have htm : t * m = m * (t - 1) + m := by
    calc
      t * m = ((t - 1) + 1) * m := by rw [Nat.sub_add_cancel htone]
      _ = m * (t - 1) + m := by ring
  have hcube : Fintype.card (Fin t × J → A) = V := by
    rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
    rw [← haeq, ← hmeq]
    rw [htm, pow_add, ← hPdef, hV]
  have hFlower : F ≤
      (Erdos847BlockCandidates.candidateLines t S).card := by
    rw [hF, hPdef, haeq, hmeq]
    exact Erdos847BlockCandidates.candidateLines_card_lower hSne
  have hparam : (2 * A₀) *
      ((Fintype.card A * R.card) * (t * 2 ^ m) +
        (d ^ 2 * Fintype.card (Fin t × J → A) +
          (Fintype.card A * d) ^ 2 * Fintype.card (Fin t × J → A)) * d) <
      d * (Erdos847BlockCandidates.candidateLines t S).card := by
    rw [← haeq, hcube]
    exact block_parameter_bound ha hA₀ hP hC hd ht hV hF hs hRcard hFlower
  exact Erdos847LineExclusions.nonaddable_fraction
    (t := t) (m := m) (d := d) (A₀ := A₀)
    (Erdos847BlockCandidates.candidateLines t S) R
    (coordinateBlock (J := J) t)
    (candidateLines_supported t S)
    (by intro j; simpa [hmeq] using card_coordinateBlock (J := J) t j)
    hR hparam

/-- Exact target of the sparse Hales--Jewett selection step. -/
def SparseHalesJewett (A : Type u) (K : Type w) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (S : Finset (Line A I)),
    IsSparse S ∧ IsRamseyFamily S K

/-- Sparse Hales--Jewett, in the exact tripod/triangle-free form used by
Reiher--Rödl--Sales.  The ambient cube consists of many disjoint copies of an
ordinary Hales--Jewett cube. -/
theorem sparse_hales_jewett (A : Type u) [Fintype A] [Nontrivial A]
    (K : Type w) [Fintype K] : SparseHalesJewett A K := by
  classical
  cases isEmpty_or_nonempty K with
  | inl hK =>
      letI : IsEmpty K := hK
      refine ⟨PEmpty, inferInstance, ∅, isSparse_empty, ?_⟩
      intro color
      exact isEmptyElim (color fun i ↦ nomatch i)
  | inr hK =>
      letI : Nonempty K := hK
      letI : Inhabited K := Classical.inhabited_of_nonempty hK
      obtain ⟨J, hJ, S, hHJ⟩ := exists_finite_ramsey_family A K
      letI : Fintype J := hJ
      have hSne : S.Nonempty := by
        obtain ⟨l, hl, -⟩ := hHJ (fun _ ↦ default)
        exact ⟨l, hl⟩
      let a := Fintype.card A
      let m := Fintype.card J
      let r := Fintype.card K
      let A₀ := (a + 1) ^ m
      let C := 2 * A₀ * (r + 1)
      let d := 4 * A₀ * a * C * a ^ m * 2 ^ m + 1
      let t := 8 * A₀ * a ^ 2 * d ^ 2 * a ^ m + 1
      let P := a ^ (m * (t - 1))
      let V := P * a ^ m
      let F := t * P
      let s := r * V + 1
      let X : Finset (Line A (Fin t × J)) :=
        Erdos847BlockCandidates.candidateLines t S
      let colours : Finset (((Fin t × J → A) → K)) := Finset.univ
      let Hit : Line A (Fin t × J) → ((Fin t × J → A) → K) → Prop :=
        fun l color ↦ l.IsMono color
      let Good : Finset (Line A (Fin t × J)) → Prop :=
        fun R ↦ Erdos847LineExclusions.Suitable R d
      have ha : 0 < a := by
        dsimp [a]
        exact Fintype.card_pos
      have hA₀ : 0 < A₀ := by dsimp [A₀]; positivity
      have hd : 0 < d := by dsimp [d]; positivity
      have ht : 0 < t := by dsimp [t]; positivity
      have htone : 1 ≤ t := by omega
      have hP : 0 < P := by dsimp [P]; positivity
      have hF : 0 < F := by dsimp [F]; positivity
      have htm : t * m = m * (t - 1) + m := by
        calc
          t * m = ((t - 1) + 1) * m := by rw [Nat.sub_add_cancel htone]
          _ = m * (t - 1) + m := by ring
      have hcube : Fintype.card (Fin t × J → A) = V := by
        rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
        change a ^ (t * m) = V
        rw [htm, pow_add]
      have hFlower : F ≤ X.card := by
        simpa [F, P, X, a, m] using
          (Erdos847BlockCandidates.candidateLines_card_lower
            (t := t) (S := S) hSne)
      have hX : 0 < X.card := hF.trans_le hFlower
      have hdense : ∀ c ∈ colours,
          X.card ≤ A₀ * (X.filter fun l ↦ Hit l c).card := by
        intro c _hc
        have hupper := Erdos847BlockCandidates.candidateLines_card_upper t S
        have hlower := Erdos847BlockCandidates.monoCandidateLines_card_lower hHJ c
        calc
          X.card ≤ F * A₀ := by
            simpa [X, F, P, A₀, a, m] using hupper
          _ = A₀ * F := by ring
          _ ≤ A₀ * (X.filter fun l ↦ Hit l c).card := by
            apply Nat.mul_le_mul_left
            simpa [X, Hit, F, P, a, m,
              Erdos847BlockCandidates.monoCandidateLines] using hlower
      have hempty : Good ∅ := by
        dsimp [Good]
        constructor
        · intro x
          simp [Erdos847LineExclusions.DegreeBound,
            Erdos847LineExclusions.lineDegree,
            Erdos847LineExclusions.incidentLines]
        · constructor
          · simp [Erdos847LineExclusions.HasTripod]
          · simp [Erdos847LineExclusions.HasTriangle]
      have hnonadd : ∀ (R : Finset (Line A (Fin t × J))), Good R →
          R.card < (2 * A₀) * s →
          2 * A₀ * (X.filter fun l ↦ ¬ Good (insert l R)).card < X.card := by
        intro R hR hRcard
        change Erdos847LineExclusions.Suitable R d at hR
        change (2 * A₀) *
          (Erdos847LineExclusions.nonaddable X R d).card < X.card
        change (2 * A₀) *
          (Erdos847LineExclusions.nonaddable
            (Erdos847BlockCandidates.candidateLines t S) R d).card <
          (Erdos847BlockCandidates.candidateLines t S).card
        exact block_candidates_nonaddable A S hSne ha hA₀ hP
          rfl rfl rfl rfl rfl rfl rfl rfl rfl R hR hRcard
      have hcolourCard : colours.card = r ^ V := by
        rw [show colours.card = Fintype.card ((Fin t × J → A) → K) by
          simp [colours]]
        rw [Fintype.card_fun]
        change r ^ Fintype.card (Fin t × J → A) = r ^ V
        rw [hcube]
      have hcolours : colours.card < 2 ^ s := by
        rw [hcolourCard]
        simpa [s] using pow_lt_two_pow_mul_add_one r V
      obtain ⟨R, hR, hbad⟩ := exists_suitable_hitting_family
        X colours Hit Good hA₀ hempty hdense hnonadd hcolours
      refine ⟨Fin t × J, inferInstance, R, ?_, ?_⟩
      · constructor
        · change ¬ Erdos847LineExclusions.HasTripod R
          exact hR.2.1
        · change ¬ Erdos847LineExclusions.HasTriangle R
          exact hR.2.2
      · intro color
        by_contra hnone
        have hall : ∀ l ∈ R, ¬ Hit l color := by
          intro l hl hmono
          exact hnone ⟨l, hl, hmono⟩
        have hmem : color ∈ Erdos847SparseSelection.badColourings colours Hit R :=
          Erdos847SparseSelection.mem_badColourings.mpr ⟨Finset.mem_univ _, hall⟩
        rw [hbad] at hmem
        simp at hmem

end Erdos847SparseLines

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/Pictures.lean` -/

section
/-
# Pictures for the Reiher--Rödl--Sales construction (the ternary case)

This file isolates the finite, purely structural part of the ``picture''
construction used in the negative solution of Erdős problem 847.  It has no
dependencies on the analytic estimates used to produce a sparse Hales--Jewett
line system.

There are two results here.

* `pictureZero` is the explicit initial picture.  Its points are the three
  labelled vertices of every edge of the base hypergraph.  Two copies of the
  edge set are used as coordinates; the second copy is a signature which
  prevents a quasiline from using points belonging to different edges.
* `amalgamation_preserves` is the reusable formal core of partite
  amalgamation.  The genuinely difficult incidence argument is exposed as
  `EveryQuasilineConfined`: every quasiline in the amalgamated object is
  contained in one standard copy.  Once this is known, preservation of the
  picture invariant is formal.

The alphabet is fixed to `Fin 3`.  A quasiline is represented by an ordering
of its three points; in every coordinate the three entries must be constant
or pairwise distinct.  A combinatorial line is a quasiline for which one
global permutation of the alphabet gives the order in every moving
coordinate.
-/

namespace Erdos847Pictures

open Function Set

set_option autoImplicit false

abbrev Alphabet := Fin 3

/-- A finite simple `3`-uniform hypergraph. -/
structure ThreeGraph (V : Type*) [DecidableEq V] where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = 3

namespace ThreeGraph

variable {V : Type*} [DecidableEq V]

/-- The finite type of edges of `G`. -/
abbrev Edge (G : ThreeGraph V) := {e : Finset V // e ∈ G.edges}

/--
The form of `K₄³-minus-freeness used in the ternary RRS amalgamation:
among any four vertices there are at most two edges of the hypergraph.
-/
def K4MinusFree (G : ThreeGraph V) : Prop :=
  ∀ s : Finset V, s.card = 4 →
    (G.edges.filter fun e => e ⊆ s).card ≤ 2

/-- A simple hypergraph is linear when two edges sharing two vertices agree. -/
def Linear (G : ThreeGraph V) : Prop :=
  ∀ e f : G.Edge, 2 ≤ (e.1 ∩ f.1).card → e = f

/-- A noncomputable labelling of every `3`-edge by the ternary alphabet. -/
noncomputable def edgeEquiv (G : ThreeGraph V) (e : G.Edge) :
    Alphabet ≃ {v : V // v ∈ (e.1 : Finset V)} :=
  Fintype.equivOfCardEq <| by
    rw [Fintype.card_fin, Fintype.card_coe]
    exact (G.uniform e.1 e.2).symm

@[simp]
theorem edgeEquiv_mem (G : ThreeGraph V) (e : G.Edge) (a : Alphabet) :
    (G.edgeEquiv e a : V) ∈ e.1 :=
  (G.edgeEquiv e a).2

end ThreeGraph

section Lines

variable {P C : Type*}

/--
An unordered ternary quasiline, represented by an injective enumeration.
At each coordinate its three entries are either constant or pairwise
distinct.
-/
def IsQuasiline (embed : P → C → Alphabet) (l : Alphabet → P) : Prop :=
  Injective l ∧
    ∀ c, (∃ a, ∀ i, embed (l i) c = a) ∨ Injective (fun i => embed (l i) c)

/--
The three enumerated points form a genuine combinatorial line.  The
permutation `σ` accounts for the arbitrary ordering of an unordered line.
-/
def IsCombinatorialLine (embed : P → C → Alphabet)
    (l : Alphabet → P) : Prop :=
  Injective l ∧
    ∃ σ : Equiv.Perm Alphabet,
      ∀ c, (∃ a, ∀ i, embed (l i) c = a) ∨ ∀ i, embed (l i) c = σ i

theorem range_fin3 (f : Alphabet → P) :
    Set.range f = ({f 0, f 1, f 2} : Set P) := by
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hp | hp | hp
    · exact ⟨0, hp.symm⟩
    · exact ⟨1, hp.symm⟩
    · exact ⟨2, hp.symm⟩

/-- Two combinatorial lines in a cube which share two distinct points have
the same point set. -/
theorem combinatorialLine_range_eq_of_two_points
    (embed : P → C → Alphabet) (hembed : Injective embed)
    (l m : Alphabet → P)
    (hl : IsCombinatorialLine embed l)
    (hm : IsCombinatorialLine embed m)
    {i₀ i₁ j₀ j₁ : Alphabet} (hi : i₀ ≠ i₁)
    (h₀ : l i₀ = m j₀) (h₁ : l i₁ = m j₁) :
    Set.range l = Set.range m := by
  rcases hl with ⟨hlinj, σ, hσ⟩
  rcases hm with ⟨hminj, τ, hτ⟩
  have hj : j₀ ≠ j₁ := by
    intro hj
    apply hi
    apply hlinj
    rw [h₀, h₁, hj]
  let ρ : Equiv.Perm Alphabet := σ.trans τ.symm
  have hpoint : ∀ i, l i = m (ρ i) := by
    intro i
    apply hembed
    funext c
    rcases hσ c with ⟨a, ha⟩ | hmove
    · rcases hτ c with ⟨b, hb⟩ | kmove
      · calc
          embed (l i) c = a := ha i
          _ = embed (l i₀) c := (ha i₀).symm
          _ = embed (m j₀) c := congrArg (fun p => embed p c) h₀
          _ = b := hb j₀
          _ = embed (m (ρ i)) c := (hb (ρ i)).symm
      · exfalso
        apply hj
        apply τ.injective
        calc
          τ j₀ = embed (m j₀) c := (kmove j₀).symm
          _ = embed (l i₀) c := congrArg (fun p => embed p c) h₀.symm
          _ = a := ha i₀
          _ = embed (l i₁) c := (ha i₁).symm
          _ = embed (m j₁) c := congrArg (fun p => embed p c) h₁
          _ = τ j₁ := kmove j₁
    · rcases hτ c with ⟨b, hb⟩ | kmove
      · exfalso
        apply hi
        apply σ.injective
        calc
          σ i₀ = embed (l i₀) c := (hmove i₀).symm
          _ = embed (m j₀) c := congrArg (fun p => embed p c) h₀
          _ = b := hb j₀
          _ = embed (m j₁) c := (hb j₁).symm
          _ = embed (l i₁) c := congrArg (fun p => embed p c) h₁.symm
          _ = σ i₁ := hmove i₁
      · calc
          embed (l i) c = σ i := hmove i
          _ = τ (ρ i) := by simp [ρ]
          _ = embed (m (ρ i)) c := (kmove (ρ i)).symm
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨ρ i, (hpoint i).symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨i, hiρ⟩ := ρ.surjective j
    exact ⟨i, (hpoint i).trans (congrArg m hiρ)⟩

theorem combinatorialLine_range_inter_subsingleton
    (embed : P → C → Alphabet) (hembed : Injective embed)
    (l m : Alphabet → P)
    (hl : IsCombinatorialLine embed l)
    (hm : IsCombinatorialLine embed m)
    (hne : Set.range l ≠ Set.range m) :
    (Set.range l ∩ Set.range m).Subsingleton := by
  intro p hp q hq
  by_contra hpq
  obtain ⟨i₀, hi₀⟩ := hp.1
  obtain ⟨j₀, hj₀⟩ := hp.2
  obtain ⟨i₁, hi₁⟩ := hq.1
  obtain ⟨j₁, hj₁⟩ := hq.2
  have hii : i₀ ≠ i₁ := by
    intro h
    apply hpq
    rw [← hi₀, ← hi₁, h]
  apply hne
  exact combinatorialLine_range_eq_of_two_points embed hembed l m hl hm hii
    (hi₀.trans hj₀.symm) (hi₁.trans hj₁.symm)

end Lines

section Pictures

variable {V : Type*} [DecidableEq V]

/-- The images of the three points enumerated by `l` are precisely one edge. -/
def MapsOntoEdge {P : Type*} (G : ThreeGraph V) (proj : P → V)
    (l : Alphabet → P) : Prop :=
  ∃ e : G.Edge, Set.range (fun i => proj (l i)) = (e.1 : Set V)

/--
A picture over `G`: every quasiline among its points is a genuine
combinatorial line and projects onto an edge of `G`.
-/
structure Picture (G : ThreeGraph V) (P C : Type*) where
  embed : P → C → Alphabet
  embed_injective : Injective embed
  proj : P → V
  quasiline_is_line : ∀ l, IsQuasiline embed l → IsCombinatorialLine embed l
  quasiline_maps_edge : ∀ l, IsQuasiline embed l → MapsOntoEdge G proj l

end Pictures

section PictureZero

variable {V : Type*} [DecidableEq V]
variable (G : ThreeGraph V)

/-- The point and coordinate types of picture zero. -/
abbrev ZeroPoint := G.Edge × Alphabet
abbrev ZeroCoord := G.Edge ⊕ G.Edge

/--
The explicit word belonging to the `a`th vertex of edge `e`.  The left
coordinate `e` carries the moving value; the right coordinate `e` is the
edge signature.  We use the three values `0,1,2`, with signatures only using
`1,2`.
-/
def zeroWord (p : ZeroPoint G) : ZeroCoord G → Alphabet
  | Sum.inl e => if e = p.1 then p.2 else 1
  | Sum.inr e => if e = p.1 then 2 else 1

@[simp]
theorem zeroWord_inl_same (p : ZeroPoint G) :
    zeroWord G p (Sum.inl p.1) = p.2 := by
  simp [zeroWord]

@[simp]
theorem zeroWord_inr_same (p : ZeroPoint G) :
    zeroWord G p (Sum.inr p.1) = 2 := by
  simp [zeroWord]

theorem zeroWord_right_ne_zero (p : ZeroPoint G) (e : G.Edge) :
    zeroWord G p (Sum.inr e) ≠ 0 := by
  simp only [zeroWord]
  split <;> decide

theorem zeroWord_injective : Injective (zeroWord G) := by
  intro p q hpq
  have hr := congrFun hpq (Sum.inr p.1)
  have he : p.1 = q.1 := by
    by_contra hne
    simp [zeroWord, hne] at hr
  have hl := congrFun hpq (Sum.inl p.1)
  have ha : p.2 = q.2 := by
    simpa [zeroWord, he] using hl
  exact Prod.ext he ha

/-- The projection from picture zero to the labelled vertices of its edge. -/
noncomputable def zeroProj (p : ZeroPoint G) : V :=
  G.edgeEquiv p.1 p.2

/--
Every quasiline in picture zero lies over one edge.  This is the signature
coordinate argument from the RRS construction.
-/
theorem zero_quasiline_has_one_edge
    (l : Alphabet → ZeroPoint G)
    (hl : IsQuasiline (zeroWord G) l) :
    ∀ i, (l i).1 = (l 0).1 := by
  let e₀ : G.Edge := (l 0).1
  have hconstant : ∃ a, ∀ i, zeroWord G (l i) (Sum.inr e₀) = a := by
    rcases hl.2 (Sum.inr e₀) with hconst | hinj
    · exact hconst
    · exfalso
      have hsurj : Surjective (fun i => zeroWord G (l i) (Sum.inr e₀)) :=
        (Finite.injective_iff_surjective.mp hinj)
      obtain ⟨i, hi⟩ := hsurj 0
      exact zeroWord_right_ne_zero G (l i) e₀ hi
  obtain ⟨a, ha⟩ := hconstant
  intro i
  have hi0 : zeroWord G (l i) (Sum.inr e₀) =
      zeroWord G (l 0) (Sum.inr e₀) := (ha i).trans (ha 0).symm
  change (l i).1 = e₀
  by_contra hne
  have hreverse : (l 0).1 = (l i).1 := by
    simpa [zeroWord, e₀] using hi0
  exact hne hreverse.symm

/-- The alphabet labels occurring on a picture-zero quasiline are distinct. -/
theorem zero_quasiline_labels_injective
    (l : Alphabet → ZeroPoint G)
    (hl : IsQuasiline (zeroWord G) l) :
    Injective (fun i => (l i).2) := by
  intro i j hij
  apply hl.1
  apply Prod.ext
  · exact (zero_quasiline_has_one_edge G l hl i).trans
      (zero_quasiline_has_one_edge G l hl j).symm
  · exact hij

/-- Every quasiline in picture zero is one of its selected lines. -/
theorem zero_quasiline_is_line
    (l : Alphabet → ZeroPoint G)
    (hl : IsQuasiline (zeroWord G) l) :
    IsCombinatorialLine (zeroWord G) l := by
  let σ : Equiv.Perm Alphabet := Equiv.ofBijective (fun i => (l i).2) ⟨
    zero_quasiline_labels_injective G l hl,
    Finite.injective_iff_surjective.mp (zero_quasiline_labels_injective G l hl)
  ⟩
  refine ⟨hl.1, σ, ?_⟩
  intro c
  cases c with
  | inl e =>
      by_cases he : e = (l 0).1
      · right
        intro i
        have hei : e = (l i).1 :=
          he.trans (zero_quasiline_has_one_edge G l hl i).symm
        simp only [zeroWord, hei, if_pos]
        rfl
      · left
        refine ⟨1, ?_⟩
        intro i
        have hei : e ≠ (l i).1 := by
          intro h
          exact he (h.trans (zero_quasiline_has_one_edge G l hl i))
        simp [zeroWord, hei]
  | inr e =>
      by_cases he : e = (l 0).1
      · left
        refine ⟨2, ?_⟩
        intro i
        have hei : e = (l i).1 :=
          he.trans (zero_quasiline_has_one_edge G l hl i).symm
        simp [zeroWord, hei]
      · left
        refine ⟨1, ?_⟩
        intro i
        have hei : e ≠ (l i).1 := by
          intro h
          exact he (h.trans (zero_quasiline_has_one_edge G l hl i))
        simp [zeroWord, hei]

/-- Every picture-zero quasiline projects onto its indexing edge. -/
theorem zero_quasiline_maps_edge
    (l : Alphabet → ZeroPoint G)
    (hl : IsQuasiline (zeroWord G) l) :
    MapsOntoEdge G (zeroProj G) l := by
  let e₀ : G.Edge := (l 0).1
  let σ : Equiv.Perm Alphabet := Equiv.ofBijective (fun i => (l i).2) ⟨
    zero_quasiline_labels_injective G l hl,
    Finite.injective_iff_surjective.mp (zero_quasiline_labels_injective G l hl)
  ⟩
  refine ⟨e₀, Set.ext ?_⟩
  intro v
  constructor
  · rintro ⟨i, rfl⟩
    change (G.edgeEquiv (l i).1 (l i).2 : V) ∈ e₀.1
    rw [zero_quasiline_has_one_edge G l hl i]
    exact ThreeGraph.edgeEquiv_mem G e₀ (l i).2
  · intro hv
    let w : {v : V // v ∈ e₀.1} := ⟨v, hv⟩
    obtain ⟨a, ha⟩ := (G.edgeEquiv e₀).surjective w
    obtain ⟨i, hi⟩ := σ.surjective a
    refine ⟨i, ?_⟩
    change G.edgeEquiv (l i).1 (l i).2 = v
    rw [zero_quasiline_has_one_edge G l hl i]
    have hlabel : (l i).2 = a := by
      change σ i = a
      exact hi
    rw [hlabel]
    exact congrArg Subtype.val ha

/-- The explicit initial RRS picture over an arbitrary finite 3-graph. -/
noncomputable def pictureZero : Picture G (ZeroPoint G) (ZeroCoord G) where
  embed := zeroWord G
  embed_injective := zeroWord_injective G
  proj := zeroProj G
  quasiline_is_line := zero_quasiline_is_line G
  quasiline_maps_edge := zero_quasiline_maps_edge G

end PictureZero

section Amalgamation

variable {V P C Q D I : Type*} [DecidableEq V]
variable {G : ThreeGraph V}

/--
Data common to all partite amalgamations of a picture.  The incidence proof
which uses a sparse line system is deliberately not included as a field:
it is the separate predicate `EveryQuasilineConfined` below.
-/
structure AmalgamationData (source : Picture G P C) (Q D I : Type*) where
  embed : Q → D → Alphabet
  embed_injective : Injective embed
  proj : Q → V
  copy : I → P → Q
  copy_injective : ∀ i, Injective (copy i)
  proj_copy : ∀ i p, proj (copy i p) = source.proj p
  transports_lines : ∀ i l,
    IsCombinatorialLine source.embed l →
      IsCombinatorialLine embed (fun a => copy i (l a))

/--
The exact geometric output needed from the tripod/triangle-free sparse line
system: each quasiline in the amalgamation is the image of a quasiline in
one standard copy.
-/
def EveryQuasilineConfined (source : Picture G P C)
    (A : AmalgamationData source Q D I) : Prop :=
  ∀ l, IsQuasiline A.embed l →
    ∃ i lp, IsQuasiline source.embed lp ∧ ∀ a, l a = A.copy i (lp a)

/--
A certificate recording both hypotheses used in the ternary RRS incidence
argument.  `K4MinusFree` rules out its exceptional four-vertex pattern; the
sparse (tripod- and triangle-free) line system must establish confinement.
-/
structure TernaryConfinementCertificate (source : Picture G P C)
    (A : AmalgamationData source Q D I) : Prop where
  k4MinusFree : G.K4MinusFree
  confined : EveryQuasilineConfined source A

/--
Once sparse incidence gives confinement, a partite amalgamation is again a
picture.  This is the formal transport step of the RRS proof.
-/
noncomputable def amalgamationPicture (source : Picture G P C)
    (A : AmalgamationData source Q D I)
    (hconf : EveryQuasilineConfined source A) : Picture G Q D where
  embed := A.embed
  embed_injective := A.embed_injective
  proj := A.proj
  quasiline_is_line := by
    intro l hl
    obtain ⟨i, lp, hlp, hcopy⟩ := hconf l hl
    have hline := A.transports_lines i lp (source.quasiline_is_line lp hlp)
    have hl_eq : l = fun a => A.copy i (lp a) := funext hcopy
    rw [hl_eq]
    exact hline
  quasiline_maps_edge := by
    intro l hl
    obtain ⟨i, lp, hlp, hcopy⟩ := hconf l hl
    obtain ⟨e, he⟩ := source.quasiline_maps_edge lp hlp
    refine ⟨e, ?_⟩
    have hl_eq : l = fun a => A.copy i (lp a) := funext hcopy
    rw [hl_eq]
    simpa only [A.proj_copy] using he

/--
The ternary, `K₄³-minus-free` formulation used by RRS.  The first field of
the certificate is consumed by the incidence proof which constructs the
second; preservation itself only transports the second field.
-/
theorem amalgamation_preserves (source : Picture G P C)
    (A : AmalgamationData source Q D I)
    (h : TernaryConfinementCertificate source A) :
    ∃ result : Picture G Q D,
      result.embed = A.embed ∧ result.proj = A.proj := by
  let result := amalgamationPicture source A h.confined
  exact ⟨result, rfl, rfl⟩

end Amalgamation

section RawPartiteAmalgamation

/-!
The remainder of this file constructs the actual union of standard copies
used in Proposition 4.5 of Reiher--Rödl--Sales.  Unlike `AmalgamationData`,
the point type below is literally a subtype of the outer word cube.
-/

variable {V P C N : Type*} [DecidableEq V]
variable {G : ThreeGraph V}

/-- The music line over `x`, regarded as an alphabet in its own right. -/
abbrev MusicFiber (source : Picture G P C) (x : V) :=
  {p : P // source.proj p = x}

/--
At outer coordinate `s`, a standard copy either uses the source point `p`
(a moving coordinate of `U`) or the fixed music-line point stored by `U`.
-/
def sectionPoint (source : Picture G P C) (x : V)
    (U : Combinatorics.Line (MusicFiber source x) N) (p : P) (s : N) : P :=
  ((U.idxFun s).map Subtype.val).getD p

/-- The coordinate-block extension `η⁺_U` of a line over the music line. -/
def extendWord (source : Picture G P C) (x : V)
    (U : Combinatorics.Line (MusicFiber source x) N) (p : P) :
    N × C → Alphabet :=
  fun sc => source.embed (sectionPoint source x U p sc.1) sc.2

@[simp]
theorem sectionPoint_none (source : Picture G P C) (x : V)
    (U : Combinatorics.Line (MusicFiber source x) N) (p : P) (s : N)
    (hs : U.idxFun s = none) :
    sectionPoint source x U p s = p := by
  simp [sectionPoint, hs]

@[simp]
theorem sectionPoint_some (source : Picture G P C) (x : V)
    (U : Combinatorics.Line (MusicFiber source x) N) (p : P) (s : N)
    (f : MusicFiber source x) (hs : U.idxFun s = some f) :
    sectionPoint source x U p s = f.1 := by
  simp [sectionPoint, hs]

theorem sectionPoint_mem_fiber_or_eq (source : Picture G P C) (x : V)
    (U : Combinatorics.Line (MusicFiber source x) N) (p : P) (s : N) :
    source.proj (sectionPoint source x U p s) = x ∨
      sectionPoint source x U p s = p := by
  cases hs : U.idxFun s with
  | none => exact Or.inr (sectionPoint_none source x U p s hs)
  | some f =>
      left
      rw [sectionPoint_some source x U p s f hs]
      exact f.2

theorem moving_iff_sectionPoint_eq (source : Picture G P C) (x : V)
    (U : Combinatorics.Line (MusicFiber source x) N) (p : P)
    (hp : source.proj p ≠ x) (s : N) :
    U.idxFun s = none ↔ sectionPoint source x U p s = p := by
  constructor
  · exact sectionPoint_none source x U p s
  · intro hsec
    cases hs : U.idxFun s with
    | none => rfl
    | some f =>
        exfalso
        have hfp : f.1 = p := by
          simpa [sectionPoint, hs] using hsec
        exact hp (hfp.symm ▸ f.2)

theorem fixed_value_of_sectionPoint_eq (source : Picture G P C) (x : V)
    (U : Combinatorics.Line (MusicFiber source x) N) (p q : P)
    (hp : source.proj p ≠ x) (hq : source.proj q = x) (s : N)
    (hsec : sectionPoint source x U p s = q) :
    ∃ f : MusicFiber source x, U.idxFun s = some f ∧ f.1 = q := by
  cases hs : U.idxFun s with
  | none =>
      exfalso
      have hpq : p = q := by simpa [sectionPoint, hs] using hsec
      exact hp (hpq ▸ hq)
  | some f =>
      exact ⟨f, rfl, by simpa [sectionPoint, hs] using hsec⟩

theorem extendWord_section_injective (source : Picture G P C) (x : V)
    {U W : Combinatorics.Line (MusicFiber source x) N} {p q : P}
    (h : extendWord source x U p = extendWord source x W q) (s : N) :
    sectionPoint source x U p s = sectionPoint source x W q s := by
  apply source.embed_injective
  funext c
  exact congrFun h (s, c)

/-- Every standard-copy embedding is injective. -/
theorem extendWord_injective (source : Picture G P C) (x : V)
    (U : Combinatorics.Line (MusicFiber source x) N) :
    Injective (extendWord source x U) := by
  intro p q hpq
  obtain ⟨s, hs⟩ := U.proper
  have hsec := extendWord_section_injective source x hpq s
  simpa [sectionPoint, hs] using hsec

/--
If two extended words agree and the first source point is not on the music
line, then the two line indices and the two source points agree.  This is the
uniqueness assertion behind Fact 4.4(ii).
-/
theorem extendWord_eq_of_not_mem_fiber (source : Picture G P C) (x : V)
    {U W : Combinatorics.Line (MusicFiber source x) N} {p q : P}
    (hp : source.proj p ≠ x)
    (h : extendWord source x U p = extendWord source x W q) :
    U = W ∧ p = q := by
  obtain ⟨s, hs⟩ := U.proper
  have hsecs := extendWord_section_injective source x h s
  have hWs : W.idxFun s = none := by
    cases hcase : W.idxFun s with
    | none => rfl
    | some f =>
        exfalso
        have hp_eq : p = f.1 := by
          simpa [sectionPoint, hs, hcase] using hsecs
        exact hp (hp_eq ▸ f.2)
  have hpq : p = q := by
    simpa [sectionPoint, hs, hWs] using hsecs
  subst q
  have hidx : U.idxFun = W.idxFun := by
    funext t
    have ht := extendWord_section_injective source x h t
    cases hU : U.idxFun t with
    | none =>
        cases hW : W.idxFun t with
        | none => rfl
        | some f =>
            exfalso
            have hp_eq : p = f.1 := by
              simpa [sectionPoint, hU, hW] using ht
            exact hp (hp_eq ▸ f.2)
    | some f =>
        cases hW : W.idxFun t with
        | none =>
            exfalso
            have hp_eq : f.1 = p := by
              simpa [sectionPoint, hU, hW] using ht
            exact hp (hp_eq.symm ▸ f.2)
        | some g =>
            have hfg : f = g := Subtype.ext <| by
              simpa [sectionPoint, hU, hW] using ht
            simp [hU, hW, hfg]
  have hUW : U = W := by
    cases U
    cases W
    simp_all only [Combinatorics.Line.mk.injEq]
  exact ⟨hUW, rfl⟩

/-- Fact 4.4(ii), in its representative form. -/
theorem standard_copies_intersect_only_in_fiber
    (source : Picture G P C) (x : V)
    {U W : Combinatorics.Line (MusicFiber source x) N} {p q : P}
    (hUW : U ≠ W)
    (h : extendWord source x U p = extendWord source x W q) :
    source.proj p = x ∧ source.proj q = x := by
  constructor
  · by_contra hp
    exact hUW (extendWord_eq_of_not_mem_fiber source x hp h).1
  · by_contra hq
    have h' : extendWord source x W q = extendWord source x U p := h.symm
    exact hUW (extendWord_eq_of_not_mem_fiber source x hq h').1.symm

/-- The literal union of all selected standard-copy word images. -/
def IsAmalgamWord (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (w : N × C → Alphabet) : Prop :=
  ∃ U, U ∈ lines ∧ ∃ p, w = extendWord source x U p

abbrev RawAmalgamPoint (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N)) :=
  {w : N × C → Alphabet // IsAmalgamWord source x lines w}

/-- A chosen source representative of a point in the union. -/
noncomputable def rawRepresentative (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (q : RawAmalgamPoint source x lines) : P :=
  Classical.choose (Classical.choose_spec q.2).2

/-- The line index chosen together with `rawRepresentative`. -/
noncomputable def rawRepresentativeLine (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (q : RawAmalgamPoint source x lines) :
    Combinatorics.Line (MusicFiber source x) N :=
  Classical.choose q.2

theorem rawRepresentativeLine_mem (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (q : RawAmalgamPoint source x lines) :
    rawRepresentativeLine source x lines q ∈ lines :=
  (Classical.choose_spec q.2).1

theorem rawRepresentative_spec (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (q : RawAmalgamPoint source x lines) :
    q.1 = extendWord source x (rawRepresentativeLine source x lines q)
      (rawRepresentative source x lines q) :=
  Classical.choose_spec (Classical.choose_spec q.2).2

/-- The projection on the union, defined using an arbitrary representative. -/
noncomputable def rawProj (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (q : RawAmalgamPoint source x lines) : V :=
  source.proj (rawRepresentative source x lines q)

/-- The embedding of a selected standard copy into the literal union. -/
def standardCopy (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (U : Combinatorics.Line (MusicFiber source x) N) (hU : U ∈ lines)
    (p : P) : RawAmalgamPoint source x lines :=
  ⟨extendWord source x U p, U, hU, p, rfl⟩

theorem standardCopy_injective (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (U : Combinatorics.Line (MusicFiber source x) N) (hU : U ∈ lines) :
    Injective (standardCopy source x lines U hU) := by
  intro p q hpq
  exact extendWord_injective source x U (congrArg Subtype.val hpq)

/-- The projection is independent of the representative used to define it. -/
theorem rawProj_standardCopy (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (U : Combinatorics.Line (MusicFiber source x) N) (hU : U ∈ lines)
    (p : P) :
    rawProj source x lines (standardCopy source x lines U hU p) = source.proj p := by
  unfold rawProj
  let W := rawRepresentativeLine source x lines
    (standardCopy source x lines U hU p)
  let q := rawRepresentative source x lines
    (standardCopy source x lines U hU p)
  have heq : extendWord source x W q = extendWord source x U p := by
    exact (rawRepresentative_spec source x lines
      (standardCopy source x lines U hU p)).symm
  by_cases hWU : W = U
  · have hqp : q = p := extendWord_injective source x U <| by
      simpa [W, hWU] using heq
    simpa [q, hqp]
  · obtain ⟨hq, hp⟩ := standard_copies_intersect_only_in_fiber source x hWU heq
    exact hq.trans hp.symm

/-- The ambient-word embedding of the literal union. -/
def rawEmbed (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (q : RawAmalgamPoint source x lines) : N × C → Alphabet := q.1

theorem rawEmbed_injective (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N)) :
    Injective (rawEmbed source x lines) :=
  Subtype.val_injective

/-- A source combinatorial line remains a line in every standard copy. -/
theorem standardCopy_transports_line (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (U : Combinatorics.Line (MusicFiber source x) N) (hU : U ∈ lines)
    (l : Alphabet → P) (hl : IsCombinatorialLine source.embed l) :
    IsCombinatorialLine (rawEmbed source x lines)
      (fun a => standardCopy source x lines U hU (l a)) := by
  rcases hl with ⟨hlinj, σ, hσ⟩
  refine ⟨(standardCopy_injective source x lines U hU).comp hlinj, σ, ?_⟩
  rintro ⟨s, c⟩
  cases hs : U.idxFun s with
  | none =>
      rcases hσ c with hconst | hmove
      · left
        obtain ⟨a, ha⟩ := hconst
        exact ⟨a, fun i => by simpa [rawEmbed, standardCopy, extendWord,
          sectionPoint, hs] using ha i⟩
      · right
        intro i
        simpa [rawEmbed, standardCopy, extendWord, sectionPoint, hs] using hmove i
  | some f =>
      left
      refine ⟨source.embed f.1 c, ?_⟩
      intro i
      simp [rawEmbed, standardCopy, extendWord, sectionPoint, hs]

/-- The raw construction supplies the formal standard-copy transport data. -/
noncomputable def rawAmalgamationData (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N)) :
    AmalgamationData source (RawAmalgamPoint source x lines) (N × C)
      {U // U ∈ lines} where
  embed := rawEmbed source x lines
  embed_injective := rawEmbed_injective source x lines
  proj := rawProj source x lines
  copy U := standardCopy source x lines U.1 U.2
  copy_injective U := standardCopy_injective source x lines U.1 U.2
  proj_copy U := rawProj_standardCopy source x lines U.1 U.2
  transports_lines U := standardCopy_transports_line source x lines U.1 U.2

/-- Intersection of two combinatorial lines, as sets of words. -/
def RawLinesIntersect {A I : Type*}
    (U W : Combinatorics.Line A I) : Prop :=
  ∃ a b, U a = W b

/-- Three lines have a common point. -/
def RawLinesCommonPoint {A I : Type*}
    (U W Z : Combinatorics.Line A I) : Prop :=
  ∃ a b c, U a = W b ∧ W b = Z c

/-- The moving-coordinate set of a raw Hales--Jewett line. -/
def RawMovingSet {A I : Type*} (U : Combinatorics.Line A I) : Set I :=
  {i | U.idxFun i = none}

/-- `U` has moving set equal to the disjoint union of those of `W` and `Z`. -/
def RawMovingDisjointUnion {A I : Type*}
    (U W Z : Combinatorics.Line A I) : Prop :=
  RawMovingSet U = RawMovingSet W ∪ RawMovingSet Z ∧
    Disjoint (RawMovingSet W) (RawMovingSet Z)

/--
The exact RRS tripod (Definition 3.6): three distinct concurrent lines, with
the moving set of one line the disjoint union of the other two.  Since a
line system is unordered, any of the three lines may be the union line.
-/
def IsRawTripod {A I : Type*}
    (U W Z : Combinatorics.Line A I) : Prop :=
  U ≠ W ∧ U ≠ Z ∧ W ≠ Z ∧ RawLinesCommonPoint U W Z ∧
    (RawMovingDisjointUnion U W Z ∨ RawMovingDisjointUnion W U Z ∨
      RawMovingDisjointUnion Z U W)

/-- A triangle consists of three distinct pairwise-intersecting lines with no
common point. -/
def IsRawTriangle {A I : Type*}
    (U W Z : Combinatorics.Line A I) : Prop :=
  U ≠ W ∧ U ≠ Z ∧ W ≠ Z ∧
    RawLinesIntersect U W ∧ RawLinesIntersect U Z ∧ RawLinesIntersect W Z ∧
    ¬ RawLinesCommonPoint U W Z

def RawLineSystemHasNoTripod {A I : Type*}
    (lines : Set (Combinatorics.Line A I)) : Prop :=
  ∀ ⦃U W Z⦄, U ∈ lines → W ∈ lines → Z ∈ lines → ¬ IsRawTripod U W Z

def RawLineSystemHasNoTriangle {A I : Type*}
    (lines : Set (Combinatorics.Line A I)) : Prop :=
  ∀ ⦃U W Z⦄, U ∈ lines → W ∈ lines → Z ∈ lines → ¬ IsRawTriangle U W Z

/-- Projection along an indexed source quasiline is injective, since it maps
onto a three-element edge. -/
theorem mapsOntoEdge_proj_injective (source : Picture G P C)
    {l : Alphabet → P} (hl : MapsOntoEdge G source.proj l) :
    Injective (fun i => source.proj (l i)) := by
  obtain ⟨e, he⟩ := hl
  let f : Alphabet → {v : V // v ∈ e.1} := fun i =>
    ⟨source.proj (l i), by
      have hi : source.proj (l i) ∈ Set.range (fun j => source.proj (l j)) :=
        Set.mem_range_self i
      rw [he] at hi
      exact hi⟩
  have hsurj : Surjective f := by
    intro v
    have hv : (v.1 : V) ∈ Set.range (fun i => source.proj (l i)) := by
      rw [he]
      exact v.2
    obtain ⟨i, hi⟩ := hv
    exact ⟨i, Subtype.ext hi⟩
  have hinj : Injective f :=
    hsurj.injective_of_finite (G.edgeEquiv e)
  intro i j hij
  apply hinj
  exact Subtype.ext hij

/-- In a linear base 3-graph, two projected ternary lines which share two
projected vertices also share their third projected vertex. -/
theorem linear_forces_third_projection (source : Picture G P C)
    (hlinear : G.Linear) (k t : Alphabet → P)
    (hk : MapsOntoEdge G source.proj k)
    (ht : MapsOntoEdge G source.proj t)
    (hcommon₀ : source.proj (k 0) = source.proj (t 0))
    (hcommon₁ : source.proj (k 2) = source.proj (t 1)) :
    source.proj (k 1) = source.proj (t 2) := by
  have hkinj := mapsOntoEdge_proj_injective source hk
  have htinj := mapsOntoEdge_proj_injective source ht
  obtain ⟨e, he⟩ := hk
  obtain ⟨f, hf⟩ := ht
  have hkIn (i : Alphabet) : source.proj (k i) ∈ e.1 := by
    have hi : source.proj (k i) ∈ Set.range (fun j => source.proj (k j)) :=
      Set.mem_range_self i
    rw [he] at hi
    exact hi
  have htIn (i : Alphabet) : source.proj (t i) ∈ f.1 := by
    have hi : source.proj (t i) ∈ Set.range (fun j => source.proj (t j)) :=
      Set.mem_range_self i
    rw [hf] at hi
    exact hi
  have hxy : source.proj (k 0) ≠ source.proj (k 2) := by
    intro h
    exact (by decide : (0 : Alphabet) ≠ 2) (hkinj h)
  have hsub : ({source.proj (k 0), source.proj (k 2)} : Finset V) ⊆
      e.1 ∩ f.1 := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Finset.mem_inter]
    rcases hy with rfl | rfl
    · exact ⟨hkIn 0, hcommon₀ ▸ htIn 0⟩
    · exact ⟨hkIn 2, hcommon₁ ▸ htIn 1⟩
  have hef : e = f := hlinear e f <| by
    calc
      2 = ({source.proj (k 0), source.proj (k 2)} : Finset V).card := by
        simp [hxy]
      _ ≤ (e.1 ∩ f.1).card := Finset.card_le_card hsub
  have hzIn : source.proj (k 1) ∈
      Set.range (fun j => source.proj (t j)) := by
    rw [hf]
    rw [← hef]
    exact hkIn 1
  obtain ⟨j, hj⟩ := hzIn
  fin_cases j
  · exfalso
    have heq : source.proj (k 0) = source.proj (k 1) := hcommon₀.trans hj
    exact (by decide : (0 : Alphabet) ≠ 1) (hkinj heq)
  · exfalso
    have heq : source.proj (k 2) = source.proj (k 1) := hcommon₁.trans hj
    exact (by decide : (2 : Alphabet) ≠ 1) (hkinj heq)
  · exact hj.symm

/--
For a quasiline in the outer cube, every outer-coordinate section is either
constant or a source quasiline.  This is the first reduction in Proposition
4.5.
-/
theorem raw_quasiline_section (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (l : Alphabet → RawAmalgamPoint source x lines)
    (U : Alphabet → Combinatorics.Line (MusicFiber source x) N)
    (p : Alphabet → P)
    (hword : ∀ i, (l i).1 = extendWord source x (U i) (p i))
    (hl : IsQuasiline (rawEmbed source x lines) l) (s : N) :
    (∃ q, ∀ i, sectionPoint source x (U i) (p i) s = q) ∨
      IsQuasiline source.embed
        (fun i => sectionPoint source x (U i) (p i) s) := by
  let sec : Alphabet → P := fun i => sectionPoint source x (U i) (p i) s
  by_cases hinj : Injective sec
  · right
    refine ⟨hinj, ?_⟩
    intro c
    simpa [rawEmbed, sec, hword, extendWord] using hl.2 (s, c)
  · left
    rw [not_injective_iff] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    have hconst_coord : ∀ c, ∃ a, ∀ k, source.embed (sec k) c = a := by
      intro c
      rcases hl.2 (s, c) with hconst | hcoordinj
      · simpa [rawEmbed, sec, hword, extendWord] using hconst
      · exfalso
        apply hne
        apply hcoordinj
        simpa [rawEmbed, sec, hword, extendWord] using
          congrArg (fun q => source.embed q c) hij
    refine ⟨sec 0, ?_⟩
    intro k
    apply source.embed_injective
    funext c
    obtain ⟨a, ha⟩ := hconst_coord c
    exact (ha k).trans (ha 0).symm

theorem raw_quasiline_has_source_section (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (l : Alphabet → RawAmalgamPoint source x lines)
    (U : Alphabet → Combinatorics.Line (MusicFiber source x) N)
    (p : Alphabet → P)
    (hword : ∀ i, (l i).1 = extendWord source x (U i) (p i))
    (hl : IsQuasiline (rawEmbed source x lines) l) :
    ∃ s, IsQuasiline source.embed
      (fun i => sectionPoint source x (U i) (p i) s) := by
  by_contra hnone
  push Not at hnone
  have hconstant : ∀ s, ∃ q, ∀ i,
      sectionPoint source x (U i) (p i) s = q := by
    intro s
    rcases raw_quasiline_section source x lines l U p hword hl s with hconst | hline
    · exact hconst
    · exact False.elim (hnone s hline)
  have h01 : l 0 = l 1 := by
    apply Subtype.ext
    funext sc
    obtain ⟨q, hq⟩ := hconstant sc.1
    rw [hword 0, hword 1]
    simp only [extendWord]
    rw [hq 0, hq 1]
  exact Fin.zero_ne_one (hl.1 h01)

/-- If a predicate holds for at most one ternary index, a permutation puts
two indices where it fails into positions `0` and `1`. -/
theorem exists_perm_two_not {R : Alphabet → Prop}
    (hatMostOne : ∀ i j, R i → R j → i = j) :
    ∃ σ : Equiv.Perm Alphabet, ¬ R (σ 0) ∧ ¬ R (σ 1) := by
  classical
  have hpairs : ∃ i j : Alphabet, i ≠ j ∧ ¬ R i ∧ ¬ R j := by
    by_cases h0 : R 0
    · by_cases h1 : R 1
      · exact False.elim (Fin.zero_ne_one (hatMostOne 0 1 h0 h1))
      · by_cases h2 : R 2
        · exact False.elim (by
            have h02 : (0 : Alphabet) = 2 := hatMostOne 0 2 h0 h2
            exact (by decide : (0 : Alphabet) ≠ 2) h02)
        · exact ⟨1, 2, by decide, h1, h2⟩
    · by_cases h1 : R 1
      · by_cases h2 : R 2
        · exact False.elim (by
            have h12 : (1 : Alphabet) = 2 := hatMostOne 1 2 h1 h2
            exact (by decide : (1 : Alphabet) ≠ 2) h12)
        · exact ⟨0, 2, by decide, h0, h2⟩
      · exact ⟨0, 1, by decide, h0, h1⟩
  obtain ⟨i, j, hij, hi, hj⟩ := hpairs
  let f : Fin 2 → Alphabet := fun a => ⟨a.1, by omega⟩
  let g : Fin 2 → Alphabet := Fin.cases i (fun _ => j)
  have hf : Injective f := by
    intro a b hab
    exact Fin.ext (Fin.mk.inj_iff.mp hab)
  have hg : Injective g := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exfalso
      change i = j at hab
      exact hij hab
    · exfalso
      change j = i at hab
      exact hij hab.symm
    · rfl
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨σ, ?_, ?_⟩
  · simpa [f, g] using hσ 0 ▸ hi
  · simpa [f, g] using hσ 1 ▸ hj

/-- Normal form used at the start of the ternary proof of Proposition 4.5. -/
structure NormalizedRawQuasiline (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (l : Alphabet → RawAmalgamPoint source x lines) where
  perm : Equiv.Perm Alphabet
  line : Alphabet → Combinatorics.Line (MusicFiber source x) N
  point : Alphabet → P
  coordinate : N
  line_mem : ∀ i, line i ∈ lines
  word_eq : ∀ i, (l (perm i)).1 = extendWord source x (line i) (point i)
  outer_quasiline : IsQuasiline (rawEmbed source x lines) (fun i => l (perm i))
  source_section : IsQuasiline source.embed
    (fun i => sectionPoint source x (line i) (point i) coordinate)
  point_zero_not_fiber : source.proj (point 0) ≠ x
  point_one_not_fiber : source.proj (point 1) ≠ x
  section_zero : sectionPoint source x (line 0) (point 0) coordinate = point 0
  section_one : sectionPoint source x (line 1) (point 1) coordinate = point 1

theorem normalize_raw_quasiline (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (l : Alphabet → RawAmalgamPoint source x lines)
    (hl : IsQuasiline (rawEmbed source x lines) l) :
    Nonempty (NormalizedRawQuasiline source x lines l) := by
  classical
  let U : Alphabet → Combinatorics.Line (MusicFiber source x) N :=
    fun i => rawRepresentativeLine source x lines (l i)
  let p : Alphabet → P := fun i => rawRepresentative source x lines (l i)
  have hU (i : Alphabet) : U i ∈ lines :=
    rawRepresentativeLine_mem source x lines (l i)
  have hword (i : Alphabet) :
      (l i).1 = extendWord source x (U i) (p i) :=
    rawRepresentative_spec source x lines (l i)
  obtain ⟨s, hs⟩ := raw_quasiline_has_source_section source x lines l U p hword hl
  let sec : Alphabet → P := fun i => sectionPoint source x (U i) (p i) s
  have hprojInj : Injective (fun i => source.proj (sec i)) :=
    mapsOntoEdge_proj_injective source (source.quasiline_maps_edge sec hs)
  have hatMostOne : ∀ i j, source.proj (sec i) = x →
      source.proj (sec j) = x → i = j := by
    intro i j hi hj
    exact hprojInj (hi.trans hj.symm)
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_two_not hatMostOne
  let U' : Alphabet → Combinatorics.Line (MusicFiber source x) N := fun i => U (σ i)
  let p' : Alphabet → P := fun i => p (σ i)
  have hsec0 : sectionPoint source x (U' 0) (p' 0) s = p' 0 := by
    apply (sectionPoint_mem_fiber_or_eq source x (U' 0) (p' 0) s).resolve_left
    exact hσ0
  have hsec1 : sectionPoint source x (U' 1) (p' 1) s = p' 1 := by
    apply (sectionPoint_mem_fiber_or_eq source x (U' 1) (p' 1) s).resolve_left
    exact hσ1
  have hp0 : source.proj (p' 0) ≠ x := by simpa [sec, U', p', hsec0] using hσ0
  have hp1 : source.proj (p' 1) ≠ x := by simpa [sec, U', p', hsec1] using hσ1
  have houter : IsQuasiline (rawEmbed source x lines) (fun i => l (σ i)) := by
    refine ⟨hl.1.comp σ.injective, ?_⟩
    intro c
    rcases hl.2 c with ⟨a, ha⟩ | hinj
    · exact Or.inl ⟨a, fun i => ha (σ i)⟩
    · exact Or.inr (hinj.comp σ.injective)
  have hsource : IsQuasiline source.embed
      (fun i => sectionPoint source x (U' i) (p' i) s) := by
    refine ⟨hs.1.comp σ.injective, ?_⟩
    intro c
    rcases hs.2 c with ⟨a, ha⟩ | hinj
    · exact Or.inl ⟨a, fun i => ha (σ i)⟩
    · exact Or.inr (hinj.comp σ.injective)
  exact ⟨{
    perm := σ
    line := U'
    point := p'
    coordinate := s
    line_mem := fun i => hU (σ i)
    word_eq := fun i => hword (σ i)
    outer_quasiline := houter
    source_section := hsource
    point_zero_not_fiber := hp0
    point_one_not_fiber := hp1
    section_zero := hsec0
    section_one := hsec1
  }⟩

end RawPartiteAmalgamation

end Erdos847Pictures

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/Iteration.lean` -/

section
/-
# Abstract iteration for the Reiher--Rödl--Sales pictures

The incidence geometry of a single partite amalgamation is isolated in
`Erdos847Pictures`.  This file formalizes the other half of the argument:
successive amalgamations over the fibers of the projection, followed by the
backward color-focusing argument.

The only input left abstract is `oneFiberAmalgamate`.  It is an ordinary
parameter of the iteration theorem, with no global declaration: supplied with a sparse,
high-chromatic family over one fiber, it returns a new picture together with
its standard copies.  Everything after that construction is proved here.
-/

namespace Erdos847Iteration

open Function Set
open Erdos847Pictures

set_option autoImplicit false

universe uV uP uC uK

variable {V : Type uV} [DecidableEq V]
variable {G : ThreeGraph V}

/-! ## Ramsey and independence predicates -/

namespace ThreeGraph

/-- Every coloring of the vertices by `K` has a monochromatic edge. -/
def RamseyFor (G : ThreeGraph V) (K : Type uK) : Prop :=
  ∀ color : V → K,
    ∃ e : G.Edge, ∃ k : K, ∀ v ∈ e.1, color v = k

/-- A finite vertex set containing no edge of `G`. -/
def Independent (G : ThreeGraph V) (I : Finset V) : Prop :=
  ∀ e ∈ G.edges, ¬e ⊆ I

end ThreeGraph

section PicturePredicates

variable {P : Type uP} {C : Type uC}

/-- A picture has a monochromatic combinatorial line in every `K`-coloring. -/
def PictureRamseyFor (picture : Picture G P C) (K : Type uK) : Prop :=
  ∀ color : P → K,
    ∃ l : Alphabet → P, IsCombinatorialLine picture.embed l ∧
      ∃ k : K, ∀ a, color (l a) = k

/-- The initial picture must contain a selected line above every base edge. -/
def RealizesEveryEdge (picture : Picture G P C) : Prop :=
  ∀ e : G.Edge,
    ∃ l : Alphabet → P, IsCombinatorialLine picture.embed l ∧
      Set.range (fun a => picture.proj (l a)) = (e.1 : Set V)

end PicturePredicates

/-! ## The one-fiber construction interface -/

section SparseFamilies

variable {P : Type uP} {C : Type uC}

/-- The fiber (music line) of a picture above a base vertex. -/
abbrev Fiber (picture : Picture G P C) (x : V) :=
  {p : P // picture.proj p = x}

/-- The exact RRS tripod pattern, stated for an abstract moving-support map:
three pairwise distinct lines have a common word and, after relabeling, the
moving support of the first is the disjoint union of the other two. -/
def HasTripod {W I M : Type*} (line : I → Set W)
    (movingSupport : I → Set M) : Prop :=
  ∃ i j k : I, i ≠ j ∧ j ≠ k ∧ k ≠ i ∧
    (∃ w, w ∈ line i ∧ w ∈ line j ∧ w ∈ line k) ∧
    movingSupport i = movingSupport j ∪ movingSupport k ∧
    Disjoint (movingSupport j) (movingSupport k)

/-- Three members of a set system with three distinct pairwise intersection
points.  This is the triangle configuration excluded by the sparse line
system in the ternary amalgamation. -/
def HasTriangle {W I : Type*} (line : I → Set W) : Prop :=
  ∃ i j k : I, i ≠ j ∧ j ≠ k ∧ k ≠ i ∧
    (line i ∩ line j).Nonempty ∧
    (line j ∩ line k).Nonempty ∧
    (line k ∩ line i).Nonempty ∧
    line i ∩ line j ∩ line k = ∅

/--
The abstract output of the sparse Hales--Jewett lemma over one fiber.
`highChromatic` is precisely the property used by backward focusing; the two
remaining fields record the incidence hypotheses used by the one-fiber
amalgamation theorem.
-/
structure SparseFiberLineFamily
    (picture : Picture G P C) (x : V) (K : Type uK) where
  Word : Type uP
  Index : Type uP
  Move : Type uP
  line : Index → Fiber picture x → Word
  movingSupport : Index → Set Move
  line_injective : ∀ i, Injective (line i)
  highChromatic : ∀ color : Word → K,
    ∃ i : Index, ∃ k : K, ∀ a, color (line i a) = k
  noTripod : ¬HasTripod (fun i => Set.range (line i)) movingSupport
  noTriangle : ¬HasTriangle (fun i => Set.range (line i))

end SparseFamilies

section StandardCopies

variable {P : Type uP} {C : Type uC}
variable {Q : Type uP} {D : Type uC}

/-- A standard copy preserves the projection and transports all selected
combinatorial lines. -/
structure StandardCopy (source : Picture G P C) (target : Picture G Q D)
    (copy : P → Q) : Prop where
  injective : Injective copy
  proj_copy : ∀ p, target.proj (copy p) = source.proj p
  transports_lines : ∀ l,
    IsCombinatorialLine source.embed l →
      IsCombinatorialLine target.embed (fun a => copy (l a))

namespace StandardCopy

theorem refl (picture : Picture G P C) :
    StandardCopy picture picture id where
  injective := injective_id
  proj_copy := by intro p; rfl
  transports_lines := by intro l hl; simpa using hl

theorem comp {R : Type uP} {E : Type uC}
    {source : Picture G P C} {middle : Picture G Q D}
    {target : Picture G R E} {f : P → Q} {g : Q → R}
    (hf : StandardCopy source middle f)
    (hg : StandardCopy middle target g) :
    StandardCopy source target (g ∘ f) where
  injective := hg.injective.comp hf.injective
  proj_copy := by
    intro p
    exact (hg.proj_copy (f p)).trans (hf.proj_copy p)
  transports_lines := by
    intro l hl
    simpa only [Function.comp_apply] using
      hg.transports_lines (fun a => f (l a)) (hf.transports_lines l hl)

/-- A standard copy transports nontriviality of every source fiber to the
corresponding target fiber.  This is the convenient way for a concrete
one-fiber amalgamation to fill `FiberExtension.targetFiberNontrivial`. -/
theorem targetFiberNontrivial
    {source : Picture G P C} {target : Picture G Q D} {copy : P → Q}
    (hcopy : StandardCopy source target copy)
    (hsource : ∀ x : V, Nontrivial (Fiber source x)) (x : V) :
    Nontrivial (Fiber target x) := by
  let copyFiber : Fiber source x → Fiber target x := fun p =>
    ⟨copy p.1, (hcopy.proj_copy p.1).trans p.2⟩
  have hinjective : Injective copyFiber := by
    intro p q hpq
    apply Subtype.ext
    exact hcopy.injective (congrArg Subtype.val hpq)
  exact @Function.Injective.nontrivial _ _ (hsource x) copyFiber hinjective

end StandardCopy

/--
Abstract result of one actual RRS amalgamation.  The sparse family and the
incidence proof are consumed by the construction producing this structure.
For each coloring, `focus` selects a standard copy on which the chosen fiber
is monochromatic.
-/
structure FiberExtension (source : Picture G P C) (x : V) (K : Type uK) where
  Point : Type uP
  Coord : Type uC
  pointFintype : Fintype Point
  coordFintype : Fintype Coord
  target : Picture G Point Coord
  targetFiberNontrivial : ∀ y : V, Nontrivial (Fiber target y)
  focus : ∀ color : Point → K,
    ∃ copy : P → Point, StandardCopy source target copy ∧
      ∃ k : K, ∀ p, source.proj p = x → color (copy p) = k

/-- A composite standard copy in which all fibers listed in `vertices` have
already been focused. -/
structure FocusedExtension
    (source : Picture G P C) (vertices : List V) (K : Type uK) where
  Point : Type uP
  Coord : Type uC
  pointFintype : Fintype Point
  coordFintype : Fintype Coord
  target : Picture G Point Coord
  targetFiberNontrivial : ∀ x : V, Nontrivial (Fiber target x)
  focused : ∀ color : Point → K,
    ∃ copy : P → Point, StandardCopy source target copy ∧
      ∀ x ∈ vertices, ∃ k : K, ∀ p,
        source.proj p = x → color (copy p) = k

/-- Before any amalgamation, the identity copy focuses the empty list. -/
noncomputable def FocusedExtension.nil
    [Fintype P] [Fintype C]
    (source : Picture G P C) (K : Type uK)
    (sourceFiberNontrivial : ∀ x : V, Nontrivial (Fiber source x)) :
    FocusedExtension source [] K where
  Point := P
  Coord := C
  pointFintype := inferInstance
  coordFintype := inferInstance
  target := source
  targetFiberNontrivial := sourceFiberNontrivial
  focused := by
    intro color
    exact ⟨id, StandardCopy.refl source, by simp⟩

/-- One backward-focusing step.  Old fiber colors survive because a standard
copy commutes with the projection. -/
noncomputable def FocusedExtension.cons
    {source : Picture G P C} {K : Type uK}
    {vertices : List V} {x : V}
    (old : FocusedExtension source vertices K)
    (step : FiberExtension old.target x K) :
    FocusedExtension source (x :: vertices) K where
  Point := step.Point
  Coord := step.Coord
  pointFintype := step.pointFintype
  coordFintype := step.coordFintype
  target := step.target
  targetFiberNontrivial := step.targetFiberNontrivial
  focused := by
    intro color
    obtain ⟨f, hf, kx, hx⟩ := step.focus color
    obtain ⟨g, hg, hold⟩ := old.focused (fun q => color (f q))
    refine ⟨f ∘ g, hg.comp hf, ?_⟩
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · refine ⟨kx, ?_⟩
      intro p hp
      exact hx (g p) ((hg.proj_copy p).trans hp)
    · obtain ⟨ky, hky⟩ := hold y hy
      exact ⟨ky, by simpa only [Function.comp_apply] using hky⟩

end StandardCopies

/-! ## Finite iteration and the Ramsey conclusion -/

section Iteration

variable {P : Type uP} {C : Type uC}

/-- Iterate the supplied one-fiber construction over a finite list of base
vertices.  The construction hypothesis is explicitly parameterized by the
sparse family it consumes. -/
noncomputable def iterate
    [Fintype P] [Fintype C]
    (source : Picture G P C) (K : Type uK) (vertices : List V)
    (sourceFiberNontrivial : ∀ x : V, Nontrivial (Fiber source x))
    (family : ∀ {P' : Type uP} {C' : Type uC}
      [Fintype P'] [Fintype C']
      (picture : Picture G P' C') (x : V)
      [Nontrivial (Fiber picture x)],
        SparseFiberLineFamily picture x K)
    (oneFiberAmalgamate : ∀ {P' : Type uP} {C' : Type uC}
      [Fintype P'] [Fintype C']
      (picture : Picture G P' C')
      (sourceFibers : ∀ y : V, Nontrivial (Fiber picture y))
      (x : V)
      [Nontrivial (Fiber picture x)]
      (_lines : SparseFiberLineFamily picture x K),
        FiberExtension picture x K) :
    FocusedExtension source vertices K := by
  induction vertices with
  | nil => exact FocusedExtension.nil source K sourceFiberNontrivial
  | cons x xs ih =>
      let old := ih
      letI : Fintype old.Point := old.pointFintype
      letI : Fintype old.Coord := old.coordFintype
      letI : Nontrivial (Fiber old.target x) :=
        old.targetFiberNontrivial x
      let lines := family old.target x
      exact FocusedExtension.cons old
        (oneFiberAmalgamate old.target old.targetFiberNontrivial x lines)

/-- Focusing every base vertex transfers the base Ramsey property to the
final picture. -/
theorem focusedExtension_ramsey [Fintype V]
    {source : Picture G P C} (hrealizes : RealizesEveryEdge source)
    {vertices : List V} (hall : ∀ x : V, x ∈ vertices)
    {K : Type uK} (hG : ThreeGraph.RamseyFor G K)
    (result : FocusedExtension source vertices K) :
    PictureRamseyFor result.target K := by
  intro color
  obtain ⟨copy, hcopy, hfocused⟩ := result.focused color
  have hfiber : ∀ x : V, ∃ k : K, ∀ p,
      source.proj p = x → color (copy p) = k := by
    intro x
    exact hfocused x (hall x)
  let vertexColor : V → K := fun x => Classical.choose (hfiber x)
  obtain ⟨e, k, he⟩ := hG vertexColor
  obtain ⟨l, hline, hproj⟩ := hrealizes e
  refine ⟨fun a => copy (l a), hcopy.transports_lines l hline, k, ?_⟩
  intro a
  have hmem : source.proj (l a) ∈ e.1 := by
    change source.proj (l a) ∈ (e.1 : Set V)
    rw [← hproj]
    exact ⟨a, rfl⟩
  have hpoint := Classical.choose_spec (hfiber (source.proj (l a)))
  calc
    color (copy (l a)) = vertexColor (source.proj (l a)) :=
      hpoint (l a) rfl
    _ = k := he _ hmem

/-- The finite backward-focusing construction, packaged as an existential
final picture. -/
theorem exists_ramsey_final_picture [Fintype V]
    [Fintype P] [Fintype C]
    (source : Picture G P C) (K : Type uK)
    (sourceFiberNontrivial : ∀ x : V, Nontrivial (Fiber source x))
    (hrealizes : RealizesEveryEdge source)
    (hG : ThreeGraph.RamseyFor G K)
    (family : ∀ {P' : Type uP} {C' : Type uC}
      [Fintype P'] [Fintype C']
      (picture : Picture G P' C') (x : V)
      [Nontrivial (Fiber picture x)],
        SparseFiberLineFamily picture x K)
    (oneFiberAmalgamate : ∀ {P' : Type uP} {C' : Type uC}
      [Fintype P'] [Fintype C']
      (picture : Picture G P' C')
      (sourceFibers : ∀ y : V, Nontrivial (Fiber picture y))
      (x : V)
      [Nontrivial (Fiber picture x)]
      (_lines : SparseFiberLineFamily picture x K),
        FiberExtension picture x K) :
    ∃ (Q : Type uP) (D : Type uC)
      (_ : Fintype Q) (_ : Fintype D) (final : Picture G Q D),
      (∀ x : V, Nontrivial (Fiber final x)) ∧
        PictureRamseyFor final K := by
  let vertices := (Finset.univ : Finset V).toList
  let result := iterate source K vertices sourceFiberNontrivial
    family oneFiberAmalgamate
  refine ⟨result.Point, result.Coord, result.pointFintype,
    result.coordFintype, result.target, result.targetFiberNontrivial, ?_⟩
  apply focusedExtension_ramsey hrealizes (hG := hG) (result := result)
  intro x
  simp [vertices]

end Iteration

/-! ## Picture zero realizes every base edge -/

section PictureZero

theorem pictureZero_realizesEveryEdge (G : ThreeGraph V) :
    RealizesEveryEdge (pictureZero G) := by
  intro e
  let l : Alphabet → ZeroPoint G := fun a => (e, a)
  have hline : IsCombinatorialLine (zeroWord G) l := by
    refine ⟨?_, Equiv.refl Alphabet, ?_⟩
    · intro a b hab
      exact congrArg Prod.snd hab
    · intro c
      cases c with
      | inl e' =>
          by_cases he : e' = e
          · right
            intro a
            subst e'
            simp [l, zeroWord]
          · left
            refine ⟨1, ?_⟩
            intro a
            simp [l, zeroWord, he]
      | inr e' =>
          by_cases he : e' = e
          · left
            refine ⟨2, ?_⟩
            intro a
            subst e'
            simp [l, zeroWord]
          · left
            refine ⟨1, ?_⟩
            intro a
            simp [l, zeroWord, he]
  refine ⟨l, hline, Set.ext ?_⟩
  intro v
  constructor
  · rintro ⟨a, rfl⟩
    exact ThreeGraph.edgeEquiv_mem G e a
  · intro hv
    let ev : {v : V // v ∈ e.1} := ⟨v, hv⟩
    obtain ⟨a, ha⟩ := (G.edgeEquiv e).surjective ev
    refine ⟨a, ?_⟩
    exact congrArg Subtype.val ha

end PictureZero

/-! ## Weighted independent sets pull back along the projection -/

section FractionalPullback

variable {P : Type uP} {C : Type uC}

end FractionalPullback

end Erdos847Iteration

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/ConfinementKernels.lean` -/

section
namespace Erdos847ConfinementKernels

open Function Set

set_option autoImplicit false

abbrev Alphabet := Fin 3

/-! ## Elementary classifications of ternary rows -/

/-!
`Admissible fiber c row` is the normalized form of (4.2): in position `i`,
the section is either on the music fiber or is its distinguished source
representative `c i`.
-/
def Admissible {P : Type*} (fiber : P → Prop) (c row : Alphabet → P) : Prop :=
  ∀ i, fiber (row i) ∨ row i = c i

/-- The same-range/different-order normal form in the ternary case. -/
theorem same_range_normal_forms {P : Type*} {fiber : P → Prop}
    {c row : Alphabet → P} {a : P}
    (hc0 : ¬ fiber (c 0)) (hc1 : ¬ fiber (c 1))
    (hrow : Injective row)
    (hadm : Admissible fiber c row)
    (hrange : Set.range row = {c 0, c 1, a})
    (hne : row 0 ≠ c 0 ∨ row 1 ≠ c 1 ∨ row 2 ≠ a) :
    (row 0 = a ∧ row 1 = c 1 ∧ row 2 = c 0 ∧ c 2 = c 0) ∨
      (row 0 = c 0 ∧ row 1 = a ∧ row 2 = c 1 ∧ c 2 = c 1) := by
  have hmem (i : Alphabet) : row i = c 0 ∨ row i = c 1 ∨ row i = a := by
    have : row i ∈ ({c 0, c 1, a} : Set P) := by
      rw [← hrange]
      exact Set.mem_range_self i
    simpa [eq_comm] using this
  have hr0 : row 0 = c 0 ∨ row 0 = a := by
    rcases hadm 0 with hf | hc
    · rcases hmem 0 with h | h | h
      · exact Or.inl h
      · exact False.elim (hc1 (h ▸ hf))
      · exact Or.inr h
    · exact Or.inl hc
  have hr1 : row 1 = c 1 ∨ row 1 = a := by
    rcases hadm 1 with hf | hc
    · rcases hmem 1 with h | h | h
      · exact False.elim (hc0 (h ▸ hf))
      · exact Or.inl h
      · exact Or.inr h
    · exact Or.inl hc
  rcases hr0 with hr0 | hr0 <;> rcases hr1 with hr1 | hr1
  · exfalso
    have hr2 : row 2 = a := by
      rcases hmem 2 with h | h | h
      · exact False.elim (by
          apply (by decide : (2 : Alphabet) ≠ 0)
          apply hrow
          exact h.trans hr0.symm)
      · exact False.elim (by
          apply (by decide : (2 : Alphabet) ≠ 1)
          apply hrow
          exact h.trans hr1.symm)
      · exact h
    rcases hne with hne | hne | hne
    · exact hne hr0
    · exact hne hr1
    · exact hne hr2
  · right
    have hr2 : row 2 = c 1 := by
      rcases hmem 2 with h | h | h
      · exact False.elim (by
          apply (by decide : (2 : Alphabet) ≠ 0)
          apply hrow
          exact h.trans hr0.symm)
      · exact h
      · exact False.elim (by
          apply (by decide : (2 : Alphabet) ≠ 1)
          apply hrow
          exact h.trans hr1.symm)
    refine ⟨hr0, hr1, hr2, ?_⟩
    rcases hadm 2 with hf | hc
    · exact False.elim (hc1 (hr2 ▸ hf))
    · exact hc.symm.trans hr2
  · left
    have hr2 : row 2 = c 0 := by
      rcases hmem 2 with h | h | h
      · exact h
      · exact False.elim (by
          apply (by decide : (2 : Alphabet) ≠ 1)
          apply hrow
          exact h.trans hr1.symm)
      · exact False.elim (by
          apply (by decide : (2 : Alphabet) ≠ 0)
          apply hrow
          exact h.trans hr0.symm)
    refine ⟨hr0, hr1, hr2, ?_⟩
    rcases hadm 2 with hf | hc
    · exact False.elim (hc0 (hr2 ▸ hf))
    · exact hc.symm.trans hr2
  · exact False.elim <| (by decide : (0 : Alphabet) ≠ 1) <| hrow <|
      hr0.trans hr1.symm

/--
Two distinct ternary source-line ranges, each having at most one fiber
point, have the two normal forms from the second case of Proposition 4.5.
The `Subsingleton` hypothesis is the usual fact that two distinct
combinatorial lines meet in at most one point.
-/
theorem distinct_range_normal_forms {P : Type*} {fiber : P → Prop}
    {c row : Alphabet → P} {a : P}
    (hc01 : c 0 ≠ c 1)
    (hc0 : ¬ fiber (c 0)) (hc1 : ¬ fiber (c 1))
    (hadm : Admissible fiber c row)
    (hfiber : ∀ i j, fiber (row i) → fiber (row j) → i = j)
    (hinter : (Set.range row ∩ ({c 0, c 1, a} : Set P)).Subsingleton) :
    (∃ b, fiber b ∧ b ≠ a ∧
      row 0 = c 0 ∧ row 1 = b ∧ row 2 = c 2) ∨
      (∃ b, fiber b ∧ b ≠ a ∧
        row 0 = b ∧ row 1 = c 1 ∧ row 2 = c 2) := by
  have shared_eq {u v : P}
      (hurow : u ∈ Set.range row) (hubase : u ∈ ({c 0, c 1, a} : Set P))
      (hvrow : v ∈ Set.range row) (hvbase : v ∈ ({c 0, c 1, a} : Set P)) :
      u = v := hinter ⟨hurow, hubase⟩ ⟨hvrow, hvbase⟩
  rcases hadm 0 with h0f | h0c <;>
    rcases hadm 1 with h1f | h1c <;>
    rcases hadm 2 with h2f | h2c
  · exact False.elim <| (by decide : (0 : Alphabet) ≠ 1) <| hfiber 0 1 h0f h1f
  · exact False.elim <| (by decide : (0 : Alphabet) ≠ 1) <| hfiber 0 1 h0f h1f
  · exact False.elim <| (by decide : (0 : Alphabet) ≠ 2) <| hfiber 0 2 h0f h2f
  · right
    refine ⟨row 0, h0f, ?_, rfl, h1c, h2c⟩
    intro h0a
    have hca : c 1 = a := shared_eq
      ⟨1, h1c⟩ (by simp)
      ⟨0, h0a⟩ (by simp)
    exact hc1 (hca ▸ by simpa [h0a] using h0f)
  · exact False.elim <| (by decide : (1 : Alphabet) ≠ 2) <| hfiber 1 2 h1f h2f
  · left
    refine ⟨row 1, h1f, ?_, h0c, rfl, h2c⟩
    intro h1a
    have hca : c 0 = a := shared_eq
      ⟨0, h0c⟩ (by simp)
      ⟨1, h1a⟩ (by simp)
    exact hc0 (hca ▸ by simpa [h1a] using h1f)
  · exfalso
    have hEq : c 0 = c 1 := shared_eq
      ⟨0, h0c⟩ (by simp)
      ⟨1, h1c⟩ (by simp)
    exact hc01 hEq
  · exfalso
    have hEq : c 0 = c 1 := shared_eq
      ⟨0, h0c⟩ (by simp)
      ⟨1, h1c⟩ (by simp)
    exact hc01 hEq

/--
With three normalized outside representatives and at most one fiber entry,
there are only the three `2 + 1` masks or the all-moving mask.  Applied after
the first two distinct ranges have been named, the third disjunct is exactly
the potential `{d,c₁,c₂}` line; the last disjunct meets either named line in
two outside points and is therefore excluded by line uniqueness.
-/
theorem normalized_row_four_forms {P : Type*} {fiber : P → Prop}
    {c row : Alphabet → P}
    (hadm : Admissible fiber c row)
    (hfiber : ∀ i j, fiber (row i) → fiber (row j) → i = j) :
    (fiber (row 0) ∧ row 1 = c 1 ∧ row 2 = c 2) ∨
      (row 0 = c 0 ∧ fiber (row 1) ∧ row 2 = c 2) ∨
      (row 0 = c 0 ∧ row 1 = c 1 ∧ fiber (row 2)) ∨
      (row 0 = c 0 ∧ row 1 = c 1 ∧ row 2 = c 2) := by
  rcases hadm 0 with h0f | h0c <;>
    rcases hadm 1 with h1f | h1c <;>
    rcases hadm 2 with h2f | h2c
  · exact False.elim <| (by decide : (0 : Alphabet) ≠ 1) <| hfiber 0 1 h0f h1f
  · exact False.elim <| (by decide : (0 : Alphabet) ≠ 1) <| hfiber 0 1 h0f h1f
  · exact False.elim <| (by decide : (0 : Alphabet) ≠ 2) <| hfiber 0 2 h0f h2f
  · exact Or.inl ⟨h0f, h1c, h2c⟩
  · exact False.elim <| (by decide : (1 : Alphabet) ≠ 2) <| hfiber 1 2 h1f h2f
  · exact Or.inr <| Or.inl ⟨h0c, h1f, h2c⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨h0c, h1c, h2f⟩
  · exact Or.inr <| Or.inr <| Or.inr ⟨h0c, h1c, h2c⟩

/-! ## Moving-mask kernels -/

end Erdos847ConfinementKernels

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/FiniteArch.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
Scratch architecture for the finite core of Erdős 847.

The point of this file is not to duplicate the RRS construction.  It records two reductions that
make the target specialization substantially smaller:

* hypergraphs are finite families of finite vertex sets;
* the `1/3` fractional property is expressed using natural-valued multiplicities.  This is exactly
  what is needed for pullback along the picture projection, and avoids normalized real weights.
-/

namespace Erdos847FiniteArch

open scoped BigOperators
open Function Set
open Erdos847Pictures

/-! A quasiline is best represented parametrically.  This avoids quotienting by the six possible
labellings of a three-element `Finset`, while remaining exactly the unordered notion after taking
the range. -/

lemma line_injective {A I : Type*} [Nontrivial A]
    (L : Combinatorics.Line A I) : Function.Injective L := by
  intro a b hab
  obtain ⟨i, hi⟩ := L.proper
  have := congrFun hab i
  simpa [Combinatorics.Line.coe_apply, hi] using this

abbrev FinHypergraph (V : Type*) [DecidableEq V] := Finset (Finset V)

def Independent {V : Type*} [DecidableEq V] (H : FinHypergraph V) (I : Finset V) : Prop :=
  ∀ e ∈ H, ¬ e ⊆ I

/-- The cleared-denominator `1/3` fractional property, only for natural multiplicities. -/
def NatFractionalThird {V : Type*} [Fintype V] [DecidableEq V]
    (H : FinHypergraph V) : Prop :=
  ∀ w : V → ℕ, ∃ I : Finset V, Independent H I ∧
    (∑ x, w x) ≤ 3 * ∑ x ∈ I, w x

/-- A map which sends every source edge onto a target edge. -/
def MapsEdges {U V : Type*} [DecidableEq U] [DecidableEq V]
    (f : U → V) (G : FinHypergraph U) (H : FinHypergraph V) : Prop :=
  ∀ e ∈ G, e.image f ∈ H

lemma independent_preimage {U V : Type*} [Fintype U] [DecidableEq U] [DecidableEq V]
    {f : U → V} {G : FinHypergraph U} {H : FinHypergraph V}
    (hf : MapsEdges f G H) {J : Finset V} (hJ : Independent H J) :
    Independent G (Finset.univ.filter fun x ↦ f x ∈ J) := by
  intro e he heI
  apply hJ (e.image f) (hf e he)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact (Finset.mem_filter.mp (heI hx)).2

/-- Natural multiplicities are stable under the many-to-one projection used by pictures. -/
lemma NatFractionalThird.pullback {U V : Type*}
    [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    {f : U → V} {G : FinHypergraph U} {H : FinHypergraph V}
    (hH : NatFractionalThird H) (hf : MapsEdges f G H) :
    NatFractionalThird G := by
  intro w
  let W : V → ℕ := fun y ↦ ∑ x with f x = y, w x
  obtain ⟨J, hJ, hweight⟩ := hH W
  let I : Finset U := Finset.univ.filter fun x ↦ f x ∈ J
  refine ⟨I, independent_preimage hf hJ, ?_⟩
  have htotal : (∑ y, W y) = ∑ x, w x := by
    simp only [W]
    simpa using Finset.sum_fiberwise (Finset.univ : Finset U) f w
  have hselected : (∑ y ∈ J, W y) = ∑ x ∈ I, w x := by
    simp only [W, I]
    simpa using Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset U) J f w
  rw [← htotal, ← hselected]
  exact hweight

/-! ## Two finite incidence kernels for confinement

After one nonconstant section has been normalized, the ambient confinement proof only needs to
read the three outer line descriptions coordinate by coordinate.  The following two lemmas package
that bookkeeping.  They are deliberately stated for an arbitrary alphabet and coordinate type.
-/

section OuterIncidenceKernels

variable {A I : Type*}

/-- A line is determined by its `idxFun`. -/
lemma line_eq_of_idxFun_eq {U W : Combinatorics.Line A I}
    (h : U.idxFun = W.idxFun) : U = W := by
  cases U
  cases W
  simp_all only [Combinatorics.Line.mk.injEq]

/-- If all coordinates have the `110`, `010`-constant, or `011` pattern displayed below, then
the three lines are concurrent and their moving supports form the exact RRS tripod relation.
The witnesses `sS` and `sT` say that both nonconstant section types really occur, so the three
outer lines are distinct. -/
lemma isRawTripod_of_section_table
    (U W Z : Combinatorics.Line A I) (a : A) (sS sT : I)
    (htable : ∀ s,
      (∃ c, U.idxFun s = some c ∧ W.idxFun s = some c ∧ Z.idxFun s = some c) ∨
      (U.idxFun s = none ∧ W.idxFun s = none ∧ Z.idxFun s = some a) ∨
      (U.idxFun s = some a ∧ W.idxFun s = none ∧ Z.idxFun s = none))
    (hS : U.idxFun sS = none ∧ W.idxFun sS = none ∧ Z.idxFun sS = some a)
    (hT : U.idxFun sT = some a ∧ W.idxFun sT = none ∧ Z.idxFun sT = none) :
    IsRawTripod U W Z := by
  have hUW : U ≠ W := by
    intro h
    have := congrArg (fun L : Combinatorics.Line A I ↦ L.idxFun sT) h
    simp [hT.1, hT.2.1] at this
  have hUZ : U ≠ Z := by
    intro h
    have := congrArg (fun L : Combinatorics.Line A I ↦ L.idxFun sS) h
    simp [hS.1, hS.2.2] at this
  have hWZ : W ≠ Z := by
    intro h
    have := congrArg (fun L : Combinatorics.Line A I ↦ L.idxFun sS) h
    simp [hS.2.1, hS.2.2] at this
  have hcommon : RawLinesCommonPoint U W Z := by
    refine ⟨a, a, a, ?_, ?_⟩
    · funext s
      rcases htable s with ⟨c, hUc, hWc, hZc⟩ | hS' | hT'
      · simp [Combinatorics.Line.coe_apply, hUc, hWc]
      · simp [Combinatorics.Line.coe_apply, hS'.1, hS'.2.1]
      · simp [Combinatorics.Line.coe_apply, hT'.1, hT'.2.1]
    · funext s
      rcases htable s with ⟨c, hUc, hWc, hZc⟩ | hS' | hT'
      · simp [Combinatorics.Line.coe_apply, hWc, hZc]
      · simp [Combinatorics.Line.coe_apply, hS'.2.1, hS'.2.2]
      · simp [Combinatorics.Line.coe_apply, hT'.2.1, hT'.2.2]
  refine ⟨hUW, hUZ, hWZ, hcommon, Or.inr (Or.inl ?_)⟩
  constructor
  · ext s
    rcases htable s with ⟨c, hUc, hWc, hZc⟩ | hS' | hT'
    · simp [RawMovingSet, hUc, hWc, hZc]
    · simp [RawMovingSet, hS'.1, hS'.2.1, hS'.2.2]
    · simp [RawMovingSet, hT'.1, hT'.2.1, hT'.2.2]
  · rw [Set.disjoint_left]
    intro s hsU hsZ
    rcases htable s with ⟨c, hUc, hWc, hZc⟩ | hS' | hT'
    · simp [RawMovingSet, hUc] at hsU
    · simp [RawMovingSet, hS'.2.2] at hsZ
    · simp [RawMovingSet, hT'.1] at hsU

/-- The complementary status table has three pairwise intersections and no common point.  This is
the precise outer-line triangle created by two different source section-lines once a third section
type has been ruled out by linearity of the base hypergraph. -/
lemma isRawTriangle_of_section_table
    (U W Z : Combinatorics.Line A I) (a b : A) (sS sT : I) (hab : a ≠ b)
    (htable : ∀ s,
      (∃ c, U.idxFun s = some c ∧ W.idxFun s = some c ∧ Z.idxFun s = some c) ∨
      (U.idxFun s = none ∧ W.idxFun s = none ∧ Z.idxFun s = some a) ∨
      (U.idxFun s = none ∧ W.idxFun s = some b ∧ Z.idxFun s = none))
    (hS : U.idxFun sS = none ∧ W.idxFun sS = none ∧ Z.idxFun sS = some a)
    (hT : U.idxFun sT = none ∧ W.idxFun sT = some b ∧ Z.idxFun sT = none) :
    IsRawTriangle U W Z := by
  have hUW : U ≠ W := by
    intro h
    have := congrArg (fun L : Combinatorics.Line A I ↦ L.idxFun sT) h
    simp [hT.1, hT.2.1] at this
  have hUZ : U ≠ Z := by
    intro h
    have := congrArg (fun L : Combinatorics.Line A I ↦ L.idxFun sS) h
    simp [hS.1, hS.2.2] at this
  have hWZ : W ≠ Z := by
    intro h
    have := congrArg (fun L : Combinatorics.Line A I ↦ L.idxFun sS) h
    simp [hS.2.1, hS.2.2] at this
  have hUbW : U b = W b := by
    funext s
    rcases htable s with ⟨c, hUc, hWc, hZc⟩ | hS' | hT'
    · simp [Combinatorics.Line.coe_apply, hUc, hWc]
    · simp [Combinatorics.Line.coe_apply, hS'.1, hS'.2.1]
    · simp [Combinatorics.Line.coe_apply, hT'.1, hT'.2.1]
  have hUaZ : U a = Z a := by
    funext s
    rcases htable s with ⟨c, hUc, hWc, hZc⟩ | hS' | hT'
    · simp [Combinatorics.Line.coe_apply, hUc, hZc]
    · simp [Combinatorics.Line.coe_apply, hS'.1, hS'.2.2]
    · simp [Combinatorics.Line.coe_apply, hT'.1, hT'.2.2]
  have hWaZb : W a = Z b := by
    funext s
    rcases htable s with ⟨c, hUc, hWc, hZc⟩ | hS' | hT'
    · simp [Combinatorics.Line.coe_apply, hWc, hZc]
    · simp [Combinatorics.Line.coe_apply, hS'.2.1, hS'.2.2]
    · simp [Combinatorics.Line.coe_apply, hT'.2.1, hT'.2.2]
  refine ⟨hUW, hUZ, hWZ, ⟨b, b, hUbW⟩, ⟨a, a, hUaZ⟩,
    ⟨a, b, hWaZb⟩, ?_⟩
  rintro ⟨i, j, k, hij, hjk⟩
  have hSij := congrFun hij sS
  have hSjk := congrFun hjk sS
  have hTij := congrFun hij sT
  simp [Combinatorics.Line.coe_apply, hS.1, hS.2.1, hS.2.2,
    hT.1, hT.2.1, hT.2.2] at hSij hSjk hTij
  apply hab
  exact hSjk.symm.trans (hSij.symm.trans hTij)

end OuterIncidenceKernels

/-! ## The all-outside branch of normalized confinement -/

section NormalizedConfinement

variable {V P C N : Type*} [DecidableEq V]
variable {G : ThreeGraph V}

end NormalizedConfinement

end Erdos847FiniteArch

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/Confinement.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

namespace Erdos847Confinement

open Function Set
open Erdos847Pictures Erdos847FiniteArch

set_option autoImplicit false

variable {V P C N : Type*} [DecidableEq V]
variable {G : ThreeGraph V}

section NormalizedSections

variable (source : Picture G P C) (x : V)
variable (lines : Set (Combinatorics.Line (MusicFiber source x) N))
variable {l : Alphabet → RawAmalgamPoint source x lines}

abbrev normalizedSection (R : NormalizedRawQuasiline source x lines l)
    (s : N) (i : Alphabet) : P :=
  sectionPoint source x (R.line i) (R.point i) s

/-- A constant outer section in normalized form is necessarily on the music
line. -/
theorem constant_section_mem_fiber
    (R : NormalizedRawQuasiline source x lines l)
    (s : N) (q : P) (hq : ∀ i, normalizedSection source x lines R s i = q) :
    source.proj q = x := by
  by_contra hqout
  have hq0 : q = R.point 0 := by
    rcases sectionPoint_mem_fiber_or_eq source x (R.line 0) (R.point 0) s with h | h
    · exact False.elim (hqout ((hq 0).symm ▸ h))
    · exact (hq 0).symm.trans h
  have hq1 : q = R.point 1 := by
    rcases sectionPoint_mem_fiber_or_eq source x (R.line 1) (R.point 1) s with h | h
    · exact False.elim (hqout ((hq 1).symm ▸ h))
    · exact (hq 1).symm.trans h
  have hbad : normalizedSection source x lines R R.coordinate 0 =
      normalizedSection source x lines R R.coordinate 1 := by
    change sectionPoint source x (R.line 0) (R.point 0) R.coordinate =
      sectionPoint source x (R.line 1) (R.point 1) R.coordinate
    rw [R.section_zero, R.section_one, ← hq0, ← hq1]
  exact Fin.zero_ne_one (R.source_section.1 hbad)

/-- Every section in normalized form is constant on the music line or is a
source quasiline. -/
theorem normalized_section_dichotomy
    (R : NormalizedRawQuasiline source x lines l) (s : N) :
    (∃ q, source.proj q = x ∧ ∀ i,
      normalizedSection source x lines R s i = q) ∨
      IsQuasiline source.embed (normalizedSection source x lines R s) := by
  rcases raw_quasiline_section source x lines (fun i => l (R.perm i))
      R.line R.point R.word_eq R.outer_quasiline s with hconst | hline
  · obtain ⟨q, hq⟩ := hconst
    exact Or.inl ⟨q, constant_section_mem_fiber source x lines R s q hq, hq⟩
  · exact Or.inr hline

/-- At most one entry of a nonconstant source section lies on the music
line. -/
theorem source_section_atMostOne_fiber
    (R : NormalizedRawQuasiline source x lines l) (s : N)
    (hs : IsQuasiline source.embed (normalizedSection source x lines R s))
    {i j : Alphabet}
    (hi : source.proj (normalizedSection source x lines R s i) = x)
    (hj : source.proj (normalizedSection source x lines R s j) = x) : i = j := by
  exact mapsOntoEdge_proj_injective source
    (source.quasiline_maps_edge _ hs) (hi.trans hj.symm)

/-- If all three normalized representative points are off the music line,
the status of a constant section is three copies of the same fixed letter. -/
theorem constant_section_status
    (R : NormalizedRawQuasiline source x lines l)
    (hp : ∀ i, source.proj (R.point i) ≠ x)
    (s : N) (q : P) (hq : source.proj q = x)
    (hsec : ∀ i, normalizedSection source x lines R s i = q) :
    ∃ a : MusicFiber source x,
      (R.line 0).idxFun s = some a ∧
      (R.line 1).idxFun s = some a ∧
      (R.line 2).idxFun s = some a := by
  let a : MusicFiber source x := ⟨q, hq⟩
  have fixed (i : Alphabet) : (R.line i).idxFun s = some a := by
    obtain ⟨f, hf, hval⟩ := fixed_value_of_sectionPoint_eq source x
      (R.line i) (R.point i) q (hp i) hq s (hsec i)
    have hfa : f = a := Subtype.ext hval
    simpa [hfa] using hf
  exact ⟨a, fixed 0, fixed 1, fixed 2⟩

/-- The section-point formula is precisely the admissibility condition used
by the finite ternary classifiers. -/
theorem section_admissible
    (R : NormalizedRawQuasiline source x lines l) (s : N) :
    Erdos847ConfinementKernels.Admissible (fun q => source.proj q = x)
      R.point (normalizedSection source x lines R s) := by
  intro i
  exact sectionPoint_mem_fiber_or_eq source x (R.line i) (R.point i) s

/--
If the third entry of the normalized base section is also outside the music
fiber, then every nonconstant section has the same ordered row as the base
section.  Consequently all three selected outer lines agree.
-/
theorem outside_third_lines_equal
    (R : NormalizedRawQuasiline source x lines l)
    (hthird : source.proj
      (normalizedSection source x lines R R.coordinate 2) ≠ x) :
    R.line 0 = R.line 1 ∧ R.line 0 = R.line 2 := by
  classical
  let base : Alphabet → P := normalizedSection source x lines R R.coordinate
  have hb0 : base 0 = R.point 0 := R.section_zero
  have hb1 : base 1 = R.point 1 := R.section_one
  have hb2 : base 2 = R.point 2 := by
    apply (sectionPoint_mem_fiber_or_eq source x (R.line 2) (R.point 2)
      R.coordinate).resolve_left
    exact hthird
  have hp : ∀ i, source.proj (R.point i) ≠ x := by
    intro i
    fin_cases i
    · exact R.point_zero_not_fiber
    · exact R.point_one_not_fiber
    · simpa [base, hb2] using hthird
  have hbaseLine : IsCombinatorialLine source.embed base :=
    source.quasiline_is_line base R.source_section
  have each_nonconstant_eq (s : N)
      (hs : IsQuasiline source.embed (normalizedSection source x lines R s)) :
      normalizedSection source x lines R s = base := by
    let row : Alphabet → P := normalizedSection source x lines R s
    have hrowMaps := source.quasiline_maps_edge row hs
    have hrowAtMost : ∀ i j,
        source.proj (row i) = x → source.proj (row j) = x → i = j := by
      intro i j hi hj
      exact mapsOntoEdge_proj_injective source hrowMaps (hi.trans hj.symm)
    have hforms := Erdos847ConfinementKernels.normalized_row_four_forms
      (section_admissible source x lines R s) hrowAtMost
    have hrange : Set.range row = Set.range base := by
      have hrowLine : IsCombinatorialLine source.embed row :=
        source.quasiline_is_line row hs
      rcases hforms with h0 | h1 | h2 | h3
      · exact (combinatorialLine_range_eq_of_two_points source.embed
          source.embed_injective row base hrowLine hbaseLine
          (by decide : (1 : Alphabet) ≠ 2)
          (h0.2.1.trans hb1.symm) (h0.2.2.trans hb2.symm))
      · exact (combinatorialLine_range_eq_of_two_points source.embed
          source.embed_injective row base hrowLine hbaseLine
          (by decide : (0 : Alphabet) ≠ 2)
          (h1.1.trans hb0.symm) (h1.2.2.trans hb2.symm))
      · exact (combinatorialLine_range_eq_of_two_points source.embed
          source.embed_injective row base hrowLine hbaseLine
          (by decide : (0 : Alphabet) ≠ 1)
          (h2.1.trans hb0.symm) (h2.2.1.trans hb1.symm))
      · exact (combinatorialLine_range_eq_of_two_points source.embed
          source.embed_injective row base hrowLine hbaseLine
          (by decide : (0 : Alphabet) ≠ 1)
          (h3.1.trans hb0.symm) (h3.2.1.trans hb1.symm))
    by_contra hne
    have hcoords : row 0 ≠ R.point 0 ∨ row 1 ≠ R.point 1 ∨
        row 2 ≠ base 2 := by
      by_contra hall
      push Not at hall
      apply hne
      funext i
      fin_cases i
      · exact hall.1.trans hb0.symm
      · exact hall.2.1.trans hb1.symm
      · exact hall.2.2
    have hnormal := Erdos847ConfinementKernels.same_range_normal_forms
      R.point_zero_not_fiber R.point_one_not_fiber hs.1
      (section_admissible source x lines R s)
      (by simpa [hb0, hb1, Erdos847Pictures.range_fin3] using hrange)
      hcoords
    rcases hnormal with hswap0 | hswap1
    · have hp20 : R.point 2 = R.point 0 := hswap0.2.2.2
      have hb20 : base 2 = base 0 := hb2.trans (hp20.trans hb0.symm)
      exact (by decide : (2 : Alphabet) ≠ 0) (R.source_section.1 hb20)
    · have hp21 : R.point 2 = R.point 1 := hswap1.2.2.2
      have hb21 : base 2 = base 1 := hb2.trans (hp21.trans hb1.symm)
      exact (by decide : (2 : Alphabet) ≠ 1) (R.source_section.1 hb21)
  have hidx (i j : Alphabet) : (R.line i).idxFun = (R.line j).idxFun := by
    funext s
    rcases normalized_section_dichotomy source x lines R s with hconst | hline
    · obtain ⟨q, hq, hsec⟩ := hconst
      obtain ⟨a, h0, h1, h2⟩ := constant_section_status source x lines R hp s q hq hsec
      fin_cases i <;> fin_cases j <;> simp_all
    · have hrow := congrFun (each_nonconstant_eq s hline)
      have hmove (k : Alphabet) : (R.line k).idxFun s = none :=
        (moving_iff_sectionPoint_eq source x (R.line k) (R.point k) (hp k) s).2 <| by
          have := hrow k
          fin_cases k <;> simp_all [base]
      rw [hmove i, hmove j]
  constructor
  · exact Erdos847FiniteArch.line_eq_of_idxFun_eq (hidx 0 1)
  · exact Erdos847FiniteArch.line_eq_of_idxFun_eq (hidx 0 2)

def NormalizedConfined
    (R : NormalizedRawQuasiline source x lines l) : Prop :=
  ∃ (U : Combinatorics.Line (MusicFiber source x) N) (hU : U ∈ lines)
      (p : Alphabet → P),
    IsQuasiline source.embed p ∧
      ∀ i, l (R.perm i) = standardCopy source x lines U hU (p i)

theorem isQuasiline_reindex {D Q : Type*}
    (embed : Q → D → Alphabet) (q : Alphabet → Q)
    (hq : IsQuasiline embed q) (σ : Equiv.Perm Alphabet) :
    IsQuasiline embed (fun i => q (σ i)) := by
  constructor
  · intro i j hij
    exact σ.injective (hq.1 hij)
  · intro d
    rcases hq.2 d with ⟨a, ha⟩ | hm
    · exact Or.inl ⟨a, fun i => ha (σ i)⟩
    · exact Or.inr (hm.comp σ.injective)

/-- If every nonconstant section has the normalized base ordering, the raw
quasiline lies in the standard copy indexed by `R.line 0`. -/
theorem confined_of_all_nonconstant_base
    (R : NormalizedRawQuasiline source x lines l)
    (hall : ∀ s, IsQuasiline source.embed
      (normalizedSection source x lines R s) →
      normalizedSection source x lines R s =
        normalizedSection source x lines R R.coordinate) :
    NormalizedConfined source x lines R := by
  let base := normalizedSection source x lines R R.coordinate
  refine ⟨R.line 0, R.line_mem 0, base, R.source_section, ?_⟩
  intro i
  apply Subtype.ext
  rw [R.word_eq i]
  funext sc
  simp only [extendWord]
  congr 1
  rcases normalized_section_dichotomy source x lines R sc.1 with hconst | hline
  · obtain ⟨q, hq, hsec⟩ := hconst
    obtain ⟨f, hf, hval⟩ := fixed_value_of_sectionPoint_eq source x
      (R.line 0) (R.point 0) q R.point_zero_not_fiber hq sc.1 (hsec 0)
    rw [show sectionPoint source x (R.line i) (R.point i) sc.1 = q from hsec i]
    simp [sectionPoint, hf, hval]
  · have hrow := hall sc.1 hline
    have hmove : (R.line 0).idxFun sc.1 = none :=
      (moving_iff_sectionPoint_eq source x (R.line 0) (R.point 0)
        R.point_zero_not_fiber sc.1).2 <| by
          have hh := congrFun hrow 0
          change sectionPoint source x (R.line 0) (R.point 0) sc.1 =
            sectionPoint source x (R.line 0) (R.point 0) R.coordinate at hh
          exact hh.trans R.section_zero
    have hh := congrFun hrow i
    change sectionPoint source x (R.line i) (R.point i) sc.1 = base i at hh
    rw [hh]
    simp [sectionPoint, hmove]

/-- Same-range part of Proposition 4.5.  Either all rows have the base
ordering and confinement is immediate, or the exact RRS tripod occurs. -/
theorem same_range_fiber_confined_or_tripod
    (R : NormalizedRawQuasiline source x lines l)
    (hfiber : source.proj
      (normalizedSection source x lines R R.coordinate 2) = x)
    (hallRange : ∀ s,
      IsQuasiline source.embed (normalizedSection source x lines R s) →
      Set.range (normalizedSection source x lines R s) =
        Set.range (normalizedSection source x lines R R.coordinate)) :
    NormalizedConfined source x lines R ∨
      ∃ U W Z, U ∈ lines ∧ W ∈ lines ∧ Z ∈ lines ∧ IsRawTripod U W Z := by
  classical
  let base := normalizedSection source x lines R R.coordinate
  by_cases hdiff : ∃ s, IsQuasiline source.embed
      (normalizedSection source x lines R s) ∧
      normalizedSection source x lines R s ≠ base
  · obtain ⟨t, htline, htdiff⟩ := hdiff
    let row := normalizedSection source x lines R t
    have hb0 : base 0 = R.point 0 := R.section_zero
    have hb1 : base 1 = R.point 1 := R.section_one
    have hbaseRange : Set.range base =
        ({R.point 0, R.point 1, base 2} : Set P) := by
      rw [range_fin3, hb0, hb1]
    have htcoords : row 0 ≠ R.point 0 ∨ row 1 ≠ R.point 1 ∨ row 2 ≠ base 2 := by
      by_contra h
      push Not at h
      apply htdiff
      funext i
      fin_cases i
      · exact h.1.trans hb0.symm
      · exact h.2.1.trans hb1.symm
      · exact h.2.2
    have htNormal := Erdos847ConfinementKernels.same_range_normal_forms
      R.point_zero_not_fiber R.point_one_not_fiber htline.1
      (section_admissible source x lines R t)
      (by rw [hallRange t htline, hbaseRange]) htcoords
    rcases htNormal with hA | hB
    · have hp2 : source.proj (R.point 2) ≠ x := by
        rw [hA.2.2.2]
        exact R.point_zero_not_fiber
      have hpAll : ∀ i, source.proj (R.point i) ≠ x := by
        intro i
        fin_cases i
        · exact R.point_zero_not_fiber
        · exact R.point_one_not_fiber
        · exact hp2
      let a : MusicFiber source x := ⟨base 2, hfiber⟩
      have table : ∀ s,
          (∃ c, (R.line 0).idxFun s = some c ∧
            (R.line 1).idxFun s = some c ∧ (R.line 2).idxFun s = some c) ∨
          ((R.line 0).idxFun s = none ∧ (R.line 1).idxFun s = none ∧
            (R.line 2).idxFun s = some a) ∨
          ((R.line 0).idxFun s = some a ∧ (R.line 1).idxFun s = none ∧
            (R.line 2).idxFun s = none) := by
        intro s
        rcases normalized_section_dichotomy source x lines R s with hc | hl
        · obtain ⟨q, hq, hs⟩ := hc
          obtain ⟨c, h0, h1, h2⟩ := constant_section_status source x lines R
            hpAll s q hq hs
          exact Or.inl ⟨c, h0, h1, h2⟩
        · have hrange := hallRange s hl
          by_cases heq : normalizedSection source x lines R s = base
          · right; left
            have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
              (R.point 0) R.point_zero_not_fiber s).2 <| by
                have hh := congrFun heq 0
                change sectionPoint source x (R.line 0) (R.point 0) s = base 0 at hh
                exact hh.trans hb0
            have hm1 := (moving_iff_sectionPoint_eq source x (R.line 1)
              (R.point 1) R.point_one_not_fiber s).2 <| by
                have hh := congrFun heq 1
                change sectionPoint source x (R.line 1) (R.point 1) s = base 1 at hh
                exact hh.trans hb1
            obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
              (R.line 2) (R.point 2) (base 2) hp2 hfiber s (congrFun heq 2)
            have hfa : f = a := Subtype.ext hv
            exact ⟨hm0, hm1, by simpa [hfa] using hf⟩
          · have hcoords : normalizedSection source x lines R s 0 ≠ R.point 0 ∨
                normalizedSection source x lines R s 1 ≠ R.point 1 ∨
                normalizedSection source x lines R s 2 ≠ base 2 := by
              by_contra h
              push Not at h
              apply heq
              funext i
              fin_cases i
              · exact h.1.trans hb0.symm
              · exact h.2.1.trans hb1.symm
              · exact h.2.2
            have hn := Erdos847ConfinementKernels.same_range_normal_forms
              R.point_zero_not_fiber R.point_one_not_fiber hl.1
              (section_admissible source x lines R s)
              (by rw [hrange, hbaseRange]) hcoords
            rcases hn with hn | hn
            · right; right
              obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
                (R.line 0) (R.point 0) (base 2) R.point_zero_not_fiber hfiber s hn.1
              have hfa : f = a := Subtype.ext hv
              have hm1 := (moving_iff_sectionPoint_eq source x (R.line 1)
                (R.point 1) R.point_one_not_fiber s).2 hn.2.1
              have hm2 := (moving_iff_sectionPoint_eq source x (R.line 2)
                (R.point 2) hp2 s).2 (hn.2.2.1.trans hA.2.2.2.symm)
              exact ⟨by simpa [hfa] using hf, hm1, hm2⟩
            · exfalso
              apply (by decide : (1 : Alphabet) ≠ 0)
              apply R.source_section.1
              change base 1 = base 0
              exact hb1.trans ((hn.2.2.2.symm.trans hA.2.2.2).trans hb0.symm)
      have hS : (R.line 0).idxFun R.coordinate = none ∧
          (R.line 1).idxFun R.coordinate = none ∧
          (R.line 2).idxFun R.coordinate = some a := by
        have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
          (R.point 0) R.point_zero_not_fiber R.coordinate).2 R.section_zero
        have hm1 := (moving_iff_sectionPoint_eq source x (R.line 1)
          (R.point 1) R.point_one_not_fiber R.coordinate).2 R.section_one
        obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
          (R.line 2) (R.point 2) (base 2) hp2 hfiber R.coordinate rfl
        have hfa : f = a := Subtype.ext hv
        exact ⟨hm0, hm1, by simpa [hfa] using hf⟩
      have hT : (R.line 0).idxFun t = some a ∧
          (R.line 1).idxFun t = none ∧ (R.line 2).idxFun t = none := by
        obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
          (R.line 0) (R.point 0) (base 2) R.point_zero_not_fiber hfiber t hA.1
        have hfa : f = a := Subtype.ext hv
        have hm1 := (moving_iff_sectionPoint_eq source x (R.line 1)
          (R.point 1) R.point_one_not_fiber t).2 hA.2.1
        have hm2 := (moving_iff_sectionPoint_eq source x (R.line 2)
          (R.point 2) hp2 t).2 (hA.2.2.1.trans hA.2.2.2.symm)
        exact ⟨by simpa [hfa] using hf, hm1, hm2⟩
      right
      exact ⟨R.line 0, R.line 1, R.line 2, R.line_mem 0, R.line_mem 1,
        R.line_mem 2, Erdos847FiniteArch.isRawTripod_of_section_table
          (R.line 0) (R.line 1) (R.line 2) a R.coordinate t table hS hT⟩
    · -- The second normal form is the same tripod with lines 0 and 1 exchanged.
      have hp2 : source.proj (R.point 2) ≠ x := by
        rw [hB.2.2.2]
        exact R.point_one_not_fiber
      have hpAll : ∀ i, source.proj (R.point i) ≠ x := by
        intro i
        fin_cases i
        · exact R.point_zero_not_fiber
        · exact R.point_one_not_fiber
        · exact hp2
      let a : MusicFiber source x := ⟨base 2, hfiber⟩
      have table : ∀ s,
          (∃ c, (R.line 1).idxFun s = some c ∧
            (R.line 0).idxFun s = some c ∧ (R.line 2).idxFun s = some c) ∨
          ((R.line 1).idxFun s = none ∧ (R.line 0).idxFun s = none ∧
            (R.line 2).idxFun s = some a) ∨
          ((R.line 1).idxFun s = some a ∧ (R.line 0).idxFun s = none ∧
            (R.line 2).idxFun s = none) := by
        intro s
        rcases normalized_section_dichotomy source x lines R s with hc | hl
        · obtain ⟨q, hq, hs⟩ := hc
          obtain ⟨c, h0, h1, h2⟩ := constant_section_status source x lines R
            hpAll s q hq hs
          exact Or.inl ⟨c, h1, h0, h2⟩
        · have hrange := hallRange s hl
          by_cases heq : normalizedSection source x lines R s = base
          · right; left
            have hm1 := (moving_iff_sectionPoint_eq source x (R.line 1)
              (R.point 1) R.point_one_not_fiber s).2 <| by
                have hh := congrFun heq 1
                change sectionPoint source x (R.line 1) (R.point 1) s = base 1 at hh
                exact hh.trans hb1
            have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
              (R.point 0) R.point_zero_not_fiber s).2 <| by
                have hh := congrFun heq 0
                change sectionPoint source x (R.line 0) (R.point 0) s = base 0 at hh
                exact hh.trans hb0
            obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
              (R.line 2) (R.point 2) (base 2) hp2 hfiber s (congrFun heq 2)
            have hfa : f = a := Subtype.ext hv
            exact ⟨hm1, hm0, by simpa [hfa] using hf⟩
          · have hcoords : normalizedSection source x lines R s 0 ≠ R.point 0 ∨
                normalizedSection source x lines R s 1 ≠ R.point 1 ∨
                normalizedSection source x lines R s 2 ≠ base 2 := by
              by_contra h
              push Not at h
              apply heq
              funext i
              fin_cases i
              · exact h.1.trans hb0.symm
              · exact h.2.1.trans hb1.symm
              · exact h.2.2
            have hn := Erdos847ConfinementKernels.same_range_normal_forms
              R.point_zero_not_fiber R.point_one_not_fiber hl.1
              (section_admissible source x lines R s)
              (by rw [hrange, hbaseRange]) hcoords
            rcases hn with hn | hn
            · exfalso
              apply (by decide : (0 : Alphabet) ≠ 1)
              apply R.source_section.1
              change base 0 = base 1
              exact hb0.trans ((hn.2.2.2.symm.trans hB.2.2.2).trans hb1.symm)
            · right; right
              obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
                (R.line 1) (R.point 1) (base 2) R.point_one_not_fiber hfiber s hn.2.1
              have hfa : f = a := Subtype.ext hv
              have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
                (R.point 0) R.point_zero_not_fiber s).2 hn.1
              have hm2 := (moving_iff_sectionPoint_eq source x (R.line 2)
                (R.point 2) hp2 s).2 (hn.2.2.1.trans hB.2.2.2.symm)
              exact ⟨by simpa [hfa] using hf, hm0, hm2⟩
      have hS : (R.line 1).idxFun R.coordinate = none ∧
          (R.line 0).idxFun R.coordinate = none ∧
          (R.line 2).idxFun R.coordinate = some a := by
        have hm1 := (moving_iff_sectionPoint_eq source x (R.line 1)
          (R.point 1) R.point_one_not_fiber R.coordinate).2 R.section_one
        have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
          (R.point 0) R.point_zero_not_fiber R.coordinate).2 R.section_zero
        obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
          (R.line 2) (R.point 2) (base 2) hp2 hfiber R.coordinate rfl
        have hfa : f = a := Subtype.ext hv
        exact ⟨hm1, hm0, by simpa [hfa] using hf⟩
      have hT : (R.line 1).idxFun t = some a ∧
          (R.line 0).idxFun t = none ∧ (R.line 2).idxFun t = none := by
        obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
          (R.line 1) (R.point 1) (base 2) R.point_one_not_fiber hfiber t hB.2.1
        have hfa : f = a := Subtype.ext hv
        have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
          (R.point 0) R.point_zero_not_fiber t).2 hB.1
        have hm2 := (moving_iff_sectionPoint_eq source x (R.line 2)
          (R.point 2) hp2 t).2 (hB.2.2.1.trans hB.2.2.2.symm)
        exact ⟨by simpa [hfa] using hf, hm0, hm2⟩
      right
      exact ⟨R.line 1, R.line 0, R.line 2, R.line_mem 1, R.line_mem 0,
        R.line_mem 2, Erdos847FiniteArch.isRawTripod_of_section_table
          (R.line 1) (R.line 0) (R.line 2) a R.coordinate t table hS hT⟩
  · left
    apply confined_of_all_nonconstant_base source x lines R
    intro s hs
    by_contra hne
    exact hdiff ⟨s, hs, hne⟩

/-- The first of the two distinct-range normal forms produces the exact
outer-line triangle.  Linearity of the base graph rules out the complementary
fiber mask for every later section. -/
theorem distinct_range_zero_triangle
    (R : NormalizedRawQuasiline source x lines l)
    (hlinear : G.Linear)
    (hfiber : source.proj
      (normalizedSection source x lines R R.coordinate 2) = x)
    (t : N)
    (htline : IsQuasiline source.embed
      (normalizedSection source x lines R t))
    (b : P)
    (hb : source.proj b = x)
    (hba : b ≠ normalizedSection source x lines R R.coordinate 2)
    (ht0 : normalizedSection source x lines R t 0 = R.point 0)
    (ht1 : normalizedSection source x lines R t 1 = b)
    (ht2 : normalizedSection source x lines R t 2 = R.point 2) :
    ∃ U W Z, U ∈ lines ∧ W ∈ lines ∧ Z ∈ lines ∧ IsRawTriangle U W Z := by
  classical
  let base := normalizedSection source x lines R R.coordinate
  let row := normalizedSection source x lines R t
  have hb0 : base 0 = R.point 0 := R.section_zero
  have hb1 : base 1 = R.point 1 := R.section_one
  have htMaps := source.quasiline_maps_edge row htline
  have htProjInj := mapsOntoEdge_proj_injective source htMaps
  have hp2 : source.proj (R.point 2) ≠ x := by
    intro hp2
    apply (by decide : (1 : Alphabet) ≠ 2)
    apply htProjInj
    simpa [row, ht1, ht2, hb, hp2]
  have hpAll : ∀ i, source.proj (R.point i) ≠ x := by
    intro i
    fin_cases i
    · exact R.point_zero_not_fiber
    · exact R.point_one_not_fiber
    · exact hp2
  have hproj12 : source.proj (R.point 1) = source.proj (R.point 2) := by
    have h := linear_forces_third_projection source hlinear base row
      (source.quasiline_maps_edge base R.source_section) htMaps
      (by simpa [base, row, hb0, ht0])
      (by simpa [base, row, ht1, hb, hfiber])
    simpa [base, row, hb1, ht2] using h
  let aa : MusicFiber source x := ⟨base 2, hfiber⟩
  let bb : MusicFiber source x := ⟨b, hb⟩
  have hab : aa ≠ bb := by
    intro h
    apply hba
    exact congrArg Subtype.val h.symm
  have table : ∀ s,
      (∃ c, (R.line 0).idxFun s = some c ∧
        (R.line 1).idxFun s = some c ∧ (R.line 2).idxFun s = some c) ∨
      ((R.line 0).idxFun s = none ∧ (R.line 1).idxFun s = none ∧
        (R.line 2).idxFun s = some aa) ∨
      ((R.line 0).idxFun s = none ∧ (R.line 1).idxFun s = some bb ∧
        (R.line 2).idxFun s = none) := by
    intro s
    rcases normalized_section_dichotomy source x lines R s with hc | hl
    · obtain ⟨q, hq, hs⟩ := hc
      obtain ⟨c, h0, h1, h2⟩ := constant_section_status source x lines R
        hpAll s q hq hs
      exact Or.inl ⟨c, h0, h1, h2⟩
    · let q := normalizedSection source x lines R s
      have hqMaps := source.quasiline_maps_edge q hl
      have hqProjInj := mapsOntoEdge_proj_injective source hqMaps
      have hforms := Erdos847ConfinementKernels.normalized_row_four_forms
        (section_admissible source x lines R s)
        (by
          intro i j hi hj
          exact source_section_atMostOne_fiber source x lines R s hl hi hj)
      rcases hforms with hF0 | hF1 | hF2 | hM
      · exfalso
        apply (by decide : (1 : Alphabet) ≠ 2)
        apply hqProjInj
        simpa [q, hF0.2.1, hF0.2.2] using hproj12
      · right; right
        have hRange : Set.range q = Set.range row :=
          combinatorialLine_range_eq_of_two_points source.embed source.embed_injective
            q row (source.quasiline_is_line q hl)
            (source.quasiline_is_line row htline)
            (by decide : (0 : Alphabet) ≠ 2)
            (hF1.1.trans ht0.symm) (hF1.2.2.trans ht2.symm)
        have hqb : q 1 = b := by
          have hm : q 1 ∈ Set.range row := by
            rw [← hRange]
            exact Set.mem_range_self 1
          rw [range_fin3] at hm
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
          rcases hm with h | h | h
          · exfalso
            apply R.point_zero_not_fiber
            have hxrow : source.proj (row 0) = x := by
              rw [← h]
              exact hF1.2.1
            simpa [row, ht0] using hxrow
          · simpa [q, row] using h.trans ht1
          · exfalso
            apply hp2
            have hxrow : source.proj (row 2) = x := by
              rw [← h]
              exact hF1.2.1
            simpa [row, ht2] using hxrow
        have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
          (R.point 0) R.point_zero_not_fiber s).2 hF1.1
        obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
          (R.line 1) (R.point 1) b R.point_one_not_fiber hb s hqb
        have hfb : f = bb := Subtype.ext hv
        have hm2 := (moving_iff_sectionPoint_eq source x (R.line 2)
          (R.point 2) hp2 s).2 hF1.2.2
        exact ⟨hm0, by simpa [hfb] using hf, hm2⟩
      · right; left
        have hRange : Set.range q = Set.range base :=
          combinatorialLine_range_eq_of_two_points source.embed source.embed_injective
            q base (source.quasiline_is_line q hl)
            (source.quasiline_is_line base R.source_section)
            (by decide : (0 : Alphabet) ≠ 1)
            (hF2.1.trans hb0.symm) (hF2.2.1.trans hb1.symm)
        have hqa : q 2 = base 2 := by
          have hm : q 2 ∈ Set.range base := by
            rw [← hRange]
            exact Set.mem_range_self 2
          rw [range_fin3] at hm
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
          rcases hm with h | h | h
          · exfalso
            apply R.point_zero_not_fiber
            rw [← hb0, ← h]
            exact hF2.2.2
          · exfalso
            apply R.point_one_not_fiber
            rw [← hb1, ← h]
            exact hF2.2.2
          · simpa [q, base] using h
        have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
          (R.point 0) R.point_zero_not_fiber s).2 hF2.1
        have hm1 := (moving_iff_sectionPoint_eq source x (R.line 1)
          (R.point 1) R.point_one_not_fiber s).2 hF2.2.1
        obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
          (R.line 2) (R.point 2) (base 2) hp2 hfiber s hqa
        have hfa : f = aa := Subtype.ext hv
        exact ⟨hm0, hm1, by simpa [hfa] using hf⟩
      · exfalso
        have hRange : Set.range q = Set.range base :=
          combinatorialLine_range_eq_of_two_points source.embed source.embed_injective
            q base (source.quasiline_is_line q hl)
            (source.quasiline_is_line base R.source_section)
            (by decide : (0 : Alphabet) ≠ 1)
            (hM.1.trans hb0.symm) (hM.2.1.trans hb1.symm)
        have hm : q 2 ∈ Set.range base := by
          rw [← hRange]
          exact Set.mem_range_self 2
        rw [range_fin3] at hm
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
        rcases hm with h | h | h
        · apply (by decide : (2 : Alphabet) ≠ 0)
          apply hl.1
          exact h.trans (hb0.trans hM.1.symm)
        · apply (by decide : (2 : Alphabet) ≠ 1)
          apply hl.1
          exact h.trans (hb1.trans hM.2.1.symm)
        · apply hp2
          have hxq : source.proj (q 2) = x := by
            rw [h]
            exact hfiber
          simpa [q, hM.2.2] using hxq
  have hS : (R.line 0).idxFun R.coordinate = none ∧
      (R.line 1).idxFun R.coordinate = none ∧
      (R.line 2).idxFun R.coordinate = some aa := by
    have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
      (R.point 0) R.point_zero_not_fiber R.coordinate).2 R.section_zero
    have hm1 := (moving_iff_sectionPoint_eq source x (R.line 1)
      (R.point 1) R.point_one_not_fiber R.coordinate).2 R.section_one
    obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
      (R.line 2) (R.point 2) (base 2) hp2 hfiber R.coordinate rfl
    have hfa : f = aa := Subtype.ext hv
    exact ⟨hm0, hm1, by simpa [hfa] using hf⟩
  have hT : (R.line 0).idxFun t = none ∧
      (R.line 1).idxFun t = some bb ∧ (R.line 2).idxFun t = none := by
    have hm0 := (moving_iff_sectionPoint_eq source x (R.line 0)
      (R.point 0) R.point_zero_not_fiber t).2 ht0
    obtain ⟨f, hf, hv⟩ := fixed_value_of_sectionPoint_eq source x
      (R.line 1) (R.point 1) b R.point_one_not_fiber hb t ht1
    have hfb : f = bb := Subtype.ext hv
    have hm2 := (moving_iff_sectionPoint_eq source x (R.line 2)
      (R.point 2) hp2 t).2 ht2
    exact ⟨hm0, by simpa [hfb] using hf, hm2⟩
  exact ⟨R.line 0, R.line 1, R.line 2, R.line_mem 0, R.line_mem 1, R.line_mem 2,
    Erdos847FiniteArch.isRawTriangle_of_section_table
      (R.line 0) (R.line 1) (R.line 2) aa bb R.coordinate t hab table hS hT⟩

/-- The symmetric distinct-range normal form reduces to
`distinct_range_zero_triangle` by swapping the first two ternary indices. -/
theorem distinct_range_one_triangle
    (R : NormalizedRawQuasiline source x lines l)
    (hlinear : G.Linear)
    (hfiber : source.proj
      (normalizedSection source x lines R R.coordinate 2) = x)
    (t : N)
    (htline : IsQuasiline source.embed
      (normalizedSection source x lines R t))
    (b : P)
    (hb : source.proj b = x)
    (hba : b ≠ normalizedSection source x lines R R.coordinate 2)
    (ht0 : normalizedSection source x lines R t 0 = b)
    (ht1 : normalizedSection source x lines R t 1 = R.point 1)
    (ht2 : normalizedSection source x lines R t 2 = R.point 2) :
    ∃ U W Z, U ∈ lines ∧ W ∈ lines ∧ Z ∈ lines ∧ IsRawTriangle U W Z := by
  let τ : Equiv.Perm Alphabet := Equiv.swap 0 1
  have hτ2 : τ 2 = 2 := by
    simp [τ, Equiv.swap_apply_of_ne_of_ne]
  let S : NormalizedRawQuasiline source x lines l := {
    perm := τ.trans R.perm
    line := fun i => R.line (τ i)
    point := fun i => R.point (τ i)
    coordinate := R.coordinate
    line_mem := fun i => R.line_mem (τ i)
    word_eq := by
      intro i
      simpa [τ] using R.word_eq (τ i)
    outer_quasiline := by
      simpa using isQuasiline_reindex (rawEmbed source x lines)
        (fun i => l (R.perm i)) R.outer_quasiline τ
    source_section := by
      simpa using isQuasiline_reindex source.embed
        (fun i => sectionPoint source x (R.line i) (R.point i) R.coordinate)
        R.source_section τ
    point_zero_not_fiber := by simpa [τ] using R.point_one_not_fiber
    point_one_not_fiber := by simpa [τ] using R.point_zero_not_fiber
    section_zero := by simpa [τ] using R.section_one
    section_one := by simpa [τ] using R.section_zero }
  exact distinct_range_zero_triangle source x lines S hlinear
    (by simpa [normalizedSection, S, hτ2] using hfiber) t
    (by
      have hs := isQuasiline_reindex source.embed
        (normalizedSection source x lines R t) htline τ
      simpa [normalizedSection, S] using hs)
    b hb
    (by simpa [normalizedSection, S, hτ2] using hba)
    (by simpa [normalizedSection, S, τ] using ht1)
    (by simpa [normalizedSection, S, τ] using ht0)
    (by simpa [normalizedSection, S, hτ2] using ht2)

/-- The complete distinct-range branch: the elementary ternary classifier
chooses one of the two orientations proved above. -/
theorem distinct_range_fiber_triangle
    (R : NormalizedRawQuasiline source x lines l)
    (hlinear : G.Linear)
    (hfiber : source.proj
      (normalizedSection source x lines R R.coordinate 2) = x)
    (t : N)
    (htline : IsQuasiline source.embed
      (normalizedSection source x lines R t))
    (htrange : Set.range (normalizedSection source x lines R t) ≠
      Set.range (normalizedSection source x lines R R.coordinate)) :
    ∃ U W Z, U ∈ lines ∧ W ∈ lines ∧ Z ∈ lines ∧ IsRawTriangle U W Z := by
  let base := normalizedSection source x lines R R.coordinate
  let row := normalizedSection source x lines R t
  have hb0 : base 0 = R.point 0 := R.section_zero
  have hb1 : base 1 = R.point 1 := R.section_one
  have hp01 : R.point 0 ≠ R.point 1 := by
    intro h
    apply (by decide : (0 : Alphabet) ≠ 1)
    apply R.source_section.1
    exact R.section_zero.trans (h.trans R.section_one.symm)
  have hinter : (Set.range row ∩
      ({R.point 0, R.point 1, base 2} : Set P)).Subsingleton := by
    have hi := combinatorialLine_range_inter_subsingleton source.embed
      source.embed_injective row base
      (source.quasiline_is_line row htline)
      (source.quasiline_is_line base R.source_section) htrange
    simpa [range_fin3, hb0, hb1] using hi
  have hforms := Erdos847ConfinementKernels.distinct_range_normal_forms
    hp01 R.point_zero_not_fiber R.point_one_not_fiber
    (section_admissible source x lines R t)
    (by
      intro i j hi hj
      exact source_section_atMostOne_fiber source x lines R t htline hi hj)
    hinter
  rcases hforms with ⟨b, hb, hba, ht0, ht1, ht2⟩ |
      ⟨b, hb, hba, ht0, ht1, ht2⟩
  · exact distinct_range_zero_triangle source x lines R hlinear hfiber t htline
      b hb hba ht0 ht1 ht2
  · exact distinct_range_one_triangle source x lines R hlinear hfiber t htline
      b hb hba ht0 ht1 ht2

/-- Proposition 4.5 in normalized form, specialized to a linear ternary base
graph.  The only alternatives to confinement are an exact RRS tripod or
triangle, both excluded by the sparse selected line system. -/
theorem normalized_confined_of_sparse_linear
    (R : NormalizedRawQuasiline source x lines l)
    (hlinear : G.Linear)
    (htripod : RawLineSystemHasNoTripod lines)
    (htriangle : RawLineSystemHasNoTriangle lines) :
    NormalizedConfined source x lines R := by
  let base := normalizedSection source x lines R R.coordinate
  by_cases hfiber : source.proj (base 2) = x
  · by_cases hall : ∀ s,
        IsQuasiline source.embed (normalizedSection source x lines R s) →
        Set.range (normalizedSection source x lines R s) = Set.range base
    · rcases same_range_fiber_confined_or_tripod source x lines R hfiber hall with
        hconf | ⟨U, W, Z, hU, hW, hZ, htrip⟩
      · exact hconf
      · exact False.elim (htripod hU hW hZ htrip)
    · push Not at hall
      obtain ⟨t, htline, htrange⟩ := hall
      obtain ⟨U, W, Z, hU, hW, hZ, htri⟩ :=
        distinct_range_fiber_triangle source x lines R hlinear hfiber t htline htrange
      exact False.elim (htriangle hU hW hZ htri)
  · have hlines := outside_third_lines_equal source x lines R hfiber
    have hb2 : base 2 = R.point 2 := by
      apply (sectionPoint_mem_fiber_or_eq source x (R.line 2) (R.point 2)
        R.coordinate).resolve_left
      exact hfiber
    have hbase : base = R.point := by
      funext i
      fin_cases i
      · exact R.section_zero
      · exact R.section_one
      · exact hb2
    refine ⟨R.line 0, R.line_mem 0, R.point, ?_, ?_⟩
    · rw [← hbase]
      exact R.source_section
    · intro i
      have hli : R.line i = R.line 0 := by
        fin_cases i
        · rfl
        · exact hlines.1.symm
        · exact hlines.2.symm
      apply Subtype.ext
      simpa [standardCopy, hli] using R.word_eq i

/-- Concrete confinement theorem for the literal raw partite amalgamation. -/
theorem raw_everyQuasilineConfined_of_sparse_linear
    (hlinear : G.Linear)
    (htripod : RawLineSystemHasNoTripod lines)
    (htriangle : RawLineSystemHasNoTriangle lines) :
    EveryQuasilineConfined source (rawAmalgamationData source x lines) := by
  intro q hq
  obtain ⟨R⟩ := normalize_raw_quasiline source x lines q hq
  obtain ⟨U, hU, p, hp, hcopy⟩ :=
    normalized_confined_of_sparse_linear source x lines R hlinear htripod htriangle
  let p' : Alphabet → P := fun i => p (R.perm.symm i)
  refine ⟨⟨U, hU⟩, p', isQuasiline_reindex source.embed p hp R.perm.symm, ?_⟩
  intro i
  have h := hcopy (R.perm.symm i)
  simpa [p', rawAmalgamationData] using h

end NormalizedSections

end Erdos847Confinement

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Util/EuclideanGeometry.lean` -/

section
/-! Scoped notation for the Euclidean plane, shared by geometric developments. -/

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos846.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 846.
https://www.erdosproblems.com/forum/thread/846

Informal authors:
- a DeepMind prover agent

Statement authors:
- Formal Conjectures authors

Formal authors:
- a DeepMind prover agent
- George Tsoukalas

URLs:
- https://www.erdosproblems.com/forum/thread/846#post-4447
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/846.lean
- https://github.com/google-deepmind/formal-conjectures/blob/2404258180688283e5141021c75464dc2acfb798/FormalConjectures/ErdosProblems/846.lean
-/
/-
Copyright 2025 The Formal Conjectures Authors.

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

section
open Set

variable {α : Type*} {r : α → α → α → Prop} {s t : Set α} {x y z : α}

end

/-!
# Erdős Problem 846

*Reference:* [erdosproblems.com/846](https://www.erdosproblems.com/846)
-/
open EuclideanGeometry

namespace Erdos846

section Prelims

end Prelims

open MeasureTheory
open Polynomial
open scoped BigOperators
open scoped ENNReal
open scoped EuclideanGeometry
open scoped InnerProductSpace
open scoped intervalIntegral
open scoped List
open scoped Matrix
open scoped Nat
open scoped NNReal
open scoped Pointwise
open scoped ProbabilityTheory
open scoped Real
open scoped symmDiff
open scoped Topology

def IsTriangle (e₁ e₂ e₃ : ℕ × ℕ) : Prop :=
  ∃ i j k : ℕ, i < j ∧ j < k ∧
    ({e₁, e₂, e₃} : Set (ℕ × ℕ)) = {(i, j), (j, k), (i, k)}

def R_num : ℕ → ℕ
| 0 => 3
| (K + 1) => (K + 1) * R_num K + 2

lemma finite_ramsey_ind (K : ℕ) (V : Finset ℕ) (c : (ℕ × ℕ) → Fin K)
    (hV : V.card ≥ R_num K) :
  ∃ i ∈ V, ∃ j ∈ V, ∃ k ∈ V,
    i < j ∧ j < k ∧ c (i, j) = c (j, k) ∧ c (j, k) = c (i, k) := by
  classical
  induction K generalizing V with
  | zero =>
    exact Fin.elim0 (c (0, 0))
  | succ K ih =>
    have h_nonempty : V.Nonempty := by
      delta Erdos846.R_num at*
      apply V.card_ne_zero.mp<|ne_zero_of_lt hV
    let v0 := V.min' h_nonempty
    let V' := V.erase v0
    have h_pigeon :
        ∃ c0 : Fin (K + 1), ∃ S ⊆ V',
          S.card ≥ R_num K ∧ ∀ x ∈ S, c (v0, x) = c0 := by
      delta Erdos846.R_num at*
      refine(Finset.exists_le_of_sum_le Finset.univ_nonempty ?_).imp fun and y=>
        ⟨ _, (V').filter_subset _,y.2, fun and=>And.right ∘ Finset.mem_filter.1⟩
      exact ( Fin.sum_const _ _).trans_le
        (V'.card_eq_sum_card_fiberwise (fun a s=> Finset.mem_univ (c _))▸
          V.card_erase_of_mem (V.min'_mem _)▸Nat.le_pred_of_lt ((Nat.le_of_lt hV)))
    obtain ⟨c0, S, hS_sub, hS_card, hS_c⟩ := h_pigeon
    have h_S_sub_V : S ⊆ V := hS_sub.trans (V.erase_subset _)
    have h_case :
        (∃ x ∈ S, ∃ y ∈ S, x < y ∧ c (x, y) = c0) ∨
          (∀ x ∈ S, ∀ y ∈ S, x < y → c (x, y) ≠ c0) := by
      by_cases h : ∃ x ∈ S, ∃ y ∈ S, x < y ∧ c (x, y) = c0
      · exact Or.inl h
      · exact Or.inr fun x hx y hy hxy hxyc => h ⟨x, hx, y, hy, hxy, hxyc⟩
    cases h_case with
    | inl h1 =>
      obtain ⟨x, hx, y, hy, hxy, hcxy⟩ := h1
      have hv0_in : v0 ∈ V := by apply V.min'_mem
      have hx_in : x ∈ V := h_S_sub_V hx
      have hy_in : y ∈ V := h_S_sub_V hy
      have hv0x : v0 < x := by
        exact lt_of_le_of_ne (V.min'_le x hx_in) (Ne.symm (Finset.mem_erase.mp (hS_sub hx)).1)
      have hc0x : c (v0, x) = c0 := hS_c x hx
      have hc0y : c (v0, y) = c0 := hS_c y hy
      use v0, hv0_in, x, hx_in, y, hy_in
      exact ⟨hv0x, hxy, hc0x.trans hcxy.symm, hcxy.trans hc0y.symm⟩
    | inr h2 =>
      have hKpos : 0 < K := by
        by_contra hK
        have hK0 : K = 0 := Nat.eq_zero_of_not_pos hK
        subst K
        have hS_two : 1 < S.card := by
          have hS_three : 3 ≤ S.card := by
            simpa [R_num] using hS_card
          omega
        obtain ⟨x, hx, y, hy, hxy_ne⟩ := Finset.one_lt_card.mp hS_two
        rcases lt_or_gt_of_ne hxy_ne with hxy | hyx
        · have hc_eq : c (x, y) = c0 := by
            apply Fin.ext
            omega
          exact h2 x hx y hy hxy hc_eq
        · have hc_eq : c (y, x) = c0 := by
            apply Fin.ext
            omega
          exact h2 y hy x hx hyx hc_eq
      have h1_prop : ∀ x : Fin (K+1), x.val < c0.val → x.val < K := by omega
      have h2_prop : ∀ x : Fin (K+1), x.val > c0.val → x.val - 1 < K := by
        match K with | 0 => omega | 1 => omega | K + 2 => omega
      let map_color : Fin (K + 1) → Fin K := fun x =>
        if h : x.val < c0.val then ⟨x.val, h1_prop x h⟩
        else if h2 : x.val > c0.val then ⟨x.val - 1, h2_prop x h2⟩
        else ⟨0, hKpos⟩
      let c' : (ℕ × ℕ) → Fin K := fun e => map_color (c e)
      have h_inj : ∀ a b, a ≠ c0 → b ≠ c0 → map_color a = map_color b → a = b := by
        intro a b ha_ne hb_ne hmap
        apply Fin.ext
        have hval := congrArg Fin.val hmap
        by_cases ha_lt : a < c0
        · have ha_val_lt : a.val < c0.val := ha_lt
          by_cases hb_lt : b < c0
          · simpa [map_color, ha_lt, hb_lt] using hval
          · have hb_gt : b.val > c0.val := by
              have hb_val_ne : b.val ≠ c0.val := by
                intro h
                exact hb_ne (Fin.ext h)
              omega
            have hb_fin_gt : c0 < b := hb_gt
            simp [map_color, ha_lt, hb_lt, hb_fin_gt] at hval
            omega
        · have ha_gt : a.val > c0.val := by
            have ha_val_ne : a.val ≠ c0.val := by
              intro h
              exact ha_ne (Fin.ext h)
            omega
          have ha_fin_gt : c0 < a := ha_gt
          by_cases hb_lt : b < c0
          · have hb_val_lt : b.val < c0.val := hb_lt
            simp [map_color, ha_lt, ha_fin_gt, hb_lt] at hval
            omega
          · have hb_gt : b.val > c0.val := by
              have hb_val_ne : b.val ≠ c0.val := by
                intro h
                exact hb_ne (Fin.ext h)
              omega
            have hb_fin_gt : c0 < b := hb_gt
            simp [map_color, ha_lt, ha_fin_gt, hb_lt, hb_fin_gt] at hval
            omega
      obtain ⟨i, hi, j, hj, k, hk, hij, hjk, hc1, hc2⟩ := ih S c' hS_card
      use i, h_S_sub_V hi, j, h_S_sub_V hj, k, h_S_sub_V hk
      refine ⟨hij, hjk, ?_, ?_⟩
      · have hc_i_j : c (i, j) ≠ c0 := h2 i hi j hj hij
        have hc_j_k : c (j, k) ≠ c0 := h2 j hj k hk hjk
        exact h_inj (c (i, j)) (c (j, k)) hc_i_j hc_j_k hc1
      · have hc_j_k : c (j, k) ≠ c0 := h2 j hj k hk hjk
        have hc_i_k : c (i, k) ≠ c0 := h2 i hi k hk (lt_trans hij hjk)
        exact h_inj (c (j, k)) (c (i, k)) hc_j_k hc_i_k hc2

lemma finite_ramsey (K : ℕ) : ∃ N : ℕ,
  ∀ c : (ℕ × ℕ) → Fin K,
    ∃ i j k, i < j ∧ j < k ∧ k < N ∧
      c (i, j) = c (j, k) ∧ c (j, k) = c (i, k) := by
  use R_num K + 1
  intro c
  let V := Finset.range (R_num K + 1)
  have hV : V.card ≥ R_num K := by
    simp [V]
  obtain ⟨i, hi, j, hj, k, hk, hij, hjk, hc1, hc2⟩ := finite_ramsey_ind K V c hV
  use i, j, k
  refine ⟨hij, hjk, ?_, hc1, hc2⟩
  · have h_k_in : k ∈ Finset.range (R_num K + 1) := hk
    rw [Finset.mem_range] at h_k_in
    exact h_k_in

end Erdos846

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/TriangleBase.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The triangle hypergraph used as the first finite model for Erdős 847

The vertices are the (increasingly oriented) edges of a complete graph.  Three
vertices form a hyperedge when the corresponding graph edges are the boundary
of a graph triangle.  This file records the three elementary properties of
this model: its finite Ramsey property, the max-cut half-density estimate, and
its linearity (hence, in particular, exclusion of `K₄⁽³⁾` minus an edge).
-/

namespace Erdos847TriangleBase

open Erdos846
open scoped BigOperators

/-- The increasingly oriented edges of the complete graph on `Fin N`, written
as pairs of natural numbers so that we can directly reuse `Erdos846`'s Ramsey
and max-cut arguments. -/
def vertices (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range N).product (Finset.range N)).filter fun e ↦ e.1 < e.2

@[simp] lemma mem_vertices {N : ℕ} {e : ℕ × ℕ} :
    e ∈ vertices N ↔ e.1 < e.2 ∧ e.2 < N := by
  rcases e with ⟨a, b⟩
  simp [vertices]
  omega

/-- Hyperedges are triples of graph edges forming a graph triangle. -/
abbrev IsHyperedge := Erdos846.IsTriangle

/-- The complete-graph triangle hypergraph is Ramsey: for every number of
colors, one sufficiently large finite base has a monochromatic hyperedge. -/
theorem exists_monochromatic_hyperedge (r : ℕ) :
    ∃ N : ℕ, ∀ color : (ℕ × ℕ) → Fin r,
      ∃ e₀ ∈ vertices N, ∃ e₁ ∈ vertices N, ∃ e₂ ∈ vertices N,
        e₀ ≠ e₁ ∧ e₀ ≠ e₂ ∧ e₁ ≠ e₂ ∧
          IsHyperedge e₀ e₁ e₂ ∧
          color e₀ = color e₁ ∧ color e₁ = color e₂ := by
  obtain ⟨N, hN⟩ := Erdos846.finite_ramsey r
  refine ⟨N, fun color ↦ ?_⟩
  obtain ⟨i, j, k, hij, hjk, hkN, hc₀, hc₁⟩ := hN color
  refine ⟨(i, j), ?_, (j, k), ?_, (i, k), ?_, ?_, ?_, ?_, ?_, hc₀, hc₁⟩
  · exact mem_vertices.mpr ⟨hij, lt_trans hjk hkN⟩
  · exact mem_vertices.mpr ⟨hjk, hkN⟩
  · exact mem_vertices.mpr ⟨lt_trans hij hjk, hkN⟩
  · intro h
    have := congrArg Prod.fst h
    simp at this
    omega
  · intro h
    have := congrArg Prod.snd h
    simp at this
    omega
  · intro h
    have := congrArg Prod.fst h
    simp at this
    omega
  · exact ⟨i, j, k, hij, hjk, rfl⟩

/-- The same Ramsey statement for a coloring whose domain is exactly the
finite vertex set (rather than an ambient coloring of all natural pairs). -/
theorem exists_monochromatic_hyperedge_on_vertices (r : ℕ) :
    ∃ N : ℕ, ∀ color : {e // e ∈ vertices N} → Fin r,
      ∃ e₀ e₁ e₂ : {e // e ∈ vertices N},
        e₀ ≠ e₁ ∧ e₀ ≠ e₂ ∧ e₁ ≠ e₂ ∧
          IsHyperedge e₀.1 e₁.1 e₂.1 ∧
          color e₀ = color e₁ ∧ color e₁ = color e₂ := by
  obtain ⟨N, hN⟩ := exists_monochromatic_hyperedge r
  refine ⟨N + 2, fun color ↦ ?_⟩
  have hdefault : (0, 1) ∈ vertices (N + 2) := mem_vertices.mpr ⟨by omega, by omega⟩
  let defaultVertex : {e // e ∈ vertices (N + 2)} := ⟨(0, 1), hdefault⟩
  let ambientColor : (ℕ × ℕ) → Fin r := fun e ↦
    if he : e ∈ vertices (N + 2) then color ⟨e, he⟩ else color defaultVertex
  obtain ⟨e₀, he₀, e₁, he₁, e₂, he₂, h₀₁, h₀₂, h₁₂, htri, hc₀, hc₁⟩ := hN ambientColor
  have he₀' : e₀ ∈ vertices (N + 2) := by
    have he := mem_vertices.mp he₀
    exact mem_vertices.mpr ⟨he.1, lt_trans he.2 (by omega)⟩
  have he₁' : e₁ ∈ vertices (N + 2) := by
    have he := mem_vertices.mp he₁
    exact mem_vertices.mpr ⟨he.1, lt_trans he.2 (by omega)⟩
  have he₂' : e₂ ∈ vertices (N + 2) := by
    have he := mem_vertices.mp he₂
    exact mem_vertices.mpr ⟨he.1, lt_trans he.2 (by omega)⟩
  refine ⟨⟨e₀, he₀'⟩, ⟨e₁, he₁'⟩, ⟨e₂, he₂'⟩, ?_, ?_, ?_, htri, ?_, ?_⟩
  · intro h
    exact h₀₁ (congrArg Subtype.val h)
  · intro h
    exact h₀₂ (congrArg Subtype.val h)
  · intro h
    exact h₁₂ (congrArg Subtype.val h)
  · dsimp [ambientColor] at hc₀
    rw [dif_pos he₀', dif_pos he₁'] at hc₀
    exact hc₀
  · dsimp [ambientColor] at hc₁
    rw [dif_pos he₁', dif_pos he₂'] at hc₁
    exact hc₁

/-- Weighted form of the max-cut estimate, with an explicit bound on all
endpoints.  The induction assigns the last graph vertex to whichever side
captures at least half of the total incident weight. -/
private theorem weighted_maxCut_bounded (n : ℕ) (S : Finset (ℕ × ℕ))
    (weight : (ℕ × ℕ) → ℕ)
    (hne : ∀ e ∈ S, e.1 ≠ e.2)
    (hbound : ∀ e ∈ S, e.1 < n ∧ e.2 < n) :
    ∃ cut : ℕ → Bool,
      2 * ∑ e ∈ S.filter (fun e ↦ cut e.1 ≠ cut e.2), weight e ≥
        ∑ e ∈ S, weight e := by
  induction n generalizing S with
  | zero =>
      refine ⟨fun _ ↦ true, ?_⟩
      have hS0 : S = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        exact Nat.not_lt_zero e.1 (hbound e he).1
      simp [hS0]
  | succ n ih =>
      let old := S.filter (fun e ↦ e.1 < n ∧ e.2 < n)
      let fresh := S.filter (fun e ↦ ¬ (e.1 < n ∧ e.2 < n))
      have hold_bound : ∀ e ∈ old, e.1 < n ∧ e.2 < n := by
        intro e he
        exact (Finset.mem_filter.mp he).2
      have hold_ne : ∀ e ∈ old, e.1 ≠ e.2 := by
        intro e he
        exact hne e (Finset.mem_filter.mp he).1
      obtain ⟨cut, hcut⟩ := ih old hold_ne hold_bound
      have htotal :
          (∑ e ∈ S, weight e) =
            (∑ e ∈ old, weight e) + ∑ e ∈ fresh, weight e := by
        simpa [old, fresh] using
          (Finset.sum_filter_add_sum_filter_not S
            (fun e : ℕ × ℕ ↦ e.1 < n ∧ e.2 < n) weight).symm
      have hsplit (g : ℕ → Bool) :
          (∑ e ∈ S.filter (fun e ↦ g e.1 ≠ g e.2), weight e) =
            (∑ e ∈ old.filter (fun e ↦ g e.1 ≠ g e.2), weight e) +
              ∑ e ∈ fresh.filter (fun e ↦ g e.1 ≠ g e.2), weight e := by
        let p : ℕ × ℕ → Prop := fun e ↦ e.1 < n ∧ e.2 < n
        let q : ℕ × ℕ → Prop := fun e ↦ g e.1 ≠ g e.2
        have hpartition := Finset.sum_filter_add_sum_filter_not (S.filter q) p weight
        have hleft : (S.filter q).filter p = old.filter q := by
          ext e
          simp [old, p, q, and_left_comm, and_assoc, and_comm]
        have hright : (S.filter q).filter (fun e ↦ ¬ p e) = fresh.filter q := by
          ext e
          simp [fresh, p, q, and_assoc, and_comm]
        rw [hleft, hright] at hpartition
        exact hpartition.symm
      let cutTrue := fun x ↦ if x = n then true else cut x
      let cutFalse := fun x ↦ if x = n then false else cut x
      have htrue_old :
          (∑ e ∈ old.filter (fun e ↦ cutTrue e.1 ≠ cutTrue e.2), weight e) =
            ∑ e ∈ old.filter (fun e ↦ cut e.1 ≠ cut e.2), weight e := by
        have hfilters :
            old.filter (fun e ↦ cutTrue e.1 ≠ cutTrue e.2) =
              old.filter (fun e ↦ cut e.1 ≠ cut e.2) := by
          apply Finset.filter_congr
          intro e he
          have heb := hold_bound e he
          simp [cutTrue, Nat.ne_of_lt heb.1, Nat.ne_of_lt heb.2]
        rw [hfilters]
      have hfalse_old :
          (∑ e ∈ old.filter (fun e ↦ cutFalse e.1 ≠ cutFalse e.2), weight e) =
            ∑ e ∈ old.filter (fun e ↦ cut e.1 ≠ cut e.2), weight e := by
        have hfilters :
            old.filter (fun e ↦ cutFalse e.1 ≠ cutFalse e.2) =
              old.filter (fun e ↦ cut e.1 ≠ cut e.2) := by
          apply Finset.filter_congr
          intro e he
          have heb := hold_bound e he
          simp [cutFalse, Nat.ne_of_lt heb.1, Nat.ne_of_lt heb.2]
        rw [hfilters]
      have hfresh_complement :
          fresh.filter (fun e ↦ cutFalse e.1 ≠ cutFalse e.2) =
            fresh.filter (fun e ↦ ¬ (cutTrue e.1 ≠ cutTrue e.2)) := by
        apply Finset.filter_congr
        intro e he
        have heS : e ∈ S := (Finset.mem_filter.mp he).1
        have hnot : ¬ (e.1 < n ∧ e.2 < n) := (Finset.mem_filter.mp he).2
        have hb := hbound e heS
        have hneq := hne e heS
        have hcases : (e.1 = n ∧ e.2 < n) ∨ (e.1 < n ∧ e.2 = n) := by omega
        rcases hcases with h | h
        · cases hcut2 : cut e.2 <;>
            simp [cutTrue, cutFalse, h.1, Nat.ne_of_lt h.2, hcut2]
        · cases hcut1 : cut e.1 <;>
            simp [cutTrue, cutFalse, Nat.ne_of_lt h.1, h.2, hcut1]
      have hfresh_sum :
          (∑ e ∈ fresh.filter (fun e ↦ cutTrue e.1 ≠ cutTrue e.2), weight e) +
              ∑ e ∈ fresh.filter (fun e ↦ cutFalse e.1 ≠ cutFalse e.2), weight e =
            ∑ e ∈ fresh, weight e := by
        rw [hfresh_complement]
        exact Finset.sum_filter_add_sum_filter_not fresh
          (fun e ↦ cutTrue e.1 ≠ cutTrue e.2) weight
      have hone :
          2 * (∑ e ∈ fresh.filter (fun e ↦ cutTrue e.1 ≠ cutTrue e.2), weight e) ≥
              ∑ e ∈ fresh, weight e ∨
            2 * (∑ e ∈ fresh.filter (fun e ↦ cutFalse e.1 ≠ cutFalse e.2), weight e) ≥
              ∑ e ∈ fresh, weight e := by
        omega
      rcases hone with htrue | hfalse
      · refine ⟨cutTrue, ?_⟩
        rw [hsplit cutTrue, htotal, htrue_old]
        omega
      · refine ⟨cutFalse, ?_⟩
        rw [hsplit cutFalse, htotal, hfalse_old]
        omega

/-- Every finite naturally weighted graph admits a cut containing at least half
of its total edge weight. -/
theorem exists_weighted_cut (S : Finset (ℕ × ℕ)) (weight : (ℕ × ℕ) → ℕ)
    (hne : ∀ e ∈ S, e.1 ≠ e.2) :
    ∃ cut : ℕ → Bool,
      2 * ∑ e ∈ S.filter (fun e ↦ cut e.1 ≠ cut e.2), weight e ≥
        ∑ e ∈ S, weight e := by
  let n := S.sup (fun e ↦ max e.1 e.2) + 1
  have hbound : ∀ e ∈ S, e.1 < n ∧ e.2 < n := by
    intro e he
    have hle := S.le_sup (f := fun e ↦ max e.1 e.2) he
    dsimp [n]
    omega
  exact weighted_maxCut_bounded n S weight hne hbound

/-- The triangle hypergraph is linear: two hyperedges which share two vertices
have the same third vertex. -/
theorem third_edge_unique {a b c d : ℕ × ℕ} (hab : a ≠ b)
    (habc : IsHyperedge a b c) (habd : IsHyperedge a b d) : c = d := by
  rcases habc with ⟨i, j, k, hij, hjk, hijk⟩
  rcases habd with ⟨p, q, r, hpq, hqr, hpqr⟩
  have hijkSet := hijk
  have hpqrSet := hpqr
  simp only [Set.ext_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hijk hpqr
  have ha₁ : a = (i, j) ∨ a = (j, k) ∨ a = (i, k) := (hijk a).mp (by simp)
  have hb₁ : b = (i, j) ∨ b = (j, k) ∨ b = (i, k) := (hijk b).mp (by simp)
  have ha₂ : a = (p, q) ∨ a = (q, r) ∨ a = (p, r) := (hpqr a).mp (by simp)
  have hb₂ : b = (p, q) ∨ b = (q, r) ∨ b = (p, r) := (hpqr b).mp (by simp)
  have hcanonCard :
      ({(i, j), (j, k), (i, k)} : Set (ℕ × ℕ)).encard = 3 := by
    apply Set.encard_eq_three.mpr
    refine ⟨(i, j), (j, k), (i, k), ?_, ?_, ?_, rfl⟩
    all_goals intro h; simp only [Prod.mk.injEq] at h; omega
  have habcCard : ({a, b, c} : Set (ℕ × ℕ)).encard = 3 := by
    rw [hijkSet]
    exact hcanonCard
  have hca : c ≠ a := by
    intro h
    subst c
    have : ({b, a} : Set (ℕ × ℕ)).encard = 3 := by simpa using habcCard
    rw [Set.encard_pair hab.symm] at this
    norm_num at this
  have hcb : c ≠ b := by
    intro h
    subst c
    have : ({a, b} : Set (ℕ × ℕ)).encard = 3 := by simpa using habcCard
    rw [Set.encard_pair hab] at this
    norm_num at this
  have hcanonEq :
      ({(i, j), (j, k), (i, k)} : Set (ℕ × ℕ)) =
        {(p, q), (q, r), (p, r)} := by
    rcases ha₁ with ha₁ | ha₁ | ha₁ <;>
      rcases hb₁ with hb₁ | hb₁ | hb₁ <;>
      rcases ha₂ with ha₂ | ha₂ | ha₂ <;>
      rcases hb₂ with hb₂ | hb₂ | hb₂ <;>
      simp_all [Prod.ext_iff] <;> omega
  have habcd : ({a, b, c} : Set (ℕ × ℕ)) = {a, b, d} :=
    hijkSet.trans (hcanonEq.trans hpqrSet.symm)
  have hcMem : c ∈ ({a, b, d} : Set (ℕ × ℕ)) := habcd.subset (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcMem
  rcases hcMem with h | h | h
  · exact (hca h).elim
  · exact (hcb h).elim
  · exact h

/-- The hyperedge relation depends only on the underlying three-element set,
not on the order in which the three graph edges are listed. -/
theorem isHyperedge_of_set_eq {a b c x y z : ℕ × ℕ}
    (h : IsHyperedge a b c)
    (hs : ({x, y, z} : Set (ℕ × ℕ)) = {a, b, c}) :
    IsHyperedge x y z := by
  rcases h with ⟨i, j, k, hij, hjk, hset⟩
  exact ⟨i, j, k, hij, hjk, hs.trans hset⟩

/-- Recenter a hyperedge at any two distinct vertices it contains. -/
theorem hyperedge_recenter {a b c x y : ℕ × ℕ}
    (h : IsHyperedge a b c)
    (hx : x ∈ ({a, b, c} : Set (ℕ × ℕ)))
    (hy : y ∈ ({a, b, c} : Set (ℕ × ℕ))) (hxy : x ≠ y) :
    ∃ z, IsHyperedge x y z ∧
      ({a, b, c} : Set (ℕ × ℕ)) = {x, y, z} := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl
  · rcases hy with rfl | rfl | rfl
    · exact (hxy rfl).elim
    · refine ⟨c, isHyperedge_of_set_eq h ?_, ?_⟩ <;>
        ext u <;> simp [or_comm, or_left_comm]
    · refine ⟨b, isHyperedge_of_set_eq h ?_, ?_⟩ <;>
        ext u <;> simp [or_comm, or_left_comm]
  · rcases hy with rfl | rfl | rfl
    · refine ⟨c, isHyperedge_of_set_eq h ?_, ?_⟩ <;>
        ext u <;> simp [or_comm, or_left_comm]
    · exact (hxy rfl).elim
    · refine ⟨a, isHyperedge_of_set_eq h ?_, ?_⟩ <;>
        ext u <;> simp [or_comm, or_left_comm]
  · rcases hy with rfl | rfl | rfl
    · refine ⟨b, isHyperedge_of_set_eq h ?_, ?_⟩ <;>
        ext u <;> simp [or_comm, or_left_comm]
    · refine ⟨a, isHyperedge_of_set_eq h ?_, ?_⟩ <;>
        ext u <;> simp [or_comm, or_left_comm]
    · exact (hxy rfl).elim

/-- A finite set of graph edges is a hyperedge of the triangle hypergraph. -/
def IsHyperedgeSet (E : Finset (ℕ × ℕ)) : Prop :=
  ∃ a b c, IsHyperedge a b c ∧ E = {a, b, c}

/-- `ThreeGraph.Linear`-style formulation: two distinct hyperedge-sets intersect
in at most one vertex. -/
theorem hyperedgeSets_linear {E F : Finset (ℕ × ℕ)}
    (hE : IsHyperedgeSet E) (hF : IsHyperedgeSet F) (hEF : E ≠ F) :
    (E ∩ F).card ≤ 1 := by
  by_contra hcard
  have hone : 1 < (E ∩ F).card := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hone
  have hxE : x ∈ E := (Finset.mem_inter.mp hx).1
  have hxF : x ∈ F := (Finset.mem_inter.mp hx).2
  have hyE : y ∈ E := (Finset.mem_inter.mp hy).1
  have hyF : y ∈ F := (Finset.mem_inter.mp hy).2
  rcases hE with ⟨a, b, c, habc, rfl⟩
  rcases hF with ⟨p, q, r, hpqr, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxE hxF hyE hyF
  have hxESet : x ∈ ({a, b, c} : Set (ℕ × ℕ)) := by simpa using hxE
  have hyESet : y ∈ ({a, b, c} : Set (ℕ × ℕ)) := by simpa using hyE
  have hxFSet : x ∈ ({p, q, r} : Set (ℕ × ℕ)) := by simpa using hxF
  have hyFSet : y ∈ ({p, q, r} : Set (ℕ × ℕ)) := by simpa using hyF
  obtain ⟨z, hxyz, hEset⟩ := hyperedge_recenter habc hxESet hyESet hxy
  obtain ⟨w, hxyw, hFset⟩ := hyperedge_recenter hpqr hxFSet hyFSet hxy
  have hzw : z = w := third_edge_unique hxy hxyz hxyw
  apply hEF
  apply Finset.ext
  intro u
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hmemE := Set.ext_iff.mp hEset u
  have hmemF := Set.ext_iff.mp hFset u
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmemE hmemF
  rw [hmemE, hmemF, hzw]

end Erdos847TriangleBase

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/TriangleAdapter.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Adapter from the complete-graph triangle model to the RRS finite interfaces

This file packages `Erdos847TriangleBase` as an
`Erdos847Pictures.ThreeGraph`, then proves the precise Ramsey, fractional,
and linear properties consumed by the picture iteration.
-/

namespace Erdos847TriangleAdapter

open scoped BigOperators
open Erdos847Pictures Erdos847FiniteArch Erdos847Iteration
open Erdos847TriangleBase

/-- Vertices of the finite base are the edges of the complete graph on
`Fin N`. -/
abbrev Vertex (N : ℕ) := {e : ℕ × ℕ // e ∈ vertices N}

/-- The predicate defining a hyperedge on the finite vertex subtype. -/
def IsTriangleEdge {N : ℕ} (E : Finset (Vertex N)) : Prop :=
  ∃ a b c : Vertex N,
    IsHyperedge a.1 b.1 c.1 ∧ E = {a, b, c}

/-- The `3`-graph of graph triangles in the complete graph on `Fin N`. -/
noncomputable def triangleGraph (N : ℕ) : ThreeGraph (Vertex N) where
  edges := by
    classical
    exact (Finset.univ.powersetCard 3).filter IsTriangleEdge
  uniform := by
    classical
    intro E hE
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hE).1).2

/-- Exact edge membership in `triangleGraph`.  The cardinality conjunct is
kept explicit, so this correspondence does not need a separate proof that
`IsTriangle` itself forces its three arguments to be distinct. -/
@[simp] theorem mem_triangleGraph_edges {N : ℕ} {E : Finset (Vertex N)} :
    E ∈ (triangleGraph N).edges ↔ E.card = 3 ∧ IsTriangleEdge E := by
  classical
  change E ∈ (Finset.univ.powersetCard 3).filter IsTriangleEdge ↔ _
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨_, hcard⟩, htri⟩
    exact ⟨hcard, htri⟩
  · rintro ⟨hcard, htri⟩
    exact ⟨⟨Finset.subset_univ E, hcard⟩, htri⟩

/-- A listed triangle of three distinct subtype vertices is an edge. -/
theorem triple_mem_triangleGraph {N : ℕ} {a b c : Vertex N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (htri : IsHyperedge a.1 b.1 c.1) :
    ({a, b, c} : Finset (Vertex N)) ∈ (triangleGraph N).edges := by
  rw [mem_triangleGraph_edges]
  refine ⟨by simp [hab, hac, hbc], a, b, c, htri, rfl⟩

/-- Convert the concrete monochromatic-triangle statement into the abstract
`ThreeGraph.RamseyFor` interface. -/
theorem triangleGraph_ramseyFor_of {N r : ℕ}
    (hRamsey : ∀ color : Vertex N → Fin r,
      ∃ e₀ e₁ e₂ : Vertex N,
        e₀ ≠ e₁ ∧ e₀ ≠ e₂ ∧ e₁ ≠ e₂ ∧
          IsHyperedge e₀.1 e₁.1 e₂.1 ∧
          color e₀ = color e₁ ∧ color e₁ = color e₂) :
    Erdos847Iteration.ThreeGraph.RamseyFor (triangleGraph N) (Fin r) := by
  classical
  intro color
  obtain ⟨e₀, e₁, e₂, h₀₁, h₀₂, h₁₂, htri, hc₀, hc₁⟩ := hRamsey color
  let E : Finset (Vertex N) := {e₀, e₁, e₂}
  have hE : E ∈ (triangleGraph N).edges := by
    exact triple_mem_triangleGraph h₀₁ h₀₂ h₁₂ htri
  refine ⟨⟨E, hE⟩, color e₀, ?_⟩
  intro v hv
  change v ∈ E at hv
  simp only [E, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · rfl
  · exact hc₀.symm
  · exact hc₁.symm.trans hc₀.symm

/-- Forget the finite-bound proofs on a set of base vertices. -/
def edgeVal {N : ℕ} (E : Finset (Vertex N)) : Finset (ℕ × ℕ) :=
  E.image Subtype.val

theorem edgeVal_injective {N : ℕ} : Function.Injective (@edgeVal N) := by
  classical
  intro E F hEF
  apply Finset.ext
  intro x
  have hmem := congrArg (fun S : Finset (ℕ × ℕ) ↦ x.1 ∈ S) hEF
  simpa [edgeVal] using hmem

theorem edgeVal_card {N : ℕ} (E : Finset (Vertex N)) :
    (edgeVal E).card = E.card := by
  classical
  exact Finset.card_image_of_injective E Subtype.val_injective

theorem edgeVal_isHyperedgeSet {N : ℕ} {E : Finset (Vertex N)}
    (hE : IsTriangleEdge E) : IsHyperedgeSet (edgeVal E) := by
  classical
  rcases hE with ⟨a, b, c, htri, rfl⟩
  refine ⟨a.1, b.1, c.1, htri, ?_⟩
  simp [edgeVal]

/-- The complete-graph triangle model is a linear `ThreeGraph`. -/
theorem triangleGraph_linear (N : ℕ) : (triangleGraph N).Linear := by
  classical
  intro E F htwo
  by_contra hEF
  have hvalNe : edgeVal E.1 ≠ edgeVal F.1 := by
    intro h
    exact hEF (Subtype.ext (edgeVal_injective h))
  have hElin : IsHyperedgeSet (edgeVal E.1) :=
    edgeVal_isHyperedgeSet (mem_triangleGraph_edges.mp E.2).2
  have hFlin : IsHyperedgeSet (edgeVal F.1) :=
    edgeVal_isHyperedgeSet (mem_triangleGraph_edges.mp F.2).2
  have hbase := hyperedgeSets_linear hElin hFlin hvalNe
  have hsub : edgeVal (E.1 ∩ F.1) ⊆ edgeVal E.1 ∩ edgeVal F.1 := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    have hv' := Finset.mem_inter.mp hv
    exact Finset.mem_inter.mpr ⟨
      Finset.mem_image.mpr ⟨v, hv'.1, rfl⟩,
      Finset.mem_image.mpr ⟨v, hv'.2, rfl⟩⟩
  have himage : 2 ≤ (edgeVal E.1 ∩ edgeVal F.1).card := by
    calc
      2 ≤ (E.1 ∩ F.1).card := htwo
      _ = (edgeVal (E.1 ∩ F.1)).card := (edgeVal_card _).symm
      _ ≤ (edgeVal E.1 ∩ edgeVal F.1).card := Finset.card_le_card hsub
  omega

/-- The max-cut half bound implies the cleared-denominator `1/3`
fractional property required by the finite RRS architecture. -/
theorem triangleGraph_natFractionalThird (N : ℕ) :
    NatFractionalThird (triangleGraph N).edges := by
  classical
  intro w
  let ambientWeight : (ℕ × ℕ) → ℕ := fun e ↦
    if he : e ∈ vertices N then w ⟨e, he⟩ else 0
  have hne : ∀ e ∈ vertices N, e.1 ≠ e.2 := by
    intro e he
    exact ne_of_lt (mem_vertices.mp he).1
  obtain ⟨cut, hcut⟩ := exists_weighted_cut (vertices N) ambientWeight hne
  let crossing : Finset (ℕ × ℕ) :=
    (vertices N).filter fun e ↦ cut e.1 ≠ cut e.2
  let I : Finset (Vertex N) :=
    Finset.univ.filter fun e ↦ cut e.1.1 ≠ cut e.1.2
  have htotal :
      (∑ e ∈ vertices N, ambientWeight e) = ∑ v : Vertex N, w v := by
    calc
      (∑ e ∈ vertices N, ambientWeight e) =
          ∑ v : Vertex N, ambientWeight v.1 := by
            exact Finset.sum_subtype (vertices N) (fun _ ↦ Iff.rfl) ambientWeight
      _ = ∑ v : Vertex N, w v := by
        apply Finset.sum_congr rfl
        intro v hv
        dsimp [ambientWeight]
        rw [if_pos v.2]
  have hselected :
      (∑ e ∈ crossing, ambientWeight e) = ∑ v ∈ I, w v := by
    apply Finset.sum_bij
      (fun e he ↦ (⟨e, (Finset.mem_filter.mp he).1⟩ : Vertex N))
    · intro e he
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Finset.mem_filter.mp he).2
    · intro e₁ he₁ e₂ he₂ h
      exact congrArg Subtype.val h
    · intro v hv
      refine ⟨v.1, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨v.2, (Finset.mem_filter.mp hv).2⟩
      · rfl
    · intro e he
      dsimp [ambientWeight]
      rw [dif_pos (Finset.mem_filter.mp he).1]
  refine ⟨I, ?_, ?_⟩
  · intro E hE hEI
    obtain ⟨hcard, a, b, c, htri, rfl⟩ := mem_triangleGraph_edges.mp hE
    have haI : a ∈ I := hEI (by simp)
    have hbI : b ∈ I := hEI (by simp)
    have hcI : c ∈ I := hEI (by simp)
    have haCross : cut a.1.1 ≠ cut a.1.2 := (Finset.mem_filter.mp haI).2
    have hbCross : cut b.1.1 ≠ cut b.1.2 := (Finset.mem_filter.mp hbI).2
    have hcCross : cut c.1.1 ≠ cut c.1.2 := (Finset.mem_filter.mp hcI).2
    rcases htri with ⟨i, j, k, hij, hjk, hset⟩
    have hcross : ∀ e ∈ ({a.1, b.1, c.1} : Set (ℕ × ℕ)),
        cut e.1 ≠ cut e.2 := by
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl
      · exact haCross
      · exact hbCross
      · exact hcCross
    have hIJ : cut i ≠ cut j := hcross (i, j) (by rw [hset]; simp)
    have hJK : cut j ≠ cut k := hcross (j, k) (by rw [hset]; simp)
    have hIK : cut i ≠ cut k := hcross (i, k) (by rw [hset]; simp)
    cases hi : cut i <;> cases hj : cut j <;> cases hk : cut k <;> simp_all
  · rw [← htotal, ← hselected]
    change 2 * (∑ e ∈ crossing, ambientWeight e) ≥
      ∑ e ∈ vertices N, ambientWeight e at hcut
    omega

/-- Inclusion of complete-graph edge vertices when the ambient order grows. -/
def vertexInclusion {N M : ℕ} (hNM : N ≤ M) : Vertex N → Vertex M := fun e ↦
  ⟨e.1, mem_vertices.mpr ⟨(mem_vertices.mp e.2).1,
    lt_of_lt_of_le (mem_vertices.mp e.2).2 hNM⟩⟩

theorem vertexInclusion_injective {N M : ℕ} (hNM : N ≤ M) :
    Function.Injective (vertexInclusion hNM) := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun x : Vertex M ↦ x.1) h

/-- Concrete monochromatic triangles persist when extra complete-graph
vertices are added. -/
theorem monochromatic_hyperedge_mono {N M r : ℕ} (hNM : N ≤ M)
    (hRamsey : ∀ color : Vertex N → Fin r,
      ∃ e₀ e₁ e₂ : Vertex N,
        e₀ ≠ e₁ ∧ e₀ ≠ e₂ ∧ e₁ ≠ e₂ ∧
          IsHyperedge e₀.1 e₁.1 e₂.1 ∧
          color e₀ = color e₁ ∧ color e₁ = color e₂) :
    ∀ color : Vertex M → Fin r,
      ∃ e₀ e₁ e₂ : Vertex M,
        e₀ ≠ e₁ ∧ e₀ ≠ e₂ ∧ e₁ ≠ e₂ ∧
          IsHyperedge e₀.1 e₁.1 e₂.1 ∧
          color e₀ = color e₁ ∧ color e₁ = color e₂ := by
  intro color
  let inc := vertexInclusion hNM
  obtain ⟨e₀, e₁, e₂, h₀₁, h₀₂, h₁₂, htri, hc₀, hc₁⟩ :=
    hRamsey (fun e ↦ color (inc e))
  refine ⟨inc e₀, inc e₁, inc e₂, ?_, ?_, ?_, ?_, hc₀, hc₁⟩
  · exact (vertexInclusion_injective hNM).ne h₀₁
  · exact (vertexInclusion_injective hNM).ne h₀₂
  · exact (vertexInclusion_injective hNM).ne h₁₂
  · exact htri

/-- Bundled finite base, enlarged to have at least three complete-graph
vertices for the picture-zero fiber construction. -/
theorem exists_triangleBase_package (r : ℕ) :
    ∃ N : ℕ, 3 ≤ N ∧
      Erdos847Iteration.ThreeGraph.RamseyFor (triangleGraph N) (Fin r) ∧
      NatFractionalThird (triangleGraph N).edges ∧
      (triangleGraph N).Linear := by
  obtain ⟨N, hN⟩ := exists_monochromatic_hyperedge_on_vertices r
  let M := N + 3
  have hNM : N ≤ M := by simp [M]
  have hRamseyM := monochromatic_hyperedge_mono hNM hN
  refine ⟨M, by simp [M], triangleGraph_ramseyFor_of hRamseyM,
    triangleGraph_natFractionalThird M, triangleGraph_linear M⟩

/-! ## A fiber-doubled initial picture -/

section DoubledPictureZero

variable {V : Type*} [DecidableEq V]
variable (G : ThreeGraph V)

/-- Two tagged copies of every point of picture zero. -/
abbrev DoubledZeroPoint := ZeroPoint G × Bool

/-- One extra coordinate records the Boolean tag. -/
abbrev DoubledZeroCoord := ZeroCoord G ⊕ Unit

def boolTag (b : Bool) : Alphabet := if b then 1 else 0

theorem boolTag_injective : Function.Injective boolTag := by
  intro a b h
  cases a <;> cases b <;> simp [boolTag] at h ⊢

def doubledZeroWord (p : DoubledZeroPoint G) : DoubledZeroCoord G → Alphabet
  | Sum.inl c => zeroWord G p.1 c
  | Sum.inr _ => boolTag p.2

noncomputable def doubledZeroProj (p : DoubledZeroPoint G) : V := zeroProj G p.1

theorem doubledZeroWord_injective : Function.Injective (doubledZeroWord G) := by
  intro p q hpq
  have hfirst : p.1 = q.1 := by
    apply zeroWord_injective G
    funext c
    exact congrFun hpq (Sum.inl c)
  have htag : p.2 = q.2 := by
    apply boolTag_injective
    exact congrFun hpq (Sum.inr ())
  exact Prod.ext hfirst htag

/-- The Boolean tag is constant along every doubled quasiline. -/
theorem doubled_quasiline_tag_constant
    (l : Alphabet → DoubledZeroPoint G)
    (hl : IsQuasiline (doubledZeroWord G) l) :
    ∃ b : Bool, ∀ i, (l i).2 = b := by
  rcases hl.2 (Sum.inr ()) with hconst | hinj
  · refine ⟨(l 0).2, fun i ↦ ?_⟩
    apply boolTag_injective
    exact (hconst.choose_spec i).trans (hconst.choose_spec 0).symm
  · exfalso
    have htagInj : Function.Injective (fun i ↦ (l i).2) := by
      intro i j h
      apply hinj
      exact congrArg boolTag h
    exact (Fintype.not_injective_of_card_lt (fun i : Alphabet ↦ (l i).2) (by decide)) htagInj

/-- Forgetting the Boolean tag turns a doubled quasiline into a picture-zero
quasiline. -/
theorem doubled_quasiline_first
    (l : Alphabet → DoubledZeroPoint G)
    (hl : IsQuasiline (doubledZeroWord G) l) :
    IsQuasiline (zeroWord G) (fun i ↦ (l i).1) := by
  obtain ⟨b, hb⟩ := doubled_quasiline_tag_constant G l hl
  refine ⟨?_, ?_⟩
  · intro i j h
    apply hl.1
    apply Prod.ext h
    exact (hb i).trans (hb j).symm
  · intro c
    simpa [doubledZeroWord] using hl.2 (Sum.inl c)

/-- A fixed-tag lift of a picture-zero line is a line in the doubled
picture. -/
theorem doubled_line_of_zero_line (l : Alphabet → ZeroPoint G) (b : Bool)
    (hl : IsCombinatorialLine (zeroWord G) l) :
    IsCombinatorialLine (doubledZeroWord G) (fun i ↦ (l i, b)) := by
  rcases hl with ⟨hinj, σ, hσ⟩
  refine ⟨fun i j h ↦ hinj (congrArg Prod.fst h), σ, ?_⟩
  intro c
  cases c with
  | inl c => simpa [doubledZeroWord] using hσ c
  | inr _ => exact Or.inl ⟨boolTag b, fun _ ↦ rfl⟩

theorem doubled_quasiline_is_line
    (l : Alphabet → DoubledZeroPoint G)
    (hl : IsQuasiline (doubledZeroWord G) l) :
    IsCombinatorialLine (doubledZeroWord G) l := by
  obtain ⟨b, hb⟩ := doubled_quasiline_tag_constant G l hl
  obtain ⟨_, σ, hσ⟩ := zero_quasiline_is_line G (fun i ↦ (l i).1)
    (doubled_quasiline_first G l hl)
  refine ⟨hl.1, σ, ?_⟩
  intro c
  cases c with
  | inl c => simpa [doubledZeroWord] using hσ c
  | inr _ =>
      exact Or.inl ⟨boolTag b, fun i ↦ by simp [doubledZeroWord, hb i]⟩

theorem doubled_quasiline_maps_edge
    (l : Alphabet → DoubledZeroPoint G)
    (hl : IsQuasiline (doubledZeroWord G) l) :
    MapsOntoEdge G (doubledZeroProj G) l := by
  obtain ⟨e, he⟩ := zero_quasiline_maps_edge G (fun i ↦ (l i).1)
    (doubled_quasiline_first G l hl)
  refine ⟨e, ?_⟩
  change Set.range (fun i ↦ zeroProj G (l i).1) = (e.1 : Set V)
  exact he

/-- Picture zero with every point duplicated.  The extra tag coordinate
prevents a quasiline from mixing the two copies. -/
noncomputable def doubledPictureZero :
    Picture G (DoubledZeroPoint G) (DoubledZeroCoord G) where
  embed := doubledZeroWord G
  embed_injective := doubledZeroWord_injective G
  proj := doubledZeroProj G
  quasiline_is_line := doubled_quasiline_is_line G
  quasiline_maps_edge := doubled_quasiline_maps_edge G

/-- Fixed-tag copies still realize every base edge. -/
theorem doubledPictureZero_realizesEveryEdge :
    RealizesEveryEdge (doubledPictureZero G) := by
  intro e
  obtain ⟨l, hl, hrange⟩ := pictureZero_realizesEveryEdge G e
  refine ⟨fun a ↦ (l a, false), doubled_line_of_zero_line G l false hl, ?_⟩
  change Set.range (fun a ↦ zeroProj G (l a)) = (e.1 : Set V)
  change Set.range (fun a ↦ zeroProj G (l a)) = (e.1 : Set V) at hrange
  exact hrange

/-- Every fiber of the doubled picture is nontrivial as soon as the
corresponding base vertex lies in one base edge. -/
theorem doubledPictureZero_fiber_nontrivial
    (hincident : ∀ x : V, ∃ e : G.Edge, x ∈ e.1) (x : V) :
    Nontrivial (Erdos847Iteration.Fiber (doubledPictureZero G) x) := by
  obtain ⟨e, hxe⟩ := hincident x
  let vx : {v : V // v ∈ e.1} := ⟨x, hxe⟩
  obtain ⟨a, ha⟩ := (G.edgeEquiv e).surjective vx
  have hproj : doubledZeroProj G ((e, a), false) = x := by
    exact congrArg Subtype.val ha
  refine ⟨⟨((e, a), false), hproj⟩, ⟨((e, a), true), ?_⟩, ?_⟩
  · exact hproj
  · intro h
    have hp := congrArg Subtype.val h
    have hb := congrArg (fun p : DoubledZeroPoint G ↦ p.2) hp
    simp at hb

end DoubledPictureZero

/-! ## Incidence and doubled fibers for the triangle base -/

/-- When `N ≥ 3`, every complete-graph edge belongs to a graph triangle,
hence every vertex of `triangleGraph N` lies in a hyperedge. -/
theorem triangleGraph_vertex_incident {N : ℕ} (hN : 3 ≤ N) (x : Vertex N) :
    ∃ e : (triangleGraph N).Edge, x ∈ e.1 := by
  classical
  rcases x with ⟨⟨i, j⟩, hx⟩
  have hij : i < j := (mem_vertices.mp hx).1
  have hjN : j < N := (mem_vertices.mp hx).2
  by_cases hi0 : i = 0
  · subst i
    by_cases hj1 : j = 1
    · subst j
      let b : Vertex N := ⟨(0, 2), mem_vertices.mpr ⟨by omega, by omega⟩⟩
      let c : Vertex N := ⟨(1, 2), mem_vertices.mpr ⟨by omega, by omega⟩⟩
      have hxb : (⟨(0, 1), hx⟩ : Vertex N) ≠ b := by
        intro h
        have := congrArg (fun v : Vertex N ↦ v.1.2) h
        simp [b] at this
      have hxc : (⟨(0, 1), hx⟩ : Vertex N) ≠ c := by
        intro h
        have := congrArg (fun v : Vertex N ↦ v.1.1) h
        simp [c] at this
      have hbc : b ≠ c := by
        intro h
        have := congrArg (fun v : Vertex N ↦ v.1.1) h
        simp [b, c] at this
      have htri : IsHyperedge (0, 1) b.1 c.1 := by
        refine ⟨0, 1, 2, by omega, by omega, ?_⟩
        ext e
        simp [b, c, or_comm]
      let E : Finset (Vertex N) := {⟨(0, 1), hx⟩, b, c}
      have hE : E ∈ (triangleGraph N).edges :=
        triple_mem_triangleGraph hxb hxc hbc htri
      exact ⟨⟨E, hE⟩, by simp [E]⟩
    · have h1j : 1 < j := by omega
      let b : Vertex N := ⟨(0, 1), mem_vertices.mpr ⟨by omega, by omega⟩⟩
      let c : Vertex N := ⟨(1, j), mem_vertices.mpr ⟨h1j, hjN⟩⟩
      have hxb : (⟨(0, j), hx⟩ : Vertex N) ≠ b := by
        intro h
        apply hj1
        exact congrArg (fun v : Vertex N ↦ v.1.2) h
      have hxc : (⟨(0, j), hx⟩ : Vertex N) ≠ c := by
        intro h
        have := congrArg (fun v : Vertex N ↦ v.1.1) h
        simp [c] at this
      have hbc : b ≠ c := by
        intro h
        have := congrArg (fun v : Vertex N ↦ v.1.1) h
        simp [b, c] at this
      have htri : IsHyperedge (0, j) b.1 c.1 := by
        refine ⟨0, 1, j, by omega, h1j, ?_⟩
        ext e
        simp [b, c, or_comm, or_left_comm]
      let E : Finset (Vertex N) := {⟨(0, j), hx⟩, b, c}
      have hE : E ∈ (triangleGraph N).edges :=
        triple_mem_triangleGraph hxb hxc hbc htri
      exact ⟨⟨E, hE⟩, by simp [E]⟩
  · have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
    let b : Vertex N := ⟨(0, i), mem_vertices.mpr ⟨hiPos, lt_trans hij hjN⟩⟩
    let c : Vertex N := ⟨(0, j), mem_vertices.mpr ⟨lt_trans hiPos hij, hjN⟩⟩
    have hxb : (⟨(i, j), hx⟩ : Vertex N) ≠ b := by
      intro h
      apply hi0
      exact congrArg (fun v : Vertex N ↦ v.1.1) h
    have hxc : (⟨(i, j), hx⟩ : Vertex N) ≠ c := by
      intro h
      apply hi0
      exact congrArg (fun v : Vertex N ↦ v.1.1) h
    have hbc : b ≠ c := by
      intro h
      have := congrArg (fun v : Vertex N ↦ v.1.2) h
      exact (ne_of_lt hij) this
    have htri : IsHyperedge (i, j) b.1 c.1 := by
      refine ⟨0, i, j, hiPos, hij, ?_⟩
      ext e
      simp [b, c, or_left_comm]
    let E : Finset (Vertex N) := {⟨(i, j), hx⟩, b, c}
    have hE : E ∈ (triangleGraph N).edges :=
      triple_mem_triangleGraph hxb hxc hbc htri
    exact ⟨⟨E, hE⟩, by simp [E]⟩

/-- Consequently every source fiber of the doubled initial triangle picture
is nontrivial for the bundled bases (`N ≥ 3`). -/
theorem doubledTrianglePicture_fiber_nontrivial {N : ℕ} (hN : 3 ≤ N)
    (x : Vertex N) :
    Nontrivial (Erdos847Iteration.Fiber
      (doubledPictureZero (triangleGraph N)) x) :=
  doubledPictureZero_fiber_nontrivial (triangleGraph N)
    (triangleGraph_vertex_incident hN) x

end Erdos847TriangleAdapter

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/Encoding.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The ternary-word encoding used for Erdős 847

This file isolates the elementary encoding layer needed by the RRS construction.
Words in `Fin m → Fin 3` are read as base-six integers.  Base six is large enough
that a three-term arithmetic progression of encoded words has no carries, so it
is exactly a coordinatewise midpoint.  For three-letter words this means that
each coordinate is constant, `0,1,2`, or `2,1,0`.
-/

namespace Erdos847Encoding

open Set

/-- A word of length `m` over the three-letter alphabet. -/
abbrev Word (m : ℕ) := Fin m → Fin 3

/-- Interpret a ternary word using place values `6^i`.

This is the specialization to alphabet size three of the Hales--Jewett encoding
used in the formalization of Erdős 966.
-/
noncomputable def encode (m : ℕ) (v : Word m) : ℕ :=
  ∑ i : Fin m, (v i).val * 6 ^ (i : ℕ)

/-- The coordinate condition forced by a three-term arithmetic progression of
encoded words.  The word `v` is the coordinatewise midpoint of `u` and `w`.
-/
def IsWeakQuasiLine {m : ℕ} (u v w : Word m) : Prop :=
  ∀ i, (u i : ℕ) + (w i : ℕ) = 2 * (v i : ℕ)

/-- A set of words is quasiline-free if every coordinatewise midpoint triple in
the set is constant. -/
def QuasiLineFree {m : ℕ} (S : Set (Word m)) : Prop :=
  ∀ ⦃u⦄, u ∈ S → ∀ ⦃v⦄, v ∈ S → ∀ ⦃w⦄, w ∈ S →
    IsWeakQuasiLine u v w → u = w

/-- The base-six word encoding is injective. -/
theorem encode_injective (m : ℕ) : Function.Injective (encode m) := by
  intro v w hvw
  have h_eq : ∀ i, v i = w i := by
    induction m with
    | zero => simp
    | succ m ih =>
        have h0 : v 0 = w 0 := by
          have hmod := congrArg (· % 6) hvw
          unfold encode at hmod
          simp only [Fin.sum_univ_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero,
            mul_one, Fin.val_succ] at hmod
          simp only [pow_succ, ← mul_assoc, ← Finset.sum_mul] at hmod
          simp [Nat.add_mod] at hmod
          apply Fin.ext
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
          exact hmod
        have htail :
            encode m (fun i ↦ v i.succ) = encode m (fun i ↦ w i.succ) := by
          unfold encode at hvw ⊢
          simp only [Fin.sum_univ_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero,
            mul_one, Fin.val_succ] at hvw
          simp only [pow_succ, ← mul_assoc, ← Finset.sum_mul] at hvw
          rw [h0] at hvw
          exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < 6) (Nat.add_left_cancel hvw)
        exact fun i ↦ Fin.cases h0 (ih htail) i
  funext i
  exact h_eq i

/-- Classification of midpoints in the alphabet `{0,1,2}`. -/
theorem fin3_midpoint_iff (x y z : Fin 3) :
    (x : ℕ) + (z : ℕ) = 2 * (y : ℕ) ↔
      (x = y ∧ y = z) ∨
      (x = 0 ∧ y = 1 ∧ z = 2) ∨
      (x = 2 ∧ y = 1 ∧ z = 0) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

/-- A weak quasiline is equivalently coordinatewise constant, forward, or
reverse.  The orientation is allowed to vary between coordinates. -/
theorem isWeakQuasiLine_iff {m : ℕ} (u v w : Word m) :
    IsWeakQuasiLine u v w ↔
      ∀ i,
        (u i = v i ∧ v i = w i) ∨
        (u i = 0 ∧ v i = 1 ∧ w i = 2) ∨
        (u i = 2 ∧ v i = 1 ∧ w i = 0) := by
  simp only [IsWeakQuasiLine, fin3_midpoint_iff]

/-- Carry-free reflection: an arithmetic midpoint of encoded words is a
coordinatewise midpoint. -/
theorem encode_reflects_midpoint {m : ℕ} (u v w : Word m)
    (h : encode m u + encode m w = 2 * encode m v) :
    IsWeakQuasiLine u v w := by
  unfold IsWeakQuasiLine
  unfold encode at h
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Fin.sum_univ_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero,
        mul_one, Fin.val_succ] at h
      have hfirst : (u 0).val + (w 0).val = 2 * (v 0).val := by
        have hmod := congrArg (· % 6) h
        simp only [pow_succ, ← mul_assoc, ← Finset.sum_mul] at hmod
        simp [Nat.add_mod, Nat.mul_mod] at hmod
        simpa [Nat.mod_eq_of_lt (by omega : (u 0).val + (w 0).val < 6),
          Nat.mod_eq_of_lt (by omega : 2 * (v 0).val < 6)] using hmod
      have htail :
          (∑ i : Fin m, (u i.succ).val * 6 ^ (i : ℕ)) +
              ∑ i : Fin m, (w i.succ).val * 6 ^ (i : ℕ) =
            2 * ∑ i : Fin m, (v i.succ).val * 6 ^ (i : ℕ) := by
        simp only [pow_succ, ← mul_assoc, ← Finset.sum_mul] at h
        omega
      exact fun i ↦ Fin.cases hfirst
        (ih (fun j ↦ u j.succ) (fun j ↦ v j.succ) (fun j ↦ w j.succ) htail) i

/-- The set-level transport lemma: deleting all quasilines in word space is
enough to delete all nontrivial three-term arithmetic progressions after the
base-six encoding. -/
theorem threeAPFree_image_encode {m : ℕ} {S : Set (Word m)}
    (hS : QuasiLineFree S) :
    ThreeAPFree (encode m '' S) := by
  rw [threeAPFree_iff_eq_right]
  rintro a ⟨u, hu, rfl⟩ b ⟨v, hv, rfl⟩ c ⟨w, hw, rfl⟩ habc
  apply congrArg (encode m)
  exact hS hu hv hw (encode_reflects_midpoint u v w (by simpa [two_mul] using habc))

/-- Finset form of `threeAPFree_image_encode`. -/
theorem threeAPFree_finset_image_encode {m : ℕ} {S : Finset (Word m)}
    (hS : QuasiLineFree (S : Set (Word m))) :
    ThreeAPFree ((S.image (encode m) : Finset ℕ) : Set ℕ) := by
  rw [show ((S.image (encode m) : Finset ℕ) : Set ℕ) =
      encode m '' (S : Set (Word m)) by ext; simp]
  exact threeAPFree_image_encode hS

end Erdos847Encoding

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/PictureOutput.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Extracting a finite integer block from a final RRS picture

This file contains the last, elementary step of the finite RRS construction.
A finite picture which is Ramsey for `r` colours and which projects to a base
three-graph having the natural `1/3` fractional property gives a finite set of
natural numbers with the two properties needed by the separated-block
assembly.
-/

namespace Erdos847PictureOutput

open Function Set
open Erdos847Pictures Erdos847Encoding Erdos847FiniteArch

set_option autoImplicit false

/-- Reindex an arbitrary finite coordinate type by its canonical finite
ordinal.  This is only a change of names; all picture structure is preserved. -/
noncomputable def reindexFin {V P C : Type*} [DecidableEq V] [Fintype C]
    {G : ThreeGraph V} (picture : Picture G P C) :
    Picture G P (Fin (Fintype.card C)) where
  embed p i := picture.embed p ((Fintype.equivFin C).symm i)
  embed_injective := by
    intro p q hpq
    apply picture.embed_injective
    funext c
    have hi := congrFun hpq (Fintype.equivFin C c)
    simpa using hi
  proj := picture.proj
  quasiline_is_line := by
    intro l hl
    have hold : IsQuasiline picture.embed l := by
      refine ⟨hl.1, ?_⟩
      intro c
      simpa using hl.2 (Fintype.equivFin C c)
    rcases picture.quasiline_is_line l hold with ⟨hinj, σ, hσ⟩
    refine ⟨hinj, σ, ?_⟩
    intro i
    simpa using hσ ((Fintype.equivFin C).symm i)
  quasiline_maps_edge := by
    intro l hl
    apply picture.quasiline_maps_edge l
    refine ⟨hl.1, ?_⟩
    intro c
    simpa using hl.2 (Fintype.equivFin C c)

/-- A selected combinatorial line stays selected after finite-coordinate
reindexing. -/
theorem isCombinatorialLine_reindexFin {V P C : Type*} [DecidableEq V]
    [Fintype C] {G : ThreeGraph V} (picture : Picture G P C)
    {l : Alphabet → P} (hl : IsCombinatorialLine picture.embed l) :
    IsCombinatorialLine (reindexFin picture).embed l := by
  rcases hl with ⟨hinj, σ, hσ⟩
  refine ⟨hinj, σ, ?_⟩
  intro i
  simpa [reindexFin] using hσ ((Fintype.equivFin C).symm i)

/-- Coordinatewise midpoints are preserved by the base-six encoding. -/
theorem encode_preserves_midpoint {m : ℕ} (u v w : Word m)
    (h : IsWeakQuasiLine u v w) :
    encode m u + encode m w = 2 * encode m v := by
  unfold encode
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (u i).val * 6 ^ (i : ℕ) + (w i).val * 6 ^ (i : ℕ) =
        ((u i).val + (w i).val) * 6 ^ (i : ℕ) := (Nat.add_mul ..).symm
    _ = (2 * (v i).val) * 6 ^ (i : ℕ) := by rw [h i]
    _ = 2 * ((v i).val * 6 ^ (i : ℕ)) := by simp [Nat.mul_assoc]

/-- Reindexing a custom combinatorial line by its global alphabet permutation
puts its three encoded points in arithmetic-progression order. -/
theorem custom_line_encodes_AP {V P : Type*} [DecidableEq V]
    {G : ThreeGraph V} {m : ℕ} (picture : Picture G P (Fin m))
    (l : Alphabet → P) (hl : IsCombinatorialLine picture.embed l) :
    ∃ q : Alphabet → P,
      (∀ a, q a ∈ Set.range l) ∧
      encode m (picture.embed (q 0)) + encode m (picture.embed (q 2)) =
        2 * encode m (picture.embed (q 1)) ∧
      encode m (picture.embed (q 0)) ≠ encode m (picture.embed (q 2)) := by
  rcases hl with ⟨hlinj, σ, hσ⟩
  let q : Alphabet → P := fun a => l (σ.symm a)
  refine ⟨q, ?_, ?_, ?_⟩
  · intro a
    exact ⟨σ.symm a, rfl⟩
  · apply encode_preserves_midpoint
    intro c
    rcases hσ c with ⟨x, hx⟩ | hmove
    · simp only [q, hx]
      simp [two_mul]
    · simp only [q, hmove, Equiv.apply_symm_apply]
      decide
  · apply (encode_injective m).ne
    apply picture.embed_injective.ne
    apply hlinj.ne
    intro h
    have := congrArg σ h
    simp at this

/-- A word midpoint with distinct endpoints gives an injective custom
quasiline enumeration. -/
theorem isQuasiline_of_weak_of_ne {m : ℕ} (u v w : Word m)
    (hmid : IsWeakQuasiLine u v w) (huw : u ≠ w) :
    IsQuasiline id ![u, v, w] := by
  have huv : u ≠ v := by
    intro huv
    apply huw
    funext i
    have hi := hmid i
    have huvi := congrFun huv i
    apply Fin.ext
    rw [huvi] at hi
    omega
  have hvw : v ≠ w := by
    intro hvw
    apply huw
    funext i
    have hi := hmid i
    have hvwi := congrFun hvw i
    apply Fin.ext
    rw [hvwi] at hi
    omega
  constructor
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  · intro i
    rw [isWeakQuasiLine_iff] at hmid
    rcases hmid i with hconst | hforward | hreverse
    · left
      exact ⟨u i, by intro a; fin_cases a <;> simp_all⟩
    · right
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    · right
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all

/-- If all points of a picture project into an independent set of the base
three-graph, their words contain no nonconstant quasiline. -/
theorem quasiLineFree_image_of_independent
    {V P : Type*} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
    {G : ThreeGraph V} {m : ℕ} (picture : Picture G P (Fin m))
    {I : Finset V} (hI : Erdos847FiniteArch.Independent G.edges I)
    {D : Finset P} (hproj : ∀ p ∈ D, picture.proj p ∈ I) :
    QuasiLineFree ((D.image picture.embed : Finset (Word m)) : Set (Word m)) := by
  intro u hu v hv w hw hmid
  obtain ⟨pu, hpuD, hpu⟩ := Finset.mem_image.mp hu
  obtain ⟨pv, hpvD, hpv⟩ := Finset.mem_image.mp hv
  obtain ⟨pw, hpwD, hpw⟩ := Finset.mem_image.mp hw
  subst u
  subst v
  subst w
  by_contra huw
  let l : Alphabet → P := ![pu, pv, pw]
  have hwords : IsQuasiline id ![picture.embed pu, picture.embed pv, picture.embed pw] :=
    isQuasiline_of_weak_of_ne _ _ _ hmid huw
  have hl : IsQuasiline picture.embed l := by
    constructor
    · intro a b hab
      apply hwords.1
      fin_cases a <;> fin_cases b <;> simp_all [l]
    · intro c
      rcases hwords.2 c with ⟨d, hd⟩ | hinj
      · left
        refine ⟨d, ?_⟩
        intro a
        fin_cases a
        · simpa [l] using hd 0
        · simpa [l] using hd 1
        · simpa [l] using hd 2
      · right
        intro a b hab
        apply hinj
        fin_cases a <;> fin_cases b <;> simp_all [l]
  obtain ⟨e, he⟩ := picture.quasiline_maps_edge l hl
  apply hI e.1 e.2
  intro x hx
  have hxrange : x ∈ Set.range (fun a => picture.proj (l a)) := by
    rw [he]
    exact hx
  obtain ⟨a, rfl⟩ := hxrange
  fin_cases a
  · exact hproj pu hpuD
  · exact hproj pv hpvD
  · exact hproj pw hpwD

/-- The finite output theorem.  Its assumptions are precisely the two facts
provided by the final stage of the picture construction: Ramsey focusing and
the natural fractional-third property of the base graph. -/
theorem exists_encoded_block
    {V P : Type*} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
    {G : ThreeGraph V} {m r : ℕ} (picture : Picture G P (Fin m))
    (hr : 0 < r)
    (hRamsey : ∀ color : P → Fin r,
      ∃ l : Alphabet → P, IsCombinatorialLine picture.embed l ∧
        ∃ k : Fin r, ∀ a, color (l a) = k)
    (hFractional : NatFractionalThird G.edges) :
    ∃ X : Finset ℕ,
      X.Nonempty ∧
      (∀ color : ℕ → Fin r,
        ∃ a ∈ X, ∃ b ∈ X, ∃ c ∈ X,
          a + c = b + b ∧ a ≠ c ∧
          color a = color b ∧ color b = color c) ∧
      (∀ Y : Finset ℕ, Y ⊆ X →
        ∃ Z : Finset ℕ, Z ⊆ Y ∧ Y.card ≤ 3 * Z.card ∧
          ThreeAPFree (Z : Set ℕ)) := by
  let f : P → ℕ := fun p => encode m (picture.embed p)
  let X : Finset ℕ := Finset.univ.image f
  have hf : Function.Injective f :=
    (encode_injective m).comp picture.embed_injective
  have hXne : X.Nonempty := by
    let color : P → Fin r := fun _ => ⟨0, hr⟩
    obtain ⟨l, hl, k, hk⟩ := hRamsey color
    exact ⟨f (l 0), Finset.mem_image.mpr ⟨l 0, Finset.mem_univ _, rfl⟩⟩
  refine ⟨X, hXne, ?_, ?_⟩
  · intro color
    obtain ⟨l, hl, k, hk⟩ := hRamsey (fun p => color (f p))
    obtain ⟨q, hqrange, hAP, hne⟩ := custom_line_encodes_AP picture l hl
    refine ⟨f (q 0), ?_, f (q 1), ?_, f (q 2), ?_, ?_, hne, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨q 0, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨q 1, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨q 2, Finset.mem_univ _, rfl⟩
    · simpa [two_mul] using hAP
    · obtain ⟨a, ha⟩ := hqrange 0
      obtain ⟨b, hb⟩ := hqrange 1
      calc
        color (f (q 0)) = color (f (l a)) := congrArg (fun p => color (f p)) ha.symm
        _ = k := hk a
        _ = color (f (l b)) := (hk b).symm
        _ = color (f (q 1)) := congrArg (fun p => color (f p)) hb
    · obtain ⟨a, ha⟩ := hqrange 1
      obtain ⟨b, hb⟩ := hqrange 2
      calc
        color (f (q 1)) = color (f (l a)) := congrArg (fun p => color (f p)) ha.symm
        _ = k := hk a
        _ = color (f (l b)) := (hk b).symm
        _ = color (f (q 2)) := congrArg (fun p => color (f p)) hb
  · intro Y hYX
    let D : Finset P := Finset.univ.filter fun p => f p ∈ Y
    let pointWeight : P → ℕ := fun p => if p ∈ D then 1 else 0
    let W : V → ℕ := fun y => ∑ p with picture.proj p = y, pointWeight p
    obtain ⟨I, hI, hweight⟩ := hFractional W
    let E : Finset P := D.filter fun p => picture.proj p ∈ I
    let Z : Finset ℕ := E.image f
    have hDimage : D.image f = Y := by
      ext y
      constructor
      · intro hy
        obtain ⟨p, hpD, rfl⟩ := Finset.mem_image.mp hy
        exact (Finset.mem_filter.mp hpD).2
      · intro hy
        have hyX := hYX hy
        obtain ⟨p, hp, hpy⟩ := Finset.mem_image.mp hyX
        refine Finset.mem_image.mpr ⟨p, ?_, hpy⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpy ▸ hy⟩
    have hZsubset : Z ⊆ Y := by
      intro y hy
      obtain ⟨p, hpE, rfl⟩ := Finset.mem_image.mp hy
      have hpD := (Finset.mem_filter.mp hpE).1
      rw [← hDimage]
      exact Finset.mem_image.mpr ⟨p, hpD, rfl⟩
    have htotal : (∑ y, W y) = D.card := by
      have hfiber : (∑ y, W y) = ∑ p, pointWeight p := by
        simp only [W]
        simpa using Finset.sum_fiberwise (Finset.univ : Finset P)
          picture.proj pointWeight
      rw [hfiber]
      simp [pointWeight]
    have hselected : (∑ y ∈ I, W y) = E.card := by
      have hfiber : (∑ y ∈ I, W y) =
          ∑ p ∈ Finset.univ.filter (fun p => picture.proj p ∈ I), pointWeight p := by
        simp only [W]
        simpa using Finset.sum_fiberwise_eq_sum_filter
          (Finset.univ : Finset P) I picture.proj pointWeight
      rw [hfiber]
      simp [pointWeight, E, D, Finset.filter_filter, and_comm]
    have hcard : Y.card ≤ 3 * Z.card := by
      rw [← hDimage, Finset.card_image_of_injective _ hf]
      rw [show Z.card = E.card by simp [Z, Finset.card_image_of_injective _ hf]]
      rw [← htotal, ← hselected]
      exact hweight
    have hfreeWords :
        QuasiLineFree ((E.image picture.embed : Finset (Word m)) : Set (Word m)) := by
      apply quasiLineFree_image_of_independent picture hI
      intro p hpE
      exact (Finset.mem_filter.mp hpE).2
    have hfree : ThreeAPFree (Z : Set ℕ) := by
      have := threeAPFree_finset_image_encode hfreeWords
      simpa [Z, f, Finset.image_image] using this
    exact ⟨Z, hZsubset, hcard, hfree⟩

/-- Real-valued form of `exists_encoded_block`, ready to instantiate the
`mu = 1/3` density field in the separated-block assembly. -/
theorem exists_encoded_block_one_third
    {V P : Type*} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
    {G : ThreeGraph V} {m r : ℕ} (picture : Picture G P (Fin m))
    (hr : 0 < r)
    (hRamsey : ∀ color : P → Fin r,
      ∃ l : Alphabet → P, IsCombinatorialLine picture.embed l ∧
        ∃ k : Fin r, ∀ a, color (l a) = k)
    (hFractional : NatFractionalThird G.edges) :
    ∃ X : Finset ℕ,
      X.Nonempty ∧
      (∀ color : ℕ → Fin r,
        ∃ a ∈ X, ∃ b ∈ X, ∃ c ∈ X,
          a + c = b + b ∧ a ≠ c ∧
          color a = color b ∧ color b = color c) ∧
      (∀ Y : Finset ℕ, Y ⊆ X →
        ∃ Z : Finset ℕ, Z ⊆ Y ∧
          (Z.card : ℝ) ≥ (1 / 3 : ℝ) * Y.card ∧
          ThreeAPFree (Z : Set ℕ)) := by
  obtain ⟨X, hXne, hXRamsey, hXdense⟩ :=
    exists_encoded_block picture hr hRamsey hFractional
  refine ⟨X, hXne, hXRamsey, ?_⟩
  intro Y hYX
  obtain ⟨Z, hZY, hcard, hfree⟩ := hXdense Y hYX
  refine ⟨Z, hZY, ?_, hfree⟩
  have hcast : (Y.card : ℝ) ≤ 3 * (Z.card : ℝ) := by
    exact_mod_cast hcard
  norm_num at ⊢ hcast
  linarith

/-- Coordinate-type-independent output theorem.  In particular, it consumes
the `Coord` type produced existentially by the finite picture iteration
without asking that construction to choose a literal `Fin m`. -/
theorem exists_encoded_block_one_third_of_finite_coords
    {V P C : Type*} [Fintype V] [DecidableEq V]
    [Fintype P] [DecidableEq P] [Fintype C]
    {G : ThreeGraph V} {r : ℕ} (picture : Picture G P C)
    (hr : 0 < r)
    (hRamsey : ∀ color : P → Fin r,
      ∃ l : Alphabet → P, IsCombinatorialLine picture.embed l ∧
        ∃ k : Fin r, ∀ a, color (l a) = k)
    (hFractional : NatFractionalThird G.edges) :
    ∃ X : Finset ℕ,
      X.Nonempty ∧
      (∀ color : ℕ → Fin r,
        ∃ a ∈ X, ∃ b ∈ X, ∃ c ∈ X,
          a + c = b + b ∧ a ≠ c ∧
          color a = color b ∧ color b = color c) ∧
      (∀ Y : Finset ℕ, Y ⊆ X →
        ∃ Z : Finset ℕ, Z ⊆ Y ∧
          (Z.card : ℝ) ≥ (1 / 3 : ℝ) * Y.card ∧
          ThreeAPFree (Z : Set ℕ)) := by
  apply exists_encoded_block_one_third (reindexFin picture) hr
  · intro color
    obtain ⟨l, hl, k, hk⟩ := hRamsey color
    exact ⟨l, isCombinatorialLine_reindexFin picture hl, k, hk⟩
  · exact hFractional

end Erdos847PictureOutput

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/FinitePipeline.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Finite pipeline for Erdős 847

This module is the integration seam from the sparse Hales--Jewett theorem to
the iterated final picture and then to the encoded integer block.  While the
final sparse-selection and confinement theorems are being completed, the
fully concrete adapters are developed here.
-/

namespace Erdos847FinitePipeline

open Function Set Combinatorics
open Erdos847Pictures Erdos847Iteration
open Erdos847SparseLines
open Erdos847Confinement

set_option autoImplicit false

variable {V : Type} [DecidableEq V]
variable {G : ThreeGraph V}
variable {P C K : Type}

/-! ## Adapting a concrete sparse cube family -/

/-- A concrete sparse Hales--Jewett line system supplies the abstract family
interface used by the focusing layer. -/
theorem sparseFiberLineFamilyOf_nonempty
    (picture : Picture G P C) (x : V) (K : Type)
    [Nontrivial (Fiber picture x)]
    (h : SparseHalesJewett (Fiber picture x) K) :
    Nonempty (SparseFiberLineFamily picture x K) := by
  classical
  rcases h with ⟨N, hN, S, hsparse, hramsey⟩
  letI : Fintype N := hN
  let movingSupport : {U // U ∈ S} → Set N := fun U ↦
    (Erdos847SparseLines.movingSet U.1 : Set N)
  refine ⟨{
    Word := N → Fiber picture x
    Index := {U // U ∈ S}
    Move := N
    line := fun U ↦ U.1
    movingSupport := movingSupport
    line_injective := fun U ↦ line_apply_injective U.1
    highChromatic := ?_
    noTripod := ?_
    noTriangle := ?_
  }⟩
  · intro color
    obtain ⟨U, hUS, k, hk⟩ := hramsey color
    exact ⟨⟨U, hUS⟩, k, hk⟩
  · intro htripod
    apply hsparse.1
    rcases htripod with
      ⟨U, W, Z, hUW, hWZ, hZU, ⟨q, hqU, hqW, hqZ⟩, hmove, hdisj⟩
    have hUW' : U.1 ≠ W.1 := fun h ↦ hUW (Subtype.ext h)
    have hWZ' : W.1 ≠ Z.1 := fun h ↦ hWZ (Subtype.ext h)
    have hZU' : Z.1 ≠ U.1 := fun h ↦ hZU (Subtype.ext h)
    have hmove' : Erdos847SparseLines.movingSet U.1 =
        Erdos847SparseLines.movingSet W.1 ∪
          Erdos847SparseLines.movingSet Z.1 := by
      ext s
      have hs := Set.ext_iff.mp hmove s
      simpa [movingSupport] using hs
    have hdisj' : Disjoint (Erdos847SparseLines.movingSet W.1)
        (Erdos847SparseLines.movingSet Z.1) := by
      rw [Finset.disjoint_left]
      intro s hsW hsZ
      exact Set.disjoint_left.mp hdisj
        (by simpa [movingSupport] using hsW)
        (by simpa [movingSupport] using hsZ)
    exact ⟨U.1, U.2, W.1, W.2, Z.1, Z.2,
      hUW', hWZ', hZU', ⟨q, hqU, hqW, hqZ⟩, hmove', hdisj'⟩
  · intro htriangle
    apply hsparse.2
    rcases htriangle with
      ⟨U, W, Z, hUW, hWZ, hZU, hUWmeet, hWZmeet, hZUmeet, hempty⟩
    exact ⟨U.1, U.2, W.1, W.2, Z.1, Z.2,
      (fun h ↦ hUW (Subtype.ext h)),
      (fun h ↦ hWZ (Subtype.ext h)),
      (fun h ↦ hZU (Subtype.ext h)),
      hUWmeet, hWZmeet, hZUmeet, hempty⟩

/-- Choice of the concrete adapter packaged by the preceding propositional
existence theorem. -/
noncomputable def sparseFiberLineFamilyOf
    (picture : Picture G P C) (x : V) (K : Type)
    [Nontrivial (Fiber picture x)]
    (h : SparseHalesJewett (Fiber picture x) K) :
    SparseFiberLineFamily picture x K :=
  Classical.choice (sparseFiberLineFamilyOf_nonempty picture x K h)

/-! ## Translating the finite sparse predicates to raw line systems -/

theorem rawLineSystemHasNoTripod_of_isSparse
    {A N : Type} [Fintype N] (S : Finset (Line A N)) (hS : IsSparse S) :
    RawLineSystemHasNoTripod (S : Set (Line A N)) := by
  classical
  intro U W Z hU hW hZ hraw
  rcases hraw with ⟨hUW, hUZ, hWZ, hcommon, hmoving⟩
  have forbidden (L₀ L₁ L₂ : Line A N)
      (hL₀ : L₀ ∈ S) (hL₁ : L₁ ∈ S) (hL₂ : L₂ ∈ S)
      (h₀₁ : L₀ ≠ L₁) (h₁₂ : L₁ ≠ L₂) (h₂₀ : L₂ ≠ L₀)
      (hc : RawLinesCommonPoint L₀ L₁ L₂)
      (hm : RawMovingDisjointUnion L₀ L₁ L₂) : False := by
    apply hS.1
    rcases hc with ⟨a, b, c, hab, hbc⟩
    have hmove : Erdos847SparseLines.movingSet L₀ =
        Erdos847SparseLines.movingSet L₁ ∪
          Erdos847SparseLines.movingSet L₂ := by
      ext s
      have hs := Set.ext_iff.mp hm.1 s
      simpa [RawMovingSet, Erdos847SparseLines.movingSet] using hs
    have hdisj : Disjoint (Erdos847SparseLines.movingSet L₁)
        (Erdos847SparseLines.movingSet L₂) := by
      rw [Finset.disjoint_left]
      intro s hs₁ hs₂
      exact Set.disjoint_left.mp hm.2
        (by simpa [RawMovingSet, Erdos847SparseLines.movingSet] using hs₁)
        (by simpa [RawMovingSet, Erdos847SparseLines.movingSet] using hs₂)
    exact ⟨L₀, hL₀, L₁, hL₁, L₂, hL₂, h₀₁, h₁₂, h₂₀,
      ⟨L₀ a, ⟨a, rfl⟩, ⟨b, hab.symm⟩, ⟨c, (hab.trans hbc).symm⟩⟩,
      hmove, hdisj⟩
  rcases hmoving with hm | hm | hm
  · exact forbidden U W Z hU hW hZ hUW hWZ (fun h ↦ hUZ h.symm) hcommon hm
  · have hc : RawLinesCommonPoint W U Z := by
      rcases hcommon with ⟨a, b, c, hab, hbc⟩
      exact ⟨b, a, c, hab.symm, hab.trans hbc⟩
    exact forbidden W U Z hW hU hZ (fun h ↦ hUW h.symm) hUZ
      (Ne.symm hWZ) hc hm
  · have hc : RawLinesCommonPoint Z U W := by
      rcases hcommon with ⟨a, b, c, hab, hbc⟩
      exact ⟨c, a, b, (hab.trans hbc).symm, hab⟩
    exact forbidden Z U W hZ hU hW (fun h ↦ hUZ h.symm) hUW hWZ hc hm

theorem rawLineSystemHasNoTriangle_of_isSparse
    {A N : Type} [Fintype N] (S : Finset (Line A N)) (hS : IsSparse S) :
    RawLineSystemHasNoTriangle (S : Set (Line A N)) := by
  classical
  intro U W Z hU hW hZ hraw
  apply hS.2
  rcases hraw with ⟨hUW, hUZ, hWZ, hUWmeet, hUZmeet, hWZmeet, hcommon⟩
  have meet {L M : Line A N} (h : RawLinesIntersect L M) :
      (linePoints L ∩ linePoints M).Nonempty := by
    rcases h with ⟨a, b, hab⟩
    exact ⟨L a, ⟨a, rfl⟩, ⟨b, hab.symm⟩⟩
  have hempty : linePoints U ∩ linePoints W ∩ linePoints Z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    rcases hq with ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ⟨c, hc⟩⟩
    apply hcommon
    exact ⟨a, b, c, ha.trans hb.symm, hb.trans hc.symm⟩
  have hZUmeet : RawLinesIntersect Z U := by
    rcases hUZmeet with ⟨a, b, hab⟩
    exact ⟨b, a, hab.symm⟩
  exact ⟨U, hU, W, hW, Z, hZ, hUW, hWZ, (fun h ↦ hUZ h.symm),
    meet hUWmeet, meet hWZmeet, meet hZUmeet, hempty⟩

/-! ## The concrete one-fiber extension, parameterized only by confinement -/

/-- Expanding a cube word over the music fiber into coordinate blocks. -/
def expandFiberWord (source : Picture G P C) (x : V) {N : Type*}
    (w : N → Fiber source x) : N × C → Alphabet :=
  fun sc ↦ source.embed (w sc.1).1 sc.2

/-- On a selected outer line, block expansion is exactly `extendWord` of a
fiber point. -/
theorem expandFiberWord_line (source : Picture G P C) (x : V) {N : Type*}
    (U : Line (Fiber source x) N) (a : Fiber source x) :
    expandFiberWord source x (U a) = extendWord source x U a.1 := by
  funext sc
  simp only [expandFiberWord, extendWord]
  cases hs : U.idxFun sc.1 with
  | none => simp [Line.coe_apply, sectionPoint, hs]
  | some f => simp [Line.coe_apply, sectionPoint, hs]

/-- Build the actual raw partite amalgamation from one concrete sparse line
system.  The difficult incidence theorem appears only as `hconf`; every other
field of `FiberExtension` is discharged here. -/
noncomputable def rawFiberExtensionOfSystem
    [Fintype P] [Fintype C] [Fintype K] [Nonempty K]
    {N : Type} [Fintype N]
    (picture : Picture G P C) (x : V)
    (sourceFiberNontrivial : ∀ y : V, Nontrivial (Fiber picture y))
    (S : Finset (Line (Fiber picture x) N))
    (hramsey : IsRamseyFamily S K)
    (hconf : EveryQuasilineConfined picture
      (rawAmalgamationData picture x (S : Set (Line (Fiber picture x) N)))) :
    FiberExtension picture x K := by
  classical
  let lineSet : Set (Line (Fiber picture x) N) := S
  let data := rawAmalgamationData picture x lineSet
  let target := amalgamationPicture picture data (by simpa [data, lineSet] using hconf)
  letI : Fintype (RawAmalgamPoint picture x lineSet) := Fintype.ofFinite _
  letI : Fintype (N × C) := inferInstance
  letI : Inhabited K :=
    Classical.inhabited_of_nonempty (inferInstance : Nonempty K)
  have hcopy (U : Line (Fiber picture x) N) (hU : U ∈ S) :
      StandardCopy picture target (standardCopy picture x lineSet U (by simpa [lineSet] using hU)) := by
    refine {
      injective := standardCopy_injective picture x lineSet U _
      proj_copy := ?_
      transports_lines := ?_
    }
    · intro p
      change rawProj picture x lineSet
        (standardCopy picture x lineSet U _ p) = picture.proj p
      exact rawProj_standardCopy picture x lineSet U
        (by simpa [lineSet] using hU) p
    · intro l hl
      change IsCombinatorialLine (rawEmbed picture x lineSet)
        (fun a ↦ standardCopy picture x lineSet U _ (l a))
      exact standardCopy_transports_line picture x lineSet U
        (by simpa [lineSet] using hU) l hl
  have hSne : S.Nonempty := by
    obtain ⟨U, hUS, -⟩ := hramsey (fun _ ↦ default)
    exact ⟨U, hUS⟩
  refine {
    Point := RawAmalgamPoint picture x lineSet
    Coord := N × C
    pointFintype := inferInstance
    coordFintype := inferInstance
    target := target
    targetFiberNontrivial := ?_
    focus := ?_
  }
  · obtain ⟨U₀, hU₀⟩ := hSne
    intro y
    exact (hcopy U₀ hU₀).targetFiberNontrivial sourceFiberNontrivial y
  · intro color
    let cubeColor : (N → Fiber picture x) → K := fun w ↦
      if hw : IsAmalgamWord picture x lineSet (expandFiberWord picture x w)
      then color ⟨expandFiberWord picture x w, hw⟩
      else default
    obtain ⟨U, hUS, k, hk⟩ := hramsey cubeColor
    have hUS' : U ∈ lineSet := by simpa [lineSet] using hUS
    refine ⟨standardCopy picture x lineSet U hUS', hcopy U hUS, k, ?_⟩
    intro p hp
    let a : Fiber picture x := ⟨p, hp⟩
    have hw : IsAmalgamWord picture x lineSet
        (expandFiberWord picture x (U a)) := by
      exact ⟨U, hUS', a.1, expandFiberWord_line picture x U a⟩
    have hpoint :
        (⟨expandFiberWord picture x (U a), hw⟩ :
          RawAmalgamPoint picture x lineSet) =
          standardCopy picture x lineSet U hUS' p := by
      apply Subtype.ext
      exact expandFiberWord_line picture x U a
    have hmono := hk a
    simpa only [cubeColor, dif_pos hw, hpoint] using hmono

/-- Once a confinement theorem is available uniformly for sparse systems,
the sparse Hales--Jewett theorem and the raw constructor produce a one-fiber
extension.  The result is first built under `Nonempty` because the sparse
theorem is proposition-valued. -/
theorem oneFiberExtensionOfConfinement_nonempty
    [Fintype P] [Fintype C] [Fintype K] [Nonempty K]
    (picture : Picture G P C) (x : V)
    [Nontrivial (Fiber picture x)]
    (sourceFiberNontrivial : ∀ y : V, Nontrivial (Fiber picture y))
    (confinement : ∀ {N : Type} [Fintype N]
      (S : Finset (Line (Fiber picture x) N)), IsSparse S →
        EveryQuasilineConfined picture
          (rawAmalgamationData picture x (S : Set (Line (Fiber picture x) N)))) :
    Nonempty (FiberExtension picture x K) := by
  classical
  rcases sparse_hales_jewett (Fiber picture x) K with
    ⟨N, hN, S, hsparse, hramsey⟩
  letI : Fintype N := hN
  exact ⟨rawFiberExtensionOfSystem picture x sourceFiberNontrivial S hramsey
    (confinement S hsparse)⟩

/-- Chosen one-fiber extension supplied by sparse Hales--Jewett and a uniform
confinement theorem. -/
noncomputable def oneFiberExtensionOfConfinement
    [Fintype P] [Fintype C] [Fintype K] [Nonempty K]
    (picture : Picture G P C) (x : V)
    [Nontrivial (Fiber picture x)]
    (sourceFiberNontrivial : ∀ y : V, Nontrivial (Fiber picture y))
    (confinement : ∀ {N : Type} [Fintype N]
      (S : Finset (Line (Fiber picture x) N)), IsSparse S →
        EveryQuasilineConfined picture
          (rawAmalgamationData picture x (S : Set (Line (Fiber picture x) N)))) :
    FiberExtension picture x K :=
  Classical.choice <| oneFiberExtensionOfConfinement_nonempty picture x
    sourceFiberNontrivial confinement

/-- The actual one-fiber step used by the finite iteration.  The abstract
family parameter is the certificate consumed by the focusing API; the raw
amalgamation selects a concrete sparse Hales--Jewett system and confines it
using linearity of the base together with the sparse tripod/triangle
exclusions. -/
noncomputable def oneFiberAmalgamate
    [Fintype P] [Fintype C] [Fintype K] [Nonempty K]
    (hlinear : G.Linear)
    (picture : Picture G P C)
    (sourceFiberNontrivial : ∀ y : V, Nontrivial (Fiber picture y))
    (x : V) [Nontrivial (Fiber picture x)]
    (_lines : SparseFiberLineFamily picture x K) :
    FiberExtension picture x K :=
  oneFiberExtensionOfConfinement picture x sourceFiberNontrivial <| by
    intro N _ S hS
    exact raw_everyQuasilineConfined_of_sparse_linear picture x
      (S : Set (Line (Fiber picture x) N)) hlinear
      (rawLineSystemHasNoTripod_of_isSparse S hS)
      (rawLineSystemHasNoTriangle_of_isSparse S hS)

/-- Uniform choice of the abstract sparse family required by the iterator. -/
noncomputable def sparseFamily
    [Fintype P] [Fintype C] [Fintype K]
    (picture : Picture G P C) (x : V)
    [Nontrivial (Fiber picture x)] :
    SparseFiberLineFamily picture x K :=
  sparseFiberLineFamilyOf picture x K
    (sparse_hales_jewett (Fiber picture x) K)

/-! ## Initial-picture finite and fiber instances -/

/-! ## Complete finite RRS block -/

/-- For every positive finite color count there is a finite integer block
which is Ramsey for nontrivial three-term arithmetic progressions, while
every subset has a three-AP-free subset of at least one third its size. -/
theorem exists_finite_rrs_block (r : ℕ) (hr : 0 < r) :
    ∃ X : Finset ℕ,
      X.Nonempty ∧
      (∀ color : ℕ → Fin r,
        ∃ a ∈ X, ∃ b ∈ X, ∃ c ∈ X,
          a + c = b + b ∧ a ≠ c ∧
          color a = color b ∧ color b = color c) ∧
      (∀ Y : Finset ℕ, Y ⊆ X →
        ∃ Z : Finset ℕ, Z ⊆ Y ∧
          (Z.card : ℝ) ≥ (1 / 3 : ℝ) * Y.card ∧
          ThreeAPFree (Z : Set ℕ)) := by
  classical
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨N, hN, hRamsey, hFractional, hlinear⟩ :=
    Erdos847TriangleAdapter.exists_triangleBase_package r
  let base := Erdos847TriangleAdapter.triangleGraph N
  let source := Erdos847TriangleAdapter.doubledPictureZero base
  have hsourceFibers : ∀ x : Erdos847TriangleAdapter.Vertex N,
      Nontrivial (Fiber source x) := by
    intro x
    exact Erdos847TriangleAdapter.doubledTrianglePicture_fiber_nontrivial hN x
  have hrealizes : RealizesEveryEdge source := by
    exact Erdos847TriangleAdapter.doubledPictureZero_realizesEveryEdge base
  obtain ⟨Q, D, hQ, hD, final, hfinalFibers, hfinalRamsey⟩ :=
    exists_ramsey_final_picture source (Fin r) hsourceFibers hrealizes hRamsey
      (fun picture x ↦ sparseFamily picture x)
      (fun picture sourceFibers x _ lines ↦
        oneFiberAmalgamate hlinear picture sourceFibers x lines)
  letI : Fintype Q := hQ
  letI : Fintype D := hD
  exact Erdos847PictureOutput.exists_encoded_block_one_third_of_finite_coords
    final hr hfinalRamsey hFractional

end Erdos847FinitePipeline

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/Assembly.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Assembly of separated finite blocks for Erdős 847

This file isolates the elementary infinitary assembly step.  The genuinely
combinatorial input is a sequence of finite blocks with a Ramsey property and
a hereditary positive-density independent-set property.  We translate those
blocks far apart, so that no three-term progression can use two blocks.
-/

namespace Erdos847Assembly

open Set
open scoped Pointwise

attribute [local instance] Classical.propDecidable

/-- A nonconstant monochromatic three-term arithmetic progression. -/
def HasMonochromaticThreeAP (A : Set ℕ) {r : ℕ} (color : ℕ → Fin r) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
    a + c = b + b ∧ a ≠ c ∧ color a = color b ∧ color b = color c

/-- Every nonempty finite coloring contains a monochromatic three-AP. -/
def RamseyForThreeAP (A : Set ℕ) : Prop :=
  ∀ r : ℕ, 0 < r → ∀ color : ℕ → Fin r, HasMonochromaticThreeAP A color

/-- The pair of global properties needed for the negative answer. -/
def IsRRSCounterexample (A : Set ℕ) (mu : ℝ) : Prop :=
  RamseyForThreeAP A ∧
    ∀ B : Set ℕ, B ⊆ A → B.Finite →
      ∃ C : Set ℕ, C ⊆ B ∧ C.ncard ≥ mu * B.ncard ∧ ThreeAPFree C

/-- The largest entry of a finite block (zero for the empty block). -/
def blockMax (X : ℕ → Finset ℕ) (n : ℕ) : ℕ := (X n).sup id

/-- `cap X n` is an upper bound for all translated blocks with index `< n`. -/
def cap (X : ℕ → Finset ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * cap X n + 2 * blockMax X n + 1

/-- Translation used for block `n`.  The extra `blockMax` term prevents a
progression with two points in the new block and one point in the old union. -/
def offset (X : ℕ → Finset ℕ) (n : ℕ) : ℕ :=
  2 * cap X n + blockMax X n + 1

/-- Translate a finite subset of the `n`-th raw block. -/
def translate (X : ℕ → Finset ℕ) (n : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image fun x => offset X n + x

/-- The translated `n`-th block. -/
def placed (X : ℕ → Finset ℕ) (n : ℕ) : Finset ℕ := translate X n (X n)

/-- The infinite union of the translated blocks. -/
def assembled (X : ℕ → Finset ℕ) : Set ℕ := ⋃ n, (placed X n : Set ℕ)

lemma le_blockMax {X : ℕ → Finset ℕ} {n x : ℕ} (hx : x ∈ X n) : x ≤ blockMax X n := by
  exact Finset.le_sup (f := id) hx

lemma cap_step (X : ℕ → Finset ℕ) (n : ℕ) :
    cap X (n + 1) = 2 * cap X n + 2 * blockMax X n + 1 := by
  rfl

lemma cap_le_succ (X : ℕ → Finset ℕ) (n : ℕ) : cap X n ≤ cap X (n + 1) := by
  rw [cap_step]
  omega

lemma cap_mono (X : ℕ → Finset ℕ) : Monotone (cap X) :=
  monotone_nat_of_le_succ (cap_le_succ X)

lemma offset_separated (X : ℕ → Finset ℕ) (n : ℕ) :
    2 * cap X n + blockMax X n < offset X n := by
  simp [offset]

lemma mem_translate_iff {X : ℕ → Finset ℕ} {n : ℕ} {S : Finset ℕ} {y : ℕ} :
    y ∈ translate X n S ↔ ∃ x ∈ S, offset X n + x = y := by
  simp [translate]

lemma translate_lower {X : ℕ → Finset ℕ} {n : ℕ} {S : Finset ℕ} {y : ℕ}
    (hy : y ∈ translate X n S) : offset X n ≤ y := by
  obtain ⟨x, hx, rfl⟩ := mem_translate_iff.mp hy
  omega

lemma translate_upper {X : ℕ → Finset ℕ} {n : ℕ} {S : Finset ℕ} {y : ℕ}
    (hSX : S ⊆ X n) (hy : y ∈ translate X n S) : y ≤ cap X (n + 1) := by
  obtain ⟨x, hx, rfl⟩ := mem_translate_iff.mp hy
  have hxmax := le_blockMax (hSX hx)
  simp only [offset, cap_step]
  omega

lemma translate_upper_short {X : ℕ → Finset ℕ} {n : ℕ} {S : Finset ℕ} {y : ℕ}
    (hSX : S ⊆ X n) (hy : y ∈ translate X n S) :
    y ≤ offset X n + blockMax X n := by
  obtain ⟨x, hx, rfl⟩ := mem_translate_iff.mp hy
  have hxmax := le_blockMax (hSX hx)
  omega

lemma translate_injective (X : ℕ → Finset ℕ) (n : ℕ) :
    Function.Injective (fun x : ℕ => offset X n + x) := by
  intro a b h
  exact Nat.add_left_cancel h

@[simp] lemma card_translate (X : ℕ → Finset ℕ) (n : ℕ) (S : Finset ℕ) :
    (translate X n S).card = S.card := by
  exact Finset.card_image_of_injective S (translate_injective X n)

lemma threeAPFree_translate {X : ℕ → Finset ℕ} {n : ℕ} {S : Finset ℕ}
    (hS : ThreeAPFree (S : Set ℕ)) : ThreeAPFree (translate X n S : Set ℕ) := by
  rw [threeAPFree_iff_eq_right] at hS ⊢
  intro a ha b hb c hc habc
  obtain ⟨a', ha', rfl⟩ := mem_translate_iff.mp ha
  obtain ⟨b', hb', rfl⟩ := mem_translate_iff.mp hb
  obtain ⟨c', hc', rfl⟩ := mem_translate_iff.mp hc
  congr 1
  apply hS ha' hb' hc'
  omega

/-- Two 3-AP-free finite sets remain 3-AP-free when the second lies in an
interval `[L,L+M]` and the first below `U`, provided `L > 2U+M`. -/
lemma threeAPFree_union_of_separated {S T : Finset ℕ} {U M L : ℕ}
    (hS : ThreeAPFree (S : Set ℕ)) (hT : ThreeAPFree (T : Set ℕ))
    (hSupper : ∀ x ∈ S, x ≤ U)
    (hTlower : ∀ x ∈ T, L ≤ x)
    (hTupper : ∀ x ∈ T, x ≤ L + M)
    (hsep : 2 * U + M < L) :
    ThreeAPFree ((S ∪ T : Finset ℕ) : Set ℕ) := by
  rw [threeAPFree_iff_eq_right] at hS hT ⊢
  intro a ha b hb c hc habc
  simp only [Finset.mem_coe, Finset.mem_union] at ha hb hc
  rcases ha with haS | haT <;> rcases hb with hbS | hbT <;> rcases hc with hcS | hcT
  · exact hS haS hbS hcS habc
  · have haU := hSupper a haS
    have hbU := hSupper b hbS
    have hcL := hTlower c hcT
    omega
  · have haU := hSupper a haS
    have hbL := hTlower b hbT
    have hcU := hSupper c hcS
    omega
  · have haU := hSupper a haS
    have hbL := hTlower b hbT
    have hcL := hTlower c hcT
    have hcTop := hTupper c hcT
    omega
  · have haL := hTlower a haT
    have hbU := hSupper b hbS
    have hcU := hSupper c hcS
    omega
  · have haL := hTlower a haT
    have haTop := hTupper a haT
    have hbU := hSupper b hbS
    have hcL := hTlower c hcT
    omega
  · have haL := hTlower a haT
    have haTop := hTupper a haT
    have hbL := hTlower b hbT
    have hcU := hSupper c hcS
    omega
  · exact hT haT hbT hcT habc

/-- Union of the first `n` translated finite subsets. -/
def blockPrefix (X D : ℕ → Finset ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.range n).biUnion fun i => translate X i (D i)

lemma blockPrefix_succ (X D : ℕ → Finset ℕ) (n : ℕ) :
    blockPrefix X D (n + 1) = translate X n (D n) ∪ blockPrefix X D n := by
  simp [blockPrefix, Finset.range_add_one]

lemma blockPrefix_upper {X D : ℕ → Finset ℕ} (hDX : ∀ i, D i ⊆ X i) {n y : ℕ}
    (hy : y ∈ blockPrefix X D n) : y ≤ cap X n := by
  obtain ⟨i, hi, hyi⟩ := Finset.mem_biUnion.mp hy
  have hi' : i + 1 ≤ n := by simpa using (Finset.mem_range.mp hi)
  exact (translate_upper (hDX i) hyi).trans (cap_mono X hi')

lemma disjoint_translate_of_lt {X D : ℕ → Finset ℕ} (hDX : ∀ i, D i ⊆ X i)
    {i j : ℕ} (hij : i < j) : Disjoint (translate X i (D i)) (translate X j (D j)) := by
  rw [Finset.disjoint_left]
  intro y hyi hyj
  have hycap : y ≤ cap X j :=
    (translate_upper (hDX i) hyi).trans (cap_mono X (by omega))
  have hyoff : offset X j ≤ y := translate_lower hyj
  have hsep := offset_separated X j
  omega

lemma pairwiseDisjoint_translate {X D : ℕ → Finset ℕ} (hDX : ∀ i, D i ⊆ X i)
    (s : Finset ℕ) : (s : Set ℕ).PairwiseDisjoint fun i => translate X i (D i) := by
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · exact disjoint_translate_of_lt hDX hij'
  · exact (disjoint_translate_of_lt hDX hji').symm

/-- Every finite prefix of translated 3-AP-free subsets is still 3-AP-free. -/
lemma threeAPFree_blockPrefix {X D : ℕ → Finset ℕ} (hDX : ∀ i, D i ⊆ X i)
    (hDfree : ∀ i, ThreeAPFree (D i : Set ℕ)) :
    ∀ n, ThreeAPFree (blockPrefix X D n : Set ℕ) := by
  intro n
  induction n with
  | zero => simp [blockPrefix]
  | succ n ih =>
      rw [blockPrefix_succ]
      rw [Finset.union_comm]
      apply threeAPFree_union_of_separated (U := cap X n) (M := blockMax X n)
        (L := offset X n) ih (threeAPFree_translate (hDfree n))
      · intro y hy
        exact blockPrefix_upper hDX hy
      · intro y hy
        exact translate_lower hy
      · intro y hy
        exact translate_upper_short (hDX n) hy
      ·
        exact offset_separated X n

/-- Union of a subset chosen from every translated block. -/
def assembledSubsets (X D : ℕ → Finset ℕ) : Set ℕ :=
  ⋃ n, (translate X n (D n) : Set ℕ)

lemma mem_assembledSubsets_iff {X D : ℕ → Finset ℕ} {y : ℕ} :
    y ∈ assembledSubsets X D ↔ ∃ n, y ∈ translate X n (D n) := by
  simp [assembledSubsets]

lemma mem_blockPrefix_of_mem_translate {X D : ℕ → Finset ℕ} {i n y : ℕ}
    (hi : i < n) (hy : y ∈ translate X i (D i)) : y ∈ blockPrefix X D n := by
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hy⟩

/-- Arbitrary (not necessarily finite) unions of blockwise 3-AP-free choices
are 3-AP-free, because any three points lie in one finite prefix. -/
lemma threeAPFree_assembledSubsets {X D : ℕ → Finset ℕ} (hDX : ∀ i, D i ⊆ X i)
    (hDfree : ∀ i, ThreeAPFree (D i : Set ℕ)) :
    ThreeAPFree (assembledSubsets X D) := by
  rw [threeAPFree_iff_eq_right]
  intro a ha b hb c hc habc
  obtain ⟨ia, ha⟩ := mem_assembledSubsets_iff.mp ha
  obtain ⟨ib, hb⟩ := mem_assembledSubsets_iff.mp hb
  obtain ⟨ic, hc⟩ := mem_assembledSubsets_iff.mp hc
  let n := max ia (max ib ic) + 1
  apply (threeAPFree_iff_eq_right.mp (threeAPFree_blockPrefix hDX hDfree n))
    (mem_blockPrefix_of_mem_translate (by simp [n]) ha)
    (mem_blockPrefix_of_mem_translate (by simp [n]) hb)
    (mem_blockPrefix_of_mem_translate (by simp [n]) hc)
    habc

/-- Finite-block Ramsey input.  Only the block with index `r` is used against
an `r`-coloring. -/
def BlockRamsey (X : ℕ → Finset ℕ) : Prop :=
  ∀ r : ℕ, ∀ color : ℕ → Fin r, HasMonochromaticThreeAP (X r : Set ℕ) color

/-- Hereditary density input on every raw block. -/
def BlockDense (X : ℕ → Finset ℕ) (mu : ℝ) : Prop :=
  ∀ i : ℕ, ∀ B : Finset ℕ, B ⊆ X i →
    ∃ C : Finset ℕ, C ⊆ B ∧ (C.card : ℝ) ≥ mu * B.card ∧
      ThreeAPFree (C : Set ℕ)

/-- A monochromatic progression in raw block `r` translates to one in the
assembled set. -/
lemma ramseyForThreeAP_assembled {X : ℕ → Finset ℕ} (hRamsey : BlockRamsey X) :
    RamseyForThreeAP (assembled X) := by
  intro r hr color
  obtain ⟨a, ha, b, hb, c, hc, habc, hac, hab, hbc⟩ :=
    hRamsey r (fun x => color (offset X r + x))
  refine ⟨offset X r + a, ?_, offset X r + b, ?_, offset X r + c, ?_, ?_, ?_, hab, hbc⟩
  · exact Set.mem_iUnion.mpr ⟨r, mem_translate_iff.mpr ⟨a, ha, rfl⟩⟩
  · exact Set.mem_iUnion.mpr ⟨r, mem_translate_iff.mpr ⟨b, hb, rfl⟩⟩
  · exact Set.mem_iUnion.mpr ⟨r, mem_translate_iff.mpr ⟨c, hc, rfl⟩⟩
  · omega
  · intro h
    exact hac (Nat.add_left_cancel h)

lemma index_le_cap (X : ℕ → Finset ℕ) : ∀ n, n ≤ cap X n := by
  intro n
  induction n with
  | zero => simp [cap]
  | succ n ih =>
      rw [cap_step]
      omega

lemma cap_lt_offset (X : ℕ → Finset ℕ) (n : ℕ) : cap X n < offset X n := by
  have := offset_separated X n
  omega

lemma assembled_unbounded {X : ℕ → Finset ℕ} (hXne : ∀ i, (X i).Nonempty) (N : ℕ) :
    ∃ y ∈ assembled X, N < y := by
  obtain ⟨x, hx⟩ := hXne (N + 1)
  refine ⟨offset X (N + 1) + x, ?_, ?_⟩
  · exact Set.mem_iUnion.mpr ⟨N + 1, mem_translate_iff.mpr ⟨x, hx, rfl⟩⟩
  · have hcap := index_le_cap X (N + 1)
    have hoff := cap_lt_offset X (N + 1)
    omega

lemma assembled_infinite {X : ℕ → Finset ℕ} (hXne : ∀ i, (X i).Nonempty) :
    (assembled X).Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := hfin.exists_le
  obtain ⟨y, hy, hNy⟩ := assembled_unbounded hXne N
  exact (not_lt_of_ge (hN y hy)) hNy

/-- The hereditary density property survives assembly.  A finite `B` meets
only finitely many translated blocks; extract in every raw fiber and add the
cardinality inequalities, using disjointness of the translated intervals. -/
lemma dense_assembled {X : ℕ → Finset ℕ} {mu : ℝ} (hDense : BlockDense X mu) :
    ∀ B : Set ℕ, B ⊆ assembled X → B.Finite →
      ∃ C : Set ℕ, C ⊆ B ∧ C.ncard ≥ mu * B.ncard ∧ ThreeAPFree C := by
  intro B hBA hBfin
  let BF : Finset ℕ := hBfin.toFinset
  have hBcover : B ⊆ ⋃ i, (placed X i : Set ℕ) := by
    simpa [assembled] using hBA
  obtain ⟨I, hIfin, hBI⟩ := finite_subset_iUnion hBfin hBcover
  let IF : Finset ℕ := hIfin.toFinset
  let P : ℕ → Finset ℕ := fun i =>
    (X i).filter fun x => offset X i + x ∈ BF
  have hPX : ∀ i, P i ⊆ X i := by
    intro i x hx
    exact (Finset.mem_filter.mp hx).1
  have hBFunion : BF = IF.biUnion fun i => translate X i (P i) := by
    ext y
    constructor
    · intro hy
      have hyB : y ∈ B := by simpa [BF] using hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hBI hyB)
      obtain ⟨hiI, hyplace⟩ := Set.mem_iUnion.mp hi
      change y ∈ translate X i (X i) at hyplace
      obtain ⟨x, hx, rfl⟩ := mem_translate_iff.mp hyplace
      apply Finset.mem_biUnion.mpr
      refine ⟨i, ?_, mem_translate_iff.mpr ⟨x, ?_, rfl⟩⟩
      · simpa [IF] using hiI
      · exact Finset.mem_filter.mpr ⟨hx, hy⟩
    · intro hy
      obtain ⟨i, hiI, hyi⟩ := Finset.mem_biUnion.mp hy
      obtain ⟨x, hx, rfl⟩ := mem_translate_iff.mp hyi
      exact (Finset.mem_filter.mp hx).2
  have hBcard : BF.card = ∑ i ∈ IF, (P i).card := by
    calc
      BF.card = (IF.biUnion fun i => translate X i (P i)).card :=
        congrArg Finset.card hBFunion
      _ = ∑ i ∈ IF, (translate X i (P i)).card :=
        Finset.card_biUnion (pairwiseDisjoint_translate hPX IF)
      _ = ∑ i ∈ IF, (P i).card := by simp
  let D : ℕ → Finset ℕ := fun i => Classical.choose (hDense i (P i) (hPX i))
  have hDspec (i : ℕ) :
      D i ⊆ P i ∧ (D i).card ≥ mu * (P i).card ∧ ThreeAPFree (D i : Set ℕ) := by
    exact Classical.choose_spec (hDense i (P i) (hPX i))
  have hDP : ∀ i, D i ⊆ P i := fun i => (hDspec i).1
  have hDX : ∀ i, D i ⊆ X i := fun i => (hDP i).trans (hPX i)
  have hDcard : ∀ i, (D i).card ≥ mu * (P i).card := fun i => (hDspec i).2.1
  have hDfree : ∀ i, ThreeAPFree (D i : Set ℕ) := fun i => (hDspec i).2.2
  let CF : Finset ℕ := IF.biUnion fun i => translate X i (D i)
  have hCFsubset : CF ⊆ BF := by
    intro y hy
    obtain ⟨i, hiI, hyi⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨x, hx, rfl⟩ := mem_translate_iff.mp hyi
    exact (Finset.mem_filter.mp (hDP i hx)).2
  have hCcard : CF.card = ∑ i ∈ IF, (D i).card := by
    calc
      CF.card = (IF.biUnion fun i => translate X i (D i)).card := rfl
      _ = ∑ i ∈ IF, (translate X i (D i)).card :=
        Finset.card_biUnion (pairwiseDisjoint_translate hDX IF)
      _ = ∑ i ∈ IF, (D i).card := by simp
  have hsum :
      ∑ i ∈ IF, mu * ((P i).card : ℝ) ≤ ∑ i ∈ IF, ((D i).card : ℝ) := by
    exact Finset.sum_le_sum fun i hi => hDcard i
  have hcardineq : (CF.card : ℝ) ≥ mu * (BF.card : ℝ) := by
    rw [hCcard, hBcard]
    simp only [Nat.cast_sum, Finset.mul_sum]
    exact hsum
  have hCFfree : ThreeAPFree (CF : Set ℕ) := by
    apply (threeAPFree_assembledSubsets hDX hDfree).mono
    intro y hy
    obtain ⟨i, hiI, hyi⟩ := Finset.mem_biUnion.mp hy
    exact mem_assembledSubsets_iff.mpr ⟨i, hyi⟩
  refine ⟨(CF : Set ℕ), ?_, ?_, hCFfree⟩
  · intro y hy
    have : y ∈ BF := hCFsubset hy
    simpa [BF] using this
  · simpa [BF, Set.ncard_eq_toFinset_card B hBfin] using hcardineq

/-- Complete elementary assembly theorem. -/
theorem isRRSCounterexample_assembled {X : ℕ → Finset ℕ} {mu : ℝ}
    (hRamsey : BlockRamsey X) (hDense : BlockDense X mu) :
    IsRRSCounterexample (assembled X) mu := by
  exact ⟨ramseyForThreeAP_assembled hRamsey, dense_assembled hDense⟩

/-- Nonempty finite blocks therefore give an infinite global counterexample. -/
theorem infinite_and_isRRSCounterexample_assembled {X : ℕ → Finset ℕ} {mu : ℝ}
    (hXne : ∀ i, (X i).Nonempty) (hRamsey : BlockRamsey X) (hDense : BlockDense X mu) :
    (assembled X).Infinite ∧ IsRRSCounterexample (assembled X) mu := by
  exact ⟨assembled_infinite hXne, isRRSCounterexample_assembled hRamsey hDense⟩

theorem exists_infinite_isRRSCounterexample {X : ℕ → Finset ℕ} {mu : ℝ}
    (hXne : ∀ i, (X i).Nonempty) (hRamsey : BlockRamsey X) (hDense : BlockDense X mu) :
    ∃ A : Set ℕ, A.Infinite ∧ IsRRSCounterexample A mu := by
  exact ⟨assembled X, infinite_and_isRRSCounterexample_assembled hXne hRamsey hDense⟩

end Erdos847Assembly

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/FinalAssembly.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Passing from finite Erdős 847 blocks to the infinite counterexample

This is the last purely logical adapter in the construction.  Its hypothesis
is exactly the finite-block conclusion produced by the picture construction.
-/

namespace Erdos847FinalAssembly

open Erdos847Assembly

attribute [local instance] Classical.propDecidable

/-- The finite conclusion needed from the RRS picture construction. -/
def IsGoodBlock (r : ℕ) (X : Finset ℕ) : Prop :=
  X.Nonempty ∧
    (∀ color : ℕ → Fin r, HasMonochromaticThreeAP (X : Set ℕ) color) ∧
    (∀ B : Finset ℕ, B ⊆ X →
      ∃ C : Finset ℕ, C ⊆ B ∧
        (C.card : ℝ) ≥ (1 / 3 : ℝ) * B.card ∧
        ThreeAPFree (C : Set ℕ))

/-- Good finite blocks for every positive number of colours assemble to an
infinite set having the two RRS properties. -/
theorem exists_infinite_counterexample_of_good_blocks
    (hblocks : ∀ r : ℕ, 0 < r → ∃ X : Finset ℕ, IsGoodBlock r X) :
    ∃ A : Set ℕ, A.Infinite ∧
      Erdos847Assembly.IsRRSCounterexample A (1 / 3 : ℝ) := by
  let block : ℕ → Finset ℕ := fun i ↦
    Classical.choose (hblocks (i + 1) (by omega))
  have hspec (i : ℕ) : IsGoodBlock (i + 1) (block i) := by
    exact Classical.choose_spec (hblocks (i + 1) (by omega))
  have hne : ∀ i, (block i).Nonempty := fun i ↦ (hspec i).1
  have hramsey : BlockRamsey block := by
    intro r color
    by_cases hr : 0 < r
    · obtain ⟨a, ha, b, hb, c, hc, habc, hac, hab, hbc⟩ :=
        (hspec r).2.1 (fun n ↦ (color n).castSucc)
      refine ⟨a, ha, b, hb, c, hc, habc, hac, ?_, ?_⟩
      · exact Fin.castSucc_injective r hab
      · exact Fin.castSucc_injective r hbc
    · have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
      subst r
      exact Fin.elim0 (color 0)
  have hdense : BlockDense block (1 / 3 : ℝ) := by
    intro i B hB
    exact (hspec i).2.2 B hB
  exact exists_infinite_isRRSCounterexample hne hramsey hdense

end Erdos847FinalAssembly

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847/Construction.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The constructed counterexample for Erdős 847

This module joins the finite RRS block theorem to the separated-block
assembly.  The resulting set has hereditary one-third 3-AP-free subsets and
is Ramsey for a three-term arithmetic progression under every finite
coloring.
-/

namespace Erdos847Construction

/-- The complete RRS counterexample, with the convenient constant `1/3`. -/
theorem exists_counterexample :
    ∃ A : Set ℕ, A.Infinite ∧
      Erdos847Assembly.IsRRSCounterexample A (1 / 3 : ℝ) := by
  apply Erdos847FinalAssembly.exists_infinite_counterexample_of_good_blocks
  intro r hr
  obtain ⟨X, hne, hramsey, hdense⟩ :=
    Erdos847FinitePipeline.exists_finite_rrs_block r hr
  exact ⟨X, hne, hramsey, hdense⟩

end Erdos847Construction

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos847.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 847.
https://www.erdosproblems.com/forum/thread/847

Informal authors:
- Christian Reiher
- Vojtěch Rödl
- Marcelo Sales

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos847.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/847.lean
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Erdős Problem 847

The negative solution is due to Christian Reiher, Vojtěch Rödl, and Marcelo Sales,
*Colouring versus density in integers and Hales--Jewett cubes* (2024).

The detailed mathematical proof and its Leanization map are in `tex/847.tex`.
-/

open Set

attribute [local instance] Classical.propDecidable

/-- `HasFew3APs A` is the local positive-proportion hypothesis in the upstream statement. -/
def HasFew3APs (A : Set ℕ) : Prop :=
  ∃ ε : ℝ, ε > 0 ∧ ∀ B : Set ℕ, B ⊆ A → Finite B →
    ∃ C : Set ℕ, C ⊆ B ∧ C.ncard ≥ ε * B.ncard ∧ ThreeAPFree C

/-- A nonconstant monochromatic three-term arithmetic progression for a coloring of `A`. -/
def HasMonochromaticThreeAP (A : Set ℕ) {r : ℕ} (color : ℕ → Fin r) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
    a + c = b + b ∧ a ≠ c ∧ color a = color b ∧ color b = color c

/-- Every coloring of `A` by a nonempty finite palette has a monochromatic three-AP. -/
def RamseyForThreeAP (A : Set ℕ) : Prop :=
  ∀ r : ℕ, 0 < r → ∀ color : ℕ → Fin r, HasMonochromaticThreeAP A color

/-- The two properties supplied by the Reiher--Rödl--Sales counterexample. -/
def IsRRSCounterexample (A : Set ℕ) (μ : ℝ) : Prop :=
  RamseyForThreeAP A ∧
    ∀ B : Set ℕ, B ⊆ A → Finite B →
      ∃ C : Set ℕ, C ⊆ B ∧ C.ncard ≥ μ * B.ncard ∧ ThreeAPFree C

lemma hasFew3APs_of_isRRSCounterexample {A : Set ℕ} {μ : ℝ} (hμ : 0 < μ)
    (hA : IsRRSCounterexample A μ) : HasFew3APs A := by
  exact ⟨μ, hμ, hA.2⟩

/-- A finite cover by three-AP-free sets gives a finite coloring with no monochromatic three-AP. -/
lemma not_finite_threeAPFree_cover {A : Set ℕ} [Infinite A]
    (hRamsey : RamseyForThreeAP A) :
    ¬ ∃ n, ∃ S : Fin n → Set ℕ,
      (∀ i, ThreeAPFree (S i)) ∧ A = ⋃ i : Fin n, S i := by
  rintro ⟨n, S, hfree, hcover⟩
  have hn : 0 < n := by
    by_contra hnpos
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnpos
    subst n
    have hAempty : A = ∅ := by simpa using hcover
    have hAfin : A.Finite := by simp [hAempty]
    exact (Set.infinite_coe_iff.mp (inferInstance : Infinite A)) hAfin
  have hindex : ∀ x ∈ A, ∃ i : Fin n, x ∈ S i := by
    intro x hx
    rw [hcover] at hx
    exact Set.mem_iUnion.mp hx
  let color : ℕ → Fin n := fun x =>
    if hx : x ∈ A then Classical.choose (hindex x hx) else ⟨0, hn⟩
  have color_mem : ∀ {x : ℕ}, x ∈ A → x ∈ S (color x) := by
    intro x hx
    simp only [color, dif_pos hx]
    exact Classical.choose_spec (hindex x hx)
  obtain ⟨a, ha, b, hb, c, hc, habc, hac, hab, hbc⟩ := hRamsey n hn color
  have haS : a ∈ S (color a) := color_mem ha
  have hbS : b ∈ S (color a) := by simpa [hab] using color_mem hb
  have hcS : c ∈ S (color a) := by simpa [hab, hbc] using color_mem hc
  have := (threeAPFree_iff_eq_right.mp (hfree (color a))) haS hbS hcS habc
  exact hac this

/-- Once the RRS set has been constructed, it refutes the literal upstream universal statement. -/
lemma negative_answer_of_counterexample {A : Set ℕ} [Infinite A] {μ : ℝ} (hμ : 0 < μ)
    (hA : IsRRSCounterexample A μ) :
    ¬ (∀ X : Set ℕ, Infinite X → HasFew3APs X →
      ∃ n, ∃ S : Fin n → Set ℕ,
        (∀ i, ThreeAPFree (S i)) ∧ X = ⋃ i : Fin n, S i) := by
  intro h
  exact not_finite_threeAPFree_cover hA.1
    (h A (inferInstance : Infinite A) (hasFew3APs_of_isRRSCounterexample hμ hA))

/-- Erdős Problem 847 has a negative answer.  The witness is the separated
union of the finite RRS blocks constructed above the sparse Hales--Jewett
line systems. -/
theorem erdos_847 :
    ¬ ∀ A : Set ℕ, Infinite A → HasFew3APs A →
      ∃ n, ∃ S : Fin n → Set ℕ,
        (∀ i, ThreeAPFree (S i)) ∧ A = ⋃ i : Fin n, S i := by
  intro hcover
  obtain ⟨A, hAinfinite, hA⟩ :=
    Erdos847Construction.exists_counterexample
  letI : Infinite A := Set.infinite_coe_iff.mpr hAinfinite
  have hA' : IsRRSCounterexample A (1 / 3 : ℝ) := by
    exact hA
  exact (negative_answer_of_counterexample (by norm_num) hA') hcover

end

#print axioms erdos_847
-- 'Erdos847.erdos_847' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos847
