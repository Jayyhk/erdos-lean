import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos113

/-
# Problem Description

Erdős Problem 113 ($500), conjectured by Erdős and Simonovits: if `G` is bipartite then
`ex(n; G) ≪ n^(3/2)` if and only if `G` is 2-degenerate, i.e. `G` contains no induced
subgraph of minimum degree at least 3. `erdos_113` proves this is false.

Disproved by Janzer. The witness is a 3-regular bipartite graph with
`ex(n; H) ≪ n^(31/21)`. Since `31/21 ≈ 1.476 < 3/2`, it satisfies the `n^(3/2)` bound, yet
being 3-regular it has no vertex of degree at most two and so is not 2-degenerate — which
breaks the "only if" direction.

`HasThreeHalvesExtremalBound H` is `extremalNumber n H =O[atTop] n ^ (3/2 : ℝ)`, and
`IsTwoDegenerate G` is `∀ S : Set V, S.Nonempty → ∃ v : S, (G.neighborSet v ∩ S).ncard ≤ 2`,
which is exactly "every nonempty induced subgraph has a vertex of degree at most two".
-/

universe u

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Conflict.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Conflict

noncomputable def walkCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) (u v : W) : ℕ :=
  Fintype.card {p : A.Walk u v // p.length = m}

noncomputable def closedWalkCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) : ℕ :=
  ∑ x : W, walkCount A m x x

lemma closedWalkCount_cast_eq_trace {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) :
    (closedWalkCount A m : ℝ) = Matrix.trace (A.adjMatrix ℝ ^ m) := by
  rw [closedWalkCount, Nat.cast_sum, Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.diag_apply, A.adjMatrix_pow_apply_eq_card_walk]
  rfl

lemma closedWalkCount_cast_eq_sum_walkCount_sq {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) :
    (closedWalkCount A (2 * m) : ℝ) =
      ∑ u : W, ∑ v : W, (walkCount A m u v : ℝ) ^ 2 := by
  rw [closedWalkCount_cast_eq_trace]
  have hpow : A.adjMatrix ℝ ^ (2 * m) =
      A.adjMatrix ℝ ^ m * A.adjMatrix ℝ ^ m := by
    rw [show 2 * m = m + m by omega, pow_add]
  rw [hpow, Matrix.trace]
  apply Finset.sum_congr rfl
  intro u _
  rw [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro v _
  rw [A.adjMatrix_pow_apply_eq_card_walk,
    A.adjMatrix_pow_apply_eq_card_walk]
  have hrev : walkCount A m v u = walkCount A m u v := by
    unfold walkCount
    apply Fintype.card_congr
    exact
      { toFun := fun p ↦ ⟨p.1.reverse, by simpa using p.2⟩
        invFun := fun p ↦ ⟨p.1.reverse, by simpa using p.2⟩
        left_inv := by intro p; apply Subtype.ext; simp
        right_inv := by intro p; apply Subtype.ext; simp }
  change (walkCount A m u v : ℝ) * (walkCount A m v u : ℝ) = _
  rw [hrev]
  ring

abbrev FixedWalk {W : Type*} (A : SimpleGraph W) (m : ℕ) (u v : W) :=
  {p : A.Walk u v // p.length = m}

def WalkConflict784 {W : Type*} {A : SimpleGraph W}
    (R : W → W → Prop) (x : W) {z y : W} (q : FixedWalk A 784 y z) : Prop :=
  ∃ i : Fin 49, ∃ j : Fin 16,
    R x (q.1.getVert (16 * i.val + j.val))

noncomputable instance instDecidableWalkConflict784 {W : Type*} {A : SimpleGraph W}
    (R : W → W → Prop) [DecidableRel R] (x : W) {z y : W}
    (q : FixedWalk A 784 y z) : Decidable (WalkConflict784 R x q) :=
  Classical.propDecidable _

noncomputable def walkConflictingNeighbors784 {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    {z y : W} (q : FixedWalk A 784 y z) : Finset W := by
  classical
  exact (A.neighborFinset y).filter fun x ↦ WalkConflict784 R x q

@[simp] lemma mem_walkConflictingNeighbors784 {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    {z y : W} (q : FixedWalk A 784 y z) (x : W) :
    x ∈ walkConflictingNeighbors784 A R q ↔
      A.Adj y x ∧ WalkConflict784 R x q := by
  classical
  simp [walkConflictingNeighbors784]

lemma card_lowFixedWalks_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (t : ℝ) (ht : 0 ≤ t)
    (z x₁ : W) (x₂ : A.neighborSet x₁) :
    (Fintype.card {q : FixedWalk A 784 x₂.1 z //
      (walkCount A 784 x₂.1 z : ℝ) <
        t * (walkCount A 783 z x₁ : ℝ)} : ℝ) ≤
      t * (walkCount A 783 z x₁ : ℝ) := by
  let T := {q : FixedWalk A 784 x₂.1 z //
    (walkCount A 784 x₂.1 z : ℝ) <
      t * (walkCount A 783 z x₁ : ℝ)}
  have hnonneg : 0 ≤ t * (walkCount A 783 z x₁ : ℝ) :=
    mul_nonneg ht (by positivity)
  cases isEmpty_or_nonempty T with
  | inl hempty =>
      have hcard : Fintype.card T = 0 := Fintype.card_eq_zero
      rw [hcard, Nat.cast_zero]
      exact hnonneg
  | inr hnonempty =>
      let q : T := Classical.choice hnonempty
      calc
        (Fintype.card T : ℝ) ≤
            (Fintype.card (FixedWalk A 784 x₂.1 z) : ℝ) := by
          exact_mod_cast Fintype.card_subtype_le (fun _q : FixedWalk A 784 x₂.1 z ↦
            (walkCount A 784 x₂.1 z : ℝ) <
              t * (walkCount A 783 z x₁ : ℝ))
        _ = (walkCount A 784 x₂.1 z : ℝ) := rfl
        _ ≤ t * (walkCount A 783 z x₁ : ℝ) := q.2.le

lemma card_highFixedWalks_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (t : ℝ) (ht : 0 < t)
    (z x₂ : W) (q : FixedWalk A 784 x₂ z)
    (x₁ : ↑(walkConflictingNeighbors784 A R q)) :
    (Fintype.card {p : FixedWalk A 783 z x₁.1 //
      t * (walkCount A 783 z x₁.1 : ℝ) ≤
        (walkCount A 784 x₂ z : ℝ)} : ℝ) ≤
      t⁻¹ * (walkCount A 784 x₂ z : ℝ) := by
  let T := {p : FixedWalk A 783 z x₁.1 //
    t * (walkCount A 783 z x₁.1 : ℝ) ≤
      (walkCount A 784 x₂ z : ℝ)}
  have hnonneg : 0 ≤ t⁻¹ * (walkCount A 784 x₂ z : ℝ) :=
    mul_nonneg (inv_nonneg.mpr ht.le) (by positivity)
  cases isEmpty_or_nonempty T with
  | inl hempty =>
      have hcard : Fintype.card T = 0 := Fintype.card_eq_zero
      rw [hcard, Nat.cast_zero]
      exact hnonneg
  | inr hnonempty =>
      let p : T := Classical.choice hnonempty
      calc
        (Fintype.card T : ℝ) ≤
            (Fintype.card (FixedWalk A 783 z x₁.1) : ℝ) := by
          exact_mod_cast Fintype.card_subtype_le (fun _p : FixedWalk A 783 z x₁.1 ↦
            t * (walkCount A 783 z x₁.1 : ℝ) ≤
              (walkCount A 784 x₂ z : ℝ))
        _ = (walkCount A 783 z x₁.1 : ℝ) := rfl
        _ ≤ t⁻¹ * (walkCount A 784 x₂ z : ℝ) := by
          rw [inv_mul_eq_div]
          exact (le_div_iff₀' ht).2 p.2

abbrev RawHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] :=
  Σ z : W, Σ x₁ : W,
    FixedWalk A 783 z x₁ ×
      Σ x₂ : A.neighborSet x₁, FixedWalk A 784 x₂.1 z

abbrev BadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :=
  {b : RawHalfCycle A // WalkConflict784 R b.2.1 b.2.2.2.2}

def eraseBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :
    BadHalfCycle A R → RawHalfCycle A
  | b => b.1

lemma eraseBadHalfCycle_injective {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :
    Function.Injective (eraseBadHalfCycle A R) := by
  exact Subtype.val_injective

end Conflict

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/WalkFin.lean` -/

section
open scoped SimpleGraph

namespace WF

def walkOfFin {W : Type*} {A : SimpleGraph W} :
    ∀ (n : ℕ) (f : Fin (n + 1) → W),
      (∀ i : Fin n, A.Adj (f i.castSucc) (f i.succ)) →
        A.Walk (f ⟨0, Nat.zero_lt_succ n⟩) (f ⟨n, Nat.lt_succ_self n⟩)
  | 0, f, _ => .nil
  | n + 1, f, h => by
      let g : Fin (n + 1) → W := fun i ↦ f i.succ
      have hg : ∀ i : Fin n, A.Adj (g i.castSucc) (g i.succ) := by
        intro i
        exact h i.succ
      exact (walkOfFin n g hg).cons (h ⟨0, Nat.zero_lt_succ n⟩)

@[simp] lemma walkOfFin_length {W : Type*} {A : SimpleGraph W}
    (n : ℕ) (f : Fin (n + 1) → W)
    (h : ∀ i : Fin n, A.Adj (f i.castSucc) (f i.succ)) :
    (walkOfFin n f h).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [walkOfFin, SimpleGraph.Walk.length_cons]
      rw [ih]

lemma walkOfFin_getVert {W : Type*} {A : SimpleGraph W}
    (n : ℕ) (f : Fin (n + 1) → W)
    (h : ∀ i : Fin n, A.Adj (f i.castSucc) (f i.succ))
    (i : ℕ) (hi : i ≤ n) :
    (walkOfFin n f h).getVert i = f ⟨i, Nat.lt_succ_iff.mpr hi⟩ := by
  induction n generalizing i with
  | zero =>
      have : i = 0 := by omega
      subst i
      simp [walkOfFin]
  | succ n ih =>
      by_cases hi0 : i = 0
      · subst i
        simp [walkOfFin]
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        simp only [walkOfFin, SimpleGraph.Walk.getVert_cons_succ]
        exact ih (fun k : Fin (n + 1) ↦ f k.succ)
          (fun k : Fin n ↦ h k.succ) j (by omega)

end WF

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Encode.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Encode

open Conflict WF

def cyclicAdd1568 (i : Fin 1568) (d : Nat) : Fin 1568 :=
  ⟨(i.val + d) % 1568, Nat.mod_lt _ (by omega)⟩

lemma cyclicAdd1568_zero (i : Fin 1568) : cyclicAdd1568 i 0 = i := by
  apply Fin.ext
  simp [cyclicAdd1568, Nat.mod_eq_of_lt i.isLt]

lemma cyclicAdd1568_add (i : Fin 1568) (a b : Nat) :
    cyclicAdd1568 (cyclicAdd1568 i a) b = cyclicAdd1568 i (a + b) := by
  apply Fin.ext
  simp only [cyclicAdd1568]
  omega

lemma cyclicAdd1568_full (i : Fin 1568) : cyclicAdd1568 i 1568 = i := by
  apply Fin.ext
  change (i.val + 1568) % 1568 = i.val
  omega

lemma exists_short_oriented_pair (i j : Fin 1568) (hij : i ≠ j) :
    ∃ c : Fin 1568, ∃ d : Fin 784,
      cyclicAdd1568 c (d.val + 1) = j ∧ c = i ∨
      cyclicAdd1568 c (d.val + 1) = i ∧ c = j := by
  by_cases hijv : i.val < j.val
  · let e := j.val - i.val
    by_cases he : e ≤ 784
    · refine ⟨i, ⟨e - 1, by dsimp [e]; omega⟩, Or.inl ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd1568, e]
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    · let e' := 1568 - e
      refine ⟨j, ⟨e' - 1, by dsimp [e', e]; omega⟩, Or.inr ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd1568, e', e]
      omega
  · have hjiv : j.val < i.val := by
      have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
      omega
    let e := i.val - j.val
    by_cases he : e ≤ 784
    · refine ⟨j, ⟨e - 1, by dsimp [e]; omega⟩, Or.inr ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd1568, e]
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    · let e' := 1568 - e
      refine ⟨i, ⟨e' - 1, by dsimp [e', e]; omega⟩, Or.inl ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd1568, e', e]
      omega

abbrev ClosedWalk1568 {W : Type*} (A : SimpleGraph W) :=
  Σ x : W, {p : A.Walk x x // p.length = 1568}

def cv {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (i : Fin 1568) : W :=
  P.2.1.getVert i.val

lemma cv_adj_add_one {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (i : Fin 1568) :
    A.Adj (cv P i) (cv P (cyclicAdd1568 i 1)) := by
  have hi : i.val < P.2.1.length := by rw [P.2.2]; exact i.isLt
  have hadj := P.2.1.adj_getVert_succ hi
  by_cases hwrap : i.val + 1 < 1568
  · simpa [cv, cyclicAdd1568, Nat.mod_eq_of_lt hwrap] using hadj
  · have hilast : i.val = 1567 := by omega
    have hend : P.2.1.getVert 1568 = P.1 := by
      simpa only [P.2.2] using P.2.1.getVert_length
    have hstart : P.2.1.getVert 0 = P.1 := P.2.1.getVert_zero
    simpa [cv, cyclicAdd1568, hilast, hend, hstart] using hadj

def qSeq {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) (r : Fin 785) : W :=
  cv P (cyclicAdd1568 c (r.val + 1))

lemma qSeq_adj {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) (r : Fin 784) :
    A.Adj (qSeq P c r.castSucc) (qSeq P c r.succ) := by
  have h := cv_adj_add_one P (cyclicAdd1568 c (r.val + 1))
  simpa only [qSeq, Fin.val_castSucc, Fin.val_succ, cyclicAdd1568_add,
    show r.val + 1 + 1 = r.val + 2 by omega] using h

def qWalk {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) :
    A.Walk (qSeq P c ⟨0, by omega⟩) (qSeq P c ⟨784, by omega⟩) :=
  walkOfFin 784 (qSeq P c) (qSeq_adj P c)

@[simp] lemma qWalk_length {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) : (qWalk P c).length = 784 := by
  exact walkOfFin_length 784 (qSeq P c) (qSeq_adj P c)

lemma qWalk_getVert {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) (i : Nat) (hi : i ≤ 784) :
    (qWalk P c).getVert i = cv P (cyclicAdd1568 c (i + 1)) := by
  simp only [qWalk]
  exact walkOfFin_getVert 784 (qSeq P c) (qSeq_adj P c) i hi

def pSeq {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) (r : Fin 784) : W :=
  cv P (cyclicAdd1568 c (785 + r.val))

lemma pSeq_adj {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) (r : Fin 783) :
    A.Adj (pSeq P c r.castSucc) (pSeq P c r.succ) := by
  have h := cv_adj_add_one P (cyclicAdd1568 c (785 + r.val))
  simpa only [pSeq, Fin.val_castSucc, Fin.val_succ, cyclicAdd1568_add,
    show 785 + r.val + 1 = 785 + (r.val + 1) by omega] using h

def pWalk {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) :
    A.Walk (pSeq P c ⟨0, by omega⟩) (pSeq P c ⟨783, by omega⟩) :=
  walkOfFin 783 (pSeq P c) (pSeq_adj P c)

@[simp] lemma pWalk_length {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) : (pWalk P c).length = 783 := by
  exact walkOfFin_length 783 (pSeq P c) (pSeq_adj P c)

lemma pWalk_getVert {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) (i : Nat) (hi : i ≤ 783) :
    (pWalk P c).getVert i = cv P (cyclicAdd1568 c (785 + i)) := by
  simp only [pWalk]
  exact walkOfFin_getVert 783 (pSeq P c) (pSeq_adj P c) i hi

noncomputable def makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk1568 A) (c : Fin 1568) (d : Fin 784)
    (hR : R (cv P c) (cv P (cyclicAdd1568 c (d.val + 1)))) :
    BadHalfCycle A R := by
  let z := qSeq P c ⟨784, by omega⟩
  let x₁ := pSeq P c ⟨783, by omega⟩
  let p : FixedWalk A 783 z x₁ :=
    ⟨(pWalk P c).copy (by simp [z, qSeq, pSeq]) rfl, by
      rw [SimpleGraph.Walk.length_copy, pWalk_length]⟩
  let x₂ : A.neighborSet x₁ := ⟨qSeq P c ⟨0, by omega⟩, by
    have h := cv_adj_add_one P c
    simpa [x₁, qSeq, pSeq, cyclicAdd1568_full] using h⟩
  let q : FixedWalk A 784 x₂.1 z := ⟨qWalk P c, qWalk_length P c⟩
  refine ⟨⟨z, x₁, p, x₂, q⟩, ?_⟩
  let i : Fin 49 := ⟨d.val / 16, by omega⟩
  let j : Fin 16 := ⟨d.val % 16, Nat.mod_lt _ (by omega)⟩
  refine ⟨i, j, ?_⟩
  have hd : 16 * i.val + j.val = d.val := by
    dsimp [i, j]
    omega
  have hq := qWalk_getVert P c d.val (Nat.le_of_lt d.isLt)
  dsimp [x₁, q]
  rw [hd, hq]
  simpa [pSeq, cyclicAdd1568_full] using hR

def cyclicOffset1568 (c i : Fin 1568) : Nat :=
  (i.val + 1568 - c.val) % 1568

lemma cyclicAdd_offset (c i : Fin 1568) :
    cyclicAdd1568 c (cyclicOffset1568 c i) = i := by
  apply Fin.ext
  simp only [cyclicAdd1568, cyclicOffset1568]
  omega

abbrev PackedWalk {W : Type*} (A : SimpleGraph W) :=
  Σ u : W, Σ v : W, A.Walk u v

def packedWalkVertex {W : Type*} {A : SimpleGraph W}
    (p : PackedWalk A) (i : Nat) : W := p.2.2.getVert i

def packedQ {W : Type*} [Fintype W] [DecidableEq W]
    {A : SimpleGraph W} [DecidableRel A.Adj]
    {R : W → W → Prop} [DecidableRel R]
    (b : BadHalfCycle A R) : PackedWalk A :=
  ⟨b.1.2.2.2.1.1, b.1.1, b.1.2.2.2.2.1⟩

def packedP {W : Type*} [Fintype W] [DecidableEq W]
    {A : SimpleGraph W} [DecidableRel A.Adj]
    {R : W → W → Prop} [DecidableRel R]
    (b : BadHalfCycle A R) : PackedWalk A :=
  ⟨b.1.1, b.1.2.1, b.1.2.2.1.1⟩

def decodeHalfVertex {W : Type*} [Fintype W] [DecidableEq W]
    {A : SimpleGraph W} [DecidableRel A.Adj]
    {R : W → W → Prop} [DecidableRel R]
    (c : Fin 1568) (b : BadHalfCycle A R)
    (i : Fin 1568) : W :=
  let d := cyclicOffset1568 c i
  if d = 0 then b.1.2.1
  else if d ≤ 785 then packedWalkVertex (packedQ b) (d - 1)
  else packedWalkVertex (packedP b) (d - 785)

@[simp] lemma makeBadHalfCycle_x1 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk1568 A) (c : Fin 1568) (d : Fin 784)
    (hR : R (cv P c) (cv P (cyclicAdd1568 c (d.val + 1)))) :
    (makeBadHalfCycle A R P c d hR).1.2.1 = pSeq P c ⟨783, by omega⟩ := by
  rfl

@[simp] lemma packedQ_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk1568 A) (c : Fin 1568) (d : Fin 784)
    (hR : R (cv P c) (cv P (cyclicAdd1568 c (d.val + 1)))) :
    packedQ (makeBadHalfCycle A R P c d hR) =
      ⟨qSeq P c ⟨0, by omega⟩, qSeq P c ⟨784, by omega⟩, qWalk P c⟩ := by
  rfl

@[simp] lemma packedP_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk1568 A) (c : Fin 1568) (d : Fin 784)
    (hR : R (cv P c) (cv P (cyclicAdd1568 c (d.val + 1)))) :
    packedP (makeBadHalfCycle A R P c d hR) =
      ⟨qSeq P c ⟨784, by omega⟩, pSeq P c ⟨783, by omega⟩,
        (pWalk P c).copy (by simp [qSeq, pSeq]) rfl⟩ := by
  rfl

lemma packedP_makeBadHalfCycle_getVert {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk1568 A) (c : Fin 1568) (d : Fin 784)
    (hR : R (cv P c) (cv P (cyclicAdd1568 c (d.val + 1)))) (i : Nat) :
    packedWalkVertex (packedP (makeBadHalfCycle A R P c d hR)) i =
      (pWalk P c).getVert i := by
  unfold packedWalkVertex packedP
  dsimp [makeBadHalfCycle]
  simp only [SimpleGraph.Walk.getVert_copy]

lemma decode_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk1568 A) (c : Fin 1568) (d : Fin 784)
    (hR : R (cv P c) (cv P (cyclicAdd1568 c (d.val + 1))))
    (i : Fin 1568) :
    decodeHalfVertex c (makeBadHalfCycle A R P c d hR) i = cv P i := by
  let e := cyclicOffset1568 c i
  have he_lt : e < 1568 := Nat.mod_lt _ (by omega)
  by_cases he0 : e = 0
  · have hi : i = c := by
      have := cyclicAdd_offset c i
      symm
      simpa [e, he0, cyclicAdd1568_zero] using this
    subst i
    simp [decodeHalfVertex, e, he0, pSeq,
      cyclicAdd1568_full]
  · by_cases he785 : e ≤ 785
    · have hq := qWalk_getVert P c (e - 1) (by omega)
      have hadd : cyclicAdd1568 c ((e - 1) + 1) = i := by
        rw [show e - 1 + 1 = e by omega]
        exact cyclicAdd_offset c i
      dsimp [e] at he0 he785 hq hadd ⊢
      simp only [decodeHalfVertex, he0, ↓reduceIte, he785]
      rw [packedQ_makeBadHalfCycle A R P c d hR]
      simp only [packedWalkVertex]
      rw [hq, hadd]
    · have hp := pWalk_getVert P c (e - 785) (by omega)
      have hadd : cyclicAdd1568 c (785 + (e - 785)) = i := by
        rw [show 785 + (e - 785) = e by omega]
        exact cyclicAdd_offset c i
      dsimp [e] at he0 he785 hp hadd ⊢
      simp only [decodeHalfVertex, he0, ↓reduceIte, he785]
      rw [packedP_makeBadHalfCycle_getVert A R P c d hR, hp, hadd]

lemma closedWalk1568_ext {W : Type*} {A : SimpleGraph W}
    (P Q : ClosedWalk1568 A) (h : ∀ i, cv P i = cv Q i) : P = Q := by
  rcases P with ⟨x, p, hp⟩
  rcases Q with ⟨y, q, hq⟩
  have hxy : x = y := by
    have h0 := h ⟨0, by omega⟩
    simpa [cv] using h0
  subst y
  have hpq : p = q := by
    apply SimpleGraph.Walk.ext_getVert
    intro k
    by_cases hk : k < 1568
    · simpa [cv] using h ⟨k, hk⟩
    · rw [p.getVert_of_length_le (by omega), q.getVert_of_length_le (by omega)]
  subst q
  rfl

abbrev BadClosedWalk1568 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :=
  {P : ClosedWalk1568 A // ∃ i j, i ≠ j ∧ R (cv P i) (cv P j)}

lemma exists_orientedConflict1568 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) (b : BadClosedWalk1568 A R) :
    ∃ c : Fin 1568, ∃ d : Fin 784,
      R (cv b.1 c) (cv b.1 (cyclicAdd1568 c (d.val + 1))) := by
  rcases b.2 with ⟨i, j, hij, hR⟩
  rcases exists_short_oriented_pair i j hij with ⟨c, d, h | h⟩
  · refine ⟨c, d, ?_⟩
    rw [h.1, h.2]
    exact hR
  · refine ⟨c, d, ?_⟩
    rw [h.1, h.2]
    exact hsymm _ _ hR

noncomputable def orientedConflict1568 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) (b : BadClosedWalk1568 A R) :
    Σ c : Fin 1568, {d : Fin 784 //
      R (cv b.1 c) (cv b.1 (cyclicAdd1568 c (d.val + 1)))} := by
  let c := Classical.choose (exists_orientedConflict1568 A R hsymm b)
  let d := Classical.choose (Classical.choose_spec
    (exists_orientedConflict1568 A R hsymm b))
  exact ⟨c, d, Classical.choose_spec (Classical.choose_spec
    (exists_orientedConflict1568 A R hsymm b))⟩

noncomputable def encodeBadClosedWalk1568 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    BadClosedWalk1568 A R → Fin 1568 × BadHalfCycle A R := fun b ↦
  let w := orientedConflict1568 A R hsymm b
  ⟨w.1, makeBadHalfCycle A R b.1 w.1 w.2.1 w.2.2⟩

lemma encodeBadClosedWalk1568_injective {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    Function.Injective (encodeBadClosedWalk1568 A R hsymm) := by
  intro b b' hbb'
  apply Subtype.ext
  apply closedWalk1568_ext
  intro i
  have hdecode := congrArg (fun z : Fin 1568 × BadHalfCycle A R ↦
    decodeHalfVertex z.1 z.2 i) hbb'
  simpa only [encodeBadClosedWalk1568, decode_makeBadHalfCycle] using hdecode

lemma card_BadClosedWalk1568_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    Fintype.card (BadClosedWalk1568 A R) ≤
      1568 * Fintype.card (BadHalfCycle A R) := by
  calc
    Fintype.card (BadClosedWalk1568 A R) ≤
        Fintype.card (Fin 1568 × BadHalfCycle A R) :=
      Fintype.card_le_of_injective _ (encodeBadClosedWalk1568_injective A R hsymm)
    _ = 1568 * Fintype.card (BadHalfCycle A R) := by simp

end Encode

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Moments.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Lower

noncomputable def walkMass {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) (x : W) : ℝ :=
  ∑ y : W, (Conflict.walkCount A m x y : ℝ)

lemma walkMass_eq_matrix_sum {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) (x : W) :
    walkMass A m x = ∑ y : W, (A.adjMatrix ℝ ^ m) x y := by
  unfold walkMass
  apply Finset.sum_congr rfl
  intro y _
  rw [A.adjMatrix_pow_apply_eq_card_walk]
  rfl

@[simp] lemma walkMass_zero {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (x : W) :
    walkMass A 0 x = 1 := by
  rw [walkMass_eq_matrix_sum]
  simp [Matrix.one_apply]

lemma walkMass_succ {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) (x : W) :
    walkMass A (m + 1) x = ∑ y ∈ A.neighborFinset x, walkMass A m y := by
  classical
  rw [walkMass_eq_matrix_sum]
  simp_rw [pow_succ']
  simp only [Matrix.mul_apply]
  calc
    (∑ z, ∑ y, A.adjMatrix ℝ x y * (A.adjMatrix ℝ ^ m) y z) =
        ∑ y, ∑ z, A.adjMatrix ℝ x y * (A.adjMatrix ℝ ^ m) y z :=
      Finset.sum_comm
    _ = ∑ y, if A.Adj x y then walkMass A m y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.mul_sum, ← walkMass_eq_matrix_sum]
      simp only [SimpleGraph.adjMatrix_apply]
      split_ifs <;> simp
    _ = ∑ y ∈ A.neighborFinset x, walkMass A m y := by
      rw [← Finset.sum_filter]
      congr 1
      ext y
      simp

lemma walkMass_lower {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (d : ℝ)
    (hd : 0 ≤ d) (hdeg : ∀ x, d ≤ (A.degree x : ℝ)) (m : ℕ) (x : W) :
    d ^ m ≤ walkMass A m x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      rw [show m + 1 = Nat.succ m by omega, pow_succ, walkMass_succ]
      calc
        d ^ m * d ≤ d ^ m * (A.degree x : ℝ) := by
          apply mul_le_mul_of_nonneg_left (hdeg x)
          positivity
        _ = ∑ _y ∈ A.neighborFinset x, d ^ m := by
          simp [SimpleGraph.card_neighborFinset_eq_degree]
          ring
        _ ≤ ∑ y ∈ A.neighborFinset x, walkMass A m y := by
          apply Finset.sum_le_sum
          intro y _
          exact ih y

lemma closedWalkCount_lower_of_minDegree {W : Type*} [Fintype W]
    [DecidableEq W] [Nonempty W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (d : ℝ)
    (hd : 0 ≤ d) (hdeg : ∀ x, d ≤ (A.degree x : ℝ)) (m : ℕ) :
    d ^ (2 * m) ≤ (Conflict.closedWalkCount A (2 * m) : ℝ) := by
  let n : ℝ := Fintype.card W
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos
  have hmass_nonneg (x : W) : 0 ≤ walkMass A m x := by
    unfold walkMass
    positivity
  have hmass (x : W) : d ^ m ≤ walkMass A m x :=
    walkMass_lower A d hd hdeg m x
  have hsumlower : n * d ^ (2 * m) ≤ ∑ x : W, (walkMass A m x) ^ 2 := by
    rw [show d ^ (2 * m) = (d ^ m) ^ 2 by ring]
    calc
      n * (d ^ m) ^ 2 = ∑ _x : W, (d ^ m) ^ 2 := by
        simp [n]
      _ ≤ ∑ x : W, (walkMass A m x) ^ 2 := by
        apply Finset.sum_le_sum
        intro x _
        exact (sq_le_sq₀ (by positivity) (hmass_nonneg x)).2 (hmass x)
  have hcs : (∑ x : W, (walkMass A m x) ^ 2) ≤
      n * (Conflict.closedWalkCount A (2 * m) : ℝ) := by
    rw [Conflict.closedWalkCount_cast_eq_sum_walkCount_sq]
    calc
      (∑ x : W, (walkMass A m x) ^ 2) ≤
          ∑ x : W, n * ∑ y : W, (Conflict.walkCount A m x y : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro x _
        simpa only [walkMass, n, Finset.card_univ, Nat.cast_ofNat] using
          (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset W))
            (f := fun y ↦ (Conflict.walkCount A m x y : ℝ)))
      _ = n * ∑ x : W, ∑ y : W,
          (Conflict.walkCount A m x y : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
  have hmul : n * d ^ (2 * m) ≤
      n * (Conflict.closedWalkCount A (2 * m) : ℝ) := hsumlower.trans hcs
  exact (mul_le_mul_iff_right₀ hn).mp hmul

end Lower

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/ConflictSides.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Erdos113Sides

open Conflict

abbrev LowHalfCycleSide {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (b : Bool) (t : ℝ) :=
  Σ z : W, Σ x₁ : {x : W // side x = b},
    FixedWalk A 783 z x₁.1 ×
      Σ x₂ : A.neighborSet x₁.1,
        {q : FixedWalk A 784 x₂.1 z //
          (walkCount A 784 x₂.1 z : ℝ) <
            t * (walkCount A 783 z x₁.1 : ℝ)}

abbrev HighBadHalfCycleSide {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (b : Bool) (t : ℝ) :=
  Σ z : W, Σ x₂ : {x : W // side x = !b},
    Σ q : FixedWalk A 784 x₂.1 z,
      Σ x₁ : {x : ↑(walkConflictingNeighbors784 A R q) // side x.1 = b},
        {p : FixedWalk A 783 z x₁.1.1 //
          t * (walkCount A 783 z x₁.1.1 : ℝ) ≤
            (walkCount A 784 x₂.1 z : ℝ)}

lemma card_LowHalfCycleSide_cast {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (b : Bool) (t : ℝ) :
    (Fintype.card (LowHalfCycleSide A side b t) : ℝ) =
      ∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 783 z x₁.1 : ℝ) *
          ∑ x₂ : A.neighborSet x₁.1,
            (Fintype.card {q : FixedWalk A 784 x₂.1 z //
              (walkCount A 784 x₂.1 z : ℝ) <
                t * (walkCount A 783 z x₁.1 : ℝ)} : ℝ) := by
  simp only [LowHalfCycleSide, Fintype.card_sigma, Fintype.card_prod,
    Nat.cast_sum, Nat.cast_mul]
  rfl

lemma card_LowHalfCycleSide_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (b : Bool) (t D : ℝ) (ht : 0 ≤ t) (hD : 0 ≤ D)
    (hdegree : ∀ x, side x = b → (A.degree x : ℝ) ≤ D) :
    (Fintype.card (LowHalfCycleSide A side b t) : ℝ) ≤
      D * t * (closedWalkCount A 1566 : ℝ) := by
  rw [card_LowHalfCycleSide_cast]
  calc
    (∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 783 z x₁.1 : ℝ) *
          ∑ x₂ : A.neighborSet x₁.1,
            (Fintype.card {q : FixedWalk A 784 x₂.1 z //
              (walkCount A 784 x₂.1 z : ℝ) <
                t * (walkCount A 783 z x₁.1 : ℝ)} : ℝ)) ≤
      ∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 783 z x₁.1 : ℝ) *
          (D * (t * (walkCount A 783 z x₁.1 : ℝ))) := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro x₁ _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        (∑ x₂ : A.neighborSet x₁.1,
            (Fintype.card {q : FixedWalk A 784 x₂.1 z //
              (walkCount A 784 x₂.1 z : ℝ) <
                t * (walkCount A 783 z x₁.1 : ℝ)} : ℝ)) ≤
            ∑ _x₂ : A.neighborSet x₁.1,
              t * (walkCount A 783 z x₁.1 : ℝ) := by
          apply Finset.sum_le_sum
          intro x₂ _
          exact card_lowFixedWalks_le A t ht z x₁.1 x₂
        _ = (A.degree x₁.1 : ℝ) *
              (t * (walkCount A 783 z x₁.1 : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            SimpleGraph.card_neighborSet_eq_degree, Nat.cast_mul]
        _ ≤ D * (t * (walkCount A 783 z x₁.1 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right (hdegree x₁.1 x₁.2)
            (mul_nonneg ht (by positivity))
    _ = D * t * (∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 783 z x₁.1 : ℝ) ^ 2) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x₁ _
      ring
    _ ≤ D * t * (∑ z : W, ∑ x₁ : W,
        (walkCount A 783 z x₁ : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD ht)
      apply Finset.sum_le_sum
      intro z _
      rw [← Finset.sum_subtype (Finset.univ.filter fun x : W ↦ side x = b)
        (by simp) (fun x ↦ (walkCount A 783 z x : ℝ) ^ 2)]
      apply Finset.sum_le_sum_of_subset_of_nonneg (by simp)
      intro x _ _
      positivity
    _ = D * t * (closedWalkCount A 1566 : ℝ) := by
      rw [show 1566 = 2 * 783 by norm_num,
        closedWalkCount_cast_eq_sum_walkCount_sq]

lemma card_walkConflictingNeighbors784_le_at {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (s : ℝ)
    (hsymm : ∀ x y, R x y → R y x)
    {z y : W} (q : FixedWalk A 784 y z)
    (hlocal : ∀ u,
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s) :
    ((walkConflictingNeighbors784 A R q).card : ℝ) ≤ 784 * s := by
  classical
  let E (i : Fin 49) (j : Fin 16) :=
    (A.neighborFinset y).filter (R (q.1.getVert (16 * i.val + j.val)))
  let U := Finset.univ.biUnion fun i : Fin 49 ↦ Finset.univ.biUnion (E i)
  have hsubset : walkConflictingNeighbors784 A R q ⊆ U := by
    intro x hx
    rw [walkConflictingNeighbors784, Finset.mem_filter] at hx
    have hconf := hx.2
    change ∃ i : Fin 49, ∃ j : Fin 16,
      R x (q.1.getVert (16 * i.val + j.val)) at hconf
    obtain ⟨i, j, hi⟩ := hconf
    simp only [U, Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ _, j, Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr ⟨hx.1, hsymm _ _ hi⟩
  calc
    ((walkConflictingNeighbors784 A R q).card : ℝ) ≤ (U.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ i : Fin 49, ∑ j : Fin 16, ((E i j).card : ℝ) := by
      calc
        (U.card : ℝ) ≤
            ∑ i : Fin 49, (((Finset.univ.biUnion (E i)).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ i : Fin 49, ∑ j : Fin 16, ((E i j).card : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin 49, ∑ _j : Fin 16, s := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact hlocal _
    _ = 784 * s := by simp; ring

lemma card_HighBadHalfCycleSide_cast {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (b : Bool) (t : ℝ) :
    (Fintype.card (HighBadHalfCycleSide A R side b t) : ℝ) =
      ∑ z : W, ∑ x₂ : {x : W // side x = !b},
        ∑ q : FixedWalk A 784 x₂.1 z,
          ∑ x₁ : {x : ↑(walkConflictingNeighbors784 A R q) // side x.1 = b},
            (Fintype.card {p : FixedWalk A 783 z x₁.1.1 //
              t * (walkCount A 783 z x₁.1.1 : ℝ) ≤
                (walkCount A 784 x₂.1 z : ℝ)} : ℝ) := by
  simp only [HighBadHalfCycleSide, Fintype.card_sigma, Nat.cast_sum]

lemma card_HighBadHalfCycleSide_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (b : Bool) (t s : ℝ)
    (ht : 0 < t) (hs : 0 ≤ s)
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y, side y = !b →
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s) :
    (Fintype.card (HighBadHalfCycleSide A R side b t) : ℝ) ≤
      784 * s * t⁻¹ * (closedWalkCount A 1568 : ℝ) := by
  rw [card_HighBadHalfCycleSide_cast]
  calc
    (∑ z : W, ∑ x₂ : {x : W // side x = !b},
        ∑ q : FixedWalk A 784 x₂.1 z,
          ∑ x₁ : {x : ↑(walkConflictingNeighbors784 A R q) // side x.1 = b},
            (Fintype.card {p : FixedWalk A 783 z x₁.1.1 //
              t * (walkCount A 783 z x₁.1.1 : ℝ) ≤
                (walkCount A 784 x₂.1 z : ℝ)} : ℝ)) ≤
      ∑ z : W, ∑ x₂ : {x : W // side x = !b},
        ∑ _q : FixedWalk A 784 x₂.1 z,
          784 * s * (t⁻¹ * (walkCount A 784 x₂.1 z : ℝ)) := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro x₂ _
      apply Finset.sum_le_sum
      intro q _
      calc
        (∑ x₁ : {x : ↑(walkConflictingNeighbors784 A R q) // side x.1 = b},
            (Fintype.card {p : FixedWalk A 783 z x₁.1.1 //
              t * (walkCount A 783 z x₁.1.1 : ℝ) ≤
                (walkCount A 784 x₂.1 z : ℝ)} : ℝ)) ≤
            ∑ _x₁ : {x : ↑(walkConflictingNeighbors784 A R q) // side x.1 = b},
              t⁻¹ * (walkCount A 784 x₂.1 z : ℝ) := by
          apply Finset.sum_le_sum
          intro x₁ _
          exact card_highFixedWalks_le A R t ht z x₂.1 q x₁.1
        _ = (Fintype.card {x : ↑(walkConflictingNeighbors784 A R q) //
              side x.1 = b} : ℝ) *
              (t⁻¹ * (walkCount A 784 x₂.1 z : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Nat.cast_mul]
        _ ≤ ((walkConflictingNeighbors784 A R q).card : ℝ) *
              (t⁻¹ * (walkCount A 784 x₂.1 z : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (inv_nonneg.mpr ht.le) (by positivity))
          have hc := Fintype.card_subtype_le
            (fun x : ↑(walkConflictingNeighbors784 A R q) ↦ side x.1 = b)
          have hc' : Fintype.card {x : ↑(walkConflictingNeighbors784 A R q) //
                side x.1 = b} ≤ (walkConflictingNeighbors784 A R q).card := by
            simpa only [Fintype.card_coe] using hc
          exact_mod_cast hc'
        _ ≤ (784 * s) *
              (t⁻¹ * (walkCount A 784 x₂.1 z : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (inv_nonneg.mpr ht.le) (by positivity))
          exact card_walkConflictingNeighbors784_le_at A R s hsymm q
            (fun u ↦ hlocal u x₂.1 x₂.2)
        _ = 784 * s *
              (t⁻¹ * (walkCount A 784 x₂.1 z : ℝ)) := by ring
    _ = 784 * s * t⁻¹ * (∑ z : W,
        ∑ x₂ : {x : W // side x = !b},
          (walkCount A 784 x₂.1 z : ℝ) ^ 2) := by
      simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Finset.mul_sum, walkCount]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x₂ _
      ring
    _ ≤ 784 * s * t⁻¹ * (∑ z : W, ∑ x₂ : W,
        (walkCount A 784 x₂ z : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro z _
      rw [← Finset.sum_subtype (Finset.univ.filter fun x : W ↦ side x = !b)
        (by simp) (fun x ↦ (walkCount A 784 x z : ℝ) ^ 2)]
      apply Finset.sum_le_sum_of_subset_of_nonneg (by simp)
      intro x _ _
      positivity
    _ = 784 * s * t⁻¹ * (closedWalkCount A 1568 : ℝ) := by
      rw [show 1568 = 2 * 784 by norm_num,
        closedWalkCount_cast_eq_sum_walkCount_sq]
      congr 1
      exact Finset.sum_comm

abbrev HalfCycleSideSplit {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ) :=
  Σ b : Bool,
    LowHalfCycleSide A side b (t b) ⊕
      HighBadHalfCycleSide A R side b (t b)

noncomputable def encodeBadHalfCycleSideSplit {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x) :
    BadHalfCycle A R → HalfCycleSideSplit A R side t
  | ⟨⟨z, x₁, p, x₂, q⟩, hbad⟩ =>
      let b := side x₁
      if hlow : (walkCount A 784 x₂.1 z : ℝ) <
          t b * (walkCount A 783 z x₁ : ℝ) then
        ⟨b, Sum.inl ⟨z, ⟨x₁, rfl⟩, p, x₂, ⟨q, hlow⟩⟩⟩
      else
        ⟨b, Sum.inr ⟨z, ⟨x₂.1, hcross x₂.2⟩, q,
          ⟨⟨x₁, by
            rw [mem_walkConflictingNeighbors784]
            exact ⟨by simpa using x₂.2.symm, hbad⟩⟩, rfl⟩,
          ⟨p, le_of_not_gt hlow⟩⟩⟩

noncomputable def decodeHalfCycleSideSplit {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ) :
    HalfCycleSideSplit A R side t → RawHalfCycle A
  | ⟨_b, Sum.inl ⟨z, x₁, p, x₂, q⟩⟩ =>
      ⟨z, x₁.1, p, x₂, q.1⟩
  | ⟨_b, Sum.inr ⟨z, x₂, q, x₁, p⟩⟩ =>
      ⟨z, x₁.1.1, p.1,
        ⟨x₂.1, by
          have hx := x₁.1.2
          rw [mem_walkConflictingNeighbors784] at hx
          exact hx.1.symm⟩,
        q⟩

lemma decode_encodeBadHalfCycleSideSplit {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (b : BadHalfCycle A R) :
    decodeHalfCycleSideSplit A R side t
        (encodeBadHalfCycleSideSplit A R side t hcross b) =
      eraseBadHalfCycle A R b := by
  rcases b with ⟨⟨z, x₁, p, x₂, q⟩, hbad⟩
  simp only [encodeBadHalfCycleSideSplit]
  split <;> simp [decodeHalfCycleSideSplit, eraseBadHalfCycle]

lemma encodeBadHalfCycleSideSplit_injective {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x) :
    Function.Injective (encodeBadHalfCycleSideSplit A R side t hcross) := by
  intro b c h
  apply eraseBadHalfCycle_injective A R
  rw [← decode_encodeBadHalfCycleSideSplit A R side t hcross b,
    ← decode_encodeBadHalfCycleSideSplit A R side t hcross c, h]

lemma card_BadHalfCycle_side_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t D s : Bool → ℝ)
    (ht : ∀ b, 0 < t b) (hD : ∀ b, 0 ≤ D b) (hs : ∀ b, 0 ≤ s b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D (side x))
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y,
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s (side y)) :
    (Fintype.card (BadHalfCycle A R) : ℝ) ≤
      ∑ b : Bool, (D b * t b * (closedWalkCount A 1566 : ℝ) +
        784 * s (!b) * (t b)⁻¹ * (closedWalkCount A 1568 : ℝ)) := by
  have hcardNat := Fintype.card_le_of_injective
    (encodeBadHalfCycleSideSplit A R side t hcross)
    (encodeBadHalfCycleSideSplit_injective A R side t hcross)
  have hcard : (Fintype.card (BadHalfCycle A R) : ℝ) ≤
      Fintype.card (HalfCycleSideSplit A R side t) := by
    exact_mod_cast hcardNat
  rw [Fintype.card_sigma, Nat.cast_sum] at hcard
  refine hcard.trans ?_
  apply Finset.sum_le_sum
  intro b _
  rw [Fintype.card_sum, Nat.cast_add]
  apply add_le_add
  · exact card_LowHalfCycleSide_le A side b (t b) (D b)
      (ht b).le (hD b) (fun x hx ↦ by simpa [hx] using hdegree x)
  · exact card_HighBadHalfCycleSide_le A R side b (t b) (s (!b))
      (ht b) (hs (!b)) hsymm (fun u y hy ↦ by simpa [hy] using hlocal u y)

lemma card_BadClosedWalk1568_side_cast_le {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t D s : Bool → ℝ)
    (ht : ∀ b, 0 < t b) (hD : ∀ b, 0 ≤ D b) (hs : ∀ b, 0 ≤ s b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D (side x))
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y,
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s (side y)) :
    (Fintype.card (Encode.BadClosedWalk1568 A R) : ℝ) ≤
      1568 * ∑ b : Bool,
        (D b * t b * (closedWalkCount A 1566 : ℝ) +
          784 * s (!b) * (t b)⁻¹ * (closedWalkCount A 1568 : ℝ)) := by
  calc
    (Fintype.card (Encode.BadClosedWalk1568 A R) : ℝ) ≤
        1568 * (Fintype.card (BadHalfCycle A R) : ℝ) := by
      exact_mod_cast Encode.card_BadClosedWalk1568_le A R hsymm
    _ ≤ 1568 * ∑ b : Bool,
        (D b * t b * (closedWalkCount A 1566 : ℝ) +
          784 * s (!b) * (t b)⁻¹ * (closedWalkCount A 1568 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact card_BadHalfCycle_side_le A R side t D s ht hD hs hcross hdegree
        hsymm hlocal

end Erdos113Sides

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/MomentsBipartite.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Erdos113LowerBipartite

open Conflict Lower

def alternatingProduct (d : Bool → ℝ) : Bool → ℕ → ℝ
  | _b, 0 => 1
  | b, m + 1 => d b * alternatingProduct d (!b) m

lemma alternatingProduct_nonneg (d : Bool → ℝ) (hd : ∀ b, 0 ≤ d b)
    (b : Bool) (m : ℕ) : 0 ≤ alternatingProduct d b m := by
  induction m generalizing b with
  | zero => simp [alternatingProduct]
  | succ m ih =>
      rw [alternatingProduct]
      exact mul_nonneg (hd b) (ih (!b))

lemma alternatingProduct_even (d : Bool → ℝ) (b : Bool) (m : ℕ) :
    alternatingProduct d b (2 * m) = (d b * d (!b)) ^ m := by
  induction m with
  | zero => simp [alternatingProduct]
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 2 by omega]
      rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega,
        alternatingProduct, alternatingProduct]
      simp only [Bool.not_not]
      rw [ih, pow_succ]
      ring

lemma walkMass_lower_bipartite {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (d : Bool → ℝ)
    (hd : ∀ b, 0 ≤ d b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdeg : ∀ x, d (side x) ≤ (A.degree x : ℝ))
    (m : ℕ) (x : W) :
    alternatingProduct d (side x) m ≤ walkMass A m x := by
  induction m generalizing x with
  | zero => simp [alternatingProduct]
  | succ m ih =>
      rw [show m + 1 = Nat.succ m by omega, alternatingProduct, walkMass_succ]
      calc
        d (side x) * alternatingProduct d (!side x) m ≤
            (A.degree x : ℝ) * alternatingProduct d (!side x) m := by
          exact mul_le_mul_of_nonneg_right (hdeg x)
            (alternatingProduct_nonneg d hd (!side x) m)
        _ = ∑ _y ∈ A.neighborFinset x,
              alternatingProduct d (!side x) m := by
          simp [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ ∑ y ∈ A.neighborFinset x, walkMass A m y := by
          apply Finset.sum_le_sum
          intro y hy
          have hadj : A.Adj x y := (A.mem_neighborFinset x y).mp hy
          simpa [hcross hadj] using ih y

/-- The matching two-sided upper bound for walk mass. -/
lemma walkMass_upper_bipartite {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (D : Bool → ℝ)
    (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdeg : ∀ x, (A.degree x : ℝ) ≤ D (side x))
    (m : ℕ) (x : W) :
    walkMass A m x ≤ alternatingProduct D (side x) m := by
  induction m generalizing x with
  | zero => simp [alternatingProduct]
  | succ m ih =>
      rw [show m + 1 = Nat.succ m by omega, alternatingProduct, walkMass_succ]
      calc
        (∑ y ∈ A.neighborFinset x, walkMass A m y) ≤
            ∑ _y ∈ A.neighborFinset x,
              alternatingProduct D (!side x) m := by
          apply Finset.sum_le_sum
          intro y hy
          have hadj : A.Adj x y := (A.mem_neighborFinset x y).mp hy
          simpa [hcross hadj] using ih y
        _ = (A.degree x : ℝ) * alternatingProduct D (!side x) m := by
          simp [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ D (side x) * alternatingProduct D (!side x) m := by
          exact mul_le_mul_of_nonneg_right (hdeg x)
            (alternatingProduct_nonneg D hD (!side x) m)

lemma closedWalkCount_lower_of_walkMass {W : Type*} [Fintype W]
    [DecidableEq W] [Nonempty W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (q : ℝ) (hq : 0 ≤ q)
    (m : ℕ) (hmass : ∀ x, q ≤ walkMass A m x) :
    q ^ 2 ≤ (closedWalkCount A (2 * m) : ℝ) := by
  let n : ℝ := Fintype.card W
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos
  have hmass_nonneg (x : W) : 0 ≤ walkMass A m x := by
    unfold walkMass
    positivity
  have hsumlower : n * q ^ 2 ≤ ∑ x : W, (walkMass A m x) ^ 2 := by
    calc
      n * q ^ 2 = ∑ _x : W, q ^ 2 := by simp [n]
      _ ≤ ∑ x : W, (walkMass A m x) ^ 2 := by
        apply Finset.sum_le_sum
        intro x _
        exact (sq_le_sq₀ hq (hmass_nonneg x)).2 (hmass x)
  have hcs : (∑ x : W, (walkMass A m x) ^ 2) ≤
      n * (closedWalkCount A (2 * m) : ℝ) := by
    rw [closedWalkCount_cast_eq_sum_walkCount_sq]
    calc
      (∑ x : W, (walkMass A m x) ^ 2) ≤
          ∑ x : W, n * ∑ y : W, (walkCount A m x y : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro x _
        simpa only [walkMass, n, Finset.card_univ, Nat.cast_ofNat] using
          (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset W))
            (f := fun y ↦ (walkCount A m x y : ℝ)))
      _ = n * ∑ x : W, ∑ y : W, (walkCount A m x y : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
  exact (mul_le_mul_iff_right₀ hn).mp (hsumlower.trans hcs)

lemma closedWalkCount_1568_lower_bipartite {W : Type*} [Fintype W]
    [DecidableEq W] [Nonempty W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (d : Bool → ℝ)
    (hd : ∀ b, 0 ≤ d b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdeg : ∀ x, d (side x) ≤ (A.degree x : ℝ)) :
    (d false * d true) ^ 784 ≤ (closedWalkCount A 1568 : ℝ) := by
  let q := (d false * d true) ^ 392
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hmass (x : W) : q ≤ walkMass A 784 x := by
    have h := walkMass_lower_bipartite A side d hd hcross hdeg 784 x
    rw [show 784 = 2 * 392 by norm_num, alternatingProduct_even] at h
    cases hx : side x <;> simpa [q, hx, mul_comm] using h
  have h := closedWalkCount_lower_of_walkMass A q hq 784 hmass
  rw [show 2 * 784 = 1568 by norm_num] at h
  calc
    (d false * d true) ^ 784 = q ^ 2 := by dsimp [q]; ring
    _ ≤ (closedWalkCount A 1568 : ℝ) := h

end Erdos113LowerBipartite

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Regularization.lean` -/

section
open scoped BigOperators

namespace Erdos113Regular

noncomputable def degreeBinCount {W : Type*} [Fintype W] : ℕ :=
  Nat.log 2 (Fintype.card W) + 1

noncomputable def degreeBin {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i : Fin (degreeBinCount (W := W))) : Finset W :=
  Finset.univ.filter fun x ↦ 0 < A.degree x ∧ Nat.log 2 (A.degree x) = i.val

lemma mem_degreeBin {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i : Fin (degreeBinCount (W := W))) (x : W) :
    x ∈ degreeBin A i ↔ 0 < A.degree x ∧ Nat.log 2 (A.degree x) = i.val := by
  simp [degreeBin]

def degreeBinIndex {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (x : W) :
    Fin (degreeBinCount (W := W)) :=
  ⟨Nat.log 2 (A.degree x), by
    dsimp [degreeBinCount]
    have hdeg := A.degree_lt_card_verts x
    have hlog := Nat.log_mono_right (b := 2) hdeg.le
    omega⟩

lemma sum_degreeBins_eq_sum_degrees
    {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] :
    ∑ i : Fin (degreeBinCount (W := W)),
        ∑ x ∈ degreeBin A i, A.degree x =
      ∑ x : W, A.degree x := by
  classical
  calc
    (∑ i : Fin (degreeBinCount (W := W)),
        ∑ x ∈ degreeBin A i, A.degree x) =
        ∑ i : Fin (degreeBinCount (W := W)),
          ∑ x ∈ (Finset.univ : Finset W) with degreeBinIndex A x = i,
            A.degree x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [degreeBin, Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : 0 < A.degree x
      · by_cases hi : Nat.log 2 (A.degree x) = i.val
        · have hfin : degreeBinIndex A x = i := Fin.ext hi
          simp [hx, hi, hfin]
        · have hfin : degreeBinIndex A x ≠ i := by
            intro h
            exact hi (congrArg Fin.val h)
          simp [hx, hi, hfin]
      · have hz : A.degree x = 0 := Nat.eq_zero_of_not_pos hx
        simp [hz]
    _ = ∑ x : W, A.degree x :=
      Finset.sum_fiberwise (Finset.univ : Finset W)
        (degreeBinIndex A) (fun x ↦ A.degree x)

abbrev BinNeighbor {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (x : W) (j : Fin (degreeBinCount (W := W))) :=
  {y : ↑(degreeBin A j) // A.Adj x y.1}

noncomputable def cellCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i j : Fin (degreeBinCount (W := W))) : ℕ :=
  ∑ x : ↑(degreeBin A i), Fintype.card (BinNeighbor A x.1 j)

abbrev NeighborBinFiber {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (x : W) (j : Fin (degreeBinCount (W := W))) :=
  {y : A.neighborSet x // degreeBinIndex A y.1 = j}

noncomputable def binNeighborEquivFiber {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (x : W) (j : Fin (degreeBinCount (W := W))) :
    BinNeighbor A x j ≃ NeighborBinFiber A x j where
  toFun y := ⟨⟨y.1.1, y.2⟩, by
    apply Fin.ext
    exact ((mem_degreeBin A j y.1.1).mp y.1.2).2⟩
  invFun y := by
    have hypos : 0 < A.degree y.1.1 := by
      have : x ∈ A.neighborFinset y.1.1 :=
        (A.mem_neighborFinset y.1.1 x).mpr y.1.2.symm
      exact Finset.card_pos.mpr ⟨x, this⟩
    have hybin : y.1.1 ∈ degreeBin A j := by
      rw [mem_degreeBin]
      exact ⟨hypos, congrArg Fin.val y.2⟩
    exact ⟨⟨y.1.1, hybin⟩, y.1.2⟩
  left_inv y := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; apply Subtype.ext; rfl

lemma sum_cellCount_row {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i : Fin (degreeBinCount (W := W))) :
    ∑ j, cellCount A i j = ∑ x ∈ degreeBin A i, A.degree x := by
  simp only [cellCount]
  rw [Finset.sum_comm]
  calc
    ∑ x : ↑(degreeBin A i), ∑ j,
        Fintype.card (BinNeighbor A x.1 j) =
        ∑ x : ↑(degreeBin A i), ∑ j,
          Fintype.card (NeighborBinFiber A x.1 j) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro j _
      exact Fintype.card_congr (binNeighborEquivFiber A x.1 j)
    _ = ∑ x : ↑(degreeBin A i), A.degree x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Fintype.card_sigma]
      rw [Fintype.card_congr (Equiv.sigmaFiberEquiv
        (fun y : A.neighborSet x.1 ↦ degreeBinIndex A y.1))]
      exact SimpleGraph.card_neighborSet_eq_degree A x.1
    _ = ∑ x ∈ degreeBin A i, A.degree x :=
      Finset.sum_coe_sort (degreeBin A i) (fun x ↦ A.degree x)

lemma degree_bounds_of_mem_bin {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i : Fin (degreeBinCount (W := W))) {x : W} (hx : x ∈ degreeBin A i) :
    2 ^ i.val ≤ A.degree x ∧ A.degree x < 2 ^ (i.val + 1) := by
  rw [mem_degreeBin] at hx
  have hspec := (Nat.log_eq_iff (b := 2) (m := i.val) (n := A.degree x)
    (Or.inr ⟨Nat.one_lt_two, hx.1.ne'⟩)).mp hx.2
  exact hspec

lemma binWeight_le_two_row {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i : Fin (degreeBinCount (W := W))) :
    (degreeBin A i).card * 2 ^ (i.val + 1) ≤ 2 * ∑ j, cellCount A i j := by
  rw [sum_cellCount_row]
  calc
    (degreeBin A i).card * 2 ^ (i.val + 1) =
        ∑ _x ∈ degreeBin A i, 2 * 2 ^ i.val := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, pow_succ]
      ring
    _ ≤ ∑ x ∈ degreeBin A i, 2 * A.degree x := by
      apply Finset.sum_le_sum
      intro x hx
      exact Nat.mul_le_mul_left 2 (degree_bounds_of_mem_bin A i hx).1
    _ = 2 * ∑ x ∈ degreeBin A i, A.degree x := by
      rw [Finset.mul_sum]

end Erdos113Regular

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/ActiveBins.lean` -/

section
open scoped BigOperators

namespace Erdos113ActiveBins

open Erdos113Regular

/-- A degree cell can simultaneously be chosen dense and balanced.  Its
edge count loses only the square of the number of dyadic bins, while the
balance inequality is the input needed by the two-sided pruning lemma. -/
lemma exists_dense_active_degree_cell
    {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (hedge : ∃ x y, A.Adj x y) :
    ∃ i j : Fin (degreeBinCount (W := W)),
      0 < cellCount A i j ∧
      A.edgeFinset.card ≤
        (degreeBinCount (W := W)) ^ 2 * cellCount A i j ∧
      (degreeBin A i).card * 2 ^ (i.val + 1) +
          (degreeBin A j).card * 2 ^ (j.val + 1) ≤
        4 * degreeBinCount (W := W) * cellCount A i j := by
  classical
  let L := degreeBinCount (W := W)
  letI : Nonempty (Fin L) :=
    ⟨⟨0, by dsimp [L, degreeBinCount]; omega⟩⟩
  let w : Fin L → ℕ := fun i ↦
    (degreeBin A i).card * 2 ^ (i.val + 1)
  obtain ⟨i, _hiuniv, himax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin L)) w Finset.univ_nonempty
  obtain ⟨j, _hjuniv, hjmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin L)) (cellCount A i) Finset.univ_nonempty
  have hLcard : Fintype.card (Fin L) = L := Fintype.card_fin L
  have hrow_le_w (k : Fin L) :
      ∑ x ∈ degreeBin A k, A.degree x ≤ w k := by
    calc
      (∑ x ∈ degreeBin A k, A.degree x) ≤
          ∑ _x ∈ degreeBin A k, 2 ^ (k.val + 1) := by
        apply Finset.sum_le_sum
        intro x hx
        exact (degree_bounds_of_mem_bin A k hx).2.le
      _ = w k := by
        simp [w]
  have htwice_edges_le : 2 * A.edgeFinset.card ≤ L * w i := by
    calc
      2 * A.edgeFinset.card = ∑ x : W, A.degree x :=
        A.sum_degrees_eq_twice_card_edges.symm
      _ = ∑ k : Fin L, ∑ x ∈ degreeBin A k, A.degree x := by
        simpa [L] using (sum_degreeBins_eq_sum_degrees A).symm
      _ ≤ ∑ k : Fin L, w k := by
        apply Finset.sum_le_sum
        intro k _
        exact hrow_le_w k
      _ ≤ ∑ _k : Fin L, w i := by
        apply Finset.sum_le_sum
        intro k hk
        exact himax k hk
      _ = L * w i := by simp [hLcard]
  have hwi_row : w i ≤ 2 * ∑ k : Fin L, cellCount A i k := by
    simpa [w, L] using binWeight_le_two_row A i
  have hrow_cell : ∑ k : Fin L, cellCount A i k ≤ L * cellCount A i j := by
    calc
      (∑ k : Fin L, cellCount A i k) ≤
          ∑ _k : Fin L, cellCount A i j := by
        apply Finset.sum_le_sum
        intro k hk
        exact hjmax k hk
      _ = L * cellCount A i j := by simp [hLcard]
  have hdense_twice :
      2 * A.edgeFinset.card ≤
        2 * (L ^ 2 * cellCount A i j) := by
    calc
      2 * A.edgeFinset.card ≤ L * w i := htwice_edges_le
      _ ≤ L * (2 * ∑ k : Fin L, cellCount A i k) :=
        Nat.mul_le_mul_left L hwi_row
      _ ≤ L * (2 * (L * cellCount A i j)) := by
        gcongr
      _ = 2 * (L ^ 2 * cellCount A i j) := by ring
  have hdense : A.edgeFinset.card ≤ L ^ 2 * cellCount A i j := by
    omega
  have hedgepos : 0 < A.edgeFinset.card := by
    obtain ⟨x, y, hxy⟩ := hedge
    apply Finset.card_pos.mpr
    exact ⟨s(x, y), by simpa using hxy⟩
  have hcellpos : 0 < cellCount A i j := by
    by_contra! hz
    have hz' : cellCount A i j = 0 := Nat.eq_zero_of_le_zero hz
    rw [hz', mul_zero] at hdense
    omega
  have hwj : w j ≤ w i := himax j (Finset.mem_univ _)
  have hbalanced : w i + w j ≤ 4 * L * cellCount A i j := by
    calc
      w i + w j ≤ 2 * w i := by omega
      _ ≤ 4 * ∑ k : Fin L, cellCount A i k := by omega
      _ ≤ 4 * (L * cellCount A i j) := Nat.mul_le_mul_left 4 hrow_cell
      _ = 4 * L * cellCount A i j := by ring
  refine ⟨i, j, hcellpos, ?_, ?_⟩
  · simpa [L] using hdense
  · simpa [w, L] using hbalanced

end Erdos113ActiveBins

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Pruning.lean` -/

section
namespace Erdos113Pruning

theorem exists_pruned_indexed {a K : Type*} [DecidableEq a] [DecidableEq K]
    (C : Finset a) (S : Finset K) (fiber : K → Finset a) (t : K → ℕ) :
    ∃ D : Finset a,
      D ⊆ C ∧
      C.card ≤ D.card + ∑ k ∈ S, (t k - 1) ∧
      ∀ k ∈ S, (D ∩ fiber k).Nonempty → t k ≤ (D ∩ fiber k).card := by
  induction hn : S.card using Nat.strong_induction_on generalizing C S with
  | h n ih =>
      by_cases hsmall : ∃ k ∈ S,
          (C ∩ fiber k).Nonempty ∧ (C ∩ fiber k).card < t k
      · obtain ⟨k, hk, _hne, hlt⟩ := hsmall
        have herase_lt : (S.erase k).card < n := by
          rw [← hn]
          exact Finset.card_erase_lt_of_mem hk
        obtain ⟨D, hDsub, hDcard, hDstab⟩ :=
          ih (S.erase k).card herase_lt (C \ fiber k) (S.erase k) rfl
        refine ⟨D, hDsub.trans Finset.sdiff_subset, ?_, ?_⟩
        · have hsplit := Finset.card_sdiff_add_card_inter C (fiber k)
          have hkbound : (C ∩ fiber k).card ≤ t k - 1 := Nat.le_sub_one_of_lt hlt
          calc
            C.card = (C \ fiber k).card + (C ∩ fiber k).card := hsplit.symm
            _ ≤ (D.card + ∑ j ∈ S.erase k, (t j - 1)) + (t k - 1) :=
              Nat.add_le_add hDcard hkbound
            _ = D.card + ∑ j ∈ S, (t j - 1) := by
              rw [← Finset.sum_erase_add S (fun j ↦ t j - 1) hk]
              omega
        · intro j hj hnonempty
          by_cases hjk : j = k
          · subst j
            obtain ⟨x, hx⟩ := hnonempty
            have ⟨hxD, hxF⟩ := Finset.mem_inter.mp hx
            exact ((Finset.mem_sdiff.mp (hDsub hxD)).2 hxF).elim
          · exact hDstab j (Finset.mem_erase.mpr ⟨hjk, hj⟩) hnonempty
      · refine ⟨C, Finset.Subset.rfl, by omega, ?_⟩
        intro k hk hne
        exact le_of_not_gt (fun hlt ↦ hsmall ⟨k, hk, hne, hlt⟩)

end Erdos113Pruning

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/BipartiteGraph.lean` -/

section
namespace Erdos113BipartiteGraph

abbrev LiveLeft {U V : Type*} [Fintype U] [Fintype V]
    (E : Finset (U × V)) := {u : U // ∃ v, (u, v) ∈ E}

abbrev LiveRight {U V : Type*} [Fintype U] [Fintype V]
    (E : Finset (U × V)) := {v : V // ∃ u, (u, v) ∈ E}

def retainedGraph {U V : Type*} [Fintype U] [Fintype V]
    (E : Finset (U × V)) : SimpleGraph (LiveLeft E ⊕ LiveRight E) where
  Adj x y := match x, y with
    | Sum.inl u, Sum.inr v => (u.1, v.1) ∈ E
    | Sum.inr v, Sum.inl u => (u.1, v.1) ∈ E
    | _, _ => False
  symm := ⟨by
    rintro (u | v) (u' | v') h <;> simp_all⟩
  loopless := ⟨by
    rintro (u | v) h <;> simp_all⟩

instance {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (E : Finset (U × V)) :
    DecidableRel (retainedGraph E).Adj := fun x y ↦ by
  rcases x with u | v <;> rcases y with u' | v' <;>
    simp only [retainedGraph] <;> infer_instance

noncomputable def leftFiber {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] (E : Finset (U × V)) (u : U) : Finset (U × V) :=
  E.filter fun p ↦ p.1 = u

noncomputable def rightFiber {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq V] (E : Finset (U × V)) (v : V) : Finset (U × V) :=
  E.filter fun p ↦ p.2 = v

@[simp] lemma mem_leftFiber {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] (E : Finset (U × V)) (u : U) (p : U × V) :
    p ∈ leftFiber E u ↔ p ∈ E ∧ p.1 = u := by
  simp [leftFiber]

@[simp] lemma mem_rightFiber {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq V] (E : Finset (U × V)) (v : V) (p : U × V) :
    p ∈ rightFiber E v ↔ p ∈ E ∧ p.2 = v := by
  simp [rightFiber]

/-- Counting a finite bipartite edge set by its left endpoint. -/
lemma card_eq_sum_leftFiber {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] (E : Finset (U × V)) :
    E.card = ∑ u : U, (leftFiber E u).card := by
  classical
  simpa [leftFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (s := E) (t := (Finset.univ : Finset U)) (f := Prod.fst)
      (by
        intro p _hp
        exact Finset.mem_univ p.1 :
        (E : Set (U × V)).MapsTo Prod.fst
          (↑(Finset.univ : Finset U) : Set U)))

/-- Counting a finite bipartite edge set by its right endpoint. -/
lemma card_eq_sum_rightFiber {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq V] (E : Finset (U × V)) :
    E.card = ∑ v : V, (rightFiber E v).card := by
  classical
  simpa [rightFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (s := E) (t := (Finset.univ : Finset V)) (f := Prod.snd)
      (by
        intro p _hp
        exact Finset.mem_univ p.2 :
        (E : Set (U × V)).MapsTo Prod.snd
          (↑(Finset.univ : Finset V) : Set V)))

lemma card_le_card_mul_of_leftFiber_le {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] (E : Finset (U × V)) (D : ℕ)
    (h : ∀ u, (leftFiber E u).card ≤ D) :
    E.card ≤ Fintype.card U * D := by
  rw [card_eq_sum_leftFiber]
  calc
    ∑ u : U, (leftFiber E u).card ≤ ∑ _u : U, D :=
      Finset.sum_le_sum (fun u _ ↦ h u)
    _ = Fintype.card U * D := by simp

lemma card_le_card_mul_of_rightFiber_le {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq V] (E : Finset (U × V)) (D : ℕ)
    (h : ∀ v, (rightFiber E v).card ≤ D) :
    E.card ≤ Fintype.card V * D := by
  rw [card_eq_sum_rightFiber]
  calc
    ∑ v : V, (rightFiber E v).card ≤ ∑ _v : V, D :=
      Finset.sum_le_sum (fun v _ ↦ h v)
    _ = Fintype.card V * D := by simp

noncomputable def leftNeighborEquivFiber {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (E : Finset (U × V)) (u : LiveLeft E) :
    (retainedGraph E).neighborSet (Sum.inl u) ≃ ↑(leftFiber E u.1) where
  toFun y := by
    rcases y with ⟨y, hy⟩
    rcases y with u' | v
    · exact False.elim hy
    · exact ⟨(u.1, v.1), by
        rw [mem_leftFiber]
        exact ⟨hy, rfl⟩⟩
  invFun p := by
    have hp := (mem_leftFiber E u.1 p.1).mp p.2
    let v : LiveRight E := ⟨p.1.2, ⟨p.1.1, hp.1⟩⟩
    refine ⟨Sum.inr v, ?_⟩
    change (u.1, p.1.2) ∈ E
    convert hp.1 using 1
    apply Prod.ext
    · exact hp.2.symm
    · rfl
  left_inv y := by
    rcases y with ⟨y, hy⟩
    rcases y with u' | v
    · exact False.elim hy
    · apply Subtype.ext
      rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact ((mem_leftFiber E u.1 p.1).mp p.2).2.symm
    · rfl

noncomputable def rightNeighborEquivFiber {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (E : Finset (U × V)) (v : LiveRight E) :
    (retainedGraph E).neighborSet (Sum.inr v) ≃ ↑(rightFiber E v.1) where
  toFun y := by
    rcases y with ⟨y, hy⟩
    rcases y with u | v'
    · exact ⟨(u.1, v.1), by
        rw [mem_rightFiber]
        exact ⟨hy, rfl⟩⟩
    · exact False.elim hy
  invFun p := by
    have hp := (mem_rightFiber E v.1 p.1).mp p.2
    let u : LiveLeft E := ⟨p.1.1, ⟨p.1.2, hp.1⟩⟩
    refine ⟨Sum.inl u, ?_⟩
    change (p.1.1, v.1) ∈ E
    convert hp.1 using 1
    apply Prod.ext
    · rfl
    · exact hp.2.symm
  left_inv y := by
    rcases y with ⟨y, hy⟩
    rcases y with u | v'
    · apply Subtype.ext
      rfl
    · exact False.elim hy
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact ((mem_rightFiber E v.1 p.1).mp p.2).2.symm

lemma degree_inl {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (E : Finset (U × V)) (u : LiveLeft E) :
    (retainedGraph E).degree (Sum.inl u) = (leftFiber E u.1).card := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  simpa only [Fintype.card_coe] using Fintype.card_congr (leftNeighborEquivFiber E u)

lemma degree_inr {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (E : Finset (U × V)) (v : LiveRight E) :
    (retainedGraph E).degree (Sum.inr v) = (rightFiber E v.1).card := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  simpa only [Fintype.card_coe] using Fintype.card_congr (rightNeighborEquivFiber E v)

lemma cross {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (E : Finset (U × V))
    {x y : LiveLeft E ⊕ LiveRight E} (h : (retainedGraph E).Adj x y) :
    Sum.elim (fun _ ↦ false) (fun _ ↦ true) y =
      !Sum.elim (fun _ ↦ false) (fun _ ↦ true) x := by
  rcases x with u | v <;> rcases y with u' | v' <;> simp_all [retainedGraph]

lemma nonempty_of_nonempty {U V : Type*} [Fintype U] [Fintype V]
    (E : Finset (U × V)) (hE : E.Nonempty) :
    Nonempty (LiveLeft E ⊕ LiveRight E) := by
  obtain ⟨⟨u, v⟩, huv⟩ := hE
  exact ⟨Sum.inl ⟨u, ⟨v, huv⟩⟩⟩

end Erdos113BipartiteGraph

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/CellPruning.lean` -/

section
open scoped BigOperators

namespace Erdos113CellPruning

noncomputable section

open Erdos113Regular Erdos113ActiveBins Erdos113BipartiteGraph

abbrev BinVertex {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i : Fin (degreeBinCount (W := W))) := ↑(degreeBin A i)

noncomputable def cellEdges {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i j : Fin (degreeBinCount (W := W))) :
    Finset (BinVertex A i × BinVertex A j) :=
  Finset.univ.filter fun p ↦ A.Adj p.1.1 p.2.1

@[simp] lemma mem_cellEdges {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i j : Fin (degreeBinCount (W := W)))
    (p : BinVertex A i × BinVertex A j) :
    p ∈ cellEdges A i j ↔ A.Adj p.1.1 p.2.1 := by
  simp [cellEdges]

noncomputable def cellEdgesEquivSigma {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i j : Fin (degreeBinCount (W := W))) :
    ↑(cellEdges A i j) ≃ (Σ x : BinVertex A i, BinNeighbor A x.1 j) where
  toFun p := ⟨p.1.1, ⟨p.1.2, (mem_cellEdges A i j p.1).mp p.2⟩⟩
  invFun p := ⟨(p.1, p.2.1), (mem_cellEdges A i j _).mpr p.2.2⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by rfl

lemma card_cellEdges {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i j : Fin (degreeBinCount (W := W))) :
    (cellEdges A i j).card = cellCount A i j := by
  rw [← Fintype.card_coe]
  rw [show cellCount A i j = Fintype.card
      (Σ x : BinVertex A i, BinNeighbor A x.1 j) by
    simp only [cellCount, Fintype.card_sigma]]
  exact Fintype.card_congr (cellEdgesEquivSigma A i j)

noncomputable def cellThreshold (cap L : ℕ) : ℕ :=
  ⌈(cap : ℝ) / (16 * L : ℕ)⌉₊

lemma cellThreshold_pos {cap L : ℕ} (hcap : 0 < cap) (hL : 0 < L) :
    0 < cellThreshold cap L := by
  rw [cellThreshold, Nat.ceil_pos]
  positivity

lemma cast_cellThreshold_sub_one_le {cap L : ℕ} (hcap : 0 < cap)
    (hL : 0 < L) :
    ((cellThreshold cap L - 1 : ℕ) : ℝ) ≤ (cap : ℝ) / (16 * L : ℕ) := by
  have htpos : 0 < cellThreshold cap L := cellThreshold_pos hcap hL
  have hlt := Nat.ceil_lt_add_one
    (show 0 ≤ (cap : ℝ) / (16 * L : ℕ) by positivity)
  change (cellThreshold cap L : ℝ) < (cap : ℝ) / (16 * L : ℕ) + 1 at hlt
  rw [Nat.cast_sub (by omega : 1 ≤ cellThreshold cap L), Nat.cast_one]
  linarith

lemma cap_div_le_cast_cellThreshold {cap L : ℕ} :
    (cap : ℝ) / (16 * L : ℕ) ≤ (cellThreshold cap L : ℝ) := by
  exact Nat.le_ceil _

theorem exists_pruned_cell {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (hedge : ∃ x y, A.Adj x y) :
    ∃ (i j : Fin (degreeBinCount (W := W)))
      (D : Finset (BinVertex A i × BinVertex A j)),
      D ⊆ cellEdges A i j ∧ D.Nonempty ∧
      A.edgeFinset.card ≤
        2 * (degreeBinCount (W := W)) ^ 2 * D.card ∧
      (∀ x : BinVertex A i,
        (D ∩ leftFiber (cellEdges A i j) x).Nonempty →
          cellThreshold (2 ^ (i.val + 1)) (degreeBinCount (W := W)) ≤
            (leftFiber D x).card) ∧
      (∀ y : BinVertex A j,
        (D ∩ rightFiber (cellEdges A i j) y).Nonempty →
          cellThreshold (2 ^ (j.val + 1)) (degreeBinCount (W := W)) ≤
            (rightFiber D y).card) := by
  classical
  obtain ⟨i, j, hcellpos, hcellDense, hweight⟩ :=
    exists_dense_active_degree_cell A hedge
  let C := cellEdges A i j
  let L := degreeBinCount (W := W)
  let tL := cellThreshold (2 ^ (i.val + 1)) L
  let tR := cellThreshold (2 ^ (j.val + 1)) L
  let fiber : (BinVertex A i ⊕ BinVertex A j) →
      Finset (BinVertex A i × BinVertex A j) :=
    Sum.elim (leftFiber C) (rightFiber C)
  let threshold : (BinVertex A i ⊕ BinVertex A j) → ℕ :=
    Sum.elim (fun _ ↦ tL) (fun _ ↦ tR)
  obtain ⟨D, hDsub, hDcard, hDstab⟩ :=
    Erdos113Pruning.exists_pruned_indexed C Finset.univ fiber threshold
  have hLpos : 0 < L := by dsimp [L, degreeBinCount]; omega
  have hcost : ((∑ k : BinVertex A i ⊕ BinVertex A j,
      (threshold k - 1) : ℕ) : ℝ) ≤ (C.card : ℝ) / 4 := by
    have htL := cast_cellThreshold_sub_one_le (cap := 2 ^ (i.val + 1)) (L := L)
      (pow_pos (by omega) _) hLpos
    have htR := cast_cellThreshold_sub_one_le (cap := 2 ^ (j.val + 1)) (L := L)
      (pow_pos (by omega) _) hLpos
    have hfirst : ((∑ k : BinVertex A i ⊕ BinVertex A j,
        (threshold k - 1) : ℕ) : ℝ) ≤
        ((degreeBin A i).card * 2 ^ (i.val + 1) +
          (degreeBin A j).card * 2 ^ (j.val + 1) : ℕ) / (16 * L : ℕ) := by
      simp only [Fintype.sum_sum_type, threshold, tL, tR, Sum.elim_inl,
        Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_mul]
      have hi : ((degreeBin A i).card : ℝ) * (tL - 1 : ℕ) ≤
          ((degreeBin A i).card : ℝ) *
            ((2 ^ (i.val + 1) : ℕ) : ℝ) / (16 * L : ℕ) := by
        calc
          ((degreeBin A i).card : ℝ) * (tL - 1 : ℕ) ≤
              ((degreeBin A i).card : ℝ) *
                (((2 ^ (i.val + 1) : ℕ) : ℝ) / (16 * L : ℕ)) := by gcongr
          _ = _ := by ring
      have hj : ((degreeBin A j).card : ℝ) * (tR - 1 : ℕ) ≤
          ((degreeBin A j).card : ℝ) *
            ((2 ^ (j.val + 1) : ℕ) : ℝ) / (16 * L : ℕ) := by
        calc
          ((degreeBin A j).card : ℝ) * (tR - 1 : ℕ) ≤
              ((degreeBin A j).card : ℝ) *
                (((2 ^ (j.val + 1) : ℕ) : ℝ) / (16 * L : ℕ)) := by gcongr
          _ = _ := by ring
      push_cast
      calc
        ((degreeBin A i).card : ℝ) * (tL - 1 : ℕ) +
            ((degreeBin A j).card : ℝ) * (tR - 1 : ℕ) ≤
            ((degreeBin A i).card : ℝ) * (2 ^ (i.val + 1) : ℕ) /
                (16 * L : ℕ) +
              ((degreeBin A j).card : ℝ) * (2 ^ (j.val + 1) : ℕ) /
                (16 * L : ℕ) := add_le_add hi hj
        _ = (((degreeBin A i).card : ℝ) * (2 ^ (i.val + 1) : ℕ) +
              ((degreeBin A j).card : ℝ) * (2 ^ (j.val + 1) : ℕ)) /
              (16 * L : ℕ) := by ring
        _ = (((degreeBin A i).card : ℝ) * (2 : ℝ) ^ (i.val + 1) +
              ((degreeBin A j).card : ℝ) * (2 : ℝ) ^ (j.val + 1)) /
              (16 * (L : ℝ)) := by norm_num
    have hweightR :
        (((degreeBin A i).card * 2 ^ (i.val + 1) +
          (degreeBin A j).card * 2 ^ (j.val + 1) : ℕ) : ℝ) ≤
          4 * L * (C.card : ℝ) := by
      exact_mod_cast (show
        (degreeBin A i).card * 2 ^ (i.val + 1) +
            (degreeBin A j).card * 2 ^ (j.val + 1) ≤
          4 * L * C.card by
        simpa [L, C, card_cellEdges A i j] using hweight)
    calc
      ((∑ k : BinVertex A i ⊕ BinVertex A j,
          (threshold k - 1) : ℕ) : ℝ) ≤
          ((degreeBin A i).card * 2 ^ (i.val + 1) +
            (degreeBin A j).card * 2 ^ (j.val + 1) : ℕ) /
              (16 * L : ℕ) := hfirst
      _ ≤ (C.card : ℝ) / 4 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (16 * L : ℕ))).2
        calc
          (((degreeBin A i).card * 2 ^ (i.val + 1) +
            (degreeBin A j).card * 2 ^ (j.val + 1) : ℕ) : ℝ) ≤
              4 * L * (C.card : ℝ) := hweightR
          _ = (C.card : ℝ) / 4 * ((16 * L : ℕ) : ℝ) := by
            push_cast
            ring
  have hCpos : 0 < C.card := by
    simpa [C, card_cellEdges A i j] using hcellpos
  have hDnonempty : D.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hDEmpty
    have hDzero : D.card = 0 := by simp [hDEmpty]
    have hcardR : (C.card : ℝ) ≤
        ((∑ k : BinVertex A i ⊕ BinVertex A j,
          (threshold k - 1) : ℕ) : ℝ) := by
      exact_mod_cast (by simpa [hDzero] using hDcard)
    have hCposR : (0 : ℝ) < C.card := by exact_mod_cast hCpos
    nlinarith
  have hCDreal : (C.card : ℝ) ≤ 2 * (D.card : ℝ) := by
    have hDcardR : (C.card : ℝ) ≤
        (D.card : ℝ) +
          ((∑ k : BinVertex A i ⊕ BinVertex A j,
            (threshold k - 1) : ℕ) : ℝ) := by
      exact_mod_cast hDcard
    nlinarith
  have hCD : C.card ≤ 2 * D.card := by exact_mod_cast hCDreal
  have hDenseD : A.edgeFinset.card ≤
      2 * (degreeBinCount (W := W)) ^ 2 * D.card := by
    calc
      A.edgeFinset.card ≤
          (degreeBinCount (W := W)) ^ 2 * cellCount A i j := hcellDense
      _ = (degreeBinCount (W := W)) ^ 2 * C.card := by
        change (degreeBinCount (W := W)) ^ 2 * cellCount A i j =
          (degreeBinCount (W := W)) ^ 2 * (cellEdges A i j).card
        rw [card_cellEdges]
      _ ≤ (degreeBinCount (W := W)) ^ 2 * (2 * D.card) :=
        Nat.mul_le_mul_left _ hCD
      _ = 2 * (degreeBinCount (W := W)) ^ 2 * D.card := by ring
  have hleft (x : BinVertex A i) :
      D ∩ leftFiber C x = leftFiber D x := by
    ext p
    simp only [Finset.mem_inter, mem_leftFiber]
    constructor
    · exact fun hp ↦ ⟨hp.1, hp.2.2⟩
    · exact fun hp ↦ ⟨hp.1, hDsub hp.1, hp.2⟩
  have hright (y : BinVertex A j) :
      D ∩ rightFiber C y = rightFiber D y := by
    ext p
    simp only [Finset.mem_inter, mem_rightFiber]
    constructor
    · exact fun hp ↦ ⟨hp.1, hp.2.2⟩
    · exact fun hp ↦ ⟨hp.1, hDsub hp.1, hp.2⟩
  refine ⟨i, j, D, hDsub, hDnonempty, hDenseD, ?_, ?_⟩
  · intro x hx
    have hs := hDstab (Sum.inl x) (Finset.mem_univ _) hx
    change tL ≤ (D ∩ leftFiber C x).card at hs
    rw [hleft x] at hs
    simpa [threshold, tL, fiber, L] using hs
  · intro y hy
    have hs := hDstab (Sum.inr y) (Finset.mem_univ _) hy
    change tR ≤ (D ∩ rightFiber C y).card at hs
    rw [hright y] at hs
    simpa [threshold, tR, fiber, L] using hs

lemma card_leftFiber_le_degree {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i j : Fin (degreeBinCount (W := W)))
    (D : Finset (BinVertex A i × BinVertex A j))
    (hD : D ⊆ cellEdges A i j) (x : BinVertex A i) :
    (leftFiber D x).card ≤ A.degree x.1 := by
  let f : ↑(leftFiber D x) → A.neighborSet x.1 := fun p ↦
    ⟨p.1.2.1, by
      have hp := (mem_leftFiber D x p.1).mp p.2
      have hadj := (mem_cellEdges A i j p.1).mp (hD hp.1)
      simpa [hp.2] using hadj⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have hpqW := congrArg Subtype.val hpq
    change p.1.2.1 = q.1.2.1 at hpqW
    apply Subtype.ext
    apply Prod.ext
    · exact ((mem_leftFiber D x p.1).mp p.2).2.trans
        ((mem_leftFiber D x q.1).mp q.2).2.symm
    · apply Subtype.ext
      exact hpqW
  rw [← Fintype.card_coe, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_injective f hf

lemma card_rightFiber_le_degree {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i j : Fin (degreeBinCount (W := W)))
    (D : Finset (BinVertex A i × BinVertex A j))
    (hD : D ⊆ cellEdges A i j) (y : BinVertex A j) :
    (rightFiber D y).card ≤ A.degree y.1 := by
  let f : ↑(rightFiber D y) → A.neighborSet y.1 := fun p ↦
    ⟨p.1.1.1, by
      have hp := (mem_rightFiber D y p.1).mp p.2
      have hadj := (mem_cellEdges A i j p.1).mp (hD hp.1)
      simpa [hp.2] using hadj.symm⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have hpqW := congrArg Subtype.val hpq
    change p.1.1.1 = q.1.1.1 at hpqW
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact hpqW
    · exact ((mem_rightFiber D y p.1).mp p.2).2.trans
        ((mem_rightFiber D y q.1).mp q.2).2.symm
  rw [← Fintype.card_coe, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_injective f hf

end

end Erdos113CellPruning

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Paths.lean` -/

section
/-!
# Counting finite vertex sequences which follow graph edges
-/

open scoped SimpleGraph BigOperators Real

namespace Erdos113Paths

open Conflict Lower

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A labelled walk written as its `m+1` successive vertices. -/
abbrev PathTuple (G : SimpleGraph V) (m : ℕ) :=
  {f : Fin (m + 1) → V //
    ∀ i : Fin m, G.Adj (f i.castSucc) (f i.succ)}

/-- Package a vertex sequence as a Mathlib walk, retaining both endpoints. -/
def encodePathTuple (G : SimpleGraph V) (m : ℕ) :
    PathTuple G m →
      Σ u : V, Σ v : V, Conflict.FixedWalk G m u v := fun f ↦
  ⟨f.1 ⟨0, Nat.zero_lt_succ m⟩,
    f.1 ⟨m, Nat.lt_succ_self m⟩,
    ⟨WF.walkOfFin m f.1 f.2, WF.walkOfFin_length m f.1 f.2⟩⟩

lemma encodePathTuple_injective (G : SimpleGraph V) (m : ℕ) :
    Function.Injective (encodePathTuple G m) := by
  intro f g h
  apply Subtype.ext
  funext i
  have hw := congrArg (fun z ↦ z.2.2.1.getVert i.val) h
  change (WF.walkOfFin m f.1 f.2).getVert i.val =
    (WF.walkOfFin m g.1 g.2).getVert i.val at hw
  rw [WF.walkOfFin_getVert m f.1 f.2 i.val (Nat.le_of_lt_succ i.2),
    WF.walkOfFin_getVert m g.1 g.2 i.val (Nat.le_of_lt_succ i.2)] at hw
  exact hw

/-- For an odd-length bipartite path, starting from its first oriented edge
replaces the crude vertex-count factor by twice the number of edges.  This is
the form used for adjacent-pair patterns in the many-four-cycle family. -/
lemma card_pathTuple_53_cast_le_bipartite_edges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (D : Bool → ℝ) (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x)) :
    (Fintype.card (PathTuple G 53) : ℝ) ≤
      2 * G.edgeFinset.card * (D false * D true) ^ 26 := by
  classical
  have hcard : Fintype.card (PathTuple G 53) ≤
      Fintype.card (Σ u : V, Σ v : V, Conflict.FixedWalk G 53 u v) :=
    Fintype.card_le_of_injective (encodePathTuple G 53)
      (encodePathTuple_injective G 53)
  have hmass (x : V) :
      Lower.walkMass G 53 x ≤ (G.degree x : ℝ) * (D false * D true) ^ 26 := by
    rw [show 53 = 52 + 1 by norm_num, Lower.walkMass_succ]
    calc
      (∑ y ∈ G.neighborFinset x, Lower.walkMass G 52 y) ≤
          ∑ _y ∈ G.neighborFinset x, (D false * D true) ^ 26 := by
        apply Finset.sum_le_sum
        intro y hy
        have hyadj : G.Adj x y := (G.mem_neighborFinset x y).mp hy
        have hupper := Erdos113LowerBipartite.walkMass_upper_bipartite
          G side D hD hcross hdeg 52 y
        rw [show 52 = 2 * 26 by norm_num,
          Erdos113LowerBipartite.alternatingProduct_even] at hupper
        cases h : side y <;> simp [h] at hupper ⊢ <;>
          simpa [mul_comm] using hupper
      _ = (G.degree x : ℝ) * (D false * D true) ^ 26 := by
        simp [SimpleGraph.card_neighborFinset_eq_degree]
  calc
    (Fintype.card (PathTuple G 53) : ℝ) ≤
        Fintype.card (Σ u : V, Σ v : V, Conflict.FixedWalk G 53 u v) := by
      exact_mod_cast hcard
    _ = ∑ u : V, Lower.walkMass G 53 u := by
      simp only [Fintype.card_sigma, Nat.cast_sum]
      rfl
    _ ≤ ∑ u : V, (G.degree u : ℝ) * (D false * D true) ^ 26 := by
      exact Finset.sum_le_sum fun u _ ↦ hmass u
    _ = (∑ u : V, (G.degree u : ℝ)) * (D false * D true) ^ 26 := by
      rw [Finset.sum_mul]
    _ = 2 * G.edgeFinset.card * (D false * D true) ^ 26 := by
      norm_cast
      rw [G.sum_degrees_eq_twice_card_edges]

end Erdos113Paths

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Cycles.lean` -/

section
/-!
# Finite ordered cycles used in the proof of Erdős 113

The source proof counts *labelled, oriented* cycles.  Keeping that convention
avoids quotienting by rotations and reflections; all constants in the
extremal argument are insensitive to the resulting fixed multiplicity.
-/

open scoped SimpleGraph

namespace Erdos113Cycles

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A cyclically adjacent tuple.  Vertices are not required to be distinct. -/
def IsHomCycle (G : SimpleGraph V) {r : ℕ} [NeZero r] (x : Fin r → V) : Prop :=
  ∀ i, G.Adj (x i) (x (i + 1))

/-- A labelled, oriented, genuine cycle. -/
def IsGenuineCycle (G : SimpleGraph V) {r : ℕ} [NeZero r] (x : Fin r → V) : Prop :=
  Function.Injective x ∧ IsHomCycle G x

noncomputable instance (G : SimpleGraph V) {r : ℕ} [NeZero r] :
    DecidablePred (IsHomCycle G : (Fin r → V) → Prop) := Classical.decPred _

noncomputable instance (G : SimpleGraph V) {r : ℕ} [NeZero r] :
    DecidablePred (IsGenuineCycle G : (Fin r → V) → Prop) := Classical.decPred _

/-- The finite set of labelled, oriented genuine `r`-cycles. -/
noncomputable def genuineCycles (G : SimpleGraph V) (r : ℕ) [NeZero r] :
    Finset (Fin r → V) :=
  Finset.univ.filter (IsGenuineCycle G)

@[simp] lemma mem_genuineCycles {G : SimpleGraph V} {r : ℕ} [NeZero r]
    {x : Fin r → V} :
    x ∈ genuineCycles G r ↔ IsGenuineCycle G x := by
  classical
  simp [genuineCycles]

/-- The edge used at cyclic position `i`. -/
def cycleEdge {r : ℕ} [NeZero r] (x : Fin r → V) (i : Fin r) : Sym2 V :=
  s(x i, x (i + 1))

/-- Restrict a graph to a chosen finite set of its (non-diagonal) edges. -/
def graphOfEdges (D : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (D : Set (Sym2 V))

noncomputable instance (D : Finset (Sym2 V)) : DecidableRel (graphOfEdges D).Adj := by
  classical
  infer_instance

lemma graphOfEdges_adj_iff {D : Finset (Sym2 V)} {u v : V} :
    (graphOfEdges D).Adj u v ↔ s(u, v) ∈ D ∧ u ≠ v := by
  simp [graphOfEdges, SimpleGraph.fromEdgeSet_adj]

lemma graphOfEdges_le {G : SimpleGraph V} [DecidableRel G.Adj]
    {D : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) :
    graphOfEdges D ≤ G := by
  intro u v huv
  have hd : s(u, v) ∈ D := (graphOfEdges_adj_iff.mp huv).1
  exact (SimpleGraph.mem_edgeFinset.mp (hD hd))

lemma edgeFinset_graphOfEdges {D : Finset (Sym2 V)}
    (hdiag : Disjoint (D : Set (Sym2 V)) Sym2.diagSet) :
    (graphOfEdges D).edgeFinset = D := by
  apply Finset.coe_injective
  simp only [SimpleGraph.edgeFinset, Set.coe_toFinset]
  unfold graphOfEdges
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  exact sdiff_eq_left.mpr hdiag

lemma disjoint_diag_of_subset_edgeFinset {G : SimpleGraph V} [DecidableRel G.Adj]
    {D : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) :
    Disjoint (D : Set (Sym2 V)) Sym2.diagSet := by
  refine Set.disjoint_left.2 ?_
  intro e heD hediag
  have heG : e ∈ G.edgeSet := by
    have : e ∈ G.edgeFinset := hD (by simpa using heD)
    simpa using this
  exact G.not_isDiag_of_mem_edgeSet heG hediag

lemma edgeFinset_graphOfEdges_of_subset {G : SimpleGraph V} [DecidableRel G.Adj]
    {D : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) :
    (graphOfEdges D).edgeFinset = D :=
  edgeFinset_graphOfEdges (disjoint_diag_of_subset_edgeFinset hD)

lemma isHomCycle_graphOfEdges_iff {G : SimpleGraph V} [DecidableRel G.Adj]
    {D : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) {r : ℕ} [NeZero r]
    {x : Fin r → V} :
    IsHomCycle (graphOfEdges D) x ↔ ∀ i, cycleEdge x i ∈ D := by
  constructor
  · intro hx i
    exact (graphOfEdges_adj_iff.mp (hx i)).1
  · intro hx i
    have hiG : G.Adj (x i) (x (i + 1)) :=
      SimpleGraph.mem_edgeFinset.mp (hD (hx i))
    exact graphOfEdges_adj_iff.mpr ⟨hx i, hiG.ne⟩

/-- Cycles of `G` which use a specified edge. -/
noncomputable def cyclesThroughEdge (G : SimpleGraph V) (r : ℕ) [NeZero r]
    (e : Sym2 V) :
    Finset (Fin r → V) :=
  (genuineCycles G r).filter fun x ↦ ∃ i, cycleEdge x i = e

@[simp] lemma mem_cyclesThroughEdge {G : SimpleGraph V} {r : ℕ} [NeZero r]
    {e : Sym2 V} {x : Fin r → V} :
    x ∈ cyclesThroughEdge G r e ↔
      IsGenuineCycle G x ∧ ∃ i, cycleEdge x i = e := by
  classical
  simp [cyclesThroughEdge]

lemma cyclesThroughEdge_mono {G H : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (hGH : G ≤ H) (r : ℕ) [NeZero r] (e : Sym2 V) :
    cyclesThroughEdge G r e ⊆ cyclesThroughEdge H r e := by
  intro x hx
  rw [mem_cyclesThroughEdge] at hx ⊢
  exact ⟨⟨hx.1.1, fun i ↦ hGH (hx.1.2 i)⟩, hx.2⟩

end Erdos113Cycles

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Cycle56.lean` -/

section
/-!
# Ordered homomorphic 56-cycles and closed walks
-/

open scoped SimpleGraph

namespace Erdos113Cycle56

open Erdos113Cycles

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Tuple56 (V : Type*) := Fin 56 → V

abbrev ClosedWalk56 (G : SimpleGraph V) :=
  Σ v : V, Conflict.FixedWalk G 56 v v

/-- Read the first 56 vertices of a length-56 closed walk. -/
def closedWalkTuple (G : SimpleGraph V) (P : ClosedWalk56 G) : Tuple56 V :=
  fun i ↦ P.2.1.getVert i.val

lemma closedWalkTuple_isHomCycle (G : SimpleGraph V) (P : ClosedWalk56 G) :
    IsHomCycle G (closedWalkTuple G P) := by
  intro i
  have hi : i.val < P.2.1.length := by simpa [P.2.2] using i.isLt
  have h := P.2.1.adj_getVert_succ hi
  by_cases hlast : i.val + 1 < 56
  · have hadd : (i + 1 : Fin 56).val = i.val + 1 :=
      Fin.val_add_eq_of_add_lt (by simpa using hlast)
    simpa [closedWalkTuple, hadd] using h
  · have hi55 : i.val = 55 := by omega
    have hend : P.2.1.getVert 56 = P.1 := by
      simpa [P.2.2] using P.2.1.getVert_length
    have hstart : P.2.1.getVert 0 = P.1 := P.2.1.getVert_zero
    have hi' : i = (55 : Fin 56) := Fin.ext hi55
    subst i
    simpa [closedWalkTuple, hend, hstart] using h

/-- Append the initial vertex to a cyclic 56-tuple. -/
def closeSeq (x : Tuple56 V) (j : Fin 57) : V :=
  if h : j.val < 56 then x ⟨j.val, h⟩ else x 0

@[simp] lemma closeSeq_castSucc (x : Tuple56 V) (i : Fin 56) :
    closeSeq x i.castSucc = x i := by
  simp [closeSeq]

@[simp] lemma closeSeq_last (x : Tuple56 V) : closeSeq x (Fin.last 56) = x 0 := by
  simp [closeSeq]

lemma closeSeq_succ (x : Tuple56 V) (i : Fin 56) :
    closeSeq x i.succ = x (i + 1) := by
  by_cases h : i.val + 1 < 56
  · simp only [closeSeq, Fin.val_succ, h, ↓reduceDIte]
    congr 1
    apply Fin.ext
    symm
    exact Fin.val_add_eq_of_add_lt (by simpa using h)
  · have hi : i.val = 55 := by omega
    have hi' : i = (55 : Fin 56) := Fin.ext hi
    subst i
    simp [closeSeq]

lemma closeSeq_adj {G : SimpleGraph V} {x : Tuple56 V}
    (hx : IsHomCycle G x) (i : Fin 56) :
    G.Adj (closeSeq x i.castSucc) (closeSeq x i.succ) := by
  rw [closeSeq_castSucc, closeSeq_succ]
  exact hx i

/-- Turn a cyclic tuple into the corresponding closed walk. -/
def tupleClosedWalk {G : SimpleGraph V} (x : Tuple56 V) (hx : IsHomCycle G x) :
    ClosedWalk56 G := by
  let p := WF.walkOfFin 56 (closeSeq x) (closeSeq_adj hx)
  refine ⟨x 0, ⟨p.copy ?_ ?_, ?_⟩⟩
  · simp [p, closeSeq]
  · simp [p, closeSeq]
  · simp [p]

@[simp] lemma closedWalkTuple_tupleClosedWalk {G : SimpleGraph V}
    (x : Tuple56 V) (hx : IsHomCycle G x) :
    closedWalkTuple G (tupleClosedWalk x hx) = x := by
  funext i
  simp only [closedWalkTuple, tupleClosedWalk]
  rw [SimpleGraph.Walk.getVert_copy]
  simpa [closeSeq] using
    (WF.walkOfFin_getVert 56 (closeSeq x) (closeSeq_adj hx) i.val
      (Nat.le_of_lt i.isLt))

lemma closedWalkTuple_injective (G : SimpleGraph V) :
    Function.Injective (closedWalkTuple G) := by
  rintro ⟨p, P⟩ ⟨q, Q⟩ hPQ
  have hstart : p = q := by
    have h0 := congrFun hPQ 0
    simpa [closedWalkTuple] using h0
  subst q
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Subtype.ext
  apply SimpleGraph.Walk.ext_getVert_le_length
  · rw [P.2, Q.2]
  · intro i hiP
    by_cases hi : i < 56
    · have h := congrFun hPQ ⟨i, hi⟩
      simpa [closedWalkTuple] using h
    · have hiP' : i ≤ 56 := by simpa [P.2] using hiP
      have hi56 : i = 56 := by omega
      subst i
      have hp : P.1.getVert 56 = p := by
        simpa [P.2] using P.1.getVert_length
      have hq : Q.1.getVert 56 = p := by
        simpa [Q.2] using Q.1.getVert_length
      exact hp.trans hq.symm

noncomputable def closedWalkHomEquiv (G : SimpleGraph V) :
    ClosedWalk56 G ≃ {x : Tuple56 V // IsHomCycle G x} :=
  Equiv.ofBijective
    (fun P ↦ ⟨closedWalkTuple G P, closedWalkTuple_isHomCycle G P⟩)
    ⟨fun _ _ h ↦ closedWalkTuple_injective G (congrArg Subtype.val h), by
      intro x
      refine ⟨tupleClosedWalk x.1 x.2, ?_⟩
      apply Subtype.ext
      exact closedWalkTuple_tupleClosedWalk x.1 x.2⟩

lemma card_homCycle56_eq_closedWalkCount (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card {x : Tuple56 V // IsHomCycle G x} =
      Conflict.closedWalkCount G 56 := by
  rw [← Fintype.card_congr (closedWalkHomEquiv G)]
  simp only [Fintype.card_sigma, Conflict.closedWalkCount]
  rfl

end Erdos113Cycle56

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Conflict56.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Conflict56

noncomputable def walkCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) (u v : W) : ℕ :=
  Fintype.card {p : A.Walk u v // p.length = m}

noncomputable def closedWalkCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) : ℕ :=
  ∑ x : W, walkCount A m x x

lemma closedWalkCount_cast_eq_trace {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) :
    (closedWalkCount A m : ℝ) = Matrix.trace (A.adjMatrix ℝ ^ m) := by
  rw [closedWalkCount, Nat.cast_sum, Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.diag_apply, A.adjMatrix_pow_apply_eq_card_walk]
  rfl

lemma closedWalkCount_cast_eq_sum_walkCount_sq {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) :
    (closedWalkCount A (2 * m) : ℝ) =
      ∑ u : W, ∑ v : W, (walkCount A m u v : ℝ) ^ 2 := by
  rw [closedWalkCount_cast_eq_trace]
  have hpow : A.adjMatrix ℝ ^ (2 * m) =
      A.adjMatrix ℝ ^ m * A.adjMatrix ℝ ^ m := by
    rw [show 2 * m = m + m by omega, pow_add]
  rw [hpow, Matrix.trace]
  apply Finset.sum_congr rfl
  intro u _
  rw [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro v _
  rw [A.adjMatrix_pow_apply_eq_card_walk,
    A.adjMatrix_pow_apply_eq_card_walk]
  have hrev : walkCount A m v u = walkCount A m u v := by
    unfold walkCount
    apply Fintype.card_congr
    exact
      { toFun := fun p ↦ ⟨p.1.reverse, by simpa using p.2⟩
        invFun := fun p ↦ ⟨p.1.reverse, by simpa using p.2⟩
        left_inv := by intro p; apply Subtype.ext; simp
        right_inv := by intro p; apply Subtype.ext; simp }
  change (walkCount A m u v : ℝ) * (walkCount A m v u : ℝ) = _
  rw [hrev]
  ring

abbrev FixedWalk {W : Type*} (A : SimpleGraph W) (m : ℕ) (u v : W) :=
  {p : A.Walk u v // p.length = m}

def WalkConflict28 {W : Type*} {A : SimpleGraph W}
    (R : W → W → Prop) (x : W) {z y : W} (q : FixedWalk A 28 y z) : Prop :=
  ∃ i : Fin 7, ∃ j : Fin 4,
    R x (q.1.getVert (4 * i.val + j.val))

noncomputable instance instDecidableWalkConflict28 {W : Type*} {A : SimpleGraph W}
    (R : W → W → Prop) [DecidableRel R] (x : W) {z y : W}
    (q : FixedWalk A 28 y z) : Decidable (WalkConflict28 R x q) :=
  Classical.propDecidable _

noncomputable def walkConflictingNeighbors28 {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    {z y : W} (q : FixedWalk A 28 y z) : Finset W := by
  classical
  exact (A.neighborFinset y).filter fun x ↦ WalkConflict28 R x q

@[simp] lemma mem_walkConflictingNeighbors28 {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    {z y : W} (q : FixedWalk A 28 y z) (x : W) :
    x ∈ walkConflictingNeighbors28 A R q ↔
      A.Adj y x ∧ WalkConflict28 R x q := by
  classical
  simp [walkConflictingNeighbors28]

lemma card_lowFixedWalks_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (t : ℝ) (ht : 0 ≤ t)
    (z x₁ : W) (x₂ : A.neighborSet x₁) :
    (Fintype.card {q : FixedWalk A 28 x₂.1 z //
      (walkCount A 28 x₂.1 z : ℝ) <
        t * (walkCount A 27 z x₁ : ℝ)} : ℝ) ≤
      t * (walkCount A 27 z x₁ : ℝ) := by
  let T := {q : FixedWalk A 28 x₂.1 z //
    (walkCount A 28 x₂.1 z : ℝ) <
      t * (walkCount A 27 z x₁ : ℝ)}
  have hnonneg : 0 ≤ t * (walkCount A 27 z x₁ : ℝ) :=
    mul_nonneg ht (by positivity)
  cases isEmpty_or_nonempty T with
  | inl hempty =>
      have hcard : Fintype.card T = 0 := Fintype.card_eq_zero
      rw [hcard, Nat.cast_zero]
      exact hnonneg
  | inr hnonempty =>
      let q : T := Classical.choice hnonempty
      calc
        (Fintype.card T : ℝ) ≤
            (Fintype.card (FixedWalk A 28 x₂.1 z) : ℝ) := by
          exact_mod_cast Fintype.card_subtype_le (fun _q : FixedWalk A 28 x₂.1 z ↦
            (walkCount A 28 x₂.1 z : ℝ) <
              t * (walkCount A 27 z x₁ : ℝ))
        _ = (walkCount A 28 x₂.1 z : ℝ) := rfl
        _ ≤ t * (walkCount A 27 z x₁ : ℝ) := q.2.le

lemma card_highFixedWalks_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (t : ℝ) (ht : 0 < t)
    (z x₂ : W) (q : FixedWalk A 28 x₂ z)
    (x₁ : ↑(walkConflictingNeighbors28 A R q)) :
    (Fintype.card {p : FixedWalk A 27 z x₁.1 //
      t * (walkCount A 27 z x₁.1 : ℝ) ≤
        (walkCount A 28 x₂ z : ℝ)} : ℝ) ≤
      t⁻¹ * (walkCount A 28 x₂ z : ℝ) := by
  let T := {p : FixedWalk A 27 z x₁.1 //
    t * (walkCount A 27 z x₁.1 : ℝ) ≤
      (walkCount A 28 x₂ z : ℝ)}
  have hnonneg : 0 ≤ t⁻¹ * (walkCount A 28 x₂ z : ℝ) :=
    mul_nonneg (inv_nonneg.mpr ht.le) (by positivity)
  cases isEmpty_or_nonempty T with
  | inl hempty =>
      have hcard : Fintype.card T = 0 := Fintype.card_eq_zero
      rw [hcard, Nat.cast_zero]
      exact hnonneg
  | inr hnonempty =>
      let p : T := Classical.choice hnonempty
      calc
        (Fintype.card T : ℝ) ≤
            (Fintype.card (FixedWalk A 27 z x₁.1) : ℝ) := by
          exact_mod_cast Fintype.card_subtype_le (fun _p : FixedWalk A 27 z x₁.1 ↦
            t * (walkCount A 27 z x₁.1 : ℝ) ≤
              (walkCount A 28 x₂ z : ℝ))
        _ = (walkCount A 27 z x₁.1 : ℝ) := rfl
        _ ≤ t⁻¹ * (walkCount A 28 x₂ z : ℝ) := by
          rw [inv_mul_eq_div]
          exact (le_div_iff₀' ht).2 p.2

abbrev RawHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] :=
  Σ z : W, Σ x₁ : W,
    FixedWalk A 27 z x₁ ×
      Σ x₂ : A.neighborSet x₁, FixedWalk A 28 x₂.1 z

abbrev BadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :=
  {b : RawHalfCycle A // WalkConflict28 R b.2.1 b.2.2.2.2}

def eraseBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :
    BadHalfCycle A R → RawHalfCycle A
  | b => b.1

lemma eraseBadHalfCycle_injective {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :
    Function.Injective (eraseBadHalfCycle A R) := by
  exact Subtype.val_injective

end Conflict56

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Encode56.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Encode56

open Conflict56 WF

def cyclicAdd56 (i : Fin 56) (d : Nat) : Fin 56 :=
  ⟨(i.val + d) % 56, Nat.mod_lt _ (by omega)⟩

lemma cyclicAdd56_zero (i : Fin 56) : cyclicAdd56 i 0 = i := by
  apply Fin.ext
  simp [cyclicAdd56, Nat.mod_eq_of_lt i.isLt]

lemma cyclicAdd56_add (i : Fin 56) (a b : Nat) :
    cyclicAdd56 (cyclicAdd56 i a) b = cyclicAdd56 i (a + b) := by
  apply Fin.ext
  simp only [cyclicAdd56]
  omega

lemma cyclicAdd56_full (i : Fin 56) : cyclicAdd56 i 56 = i := by
  apply Fin.ext
  change (i.val + 56) % 56 = i.val
  omega

lemma exists_short_oriented_pair (i j : Fin 56) (hij : i ≠ j) :
    ∃ c : Fin 56, ∃ d : Fin 28,
      cyclicAdd56 c (d.val + 1) = j ∧ c = i ∨
      cyclicAdd56 c (d.val + 1) = i ∧ c = j := by
  by_cases hijv : i.val < j.val
  · let e := j.val - i.val
    by_cases he : e ≤ 28
    · refine ⟨i, ⟨e - 1, by dsimp [e]; omega⟩, Or.inl ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd56, e]
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    · let e' := 56 - e
      refine ⟨j, ⟨e' - 1, by dsimp [e', e]; omega⟩, Or.inr ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd56, e', e]
      omega
  · have hjiv : j.val < i.val := by
      have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
      omega
    let e := i.val - j.val
    by_cases he : e ≤ 28
    · refine ⟨j, ⟨e - 1, by dsimp [e]; omega⟩, Or.inr ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd56, e]
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    · let e' := 56 - e
      refine ⟨i, ⟨e' - 1, by dsimp [e', e]; omega⟩, Or.inl ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd56, e', e]
      omega

abbrev ClosedWalk56 {W : Type*} (A : SimpleGraph W) :=
  Σ x : W, {p : A.Walk x x // p.length = 56}

def cv {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (i : Fin 56) : W :=
  P.2.1.getVert i.val

lemma cv_adj_add_one {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (i : Fin 56) :
    A.Adj (cv P i) (cv P (cyclicAdd56 i 1)) := by
  have hi : i.val < P.2.1.length := by rw [P.2.2]; exact i.isLt
  have hadj := P.2.1.adj_getVert_succ hi
  by_cases hwrap : i.val + 1 < 56
  · simpa [cv, cyclicAdd56, Nat.mod_eq_of_lt hwrap] using hadj
  · have hilast : i.val = 55 := by omega
    have hend : P.2.1.getVert 56 = P.1 := by
      simpa only [P.2.2] using P.2.1.getVert_length
    have hstart : P.2.1.getVert 0 = P.1 := P.2.1.getVert_zero
    simpa [cv, cyclicAdd56, hilast, hend, hstart] using hadj

def qSeq {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (r : Fin 29) : W :=
  cv P (cyclicAdd56 c (r.val + 1))

lemma qSeq_adj {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (r : Fin 28) :
    A.Adj (qSeq P c r.castSucc) (qSeq P c r.succ) := by
  have h := cv_adj_add_one P (cyclicAdd56 c (r.val + 1))
  simpa only [qSeq, Fin.val_castSucc, Fin.val_succ, cyclicAdd56_add,
    show r.val + 1 + 1 = r.val + 2 by omega] using h

def qWalk {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) :
    A.Walk (qSeq P c ⟨0, by omega⟩) (qSeq P c ⟨28, by omega⟩) :=
  walkOfFin 28 (qSeq P c) (qSeq_adj P c)

@[simp] lemma qWalk_length {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) : (qWalk P c).length = 28 := by
  exact walkOfFin_length 28 (qSeq P c) (qSeq_adj P c)

lemma qWalk_getVert {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (i : Nat) (hi : i ≤ 28) :
    (qWalk P c).getVert i = cv P (cyclicAdd56 c (i + 1)) := by
  simp only [qWalk]
  exact walkOfFin_getVert 28 (qSeq P c) (qSeq_adj P c) i hi

def pSeq {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (r : Fin 28) : W :=
  cv P (cyclicAdd56 c (29 + r.val))

lemma pSeq_adj {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (r : Fin 27) :
    A.Adj (pSeq P c r.castSucc) (pSeq P c r.succ) := by
  have h := cv_adj_add_one P (cyclicAdd56 c (29 + r.val))
  simpa only [pSeq, Fin.val_castSucc, Fin.val_succ, cyclicAdd56_add,
    show 29 + r.val + 1 = 29 + (r.val + 1) by omega] using h

def pWalk {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) :
    A.Walk (pSeq P c ⟨0, by omega⟩) (pSeq P c ⟨27, by omega⟩) :=
  walkOfFin 27 (pSeq P c) (pSeq_adj P c)

@[simp] lemma pWalk_length {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) : (pWalk P c).length = 27 := by
  exact walkOfFin_length 27 (pSeq P c) (pSeq_adj P c)

lemma pWalk_getVert {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (i : Nat) (hi : i ≤ 27) :
    (pWalk P c).getVert i = cv P (cyclicAdd56 c (29 + i)) := by
  simp only [pWalk]
  exact walkOfFin_getVert 27 (pSeq P c) (pSeq_adj P c) i hi

noncomputable def makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c (d.val + 1)))) :
    BadHalfCycle A R := by
  let z := qSeq P c ⟨28, by omega⟩
  let x₁ := pSeq P c ⟨27, by omega⟩
  let p : FixedWalk A 27 z x₁ :=
    ⟨(pWalk P c).copy (by simp [z, qSeq, pSeq]) rfl, by
      rw [SimpleGraph.Walk.length_copy, pWalk_length]⟩
  let x₂ : A.neighborSet x₁ := ⟨qSeq P c ⟨0, by omega⟩, by
    have h := cv_adj_add_one P c
    simpa [x₁, qSeq, pSeq, cyclicAdd56_full] using h⟩
  let q : FixedWalk A 28 x₂.1 z := ⟨qWalk P c, qWalk_length P c⟩
  refine ⟨⟨z, x₁, p, x₂, q⟩, ?_⟩
  let i : Fin 7 := ⟨d.val / 4, by omega⟩
  let j : Fin 4 := ⟨d.val % 4, Nat.mod_lt _ (by omega)⟩
  refine ⟨i, j, ?_⟩
  have hd : 4 * i.val + j.val = d.val := by
    dsimp [i, j]
    omega
  have hq := qWalk_getVert P c d.val (Nat.le_of_lt d.isLt)
  dsimp [x₁, q]
  rw [hd, hq]
  simpa [pSeq, cyclicAdd56_full] using hR

def cyclicOffset56 (c i : Fin 56) : Nat :=
  (i.val + 56 - c.val) % 56

lemma cyclicAdd_offset (c i : Fin 56) :
    cyclicAdd56 c (cyclicOffset56 c i) = i := by
  apply Fin.ext
  simp only [cyclicAdd56, cyclicOffset56]
  omega

abbrev PackedWalk {W : Type*} (A : SimpleGraph W) :=
  Σ u : W, Σ v : W, A.Walk u v

def packedWalkVertex {W : Type*} {A : SimpleGraph W}
    (p : PackedWalk A) (i : Nat) : W := p.2.2.getVert i

def packedQ {W : Type*} [Fintype W] [DecidableEq W]
    {A : SimpleGraph W} [DecidableRel A.Adj]
    {R : W → W → Prop} [DecidableRel R]
    (b : BadHalfCycle A R) : PackedWalk A :=
  ⟨b.1.2.2.2.1.1, b.1.1, b.1.2.2.2.2.1⟩

def packedP {W : Type*} [Fintype W] [DecidableEq W]
    {A : SimpleGraph W} [DecidableRel A.Adj]
    {R : W → W → Prop} [DecidableRel R]
    (b : BadHalfCycle A R) : PackedWalk A :=
  ⟨b.1.1, b.1.2.1, b.1.2.2.1.1⟩

def decodeHalfVertex {W : Type*} [Fintype W] [DecidableEq W]
    {A : SimpleGraph W} [DecidableRel A.Adj]
    {R : W → W → Prop} [DecidableRel R]
    (c : Fin 56) (b : BadHalfCycle A R)
    (i : Fin 56) : W :=
  let d := cyclicOffset56 c i
  if d = 0 then b.1.2.1
  else if d ≤ 29 then packedWalkVertex (packedQ b) (d - 1)
  else packedWalkVertex (packedP b) (d - 29)

@[simp] lemma makeBadHalfCycle_x1 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c (d.val + 1)))) :
    (makeBadHalfCycle A R P c d hR).1.2.1 = pSeq P c ⟨27, by omega⟩ := by
  rfl

@[simp] lemma packedQ_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c (d.val + 1)))) :
    packedQ (makeBadHalfCycle A R P c d hR) =
      ⟨qSeq P c ⟨0, by omega⟩, qSeq P c ⟨28, by omega⟩, qWalk P c⟩ := by
  rfl

@[simp] lemma packedP_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c (d.val + 1)))) :
    packedP (makeBadHalfCycle A R P c d hR) =
      ⟨qSeq P c ⟨28, by omega⟩, pSeq P c ⟨27, by omega⟩,
        (pWalk P c).copy (by simp [qSeq, pSeq]) rfl⟩ := by
  rfl

lemma packedP_makeBadHalfCycle_getVert {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c (d.val + 1)))) (i : Nat) :
    packedWalkVertex (packedP (makeBadHalfCycle A R P c d hR)) i =
      (pWalk P c).getVert i := by
  unfold packedWalkVertex packedP
  dsimp [makeBadHalfCycle]
  simp only [SimpleGraph.Walk.getVert_copy]

lemma decode_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c (d.val + 1))))
    (i : Fin 56) :
    decodeHalfVertex c (makeBadHalfCycle A R P c d hR) i = cv P i := by
  let e := cyclicOffset56 c i
  have he_lt : e < 56 := Nat.mod_lt _ (by omega)
  by_cases he0 : e = 0
  · have hi : i = c := by
      have := cyclicAdd_offset c i
      symm
      simpa [e, he0, cyclicAdd56_zero] using this
    subst i
    simp [decodeHalfVertex, e, he0, pSeq,
      cyclicAdd56_full]
  · by_cases he29 : e ≤ 29
    · have hq := qWalk_getVert P c (e - 1) (by omega)
      have hadd : cyclicAdd56 c ((e - 1) + 1) = i := by
        rw [show e - 1 + 1 = e by omega]
        exact cyclicAdd_offset c i
      dsimp [e] at he0 he29 hq hadd ⊢
      simp only [decodeHalfVertex, he0, ↓reduceIte, he29]
      rw [packedQ_makeBadHalfCycle A R P c d hR]
      simp only [packedWalkVertex]
      rw [hq, hadd]
    · have hp := pWalk_getVert P c (e - 29) (by omega)
      have hadd : cyclicAdd56 c (29 + (e - 29)) = i := by
        rw [show 29 + (e - 29) = e by omega]
        exact cyclicAdd_offset c i
      dsimp [e] at he0 he29 hp hadd ⊢
      simp only [decodeHalfVertex, he0, ↓reduceIte, he29]
      rw [packedP_makeBadHalfCycle_getVert A R P c d hR, hp, hadd]

lemma closedWalk56_ext {W : Type*} {A : SimpleGraph W}
    (P Q : ClosedWalk56 A) (h : ∀ i, cv P i = cv Q i) : P = Q := by
  rcases P with ⟨x, p, hp⟩
  rcases Q with ⟨y, q, hq⟩
  have hxy : x = y := by
    have h0 := h ⟨0, by omega⟩
    simpa [cv] using h0
  subst y
  have hpq : p = q := by
    apply SimpleGraph.Walk.ext_getVert
    intro k
    by_cases hk : k < 56
    · simpa [cv] using h ⟨k, hk⟩
    · rw [p.getVert_of_length_le (by omega), q.getVert_of_length_le (by omega)]
  subst q
  rfl

abbrev BadClosedWalk56 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :=
  {P : ClosedWalk56 A // ∃ i j, i ≠ j ∧ R (cv P i) (cv P j)}

lemma exists_orientedConflict56 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) (b : BadClosedWalk56 A R) :
    ∃ c : Fin 56, ∃ d : Fin 28,
      R (cv b.1 c) (cv b.1 (cyclicAdd56 c (d.val + 1))) := by
  rcases b.2 with ⟨i, j, hij, hR⟩
  rcases exists_short_oriented_pair i j hij with ⟨c, d, h | h⟩
  · refine ⟨c, d, ?_⟩
    rw [h.1, h.2]
    exact hR
  · refine ⟨c, d, ?_⟩
    rw [h.1, h.2]
    exact hsymm _ _ hR

noncomputable def orientedConflict56 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) (b : BadClosedWalk56 A R) :
    Σ c : Fin 56, {d : Fin 28 //
      R (cv b.1 c) (cv b.1 (cyclicAdd56 c (d.val + 1)))} := by
  let c := Classical.choose (exists_orientedConflict56 A R hsymm b)
  let d := Classical.choose (Classical.choose_spec
    (exists_orientedConflict56 A R hsymm b))
  exact ⟨c, d, Classical.choose_spec (Classical.choose_spec
    (exists_orientedConflict56 A R hsymm b))⟩

noncomputable def encodeBadClosedWalk56 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    BadClosedWalk56 A R → Fin 56 × BadHalfCycle A R := fun b ↦
  let w := orientedConflict56 A R hsymm b
  ⟨w.1, makeBadHalfCycle A R b.1 w.1 w.2.1 w.2.2⟩

lemma encodeBadClosedWalk56_injective {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    Function.Injective (encodeBadClosedWalk56 A R hsymm) := by
  intro b b' hbb'
  apply Subtype.ext
  apply closedWalk56_ext
  intro i
  have hdecode := congrArg (fun z : Fin 56 × BadHalfCycle A R ↦
    decodeHalfVertex z.1 z.2 i) hbb'
  simpa only [encodeBadClosedWalk56, decode_makeBadHalfCycle] using hdecode

lemma card_BadClosedWalk56_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    Fintype.card (BadClosedWalk56 A R) ≤
      56 * Fintype.card (BadHalfCycle A R) := by
  calc
    Fintype.card (BadClosedWalk56 A R) ≤
        Fintype.card (Fin 56 × BadHalfCycle A R) :=
      Fintype.card_le_of_injective _ (encodeBadClosedWalk56_injective A R hsymm)
    _ = 56 * Fintype.card (BadHalfCycle A R) := by simp

end Encode56

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Consecutive56.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Consecutive56

noncomputable def walkCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) (u v : W) : ℕ :=
  Fintype.card {p : A.Walk u v // p.length = m}

noncomputable def closedWalkCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) : ℕ :=
  ∑ x : W, walkCount A m x x

lemma closedWalkCount_cast_eq_trace {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) :
    (closedWalkCount A m : ℝ) = Matrix.trace (A.adjMatrix ℝ ^ m) := by
  rw [closedWalkCount, Nat.cast_sum, Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.diag_apply, A.adjMatrix_pow_apply_eq_card_walk]
  rfl

lemma closedWalkCount_cast_eq_sum_walkCount_sq {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) :
    (closedWalkCount A (2 * m) : ℝ) =
      ∑ u : W, ∑ v : W, (walkCount A m u v : ℝ) ^ 2 := by
  rw [closedWalkCount_cast_eq_trace]
  have hpow : A.adjMatrix ℝ ^ (2 * m) =
      A.adjMatrix ℝ ^ m * A.adjMatrix ℝ ^ m := by
    rw [show 2 * m = m + m by omega, pow_add]
  rw [hpow, Matrix.trace]
  apply Finset.sum_congr rfl
  intro u _
  rw [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro v _
  rw [A.adjMatrix_pow_apply_eq_card_walk,
    A.adjMatrix_pow_apply_eq_card_walk]
  have hrev : walkCount A m v u = walkCount A m u v := by
    unfold walkCount
    apply Fintype.card_congr
    exact
      { toFun := fun p ↦ ⟨p.1.reverse, by simpa using p.2⟩
        invFun := fun p ↦ ⟨p.1.reverse, by simpa using p.2⟩
        left_inv := by intro p; apply Subtype.ext; simp
        right_inv := by intro p; apply Subtype.ext; simp }
  change (walkCount A m u v : ℝ) * (walkCount A m v u : ℝ) = _
  rw [hrev]
  ring

abbrev FixedWalk {W : Type*} (A : SimpleGraph W) (m : ℕ) (u v : W) :=
  {p : A.Walk u v // p.length = m}

def WalkConflict28 {W : Type*} {A : SimpleGraph W}
    (R : W → W → Prop) (x : W) {z y : W} (q : FixedWalk A 28 y z) : Prop :=
  R x (q.1.getVert 1)

noncomputable instance instDecidableWalkConflict28 {W : Type*} {A : SimpleGraph W}
    (R : W → W → Prop) [DecidableRel R] (x : W) {z y : W}
    (q : FixedWalk A 28 y z) : Decidable (WalkConflict28 R x q) :=
  Classical.propDecidable _

noncomputable def walkConflictingNeighbors28 {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    {z y : W} (q : FixedWalk A 28 y z) : Finset W := by
  classical
  exact (A.neighborFinset y).filter fun x ↦ WalkConflict28 R x q

@[simp] lemma mem_walkConflictingNeighbors28 {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    {z y : W} (q : FixedWalk A 28 y z) (x : W) :
    x ∈ walkConflictingNeighbors28 A R q ↔
      A.Adj y x ∧ WalkConflict28 R x q := by
  classical
  simp [walkConflictingNeighbors28]

lemma card_lowFixedWalks_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (t : ℝ) (ht : 0 ≤ t)
    (z x₁ : W) (x₂ : A.neighborSet x₁) :
    (Fintype.card {q : FixedWalk A 28 x₂.1 z //
      (walkCount A 28 x₂.1 z : ℝ) <
        t * (walkCount A 27 z x₁ : ℝ)} : ℝ) ≤
      t * (walkCount A 27 z x₁ : ℝ) := by
  let T := {q : FixedWalk A 28 x₂.1 z //
    (walkCount A 28 x₂.1 z : ℝ) <
      t * (walkCount A 27 z x₁ : ℝ)}
  have hnonneg : 0 ≤ t * (walkCount A 27 z x₁ : ℝ) :=
    mul_nonneg ht (by positivity)
  cases isEmpty_or_nonempty T with
  | inl hempty =>
      have hcard : Fintype.card T = 0 := Fintype.card_eq_zero
      rw [hcard, Nat.cast_zero]
      exact hnonneg
  | inr hnonempty =>
      let q : T := Classical.choice hnonempty
      calc
        (Fintype.card T : ℝ) ≤
            (Fintype.card (FixedWalk A 28 x₂.1 z) : ℝ) := by
          exact_mod_cast Fintype.card_subtype_le (fun _q : FixedWalk A 28 x₂.1 z ↦
            (walkCount A 28 x₂.1 z : ℝ) <
              t * (walkCount A 27 z x₁ : ℝ))
        _ = (walkCount A 28 x₂.1 z : ℝ) := rfl
        _ ≤ t * (walkCount A 27 z x₁ : ℝ) := q.2.le

lemma card_highFixedWalks_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (t : ℝ) (ht : 0 < t)
    (z x₂ : W) (q : FixedWalk A 28 x₂ z)
    (x₁ : ↑(walkConflictingNeighbors28 A R q)) :
    (Fintype.card {p : FixedWalk A 27 z x₁.1 //
      t * (walkCount A 27 z x₁.1 : ℝ) ≤
        (walkCount A 28 x₂ z : ℝ)} : ℝ) ≤
      t⁻¹ * (walkCount A 28 x₂ z : ℝ) := by
  let T := {p : FixedWalk A 27 z x₁.1 //
    t * (walkCount A 27 z x₁.1 : ℝ) ≤
      (walkCount A 28 x₂ z : ℝ)}
  have hnonneg : 0 ≤ t⁻¹ * (walkCount A 28 x₂ z : ℝ) :=
    mul_nonneg (inv_nonneg.mpr ht.le) (by positivity)
  cases isEmpty_or_nonempty T with
  | inl hempty =>
      have hcard : Fintype.card T = 0 := Fintype.card_eq_zero
      rw [hcard, Nat.cast_zero]
      exact hnonneg
  | inr hnonempty =>
      let p : T := Classical.choice hnonempty
      calc
        (Fintype.card T : ℝ) ≤
            (Fintype.card (FixedWalk A 27 z x₁.1) : ℝ) := by
          exact_mod_cast Fintype.card_subtype_le (fun _p : FixedWalk A 27 z x₁.1 ↦
            t * (walkCount A 27 z x₁.1 : ℝ) ≤
              (walkCount A 28 x₂ z : ℝ))
        _ = (walkCount A 27 z x₁.1 : ℝ) := rfl
        _ ≤ t⁻¹ * (walkCount A 28 x₂ z : ℝ) := by
          rw [inv_mul_eq_div]
          exact (le_div_iff₀' ht).2 p.2

abbrev RawHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] :=
  Σ z : W, Σ x₁ : W,
    FixedWalk A 27 z x₁ ×
      Σ x₂ : A.neighborSet x₁, FixedWalk A 28 x₂.1 z

abbrev BadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :=
  {b : RawHalfCycle A // WalkConflict28 R b.2.1 b.2.2.2.2}

def eraseBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :
    BadHalfCycle A R → RawHalfCycle A
  | b => b.1

lemma eraseBadHalfCycle_injective {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :
    Function.Injective (eraseBadHalfCycle A R) := by
  exact Subtype.val_injective

end Consecutive56

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/EncodeConsecutive56.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace EncodeConsecutive56

open Consecutive56 WF

def cyclicAdd56 (i : Fin 56) (d : Nat) : Fin 56 :=
  ⟨(i.val + d) % 56, Nat.mod_lt _ (by omega)⟩

lemma cyclicAdd56_zero (i : Fin 56) : cyclicAdd56 i 0 = i := by
  apply Fin.ext
  simp [cyclicAdd56, Nat.mod_eq_of_lt i.isLt]

lemma cyclicAdd56_add (i : Fin 56) (a b : Nat) :
    cyclicAdd56 (cyclicAdd56 i a) b = cyclicAdd56 i (a + b) := by
  apply Fin.ext
  simp only [cyclicAdd56]
  omega

lemma cyclicAdd56_full (i : Fin 56) : cyclicAdd56 i 56 = i := by
  apply Fin.ext
  change (i.val + 56) % 56 = i.val
  omega

lemma exists_short_oriented_pair (i j : Fin 56) (hij : i ≠ j) :
    ∃ c : Fin 56, ∃ d : Fin 28,
      cyclicAdd56 c (d.val + 1) = j ∧ c = i ∨
      cyclicAdd56 c (d.val + 1) = i ∧ c = j := by
  by_cases hijv : i.val < j.val
  · let e := j.val - i.val
    by_cases he : e ≤ 28
    · refine ⟨i, ⟨e - 1, by dsimp [e]; omega⟩, Or.inl ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd56, e]
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    · let e' := 56 - e
      refine ⟨j, ⟨e' - 1, by dsimp [e', e]; omega⟩, Or.inr ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd56, e', e]
      omega
  · have hjiv : j.val < i.val := by
      have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
      omega
    let e := i.val - j.val
    by_cases he : e ≤ 28
    · refine ⟨j, ⟨e - 1, by dsimp [e]; omega⟩, Or.inr ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd56, e]
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    · let e' := 56 - e
      refine ⟨i, ⟨e' - 1, by dsimp [e', e]; omega⟩, Or.inl ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd56, e', e]
      omega

abbrev ClosedWalk56 {W : Type*} (A : SimpleGraph W) :=
  Σ x : W, {p : A.Walk x x // p.length = 56}

def cv {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (i : Fin 56) : W :=
  P.2.1.getVert i.val

lemma cv_adj_add_one {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (i : Fin 56) :
    A.Adj (cv P i) (cv P (cyclicAdd56 i 1)) := by
  have hi : i.val < P.2.1.length := by rw [P.2.2]; exact i.isLt
  have hadj := P.2.1.adj_getVert_succ hi
  by_cases hwrap : i.val + 1 < 56
  · simpa [cv, cyclicAdd56, Nat.mod_eq_of_lt hwrap] using hadj
  · have hilast : i.val = 55 := by omega
    have hend : P.2.1.getVert 56 = P.1 := by
      simpa only [P.2.2] using P.2.1.getVert_length
    have hstart : P.2.1.getVert 0 = P.1 := P.2.1.getVert_zero
    simpa [cv, cyclicAdd56, hilast, hend, hstart] using hadj

def qSeq {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (r : Fin 29) : W :=
  cv P (cyclicAdd56 c (r.val + 1))

lemma qSeq_adj {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (r : Fin 28) :
    A.Adj (qSeq P c r.castSucc) (qSeq P c r.succ) := by
  have h := cv_adj_add_one P (cyclicAdd56 c (r.val + 1))
  simpa only [qSeq, Fin.val_castSucc, Fin.val_succ, cyclicAdd56_add,
    show r.val + 1 + 1 = r.val + 2 by omega] using h

def qWalk {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) :
    A.Walk (qSeq P c ⟨0, by omega⟩) (qSeq P c ⟨28, by omega⟩) :=
  walkOfFin 28 (qSeq P c) (qSeq_adj P c)

@[simp] lemma qWalk_length {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) : (qWalk P c).length = 28 := by
  exact walkOfFin_length 28 (qSeq P c) (qSeq_adj P c)

lemma qWalk_getVert {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (i : Nat) (hi : i ≤ 28) :
    (qWalk P c).getVert i = cv P (cyclicAdd56 c (i + 1)) := by
  simp only [qWalk]
  exact walkOfFin_getVert 28 (qSeq P c) (qSeq_adj P c) i hi

def pSeq {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (r : Fin 28) : W :=
  cv P (cyclicAdd56 c (29 + r.val))

lemma pSeq_adj {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (r : Fin 27) :
    A.Adj (pSeq P c r.castSucc) (pSeq P c r.succ) := by
  have h := cv_adj_add_one P (cyclicAdd56 c (29 + r.val))
  simpa only [pSeq, Fin.val_castSucc, Fin.val_succ, cyclicAdd56_add,
    show 29 + r.val + 1 = 29 + (r.val + 1) by omega] using h

def pWalk {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) :
    A.Walk (pSeq P c ⟨0, by omega⟩) (pSeq P c ⟨27, by omega⟩) :=
  walkOfFin 27 (pSeq P c) (pSeq_adj P c)

@[simp] lemma pWalk_length {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) : (pWalk P c).length = 27 := by
  exact walkOfFin_length 27 (pSeq P c) (pSeq_adj P c)

lemma pWalk_getVert {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (i : Nat) (hi : i ≤ 27) :
    (pWalk P c).getVert i = cv P (cyclicAdd56 c (29 + i)) := by
  simp only [pWalk]
  exact walkOfFin_getVert 27 (pSeq P c) (pSeq_adj P c) i hi

noncomputable def makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c 2))) :
    BadHalfCycle A R := by
  let z := qSeq P c ⟨28, by omega⟩
  let x₁ := pSeq P c ⟨27, by omega⟩
  let p : FixedWalk A 27 z x₁ :=
    ⟨(pWalk P c).copy (by simp [z, qSeq, pSeq]) rfl, by
      rw [SimpleGraph.Walk.length_copy, pWalk_length]⟩
  let x₂ : A.neighborSet x₁ := ⟨qSeq P c ⟨0, by omega⟩, by
    have h := cv_adj_add_one P c
    simpa [x₁, qSeq, pSeq, cyclicAdd56_full] using h⟩
  let q : FixedWalk A 28 x₂.1 z := ⟨qWalk P c, qWalk_length P c⟩
  refine ⟨⟨z, x₁, p, x₂, q⟩, ?_⟩
  have hq := qWalk_getVert P c 1 (by omega)
  change R (pSeq P c ⟨27, by omega⟩) ((qWalk P c).getVert 1)
  rw [hq]
  simpa [pSeq, cyclicAdd56_full] using hR

def cyclicOffset56 (c i : Fin 56) : Nat :=
  (i.val + 56 - c.val) % 56

lemma cyclicAdd_offset (c i : Fin 56) :
    cyclicAdd56 c (cyclicOffset56 c i) = i := by
  apply Fin.ext
  simp only [cyclicAdd56, cyclicOffset56]
  omega

abbrev PackedWalk {W : Type*} (A : SimpleGraph W) :=
  Σ u : W, Σ v : W, A.Walk u v

def packedWalkVertex {W : Type*} {A : SimpleGraph W}
    (p : PackedWalk A) (i : Nat) : W := p.2.2.getVert i

def packedQ {W : Type*} [Fintype W] [DecidableEq W]
    {A : SimpleGraph W} [DecidableRel A.Adj]
    {R : W → W → Prop} [DecidableRel R]
    (b : BadHalfCycle A R) : PackedWalk A :=
  ⟨b.1.2.2.2.1.1, b.1.1, b.1.2.2.2.2.1⟩

def packedP {W : Type*} [Fintype W] [DecidableEq W]
    {A : SimpleGraph W} [DecidableRel A.Adj]
    {R : W → W → Prop} [DecidableRel R]
    (b : BadHalfCycle A R) : PackedWalk A :=
  ⟨b.1.1, b.1.2.1, b.1.2.2.1.1⟩

def decodeHalfVertex {W : Type*} [Fintype W] [DecidableEq W]
    {A : SimpleGraph W} [DecidableRel A.Adj]
    {R : W → W → Prop} [DecidableRel R]
    (c : Fin 56) (b : BadHalfCycle A R)
    (i : Fin 56) : W :=
  let d := cyclicOffset56 c i
  if d = 0 then b.1.2.1
  else if d ≤ 29 then packedWalkVertex (packedQ b) (d - 1)
  else packedWalkVertex (packedP b) (d - 29)

@[simp] lemma makeBadHalfCycle_x1 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c 2))) :
    (makeBadHalfCycle A R P c d hR).1.2.1 = pSeq P c ⟨27, by omega⟩ := by
  rfl

@[simp] lemma packedQ_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c 2))) :
    packedQ (makeBadHalfCycle A R P c d hR) =
      ⟨qSeq P c ⟨0, by omega⟩, qSeq P c ⟨28, by omega⟩, qWalk P c⟩ := by
  rfl

@[simp] lemma packedP_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c 2))) :
    packedP (makeBadHalfCycle A R P c d hR) =
      ⟨qSeq P c ⟨28, by omega⟩, pSeq P c ⟨27, by omega⟩,
        (pWalk P c).copy (by simp [qSeq, pSeq]) rfl⟩ := by
  rfl

lemma packedP_makeBadHalfCycle_getVert {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c 2))) (i : Nat) :
    packedWalkVertex (packedP (makeBadHalfCycle A R P c d hR)) i =
      (pWalk P c).getVert i := by
  unfold packedWalkVertex packedP
  dsimp [makeBadHalfCycle]
  simp only [SimpleGraph.Walk.getVert_copy]

lemma decode_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c 2)))
    (i : Fin 56) :
    decodeHalfVertex c (makeBadHalfCycle A R P c d hR) i = cv P i := by
  let e := cyclicOffset56 c i
  have he_lt : e < 56 := Nat.mod_lt _ (by omega)
  by_cases he0 : e = 0
  · have hi : i = c := by
      have := cyclicAdd_offset c i
      symm
      simpa [e, he0, cyclicAdd56_zero] using this
    subst i
    simp [decodeHalfVertex, e, he0, pSeq,
      cyclicAdd56_full]
  · by_cases he29 : e ≤ 29
    · have hq := qWalk_getVert P c (e - 1) (by omega)
      have hadd : cyclicAdd56 c ((e - 1) + 1) = i := by
        rw [show e - 1 + 1 = e by omega]
        exact cyclicAdd_offset c i
      dsimp [e] at he0 he29 hq hadd ⊢
      simp only [decodeHalfVertex, he0, ↓reduceIte, he29]
      rw [packedQ_makeBadHalfCycle A R P c d hR]
      simp only [packedWalkVertex]
      rw [hq, hadd]
    · have hp := pWalk_getVert P c (e - 29) (by omega)
      have hadd : cyclicAdd56 c (29 + (e - 29)) = i := by
        rw [show 29 + (e - 29) = e by omega]
        exact cyclicAdd_offset c i
      dsimp [e] at he0 he29 hp hadd ⊢
      simp only [decodeHalfVertex, he0, ↓reduceIte, he29]
      rw [packedP_makeBadHalfCycle_getVert A R P c d hR, hp, hadd]

lemma closedWalk56_ext {W : Type*} {A : SimpleGraph W}
    (P Q : ClosedWalk56 A) (h : ∀ i, cv P i = cv Q i) : P = Q := by
  rcases P with ⟨x, p, hp⟩
  rcases Q with ⟨y, q, hq⟩
  have hxy : x = y := by
    have h0 := h ⟨0, by omega⟩
    simpa [cv] using h0
  subst y
  have hpq : p = q := by
    apply SimpleGraph.Walk.ext_getVert
    intro k
    by_cases hk : k < 56
    · simpa [cv] using h ⟨k, hk⟩
    · rw [p.getVert_of_length_le (by omega), q.getVert_of_length_le (by omega)]
  subst q
  rfl

abbrev BadClosedWalk56 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :=
  {P : ClosedWalk56 A // ∃ i, R (cv P i) (cv P (cyclicAdd56 i 2))}

lemma exists_orientedConflict56 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) (b : BadClosedWalk56 A R) :
    ∃ c : Fin 56, ∃ d : Fin 28,
      R (cv b.1 c) (cv b.1 (cyclicAdd56 c 2)) := by
  obtain ⟨c, hc⟩ := b.2
  exact ⟨c, 0, hc⟩

noncomputable def orientedConflict56 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) (b : BadClosedWalk56 A R) :
    Σ c : Fin 56, {d : Fin 28 //
      R (cv b.1 c) (cv b.1 (cyclicAdd56 c 2))} := by
  let c := Classical.choose (exists_orientedConflict56 A R hsymm b)
  let d := Classical.choose (Classical.choose_spec
    (exists_orientedConflict56 A R hsymm b))
  exact ⟨c, d, Classical.choose_spec (Classical.choose_spec
    (exists_orientedConflict56 A R hsymm b))⟩

noncomputable def encodeBadClosedWalk56 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    BadClosedWalk56 A R → Fin 56 × BadHalfCycle A R := fun b ↦
  let w := orientedConflict56 A R hsymm b
  ⟨w.1, makeBadHalfCycle A R b.1 w.1 w.2.1 w.2.2⟩

lemma encodeBadClosedWalk56_injective {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    Function.Injective (encodeBadClosedWalk56 A R hsymm) := by
  intro b b' hbb'
  apply Subtype.ext
  apply closedWalk56_ext
  intro i
  have hdecode := congrArg (fun z : Fin 56 × BadHalfCycle A R ↦
    decodeHalfVertex z.1 z.2 i) hbb'
  simpa only [encodeBadClosedWalk56, decode_makeBadHalfCycle] using hdecode

lemma card_BadClosedWalk56_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    Fintype.card (BadClosedWalk56 A R) ≤
      56 * Fintype.card (BadHalfCycle A R) := by
  calc
    Fintype.card (BadClosedWalk56 A R) ≤
        Fintype.card (Fin 56 × BadHalfCycle A R) :=
      Fintype.card_le_of_injective _ (encodeBadClosedWalk56_injective A R hsymm)
    _ = 56 * Fintype.card (BadHalfCycle A R) := by simp

end EncodeConsecutive56

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/FourCycles.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Erdos113FourCycles

open Erdos113Cycles

variable {V : Type*} [Fintype V] [DecidableEq V]

def commonNeighborFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : Finset V :=
  G.neighborFinset u ∩ G.neighborFinset v

def codegree (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℕ :=
  (commonNeighborFinset G u v).card

@[simp] lemma mem_commonNeighborFinset {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v w : V} :
    w ∈ commonNeighborFinset G u v ↔ G.Adj u w ∧ G.Adj v w := by
  simp [commonNeighborFinset, SimpleGraph.mem_neighborFinset]

/-- Ordered choices of the two other vertices of a four-cycle containing
the oriented edge `u-y`.  The first coordinate is the other neighbor of
`y`; the second is the other common neighbor of `u` and that vertex. -/
noncomputable def extensionsThroughEdge (G : SimpleGraph V)
    [DecidableRel G.Adj] (u y : V) : Finset (Σ _x : V, V) := by
  classical
  exact ((G.neighborFinset y).erase u).sigma fun x ↦
    (commonNeighborFinset G u x).erase y

@[simp] lemma mem_extensionsThroughEdge
    {G : SimpleGraph V} [DecidableRel G.Adj] {u y : V} {p : Σ _x : V, V} :
    p ∈ extensionsThroughEdge G u y ↔
      G.Adj y p.1 ∧ p.1 ≠ u ∧ G.Adj u p.2 ∧
        G.Adj p.1 p.2 ∧ p.2 ≠ y := by
  classical
  simp only [extensionsThroughEdge, Finset.mem_sigma, Finset.mem_erase,
    SimpleGraph.mem_neighborFinset, mem_commonNeighborFinset]
  aesop

def extensionCycleTuple (u y : V) (p : Σ _x : V, V) : Fin 4 → V :=
  ![y, u, p.2, p.1]

lemma extensionCycleTuple_genuine
    {G : SimpleGraph V} [DecidableRel G.Adj] {u y : V} {p : Σ _x : V, V}
    (huy : G.Adj y u) (hp : p ∈ extensionsThroughEdge G u y) :
    IsGenuineCycle G (extensionCycleTuple u y p) := by
  have h := mem_extensionsThroughEdge.mp hp
  have hyu : y ≠ u := huy.ne
  have hyx : y ≠ p.1 := h.1.ne
  have hux : u ≠ p.1 := h.2.1.symm
  have huz : u ≠ p.2 := h.2.2.1.ne
  have hxz : p.1 ≠ p.2 := h.2.2.2.1.ne
  have hyz : y ≠ p.2 := h.2.2.2.2.symm
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [extensionCycleTuple]
  · intro i
    fin_cases i
    · exact huy
    · exact h.2.2.1
    · exact h.2.2.2.1.symm
    · exact h.1.symm

noncomputable def extensionToCycleThroughEdge
    (G : SimpleGraph V) [DecidableRel G.Adj] (u y : V) (huy : G.Adj y u) :
    ↑(extensionsThroughEdge G u y) →
      ↑(cyclesThroughEdge G 4 s(u, y)) := fun p ↦ by
  refine ⟨extensionCycleTuple u y p.1, ?_⟩
  rw [mem_cyclesThroughEdge]
  refine ⟨extensionCycleTuple_genuine huy p.2, ⟨0, ?_⟩⟩
  simp [cycleEdge, extensionCycleTuple, Sym2.eq_swap]

lemma extensionToCycleThroughEdge_injective
    (G : SimpleGraph V) [DecidableRel G.Adj] (u y : V) (huy : G.Adj y u) :
    Function.Injective (extensionToCycleThroughEdge G u y huy) := by
  intro p q hpq
  apply Subtype.ext
  apply Sigma.ext
  · have ht := congrArg Subtype.val hpq
    change extensionCycleTuple u y p.1 = extensionCycleTuple u y q.1 at ht
    have h := congrFun ht (3 : Fin 4)
    simpa [extensionCycleTuple] using h
  · apply heq_of_eq
    have ht := congrArg Subtype.val hpq
    change extensionCycleTuple u y p.1 = extensionCycleTuple u y q.1 at ht
    have h := congrFun ht (2 : Fin 4)
    simpa [extensionCycleTuple] using h

lemma card_extensionsThroughEdge_le_cyclesThroughEdge
    (G : SimpleGraph V) [DecidableRel G.Adj] (u y : V) (huy : G.Adj y u) :
    (extensionsThroughEdge G u y).card ≤
      (cyclesThroughEdge G 4 s(u, y)).card := by
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective
    (extensionToCycleThroughEdge G u y huy)
    (extensionToCycleThroughEdge_injective G u y huy)

def highCodegreeNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (u y : V) : Finset V :=
  (G.neighborFinset y).filter fun x ↦ u ≠ x ∧ s < codegree G u x

@[simp] lemma mem_highCodegreeNeighbors {G : SimpleGraph V} [DecidableRel G.Adj]
    {s : ℕ} {u y x : V} :
    x ∈ highCodegreeNeighbors G s u y ↔
      G.Adj y x ∧ u ≠ x ∧ s < codegree G u x := by
  simp [highCodegreeNeighbors, SimpleGraph.mem_neighborFinset]

lemma card_highCodegreeNeighbors_mul_le_extensionsThroughEdge
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) {u y : V}
    (huy : G.Adj y u) :
    (highCodegreeNeighbors G s u y).card * s ≤
      (extensionsThroughEdge G u y).card := by
  classical
  let S := highCodegreeNeighbors G s u y
  let T := (G.neighborFinset y).erase u
  let f (x : V) := (commonNeighborFinset G u x).erase y
  have hST : S ⊆ T := by
    intro x hx
    have hx' := mem_highCodegreeNeighbors.mp hx
    exact Finset.mem_erase.mpr ⟨hx'.2.1.symm, by
      simpa [SimpleGraph.mem_neighborFinset] using hx'.1⟩
  have hf (x : V) (hx : x ∈ S) : s ≤ (f x).card := by
    have hx' := mem_highCodegreeNeighbors.mp hx
    have hy : y ∈ commonNeighborFinset G u x := by
      rw [mem_commonNeighborFinset]
      exact ⟨huy.symm, hx'.1.symm⟩
    have herase := Finset.card_erase_add_one hy
    change ((commonNeighborFinset G u x).erase y).card + 1 =
      (commonNeighborFinset G u x).card at herase
    have hhigh := hx'.2.2
    change s < (commonNeighborFinset G u x).card at hhigh
    change s ≤ ((commonNeighborFinset G u x).erase y).card
    omega
  rw [extensionsThroughEdge, Finset.card_sigma]
  change S.card * s ≤ ∑ x ∈ T, (f x).card
  calc
    S.card * s = ∑ _x ∈ S, s := by simp
    _ ≤ ∑ x ∈ S, (f x).card := by
      apply Finset.sum_le_sum
      intro x hx
      exact hf x hx
    _ ≤ ∑ x ∈ T, (f x).card :=
      Finset.sum_le_sum_of_subset hST

lemma card_highCodegreeNeighbors_cast_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) {u y : V}
    (hs : 0 < s) (huy : G.Adj y u) (Q : ℝ)
    (hcap : ((extensionsThroughEdge G u y).card : ℝ) ≤ Q) :
    ((highCodegreeNeighbors G s u y).card : ℝ) ≤ Q / s := by
  have hmulNat :=
    card_highCodegreeNeighbors_mul_le_extensionsThroughEdge G s huy
  have hmul : ((highCodegreeNeighbors G s u y).card : ℝ) * s ≤ Q := by
    calc
      ((highCodegreeNeighbors G s u y).card : ℝ) * s =
          (((highCodegreeNeighbors G s u y).card * s : ℕ) : ℝ) := by
        norm_num
      _ ≤ ((extensionsThroughEdge G u y).card : ℝ) := by
        exact_mod_cast hmulNat
      _ ≤ Q := hcap
  exact (le_div_iff₀ (by exact_mod_cast hs)).2 hmul

end Erdos113FourCycles

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Moments56.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Erdos113Moments56

lemma trace_pow_eq_sum_eigenvalues_pow {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (j : ℕ) :
    Matrix.trace (A ^ j) = ∑ i, hA.eigenvalues i ^ j := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle]
  simp [Matrix.diagonal_pow]

lemma closedWalkCount_cast_eq_sum_eigenvalues_pow {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) :
    (Conflict56.closedWalkCount A m : ℝ) =
      ∑ i, ((A.isHermitian_adjMatrix ℝ).eigenvalues i) ^ m := by
  rw [Conflict56.closedWalkCount_cast_eq_trace]
  exact trace_pow_eq_sum_eigenvalues_pow _ _ _

/-- The `L²⁷`--`L²²⁸` interpolation used after cutting a
56-step closed walk into pieces of lengths 27 and 28. -/
lemma closedWalkCount_interpolation_28 {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj] :
    (Conflict56.closedWalkCount A 54 : ℝ) ≤
      (Fintype.card W : ℝ) ^ ((1 : ℝ) / 28) *
        (Conflict56.closedWalkCount A 56 : ℝ) ^ ((27 : ℝ) / 28) := by
  let hA := A.isHermitian_adjMatrix ℝ
  let lam : W → ℝ := hA.eigenvalues
  have hholder : Real.HolderConjugate (28 : ℝ) ((28 : ℝ) / 27) := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg
    (s := Finset.univ) (f := fun _ : W ↦ (1 : ℝ))
    (g := fun i : W ↦ (lam i ^ 2) ^ (27 : ℕ)) hholder
    (by intro i hi; positivity) (by intro i hi; positivity)
  dsimp [hA, lam] at hh
  have hleft (x : ℝ) : x ^ 54 = (x ^ 2) ^ 27 := by ring
  have hright (x : ℝ) :
      ((x ^ 2) ^ (27 : ℕ)) ^ ((28 : ℝ) / 27) = x ^ 56 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (sq_nonneg x)]
    norm_num
    ring
  simp_rw [hright] at hh
  simp_rw [← hleft] at hh
  rw [closedWalkCount_cast_eq_sum_eigenvalues_pow,
    closedWalkCount_cast_eq_sum_eigenvalues_pow]
  simp only [one_mul, Real.one_rpow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hh
  convert hh using 1 <;> norm_num

end Erdos113Moments56

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/CyclePruning.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Erdos113CyclePruning

open Erdos113Cycles
open Erdos113FourCycles

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def orderedFourCycles (D : Finset (Sym2 V)) :
    Finset (Fin 4 → V) :=
  genuineCycles (graphOfEdges D) 4

noncomputable def orderedFourCyclesThroughEdge
    (D : Finset (Sym2 V)) (e : Sym2 V) : Finset (Fin 4 → V) :=
  cyclesThroughEdge (graphOfEdges D) 4 e

@[simp] lemma mem_orderedFourCycles {D : Finset (Sym2 V)} {x : Fin 4 → V} :
    x ∈ orderedFourCycles D ↔ IsGenuineCycle (graphOfEdges D) x := by
  simp [orderedFourCycles]

@[simp] lemma mem_orderedFourCyclesThroughEdge
    {D : Finset (Sym2 V)} {e : Sym2 V} {x : Fin 4 → V} :
    x ∈ orderedFourCyclesThroughEdge D e ↔
      IsGenuineCycle (graphOfEdges D) x ∧ ∃ i, cycleEdge x i = e := by
  simp [orderedFourCyclesThroughEdge]

lemma orderedFourCyclesThroughEdge_subset
    (D : Finset (Sym2 V)) (e : Sym2 V) :
    orderedFourCyclesThroughEdge D e ⊆ orderedFourCycles D := by
  intro x hx
  exact mem_orderedFourCycles.mpr
    (mem_orderedFourCyclesThroughEdge.mp hx).1

lemma orderedFourCycles_erase_edge
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {D : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) {e : Sym2 V} (he : e ∈ D) :
    orderedFourCycles (D.erase e) =
      orderedFourCycles D \ orderedFourCyclesThroughEdge D e := by
  classical
  ext x
  rw [Finset.mem_sdiff, mem_orderedFourCycles,
    mem_orderedFourCycles, mem_orderedFourCyclesThroughEdge]
  have hDerase : D.erase e ⊆ G.edgeFinset := (Finset.erase_subset _ _).trans hD
  rw [IsGenuineCycle, IsGenuineCycle,
    isHomCycle_graphOfEdges_iff hDerase,
    isHomCycle_graphOfEdges_iff hD]
  constructor
  · rintro ⟨hinj, hedge⟩
    refine ⟨⟨hinj, fun i ↦ Finset.mem_of_mem_erase (hedge i)⟩, ?_⟩
    rintro ⟨_hgen, i, hi⟩
    exact (Finset.mem_erase.mp (hedge i)).1 hi
  · rintro ⟨⟨hinj, hedge⟩, hnot⟩
    refine ⟨hinj, fun i ↦ Finset.mem_erase.mpr ⟨?_, hedge i⟩⟩
    intro hi
    exact hnot ⟨⟨hinj, hedge⟩, i, hi⟩

lemma card_orderedFourCycles_erase_add_through
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {D : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) {e : Sym2 V} (he : e ∈ D) :
    (orderedFourCycles (D.erase e)).card +
        (orderedFourCyclesThroughEdge D e).card =
      (orderedFourCycles D).card := by
  rw [orderedFourCycles_erase_edge hD he]
  exact Finset.card_sdiff_add_card_eq_card
    (orderedFourCyclesThroughEdge_subset D e)

lemma card_orderedFourCycles_le (D : Finset (Sym2 V)) :
    (orderedFourCycles D).card ≤ (Fintype.card V) ^ 4 := by
  calc
    (orderedFourCycles D).card ≤ Fintype.card (Fin 4 → V) := by
      simpa using Finset.card_le_card (Finset.subset_univ (s := orderedFourCycles D))
    _ = (Fintype.card V) ^ 4 := by simp

/-- Repeatedly remove an edge carried by at least `K` ordered four-cycles.
The number of removed edges, times `K`, is paid for by the ordered
four-cycles that disappear. -/
theorem exists_pruned_subset
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : ℕ) :
    ∀ E : Finset (Sym2 V), E ⊆ G.edgeFinset →
      ∃ D : Finset (Sym2 V),
        D ⊆ E ∧
        (E \ D).card * K + (orderedFourCycles D).card ≤
          (orderedFourCycles E).card ∧
        ∀ e ∈ D, (orderedFourCyclesThroughEdge D e).card < K := by
  classical
  intro E
  induction E using Finset.strongInductionOn with
  | _ E ih =>
      intro hE
      by_cases hgood :
          ∀ e ∈ E, (orderedFourCyclesThroughEdge E e).card < K
      · exact ⟨E, Finset.Subset.rfl, by simp, hgood⟩
      · push_neg at hgood
        obtain ⟨e, he, hload⟩ := hgood
        have hproper : E.erase e ⊂ E := Finset.erase_ssubset he
        have hEraseG : E.erase e ⊆ G.edgeFinset :=
          (Finset.erase_subset e E).trans hE
        obtain ⟨D, hDErase, hpaid, hDgood⟩ :=
          ih (E.erase e) hproper hEraseG
        have hDE : D ⊆ E := hDErase.trans (Finset.erase_subset e E)
        have heD : e ∉ D := by
          intro heMem
          exact (Finset.mem_erase.mp (hDErase heMem)).1 rfl
        have heDiff : e ∉ (E.erase e \ D) := by simp
        have hdiff : E \ D = insert e (E.erase e \ D) := by
          ext z
          by_cases hze : z = e <;> simp_all
        have hcycle := card_orderedFourCycles_erase_add_through hE he
        refine ⟨D, hDE, ?_, hDgood⟩
        rw [hdiff, Finset.card_insert_of_notMem heDiff]
        simp only [add_mul, one_mul]
        omega

end Erdos113CyclePruning

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/ConflictSides56.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Erdos113Sides56

open Conflict56

abbrev LowHalfCycleSide {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (b : Bool) (t : ℝ) :=
  Σ z : W, Σ x₁ : {x : W // side x = b},
    FixedWalk A 27 z x₁.1 ×
      Σ x₂ : A.neighborSet x₁.1,
        {q : FixedWalk A 28 x₂.1 z //
          (walkCount A 28 x₂.1 z : ℝ) <
            t * (walkCount A 27 z x₁.1 : ℝ)}

abbrev HighBadHalfCycleSide {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (b : Bool) (t : ℝ) :=
  Σ z : W, Σ x₂ : {x : W // side x = !b},
    Σ q : FixedWalk A 28 x₂.1 z,
      Σ x₁ : {x : ↑(walkConflictingNeighbors28 A R q) // side x.1 = b},
        {p : FixedWalk A 27 z x₁.1.1 //
          t * (walkCount A 27 z x₁.1.1 : ℝ) ≤
            (walkCount A 28 x₂.1 z : ℝ)}

lemma card_LowHalfCycleSide_cast {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (b : Bool) (t : ℝ) :
    (Fintype.card (LowHalfCycleSide A side b t) : ℝ) =
      ∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 27 z x₁.1 : ℝ) *
          ∑ x₂ : A.neighborSet x₁.1,
            (Fintype.card {q : FixedWalk A 28 x₂.1 z //
              (walkCount A 28 x₂.1 z : ℝ) <
                t * (walkCount A 27 z x₁.1 : ℝ)} : ℝ) := by
  simp only [LowHalfCycleSide, Fintype.card_sigma, Fintype.card_prod,
    Nat.cast_sum, Nat.cast_mul]
  rfl

lemma card_LowHalfCycleSide_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (b : Bool) (t D : ℝ) (ht : 0 ≤ t) (hD : 0 ≤ D)
    (hdegree : ∀ x, side x = b → (A.degree x : ℝ) ≤ D) :
    (Fintype.card (LowHalfCycleSide A side b t) : ℝ) ≤
      D * t * (closedWalkCount A 54 : ℝ) := by
  rw [card_LowHalfCycleSide_cast]
  calc
    (∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 27 z x₁.1 : ℝ) *
          ∑ x₂ : A.neighborSet x₁.1,
            (Fintype.card {q : FixedWalk A 28 x₂.1 z //
              (walkCount A 28 x₂.1 z : ℝ) <
                t * (walkCount A 27 z x₁.1 : ℝ)} : ℝ)) ≤
      ∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 27 z x₁.1 : ℝ) *
          (D * (t * (walkCount A 27 z x₁.1 : ℝ))) := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro x₁ _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        (∑ x₂ : A.neighborSet x₁.1,
            (Fintype.card {q : FixedWalk A 28 x₂.1 z //
              (walkCount A 28 x₂.1 z : ℝ) <
                t * (walkCount A 27 z x₁.1 : ℝ)} : ℝ)) ≤
            ∑ _x₂ : A.neighborSet x₁.1,
              t * (walkCount A 27 z x₁.1 : ℝ) := by
          apply Finset.sum_le_sum
          intro x₂ _
          exact card_lowFixedWalks_le A t ht z x₁.1 x₂
        _ = (A.degree x₁.1 : ℝ) *
              (t * (walkCount A 27 z x₁.1 : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            SimpleGraph.card_neighborSet_eq_degree, Nat.cast_mul]
        _ ≤ D * (t * (walkCount A 27 z x₁.1 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right (hdegree x₁.1 x₁.2)
            (mul_nonneg ht (by positivity))
    _ = D * t * (∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 27 z x₁.1 : ℝ) ^ 2) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x₁ _
      ring
    _ ≤ D * t * (∑ z : W, ∑ x₁ : W,
        (walkCount A 27 z x₁ : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD ht)
      apply Finset.sum_le_sum
      intro z _
      rw [← Finset.sum_subtype (Finset.univ.filter fun x : W ↦ side x = b)
        (by simp) (fun x ↦ (walkCount A 27 z x : ℝ) ^ 2)]
      apply Finset.sum_le_sum_of_subset_of_nonneg (by simp)
      intro x _ _
      positivity
    _ = D * t * (closedWalkCount A 54 : ℝ) := by
      rw [show 54 = 2 * 27 by norm_num,
        closedWalkCount_cast_eq_sum_walkCount_sq]

lemma card_walkConflictingNeighbors28_le_at {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (s : ℝ)
    (hsymm : ∀ x y, R x y → R y x)
    {z y : W} (q : FixedWalk A 28 y z)
    (hlocal : ∀ u,
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s) :
    ((walkConflictingNeighbors28 A R q).card : ℝ) ≤ 28 * s := by
  classical
  let E (i : Fin 7) (j : Fin 4) :=
    (A.neighborFinset y).filter (R (q.1.getVert (4 * i.val + j.val)))
  let U := Finset.univ.biUnion fun i : Fin 7 ↦ Finset.univ.biUnion (E i)
  have hsubset : walkConflictingNeighbors28 A R q ⊆ U := by
    intro x hx
    rw [walkConflictingNeighbors28, Finset.mem_filter] at hx
    have hconf := hx.2
    change ∃ i : Fin 7, ∃ j : Fin 4,
      R x (q.1.getVert (4 * i.val + j.val)) at hconf
    obtain ⟨i, j, hi⟩ := hconf
    simp only [U, Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ _, j, Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr ⟨hx.1, hsymm _ _ hi⟩
  calc
    ((walkConflictingNeighbors28 A R q).card : ℝ) ≤ (U.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ i : Fin 7, ∑ j : Fin 4, ((E i j).card : ℝ) := by
      calc
        (U.card : ℝ) ≤
            ∑ i : Fin 7, (((Finset.univ.biUnion (E i)).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ i : Fin 7, ∑ j : Fin 4, ((E i j).card : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin 7, ∑ _j : Fin 4, s := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact hlocal _
    _ = 28 * s := by simp; ring

lemma card_HighBadHalfCycleSide_cast {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (b : Bool) (t : ℝ) :
    (Fintype.card (HighBadHalfCycleSide A R side b t) : ℝ) =
      ∑ z : W, ∑ x₂ : {x : W // side x = !b},
        ∑ q : FixedWalk A 28 x₂.1 z,
          ∑ x₁ : {x : ↑(walkConflictingNeighbors28 A R q) // side x.1 = b},
            (Fintype.card {p : FixedWalk A 27 z x₁.1.1 //
              t * (walkCount A 27 z x₁.1.1 : ℝ) ≤
                (walkCount A 28 x₂.1 z : ℝ)} : ℝ) := by
  simp only [HighBadHalfCycleSide, Fintype.card_sigma, Nat.cast_sum]

lemma card_HighBadHalfCycleSide_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (b : Bool) (t s : ℝ)
    (ht : 0 < t) (hs : 0 ≤ s)
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y, side y = !b →
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s) :
    (Fintype.card (HighBadHalfCycleSide A R side b t) : ℝ) ≤
      28 * s * t⁻¹ * (closedWalkCount A 56 : ℝ) := by
  rw [card_HighBadHalfCycleSide_cast]
  calc
    (∑ z : W, ∑ x₂ : {x : W // side x = !b},
        ∑ q : FixedWalk A 28 x₂.1 z,
          ∑ x₁ : {x : ↑(walkConflictingNeighbors28 A R q) // side x.1 = b},
            (Fintype.card {p : FixedWalk A 27 z x₁.1.1 //
              t * (walkCount A 27 z x₁.1.1 : ℝ) ≤
                (walkCount A 28 x₂.1 z : ℝ)} : ℝ)) ≤
      ∑ z : W, ∑ x₂ : {x : W // side x = !b},
        ∑ _q : FixedWalk A 28 x₂.1 z,
          28 * s * (t⁻¹ * (walkCount A 28 x₂.1 z : ℝ)) := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro x₂ _
      apply Finset.sum_le_sum
      intro q _
      calc
        (∑ x₁ : {x : ↑(walkConflictingNeighbors28 A R q) // side x.1 = b},
            (Fintype.card {p : FixedWalk A 27 z x₁.1.1 //
              t * (walkCount A 27 z x₁.1.1 : ℝ) ≤
                (walkCount A 28 x₂.1 z : ℝ)} : ℝ)) ≤
            ∑ _x₁ : {x : ↑(walkConflictingNeighbors28 A R q) // side x.1 = b},
              t⁻¹ * (walkCount A 28 x₂.1 z : ℝ) := by
          apply Finset.sum_le_sum
          intro x₁ _
          exact card_highFixedWalks_le A R t ht z x₂.1 q x₁.1
        _ = (Fintype.card {x : ↑(walkConflictingNeighbors28 A R q) //
              side x.1 = b} : ℝ) *
              (t⁻¹ * (walkCount A 28 x₂.1 z : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Nat.cast_mul]
        _ ≤ ((walkConflictingNeighbors28 A R q).card : ℝ) *
              (t⁻¹ * (walkCount A 28 x₂.1 z : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (inv_nonneg.mpr ht.le) (by positivity))
          have hc := Fintype.card_subtype_le
            (fun x : ↑(walkConflictingNeighbors28 A R q) ↦ side x.1 = b)
          have hc' : Fintype.card {x : ↑(walkConflictingNeighbors28 A R q) //
                side x.1 = b} ≤ (walkConflictingNeighbors28 A R q).card := by
            simpa only [Fintype.card_coe] using hc
          exact_mod_cast hc'
        _ ≤ (28 * s) *
              (t⁻¹ * (walkCount A 28 x₂.1 z : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (inv_nonneg.mpr ht.le) (by positivity))
          exact card_walkConflictingNeighbors28_le_at A R s hsymm q
            (fun u ↦ hlocal u x₂.1 x₂.2)
        _ = 28 * s *
              (t⁻¹ * (walkCount A 28 x₂.1 z : ℝ)) := by ring
    _ = 28 * s * t⁻¹ * (∑ z : W,
        ∑ x₂ : {x : W // side x = !b},
          (walkCount A 28 x₂.1 z : ℝ) ^ 2) := by
      simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Finset.mul_sum, walkCount]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x₂ _
      ring
    _ ≤ 28 * s * t⁻¹ * (∑ z : W, ∑ x₂ : W,
        (walkCount A 28 x₂ z : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro z _
      rw [← Finset.sum_subtype (Finset.univ.filter fun x : W ↦ side x = !b)
        (by simp) (fun x ↦ (walkCount A 28 x z : ℝ) ^ 2)]
      apply Finset.sum_le_sum_of_subset_of_nonneg (by simp)
      intro x _ _
      positivity
    _ = 28 * s * t⁻¹ * (closedWalkCount A 56 : ℝ) := by
      rw [show 56 = 2 * 28 by norm_num,
        closedWalkCount_cast_eq_sum_walkCount_sq]
      congr 1
      exact Finset.sum_comm

abbrev HalfCycleSideSplit {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ) :=
  Σ b : Bool,
    LowHalfCycleSide A side b (t b) ⊕
      HighBadHalfCycleSide A R side b (t b)

noncomputable def encodeBadHalfCycleSideSplit {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x) :
    BadHalfCycle A R → HalfCycleSideSplit A R side t
  | ⟨⟨z, x₁, p, x₂, q⟩, hbad⟩ =>
      let b := side x₁
      if hlow : (walkCount A 28 x₂.1 z : ℝ) <
          t b * (walkCount A 27 z x₁ : ℝ) then
        ⟨b, Sum.inl ⟨z, ⟨x₁, rfl⟩, p, x₂, ⟨q, hlow⟩⟩⟩
      else
        ⟨b, Sum.inr ⟨z, ⟨x₂.1, hcross x₂.2⟩, q,
          ⟨⟨x₁, by
            rw [mem_walkConflictingNeighbors28]
            exact ⟨by simpa using x₂.2.symm, hbad⟩⟩, rfl⟩,
          ⟨p, le_of_not_gt hlow⟩⟩⟩

noncomputable def decodeHalfCycleSideSplit {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ) :
    HalfCycleSideSplit A R side t → RawHalfCycle A
  | ⟨_b, Sum.inl ⟨z, x₁, p, x₂, q⟩⟩ =>
      ⟨z, x₁.1, p, x₂, q.1⟩
  | ⟨_b, Sum.inr ⟨z, x₂, q, x₁, p⟩⟩ =>
      ⟨z, x₁.1.1, p.1,
        ⟨x₂.1, by
          have hx := x₁.1.2
          rw [mem_walkConflictingNeighbors28] at hx
          exact hx.1.symm⟩,
        q⟩

lemma decode_encodeBadHalfCycleSideSplit {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (b : BadHalfCycle A R) :
    decodeHalfCycleSideSplit A R side t
        (encodeBadHalfCycleSideSplit A R side t hcross b) =
      eraseBadHalfCycle A R b := by
  rcases b with ⟨⟨z, x₁, p, x₂, q⟩, hbad⟩
  simp only [encodeBadHalfCycleSideSplit]
  split <;> simp [decodeHalfCycleSideSplit, eraseBadHalfCycle]

lemma encodeBadHalfCycleSideSplit_injective {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x) :
    Function.Injective (encodeBadHalfCycleSideSplit A R side t hcross) := by
  intro b c h
  apply eraseBadHalfCycle_injective A R
  rw [← decode_encodeBadHalfCycleSideSplit A R side t hcross b,
    ← decode_encodeBadHalfCycleSideSplit A R side t hcross c, h]

lemma card_BadHalfCycle_side_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t D s : Bool → ℝ)
    (ht : ∀ b, 0 < t b) (hD : ∀ b, 0 ≤ D b) (hs : ∀ b, 0 ≤ s b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D (side x))
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y,
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s (side y)) :
    (Fintype.card (BadHalfCycle A R) : ℝ) ≤
      ∑ b : Bool, (D b * t b * (closedWalkCount A 54 : ℝ) +
        28 * s (!b) * (t b)⁻¹ * (closedWalkCount A 56 : ℝ)) := by
  have hcardNat := Fintype.card_le_of_injective
    (encodeBadHalfCycleSideSplit A R side t hcross)
    (encodeBadHalfCycleSideSplit_injective A R side t hcross)
  have hcard : (Fintype.card (BadHalfCycle A R) : ℝ) ≤
      Fintype.card (HalfCycleSideSplit A R side t) := by
    exact_mod_cast hcardNat
  rw [Fintype.card_sigma, Nat.cast_sum] at hcard
  refine hcard.trans ?_
  apply Finset.sum_le_sum
  intro b _
  rw [Fintype.card_sum, Nat.cast_add]
  apply add_le_add
  · exact card_LowHalfCycleSide_le A side b (t b) (D b)
      (ht b).le (hD b) (fun x hx ↦ by simpa [hx] using hdegree x)
  · exact card_HighBadHalfCycleSide_le A R side b (t b) (s (!b))
      (ht b) (hs (!b)) hsymm (fun u y hy ↦ by simpa [hy] using hlocal u y)

lemma card_BadClosedWalk56_side_cast_le {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t D s : Bool → ℝ)
    (ht : ∀ b, 0 < t b) (hD : ∀ b, 0 ≤ D b) (hs : ∀ b, 0 ≤ s b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D (side x))
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y,
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s (side y)) :
    (Fintype.card (Encode56.BadClosedWalk56 A R) : ℝ) ≤
      56 * ∑ b : Bool,
        (D b * t b * (closedWalkCount A 54 : ℝ) +
          28 * s (!b) * (t b)⁻¹ * (closedWalkCount A 56 : ℝ)) := by
  calc
    (Fintype.card (Encode56.BadClosedWalk56 A R) : ℝ) ≤
        56 * (Fintype.card (BadHalfCycle A R) : ℝ) := by
      exact_mod_cast Encode56.card_BadClosedWalk56_le A R hsymm
    _ ≤ 56 * ∑ b : Bool,
        (D b * t b * (closedWalkCount A 54 : ℝ) +
          28 * s (!b) * (t b)⁻¹ * (closedWalkCount A 56 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact card_BadHalfCycle_side_le A R side t D s ht hD hs hcross hdegree
        hsymm hlocal

end Erdos113Sides56

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/ConflictSidesConsecutive56.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Erdos113SidesConsecutive56

open Consecutive56

abbrev LowHalfCycleSide {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (b : Bool) (t : ℝ) :=
  Σ z : W, Σ x₁ : {x : W // side x = b},
    FixedWalk A 27 z x₁.1 ×
      Σ x₂ : A.neighborSet x₁.1,
        {q : FixedWalk A 28 x₂.1 z //
          (walkCount A 28 x₂.1 z : ℝ) <
            t * (walkCount A 27 z x₁.1 : ℝ)}

abbrev HighBadHalfCycleSide {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (b : Bool) (t : ℝ) :=
  Σ z : W, Σ x₂ : {x : W // side x = !b},
    Σ q : FixedWalk A 28 x₂.1 z,
      Σ x₁ : {x : ↑(walkConflictingNeighbors28 A R q) // side x.1 = b},
        {p : FixedWalk A 27 z x₁.1.1 //
          t * (walkCount A 27 z x₁.1.1 : ℝ) ≤
            (walkCount A 28 x₂.1 z : ℝ)}

lemma card_LowHalfCycleSide_cast {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (b : Bool) (t : ℝ) :
    (Fintype.card (LowHalfCycleSide A side b t) : ℝ) =
      ∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 27 z x₁.1 : ℝ) *
          ∑ x₂ : A.neighborSet x₁.1,
            (Fintype.card {q : FixedWalk A 28 x₂.1 z //
              (walkCount A 28 x₂.1 z : ℝ) <
                t * (walkCount A 27 z x₁.1 : ℝ)} : ℝ) := by
  simp only [LowHalfCycleSide, Fintype.card_sigma, Fintype.card_prod,
    Nat.cast_sum, Nat.cast_mul]
  rfl

lemma card_LowHalfCycleSide_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (b : Bool) (t D : ℝ) (ht : 0 ≤ t) (hD : 0 ≤ D)
    (hdegree : ∀ x, side x = b → (A.degree x : ℝ) ≤ D) :
    (Fintype.card (LowHalfCycleSide A side b t) : ℝ) ≤
      D * t * (closedWalkCount A 54 : ℝ) := by
  rw [card_LowHalfCycleSide_cast]
  calc
    (∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 27 z x₁.1 : ℝ) *
          ∑ x₂ : A.neighborSet x₁.1,
            (Fintype.card {q : FixedWalk A 28 x₂.1 z //
              (walkCount A 28 x₂.1 z : ℝ) <
                t * (walkCount A 27 z x₁.1 : ℝ)} : ℝ)) ≤
      ∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 27 z x₁.1 : ℝ) *
          (D * (t * (walkCount A 27 z x₁.1 : ℝ))) := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro x₁ _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        (∑ x₂ : A.neighborSet x₁.1,
            (Fintype.card {q : FixedWalk A 28 x₂.1 z //
              (walkCount A 28 x₂.1 z : ℝ) <
                t * (walkCount A 27 z x₁.1 : ℝ)} : ℝ)) ≤
            ∑ _x₂ : A.neighborSet x₁.1,
              t * (walkCount A 27 z x₁.1 : ℝ) := by
          apply Finset.sum_le_sum
          intro x₂ _
          exact card_lowFixedWalks_le A t ht z x₁.1 x₂
        _ = (A.degree x₁.1 : ℝ) *
              (t * (walkCount A 27 z x₁.1 : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            SimpleGraph.card_neighborSet_eq_degree, Nat.cast_mul]
        _ ≤ D * (t * (walkCount A 27 z x₁.1 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right (hdegree x₁.1 x₁.2)
            (mul_nonneg ht (by positivity))
    _ = D * t * (∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 27 z x₁.1 : ℝ) ^ 2) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x₁ _
      ring
    _ ≤ D * t * (∑ z : W, ∑ x₁ : W,
        (walkCount A 27 z x₁ : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD ht)
      apply Finset.sum_le_sum
      intro z _
      rw [← Finset.sum_subtype (Finset.univ.filter fun x : W ↦ side x = b)
        (by simp) (fun x ↦ (walkCount A 27 z x : ℝ) ^ 2)]
      apply Finset.sum_le_sum_of_subset_of_nonneg (by simp)
      intro x _ _
      positivity
    _ = D * t * (closedWalkCount A 54 : ℝ) := by
      rw [show 54 = 2 * 27 by norm_num,
        closedWalkCount_cast_eq_sum_walkCount_sq]

lemma card_walkConflictingNeighbors28_le_at {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (s : ℝ)
    (hsymm : ∀ x y, R x y → R y x)
    {z y : W} (q : FixedWalk A 28 y z)
    (hlocal : ∀ u, A.Adj y u →
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s) :
    ((walkConflictingNeighbors28 A R q).card : ℝ) ≤ s := by
  classical
  have hqadj : A.Adj y (q.1.getVert 1) := by
    have h := q.1.adj_getVert_succ (show 0 < q.1.length by simp [q.2])
    simpa using h
  have heq : walkConflictingNeighbors28 A R q =
      (A.neighborFinset y).filter (R (q.1.getVert 1)) := by
    ext x
    rw [walkConflictingNeighbors28, Finset.mem_filter, Finset.mem_filter]
    change (x ∈ A.neighborFinset y ∧ R x (q.1.getVert 1)) ↔
      (x ∈ A.neighborFinset y ∧ R (q.1.getVert 1) x)
    constructor
    · rintro ⟨hxy, hR⟩
      exact ⟨hxy, hsymm _ _ hR⟩
    · rintro ⟨hxy, hR⟩
      exact ⟨hxy, hsymm _ _ hR⟩
  rw [heq]
  exact hlocal _ hqadj

lemma card_HighBadHalfCycleSide_cast {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (b : Bool) (t : ℝ) :
    (Fintype.card (HighBadHalfCycleSide A R side b t) : ℝ) =
      ∑ z : W, ∑ x₂ : {x : W // side x = !b},
        ∑ q : FixedWalk A 28 x₂.1 z,
          ∑ x₁ : {x : ↑(walkConflictingNeighbors28 A R q) // side x.1 = b},
            (Fintype.card {p : FixedWalk A 27 z x₁.1.1 //
              t * (walkCount A 27 z x₁.1.1 : ℝ) ≤
                (walkCount A 28 x₂.1 z : ℝ)} : ℝ) := by
  simp only [HighBadHalfCycleSide, Fintype.card_sigma, Nat.cast_sum]

lemma card_HighBadHalfCycleSide_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (b : Bool) (t s : ℝ)
    (ht : 0 < t) (hs : 0 ≤ s)
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y, A.Adj y u → side y = !b →
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s) :
    (Fintype.card (HighBadHalfCycleSide A R side b t) : ℝ) ≤
      s * t⁻¹ * (closedWalkCount A 56 : ℝ) := by
  rw [card_HighBadHalfCycleSide_cast]
  calc
    (∑ z : W, ∑ x₂ : {x : W // side x = !b},
        ∑ q : FixedWalk A 28 x₂.1 z,
          ∑ x₁ : {x : ↑(walkConflictingNeighbors28 A R q) // side x.1 = b},
            (Fintype.card {p : FixedWalk A 27 z x₁.1.1 //
              t * (walkCount A 27 z x₁.1.1 : ℝ) ≤
                (walkCount A 28 x₂.1 z : ℝ)} : ℝ)) ≤
      ∑ z : W, ∑ x₂ : {x : W // side x = !b},
        ∑ _q : FixedWalk A 28 x₂.1 z,
          s * (t⁻¹ * (walkCount A 28 x₂.1 z : ℝ)) := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro x₂ _
      apply Finset.sum_le_sum
      intro q _
      calc
        (∑ x₁ : {x : ↑(walkConflictingNeighbors28 A R q) // side x.1 = b},
            (Fintype.card {p : FixedWalk A 27 z x₁.1.1 //
              t * (walkCount A 27 z x₁.1.1 : ℝ) ≤
                (walkCount A 28 x₂.1 z : ℝ)} : ℝ)) ≤
            ∑ _x₁ : {x : ↑(walkConflictingNeighbors28 A R q) // side x.1 = b},
              t⁻¹ * (walkCount A 28 x₂.1 z : ℝ) := by
          apply Finset.sum_le_sum
          intro x₁ _
          exact card_highFixedWalks_le A R t ht z x₂.1 q x₁.1
        _ = (Fintype.card {x : ↑(walkConflictingNeighbors28 A R q) //
              side x.1 = b} : ℝ) *
              (t⁻¹ * (walkCount A 28 x₂.1 z : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Nat.cast_mul]
        _ ≤ ((walkConflictingNeighbors28 A R q).card : ℝ) *
              (t⁻¹ * (walkCount A 28 x₂.1 z : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (inv_nonneg.mpr ht.le) (by positivity))
          have hc := Fintype.card_subtype_le
            (fun x : ↑(walkConflictingNeighbors28 A R q) ↦ side x.1 = b)
          have hc' : Fintype.card {x : ↑(walkConflictingNeighbors28 A R q) //
                side x.1 = b} ≤ (walkConflictingNeighbors28 A R q).card := by
            simpa only [Fintype.card_coe] using hc
          exact_mod_cast hc'
        _ ≤ s *
              (t⁻¹ * (walkCount A 28 x₂.1 z : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (inv_nonneg.mpr ht.le) (by positivity))
          exact card_walkConflictingNeighbors28_le_at A R s hsymm q
            (fun u huy ↦ hlocal u x₂.1 huy x₂.2)
        _ = s *
              (t⁻¹ * (walkCount A 28 x₂.1 z : ℝ)) := by ring
    _ = s * t⁻¹ * (∑ z : W,
        ∑ x₂ : {x : W // side x = !b},
          (walkCount A 28 x₂.1 z : ℝ) ^ 2) := by
      simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Finset.mul_sum, walkCount]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x₂ _
      ring
    _ ≤ s * t⁻¹ * (∑ z : W, ∑ x₂ : W,
        (walkCount A 28 x₂ z : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro z _
      rw [← Finset.sum_subtype (Finset.univ.filter fun x : W ↦ side x = !b)
        (by simp) (fun x ↦ (walkCount A 28 x z : ℝ) ^ 2)]
      apply Finset.sum_le_sum_of_subset_of_nonneg (by simp)
      intro x _ _
      positivity
    _ = s * t⁻¹ * (closedWalkCount A 56 : ℝ) := by
      rw [show 56 = 2 * 28 by norm_num,
        closedWalkCount_cast_eq_sum_walkCount_sq]
      congr 1
      exact Finset.sum_comm

abbrev HalfCycleSideSplit {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ) :=
  Σ b : Bool,
    LowHalfCycleSide A side b (t b) ⊕
      HighBadHalfCycleSide A R side b (t b)

noncomputable def encodeBadHalfCycleSideSplit {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x) :
    BadHalfCycle A R → HalfCycleSideSplit A R side t
  | ⟨⟨z, x₁, p, x₂, q⟩, hbad⟩ =>
      let b := side x₁
      if hlow : (walkCount A 28 x₂.1 z : ℝ) <
          t b * (walkCount A 27 z x₁ : ℝ) then
        ⟨b, Sum.inl ⟨z, ⟨x₁, rfl⟩, p, x₂, ⟨q, hlow⟩⟩⟩
      else
        ⟨b, Sum.inr ⟨z, ⟨x₂.1, hcross x₂.2⟩, q,
          ⟨⟨x₁, by
            rw [mem_walkConflictingNeighbors28]
            exact ⟨by simpa using x₂.2.symm, hbad⟩⟩, rfl⟩,
          ⟨p, le_of_not_gt hlow⟩⟩⟩

noncomputable def decodeHalfCycleSideSplit {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ) :
    HalfCycleSideSplit A R side t → RawHalfCycle A
  | ⟨_b, Sum.inl ⟨z, x₁, p, x₂, q⟩⟩ =>
      ⟨z, x₁.1, p, x₂, q.1⟩
  | ⟨_b, Sum.inr ⟨z, x₂, q, x₁, p⟩⟩ =>
      ⟨z, x₁.1.1, p.1,
        ⟨x₂.1, by
          have hx := x₁.1.2
          rw [mem_walkConflictingNeighbors28] at hx
          exact hx.1.symm⟩,
        q⟩

lemma decode_encodeBadHalfCycleSideSplit {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (b : BadHalfCycle A R) :
    decodeHalfCycleSideSplit A R side t
        (encodeBadHalfCycleSideSplit A R side t hcross b) =
      eraseBadHalfCycle A R b := by
  rcases b with ⟨⟨z, x₁, p, x₂, q⟩, hbad⟩
  simp only [encodeBadHalfCycleSideSplit]
  split <;> simp [decodeHalfCycleSideSplit, eraseBadHalfCycle]

lemma encodeBadHalfCycleSideSplit_injective {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x) :
    Function.Injective (encodeBadHalfCycleSideSplit A R side t hcross) := by
  intro b c h
  apply eraseBadHalfCycle_injective A R
  rw [← decode_encodeBadHalfCycleSideSplit A R side t hcross b,
    ← decode_encodeBadHalfCycleSideSplit A R side t hcross c, h]

lemma card_BadHalfCycle_side_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t D s : Bool → ℝ)
    (ht : ∀ b, 0 < t b) (hD : ∀ b, 0 ≤ D b) (hs : ∀ b, 0 ≤ s b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D (side x))
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y, A.Adj y u →
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s (side y)) :
    (Fintype.card (BadHalfCycle A R) : ℝ) ≤
      ∑ b : Bool, (D b * t b * (closedWalkCount A 54 : ℝ) +
        s (!b) * (t b)⁻¹ * (closedWalkCount A 56 : ℝ)) := by
  have hcardNat := Fintype.card_le_of_injective
    (encodeBadHalfCycleSideSplit A R side t hcross)
    (encodeBadHalfCycleSideSplit_injective A R side t hcross)
  have hcard : (Fintype.card (BadHalfCycle A R) : ℝ) ≤
      Fintype.card (HalfCycleSideSplit A R side t) := by
    exact_mod_cast hcardNat
  rw [Fintype.card_sigma, Nat.cast_sum] at hcard
  refine hcard.trans ?_
  apply Finset.sum_le_sum
  intro b _
  rw [Fintype.card_sum, Nat.cast_add]
  apply add_le_add
  · exact card_LowHalfCycleSide_le A side b (t b) (D b)
      (ht b).le (hD b) (fun x hx ↦ by simpa [hx] using hdegree x)
  · exact card_HighBadHalfCycleSide_le A R side b (t b) (s (!b))
      (ht b) (hs (!b)) hsymm
      (fun u y huy hy ↦ by simpa [hy] using hlocal u y huy)

lemma card_BadClosedWalk56_side_cast_le {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t D s : Bool → ℝ)
    (ht : ∀ b, 0 < t b) (hD : ∀ b, 0 ≤ D b) (hs : ∀ b, 0 ≤ s b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D (side x))
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y, A.Adj y u →
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s (side y)) :
    (Fintype.card (EncodeConsecutive56.BadClosedWalk56 A R) : ℝ) ≤
      56 * ∑ b : Bool,
        (D b * t b * (closedWalkCount A 54 : ℝ) +
          s (!b) * (t b)⁻¹ * (closedWalkCount A 56 : ℝ)) := by
  calc
    (Fintype.card (EncodeConsecutive56.BadClosedWalk56 A R) : ℝ) ≤
        56 * (Fintype.card (BadHalfCycle A R) : ℝ) := by
      exact_mod_cast EncodeConsecutive56.card_BadClosedWalk56_le A R hsymm
    _ ≤ 56 * ∑ b : Bool,
        (D b * t b * (closedWalkCount A 54 : ℝ) +
          s (!b) * (t b)⁻¹ * (closedWalkCount A 56 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact card_BadHalfCycle_side_le A R side t D s ht hD hs hcross hdegree
        hsymm hlocal

end Erdos113SidesConsecutive56

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Cycle28.lean` -/

section
/-!
# Ordered homomorphic 28-cycles and closed walks
-/

open scoped SimpleGraph

namespace Erdos113Cycle28

open Erdos113Cycles

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Tuple28 (V : Type*) := Fin 28 → V

abbrev ClosedWalk28 (G : SimpleGraph V) :=
  Σ v : V, Conflict.FixedWalk G 28 v v

/-- Read the first 28 vertices of a length-28 closed walk. -/
def closedWalkTuple (G : SimpleGraph V) (P : ClosedWalk28 G) : Tuple28 V :=
  fun i ↦ P.2.1.getVert i.val

lemma closedWalkTuple_isHomCycle (G : SimpleGraph V) (P : ClosedWalk28 G) :
    IsHomCycle G (closedWalkTuple G P) := by
  intro i
  have hi : i.val < P.2.1.length := by simpa [P.2.2] using i.isLt
  have h := P.2.1.adj_getVert_succ hi
  by_cases hlast : i.val + 1 < 28
  · have hadd : (i + 1 : Fin 28).val = i.val + 1 :=
      Fin.val_add_eq_of_add_lt (by simpa using hlast)
    simpa [closedWalkTuple, hadd] using h
  · have hi55 : i.val = 27 := by omega
    have hend : P.2.1.getVert 28 = P.1 := by
      simpa [P.2.2] using P.2.1.getVert_length
    have hstart : P.2.1.getVert 0 = P.1 := P.2.1.getVert_zero
    have hi' : i = (27 : Fin 28) := Fin.ext hi55
    subst i
    simpa [closedWalkTuple, hend, hstart] using h

/-- Append the initial vertex to a cyclic 28-tuple. -/
def closeSeq (x : Tuple28 V) (j : Fin 29) : V :=
  if h : j.val < 28 then x ⟨j.val, h⟩ else x 0

@[simp] lemma closeSeq_castSucc (x : Tuple28 V) (i : Fin 28) :
    closeSeq x i.castSucc = x i := by
  simp [closeSeq]

@[simp] lemma closeSeq_last (x : Tuple28 V) : closeSeq x (Fin.last 28) = x 0 := by
  simp [closeSeq]

lemma closeSeq_succ (x : Tuple28 V) (i : Fin 28) :
    closeSeq x i.succ = x (i + 1) := by
  by_cases h : i.val + 1 < 28
  · simp only [closeSeq, Fin.val_succ, h, ↓reduceDIte]
    congr 1
    apply Fin.ext
    symm
    exact Fin.val_add_eq_of_add_lt (by simpa using h)
  · have hi : i.val = 27 := by omega
    have hi' : i = (27 : Fin 28) := Fin.ext hi
    subst i
    simp [closeSeq]

lemma closeSeq_adj {G : SimpleGraph V} {x : Tuple28 V}
    (hx : IsHomCycle G x) (i : Fin 28) :
    G.Adj (closeSeq x i.castSucc) (closeSeq x i.succ) := by
  rw [closeSeq_castSucc, closeSeq_succ]
  exact hx i

/-- Turn a cyclic tuple into the corresponding closed walk. -/
def tupleClosedWalk {G : SimpleGraph V} (x : Tuple28 V) (hx : IsHomCycle G x) :
    ClosedWalk28 G := by
  let p := WF.walkOfFin 28 (closeSeq x) (closeSeq_adj hx)
  refine ⟨x 0, ⟨p.copy ?_ ?_, ?_⟩⟩
  · simp [p, closeSeq]
  · simp [p, closeSeq]
  · simp [p]

@[simp] lemma closedWalkTuple_tupleClosedWalk {G : SimpleGraph V}
    (x : Tuple28 V) (hx : IsHomCycle G x) :
    closedWalkTuple G (tupleClosedWalk x hx) = x := by
  funext i
  simp only [closedWalkTuple, tupleClosedWalk]
  rw [SimpleGraph.Walk.getVert_copy]
  simpa [closeSeq] using
    (WF.walkOfFin_getVert 28 (closeSeq x) (closeSeq_adj hx) i.val
      (Nat.le_of_lt i.isLt))

lemma closedWalkTuple_injective (G : SimpleGraph V) :
    Function.Injective (closedWalkTuple G) := by
  rintro ⟨p, P⟩ ⟨q, Q⟩ hPQ
  have hstart : p = q := by
    have h0 := congrFun hPQ 0
    simpa [closedWalkTuple] using h0
  subst q
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Subtype.ext
  apply SimpleGraph.Walk.ext_getVert_le_length
  · rw [P.2, Q.2]
  · intro i hiP
    by_cases hi : i < 28
    · have h := congrFun hPQ ⟨i, hi⟩
      simpa [closedWalkTuple] using h
    · have hiP' : i ≤ 28 := by simpa [P.2] using hiP
      have hi28 : i = 28 := by omega
      subst i
      have hp : P.1.getVert 28 = p := by
        simpa [P.2] using P.1.getVert_length
      have hq : Q.1.getVert 28 = p := by
        simpa [Q.2] using Q.1.getVert_length
      exact hp.trans hq.symm

noncomputable def closedWalkHomEquiv (G : SimpleGraph V) :
    ClosedWalk28 G ≃ {x : Tuple28 V // IsHomCycle G x} :=
  Equiv.ofBijective
    (fun P ↦ ⟨closedWalkTuple G P, closedWalkTuple_isHomCycle G P⟩)
    ⟨fun _ _ h ↦ closedWalkTuple_injective G (congrArg Subtype.val h), by
      intro x
      refine ⟨tupleClosedWalk x.1 x.2, ?_⟩
      apply Subtype.ext
      exact closedWalkTuple_tupleClosedWalk x.1 x.2⟩

lemma card_homCycle28_eq_closedWalkCount (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card {x : Tuple28 V // IsHomCycle G x} =
      Conflict.closedWalkCount G 28 := by
  rw [← Fintype.card_congr (closedWalkHomEquiv G)]
  simp only [Fintype.card_sigma, Conflict.closedWalkCount]
  rfl

end Erdos113Cycle28

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Conflict28.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Conflict28

noncomputable def walkCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) (u v : W) : ℕ :=
  Fintype.card {p : A.Walk u v // p.length = m}

noncomputable def closedWalkCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) : ℕ :=
  ∑ x : W, walkCount A m x x

lemma closedWalkCount_cast_eq_trace {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) :
    (closedWalkCount A m : ℝ) = Matrix.trace (A.adjMatrix ℝ ^ m) := by
  rw [closedWalkCount, Nat.cast_sum, Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.diag_apply, A.adjMatrix_pow_apply_eq_card_walk]
  rfl

lemma closedWalkCount_cast_eq_sum_walkCount_sq {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) :
    (closedWalkCount A (2 * m) : ℝ) =
      ∑ u : W, ∑ v : W, (walkCount A m u v : ℝ) ^ 2 := by
  rw [closedWalkCount_cast_eq_trace]
  have hpow : A.adjMatrix ℝ ^ (2 * m) =
      A.adjMatrix ℝ ^ m * A.adjMatrix ℝ ^ m := by
    rw [show 2 * m = m + m by omega, pow_add]
  rw [hpow, Matrix.trace]
  apply Finset.sum_congr rfl
  intro u _
  rw [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro v _
  rw [A.adjMatrix_pow_apply_eq_card_walk,
    A.adjMatrix_pow_apply_eq_card_walk]
  have hrev : walkCount A m v u = walkCount A m u v := by
    unfold walkCount
    apply Fintype.card_congr
    exact
      { toFun := fun p ↦ ⟨p.1.reverse, by simpa using p.2⟩
        invFun := fun p ↦ ⟨p.1.reverse, by simpa using p.2⟩
        left_inv := by intro p; apply Subtype.ext; simp
        right_inv := by intro p; apply Subtype.ext; simp }
  change (walkCount A m u v : ℝ) * (walkCount A m v u : ℝ) = _
  rw [hrev]
  ring

abbrev FixedWalk {W : Type*} (A : SimpleGraph W) (m : ℕ) (u v : W) :=
  {p : A.Walk u v // p.length = m}

def WalkConflict14 {W : Type*} {A : SimpleGraph W}
    (R : W → W → Prop) (x : W) {z y : W} (q : FixedWalk A 14 y z) : Prop :=
  ∃ i : Fin 7, ∃ j : Fin 2,
    R x (q.1.getVert (2 * i.val + j.val))

noncomputable instance instDecidableWalkConflict14 {W : Type*} {A : SimpleGraph W}
    (R : W → W → Prop) [DecidableRel R] (x : W) {z y : W}
    (q : FixedWalk A 14 y z) : Decidable (WalkConflict14 R x q) :=
  Classical.propDecidable _

noncomputable def walkConflictingNeighbors14 {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    {z y : W} (q : FixedWalk A 14 y z) : Finset W := by
  classical
  exact (A.neighborFinset y).filter fun x ↦ WalkConflict14 R x q

@[simp] lemma mem_walkConflictingNeighbors14 {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    {z y : W} (q : FixedWalk A 14 y z) (x : W) :
    x ∈ walkConflictingNeighbors14 A R q ↔
      A.Adj y x ∧ WalkConflict14 R x q := by
  classical
  simp [walkConflictingNeighbors14]

lemma card_lowFixedWalks_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (t : ℝ) (ht : 0 ≤ t)
    (z x₁ : W) (x₂ : A.neighborSet x₁) :
    (Fintype.card {q : FixedWalk A 14 x₂.1 z //
      (walkCount A 14 x₂.1 z : ℝ) <
        t * (walkCount A 13 z x₁ : ℝ)} : ℝ) ≤
      t * (walkCount A 13 z x₁ : ℝ) := by
  let T := {q : FixedWalk A 14 x₂.1 z //
    (walkCount A 14 x₂.1 z : ℝ) <
      t * (walkCount A 13 z x₁ : ℝ)}
  have hnonneg : 0 ≤ t * (walkCount A 13 z x₁ : ℝ) :=
    mul_nonneg ht (by positivity)
  cases isEmpty_or_nonempty T with
  | inl hempty =>
      have hcard : Fintype.card T = 0 := Fintype.card_eq_zero
      rw [hcard, Nat.cast_zero]
      exact hnonneg
  | inr hnonempty =>
      let q : T := Classical.choice hnonempty
      calc
        (Fintype.card T : ℝ) ≤
            (Fintype.card (FixedWalk A 14 x₂.1 z) : ℝ) := by
          exact_mod_cast Fintype.card_subtype_le (fun _q : FixedWalk A 14 x₂.1 z ↦
            (walkCount A 14 x₂.1 z : ℝ) <
              t * (walkCount A 13 z x₁ : ℝ))
        _ = (walkCount A 14 x₂.1 z : ℝ) := rfl
        _ ≤ t * (walkCount A 13 z x₁ : ℝ) := q.2.le

lemma card_highFixedWalks_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (t : ℝ) (ht : 0 < t)
    (z x₂ : W) (q : FixedWalk A 14 x₂ z)
    (x₁ : ↑(walkConflictingNeighbors14 A R q)) :
    (Fintype.card {p : FixedWalk A 13 z x₁.1 //
      t * (walkCount A 13 z x₁.1 : ℝ) ≤
        (walkCount A 14 x₂ z : ℝ)} : ℝ) ≤
      t⁻¹ * (walkCount A 14 x₂ z : ℝ) := by
  let T := {p : FixedWalk A 13 z x₁.1 //
    t * (walkCount A 13 z x₁.1 : ℝ) ≤
      (walkCount A 14 x₂ z : ℝ)}
  have hnonneg : 0 ≤ t⁻¹ * (walkCount A 14 x₂ z : ℝ) :=
    mul_nonneg (inv_nonneg.mpr ht.le) (by positivity)
  cases isEmpty_or_nonempty T with
  | inl hempty =>
      have hcard : Fintype.card T = 0 := Fintype.card_eq_zero
      rw [hcard, Nat.cast_zero]
      exact hnonneg
  | inr hnonempty =>
      let p : T := Classical.choice hnonempty
      calc
        (Fintype.card T : ℝ) ≤
            (Fintype.card (FixedWalk A 13 z x₁.1) : ℝ) := by
          exact_mod_cast Fintype.card_subtype_le (fun _p : FixedWalk A 13 z x₁.1 ↦
            t * (walkCount A 13 z x₁.1 : ℝ) ≤
              (walkCount A 14 x₂ z : ℝ))
        _ = (walkCount A 13 z x₁.1 : ℝ) := rfl
        _ ≤ t⁻¹ * (walkCount A 14 x₂ z : ℝ) := by
          rw [inv_mul_eq_div]
          exact (le_div_iff₀' ht).2 p.2

abbrev RawHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] :=
  Σ z : W, Σ x₁ : W,
    FixedWalk A 13 z x₁ ×
      Σ x₂ : A.neighborSet x₁, FixedWalk A 14 x₂.1 z

abbrev BadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :=
  {b : RawHalfCycle A // WalkConflict14 R b.2.1 b.2.2.2.2}

def eraseBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :
    BadHalfCycle A R → RawHalfCycle A
  | b => b.1

lemma eraseBadHalfCycle_injective {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :
    Function.Injective (eraseBadHalfCycle A R) := by
  exact Subtype.val_injective

end Conflict28

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Encode28.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Encode28

open Conflict28 WF

def cyclicAdd28 (i : Fin 28) (d : Nat) : Fin 28 :=
  ⟨(i.val + d) % 28, Nat.mod_lt _ (by omega)⟩

lemma cyclicAdd28_zero (i : Fin 28) : cyclicAdd28 i 0 = i := by
  apply Fin.ext
  simp [cyclicAdd28, Nat.mod_eq_of_lt i.isLt]

lemma cyclicAdd28_add (i : Fin 28) (a b : Nat) :
    cyclicAdd28 (cyclicAdd28 i a) b = cyclicAdd28 i (a + b) := by
  apply Fin.ext
  simp only [cyclicAdd28]
  omega

lemma cyclicAdd28_full (i : Fin 28) : cyclicAdd28 i 28 = i := by
  apply Fin.ext
  change (i.val + 28) % 28 = i.val
  omega

lemma exists_short_oriented_pair (i j : Fin 28) (hij : i ≠ j) :
    ∃ c : Fin 28, ∃ d : Fin 14,
      cyclicAdd28 c (d.val + 1) = j ∧ c = i ∨
      cyclicAdd28 c (d.val + 1) = i ∧ c = j := by
  by_cases hijv : i.val < j.val
  · let e := j.val - i.val
    by_cases he : e ≤ 14
    · refine ⟨i, ⟨e - 1, by dsimp [e]; omega⟩, Or.inl ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd28, e]
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    · let e' := 28 - e
      refine ⟨j, ⟨e' - 1, by dsimp [e', e]; omega⟩, Or.inr ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd28, e', e]
      omega
  · have hjiv : j.val < i.val := by
      have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
      omega
    let e := i.val - j.val
    by_cases he : e ≤ 14
    · refine ⟨j, ⟨e - 1, by dsimp [e]; omega⟩, Or.inr ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd28, e]
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    · let e' := 28 - e
      refine ⟨i, ⟨e' - 1, by dsimp [e', e]; omega⟩, Or.inl ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd28, e', e]
      omega

abbrev ClosedWalk28 {W : Type*} (A : SimpleGraph W) :=
  Σ x : W, {p : A.Walk x x // p.length = 28}

def cv {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (i : Fin 28) : W :=
  P.2.1.getVert i.val

lemma cv_adj_add_one {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (i : Fin 28) :
    A.Adj (cv P i) (cv P (cyclicAdd28 i 1)) := by
  have hi : i.val < P.2.1.length := by rw [P.2.2]; exact i.isLt
  have hadj := P.2.1.adj_getVert_succ hi
  by_cases hwrap : i.val + 1 < 28
  · simpa [cv, cyclicAdd28, Nat.mod_eq_of_lt hwrap] using hadj
  · have hilast : i.val = 27 := by omega
    have hend : P.2.1.getVert 28 = P.1 := by
      simpa only [P.2.2] using P.2.1.getVert_length
    have hstart : P.2.1.getVert 0 = P.1 := P.2.1.getVert_zero
    simpa [cv, cyclicAdd28, hilast, hend, hstart] using hadj

def qSeq {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) (r : Fin 15) : W :=
  cv P (cyclicAdd28 c (r.val + 1))

lemma qSeq_adj {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) (r : Fin 14) :
    A.Adj (qSeq P c r.castSucc) (qSeq P c r.succ) := by
  have h := cv_adj_add_one P (cyclicAdd28 c (r.val + 1))
  simpa only [qSeq, Fin.val_castSucc, Fin.val_succ, cyclicAdd28_add,
    show r.val + 1 + 1 = r.val + 2 by omega] using h

def qWalk {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) :
    A.Walk (qSeq P c ⟨0, by omega⟩) (qSeq P c ⟨14, by omega⟩) :=
  walkOfFin 14 (qSeq P c) (qSeq_adj P c)

@[simp] lemma qWalk_length {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) : (qWalk P c).length = 14 := by
  exact walkOfFin_length 14 (qSeq P c) (qSeq_adj P c)

lemma qWalk_getVert {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) (i : Nat) (hi : i ≤ 14) :
    (qWalk P c).getVert i = cv P (cyclicAdd28 c (i + 1)) := by
  simp only [qWalk]
  exact walkOfFin_getVert 14 (qSeq P c) (qSeq_adj P c) i hi

def pSeq {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) (r : Fin 14) : W :=
  cv P (cyclicAdd28 c (15 + r.val))

lemma pSeq_adj {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) (r : Fin 13) :
    A.Adj (pSeq P c r.castSucc) (pSeq P c r.succ) := by
  have h := cv_adj_add_one P (cyclicAdd28 c (15 + r.val))
  simpa only [pSeq, Fin.val_castSucc, Fin.val_succ, cyclicAdd28_add,
    show 15 + r.val + 1 = 15 + (r.val + 1) by omega] using h

def pWalk {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) :
    A.Walk (pSeq P c ⟨0, by omega⟩) (pSeq P c ⟨13, by omega⟩) :=
  walkOfFin 13 (pSeq P c) (pSeq_adj P c)

@[simp] lemma pWalk_length {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) : (pWalk P c).length = 13 := by
  exact walkOfFin_length 13 (pSeq P c) (pSeq_adj P c)

lemma pWalk_getVert {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) (i : Nat) (hi : i ≤ 13) :
    (pWalk P c).getVert i = cv P (cyclicAdd28 c (15 + i)) := by
  simp only [pWalk]
  exact walkOfFin_getVert 13 (pSeq P c) (pSeq_adj P c) i hi

noncomputable def makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk28 A) (c : Fin 28) (d : Fin 14)
    (hR : R (cv P c) (cv P (cyclicAdd28 c (d.val + 1)))) :
    BadHalfCycle A R := by
  let z := qSeq P c ⟨14, by omega⟩
  let x₁ := pSeq P c ⟨13, by omega⟩
  let p : FixedWalk A 13 z x₁ :=
    ⟨(pWalk P c).copy (by simp [z, qSeq, pSeq]) rfl, by
      rw [SimpleGraph.Walk.length_copy, pWalk_length]⟩
  let x₂ : A.neighborSet x₁ := ⟨qSeq P c ⟨0, by omega⟩, by
    have h := cv_adj_add_one P c
    simpa [x₁, qSeq, pSeq, cyclicAdd28_full] using h⟩
  let q : FixedWalk A 14 x₂.1 z := ⟨qWalk P c, qWalk_length P c⟩
  refine ⟨⟨z, x₁, p, x₂, q⟩, ?_⟩
  let i : Fin 7 := ⟨d.val / 2, by omega⟩
  let j : Fin 2 := ⟨d.val % 2, Nat.mod_lt _ (by omega)⟩
  refine ⟨i, j, ?_⟩
  have hd : 2 * i.val + j.val = d.val := by
    dsimp [i, j]
    omega
  have hq := qWalk_getVert P c d.val (Nat.le_of_lt d.isLt)
  dsimp [x₁, q]
  rw [hd, hq]
  simpa [pSeq, cyclicAdd28_full] using hR

def cyclicOffset28 (c i : Fin 28) : Nat :=
  (i.val + 28 - c.val) % 28

lemma cyclicAdd_offset (c i : Fin 28) :
    cyclicAdd28 c (cyclicOffset28 c i) = i := by
  apply Fin.ext
  simp only [cyclicAdd28, cyclicOffset28]
  omega

abbrev PackedWalk {W : Type*} (A : SimpleGraph W) :=
  Σ u : W, Σ v : W, A.Walk u v

def packedWalkVertex {W : Type*} {A : SimpleGraph W}
    (p : PackedWalk A) (i : Nat) : W := p.2.2.getVert i

def packedQ {W : Type*} [Fintype W] [DecidableEq W]
    {A : SimpleGraph W} [DecidableRel A.Adj]
    {R : W → W → Prop} [DecidableRel R]
    (b : BadHalfCycle A R) : PackedWalk A :=
  ⟨b.1.2.2.2.1.1, b.1.1, b.1.2.2.2.2.1⟩

def packedP {W : Type*} [Fintype W] [DecidableEq W]
    {A : SimpleGraph W} [DecidableRel A.Adj]
    {R : W → W → Prop} [DecidableRel R]
    (b : BadHalfCycle A R) : PackedWalk A :=
  ⟨b.1.1, b.1.2.1, b.1.2.2.1.1⟩

def decodeHalfVertex {W : Type*} [Fintype W] [DecidableEq W]
    {A : SimpleGraph W} [DecidableRel A.Adj]
    {R : W → W → Prop} [DecidableRel R]
    (c : Fin 28) (b : BadHalfCycle A R)
    (i : Fin 28) : W :=
  let d := cyclicOffset28 c i
  if d = 0 then b.1.2.1
  else if d ≤ 15 then packedWalkVertex (packedQ b) (d - 1)
  else packedWalkVertex (packedP b) (d - 15)

@[simp] lemma makeBadHalfCycle_x1 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk28 A) (c : Fin 28) (d : Fin 14)
    (hR : R (cv P c) (cv P (cyclicAdd28 c (d.val + 1)))) :
    (makeBadHalfCycle A R P c d hR).1.2.1 = pSeq P c ⟨13, by omega⟩ := by
  rfl

@[simp] lemma packedQ_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk28 A) (c : Fin 28) (d : Fin 14)
    (hR : R (cv P c) (cv P (cyclicAdd28 c (d.val + 1)))) :
    packedQ (makeBadHalfCycle A R P c d hR) =
      ⟨qSeq P c ⟨0, by omega⟩, qSeq P c ⟨14, by omega⟩, qWalk P c⟩ := by
  rfl

@[simp] lemma packedP_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk28 A) (c : Fin 28) (d : Fin 14)
    (hR : R (cv P c) (cv P (cyclicAdd28 c (d.val + 1)))) :
    packedP (makeBadHalfCycle A R P c d hR) =
      ⟨qSeq P c ⟨14, by omega⟩, pSeq P c ⟨13, by omega⟩,
        (pWalk P c).copy (by simp [qSeq, pSeq]) rfl⟩ := by
  rfl

lemma packedP_makeBadHalfCycle_getVert {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk28 A) (c : Fin 28) (d : Fin 14)
    (hR : R (cv P c) (cv P (cyclicAdd28 c (d.val + 1)))) (i : Nat) :
    packedWalkVertex (packedP (makeBadHalfCycle A R P c d hR)) i =
      (pWalk P c).getVert i := by
  unfold packedWalkVertex packedP
  dsimp [makeBadHalfCycle]
  simp only [SimpleGraph.Walk.getVert_copy]

lemma decode_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk28 A) (c : Fin 28) (d : Fin 14)
    (hR : R (cv P c) (cv P (cyclicAdd28 c (d.val + 1))))
    (i : Fin 28) :
    decodeHalfVertex c (makeBadHalfCycle A R P c d hR) i = cv P i := by
  let e := cyclicOffset28 c i
  have he_lt : e < 28 := Nat.mod_lt _ (by omega)
  by_cases he0 : e = 0
  · have hi : i = c := by
      have := cyclicAdd_offset c i
      symm
      simpa [e, he0, cyclicAdd28_zero] using this
    subst i
    simp [decodeHalfVertex, e, he0, pSeq,
      cyclicAdd28_full]
  · by_cases he29 : e ≤ 15
    · have hq := qWalk_getVert P c (e - 1) (by omega)
      have hadd : cyclicAdd28 c ((e - 1) + 1) = i := by
        rw [show e - 1 + 1 = e by omega]
        exact cyclicAdd_offset c i
      dsimp [e] at he0 he29 hq hadd ⊢
      simp only [decodeHalfVertex, he0, ↓reduceIte, he29]
      rw [packedQ_makeBadHalfCycle A R P c d hR]
      simp only [packedWalkVertex]
      rw [hq, hadd]
    · have hp := pWalk_getVert P c (e - 15) (by omega)
      have hadd : cyclicAdd28 c (15 + (e - 15)) = i := by
        rw [show 15 + (e - 15) = e by omega]
        exact cyclicAdd_offset c i
      dsimp [e] at he0 he29 hp hadd ⊢
      simp only [decodeHalfVertex, he0, ↓reduceIte, he29]
      rw [packedP_makeBadHalfCycle_getVert A R P c d hR, hp, hadd]

lemma closedWalk28_ext {W : Type*} {A : SimpleGraph W}
    (P Q : ClosedWalk28 A) (h : ∀ i, cv P i = cv Q i) : P = Q := by
  rcases P with ⟨x, p, hp⟩
  rcases Q with ⟨y, q, hq⟩
  have hxy : x = y := by
    have h0 := h ⟨0, by omega⟩
    simpa [cv] using h0
  subst y
  have hpq : p = q := by
    apply SimpleGraph.Walk.ext_getVert
    intro k
    by_cases hk : k < 28
    · simpa [cv] using h ⟨k, hk⟩
    · rw [p.getVert_of_length_le (by omega), q.getVert_of_length_le (by omega)]
  subst q
  rfl

abbrev BadClosedWalk28 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :=
  {P : ClosedWalk28 A // ∃ i j, i ≠ j ∧ R (cv P i) (cv P j)}

lemma exists_orientedConflict28 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) (b : BadClosedWalk28 A R) :
    ∃ c : Fin 28, ∃ d : Fin 14,
      R (cv b.1 c) (cv b.1 (cyclicAdd28 c (d.val + 1))) := by
  rcases b.2 with ⟨i, j, hij, hR⟩
  rcases exists_short_oriented_pair i j hij with ⟨c, d, h | h⟩
  · refine ⟨c, d, ?_⟩
    rw [h.1, h.2]
    exact hR
  · refine ⟨c, d, ?_⟩
    rw [h.1, h.2]
    exact hsymm _ _ hR

noncomputable def orientedConflict28 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) (b : BadClosedWalk28 A R) :
    Σ c : Fin 28, {d : Fin 14 //
      R (cv b.1 c) (cv b.1 (cyclicAdd28 c (d.val + 1)))} := by
  let c := Classical.choose (exists_orientedConflict28 A R hsymm b)
  let d := Classical.choose (Classical.choose_spec
    (exists_orientedConflict28 A R hsymm b))
  exact ⟨c, d, Classical.choose_spec (Classical.choose_spec
    (exists_orientedConflict28 A R hsymm b))⟩

noncomputable def encodeBadClosedWalk28 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    BadClosedWalk28 A R → Fin 28 × BadHalfCycle A R := fun b ↦
  let w := orientedConflict28 A R hsymm b
  ⟨w.1, makeBadHalfCycle A R b.1 w.1 w.2.1 w.2.2⟩

lemma encodeBadClosedWalk28_injective {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    Function.Injective (encodeBadClosedWalk28 A R hsymm) := by
  intro b b' hbb'
  apply Subtype.ext
  apply closedWalk28_ext
  intro i
  have hdecode := congrArg (fun z : Fin 28 × BadHalfCycle A R ↦
    decodeHalfVertex z.1 z.2 i) hbb'
  simpa only [encodeBadClosedWalk28, decode_makeBadHalfCycle] using hdecode

lemma card_BadClosedWalk28_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    Fintype.card (BadClosedWalk28 A R) ≤
      28 * Fintype.card (BadHalfCycle A R) := by
  calc
    Fintype.card (BadClosedWalk28 A R) ≤
        Fintype.card (Fin 28 × BadHalfCycle A R) :=
      Fintype.card_le_of_injective _ (encodeBadClosedWalk28_injective A R hsymm)
    _ = 28 * Fintype.card (BadHalfCycle A R) := by simp

end Encode28

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Moments28.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Erdos113Moments28

lemma trace_pow_eq_sum_eigenvalues_pow {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (j : ℕ) :
    Matrix.trace (A ^ j) = ∑ i, hA.eigenvalues i ^ j := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle]
  simp [Matrix.diagonal_pow]

lemma closedWalkCount_cast_eq_sum_eigenvalues_pow {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) :
    (Conflict28.closedWalkCount A m : ℝ) =
      ∑ i, ((A.isHermitian_adjMatrix ℝ).eigenvalues i) ^ m := by
  rw [Conflict28.closedWalkCount_cast_eq_trace]
  exact trace_pow_eq_sum_eigenvalues_pow _ _ _

/-- The `L²⁷`--`L²²⁸` interpolation used after cutting a
28-step closed walk into pieces of lengths 13 and 14. -/
lemma closedWalkCount_interpolation_28 {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj] :
    (Conflict28.closedWalkCount A 26 : ℝ) ≤
      (Fintype.card W : ℝ) ^ ((1 : ℝ) / 14) *
        (Conflict28.closedWalkCount A 28 : ℝ) ^ ((13 : ℝ) / 14) := by
  let hA := A.isHermitian_adjMatrix ℝ
  let lam : W → ℝ := hA.eigenvalues
  have hholder : Real.HolderConjugate (14 : ℝ) ((14 : ℝ) / 13) := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg
    (s := Finset.univ) (f := fun _ : W ↦ (1 : ℝ))
    (g := fun i : W ↦ (lam i ^ 2) ^ (13 : ℕ)) hholder
    (by intro i hi; positivity) (by intro i hi; positivity)
  dsimp [hA, lam] at hh
  have hleft (x : ℝ) : x ^ 26 = (x ^ 2) ^ 13 := by ring
  have hright (x : ℝ) :
      ((x ^ 2) ^ (13 : ℕ)) ^ ((14 : ℝ) / 13) = x ^ 28 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (sq_nonneg x)]
    norm_num
    ring
  simp_rw [hright] at hh
  simp_rw [← hleft] at hh
  rw [closedWalkCount_cast_eq_sum_eigenvalues_pow,
    closedWalkCount_cast_eq_sum_eigenvalues_pow]
  simp only [one_mul, Real.one_rpow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hh
  convert hh using 1 <;> norm_num

end Erdos113Moments28

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/ConflictSides28.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Erdos113Sides28

open Conflict28

abbrev LowHalfCycleSide {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (b : Bool) (t : ℝ) :=
  Σ z : W, Σ x₁ : {x : W // side x = b},
    FixedWalk A 13 z x₁.1 ×
      Σ x₂ : A.neighborSet x₁.1,
        {q : FixedWalk A 14 x₂.1 z //
          (walkCount A 14 x₂.1 z : ℝ) <
            t * (walkCount A 13 z x₁.1 : ℝ)}

abbrev HighBadHalfCycleSide {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (b : Bool) (t : ℝ) :=
  Σ z : W, Σ x₂ : {x : W // side x = !b},
    Σ q : FixedWalk A 14 x₂.1 z,
      Σ x₁ : {x : ↑(walkConflictingNeighbors14 A R q) // side x.1 = b},
        {p : FixedWalk A 13 z x₁.1.1 //
          t * (walkCount A 13 z x₁.1.1 : ℝ) ≤
            (walkCount A 14 x₂.1 z : ℝ)}

lemma card_LowHalfCycleSide_cast {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (b : Bool) (t : ℝ) :
    (Fintype.card (LowHalfCycleSide A side b t) : ℝ) =
      ∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 13 z x₁.1 : ℝ) *
          ∑ x₂ : A.neighborSet x₁.1,
            (Fintype.card {q : FixedWalk A 14 x₂.1 z //
              (walkCount A 14 x₂.1 z : ℝ) <
                t * (walkCount A 13 z x₁.1 : ℝ)} : ℝ) := by
  simp only [LowHalfCycleSide, Fintype.card_sigma, Fintype.card_prod,
    Nat.cast_sum, Nat.cast_mul]
  rfl

lemma card_LowHalfCycleSide_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (b : Bool) (t D : ℝ) (ht : 0 ≤ t) (hD : 0 ≤ D)
    (hdegree : ∀ x, side x = b → (A.degree x : ℝ) ≤ D) :
    (Fintype.card (LowHalfCycleSide A side b t) : ℝ) ≤
      D * t * (closedWalkCount A 26 : ℝ) := by
  rw [card_LowHalfCycleSide_cast]
  calc
    (∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 13 z x₁.1 : ℝ) *
          ∑ x₂ : A.neighborSet x₁.1,
            (Fintype.card {q : FixedWalk A 14 x₂.1 z //
              (walkCount A 14 x₂.1 z : ℝ) <
                t * (walkCount A 13 z x₁.1 : ℝ)} : ℝ)) ≤
      ∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 13 z x₁.1 : ℝ) *
          (D * (t * (walkCount A 13 z x₁.1 : ℝ))) := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro x₁ _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        (∑ x₂ : A.neighborSet x₁.1,
            (Fintype.card {q : FixedWalk A 14 x₂.1 z //
              (walkCount A 14 x₂.1 z : ℝ) <
                t * (walkCount A 13 z x₁.1 : ℝ)} : ℝ)) ≤
            ∑ _x₂ : A.neighborSet x₁.1,
              t * (walkCount A 13 z x₁.1 : ℝ) := by
          apply Finset.sum_le_sum
          intro x₂ _
          exact card_lowFixedWalks_le A t ht z x₁.1 x₂
        _ = (A.degree x₁.1 : ℝ) *
              (t * (walkCount A 13 z x₁.1 : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            SimpleGraph.card_neighborSet_eq_degree, Nat.cast_mul]
        _ ≤ D * (t * (walkCount A 13 z x₁.1 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right (hdegree x₁.1 x₁.2)
            (mul_nonneg ht (by positivity))
    _ = D * t * (∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 13 z x₁.1 : ℝ) ^ 2) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x₁ _
      ring
    _ ≤ D * t * (∑ z : W, ∑ x₁ : W,
        (walkCount A 13 z x₁ : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD ht)
      apply Finset.sum_le_sum
      intro z _
      rw [← Finset.sum_subtype (Finset.univ.filter fun x : W ↦ side x = b)
        (by simp) (fun x ↦ (walkCount A 13 z x : ℝ) ^ 2)]
      apply Finset.sum_le_sum_of_subset_of_nonneg (by simp)
      intro x _ _
      positivity
    _ = D * t * (closedWalkCount A 26 : ℝ) := by
      rw [show 26 = 2 * 13 by norm_num,
        closedWalkCount_cast_eq_sum_walkCount_sq]

lemma card_walkConflictingNeighbors14_le_at {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (s : ℝ)
    (hsymm : ∀ x y, R x y → R y x)
    {z y : W} (q : FixedWalk A 14 y z)
    (hlocal : ∀ u,
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s) :
    ((walkConflictingNeighbors14 A R q).card : ℝ) ≤ 14 * s := by
  classical
  let E (i : Fin 7) (j : Fin 2) :=
    (A.neighborFinset y).filter (R (q.1.getVert (2 * i.val + j.val)))
  let U := Finset.univ.biUnion fun i : Fin 7 ↦ Finset.univ.biUnion (E i)
  have hsubset : walkConflictingNeighbors14 A R q ⊆ U := by
    intro x hx
    rw [walkConflictingNeighbors14, Finset.mem_filter] at hx
    have hconf := hx.2
    change ∃ i : Fin 7, ∃ j : Fin 2,
      R x (q.1.getVert (2 * i.val + j.val)) at hconf
    obtain ⟨i, j, hi⟩ := hconf
    simp only [U, Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ _, j, Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr ⟨hx.1, hsymm _ _ hi⟩
  calc
    ((walkConflictingNeighbors14 A R q).card : ℝ) ≤ (U.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ i : Fin 7, ∑ j : Fin 2, ((E i j).card : ℝ) := by
      calc
        (U.card : ℝ) ≤
            ∑ i : Fin 7, (((Finset.univ.biUnion (E i)).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ i : Fin 7, ∑ j : Fin 2, ((E i j).card : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin 7, ∑ _j : Fin 2, s := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact hlocal _
    _ = 14 * s := by simp; ring

lemma card_HighBadHalfCycleSide_cast {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (b : Bool) (t : ℝ) :
    (Fintype.card (HighBadHalfCycleSide A R side b t) : ℝ) =
      ∑ z : W, ∑ x₂ : {x : W // side x = !b},
        ∑ q : FixedWalk A 14 x₂.1 z,
          ∑ x₁ : {x : ↑(walkConflictingNeighbors14 A R q) // side x.1 = b},
            (Fintype.card {p : FixedWalk A 13 z x₁.1.1 //
              t * (walkCount A 13 z x₁.1.1 : ℝ) ≤
                (walkCount A 14 x₂.1 z : ℝ)} : ℝ) := by
  simp only [HighBadHalfCycleSide, Fintype.card_sigma, Nat.cast_sum]

lemma card_HighBadHalfCycleSide_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (b : Bool) (t s : ℝ)
    (ht : 0 < t) (hs : 0 ≤ s)
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y, side y = !b →
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s) :
    (Fintype.card (HighBadHalfCycleSide A R side b t) : ℝ) ≤
      14 * s * t⁻¹ * (closedWalkCount A 28 : ℝ) := by
  rw [card_HighBadHalfCycleSide_cast]
  calc
    (∑ z : W, ∑ x₂ : {x : W // side x = !b},
        ∑ q : FixedWalk A 14 x₂.1 z,
          ∑ x₁ : {x : ↑(walkConflictingNeighbors14 A R q) // side x.1 = b},
            (Fintype.card {p : FixedWalk A 13 z x₁.1.1 //
              t * (walkCount A 13 z x₁.1.1 : ℝ) ≤
                (walkCount A 14 x₂.1 z : ℝ)} : ℝ)) ≤
      ∑ z : W, ∑ x₂ : {x : W // side x = !b},
        ∑ _q : FixedWalk A 14 x₂.1 z,
          14 * s * (t⁻¹ * (walkCount A 14 x₂.1 z : ℝ)) := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro x₂ _
      apply Finset.sum_le_sum
      intro q _
      calc
        (∑ x₁ : {x : ↑(walkConflictingNeighbors14 A R q) // side x.1 = b},
            (Fintype.card {p : FixedWalk A 13 z x₁.1.1 //
              t * (walkCount A 13 z x₁.1.1 : ℝ) ≤
                (walkCount A 14 x₂.1 z : ℝ)} : ℝ)) ≤
            ∑ _x₁ : {x : ↑(walkConflictingNeighbors14 A R q) // side x.1 = b},
              t⁻¹ * (walkCount A 14 x₂.1 z : ℝ) := by
          apply Finset.sum_le_sum
          intro x₁ _
          exact card_highFixedWalks_le A R t ht z x₂.1 q x₁.1
        _ = (Fintype.card {x : ↑(walkConflictingNeighbors14 A R q) //
              side x.1 = b} : ℝ) *
              (t⁻¹ * (walkCount A 14 x₂.1 z : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Nat.cast_mul]
        _ ≤ ((walkConflictingNeighbors14 A R q).card : ℝ) *
              (t⁻¹ * (walkCount A 14 x₂.1 z : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (inv_nonneg.mpr ht.le) (by positivity))
          have hc := Fintype.card_subtype_le
            (fun x : ↑(walkConflictingNeighbors14 A R q) ↦ side x.1 = b)
          have hc' : Fintype.card {x : ↑(walkConflictingNeighbors14 A R q) //
                side x.1 = b} ≤ (walkConflictingNeighbors14 A R q).card := by
            simpa only [Fintype.card_coe] using hc
          exact_mod_cast hc'
        _ ≤ (14 * s) *
              (t⁻¹ * (walkCount A 14 x₂.1 z : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (inv_nonneg.mpr ht.le) (by positivity))
          exact card_walkConflictingNeighbors14_le_at A R s hsymm q
            (fun u ↦ hlocal u x₂.1 x₂.2)
        _ = 14 * s *
              (t⁻¹ * (walkCount A 14 x₂.1 z : ℝ)) := by ring
    _ = 14 * s * t⁻¹ * (∑ z : W,
        ∑ x₂ : {x : W // side x = !b},
          (walkCount A 14 x₂.1 z : ℝ) ^ 2) := by
      simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Finset.mul_sum, walkCount]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x₂ _
      ring
    _ ≤ 14 * s * t⁻¹ * (∑ z : W, ∑ x₂ : W,
        (walkCount A 14 x₂ z : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro z _
      rw [← Finset.sum_subtype (Finset.univ.filter fun x : W ↦ side x = !b)
        (by simp) (fun x ↦ (walkCount A 14 x z : ℝ) ^ 2)]
      apply Finset.sum_le_sum_of_subset_of_nonneg (by simp)
      intro x _ _
      positivity
    _ = 14 * s * t⁻¹ * (closedWalkCount A 28 : ℝ) := by
      rw [show 28 = 2 * 14 by norm_num,
        closedWalkCount_cast_eq_sum_walkCount_sq]
      congr 1
      exact Finset.sum_comm

abbrev HalfCycleSideSplit {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ) :=
  Σ b : Bool,
    LowHalfCycleSide A side b (t b) ⊕
      HighBadHalfCycleSide A R side b (t b)

noncomputable def encodeBadHalfCycleSideSplit {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x) :
    BadHalfCycle A R → HalfCycleSideSplit A R side t
  | ⟨⟨z, x₁, p, x₂, q⟩, hbad⟩ =>
      let b := side x₁
      if hlow : (walkCount A 14 x₂.1 z : ℝ) <
          t b * (walkCount A 13 z x₁ : ℝ) then
        ⟨b, Sum.inl ⟨z, ⟨x₁, rfl⟩, p, x₂, ⟨q, hlow⟩⟩⟩
      else
        ⟨b, Sum.inr ⟨z, ⟨x₂.1, hcross x₂.2⟩, q,
          ⟨⟨x₁, by
            rw [mem_walkConflictingNeighbors14]
            exact ⟨by simpa using x₂.2.symm, hbad⟩⟩, rfl⟩,
          ⟨p, le_of_not_gt hlow⟩⟩⟩

noncomputable def decodeHalfCycleSideSplit {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ) :
    HalfCycleSideSplit A R side t → RawHalfCycle A
  | ⟨_b, Sum.inl ⟨z, x₁, p, x₂, q⟩⟩ =>
      ⟨z, x₁.1, p, x₂, q.1⟩
  | ⟨_b, Sum.inr ⟨z, x₂, q, x₁, p⟩⟩ =>
      ⟨z, x₁.1.1, p.1,
        ⟨x₂.1, by
          have hx := x₁.1.2
          rw [mem_walkConflictingNeighbors14] at hx
          exact hx.1.symm⟩,
        q⟩

lemma decode_encodeBadHalfCycleSideSplit {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (b : BadHalfCycle A R) :
    decodeHalfCycleSideSplit A R side t
        (encodeBadHalfCycleSideSplit A R side t hcross b) =
      eraseBadHalfCycle A R b := by
  rcases b with ⟨⟨z, x₁, p, x₂, q⟩, hbad⟩
  simp only [encodeBadHalfCycleSideSplit]
  split <;> simp [decodeHalfCycleSideSplit, eraseBadHalfCycle]

lemma encodeBadHalfCycleSideSplit_injective {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x) :
    Function.Injective (encodeBadHalfCycleSideSplit A R side t hcross) := by
  intro b c h
  apply eraseBadHalfCycle_injective A R
  rw [← decode_encodeBadHalfCycleSideSplit A R side t hcross b,
    ← decode_encodeBadHalfCycleSideSplit A R side t hcross c, h]

lemma card_BadHalfCycle_side_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t D s : Bool → ℝ)
    (ht : ∀ b, 0 < t b) (hD : ∀ b, 0 ≤ D b) (hs : ∀ b, 0 ≤ s b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D (side x))
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y,
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s (side y)) :
    (Fintype.card (BadHalfCycle A R) : ℝ) ≤
      ∑ b : Bool, (D b * t b * (closedWalkCount A 26 : ℝ) +
        14 * s (!b) * (t b)⁻¹ * (closedWalkCount A 28 : ℝ)) := by
  have hcardNat := Fintype.card_le_of_injective
    (encodeBadHalfCycleSideSplit A R side t hcross)
    (encodeBadHalfCycleSideSplit_injective A R side t hcross)
  have hcard : (Fintype.card (BadHalfCycle A R) : ℝ) ≤
      Fintype.card (HalfCycleSideSplit A R side t) := by
    exact_mod_cast hcardNat
  rw [Fintype.card_sigma, Nat.cast_sum] at hcard
  refine hcard.trans ?_
  apply Finset.sum_le_sum
  intro b _
  rw [Fintype.card_sum, Nat.cast_add]
  apply add_le_add
  · exact card_LowHalfCycleSide_le A side b (t b) (D b)
      (ht b).le (hD b) (fun x hx ↦ by simpa [hx] using hdegree x)
  · exact card_HighBadHalfCycleSide_le A R side b (t b) (s (!b))
      (ht b) (hs (!b)) hsymm (fun u y hy ↦ by simpa [hy] using hlocal u y)

lemma card_BadClosedWalk28_side_cast_le {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t D s : Bool → ℝ)
    (ht : ∀ b, 0 < t b) (hD : ∀ b, 0 ≤ D b) (hs : ∀ b, 0 ≤ s b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D (side x))
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y,
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s (side y)) :
    (Fintype.card (Encode28.BadClosedWalk28 A R) : ℝ) ≤
      28 * ∑ b : Bool,
        (D b * t b * (closedWalkCount A 26 : ℝ) +
          14 * s (!b) * (t b)⁻¹ * (closedWalkCount A 28 : ℝ)) := by
  calc
    (Fintype.card (Encode28.BadClosedWalk28 A R) : ℝ) ≤
        28 * (Fintype.card (BadHalfCycle A R) : ℝ) := by
      exact_mod_cast Encode28.card_BadClosedWalk28_le A R hsymm
    _ ≤ 28 * ∑ b : Bool,
        (D b * t b * (closedWalkCount A 26 : ℝ) +
          14 * s (!b) * (t b)⁻¹ * (closedWalkCount A 28 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact card_BadHalfCycle_side_le A R side t D s ht hD hs hcross hdegree
        hsymm hlocal

end Erdos113Sides28

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Genuine28.lean` -/

section
open scoped Real SimpleGraph BigOperators

namespace Erdos113Genuine28

open Erdos113Cycles

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev HomCycle28 (G : SimpleGraph V) :=
  {x : Fin 28 → V // IsHomCycle G x}

abbrev RepeatedHomCycle28 (G : SimpleGraph V) :=
  {x : HomCycle28 G // ¬ Function.Injective x.1}

noncomputable def homCyclePartition (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    HomCycle28 G → ↑(genuineCycles G 28) ⊕ RepeatedHomCycle28 G :=
  fun x ↦ by
    classical
    by_cases hinj : Function.Injective x.1
    · exact Sum.inl ⟨x.1, mem_genuineCycles.mpr ⟨hinj, x.2⟩⟩
    · exact Sum.inr ⟨x, hinj⟩

def homCyclePartitionDecode {G : SimpleGraph V} [DecidableRel G.Adj] :
    ↑(genuineCycles G 28) ⊕ RepeatedHomCycle28 G → (Fin 28 → V)
  | Sum.inl x => x.1
  | Sum.inr x => x.1.1

@[simp] lemma homCyclePartitionDecode_partition
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : HomCycle28 G) :
    homCyclePartitionDecode (homCyclePartition G x) = x.1 := by
  classical
  unfold homCyclePartition
  split <;> rfl

lemma homCyclePartition_injective (G : SimpleGraph V) [DecidableRel G.Adj] :
    Function.Injective (homCyclePartition G) := by
  intro x y hxy
  apply Subtype.ext
  have h := congrArg homCyclePartitionDecode hxy
  simpa using h

noncomputable def repeatedHomCycleToBadClosedWalk
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    RepeatedHomCycle28 G →
      Encode28.BadClosedWalk28 G (fun u v ↦ u = v) :=
  fun x ↦ by
    let P := Erdos113Cycle28.tupleClosedWalk x.1.1 x.1.2
    refine ⟨P, ?_⟩
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp x.2
    refine ⟨i, j, hne, ?_⟩
    have hread :=
      Erdos113Cycle28.closedWalkTuple_tupleClosedWalk x.1.1 x.1.2
    exact (congrFun hread i).trans (hij.trans (congrFun hread j).symm)

lemma repeatedHomCycleToBadClosedWalk_injective
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Function.Injective (repeatedHomCycleToBadClosedWalk G) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  have hP := congrArg (fun z ↦ (z.1 : Encode28.ClosedWalk28 G)) hxy
  change Erdos113Cycle28.tupleClosedWalk x.1.1 x.1.2 =
    Erdos113Cycle28.tupleClosedWalk y.1.1 y.1.2 at hP
  have hread := congrArg (Erdos113Cycle28.closedWalkTuple G) hP
  simpa only [Erdos113Cycle28.closedWalkTuple_tupleClosedWalk] using hread

lemma card_homCycle28_eq_closedWalkCount
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card (HomCycle28 G) = Conflict28.closedWalkCount G 28 := by
  calc
    Fintype.card (HomCycle28 G) = Conflict.closedWalkCount G 28 :=
      Erdos113Cycle28.card_homCycle28_eq_closedWalkCount G
    _ = Conflict28.closedWalkCount G 28 := rfl

abbrev RelationFreeHomCycle28
    (G : SimpleGraph V) (R : V → V → Prop) :=
  {x : HomCycle28 G // ∀ i j, i ≠ j → ¬ R (x.1 i) (x.1 j)}

abbrev RelationBadHomCycle28
    (G : SimpleGraph V) (R : V → V → Prop) :=
  {x : HomCycle28 G // ∃ i j, i ≠ j ∧ R (x.1 i) (x.1 j)}

noncomputable def relationPartition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R] :
    HomCycle28 G → RelationFreeHomCycle28 G R ⊕ RelationBadHomCycle28 G R :=
  fun x ↦ by
    classical
    by_cases hfree : ∀ i j, i ≠ j → ¬ R (x.1 i) (x.1 j)
    · exact Sum.inl ⟨x, hfree⟩
    · push Not at hfree
      exact Sum.inr ⟨x, hfree⟩

def relationPartitionDecode
    {G : SimpleGraph V} {R : V → V → Prop} :
    RelationFreeHomCycle28 G R ⊕ RelationBadHomCycle28 G R → (Fin 28 → V)
  | Sum.inl x => x.1.1
  | Sum.inr x => x.1.1

@[simp] lemma relationPartitionDecode_partition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R] (x : HomCycle28 G) :
    relationPartitionDecode (relationPartition G R x) = x.1 := by
  classical
  unfold relationPartition
  split <;> rfl

lemma relationPartition_injective
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R] :
    Function.Injective (relationPartition G R) := by
  intro x y hxy
  apply Subtype.ext
  have h := congrArg relationPartitionDecode hxy
  simpa using h

noncomputable def relationBadHomCycleToBadClosedWalk
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R] :
    RelationBadHomCycle28 G R → Encode28.BadClosedWalk28 G R :=
  fun x ↦ by
    let P := Erdos113Cycle28.tupleClosedWalk x.1.1 x.1.2
    refine ⟨P, ?_⟩
    obtain ⟨i, j, hij, hR⟩ := x.2
    refine ⟨i, j, hij, ?_⟩
    have hread :=
      Erdos113Cycle28.closedWalkTuple_tupleClosedWalk x.1.1 x.1.2
    have hi := congrFun hread i
    have hj := congrFun hread j
    rw [← hi, ← hj] at hR
    simpa [P, Encode28.cv, Erdos113Cycle28.closedWalkTuple] using hR

@[simp] lemma relationBadHomCycleToBadClosedWalk_walk
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R]
    (x : RelationBadHomCycle28 G R) :
    ((relationBadHomCycleToBadClosedWalk G R x).1 : Encode28.ClosedWalk28 G) =
      Erdos113Cycle28.tupleClosedWalk x.1.1 x.1.2 := by
  rfl

lemma relationBadHomCycleToBadClosedWalk_injective
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R] :
    Function.Injective (relationBadHomCycleToBadClosedWalk G R) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  have hP := congrArg (fun z ↦ (z.1 : Encode28.ClosedWalk28 G)) hxy
  simp only [relationBadHomCycleToBadClosedWalk_walk] at hP
  have hread := congrArg (Erdos113Cycle28.closedWalkTuple G) hP
  simpa only [Erdos113Cycle28.closedWalkTuple_tupleClosedWalk] using hread

lemma card_homCycle28_le_relationFree_add_bad
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R] :
    Fintype.card (HomCycle28 G) ≤
      Fintype.card (RelationFreeHomCycle28 G R) +
        Fintype.card (Encode28.BadClosedWalk28 G R) := by
  have hpartition := Fintype.card_le_of_injective (relationPartition G R)
    (relationPartition_injective G R)
  rw [Fintype.card_sum] at hpartition
  have hbad := Fintype.card_le_of_injective
    (relationBadHomCycleToBadClosedWalk G R)
    (relationBadHomCycleToBadClosedWalk_injective G R)
  omega

lemma closedWalkCount_26_interpolation_28
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Conflict28.closedWalkCount G 26 : ℝ) ≤
      (Fintype.card V : ℝ) ^ ((1 : ℝ) / 14) *
        (Conflict28.closedWalkCount G 28 : ℝ) ^ ((13 : ℝ) / 14) :=
  Erdos113Moments28.closedWalkCount_interpolation_28 G

lemma closedWalkCount_28_lower_bipartite
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (d : Bool → ℝ)
    (hd : ∀ b, 0 ≤ d b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hmin : ∀ x, d (side x) ≤ (G.degree x : ℝ)) :
    (d false * d true) ^ 14 ≤
      (Conflict28.closedWalkCount G 28 : ℝ) := by
  let q := (d false * d true) ^ 7
  have hq : 0 ≤ q := by
    dsimp [q]
    exact pow_nonneg (mul_nonneg (hd false) (hd true)) _
  have hmass (x : V) : q ≤ Lower.walkMass G 14 x := by
    have h := Erdos113LowerBipartite.walkMass_lower_bipartite
      G side d hd hcross hmin 14 x
    rw [show 14 = 2 * 7 by norm_num,
      Erdos113LowerBipartite.alternatingProduct_even] at h
    cases hx : side x <;> simpa [q, hx, mul_comm] using h
  have h := Erdos113LowerBipartite.closedWalkCount_lower_of_walkMass
    G q hq 14 hmass
  rw [show 2 * 14 = 28 by norm_num] at h
  calc
    (d false * d true) ^ 14 = q ^ 2 := by dsimp [q]; ring
    _ ≤ (Conflict.closedWalkCount G 28 : ℝ) := h
    _ = (Conflict28.closedWalkCount G 28 : ℝ) := rfl

lemma relationFreeCycles_half_closedWalkCount_of_side_numerics
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R]
    (side : V → Bool) (t D : Bool → ℝ)
    (ht : ∀ b, 0 < t b) (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdegree : ∀ x, (G.degree x : ℝ) ≤ D (side x))
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y,
      (((G.neighborFinset y).filter (R u)).card : ℝ) ≤ 1)
    (hnum : 28 * ∑ b : Bool,
        (D b * t b * (Conflict28.closedWalkCount G 26 : ℝ) +
          14 * (t b)⁻¹ * (Conflict28.closedWalkCount G 28 : ℝ)) ≤
      (Conflict28.closedWalkCount G 28 : ℝ) / 2) :
    (Conflict28.closedWalkCount G 28 : ℝ) / 2 ≤
      (Fintype.card (RelationFreeHomCycle28 G R) : ℝ) := by
  let s : Bool → ℝ := fun _ ↦ 1
  have hbad := Erdos113Sides28.card_BadClosedWalk28_side_cast_le
    G R side t D s ht hD (fun _ ↦ by norm_num) hcross hdegree hsymm
      (fun u y ↦ by simpa [s] using hlocal u y)
  have hcard := card_homCycle28_le_relationFree_add_bad G R
  rw [card_homCycle28_eq_closedWalkCount G] at hcard
  have hcardR : (Conflict28.closedWalkCount G 28 : ℝ) ≤
      (Fintype.card (RelationFreeHomCycle28 G R) : ℝ) +
        (Fintype.card (Encode28.BadClosedWalk28 G R) : ℝ) := by
    exact_mod_cast hcard
  have hbad' : (Fintype.card (Encode28.BadClosedWalk28 G R) : ℝ) ≤
      28 * ∑ b : Bool,
        (D b * t b * (Conflict28.closedWalkCount G 26 : ℝ) +
          14 * (t b)⁻¹ * (Conflict28.closedWalkCount G 28 : ℝ)) := by
    simpa [s] using hbad
  linarith

/-- Two-sided version used for a pruned bipartite degree cell.  The two
degree scales may be different; only the almost-regularity ratio on each
side enters the estimate. -/
lemma relationFreeCycles_half_of_bipartiteAlmostRegular
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R]
    (side : V → Bool) (d : Bool → ℝ) (L N : ℝ)
    (hN : N = Fintype.card V)
    (hd : ∀ b, 0 < d b) (hL : 0 < L)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hmin : ∀ x, d (side x) ≤ (G.degree x : ℝ))
    (hmax : ∀ x, (G.degree x : ℝ) ≤ L * d (side x))
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y,
      (((G.neighborFinset y).filter (R u)).card : ℝ) ≤ 1)
    (hlarge : ∀ b, 702464 * L * N ^ ((1 : ℝ) / 14) ≤ d b) :
    (Conflict28.closedWalkCount G 28 : ℝ) / 2 ≤
      (Fintype.card (RelationFreeHomCycle28 G R) : ℝ) := by
  have hNpos : 0 < N := by rw [hN]; positivity
  let Q : ℝ := N ^ ((1 : ℝ) / 14)
  have hQ : 0 < Q := Real.rpow_pos_of_pos hNpos _
  let H : ℝ := Conflict28.closedWalkCount G 28
  let H' : ℝ := Conflict28.closedWalkCount G 26
  let p : ℝ := d false * d true
  have hp : 0 < p := by dsimp [p]; exact mul_pos (hd false) (hd true)
  have hHlower : p ^ 14 ≤ H := by
    dsimp [H, p]
    exact closedWalkCount_28_lower_bipartite
      G side d (fun b ↦ (hd b).le) hcross hmin
  have hHpos : 0 < H := lt_of_lt_of_le (by positivity : 0 < p ^ 14) hHlower
  have hinterp : H' ≤ Q * H ^ ((13 : ℝ) / 14) := by
    dsimp [H', Q, H]
    simpa [hN] using closedWalkCount_26_interpolation_28 G
  have hrootid :
      H ^ ((13 : ℝ) / 14) * H ^ ((1 : ℝ) / 14) = H := by
    rw [← Real.rpow_add hHpos]
    norm_num
  have hproot : p ≤ H ^ ((1 : ℝ) / 14) := by
    have hr := Real.rpow_le_rpow (by positivity : 0 ≤ p ^ 14) hHlower
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 14)
    convert hr using 1
    conv_rhs => rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hp.le]
    norm_num
  have hHp : H' * p ≤ Q * H := by
    calc
      H' * p ≤ (Q * H ^ ((13 : ℝ) / 14)) * p := by gcongr
      _ ≤ (Q * H ^ ((13 : ℝ) / 14)) *
          H ^ ((1 : ℝ) / 14) := by gcongr
      _ = Q *
          (H ^ ((13 : ℝ) / 14) * H ^ ((1 : ℝ) / 14)) := by ring
      _ = Q * H := by rw [hrootid]
  let t : Bool → ℝ := fun b ↦ p / (224 * (L * d b) * Q)
  have ht : ∀ b, 0 < t b := by
    intro b
    dsimp [t]
    exact div_pos hp (mul_pos (mul_pos (by norm_num) (mul_pos hL (hd b))) hQ)
  have htlarge : ∀ b, 3136 ≤ t b := by
    intro b
    apply (le_div_iff₀
      (mul_pos (mul_pos (by norm_num) (mul_pos hL (hd b))) hQ)).2
    change 3136 * (224 * (L * d b) * Q) ≤ p
    cases b
    · calc
        3136 * (224 * (L * d false) * Q) =
            d false * (702464 * L * Q) := by ring
        _ ≤ d false * d true :=
          mul_le_mul_of_nonneg_left (by simpa [Q] using hlarge true) (hd false).le
        _ = p := by rfl
    · calc
        3136 * (224 * (L * d true) * Q) =
            d true * (702464 * L * Q) := by ring
        _ ≤ d true * d false :=
          mul_le_mul_of_nonneg_left (by simpa [Q] using hlarge false) (hd true).le
        _ = p := by dsimp [p]; ring
  have hquot : (H' * p) / Q ≤ H := by
    apply (div_le_iff₀ hQ).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hHp
  have hfirst : ∀ b,
      (L * d b) * t b * H' ≤ H / 224 := by
    intro b
    have hid : (L * d b) * t b * H' = ((H' * p) / Q) / 224 := by
      dsimp [t]
      field_simp [ne_of_gt hL, ne_of_gt (hd b), ne_of_gt hQ]
    rw [hid]
    exact div_le_div_of_nonneg_right hquot (by norm_num)
  have htinv : ∀ b, (t b)⁻¹ ≤ (3136 : ℝ)⁻¹ := by
    intro b
    exact (inv_le_inv₀ (ht b) (by norm_num)).2 (htlarge b)
  have hsecond : ∀ b, 14 * (t b)⁻¹ * H ≤ H / 224 := by
    intro b
    calc
      14 * (t b)⁻¹ * H ≤ 14 * (3136 : ℝ)⁻¹ * H := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (htinv b) (by norm_num)) hHpos.le
      _ = H / 224 := by norm_num; ring
  apply relationFreeCycles_half_closedWalkCount_of_side_numerics
    G R side t (fun b ↦ L * d b) ht (fun b ↦ (mul_pos hL (hd b)).le)
    hcross hmax hsymm hlocal
  calc
    28 * ∑ b : Bool,
        ((L * d b) * t b * (Conflict28.closedWalkCount G 26 : ℝ) +
          14 * (t b)⁻¹ * (Conflict28.closedWalkCount G 28 : ℝ)) =
        28 * ∑ b : Bool,
          ((L * d b) * t b * H' + 14 * (t b)⁻¹ * H) := by
      rfl
    _ ≤ 28 * ∑ _b : Bool, (H / 224 + H / 224) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun b _ ↦ add_le_add (hfirst b) (hsecond b))
    _ = (Conflict28.closedWalkCount G 28 : ℝ) / 2 := by
      simp only [Fintype.sum_bool]
      dsimp [H]
      ring

end Erdos113Genuine28

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Supersaturation28.lean` -/

section
open scoped BigOperators Real SimpleGraph

namespace Erdos113Supersaturation28

noncomputable section

open Erdos113Cycles Erdos113Regular Erdos113BipartiteGraph
  Erdos113CellPruning Erdos113Genuine28

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A polynomial-slack, fully finite substitute for the fixed-length
Morris--Saxton supersaturation statement needed in the many-four-cycle
case.  The powers of `degreeBinCount` are harmless logarithmic losses.

The numerical hypothesis says that the minimum degree furnished by the
dense pruned cell is large enough for the length-28 conflict estimate. -/
theorem genuineCycles28_lower_of_edgeDensity
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (hedge : ∃ x y, A.Adj x y)
    (hlarge :
      702464 * (16 * (degreeBinCount (W := W) : ℝ)) *
          (2 * Fintype.card W : ℝ) ^ ((1 : ℝ) / 14) ≤
        (A.edgeFinset.card : ℝ) /
          (32 * (degreeBinCount (W := W) : ℝ) ^ 3 * Fintype.card W)) :
    ((A.edgeFinset.card : ℝ) /
        (32 * (degreeBinCount (W := W) : ℝ) ^ 3 * Fintype.card W)) ^ 28 /
        (2 * (2 : ℝ) ^ 28) ≤
      ((genuineCycles A 28).card : ℝ) := by
  classical
  obtain ⟨i, j, E, hEsub, hEne, hEdense, hleftMin, hrightMin⟩ :=
    exists_pruned_cell A hedge
  let B := retainedGraph E
  let side : LiveLeft E ⊕ LiveRight E → Bool :=
    Sum.elim (fun _ ↦ false) (fun _ ↦ true)
  let proj : LiveLeft E ⊕ LiveRight E → W :=
    Sum.elim (fun x ↦ x.1.1) (fun y ↦ y.1.1)
  let R : (LiveLeft E ⊕ LiveRight E) →
      (LiveLeft E ⊕ LiveRight E) → Prop := fun x y ↦ proj x = proj y
  let L : ℝ := degreeBinCount (W := W)
  let cap : Bool → ℝ := fun b ↦
    if b then 2 ^ (j.val + 1) else 2 ^ (i.val + 1)
  let d : Bool → ℝ := fun b ↦ cap b / (16 * L)
  let δ : ℝ := (A.edgeFinset.card : ℝ) /
    (32 * L ^ 3 * Fintype.card W)
  let N : ℝ := Fintype.card (LiveLeft E ⊕ LiveRight E)
  letI : DecidableRel B.Adj := inferInstance
  letI : DecidableRel R := fun x y ↦ inferInstanceAs (Decidable (proj x = proj y))
  letI : Nonempty (LiveLeft E ⊕ LiveRight E) :=
    nonempty_of_nonempty E hEne
  have hn : 0 < (Fintype.card W : ℝ) := by
    obtain ⟨x, y, hxy⟩ := hedge
    have : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨x⟩
    exact_mod_cast this
  have hL : 0 < L := by
    dsimp [L, degreeBinCount]
    positivity
  have hcap : ∀ b, 0 < cap b := by
    intro b
    cases b <;> simp [cap] <;> positivity
  have hd : ∀ b, 0 < d b := by
    intro b
    dsimp [d]
    exact div_pos (hcap b) (mul_pos (by norm_num) hL)
  have hcardN : Fintype.card (LiveLeft E ⊕ LiveRight E) ≤
      2 * Fintype.card W := by
    rw [Fintype.card_sum]
    have hl : Fintype.card (LiveLeft E) ≤ Fintype.card W := by
      calc
        Fintype.card (LiveLeft E) ≤ Fintype.card (BinVertex A i) :=
          Fintype.card_subtype_le _
        _ ≤ Fintype.card W := Fintype.card_subtype_le _
    have hr : Fintype.card (LiveRight E) ≤ Fintype.card W := by
      calc
        Fintype.card (LiveRight E) ≤ Fintype.card (BinVertex A j) :=
          Fintype.card_subtype_le _
        _ ≤ Fintype.card W := Fintype.card_subtype_le _
    omega
  have hNroot : N ^ ((1 : ℝ) / 14) ≤
      (2 * Fintype.card W : ℝ) ^ ((1 : ℝ) / 14) := by
    apply Real.rpow_le_rpow
    · dsimp [N]
      positivity
    · dsimp [N]
      exact_mod_cast hcardN
    · norm_num
  have hEcapLeft : E.card ≤ Fintype.card W * 2 ^ (i.val + 1) := by
    calc
      E.card ≤ Fintype.card (BinVertex A i) * 2 ^ (i.val + 1) :=
        card_le_card_mul_of_leftFiber_le E _ (fun x ↦ by
          exact (card_leftFiber_le_degree A i j E hEsub x).trans
            (degree_bounds_of_mem_bin A i x.2).2.le)
      _ ≤ Fintype.card W * 2 ^ (i.val + 1) := by
        gcongr
        exact Fintype.card_subtype_le _
  have hEcapRight : E.card ≤ Fintype.card W * 2 ^ (j.val + 1) := by
    calc
      E.card ≤ Fintype.card (BinVertex A j) * 2 ^ (j.val + 1) :=
        card_le_card_mul_of_rightFiber_le E _ (fun y ↦ by
          exact (card_rightFiber_le_degree A i j E hEsub y).trans
            (degree_bounds_of_mem_bin A j y.2).2.le)
      _ ≤ Fintype.card W * 2 ^ (j.val + 1) := by
        gcongr
        exact Fintype.card_subtype_le _
  have hδd : ∀ b, δ ≤ d b := by
    intro b
    have hnat : A.edgeFinset.card ≤
        2 * degreeBinCount (W := W) ^ 2 *
          (Fintype.card W * (if b then 2 ^ (j.val + 1) else 2 ^ (i.val + 1))) := by
      calc
        A.edgeFinset.card ≤
            2 * degreeBinCount (W := W) ^ 2 * E.card := hEdense
        _ ≤ 2 * degreeBinCount (W := W) ^ 2 *
            (Fintype.card W *
              (if b then 2 ^ (j.val + 1) else 2 ^ (i.val + 1))) := by
          gcongr
          cases b
          · simpa using hEcapLeft
          · simpa using hEcapRight
    have hreal : (A.edgeFinset.card : ℝ) ≤
        2 * L ^ 2 * (Fintype.card W : ℝ) * cap b := by
      cases b
      · simp only [Bool.false_eq_true, if_false] at hnat
        dsimp [L, cap]
        push_cast
        exact_mod_cast (by simpa [mul_assoc] using hnat)
      · simp only [if_true] at hnat
        dsimp [L, cap]
        push_cast
        exact_mod_cast (by simpa [mul_assoc] using hnat)
    dsimp [δ, d]
    apply (div_le_iff₀ (by positivity :
      (0 : ℝ) < 32 * L ^ 3 * Fintype.card W)).2
    calc
      (A.edgeFinset.card : ℝ) ≤
          2 * L ^ 2 * (Fintype.card W : ℝ) * cap b := hreal
      _ = cap b / (16 * L) *
          (32 * L ^ 3 * Fintype.card W) := by
        field_simp [ne_of_gt hL]
        ring
  have hprojAdj {x y : LiveLeft E ⊕ LiveRight E} (hxy : B.Adj x y) :
      A.Adj (proj x) (proj y) := by
    rcases x with x | x <;> rcases y with y | y
    · exact False.elim hxy
    · exact (mem_cellEdges A i j _).mp (hEsub hxy)
    · exact ((mem_cellEdges A i j _).mp (hEsub hxy)).symm
    · exact False.elim hxy
  have hdegreeMax (x : LiveLeft E ⊕ LiveRight E) :
      (B.degree x : ℝ) ≤ (16 * L) * d (side x) := by
    have hcapDegree : (B.degree x : ℝ) ≤ cap (side x) := by
      rcases x with x | x
      · rw [degree_inl]
        dsimp [side, cap]
        exact_mod_cast (card_leftFiber_le_degree A i j E hEsub x.1).trans
          (degree_bounds_of_mem_bin A i x.1.2).2.le
      · rw [degree_inr]
        dsimp [side, cap]
        exact_mod_cast (card_rightFiber_le_degree A i j E hEsub x.1).trans
          (degree_bounds_of_mem_bin A j x.1.2).2.le
    have hid : cap (side x) = (16 * L) * d (side x) := by
      dsimp [d]
      field_simp [ne_of_gt hL]
    exact hcapDegree.trans_eq hid
  have hdegreeMin (x : LiveLeft E ⊕ LiveRight E) :
      d (side x) ≤ (B.degree x : ℝ) := by
    rcases x with x | x
    · obtain ⟨y, hy⟩ := x.2
      have hinc : (E ∩ leftFiber (cellEdges A i j) x.1).Nonempty := by
        refine ⟨(x.1, y), Finset.mem_inter.mpr ⟨hy, ?_⟩⟩
        exact (mem_leftFiber _ _ _).mpr ⟨hEsub hy, rfl⟩
      have hm := hleftMin x.1 hinc
      rw [degree_inl]
      have hmR : ((cellThreshold (2 ^ (i.val + 1))
          (degreeBinCount (W := W)) : ℕ) : ℝ) ≤
          ((leftFiber E x.1).card : ℝ) := by exact_mod_cast hm
      have hbase := (cap_div_le_cast_cellThreshold
        (cap := 2 ^ (i.val + 1))
        (L := degreeBinCount (W := W))).trans hmR
      dsimp [d, cap, side, L]
      norm_num [Nat.cast_pow, Nat.cast_mul] at hbase ⊢
      simpa using hbase
    · obtain ⟨y, hy⟩ := x.2
      have hinc : (E ∩ rightFiber (cellEdges A i j) x.1).Nonempty := by
        refine ⟨(y, x.1), Finset.mem_inter.mpr ⟨hy, ?_⟩⟩
        exact (mem_rightFiber _ _ _).mpr ⟨hEsub hy, rfl⟩
      have hm := hrightMin x.1 hinc
      rw [degree_inr]
      have hmR : ((cellThreshold (2 ^ (j.val + 1))
          (degreeBinCount (W := W)) : ℕ) : ℝ) ≤
          ((rightFiber E x.1).card : ℝ) := by exact_mod_cast hm
      have hbase := (cap_div_le_cast_cellThreshold
        (cap := 2 ^ (j.val + 1))
        (L := degreeBinCount (W := W))).trans hmR
      dsimp [d, cap, side, L]
      norm_num [Nat.cast_pow, Nat.cast_mul] at hbase ⊢
      simpa using hbase
  have hcross : ∀ {x y}, B.Adj x y → side y = !side x := by
    intro x y hxy
    exact cross E hxy
  have hlocal (u y : LiveLeft E ⊕ LiveRight E) :
      (((B.neighborFinset y).filter (R u)).card : ℝ) ≤ 1 := by
    have hinj : Set.InjOn proj (B.neighborSet y) := by
      intro x hx z hz hxz
      rcases y with y | y
      · rcases x with x | x
        · exact False.elim hx
        · rcases z with z | z
          · exact False.elim hz
          · congr 1
            apply Subtype.ext
            apply Subtype.ext
            exact hxz
      · rcases x with x | x
        · rcases z with z | z
          · congr 1
            apply Subtype.ext
            apply Subtype.ext
            exact hxz
          · exact False.elim hz
        · exact False.elim hx
    have hsub : (B.neighborFinset y).filter (R u) ⊆
        (B.neighborFinset y).filter (fun z ↦ proj z = proj u) := by
      intro z hz
      have hz' := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hz'.1, hz'.2.symm⟩
    have hone : ((B.neighborFinset y).filter
        (fun z ↦ proj z = proj u)).card ≤ 1 := by
      by_contra! htwo
      obtain ⟨x, hx, z, hz, hxz⟩ := Finset.one_lt_card.mp htwo
      have hxeq := (Finset.mem_filter.mp hx).2
      have hzeq := (Finset.mem_filter.mp hz).2
      apply hxz
      apply hinj
      · exact (B.mem_neighborFinset y x).mp (Finset.mem_filter.mp hx).1
      · exact (B.mem_neighborFinset y z).mp (Finset.mem_filter.mp hz).1
      · exact hxeq.trans hzeq.symm
    exact_mod_cast (Finset.card_le_card hsub).trans hone
  have hlargeB : ∀ b,
      702464 * (16 * L) * N ^ ((1 : ℝ) / 14) ≤ d b := by
    intro b
    calc
      702464 * (16 * L) * N ^ ((1 : ℝ) / 14) ≤
          702464 * (16 * L) *
            (2 * Fintype.card W : ℝ) ^ ((1 : ℝ) / 14) := by
        gcongr
      _ ≤ δ := by simpa [δ, L] using hlarge
      _ ≤ d b := hδd b
  have hfree := relationFreeCycles_half_of_bipartiteAlmostRegular
    B R side d (16 * L) N rfl hd (by positivity) hcross hdegreeMin
      hdegreeMax (fun _ _ h ↦ h.symm) hlocal hlargeB
  have hδnonneg : 0 ≤ δ := by dsimp [δ]; positivity
  have hclosedLower : δ ^ 28 ≤ (Conflict28.closedWalkCount B 28 : ℝ) := by
    calc
      δ ^ 28 = (δ * δ) ^ 14 := by ring
      _ ≤ (d false * d true) ^ 14 := by
        apply pow_le_pow_left₀ (mul_nonneg hδnonneg hδnonneg)
        exact mul_le_mul (hδd false) (hδd true) hδnonneg (hd false).le
      _ ≤ (Conflict28.closedWalkCount B 28 : ℝ) :=
        closedWalkCount_28_lower_bipartite B side d
          (fun b ↦ (hd b).le) hcross hdegreeMin
  let f : RelationFreeHomCycle28 B R →
      (Fin 28 → Bool) × ↑(genuineCycles A 28) := fun x ↦
    (fun k ↦ side (x.1.1 k),
      ⟨fun k ↦ proj (x.1.1 k), by
        rw [mem_genuineCycles]
        refine ⟨?_, ?_⟩
        · intro p q hpq
          by_contra hpne
          exact x.2 p q hpne hpq
        · intro k
          exact hprojAdj (x.1.2 k)⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    funext k
    have hs := congrFun (congrArg Prod.fst hxy) k
    have hp := congrFun (congrArg (fun z ↦ (z.2.1 : Fin 28 → W)) hxy) k
    rcases hx : x.1.1 k with u | v <;> rcases hy : y.1.1 k with u' | v'
    · congr 1
      apply Subtype.ext
      apply Subtype.ext
      simpa [f, proj, hx, hy] using hp
    · have : false = true := by simpa [f, side, hx, hy] using hs
      contradiction
    · have : true = false := by simpa [f, side, hx, hy] using hs
      contradiction
    · congr 1
      apply Subtype.ext
      apply Subtype.ext
      simpa [f, proj, hx, hy] using hp
  have hcardNat := Fintype.card_le_of_injective f hf
  have hcard : (Fintype.card (RelationFreeHomCycle28 B R) : ℝ) ≤
      (2 : ℝ) ^ 28 * ((genuineCycles A 28).card : ℝ) := by
    have hcardNat' : Fintype.card (RelationFreeHomCycle28 B R) ≤
        2 ^ 28 * (genuineCycles A 28).card := by
      rw [← Fintype.card_coe]
      simpa using hcardNat
    exact_mod_cast hcardNat'
  have hpowpos : 0 < (2 : ℝ) ^ 28 := by positivity
  calc
    δ ^ 28 / (2 * (2 : ℝ) ^ 28) =
        (δ ^ 28 / 2) / (2 : ℝ) ^ 28 := by ring
    _ ≤ ((Conflict28.closedWalkCount B 28 : ℝ) / 2) /
          (2 : ℝ) ^ 28 := by
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hclosedLower (by norm_num)) hpowpos.le
    _ ≤ (Fintype.card (RelationFreeHomCycle28 B R) : ℝ) /
          (2 : ℝ) ^ 28 := div_le_div_of_nonneg_right hfree hpowpos.le
    _ ≤ ((genuineCycles A 28).card : ℝ) :=
      (div_le_iff₀ hpowpos).2 (by
        simpa [mul_comm] using hcard)

end

end Erdos113Supersaturation28

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Alternating56.lean` -/

section
open scoped SimpleGraph

namespace Erdos113Alternating56

open Erdos113Cycles

def halfIndex (p : Fin 56) : Fin 28 := ⟨p.val / 2, by omega⟩

def evenIndex (i : Fin 28) : Fin 56 := ⟨2 * i.val, by omega⟩

def oddIndex (i : Fin 28) : Fin 56 := ⟨2 * i.val + 1, by omega⟩

def alternatingTuple {V : Type*} (x y : Fin 28 → V) : Fin 56 → V :=
  fun p ↦ if p.val % 2 = 0 then x (halfIndex p) else y (halfIndex p)

@[simp] lemma halfIndex_evenIndex (i : Fin 28) : halfIndex (evenIndex i) = i := by
  apply Fin.ext
  simp [halfIndex, evenIndex]

@[simp] lemma halfIndex_oddIndex (i : Fin 28) : halfIndex (oddIndex i) = i := by
  apply Fin.ext
  simp only [halfIndex, oddIndex]
  omega

@[simp] lemma alternatingTuple_even {V : Type*} (x y : Fin 28 → V)
    (i : Fin 28) : alternatingTuple x y (evenIndex i) = x i := by
  rw [alternatingTuple, if_pos (by simp [evenIndex]), halfIndex_evenIndex]

@[simp] lemma alternatingTuple_odd {V : Type*} (x y : Fin 28 → V)
    (i : Fin 28) : alternatingTuple x y (oddIndex i) = y i := by
  rw [alternatingTuple, if_neg (by simp [oddIndex]), halfIndex_oddIndex]

lemma evenIndex_halfIndex_of_even (p : Fin 56) (hp : p.val % 2 = 0) :
    evenIndex (halfIndex p) = p := by
  apply Fin.ext
  simp only [evenIndex, halfIndex]
  omega

lemma oddIndex_halfIndex_of_odd (p : Fin 56) (hp : p.val % 2 ≠ 0) :
    oddIndex (halfIndex p) = p := by
  apply Fin.ext
  simp only [oddIndex, halfIndex]
  have hp' : p.val % 2 = 1 := by omega
  omega

lemma evenIndex_add_one (i : Fin 28) : evenIndex i + 1 = oddIndex i := by
  apply Fin.ext
  rw [Fin.val_add_eq_of_add_lt]
  · simp [evenIndex, oddIndex]
  · simp [evenIndex]
    omega

lemma oddIndex_add_one (i : Fin 28) : oddIndex i + 1 = evenIndex (i + 1) := by
  apply Fin.ext
  simp only [oddIndex, evenIndex]
  change (2 * i.val + 1 + 1) % 56 = 2 * ((i.val + 1) % 28)
  omega

lemma alternatingTuple_injective {V : Type*} {x y : Fin 28 → V}
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hdisj : ∀ i j, x i ≠ y j) :
    Function.Injective (alternatingTuple x y) := by
  intro p q hpq
  by_cases hp : p.val % 2 = 0
  · by_cases hq : q.val % 2 = 0
    · have hix : x (halfIndex p) = x (halfIndex q) := by
        simpa [alternatingTuple, hp, hq] using hpq
      rw [← evenIndex_halfIndex_of_even p hp,
        ← evenIndex_halfIndex_of_even q hq, hx hix]
    · exact False.elim (hdisj (halfIndex p) (halfIndex q) (by
        simpa [alternatingTuple, hp, hq] using hpq))
  · by_cases hq : q.val % 2 = 0
    · exact False.elim (hdisj (halfIndex q) (halfIndex p) (by
        simpa [alternatingTuple, hp, hq] using hpq.symm))
    · have hiy : y (halfIndex p) = y (halfIndex q) := by
        simpa [alternatingTuple, hp, hq] using hpq
      rw [← oddIndex_halfIndex_of_odd p hp,
        ← oddIndex_halfIndex_of_odd q hq, hy hiy]

lemma alternatingTuple_hom {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x y : Fin 28 → V)
    (hxy : ∀ i, G.Adj (x i) (y i))
    (hyx : ∀ i, G.Adj (y i) (x (i + 1))) :
    IsHomCycle G (alternatingTuple x y) := by
  intro p
  by_cases hp : p.val % 2 = 0
  · rw [← evenIndex_halfIndex_of_even p hp, evenIndex_add_one]
    simpa using hxy (halfIndex p)
  · rw [← oddIndex_halfIndex_of_odd p hp, oddIndex_add_one]
    simpa using hyx (halfIndex p)

lemma alternatingTuple_genuine {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x y : Fin 28 → V)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hdisj : ∀ i j, x i ≠ y j)
    (hxy : ∀ i, G.Adj (x i) (y i))
    (hyx : ∀ i, G.Adj (y i) (x (i + 1))) :
    IsGenuineCycle G (alternatingTuple x y) :=
  ⟨alternatingTuple_injective hx hy hdisj,
    alternatingTuple_hom G x y hxy hyx⟩

lemma alternatingTuple_pair_injective {V : Type*} :
    Function.Injective (fun p : (Fin 28 → V) × (Fin 28 → V) ↦
      alternatingTuple p.1 p.2) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  apply Prod.ext
  · funext i
    have hi := congrFun h (evenIndex i)
    simpa using hi
  · funext i
    have hi := congrFun h (oddIndex i)
    simpa using hi

end Erdos113Alternating56

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/LiftCounting.lean` -/

section
open scoped BigOperators

namespace Erdos113LiftCounting

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Index := Fin 28

def allChoices (S : Index → Finset V) : Finset (Index → V) :=
  Fintype.piFinset S

@[simp] lemma mem_allChoices {S : Index → Finset V} {y : Index → V} :
    y ∈ allChoices S ↔ ∀ i, y i ∈ S i := by
  simp [allChoices]

def duplicateEvent (S : Index → Finset V) (p q : Index) :
    Finset (Index → V) :=
  (allChoices S).filter fun y ↦ y p = y q

def forbiddenEvent (S : Index → Finset V) (X : Finset V) (p : Index) :
    Finset (Index → V) :=
  (allChoices S).filter fun y ↦ y p ∈ X

def indexPairs : Finset (Index × Index) :=
  Finset.univ.filter fun pq ↦ pq.1 ≠ pq.2

def duplicateBad (S : Index → Finset V) : Finset (Index → V) :=
  indexPairs.biUnion fun pq ↦ duplicateEvent S pq.1 pq.2

def forbiddenBad (S : Index → Finset V) (X : Finset V) :
    Finset (Index → V) :=
  Finset.univ.biUnion fun p ↦ forbiddenEvent S X p

def validChoices (S : Index → Finset V) (X : Finset V) :
    Finset (Index → V) :=
  allChoices S \ (duplicateBad S ∪ forbiddenBad S X)

@[simp] lemma mem_duplicateEvent {S : Index → Finset V} {p q : Index}
    {y : Index → V} :
    y ∈ duplicateEvent S p q ↔ (∀ i, y i ∈ S i) ∧ y p = y q := by
  simp [duplicateEvent]

@[simp] lemma mem_forbiddenEvent {S : Index → Finset V} {X : Finset V}
    {p : Index} {y : Index → V} :
    y ∈ forbiddenEvent S X p ↔ (∀ i, y i ∈ S i) ∧ y p ∈ X := by
  simp [forbiddenEvent]

@[simp] lemma mem_indexPairs {p q : Index} : (p, q) ∈ indexPairs ↔ p ≠ q := by
  simp [indexPairs]

lemma card_indexPairs_le : indexPairs.card ≤ 28 ^ 2 := by
  calc
    indexPairs.card ≤ (Finset.univ : Finset (Index × Index)).card :=
      Finset.card_filter_le _ _
    _ = 28 ^ 2 := by simp [pow_two]

private def restrictAway (p : Index) (y : Index → V) : Fin 27 → V :=
  fun i ↦ y (p.succAbove i)

lemma duplicateEvent_card_le (S : Index → Finset V) (s : ℕ)
    (hupper : ∀ i, (S i).card ≤ 2 * s) (p q : Index) (hpq : p ≠ q) :
    (duplicateEvent S p q).card ≤ (2 * s) ^ 27 := by
  let T : Finset (Fin 27 → V) :=
    Fintype.piFinset fun i ↦ S (p.succAbove i)
  calc
    (duplicateEvent S p q).card ≤ T.card := by
      apply Finset.card_le_card_of_injOn (restrictAway p)
      · intro y hy
        have hyall := (mem_duplicateEvent.mp hy).1
        change restrictAway p y ∈ T
        simp only [T, Fintype.mem_piFinset]
        intro i
        exact hyall (p.succAbove i)
      · intro y hy z hz hyz
        have hyeq := (mem_duplicateEvent.mp hy).2
        have hzeq := (mem_duplicateEvent.mp hz).2
        funext i
        by_cases hip : i = p
        · subst i
          have hqp : q ≠ p := hpq.symm
          obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hqp
          have hcoord := congrFun hyz k
          change y (p.succAbove k) = z (p.succAbove k) at hcoord
          rw [hk] at hcoord
          exact hyeq.trans (hcoord.trans hzeq.symm)
        · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hip
          have hcoord := congrFun hyz k
          change y (p.succAbove k) = z (p.succAbove k) at hcoord
          simpa [hk] using hcoord
    _ ≤ (2 * s) ^ 27 := by
      rw [show T.card = ∏ i : Fin 27, (S (p.succAbove i)).card by
        exact Fintype.card_piFinset _]
      calc
        ∏ i : Fin 27, (S (p.succAbove i)).card ≤
            ∏ _i : Fin 27, (2 * s) := by
          exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) fun i _ ↦ hupper _
        _ = (2 * s) ^ 27 := by simp

lemma forbiddenEvent_card_le (S : Index → Finset V) (X : Finset V) (s : ℕ)
    (hupper : ∀ i, (S i).card ≤ 2 * s) (p : Index) :
    (forbiddenEvent S X p).card ≤ X.card * (2 * s) ^ 27 := by
  let T : Finset (Fin 27 → V) :=
    Fintype.piFinset fun i ↦ S (p.succAbove i)
  let U : Finset (V × (Fin 27 → V)) := X ×ˢ T
  let f : (Index → V) → V × (Fin 27 → V) := fun y ↦ (y p, restrictAway p y)
  calc
    (forbiddenEvent S X p).card ≤ U.card := by
      apply Finset.card_le_card_of_injOn f
      · intro y hy
        have hydata := mem_forbiddenEvent.mp hy
        change f y ∈ U
        rw [Finset.mem_product]
        refine ⟨hydata.2, ?_⟩
        simp only [T, Fintype.mem_piFinset]
        intro i
        exact hydata.1 (p.succAbove i)
      · intro y _hy z _hz hyz
        funext i
        by_cases hip : i = p
        · subst i
          exact congrArg Prod.fst hyz
        · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hip
          have hcoord := congrFun (congrArg Prod.snd hyz) k
          change y (p.succAbove k) = z (p.succAbove k) at hcoord
          simpa [hk] using hcoord
    _ ≤ X.card * (2 * s) ^ 27 := by
      rw [show U.card = X.card * T.card by simp [U]]
      gcongr
      rw [show T.card = ∏ i : Fin 27, (S (p.succAbove i)).card by
        exact Fintype.card_piFinset _]
      calc
        ∏ i : Fin 27, (S (p.succAbove i)).card ≤
            ∏ _i : Fin 27, (2 * s) := by
          exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) fun i _ ↦ hupper _
        _ = (2 * s) ^ 27 := by simp

lemma duplicateBad_card_le (S : Index → Finset V) (s : ℕ)
    (hupper : ∀ i, (S i).card ≤ 2 * s) :
    (duplicateBad S).card ≤ 28 ^ 2 * (2 * s) ^ 27 := by
  calc
    (duplicateBad S).card ≤
        ∑ pq ∈ indexPairs, (duplicateEvent S pq.1 pq.2).card := by
      exact Finset.card_biUnion_le
    _ ≤ indexPairs.card * (2 * s) ^ 27 := by
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul indexPairs
        (fun pq ↦ (duplicateEvent S pq.1 pq.2).card) ((2 * s) ^ 27)
        (fun pq hpq ↦ duplicateEvent_card_le S s hupper pq.1 pq.2
          (mem_indexPairs.mp hpq))
    _ ≤ 28 ^ 2 * (2 * s) ^ 27 := by
      gcongr
      exact card_indexPairs_le

lemma forbiddenBad_card_le (S : Index → Finset V) (X : Finset V) (s : ℕ)
    (hupper : ∀ i, (S i).card ≤ 2 * s) (hX : X.card ≤ 28) :
    (forbiddenBad S X).card ≤ 28 ^ 2 * (2 * s) ^ 27 := by
  calc
    (forbiddenBad S X).card ≤
        ∑ p : Index, (forbiddenEvent S X p).card := by
      simpa [forbiddenBad] using
        (Finset.card_biUnion_le (s := (Finset.univ : Finset Index))
          (t := fun p ↦ forbiddenEvent S X p))
    _ ≤ ∑ _p : Index, (28 * (2 * s) ^ 27) := by
      gcongr with p
      exact (forbiddenEvent_card_le S X s hupper p).trans (by gcongr)
    _ = 28 ^ 2 * (2 * s) ^ 27 := by simp [pow_two]; ring

lemma bad_card_le (S : Index → Finset V) (X : Finset V) (s : ℕ)
    (hupper : ∀ i, (S i).card ≤ 2 * s) (hX : X.card ≤ 28) :
    (duplicateBad S ∪ forbiddenBad S X).card ≤
      1568 * (2 * s) ^ 27 := by
  calc
    (duplicateBad S ∪ forbiddenBad S X).card ≤
        (duplicateBad S).card + (forbiddenBad S X).card :=
      Finset.card_union_le _ _
    _ ≤ 28 ^ 2 * (2 * s) ^ 27 + 28 ^ 2 * (2 * s) ^ 27 :=
      Nat.add_le_add (duplicateBad_card_le S s hupper)
        (forbiddenBad_card_le S X s hupper hX)
    _ = 1568 * (2 * s) ^ 27 := by ring

lemma allChoices_card_lower (S : Index → Finset V) (s : ℕ)
    (hlower : ∀ i, s ≤ (S i).card) :
    s ^ 28 ≤ (allChoices S).card := by
  rw [show (allChoices S).card = ∏ i : Index, (S i).card by
    exact Fintype.card_piFinset _]
  calc
    s ^ 28 = ∏ _i : Index, s := by simp
    _ ≤ ∏ i : Index, (S i).card := by
      exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) fun i _ ↦ hlower i

lemma validChoices_half_lower (S : Index → Finset V) (X : Finset V) (s : ℕ)
    (hlower : ∀ i, s ≤ (S i).card)
    (hupper : ∀ i, (S i).card ≤ 2 * s)
    (hX : X.card ≤ 28)
    (hs : 3136 * 2 ^ 27 ≤ s) :
    s ^ 28 ≤ 2 * (validChoices S X).card := by
  let B := duplicateBad S ∪ forbiddenBad S X
  have hall := allChoices_card_lower S s hlower
  have hsplit : (allChoices S).card ≤ (validChoices S X).card + B.card := by
    simpa [validChoices, B, add_comm] using
      (Finset.card_le_card_sdiff_add_card (s := allChoices S) (t := B))
  have hbad : B.card ≤ 1568 * (2 * s) ^ 27 := by
    exact bad_card_le S X s hupper hX
  have hnum : 2 * (1568 * (2 * s) ^ 27) ≤ s ^ 28 := by
    calc
      2 * (1568 * (2 * s) ^ 27) = (3136 * 2 ^ 27) * s ^ 27 := by ring
      _ ≤ s * s ^ 27 := Nat.mul_le_mul_right (s ^ 27) hs
      _ = s ^ 28 := by ring
  omega

lemma mem_validChoices {S : Index → Finset V} {X : Finset V}
    {y : Index → V} :
    y ∈ validChoices S X ↔
      (∀ i, y i ∈ S i) ∧ Function.Injective y ∧ ∀ i, y i ∉ X := by
  constructor
  · intro hy
    have hydata := Finset.mem_sdiff.mp hy
    have hall := mem_allChoices.mp hydata.1
    refine ⟨hall, ?_, ?_⟩
    · intro p q hpq
      by_contra hpne
      apply hydata.2
      rw [Finset.mem_union]
      left
      rw [duplicateBad, Finset.mem_biUnion]
      exact ⟨(p, q), mem_indexPairs.mpr hpne, mem_duplicateEvent.mpr ⟨hall, hpq⟩⟩
    · intro p hpX
      apply hydata.2
      rw [Finset.mem_union]
      right
      rw [forbiddenBad, Finset.mem_biUnion]
      exact ⟨p, Finset.mem_univ _, mem_forbiddenEvent.mpr ⟨hall, hpX⟩⟩
  · rintro ⟨hall, hinj, hX⟩
    rw [validChoices, Finset.mem_sdiff]
    refine ⟨mem_allChoices.mpr hall, ?_⟩
    rw [Finset.mem_union]
    push_neg
    constructor
    · intro hdup
      rw [duplicateBad, Finset.mem_biUnion] at hdup
      obtain ⟨pq, hpq, hy⟩ := hdup
      exact (mem_indexPairs.mp hpq) (hinj (mem_duplicateEvent.mp hy).2)
    · intro hforbid
      rw [forbiddenBad, Finset.mem_biUnion] at hforbid
      obtain ⟨p, _hp, hy⟩ := hforbid
      exact hX p (mem_forbiddenEvent.mp hy).2

end

end Erdos113LiftCounting

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/ManyLifts.lean` -/

section
open scoped SimpleGraph

namespace Erdos113ManyLifts

noncomputable section

open Erdos113Cycles Erdos113Alternating56 Erdos113LiftCounting

variable {T V : Type*} [Fintype T] [DecidableEq T]
  [Fintype V] [DecidableEq V]

/-- The finite data needed to lift an auxiliary edge `a--b` through a
middle host vertex.  This is the abstract core of Janzer's many-four-cycle
construction. -/
structure LiftSystem (F : SimpleGraph T) (G : SimpleGraph V) where
  embed : T → V
  embed_injective : Function.Injective embed
  middle : T → T → Finset V
  lower : ℕ
  lower_pos : 0 < lower
  lower_card : ∀ {a b}, F.Adj a b → lower ≤ (middle a b).card
  upper_card : ∀ {a b}, F.Adj a b → (middle a b).card ≤ 2 * lower
  adj_left : ∀ {a b y}, y ∈ middle a b → G.Adj (embed a) y
  adj_right : ∀ {a b y}, y ∈ middle a b → G.Adj y (embed b)
  middle_disjoint : ∀ {a b y}, y ∈ middle a b → ∀ t, y ≠ embed t

def cycleMiddleSets {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (x : Fin 28 → T) : Fin 28 → Finset V :=
  fun i ↦ L.middle (x i) (x (i + 1))

def cycleEmbeddedVertices {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (x : Fin 28 → T) : Finset V :=
  Finset.univ.image fun i ↦ L.embed (x i)

def liftsOfCycle {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (x : Fin 28 → T) : Finset (Fin 28 → V) :=
  validChoices (cycleMiddleSets L x) (cycleEmbeddedVertices L x)

def liftPairs (F : SimpleGraph T) (G : SimpleGraph V) (L : LiftSystem F G) :
    Finset ((x : Fin 28 → T) × (Fin 28 → V)) :=
  (genuineCycles F 28).sigma fun x ↦ liftsOfCycle L x

def liftedTuple {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (p : (x : Fin 28 → T) × (Fin 28 → V)) : Fin 56 → V :=
  alternatingTuple (L.embed ∘ p.1) p.2

def liftedCycles (F : SimpleGraph T) (G : SimpleGraph V) (L : LiftSystem F G) :
    Finset (Fin 56 → V) :=
  (liftPairs F G L).image (liftedTuple L)

@[simp] lemma mem_cycleEmbeddedVertices {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (x : Fin 28 → T) (v : V) :
    v ∈ cycleEmbeddedVertices L x ↔ ∃ i, L.embed (x i) = v := by
  simp [cycleEmbeddedVertices]

lemma cycleEmbeddedVertices_card_le {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (x : Fin 28 → T) :
    (cycleEmbeddedVertices L x).card ≤ 28 := by
  calc
    (cycleEmbeddedVertices L x).card ≤ (Finset.univ : Finset (Fin 28)).card := by
      exact Finset.card_image_le
    _ = 28 := by simp

@[simp] lemma mem_liftPairs {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {p : (x : Fin 28 → T) × (Fin 28 → V)} :
    p ∈ liftPairs F G L ↔
      IsGenuineCycle F p.1 ∧ p.2 ∈ liftsOfCycle L p.1 := by
  simp [liftPairs]

lemma liftedTuple_injective {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) : Function.Injective (liftedTuple L) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ hpq
  have hpair : (L.embed ∘ x, y) = (L.embed ∘ x', y') :=
    alternatingTuple_pair_injective hpq
  have hx : x = x' := by
    funext i
    exact L.embed_injective (congrFun (congrArg Prod.fst hpair) i)
  subst x'
  have hy : y = y' := congrArg Prod.snd hpair
  subst y'
  rfl

lemma card_liftedCycles {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) :
    (liftedCycles F G L).card = (liftPairs F G L).card := by
  exact Finset.card_image_of_injective _ (liftedTuple_injective L)

lemma liftsOfCycle_half_lower {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (hlarge : 3136 * 2 ^ 27 ≤ L.lower)
    {x : Fin 28 → T} (hx : IsGenuineCycle F x) :
    L.lower ^ 28 ≤ 2 * (liftsOfCycle L x).card := by
  apply validChoices_half_lower
  · intro i
    exact L.lower_card (hx.2 i)
  · intro i
    exact L.upper_card (hx.2 i)
  · exact cycleEmbeddedVertices_card_le L x
  · exact hlarge

theorem liftedCycles_card_lower {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (hlarge : 3136 * 2 ^ 27 ≤ L.lower) :
    (genuineCycles F 28).card * L.lower ^ 28 ≤
      2 * (liftedCycles F G L).card := by
  rw [card_liftedCycles, liftPairs, Finset.card_sigma]
  have hsum : ∑ x ∈ genuineCycles F 28, L.lower ^ 28 ≤
      ∑ x ∈ genuineCycles F 28, 2 * (liftsOfCycle L x).card := by
    exact Finset.sum_le_sum fun x hx ↦
      liftsOfCycle_half_lower L hlarge (mem_genuineCycles.mp hx)
  simpa [Finset.mul_sum, Finset.sum_mul] using hsum

lemma liftedTuple_genuine {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {p : (x : Fin 28 → T) × (Fin 28 → V)}
    (hp : p ∈ liftPairs F G L) :
    IsGenuineCycle G (liftedTuple L p) := by
  have hx := (mem_liftPairs L).mp hp
  have hy := mem_validChoices.mp hx.2
  apply alternatingTuple_genuine
  · exact L.embed_injective.comp hx.1.1
  · exact hy.2.1
  · intro i j heq
    exact hy.2.2 j ((mem_cycleEmbeddedVertices L p.1 (p.2 j)).mpr ⟨i, heq⟩)
  · intro i
    exact L.adj_left (hy.1 i)
  · intro i
    exact L.adj_right (hy.1 i)

theorem liftedCycles_genuine {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {z : Fin 56 → V}
    (hz : z ∈ liftedCycles F G L) : IsGenuineCycle G z := by
  rw [liftedCycles, Finset.mem_image] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  exact liftedTuple_genuine L hp

abbrev OffSingle56 (i : Fin 56) := {j : Fin 56 // j ≠ i}

def restrictOffSingle56 (i : Fin 56) (z : Fin 56 → V) :
    OffSingle56 i → V := fun j ↦ z j

def singleFiber56 (C : Finset (Fin 56 → V)) (i : Fin 56)
    (r : OffSingle56 i → V) : Finset (Fin 56 → V) :=
  C.filter fun z ↦ restrictOffSingle56 i z = r

lemma eval_injective_on_singleFiber56 (C : Finset (Fin 56 → V))
    (i : Fin 56) (r : OffSingle56 i → V) :
    Set.InjOn (fun z : Fin 56 → V ↦ z i) (singleFiber56 C i r) := by
  intro z hz w hw hzi
  have hzrest := (Finset.mem_filter.mp hz).2
  have hwrest := (Finset.mem_filter.mp hw).2
  funext j
  by_cases hji : j = i
  · simpa [hji] using hzi
  · have h := congrFun (hzrest.trans hwrest.symm) ⟨j, hji⟩
    exact h

lemma value_eq_of_mem_singleFiber56 {C : Finset (Fin 56 → V)}
    {i : Fin 56} {r : OffSingle56 i → V} {z w : Fin 56 → V}
    (hz : z ∈ singleFiber56 C i r) (hw : w ∈ singleFiber56 C i r)
    {j : Fin 56} (hji : j ≠ i) : z j = w j := by
  have hzrest := (Finset.mem_filter.mp hz).2
  have hwrest := (Finset.mem_filter.mp hw).2
  exact congrFun (hzrest.trans hwrest.symm) ⟨j, hji⟩

lemma fin56_sub_one_ne (i : Fin 56) : i - 1 ≠ i := by
  decide +revert

lemma fin56_add_one_ne (i : Fin 56) : i + 1 ≠ i := by
  decide +revert

lemma fin56_sub_one_add_one (i : Fin 56) : i - 1 + 1 = i := by
  decide +revert

lemma evenIndex_ne_oddIndex (i j : Fin 28) : evenIndex i ≠ oddIndex j := by
  intro h
  have := congrArg Fin.val h
  simp [evenIndex, oddIndex] at this
  omega

/-- A missing even coordinate is controlled by the host vertices in the
embedded auxiliary part that join its two fixed neighboring middle
vertices. -/
def bridgeAnchors {F : SimpleGraph T} {G : SimpleGraph V}
    [DecidableRel G.Adj] (L : LiftSystem F G) (u w : V) : Finset T :=
  Finset.univ.filter fun t ↦ G.Adj u (L.embed t) ∧ G.Adj (L.embed t) w

def IsMiddleVertex {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (y : V) : Prop :=
  ∃ a b, y ∈ L.middle a b

@[simp] lemma mem_bridgeAnchors {F : SimpleGraph T} {G : SimpleGraph V}
    [DecidableRel G.Adj] (L : LiftSystem F G) {u w : V} {t : T} :
    t ∈ bridgeAnchors L u w ↔
      G.Adj u (L.embed t) ∧ G.Adj (L.embed t) w := by
  simp [bridgeAnchors]

lemma oddIndex_halfIndex_sub_one_of_even (i : Fin 56)
    (hi : i.val % 2 = 0) :
    oddIndex (halfIndex i - 1) = i - 1 := by
  revert i
  decide +revert

theorem singleFiber56_liftedCycles_card_le
    {F : SimpleGraph T} {G : SimpleGraph V} [DecidableRel G.Adj]
    (L : LiftSystem F G)
    (cap : ℕ) (hmiddle : 2 * L.lower ≤ cap)
    (hbridge : ∀ u w, IsMiddleVertex L u →
      (bridgeAnchors L u w).card ≤ cap)
    (i : Fin 56) (r : OffSingle56 i → V) :
    (singleFiber56 (liftedCycles F G L) i r).card ≤ cap := by
  let C := liftedCycles F G L
  let K := singleFiber56 C i r
  by_cases hK : K.Nonempty
  · obtain ⟨z₀, hz₀K⟩ := hK
    have hz₀C : z₀ ∈ C := (Finset.mem_filter.mp hz₀K).1
    change z₀ ∈ liftedCycles F G L at hz₀C
    rw [liftedCycles, Finset.mem_image] at hz₀C
    obtain ⟨p₀, hp₀, hp₀eq⟩ := hz₀C
    by_cases hi : i.val % 2 = 0
    · let B := bridgeAnchors L (z₀ (i - 1)) (z₀ (i + 1))
      let E : Finset V := B.image L.embed
      have hzprevMiddle : IsMiddleVertex L (z₀ (i - 1)) := by
        have hp₀data := (mem_liftPairs L).mp hp₀
        have hp₀choices := (mem_validChoices.mp hp₀data.2).1
        let j := halfIndex i
        let k : Fin 28 := j - 1
        have hrepr : oddIndex k = i - 1 := by
          simpa [k, j] using oddIndex_halfIndex_sub_one_of_even i hi
        have hval : z₀ (i - 1) = p₀.2 k := by
          rw [← hp₀eq, ← hrepr]
          simp [liftedTuple]
        refine ⟨p₀.1 k, p₀.1 (k + 1), ?_⟩
        rw [hval]
        simpa [cycleMiddleSets] using hp₀choices k
      calc
        K.card ≤ E.card := by
          apply Finset.card_le_card_of_injOn (fun z : Fin 56 → V ↦ z i)
          · intro z hzK
            have hzC : z ∈ C := (Finset.mem_filter.mp hzK).1
            change z ∈ liftedCycles F G L at hzC
            rw [liftedCycles, Finset.mem_image] at hzC
            obtain ⟨p, hp, rfl⟩ := hzC
            have hpgen := liftedTuple_genuine L hp
            have hprev : liftedTuple L p (i - 1) = z₀ (i - 1) :=
              value_eq_of_mem_singleFiber56 hzK hz₀K (fin56_sub_one_ne i)
            have hnext : liftedTuple L p (i + 1) = z₀ (i + 1) :=
              value_eq_of_mem_singleFiber56 hzK hz₀K (fin56_add_one_ne i)
            change liftedTuple L p i ∈ E
            simp only [E, Finset.mem_image]
            refine ⟨p.1 (halfIndex i), ?_, ?_⟩
            · rw [mem_bridgeAnchors]
              constructor
              · rw [← hprev]
                have h := hpgen.2 (i - 1)
                rw [fin56_sub_one_add_one] at h
                simpa [liftedTuple, alternatingTuple, hi] using h
              · rw [← hnext]
                have h := hpgen.2 i
                simpa [liftedTuple, alternatingTuple, hi] using h
            · simp [liftedTuple, alternatingTuple, hi]
          · exact eval_injective_on_singleFiber56 C i r
        _ ≤ B.card := Finset.card_image_le
        _ ≤ cap := hbridge _ _ hzprevMiddle
    · let j := halfIndex i
      let B := L.middle (p₀.1 j) (p₀.1 (j + 1))
      calc
        K.card ≤ B.card := by
          apply Finset.card_le_card_of_injOn (fun z : Fin 56 → V ↦ z i)
          · intro z hzK
            have hzC : z ∈ C := (Finset.mem_filter.mp hzK).1
            change z ∈ liftedCycles F G L at hzC
            rw [liftedCycles, Finset.mem_image] at hzC
            obtain ⟨p, hp, hpeq⟩ := hzC
            have hpdata := (mem_liftPairs L).mp hp
            have hpchoices := (mem_validChoices.mp hpdata.2).1
            have hrepr : oddIndex j = i := oddIndex_halfIndex_of_odd i hi
            have hleft : p.1 j = p₀.1 j := by
              apply L.embed_injective
              have hne : evenIndex j ≠ i := by
                rw [← hrepr]
                exact evenIndex_ne_oddIndex j j
              have hcoord := value_eq_of_mem_singleFiber56 hzK hz₀K
                hne
              rw [← hpeq, ← hp₀eq] at hcoord
              simpa [liftedTuple] using hcoord
            have hright : p.1 (j + 1) = p₀.1 (j + 1) := by
              apply L.embed_injective
              have hne : evenIndex (j + 1) ≠ i := by
                rw [← hrepr]
                exact evenIndex_ne_oddIndex (j + 1) j
              have hcoord := value_eq_of_mem_singleFiber56 hzK hz₀K
                hne
              rw [← hpeq, ← hp₀eq] at hcoord
              simpa [liftedTuple] using hcoord
            change z i ∈ B
            rw [← hpeq, ← hrepr]
            simpa [B, cycleMiddleSets, liftedTuple, hleft, hright] using hpchoices j
          · exact eval_injective_on_singleFiber56 C i r
        _ ≤ cap := by
          have hp₀gen := (mem_liftPairs L).mp hp₀
          exact (L.upper_card (hp₀gen.1.2 j)).trans hmiddle
  · simp only [Finset.not_nonempty_iff_eq_empty] at hK
    change K.card ≤ cap
    rw [hK]
    simp

end

end Erdos113ManyLifts

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/Incidence.lean` -/

section
open scoped SimpleGraph

namespace Erdos113Incidence

noncomputable section

open Erdos113Cycles Erdos113Alternating56 Erdos113LiftCounting
  Erdos113ManyLifts

variable {T V : Type*} [Fintype T] [DecidableEq T]
  [Fintype V] [DecidableEq V]

def Linked {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (t : T) (y : V) : Prop :=
  (∃ b, y ∈ L.middle t b) ∨ ∃ a, y ∈ L.middle a t

noncomputable def leftPartners {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (t : T) : Finset V :=
  by classical exact Finset.univ.filter (Linked L t)

noncomputable def rightPartners {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (y : V) : Finset T :=
  by classical exact Finset.univ.filter fun t ↦ Linked L t y

@[simp] lemma mem_leftPartners {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {t : T} {y : V} :
    y ∈ leftPartners L t ↔ Linked L t y := by
  simp [leftPartners]

@[simp] lemma mem_rightPartners {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {t : T} {y : V} :
    t ∈ rightPartners L y ↔ Linked L t y := by
  simp [rightPartners]

lemma linked_ne_embed {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {t : T} {y : V} (h : Linked L t y) (u : T) :
    y ≠ L.embed u := by
  rcases h with ⟨b, hy⟩ | ⟨a, hy⟩
  · exact L.middle_disjoint hy u
  · exact L.middle_disjoint hy u

def incidenceRel {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (u y : V) : Prop :=
  ∃ t, L.embed t = u ∧ Linked L t y

def incidenceGraph {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) : SimpleGraph V :=
  SimpleGraph.fromRel (incidenceRel L)

noncomputable instance incidenceGraph_decidableRel
    {F : SimpleGraph T} {G : SimpleGraph V} (L : LiftSystem F G) :
    DecidableRel (incidenceGraph L).Adj := Classical.decRel _

@[simp] lemma incidenceGraph_adj_iff {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {u y : V} :
    (incidenceGraph L).Adj u y ↔
      u ≠ y ∧ (incidenceRel L u y ∨ incidenceRel L y u) := by
  exact SimpleGraph.fromRel_adj _ _ _

lemma incidenceGraph_adj_embed_of_linked
    {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {t : T} {y : V} (h : Linked L t y) :
    (incidenceGraph L).Adj (L.embed t) y := by
  rw [incidenceGraph_adj_iff]
  exact ⟨(linked_ne_embed L h t).symm, Or.inl ⟨t, rfl, h⟩⟩

lemma liftedTuple_hom_incidence {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {p : (x : Fin 28 → T) × (Fin 28 → V)}
    (hp : p ∈ liftPairs F G L) :
    IsHomCycle (incidenceGraph L) (liftedTuple L p) := by
  have hpdata := (mem_liftPairs L).mp hp
  have hchoices := (mem_validChoices.mp hpdata.2).1
  apply alternatingTuple_hom
  · intro i
    apply incidenceGraph_adj_embed_of_linked
    exact Or.inl ⟨p.1 (i + 1), hchoices i⟩
  · intro i
    exact (incidenceGraph_adj_embed_of_linked L
      (Or.inr ⟨p.1 i, hchoices i⟩)).symm

theorem liftedCycles_genuine_incidence {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {z : Fin 56 → V}
    (hz : z ∈ liftedCycles F G L) :
    IsGenuineCycle (incidenceGraph L) z := by
  rw [liftedCycles, Finset.mem_image] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  exact ⟨(liftedTuple_genuine L hp).1, liftedTuple_hom_incidence L hp⟩

noncomputable def embeddedVertices {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) : Finset V :=
  Finset.univ.image L.embed

def incidenceSide {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (v : V) : Bool :=
  decide (v ∈ embeddedVertices L)

@[simp] lemma incidenceSide_eq_true {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {v : V} :
    incidenceSide L v = true ↔ v ∈ embeddedVertices L := by
  simp [incidenceSide]

@[simp] lemma incidenceSide_embed {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (t : T) : incidenceSide L (L.embed t) = true := by
  simp [incidenceSide, embeddedVertices]

lemma incidenceSide_linked {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {t : T} {y : V} (h : Linked L t y) :
    incidenceSide L y = false := by
  rw [Bool.eq_false_iff]
  intro hy
  rw [incidenceSide_eq_true] at hy
  obtain ⟨u, _hu, hueq⟩ := Finset.mem_image.mp hy
  exact linked_ne_embed L h u hueq.symm

lemma incidenceGraph_cross {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {u y : V} (h : (incidenceGraph L).Adj u y) :
    incidenceSide L y = !(incidenceSide L u) := by
  rcases (incidenceGraph_adj_iff L).mp h with ⟨_, hrel | hrel⟩
  · obtain ⟨t, rfl, hty⟩ := hrel
    simp [incidenceSide_linked L hty]
  · obtain ⟨t, rfl, htu⟩ := hrel
    simp [incidenceSide_linked L htu]

lemma incidenceGraph_degree_embed_le {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (t : T) :
    (incidenceGraph L).degree (L.embed t) ≤ (leftPartners L t).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro y hy
  rw [mem_leftPartners]
  have hadj := ((incidenceGraph L).mem_neighborFinset (L.embed t) y).mp hy
  rcases (incidenceGraph_adj_iff L).mp hadj with ⟨_, hrel | hrel⟩
  · obtain ⟨u, hu, huy⟩ := hrel
    have hut : u = t := L.embed_injective hu
    simpa [hut] using huy
  · obtain ⟨u, _huy, huembed⟩ := hrel
    exact False.elim ((linked_ne_embed L huembed t) rfl)

lemma incidenceGraph_degree_nonembedded_le {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {y : V} (hy : y ∉ embeddedVertices L) :
    (incidenceGraph L).degree y ≤ (rightPartners L y).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc
    ((incidenceGraph L).neighborFinset y).card ≤
        ((rightPartners L y).image L.embed).card := by
      apply Finset.card_le_card
      intro z hz
      have hadj := ((incidenceGraph L).mem_neighborFinset y z).mp hz
      rcases (incidenceGraph_adj_iff L).mp hadj with ⟨_, hrel | hrel⟩
      · obtain ⟨t, hty, _htz⟩ := hrel
        exact False.elim (hy (by simp [embeddedVertices, ← hty]))
      · obtain ⟨t, htz, hty⟩ := hrel
        rw [Finset.mem_image]
        exact ⟨t, by simpa using hty, htz⟩
    _ ≤ (rightPartners L y).card := Finset.card_image_le

theorem incidenceGraph_degree_le
    {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (A B : ℕ)
    (hleft : ∀ t, (leftPartners L t).card ≤ A)
    (hright : ∀ y, (rightPartners L y).card ≤ B) (v : V) :
    (incidenceGraph L).degree v ≤ if incidenceSide L v then A else B := by
  by_cases hv : v ∈ embeddedVertices L
  · obtain ⟨t, _ht, htv⟩ := Finset.mem_image.mp hv
    subst v
    simp [incidenceSide_embed,
      (incidenceGraph_degree_embed_le L t).trans (hleft t)]
  · have hs : incidenceSide L v = false := by
      simp [incidenceSide, hv]
    rw [hs]
    exact (incidenceGraph_degree_nonembedded_le L hv).trans (hright v)

theorem incidenceGraph_isBipartiteWith
    {F : SimpleGraph T} {G : SimpleGraph V} (L : LiftSystem F G) :
    (incidenceGraph L).IsBipartiteWith (↑(embeddedVertices L) : Set V)
      (↑((embeddedVertices L)ᶜ) : Set V) := by
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    intro a ha hb
    have hnot : a ∉ embeddedVertices L := by simpa using hb
    exact hnot ha
  intro u y huy
  have hcross := incidenceGraph_cross L huy
  by_cases hu : u ∈ embeddedVertices L
  · left
    refine ⟨hu, ?_⟩
    have hsu : incidenceSide L u = true := by simp [incidenceSide, hu]
    rw [hsu] at hcross
    have hsy : incidenceSide L y = false := by simpa using hcross
    simpa [incidenceSide] using hsy
  · right
    refine ⟨by simpa using hu, ?_⟩
    have hsu : incidenceSide L u = false := by simp [incidenceSide, hu]
    rw [hsu] at hcross
    have hsy : incidenceSide L y = true := by simpa using hcross
    simpa [incidenceSide] using hsy

theorem incidenceGraph_edge_card_le
    {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (A : ℕ)
    (hleft : ∀ t, (leftPartners L t).card ≤ A) :
    (incidenceGraph L).edgeFinset.card ≤ Fintype.card T * A := by
  have hsum := (incidenceGraph L).isBipartiteWith_sum_degrees_eq_card_edges
    (s := embeddedVertices L) (t := (embeddedVertices L)ᶜ)
    (incidenceGraph_isBipartiteWith L)
  calc
    (incidenceGraph L).edgeFinset.card =
        ∑ v ∈ embeddedVertices L, (incidenceGraph L).degree v := by
      simpa using hsum.symm
    _ ≤ ∑ _v ∈ embeddedVertices L, A := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨t, _ht, htv⟩ := Finset.mem_image.mp hv
      subst v
      exact (incidenceGraph_degree_embed_le L t).trans (hleft t)
    _ = (embeddedVertices L).card * A := by simp
    _ ≤ Fintype.card T * A := by
      gcongr
      exact Finset.card_image_le

end

end Erdos113Incidence

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/AnchoredLifts.lean` -/

section
open scoped SimpleGraph

namespace Erdos113AnchoredLifts

noncomputable section

open Erdos113ManyLifts Erdos113Incidence

variable {T V : Type*} [Fintype T] [DecidableEq T]
  [Fintype V] [DecidableEq V]

def anchorNeighbors {F : SimpleGraph T} {G : SimpleGraph V}
    [DecidableRel G.Adj] (L : LiftSystem F G) (v y : V) : Finset T :=
  Finset.univ.filter fun t ↦ G.Adj v (L.embed t) ∧ G.Adj (L.embed t) y

@[simp] lemma mem_anchorNeighbors {F : SimpleGraph T} {G : SimpleGraph V}
    [DecidableRel G.Adj] (L : LiftSystem F G) {v y : V} {t : T} :
    t ∈ anchorNeighbors L v y ↔
      G.Adj v (L.embed t) ∧ G.Adj (L.embed t) y := by
  simp [anchorNeighbors]

/-- A lift system whose embedded vertices all lie in the neighborhood of
one anchor.  The anchor-codegree cap controls both the right incidence
degrees and the even-coordinate single fibers. -/
structure AnchoredLiftSystem (F : SimpleGraph T) (G : SimpleGraph V)
    [DecidableRel G.Adj] extends LiftSystem F G where
  anchor : V
  leftCap : ℕ
  rightCap : ℕ
  anchor_adj : ∀ t, G.Adj anchor (toLiftSystem.embed t)
  anchor_cap : ∀ y, IsMiddleVertex toLiftSystem y →
    (anchorNeighbors toLiftSystem anchor y).card ≤ rightCap
  left_cap : ∀ t, (leftPartners toLiftSystem t).card ≤ leftCap

lemma bridgeAnchors_subset_anchorNeighbors
    {F : SimpleGraph T} {G : SimpleGraph V} [DecidableRel G.Adj]
    (A : AnchoredLiftSystem F G) (u w : V) :
    bridgeAnchors A.toLiftSystem u w ⊆
      anchorNeighbors A.toLiftSystem A.anchor u := by
  intro t ht
  have htdata := (mem_bridgeAnchors A.toLiftSystem).mp ht
  rw [mem_anchorNeighbors]
  exact ⟨A.anchor_adj t, htdata.1.symm⟩

theorem bridgeAnchors_card_le
    {F : SimpleGraph T} {G : SimpleGraph V} [DecidableRel G.Adj]
    (A : AnchoredLiftSystem F G) (u w : V)
    (hu : IsMiddleVertex A.toLiftSystem u) :
    (bridgeAnchors A.toLiftSystem u w).card ≤ A.rightCap :=
  (Finset.card_le_card (bridgeAnchors_subset_anchorNeighbors A u w)).trans
    (A.anchor_cap u hu)

lemma linked_mem_anchorNeighbors
    {F : SimpleGraph T} {G : SimpleGraph V} [DecidableRel G.Adj]
    (A : AnchoredLiftSystem F G) {t : T} {y : V}
    (h : Linked A.toLiftSystem t y) :
    t ∈ anchorNeighbors A.toLiftSystem A.anchor y := by
  rw [mem_anchorNeighbors]
  refine ⟨A.anchor_adj t, ?_⟩
  rcases h with ⟨b, hy⟩ | ⟨a, hy⟩
  · exact A.toLiftSystem.adj_left hy
  · exact (A.toLiftSystem.adj_right hy).symm

lemma isMiddleVertex_of_linked
    {F : SimpleGraph T} {G : SimpleGraph V} [DecidableRel G.Adj]
    (A : AnchoredLiftSystem F G) {t : T} {y : V}
    (h : Linked A.toLiftSystem t y) :
    IsMiddleVertex A.toLiftSystem y := by
  rcases h with ⟨b, hy⟩ | ⟨a, hy⟩
  · exact ⟨t, b, hy⟩
  · exact ⟨a, t, hy⟩

theorem rightPartners_card_le
    {F : SimpleGraph T} {G : SimpleGraph V} [DecidableRel G.Adj]
    (A : AnchoredLiftSystem F G) (y : V) :
    (rightPartners A.toLiftSystem y).card ≤ A.rightCap := by
  by_cases hy : (rightPartners A.toLiftSystem y).Nonempty
  · obtain ⟨t₀, ht₀⟩ := hy
    have hmiddle := isMiddleVertex_of_linked A
      ((mem_rightPartners A.toLiftSystem).mp ht₀)
    calc
      (rightPartners A.toLiftSystem y).card ≤
          (anchorNeighbors A.toLiftSystem A.anchor y).card := by
        apply Finset.card_le_card
        intro t ht
        exact linked_mem_anchorNeighbors A
          ((mem_rightPartners A.toLiftSystem).mp ht)
      _ ≤ A.rightCap := A.anchor_cap y hmiddle
  · simp only [Finset.not_nonempty_iff_eq_empty] at hy
    simp [hy]

end

end Erdos113AnchoredLifts

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/AnchorConstruction.lean` -/

section
open scoped SimpleGraph

namespace Erdos113AnchorConstruction

noncomputable section

open Erdos113ManyLifts Erdos113Incidence Erdos113AnchoredLifts
  Erdos113FourCycles

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev NeighborVertex (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :=
  ↑(G.neighborFinset v)

def neighborEmbed {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} :
    NeighborVertex G v → V := fun x ↦ x.1

lemma neighborEmbed_injective {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} :
    Function.Injective (neighborEmbed (G := G) (v := v)) :=
  Subtype.val_injective

def selectedMiddle (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    (a b : NeighborVertex G v) : Finset V :=
  ((commonNeighborFinset G a.1 b.1).erase v).filter fun y ↦ P a.1 y b.1

@[simp] lemma mem_selectedMiddle
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    {a b : NeighborVertex G v} {y : V} :
    y ∈ selectedMiddle G v P a b ↔
      G.Adj a.1 y ∧ G.Adj b.1 y ∧ y ≠ v ∧ P a.1 y b.1 := by
  simp [selectedMiddle, mem_commonNeighborFinset, and_assoc, and_left_comm]

lemma selectedMiddle_comm
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    (hP : ∀ x y z, P x y z ↔ P z y x)
    (a b : NeighborVertex G v) :
    selectedMiddle G v P a b = selectedMiddle G v P b a := by
  ext y
  simp only [mem_selectedMiddle]
  rw [hP]
  aesop

def selectedPairGraph
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    (lower : ℕ) : SimpleGraph (NeighborVertex G v) :=
  SimpleGraph.fromRel fun a b ↦
    lower ≤ (selectedMiddle G v P a b).card ∧
      (selectedMiddle G v P a b).card ≤ 2 * lower

noncomputable instance selectedPairGraph_decidableRel
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    (lower : ℕ) : DecidableRel (selectedPairGraph G v P lower).Adj :=
  Classical.decRel _

lemma selectedPairGraph_bounds
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    (hP : ∀ x y z, P x y z ↔ P z y x)
    (lower : ℕ) {a b : NeighborVertex G v}
    (hab : (selectedPairGraph G v P lower).Adj a b) :
    lower ≤ (selectedMiddle G v P a b).card ∧
      (selectedMiddle G v P a b).card ≤ 2 * lower := by
  rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨_, h | h⟩
  · exact h
  · simpa [selectedMiddle_comm G v P hP a b] using h

noncomputable def selectedLiftSystem
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool)
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    (hP : ∀ x y z, P x y z ↔ P z y x)
    (lower : ℕ) (hlower : 0 < lower) :
    LiftSystem (selectedPairGraph G v P lower) G where
  embed := neighborEmbed
  embed_injective := neighborEmbed_injective
  middle := selectedMiddle G v P
  lower := lower
  lower_pos := hlower
  lower_card := fun h ↦ (selectedPairGraph_bounds G v P hP lower h).1
  upper_card := fun h ↦ (selectedPairGraph_bounds G v P hP lower h).2
  adj_left := fun h ↦ (mem_selectedMiddle G v P).mp h |>.1
  adj_right := fun h ↦ (mem_selectedMiddle G v P).mp h |>.2.1 |>.symm
  middle_disjoint := by
    intro a b y hy t hyt
    have hydata := (mem_selectedMiddle G v P).mp hy
    have hav : G.Adj v a.1 := (G.mem_neighborFinset v a.1).mp a.2
    have htv : G.Adj v t.1 := (G.mem_neighborFinset v t.1).mp t.2
    have hya := hcross hydata.1
    have hva := hcross hav
    have hvt := hcross htv
    have hside : side y = side v := by
      rw [hya, hva]
      cases side v <;> rfl
    have hsidemap : side y = side t.1 := by
      simpa [neighborEmbed] using congrArg side hyt
    rw [hside, hvt] at hsidemap
    exact (Bool.eq_not_self (side v)).mp hsidemap

theorem anchorNeighbors_card_le_codegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool)
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    (hP : ∀ x y z, P x y z ↔ P z y x)
    (lower : ℕ) (hlower : 0 < lower) (y : V) :
    (anchorNeighbors (selectedLiftSystem G side hcross v P hP lower hlower) v y).card ≤
      codegree G v y := by
  let S := anchorNeighbors
    (selectedLiftSystem G side hcross v P hP lower hlower) v y
  calc
    S.card = (S.image neighborEmbed).card :=
      (Finset.card_image_of_injective S neighborEmbed_injective).symm
    _ ≤ codegree G v y := by
      apply Finset.card_le_card
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
      change t ∈ anchorNeighbors
        (selectedLiftSystem G side hcross v P hP lower hlower) v y at ht
      rw [mem_anchorNeighbors] at ht
      rw [mem_commonNeighborFinset]
      exact ⟨ht.1, ht.2.symm⟩

/-- Package the selected-middle construction as an anchored lift system.
The only remaining inputs are the two incidence estimates produced by the
dyadic four-cycle selection. -/
noncomputable def selectedAnchoredLiftSystem
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool)
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    (hP : ∀ x y z, P x y z ↔ P z y x)
    (lower : ℕ) (hlower : 0 < lower)
    (leftCap rightCap : ℕ)
    (hcodegree : ∀ y,
      IsMiddleVertex (selectedLiftSystem G side hcross v P hP lower hlower) y →
        codegree G v y ≤ rightCap)
    (hleft : ∀ t,
      (leftPartners
        (selectedLiftSystem G side hcross v P hP lower hlower) t).card ≤ leftCap) :
    AnchoredLiftSystem (selectedPairGraph G v P lower) G where
  toLiftSystem := selectedLiftSystem G side hcross v P hP lower hlower
  anchor := v
  leftCap := leftCap
  rightCap := rightCap
  anchor_adj := fun t ↦ (G.mem_neighborFinset v t.1).mp t.2
  anchor_cap := by
    intro y hy
    exact (anchorNeighbors_card_le_codegree
      G side hcross v P hP lower hlower y).trans (hcodegree y hy)
  left_cap := hleft

end

end Erdos113AnchorConstruction

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/DynamicPruning.lean` -/

section
open scoped Real SimpleGraph

namespace Erdos113DynamicPruning

noncomputable section

open Erdos113Cycles Erdos113CyclePruning
  Erdos113Regular

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The integer load threshold used at one dyadic stage.  The predecessor
of the ceiling, rather than the ceiling itself, is what removes the usual
additive-one loss from the final local estimate. -/
def dynamicThreshold (m R q : ℕ) : ℕ :=
  ⌈((8 * R * (q + 1) : ℕ) : ℝ) / m⌉₊

lemma dynamicThreshold_pos {m R q : ℕ} (hm : 0 < m) (hR : 0 < R) :
    0 < dynamicThreshold m R q := by
  rw [dynamicThreshold, Nat.ceil_pos]
  positivity

lemma cast_dynamicThreshold_sub_one_le {m R q : ℕ}
    (hm : 0 < m) (hR : 0 < R) :
    ((dynamicThreshold m R q - 1 : ℕ) : ℝ) ≤
      ((8 * R * (q + 1) : ℕ) : ℝ) / m := by
  have hpos := dynamicThreshold_pos (q := q) hm hR
  have hlt := Nat.ceil_lt_add_one
    (show 0 ≤ ((8 * R * (q + 1) : ℕ) : ℝ) / m by positivity)
  change (dynamicThreshold m R q : ℝ) <
    ((8 * R * (q + 1) : ℕ) : ℝ) / m + 1 at hlt
  rw [Nat.cast_sub (by omega : 1 ≤ dynamicThreshold m R q), Nat.cast_one]
  linarith

lemma ratio_le_cast_dynamicThreshold {m R q : ℕ} :
    ((8 * R * (q + 1) : ℕ) : ℝ) / m ≤
      (dynamicThreshold m R q : ℝ) := by
  exact Nat.le_ceil _

/-- Internal dyadic recursion.  `m` and `R` remain the initial edge count
and total number of available halving stages, while `r` is the number of
stages still available. -/
private theorem exists_dynamic_pruned_aux
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m R r : ℕ) (hm : 0 < m) (hR : 0 < R) (hr : r ≤ R) :
    ∀ E : Finset (Sym2 V), E ⊆ G.edgeFinset → E.card ≤ m →
      (orderedFourCycles E).card < 2 ^ r →
      ∃ D : Finset (Sym2 V),
        D ⊆ E ∧
        (E \ D).card * (8 * R) ≤ r * m ∧
        ∀ e ∈ D,
          D.card * (orderedFourCyclesThroughEdge D e).card ≤
            16 * R * ((orderedFourCycles D).card + 1) := by
  induction r with
  | zero =>
      intro E hEG hEm hq
      have hqzero : (orderedFourCycles E).card = 0 := by
        simpa using hq
      refine ⟨E, Finset.Subset.rfl, by simp, ?_⟩
      intro e he
      have hsub := orderedFourCyclesThroughEdge_subset E e
      have hloadzero : (orderedFourCyclesThroughEdge E e).card = 0 := by
        have hcard := Finset.card_le_card hsub
        omega
      simp [hloadzero]
  | succ r ih =>
      intro E hEG hEm hq
      let q := (orderedFourCycles E).card
      let K := dynamicThreshold m R q
      have hK : 0 < K := by
        dsimp [K]
        exact dynamicThreshold_pos hm hR
      obtain ⟨E₁, hE₁E, hpaid, hload⟩ :=
        exists_pruned_subset G K E hEG
      have hE₁G : E₁ ⊆ G.edgeFinset := hE₁E.trans hEG
      have hE₁m : E₁.card ≤ m := (Finset.card_le_card hE₁E).trans hEm
      let q₁ := (orderedFourCycles E₁).card
      have hq₁q : q₁ ≤ q := by
        dsimp [q₁, q]
        omega
      have hstage : (E \ E₁).card * (8 * R) ≤ m := by
        have hratio := ratio_le_cast_dynamicThreshold (m := m) (R := R) (q := q)
        have hpaid' : (E \ E₁).card * K ≤ q := by
          dsimp [q, K] at hpaid ⊢
          omega
        have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        have hrealPaid :
            ((E \ E₁).card : ℝ) * (K : ℝ) ≤ (q : ℝ) := by
          exact_mod_cast hpaid'
        have hrealRatio :
            (((8 * R * (q + 1) : ℕ) : ℝ) / m) ≤ (K : ℝ) := by
          simpa [K] using hratio
        have hreal :
            (((E \ E₁).card * (8 * R) : ℕ) : ℝ) < (m : ℝ) := by
          have hqnonneg : (0 : ℝ) ≤ q := by positivity
          have hqone : (0 : ℝ) < q + 1 := by positivity
          have hmul :
              ((E \ E₁).card : ℝ) *
                  ((((8 * R * (q + 1) : ℕ) : ℝ) / m)) ≤ (q : ℝ) :=
            (mul_le_mul_of_nonneg_left hrealRatio
              (by positivity : (0 : ℝ) ≤ (E \ E₁).card)).trans hrealPaid
          push_cast at hmul ⊢
          have hmul' :
              ((E \ E₁).card : ℝ) * (8 * R : ℕ) * (q + 1 : ℕ) ≤
                (q : ℝ) * m := by
            apply (div_le_iff₀ hmR).mp
            calc
              (((E \ E₁).card : ℝ) * (8 * R : ℕ) * (q + 1 : ℕ)) /
                    (m : ℝ) =
                  ((E \ E₁).card : ℝ) *
                    ((((8 * R * (q + 1) : ℕ) : ℝ) / m)) := by
                      push_cast
                      ring
              _ ≤ (q : ℝ) := by
                    simpa [Nat.cast_mul, Nat.cast_add] using hmul
          push_cast at hmul' ⊢
          nlinarith
        exact_mod_cast hreal.le
      by_cases hhalf : 2 * q₁ < q
      · have hq₁pow : q₁ < 2 ^ r := by
          have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
          rw [hpow] at hq
          omega
        obtain ⟨D, hDE₁, hbudget, hlocal⟩ :=
          ih (Nat.le_trans (Nat.le_succ r) hr) E₁ hE₁G hE₁m hq₁pow
        refine ⟨D, hDE₁.trans hE₁E, ?_, hlocal⟩
        have hsplit : (E \ D).card = (E \ E₁).card + (E₁ \ D).card := by
          have h₁ := Finset.card_sdiff_add_card_eq_card hDE₁
          have h₂ := Finset.card_sdiff_add_card_eq_card (hDE₁.trans hE₁E)
          have h₃ := Finset.card_sdiff_add_card_eq_card hE₁E
          omega
        rw [hsplit, Nat.add_mul]
        calc
          (E \ E₁).card * (8 * R) + (E₁ \ D).card * (8 * R) ≤
              m + r * m := Nat.add_le_add hstage hbudget
          _ = (r + 1) * m := by ring
      · have hqle : q ≤ 2 * q₁ := by omega
        refine ⟨E₁, hE₁E, ?_, ?_⟩
        · exact hstage.trans (by
            have : m ≤ (r + 1) * m := by
              nlinarith
            exact this)
        · intro e he
          have hloadNat : (orderedFourCyclesThroughEdge E₁ e).card ≤ K - 1 :=
            Nat.le_sub_one_of_lt (hload e he)
          have hpred := cast_dynamicThreshold_sub_one_le
            (m := m) (R := R) (q := q) hm hR
          have hDcard : E₁.card ≤ m := hE₁m
          have hreal :
              ((E₁.card * (orderedFourCyclesThroughEdge E₁ e).card : ℕ) : ℝ) ≤
                ((16 * R * (q₁ + 1) : ℕ) : ℝ) := by
            have hmnonneg : (0 : ℝ) ≤ m := by positivity
            have hloadReal :
                ((orderedFourCyclesThroughEdge E₁ e).card : ℝ) ≤
                  (K - 1 : ℕ) := by exact_mod_cast hloadNat
            calc
              ((E₁.card * (orderedFourCyclesThroughEdge E₁ e).card : ℕ) : ℝ) ≤
                  (m : ℝ) * (K - 1 : ℕ) := by
                    push_cast
                    gcongr
              _ ≤ (m : ℝ) *
                    (((8 * R * (q + 1) : ℕ) : ℝ) / m) := by gcongr
              _ = ((8 * R * (q + 1) : ℕ) : ℝ) := by
                    field_simp
              _ ≤ ((16 * R * (q₁ + 1) : ℕ) : ℝ) := by
                    exact_mod_cast (by nlinarith :
                      8 * R * (q + 1) ≤ 16 * R * (q₁ + 1))
          exact_mod_cast hreal

/-- Repeated dyadic pruning retains strictly more than half of a nonempty
edge set and gives a local ordered-four-cycle load controlled by the final,
not the initial, ordered-four-cycle count. -/
theorem exists_dynamically_pruned_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset (Sym2 V)) (hE : E ⊆ G.edgeFinset) (R : ℕ) (hR : 0 < R)
    (hEne : E.Nonempty)
    (hq : (orderedFourCycles E).card < 2 ^ R) :
    ∃ D : Finset (Sym2 V),
      D ⊆ E ∧ E.card < 2 * D.card ∧
      ∀ e ∈ D,
        D.card * (orderedFourCyclesThroughEdge D e).card ≤
          16 * R * ((orderedFourCycles D).card + 1) := by
  let m := E.card
  have hm : 0 < m := by simpa [m] using Finset.card_pos.mpr hEne
  obtain ⟨D, hDE, hbudget, hlocal⟩ :=
    exists_dynamic_pruned_aux G m R R hm hR le_rfl E hE (by simp [m]) hq
  refine ⟨D, hDE, ?_, hlocal⟩
  have hcancel : (E \ D).card * 8 ≤ m := by
    have hb : R * ((E \ D).card * 8) ≤ R * m := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hbudget
    exact Nat.le_of_mul_le_mul_left hb hR
  have hcard := Finset.card_sdiff_add_card_eq_card hDE
  dsimp [m] at hcancel
  omega

/-- The graph-theoretic specialization needs only four times the binary
degree-bin count, since the total number of ordered four-cycles is at most
`|V|^4`. -/
theorem exists_dynamically_pruned_edgeFinset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hedge : ∃ x y, G.Adj x y) :
    ∃ D : Finset (Sym2 V),
      D ⊆ G.edgeFinset ∧ G.edgeFinset.card < 2 * D.card ∧
      ∀ e ∈ D,
        D.card * (orderedFourCyclesThroughEdge D e).card ≤
          64 * degreeBinCount (W := V) *
            ((orderedFourCycles D).card + 1) := by
  let L := degreeBinCount (W := V)
  let R := 4 * L
  have hnpos : 0 < Fintype.card V := by
    obtain ⟨x, _y, _hxy⟩ := hedge
    exact Fintype.card_pos_iff.mpr ⟨x⟩
  have hL : 0 < L := by
    dsimp [L, degreeBinCount]
    omega
  have hR : 0 < R := by dsimp [R]; positivity
  have hnlt : Fintype.card V < 2 ^ L := by
    simpa [L, degreeBinCount, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Fintype.card V))
  have hnPow : Fintype.card V ^ 4 < 2 ^ R := by
    calc
      Fintype.card V ^ 4 < (2 ^ L) ^ 4 := by gcongr
      _ = 2 ^ R := by
        -- R = 4 * L, so (2 ^ L) ^ 4 = 2 ^ (L * 4) = 2 ^ (4 * L)
        rw [show R = 4 * L from rfl, ← pow_mul, Nat.mul_comm]
  have hq : (orderedFourCycles G.edgeFinset).card < 2 ^ R :=
    (card_orderedFourCycles_le G.edgeFinset).trans_lt hnPow
  have hEne : G.edgeFinset.Nonempty := by
    obtain ⟨x, y, hxy⟩ := hedge
    exact ⟨s(x, y), by simpa using hxy⟩
  obtain ⟨D, hDsub, hDcard, hDload⟩ :=
    exists_dynamically_pruned_subset G G.edgeFinset Finset.Subset.rfl
      R hR hEne hq
  refine ⟨D, hDsub, hDcard, ?_⟩
  intro e he
  convert hDload e he using 1 <;> dsimp [R, L] <;> ring

end

end Erdos113DynamicPruning

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/FourCycleSelection.lean` -/

section
open scoped SimpleGraph

namespace Erdos113FourCycleSelection

noncomputable section

open Erdos113Cycles Erdos113FourCycles Erdos113CyclePruning
  Erdos113AnchorConstruction

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Rotate a labelled four-cycle by one step. -/
def rotateFour (x : Fin 4 → V) : Fin 4 → V := fun i ↦ x (i + 1)

lemma fin4_add_one_injective : Function.Injective (fun i : Fin 4 ↦ i + 1) := by
  decide +revert

lemma fin4_add_one_add_one (i : Fin 4) : i + 1 + 1 = i + 2 := by
  decide +revert

lemma fin4_sub_one_add_one (i : Fin 4) : i - 1 + 1 = i := by
  decide +revert

lemma rotateFour_injective : Function.Injective (rotateFour : (Fin 4 → V) → Fin 4 → V) := by
  intro x y hxy
  funext i
  have h := congrFun hxy (i - 1)
  simpa [rotateFour, fin4_sub_one_add_one] using h

lemma rotateFour_genuine {G : SimpleGraph V} {x : Fin 4 → V}
    (hx : IsGenuineCycle G x) : IsGenuineCycle G (rotateFour x) := by
  constructor
  · exact hx.1.comp fin4_add_one_injective
  · intro i
    simpa [rotateFour, fin4_add_one_add_one] using hx.2 (i + 1)

@[simp] lemma rotateFour_zero (x : Fin 4 → V) : rotateFour x 0 = x 1 := rfl
@[simp] lemma rotateFour_one (x : Fin 4 → V) : rotateFour x 1 = x 2 := rfl
@[simp] lemma rotateFour_two (x : Fin 4 → V) : rotateFour x 2 = x 3 := rfl
@[simp] lemma rotateFour_three (x : Fin 4 → V) : rotateFour x 3 = x 0 := rfl

/-- Ordered four-cycles for which the diagonal through coordinates `0,2`
has at least the codegree of the other diagonal. -/
def orientedFourCycles (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (Fin 4 → V) :=
  (genuineCycles G 4).filter fun x ↦
    codegree G (x 1) (x 3) ≤ codegree G (x 0) (x 2)

@[simp] lemma mem_orientedFourCycles
    {G : SimpleGraph V} [DecidableRel G.Adj] {x : Fin 4 → V} :
    x ∈ orientedFourCycles G ↔
      IsGenuineCycle G x ∧
        codegree G (x 1) (x 3) ≤ codegree G (x 0) (x 2) := by
  simp [orientedFourCycles]

lemma rotateFour_mem_oriented_of_not
    {G : SimpleGraph V} [DecidableRel G.Adj] {x : Fin 4 → V}
    (hx : IsGenuineCycle G x)
    (hnot : ¬codegree G (x 1) (x 3) ≤ codegree G (x 0) (x 2)) :
    rotateFour x ∈ orientedFourCycles G := by
  rw [mem_orientedFourCycles]
  refine ⟨rotateFour_genuine hx, ?_⟩
  simp only [rotateFour_zero, rotateFour_one, rotateFour_two, rotateFour_three]
  have hlt : codegree G (x 0) (x 2) < codegree G (x 1) (x 3) := by omega
  simpa [codegree, commonNeighborFinset, Finset.inter_comm] using hlt.le

/-- At least half of the labelled ordered four-cycles have the preferred
diagonal orientation. -/
theorem genuineCycles_four_card_le_twice_oriented
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (genuineCycles G 4).card ≤ 2 * (orientedFourCycles G).card := by
  let f : ↑(genuineCycles G 4) →
      ↑(orientedFourCycles G) ⊕ ↑(orientedFourCycles G) := fun x ↦
    if h : codegree G (x.1 1) (x.1 3) ≤ codegree G (x.1 0) (x.1 2) then
      Sum.inl ⟨x.1, (mem_orientedFourCycles).mpr
        ⟨(mem_genuineCycles).mp x.2, h⟩⟩
    else
      Sum.inr ⟨rotateFour x.1,
        rotateFour_mem_oriented_of_not (mem_genuineCycles.mp x.2) h⟩
  have hf : Function.Injective f := by
    intro x y hxy
    dsimp [f] at hxy
    split at hxy <;> split at hxy
    · exact Subtype.ext (congrArg (fun z ↦ z.elim Subtype.val Subtype.val) hxy)
    · contradiction
    · contradiction
    · apply Subtype.ext
      apply rotateFour_injective
      exact congrArg (fun z ↦ z.elim Subtype.val Subtype.val) hxy
  have hcard := Fintype.card_le_of_injective f hf
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  simpa only [Fintype.card_sum, two_mul] using hcard

lemma exists_fiber_with_card_bound
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (T : Finset B) (hT : T.Nonempty) (f : A → B)
    (hf : ∀ x ∈ S, f x ∈ T) :
    ∃ y ∈ T, S.card ≤ T.card * (S.filter fun x ↦ f x = y).card := by
  classical
  let w : B → ℕ := fun y ↦ (S.filter fun x ↦ f x = y).card
  obtain ⟨y, hyT, hymax⟩ := Finset.exists_max_image T w hT
  refine ⟨y, hyT, ?_⟩
  rw [Finset.card_eq_sum_card_fiberwise (s := S) (t := T) hf]
  calc
    (∑ z ∈ T, (S.filter fun x ↦ f x = z).card) ≤
        ∑ _z ∈ T, w y := by
      apply Finset.sum_le_sum
      intro z hz
      exact hymax z hz
    _ = T.card * (S.filter fun x ↦ f x = y).card := by simp [w]

def orientedFourCyclesAt (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Finset (Fin 4 → V) :=
  (orientedFourCycles G).filter fun x ↦ x 0 = v

@[simp] lemma mem_orientedFourCyclesAt
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} {x : Fin 4 → V} :
    x ∈ orientedFourCyclesAt G v ↔
      x ∈ orientedFourCycles G ∧ x 0 = v := by
  simp [orientedFourCyclesAt]

/-- A total logarithmic bucket; values larger than `N` are clamped into the
last bucket.  On values at most `N` it is the ordinary base-two logarithm. -/
def boundedLogIndex (N a : ℕ) : Fin (Nat.log 2 N + 1) :=
  ⟨min (Nat.log 2 a) (Nat.log 2 N), by omega⟩

lemma boundedLogIndex_val_of_le {N a : ℕ} (ha : a ≤ N) :
    (boundedLogIndex N a).val = Nat.log 2 a := by
  dsimp [boundedLogIndex]
  rw [min_eq_left]
  exact Nat.log_mono_right ha

def dyadicFiber {A : Type*} [DecidableEq A]
    (S : Finset A) (N : ℕ) (f : A → ℕ)
    (i : Fin (Nat.log 2 N + 1)) : Finset A :=
  S.filter fun x ↦ boundedLogIndex N (f x) = i

@[simp] lemma mem_dyadicFiber {A : Type*} [DecidableEq A]
    {S : Finset A} {N : ℕ} {f : A → ℕ}
    {i : Fin (Nat.log 2 N + 1)} {x : A} :
    x ∈ dyadicFiber S N f i ↔ x ∈ S ∧ boundedLogIndex N (f x) = i := by
  simp [dyadicFiber]

theorem exists_large_dyadicFiber
    {A : Type*} [DecidableEq A] (S : Finset A) (N : ℕ) (f : A → ℕ) :
    ∃ i : Fin (Nat.log 2 N + 1),
      S.card ≤ (Nat.log 2 N + 1) * (dyadicFiber S N f i).card := by
  have hT : (Finset.univ : Finset (Fin (Nat.log 2 N + 1))).Nonempty := by
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨i, _hi, hcard⟩ := exists_fiber_with_card_bound S
    (Finset.univ : Finset (Fin (Nat.log 2 N + 1))) hT
      (fun x ↦ boundedLogIndex N (f x)) (by simp)
  refine ⟨i, ?_⟩
  simpa [dyadicFiber] using hcard

lemma dyadicFiber_bounds
    {A : Type*} [DecidableEq A] {S : Finset A} {N : ℕ} {f : A → ℕ}
    {i : Fin (Nat.log 2 N + 1)} {x : A}
    (hx : x ∈ dyadicFiber S N f i) (hpos : 0 < f x) (hle : f x ≤ N) :
    2 ^ i.val ≤ f x ∧ f x < 2 ^ (i.val + 1) := by
  have hlog : Nat.log 2 (f x) = i.val := by
    have hi := (mem_dyadicFiber.mp hx).2
    have hb := boundedLogIndex_val_of_le hle
    exact hb.symm.trans (congrArg Fin.val hi)
  exact (Nat.log_eq_iff (b := 2) (m := i.val) (n := f x)
    (Or.inr ⟨Nat.one_lt_two, hpos.ne'⟩)).mp hlog

lemma two_le_codegree_diagonal
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x : Fin 4 → V} (hx : IsGenuineCycle G x) :
    2 ≤ codegree G (x 0) (x 2) := by
  rw [codegree]
  apply Finset.one_lt_card.mpr
  refine ⟨x 1, ?_, x 3, ?_, hx.1.ne (by decide)⟩
  · rw [mem_commonNeighborFinset]
    exact ⟨hx.2 0, (hx.2 1).symm⟩
  · rw [mem_commonNeighborFinset]
    exact ⟨(hx.2 3).symm, hx.2 2⟩

lemma codegree_le_card (G : SimpleGraph V) [DecidableRel G.Adj] (u w : V) :
    codegree G u w ≤ Fintype.card V := by
  rw [codegree]
  exact Finset.card_le_univ _

lemma codegree_comm (G : SimpleGraph V) [DecidableRel G.Adj] (u w : V) :
    codegree G u w = codegree G w u := by
  simp [codegree, commonNeighborFinset, Finset.inter_comm]

def sideVertices (side : V → Bool) (b : Bool) : Finset V :=
  Finset.univ.filter fun v ↦ side v = b

@[simp] lemma mem_sideVertices {side : V → Bool} {b : Bool} {v : V} :
    v ∈ sideVertices side b ↔ side v = b := by
  simp [sideVertices]

def activeSideVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (b : Bool) : Finset V :=
  Finset.univ.filter fun v ↦ side v = b ∧ 0 < G.degree v

@[simp] lemma mem_activeSideVertices
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {side : V → Bool} {b : Bool} {v : V} :
    v ∈ activeSideVertices G side b ↔ side v = b ∧ 0 < G.degree v := by
  simp [activeSideVertices]

def orientedFourCyclesOnSide
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (b : Bool) : Finset (Fin 4 → V) :=
  (orientedFourCycles G).filter fun x ↦ side (x 0) = b

@[simp] lemma mem_orientedFourCyclesOnSide
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {side : V → Bool} {b : Bool} {x : Fin 4 → V} :
    x ∈ orientedFourCyclesOnSide G side b ↔
      x ∈ orientedFourCycles G ∧ side (x 0) = b := by
  simp [orientedFourCyclesOnSide]

theorem exists_side_with_many_oriented_cycles
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) :
    ∃ b : Bool, (orientedFourCycles G).card ≤
      2 * (orientedFourCyclesOnSide G side b).card := by
  obtain ⟨b, _hb, hcard⟩ := exists_fiber_with_card_bound
    (orientedFourCycles G) (Finset.univ : Finset Bool)
      (by simp) (fun x ↦ side (x 0)) (by simp)
  refine ⟨b, ?_⟩
  simpa [orientedFourCyclesOnSide] using hcard

def orientedFourCyclesAtSideAnchor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (b : Bool) (v : V) : Finset (Fin 4 → V) :=
  (orientedFourCyclesOnSide G side b).filter fun x ↦ x 0 = v

@[simp] lemma mem_orientedFourCyclesAtSideAnchor
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {side : V → Bool} {b : Bool} {v : V} {x : Fin 4 → V} :
    x ∈ orientedFourCyclesAtSideAnchor G side b v ↔
      x ∈ orientedFourCycles G ∧ side (x 0) = b ∧ x 0 = v := by
  simp [orientedFourCyclesAtSideAnchor, and_assoc]

theorem exists_side_anchor_with_many_oriented_cycles
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (hne : (orientedFourCycles G).Nonempty) :
    ∃ (b : Bool) (v : V), side v = b ∧
      (orientedFourCycles G).card ≤
        2 * (activeSideVertices G side b).card *
          (orientedFourCyclesAtSideAnchor G side b v).card := by
  obtain ⟨b, hb⟩ := exists_side_with_many_oriented_cycles G side
  have hsideNe : (orientedFourCyclesOnSide G side b).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hOzero : (orientedFourCycles G).card = 0 := by
      rw [hempty] at hb
      simpa using hb
    exact hne.ne_empty (Finset.card_eq_zero.mp hOzero)
  obtain ⟨x, hx⟩ := hsideNe
  have hT : (activeSideVertices G side b).Nonempty := by
    have hxgen := (mem_orientedFourCycles.mp
      (mem_orientedFourCyclesOnSide.mp hx).1).1
    refine ⟨x 0, (mem_activeSideVertices).mpr
      ⟨(mem_orientedFourCyclesOnSide.mp hx).2, ?_⟩⟩
    rw [← G.card_neighborFinset_eq_degree, Finset.card_pos]
    exact ⟨x 1, (G.mem_neighborFinset (x 0) (x 1)).mpr (hxgen.2 0)⟩
  obtain ⟨v, hv, hvcard⟩ := exists_fiber_with_card_bound
    (orientedFourCyclesOnSide G side b) (activeSideVertices G side b) hT
      (fun x ↦ x 0) (by
        intro z hz
        have hzdata := mem_orientedFourCyclesOnSide.mp hz
        have hzgen := (mem_orientedFourCycles.mp hzdata.1).1
        rw [mem_activeSideVertices]
        refine ⟨hzdata.2, ?_⟩
        rw [← G.card_neighborFinset_eq_degree, Finset.card_pos]
        exact ⟨z 1, (G.mem_neighborFinset (z 0) (z 1)).mpr (hzgen.2 0)⟩)
  refine ⟨b, v, (mem_activeSideVertices.mp hv).1, ?_⟩
  calc
    (orientedFourCycles G).card ≤
        2 * (orientedFourCyclesOnSide G side b).card := hb
    _ ≤ 2 * ((activeSideVertices G side b).card *
        (orientedFourCyclesAtSideAnchor G side b v).card) := by
      gcongr
      simpa [orientedFourCyclesAtSideAnchor] using hvcard
    _ = 2 * (activeSideVertices G side b).card *
        (orientedFourCyclesAtSideAnchor G side b v).card := by ring

def anchorCodegreeDyadicCycles
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (b : Bool) (v : V)
    (i : Fin (Nat.log 2 (Fintype.card V) + 1)) : Finset (Fin 4 → V) :=
  dyadicFiber (orientedFourCyclesAtSideAnchor G side b v)
    (Fintype.card V) (fun x ↦ codegree G v (x 2)) i

theorem exists_side_anchor_dyadic_cycles
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (hne : (genuineCycles G 4).Nonempty) :
    ∃ (b : Bool) (v : V)
      (i : Fin (Nat.log 2 (Fintype.card V) + 1)),
      side v = b ∧ 1 ≤ i.val ∧
      (genuineCycles G 4).card ≤
        4 * (activeSideVertices G side b).card *
          (Nat.log 2 (Fintype.card V) + 1) *
            (anchorCodegreeDyadicCycles G side b v i).card := by
  have hgenpos := Finset.card_pos.mpr hne
  have hOpos : 0 < (orientedFourCycles G).card := by
    have hhalf := genuineCycles_four_card_le_twice_oriented G
    omega
  obtain ⟨b, v, hvside, hanchor⟩ :=
    exists_side_anchor_with_many_oriented_cycles G side (Finset.card_pos.mp hOpos)
  obtain ⟨i, hi⟩ := exists_large_dyadicFiber
    (orientedFourCyclesAtSideAnchor G side b v) (Fintype.card V)
      (fun x ↦ codegree G v (x 2))
  have hbinne : (anchorCodegreeDyadicCycles G side b v i).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hAtpos : 0 < (orientedFourCyclesAtSideAnchor G side b v).card := by
      have : 0 < (orientedFourCycles G).card := hOpos
      nlinarith
    change (orientedFourCyclesAtSideAnchor G side b v).card ≤
      (Nat.log 2 (Fintype.card V) + 1) *
        (anchorCodegreeDyadicCycles G side b v i).card at hi
    rw [hempty] at hi
    exact (not_le_of_gt hAtpos) (by simpa using hi)
  obtain ⟨x, hx⟩ := hbinne
  have hxAt := (mem_dyadicFiber.mp hx).1
  have hxdata := mem_orientedFourCyclesAtSideAnchor.mp hxAt
  have hxgen := (mem_orientedFourCycles.mp hxdata.1).1
  have hxzero : x 0 = v := hxdata.2.2
  have hbounds := dyadicFiber_bounds hx
    (by
      have := two_le_codegree_diagonal hxgen
      simpa [hxzero] using (lt_of_lt_of_le Nat.zero_lt_two this))
    (codegree_le_card G v (x 2))
  have hiOne : 1 ≤ i.val := by
    by_contra! hiZero
    have : i.val = 0 := by omega
    rw [this] at hbounds
    have htwo : 2 ≤ codegree G v (x 2) := by
      simpa [hxzero] using two_le_codegree_diagonal hxgen
    omega
  refine ⟨b, v, i, hvside, hiOne, ?_⟩
  calc
    (genuineCycles G 4).card ≤ 2 * (orientedFourCycles G).card :=
      genuineCycles_four_card_le_twice_oriented G
    _ ≤ 2 * (2 * (activeSideVertices G side b).card *
        (orientedFourCyclesAtSideAnchor G side b v).card) := by gcongr
    _ ≤ 2 * (2 * (activeSideVertices G side b).card *
        ((Nat.log 2 (Fintype.card V) + 1) *
          (anchorCodegreeDyadicCycles G side b v i).card)) := by
      gcongr
      simpa [anchorCodegreeDyadicCycles] using hi
    _ = 4 * (activeSideVertices G side b).card *
        (Nat.log 2 (Fintype.card V) + 1) *
          (anchorCodegreeDyadicCycles G side b v i).card := by ring

structure Triple (V : Type*) where
  left : V
  middle : V
  right : V
deriving DecidableEq, Fintype

def cycleTriple (x : Fin 4 → V) : Triple V :=
  ⟨x 1, x 2, x 3⟩

def swapTriple (p : Triple V) : Triple V :=
  ⟨p.right, p.middle, p.left⟩

@[simp] lemma swapTriple_swapTriple (p : Triple V) :
    swapTriple (swapTriple p) = p := by cases p; rfl

lemma cycleTriple_injOn_at_anchor
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {side : V → Bool} {b : Bool} {v : V}
    {i : Fin (Nat.log 2 (Fintype.card V) + 1)} :
    Set.InjOn cycleTriple
      (↑(anchorCodegreeDyadicCycles G side b v i) : Set (Fin 4 → V)) := by
  intro x hx y hy hxy
  have hxAt := (mem_dyadicFiber.mp hx).1
  have hyAt := (mem_dyadicFiber.mp hy).1
  have hxzero := (mem_orientedFourCyclesAtSideAnchor.mp hxAt).2.2
  have hyzero := (mem_orientedFourCyclesAtSideAnchor.mp hyAt).2.2
  funext j
  fin_cases j
  · exact hxzero.trans hyzero.symm
  · exact congrArg Triple.left hxy
  · exact congrArg Triple.middle hxy
  · exact congrArg Triple.right hxy

/-- Symmetrize the selected oriented four-cycles in their two endpoint
coordinates. -/
def selectedTriples
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (b : Bool) (v : V)
    (i : Fin (Nat.log 2 (Fintype.card V) + 1)) : Finset (Triple V) :=
  let A := (anchorCodegreeDyadicCycles G side b v i).image cycleTriple
  A ∪ A.image swapTriple

lemma selectedTriples_symmetric
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (b : Bool) (v : V)
    (i : Fin (Nat.log 2 (Fintype.card V) + 1))
    {p : Triple V} (hp : p ∈ selectedTriples G side b v i) :
    swapTriple p ∈ selectedTriples G side b v i := by
  simp only [selectedTriples, Finset.mem_union, Finset.mem_image] at hp ⊢
  rcases hp with hp | hp
  · right
    exact ⟨p, hp, rfl⟩
  · obtain ⟨q, hq, rfl⟩ := hp
    left
    simpa using hq

lemma anchorCodegreeDyadicCycles_data
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {side : V → Bool} {b : Bool} {v : V}
    {i : Fin (Nat.log 2 (Fintype.card V) + 1)}
    {x : Fin 4 → V} (hx : x ∈ anchorCodegreeDyadicCycles G side b v i) :
    IsGenuineCycle G x ∧ x 0 = v ∧
      codegree G (x 1) (x 3) ≤ codegree G v (x 2) ∧
      2 ^ i.val ≤ codegree G v (x 2) ∧
      codegree G v (x 2) < 2 ^ (i.val + 1) := by
  have hxAt := (mem_dyadicFiber.mp hx).1
  have hxdata := mem_orientedFourCyclesAtSideAnchor.mp hxAt
  have hxorient := mem_orientedFourCycles.mp hxdata.1
  have hxzero := hxdata.2.2
  have hbounds := dyadicFiber_bounds hx
    (by
      have htwo := two_le_codegree_diagonal hxorient.1
      rw [hxzero] at htwo
      omega)
    (codegree_le_card G v (x 2))
  exact ⟨hxorient.1, hxzero, by simpa [hxzero] using hxorient.2,
    hbounds.1, hbounds.2⟩

lemma selectedTriples_card_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (b : Bool) (v : V)
    (i : Fin (Nat.log 2 (Fintype.card V) + 1)) :
    (anchorCodegreeDyadicCycles G side b v i).card ≤
      (selectedTriples G side b v i).card := by
  let A := (anchorCodegreeDyadicCycles G side b v i).image cycleTriple
  calc
    (anchorCodegreeDyadicCycles G side b v i).card = A.card := by
      exact (Finset.card_image_of_injOn cycleTriple_injOn_at_anchor).symm
    _ ≤ (A ∪ A.image swapTriple).card :=
      Finset.card_le_card (Finset.subset_union_left)
    _ = (selectedTriples G side b v i).card := by
      rfl

lemma selectedTriple_data
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {side : V → Bool} {b : Bool} {v : V}
    {i : Fin (Nat.log 2 (Fintype.card V) + 1)}
    {p : Triple V} (hp : p ∈ selectedTriples G side b v i) :
    G.Adj v p.left ∧ G.Adj p.left p.middle ∧
      G.Adj p.middle p.right ∧ G.Adj p.right v ∧
      p.middle ≠ v ∧
      p.left ≠ p.right ∧
      codegree G p.left p.right ≤ codegree G v p.middle ∧
      2 ^ i.val ≤ codegree G v p.middle ∧
      codegree G v p.middle < 2 ^ (i.val + 1) := by
  simp only [selectedTriples, Finset.mem_union, Finset.mem_image] at hp
  rcases hp with hp | hp
  · obtain ⟨x, hx, rfl⟩ := hp
    have h := anchorCodegreeDyadicCycles_data hx
    exact ⟨by simpa [cycleTriple, h.2.1] using h.1.2 0,
      by simpa [cycleTriple] using h.1.2 1,
      by simpa [cycleTriple] using h.1.2 2,
      by simpa [cycleTriple, h.2.1] using h.1.2 3,
      by
        simpa [cycleTriple, h.2.1] using h.1.1.ne (by decide : (2 : Fin 4) ≠ 0),
      by simpa [cycleTriple] using h.1.1.ne (by decide : (1 : Fin 4) ≠ 3),
      by simpa [cycleTriple] using h.2.2.1,
      by simpa [cycleTriple] using h.2.2.2.1,
      by simpa [cycleTriple] using h.2.2.2.2⟩
  · obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨x, hx, rfl⟩ := hq
    have h := anchorCodegreeDyadicCycles_data hx
    exact ⟨by simpa [cycleTriple, swapTriple, h.2.1] using (h.1.2 3).symm,
      by simpa [cycleTriple, swapTriple] using (h.1.2 2).symm,
      by simpa [cycleTriple, swapTriple] using (h.1.2 1).symm,
      by simpa [cycleTriple, swapTriple, h.2.1] using (h.1.2 0).symm,
      by
        simpa [cycleTriple, swapTriple, h.2.1] using
          h.1.1.ne (by decide : (2 : Fin 4) ≠ 0),
      by
        simpa [cycleTriple, swapTriple] using
          h.1.1.ne (by decide : (3 : Fin 4) ≠ 1),
      by
        change codegree G (x 3) (x 1) ≤ codegree G v (x 2)
        rw [codegree_comm]
        exact h.2.2.1,
      by simpa [cycleTriple, swapTriple] using h.2.2.2.1,
      by simpa [cycleTriple, swapTriple] using h.2.2.2.2⟩

structure FirstSelection (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) where
  anchorSide : Bool
  anchor : V
  scaleIndex : Fin (Nat.log 2 (Fintype.card V) + 1)
  triples : Finset (Triple V)
  anchor_side : side anchor = anchorSide
  scaleIndex_pos : 1 ≤ scaleIndex.val
  triples_nonempty : triples.Nonempty
  many : (genuineCycles G 4).card ≤
    4 * (activeSideVertices G side anchorSide).card *
      (Nat.log 2 (Fintype.card V) + 1) * triples.card
  symmetric : ∀ ⦃p⦄, p ∈ triples → swapTriple p ∈ triples
  data : ∀ ⦃p⦄, p ∈ triples →
    G.Adj anchor p.left ∧ G.Adj p.left p.middle ∧
      G.Adj p.middle p.right ∧ G.Adj p.right anchor ∧
      p.middle ≠ anchor ∧
      p.left ≠ p.right ∧
      codegree G p.left p.right ≤ codegree G anchor p.middle ∧
      2 ^ scaleIndex.val ≤ codegree G anchor p.middle ∧
      codegree G anchor p.middle < 2 ^ (scaleIndex.val + 1)

theorem exists_firstSelection
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (hne : (genuineCycles G 4).Nonempty) :
    Nonempty (FirstSelection G side) := by
  obtain ⟨b, v, i, hvside, hipos, hmany⟩ :=
    exists_side_anchor_dyadic_cycles G side hne
  exact ⟨{
    anchorSide := b
    anchor := v
    scaleIndex := i
    triples := selectedTriples G side b v i
    anchor_side := hvside
    scaleIndex_pos := hipos
    triples_nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hsel := selectedTriples_card_lower G side b v i
      rw [hempty] at hsel
      simp only [Finset.card_empty] at hsel
      have hbucket :
          (anchorCodegreeDyadicCycles G side b v i).card = 0 := by
        omega
      have hzero : (genuineCycles G 4).card = 0 := by
        apply Nat.eq_zero_of_le_zero
        simpa [hbucket] using hmany
      exact hne.ne_empty (Finset.card_eq_zero.mp hzero)
    many := hmany.trans (by
      gcongr
      exact selectedTriples_card_lower G side b v i)
    symmetric := fun {_} hp ↦ selectedTriples_symmetric
      (G := G) (side := side) (b := b) (v := v) (i := i) hp
    data := fun {_} hp ↦ selectedTriple_data
      (G := G) (side := side) (b := b) (v := v) (i := i) hp }⟩

namespace FirstSelection

variable {G : SimpleGraph V} [DecidableRel G.Adj] {side : V → Bool}

/-- The symmetric ternary predicate encoded by a first-stage selection. -/
def predicate (S : FirstSelection G side) (x y z : V) : Prop :=
  (⟨x, y, z⟩ : Triple V) ∈ S.triples

instance predicate_decidable (S : FirstSelection G side) (x y z : V) :
    Decidable (S.predicate x y z) := by
  change Decidable ((⟨x, y, z⟩ : Triple V) ∈ S.triples)
  infer_instance

lemma predicate_symm (S : FirstSelection G side) (x y z : V) :
    S.predicate x y z ↔ S.predicate z y x := by
  constructor
  · intro h
    exact S.symmetric h
  · intro h
    simpa [predicate, swapTriple] using S.symmetric h

/-- The ordered pair of neighbours of the anchor occurring as the two
endpoints of a selected triple. -/
def endpointPair (S : FirstSelection G side) (p : ↑S.triples) :
    NeighborVertex G S.anchor × NeighborVertex G S.anchor :=
  (⟨p.1.left, (G.mem_neighborFinset S.anchor p.1.left).mpr
      (S.data p.2).1⟩,
    ⟨p.1.right, (G.mem_neighborFinset S.anchor p.1.right).mpr
      (S.data p.2).2.2.2.1.symm⟩)

@[simp] lemma endpointPair_fst_val (S : FirstSelection G side)
    (p : ↑S.triples) : (S.endpointPair p).1.1 = p.1.left := rfl

@[simp] lemma endpointPair_snd_val (S : FirstSelection G side)
    (p : ↑S.triples) : (S.endpointPair p).2.1 = p.1.right := rfl

def middleCount (S : FirstSelection G side)
    (ab : NeighborVertex G S.anchor × NeighborVertex G S.anchor) : ℕ :=
  (selectedMiddle G S.anchor S.predicate ab.1 ab.2).card

lemma triple_middle_mem (S : FirstSelection G side) (p : ↑S.triples) :
    p.1.middle ∈ selectedMiddle G S.anchor S.predicate
      (S.endpointPair p).1 (S.endpointPair p).2 := by
  rw [mem_selectedMiddle]
  have h := S.data p.2
  exact ⟨h.2.1, h.2.2.1.symm, h.2.2.2.2.1, p.2⟩

lemma selectedMiddle_card_le_codegree (S : FirstSelection G side)
    (ab : NeighborVertex G S.anchor × NeighborVertex G S.anchor) :
    S.middleCount ab ≤ codegree G ab.1.1 ab.2.1 := by
  rw [middleCount, codegree]
  apply Finset.card_le_card
  intro y hy
  exact Finset.mem_inter.mpr
    ⟨(G.mem_neighborFinset ab.1.1 y).mpr
        ((mem_selectedMiddle G S.anchor S.predicate).mp hy |>.1),
      (G.mem_neighborFinset ab.2.1 y).mpr
        ((mem_selectedMiddle G S.anchor S.predicate).mp hy |>.2.1)⟩

lemma middleCount_pos_at_triple (S : FirstSelection G side)
    (p : ↑S.triples) : 0 < S.middleCount (S.endpointPair p) := by
  rw [middleCount]
  exact Finset.card_pos.mpr ⟨p.1.middle, S.triple_middle_mem p⟩

lemma middleCount_lt_scaleCap_at_triple (S : FirstSelection G side)
    (p : ↑S.triples) :
    S.middleCount (S.endpointPair p) < 2 ^ (S.scaleIndex.val + 1) := by
  have hdata := S.data p.2
  exact (S.selectedMiddle_card_le_codegree (S.endpointPair p)).trans_lt
    (hdata.2.2.2.2.2.2.1.trans_lt hdata.2.2.2.2.2.2.2.2)

/-- The second dyadic bucket, now sorting selected triples by the number of
selected middles above their ordered endpoint pair. -/
def secondDyadicTriples (S : FirstSelection G side)
    (j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)) :
    Finset ↑S.triples :=
  dyadicFiber (Finset.univ : Finset ↑S.triples)
    (2 ^ (S.scaleIndex.val + 1))
    (fun p ↦ S.middleCount (S.endpointPair p)) j

def secondDyadicPairs (S : FirstSelection G side)
    (j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)) :
    Finset (NeighborVertex G S.anchor × NeighborVertex G S.anchor) :=
  (S.secondDyadicTriples j).image S.endpointPair

theorem exists_second_dyadic_bucket (S : FirstSelection G side) :
    ∃ j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1),
      S.triples.card ≤
        (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1) *
          (S.secondDyadicTriples j).card := by
  obtain ⟨j, hj⟩ := exists_large_dyadicFiber
    (Finset.univ : Finset ↑S.triples) (2 ^ (S.scaleIndex.val + 1))
      (fun p ↦ S.middleCount (S.endpointPair p))
  refine ⟨j, ?_⟩
  simpa [secondDyadicTriples] using hj

lemma secondDyadicTriples_count_bounds (S : FirstSelection G side)
    {j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)}
    {p : ↑S.triples} (hp : p ∈ S.secondDyadicTriples j) :
    2 ^ j.val ≤ S.middleCount (S.endpointPair p) ∧
      S.middleCount (S.endpointPair p) < 2 ^ (j.val + 1) := by
  apply dyadicFiber_bounds hp (S.middleCount_pos_at_triple p)
  exact (S.middleCount_lt_scaleCap_at_triple p).le

lemma secondDyadicPairs_count_bounds (S : FirstSelection G side)
    {j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)}
    {ab : NeighborVertex G S.anchor × NeighborVertex G S.anchor}
    (hab : ab ∈ S.secondDyadicPairs j) :
    2 ^ j.val ≤ S.middleCount ab ∧
      S.middleCount ab < 2 ^ (j.val + 1) := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hab
  exact S.secondDyadicTriples_count_bounds hp

lemma secondDyadicPairs_ne (S : FirstSelection G side)
    {j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)}
    {ab : NeighborVertex G S.anchor × NeighborVertex G S.anchor}
    (hab : ab ∈ S.secondDyadicPairs j) : ab.1 ≠ ab.2 := by
  obtain ⟨p, _hp, hpab⟩ := Finset.mem_image.mp hab
  intro heq
  have hval := congrArg (fun q : NeighborVertex G S.anchor ↦ q.1) heq
  have hpdata := S.data p.2
  apply hpdata.2.2.2.2.2.1
  simpa [← hpab] using hval

lemma card_le_image_card_mul_of_fiber_le
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (T : Finset A) (f : A → B) (M : ℕ)
    (hfiber : ∀ b ∈ T.image f,
      (T.filter fun a ↦ f a = b).card ≤ M) :
    T.card ≤ (T.image f).card * M := by
  rw [Finset.card_eq_sum_card_fiberwise
    (s := T) (t := T.image f) (fun a ha ↦ Finset.mem_image.mpr ⟨a, ha, rfl⟩)]
  calc
    (∑ b ∈ T.image f, (T.filter fun a ↦ f a = b).card) ≤
        ∑ _b ∈ T.image f, M := by
      apply Finset.sum_le_sum
      intro b hb
      exact hfiber b hb
    _ = (T.image f).card * M := by simp

lemma secondDyadic_fiber_card_le_middleCount (S : FirstSelection G side)
    {j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)}
    {ab : NeighborVertex G S.anchor × NeighborVertex G S.anchor} :
    ((S.secondDyadicTriples j).filter fun p ↦ S.endpointPair p = ab).card ≤
      S.middleCount ab := by
  rw [middleCount]
  apply Finset.card_le_card_of_injOn (fun p : ↑S.triples ↦ p.1.middle)
  · intro p hp
    have hpdata := Finset.mem_filter.mp hp
    have hm := S.triple_middle_mem p
    simpa [hpdata.2] using hm
  · intro p hp q hq hmiddle
    have hpPair := (Finset.mem_filter.mp hp).2
    have hqPair := (Finset.mem_filter.mp hq).2
    have hpqPair : S.endpointPair p = S.endpointPair q :=
      hpPair.trans hqPair.symm
    apply Subtype.ext
    rcases p with ⟨⟨pl, pm, pr⟩, hp'⟩
    rcases q with ⟨⟨ql, qm, qr⟩, hq'⟩
    simp only [endpointPair] at hpqPair
    simp only at hmiddle ⊢
    have hleft : pl = ql := congrArg (fun z ↦ z.1.1) hpqPair
    have hright : pr = qr := congrArg (fun z ↦ z.2.1) hpqPair
    subst ql
    subst qm
    subst qr
    rfl

theorem secondDyadicTriples_card_le_pairs (S : FirstSelection G side)
    (j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)) :
    (S.secondDyadicTriples j).card ≤
      (S.secondDyadicPairs j).card * 2 ^ (j.val + 1) := by
  apply card_le_image_card_mul_of_fiber_le
  intro ab hab
  exact (S.secondDyadic_fiber_card_le_middleCount (j := j) (ab := ab)).trans
    (S.secondDyadicPairs_count_bounds hab).2.le

/-- The auxiliary graph on neighbours of the chosen anchor at the second
dyadic scale. -/
def auxiliaryGraph (S : FirstSelection G side)
    (j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)) :
    SimpleGraph (NeighborVertex G S.anchor) :=
  selectedPairGraph G S.anchor S.predicate (2 ^ j.val)

noncomputable instance auxiliaryGraph_decidableRel (S : FirstSelection G side)
    (j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)) :
    DecidableRel (S.auxiliaryGraph j).Adj := Classical.decRel _

lemma secondDyadicPairs_adj (S : FirstSelection G side)
    {j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)}
    {ab : NeighborVertex G S.anchor × NeighborVertex G S.anchor}
    (hab : ab ∈ S.secondDyadicPairs j) :
    (S.auxiliaryGraph j).Adj ab.1 ab.2 := by
  have hb := S.secondDyadicPairs_count_bounds hab
  rw [auxiliaryGraph, selectedPairGraph, SimpleGraph.fromRel_adj]
  refine ⟨S.secondDyadicPairs_ne hab, Or.inl ?_⟩
  constructor
  · simpa [middleCount] using hb.1
  · have hpow : 2 ^ (j.val + 1) = 2 * 2 ^ j.val := by
      simp [pow_succ, Nat.mul_comm]
    rw [hpow] at hb
    simpa [middleCount] using hb.2.le

theorem secondDyadicPairs_card_le_twice_edges (S : FirstSelection G side)
    (j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)) :
    (S.secondDyadicPairs j).card ≤
      2 * (S.auxiliaryGraph j).edgeFinset.card := by
  have hsubset : S.secondDyadicPairs j ⊆
      (Finset.univ.filter fun ab :
        NeighborVertex G S.anchor × NeighborVertex G S.anchor ↦
          (S.auxiliaryGraph j).Adj ab.1 ab.2) := by
    intro ab hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact S.secondDyadicPairs_adj hab
  exact (Finset.card_le_card hsubset).trans_eq
    (S.auxiliaryGraph j).two_mul_card_edgeFinset.symm

theorem secondDyadicTriples_card_le_auxiliary_edges
    (S : FirstSelection G side)
    (j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)) :
    (S.secondDyadicTriples j).card ≤
      2 ^ (j.val + 2) * (S.auxiliaryGraph j).edgeFinset.card := by
  calc
    (S.secondDyadicTriples j).card ≤
        (S.secondDyadicPairs j).card * 2 ^ (j.val + 1) :=
      S.secondDyadicTriples_card_le_pairs j
    _ ≤ (2 * (S.auxiliaryGraph j).edgeFinset.card) *
        2 ^ (j.val + 1) := by
      gcongr
      exact S.secondDyadicPairs_card_le_twice_edges j
    _ = 2 ^ (j.val + 2) * (S.auxiliaryGraph j).edgeFinset.card := by
      simp [pow_succ]
      ring

/-- The output of Janzer's two dyadic pigeonhole steps.  Its auxiliary
graph has `2^index` to `2^(index+1)` selected middles above each of the
ordered pairs retained by the bucket, and its edge count controls the
number of first-stage triples. -/
structure SecondSelection (S : FirstSelection G side) where
  index : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)
  bucket_nonempty : (S.secondDyadicTriples index).Nonempty
  many : S.triples.card ≤
    (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1) *
      2 ^ (index.val + 2) * (S.auxiliaryGraph index).edgeFinset.card

theorem exists_secondSelection (S : FirstSelection G side) :
    Nonempty S.SecondSelection := by
  obtain ⟨j, hj⟩ := S.exists_second_dyadic_bucket
  exact ⟨{
    index := j
    bucket_nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty] at hj
      simp at hj
      exact S.triples_nonempty.ne_empty hj
    many := hj.trans (by
      calc
        (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1) *
            (S.secondDyadicTriples j).card ≤
            (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1) *
              (2 ^ (j.val + 2) *
                (S.auxiliaryGraph j).edgeFinset.card) := by
          gcongr
          exact S.secondDyadicTriples_card_le_auxiliary_edges j
        _ = (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1) *
              2 ^ (j.val + 2) *
                (S.auxiliaryGraph j).edgeFinset.card := by ring) }⟩

lemma SecondSelection.auxiliary_edge
    (S : FirstSelection G side) (R : S.SecondSelection) :
    ∃ a b, (S.auxiliaryGraph R.index).Adj a b := by
  obtain ⟨p, hp⟩ := R.bucket_nonempty
  let ab := S.endpointPair p
  exact ⟨ab.1, ab.2, S.secondDyadicPairs_adj
    (Finset.mem_image.mpr ⟨p, hp, rfl⟩)⟩

end FirstSelection

end

end Erdos113FourCycleSelection

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/SelectedLift.lean` -/

section
open scoped SimpleGraph

namespace Erdos113SelectedLift

noncomputable section

open Erdos113Cycles Erdos113FourCycles Erdos113ManyLifts
  Erdos113Incidence Erdos113AnchoredLifts Erdos113AnchorConstruction
  Erdos113FourCycleSelection

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {side : V → Bool}

namespace FirstSelection.SecondSelection

variable (S : FirstSelection G side) (R : S.SecondSelection)

/-- The lift system encoded by the two dyadic selections. -/
noncomputable def liftSystem
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x) :
    LiftSystem (S.auxiliaryGraph R.index) G :=
  selectedLiftSystem G side hcross S.anchor S.predicate
    S.predicate_symm (2 ^ R.index.val) (by positivity)

lemma middle_codegree_lt_scaleCap
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    {y : V} (hy : IsMiddleVertex (liftSystem S R hcross) y) :
    codegree G S.anchor y < 2 ^ (S.scaleIndex.val + 1) := by
  rcases hy with ⟨a, b, hy⟩
  have hmem : y ∈ selectedMiddle G S.anchor S.predicate a b := by
    simpa [liftSystem, selectedLiftSystem] using hy
  have hp := (mem_selectedMiddle G S.anchor S.predicate).mp hmem
  exact (S.data hp.2.2.2).2.2.2.2.2.2.2.2

lemma linked_selected_data
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    {t : NeighborVertex G S.anchor} {y : V}
    (hy : Linked (liftSystem S R hcross) t y) :
    G.Adj t.1 y ∧ y ≠ S.anchor ∧
      2 ^ S.scaleIndex.val ≤ codegree G S.anchor y := by
  rcases hy with ⟨b, hy⟩ | ⟨a, hy⟩
  · have hmem : y ∈ selectedMiddle G S.anchor S.predicate t b := by
      simpa [liftSystem, selectedLiftSystem] using hy
    have hm := (mem_selectedMiddle G S.anchor S.predicate).mp hmem
    have hd := S.data hm.2.2.2
    exact ⟨hm.1, hm.2.2.1, hd.2.2.2.2.2.2.2.1⟩
  · have hmem : y ∈ selectedMiddle G S.anchor S.predicate a t := by
      simpa [liftSystem, selectedLiftSystem] using hy
    have hm := (mem_selectedMiddle G S.anchor S.predicate).mp hmem
    have hp : S.predicate t.1 y a.1 :=
      (S.predicate_symm a.1 y t.1).mp hm.2.2.2
    have hd := S.data hp
    exact ⟨hm.2.1, hm.2.2.1, hd.2.2.2.2.2.2.2.1⟩

lemma leftPartners_subset_highCodegreeNeighbors
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (t : NeighborVertex G S.anchor) :
    leftPartners (liftSystem S R hcross) t ⊆
      highCodegreeNeighbors G (2 ^ S.scaleIndex.val - 1) S.anchor t.1 := by
  intro y hy
  have hd := linked_selected_data S R hcross
    ((mem_leftPartners (liftSystem S R hcross)).mp hy)
  rw [mem_highCodegreeNeighbors]
  exact ⟨hd.1, hd.2.1.symm, by
    have hpos : 0 < 2 ^ S.scaleIndex.val := by positivity
    omega⟩

theorem leftPartners_card_mul_threshold_le_extensions
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (t : NeighborVertex G S.anchor) :
    (leftPartners (liftSystem S R hcross) t).card *
        (2 ^ S.scaleIndex.val - 1) ≤
      (extensionsThroughEdge G S.anchor t.1).card := by
  calc
    (leftPartners (liftSystem S R hcross) t).card *
        (2 ^ S.scaleIndex.val - 1) ≤
      (highCodegreeNeighbors G (2 ^ S.scaleIndex.val - 1)
        S.anchor t.1).card * (2 ^ S.scaleIndex.val - 1) := by
      gcongr
      exact leftPartners_subset_highCodegreeNeighbors S R hcross t
    _ ≤ (extensionsThroughEdge G S.anchor t.1).card :=
      card_highCodegreeNeighbors_mul_le_extensionsThroughEdge G
        (2 ^ S.scaleIndex.val - 1)
        ((G.mem_neighborFinset S.anchor t.1).mp t.2 |>.symm)

theorem leftPartners_card_le_of_cycle_cap
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (Q : ℕ)
    (hcycle : ∀ t : NeighborVertex G S.anchor,
      (cyclesThroughEdge G 4 s(S.anchor, t.1)).card ≤ Q)
    (t : NeighborVertex G S.anchor) :
    (leftPartners (liftSystem S R hcross) t).card ≤
      Q / (2 ^ S.scaleIndex.val - 1) := by
  have hthreshold : 0 < 2 ^ S.scaleIndex.val - 1 := by
    have hne : S.scaleIndex.val ≠ 0 := Nat.ne_of_gt S.scaleIndex_pos
    have : 1 < 2 ^ S.scaleIndex.val := Nat.one_lt_two_pow hne
    omega
  rw [Nat.le_div_iff_mul_le hthreshold]
  exact (leftPartners_card_mul_threshold_le_extensions S R hcross t).trans
    ((card_extensionsThroughEdge_le_cyclesThroughEdge G S.anchor t.1
      ((G.mem_neighborFinset S.anchor t.1).mp t.2 |>.symm)).trans
        (hcycle t))

/-- Package the selected lift system with the two incidence caps. -/
noncomputable def anchoredLiftSystem
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (Q : ℕ)
    (hcycle : ∀ t : NeighborVertex G S.anchor,
      (cyclesThroughEdge G 4 s(S.anchor, t.1)).card ≤ Q) :
    AnchoredLiftSystem (S.auxiliaryGraph R.index) G :=
  selectedAnchoredLiftSystem G side hcross S.anchor S.predicate
    S.predicate_symm (2 ^ R.index.val) (by positivity)
    (Q / (2 ^ S.scaleIndex.val - 1))
    (2 ^ (S.scaleIndex.val + 1))
    (fun y hy ↦ (middle_codegree_lt_scaleCap S R hcross hy).le)
    (leftPartners_card_le_of_cycle_cap S R hcross Q hcycle)

end FirstSelection.SecondSelection

end

end Erdos113SelectedLift

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos63/BipartiteHalf.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# A bipartite subgraph containing at least half the edges

This file proves the finite simple-graph form of the elementary maximum-cut
lemma used as Proposition 2.4 in Liu--Montgomery.  The proof exposes a finite
graph as its finset of directed edges and adapts the Boolean-cut induction from
`ErdosProblems/Erdos846.lean`.
-/

namespace Erdos63

attribute [local instance] Classical.propDecidable

/-- A loopless finset of ordered pairs whose coordinates are below `n` has a
Boolean cut containing at least half of its pairs. -/
private lemma nat_bool_cut_half_ind (n : ℕ) (S : Finset (ℕ × ℕ))
    (h_ne : ∀ e ∈ S, e.1 ≠ e.2) (hV : ∀ e ∈ S, e.1 < n ∧ e.2 < n) :
    ∃ f : ℕ → Bool, S.card ≤ 2 * (S.filter fun e ↦ f e.1 ≠ f e.2).card := by
  induction n generalizing S with
  | zero =>
      refine ⟨fun _ ↦ true, ?_⟩
      have hS : S = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        exact Nat.not_lt_zero e.1 (hV e he).1
      simp [hS]
  | succ n ih =>
      let S' := S.filter fun e ↦ e.1 < n ∧ e.2 < n
      have hV' : ∀ e ∈ S', e.1 < n ∧ e.2 < n := by
        intro e he
        exact (Finset.mem_filter.mp he).2
      have h_ne' : ∀ e ∈ S', e.1 ≠ e.2 := by
        intro e he
        exact h_ne e (Finset.mem_filter.mp he).1
      obtain ⟨f', hf'⟩ := ih S' h_ne' hV'
      let S_n := S.filter fun e ↦ ¬(e.1 < n ∧ e.2 < n)
      have h_card : S.card = S'.card + S_n.card := by
        have h := Finset.card_filter_add_card_filter_not
          (s := S) (p := fun e : ℕ × ℕ ↦ e.1 < n ∧ e.2 < n)
        simpa [S', S_n] using h.symm
      have h_count_split (f : ℕ → Bool) :
          (S.filter fun e ↦ f e.1 ≠ f e.2).card =
            (S'.filter fun e ↦ f e.1 ≠ f e.2).card +
              (S_n.filter fun e ↦ f e.1 ≠ f e.2).card := by
        let p : ℕ × ℕ → Prop := fun e ↦ e.1 < n ∧ e.2 < n
        let q : ℕ × ℕ → Prop := fun e ↦ f e.1 ≠ f e.2
        have h := Finset.card_filter_add_card_filter_not (s := S.filter q) (p := p)
        have hA : (S.filter q).filter p = S'.filter q := by
          ext e
          simp [S', p, q, and_left_comm, and_assoc, and_comm]
        have hB : (S.filter q).filter (fun e ↦ ¬p e) = S_n.filter q := by
          ext e
          simp [S_n, p, q, and_assoc, and_comm]
        rw [← h, hA, hB]
      let f1 := fun x ↦ if x = n then true else f' x
      let f2 := fun x ↦ if x = n then false else f' x
      have h_f1_S' :
          (S'.filter fun e ↦ f1 e.1 ≠ f1 e.2).card =
            (S'.filter fun e ↦ f' e.1 ≠ f' e.2).card := by
        apply congrArg Finset.card
        apply Finset.filter_congr
        intro e he
        simp [f1, Nat.ne_of_lt (hV' e he).1, Nat.ne_of_lt (hV' e he).2]
      have h_f2_S' :
          (S'.filter fun e ↦ f2 e.1 ≠ f2 e.2).card =
            (S'.filter fun e ↦ f' e.1 ≠ f' e.2).card := by
        apply congrArg Finset.card
        apply Finset.filter_congr
        intro e he
        simp [f2, Nat.ne_of_lt (hV' e he).1, Nat.ne_of_lt (hV' e he).2]
      have h_sum_Sn :
          (S_n.filter fun e ↦ f1 e.1 ≠ f1 e.2).card +
              (S_n.filter fun e ↦ f2 e.1 ≠ f2 e.2).card = S_n.card := by
        have hcomp :
            S_n.filter (fun e ↦ f2 e.1 ≠ f2 e.2) =
              S_n.filter (fun e ↦ ¬f1 e.1 ≠ f1 e.2) := by
          apply Finset.filter_congr
          intro e he
          have heS : e ∈ S := (Finset.mem_filter.mp he).1
          have hnot : ¬(e.1 < n ∧ e.2 < n) := (Finset.mem_filter.mp he).2
          have hv := hV e heS
          have hne := h_ne e heS
          have hcases : (e.1 = n ∧ e.2 < n) ∨ (e.1 < n ∧ e.2 = n) := by
            omega
          cases hcases with
          | inl h =>
              cases f' e.2 <;> simp [f1, f2, h.1, Nat.ne_of_lt h.2]
          | inr h =>
              cases f' e.1 <;> simp [f1, f2, Nat.ne_of_lt h.1, h.2]
        rw [hcomp]
        exact Finset.card_filter_add_card_filter_not
          (s := S_n) (p := fun e ↦ f1 e.1 ≠ f1 e.2)
      have h_max :
          S_n.card ≤ 2 * (S_n.filter fun e ↦ f1 e.1 ≠ f1 e.2).card ∨
            S_n.card ≤ 2 * (S_n.filter fun e ↦ f2 e.1 ≠ f2 e.2).card := by
        omega
      cases h_max with
      | inl h1 =>
          refine ⟨f1, ?_⟩
          have h_old :
              S'.card ≤ 2 * (S'.filter fun e ↦ f1 e.1 ≠ f1 e.2).card := by
            rwa [h_f1_S']
          rw [h_count_split f1, h_card]
          omega
      | inr h2 =>
          refine ⟨f2, ?_⟩
          have h_old :
              S'.card ≤ 2 * (S'.filter fun e ↦ f2 e.1 ≠ f2 e.2).card := by
            rwa [h_f2_S']
          rw [h_count_split f2, h_card]
          omega

/-- A finite loopless finset of ordered pairs has a Boolean cut containing
at least half of its pairs. -/
private lemma nat_bool_cut_half (S : Finset (ℕ × ℕ))
    (h_ne : ∀ e ∈ S, e.1 ≠ e.2) :
    ∃ f : ℕ → Bool, S.card ≤ 2 * (S.filter fun e ↦ f e.1 ≠ f e.2).card := by
  have h_bound : ∃ n, ∀ e ∈ S, e.1 < n ∧ e.2 < n := by
    refine ⟨S.sup (fun e ↦ max e.1 e.2) + 1, ?_⟩
    intro e he
    have hle : max e.1 e.2 ≤ S.sup (fun e ↦ max e.1 e.2) :=
      Finset.le_sup (f := fun e ↦ max e.1 e.2) he
    omega
  obtain ⟨n, hn⟩ := h_bound
  exact nat_bool_cut_half_ind n S h_ne hn

/-- Every finite simple graph has a spanning bipartite subgraph containing at
least half of its edges. -/
theorem exists_bipartite_subgraph_half {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ H : SimpleGraph V,
      H ≤ G ∧ H.IsBipartite ∧ G.edgeFinset.card ≤ 2 * H.edgeFinset.card := by
  classical
  let enc : V → ℕ := fun v ↦ (Fintype.equivFin V v : ℕ)
  have enc_injective : Function.Injective enc := by
    intro v w hvw
    apply (Fintype.equivFin V).injective
    exact Fin.ext hvw
  let pairEnc : V × V → ℕ × ℕ := fun e ↦ (enc e.1, enc e.2)
  have pairEnc_injective : Function.Injective pairEnc := by
    rintro ⟨v, w⟩ ⟨v', w'⟩ h
    simp only [pairEnc, Prod.mk.injEq] at h ⊢
    exact ⟨enc_injective h.1, enc_injective h.2⟩
  let D : Finset (V × V) := Finset.univ.filter fun e ↦ G.Adj e.1 e.2
  let S : Finset (ℕ × ℕ) := D.image pairEnc
  have hS_ne : ∀ e ∈ S, e.1 ≠ e.2 := by
    intro e he
    obtain ⟨d, hdD, rfl⟩ := Finset.mem_image.mp he
    have hadj : G.Adj d.1 d.2 := (Finset.mem_filter.mp hdD).2
    intro h
    have hv : d.1 = d.2 := enc_injective h
    rw [hv] at hadj
    exact G.loopless.irrefl d.2 hadj
  obtain ⟨f, hf⟩ := nat_bool_cut_half S hS_ne
  let g : V → Bool := fun v ↦ f (enc v)
  let A : Set V := {v | g v = true}
  let H : SimpleGraph V := G.between A Aᶜ
  -- Keep `edgeFinset` independent of the specialized decidability instance for
  -- `between`: the theorem statement was elaborated with this classical one.
  letI : DecidableRel H.Adj := fun _ _ ↦ Classical.propDecidable _
  refine ⟨H, SimpleGraph.between_le, SimpleGraph.between_isBipartite disjoint_compl_right, ?_⟩
  have hS_card : S.card = D.card := Finset.card_image_of_injective D pairEnc_injective
  have hcut_image :
      S.filter (fun e ↦ f e.1 ≠ f e.2) =
        (D.filter fun e ↦ g e.1 ≠ g e.2).image pairEnc := by
    ext e
    simp only [S, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨d, hdD, rfl⟩, hcut⟩
      exact ⟨d, ⟨hdD, hcut⟩, rfl⟩
    · rintro ⟨d, ⟨hdD, hcut⟩, rfl⟩
      exact ⟨⟨d, hdD, rfl⟩, hcut⟩
  have hcut_card :
      (S.filter fun e ↦ f e.1 ≠ f e.2).card =
        (D.filter fun e ↦ g e.1 ≠ g e.2).card := by
    rw [hcut_image, Finset.card_image_of_injective _ pairEnc_injective]
  have hD_card : D.card = 2 * G.edgeFinset.card := by
    simpa [D] using G.two_mul_card_edgeFinset.symm
  have hH_directed :
      D.filter (fun e ↦ g e.1 ≠ g e.2) =
        Finset.univ.filter fun e : V × V ↦ H.Adj e.1 e.2 := by
    ext e
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, H,
      SimpleGraph.between_adj, A, Set.mem_setOf_eq, Set.mem_compl_iff]
    cases h₁ : g e.1 <;> cases h₂ : g e.2 <;> simp [h₁, h₂]
  have hH_card :
      (D.filter fun e ↦ g e.1 ≠ g e.2).card = 2 * H.edgeFinset.card := by
    rw [hH_directed, ← H.two_mul_card_edgeFinset]
  rw [hS_card, hD_card, hcut_card, hH_card] at hf
  exact Nat.le_of_mul_le_mul_left hf Nat.two_pos

end Erdos63

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/HostCell.lean` -/

section
open scoped SimpleGraph

namespace Erdos113HostCell

noncomputable section

open Erdos113Cycles Erdos113Regular Erdos113ActiveBins
  Erdos113CellPruning Erdos113CyclePruning Erdos113DynamicPruning
  Erdos113FourCycles

variable {V : Type*} [Fintype V] [DecidableEq V]

def sideOfColor (c : V → Fin 2) (v : V) : Bool :=
  decide (c v = 1)

lemma sideOfColor_cross {G : SimpleGraph V} {c : V → Fin 2}
    (hc : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w)
    {v w : V} (hvw : G.Adj v w) :
    sideOfColor c w = !(sideOfColor c v) := by
  have hne := hc hvw
  have hv : c v = 0 ∨ c v = 1 := by omega
  have hw : c w = 0 ∨ c w = 1 := by omega
  rcases hv with hv | hv <;> rcases hw with hw | hw <;>
    simp_all [sideOfColor]

def cellPairsAtSide (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (i j : Fin (degreeBinCount (W := V))) (b : Bool) :
    Finset (BinVertex G i × BinVertex G j) :=
  (cellEdges G i j).filter fun p ↦ sideOfColor c p.1.1 = b

@[simp] lemma mem_cellPairsAtSide
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (i j : Fin (degreeBinCount (W := V)))
    {b : Bool} {p : BinVertex G i × BinVertex G j} :
    p ∈ cellPairsAtSide G c i j b ↔
      p ∈ cellEdges G i j ∧ sideOfColor c p.1.1 = b := by
  simp [cellPairsAtSide]

lemma exists_dense_oriented_cell
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (hedge : ∃ x y, G.Adj x y) :
    ∃ (i j : Fin (degreeBinCount (W := V))) (b : Bool),
      (cellPairsAtSide G c i j b).Nonempty ∧
      G.edgeFinset.card ≤
        2 * degreeBinCount (W := V) ^ 2 *
          (cellPairsAtSide G c i j b).card ∧
      (degreeBin G i).card * 2 ^ (i.val + 1) +
          (degreeBin G j).card * 2 ^ (j.val + 1) ≤
        8 * degreeBinCount (W := V) *
          (cellPairsAtSide G c i j b).card := by
  obtain ⟨i, j, hcellpos, hdense, hbalanced⟩ :=
    exists_dense_active_degree_cell G hedge
  let E₀ := cellPairsAtSide G c i j false
  let E₁ := cellPairsAtSide G c i j true
  have hsum : E₀.card + E₁.card = (cellEdges G i j).card := by
    have hunion : E₀ ∪ E₁ = cellEdges G i j := by
      ext p
      by_cases h : sideOfColor c p.1.1 = false <;>
        simp [E₀, E₁, cellPairsAtSide, h]
    have hdisj : Disjoint E₀ E₁ := by
      rw [Finset.disjoint_left]
      intro p hp₀ hp₁
      have h₀ := (mem_cellPairsAtSide G c i j).mp hp₀
      have h₁ := (mem_cellPairsAtSide G c i j).mp hp₁
      simp_all [E₀, E₁]
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  by_cases hhalf : (cellEdges G i j).card ≤ 2 * E₀.card
  · have hE₀pos : 0 < E₀.card := by
      rw [card_cellEdges] at hhalf
      omega
    refine ⟨i, j, false, Finset.card_pos.mp hE₀pos, ?_, ?_⟩
    · calc
        G.edgeFinset.card ≤
            degreeBinCount (W := V) ^ 2 * cellCount G i j := hdense
        _ = degreeBinCount (W := V) ^ 2 * (cellEdges G i j).card := by
          rw [card_cellEdges]
        _ ≤ degreeBinCount (W := V) ^ 2 * (2 * E₀.card) := by gcongr
        _ = 2 * degreeBinCount (W := V) ^ 2 *
            (cellPairsAtSide G c i j false).card := by
          dsimp [E₀]
          ring
    · calc
        (degreeBin G i).card * 2 ^ (i.val + 1) +
            (degreeBin G j).card * 2 ^ (j.val + 1) ≤
            4 * degreeBinCount (W := V) * cellCount G i j := hbalanced
        _ = 4 * degreeBinCount (W := V) * (cellEdges G i j).card := by
          rw [card_cellEdges]
        _ ≤ 4 * degreeBinCount (W := V) * (2 * E₀.card) := by gcongr
        _ = 8 * degreeBinCount (W := V) *
            (cellPairsAtSide G c i j false).card := by
          dsimp [E₀]
          ring
  · have hhalf₁ : (cellEdges G i j).card ≤ 2 * E₁.card := by omega
    have hE₁pos : 0 < E₁.card := by
      rw [card_cellEdges] at hhalf₁
      omega
    refine ⟨i, j, true, Finset.card_pos.mp hE₁pos, ?_, ?_⟩
    · calc
        G.edgeFinset.card ≤
            degreeBinCount (W := V) ^ 2 * cellCount G i j := hdense
        _ = degreeBinCount (W := V) ^ 2 * (cellEdges G i j).card := by
          rw [card_cellEdges]
        _ ≤ degreeBinCount (W := V) ^ 2 * (2 * E₁.card) := by gcongr
        _ = 2 * degreeBinCount (W := V) ^ 2 *
            (cellPairsAtSide G c i j true).card := by
          dsimp [E₁]
          ring
    · calc
        (degreeBin G i).card * 2 ^ (i.val + 1) +
            (degreeBin G j).card * 2 ^ (j.val + 1) ≤
            4 * degreeBinCount (W := V) * cellCount G i j := hbalanced
        _ = 4 * degreeBinCount (W := V) * (cellEdges G i j).card := by
          rw [card_cellEdges]
        _ ≤ 4 * degreeBinCount (W := V) * (2 * E₁.card) := by gcongr
        _ = 8 * degreeBinCount (W := V) *
            (cellPairsAtSide G c i j true).card := by
          dsimp [E₁]
          ring

def cellPairEdge {G : SimpleGraph V} [DecidableRel G.Adj]
    {i j : Fin (degreeBinCount (W := V))}
    (p : BinVertex G i × BinVertex G j) : Sym2 V :=
  s(p.1.1, p.2.1)

lemma cellPairEdge_injOn
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (hc : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w)
    (i j : Fin (degreeBinCount (W := V))) (b : Bool) :
    Set.InjOn (cellPairEdge (G := G) (i := i) (j := j))
      (cellPairsAtSide G c i j b) := by
  intro p hp q hq hpq
  have hpdata := (mem_cellPairsAtSide G c i j).mp hp
  have hqdata := (mem_cellPairsAtSide G c i j).mp hq
  have hpAdj := (mem_cellEdges G i j p).mp hpdata.1
  have hqAdj := (mem_cellEdges G i j q).mp hqdata.1
  rcases Sym2.eq_iff.mp hpq with hsame | hswap
  · apply Prod.ext
    · apply Subtype.ext
      exact hsame.1
    · apply Subtype.ext
      exact hsame.2
  · have hpCross := sideOfColor_cross hc hpAdj
    have hqCross := sideOfColor_cross hc hqAdj
    have hbad : b = !b := by
      calc
        b = sideOfColor c p.1.1 := hpdata.2.symm
        _ = sideOfColor c q.2.1 := by rw [hswap.1]
        _ = !(sideOfColor c q.1.1) := hqCross
        _ = !b := by rw [hqdata.2]
    cases b <;> contradiction

def orientedCellEdges
  (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (i j : Fin (degreeBinCount (W := V))) (b : Bool) :
    Finset (Sym2 V) :=
  (cellPairsAtSide G c i j b).image
    (cellPairEdge (G := G) (i := i) (j := j))

lemma card_orientedCellEdges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (hc : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w)
    (i j : Fin (degreeBinCount (W := V))) (b : Bool) :
    (orientedCellEdges G c i j b).card =
      (cellPairsAtSide G c i j b).card := by
  exact Finset.card_image_iff.mpr (cellPairEdge_injOn G c hc i j b)

lemma orientedCellEdges_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (i j : Fin (degreeBinCount (W := V))) (b : Bool) :
    orientedCellEdges G c i j b ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
  have hpCell := (mem_cellPairsAtSide G c i j).mp hp
  have hpAdj := (mem_cellEdges G i j p).mp hpCell.1
  simpa [cellPairEdge] using hpAdj

lemma endpoint_mem_degreeBin_of_mem_orientedCellEdges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (hc : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w)
    (i j : Fin (degreeBinCount (W := V))) (b : Bool)
    {v w : V} (hvw : s(v, w) ∈ orientedCellEdges G c i j b) :
    (sideOfColor c v = b → v ∈ degreeBin G i) ∧
      (sideOfColor c v ≠ b → v ∈ degreeBin G j) := by
  obtain ⟨p, hp, hpedge⟩ := Finset.mem_image.mp hvw
  have hpdata := (mem_cellPairsAtSide G c i j).mp hp
  have hpAdj := (mem_cellEdges G i j p).mp hpdata.1
  have hpCross := sideOfColor_cross hc hpAdj
  change s(p.1.1, p.2.1) = s(v, w) at hpedge
  rcases Sym2.eq_iff.mp hpedge with hsame | hswap
  · refine ⟨?_, ?_⟩
    · intro _
      simpa [← hsame.1] using p.1.2
    intro hne
    exact False.elim (hne (by simpa [← hsame.1] using hpdata.2))
  · refine ⟨?_, ?_⟩
    · intro heq
      have hsidev : sideOfColor c v = !b := by
        calc
          sideOfColor c v = sideOfColor c p.2.1 :=
            congrArg (sideOfColor c) hswap.2.symm
          _ = !(sideOfColor c p.1.1) := hpCross
          _ = !b := congrArg (fun x : Bool ↦ !x) hpdata.2
      cases b <;> simp_all
    · intro _
      simpa [← hswap.2] using p.2.2

lemma graphOfOrientedSubset_degree_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (hc : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w)
    (i j : Fin (degreeBinCount (W := V))) (b : Bool)
    (D : Finset (Sym2 V)) (hD : D ⊆ orientedCellEdges G c i j b)
    (v : V) :
    (graphOfEdges D).degree v ≤
      if sideOfColor c v = b then 2 ^ (i.val + 1) else 2 ^ (j.val + 1) := by
  let P := graphOfEdges D
  by_cases hz : P.degree v = 0
  · simp [P, hz]
  · have hpos : 0 < P.degree v := Nat.pos_of_ne_zero hz
    have hneighbor : (P.neighborFinset v).Nonempty := Finset.card_pos.mp (by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact hpos)
    obtain ⟨w, hw⟩ := hneighbor
    have hpAdj : P.Adj v w := (P.mem_neighborFinset v w).mp hw
    have hedgeD : s(v, w) ∈ D := (graphOfEdges_adj_iff.mp hpAdj).1
    have hbins := endpoint_mem_degreeBin_of_mem_orientedCellEdges
      G c hc i j b (hD hedgeD)
    have hdegreeMono : P.degree v ≤ G.degree v := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree,
        ← SimpleGraph.card_neighborFinset_eq_degree]
      apply Finset.card_le_card
      intro y hy
      apply (G.mem_neighborFinset v y).mpr
      simpa using (orientedCellEdges_subset G c i j b
        (hD (graphOfEdges_adj_iff.mp ((P.mem_neighborFinset v y).mp hy)).1))
    by_cases hvb : sideOfColor c v = b
    · rw [if_pos hvb]
      exact hdegreeMono.trans (degree_bounds_of_mem_bin G i (hbins.1 hvb)).2.le
    · rw [if_neg hvb]
      exact hdegreeMono.trans (degree_bounds_of_mem_bin G j (hbins.2 hvb)).2.le

lemma graphOfOrientedSubset_cross
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (hc : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w)
    (i j : Fin (degreeBinCount (W := V))) (b : Bool)
    (D : Finset (Sym2 V)) (hD : D ⊆ orientedCellEdges G c i j b)
    {v w : V} (hvw : (graphOfEdges D).Adj v w) :
    sideOfColor c w = !(sideOfColor c v) := by
  apply sideOfColor_cross hc
  simpa using (orientedCellEdges_subset G c i j b
    (hD (graphOfEdges_adj_iff.mp hvw).1))

/-- Vertices on one color side which are incident with a retained edge. -/
def liveSideVertices (D : Finset (Sym2 V)) (c : V → Fin 2) (b : Bool) :
    Finset V :=
  Finset.univ.filter fun v ↦
    sideOfColor c v = b ∧ 0 < (graphOfEdges D).degree v

@[simp] lemma mem_liveSideVertices
    {D : Finset (Sym2 V)} {c : V → Fin 2} {b : Bool} {v : V} :
    v ∈ liveSideVertices D c b ↔
      sideOfColor c v = b ∧ 0 < (graphOfEdges D).degree v := by
  simp [liveSideVertices]

lemma liveSideVertices_subset_leftBin
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (hc : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w)
    (i j : Fin (degreeBinCount (W := V))) (b : Bool)
    (D : Finset (Sym2 V)) (hD : D ⊆ orientedCellEdges G c i j b) :
    liveSideVertices D c b ⊆ degreeBin G i := by
  intro v hv
  have hvdata := mem_liveSideVertices.mp hv
  have hneigh : ((graphOfEdges D).neighborFinset v).Nonempty := by
    rw [← Finset.card_pos]
    simpa using hvdata.2
  obtain ⟨w, hw⟩ := hneigh
  have hvw := ((graphOfEdges D).mem_neighborFinset v w).mp hw
  have hedge : s(v, w) ∈ orientedCellEdges G c i j b :=
    hD (graphOfEdges_adj_iff.mp hvw).1
  exact (endpoint_mem_degreeBin_of_mem_orientedCellEdges
    G c hc i j b hedge).1 hvdata.1

lemma liveSideVertices_subset_rightBin
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (hc : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w)
    (i j : Fin (degreeBinCount (W := V))) (b : Bool)
    (D : Finset (Sym2 V)) (hD : D ⊆ orientedCellEdges G c i j b) :
    liveSideVertices D c (!b) ⊆ degreeBin G j := by
  intro v hv
  have hvdata := mem_liveSideVertices.mp hv
  have hneigh : ((graphOfEdges D).neighborFinset v).Nonempty := by
    rw [← Finset.card_pos]
    simpa using hvdata.2
  obtain ⟨w, hw⟩ := hneigh
  have hvw := ((graphOfEdges D).mem_neighborFinset v w).mp hw
  have hedge : s(v, w) ∈ orientedCellEdges G c i j b :=
    hD (graphOfEdges_adj_iff.mp hvw).1
  apply (endpoint_mem_degreeBin_of_mem_orientedCellEdges
    G c hc i j b hedge).2
  intro heq
  have hbad : b = !b := heq.symm.trans hvdata.1
  cases b <;> simp at hbad

/-- Every graph with an edge has a dense, genuinely bipartite dyadic cell
which has also been dynamically pruned.  The two dyadic degree caps are
retained, more than half of the oriented cell edges survive, and every
surviving edge has final-relative ordered-four-cycle load. -/
theorem exists_dense_dynamically_pruned_bipartite_cell
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hedge : ∃ x y, G.Adj x y) :
    ∃ (c : V → Fin 2) (i j : Fin (degreeBinCount (W := V)))
      (b : Bool) (D : Finset (Sym2 V)),
      D.Nonempty ∧ D ⊆ G.edgeFinset ∧
      G.edgeFinset.card <
        8 * degreeBinCount (W := V) ^ 2 * D.card ∧
      (∀ ⦃v w⦄, (graphOfEdges D).Adj v w →
        sideOfColor c w = !(sideOfColor c v)) ∧
      (∀ v, (graphOfEdges D).degree v ≤
        if sideOfColor c v = b then 2 ^ (i.val + 1)
        else 2 ^ (j.val + 1)) ∧
      2 ^ (i.val + 1) ≤ 2 * G.maxDegree ∧
      2 ^ (j.val + 1) ≤ 2 * G.maxDegree ∧
      (liveSideVertices D c b).card * 2 ^ (i.val + 1) +
          (liveSideVertices D c (!b)).card * 2 ^ (j.val + 1) <
        16 * degreeBinCount (W := V) * D.card ∧
      ∀ e ∈ D,
        D.card * (orderedFourCyclesThroughEdge D e).card ≤
          64 * degreeBinCount (W := V) *
            ((orderedFourCycles D).card + 1) := by
  classical
  obtain ⟨H, hHG, hHbip, hGHcard⟩ :=
    Erdos63.exists_bipartite_subgraph_half G
  obtain ⟨c, hc⟩ := hHbip
  have hcne : ∀ ⦃v w⦄, H.Adj v w → c v ≠ c w := by
    intro v w hvw
    simpa using hc hvw
  have hGcardpos : 0 < G.edgeFinset.card := by
    obtain ⟨x, y, hxy⟩ := hedge
    exact Finset.card_pos.mpr ⟨s(x, y), by simpa using hxy⟩
  have hHcardpos : 0 < H.edgeFinset.card := by omega
  have hHedge : ∃ x y, H.Adj x y := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp hHcardpos
    induction e using Sym2.inductionOn with
    | _ x y => exact ⟨x, y, by simpa using he⟩
  obtain ⟨i, j, b, hcellne, hcellDense, hcellBalanced⟩ :=
    exists_dense_oriented_cell H c hHedge
  let E := orientedCellEdges H c i j b
  let C := graphOfEdges E
  have hEH : E ⊆ H.edgeFinset := orientedCellEdges_subset H c i j b
  have hCEdge : C.edgeFinset = E := by
    dsimp [C]
    exact edgeFinset_graphOfEdges_of_subset hEH
  have hEne : E.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hE
    have : (cellPairsAtSide H c i j b).card = 0 := by
      rw [← card_orientedCellEdges H c hcne i j b]
      simp [E, hE]
    have := Finset.card_pos.mpr hcellne
    omega
  have hCedge : ∃ x y, C.Adj x y := by
    obtain ⟨e, he⟩ := hEne
    induction e using Sym2.inductionOn with
    | _ x y =>
        refine ⟨x, y, ?_⟩
        rw [graphOfEdges_adj_iff]
        have hxy : H.Adj x y := by simpa using hEH he
        exact ⟨he, hxy.ne⟩
  obtain ⟨D, hDC, hCDcard, hDload⟩ :=
    exists_dynamically_pruned_edgeFinset C hCedge
  have hDE : D ⊆ E := by simpa [hCEdge] using hDC
  have hDorient : D ⊆ orientedCellEdges H c i j b := by simpa [E] using hDE
  have hDnonempty : D.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hDempty
    simp [hDempty] at hCDcard
  have hDG : D ⊆ G.edgeFinset :=
    hDorient.trans (orientedCellEdges_subset H c i j b) |>.trans
      (SimpleGraph.edgeFinset_mono hHG)
  have hEcard : E.card = (cellPairsAtSide H c i j b).card := by
    simpa [E] using card_orientedCellEdges H c hcne i j b
  obtain ⟨p, hp⟩ := hcellne
  have hpCell := (mem_cellPairsAtSide H c i j).mp hp
  have hleftCap : 2 ^ (i.val + 1) ≤ 2 * G.maxDegree := by
    have hlower := (degree_bounds_of_mem_bin H i p.1.2).1
    have hmono : H.degree p.1.1 ≤ G.degree p.1.1 :=
      SimpleGraph.degree_le_of_le hHG
    calc
      2 ^ (i.val + 1) = 2 * 2 ^ i.val := by ring
      _ ≤ 2 * H.degree p.1.1 := by gcongr
      _ ≤ 2 * G.degree p.1.1 := by gcongr
      _ ≤ 2 * G.maxDegree := by gcongr; exact G.degree_le_maxDegree _
  have hrightCap : 2 ^ (j.val + 1) ≤ 2 * G.maxDegree := by
    have hlower := (degree_bounds_of_mem_bin H j p.2.2).1
    have hmono : H.degree p.2.1 ≤ G.degree p.2.1 :=
      SimpleGraph.degree_le_of_le hHG
    calc
      2 ^ (j.val + 1) = 2 * 2 ^ j.val := by ring
      _ ≤ 2 * H.degree p.2.1 := by gcongr
      _ ≤ 2 * G.degree p.2.1 := by gcongr
      _ ≤ 2 * G.maxDegree := by gcongr; exact G.degree_le_maxDegree _
  have hDenseFinal : G.edgeFinset.card <
      8 * degreeBinCount (W := V) ^ 2 * D.card := by
    calc
      G.edgeFinset.card ≤ 2 * H.edgeFinset.card := hGHcard
      _ ≤ 2 * (2 * degreeBinCount (W := V) ^ 2 *
            (cellPairsAtSide H c i j b).card) := by gcongr
      _ = 4 * degreeBinCount (W := V) ^ 2 * E.card := by
        rw [hEcard]
        ring
      _ < 4 * degreeBinCount (W := V) ^ 2 * (2 * D.card) := by
        gcongr
        · dsimp [degreeBinCount]
          positivity
        · simpa [hCEdge] using hCDcard
      _ = 8 * degreeBinCount (W := V) ^ 2 * D.card := by ring
  have hBalancedFinal :
      (liveSideVertices D c b).card * 2 ^ (i.val + 1) +
          (liveSideVertices D c (!b)).card * 2 ^ (j.val + 1) <
        16 * degreeBinCount (W := V) * D.card := by
    calc
      (liveSideVertices D c b).card * 2 ^ (i.val + 1) +
          (liveSideVertices D c (!b)).card * 2 ^ (j.val + 1) ≤
          (degreeBin H i).card * 2 ^ (i.val + 1) +
            (degreeBin H j).card * 2 ^ (j.val + 1) := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_right _ (Finset.card_le_card
            (liveSideVertices_subset_leftBin H c hcne i j b D hDorient))
        · exact Nat.mul_le_mul_right _ (Finset.card_le_card
            (liveSideVertices_subset_rightBin H c hcne i j b D hDorient))
      _ ≤ 8 * degreeBinCount (W := V) *
          (cellPairsAtSide H c i j b).card := hcellBalanced
      _ = 8 * degreeBinCount (W := V) * E.card := by rw [hEcard]
      _ < 8 * degreeBinCount (W := V) * (2 * D.card) := by
        gcongr
        · dsimp [degreeBinCount]
          positivity
        · simpa [hCEdge] using hCDcard
      _ = 16 * degreeBinCount (W := V) * D.card := by ring
  refine ⟨c, i, j, b, D, hDnonempty, hDG, hDenseFinal, ?_, ?_,
    hleftCap, hrightCap, ?_, ?_⟩
  · intro v w hvw
    exact graphOfOrientedSubset_cross H c hcne i j b D hDorient hvw
  · intro v
    exact graphOfOrientedSubset_degree_le H c hcne i j b D hDorient v
  · exact hBalancedFinal
  · intro e he
    simpa [hCEdge] using hDload e he

/-- A named package for the dynamically pruned balanced host cell. -/
structure DenseHostCell (G : SimpleGraph V) [DecidableRel G.Adj] where
  color : V → Fin 2
  leftIndex : Fin (degreeBinCount (W := V))
  rightIndex : Fin (degreeBinCount (W := V))
  anchorSide : Bool
  edges : Finset (Sym2 V)
  edges_nonempty : edges.Nonempty
  edges_subset : edges ⊆ G.edgeFinset
  dense : G.edgeFinset.card <
    8 * degreeBinCount (W := V) ^ 2 * edges.card
  cross : ∀ ⦃v w : V⦄, (graphOfEdges edges).Adj v w →
    sideOfColor color w = !(sideOfColor color v)
  degree_cap : ∀ v : V, (graphOfEdges edges).degree v ≤
    if sideOfColor color v = anchorSide then 2 ^ (leftIndex.1 + 1)
    else 2 ^ (rightIndex.1 + 1)
  leftCap_le : 2 ^ (leftIndex.1 + 1) ≤ 2 * G.maxDegree
  rightCap_le : 2 ^ (rightIndex.1 + 1) ≤ 2 * G.maxDegree
  balanced :
    (liveSideVertices edges color anchorSide).card * 2 ^ (leftIndex.1 + 1) +
        (liveSideVertices edges color (!anchorSide)).card *
          2 ^ (rightIndex.1 + 1) <
      16 * degreeBinCount (W := V) * edges.card
  local_load : ∀ e ∈ edges,
    edges.card * (orderedFourCyclesThroughEdge edges e).card ≤
      64 * degreeBinCount (W := V) *
        ((orderedFourCycles edges).card + 1)

theorem exists_denseHostCell
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hedge : ∃ x y, G.Adj x y) : Nonempty (DenseHostCell G) := by
  obtain ⟨c, i, j, b, D, hne, hsub, hdense, hcross, hcap,
      hleftCap, hrightCap, hbal, hload⟩ :=
    exists_dense_dynamically_pruned_bipartite_cell G hedge
  exact ⟨{
    color := c
    leftIndex := i
    rightIndex := j
    anchorSide := b
    edges := D
    edges_nonempty := hne
    edges_subset := hsub
    dense := hdense
    cross := hcross
    degree_cap := hcap
    leftCap_le := hleftCap
    rightCap_le := hrightCap
    balanced := hbal
    local_load := hload }⟩

def DenseHostCell.dynamicCycleCap
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G) : ℕ :=
  (64 * degreeBinCount (W := V) *
      ((orderedFourCycles H.edges).card + 1)) / H.edges.card

theorem DenseHostCell.cyclesThroughEdge_le_dynamicCycleCap
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G)
    {u v : V} (huv : (graphOfEdges H.edges).Adj u v) :
    (cyclesThroughEdge (graphOfEdges H.edges) 4 s(u, v)).card ≤
      H.dynamicCycleCap := by
  have hedge : s(u, v) ∈ H.edges := (graphOfEdges_adj_iff.mp huv).1
  rw [dynamicCycleCap, Nat.le_div_iff_mul_le H.edges_nonempty.card_pos]
  simpa [orderedFourCyclesThroughEdge, Nat.mul_comm] using
    H.local_load s(u, v) hedge

theorem DenseHostCell.extensionsThroughEdge_le_dynamicCycleCap
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G)
    {u v : V} (huv : (graphOfEdges H.edges).Adj v u) :
    (extensionsThroughEdge (graphOfEdges H.edges) u v).card ≤
      H.dynamicCycleCap :=
  (card_extensionsThroughEdge_le_cyclesThroughEdge
    (graphOfEdges H.edges) u v huv).trans
      (H.cyclesThroughEdge_le_dynamicCycleCap huv.symm)

def sideFinset (c : V → Fin 2) (b : Bool) : Finset V :=
  Finset.univ.filter fun v ↦ sideOfColor c v = b

@[simp] lemma mem_sideFinset {c : V → Fin 2} {b : Bool} {v : V} :
    v ∈ sideFinset c b ↔ sideOfColor c v = b := by
  simp [sideFinset]

lemma graphOfEdges_isBipartiteWith_sideClass
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G) :
    (graphOfEdges H.edges).IsBipartiteWith
      (↑(sideFinset H.color H.anchorSide) : Set V)
      (↑(sideFinset H.color (!H.anchorSide)) : Set V) := by
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    intro v hv hnv
    have hv' := mem_sideFinset.mp hv
    have hnv' := mem_sideFinset.mp hnv
    have hbad : H.anchorSide = !H.anchorSide := hv'.symm.trans hnv'
    cases H.anchorSide <;> simp at hbad
  · intro v w hvw
    have hcross := H.cross hvw
    by_cases hv : sideOfColor H.color v = H.anchorSide
    · left
      refine ⟨mem_sideFinset.mpr hv, mem_sideFinset.mpr ?_⟩
      simpa [hv] using hcross
    · right
      have hv' : sideOfColor H.color v = !H.anchorSide := by
        cases h : sideOfColor H.color v <;>
          cases hb : H.anchorSide <;> simp_all
      refine ⟨mem_sideFinset.mpr hv', mem_sideFinset.mpr ?_⟩
      simpa [hv'] using hcross

lemma DenseHostCell.edge_card_le_card_mul_leftCap
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G) :
    H.edges.card ≤ Fintype.card V * 2 ^ (H.leftIndex.val + 1) := by
  let P := graphOfEdges H.edges
  let S := sideFinset H.color H.anchorSide
  have hPG : H.edges ⊆ G.edgeFinset := H.edges_subset
  have hPE : P.edgeFinset = H.edges := by
    exact edgeFinset_graphOfEdges_of_subset hPG
  have hsum : ∑ v ∈ S, P.degree v = H.edges.card := by
    calc
      ∑ v ∈ S, P.degree v = P.edgeFinset.card := by
        simpa [S] using P.isBipartiteWith_sum_degrees_eq_card_edges
          (graphOfEdges_isBipartiteWith_sideClass H)
      _ = H.edges.card := congrArg Finset.card hPE
  rw [← hsum]
  calc
    ∑ v ∈ S, P.degree v ≤
        ∑ _v ∈ S, 2 ^ (H.leftIndex.val + 1) := by
      apply Finset.sum_le_sum
      intro v hv
      have hvside : sideOfColor H.color v = H.anchorSide := by
        simpa [S, sideFinset] using hv
      simpa [P, hvside] using H.degree_cap v
    _ = S.card * 2 ^ (H.leftIndex.val + 1) := by simp
    _ ≤ Fintype.card V * 2 ^ (H.leftIndex.val + 1) := by
      gcongr
      exact Finset.card_le_univ S

lemma DenseHostCell.edge_card_le_card_mul_rightCap
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G) :
    H.edges.card ≤ Fintype.card V * 2 ^ (H.rightIndex.val + 1) := by
  let P := graphOfEdges H.edges
  let S := sideFinset H.color (!H.anchorSide)
  have hPG : H.edges ⊆ G.edgeFinset := H.edges_subset
  have hPE : P.edgeFinset = H.edges := by
    exact edgeFinset_graphOfEdges_of_subset hPG
  have hsum : ∑ v ∈ S, P.degree v = H.edges.card := by
    calc
      ∑ v ∈ S, P.degree v = P.edgeFinset.card := by
        simpa [S] using P.isBipartiteWith_sum_degrees_eq_card_edges'
          (graphOfEdges_isBipartiteWith_sideClass H)
      _ = H.edges.card := congrArg Finset.card hPE
  rw [← hsum]
  calc
    ∑ v ∈ S, P.degree v ≤
        ∑ _v ∈ S, 2 ^ (H.rightIndex.val + 1) := by
      apply Finset.sum_le_sum
      intro v hv
      have hvside : sideOfColor H.color v = !H.anchorSide := by
        simpa [S, sideFinset] using hv
      have hvne : sideOfColor H.color v ≠ H.anchorSide := by
        intro heq
        have : H.anchorSide = !H.anchorSide := heq.symm.trans hvside
        cases H.anchorSide <;> simp at this
      simpa [P, hvne] using H.degree_cap v
    _ = S.card * 2 ^ (H.rightIndex.val + 1) := by simp
    _ ≤ Fintype.card V * 2 ^ (H.rightIndex.val + 1) := by
      gcongr
      exact Finset.card_le_univ S

def DenseHostCell.sideCap
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G)
    (b : Bool) : ℕ :=
  if b = H.anchorSide then 2 ^ (H.leftIndex.val + 1)
  else 2 ^ (H.rightIndex.val + 1)

lemma DenseHostCell.edge_card_le_card_mul_sideCap
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G) (b : Bool) :
    H.edges.card ≤ Fintype.card V * H.sideCap b := by
  by_cases hb : b = H.anchorSide
  · subst b
    simpa [DenseHostCell.sideCap] using H.edge_card_le_card_mul_leftCap
  · have hb' : b = !H.anchorSide := by
      cases hb0 : b <;> cases ha : H.anchorSide <;> simp_all
    rw [hb']
    simpa [DenseHostCell.sideCap] using H.edge_card_le_card_mul_rightCap

lemma DenseHostCell.sideCap_le_two_maxDegree
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G) (b : Bool) :
    H.sideCap b ≤ 2 * G.maxDegree := by
  by_cases hb : b = H.anchorSide
  · simpa [DenseHostCell.sideCap, hb] using H.leftCap_le
  · simpa [DenseHostCell.sideCap, hb] using H.rightCap_le

end

end Erdos113HostCell

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/HostPruning.lean` -/

section
open scoped SimpleGraph BigOperators

namespace Erdos113HostPruning

noncomputable section

open Erdos113Regular Erdos113CellPruning Erdos113HostCell
  Erdos113Pruning Erdos113Cycles Erdos113FourCycles

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma incidenceFinset_graphOfEdges_inter
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {D E : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) (hED : E ⊆ D)
    (v : V) :
    E ∩ (graphOfEdges D).incidenceFinset v =
      (graphOfEdges E).incidenceFinset v := by
  have hE : E ⊆ G.edgeFinset := hED.trans hD
  rw [(graphOfEdges D).incidenceFinset_eq_filter,
    (graphOfEdges E).incidenceFinset_eq_filter,
    edgeFinset_graphOfEdges_of_subset hD,
    edgeFinset_graphOfEdges_of_subset hE]
  ext e
  simp only [Finset.mem_inter, Finset.mem_filter]
  tauto

lemma live_of_positive_degree_subset
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {D E : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) (hED : E ⊆ D)
    (c : V → Fin 2) {b : Bool} {v : V}
    (hvside : sideOfColor c v = b)
    (hv : 0 < (graphOfEdges E).degree v) :
    v ∈ liveSideVertices D c b := by
  rw [mem_liveSideVertices]
  refine ⟨hvside, ?_⟩
  rw [← (graphOfEdges D).card_incidenceFinset_eq_degree]
  rw [← (graphOfEdges E).card_incidenceFinset_eq_degree] at hv
  exact hv.trans_le (Finset.card_le_card (by
      intro e he
      rw [← incidenceFinset_graphOfEdges_inter hD hED] at he
      exact (Finset.mem_inter.mp he).2))

/-- A final low-degree deletion on a dynamically pruned cell.  The balanced
cell estimate pays for both sides, so more than half of the edges remain. -/
theorem exists_minDegree_pruned_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (i j : Fin (degreeBinCount (W := V))) (b : Bool)
    (D : Finset (Sym2 V)) (hD : D ⊆ G.edgeFinset) (hDne : D.Nonempty)
    (hbalanced :
      (liveSideVertices D c b).card * 2 ^ (i.val + 1) +
          (liveSideVertices D c (!b)).card * 2 ^ (j.val + 1) <
        16 * degreeBinCount (W := V) * D.card) :
    ∃ E : Finset (Sym2 V),
      E ⊆ D ∧ D.card < 2 * E.card ∧ E.Nonempty ∧
      ∀ v, 0 < (graphOfEdges E).degree v →
        (if sideOfColor c v = b then
          cellThreshold (2 ^ (i.val + 1))
            (4 * degreeBinCount (W := V))
        else
          cellThreshold (2 ^ (j.val + 1))
            (4 * degreeBinCount (W := V))) ≤
          (graphOfEdges E).degree v := by
  classical
  let XL := liveSideVertices D c b
  let XR := liveSideVertices D c (!b)
  let S := XL ∪ XR
  let L := degreeBinCount (W := V)
  let tL := cellThreshold (2 ^ (i.val + 1)) (4 * L)
  let tR := cellThreshold (2 ^ (j.val + 1)) (4 * L)
  let threshold : V → ℕ := fun v ↦ if v ∈ XL then tL else tR
  let fiber : V → Finset (Sym2 V) := fun v ↦
    (graphOfEdges D).incidenceFinset v
  have hLpos : 0 < L := by dsimp [L, degreeBinCount]; omega
  have hXLXR : Disjoint XL XR := by
    rw [Finset.disjoint_left]
    intro v hvL hvR
    have hLside := (mem_liveSideVertices.mp hvL).1
    have hRside := (mem_liveSideVertices.mp hvR).1
    have hbad : b = !b := hLside.symm.trans hRside
    cases b <;> simp at hbad
  have hsumNat :
      ∑ v ∈ S, (threshold v - 1) =
        XL.card * (tL - 1) + XR.card * (tR - 1) := by
    change ∑ v ∈ XL ∪ XR, (threshold v - 1) = _
    rw [Finset.sum_union hXLXR]
    congr 1
    · calc
        ∑ v ∈ XL, (threshold v - 1) =
            ∑ _v ∈ XL, (tL - 1) := by
          apply Finset.sum_congr rfl
          intro v hvL
          simp [threshold, hvL]
        _ = XL.card * (tL - 1) := by simp
    · calc
        ∑ v ∈ XR, (threshold v - 1) =
            ∑ _v ∈ XR, (tR - 1) := by
          apply Finset.sum_congr rfl
          intro v hvR
          have hvnot : v ∉ XL := fun hvL ↦
            Finset.disjoint_left.mp hXLXR hvL hvR
          simp [threshold, hvnot]
        _ = XR.card * (tR - 1) := by simp
  have htL := cast_cellThreshold_sub_one_le
    (cap := 2 ^ (i.val + 1)) (L := 4 * L)
      (by positivity) (by positivity)
  have htR := cast_cellThreshold_sub_one_le
    (cap := 2 ^ (j.val + 1)) (L := 4 * L)
      (by positivity) (by positivity)
  have hcost : ((∑ v ∈ S, (threshold v - 1) : ℕ) : ℝ) <
      (D.card : ℝ) / 4 := by
    rw [hsumNat, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
    have hleft : (XL.card : ℝ) * (tL - 1 : ℕ) ≤
        (XL.card : ℝ) * (2 ^ (i.val + 1) : ℕ) / (64 * L) := by
      calc
        (XL.card : ℝ) * (tL - 1 : ℕ) ≤
            (XL.card : ℝ) *
              ((2 ^ (i.val + 1) : ℕ) / (16 * (4 * L) : ℕ)) := by
          gcongr
        _ = _ := by push_cast; ring
    have hright : (XR.card : ℝ) * (tR - 1 : ℕ) ≤
        (XR.card : ℝ) * (2 ^ (j.val + 1) : ℕ) / (64 * L) := by
      calc
        (XR.card : ℝ) * (tR - 1 : ℕ) ≤
            (XR.card : ℝ) *
              ((2 ^ (j.val + 1) : ℕ) / (16 * (4 * L) : ℕ)) := by
          gcongr
        _ = _ := by push_cast; ring
    have hbalancedR :
        (XL.card : ℝ) * (2 ^ (i.val + 1) : ℕ) +
            (XR.card : ℝ) * (2 ^ (j.val + 1) : ℕ) <
          16 * L * (D.card : ℝ) := by
      exact_mod_cast hbalanced
    calc
      (XL.card : ℝ) * (tL - 1 : ℕ) +
          (XR.card : ℝ) * (tR - 1 : ℕ) ≤
        (XL.card : ℝ) * (2 ^ (i.val + 1) : ℕ) / (64 * L) +
          (XR.card : ℝ) * (2 ^ (j.val + 1) : ℕ) / (64 * L) :=
        add_le_add hleft hright
      _ = ((XL.card : ℝ) * (2 ^ (i.val + 1) : ℕ) +
          (XR.card : ℝ) * (2 ^ (j.val + 1) : ℕ)) / (64 * L) := by ring
      _ < (16 * L * (D.card : ℝ)) / (64 * L) := by
        gcongr
      _ = (D.card : ℝ) / 4 := by
        have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
        field_simp
        ring
  obtain ⟨E, hED, hcard, hstable⟩ :=
    exists_pruned_indexed D S fiber threshold
  have hmore : D.card < 2 * E.card := by
    have hcardR : (D.card : ℝ) ≤ (E.card : ℝ) +
        ((∑ v ∈ S, (threshold v - 1) : ℕ) : ℝ) := by
      exact_mod_cast hcard
    have : (D.card : ℝ) < 2 * E.card := by nlinarith
    exact_mod_cast this
  have hEne : E.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    rw [hzero] at hmore
    simp at hmore
  refine ⟨E, hED, hmore, hEne, ?_⟩
  intro v hv
  have hside : sideOfColor c v = b ∨ sideOfColor c v = !b := by
    cases sideOfColor c v <;> cases b <;> simp
  have hvS : v ∈ S := by
    rcases hside with hs | hs
    · exact Finset.mem_union_left _
        (live_of_positive_degree_subset hD hED c hs hv)
    · exact Finset.mem_union_right _
        (live_of_positive_degree_subset hD hED c hs hv)
  have hincne : (E ∩ fiber v).Nonempty := by
    rw [show E ∩ fiber v = (graphOfEdges E).incidenceFinset v by
      exact incidenceFinset_graphOfEdges_inter hD hED v]
    rw [← Finset.card_pos, (graphOfEdges E).card_incidenceFinset_eq_degree]
    exact hv
  have hst := hstable v hvS hincne
  rw [show E ∩ fiber v = (graphOfEdges E).incidenceFinset v by
    exact incidenceFinset_graphOfEdges_inter hD hED v,
    (graphOfEdges E).card_incidenceFinset_eq_degree] at hst
  by_cases hs : sideOfColor c v = b
  · have hvXL : v ∈ XL := live_of_positive_degree_subset hD hED c hs hv
    simpa [threshold, tL, L, hs, hvXL] using hst
  · have hvnot : v ∉ XL := by
      intro hvXL
      exact hs (mem_liveSideVertices.mp hvXL).1
    simpa [threshold, tR, L, hs, hvnot] using hst

/-- The minimum-degree refinement of a named dense host cell. -/
structure MinDegreeHostCell
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G) where
  edges : Finset (Sym2 V)
  edges_subset : edges ⊆ H.edges
  dense : H.edges.card < 2 * edges.card
  edges_nonempty : edges.Nonempty
  min_degree : ∀ v, 0 < (graphOfEdges edges).degree v →
    (if sideOfColor H.color v = H.anchorSide then
      cellThreshold (2 ^ (H.leftIndex.val + 1))
        (4 * degreeBinCount (W := V))
    else
      cellThreshold (2 ^ (H.rightIndex.val + 1))
        (4 * degreeBinCount (W := V))) ≤
      (graphOfEdges edges).degree v

theorem DenseHostCell.exists_minDegreeHostCell
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G) :
    Nonempty (MinDegreeHostCell H) := by
  obtain ⟨E, hsub, hdense, hne, hmin⟩ := exists_minDegree_pruned_subset
    G H.color H.leftIndex H.rightIndex H.anchorSide H.edges
      H.edges_subset H.edges_nonempty H.balanced
  exact ⟨{
    edges := E
    edges_subset := hsub
    dense := hdense
    edges_nonempty := hne
    min_degree := hmin }⟩

abbrev LiveVertex (E : Finset (Sym2 V)) := (graphOfEdges E).support

def liveGraph (E : Finset (Sym2 V)) : SimpleGraph (LiveVertex E) :=
  (graphOfEdges E).induce (graphOfEdges E).support

noncomputable instance liveGraph_decidableRel (E : Finset (Sym2 V)) :
    DecidableRel (liveGraph E).Adj := Classical.decRel _

lemma liveGraph_degree (E : Finset (Sym2 V)) (v : LiveVertex E) :
    (liveGraph E).degree v = (graphOfEdges E).degree v.1 := by
  exact (graphOfEdges E).degree_induce_support v

def liveSide (E : Finset (Sym2 V)) (c : V → Fin 2)
    (v : LiveVertex E) : Bool := sideOfColor c v.1

lemma MinDegreeHostCell.live_cross
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : DenseHostCell G} (K : MinDegreeHostCell H)
    {x y : LiveVertex K.edges} (hxy : (liveGraph K.edges).Adj x y) :
    liveSide K.edges H.color y = !liveSide K.edges H.color x := by
  have hsub : K.edges ⊆ (graphOfEdges H.edges).edgeFinset := by
    simpa [edgeFinset_graphOfEdges_of_subset H.edges_subset] using K.edges_subset
  exact H.cross ((graphOfEdges_le hsub) hxy)

lemma MinDegreeHostCell.live_degree_cap
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : DenseHostCell G} (K : MinDegreeHostCell H)
    (v : LiveVertex K.edges) :
    (liveGraph K.edges).degree v ≤
      if liveSide K.edges H.color v = H.anchorSide then
        2 ^ (H.leftIndex.val + 1)
      else 2 ^ (H.rightIndex.val + 1) := by
  rw [liveGraph_degree]
  have hsub : K.edges ⊆ (graphOfEdges H.edges).edgeFinset := by
    simpa [edgeFinset_graphOfEdges_of_subset H.edges_subset] using K.edges_subset
  exact (SimpleGraph.degree_le_of_le (graphOfEdges_le hsub)).trans
    (H.degree_cap v.1)

lemma MinDegreeHostCell.live_degree_min
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : DenseHostCell G} (K : MinDegreeHostCell H)
    (v : LiveVertex K.edges) :
    (if liveSide K.edges H.color v = H.anchorSide then
      cellThreshold (2 ^ (H.leftIndex.val + 1))
        (4 * degreeBinCount (W := V))
    else
      cellThreshold (2 ^ (H.rightIndex.val + 1))
        (4 * degreeBinCount (W := V))) ≤
      (liveGraph K.edges).degree v := by
  rw [liveGraph_degree]
  apply K.min_degree
  rw [SimpleGraph.degree_pos_iff_mem_support]
  exact v.2

def sideMinimum
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G)
    (b : Bool) : ℝ :=
  (H.sideCap b : ℝ) / (64 * degreeBinCount (W := V) : ℕ)

lemma MinDegreeHostCell.live_degree_upper_real
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : DenseHostCell G} (K : MinDegreeHostCell H)
    (v : LiveVertex K.edges) :
    ((liveGraph K.edges).degree v : ℝ) ≤
      H.sideCap (liveSide K.edges H.color v) := by
  exact_mod_cast K.live_degree_cap v

lemma MinDegreeHostCell.live_degree_lower_real
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : DenseHostCell G} (K : MinDegreeHostCell H)
    (v : LiveVertex K.edges) :
    sideMinimum H (liveSide K.edges H.color v) ≤
      ((liveGraph K.edges).degree v : ℝ) := by
  let L := degreeBinCount (W := V)
  have hmin := K.live_degree_min v
  have hL : 0 < L := by dsimp [L, degreeBinCount]; omega
  by_cases hb : liveSide K.edges H.color v = H.anchorSide
  · have hceil := cap_div_le_cast_cellThreshold
        (cap := 2 ^ (H.leftIndex.val + 1)) (L := 4 * L)
    have hcast :
        ((cellThreshold (2 ^ (H.leftIndex.val + 1)) (4 * L) : ℕ) : ℝ) ≤
          ((liveGraph K.edges).degree v : ℝ) := by
      exact_mod_cast (by simpa [hb] using hmin)
    calc
      sideMinimum H (liveSide K.edges H.color v) =
          ((2 ^ (H.leftIndex.val + 1) : ℕ) : ℝ) /
            (16 * (4 * L) : ℕ) := by
        simp [sideMinimum, DenseHostCell.sideCap, hb, L]
        ring
      _ ≤ (cellThreshold (2 ^ (H.leftIndex.val + 1)) (4 * L) : ℕ) := hceil
      _ ≤ ((liveGraph K.edges).degree v : ℝ) := hcast
  · have hceil := cap_div_le_cast_cellThreshold
        (cap := 2 ^ (H.rightIndex.val + 1)) (L := 4 * L)
    have hcast :
        ((cellThreshold (2 ^ (H.rightIndex.val + 1)) (4 * L) : ℕ) : ℝ) ≤
          ((liveGraph K.edges).degree v : ℝ) := by
      exact_mod_cast (by simpa [hb] using hmin)
    calc
      sideMinimum H (liveSide K.edges H.color v) =
          ((2 ^ (H.rightIndex.val + 1) : ℕ) : ℝ) /
            (16 * (4 * L) : ℕ) := by
        simp [sideMinimum, DenseHostCell.sideCap, hb, L]
        ring
      _ ≤ (cellThreshold (2 ^ (H.rightIndex.val + 1)) (4 * L) : ℕ) := hceil
      _ ≤ ((liveGraph K.edges).degree v : ℝ) := hcast

lemma MinDegreeHostCell.liveGraph_edge_card
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : DenseHostCell G} (K : MinDegreeHostCell H) :
    (liveGraph K.edges).edgeFinset.card = K.edges.card := by
  have hKG : K.edges ⊆ G.edgeFinset := K.edges_subset.trans H.edges_subset
  calc
    (liveGraph K.edges).edgeFinset.card =
        (graphOfEdges K.edges).edgeFinset.card :=
      (graphOfEdges K.edges).card_edgeFinset_induce_support
    _ = K.edges.card := congrArg Finset.card
      (edgeFinset_graphOfEdges_of_subset hKG)

noncomputable def liveExtensionEmbedding (E : Finset (Sym2 V))
    (u y : LiveVertex E) :
    ↑(extensionsThroughEdge (liveGraph E) u y) →
      ↑(extensionsThroughEdge (graphOfEdges E) u.1 y.1) := fun p ↦ by
  refine ⟨⟨p.1.1.1, p.1.2.1⟩, ?_⟩
  have hp := mem_extensionsThroughEdge.mp p.2
  rw [mem_extensionsThroughEdge]
  exact ⟨hp.1, (fun h ↦ hp.2.1 (Subtype.ext h)),
    hp.2.2.1, hp.2.2.2.1,
      (fun h ↦ hp.2.2.2.2 (Subtype.ext h))⟩

lemma liveExtensionEmbedding_injective (E : Finset (Sym2 V))
    (u y : LiveVertex E) :
    Function.Injective (liveExtensionEmbedding E u y) := by
  intro p q hpq
  have ht := congrArg Subtype.val hpq
  change (⟨p.1.1.1, p.1.2.1⟩ : Σ _x : V, V) =
    ⟨q.1.1.1, q.1.2.1⟩ at ht
  apply Subtype.ext
  apply Sigma.ext
  · apply Subtype.ext
    exact congrArg (fun z : Σ _x : V, V ↦ z.1) ht
  · apply heq_of_eq
    apply Subtype.ext
    exact congrArg (fun z : Σ _x : V, V ↦ z.2) ht

lemma card_liveExtensions_le (E : Finset (Sym2 V))
    (u y : LiveVertex E) :
    (extensionsThroughEdge (liveGraph E) u y).card ≤
      (extensionsThroughEdge (graphOfEdges E) u.1 y.1).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective (liveExtensionEmbedding E u y)
      (liveExtensionEmbedding_injective E u y)

lemma MinDegreeHostCell.extensionsThroughEdge_le_dynamicCycleCap
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : DenseHostCell G} (K : MinDegreeHostCell H)
    {u y : LiveVertex K.edges} (huy : (liveGraph K.edges).Adj y u) :
    (extensionsThroughEdge (liveGraph K.edges) u y).card ≤
      H.dynamicCycleCap := by
  have hEU : (graphOfEdges K.edges).Adj y.1 u.1 := huy
  have hsub : K.edges ⊆ (graphOfEdges H.edges).edgeFinset := by
    simpa [edgeFinset_graphOfEdges_of_subset H.edges_subset] using K.edges_subset
  have hDU : (graphOfEdges H.edges).Adj y.1 u.1 :=
    (graphOfEdges_le hsub) hEU
  calc
    (extensionsThroughEdge (liveGraph K.edges) u y).card ≤
        (extensionsThroughEdge (graphOfEdges K.edges) u.1 y.1).card :=
      card_liveExtensions_le K.edges u y
    _ ≤ (cyclesThroughEdge (graphOfEdges K.edges) 4 s(u.1, y.1)).card :=
      card_extensionsThroughEdge_le_cyclesThroughEdge
        (graphOfEdges K.edges) u.1 y.1 hEU
    _ ≤ (cyclesThroughEdge (graphOfEdges H.edges) 4 s(u.1, y.1)).card :=
      Finset.card_le_card (cyclesThroughEdge_mono
        (graphOfEdges_le hsub) 4 s(u.1, y.1))
    _ ≤ H.dynamicCycleCap := H.cyclesThroughEdge_le_dynamicCycleCap hDU.symm

theorem MinDegreeHostCell.liveGraph_isContained_original
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : DenseHostCell G} (K : MinDegreeHostCell H) :
    liveGraph K.edges ⊑ G := by
  have hsub : K.edges ⊆ (graphOfEdges H.edges).edgeFinset := by
    simpa [edgeFinset_graphOfEdges_of_subset H.edges_subset] using K.edges_subset
  have hlive : liveGraph K.edges ⊑ graphOfEdges K.edges := by
    exact ⟨(SimpleGraph.Embedding.induce
      (graphOfEdges K.edges).support).toCopy⟩
  exact hlive.trans_le
    ((graphOfEdges_le hsub).trans (graphOfEdges_le H.edges_subset))

end

end Erdos113HostPruning

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/AlmostRegular.lean` -/

section
open scoped BigOperators SimpleGraph

namespace Erdos113AlmostRegular

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

open Erdos113Pruning Erdos113Cycles

/-- A maximum-weight `b`-subset.  Every point outside it has weight at most
every point inside it, and hence `b` times its weight is bounded by the total
weight of the subset. -/
theorem exists_top_subset {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → ℕ) (b : ℕ) (hb : b ≤ Fintype.card V) :
    ∃ B : Finset V, B.card = b ∧
      ∀ x ∉ B, b * w x ≤ ∑ y ∈ B, w y := by
  classical
  let candidates := (Finset.univ : Finset V).powersetCard b
  have hcand : candidates.Nonempty := by
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hb
    exact ⟨B, by simpa [candidates, hBcard] using hBsub⟩
  obtain ⟨B, hBcand, hBmax⟩ :=
    Finset.exists_max_image candidates (fun A ↦ ∑ y ∈ A, w y) hcand
  have hBcard : B.card = b := (Finset.mem_powersetCard.mp hBcand).2
  refine ⟨B, hBcard, ?_⟩
  intro x hx
  have hpoint : ∀ y ∈ B, w x ≤ w y := by
    intro y hy
    by_contra! hyx
    let B' := insert x (B.erase y)
    have hB'card : B'.card = b := by
      dsimp [B']
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_erase_of_mem hy, hBcard]
        have : 0 < b := by
          rw [← hBcard, Finset.card_pos]
          exact ⟨y, hy⟩
        omega
      · simp [hx]
    have hB'mem : B' ∈ candidates := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hB'card⟩
    have hle := hBmax B' hB'mem
    have hsum : (∑ z ∈ B, w z) < ∑ z ∈ B', w z := by
      have herase : (∑ z ∈ B.erase y, w z) + w y = ∑ z ∈ B, w z :=
        Finset.sum_erase_add _ _ hy
      have hxerase : x ∉ B.erase y := by simp [hx]
      rw [show (∑ z ∈ B', w z) = w x + ∑ z ∈ B.erase y, w z by
        dsimp [B']
        exact Finset.sum_insert hxerase]
      omega
    omega
  calc
    b * w x = ∑ _y ∈ B, w x := by simp [hBcard]
    _ ≤ ∑ y ∈ B, w y := Finset.sum_le_sum fun y hy ↦ hpoint y hy

def dartsFrom (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) : Finset (V × V) :=
  Finset.univ.filter fun p ↦ p.1 ∈ B ∧ G.Adj p.1 p.2

@[simp] lemma mem_dartsFrom {G : SimpleGraph V} [DecidableRel G.Adj]
    {B : Finset V} {p : V × V} :
    p ∈ dartsFrom G B ↔ p.1 ∈ B ∧ G.Adj p.1 p.2 := by
  simp [dartsFrom]

lemma card_dartsFrom (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) :
    (dartsFrom G B).card = ∑ v ∈ B, G.degree v := by
  classical
  rw [dartsFrom, Finset.card_filter]
  rw [show (Finset.univ : Finset (V × V)) =
    (Finset.univ : Finset V).product Finset.univ by ext; simp]
  calc
    (∑ p ∈ (Finset.univ : Finset V).product Finset.univ,
        (if p.1 ∈ B ∧ G.Adj p.1 p.2 then (1 : ℕ) else 0)) =
        ∑ x ∈ (Finset.univ : Finset V), ∑ y ∈ (Finset.univ : Finset V),
          (if x ∈ B ∧ G.Adj x y then (1 : ℕ) else 0) := by
      exact Finset.sum_product _ _ _
    _ = ∑ x ∈ B, ∑ y : V,
          (if G.Adj x y then (1 : ℕ) else 0) := by
      calc
        (∑ x : V, ∑ y : V,
            (if x ∈ B ∧ G.Adj x y then (1 : ℕ) else 0)) =
            ∑ x : V, if x ∈ B then
              (∑ y : V, if G.Adj x y then (1 : ℕ) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxB : x ∈ B <;> simp [hxB]
        _ = ∑ x ∈ B, ∑ y : V,
              (if G.Adj x y then (1 : ℕ) else 0) := by
          rw [← Finset.sum_filter]
          simp
    _ = ∑ x ∈ B, G.degree x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.card_filter, show
        (Finset.univ.filter fun y ↦ G.Adj x y) = G.neighborFinset x by ext; simp]
      exact G.card_neighborFinset_eq_degree x

def dartsToPart (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) (P : Finpartition (Finset.univ : Finset V))
    (C : Finset V) : Finset (V × V) :=
  (dartsFrom G B).filter fun p ↦
    P.part p.2 = C

@[simp] lemma mem_dartsToPart {G : SimpleGraph V} [DecidableRel G.Adj]
    {B : Finset V} {P : Finpartition (Finset.univ : Finset V)}
    {C : Finset V} {p : V × V} :
    p ∈ dartsToPart G B P C ↔
      p.1 ∈ B ∧ G.Adj p.1 p.2 ∧
        P.part p.2 = C := by
  simp [dartsToPart, and_assoc]

lemma exists_part_with_many_darts
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) (P : Finpartition (Finset.univ : Finset V))
    (hP : P.parts.Nonempty) :
    ∃ C ∈ P.parts,
      (dartsFrom G B).card ≤ P.parts.card * (dartsToPart G B P C).card := by
  classical
  let weight : Finset V → ℕ := fun C ↦ (dartsToPart G B P C).card
  obtain ⟨C, hCP, hCmax⟩ := Finset.exists_max_image P.parts weight hP
  refine ⟨C, hCP, ?_⟩
  have hsum : (dartsFrom G B).card =
      ∑ C ∈ P.parts, (dartsToPart G B P C).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (s := dartsFrom G B) (t := P.parts)
      (f := fun p ↦ P.part p.2)]
    · rfl
    · intro p hp
      exact P.part_mem.mpr (Finset.mem_univ _)
  rw [hsum]
  calc
    ∑ D ∈ P.parts, (dartsToPart G B P D).card ≤
        ∑ _D ∈ P.parts, weight C := by
      apply Finset.sum_le_sum
      intro D hDP
      exact hCmax D hDP
    _ = P.parts.card * (dartsToPart G B P C).card := by simp [weight]

/-- Darts from `B` whose other endpoint lies in a part `C` inject into the
oriented edges of the induced graph on `B ∪ C`. -/
lemma card_dartsToPart_le_twice_induced_edges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) (P : Finpartition (Finset.univ : Finset V))
    {C : Finset V} (hCP : C ∈ P.parts) :
    (dartsToPart G B P C).card ≤
      2 * (G.induce (↑(B ∪ C) : Set V)).edgeFinset.card := by
  classical
  let S := B ∪ C
  let A := G.induce (↑S : Set V)
  let D := dartsToPart G B P C
  let target := (Finset.univ : Finset (S × S)).filter fun p ↦ A.Adj p.1 p.2
  let f : ↑D → S × S := fun p ↦
    (⟨p.1.1, Finset.mem_union_left C (mem_dartsToPart.mp p.2).1⟩,
      ⟨p.1.2, Finset.mem_union_right B (by
        have hpart := P.mem_part (Finset.mem_univ p.1.2)
        rw [(mem_dartsToPart.mp p.2).2.2] at hpart
        exact hpart)⟩)
  have hfmem : ∀ p, f p ∈ target := by
    intro p
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (mem_dartsToPart.mp p.2).2.1
  have hfinj : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z ↦ z.1.1) hpq
    · exact congrArg (fun z ↦ z.2.1) hpq
  have hcard : D.card ≤ target.card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective
      (fun p ↦ ⟨f p, hfmem p⟩) (fun p q h ↦ hfinj (congrArg Subtype.val h))
  calc
    D.card ≤ target.card := hcard
    _ = 2 * A.edgeFinset.card := by
      simpa [target] using A.two_mul_card_edgeFinset.symm
    _ = 2 * (G.induce (↑(B ∪ C) : Set V)).edgeFinset.card := rfl

def incidentEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) : Finset (Sym2 V) :=
  B.biUnion fun v ↦ G.incidenceFinset v

lemma card_incidentEdges_le_sum_degrees
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) :
    (incidentEdges G B).card ≤ ∑ v ∈ B, G.degree v := by
  classical
  calc
    (incidentEdges G B).card ≤ ∑ v ∈ B, (G.incidenceFinset v).card := by
      exact Finset.card_biUnion_le
    _ = ∑ v ∈ B, G.degree v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact G.card_incidenceFinset_eq_degree v

def outsideEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset \ incidentEdges G B

lemma outsideEdges_subset_edgeFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) :
    outsideEdges G B ⊆ G.edgeFinset := Finset.sdiff_subset

lemma card_edgeFinset_le_outside_add_sum_degrees
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) :
    G.edgeFinset.card ≤ (outsideEdges G B).card + ∑ v ∈ B, G.degree v := by
  have hsplit := Finset.card_sdiff_add_card_inter G.edgeFinset (incidentEdges G B)
  calc
    G.edgeFinset.card = (outsideEdges G B).card +
        (G.edgeFinset ∩ incidentEdges G B).card := hsplit.symm
    _ ≤ (outsideEdges G B).card + (incidentEdges G B).card := by
      gcongr
      exact (Finset.inter_subset_right :
        G.edgeFinset ∩ incidentEdges G B ⊆ incidentEdges G B)
    _ ≤ (outsideEdges G B).card + ∑ v ∈ B, G.degree v := by
      gcongr
      exact card_incidentEdges_le_sum_degrees G B

lemma endpoint_not_mem_of_edge_outside
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V)
    {e : Sym2 V} (he : e ∈ outsideEdges G B) {v : V} (hv : v ∈ e) :
    v ∉ B := by
  intro hvB
  have heinc : e ∈ incidentEdges G B := by
    rw [incidentEdges, Finset.mem_biUnion]
    refine ⟨v, hvB, ?_⟩
    rw [G.mem_incidenceFinset]
    exact ⟨(by simpa using outsideEdges_subset_edgeFinset G B he), hv⟩
  exact (Finset.mem_sdiff.mp he).2 heinc

lemma incidenceFinset_graphOfEdges_inter
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {D E : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) (hED : E ⊆ D)
    (v : V) :
    E ∩ (graphOfEdges D).incidenceFinset v =
      (graphOfEdges E).incidenceFinset v := by
  have hE : E ⊆ G.edgeFinset := hED.trans hD
  rw [(graphOfEdges D).incidenceFinset_eq_filter,
    (graphOfEdges E).incidenceFinset_eq_filter,
    edgeFinset_graphOfEdges_of_subset hD,
    edgeFinset_graphOfEdges_of_subset hE]
  ext e
  simp only [Finset.mem_inter, Finset.mem_filter]
  tauto

/-- The number of selected edges incident with a vertex.  We use this
set-theoretic form while maximizing a degree-capped edge set. -/
def selectedDegree (E : Finset (Sym2 V)) (v : V) : ℕ :=
  (E.filter fun e ↦ v ∈ e).card

lemma selectedDegree_eq_graph_degree
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {E : Finset (Sym2 V)} (hE : E ⊆ G.edgeFinset) (v : V) :
    selectedDegree E v = (graphOfEdges E).degree v := by
  rw [← (graphOfEdges E).card_incidenceFinset_eq_degree,
    (graphOfEdges E).incidenceFinset_eq_filter,
    edgeFinset_graphOfEdges_of_subset hE]
  rfl

lemma selectedDegree_insert_of_mem
    {E : Finset (Sym2 V)} {e : Sym2 V} (he : e ∉ E)
    {v : V} (hv : v ∈ e) :
    selectedDegree (insert e E) v = selectedDegree E v + 1 := by
  simp [selectedDegree, Finset.filter_insert, hv, he]

lemma selectedDegree_insert_of_not_mem
    {E : Finset (Sym2 V)} {e : Sym2 V} (he : e ∉ E)
    {v : V} (hv : v ∉ e) :
    selectedDegree (insert e E) v = selectedDegree E v := by
  simp [selectedDegree, Finset.filter_insert, hv, he]

/-- Edge sets whose degrees are everywhere at most `D`. -/
def DegreeCapped (D : ℕ) (E : Finset (Sym2 V)) : Prop :=
  ∀ v, selectedDegree E v ≤ D

lemma degreeCapped_empty (D : ℕ) : DegreeCapped (V := V) D ∅ := by
  intro v
  simp [DegreeCapped, selectedDegree]

/-- A maximum-cardinality degree-capped edge set is inclusion-maximal: every
omitted edge has a saturated endpoint. -/
theorem exists_maximal_degreeCapped
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) :
    ∃ E : Finset (Sym2 V),
      E ⊆ G.edgeFinset ∧
      DegreeCapped D E ∧
      ∀ e ∈ G.edgeFinset, e ∉ E →
        ∃ v ∈ e, D ≤ selectedDegree E v := by
  classical
  let good := G.edgeFinset.powerset.filter fun E ↦ DegreeCapped D E
  have hgood : good.Nonempty := ⟨∅, by simp [good, degreeCapped_empty]⟩
  obtain ⟨E, hEgood, hEmax⟩ :=
    Finset.exists_max_image good Finset.card hgood
  have hEsub : E ⊆ G.edgeFinset :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hEgood).1
  have hEcap : DegreeCapped D E := (Finset.mem_filter.mp hEgood).2
  refine ⟨E, hEsub, hEcap, ?_⟩
  intro e heG heE
  by_contra hsat
  push_neg at hsat
  have hinsertCap : DegreeCapped D (insert e E) := by
    intro v
    by_cases hv : v ∈ e
    · rw [selectedDegree_insert_of_mem heE hv]
      have := hsat v hv
      omega
    · rw [selectedDegree_insert_of_not_mem heE hv]
      exact hEcap v
  have hinsertGood : insert e E ∈ good := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mpr ?_, hinsertCap⟩
    intro f hf
    rw [Finset.mem_insert] at hf
    rcases hf with rfl | hf
    · exact heG
    · exact hEsub hf
  have hle := hEmax (insert e E) hinsertGood
  rw [Finset.card_insert_of_notMem heE] at hle
  omega

def saturatedVertices (D : ℕ) (E : Finset (Sym2 V)) : Finset V :=
  Finset.univ.filter fun v ↦ D ≤ selectedDegree E v

@[simp] lemma mem_saturatedVertices {D : ℕ} {E : Finset (Sym2 V)} {v : V} :
    v ∈ saturatedVertices D E ↔ D ≤ selectedDegree E v := by
  simp [saturatedVertices]

lemma edgeFinset_subset_selected_union_incidentSaturated
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : ℕ} {E : Finset (Sym2 V)}
    (hEsub : E ⊆ G.edgeFinset)
    (hmax : ∀ e ∈ G.edgeFinset, e ∉ E →
      ∃ v ∈ e, D ≤ selectedDegree E v) :
    G.edgeFinset ⊆ E ∪ incidentEdges G (saturatedVertices D E) := by
  intro e heG
  by_cases heE : e ∈ E
  · exact Finset.mem_union_left _ heE
  · obtain ⟨v, hve, hvsat⟩ := hmax e heG heE
    apply Finset.mem_union_right
    rw [incidentEdges, Finset.mem_biUnion]
    refine ⟨v, mem_saturatedVertices.mpr hvsat, ?_⟩
    rw [G.mem_incidenceFinset]
    exact ⟨(by simpa using heG), hve⟩

lemma saturated_mul_cap_le_twice_selected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : ℕ} {E : Finset (Sym2 V)} (hEsub : E ⊆ G.edgeFinset) :
    (saturatedVertices D E).card * D ≤ 2 * E.card := by
  classical
  calc
    (saturatedVertices D E).card * D =
        ∑ _v ∈ saturatedVertices D E, D := by simp
    _ ≤ ∑ v ∈ saturatedVertices D E, selectedDegree E v := by
      apply Finset.sum_le_sum
      intro v hv
      exact mem_saturatedVertices.mp hv
    _ ≤ ∑ v : V, selectedDegree E v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro v hvU hvS
      omega
    _ = ∑ v : V, (graphOfEdges E).degree v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact selectedDegree_eq_graph_degree hEsub v
    _ = 2 * (graphOfEdges E).edgeFinset.card :=
      (graphOfEdges E).sum_degrees_eq_twice_card_edges
    _ = 2 * E.card := by rw [edgeFinset_graphOfEdges_of_subset hEsub]

lemma card_edgeFinset_le_selected_add_saturated_degrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : ℕ} {E : Finset (Sym2 V)}
    (hEsub : E ⊆ G.edgeFinset)
    (hmax : ∀ e ∈ G.edgeFinset, e ∉ E →
      ∃ v ∈ e, D ≤ selectedDegree E v) :
    G.edgeFinset.card ≤ E.card +
      ∑ v ∈ saturatedVertices D E, G.degree v := by
  calc
    G.edgeFinset.card ≤
        (E ∪ incidentEdges G (saturatedVertices D E)).card :=
      Finset.card_le_card
        (edgeFinset_subset_selected_union_incidentSaturated G hEsub hmax)
    _ ≤ E.card + (incidentEdges G (saturatedVertices D E)).card :=
      Finset.card_union_le _ _
    _ ≤ E.card + ∑ v ∈ saturatedVertices D E, G.degree v := by
      gcongr
      exact card_incidentEdges_le_sum_degrees G _

lemma degree_mul_card_le_of_almost_regular
    (G : SimpleGraph V) [DecidableRel G.Adj] {K : ℕ}
    (hreg : ∀ x y, G.degree x ≤ K * G.degree y) (x : V) :
    Fintype.card V * G.degree x ≤ 2 * K * G.edgeFinset.card := by
  calc
    Fintype.card V * G.degree x = ∑ _y : V, G.degree x := by simp
    _ ≤ ∑ y : V, K * G.degree y := by
      apply Finset.sum_le_sum
      intro y hy
      exact hreg x y
    _ = K * ∑ y : V, G.degree y := by rw [Finset.mul_sum]
    _ = K * (2 * G.edgeFinset.card) := by
      rw [G.sum_degrees_eq_twice_card_edges]
    _ = 2 * K * G.edgeFinset.card := by ring

lemma card_mul_sum_degrees_le_of_almost_regular
    (G : SimpleGraph V) [DecidableRel G.Adj] {K : ℕ}
    (hreg : ∀ x y, G.degree x ≤ K * G.degree y) (S : Finset V) :
    Fintype.card V * (∑ v ∈ S, G.degree v) ≤
      S.card * (2 * K * G.edgeFinset.card) := by
  calc
    Fintype.card V * (∑ v ∈ S, G.degree v) =
        ∑ v ∈ S, Fintype.card V * G.degree v := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _v ∈ S, 2 * K * G.edgeFinset.card := by
      apply Finset.sum_le_sum
      intro v hv
      exact degree_mul_card_le_of_almost_regular G hreg v
    _ = S.card * (2 * K * G.edgeFinset.card) := by simp

/-- Deterministic bounded-degree sparsification.  The constants are chosen so
that the maximal capped set cannot have fewer than `t` edges: otherwise its
saturated vertices cover the omitted edges, but their total incidence is too
small. -/
theorem exists_dense_degreeCapped_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K D t : ℕ) (hK : 0 < K) (ht : 0 < t)
    (hedges : 4 * t ≤ G.edgeFinset.card)
    (hcap : 8 * K * t ≤ D * Fintype.card V)
    (hreg : ∀ x y, G.degree x ≤ K * G.degree y) :
    ∃ E : Finset (Sym2 V),
      E ⊆ G.edgeFinset ∧
      t ≤ E.card ∧
      ∀ v, (graphOfEdges E).degree v ≤ D := by
  classical
  obtain ⟨E, hEsub, hEcap, hEmax⟩ := exists_maximal_degreeCapped G D
  refine ⟨E, hEsub, ?_, ?_⟩
  · by_contra hEt
    have hElt : E.card < t := Nat.lt_of_not_ge hEt
    let S := saturatedVertices D E
    have hcover := card_edgeFinset_le_selected_add_saturated_degrees
      G hEsub hEmax
    have hsat := saturated_mul_cap_le_twice_selected G
      (D := D) (E := E) hEsub
    have hsum := card_mul_sum_degrees_le_of_almost_regular G hreg S
    have hDmul :
        D * Fintype.card V * (∑ v ∈ S, G.degree v) ≤
          4 * K * E.card * G.edgeFinset.card := by
      calc
        D * Fintype.card V * (∑ v ∈ S, G.degree v) =
            D * (Fintype.card V * (∑ v ∈ S, G.degree v)) := by ring
        _ ≤ D * (S.card * (2 * K * G.edgeFinset.card)) := by gcongr
        _ = (S.card * D) * (2 * K * G.edgeFinset.card) := by ring
        _ ≤ (2 * E.card) * (2 * K * G.edgeFinset.card) := by gcongr
        _ = 4 * K * E.card * G.edgeFinset.card := by ring
    have hcoverMul :
        D * Fintype.card V * G.edgeFinset.card ≤
          D * Fintype.card V * E.card +
            4 * K * E.card * G.edgeFinset.card := by
      calc
        D * Fintype.card V * G.edgeFinset.card ≤
            D * Fintype.card V *
              (E.card + ∑ v ∈ S, G.degree v) := by gcongr
        _ = D * Fintype.card V * E.card +
            D * Fintype.card V * (∑ v ∈ S, G.degree v) := by ring
        _ ≤ D * Fintype.card V * E.card +
            4 * K * E.card * G.edgeFinset.card := by gcongr
    have hDmpos : 0 < D * Fintype.card V := by
      have : 0 < 8 * K * t := by positivity
      exact this.trans_le hcap
    have hepos : 0 < G.edgeFinset.card := by
      exact (by positivity : 0 < 4 * t).trans_le hedges
    have hupper :
        D * Fintype.card V * G.edgeFinset.card ≤
          D * Fintype.card V * t + 4 * K * t * G.edgeFinset.card := by
      exact hcoverMul.trans (add_le_add
        (Nat.mul_le_mul_left (D * Fintype.card V) hElt.le)
        (Nat.mul_le_mul_right G.edgeFinset.card
          (Nat.mul_le_mul_left (4 * K) hElt.le)))
    have hquarter :
        4 * (D * Fintype.card V * t) ≤
          D * Fintype.card V * G.edgeFinset.card := by
      calc
        4 * (D * Fintype.card V * t) =
            D * Fintype.card V * (4 * t) := by ring
        _ ≤ D * Fintype.card V * G.edgeFinset.card := by gcongr
    have hhalf :
        2 * (4 * K * t * G.edgeFinset.card) ≤
          D * Fintype.card V * G.edgeFinset.card := by
      calc
        2 * (4 * K * t * G.edgeFinset.card) =
            (8 * K * t) * G.edgeFinset.card := by ring
        _ ≤ (D * Fintype.card V) * G.edgeFinset.card := by gcongr
        _ = D * Fintype.card V * G.edgeFinset.card := by ring
    have hfourUpper := Nat.mul_le_mul_left 4 hupper
    have hthree :
        4 * (D * Fintype.card V * t +
            4 * K * t * G.edgeFinset.card) ≤
          3 * (D * Fintype.card V * G.edgeFinset.card) := by
      nlinarith
    have hbad :
        4 * (D * Fintype.card V * G.edgeFinset.card) ≤
          3 * (D * Fintype.card V * G.edgeFinset.card) :=
      hfourUpper.trans hthree
    have : 0 < D * Fintype.card V * G.edgeFinset.card := by positivity
    omega
  · intro v
    rw [← selectedDegree_eq_graph_degree hEsub v]
    exact hEcap v

def blockCount : ℕ := 2 ^ (100 : ℕ)

def shrinkFactor : ℕ := blockCount / 4

def edgeLossFactor : ℕ := 4 * blockCount

def regularFactor : ℕ := 32 * blockCount

lemma blockCount_pos : 0 < blockCount := by
  norm_num [blockCount]

lemma blockCount_two_le : 2 ≤ blockCount := by
  norm_num [blockCount]

lemma shrinkFactor_two_le : 2 ≤ shrinkFactor := by
  norm_num [shrinkFactor, blockCount]

lemma edgeLoss_power_le_shrink_power :
    edgeLossFactor ^ 21 ≤ shrinkFactor ^ 22 := by
  norm_num [edgeLossFactor, shrinkFactor, blockCount, pow_succ]

lemma edgeLoss_density_power_le :
    edgeLossFactor ^ 21 ≤ shrinkFactor ^ 31 := by
  exact edgeLoss_power_le_shrink_power.trans (by
    have hs : 1 ≤ shrinkFactor := le_trans (by omega) shrinkFactor_two_le
    have h := pow_le_pow_right₀ hs
      (by omega : 22 ≤ 31)
    simpa using h)

lemma linear_density_of_large {n e : ℕ}
    (hn : blockCount ≤ n) (hdense : n ^ 31 < e ^ 21) :
    32 * n ≤ e := by
  by_contra! he
  have hep : e ^ 21 ≤ (32 * n) ^ 21 := pow_le_pow_left' he.le 21
  have hpow : n ^ 21 * n ^ 10 < 32 ^ 21 * n ^ 21 := by
    simpa [← pow_add, mul_pow, mul_comm] using hdense.trans_le hep
  have hnpos : 0 < n := blockCount_pos.trans_le hn
  have hsmall : n ^ 10 < 32 ^ 21 := by
    have hp : 0 < n ^ 21 := pow_pos hnpos 21
    apply (Nat.mul_lt_mul_left hp).mp
    simpa [mul_comm] using hpow
  have hlarge : blockCount ^ 10 ≤ n ^ 10 := pow_le_pow_left' hn 10
  have : blockCount ^ 10 < 32 ^ 21 := hlarge.trans_lt hsmall
  norm_num [blockCount, pow_succ] at this

lemma quotientBlock_pos (n : ℕ) : 0 < n / blockCount + 1 := by
  exact Nat.zero_lt_succ _

lemma quotientBlock_le_card {n : ℕ} (hn : blockCount ≤ n) :
    n / blockCount + 1 ≤ n := by
  have htwo := blockCount_two_le
  have hdiv : n / blockCount ≤ n / 2 :=
    Nat.div_le_div_left htwo (by omega)
  have hn2 : n / 2 + 1 ≤ n := by
    have : 2 ≤ n := htwo.trans hn
    omega
  omega

lemma card_le_blockCount_mul_quotientBlock (n : ℕ) :
    n ≤ blockCount * (n / blockCount + 1) :=
  (Nat.lt_mul_div_succ n blockCount_pos).le

lemma blockCount_mul_quotientBlock_le_twice {n : ℕ}
    (hn : blockCount ≤ n) :
    blockCount * (n / blockCount + 1) ≤ 2 * n := by
  have hdiv := Nat.div_mul_le_self n blockCount
  have : n / blockCount * blockCount + blockCount ≤ n + n :=
    Nat.add_le_add hdiv hn
  calc
    blockCount * (n / blockCount + 1) =
        n / blockCount * blockCount + blockCount := by ring
    _ ≤ n + n := this
    _ = 2 * n := by omega

lemma shrink_union_bound {n b c : ℕ} (hn : blockCount ≤ n)
    (hb : b ≤ n / blockCount + 1) (hc : c ≤ n / blockCount + 1) :
    shrinkFactor * (b + c) ≤ n := by
  have hMdiv : blockCount = 4 * shrinkFactor := by
    norm_num [blockCount, shrinkFactor]
  have hsum : b + c ≤ 2 * (n / blockCount + 1) := by omega
  have hbase := blockCount_mul_quotientBlock_le_twice hn
  have hhalf : 2 * shrinkFactor * (n / blockCount + 1) ≤ n := by
    apply Nat.le_of_mul_le_mul_left (c := 2) _ (by omega)
    calc
      2 * (2 * shrinkFactor * (n / blockCount + 1)) =
          blockCount * (n / blockCount + 1) := by rw [hMdiv]; ring
      _ ≤ 2 * n := hbase
  exact (Nat.mul_le_mul_left shrinkFactor hsum).trans (by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hhalf)

lemma rpow_density_of_power_density {m e : ℕ}
    (h : m ^ 31 < (4 * e) ^ 21) :
    (m : ℝ) ^ ((31 : ℝ) / 21) < 4 * e := by
  have hcast : (m : ℝ) ^ (31 : ℕ) < (4 * (e : ℝ)) ^ (21 : ℕ) := by
    exact_mod_cast h
  have hroot := Real.rpow_lt_rpow (by positivity :
      0 ≤ (m : ℝ) ^ (31 : ℕ)) hcast (by norm_num : (0 : ℝ) < 1 / 21)
  calc
    (m : ℝ) ^ ((31 : ℝ) / 21) =
        ((m : ℝ) ^ (31 : ℕ)) ^ ((1 : ℝ) / 21) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m)]
      norm_num
    _ < ((4 * (e : ℝ)) ^ (21 : ℕ)) ^ ((1 : ℝ) / 21) := hroot
    _ = 4 * e := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity :
        (0 : ℝ) ≤ 4 * e)]
      norm_num

lemma power_density_of_rpow_density {n e : ℕ}
    (h : (n : ℝ) ^ ((31 : ℝ) / 21) < e) :
    n ^ 31 < e ^ 21 := by
  have hp := Real.rpow_lt_rpow
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    h (by norm_num : (0 : ℝ) < 21)
  have hreal : ((n ^ 31 : ℕ) : ℝ) < ((e ^ 21 : ℕ) : ℝ) := by
    calc
      ((n ^ 31 : ℕ) : ℝ) =
          ((n : ℝ) ^ ((31 : ℝ) / 21)) ^ (21 : ℝ) := by
        push_cast
        rw [← Real.rpow_mul (Nat.cast_nonneg n)]
        norm_num
      _ < (e : ℝ) ^ (21 : ℝ) := hp
      _ = ((e ^ 21 : ℕ) : ℝ) := by
        norm_num [Real.rpow_natCast]
  exact_mod_cast hreal

noncomputable def densityTarget (m : ℕ) : ℕ :=
  ⌈(m : ℝ) ^ ((31 : ℝ) / 21) / 64⌉₊

noncomputable def degreeCapTarget (K m : ℕ) : ℕ :=
  ⌈(8 * K * densityTarget m : ℕ) / (m : ℝ)⌉₊

lemma densityTarget_pos {m : ℕ} (hm : 0 < m) : 0 < densityTarget m := by
  rw [densityTarget, Nat.ceil_pos]
  positivity

lemma densityTarget_cast_lt {m : ℕ} (hm : 64 ≤ m) :
    (densityTarget m : ℝ) <
      (m : ℝ) ^ ((31 : ℝ) / 21) / 32 := by
  let x : ℝ := (m : ℝ) ^ ((31 : ℝ) / 21)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hexp : (1 : ℝ) ≤ (31 : ℝ) / 21 := by norm_num
  have hx64 : (64 : ℝ) ≤ x := by
    calc
      (64 : ℝ) ≤ m := by exact_mod_cast hm
      _ ≤ x := Real.self_le_rpow_of_one_le hm1 hexp
  calc
    (densityTarget m : ℝ) < x / 64 + 1 := by
      simpa [densityTarget, x] using
        (Nat.ceil_lt_add_one (show 0 ≤
          (m : ℝ) ^ ((31 : ℝ) / 21) / 64 by positivity))
    _ ≤ x / 32 := by nlinarith

lemma four_mul_densityTarget_le {m e : ℕ} (hm : 64 ≤ m)
    (hdense : m ^ 31 < (4 * e) ^ 21) :
    4 * densityTarget m ≤ e := by
  let x : ℝ := (m : ℝ) ^ ((31 : ℝ) / 21)
  have htlt : (densityTarget m : ℝ) < x / 32 := by
    simpa [x] using densityTarget_cast_lt hm
  have hxe : x < 4 * (e : ℝ) := by
    simpa [x] using rpow_density_of_power_density hdense
  have hreal : (4 * densityTarget m : ℕ) < (e : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast hreal.le

lemma degreeCapTarget_mul_card {K m : ℕ} (hm : 0 < m) :
    8 * K * densityTarget m ≤ degreeCapTarget K m * m := by
  have hceil : ((8 * K * densityTarget m : ℕ) : ℝ) / m ≤
      (degreeCapTarget K m : ℝ) := by
    exact Nat.le_ceil _
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hreal : ((8 * K * densityTarget m : ℕ) : ℝ) ≤
      (degreeCapTarget K m : ℝ) * m := by
    calc
      ((8 * K * densityTarget m : ℕ) : ℝ) =
          (((8 * K * densityTarget m : ℕ) : ℝ) / m) * m := by field_simp
      _ ≤ (degreeCapTarget K m : ℝ) * m := by gcongr
  exact_mod_cast hreal

lemma degreeCapTarget_cast_lt (K m : ℕ) (hm : 64 ≤ m) :
    (degreeCapTarget K m : ℝ) <
      ((K : ℝ) + 1) * (m : ℝ) ^ ((10 : ℝ) / 21) := by
  let x : ℝ := (m : ℝ) ^ ((31 : ℝ) / 21)
  let z : ℝ := (m : ℝ) ^ ((10 : ℝ) / 21)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hz1 : (1 : ℝ) ≤ z := by
    exact Real.one_le_rpow hm1 (by norm_num)
  have htz : (densityTarget m : ℝ) < x / 32 := by
    simpa [x] using densityTarget_cast_lt hm
  have hxdiv : x / (m : ℝ) = z := by
    rw [← Real.rpow_sub_one hmpos.ne']
    dsimp [x, z]
    congr 1
    norm_num
  let y : ℝ := ((8 * K * densityTarget m : ℕ) : ℝ) / m
  have hyle : y ≤ (K : ℝ) / 4 * z := by
    dsimp [y]
    push_cast
    calc
      8 * (K : ℝ) * (densityTarget m : ℝ) / m ≤
          8 * (K : ℝ) * (x / 32) / m := by
        by_cases hK : K = 0
        · simp [hK]
        · have hfac : (0 : ℝ) < 8 * K := by positivity
          exact (div_lt_div_of_pos_right
            (mul_lt_mul_of_pos_left htz hfac) hmpos).le
      _ = (K : ℝ) / 4 * z := by rw [← hxdiv]; ring
  have hceil : (degreeCapTarget K m : ℝ) < y + 1 := by
    simpa [degreeCapTarget, y] using
      (Nat.ceil_lt_add_one (show 0 ≤
        ((8 * K * densityTarget m : ℕ) : ℝ) / m by positivity))
  have hK0 : (0 : ℝ) ≤ K := by positivity
  nlinarith

/-- The output package of the deterministic Erdős--Simonovits
regularization descent.  Its vertex type may change at each induced-subgraph
step, while `contained` remembers the embedding into the original host. -/
structure RegularCore {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  W : Type u
  [fintypeW : Fintype W]
  [decEqW : DecidableEq W]
  graph : SimpleGraph W
  [decAdj : DecidableRel graph.Adj]
  contained : graph ⊑ G
  edges_nonempty : graph.edgeFinset.Nonempty
  density : Fintype.card W ^ 31 < (4 * graph.edgeFinset.card) ^ 21
  almost_regular : ∀ x y, graph.degree x ≤ regularFactor * graph.degree y
  transfer : G.edgeFinset.card ^ 21 * Fintype.card W ^ 22 ≤
    (4 * graph.edgeFinset.card) ^ 21 * Fintype.card V ^ 22

def RegularCore.order
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (K : RegularCore G) : ℕ :=
  @Fintype.card K.W K.fintypeW

/-- The bounded-degree graph delivered by regularization followed by
deterministic sparsification. -/
structure SparseCore {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  W : Type u
  [fintypeW : Fintype W]
  [decEqW : DecidableEq W]
  graph : SimpleGraph W
  [decAdj : DecidableRel graph.Adj]
  contained : graph ⊑ G
  order_large : 64 ≤ Fintype.card W
  edges_nonempty : graph.edgeFinset.Nonempty
  edge_lower : (Fintype.card W : ℝ) ^ ((31 : ℝ) / 21) / 64 ≤
    (graph.edgeFinset.card : ℝ)
  degree_upper : ∀ x,
    (graph.degree x : ℝ) ≤
      (regularFactor + 1 : ℕ) *
        (Fintype.card W : ℝ) ^ ((10 : ℝ) / 21)
  host_growth : G.edgeFinset.card ^ 21 ≤
    4 ^ 21 * Fintype.card W ^ 20 * Fintype.card V ^ 22

def SparseCore.order
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (K : SparseCore G) : ℕ :=
  @Fintype.card K.W K.fintypeW

def SparseCore.maximumDegree
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (K : SparseCore G) : ℕ :=
  @SimpleGraph.maxDegree K.W K.graph K.fintypeW K.decAdj

lemma SparseCore.maxDegree_upper
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (K : SparseCore G) :
    (K.maximumDegree : ℝ) ≤
      (regularFactor + 1 : ℕ) *
        (K.order : ℝ) ^ ((10 : ℝ) / 21) := by
  letI : Fintype K.W := K.fintypeW
  letI : DecidableEq K.W := K.decEqW
  letI : DecidableRel K.graph.Adj := K.decAdj
  letI : Nonempty K.W := Fintype.card_pos_iff.mp (by
    have := K.order_large
    omega)
  obtain ⟨v, hv⟩ := K.graph.exists_maximal_degree_vertex
  rw [show K.maximumDegree = K.graph.maxDegree by rfl, hv]
  simpa [SparseCore.order] using K.degree_upper v

lemma RegularCore.host_growth
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (K : RegularCore G) (hm : 0 < K.order) :
    G.edgeFinset.card ^ 21 ≤
      4 ^ 21 * K.order ^ 20 * Fintype.card V ^ 22 := by
  letI : Fintype K.W := K.fintypeW
  letI : DecidableEq K.W := K.decEqW
  letI : DecidableRel K.graph.Adj := K.decAdj
  let m := Fintype.card K.W
  have hedge : K.graph.edgeFinset.card ≤ m ^ 2 := by
    calc
      K.graph.edgeFinset.card ≤ m.choose 2 :=
        K.graph.card_edgeFinset_le_card_choose_two
      _ = m * (m - 1) / 2 := Nat.choose_two_right m
      _ ≤ m * (m - 1) := Nat.div_le_self _ _
      _ ≤ m * m := by gcongr; omega
      _ = m ^ 2 := by ring
  have htransfer := K.transfer
  have hmul :
      G.edgeFinset.card ^ 21 * m ^ 22 ≤
        (4 ^ 21 * m ^ 20 * Fintype.card V ^ 22) * m ^ 22 := by
    calc
      G.edgeFinset.card ^ 21 * m ^ 22 ≤
          (4 * K.graph.edgeFinset.card) ^ 21 *
            Fintype.card V ^ 22 := by simpa [m] using htransfer
      _ ≤ (4 * m ^ 2) ^ 21 * Fintype.card V ^ 22 := by gcongr
      _ = (4 ^ 21 * m ^ 20 * Fintype.card V ^ 22) * m ^ 22 := by ring
  exact le_of_mul_le_mul_right hmul (pow_pos (by simpa [m, RegularCore.order] using hm) 22)

theorem RegularCore.exists_sparseCore
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (K : RegularCore G) (hm : 64 ≤ K.order) :
    Nonempty (SparseCore G) := by
  classical
  letI : Fintype K.W := K.fintypeW
  letI : DecidableEq K.W := K.decEqW
  letI : DecidableRel K.graph.Adj := K.decAdj
  let m := Fintype.card K.W
  let t := densityTarget m
  let D := degreeCapTarget regularFactor m
  have hmpos : 0 < m := by
    have : 64 ≤ m := by simpa [m, RegularCore.order] using hm
    omega
  have htpos : 0 < t := densityTarget_pos hmpos
  have hfour : 4 * t ≤ K.graph.edgeFinset.card := by
    apply four_mul_densityTarget_le (by simpa [m, RegularCore.order] using hm)
    simpa [t, m] using K.density
  have hcap : 8 * regularFactor * t ≤ D * m := by
    simpa [D, t] using
      (degreeCapTarget_mul_card (K := regularFactor) (m := m) hmpos)
  obtain ⟨E, hEsub, htE, hEdeg⟩ := exists_dense_degreeCapped_subset
    K.graph regularFactor D t (by
      dsimp [regularFactor, blockCount]
      positivity) htpos hfour hcap K.almost_regular
  let F := graphOfEdges E
  have hFedges : F.edgeFinset = E := by
    dsimp [F]
    exact edgeFinset_graphOfEdges_of_subset hEsub
  have hcontainedCore : F ⊑ K.graph :=
    SimpleGraph.IsContained.of_le (graphOfEdges_le hEsub)
  refine ⟨{
    W := K.W
    graph := F
    contained := hcontainedCore.trans K.contained
    order_large := by simpa [m, RegularCore.order] using hm
    edges_nonempty := by
      rw [hFedges]
      exact Finset.card_pos.mp (htpos.trans_le htE)
    edge_lower := ?_
    degree_upper := ?_
    host_growth := by
      simpa [m, RegularCore.order] using
        (RegularCore.host_growth K
          (by simpa [m, RegularCore.order] using hmpos)) }⟩
  · rw [hFedges]
    calc
      (Fintype.card K.W : ℝ) ^ ((31 : ℝ) / 21) / 64 ≤
          (densityTarget m : ℝ) := by
        change (Fintype.card K.W : ℝ) ^ ((31 : ℝ) / 21) / 64 ≤
          (↑⌈(Fintype.card K.W : ℝ) ^ ((31 : ℝ) / 21) / 64⌉₊ : ℝ)
        exact Nat.le_ceil _
      _ ≤ (E.card : ℝ) := by exact_mod_cast htE
  · intro x
    have hxD : (F.degree x : ℝ) ≤ D := by
      exact_mod_cast hEdeg x
    have hDupper := degreeCapTarget_cast_lt regularFactor m
      (by simpa [m, RegularCore.order] using hm)
    exact hxD.trans (by
      simpa [D, m] using hDupper.le)

theorem regularCore_of_small
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hsmall : Fintype.card V < blockCount)
    (hdense : Fintype.card V ^ 31 < G.edgeFinset.card ^ 21) :
    Nonempty (RegularCore G) := by
  classical
  let A := G.induce G.support
  have hedge : G.edgeFinset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    rw [hzero] at hdense
    simp at hdense
  have hAedge : A.edgeFinset.card = G.edgeFinset.card := by
    exact G.card_edgeFinset_induce_support
  have hWle : Fintype.card G.support ≤ Fintype.card V := Fintype.card_subtype_le _
  have hreg : ∀ x y, A.degree x ≤ regularFactor * A.degree y := by
    intro x y
    change (G.induce G.support).degree x ≤
      regularFactor * (G.induce G.support).degree y
    rw [G.degree_induce_support, G.degree_induce_support]
    have hx : G.degree x.1 < Fintype.card V := G.degree_lt_card_verts x.1
    have hy : 0 < G.degree y.1 := by
      rw [SimpleGraph.degree_pos_iff_mem_support]
      exact y.2
    have hfactor : Fintype.card V ≤ regularFactor := by
      dsimp [regularFactor]
      omega
    nlinarith
  exact ⟨{
    W := G.support
    graph := A
    contained := ⟨(SimpleGraph.Embedding.induce G.support).toCopy⟩
    edges_nonempty := by
      apply Finset.card_pos.mp
      rw [hAedge]
      exact Finset.card_pos.mpr hedge
    density := by
      rw [hAedge]
      exact (pow_le_pow_left' hWle 31).trans_lt
        (hdense.trans_le (pow_le_pow_left' (by omega) 21))
    almost_regular := hreg
    transfer := by
      rw [hAedge]
      calc
        G.edgeFinset.card ^ 21 * Fintype.card G.support ^ 22 ≤
            G.edgeFinset.card ^ 21 * Fintype.card V ^ 22 := by
          gcongr
        _ ≤ (4 * G.edgeFinset.card) ^ 21 * Fintype.card V ^ 22 := by
          gcongr
          omega }⟩

noncomputable def edgeSupportGraph (E : Finset (Sym2 V)) :
    SimpleGraph (graphOfEdges E).support :=
  (graphOfEdges E).induce (graphOfEdges E).support

noncomputable instance edgeSupportGraph_decidableRel (E : Finset (Sym2 V)) :
    DecidableRel (edgeSupportGraph E).Adj := Classical.decRel _

theorem regularCore_of_top_sparse
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V)
    (hlarge : blockCount ≤ Fintype.card V)
    (hdense : Fintype.card V ^ 31 < G.edgeFinset.card ^ 21)
    (hBcard : B.card = Fintype.card V / blockCount + 1)
    (htop : ∀ x ∉ B, B.card * G.degree x ≤ ∑ y ∈ B, G.degree y)
    (hsparse : 2 * (∑ y ∈ B, G.degree y) ≤ G.edgeFinset.card) :
    Nonempty (RegularCore G) := by
  classical
  let n := Fintype.card V
  let e := G.edgeFinset.card
  let D := outsideEdges G B
  let H := graphOfEdges D
  let t := e / (16 * n)
  have hnpos : 0 < n := blockCount_pos.trans_le hlarge
  have helinear : 32 * n ≤ e := linear_density_of_large hlarge hdense
  have hepos : 0 < e := by omega
  have htpos : 0 < t := by
    dsimp [t]
    apply Nat.div_pos
    · omega
    · positivity
  have hDsub : D ⊆ G.edgeFinset := outsideEdges_subset_edgeFinset G B
  have heD : e ≤ 2 * D.card := by
    have hsplit := card_edgeFinset_le_outside_add_sum_degrees G B
    dsimp [e, D] at hsplit ⊢
    omega
  obtain ⟨E, hED, hcard, hstable⟩ :=
    exists_pruned_indexed D (Finset.univ : Finset V)
      (fun v ↦ H.incidenceFinset v) (fun _ ↦ t)
  have hcost : ∑ _v : V, (t - 1) ≤ e / 16 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      n * (t - 1) ≤ n * t := by gcongr; omega
      _ ≤ e / 16 := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < 16)]
        dsimp [t]
        calc
          n * (e / (16 * n)) * 16 = e / (16 * n) * (16 * n) := by ring
          _ ≤ e := Nat.div_mul_le_self _ _
  have heE : e ≤ 4 * E.card := by
    have hcard' : D.card ≤ E.card + e / 16 := hcard.trans (by
      simpa using Nat.add_le_add_left hcost E.card)
    have heighth : 8 * (e / 16) ≤ e := by
      calc
        8 * (e / 16) ≤ 8 * (e / 8) :=
          Nat.mul_le_mul_left 8 (Nat.div_le_div_left (a := e) (by omega) (by omega))
        _ ≤ e := Nat.mul_div_le _ _
    omega
  have hEne : E.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    rw [hzero] at heE
    simp at heE
    omega
  have hEsubG : E ⊆ G.edgeFinset := hED.trans hDsub
  let A₀ := graphOfEdges E
  let A := edgeSupportGraph E
  have hAedge : A.edgeFinset.card = E.card := by
    calc
      A.edgeFinset.card = A₀.edgeFinset.card := by
        exact A₀.card_edgeFinset_induce_support
      _ = E.card := by
        exact congrArg Finset.card (edgeFinset_graphOfEdges_of_subset hEsubG)
  have hdegree (v : A₀.support) : A.degree v = A₀.degree v.1 := by
    exact A₀.degree_induce_support v
  have hmin (v : A₀.support) : t ≤ A.degree v := by
    have hvpos : 0 < A₀.degree v.1 := by
      rw [SimpleGraph.degree_pos_iff_mem_support]
      exact v.2
    have hincne : (E ∩ H.incidenceFinset v.1).Nonempty := by
      rw [show E ∩ H.incidenceFinset v.1 = A₀.incidenceFinset v.1 by
        exact incidenceFinset_graphOfEdges_inter hDsub hED v.1]
      rw [← Finset.card_pos, A₀.card_incidenceFinset_eq_degree]
      exact hvpos
    have hs := hstable v.1 (Finset.mem_univ _) hincne
    rw [show E ∩ H.incidenceFinset v.1 = A₀.incidenceFinset v.1 by
      exact incidenceFinset_graphOfEdges_inter hDsub hED v.1,
      A₀.card_incidenceFinset_eq_degree] at hs
    simpa [hdegree v] using hs
  have hmax (v : A₀.support) : A.degree v ≤ regularFactor * t := by
    have hvnot : v.1 ∉ B := by
      have hvpos : 0 < A₀.degree v.1 := by
        rw [SimpleGraph.degree_pos_iff_mem_support]
        exact v.2
      obtain ⟨w, hvw⟩ := (A₀.degree_pos_iff_exists_adj v.1).mp hvpos
      have hedge : s(v.1, w) ∈ E := (graphOfEdges_adj_iff.mp hvw).1
      exact endpoint_not_mem_of_edge_outside G B (hED hedge)
        (by simp)
    have hdegmono : A₀.degree v.1 ≤ G.degree v.1 :=
      SimpleGraph.degree_le_of_le (v := v.1) (graphOfEdges_le hEsubG)
    have htopv := htop v.1 hvnot
    have hsum : ∑ y ∈ B, G.degree y ≤ e := by
      dsimp [e]
      omega
    have hbpos : 0 < B.card := by rw [hBcard]; exact quotientBlock_pos n
    have hnb : n ≤ blockCount * B.card := by
      rw [hBcard]
      exact card_le_blockCount_mul_quotientBlock n
    have heupper : e < 32 * n * t := by
      have hdiv := Nat.lt_mul_div_succ e (by positivity : 0 < 16 * n)
      have htge : 2 ≤ t := by
        dsimp [t]
        rw [Nat.le_div_iff_mul_le (by positivity : 0 < 16 * n)]
        nlinarith
      dsimp [t] at hdiv ⊢
      nlinarith
    have hbd : B.card * A.degree v ≤ e := by
      rw [hdegree]
      exact (Nat.mul_le_mul_left B.card hdegmono).trans (htopv.trans hsum)
    have hrf : regularFactor = 32 * blockCount := rfl
    rw [hrf]
    apply Nat.le_of_mul_le_mul_left (c := B.card) _ hbpos
    calc
      B.card * A.degree v ≤ e := hbd
      _ ≤ 32 * n * t := heupper.le
      _ ≤ B.card * (32 * blockCount * t) := by
        nlinarith
  exact ⟨{
    W := A₀.support
    graph := A
    contained := by
      have hAA₀ : A ⊑ A₀ := by
        simpa [A, A₀, edgeSupportGraph] using
          (show (A₀.induce A₀.support) ⊑ A₀ from
            ⟨(SimpleGraph.Embedding.induce A₀.support).toCopy⟩)
      exact hAA₀.trans_le (graphOfEdges_le hEsubG)
    edges_nonempty := by
      apply Finset.card_pos.mp
      rw [hAedge]
      exact Finset.card_pos.mpr hEne
    density := by
      have hWle : Fintype.card A₀.support ≤ n := Fintype.card_subtype_le _
      rw [hAedge]
      exact (pow_le_pow_left' hWle 31).trans_lt
        (hdense.trans_le (pow_le_pow_left' heE 21))
    almost_regular := fun x y ↦ (hmax x).trans
      (Nat.mul_le_mul_left regularFactor (hmin y))
    transfer := by
      have hWle : Fintype.card A₀.support ≤ n := Fintype.card_subtype_le _
      rw [hAedge]
      calc
        e ^ 21 * Fintype.card A₀.support ^ 22 ≤ e ^ 21 * n ^ 22 := by
          gcongr
        _ ≤ (4 * E.card) ^ 21 * n ^ 22 := by gcongr }⟩

/-- The dense alternative of the top-block dichotomy.  It finds a much
smaller induced graph, loses at most `edgeLossFactor` in edge count, and
preserves the `31/21` density inequality. -/
theorem exists_dense_induced_step
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V)
    (hlarge : blockCount ≤ Fintype.card V)
    (hdense : Fintype.card V ^ 31 < G.edgeFinset.card ^ 21)
    (hBcard : B.card = Fintype.card V / blockCount + 1)
    (hdenseTop : G.edgeFinset.card < 2 * (∑ y ∈ B, G.degree y)) :
    ∃ S : Finset V,
      S.Nonempty ∧
      shrinkFactor * S.card ≤ Fintype.card V ∧
      S.card < Fintype.card V ∧
      G.edgeFinset.card <
        edgeLossFactor * (G.induce (↑S : Set V)).edgeFinset.card ∧
      S.card ^ 31 < (G.induce (↑S : Set V)).edgeFinset.card ^ 21 := by
  classical
  let n := Fintype.card V
  let e := G.edgeFinset.card
  obtain ⟨P, hPeq, hPcard⟩ :=
    Finpartition.exists_equipartition_card_eq (Finset.univ : Finset V)
      blockCount_pos.ne' hlarge
  have hPne : P.parts.Nonempty := by
    rw [← Finset.card_pos, hPcard]
    exact blockCount_pos
  obtain ⟨C, hCP, hmany⟩ := exists_part_with_many_darts G B P hPne
  let S := B ∪ C
  let A := G.induce (↑S : Set V)
  have hCcard : C.card ≤ n / blockCount + 1 := by
    have h := hPeq.card_part_le_average_add_one hCP
    rw [hPcard] at h
    simpa [n] using h
  have hScard : S.card ≤ B.card + C.card := Finset.card_union_le B C
  have hshrink : shrinkFactor * S.card ≤ n := by
    apply (Nat.mul_le_mul_left shrinkFactor hScard).trans
    apply shrink_union_bound hlarge
    · rw [hBcard]
    · exact hCcard
  have hedgeLoss : e < edgeLossFactor * A.edgeFinset.card := by
    have hdarts : (dartsFrom G B).card = ∑ y ∈ B, G.degree y :=
      card_dartsFrom G B
    have hto := card_dartsToPart_le_twice_induced_edges G B P hCP
    dsimp [e, edgeLossFactor]
    rw [← hPcard]
    calc
      G.edgeFinset.card < 2 * (∑ y ∈ B, G.degree y) := hdenseTop
      _ = 2 * (dartsFrom G B).card := by rw [hdarts]
      _ ≤ 2 * (P.parts.card * (dartsToPart G B P C).card) := by gcongr
      _ ≤ 4 * P.parts.card * A.edgeFinset.card := by
        dsimp [A, S] at hto ⊢
        nlinarith
      _ = 4 * P.parts.card *
          (G.induce (↑(B ∪ C) : Set V)).edgeFinset.card := rfl
  have hApos : 0 < A.edgeFinset.card := by
    have hepos : 0 < e := by
      by_contra! hezero
      have heq : e = 0 := by omega
      dsimp [e, n] at heq ⊢
      rw [heq] at hdense
      simp at hdense
    by_contra! hzero
    have heq : A.edgeFinset.card = 0 := by omega
    rw [heq] at hedgeLoss
    simp at hedgeLoss
  have hSne : S.Nonempty := by
    obtain ⟨edge, hedge⟩ := Finset.card_pos.mp hApos
    induction edge using Sym2.inductionOn with
    | _ x y =>
        have hxy : A.Adj x y := A.mem_edgeFinset.mp hedge
        exact ⟨x.1, x.2⟩
  have hSlt : S.card < n := by
    have hs2 := shrinkFactor_two_le
    have hSpos := Finset.card_pos.mpr hSne
    have htwo : 2 * S.card ≤ n :=
      (Nat.mul_le_mul_right S.card hs2).trans hshrink
    omega
  have hSdense : S.card ^ 31 < A.edgeFinset.card ^ 21 := by
    have hlossPow : e ^ 21 ≤
        edgeLossFactor ^ 21 * A.edgeFinset.card ^ 21 := by
      rw [← mul_pow]
      exact pow_le_pow_left' hedgeLoss.le 21
    have hshrinkPow : shrinkFactor ^ 31 * S.card ^ 31 ≤ n ^ 31 := by
      rw [← mul_pow]
      exact pow_le_pow_left' hshrink 31
    have hchain : shrinkFactor ^ 31 * S.card ^ 31 <
        shrinkFactor ^ 31 * A.edgeFinset.card ^ 21 := by
      calc
        shrinkFactor ^ 31 * S.card ^ 31 ≤ n ^ 31 := hshrinkPow
        _ < e ^ 21 := by simpa [n, e] using hdense
        _ ≤ edgeLossFactor ^ 21 * A.edgeFinset.card ^ 21 := hlossPow
        _ ≤ shrinkFactor ^ 31 * A.edgeFinset.card ^ 21 := by
          exact Nat.mul_le_mul_right _ edgeLoss_density_power_le
    have hspos : 0 < shrinkFactor := (by
      exact (by omega : 0 < 2).trans_le shrinkFactor_two_le)
    exact (Nat.mul_lt_mul_left (pow_pos hspos 31)).mp hchain
  exact ⟨S, hSne, hshrink, hSlt, by simpa [S, A, n, e] using hedgeLoss,
    by simpa [S, A] using hSdense⟩

/-- Deterministic Erdős--Simonovits regularization, specialized to the
exponent `31/21`. -/
theorem exists_regularCore
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : Fintype.card V ^ 31 < G.edgeFinset.card ^ 21) :
    Nonempty (RegularCore G) := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
      by_cases hsmall : n < blockCount
      · exact regularCore_of_small G (by simpa [hn] using hsmall) (by simpa [hn] using hdense)
      · have hlarge : blockCount ≤ n := le_of_not_gt hsmall
        let b := n / blockCount + 1
        have hb : b ≤ Fintype.card V := by
          rw [hn]
          exact quotientBlock_le_card hlarge
        obtain ⟨B, hBcard, htop⟩ :=
          exists_top_subset (fun v ↦ G.degree v) b hb
        by_cases hsparse : 2 * (∑ y ∈ B, G.degree y) ≤ G.edgeFinset.card
        · exact regularCore_of_top_sparse G B (by simpa [hn] using hlarge)
            (by simpa [hn] using hdense) (by simpa [b, hn] using hBcard)
            (by
              intro x hx
              rw [hBcard]
              exact htop x hx) hsparse
        · have hdenseTop : G.edgeFinset.card <
              2 * (∑ y ∈ B, G.degree y) := lt_of_not_ge hsparse
          obtain ⟨S, hSne, hshrink, hSlt, hedgeLoss, hSdense⟩ :=
            exists_dense_induced_step G B (by simpa [hn] using hlarge)
              (by simpa [hn] using hdense) (by simpa [b, hn] using hBcard)
              hdenseTop
          let A := G.induce (↑S : Set V)
          have hSlt' : S.card < n := by simpa [hn] using hSlt
          have hrec : Nonempty (RegularCore A) := by
            apply ih S.card hSlt' (V := ↑S) A
            · simpa [A] using hSdense
            · exact Fintype.card_coe S
          obtain ⟨K⟩ := hrec
          letI : Fintype K.W := K.fintypeW
          letI : DecidableEq K.W := K.decEqW
          letI : DecidableRel K.graph.Adj := K.decAdj
          have hAG : A ⊑ G := by
            simpa [A] using
              (show (G.induce (↑S : Set V)) ⊑ G from
                ⟨(SimpleGraph.Embedding.induce (↑S : Set V)).toCopy⟩)
          refine ⟨{
            W := K.W
            graph := K.graph
            contained := K.contained.trans hAG
            edges_nonempty := K.edges_nonempty
            density := K.density
            almost_regular := K.almost_regular
            transfer := ?_ }⟩
          let e := G.edgeFinset.card
          let e' := A.edgeFinset.card
          let f := K.graph.edgeFinset.card
          let m := Fintype.card K.W
          let n' := S.card
          have hepow : e ^ 21 ≤ edgeLossFactor ^ 21 * e' ^ 21 := by
            rw [← mul_pow]
            exact pow_le_pow_left' hedgeLoss.le 21
          have hnpow : shrinkFactor ^ 22 * n' ^ 22 ≤ n ^ 22 := by
            rw [← mul_pow]
            exact pow_le_pow_left' (by simpa [n', hn] using hshrink) 22
          have htransfer := K.transfer
          dsimp [e', f, m, n', A] at htransfer ⊢
          dsimp [e, e', f, m, n', A] at hepow hnpow
          calc
            G.edgeFinset.card ^ 21 * Fintype.card K.W ^ 22 ≤
                (edgeLossFactor ^ 21 * A.edgeFinset.card ^ 21) *
                  Fintype.card K.W ^ 22 := by gcongr
            _ = edgeLossFactor ^ 21 *
                (A.edgeFinset.card ^ 21 * Fintype.card K.W ^ 22) := by ring
            _ ≤ edgeLossFactor ^ 21 *
                ((4 * K.graph.edgeFinset.card) ^ 21 * S.card ^ 22) := by
              apply Nat.mul_le_mul_left
              simpa using htransfer
            _ ≤ shrinkFactor ^ 22 *
                ((4 * K.graph.edgeFinset.card) ^ 21 * S.card ^ 22) := by
              exact Nat.mul_le_mul_right _ edgeLoss_power_le_shrink_power
            _ = (4 * K.graph.edgeFinset.card) ^ 21 *
                (shrinkFactor ^ 22 * S.card ^ 22) := by ring
            _ ≤ (4 * K.graph.edgeFinset.card) ^ 21 * n ^ 22 := by
              exact Nat.mul_le_mul_left _ hnpow
            _ = (4 * K.graph.edgeFinset.card) ^ 21 * Fintype.card V ^ 22 := by
              rw [hn]

def sparseCoreHostThreshold : ℕ := 4 ^ 21 * 64 ^ 20 + 1

/-- A host above the `31/21` density scale and beyond one explicit finite
threshold has a bounded-degree sparse core.  The threshold only excludes the
possibility that the regularization descent ends on fewer than 64 vertices. -/
theorem exists_sparseCore_of_large_host
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hlarge : sparseCoreHostThreshold ≤ Fintype.card V)
    (hdense : (Fintype.card V : ℝ) ^ ((31 : ℝ) / 21) <
      (G.edgeFinset.card : ℝ)) :
    Nonempty (SparseCore G) := by
  classical
  have hdensePow : Fintype.card V ^ 31 < G.edgeFinset.card ^ 21 :=
    power_density_of_rpow_density hdense
  obtain ⟨K⟩ := exists_regularCore G hdensePow
  letI : Fintype K.W := K.fintypeW
  letI : DecidableEq K.W := K.decEqW
  letI : DecidableRel K.graph.Adj := K.decAdj
  have hmpos : 0 < K.order := by
    obtain ⟨e, he⟩ := K.edges_nonempty
    induction e using Sym2.inductionOn with
    | _ x y =>
        have : 0 < Fintype.card K.W := Fintype.card_pos_iff.mpr ⟨x⟩
        simpa [RegularCore.order] using this
  by_cases hm : 64 ≤ K.order
  · exact K.exists_sparseCore hm
  · have hm64 : K.order ≤ 64 := by omega
    have hgrowth := K.host_growth hmpos
    let C : ℕ := 4 ^ 21 * 64 ^ 20
    have hmPow : K.order ^ 20 ≤ 64 ^ 20 := pow_le_pow_left' hm64 20
    have hchain : Fintype.card V ^ 31 < C * Fintype.card V ^ 22 := by
      calc
        Fintype.card V ^ 31 < G.edgeFinset.card ^ 21 := hdensePow
        _ ≤ 4 ^ 21 * K.order ^ 20 * Fintype.card V ^ 22 := hgrowth
        _ ≤ (4 ^ 21 * 64 ^ 20) * Fintype.card V ^ 22 := by gcongr
        _ = C * Fintype.card V ^ 22 := rfl
    have hnpos : 0 < Fintype.card V := by
      have : 0 < sparseCoreHostThreshold := by
        dsimp [sparseCoreHostThreshold]
        positivity
      exact this.trans_le hlarge
    have hcancel : Fintype.card V ^ 9 < C := by
      apply lt_of_mul_lt_mul_right (a := Fintype.card V ^ 22) _
        (Nat.zero_le _)
      simpa [← pow_add] using hchain
    have hnlepow : Fintype.card V ≤ Fintype.card V ^ 9 := by
      calc
        Fintype.card V = Fintype.card V ^ 1 := by simp
        _ ≤ Fintype.card V ^ 9 :=
          pow_le_pow_right₀ (by omega : 1 ≤ Fintype.card V) (by omega)
    have hCN : C + 1 ≤ Fintype.card V := by
      simpa [C, sparseCoreHostThreshold] using hlarge
    omega

end

end Erdos113AlmostRegular

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113/HostAsymptotics.lean` -/

section
open Filter
open scoped Topology Real

namespace Erdos113HostAsymptotics

noncomputable section

open Erdos113AlmostRegular

/-- A fixed multiple of a smaller real power is eventually bounded by a
larger power.  This is the elementary absorption principle used for every
constant in the final host calculation. -/
theorem eventually_const_mul_rpow_le_rpow
    {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  have hdelta : 0 < b - a := sub_pos.mpr hab
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) ^ (b - a) :=
    tendsto_atTop.mp ht C
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : (0 : ℝ) < n := by positivity
  calc
    C * (n : ℝ) ^ a ≤ (n : ℝ) ^ (b - a) * (n : ℝ) ^ a := by
      gcongr
    _ = (n : ℝ) ^ b := by
      rw [← Real.rpow_add hnpos]
      congr 2
      ring

/-- The base-two dyadic-bin count is eventually bounded by three times any
prescribed positive power. -/
lemma eventually_logBin_le_three_rpow {e : ℝ} (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop,
      ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 3 * (n : ℝ) ^ e := by
  have hlo := (isLittleO_log_rpow_atTop he).natCast_atTop
  have hb := hlo.bound (c := (1 : ℝ)) zero_lt_one
  filter_upwards [hb, eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hnpos : (0 : ℝ) < n := by positivity
  have hnne : n ≠ 0 := by omega
  have hpowNat : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hnne
  have hpowReal : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
    exact_mod_cast hpowNat
  have hlogle := Real.log_le_log
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 n) hpowReal
  rw [Real.log_pow] at hlogle
  have hlogtwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hk : ((Nat.log 2 n : ℕ) : ℝ) / 2 ≤ Real.log n := by
    have hk0 : (0 : ℝ) ≤ ((Nat.log 2 n : ℕ) : ℝ) := by positivity
    calc
      ((Nat.log 2 n : ℕ) : ℝ) / 2 ≤
          (Nat.log 2 n : ℝ) * Real.log 2 := by
        nlinarith
      _ ≤ Real.log n := hlogle
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hn
  have hlognonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hrpownonneg : 0 ≤ (n : ℝ) ^ e := Real.rpow_nonneg hnpos.le _
  rw [abs_of_nonneg hlognonneg, abs_of_nonneg hrpownonneg, one_mul] at hn
  have hone : 1 ≤ (n : ℝ) ^ e :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) he.le
  push_cast
  nlinarith

/-- Any fixed power of the dyadic-bin count is subpolynomial.  The statement
is arranged in the exact multiplicative form needed by the host estimates. -/
theorem eventually_const_mul_rpow_mul_logBin_pow_le_rpow
    (C : ℝ) (k : ℕ) {a b : ℝ} (hC : 0 ≤ C) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ a * ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ k ≤
        (n : ℝ) ^ b := by
  let e : ℝ := (b - a) / (2 * (k + 1))
  have he : 0 < e := by
    dsimp [e]
    positivity
  have hexp : a + (k : ℝ) * e < b := by
    dsimp [e]
    have hk : (0 : ℝ) ≤ k := by positivity
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    field_simp
    nlinarith
  have habsorb := eventually_const_mul_rpow_le_rpow
    (a := a + (k : ℝ) * e) (b := b) (C := C * 3 ^ k)
      hexp (mul_nonneg hC (by positivity))
  filter_upwards [eventually_logBin_le_three_rpow he, habsorb,
    eventually_ge_atTop (1 : ℕ)] with n hlog habsorb hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hnPow : ((n : ℝ) ^ e) ^ k =
      (n : ℝ) ^ ((k : ℝ) * e) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    rw [mul_comm]
  calc
    C * (n : ℝ) ^ a * ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ k ≤
        C * (n : ℝ) ^ a * (3 * (n : ℝ) ^ e) ^ k := by
      gcongr
    _ = (C * 3 ^ k) * (n : ℝ) ^ (a + (k : ℝ) * e) := by
      rw [mul_pow, hnPow]
      rw [show C * (n : ℝ) ^ a *
          (3 ^ k * (n : ℝ) ^ ((k : ℝ) * e)) =
        (C * 3 ^ k) * ((n : ℝ) ^ a *
          (n : ℝ) ^ ((k : ℝ) * e)) by ring]
      rw [← Real.rpow_add hnpos]
    _ ≤ (n : ℝ) ^ b := habsorb

/-- The finite list of subpolynomial absorptions used after the sparse-core
reduction. -/
def HostPowerReady (m : ℕ) : Prop :=
  let L : ℝ := (Nat.log 2 m + 1 : ℕ)
  let R : ℝ := regularFactor + 1
  (1792 * R * 32768 ^ (2 : ℕ)) *
      (m : ℝ) ^ ((149 : ℝ) / 168) * L ^ (6 : ℕ) ≤
        (m : ℝ) ^ ((20 : ℝ) / 21) ∧
  25088 * (m : ℝ) ^ (0 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) ∧
  224 * (m : ℝ) ^ ((1 : ℝ) / 3) ≤ (m : ℝ) ^ ((3 : ℝ) / 8) ∧
  (1792 * R * (4 * R ^ (2 : ℕ)) ^ (26 : ℕ) * 32768 ^ (56 : ℕ)) *
      (m : ℝ) ^ ((557 : ℝ) / 21) * L ^ (168 : ℕ) ≤
        (m : ℝ) ^ ((1117 : ℝ) / 42) ∧
  131072 * (m : ℝ) ^ (0 : ℝ) * L ^ (3 : ℕ) ≤
      (m : ℝ) ^ ((44 : ℝ) / 21) ∧
  (8388608 * R ^ (2 : ℕ) * (3136 * 2 ^ (27 : ℕ))) *
      (m : ℝ) ^ (0 : ℝ) * L ^ (5 : ℕ) ≤
        (m : ℝ) ^ ((1 : ℝ) / 7) ∧
  ((702464 * 512) * 16777216 * R ^ (2 : ℕ) *
      (2 * R) ^ ((1 : ℝ) / 14)) *
      (m : ℝ) ^ ((25 : ℝ) / 49) * L ^ (9 : ℕ) ≤
        (m : ℝ) ^ ((13 : ℝ) / 21) ∧
  (((224 * 1536 * 512 ^ (26 : ℕ)) *
      (32 ^ (56 : ℕ) * (4 * 2 ^ (28 : ℕ)))) *
      R ^ (29 : ℕ) * 512 ^ (29 : ℕ)) *
      (m : ℝ) ^ ((1756 : ℝ) / 42) * L ^ (224 : ℕ) ≤
        (m : ℝ) ^ ((1759 : ℝ) / 42)

theorem eventually_hostPowerReady : ∀ᶠ m : ℕ in atTop, HostPowerReady m := by
  let R : ℝ := regularFactor + 1
  have h₁ := eventually_const_mul_rpow_mul_logBin_pow_le_rpow
    (1792 * R * 32768 ^ (2 : ℕ)) 6 (by positivity)
      (by norm_num : (149 : ℝ) / 168 < 20 / 21)
  have h₂ := eventually_const_mul_rpow_le_rpow
    (C := (25088 : ℝ)) (a := 0) (b := (1 : ℝ) / 4)
      (by norm_num) (by positivity)
  have h₃ := eventually_const_mul_rpow_le_rpow
    (C := (224 : ℝ)) (a := (1 : ℝ) / 3) (b := (3 : ℝ) / 8)
      (by norm_num) (by positivity)
  have h₄ := eventually_const_mul_rpow_mul_logBin_pow_le_rpow
    (1792 * R * (4 * R ^ (2 : ℕ)) ^ (26 : ℕ) * 32768 ^ (56 : ℕ)) 168
      (by positivity) (by norm_num : (557 : ℝ) / 21 < 1117 / 42)
  have h₅ := eventually_const_mul_rpow_mul_logBin_pow_le_rpow
    (131072 : ℝ) 3 (by positivity)
      (by norm_num : (0 : ℝ) < 44 / 21)
  have h₆ := eventually_const_mul_rpow_mul_logBin_pow_le_rpow
    (8388608 * R ^ (2 : ℕ) * (3136 * 2 ^ (27 : ℕ))) 5
      (by positivity) (by norm_num : (0 : ℝ) < 1 / 7)
  have h₇ := eventually_const_mul_rpow_mul_logBin_pow_le_rpow
    ((702464 * 512) * 16777216 * R ^ (2 : ℕ) *
      (2 * R) ^ ((1 : ℝ) / 14)) 9 (by positivity)
      (by norm_num : (25 : ℝ) / 49 < 13 / 21)
  have h₈ := eventually_const_mul_rpow_mul_logBin_pow_le_rpow
    (((224 * 1536 * 512 ^ (26 : ℕ)) *
      (32 ^ (56 : ℕ) * (4 * 2 ^ (28 : ℕ)))) *
      R ^ (29 : ℕ) * 512 ^ (29 : ℕ)) 224 (by positivity)
      (by norm_num : (1756 : ℝ) / 42 < 1759 / 42)
  filter_upwards [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈] with m
    hm₁ hm₂ hm₃ hm₄ hm₅ hm₆ hm₇ hm₈
  simpa [HostPowerReady, R] using
    And.intro hm₁ (And.intro hm₂ (And.intro hm₃ (And.intro hm₄
      (And.intro hm₅ (And.intro hm₆ (And.intro hm₇ hm₈))))))

/-- The finite algebra in Janzer's many-four-cycle branch.  The hypotheses
are precisely the two dyadic counting inequality, the dynamically-pruned
local four-cycle cap, and one final monomial inequality. -/
theorem many_branch_numeric_of_master
    (m L N a b f q d Q : ℕ) (β : ℝ)
    (hL : 0 < L) (hN : 0 < N) (ha : 2 ≤ a)
    (hq : 0 < q) (hd : 0 < d) (hβ : 0 ≤ β)
    (hb : b < 2 * a)
    (hQ : Q * d ≤ 128 * L * q)
    (hselection : q ≤ 32 * m * L ^ 2 * b * f)
    (hmaster :
      ((224 * 1536 * 512 ^ (26 : ℕ)) *
          (32 ^ (56 : ℕ) * (4 * 2 ^ (28 : ℕ))) : ℝ) *
          m ^ (28 : ℕ) * L ^ (167 : ℕ) * N ^ (29 : ℕ) ≤
        β * q * d ^ (27 : ℕ)) :
    (112 * (2 * b + 2 * a) : ℝ) *
        (2 * (((N * (Q / (a - 1)) : ℕ) : ℝ)) *
          (((((2 * a) * (Q / (a - 1)) : ℕ) : ℝ)) ^ (26 : ℕ))) ≤
      β *
        ((((f : ℝ) /
            (32 * (L : ℝ) ^ (3 : ℕ) * N)) ^ (28 : ℕ) /
              (2 * (2 : ℝ) ^ (28 : ℕ))) *
            (b : ℝ) ^ (28 : ℕ) / 2) := by
  let ℓ := Q / (a - 1)
  let X : ℝ := (112 * (2 * b + 2 * a) : ℝ) *
    (2 * (N * ℓ) * ((2 * a) * ℓ) ^ (26 : ℕ))
  let Y : ℝ :=
    ((((f : ℝ) / (32 * (L : ℝ) ^ (3 : ℕ) * N)) ^ (28 : ℕ) /
        (2 * (2 : ℝ) ^ (28 : ℕ))) *
      (b : ℝ) ^ (28 : ℕ) / 2)
  let C₁ : ℝ := 224 * 1536 * 512 ^ (26 : ℕ)
  let C₂ : ℝ := 32 ^ (56 : ℕ) * (4 * 2 ^ (28 : ℕ))
  have hℓQ : ℓ * (a - 1) ≤ Q := by
    dsimp [ℓ]
    exact Nat.div_mul_le_self Q (a - 1)
  have haa : a ≤ 2 * (a - 1) := by omega
  have hℓad : ℓ * a * d ≤ 256 * L * q := by
    calc
      ℓ * a * d ≤ ℓ * (2 * (a - 1)) * d := by gcongr
      _ = 2 * (ℓ * (a - 1)) * d := by ring
      _ ≤ 2 * Q * d := by gcongr
      _ = 2 * (Q * d) := by ring
      _ ≤ 2 * (128 * L * q) := by gcongr
      _ = 256 * L * q := by ring
  have hcap : 2 * b + 2 * a ≤ 6 * a := by omega
  have hcapℓd : (2 * b + 2 * a) * ℓ * d ≤ 1536 * L * q := by
    calc
      (2 * b + 2 * a) * ℓ * d ≤ (6 * a) * ℓ * d := by gcongr
      _ = 6 * (ℓ * a * d) := by ring
      _ ≤ 6 * (256 * L * q) := by gcongr
      _ = 1536 * L * q := by ring
  have hpairℓd : ((2 * a) * ℓ) * d ≤ 512 * L * q := by
    calc
      ((2 * a) * ℓ) * d = 2 * (ℓ * a * d) := by ring
      _ ≤ 2 * (256 * L * q) := by gcongr
      _ = 512 * L * q := by ring
  have hcapℓdR : (((2 * b + 2 * a) * ℓ * d : ℕ) : ℝ) ≤
      1536 * L * q := by exact_mod_cast hcapℓd
  have hpairℓdR : (((2 * a) * ℓ * d : ℕ) : ℝ) ≤
      512 * L * q := by exact_mod_cast hpairℓd
  have hXd : X * (d : ℝ) ^ (27 : ℕ) ≤
      C₁ * N * (L : ℝ) ^ (27 : ℕ) * (q : ℝ) ^ (27 : ℕ) := by
    have hpow : ((((2 * a) * ℓ * d : ℕ) : ℝ) ^ (26 : ℕ)) ≤
        (512 * (L : ℝ) * q) ^ (26 : ℕ) := by
      apply pow_le_pow_left₀ (by positivity)
      exact hpairℓdR
    dsimp [X, C₁]
    push_cast at hcapℓdR hpairℓdR hpow ⊢
    calc
      (112 : ℝ) * (2 * (b : ℝ) + 2 * a) *
            (2 * ((N : ℝ) * ℓ) * (2 * (a : ℝ) * ℓ) ^ 26) * d ^ 27 =
          224 * (N : ℝ) * ((2 * (b : ℝ) + 2 * a) * ℓ * d) *
            (((2 * (a : ℝ) * ℓ) * d) ^ 26) := by ring
      _ ≤ 224 * (N : ℝ) * (1536 * L * q) * (512 * L * q) ^ 26 := by
        gcongr
      _ = (224 * 1536 * 512 ^ 26) * (N : ℝ) * L ^ 27 * q ^ 27 := by ring
  have hselectionR : (q : ℝ) ≤
      32 * m * (L : ℝ) ^ (2 : ℕ) * b * f := by
    exact_mod_cast hselection
  have hselectionPow : (q : ℝ) ^ (28 : ℕ) ≤
      (32 * (m : ℝ) * (L : ℝ) ^ (2 : ℕ) * b * f) ^ (28 : ℕ) := by
    apply pow_le_pow_left₀ (by positivity)
    exact hselectionR
  have hYidentity :
      C₂ * (m : ℝ) ^ (28 : ℕ) * (L : ℝ) ^ (140 : ℕ) *
          (N : ℝ) ^ (28 : ℕ) * Y =
        (32 * m * (L : ℝ) ^ (2 : ℕ) * b * f) ^ (28 : ℕ) := by
    have hden : (32 * (L : ℝ) ^ (3 : ℕ) * N) ≠ 0 := by positivity
    dsimp [C₂, Y]
    field_simp
    ring
  have hqY : (q : ℝ) ^ (28 : ℕ) ≤
      C₂ * (m : ℝ) ^ (28 : ℕ) * (L : ℝ) ^ (140 : ℕ) *
        (N : ℝ) ^ (28 : ℕ) * Y := by
    rw [hYidentity]
    exact hselectionPow
  have hqZY :
      (q : ℝ) *
          (C₁ * N * (L : ℝ) ^ (27 : ℕ) * (q : ℝ) ^ (27 : ℕ)) ≤
        β * q * (d : ℝ) ^ (27 : ℕ) * Y := by
    calc
      (q : ℝ) *
          (C₁ * N * (L : ℝ) ^ (27 : ℕ) * (q : ℝ) ^ (27 : ℕ)) =
          C₁ * N * (L : ℝ) ^ (27 : ℕ) * (q : ℝ) ^ (28 : ℕ) := by ring
      _ ≤ C₁ * N * (L : ℝ) ^ (27 : ℕ) *
          (C₂ * (m : ℝ) ^ (28 : ℕ) * (L : ℝ) ^ (140 : ℕ) *
            (N : ℝ) ^ (28 : ℕ) * Y) := by gcongr
      _ = (C₁ * C₂ * (m : ℝ) ^ (28 : ℕ) *
          (L : ℝ) ^ (167 : ℕ) * (N : ℝ) ^ (29 : ℕ)) * Y := by ring
      _ ≤ (β * q * (d : ℝ) ^ (27 : ℕ)) * Y := by
        apply mul_le_mul_of_nonneg_right
        · simpa [C₁, C₂] using hmaster
        · dsimp [Y]
          positivity
      _ = β * q * (d : ℝ) ^ (27 : ℕ) * Y := rfl
  have hZY : C₁ * N * (L : ℝ) ^ (27 : ℕ) * (q : ℝ) ^ (27 : ℕ) ≤
      β * (d : ℝ) ^ (27 : ℕ) * Y := by
    apply (mul_le_mul_iff_right₀ (by exact_mod_cast hq : (0 : ℝ) < q)).mp
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hqZY
  have hXdY : X * (d : ℝ) ^ (27 : ℕ) ≤
      (β * Y) * (d : ℝ) ^ (27 : ℕ) := by
    calc
      X * (d : ℝ) ^ (27 : ℕ) ≤
          C₁ * N * (L : ℝ) ^ (27 : ℕ) * (q : ℝ) ^ (27 : ℕ) := hXd
      _ ≤ β * (d : ℝ) ^ (27 : ℕ) * Y := hZY
      _ = (β * Y) * (d : ℝ) ^ (27 : ℕ) := by ring
  have hdPow : (0 : ℝ) < (d : ℝ) ^ (27 : ℕ) := by positivity
  have hXY : X ≤ β * Y := (mul_le_mul_iff_left₀ hdPow).mp hXdY
  simpa [X, Y, ℓ] using hXY

/-- Finite algebra for the few-four-cycle branch.  Each of the four kinds of
bad-walk contribution is budgeted by `W / 896`; there are two color classes
and the outer factor is `56`. -/
theorem few_branch_numerics
    (n s e : ℕ) (W d β Q : ℝ) (D t₀ t₂ : Bool → ℝ)
    (hs : 0 < s) (hd : 0 < d) (hβ : 0 ≤ β)
    (hD : ∀ b, 0 ≤ D b) (ht₀ : ∀ b, 0 < t₀ b)
    (ht₂ : ∀ b, 0 < t₂ b) (hQ : 0 ≤ Q)
    (hW : d ^ (56 : ℕ) ≤ W)
    (hinterp₀ : ∀ b,
      896 * D b * t₀ b * (n : ℝ) ^ ((1 : ℝ) / 28) ≤ d ^ (2 : ℕ))
    (hinterp₂ : ∀ b,
      896 * D b * t₂ b * (n : ℝ) ^ ((1 : ℝ) / 28) ≤ d ^ (2 : ℕ))
    (hinv₀ : ∀ b, 896 * 28 * (t₀ b)⁻¹ ≤ 1)
    (hinv₂ : ∀ b, 896 * (Q / s) * (t₂ b)⁻¹ ≤ 1)
    (hpattern :
      (448 * s : ℝ) * e * (D false * D true) ^ (26 : ℕ) ≤
        β * d ^ (56 : ℕ)) :
    (0 < W) ∧
    (56 * ∑ b : Bool,
          (D b * t₀ b *
              ((n : ℝ) ^ ((1 : ℝ) / 28) * W ^ ((27 : ℝ) / 28)) +
            28 * (t₀ b)⁻¹ * W) +
        56 * ∑ b : Bool,
          (D b * t₂ b *
              ((n : ℝ) ^ ((1 : ℝ) / 28) * W ^ ((27 : ℝ) / 28)) +
            (Q / s) * (t₂ b)⁻¹ * W) ≤ W / 2) ∧
    ((16 * 7 * s : ℝ) *
        (2 * e * (D false * D true) ^ (26 : ℕ)) ≤ β * (W / 2)) := by
  have hWpos : 0 < W := lt_of_lt_of_le (by positivity : 0 < d ^ (56 : ℕ)) hW
  have hroot : d ^ (2 : ℕ) ≤ W ^ ((1 : ℝ) / 28) := by
    have hr := Real.rpow_le_rpow (by positivity : 0 ≤ d ^ (56 : ℕ)) hW
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 28)
    calc
      d ^ (2 : ℕ) = (d ^ (56 : ℕ)) ^ ((1 : ℝ) / 28) := by
        rw [← Real.rpow_natCast]
        rw [show d ^ (56 : ℕ) = d ^ (56 : ℝ) by
          exact (Real.rpow_natCast d 56).symm]
        rw [← Real.rpow_mul hd.le]
        norm_num
      _ ≤ W ^ ((1 : ℝ) / 28) := hr
  have hsplit : W ^ ((27 : ℝ) / 28) * W ^ ((1 : ℝ) / 28) = W := by
    rw [← Real.rpow_add hWpos]
    norm_num [Real.rpow_one]
  have hinterpTerm₀ (b : Bool) :
      D b * t₀ b * ((n : ℝ) ^ ((1 : ℝ) / 28) * W ^ ((27 : ℝ) / 28)) ≤
        W / 896 := by
    have hbase := (hinterp₀ b).trans hroot
    have hmul := mul_le_mul_of_nonneg_right hbase
      (Real.rpow_nonneg hWpos.le ((27 : ℝ) / 28))
    rw [show 896 * D b * t₀ b * (n : ℝ) ^ ((1 : ℝ) / 28) *
          W ^ ((27 : ℝ) / 28) =
        896 * (D b * t₀ b *
          ((n : ℝ) ^ ((1 : ℝ) / 28) * W ^ ((27 : ℝ) / 28))) by ring,
      mul_comm (W ^ ((1 : ℝ) / 28)), hsplit] at hmul
    nlinarith
  have hinterpTerm₂ (b : Bool) :
      D b * t₂ b * ((n : ℝ) ^ ((1 : ℝ) / 28) * W ^ ((27 : ℝ) / 28)) ≤
        W / 896 := by
    have hbase := (hinterp₂ b).trans hroot
    have hmul := mul_le_mul_of_nonneg_right hbase
      (Real.rpow_nonneg hWpos.le ((27 : ℝ) / 28))
    rw [show 896 * D b * t₂ b * (n : ℝ) ^ ((1 : ℝ) / 28) *
          W ^ ((27 : ℝ) / 28) =
        896 * (D b * t₂ b *
          ((n : ℝ) ^ ((1 : ℝ) / 28) * W ^ ((27 : ℝ) / 28))) by ring,
      mul_comm (W ^ ((1 : ℝ) / 28)), hsplit] at hmul
    nlinarith
  have hinvTerm₀ (b : Bool) : 28 * (t₀ b)⁻¹ * W ≤ W / 896 := by
    have := mul_le_mul_of_nonneg_right (hinv₀ b) hWpos.le
    nlinarith
  have hinvTerm₂ (b : Bool) : (Q / s) * (t₂ b)⁻¹ * W ≤ W / 896 := by
    have := mul_le_mul_of_nonneg_right (hinv₂ b) hWpos.le
    nlinarith
  refine ⟨hWpos, ?_, ?_⟩
  · rw [Fintype.sum_bool, Fintype.sum_bool]
    have h0t := hinterpTerm₀ true
    have h0f := hinterpTerm₀ false
    have h2t := hinterpTerm₂ true
    have h2f := hinterpTerm₂ false
    have hi0t := hinvTerm₀ true
    have hi0f := hinvTerm₀ false
    have hi2t := hinvTerm₂ true
    have hi2f := hinvTerm₂ false
    linarith
  · have hp := hpattern.trans (mul_le_mul_of_nonneg_left hW hβ)
    nlinarith

end

end Erdos113HostAsymptotics

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos113.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 113.
https://www.erdosproblems.com/forum/thread/113

Informal authors:
- Oliver Janzer

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos113.md
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
# Erdős Problem 113

The mathematical proof and its correspondence with this development are
documented in `tex/113.tex`.
-/

open Filter
open scoped Asymptotics Real SimpleGraph

/-- Every nonempty induced subgraph has a vertex of degree at most two. -/
def IsTwoDegenerate {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, S.Nonempty →
    ∃ v : S, (G.neighborSet v ∩ S).ncard ≤ 2

/-- The extremal number of `H` is `O(n^(3/2))`. -/
def HasThreeHalvesExtremalBound {V : Type*} (H : SimpleGraph V) : Prop :=
  (fun n : ℕ ↦ (SimpleGraph.extremalNumber n H : ℝ)) =O[atTop]
    (fun n : ℕ ↦ (n : ℝ) ^ ((3 : ℝ) / 2))

/-- A real-exponent version of the extremal bound, used to keep the
asymptotic bookkeeping separate from the combinatorial embedding theorem. -/
def HasExtremalBound {V : Type*} (a : ℝ) (H : SimpleGraph V) : Prop :=
  (fun n : ℕ ↦ (SimpleGraph.extremalNumber n H : ℝ)) =O[atTop]
    (fun n : ℕ ↦ (n : ℝ) ^ a)

lemma hasExtremalBound_of_eventually_le {V : Type*} {H : SimpleGraph V} {a : ℝ}
    (h : ∀ᶠ n : ℕ in atTop,
      (SimpleGraph.extremalNumber n H : ℝ) ≤ (n : ℝ) ^ a) :
    HasExtremalBound a H := by
  apply Asymptotics.IsBigO.of_bound'
  filter_upwards [h] with n hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg hn0 _)]
  exact hn

lemma rpow_thirtyOne_div_twentyOne_isBigO_three_div_two :
    (fun n : ℕ ↦ (n : ℝ) ^ ((31 : ℝ) / 21)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ ((3 : ℝ) / 2)) := by
  apply Asymptotics.IsBigO.of_bound' 
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hn0 _),
    abs_of_nonneg (Real.rpow_nonneg hn0 _)]
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast hn
  · norm_num

lemma hasThreeHalvesExtremalBound_of_thirtyOne_div_twentyOne {V : Type*}
    {H : SimpleGraph V} (h : HasExtremalBound ((31 : ℝ) / 21) H) :
    HasThreeHalvesExtremalBound H :=
  h.trans rpow_thirtyOne_div_twentyOne_isBigO_three_div_two

/-! ## A finite pruning engine

This is the deletion argument used in Janzer's good-to-nice cycle-family
lemma.  The conclusion packages a terminal subfamily, the bound on the total
number of deleted members, and the lower bound in every surviving fiber. -/

theorem exists_pruned_subfamily {α : Type*} [DecidableEq α] (t : ℕ)
    (C : Finset α) (fibers : Finset (Finset α)) :
    ∃ D : Finset α,
      D ⊆ C ∧
      C.card ≤ D.card + fibers.card * (t - 1) ∧
      ∀ F ∈ fibers, (D ∩ F).Nonempty → t ≤ (D ∩ F).card := by
  induction hn : fibers.card using Nat.strong_induction_on generalizing C fibers with
  | h n ih =>
      by_cases hsmall : ∃ F ∈ fibers, (C ∩ F).Nonempty ∧ (C ∩ F).card < t
      · obtain ⟨F, hFmem, _hFnonempty, hFsmall⟩ := hsmall
        have herase_lt : (fibers.erase F).card < n := by
          rw [← hn]
          exact Finset.card_erase_lt_of_mem hFmem
        obtain ⟨D, hDsub, hDcard, hDstab⟩ :=
          ih (fibers.erase F).card herase_lt (C \ F) (fibers.erase F) rfl
        refine ⟨D, hDsub.trans Finset.sdiff_subset, ?_, ?_⟩
        · have hsplit := Finset.card_sdiff_add_card_inter C F
          have herase := Finset.card_erase_add_one hFmem
          have hFbound : (C ∩ F).card ≤ t - 1 := Nat.le_sub_one_of_lt hFsmall
          calc
            C.card = (C \ F).card + (C ∩ F).card := hsplit.symm
            _ ≤ (D.card + (fibers.erase F).card * (t - 1)) + (t - 1) :=
              Nat.add_le_add hDcard hFbound
            _ = D.card + fibers.card * (t - 1) := by
              rw [← herase, Nat.add_mul, one_mul]
              omega
            _ = D.card + n * (t - 1) := by rw [← hn]
        · intro F' hF'mem hnonempty
          by_cases hF'eq : F' = F
          · subst F'
            have hempty : D ∩ F = ∅ := by
              apply Finset.eq_empty_iff_forall_notMem.mpr
              intro x hx
              have hxD := hDsub (Finset.mem_inter.mp hx).1
              exact (Finset.mem_sdiff.mp hxD).2 (Finset.mem_inter.mp hx).2
            exact (by simpa [hempty] using hnonempty)
          · exact hDstab F' (Finset.mem_erase.mpr ⟨hF'eq, hF'mem⟩) hnonempty
      · refine ⟨C, Finset.Subset.rfl, by omega, ?_⟩
        intro F hFmem hnonempty
        exact le_of_not_gt fun hlt ↦ hsmall ⟨F, hFmem, hnonempty, hlt⟩

/-! ### Ordered 56-cycles and Janzer's good/nice conditions

The chosen value `k = 7` makes the cycle length `8k = 56`.  Restrictions to
all coordinates except one, or except a cyclic adjacent pair, give a
literal finite model of the fibers in Definitions 2.11 and 2.12 of Janzer's
paper. -/

abbrev CycleTuple (V : Type*) := Fin 56 → V

def IsGenuineCycleTuple {V : Type*} (G : SimpleGraph V) (x : CycleTuple V) : Prop :=
  Function.Injective x ∧ ∀ i, G.Adj (x i) (x (i + 1))

abbrev OffSingle (i : Fin 56) := {j : Fin 56 // j ≠ i}

abbrev OffPair (i : Fin 56) := {j : Fin 56 // j ≠ i ∧ j ≠ i + 1}

def restrictOffSingle {V : Type*} (i : Fin 56) (x : CycleTuple V) :
    OffSingle i → V := fun j ↦ x j

def restrictOffPair {V : Type*} (i : Fin 56) (x : CycleTuple V) :
    OffPair i → V := fun j ↦ x j

def singleFiber {V : Type*} [Fintype V] [DecidableEq V] (C : Finset (CycleTuple V))
    (i : Fin 56) (r : OffSingle i → V) : Finset (CycleTuple V) :=
  C.filter fun x ↦ restrictOffSingle i x = r

def pairFiber {V : Type*} [Fintype V] [DecidableEq V] (C : Finset (CycleTuple V))
    (i : Fin 56) (r : OffPair i → V) : Finset (CycleTuple V) :=
  C.filter fun x ↦ restrictOffPair i x = r

def pairPatterns {V : Type*} [Fintype V] [DecidableEq V] (C : Finset (CycleTuple V))
    (i : Fin 56) : Finset (OffPair i → V) :=
  C.image (restrictOffPair i)

/-! The `54` retained coordinates of an adjacent-pair pattern occur in one
consecutive path.  This explicit cyclic ordering makes the standard
`|V| Δ^53` pattern bound a direct application of finite walk counting. -/

def shiftTwo56 (t : Fin 54) : Fin 56 := ⟨t.val + 2, by omega⟩

def offPairOrder (i : Fin 56) (t : Fin 54) : OffPair i :=
  ⟨i + shiftTwo56 t, by decide +revert, by decide +revert⟩

lemma offPairOrder_bijective (i : Fin 56) : Function.Bijective (offPairOrder i) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro a b hab
    have hab' : i + shiftTwo56 a = i + shiftTwo56 b :=
      congrArg Subtype.val hab
    have hs : shiftTwo56 a = shiftTwo56 b := add_left_cancel hab'
    apply Fin.ext
    have hv := congrArg Fin.val hs
    simpa [shiftTwo56] using hv
  · have hcard : Fintype.card (OffPair i) = 54 := by
      decide +revert
    simp [hcard]

lemma shiftTwo56_castSucc_add_one (t : Fin 53) :
    shiftTwo56 t.castSucc + 1 = shiftTwo56 t.succ := by
  apply Fin.ext
  rw [Fin.val_add_eq_of_add_lt]
  · simp [shiftTwo56]
  · simp [shiftTwo56]
    omega

def pairPatternPath {V : Type*} (i : Fin 56) (r : OffPair i → V) : Fin 54 → V :=
  fun t ↦ r (offPairOrder i t)

lemma pairPatternPath_injective {V : Type*} (i : Fin 56) :
    Function.Injective (pairPatternPath (V := V) i) := by
  intro r s hrs
  funext j
  obtain ⟨t, rfl⟩ := (offPairOrder_bijective i).2 j
  exact congrFun hrs t

noncomputable def pairPatternToPathTuple {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Finset (CycleTuple V))
    (hgen : ∀ x ∈ C, IsGenuineCycleTuple G x) (i : Fin 56) :
    ↑(pairPatterns C i) → Erdos113Paths.PathTuple G 53 := fun r ↦ by
  refine ⟨pairPatternPath i r.1, ?_⟩
  obtain ⟨x, hxC, hxr⟩ := Finset.mem_image.mp r.2
  intro t
  have hadj := (hgen x hxC).2 (i + shiftTwo56 t.castSucc)
  change G.Adj
    (r.1 (offPairOrder i t.castSucc))
    (r.1 (offPairOrder i t.succ))
  rw [← hxr]
  simpa [restrictOffPair, offPairOrder, add_assoc,
    shiftTwo56_castSucc_add_one] using hadj

lemma pairPatternToPathTuple_injective {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Finset (CycleTuple V))
    (hgen : ∀ x ∈ C, IsGenuineCycleTuple G x) (i : Fin 56) :
    Function.Injective (pairPatternToPathTuple G C hgen i) := by
  intro r s hrs
  apply Subtype.ext
  apply pairPatternPath_injective i
  exact congrArg Subtype.val hrs

lemma pairPatterns_card_cast_le_bipartite_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (D : Bool → ℝ) (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x))
    (C : Finset (CycleTuple V))
    (hgen : ∀ x ∈ C, IsGenuineCycleTuple G x) (i : Fin 56) :
    ((pairPatterns C i).card : ℝ) ≤
      2 * G.edgeFinset.card * (D false * D true) ^ 26 := by
  classical
  have hcard : Fintype.card ↑(pairPatterns C i) ≤
      Fintype.card (Erdos113Paths.PathTuple G 53) :=
    Fintype.card_le_of_injective (pairPatternToPathTuple G C hgen i)
      (pairPatternToPathTuple_injective G C hgen i)
  calc
    ((pairPatterns C i).card : ℝ) = Fintype.card ↑(pairPatterns C i) := by simp
    _ ≤ Fintype.card (Erdos113Paths.PathTuple G 53) := by exact_mod_cast hcard
    _ ≤ 2 * G.edgeFinset.card * (D false * D true) ^ 26 :=
      Erdos113Paths.card_pathTuple_53_cast_le_bipartite_edges
        G side D hD hcross hdeg

def commonNeighborFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Finset V :=
  G.neighborFinset u ∩ G.neighborFinset v

def codegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℕ :=
  (commonNeighborFinset G u v).card

@[simp] lemma mem_commonNeighborFinset {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v w : V} :
    w ∈ commonNeighborFinset G u v ↔ G.Adj u w ∧ G.Adj v w := by
  simp [commonNeighborFinset, SimpleGraph.mem_neighborFinset]

def HasControlledTwoStepCodegrees {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) (x : CycleTuple V) : Prop :=
  ∀ i, codegree G (x i) (x (i + 2)) ≤ s

noncomputable def controlledGenuineCycles {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) : Finset (CycleTuple V) :=
  by
    classical
    exact Finset.univ.filter fun x ↦
      IsGenuineCycleTuple G x ∧ HasControlledTwoStepCodegrees G s x

@[simp] lemma mem_controlledGenuineCycles {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s : ℕ} {x : CycleTuple V} :
    x ∈ controlledGenuineCycles G s ↔
      IsGenuineCycleTuple G x ∧ HasControlledTwoStepCodegrees G s x := by
  classical
  simp [controlledGenuineCycles]

lemma fin56_sub_one_add_one (i : Fin 56) : i - 1 + 1 = i := by
  decide +revert

lemma fin56_sub_one_ne (i : Fin 56) : i - 1 ≠ i := by
  decide +revert

lemma fin56_add_one_ne_self (i : Fin 56) : i + 1 ≠ i := by
  decide +revert

lemma fin56_sub_one_add_two (i : Fin 56) : i - 1 + 2 = i + 1 := by
  decide +revert

lemma singleFiber_card_le_of_controlled {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) (i : Fin 56)
    (r : OffSingle i → V) :
    (singleFiber (controlledGenuineCycles G s) i r).card ≤ s := by
  classical
  let F := singleFiber (controlledGenuineCycles G s) i r
  by_cases hF : F.Nonempty
  · let x₀ : CycleTuple V := hF.choose
    have hx₀F : x₀ ∈ F := hF.choose_spec
    have hx₀data := Finset.mem_filter.mp hx₀F
    have hx₀control := (mem_controlledGenuineCycles.mp hx₀data.1).2 (i - 1)
    let f : ↑F → ↑(commonNeighborFinset G (x₀ (i - 1)) (x₀ (i + 1))) :=
      fun x ↦ ⟨x.1 i, by
        rw [mem_commonNeighborFinset]
        have hxdata := Finset.mem_filter.mp x.2
        have hxgen := (mem_controlledGenuineCycles.mp hxdata.1).1
        have hrest : restrictOffSingle i x.1 = restrictOffSingle i x₀ :=
          hxdata.2.trans hx₀data.2.symm
        have hprev : x.1 (i - 1) = x₀ (i - 1) :=
          congrFun hrest ⟨i - 1, fin56_sub_one_ne i⟩
        have hnext : x.1 (i + 1) = x₀ (i + 1) :=
          congrFun hrest ⟨i + 1, fin56_add_one_ne_self i⟩
        constructor
        · simpa [hprev, fin56_sub_one_add_one] using hxgen.2 (i - 1)
        · simpa [hnext] using (hxgen.2 i).symm⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      funext j
      by_cases hji : j = i
      · subst j
        exact congrArg Subtype.val hxy
      · have hxdata := Finset.mem_filter.mp x.2
        have hydata := Finset.mem_filter.mp y.2
        exact (congrFun hxdata.2 ⟨j, hji⟩).trans
          (congrFun hydata.2 ⟨j, hji⟩).symm
    have hcard : F.card ≤
        (commonNeighborFinset G (x₀ (i - 1)) (x₀ (i + 1))).card := by
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
    exact hcard.trans (by
      simpa [codegree, fin56_sub_one_add_two] using hx₀control)
  · simp only [Finset.not_nonempty_iff_eq_empty] at hF
    simp [F, hF]

/-- Janzer's `β`-good condition, specialized to `k = 7`.  The third field is
the denominator-free form of
`patterns ≤ β |C| / (16 k s)`. -/
structure IsGoodCycleFamily {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (β : ℝ) (C : Finset (CycleTuple V)) : Type where
  s : ℕ
  s_pos : 0 < s
  genuine : ∀ x ∈ C, IsGenuineCycleTuple G x
  single_card : ∀ (i : Fin 56) (r : OffSingle i → V),
    (singleFiber C i r).card ≤ s
  pattern_card : ∀ i : Fin 56,
    (16 * 7 * s : ℝ) * (pairPatterns C i).card ≤ β * C.card

noncomputable def controlledGenuineCycles_isGood_bipartite_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (D : Bool → ℝ)
    (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x))
    (s : ℕ) (hs : 0 < s) (β L₀ : ℝ) (hβ : 0 ≤ β)
    (hcard : L₀ ≤ ((controlledGenuineCycles G s).card : ℝ))
    (hnumeric : (16 * 7 * s : ℝ) *
        (2 * G.edgeFinset.card * (D false * D true) ^ 26) ≤ β * L₀) :
    IsGoodCycleFamily G β (controlledGenuineCycles G s) := by
  refine ⟨s, hs, ?_, ?_, ?_⟩
  · intro x hx
    exact (mem_controlledGenuineCycles.mp hx).1
  · exact singleFiber_card_le_of_controlled G s
  · intro i
    calc
      (16 * 7 * s : ℝ) *
          (pairPatterns (controlledGenuineCycles G s) i).card ≤
          (16 * 7 * s : ℝ) *
            (2 * G.edgeFinset.card * (D false * D true) ^ 26) := by
        gcongr
        exact pairPatterns_card_cast_le_bipartite_edges
          G side D hD hcross hdeg (controlledGenuineCycles G s)
            (fun x hx ↦ (mem_controlledGenuineCycles.mp hx).1) i
      _ ≤ β * L₀ := hnumeric
      _ ≤ β * (controlledGenuineCycles G s).card :=
        mul_le_mul_of_nonneg_left hcard hβ

/-- The abstract many-four-cycle package.  Once the dyadic extraction gives
an auxiliary lift system and its two incidence-degree caps, the checked
supersaturation/lifting count and the edge-refined path estimate supply all
three fields of Janzer's good-family definition. -/
noncomputable def liftedCycles_isGood
    {T V : Type*} [Fintype T] [DecidableEq T]
    [Fintype V] [DecidableEq V]
    (F : SimpleGraph T) (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : Erdos113ManyLifts.LiftSystem F G)
    (cap : ℕ) (hcap : 0 < cap)
    (hmiddle : 2 * L.lower ≤ cap)
    (hbridge : ∀ u w, Erdos113ManyLifts.IsMiddleVertex L u →
      (Erdos113ManyLifts.bridgeAnchors L u w).card ≤ cap)
    (A B : ℕ)
    (hleft : ∀ t, (Erdos113Incidence.leftPartners L t).card ≤ A)
    (hright : ∀ y, (Erdos113Incidence.rightPartners L y).card ≤ B)
    (β L₀ : ℝ) (hβ : 0 ≤ β)
    (hcard : L₀ ≤ ((Erdos113ManyLifts.liftedCycles F G L).card : ℝ))
    (hnumeric : (16 * 7 * cap : ℝ) *
        (2 * (Fintype.card T * A) * (B * A) ^ 26) ≤ β * L₀) :
    IsGoodCycleFamily G β (Erdos113ManyLifts.liftedCycles F G L) := by
  let I := Erdos113Incidence.incidenceGraph L
  let side := Erdos113Incidence.incidenceSide L
  let D : Bool → ℝ := fun b ↦ if b then A else B
  have hD : ∀ b, 0 ≤ D b := by intro b; positivity
  have hdeg : ∀ v, (I.degree v : ℝ) ≤ D (side v) := by
    intro v
    dsimp [I, D, side]
    exact_mod_cast Erdos113Incidence.incidenceGraph_degree_le L A B hleft hright v
  have hedge : (I.edgeFinset.card : ℝ) ≤ Fintype.card T * A := by
    exact_mod_cast Erdos113Incidence.incidenceGraph_edge_card_le L A hleft
  refine ⟨cap, hcap, ?_, ?_, ?_⟩
  · intro z hz
    exact Erdos113ManyLifts.liftedCycles_genuine L hz
  · intro i r
    change (Erdos113ManyLifts.singleFiber56
      (Erdos113ManyLifts.liftedCycles F G L) i r).card ≤ cap
    exact Erdos113ManyLifts.singleFiber56_liftedCycles_card_le
      L cap hmiddle hbridge i r
  · intro i
    norm_num [Nat.cast_mul] at hnumeric ⊢
    have hpattern : ((pairPatterns
        (Erdos113ManyLifts.liftedCycles F G L) i).card : ℝ) ≤
        2 * (Fintype.card T * A) * (B * A) ^ 26 := by
      calc
        ((pairPatterns (Erdos113ManyLifts.liftedCycles F G L) i).card : ℝ) ≤
            2 * I.edgeFinset.card * (D false * D true) ^ 26 :=
          pairPatterns_card_cast_le_bipartite_edges I side D hD
            (fun {_ _} h ↦ Erdos113Incidence.incidenceGraph_cross L h)
            hdeg (Erdos113ManyLifts.liftedCycles F G L) (fun z hz ↦
              Erdos113Incidence.liftedCycles_genuine_incidence L hz) i
        _ ≤ 2 * (Fintype.card T * A) * (B * A) ^ 26 := by
          dsimp [D]
          gcongr
    calc
      (112 * cap : ℝ) *
          (pairPatterns (Erdos113ManyLifts.liftedCycles F G L) i).card ≤
          (112 * cap : ℝ) *
            (2 * (Fintype.card T * A) * (B * A) ^ 26) := by
        gcongr
      _ ≤ β * L₀ := hnumeric
      _ ≤ β * (Erdos113ManyLifts.liftedCycles F G L).card :=
        mul_le_mul_of_nonneg_left hcard hβ

/-- The checked many-four-cycle construction, with all asymptotic
bookkeeping exposed as explicit numerical hypotheses. -/
noncomputable def manyFourCycleGoodFamily_of_numerics
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool)
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (S : Erdos113FourCycleSelection.FirstSelection G side)
    (R : S.SecondSelection)
    (Q : ℕ)
    (hcycle : ∀ t : Erdos113AnchorConstruction.NeighborVertex G S.anchor,
      (Erdos113Cycles.cyclesThroughEdge G 4 s(S.anchor, t.1)).card ≤ Q)
    (hlift : 3136 * 2 ^ 27 ≤ 2 ^ R.index.val)
    (hsuper :
      702464 * (16 *
          (Erdos113Regular.degreeBinCount
            (W := Erdos113AnchorConstruction.NeighborVertex G S.anchor) : ℝ)) *
          (2 * Fintype.card
            (Erdos113AnchorConstruction.NeighborVertex G S.anchor) : ℝ) ^
              ((1 : ℝ) / 14) ≤
        ((S.auxiliaryGraph R.index).edgeFinset.card : ℝ) /
          (32 *
            (Erdos113Regular.degreeBinCount
              (W := Erdos113AnchorConstruction.NeighborVertex G S.anchor) : ℝ) ^ 3 *
            Fintype.card
              (Erdos113AnchorConstruction.NeighborVertex G S.anchor)))
    (β : ℝ) (hβ : 0 ≤ β)
    (hnumeric :
      let A :=
        Erdos113SelectedLift.FirstSelection.SecondSelection.anchoredLiftSystem
          S R hcross Q hcycle
      let δ := ((S.auxiliaryGraph R.index).edgeFinset.card : ℝ) /
        (32 *
          (Erdos113Regular.degreeBinCount
            (W := Erdos113AnchorConstruction.NeighborVertex G S.anchor) : ℝ) ^ 3 *
          Fintype.card
            (Erdos113AnchorConstruction.NeighborVertex G S.anchor))
      let L₀ := (δ ^ 28 / (2 * (2 : ℝ) ^ 28)) *
        ((2 ^ R.index.val : ℕ) : ℝ) ^ 28 / 2
      (16 * 7 *
          (2 ^ (R.index.val + 1) + 2 ^ (S.scaleIndex.val + 1)) : ℝ) *
        (2 * (Fintype.card
            (Erdos113AnchorConstruction.NeighborVertex G S.anchor) * A.leftCap) *
          (A.rightCap * A.leftCap) ^ 26) ≤ β * L₀) :
    IsGoodCycleFamily G β
      (Erdos113ManyLifts.liftedCycles
        (S.auxiliaryGraph R.index) G
          (Erdos113SelectedLift.FirstSelection.SecondSelection.liftSystem
            S R hcross)) := by
  let F := S.auxiliaryGraph R.index
  let A :=
    Erdos113SelectedLift.FirstSelection.SecondSelection.anchoredLiftSystem
      S R hcross Q hcycle
  let L := A.toLiftSystem
  let δ := (F.edgeFinset.card : ℝ) /
    (32 *
      (Erdos113Regular.degreeBinCount
        (W := Erdos113AnchorConstruction.NeighborVertex G S.anchor) : ℝ) ^ 3 *
      Fintype.card
        (Erdos113AnchorConstruction.NeighborVertex G S.anchor))
  let L₀ := (δ ^ 28 / (2 * (2 : ℝ) ^ 28)) *
    ((2 ^ R.index.val : ℕ) : ℝ) ^ 28 / 2
  have hFcycles : δ ^ 28 / (2 * (2 : ℝ) ^ 28) ≤
      ((Erdos113Cycles.genuineCycles F 28).card : ℝ) := by
    exact Erdos113Supersaturation28.genuineCycles28_lower_of_edgeDensity
      F R.auxiliary_edge (by simpa [F, δ] using hsuper)
  have hlower : 3136 * 2 ^ 27 ≤ L.lower := by
    change 3136 * 2 ^ 27 ≤ 2 ^ R.index.val
    exact hlift
  have hliftNat := Erdos113ManyLifts.liftedCycles_card_lower L hlower
  have hliftReal :
      ((Erdos113Cycles.genuineCycles F 28).card : ℝ) *
          (((2 ^ R.index.val : ℕ) : ℝ) ^ 28) ≤
        2 * ((Erdos113ManyLifts.liftedCycles F G L).card : ℝ) := by
    exact_mod_cast hliftNat
  have hcard : L₀ ≤
      ((Erdos113ManyLifts.liftedCycles F G L).card : ℝ) := by
    have hpownonneg : 0 ≤ (((2 ^ R.index.val : ℕ) : ℝ) ^ 28) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hFcycles hpownonneg
    dsimp [L₀]
    nlinarith
  have hleft : ∀ t, (Erdos113Incidence.leftPartners L t).card ≤ A.leftCap :=
    A.left_cap
  have hright : ∀ y, (Erdos113Incidence.rightPartners L y).card ≤ A.rightCap :=
    Erdos113AnchoredLifts.rightPartners_card_le A
  refine liftedCycles_isGood F G L
    (2 ^ (R.index.val + 1) + 2 ^ (S.scaleIndex.val + 1)) (by positivity)
      ?_ ?_ A.leftCap A.rightCap hleft hright β L₀ hβ hcard ?_
  · dsimp [L, A]
    simp only [Erdos113SelectedLift.FirstSelection.SecondSelection.anchoredLiftSystem,
      Erdos113AnchorConstruction.selectedAnchoredLiftSystem,
      Erdos113SelectedLift.FirstSelection.SecondSelection.liftSystem,
      Erdos113AnchorConstruction.selectedLiftSystem]
    change 2 * 2 ^ R.index.val ≤
      2 ^ (R.index.val + 1) + 2 ^ (S.scaleIndex.val + 1)
    simp only [pow_succ]
    omega
  · intro u w hu
    exact (Erdos113AnchoredLifts.bridgeAnchors_card_le A u w hu).trans (by
      dsimp [A]
      simp only [Erdos113SelectedLift.FirstSelection.SecondSelection.anchoredLiftSystem,
        Erdos113AnchorConstruction.selectedAnchoredLiftSystem]
      omega)
  · simpa [A, L₀, δ, F] using hnumeric

/-! ### Removing the two kinds of bad homomorphic 56-cycles

The source proof first counts all homomorphic cycles, then removes cycles
with a repeated vertex and cycles having a high-codegree distance-two pair.
The two injective encodings below connect those tuple predicates to the
closed-walk estimates in `Encode56` and `EncodeConsecutive56`. -/

abbrev HomCycle56 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :=
  {x : CycleTuple V // Erdos113Cycles.IsHomCycle G x}

abbrev RepeatedHomCycle56 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :=
  {x : HomCycle56 G // ¬ Function.Injective x.1}

def HighCodegreeRelation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) (u v : V) : Prop :=
  u ≠ v ∧ s < codegree G u v

noncomputable instance instDecidableHighCodegreeRelation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    DecidableRel (HighCodegreeRelation G s) := Classical.decRel _

abbrev HighStepHomCycle56 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :=
  {x : HomCycle56 G // ∃ i,
    HighCodegreeRelation G s (x.1 i) (x.1 (i + 2))}

lemma fin56_ne_add_two (i : Fin 56) : i ≠ i + 2 := by
  decide +revert

noncomputable def homCyclePartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    HomCycle56 G →
      ↑(controlledGenuineCycles G s) ⊕
        (RepeatedHomCycle56 G ⊕ HighStepHomCycle56 G s) := fun x ↦ by
  classical
  by_cases hinj : Function.Injective x.1
  · by_cases hcontrol : HasControlledTwoStepCodegrees G s x.1
    · exact Sum.inl ⟨x.1, mem_controlledGenuineCycles.mpr
        ⟨⟨hinj, x.2⟩, hcontrol⟩⟩
    · apply Sum.inr
      apply Sum.inr
      refine ⟨x, ?_⟩
      simp only [HasControlledTwoStepCodegrees, not_forall] at hcontrol
      obtain ⟨i, hi⟩ := hcontrol
      exact ⟨i, hinj.ne (fin56_ne_add_two i), Nat.lt_of_not_ge hi⟩
  · exact Sum.inr (Sum.inl ⟨x, hinj⟩)

def homCyclePartitionDecode {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s : ℕ} :
    ↑(controlledGenuineCycles G s) ⊕
        (RepeatedHomCycle56 G ⊕ HighStepHomCycle56 G s) →
      CycleTuple V
  | Sum.inl x => x.1
  | Sum.inr (Sum.inl x) => x.1.1
  | Sum.inr (Sum.inr x) => x.1.1

@[simp] lemma homCyclePartitionDecode_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) (x : HomCycle56 G) :
    homCyclePartitionDecode (homCyclePartition G s x) = x.1 := by
  classical
  unfold homCyclePartition
  split
  · split <;> rfl
  · rfl

lemma homCyclePartition_injective {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    Function.Injective (homCyclePartition G s) := by
  intro x y hxy
  apply Subtype.ext
  have := congrArg homCyclePartitionDecode hxy
  simpa using this

noncomputable def repeatedHomCycleToBadClosedWalk
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    RepeatedHomCycle56 G → Encode56.BadClosedWalk56 G (fun u v ↦ u = v) :=
  fun x ↦ by
    let P := Erdos113Cycle56.tupleClosedWalk x.1.1 x.1.2
    refine ⟨P, ?_⟩
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp x.2
    refine ⟨i, j, hne, ?_⟩
    have hread := Erdos113Cycle56.closedWalkTuple_tupleClosedWalk x.1.1 x.1.2
    exact (congrFun hread i).trans (hij.trans (congrFun hread j).symm)

lemma repeatedHomCycleToBadClosedWalk_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Function.Injective (repeatedHomCycleToBadClosedWalk G) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  have hP := congrArg (fun z ↦ (z.1 : Encode56.ClosedWalk56 G)) hxy
  change Erdos113Cycle56.tupleClosedWalk x.1.1 x.1.2 =
    Erdos113Cycle56.tupleClosedWalk y.1.1 y.1.2 at hP
  have hread := congrArg (Erdos113Cycle56.closedWalkTuple G) hP
  simpa only [Erdos113Cycle56.closedWalkTuple_tupleClosedWalk] using hread

lemma cyclicAdd56_two (i : Fin 56) :
    EncodeConsecutive56.cyclicAdd56 i 2 = i + 2 := by
  apply Fin.ext
  simp only [EncodeConsecutive56.cyclicAdd56]
  omega

noncomputable def highStepHomCycleToBadClosedWalk
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    HighStepHomCycle56 G s →
      EncodeConsecutive56.BadClosedWalk56 G (HighCodegreeRelation G s) :=
  fun x ↦ by
    let P := Erdos113Cycle56.tupleClosedWalk x.1.1 x.1.2
    refine ⟨P, ?_⟩
    obtain ⟨i, hi⟩ := x.2
    refine ⟨i, ?_⟩
    have hread := Erdos113Cycle56.closedWalkTuple_tupleClosedWalk x.1.1 x.1.2
    have hread_i := congrFun hread i
    have hread_i2 := congrFun hread (i + 2)
    rw [← hread_i, ← hread_i2] at hi
    simpa [EncodeConsecutive56.cv, P,
      Erdos113Cycle56.closedWalkTuple, cyclicAdd56_two] using hi

lemma highStepHomCycleToBadClosedWalk_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    Function.Injective (highStepHomCycleToBadClosedWalk G s) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  have hP := congrArg
    (fun z ↦ (z.1 : EncodeConsecutive56.ClosedWalk56 G)) hxy
  change Erdos113Cycle56.tupleClosedWalk x.1.1 x.1.2 =
    Erdos113Cycle56.tupleClosedWalk y.1.1 y.1.2 at hP
  have hread := congrArg (Erdos113Cycle56.closedWalkTuple G) hP
  simpa only [Erdos113Cycle56.closedWalkTuple_tupleClosedWalk] using hread

lemma card_homCycle56_le_controlled_add_bad
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    Fintype.card (HomCycle56 G) ≤
      (controlledGenuineCycles G s).card +
        Fintype.card (Encode56.BadClosedWalk56 G (fun u v ↦ u = v)) +
        Fintype.card
          (EncodeConsecutive56.BadClosedWalk56 G (HighCodegreeRelation G s)) := by
  have hpartition := Fintype.card_le_of_injective (homCyclePartition G s)
    (homCyclePartition_injective G s)
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_coe] at hpartition
  have hrepeat := Fintype.card_le_of_injective
    (repeatedHomCycleToBadClosedWalk G)
    (repeatedHomCycleToBadClosedWalk_injective G)
  have hhigh := Fintype.card_le_of_injective
    (highStepHomCycleToBadClosedWalk G s)
    (highStepHomCycleToBadClosedWalk_injective G s)
  omega

lemma codegree_comm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    codegree G u v = codegree G v u := by
  simp [codegree, commonNeighborFinset, Finset.inter_comm]

lemma highCodegreeRelation_symmetric
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    ∀ u v, HighCodegreeRelation G s u v →
      HighCodegreeRelation G s v u := by
  intro u v huv
  exact ⟨huv.1.symm, by simpa [codegree_comm G u v] using huv.2⟩

lemma repeatedBadClosedWalk56_side_cast_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (t D : Bool → ℝ)
    (ht : ∀ b, 0 < t b) (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x)) :
    (Fintype.card
      (Encode56.BadClosedWalk56 G (fun u v ↦ u = v)) : ℝ) ≤
      56 * ∑ b : Bool,
        (D b * t b * (Conflict56.closedWalkCount G 54 : ℝ) +
          28 * (t b)⁻¹ * (Conflict56.closedWalkCount G 56 : ℝ)) := by
  have hlocal : ∀ u y,
      (((G.neighborFinset y).filter (fun v ↦ u = v)).card : ℝ) ≤ 1 := by
    intro u y
    have hsub : (G.neighborFinset y).filter (fun v ↦ u = v) ⊆ {u} := by
      intro v hv
      simpa using (Finset.mem_filter.mp hv).2.symm
    exact_mod_cast (Finset.card_le_card hsub).trans (by simp)
  simpa only [mul_one, one_mul] using
    (Erdos113Sides56.card_BadClosedWalk56_side_cast_le
      G (fun u v ↦ u = v) side t D (fun _ ↦ 1) ht hD
        (fun _ ↦ by norm_num) hcross hdeg (fun _ _ h ↦ h.symm) hlocal)

lemma highStepBadClosedWalk56_side_cast_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (s : ℕ) (hs : 0 < s)
    (Q t D : Bool → ℝ)
    (hQ : ∀ b, 0 ≤ Q b) (ht : ∀ b, 0 < t b)
    (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x))
    (hcap : ∀ u y, G.Adj y u →
      ((Erdos113FourCycles.extensionsThroughEdge G u y).card : ℝ) ≤
        Q (side y)) :
    (Fintype.card (EncodeConsecutive56.BadClosedWalk56 G
      (HighCodegreeRelation G s)) : ℝ) ≤
      56 * ∑ b : Bool,
        (D b * t b * (Consecutive56.closedWalkCount G 54 : ℝ) +
          (Q (!b) / s) * (t b)⁻¹ *
            (Consecutive56.closedWalkCount G 56 : ℝ)) := by
  let S : Bool → ℝ := fun b ↦ Q b / s
  have hS : ∀ b, 0 ≤ S b := fun b ↦ div_nonneg (hQ b) (by positivity)
  have hlocal : ∀ u y, G.Adj y u →
      (((G.neighborFinset y).filter (HighCodegreeRelation G s u)).card : ℝ) ≤
        S (side y) := by
    intro u y huy
    have heq : (G.neighborFinset y).filter (HighCodegreeRelation G s u) =
        Erdos113FourCycles.highCodegreeNeighbors G s u y := by
      ext x
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
        HighCodegreeRelation, Erdos113FourCycles.mem_highCodegreeNeighbors]
      rfl
    rw [heq]
    exact Erdos113FourCycles.card_highCodegreeNeighbors_cast_le
      G s hs huy (Q (side y)) (hcap u y huy)
  simpa [S] using
    (Erdos113SidesConsecutive56.card_BadClosedWalk56_side_cast_le
      G (HighCodegreeRelation G s) side t D S ht hD hS hcross hdeg
        (highCodegreeRelation_symmetric G s) hlocal)

lemma controlledGenuineCycles_card_lower_of_bad_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) (B₀ B₂ : ℝ)
    (hB₀ : (Fintype.card
      (Encode56.BadClosedWalk56 G (fun u v ↦ u = v)) : ℝ) ≤ B₀)
    (hB₂ : (Fintype.card (EncodeConsecutive56.BadClosedWalk56 G
      (HighCodegreeRelation G s)) : ℝ) ≤ B₂) :
    (Conflict.closedWalkCount G 56 : ℝ) - B₀ - B₂ ≤
      ((controlledGenuineCycles G s).card : ℝ) := by
  have hcardNat := card_homCycle56_le_controlled_add_bad G s
  have hcard : (Fintype.card (HomCycle56 G) : ℝ) ≤
      (controlledGenuineCycles G s).card +
        Fintype.card (Encode56.BadClosedWalk56 G (fun u v ↦ u = v)) +
        Fintype.card (EncodeConsecutive56.BadClosedWalk56 G
          (HighCodegreeRelation G s)) := by
    exact_mod_cast hcardNat
  have htotal : (Fintype.card (HomCycle56 G) : ℝ) =
      (Conflict.closedWalkCount G 56 : ℝ) := by
    exact_mod_cast Erdos113Cycle56.card_homCycle56_eq_closedWalkCount G
  rw [htotal] at hcard
  linarith

lemma controlledGenuineCycles_card_lower_bipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (s : ℕ) (hs : 0 < s)
    (Q D t₀ t₂ : Bool → ℝ)
    (hQ : ∀ b, 0 ≤ Q b) (hD : ∀ b, 0 ≤ D b)
    (ht₀ : ∀ b, 0 < t₀ b) (ht₂ : ∀ b, 0 < t₂ b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x))
    (hcap : ∀ u y, G.Adj y u →
      ((Erdos113FourCycles.extensionsThroughEdge G u y).card : ℝ) ≤
        Q (side y)) :
    (Conflict.closedWalkCount G 56 : ℝ) -
        56 * ∑ b : Bool,
          (D b * t₀ b * (Conflict.closedWalkCount G 54 : ℝ) +
            28 * (t₀ b)⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) -
        56 * ∑ b : Bool,
          (D b * t₂ b * (Conflict.closedWalkCount G 54 : ℝ) +
            (Q (!b) / s) * (t₂ b)⁻¹ *
              (Conflict.closedWalkCount G 56 : ℝ)) ≤
      ((controlledGenuineCycles G s).card : ℝ) := by
  have hrepeat := repeatedBadClosedWalk56_side_cast_le
    G side t₀ D ht₀ hD hcross hdeg
  have hhigh := highStepBadClosedWalk56_side_cast_le
    G side s hs Q t₂ D hQ ht₂ hD hcross hdeg hcap
  apply controlledGenuineCycles_card_lower_of_bad_bounds G s _ _
  · simpa only [Conflict56.closedWalkCount, Conflict.closedWalkCount,
      Conflict56.walkCount, Conflict.walkCount] using hrepeat
  · simpa only [Consecutive56.closedWalkCount, Conflict.closedWalkCount,
      Consecutive56.walkCount, Conflict.walkCount] using hhigh

lemma controlledGenuineCycles_half_closedWalkCount_bipartite_of_numerics
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (s : ℕ) (hs : 0 < s)
    (Q D t₀ t₂ : Bool → ℝ)
    (hQ : ∀ b, 0 ≤ Q b) (hD : ∀ b, 0 ≤ D b)
    (ht₀ : ∀ b, 0 < t₀ b) (ht₂ : ∀ b, 0 < t₂ b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x))
    (hcap : ∀ u y, G.Adj y u →
      ((Erdos113FourCycles.extensionsThroughEdge G u y).card : ℝ) ≤
        Q (side y))
    (hclosed : 0 < (Conflict.closedWalkCount G 56 : ℝ))
    (hnumeric :
      56 * ∑ b : Bool,
          (D b * t₀ b *
              ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
                (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
            28 * (t₀ b)⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) +
        56 * ∑ b : Bool,
          (D b * t₂ b *
              ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
                (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
            (Q (!b) / s) * (t₂ b)⁻¹ *
              (Conflict.closedWalkCount G 56 : ℝ)) ≤
        (Conflict.closedWalkCount G 56 : ℝ) / 2) :
    (Conflict.closedWalkCount G 56 : ℝ) / 2 ≤
      ((controlledGenuineCycles G s).card : ℝ) := by
  have hinterp : (Conflict.closedWalkCount G 54 : ℝ) ≤
      (Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
        (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28) := by
    simpa only [Conflict56.closedWalkCount, Conflict.closedWalkCount,
      Conflict56.walkCount, Conflict.walkCount] using
      Erdos113Moments56.closedWalkCount_interpolation_28 G
  have hraw := controlledGenuineCycles_card_lower_bipartite
    G side s hs Q D t₀ t₂ hQ hD ht₀ ht₂ hcross hdeg hcap
  have hreplace₀ : ∀ b,
      D b * t₀ b * (Conflict.closedWalkCount G 54 : ℝ) ≤
        D b * t₀ b *
          ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
            (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) := by
    intro b
    exact mul_le_mul_of_nonneg_left hinterp
      (mul_nonneg (hD b) (ht₀ b).le)
  have hreplace₂ : ∀ b,
      D b * t₂ b * (Conflict.closedWalkCount G 54 : ℝ) ≤
        D b * t₂ b *
          ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
            (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) := by
    intro b
    exact mul_le_mul_of_nonneg_left hinterp
      (mul_nonneg (hD b) (ht₂ b).le)
  have hsum₀ :
      ∑ b : Bool,
          (D b * t₀ b * (Conflict.closedWalkCount G 54 : ℝ) +
            28 * (t₀ b)⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) ≤
        ∑ b : Bool,
          (D b * t₀ b *
              ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
                (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
            28 * (t₀ b)⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) := by
    exact Finset.sum_le_sum (fun b _ ↦ add_le_add (hreplace₀ b) le_rfl)
  have hsum₂ :
      ∑ b : Bool,
          (D b * t₂ b * (Conflict.closedWalkCount G 54 : ℝ) +
            (Q (!b) / s) * (t₂ b)⁻¹ *
              (Conflict.closedWalkCount G 56 : ℝ)) ≤
        ∑ b : Bool,
          (D b * t₂ b *
              ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
                (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
            (Q (!b) / s) * (t₂ b)⁻¹ *
              (Conflict.closedWalkCount G 56 : ℝ)) := by
    exact Finset.sum_le_sum (fun b _ ↦ add_le_add (hreplace₂ b) le_rfl)
  linarith

lemma closedWalkCount_56_lower_of_minDegree
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ)
    (hd : 0 ≤ d) (hmin : ∀ x, d ≤ (G.degree x : ℝ)) :
    d ^ 56 ≤ (Conflict.closedWalkCount G 56 : ℝ) := by
  simpa only [show 56 = 2 * 28 by norm_num] using
    Lower.closedWalkCount_lower_of_minDegree G d hd hmin 28

/-- Janzer's `β`-nice condition, again for `k = 7`.  In every adjacent-pair
fiber, prescribing either missing coordinate occupies at most a `β`
proportion. -/
structure IsNiceCycleFamily {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (β : ℝ) (C : Finset (CycleTuple V)) : Prop where
  genuine : ∀ x ∈ C, IsGenuineCycleTuple G x
  balanced : ∀ (i : Fin 56) (r : OffPair i → V) (u : V),
    (((pairFiber C i r).filter fun x : CycleTuple V ↦
      x i = u ∨ x (i + 1) = u).card : ℝ) ≤
      β * (pairFiber C i r).card

def fillPairLeft {V : Type*} (i : Fin 56) (r : OffPair i → V) (u : V) :
    OffSingle (i + 1) → V := fun j ↦
  if h : (j : Fin 56) = i then u else r ⟨j, h, j.property⟩

def fillPairRight {V : Type*} (i : Fin 56) (r : OffPair i → V) (u : V) :
    OffSingle i → V := fun j ↦
  if h : (j : Fin 56) = i + 1 then u else r ⟨j, j.property, h⟩

lemma pairFiber_filter_left_subset_singleFiber {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (i : Fin 56) (r : OffPair i → V) (u : V) :
    (pairFiber C i r).filter (fun x : CycleTuple V ↦ x i = u) ⊆
      singleFiber C (i + 1) (fillPairLeft i r u) := by
  intro x hx
  have hxpair := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hxleft := (Finset.mem_filter.mp hx).2
  rw [singleFiber, Finset.mem_filter]
  refine ⟨hxpair.1, ?_⟩
  funext j
  simp only [restrictOffSingle, fillPairLeft]
  split_ifs with hj
  · simpa [hj] using hxleft
  · have hrest := congrFun hxpair.2 ⟨j, hj, j.property⟩
    exact hrest

lemma pairFiber_filter_right_subset_singleFiber {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (i : Fin 56) (r : OffPair i → V) (u : V) :
    (pairFiber C i r).filter (fun x : CycleTuple V ↦ x (i + 1) = u) ⊆
      singleFiber C i (fillPairRight i r u) := by
  intro x hx
  have hxpair := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hxright := (Finset.mem_filter.mp hx).2
  rw [singleFiber, Finset.mem_filter]
  refine ⟨hxpair.1, ?_⟩
  funext j
  simp only [restrictOffSingle, fillPairRight]
  split_ifs with hj
  · simpa [hj] using hxright
  · have hrest := congrFun hxpair.2 ⟨j, j.property, hj⟩
    exact hrest

lemma IsGoodCycleFamily.prescribed_pair_card_le {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {β : ℝ} {C : Finset (CycleTuple V)}
    (hgood : IsGoodCycleFamily G β C) (i : Fin 56) (r : OffPair i → V) (u : V) :
    ((pairFiber C i r).filter fun x : CycleTuple V ↦
      x i = u ∨ x (i + 1) = u).card ≤
      2 * hgood.s := by
  let L := (pairFiber C i r).filter (fun x : CycleTuple V ↦ x i = u)
  let R := (pairFiber C i r).filter (fun x : CycleTuple V ↦ x (i + 1) = u)
  have hsubset :
      (pairFiber C i r).filter (fun x : CycleTuple V ↦
        x i = u ∨ x (i + 1) = u) ⊆ L ∪ R := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_union, L, R] at hx ⊢
    exact hx.2.elim (fun h ↦ Or.inl ⟨hx.1, h⟩) (fun h ↦ Or.inr ⟨hx.1, h⟩)
  have hL : L.card ≤ hgood.s :=
    (Finset.card_le_card (pairFiber_filter_left_subset_singleFiber C i r u)).trans
      (hgood.single_card (i + 1) (fillPairLeft i r u))
  have hR : R.card ≤ hgood.s :=
    (Finset.card_le_card (pairFiber_filter_right_subset_singleFiber C i r u)).trans
      (hgood.single_card i (fillPairRight i r u))
  calc
    ((pairFiber C i r).filter fun x : CycleTuple V ↦
      x i = u ∨ x (i + 1) = u).card ≤
        (L ∪ R).card := Finset.card_le_card hsubset
    _ ≤ L.card + R.card := Finset.card_union_le L R
    _ ≤ 2 * hgood.s := by omega

def relevantPairFibers {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) : Finset (Finset (CycleTuple V)) :=
  Finset.univ.biUnion fun i : Fin 56 ↦
    (pairPatterns C i).image (pairFiber C i)

lemma pairFiber_mem_relevantPairFibers_of_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (i : Fin 56) (r : OffPair i → V)
    (hr : (pairFiber C i r).Nonempty) :
    pairFiber C i r ∈ relevantPairFibers C := by
  obtain ⟨x, hx⟩ := hr
  have hxdata := Finset.mem_filter.mp hx
  rw [relevantPairFibers, Finset.mem_biUnion]
  refine ⟨i, Finset.mem_univ i, ?_⟩
  rw [Finset.mem_image]
  refine ⟨restrictOffPair i x, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨x, hxdata.1, rfl⟩
  · exact congrArg (pairFiber C i) hxdata.2

lemma card_relevantPairFibers_le {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) :
    (relevantPairFibers C).card ≤ ∑ i : Fin 56, (pairPatterns C i).card := by
  calc
    (relevantPairFibers C).card ≤
        ∑ i : Fin 56, ((pairPatterns C i).image (pairFiber C i)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ i : Fin 56, (pairPatterns C i).card := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.card_image_le

lemma IsGoodCycleFamily.relevantPairFibers_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {β : ℝ} {C : Finset (CycleTuple V)}
    (hgood : IsGoodCycleFamily G β C) :
    (16 * 7 * hgood.s : ℝ) * (relevantPairFibers C).card ≤
      56 * (β * C.card) := by
  have hcard : ((relevantPairFibers C).card : ℝ) ≤
      ∑ i : Fin 56, ((pairPatterns C i).card : ℝ) := by
    exact_mod_cast card_relevantPairFibers_le C
  calc
    (16 * 7 * hgood.s : ℝ) * (relevantPairFibers C).card ≤
        (16 * 7 * hgood.s : ℝ) *
          ∑ i : Fin 56, ((pairPatterns C i).card : ℝ) := by
      gcongr
    _ = ∑ i : Fin 56,
          (16 * 7 * hgood.s : ℝ) * (pairPatterns C i).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _i : Fin 56, β * C.card := by
      exact Finset.sum_le_sum fun i _ ↦ hgood.pattern_card i
    _ = 56 * (β * C.card) := by simp

/-- Janzer's pruning lemma (Lemma 2.15), specialized to the 56-coordinate
families used for `H_{7,784}`. -/
theorem IsGoodCycleFamily.exists_nice_subfamily {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {β : ℝ} {C : Finset (CycleTuple V)}
    (hgood : IsGoodCycleFamily G β C) (hβ : 0 < β) (hC : C.Nonempty) :
    ∃ C' : Finset (CycleTuple V),
      C' ⊆ C ∧ C'.Nonempty ∧ IsNiceCycleFamily G β C' := by
  let x : ℝ := 2 * hgood.s / β
  let t : ℕ := ⌈x⌉₊
  let fibers := relevantPairFibers C
  have hxpos : 0 < x := by
    dsimp [x]
    have hs : (0 : ℝ) < hgood.s := by exact_mod_cast hgood.s_pos
    positivity
  have htpos : 0 < t := by
    exact Nat.ceil_pos.mpr hxpos
  have htminus : ((t - 1 : ℕ) : ℝ) < x := by
    have htceil := Nat.ceil_lt_add_one hxpos.le
    change (t : ℝ) < x + 1 at htceil
    rw [Nat.cast_sub (by omega : 1 ≤ t)]
    norm_num
    linarith
  have htwo : (2 * hgood.s : ℝ) * (fibers.card : ℝ) ≤ β * C.card := by
    have hrel := hgood.relevantPairFibers_bound
    change (16 * 7 * hgood.s : ℝ) * fibers.card ≤ 56 * (β * C.card) at hrel
    norm_num at hrel ⊢
    nlinarith
  have hratio : (fibers.card : ℝ) * x ≤ C.card := by
    dsimp [x]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hβ).2
    nlinarith
  have hpruneCard : fibers.card * (t - 1) < C.card := by
    by_cases hfibers : fibers.card = 0
    · simp [hfibers, hC.card_pos]
    · have hfibersPos : 0 < (fibers.card : ℝ) := by positivity
      have hstrict : (fibers.card : ℝ) * (t - 1 : ℕ) < (C.card : ℝ) :=
        (mul_lt_mul_of_pos_left htminus hfibersPos).trans_le hratio
      exact_mod_cast hstrict
  obtain ⟨C', hC'subset, hC'card, hC'stable⟩ :=
    exists_pruned_subfamily t C fibers
  have hC'nonempty : C'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.card_empty, zero_add] at hC'card
    omega
  refine ⟨C', hC'subset, hC'nonempty, ?_⟩
  refine ⟨?_, ?_⟩
  · intro y hy
    exact hgood.genuine y (hC'subset hy)
  · intro i r u
    by_cases hpair : (pairFiber C' i r).Nonempty
    · have hpairOriginal : (pairFiber C i r).Nonempty := by
        obtain ⟨y, hy⟩ := hpair
        refine ⟨y, ?_⟩
        have hy' := Finset.mem_filter.mp hy
        exact Finset.mem_filter.mpr ⟨hC'subset hy'.1, hy'.2⟩
      have hmem : pairFiber C i r ∈ fibers := by
        exact pairFiber_mem_relevantPairFibers_of_nonempty C i r hpairOriginal
      have hinter : C' ∩ pairFiber C i r = pairFiber C' i r := by
        ext y
        simp only [pairFiber, Finset.mem_inter, Finset.mem_filter]
        constructor
        · exact fun hy ↦ ⟨hy.1, hy.2.2⟩
        · exact fun hy ↦ ⟨hy.1, hC'subset hy.1, hy.2⟩
      have htcard : t ≤ (pairFiber C' i r).card := by
        rw [← hinter]
        exact hC'stable (pairFiber C i r) hmem (by simpa [hinter] using hpair)
      have hxcard : x ≤ ((pairFiber C' i r).card : ℝ) := by
        exact (Nat.le_ceil x).trans (by exact_mod_cast htcard)
      have hdenom : (2 * hgood.s : ℝ) ≤
          β * (pairFiber C' i r).card := by
        have := mul_le_mul_of_nonneg_left hxcard hβ.le
        dsimp [x] at this
        calc
          (2 * hgood.s : ℝ) = β * ((2 * hgood.s : ℝ) / β) := by
            field_simp
          _ ≤ β * (pairFiber C' i r).card := this
      have heventSubset :
          (pairFiber C' i r).filter (fun y : CycleTuple V ↦
            y i = u ∨ y (i + 1) = u) ⊆
            (pairFiber C i r).filter (fun y : CycleTuple V ↦
              y i = u ∨ y (i + 1) = u) := by
        intro y hy
        simp only [Finset.mem_filter] at hy ⊢
        have hypair := Finset.mem_filter.mp hy.1
        exact ⟨Finset.mem_filter.mpr ⟨hC'subset hypair.1, hypair.2⟩, hy.2⟩
      have hevent :
          ((pairFiber C' i r).filter (fun y : CycleTuple V ↦
            y i = u ∨ y (i + 1) = u)).card ≤
            2 * hgood.s :=
        (Finset.card_le_card heventSubset).trans (hgood.prescribed_pair_card_le i r u)
      have heventReal :
          (((pairFiber C' i r).filter (fun y : CycleTuple V ↦
            y i = u ∨ y (i + 1) = u)).card : ℝ) ≤ (2 * hgood.s : ℝ) := by
        exact_mod_cast hevent
      exact heventReal.trans hdenom
    · have hempty : pairFiber C' i r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpair
      simp [hempty]

/-! ## The explicit Janzer graph -/

/-- There are fourteen matching-pairs of rows in the chosen graph `H_{7,784}`. -/
abbrev Row := Fin 14 × Bool

/-- Splitting a cyclic coordinate of length `1568` into a coordinate modulo `784`
and its parity bit. -/
abbrev Column := ZMod 784 × Bool

/-- The perfect matching between rows `(2i+1,2i+2)`. -/
def matchingRow (r : Row) : Row := (r.1, !r.2)

/-- The row involution used by the nonmatching two-factor.  It fixes the two
boundary rows and pairs every two consecutive interior rows. -/
def turnRow (r : Row) : Row :=
  match r.2 with
  | false => if h : r.1 = 0 then r else (⟨r.1.val - 1, by omega⟩, true)
  | true => if h : r.1 = 13 then r else (⟨r.1.val + 1, by omega⟩, false)

lemma turnRow_involutive (r : Row) : turnRow (turnRow r) = r := by
  decide +revert

/-- Successor on the cyclic coordinate of length `1568`. -/
def nextColumn (c : Column) : Column :=
  match c.2 with
  | false => (c.1, true)
  | true => (c.1 + 1, false)

/-- Predecessor on the cyclic coordinate of length `1568`. -/
def prevColumn (c : Column) : Column :=
  match c.2 with
  | false => (c.1 - 1, true)
  | true => (c.1, false)

/-! ### The 56-cycle interleaving used by the auxiliary graph -/

abbrev SliceTuple (V : Type*) := Row → V

def rowOfFin28 (r : Fin 28) : Row :=
  (⟨r.val / 2, by omega⟩, decide (r.val % 2 = 1))

def interleavingRow (p : Fin 56) : Row :=
  if h : p.val < 28 then rowOfFin28 ⟨p.val, h⟩
  else rowOfFin28 ⟨55 - p.val, by omega⟩

def interleavingUsesLeft (p : Fin 56) : Bool :=
  if p.val < 28 then decide (p.val % 4 < 2)
  else decide ((p.val - 28) % 4 < 2)

def interleavingCoordinate (p : Fin 56) : Bool × Row :=
  (interleavingUsesLeft p, interleavingRow p)

def evalSliceCoordinate {V : Type*} (y z : SliceTuple V) (a : Bool × Row) : V :=
  if a.1 then y a.2 else z a.2

def interleavedCycle {V : Type*} (y z : SliceTuple V) : CycleTuple V :=
  fun p ↦ evalSliceCoordinate y z (interleavingCoordinate p)

lemma interleavingCoordinate_injective : Function.Injective interleavingCoordinate := by
  decide +revert

lemma interleavingCoordinate_bijective : Function.Bijective interleavingCoordinate := by
  apply (Fintype.bijective_iff_injective_and_card interleavingCoordinate).2
  refine ⟨interleavingCoordinate_injective, ?_⟩
  decide

noncomputable def interleavingEquiv : Fin 56 ≃ Bool × Row :=
  Equiv.ofBijective interleavingCoordinate interleavingCoordinate_bijective

noncomputable def sliceOfCycle {V : Type*} (b : Bool) (x : CycleTuple V) :
    SliceTuple V := fun r ↦ x (interleavingEquiv.symm (b, r))

@[simp] lemma interleavingCoordinate_equiv_symm (a : Bool × Row) :
    interleavingCoordinate (interleavingEquiv.symm a) = a :=
  interleavingEquiv.apply_symm_apply a

@[simp] lemma sliceOfCycle_interleavedCycle_left {V : Type*}
    (y z : SliceTuple V) : sliceOfCycle true (interleavedCycle y z) = y := by
  funext r
  simp [sliceOfCycle, interleavedCycle, evalSliceCoordinate]

@[simp] lemma sliceOfCycle_interleavedCycle_right {V : Type*}
    (y z : SliceTuple V) : sliceOfCycle false (interleavedCycle y z) = z := by
  funext r
  simp [sliceOfCycle, interleavedCycle, evalSliceCoordinate]

lemma interleavedCycle_sliceOfCycle {V : Type*} (x : CycleTuple V) :
    interleavedCycle (sliceOfCycle true x) (sliceOfCycle false x) = x := by
  funext p
  have hp : interleavingEquiv.symm (interleavingCoordinate p) = p := by
    apply interleavingCoordinate_injective
    simp
  unfold interleavedCycle evalSliceCoordinate
  split <;> rename_i h
  · change x (interleavingEquiv.symm (true, (interleavingCoordinate p).2)) = x p
    rw [show (true, (interleavingCoordinate p).2) = interleavingCoordinate p by
      ext <;> simp_all, hp]
  · change x (interleavingEquiv.symm (false, (interleavingCoordinate p).2)) = x p
    rw [show (false, (interleavingCoordinate p).2) = interleavingCoordinate p by
      ext <;> simp_all, hp]

def sameSidePairStart (p : Fin 56) : Fin 56 :=
  if interleavingUsesLeft (p + 1) = interleavingUsesLeft p then p else p - 1

lemma sameSidePairStart_spec (p : Fin 56) :
    (sameSidePairStart p = p ∨ sameSidePairStart p + 1 = p) ∧
    interleavingUsesLeft (sameSidePairStart p) = interleavingUsesLeft p ∧
    interleavingUsesLeft (sameSidePairStart p + 1) = interleavingUsesLeft p := by
  decide +revert

@[simp] lemma interleavingUsesLeft_equiv_symm (b : Bool) (r : Row) :
    interleavingUsesLeft (interleavingEquiv.symm (b, r)) = b := by
  have h := congrArg Prod.fst (interleavingCoordinate_equiv_symm (b, r))
  exact h

lemma sliceOfCycle_eq_of_restrictOffPair_eq {V : Type*} (b : Bool)
    (i : Fin 56) {x x' : CycleTuple V}
    (hi : interleavingUsesLeft i ≠ b)
    (hi1 : interleavingUsesLeft (i + 1) ≠ b)
    (hrest : restrictOffPair i x' = restrictOffPair i x) :
    sliceOfCycle b x' = sliceOfCycle b x := by
  funext r
  let p := interleavingEquiv.symm (b, r)
  have hpuse : interleavingUsesLeft p = b := interleavingUsesLeft_equiv_symm b r
  have hpi : p ≠ i := by
    intro h
    apply hi
    rw [← h]
    exact hpuse
  have hpi1 : p ≠ i + 1 := by
    intro h
    apply hi1
    rw [← h]
    exact hpuse
  exact congrFun hrest ⟨p, hpi, hpi1⟩

noncomputable def fixedSliceCycles {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (b : Bool) (y : SliceTuple V) :
    Finset (CycleTuple V) := C.filter fun x ↦ sliceOfCycle b x = y

lemma fixedSliceCycles_pairFiber_subset {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (b : Bool) (y : SliceTuple V)
    (r : Row) (x : CycleTuple V) (hx : x ∈ fixedSliceCycles C b y) :
    pairFiber C (sameSidePairStart (interleavingEquiv.symm (!b, r)))
      (restrictOffPair (sameSidePairStart (interleavingEquiv.symm (!b, r))) x) ⊆
        fixedSliceCycles C b y := by
  intro x' hx'
  let p := interleavingEquiv.symm (!b, r)
  let i := sameSidePairStart p
  have hpuse : interleavingUsesLeft p = !b := interleavingUsesLeft_equiv_symm (!b) r
  have hispec := sameSidePairStart_spec p
  have hiuse : interleavingUsesLeft i = !b := hispec.2.1.trans hpuse
  have hi1use : interleavingUsesLeft (i + 1) = !b := hispec.2.2.trans hpuse
  have hine : interleavingUsesLeft i ≠ b := by
    rw [hiuse]
    cases b <;> decide
  have hi1ne : interleavingUsesLeft (i + 1) ≠ b := by
    rw [hi1use]
    cases b <;> decide
  have hxdata := Finset.mem_filter.mp hx
  have hx'data := Finset.mem_filter.mp hx'
  rw [fixedSliceCycles, Finset.mem_filter]
  refine ⟨hx'data.1, ?_⟩
  calc
    sliceOfCycle b x' = sliceOfCycle b x :=
      sliceOfCycle_eq_of_restrictOffPair_eq b i hine hi1ne hx'data.2
    _ = y := hxdata.2

lemma IsNiceCycleFamily.fixedSliceCycles_coordinate_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {β : ℝ} {C : Finset (CycleTuple V)}
    (hnice : IsNiceCycleFamily G β C) (b : Bool) (y : SliceTuple V)
    (r : Row) (u : V) :
    (((fixedSliceCycles C b y).filter fun x : CycleTuple V ↦
      sliceOfCycle (!b) x r = u).card : ℝ) ≤
      β * (fixedSliceCycles C b y).card := by
  let D := fixedSliceCycles C b y
  let p := interleavingEquiv.symm (!b, r)
  let i := sameSidePairStart p
  let key : CycleTuple V → (OffPair i → V) := restrictOffPair i
  let keys := D.image key
  let E := D.filter fun x : CycleTuple V ↦ sliceOfCycle (!b) x r = u
  have hispec := sameSidePairStart_spec p
  have hfiber (q : OffPair i → V) (hq : q ∈ keys) :
      D.filter (fun x ↦ key x = q) = pairFiber C i q := by
    obtain ⟨w, hwD, hwq⟩ := Finset.mem_image.mp hq
    ext x
    simp only [Finset.mem_filter]
    constructor
    · intro hx
      have hxC := (Finset.mem_filter.mp hx.1).1
      exact Finset.mem_filter.mpr ⟨hxC, hx.2⟩
    · intro hx
      have hxpair := Finset.mem_filter.mp hx
      have hsubset := fixedSliceCycles_pairFiber_subset C b y r w hwD
      have hxD : x ∈ D := hsubset (by
        rw [show restrictOffPair i w = q from hwq]
        exact hx)
      exact ⟨hxD, hxpair.2⟩
  have hlocal (q : OffPair i → V) (hq : q ∈ keys) :
      (((E.filter fun x ↦ key x = q).card : ℕ) : ℝ) ≤
        β * (D.filter fun x ↦ key x = q).card := by
    have hsubset : E.filter (fun x ↦ key x = q) ⊆
        (pairFiber C i q).filter (fun x : CycleTuple V ↦
          x i = u ∨ x (i + 1) = u) := by
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      have hxE := Finset.mem_filter.mp hx'.1
      have hxpair : x ∈ pairFiber C i q := by
        rw [← hfiber q hq]
        exact Finset.mem_filter.mpr ⟨hxE.1, hx'.2⟩
      refine Finset.mem_filter.mpr ⟨hxpair, ?_⟩
      have hxu : x p = u := by
        simpa [p, sliceOfCycle] using hxE.2
      rcases hispec.1 with hpi | hpi
      · exact Or.inl (by simpa [i, hpi] using hxu)
      · exact Or.inr (by simpa [i, hpi] using hxu)
    calc
      (((E.filter fun x ↦ key x = q).card : ℕ) : ℝ) ≤
          (((pairFiber C i q).filter (fun x : CycleTuple V ↦
            x i = u ∨ x (i + 1) = u)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      _ ≤ β * (pairFiber C i q).card := hnice.balanced i q u
      _ = β * (D.filter fun x ↦ key x = q).card := by rw [hfiber q hq]
  have hEcard : E.card = ∑ q ∈ keys, (E.filter fun x ↦ key x = q).card :=
    Finset.card_eq_sum_card_fiberwise fun x hx ↦ by
      exact Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩
  have hDcard : D.card = ∑ q ∈ keys, (D.filter fun x ↦ key x = q).card :=
    Finset.card_eq_sum_card_fiberwise fun x hx ↦
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
  change (E.card : ℝ) ≤ β * D.card
  calc
    (E.card : ℝ) = ∑ q ∈ keys, ((E.filter fun x ↦ key x = q).card : ℝ) := by
      exact_mod_cast hEcard
    _ ≤ ∑ q ∈ keys, β * (D.filter fun x ↦ key x = q).card := by
      exact Finset.sum_le_sum fun q hq ↦ hlocal q hq
    _ = β * ∑ q ∈ keys, ((D.filter fun x ↦ key x = q).card : ℝ) := by
      rw [Finset.mul_sum]
    _ = β * D.card := by rw [← Nat.cast_sum, ← hDcard]

def orientedCycle {V : Type*} (b : Bool) (y z : SliceTuple V) : CycleTuple V :=
  if b then interleavedCycle y z else interleavedCycle z y

@[simp] lemma sliceOfCycle_orientedCycle_fixed {V : Type*}
    (b : Bool) (y z : SliceTuple V) : sliceOfCycle b (orientedCycle b y z) = y := by
  cases b <;> simp [orientedCycle]

@[simp] lemma sliceOfCycle_orientedCycle_free {V : Type*}
    (b : Bool) (y z : SliceTuple V) : sliceOfCycle (!b) (orientedCycle b y z) = z := by
  cases b <;> simp [orientedCycle]

lemma orientedCycle_injective {V : Type*} (b : Bool) (y : SliceTuple V) :
    Function.Injective (orientedCycle b y) := by
  intro z z' h
  have := congrArg (sliceOfCycle (!b)) h
  simpa using this

noncomputable def orientedNeighbors {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (b : Bool) (y : SliceTuple V) :
    Finset (SliceTuple V) :=
  Finset.univ.filter fun z ↦ orientedCycle b y z ∈ C

lemma orientedNeighbors_image {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (b : Bool) (y : SliceTuple V) :
    (orientedNeighbors C b y).image (orientedCycle b y) = fixedSliceCycles C b y := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hz' := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hz'.2, sliceOfCycle_orientedCycle_fixed b y z⟩
  · intro hx
    have hx' := Finset.mem_filter.mp hx
    let z := sliceOfCycle (!b) x
    have hrepr : orientedCycle b y z = x := by
      cases b
      · change interleavedCycle z y = x
        rw [← hx'.2]
        exact interleavedCycle_sliceOfCycle x
      · change interleavedCycle y z = x
        rw [← hx'.2]
        exact interleavedCycle_sliceOfCycle x
    refine Finset.mem_image.mpr ⟨z, ?_, hrepr⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hrepr.symm ▸ hx'.1⟩

lemma card_orientedNeighbors {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (b : Bool) (y : SliceTuple V) :
    (orientedNeighbors C b y).card = (fixedSliceCycles C b y).card := by
  rw [← orientedNeighbors_image C b y, Finset.card_image_iff.mpr]
  exact (orientedCycle_injective b y).injOn

lemma orientedNeighbors_coordinate_card {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (b : Bool) (y : SliceTuple V)
    (r : Row) (u : V) :
    ((orientedNeighbors C b y).filter fun z ↦ z r = u).card =
      ((fixedSliceCycles C b y).filter fun x ↦ sliceOfCycle (!b) x r = u).card := by
  let S := (orientedNeighbors C b y).filter fun z ↦ z r = u
  have himage : S.image (orientedCycle b y) =
      (fixedSliceCycles C b y).filter fun x ↦ sliceOfCycle (!b) x r = u := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hz' := Finset.mem_filter.mp hz
      have hcycle := Finset.mem_filter.mp hz'.1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hcycle.2, sliceOfCycle_orientedCycle_fixed b y z⟩,
          by simpa using hz'.2⟩
    · intro hx
      have hx' := Finset.mem_filter.mp hx
      have hxD := Finset.mem_filter.mp hx'.1
      let z := sliceOfCycle (!b) x
      have hrepr : orientedCycle b y z = x := by
        cases b
        · change interleavedCycle z y = x
          rw [← hxD.2]
          exact interleavedCycle_sliceOfCycle x
        · change interleavedCycle y z = x
          rw [← hxD.2]
          exact interleavedCycle_sliceOfCycle x
      refine Finset.mem_image.mpr ⟨z, ?_, hrepr⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ z, hrepr.symm ▸ hxD.1⟩, hx'.2⟩
  rw [← himage, Finset.card_image_iff.mpr]
  exact (orientedCycle_injective b y).injOn

def CyclicallyAdjacentCoordinates (a b : Bool × Row) : Prop :=
  (List.finRange 56).any (fun p ↦ decide
    ((interleavingCoordinate p = a ∧ interleavingCoordinate (p + 1) = b) ∨
    (interleavingCoordinate p = b ∧ interleavingCoordinate (p + 1) = a))) = true

instance instDecidableCyclicallyAdjacentCoordinates (a b : Bool × Row) :
    Decidable (CyclicallyAdjacentCoordinates a b) := by
  unfold CyclicallyAdjacentCoordinates
  infer_instance

lemma interleaving_left_matching (r : Row) :
    CyclicallyAdjacentCoordinates (true, r) (true, matchingRow r) := by
  rcases r with ⟨i, b⟩
  fin_cases i <;> cases b <;> decide

lemma interleaving_right_matching (r : Row) :
    CyclicallyAdjacentCoordinates (false, r) (false, matchingRow r) := by
  rcases r with ⟨i, b⟩
  fin_cases i <;> cases b <;> decide

lemma interleaving_cross (r : Row) :
    CyclicallyAdjacentCoordinates (true, r) (false, turnRow r) := by
  rcases r with ⟨i, b⟩
  fin_cases i <;> cases b <;> decide

lemma adj_evalSliceCoordinate_of_cyclicallyAdjacent {V : Type*}
    (G : SimpleGraph V) (y z : SliceTuple V)
    (hcycle : ∀ p, G.Adj (interleavedCycle y z p) (interleavedCycle y z (p + 1)))
    {a b : Bool × Row} (hab : CyclicallyAdjacentCoordinates a b) :
    G.Adj (evalSliceCoordinate y z a) (evalSliceCoordinate y z b) := by
  rw [CyclicallyAdjacentCoordinates, List.any_iff_exists_prop] at hab
  obtain ⟨p, _hpMem, hp | hp⟩ := hab
  · simpa [interleavedCycle, hp.1, hp.2] using hcycle p
  · simpa [interleavedCycle, hp.1, hp.2] using (hcycle p).symm

/-- The three edge families between two consecutive columns: the matching in
each column and the row-turning edges between the columns. -/
def CompatibleSlices {V : Type*} (G : SimpleGraph V)
    (y z : SliceTuple V) : Prop :=
  (∀ r, G.Adj (y r) (y (matchingRow r))) ∧
  (∀ r, G.Adj (z r) (z (matchingRow r))) ∧
  (∀ r, G.Adj (y r) (z (turnRow r)))

lemma compatibleSlices_of_interleavedCycle {V : Type*} (G : SimpleGraph V)
    (y z : SliceTuple V) (hcycle : IsGenuineCycleTuple G (interleavedCycle y z)) :
    CompatibleSlices G y z := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    simpa [evalSliceCoordinate] using
      adj_evalSliceCoordinate_of_cyclicallyAdjacent G y z hcycle.2
        (interleaving_left_matching r)
  · intro r
    simpa [evalSliceCoordinate] using
      adj_evalSliceCoordinate_of_cyclicallyAdjacent G y z hcycle.2
        (interleaving_right_matching r)
  · intro r
    simpa [evalSliceCoordinate] using
      adj_evalSliceCoordinate_of_cyclicallyAdjacent G y z hcycle.2
        (interleaving_cross r)

lemma CompatibleSlices.symm {V : Type*} {G : SimpleGraph V}
    {y z : SliceTuple V} (h : CompatibleSlices G y z) : CompatibleSlices G z y := by
  refine ⟨h.2.1, h.1, ?_⟩
  intro r
  have hr := h.2.2 (turnRow r)
  rw [turnRow_involutive] at hr
  exact hr.symm

lemma interleavedCycle_self_not_injective {V : Type*} (y : SliceTuple V) :
    ¬ Function.Injective (interleavedCycle y y) := by
  intro hinj
  have heq : interleavedCycle y y (0 : Fin 56) = interleavedCycle y y (55 : Fin 56) := by
    rfl
  have hindex := hinj heq
  have hval := congrArg Fin.val hindex
  norm_num at hval

lemma evalSliceCoordinate_injective_of_interleavedCycle {V : Type*}
    {G : SimpleGraph V} {y z : SliceTuple V}
    (hcycle : IsGenuineCycleTuple G (interleavedCycle y z)) :
    Function.Injective (evalSliceCoordinate y z) := by
  intro a b hab
  obtain ⟨p, hp⟩ := interleavingCoordinate_bijective.2 a
  obtain ⟨q, hq⟩ := interleavingCoordinate_bijective.2 b
  rw [← hp, ← hq] at hab ⊢
  exact congrArg interleavingCoordinate (hcycle.1 hab)

/-- Two auxiliary vertices conflict if some coordinate of one equals some
coordinate of the other. -/
def SlicesConflict {V : Type*} (y z : SliceTuple V) : Prop :=
  ∃ r s : Row, y r = z s

lemma SlicesConflict.symm {V : Type*} {y z : SliceTuple V}
    (h : SlicesConflict y z) : SlicesConflict z y := by
  obtain ⟨r, s, hrs⟩ := h
  exact ⟨s, r, hrs.symm⟩

/-- The auxiliary graph in Janzer's Lemma 2.16: two row-slices are adjacent
when one of the two oriented interleavings belongs to the cycle family. -/
def auxiliaryGraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Finset (CycleTuple V))
    (hfamily : ∀ x ∈ C, IsGenuineCycleTuple G x) : SimpleGraph (SliceTuple V) where
  Adj y z := interleavedCycle y z ∈ C ∨ interleavedCycle z y ∈ C
  symm := ⟨by aesop⟩
  loopless := ⟨by
    intro y hy
    rcases hy with hy | hy
    · exact interleavedCycle_self_not_injective y (hfamily _ hy).1
    · exact interleavedCycle_self_not_injective y (hfamily _ hy).1⟩

instance auxiliaryGraph.instDecidableRel {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Finset (CycleTuple V))
    (hfamily : ∀ x ∈ C, IsGenuineCycleTuple G x) :
    DecidableRel (auxiliaryGraph G C hfamily).Adj := fun y z ↦ by
  change Decidable (interleavedCycle y z ∈ C ∨ interleavedCycle z y ∈ C)
  infer_instance

lemma auxiliaryGraph_neighborFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Finset (CycleTuple V))
    (hfamily : ∀ x ∈ C, IsGenuineCycleTuple G x) (y : SliceTuple V) :
    (auxiliaryGraph G C hfamily).neighborFinset y =
      orientedNeighbors C true y ∪ orientedNeighbors C false y := by
  ext z
  rw [SimpleGraph.mem_neighborFinset]
  change (interleavedCycle y z ∈ C ∨ interleavedCycle z y ∈ C) ↔ _
  simp [orientedNeighbors, orientedCycle]

lemma orientedNeighbors_subset_auxiliary_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Finset (CycleTuple V))
    (hfamily : ∀ x ∈ C, IsGenuineCycleTuple G x) (b : Bool) (y : SliceTuple V) :
    orientedNeighbors C b y ⊆ (auxiliaryGraph G C hfamily).neighborFinset y := by
  rw [auxiliaryGraph_neighborFinset G C hfamily y]
  cases b
  · exact Finset.subset_union_right
  · exact Finset.subset_union_left

lemma IsNiceCycleFamily.auxiliary_coordinate_conflict_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {β : ℝ} {C : Finset (CycleTuple V)}
    (hnice : IsNiceCycleFamily G β C) (hβ : 0 ≤ β)
    (y : SliceTuple V) (r : Row) (u : V) :
    ((((auxiliaryGraph G C hnice.genuine).neighborFinset y).filter fun z ↦
      z r = u).card : ℝ) ≤
      2 * β * (auxiliaryGraph G C hnice.genuine).degree y := by
  let A := auxiliaryGraph G C hnice.genuine
  let E (b : Bool) := (orientedNeighbors C b y).filter fun z ↦ z r = u
  have hlocal (b : Bool) : (E b).card ≤ β * A.degree y := by
    calc
      ((E b).card : ℝ) =
          (((fixedSliceCycles C b y).filter fun x : CycleTuple V ↦
            sliceOfCycle (!b) x r = u).card : ℝ) := by
        exact_mod_cast orientedNeighbors_coordinate_card C b y r u
      _ ≤ β * (fixedSliceCycles C b y).card :=
        hnice.fixedSliceCycles_coordinate_bound b y r u
      _ = β * (orientedNeighbors C b y).card := by
        rw [card_orientedNeighbors C b y]
      _ ≤ β * A.degree y := by
        apply mul_le_mul_of_nonneg_left _ hβ
        exact_mod_cast Finset.card_le_card
          (orientedNeighbors_subset_auxiliary_neighborFinset G C hnice.genuine b y)
  have hsubset : (A.neighborFinset y).filter (fun z ↦ z r = u) ⊆ E true ∪ E false := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    rw [auxiliaryGraph_neighborFinset G C hnice.genuine y] at hz'
    rcases Finset.mem_union.mp hz'.1 with hz | hz
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hz'.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, hz'.2⟩)
  calc
    (((A.neighborFinset y).filter (fun z ↦ z r = u)).card : ℝ) ≤
        ((E true ∪ E false).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ (E true).card + (E false).card := by
      exact_mod_cast Finset.card_union_le (E true) (E false)
    _ ≤ β * A.degree y + β * A.degree y := add_le_add (hlocal true) (hlocal false)
    _ = 2 * β * A.degree y := by ring

noncomputable instance instDecidableSlicesConflict {V : Type*}
    (x y : SliceTuple V) : Decidable (SlicesConflict x y) :=
  Classical.propDecidable _

noncomputable def conflictingNeighbors {V : Type*} [Fintype V]
    (A : SimpleGraph (SliceTuple V)) [DecidableRel A.Adj]
    (x y : SliceTuple V) : Finset (SliceTuple V) :=
  (A.neighborFinset y).filter (SlicesConflict x)

lemma IsNiceCycleFamily.auxiliary_conflicting_neighbors_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {β : ℝ} {C : Finset (CycleTuple V)}
    (hnice : IsNiceCycleFamily G β C) (hβ : 0 ≤ β)
    (x y : SliceTuple V) :
    ((conflictingNeighbors (auxiliaryGraph G C hnice.genuine) x y).card : ℝ) ≤
      1568 * β * (auxiliaryGraph G C hnice.genuine).degree y := by
  let A := auxiliaryGraph G C hnice.genuine
  let E (r s : Row) := (A.neighborFinset y).filter fun z ↦ z s = x r
  let U := Finset.univ.biUnion fun r : Row ↦
    Finset.univ.biUnion fun s : Row ↦ E r s
  have hsubset : conflictingNeighbors A x y ⊆ U := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    obtain ⟨r, s, hrs⟩ := hz'.2
    simp only [U, Finset.mem_biUnion]
    refine ⟨r, Finset.mem_univ r, ?_⟩
    exact ⟨s, Finset.mem_univ s, Finset.mem_filter.mpr ⟨hz'.1, hrs.symm⟩⟩
  have hUcard : (U.card : ℝ) ≤
      ∑ r : Row, ∑ s : Row, ((E r s).card : ℝ) := by
    calc
      (U.card : ℝ) ≤
          (∑ r : Row, (Finset.univ.biUnion fun s : Row ↦ E r s).card : ℕ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ r : Row, ∑ s : Row, ((E r s).card : ℝ) := by
        rw [Nat.cast_sum]
        apply Finset.sum_le_sum
        intro r _
        exact_mod_cast Finset.card_biUnion_le
  calc
    ((conflictingNeighbors A x y).card : ℝ) ≤ (U.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ r : Row, ∑ s : Row, ((E r s).card : ℝ) := hUcard
    _ ≤ ∑ _r : Row, ∑ _s : Row, 2 * β * A.degree y := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro s _
      exact hnice.auxiliary_coordinate_conflict_bound hβ y s (x r)
    _ = 1568 * β * A.degree y := by
      norm_num [Fintype.card_congr (Equiv.prodComm (Fin 14) Bool)]
      ring

noncomputable def relationNeighbors {W : Type*} [Fintype W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (x y : W) : Finset W :=
  (A.neighborFinset y).filter (R x)

noncomputable def cleanSelectorThreshold (N : ℕ) : ℝ :=
  (2 ^ (28 : ℕ) * 784 ^ (3 : ℕ) * (Real.log N) ^ (4 : ℕ) *
    (N : ℝ) ^ ((1 : ℝ) / 784))⁻¹

@[simp] lemma card_Row : Fintype.card Row = 28 := by decide

@[simp] lemma card_sliceTuple_fin (n : ℕ) :
    Fintype.card (SliceTuple (Fin n)) = n ^ 28 := by
  simp [SliceTuple]

lemma log_four_isLittleO_rpow_one_div_twentyEight :
    (fun n : ℕ ↦ Real.log (n : ℝ) ^ (4 : ℕ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 28)) := by
  have h := (isLittleO_log_rpow_atTop
    (r := (1 : ℝ) / 112) (by norm_num)).pow (by omega : 0 < (4 : ℕ))
  have hn := h.natCast_atTop
  apply hn.congr_right
  intro n
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

lemma eventually_log_pow_scaled_lt_rpow (K : ℝ) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop,
      K * Real.log (n : ℝ) ^ (4 : ℕ) < (n : ℝ) ^ ((1 : ℝ) / 28) := by
  have h := log_four_isLittleO_rpow_one_div_twentyEight.const_mul_left K
  have hb := h.bound (c := (1 : ℝ) / 2) (by norm_num)
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hrpow : 0 < (n : ℝ) ^ ((1 : ℝ) / 28) :=
    Real.rpow_pos_of_pos (by positivity) _
  rw [abs_of_nonneg (mul_nonneg hK.le (pow_nonneg hlog 4)),
    abs_of_pos hrpow] at hn
  nlinarith

/-- The precise analytic inequality needed to apply the selector to a nice
family with `β = n⁻¹ʲ¹⁴`.  The auxiliary vertex set has cardinality
`n²⁸`, while its local conflict factor is `1568β`. -/
lemma eventually_cleanSelectorThreshold :
    ∀ᶠ n : ℕ in atTop,
      1568 * (n : ℝ) ^ (-(1 : ℝ) / 14) <
        cleanSelectorThreshold (Fintype.card (SliceTuple (Fin n))) := by
  let K : ℝ := 1568 * 2 ^ (28 : ℕ) * 784 ^ (3 : ℕ) * 28 ^ (4 : ℕ)
  have hK : 0 < K := by positivity
  filter_upwards [eventually_log_pow_scaled_lt_rpow K hK,
    eventually_ge_atTop (2 : ℕ)] with n hgrowth hn
  rw [card_sliceTuple_fin, cleanSelectorThreshold]
  have hnpos : 0 < (n : ℝ) := by positivity
  have hnpow : ((n ^ 28 : ℕ) : ℝ) = (n : ℝ) ^ (28 : ℕ) := by norm_cast
  rw [hnpow, Real.log_pow]
  have hrpowpow : (((n : ℝ) ^ (28 : ℕ)) ^ ((1 : ℝ) / 784)) =
      (n : ℝ) ^ ((1 : ℝ) / 28) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hnpos.le]
    norm_num
  rw [hrpowpow]
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hrightpos : 0 < (n : ℝ) ^ ((1 : ℝ) / 28) :=
    Real.rpow_pos_of_pos hnpos _
  let D : ℝ :=
      2 ^ (28 : ℕ) * 784 ^ (3 : ℕ) *
        (28 * Real.log (n : ℝ)) ^ (4 : ℕ) *
          (n : ℝ) ^ ((1 : ℝ) / 28)
  change 1568 * (n : ℝ) ^ (-(1 : ℝ) / 14) < D⁻¹
  have hdenpos : 0 < D := by dsimp [D]; positivity
  rw [← mul_one D⁻¹, lt_inv_mul_iff₀' hdenpos]
  dsimp [D]
  have hneg : (n : ℝ) ^ (-(1 : ℝ) / 14) *
      (n : ℝ) ^ ((1 : ℝ) / 28) =
        (n : ℝ) ^ (-(1 : ℝ) / 28) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  rw [show 1568 * (n : ℝ) ^ (-(1 : ℝ) / 14) *
        (2 ^ (28 : ℕ) * 784 ^ (3 : ℕ) *
          (28 * Real.log (n : ℝ)) ^ (4 : ℕ) *
            (n : ℝ) ^ ((1 : ℝ) / 28)) =
      K * Real.log (n : ℝ) ^ (4 : ℕ) *
        (n : ℝ) ^ (-(1 : ℝ) / 28) by
      rw [mul_pow, ← hneg]
      dsimp [K]
      ring]
  rw [show (-(1 : ℝ) / 28) = -((1 : ℝ) / 28) by ring,
    Real.rpow_neg hnpos.le]
  calc
    K * Real.log (n : ℝ) ^ 4 * ((n : ℝ) ^ ((1 : ℝ) / 28))⁻¹ <
        (n : ℝ) ^ ((1 : ℝ) / 28) *
          ((n : ℝ) ^ ((1 : ℝ) / 28))⁻¹ :=
      mul_lt_mul_of_pos_right hgrowth (inv_pos.mpr hrightpos)
    _ = 1 := mul_inv_cancel₀ hrightpos.ne'

/-! ### Spectral interpolation for the selector

The conflict count uses the number of closed walks of lengths `1566` and
`1568`.  The following is the exact finite-dimensional Schatten-moment
interpolation used in Janzer's Lemma 2.2, proved from the spectral theorem
and Hölder's inequality. -/

lemma trace_pow_eq_sum_eigenvalues_pow {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (j : ℕ) :
    Matrix.trace (A ^ j) = ∑ i, hA.eigenvalues i ^ j := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle]
  simp [Matrix.diagonal_pow]

noncomputable def closedWalkCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) : ℕ :=
  ∑ x : W, Fintype.card {p : A.Walk x x // p.length = m}

lemma closedWalkCount_cast_eq_trace {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) :
    (closedWalkCount A m : ℝ) = Matrix.trace (A.adjMatrix ℝ ^ m) := by
  rw [closedWalkCount, Nat.cast_sum, Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.diag_apply, A.adjMatrix_pow_apply_eq_card_walk]
  norm_cast

lemma closedWalkCount_cast_eq_sum_eigenvalues_pow {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) :
    (closedWalkCount A m : ℝ) =
      ∑ i, ((A.isHermitian_adjMatrix ℝ).eigenvalues i) ^ m := by
  rw [closedWalkCount_cast_eq_trace]
  exact trace_pow_eq_sum_eigenvalues_pow _ _ _

lemma closedWalkCount_interpolation_784 {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj] :
    (closedWalkCount A 1566 : ℝ) ≤
      (Fintype.card W : ℝ) ^ ((1 : ℝ) / 784) *
        (closedWalkCount A 1568 : ℝ) ^ ((783 : ℝ) / 784) := by
  let hA := A.isHermitian_adjMatrix ℝ
  let lam : W → ℝ := hA.eigenvalues
  have hholder : Real.HolderConjugate (784 : ℝ) ((784 : ℝ) / 783) := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg
    (s := Finset.univ) (f := fun _ : W ↦ (1 : ℝ))
    (g := fun i : W ↦ (lam i ^ 2) ^ (783 : ℕ)) hholder
    (by intro i hi; positivity) (by intro i hi; positivity)
  dsimp [hA, lam] at hh
  have hleft (x : ℝ) : x ^ 1566 = (x ^ 2) ^ 783 := by ring
  have hright (x : ℝ) :
      ((x ^ 2) ^ (783 : ℕ)) ^ ((784 : ℝ) / 783) = x ^ 1568 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (sq_nonneg x)]
    norm_num
    ring
  simp_rw [hright] at hh
  simp_rw [← hleft] at hh
  rw [closedWalkCount_cast_eq_sum_eigenvalues_pow,
    closedWalkCount_cast_eq_sum_eigenvalues_pow]
  simp only [one_mul, Real.one_rpow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hh
  convert hh using 1 <;> norm_num

def columnLinearIndex (c : Column) : Fin 1568 :=
  ⟨2 * c.1.val + if c.2 then 1 else 0, by
    have hc := ZMod.val_lt c.1
    split <;> omega⟩

def cyclicSucc1568 (i : Fin 1568) : Fin 1568 :=
  ⟨(i.val + 1) % 1568, Nat.mod_lt _ (by omega)⟩

lemma cyclicSucc1568_columnLinearIndex (c : Column) :
    cyclicSucc1568 (columnLinearIndex c) =
      columnLinearIndex (nextColumn c) := by
  rcases c with ⟨j, b⟩
  cases b
  · apply Fin.ext
    change (2 * j.val + 0 + 1) % 1568 = 2 * j.val + 1
    rw [Nat.mod_eq_of_lt]
    have hj := ZMod.val_lt j
    omega
  · apply Fin.ext
    change (2 * j.val + 1 + 1) % 1568 = 2 * (j + 1).val + 0
    rw [ZMod.val_add]
    change (2 * j.val + 1 + 1) % 1568 = 2 * ((j.val + 1) % 784)
    omega

lemma columnLinearIndex_injective : Function.Injective columnLinearIndex := by
  rintro ⟨j, b⟩ ⟨k, d⟩ h
  have hv : 2 * j.val + (if b then 1 else 0) =
      2 * k.val + (if d then 1 else 0) := congrArg Fin.val h
  cases b <;> cases d
  · apply Prod.ext
    · apply ZMod.val_injective 784
      simpa using hv
    · rfl
  · simp at hv
    omega
  · simp at hv
    omega
  · apply Prod.ext
    · apply ZMod.val_injective 784
      simp at hv
      omega
    · rfl

lemma columnLinearIndex_bijective : Function.Bijective columnLinearIndex := by
  apply (Fintype.bijective_iff_injective_and_card columnLinearIndex).2
  exact ⟨columnLinearIndex_injective, by simp [Column]⟩

noncomputable def columnLinearEquiv : Column ≃ Fin 1568 :=
  Equiv.ofBijective columnLinearIndex columnLinearIndex_bijective

@[simp] lemma columnLinearEquiv_apply (c : Column) :
    columnLinearEquiv c = columnLinearIndex c := rfl

/-! Closed walks are a second, counting-friendly representation of the same
homomorphic `1568`-cycles.  Unlike a raw function on `Fin 1568`, Mathlib's
walk type splits canonically into shorter walks, which is what the proof of
the conflict estimate needs. -/

abbrev ClosedWalk1568 {W : Type*} (A : SimpleGraph W) :=
  Σ x : W, {p : A.Walk x x // p.length = 1568}

lemma card_ClosedWalk1568 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] :
    Fintype.card (ClosedWalk1568 A) = closedWalkCount A 1568 := by
  simp [ClosedWalk1568, closedWalkCount, Fintype.card_sigma]

def closedWalkVertex1568 {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (i : Fin 1568) : W :=
  P.2.1.getVert i.val

lemma closedWalkVertex1568_adj_succ {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (i : Fin 1568) :
    A.Adj (closedWalkVertex1568 P i)
      (closedWalkVertex1568 P (cyclicSucc1568 i)) := by
  have hi : i.val < P.2.1.length := by rw [P.2.2]; exact i.isLt
  have hadj := P.2.1.adj_getVert_succ hi
  by_cases hwrap : i.val + 1 < 1568
  · simpa [closedWalkVertex1568, cyclicSucc1568,
      Nat.mod_eq_of_lt hwrap] using hadj
  · have hilast : i.val = 1567 := by omega
    have hend : P.2.1.getVert 1568 = P.1 := by
      simpa only [P.2.2] using P.2.1.getVert_length
    have hstart : P.2.1.getVert 0 = P.1 := P.2.1.getVert_zero
    simpa [closedWalkVertex1568, cyclicSucc1568, hilast, hend, hstart] using hadj

def HasClosedWalkConflict1568 {W : Type*} {A : SimpleGraph W}
    (R : W → W → Prop) (P : ClosedWalk1568 A) : Prop :=
  ∃ i j, i ≠ j ∧
    R (closedWalkVertex1568 P i) (closedWalkVertex1568 P j)

noncomputable def badClosedWalks1568 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] : Finset (ClosedWalk1568 A) := by
  classical
  exact Finset.univ.filter (HasClosedWalkConflict1568 R)

@[simp] lemma mem_badClosedWalks1568 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (P : ClosedWalk1568 A) :
    P ∈ badClosedWalks1568 A R ↔ HasClosedWalkConflict1568 R P := by
  classical
  simp [badClosedWalks1568]

lemma exists_pairwise_nonconflicting_column_cycle_of_badClosedWalks_lt
    {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hcard : (badClosedWalks1568 A R).card < closedWalkCount A 1568) :
    ∃ X : Column → W,
      (∀ c, A.Adj (X c) (X (nextColumn c))) ∧
      ∀ c d, c ≠ d → ¬ R (X c) (X d) := by
  classical
  have htotal : (Finset.univ : Finset (ClosedWalk1568 A)).card =
      closedWalkCount A 1568 := by
    rw [Finset.card_univ, card_ClosedWalk1568]
  have hnsubset : ¬ (Finset.univ : Finset (ClosedWalk1568 A)) ⊆
      badClosedWalks1568 A R := by
    intro hsubset
    have := Finset.card_le_card hsubset
    rw [htotal] at this
    omega
  obtain ⟨P, _hPuniv, hPgood⟩ := Finset.not_subset.mp hnsubset
  let X : Column → W := fun c ↦ closedWalkVertex1568 P (columnLinearIndex c)
  refine ⟨X, ?_, ?_⟩
  · intro c
    simpa only [X, ← cyclicSucc1568_columnLinearIndex] using
      closedWalkVertex1568_adj_succ P (columnLinearIndex c)
  · intro c d hcd hR
    apply hPgood
    rw [mem_badClosedWalks1568]
    refine ⟨columnLinearIndex c, columnLinearIndex d,
      fun h ↦ hcd (columnLinearIndex_injective h), ?_⟩
    exact hR

lemma card_badClosedWalks1568_eq {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :
    (badClosedWalks1568 A R).card =
      Fintype.card (Encode.BadClosedWalk1568 A R) := by
  classical
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  exact
    { toFun := fun p ↦ ⟨p.1, by
        have hp := (mem_badClosedWalks1568 A R p.1).mp p.2
        exact hp⟩
      invFun := fun p ↦ ⟨p.1, by
        apply (mem_badClosedWalks1568 A R p.1).mpr
        exact p.2⟩
      left_inv := by intro p; apply Subtype.ext; rfl
      right_inv := by intro p; apply Subtype.ext; rfl }

lemma badClosedWalks1568_side_cast_le {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t D s : Bool → ℝ)
    (ht : ∀ b, 0 < t b) (hD : ∀ b, 0 ≤ D b) (hs : ∀ b, 0 ≤ s b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D (side x))
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y,
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s (side y)) :
    ((badClosedWalks1568 A R).card : ℝ) ≤
      1568 * ∑ b : Bool,
        (D b * t b * (closedWalkCount A 1566 : ℝ) +
          784 * s (!b) * (t b)⁻¹ * (closedWalkCount A 1568 : ℝ)) := by
  rw [card_badClosedWalks1568_eq]
  simpa only [Erdos113.closedWalkCount, Conflict.closedWalkCount,
    Conflict.walkCount] using
      Erdos113Sides.card_BadClosedWalk1568_side_cast_le
        A R side t D s ht hD hs hcross hdegree hsymm hlocal

lemma exists_cleanCycle_of_bipartiteAlmostRegular
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hR : ∀ x y, R x y → R y x)
    (side : W → Bool) (d D : Bool → ℝ) (N L α : ℝ)
    (hN : N = Fintype.card W)
    (hd : ∀ b, 0 < d b) (hD : ∀ b, 0 < D b)
    (hL : 0 < L) (hα : 0 ≤ α)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hmin : ∀ x, d (side x) ≤ (A.degree x : ℝ))
    (hmax : ∀ x, (A.degree x : ℝ) ≤ D (side x))
    (hreg : ∀ b, D b ≤ L * d b)
    (hlocal : ∀ u y,
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ α * D (side y))
    (hsmall : α <
      (4 * 1568 * 784 * 6272 * L ^ 2 * N ^ ((1 : ℝ) / 784))⁻¹) :
    ∃ X : Column → W,
      (∀ c, A.Adj (X c) (X (nextColumn c))) ∧
      ∀ c e, c ≠ e → ¬ R (X c) (X e) := by
  have hNpos : 0 < N := by rw [hN]; positivity
  let Q : ℝ := N ^ ((1 : ℝ) / 784)
  have hQ : 0 < Q := Real.rpow_pos_of_pos hNpos _
  let t : Bool → ℝ := fun b ↦ D (!b) / (6272 * L ^ 2 * Q)
  have ht : ∀ b, 0 < t b := by
    intro b
    dsimp [t]
    exact div_pos (hD (!b)) (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hL)) hQ)
  let H : ℝ := Erdos113.closedWalkCount A 1568
  let H' : ℝ := Erdos113.closedWalkCount A 1566
  let p : ℝ := d false * d true
  have hp : 0 < p := by exact mul_pos (hd false) (hd true)
  have hHlower : p ^ 784 ≤ H := by
    dsimp [H, p]
    simpa only [Erdos113.closedWalkCount, Conflict.closedWalkCount,
      Conflict.walkCount] using
      Erdos113LowerBipartite.closedWalkCount_1568_lower_bipartite
        A side d (fun b ↦ (hd b).le) hcross hmin
  have hHpos : 0 < H := lt_of_lt_of_le (by positivity : 0 < p ^ 784) hHlower
  have hinterp : H' ≤ Q * H ^ ((783 : ℝ) / 784) := by
    dsimp [H', Q, H]
    simpa [hN] using Erdos113.closedWalkCount_interpolation_784 A
  have hrootid : H ^ ((783 : ℝ) / 784) * H ^ ((1 : ℝ) / 784) = H := by
    rw [← Real.rpow_add hHpos]
    norm_num
  have hproot : p ≤ H ^ ((1 : ℝ) / 784) := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ p ^ 784) hHlower
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 784)
    convert h using 1
    conv_rhs => rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hp.le]
    norm_num
  have hHp : H' * p ≤ Q * H := by
    calc
      H' * p ≤ (Q * H ^ ((783 : ℝ) / 784)) * p := by gcongr
      _ ≤ (Q * H ^ ((783 : ℝ) / 784)) *
          H ^ ((1 : ℝ) / 784) := by gcongr
      _ = Q * (H ^ ((783 : ℝ) / 784) * H ^ ((1 : ℝ) / 784)) := by ring
      _ = Q * H := by rw [hrootid]
  have hDprod : D false * D true ≤ L ^ 2 * p := by
    calc
      D false * D true ≤ (L * d false) * (L * d true) :=
        mul_le_mul (hreg false) (hreg true) (hD true).le
          (mul_nonneg hL.le (hd false).le)
      _ = L ^ 2 * p := by dsimp [p]; ring
  have hfirst : 1568 *
      (∑ b : Bool, D b * t b * H') ≤ H / 2 := by
    have hden : 0 < 6272 * L ^ 2 * Q := by positivity
    have hcore : D false * D true * H' ≤ L ^ 2 * Q * H := by
      calc
        D false * D true * H' ≤ (L ^ 2 * p) * H' := by
          gcongr
        _ = L ^ 2 * (H' * p) := by ring
        _ ≤ L ^ 2 * (Q * H) := by gcongr
        _ = L ^ 2 * Q * H := by ring
    simp only [Fintype.sum_bool]
    dsimp [t]
    simp only [Bool.not_false, Bool.not_true]
    have hquot : (D false * D true * H') / (L ^ 2 * Q) ≤ H := by
      apply (div_le_iff₀ (by positivity : 0 < L ^ 2 * Q)).2
      simpa [mul_assoc, mul_left_comm, mul_comm] using hcore
    have heq : 1568 *
        (D false * (D true / (6272 * L ^ 2 * Q)) * H' +
          D true * (D false / (6272 * L ^ 2 * Q)) * H') =
        (1 / 2 : ℝ) * ((D false * D true * H') / (L ^ 2 * Q)) := by
      field_simp
      <;> ring
    rw [show 1568 *
        (D true * (D false / (6272 * L ^ 2 * Q)) * H' +
          D false * (D true / (6272 * L ^ 2 * Q)) * H') =
        (1 / 2 : ℝ) * ((D false * D true * H') / (L ^ 2 * Q)) by
      simpa [add_comm] using heq]
    nlinarith
  have hcoef : 1568 * 784 *
      (∑ b : Bool, (α * D (!b)) * (t b)⁻¹) < (1 : ℝ) / 2 := by
    have hbound : α *
        (4 * 1568 * 784 * 6272 * L ^ 2 * Q) < 1 := by
      have hdenpos : 0 < 4 * 1568 * 784 * 6272 * L ^ 2 * Q := by positivity
      apply (lt_inv_mul_iff₀' hdenpos).mp
      simpa [Q] using hsmall
    simp only [Fintype.sum_bool]
    have htfalse : (t false)⁻¹ = (6272 * L ^ 2 * Q) / D true := by
      dsimp [t]
      rw [Bool.not_false]
      rw [inv_div]
    have httrue : (t true)⁻¹ = (6272 * L ^ 2 * Q) / D false := by
      dsimp [t]
      rw [Bool.not_true]
      rw [inv_div]
    have htermfalse : (α * D true) * (t false)⁻¹ =
        α * (6272 * L ^ 2 * Q) := by
      rw [htfalse]
      field_simp [(hD true).ne']
    have htermtrue : (α * D false) * (t true)⁻¹ =
        α * (6272 * L ^ 2 * Q) := by
      rw [httrue]
      field_simp [(hD false).ne']
    simp only [Bool.not_true, Bool.not_false]
    rw [htermtrue, htermfalse]
    nlinarith
  have hsecond : 1568 *
      (∑ b : Bool, 784 * (α * D (!b)) * (t b)⁻¹ * H) < H / 2 := by
    have heq : 1568 *
        (∑ b : Bool, 784 * (α * D (!b)) * (t b)⁻¹ * H) =
        (1568 * 784 * (∑ b : Bool, (α * D (!b)) * (t b)⁻¹)) * H := by
      simp only [Fintype.sum_bool]
      ring
    rw [heq]
    nlinarith
  have hbad := badClosedWalks1568_side_cast_le A R side t D
    (fun b ↦ α * D b) ht (fun b ↦ (hD b).le)
      (fun b ↦ mul_nonneg hα (hD b).le) hcross hmax hR hlocal
  have hbadlt : ((badClosedWalks1568 A R).card : ℝ) < H := by
    calc
      ((badClosedWalks1568 A R).card : ℝ) ≤
          1568 * ∑ b : Bool,
            (D b * t b * H' +
              784 * (α * D (!b)) * (t b)⁻¹ * H) := by
        simpa [H, H'] using hbad
      _ = 1568 * (∑ b : Bool, D b * t b * H') +
          1568 * (∑ b : Bool,
            784 * (α * D (!b)) * (t b)⁻¹ * H) := by
        simp only [Fintype.sum_bool]
        ring
      _ < H / 2 + H / 2 := add_lt_add_of_le_of_lt hfirst hsecond
      _ = H := by ring
  apply exists_pairwise_nonconflicting_column_cycle_of_badClosedWalks_lt
  dsimp [H] at hbadlt
  exact_mod_cast hbadlt

abbrev BlockedAuxiliaryColumnCycle (W : Type u) := Fin 98 → Fin 16 → W

noncomputable def blockedAuxiliaryColumnCycleEquiv (W : Type u) :
    BlockedAuxiliaryColumnCycle W ≃ (Column → W) :=
  (Equiv.curry (Fin 98) (Fin 16) W).symm.trans <|
    Equiv.arrowCongr (finProdFinEquiv.trans columnLinearEquiv.symm) (Equiv.refl W)

def evalBlockedAuxiliaryColumnCycle {W : Type u}
    (P : BlockedAuxiliaryColumnCycle W) (c : Column) : W :=
  P ⟨(columnLinearIndex c).val / 16, by
      have hc := (columnLinearIndex c).isLt
      omega⟩
    ⟨(columnLinearIndex c).val % 16, Nat.mod_lt _ (by omega)⟩

@[simp] lemma blockedAuxiliaryColumnCycleEquiv_apply {W : Type u}
    (P : BlockedAuxiliaryColumnCycle W) (c : Column) :
    blockedAuxiliaryColumnCycleEquiv W P c = evalBlockedAuxiliaryColumnCycle P c := by
  change Function.uncurry P (finProdFinEquiv.symm (columnLinearIndex c)) = _
  rw [finProdFinEquiv_symm_apply]
  rfl

def IsHomBlockedAuxiliaryColumnCycle {W : Type u}
    (A : SimpleGraph W) (P : BlockedAuxiliaryColumnCycle W) : Prop :=
  ∀ c, A.Adj (evalBlockedAuxiliaryColumnCycle P c)
    (evalBlockedAuxiliaryColumnCycle P (nextColumn c))

def HasBlockedAuxiliaryColumnConflict {W : Type u}
    (R : W → W → Prop) (P : BlockedAuxiliaryColumnCycle W) : Prop :=
  ∃ c d, c ≠ d ∧
    R (evalBlockedAuxiliaryColumnCycle P c) (evalBlockedAuxiliaryColumnCycle P d)

noncomputable def homAuxiliaryColumnCycles {W : Type u} [Fintype W]
    (A : SimpleGraph W) [DecidableRel A.Adj] :
    Finset (BlockedAuxiliaryColumnCycle W) :=
  by classical exact Finset.univ.filter (IsHomBlockedAuxiliaryColumnCycle A)

noncomputable def badAuxiliaryColumnCycles {W : Type u} [Fintype W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :
    Finset (BlockedAuxiliaryColumnCycle W) :=
  by classical exact
    (homAuxiliaryColumnCycles A).filter (HasBlockedAuxiliaryColumnConflict R)

@[simp] lemma mem_homAuxiliaryColumnCycles {W : Type u} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (P : BlockedAuxiliaryColumnCycle W) :
    P ∈ homAuxiliaryColumnCycles A ↔
      IsHomBlockedAuxiliaryColumnCycle A P := by
  classical
  simp [homAuxiliaryColumnCycles]

@[simp] lemma mem_badAuxiliaryColumnCycles {W : Type u} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : BlockedAuxiliaryColumnCycle W) :
    P ∈ badAuxiliaryColumnCycles A R ↔
      IsHomBlockedAuxiliaryColumnCycle A P ∧
      HasBlockedAuxiliaryColumnConflict R P := by
  classical
  simp [badAuxiliaryColumnCycles]

/-- The specialized clean-cycle selector distilled from Janzer's Lemmas
2.3--2.5.  It is kept as a proposition so the analytic counting proof can be
developed independently of the explicit witness and interleaving. -/
def CleanCycleSelector1568 : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (α : ℝ),
    (∀ x y, R x y → R y x) →
    (∃ x y, A.Adj x y) →
    (∀ x y, ((relationNeighbors A R x y).card : ℝ) ≤ α * A.degree y) →
    α < cleanSelectorThreshold (Fintype.card W) →
    ∃ X : Column → W,
      (∀ c, A.Adj (X c) (X (nextColumn c))) ∧
      ∀ c d, c ≠ d → ¬ R (X c) (X d)

open Erdos113Regular Erdos113BipartiteGraph Erdos113CellPruning

theorem cleanCycleSelector1568_proof : CleanCycleSelector1568 := by
  intro W instFintype instDecEq A instDecAdj R instDecR α hR hedge hlocal hsmall
  letI : Fintype W := instFintype
  letI : DecidableEq W := instDecEq
  letI : DecidableRel A.Adj := instDecAdj
  letI : DecidableRel R := instDecR
  classical
  have hα : 0 ≤ α := by
    obtain ⟨x, y, hxy⟩ := hedge
    have hypos : 0 < A.degree y := by
      apply Finset.card_pos.mpr
      exact ⟨x, (A.mem_neighborFinset y x).mpr hxy.symm⟩
    have hloc := hlocal x y
    have hleft : (0 : ℝ) ≤ ((relationNeighbors A R x y).card : ℝ) := by positivity
    have hprod : 0 ≤ α * (A.degree y : ℝ) := hleft.trans hloc
    exact nonneg_of_mul_nonneg_left hprod (by exact_mod_cast hypos)
  obtain ⟨i, j, E, hEsub, hEne, _hEdense, hleftMin, hrightMin⟩ :=
    exists_pruned_cell A hedge
  let B := retainedGraph E
  let side : LiveLeft E ⊕ LiveRight E → Bool :=
    Sum.elim (fun _ ↦ false) (fun _ ↦ true)
  let proj : LiveLeft E ⊕ LiveRight E → W :=
    Sum.elim (fun x ↦ x.1.1) (fun y ↦ y.1.1)
  let R' : (LiveLeft E ⊕ LiveRight E) →
      (LiveLeft E ⊕ LiveRight E) → Prop := fun x y ↦ R (proj x) (proj y)
  letI : DecidableRel B.Adj := inferInstance
  letI : DecidableRel R' := fun x y ↦ instDecR (proj x) (proj y)
  let L : ℝ := degreeBinCount (W := W)
  let cap : Bool → ℝ := fun b ↦ if b then 2 ^ (j.val + 1) else 2 ^ (i.val + 1)
  let d : Bool → ℝ := fun b ↦ cap b / (16 * L)
  have hLpos : 0 < L := by
    dsimp [L, degreeBinCount]
    positivity
  have hcap : ∀ b, 0 < cap b := by
    intro b
    cases b <;> simp [cap] <;> positivity
  have hprojAdj {x y : LiveLeft E ⊕ LiveRight E} (hxy : B.Adj x y) :
      A.Adj (proj x) (proj y) := by
    rcases x with x | x <;> rcases y with y | y
    · exact False.elim hxy
    · have he : (x.1, y.1) ∈ E := hxy
      exact (mem_cellEdges A i j _).mp (hEsub he)
    · have he : (y.1, x.1) ∈ E := hxy
      exact ((mem_cellEdges A i j _).mp (hEsub he)).symm
    · exact False.elim hxy
  have hprojInjOnNeighbor (y : LiveLeft E ⊕ LiveRight E) :
      Set.InjOn proj (B.neighborSet y) := by
    intro x hx z hz hxz
    rcases y with y | y
    · rcases x with x | x
      · exact False.elim hx
      · rcases z with z | z
        · exact False.elim hz
        · congr 1
          apply Subtype.ext
          apply Subtype.ext
          exact hxz
    · rcases x with x | x
      · rcases z with z | z
        · congr 1
          apply Subtype.ext
          apply Subtype.ext
          exact hxz
        · exact False.elim hz
      · exact False.elim hx
  have hprojDegreeCap (x : LiveLeft E ⊕ LiveRight E) :
      (A.degree (proj x) : ℝ) ≤ cap (side x) := by
    rcases x with x | x
    · have hb := (degree_bounds_of_mem_bin A i x.1.2).2
      dsimp [proj, side, cap]
      exact_mod_cast hb.le
    · have hb := (degree_bounds_of_mem_bin A j x.1.2).2
      dsimp [proj, side, cap]
      exact_mod_cast hb.le
  have hdegreeCap (x : LiveLeft E ⊕ LiveRight E) :
      (B.degree x : ℝ) ≤ cap (side x) := by
    rcases x with x | x
    · rw [Erdos113BipartiteGraph.degree_inl]
      have hf := card_leftFiber_le_degree A i j E hEsub x.1
      have hb := (degree_bounds_of_mem_bin A i x.1.2).2
      dsimp [side, cap]
      exact_mod_cast hf.trans hb.le
    · rw [Erdos113BipartiteGraph.degree_inr]
      have hf := card_rightFiber_le_degree A i j E hEsub x.1
      have hb := (degree_bounds_of_mem_bin A j x.1.2).2
      dsimp [side, cap]
      exact_mod_cast hf.trans hb.le
  have hdegreeMin (x : LiveLeft E ⊕ LiveRight E) :
      d (side x) ≤ (B.degree x : ℝ) := by
    rcases x with x | x
    · obtain ⟨y, hy⟩ := x.2
      have hinc : (E ∩ leftFiber (cellEdges A i j) x.1).Nonempty := by
        refine ⟨(x.1, y), Finset.mem_inter.mpr ⟨hy, ?_⟩⟩
        exact (mem_leftFiber _ _ _).mpr ⟨hEsub hy, rfl⟩
      have hm := hleftMin x.1 hinc
      rw [Erdos113BipartiteGraph.degree_inl]
      dsimp [d, cap, side, L]
      have hmR : ((cellThreshold (2 ^ (i.val + 1))
          (degreeBinCount (W := W)) : ℕ) : ℝ) ≤
          ((leftFiber E x.1).card : ℝ) := by exact_mod_cast hm
      have hbase := (cap_div_le_cast_cellThreshold (cap := 2 ^ (i.val + 1))
        (L := degreeBinCount (W := W))).trans hmR
      norm_num [Nat.cast_pow, Nat.cast_mul] at hbase
      simpa using hbase
    · obtain ⟨y, hy⟩ := x.2
      have hinc : (E ∩ rightFiber (cellEdges A i j) x.1).Nonempty := by
        refine ⟨(y, x.1), Finset.mem_inter.mpr ⟨hy, ?_⟩⟩
        exact (mem_rightFiber _ _ _).mpr ⟨hEsub hy, rfl⟩
      have hm := hrightMin x.1 hinc
      rw [Erdos113BipartiteGraph.degree_inr]
      dsimp [d, cap, side, L]
      have hmR : ((cellThreshold (2 ^ (j.val + 1))
          (degreeBinCount (W := W)) : ℕ) : ℝ) ≤
          ((rightFiber E x.1).card : ℝ) := by exact_mod_cast hm
      have hbase := (cap_div_le_cast_cellThreshold (cap := 2 ^ (j.val + 1))
        (L := degreeBinCount (W := W))).trans hmR
      norm_num [Nat.cast_pow, Nat.cast_mul] at hbase
      simpa using hbase
  have hlocal' (x y : LiveLeft E ⊕ LiveRight E) :
      ((((B.neighborFinset y).filter (R' x)).card : ℕ) : ℝ) ≤
        α * cap (side y) := by
    let S := (B.neighborFinset y).filter (R' x)
    let T := (A.neighborFinset (proj y)).filter (R (proj x))
    have hinj : Set.InjOn proj S := by
      intro z hz w hw hzw
      apply hprojInjOnNeighbor y
      · exact (B.mem_neighborFinset y z).mp (Finset.mem_filter.mp hz).1
      · exact (B.mem_neighborFinset y w).mp (Finset.mem_filter.mp hw).1
      · exact hzw
    have himage : S.image proj ⊆ T := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      have hw' := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr
        ⟨(A.mem_neighborFinset (proj y) (proj w)).mpr
          (hprojAdj ((B.mem_neighborFinset y w).mp hw'.1)), hw'.2⟩
    calc
      (S.card : ℝ) = ((S.image proj).card : ℝ) := by
        congr 1
        exact (Finset.card_image_iff.mpr hinj).symm
      _ ≤ (T.card : ℝ) := by exact_mod_cast Finset.card_le_card himage
      _ ≤ α * A.degree (proj y) := by
        simpa [T, relationNeighbors] using hlocal (proj x) (proj y)
      _ ≤ α * cap (side y) := by
        exact mul_le_mul_of_nonneg_left (hprojDegreeCap y) hα
  have hlocalR : ∀ x y,
      ((((B.neighborFinset y).filter (R' x)).card : ℕ) : ℝ) ≤
        α * cap (side y) := hlocal'
  have hcross : ∀ {x y}, B.Adj x y → side y = !side x := by
    intro x y hxy
    exact Erdos113BipartiteGraph.cross E hxy
  letI : Nonempty (LiveLeft E ⊕ LiveRight E) :=
    Erdos113BipartiteGraph.nonempty_of_nonempty E hEne
  let N' : ℝ := Fintype.card (LiveLeft E ⊕ LiveRight E)
  have hcardN : Fintype.card (LiveLeft E ⊕ LiveRight E) ≤ 2 * Fintype.card W := by
    rw [Fintype.card_sum]
    have hleftCard : Fintype.card (LiveLeft E) ≤ Fintype.card W := by
      calc
        Fintype.card (LiveLeft E) ≤ Fintype.card (BinVertex A i) :=
          Fintype.card_subtype_le _
        _ ≤ Fintype.card W := Fintype.card_subtype_le _
    have hrightCard : Fintype.card (LiveRight E) ≤ Fintype.card W := by
      calc
        Fintype.card (LiveRight E) ≤ Fintype.card (BinVertex A j) :=
          Fintype.card_subtype_le _
        _ ≤ Fintype.card W := Fintype.card_subtype_le _
    omega
  have hNtwo : 2 ≤ Fintype.card W := by
    obtain ⟨x, y, hxy⟩ := hedge
    have hone : 1 < Fintype.card W :=
      Fintype.one_lt_card_iff.mpr ⟨x, y, hxy.ne⟩
    omega
  have hlogpos : 0 < Real.log (Fintype.card W : ℝ) :=
    Real.log_pos (by exact_mod_cast hNtwo)
  have hLlog : L ≤ 4 * Real.log (Fintype.card W : ℝ) := by
    let k := Nat.log 2 (Fintype.card W)
    have hpow := Nat.pow_log_le_self 2 (show Fintype.card W ≠ 0 by omega)
    have hpowpos : (0 : ℝ) < (2 : ℕ) ^ k := by positivity
    have hnpos : (0 : ℝ) < Fintype.card W := by positivity
    have hlogle := Real.strictMonoOn_log.monotoneOn
      (by exact hpowpos) (by exact hnpos) (by exact_mod_cast hpow)
    rw [Real.log_pow] at hlogle
    have hlogtwo : (1 / 2 : ℝ) < Real.log 2 :=
      (by nlinarith [Real.log_two_gt_d9])
    have hk : (0 : ℝ) ≤ k := by positivity
    have hkmul : (k : ℝ) * (1 / 2 : ℝ) ≤ (k : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlogtwo.le hk
    have hlogmono := Real.strictMonoOn_log.monotoneOn
      (by norm_num : (2 : ℝ) ∈ Set.Ioi 0)
      (by
        change (0 : ℝ) < (Fintype.card W : ℝ)
        exact_mod_cast (show 0 < Fintype.card W by omega))
      (by exact_mod_cast hNtwo)
    have hkbound : (k : ℝ) / 2 ≤ Real.log (Fintype.card W : ℝ) := by
      calc
        (k : ℝ) / 2 = (k : ℝ) * (1 / 2) := by ring
        _ ≤ (k : ℝ) * Real.log 2 := hkmul
        _ ≤ Real.log (Fintype.card W : ℝ) := by simpa using hlogle
    have hone : (1 : ℝ) ≤ 2 * Real.log (Fintype.card W : ℝ) := by
      nlinarith
    change ((Nat.log 2 (Fintype.card W) + 1 : ℕ) : ℝ) ≤
      4 * Real.log (Fintype.card W : ℝ)
    rw [Nat.cast_add, Nat.cast_one]
    change (k : ℝ) + 1 ≤ 4 * Real.log (Fintype.card W : ℝ)
    nlinarith
  have hNroot : N' ^ ((1 : ℝ) / 784) ≤
      2 * (Fintype.card W : ℝ) ^ ((1 : ℝ) / 784) := by
    have hN'nonneg : 0 ≤ N' := by dsimp [N']; positivity
    have hcast : N' ≤ 2 * (Fintype.card W : ℝ) := by
      dsimp [N']
      exact_mod_cast hcardN
    calc
      N' ^ ((1 : ℝ) / 784) ≤
          (2 * (Fintype.card W : ℝ)) ^ ((1 : ℝ) / 784) :=
        Real.rpow_le_rpow hN'nonneg hcast (by norm_num)
      _ = (2 : ℝ) ^ ((1 : ℝ) / 784) *
          (Fintype.card W : ℝ) ^ ((1 : ℝ) / 784) := by
        rw [Real.mul_rpow] <;> positivity
      _ ≤ 2 * (Fintype.card W : ℝ) ^ ((1 : ℝ) / 784) := by
        gcongr
        exact Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hdenom :
      4 * 1568 * 784 * 6272 * (16 * L) ^ 2 *
          N' ^ ((1 : ℝ) / 784) ≤
        2 ^ (28 : ℕ) * 784 ^ (3 : ℕ) *
          Real.log (Fintype.card W : ℝ) ^ (4 : ℕ) *
          (Fintype.card W : ℝ) ^ ((1 : ℝ) / 784) := by
    let l := Real.log (Fintype.card W : ℝ)
    let q := (Fintype.card W : ℝ) ^ ((1 : ℝ) / 784)
    have hl : 0 < l := hlogpos
    have hq : 0 < q := Real.rpow_pos_of_pos (by positivity) _
    have hLsq : L ^ 2 ≤ 16 * l ^ 2 := by
      dsimp [l]
      nlinarith [sq_nonneg (4 * Real.log (Fintype.card W : ℝ) - L)]
    have hlogsq : (1 : ℝ) ≤ 512 * l ^ 2 := by
      have hlogtwo : (1 / 2 : ℝ) < Real.log 2 := by
        nlinarith [Real.log_two_gt_d9]
      have hlogmono := Real.strictMonoOn_log.monotoneOn
        (by norm_num : (2 : ℝ) ∈ Set.Ioi 0)
        (by
          change (0 : ℝ) < (Fintype.card W : ℝ)
          exact_mod_cast (show 0 < Fintype.card W by omega))
        (by exact_mod_cast hNtwo)
      dsimp [l]
      nlinarith
    calc
      4 * 1568 * 784 * 6272 * (16 * L) ^ 2 *
          N' ^ ((1 : ℝ) / 784) =
          2 ^ (14 : ℕ) * 784 ^ (3 : ℕ) * L ^ 2 *
            N' ^ ((1 : ℝ) / 784) := by
        norm_num
        left
        ring
      _ ≤ 2 ^ (14 : ℕ) * 784 ^ (3 : ℕ) * (16 * l ^ 2) *
          N' ^ ((1 : ℝ) / 784) := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left hLsq
          positivity
        · exact Real.rpow_nonneg (by dsimp [N']; positivity) _
      _ ≤ 2 ^ (14 : ℕ) * 784 ^ (3 : ℕ) * (16 * l ^ 2) * (2 * q) := by
        apply mul_le_mul_of_nonneg_left hNroot
        positivity
      _ = 2 ^ (19 : ℕ) * 784 ^ (3 : ℕ) * l ^ 2 * q := by
        norm_num
        ring
      _ ≤ (512 * l ^ 2) *
          (2 ^ (19 : ℕ) * 784 ^ (3 : ℕ) * l ^ 2 * q) := by
        have hc : 0 ≤ (2 ^ (19 : ℕ) : ℝ) * 784 ^ (3 : ℕ) * l ^ 2 * q := by
          positivity
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hlogsq hc
      _ = 2 ^ (28 : ℕ) * 784 ^ (3 : ℕ) * l ^ (4 : ℕ) * q := by
        norm_num
        ring
      _ = 2 ^ (28 : ℕ) * 784 ^ (3 : ℕ) *
          Real.log (Fintype.card W : ℝ) ^ (4 : ℕ) *
          (Fintype.card W : ℝ) ^ ((1 : ℝ) / 784) := rfl
  have hsmall' : α <
      (4 * 1568 * 784 * 6272 * (16 * L) ^ 2 *
        N' ^ ((1 : ℝ) / 784))⁻¹ := by
    have hbigpos : 0 < 2 ^ (28 : ℕ) * 784 ^ (3 : ℕ) *
        Real.log (Fintype.card W : ℝ) ^ (4 : ℕ) *
        (Fintype.card W : ℝ) ^ ((1 : ℝ) / 784) := by positivity
    have hsmallpos : 0 < 4 * 1568 * 784 * 6272 * (16 * L) ^ 2 *
        N' ^ ((1 : ℝ) / 784) := by
      have hN'pos : 0 < N' := by dsimp [N']; positivity
      positivity
    apply hsmall.trans_le
    apply (inv_le_inv₀ hbigpos hsmallpos).2
    simpa [cleanSelectorThreshold] using hdenom
  obtain ⟨X, hXadj, hXfree⟩ := exists_cleanCycle_of_bipartiteAlmostRegular
    B R' (fun x y h ↦ hR _ _ h) side d cap N' (16 * L) α rfl
    (fun b ↦ by dsimp [d]; positivity) hcap (by positivity) hα hcross
    hdegreeMin hdegreeCap (fun b ↦ by
      dsimp [d]
      field_simp
      exact le_rfl) hlocalR hsmall'
  refine ⟨fun c ↦ proj (X c), ?_, ?_⟩
  · intro c
    exact hprojAdj (hXadj c)
  · intro c e hce hconf
    exact hXfree c e hce hconf

lemma auxiliaryGraph_adj_compatible {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : Finset (CycleTuple V)}
    (hfamily : ∀ x ∈ C, IsGenuineCycleTuple G x) {y z : SliceTuple V}
    (h : (auxiliaryGraph G C hfamily).Adj y z) : CompatibleSlices G y z := by
  rcases h with h | h
  · exact compatibleSlices_of_interleavedCycle G y z (hfamily _ h)
  · exact (compatibleSlices_of_interleavedCycle G z y (hfamily _ h)).symm

lemma auxiliaryGraph_adj_left_injective {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : Finset (CycleTuple V)}
    (hfamily : ∀ x ∈ C, IsGenuineCycleTuple G x) {y z : SliceTuple V}
    (h : (auxiliaryGraph G C hfamily).Adj y z) : Function.Injective y := by
  rcases h with h | h
  · have hinj := evalSliceCoordinate_injective_of_interleavedCycle (hfamily _ h)
    intro r s hrs
    have hp : (true, r) = (true, s) := hinj (by
      simpa [evalSliceCoordinate] using hrs)
    exact congrArg Prod.snd hp
  · have hinj := evalSliceCoordinate_injective_of_interleavedCycle (hfamily _ h)
    intro r s hrs
    have hp : (false, r) = (false, s) := hinj (by
      simpa [evalSliceCoordinate] using hrs)
    exact congrArg Prod.snd hp

/-- The Erdős--Simonovits assertion from Problem 113. -/
def ErdosSimonovitsConjecture : Prop :=
  ∀ (V : Type) [Fintype V], ∀ H : SimpleGraph V,
    H.IsBipartite → (HasThreeHalvesExtremalBound H ↔ IsTwoDegenerate H)

/-- Vertex type of Janzer's graph `H_{7,784}`. -/
abbrev Vertex := Row × Column

def matchingVertex (v : Vertex) : Vertex := (matchingRow v.1, v.2)

def nextVertex (v : Vertex) : Vertex := (turnRow v.1, nextColumn v.2)

def prevVertex (v : Vertex) : Vertex := (turnRow v.1, prevColumn v.2)

lemma matchingRow_involutive : Function.Involutive matchingRow := by
  intro r
  cases r with
  | mk i b => cases b <;> rfl

lemma nextColumn_prevColumn (c : Column) : nextColumn (prevColumn c) = c := by
  rcases c with ⟨j, b⟩
  cases b <;> simp [nextColumn, prevColumn]

lemma prevColumn_nextColumn (c : Column) : prevColumn (nextColumn c) = c := by
  rcases c with ⟨j, b⟩
  cases b <;> simp [nextColumn, prevColumn]

lemma matchingVertex_involutive : Function.Involutive matchingVertex := by
  intro v
  simp [matchingVertex, matchingRow_involutive v.1]

lemma nextVertex_prevVertex (v : Vertex) : nextVertex (prevVertex v) = v := by
  change (turnRow (turnRow v.1), nextColumn (prevColumn v.2)) = v
  rw [turnRow_involutive, nextColumn_prevColumn]

lemma prevVertex_nextVertex (v : Vertex) : prevVertex (nextVertex v) = v := by
  change (turnRow (turnRow v.1), prevColumn (nextColumn v.2)) = v
  rw [turnRow_involutive, prevColumn_nextColumn]

lemma matchingVertex_ne (v : Vertex) : matchingVertex v ≠ v := by
  intro h
  have hb := congrArg (fun w : Vertex ↦ w.1.2) h
  cases v.1.2 <;> simp [matchingVertex, matchingRow] at hb

lemma nextColumn_ne (c : Column) : nextColumn c ≠ c := by
  rcases c with ⟨j, b⟩
  cases b <;> simp [nextColumn]

lemma prevColumn_ne (c : Column) : prevColumn c ≠ c := by
  rcases c with ⟨j, b⟩
  cases b <;> simp [prevColumn]

lemma nextColumn_ne_prevColumn (c : Column) : nextColumn c ≠ prevColumn c := by
  have hone : (1 : ZMod 784) ≠ 0 := by decide
  rcases c with ⟨j, b⟩
  cases b
  · intro h
    have hj := congrArg Prod.fst h
    simp [nextColumn, prevColumn] at hj
    have hzero : (1 : ZMod 784) = 0 := by
      linear_combination hj
    exact hone hzero
  · intro h
    have hj := congrArg Prod.fst h
    simp [nextColumn, prevColumn] at hj
    exact hone hj

/-
The following three vertex-level nonfixed-point statements are kept separate
because they are also used to compute the degree exactly.
-/
lemma nextVertex_ne (v : Vertex) : nextVertex v ≠ v := by
  exact fun h ↦ nextColumn_ne v.2 (congrArg Prod.snd h)

lemma prevVertex_ne (v : Vertex) : prevVertex v ≠ v := by
  exact fun h ↦ prevColumn_ne v.2 (congrArg Prod.snd h)

/-- Janzer's graph `H_{7,784}`.  Its three neighbors at `v` are the matching
neighbor and the successor and predecessor in the nonmatching two-factor. -/
def janzerGraph : SimpleGraph Vertex where
  Adj v w := w = matchingVertex v ∨ w = nextVertex v ∨ w = prevVertex v
  symm := ⟨by
    intro v w h
    rcases h with h | h | h
    · left
      rw [h, matchingVertex_involutive]
    · right; right
      rw [h, prevVertex_nextVertex]
    · right; left
      rw [h, nextVertex_prevVertex]
    ⟩
  loopless := ⟨by
    intro v h
    rcases h with h | h | h
    · exact matchingVertex_ne v h.symm
    · exact nextVertex_ne v h.symm
    · exact prevVertex_ne v h.symm
    ⟩

instance : DecidableRel janzerGraph.Adj := fun v w ↦ by
  change Decidable (w = matchingVertex v ∨ w = nextVertex v ∨ w = prevVertex v)
  infer_instance

lemma janzerGraph_neighborFinset (v : Vertex) :
    janzerGraph.neighborFinset v = {matchingVertex v, nextVertex v, prevVertex v} := by
  ext w
  rw [SimpleGraph.mem_neighborFinset]
  change (w = matchingVertex v ∨ w = nextVertex v ∨ w = prevVertex v) ↔ _
  simp only [Finset.mem_insert, Finset.mem_singleton]

lemma matchingVertex_ne_nextVertex (v : Vertex) : matchingVertex v ≠ nextVertex v := by
  intro h
  exact nextColumn_ne v.2 (congrArg Prod.snd h).symm

lemma matchingVertex_ne_prevVertex (v : Vertex) : matchingVertex v ≠ prevVertex v := by
  intro h
  exact prevColumn_ne v.2 (congrArg Prod.snd h).symm

lemma nextVertex_ne_prevVertex (v : Vertex) : nextVertex v ≠ prevVertex v := by
  exact fun h ↦ nextColumn_ne_prevColumn v.2 (congrArg Prod.snd h)

theorem janzerGraph_regular : janzerGraph.IsRegularOfDegree 3 := by
  intro v
  rw [← janzerGraph.card_neighborFinset_eq_degree, janzerGraph_neighborFinset]
  simp [matchingVertex_ne_nextVertex v, matchingVertex_ne_prevVertex v,
    nextVertex_ne_prevVertex v]

/-- The row contribution to the bipartite coloring. -/
def rowColor (r : Row) : Bool := decide (r.1.val % 2 = 1) != r.2

/-- The explicit two-coloring of `H_{7,784}`. -/
def vertexColorBool (v : Vertex) : Bool := rowColor v.1 != v.2.2

lemma rowColor_matchingRow (r : Row) : rowColor (matchingRow r) = !rowColor r := by
  decide +revert

lemma rowColor_turnRow (r : Row) : rowColor (turnRow r) = rowColor r := by
  decide +revert

lemma vertexColorBool_matchingVertex (v : Vertex) :
    vertexColorBool (matchingVertex v) = !vertexColorBool v := by
  rcases v with ⟨r, c⟩
  simp only [vertexColorBool, matchingVertex, rowColor_matchingRow]
  cases rowColor r <;> cases c.2 <;> decide

lemma vertexColorBool_nextVertex (v : Vertex) :
    vertexColorBool (nextVertex v) = !vertexColorBool v := by
  rcases v with ⟨r, j, b⟩
  simp only [vertexColorBool, nextVertex, rowColor_turnRow]
  cases rowColor r <;> cases b <;> simp [nextColumn]

lemma vertexColorBool_prevVertex (v : Vertex) :
    vertexColorBool (prevVertex v) = !vertexColorBool v := by
  rcases v with ⟨r, j, b⟩
  simp only [vertexColorBool, prevVertex, rowColor_turnRow]
  cases rowColor r <;> cases b <;> simp [prevColumn]

def vertexColor (v : Vertex) : Fin 2 := if vertexColorBool v then 1 else 0

theorem janzerGraph_bipartite : janzerGraph.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk vertexColor ?_⟩
  intro v w h
  rcases h with rfl | rfl | rfl
  · simp only [vertexColor]
    rw [vertexColorBool_matchingVertex]
    cases vertexColorBool v <;> decide
  · simp only [vertexColor]
    rw [vertexColorBool_nextVertex]
    cases vertexColorBool v <;> decide
  · simp only [vertexColor]
    rw [vertexColorBool_prevVertex]
    cases vertexColorBool v <;> decide

theorem janzerGraph_not_twoDegenerate : ¬ IsTwoDegenerate janzerGraph := by
  classical
  intro h
  obtain ⟨v, hv⟩ := h Set.univ Set.univ_nonempty
  have hncard : (janzerGraph.neighborSet (v : Vertex)).ncard = 3 := by
    rw [Set.ncard_eq_toFinset_card']
    change janzerGraph.degree (v : Vertex) = 3
    exact janzerGraph_regular v
  simp only [Set.inter_univ] at hv
  omega

/-! ### From a clean auxiliary cycle to a copy of `H_{7,784}` -/

/-- A conflict-free cyclic traversal of the auxiliary graph.  Conflict-free
means that no two row coordinates selected anywhere on the cycle coincide. -/
structure IsCleanAuxiliaryColumnCycle {V : Type*}
    (A : SimpleGraph (SliceTuple V)) (X : Column → SliceTuple V) : Prop where
  injective : Function.Injective (fun v : Vertex ↦ X v.2 v.1)
  adjacent : ∀ c, A.Adj (X c) (X (nextColumn c))

/-- This is the output format of the clean-cycle selector: consecutive
auxiliary vertices are adjacent and distinct positions share no coordinate. -/
structure IsPairwiseNonconflictingAuxiliaryColumnCycle {V : Type*}
    (A : SimpleGraph (SliceTuple V)) (X : Column → SliceTuple V) : Prop where
  adjacent : ∀ c, A.Adj (X c) (X (nextColumn c))
  nonconflicting : ∀ c d, c ≠ d → ¬ SlicesConflict (X c) (X d)

lemma IsPairwiseNonconflictingAuxiliaryColumnCycle.toClean
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : Finset (CycleTuple V)}
    (hfamily : ∀ x ∈ C, IsGenuineCycleTuple G x)
    {X : Column → SliceTuple V}
    (h : IsPairwiseNonconflictingAuxiliaryColumnCycle
      (auxiliaryGraph G C hfamily) X) :
    IsCleanAuxiliaryColumnCycle (auxiliaryGraph G C hfamily) X := by
  refine ⟨?_, h.adjacent⟩
  rintro ⟨r, c⟩ ⟨s, d⟩ hrs
  by_cases hcd : c = d
  · subst d
    have hinj := auxiliaryGraph_adj_left_injective hfamily (h.adjacent c)
    have hrs' : r = s := hinj hrs
    simp [hrs']
  · exact (h.nonconflicting c d hcd ⟨r, s, hrs⟩).elim

/-- A cyclic list of row-slices is clean if consecutive slices generate
members of `C` and all `14 · 2 · 1568` selected host vertices are distinct. -/
structure IsCleanSliceCycle {V : Type*} (G : SimpleGraph V)
    (X : Column → SliceTuple V) : Prop where
  injective : Function.Injective (fun v : Vertex ↦ X v.2 v.1)
  compatible : ∀ c, CompatibleSlices G (X c) (X (nextColumn c))

/-- Janzer's interleaving has exactly the adjacency pattern needed to embed
the explicit graph once a clean auxiliary `1568`-cycle has been selected. -/
theorem copy_of_cleanSliceCycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X : Column → SliceTuple V)
    (hclean : IsCleanSliceCycle G X) :
    janzerGraph ⊑ G := by
  refine ⟨⟨⟨fun v ↦ X v.2 v.1, ?_⟩, hclean.injective⟩⟩
  intro v w hvw
  change w = matchingVertex v ∨ w = nextVertex v ∨ w = prevVertex v at hvw
  rcases hvw with rfl | rfl | rfl
  · exact (hclean.compatible v.2).1 v.1
  · exact (hclean.compatible v.2).2.2 v.1
  · have hp := (hclean.compatible (prevColumn v.2)).2.2 (turnRow v.1)
    rw [nextColumn_prevColumn, turnRow_involutive] at hp
    exact hp.symm

theorem copy_of_cleanAuxiliaryColumnCycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Finset (CycleTuple V))
    (hfamily : ∀ x ∈ C, IsGenuineCycleTuple G x)
    (X : Column → SliceTuple V)
    (hclean : IsCleanAuxiliaryColumnCycle (auxiliaryGraph G C hfamily) X) :
    janzerGraph ⊑ G := by
  apply copy_of_cleanSliceCycle G X
  refine ⟨hclean.injective, ?_⟩
  intro c
  exact auxiliaryGraph_adj_compatible hfamily (hclean.adjacent c)

theorem IsNiceCycleFamily.janzerGraph_isContained_of_cleanCycleSelector
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {β : ℝ} {C : Finset (CycleTuple V)}
    (hnice : IsNiceCycleFamily G β C) (hβ : 0 ≤ β) (hC : C.Nonempty)
    (hselector : CleanCycleSelector1568.{u})
    (hsmall : 1568 * β < cleanSelectorThreshold (Fintype.card (SliceTuple V))) :
    janzerGraph ⊑ G := by
  let A := auxiliaryGraph G C hnice.genuine
  have hedge : ∃ y z, A.Adj y z := by
    obtain ⟨x, hx⟩ := hC
    refine ⟨sliceOfCycle true x, sliceOfCycle false x, ?_⟩
    left
    simpa [A, interleavedCycle_sliceOfCycle] using hx
  have hlocal : ∀ x y,
      ((relationNeighbors A SlicesConflict x y).card : ℝ) ≤
        (1568 * β) * A.degree y := by
    intro x y
    simpa only [A, relationNeighbors, conflictingNeighbors] using
      hnice.auxiliary_conflicting_neighbors_bound hβ x y
  obtain ⟨X, hXadj, hXconflict⟩ :=
    hselector (SliceTuple V) A SlicesConflict (1568 * β)
      (fun _ _ h ↦ h.symm) hedge hlocal hsmall
  apply copy_of_cleanAuxiliaryColumnCycle G C hnice.genuine X
  apply IsPairwiseNonconflictingAuxiliaryColumnCycle.toClean hnice.genuine
  exact ⟨hXadj, hXconflict⟩

theorem IsGoodCycleFamily.janzerGraph_isContained
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {β : ℝ} {C : Finset (CycleTuple V)}
    (hgood : IsGoodCycleFamily G β C) (hβ : 0 < β) (hC : C.Nonempty)
    (hsmall : 1568 * β < cleanSelectorThreshold (Fintype.card (SliceTuple V))) :
    janzerGraph ⊑ G := by
  obtain ⟨C', hC'sub, hC'nonempty, hnice⟩ :=
    hgood.exists_nice_subfamily hβ hC
  exact hnice.janzerGraph_isContained_of_cleanCycleSelector
    hβ.le hC'nonempty cleanCycleSelector1568_proof hsmall

theorem janzerGraph_isContained_of_fewFourCycle_bipartite_numerics
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (s : ℕ) (β : ℝ)
    (Q D t₀ t₂ : Bool → ℝ)
    (hs : 0 < s) (hβ : 0 < β)
    (hQ : ∀ b, 0 ≤ Q b) (hD : ∀ b, 0 ≤ D b)
    (ht₀ : ∀ b, 0 < t₀ b) (ht₂ : ∀ b, 0 < t₂ b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x))
    (hcap : ∀ u y, G.Adj y u →
      ((Erdos113FourCycles.extensionsThroughEdge G u y).card : ℝ) ≤
        Q (side y))
    (hclosed : 0 < (Conflict.closedWalkCount G 56 : ℝ))
    (hbad :
      56 * ∑ b : Bool,
          (D b * t₀ b *
              ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
                (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
            28 * (t₀ b)⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) +
        56 * ∑ b : Bool,
          (D b * t₂ b *
              ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
                (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
            (Q (!b) / s) * (t₂ b)⁻¹ *
              (Conflict.closedWalkCount G 56 : ℝ)) ≤
        (Conflict.closedWalkCount G 56 : ℝ) / 2)
    (hpattern : (16 * 7 * s : ℝ) *
        (2 * G.edgeFinset.card * (D false * D true) ^ 26) ≤
      β * ((Conflict.closedWalkCount G 56 : ℝ) / 2))
    (hsmall : 1568 * β < cleanSelectorThreshold
      (Fintype.card (SliceTuple V))) :
    janzerGraph ⊑ G := by
  let C := controlledGenuineCycles G s
  have hhalf := controlledGenuineCycles_half_closedWalkCount_bipartite_of_numerics
    G side s hs Q D t₀ t₂ hQ hD ht₀ ht₂ hcross hdeg hcap hclosed hbad
  have hgood : IsGoodCycleFamily G β C :=
    controlledGenuineCycles_isGood_bipartite_edges
      G side D hD hcross hdeg s hs β
        ((Conflict.closedWalkCount G 56 : ℝ) / 2) hβ.le hhalf hpattern
  have hC : C.Nonempty := by
    have hcardpos : 0 < (C.card : ℝ) := by linarith
    exact Finset.card_pos.mp (by exact_mod_cast hcardpos)
  exact hgood.janzerGraph_isContained hβ hC hsmall

/-! ## Quantitative data from the two dyadic selections -/

open Erdos113FourCycleSelection Erdos113AnchorConstruction

lemma codegree_le_degree_left
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    Erdos113FourCycles.codegree G u v ≤ G.degree u := by
  rw [Erdos113FourCycles.codegree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  exact Finset.card_le_card Finset.inter_subset_left

lemma FirstSelection.SecondSelection.secondScale_lt_twice_firstScale
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {side : V → Bool}
    (S : FirstSelection G side) (R : S.SecondSelection) :
    2 ^ R.index.val < 2 * 2 ^ S.scaleIndex.val := by
  obtain ⟨p, hp⟩ := R.bucket_nonempty
  have hb := S.secondDyadicTriples_count_bounds hp
  exact hb.1.trans_lt (by
    simpa [pow_succ, Nat.mul_comm] using
      S.middleCount_lt_scaleCap_at_triple p)

lemma FirstSelection.SecondSelection.auxiliary_edge_card_le_square
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {side : V → Bool}
    (S : FirstSelection G side) (R : S.SecondSelection) :
    (S.auxiliaryGraph R.index).edgeFinset.card ≤
      Fintype.card (NeighborVertex G S.anchor) ^ 2 := by
  calc
    (S.auxiliaryGraph R.index).edgeFinset.card ≤
        (Fintype.card (NeighborVertex G S.anchor)).choose 2 :=
      (S.auxiliaryGraph R.index).card_edgeFinset_le_card_choose_two
    _ ≤ Fintype.card (NeighborVertex G S.anchor) ^ 2 := by
      rw [Nat.choose_two_right]
      have hsub : Fintype.card (NeighborVertex G S.anchor) - 1 ≤
          Fintype.card (NeighborVertex G S.anchor) := by omega
      exact (Nat.div_le_self _ _).trans (by
        simpa [pow_two] using Nat.mul_le_mul_left
          (Fintype.card (NeighborVertex G S.anchor)) hsub)

lemma FirstSelection.SecondSelection.selection_count_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {side : V → Bool}
    (S : FirstSelection G side) (R : S.SecondSelection) :
    (Erdos113Cycles.genuineCycles G 4).card ≤
      32 * Fintype.card V *
        (Nat.log 2 (Fintype.card V) + 1) ^ 2 *
        2 ^ R.index.val *
        (S.auxiliaryGraph R.index).edgeFinset.card := by
  let m := Fintype.card V
  let L := Nat.log 2 m + 1
  let T := S.triples.card
  let f := (S.auxiliaryGraph R.index).edgeFinset.card
  let b := 2 ^ R.index.val
  have hactive :
      (Erdos113FourCycleSelection.activeSideVertices
        G side S.anchorSide).card ≤ m :=
    Finset.card_le_univ _
  have hfirst : (Erdos113Cycles.genuineCycles G 4).card ≤
      4 * m * L * T := by
    calc
      (Erdos113Cycles.genuineCycles G 4).card ≤
          4 * (Erdos113FourCycleSelection.activeSideVertices
            G side S.anchorSide).card * L * T := by
        simpa [m, L, T] using S.many
      _ ≤ 4 * m * L * T := by gcongr
  have hlog :
      Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1 ≤ 2 * L := by
    rw [Nat.log_pow (by omega : 1 < 2)]
    have hi : S.scaleIndex.val + 1 ≤ L := by
      simpa [L, m] using S.scaleIndex.isLt
    have hLpos : 0 < L := by dsimp [L]; omega
    omega
  have hsecond : T ≤ 8 * L * b * f := by
    have hpow : 2 ^ (R.index.val + 2) = 4 * b := by
      dsimp [b]
      ring
    calc
      T ≤ (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1) *
            2 ^ (R.index.val + 2) * f := by
        simpa [T, f] using R.many
      _ ≤ (2 * L) * 2 ^ (R.index.val + 2) * f := by
        gcongr
      _ = (2 * L) * (4 * b) * f := by rw [hpow]
      _ = 8 * L * b * f := by ring
  calc
    (Erdos113Cycles.genuineCycles G 4).card ≤ 4 * m * L * T := hfirst
    _ ≤ 4 * m * L * (8 * L * b * f) := by gcongr
    _ = 32 * m * L ^ 2 * b * f := by ring

lemma cleanSelectorThreshold_slice_mono {n m : ℕ}
    (hn : 2 ≤ n) (hnm : n ≤ m) :
    cleanSelectorThreshold (Fintype.card (SliceTuple (Fin m))) ≤
      cleanSelectorThreshold (Fintype.card (SliceTuple (Fin n))) := by
  rw [card_sliceTuple_fin, card_sliceTuple_fin, cleanSelectorThreshold,
    cleanSelectorThreshold]
  have hpowNat : n ^ 28 ≤ m ^ 28 := pow_le_pow_left' hnm 28
  have hpowReal : ((n ^ 28 : ℕ) : ℝ) ≤ (m ^ 28 : ℕ) := by
    exact_mod_cast hpowNat
  have hnPowPos : (0 : ℝ) < (n ^ 28 : ℕ) := by positivity
  have hlog : Real.log (n ^ 28 : ℕ) ≤ Real.log (m ^ 28 : ℕ) :=
    Real.log_le_log hnPowPos hpowReal
  have hlogn : 0 ≤ Real.log (n ^ 28 : ℕ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n ^ 28 by
      exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega)))
  have hlognpos : 0 < Real.log (n ^ 28 : ℕ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n ^ 28 by
      exact one_lt_pow₀ (by omega : 1 < n) (by norm_num : (28 : ℕ) ≠ 0))
  have hrpow : ((n ^ 28 : ℕ) : ℝ) ^ ((1 : ℝ) / 784) ≤
      ((m ^ 28 : ℕ) : ℝ) ^ ((1 : ℝ) / 784) :=
    Real.rpow_le_rpow (by positivity) hpowReal (by norm_num)
  apply inv_anti₀
  · positivity
  · gcongr

/-! ## The exact host-embedding boundary -/

/-- At order `n`, every host with more than `n^(31/21)` edges contains the
fixed Janzer graph.  Janzer's combinatorial argument proves this eventually. -/
def JanzerHostEmbeddingAt (n : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (n : ℝ) ^ ((31 : ℝ) / 21) < (G.edgeFinset.card : ℝ) →
      janzerGraph ⊑ G

/-- The host-embedding formulation is exactly strong enough to imply the
eventual extremal-number estimate; this is the formal version of the final
sentence in the proof of Janzer's Theorem 1.6. -/
lemma hasExtremalBound_of_eventually_janzerHostEmbedding
    (h : ∀ᶠ n : ℕ in atTop, JanzerHostEmbeddingAt n) :
    HasExtremalBound ((31 : ℝ) / 21) janzerGraph := by
  apply hasExtremalBound_of_eventually_le
  filter_upwards [h] with n hn
  by_contra! hex
  have hnonneg : 0 ≤ (n : ℝ) ^ ((31 : ℝ) / 21) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hex' : (n : ℝ) ^ ((31 : ℝ) / 21) <
      (SimpleGraph.extremalNumber (Fintype.card (Fin n)) janzerGraph : ℝ) := by
    simpa using hex
  have hlt :=
    (SimpleGraph.lt_extremalNumber_iff_of_nonneg
      (V := Fin n) janzerGraph hnonneg).mp hex'
  obtain ⟨G, _, hfree, hedge⟩ := hlt
  exact hfree (hn G hedge)

/-! ## Logical assembly

The sole remaining mathematical input after the explicit construction is
Janzer's extremal estimate.  This lemma records the exact reduction, without
adding the estimate as an assumption to the final theorem. -/

lemma not_erdosSimonovitsConjecture_of_janzer_bound
    (h : HasExtremalBound ((31 : ℝ) / 21) janzerGraph) :
    ¬ ErdosSimonovitsConjecture := by
  intro hconj
  have hiff := hconj Vertex janzerGraph janzerGraph_bipartite
  exact janzerGraph_not_twoDegenerate
    (hiff.mp (hasThreeHalvesExtremalBound_of_thirtyOne_div_twentyOne h))

open scoped BigOperators

open Erdos113AlmostRegular Erdos113HostCell Erdos113HostPruning
  Erdos113HostAsymptotics Erdos113CyclePruning Erdos113FourCycleSelection
  Erdos113Regular Erdos113AnchorConstruction Erdos113Cycles

lemma sparseCore_denseCell_common
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : SparseCore G) :
    letI : Fintype C.W := C.fintypeW
    letI : DecidableEq C.W := C.decEqW
    letI : DecidableRel C.graph.Adj := C.decAdj
    ∀ H : DenseHostCell C.graph,
    let m := C.order
    let L := degreeBinCount (W := C.W)
    let d : ℝ := H.edges.card
    let d₀ := d / (64 * m * L)
    (m : ℝ) ^ ((31 : ℝ) / 21) < 512 * L ^ (2 : ℕ) * d ∧
    (m : ℝ) ^ ((10 : ℝ) / 21) < 32768 * L ^ (3 : ℕ) * d₀ ∧
    (∀ b, (H.sideCap b : ℝ) ≤
      2 * (regularFactor + 1 : ℕ) * (m : ℝ) ^ ((10 : ℝ) / 21)) ∧
    (∀ b, d₀ ≤ sideMinimum H b) := by
  letI : Fintype C.W := C.fintypeW
  letI : DecidableEq C.W := C.decEqW
  letI : DecidableRel C.graph.Adj := C.decAdj
  intro H
  let m := C.order
  let L := degreeBinCount (W := C.W)
  let d : ℝ := H.edges.card
  let d₀ := d / (64 * m * L)
  have hm : 64 ≤ m := by simpa [m, SparseCore.order] using C.order_large
  have hmpos : (0 : ℝ) < m := by positivity
  have hLpos : (0 : ℝ) < L := by
    dsimp [L, degreeBinCount]
    positivity
  have hedgeCore : (m : ℝ) ^ ((31 : ℝ) / 21) <
      512 * (L : ℝ) ^ (2 : ℕ) * d := by
    have hlower := C.edge_lower
    have hdense : (C.graph.edgeFinset.card : ℝ) <
        8 * (L : ℝ) ^ (2 : ℕ) * d := by
      have hdense0 : (C.graph.edgeFinset.card : ℝ) <
          ((8 * L ^ 2 * H.edges.card : ℕ) : ℝ) := by
        exact_mod_cast H.dense
      norm_num [Nat.cast_mul, Nat.cast_pow, d] at hdense0 ⊢
      simpa using hdense0
    calc
      (m : ℝ) ^ ((31 : ℝ) / 21) =
          64 * ((m : ℝ) ^ ((31 : ℝ) / 21) / 64) := by ring
      _ ≤ 64 * C.graph.edgeFinset.card := by
        gcongr
        simpa [m, SparseCore.order] using hlower
      _ < 64 * (8 * (L : ℝ) ^ (2 : ℕ) * d) := by gcongr
      _ = 512 * (L : ℝ) ^ (2 : ℕ) * d := by ring
  have hd₀ : (m : ℝ) ^ ((10 : ℝ) / 21) <
      32768 * (L : ℝ) ^ (3 : ℕ) * d₀ := by
    have hid : (m : ℝ) ^ ((31 : ℝ) / 21) =
        (m : ℝ) ^ ((10 : ℝ) / 21) * m := by
      calc
        (m : ℝ) ^ ((31 : ℝ) / 21) =
            (m : ℝ) ^ ((10 : ℝ) / 21 + 1) := by norm_num
        _ = (m : ℝ) ^ ((10 : ℝ) / 21) * (m : ℝ) ^ (1 : ℝ) :=
          Real.rpow_add hmpos _ _
        _ = _ := by rw [Real.rpow_one]
    rw [hid] at hedgeCore
    dsimp [d₀]
    rw [show 32768 * (L : ℝ) ^ (3 : ℕ) *
        (d / (64 * m * L)) = 512 * (L : ℝ) ^ (2 : ℕ) * d / m by
      field_simp
      ring]
    exact (lt_div_iff₀ hmpos).2 (by simpa [mul_comm] using hedgeCore)
  have hcap (b : Bool) : (H.sideCap b : ℝ) ≤
      2 * (regularFactor + 1 : ℕ) * (m : ℝ) ^ ((10 : ℝ) / 21) := by
    have h₁ : H.sideCap b ≤ 2 * C.graph.maxDegree := H.sideCap_le_two_maxDegree b
    have h₂ := C.maxDegree_upper
    have h₁R : (H.sideCap b : ℝ) ≤ 2 * C.graph.maxDegree := by
      exact_mod_cast h₁
    exact h₁R.trans (by
      calc
        (2 : ℝ) * C.graph.maxDegree ≤
            2 * ((regularFactor + 1 : ℕ) *
              (m : ℝ) ^ ((10 : ℝ) / 21)) := by
          gcongr
          simpa [SparseCore.maximumDegree, m] using h₂
        _ = _ := by ring)
  have hd₀min (b : Bool) : d₀ ≤ sideMinimum H b := by
    have hedgeCap : H.edges.card ≤ m * H.sideCap b := by
      simpa [m, SparseCore.order] using H.edge_card_le_card_mul_sideCap b
    have hedgeCapR : d ≤ (m : ℝ) * H.sideCap b := by
      have hedgeCap0 : (H.edges.card : ℝ) ≤
          ((m * H.sideCap b : ℕ) : ℝ) := by exact_mod_cast hedgeCap
      norm_num [Nat.cast_mul, d] at hedgeCap0 ⊢
      simpa using hedgeCap0
    dsimp [d₀, sideMinimum]
    norm_num [Nat.cast_mul]
    change d / (64 * (m : ℝ) * L) ≤
      (H.sideCap b : ℝ) / (64 * (L : ℝ))
    rw [show d / ((64 : ℝ) * m * L) = (d / m) / (64 * L) by
      field_simp]
    apply (div_le_div_iff_of_pos_right (by positivity :
      (0 : ℝ) < 64 * (L : ℝ))).2
    apply (div_le_iff₀ hmpos).2
    simpa [mul_comm] using hedgeCapR
  simpa [m, L, d, d₀] using And.intro hedgeCore
    (And.intro hd₀ (And.intro hcap hd₀min))

lemma low_ready_inputs
    (m n e : ℕ) (d₀ Q : ℝ) (D : Bool → ℝ)
    (hm : 64 ≤ m) (hready : HostPowerReady m)
    (hn : n ≤ m)
    (hDnonneg : ∀ b, 0 ≤ D b)
    (hDcap : ∀ b, D b ≤
      2 * (regularFactor + 1 : ℕ) * (m : ℝ) ^ ((10 : ℝ) / 21))
    (hedge : ∀ b, (e : ℝ) ≤ (m : ℝ) * D b)
    (hd₀ : (m : ℝ) ^ ((10 : ℝ) / 21) <
      32768 * ((Nat.log 2 m + 1 : ℕ) : ℝ) ^ (3 : ℕ) * d₀)
    (hQ : Q ≤ (m : ℝ) ^ ((13 : ℝ) / 21) / 4) :
    let s := ⌈(m : ℝ) ^ ((2 : ℝ) / 7)⌉₊
    let β := (m : ℝ) ^ (-(1 : ℝ) / 14)
    let t₀ : Bool → ℝ := fun _ ↦ (m : ℝ) ^ ((1 : ℝ) / 4)
    let t₂ : Bool → ℝ := fun _ ↦ (m : ℝ) ^ ((3 : ℝ) / 8)
    (0 < s) ∧
    (∀ b, 896 * D b * t₀ b * (n : ℝ) ^ ((1 : ℝ) / 28) ≤ d₀ ^ (2 : ℕ)) ∧
    (∀ b, 896 * D b * t₂ b * (n : ℝ) ^ ((1 : ℝ) / 28) ≤ d₀ ^ (2 : ℕ)) ∧
    (∀ b, 896 * 28 * (t₀ b)⁻¹ ≤ 1) ∧
    (∀ b, 896 * (Q / s) * (t₂ b)⁻¹ ≤ 1) ∧
    (448 * s : ℝ) * e * (D false * D true) ^ (26 : ℕ) ≤
      β * d₀ ^ (56 : ℕ) := by
  let s := ⌈(m : ℝ) ^ ((2 : ℝ) / 7)⌉₊
  let β := (m : ℝ) ^ (-(1 : ℝ) / 14)
  let t₀ : Bool → ℝ := fun _ ↦ (m : ℝ) ^ ((1 : ℝ) / 4)
  let t₂ : Bool → ℝ := fun _ ↦ (m : ℝ) ^ ((3 : ℝ) / 8)
  let L : ℝ := (Nat.log 2 m + 1 : ℕ)
  let R : ℝ := regularFactor + 1
  have hmpos : (0 : ℝ) < m := by positivity
  have hmone : (1 : ℝ) ≤ m := by
    exact_mod_cast (show 1 ≤ m by omega)
  have hLpos : 0 < L := by dsimp [L]; positivity
  change (m : ℝ) ^ ((10 : ℝ) / 21) <
    32768 * L ^ (3 : ℕ) * d₀ at hd₀
  have hd₀pos : 0 < d₀ := by
    have hright : 0 < 32768 * L ^ (3 : ℕ) * d₀ :=
      (Real.rpow_pos_of_pos hmpos _).trans hd₀
    have hc : 0 < (32768 * L ^ (3 : ℕ) : ℝ) := by positivity
    have hprod : 0 < (32768 * L ^ (3 : ℕ)) * d₀ := by
      simpa only [mul_assoc] using hright
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.2
    · exact (not_lt_of_ge hc.le h.1).elim
  have hsLower : (m : ℝ) ^ ((2 : ℝ) / 7) ≤ s := by
    exact Nat.le_ceil _
  have hsUpper : (s : ℝ) ≤ 2 * (m : ℝ) ^ ((2 : ℝ) / 7) := by
    have hceil := Nat.ceil_lt_add_one
      (Real.rpow_nonneg hmpos.le ((2 : ℝ) / 7))
    have hone : 1 ≤ (m : ℝ) ^ ((2 : ℝ) / 7) :=
      Real.one_le_rpow hmone (by norm_num)
    dsimp [s]
    linarith
  have hspos : 0 < s := by
    rw [show s = ⌈(m : ℝ) ^ ((2 : ℝ) / 7)⌉₊ by rfl,
      Nat.ceil_pos]
    exact Real.rpow_pos_of_pos hmpos _
  have hnroot : (n : ℝ) ^ ((1 : ℝ) / 28) ≤
      (m : ℝ) ^ ((1 : ℝ) / 28) := by
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast hn
    · norm_num
  have hpowProduct :
      (m : ℝ) ^ ((10 : ℝ) / 21) *
          (m : ℝ) ^ ((3 : ℝ) / 8) *
          (m : ℝ) ^ ((1 : ℝ) / 28) =
        (m : ℝ) ^ ((149 : ℝ) / 168) := by
    rw [← Real.rpow_add hmpos, ← Real.rpow_add hmpos]
    congr 2
    norm_num
  have hd₀sq : (m : ℝ) ^ ((20 : ℝ) / 21) <
      32768 ^ (2 : ℕ) * L ^ (6 : ℕ) * d₀ ^ (2 : ℕ) := by
    have hsquare := (sq_lt_sq₀
      (Real.rpow_nonneg hmpos.le ((10 : ℝ) / 21))
      (by positivity : 0 ≤ 32768 * L ^ (3 : ℕ) * d₀)).mpr hd₀
    have hbase :
        ((m : ℝ) ^ ((10 : ℝ) / 21)) ^ (2 : ℕ) =
          (m : ℝ) ^ ((20 : ℝ) / 21) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
      norm_num
    rw [hbase] at hsquare
    calc
      (m : ℝ) ^ ((20 : ℝ) / 21) <
          (32768 * L ^ (3 : ℕ) * d₀) ^ (2 : ℕ) := hsquare
      _ = 32768 ^ (2 : ℕ) * L ^ (6 : ℕ) * d₀ ^ (2 : ℕ) := by ring
  rcases hready with ⟨hr₁, hr₂, hr₃, hr₄, _hr₅, _hr₆, _hr₇, _hr₈⟩
  change (1792 * R * 32768 ^ (2 : ℕ)) *
      (m : ℝ) ^ ((149 : ℝ) / 168) * L ^ (6 : ℕ) ≤
        (m : ℝ) ^ ((20 : ℝ) / 21) at hr₁
  change 25088 * (m : ℝ) ^ (0 : ℝ) ≤
      (m : ℝ) ^ ((1 : ℝ) / 4) at hr₂
  change 224 * (m : ℝ) ^ ((1 : ℝ) / 3) ≤
      (m : ℝ) ^ ((3 : ℝ) / 8) at hr₃
  change (1792 * R * (4 * R ^ (2 : ℕ)) ^ (26 : ℕ) *
      32768 ^ (56 : ℕ)) * (m : ℝ) ^ ((557 : ℝ) / 21) *
        L ^ (168 : ℕ) ≤ (m : ℝ) ^ ((1117 : ℝ) / 42) at hr₄
  have hDcapR (b : Bool) : D b ≤
      2 * R * (m : ℝ) ^ ((10 : ℝ) / 21) := by
    simpa [R, Nat.cast_add] using hDcap b
  have hinterp₂ (b : Bool) :
      896 * D b * t₂ b * (n : ℝ) ^ ((1 : ℝ) / 28) ≤ d₀ ^ (2 : ℕ) := by
    have hscaled :
        (1792 * R * (m : ℝ) ^ ((149 : ℝ) / 168)) *
            (32768 ^ (2 : ℕ) * L ^ (6 : ℕ)) ≤
          (32768 ^ (2 : ℕ) * L ^ (6 : ℕ)) * d₀ ^ (2 : ℕ) := by
      calc
        _ = (1792 * R * 32768 ^ (2 : ℕ)) *
            (m : ℝ) ^ ((149 : ℝ) / 168) * L ^ (6 : ℕ) := by ring
        _ ≤ (m : ℝ) ^ ((20 : ℝ) / 21) := hr₁
        _ ≤ _ := hd₀sq.le
    have hmain : 1792 * R * (m : ℝ) ^ ((149 : ℝ) / 168) ≤
        d₀ ^ (2 : ℕ) := by
      exact (mul_le_mul_iff_right₀ (by positivity :
        (0 : ℝ) < 32768 ^ (2 : ℕ) * L ^ (6 : ℕ))).mp (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
    calc
      896 * D b * t₂ b * (n : ℝ) ^ ((1 : ℝ) / 28) ≤
          896 * (2 * R * (m : ℝ) ^ ((10 : ℝ) / 21)) *
            (m : ℝ) ^ ((3 : ℝ) / 8) *
              (m : ℝ) ^ ((1 : ℝ) / 28) := by
        dsimp [t₂, R]
        gcongr
        · simpa [R, Nat.cast_add] using hDcap b
      _ = 1792 * R * (m : ℝ) ^ ((149 : ℝ) / 168) := by
        rw [← hpowProduct]
        ring
      _ ≤ _ := hmain
  have ht₀le (b : Bool) : t₀ b ≤ t₂ b := by
    dsimp [t₀, t₂]
    exact Real.rpow_le_rpow_of_exponent_le hmone (by norm_num)
  have hinterp₀ (b : Bool) :
      896 * D b * t₀ b * (n : ℝ) ^ ((1 : ℝ) / 28) ≤ d₀ ^ (2 : ℕ) := by
    calc
      _ ≤ 896 * D b * t₂ b * (n : ℝ) ^ ((1 : ℝ) / 28) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (ht₀le b)
            (mul_nonneg (by norm_num) (hDnonneg b)))
          (Real.rpow_nonneg (by positivity) _)
      _ ≤ _ := hinterp₂ b
  have hinv₀ (b : Bool) : 896 * 28 * (t₀ b)⁻¹ ≤ 1 := by
    have htpos : 0 < t₀ b := by dsimp [t₀]; positivity
    apply (mul_inv_le_iff₀ htpos).2
    dsimp [t₀]
    norm_num [Real.rpow_zero] at hr₂ ⊢
    simpa using hr₂
  have hinv₂ (b : Bool) : 896 * (Q / s) * (t₂ b)⁻¹ ≤ 1 := by
    have htpos : 0 < t₂ b := by dsimp [t₂]; positivity
    apply (mul_inv_le_iff₀ htpos).2
    have hsLowerPos : 0 < (s : ℝ) := by positivity
    have hdiv : Q / s ≤ (m : ℝ) ^ ((1 : ℝ) / 3) / 4 := by
      apply (div_le_iff₀ hsLowerPos).2
      calc
        Q ≤ (m : ℝ) ^ ((13 : ℝ) / 21) / 4 := hQ
        _ = ((m : ℝ) ^ ((1 : ℝ) / 3) / 4) *
            (m : ℝ) ^ ((2 : ℝ) / 7) := by
          rw [show (m : ℝ) ^ ((13 : ℝ) / 21) =
            (m : ℝ) ^ ((1 : ℝ) / 3) *
              (m : ℝ) ^ ((2 : ℝ) / 7) by
                rw [← Real.rpow_add hmpos]
                norm_num]
          ring
        _ ≤ ((m : ℝ) ^ ((1 : ℝ) / 3) / 4) * s := by gcongr
    calc
      896 * (Q / s) ≤ 896 * ((m : ℝ) ^ ((1 : ℝ) / 3) / 4) := by gcongr
      _ = 224 * (m : ℝ) ^ ((1 : ℝ) / 3) := by ring
      _ ≤ (m : ℝ) ^ ((3 : ℝ) / 8) := hr₃
      _ = 1 * t₂ b := by simp [t₂]
  have hpattern : (448 * s : ℝ) * e *
      (D false * D true) ^ (26 : ℕ) ≤ β * d₀ ^ (56 : ℕ) := by
    have he : (e : ℝ) ≤
        (m : ℝ) * (2 * R * (m : ℝ) ^ ((10 : ℝ) / 21)) :=
      (hedge false).trans (mul_le_mul_of_nonneg_left
        (hDcapR false) hmpos.le)
    have hDD : D false * D true ≤
        (2 * R * (m : ℝ) ^ ((10 : ℝ) / 21)) *
          (2 * R * (m : ℝ) ^ ((10 : ℝ) / 21)) :=
      mul_le_mul (hDcapR false) (hDcapR true) (hDnonneg true)
        (by positivity)
    have hleft : (448 * s : ℝ) * e * (D false * D true) ^ (26 : ℕ) ≤
        (1792 * R * (4 * R ^ (2 : ℕ)) ^ (26 : ℕ)) *
          (m : ℝ) ^ ((557 : ℝ) / 21) := by
      calc
        _ ≤ 448 * (2 * (m : ℝ) ^ ((2 : ℝ) / 7)) *
            ((m : ℝ) * (2 * R * (m : ℝ) ^ ((10 : ℝ) / 21))) *
            ((2 * R * (m : ℝ) ^ ((10 : ℝ) / 21)) *
              (2 * R * (m : ℝ) ^ ((10 : ℝ) / 21))) ^ (26 : ℕ) := by
          gcongr
          all_goals first
            | exact hsUpper
            | exact he
            | exact hDD
            | exact mul_nonneg (hDnonneg false) (hDnonneg true)
            | positivity
        _ = _ := by
          have hm557 : (m : ℝ) ^ ((2 : ℝ) / 7) * m *
              (m : ℝ) ^ ((10 : ℝ) / 21) *
              (((m : ℝ) ^ ((10 : ℝ) / 21) *
                (m : ℝ) ^ ((10 : ℝ) / 21)) ^ (26 : ℕ)) =
              (m : ℝ) ^ ((557 : ℝ) / 21) := by
            rw [show (m : ℝ) ^ ((10 : ℝ) / 21) *
                (m : ℝ) ^ ((10 : ℝ) / 21) =
                (m : ℝ) ^ ((20 : ℝ) / 21) by
                  rw [← Real.rpow_add hmpos]
                  norm_num]
            rw [show ((m : ℝ) ^ ((20 : ℝ) / 21)) ^ (26 : ℕ) =
                (m : ℝ) ^ ((520 : ℝ) / 21) by
                  rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
                  norm_num]
            have hA : (m : ℝ) ^ ((2 : ℝ) / 7) * m =
                (m : ℝ) ^ ((9 : ℝ) / 7) := by
              calc
                _ = (m : ℝ) ^ ((2 : ℝ) / 7) * (m : ℝ) ^ (1 : ℝ) := by
                  rw [Real.rpow_one]
                _ = (m : ℝ) ^ ((2 : ℝ) / 7 + 1) :=
                  (Real.rpow_add hmpos _ _).symm
                _ = _ := by norm_num
            have hB : (m : ℝ) ^ ((10 : ℝ) / 21) *
                (m : ℝ) ^ ((520 : ℝ) / 21) =
                (m : ℝ) ^ ((530 : ℝ) / 21) := by
              rw [← Real.rpow_add hmpos]
              norm_num
            rw [show (m : ℝ) ^ ((2 : ℝ) / 7) * m *
                (m : ℝ) ^ ((10 : ℝ) / 21) *
                (m : ℝ) ^ ((520 : ℝ) / 21) =
                ((m : ℝ) ^ ((2 : ℝ) / 7) * m) *
                  ((m : ℝ) ^ ((10 : ℝ) / 21) *
                    (m : ℝ) ^ ((520 : ℝ) / 21)) by ring,
              hA, hB, ← Real.rpow_add hmpos]
            norm_num
          rw [show (2 * R * (m : ℝ) ^ ((10 : ℝ) / 21)) *
              (2 * R * (m : ℝ) ^ ((10 : ℝ) / 21)) =
              (4 * R ^ (2 : ℕ)) *
                ((m : ℝ) ^ ((10 : ℝ) / 21) *
                  (m : ℝ) ^ ((10 : ℝ) / 21)) by ring,
            mul_pow, ← hm557]
          ring
    have hd₀pow : (m : ℝ) ^ ((560 : ℝ) / 21) <
        32768 ^ (56 : ℕ) * L ^ (168 : ℕ) * d₀ ^ (56 : ℕ) := by
      have hp := pow_lt_pow_left₀ hd₀
        (Real.rpow_nonneg hmpos.le _) (by omega : (56 : ℕ) ≠ 0)
      have hbase : ((m : ℝ) ^ ((10 : ℝ) / 21)) ^ (56 : ℕ) =
          (m : ℝ) ^ ((560 : ℝ) / 21) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
        norm_num
      rw [hbase] at hp
      calc
        (m : ℝ) ^ ((560 : ℝ) / 21) <
            (32768 * L ^ (3 : ℕ) * d₀) ^ (56 : ℕ) := hp
        _ = 32768 ^ (56 : ℕ) * L ^ (168 : ℕ) * d₀ ^ (56 : ℕ) := by
          rw [mul_pow, mul_pow, ← pow_mul]
    have hβpow : β * (m : ℝ) ^ ((560 : ℝ) / 21) =
        (m : ℝ) ^ ((1117 : ℝ) / 42) := by
      dsimp [β]
      rw [← Real.rpow_add hmpos]
      congr 2
      norm_num
    have hscaled :
        (1792 * R * (4 * R ^ (2 : ℕ)) ^ (26 : ℕ) *
            (m : ℝ) ^ ((557 : ℝ) / 21)) *
            (32768 ^ (56 : ℕ) * L ^ (168 : ℕ)) ≤
          (32768 ^ (56 : ℕ) * L ^ (168 : ℕ)) *
            (β * d₀ ^ (56 : ℕ)) := by
      calc
        _ = (1792 * R * (4 * R ^ (2 : ℕ)) ^ (26 : ℕ) *
            32768 ^ (56 : ℕ)) * (m : ℝ) ^ ((557 : ℝ) / 21) *
              L ^ (168 : ℕ) := by ring
        _ ≤ (m : ℝ) ^ ((1117 : ℝ) / 42) := hr₄
        _ = β * (m : ℝ) ^ ((560 : ℝ) / 21) := hβpow.symm
        _ ≤ β * (32768 ^ (56 : ℕ) * L ^ (168 : ℕ) *
              d₀ ^ (56 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left hd₀pow.le (by positivity)
        _ = _ := by ring
    have hmain :
        1792 * R * (4 * R ^ (2 : ℕ)) ^ (26 : ℕ) *
            (m : ℝ) ^ ((557 : ℝ) / 21) ≤ β * d₀ ^ (56 : ℕ) := by
      exact (mul_le_mul_iff_right₀ (by positivity :
        (0 : ℝ) < 32768 ^ (56 : ℕ) * L ^ (168 : ℕ))).mp (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
    exact hleft.trans hmain
  simpa [s, β, t₀, t₂] using
    And.intro hspos (And.intro hinterp₀ (And.intro hinterp₂
      (And.intro hinv₀ (And.intro hinv₂ hpattern))))

lemma sparseCore_low_branch
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : SparseCore G) :
    letI : Fintype C.W := C.fintypeW
    letI : DecidableEq C.W := C.decEqW
    letI : DecidableRel C.graph.Adj := C.decAdj
    ∀ (H : DenseHostCell C.graph) (K : MinDegreeHostCell H),
      HostPowerReady C.order →
      1568 * (C.order : ℝ) ^ (-(1 : ℝ) / 14) <
        cleanSelectorThreshold (Fintype.card (SliceTuple C.W)) →
      (((orderedFourCycles H.edges).card + 1 : ℕ) : ℝ) ≤
        (H.edges.card : ℝ) *
          (C.order : ℝ) ^ ((13 : ℝ) / 21) /
            (256 * degreeBinCount (W := C.W)) →
      janzerGraph ⊑ G := by
  letI : Fintype C.W := C.fintypeW
  letI : DecidableEq C.W := C.decEqW
  letI : DecidableRel C.graph.Adj := C.decAdj
  intro H K hready hsmall hlow
  let m := C.order
  let L := degreeBinCount (W := C.W)
  let d : ℝ := H.edges.card
  let d₀ := d / (64 * m * L)
  let P := liveGraph K.edges
  let n := Fintype.card (LiveVertex K.edges)
  let e := P.edgeFinset.card
  let Q : ℝ := H.dynamicCycleCap
  let D : Bool → ℝ := fun b ↦ H.sideCap b
  let s := ⌈(m : ℝ) ^ ((2 : ℝ) / 7)⌉₊
  let β := (m : ℝ) ^ (-(1 : ℝ) / 14)
  let t₀ : Bool → ℝ := fun _ ↦ (m : ℝ) ^ ((1 : ℝ) / 4)
  let t₂ : Bool → ℝ := fun _ ↦ (m : ℝ) ^ ((3 : ℝ) / 8)
  let W : ℝ := Conflict.closedWalkCount P 56
  have hm : 64 ≤ m := by simpa [m, SparseCore.order] using C.order_large
  have hmpos : (0 : ℝ) < m := by positivity
  have hLpos : (0 : ℝ) < L := by dsimp [L, degreeBinCount]; positivity
  have hdpos : 0 < d := by dsimp [d]; exact_mod_cast H.edges_nonempty.card_pos
  obtain ⟨_hcore, hd₀lower, hDcap, hd₀min⟩ :=
    sparseCore_denseCell_common C H
  change (m : ℝ) ^ ((10 : ℝ) / 21) <
    32768 * (L : ℝ) ^ (3 : ℕ) * d₀ at hd₀lower
  have hd₀pos : 0 < d₀ := by
    have hright : 0 < 32768 * (L : ℝ) ^ (3 : ℕ) * d₀ :=
      (Real.rpow_pos_of_pos hmpos _).trans hd₀lower
    have hc : 0 < (32768 * (L : ℝ) ^ (3 : ℕ) : ℝ) := by positivity
    have hprod : 0 < (32768 * (L : ℝ) ^ (3 : ℕ)) * d₀ := by
      simpa only [mul_assoc] using hright
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.2
    · exact (not_lt_of_ge hc.le h.1).elim
  have hPedge : P.edgeFinset.Nonempty := by
    apply Finset.card_pos.mp
    change 0 < P.edgeFinset.card
    rw [show P.edgeFinset.card = K.edges.card by
      simpa [P] using K.liveGraph_edge_card]
    exact K.edges_nonempty.card_pos
  letI : Nonempty (LiveVertex K.edges) := by
    obtain ⟨z, hz⟩ := hPedge
    induction z using Sym2.inductionOn with
    | _ x y => exact ⟨x⟩
  have hn : n ≤ m := by
    dsimp [n, m, SparseCore.order]
    exact Fintype.card_subtype_le _
  have hn2 : 2 ≤ n := by
    obtain ⟨z, hz⟩ := hPedge
    induction z using Sym2.inductionOn with
    | _ x y =>
      have hxy : P.Adj x y := P.mem_edgeFinset.mp hz
      have hdegpos : 0 < P.degree x :=
        (P.degree_pos_iff_exists_adj x).2 ⟨y, hxy⟩
      have hdeglt : P.degree x < n := by
        simpa [n] using P.degree_lt_card_verts x
      omega
  have hedge (b : Bool) : (e : ℝ) ≤ (m : ℝ) * D b := by
    have h₁ : e ≤ H.edges.card := by
      rw [show e = K.edges.card by simpa [e, P] using K.liveGraph_edge_card]
      exact Finset.card_le_card K.edges_subset
    have h₂ : H.edges.card ≤ m * H.sideCap b := by
      simpa [m, SparseCore.order] using H.edge_card_le_card_mul_sideCap b
    have hR : (e : ℝ) ≤ ((m * H.sideCap b : ℕ) : ℝ) := by
      exact_mod_cast h₁.trans h₂
    norm_num [Nat.cast_mul, D] at hR ⊢
    simpa [D] using hR
  have hQbound : Q ≤ (m : ℝ) ^ ((13 : ℝ) / 21) / 4 := by
    have hnat : H.dynamicCycleCap * H.edges.card ≤
        64 * L * ((orderedFourCycles H.edges).card + 1) := by
      dsimp [DenseHostCell.dynamicCycleCap]
      exact Nat.div_mul_le_self _ _
    have hreal : Q * d ≤
        64 * (L : ℝ) * (((orderedFourCycles H.edges).card + 1 : ℕ) : ℝ) := by
      have hR : ((H.dynamicCycleCap * H.edges.card : ℕ) : ℝ) ≤
          ((64 * L * ((orderedFourCycles H.edges).card + 1) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      norm_num [Nat.cast_mul, Q, d] at hR ⊢
      simpa [Q, d] using hR
    have hlow' : (((orderedFourCycles H.edges).card + 1 : ℕ) : ℝ) ≤
        d * (m : ℝ) ^ ((13 : ℝ) / 21) / (256 * (L : ℝ)) := by
      simpa [m, L, d, Nat.cast_mul] using hlow
    have hprod : Q * d ≤ ((m : ℝ) ^ ((13 : ℝ) / 21) / 4) * d := by
      calc
        Q * d ≤ 64 * (L : ℝ) *
          (d * (m : ℝ) ^ ((13 : ℝ) / 21) / (256 * L)) := by
          exact hreal.trans (mul_le_mul_of_nonneg_left hlow' (by positivity))
        _ = ((m : ℝ) ^ ((13 : ℝ) / 21) / 4) * d := by
          field_simp
          ring
    exact (mul_le_mul_iff_left₀ hdpos).mp (by
      simpa [mul_comm] using hprod)
  have hDnonneg (b : Bool) : 0 ≤ D b := by dsimp [D]; positivity
  obtain ⟨hspos, hinterp₀, hinterp₂, hinv₀, hinv₂, hpattern⟩ :=
    low_ready_inputs m n e d₀ Q D hm (by simpa [m] using hready) hn
      hDnonneg (by simpa [m, D] using hDcap) hedge
      (by exact hd₀lower) hQbound
  have hWlower : d₀ ^ (56 : ℕ) ≤ W := by
    apply closedWalkCount_56_lower_of_minDegree P d₀ hd₀pos.le
    intro v
    exact (hd₀min (liveSide K.edges H.color v)).trans
      (K.live_degree_lower_real v)
  have hfew := few_branch_numerics n s e W d₀ β Q D t₀ t₂
    hspos hd₀pos (by dsimp [β]; positivity) hDnonneg
    (fun _ ↦ by dsimp [t₀]; positivity) (fun _ ↦ by dsimp [t₂]; positivity)
    (by dsimp [Q]; positivity) hWlower hinterp₀ hinterp₂ hinv₀ hinv₂ hpattern
  have hdeg (v : LiveVertex K.edges) : (P.degree v : ℝ) ≤
      D (liveSide K.edges H.color v) := by
    simpa [P, D] using K.live_degree_upper_real v
  have hcap (u y : LiveVertex K.edges) (huy : P.Adj y u) :
      ((Erdos113FourCycles.extensionsThroughEdge P u y).card : ℝ) ≤
        (fun _ : Bool ↦ Q) (liveSide K.edges H.color y) := by
    have hnat := K.extensionsThroughEdge_le_dynamicCycleCap
      (by simpa [P] using huy)
    have hreal :
        ((Erdos113FourCycles.extensionsThroughEdge
          (liveGraph K.edges) u y).card : ℝ) ≤ (H.dynamicCycleCap : ℝ) := by
      exact_mod_cast hnat
    simpa only [P, Q] using hreal
  have hsmallLive : 1568 * β <
      cleanSelectorThreshold (Fintype.card (SliceTuple (LiveVertex K.edges))) := by
    calc
      1568 * β < cleanSelectorThreshold (Fintype.card (SliceTuple C.W)) := by
        simpa [β, m] using hsmall
      _ = cleanSelectorThreshold (Fintype.card (SliceTuple (Fin m))) := by
        congr 2
        simp [SliceTuple, m, SparseCore.order]
      _ ≤ cleanSelectorThreshold (Fintype.card (SliceTuple (Fin n))) :=
        cleanSelectorThreshold_slice_mono hn2 hn
      _ = cleanSelectorThreshold
          (Fintype.card (SliceTuple (LiveVertex K.edges))) := by
        congr 2
        simp [SliceTuple, n]
  have hcopyP : janzerGraph ⊑ P :=
    janzerGraph_isContained_of_fewFourCycle_bipartite_numerics
      P (liveSide K.edges H.color) s β (fun _ ↦ Q) D t₀ t₂ hspos
        (by dsimp [β]; positivity) (fun _ ↦ by dsimp [Q]; positivity)
        hDnonneg (fun _ ↦ by dsimp [t₀]; positivity)
        (fun _ ↦ by dsimp [t₂]; positivity)
        (fun {_ _} h ↦ K.live_cross (by simpa [P] using h)) hdeg hcap
        hfew.1 hfew.2.1 hfew.2.2 hsmallLive
  exact (hcopyP.trans K.liveGraph_isContained_original).trans C.contained

lemma high_ready_inputs
    (m L ℓ N a b f q d : ℕ)
    (hm : 64 ≤ m) (hL : L = Nat.log 2 m + 1)
    (hℓpos : 0 < ℓ) (hℓL : ℓ ≤ L)
    (hready : HostPowerReady m)
    (hcore : (m : ℝ) ^ ((31 : ℝ) / 21) <
      512 * (L : ℝ) ^ (2 : ℕ) * d)
    (hq : (d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21) /
      (512 * L) < q)
    (hNpos : 0 < N) (haN : a ≤ N) (hb : b < 2 * a)
    (hNcap : (N : ℝ) ≤
      (regularFactor + 1 : ℕ) * (m : ℝ) ^ ((10 : ℝ) / 21))
    (hfcap : f ≤ N ^ 2)
    (hselection : q ≤ 32 * m * L ^ 2 * b * f) :
    3136 * 2 ^ 27 ≤ b ∧
    702464 * (16 * (ℓ : ℝ)) * (2 * N : ℝ) ^ ((1 : ℝ) / 14) ≤
      (f : ℝ) / (32 * (ℓ : ℝ) ^ 3 * N) ∧
    let β := (m : ℝ) ^ (-(1 : ℝ) / 14)
    ((224 * 1536 * 512 ^ (26 : ℕ)) *
        (32 ^ (56 : ℕ) * (4 * 2 ^ (28 : ℕ))) : ℝ) *
        m ^ (28 : ℕ) * L ^ (167 : ℕ) * N ^ (29 : ℕ) ≤
      β * q * d ^ (27 : ℕ) := by
  let R : ℝ := regularFactor + 1
  let β := (m : ℝ) ^ (-(1 : ℝ) / 14)
  have hmpos : (0 : ℝ) < m := by positivity
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := by rw [hL]; omega
    exact_mod_cast this
  have hℓposR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hdpos : (0 : ℝ) < d := by
    have hright : 0 < (512 * (L : ℝ) ^ (2 : ℕ)) * d :=
      (Real.rpow_pos_of_pos hmpos _).trans hcore
    rcases mul_pos_iff.mp hright with h | h
    · exact h.2
    · exact (not_lt_of_ge (by positivity :
        (0 : ℝ) ≤ 512 * L ^ (2 : ℕ)) h.1).elim
  have hNcapR : (N : ℝ) ≤ R * (m : ℝ) ^ ((10 : ℝ) / 21) := by
    simpa [R, Nat.cast_add] using hNcap
  have hqlower : (m : ℝ) ^ ((44 : ℝ) / 21) <
      512 ^ (2 : ℕ) * (L : ℝ) ^ (3 : ℕ) * q := by
    have hdenpos : (0 : ℝ) < 512 * L := by positivity
    have hqmul : (d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21) <
        (512 * (L : ℝ)) * q := by
      simpa [mul_comm] using (div_lt_iff₀ hdenpos).mp hq
    have hpow : (m : ℝ) ^ ((31 : ℝ) / 21) *
        (m : ℝ) ^ ((13 : ℝ) / 21) =
          (m : ℝ) ^ ((44 : ℝ) / 21) := by
      rw [← Real.rpow_add hmpos]
      congr 2
      norm_num
    calc
      (m : ℝ) ^ ((44 : ℝ) / 21) =
          (m : ℝ) ^ ((31 : ℝ) / 21) *
            (m : ℝ) ^ ((13 : ℝ) / 21) := hpow.symm
      _ < (512 * (L : ℝ) ^ (2 : ℕ) * d) *
          (m : ℝ) ^ ((13 : ℝ) / 21) := by gcongr
      _ = (512 * (L : ℝ) ^ (2 : ℕ)) *
          (d * (m : ℝ) ^ ((13 : ℝ) / 21)) := by ring
      _ < (512 * (L : ℝ) ^ (2 : ℕ)) *
          ((512 * L) * q) := by
        exact mul_lt_mul_of_pos_left hqmul (by positivity)
      _ = 512 ^ (2 : ℕ) * (L : ℝ) ^ (3 : ℕ) * q := by ring
  have hselectionR : (q : ℝ) ≤
      32 * m * (L : ℝ) ^ (2 : ℕ) * b * f := by exact_mod_cast hselection
  have hfcapR : (f : ℝ) ≤ (N : ℝ) ^ (2 : ℕ) := by exact_mod_cast hfcap
  have hNpow : (N : ℝ) ^ (2 : ℕ) ≤
      R ^ (2 : ℕ) * (m : ℝ) ^ ((20 : ℝ) / 21) := by
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ N) hNcapR
      (2 : ℕ)
    have hm20 : ((m : ℝ) ^ ((10 : ℝ) / 21)) ^ (2 : ℕ) =
        (m : ℝ) ^ ((20 : ℝ) / 21) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
      norm_num
    simpa [mul_pow, hm20] using hs
  have hqUpper : (q : ℝ) ≤
      32 * R ^ (2 : ℕ) * (L : ℝ) ^ (2 : ℕ) * b *
        (m : ℝ) ^ ((41 : ℝ) / 21) := by
    calc
      (q : ℝ) ≤ 32 * m * (L : ℝ) ^ (2 : ℕ) * b * f := hselectionR
      _ ≤ 32 * m * (L : ℝ) ^ (2 : ℕ) * b *
          (R ^ (2 : ℕ) * (m : ℝ) ^ ((20 : ℝ) / 21)) := by
        gcongr
        exact hfcapR.trans hNpow
      _ = _ := by
        have hm41 : (m : ℝ) * (m : ℝ) ^ ((20 : ℝ) / 21) =
            (m : ℝ) ^ ((41 : ℝ) / 21) := by
          calc
            _ = (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ ((20 : ℝ) / 21) := by
              rw [Real.rpow_one]
            _ = (m : ℝ) ^ (1 + (20 : ℝ) / 21) :=
              (Real.rpow_add hmpos _ _).symm
            _ = _ := by norm_num
        rw [show 32 * (m : ℝ) * (L : ℝ) ^ (2 : ℕ) * b *
            (R ^ (2 : ℕ) * (m : ℝ) ^ ((20 : ℝ) / 21)) =
            32 * R ^ (2 : ℕ) * (L : ℝ) ^ (2 : ℕ) * b *
              ((m : ℝ) * (m : ℝ) ^ ((20 : ℝ) / 21)) by ring,
          hm41]
  have hpone : (m : ℝ) ^ ((1 : ℝ) / 7) <
      8388608 * R ^ (2 : ℕ) * (L : ℝ) ^ (5 : ℕ) * b := by
    have h41pos : 0 < (m : ℝ) ^ ((41 : ℝ) / 21) :=
      Real.rpow_pos_of_pos hmpos _
    have hscaled : (m : ℝ) ^ ((41 : ℝ) / 21) *
        (m : ℝ) ^ ((1 : ℝ) / 7) <
      (m : ℝ) ^ ((41 : ℝ) / 21) *
        (8388608 * R ^ (2 : ℕ) * (L : ℝ) ^ (5 : ℕ) * b) := by
      calc
      (m : ℝ) ^ ((41 : ℝ) / 21) * (m : ℝ) ^ ((1 : ℝ) / 7) =
          (m : ℝ) ^ ((44 : ℝ) / 21) := by
        rw [← Real.rpow_add hmpos]
        congr 2
        norm_num
      _ < 512 ^ (2 : ℕ) * (L : ℝ) ^ (3 : ℕ) * q := hqlower
      _ ≤ 512 ^ (2 : ℕ) * (L : ℝ) ^ (3 : ℕ) *
          (32 * R ^ (2 : ℕ) * (L : ℝ) ^ (2 : ℕ) * b *
            (m : ℝ) ^ ((41 : ℝ) / 21)) := by gcongr
      _ = (m : ℝ) ^ ((41 : ℝ) / 21) *
          (8388608 * R ^ (2 : ℕ) * (L : ℝ) ^ (5 : ℕ) * b) := by ring
    exact lt_of_mul_lt_mul_left hscaled h41pos.le
  rcases hready with ⟨_hr₁, _hr₂, _hr₃, _hr₄, _hr₅, hr₆, hr₇, hr₈⟩
  rw [← hL] at hr₆ hr₇ hr₈
  change (8388608 * R ^ (2 : ℕ) * (3136 * 2 ^ (27 : ℕ))) *
      (m : ℝ) ^ (0 : ℝ) * (L : ℝ) ^ (5 : ℕ) ≤
        (m : ℝ) ^ ((1 : ℝ) / 7) at hr₆
  have hliftR : (3136 * 2 ^ (27 : ℕ) : ℝ) ≤ b := by
    have hcpos : 0 < 8388608 * R ^ (2 : ℕ) * (L : ℝ) ^ (5 : ℕ) := by positivity
    have hscaled :
        (8388608 * R ^ (2 : ℕ) * (L : ℝ) ^ (5 : ℕ)) *
            (3136 * 2 ^ (27 : ℕ) : ℝ) ≤
          (8388608 * R ^ (2 : ℕ) * (L : ℝ) ^ (5 : ℕ)) * b := by
      calc
      (8388608 * R ^ (2 : ℕ) * (L : ℝ) ^ (5 : ℕ)) *
          (3136 * 2 ^ (27 : ℕ) : ℝ) =
          (8388608 * R ^ (2 : ℕ) * (3136 * 2 ^ (27 : ℕ))) *
            (m : ℝ) ^ (0 : ℝ) * (L : ℝ) ^ (5 : ℕ) := by
        rw [Real.rpow_zero]
        ring
      _ ≤ (m : ℝ) ^ ((1 : ℝ) / 7) := hr₆
      _ ≤ 8388608 * R ^ (2 : ℕ) * (L : ℝ) ^ (5 : ℕ) * b := hpone.le
      _ = _ := by ring
    exact le_of_mul_le_mul_left hscaled hcpos
  have hlift : 3136 * 2 ^ 27 ≤ b := by exact_mod_cast hliftR
  have hbN : (b : ℝ) < 2 * N := by
    exact_mod_cast hb.trans_le (Nat.mul_le_mul_left 2 haN)
  have hqpos : (0 : ℝ) < q :=
    (div_pos (mul_pos hdpos (Real.rpow_pos_of_pos hmpos _)) (by positivity)).trans hq
  have hqposNat : 0 < q := by exact_mod_cast hqpos
  have hfpos : (0 : ℝ) < f := by
    have : 0 < f := by
      by_contra! hf
      have : f = 0 := by omega
      rw [this] at hselection
      simp at hselection
      omega
    exact_mod_cast this
  have hqUpperF : (q : ℝ) <
      64 * (m : ℝ) * (L : ℝ) ^ (2 : ℕ) * N * f := by
    calc
      (q : ℝ) ≤ 32 * m * (L : ℝ) ^ (2 : ℕ) * b * f := hselectionR
      _ < 32 * m * (L : ℝ) ^ (2 : ℕ) * (2 * N) * f := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left hbN (by positivity)) hfpos
      _ = _ := by ring
  have hfLower : (m : ℝ) ^ ((23 : ℝ) / 21) <
      16777216 * (L : ℝ) ^ (5 : ℕ) * N * f := by
    have hm23pos : 0 < (m : ℝ) := hmpos
    have hscaled : (m : ℝ) * (m : ℝ) ^ ((23 : ℝ) / 21) <
        (m : ℝ) * (16777216 * (L : ℝ) ^ (5 : ℕ) * N * f) := by
      calc
      (m : ℝ) * (m : ℝ) ^ ((23 : ℝ) / 21) =
          (m : ℝ) ^ ((44 : ℝ) / 21) := by
        calc
          _ = (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ ((23 : ℝ) / 21) := by
            rw [Real.rpow_one]
          _ = (m : ℝ) ^ (1 + (23 : ℝ) / 21) :=
            (Real.rpow_add hmpos _ _).symm
          _ = _ := by norm_num
      _ < 512 ^ (2 : ℕ) * (L : ℝ) ^ (3 : ℕ) * q := hqlower
      _ < 512 ^ (2 : ℕ) * (L : ℝ) ^ (3 : ℕ) *
          (64 * (m : ℝ) * (L : ℝ) ^ (2 : ℕ) * N * f) := by gcongr
      _ = (m : ℝ) * (16777216 * (L : ℝ) ^ (5 : ℕ) * N * f) := by ring
    exact lt_of_mul_lt_mul_left hscaled hm23pos.le
  change ((702464 * 512) * 16777216 * R ^ (2 : ℕ) *
      (2 * R) ^ ((1 : ℝ) / 14)) *
      (m : ℝ) ^ ((25 : ℝ) / 49) * (L : ℝ) ^ (9 : ℕ) ≤
        (m : ℝ) ^ ((13 : ℝ) / 21) at hr₇
  have hNroot : (2 * N : ℝ) ^ ((1 : ℝ) / 14) ≤
      (2 * R) ^ ((1 : ℝ) / 14) *
        (m : ℝ) ^ ((5 : ℝ) / 147) := by
    have hbase : (2 * N : ℝ) ≤
        (2 * R) * (m : ℝ) ^ ((10 : ℝ) / 21) := by
      calc
        (2 : ℝ) * N ≤ 2 * (R * (m : ℝ) ^ ((10 : ℝ) / 21)) := by gcongr
        _ = _ := by ring
    have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 * N)
      hbase (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 14)
    calc
      _ ≤ ((2 * R) * (m : ℝ) ^ ((10 : ℝ) / 21)) ^
          ((1 : ℝ) / 14) := hp
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hmpos.le]
        norm_num
  have hsuperNumerator :
      (702464 * 512 : ℝ) * (ℓ : ℝ) ^ (4 : ℕ) * N *
          (2 * N : ℝ) ^ ((1 : ℝ) / 14) ≤ f := by
    have hleft :
        ((702464 * 512 : ℝ) * (ℓ : ℝ) ^ (4 : ℕ) * N *
          (2 * N : ℝ) ^ ((1 : ℝ) / 14)) *
          (16777216 * (L : ℝ) ^ (5 : ℕ) * N) ≤
        (m : ℝ) ^ ((23 : ℝ) / 21) := by
      calc
        _ ≤ ((702464 * 512 : ℝ) * (L : ℝ) ^ (4 : ℕ) *
            (R * (m : ℝ) ^ ((10 : ℝ) / 21)) *
            ((2 * R) ^ ((1 : ℝ) / 14) *
              (m : ℝ) ^ ((5 : ℝ) / 147))) *
            (16777216 * (L : ℝ) ^ (5 : ℕ) *
              (R * (m : ℝ) ^ ((10 : ℝ) / 21))) := by
          gcongr
          all_goals first
            | exact hNcapR
            | exact hNroot
            | exact_mod_cast hℓL
            | positivity
        _ = (((702464 * 512) * 16777216 * R ^ (2 : ℕ) *
              (2 * R) ^ ((1 : ℝ) / 14)) *
              (m : ℝ) ^ ((25 : ℝ) / 49) * (L : ℝ) ^ (9 : ℕ)) *
              (m : ℝ) ^ ((10 : ℝ) / 21) := by
          have hpow25 : (m : ℝ) ^ ((5 : ℝ) / 147) *
              (m : ℝ) ^ ((10 : ℝ) / 21) =
              (m : ℝ) ^ ((25 : ℝ) / 49) := by
            rw [← Real.rpow_add hmpos]
            congr 2
            norm_num
          let K₀ : ℝ := (702464 * 512) * 16777216 * R ^ (2 : ℕ) *
            (2 * R) ^ ((1 : ℝ) / 14) *
              (m : ℝ) ^ ((10 : ℝ) / 21) * (L : ℝ) ^ (9 : ℕ)
          calc
            _ = K₀ * ((m : ℝ) ^ ((5 : ℝ) / 147) *
                (m : ℝ) ^ ((10 : ℝ) / 21)) := by
              dsimp [K₀]
              ring
            _ = K₀ * (m : ℝ) ^ ((25 : ℝ) / 49) := by rw [hpow25]
            _ = _ := by
              dsimp [K₀]
              ring
        _ ≤ (m : ℝ) ^ ((13 : ℝ) / 21) *
            (m : ℝ) ^ ((10 : ℝ) / 21) := by gcongr
        _ = (m : ℝ) ^ ((23 : ℝ) / 21) := by
          rw [← Real.rpow_add hmpos]
          congr 2
          norm_num
    have hdenpos : 0 < 16777216 * (L : ℝ) ^ (5 : ℕ) * N := by positivity
    have hscaled := hleft.trans hfLower.le
    exact (mul_le_mul_iff_right₀ hdenpos).mp (by
      simpa [mul_comm] using hscaled)
  have hsuper :
      702464 * (16 * (ℓ : ℝ)) * (2 * N : ℝ) ^ ((1 : ℝ) / 14) ≤
        (f : ℝ) / (32 * (ℓ : ℝ) ^ 3 * N) := by
    apply (le_div_iff₀ (by positivity :
      (0 : ℝ) < 32 * (ℓ : ℝ) ^ 3 * N)).2
    calc
      702464 * (16 * (ℓ : ℝ)) * (2 * N : ℝ) ^ ((1 : ℝ) / 14) *
          (32 * (ℓ : ℝ) ^ 3 * N) =
        (702464 * 512 : ℝ) * (ℓ : ℝ) ^ (4 : ℕ) * N *
          (2 * N : ℝ) ^ ((1 : ℝ) / 14) := by ring
      _ ≤ f := hsuperNumerator
  change (((224 * 1536 * 512 ^ (26 : ℕ)) *
      (32 ^ (56 : ℕ) * (4 * 2 ^ (28 : ℕ)))) *
      R ^ (29 : ℕ) * 512 ^ (29 : ℕ)) *
      (m : ℝ) ^ ((1756 : ℝ) / 42) * (L : ℝ) ^ (224 : ℕ) ≤
        (m : ℝ) ^ ((1759 : ℝ) / 42) at hr₈
  have hdLower : (m : ℝ) ^ ((31 : ℝ) / 21) <
      (512 * (L : ℝ) ^ (2 : ℕ)) * d := hcore
  have hdPow : (m : ℝ) ^ ((868 : ℝ) / 21) <
      512 ^ (28 : ℕ) * (L : ℝ) ^ (56 : ℕ) * d ^ (28 : ℕ) := by
    have hp := pow_lt_pow_left₀ hdLower
      (Real.rpow_nonneg hmpos.le _) (by omega : (28 : ℕ) ≠ 0)
    have hbase : ((m : ℝ) ^ ((31 : ℝ) / 21)) ^ (28 : ℕ) =
        (m : ℝ) ^ ((868 : ℝ) / 21) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
      norm_num
    rw [hbase] at hp
    calc
      _ < ((512 * (L : ℝ) ^ (2 : ℕ)) * d) ^ (28 : ℕ) := hp
      _ = _ := by rw [mul_pow, mul_pow, ← pow_mul]
  have hN29 : (N : ℝ) ^ (29 : ℕ) ≤
      R ^ (29 : ℕ) * (m : ℝ) ^ ((290 : ℝ) / 21) := by
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ N) hNcapR 29
    have hm290 : ((m : ℝ) ^ ((10 : ℝ) / 21)) ^ (29 : ℕ) =
        (m : ℝ) ^ ((290 : ℝ) / 21) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
      norm_num
    simpa [mul_pow, hm290] using hp
  have hmaster :
      ((224 * 1536 * 512 ^ (26 : ℕ)) *
          (32 ^ (56 : ℕ) * (4 * 2 ^ (28 : ℕ))) : ℝ) *
          m ^ (28 : ℕ) * L ^ (167 : ℕ) * N ^ (29 : ℕ) ≤
        β * q * d ^ (27 : ℕ) := by
    let C₀ : ℝ := (224 * 1536 * 512 ^ (26 : ℕ)) *
      (32 ^ (56 : ℕ) * (4 * 2 ^ (28 : ℕ)))
    have hleft : C₀ * (m : ℝ) ^ (28 : ℕ) * (L : ℝ) ^ (167 : ℕ) *
        (N : ℝ) ^ (29 : ℕ) ≤
      C₀ * R ^ (29 : ℕ) * (m : ℝ) ^ ((878 : ℝ) / 21) *
        (L : ℝ) ^ (167 : ℕ) := by
      calc
        _ ≤ C₀ * (m : ℝ) ^ (28 : ℕ) * (L : ℝ) ^ (167 : ℕ) *
            (R ^ (29 : ℕ) * (m : ℝ) ^ ((290 : ℝ) / 21)) := by gcongr
        _ = _ := by
          have hm878 : (m : ℝ) ^ (28 : ℕ) *
              (m : ℝ) ^ ((290 : ℝ) / 21) =
              (m : ℝ) ^ ((878 : ℝ) / 21) := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hmpos]
            congr 2
            norm_num
          calc
            _ = C₀ * R ^ (29 : ℕ) *
                ((m : ℝ) ^ (28 : ℕ) *
                  (m : ℝ) ^ ((290 : ℝ) / 21)) *
                  (L : ℝ) ^ (167 : ℕ) := by ring
            _ = _ := by rw [hm878]
    have hd13 : (d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21) <
        (512 * (L : ℝ)) * q := by
      have hden : (0 : ℝ) < 512 * L := by positivity
      simpa [mul_comm] using (div_lt_iff₀ hden).mp hq
    have hqd : (m : ℝ) ^ ((881 : ℝ) / 21) <
        512 ^ (29 : ℕ) * (L : ℝ) ^ (57 : ℕ) *
          ((q : ℝ) * d ^ (27 : ℕ)) := by
      calc
        (m : ℝ) ^ ((881 : ℝ) / 21) =
            (m : ℝ) ^ ((868 : ℝ) / 21) *
              (m : ℝ) ^ ((13 : ℝ) / 21) := by
          rw [← Real.rpow_add hmpos]
          congr 2
          norm_num
        _ < (512 ^ (28 : ℕ) * (L : ℝ) ^ (56 : ℕ) * d ^ (28 : ℕ)) *
            (m : ℝ) ^ ((13 : ℝ) / 21) := by gcongr
        _ = (512 ^ (28 : ℕ) * (L : ℝ) ^ (56 : ℕ) * d ^ (27 : ℕ)) *
            (d * (m : ℝ) ^ ((13 : ℝ) / 21)) := by ring
        _ < (512 ^ (28 : ℕ) * (L : ℝ) ^ (56 : ℕ) * d ^ (27 : ℕ)) *
            ((512 * (L : ℝ)) * q) := by gcongr
        _ = 512 ^ (29 : ℕ) * (L : ℝ) ^ (57 : ℕ) *
            ((q : ℝ) * d ^ (27 : ℕ)) := by ring
    have hβ881 : β * (m : ℝ) ^ ((881 : ℝ) / 21) =
        (m : ℝ) ^ ((1759 : ℝ) / 42) := by
      dsimp [β]
      rw [← Real.rpow_add hmpos]
      congr 2
      norm_num
    have hright :
        (m : ℝ) ^ ((1759 : ℝ) / 42) <
          (512 ^ (29 : ℕ) * (L : ℝ) ^ (57 : ℕ)) *
            (β * (q : ℝ) * d ^ (27 : ℕ)) := by
      rw [← hβ881]
      have hβpos : 0 < β := by dsimp [β]; positivity
      calc
        β * (m : ℝ) ^ ((881 : ℝ) / 21) <
            β * (512 ^ (29 : ℕ) * (L : ℝ) ^ (57 : ℕ) *
              ((q : ℝ) * d ^ (27 : ℕ))) :=
          mul_lt_mul_of_pos_left hqd hβpos
        _ = _ := by ac_rfl
    have hdenpos : 0 < 512 ^ (29 : ℕ) * (L : ℝ) ^ (57 : ℕ) := by positivity
    apply (mul_le_mul_iff_right₀ hdenpos).mp
    calc
      (512 ^ (29 : ℕ) * (L : ℝ) ^ (57 : ℕ)) *
          (C₀ * (m : ℝ) ^ (28 : ℕ) * (L : ℝ) ^ (167 : ℕ) *
            (N : ℝ) ^ (29 : ℕ)) ≤
        (512 ^ (29 : ℕ) * (L : ℝ) ^ (57 : ℕ)) *
          (C₀ * R ^ (29 : ℕ) * (m : ℝ) ^ ((878 : ℝ) / 21) *
            (L : ℝ) ^ (167 : ℕ)) := by gcongr
      _ = (C₀ * R ^ (29 : ℕ) * 512 ^ (29 : ℕ)) *
          (m : ℝ) ^ ((1756 : ℝ) / 42) * (L : ℝ) ^ (224 : ℕ) := by
        norm_num [show (878 : ℝ) / 21 = 1756 / 42 by norm_num]
        ring
      _ ≤ (m : ℝ) ^ ((1759 : ℝ) / 42) := by
        simpa [C₀] using hr₈
      _ ≤ (512 ^ (29 : ℕ) * (L : ℝ) ^ (57 : ℕ)) *
          (β * (q : ℝ) * d ^ (27 : ℕ)) := hright.le
  exact ⟨hlift, hsuper, by simpa [β] using hmaster⟩

lemma selectedLiftedCycles_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool)
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (S : FirstSelection G side) (R : S.SecondSelection)
    (Q : ℕ)
    (hcycle : ∀ t : NeighborVertex G S.anchor,
      (Erdos113Cycles.cyclesThroughEdge G 4 s(S.anchor, t.1)).card ≤ Q)
    (hlift : 3136 * 2 ^ 27 ≤ 2 ^ R.index.val)
    (hsuper :
      702464 * (16 *
          (degreeBinCount (W := NeighborVertex G S.anchor) : ℝ)) *
          (2 * Fintype.card (NeighborVertex G S.anchor) : ℝ) ^
            ((1 : ℝ) / 14) ≤
        ((S.auxiliaryGraph R.index).edgeFinset.card : ℝ) /
          (32 *
            (degreeBinCount (W := NeighborVertex G S.anchor) : ℝ) ^ 3 *
            Fintype.card (NeighborVertex G S.anchor))) :
    (Erdos113ManyLifts.liftedCycles
      (S.auxiliaryGraph R.index) G
      (Erdos113SelectedLift.FirstSelection.SecondSelection.liftSystem
        S R hcross)).Nonempty := by
  let F := S.auxiliaryGraph R.index
  let L := Erdos113SelectedLift.FirstSelection.SecondSelection.liftSystem
    S R hcross
  let δ : ℝ := (F.edgeFinset.card : ℝ) /
    (32 * (degreeBinCount (W := NeighborVertex G S.anchor) : ℝ) ^ 3 *
      Fintype.card (NeighborVertex G S.anchor))
  have hFcycles : δ ^ 28 / (2 * (2 : ℝ) ^ 28) ≤
      ((Erdos113Cycles.genuineCycles F 28).card : ℝ) := by
    exact Erdos113Supersaturation28.genuineCycles28_lower_of_edgeDensity
      F R.auxiliary_edge (by simpa [F, δ] using hsuper)
  obtain ⟨x, y, hxy⟩ := R.auxiliary_edge
  have hfpos : 0 < F.edgeFinset.card := by
    apply Finset.card_pos.mpr
    exact ⟨s(x, y), F.mem_edgeFinset.mpr hxy⟩
  have hNpos : 0 < Fintype.card (NeighborVertex G S.anchor) :=
    Fintype.card_pos_iff.mpr ⟨x⟩
  have hfposR : (0 : ℝ) < F.edgeFinset.card := by exact_mod_cast hfpos
  have hNposR : (0 : ℝ) < Fintype.card (NeighborVertex G S.anchor) := by
    exact_mod_cast hNpos
  have hellposNat : 0 <
      degreeBinCount (W := NeighborVertex G S.anchor) := by
    dsimp [degreeBinCount]
    omega
  have hellposR : (0 : ℝ) <
      degreeBinCount (W := NeighborVertex G S.anchor) := by
    exact_mod_cast hellposNat
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact div_pos hfposR (by positivity)
  have hcycleposR :
      0 < ((Erdos113Cycles.genuineCycles F 28).card : ℝ) := by
    exact (by positivity : 0 < δ ^ 28 / (2 * (2 : ℝ) ^ 28)).trans_le
      hFcycles
  have hcyclepos : 0 < (Erdos113Cycles.genuineCycles F 28).card := by
    exact_mod_cast hcycleposR
  have hlower : 3136 * 2 ^ 27 ≤ L.lower := by
    change 3136 * 2 ^ 27 ≤ 2 ^ R.index.val
    exact hlift
  have hcount := Erdos113ManyLifts.liftedCycles_card_lower L hlower
  have hleftpos :
      0 < (Erdos113Cycles.genuineCycles F 28).card * L.lower ^ 28 := by
    exact Nat.mul_pos hcyclepos (by positivity)
  have hrightpos :
      0 < 2 * (Erdos113ManyLifts.liftedCycles F G L).card :=
    hleftpos.trans_le hcount
  have hcardpos :
      0 < (Erdos113ManyLifts.liftedCycles F G L).card := by omega
  have hnonempty := Finset.card_pos.mp hcardpos
  simpa [F, L] using hnonempty

lemma sparseCore_high_branch
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : SparseCore G) :
    letI : Fintype C.W := C.fintypeW
    letI : DecidableEq C.W := C.decEqW
    letI : DecidableRel C.graph.Adj := C.decAdj
    ∀ H : DenseHostCell C.graph,
      HostPowerReady C.order →
      1568 * (C.order : ℝ) ^ (-(1 : ℝ) / 14) <
        cleanSelectorThreshold (Fintype.card (SliceTuple C.W)) →
      ¬ ((((orderedFourCycles H.edges).card + 1 : ℕ) : ℝ) ≤
        (H.edges.card : ℝ) *
          (C.order : ℝ) ^ ((13 : ℝ) / 21) /
            (256 * degreeBinCount (W := C.W))) →
      janzerGraph ⊑ G := by
  letI : Fintype C.W := C.fintypeW
  letI : DecidableEq C.W := C.decEqW
  letI : DecidableRel C.graph.Adj := C.decAdj
  intro H hready hsmall hhigh
  let m := C.order
  let L := degreeBinCount (W := C.W)
  let P := graphOfEdges H.edges
  let q := (Erdos113Cycles.genuineCycles P 4).card
  let d := H.edges.card
  let β := (m : ℝ) ^ (-(1 : ℝ) / 14)
  have hm : 64 ≤ m := by simpa [m, SparseCore.order] using C.order_large
  have hmpos : (0 : ℝ) < m := by positivity
  have hLpos : 0 < L := by dsimp [L, degreeBinCount]; omega
  have hLposR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hdpos : 0 < d := by dsimp [d]; exact H.edges_nonempty.card_pos
  have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
  obtain ⟨hcore, _hd₀lower, _hDcap, _hd₀min⟩ :=
    sparseCore_denseCell_common C H
  change (m : ℝ) ^ ((31 : ℝ) / 21) <
    512 * (L : ℝ) ^ (2 : ℕ) * d at hcore
  have hhigh' :
      (d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21) / (256 * L) <
        (((q + 1 : ℕ) : ℝ)) := by
    apply lt_of_not_ge
    simpa [m, L, P, q, d, orderedFourCycles, Nat.cast_mul] using hhigh
  rcases hready with ⟨hr₁, hr₂, hr₃, hr₄, hr₅, hr₆, hr₇, hr₈⟩
  have hm44 : (m : ℝ) ^ ((44 : ℝ) / 21) <
      512 * (L : ℝ) ^ (2 : ℕ) * d *
        (m : ℝ) ^ ((13 : ℝ) / 21) := by
    calc
      (m : ℝ) ^ ((44 : ℝ) / 21) =
          (m : ℝ) ^ ((31 : ℝ) / 21) *
            (m : ℝ) ^ ((13 : ℝ) / 21) := by
        rw [← Real.rpow_add hmpos]
        congr 2
        norm_num
      _ < _ := by gcongr
  have hr₅' : 131072 * (L : ℝ) ^ (3 : ℕ) ≤
      (m : ℝ) ^ ((44 : ℝ) / 21) := by
    rw [Real.rpow_zero, mul_one] at hr₅
    simpa only [L, degreeBinCount, m, SparseCore.order] using hr₅
  have hthresholdMul :
      (512 * (L : ℝ) ^ (2 : ℕ)) * (256 * L) <
        (512 * (L : ℝ) ^ (2 : ℕ)) *
          ((d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21)) := by
    calc
      _ = 131072 * (L : ℝ) ^ (3 : ℕ) := by ring
      _ ≤ (m : ℝ) ^ ((44 : ℝ) / 21) := hr₅'
      _ < 512 * (L : ℝ) ^ (2 : ℕ) * d *
          (m : ℝ) ^ ((13 : ℝ) / 21) := hm44
      _ = _ := by ring
  have hthresholdNumerator :
      256 * (L : ℝ) < (d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21) :=
    lt_of_mul_lt_mul_left hthresholdMul (by positivity)
  have honeThreshold : (1 : ℝ) <
      (d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21) / (256 * L) := by
    exact (lt_div_iff₀ (by positivity : (0 : ℝ) < 256 * (L : ℝ))).2
      (by simpa using hthresholdNumerator)
  have hqposR : (0 : ℝ) < q := by
    have hqone : (1 : ℝ) < ((q + 1 : ℕ) : ℝ) :=
      honeThreshold.trans hhigh'
    have hqoneNat : 1 < q + 1 := by exact_mod_cast hqone
    exact_mod_cast (show 0 < q by omega)
  have hqpos : 0 < q := by exact_mod_cast hqposR
  have hqplus : ((q + 1 : ℕ) : ℝ) ≤ 2 * q := by
    exact_mod_cast (show q + 1 ≤ 2 * q by omega)
  have hqlower :
      (d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21) / (512 * L) < q := by
    calc
      _ = ((d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21) / (256 * L)) / 2 := by
        field_simp
        ring
      _ < (((q + 1 : ℕ) : ℝ)) / 2 := by gcongr
      _ ≤ q := by linarith
  have hPcycles : (Erdos113Cycles.genuineCycles P 4).Nonempty :=
    Finset.card_pos.mp (by simpa [q] using hqpos)
  obtain ⟨S⟩ := exists_firstSelection P (sideOfColor H.color) hPcycles
  obtain ⟨R⟩ := S.exists_secondSelection
  let N := Fintype.card (NeighborVertex P S.anchor)
  let a := 2 ^ S.scaleIndex.val
  let b := 2 ^ R.index.val
  let f := (S.auxiliaryGraph R.index).edgeFinset.card
  let ell := degreeBinCount (W := NeighborVertex P S.anchor)
  have hcross : ∀ ⦃x y⦄, P.Adj x y →
      sideOfColor H.color y = !sideOfColor H.color x := by
    intro x y hxy
    exact H.cross hxy
  have hNdegree : N = P.degree S.anchor := by
    simp [N, NeighborVertex, SimpleGraph.card_neighborFinset_eq_degree]
  have hNpos : 0 < N := by
    obtain ⟨p, hp⟩ := S.triples_nonempty
    rw [hNdegree]
    exact (P.degree_pos_iff_exists_adj S.anchor).2 ⟨p.left, (S.data hp).1⟩
  have haN : a ≤ N := by
    obtain ⟨p, hp⟩ := S.triples_nonempty
    calc
      a = 2 ^ S.scaleIndex.val := rfl
      _ ≤ Erdos113FourCycles.codegree P S.anchor p.middle :=
        (S.data hp).2.2.2.2.2.2.2.1
      _ ≤ P.degree S.anchor := codegree_le_degree_left P S.anchor p.middle
      _ = N := hNdegree.symm
  have ha : 2 ≤ a := by
    dsimp [a]
    exact Nat.one_lt_two_pow (Nat.ne_of_gt S.scaleIndex_pos)
  have hb : b < 2 * a := by
    simpa [a, b] using
      Erdos113.FirstSelection.SecondSelection.secondScale_lt_twice_firstScale S R
  have hPcore : P ≤ C.graph := graphOfEdges_le H.edges_subset
  have hNcapNat : N ≤ C.graph.maxDegree := by
    rw [hNdegree]
    exact (SimpleGraph.degree_le_of_le hPcore).trans
      (C.graph.degree_le_maxDegree S.anchor)
  have hNcap : (N : ℝ) ≤
      (regularFactor + 1 : ℕ) * (m : ℝ) ^ ((10 : ℝ) / 21) := by
    calc
      (N : ℝ) ≤ C.graph.maxDegree := by exact_mod_cast hNcapNat
      _ ≤ _ := by simpa [m, SparseCore.maximumDegree] using C.maxDegree_upper
  have hNm : N ≤ m := by
    dsimp [N, m, SparseCore.order]
    exact Fintype.card_subtype_le _
  have hellpos : 0 < ell := by dsimp [ell, degreeBinCount]; omega
  have hellL : ell ≤ L := by
    dsimp [ell, L, degreeBinCount]
    exact Nat.add_le_add_right (Nat.log_mono_right hNm) 1
  have hfcap : f ≤ N ^ 2 := by
    simpa only [f, N] using
      Erdos113.FirstSelection.SecondSelection.auxiliary_edge_card_le_square S R
  have hselection : q ≤ 32 * m * L ^ 2 * b * f := by
    simpa only [q, m, L, b, f, SparseCore.order, degreeBinCount] using
      Erdos113.FirstSelection.SecondSelection.selection_count_bound S R
  obtain ⟨hlift, hsuper, hmaster⟩ := high_ready_inputs
    m L ell N a b f q d hm (by rfl) hellpos hellL
      (by simpa [HostPowerReady, m] using
        And.intro hr₁ (And.intro hr₂ (And.intro hr₃ (And.intro hr₄
          (And.intro hr₅ (And.intro hr₆ (And.intro hr₇ hr₈)))))))
      hcore hqlower hNpos haN hb hNcap hfcap hselection
  have hQd : H.dynamicCycleCap * d ≤ 128 * L * q := by
    have hdiv : H.dynamicCycleCap * H.edges.card ≤
        64 * L * ((orderedFourCycles H.edges).card + 1) := by
      dsimp [DenseHostCell.dynamicCycleCap]
      exact Nat.div_mul_le_self _ _
    have hqplusNat : (orderedFourCycles H.edges).card + 1 ≤ 2 * q := by
      simpa [P, q, orderedFourCycles] using
        (show q + 1 ≤ 2 * q by omega)
    calc
      H.dynamicCycleCap * d = H.dynamicCycleCap * H.edges.card := rfl
      _ ≤ 64 * L * ((orderedFourCycles H.edges).card + 1) := hdiv
      _ ≤ 64 * L * (2 * q) := by gcongr
      _ = 128 * L * q := by ring
  have hcycle : ∀ t : NeighborVertex P S.anchor,
      (Erdos113Cycles.cyclesThroughEdge P 4 s(S.anchor, t.1)).card ≤
        H.dynamicCycleCap := by
    intro t
    exact H.cyclesThroughEdge_le_dynamicCycleCap
      ((P.mem_neighborFinset S.anchor t.1).mp t.2)
  have hnumeric := many_branch_numeric_of_master
    m L N a b f q d H.dynamicCycleCap β hLpos hNpos ha hqpos hdpos
      (by dsimp [β]; positivity) hb hQd hselection hmaster
  have hdeltaMono :
      (f : ℝ) / (32 * (L : ℝ) ^ (3 : ℕ) * N) ≤
        (f : ℝ) / (32 * (ell : ℝ) ^ (3 : ℕ) * N) := by
    apply div_le_div_of_nonneg_left (by positivity)
      (by positivity : (0 : ℝ) < 32 * (ell : ℝ) ^ (3 : ℕ) * N)
    gcongr
  have hdeltaNonneg :
      (0 : ℝ) ≤ (f : ℝ) / (32 * (L : ℝ) ^ (3 : ℕ) * N) :=
    div_nonneg (by exact_mod_cast (Nat.zero_le f)) (by positivity)
  have hdeltaPow :
      ((f : ℝ) / (32 * (L : ℝ) ^ (3 : ℕ) * N)) ^ (28 : ℕ) ≤
        ((f : ℝ) / (32 * (ell : ℝ) ^ (3 : ℕ) * N)) ^ (28 : ℕ) :=
    pow_le_pow_left₀ hdeltaNonneg hdeltaMono 28
  have hYmono :
      ((((f : ℝ) / (32 * (L : ℝ) ^ (3 : ℕ) * N)) ^ (28 : ℕ) /
          (2 * (2 : ℝ) ^ (28 : ℕ))) * (b : ℝ) ^ (28 : ℕ) / 2) ≤
        ((((f : ℝ) / (32 * (ell : ℝ) ^ (3 : ℕ) * N)) ^ (28 : ℕ) /
          (2 * (2 : ℝ) ^ (28 : ℕ))) * (b : ℝ) ^ (28 : ℕ) / 2) := by
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (div_le_div_iff_of_pos_right
      (by positivity : (0 : ℝ) < 2 * (2 : ℝ) ^ (28 : ℕ))).2 hdeltaPow
  have hnumericEll :
      (112 * (2 * b + 2 * a) : ℝ) *
          (2 * (((N * (H.dynamicCycleCap / (a - 1)) : ℕ) : ℝ)) *
            (((((2 * a) * (H.dynamicCycleCap / (a - 1)) : ℕ) : ℝ)) ^
              (26 : ℕ))) ≤
        β *
          ((((f : ℝ) /
              (32 * (ell : ℝ) ^ (3 : ℕ) * N)) ^ (28 : ℕ) /
                (2 * (2 : ℝ) ^ (28 : ℕ))) *
              (b : ℝ) ^ (28 : ℕ) / 2) := by
    apply hnumeric.trans
    exact mul_le_mul_of_nonneg_left hYmono (by dsimp [β]; positivity)
  have hgood := manyFourCycleGoodFamily_of_numerics
    P (sideOfColor H.color) hcross S R H.dynamicCycleCap hcycle
      hlift hsuper β (by dsimp [β]; positivity) (by
        dsimp only
        simp only [
          Erdos113SelectedLift.FirstSelection.SecondSelection.anchoredLiftSystem,
          Erdos113AnchorConstruction.selectedAnchoredLiftSystem]
        have hbReal : (2 : ℝ) ^ (R.index.val + 1) = 2 * (b : ℝ) := by
          rw [pow_succ]
          norm_num [b]
          ring
        have haReal : (2 : ℝ) ^ (S.scaleIndex.val + 1) = 2 * (a : ℝ) := by
          rw [pow_succ]
          norm_num [a]
          ring
        have haNatR : (((2 ^ (S.scaleIndex.val + 1) : ℕ) : ℝ)) =
            2 * (a : ℝ) := by
          simp only [pow_succ, Nat.cast_mul, Nat.cast_ofNat, a]
          ring
        rw [hbReal, haReal, haNatR]
        norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hnumericEll ⊢
        simpa only [a, b, N, ell, f] using hnumericEll)
  have hfamily :
      (Erdos113ManyLifts.liftedCycles
        (S.auxiliaryGraph R.index) P
        (Erdos113SelectedLift.FirstSelection.SecondSelection.liftSystem
          S R hcross)).Nonempty :=
    selectedLiftedCycles_nonempty P (sideOfColor H.color) hcross S R
      H.dynamicCycleCap hcycle hlift hsuper
  have hcopyP : janzerGraph ⊑ P :=
    hgood.janzerGraph_isContained (by dsimp [β]; positivity) hfamily (by
      simpa [β, m, P] using hsmall)
  exact (hcopyP.trans (SimpleGraph.IsContained.of_le hPcore)).trans C.contained

theorem SparseCore.janzerGraph_isContained
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : SparseCore G) :
    letI : Fintype C.W := C.fintypeW
    letI : DecidableEq C.W := C.decEqW
    HostPowerReady C.order →
    1568 * (C.order : ℝ) ^ (-(1 : ℝ) / 14) <
      cleanSelectorThreshold (Fintype.card (SliceTuple C.W)) →
    janzerGraph ⊑ G := by
  letI : Fintype C.W := C.fintypeW
  letI : DecidableEq C.W := C.decEqW
  letI : DecidableRel C.graph.Adj := C.decAdj
  intro hready hsmall
  obtain ⟨e, he⟩ := C.edges_nonempty
  obtain ⟨x, y, hxy⟩ : ∃ x y, C.graph.Adj x y := by
    induction e using Sym2.inductionOn with
    | _ x y => exact ⟨x, y, C.graph.mem_edgeFinset.mp he⟩
  obtain ⟨H⟩ := exists_denseHostCell C.graph ⟨x, y, hxy⟩
  by_cases hlow :
      (((orderedFourCycles H.edges).card + 1 : ℕ) : ℝ) ≤
        (H.edges.card : ℝ) *
          (C.order : ℝ) ^ ((13 : ℝ) / 21) /
            (256 * degreeBinCount (W := C.W))
  · obtain ⟨K⟩ :=
      Erdos113HostPruning.DenseHostCell.exists_minDegreeHostCell H
    exact sparseCore_low_branch C H K hready hsmall hlow
  · exact sparseCore_high_branch C H hready hsmall hlow

lemma janzerHostEmbeddingAt_of_core_threshold
    (M n : ℕ)
    (hready : ∀ m, M ≤ m → HostPowerReady m)
    (hsmall : ∀ m, M ≤ m →
      1568 * (m : ℝ) ^ (-(1 : ℝ) / 14) <
        cleanSelectorThreshold (Fintype.card (SliceTuple (Fin m))))
    (hnlarge : max sparseCoreHostThreshold (4 ^ 21 * M ^ 20 + 1) ≤ n) :
    JanzerHostEmbeddingAt n := by
  intro G _inst hdense
  have hhostLarge : sparseCoreHostThreshold ≤ Fintype.card (Fin n) := by
    simp only [Fintype.card_fin]
    exact (Nat.le_max_left _ _).trans hnlarge
  obtain ⟨C⟩ := exists_sparseCore_of_large_host G hhostLarge (by
    simpa using hdense)
  have hnpos : 0 < n := by
    have hthresholdPos : 0 < 4 ^ 21 * M ^ 20 + 1 := by positivity
    exact hthresholdPos.trans_le ((Nat.le_max_right _ _).trans hnlarge)
  have hdensePow : n ^ 31 < G.edgeFinset.card ^ 21 :=
    power_density_of_rpow_density hdense
  have hchain : n ^ 31 < 4 ^ 21 * C.order ^ 20 * n ^ 22 := by
    calc
      n ^ 31 < G.edgeFinset.card ^ 21 := hdensePow
      _ ≤ 4 ^ 21 * C.order ^ 20 * Fintype.card (Fin n) ^ 22 := C.host_growth
      _ = 4 ^ 21 * C.order ^ 20 * n ^ 22 := by simp
  have hcancel : n ^ 9 < 4 ^ 21 * C.order ^ 20 := by
    apply lt_of_mul_lt_mul_right (a := n ^ 22) _ (Nat.zero_le _)
    simpa [← pow_add] using hchain
  have hMcore : M ≤ C.order := by
    by_contra! hm
    have hmPow : C.order ^ 20 ≤ M ^ 20 :=
      pow_le_pow_left' (by omega : C.order ≤ M) 20
    have hcancel' : n ^ 9 < 4 ^ 21 * M ^ 20 :=
      hcancel.trans_le (Nat.mul_le_mul_left _ hmPow)
    have hnlepow : n ≤ n ^ 9 := by
      calc
        n = n ^ 1 := by simp
        _ ≤ n ^ 9 := pow_le_pow_right₀ (by omega : 1 ≤ n) (by omega)
    have hthreshold : 4 ^ 21 * M ^ 20 + 1 ≤ n :=
      (Nat.le_max_right _ _).trans hnlarge
    omega
  letI : Fintype C.W := C.fintypeW
  letI : DecidableEq C.W := C.decEqW
  have hsmallW : 1568 * (C.order : ℝ) ^ (-(1 : ℝ) / 14) <
      cleanSelectorThreshold (Fintype.card (SliceTuple C.W)) := by
    rw [show Fintype.card (SliceTuple C.W) =
        Fintype.card (SliceTuple (Fin C.order)) by
      calc
        Fintype.card (SliceTuple C.W) = C.order ^ 28 := by
          simp [SliceTuple, SparseCore.order]
        _ = Fintype.card (SliceTuple (Fin C.order)) :=
          (card_sliceTuple_fin C.order).symm]
    exact hsmall C.order hMcore
  exact Erdos113.SparseCore.janzerGraph_isContained C
    (hready C.order hMcore) hsmallW

theorem eventually_janzerHostEmbedding :
    ∀ᶠ n : ℕ in atTop, JanzerHostEmbeddingAt n := by
  have hboth := eventually_hostPowerReady.and eventually_cleanSelectorThreshold
  obtain ⟨M, hM⟩ := eventually_atTop.1 hboth
  filter_upwards [eventually_ge_atTop
    (max sparseCoreHostThreshold (4 ^ 21 * M ^ 20 + 1))] with n hn
  exact janzerHostEmbeddingAt_of_core_threshold M n
    (fun m hm ↦ (hM m hm).1) (fun m hm ↦ (hM m hm).2) hn

theorem janzerGraph_hasExtremalBound :
    HasExtremalBound ((31 : ℝ) / 21) janzerGraph :=
  hasExtremalBound_of_eventually_janzerHostEmbedding
    eventually_janzerHostEmbedding

/-- Janzer's counterexample resolves Erdős Problem 113 negatively. -/
theorem erdos_113 :
    ¬ (∀ (V : Type) [Fintype V], ∀ H : SimpleGraph V,
      H.IsBipartite → (HasThreeHalvesExtremalBound H ↔ IsTwoDegenerate H)) :=
  not_erdosSimonovitsConjecture_of_janzer_bound janzerGraph_hasExtremalBound

end

#print axioms erdos_113
-- 'Erdos113.erdos_113' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos113
