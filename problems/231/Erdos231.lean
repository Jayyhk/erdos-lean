import Mathlib

set_option linter.mathlibStandardSet false

namespace Erdos231

/-
# Problem Description

Erdős Problem 231. Erdős conjectured that every string of length `2 ^ k` over an alphabet
of `k` symbols must contain an *abelian square*: two consecutive blocks `x` and `y` such
that `y` is a permutation of `x`. `erdos_231` disproves this.

The source is Erdős, *Some unsolved problems*, Magyar Tud. Akad. Mat. Kutató Int. Közl. 6
(1961), 221--254, p. 240, footnote 2. Erdős calls two consecutive blocks "identical" when
"each symbol occurs the same number of times in both of them (i.e. we disregard order)",
which is the `List.Perm` condition used below.

Erdős writes the length as `2 ^ k - 1`, and erdosproblems.com quotes him verbatim, but
that is an off-by-one: the longest abelian-square-free string over `k` symbols has length
exactly `2 ^ k - 1` (for `k = 2` it is `010`, for `k = 3` it is `0102010`), so the `2 ^ k - 1`
form is false for every `k >= 2` and is disproved by a three-letter word. It also
contradicts the sentence Erdős writes immediately after, "This is true for `k <= 3`, but
for `k = 4` de Bruijn and I disproved it", which holds precisely for the `2 ^ k` form.
erdosproblems.com records the same correction: "Perhaps Erdős meant `2 ^ k`, where indeed
there is an example for `k = 4`: 1213121412132124." This file therefore states the `2 ^ k`
form, as the repository has since the entry was added.

The disproof is a single explicit witness: the length-16 word `1213121412132124`, i.e.
`[0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 1, 0, 1, 3]` over `Fin 4`, contains no abelian
square, and `16 = 2 ^ 4`. The search over its factors is discharged by kernel `decide`,
via the hand-proved bridging lemmas `isAbelianSquare_iff` and `containsAbelianSquare_iff`
relating the `Bool`-valued decision procedures to their `Prop` counterparts. This replaces
the repository's previous proof, which obtained arbitrarily long witnesses from Keränen's
85-uniform morphism and needed `native_decide`; `erdos_231` now depends on Lean's standard
foundations alone.

The decision procedures, their correctness lemmas, and the witness are vendored from plby
(github.com/plby/lean-proofs), `src/latest/ErdosProblems/Erdos231.lean` and
`src/latest/ErdosProblems/Erdos231/Proof.lean`, concatenated with the project-internal
import removed so that `Mathlib` is the only import. Two changes: the witness is the full
sixteen-symbol string rather than its fifteen-symbol prefix, and `erdos_231` is stated in
the half-length `Perm` form the repository already used, bridged by
`isAbelianSquare_of_perm`. Those upstream files are in turn taken from AxiomProver / Axiom
Math, github.com/AxiomMath/erdos-public, `Erdos/Erdos231/solution.lean`, under the MIT
licence reproduced here:

  MIT License

  Copyright (c) 2026 Axiom Math.

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
-/

def IsAbelianSquare {α : Type*} (w : List α) : Prop :=
  ∃ u v : List α, u ≠ [] ∧ v ≠ [] ∧ u.length = v.length ∧ u.Perm v ∧ w = u ++ v

def isAbelianSquare {α : Type*} [DecidableEq α] (w : List α) : Bool :=
  w.length % 2 == 0 ∧ w.length / 2 ≥ 1 ∧ (w.take (w.length / 2)).Perm (w.drop (w.length / 2))

def ContainsAbelianSquare {α : Type*} (w : List α) : Prop :=
  ∃ i len : ℕ, 2 ≤ len ∧ i + len ≤ w.length ∧
    IsAbelianSquare ((w.drop i).take len)

def containsAbelianSquare {α : Type*} [DecidableEq α] (w : List α) : Bool :=
  (List.range w.length).any fun i =>
    (List.range ((w.length - i) / 2)).any fun m =>
      isAbelianSquare ((w.drop i).take (2 * (m + 1)))

def IsAbelianSquareFree {α : Type*} (w : List α) : Prop :=
  ¬ContainsAbelianSquare w

/-- `isAbelianSquare` correctly decides `IsAbelianSquare`. -/
theorem isAbelianSquare_iff {α : Type*} [DecidableEq α] (w : List α) :
    isAbelianSquare w = true ↔ IsAbelianSquare w := by
  refine ⟨fun h => ?_, fun ⟨u, v, hu, _, hlen, hperm, hw⟩ => ?_⟩
  · simp only [isAbelianSquare, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨hmod, hge, hperm⟩ := h
    refine ⟨w.take (w.length / 2), w.drop (w.length / 2), ?_, ?_, ?_, hperm,
      (List.take_append_drop (w.length / 2) w).symm⟩
    · simp [← List.length_eq_zero_iff, List.length_take]
      omega
    · simp [← List.length_eq_zero_iff, List.length_drop]
      omega
    · simp [List.length_take, List.length_drop]
      omega
  · subst hw
    have h_len : (u ++ v).length = 2 * u.length := by
      rw [List.length_append, ← hlen, two_mul]
    have h_pos : 1 ≤ u.length := List.length_pos_iff.mpr hu
    simp [isAbelianSquare, h_len, h_pos, hperm]

/-- `containsAbelianSquare` correctly decides `ContainsAbelianSquare`. -/
theorem containsAbelianSquare_iff {α : Type*} [DecidableEq α] (w : List α) :
    containsAbelianSquare w = true ↔ ContainsAbelianSquare w := by
  unfold containsAbelianSquare
  simp only [List.any_eq_true, List.mem_range]
  refine ⟨fun ⟨i, hi, m, hm, hsq⟩ => ⟨i, 2 * (m + 1), by omega, by omega,
    (isAbelianSquare_iff _).mp hsq⟩, fun ⟨i, len, hlen, hbound, hsq⟩ => ?_⟩
  have hbool : isAbelianSquare ((w.drop i).take len) = true := (isAbelianSquare_iff _).mpr hsq
  have hlen_eq : ((w.drop i).take len).length = len := by
    rw [List.length_take, List.length_drop]
    omega
  have heven : len % 2 = 0 := by
    simp only [isAbelianSquare, beq_iff_eq, decide_eq_true_eq, hlen_eq] at hbool
    exact hbool.1
  refine ⟨i, by omega, len / 2 - 1, by omega, ?_⟩
  rw [show 2 * (len / 2 - 1 + 1) = len by omega]
  exact hbool

/-- **Explicit witness for `k = 4`.** The word
`[0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 1, 0, 1, 3]` over `Fin 4` — the string
`1213121412132124` recorded on erdosproblems.com — has length `2 ^ 4 = 16` and contains
no abelian square. -/
theorem erdos_problem_231_k4 :
    let S : List (Fin 4) := [0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 1, 0, 1, 3]
    S.length = 2 ^ 4 ∧ IsAbelianSquareFree S :=
  ⟨rfl, fun hcontra => absurd ((containsAbelianSquare_iff _).mpr hcontra) (by decide)⟩

/-- **Erdős Problem 231 (Disproof).** -/
theorem erdos_problem_231_disproof :
    ∃ k : ℕ, 0 < k ∧ ∃ S : List (Fin k),
      S.length = 2 ^ k ∧ IsAbelianSquareFree S :=
  ⟨4, by norm_num, _, erdos_problem_231_k4.1, erdos_problem_231_k4.2⟩

/-- Two adjacent equal-length blocks that are permutations of each other form an
`IsAbelianSquare` factor of twice that length. This converts the half-length `Perm`
phrasing of the conjecture into the `u ++ v` phrasing the decision procedure uses. -/
theorem isAbelianSquare_of_perm {α : Type*} (w : List α) (i l : ℕ) (hl : 0 < l)
    (hb : i + 2 * l ≤ w.length)
    (hperm : ((w.drop i).take l).Perm ((w.drop (i + l)).take l)) :
    IsAbelianSquare ((w.drop i).take (2 * l)) := by
  have hlen1 : ((w.drop i).take l).length = l := by
    rw [List.length_take, List.length_drop]; omega
  have hlen2 : ((w.drop (i + l)).take l).length = l := by
    rw [List.length_take, List.length_drop]; omega
  refine ⟨(w.drop i).take l, (w.drop (i + l)).take l, ?_, ?_, by rw [hlen1, hlen2],
    hperm, ?_⟩
  · intro hc; rw [hc] at hlen1; simp at hlen1; omega
  · intro hc; rw [hc] at hlen2; simp at hlen2; omega
  · rw [two_mul, List.take_add, List.drop_drop]

/-- **Erdős Problem 231.** Erdős conjectured that every string of length `2 ^ k` over an
alphabet of `k` symbols contains an abelian square. This is false: `k = 4` is a
counterexample. -/
theorem erdos_231 :
    ¬ ∀ k, 2 ≤ k →
        ∀ w : List (Fin k), w.length = 2 ^ k →
          ∃ i l, 0 < l ∧ i + 2 * l ≤ w.length ∧
            (w.drop i |>.take l).Perm (w.drop (i + l) |>.take l) := by
  intro h
  obtain ⟨i, l, hlpos, hbound, hperm⟩ := h 4 (by norm_num) _ erdos_problem_231_k4.1
  exact erdos_problem_231_k4.2
    ⟨i, 2 * l, by omega, by omega, isAbelianSquare_of_perm _ i l hlpos hbound hperm⟩

#print axioms erdos_231
-- 'Erdos231.erdos_231' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos231
