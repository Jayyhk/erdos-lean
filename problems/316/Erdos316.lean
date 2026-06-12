/-
Erdős Problem 316 — https://www.erdosproblems.com/316

Disproof (Sándor [Sa97]; the minimal counterexample {2,3,4,5,6,7,10,11,13,14,15} was
found by Tom Stobart). Formalized in Lean by Mehta as part of the Google DeepMind
Formal Conjectures project. Adapted here: `import Mathlib`, the `formal-conjectures`
`answer(False) ↔ …` sentinel rewritten as `¬ …`, and wrapped in `namespace Erdos316`.
-/
import Mathlib

namespace Erdos316

set_option maxHeartbeats 1000000

/-- **Erdős Problem 316.** Main statement (proven via the counterexample
`{2,3,4,5,6,7,10,11,13,14,15}` due to Sándor; minimal version by Tom Stobart). -/
theorem erdos_316_main : ¬ ∀ A : Finset ℕ, 0 ∉ A → 1 ∉ A →
    ∑ n ∈ A, (1 / n : ℚ) < 2 → ∃ (A₁ A₂ : Finset ℕ),
      Disjoint A₁ A₂ ∧ A = A₁ ∪ A₂ ∧
      ∑ n ∈ A₁, (1 / n : ℚ) < 1 ∧ ∑ n ∈ A₂, (1 / n : ℚ) < 1 := by
  simp only [one_div, not_forall, not_exists, not_and, not_lt]
  let A : Finset ℕ := {2, 3, 4, 5, 6, 7, 10, 11, 13, 14, 15}
  refine ⟨A, by decide, by decide, by decide +kernel, ?_⟩
  suffices h : ∀ B ⊆ A, ∑ n ∈ B, (n : ℚ)⁻¹ < 1 → 1 ≤ ∑ n ∈ A \ B, (n : ℚ)⁻¹ by
    rintro B C hBC hA hlt
    have : C = A \ B := by rw [hA, Finset.union_sdiff_cancel_left hBC]
    exact this ▸ h B (by simp [hA]) hlt
  decide +kernel

/-- The statement fails for *multisets*: e.g. `2,3,3,5,5,5,5`. -/
lemma erdos_316_multiset : ∃ A : Multiset ℕ, 0 ∉ A ∧ 1 ∉ A ∧
    (A.map ((1 : ℚ) / ·)).sum < 2 ∧ ∀ (A₁ A₂ : Multiset ℕ),
      A = A₁ + A₂ →
        1 ≤ (A₁.map ((1 : ℚ) / ·)).sum ∨ 1 ≤ (A₂.map ((1 : ℚ) / ·)).sum := by
  let A : Multiset ℕ := {2, 3, 3, 5, 5, 5, 5}
  refine ⟨A, by decide, by decide, by decide +kernel, ?_⟩
  suffices h : ∀ B ∈ A.powerset, 1 ≤ (B.map (fun x ↦ (x : ℚ)⁻¹)).sum ∨
      1 ≤ ((A - B).map (fun x ↦ (x : ℚ)⁻¹)).sum by
    intro B C hBC
    have : C = A - B := by simp [hBC]
    simp only [Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, Multiset.map_map,
      Function.comp_apply, one_div] at h ⊢
    exact this ▸ h B (by simp [hBC])
  decide +kernel

/-- **Erdős Problem 316**: every finite `A ⊆ ℕ \ {1}` with `∑ 1/n < 2` admits
a partition into two parts each with sum `< 1`. *False* (counterexample above). -/
theorem erdos_316 : ¬ ∀ A : Finset ℕ, 0 ∉ A → 1 ∉ A →
    ∑ n ∈ A, (1 / n : ℚ) < 2 → ∃ (A₁ A₂ : Finset ℕ),
      Disjoint A₁ A₂ ∧ A = A₁ ∪ A₂ ∧
      ∑ n ∈ A₁, (1 / n : ℚ) < 1 ∧ ∑ n ∈ A₂, (1 / n : ℚ) < 1 := erdos_316_main

#print axioms erdos_316
-- 'Erdos316.erdos_316' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos316
