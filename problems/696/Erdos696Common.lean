/-
# Shared definitions for Erdős problem 696

Provides the `piMod` prime-counting function in arithmetic progressions.
Factored out so that the standalone Brun–Titchmarsh proof
(`BrunTitchmarshAP.lean`) can reference it without creating an import
cycle with the main `Erdos696.lean` file.
-/
import Mathlib

namespace Erdos696

/-- The prime-counting function in arithmetic progressions:
`piMod t q a = #{p ≤ t : p prime, p ≡ a (mod q)}`. -/
noncomputable def piMod (t : ℝ) (q a : ℕ) : ℕ :=
  Nat.card {p : ℕ | p ≤ ⌊t⌋₊ ∧ p.Prime ∧ p % q = a % q}

end Erdos696
