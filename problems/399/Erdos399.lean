import Mathlib

namespace Erdos399

open Nat

/-- **Erdős Problem 399** (disproof). "Is it true that there are no solutions to
`n! = xᵏ ± yᵏ` with `x, y, n ∈ ℕ`, `xy > 1` and `k > 2`?" — No: Jonas Barfield's
counterexample `10! = 48⁴ − 36⁴` (equivalently `10! + 36⁴ = 48⁴`). -/
theorem erdos_399 :
    ∃ (n x y k : ℕ), 1 < x * y ∧ 2 < k ∧ (n ! = x ^ k + y ^ k ∨ n ! + y ^ k = x ^ k) :=
  ⟨10, 48, 36, 4, by decide⟩

#print axioms erdos_399
-- 'Erdos399.erdos_399' depends on axioms: [propext]

end Erdos399
