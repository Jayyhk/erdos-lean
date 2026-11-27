import Mathlib

namespace Erdos482

/-
# Erdős Problem 482

Define a sequence by $a_1=1$ and
$$a_{n+1}=\lfloor\sqrt{2}(a_n+1/2)\rfloor$$
for $n\geq 1$. The difference $a_{2n+1}-2a_{2n-1}$ is the $n$th digit in the binary expansion
of $\sqrt{2}$. Find similar results for $\theta=\sqrt{m}$, and other algebraic numbers.

The result for $\sqrt{2}$ is due to Graham and Pollak [GrPo70] (`erdos_482_verbatim`, in the
site's 1-indexing, counting the leading $1$ of $\sqrt{2} = 1.0110101\ldots_2$ as the first
digit). The open-ended part is answered by Stoll's generalisation [St05]
(`General.erdos482_resolution`): for every real $w > 0$ and every base $g \geq 2$ there is an
explicit recurrence of the same shape whose differences
$u_{2n} - g\,u_{2n-2}$ are the base-$g$ digits of $w$. `erdos_482` states both.

Formalised by Trevor Morris in `gotrevor/lean-gallery`; the 47 modules forming the closure of
`erdos_482_verbatim` and `erdos482_resolution` are flattened here in dependency order, with the
upstream `LeanGallery.NumberTheory.Erdos482` namespace merged into this file's `Erdos482`.
Stoll's further results [St06], formalised upstream in further modules, are not part of this
closure. `erdos_482` is added here: it combines `erdos_482_verbatim` and
`General.erdos482_resolution`, and adds no mathematical content.

Declarations that `erdos_482` does not depend on have been removed.
-/

/-! ### Upstream module `Basic.lean` -/

/-!
# Erdős #482 — Graham–Pollak: the recurrence extracts the binary digits of √2

`u 0 = 1`,  `u (n+1) = ⌊√2 · (u n + 1/2)⌋`.  Then `u (2n+1) − 2·u (2n−1)` is the n-th binary
digit of √2.  Source: Stoll, *A fancy way to obtain the binary digits of 759250125√2*,
arXiv:0902.4168 (free); orig. Graham–Pollak, Math. Mag. 43 (1970) 143–145.
-/

/-- The Graham–Pollak sequence.  (`noncomputable`: `Real.sqrt` is.) -/
noncomputable def u : ℕ → ℕ
  | 0     => 1
  | n + 1 => ⌊Real.sqrt 2 * ((u n : ℝ) + 1 / 2)⌋₊

/-! ### Upstream module `Crux.lean` -/

/-- The crux universal inequality (Stoll eq (7), generalized): for every real `x`,
`0 ≤ {x} − √2·{x/2} + √2/2 < 1`.  Proof: case-split on parity of `⌊x⌋` (so `{x} = 2{x/2}` or
`2{x/2} − 1`), then `nlinarith` with `√2² = 2`, `1 ≤ √2 ≤ 3/2`.  No mathlib lemma supplies this. -/
theorem crux (x : ℝ) :
    0 ≤ Int.fract x - Real.sqrt 2 * Int.fract (x / 2) + Real.sqrt 2 / 2 ∧
        Int.fract x - Real.sqrt 2 * Int.fract (x / 2) + Real.sqrt 2 / 2 < 1 := by
  -- √2 facts
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have hs32 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [hs2, sq_nonneg (Real.sqrt 2 - 2)]
  set s := Real.sqrt 2 with hsdef
  -- fract facts
  set f := Int.fract x with hf
  set g := Int.fract (x / 2) with hg
  have hf0 : 0 ≤ f := Int.fract_nonneg x
  have hf1 : f < 1 := Int.fract_lt_one x
  have hg0 : 0 ≤ g := Int.fract_nonneg (x / 2)
  have hg1 : g < 1 := Int.fract_lt_one (x / 2)
  -- parity integer m := ⌊x⌋ - 2⌊x/2⌋, with f = 2g - m
  set m : ℤ := ⌊x⌋ - 2 * ⌊x / 2⌋ with hm
  have key : f = 2 * g - (m : ℝ) := by
    rw [hf, hg, hm]
    push_cast
    rw [← Int.self_sub_floor x, ← Int.self_sub_floor (x / 2)]
    ring
  -- m ∈ {0,1}
  have hmval : (m : ℝ) = 2 * g - f := by linarith [key]
  have hub : (m : ℝ) < 2 := by rw [hmval]; linarith
  have hlb : (-1 : ℝ) < (m : ℝ) := by rw [hmval]; linarith
  have hm01 : m = 0 ∨ m = 1 := by
    have a1 : m < 2 := by exact_mod_cast hub
    have a2 : (-1 : ℤ) < m := by exact_mod_cast hlb
    omega
  rcases hm01 with h | h
  · -- m = 0 : f = 2g, so g < 1/2
    rw [h] at key
    push_cast at key
    have key' : f = 2 * g := by linarith [key]
    refine ⟨?_, ?_⟩
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 - s) hg0, hs1, hs32]
    · nlinarith [mul_pos (by linarith : (0:ℝ) < 2 - s) (by linarith : (0:ℝ) < 1 / 2 - g), hs1, hs32]
  · -- m = 1 : f = 2g - 1, so g ≥ 1/2
    rw [h] at key
    push_cast at key
    have key' : f = 2 * g - 1 := by linarith [key]
    refine ⟨?_, ?_⟩
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 - s) (by linarith : (0:ℝ) ≤ g - 1 / 2), hs1, hs32]
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 - s) (by linarith : (0:ℝ) ≤ g - 1 / 2), hs1, hs32]

/-! # `Erdos482` (umbrella import) -/

/-! ### Upstream module `Induction.lean` -/

/-! ## The two Graham–Pollak floor identities, corrected to faithful index form

Stoll §4 specialized to GP (verified numerically against the sequence):
* (6')  `u (2j+1) = ⌊√2·2^j⌋ + 2^j`
* (5')  `u (2j+2) = ⌊√2·2^j⌋ + 2^(j+1)`

The even→odd step is exactly `crux`; the odd→even step is the eq-(8) interval check below.
-/

/-- Stoll eq (8) interval check (GP, ε = 1/2): for `w ∈ [0,1)`,
`0 ≤ w·(1−√2) + √2/2 < 1`.  Used by the odd→even induction step. -/
private lemma eq8 {w : ℝ} (h0 : 0 ≤ w) (h1 : w < 1) :
    0 ≤ w * (1 - Real.sqrt 2) + Real.sqrt 2 / 2 ∧
      w * (1 - Real.sqrt 2) + Real.sqrt 2 / 2 < 1 := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have hs32 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [hs2, sq_nonneg (Real.sqrt 2 - 2)]
  refine ⟨?_, ?_⟩
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - w) (by linarith : (0:ℝ) ≤ Real.sqrt 2 - 1)]
  · nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ Real.sqrt 2 - 1)]

/-- even→odd floor step: from `u(2j+2) = ⌊√2·2^j⌋ + 2^(j+1)` derive `u(2j+3) = ⌊√2·2^(j+1)⌋ + 2^(j+1)`.
Reduces to `crux (√2·2^(j+1))`. -/
private lemma floorB (j : ℕ) :
    ⌊Real.sqrt 2 * (((⌊Real.sqrt 2 * 2 ^ j⌋ + 2 ^ (j + 1) : ℤ) : ℝ) + 1 / 2)⌋
      = ⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 1) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  obtain ⟨cl, cu⟩ := crux (Real.sqrt 2 * 2 ^ (j + 1))
  have hhalf : Real.sqrt 2 * 2 ^ (j + 1) / 2 = Real.sqrt 2 * 2 ^ j := by ring
  rw [hhalf] at cl cu
  have key : Real.sqrt 2 * (((⌊Real.sqrt 2 * 2 ^ j⌋ + 2 ^ (j + 1) : ℤ) : ℝ) + 1 / 2)
      = ((⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 1) : ℤ) : ℝ)
        + (Int.fract (Real.sqrt 2 * 2 ^ (j + 1))
            - Real.sqrt 2 * Int.fract (Real.sqrt 2 * 2 ^ j) + Real.sqrt 2 / 2) := by
    rw [← Int.self_sub_floor (Real.sqrt 2 * 2 ^ (j + 1)), ← Int.self_sub_floor (Real.sqrt 2 * 2 ^ j)]
    push_cast
    linear_combination (2:ℝ) ^ j * hs2
  rw [key, Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr ⟨cl, cu⟩, add_zero]

/-- odd→even floor step: from `u(2j+3) = ⌊√2·2^(j+1)⌋ + 2^(j+1)` derive
`u(2j+4) = ⌊√2·2^(j+1)⌋ + 2^(j+2)`.  Reduces to `eq8`. -/
private lemma floorA (j : ℕ) :
    ⌊Real.sqrt 2 * (((⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 1) : ℤ) : ℝ) + 1 / 2)⌋
      = ⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 2) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  obtain ⟨el, eu⟩ := eq8 (Int.fract_nonneg (Real.sqrt 2 * 2 ^ (j + 1)))
    (Int.fract_lt_one (Real.sqrt 2 * 2 ^ (j + 1)))
  have key : Real.sqrt 2 * (((⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 1) : ℤ) : ℝ) + 1 / 2)
      = ((⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 2) : ℤ) : ℝ)
        + (Int.fract (Real.sqrt 2 * 2 ^ (j + 1)) * (1 - Real.sqrt 2) + Real.sqrt 2 / 2) := by
    rw [← Int.self_sub_floor (Real.sqrt 2 * 2 ^ (j + 1))]
    push_cast
    linear_combination (2:ℝ) ^ (j + 1) * hs2
  rw [key, Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr ⟨el, eu⟩, add_zero]

/-- The recurrence over ℤ (the argument is nonnegative, so `Nat.floor = Int.floor`). -/
private lemma urec (n : ℕ) :
    (u (n + 1) : ℤ) = ⌊Real.sqrt 2 * ((u n : ℝ) + 1 / 2)⌋ := by
  have h : u (n + 1) = ⌊Real.sqrt 2 * ((u n : ℝ) + 1 / 2)⌋₊ := rfl
  rw [h, Int.natCast_floor_eq_floor (by positivity)]

/-- The joint Graham–Pollak identities, proved by induction on `j`. -/
theorem gp_pair (j : ℕ) :
    (u (2 * j + 1) : ℤ) = ⌊Real.sqrt 2 * 2 ^ j⌋ + 2 ^ j ∧
      (u (2 * j + 2) : ℤ) = ⌊Real.sqrt 2 * 2 ^ j⌋ + 2 ^ (j + 1) := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have hs32 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [hs2, sq_nonneg (Real.sqrt 2 - 2)]
  have hlo : (4:ℝ) / 3 ≤ Real.sqrt 2 := by nlinarith [hs2, hsnn]
  induction j with
  | zero =>
    have hfloors : ⌊Real.sqrt 2⌋ = 1 := by
      rw [Int.floor_eq_iff]; constructor <;> [exact_mod_cast hs1; · push_cast; linarith]
    have hu1 : (u 1 : ℤ) = 2 := by
      rw [urec 0]
      have : u 0 = 1 := rfl
      rw [this]
      push_cast
      rw [Int.floor_eq_iff]; constructor <;> [(push_cast; nlinarith); (push_cast; nlinarith)]
    have hu2 : (u 2 : ℤ) = 3 := by
      have e : (2:ℕ) = 1 + 1 := rfl
      rw [e, urec 1]
      rw [show ((u 1 : ℝ)) = ((u 1 : ℤ) : ℝ) by push_cast; ring, hu1]
      push_cast
      rw [Int.floor_eq_iff]; constructor <;> [(push_cast; nlinarith); (push_cast; nlinarith)]
    refine ⟨?_, ?_⟩
    · simpa [hfloors] using hu1
    · simpa [hfloors] using hu2
  | succ j IH =>
    have h2r : ((u (2 * j + 2) : ℕ) : ℝ)
        = ((⌊Real.sqrt 2 * 2 ^ j⌋ + 2 ^ (j + 1) : ℤ) : ℝ) := by exact_mod_cast IH.2
    have step1 : (u (2 * j + 2 + 1) : ℤ) = ⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 1) := by
      rw [urec (2 * j + 2), h2r]; exact floorB j
    have h3r : ((u (2 * j + 2 + 1) : ℕ) : ℝ)
        = ((⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 1) : ℤ) : ℝ) := by exact_mod_cast step1
    have step2 : (u (2 * j + 2 + 1 + 1) : ℤ) = ⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 2) := by
      rw [urec (2 * j + 2 + 1), h3r]; exact floorA j
    refine ⟨?_, ?_⟩
    · show (u (2 * (j + 1) + 1) : ℤ) = ⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 1)
      have : 2 * (j + 1) + 1 = 2 * j + 2 + 1 := by ring
      rw [this]; exact step1
    · show (u (2 * (j + 1) + 2) : ℤ) = ⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 1 + 1)
      have : 2 * (j + 1) + 2 = 2 * j + 2 + 1 + 1 := by ring
      rw [this]; exact step2

/-! ## Basic structural properties of the sequence -/

/-! ### Upstream module `Digits.lean` -/

/-! ## Bridge to mathlib's canonical `Real.digits`

`Real.digits y b i = Fin.ofNat _ ⌊y · b^(i+1)⌋₊` (the base-`b` digits of `y ∈ [0,1)`).
For `x` with `1 ≤ x < 2` (so `Int.fract x = x − 1`), the `i`-th base-2 digit of `Int.fract x`
equals Stoll's floor-difference digit `⌊x·2^(i+1)⌋ − 2·⌊x·2^i⌋`.  This certifies that our
`binDigit` is the standard binary-digit notion. -/

/-! ### Upstream module `Main.lean` -/

/-! # `Erdos482` (umbrella import) -/

/-! ### Upstream module `Verbatim.lean` -/

/-!
# Erdős #482 in the website's own indexing

erdosproblems.com/482 states the problem with a 1-indexed sequence: $a_1 = 1$,
$a_{n+1} = \lfloor \sqrt{2}(a_n + 1/2) \rfloor$, and claims that $a_{2n+1} - 2a_{2n-1}$ is the
$n$-th digit of the binary expansion $\sqrt{2} = 1.0110101\ldots_2$, counting the leading `1` as
the first digit.

The development elsewhere uses the 0-indexed `u` with `u k = a (k+1)`, and its headline
`graham_pollak` is about the *even*-indexed terms `a (2n+2) − 2 a (2n)`, which give the digits after
the binary point.  This file proves the literal odd-index statement from the closed form `gp_pair`.
-/

/-- The Graham–Pollak sequence in the website's 1-indexing: `a 1 = 1`,
`a (n+1) = ⌊√2·(a n + 1/2)⌋` for `n ≥ 1`.  The value `a 0` is unused. -/
noncomputable def a : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => ⌊Real.sqrt 2 * ((a (n + 1) : ℝ) + 1 / 2)⌋₊

theorem a_succ (n : ℕ) : a (n + 1) = u n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [a, ih, u]

/-- `⌊2z⌋ − 2⌊z⌋` is the parity of `⌊2z⌋` for `z ≥ 0`. -/
theorem floor_two_mul_sub_eq_mod (z : ℝ) (hz : 0 ≤ z) :
    ⌊2 * z⌋ - 2 * ⌊z⌋ = ((⌊2 * z⌋₊ % 2 : ℕ) : ℤ) := by
  have h2z : (0 : ℝ) ≤ 2 * z := by linarith
  have hdiv : ⌊z⌋₊ = ⌊2 * z⌋₊ / 2 := by
    have := Nat.floor_div_natCast (2 * z) 2
    push_cast at this
    rw [← this]
    congr 1
    ring
  rw [← Int.natCast_floor_eq_floor hz, ← Int.natCast_floor_eq_floor h2z, hdiv]
  omega

/-- **Erdős #482, verbatim.**  For every `n ≥ 1`, `a (2n+1) − 2·a (2n−1)` is the `n`-th binary digit
of `√2 = 1.0110101…₂`, i.e. `⌊√2 · 2^(n−1)⌋ mod 2`. -/
theorem erdos_482_verbatim (n : ℕ) (hn : 1 ≤ n) :
    (a (2 * n + 1) : ℤ) - 2 * (a (2 * n - 1) : ℤ)
      = ((⌊Real.sqrt 2 * 2 ^ (n - 1)⌋₊ % 2 : ℕ) : ℤ) := by
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 : 2 * (m + 1) + 1 = (2 * m + 2) + 1 := by ring
  rw [e1, a_succ, show 2 * (m + 1) - 1 = 2 * m + 1 by omega, a_succ, Nat.add_sub_cancel]
  cases m with
  | zero =>
    have h2 := (gp_pair 0).2
    have hfl : ⌊Real.sqrt 2⌋ = 1 := by
      rw [Int.floor_eq_iff]
      constructor
      · push_cast
        exact Real.one_le_sqrt.mpr (by norm_num)
      · push_cast
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
    have hfln : ⌊Real.sqrt 2⌋₊ = 1 := by
      have := Int.natCast_floor_eq_floor hs0
      omega
    simp only [pow_zero, mul_one, zero_add] at h2 ⊢
    rw [hfln, hfl] at *
    simp [u] at h2 ⊢
    omega
  | succ k =>
    have hA := (gp_pair (k + 1)).2
    have hB := (gp_pair k).2
    have hz : (0 : ℝ) ≤ Real.sqrt 2 * 2 ^ k := by positivity
    have key := floor_two_mul_sub_eq_mod (Real.sqrt 2 * 2 ^ k) hz
    have e2 : 2 * (Real.sqrt 2 * 2 ^ k) = Real.sqrt 2 * 2 ^ (k + 1) := by ring
    rw [e2] at key
    rw [← key, hA, show 2 * (k + 1) = 2 * k + 2 by ring, hB]
    ring

/-! ### Upstream module `General/Digits.lean` -/

/-!
# General base-`g` digit extraction (Stoll [St05], Proposition 2)

The `0902.4168` work in `Erdos482.Stoll` is the base-2, `α√2` special case.  Stoll's J. Integer Seq.
**8** (2005) paper [St05] resolves Erdős–Graham #482 in full: for *any* real `w > 0` and *any* integer
base `g ≥ 2`, an explicit floor-recurrence reads off the base-`g` digits of `w`.  This module begins
that track with the foundational digit-extraction formula and its range bound.

`gdigit g t n := ⌊t·gⁿ⌋ − g·⌊t·gⁿ⁻¹⌋` is the `n`-th base-`g` digit of (the mantissa) `t`.  The key
fact — used at *every* induction step of St05's closed-form proofs — is the range bound
`0 ≤ gdigit g t n < g`, which is just `0 ≤ ⌊g·x⌋ − g·⌊x⌋ < g` at `x = t·gⁿ⁻¹`.

Numerically verified (`tools/sandbox/st05_thm13_verify.py`): the closed forms + this digit identity
hold for `w ∈ {√2, √3, π}`, `g ∈ {2,3,10}`, at the ε-interval endpoints, over many `n`.
-/

namespace General

/-- The base-`g` digit operator on a real `x` at the integer scale: `⌊g·x⌋ − g·⌊x⌋`.  For `x ≥ 0`
this is the leading base-`g` digit of `g·x`'s fractional carry. -/
noncomputable def digitStep (g : ℕ) (x : ℝ) : ℤ := ⌊(g : ℝ) * x⌋ - g * ⌊x⌋

/-- **The digit-step range bound.**  For `g ≥ 1` and any real `x`, `0 ≤ ⌊g·x⌋ − g·⌊x⌋ < g`.
(Writing `x = ⌊x⌋ + {x}`, the step equals `⌊g·{x}⌋ ∈ {0,…,g−1}`.)  This is the single inequality
behind every St05 induction step. -/
theorem digitStep_mem (g : ℕ) (hg : 1 ≤ g) (x : ℝ) :
    0 ≤ digitStep g x ∧ digitStep g x < (g : ℤ) := by
  have hgr : (0 : ℝ) ≤ (g : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · -- g·⌊x⌋ ≤ ⌊g·x⌋  ⟺  ↑(g·⌊x⌋) ≤ g·x
    rw [digitStep, sub_nonneg, Int.le_floor]
    push_cast
    exact mul_le_mul_of_nonneg_left (Int.floor_le x) hgr
  · -- ⌊g·x⌋ < g·⌊x⌋ + g  ⟺  g·x < ↑(g·⌊x⌋ + g)
    rw [digitStep, sub_lt_iff_lt_add, Int.floor_lt]
    push_cast
    have : (g : ℝ) * x < (g : ℝ) * ((⌊x⌋ : ℝ) + 1) :=
      mul_lt_mul_of_pos_left (Int.lt_floor_add_one x) (by exact_mod_cast hg)
    linarith

/-- **Proposition 2 (St05) — mathlib bridge, general base.**  For `y ≥ 0` and base `g` (`NeZero g`),
mathlib's `i`-th base-`g` digit of `y` is exactly the floor difference `⌊y·g^{i+1}⌋ − g·⌊y·g^i⌋ =
digitStep g (y·g^i)`.  Generalizes the repo's base-2 `Erdos482.digits_eq_floor_sub` to any base —
the bridge that identifies St05's recurrence output with the actual base-`g` digits of `w`. -/
theorem realDigits_eq_digitStep (g : ℕ) [NeZero g] (y : ℝ) (hy0 : 0 ≤ y) (i : ℕ) :
    ((Real.digits y g i : ℕ) : ℤ) = digitStep g (y * (g : ℝ) ^ i) := by
  have hg : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  set N : ℤ := ⌊y * (g : ℝ) ^ (i + 1)⌋ with hN
  set M : ℤ := ⌊y * (g : ℝ) ^ i⌋ with hM
  have hds : digitStep g (y * (g : ℝ) ^ i) = N - g * M := by
    unfold digitStep
    rw [hN, hM, show (g : ℝ) * (y * (g : ℝ) ^ i) = y * (g : ℝ) ^ (i + 1) by ring]
  obtain ⟨hlo, hhi⟩ := digitStep_mem g hg (y * (g : ℝ) ^ i)
  rw [hds] at hlo hhi
  have hdval : ((Real.digits y g i : ℕ) : ℤ) = ((⌊y * (g : ℝ) ^ (i + 1)⌋₊ % g : ℕ) : ℤ) := by
    simp only [Real.digits, Fin.val_ofNat]
  have hpos : (0 : ℝ) ≤ y * (g : ℝ) ^ (i + 1) := mul_nonneg hy0 (by positivity)
  have hfn : (⌊y * (g : ℝ) ^ (i + 1)⌋₊ : ℤ) = N := by rw [Int.natCast_floor_eq_floor hpos]
  -- N % g = N − g·M : the part `g·M` is killed mod g, and `N − g·M ∈ [0,g)`.
  have hmod : N % (g : ℤ) = N - g * M := by
    conv_lhs => rw [show N = (N - g * M) + g * M by ring]
    rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hlo hhi]
  rw [hds, hdval, Int.natCast_mod, hfn, hmod]

end General

/-! ### Upstream module `General/Thm13.lean` -/

/-!
# Stoll [St05] Theorem 1.3 — digit extraction from the closed forms

Theorem 1.3 (g-ary, any base `g ≥ 2`): with `t = w/g^m` the base-`g` mantissa of `w`,
`a = g/((g−1)(t+g))`, `b = g/a`, recurrence `u₁ = 1`, `uₙ₊₁ = ⌊a(uₙ+ε)⌋` (n odd),
`⌊b(uₙ + 1/(g−1))⌋` (n even), one has `u₂ₙ₊₁ − g·u₂ₙ₋₁` = the n-th base-`g` digit of `w`.
The closed forms are `u₂ₖ = (g^{k−1}−1)/(g−1)` and `u₂ₖ₊₁ = g^k + ⌊t·g^{k−1}⌋`.

This module proves the **conclusion modulo the closed-form induction**: *given* the odd-index closed
form, the Graham–Pollak-style difference reads off a base-`g` digit (in `digitStep` form, range
`[0,g)`).  The closed-form induction itself (from the recurrence) is the remaining piece.

Numerically verified end-to-end (`tools/sandbox/st05_thm13_verify.py`).  The odd-index closed form is
written `u(2k+1) = g^k + ⌊t·g^k / g⌋` to avoid a negative exponent at `k = 0` (there it reads
`1 + ⌊t/g⌋ = 1 = u₁`, since `1 ≤ t < g`).
-/

namespace General

/-- **St05 Theorem 1.3 recurrence** (0-indexed, `gu g a b ε n = u_{n+1}`, `u₁ = 1`).  The step from
index `n` uses the `(a, ε)` offset when `n` is even (i.e. original odd index `n+1`) and
`(b, 1/(g−1))` when `n` is odd.  With `a = g/((g−1)(t+g))`, `b = g/a = (g−1)(t+g)`, this is the
recurrence whose closed forms are `gu(2k) = g^k + ⌊t·g^{k−1}⌋`, `(g−1)·gu(2k+1) = g^k − 1` — the
object the Aristotle closed-form induction (`tools/aristotle/thm13closed`, job `e0240fef`) ports onto. -/
noncomputable def gu (g : ℕ) (a b ε : ℝ) : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
      if Even n then ⌊a * ((gu g a b ε n : ℝ) + ε)⌋
      else ⌊b * ((gu g a b ε n : ℝ) + 1 / ((g : ℝ) - 1))⌋

@[simp] theorem gu_zero (g : ℕ) (a b ε : ℝ) : gu g a b ε 0 = 1 := rfl

/-- **St05 Theorem 1.3, digit-extraction step (from the odd-index closed form).**  If `u : ℕ → ℤ`
satisfies `u(2k+1) = g^k + ⌊t·g^k/g⌋` for all `k`, then for every `n ≥ 1`,
`u(2n+1) − g·u(2n−1) = digitStep g (t·g^{n−1}/g)`, a base-`g` digit lying in `[0,g)`. -/
theorem thm13_digit_of_oddClosed (g : ℕ) (hg : 1 ≤ g) (t : ℝ) (u : ℕ → ℤ)
    (hodd : ∀ k, u (2 * k + 1) = (g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋)
    (n : ℕ) (hn : 1 ≤ n) :
    u (2 * n + 1) - g * u (2 * n - 1) = digitStep g (t * (g : ℝ) ^ (n - 1) / g) ∧
      0 ≤ u (2 * n + 1) - g * u (2 * n - 1) ∧
      u (2 * n + 1) - g * u (2 * n - 1) < (g : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hgne : (g : ℝ) ≠ 0 := by positivity
  have he : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have hdig : u (2 * (m + 1) + 1) - g * u (2 * (m + 1) - 1)
      = digitStep g (t * (g : ℝ) ^ (m + 1 - 1) / g) := by
    rw [he, hodd (m + 1), hodd m, Nat.add_sub_cancel]
    simp only [digitStep]
    rw [show t * (g : ℝ) ^ (m + 1) / g = (g : ℝ) * (t * (g : ℝ) ^ m / g) by field_simp; ring]
    ring
  refine ⟨hdig, ?_, ?_⟩
  · rw [hdig]; exact (digitStep_mem g hg _).1
  · rw [hdig]; exact (digitStep_mem g hg _).2

/-- **St05 Theorem 1.3 conclusion as a literal mathlib digit.**  Chaining
`thm13_digit_of_oddClosed` with the general Prop-2 bridge `realDigits_eq_digitStep`: under the
odd-index closed form, `u(2n+1) − g·u(2n−1)` is exactly mathlib's leading base-`g` digit
`Real.digits (t·g^{n−1}/g) g 0` (`g ≥ 2`, `t ≥ 0`, `n ≥ 1`).  This identifies St05's recurrence
output with a bona-fide base-`g` digit in mathlib's API. -/
theorem thm13_digit_realDigits (g : ℕ) [NeZero g] (hg : 2 ≤ g) (t : ℝ) (ht : 0 ≤ t) (u : ℕ → ℤ)
    (hodd : ∀ k, u (2 * k + 1) = (g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋)
    (n : ℕ) (hn : 1 ≤ n) :
    u (2 * n + 1) - g * u (2 * n - 1)
      = ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hy0 : 0 ≤ t * (g : ℝ) ^ (n - 1) / g := by positivity
  rw [(thm13_digit_of_oddClosed g (by omega) t u hodd n hn).1,
    realDigits_eq_digitStep g (t * (g : ℝ) ^ (n - 1) / g) hy0 0, pow_zero, mul_one]

end General

/-! ### Upstream module `General/Thm13Closed.lean` -/

/-!
# Stoll [St05] Theorem 1.3 — the closed-form joint induction (unconditional)

This module discharges the LAST remaining piece of St05 Theorem 1.3: the two closed forms of the
recurrence `gu` (defined in `General/Thm13.lean`) follow from the recurrence by joint induction.
Combined with `thm13_digit_of_oddClosed`/`thm13_digit_realDigits` this yields the **unconditional**
Theorem 1.3 (the g-ary digits of any `w > 0`).

Setup (base `g ≥ 2`, `t` = base-`g` mantissa so `1 ≤ t < g`):
`a = g/((g−1)(t+g))`, `b = (g−1)(t+g)` (so `a·b = g`), `−1/g ≤ ε < (g+1)(g−2)/g`.
Closed forms (`k ≥ 0`):  `gu(2k) = g^k + ⌊t·g^k/g⌋`  and  `(g−1)·gu(2k+1) = g^k − 1`.

The proof rests on two single-step floor identities:
* `step_eo` (even→odd, the crux): `(g−1)·⌊a·(gu(2k)+ε)⌋ = g^k − 1`.  The algebra reduces to
  `(g−1)·a·(g^k + m + ε) = g·(g^k + m + ε)/(t+g)` with `m = ⌊t·g^k/g⌋`; the parameter bounds pin
  the result into `[(g^k−1)/(g−1), (g^k−1)/(g−1)+1)`.
* `step_oe` (odd→even, exact): `b·(gu(2k+1)+1/(g−1)) = g^{k+1} + t·g^k`, so its floor is
  `g^{k+1} + ⌊t·g^k⌋ = g^{k+1} + ⌊t·g^{k+1}/g⌋`.
-/

namespace General

/-- `(g−1)·(∑_{i<k} g^i) = g^k − 1` (geometric sum, integer version). -/
theorem geomSumI_mul (g : ℕ) (k : ℕ) :
    ((g : ℤ) - 1) * (∑ i ∈ Finset.range k, (g : ℤ) ^ i) = (g : ℤ) ^ k - 1 := by
  rw [mul_comm]; exact geom_sum_mul (g : ℤ) k

/-- Defining equation of `gu` at a successor index. -/
theorem gu_succ (g : ℕ) (a b ε : ℝ) (n : ℕ) :
    gu g a b ε (n + 1)
      = if Even n then ⌊a * ((gu g a b ε n : ℝ) + ε)⌋
        else ⌊b * ((gu g a b ε n : ℝ) + 1 / ((g : ℝ) - 1))⌋ := rfl

/-- **Even→odd step** (the crux of Thm 1.3's induction).  At an even index, the recurrence value
`g^k + ⌊t·g^k/g⌋` feeds the `(a,ε)` floor and produces the geometric sum `(g^k−1)/(g−1)`, phrased
as `(g−1)·⌊…⌋ = g^k − 1`. -/
theorem step_eo (g : ℕ) (hg : 2 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (ε a : ℝ) (ha : a = (g : ℝ) / (((g : ℝ) - 1) * (t + g)))
    (hε0 : -1 / (g : ℝ) ≤ ε) (hε1 : ε < ((g : ℝ) + 1) * ((g : ℝ) - 2) / g) (k : ℕ) :
    ((g : ℤ) - 1) * ⌊a * ((((g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋ : ℤ) : ℝ) + ε)⌋
      = (g : ℤ) ^ k - 1 := by
  have hgR : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have htg : (0 : ℝ) < t + g := by linarith
  set m : ℤ := ⌊t * (g : ℝ) ^ k / g⌋ with hm
  -- fractional-part facts, cleared of the /g
  have hmg_le : (m : ℝ) * (g : ℝ) ≤ t * (g : ℝ) ^ k := by
    have h := Int.floor_le (t * (g : ℝ) ^ k / g); rw [← hm] at h
    rw [le_div_iff₀ hgpos] at h; exact h
  have hmg_lt : t * (g : ℝ) ^ k < ((m : ℝ) + 1) * (g : ℝ) := by
    have h := Int.lt_floor_add_one (t * (g : ℝ) ^ k / g); rw [← hm] at h
    rw [div_lt_iff₀ hgpos] at h; exact h
  -- ε bounds, cleared of the /g
  have hgε0 : (-1 : ℝ) ≤ (g : ℝ) * ε := by
    have h := hε0; rw [div_le_iff₀ hgpos] at h; linarith
  have hgε1 : (g : ℝ) * ε < ((g : ℝ) + 1) * ((g : ℝ) - 2) := by
    have h := hε1; rw [lt_div_iff₀ hgpos] at h; linarith
  -- the geometric-sum integer
  set S : ℤ := ∑ i ∈ Finset.range k, (g : ℤ) ^ i with hSdef
  have hScast : ((g : ℝ) - 1) * (S : ℝ) = (g : ℝ) ^ k - 1 := by
    have h2 : ((((g : ℤ) - 1) * S : ℤ) : ℝ) = (((g : ℤ) ^ k - 1 : ℤ) : ℝ) :=
      congrArg _ (geomSumI_mul g k)
    push_cast at h2; linarith
  set X : ℝ := a * ((((g : ℤ) ^ k + m : ℤ) : ℝ) + ε) with hX
  have hXcast : ((((g : ℤ) ^ k + m : ℤ) : ℝ)) = (g : ℝ) ^ k + (m : ℝ) := by push_cast; ring
  -- key identity: (g-1)·X = g·(g^k + m + ε)/(t+g)
  have hkey : ((g : ℝ) - 1) * X = (g : ℝ) * ((g : ℝ) ^ k + (m : ℝ) + ε) / (t + g) := by
    rw [hX, ha, hXcast]; field_simp
  have hfloor : ⌊X⌋ = S := by
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩
    · -- (S:ℝ) ≤ X
      have hle : ((g : ℝ) - 1) * (S : ℝ) ≤ ((g : ℝ) - 1) * X := by
        rw [hScast, hkey, le_div_iff₀ htg]
        nlinarith [hmg_lt, hgε0, ht1]
      exact le_of_mul_le_mul_left hle hg1
    · -- X < S + 1
      have hlt : ((g : ℝ) - 1) * X < ((g : ℝ) - 1) * ((S : ℝ) + 1) := by
        have hRHS : ((g : ℝ) - 1) * ((S : ℝ) + 1) = (g : ℝ) ^ k - 1 + ((g : ℝ) - 1) := by
          rw [mul_add, hScast, mul_one]
        rw [hkey, hRHS, div_lt_iff₀ htg]
        nlinarith [hmg_le, hgε1, ht1, ht2,
          mul_nonneg (by linarith : (0 : ℝ) ≤ (g : ℝ) - 2) (by linarith : (0 : ℝ) ≤ t - 1)]
      exact lt_of_mul_lt_mul_left hlt (le_of_lt hg1)
  -- conclude
  rw [hX] at hfloor
  rw [hfloor, hSdef]
  exact geomSumI_mul g k

/-- **Odd→even step** (exact).  At an odd index, the recurrence value `(g^k−1)/(g−1)` feeds the
`(b, 1/(g−1))` floor and produces `g^{k+1} + ⌊t·g^{k+1}/g⌋` exactly. -/
theorem step_oe (g : ℕ) (hg : 2 ≤ g) (t : ℝ) (b : ℝ) (hb : b = ((g : ℝ) - 1) * (t + g))
    (k : ℕ) (v : ℤ) (hv : ((g : ℤ) - 1) * v = (g : ℤ) ^ k - 1) :
    ⌊b * ((v : ℝ) + 1 / ((g : ℝ) - 1))⌋ = (g : ℤ) ^ (k + 1) + ⌊t * (g : ℝ) ^ (k + 1) / g⌋ := by
  have hgR : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hg0 : (g : ℝ) ≠ 0 := ne_of_gt hgpos
  have hvcast : ((g : ℝ) - 1) * (v : ℝ) = (g : ℝ) ^ k - 1 := by exact_mod_cast hv
  -- b·(v + 1/(g-1)) = g^{k+1} + t·g^k
  have hval : b * ((v : ℝ) + 1 / ((g : ℝ) - 1)) = (g : ℝ) ^ (k + 1) + t * (g : ℝ) ^ k := by
    rw [hb]
    have hne : (g : ℝ) - 1 ≠ 0 := ne_of_gt hg1
    have expand : ((g : ℝ) - 1) * (t + g) * ((v : ℝ) + 1 / ((g : ℝ) - 1))
        = (t + g) * (((g : ℝ) - 1) * (v : ℝ)) + (t + g) := by field_simp
    rw [expand, hvcast, pow_succ]; ring
  rw [hval]
  -- align the RHS digit, then peel the integer off the floor
  have hdig : ⌊t * (g : ℝ) ^ (k + 1) / g⌋ = ⌊t * (g : ℝ) ^ k⌋ := by
    rw [show t * (g : ℝ) ^ (k + 1) / g = t * (g : ℝ) ^ k from by rw [pow_succ]; field_simp]
  rw [hdig, show (g : ℝ) ^ (k + 1) = (((g : ℤ) ^ (k + 1) : ℤ) : ℝ) from by norm_cast,
    Int.floor_intCast_add]

/-- **St05 Theorem 1.3 — the closed-form joint induction (unconditional).**  For the recurrence `gu`
(with `a = g/((g−1)(t+g))`, `b = (g−1)(t+g)`, mantissa `1 ≤ t < g`, base `g ≥ 2`, offset
`−1/g ≤ ε < (g+1)(g−2)/g`), both closed forms hold. -/
theorem thm13_closed (g : ℕ) (hg : 2 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (ε a b : ℝ) (ha : a = (g : ℝ) / (((g : ℝ) - 1) * (t + g)))
    (hb : b = ((g : ℝ) - 1) * (t + g))
    (hε0 : -1 / (g : ℝ) ≤ ε) (hε1 : ε < ((g : ℝ) + 1) * ((g : ℝ) - 2) / g) :
    (∀ k, gu g a b ε (2 * k) = (g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋) ∧
      (∀ k, ((g : ℤ) - 1) * gu g a b ε (2 * k + 1) = (g : ℤ) ^ k - 1) := by
  have hgR : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  -- B_k from A_k via step_eo (index 2k is Even)
  have hBfromA : ∀ k, gu g a b ε (2 * k) = (g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋ →
      ((g : ℤ) - 1) * gu g a b ε (2 * k + 1) = (g : ℤ) ^ k - 1 := by
    intro k hAk
    have hstep : gu g a b ε (2 * k + 1) = ⌊a * ((gu g a b ε (2 * k) : ℝ) + ε)⌋ := by
      rw [gu_succ, if_pos ⟨k, two_mul k⟩]
    rw [hstep, hAk]
    exact step_eo g hg t ht1 ht2 ε a ha hε0 hε1 k
  -- A_{k+1} from B_k via step_oe (index 2k+1 is Odd)
  have hAfromB : ∀ k, ((g : ℤ) - 1) * gu g a b ε (2 * k + 1) = (g : ℤ) ^ k - 1 →
      gu g a b ε (2 * (k + 1)) = (g : ℤ) ^ (k + 1) + ⌊t * (g : ℝ) ^ (k + 1) / g⌋ := by
    intro k hBk
    have hodd : ¬ Even (2 * k + 1) := by
      simp only [Nat.even_add_one, not_not]; exact ⟨k, two_mul k⟩
    have hstep : gu g a b ε (2 * (k + 1))
        = ⌊b * ((gu g a b ε (2 * k + 1) : ℝ) + 1 / ((g : ℝ) - 1))⌋ := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring, gu_succ, if_neg hodd]
    rw [hstep]
    exact step_oe g hg t b hb k (gu g a b ε (2 * k + 1)) hBk
  -- A by induction
  have hA : ∀ k, gu g a b ε (2 * k) = (g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋ := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.mul_zero, gu_zero, pow_zero, mul_one]
      have hfl : ⌊t / (g : ℝ)⌋ = 0 := by
        rw [Int.floor_eq_zero_iff, Set.mem_Ico]
        exact ⟨by positivity, by rw [div_lt_one hgpos]; linarith⟩
      rw [hfl]; omega
    | succ n ih => exact hAfromB n (hBfromA n ih)
  exact ⟨hA, fun k => hBfromA k (hA k)⟩

/-- **St05 Theorem 1.3 — unconditional, end to end.**  For the recurrence `gu` with the St05
parameters (`a = g/((g−1)(t+g))`, `b = (g−1)(t+g)`, mantissa `1 ≤ t < g`, base `g ≥ 2`, offset
`−1/g ≤ ε < (g+1)(g−2)/g`), the Graham–Pollak difference `gu(2n) − g·gu(2n−2)` (which is
`u_{2n+1} − g·u_{2n−1}` in St05's 1-indexing, since `gu m = u_{m+1}`) is exactly the leading
base-`g` digit `Real.digits (t·g^{n−1}/g) g 0`.  No `sorry`, no custom axiom: this discharges
Theorem 1.3 completely. -/
theorem thm13_digits (g : ℕ) [NeZero g] (hg : 2 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (ε a b : ℝ) (ha : a = (g : ℝ) / (((g : ℝ) - 1) * (t + g)))
    (hb : b = ((g : ℝ) - 1) * (t + g))
    (hε0 : -1 / (g : ℝ) ≤ ε) (hε1 : ε < ((g : ℝ) + 1) * ((g : ℝ) - 2) / g)
    (n : ℕ) (hn : 1 ≤ n) :
    gu g a b ε (2 * n) - g * gu g a b ε (2 * n - 2)
      = ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hclosed := (thm13_closed g hg t ht1 ht2 ε a b ha hb hε0 hε1).1
  have ht0 : (0 : ℝ) ≤ t := by linarith
  -- view gu as the 1-indexed u via u j = gu (j-1); then u(2k+1) = gu(2k) is the odd closed form
  have hodd : ∀ k, (fun j => gu g a b ε (j - 1)) (2 * k + 1)
      = (g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋ := by
    intro k; simpa using hclosed k
  have hmain := thm13_digit_realDigits g hg t ht0 (fun j => gu g a b ε (j - 1)) hodd n hn
  -- u(2n+1) = gu(2n),  u(2n-1) = gu(2n-2)
  have e1 : 2 * n + 1 - 1 = 2 * n := by omega
  have e2 : 2 * n - 1 - 1 = 2 * n - 2 := by omega
  simp only [e1, e2] at hmain
  exact hmain

end General

/-! ### Upstream module `General/Mantissa.lean` -/

/-!
# Base-`g` mantissa (Stoll [St05], §1)

For a real `w > 0` and integer base `g ≥ 2`, the mantissa `t = w / g^m` with `m = ⌊log_g w⌋` lies in
`[1, g)`.  This is the normalisation feeding St05's recurrences (`General/Thm13`, `Thm12`).
-/

namespace General

/-- **The base-`g` mantissa lies in `[1, g)`.**  `m = ⌊log_g w⌋`, `t = w/g^m`, then `1 ≤ t < g`. -/
theorem mantissa_mem (g : ℕ) (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w) :
    1 ≤ w / (g : ℝ) ^ (⌊Real.logb g w⌋) ∧
      w / (g : ℝ) ^ (⌊Real.logb g w⌋) < (g : ℝ) := by
  set b : ℝ := (g : ℝ) with hbdef
  have hb1 : (1 : ℝ) < b := by rw [hbdef]; exact_mod_cast hg
  have hbpos : (0 : ℝ) < b := by linarith
  have hbne1 : b ≠ 1 := by linarith
  set m : ℤ := ⌊Real.logb b w⌋ with hm
  have hpow_pos : (0 : ℝ) < b ^ m := zpow_pos hbpos m
  -- b^m ≤ w
  have hle : b ^ m ≤ w := by
    have h1 : b ^ (m : ℝ) ≤ b ^ Real.logb b w :=
      (Real.rpow_le_rpow_left_iff hb1).mpr (Int.floor_le _)
    rwa [Real.rpow_intCast, Real.rpow_logb hbpos hbne1 hw] at h1
  -- w < b^(m+1)
  have hlt : w < b ^ (m + 1) := by
    have h2 : b ^ Real.logb b w < b ^ ((m : ℝ) + 1) :=
      (Real.rpow_lt_rpow_left_iff hb1).mpr (Int.lt_floor_add_one _)
    rw [Real.rpow_logb hbpos hbne1 hw] at h2
    have hcast : b ^ ((m : ℝ) + 1) = b ^ (m + 1) := by
      rw [← Real.rpow_intCast b (m + 1)]; push_cast; ring_nf
    rwa [hcast] at h2
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hpow_pos]; linarith
  · rw [div_lt_iff₀ hpow_pos]
    have hsplit : b ^ (m + 1) = b * b ^ m := by rw [zpow_add_one₀ (by linarith)]; ring
    rw [hsplit] at hlt; linarith

end General

/-! ### Upstream module `General/St06Example.lean` -/

/-!
# Stoll [St06] Example 1.1 — the ternary digits of `e` via a `π,e`-recurrence

**Source.** T. Stoll, *On a problem of Erdős and Graham concerning digits*, **Acta Arith. 125**
(2006), 89–100, Example 1.1.  The showcase instance of St06's 3-parameter family (Thm 3.1):

> `v₁ = 3`,
> `v_{n+1} = ⌊ −3/(e+9) · (vₙ + π) ⌋` if `n` odd,
> `v_{n+1} = ⌊ −(e+9) · (vₙ + 1) ⌋` if `n` even.
> Then `v_{2n+1} − 3·v_{2n−1}` is the `n`-th ternary digit of `e = (2.201101121…)₃`.

This is Thm 3.1 at `g=3, m=3, l=2, k=−1`, with `w = t = e` and `ε = π`: triple `(3,2,−1) ∈ 𝒟₂⁻`,
`a = klg/((g−1)(t+mg)) = −3/(e+9)`, `b = g/a = −(e+9)`, even-step shift `l/(g−1) = 1`.  Unlike St05
(`Cor13e.lean`, which extracts the same digits from the *positive*-coefficient `gu` recurrence), this
uses **negative** coefficients and the transcendental offset `π`, with a leading term `m·gⁿ = 3·3ⁿ`
in the closed form.  Numerically verified to `n = 40` (`tools/sandbox/st06_example11_verify.py`).

The two closed forms (`su` is 0-indexed, `su n = v_{n+1}`):
* `su (2k)   = 3·3^k + ⌊e·3^k/3⌋`   (= `v_{2k+1}`, the `m·gᵏ + ⌊t·gᵏ/g⌋` odd form),
* `su (2k+1) = −(3^k + 1)`           (= `v_{2k+2}`, the `l(k·gᵏ−1)/(g−1)` even form).

Axiom-clean (inherits `[propext, Classical.choice, Quot.sound]`).
-/

namespace General

/-! ## The `e`/`π` instance (`g=3, m=3, l=2, k=−1`) -/

end General

/-! ### Upstream module `General/St06Thm31.lean` -/

/-!
# Stoll [St06] Theorem 3.1 — subcone `𝒟₂⁻` (the cone containing Example 1.1)

**Source.** T. Stoll, *On a problem of Erdős and Graham concerning digits*, **Acta Arith. 125**
(2006), 89–100, Theorem 3.1.  St06 generalizes St05 (`Thm13Closed.lean`) to a 3-parameter `(m,l,k)`
family of floor recurrences.  This module formalizes the theorem for **one subcone, `𝒟₂⁻`** — the
negative-`k` cone that contains the showcase Example 1.1 (`g=3,m=3,l=2,k=−1`, `St06Example.lean`).

Parameters (Def 2.2/2.3, subcone `𝒟₂⁻`): `g ≥ 3`, `m ≥ 1`, `0 < l ≤ g−1`, `k < 0`, and the
divisibility `(g−1) ∣ (k−1)l` (so the even closed form is integral).  Coefficients
`a = klg/((g−1)(t+mg))`, `b = g/a = (g−1)(t+mg)/(kl)`, even-step shift `l/(g−1)`.  Offset interval
(**corrected** — see `notes/ST06-THM31-ERRATUM.md`): `1 + (g−l−1)(mg+1)/(klg) ≤ ε < −(mg+1)/(kg)`.

Closed forms (`su` 0-indexed, `su n = u_{n+1}`):
* `su (2j)   = m·gʲ + ⌊t·gʲ/g⌋`        (the `u_{2n+1}` odd form, leading coeff `m`),
* `(g−1)·su (2j+1) = l(k·gʲ − 1)`       (the `u_{2n}` even form, written ×(g−1) to dodge division).

Conclusion: the Graham–Pollak difference `su(2n) − g·su(2n−2)` reads off `w`'s base-`g` digits.
Numerically verified over ~1M `(g,m,l,k,t,ε,f)` points.  Axiom-clean.
-/

namespace General

/-! ## Subcone `𝒟₁` (cone `𝒜₁`: `l < 0`) — shows the master handles negative `l` -/

/-! ## Subcone `𝒟₃` (cone `𝒜₃`: `l > g−1`) -/

/-! ## Cone `Ω₂` (`m ≤ −2`): here `P = t+mg < 0`, so `(g−1)P < 0` and the final `÷(g−1)P` step flips.
The cone-agnostic master `st06_thm31_closed_core` is UNCHANGED (it only needs `t+mg ≠ 0`); only the
`*_core` inequality lemmas need the sign-flipped division.  `𝒟₅⁻` below is the template. -/

end General

/-! ### Upstream module `General/St06Thm33.lean` -/

/-!
# Stoll [St06] Theorem 3.3 — the binary (`g = 2`) family

**Source.** T. Stoll, *On a problem of Erdős and Graham concerning digits*, **Acta Arith. 125**
(2006), 89–100, Theorem 3.3.  This is the binary analogue of Theorem 3.1 (`St06Thm31.lean`), which
explicitly **excludes** `g = 2`.  The recurrence (with `t ∈ [1,2)` the binary mantissa of `w`,
integers `m ≥ 1`, `0 ≤ l ≤ m−1`, `k ≥ 0`):

> `u₁ = m`,
> `u_{n+1} = ⌊a·(uₙ + ½)⌋`   (`n` odd),
> `u_{n+1} = ⌊b·(uₙ + ε)⌋`   (`n` even),
> with `a = 2k+1 + (t+2l)/(t+2m)`, `b = 2/a`, and the **`k`-independent** offset interval
> `½ − (2l+1)/(2(2m+1)) ≤ ε < ½ + (2l+1)/(2(2m+1))`.

Two conclusions:
* (1)  `u_{2n+1} − 2·u_{2n−1} = dₙ`                        (the `n`-th binary digit of `w`),
* (2)  `u_{2n+2} − 2·u_{2n} = d_{n+1} + k·(2dₙ − 1)`,

where `dₙ` is indexed with `d₁ = ⌊t·2⁰⌋ − 2⌊t·2^{−1}⌋` (the integer digit), the same convention as
`General/Cor13e.lean`.  `w = √2, (m,l,k) = (1,0,0), ε = ½` is the headline Graham–Pollak instance.

## Closed forms (`su` 0-indexed, `su n = u_{n+1}`, used as `su a b (1/2) ε m`)
* **odd index**   `su (2n)   = m·2ⁿ + ⌊t·2ⁿ/2⌋`                       (= `u_{2n+1}`),
* **even index**  `su (2n+1) = 2k·(m·2ⁿ+⌊t·2ⁿ/2⌋) + (m+l)·2ⁿ + ⌊t·2ⁿ⌋ + k`   (= `u_{2n+2}`).

Conclusion (1) is then `digit_of_evenClosed_coeff` (`St06Example.lean`) at `g = 2`, `c = m`.

Both closed forms verified numerically over many `(m,l,k,t,ε)` and to large `n`
(`tools/sandbox/st06_thm33_verify.py`, `/tmp/st06_*.py`).  Axiom-clean.
-/

namespace General

/-! ## The two floor cruxes (abstracted over an integer `s ≥ 1` standing for `2ⁿ`).

Only the binary-digit relation `2B ≤ C ≤ 2B+1` (`B = ⌊t·s/2⌋`, `C = ⌊t·s⌋`) is used, so the cruxes
hold for **every** integer `s ≥ 1`, not just powers of two. -/

/-! ## The closed forms and the two digit conclusions -/

end General

/-! ### Upstream module `General/St06Thm34.lean` -/

/-!
# Stoll [St06] Theorem 3.4 — the second binary (`g = 2`) family, at `ε = ½`

**Source.** T. Stoll, *On a problem of Erdős and Graham concerning digits*, **Acta Arith. 125**
(2006), 89–100, Theorem 3.4.  Same recurrence shape as Theorem 3.3 (`St06Thm33.lean`) but with
`a = 2k+1 + 2l/(t+2m)` (the numerator is `2l`, not `t+2l`) and `1 ≤ l ≤ m`.

> `u₁ = m`, `u_{n+1} = ⌊a·(uₙ + ε)⌋` (`n` odd), `u_{n+1} = ⌊b·(uₙ + ½)⌋` (`n` even), `b = 2/a`.

i.e. **`ε` sits on the `a`-step** (the odd→even paper step that Stoll varies) and `½` on the `b`-step.
In our 0-indexed `St06Example.su a b ε s m` this is `su a b ε (1/2) m` (`ε` enters at `Even n`).

**Closed forms** (`su a b ε (1/2) m`, verified `0/4000` random `(m,l,k,t)`):
* odd   `su(2j)   = m·2ʲ + ⌊t·2ʲ/2⌋`                         (the universal odd form),
* even  `su(2j+1) = (2k+1)·(m·2ʲ+⌊t·2ʲ/2⌋) + k + l·2ʲ`.

Conclusion (1) — `su(2n) − 2·su(2n−2) = nth binary digit of w` — is then `digit_of_evenClosed_coeff`
at `g=2, c=m`, identical to Theorem 3.3.

**ε-interval — the GENUINE, full, `t`-universal interval** (`st06_thm34_astep_eps`,
`st06_thm34_closed_eps`, `st06_thm34_digits_eps`, `st06_thm34_isBit_eps`).  Conclusion (1) holds for
**every** `ε` in Stoll's printed symmetric interval

> `½ − (m−l+½)/D₁  ≤  ε  <  ½ + (m−l+½)/D₁`,   `D₁ = (2m+1)(2k+1)+2l`,

uniformly over all real `w > 0` (`t ∈ [1,2)`).  No Diophantine / equidistribution input: the `a`-step
floor bracket `0 ≤ Dε − (t+2m)k + l(2B − t·s) < t+2m` is bounded by the **independent** worst cases of
`t ∈ [1,2)` and `2B − t·s ∈ (−2,0]`, both binding at `t=1` (hence the `D₁` denominator).

**⚠️ Historical note — the `ε`-on-`b`-step "obstruction" theorems below**
(`st06_thm34_bstep_value/band`, `st06_thm34_band_fails_below/above_half`) study a **different**
recurrence: `ε` on the `b`-step, `½` on the `a`-step — that is Theorem **3.3**'s placement, with `ε ↔ ½`
**swapped** from Theorem 3.4.  They are sound Lean (axiom-clean) but say **nothing** about Theorem 3.4;
their "only `ε = ½` works" conclusion is an artifact of putting `ε` on the genuinely non-uniform step.
The ON-LINE findings (2026-06-13, `archive/findings/`) caught this.  The honest Theorem 3.4 result is
the full interval above — kept the swapped theorems as a documented contrast (a faithful proof of an
*unfaithful* statement; `#print axioms` clean says nothing about statement-faithfulness).  Axiom-clean.
-/

namespace General

/-! ## The GENUINE full-interval Theorem 3.4 (every `ε` in Stoll's printed symmetric interval)

The theorems below are Stoll's actual Theorem 3.4: the recurrence is `su a b ε (1/2) m` — `ε` on the
`a`-step (the offset Stoll varies), `½` on the `b`-step — and the conclusion holds for **every** `ε`
in the printed symmetric interval, uniformly over `w` (i.e. `t ∈ [1,2)`).  This is the genuine
content the ON-LINE findings (2026-06-13) identified: the `ε`-on-`b`-step obstruction theorems above
(`st06_thm34_band_fails_*`) are about a *different* recurrence (`3.3`-placement, `ε ↔ ½` swapped) and
say nothing about Theorem 3.4.  Here the interval is a real theorem, not a single point. -/

end General

/-! ### Upstream module `General/St06Cor35.lean` -/

/-!
# Stoll [St06] Corollary 3.5 — the Beatty foundation

**Source.** T. Stoll, *On a problem of Erdős and Graham concerning digits*, **Acta Arith. 125**
(2006), 89–100, Corollary 3.5.  The elegant capstone unifies the binary digit-extraction recurrences
via **Beatty's / Rayleigh's theorem**: the two Beatty sequences `B⁺(1+√2)` and `B⁺(1+1/√2)` partition
the positive integers, and (extended to all signs) every `m ∈ ℤ∖{−1,0}` is `⌊r(1+1/√2)⌋` or
`⌊r(1+√2)⌋` for a unique `r`, which fixes the `w` whose binary digits the `√2`-recurrence reproduces.

This module establishes the **verified Beatty foundation** that the full corollary rests on:
* `Erdos482.General.irrational_one_add_sqrt2` — `1 + √2` is irrational;
* `Erdos482.General.holderConjugate_one_add_sqrt2` — `(1+√2)` and `(1+1/√2)` are Hölder conjugate
  (`(1+√2)⁻¹ + (1+1/√2)⁻¹ = 1`), the exact hypothesis Rayleigh's theorem needs;
* `Erdos482.General.beatty_partition_sqrt2` — Rayleigh's partition for this conjugate pair:
  `{⌊k(1+√2)⌋ | k>0} ∆ {⌊k(1+1/√2)⌋ | k>0} = ℤ_{>0}`.

The remaining step of Cor 3.5 — packaging, for each representable `m`, the `w = w(r)` and the index
shift `M = ⌊log₂ w⌋` so that `su √2 √2 (1/2) (1/2) m` reproduces `w`'s digits via the (already proved)
digit theorem — is the next increment (see `notes/ST06-PLAN.md` Cor 3.5; the per-`w` recurrence is the
`m=1,(l,k)=(0,0)` Graham–Pollak instance of `St06Thm33`).  Axiom-clean.
-/

namespace General

/-! ## The Cor 3.5 digit engine — generalized Graham–Pollak (factor `r`)

The Graham–Pollak recurrence `su √2 √2 ½ ½ m` (both steps `⌊√2·(·+½)⌋`) started at the Beatty value
`m = ⌊r·(1+1/√2)⌋ = r + ⌊r√2/2⌋` (case 1) or `m = ⌊r·(1+√2)⌋ = r + ⌊r√2⌋` (case 2) reads off the
binary digits of `r·√2`.  This is the classical `gp_pair` (the `r=1` case) generalized by a free
factor `r ∈ ℕ`; the `s`-cancellation crux (`Erdos482.crux`) and the odd-step bound
(`Erdos482.eq8_general`, at `ε=½`) are both universal, so inserting `r` is mechanical. -/

/-! ## Beatty connection and the capstone -/

end General

/-! ### Upstream module `General/SelfRefWall.lean` -/

/-!
# The self-referential digit crux is exactly the √2 / base-2 phenomenon

**Context.** The headline Graham–Pollak result rests on `Erdos482.crux`: the *self-referential*
inequality `0 ≤ {x} − √2·{x/2} + √2/2 < 1`, where the recurrence's own coefficient `√2` equals the
algebraic generator of the number whose digits it reads.  A natural question (cf.
`notes/CUBIC-EXPLORATION.md`): does this self-reference generalize to other bases `g` — i.e. does
`u ↦ ⌊√g·(u + c)⌋` read base-`g` digits, via a `g`-analogue crux

> `0 ≤ {x} − √g·{x/g} + c·√g < 1`   for all `x`?

**Answer: NO for every `g ≥ 3`, for ANY offset `c`** (`selfref_crux_fails_of_three_le`).  Combined
with `Erdos482.crux` (the `g = 2`, `c = ½` case) this pins the phenomenon down completely: the elegant
self-referential digit extraction exists **iff `g = 2`** — it is a genuinely quadratic, base-2
miracle, not the tip of a tower of base-`g` analogues.  (Stoll's general St05/St06 results read *any*
real's base-`g` digits, but with a `w`-tuned rational coefficient, never the self-referential `√g`.)

**Proof idea.**  Two witnesses pin `c` between incompatible bounds when `g ≥ 3`:
* `x = g − 1`  has `{x} = 0`, `{x/g} = (g−1)/g`, so the lower bound forces `c·√g ≥ √g·(g−1)/g`,
  i.e. `c ≥ (g−1)/g`;
* `x = ½`  has `{x} = ½`, `{x/g} = 1/(2g)`, so the upper bound needs `½ − √g/(2g) + c·√g < 1`.
Substituting `c ≥ (g−1)/g` and `√g·√g = g` reduces the two to `2g − √g − 3 < 0`, which is false for
`g ≥ 3` (there `√g < g`, so `2g − √g − 3 > g − 3 ≥ 0`).  No `c` survives.
-/

namespace General

/-!
## The single-internal-floor crux is *solvable* for every sub-2 multiplier — the cubic obstruction is NOT here

An ON-LINE literature finding (`archive/findings/…cubic-selfref-literature.md`) proposed a "Tier-1"
cubic impossibility: that for `α = 2^{1/3}` reading base 2, **no** constant offset `c` makes the
single-internal-floor crux `0 ≤ {x} − α·{x/2} + c·α < 1` hold for all `x` (expecting the two-witness
method of `selfref_crux_fails_of_three_le` to scale up).

**That expectation is FALSE.**  The two-witness method does *not* scale to this object, because here
the *division stays at base 2* while only the multiplier changes — unlike `selfref_crux_fails_of_three_le`,
where both the division (`/g`) and the multiplier (`√g`) grow together.  In fact `c = ½` works for
**every** multiplier `0 ≤ β < 2` (and fails exactly at `β = 2`).  The reason is a clean width-1 identity:
with `t := {x/2}` one has `{x} = 2t − ⌊2t⌋`, so

* for `t < ½`:  `{x} − β t + β/2 = t(2−β) + β/2 ∈ [β/2, 1)`;
* for `t ≥ ½`:  `{x} − β t + β/2 = t(2−β) − 1 + β/2 ∈ [0, 1−β/2)`.

Both half-open ranges sit inside `[0,1)` precisely when `0 ≤ β < 2`.  (HOSTCHECK: 2M random samples at
`β = 2^{1/3}` give zero violations; `β = 2` gives ~50%.)

**Consequence for the cubic story.**  The genuine cubic obstruction is therefore *not* at the
single-floor level at all — it lives in the **3-step offset schedule** (two internal floors whose
rounding errors must cancel simultaneously; the `j ≈ 64` numeric breakdown of `cubic_recover.py`).
`selfref_crux_solvable_iff` (multiplier *and* division both `= g`) is the self-referential statement
that genuinely fails for `g ≥ 3`; the divide-by-2 single floor below is a *different* object that
survives, and conflating the two was the finding doc's error.  This corrects the record and sharpens
where the cubic wall actually is.
-/

end General

/-! ### Upstream module `General/CubicDefect.lean` -/

/-!
# The cubic three-step defect identity — where the cubic obstruction actually lives

**Context.**  `Erdos482.crux` makes the Graham–Pollak two-step `√2`-map a clean multiply-by-2 shift:
the single internal floor's rounding error stays in a width-1 window, uniformly in `x`.  The natural
cubic analogue replaces `√2` by `α = 2^{1/3}` (`α³ = 2`) and uses a **three**-step map with a
3-periodic offset schedule `(c₀,c₁,c₂)`:
`v₁ = ⌊α(u+c₀)⌋`, `v₂ = ⌊α(v₁+c₁)⌋`, `v₃ = ⌊α(v₂+c₂)⌋`.  For this to read base-2 digits, the
three-fold composite must be a clean shift `v₃ = 2u + (digit)` for all `u` along the orbit.

**This file proves the exact algebraic identity governing that composite** (`cubic_threestep_defect`):

> `v₃ = 2u + (2c₀ + α²c₁ + αc₂) − (α²·f₁ + α·f₂ + f₃)`,
> where `f₁ = {α(u+c₀)}`, `f₂ = {α(v₁+c₁)}`, `f₃ = {α(v₂+c₂)}` are the three internal floor errors.

It is pure algebra (the only input is `α³ = 2`).  Its payoff is to **localize the cubic wall precisely**:

* The "digit" produced is `v₃ − 2u = (2c₀+α²c₁+αc₂) − (α²f₁ + α·f₂ + f₃)`.
* For a base-2 readout this must lie in `{0,1}` for **every** `u` on the orbit, i.e. the **combined
  defect** `α²f₁ + α·f₂ + f₃` must stay inside a *single* width-1 window `(2c₀+α²c₁+αc₂) − {0,1}`.
* But `f₁,f₂,f₃ ∈ [0,1)` independently, so `α²f₁ + α·f₂ + f₃` ranges over `[0, α²+α+1) ≈ [0, 4.05)`
  — width `α²+α+1 > 1` (`cubic_combined_defect_range_wide`).  **Two internal floors give a defect
  spread far exceeding 1**, unlike the single-floor `√2` case whose spread is exactly 1.

So the cubic obstruction is **not** at any single-floor level (cf.
`SelfRefWall.onefloor_div2_crux_cbrt2`, where the single floor *is* solvable): it is forced by the
**two** internal floors of the three-step composite, whose errors `(f₁,f₂,f₃)` cannot be simultaneously
pinned into a width-1 window by any fixed offset schedule once the orbit explores their full range.
Whether the geometric orbit `u_n ≈ W·2^{n/3}` actually realises that full range is the residual
(equidistribution-of `{α^n ξ}`) question — see `notes/CUBIC-EXPLORATION.md` and `PENDING_WORK.md`.
-/

/-! ### Upstream module `General/DoublingOrbit.lean` -/

/-!
# A.e. density of the doubling-map orbit on `ℝ/ℤ`

The cubic self-referential frontier (`General/CubicDefect.lean`) reduces to a statement about the
**doubling map** `x ↦ 2x` on the circle: the block orbit `uₙ = ⌊W·2ⁿ⌋` makes the first internal-floor
error a doubling-map orbit `≈ {αW·2ⁿ}`, so the residual obstruction is whether that orbit avoids a
constrained set (the two-plane confinement of `cubic_orbit_defect_confined`).  For a *specific* `W` this
is the open "is this number base-2 normal" question; but for **almost every** `W` the orbit cannot avoid
any nonempty open set, which already rules out the measure-zero confinement.

This file proves that unconditional a.e. statement, using only the ergodicity of `×2` on `AddCircle`
(`AddCircle.ergodic_nsmul`, already in mathlib) — **no pointwise Birkhoff theorem is needed**:

* `ae_orbit_mem_of_isOpen`: for any nonempty open `U`, a.e. `x` has its forward doubling-orbit enter
  `U`.  (Heart: the "ever hits `U`" set `A = ⋃ₙ T⁻ⁿU` satisfies `T⁻¹A ⊆ A` and `μ A ≥ μ U > 0`, so
  ergodicity forces `A` conull.)
* `ae_dense_orbit_doubling`: a.e. `x` has a **dense** doubling-orbit (intersect the previous over a
  countable basis).

These are the ergodic core of attack-path #2 (the a.e.-`W` unconditional cubic route) in
`PENDING_WORK.md`.  Density (not full equidistribution) already contradicts the two-plane confinement,
so this is the right tool — the remaining gap to a complete a.e.-`W` cubic theorem is the *skew-product*
step relating the joint internal-floor coordinates `(f₁,f₂,f₃)` to this single doubling orbit.
-/

/-! ### Upstream module `General/WeylDoubling.lean` -/

/-!
# Weyl bricks for a.e. equidistribution of the doubling orbit `{2ⁿs}`

`PENDING_WORK.md ★★` reduces the a.e.-`W` cubic impossibility to **a.e. equidistribution of the doubling
orbit `{2ⁿ s}`** (`s ∈ ℝ`), provable WITHOUT a pointwise Birkhoff theorem via the **Davenport–Erdős–
LeVeque** L² method: bound the mean square of the Weyl exponential sum, then apply Borel–Cantelli (both
ingredients are in mathlib).  This file holds the first concrete bricks.

* `char_int`: character orthogonality on `[0,1]`, `∫₀¹ e^{2πi M s} ds = δ_{M,0}`.
* `two_pow_inj`: `(2:ℤ)ⁿ = 2ᵐ ↔ n = m` (used to identify the diagonal of the Weyl double sum).
* `weyl_double_sum_integral`: termwise integration of an abstract double exponential sum.
* `doubling_weyl_L2_mean`: **the Weyl L² mean** `∫₀¹ (∑_{n,m<N} e^{2πi·k·(2ⁿ−2ᵐ)·s}) ds = N` for `k≠0`
  — the mean square of the doubling exponential sum, with only the `N` diagonal terms surviving.

With the L² mean, DEL gives `(1/N)Σ_{n<N} e^{2πi k 2ⁿ s} → 0` a.e. (Borel–Cantelli along `N_j=j²` +
monotonicity), i.e. a.e. base-2 equidistribution — the remaining input for the cubic frontier's path #2.

*Elaboration note.*  Commuting the *double* finite sum through the interval integral whnf-loops if the
summand carries inline integer arithmetic in its cast; `weyl_double_sum_integral` is stated over an
**abstract** `G : ℕ → ℕ → ℤ` precisely so defeq never unfolds that arithmetic; the doubling instance
then follows by `rw [weyl_double_sum_integral …]` and a diagonal count.
-/

/-! ### Upstream module `General/BaseGWeyl.lean` -/

/-!
# Base-`g` Weyl bricks for a.e. equidistribution of the orbit `{gⁿs}`

The base-`g` (`g ≥ 2`) analogue of `WeylDoubling`.  The a.e.-`W` general-`d` impossibility generalizes
from base 2 (doubling, window width 2, digits `{0,1}`) to base `g` (multiplier `gⁿ`, window width `g`,
digits `{0,…,g-1}`); the analytic engine is **base-agnostic** — the only base-specific input is the
injectivity `n ↦ gⁿ`, which here replaces `WeylDoubling.two_pow_inj`.

* `g_pow_inj`: `(g:ℤ)ⁿ = gᵐ ↔ n = m` for `g ≥ 2` (`Nat.pow_right_injective`).
* `baseG_weyl_L2_mean`: the Weyl L² mean `∫₀¹ (∑_{n,m<N} e(k(gⁿ−gᵐ)s)) ds = N` (`k ≠ 0`).
* `baseG_weyl_L2_normalized`: `∫₀¹ ‖(1/N)∑_{n<N} e(k·gⁿ·s)‖² ds = 1/N` — exactly `∫‖g_N‖²` for the DEL
  engine, summable along `N=j²`.

The abstract `weyl_double_sum_integral` + `char_int` (orthogonality) are reused verbatim from
`WeylDoubling`; only the diagonal-count lemma changes base.
-/

/-! ### Upstream module `General/Equidistribution.lean` -/

/-!
# Equidistribution framework + Weyl's criterion (toward the a.e.-`W` cubic frontier)

`PENDING_WORK.md ★★` reduces the a.e.-`W` cubic impossibility to **a.e. equidistribution of the doubling
orbit `{2ⁿ s}`**, via Davenport–Erdős–LeVeque (DEL). The DEL chain produces
`(1/N_j)∑_{n<N_j} e(k·2ⁿ s) → 0` a.e. along the subsequence `N_j = j²`; two pieces then assemble the
equidistribution statement, and **neither is in mathlib**:

* **gap-filling** (`cesaro_fill_of_subseq_sq`): from convergence along the squares `N_j = j²` to
  convergence along *all* `N`, using only that the summands are bounded (`‖aₙ‖ ≤ 1`). Elementary, but
  the `Nat.sqrt`-squeeze bookkeeping is the work. Factored through `cesaro_fill_aux`, an abstract
  statement about any sequence of partial sums with `1`-Lipschitz increments.
* **Weyl's criterion** (to come): a sequence on `AddCircle 1` is equidistributed iff all its nonzero
  Weyl sums `(1/N)∑ fourier k` vanish — the `⟸` direction needs Stone–Weierstrass
  (`span_fourier_closure_eq_top`, present in mathlib).
-/

/-! ### Upstream module `General/DELEngine.lean` -/

/-!
# The Davenport–Erdős–LeVeque L² engine (Markov + first Borel–Cantelli)

On `[0,1]` with Lebesgue measure: if a sequence of (a.e. strongly) measurable `ℂ`-valued functions
`g_j` has **finite total mean square** `∑_j ∫₀¹ ‖g_j‖² < ∞`, then `g_j → 0` almost everywhere.

This is the abstract analytic step (a) of `PENDING_WORK.md ★★`.  Applied to
`g_j(s) = (1/j²)·∑_{n<j²} e^{2πi k 2ⁿ s}` — whose mean square `∫₀¹‖g_j‖² = 1/j²` (from
`WeylDoubling.doubling_weyl_L2_normalized`) is summable — it yields, along `N_j = j²`,
`(1/N_j)∑_{n<N_j} e(k2ⁿs) → 0` a.e.; gap-filling (`Equidistribution.cesaro_fill_of_subseq_sq`) upgrades
to all `N`, and the Weyl criterion (`Equidistribution.weyl_criterion`) turns that into a.e. base-2
equidistribution of `{2ⁿs}` — the cubic frontier's path #2.

**Provenance.** Proved by Aristotle (job `bd44d316`), verified here in-kernel and `#print axioms`-clean.
Aristotle flagged a genuine **faithfulness bug** in the originally-submitted statement: the hypothesis
`Summable (fun j => ∫⁻ ‖g_j‖₊²)` is *vacuous* (`ENNReal.summable` — every `ℝ≥0∞`-valued function is
`Summable`), so the theorem as first stated was false (the constant `g_j = 1` satisfies it but does not
tend to `0`).  The intended `∑_j ∫₀¹‖g_j‖² < ∞` is the `ℝ≥0∞`-valued total-sum *finiteness*
`(∑' j, ∫⁻ ‖g_j‖₊²) ≠ ⊤`, used below.  (KB: `#print axioms` clean ≠ statement-faithful.)
-/

/-! ### Upstream module `General/DoublingEquidist.lean` -/

/-!
# Step (b) assembly: a.e. equidistribution of the doubling orbit `{2ⁿ s}`

`PENDING_WORK.md ★★` step (b).  Combining the bricks of this lap —
* `WeylDoubling.doubling_weyl_L2_normalized` (`∫₀¹‖(1/N)∑_{n<N} e(k2ⁿ·)‖² = 1/N`),
* `DELEngine.l2_bridge` + `DELEngine.ae_tendsto_zero_of_summable_sq` (the DEL L² engine),
* `Equidistribution.tsum_ofReal_inv_sq_ne_top` (p-series finiteness),
* `Equidistribution.cesaro_fill_of_subseq_sq` (gap-fill `j²` → all `N`),
* `Equidistribution.weyl_criterion` + `fourier_doubling_eq` (Weyl criterion + the fourier↔exp seam),

we obtain: **for almost every `s ∈ [0,1]`, the doubling orbit `n ↦ ↑(2ⁿ s)` is equidistributed on
`ℝ/ℤ`** (`ae_doubling_orbit_equidistributed`).  This is the unconditional a.e. input that the cubic
self-referential frontier's path #2 lifts to `T³` (step (c)) to break the two-plane defect confinement.
-/

/-! ### Upstream module `General/BaseGEquidist.lean` -/

/-!
# a.e. equidistribution of the base-`g` orbit `{gⁿ s}`

The base-`g` (`g ≥ 2`) analogue of `DoublingEquidist`.  For almost every real `s`, the orbit
`n ↦ ↑(gⁿ s)` is equidistributed on `ℝ/ℤ` — the base-`g` Borel normality statement, via the
Davenport–Erdős–LeVeque L² method (`BaseGWeyl.baseG_weyl_L2_normalized` + the DEL engine).

* `ae_baseG_weyl_tendsto` / `ae_baseG_weyl_tendsto_real`: per-frequency a.e. vanishing of the base-`g`
  Weyl average (over `[0,1]` resp. all of `ℝ`).
* `ae_baseG_orbit_equidistributed` / `_real`: a.e. equidistribution of the base-`g` orbit.

The general periodicity bridge `ae_of_ae_restrict_Icc01_of_periodic` and the gap-fill /
Weyl-criterion / DEL pieces are all base-agnostic and reused verbatim.
-/

/-! ### Upstream module `General/MultidimWeyl.lean` -/

/-!
# Multidimensional Weyl criterion (toward step (c): the `T³` lift of the cubic frontier)

`PENDING_WORK.md ★★` step (c) lifts the a.e. doubling equidistribution to the torus
`UnitAddTorus d = d → ℝ/ℤ`.  mathlib's `Mathlib.Analysis.Fourier.AddCircleMulti` already provides the
torus Fourier characters `mFourier` and torus Stone–Weierstrass (`span_mFourier_closure_eq_top`), so the
multidimensional Weyl criterion is a near-mirror of the 1-D `Equidistribution.weyl_criterion`.

This file builds the genuinely-new crux first: **the torus Fourier integral**
`∫ mFourier n = δ_{n,0}` (`integral_mFourier_eq`), via Fubini over the product measure
(`integral_fintype_prod_volume_eq_prod`) and the 1-D `integral_fourier_eq`.
-/

/-! ### Upstream module `General/EquidistDense.lean` -/

/-!
# Equidistribution ⇒ dense orbit (step (c) piece 3 of the cubic frontier)

`PENDING_WORK.md ★★` step (c) piece 3.  The genuinely-new general fact (mathlib-absent): on a compact
Hausdorff Borel space with a finite, open-positive measure `μ`, if the Cesàro averages of every
continuous test function converge to its integral, then the orbit `{xₙ}` is **dense**.

This is the bridge that lets the a.e.-`W` `T³` equidistribution (assembled from the doubling
equidistribution via the Weyl reduction) contradict the **measure-zero two-plane defect confinement**
of the cubic self-referential map (`CubicDefect`).

**Provenance.** The general lemma `isEquidistributed_dense` (and its bump helper) were proved by
Aristotle (job `3e68d32f`), verified here in-kernel + `#print axioms`-clean.  Specialized below to the
torus `Tᵈ` (`isEquidistributedTorus_dense`) — the form the cubic frontier consumes.
-/

/-! ### Upstream module `General/CubicTorusEquidist.lean` -/

/-!
# Final assembly: a.e.-`W` equidistribution of the cubic `T³` orbit `2ⁿ(W, αW, α²W)`

`PENDING_WORK.md ★★` step (c), the assembly that lifts the a.e. doubling equidistribution to the torus.
For `α = 2^{1/3}` and almost every real `W`, the orbit
`n ↦ (2ⁿ·W mod 1, 2ⁿ·αW mod 1, 2ⁿ·α²W mod 1) ∈ T³` is **equidistributed**, hence **dense**.

**The Weyl reduction.**  For a nonzero frequency `m : Fin 3 → ℤ`, the torus character along the orbit is
`mFourier m (orbitₙ) = e(2πi · 2ⁿ · ξ·W)` with `ξ := m₀ + m₁α + m₂α²`.  By `cubic_lin_indep_int`
(`{1,α,α²}` ℤ-independent), `m ≠ 0 ⇒ ξ ≠ 0`, so this is the **frequency-1 doubling Weyl sum** at the
scaled seed `s = ξ·W`.  `ae_doubling_weyl_tendsto_real 1` (a.e.-`ℝ` vanishing) scaled by
`ae_comp_mul_left` (the `s = ξW` substitution, `ξ ≠ 0`) gives per-`m` a.e.-`W` vanishing; intersecting
over the countably many `m ≠ 0` (`ae_all_iff`) and applying `weyl_criterion_torus` yields the a.e.-`W`
`T³` equidistribution.  `isEquidistributedTorus_dense` then gives the dense orbit — the input the
cubic-defect confinement (`CubicDefect.cubic_orbit_defect_confined`, a measure-zero two-plane set) must
contradict for the unconditional a.e.-`W` cubic impossibility.
-/

/-! ### Upstream module `General/CubicDefectLink.lean` -/

/-!
# The cubic defect as a function of the base-2 orbit point (toward the density contradiction)

`PENDING_WORK.md ★★` step (c) piece 4.  The cubic block orbit is `uₙ = ⌊W·2ⁿ⌋` (base-2,
`CubicDefect.cubic_block_orbit_base_two_bounds`).  We express the two internal floor errors `f₁, f₂` at
`uₙ` purely through the **canonical fractional coordinates** of the doubling orbit point
`(r₁, r₂, r₃) = ({W·2ⁿ}, {αW·2ⁿ}, {α²W·2ⁿ})`:

* `cubic_f1_orbit`:  `f₁ = {r₂ − α·r₁ + α·c₀}`,
* `cubic_f2_orbit`:  `f₂ = {r₃ − α²·r₁ − α·f₁ + α²c₀ + αc₁}`.

Hence the **partial defect** `g = α²f₁ + αf₂` (which, by `CubicDefect.cubic_partial_defect_mem_window`,
must lie in the width-2 window `(C−2, C]` for a digit-reading orbit) is a fixed function of
`(r₁, r₂, r₃)` — continuous away from the floor-jump surfaces.  As the orbit point ranges densely over
`T³` (`CubicTorusEquidist.ae_W_cubic_torus_orbit_dense`), `(f₁, f₂)` ranges over `[0,1)²`, so `g` ranges
over `[0, α²+α)` (width `> 2`), leaving the window — the unconditional a.e.-`W` contradiction.  This file
builds the algebraic half (the orbit-coordinate identities); the density/continuity finish remains.
-/

/-! ### Upstream module `General/BinaryExpansion.lean` -/

/-!
# Binary block orbits recover the base-2 floor expansion of their value

A **binary block orbit** is a sequence `orbit : ℕ → ℤ` with `orbit 0 = m` and the doubling-plus-digit
recurrence `orbit (n+1) = 2·orbit n + dₙ`, each digit `dₙ ∈ {0,1}`.  Its real *value* is the binary
number `W = m + ∑ₖ dₖ·2^(−(k+1))`.  Provided the digit sequence is not eventually all `1` (`htail`: every
tail contains a `0` — excluding dyadic boundary values), the orbit is exactly the base-2 block orbit of
`W`:  `⌊W·2ⁿ⌋ = orbit n` for every `n` (`binary_floor_eq`).

This is the bridge that turns a digit-reading *recurrence* orbit (e.g. the cubic self-referential map's
`orbit(n+1) = cubicV3(orbit n)`) into a statement about the floor orbit `⌊W·2ⁿ⌋` of its value, the form
the a.e.-`W` impossibility theorems consume.
-/

/-! ### Upstream module `General/CubicFinish.lean` -/

/-!
# Piece 2 of the cubic finish: the partial defect as a *continuous* function on `T³`

`PENDING_WORK.md ★★★` piece 2.  To feed the density tool `EquidistDense.exists_lt_of_dense_continuousAt`
we need a single function `F : T³ → ℝ` (`T = ℝ/ℤ`) with
* `F (cubicTorusOrbit W n) = cubicPartialDefect α c0 c1 c2 (⌊W·2ⁿ⌋)` — it reads the partial defect along
  the orbit, and
* `ContinuousAt F p` at any torus point `p` whose three real representatives `ρ(p i) = {·}` are nonzero
  and whose two inner `fract`-arguments are non-integers.

The representative map `ρ : ℝ/ℤ → ℝ` is the canonical interior chart `ρ x := (AddCircle.equivIco 1 0 x)`,
which satisfies `ρ (↑t) = Int.fract t` (`AddCircle.coe_equivIco_mk_apply`) and is `ContinuousAt` away from
`0` (`AddCircle.continuousAt_equivIco`).  Then `F a := cubicGpd α c0 c1 (ρ (a 0)) (ρ (a 1)) (ρ (a 2))`,
and `ContinuousAt F p` reduces (via `ContinuousAt.comp`) to `continuousAt_cubicGpd`
(`CubicDefectLink`).
-/

noncomputable section
namespace General

/-! ### The cubic multiplier `cbrt2` satisfies `cbrt2 ^ 3 = 2`. -/

/-! ### The geometric crux: the partial defect leaves every digit window.

For any schedule `(c₀,c₁,c₂)` there is an interior, non-jump point of the canonical fractional-coordinate
cube `(0,1)³` at which the partial-defect function `cubicGpd` *leaves* the digit window `(C−2, C]`
(`C = 2c₀+α²c₁+αc₂`).  This is the width-`(α²+α) > 2` range argument made constructive: choose `(fA,fB)`
near a corner of `(0,1)²` so that `cubicGpd = α²fA + αfB` exceeds `C` (when `C < α²+α`) or falls below
`C−2` (when `C ≥ α²+α`); realize `(fA,fB)` by solving the two `fract` equations for `(r₁,r₂,r₃)`.

Proof harvested from Aristotle job `7b1ff2ad` ("gpdwin"), verified in our kernel + `#print axioms`-clean.
-/

end General

end
/-! ### Upstream module `General/QuarticDefect.lean` -/

/-!
# The quartic four-step self-referential floor map (degree-4 generalization, foundations)

Generalizing `CubicDefect` from `α = 2^{1/3}` (3 steps) to `α = 2^{1/4}` (4 steps).  The four-step map
`v₁=⌊α(u+c₀)⌋`, `v₂=⌊α(v₁+c₁)⌋`, `v₃=⌊α(v₂+c₂)⌋`, `v₄=⌊α(v₃+c₃)⌋` reads base-2 digits iff
`v₄ − 2u ∈ {0,1}` for every block `u = ⌊W·2ⁿ⌋` (note `α⁴ = 2`, so four steps multiply by `2`).

This file ports the *algebraic backbone*: the four-step defect identity (`quartic_fourstep_defect`), the
digit bridge (`quarticV4_sub_eq`), and the combined-defect range-width obstruction
(`quartic_combined_defect_range_wide`).  The analytic finish (a.e.-`W` `T⁴` equidistribution + geometry)
reuses the already-general `MultidimWeyl`/`EquidistDense`/`DELEngine` machinery and the
`quartic_lin_indep_int` backbone (in progress); see `PENDING_WORK.md`.
-/

namespace General

noncomputable section

/-! ### The defect collapse: the fourth floor error is forced, and the digit is `⌊C − g⌋`.

Mirrors the cubic `g`-collapse (`CubicDefect.cubic_f3_eq` … `cubic_partial_defect_mem_window`).  The
*three*-floor partial defect `g = α³f₁ + α²f₂ + αf₃` (the first three internal errors) governs the whole
quartic readout: the fourth error is forced `f₄ = {C − g}`, the extracted digit is `⌊C − g⌋`, and a
base-2 digit confines `g` to the width-2 window `(C−2, C]`.  Since `g` ranges over `[0, α³+α²+α)` with
width `α³+α²+α ≈ 4.28 > 2`, an orbit exploring that range leaves the window. -/

/-! ### ℤ-linear independence of `{1, 2^{1/4}, 2^{2/4}, 2^{3/4}}` (the quartic algebraic backbone). -/

end

end General

/-! ### Upstream module `General/QuarticDefectLink.lean` -/

/-!
# The quartic partial defect as a function of the base-2 orbit point (degree-4 generalization)

Degree-4 analogue of `CubicDefectLink`.  The four-step block orbit is `uₙ = ⌊W·2ⁿ⌋`; we express the
three internal floor errors `f₁, f₂, f₃` at `uₙ` through the canonical fractional coordinates of the
doubling orbit point `(r₁,r₂,r₃,r₄) = ({W·2ⁿ}, {αW·2ⁿ}, {α²W·2ⁿ}, {α³W·2ⁿ})`:

* `quartic_f1_orbit`:  `f₁ = {r₂ − α·r₁ + α·c₀}`,
* `quartic_f2_orbit`:  `f₂ = {r₃ − α²·r₁ − α·f₁ + α²c₀ + αc₁}`,
* `quartic_f3_orbit`:  `f₃ = {r₄ − α³·r₁ − α²·f₁ − α·f₂ + α³c₀ + α²c₁ + αc₂}`.

Hence the three-floor partial defect `g = α³f₁ + α²f₂ + αf₃` is a fixed function `quarticGpd` of
`(r₁,r₂,r₃,r₄)`, continuous away from the floor-jump surfaces.  As the orbit point ranges densely over
`T⁴` (the `T⁴` equidistribution, parallel to the cubic), `g` ranges over `[0, α³+α²+α)` (width `> 2`),
leaving the window of `QuarticDefect.quartic_partial_defect_mem_window` — the unconditional a.e.-`W`
quartic contradiction.  This file builds the algebraic half (the orbit-coordinate identities + `quarticGpd`).
-/

/-! ### Upstream module `General/QuarticTorusEquidist.lean` -/

/-!
# a.e.-`W` equidistribution of the quartic `T⁴` orbit `2ⁿ(W, αW, α²W, α³W)`

Degree-4 analogue of `CubicTorusEquidist`.  For `α = 2^{1/4}` and almost every real `W`, the orbit
`n ↦ (2ⁿW, 2ⁿαW, 2ⁿα²W, 2ⁿα³W) mod 1 ∈ T⁴` is equidistributed, hence dense.  The Weyl reduction is
identical to the cubic: the torus character along the orbit is `e(2πi·2ⁿ·ξW)` with
`ξ = m₀+m₁α+m₂α²+m₃α³`, nonzero for `m ≠ 0` by `quartic_lin_indep_int`; this is the frequency-1 doubling
Weyl sum at `s = ξW`, killed a.e. by the doubling equidistribution backbone scaled via `ae_comp_mul_left`.
-/

/-! ### Upstream module `General/QuarticFinish.lean` -/

/-!
# The quartic geometric crux: the partial defect leaves every digit window

Degree-4 analogue of `CubicFinish.cubicGpd_exceeds_window`.  For any schedule `(c₀,c₁,c₂)` and any
constant `C`, there is an interior non-jump point `(r₁,r₂,r₃,r₄) ∈ (0,1)⁴` where the three-floor partial
defect `quarticGpd = α³fA + α²fB + α·fC` (with `fA,fB,fC ∈ (0,1)`) leaves the width-2 window `(C−2, C]`.
The range `(0, α³+α²+α)` has width `α³+α²+α > 3 > 2` (as `α = 2^{1/4} > 1`), so no window of length 2
contains it.  Realization reuses `CubicFinish.fract_shift_realize`: fix `r₁ = 1/2`, solve `r₂,r₃,r₄` for
the three prescribed fractional parts.
-/

/-! ### Upstream module `General/RpowLinIndep.lean` -/

/-!
# General degree-`d` ℤ-linear independence of `{1, 2^{1/d}, …, 2^{(d-1)/d}}`

**Context (the general-`d` self-referential frontier).**  The cubic (`CubicDefect.lean`) and quartic
(`QuarticDefect.lean`) self-referential impossibilities each needed, as their single genuinely-hard
algebraic brick, the ℤ-linear independence of the powers of `α = 2^{1/d}`:
`cubic_lin_indep_int` (`d = 3`) and `quartic_lin_indep_int` (`d = 4`).  Those were proved by *ad hoc*
per-degree arguments — a cubic elimination and an infinite 2-adic norm descent — neither of which
generalizes cleanly to arbitrary `d`.

**This file proves the brick uniformly for every `d ≥ 1`** (`rpow_lin_indep_int`): the only integer
relation `∑_{i<d} aᵢ·αⁱ = 0` is the trivial one.  The principled route is **Eisenstein at the prime
`2`**: `Xᵈ − 2` is irreducible over `ℤ` (`irreducible_of_eisenstein_criterion`), hence over `ℚ`
(Gauss's lemma, `Monic.irreducible_iff_irreducible_map_fraction_map`), so it is the minimal polynomial
of the real number `α = 2^{1/d}` over `ℚ` (`minpoly.eq_of_irreducible_of_monic`).  A nonzero rational
polynomial of degree `< d` therefore cannot vanish at `α` (`minpoly.degree_le_of_ne_zero`), which is
exactly the asserted linear independence after reading off coefficients.

This is the algebraic engine that lets the entire cubic/quartic development be replayed at any degree
`d ≥ 3` (where the partial-defect window `α + α² + … + α^{d-1}` has width `> 2`).  Mathlib's Kummer
irreducibility (`X_pow_sub_C_irreducible_of_prime`) only covers *prime* exponents, so it misses
`d = 4, 6, 8, 9, …`; Eisenstein at `2` covers **all** `d` at once.

Everything here depends only on the trust base `[propext, Classical.choice, Quot.sound]`.
-/

/-! ### Upstream module `General/RpowWindow.lean` -/

/-!
# General degree-`d` partial-defect window width `> 2`

**Context (the general-`d` self-referential frontier).**  In the cubic/quartic impossibilities the
combined internal-floor defect `g = α^{d-1}f₁ + α^{d-2}f₂ + … + α f_{d-1}` (with `α = 2^{1/d}`,
`fᵢ ∈ [0,1)`) ranges over `[0, S_d)` with `S_d = α + α² + … + α^{d-1}`.  A base-2 digit forces
`g` into a window of width `2`; the impossibility is driven by `S_d > 2`, so a dense orbit of
`(f₁,…,f_{d-1})` must leave the window.  (`cubic_combined_defect_range_wide` is the `d = 3` instance.)

**This file proves the width brick uniformly for every `d ≥ 3`** (`rrt_window_gt_two`).  The clean
pivot is the closed form: since `α^d = 2`, the geometric sum gives `S_d = 1/(α-1) − 1 = (2-α)/(α-1)`,
and `S_d > 2 ⟺ α < 4/3 ⟺ 2 < (4/3)^d`, which holds for all `d ≥ 3` because `(4/3)³ = 64/27 > 2` and
`(4/3)^d` is increasing.  (For `d = 2`, `α = √2 ≈ 1.41 > 4/3`, `S_2 = √2 < 2` — consistent with the
original Graham–Pollak `√2` recurrence being solvable: the obstruction begins exactly at `d = 3`.)

Everything here depends only on the trust base `[propext, Classical.choice, Quot.sound]`.
-/

/-! ### Upstream module `General/GeneralDefect.lean` -/

/-!
# The general degree-`d` defect identity

**Context (the general-`d` self-referential frontier).**  `CubicDefect.lean` / `QuarticDefect.lean`
proved, for `d = 3, 4`, that the `d`-step floor map
`vₖ₊₁ = ⌊α(vₖ + cₖ)⌋`  (`α = 2^{1/d}`, `v₀ = u`)
satisfies the *defect identity*
`v_d = 2u + C − D`,  `C = ∑_{k<d} α^{d-k} cₖ`,  `D = ∑_{k<d} α^{d-1-k} fₖ`,  `fₖ = {α(vₖ+cₖ)}`,
by an explicit `linear_combination` of the `d` floor equations.  That cannot be written down for a
*variable* `d`.

**This file proves the defect identity uniformly for every `d`** (`dStep_defect_identity`).  The clean
generalization is to recognize the floor map as an **affine recurrence** `vₖ₊₁ = α·vₖ + bₖ` with
`bₖ = α cₖ − fₖ`, whose closed form `v_d = αᵈ·v₀ + ∑_{k<d} α^{d-1-k} bₖ` (`affine_rec_closed`) is a
one-line induction.  Substituting `αᵈ = 2` and splitting `bₖ` recovers the identity.

This is the degree-agnostic replacement for the hand-rolled cubic/quartic `linear_combination`s, and
the algebraic backbone for the uniform general-`d` impossibility (paired with `rpow_lin_indep_int` and
`rrt_window_gt_two`).  Everything depends only on `[propext, Classical.choice, Quot.sound]`.
-/

namespace General

/-! ### Base-`b` versions of the digit-extraction chain (toward the base-`g` generalization)

The base-2 chain above hardcodes the doubling `2u` (from `α^(e+1) = 2`).  Below are the same lemmas
parametrized by an arbitrary base `b : ℕ` (`α^(e+1) = (b:ℝ)`), where the extracted base-`b` digit is
`v_{e+1} − b·u`.  These are the algebraic core of the base-`b` impossibility; the base-2 ones are the
`b = 2` instances.  Combined with `geom_window_gt_base` (window width `> b` for `b^{1/d} < 2b/(b+1)`),
they give the base-`b` obstruction. -/

end General

/-! ### Upstream module `General/GeneralDefectCheck.lean` -/

/-!
# Faithfulness: the cubic engine is the `d = 3` instance of the general one

The general degree-`d` defect engine (`GeneralDefect.lean`) is meant to subsume the hand-rolled,
independently-verified cubic engine (`CubicDefect.lean`).  This file machine-checks that subsumption on
the *map* level: the explicit three-fold-nested floor `cubicV3` is literally `dStepV … 3` for the
schedule `(c₀,c₁,c₂)`, and consequently the abstract `dStep_defect_identity` instantiates to the
already-proven cubic identity `cubicV3_sub_eq`.  This is a genuine cross-check (not a re-proof): it
validates that the general statement is the correct generalization of the verified special case.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

/-! ### Upstream module `General/GeneralOrbit.lean` -/

/-!
# The general degree-`d` floor errors as functions of the doubling-orbit coordinates

**Context (the general-`d` analytic bridge).**  `GeneralDefect.lean` reduces the `d`-step impossibility
to the partial defect `g = ∑_{k<d-1} α^{d-1-k} fₖ` of the floor errors `fₖ` at the integer start
`u = ⌊W·2ⁿ⌋`.  To run the equidistribution argument we must express each `fₖ` as a function of the
`Tᵈ` doubling-orbit coordinates `rᵢ = {αⁱ·W·2ⁿ}`.

**This file proves that orbit-coordinate form uniformly for every `k`** (`dStepF_orbit`), the
degree-agnostic analogue of `cubic_f1_orbit`/`cubic_f2_orbit`.  The clean route is the affine-recurrence
closed form (`affine_rec_closed`): since
`α(vₖ + cₖ) = α^{k+1}⌊W2ⁿ⌋ + ∑_{j<k} α^{k-j}(αcⱼ − fⱼ) + αcₖ`
and `α^{k+1}⌊W2ⁿ⌋ = ⌊α^{k+1}W2ⁿ⌋ + {α^{k+1}W2ⁿ} − α^{k+1}{W2ⁿ}`, dropping the integer floor gives
`fₖ = { {α^{k+1}W2ⁿ} − α^{k+1}{W2ⁿ} + ∑_{j<k} α^{k-j}(αcⱼ − fⱼ) + αcₖ }`.
No fresh induction is needed — `affine_rec_closed` already did it.

This is the entry point to the remaining analytic `Tᵈ`-assembly (density + the geometry crux
`exists_partial_defect_outside_window`).  Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

/-! ### Upstream module `General/GeneralTorusEquidist.lean` -/

/-!
# a.e.-`W` equidistribution of the general `Tᵈ` orbit `2ⁿ(W, αW, …, α^{d-1}W)`

The degree-`d` analogue of `CubicTorusEquidist` (`α = 2^{1/d}`): for almost every real `W`, the orbit
`n ↦ (2ⁿ·αⁱ·W mod 1)_{i<d} ∈ Tᵈ` is **equidistributed**, hence **dense**.  The analytic engine
(`MultidimWeyl.weyl_criterion_torus`, `DELEngine.ae_comp_mul_left`,
`DoublingEquidist.ae_doubling_weyl_tendsto_real`) is already degree-agnostic; the only per-degree input
is the ℤ-linear independence `rpow_lin_indep_int` (⇒ `ξ = ∑ᵢ mᵢαⁱ ≠ 0` for `m ≠ 0`).
-/

/-! ### Upstream module `General/BaseGTorusEquidist.lean` -/

/-!
# a.e.-`W` equidistribution of the base-`g` torus orbit `gⁿ(W, αW, …, α^{d-1}W)`

The base-`g` analogue of `GeneralTorusEquidist` (`α = g^{1/d}`).  For almost every real `W`, the orbit
`n ↦ (gⁿ·αⁱ·W mod 1)_{i<d} ∈ Tᵈ` is **equidistributed**, hence **dense** — *provided* the frequencies
`{1, α, …, α^{d-1}}` are ℤ-linearly independent (`hli`), i.e. `Xᵈ − g` is irreducible over ℚ.

The analytic engine (`MultidimWeyl.weyl_criterion_torus`, `DELEngine.ae_comp_mul_left`,
`BaseGEquidist.ae_baseG_weyl_tendsto_real`) is base- and degree-agnostic; the only per-`(g,d)` input is
the ℤ-linear independence, supplied here as a hypothesis (`hli : ∀ m ≠ 0, ∑ᵢ mᵢαⁱ ≠ 0`) to be discharged
separately (Eisenstein for `g` prime-power-free, or `X_pow_sub_C_irreducible_of_prime` for `d` prime and
`g` not a perfect `d`-th power).
-/

/-! ### Upstream module `General/GaryExpansion.lean` -/

/-!
# Base-`g` block orbits recover the base-`g` floor expansion of their value

The base-`g` (`g ≥ 2`) analogue of `BinaryExpansion`.  A **base-`g` block orbit** is a sequence
`orbit : ℕ → ℤ` with `orbit 0 = m` and `orbit (n+1) = g·orbit n + dₙ`, each digit `dₙ ∈ {0,…,g-1}`.  Its
real value is `W = m + ∑ₖ dₖ·g^{−(k+1)}`.  Provided the digit sequence is not eventually all `g-1`
(`htail`: every tail contains a digit `≤ g-2` — excluding `g`-adic boundary values), the orbit is exactly
the base-`g` block orbit of `W`: `⌊W·gⁿ⌋ = orbit n` for every `n` (`gary_floor_eq`).

Bridge for the base-`g` self-referential capstones (`BaseGFinish`), turning a digit-reading *recurrence*
orbit into a statement about the floor orbit `⌊W·gⁿ⌋` of its value.
-/

/-! ### Upstream module `General/GeneralTorusFinish.lean` -/

/-!
# Torus-level plumbing for the general degree-`d` finish

Expresses the partial defect `dStepPartial` along the base-2 orbit as a function `dGpdTorus` on the
torus `Tᵈ = (ℝ/ℤ)ᵈ` (reusing `CubicFinish.torusRep`, the interior chart `ℝ/ℤ → [0,1)`), and proves it
is `ContinuousAt` torus points with nonzero coordinates and non-integer inner arguments.  This is the
glue between the algebraic engine (`GeneralOrbit.dGpd`) and the geometric input
(`GeneralTorusEquidist.ae_W_dTorus_orbit_dense`); the only remaining step to the general headline is the
nonzero-coordinate realization (see `PENDING_WORK.md`).
-/

/-! ### Upstream module `General/BaseGFinish.lean` -/

/-!
# The base-`g` general-degree impossibility (uniform over schedules)

The base-`g` analogue of `GeneralTorusFinish.ae_no_dStep_schedule_reads_base_two`.  For `α = g^{1/d}`
with `g ≥ 2`, an Eisenstein prime for `g` (`p ∣ g`, `p² ∤ g`, giving ℤ-lin-indep of `{1, α, …, α^{d-1}}`),
and the window-escape bound `α < 2g/(g+1)` (which forces the partial-defect window width `S_d > g`,
`geom_window_gt_base`), almost every real `W` admits **no** degree-`d` schedule reading `W`'s base-`g`
digits: for every `c` there is a step `n` where the extracted digit `dStepV(⌊W·gⁿ⌋) − g·⌊W·gⁿ⌋`
leaves `{0, …, g-1}`.

The plumbing (`coordsOf`, `dGpdTorus`, `continuousAt_dGpdTorus`) and the geometry-crux construction
(`realizeR0`, `orbitF_realizeR0`, the countable bad-set seed choice) are all base-agnostic; only the
multiplier `gⁿ`, the window width `S_d > g`, and the digit window `(C − g, C]` differ from base 2.
-/

/-! ### Upstream module `General/BaseGSubsumes.lean` -/

/-!
# Cross-development consistency: the base-`g` story at `g = 2` reproduces the base-2 story

A kernel-checked faithfulness anchor (à la `GeneralSubsumes`).  The base-`g` digit-representability
predicate `DStepDigitRepresentableBaseG 2 d W` — which encodes a valid base-2 digit as the *interval*
`0 ≤ dStepV − 2u ≤ 1` — coincides with the independently-built base-2 predicate
`DStepDigitRepresentable d W`, which encodes it as the *two-point set* `dStepV − 2u ∈ {0,1}`.  They agree
because the extracted digit is an **integer** (`dStepV` at the last step is a floor, `dStepZ`), and
`grt 2 d = rrt d`.  Hence the base-`g` `g = 2` impossibility is the base-2 impossibility.
-/

/-! ### Upstream module `General/GeneralSubsumes.lean` -/

/-!
# The general degree-`d` impossibility subsumes the hand-rolled cubic and quartic

`GeneralTorusFinish.ae_no_dStep_schedule_reads_base_two` is the uniform degree-`d` (`d ≥ 3`)
impossibility.  This file machine-checks that it genuinely **subsumes** the two independently-developed
special cases (`CubicFinish.ae_no_cubic_schedule_reads_base_two`, `d = 3`, and
`QuarticFinish.ae_no_quartic_schedule_reads_base_two`, `d = 4`): each is re-derived here purely as the
general theorem instantiated at the appropriate degree, via the map-level bridges `cubicV3_eq_dStepV` /
`quarticV4_eq_dStepV` (`GeneralDefectCheck`).

This is a genuine **cross-development consistency check**, not a re-proof: the cubic/quartic headlines
were proven by hand-rolled engines; the general headline by the degree-agnostic engine.  That the latter
*implies* the former (kernel-checked) is strong evidence both statements are faithful — a subtle error in
the general window/defect would break this derivation.  Axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

/-! ### Upstream module `General/Erdos482General.lean` -/

/-!
# Erdős–Graham #482 — the general resolution (any `w > 0`, any base `g ≥ 2`)

The headline deliverable of the St05 track, packaged as one statement.  Given any real `w > 0` and any
integer base `g ≥ 2`, there is an explicit floor-recurrence `gu g a b ε` (with `a·b = g`, built from the
base-`g` mantissa `t = w / g^{⌊log_g w⌋} ∈ [1, g)`) whose Graham–Pollak difference
`gu(2n) − g·gu(2n−2)` is exactly the `n`-th base-`g` digit of `w` (as the mathlib digit
`Real.digits (t·g^{n−1}/g) g 0`).  This is Erdős–Graham's "similar results for √m and other algebraic
numbers" — made fully explicit and machine-checked.  Inherits `thm13_digits`: axiom-clean.

We take the offset `ε = −1/g`, which lies in St05's admissible range `[−1/g, (g+1)(g−2)/g)` for **every**
`g ≥ 2` (at `g = 2` the range is `[−1/2, 0)`, so `ε = 0` would fail — `ε = −1/g` is the safe uniform
witness).
-/

namespace General

/-- **Erdős–Graham #482, resolved in full generality.**  For any `w > 0` and integer base `g ≥ 2`,
with mantissa `t = w/g^{⌊log_g w⌋}`, there exist coefficients `a, b, ε` (with `a·b = g`) so that the
recurrence `gu g a b ε` reads off the base-`g` digits of `w`:
`gu(2n) − g·gu(2n−2) = Real.digits (t·g^{n−1}/g) g 0` for every `n ≥ 1`. -/
theorem erdos482_resolution (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w) :
    ∃ a b ε : ℝ, a * b = (g : ℝ) ∧
      ∀ n, 1 ≤ n →
        gu g a b ε (2 * n) - g * gu g a b ε (2 * n - 2)
          = ((Real.digits
              (w / (g : ℝ) ^ (⌊Real.logb g w⌋) * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hgpos : (0 : ℝ) < (g : ℝ) := by positivity
  have hg1 : (g : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    linarith
  set t : ℝ := w / (g : ℝ) ^ (⌊Real.logb g w⌋) with ht
  obtain ⟨ht1, ht2⟩ := mantissa_mem g hg w hw
  have htg : t + (g : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ t := ht1; positivity
  refine ⟨(g : ℝ) / (((g : ℝ) - 1) * (t + g)), ((g : ℝ) - 1) * (t + g), -1 / (g : ℝ), ?_, ?_⟩
  · field_simp
  · intro n hn
    have hε0 : -1 / (g : ℝ) ≤ -1 / (g : ℝ) := le_refl _
    have hg2 : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    have hε1 : -1 / (g : ℝ) < ((g : ℝ) + 1) * ((g : ℝ) - 2) / g := by
      rw [div_lt_div_iff_of_pos_right hgpos]
      nlinarith [hg2, mul_nonneg (show (0 : ℝ) ≤ (g : ℝ) - 2 by linarith)
        (show (0 : ℝ) ≤ (g : ℝ) + 1 by linarith)]
    exact thm13_digits g hg t ht1 ht2 (-1 / (g : ℝ))
      ((g : ℝ) / (((g : ℝ) - 1) * (t + g))) (((g : ℝ) - 1) * (t + g)) rfl rfl hε0 hε1 n hn

end General

/-- Erdős Problem 482: the Graham--Pollak digits of `√2` in the site's indexing, and Stoll's
resolution for every real `w > 0` in every base `g ≥ 2`. -/
theorem erdos_482 :
    (∀ n : ℕ, 1 ≤ n →
      (a (2 * n + 1) : ℤ) - 2 * (a (2 * n - 1) : ℤ)
        = ((⌊Real.sqrt 2 * 2 ^ (n - 1)⌋₊ % 2 : ℕ) : ℤ)) ∧
    (∀ (g : ℕ) [NeZero g], 2 ≤ g → ∀ w : ℝ, 0 < w →
      ∃ a b ε : ℝ, a * b = (g : ℝ) ∧
        ∀ n, 1 ≤ n →
          General.gu g a b ε (2 * n) - g * General.gu g a b ε (2 * n - 2)
            = ((Real.digits
                (w / (g : ℝ) ^ (⌊Real.logb g w⌋) * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ)) :=
  ⟨erdos_482_verbatim, fun g _ hg w hw => General.erdos482_resolution g hg w hw⟩

#print axioms erdos_482
-- 'Erdos482.erdos_482' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos482
